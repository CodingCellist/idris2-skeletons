module Skeletons.Farm

import System
import Data.List

import System.Concurrency.BufferedChannel

%default total

||| A worker can either get another task or an indication that there is no more
||| work so it should stop.
public export
data WorkUnit : Type -> Type where
  TASK : Lazy task -> WorkUnit task
  STOP : WorkUnit _

||| A work result is either a value resulting from running the work, or an
||| indication that the worker is done (i.e. that it received a `STOP`
||| @WorkUnit@).
public export
data WorkResult : Type -> Type where
  RES : val -> WorkResult val
  DONE : WorkResult _

||| A Farm is a skeleton consisting of a maximum number of workers/threads to
||| use, and a list of independent work-units to be done. Since each work-unit
||| is self-contained, they can be run in parallel with workers picking up new
||| work-units as they finish their current one. This repeats until all the
||| work-units have been computed.
export
data Farm : Type -> Type where
  MkFarm : (nWorkers : Nat)
         -> (work : List (WorkUnit resTy))
         -> Farm resTy

||| Create a new farm which uses the specified number of workers and does the
||| specified work.
|||
||| @nWorkers The number of workers (threads) the farm can use.
||| @work     A list of `WorkUnit`s that the workers need to do.
export
initFarm : (nWorkers : Nat) -> (work : List (WorkUnit resTy)) -> Farm resTy
initFarm = MkFarm

||| A basic unit of work in a farm. Retrieves work from the channel referenced
||| in workRef, sending the results to outRef, until a `STOP` instruction is
||| received.
worker : (workRef : IORef (BufferedChannel (WorkUnit a)))
       -> (outRef : IORef (BufferedChannel (WorkResult a)))
       -> IO ()
worker workRef outRef =
  do (MkDPair workChan recv) <- becomeReceiver Blocking workRef
     (MkDPair outChan send) <- becomeSender outRef
     (TASK task) <- recv workChan
        | STOP => send Signal outChan DONE
     send Signal outChan (RES task)
     --                   ^ TASK is Lazy, but RES is not  => evaluation!
     let workRef' = assert_smaller workRef workRef
     --             ^ Idris cannot know recv reduces the size of shared channel
     worker workRef' outRef

||| Given a list of ThreadIDs, fork a single thread whose sole purpose is
||| waiting on all those threads to finish.
waitOnThreadBundle : (ts : List ThreadID)
                   -> IO ThreadID
waitOnThreadBundle ts = fork $ ignore (traverse (\t => threadWait t) ts)

||| Given a farm containing a list of work, create a BufferedChannel containing
||| all the work and a number of `STOP` instructions equal to the number of
||| workers in the farm.
|||
||| @farm The farm whose work needs to be loaded into a BufferedChannel.
loadWork : (farm : Farm a)
         -> IO (IORef (BufferedChannel (WorkUnit a)))
loadWork (MkFarm nWorkers work) =
  do putStr "Loading work... "
     workRef <- makeBufferedChannel
     (MkDPair workChan flexSend) <- becomeSender workRef
     let send = flexSend Signal 
     ignore $ traverse (\w => send workChan w) work
     ignore $ for (replicate nWorkers STOP) (\stop => send workChan stop)
     putStrLn "Done."
     pure workRef

||| Given a number of workers, a referenence to a channel on which to receive
||| work, and a reference to a channel on which the workers can put their
||| result(s), spawns @nWorkers@ many threads wired up to the channels as
||| appropriate.
|||
||| @nWorkers The number of worker threads to spawn.
||| @workRef  An IORef to a BufferedChannel on which to receive work units.
||| @outRef   An IORef to a BufferedChannel on which to send the work results.
spawnWorkers : (nWorkers : Nat)
             -> (workRef : IORef (BufferedChannel (WorkUnit a)))
             -> (outRef : IORef (BufferedChannel (WorkResult a)))
             -> IO (List ThreadID)
spawnWorkers 0 _ _ = pure []
spawnWorkers (S k) workRef outRef =
  do workerThreadID <- fork $ worker workRef outRef
     workerThreadIDs <- spawnWorkers k workRef outRef
     pure (workerThreadID :: workerThreadIDs)

||| Run a farm, spawning n threads where n is the number of workers in the farm.
||| Returns a @ThreadID@ representing a thread waiting on all the workers in the
||| farm, and an @IORef@ to a @BufferedChannel@ over which to receive the work
||| results.
|||
||| @farm The farm to run.
export
runFarm : (farm : Farm a)
        -> IO (ThreadID, IORef (BufferedChannel (WorkResult a)))
runFarm farm@(MkFarm nWorkers work) =
  do outRef <- makeBufferedChannel
     workRef <- loadWork farm
     workerThreadIDs <- spawnWorkers nWorkers workRef outRef
     putStrLn $ "Spawned " ++ show nWorkers ++ " workers."
     bundleThreadID <- waitOnThreadBundle workerThreadIDs
     pure (bundleThreadID, outRef)

||| Retrieve all the output from a farm that has been run.
|||
||| @farm   The farm that was run.
||| @runRes The pair that was returned from calling `runFarm` on the farm.
export
collect : (farm : Farm a)
        -> (runRes : (ThreadID, IORef (BufferedChannel (WorkResult a))))
        -> IO (List a)
collect (MkFarm nWorkers _) (bundleThreadID, resRef) =
  do resList <- collect' [] nWorkers resRef
     putStrLn "Collected all results, waiting for worker threads to stop..."
     threadWait bundleThreadID
     putStrLn "All workers stopped, returning results."
     pure resList
  where
    collect' : List a -> Nat -> IORef (BufferedChannel (WorkResult a)) -> IO (List a)
    collect' acc 0 _ = pure acc
    collect' acc (S k) resRef =
      do (MkDPair resChan recv) <- becomeReceiver Blocking resRef
         workRes <- recv resChan
         -- (note: having `assert_smaller` here doesn't work)
         case workRes of
              (RES val) => do let resRef' = assert_smaller resRef resRef
                              collect' (val :: acc) (S k) resRef'
              DONE => do let resRef' = assert_smaller resRef resRef
                         collect' acc k resRef'   -- one worker done, so reduce k

