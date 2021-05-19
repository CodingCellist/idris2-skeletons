module Skeletons.Farm

import System
import Data.List

import System.Concurrency.DirectionalChannel

%default total

||| A worker can either get another task or an indication that there is no more
||| work.
data WorkUnit : Type -> Type where
  TASK : Lazy task -> WorkUnit task
  STOP : WorkUnit _

data WorkResult : Type -> Type where
  RES : res -> WorkResult res
  DONE : WorkResult _

||| A Farm has a max number of workers, and a list of work to be done
data Farm : Type -> Type where
  MkFarm : (nWorkers : Nat)
         -> (work : List (WorkUnit resTy))
         -> Farm resTy

||| A basic unit of work in a farm. Retrieves work from the channel referenced
||| in workRef, sending the results to outRef, until a `STOP` instruction is
||| received.
worker : (workRef : IORef (DirectionalChannel (WorkUnit a)))
       -> (outRef : IORef (DirectionalChannel a))
       -> IO ()
worker workRef outRef =
  do (MkDPair workChan recv) <- becomeReceiver workRef
     (MkDPair outChan send) <- becomeSender outRef
     (TASK task) <- recv workChan
        | STOP => pure ()
     send outChan task
     -- FIXME: v  Correct use of assert_total? I'm not convinced...
     assert_total $ worker workRef outRef

||| Given a list of ThreadIDs, fork a single thread whose sole purpose is
||| waiting on all those threads to finish.
waitOnThreadBundle : (ts : List ThreadID)
                   -> IO ThreadID
waitOnThreadBundle ts = fork $ ignore (traverse (\t => threadWait t) ts)

||| Given a list of work, create a DirectionalChannel containing all the work.
loadWork : {a : _}
         -> (farm : Farm a)
         -> IO (IORef (DirectionalChannel (WorkUnit a)))
loadWork (MkFarm nWorkers work) =
  do putStr "Loading work... "
     workRef <- makeDirectionalChannel
     (MkDPair workChan send) <- becomeSender workRef
     ignore $ traverse (\w => send workChan w) work
     -- FIXME: v  Nicer way to do this?
     ignore $ for (replicate nWorkers STOP) (\stop => send workChan stop)
     putStrLn "Done."
     pure workRef

spawnWorkers : (nWorkers : Nat)
             -> (workRef : IORef (DirectionalChannel (WorkUnit a)))
             -> (outRef : IORef (DirectionalChannel a))
             -> IO (List ThreadID)
spawnWorkers 0 _ _ = pure []
spawnWorkers (S k) workRef outRef =
  do workerThreadID <- fork $ worker workRef outRef
     workerThreadIDs <- spawnWorkers k workRef outRef
     pure (workerThreadID :: workerThreadIDs)

||| Run a farm, spawning n threads where n is the number of workers in the farm
runFarm : {a : _} -> Farm a -> IO (ThreadID, IORef (DirectionalChannel a))
runFarm farm@(MkFarm nWorkers work) =
  do outRef <- makeDirectionalChannel
     workRef <- loadWork farm
     workerThreadIDs <- spawnWorkers nWorkers workRef outRef
     putStrLn $ "Spawned " ++ show nWorkers ++ " workers."
     bundleThreadID <- waitOnThreadBundle workerThreadIDs
     pure (bundleThreadID, outRef)

||| Retrieve all the output from a farm that has been run.
collect : (farm : Farm a)
        -> (runRes : (ThreadID, IORef (DirectionalChannel a)))
        -> IO (List a)
collect (MkFarm nWorkers _) (bundleThreadID, resRef) =
  do resList <- collect' nWorkers resRef
     threadWait bundleThreadID
     pure resList
  where
    collect' : Nat -> IORef (DirectionalChannel a) -> IO (List a)
    collect' 0 _ = pure []
    collect' (S k) resRef =
      do (MkDPair resChan recv) <- becomeReceiver resRef
         res <- recv resChan
         case res of
              case_val => ?collect'_rhs_2
     

ack : Nat -> Nat -> Nat
ack 0 j = (S j)
ack (S k) 0 = ack k 1
ack (S k) (S j) = ack k $ ack (S k) j

ackList : List (WorkUnit Nat)
ackList = [TASK (ack 2 2), TASK (ack 3 7), TASK (ack 3 6), TASK (ack 3 7)]

ackFarm : Farm Nat
ackFarm = (MkFarm 6 ackList)

ackMain : IO ()
ackMain =
  do putStrLn "Starting..."
     (bundleThreadID, resRef) <- runFarm ackFarm
     putStrLn "Farm running."
     (MkDPair resChan recv) <- becomeReceiver resRef
     res <- recv resChan
     putStrLn $ "First res: " ++ show res
     threadWait bundleThreadID
     putStrLn "DONE"

