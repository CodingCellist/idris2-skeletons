module Skeletons.Farm

import System
import Data.List

import System.Concurrency.BufferedChannel

%default total

||| A worker can either get another task or an indication that there is no more
||| work.
data WorkUnit : Type -> Type where
  TASK : Lazy task -> WorkUnit task
  STOP : WorkUnit _

data WorkResult : Type -> Type where
  RES : val -> WorkResult val
  DONE : WorkResult _

||| A Farm has a max number of workers, and a list of work to be done
data Farm : Type -> Type where
  MkFarm : (nWorkers : Nat)
         -> (work : List (WorkUnit resTy))
         -> Farm resTy

||| A basic unit of work in a farm. Retrieves work from the channel referenced
||| in workRef, sending the results to outRef, until a `STOP` instruction is
||| received.
worker : (workRef : IORef (BufferedChannel (WorkUnit a)))
       -> (outRef : IORef (BufferedChannel (WorkResult a)))
       -> IO ()
worker workRef outRef =
  do (MkDPair workChan recv) <- becomeReceiver Blocking workRef
     (MkDPair outChan send) <- becomeSender Signal outRef
     (TASK task) <- recv workChan
        | STOP => send outChan DONE
     send outChan (RES task)   -- TASK is Lazy, but RES is not  => evaluation!
     -- FIXME: v  Correct use of assert_total? I'm not convinced...
     assert_total $ worker workRef outRef

||| Given a list of ThreadIDs, fork a single thread whose sole purpose is
||| waiting on all those threads to finish.
waitOnThreadBundle : (ts : List ThreadID)
                   -> IO ThreadID
waitOnThreadBundle ts = fork $ ignore (traverse (\t => threadWait t) ts)

||| Given a list of work, create a BufferedChannel containing all the work.
loadWork : (farm : Farm a)
         -> IO (IORef (BufferedChannel (WorkUnit a)))
loadWork (MkFarm nWorkers work) =
  do putStr "Loading work... "
     workRef <- makeBufferedChannel
     (MkDPair workChan send) <- becomeSender Signal workRef
     ignore $ traverse (\w => send workChan w) work
     -- FIXME: v  Nicer way to do this?
     ignore $ for (replicate nWorkers STOP) (\stop => send workChan stop)
     putStrLn "Done."
     pure workRef

spawnWorkers : (nWorkers : Nat)
             -> (workRef : IORef (BufferedChannel (WorkUnit a)))
             -> (outRef : IORef (BufferedChannel (WorkResult a)))
             -> IO (List ThreadID)
spawnWorkers 0 _ _ = pure []
spawnWorkers (S k) workRef outRef =
  do workerThreadID <- fork $ worker workRef outRef
     workerThreadIDs <- spawnWorkers k workRef outRef
     pure (workerThreadID :: workerThreadIDs)

||| Run a farm, spawning n threads where n is the number of workers in the farm
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
         case workRes of
              -- FIXME     v  Correct use of `assert_total`?
              (RES val) => assert_total $ collect' (val :: acc) (S k) resRef
              DONE => collect' acc k resRef   -- one worker done, so reduce k
     

-------------
-- Example --
-------------

ack : Nat -> Nat -> Nat
ack 0 j = (S j)
ack (S k) 0 = ack k 1
ack (S k) (S j) = ack k $ ack (S k) j

ackList : List (WorkUnit Nat)
ackList = replicate 16 (TASK (ack 4 1))
--ackList = [TASK (ack 2 2), TASK (ack 4 1), TASK (ack 3 12), TASK (ack 4 1)]
--               ^ fast          ^ slow          ^ slow-ish      ^ slow

ackSeq : IO ()
ackSeq = do putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1
            putStrLn $ show $ ack 4 1

ackFarm : Farm Nat
ackFarm = (MkFarm 8 ackList)

ackMain : IO ()
ackMain =
  do putStrLn "Starting..."
     (bundleThreadID, resRef) <- runFarm ackFarm
     putStrLn "Farm running."
     (MkDPair resChan recv) <- becomeReceiver Blocking resRef
     resList <- collect ackFarm (bundleThreadID, resRef)
     putStrLn $ "Results: " ++ show resList
     putStrLn "DONE"

