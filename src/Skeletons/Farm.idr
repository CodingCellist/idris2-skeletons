module Skeletons.Farm

import System
import Data.List

import System.Concurrency.DirectionalChannel

%default total

||| A worker can either get another task or an indication that there is no more
||| work.
data WorkUnit : Type -> Type where
  TASK : Lazy task -> WorkUnit task
  DONE : WorkUnit _

||| A Farm has a max number of workers, and a list of work to be done
data Farm : Type -> Type where
  MkFarm : (nWorkers : Nat)
         -> (work : List (WorkUnit resTy))
--         -> {auto 0 ok : NonEmpty work}
         -> Farm resTy

worker : (workRef : IORef (DirectionalChannel (WorkUnit a)))
       -> (outRef : IORef (DirectionalChannel a))
       -> IO ()
worker workRef outRef =
  do (MkDPair workChan recv) <- becomeReceiver workRef
     (MkDPair outChan send) <- becomeSender outRef
     (TASK task) <- recv workChan
        | DONE => pure ()
     send outChan task
     -- FIXME: v  Correct use of assert_total? I'm not convinced...
     assert_total $ worker workRef outRef

||| Given a list of ThreadIDs, fork a single thread whose sole purpose is
||| waiting on all those threads to finish.
waitOnThreadBundle : (ts : List ThreadID)
--                   -> {auto 0 ok : NonEmpty ts}
                   -> IO ThreadID
waitOnThreadBundle ts = fork $ ignore (traverse (\t => threadWait t) ts)

||| Given a list of work, create a DirectionalChannel containing all the work.
loadWork : {a : _}
         -> (work : List (WorkUnit a))
         -> IO (IORef (DirectionalChannel (WorkUnit a)))
loadWork work =
  do putStr "Loading work... "
     workRef <- makeDirectionalChannel
     (MkDPair workChan send) <- becomeSender workRef
     ignore $ traverse (\w => send workChan w) work
     putStrLn "Done."
     pure workRef

spawnWorkers : (nWorkers : Nat)
             -> (workRef : IORef (DirectionalChannel (WorkUnit a)))
             -> (outRef : IORef (DirectionalChannel a))
             -> IO ()
spawnWorkers 0 _ _ = pure ()
spawnWorkers (S k) workRef outRef =
  do workerThreadID <- fork $ worker workRef outRef
     spawnWorkers k workRef outRef

||| Run a farm, spawning n threads where n is the number of workers in the farm
runFarm : {a : _} -> Farm a -> IO (IORef (DirectionalChannel a))
runFarm farm@(MkFarm nWorkers work) =
  do outRef <- makeDirectionalChannel
     workRef <- loadWork work
     spawnWorkers nWorkers workRef outRef
     putStrLn $ "Spawned " ++ show nWorkers ++ " workers."
     pure outRef

ack : Nat -> Nat -> Nat
ack 0 j = (S j)
ack (S k) 0 = ack k 1
ack (S k) (S j) = ack k $ ack (S k) j

ackList : List (WorkUnit Nat)
ackList = [TASK (ack 4 2), TASK (ack 4 2), TASK (ack 4 2), TASK (ack 4 2)]

ackFarm : Farm Nat
ackFarm = (MkFarm 6 ackList)

ackMain : IO ()
ackMain =
  do putStrLn "Starting..."
     resRef <- runFarm ackFarm
     putStrLn "Started farm."
     (MkDPair resChan recv) <- becomeReceiver resRef
     res <- recv resChan
     putStrLn $ "Res: " ++ show res
     putStrLn "DONE"

