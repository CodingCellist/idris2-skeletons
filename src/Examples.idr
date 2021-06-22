import Skeletons
import System.Concurrency.BufferedChannel

import Data.List

------------------
-- Farm Example --
------------------

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
ackFarm = initFarm 8 ackList

farmMain : IO ()
farmMain =
  do putStrLn "Starting..."
     (bundleThreadID, resRef) <- runFarm ackFarm
     putStrLn "Farm running."
     (MkDPair resChan recv) <- becomeReceiver Blocking resRef
     resList <- collect ackFarm (bundleThreadID, resRef)
     putStrLn $ "Results: " ++ show resList
     putStrLn "DONE"


----------------------
-- Pipeline Example --
----------------------

||| n natural numbers on outChan, in descending order
countdown : (n : Nat)
          -> (outRef : IORef (BufferedChannel (PipelineData Nat)))
          -> IO ()
countdown 0 outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send Signal outChan DONE

countdown (S k) outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send Signal outChan $ NEXT (S k)
     countdown k outRef


||| n natural numbers on outChan, in ascending order
nats : (n : Nat)
     -> (outRef : IORef (BufferedChannel (PipelineData Nat)))
     -> IO ()
nats n outRef = nats' n Z outRef
  where
    nats' : Nat -> Nat -> IORef (BufferedChannel (PipelineData Nat)) -> IO ()
    nats' 0 k oRef =
      do (MkDPair outChan send) <- becomeSender oRef
         send Signal outChan $ NEXT k
         send Signal outChan DONE

    nats' (S j) k oRef =
      do (MkDPair outChan send) <- becomeSender oRef
         send Signal outChan $ NEXT k
         nats' j (S k) oRef


||| Squares its input
squareStage : PipelineData Nat -> PipelineData Nat
squareStage DONE = DONE
squareStage (NEXT x) = NEXT (x * x)

||| Converts its input to a String
showStage : Show a => PipelineData a -> PipelineData String
showStage DONE = DONE
showStage (NEXT x) = NEXT (show x)

||| Prints its input
printStage : PipelineData String -> PipelineData (IO ())
printStage DONE = DONE
printStage (NEXT x) = NEXT (putStrLn x)

squarePL : Pipeline Nat String
squarePL = initPipeline squareStage
           |> showStage

partial
pipelineMain : IO ()
pipelineMain =
  do inRef <- makeBufferedChannel
     nats 10 inRef
     (tid, resRef) <- runPipeline squarePL inRef
     (MkDPair resChan recv) <- becomeReceiver Blocking resRef
     firstRes <- recv resChan
     printLoop firstRes (MkDPair resChan recv)
     putStrLn "Main done."
  where
    partial
    printLoop : PipelineData String
              -> (resChan : BufferedChannel (PipelineData String)
                            ** BlockingReceiver (PipelineData String))
              -> IO ()
    printLoop DONE _ = putStrLn "Received DONE"
    printLoop (NEXT s) resDPair@(MkDPair resChan recv) =
      do putStrLn s
         next <- recv resChan
         printLoop next resDPair

