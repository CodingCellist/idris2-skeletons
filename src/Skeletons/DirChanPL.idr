module Skeletons.DirChanPL

import System
import System.Concurrency
import System.Concurrency.DirectionalChannel

%default total

||| Representation of the data in a pipeline. Data flows through the stage(s)
||| using NEXT, until we are DONE.
data PipelineData : Type -> Type where
  DONE : PipelineData a
  NEXT : a -> PipelineData a

||| A step in a pipeline, processing a type of PipelineData.
data DPipelineStage : Type -> Type -> Type where
  MkDStep : (PipelineData a -> PipelineData b) -> DPipelineStage a b

||| A Data Pipeline consists of either its Endpoint, where the final processing
||| step happens; or a Stage where some processing happens, followed by a
||| continuation Pipeline where the rest of the processing happens.
data DPipeline : Type -> Type -> Type where
  DEndpoint : (lastly : DPipelineStage a b) -> DPipeline a b
  DStage    : {b : Type}
            -> (thisStage : DPipelineStage a b)
            -> (continuation : DPipeline b c)
            -> DPipeline a c


||| Declare a new pipeline, with initStage as its only Stage.
initPipeline : (initStage : PipelineData a -> PipelineData b) -> DPipeline a b
initPipeline initStage = DEndpoint $ MkDStep initStage


||| Add a Stage to the end of an existing Pipeline.
addStage : {b : _}
         -> (pl : DPipeline a b)
         -> (newStage : PipelineData b -> PipelineData c)
         -> DPipeline a c
addStage (DEndpoint lastly) newStage =
  DStage lastly (DEndpoint $ MkDStep newStage)  -- newStage becomes new `lastly`

addStage (DStage thisStage continuation) newStage =
  DStage thisStage $ addStage continuation newStage


infixl 8 |=>

||| Shorthand for `addStage`
(|=>) : {b : _} -> DPipeline a b -> (PipelineData b -> PipelineData c) -> DPipeline a c
(|=>) = addStage


||| Given some input, process it and keep receiving input. If the input was
||| initially DONE / When the loop eventually gets a DONE, no processing is
||| computed and the DONE is simply passed along on the outChan Channel.
partial
loop : (stage : (DPipelineStage a b))
     -> (plData : PipelineData a)
     -> (inRef : IORef (DirectionalChannel (PipelineData a) ))
     -> (outRef : IORef (DirectionalChannel (PipelineData b) ))
     -> IO ()
loop _ DONE _ outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send outChan DONE

loop stage@(MkDStep f) next inRef outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     (MkDPair inChan  recv) <- becomeReceiver inRef
     
     send outChan (f next)
     next' <- recv inChan
     loop stage next' inRef outRef


||| Given a Pipeline and a Channel which supplies input for the first stage,
||| run each stage of the Pipeline in parallel, linking them up using Channels.
runDPipeline : {y : _}
             -> (pl : DPipeline x y)
             -> (inRef : IORef (DirectionalChannel (PipelineData x)))
             -> IO (ThreadID, IORef (DirectionalChannel (PipelineData y)))
runDPipeline (DEndpoint lastly) inRef =
  do outRef <- makeDirectionalChannel
     (MkDPair outChan send) <- becomeSender outRef
     (MkDPair inChan  recv) <- becomeReceiver inRef

     input <- recv inChan
     threadID <- fork $ loop lastly input inRef outRef
     pure (threadID, outRef)

runDPipeline (DStage thisStage continuation) inRef =
  do linkRef <- makeDirectionalChannel
     (MkDPair inChan recv) <- becomeReceiver inRef

     input <- recv inChan
     doWeCare <- fork $ loop thisStage input inRef linkRef
     runDPipeline continuation linkRef


||| n natural numbers on outChan, in descending order
countdown : (n : Nat)
          -> (outRef : IORef (DirectionalChannel (PipelineData Nat)))
          -> IO ()
countdown 0 outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send outChan DONE

countdown (S k) outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send outChan $ NEXT (S k)
     countdown k outRef


||| n natural numbers on outChan, in ascending order
nats : (n : Nat)
     -> (outRef : IORef (DirectionalChannel (PipelineData Nat)))
     -> IO ()
nats n outRef = nats' n Z outRef
  where
    nats' : Nat -> Nat -> IORef (DirectionalChannel (PipelineData Nat)) -> IO ()
    nats' 0 k oRef =
      do (MkDPair outChan send) <- becomeSender oRef
         send outChan $ NEXT k
         send outChan DONE

    nats' (S j) k oRef =
      do (MkDPair outChan send) <- becomeSender oRef
         send outChan $ NEXT k
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

squarePL : DPipeline Nat String
squarePL = initPipeline squareStage
           |=> showStage

partial
squareMain : IO ()
squareMain =
  do inRef <- makeDirectionalChannel
     nats 10 inRef
     (tid, resRef) <- runDPipeline squarePL inRef
     (MkDPair resChan recv) <- becomeReceiver resRef
     firstRes <- recv resChan
     printLoop firstRes (MkDPair resChan recv)
     putStrLn "Main done."
  where
    partial
    printLoop : PipelineData String
              -> (resChan : DirectionalChannel (PipelineData String)
                            ** ReceiverFunc (PipelineData String))
              -> IO ()
    printLoop DONE _ = putStrLn "Received DONE"
    printLoop (NEXT s) resDPair@(MkDPair resChan recv) =
      do putStrLn s
         next <- recv resChan
         printLoop next resDPair
