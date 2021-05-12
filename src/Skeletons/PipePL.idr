module Skeletons.PipePL

import System
import System.Concurrency
import System.Concurrency.BufferedChannel

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
     -> (inRef : IORef (BufferedChannel (PipelineData a) (PipelineData () )))
     -> (outRef : IORef (BufferedChannel (PipelineData b) (PipelineData () )))
     -> IO ()
loop _ DONE _ outRef =
  do outPipe <- makeReceiver outRef     -- Slightly confusing, but this process
                                        -- is the "receiver" for the input to
                                        -- the other process; might help to
                                        -- think dual ( dual ( pipe ) ) ?
     sendAndSignal outPipe $ prepare DONE

loop stage@(MkDStep f) next inRef outRef =
  do inPipe <- makeSender inRef       -- We're the sender/responder on this chan
     outPipe <- makeReceiver outRef

     sendAndSignal outPipe $ prepare (f next)
     (Just msg) <- await inPipe
        | Nothing => assert_total $ idris_crash "Await should never get Nothing"
     let next' = unsafeOpen msg     -- FIXME: not actually unsafe
     loop stage next' inRef outRef  -- FIXME: partial


||| Given a Pipeline and a Channel which supplies input for the first stage,
||| run each stage of the Pipeline in parallel, linking them up using Channels.
runDPipeline : {y : _}
             -> (pl : DPipeline x y)
             -> (inRef : IORef (BufferedChannel (PipelineData x)
                                                (PipelineData () )))
             -> IO (ThreadID, IORef (BufferedChannel (PipelineData y)
                                                     (PipelineData () ) ))
runDPipeline (DEndpoint lastly) inRef =
  do outRef <- makeBufferedChannel {a=(PipelineData y)} {b=(PipelineData () )}
                                               -- FIXME: ^ This seems cursed...
                                               -- But then again, the other
                                               -- process will never be sending
                                               -- something back...
     inPipe <- makeSender inRef

     (Just msg) <- await inPipe
        | Nothing => assert_total $ idris_crash "Await should never get Nothing"
     let input = unsafeOpen msg   -- FIXME: not actually unsafe
     threadID <- fork $ loop lastly input inRef outRef
     pure (threadID, outRef)

runDPipeline (DStage {b} thisStage continuation) inRef =
  do linkRef <- makeBufferedChannel {a=(PipelineData b)} {b=(PipelineData () )}
     inPipe <- makeSender inRef

     (Just msg) <- await inPipe
        | Nothing => assert_total $ idris_crash "Await should never get Nothing"
     let input = unsafeOpen msg     -- FIXME: not actually unsafe
     doWeCare <- fork $ loop thisStage input inRef linkRef
     runDPipeline continuation linkRef


||| n natural numbers on outChan, in descending order
countdown : (n : Nat)
          -> (outRef : IORef (BufferedChannel (PipelineData Nat)
                                              (PipelineData () ) ))
          -> IO ()
countdown 0 outRef =
  do outPipe <- makeReceiver outRef
     sendAndSignal outPipe $ prepare DONE

countdown (S k) outRef =
  do outPipe <- makeReceiver outRef
     sendAndSignal outPipe $ prepare (NEXT (S k))
     countdown k outRef


||| n natural numbers on outChan, in ascending order
nats : (n : Nat)
     -> (outRef : IORef (BufferedChannel (PipelineData Nat)
                                         (PipelineData () ) ))
     -> IO ()
nats n outRef = nats' n Z outRef
  where
    nats' : Nat
          -> Nat
          -> IORef (BufferedChannel (PipelineData Nat) (PipelineData ()) )
          -> IO ()
    nats' 0 k oRef = do outPipe <- makeReceiver oRef
                        sendAndSignal outPipe $ prepare (NEXT k)
                        sendAndSignal outPipe $ prepare DONE

    nats' (S j) k oRef = do outPipe <- makeReceiver oRef
                            sendAndSignal outPipe $ prepare (NEXT k)
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
  do inRef <- makeBufferedChannel {a=(PipelineData Nat)} {b=(PipelineData ())}
     nats 10 inRef
     (tid, resRef) <- runDPipeline squarePL inRef
     resPipe <- makeSender resRef
     (Just msg) <- await resPipe
        | Nothing => assert_total $ idris_crash "Await should never get Nothing"
     let firstThing = unsafeOpen msg    -- FIXME: Not actually unsafe
     printLoop firstThing resRef
     putStrLn "Main done"
  where
    partial
    printLoop : PipelineData String
              -> IORef (BufferedChannel (PipelineData String)
                                        (PipelineData ()    ))
              -> IO ()
    printLoop DONE _ = putStrLn "Received DONE"
    printLoop (NEXT x) rRef = do putStrLn x
                                 rPipe <- makeSender rRef
                                 (Just msg') <- await rPipe
                                    | Nothing => assert_total $
                                                 idris_crash "Got Nothing"
                                 let next = unsafeOpen msg'
                                 printLoop next rRef

