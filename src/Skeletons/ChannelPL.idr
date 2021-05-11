module Skeletons.ChannelPL

import System
import System.Concurrency

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
  DStage    : (thisStage : DPipelineStage a b)
            -> (continuation : DPipeline b c)
            -> DPipeline a c

||| Declare a new pipeline, with initStage as its only Stage.
initPipeline : (initStage : PipelineData a -> PipelineData b) -> DPipeline a b
initPipeline initStage = DEndpoint $ MkDStep initStage

||| Add a Stage to the end of an existing Pipeline.
addStage : (pl : DPipeline a b)
         -> (newStage : PipelineData b -> PipelineData c)
         -> DPipeline a c
addStage (DEndpoint lastly) newStage =
  DStage lastly (DEndpoint $ MkDStep newStage)  -- newStage becomes new `lastly`
addStage (DStage thisStage continuation) newStage =
  DStage thisStage $ addStage continuation newStage

infixl 8 |=>

||| Shorthand for `addStage`
(|=>) : DPipeline a b -> (PipelineData b -> PipelineData c) -> DPipeline a c
(|=>) = addStage

||| Given some input, process it and keep receiving input. If the input was
||| initially DONE / When the loop eventually gets a DONE, no processing is
||| computed and the DONE is simply passed along on the outChan Channel.
loop : (stage : (DPipelineStage a b))
     -> (plData : PipelineData a)
     -> (inChan : Channel (PipelineData a))
     -> (outChan : Channel (PipelineData b))
     -> IO ()
loop _                 DONE _      outChan = channelPut outChan DONE
loop stage@(MkDStep f) next inChan outChan =
  do channelPut outChan (f next)
     next' <- channelGet inChan
     assert_total $ loop stage next' inChan outChan
     -- ^ FIXME: Is this correct/appropriate use of `assert_total`?
     --          Probably not...

||| Given a Pipeline and a Channel which supplies input for the first stage,
||| run each stage of the Pipeline in parallel, linking them up using Channels.
runDPipeline : (pl : DPipeline x y)
             -> (inChan : Channel (PipelineData x))
             -> IO (ThreadID, Channel (PipelineData y))
runDPipeline (DEndpoint lastly) inChan =
  do outChan <- makeChannel
     input <- channelGet inChan
     threadID <- fork $ loop lastly input inChan outChan
     pure (threadID, outChan)

runDPipeline (DStage thisStage continuation) inChan =
  do link <- makeChannel    -- Channel b
     input <- channelGet inChan   -- Data x
     doWeCare <- fork $ loop thisStage input inChan link    -- x -> b
     -- continuation : b -> y
     runDPipeline continuation link

||| n natural numbers on outChan, in descending order
countdown : (n : Nat) -> (outChan : Channel (PipelineData Nat)) -> IO ()
countdown 0 outChan = channelPut outChan DONE
countdown (S k) outChan = do channelPut outChan $ NEXT (S k)
                             countdown k outChan

||| n natural numbers on outChan, in ascending order
nats : (n : Nat) -> (outChan : Channel (PipelineData Nat)) -> IO ()
nats n outChan = nats' n Z outChan
  where
    nats' : Nat -> Nat -> Channel (PipelineData Nat) -> IO ()
    nats' 0 k c = do channelPut c $ NEXT k
                     channelPut c DONE
    nats' (S j) k c = do channelPut c $ NEXT k
                         nats' j (S k) c

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
  do inChan <- makeChannel
     ignore $ fork $ nats 10 inChan   -- channels block on Put until Get... O.o
     (tid, resChan) <- runDPipeline squarePL inChan
     firstThing <- channelGet resChan
     printLoop firstThing resChan
     putStrLn "Main done"
  where
    partial
    printLoop : PipelineData String -> Channel (PipelineData String) -> IO ()
    printLoop DONE _ = putStrLn "Recieved DONE"
    printLoop (NEXT x) c = do putStrLn x
                              next <- channelGet c
                              printLoop next c

