module Skeletons.Pipeline

import System
import System.Concurrency
import System.Concurrency.BufferedChannel

%default total

||| Representation of the data in a pipeline. Data flows through the stage(s)
||| using NEXT, until we are DONE.
public export
data PipelineData : Type -> Type where
  DONE : PipelineData a
  NEXT : a -> PipelineData a

||| A stage in a pipeline, processing a type of @PipelineData@.
data PipelineStage : Type -> Type -> Type where
  MkDStep : (PipelineData a -> PipelineData b) -> PipelineStage a b

||| A Pipeline from a -> b is a skeleton typically consisting of multiple
||| independent stages, with the final stage producing something of type `b`,
||| and the other stages doing intermediary work towards this. Since the stages
||| are independent, each stage can be run in parallel.
export
data Pipeline : Type -> Type -> Type where
  -- A Data Pipeline consists of either its Endpoint, where the final processing
  -- step happens; or a Stage where some processing happens, followed by a
  -- continuation Pipeline where the rest of the processing happens.
  DEndpoint : (lastly : PipelineStage a b) -> Pipeline a b
  DStage    : (thisStage : PipelineStage a b)
            -> (continuation : Pipeline b c)
            -> Pipeline a c


||| Declare a new pipeline, with initStage as its only stage.
|||
||| @initStage A stage to use as the basis for a new pipeline.
export
initPipeline : (initStage : PipelineData a -> PipelineData b) -> Pipeline a b
initPipeline initStage = DEndpoint $ MkDStep initStage


||| Add a stage to the end of an existing @Pipeline@, changing the output-type
||| of the Pipeline.
|||
||| @pl       The Pipeline to add the stage to.
||| @newStage The stage to add.
export
addStage : (pl : Pipeline a b)
         -> (newStage : PipelineData b -> PipelineData c)
         -> Pipeline a c
addStage (DEndpoint lastly) newStage =
  DStage lastly (DEndpoint $ MkDStep newStage)  -- newStage becomes new `lastly`

addStage (DStage thisStage continuation) newStage =
  DStage thisStage $ addStage continuation newStage


infixl 8 |>

||| Shorthand for `addStage`.
export
(|>) : {b : _} -> Pipeline a b -> (PipelineData b -> PipelineData c) -> Pipeline a c
(|>) = addStage


||| Given some input, process it and keep receiving input. If the input was
||| initially `DONE` / When the loop eventually gets a `DONE`, no processing is
||| computed and the `DONE` is simply passed along on the `outChan`
||| BufferedChannel.
loop : (stage : (PipelineStage a b))
     -> (plData : PipelineData a)
     -> (inRef : IORef (BufferedChannel (PipelineData a) ))
     -> (outRef : IORef (BufferedChannel (PipelineData b) ))
     -> IO ()
loop _ DONE _ outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     send Signal outChan DONE

loop stage@(MkDStep f) next inRef outRef =
  do (MkDPair outChan send) <- becomeSender outRef
     (MkDPair inChan  recv) <- becomeReceiver Blocking inRef
     
     send Signal outChan (f next)
     next' <- recv inChan
     let inRef' = assert_smaller inRef inRef
     --           ^ Idris cannot know recv reduces the size of a shared channel
     loop stage next' inRef' outRef


||| Given a @Pipeline@ and a @BufferedChannel@ which supplies input for the
||| first stage, run each stage of the Pipeline in parallel, linking them up
||| using BufferedChannels. Returns the @ThreadID@ of the last stage in the
||| Pipeline, and an @IORef@ to a BufferedChannel over which to receive the
||| final results.
|||
||| @pl    The Pipeline to run.
||| @inRef An IORef to a BufferedChannel containing the input for the initial
|||        stage.
export
runPipeline : (pl : Pipeline x y)
             -> (inRef : IORef (BufferedChannel (PipelineData x)))
             -> IO (ThreadID, IORef (BufferedChannel (PipelineData y)))
runPipeline (DEndpoint lastly) inRef =
  do outRef <- makeBufferedChannel
     (MkDPair inChan  recv) <- becomeReceiver Blocking inRef

     input <- recv inChan
     threadID <- fork $ loop lastly input inRef outRef
     pure (threadID, outRef)

runPipeline (DStage thisStage continuation) inRef =
  do linkRef <- makeBufferedChannel
     (MkDPair inChan recv) <- becomeReceiver Blocking inRef

     input <- recv inChan
     doWeCare <- fork $ loop thisStage input inRef linkRef
     -- ^ I don't think we do...
     runPipeline continuation linkRef

