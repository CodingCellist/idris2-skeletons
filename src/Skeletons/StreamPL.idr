module Skeletons.StreamPL

import System
import System.Concurrency

-- FIXME: Is this approach better? Or is it better to leave streams up to the
--        user?

||| A way of denoting the next bit of input, or the end of a pipeline.
data PipelineData : Type -> Type where
  DONE : PipelineData d
              -- FIXME: need rest?
  Next : a -> (rest : PipelineData a) -> PipelineData a   

||| A single step in a pipeline, taking an input and producing an output
data DPipelineStep : Type -> Type -> Type where
  MkDStep : (PipelineData a -> PipelineData b) -> DPipelineStep a b

||| A pipeline consisting of either just an Endpoint, or a series of steps
||| terminating in an Endpoint.
export
data DPipeline : Type -> Type -> Type where
  DEndpoint : (end : DPipelineStep a b) -> DPipeline a b
  DStep     : (now : DPipelineStep a b)
            -> (then_ : DPipeline b c)
            -> DPipeline a c

makeDPipeline : (f : (PipelineData a -> PipelineData b)) -> DPipeline a b
makeDPipeline f = DEndpoint $ MkDStep f

addDStep : (dPl : DPipeline a b)
         -> (newStep : (PipelineData b -> PipelineData c))
         -> DPipeline a c
addDStep (DEndpoint end) newStep =
  DStep end (DEndpoint (MkDStep newStep))

addDStep (DStep now then_) newStep =
  DStep now (addDStep then_ newStep)

total
loop : (PipelineData a -> PipelineData b)
     -> (aThing : PipelineData a)
     -> (inChan : Channel (PipelineData a))
     -> (outChan : Channel (PipelineData b))
     -> IO ()
loop f DONE inChan outChan = channelPut outChan DONE
loop f (Next x rest) inChan outChan = ?loop_rhs_2

--runDPipeline' : (inChan : Channel (PipelineData a))
--              -> DPipeline a b
--              -> IO (ThreadID, Channel (PipelineData b))
--runDPipeline' inChan (DEndpoint end) =
--  do outChan <- makeChannel
--     (Next input rest) <- channelGet inChan
--        | DONE => do channelPut outChan $ Next (end DONE) DONE
--     channelPut outChan $ Next (end input) (end rest)
--     ?runDPipeline'_rhs_1
--runDPipeline' inChan (DStep now then_) = ?runDPipeline'_rhs_2

--loop f inChan outChan =
--  do input <- channelGet inChan
--     case input of
--          DONE => channelPut outChan DONE
--          _    => do channelPut outChan $ f input
--                     loop f inChan outChan

runDPipeline : (inChan : Channel (PipelineData a))
             -> DPipeline a b
             -> IO (ThreadID, Channel (PipelineData b))
runDPipeline inChan (DEndpoint (MkDStep endFunc)) =
  do outChan <- makeChannel
     --threadID <- fork $ loop endFunc input output
     threadID <- fork ?todo
     pure (threadID, outChan)

--  do o <- makeChannel
--     threadID <- fork $ do (Next inp) <- channelGet input
--                              | DONE => pure ()
--                           let res = endFunc inp
--                           pure () -- TODO
runDPipeline input (DStep now then_) = ?runDPipeline_rhs_2

generator : Nat -> PipelineData Int
generator 0 = DONE
generator (S k) = Next (cast (S k)) (generator k)

channelGenerator : Nat -> (outChan : Channel (PipelineData Nat)) -> IO ()
channelGenerator 0 outChan = channelPut outChan DONE
channelGenerator (S k) outChan = do channelPut outChan $ Next (S k) DONE
                                    channelGenerator k outChan

doubler : PipelineData Int -> PipelineData Int
doubler DONE = DONE
doubler (Next x rest) = Next (2 * x) (doubler rest)

adder : PipelineData Int -> PipelineData Int
adder DONE = DONE
adder (Next x rest) =
  case adder rest of
       DONE => Next x DONE
       (Next y rest') => Next (x + y) (adder rest')

--dfun1 : PipelineData Int -> PipelineData Int
--dfun1 (Next x) = Next x
--dfun1 DONE = DONE
--
--dfun2 : PipelineData Int -> PipelineData Int
--dfun2 (Next x) = Next (x * 2)
--dfun2 DONE = DONE
--
--dfun3 : PipelineData Int -> PipelineData Int
--dfun3 (Next x) = Next (x + 1)
--dfun3 DONE = DONE

dex1 : DPipeline Int Int
dex1 = ?dex1_rhs

