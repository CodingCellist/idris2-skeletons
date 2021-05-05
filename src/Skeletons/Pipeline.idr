module Skeletons.Pipeline

import System.Concurrency
-- import Skeletons.Common

-- FIXME: Needed?
||| A way of denoting the next bit of input, or the end of a pipeline.
data PipelineData : Type -> Type where
  Next : a -> PipelineData a
  DONE : PipelineData d

||| A single step in a pipeline, taking an input and producing an output
data PipelineStep : Type -> Type -> Type where
  MkStep : (a -> b) -> PipelineStep a b

||| A pipeline consisting of either just an Endpoint, or a series of steps
||| terminating in an Endpoint.
export
data Pipeline : Type -> Type -> Type where
  Endpoint : (end : PipelineStep a b) -> Pipeline a b
  Step     : (now : PipelineStep a b)
           -> (then_ : Pipeline b c)
           -> Pipeline a c


||| Create a pipeline which only does the thing specified by f.
export
makePipeline : (f : (a -> b)) -> Pipeline a b
makePipeline f = Endpoint $ MkStep f


||| Add a new step to an existing pipeline
export
addStep : (pl : Pipeline a b) -> (newStep : (b -> c)) -> Pipeline a c
addStep (Endpoint end) newStep =
  Step end (Endpoint (MkStep newStep))

addStep (Step now then_) newStep =
  Step now (addStep then_ newStep)

infixl 8 |->

||| Shorthand for `addStep`
(|->) : Pipeline a b -> (b -> c) -> Pipeline a c
(|->) = addStep


||| Run a pipeline, returning a ThreadID representing the final stage, and a
||| Channel to receive the output from the final stage on.
runPipeline : (input : Channel i) -> Pipeline i o -> IO (ThreadID, Channel o)
runPipeline input (Endpoint (MkStep endFunc)) =
  do output <- makeChannel
     threadID <- fork $ do inp <- channelGet input
                           let res = endFunc inp
                           channelPut output res
     pure (threadID, output)

runPipeline input (Step (MkStep nowFunc) then_) =
  do output <- makeChannel
     -- fork the `now` step
     threadID <- fork $ do inp <- channelGet input
                           let res = nowFunc inp
                           channelPut output res
     -- only partially done; still need to do the rest, using the new output
     runPipeline output then_

-- runPipeline (Endpoint end) = ?runPipeline_rhs_1
-- runPipeline (Step now then_) = ?runPipeline_rhs_2

-- EXAMPLE --

fun1 : Int -> Int
fun1 i = i

fun2 : Int -> Int
fun2 i = 2 * i

fun3 : Int -> Int
fun3 i = i + 1

ex1 : Pipeline Int Int
ex1 =
  let
    part1 = makePipeline fun1
    part2 = addStep part1 fun2
  in
    part2

ex2 : Pipeline Int Int
ex2 = makePipeline fun1
      |-> fun2
      |-> fun3


testEx1 : IO ()
testEx1 = do i <- makeChannel
             (_, o) <- runPipeline i ex1
             channelPut i 2
             res <- channelGet o
             putStrLn $ show res

testEx2 : IO ()
testEx2 = do i <- makeChannel
             (_, o) <- runPipeline i ex2
             channelPut i 2
             res <- channelGet o
             putStrLn $ show res

