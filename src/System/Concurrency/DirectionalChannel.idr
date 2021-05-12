-- Idris 2

module System.Concurrency.DirectionalChannel

import public Data.IORef
import System.Concurrency

import public System.Concurrency.Queue

%default total

||| A channel for inter-process communication where one side is the sender, and
||| the other is the receiver.
export
data DirectionalChannel : Type -> Type where
  MkDirectionalChannel : (condLock : Mutex)
                       -> (condVar : Condition)
                       -> (qRef    : IORef (Queue a))
                       -> DirectionalChannel a

||| Create a new DirectionalChannel and obtain the reference to it.
export
makeDirectionalChannel : {a : _} -> IO (IORef (DirectionalChannel a))
makeDirectionalChannel =
  do cl <- makeMutex
     cv <- makeCondition
     q  <- makeQueue
     newIORef (MkDirectionalChannel cl cv q)

||| The type of a sender function is something which takes a channel and a thing
||| to send, and produces an empty IO action, i.e. the sending of the message.
public export
SenderFunc : Type -> Type
SenderFunc a = DirectionalChannel a -> a -> IO ()

||| Send a thing on the directed channel and signal its internal condition
||| variable.
sendAndSignal : SenderFunc a
sendAndSignal (MkDirectionalChannel _ condVar qRef) msg =
  do enqueue qRef $ prepare msg     -- FIXME: Can probably remove `Message` type
     conditionSignal condVar

||| Send a thing on the directed channel and broadcast its internal condition
||| variable.
sendAndBroadcast : SenderFunc a
sendAndBroadcast (MkDirectionalChannel _ condVar qRef) msg =
  do enqueue qRef $ prepare msg
     conditionBroadcast condVar

||| The type of a receiver function is something which takes a channel and
||| produces an IO action containing a thing on the channel, i.e. the receiving
||| of the message.
public export
ReceiverFunc : Type -> Type
ReceiverFunc a = DirectionalChannel a -> IO a

||| Crash Idris with a message signalling that something went wrong in terms of
||| the fundamental guarantees of condition variables.
awaitCrash : IO a
awaitCrash =
  assert_total $ idris_crash "Await somehow got Nothing despite waiting on a CV"

||| Block on the directed channel's internal condition variable until a message
||| arrives, at which point, retrieve the contents.
await : ReceiverFunc a
await (MkDirectionalChannel condLock condVar qRef) =
  do (Just msg) <- dequeue qRef
        -- if there wasn't anything in the queue, wait until something appears
        | Nothing => do mutexAcquire condLock
                        conditionWait condVar condLock
                        (Just msg') <- dequeue qRef
                           | Nothing => awaitCrash
                        mutexRelease condLock
                        pure $ unsafeOpen msg'
     pure $ unsafeOpen msg   -- < ^            --  FIXME: Not really unsafe

||| Given a reference to a directed channel, obtain the ability to send on the
||| channel.
export
becomeSender : IORef (DirectionalChannel a)
             -> IO (dc : DirectionalChannel a ** (SenderFunc a))
becomeSender dcRef =
  do theDC <- readIORef dcRef
     pure (MkDPair theDC sendAndSignal)

||| Given a reference to a directed channel, obtain the ability to receive on
||| the channel.
export
becomeReceiver : IORef (DirectionalChannel a)
               -> IO (dc : DirectionalChannel a ** (ReceiverFunc a))
becomeReceiver dcRef =
  do theDC <- readIORef dcRef
     pure (MkDPair theDC await)

-- TODO: In an ideal world, becomeSender would require you to relinquish your
-- ability to also become a receiver for the specific channel (since they're
-- directional). However, this doesn't seem to be (easily) possible.
--becomeSender : IORef (DirectionalChannel a)
--             -> (1 becomeRec : (IORef (DirectionalChannel a)
--                                -> IO (dc : DirectionalChannel a **
--                                            (ReceiverFunc a))))
--             -> IO (dc : DirectionalChannel a ** (SenderFunc a))

