-- Idris 2

||| A Queue implementation based on the description in Purely Functional Data
||| Structures by Chris Okasaki
module System.Concurrency.Queue

import Data.List
import Data.IORef
import System.Concurrency

-- Box, but sensibly named
export
data Message : Type -> Type where
  MkMessage : (contents : a) -> Message a

||| Prepare something for sending by putting it in a Message. Note that there is
||| no way to safely retrieve items from a Message once they're in there!
|||
||| @item: the thing to put in the message
export
prepare : (item : ty) -> Message ty
prepare item = MkMessage item

||| Open a message, expecting it to contain something of `expectedType`. Note
||| however, that we cannot possibly guarantee that the message actually
||| contains this, since it has come from the outside (hence 'unsafe').
|||
||| @msg: the message to open
||| @expectedType: the Type that the contents are assumed to have
export
unsafeOpen : Message ty -> ty
unsafeOpen (MkMessage contents) = contents

public export
Stack : Type -> Type
Stack a = List (Message a)

emptyStack : {0 a : Type} -> Stack a
emptyStack = []

makeStack : {a : Type} -> IO (IORef (Stack a))
makeStack = newIORef emptyStack

namespace Stack
  ||| Put something at the top of the stack.
  |||
  ||| MT-Safe: NO
  export
  push : {0 a : Type}
       -> (sRef : IORef (Stack a))
       -> (msg : Message a)
       -> IO ()
  push sRef msg = modifyIORef sRef ((::) msg)

  ||| Get the first item on the stack if there is one, removing it in the
  ||| process.
  |||
  ||| MT-Safe: NO
  export
  pop : {0 a : Type} -> (sRef : IORef (Stack a)) -> IO (Maybe (Message a))
  pop sRef = do stack <- readIORef sRef
                case stack of
                     [] => pure Nothing
                     (m :: ms) => do writeIORef sRef ms
                                     pure (Just m)

  ||| Get the first item on the stack if there is one, without removing it.
  |||
  ||| MT-Safe: NO
  export
  peek : {0 a : Type} -> (sRef : IORef (Stack a)) -> IO (Maybe (Message a))
  peek sRef = do stack <- readIORef sRef
                 case stack of
                      [] => pure Nothing
                      (m :: ms) => pure (Just m)

export
data Queue : Type -> Type where
  MkQueue : {0 a : Type}
          -> (front : IORef (Stack a))
          -> (rear  : IORef (Stack a))
          -> (lock : Mutex)
          -> Queue a

getFront : Queue a -> IORef (Stack a)
getFront (MkQueue front _ _) = front

getRear : Queue a -> IORef (Stack a)
getRear (MkQueue _ rear _) = rear

||| Create a new, empty queue.
export
makeQueue : {a : Type} -> IO (IORef (Queue a))
makeQueue = do qLock <- makeMutex
               fRef <- makeStack
               rRef <- makeStack
               newIORef (MkQueue fRef rRef qLock)

namespace Queue
  ||| Lock the queue by acquiring its mutex.
  ||| (ONLY FOR INTERNAL USE)
  |||
  ||| MT-Safe: NO
  lockQueue : Queue _ -> IO ()
  lockQueue (MkQueue _ _ lock) = mutexAcquire lock

  ||| Unlock the queue by releasing its mutex.
  ||| (ONLY FOR INTERNAL USE)
  |||
  ||| MT-Safe: NO
  unlockQueue : Queue _ -> IO ()
  unlockQueue (MkQueue _ _ lock) = mutexRelease lock

  ||| Move the rear to the front. Used when we're out of items in the front and
  ||| there may be items in the rear.
  ||| (ONLY FOR INTERNAL USE)
  |||
  ||| MT-Safe: NO
  reorder : {0 a : Type}
          -> (frontRef : IORef (Stack a))
          -> (rearRef : IORef (Stack a))
          -> IO ()
  reorder frontRef rearRef = do rear <- readIORef rearRef
                                case rear of
                                     [] => pure ()
                                     xs => do writeIORef frontRef (reverse xs)
                                              writeIORef rearRef emptyStack

  ||| Put a message at the end of the queue.
  |||
  ||| MT-Safe: YES
  export
  enqueue : {0 a : Type}
          -> (qRef : IORef (Queue a))
          -> (msg : Message a)
          -> IO ()
  enqueue qRef msg = do queue <- readIORef qRef
                        lockQueue queue
                        push (getRear queue) msg
                        unlockQueue queue

  ||| Get a message from the queue if there is one, removing it in the process.
  |||
  ||| MT-Safe: YES
  export
  dequeue : {0 a : Type}
          -> (qRef : IORef (Queue a))
          -> IO (Maybe (Message a))
  dequeue qRef =
    do queue <- readIORef qRef
       lockQueue queue
       let frontRef = getFront queue
       let rearRef  = getRear  queue
       maybeFront <- pop frontRef
       case maybeFront of
            Nothing =>
              do reorder frontRef rearRef
                 maybeFront' <- pop frontRef
                 case maybeFront' of
                      Nothing => do unlockQueue queue
                                    pure Nothing
                      (Just msg') => do unlockQueue queue
                                        pure (Just msg')

            (Just msg) => do unlockQueue queue
                             pure (Just msg)

  ||| Get a message from the queue if there is one, without removing it.
  |||
  ||| MT-Safe: YES
  export
  peek : {0 a : Type}
       -> (qRef : IORef (Queue a))
       -> IO (Maybe (Message a))
  peek qRef =
    do queue <- readIORef qRef
       lockQueue queue
       let frontRef = getFront queue
       let rearRef  = getRear  queue
       maybeFront <- peek frontRef
       case maybeFront of
            Nothing =>
              do reorder frontRef rearRef
                 maybeFront' <- peek frontRef
                 case maybeFront' of
                      Nothing     => do unlockQueue queue
                                        pure Nothing
                      (Just msg') => do unlockQueue queue
                                        pure (Just msg')

            (Just msg) => do unlockQueue queue
                             pure (Just msg)

