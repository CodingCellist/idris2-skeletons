-- Idris 2

module System.Concurrency.BufferedChannel

import public Data.IORef
import System.Concurrency

import public System.Concurrency.Queue

export
data BufferedChannel : Type -> Type -> Type where
  MkBufferedChannel : {0 a : Type} -> {0 b : Type}
                    -> (inbox  : IORef (Queue a))
                    -> (iCondLock : Mutex)
                    -> (iCondVar : Condition)
                    -> (outbox : IORef (Queue b))
                    -> (oCondLock : Mutex)
                    -> (oCondVar : Condition)
                    -> BufferedChannel a b


---------------------------
-- CONSTRUCTOR FUNCTIONS --
---------------------------

||| Create a new BufferedChannel.
export
makeBufferedChannel : {a : Type} -> {b : Type}
                    -> IO (IORef (BufferedChannel a b))
makeBufferedChannel = do iQueue <- makeQueue
                         iCondLock <- makeMutex
                         iCondVar <- makeCondition
                         -- ^ inbox things
                         -- v outbox things
                         oQueue <- makeQueue
                         oCondLock <- makeMutex
                         oCondVar <- makeCondition
                         -- create the channel in an IORef
                         newIORef (MkBufferedChannel iQueue iCondLock iCondVar
                                                     oQueue oCondLock oCondVar)

||| Given an IORef to a BufferedChannel, obtained through the
||| `makeBufferedChannel` function, create a version which is primarily used for
||| sending messages.
export
makeSender : (cRef : IORef (BufferedChannel a b)) -> IO (BufferedChannel a b)
makeSender cRef
  = do (MkBufferedChannel inbox iCL iCV outbox oCL oCV) <- readIORef cRef
       pure (MkBufferedChannel inbox iCL iCV outbox oCL oCV)

||| Given an IORef to a BufferedChannel, obtained through the
||| `makeBufferedChannel` function, create a version which is primarily used for
||| receiving messages.
export
makeReceiver : (cRef : IORef (BufferedChannel a b)) -> IO (BufferedChannel b a)
makeReceiver cRef
  = do (MkBufferedChannel inbox iCL iCV outbox oCL oCV) <- readIORef cRef
       pure (MkBufferedChannel outbox oCL oCV inbox iCL iCV)


------------------------
-- INBOX MANIPULATION --
------------------------

getInbox : BufferedChannel a b -> IORef (Queue a)
getInbox (MkBufferedChannel inbox _ _ _ _ _) = inbox

-- FIXME: Do we need this function?
-- ||| Wait on the condition variable for the BufferedChannel's inbox.
-- waitInbox : BufferedChannel a b -> IO ()
-- waitInbox (MkBufferedChannel inbox iCondLock iCondVar _ _ _)
--   = do mutexAcquire iCondLock
--        conditionWait iCondVar iCondLock
--
-- OLD IMPLEMENTATION
--  = do
--       conditionWait iCondVar iCondLock
--
-- OLD OLD IMPLEMENTATION
--  = conditionWait iCondVar iCondLock


-------------------------
-- OUTBOX MANIPULATION --
-------------------------

getOutbox : BufferedChannel a b -> IORef (Queue b)
getOutbox (MkBufferedChannel _ _ _ outbox _ _) = outbox

||| Unlock at least one of the threads currently waiting on the outbox's
||| condition variable.
|||
||| On a *nix system, see `man 3 pthread_cond_broadcast` for more details
||| regarding the difference between this function and the `broadcastOutbox`
||| function.
signalOutbox : BufferedChannel a b -> IO ()
signalOutbox (MkBufferedChannel _ _ _ _ _  oCondVar)
  = conditionSignal oCondVar

||| Unlock all of the threads currently waiting on the outbox's condition
||| variable.
|||
||| On a *nix system, see `man 3 pthread_cond_broadcast` for more details
||| regarding the difference between this function and the `signalOutbox`
||| function.
broadcastOutbox : BufferedChannel a b -> IO ()
broadcastOutbox (MkBufferedChannel _ _ _ _ _ oCondVar)
  = conditionBroadcast oCondVar


-------------
-- SENDING --
-------------

||| Send a Message through the BufferedChannel and *signal* on the condition variable
||| for the BufferedChannel's outbox to indicate to at least one blocking thread
||| blocking on it, that a Message can be received (see `signalOutbox`).
|||
||| @chan: The BufferedChannel to send the Message through.
||| @msg: The Message to send.
|||
||| MT-Safe: YES
export
sendAndSignal : (chan : BufferedChannel a b) -> (msg : Message b) -> IO ()
sendAndSignal chan msg =
  do enqueue (getOutbox chan) msg
     signalOutbox chan

||| Send a Message through the BufferedChannel and *broadcast* on the condition variable
||| for the BufferedChannel's outbox to indicate to all threads currently blocking on
||| it, that a Message can be received (see `signalOutbox`).
|||
||| @chan: The BufferedChannel to send the Message through.
||| @msg: The Message to send.
|||
||| MT-Safe: YES
export
sendAndBroadcast : (chan : BufferedChannel a b) -> (msg : Message b) -> IO ()
sendAndBroadcast chan msg =
  do enqueue (getOutbox chan) msg
     broadcastOutbox chan


---------------
-- RECEIVING --
---------------

||| Receive a Message through the BufferedChannel, if there is one, removing it from the
||| inbox in the process. Does not block but immediately returns `Nothing` if
||| there was no message available.
|||
||| @chan: The BufferedChannel to receive the Message through.
|||
||| MT-Safe: YES
export
receive : (chan : BufferedChannel a b) -> IO (Maybe (Message a))
receive chan = dequeue (getInbox chan)

||| Similar to `receive`, but blocks on the condition variable of the inbox
||| until a Message is available, at which point it receives the Message,
||| removing it from the inbox in the process.
|||
||| @chan: The BufferedChannel to receive the Message through.
|||
||| MT-Safe: YES
export
await : (chan : BufferedChannel a b) -> IO (Maybe (Message a))
await (MkBufferedChannel inbox iCondLock iCondVar _ _ _) =
  do maybeMsg <- dequeue inbox
     case maybeMsg of
          -- if at first you don't succeed...
          Nothing => do mutexAcquire iCondLock   -- see man 3 pthread_cond_await
                        conditionWait iCondVar iCondLock
                        rawMsg <- dequeue inbox
                        mutexRelease iCondLock   -- FIXME: necessary? Yes. Right place for it?
                        pure rawMsg
          justMsg => pure justMsg

--------------
-- PEEK/SPY --
--------------

||| Receive a Message through the BufferedChannel, if there is one, *without* removing
||| from the inbox in the process. Does not block but immediately returns
||| `Nothing` if there was no message available.
|||
||| @chan: The BufferedChannel to receive the Message through.
|||
||| MT-Safe: YES
export
peek : (chan : BufferedChannel a b) -> IO (Maybe (Message a))
peek (MkBufferedChannel inbox _ _ _ _ _) = peek inbox

||| Watches the BufferedChannel until a Message appears, at which point it "reports
||| back" with the Message. Hence, `spy`.
|||
||| Similar to `peek`, but blocks on the condition variable of the inbox until
||| a Message is available, at which point it receives the Message, *without*
||| removing it from the BufferedChannel's inbox in the process.
|||
||| @chan: The BufferedChannel to receive the Message through.
|||
||| MT-Safe: YES
export
spy : (chan : BufferedChannel a b) -> IO (Maybe (Message a))
spy (MkBufferedChannel inbox iCondLock iCondVar _ _ _) =
  do maybeMsg <- peek inbox
     case maybeMsg of
          Nothing => do mutexAcquire iCondLock
                        conditionWait iCondVar iCondLock
                        rawMsg <- peek inbox
                        mutexRelease iCondLock
                        pure rawMsg
          justMsg => pure justMsg

