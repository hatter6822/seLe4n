import SeLe4n.Prelude

namespace SeLe4n.Model

/-- Amortized O(1) FIFO queue represented as `{head, tail}` lists.

`head` stores front-to-back elements ready to dequeue.
`tail` stores back-to-front elements recently enqueued. -/
structure ThreadQueue where
  head : List SeLe4n.ThreadId
  tail : List SeLe4n.ThreadId
  deriving Repr, DecidableEq

namespace ThreadQueue

def empty : ThreadQueue := { head := [], tail := [] }

instance : EmptyCollection ThreadQueue where
  emptyCollection := empty

def toList (q : ThreadQueue) : List SeLe4n.ThreadId :=
  q.head ++ q.tail.reverse

def ofList (xs : List SeLe4n.ThreadId) : ThreadQueue :=
  { head := xs, tail := [] }

private def normalize (q : ThreadQueue) : ThreadQueue :=
  match q.head with
  | [] => { head := q.tail.reverse, tail := [] }
  | _ => q

def isEmpty (q : ThreadQueue) : Bool :=
  q.head.isEmpty && q.tail.isEmpty

def length (q : ThreadQueue) : Nat :=
  q.head.length + q.tail.length

/-- O(1) enqueue at queue tail (amortized over dequeues). -/
def enqueueTail (q : ThreadQueue) (tid : SeLe4n.ThreadId) : ThreadQueue :=
  { q with tail := tid :: q.tail }

/-- O(1) dequeue from queue head (amortized). -/
def dequeueHead (q : ThreadQueue) : Option (SeLe4n.ThreadId × ThreadQueue) :=
  let nq := normalize q
  match nq.head with
  | [] => none
  | x :: xs => some (x, { head := xs, tail := nq.tail })

def enqueue_tail (q : ThreadQueue) (tid : SeLe4n.ThreadId) : ThreadQueue :=
  enqueueTail q tid

def dequeue_head (q : ThreadQueue) : Option (SeLe4n.ThreadId × ThreadQueue) :=
  dequeueHead q

@[simp] theorem toList_ofList (xs : List SeLe4n.ThreadId) :
    (ofList xs).toList = xs := by
  simp [ofList, toList]

@[simp] theorem toList_enqueue_tail_ofList (xs : List SeLe4n.ThreadId) (tid : SeLe4n.ThreadId) :
    (enqueue_tail (ofList xs) tid).toList = xs ++ [tid] := by
  simp [enqueue_tail, enqueueTail, ofList, toList]

@[simp] theorem dequeue_head_ofList_cons (x : SeLe4n.ThreadId) (xs : List SeLe4n.ThreadId) :
    dequeue_head (ofList (x :: xs)) = some (x, ofList xs) := by
  simp [dequeue_head, dequeueHead, ofList, normalize]

@[simp] theorem dequeue_head_ofList_nil :
    dequeue_head (ofList []) = none := by
  simp [dequeue_head, dequeueHead, ofList, normalize]

end ThreadQueue

end SeLe4n.Model
