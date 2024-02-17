###### A: Explain, concisely, the difference between local correctness and global correctness.

We haven't defined global correctness. Local correctness argues about the correctness of a single thread, while global correctness additionally argues about all possible traces of the program in a static way.

###### B What is a concurrent invariant, and how does it differ from a loop invariant?

A concurrent invariant is an invariant that holds at **every** point in the program. In contrast, a loop invariant holds at certain points of the program (before loop, start of iteration, end of iteration, after loop) and can be broken everywhere else (especially in between the start and end of an iteration).

###### C What does ”mutual exclusion” mean in terms of assertions? What does it imply about possible program traces?

Mutex helps us to exclude many traces where interference occurs.
More precisely, it excludes all traces where the critical sections overlap. This means that critical sections are accessed serially.

Lets be `A` and `B` be two assertions in the critical section in two different threads. Then `A and B = ⊥` by the definition of the mutex/lock.
This means there is no state in which the threads can be at the `A` and `B` assertion respectively at the same time.

###### D What is a non-interference proof? What can you assume, what must you show?

A non-interference proof is a proof that regardless at which step a thread is at, no other thread can weaken the current assertion.

Let `{A}` be an assertion and `{B}s{C}` an interfering statement.
We need to show that `A ∧ B => wp(s, A)`, with `wp(s, A)` denoting the weakest precondition with statement `s` and postcondition `A`.

By showing that `A` can be preserved if statement `s` is executed and if the starting state `A ∧ B` is one of the state that fulfil this. (*tldr*: Assume `A ∧ B` to show `wp(s, A)`)