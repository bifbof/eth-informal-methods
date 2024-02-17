### Question 5

State the updated invariants and interpretations for `transfer()`. (*0.25 pts*)

````rust
Interpretations:
S_O    = O[0, y)
S_B20  = O[y, h2)
S_B2   = B2[h2 upto t2)
S_B1B2 = B2[t2 upto h1)
S_B1   = B1[h1 upto t1)
S_IB1  = B1[t1 upto x)
S_I    = I[x, N)

Invariants:
I      := S_O + SB2O + S_B2 + S_B1B2 + S_B1 + S_IB1 + SI = K
side   := h2 <= t2 && h1 <= t1 && t2 - h2 <= NB2 && t1 - h1 <= NB1
bounds := x <= N && y <= N
````

### Question 6

Provide a pseudocode implementation of `transfer()`, labelled and annotated just as in figures 2 and 3 (for `push()` and `pop()`). Your solution should be about as complex as for the existing functions. It must be clear from your annotations that your implementation is locally correct. Make sure to label each of the points between two statements as is done in figures 2 and 3 for `push()` and `pop()`. (*0.5 pts*)

````rust
# transfer gets the local loop invariant t2 = h1
transfer():
[13]
{ S_O + SB2O + S_B2 + S_B1B2 + S_B1 + S_IB1 + SI = K }
{ h2 <= t2 && h1 <= t1 && t2 - h2 <= NB2 && t1 - h1 <= NB1 }
{ x <= N && y <= N }
{ t2 = h1 }
wait until h1 < t1 and t2 - h2 < NB2
[14]
{ S_O + SB2O
  + B2[h2 upto t2) + [] + (B1[h1 mod NB1] + B1[h1+1 upto t1))
  + S_IB1 + S_I = K }
{ h2 <= t2 && h1 < t1 && t2 - h2 < NB2 && t1 - h1 <= NB1 }
{ x <= N && y <= N }
{ t2 = h1 }
B2[t2 mod NB2] := B1[h1 mod NB1]
[15]
{ S_O + S_B2O 
  + B2[h2 upto t2) + [] + (B2[t2 mod NB2] + B1[h1+1 upto t1))
  + S_IB1 + S_I = K }
  }
{ h2 <= t2 && h1 < t1 && t2 - h2 < NB2 && t1 - h1 <= NB1 }
{ x <= N && y <= N }
{ t2 = h1 }
h1 := h1 + 1
[16]
{ S_O + S_B2O 
  + B2[h2 upto t2) + B2[t2 mod NB2] + B1[h1 upto t1)
  + S_IB1 + S_I = K }
  }
{ h2 <= t2 && h1 <= t1 && t2 - h2 < NB2 && t1 - h1 <= NB1 }
{ x <= N && y <= N }
{ t2 + 1 = h1 }
t2 := t2 + 1
[17]
{ S_O + S_B2O 
  + B2[h2 upto t2) + [] + B1[h1 upto t1)
  + S_IB1 + S_I = K }
  }
{ h2 <= t2 && h1 <= t1 && t2 - h2 <= NB2 && t1 - h1 <= NB1 }
{ x <= N && y <= N }
{ t2 = h1 }
````

### Question 7

Identify all required non-interference proofs between `push()`/`transfer()` and `pop()`/`transfer()`, using assertion numbers (e.g. [2] vs. [7] -> [8] or [3,4,5] vs. [4,5,6,7,8] -> [5,6,7,8,9]).

For each of these, either state why a proof is unnecessary (e.g. conflicting preconditions, or disjoint variables), or provide a **concise** proof by annotation of the corresponding Hoare triple. (*0.25 pts)*

> To quote a reply from the forum:
>
> you can apply the [x] vs [y] -> [z] syntax per conjunct. But you have to make sure that you look at all interference pairs at every step. In particular, you might have to look at the same pair for multiple conjuncts.

````
First we analyze what conjuncts we have to consider.

* The invariants `S_O + SB2O + S_B2 + S_B1B2 + S_B1 + S_IB1 + SI = K`, `h2 <= t2 && h1 <= t1 && t2 - h2 <= NB2 && t1 - h1 <= NB1`, and `x <= N && y <= N` are preserved in every step. Thus no interfering can invalidate them.
* The loop invariants and their modifications `t2 = h1`, `t2+1 = h1`, `t1 = x`, `t1 + 1`, `y = h2`, `y + 1 = h2`, `t2 = h1`, involve the shared variables `h1`, `t1`, `h2`, `t2` but the pairs are only ever updated and used in one thread, which means no other thread can invalidate them.
* The conjuncts `x < N` and `y < N`, involve only the local variables `x` and `y` and the constant `N`, so interference is impossible.
* This leaves only `h2 < t2 `, `t1 - h1 < NB1`, `h1 < t1`, and  `t2 - h2 < N_B2`

[8, 9, 10] vs [16] -> [17], left where h2 < t2 occurs, 
                            right possible interference statements
For this we can write the following proof
{h2 < t2}
t2 := t2 + 1
{h2 < t2}

[2, 3, 4, 5] vs [15] -> [16], left where t1 - h1 < NB1 occurs,
                              right possible interference statements
For this we can write the following proof
{t1 - h1 < NB1}
h1 := h1 + 1
{t1 - h1 < NB1}

[14, 15] vs [5] -> [6], left where h1 < t1 occurs,
                        right possible interference statements
For this we can write the following proof
{h1 < t1}
t1 := t1 + 1
{h1 < t1}

[14, 15, 16] vs [9] -> [11], left where t2 - h2 < NB2 occurs,
                             right possible interference statements
For this we can write the following proof
{t2 - h2 < NB2}
h2 := h2 + 1
{t2 - h2 < NB2}

All other proofs are not required as they do not modify the conjuncts whose interference we do need to proof.
````

### Question 8

Show that the parallel composition of `push()`, `pop()`, and `transfer()` is correct.

````
I assume now that we don't have to do the local correctness, and noninterference, as this was the exercise of the last two questions.

That means the only thing remaining is the Partial Correctness proof;

If we initialize our variables the following way
x, y, t1, h1, t2, h2 := 0, 0, 0, 0, 0, 0
Then we get the invariant before the loop 
{ [] + [] + [] + [] + [] + [] + I[0, N) = K }
and therefore K = I[0, N)
If we keep the loop-structure from the assignment,
we get if we exit the parallel section
S_O + SB2O + S_B2 + S_B1B2 + S_B1 + S_IB1 + SI = I[0, N) && y = N
and as S_O = O[0, N) per definition 
it follows that O[0, N) = I[0, N)
Showing that we have the condition that we want and thus finishing
Partial correctness proof.

With the partial correctness proof finished we have also shown 
that the parallel composition is correct
- local correctness ✓
- noninterference ✓
- partial correctness ✓
````

