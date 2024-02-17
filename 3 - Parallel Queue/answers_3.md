### Question 9

State the updated interpretations and the invariants of {Red,Blue}.{push(),pop()} in terms of the existing (lecture notes) and new (*xt, yh, and y'*) variables. (*0.25 pts*)

````rust
Note that I don't use yh, I found a solution without it, and I am confident it works.
I use Col as stand-in for {Red, Blue}

Interpretations:
Col.S_O  = Col.O[0, Col.y)
Col.S_BO = Col.O[Col.y, Col.y')
Col.S_B  = [B[i].v| B[i].c = Col for B[h upto t)]
Col.S_IB = [B[i].v| B[t upto Col.x + Col.xt)]
Col.S_I  = Col.I[Col.x, Col.N)

Invariants:
Ired  := Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred
Iblue := Blue.SO + Blue.S_BO + Blue.S_B + Blue.S_IB + Blue.S_I = Kblue
Red.bounds  := Red.x <= Red.N && Red.y <= Red.N
Blue.bounds := Blue.x <= Blue.N && Blue.y <= Blue.N
side        := h <= t && t - h <= N_B
````

### Question 10

Provide the updated implementation of `pop()`, replacing the no-op at [9] with an appropriate statement. Make sure to update your annotations as well to account for your new invariants and interpretations. (*0.25 pts*)

````rust
The task description asked to only modify the statement at [9].
I found that to be impossible, as I needed to add the correct waiting statment and change the buffer read as well.

I show here the implementation for Red and appeal to symmetry for Blue. 
The invariants Iblue and Blue.bounds aren't touched so I aggregate
them into IB to be concise:

IB := Iblue && Blue.bounds

pop gets loop invariant `Red.y = Red.y'` and the loop condition `y != N`

pop()
[8]
{ IB }
{ Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h <= t && t - h <= N_B }
{ Red.y = Red.y' }
wait until h < t and B[h mod N_B].c = col
[9]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (B[h mod N_B].v + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.s_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t && t - h <= N_B }
{ Red.y = Red.y' && B[h mod N_B].c = Red }
Red.O[Red.y] := B[h mod N_B].v
[10]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (Red.O[Red.y] + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.s_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t && t - h <= N_B }
{ Red.y = Red.y' }
[11]
Red.y' := Red.y' + 1
{ IB }
{ Red.O[0, Red.y) + [] 
  + (Red.O[Red.y] + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.s_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t && t - h <= N_B }
{ Red.y + 1 = Red.y' }
h := h + 1
[12]
{ IB }
{ Red.O[0, Red.y) + Red.O[Red.y] 
  + ([B[i].v| B[i].c = Red for B[h upto t)]) 
  + Red.S_IB + Red.s_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h <= t && t - h <= N_B }
{ Red.y + 1 = Red.y' }
Red.y := Red.y + 1
[13]
{ IB }
{ Red.O[0, Red.y) + []
  + ([B[i].v| B[i].c = Red for B[h upto t)]) 
  + Red.S_IB + Red.s_I = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t && t - h <= N_B }
{ Red.y = Red.y' }
````

### Question 11

Provide an updated implementation of `push()`, replacing the no-op at [3] with an appropriate statement. Make sure to update the annotations as well, to account for your updated invariant(s). (*0.25 pts*)

````rust
The task description asked to only modify the statement at [3].
I found that to be impossible, as I needed to change the buffer assignment as well.

I show here the implementation for Red and appeal to symmetry for Blue. 
The invariants Iblue and Blue.bounds aren't touched so I aggregate
them into IB to be concise:

IB := Iblue && Blue.bounds

push gets loop invariant `Red.x + Red.xt <= t` and the loop condition `x != N`

push():
[1]
{ IB }
{ Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t && t - h <= N_B }
{ Red.x + Red.xt <= t }
wait until t - h < N_B
[2]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + [] + (Red.I[Red.x] + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t && t - h < N_B }
{ Red.x + Red.xt <= t }
B[t mod N_B].c := Red
[3]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + [] + (Red.I[Red.x] + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t && t - h < N_B }
{ Red.x + Red.xt <= t && B[t mod N_B].c = Red }
B[t mod N_B].v := Red.I[Red.x]
[4]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + [] + (B[t mod N_B].v + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t && t - h < N_B }
{ Red.x + Red.xt <= t && B[t mod N_B].c = Red }
Red.xt := t - Red.x
[5]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + [] + (B[t mod N_B].v + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t && t - h < N_B }
{ Red.x + Red.xt = t && B[t mod N_B].c = Red }
Red.x := Red.x + 1
[6]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + B[t mod N_B].v + Red.I[Red.x, Red.N) = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t && t - h < N_B }
{ Red.x + Red.xt = t + 1 && B[t mod N_B].c = Red }
t := t + 1
[7]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t)] 
  + [] + Red.I[Red.x, Red.N) = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t && t - h <= N_B }
{ Red.x + Red.xt <= t }
````

### Question 12

Using the [x], [y] -> [z] syntax, list all the interfering steps between `push()` and `pop()` **for the same colour**. How many are there in total? You may use shorthands such as [x,x',x''], [y,y'] -> [z,z'] to refer to multiple steps at once.

Identify which interfering steps can be discarded due to various conditions (e.g. covered by invariant, conflicting preconditions, etc.), and provide **concise** non-interference proofs for the remaining pairs. (*0.25 pts*)

````rust
How many interfering steps are there?
If I understand the question correctly it ask what steps have the possibility of interfering. This possiblitity has every pair.

push has 6 steps and 7 assertions
pop  has 5 steps and 6 assertions
so in total we have 6*6 + 7*5 = 71 possible interfering steps
they are:
[1,2,3,4,5,6,7] vs. [8,9,10,11,12] -> [9,10,11,12,13]
and
[8,9,10,11,12,13] vs. [1,2,3,4,5,6] -> [2,3,4,5,6,7]

I only do the proofs for Red and for Blue I appeal to symmetry.

First we analyze what conjuncts we have to consider.

* The invariants `Ired`, `Iblue`, `Red.bounds`, `Blue.bounds`, `side` are preserved in every step. Thus no interfering can invalidate them.
*  `Red.y = Red.y'`, `Red.y + 1 = Red.y'`, involves only the local variables thus interference is not possible
* the loop invariant and its derivatives `Red.x + Red.xt <= t`, `Red.x + Red.xt = t`, `Red.x + Red.xt = t + 1`, contain the local variables `Red.x` and `Red.xt` and the shared variable `t`. All variables are only updated and used in one thread, which means no other thread can invalidate them.
* `Red.x < Red.N`, `Red.y < Red.N`, contain the local variables `Red.x` and `Red.y` and the constant value `Red.N`, thus interference is impossible.
* `B[t mod N_B].c = Red` cannot be interfered as it occurs in the push thread and the `pop` does neither modify `t` nor `B[any-entry].c`.

Thus the remaining conjuncts to be proven are: `h < t`, `t - h < NB`, and `B[h mod N_B].c = Red`

[8, 9, 10, 11] vs [6] -> [7], left where h < t occurs,
                              right possible interference step
For this we can write the following proof
{h < t}
t := t + 1
{h < t}

[2, 3, 4, 5, 6] vs [11] -> [12], left where t - h < N_B occurs,
                                 right possible interference step
For this we can write the following proof
{t - h < N_B}
h := h + 1
{t - h < N_B}

[9] vs [2] -> [3], left where B[h mod N_B].c = Red occurs,
                   right possible interference step
For this we can write the following proof
{B[h mod N_B].c = Red}
B[t mod N_B].c := Red
{B[h mod N_B].c = Red}

All other proofs are not required as they do not modify the conjuncts whose interference we need to proof.
````

### Question 13

Show that the parallel composition of `{Red,Blue}.push()`, `{Red,Blue}.pop()` is correct for each color (you may appeal to symmetry here if it applies).

````
I assume now that we don't have to do the local correctness, and noninterference, as this was the exercise of the last two questions.

That means the only thing remaining is the Partial Correctness proof;


If we initialize our variables the following way

Red.x, Red.y, Red.xt, Red.y' := 0, 0, 0, 0
Blue.x, Blue.y, Blue.xt, Blue.y' := 0, 0, 0, 0
h, t := 0, 0
Then we get the invariant before the loop 
{ [] + [] + [] + [] + [] + [] + Red.I[0, N) = K }
and therefore Kred = Red.I[0, N)
If we keep the loop-structure from the assignment,
we get the following wehen we exit the parallel section
Red.S_O + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = I[0, N) && y = N
and as Red.S_O = O[0, N) per definition it follows that Red.O[0, N) = Red.I[0, N)
Showing that we have the condition that we want and thus finishing
Partial correctness proof.

With the partial correctness proof finished we have also shown 
that the parallel composition is correct
- local correctness ✓
- noninterference ✓
- partial correctness ✓

For Blue I appeal to symmetry
````