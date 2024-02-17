### Question 14

Identify the 4 critical sections in your program. Which may be entered simultaneously, and which not?

````
The four critical sections are
- after the wait in Red - push (RPu) (see push below between TA-TR)
- after the wait in Blue - push (BPu)
- after the wait in Red - pop  (RPo) (see pop below between HA-HR)
- after the wait in Blue - pip (BPo)

We have the following access pattern
- y: can enter simultaneously
- n: cannot enter simultanerously

|     | RPu | BPu | RPo | BPo  |
| --- | --- | --- | --- | ---- |
| RPu | -   | n   | y   | y    |
| BPu | n   | -   | y   | y    |
| RPo | y   | y   | -   | n    |
| BPo | y   | y   | n   | -    |
````

### Question 15

For each pair of critical sections that may not be entered simultaneously, state your mutually-exclusive predicates. These must:

1. Never be true at the same time.
2. Be strong enough that one prevents the other becoming true.

````
For the pair Red.push - Blue.push we add:
Interpretation
	Red.T  := Red owns the tail pointer
	Blue.T := Blue owns the tail pointer
Invariant
	!(Red.T && Blue.T)
with the predicates
Red.T && !(Red.T && Blue.T) vs Blue.T && !(Red.T && Blue.T)
we can see that both cannot be true at the same time
and Red.T && !(Red.T && Blue.T) -> !Blue.T and vice versa for Blue

For the pair Red.pop - Blue.pop we add:
Interpretation
	Red.H  := Red owns the head pointer
	Blue.H := Blue owns the head pointer
Invariant
	!(Red.H && Blue.H)
with the predicates
Red.H && !(Red.T && Blue.H) vs Blue.H && !(Red.H && Blue.H)
we can see that both cannot be true at the same time
and Red.H && !(Red.H && Blue.H) -> !Blue.H and vice versa for Blue
````

### Question 16

Provide an annotated implementation of `push()` where you replace the "wait until" statement with a loop that correctly establishes mutual exclusion, following figure 4. This loop must use CAS. Make sure that the mutex is correctly released at end of the `push()`.

Note that your annotations must imply local correctness and follow all the usual rules for annotation. Make sure that your annotations contains labels **between** the statements in both acquire and release segments, you will have to refer to them later. We suggest using [TA.N] and [TR.N] (for *tail-acquire* and *tail-release*, respectively). (*0.25 pts*)

````rust
We replaced t in a data refinement step with t_valid with the coupling invariant.

t = t_valid

I add the following invariants as well to ensure that we locally know that we do not break the mutex:

t_excl := t_used = t_valid -> !(Red.T || Blue.T)
h_excl := B[h mod N_B].c = Red -> !Blue.H
		  && B[h mod N_B].c = Blue -> !Red.H

We do the proof for Red and get the proof for Blue via symmetry.
To be concise as we never do anything with Iblue && Blue.Bounds we again define like before

IB := Iblue && Blue.bounds

to be concise

push gets loop invariant `Red.x + Red.xt <= t_valid`, `!Red.T && Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)` and the loop condition `x != N`

push():
[TA.1]
{ IB }
{ Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.x + Red.xt <= t_valid }
{ t_excl && h_excl && mutex }
{ !Red.T && Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)}
while !Red.T do
   [TA.2]
	{ IB }
    { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
    { Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
    { Red.x + Red.xt <= t_valid }
    { t_excl && h_excl && mutex }
    { !Red.T && Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)}
    Red.t_used' := t_used
    if Red.t_used' = t_valid and t_valid - h < N_B then
       [TA.3]
        { IB }
        { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
        { Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
        { Red.x + Red.xt <= t_valid }
        { t_excl && h_excl && mutex }
        { Red.t_used' = t_used -> (t_used = t_valid && t_valid - h < N_B)}
        CAS(Red.T, t_used, t_used+1, Red.t_used')
       [TA.4]
        { IB }
        { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
        { Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
        { Red.x + Red.xt <= t_valid }
        { t_excl && h_excl && mutex }
        { Red.T -> (t_used = t_valid + 1 && t_valid - h < N_B)}
    end if
end while
[5]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + [] + (Red.I[Red.x] + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h < N_B }
{ Red.x + Red.xt <= t_valid }
{ t_excl && h_excl && mutex }
{ Red.T && t_used = t_valid + 1 }
B[t_valid mod N_B].c := Red
[6]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + [] + (Red.I[Red.x] + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h < N_B }
{ Red.x + Red.xt <= t_valid && B[t_valid mod N_B].c = Red}
{ t_excl && h_excl && mutex }
{ Red.T && t_used = t_valid + 1 }
B[t_valid mod N_B].v := Red.I[Red.x]
[7]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + [] + (B[t_valid mod N_B].v + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h < N_B }
{ Red.x + Red.xt <= t_valid && B[t_valid mod N_B].c = Red}
{ t_excl && h_excl && mutex }
{ Red.T && t_used = t_valid + 1 }
Red.xt := t_valid - Red.x
[8]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + [] + (B[t_valid mod N_B].v + Red.I[Red.x+1, Red.N)) = Kred }
{ Red.x < Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h < N_B }
{ Red.x + Red.xt = t_valid && B[t_valid mod N_B].c = Red}
{ t_excl && h_excl && mutex }
{ Red.T && t_used = t_valid + 1 }
Red.x := Red.x + 1
[9]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + B[t_valid mod N_B].v + Red.I[Red.x+1, Red.N) = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h < N_B }
{ Red.x + Red.xt = t_valid + 1 && B[t_valid mod N_B].c = Red}
{ t_excl && h_excl && mutex }
{ Red.T && t_used = t_valid + 1 }
Red.T := false
[TR.10]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + B[t_valid mod N_B].v + Red.I[Red.x+1, Red.N) = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.x + Red.xt = t_valid + 1 && B[t_valid mod N_B].c = Red}
{ t_excl && h_excl && mutex }
{ !Red.T && Red.T -> (t_used = t_valid+1 && t_valid - h < N_B) && t_used = t_valid + 1 }
t_valid := t_valid + 1
[TR.11]
{ IB }
{ Red.SO + Red.S_BO + [B[i].v| B[i].c = Red for B[h upto t_valid)] 
  + [] + Red.I[Red.x+1, Red.N) = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.x + Red.xt <= t_valid }
{ t_excl && h_excl && mutex }
{ !Red.T && Red.T -> (t_used = t_valid+1 && t_valid - h < N_B) }
````

### Question 17

Provide an annotated implementation of `pop()` where you replace the "wait until" statement with a loop that correctly establishes mutual exclusion, following figure 4. CAS is not required for this loop, though you are allowed to use it. Make sure that the mutex is correctly released at end of the `pop()`.

Note that your annotations must imply local correctness and follow all the usual rules for annotation. Make sure that your annotations contains labels **between** the statements in both acquire and release segments, you will have to refer to them later. We suggest using [HA.N] and [HR.N] (for *head-acquire* and *head-release*, respectively). (*0.5 pts*)

````rust
We replaced t in a data refinement step with t_valid with the coupling invariant.

t = t_valid

I add the following invariants as well to ensure that we locally know that we do not break the mutex:

t_excl := t_used = t_valid -> !(Red.T || Blue.T)
h_excl := B[h mod N_B].c = Red -> !Blue.H
		  && B[h mod N_B].c = Blue -> !Red.H

We do the proof for Red and get the proof for Blue via symmetry.
To be concise as we never do anything with Iblue && Blue.Bounds we again define like before

IB := Iblue && Blue.bounds

to be more concise

pop gets loop invariant `Red.y = Red.y'`, `!Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid)` and the loop condition `y != N`


pop():
[HA.12]
{ IB }
{ Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.y = Red.y' }
{ t_excl && h_excl && mutex }
{ !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
while !Red.H do
   [HA.13]
	{ IB }
    { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
    { Red.x <= Red.N && Red.y < Red.N  && h <= t_valid && t_valid - h <= N_B }
    { Red.y = Red.y' }
    { t_excl && h_excl && mutex }
    { !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
    if B[h mod N_B].c = Red and h < t_valid
       [HA.14]
    	{ IB }
        { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
        { Red.x <= Red.N && Red.y < Red.N  && h < t_valid && t_valid - h <= N_B }
        { Red.y = Red.y' && B[h mod N_B].c = Red }
        { t_excl && h_excl && mutex }
        { !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
        Red.H = true
       [HA.15]
        { IB }
        { Red.SO + Red.S_BO + Red.S_B + Red.S_IB + Red.S_I = Kred }
        { Red.x <= Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
        { Red.y = Red.y'}
        { t_excl && h_excl && mutex }
        { Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
    end if
end while
[16]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (B[h mod N_B].v + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t_valid && t_valid - h <= N_B }
{ Red.y = Red.y' }
{ t_excl && h_excl && mutex }
{ Red.H && B[h mod N_B].c = Red }
Red.O[Red.y] := B[h mod N_B].v
[17]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (Red.O[Red.y] + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t_valid && t_valid - h <= N_B }
{ Red.y = Red.y' }
{ t_excl && h_excl && mutex }
{ Red.H }
Red.y' :=  Red.y' + 1
[18]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (Red.O[Red.y] + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t_valid && t_valid - h <= N_B }
{ Red.y + 1 = Red.y' }
{ t_excl && h_excl && mutex }
{ Red.H }
Red.H := false
[HR.19]
{ IB }
{ Red.O[0, Red.y) + [] 
  + (Red.O[Red.y] + [B[i].v| B[i].c = Red for B[h+1 upto t)]) 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h < t_valid && t_valid - h <= N_B }
{ Red.y + 1 = Red.y' }
{ t_excl && h_excl && mutex }
{ !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
h := h + 1
[HR.20]
{ IB }
{ Red.O[0, Red.y) + Red.O[Red.y] 
  + [B[i].v| B[i].c = Red for B[h+1 upto t)] 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y < Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.y + 1 = Red.y' }
{ t_excl && h_excl && mutex }
{ !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
Red.y :=  Red.y + 1
[HR.21]
{ IB }
{ Red.O[0, Red.y) + [] 
  + [B[i].v| B[i].c = Red for B[h+1 upto t)] 
  + Red.S_IB + Red.S_I = Kred }
{ Red.x <= Red.N && Red.y <= Red.N  && h <= t_valid && t_valid - h <= N_B }
{ Red.y = Red.y' }
{ t_excl && h_excl && mutex }
{ !Red.H && Red.H -> (B[h mod N_B].c = Red && h < t_valid) }
````

### Question 18

Using the [x], [y] -> [z] syntax, list all the interfering steps between `Red.push()`/`Blue.push()` and `Red.pop()`/`Blue.pop()`. How many are there in total? You may use shorthands such as [x,x',x''], [y,y'] -> [z,z'] to refer to multiple steps at once. (*0.25 pts*)

````
Using the assumptions like last exercise. That possible every step could interfere, even if they have conflicting preconditions.

push has 10 steps and 11 assertions
pop  has 9 steps and 10 assertions

so in total we have
- push Red interfers push Blue has 10 * 11 = 110 possible interfering steps
- push Blue interfers push Red has 10 * 11 = 110 possible interfering steps
- pop Red interfers pop Blue has 9 * 10 = 90 possible interfering steps
- pop Blue interfers pop Red has 9 * 10 = 90 possible interfering steps

so in total we have 110+110+90+90 = 400 possible interfering steps

they are:
[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11] vs [TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10] -> [TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11]
[HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21] vs [HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20] -> [HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21]

If you want to see both colors:
Red.[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11] vs Blue.[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10] -> Blue.[TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11]
Blue.[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11] vs Red.[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10] -> Red.[TA.2, TA.3, TA.4, 5, 6, 7, 8, 9, TR.10, TR.11]
Red.[HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21] vs Blue.[HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20] -> Blue.[HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21]
Blue.[HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21] vs Red.[HA.12, HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20] -> Red.[HA.13, HA.14, HA.15, 16, 17, 18, HR.19, HR.20, HR.21]

````

### Question 19

Which pairs have conflicting preconditions? Why do they not require a proof?

Of the remaining non-interference pairs, which statements are covered by true invariants? (*0.25 pts*)

````rust
We can remove pairs for conflicting preconditions that are both in the critical sections. (I do not repeat it now for every color due to symmetry)

The following pairs can be removed due to the mutual exclusion invariant. As not both can hold the lock at the same time
[5, 6, 7, 8, 9] vs [5, 6, 7, 8, 9] -> [6, 7, 8, 9, TR.10]
[16, 17, 18] vs [16, 17, 18] -> [17, 18, HR.19]

We further the can remove all pairs were a lock is set but the exclusion invariant (t_excl or h_excl) forbids it.
This is 
[5, 6, 7, 8, 9, TR.10] vs [5, 6, 7, 8, 9, TR.10] -> [6, 7, 8, 9, 10, TR.11]
[HR.14, 16, 17, 18, HR.19, HR.20] vs [HR.14, 16, 17, 18, HR.19, HR.20] -> [HR15, 17, 18, 19, HR.20, HR.21]
This is strictly more :)

But I am confused what you mean by true invariants, invariants are by definition true.
I would be really thankful if next year there would be an example how to do this.
````

### Question 20

For the remaining pairs, provide concise noninterference proofs.

````
I only do the proofs for Red and for Blue I appeal to symmetry.

First we analyze what conjuncts we have to consider.

* The invariants `Ired`, `Iblue`, `Red.bounds`, `Blue.bounds`, `side`, `t_excl`, `h_excl`, `mutex` are preserved in every step. Thus no interfering can invalidate them.
* `Red.x < Red.N`, `Red.y < Red.N`, contain the local variables `Red.x` and `Red.y` and the constant value `Red.N`, thus interference is impossible.
* `Red.y = Red.y'`, `Red.y + 1 = Red.y'`, involves only the local variables thus interference is not possible
* `!Red.T`, `Red.T`, `!Red.H`, `Red.H` are all local variables they cannot be interfered

The remaining conjucts are proven here.

For the proof LHS is where the conjunct appears, RHS possible interference steps

h < t_valid
[HA.14, 16, 18, HR.19] vs [HR.19] -> [HR.20],                  
interference impossible due to h_excl (see question 19)

`Red.x + Red.xt <= t_valid`
[TA.1, TA.2, TA.3, TA.4, 5, 6, 7, TR.11] vs [TR.10] -> [TR.11]
For this we can write the following proof
{Red.x + Red.xt <= t_valid}
t_valid := t_valid
{Red.x + Red.xt <= t_valid}

Red.x + Red.xt = t_valid + 1`, `Red.x + Red.xt = t_valid `t_used = t_valid + 1`, `t_valid - h < N_B` 
 vs [TR.10] -> [TR.11]
interference impossible due to t_excl (see question 19)

B[t_valid mod N_B].c = Red
[6, 7, 8, 9, TR.10] vs [5] -> [6]
inference impossible due to t_excl (see question 19)

B[h mod N_B].c = Red
[H14, 16] vs [HR.19] -> [HR.20]
inference impossible due to h_excl (See question 19)

Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)
there are multiple occurences but only one where Red.T is not False and thus this implication has the possibility to be wrong.
[TA.4] vs [TA.3, TR.10] -> [TA.4, TR.11]
Proof for [TA.4] vs [TA.3] -> [TA.4], condensed to the essential
case distinction
	case Red.T is False then implication is True and cannot be broken  as Red.T is local
	case Red.T is True
		then we know that t_used = t_valid + 1
		Case distinction
			case Blue.t_used != t_used then
				{Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)}
				CAS(Blue.T, t_used, t_used+1, Blue.t_used')
				{Red.T -> (t_used = t_valid+1 && t_valid - h < N_B)}
			case Blue.t_used = t_used
				then with Blue.t_used' = t_used -> (t_used = t_valid && t_valid - h < N_B)
				we learn that t_used = t_valid
				this is a contradiction to t_used = t_valid + 1
				QED
Proof for [TA.4] vs [TR.10] -> [TR.11]
inference impossible due to t_excl (see question 19)

Red.H -> (B[h mod N_B].c = Red && h < t_valid)
[HA.15] is the only occurence where Red.H is not false and thus this implaction possible False.
vs [HR.19] -> [HR.20]
In [HR.19] we learn that B[h mod N_B].c = Blue
and in [HA.15] we learn that B[h mod N_B].c = Red
this is a contradiction.
````

### Question 21

Explain why `Red.pop()` does not interfere with `Blue.push()` (nor `Blue.pop()` with `Red.push()`).

````rust
The only non-local conjuncts that Red.pop() and Blue.push() share 
are
h < t_valid (pop), t_valid - h <= N_B (push) and B[h mod N_B].c = Red (pop)

Blue.push() can only increase h, thus h < t_valid will hold regardless
Red.pop() can only decrease t, thus t_valid - h <= N_B will hold regardless
B[h mod N_B].c = Red, is only interfered by [5] -> [6]
But from [5] assertion we know that 
{ B[h mod N_B].c = Red && h <= t_valid &&  t_used = t_valid + 1 }
B[t_valid mod N_B].c := Blue
{B[h mod N_B].c = Red }
holds

It is basically the same interference proof as for Red.push() only the last part that I added here is different.
````

