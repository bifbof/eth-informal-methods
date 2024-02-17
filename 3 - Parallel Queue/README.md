# THIS CODE IS NOT COMPLETELY CORRECT! 

If got some mistakes in the code and I am too lazy to change them now :D

Feedback on my solution:

- **Question 8**: why do you know that the S_x arrays are empty?

- **Question 10**: You are double-counting elements in your invariant: After increasing y' the same element is in the end of O as well as the head of B.

- **Question 13**: Why do the individual S_x bits have to be empty?

- **Question 15**: Red.T being true does not prevent Blue.T from being true (remember it is local!)

- **Question 17**: Note that you cannot check the (shared) variable h atomically in two different conjuncts: As is the case with t', you have to make a local copy of h (call it h') in order to atomically check the predicates on h.

  A problem would arise in this case if the buffer was empty (h = t_valid), and the element pointed to by B[h mod N_B] was Blue (e.g. from a previous call to push()). Then it would be possible for a red element to be pushed *after* checking the color of B[h mod N_B], but before checking h < t_valid.

  Also note that your invariant double counts the element to be popped between [HR.18] and [HR.20].

Further does my non-interference proof not work because the exclusivity thing is not really given if you free the lock. I think the program is correct but then the exclusivity is gone and interference would be possible. This probably relates to question 15