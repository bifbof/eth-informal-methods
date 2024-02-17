#!/usr/bin/env python3
# student number: 17-932-161

# call with the following command:
# python3 upsequence.py < file.txt
# see examples_program.txt for some runs

import sys

# just for convenience as I use it multiple times
INF = float("inf")


def upsequence(A: [int]) -> [int]:
    N = len(A)
    A = A.copy()  # as we increase size by one

    # inf is good as it never overwrites one of our int values
    A.append(INF)  # A[N] := "something"

    # M is one too big to catch bigger A size
    M = [A[0]] + [INF] * N
    Prev = [INF] * (N + 1)
    n = m = l = 0
    # { m = maxlen US(n) } --> I_m
    # { l = maxlen PR(n) } --> I_l
    # { M is sorted } --> I_sorted
    # { forall k in [0, m]. M[k] = smallest A[i] with maxlen PR(i) = k } --> I_M
    # { forall i in [0, n]. Prev[i] = forall j in [0, i). min{A[j] | A[j] < A[i] and maxlen PR(j) + 1 = maxlen PR(i)} }
    # Last invariant descripes the new array that stores predecessors --> I_Prev
    while n != N:
        # { n != N and I_m and I_l and I_sorted and I_M}
        m = max(m, l + 1)
        # { I_m{n+1} } the {n+1} denotes the invariant holding for the next step
        l = binary_search(M, A[n+1])
        # { M[0, l) < A[n+1] <= M[l, m+1) }
        # |=
        # { l = maxlen PR(n+1) } --> I_l{n+1}
        M[l] = min(M[l], A[n+1])
        # { I_sorted and I_M{n+1} }

        # { I_Prev }
        if l > 0:
            # { l > 0 and I_Prev }
            # |= (with l>0 we assure we are within M's range then the definition of M entry is equivalent)
            # { M[l-1] = forall j [0, n+1]. min{A[j] | A[j] < A[n+1] and maxlen PR(j) + 1 = l and I_Prev}
            Prev[n+1] = M[l-1]
            # { Prev[n+1] = forall j in [0, n+1). min{A[j] | A[j] < A[n+1] and maxlen PR(j) + 1 = l and I_Prev}
            # |= (we get this step in how l is defined)
            # { Prev[n+1] = forall j in [0, n+1). min{A[j] | A[j] < A[n+1] and maxlen PR(j) + 1 = maxlen PR(n+1) and I_Prev}
            # |= (now we only have to attach it)
            # { I_Prev{n+1}}
        else:
            # { l <= 0 and I_Prev}
            Prev[n+1] = INF
            # { l <= 0 and Prev(n+1) = inf and I_Prev}
            # |= (as the minimum of the empty set can be denoted as infinite)
            # { I_Prev{n+1} }
        # { I_Prev{n+1} }

        # { I_m{n+1} and I_l{n+1} and I_sorted and I_M{n+1} and I_Prev{n+1}}
        n += 1
        # { I_m and I_l and I_sorted and I_M and I_Prev}

    # dropped I_l and I_sorted as not needed anymore
    # {n = N and I_m and I_M and I_Prev}
    Order = [0] * m
    m_ = m
    # as A[N] is INF we know that it did not override M[m_ - 1]
    # as with INF we can append to everything (just as a sidenote)
    next = M[m_ - 1]
    i = N
    # { next = A[q] with max q in [0, i) such that maxlen PR(q) = m_ - 1 and A[q] < Order[m_, m)} --> I_next
    # { forall r in [m_, m) exists s. A[s] = Order[r] and maxlen PR(s) = r}  --> I_Order
    # { forall q, r in [m_, m). q < r == Order[q] < Order[r]} --> I_Order_Sorted
    # { m_ >= 0 }  --> I_m_
    # I_next is true due to I_M, and A[q] < Order[m_, m) holds as due to emptiness
    # I_Order and I_Order_Sorted hold trivially at beginning as [m_, m) is empty
    while m_ > 0:
        # { m_ > 0 and I_m_, I_next, I_Order, I_Order_Sorted }
        if next == A[i - 1]:
            # { next = A[i-1], I_next, I_Order, I_m_}
            # i-1 is biggest value in range [0, i) -> thus is the searched value
            Order[m_ - 1] = next
            # { Order[m_ - 1] = A[i-1] such that maxlen PR(q) = m_ - 1 and A[i-1] < Order[m_, m)}
            # { I_Order{m-1} and I_Order_Sorted{m-1} }
            next = Prev[i - 1]
            # { next = forall j in [0, i-1). min{A[j] | A[j] < A[i-1] and maxlen PR(j) + 1 = maxlen PR(i-1)} }
            # |= ( the A[j] with the maximum j in [0, i-1) fulfills this formula as all smaller j
            #      must have a smaller or equal maximum prefix. )
            # { next = A[q] with max q in [0, i-1) such that maxlen PR(q) = (m_ - 1) - 1 and A[q] < Order[m_ -1, m)}

            # {m_ > 0}
            m_ = m_ - 1
            # {m_ >= 0} => {I_m_}
            # { I_next{i-1} and I_Order and I_Order_Sorted }  # the m_ is taken care off the i-1 not yet
        else:
            # { next != A[i-1] and I_next}
            # |= (as not equal we know that q must be in the remaining range of [0, i-1) )
            # {I_next{i-1}}
            # other invariant hold as their variables are not modified
            pass
        # {I_next{i-1}}
        i -= 1
        # {I_m_, I_next, I_Order, I_Order_Sorted }
    # {not (m > 0) and m >= 0 and I_Order, I_Order_Sorted}

    # this two invariants tell us that we stored in Order the longest common subsequence.
    # { forall r in [0, m) exists s. A[s] = Order[r] and maxlen PR(s) = r}
    # { forall q, r in [0, m). q < r == Order[q] < Order[r]}
    # Thus we are happy and can return :D
    return Order


def binary_search(A, val):
    """
    Binary search compliant with definition in class.
    Thus code documentation is thorough but quite minimal. 
    """
    N = len(A)
    # { A is sorted }
    l, h = 0, N
    # { A[0, l) < val <= A[h, N) and l <= h }
    while l != h:
        # { l != h and I }
        m = (l + h) // 2
        # { l <= m and m + 1 <= h}
        if val <= A[m]:
            # { val <= A[m, N) }
            h = m
            # { val <= A[h, N) and l <= h }
        else:
            # { A[0, m+1) < a }
            l = m + 1
            # { A[0, l) < a and l <= h}
        # { A[0, l) < a <= A[h, N) and l <= h }
    # { l = h and A[0, l) < val <= A[h, N) and l <= h }
    # |=
    # { A[0, l) < val <= A[l, N) }
    return l


if __name__ == "__main__":
    seq = [int(i) for i in sys.stdin.readlines()]
    res = upsequence(seq)
    print("\n".join(str(i) for i in res))
