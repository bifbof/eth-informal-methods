### Task 1

###### A Why (can we say that) invariant I1 is established here? (One sentence answer.)

All nodes are unmarked.

###### B What does “all-marked distance” mean? Why is invariant I2 established here? (Two sentences.)

"All-marked distance" is the length of the shortest path to a node using only marked nodes and the node itself. With all unmarked nodes, we can build only one such path namely with node 0 and distance 0.

###### C Why is invariant I3 established here? (One sentence.)

Node 0 is unmarked and 0 is smallest distance that is possible.

###### D Why is invariant I1 maintained here? (Five sentences.)

`m[tn]` contains length of the shortest path from node 0 and can be added to the marked nodes. Lets assume for contradiction that isn't the case, then there exists a shorter path through an unmarked node `x` as a direct predecessor. As `x` is unmarked there must exist an "all-marked" path to a predecessor of `x` (or `x` itself). This predecessor must have a smaller `m` value than `m[tn]`, else the path over `x` to `tn`  would be longer,  this is a contradiction as `m[tn]` is smallest values with I3.

###### E Why is invariant I2 (potentially) broken here? (One sentence.)

As we added `tn` to the marked nodes we can have shorter all-marked distances that go other `tn`.

###### F Why is invariant I3 broken here? (One sentence.)

`tn` is marked.

###### G Why is invariant I2 re-established by this code? (Three sentences.)

The only all-marked distances for unmarked nodes that may decrease must go other `tn` as last marked node. As all other paths go over a different last marked node are still the same, as with I1 there is no shorter distance to the last marked node and with I2 m still stores their distance. Thus I2 is re-established if we go over all outgoing edges of `tn` store the smallest all-marked distance with `tn` as last marked node.

###### H Why is invariant I3 re-established by this code? (One sentence.)

We store in `tn` the m-smallest node that is unmarked and this is exactly I3.

###### I Is this statement necessary to ensure termination? If so, explain its role. If it is not necessary, then why is it here? (Three sentences.)

It isn't necessary for termination, as we decrease the set of unmarked nodes by one every iteration thus termination is guaranteed by the length check.
It is needed to make sure that we don't add anything to INFTY, thus all unreachable node have the same INFTY value. Additionally we skip some computations and are faster.

###### J Why does I1 hold here? (One sentence.)

Invariant I1 is never broken anywhere in the loop.

###### K Why does I2 hold here? (Two sentences.)

If we break before I2 is re-established then with `len(un) == 0` there are no unmarked nodes and I2 holds trivially. If we break after I2 is re-established it is true also after the break. 

###### L How do we know m is ∞ for all nodes in un? (One sentence.)

If `un` contains a value, then the m-least value of all unmarked nodes is infinity (due to the breaking condition) and thus all unmarked nodes have m value infinity.

###### M How do we know m is correct for all nodes? (Four sentences.)

For all marked node we know it is correct with I1. 
For all unmarked nodes we know that `m` is ∞. Assume there exists a shorter path to any unmarked node `x`. As node`x` is unmarked, there must an "all-marked" path to a  unmarked predecessor of that node `x` (or the `x` node itself) with a smaller value than ∞. As there is none we have a contradiction and all unmarked nodes are unreachable.

### Task 2

###### 1. Coupling invariant

The type of a 0,1 value is also called boolean, this is why I use True here.

````
un1[n] = True <==> n ∉ un
nun1 = len(un)
````

### Task 3

###### State why, for efficiency’s sake, it is a good idea to introduce this G2 to replace the original G.

Iterating through all edges in a graph takes $O(|E|)$ time with $|E|$ being the number of edges.
But we only use the outgoing of a single node, if we could only access those we would be faster in $O(\deg(\text{tn}))$ with deg(tn) being the outgoing degree of node `tn`. 

###### Write down exactly and succinctly the coupling invariant that links the abstract G to the concrete G2.

````
(from, dist, to) ∈ G <==> (dist, to) ∈ G2[from]
````

### Task 4

###### Explain why it would be a good idea to use a heap-like structure hp3, say, to represent un1 based on the values assigned to its elements by m.

Searching the minimum m in a list takes $O(N)$, searching the minimum in a heap takes $O(1)$.  The additional cost in removing and updating values is $O(\log N)$ instead of $O(1)$. Without the heap we would have in the end $N$ iterations with $O(\deg(\text{tn}))$ cost for updating all successors, leading to a total cost of $O(N\cdot |E|)$. If we would have been using a heap instead an iteration would cost $O(\log N + \deg(\text{tn})\cdot \log N + 1) = O(\deg({\text{tn}}) \cdot \log N)$ for deleting a node, updating the length of all successors and then searching the minimum. Over all $N$ iterations that gives us a total cost of $O((N + |E|)\log N)$, which is significantly better.

###### Explain informally why other variables might have to be added along with hp3, and what they would be for.

In the heap we store the pair `(m[n], n)` to retrieve not only `minD` efficiently but also the corresponding `tn`.  Additionally we need a map `map3` from node indices to entries in the heap to update the entries efficiently to a smaller values. (This map could be an array of length N containing indices of the heap). We can also write coupling variables

````
(m[n], n) in hp3 <==> un1[i] == True
hp3[map3[n]] = (m[n], n)
````

###### Identify precisely the statements involving m that would be affected by this data refinement, and indicate informally what concrete computations on your concrete variable(s) would be carried out in their place.

When `m` is initialized we need to initialize the heap as well. For that we assign infinite to all N entries, as the choice for the `map3` is arbitrary in this case we just initialize it with `0, 1, 2, ..., N-1`.

When we update `m` with new values, we have to do the same with the heap. For this we use the `map3` to find the value we want to update. If the value is smaller we update the heap with the smaller value, we also have to update `map3` with every swap we do in repairing the heap.

When we search the index of the smallest m-value of the unmarked nodes, we can simply peek at the top element of the heap. This gives us the `minD` as well as the `tn`. If the heap is empty we can take a sentinel node `n_inf` and `minD= INFTY` instead.

Lastly I want to mention that in case we remove the `tn` from the set of unmarked values, we need to pop in `hp3` as well (and update the indices in `map3` accordingly). This does not involve `m`, but I found it important to mention for completeness.

