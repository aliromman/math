# Solution to Haslegrave’s Question 3 on exclusive sum numbers and bounded sum index

A graph that can be labelled with only $s$ distinct edge sums can be recognized using at most

$$
s\,3^{s-1}
$$

allowed sums. Thus the exclusive sum number stays bounded whenever the sum index stays bounded. This answers John Haslegrave’s Question 3 in the negative. [*Sum Index, Difference Index and Exclusive Sum Number of Graphs*, Graphs and Combinatorics 39 (2023), Proposition 1 and Question 3](https://doi.org/10.1007/s00373-023-02624-0)

Both parameters use distinct integer labels on the vertices. An ordinary sum labelling counts the different sums on edges. A nonedge can have one of those same sums. An exclusive labelling uses positive vertex labels and a set of positive integers $T$ such that, for distinct vertices $x,y$, their label sum belongs to $T$ exactly when $xy$ is an edge. By Haslegrave’s Proposition 1 the least possible $|T|$ is the exclusive sum number.

## Proof

Choose an optimal ordinary labelling and list its $s$ edge sums. Give each vertex a second label with $s$ ternary digits. Digit $i$ is one if the vertex has a neighbor with which it makes edge sum $i$, and zero otherwise.

Translate the old labels until all are positive. Append the ternary digits on the right. When two new labels are added, their lower $s$ digits add without a carry. The remaining part therefore records the sum of the old labels.

Suppose vertices $x,y$ have the $i$th old edge sum. Their new sum is allowed exactly when the $i$th ternary digit is two. Indeed, if the digit is two, $x$ has some neighbor $z$ making the same old sum. Cancelling the label of $x$ shows that $z$ and $y$ had the same old label. Injectivity gives $z=y$. Conversely, the two endpoints of every edge both have digit one in that edge’s coordinate.

For a fixed old edge sum, one digit is fixed at two and each of the other $s-1$ digits has three possibilities. The $s$ possible old edge sums give the claimed bound. For an edgeless graph the allowed set is empty.

## Verification and attribution

From the repository root, run

```sh
# Run at the merge commit for PR #56.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines the two parameters and the original boundedness question. `Ternary.lean` checks that the lower digits add without a carry and retain their individual values. `Solution.lean` constructs the labels for every finite simple graph and checks both implications in the adjacency rule.

OpenAI Codex devised the incidence encoding and formalized it. A search of work on exclusive sum labellings, including subsequent papers on the sum and difference indices, found no earlier bound in terms of the sum index alone.

John Haslegrave, Sum Index, Difference Index and Exclusive Sum Number of Graphs, Question 3 in the journal article, Question 5.4 in arXiv:2104.06959. [Publication](https://link.springer.com/article/10.1007/s00373-023-02624-0)
