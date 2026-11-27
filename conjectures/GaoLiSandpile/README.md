# Disproof of Li’s Odd Biconnected Graphs Conjecture on sandpile identities

Take three copies of $K_5$. Delete one edge $u_i v_i$ in each copy and join $v_i$ to $u_{i+1}$, with indices modulo three. The resulting 15-vertex graph has the maximal stable sandpile as its group identity for every sink.

The same construction works with $K_d$ for every $d\ge3$. For odd $d\ge5$ it gives a biconnected counterexample of order $3d$ to Rupert Li’s Odd Biconnected Graphs Conjecture, which states that only odd cycles and complete graphs have this property among biconnected graphs of odd order. Yibo Gao and Li restated the conjecture as Question 3.5. Their exhaustive search through 11 vertices found no counterexample. Their rings of copies of $K_4$ minus an edge have even order. [Li, slide 16](https://math.mit.edu/research/highschool/primes/materials/2019/conf/5-1-Li.pdf#page=29) · [Gao and Li, Example 3.1 and Question 3.5](https://arxiv.org/pdf/2008.10079).

## Proof

Put $h=d-2$. Each block has $h$ interior vertices and two terminals $u_i,v_i$. Every vertex has degree $h+1$. A cycle visits all vertices by going from $u_i$ through the interiors of each block to $v_i$, then crossing to the next block. Removing any vertex leaves a spanning path. For $d\ge5$ the graph has degree at least four, and $u_i$ and $v_i$ are nonadjacent.

Fix a vertex as sink. The maximal stable configuration puts $h$ chips at each nonsink. From any stable configuration, add the missing chips at each vertex to obtain this configuration. Thus it is recurrent. To see that it represents zero in the sandpile group, it suffices to find an integer function $f$ with $f(s)=0$ and

$$
(h+1)f(w)-\sum_{z\sim w}f(z)=h\qquad(w\ne s).
$$

The graph has two types of sink up to symmetry. Rotate the sink's block to block zero. If the sink is a terminal, reflect the ring if necessary to put it at $u_0$. The table gives the values of $f$ at $(u_i,\text{interior},v_i)$ in each block. In the interior-sink column, give the sink itself value zero. All other interiors in its block have the stated value. Write $x=h(d+4)$.

| Block | Terminal sink | Interior sink |
| --- | --- | --- |
| 0 | $(0,2d-2,3d-2)$ | $(4h,3h,4h)$ |
| 1 | $(d^2,d^2+d-2,d^2+d-2)$ | $(x,x+d-1,x+d)$ |
| 2 | $(d^2,d^2-2,d^2-d-2)$ | $(x+d,x+d-1,x)$ |

These entries satisfy the equation by substitution. For example, when $d=5$ and $s=u_0$, an interior vertex of block zero has value $8$ and neighbors with values $0,8,8,13$. Its Laplacian is $4\cdot8-(0+8+8+13)=3$. In general each terminal sees all $h$ interiors of its block and its matched outside terminal. Each interior sees both terminals and the other $h-1$ interiors. These two neighbor sums account for every row of the reduced Laplacian.

## Verification and prior work

`Statement.lean` defines recurrence using legal firings and defines the identity using the integer reduced Laplacian. `Solution.lean` proves the formula for every block size and sink, verifies biconnectivity and order, and checks the axioms of both the general result and the refutation. From the repository root run

```sh
# Run at the merge commit for PR #39.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Searches for the named property, the conjecture, work citing Gao and Li, and rings of cliques with one missing edge found no prior odd-order counterexample. The construction extends the authors' diamond rings. Codex found the example, derived the general potentials, and wrote the Lean formalization. An independent agent checked the source definitions, both polynomial tables, and the formal statement. Direct legal stabilization of twice the maximal configuration also returned one copy for every sink at block sizes 5, 7, 9 and 11.
