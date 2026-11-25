# Three almost-complete graphs refute the odd sandpile conjecture

Take three disjoint copies of $K_5$. Delete one edge $u_i v_i$ in each copy and join $v_i$ to $u_{i+1}$, with indices modulo three. The resulting 15-vertex graph has the maximal stable sandpile as its group identity for every choice of sink.

Rupert Li conjectured that the only biconnected graphs of odd order with this property are cycles and complete graphs. Yibo Gao and Li restated the conjecture as Question 3.5. Their exhaustive search through 11 vertices found no counterexample. They also gave rings of copies of $K_4$ minus one edge, all of even order. [Li, slide 16](https://math.mit.edu/research/highschool/primes/materials/2019/conf/5-1-Li.pdf) · [Gao and Li, Example 3.1 and Question 3.5](https://arxiv.org/pdf/2008.10079).

## Proof

A cycle visits all 15 vertices. Within each block it runs from $u_i$ through the three interior vertices to $v_i$. It then crosses the new edge to the next block. Removing any vertex leaves a spanning path. The graph has degree four at every vertex, and $u_i$ and $v_i$ are nonadjacent.

For a sink $s$, the maximal stable configuration puts three chips at every other vertex. This configuration is recurrent. From any stable configuration, add the missing chips at each vertex. The result is already stable.

It remains to show that this configuration represents zero in the sandpile group. Write $L$ for the graph Laplacian. It suffices to find an integer function $f$ on the vertices with $f(s)=0$ and

$$
(Lf)(x)=4f(x)-\sum_{y\sim x}f(y)=3\qquad (x\ne s).
$$

Rotation of the three blocks, reflection of the ring, and permutation of the three interiors within each block give two types of sink. The table lists $f$ in the order $u_i$, three interior vertices, $v_i$. In each column the sink is the entry zero.

| Block | Terminal sink | Interior sink |
| --- | --- | --- |
| 0 | $(0,8,8,8,13)$ | $(12,0,9,9,12)$ |
| 1 | $(25,28,28,28,28)$ | $(27,31,31,31,32)$ |
| 2 | $(25,23,23,23,18)$ | $(32,31,31,31,27)$ |

For example, in the terminal-sink column an interior vertex of block zero has neighbors with values $0,8,8,13$, giving $4\cdot8-(0+8+8+13)=3$. Applying the same formula at each nonsink proves the assertion.

## Verification and prior work

`Statement.lean` defines legal firings, recurrence, the reduced Laplacian condition, and the original conjecture. `Solution.lean` verifies the integer equations at every nonsink for each of the 15 sinks, proves connectivity after each vertex deletion, and checks the theorem's axioms. From the repository root run

```sh
lake exe cache get
lake build
lake env leanchecker conjectures.GaoLiSandpile.Solution
```

Searches for work citing Gao and Li, the named property, the conjecture, and rings of complete graphs with one missing edge found no previous odd-order counterexample. The construction extends the authors' diamond-ring idea. Codex found the example, derived the certificates, and wrote the Lean formalization. An independent agent checked the definitions and replayed the sandpile operation directly. For every sink, stabilizing two copies of the maximal stable configuration returned one copy.
