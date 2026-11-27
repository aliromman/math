# Disproof of Brown and Mol’s conjecture on uniqueness of node-reliability fixed points in graphs with two or more cut vertices

Keep each vertex of a graph independently with probability $p$. Write $R_G(p)$ for the probability that the surviving vertices form a nonempty connected graph. Brown and Mol proved that if a connected graph has at least two cut vertices, then $R_G(p)=p$ at least once in $(0,1)$. They conjectured uniqueness for every graph with at least two cut vertices. For every integer $t$, we construct such a graph with at least $t$ distinct interior fixed points. [*The shape of node reliability*, §4, immediately after Corollary 4.2](https://arxiv.org/pdf/1703.10573#page=16)

## A counterexample on 36 vertices

Take ten cliques in a row with the following sizes.

```math
1,\;1,\;5,\;5,\;5,\;5,\;8,\;4,\;1,\;1.
```

Join every vertex in each clique to every vertex in the next one. The second and ninth cliques each consist of a cut vertex. The surviving graph is connected and nonempty exactly when the occupied cliques form one nonempty interval.

| $p$ | $1/8$ | $1/4$ | $1/3$ | $1/2$ |
|---|---:|---:|---:|---:|
| $R_G(p)-p$, rounded | $+0.097511$ | $-0.003132$ | $+0.002013$ | $-0.021785$ |

The signs give three roots in disjoint intervals by continuity. Here is a short way to reproduce the calculation with rational arithmetic. Scan the cliques from left to right. Let $E,A,F$ be the probabilities that the occupied interval is empty, reaches the current clique, or has already ended. Start at $(1,0,0)$. A clique of size $w$ is empty with probability $e=(1-p)^w$. Update the three probabilities by

```math
(E,A,F)\longmapsto\big(Ee,\;(E+A)(1-e),\;(A+F)e\big).
```

At the end $R_G(p)=A+F$. The formal proof evaluates the equivalent sum over the occupied intervals at all four rational points.

## Arbitrarily many fixed points

For every $t$, one connected graph with two cut vertices has at least $t$ distinct fixed points in $(0,1)$. Its cliques form a path. At some values of $p$ the active cliques usually form a single interval. At others, two large active cliques have two very small cliques between them. Both small cliques must be active to connect the large ones.

Here is an explicit family. Use $n=3t+4$ layers and set $B=2^n+2$. Start with a clique of size $B^{64\cdot 16^t}$. For $j=0,\ldots,t-1$ let $q=16^{t-1-j}$ and append three cliques of sizes $B^{4q},B^{4q},B^{32q}$. Finish with three singleton layers. Removing the first or second of those last three vertices disconnects the graph.

At $p=B^{-12q}$, the initial clique and the current large clique each have probability at most $p/B$ of being empty. This follows from $(1-p)^w\le 1/(1+wp)$ for a clique of size $w$. If they are both active, each intermediate clique of size $B^{4q}$ must be active. The probability that both are active is at most $(pB^{4q})^2\le p/B$. Thus each connected occupation pattern has probability at most $p/B$. There are $2^n<B$ patterns, so reliability is strictly below $p$.

At $p=B^{-3q}$, prescribe that every layer up to the current large clique is active and that every later layer is empty. Earlier layers have size at least $B^{3q+1}$, and later layers have size at most $B^{3q-1}$. Each prescribed outcome has probability at least $1-1/B\ge 1/2$. The layers are independent. This connected pattern has probability at least $2^{-n}>p$, so reliability is strictly above $p$. The $t$ intervals $(B^{-12q},B^{-3q})$ are disjoint. Continuity gives one fixed point in each.

## Prior work and verification

Brown and Mol also found graphs without cut vertices that have two interior fixed points. Brown later proved that node reliability can have arbitrarily many intervals of decrease and inflection points. Yu studied intersections of reliability polynomials and tabulated fixed points for two finite graph classes. Searches by title, author, cut vertex and fixed point found no previous counterexample to the uniqueness conjecture or proof of the unbounded fixed-point theorem. [Brown, *Discrete Applied Mathematics* 313 (2022)](https://doi.org/10.1016/j.dam.2022.02.002) · [Yu, *Properties of Node Reliability Polynomials* (2022)](https://repository.tudelft.nl/record/uuid:1e3f4a48-50b5-4e7d-9907-6f052fcc3216)

Run these commands from the repository root. The theorem `three` gives the three intervals. Theorem `resolution` refutes uniqueness, and `unbounded_fixed_points` gives the family.

```sh
# Run at the merge commit for PR #101.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

OpenAI Codex found the example and the family and wrote the mathematical and Lean proofs.
