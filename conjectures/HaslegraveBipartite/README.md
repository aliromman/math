# Solution to Haslegrave’s Question 1 on difference and sum indices of bipartite graphs

For every positive integer $d$, there is a finite connected bipartite graph with

$$
\operatorname{dif}(G)=d,\qquad \operatorname{sum}(G)=d+1.
$$

To define these indices, label the vertices by distinct integers. Count how many different absolute differences occur on the edges, or how many different sums occur. Minimize each count over all labellings. John Haslegrave asked whether a bipartite graph can have an arbitrarily large difference between its difference index and half its sum index, rounded up. The graphs above have gap $\lfloor(d-1)/2\rfloor$. The previous bipartite example cited in the question had gap one. [*Sum Index, Difference Index and Exclusive Sum Number of Graphs*, Question 1, Graphs and Combinatorics 39 (2023)](https://doi.org/10.1007/s00373-023-02624-0)

## A graph from base-B digits

Make a left and a right copy of the integers from $0$ to $B^d$. Join $L_x$ to $R_y$ exactly when

$$
y-x\in\{0,1,B,B^2,\ldots,B^{d-1}\}.
$$

Label $L_x$ by $x$ and $R_y$ by $-y-1$. This gives exactly $d+1$ edge sums. Every labelling needs that many because $L_0$ has $d+1$ neighbors.

Now label $L_x$ by $2x$ and $R_y$ by $2y-1$. The shifts zero and one both produce absolute difference one. Each other shift gives one more difference, so $d$ suffice.

## Why fewer differences cannot work

From $L_x$ one can increase $x$ by a power of $B$ in two edges, via $R_{x+B^i}$. The base-$B$ digits therefore put every $L_x$ with $x<B^d$ within $2dB$ edges of $L_0$.

Suppose an injective labelling used only $k$ edge differences. Along any walk of length at most $r$, the displacement is an integer combination of those $k$ differences. Each coefficient lies between $-r$ and $r$. There are at most $(2r+1)^k$ possible displacements. In this graph that gives

$$
B^d\le (4dB+1)^k.
$$

Take $B=(4d+1)^{d-1}+2$. For $k\le d-1$ the right side is at most $(4d+1)^{d-1}B^{d-1}<B^d$. This proves the claimed difference index. Harrington and coauthors used signed difference counts to bound the size of spheres in trees. Here the growth of the base-$B$ graph determines its exact index. [Harrington et al., §3.3](https://arxiv.org/pdf/2008.09265#page=28)

## Verification and attribution

Run from the repository root with the pinned Lean and Mathlib releases.

```sh
# Run at the merge commit for PR #53.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The statement defines both minima over injective integer labellings of finite simple graphs. The proof verifies the two labellings, the degree obstruction, and the displacement count. Axiom guards cover the exact indices and the answer to Question 1.

OpenAI Codex found the construction and growth argument and wrote the formal proof. A search of subsequent papers on both indices located no earlier answer to this question.

John Haslegrave, Sum Index, Difference Index and Exclusive Sum Number of Graphs, Question 1 in the journal article, Question 5.1 in arXiv:2104.06959. [Publication](https://link.springer.com/article/10.1007/s00373-023-02624-0)
