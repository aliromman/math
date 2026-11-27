# Disproof of the Aliste-Prieto–de Mier–Zamora conjecture on the smallest trees with the same restricted U-polynomial

Aliste-Prieto, de Mier, and Zamora predicted that the smallest such pair has 34 vertices. The two trees below have 32. For each way to delete up to five edges, record the sizes of the resulting components in any order. Every list of sizes occurs equally often in both trees. More generally, the proposed formula overestimates the minimum at **every cut depth $m\ge5$**, and the minimum has a quadratic upper bound.

![Two trees on 32 vertices. Only the right tree has an edge joining vertices of degrees six and four.](trees.svg)

The trees are nonisomorphic. In the right tree, the degree-six vertex has two neighbors of degree four. In the left tree it has none. A direct enumeration separates the trees at six cuts. The component orders $(16,4,3,3,2,2,2)$ occur three times on the left and once on the right.

## The conjecture

Write $U_m(T)$ for the polynomial in which each set of at most $m$ deleted edges contributes one monomial $\prod_C x_{|C|}$. Here $C$ runs over the components left by those deletions. Let $\Phi(m)$ be the least common order of two nonisomorphic finite unrooted trees with equal $U_m$. Conjecture 15 asserts, for $m\ge2$,

$$
\Phi(m)=
\begin{cases}
6\cdot 2^{m/2}-2,&m\ \text{even},\\
18\cdot 2^{\lfloor m/2\rfloor-1}-2,&m\ \text{odd}.
\end{cases}
$$

The predicted minima are known for $m=2,3,4$. The pair in the figure gives $\Phi(5)\le32<34$. Its exact minimum remains open. For the full chromatic symmetric function, Stanley asked whether any two nonisomorphic trees can agree at *every* cut depth. That question remains open as well. [Aliste-Prieto, de Mier and Zamora, *Discrete Mathematics* 344 (2021), 112255, Conjecture 15 and Proposition 16](https://doi.org/10.1016/j.disc.2020.112255) · [Accepted manuscript, section 4](https://upcommons.upc.edu/server/api/core/bitstreams/d37478c0-b2df-4e6e-a862-358d205545a4/content#page=12) · [Smith, Smith and Tian, small cases](https://arxiv.org/abs/1505.01889)

## Why five cuts agree

In a rooted tree, keep the size of the component containing the root separate from all other component sizes. Let $t$ count deleted edges. Two rooted polynomials whose difference is divisible by $t^h$ agree through $h-1$ cuts.

Let $X,Y$ be the path on three vertices, rooted at its middle or at an end. Their rooted polynomials $x,y$ agree at zero cuts. Forgetting the root gives the same unrooted polynomial. Write $uv$ for identifying the roots of two trees and $H(u)$ for attaching a new root by one edge. On rooted polynomials,

$$
H(u)=zu+tL(u).
$$

Here $z$ adds a vertex to the root component, and $L$ records the size of that component as an ordinary part. The variable $z$ records the root component order minus one. Thus root identification multiplies polynomials, and $L$ is linear over the ring of cut counts and ordinary components.

The construction uses four rooted trees with polynomials $a,b,c,d$.

| Pieces | Construction | First possible difference |
|---|---|---|
| $a,b$, six vertices each | Join $X$ and $Y$ by an edge; choose either endpoint of that edge as the root. | $t^2$ |
| $c,d$, eleven vertices each | $c=H(x^2)H(y^2)$ and $d=H(xy)^2$. | $t^3$ |

For the first row, keeping the joining edge gives the same contribution. Cutting it gives the common unrooted polynomial times $t(x-y)$. For the second row, write $x=y+\delta$. Linearity gives

$$
H(x^2)H(y^2)-H(xy)^2
=H(\delta^2)H(y^2)-H(\delta y)^2.
$$

Two factors of $\delta$ supply $t^2$. The terms with no further cut cancel because $(z\delta^2)(zy^2)=(z\delta y)^2$. This supplies one more factor of $t$.

Finally, connect $ac$ to $bd$ by one edge in the first tree, and $ad$ to $bc$ in the second. Keeping this edge gives the same product. When it is cut, the difference is

```math
t\,[L(ac)L(bd)-L(ad)L(bc)].
```

The determinant is linear in each of $a-b$ and $c-d$. The total difference is divisible by $t^{1+2+3}=t^6$, as required.

## A quadratic upper bound

Start with $x,y$ above. Replace any pair of rooted polynomials $u,v$ by

$$
H(u^2)H(v^2),\qquad H(uv)^2.
$$

If $t^h$ divides $u-v$, the same determinant calculation gives a factor $t^{2h+1}$ after one step. If the inputs have order $n$, the outputs have order $4n-1$. After $k$ steps the trees have order $(8\cdot4^k+1)/3$ and agree through $2^{k+1}-2$ cuts.

To see why the new trees are nonisomorphic, remove their common top root. The two components each have $(n_{\rm new}-1)/2$ vertices, so this root is the unique centroid and any isomorphism must fix it. In the first tree the two child branches have rooted types $u^2$ and $v^2$. In the second they both have rooted type $uv$. A rooted tree is determined by the multiset of its child branches. Cancellation in that multiset gives $u^2=uv$ only when $u=v$. The two starting rootings of the path are different, so induction separates every pair from the first step onward.

For $m\ge1$, take $k=\lfloor\log_2(m+1)\rfloor$. Then $k\ge1$, $2^k\le m+1<2^{k+1}$, and the construction gives

$$
\boxed{\Phi(m)\le 3(m+1)^2.}
$$

This bound replaces the conjectured exponential growth with a quadratic upper bound. Whether $\Phi(m)$ tends to infinity remains open. [Relation to Stanley's question, Proposition 16](https://arxiv.org/pdf/2002.08186#page=11)

## Where the proposed formula fails

| Maximum cuts $m$ | 5 | 6 | 7 | 8 | 9 |
|:--|--:|--:|--:|--:|--:|
| Proposed minimum | 34 | 46 | 70 | 94 | 142 |
| Order of a verified pair | 32 | 42 | 54 | 66 | 78 |

The construction also permits two different pairs of branches. If their first possible differences have degrees $i$ and $j$, exchanging the branches across a joining edge gives agreement through $i+j$ cuts. Planting both sides at a common root gives a new rooted pair whose first possible difference has degree $i+j+1$. Starting from degrees 1, 2, and 3 above gives rooted pairs of degrees at least 4 and 5 on 17 and 23 vertices. Joining pairs of degrees $(3,3),(3,4),(4,4),(4,5)$ gives the last four columns. A two-spin sum distinguishes each pair as unrooted graphs.

The third iterate of the quadratic construction has 171 vertices and agrees through 14 cuts, so it also beats the proposed values for $10\le m\le13$. For $m\ge14$, $3(m+1)^2$ is already strictly smaller than the proposed value. This follows at $m=14,15$ by substitution and then by induction in steps of two.

## Verification and provenance

From this branch, run the following commands with Elan. The project pins Lean 4.36.0 and Mathlib 4.36.0, commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```sh
lake exe cache get
python3 scripts/verify.py
```

The statement quantifies over finite tree presentations. Any finite tree admits one by choosing a root and assembling its child subtrees. Isomorphism uses the underlying unrooted simple graph. The cut expansion sums over actual edge choices and records the component sizes. The formal proof of the quadratic bound distinguishes the two unrooted graphs by an independent integer-valued two-spin sum.

The main theorems are `counterexample`, `quadratic_bound`, and `pointwise_counterexample` in the `RestrictedUMinimum` namespace. The build checks their transitive axiom lists. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.

OpenAI Codex agents developed the construction and the formal proofs. The rooted polynomial product rules and the original extremal family are due to Aliste-Prieto, de Mier, and Zamora. An independent agent rebuilt the two pictured trees and enumerated all 206,368 deletions of zero through five edges in each. The 372 nonzero partition counts agree. Extending that check through six cuts took less than one CPU minute. A search of the original paper's forward citations and of the literature for five-cut examples and polynomial upper bounds found no earlier refutation.

The initial approach combined the authors' 2017 construction with the classical counting argument for equal sums of powers. For $N$ of order $m^2\log(m+2)$, there are more subsets of $`\{1,\ldots,N\}`$ than vectors of power sums of degrees $0$ through $m-1$. Two subsets with the same vector give trees of order $O(N^2)$ by their Theorem 3.5. This yields the weaker bound $O(m^4\log^2(m+2))$ from prior methods. The smaller examples and the quadratic construction came from tracking the first unequal cut coefficient under root identification. [Aliste-Prieto, de Mier and Zamora (2017)](https://arxiv.org/abs/1509.09210) · [Borwein and Mossinghoff, classical counting bound](https://www.cecm.sfu.ca/~pborwein/PAPERS/P153.pdf)
