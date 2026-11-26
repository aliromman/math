# Three caterpillars beat two for every $k\ge 7$

Three caterpillars disprove Conjecture 1 of Daniel Brosch and Diane Puges
for every $k\ge7$. Join them in the shape $A\star(B\star C)$, where
$\star$ adds a common root. For $7\le k\le13$, give the branches
$196n+1$, $2n+1$, and $2n+1$ leaves. For every $k\ge14$, use
$106n+1$, $47n+1$, and $47n+1$ leaves.

A caterpillar is a rooted binary tree with a leaf at each fork along its
spine. The even tree $E_6$ has two branches of three leaves each.
The density of a pattern is the probability that a uniformly chosen subset
of leaves induces that pattern. Brosch and Puges conjectured that every
double caterpillar has the greatest possible $E_6$ density at its given
$k$-leaf caterpillar density, for every $k\ge4$. They proved the balanced
case for $k=4,5,6$. [Original paper, §§2.2–2.3 and 5.2, Conjecture 1](https://doi.org/10.1007/s10107-025-02305-1).

## Proof

First take $k\ge14$. Write $u=53/100$, $q=47/100$, and $v=q/2$. Six sampled leaves induce $E_6$
when they split three and three at the outer fork, or when they split three
and three between $B$ and $C$. In the limit this gives

$$
Y=20(uq)^3+20v^6
 =\frac5{16}+\frac{18\,048\,673}{3\,200\,000\,000\,000}.
$$

A double caterpillar with branch proportions $p$ and $1-p$ has
$E_6$ density $20[p(1-p)]^3\le 5/16$. To compare the trees at the same
horizontal coordinate, let $X_k$ be the $k$-leaf caterpillar density of
our sequence. The sample induces a caterpillar whenever all $k$ leaves
belong to $A$, or exactly one belongs to $B\star C$. Thus

$$
X_k\ge u^k+kqu^{k-1}\ge(k+1)qu^{k-1}>
\frac{k+1}{2^{k-1}}\qquad(k\ge14),
$$

because $q(2u)^{13}>1$. The right side is the caterpillar density in a
balanced double caterpillar. As $p$ varies from $1/2$ to $1$, the double
caterpillar density varies continuously from $(k+1)/2^{k-1}$ to $1$ by
equation (12) of the paper. Some $p$ therefore gives exactly $X_k$. At
that coordinate our sequence has strictly greater $E_6$ density.

For $7\le k\le13$, take $u=49/50$, $q=1/50$, and $v=q/2$. Write
$g_k(p)$ for the caterpillar density of a double caterpillar with
branch masses $p,1-p$. Counting the possible splits at the two forks gives

$$
X_k=u^k+2(k+1)v^k+k(qu^{k-1}+2kuv^{k-1}),\qquad
Y=20(uq)^3+20v^6.
$$

Set $t=q+q^5/4$. Direct substitution gives
$g_k(t)<X_k<g_k(q)$ for each of the seven integer values of $k$.
It also gives $20[t(1-t)]^3<Y$. These comparisons use rational
numbers throughout. Some $p\in[q,t]$ gives $g_k(p)=X_k$ by continuity.
Since $p(1-p)\le t(1-t)$ on this interval, its double caterpillar
has strictly smaller $E_6$ density.

All pattern densities converge along both tree sequences. Inside each
branch, every subset of leaves induces a caterpillar. At a fork, count the
subsets inside a single branch and the subsets that split between its
children. For a fixed pattern this gives a sum of products of binomial
coefficients in the branch sizes. Dividing by the number of leaf subsets
gives the asserted limits.

## Source and verification

Brosch and Puges give the double-caterpillar formulas in equations (12) and
(13). Their paper first appeared in 2024 and was published online in 2025.
Searches for the conjecture, the authors' publications and talks,
and later work on rooted-tree profiles found no earlier counterexample.
AI agents found the three-branch construction, derived the bounds for all
$k\ge7$, and wrote the proof and Lean formalization.
[Author preprint](https://arxiv.org/abs/2404.12838) ·
[Authors' presentation](https://slides.danielbrosch.com/TreesAussois/).

From the repository root, run

```sh
# Run at the merge commit for PR #34.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines unordered pattern counts, the joint profile,
and the published conjecture. `Solution.lean` proves
`fails_from_seven` and `not_conjecture` and checks the latter's axioms.
