# Consecutive patterns occur throughout the interval between their thresholds

Choose a permutation of $n$ letters uniformly among those with exactly $m$ inversions. Every fixed consecutive pattern appears with probability tending to one throughout the interval predicted by Bevan and Threlfall. For example, the probability of finding four adjacent entries in relative order $2143$ tends to one whenever

$$
\sqrt n\ll m,\qquad n^{3/4}\ll \binom n2-m.
$$

Here $f\ll g$ means $f/g\to0$. An inversion is a pair of entries in decreasing order. Write $N=\binom n2$. If a pattern $\pi$ of length $k$ has $s$ inversions, its complement (reverse all value comparisons) has $s'=\binom k2-s$ inversions. The conjecture requires $n^{1-1/s}\ll m$ and $n^{1-1/s'}\ll N-m$. A side with zero inversions needs no condition. The result allows any sequence of valid inversion counts, including sequences that alternate between the two halves of the interval. [Original conjecture, §5, p. 20](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p6/pdf/)

## A short proof of the missing middle

Bevan and Threlfall proved the result near both endpoints in Theorem 1. The following argument covers the middle. Reflection of the values lets us work with $m\le N/2$.

Let $A_h$ count the permutations with $h$ inversions. Give a permutation $\sigma$ weight $q^{\operatorname{inv}(\sigma)}$. Conditional on the inversion count, this law is uniform. For $m>0$, take $q=A_{m-1}/A_m$. The sequence $(A_h)$ is symmetric and log-concave. Its generating polynomial is the product of $1+x+\cdots+x^{j-1}$ for $1\le j\le n$. Thus $0<q\le1$, and the tilted layer weights at $m-1$ and $m$ tie for the maximum. In particular, the tilted law gives layer $m$ probability at least $1/(N+1)$.

To bound $q$ from below, encode a permutation by its inversion digits. Each digit counts the smaller entries to the right of that position. For a code of sum $m$, decrease a positive digit $e_i$ by one and give this move weight $e_i$. Each starting code contributes $m$. A code of sum $m-1$ receives weight at most $\sum_i(e_i+1)=m-1+n$. Hence $m A_m\le(m-1+n)A_{m-1}$, so $q\ge1/2$ whenever $m\ge n$.

Partition the positions into disjoint blocks of length $k\ge1$, with a possible remainder. Fix the set of values in each block. Inversions between different blocks are then fixed, so relative orders within the blocks are independent. Each complete block has probability at least $q^s/k!$ of having order $\pi$. For $n\le m\le N/2$, conditioning on layer $m$ therefore gives

$$
\Pr(\text{no occurrence}\mid m)\le (N+1)\left(1-\frac{2^{-s}}{k!}\right)^{\lfloor n/k\rfloor}\longrightarrow 0.
$$

For $m<n$ and $s>0$, Theorem 1 applies above the lower threshold, since $m\ll n^{1+1/k}$. For $s=0$ the same block argument has probability at least $1/k!$ at every $q$, and the permutation at $m=0$ is increasing. Reflecting the values handles the other half. The empty pattern always occurs.

## A uniform finite bound

The formal proof also covers the sparse ranges directly. For $n\ge3$, $k\ge1$, and $0\le m\le N/2$, it proves

$$
\Pr(\text{no occurrence}\mid m)\le
52\left(1-\frac{1}{k!}\left(\frac{m}{m+n}\right)^s\right)^{\lfloor n/(4k)\rfloor}.
$$

The constant comes from conditioning on the exact inversion count. Under the tilted law, the inversion digits are independent. Set $a=\lfloor n/4\rfloor$ and test blocks in the interval of positions whose digits have $a+1,\ldots,2a$ possible values. These digits determine every comparison within each test block. For each tested digit with $j$ possible values, an untouched digit has $2j$ possible values. Its generating polynomial splits as $[2j]_x=[j]_x(1+x^j)$, with $[j]_x=1+\cdots+x^{j-1}$. Thus the sum of the untouched digits contains an independent copy of the sum of the tested digits.

Let $P$ be the largest point probability of the untouched sum. The copy just constructed implies that the tested sum has largest point probability at least $P$. Both distributions are log-concave. Each places at least half its mass within $L=\lceil2/P\rceil$ of a mode. To see this, the mass at distance $L$ on either side is at most half the peak by monotonicity and normalization. Log-concavity then bounds each farther mass by half the mass $L$ steps closer. Their sum is at most $1/2$.

By independence, an interval of $4L+1$ integers contains at least $1/4$ of the mass of the total. Since $(4L+1)P\le13$, a modal total has probability at least $P/52$. For any event determined by the tested digits, the probability of the event and total $m$ together is at most $P$ times the event probability. Conditioning at the mode therefore costs at most a factor of $52$. Testing the disjoint blocks as above gives the displayed estimate. Its right side tends to zero because $n(m/(m+n))^s\to\infty$ above the lower threshold. Complementation gives the upper half.

## Source and verification

David Bevan and Dan Threlfall, *Thresholds for Patterns in Random Permutations with a Given Number of Inversions*, Electronic Journal of Combinatorics **31** (2024), P4.6, Conjecture 21. The authors established the endpoint thresholds. Their 2023 talk announced the thresholds, and their journal article explicitly leaves the interval between them open. Threlfall’s 2025 thesis, Theorem 6.4.3, retains the endpoint restrictions. Bevan’s earlier preprint on local uniformity records gaps in its proofs. Crane, DeSalvo and Elizalde studied consecutive-pattern avoidance under Mallows weights. A search of the citing literature and these works found no earlier proof for the whole interval at a prescribed inversion count. [Journal article](https://doi.org/10.37236/12601) · [2023 talk](https://combinatorics.cis.strath.ac.uk/scm2023/Threlfall.pdf) · [Thesis](https://stax.strath.ac.uk/downloads/4b29b664s) · [Local uniformity preprint](https://arxiv.org/abs/1908.07277) · [Mallows avoidance](https://arxiv.org/abs/1609.01370)

OpenAI Codex developed the arguments and the Lean formalization. A separate Codex agent checked the source, challenged the estimates, and independently enumerated all permutations through $n=10$. [Conjecture statement](Statement.lean) · [Finite bound](Conditional.lean) · [Final theorem](Solution.lean)

From this branch run the commands below. The project pins Lean 4.36.0 and the exact Mathlib revision in `lake-manifest.json`. The final theorem checks its transitive axiom list against `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake exe cache get
lake build
lake env leanchecker conjectures.ConsecutiveThreshold.Solution
```
