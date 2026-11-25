# An optimal power of a permutation changes just one cycle length

On eight letters, raising every permutation to the 421st power leaves all permutations fixed except the eight-cycles. It pairs each eight-cycle with its fifth power. This gives $40{,}320-5{,}040/2=37{,}800$ components. No other exponent from 2 through 839 gives as many.

Matt Larson asked which exponent $2\le a<\exp(S_n)$ maximizes the number $N(a,S_n)$ of components in the graph that joins each permutation $g$ to $g^a$. The rule below gives **every maximizing exponent for every $n$**. It uses at most $n(n+1)/2$ trial pairs and requires no enumeration of permutations. [Larson, *Power maps in finite groups*, Integers 19 (2019), A58, Question 2](https://math.colgate.edu/~integers/t58/t58.pdf)

## The rule

Let $L=\operatorname{lcm}(1,\ldots,n)$. For each $n/2<k\le n$ with $k\ge2$, let $B_k$ be the least common multiple of the lengths from 1 through $n$ other than $k$. Form $a=1+jB_k$ for $1\le j\le k$. Keep the pairs with $a<L$ and $a\not\equiv1\pmod k$. If $k$ is an odd prime, keep only $a\equiv-1\pmod k$.

Assign each remaining length the weight

$$
w(k)=\begin{cases}
1/2 & k=2,\\
1/(2k) & k\text{ is an odd prime},\\
(1-1/p)/k & k\text{ is composite, with least prime factor }p.
\end{cases}
$$

The exponents attached to the least weight are exactly the answers. Their component count is $n!(1-w(k))$. For $n\le2$ the exponent range is empty.

## Why one length suffices

The cycle containing a specified letter has each length from 1 through $n$ in exactly $(n-1)!$ permutations. Call a length $k$ exceptional if $a\not\equiv1\pmod k$. Two exceptional lengths therefore move at least $2(n-1)!$ permutations. A finite map loses at least half as many components as it moves points. Each periodic orbit of length at least two contributes one component, and a point outside the periodic orbits contributes none.

Bertrand's postulate gives an odd prime $n/2<p\le n$ for $n\ge3$. The Chinese remainder theorem gives an exponent that fixes all other lengths and inverts the $p$-cycles. Its loss is $n!/(2p)<(n-1)!$. Thus each optimizer has just one exceptional length $k$. Also $2k>n$, since $2k$ would otherwise be a second exceptional length.

Exactly $n!/k$ permutations contain this long cycle. For an odd prime $k$, inversion pairs them and gives the smallest possible loss. For composite $k$, write $p$ for its least prime factor and $u=a-1$. Both $p$ and $k/p$ divide $u$. Thus $u^2\equiv pu\equiv0\pmod k$ while $u\not\equiv0\pmod k$. The binomial theorem gives $(1+u)^r\equiv1+ru\pmod k$, so all the affected orbits have length $p$. This proves the weight formula. For $k=2$, the even exponent removes the transposition from the periodic orbits.

## Verification and attribution

`Statement.lean` defines components of the actual power graph and the original maximum predicate. In `Solution.lean`, `exact_answer` proves that the arithmetic rule gives exactly all maximizers. The theorem `eight` checks both numbers in the example. From the repository root, run

```sh
lake build conjectures.LarsonPowerMap.Solution
lake env leanchecker conjectures.LarsonPowerMap.Solution
```

Larson's Lemma 1 counts components using periodic points. The new argument compares the losses from different cycle lengths and determines which exponents maximize the count. OpenAI Codex agents developed the argument, wrote the formal proof and performed an independent audit. A separate computation checked every exponent for $3\le n\le16$. Searches for Larson's question, extremal power maps and later papers citing his work found no previous solution to Question 2.
