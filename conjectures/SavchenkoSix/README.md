# Proof of Savchenko’s conjecture on the minimum number of directed six-cycles in a regular tournament

Seat an odd number $n$ of players around a circle. Each player beats the next $(n-1)/2$ players clockwise. Every other tournament on the same players in which everyone wins equally often has at least as many directed six-cycles. This proves Sergey Savchenko’s minimum conjecture, announced in 2010 and published in the *Journal of Graph Theory* in 2016. He had determined the cycle count for this circular tournament and the maximum for regular tournaments. [2010 announcement, p. 18](https://people.dm.unipi.it/ilas2010/pdf/abstracts-ct.pdf) · [Original article](https://doi.org/10.1002/jgt.21914)

A cycle visits six distinct players and is counted once up to cyclic rotation. With seven players the minimum is 28. The proof reduces tournaments of every size to a single inequality on seven players.

## A local inequality

Put $S_{ij}=1$ if player $i$ beats player $j$, $S_{ij}=-1$ if $j$ beats $i$, and $S_{ii}=0$. For a vertex set $U$ let $S_U$ denote the principal submatrix. Write

$$
D_k(T)=\sum_{|U|=k}(\det S_U-1).
$$

Every four-vertex determinant is the square of a signed sum of three numbers in $\{-1,1\}$. Hence it is one or nine and $D_4\ge0$. For the carousel, a permutation and simultaneous sign changes to rows and columns transform $S$ into the sign matrix of a linearly ordered tournament. Its four-vertex and six-vertex principal determinants all equal one.

On every seven-vertex tournament, regular or otherwise,

$$
D_6\le 3D_4.
$$

Multiplying a row and its matching column by $-1$ preserves all principal determinants. Use this to set the six off-diagonal entries of the first row to $1$. Order the six remaining players along a directed path. To extend the path, insert each new player just before the first player it beats, or at the end if it beats none. The path fixes five more signs. The certificate checks the remaining $2^{10}=1024$ orientations using the squares of the four- and six-vertex Pfaffians. Summing the inequality over all seven-vertex subsets of a tournament on $n\ge7$ players gives

$$
(n-6)D_6\le 3\binom{n-4}{3}D_4,
\qquad D_6\le\binom{n-4}{2}D_4.
$$

## Counting simple cycles

Let $R_n$ denote the carousel and $c_6$ the number of simple directed six-cycles. For any regular tournament $T$ on the same players the exact difference is

$$
64\bigl(c_6(T)-c_6(R_n)\bigr)=\left(\binom n2-14\right)D_4(T)-D_6(T).
$$

To obtain the identity, first count closed walks by the trace of the sixth power of the adjacency matrix. A repeated vertex must occur at opposite positions of the walk. Inclusion–exclusion over the three opposite pairs leaves a fourth-power trace correction when two regular tournaments are compared. If $A$ is the adjacency matrix, regularity gives $2A+I=S+J$ and $SJ=JS=0$ for the all-ones matrix $J$. Expansion then leaves the difference of $\operatorname{tr}S^6+21\operatorname{tr}S^4$. Newton’s identities express these traces in sums of principal minors and give the displayed formula.

Since $\binom n2-14-\binom{n-4}{2}=4(n-6)$, the local inequality proves the stronger bound

$$
c_6(T)-c_6(R_n)\ge\frac{n-6}{16}D_4(T).
$$

For odd orders below seven there are no six-cycles.

## Prior work and verification

Savchenko restated the minimum conjecture in 2024. The 2022 work of Grzesik, Král’, Lovász, and Volec treats maximum cycle densities. Searches using the original title, citations and later results on regular tournaments found no earlier proof of the finite minimum. OpenAI Codex derived the seven-vertex inequality and the exact deficit, formalized the argument, and ran a separate mathematical and kernel audit. [Savchenko’s restatement](https://arxiv.org/abs/2403.07629) · [Maximum cycle densities](https://doi.org/10.1016/j.jctb.2022.07.007)

```sh
# Run at the merge commit for PR #95.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines the conjecture. In `Solution.lean`, `resolution` proves the minimum and `gap` proves the quantitative bound. The Lean cycle counts include all six choices of the starting player on both sides.
