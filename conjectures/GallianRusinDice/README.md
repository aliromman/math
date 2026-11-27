# Proof of Gallian and Rusin’s conjecture on the number of 105-sided solution dice

Gallian and Rusin asked how many different 105-sided dice can occur in a game that has the same sum distribution as ordinary dice. There are exactly **40**. Every one can occur in a game of three dice. Allowing more dice introduces no other labeling.

The 40 have a simple description. Let $i$, $j$, and $k$ range independently over $0,1,2$, over $0,\ldots,4$, and over $0,\ldots,6$. Give the 105 faces the labels

$$
1+ai+bj+ck,\qquad a\mid35,\quad b\mid21,\quad c\mid15.
$$

Take positive divisors and count repeated labels with their multiplicities. The 64 choices of $(a,b,c)$ give 40 distinct multisets. Their shared description also proves that no other type of die appears.

## The question

J. A. Gallian and D. J. Rusin posed the 105-sided conjecture on p. 259 of *Cyclotomic polynomials and nonstandard dice*, Discrete Mathematics **27** (1979), 245–259. A solution die has positive integer labels and can occur among two or more 105-sided dice whose sum frequencies agree with the same number of standard dice. Permuting the faces preserves the die. The authors had already established the lower bound of 40 for products of three distinct primes. Chao, Gabel, Larson and Nasr classified the games of two such dice in 2024. [Original article](https://doi.org/10.1016/0012-365X(79)90161-4) · [Two-dice theorem](https://arxiv.org/abs/2408.10331)

## Why the list is complete

Write $P(X)=\sum_f X^{f-1}$ for one die. Its coefficients count the faces, so they are nonnegative and sum to 105. The frequency polynomial of a standard die is $S=1+X+\cdots+X^{104}$. In a game of $n$ dice, the product of their polynomials must equal $S^n$. Thus every irreducible factor of $P$ is one of the seven cyclotomic factors of $S$. Evaluating at one fixes the multiplicities of $\Phi_3,\Phi_5,\Phi_7$ at one each.

**For every odd number $m$ of faces, a cyclotomic factor of multiplicity $e$ satisfies $2^e\le m$.** To see this, take a primitive $d$-th root $z$, where $d\mid m$, and write $P=\Phi_d^eD$. The coefficients of $\Phi_d(-X)-\Phi_d(X)$ are even. Thus $P(-z)/2^e$ is the value of an integer polynomial at $z$. It is nonzero because $-z$ is not an $m$-th root of unity, and $P$ divides a power of the standard die polynomial. Its product over all primitive $d$-th roots is a nonzero integer, the resultant with $\Phi_d$. For at least one such root, $|P(-z)|\ge 2^e$. The triangle inequality gives $|P(-z)|\le P(1)=m$.

For $m=105$, each of the four remaining exponents lies between zero and six. Only 40 of the $7^4=2{,}401$ products have valid face counts. The finite check has a short certificate. If $P$ is a die, its coefficients are the base-256 digits of $P(256)$, and each digit is at most 105. Every excluded product has a digit at least 128 among its lowest 48 digits. For every survivor the proof checks all coefficients, exhibits two companion dice, and verifies its arithmetic-progression formula.

For example, $(a,b,c)=(1,3,15)$ gives the ordinary die by mixed-radix notation. With $(a,b,c)=(1,1,1)$, all labels lie between 1 and 13, and 6 can be rolled by several different faces.

## Verification

From the repository root, run

```sh
# Run at the merge commit for PR #62.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` states the exact count. The shared dice model and polynomial arithmetic are in [GallianRusin](../GallianRusin/). The other modules prove the multiplicity bound, extract the cyclotomic factors, check the finite list, and construct each three-dice game. The final theorems include the exact classification and the count. The kernel checks all finite certificates.

Targeted searches for the 105-sided count, the original article, later work on dice relabeling, and public mathematical proof catalogues found the published two-dice classification and no earlier proof of the unrestricted count. AI developed the argument and Lean proofs. Gallian and Rusin introduced the cyclotomic method and the lower bound of 40.

Joseph A. Gallian and David J. Rusin, Cyclotomic polynomials and nonstandard dice, unnumbered conjecture on exactly 40 solution dice of size 105, p. 259. [Publication](https://www.cs.umd.edu/users/gasarch/BLOGPAPERS/nonstandarddice.pdf#page=15)
