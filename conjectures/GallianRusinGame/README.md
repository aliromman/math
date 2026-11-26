# One 30-sided die needs four dice

Exactly 44 distinct 30-sided dice can take part in a game whose sum has the same distribution as the sum of ordinary dice. Of these, 43 can appear in a game of three. One requires four. Its face counts, in order for labels 1 through 14, are

$$
(1,0,2,2,3,3,4,4,3,3,2,2,0,1).
$$

## The original conjecture

J. A. Gallian and D. J. Rusin defined the *game-size* of a die to be the smallest number of dice in such a game. They use positive integer labels and identify dice that differ only by a permutation of their faces. On p. 256 of *Cyclotomic polynomials and nonstandard dice*, Discrete Mathematics **27** (1979), 245–259, they conjectured that the maximum game-size for 30 faces is four. They gave the upper bound 870 and reported a die of game-size four. The final paragraph records 44 as a lower bound on the number of solution dice. Chao, Gabel, Larson, and Nasr later classified games with two dice and a product of three distinct primes as the face count. [Original article](https://doi.org/10.1016/0012-365X(79)90161-4) · [Two-dice classification](https://arxiv.org/abs/2408.10331)

## A bound that covers every game

Write $P(X)=\sum_f X^{f-1}$ over the faces of one die. If it belongs to an $n$-dice game of size $m$, it divides $(1+X+\cdots+X^{m-1})^n$. All its roots are $m$-th roots of unity. If $\Phi_d^e$ divides $P$ and $\ell$ is a prime that does not divide $m$, then

$$
\ell^e\le m^{\ell-1}.
$$

Take the product of $|P(z)|$ over the primitive $d\ell$-th roots $z$. Every factor is at most $P(1)=m$. Write $P=\Phi_d^eD$. The corresponding product for $D$ is a nonzero integer in absolute value, since no such root has order dividing $m$. The product for $\Phi_d$ is $\ell^{\varphi(d)}$ by the classical cyclotomic resultant formula. Since there are $(\ell-1)\varphi(d)$ roots, the inequality follows. The Lean proof derives the needed lower bound for the resultant directly from $\Phi_{d\ell}\equiv\Phi_d^{\ell-1}\pmod\ell$. [T. M. Apostol, *Resultants of cyclotomic polynomials*](https://doi.org/10.1090/S0002-9939-1970-0251010-X)

For $m=30$, use $\ell=7$. The multiplicity of every factor is at most 10. Evaluating at one fixes $\Phi_2,\Phi_3,\Phi_5$ at multiplicity one. This leaves $11^4=14{,}641$ choices for the exponents of $\Phi_6,\Phi_{10},\Phi_{15},\Phi_{30}$.

A base-256 digit check reduces this list to 44. For an actual die, the digits of $P(256)$ are its face counts. Each excluded choice has a digit at least 128 among its lowest 16 digits. For all 44 remaining choices the proof verifies nonnegative coefficients with sum 30.

For 43 choices, two companions complete a three-dice game. The exception has $P=\Phi_2\Phi_3\Phi_5\Phi_6^3$. In a four-dice game it has two companions whose four exponents are $(0,1,1,1)$ and a third with $(1,2,2,2)$. Together with the exception's $(3,0,0,0)$, each exponent sums to four. Checking all possible pairs of companions excludes a game of three. Any smaller game could be padded to three with standard dice.

## Verification

Run the following commands from the repository root.

```sh
lake exe cache get
lake build conjectures.GallianRusinGame.Solution
lake env leanchecker conjectures.GallianRusinGame.Solution
```

`Statement.lean` defines the face distribution, games, and the conjectured maximum. `Multiplicity.lean` proves the bound for any auxiliary prime. `Solution.lean` proves the exact number of dice, the uniqueness and face labels of the exception, and the conjecture. Lean checks all numerical certificates in its kernel.

Searches for the original article, game-size four, the 30-faced case, later work on exotic dice, and public proof catalogues found the original witness and the two-dice classification. No earlier proof of the upper bound four was located. AI developed the upper bound argument, the enumeration, and the Lean proofs. The original paper supplies the cyclotomic model and the earlier lower witness.
