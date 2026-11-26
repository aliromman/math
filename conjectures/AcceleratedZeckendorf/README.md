# The mean accelerated Zeckendorf game lasts at most a cubic logarithm

Starting with $n$ ones, the expected number of turns in the accelerated Zeckendorf game is $O((\log n)^3)$. This proves Conjecture 1.11, which asks whether the mean is $o(n)$. The authors previously proved a logarithmic minimum game length and a linear upper bound on every game. Their simulations suggested sublinear growth. The estimate here excludes growth of order $n^\delta$ for every fixed $\delta>0$. It leaves the precise order between a logarithm and its cube open. [Original paper, pp. 4–5 and 9–12](https://www.mathstat.dal.ca/FQ/Papers/62-1/milleretal04072023.pdf)

## Game and conjecture

Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin introduced this game in *The Fibonacci Quarterly* 62 (2024), 3–14. Label the coins $F_1=1,F_2=2,F_3=3,\ldots$. A unit move can combine two consecutive Fibonacci coins into the next one. It can also replace two equal coins under these rules:

$$
1+1\to2,\qquad 2+2\to1+3,\qquad
F_i+F_i\to F_{i-2}+F_{i+1}\quad(i\ge3).
$$

On one turn a player chooses one rule and a positive number of copies to apply at once. Each legal pair of rule and batch size has equal probability. A game ends when no move is legal. Conjecture 1.11 says its mean length $E_n$ satisfies $E_n/n\to0$. [Definition 1.2 and Conjecture 1.11](https://doi.org/10.1080/00150517.2024.12427372)

## Proof

Number the coin positions from zero. Give position zero weight $5$ and position $i\ge1$ weight $2i+6$. Let $V$ be the sum of the weights of all coins. Every unit move lowers $V$ by at least one, including each of the split rules. A batch of size $j$ thus lowers $V$ by at least $j$. Initially $V=5n$.

Let $L=2(1+\lfloor\log_2(n+1)\rfloor)$. Every occupied position has index below $L$, since $F_{2i+1}\ge 2^i$. If a state has $m$ coins, then $V\le(2L+6)m$.

Write $c_r$ for the largest legal batch of rule $r$, $K=\sum_r c_r$ for the number of legal moves, and $B=\sum_r c_r(c_r+1)/2$ for the sum of their batch sizes. There are at most $2L$ rule types. At each position with $a$ coins, the equal-coin rule has capacity $\lfloor a/2\rfloor$. It follows that $m\le 2K+L$. By Cauchy–Schwarz,

$$
K^2\le2L\sum_r c_r^2\le4LB.
$$

Since $K\le B$, we get $mK\le 2K^2+LK\le9LB$. Set $A=9L(2L+6)$. If play continues, the expected batch size is $B/K\ge V/A$.

For a move of size $j$ from potential $V$ to $W$, the difference $\log(1+V)-\log(1+W)$ is at least $j/(1+V)$. As $V\ge1$ while a move is legal, the expected decrease in $2A\log(1+V)$ is at least one. Sum this estimate over successive turns. Every path has ended by turn $5n$, giving

$$
E_n\le18L(2L+6)\log(1+5n).
$$

## Verification and attribution

Run the following commands from the repository root.

```sh
lake build conjectures.AcceleratedZeckendorf.Solution
lake env leanchecker conjectures.AcceleratedZeckendorf.Solution
```

The Lean statement defines the uniform choice over all legal batch sizes. The proof shows that its full expectation equals the finite recursion at horizon $5n$. The final module checks the axiom lists of the mean bound and the conjecture.

Searches for the conjecture, the game title, and expected-length bounds found no earlier solution. Subsequent work on black-hole Zeckendorf games changes the rules by discarding coins at a fixed index. The accelerated game's logarithmic minimum and its simulation data belong to the original authors. AI developed the potential argument and the Lean proof. [Black-hole game paper](https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/FQBlackHoleZeck.pdf)
