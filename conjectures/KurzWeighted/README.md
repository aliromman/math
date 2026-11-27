# Proof of Kurz’s Conjecture 8 on Banzhaf approximation in weighted voting games

For every weighted voting rule on $n\geq2$ voters, its normalized Banzhaf vector $p$ satisfies

$$
\left\|p-\frac{(2,\ldots,2,1)}{2n-1}\right\|_1\geq\frac{1}{18n}.
$$

The bound holds even for complete simple games, in which every two voters can be ranked by their ability to replace each other in a winning coalition. Equal-weight voting gives distance $2(n-1)/(n(2n-1))$, so the minimum distance has order $1/n$.

Sascha Kurz asked whether a positive constant works in place of $1/18$. Here a coalition wins if its total weight meets the quota. The Banzhaf index counts how often a voter can change a loss into a win, then divides by the total count for all voters. The distance adds the absolute error in each voter's share. [Kurz, *Ready for the design of voting rules?*, Conjecture 8](https://www.researchgate.net/publication/262992098_Ready_for_the_Design_of_Voting_Rules) · [Conjecture 15 in the 2014 preprint](https://arxiv.org/pdf/1405.0823#page=7)

## Proof

Call the first $n-1$ voters ordinary and the last voter distinguished. Let $b_i$ be voter $i$'s unnormalized number of decisive switches. Write $T=\sum_i b_i$ and $A=T/(2n-1)$. The ordinary voters would each need $2A$ switches. Their total error is $D=\sum_{i<n}|b_i-2A|$.

**Swapping voters.** In a weighted rule, swapping ordinary voters $i$ and $j$ changes the outcome on exactly $|b_i-b_j|$ coalitions. To see this, suppose $i$ can replace $j$ in any winning coalition. For a coalition $S$ containing neither voter, the difference between their switch counts receives two contributions of $1$ exactly when $S\cup\{i\}$ wins and $S\cup\{j\}$ loses. Swapping the two voters changes the outcomes of those same two coalitions.

An arbitrary permutation of ordinary voters changes at most $2D$ outcomes. Choose a moved voter $i$ with maximal $|b_i-2A|$. The swap of $i$ with its image costs at most $2|b_i-2A|$ and fixes $i$ in the remaining permutation. The triangle inequality for the number of changed outcomes proves the claim by induction.

**Making ordinary voters interchangeable.** Given a coalition, take the majority decision of all the permuted rules, counting a tie as a win. The new rule remains monotone. If it differs from the original on a coalition, at least half of the permuted rules differ there. Summing over coalitions shows that at most $4D$ outcomes have changed. Each individual switch count changes by at most $4D$, since it is the number of winning coalitions containing that voter minus the number of winning coalitions excluding that voter.

In the new rule, either the distinguished voter has zero switches or this voter can replace any ordinary voter. Indeed, if some $k$ ordinary voters lose but win upon adding the distinguished voter, then the same is true of every set of $k$ ordinary voters. A coalition of at most $k-1$ ordinary voters still loses upon adding an ordinary voter. A coalition of at least $k$ ordinary voters wins upon adding the distinguished voter.

Let $e=|b_n-A|+D$. If the new distinguished voter has zero switches, then $A\leq |b_n-A|+4D$. Otherwise compare the distinguished voter with any ordinary voter in the new rule. Their new switch counts are in the reverse weak order from the target values $A$ and $2A$. The triangle inequality gives $A\leq e+8D$. Thus $A\leq9e$ in either case. Dividing by $T$ gives $\|p-(2,\ldots,2,1)/(2n-1)\|_1\geq1/(9(2n-1))\geq1/(18n)$.

## Earlier results and verification

Kurz and Napel computed finite optima and constructed weighted voting rules with distance asymptotic to $1/(2n)$. Their analytical construction gives an upper bound on the best attainable error. The original conjecture asks for a lower bound that applies to every weighted rule. A search for the conjecture and the target vector found no earlier universal lower bound. [Kurz and Napel, Section 5.3 and Appendix B](https://arxiv.org/pdf/1202.6245#page=16)

From the repository root, run

```sh
# Run at the merge commit for PR #58.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The project pins Lean 4.36.0 and Mathlib. [Statement.lean](Statement.lean) defines the weighted conjecture directly from the vote totals and decisive switches. [Solution.lean](Solution.lean) proves it through the stronger result for complete games and checks the axioms. OpenAI Codex developed the symmetrization argument and wrote the Lean proof.
