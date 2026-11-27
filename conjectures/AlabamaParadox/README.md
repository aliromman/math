# Proof of Janson and Linusson’s conjecture on the probability of the Alabama paradox under Hamilton’s method

When Hamilton's method assigns seats, increasing the size of the house can make a state lose a seat. For fixed, rationally independent population shares, the limiting fraction of house sizes where this happens to **any** state is at most

$$
1-\frac{2}{e}=0.264241\ldots.
$$

This proves a conjecture of Svante Janson and Svante Linusson. Their examples approach this constant as the number of states grows. Their previous upper bound was $1/e$. The probability here comes from varying the number of seats while keeping the population shares fixed. The conjecture appears after Corollary 2.3 of the journal article and after Corollary 2.4 of the preprint. [Journal article](https://doi.org/10.1239/jap/1346955333) · [Preprint, pp. 6–7 and Example 7.2](https://arxiv.org/pdf/1104.2137)

## Freeze the last winning remainder

Write $p_j$ for state $j$'s population share. At house size $n$, Hamilton first assigns $\lfloor np_j\rfloor$ seats, then gives the remaining seats to the states with the largest fractional remainders. Let $i$ be the last winner and let $c=\{np_i\}$. The allocation to state $j$ is exactly

$$
a_j=\lfloor np_j+1-c\rfloor.
$$

Keep this cutoff fixed while increasing $n$ by one. No frozen allocation decreases. A state $j\ne i$ gains one frozen seat exactly when

$$
\{n(p_j-p_i)\}\ge 1-p_j.
$$

The cutoff state itself cannot gain. If at most one state crosses, the frozen allocations use at most $n+1$ seats. Hamilton can then award all these seats and fill any vacant seat by lowering the cutoff. **A loss requires at least two crossings.**

Janson and Linusson's flag lemma gives each state an equal chance to be the last winner. Conditional on that state, the relative remainders of all the other states are independent and uniform in the limit. Their crossing indicators are therefore independent Bernoulli trials with success probabilities $p_j$. Add one independent trial for the cutoff state, with probability $p_i$. This can only increase the chance of seeing at least two successes. The resulting trials have total mean one.

## Why the constant is $2/e$

For independent trials with $\sum p_j=1$, the probability of zero or one success is

$$
\prod_j(1-p_j)\left(1+\sum_j\frac{p_j}{1-p_j}\right)\ge\frac{2}{e}.
$$

This inequality also follows from Hoeffding's extremal theorem for sums of independent trials. Our proof applies concavity of $\log$ with weights $p_j$ to $(2-p_j)/(1-p_j)$. The scalar inequality needed is

$$
\log(1-x)+x\log\frac{2-x}{1-x}\ge x(\log 2-1)\qquad (0\le x<1).
$$

Subtract the right side. The difference vanishes at zero and has derivative $\log t-(1-1/t)\ge0$, with $t=(1-x/2)/(1-x)$. Summing and applying concavity gives the displayed probability bound. [Hoeffding, *On the distribution of the number of successes in independent trials*](https://repository.lib.ncsu.edu/bitstream/1840.4/2268/1/ISMS_1955_128.pdf)

## Verification and attribution

The Lean theorem proves both existence of the house-size limit and the upper bound. It starts with Hamilton's largest-remainder rule and the integer-relation definition of rational independence. The equidistribution argument is proved from Fourier approximation on the torus. The old and new allocations are locally constant away from cutoff and tie hyperplanes, which have measure zero.

Janson and Linusson introduced the flag and gave the examples that establish sharpness. OpenAI Codex derived the frozen-cutoff argument, supplied the elementary probability proof, and formalized the result. Searches of subsequent work found no earlier general proof. McCune studies three states with population shares sampled at a fixed house size. [McCune's paper](https://arxiv.org/abs/2610.40682)

From the repository root, run

```sh
# Run at the merge commit for PR #33.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```
