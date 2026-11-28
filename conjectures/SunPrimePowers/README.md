# Disproof of Sun’s Conjecture 2.1 on a real-power extension of Mandl’s inequality using Panaitopol’s nine-prime example

Take the first nine primes and raise each to the power $1/2000$. Even their geometric mean exceeds the upper bound that Sun proposed for their arithmetic mean.

Let $p_n$ be the $`n`$th prime. Sun conjectured that for every real $\alpha>0$ and every $n\ge 2\lceil\alpha\rceil^2+\lceil\alpha\rceil+6$,

$$
\frac1n\sum_{k=1}^n p_k^\alpha < \frac{p_n^\alpha}{1+\alpha}.
$$

At $\alpha=1$ this is Mandl’s inequality. Sun reported checking the integer exponents from 2 through 700 up to $n=10^6$. The counterexample uses a small positive exponent. [Zhi-Wei Sun, *Conjectures involving arithmetical sequences*, Conjecture 2.1 and Remark 2.1 (2013)](https://arxiv.org/pdf/1208.2683#page=2)

## Proof

At $\alpha=1/2000$ the threshold is $n=9$, with $p_9=23$. Write $P=2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19\cdot23=223092870$. The arithmetic mean is at least $P^{1/18000}$ by AM–GM. This exceeds the proposed bound because

$$
P\left(\frac{2001}{2000}\right)^{18000}>23^9.
$$

Three rational comparisons give a shorter exact check:

$$
\left(\frac{2001}{2000}\right)^{80}>\frac{1301}{1250},\qquad
\left(\frac{1301}{1250}\right)^{25}>\frac{125}{46},\qquad
P\left(\frac{125}{46}\right)^9>23^9.
$$

Panaitopol had already found that the geometric mean of the first nine primes exceeds $23/e$. Applied to Sun’s later conjecture, this gives a disproof for sufficiently small positive exponents. The derivative at zero of $P^{\alpha/9}-23^\alpha/(1+\alpha)$ is positive. The integer certificate above gives an explicit exponent. [Panaitopol (1999), p. 54](https://nntdm.net/papers/nntdm-05/NNTDM-05-2-52-54.pdf#page=3)

Panaitopol’s observation supplies the obstruction. The certificate here specifies an exponent and verifies the strict inequality with integers. Work on the classical inequality includes [Axler (2019)](https://doi.org/10.5802/jtnb.1081) and [Alzer and Hassani (2024)](https://doi.org/10.13137/2464-8728/36463).

## Verification

From the repository root run

```sh
# Run at the merge commit for PR #16.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The proof computes the ninth prime and the product of the first nine primes. OpenAI Codex found the counterexample and wrote the argument and Lean proof.

Zhi-Wei Sun, “Conjectures involving arithmetical sequences” (2013), Conjecture 2.1 and Remark 2.1, arXiv:1208.2683v9, p. 2. [Publication](https://arxiv.org/pdf/1208.2683v9#page=2)
