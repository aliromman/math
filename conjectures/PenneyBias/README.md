# Disproof of Drexel, Peng and Richey’s Conjecture 1 on bias monotonicity in Penney’s ante

Toss a coin until either `1100` or `000` appears. The longer word wins with probability $7/12$ for a fair coin. It wins with probability exactly $1/2$ at a head probability $r\approx0.4508661$. For every length cap $n\ge4$, the number of strictly favored longer words, counted with their opponents, increases between $r$ and every sufficiently close bias to its right.

Drexel, Peng and Richey conjectured that this count is nonincreasing on $0<p<1/2$ for all sufficiently large $n$. Their count uses a strict majority. A tie at $r$ therefore matters. [Original paper, Conjecture 1, p. 2](https://doi.org/10.37236/13609)

## The race

Write $p$ for the chance of `1`, $t=1-p$, and $u=pt$. Let $a$ and $b$ be the chances of an eventual win after seeing `1` and `11`, respectively. From `11`, wait for the next `0`. The following bit either wins the race or returns it to state `1`, so $b=t+pa$. The win chances from `00` and `0` are $pa$ and $p(1+t)a$. One step from `1` now gives $a=tp(1+t)a+pb$, hence $a=p/(1-u)$. Starting from the empty word gives

$$
P_p(1100\text{ before }000)=\frac{p^2+pu+u^2}{1-u}.
$$

This exceeds $1/2$ precisely when $2(p^2+pu+u^2)+u-1>0$. Both $p$ and $u$ increase on $[0,1/2]$. The expression changes from $-1$ to $1/8$, so it has a unique zero $r$ there.

## Why one race decides the count

Fix $n\ge4$. Each pair that wins strictly more than half the time at $r$ already does so within some finite number of tosses. Its win probability by that time is a polynomial in $p$, so it still exceeds $1/2$ near $r$. There are finitely many such pairs. All of them therefore persist on one common neighborhood. The pair `(1100, 000)` ties at $r$ and joins them immediately to the right. The count increases by at least one. This argument compares the value **at** the tie with values just above it.

## Verification and prior work

The statement counts ordered pairs of binary words and uses the probability of a strictly earlier first occurrence. The proof derives the displayed formula from the finite-horizon coin process and proves the increase for every cap from four onward. [Statement](Statement.lean) · [Probability calculation](Witness.lean) · [Proof](Solution.lean)

```sh
# Run at the merge commit for PR #74.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The authors had already shown that an individual pair of equal-length words can have a nonmonotone win probability. That example stays below $1/2$. Searches by paper title, author names, conjecture number, and the longer-word count found no earlier disproof of Conjecture 1. OpenAI Codex found the crossing argument and wrote the mathematical proof and Lean formalization. A separate agent checked the source and independently derived the crossing with the paper's overlap formula.

Drexel, Peng and Richey, “Word Length, Bias and Bijections in Penney’s Ante,” Electronic Journal of Combinatorics 32 (2025), P4.57, Conjecture 1, p. 2, DOI 10.37236/13609. [Publication](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p57/pdf/#page=2)
