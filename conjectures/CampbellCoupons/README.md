# Disproof of Campbell’s coupon-collection conjecture in “Games of chance with multiple objectives”

In four independent draws, **two copies of each of two types** have probability $3/8$. **One copy of each of three types** has probability $4/9$. Both games use equally likely types. Campbell conjectured that the first probability was at least the second.

Let $P(m,k;T)$ be the probability of collecting at least $m$ copies of each of $k$ types in $T$ draws. Campbell proposed that $P(m,k;T)\ge P(m-1,k+1;T)$ whenever $m\ge k-1$, with $T\ge km$. This compares two ways of changing the collection goal. The comparison can fail by an arbitrarily large factor, although it holds for every sufficiently late turn when $m,k\ge2$ are fixed. [Campbell, *Games of chance with multiple objectives*, §6, p. 311 (2007)](https://doi.org/10.1007/s00184-006-0112-5)

## Counting four draws

There are $\binom42=6$ successful words among the $2^4=16$ binary words. For three types, exactly one type occurs twice. Choose that type in three ways and arrange the four coupons in $4!/2!=12$ ways. This gives $36/81=4/9$. At five draws the ordering reverses again: $P(2,2;5)=5/8>50/81=P(1,3;5)$.

## An unbounded reversal

Take $m=k$ and $T=k^2$. In the first game each type must occur exactly $k$ times. In the second game one of the $k+1$ types occurs $k$ times and each other type occurs $k-1$ times. Multinomial counting gives

$$
\frac{P(k-1,k+1;k^2)}{P(k,k;k^2)}
=\frac{(k+1)k^k}{k!}\left(\frac{k}{k+1}\right)^{k^2}
\sim \sqrt{\frac{e k}{2\pi}}.
$$

The asymptotic follows from Stirling’s formula and $k^2\log(1+1/k)=k-1/2+o(1)$.

## Fixed goals at late times

For fixed $k,m\ge2$, the $k$-type game fails only if some type appears fewer than $m$ times. For each type and each count $j<m$, there are $\binom Tj(k-1)^{T-j}$ such words. Summing gives at most $kmT^m(k-1)^T$ failed words for $T\ge1$. The $(k+1)$-type game fails whenever a specified type is missing. Consequently

$$
\frac{1-P(m,k;T)}{1-P(m-1,k+1;T)}
\le kmT^m(1-1/k^2)^T\longrightarrow 0.
$$

Thus $P(m,k;T)>P(m-1,k+1;T)$ for all sufficiently large $T$.

## Verification and prior work

The Lean statement counts words in the uniform experiment. The proof identifies the number of words with a given vector of occupancies and proves each limit from that model. [Statement](Statement.lean) · [Disproof and axiom checks](Solution.lean) · [Exact ratio and its limit](Asymptotic.lean) · [Late-time comparison](Tails.lean)

Searches for the conjecture, stochastic comparisons between the two collection goals, and publications citing Campbell found no earlier disproof. The classical multiple-collection limit theorems concern the distribution of the completion time. OpenAI Codex developed the counterexample, both extensions, and the Lean formalization. [OpenAlex citation record](https://openalex.org/W1981223868)

~~~sh
# Run at the merge commit for PR #82.
python3 scripts/verify.py --base HEAD^ --fetch-cache
~~~
