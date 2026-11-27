# Solution to Bellec and Fritz’s attainment question for the Beat the Average game

For three independent rolls $A,B,C$ of any real-valued die,

$$
\Pr(2A<B+C)<\frac23.
$$

Bellec and Fritz proved that the supremum is $2/3$ and that every law with a point mass falls strictly below it. After Theorem 1.5 they asked whether a continuous distribution can attain it. The strict inequality answers their question. In fact, the probabilities attainable by atomless nonnegative dice form exactly $(1/3,2/3)$. [Original paper, pp. 5–6](https://arxiv.org/pdf/2412.15179) · [Journal article](https://doi.org/10.1080/00029890.2026.2702871)

## Why the upper bound is strict

Let $X_1,\ldots,X_m$ be independent rolls with the same law, where $m\ge3$, and let $\bar X$ be their sample mean. At most $m-1$ rolls can fall strictly below $\bar X$. By symmetry, the expected number below $\bar X$ is $m\Pr(X_1<\bar X)$.

A constant die has probability zero. Otherwise choose two support points $a<b$. At the sample $(a,b,\ldots,b)$, the last $m-1$ rolls all lie strictly above the mean. This remains true in an open neighborhood of that sample. The neighborhood has positive probability by independence. The expected number below the mean is therefore strictly less than $m-1$.

For an atomless law, conditioning on the other rolls shows that $X_1=\bar X$ has probability zero. Applying the upper bound to $-X_1,\ldots,-X_m$ now gives $\Pr(X_1<\bar X)>1/m$.

## A die for every intermediate probability

Bellec and Fritz used a geometric series of independent digits to break ties in a strict linear inequality. In Proposition 3.3 they credit Will Sawin with this construction. Their method gives an explicit die here by choosing Bernoulli digits and the base $m+2$. [Proposition 3.3 and its proof](https://arxiv.org/html/2412.15179v4#S3)

Fix $0<q<1$. Use independent digits $D_j$ with $\Pr(D_j=1)=q$ and $\Pr(D_j=0)=1-q$. Set

$$
X=\sum_{j=0}^{\infty}\frac{D_j}{(m+2)^j}.
$$

The digits determine the value uniquely. A prescribed prefix of length $r$ has probability at most $\max(q,1-q)^r$, so this bounded nonnegative die has no atoms.

Compare the digit sequences of the $m$ rolls. At the first position where they disagree, every roll showing zero lies below the mean and every roll showing one lies above it. Indeed, after removing the common prefix and scaling the current digit to one, each remaining tail is at most $1/(m+1)$. An all-equal column occurs with probability $q^m+(1-q)^m$. A mixed column with a zero on the first roll occurs with probability $1-q-(1-q)^m$. Summing over the number of initial all-equal columns gives

$$
\Pr(X_1<\bar X)
=\frac{1-q-(1-q)^m}{1-q^m-(1-q)^m}.
$$

This continuous function tends to $(m-1)/m$ as $q$ tends to zero and to $1/m$ as $q$ tends to one. Every value strictly between the bounds occurs. For three rolls the formula reduces to $(2-q)/3$. For example, taking $q=1/5$ gives exactly $3/5$.

## Prior work and verification

Bellec and Fritz supplied the three-roll supremum, their discrete examples and the strict bound for laws with atoms. Zaytsev and Bellec resolved Bellec and Fritz’s separate four-roll Conjecture 5.1 and studied coefficient thresholds. Searches for the three-roll attainment question, sample-mean rank probabilities, and earlier work citing the original paper found no prior resolution of the atomless case. OpenAI Codex derived the strict endpoint bounds, evaluated the Bernoulli specialization of the earlier construction, and formalized the resulting classification in Lean. [Four-roll result](https://arxiv.org/abs/2611.29223)

From the repository root, run

```sh
# Run at the merge commit for PR #90.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` gives the original attainment question. `resolution` proves its negation. `attainable_spectrum` gives the exact interval for every sample size $m\ge3$, and `three_rolls` proves the three-roll formula.

Bellec and Fritz, “Optimizing over iid distributions and the Beat the Average game,” question after Theorem 1.5 and §5.2, DOI 10.1080/00029890.2026.2702871. The two-thirds supremum for three rolls is unattained by an atomless die. The proof of the attainable range credits Will Sawin’s digit construction. [Publication](https://arxiv.org/html/2412.15179v4#S5.SS2)
