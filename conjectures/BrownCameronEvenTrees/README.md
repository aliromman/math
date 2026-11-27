# Proof of Brown and Cameron’s Conjecture 4.4 on the maximum modulus of independence roots of even-order trees

Let $T$ be a tree on $2k$ vertices, with $k\ge3$. Every complex root $z$ of its independence polynomial satisfies

$$
|z|\le 2^{k-2}+k+1.
$$

This proves Brown and Cameron's Conjecture 4.4 in the preprint of *Maximum Modulus of Independence Roots of Graphs and Trees*. Their Corollary 3.4 gave $2^{k-1}+k$. The leading exponential term drops by a factor of two. The authors also gave trees for which the ratio of the top two coefficients attains the conjectured bound. [Preprint, Sections 3–4](https://arxiv.org/pdf/1812.09775) · [Journal article](https://doi.org/10.1007/s00373-020-02160-1)

## Proof

Write $a_j$ for the number of independent sets of size $j$, and let $m_j$ count those that are maximal under inclusion. Every other independent $j$-set occurs among the $j+1$ deletions from some independent $(j+1)$-set. Hence

$$
a_j\le (j+1)a_{j+1}+m_j.
$$

Fix a largest independent set $S$, let $\alpha=|S|$, and put $O=V(T)\setminus S$. A maximal independent set $U$ is determined by $B=U\cap O$. It must include every vertex of $S$ without a neighbor in $B$. For $j<\alpha$, the empty choice of $B$ gives $S$, so $m_j\le 2^{2k-\alpha}-1$.

The two color classes of a tree show that $\alpha\ge k$. We bound the ratios for $0\le j<\alpha$.

- If $\alpha\ge k+2$, then $a_j/a_{j+1}\le\alpha+2^{2k-\alpha}-1\le k+1+2^{k-2}$. The last expression bounds the value at each integer $\alpha$ because $a+2^{2k-a}$ is nonincreasing for $a\le 2k$.
- If $\alpha=k$, both color classes have size $k$. For $1\le j+1<k$, each class contains at least two distinct $(j+1)$-sets. At size $k$, each color class has a leaf because its vertex degrees sum to $2k-1$. In the opposite class, remove the leaf’s neighbor and insert the leaf. Doing this once from each class gives two more $k$-sets. The four sets meet one color class in $0,1,k-1,k$ vertices. Thus $a_{j+1}\ge4$, and $a_j/a_{j+1}\le k+2^{k-2}$.
- If $\alpha=k+1$ and $a_{j+1}\ge2$, then $m_j/a_{j+1}\le 2^{k-2}$. If $a_{j+1}=1$, the subsets of $S$ force $j=k$. It remains to show $m_k\le 2^{k-2}$.

For the last bound, pair each subset of $O$ with its complement in $O$. Suppose both occur as the outside portions of two maximal independent $k$-sets $U,W$. These sets are disjoint. Indeed, any common vertex would lie in $S$ and have a neighbor in $O$. This neighbor belongs to $U$ or $W$, which contradicts independence. Since $|U|+|W|=2k$, the sets form a bipartition. A connected graph has only one bipartition up to interchange, so at most one complementary pair contributes twice. The pair $\{\varnothing,O\}$ contributes zero. A maximal set contained in $S$ equals $S$, and an independent set containing all of $O$ cannot contain a vertex in $S$, so has at most $k-1$ vertices. The $2^{k-2}$ pairs therefore contribute at most $2^{k-2}$ sets in total.

This bounds every ratio $a_j/a_{j+1}$. The Eneström–Kakeya theorem gives the same upper bound for the modulus of each root of $\sum_j a_jz^j$. The Lean proof includes this polynomial estimate.

## Source and verification

Cameron's dissertation repeats the bound as Conjecture 6.3.3. Searches for both formulations, subsequent papers citing Brown and Cameron, and public mathematical proof archives found no earlier proof of the even-tree bound. OpenAI Codex derived the counting argument and wrote the Lean formalization. [Dissertation, Chapter 6](https://dalspaceb.library.dal.ca/server/api/core/bitstreams/c903bf10-142c-4ffe-965a-1927ad52197a/content)

```sh
# Run at the merge commit for PR #25.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Jason I. Brown and Ben Cameron, “Maximum Modulus of Independence Roots of Graphs and Trees,” arXiv:1812.09775v1, §4, p. 21, journal DOI 10.1007/s00373-020-02160-1. Preprint Conjecture 4.4 is also Conjecture 6.3.3 in Ben Cameron’s dissertation, On the Roots of Independence Polynomials. [Publication](https://arxiv.org/pdf/1812.09775v1#page=21)
