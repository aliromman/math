# Proof of Brown and Cameron’s Conjecture 4.2 on the maximum modulus of independence roots of graphs

For any graph on $n\ge3$ vertices, every root $z$ of its independence polynomial satisfies

$$
|z|\le
\begin{cases}
2\cdot3^{(n-3)/3}+n/3, & n\equiv0\pmod 3,\\
3^{(n-1)/3}+(n-1)/3, & n\equiv1\pmod 3,\\
4\cdot3^{(n-5)/3}+(n+1)/3, & n\equiv2\pmod 3.
\end{cases}
$$

This proves Brown and Cameron's Conjecture 4.2 in the preprint of *Maximum Modulus of Independence Roots of Graphs and Trees*. Its three formulas come from one quantity. Among partitions of $n-1$ into positive integers, maximize the product of the parts plus the number of parts. Brown and Cameron proved the earlier bound $3^{n/3}+n-1$ and constructed graphs whose top two coefficients have ratio equal to the proposed bound. [Preprint, Sections 2 and 4](https://arxiv.org/pdf/1812.09775) · [Journal article](https://doi.org/10.1007/s00373-020-02160-1)

## Proof

Let $a_j$ count the independent sets of size $j$, and let $m_j$ count those that are maximal under inclusion. Every other independent $j$-set extends to one of size $j+1$, so $a_j\le(j+1)a_{j+1}+m_j$. Fix a largest independent set $S$ of size $\alpha$ and put $O=V\setminus S$. A maximal independent set is determined by its intersection with $O$, since it contains every vertex of $S$ that has no neighbor in that intersection. For $j<\alpha$, the empty intersection gives $S$. Thus $m_j+1$ is at most the number of independent subsets of $O$.

We use the following consequence of Zykov's clique theorem on the complement graph. On $m$ vertices, if all independent sets have size at most $r$, then their number is at most $p_1\cdots p_r$ for some positive integers with sum $m+r$. A direct proof chooses a vertex $v$ in the largest number of independent sets and lets $W$ consist of $v$ and its neighbors. Removing or adding $v$ gives a bijection between the sets containing $v$ and those disjoint from $W$. At most $|W|$ times that many sets meet $W$. Repeat on the remaining vertices, where every independent set can be enlarged by $v$ in the original graph. This gives a factor $|W|+1$ at each step. Pad with ones if no vertices remain. [Zykov's theorem and its counting form](https://arxiv.org/abs/math/0602191)

Write $F(N)$ for the maximum of product plus number of parts over partitions of $N$. Take $0\le j<\alpha$.

- If $a_{j+1}\ge2$, apply the counting bound on $O$ with $r=\alpha$. Its parts sum to $n$. Reduce any part of size at least two by one. The new partition of $n-1$ retains at least half the product. It follows that $a_j/a_{j+1}\le\alpha+m_j/2\le F(n-1)$. If every part is one, then $m_j=0$ and the all-ones partition gives $F(n-1)\ge n$.
- If $a_{j+1}=1$, then $j+1=\alpha$ and $S$ is the unique independent set of this size. Otherwise the subsets of $S$ alone would supply two choices. Every independent subset of $O$ now has size at most $\alpha-1$. The counting bound gives $\alpha-1$ parts summing to $n-1$. Hence $a_j\le\alpha+m_j\le(\alpha-1)+p_1\cdots p_{\alpha-1}\le F(n-1)$.

The Eneström–Kakeya theorem bounds the root moduli by the largest consecutive coefficient ratio. To evaluate $F(n-1)$, merge each part of size one into another part, split parts of size at least four into two and the remainder, and replace three twos by two threes. None of these operations decreases product plus number of parts. The final partition has only threes and at most two twos. The three possibilities give the displayed bound, including $n=3,4,5$.

## Source and verification

Cameron's dissertation also gives the problem as Conjecture 6.3.1. Searches for the conjecture and subsequent work on maximum-modulus independence roots found no earlier proof. OpenAI Codex derived the coefficient bound and formalized the graph counts, the integer partition optimization and the polynomial root estimate in Lean. [Dissertation, Chapter 6](https://dalspaceb.library.dal.ca/server/api/core/bitstreams/c903bf10-142c-4ffe-965a-1927ad52197a/content)

```sh
# Run at the merge commit for PR #29.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Jason I. Brown and Ben Cameron, “Maximum Modulus of Independence Roots of Graphs and Trees,” arXiv:1812.09775v1, §4, p. 21, journal DOI 10.1007/s00373-020-02160-1. Preprint Conjecture 4.2 is also Conjecture 6.3.1 in Ben Cameron’s dissertation, On the Roots of Independence Polynomials. [Publication](https://arxiv.org/pdf/1812.09775v1#page=21)
