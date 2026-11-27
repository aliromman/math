# Proof of Billey, Fahrbach and Talmage’s Conjecture 6.4 on the complex zeros of peak polynomials

Let $S$ be a nonempty set of peak positions in a permutation and let
$m=\max S$. Every complex zero $z$ of its peak polynomial satisfies
$|z|\le m$ and $\mathop{\mathrm{Re}}z\ge-3$. The first bound is attained at
$m$. The second is attained at $-3$ by $`S=\{2,4\}`$.
[Billey, Fahrbach and Talmage, Conjectures 1.6 and 6.4, *Experimental Mathematics* 25 (2016), 165–175](https://doi.org/10.1080/10586458.2015.1051193)
· [Text of the conjecture](https://arxiv.org/html/1410.8506v2#S6)

## Proof

Write $P=p_S$ and $h_j=\nabla^j P(m)$ for the backward differences.
Alex Chengyu Li proved the concavity of the sequence between its zero
endpoints $h_0=h_m=0$. At $n=m-2$, the Newton coefficient of order $j$
is $b_j=h_j-2h_{j+1}+h_{j+2}$. Thus $b_j\le0$ for $j\le n$, and the
last coefficient $b_{n+1}$ is positive. In the expansion about $n$, the
basis term of order $j$ is $R_j(z)=\binom{z-n+j-1}{j}$, with
$R_j(m)=j+1$. At $m$ the terms cancel because $P(m)=0$. If $|z|>m$,
then $|z-n+j|>j+2$ for $0\le j\le n$. Hence $|R_j(z)|/(j+1)$ increases
strictly with $j$. The leading term now exceeds the sum of the magnitudes
of all the other terms. [Li's coefficient theorem](https://doi.org/10.2139/ssrn.7435858)
· [Disk proof](Disk.lean)

For the real-part bound, set $D_j=\binom{j+2}{2}$ and
$W_j=\binom{j+3}{3}$. If $\mathop{\mathrm{Re}}z<-3$, both
$|\binom zj|/D_j$ and $|\binom{z-1}{j}|/W_j$ increase strictly with $j$.
For a prefix $A$ ending at $a$, write $M$ for its leading Newton
coefficient and $f(j)=p_A(j)$. Then $f(a)=0$, $f$ is nondecreasing
on the integers above $a$, and $f(a+1)\ge(a-1)M$. The last inequality
follows by summing the rising coefficients at $a+1$. Each coefficient is
at least $M$. [Peak values](../PermutationPeaks/Values.lean) · [Binomial norm estimates](ComplexBasis.lean)

The induction bounds $p_A$ in two bases. In the ordinary basis its norm
is at most $`(W_{a-1}+1)M\,|\binom z{a-1}|/D_{a-1}`$. In the shifted
basis, subtract its leading term $M\binom{z-1}{a-1}$. The norm of the
remainder is at most $`2W_{a-1}M\,|\binom{z-1}{a-2}|/W_{a-2}`$. For
$a=2$ the factor $2W_{a-1}M$ can be replaced by $M$.
The singleton formula $`p_{\{a\}}(z)=\binom{z-1}{a-1}-1`$ starts the induction.

Append the last peak at $m$ and set $r=m-1$. The new leading coefficient
is $f(r)$. If $m-a=2$, the recurrence gives
$p_S(z)=f(a+1)\binom z{a+1}-2p_A(z)$. The ordinary bound and
$2(W_{a-1}+1)M\le D_{a+1}f(a+1)$ make the leading term strictly
larger than the remainder. For longer gaps use the shifted basis. Its
suffix has weight $\sum_{j=a}^{r-1}W_j(f(j+1)-f(j))$. For an odd
gap the earlier prefix cancels. For an even gap of at least four the
weight left after subtracting the suffix from $W_r f(r)$ is
$\sum_{i=a+1}^{r}D_i f(i)$. Its first three terms suffice to cover the
earlier prefix. Strict growth of the normalized basis terms again
excludes a zero. The weight inequalities and the two induction bounds
are proved for every admissible extension.
[Weight inequalities](Estimates.lean) · [Gap induction](Gap.lean)
· [Half-plane proof](HalfPlane.lean)

## Attribution and checks

The proof uses the peak recurrence of Billey, Burdzy and Sagan and the
coefficient theorem of Alex Chengyu Li. The common library adapts Li's
published Lean sources with attribution. Jiradilok and McConville discuss
this conjecture separately from their theorem on descent polynomials in
§5.4. The literature review found no previous proof of both complex-root
bounds. The research, proof development and Lean port used OpenAI Codex.
[Shared definitions and license](../PermutationPeaks/README.md)
· [Jiradilok and McConville, §5.4](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i4p41/pdf/)

An independent review checked the recurrence, index conventions, both
regions and the endpoint cases. Exact recurrence calculations covered
10,945 admissible nonempty peak sets with last peak at most 20. Direct
permutation counts checked the normalization through size nine.
The formal theorem quantifies over every finite admissible peak set.
[Statement](Statement.lean) · [Solution](Solution.lean) · [Axiom contract](axioms)

From a clean checkout of the draft, run the scoped verifier below. It
builds the affected modules, replays their declarations in the Lean kernel,
and checks the transitive axioms.

```sh
python3 scripts/verify.py --base origin/main --fetch-cache
```
