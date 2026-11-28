# Proof of Billey, Fahrbach and Talmage’s Conjecture 6.5 on real-rooted peak polynomials

An interior position $i$ of a permutation is a peak if
$\pi_{i-1}<\pi_i>\pi_{i+1}$. A peak set $S$ contains no consecutive
positions and all its positions are at least two. For $n>\max S$, the
number of permutations of $[n]$ with peak set exactly $S$ is
$2^{n-|S|-1}p_S(n)$. This formula defines the peak polynomial.
[Billey, Burdzy and Sagan, *Permutations with Given Peak Set*](https://cs.uwaterloo.ca/journals/JIS/VOL16/Billey/billey2.html)

For nonempty $S$, all complex roots of $p_S$ are real precisely when $S$ is
one of the following.

- $`\{2\}`$, $`\{2,4\}`$, $`\{3\}`$, or $`\{3,5\}`$.
- A nonempty admissible set $A$ together with $c+3$, where $c=\max A$.
- A nonempty admissible set $A$ together with both $c+3$ and $c+5$.

Every root in these cases is an integer. For the empty set, $p_\varnothing=1$,
which has no roots. The all-admissible corollary includes this extra case
explicitly. Billey, Fahrbach and Talmage proved the positive cases by
factorization in §3.2. Conjecture 6.5 asks whether these cases exhaust the
real-rooted peak polynomials. The argument below proves this converse.
[Original conjecture and factorizations](https://arxiv.org/html/1410.8506v2#S6) ·
[Journal article](https://doi.org/10.1080/10586458.2015.1051193)

## Proof

Let $A$ be the part of the peak set up to a peak $c$. For
$\mathop{\mathrm{Re}}s>0$ put
$D_s(y)=u^s-v^s$, where $u=(1+y)/2$ and $v=(1-y)/2$. There is a
nonnegative increasing density $f$ such that

```math
p_A(c+s)=\prod_{j=1}^c(s+j)\int_0^1 f(y)D_s(y)\,dy.
```

To construct $f$, express $p_A$ in its rising binomial basis. Use the
shifted coefficients as the Bernstein coefficients of a polynomial $W$,
with endpoint coefficients zero and common factor $1/c!$. Li's symmetry and
discrete concavity imply $W(t)=W(1-t)$ and $W''(t)\le0$ on $[0,1]$.
The beta integral gives
$`p_A(c+s)=s\prod_{j=1}^c(s+j)\int_0^1 W(t)t^{s-1}\,dt`$.
Integration by parts gives the displayed formula with
$f(y)=W'((1-y)/2)/2$. The normalized value for an empty prefix is
$D_s(1)=1$. The shared Lean modules adapt Alex Chengyu Li's MIT-licensed
proof of coefficient concavity and its connection to permutation counts.
[Li's paper](https://doi.org/10.2139/ssrn.7435858) ·
[Li's archived Lean source](https://doi.org/10.5281/zenodo.22661864)

Suppose a gap $g$ ends at position $c+a+g$. To append this gap, replace the
current integrand $F(s)$ by

```math
-2\,\mathbf{1}_{g\text{ even}}F(s)+
\sum_{j=a+1}^{a+g-1}(-1)^{a+g-1-j}\binom{s}{j}F(j).
```

This is the peak recurrence after division by the prefix product. It
gives three exhaustive cases.

1. **A gap $h\ge4$ followed by at most three gaps of two.** Let $r$ be the
   number of final twos. At each integer $1\le k<h$, the new polynomial has
   value $-(-2)^r p_A(c+k)$. Its sign stays constant throughout
   $h-3\le s\le h-1$. For $4\le h\le9$, the two unit intervals for $s$ and
   the variable $y^2$ give 48 polynomial bounds. Their rational
   certificates check rectangular partial sums of the coefficients. Each
   polynomial is a convex combination of these sums on its square. For $h\ge10$,
   the binomial series bounds the single-gap error relative to $D_s$ by
   $|\binom{s-2}{h-2}|$. The gap recurrence bounds the relative error after
   division by $(-2)^r$ by this quantity times
   $1+\sum_{j<r}\prod_{k=0}^{2j}(h-s+k)/(2\cdot4^j)$, which is strictly
   less than one. Now remove the prescribed factors at $c+h$ and at $c$
   when the prefix is nonempty. A polynomial with only real roots satisfies
   the midpoint log-concavity inequality on an interval free of roots.
   At $s=h-2$ this forces the ratio
   $p_A(c+s)^2/[p_A(c+s-1)p_A(c+s+1)]$ to be at least
   $4s^2/[3(s^2-1)]$. The moments of $W$ are log-convex, giving a strictly
   smaller ratio for $s\ge3$. For $s=2$, monotonicity of $f$ gives
   $\int y^3 f\ge\tfrac12\int yf$, and the ratio is at most $12/7<16/9$.
   For an empty prefix the forced lower bound is $4/3$ and the ratio is one.

2. **Four final gaps of two after a nonempty prefix.** Put $z=1+5i/2$ and
   let $K$ denote the kernel after four updates. Then $K(1,y)=8y$. On the
   lower half of the unit interval, the odd terms of the degree-eleven
   binomial expansion give $|K(z,y)|\le24y$. On the upper half,
   $|v^z|=v$ and the degree-five expansion of $(1-v)^z$ gives
   $|K(z,y)|\le14y$. Two rational Bernstein identities bound the norms of
   the approximating polynomials, and geometric estimates bound both
   series remainders. At most one quarter of $\int yf$ lies below $1/2$.
   Thus the integral changes in modulus by a factor at most $33/16$, and
   the prefix product changes by a factor at most five. The five prescribed
   linear factors at $c,c+2,c+4,c+6,c+8$ change by a combined factor greater
   than eleven. Since $5(33/16)<11$, the remaining factor decreases in
   modulus from $c+1$ to $c+z$. Every real linear factor is nondecreasing in
   modulus along this vertical segment. This excludes real-rootedness.

3. **A gap of three, or only twos from the start.** For a gap of three,
   $D_1=D_2=y$ removes all dependence on the earlier peaks except a
   positive scalar and known integer linear factors. The residual
   polynomials are translates of the four polynomials for
   $`\{2,4,\ldots,2+2r\}`$, $0\le r\le3$. The first two split into integer
   linear factors. The last two contain $x^2+2x+5$ and
   $17x^3-17x^2+87x+105$, respectively. The first decreases in modulus
   from $-1$ to $-1+i$, and the second from $1$ to $1+2i$. These exact
   comparisons exclude real-rootedness and finish the classification.

## Audit and reproduction

The prior-art search covered the source versions, citing work, and public
proof repositories. It located Li's coefficient theorem and a separate
proof of Conjecture 6.6 about the last real root. It found no previous proof
of the converse in Conjecture 6.5. An independent Codex review checked the
source hypotheses, the empty-prefix convention, both root obstructions
and the endpoint cases. A separate integer-grid interpolation recovered
all 48 positive Bernstein bounds. Independent permutation counts, interpolation
and exact Sturm chains checked all 10,945 nonempty admissible peak sets
with largest peak at most 20. Exactly 3,573 had only real roots, all integers.
The other 7,372 had a nonreal root. The Lean proofs certify the finite
inequalities and the continuous complex estimates. Codex agents developed,
reviewed and formalized the argument.
[Authors' conference paper](https://dmtcs.episciences.org/en/articles/2478) ·
[Separate last-real-root result](https://github.com/Aurantium-47/peak-polynomial-last-real-root)

The formal statement and the all-admissible corollary use the same polynomial as the permutation count. [Lean statement](Statement.lean) · [Lean proof](Solution.lean) · [Shared definitions and license](../PermutationPeaks/README.md) · [Axiom contract](axioms)

From a clean checkout of the draft, the scoped verifier builds the affected modules, replays them in the Lean kernel, and checks the transitive axioms.

```sh
python3 scripts/verify.py --base origin/main --fetch-cache
```
