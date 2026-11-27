# Proof of Conlon, Fox and Pham’s Conjecture 10 on the logarithmic density of monochromatic subset sums

Color the positive integers with three colors. For at least one color, the sums of distinct integers of that color have upper logarithmic density at least **0.8526248994…**. There is a coloring for which this bound is attained.

More generally, for every $r\ge3$, let $b>1$ be the unique root of $b^r-2rb+r-1=0$. The sharp guaranteed density for $r$ colors is

$$
c_r=\frac{1-1/(2b)}{1-b^{-r}}
   =\left(1-\frac{1}{2b}\right)\left(1+\frac{1}{2rb-r}\right).
$$

Conlon, Fox and Pham found the extremal coloring and proved the two-color case, answering a question of Erdős. Their Conjecture 10 asks whether their upper bound is sharp for every larger number of colors. The proof below establishes the matching lower bound for arbitrary colorings. [Conlon, Fox and Pham, *The upper logarithmic density of monochromatic subset sums*, Mathematika 68 (2022), 1292–1301, pp. 2 and 9 of the preprint](https://arxiv.org/pdf/2105.15195#page=9) · [Erdős Problem 1211, the earlier two-color question](https://www.erdosproblems.com/1211)

## The statement

For a set $A$ of positive integers, write $\Sigma(A)$ for its finite subset sums. Its upper logarithmic density is

$$
\overline d_{\log}(\Sigma(A))=
\limsup_{x\to\infty}\frac{1}{\log x}
\sum_{\substack{1\le n\le x\\n\in\Sigma(A)}}\frac1n.
$$

Among all partitions into $r$ nonempty parts, take the minimum of the largest of these $r$ densities. The theorem computes that minimum and gives a partition attaining it.

## Why every coloring reaches the bound

A **full shell** for a color is an exponent $k$ for which its subset sums contain every integer in $[2^k,2^{k+1})$. Each such shell contributes at least $\log 2$ to the reciprocal sum. Suppose, for a contradiction, that all the densities are less than some $C<c_r$, with room to spare. At every sufficiently large cutoff $n$, each color then has at most $Cn-1$ full shells below $n$.

**Long runs of full shells.** For each sufficiently large $N=2^j$, one color in $[N,2N)$ represents every integer between $D N(j+1)$ and $N^2/D$, for a constant $D$ depending only on $r$. The authors' Lemma 2 already supplies the shell run used below. At $N=2^{Kt}$ it gives an interval $[C_1N,C_2N^2]$ from inputs in $[N,eN)$. The Lean proof includes an elementary derivation using $[N,2N)$. Set $Q=(r+1)!$. Take groups of $r+1$ consecutive terms of $1\pmod Q$, with starting points spaced by $Q^2$. In each group two terms share a color. A positive proportion of the groups share both positions and the color. Their pairs have a common difference $d=Qh$ with $1\le h\le r$. Thus $d$ divides $Q^2$ and the lower endpoints have the same invertible residue modulo $d$. Choosing one member of each of several pairs gives a progression of subset sums with step $d$. At each dyadic scale, pigeonholing the unused endpoints gives a pair separated by a fixed proportion of the current span and by at most its length. A bounded number of such choices doubles the span. After $O_r(\log N)$ pairs, the progression covers at least $4N$ steps. Up to $d-1$ spare terms fill the residue classes. Each unused term is smaller than the interval now available, so adjoining the remaining terms extends its upper end to order $N^2$. [Original interval theorem, Lemma 2](https://www.its.caltech.edu/~dconlon/Erdoslogarithmicdensity.pdf)

Fix a large integer $K$ and put $p=K+1$, $q=2K-1$. Apply the interval bound at $j=Kt$. For every sufficiently large integer $t$, some color contains all shells in $[pt,q(t+1))$. The ratio $p/q$ can be arbitrarily close to $1/2$.

**Count intervals only after a gap.** Define $A_i(t)$ as one plus the number of full shells $j<qt$ of color $i$ followed by a missing shell $h$ with $j<h<q(t+1)$. These counts are positive and nondecreasing. The assumed density bound gives $A_i(t)\le Cqt$. Consider the product

$$
P(t)=\frac{\prod_i A_i(t)}{(qt)^r}.
$$

Choose a color $i$ covering $[pt,q(t+1))$. Let $h$ be its first missing shell at or after $pt$ and put $u=\lfloor h/q\rfloor$. Such a hole exists by the density bound, and $u>t$. Every shell in $[pt,qu)$ now counts toward $A_i(u)$, witnessed by $h$. None counted toward $A_i(t)$, since there was no intervening hole. Thus $A_i(u)-A_i(t)\ge qu-pt$.

**A product that would grow forever.** Set $z=t/u$ and $a=A_i(u)/(qu)\le C$. If $P(u)\le gP(t)$ for some $g>1$, monotonicity of the other factors gives $A_i(t)\ge A_i(u)z^r/g$. The last two inequalities imply

$$
\frac pq z\ \ge\ 1-a+a z^r/g\ \ge\ 1-C+C z^r/g.
$$

At the proposed optimum, Bernoulli's inequality $(bz)^r\ge 1+r(bz-1)$ gives $1-c_r+c_r z^r\ge z/2$. Replacing $c_r$ by $C<c_r$ makes the inequality strict on $[0,1)$, and at $z=1$ there is already a gap of $1/2$. By compactness the gap is uniform. Choose $K$ large and $g>1$ close enough to one that $1-C+Cz^r/g>(p/q)z$ throughout $[0,1]$. Hence every sufficiently large $t$ has a later $u$ with $P(u)>gP(t)$. Iteration contradicts $0<P(t)\le1$. This proves the lower bound.

## Why the bound is attained

Use the cyclic coloring of Conlon, Fox and Pham. Color $n$ by $k\bmod r$ when $b^k\le\log n<b^{k+1}$, assigning the finitely many initial integers to the first color. If the largest term of a subset sum is $n$, then the sum lies between $n$ and $n^2$. For a fixed color, the possible logarithms therefore lie in intervals $[a,2ba]$ with successive left endpoints in ratio $b^r$. These intervals are disjoint because $b^r-2b=(r-1)(2b-1)>0$. The covered fraction rises inside each interval and falls in the next gap. A geometric sum at the right endpoints shows that the largest limiting fraction is $(1-1/(2b))/(1-b^{-r})$. Passing from lengths to reciprocal sums costs a bounded amount per interval and only $O(\log\log x)$ up to $x$. Every color occurs. [Original construction, pp. 2–3](https://arxiv.org/pdf/2105.15195#page=9)

## Verification and attribution

From the repository root, run

```sh
# Run at the merge commit for PR #59.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The proof includes the finite subset-sum argument, the logarithmic-density estimates, the product argument, the extremal coloring, and the transitive axiom check. The project pins Lean 4.36.0 and Mathlib. OpenAI Codex developed the lower bound and wrote the Lean formalization. Searches by the paper title, multicolor extension, cyclic coloring, and cited references found the authors' two-color result and no earlier proof of Conjecture 10.
