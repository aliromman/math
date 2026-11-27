# Four-factor counterexamples to Gatzweiler and Krattenthaler’s Conjecture 4

The polynomial

$$
P(q)=\frac{(1-q^{25})(1-q^{36})(1-q^{40})(1-q^{42})}
           {(1-q^{3})(1-q^{14})(1-q^{18})(1-q^{20})}
$$

has coefficient $-1$ at $q^{25}$. Each numerator exponent is a
denominator exponent plus $22$. This gives a four-factor family of
counterexamples to the previously disproved Conjecture 4 of
Mona Gatzweiler and Christian Krattenthaler. They proposed that, for
positive integers $m\ge n$ and nonnegative integers $a_1,\ldots,a_n$,
every polynomial of the following form has nonnegative coefficients.

$$
\prod_{i=1}^n\frac{(1-q^{m+i})^{a_i}}{(1-q^i)^{a_i}}.
$$

Here $m=22$, $n=20$, and the four indicated indices have exponent one.
[Original paper, equation (2) and Conjecture 4](https://doi.org/10.1007/s11139-025-01285-2).

## Proof

For the displayed example, cancel $1-q^{18}$ and $1-q^{20}$ against
$1-q^{36}$ and $1-q^{40}$. The remaining denominator
$(1-q^3)(1-q^{14})$ divides $(1-q^{25})(1-q^{42})$. Both factors
divide $1-q^{42}$, their greatest common divisor is $1-q$ up to sign,
and $1-q$ divides $1-q^{25}$. No nonnegative combination of
$3,14,18,20$ equals $25$. Thus the reciprocal of the denominator has
zero coefficient at degree $25$. The numerator contributes $-q^{25}$.

There are infinitely many such examples. Choose any $s\ge2$ with
$3\nmid s$. Use $m=11s$, $n=10s$, and indices $3,7s,9s,10s$. Their
greatest common divisor is one. Put $G_t=\sum_{i=0}^{t-1}q^{3i}$.
The polynomial quotient has the explicit form

$$
(1+q^{9s})(1+q^{10s})\left[(1+q^{7s})G_{6s+1}-q^{11s+3}G_{s-1}\right].
$$

Multiplication by the denominator verifies this identity using
$(1-q^3)G_t=1-q^{3t}$. At degree $11s+3$, the first term in brackets
can contribute only from shifts $0,7s,9s,10s$ after multiplication
by the two outer factors. Their differences from $11s+3$ are
$11s+3,4s+3,2s+3,s+3$. None is divisible by three. The second term
contributes exactly $-1$.

## Prior work and verification

The original paper records Stanton's negative example with $m=1<n=17$.
Gatzweiler, Levicán-Santibáñez and Yoshida later proved positivity
when $2n\lfloor n/2\rfloor-2<m$. Their bound permits the counterexamples
above. The exponent sequences here are asymmetric. The authors' symmetric
conjecture and their conjecture for quotients of two Gaussian binomial
coefficients remain separate questions.
[Subsequent paper, Conjecture 1.3 and Corollary 3.11](https://arxiv.org/html/2603.22226v1).

CoPEER published an earlier counterexample with $m=22$, $n=21$, and
coefficient $-1$ at degree $43$. A subsequent construction used five
factors. Both precede this four-factor family. We withdraw the original
priority claim and exclude this conjecture from the research tally.
[Earlier counterexample](https://github.com/qqliu/CoPEER/blob/105523fdaf018b62eaf2883347724dfe79935611/mathematics/discoveries/entries/number-theory/fake-gaussian-positivity-counterexample.md) · [Five-factor construction](https://github.com/1337isnot1337/solved-conjectures/issues/78).

AI agents found the four exponents, derived the infinite family, and
wrote the mathematical and Lean proofs. From the repository root, run

```sh
lake exe cache get
python3 scripts/verify.py
```

`Statement.lean` gives the original conjecture over real polynomials.
`Solution.lean` proves `counterexample_family` and `not_conjecture` and
checks the axioms of the final theorem.

Mona Gatzweiler and Christian Krattenthaler, A positivity conjecture for a quotient of q-binomial coefficients, Conjecture 4 on expression (2); restated as Conjecture 1.3 by Gatzweiler, Levicán-Santibáñez and Yoshida. [Publication](https://link.springer.com/article/10.1007/s11139-025-01285-2)
