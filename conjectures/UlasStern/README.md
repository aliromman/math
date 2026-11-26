# Proof of Ulas’s Conjecture 4.4 on real zeros of Stern polynomials

For every $n\ge0$, the Stern polynomial with index

$$
h_n=\frac23(2^{2n}-1)(2^{2n+1}+1)+1
$$

is strictly positive at every real argument. At integer arguments these same polynomials have an exact prime-divisor classification. A prime divides some $B_{h_n}(t)$, with $n\ge0$ and $t\in\mathbb Z$, **if and only if it is 1 modulo 3**. Every such prime occurs already in $B_{19}(t)=3t^2+3t+1$.

Stern polynomials satisfy $B_0=0$, $B_1=1$, $B_{2j}=tB_j$, and $B_{2j+1}=B_j+B_{j+1}$. Maciej Ulas conjectured the absence of real roots for this family. Their coefficients count hyperbinary representations by the number of digits equal to one. [Ulas, *Strong arithmetic property of certain Stern polynomials*, Conjecture 4.4](https://arxiv.org/pdf/1909.10844#page=16)

## The norm and the real roots

The first quadratic identity in the proof of Ulas’s Theorem 3.1 already gives $B_{h_n}=(t^2+t+1)X^2+(t+2)XY+Y^2$ for a consecutive pair of Stern values $X,Y$ there. Completing the square gives $4B_{h_n}=(2Y+(t+2)X)^2+3t^2X^2$. At $t\ne0$, both binary digit transformations on consecutive Stern values are invertible, so the pair cannot vanish. At $t=0$ every odd-index polynomial has value one. This proves the conjecture directly from Ulas’s identity.

The formal proof also derives a norm identity over any commutative ring, directly from the two binary blocks in $h_n$. Its binary word is $(10)^n(01)^n1$. Reading a block 10 acts on $(B_j,B_{j+1})$ by $M=\left(\begin{smallmatrix}t&t\\1&1+t\end{smallmatrix}\right)$, and 01 acts by the matrix with both row and column orders reversed. Write $M^n=aM+bI$, starting from $(a,b)=(0,1)$ and updating to $((2t+1)a+b,-t^2a)$. Multiplication of the two blocks gives

$$
B_{h_n}(t)=u^2+uv+v^2,\qquad u=b+(t+1)a,\quad v=ta.
$$

## Which primes occur

Suppose $p$ divides a value at an integer $t$, and reduce the identity modulo $p$. If $v=0$, the norm forces $u=0$. When $t\ne0$ the recurrence on $(a,b)$ is invertible and forbids this. When $t=0$ it preserves $a+b=1$, again forbidding it. Thus $z=u/v$ satisfies $z^2+z+1=0$. For $p\ne3$, this is an element of multiplicative order three, so $3\mid p-1$.

In characteristic three the norm equals $(a+b)^2$. This equals one throughout the recurrence. One can check the three values of $t$ directly. At both $t=0$ and $t=-1$ the sum stays one. At $t=1$ the recurrence sends $(a,b)$ to $(b,-a)$ and starts at $(0,1)$.

Conversely, if $p\equiv1\pmod3$, the multiplicative group of the field has an element $\zeta$ of order three. Set $t=(\zeta-1)^{-1}$. Then $(\zeta-1)^2(3t^2+3t+1)=\zeta^2+\zeta+1=0$. Any integer representative of $t$ proves the assertion at index 19.

## Verification and attribution

From a clean checkout, run

```sh
# Run at the merge commit for PR #70.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The source conjecture is in [Statement.lean](Statement.lean), positivity and the norm are in [Solution.lean](Solution.lean), and the prime classification is in [Arithmetic.lean](Arithmetic.lean). The guarded axiom lists permit only `propext`, `Classical.choice`, and `Quot.sound`.

Ulas posed the conjecture and supplied the first quadratic identity. OpenAI Codex developed the positivity proof, the prime classification, and the formalization. A separate AI researcher checked the original recurrence, both proofs, and their Lean statements. The exported proofs passed both Lean and the independent Nanoda kernel. Searches by author, index family, root condition, and prime divisors found no prior complete result. The prime-index irreducibility theorem treats a different family and question. [Altizio, *Zeros of Stern polynomials in the complex plane*](https://arxiv.org/abs/2511.03847)
