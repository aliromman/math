# Disproof of Weinberger and Shayevitz’s Conjecture 1 on greedy dictatorship for the binary erasure channel

A helper sees a uniformly random binary message with each bit independently erased with probability $3/4$. The helper can send one bit to someone who must guess the entire message.

For every message length $n\ge12$, the majority of the surviving bits in a fixed block of twelve gives a normalized expected guessing rank of at most **0.7816**. Sending the first surviving bit gives a rank of at least **0.7817**, even with the best possible guessing order. The normalization is the expected rank $(2^n+1)/2$ without help.

This disproves Conjecture 1 of Nir Weinberger and Ofer Shayevitz. They conjectured that sending the first surviving bit, with a fair coin if all bits are erased, attains the optimal asymptotic guessing ratio for every erasure probability and every positive moment. They considered majority in their paper. Their example at five bits and erasure probability $0.4$ favored the first surviving bit. [*Guessing with a Bit of Help*, Entropy 22 (2020), 39, equations (5) and (99), Section 6.1](https://doi.org/10.3390/e22010039)

## The cost of a guessing order

Let $z(x)$ be the expected helper bit on input $x$, with the bit represented by $+1$ or $-1$. For a score $w(x)$, let $X,Y$ be independent uniform input words and set

$$
r_w(x)=\mathbb E_Y\mathop{\mathrm{sgn}}(w(x)-w(Y)),\qquad
A(z,w)=\mathbb E_X[z(X)r_w(X)].
$$

After a positive bit, guess higher scores first. After a negative bit, reverse the order. Average ties uniformly. The optimal order uses $w=z$ because it ranks words by their posterior probability. With $N=2^n$, the optimal first-moment ratio is

$$
1-\frac{N}{N+1} A(z,z).
$$

Indeed, if $B$ words score below $x$, $H$ score above it and $T$ tie with it, then $r_w(x)=(B-H)/N$. The mean rank of $x$ in its tie class is $H+(T+1)/2$ in descending order and $B+(T+1)/2$ in ascending order. Also, $A(z,w)\le A(z,z)$ follows by swapping $X,Y$ and pairing the two terms.

For three scores $a,b,c$, the cyclic sum of $\mathop{\mathrm{sgn}}(a-b)\mathop{\mathrm{sgn}}(a-c)$ is one unless all three scores agree, when it is zero. Taking three independent scores gives $\mathbb E[r_w(X)^2]\le1/3$. Cauchy–Schwarz now gives $A(z,w)^2\le\mathbb E[z(X)^2]/3$.

## The two helper bits

For the first surviving bit, the expected sign after prepending a bit of sign $b$ is $b/4+3z(x)/4$. Its mean square therefore satisfies $M_{n+1}=1/16+9M_n/16$ and $M_0=0$. Thus $M_n\le1/7$ and $A(z,z)\le1/\sqrt{21}$. This gives the lower bound above.

For majority, send $+1$ when at least as many ones as zeros survive in the twelve chosen positions. Score guesses by the number of ones in those positions. The other bits can be ignored at every length. To check the exact score, let $p_j=\binom{12}{j}/2^{12}$. Given $j$ input ones, the surviving ones and zeros have independent distributions $U_j\sim\mathop{\mathrm{Bin}}(j,1/4)$ and $V_j\sim\mathop{\mathrm{Bin}}(12-j,1/4)$. Then

$$
A=\sum_{j=0}^{12}p_j
\bigl(2\Pr[U_j\ge V_j]-1\bigr)
\sum_{i=0}^{12}p_i\mathop{\mathrm{sgn}}(j-i)
=\frac{3845275777343}{17592186044416}.
$$

For $n\ge12$, this order gives a ratio at most $1-(4096/4097)A<0.7816$. Using the optimal order can only reduce the ratio. The two bounds persist on taking the limit superior in the conjecture.

## Verification and attribution

The formal proof computes the same fraction by tracking the difference between two input weights and the difference between the observed numbers of ones and zeros. Each step averages over two fresh input bits and one fresh erasure. All arithmetic is exact.

Run these commands from the repository root.

```sh
# Run at the merge commit for PR #98.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

A search of papers citing or discussing the proposed greedy dictator, including work on guessing with side information, found the source analysis and no prior disproof. OpenAI Codex found the finite comparison and wrote the Lean proof.

Weinberger and Shayevitz, “Guessing with a Bit of Help,” Entropy 22 (2020), 39, §6.1, Conjecture 1, DOI 10.3390/e22010039. A counterexample for the first guesswork moment at erasure probability three quarters disproves the universal claim. [Publication](https://www.mdpi.com/1099-4300/22/1/39)
