# Infinitely many exceptional triangular products

For every nonnegative integer $k$, no two positive triangular numbers have a product that becomes a square upon adding

$$n_k=2\cdot 7^{6k+2}.$$

These integers begin with $98$ and $11{,}529{,}602$. Each is $8$ modulo $9$. This proves Conjecture 12 of Sounak Bagchi and Christian Zhou-Zheng. They had ruled out all $n$ that are $2$ or $5$ modulo $9$ and asked whether infinitely many exceptions occur outside those classes. [Original conjecture, §3.1](https://arxiv.org/html/2608.27697v1#S3.SS1)

## Proof

Write $T_a=a(a+1)/2$. Suppose that $T_aT_b+2\cdot7^{2j}=c^2$. If an odd prime $p$ divides either triangular number, then $c^2\equiv 2(7^j)^2\pmod p$. For $p\ne7$, division by $(7^j)^2$ shows that $2$ is a square modulo $p$. The supplementary law of quadratic reciprocity gives $p\equiv 1$ or $7\pmod 8$. The same conclusion holds for $p=7$. It follows by multiplication that every odd divisor of either triangular number is $1$ or $7$ modulo $8$.

Each triangular number is $r s$, where $s$ is odd and $s=2r+1$ or $2r-1$. Since $s\equiv\pm1\pmod8$, an even $r$ must be divisible by $4$. For odd $r$, both $r$ and $s$ are $1$ or $7$ modulo $8$. The relation $s=2r\pm1$ forces them to agree modulo $8$, so $rs\equiv1\pmod8$. Thus both triangular numbers are $0$, $1$ or $4$ modulo $8$. Their product has the same three possibilities. Adding $2\cdot7^{2j}\equiv2\pmod8$ gives $2$, $3$ or $6$, none of which is a square modulo $8$.

Set $j=3k+1$. Since $7^3\equiv1\pmod9$, the resulting $n_k$ are all $8$ modulo $9$. They form a strictly increasing sequence.

## Related work

Marija Bliznac Trebješanin proved the restriction on prime divisors of an admissible triangular number in Theorem 9. Her Theorem 6 establishes the two excluded residue classes, and Proposition 7 and its discussion give individual exceptions in the other classes. The argument above uses the prime restriction to obtain an infinite family of positive exceptions within one of those classes. [Bliznac Trebješanin, §§3–4](https://arxiv.org/html/2603.29565v3)

Ghosh and Sarnak studied the related integral Markoff surface. For these parameters its level is $4+2\nu^2$ with $\nu=16\cdot7^{3k+1}$. Their Proposition 8.1(ii) requires every prime divisor of $\nu$ to be $1$ or $7$ modulo $8$, and part (iii) requires $\nu$ to be prime. Here $2$ divides $\nu$. A search by author, conjecture number, and the triangular-pair equation found no earlier proof of Conjecture 12. [Ghosh and Sarnak, Proposition 8.1](https://arxiv.org/pdf/1706.06712#page=23)

## Verification

From the repository root, run the following commands.

```sh
# Run at the merge commit for PR #23.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` gives the original conjecture over integers. `Solution.lean` proves the positive family and the conjecture. Its axiom check allows propositional extensionality, classical choice and quotient soundness. OpenAI Codex derived the argument and wrote the Lean proof.
