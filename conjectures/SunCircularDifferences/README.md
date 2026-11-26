# Disproof of Sun’s Conjecture 3.3(ii) on distinct cyclic differences in finite abelian groups of odd order

In any finite abelian group of odd order $N\ge5$, take any $N-2$ elements. No circular ordering of those elements has distinct directed differences between neighbors. The smallest example is $\{0,1,2\}$ modulo $5$.

In Conjecture 3.3, Sun asked whether every subset of $n>2$ elements of a finite abelian group of odd order has a circular ordering with distinct adjacent sums. He also conjectured that a circular ordering with distinct adjacent differences exists whenever $n\nmid N$. The obstruction concerns the second assertion. [Zhi-Wei Sun, *Some new problems in additive combinatorics*, Conjecture 3.3, p. 9 (2019)](https://arxiv.org/pdf/1309.1679#page=9)

## Proof

The directed differences of a circle always sum to zero:

$$
(a_1-a_2)+(a_2-a_3)+\cdots+(a_n-a_1)=0.
$$

They are all nonzero. If $n=N-2$ and they were distinct, they would cover all nonzero elements except one element $d$. In a group of odd order, the nonzero elements come in pairs $x,-x$, so their total is zero. The sum of the differences would therefore be $-d\ne0$, a contradiction. Since $N-2>2$ and $N=(N-2)+2$, the divisibility hypothesis holds.

Sun cites a sequence about circular orders of $N-1$ elements. Searches by conjecture number, cyclic differences, and the missing-two obstruction found no earlier disproof of Conjecture 3.3(ii). The zero-sum condition for a cycle is classical. [Sun’s OEIS sequence A228762](https://oeis.org/A228762) · [Lev, *Sums and differences along Hamiltonian cycles* (2010)](https://www.sciencedirect.com/science/article/pii/S0012365X09001733)

## Verification

From the repository root run

```sh
lake exe cache get
python3 scripts/verify.py
```

The formal proof establishes the obstruction for every odd-order abelian group and applies it modulo $5$. OpenAI Codex found the counterexample and wrote the argument and Lean proof.

Zhi-Wei Sun, “Some new problems in additive combinatorics,” Nanjing University Journal of Mathematical Biquarterly 36 (2019), 134–155. The author’s version arXiv:1309.1679v9 gives Conjecture 3.3(ii), p. 9. [Publication](https://arxiv.org/pdf/1309.1679v9#page=9)
