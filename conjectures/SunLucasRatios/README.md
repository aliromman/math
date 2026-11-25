# A Lucas sequence violates Sun’s ratio bound at index five

Start with $u_0=0$, $u_1=1$ and set $u_{n+2}=3u_{n+1}+26u_n$. Its fifth,
sixth, and seventh terms are $1459$, $9135$, and $65339$. Sun’s conjecture
predicts that the ratio of consecutive roots decreases. It increases here:

$$
\frac{9135^{1/6}}{1459^{1/5}} < \frac{65339^{1/7}}{9135^{1/6}}.
$$

## Conjecture and proof

For the Fibonacci numbers $F_n$, Sun conjectured that $F_n^{1/n}$ strictly
increases from $n=2$, and that $F_{n+1}^{1/(n+1)}/F_n^{1/n}$ strictly
decreases from $n=4$. He also proposed that, for every Lucas sequence
$u_0=0$, $u_1=1$, $u_{n+2}=Au_{n+1}-Bu_n$, the corresponding ratio strictly
decreases from $n=4$ and tends to $1$, provided $A,B$ are integers with
$A>1$, $B\ne0$, $A^2>4B$ and either $A>2$ or $B\ge-9$.
[Sun, Conjecture 3.1, pp. 8–9 of the preprint](https://arxiv.org/pdf/1208.2683#page=8).

The parameters $A=3$, $B=-26$ satisfy every hypothesis. Raising the
cross-multiplied ratio inequality to the power $105$ reduces it to

$$
9135^{35}<1459^{21}\,65339^{15},
$$

which follows by integer arithmetic. Hou, Sun, and Wen proved the decrease
for Fibonacci numbers and an eventual decrease for general Lucas sequences.
Their starting index can depend on $A$ and $B$. Searches for the fixed-index
Lucas claim and its counterexamples found no earlier disproof.
[Hou, Sun, and Wen, Theorem 1.1](https://doi.org/10.5486/PMD.2014.5817).

## Verification

From the repository root, run

```sh
lake exe cache get
lake build
lake env leanchecker conjectures.SunLucasRatios.Solution
```

`Statement.lean` states all three claims. `Solution.lean` proves their
conjunction false and checks the axioms used. OpenAI Codex found the
counterexample and wrote the argument and Lean proof.
