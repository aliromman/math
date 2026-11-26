# Disproof of Sun’s Conjecture 3.10(ii) on simultaneous distinct differences and products in a circular order

Place $2,3,4,6$ around a circle. Every order repeats a directed difference or a product of neighboring numbers. More generally, a set of four positive numbers fails exactly when its middle numbers are the harmonic and arithmetic means of its smallest and largest numbers.

Sun conjectured that any set of more than three distinct nonzero real numbers admits an order in which the adjacent differences are pairwise distinct and the adjacent products are also pairwise distinct. The sole stated exception is a set of the form $\{s,-s,t,-t\}$. Four positive integers fall outside that exception. The first part of the conjecture asks for distinct sums and products, with three stated exceptions. The journal published the paper in 2019. The author’s version 9 lists the question as Conjecture 3.10(ii) on pp. 12–13. Versions 6 and 8 list it as 3.12(ii). [Zhi-Wei Sun, *Some new problems in additive combinatorics*](https://arxiv.org/pdf/1309.1679v9#page=12)

## Proof

The two pairs $\{2,6\}$ and $\{3,4\}$ have equal products:

$$
2\cdot 6=3\cdot 4=12.
$$

If one pair occupies opposite points of the circle, so does the other. Distinct adjacent products therefore require both pairs to occupy opposite points. Up to rotation and reversal, this leaves the order $(2,3,6,4)$. Its last two directed differences coincide:

$$
6-4=4-2=2.
$$

Reversing the circle changes the signs of both equal differences. Thus every order fails the second part of the conjecture.

## Classification for four positive numbers

Fix $0<a<b<c<d$. Every order fails exactly when

$$
b=\frac{2ad}{a+d},\qquad c=\frac{a+d}{2}.
$$

Equivalently, $ad=bc$ and $a+d=2c$. Under these conditions the equal products force $a,d$ to be opposite and $b,c$ to be opposite. The midpoint $c$ must then lie between $a$ and $d$ along the circle, which repeats a directed difference.

For the converse, suppose every order fails. In $(a,c,b,d)$ the only possible repeated difference requires $a+d=b+c$, and the only possible repeated product requires $ad=bc$. In $(a,b,d,c)$ the products are always distinct. Its differences can repeat only when $a+d=2b$ or $a+d=2c$. Thus $a+d=b+c$ is impossible, since $2b<b+c<2c$, and $ad=bc$ follows. Now $b<\sqrt{bc}=\sqrt{ad}\le (a+d)/2$, so $a+d=2c$.

Sun also discussed the real-number problem in a 2013 lecture. Searches by conjecture number, adjacent differences and products, and the four witness values found no earlier disproof of this assertion. [Sun’s Zhejiang University lecture, slide 35](https://www.mathnet.ru/PresentFiles/21090/sun.pdf#page=35)

## Verification

From the repository root run

```sh
# Run at the merge commit for PR #19.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The Lean statement includes both parts and all three exceptional forms. The proof checks the classification, the example, and its exclusion from the exceptional forms. OpenAI Codex found the counterexample and classification and wrote the mathematical and Lean proofs.
