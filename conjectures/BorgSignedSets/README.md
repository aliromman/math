# Proof of Borg’s Conjecture 1.4 on intersecting systems of signed sets

Let each member of a finite family of nonempty sets carry one of $k\ge2$
labels at each of its elements. Two signed sets intersect if they agree on
the label of a common element. Among all pairwise intersecting families,
one of maximum size consists of all signed sets with a fixed label at a fixed
element. Borg’s conjecture also specifies when a family of maximum size can
have no common signed element. [Borg, *Intersecting Systems of Signed Sets*,
Conjecture 1.4, EJC 14 (2007), R41](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v14i1r41)

For a support family $\mathcal F$, the star at coordinate $i$ has size

$$
D_i=\sum_{B\in\mathcal F:i\in B}k^{|B|-1}.
$$

Write $M=\max_i D_i$. A nonstar family of size $M$ exists exactly when
$k=2$ and three distinct coordinates occur in precisely the same supports
and have stars of size $M$. In that case take all words with label zero at
two or more of the three coordinates. Any two accepted words share a zero,
and the rule accepts four of the eight binary patterns.

## Proof

Let $\mathcal A$ be an intersecting family on the ground set $V$.
A full word assigns labels in $\mathbb Z/k\mathbb Z$ to all of $V$.
All extensions of members of $\mathcal A$ form an intersecting set of
full words. A word and any of its nonzero global label shifts disagree
everywhere. Thus this set meets each orbit of global shifts at most once.
Extend it to a set $U$ that takes exactly one word in every orbit.
On the uniform probability space of full words put $h=k\,1_U-1$. Its
mean is zero and its mean square is $k-1$.

For $B\in\mathcal F$, let $h_B$ be the mean of $h$ with the
coordinates in $B$ fixed. Write $\mathcal A_B$ for the selected words
with support $B$. Each word $b\in\mathcal A_B$ forces $h_B=k-1$.
Each of its $k-1$ other shifts forces $h_B=-1$. Distinct selected
words on $B$ have disjoint shift orbits. Consequently

$$
\frac{k(k-1)|\mathcal A_B|}{k^{|B|}}\leq \mathbb E[h_B^2].
$$

Decompose $h$ into the orthogonal components $u_S$ of a finite product
space. The component $u_S$ depends only on $S$ and has mean zero in each
coordinate of $S$. To obtain it, apply the coordinate-averaging operator
at each coordinate outside $S$, and the identity minus this operator at
each coordinate in $S$. These commuting projections give
$h_B=\sum_{S\subseteq B}u_S$. The masses $m_S=\mathbb E[u_S^2]/(k-1)$
sum to one, with $m_\varnothing=0$. The preceding inequality and
orthogonality give

$$
|\mathcal A|\leq\sum_{S\ne\varnothing}m_S
  \sum_{B\in\mathcal F:S\subseteq B} k^{|B|-1}\leq M.
$$

The last inequality holds since, for each $i\in S$, the inner sum is at
most $D_i$.

In equality, every positive-mass $S$ has inner sum $M$. Therefore each
coordinate of $S$ has a largest star, and every support containing one
coordinate of $S$ contains them all. Group the components by classes of
coordinates that occur in the same supports. This expresses $h$ as a sum
of functions on disjoint coordinate sets. Two nonconstant terms would give
at least three different sums, while $h$ has only two values. Thus $U$
depends on one class $C$ whose stars are largest.

The accepted patterns on $C$ have density $1/k$. Equality in the bound
implies that $\mathcal A_B$ consists of all extensions of these patterns
whenever $C\subseteq B$, and is empty otherwise. The patterns on $C$ are
themselves intersecting. If two disagreed everywhere, they could be
extended to disagree on every remaining coordinate of a support containing
$C$. The full-word theorem of Berge and Livingston gives a star for $k>2$.
In the binary case on at most two coordinates, a half-sized intersecting
family is also a star. Thus a nonstar maximum requires $k=2$ and at least
three coordinates in one class. The binary construction above attains it.
[Full-word theorem and its attribution, Borg, Theorem 1.1](https://staff.um.edu.mt/peter.borg/publications/v14i1r41.pdf)

## Prior work and verification

Borg proved the conjecture for support families compressed toward one
coordinate and for uniform support families that already have the
Erdős–Ko–Rado property. His later work covers sufficiently large alphabets.
[2007 paper](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v14i1r41) ·
[2009 restatement](https://doi.org/10.1016/j.disc.2008.09.039) ·
[2013 paper, Theorem 2.4](https://www.sciencedirect.com/science/article/pii/S0012365X13002033)

The bound on the size of an intersecting family also follows from two
earlier results. Borg reduced it to a weighted star bound on a hereditary
family. The weights in his reduction are nonnegative and decrease under
inclusion. Proposition 5.3 of Chang, Liu and Liu gives the required bound
for these weights. The orbit argument above proves the bound directly and
determines exactly when a maximum family can fail to be a star. A search
of papers citing Borg and of the equivalent signed-word formulations found
no earlier proof of this general equality criterion.
[Borg, Theorem 4.2 and Lemma 4.3](https://staff.um.edu.mt/peter.borg/publications/conjectures%20gen.pdf#page=6) ·
[Chang, Liu and Liu, Proposition 5.3](https://arxiv.org/html/2609.19123v1#S5)

[Statement.lean](Statement.lean) states both clauses.
[Solution.lean](Solution.lean) proves them in Lean, including an actual maximizing
star, the binary construction, and the full-word rigidity theorem. Run the following command
from the repository root.

~~~sh
python3 scripts/verify.py --fetch-cache
~~~

OpenAI Codex assisted with the proof and its formalization. An independent
audit compared the two clauses with the original paper and checked the orbit
count, orthogonality argument, and equality cases. A separate exact
enumeration checked all nonempty support families on three coordinates
with two and three labels, and on four coordinates with two labels.
