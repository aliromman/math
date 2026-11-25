# Four consecutive vertices disprove fence homomesy

Start with the order ideal $\{x_{10}, x_{11}, x_{12}, x_{13}\}$ in the 32-element fence $\breve F(3^{11})$. Its orbit under rowmotion contains 237 ideals. Their sizes add to 3774. The average is

$$\frac{3774}{237}=16-\frac{6}{79}.$$

Elizalde, Plante, Roby and Sagan conjectured that on a constant fence with an odd number of segments, every rowmotion orbit has average ideal size equal to half the size of the fence. Here that prediction is 16. The authors verified the conjecture for $a+t\le12$. The example has $a+t=14$. [*Rowmotion on fences*, Algebraic Combinatorics 6 (2023), Conjecture 5.4(b), p. 35](https://www.numdam.org/item/10.5802/alco.256.pdf)

## The fence and its orbit

The fence is a path of alternating increasing and decreasing chains. In $\breve F(a^t)$ each of the $t$ chains has $a-1$ vertices that belong only to it. Consecutive chains share one vertex. For $a=3$ and $t=11$ the first and last chains have two edges and each interior chain has three. Thus $x_3,x_6,\dots,x_{30}$ are alternately peaks and valleys. The two maximal elements of the starting ideal are $x_{10}$ and $x_{13}$.

Rowmotion replaces an ideal $I$ with the downward closure of the minimal elements outside $I$. The following Python code constructs the fence from its cover edges and iterates this definition.

```python
vertices = range(1, 33)
below = {x: {x} for x in vertices}
edges = [(x, x + 1) if (x // 3) % 2 == 0 else (x + 1, x)
         for x in range(1, 32)]
for _ in vertices:
    for lower, upper in edges:
        below[upper].update(below[lower])

start = frozenset({10, 11, 12, 13})
ideal, seen = start, set()
while ideal not in seen:
    seen.add(ideal)
    minima = [x for x in vertices if x not in ideal and below[x] - {x} <= ideal]
    ideal = frozenset().union(*(below[x] for x in minima))
assert ideal == start
assert (len(seen), sum(map(len, seen))) == (237, 3774)
```

The discrepancy also has a local description. Over this orbit the maximal elements of the ideals include a shared peak 93 times and a shared valley 99 times, counted with multiplicity. Theorem 14 of Mertin and Poznanović identifies the total error as $3(93-99)=-18$. Their Conjecture 12 restates the original prediction, and their Conjecture 15 gives its equivalent peak-and-valley form. A literature search found no earlier counterexample. [*Toggleability Spaces of Fences*, Electronic Journal of Combinatorics 31(4) (2024), §5](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p46/pdf/)

## Formal verification

The Lean statement defines the order on every constant fence, the rowmotion map, and the conjectured identity for every cycle of distinct ideals. The proof checks that each of the 237 supplied sets is an ideal, that all sets are distinct, that each maps to the next (including the last to the first), and that their cardinalities sum to 3774.

```sh
lake exe cache get
lake build conjectures.FenceRowmotion.Solution
lake env leanchecker conjectures.FenceRowmotion.Solution
```

OpenAI Codex found the orbit by exhaustive search, wrote the finite certificate, and formalized the argument in Lean.
