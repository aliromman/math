# Disproof of Defant and Lin’s Conjecture 10.2 on down-degree homometry in ν-Tamari lattices

For the path $\nu=EENENENNEEEEEN$, two orbits of rowmotion in the same $\nu$-Tamari lattice have length six. Their total down-degrees are

$$3+3+4+3+2+3=18,\qquad 3+2+4+2+4+2=17.$$

The down-degree counts how many elements lie immediately below a lattice element. Defant and Lin conjectured that two rowmotion orbits of the same length always have the same total down-degree. The six steps give orbit averages $3$ and $17/6$. [Defant and Lin, *Rowmotion on $`m`$-Tamari and biCambrian lattices*, Conjecture 10.2](https://doi.org/10.5070/C64163852)

## The two cycles

Use the authors’ bracket vectors. The path has five north steps and nine east steps. Each vector has 15 entries, indexed from 0. Positions $2,4,6,7,13,14$ are fixed at $0,1,2,3,4,5$, respectively. Each string in the table gives the nine remaining entries in order. Rowmotion moves down each column and then returns to the first row.

| First vector | Down-degree | Second vector | Down-degree |
| --- | ---: | --- | ---: |
| `005355554` | 3 | `333344444` | 3 |
| `553255544` | 3 | `501255555` | 2 |
| `532255444` | 4 | `333355554` | 4 |
| `321254444` | 3 | `501255544` | 2 |
| `211244444` | 2 | `333355444` | 4 |
| `101555555` | 3 | `501254444` | 2 |

The verification uses the componentwise order on all 427 valid bracket vectors. For a vector $x$, let $p$ be the componentwise minimum of $x$ and its lower covers. By Proposition 2.2 of Defant and Lin, the next vector is the greatest $y$ for which $x\wedge y=p$. For each table entry the proof checks the full set of lower covers and verifies this greatest-element condition against every vector. Thus the degree counts and the cyclic transitions both follow from the lattice order. [Defant and Lin, §§2.3 and 3.2](https://escholarship.org/uc/item/5x945586)

A second search used the Young diagram $(9,4,4,3,2)$. Theorem 1.1 of Adenbaum, Barnard, Ceballos, Chenevière, Defant, Hopkins, Müller, Rubey and Striker identifies the orbit lengths and down-degree sums for the distributive and ordinary lattices of the same path. Eu, Hioe and Lee record the original conjecture as Conjecture 2.5 and extend it to alternate Tamari lattices in Conjecture 5.1. A search for prior counterexamples found none. [Adenbaum et al., Theorem 1.1](https://arxiv.org/abs/2609.12983) · [Eu, Hioe and Lee, Conjectures 2.5 and 5.1](https://arxiv.org/abs/2605.29431)

## Verification

```sh
# Run at the merge commit for PR #54.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

OpenAI Codex found the two orbits, checked them against the bracket-vector rowmotion algorithm and the lower-cover order, and wrote the Lean proof.

Colin Defant and James Lin, Rowmotion on m-Tamari and biCambrian lattices, Conjecture 10.2. [Publication](https://escholarship.org/content/qt5x945586/qt5x945586.pdf)
