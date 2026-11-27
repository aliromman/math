# Permutation peak polynomials

For an admissible set of positions $S$ and $n>\max S$, the peak polynomial
$p_S$ counts permutations of $[n]$ with peak set exactly $S$, after division
by $2^{n-|S|-1}$. The count and the polynomial both vanish at $n=\max S$
for nonempty $S$. The empty peak set has polynomial one.
[Billey, Burdzy and Sagan, *Permutations with Given Peak Set*](https://cs.uwaterloo.ca/journals/JIS/VOL16/Billey/billey2.html)

The shared Lean modules adapt Alex Chengyu Li's MIT-licensed proof of
concavity in the rising binomial basis. They include the permutation count,
the backward Newton expansion, the recurrence that removes the last peak,
and the coefficient bounds. The two declarations in `axioms` check the
counting formula and the concavity theorem. The MIT license and attribution
apply to the adapted code. [Li's paper](https://doi.org/10.2139/ssrn.7435858)
· [Archived source](https://doi.org/10.5281/zenodo.22661864) · [License](LICENSE-Li.txt)
