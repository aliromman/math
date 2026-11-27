module

public import conjectures.MarkovFactorFour.Farey

@[expose] public section
namespace MarkovNearestFour
open MarkovFactorFour (numerator exponent)

abbrev Fraction := ℕ × ℕ

/-- Consecutive convergents, in numerator-denominator order, after each partial quotient. -/
def continuants : List ℕ → Fraction × Fraction :=
  List.foldl (fun (p : Fraction × Fraction) k =>
    (p.2, (k*p.2.1+p.1.1, k*p.2.2+p.1.2))) ((0,1),(1,0))

/-- Conjecture 8.4 at the penultimate convergent of b/a. The critical triangle is nonempty
when 1<a<b. The reflected coordinates for the two parities follow equation (32). -/
def Conjecture : Prop :=
  ∀ ds : List ℕ, (∀ k ∈ ds, 0<k) →
    let (prev, cur) := continuants ds
    let (b,a) := cur
    1<a → a<b →
      (numerator a b).coeff (if ds.length % 2=0 then exponent prev.2 (b-prev.1)
        else exponent (a-prev.2) prev.1)=4

end MarkovNearestFour
