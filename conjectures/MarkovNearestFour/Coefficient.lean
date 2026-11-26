module

public import conjectures.MarkovNearestFour.Walk
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace MarkovNearestFour
open Finset PowerSeries

private theorem first_coordinate_lt {a b x y : ℕ} (ha : 1<a) (hb : 1<b)
    (h : b*x+a*y=a*b+1) : x<a := by
  by_contra! hn
  by_cases e : a=x
  · subst x
    have ay : a*y=1 := by nlinarith
    have : a ∣ 1 := ⟨y,ay.symm⟩
    have := Nat.dvd_one.mp this
    omega
  · have hax : a+1≤x := by omega
    have := Nat.mul_le_mul_left b hax
    nlinarith

private theorem unique_weight {a b i j x y : ℕ} (ha : 1<a) (hb : 1<b) (cop : a.Coprime b)
    (h : b*i+a*j=a*b+1) (h' : b*x+a*y=a*b+1) : x=i ∧ y=j := by
  have eq : b*x ≡ b*i [MOD a] := by
    have e := congrArg (·%a) (h'.trans h.symm)
    simpa [Nat.ModEq,Nat.add_mod] using e
  have ex := Nat.ModEq.cancel_left_of_coprime cop eq
  change x%a=i%a at ex
  rw [Nat.mod_eq_of_lt (first_coordinate_lt ha hb h'),
    Nat.mod_eq_of_lt (first_coordinate_lt ha hb h)] at ex
  subst x
  exact ⟨rfl, mul_left_cancel₀ (by omega : a≠0) (Nat.add_left_cancel (h'.trans h.symm))⟩

private theorem coeff_monomial_weight (a b n : ℕ) (d : Fin 2 →₀ ℕ) (c : ℤ) :
    coeff n (specialize a b (MvPolynomial.monomial d c)) =
      if n=b*d 0+a*d 1 then c else 0 := by
  rw [specialize,MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_two]
  change coeff n ((c : Series)*((z^b)^(d 0)*(z^a)^(d 1)))=_
  rw [←pow_mul,←pow_mul,←pow_add]
  simp

/-- There is one monomial at weight ab+1, so its integer coefficient is four. -/
theorem coefficient_four (a b i j : ℕ) (ha : 1<a) (hab : a<b) (cop : a.Coprime b)
    (hw : b*i+a*j=a*b+1) : (numerator a b).coeff (exponent i j)=4 := by
  let p := numerator a b
  have h := first_above a b ha hab cop
  change coeff (a*b+1) (specialize a b p)=4 at h
  have eq : coeff (a*b+1) (specialize a b p)=p.coeff (exponent i j) := by
    calc
      _ = coeff (a*b+1) (specialize a b (∑ d∈p.support,
            MvPolynomial.monomial d (p.coeff d))) := congrArg (fun t => coeff (a*b+1) (specialize a b t)) p.as_sum
      _ = ∑ d∈p.support, if a*b+1=b*d 0+a*d 1 then p.coeff d else 0 := by
        simp only [map_sum,coeff_monomial_weight]
      _ = p.coeff (exponent i j) := by
        rw [Finset.sum_eq_single (exponent i j)]
        · simp [exponent,hw]
        · intro d _ ne
          apply ite_eq_right
          intro e
          obtain ⟨h0,h1⟩ := unique_weight ha (ha.trans hab) cop hw e.symm
          apply ne
          ext k
          fin_cases k <;> simp [exponent,h0,h1]
        · intro hne
          have hz : p.coeff (exponent i j)=0 := by simpa using hne
          simp [hz]
  exact eq.symm.trans h

end MarkovNearestFour
