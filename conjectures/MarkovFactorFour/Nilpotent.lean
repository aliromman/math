module

public import Mathlib.Dynamics.Newton
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace MarkovFactorFour

variable {R : Type*} [CommRing R]

/-- Newton lifting at zero yields the small root of T²−LT+x. -/
theorem small_root {x L : R} (hx : IsNilpotent x) (hL : IsUnit L) :
    ∃ s : R, IsNilpotent s ∧ x ∣ s ∧ s*(L-s)=x := by
  let P : Polynomial R := .X^2 - .C L * .X + .C x
  have hv : IsNilpotent (Polynomial.aeval (0 : R) P) := by simpa [P] using hx
  have hd : IsUnit (Polynomial.aeval (0 : R) P.derivative) := by
    simpa [P] using hL.neg
  obtain ⟨s, hs, hroot⟩ := (Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hv hd).exists
  have hn : IsNilpotent s := by simpa using hs
  have eqn : s*(L-s) = x := by
    simp [P] at hroot
    linear_combination -hroot
  have hunit : IsUnit (L-s) := by
    simpa [sub_eq_add_neg, add_comm] using
      (hn.neg.isUnit_add_left_of_commute hL (Commute.all _ _))
  obtain ⟨inv, hi⟩ := hunit.exists_right_inv
  exact ⟨s, hn, ⟨inv, by rw [← eqn, mul_assoc, hi, mul_one]⟩, eqn⟩

/-- This mixed trace identity is where the factor four enters. -/
theorem mixed_trace {u v s t : R} (hfour : (4 : R) = 0)
    (hs : s*(1+u+v-s)=u) (ht : t*(1+u+v-t)=v)
    (hsnil : IsNilpotent s) (htnil : IsNilpotent t) :
    (1+u+v)*(u+v)=s*(1+u+v-t)+(1+u+v-s)*t := by
  let L := 1+u+v
  let e := 1-(s+t)
  let delta := L-1-s-t
  have he : IsUnit e := ((Commute.all _ _).isNilpotent_add hsnil htnil).isUnit_one_sub
  obtain ⟨inv, hi⟩ := he.exists_right_inv
  have hde : delta*e = 2*s*t := by
    dsimp [delta,L,e]
    linear_combination -hs - ht
  have hd : delta = 2*(s*t*inv) := by
    calc
      delta = (delta*e)*inv := by rw [mul_assoc, hi, mul_one]
      _ = _ := by rw [hde]; ring
  have diff :
      L*(u+v) - (s*(L-t)+(L-s)*t) = delta*(2+delta) := by
    calc
      _ = L*delta + 2*s*t := by dsimp [delta,L]; ring
      _ = delta*(2+delta) := by rw [← hde]; dsimp [delta,e]; ring
  apply sub_eq_zero.mp
  change L*(u+v) - _ = _
  rw [diff, hd]
  calc
    _ = 4*((s*t*inv) + (s*t*inv)^2) := by ring
    _ = 0 := by rw [hfour, zero_mul]

end MarkovFactorFour
