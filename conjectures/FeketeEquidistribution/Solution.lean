module

public import conjectures.FeketeEquidistribution.Odd
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace FeketeEquidistribution
open Finset Polynomial

theorem six_factor : cyclotomic 8 ℤ ∣ fekete 6 := by
  have exponents : (range 6).filter (fun a ↦ a.Coprime 6) = {1,5} := by decide
  have phi : cyclotomic 8 ℤ = X ^ 4 + 1 := by
    rw [show 8 = 2 ^ (2 + 1) by norm_num, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [sum_range_succ,add_comm]
  refine ⟨X, ?_⟩
  rw [fekete, exponents, phi]
  simp
  ring

theorem six_unequal : ¬Equidistributed 6 8 := by
  intro h
  have bad := h 1 (by decide) (by decide) 3 (by decide) (by decide)
  exact (by decide : residueCount 6 8 1 ≠ residueCount 6 8 3) bad

theorem resolution : ¬Conjecture := by
  intro h
  obtain ⟨sf,_,fac,unequal⟩ := odd_witness
  exact unequal ((h 1122987 (by decide) sf 63 (by decide) (by decide)).mp fac)

/-- info: 'FeketeEquidistribution.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end FeketeEquidistribution
