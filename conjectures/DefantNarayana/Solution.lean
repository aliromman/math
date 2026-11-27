module

public import conjectures.DefantNarayana.Statement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Polynomial

namespace DefantNarayana

/-- A Fano line consists of three distinct nonzero binary vectors whose xor is zero. -/
private def points : List (Fin 7 → ℕ) := Id.run do
  let mut s := []
  for a in List.finRange 7 do
    for b in List.finRange 7 do
      for c in List.finRange 7 do
        if a < b ∧ b < c ∧ ((a.val + 1) ^^^ (b.val + 1)) ≠ c.val + 1 then
          s := (fun i => 1 + (if i.val < 3 then 1 else 0) +
            (if i = a ∨ i = b ∨ i = c then 1 else 0)) :: s
  return s

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem admissible : GeneralizedPermutohedron points := by
  unfold GeneralizedPermutohedron
  decide +kernel

private theorem point_entries : ∀ p ∈ points, ∀ j, p j = 1 ∨ p j = 2 ∨ p j = 3 := by
  decide +kernel

private def signature (p : Fin 7 → ℕ) : ℕ × ℕ :=
  ((List.ofFn p).count 2, (List.ofFn p).count 3)

private theorem signatures : (points.map signature).Perm
    (List.replicate 4 (6, 0) ++ List.replicate 12 (4, 1) ++ List.replicate 12 (2, 2)) := by
  decide +kernel

private theorem small (z : ℂ) : narayana 1 z = z ∧ narayana 2 z = z * (1 + z) ∧
    narayana 3 z = z * (1 + 3*z + z^2) := by
  constructor
  · norm_num [narayana, Finset.sum_range_succ, Nat.choose]
  constructor <;> norm_num [narayana, Finset.sum_range_succ, Nat.choose] <;> ring

private theorem product_formula (l : List ℕ) (z : ℂ) (h : ∀ i ∈ l, i = 1 ∨ i = 2 ∨ i = 3) :
    (l.map (narayana · z)).prod = z^l.length * (1+z)^(l.count 2) * (1+3*z+z^2)^(l.count 3) := by
  obtain ⟨h1, h2, h3⟩ := small z
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    rcases h a (List.mem_cons_self) with rfl | rfl | rfl <;>
      simp [ht, h1, h2, h3, pow_succ] <;> ring

private theorem evaluate (z : ℂ) : narayanaSum points z =
    4 * z^7 * (1+z)^2 * (7*z^4 + 37*z^3 + 63*z^2 + 37*z + 7) := by
  let g : ℕ × ℕ → ℂ := fun t => z^7 * (1+z)^t.1 * (1+3*z+z^2)^t.2
  have heq : narayanaSum points z = ((points.map signature).map g).sum := by
    unfold narayanaSum
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    simpa [g, signature] using product_formula (List.ofFn p) z (fun k hk => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk
      exact point_entries p hp j)
  rw [heq, (signatures.map g).sum_eq]
  simp [g]
  ring

private noncomputable def quartic : ℂ[X] := 7 * X^4 + 37 * X^3 + 63 * X^2 + 37 * X + 7

private theorem quartic_has_root : ∃ z : ℂ, quartic.eval z = 0 := by
  apply IsAlgClosed.exists_root
  intro h
  have he : quartic.eval 0 = quartic.eval 1 := by rw [eq_C_of_degree_eq_zero h]; simp
  norm_num [quartic] at he

private theorem positive (x : ℝ) : 0 < 7*x^4 + 37*x^3 + 63*x^2 + 37*x + 7 := by
  by_cases hx : x = 0
  · simp [hx]
  · nlinarith [sq_nonneg (14*x^2 + 37*x + 14), sq_pos_of_ne_zero hx,
      show (14*x^2+37*x+14)^2+3*x^2 = 28*(7*x^4+37*x^3+63*x^2+37*x+7) by ring]

public theorem resolution : ¬ Conjecture := by
  intro h
  obtain ⟨z, hz⟩ := quartic_has_root
  have he : 7*z^4 + 37*z^3 + 63*z^2 + 37*z + 7 = 0 := by simpa [quartic] using hz
  have hi := h 6 points admissible z (by rw [evaluate, he, mul_zero])
  have hre : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [hi])
  rw [← hre] at he
  have hreal : 7*z.re^4 + 37*z.re^3 + 63*z.re^2 + 37*z.re + 7 = 0 := by exact_mod_cast he
  exact (positive z.re).ne' hreal

/-- info: 'DefantNarayana.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end DefantNarayana
