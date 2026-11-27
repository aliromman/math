module

public import conjectures.CFPLogDensity.Statement
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity.Upper
open Finset Real

noncomputable def mass (A : Finset ℕ) : ℝ := ∑ n ∈ A, (n:ℝ)⁻¹

theorem mass_mono {A B : Finset ℕ} (sub : A⊆B) : mass A≤mass B :=
  sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ ↦ by positivity)

theorem mass_union (A B : Finset ℕ) : mass (A∪B)≤mass A+mass B := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := fun n : ℕ ↦ (n:ℝ)⁻¹)
  have z : 0≤mass (A∩B) := sum_nonneg fun _ _ ↦ by positivity
  unfold mass at *
  linarith

theorem mass_cover (A : Finset ℕ) (B : ℕ→Finset ℕ) (k : ℕ) :
    mass (A ∪ (range k).biUnion B) ≤ mass A + ∑ j ∈ range k, mass (B j) := by
  apply (mass_union ..).trans
  apply add_le_add_right
  induction k with
  | zero => simp [mass]
  | succ n ih =>
    rw [sum_range_succ,range_add_one,biUnion_insert,add_comm]
    exact (mass_union ..).trans (add_le_add_right ih _)

private theorem harmonic_mass (n : ℕ) : mass (Icc 1 n) = (harmonic n : ℝ) := by
  simp [mass,harmonic_eq_sum_Icc]

theorem mass_interval {S : Finset ℕ} {l u : ℝ} (lu : l≤u)
    (bound : ∀ n∈S, 0<n ∧ l≤log n ∧ log n≤u) : mass S ≤ 1+u-l := by
  rcases S.eq_empty_or_nonempty with e|ne
  · simp [e,mass]; linarith
  let a := S.min' ne
  let b := S.max' ne
  have ha := bound a (min'_mem ..)
  have hb := bound b (max'_mem ..)
  have ab : a≤b := S.min'_le _ (S.max'_mem ne)
  have pos := ha.1
  have sub : S⊆Icc a b := fun n hn ↦ mem_Icc.mpr ⟨S.min'_le _ hn,S.le_max' _ hn⟩
  have partition : Icc 1 b = Icc 1 (a-1) ∪ Icc a b := by ext n; simp; omega
  have disj : Disjoint (Icc 1 (a-1)) (Icc a b) := by
    apply disjoint_left.mpr
    intro n hn ht
    have := (mem_Icc.mp hn).2
    have := (mem_Icc.mp ht).1
    omega
  have parts : mass (Icc 1 b)=mass (Icc 1 (a-1))+mass (Icc a b) := by
    rw [partition,mass,sum_union disj]
    rfl
  rw [harmonic_mass,harmonic_mass] at parts
  have upper := harmonic_le_one_add_log b
  have lower := log_add_one_le_harmonic (a-1)
  rw [show a-1+1=a by omega] at lower
  exact (mass_mono sub).trans (by linarith [ha.2.1,hb.2.2])

noncomputable def coverValue (R c : ℝ) := (c-1)*R / ((R-1)*c)

/-- A partial last interval contributes at most its share at its right endpoint. -/
theorem geometric_cover {R c a y : ℝ} (hR : 1<R) (hc : 1≤c) (gap : c≤R)
    :
    (c-1)*a/(R-1) + (min (c*a) y - a) ≤ coverValue R c*y := by
  have rp : 0<R-1 := by linarith
  have cp : 0<c := by linarith
  let v := coverValue R c
  have exactEnd : (c-1)*a/(R-1) + (c*a-a) = v*(c*a) := by
    dsimp [v,coverValue]
    field_simp
    ring
  have vpos : 0≤v := by dsimp [v,coverValue]; positivity
  have vle : v≤1 := by
    dsimp [v,coverValue]
    apply (div_le_iff₀ (mul_pos rp cp)).mpr
    nlinarith
  change _ ≤ v*y
  rcases le_total (c*a) y with h|h
  · rw [min_eq_left h,exactEnd]
    exact mul_le_mul_of_nonneg_left h vpos
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.mpr vle) (sub_nonneg.mpr h)]

theorem preceding {R c a : ℝ} (hR : 1<R) (hc : 1≤c) (ha : 0≤a) (j : ℕ) :
    (∑ t ∈ range j, (1+(c-1)*(a*R^t))) ≤ j+(c-1)*(a*R^j)/(R-1) := by
  have g := geom_sum_mul R j
  have eq : ∑ t ∈ range j, (c-1)*(a*R^t) = ((c-1)*a)*(∑ t ∈ range j,R^t) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  rw [sum_add_distrib,eq,sum_const,card_range,nsmul_eq_mul,mul_one]
  apply add_le_add_right
  apply (le_div_iff₀ (by linarith : 0<R-1)).mpr
  rw [mul_assoc,g]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) ha]

end CFPLogDensity.Upper
