module

public import conjectures.ConsecutiveThreshold.LogConcavity
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators

abbrev Series := AddMonoidAlgebra ℝ ℤ

/-- Inversion generating function of one digit with d possible values. -/
noncomputable def geom (q : ℝ) (d : ℕ) : Series :=
  ∑ i∈range d,AddMonoidAlgebra.single (i:ℤ) (q^i)

/-- Evaluation at one gives the total weight. -/
noncomputable def atOne : Series →+* ℝ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℝ) (1 : Multiplicative ℤ →* ℝ) (fun _ _ ↦ Commute.all ..)

@[simp] theorem atOne_single (j : ℤ) (v : ℝ) : atOne (AddMonoidAlgebra.single j v)=v := by
  simp [atOne]

def positiveSeries (P : Series) : Prop := ∀ i,0≤P.coeff i

theorem positive_mul {P Q : Series} (p : positiveSeries P) (q : positiveSeries Q) :
    positiveSeries (P*Q) := by
  intro i
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  exact sum_nonneg fun j _ ↦ mul_nonneg (p j) (q _)

theorem positive_one : positiveSeries 1 := by
  intro i
  change 0≤(Finsupp.single (0:ℤ) (1:ℝ)) i
  simp only [Finsupp.single_apply]
  split <;> norm_num

theorem positive_prod {α : Type*} (S : Finset α) (P : α → Series)
    (p : ∀ i∈S,positiveSeries (P i)) : positiveSeries (∏ i∈S,P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using positive_one
  | insert a S ha ih =>
    rw [prod_insert ha]
    exact positive_mul (p _ (mem_insert_self ..)) (ih fun i hi ↦ p i (mem_insert_of_mem hi))

theorem coeff_sum {α : Type*} (S : Finset α) (P : α → Series) (i : ℤ) :
    (∑ x∈S,P x).coeff i=∑ x∈S,(P x).coeff i := by
  simp

theorem geom_coeff (q : ℝ) (d : ℕ) (z : ℤ) :
    (geom q d).coeff z=if 0≤z ∧ z<(d:ℤ) then q^z.toNat else 0 := by
  unfold geom
  rw [coeff_sum]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases h : 0≤z ∧ z<(d:ℤ)
  · have hz : (z.toNat:ℤ)=z := by omega
    rw [ite_eq_left h,sum_eq_single z.toNat]
    · simp [hz]
    · intro i _ ni
      have : (i:ℤ)≠z := by omega
      simp [this]
    · intro no
      have : z.toNat<d := by omega
      exact (no (mem_range.mpr this)).elim
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro i hi
    have il := mem_range.mp hi
    have : (i:ℤ)≠z := by omega
    simp [this]

theorem positive_geom {q : ℝ} (hq : 0≤q) (d : ℕ) : positiveSeries (geom q d) := by
  intro z
  rw [geom_coeff]
  split <;> positivity

theorem atOne_geom_pos {q : ℝ} (hq : 0≤q) {d : ℕ} (hd : 0<d) : 0<atOne (geom q d) := by
  simp only [geom,map_sum,atOne_single]
  have h := single_le_sum (s:=range d) (f:=fun i ↦ q^i) (fun i _ ↦ pow_nonneg hq i) (mem_range.mpr hd)
  simpa only [pow_zero] using (show 0<q^0 from by positivity).trans_le h

end ConsecutiveThreshold
