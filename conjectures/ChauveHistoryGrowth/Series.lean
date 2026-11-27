module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth

open PowerSeries Finset

abbrev S := PowerSeries ℝ

def Below (a b : S) := ∀ n, coeff n a ≤ coeff n b
infix:50 " ≼ " => Below

theorem refl (a : S) : a ≼ a := fun _ => le_rfl
theorem trans {a b c : S} (h : a ≼ b) (h' : b ≼ c) : a ≼ c := fun i => (h i).trans (h' i)
theorem zeroBelow (a : S) : 0 ≼ a ↔ ∀ n, 0 ≤ coeff n a := by simp [Below]
theorem onePos : 0 ≼ (1 : S) := by
  rw [zeroBelow]
  intro n
  by_cases h : n=0 <;> simp [coeff_one,h]
theorem addM {a b c d : S} (h : a ≼ b) (k : c ≼ d) : a+c ≼ b+d := by
  intro n
  simpa only [map_add] using add_le_add (h n) (k n)
theorem addP {a b : S} (h : 0 ≼ a) (k : 0 ≼ b) : 0 ≼ a+b := zero_add (0:S) ▸ addM h k
theorem mulM {a b c d : S} (h : a ≼ b) (k : c ≼ d) (ha : 0 ≼ a) (hd : 0 ≼ d) :
    a*c ≼ b*d := by
  intro n
  simp only [coeff_mul]
  apply sum_le_sum
  intro ij _
  exact (mul_le_mul_of_nonneg_left (k ij.2) (by simpa using ha ij.1)).trans
    (mul_le_mul_of_nonneg_right (h ij.1) (by simpa using hd ij.2))

theorem mulP {a b : S} (h : 0 ≼ a) (k : 0 ≼ b) : 0 ≼ a*b := by
  simpa using mulM h (refl b) (refl 0) k

theorem subP {a b : S} : 0 ≼ b-a ↔ a ≼ b := by
  simp [Below]

theorem nonneg_fixed {a u y : S} (ha : 0 ≼ a) (hu : 0 ≼ u) (hz : constantCoeff u = 0)
    (eqn : y = a+u*y) : 0 ≼ y := by
  rw [zeroBelow] at ha hu ⊢
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    conv_rhs => rw [eqn, map_add, coeff_mul]
    apply add_nonneg (ha _)
    apply sum_nonneg
    rintro ⟨i,j⟩ hij
    have hij' : i+j=n := Finset.mem_antidiagonal.mp hij
    by_cases h : j<n
    · exact mul_nonneg (hu i) (ih j h)
    · have hi : i=0 := by omega
      simp [hi,coeff_zero_eq_constantCoeff,hz]

def seqS (a : S) : S := (1-a)⁻¹

theorem seq_unit {a : S} (az : constantCoeff a=0) : (1-a)*seqS a=1 := by
  apply PowerSeries.mul_inv_cancel
  simp [az]

theorem seq_eq {a : S} (az : constantCoeff a=0) : seqS a=1+a*seqS a := by
  linear_combination seq_unit az

theorem seq_pos {a : S} (ha : 0 ≼ a) (az : constantCoeff a=0) : 0 ≼ seqS a :=
  nonneg_fixed onePos ha az (seq_eq az)

theorem seq_mono {a b : S} (ha : 0 ≼ a) (h : a ≼ b)
    (az : constantCoeff a=0) (bz : constantCoeff b=0) : seqS a ≼ seqS b := by
  apply subP.mp
  apply nonneg_fixed (mulP (subP.mpr h) (seq_pos ha az)) (trans ha h) bz
  linear_combination seq_eq bz - seq_eq az

def den (a b : S) := a*a+b+a*b
def num (a b : S) := a+b+a*b
def multiplier (a b : S) := 1+num a b*seqS (den a b)

theorem multiplier_one {a b : S} (ha : 0 ≼ a) (hb : 0 ≼ b)
    (az : constantCoeff a=0) (bz : constantCoeff b=0) : 1 ≼ multiplier a b := by
  have dn := addP (addP (mulP ha ha) hb) (mulP ha hb)
  have nn := addP (addP ha hb) (mulP ha hb)
  have z : constantCoeff (den a b)=0 := by simp [den,az,bz]
  simpa [multiplier,num,den] using addM (refl 1) (mulP nn (seq_pos dn z))

theorem multiplier_mono {a b c d : S} (ha : 0 ≼ a) (hb : 0 ≼ b) (ac : a ≼ c)
    (bd : b ≼ d) (az : constantCoeff a=0) (bz : constantCoeff b=0)
    (cz : constantCoeff c=0) (dz : constantCoeff d=0) : multiplier a b ≼ multiplier c d := by
  have acbd := mulM ac bd ha (trans hb bd)
  have dn := addM (addM (mulM ac ac ha (trans ha ac)) bd) acbd
  have nn := addM (addM ac bd) acbd
  have nd := addP (addP (mulP ha ha) hb) (mulP ha hb)
  have nc := addP (addP ha hb) (mulP ha hb)
  have nd' := addP (addP (mulP (trans ha ac) (trans ha ac)) (trans hb bd))
    (mulP (trans ha ac) (trans hb bd))
  have z : constantCoeff (den a b)=0 := by simp [den,az,bz]
  have w : constantCoeff (den c d)=0 := by simp [den,cz,dz]
  exact addM (refl 1) (mulM nn (seq_mono nd dn z w) nc (seq_pos nd' w))

theorem multiplier_identity {a b D : S} (az : constantCoeff a=0) (bz : constantCoeff b=0)
    (h : 1+b-b*b=(1+a-a*a)*(1+D)) :
    1+b=(1+a)*(1+D*multiplier a b) := by
  let z : S := 1-den a b
  have dz : constantCoeff (den a b)=0 := by simp [den,az,bz]
  have zu : z*seqS (den a b)=1 := seq_unit dz
  have zne : z≠0 := by intro e; simp [e] at zu
  have mz : multiplier a b*z=1+a-a*a := by
    unfold multiplier
    calc
      (1+num a b*seqS (den a b))*z = z+num a b*(z*seqS (den a b)) := by ring
      _ = 1+a-a*a := by rw [zu]; dsimp [z,den,num]; ring
  apply mul_right_cancel₀ zne
  calc
    (1+b)*z=(1+a)*z+(1+a)*((1+b-b*b)-(1+a-a*a)) := by dsimp [z,den]; ring
    _=(1+a)*z+(1+a)*D*(1+a-a*a) := by rw [h]; ring
    _=(1+a)*(1+D*multiplier a b)*z := by rw [← mz]; ring

end ChauveHistoryGrowth
end
