module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic

/-!
The separation and rounding arguments are adapted from Chen's CC0 formalization
of interval divisor covers, revision `dc150fd723184cc4e6f367aac6e7a8c9c7890f34`,
from `Chain/LP.lean` and `Chain/Proofs/Rounding.lean`.
-/

@[expose] public section
namespace ErdosSuranyi708
open Finset
open scoped Pointwise

lemma functional_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] ℝ) (u : ι → ℝ) :
    f u = ∑ i, f (Pi.single i 1) * u i := by
  have heq : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [heq, map_sum]
  apply sum_congr rfl
  intro i hi
  simp only [map_smul, smul_eq_mul]
  ring

/-- Strict finite-dimensional LP separation, with nonnegative dual multipliers. -/
lemma separating_dual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (b : κ → ℝ) (r : ℝ)
    (hfeas : ∃ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∀ p, b p ≤ ∑ i, M p i * y i)
    (hr : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
      (∀ p, b p ≤ ∑ i, M p i * y i) → r < ∑ i, y i) :
    ∃ z : κ → ℝ, (∀ p, 0 ≤ z p) ∧
      r < (∑ p, z p * b p) - ∑ i, max ((∑ p, z p * M p i) - 1) 0 := by
  classical
  let F : (ι → ℝ) → (Option κ → ℝ) := fun y i => match i with
    | none => ∑ j, y j
    | some p => b p - ∑ j, M p j * y j
  let K : Set (ι → ℝ) := Set.Icc 0 1
  let C : Set (Option κ → ℝ) := F '' K + Set.Ici 0
  let v : Option κ → ℝ := Pi.single none r
  have hFcont : Continuous F := by
    apply continuous_pi
    intro i
    cases i <;> dsimp [F] <;> fun_prop
  have hKcomp : IsCompact K := isCompact_Icc
  have hFconv : Convex ℝ (F '' K) := by
    intro u hu v hv a c ha hc hac
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, rfl⟩ := hv
    refine ⟨a • y + c • z, (convex_Icc (0 : ι → ℝ) 1) hy hz ha hc hac, ?_⟩
    ext i
    cases i with
    | none => simp [F, sum_add_distrib, ← mul_sum]
    | some p =>
      simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
      simp_rw [mul_left_comm (M p _)]
      rw [← mul_sum, ← mul_sum]
      have hh : (a+c)*b p = b p := by rw [hac, one_mul]
      nlinarith [hh]
  have hCclosed : IsClosed C := isClosed_Ici.add_left_of_isCompact (hKcomp.image hFcont)
  have hCconv : Convex ℝ C := hFconv.add (convex_Ici 0)
  have hvnot : v ∉ C := by
    rintro ⟨fy, ⟨y, hy, rfl⟩, u, hu, hsum⟩
    have hcover : ∀ p, b p ≤ ∑ i, M p i * y i := by
      intro p
      have hh := congrFun hsum (some p)
      have hu0 : 0 ≤ u (some p) := hu (some p)
      simp only [F, v, Pi.single_eq_of_ne (Option.some_ne_none p), Pi.add_apply] at hh
      linarith
    have hy' : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i => ⟨hy.1 i, hy.2 i⟩
    have hcost := hr y hy' hcover
    have hh := congrFun hsum none
    have hu0 : 0 ≤ u none := hu none
    simp only [F, v, Pi.single_eq_same, Pi.add_apply] at hh
    linarith
  obtain ⟨l, u, hlu, hul⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hvnot
  have hsep : ∀ c ∈ C, l v < l c := fun c hc => hlu.trans (hul c hc)
  let coeff : Option κ → ℝ := fun i => l (Pi.single i 1)
  have heval (w : Option κ → ℝ) : l w = ∑ i, coeff i * w i := functional_coordinates l w
  have hbase : F 0 ∈ C := by
    exact ⟨F 0, ⟨0, ⟨le_rfl, by intro i; norm_num⟩, rfl⟩, 0, by simp, add_zero _⟩
  have hcoeff : ∀ i, 0 ≤ coeff i := by
    intro i
    by_contra hi
    have hi' : coeff i < 0 := lt_of_not_ge hi
    have hgap : 0 < l (F 0) - l v + 1 := by have := hsep _ hbase; linarith
    let t := (l (F 0) - l v + 1) / (-coeff i)
    have ht : 0 < t := div_pos hgap (neg_pos.mpr hi')
    have hmem : F 0 + t • Pi.single i 1 ∈ C := by
      refine ⟨F 0, ⟨0, ⟨le_rfl, by intro j; norm_num⟩, rfl⟩, t • Pi.single i 1, ?_, rfl⟩
      intro j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> positivity
    have hs := hsep _ hmem
    rw [map_add, map_smul] at hs
    change l v < l (F 0) + t * coeff i at hs
    have hid : t * (-coeff i) = l (F 0) - l v + 1 := div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hi'))
    nlinarith
  have hcostpos : 0 < coeff none := by
    have hnon := hcoeff none
    by_contra hn
    have hz : coeff none = 0 := by linarith
    obtain ⟨y, hy, hcover⟩ := hfeas
    let w : Option κ → ℝ := Pi.single none (∑ i, y i)
    have hw : w ∈ C := by
      refine ⟨F y, ⟨y, ⟨fun i => (hy i).1, fun i => (hy i).2⟩, rfl⟩, w - F y, ?_, ?_⟩
      · intro i
        cases i with
        | none => simp [w, F]
        | some p => simpa [w, F] using sub_nonneg.mpr (hcover p)
      · abel_nf
    have hs := hsep w hw
    rw [heval w, heval v] at hs
    simp [w, v, hz] at hs
  let z : κ → ℝ := fun p => coeff (some p) / coeff none
  have hz : ∀ p, 0 ≤ z p := fun p => div_nonneg (hcoeff _) hcostpos.le
  let y : ι → ℝ := fun i => if 1 < ∑ p, z p * M p i then 1 else 0
  have hy : y ∈ K := by constructor <;> intro i <;> dsimp [y] <;> split_ifs <;> norm_num
  have hFy : F y ∈ C := ⟨F y, ⟨y,hy,rfl⟩, 0, by simp, add_zero _⟩
  have hs := hsep _ hFy
  have hc (p : κ) : coeff (some p) = coeff none * z p := by
    dsimp [z]
    rw [mul_div_cancel₀ _ (ne_of_gt hcostpos)]
  have hdouble : (∑ p, z p * ∑ i, M p i * y i) = ∑ i, (∑ p, z p * M p i) * y i := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    ring
  have hmin : ∀ i, y i * (1 - ∑ p, z p * M p i) = -max ((∑ p, z p * M p i) - 1) 0 := by
    intro i
    dsimp [y]
    split_ifs with hi
    · rw [one_mul, max_eq_left (by linarith)]
      ring
    · rw [zero_mul, max_eq_right (by linarith), neg_zero]
  have hid : (∑ i, y i) + ∑ p, z p * (b p - ∑ i, M p i * y i) =
      (∑ p, z p * b p) - ∑ i, max ((∑ p, z p * M p i) - 1) 0 := by
    simp only [mul_sub, sum_sub_distrib]
    rw [hdouble]
    have h := congrArg (fun g : ι → ℝ => ∑ i, g i) (funext hmin)
    simp only [mul_sub, mul_one, sum_sub_distrib, sum_neg_distrib] at h
    have heq : (∑ i, y i * ∑ p, z p * M p i) = ∑ i, (∑ p, z p * M p i) * y i := by
      apply sum_congr rfl
      intro i hi
      ring
    rw [heq] at h
    linarith
  have hlv : l v = coeff none * r := by rw [heval]; simp [v]
  have hlF : l (F y) = coeff none * ((∑ i, y i) + ∑ p, z p * (b p - ∑ i, M p i * y i)) := by
    rw [heval, Fintype.sum_option]
    simp only [F, hc]
    rw [mul_add]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    ring
  refine ⟨z, hz, ?_⟩
  rw [hlv, hlF, hid] at hs
  nlinarith

/-- A dependent collection of columns has a nonzero direction preserving every row. -/
lemma kernel_direction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ v : ι → ℝ, (∀ p, ∑ i, M p i * v i = 0) ∧ (∃ i, v i ≠ 0) ∧ ∑ i, v i ≤ 0 := by
  classical
  have hdep : ¬ LinearIndependent ℝ (fun i p => M p i) := by
    intro h
    have hh := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hh
    omega
  obtain ⟨v, hv, hne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hrow : ∀ p, ∑ i, M p i * v i = 0 := by
    intro p
    have h := congrFun hv p
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using h
  by_cases hcost : ∑ i, v i ≤ 0
  · exact ⟨v, hrow, hne, hcost⟩
  · refine ⟨fun i => -v i, ?_, ?_, ?_⟩
    · intro p
      simp only [mul_neg, sum_neg_distrib, hrow, neg_zero]
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, neg_ne_zero.mpr hi⟩
    · rw [sum_neg_distrib]
      linarith

/-- Move inside a finite cube until a coordinate reaches its boundary. -/
lemma cube_step {ι : Type*} [Fintype ι] (y v : ι → ℝ)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hv : ∃ i, v i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ y i + t * v i ∧ y i + t * v i ≤ 1) ∧
      ∃ i, y i + t * v i = 0 ∨ y i + t * v i = 1 := by
  classical
  let s : Finset ι := univ.filter (fun i => v i ≠ 0)
  let bound : ι → ℝ := fun i => if 0 < v i then (1-y i) / v i else -y i / v i
  have hs : s.Nonempty := by obtain ⟨i, hi⟩ := hv; exact ⟨i, by simp [s, hi]⟩
  have hbpos : ∀ i ∈ s, 0 < bound i := by
    intro i hi
    have hvi : v i ≠ 0 := (mem_filter.mp hi).2
    dsimp [bound]
    split_ifs with h
    · exact div_pos (by have := (hy i).2; linarith) h
    · exact div_pos_of_neg_of_neg (by have := (hy i).1; linarith) (lt_of_le_of_ne (le_of_not_gt h) hvi)
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image bound hs
  refine ⟨bound j, hbpos j hj, ?_, j, ?_⟩
  · intro i
    by_cases hi : v i = 0
    · simp only [hi, mul_zero, add_zero]
      exact ⟨(hy i).1.le, (hy i).2.le⟩
    have hji := hmin i (by simp [s, hi])
    have ht := (hbpos j hj).le
    by_cases hvi : 0 < v i
    · have hbound : bound j * v i ≤ 1-y i := (le_div_iff₀ hvi).mp (by simpa [bound, hvi] using hji)
      constructor
      · nlinarith [(hy i).1, mul_nonneg ht hvi.le]
      · linarith
    · have hneg : v i < 0 := lt_of_le_of_ne (le_of_not_gt hvi) hi
      have hbound : -y i ≤ bound j * v i := (le_div_iff_of_neg hneg).mp (by simpa [bound, hvi] using hji)
      constructor
      · linarith
      · nlinarith [(hy i).2, mul_nonpos_of_nonneg_of_nonpos ht hneg.le]
  · have hjv : v j ≠ 0 := (mem_filter.mp hj).2
    dsimp [bound]
    split_ifs with h
    · right
      rw [div_mul_cancel₀ _ hjv]
      ring
    · left
      rw [div_mul_cancel₀ _ hjv]
      ring

noncomputable def fractionalIndices {ι : Type*} [Fintype ι] (y : ι → ℝ) : Finset ι :=
  @Finset.filter ι (fun i => 0 < y i ∧ y i < 1) (Classical.decPred _) univ

lemma cube_reduce {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hcard : Fintype.card κ < (fractionalIndices y).card) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ p, ∑ i, M p i * z i = ∑ i, M p i * y i) ∧
      (∑ i, z i) ≤ ∑ i, y i ∧ (fractionalIndices z).card < (fractionalIndices y).card := by
  classical
  let F := fractionalIndices y
  have hF (i : ι) : i ∈ F ↔ 0 < y i ∧ y i < 1 := by simp [F, fractionalIndices]
  obtain ⟨v, hvrow, hvne, hvcost⟩ := kernel_direction (fun p (i : F) => M p i.val)
    (by simpa only [Fintype.card_coe] using hcard)
  obtain ⟨t, ht, hcube, j, hj⟩ := cube_step (fun i : F => y i.val) v
    (fun i => (hF i.val).mp i.property) hvne
  let v₀ : ι → ℝ := fun i => if h : i ∈ F then v ⟨i,h⟩ else 0
  let z : ι → ℝ := fun i => y i + t * v₀ i
  have hsum (c : ι → ℝ) : (∑ i, c i * v₀ i) = ∑ i : F, c i.val * v i := by
    simp only [v₀, mul_dite, mul_zero]
    exact (sum_attach_eq_sum_dite F (fun i => c i.val * v i)).symm
  have hrow : ∀ p, ∑ i, M p i * v₀ i = 0 := fun p => (hsum (M p)).trans (hvrow p)
  have hcost : ∑ i, v₀ i ≤ 0 := by
    have hh := hsum (fun _ => 1)
    simp only [one_mul] at hh
    exact hh ▸ hvcost
  have hzcube : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    by_cases hi : i ∈ F
    · simpa only [z, v₀, dite_eq_left hi] using hcube ⟨i,hi⟩
    · simpa only [z, v₀, dite_eq_right hi, mul_zero, add_zero] using hy i
  have hsub : fractionalIndices z ⊆ F := by
    intro i hi
    by_contra hn
    have hz : z i = y i := by simp [z, v₀, hn]
    have hzi : 0 < z i ∧ z i < 1 := by simpa [fractionalIndices] using hi
    exact hn ((hF i).mpr (hz ▸ hzi))
  have hjnot : j.val ∉ fractionalIndices z := by
    intro hjmem
    have hzj : 0 < y j.val + t * v j ∧ y j.val + t * v j < 1 := by
      simpa [fractionalIndices, z, v₀, j.property] using hjmem
    rcases hj with hj | hj <;> linarith
  refine ⟨z, hzcube, ?_, ?_, ?_⟩
  · intro p
    calc
      (∑ i, M p i * z i) = (∑ i, M p i * y i) + t * ∑ i, M p i * v₀ i := by
        simp only [z, mul_add, sum_add_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, M p i * y i := by rw [hrow, mul_zero, add_zero]
  · dsimp only [z]
    rw [sum_add_distrib, ← mul_sum]
    nlinarith
  · apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hjnot (h.symm ▸ j.property)⟩

lemma cube_round {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ p, ∑ i, M p i * z i = ∑ i, M p i * y i) ∧
      (∑ i, z i) ≤ ∑ i, y i ∧ (fractionalIndices z).card ≤ Fintype.card κ := by
  classical
  generalize hn : (fractionalIndices y).card = n
  induction n using Nat.strong_induction_on generalizing y with
  | ind n ih =>
    by_cases hsmall : (fractionalIndices y).card ≤ Fintype.card κ
    · exact ⟨y, hy, fun _ => rfl, le_rfl, hsmall⟩
    · obtain ⟨z, hz, hrow, hcost, hlt⟩ := cube_reduce M y hy (lt_of_not_ge hsmall)
      obtain ⟨w, hw, hwrow, hwcost, hwcard⟩ := ih (fractionalIndices z).card (by omega) z hz rfl
      exact ⟨w, hw, fun p => (hwrow p).trans (hrow p), hwcost.trans hcost, hwcard⟩

end ErdosSuranyi708
