module

public import conjectures.PermutationPeaks.ReflectedRecurrence

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace PeakPolynomials
open Finset

def maxPeak (S : Finset ℕ) : ℕ := S.sup id

theorem le_maxPeak {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) : i ≤ maxPeak S :=
  le_sup (f:=id) hi

theorem maxPeak_mem {S : Finset ℕ} (hS : S.Nonempty) : maxPeak S ∈ S := by
  have h := sup_mem_of_nonempty (f:=id) hS
  change S.sup id ∈ (S : Set ℕ)
  simpa only [Finset.coe_image,Set.image_id] using h

theorem admissible_subset {S T : Finset ℕ} (hS : Admissible S) (hT : T ⊆ S) :
    Admissible T := by
  constructor
  · intro i hi
    exact hS.1 i (hT hi)
  · intro i hi hj
    exact hS.2 i (hT hi) (hT hj)

theorem last_peak_reduction {S : Finset ℕ} (hS : Admissible S) (hne : S.Nonempty) :
    2 ≤ maxPeak S ∧
    Admissible (S.erase (maxPeak S)) ∧
    (∀ i ∈ S.erase (maxPeak S), 2 ≤ i ∧ i<maxPeak S-1) ∧
    insert (maxPeak S) (S.erase (maxPeak S))=S ∧
    (S.erase (maxPeak S)).card+1=S.card := by
  have hm := maxPeak_mem hne
  have hm2 := hS.1 (maxPeak S) hm
  refine ⟨hm2,admissible_subset hS (erase_subset _ _),?_,insert_erase hm,?_⟩
  · intro i hi
    obtain ⟨hne,him⟩ := mem_erase.mp hi
    have hib := le_maxPeak him
    have hnonadj := hS.2 i him
    have hgap : i+1≠maxPeak S := by intro he; exact hnonadj (he.symm ▸ hm)
    exact ⟨hS.1 i him,by omega⟩
  · exact card_erase_add_one hm

theorem last_reductions_smaller {S : Finset ℕ} (hS : Admissible S) (hne : S.Nonempty) :
    maxPeak (S.erase (maxPeak S)) < maxPeak S ∧
    maxPeak (insert (maxPeak S-1) (S.erase (maxPeak S))) < maxPeak S := by
  have hd := last_peak_reduction hS hne
  have he : maxPeak (S.erase (maxPeak S)) ≤ maxPeak S-2 := by
    apply Finset.sup_le
    intro i hi
    have := (hd.2.2.1 i hi).2
    change i ≤ maxPeak S-2
    omega
  constructor
  · omega
  · unfold maxPeak at *
    rw [sup_insert]
    change max (S.sup id-1) ((S.erase (S.sup id)).sup id) < S.sup id
    exact max_lt (by omega) (by omega)

end PeakPolynomials
namespace PeakPolynomials
open Finset

noncomputable def peakScale (n r : ℕ) : ℝ := (2 : ℝ)^((n : ℤ)-r-1)

theorem peakScale_ne_zero (n r : ℕ) : peakScale n r ≠ 0 :=
  zpow_ne_zero _ (by norm_num)

theorem peakScale_card_succ (n r : ℕ) : peakScale n r=2*peakScale n (r+1) := by
  unfold peakScale
  have he : (n : ℤ)-r-1=((n : ℤ)-(r+1)-1)+1 := by ring
  push_cast
  rw [he,zpow_add_one₀ (by norm_num : (2 : ℝ)≠0)]
  ring

theorem peakScale_split (a b r : ℕ) (hb : 0<b) :
    peakScale a r * (2 : ℝ)^(b-1)=peakScale (a+b) (r+1) := by
  unfold peakScale
  have he : ((a : ℤ)-r-1)+((b-1 : ℕ) : ℤ)=((a+b : ℕ) : ℤ)-(r+1 : ℕ)-1 := by
    omega
  rw [← zpow_natCast,← zpow_add₀ (by norm_num : (2 : ℝ)≠0),he]

noncomputable def normalizedPeakCount (n : ℕ) (S : Finset ℕ) : ℝ :=
  (peakCount n S : ℝ)/peakScale n S.card

theorem peakCount_eq_scaled (n : ℕ) (S : Finset ℕ) :
    (peakCount n S : ℝ)=peakScale n S.card * normalizedPeakCount n S := by
  unfold normalizedPeakCount
  field_simp [peakScale_ne_zero]

theorem normalized_empty (n : ℕ) (hn : 0<n) : normalizedPeakCount n ∅=1 := by
  unfold normalizedPeakCount peakScale
  rw [peakCount_empty_positive n hn,card_empty]
  simp only [Nat.cast_zero]
  have he : (n : ℤ)-0-1=((n-1 : ℕ) : ℤ) := by omega
  rw [he,zpow_natCast]
  push_cast
  exact div_self (pow_ne_zero _ (by norm_num))

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem normalized_block_recurrence (a b : ℕ) (hb : 0<b) (T : Finset ℕ)
    (hT : ∀ i ∈ T, 2 ≤ i ∧ i<a) :
    normalizedPeakCount (a+b) (insert a T) + normalizedPeakCount (a+b) (insert (a+1) T) =
      ((a+b).choose a : ℝ)*normalizedPeakCount a T - 2*normalizedPeakCount (a+b) T := by
  have ha : a ∉ T := by intro h; have := (hT a h).2; omega
  have ha1 : a+1 ∉ T := by intro h; have := (hT (a+1) h).2; omega
  have hc := congrArg (fun x : ℕ => (x : ℝ))
    (literal_block_recurrence_with_empty_count a b hb T hT)
  push_cast at hc
  rw [peakCount_eq_scaled (a+b) T,peakCount_eq_scaled (a+b) (insert a T),
    peakCount_eq_scaled (a+b) (insert (a+1) T),peakCount_eq_scaled a T,
    card_insert_of_notMem ha,card_insert_of_notMem ha1,peakScale_card_succ (a+b) T.card] at hc
  have hs := peakScale_split a b T.card hb
  have he : ((a+b).choose a : ℝ)*(peakScale a T.card*normalizedPeakCount a T)*2^(b-1) =
      peakScale (a+b) (T.card+1)*(((a+b).choose a : ℝ)*normalizedPeakCount a T) := by
    rw [← hs]
    ring
  rw [he] at hc
  have hnz := peakScale_ne_zero (a+b) (T.card+1)
  apply (mul_left_cancel₀ hnz)
  nlinarith [hc]

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset

noncomputable def peakPolynomial (S : Finset ℕ) : Polynomial ℝ := by
  classical
  exact if hS : Admissible S then
    if hne : S.Nonempty then
      C ((peakPolynomial (S.erase (maxPeak S))).eval ((maxPeak S-1 : ℕ) : ℝ)) *
        ReflectedNewton.choosePolynomial (maxPeak S) -
        C 2 * peakPolynomial (S.erase (maxPeak S)) -
        peakPolynomial (insert (maxPeak S-1) (S.erase (maxPeak S)))
    else 1
  else 0
termination_by maxPeak S
decreasing_by
  all_goals first
    | exact (last_reductions_smaller hS hne).1
    | exact (last_reductions_smaller hS hne).2

theorem peakPolynomial_inadmissible (S : Finset ℕ) (hS : ¬ Admissible S) :
    peakPolynomial S=0 := by
  rw [peakPolynomial]
  simp only [dite_eq_right hS]

theorem peakPolynomial_empty : peakPolynomial ∅=1 := by
  rw [peakPolynomial]
  have h : Admissible ∅ := by simp [Admissible]
  simp [h]

theorem peakPolynomial_recurrence (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    peakPolynomial S =
      C ((peakPolynomial (S.erase (maxPeak S))).eval ((maxPeak S-1 : ℕ) : ℝ)) *
        ReflectedNewton.choosePolynomial (maxPeak S) -
        C 2 * peakPolynomial (S.erase (maxPeak S)) -
        peakPolynomial (insert (maxPeak S-1) (S.erase (maxPeak S))) := by
  rw [peakPolynomial]
  simp only [dite_eq_left hS,dite_eq_left hne]

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset

theorem peakPolynomial_normalized_count (S : Finset ℕ) (n : ℕ) (hn : maxPeak S<n) :
    (peakPolynomial S).eval (n : ℝ)=normalizedPeakCount n S := by
  suffices hall : ∀ m : ℕ, ∀ S : Finset ℕ, maxPeak S=m → ∀ n : ℕ, m<n →
      (peakPolynomial S).eval (n : ℝ)=normalizedPeakCount n S from hall _ S rfl n hn
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro S hm n hn
    classical
    by_cases hS : Admissible S
    · by_cases hne : S.Nonempty
      · have hd := last_peak_reduction hS hne
        have hsmall := last_reductions_smaller hS hne
        let T := S.erase (maxPeak S)
        let a := maxPeak S-1
        have ha : 0<a := by dsimp [a]; omega
        have hTa : maxPeak T<a := by
          have hb : maxPeak T ≤ maxPeak S-2 := by
            apply Finset.sup_le
            intro i hi
            have := (hd.2.2.1 i hi).2
            change i ≤ maxPeak S-2
            omega
          dsimp [a]
          omega
        have hTs : maxPeak T<m := hsmall.1.trans_le hm.le
        have hQs : maxPeak (insert a T)<m := by simpa only [a,T,hm] using hsmall.2
        have hTn := ih (maxPeak T) hTs T rfl n (by omega)
        have hTan := ih (maxPeak T) hTs T rfl a hTa
        have hQn := ih (maxPeak (insert a T)) hQs (insert a T) rfl n (by omega)
        have hab : a+(n-a)=n := by dsimp [a]; omega
        have hapos : 0<n-a := by dsimp [a]; omega
        have ham : a+1=maxPeak S := by dsimp [a]; omega
        have hr := normalized_block_recurrence a (n-a) hapos T hd.2.2.1
        rw [hab,ham,hd.2.2.2.1] at hr
        rw [peakPolynomial_recurrence S hS hne]
        simp only [eval_sub,eval_mul,eval_C]
        rw [ReflectedNewton.choosePolynomial_eval _ (by omega),Ring.choose_natCast]
        change (peakPolynomial T).eval (a : ℝ)*((n.choose a : ℕ) : ℝ) -
          2*(peakPolynomial T).eval (n : ℝ) - (peakPolynomial (insert a T)).eval (n : ℝ) = _
        rw [hTan,hTn,hQn]
        linarith [hr]
      · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
        subst S
        rw [peakPolynomial_empty,eval_one,normalized_empty n (by omega)]
    · rw [peakPolynomial_inadmissible S hS,eval_zero]
      simp [normalizedPeakCount,inadmissible_peakCount n S hS]

theorem peakPolynomial_literal_count (S : Finset ℕ) (n : ℕ) (hn : maxPeak S<n) :
    (peakCount n S : ℝ)=peakScale n S.card * (peakPolynomial S).eval (n : ℝ) := by
  rw [peakPolynomial_normalized_count S n hn]
  exact peakCount_eq_scaled n S

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset

theorem normalized_count_at_max (S : Finset ℕ) (hne : S.Nonempty) :
    normalizedPeakCount (maxPeak S) S=0 := by
  simp [normalizedPeakCount,peakCount_zero_of_large_member (maxPeak S) S (maxPeak_mem hne) le_rfl]

theorem peakPolynomial_root (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    (peakPolynomial S).eval (maxPeak S : ℝ)=0 := by
  have hd := last_peak_reduction hS hne
  have hsmall := last_reductions_smaller hS hne
  let m := maxPeak S
  let T := S.erase m
  let a := m-1
  have ha : 0<a := by dsimp [a,m]; omega
  have hTa : maxPeak T<a := by
    have hb : maxPeak T ≤ m-2 := by
      apply Finset.sup_le
      intro i hi
      have := (hd.2.2.1 i hi).2
      change i ≤ m-2
      dsimp [m] at *
      omega
    dsimp [a]
    omega
  have hTn := peakPolynomial_normalized_count T m hsmall.1
  have hTan := peakPolynomial_normalized_count T a hTa
  have hQn := peakPolynomial_normalized_count (insert a T) m hsmall.2
  have ham : a+1=m := by dsimp [a,m]; omega
  have hr := normalized_block_recurrence a 1 (by omega) T hd.2.2.1
  rw [ham,hd.2.2.2.1,normalized_count_at_max S hne] at hr
  rw [peakPolynomial_recurrence S hS hne]
  simp only [eval_sub,eval_mul,eval_C]
  rw [ReflectedNewton.choosePolynomial_eval _ (by omega),Ring.choose_natCast]
  change (peakPolynomial T).eval (a : ℝ)*((m.choose a : ℕ) : ℝ) -
    2*(peakPolynomial T).eval (m : ℝ) - (peakPolynomial (insert a T)).eval (m : ℝ)=0
  rw [hTan,hTn,hQn]
  linarith [hr]

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset

theorem peakPolynomial_degree (S : Finset ℕ) :
    (peakPolynomial S).natDegree ≤ maxPeak S-1 := by
  suffices hall : ∀ m : ℕ, ∀ S : Finset ℕ, maxPeak S=m →
      (peakPolynomial S).natDegree ≤ m-1 from hall _ S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro S hm
    classical
    by_cases hS : Admissible S
    · by_cases hne : S.Nonempty
      · have hs := last_reductions_smaller hS hne
        have hT := ih _ (hs.1.trans_le hm.le) _ rfl
        have hQ := ih _ (hs.2.trans_le hm.le) _ rfl
        have hdT : (peakPolynomial (S.erase (maxPeak S))).natDegree ≤ m-1 := by omega
        have hdQ : (peakPolynomial (insert (maxPeak S-1) (S.erase (maxPeak S)))).natDegree ≤ m-1 := by omega
        rw [peakPolynomial_recurrence S hS hne]
        apply (natDegree_sub_le _ _).trans
        apply max_le
        · apply (natDegree_sub_le _ _).trans
          apply max_le
          · exact (natDegree_C_mul_le _ _).trans (by simpa only [hm] using ReflectedNewton.choosePolynomial_degree (maxPeak S))
          · exact (natDegree_C_mul_le _ _).trans hdT
        · exact hdQ
      · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
        subst S
        rw [peakPolynomial_empty]
        simp
    · rw [peakPolynomial_inadmissible S hS]
      simp

theorem admissible_card_bound (S : Finset ℕ) (hS : Admissible S) :
    S.card ≤ maxPeak S-1 := by
  have hs : S ⊆ Icc 2 (maxPeak S) := by
    intro i hi
    exact mem_Icc.mpr ⟨hS.1 i hi,le_maxPeak hi⟩
  have hc := card_le_card hs
  simp only [Nat.card_Icc] at hc
  omega

theorem peakPolynomial_original_normalization (S : Finset ℕ) (hS : Admissible S)
    (n : ℕ) (hn : maxPeak S<n) :
    (peakCount n S : ℝ)=(2 : ℝ)^(n-S.card-1)*(peakPolynomial S).eval (n : ℝ) := by
  have hc := admissible_card_bound S hS
  have he : (n : ℤ)-S.card-1=((n-S.card-1 : ℕ) : ℤ) := by omega
  rw [peakPolynomial_literal_count S n hn]
  unfold peakScale
  rw [he,zpow_natCast]

end PeakPolynomials
namespace ReflectedNewton
open Finset Polynomial

theorem reflectedLift_zero_iff_coefficients (P : Polynomial ℝ) (m : ℕ) :
    reflectedLift P m=0 ↔ ∀ k, k < m-1 → reflectedCoefficient P m k=0 := by
  constructor
  · intro hz k hk
    have h := reflectedLift_coefficient P m k hk
    rw [hz] at h
    have heval : (0 : Polynomial ℝ).eval=fun _ => 0 := by funext x; simp
    rw [heval,backward_const] at h
    exact h.symm
  · intro h
    unfold reflectedLift
    apply sum_eq_zero
    intro k hk
    rw [h k (mem_range.mp hk),C_0,zero_mul]

theorem next_lift_first_coefficient (P : Polynomial ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hP : P.natDegree ≤ r-1) : reflectedCoefficient P (r+1) 0=P.eval (r : ℝ) := by
  unfold reflectedCoefficient
  simp only [Nat.add_sub_cancel,Nat.sub_zero,Nat.zero_add,Nat.cast_add,Nat.cast_one]
  rw [backward_polynomial_vanish P (n := r) (by omega)]
  simp only [backward,sub_zero,add_sub_cancel_right]
  ring

theorem next_lift_coefficient_difference (P : Polynomial ℝ) (r k : ℕ)
    (_hr : 2 ≤ r) (hk : k+1 < r) :
    reflectedCoefficient P (r+1) (k+1)-reflectedCoefficient P (r+1) k=
      backward P.eval (k+1) (r : ℝ)-backward P.eval (r-1-k) (r : ℝ) := by
  have h1 := backward_step P.eval (k+1) (r : ℝ)
  have h2 := backward_step P.eval (r-1-k) (r : ℝ)
  have heq : r-1-k+1=r-k := by omega
  have heq2 : r-(k+1)=r-1-k := by omega
  rw [heq] at h2
  simp only [reflectedCoefficient,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,heq2]
  linarith

theorem next_lift_zero_boundary (P : Polynomial ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hP : P.natDegree ≤ r-1) :
    reflectedLift P (r+1)=0 ↔ P.eval (r : ℝ)=0 ∧
      ∀ j, 1 ≤ j → j ≤ r-1 → backward P.eval j (r : ℝ)=backward P.eval (r-j) (r : ℝ) := by
  rw [reflectedLift_zero_iff_coefficients]
  constructor
  · intro hc
    have hfirst := hc 0 (by omega)
    rw [next_lift_first_coefficient P r hr hP] at hfirst
    refine ⟨hfirst,?_⟩
    intro j hj hj'
    have hk : j-1+1 < r := by omega
    have hdiff := next_lift_coefficient_difference P r (j-1) hr hk
    rw [hc (j-1+1) (by omega),hc (j-1) (by omega)] at hdiff
    have h1 : j-1+1=j := by omega
    have h2 : r-1-(j-1)=r-j := by omega
    rw [h1,h2] at hdiff
    linarith
  · rintro ⟨hroot,hsym⟩ k hk
    induction k with
    | zero => rw [next_lift_first_coefficient P r hr hP,hroot]
    | succ k ih =>
      have hprev := ih (by omega)
      have hd := next_lift_coefficient_difference P r k hr (by omega)
      have hsym' := hsym (k+1) (by omega) (by omega)
      have hidx : r-(k+1)=r-1-k := by omega
      rw [hidx] at hsym'
      linarith

end ReflectedNewton
namespace ReflectedNewton
open Polynomial

theorem adjoining_lift_vanishes (P : Polynomial ℝ) (r : ℕ) (hr : 2 ≤ r) :
    reflectedLift (reflectedLift P r) (r+1)=0 := by
  apply (next_lift_zero_boundary (reflectedLift P r) r hr (reflectedLift_degree P r)).mpr
  refine ⟨reflectedLift_at_center P r,?_⟩
  intro j hj hjr
  have hj1 : j-1+1=j := by omega
  have hj2 : r-j-1+1=r-j := by omega
  have h1 := reflectedLift_coefficient P r (j-1) (by omega)
  have h2 := reflectedLift_coefficient P r (r-j-1) (by omega)
  rw [hj1] at h1
  rw [hj2] at h2
  rw [h1,h2]
  have hs := reflectedCoefficient_symmetry P r (j-1) hr (by omega)
  have he : r-2-(j-1)=r-j-1 := by omega
  simpa only [he] using hs

theorem constant_lift_order_two :
    reflectedLift (1 : Polynomial ℝ) 2 = choosePolynomial 2-C 2 := by
  apply Polynomial.funext
  intro x
  have hv := congrFun (reflectedLift_eval (1 : Polynomial ℝ) 2) x
  rw [hv,eval_sub,choosePolynomial_eval 2 (by omega),eval_C]
  simp [reflectedCoefficient,backward,rising,Ring.choose]

end ReflectedNewton
namespace PeakPolynomials
open Finset Polynomial

theorem admissible_insert_above (T : Finset ℕ) (hT : Admissible T) (m : ℕ)
    (hm : 2 ≤ m) (hb : ∀ i ∈ T, i+1<m) : Admissible (insert m T) := by
  constructor
  · intro i hi
    rcases mem_insert.mp hi with rfl | ht
    · exact hm
    · exact hT.1 i ht
  · intro i hi hj
    rcases mem_insert.mp hi with rfl | ht
    · rcases mem_insert.mp hj with he | hj
      · omega
      · have := hb _ hj; omega
    · rcases mem_insert.mp hj with he | hj
      · have := hb i ht; omega
      · exact hT.2 i ht hj

theorem maxPeak_insert_above (T : Finset ℕ) (m : ℕ) (hb : ∀ i ∈ T, i ≤ m) :
    maxPeak (insert m T)=m := by
  have hle : maxPeak T ≤ m := Finset.sup_le hb
  unfold maxPeak at *
  rw [sup_insert]
  exact max_eq_left hle

theorem erase_insert_above (T : Finset ℕ) (m : ℕ) (hb : ∀ i ∈ T, i<m) :
    (insert m T).erase m=T := by
  have hm : m ∉ T := by intro h; have := hb m h; omega
  simp [hm]

theorem adjacent_insert_inadmissible (T : Finset ℕ) (r : ℕ) (hr : r ∈ T) :
    ¬ Admissible (insert (r+1) T) := by
  intro h
  exact h.2 r (mem_insert_of_mem hr) (mem_insert_self _ _)

theorem peakPolynomial_insert_recurrence (T : Finset ℕ) (hT : Admissible T) (m : ℕ)
    (hm : 2 ≤ m) (hb : ∀ i ∈ T, i+1<m) :
    peakPolynomial (insert m T)=
      C ((peakPolynomial T).eval ((m-1 : ℕ) : ℝ))*ReflectedNewton.choosePolynomial m -
        C 2*peakPolynomial T-peakPolynomial (insert (m-1) T) := by
  have hS := admissible_insert_above T hT m hm hb
  have hmax := maxPeak_insert_above T m (fun i hi => by have := hb i hi; omega)
  have herase := erase_insert_above T m (fun i hi => by have := hb i hi; omega)
  rw [peakPolynomial_recurrence _ hS (insert_nonempty _ _),hmax,herase]

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset ReflectedNewton

theorem peakPolynomial_reflected_extension (m : ℕ) (hm : 2 ≤ m)
    (T : Finset ℕ) (hT : Admissible T) (hb : ∀ i ∈ T, i+1<m) :
    peakPolynomial (insert m T)=reflectedLift (peakPolynomial T) m := by
  suffices hall : ∀ m : ℕ, 2 ≤ m → ∀ T : Finset ℕ, Admissible T →
      (∀ i ∈ T, i+1<m) → peakPolynomial (insert m T)=reflectedLift (peakPolynomial T) m from
    hall m hm T hT hb
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm T hT hb
    classical
    by_cases hm2 : m=2
    · subst m
      have he : T=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        have := hT.1 i hi
        have := hb i hi
        omega
      subst T
      rw [peakPolynomial_insert_recurrence _ hT 2 hm hb,peakPolynomial_empty]
      have hbad : ¬ Admissible (insert 1 (∅ : Finset ℕ)) := by
        intro h
        have := h.1 1 (by simp)
        omega
      rw [peakPolynomial_inadmissible _ hbad,constant_lift_order_two]
      simp
    · have hm3 : 3 ≤ m := by omega
      have hmax : maxPeak T ≤ m-2 := by
        apply Finset.sup_le
        intro i hi
        have := hb i hi
        change i ≤ m-2
        omega
      have hdegree : (peakPolynomial T).natDegree ≤ m-3 := by
        have := peakPolynomial_degree T
        omega
      have hprev : peakPolynomial (insert (m-1) T)=reflectedLift (peakPolynomial T) (m-1) := by
        by_cases hgap : ∀ i ∈ T, i+1<m-1
        · exact ih (m-1) (by omega) (by omega) T hT hgap
        · push Not at hgap
          obtain ⟨r,hr,hrgap⟩ := hgap
          have hrbound := hb r hr
          have hr2 := hT.1 r hr
          have hre : r=m-2 := by omega
          have hrmax : maxPeak T=r := by have := le_maxPeak hr; omega
          have hne : T.Nonempty := ⟨r,hr⟩
          have hd := last_peak_reduction hT hne
          have hsmall : r<m := by omega
          have hsub := ih r hsmall hr2 (T.erase r)
            (admissible_subset hT (erase_subset _ _)) (by
              intro i hi
              have hh := hd.2.2.1 i (by simpa only [hrmax] using hi)
              rw [hrmax] at hh
              omega)
          rw [insert_erase hr] at hsub
          have hrnext : r+1=m-1 := by omega
          have hbad : ¬ Admissible (insert (m-1) T) := by
            rw [← hrnext]
            exact adjacent_insert_inadmissible T r hr
          rw [peakPolynomial_inadmissible _ hbad,hsub,← hrnext,adjoining_lift_vanishes _ r hr2]
      rw [peakPolynomial_insert_recurrence T hT m hm hb,hprev]
      have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      rw [hcast,← reflected_lift_recurrence (peakPolynomial T) m hm3 hdegree]
      exact add_sub_cancel_right _ _

theorem peakPolynomial_reflected (S : Finset ℕ) (hS : Admissible S) (hne : S.Nonempty) :
    peakPolynomial S=reflectedLift (peakPolynomial (S.erase (maxPeak S))) (maxPeak S) := by
  have hd := last_peak_reduction hS hne
  have h := peakPolynomial_reflected_extension (maxPeak S) hd.1 (S.erase (maxPeak S)) hd.2.1
    (fun i hi => by have := (hd.2.2.1 i hi).2; omega)
  simpa only [hd.2.2.2.1] using h

end PeakPolynomials
namespace PeakPolynomials
open Polynomial Finset ReflectedNewton

theorem backward_one_nonnegative (j : ℕ) (x : ℝ) :
    0 ≤ backward (1 : Polynomial ℝ).eval j x := by
  cases j with
  | zero => simp
  | succ j =>
    rw [backward_polynomial_vanish (1 : Polynomial ℝ) (by simp) x]

theorem peak_backward_nonnegative (S : Finset ℕ) (hS : Admissible S)
    (u : ℕ) (hu : maxPeak S ≤ u) (j : ℕ) :
    0 ≤ backward (peakPolynomial S).eval j (u : ℝ) := by
  suffices hall : ∀ m : ℕ, ∀ S : Finset ℕ, maxPeak S=m → Admissible S →
      ∀ u : ℕ, m ≤ u → ∀ j : ℕ, 0 ≤ backward (peakPolynomial S).eval j (u : ℝ) from
    hall _ S rfl hS u hu j
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro S hm hS u hu j
    classical
    by_cases hne : S.Nonempty
    · have hd := last_peak_reduction hS hne
      let T := S.erase (maxPeak S)
      have hTs : maxPeak T<m := (last_reductions_smaller hS hne).1.trans_le hm.le
      have hTm : maxPeak T ≤ maxPeak S-2 := by
        apply Finset.sup_le
        intro i hi
        have := (hd.2.2.1 i hi).2
        change i ≤ maxPeak S-2
        omega
      have hD : ∀ v, 0 ≤ backward (peakPolynomial T).eval v ((maxPeak S : ℝ)-2) := by
        intro v
        have hv := ih _ hTs T rfl hd.2.1 (maxPeak S-2) hTm v
        have he : ((maxPeak S-2 : ℕ) : ℝ)=(maxPeak S : ℝ)-2 := by
          rw [Nat.cast_sub hd.1]
          norm_num
        simpa only [he] using hv
      have hdegT : (peakPolynomial T).natDegree ≤ maxPeak S-2 := by
        have := peakPolynomial_degree T
        omega
      have hcenter : ∀ v, 0 ≤ backward (peakPolynomial S).eval v (maxPeak S : ℝ) := by
        intro v
        by_cases hv0 : v=0
        · subst v
          rw [backward_zero,peakPolynomial_root S hS hne]
        · by_cases hv : v ≤ maxPeak S-1
          · rw [peakPolynomial_reflected S hS hne]
            have hval := reflectedLift_kernel (peakPolynomial T) (maxPeak S) (v-1) hd.1 (by omega) hdegT
            have he : v-1+1=v := by omega
            rw [he] at hval
            rw [hval]
            apply sum_nonneg
            intro q hq
            exact mul_nonneg (by exact_mod_cast kernel_nonneg (maxPeak S) ((v-1 : ℕ) : ℤ) q) (hD q)
          · rw [backward_polynomial_vanish (peakPolynomial S) (by have := peakPolynomial_degree S; omega)]
      have hh := backward_nonneg_shift (peakPolynomial S) (maxPeak S : ℝ) hcenter (u-maxPeak S) j
      have he : (maxPeak S : ℝ)+(u-maxPeak S : ℕ)=u := by
        rw [← Nat.cast_add]
        congr 1
        omega
      simpa only [he] using hh
    · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
      subst S
      rw [peakPolynomial_empty]
      exact backward_one_nonnegative j (u : ℝ)

end PeakPolynomials
namespace ReflectedNewton
open Finset

noncomputable def paddedCoefficient (P : Polynomial ℝ) (m : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k ≤ (m : ℤ)-2 then reflectedCoefficient P m k.toNat else 0

theorem kernel_outside (m j : ℕ) (k : ℤ) (hk : k < 0 ∨ (m : ℤ)-2 < k) :
    kernel m k j = 0 := by
  unfold kernel
  omega

theorem paddedCoefficient_kernel (P : Polynomial ℝ) (m : ℕ)
    (hm : 2 ≤ m) (hP : P.natDegree ≤ m-2) (k : ℤ) :
    paddedCoefficient P m k =
      ∑ j ∈ range (m-1), (kernel m k j : ℝ)*backward P.eval j ((m : ℝ)-2) := by
  by_cases hk : 0 ≤ k ∧ k ≤ (m : ℤ)-2
  · rw [paddedCoefficient, ite_eq_left hk,
      reflected_coefficient_kernel P m k.toNat hm (by omega) hP]
    have hcast : (k.toNat : ℤ)=k := by omega
    simp only [hcast]
  · rw [paddedCoefficient, ite_eq_right hk]
    symm
    apply sum_eq_zero
    intro j hj
    rw [kernel_outside m j k (by omega)]
    simp

theorem paddedCoefficient_curvature (P : Polynomial ℝ) (m : ℕ)
    (hm : 2 ≤ m) (hP : P.natDegree ≤ m-2) (k : ℤ)
    (hk : 0 ≤ k ∧ k ≤ (m : ℤ)-2) :
    2*paddedCoefficient P m k-paddedCoefficient P m (k-1)-paddedCoefficient P m (k+1) =
      backward P.eval k.toNat ((m : ℝ)-2) +
      backward P.eval ((m : ℤ)-2-k).toNat ((m : ℝ)-2) := by
  rw [paddedCoefficient_kernel P m hm hP k,
    paddedCoefficient_kernel P m hm hP (k-1), paddedCoefficient_kernel P m hm hP (k+1),
    mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  have hleft : k.toNat < m-1 := by omega
  have hright : ((m : ℤ)-2-k).toNat < m-1 := by omega
  calc
    (∑ j ∈ range (m-1),
      (2*((kernel m k j : ℝ)*backward P.eval j ((m : ℝ)-2)) -
      (kernel m (k-1) j : ℝ)*backward P.eval j ((m : ℝ)-2) -
      (kernel m (k+1) j : ℝ)*backward P.eval j ((m : ℝ)-2))) =
      ∑ j ∈ range (m-1),
      ((if j=k.toNat then (1 : ℝ) else 0) +
       (if j=((m : ℤ)-2-k).toNat then (1 : ℝ) else 0))*backward P.eval j ((m : ℝ)-2) := by
        apply sum_congr rfl
        intro j hj
        have hj' : 0 ≤ (j : ℤ) ∧ (j : ℤ) ≤ (m : ℤ)-2 := by
          have := mem_range.mp hj
          omega
        have hc := kernel_curvature (m := (m : ℤ)) (k := k) (j := (j : ℤ)) (by omega) hk hj'
        have he1 : (k=(j : ℤ)) ↔ j=k.toNat := by omega
        have he2 : (k=(m : ℤ)-2-(j : ℤ)) ↔ j=((m : ℤ)-2-k).toNat := by omega
        simp only [he1, he2] at hc
        have hreal : 2*(kernel m k j : ℝ)-(kernel m (k-1) j : ℝ)-(kernel m (k+1) j : ℝ) =
          (if j=k.toNat then 1 else 0)+(if j=((m : ℤ)-2-k).toNat then 1 else 0) := by
          exact_mod_cast hc
        rw [← mul_assoc, ← sub_mul, ← sub_mul, hreal]
    _ = _ := by simp [add_mul, sum_add_distrib, ite_mul, hleft, hright]

theorem paddedCoefficient_concave (P : Polynomial ℝ) (m : ℕ)
    (hm : 2 ≤ m) (hP : P.natDegree ≤ m-2)
    (hdata : ∀ j, 0 ≤ backward P.eval j ((m : ℝ)-2)) (k : ℤ)
    (hk : 0 ≤ k ∧ k ≤ (m : ℤ)-2) :
    paddedCoefficient P m (k-1)+paddedCoefficient P m (k+1) ≤ 2*paddedCoefficient P m k := by
  have hc := paddedCoefficient_curvature P m hm hP k hk
  have h1 := hdata k.toNat
  have h2 := hdata ((m : ℤ)-2-k).toNat
  linarith

end ReflectedNewton

end PermutationPeaks
