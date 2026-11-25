module

public import conjectures.SplitMatroidFlags.Statement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [DecidableEq E] {B : Finset (Finset E)} {b t : Finset E}

/-- Exchange one element of the fixed basis for an element outside it. -/
def Swap (B : Finset (Finset E)) (b : Finset E) (i j : E) : Prop :=
  i ∈ b ∧ j ∉ b ∧ insert j (b.erase i) ∈ B

instance (B : Finset (Finset E)) (b : Finset E) (i j : E) : Decidable (Swap B b i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Match the elements of a basis to another basis by single exchanges. -/
structure Matches (B : Finset (Finset E)) (b t : Finset E) (f : E → E) : Prop where
  image_eq : b.image f = t
  injOn : Set.InjOn f b
  permitted : ∀ i ∈ b, f i = i ∨ Swap B b i (f i)

def HasMatches (B : Finset (Finset E)) (b : Finset E) : Prop :=
  ∀ t ∈ B, ∃ f, Matches B b t f

def weight (w : E → ℝ) (b : Finset E) := ∑ i ∈ b, w i

lemma Matches.sum_eq {f : E → E} (hf : Matches B b t f) {M : Type*} [AddCommMonoid M]
    (w : E → M) : ∑ j ∈ t, w j = ∑ i ∈ b, w (f i) := by
  rw [← hf.image_eq,sum_image hf.injOn]

lemma swap_diff {i j : E} (h : Swap B b i j) {M : Type*} [AddCommGroup M] (w : E → M) :
    (∑ k ∈ insert j (b.erase i), w k) - (∑ k ∈ b, w k) = w j - w i := by
  have hj : j ∉ b.erase i := fun hh => h.2.1 (mem_erase.mp hh).2
  rw [sum_insert hj, ← sum_erase_add b w h.1]
  abel

def Maximizes (B : Finset (Finset E)) (w : E → ℝ) (b : Finset E) : Prop :=
  b ∈ B ∧ ∀ t ∈ B, weight w t ≤ weight w b

lemma maximizes_iff {w : E → ℝ} (hb : b ∈ B) (hm : HasMatches B b) :
    Maximizes B w b ↔ ∀ i j, Swap B b i j → w j ≤ w i := by
  constructor
  · intro hb i j hs
    have le := hb.2 _ hs.2.2
    have eq := swap_diff hs w
    unfold weight at le
    linarith
  · refine fun h => ⟨hb,fun t ht => ?_⟩
    obtain ⟨f,hf⟩ := hm t ht
    unfold weight
    rw [hf.sum_eq w]
    refine sum_le_sum fun i hi => ?_
    rcases hf.permitted i hi with e | hswap
    · rw [e]
    · exact h i _ hswap

lemma Matches.equal_iff {w : E → ℝ} {f : E → E} (hf : Matches B b t f)
    (loc : ∀ i j, Swap B b i j → w j ≤ w i) :
    weight w t = weight w b ↔ ∀ i ∈ b, w (f i) = w i := by
  unfold weight
  rw [hf.sum_eq w]
  refine sum_eq_sum_iff_of_le ?_
  intro i hi
  rcases hf.permitted i hi with e | hs
  · rw [e]
  · exact loc _ _ hs

/-- The exchanges on which a supporting weight is constant. -/
def tight (B : Finset (Finset E)) (b : Finset E) (w : E → ℝ) (i j : E) : Prop :=
  Swap B b i j ∧ w j = w i

noncomputable def exposed (B : Finset (Finset E)) (w : E → ℝ) : Finset (Finset E) := by
  classical exact B.filter (Maximizes B w)

omit [DecidableEq E] in
lemma mem_exposed {w : E → ℝ} : t ∈ exposed B w ↔ Maximizes B w t := by
  classical exact mem_filter.trans ⟨And.right,fun h => ⟨h.1,h⟩⟩

omit [DecidableEq E] in
lemma exposed_face {w : E → ℝ} (h : Maximizes B w b) : IsFace B (exposed B w) :=
  ⟨⟨b,mem_exposed.mpr h⟩,w,fun _ => mem_exposed⟩

omit [DecidableEq E] in
lemma face_eq_exposed {F : Finset (Finset E)} (hF : IsFace B F) :
    ∃ w, F = exposed B w := by
  obtain ⟨_,w,hw⟩ := hF
  exact ⟨w,Finset.ext fun a => (hw a).trans mem_exposed.symm⟩

omit [DecidableEq E] in
lemma mem_exposed_iff_eq {w : E → ℝ} (hb : Maximizes B w b) :
    t ∈ exposed B w ↔ t ∈ B ∧ weight w t = weight w b := by
  rw [mem_exposed]
  constructor
  · exact fun h => ⟨h.1,(hb.2 _ h.1).antisymm (h.2 _ hb.1)⟩
  · exact fun ⟨ht,he⟩ => ⟨ht,he.symm ▸ hb.2⟩

lemma swap_mem_exposed {w : E → ℝ} (hb : Maximizes B w b) {i j : E} (hs : Swap B b i j) :
    insert j (b.erase i) ∈ exposed B w ↔ w j = w i := by
  rw [mem_exposed_iff_eq hb,and_iff_right hs.2.2]
  have h := swap_diff hs w
  unfold weight
  constructor <;> intro he <;> linarith

lemma exposed_eq_iff {v w : E → ℝ} (hm : HasMatches B b) (hv : Maximizes B v b) (hw : Maximizes B w b) :
    exposed B v = exposed B w ↔ ∀ i j, tight B b v i j ↔ tight B b w i j := by
  constructor
  · intro eq i j
    constructor
    · rintro ⟨hs,he⟩
      exact ⟨hs,(swap_mem_exposed hw hs).mp (eq ▸ (swap_mem_exposed hv hs).mpr he)⟩
    · rintro ⟨hs,he⟩
      exact ⟨hs,(swap_mem_exposed hv hs).mp (eq.symm ▸ (swap_mem_exposed hw hs).mpr he)⟩
  · intro he
    classical
    ext t
    rw [mem_exposed_iff_eq hv,mem_exposed_iff_eq hw,and_congr_right_iff]
    intro ht
    obtain ⟨f,hf⟩ := hm t ht
    rw [hf.equal_iff ((maximizes_iff hv.1 hm).mp hv),
      hf.equal_iff ((maximizes_iff hw.1 hm).mp hw)]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rcases hf.permitted i hi with h | hs
    · simp [h]
    · simpa [tight,hs] using he i (f i)

def edgeSpan (B : Finset (Finset E)) (b : Finset E) (w : E → ℝ) :=
  Submodule.span ℝ {u | ∃ i j, tight B b w i j ∧ u = unit j - unit i}

lemma direction_space {w : E → ℝ} (hm : HasMatches B b) (hb : Maximizes B w b) :
    vectorSpan ℝ (vertex '' ((exposed B w : Finset (Finset E)) : Set (Finset E))) = edgeSpan B b w := by
  refine le_antisymm ?_ ?_
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    have into (t) (ht : t ∈ exposed B w) : vertex t - vertex b ∈ edgeSpan B b w := by
      obtain ⟨tb,eq⟩ := (mem_exposed_iff_eq hb).mp ht
      obtain ⟨f,hf⟩ := hm t tb
      have wEq := (hf.equal_iff ((maximizes_iff hb.1 hm).mp hb)).mp eq
      rw [vertex,vertex,hf.sum_eq unit,← sum_sub_distrib]
      apply Submodule.sum_mem
      intro i hi
      rcases hf.permitted i hi with h | hs
      · simp [h]
      · exact Submodule.subset_span ⟨i,f i,⟨hs,wEq i hi⟩,rfl⟩
    rintro _ ⟨_,⟨t,ht,rfl⟩,_,⟨s,hs,rfl⟩,rfl⟩
    have h := (edgeSpan B b w).sub_mem (into t ht) (into s hs)
    change vertex t - vertex s ∈ edgeSpan B b w
    rwa [sub_sub_sub_cancel_right] at h
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,j,⟨hs,he⟩,rfl⟩
    rw [← swap_diff hs unit]
    exact vsub_mem_vectorSpan ℝ ⟨_,(swap_mem_exposed hb hs).mpr he,rfl⟩ ⟨b,mem_exposed.mpr hb,rfl⟩

end SplitMatroidFlags
