module

public import conjectures.FerroniFacePrefix.RankTwo
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

@[expose] public section

namespace FerroniFacePrefix

open Finset

variable {E C : Type} [DecidableEq E] [DecidableEq C]

private noncomputable def starSpan (A : Finset E) (anchor : E → E) :=
  Submodule.span ℝ (Set.range fun i : A => unit (i : E) - unit (anchor i))

private lemma star_mem {A : Finset E} {anchor : E → E} {i : E} (hi : i ∈ A) :
    unit i - unit (anchor i) ∈ starSpan A anchor :=
  Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩

private lemma star_rank {A : Finset E} {anchor : E → E} (ha : ∀ i ∈ A, anchor i ∉ A) :
    Module.finrank ℝ (starSpan A anchor) = A.card := by
  have hlin : LinearIndependent ℝ (fun i : A => unit (i : E) - unit (anchor i)) := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro w he i
    have entry (j : A) : (unit (j : E) - unit (anchor j)) i = if j = i then 1 else 0 := by
      have hn : anchor j ≠ i := fun e => ha j j.property (e ▸ i.property)
      by_cases h : j = i
      · subst j
        simp [unit,hn]
      · have ne : (j : E) ≠ i := fun h' => h (Subtype.ext h')
        simp [unit,hn,ne,h]
    have hh := congrFun he (i : E)
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hh
    simpa [entry] using hh
  unfold starSpan
  exact (finrank_span_eq_card hlin).trans (Fintype.card_coe A)

private lemma geometric_star {F : Finset (Finset E)} {A : Finset E} {anchor : E → E}
    (hA : ∀ i ∈ A, anchor i ∉ A) (origin : E → ℝ)
    (upper : ∀ b ∈ F, vertex b - origin ∈ starSpan A anchor)
    (lower : ∀ i ∈ A, ∃ b ∈ F, ∃ c ∈ F, vertex b - vertex c = unit i - unit (anchor i)) :
    faceDimension F = A.card := by
  have eq : vectorSpan ℝ (vertex '' (F : Set (Finset E))) = starSpan A anchor := by
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨_,⟨b,hb,rfl⟩,_,⟨c,hc,rfl⟩,rfl⟩
      change vertex b - vertex c ∈ starSpan A anchor
      have h := (starSpan A anchor).sub_mem (upper b hb) (upper c hc)
      rwa [sub_sub_sub_cancel_right] at h
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      obtain ⟨b,hb,c,hc,he⟩ := lower i i.property
      change unit (i : E) - unit (anchor i) ∈ vectorSpan ℝ (vertex '' (F : Set (Finset E)))
      rw [← he]
      exact vsub_mem_vectorSpan ℝ ⟨b,hb,rfl⟩ ⟨c,hc,rfl⟩
  rw [faceDimension,eq,star_rank hA]

private lemma vertex_pair {x y : E} (h : x ≠ y) : vertex {x,y} = unit x + unit y := by simp [vertex,h]

omit [DecidableEq E] in
lemma third_color {col : E → C} {U : Finset E} (h : 3 ≤ (U.image col).card) (a b : C) :
    ∃ k ∈ U, col k ≠ a ∧ col k ≠ b := by
  by_contra! hno
  have hs : U.image col ⊆ {a,b} := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
    simp only [mem_insert, mem_singleton]
    by_cases ha : col k = a
    · exact Or.inl ha
    · exact Or.inr (hno k hk ha)
  have hc := card_le_card hs
  have htwo : ({a,b} : Finset C).card ≤ 2 := by
    by_cases hab : a = b <;> simp [hab]
  omega

lemma support_wide {col : E → C} {U : Finset E} (h : 3 ≤ (U.image col).card) :
    (bases col U).biUnion id = U := by
  ext i
  constructor
  · intro hi
    obtain ⟨b,hb,hib⟩ := mem_biUnion.mp hi
    exact (mem_powersetCard.mp (mem_filter.mp hb).1).1 hib
  · intro hi
    obtain ⟨k,hk,hneq,_⟩ := third_color h (col i) (col i)
    exact mem_biUnion.mpr ⟨{i,k}, pair_mem.mpr ⟨hi,hk,hneq.symm⟩, by simp⟩

lemma dimension_wide {col : E → C} {U : Finset E} (h : 3 ≤ (U.image col).card) :
    faceDimension (bases col U) = U.card - 1 := by
  have hu : U.Nonempty := by by_contra! hh; simp [hh] at h
  obtain ⟨a,ha⟩ := hu
  let A := U.erase a
  let anchor : E → E := fun _ => a
  have into {i : E} (hi : i ∈ U) : unit i - unit a ∈ starSpan A anchor := by
    by_cases he : i = a
    · simp [he]
    · exact star_mem (anchor := anchor) (mem_erase.mpr ⟨he,hi⟩)
  rw [← card_erase_of_mem ha]
  apply geometric_star (A := A) (anchor := anchor) (fun _ _ => notMem_erase a U) (unit a + unit a)
  · intro t ht
    obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp ht
    rw [vertex_pair (fun e => hxy (congrArg _ e))]
    convert (starSpan A anchor).add_mem (into hx) (into hy) using 1
    abel
  · intro i hi
    obtain ⟨b,hb,hbi,hba⟩ := third_color h (col i) (col a)
    have hne : i ≠ b := fun e => hbi (congrArg _ e.symm)
    have had : a ≠ b := fun e => hba (congrArg _ e.symm)
    refine ⟨{i,b},pair_mem.mpr ⟨(mem_erase.mp hi).2,hb,hbi.symm⟩,
      {a,b},pair_mem.mpr ⟨ha,hb,hba.symm⟩,?_⟩
    rw [vertex_pair hne,vertex_pair had]
    dsimp [anchor]
    abel

lemma dimension_cross {X Y : Finset E} (hx : X.Nonempty) (hy : Y.Nonempty) (hd : Disjoint X Y) :
    faceDimension (cross X Y) = (X ∪ Y).card - 2 := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  have outside {x : E} (h : x ∈ X) : x ∉ Y := disjoint_left.mp hd h
  have different {x y : E} (hx : x ∈ X) (hy : y ∈ Y) : x ≠ y := fun e => outside hx (e ▸ hy)
  let A := X.erase a ∪ Y.erase b
  let anchor : E → E := fun i => if i ∈ X then a else b
  have ax : a ∉ A := by simp [A,outside ha]
  have bx : b ∉ X := fun h => outside h hb
  have by' : b ∉ A := by simp [A,bx]
  have away (i : E) (_ : i ∈ A) : anchor i ∉ A := by
    by_cases h : i ∈ X <;> simp [anchor,h,ax,by']
  have left {x : E} (h : x ∈ X) : unit x - unit a ∈ starSpan A anchor := by
    by_cases he : x = a
    · simp [he]
    · have hx' : x ∈ A := mem_union_left _ (mem_erase.mpr ⟨he,h⟩)
      simpa [anchor,h] using (star_mem (anchor := anchor) hx')
  have right {x : E} (h : x ∈ Y) : unit x - unit b ∈ starSpan A anchor := by
    by_cases he : x = b
    · simp [he]
    · have hx' : x ∈ A := mem_union_right _ (mem_erase.mpr ⟨he,h⟩)
      have hn : x ∉ X := fun hh => outside hh h
      simpa [anchor,hn] using (star_mem (anchor := anchor) hx')
  have card : A.card = (X ∪ Y).card - 2 := by
    dsimp only [A]
    rw [card_union_of_disjoint (hd.mono (erase_subset ..) (erase_subset ..)),
      card_erase_of_mem ha,card_erase_of_mem hb,card_union_of_disjoint hd]
    have xp := card_pos.mpr (show X.Nonempty from ⟨_,ha⟩)
    have yp := card_pos.mpr (show Y.Nonempty from ⟨_,hb⟩)
    omega
  rw [← card]
  apply geometric_star away (unit a + unit b)
  · intro t ht
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_cross.mp ht
    rw [vertex_pair (different hx hy)]
    convert (starSpan A anchor).add_mem (left hx) (right hy) using 1
    abel
  · intro i hi
    have ab := mem_cross.mpr ⟨a,ha,b,hb,rfl⟩
    rw [show A = X.erase a ∪ Y.erase b by rfl] at hi
    rcases mem_union.mp hi with hi | hi
    · have ix := (mem_erase.mp hi).2
      refine ⟨{i,b},mem_cross.mpr ⟨i,ix,b,hb,rfl⟩,{a,b},ab,?_⟩
      rw [vertex_pair (different ix hb),vertex_pair (different ha hb)]
      simp [anchor,ix]
    · have iy := (mem_erase.mp hi).2
      have ix : i ∉ X := fun hh => outside hh iy
      refine ⟨{a,i},mem_cross.mpr ⟨a,ha,i,iy,rfl⟩,{a,b},ab,?_⟩
      rw [vertex_pair (different ha iy),vertex_pair (different ha hb)]
      simp [anchor,ix]

end FerroniFacePrefix
