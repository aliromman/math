module

public import conjectures.FerroniFacePrefix.Statement
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

@[expose] public section

namespace FerroniFacePrefix

open Finset

variable {E C : Type} [DecidableEq E] [DecidableEq C]

lemma vertex_coordinate (b : Finset E) (i : E) : vertex b i = if i ∈ b then 1 else 0 := by
  simp [vertex,unit]

/-- Summing the coordinate weights of a basis is the linear functional on its indicator vector. -/
lemma vertex_weight [Fintype E] (w : E → ℝ) (b : Finset E) :
    ∑ i, w i * vertex b i = ∑ i ∈ b, w i := by
  simp [vertex_coordinate,mul_ite]

def bases (col : E → C) (U : Finset E) : Finset (Finset E) :=
  (U.powersetCard 2).filter fun b => (b.image col).card = 2

def cross (X Y : Finset E) : Finset (Finset E) :=
  (X ×ˢ Y).image fun p => {p.1, p.2}

lemma mem_bases {col : E → C} {U : Finset E} {b : Finset E} :
    b ∈ bases col U ↔ ∃ x ∈ U, ∃ y ∈ U, col x ≠ col y ∧ b = {x, y} := by
  constructor
  · intro hb
    obtain ⟨h, hc⟩ := mem_filter.mp hb
    obtain ⟨hs, hd⟩ := mem_powersetCard.mp h
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hd
    refine ⟨x, hs (by simp), y, hs (by simp), ?_, rfl⟩
    intro h
    simp [h] at hc
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    have hne : x ≠ y := fun e => hxy (congrArg _ e)
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨by
      intro k hk
      rcases (show k = x ∨ k = y by simpa using hk) with rfl | rfl
      · exact hx
      · exact hy, by simp [hne]⟩,
      by simp [hxy]⟩

lemma pair_mem {col : E → C} {U : Finset E} {x y : E} :
    {x, y} ∈ bases col U ↔ x ∈ U ∧ y ∈ U ∧ col x ≠ col y := by
  constructor
  · intro h
    obtain ⟨hU, hsize⟩ := mem_filter.mp h
    have hsub := (mem_powersetCard.mp hU).1
    exact ⟨hsub (by simp), hsub (by simp), fun he => by simp [he] at hsize⟩
  · rintro ⟨hx, hy, hne⟩
    exact mem_bases.mpr ⟨x, hx, y, hy, hne, rfl⟩

lemma mem_cross {X Y : Finset E} {b : Finset E} :
    b ∈ cross X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, b = {x,y} := by
  simp [cross, eq_comm, and_assoc]

lemma pair_mem_cross {X Y : Finset E} {x y : E} (hne : x ≠ y) :
    {x,y} ∈ cross X Y ↔ (x ∈ X ∧ y ∈ Y) ∨ (y ∈ X ∧ x ∈ Y) := by
  constructor
  · rintro h
    obtain ⟨u, hu, v, hv, he⟩ := mem_cross.mp h
    have hx : x = u ∨ x = v := by
      have hm : x ∈ ({u,v} : Finset E) := he ▸ (show x ∈ ({x,y} : Finset E) by simp)
      simpa only [mem_insert, mem_singleton] using hm
    have hy : y = u ∨ y = v := by
      have hm : y ∈ ({u,v} : Finset E) := he ▸ (show y ∈ ({x,y} : Finset E) by simp)
      simpa only [mem_insert, mem_singleton] using hm
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  · rintro (⟨hx,hy⟩ | ⟨hy,hx⟩)
    · exact mem_cross.mpr ⟨x,hx,y,hy,rfl⟩
    · exact mem_cross.mpr ⟨y,hy,x,hx,by simp [pair_comm]⟩

lemma isMatroid_bases {col : E → C} {U : Finset E} (h : (bases col U).Nonempty) :
    IsMatroid (bases col U) := by
  refine ⟨h, ?_⟩
  intro X hX Y hY i hi
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_bases.mp hX
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := mem_bases.mp hY
  have hpair {a b i : E} (ha : a ∈ U) (hb : b ∈ U) (hab : col a ≠ col b)
      (hi : i ∈ ({a,b} : Finset E) \ {p,q}) (he : i = a) :
      ∃ j ∈ ({p,q} : Finset E) \ {a,b}, insert j (({a,b} : Finset E).erase i) ∈ bases col U := by
    subst i
    have hab' : a ≠ b := fun t => hab (congrArg col t)
    have hpa : p ≠ a := by intro h; subst p; simp at hi
    have hqa : q ≠ a := by intro h; subst q; simp at hi
    by_cases hpb : col p = col b
    · have hqb : col q ≠ col b := fun h => hpq (hpb.trans h.symm)
      have hqbn : q ≠ b := fun t => hqb (congrArg col t)
      exact ⟨q,by simp [hqa, hqbn], by simpa [hab'] using (pair_mem.mpr ⟨hq,hb,hqb⟩ : {q,b} ∈ bases col U)⟩
    · have hpbn : p ≠ b := fun t => hpb (congrArg col t)
      exact ⟨p,by simp [hpa, hpbn], by simpa [hab'] using (pair_mem.mpr ⟨hp,hb,hpb⟩ : {p,b} ∈ bases col U)⟩
  rcases (show i = a ∨ i = b by simpa using (mem_sdiff.mp hi).1) with he | he
  · exact hpair ha hb hab hi he
  · rw [pair_comm a b] at hi ⊢
    exact hpair hb ha hab.symm hi he

lemma edge_weight {x y : E} (w : E → ℝ) (h : x ≠ y) : ∑ i ∈ ({x,y} : Finset E), w i = w x + w y := by
  simp [h]

lemma support_cross {X Y : Finset E} (hx : X.Nonempty) (hy : Y.Nonempty) :
    (cross X Y).biUnion id = X ∪ Y := by
  ext i
  simp only [mem_biUnion, id_eq, mem_union]
  constructor
  · rintro ⟨b,hb,hi⟩
    obtain ⟨x,hx',y,hy',rfl⟩ := mem_cross.mp hb
    rcases (show i = x ∨ i = y by simpa using hi) with rfl | rfl
    · exact Or.inl hx'
    · exact Or.inr hy'
  · rintro (h | h)
    · obtain ⟨y,hy'⟩ := hy
      exact ⟨{i,y}, mem_cross.mpr ⟨i,h,y,hy',rfl⟩, by simp⟩
    · obtain ⟨x,hx'⟩ := hx
      exact ⟨{x,i}, mem_cross.mpr ⟨x,hx',i,h,rfl⟩, by simp⟩

end FerroniFacePrefix
