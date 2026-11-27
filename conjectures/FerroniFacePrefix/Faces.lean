module

public import conjectures.FerroniFacePrefix.Dimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace FerroniFacePrefix

open Finset

variable {E C : Type} [DecidableEq E] [DecidableEq C]

def Full (col : E → C) (U : Finset E) (F : Finset (Finset E)) : Prop :=
  ∃ S ⊆ U, 3 ≤ (S.image col).card ∧ F = bases col S

def Divided (col : E → C) (U : Finset E) (F : Finset (Finset E)) : Prop :=
  ∃ (X Y : Finset E) (c : C), X.Nonempty ∧ Y.Nonempty ∧ X ⊆ U ∧ Y ⊆ U ∧
    (∀ x ∈ X, col x = c) ∧ (∀ y ∈ Y, col y ≠ c) ∧ F = cross X Y

omit [DecidableEq E] [DecidableEq C] in
lemma separated {col : E → C} {X Y : Finset E} {c : C}
    (hx : ∀ x ∈ X, col x = c) (hy : ∀ y ∈ Y, col y ≠ c) : Disjoint X Y :=
  disjoint_left.mpr fun i hi hj => hy i hj (hx i hi)

private lemma two_colors {col : E → C} {S U : Finset E} {a b : E}
    (hsub : S ⊆ U) (ha : a ∈ S) (hb : b ∈ S) (hne : col a ≠ col b)
    (hsmall : (S.image col).card < 3) : Divided col U (bases col S) := by
  let X := S.filter fun x => col x = col a
  let Y := S.filter fun y => col y ≠ col a
  have hc (x : E) (hx : x ∈ S) : col x = col a ∨ col x = col b := by
    by_contra! he
    have htr : ({col x,col a,col b} : Finset C) ⊆ S.image col := by
      intro t ht
      simp only [mem_insert,mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact mem_image_of_mem _ hx
      · exact mem_image_of_mem _ ha
      · exact mem_image_of_mem _ hb
    have hcard := card_le_card htr
    simp [he.1, he.2, hne] at hcard
    omega
  refine ⟨X,Y,col a,⟨a,by simp [X,ha]⟩,⟨b,by simp [Y,hb,hne.symm]⟩,
    (filter_subset ..).trans hsub,(filter_subset ..).trans hsub,?_,?_,?_⟩
  · exact fun _ h => (mem_filter.mp h).2
  · exact fun _ h => (mem_filter.mp h).2
  · ext t
    constructor
    · intro h
      obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp h
      rcases hc x hx with cx | cx
      · exact mem_cross.mpr ⟨x,mem_filter.mpr ⟨hx,cx⟩,y,mem_filter.mpr ⟨hy,by simpa [← cx] using hxy.symm⟩,rfl⟩
      · have cy := (hc y hy).resolve_right (fun h' => hxy (cx.trans h'.symm))
        exact mem_cross.mpr ⟨y,mem_filter.mpr ⟨hy,cy⟩,x,mem_filter.mpr ⟨hx,by simpa [cx] using hne.symm⟩,pair_comm ..⟩
    · intro h
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_cross.mp h
      exact pair_mem.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hy).1,
        fun e => (mem_filter.mp hy).2 (e.symm.trans (mem_filter.mp hx).2)⟩

lemma face_shape {col : E → C} {U : Finset E} {F : Finset (Finset E)}
    (hF : IsFace (bases col U) F) : Full col U F ∨ Divided col U F := by
  obtain ⟨hn,w,hw⟩ := hF
  have hsub : F ⊆ bases col U := fun t ht => ((hw t).mp ht).1
  obtain ⟨t,ht⟩ := hn
  obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_bases.mp (hsub ht)
  have hordered : ∃ a ∈ U, ∃ b ∈ U, col a ≠ col b ∧ {a,b} ∈ F ∧ w b ≤ w a := by
    rcases le_total (w b) (w a) with h | h
    · exact ⟨a,ha,b,hb,hab,ht,h⟩
    · exact ⟨b,hb,a,ha,hab.symm,by rwa [pair_comm],h⟩
  obtain ⟨a,ha,b,hb,hab,hpair,habw⟩ := hordered
  have ab : a ≠ b := fun e => hab (congrArg _ e)
  have hmax := ((hw _).mp hpair).2
  have upper (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) (hxy : col x ≠ col y) :
      w x + w y ≤ w a + w b := by
    simpa [edge_weight w (show x ≠ y from fun e => hxy (congrArg _ e)),edge_weight w ab] using
      hmax {x,y} (pair_mem.mpr ⟨hx,hy,hxy⟩)
  have eqiff (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) (hxy : col x ≠ col y) :
      {x,y} ∈ F ↔ w x + w y = w a + w b := by
    have xy : x ≠ y := fun e => hxy (congrArg _ e)
    constructor
    · intro h
      apply (upper _ hx _ hy hxy).antisymm
      simpa [edge_weight w xy,edge_weight w ab] using ((hw _).mp h).2 _ (hsub hpair)
    · intro he
      apply (hw _).mpr
      refine ⟨pair_mem.mpr ⟨hx,hy,hxy⟩,?_⟩
      intro t ht
      rw [edge_weight w xy,he,← edge_weight w ab]
      exact hmax _ ht
  have hi (x : E) (hx : x ∈ U) (hc : col x = col a) : w x ≤ w a := by
    linarith [upper x hx b hb (by simpa [hc] using hab)]
  have lo (x : E) (hx : x ∈ U) (hc : col x ≠ col a) : w x ≤ w b := by
    linarith [upper a ha x hx hc.symm]
  by_cases heq : w a = w b
  · let S := U.filter fun x => w x = w a
    have hbnd (x : E) (hx : x ∈ U) : w x ≤ w a := by
      by_cases hc : col x = col a
      · exact hi x hx hc
      · simpa [heq] using lo x hx hc
    have hS : F = bases col S := by
      ext t
      constructor
      · intro ht
        obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp (hsub ht)
        have hs := (eqiff x hx y hy hxy).mp ht
        exact pair_mem.mpr ⟨mem_filter.mpr ⟨hx, by linarith [hbnd x hx,hbnd y hy]⟩,
          mem_filter.mpr ⟨hy, by linarith [hbnd x hx,hbnd y hy]⟩,hxy⟩
      · intro ht
        obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp ht
        exact (eqiff x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy).mpr (by
          linarith [(mem_filter.mp hx).2,(mem_filter.mp hy).2])
    rcases le_or_gt 3 (S.image col).card with hl | hs
    · exact Or.inl ⟨S,filter_subset ..,hl,hS⟩
    · rw [hS]
      exact Or.inr (two_colors (filter_subset ..) (mem_filter.mpr ⟨ha,rfl⟩ : a ∈ S)
        (mem_filter.mpr ⟨hb,heq.symm⟩ : b ∈ S) hab hs)
  · let X := U.filter fun x => col x = col a ∧ w x = w a
    let Y := U.filter fun y => col y ≠ col a ∧ w y = w b
    refine Or.inr ⟨X,Y,col a,⟨a,by simp [X,ha]⟩,⟨b,by simp [Y,hb,hab.symm]⟩,
      filter_subset ..,filter_subset ..,fun _ h => (mem_filter.mp h).2.1,
      fun _ h => (mem_filter.mp h).2.1,?_⟩
    ext t
    constructor
    · intro ht
      obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp (hsub ht)
      have hs := (eqiff x hx y hy hxy).mp ht
      by_cases cx : col x = col a
      · have cy : col y ≠ col a := fun h => hxy (cx.trans h.symm)
        exact mem_cross.mpr ⟨x,mem_filter.mpr ⟨hx,cx,by linarith [hi x hx cx,lo y hy cy]⟩,
          y,mem_filter.mpr ⟨hy,cy,by linarith [hi x hx cx,lo y hy cy]⟩,rfl⟩
      · have cy : col y = col a := by
          by_contra h
          linarith [lt_of_le_of_ne habw (fun e => heq e.symm), lo x hx cx,lo y hy h]
        exact mem_cross.mpr ⟨y,mem_filter.mpr ⟨hy,cy,by linarith [lo x hx cx,hi y hy cy]⟩,
          x,mem_filter.mpr ⟨hx,cx,by linarith [lo x hx cx,hi y hy cy]⟩,pair_comm ..⟩
    · intro ht
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_cross.mp ht
      obtain ⟨hx',cx,wx⟩ := mem_filter.mp hx
      obtain ⟨hy',cy,wy⟩ := mem_filter.mp hy
      exact (eqiff x hx' y hy' (fun e => cy (e.symm.trans cx))).mpr (by rw [wx,wy])

omit [DecidableEq E] in
private lemma face_of_level {B F : Finset (Finset E)} {w : E → ℝ} {v : ℝ}
    (hn : F.Nonempty) (upper : ∀ b ∈ B, ∑ i ∈ b, w i ≤ v)
    (hf : ∀ b, b ∈ F ↔ b ∈ B ∧ ∑ i ∈ b, w i = v) : IsFace B F := by
  refine ⟨hn,w,fun b => ?_⟩
  constructor
  · intro h
    obtain ⟨hb,he⟩ := (hf b).mp h
    exact ⟨hb,fun t ht => he ▸ upper t ht⟩
  · rintro ⟨hb,hm⟩
    obtain ⟨t,ht⟩ := hn
    obtain ⟨htB,he⟩ := (hf t).mp ht
    exact (hf b).mpr ⟨hb,(upper b hb).antisymm (he ▸ hm t htB)⟩

lemma full_isFace {col : E → C} {U : Finset E} {F : Finset (Finset E)}
    (hF : Full col U F) : IsFace (bases col U) F := by
  obtain ⟨S,hS,ht,rfl⟩ := hF
  let w : E → ℝ := fun x => if x ∈ S then 1 else 0
  have nh : S.Nonempty := by by_contra! h; simp [h] at ht
  obtain ⟨a,ha⟩ := nh
  obtain ⟨b,hb,hab,_⟩ := third_color ht (col a) (col a)
  apply face_of_level (w := w) (v := 2) ⟨{a,b},pair_mem.mpr ⟨ha,hb,hab.symm⟩⟩
  · intro t ht
    obtain ⟨x,_,y,_,hxy,rfl⟩ := mem_bases.mp ht
    rw [edge_weight w (fun e => hxy (congrArg _ e))]
    dsimp [w]
    split_ifs <;> norm_num
  · intro t
    constructor
    · intro h
      obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp h
      exact ⟨pair_mem.mpr ⟨hS hx,hS hy,hxy⟩, by
        rw [edge_weight w (fun e => hxy (congrArg _ e))]; norm_num [w,hx,hy]⟩
    · rintro ⟨h,he⟩
      obtain ⟨x,_,y,_,hxy,rfl⟩ := mem_bases.mp h
      rw [edge_weight w (fun e => hxy (congrArg _ e))] at he
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp_all [w,pair_mem]

lemma divided_isFace {col : E → C} {U : Finset E} {F : Finset (Finset E)}
    (hF : Divided col U F) : IsFace (bases col U) F := by
  obtain ⟨X,Y,c,hx,hy,XU,YU,cx,cy,rfl⟩ := hF
  have hd := separated cx cy
  let w : E → ℝ := fun i => if i ∈ X then 2 else if i ∈ Y then 1 else 0
  have level {u v : E} (ne : col u ≠ col v) : (w u+w v = 3 ↔
      (u ∈ X ∧ v ∈ Y) ∨ (v ∈ X ∧ u ∈ Y)) ∧ w u+w v ≤ 3 := by
    have notXX : u ∈ X → v ∈ X → False := fun hu hv => ne ((cx u hu).trans (cx v hv).symm)
    have notUXY : u ∈ X → u ∈ Y → False := fun hu hv => disjoint_left.mp hd hu hv
    have notVXY : v ∈ X → v ∈ Y → False := fun hu hv => disjoint_left.mp hd hu hv
    by_cases ux : u ∈ X <;> by_cases vx : v ∈ X <;> by_cases uy : u ∈ Y <;> by_cases vy : v ∈ Y <;>
      simp_all [w] <;> norm_num
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  apply face_of_level (w := w) (v := 3) ⟨{a,b}, mem_cross.mpr ⟨a,ha,b,hb,rfl⟩⟩
  · intro t ht
    obtain ⟨u,_,v,_,hne,rfl⟩ := mem_bases.mp ht
    rw [edge_weight w (fun e => hne (congrArg _ e))]
    exact (level hne).2
  · intro t
    constructor
    · intro ht
      obtain ⟨u,hu,v,hv,rfl⟩ := mem_cross.mp ht
      have hne : col u ≠ col v := fun e => cy v hv (e.symm.trans (cx u hu))
      refine ⟨pair_mem.mpr ⟨XU hu,YU hv,hne⟩, ?_⟩
      rw [edge_weight w (fun e => hne (congrArg _ e))]
      exact (level hne).1.mpr (Or.inl ⟨hu,hv⟩)
    · rintro ⟨ht,he⟩
      obtain ⟨u,_,v,_,hne,rfl⟩ := mem_bases.mp ht
      have une : u ≠ v := fun e => hne (congrArg _ e)
      rw [edge_weight w une] at he
      exact (pair_mem_cross une).mpr ((level hne).1.mp he)

lemma support_bound {col : E → C} {U : Finset E} {F : Finset (Finset E)}
    (hf : IsFace (bases col U) F) : (F.biUnion id).card ≤ faceDimension F + 2 := by
  obtain h | h := face_shape hf
  · obtain ⟨S,_,hS,rfl⟩ := h
    rw [support_wide hS,dimension_wide hS]
    omega
  · obtain ⟨X,Y,_,hx,hy,_,_,cx,cy,rfl⟩ := h
    rw [support_cross hx hy,dimension_cross hx hy (separated cx cy)]
    omega

end FerroniFacePrefix
