module

public import conjectures.FerroniFacePrefix.Faces

@[expose] public section

namespace FerroniFacePrefix

open Finset

variable {E C : Type} [DecidableEq E] [DecidableEq C]

noncomputable def faces (B : Finset (Finset E)) (k : ℕ) : Finset (Finset (Finset E)) := by
  classical
  exact B.powerset.filter fun F => IsFace B F ∧ faceDimension F = k

lemma mem_faces {B F : Finset (Finset E)} {k : ℕ} :
    F ∈ faces B k ↔ IsFace B F ∧ faceDimension F = k := by
  classical
  change F ∈ B.powerset.filter _ ↔ _
  rw [mem_filter,mem_powerset]
  constructor
  · exact And.right
  · intro h
    obtain ⟨_,w,hw⟩ := h.1
    exact ⟨fun t ht => ((hw t).mp ht).1,h⟩

def classFace (col : E → C) (U : Finset E) (c : C) :=
  cross (U.filter (col · = c)) (U.filter (col · ≠ c))

private lemma split_union (col : E → C) (U : Finset E) (c : C) :
    U.filter (col · = c) ∪ U.filter (col · ≠ c) = U := by
  ext x
  by_cases h : col x = c <;> simp [h]

private lemma class_data {col : E → C} {U : Finset E} (h3 : 3 ≤ (U.image col).card)
    {c : C} (hc : c ∈ U.image col) : Divided col U (classFace col U c) ∧
    (classFace col U c).biUnion id = U ∧ faceDimension (classFace col U c) = U.card - 2 := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
  obtain ⟨b,hb,hb',_⟩ := third_color h3 (col a) (col a)
  have H : (U.filter (col · = col a)).Nonempty := ⟨a,by simp [ha]⟩
  have K : (U.filter (col · ≠ col a)).Nonempty := ⟨b,by simp [hb,hb']⟩
  have dis := separated (col := col) (c := col a)
    (X := U.filter (col · = col a)) (Y := U.filter (col · ≠ col a))
    (fun _ h => (mem_filter.mp h).2) (fun _ h => (mem_filter.mp h).2)
  exact ⟨⟨_,_,_,H,K,filter_subset ..,filter_subset ..,fun _ h => (mem_filter.mp h).2,
    fun _ h => (mem_filter.mp h).2,rfl⟩,
    (support_cross H K).trans (split_union ..), by
      rw [classFace,dimension_cross H K dis,split_union]⟩

private lemma class_inj {col : E → C} {U : Finset E} (h3 : 3 ≤ (U.image col).card) :
    Set.InjOn (classFace col U) (U.image col) := by
  intro c hc d _ hd
  by_contra hcd
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
  obtain ⟨b,hb,hba,hbd⟩ := third_color h3 (col a) d
  have ht : {a,b} ∈ classFace col U (col a) :=
    mem_cross.mpr ⟨a,by simp [ha],b,by simp [hb,hba],rfl⟩
  rw [hd] at ht
  have hne : a ≠ b := fun e => hba (congrArg _ e.symm)
  have hh := (pair_mem_cross hne).mp ht
  simp [hcd,hbd] at hh

lemma facet_number {col : E → C} {U : Finset E} (h3 : 3 ≤ (U.image col).card)
    (hdup : ∀ a ∈ U, ∃ b ∈ U, b ≠ a ∧ col b = col a) :
    faceNumber (bases col U) (U.card - 2) = U.card + (U.image col).card := by
  classical
  have ground : 3 ≤ U.card := h3.trans card_image_le
  have keeps (a : E) : (U.erase a).image col = U.image col := by
    refine Subset.antisymm (image_mono col (erase_subset a U)) ?_
    intro t ht
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ht
    by_cases h : b = a
    · subst b
      obtain ⟨v,hv,hva,he⟩ := hdup a hb
      exact mem_image.mpr ⟨v,mem_erase.mpr ⟨hva,hv⟩,he⟩
    · exact mem_image_of_mem _ (mem_erase.mpr ⟨h,hb⟩)
  have d3 (a : E) : 3 ≤ ((U.erase a).image col).card := by rwa [keeps]
  let D := fun a => bases col (U.erase a)
  let H := classFace col U
  let k := U.card - 2
  have dSupport (a : E) : (D a).biUnion id = U.erase a := support_wide (d3 a)
  have hSupport (c) (hc : c ∈ U.image col) : (H c).biUnion id = U := (class_data h3 hc).2.1
  have hset : faces (bases col U) k = U.image D ∪ (U.image col).image H := by
    ext F
    rw [mem_faces,mem_union]
    constructor
    · rintro ⟨hf,hd⟩
      obtain hf | hf := face_shape hf
      · obtain ⟨S,hs,hS,rfl⟩ := hf
        rw [dimension_wide hS] at hd
        have hcard := card_le_card hs
        have hdiff : (U \ S).card = 1 := by rw [card_sdiff_of_subset hs]; dsimp [k] at hd; omega
        obtain ⟨a,ha⟩ := card_eq_one.mp hdiff
        have ha' : a ∈ U \ S := by rw [ha]; simp
        obtain ⟨hau,has⟩ := mem_sdiff.mp ha'
        have he : U.erase a = S := by
          ext x
          constructor
          · intro hx
            obtain ⟨hn,hx⟩ := mem_erase.mp hx
            by_contra hno
            have ht : x ∈ U \ S := mem_sdiff.mpr ⟨hx,hno⟩
            rw [ha,mem_singleton] at ht
            exact hn ht
          · intro hx
            exact mem_erase.mpr ⟨fun he => has (he ▸ hx),hs hx⟩
        exact Or.inl (mem_image.mpr ⟨a,hau,congrArg (bases col) he⟩)
      · obtain ⟨X,Y,c,hx,hy,XU,YU,cx,cy,rfl⟩ := hf
        have hd' := dimension_cross hx hy (separated cx cy)
        have hcard := card_le_card (union_subset XU YU)
        have he : X ∪ Y = U := eq_of_subset_of_card_le (union_subset XU YU) (by
          dsimp [k] at hd; omega)
        have splitX : U.filter (col · = c) = X := by
          ext i
          constructor
          · intro hi
            obtain ⟨hi,hc⟩ := mem_filter.mp hi
            rw [← he] at hi
            exact (mem_union.mp hi).resolve_right (fun h => cy i h hc)
          · intro hi
            exact mem_filter.mpr ⟨XU hi,cx i hi⟩
        have splitY : U.filter (col · ≠ c) = Y := by
          ext i
          constructor
          · intro hi
            obtain ⟨hi,hc⟩ := mem_filter.mp hi
            rw [← he] at hi
            exact (mem_union.mp hi).resolve_left (fun h => hc (cx i h))
          · intro hi
            exact mem_filter.mpr ⟨YU hi,cy i hi⟩
        obtain ⟨a,ha⟩ := hx
        exact Or.inr (mem_image.mpr ⟨c,mem_image.mpr ⟨a,XU ha,cx a ha⟩,by simp [H,classFace,splitX,splitY]⟩)
    · rintro (hf | hf)
      · obtain ⟨a,ha,rfl⟩ := mem_image.mp hf
        refine ⟨full_isFace ⟨U.erase a,erase_subset ..,d3 a,rfl⟩,?_⟩
        rw [show D a = bases col (U.erase a) from rfl,dimension_wide (d3 a),card_erase_of_mem ha]
        dsimp [k]; omega
      · obtain ⟨c,hc,rfl⟩ := mem_image.mp hf
        exact ⟨divided_isFace (class_data h3 hc).1,(class_data h3 hc).2.2⟩
  have dis : Disjoint (U.image D) ((U.image col).image H) := by
    refine disjoint_left.mpr ?_
    intro F hD hH
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hD
    obtain ⟨c,hc,he⟩ := mem_image.mp hH
    have eq := congrArg (fun Z : Finset (Finset E) => Z.biUnion id) he
    rw [hSupport c hc,dSupport a] at eq
    exact notMem_erase a U (eq ▸ ha)
  have di : Set.InjOn D U := by
    intro a ha b _ h
    have eq := congrArg (fun Z : Finset (Finset E) => Z.biUnion id) h
    rw [dSupport,dSupport] at eq
    exact (erase_inj U ha).mp eq
  change (faces (bases col U) k).card = _
  rw [hset,card_union_of_disjoint dis,card_image_of_injOn di,card_image_of_injOn (class_inj h3)]

end FerroniFacePrefix
