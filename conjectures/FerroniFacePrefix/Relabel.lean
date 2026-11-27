module

public import conjectures.FerroniFacePrefix.Faces

@[expose] public section

namespace FerroniFacePrefix

open Finset

variable {E C : Type} [DecidableEq E] [DecidableEq C]

def relabel (f : E → E) (F : Finset (Finset E)) := F.image (image f)

lemma relabel_support (f : E → E) (F : Finset (Finset E)) :
    (relabel f F).biUnion id = (F.biUnion id).image f := by
  ext i
  simp [relabel]
  aesop

lemma relabel_involutive {f : E → E} (hinv : Function.Involutive f) :
    Function.Involutive (relabel f) := by
  have hc : Function.Involutive (image f) := by
    intro U
    simp [image_image,hinv]
  intro F
  simp [relabel,image_image,hc]

private lemma relabel_cross (f : E → E) (X Y : Finset E) :
    relabel f (cross X Y) = cross (X.image f) (Y.image f) := by
  ext t
  constructor
  · intro ht
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ht
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_cross.mp hb
    exact mem_cross.mpr ⟨f x,mem_image_of_mem _ hx,f y,mem_image_of_mem _ hy,by simp⟩
  · intro ht
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_cross.mp ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨{x,y},mem_cross.mpr ⟨x,hx,y,hy,rfl⟩,by simp⟩

private lemma relabel_bases {f : E → E} {g : C → C} {col : E → C} (hg : Function.Injective g)
    (h : ∀ x, col (f x) = g (col x)) (S : Finset E) :
    relabel f (bases col S) = bases col (S.image f) := by
  ext t
  constructor
  · intro ht
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ht
    obtain ⟨x,hx,y,hy,hxy,rfl⟩ := mem_bases.mp hb
    exact mem_bases.mpr ⟨f x,mem_image_of_mem _ hx,f y,mem_image_of_mem _ hy,
      by simp [h,hg.ne hxy],by simp⟩
  · intro ht
    obtain ⟨u,hu,v,hv,huv,rfl⟩ := mem_bases.mp ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨{x,y},pair_mem.mpr ⟨hx,hy,fun e => huv (by rw [h,h,e])⟩,by simp⟩

lemma relabel_face {col : E → C} {U V : Finset E} {F : Finset (Finset E)}
    {f : E → E} {g : C → C} (hf : Function.Injective f) (hg : Function.Injective g)
    (hcol : ∀ x, col (f x) = g (col x)) (hF : IsFace (bases col U) F)
    (hV : ∀ x ∈ F.biUnion id, f x ∈ V) :
    IsFace (bases col V) (relabel f F) ∧ faceDimension (relabel f F) = faceDimension F := by
  rcases face_shape hF with h | h
  · obtain ⟨S,_,hS,rfl⟩ := h
    have hc : ((S.image f).image col).card = (S.image col).card := by
      have he : (S.image f).image col = (S.image col).image g := by simp [image_image,Function.comp_def,hcol]
      rw [he,card_image_of_injective _ hg]
    have ht : 3 ≤ ((S.image f).image col).card := hc ▸ hS
    rw [support_wide hS] at hV
    have sub : S.image f ⊆ V := by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      exact hV x hx
    rw [relabel_bases hg hcol]
    exact ⟨full_isFace ⟨_,sub,ht,rfl⟩,by rw [dimension_wide ht,dimension_wide hS,card_image_of_injective _ hf]⟩
  · obtain ⟨X,Y,c,hx,hy,_,_,cx,cy,rfl⟩ := h
    rw [support_cross hx hy] at hV
    have px : X.image f ⊆ V := by
      intro a ha
      obtain ⟨x,h,rfl⟩ := mem_image.mp ha
      exact hV x (mem_union_left _ h)
    have py : Y.image f ⊆ V := by
      intro a ha
      obtain ⟨y,h,rfl⟩ := mem_image.mp ha
      exact hV y (mem_union_right _ h)
    have sx : ∀ x ∈ X.image f, col x = g c := by
      intro a ha
      obtain ⟨x,h,rfl⟩ := mem_image.mp ha
      rw [hcol,cx x h]
    have sy : ∀ y ∈ Y.image f, col y ≠ g c := by
      intro a ha
      obtain ⟨y,h,rfl⟩ := mem_image.mp ha
      rw [hcol]
      exact hg.ne (cy y h)
    rw [relabel_cross]
    refine ⟨divided_isFace ⟨_,_,_,hx.image _,hy.image _,px,py,sx,sy,rfl⟩,?_⟩
    rw [dimension_cross (hx.image f) (hy.image f) (separated sx sy),
      dimension_cross hx hy (separated cx cy),← image_union,card_image_of_injective _ hf]

end FerroniFacePrefix
