module
public import conjectures.SidonSetSystems.Statement
public import conjectures.SidonSetSystems.CountingInput
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace SidonSetSystems
open Finset
open scoped Classical Pointwise

def shift (t : ℕ) (A : Finset ℕ) : Finset ℕ := A.image fun x => x+t

theorem card_shift (t : ℕ) (A : Finset ℕ) : (shift t A).card=A.card :=
  card_image_of_injective _ fun _ _ h => Nat.add_right_cancel h

theorem shift_add (t u : ℕ) (A B : Finset ℕ) : shift t A + shift u B = shift (t+u) (A+B) := by
  ext x
  constructor
  · intro h
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    obtain ⟨a₀,ha₀,ea⟩ := mem_image.mp ha
    obtain ⟨b₀,hb₀,eb⟩ := mem_image.mp hb
    exact mem_image.mpr ⟨a₀+b₀,mem_add.mpr ⟨a₀,ha₀,b₀,hb₀,rfl⟩,by omega⟩
  · intro h
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hz
    exact mem_add.mpr ⟨a+t,mem_image.mpr ⟨a,ha,rfl⟩,b+u,mem_image.mpr ⟨b,hb,rfl⟩,by omega⟩

theorem shift_inj (t : ℕ) {A B : Finset ℕ} (h : shift t A=shift t B) : A=B := by
  ext x
  have hi (U : Finset ℕ) : x+t∈shift t U ↔ x∈U := by simp [shift]
  rw [←hi A,h,hi]

theorem shift_rigid {t u : ℕ} {A B : Finset ℕ} (ha : 0∈A) (hb : 0∈B)
    (h : shift t A=shift u B) : t=u ∧ A=B := by
  have term {z : ℕ} {U : Finset ℕ} (hz : 0 ∈ U) : z ∈ shift z U :=
    mem_image.mpr ⟨0,hz,Nat.zero_add _⟩
  have bound {z x : ℕ} {U : Finset ℕ} (hz : x∈shift z U) : z≤x := by
    obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    omega
  have lo := bound (h ▸ term ha : t∈shift u B)
  have hi := bound (h.symm ▸ term hb : u∈shift t A)
  obtain rfl : t=u := by omega
  exact ⟨rfl,shift_inj _ h⟩

theorem neighbors_symm {G : Finset (Finset ℕ)} {a b : Finset ℕ} (ha : a∈G)
    (h : b∈neighbors G a) : a∈neighbors G b := by
  obtain ⟨_,ne,A,hA,B,hB,C,hC,D,hD,bad,aa,bb⟩ := mem_filter.mp h
  exact mem_filter.mpr ⟨ha,ne.symm,A,hA,B,hB,C,hC,D,hD,bad,bb,aa⟩

theorem finite_coloring (G : Finset (Finset ℕ)) (D : ℕ) (degree : ∀ a∈G,(neighbors G a).card≤D) :
    ∃ f : Finset ℕ → ℕ, (∀ a∈G, f a≤D) ∧ ∀ a∈G, ∀ b∈neighbors G a, f a≠f b := by
  have color (T : Finset (Finset ℕ)) (sub : T⊆G) : ∃ f : Finset ℕ→ℕ,
      (∀ a∈T,f a≤D) ∧ ∀ a∈T, ∀ b∈T, b∈neighbors G a → f a≠f b := by
    induction T using Finset.induction_on with
    | empty => exact ⟨fun _ => 0,by simp,by simp⟩
    | @insert a T ha ih =>
      have aG := sub (mem_insert_self _ _)
      obtain ⟨f,bd,proper⟩ := ih ((subset_insert _ _).trans sub)
      let used := (neighbors G a).image f
      obtain ⟨v,hv,free⟩ := exists_mem_notMem_of_card_lt_card (s:=used) (t:=range (D+1)) (by
        have := (card_image_le (f:=f) (s:=neighbors G a)).trans (degree a aG)
        simpa [used] using (Nat.lt_succ_of_le this))
      let g := fun x : Finset ℕ => if x=a then v else f x
      have diff (b : Finset ℕ) (hb : b∈neighbors G a) : v≠f b :=
        fun eq => free (eq ▸ mem_image.mpr ⟨b,hb,rfl⟩)
      refine ⟨g,?_,?_⟩
      · intro x hx
        rcases mem_insert.mp hx with e|hx
        · subst x; simpa [g] using (Nat.le_of_lt_succ (mem_range.mp hv))
        · have ne : x≠a := fun e => ha (e ▸ hx)
          simpa [g,ne] using bd x hx
      · intro x hx y hy nb
        have xy := (mem_filter.mp nb).2.1
        rcases mem_insert.mp hx with rfl|xt
        · simpa [g,Ne.symm xy] using diff y nb
        · have xa : x≠a := fun e => ha (e ▸ xt)
          rcases mem_insert.mp hy with rfl|yt
          · simpa [g,xa] using (diff x (neighbors_symm (sub (mem_insert_of_mem xt)) nb)).symm
          · have ya : y≠a := fun e => ha (e ▸ yt)
            simpa [g,xa,ya] using proper x xt y yt nb
  obtain ⟨f,bd,h⟩ := color G (Subset.rfl)
  exact ⟨f,bd,fun a ha b hb => h a ha b (mem_filter.mp hb).1 hb⟩

theorem tags_sidon (a b c d : ℕ) (h : 3^a+3^b=3^c+3^d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have ub (x y : ℕ) : 3^x+3^y < 3^(max x y+1) := by
    have h₁ := Nat.pow_le_pow_right (by decide : 0<3) (le_max_left x y)
    have h₂ := Nat.pow_le_pow_right (by decide : 0<3) (le_max_right x y)
    have pos : 0<3^(max x y) := by positivity
    rw [pow_succ]; omega
  have side (x y z w : ℕ) (eq : 3^x+3^y=3^z+3^w) : max x y ≤ max z w := by
    by_contra! bad
    have hh := Nat.pow_le_pow_right (by decide : 0<3) (show max z w+1 ≤ max x y by omega)
    have low : 3^(max x y) ≤ 3^x+3^y := by
      rcases le_total x y with u|u
      · rw [max_eq_right u]; exact Nat.le_add_left _ _
      · rw [max_eq_left u]; exact Nat.le_add_right _ _
    have bound := ub z w
    omega
  have same := le_antisymm (side a b c d h) (side c d a b h.symm)
  have inj : Function.Injective ((3:ℕ)^·) := (pow_right_strictMono₀ (by decide : 1<(3:ℕ))).injective
  rcases le_total a b with hab|hba <;> rcases le_total c d with hcd|hdc
  · rw [max_eq_right hab,max_eq_right hcd] at same; subst d
    exact Or.inl ⟨inj (show 3^a=3^c by omega),rfl⟩
  · rw [max_eq_right hab,max_eq_left hdc] at same; subst c
    exact Or.inr ⟨inj (show 3^a=3^d by omega),rfl⟩
  · rw [max_eq_left hba,max_eq_right hcd] at same; subst d
    exact Or.inr ⟨rfl,inj (show 3^b=3^c by omega)⟩
  · rw [max_eq_left hba,max_eq_left hdc] at same; subst c
    exact Or.inl ⟨rfl,inj (show 3^b=3^d by omega)⟩

end SidonSetSystems
