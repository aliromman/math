module

public import conjectures.LuckySpots.CountCut
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section
namespace LuckySpots.Circle
open Finset
open scoped Classical
variable {m : ℕ} [NeZero m]

def shift (a : Fin m) (F : Finset (Fin m)) := F.image (·+a)
def offsets (F : Finset (Fin m)) (p : Fin m) := F.image (·-p)

noncomputable def target (F : Finset (Fin m)) (p : Fin m) : Fin m :=
  if h : (offsets F p).Nonempty then (offsets F p).min' h+p else p

noncomputable def step (F : Finset (Fin m)) (p : Fin m) := F.erase (target F p)
noncomputable def vacancies (F : Finset (Fin m)) (w : List (Fin m)) := w.foldl step F

noncomputable def hit (j : Fin m) : Finset (Fin m) → List (Fin m) → Prop
  | _,[] => False
  | F,p::ps => (p=j ∧ j∈F) ∨ hit j (step F p) ps

theorem mem_shift {a x : Fin m} {F : Finset (Fin m)} : x+a∈shift a F ↔ x∈F := by
  simp [shift]

theorem shift_univ (a : Fin m) : shift a univ=univ := by
  apply Finset.eq_univ_of_forall
  intro x
  exact mem_image.mpr ⟨x-a,mem_univ _,sub_add_cancel ..⟩

theorem offsets_shift (F : Finset (Fin m)) (p a : Fin m) :
    offsets (shift a F) (p+a)=offsets F p := by
  simp only [offsets,shift,image_image,Function.comp_def,add_sub_add_right_eq_sub]

theorem target_shift (F : Finset (Fin m)) (p a : Fin m) :
    target (shift a F) (p+a)=target F p+a := by
  simp only [target,offsets_shift]
  split <;> simp [add_assoc]

theorem step_shift (F : Finset (Fin m)) (p a : Fin m) :
    step (shift a F) (p+a)=shift a (step F p) := by
  ext x
  obtain ⟨y,rfl⟩ : ∃ y : Fin m, y+a=x := ⟨x-a,sub_add_cancel ..⟩
  simp [step,mem_shift,target_shift]

theorem vacancies_shift (F : Finset (Fin m)) (w : List (Fin m)) (a : Fin m) :
    vacancies (shift a F) (w.map (·+a))=shift a (vacancies F w) := by
  induction w generalizing F with
  | nil => rfl
  | cons p ps ih => simpa only [List.map_cons,vacancies,List.foldl_cons,step_shift] using ih (step F p)

theorem hit_shift (F : Finset (Fin m)) (w : List (Fin m)) (j a : Fin m) :
    hit (j+a) (shift a F) (w.map (·+a)) ↔ hit j F w := by
  induction w generalizing F with
  | nil => rfl
  | cons p ps ih => simp [hit,mem_shift,step_shift,ih]

theorem target_mem {F : Finset (Fin m)} (h : F.Nonempty) (p : Fin m) : target F p∈F := by
  have hd : (offsets F p).Nonempty := h.image _
  obtain ⟨x,hx,ex⟩ := mem_image.mp ((offsets F p).min'_mem hd)
  simp only [target,dite_eq_left hd,←ex,sub_add_cancel,hx]

theorem target_eq {F : Finset (Fin m)} {p x : Fin m} (hx : x∈F)
    (hl : ∀ y∈F,x-p≤y-p) : target F p=x := by
  have hd : (offsets F p).Nonempty := (show F.Nonempty from ⟨x,hx⟩).image _
  have hm : (offsets F p).min' hd = x-p := by
    apply le_antisymm
    · exact min'_le _ _ (mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,eq⟩ := mem_image.mp ((offsets F p).min'_mem hd)
      rw [←eq]
      exact hl _ hy
  simp [target,hd,hm]

theorem target_self {F : Finset (Fin m)} {p : Fin m} (hp : p∈F) : target F p=p :=
  target_eq hp (fun _ _ ↦ by simp)

theorem target_forward {F : Finset (Fin m)} {p x : Fin m} (hx : x∈F) (hp : p≤x)
    (hl : ∀ y∈F, p≤y → x≤y) : target F p=x := by
  apply target_eq hx
  intro y hy
  change (x-p).val ≤ (y-p).val
  rw [Fin.sub_val_of_le hp]
  by_cases e : p≤y
  · rw [Fin.sub_val_of_le e]
    exact Nat.sub_le_sub_right (hl y hy e) _
  · have ey : y<p := lt_of_not_ge e
    rw [Fin.coe_sub_iff_lt.mpr ey]
    have := x.isLt
    have := p.isLt
    omega

theorem step_card (F : Finset (Fin m)) (p : Fin m) : (step F p).card=F.card-1 := by
  by_cases h : F.Nonempty
  · exact card_erase_of_mem (target_mem h p)
  · simp_all [step,Finset.not_nonempty_iff_eq_empty]

theorem vacancies_card (F : Finset (Fin m)) (w : List (Fin m)) :
    (vacancies F w).card=F.card-w.length := by
  induction w generalizing F with
  | nil => simp [vacancies]
  | cons p ps ih =>
    change (vacancies (step F p) ps).card=_
    rw [ih,step_card,List.length_cons]
    omega

omit [NeZero m] in
theorem vacancies_subset (F : Finset (Fin m)) (w : List (Fin m)) : vacancies F w⊆F := by
  induction w generalizing F with
  | nil => exact Subset.rfl
  | cons p ps ih => exact (ih (step F p)).trans (erase_subset ..)

omit [NeZero m] in
theorem no_hit {j : Fin m} {F : Finset (Fin m)} (h : j∉F) (w : List (Fin m)) : ¬hit j F w := by
  induction w generalizing F with
  | nil => simp [hit]
  | cons p ps ih => simp [hit,h,ih (show j∉step F p from fun g ↦ h (erase_subset _ _ g))]

end LuckySpots.Circle
