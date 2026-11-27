module
public import conjectures.SidonSetSystems.Lower
import Mathlib.Data.Finset.Max

public section
namespace SidonSetSystems
open Finset
open scoped Pointwise Classical

private noncomputable def first (A : Finset ℕ) := if h : A.Nonempty then A.min' h else 0
private noncomputable def normal (A : Finset ℕ) := A.image fun x => x-first A
private theorem first_mem {A : Finset ℕ} (ne : A.Nonempty) : first A∈A := by
  simpa only [first,dite_eq_left ne] using A.min'_mem ne
private theorem first_le {A : Finset ℕ} {x : ℕ} (hx : x∈A) : first A≤x := by
  have ne : A.Nonempty := ⟨x,hx⟩
  simpa [first,ne] using A.min'_le x hx
private theorem restore (A : Finset ℕ) : shift (first A) (normal A)=A := by
  ext x
  constructor
  · intro h
    obtain ⟨v,hv,e⟩ := mem_image.mp h
    obtain ⟨u,hu,f⟩ := mem_image.mp hv
    have lo := first_le hu
    have : u=x := by omega
    exact this ▸ hu
  · intro h
    exact mem_image.mpr ⟨x-first A,mem_image.mpr ⟨x,h,rfl⟩,Nat.sub_add_cancel (first_le h)⟩

private theorem normal_shape {k n : ℕ} (hk : 0<k) {A : Finset ℕ} (valid : A∈(Icc 1 n).powersetCard k) :
    normal A ∈ shapes k n := by
  obtain ⟨sub,card⟩ := mem_powersetCard.mp valid
  have ne := card_pos.mp (card ▸ hk)
  have low := (mem_Icc.mp (sub (first_mem ne))).1
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨?_,?_⟩,mem_image.mpr ⟨first A,first_mem ne,Nat.sub_self _⟩⟩
  · intro x hx
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    apply mem_range.mpr
    have hi := (mem_Icc.mp (sub hu)).2
    have lo := first_le hu
    omega
  · rw [←restore A] at card
    simpa only [card_shift] using card

private theorem shift_twice (s t : ℕ) (A : Finset ℕ) : shift s (shift t A)=shift (t+s) A := by
  simp [shift,image_image,Nat.add_assoc,Function.comp_def]

private theorem shift_swap (t : ℕ) (A B : Finset ℕ) : shift t A + B = A + shift t B := by
  have zero (U : Finset ℕ) : shift 0 U=U := by simp [shift]
  calc
    _ = shift t (A+B) := by simpa only [zero,Nat.add_zero] using shift_add t 0 A B
    _ = _ := by simpa only [zero,Nat.zero_add] using (shift_add 0 t A B).symm

/-- Each additional translate of a shape uses a positive difference unique to that translate. -/
theorem extremal_upper {k n : ℕ} (hk : 0<k) (hn : 0<n) : extremal k n≤upperBound k n := by
  apply Finset.sup_le
  intro F hF
  obtain ⟨allowed,sidon⟩ := mem_filter.mp hF
  have valid := mem_powerset.mp allowed
  let fiber (s : Finset ℕ) := F.filter fun a => normal a=s
  let pick (s : Finset ℕ) := if h : (fiber s).Nonempty then ((fiber s).exists_min_image first h).choose else ∅
  let base (a : Finset ℕ) := pick (normal a)
  have spec {a : Finset ℕ} (ha : a∈F) : base a∈F ∧ normal (base a)=normal a ∧ first (base a)≤first a := by
    have inF : a∈fiber (normal a) := mem_filter.mpr ⟨ha,rfl⟩
    have ne : (fiber (normal a)).Nonempty := ⟨a,inF⟩
    have er := ((fiber (normal a)).exists_min_image first ne).choose_spec
    simpa only [base,pick,dite_eq_left ne] using (show _ from ⟨(mem_filter.mp er.1).1,(mem_filter.mp er.1).2,er.2 a inF⟩)
  let gap (a : Finset ℕ) := first a-first (base a)
  have rep {a : Finset ℕ} (ha : a∈F) : shift (gap a) (base a)=a := by
    have h := spec ha
    calc
      _ = shift (gap a) (shift (first (base a)) (normal (base a))) := congrArg _ (restore _).symm
      _ = shift (first a) (normal a) := by rw [shift_twice,h.2.1]; congr 1; dsimp [gap]; omega
      _ = a := restore _
  let R := F.filter fun a => a=base a
  let T := F.filter fun a => ¬a=base a
  have cr : R.card≤(shapes k n).card := by
    apply card_le_card_of_injOn normal (fun a ha => normal_shape hk (valid (mem_filter.mp ha).1))
    intro a ha b hb e
    exact (mem_filter.mp ha).2.trans ((congrArg pick e).trans (mem_filter.mp hb).2.symm)
  have ct : T.card≤(Icc 1 (n-k)).card := by
    apply card_le_card_of_injOn gap
    · intro a ha
      obtain ⟨af,extra⟩ := mem_filter.mp ha
      have sa := spec af
      have nonempty {u : Finset ℕ} (hu : u∈F) : u.Nonempty := card_pos.mp ((mem_powersetCard.mp (valid hu)).2 ▸ hk)
      have bp := (mem_Icc.mp ((mem_powersetCard.mp (valid sa.1)).1 (first_mem (nonempty sa.1)))).1
      have sub : a⊆Icc (first a) n := fun x hx => mem_Icc.mpr ⟨first_le hx,(mem_Icc.mp ((mem_powersetCard.mp (valid af)).1 hx)).2⟩
      have hi := card_le_card sub
      rw [(mem_powersetCard.mp (valid af)).2,Nat.card_Icc] at hi
      have pos : 0<gap a := by
        by_contra! no
        have z : gap a=0 := by omega
        have eq := rep af
        rw [z] at eq
        have : base a=a := by simpa [shift] using eq
        exact extra this.symm
      apply mem_Icc.mpr
      dsimp [gap] at *
      omega
    · intro a ha b hb eq
      obtain ⟨af,ae⟩ := mem_filter.mp ha
      obtain ⟨bf,_⟩ := mem_filter.mp hb
      have sum : a+base b=base a+b := calc
        _ = shift (gap a) (base a)+base b := congrArg (·+base b) (rep af).symm
        _ = base a+shift (gap a) (base b) := shift_swap ..
        _ = _ := by rw [eq,rep bf]
      rcases sidon a af _ (spec bf).1 _ (spec af).1 b bf sum with h|h
      · exact False.elim (ae h.1)
      · exact h.1
  have total := card_filter_add_card_filter_not (s:=F) (fun a => a=base a)
  change R.card+T.card=F.card at total
  rw [shapes_card _ _ hk hn] at cr
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at ct
  rw [←total]
  exact Nat.add_le_add cr ct

end SidonSetSystems
