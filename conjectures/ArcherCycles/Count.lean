module

public import conjectures.ArcherCycles.Patterns
public import conjectures.ArcherCycles.Cut
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.NatAntidiagonal

@[expose] public section
namespace ArcherCycles
open Finset

/-- In the second family, the entries before the minimum have no ascent. -/
noncomputable def family (g : Bool) (n : ℕ) : Finset Word := by
  classical exact (valid n).filter (fun w ↦ g=true → ¬HasEarly w)

private noncomputable def initial (g : Bool) (n : ℕ) := (valid n).filter (fun w ↦ g=true → w=[])

noncomputable def positive (n : ℕ) := (valid n).erase []

private noncomputable def branch (ij : ℕ × ℕ) :=
  ((positive ij.1) ×ˢ (family true ij.2)).image (fun qp ↦ join qp.1 qp.2)

@[simp] theorem mem_valid {w n} :
    w ∈ valid n ↔ Ranked w n ∧ ¬Has213 w ∧ ¬Has3412 w := by
  classical simp [valid, Ranked, List.mem_permutations]

@[simp] theorem mem_family {w n g} :
    w ∈ family g n ↔ w∈valid n ∧ (g=true → ¬HasEarly w) := by
  classical simp [family]

@[simp] theorem contains213_nil : ¬Has213 [] := by simp [Has213]
@[simp] theorem contains3412_nil : ¬Has3412 [] := by simp [Has3412,Four,edges,path]
@[simp] theorem early_nil : ¬HasEarly [] := by simp [HasEarly,Early,edges,path]

@[simp] theorem valid_zero : valid 0 = {[]} := by
  classical ext w
  simp [Ranked]
  rintro rfl
  simp

private theorem nil_rank : Ranked [] 0 := List.Perm.refl []

private theorem nil_join {p n} (hp : Ranked p n) (g : Bool) :
    join [] p ∈ family g (n+1) ↔ p∈initial g n := by
  have bp := rank_bounded hp
  have r := ranked_join nil_rank hp
  simp only [Nat.zero_add] at r
  simp only [mem_family,mem_valid,r,hp,true_and,contains213_join bp,contains_join bp,
    early_join bp,contains213_nil,contains3412_nil, false_or,ne_eq,not_true_eq_false,
    false_and,or_false,true_and,initial,mem_filter]
  by_cases h : p=[]
  · simp [h]
  · cases g <;> simp [h]

private theorem positive_join {q p m n} (hq : Ranked q m) (hp : Ranked p n) (qn : q≠[])
    (g : Bool) : join q p ∈ family g (m+n+1) ↔ q∈positive m ∧ p∈family true n := by
  have bp := rank_bounded hp
  simp only [mem_family,mem_valid,ranked_join hq hp,hq,hp,true_and,contains213_join bp,
    contains_join bp,early_join bp,qn,true_and,false_and,or_false,positive,mem_erase,true_implies]
  tauto

private theorem mem_branch {w ij} : w∈branch ij ↔
    ∃ q∈positive ij.1, ∃ p∈family true ij.2, join q p=w := by
  simp [branch,exists_and_left, and_assoc]

private theorem pos_rank {w n} (h : w∈positive n) : Ranked w n :=
  (mem_valid.mp (mem_erase.mp h).2).1

private theorem fam_rank {w n g} (h : w∈family g n) : Ranked w n :=
  (mem_valid.mp (mem_family.mp h).1).1

private theorem decomposition (g : Bool) (n : ℕ) :
    family g (n+1) = (initial g n).image (join []) ∪ (antidiagonal n).biUnion branch := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨rw,h213,_⟩ := mem_valid.mp (mem_family.mp hw).1
    obtain ⟨q,p,rfl,rq,rp⟩ := exists_join rw h213
    have len := rank_length rw
    simp only [join,List.length_append,List.length_map,List.length_cons] at len
    rw [mem_union]
    by_cases qz : q=[]
    · subst q
      simp only [List.length_nil,Nat.zero_add,Nat.succ.injEq] at len
      subst n
      exact Or.inl (mem_image.mpr ⟨p,(nil_join rp g).mp hw,rfl⟩)
    · have sum : q.length+p.length=n := by omega
      obtain ⟨hq,hp⟩ := (positive_join rq rp qz g).mp (sum.symm ▸ hw)
      exact Or.inr (mem_biUnion.mpr ⟨(q.length,p.length),mem_antidiagonal.mpr sum,
        mem_branch.mpr ⟨q,hq,p,hp,rfl⟩⟩)
  · rw [mem_union,mem_image,mem_biUnion]
    rintro (⟨p,hp,rfl⟩|⟨⟨i,j⟩,hij,h⟩)
    · exact (nil_join (mem_valid.mp (mem_filter.mp hp).1).1 g).mpr hp
    · obtain ⟨q,hq,p,hp,rfl⟩ := mem_branch.mp h
      have hsum : i+j=n := mem_antidiagonal.mp hij
      rw [←hsum]
      exact (positive_join (pos_rank hq) (fam_rank hp) (mem_erase.mp hq).1 g).mpr ⟨hq,hp⟩

private theorem same_parts {q p s t : Word} (h : join q p=join s t) : q=s ∧ p=t := by
  have he := @join_injective (q,p) (s,t) h
  exact Prod.mk.inj he

private theorem count_family (g : Bool) (n : ℕ) :
    (family g (n+1)).card = (initial g n).card +
      ∑ ij ∈ antidiagonal n, (positive ij.1).card * (family true ij.2).card := by
  classical
  rw [decomposition,card_union_of_disjoint,card_image_of_injective _ (fun p t h ↦ (same_parts h).2),
    card_biUnion]
  · simp [branch,card_image_of_injective _ join_injective]
  · intro a _ b _ hab
    apply disjoint_left.mpr
    intro w ha hb
    obtain ⟨q,hq,p,hp,he⟩ := mem_branch.mp ha
    obtain ⟨s,hs,t,ht,eq⟩ := mem_branch.mp hb
    obtain ⟨rfl,rfl⟩ := same_parts (he.trans eq.symm)
    exact hab (Prod.ext ((rank_length (pos_rank hq)).symm.trans (rank_length (pos_rank hs)))
      ((rank_length (fam_rank hp)).symm.trans (rank_length (fam_rank ht))))
  · apply disjoint_left.mpr
    intro w hw hb
    obtain ⟨s,_,rfl⟩ := mem_image.mp hw
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb
    obtain ⟨q,hq,p,_,eq⟩ := mem_branch.mp hi
    exact (mem_erase.mp hq).1 (same_parts eq).1

theorem count_all (n : ℕ) : (valid (n+1)).card = (valid n).card +
    ∑ ij ∈ antidiagonal n, (positive ij.1).card * (family true ij.2).card := by
  simpa [family,initial] using count_family false n

theorem count_decreasing (n : ℕ) : (family true (n+1)).card = (if n=0 then 1 else 0) +
    ∑ ij ∈ antidiagonal n, (positive ij.1).card * (family true ij.2).card := by
  rw [count_family]
  congr 1
  by_cases hz : n=0
  · simp [initial,hz,filter_singleton]
  · have hn : []∉valid n := by
      intro h
      exact hz (rank_length (mem_valid.mp h).1).symm
    rw [ite_eq_right hz,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hm,he⟩ := mem_filter.mp hw
    exact hn ((he rfl) ▸ hm)

theorem card_positive (n : ℕ) : (positive n).card = if n=0 then 0 else (valid n).card := by
  by_cases h : n=0
  · simp [h,positive]
  · have hn : []∉valid n := fun hm ↦ h (rank_length (mem_valid.mp hm).1).symm
    simp [positive,h,hn]

end ArcherCycles
