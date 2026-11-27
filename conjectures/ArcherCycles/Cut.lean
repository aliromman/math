module

public import conjectures.ArcherCycles.Blocks
import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace ArcherCycles
open Finset

private theorem contains_map {f : ℕ → ℕ} (hf : StrictMono f) (w : Word) :
    Has213 (w.map f) ↔ Has213 w := by
  constructor
  · rintro ⟨a,b,c,hs,hab,hac⟩
    obtain ⟨l,hl,hy⟩ := List.sublist_map_iff.mp hs
    obtain ⟨i,t₁,rfl,rfl,h₁⟩ := List.map_eq_cons_iff.mp hy.symm
    obtain ⟨j,t₂,rfl,rfl,h₂⟩ := List.map_eq_cons_iff.mp h₁
    obtain ⟨k,rfl,rfl⟩ := List.map_eq_singleton_iff.mp h₂
    exact ⟨i,j,k,hl,hf.lt_iff_lt.mp hab,hf.lt_iff_lt.mp hac⟩
  · rintro ⟨a,b,c,h,ha,hc⟩
    exact ⟨f a,f b,f c,h.map f,hf ha,hf hc⟩

private theorem contains_min (w : Word) : Has213 (0::w) ↔ Has213 w := by
  constructor
  · rintro ⟨a,b,c,h,ha,hc⟩
    rcases List.cons_sublist_cons'.mp h with h|⟨rfl,_⟩
    · exact ⟨a,b,c,h,ha,hc⟩
    · omega
  · rintro ⟨a,b,c,h,ha,hc⟩
    exact ⟨a,b,c,h.cons _,ha,hc⟩

theorem contains213_cycle (w : Word) : Has213 (0::w.map Nat.succ) ↔ Has213 w := by
  rw [contains_min,contains_map (fun _ _ h ↦ Nat.succ_lt_succ h)]

private theorem contains_skew (u v : Word) (sep : ∀ a ∈ u, ∀ b ∈ v, b<a) :
    Has213 (u++v) ↔ Has213 u ∨ Has213 v := by
  constructor
  · rintro ⟨a,b,c,hs,ha,hc⟩
    obtain ⟨l,r,he,hl,hr⟩ := List.sublist_append_iff.mp hs
    rcases List.cons_eq_append_iff.mp he with ⟨rfl,rfl⟩|⟨l₁,rfl,h₁⟩
    · exact Or.inr ⟨a,b,c,hr,ha,hc⟩
    have am := hl.mem (List.mem_cons_self ..)
    rcases List.cons_eq_append_iff.mp h₁ with ⟨rfl,rfl⟩|⟨l₂,rfl,h₂⟩
    · have := sep a am c (hr.mem (by simp))
      omega
    rcases List.cons_eq_append_iff.mp h₂ with ⟨rfl,rfl⟩|⟨l₃,rfl,h₃⟩
    · have := sep a am c (hr.mem (by simp))
      omega
    simp at h₃
    obtain ⟨rfl,rfl⟩ := h₃
    exact Or.inl ⟨a,b,c,hl,ha,hc⟩
  · rintro (⟨a,b,c,h,ha,hc⟩|⟨a,b,c,h,ha,hc⟩)
    · exact ⟨a,b,c,h.trans (List.sublist_append_left ..),ha,hc⟩
    · exact ⟨a,b,c,h.trans (List.sublist_append_right ..),ha,hc⟩

theorem contains213_join {p q : Word} (bp : Bounded p) :
    Has213 (join q p) ↔ Has213 q ∨ Has213 p := by
  rw [join, contains_skew, contains_min, contains_map, contains_map]
  · exact fun _ _ h ↦ Nat.succ_lt_succ h
  · exact fun _ _ h => Nat.add_lt_add_left h _
  · intro a ha b hb
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    rcases List.mem_cons.mp hb with rfl|hb
    · omega
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    have := bp j hj
    omega

def Ranked (w : Word) (n : ℕ) : Prop := w.Perm (List.range n)

theorem rank_length {w n} (h : Ranked w n) : w.length=n := by
  simpa using List.Perm.length_eq h

theorem rank_mem {w n} (h : Ranked w n) (x : ℕ) : x∈w ↔ x<n := by
  simpa using h.mem_iff (a:=x)

theorem rank_bounded {w n} (h : Ranked w n) : Bounded w := fun x hx ↦
  rank_length h ▸ (rank_mem h x).mp hx

theorem ranked_join {p q m n} (hq : Ranked q m) (hp : Ranked p n) :
    Ranked (join q p) (m+n+1) := by
  have ql := rank_length hq
  have pl := rank_length hp
  have hnq := hq.nodup_iff.mpr List.nodup_range
  have hnp := hp.nodup_iff.mpr List.nodup_range
  apply (List.perm_ext_iff_of_nodup _ List.nodup_range).mpr
  · intro i
    simp only [join,List.mem_range,List.mem_append,List.mem_cons,List.mem_map]
    constructor
    · rintro (⟨x,hx,rfl⟩|rfl|⟨x,hx,rfl⟩)
      · have := (rank_mem hq _).mp hx
        omega
      · omega
      · have := (rank_mem hp _).mp hx
        omega
    · intro hi
      by_cases iz : i=0
      · exact Or.inr (Or.inl iz)
      by_cases il : i≤n
      · exact Or.inr (Or.inr ⟨i-1,(rank_mem hp _).mpr (by omega),by omega⟩)
      · exact Or.inl ⟨i-(n+1),(rank_mem hq _).mpr (by omega),by omega⟩
  · apply List.Nodup.append
    · exact hnq.map (fun _ _ h ↦ Nat.add_left_cancel h)
    · exact List.nodup_cons.mpr ⟨by simp,hnp.map Nat.succ_injective⟩
    · intro x hx hy
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      rcases List.mem_cons.mp hy with h|h
      · omega
      obtain ⟨j,hj,he⟩ := List.mem_map.mp h
      have := (rank_mem hp j).mp hj
      omega

private theorem ranked_of_bounded {w : Word} (hw : w.Nodup) (bw : Bounded w) :
    Ranked w w.length := by
  have sub : w.toFinset ⊆ range w.length := fun x hx ↦ mem_range.mpr (bw x (by simpa using hx))
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [List.toFinset_card_of_nodup hw])
  apply (List.perm_ext_iff_of_nodup hw List.nodup_range).mpr
  intro x
  simpa using Set.ext_iff.mp (congrArg (fun s : Finset ℕ ↦ (s : Set ℕ)) eq) x

/-- Cutting at the minimum recovers the two consecutive alphabets uniquely. -/
theorem exists_join {w : Word} {n} (hw : Ranked w (n+1)) (avoid : ¬Has213 w) :
    ∃ q p, w=join q p ∧ Ranked q q.length ∧ Ranked p p.length := by
  have zero := (rank_mem hw 0).mpr (by omega)
  obtain ⟨u,v,rfl⟩ := List.mem_iff_append.mp zero
  have nd := hw.nodup_iff.mpr List.nodup_range
  obtain ⟨nu,ncons,dj⟩ := List.nodup_append'.mp nd
  obtain ⟨zv,nv⟩ := List.nodup_cons.mp ncons
  have len := rank_length hw
  simp only [List.length_append,List.length_cons] at len
  have sep : ∀ x∈u, ∀ y∈v, y<x := by
    intro x hx y hy
    have xz : x≠0 := fun h ↦ dj hx (by simp [h])
    have xy : x≠y := fun h ↦ dj hx (by simp [h,hy])
    by_contra! h
    have sa : [x].Sublist u := List.singleton_sublist.mpr hx
    have sb : [y].Sublist v := List.singleton_sublist.mpr hy
    exact avoid ⟨x,0,y,sa.append (sb.cons_cons 0),by omega,by omega⟩
  have lower : ∀ x∈u, v.length<x := by
    intro x hx
    have sub : v.toFinset ⊆ Ico 1 x := by
      intro y hy
      have my : y∈v := by simpa using hy
      exact mem_Ico.mpr ⟨by by_contra! h; exact zv ((by omega : y=0) ▸ my),sep x hx y my⟩
    have h := card_le_card sub
    rw [List.toFinset_card_of_nodup nv,Nat.card_Ico] at h
    have xz : x≠0 := fun h ↦ dj hx (by simp [h])
    omega
  have cover : Icc 1 v.length ⊆ v.toFinset := by
    intro y hy
    obtain ⟨yp,yv⟩ := mem_Icc.mp hy
    have mem := (rank_mem hw y).mpr (by omega)
    rcases List.mem_append.mp mem with mem|mem
    · have := lower y mem
      omega
    rcases List.mem_cons.mp mem with h|h
    · omega
    · simpa using h
  have eq := eq_of_subset_of_card_le cover (by simp [List.toFinset_card_of_nodup nv])
  have bounds (x) (hx : x∈v) : 1≤x ∧ x≤v.length := by
    apply mem_Icc.mp
    rw [eq]
    simpa using hx
  let q := u.map (fun x ↦ x-(v.length+1))
  let p := v.map (fun x ↦ x-1)
  have qnd : q.Nodup := by
    apply nu.map_on
    intro x hx y hy he
    have := lower x hx
    have := lower y hy
    omega
  have pnd : p.Nodup := by
    apply nv.map_on
    intro x hx y hy he
    have := bounds x hx
    have := bounds y hy
    omega
  refine ⟨q,p,?_,ranked_of_bounded qnd ?_,ranked_of_bounded pnd ?_⟩
  · simp only [join,p,q,List.length_map,List.map_map]
    congr 1
    · symm
      exact (List.map_congr_left (fun x hx ↦ (by have := lower x hx; dsimp; omega :
        ((fun y ↦ v.length+1+y) ∘ (fun y ↦ y-(v.length+1))) x = id x))).trans (List.map_id u)
    · congr 1
      symm
      exact (List.map_congr_left (fun x hx ↦ (by have := bounds x hx; dsimp; omega :
        (Nat.succ ∘ (fun y ↦ y-1)) x = id x))).trans (List.map_id v)
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    have xmax := (rank_mem hw x).mp (List.mem_append_left _ hx)
    have xmin := lower x hx
    simp only [q,List.length_map]
    omega
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    have := bounds x hx
    simp only [p,List.length_map]
    omega

private theorem prefix_join (q p : Word) :
    (join q p).takeWhile (fun x ↦ decide (x≠0)) = q.map (fun x ↦ p.length+1+x) := by
  rw [join,List.takeWhile_append_of_pos]
  · simp
  · simp

theorem join_injective : Function.Injective (fun qp : Word × Word ↦ join qp.1 qp.2) := by
  rintro ⟨q,p⟩ ⟨s,t⟩ h
  have pref := congrArg (List.takeWhile (fun x : ℕ ↦ decide (x≠0))) h
  change (join q p).takeWhile _ = (join s t).takeWhile _ at pref
  rw [prefix_join,prefix_join] at pref
  have eqlen := congrArg List.length pref
  simp only [List.length_map] at eqlen
  have tail := List.append_inj_right h (by simpa using eqlen)
  have teq : p=t := by
    have hm : p.map Nat.succ = t.map Nat.succ := List.cons.inj tail |>.2
    exact List.map_injective_iff.mpr Nat.succ_injective hm
  subst t
  have qeq : q=s := List.map_injective_iff.mpr (fun _ _ he ↦ Nat.add_left_cancel he) pref
  simp [qeq]

end ArcherCycles
