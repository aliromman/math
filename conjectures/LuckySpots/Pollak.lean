module

public import conjectures.LuckySpots.Expansion
public import conjectures.LuckySpots.CircleSums

@[expose] public section
namespace LuckySpots
open Finset
open scoped Classical

private theorem first_fit {p : ℕ} {L : List ℕ} (hs : L.Pairwise (·<·)) (hh : fits p L) :
    ∃ x∈L, p≤x ∧ (∀ y∈L, p≤y → x≤y) ∧ ∀ y, y∈park p L ↔ y≠x ∧ y∈L := by
  induction L with
  | nil => simp [fits] at hh
  | cons a as ih =>
    obtain ⟨first,rest⟩ := List.pairwise_cons.mp hs
    by_cases h : p≤a
    · refine ⟨a,by simp,h,?_,?_⟩
      · intro y hy _
        rcases List.mem_cons.mp hy with rfl|hy
        · exact le_rfl
        · exact (first y hy).le
      · intro y
        simp only [park,ite_eq_left h,List.mem_cons]
        constructor
        · exact fun hy ↦ ⟨(first y hy).ne',Or.inr hy⟩
        · exact fun ⟨ne,hm⟩ ↦ hm.resolve_left ne
    · have ht : fits p as := by
        obtain ⟨y,hy,hp⟩ := hh
        exact ⟨y,(List.mem_cons.mp hy).resolve_left (fun eq ↦ h (eq ▸ hp)),hp⟩
      obtain ⟨x,hx,px,minX,memX⟩ := ih rest ht
      refine ⟨x,by simp [hx],px,?_,?_⟩
      · intro y hy py
        exact minX y ((List.mem_cons.mp hy).resolve_left (fun eq ↦ h (eq ▸ py))) py
      · intro y
        have ha := (first x hx).ne
        simp only [park,ite_eq_right h,List.mem_cons,memX]
        grind

namespace Circle

private def fs (m : ℕ) (L : List ℕ) : Finset (Fin m) := univ.filter (·.val∈L)

private theorem mem_fs {m : ℕ} {x : Fin m} {L : List ℕ} : x∈fs m L ↔ x.val∈L := by simp [fs]
private theorem fs_range (m : ℕ) : fs m (List.range m)=univ := by ext x; simp [fs]

private theorem fs_park {m : ℕ} [NeZero m] (p : Fin m) (L : List ℕ)
    (hs : L.Pairwise (·<·)) (hb : ∀ x∈L,x<m) (hh : fits p.val L) :
    fs m (park p.val L)=step (fs m L) p := by
  obtain ⟨x,hx,hp,hl,he⟩ := first_fit hs hh
  let y : Fin m := ⟨x,hb x hx⟩
  have tar : target (fs m L) p=y :=
    target_forward (mem_fs.mpr hx) hp (fun z hz d ↦ hl z (mem_fs.mp hz) d)
  ext z
  simp only [mem_fs,step,tar,mem_erase]
  rw [show z≠y ↔ z.val≠x from not_congr (Fin.ext_iff (a:=z) (b:=y))]
  exact he z.val

private theorem line_misses {j : ℕ} {L : List ℕ} (h : j∉L) (w : List ℕ) : lucky j L w=false := by
  induction w generalizing L with
  | nil => rfl
  | cons p ps ih =>
    have next := ih (show j∉park p L from fun g ↦ h ((park_sublist _ _).subset g))
    simp [lucky,h,next]

/-- The last spot has the same status on the circle and on the line.
While it is free, every preference has an available spot before wrapping. -/
private theorem coupling (b : ℕ) (L : List ℕ) (w : List (Fin (b+1)))
    (hs : L.Pairwise (·<·)) (hb : ∀ x∈L,x<b+1) :
    ((Fin.last b)∈vacancies (fs (b+1) L) w ↔ b∈vacant L (w.map Fin.val)) ∧
    (hit (Fin.last b) (fs (b+1) L) w ↔ lucky b L (w.map Fin.val)=true) := by
  induction w generalizing L with
  | nil => simp [vacancies,mem_fs,hit,lucky]
  | cons p ps ih =>
    by_cases present : b∈L
    · have hh : fits p.val L := ⟨b,present,p.is_le⟩
      have step' := fs_park p L hs hb hh
      have next := ih (park p.val L) (hs.sublist (park_sublist _ _))
        (fun x hx ↦ hb x ((park_sublist _ _).subset hx))
      refine ⟨?_,?_⟩
      · simpa only [vacancies,List.foldl_cons,List.map_cons,vacant_cons,step'] using next.1
      · simp only [hit,←step',next.2,List.map_cons,lucky,mem_fs,Fin.val_last,present,and_true,
          Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,List.contains_iff_mem]
        rw [Fin.ext_iff]
        simp
    · have nh : Fin.last b∉fs (b+1) L := fun h ↦ present (mem_fs.mp h)
      have cv : Fin.last b∉vacancies (fs (b+1) L) (p::ps) := fun h ↦ nh ((vacancies_subset _ _).trans (Subset.refl _) h)
      have lv : b∉vacant L ((p::ps).map Fin.val) := fun h ↦ present ((vacant_sublist _ _).subset h)
      refine ⟨iff_of_false cv lv,iff_of_false (no_hit nh _) ?_⟩
      rw [line_misses present]
      decide

theorem U_value {j l : ℕ} (hj : 0<j) (hl : j≤l) : U j l=K j*(j:ℚ)^l := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have e := lucky_mean (Fin.last b) l hl
  have same (w : List (Fin (b+1))) : hit (Fin.last b) univ w ↔ lastLucky (b+1) (w.map Fin.val) := by
    simpa only [fs_range,Nat.succ_sub_one,lastLucky] using
      (coupling b (List.range (b+1)) w List.pairwise_lt_range (fun _ ↦ List.mem_range.mp)).2
  simp_rw [same] at e
  rw [C_words l (fun w ↦ wt (lastLucky (b+1) w))] at e
  change (b+1:ℕ)*U (b+1) l=_ at e
  push_cast at e
  unfold K
  push_cast
  field_simp at e ⊢
  nlinarith

private theorem vacant_accepted {b k : ℕ} {w : List ℕ} (hw : w∈words (b+1) k) :
    b∈vacant (List.range (b+1)) w ↔ accepted (List.range b) w := by
  have eq : low (b+1) w=w := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true ((mem_words.mp hw).2 x hx)
  have h := (barrier b (List.range b) [] w (fun _ ↦ List.mem_range.mp) (by simp)).1
  simpa only [List.range_succ,eq] using h

private theorem sum_fit (b k : ℕ) :
    W (b+1) k (fun w ↦ wt (accepted (List.range b) w)) =
      W b k (fun w ↦ wt (accepted (List.range b) w)) := by
  simp only [W,wt,Finset.sum_boole]
  apply congrArg (fun s : Finset (List ℕ) ↦ (s.card:ℚ))
  apply Finset.ext
  intro w
  constructor
  · intro a
    obtain ⟨hw,ha⟩ := mem_filter.mp a
    refine mem_filter.mpr ⟨mem_words.mpr ⟨(mem_words.mp hw).1,?_⟩,ha⟩
    intro p hp
    obtain ⟨x,hx,hp⟩ := accepted_letters ha p hp
    exact lt_of_le_of_lt hp (List.mem_range.mp hx)
  · intro a
    obtain ⟨hw,ha⟩ := mem_filter.mp a
    obtain ⟨len,bnd⟩ := mem_words.mp hw
    exact mem_filter.mpr ⟨mem_words.mpr ⟨len,fun x hx ↦ Nat.lt_succ_of_lt (bnd x hx)⟩,ha⟩

theorem accepted_count (b k : ℕ) (hk : k≤b+1) :
    W b k (fun w ↦ wt (accepted (List.range b) w)) =
      ((b+1:ℚ)-k)*(b+1:ℚ)^k/(b+1:ℚ) := by
  have e := vacancy_mean (Fin.last b) k
  have same (w : List (Fin (b+1))) : Fin.last b∈vacancies univ w ↔ b∈vacant (List.range (b+1)) (w.map Fin.val) := by
    simpa only [fs_range] using (coupling b _ w List.pairwise_lt_range (fun _ ↦ List.mem_range.mp)).1
  simp_rw [same] at e
  rw [C_words k (fun w ↦ wt (b∈vacant (List.range (b+1)) w))] at e
  rw [W_congr (fun w hw ↦ show wt (b∈vacant (List.range (b+1)) w)=wt (accepted (List.range b) w) by rw [vacant_accepted hw]),sum_fit] at e
  rw [Nat.cast_sub hk] at e
  push_cast at e
  field_simp
  linarith

end Circle
end LuckySpots
