module

public import conjectures.LuckySpots.WordSums

@[expose] public section
namespace LuckySpots
open List

/-- A car with this preference has a vacant place within reach. -/
def fits (p : ℕ) (free : List ℕ) := ∃ x∈free,p≤x

/-- Every car in the given list can park. -/
def accepted : List ℕ → List ℕ → Prop
  | _, [] => True
  | free,p::ps => fits p free ∧ accepted (park p free) ps

@[simp] theorem vacant_nil (free : List ℕ) : vacant free [] = free := rfl
@[simp] theorem vacant_cons (free : List ℕ) (p : ℕ) (ps : List ℕ) :
    vacant free (p::ps) = vacant (park p free) ps := rfl

theorem park_sublist (p : ℕ) (free : List ℕ) : park p free <+ free := by
  induction free with
  | nil => simp [park]
  | cons x xs ih =>
    by_cases h : p≤x
    · simp [park,h]
    · simpa [park,h] using ih.cons_cons x

theorem vacant_sublist (free ps : List ℕ) : vacant free ps <+ free := by
  induction ps generalizing free with
  | nil => simp
  | cons p ps ih => exact (ih _).trans (park_sublist _ _)

theorem park_misses {p : ℕ} {L : List ℕ} (h : ¬fits p L) : park p L=L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : ¬p≤x := fun hx ↦ h ⟨x,by simp,hx⟩
    have hs : ¬fits p xs := fun ⟨y,hy,he⟩ ↦ h ⟨y,by simp [hy],he⟩
    simp [park,hx,ih hs]

theorem park_length {p : ℕ} {L : List ℕ} (h : fits p L) :
    (park p L).length+1=L.length := by
  induction L with
  | nil => simp [fits] at h
  | cons x xs ih =>
    by_cases hx : p≤x
    · simp [park,hx]
    · have hs : fits p xs := by
        obtain ⟨y,hy,he⟩ := h
        have hne : y≠x := fun e ↦ hx (e ▸ he)
        exact ⟨y,(List.mem_cons.mp hy).resolve_left hne,he⟩
      simp [park,hx,ih hs]

theorem vacant_capacity (L w : List ℕ) : L.length ≤ (vacant L w).length+w.length := by
  induction w generalizing L with
  | nil => simp
  | cons p ps ih =>
    have step := ih (park p L)
    by_cases h : fits p L
    · have e := park_length h
      simp only [vacant_cons,List.length_cons]
      omega
    · simp [park_misses h] at step ⊢
      omega

theorem accepted_iff_length {L w : List ℕ} :
    accepted L w ↔ (vacant L w).length+w.length=L.length := by
  induction w generalizing L with
  | nil => simp [accepted]
  | cons p ps ih =>
    by_cases h : fits p L
    · simp only [accepted,h,true_and,vacant_cons,List.length_cons,ih]
      have e := park_length h
      omega
    · have cap := vacant_capacity L ps
      simp only [accepted,h,false_and,vacant_cons,List.length_cons,park_misses h,false_iff]
      omega

theorem accepted_letters {L w : List ℕ} (h : accepted L w) :
    ∀ p∈w, fits p L := by
  induction w generalizing L with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha,hs⟩ := h
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ha
    · obtain ⟨x,hx,he⟩ := ih hs p hp
      exact ⟨x,(park_sublist _ _).subset hx,he⟩

theorem park_append_hit {p : ℕ} {L : List ℕ} (h : fits p L) (R : List ℕ) :
    park p (L++R)=park p L++R := by
  induction L with
  | nil => simp [fits] at h
  | cons x xs ih =>
    by_cases hx : p≤x
    · simp [park,hx]
    · obtain ⟨y,hy,he⟩ := h
      have hs : fits p xs := ⟨y,(List.mem_cons.mp hy).resolve_left (fun e ↦ hx (e ▸ he)),he⟩
      simp [park,hx,ih hs]

theorem park_append_miss {p : ℕ} {L : List ℕ} (h : ¬fits p L) (R : List ℕ) :
    park p (L++R)=L++park p R := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : ¬p≤x := fun hx ↦ h ⟨x,by simp,hx⟩
    have hs : ¬fits p xs := fun ⟨y,hy,he⟩ ↦ h ⟨y,by simp [hy],he⟩
    simp [park,hx,ih hs]

/-- The letters at or above the cut, with their original labels. -/
def upper (m : ℕ) (w : List ℕ) := w.filter (m≤·)

theorem upper_eq (m : ℕ) (w : List ℕ) : upper m w=(high m w).map (m+·) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    by_cases h : m≤a
    · simpa [upper,high,h,Nat.add_sub_of_le h] using congrArg (a::·) ih
    · simpa [upper,high,h] using ih

theorem park_shift (d p : ℕ) (L : List ℕ) :
    park (d+p) (L.map (d+·)) = (park p L).map (d+·) := by
  induction L with
  | nil => rfl
  | cons x xs ih => by_cases h : p≤x <;> simp [park,h,ih]

theorem vacant_shift (d : ℕ) (L w : List ℕ) :
    vacant (L.map (d+·)) (w.map (d+·)) = (vacant L w).map (d+·) := by
  induction w generalizing L with
  | nil => rfl
  | cons p ps ih => simp [park_shift,ih]

theorem lucky_shift (d j : ℕ) (L w : List ℕ) :
    lucky (d+j) (L.map (d+·)) (w.map (d+·)) = lucky j L w := by
  induction w generalizing L with
  | nil => rfl
  | cons p ps ih =>
    simp [lucky,park_shift,ih]

/-- A vacant separator survives precisely when all the lower preferences fit to its left.
In that case the two sides run independently. -/
theorem barrier (i : ℕ) (L R w : List ℕ) (hL : ∀ x ∈ L, x < i) (hR : ∀ x ∈ R, i < x) :
    (i∈vacant (L++i::R) w ↔ accepted L (low (i+1) w)) ∧
    (accepted L (low (i+1) w) →
      vacant (L++i::R) w = vacant L (low (i+1) w) ++ i :: vacant R (upper (i+1) w) ∧
      ∀ j, i<j → lucky j (L++i::R) w=lucky j R (upper (i+1) w)) := by
  induction w generalizing L R with
  | nil => simp [low,upper,accepted,lucky]
  | cons p ps ih =>
    by_cases hp : p < i+1
    · have hn : ¬i+1≤p := by omega
      simp only [low, List.filter_cons_of_pos (p:=fun z : ℕ ↦ decide (z < i+1)) (by simpa using hp),
        upper, List.filter_cons_of_neg (p:=fun z : ℕ ↦ decide (i+1≤z)) (by simpa using hn),accepted,
        vacant_cons]
      change (i∈vacant (park p (L++i::R)) ps ↔ fits p L ∧ accepted (park p L) (low (i+1) ps)) ∧ _
      by_cases hit : fits p L
      · rw [park_append_hit hit]
        have A := ih (park p L) R (fun x hx ↦ hL x ((park_sublist _ _).subset hx)) hR
        refine ⟨by simpa [hit] using A.1,?_⟩
        rintro ⟨_,hs⟩
        refine ⟨(A.2 hs).1,fun j hj ↦ ?_⟩
        have hn : p≠j := by omega
        simpa [lucky,hn,park_append_hit hit,upper] using (A.2 hs).2 j hj
      · rw [park_append_miss hit]
        have hi : p ≤ i := by omega
        have no : i∉vacant (L++R) ps := by
          intro hh
          rcases List.mem_append.mp ((vacant_sublist _ _).subset hh) with h|h
          · exact lt_irrefl _ (hL _ h)
          · exact lt_irrefl _ (hR _ h)
        simp [park,hi,hit,no]
    · have hh : i+1≤p := by omega
      have miss : ¬fits p L := by
        rintro ⟨x,hx,he⟩
        have := hL x hx
        omega
      have pni : ¬p ≤ i := by omega
      have ep : park p (L++i::R)=L++i::park p R := by simp [park_append_miss miss,park,pni]
      have A := ih L (park p R) hL (fun x hx ↦ hR x ((park_sublist _ _).subset hx))
      simp only [low, List.filter_cons_of_neg (p:=fun z : ℕ ↦ decide (z < i+1)) (by simpa using hp),
        upper, List.filter_cons_of_pos (p:=fun z : ℕ ↦ decide (i+1≤z)) (by simpa using hh),
        vacant_cons,ep]
      refine ⟨A.1, fun hs ↦ ⟨(A.2 hs).1,fun j hj ↦ ?_⟩⟩
      have nj : j∉L := fun h ↦ (hL j h).asymm hj
      have jne : j≠i := by omega
      simp only [lucky,ep,(A.2 hs).2 j hj]
      have eqb : (L++i::R).contains j=R.contains j := by
        simp [nj,jne]
      rw [eqb]
      rfl

end LuckySpots
