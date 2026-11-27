module

public import conjectures.LuckySpots.Parking

@[expose] public section
namespace LuckySpots
open List

def good (n : ℕ) (u : List ℕ) := u ∈ words n n ∧ vacant (List.range n) u=[]

private theorem range_cut (i b : ℕ) :
    List.range (i+1+b) = List.range i++i::(List.range b).map (i+1+·) := by
  rw [List.range_add, List.range_succ]
  simp

theorem first_empty (i b : ℕ) (w : List ℕ) :
    ((vacant (List.range (i+1+b)) w).head?=some i ↔ good i (low (i+1) w)) ∧
    (good i (low (i+1) w) → ∀ d : ℕ,
      lucky (i+1+d) (List.range (i+1+b)) w = lucky d (List.range b) (high (i+1) w)) := by
  let L := List.range i
  let R := (List.range b).map (i+1+·)
  let u := low (i+1) w
  have hL : ∀ x∈L, x < i := fun _ h ↦ List.mem_range.mp h
  have hR : ∀ x∈R, i < x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    omega
  have B := barrier i L R w hL hR
  have G : good i u ↔ accepted L u ∧ vacant L u=[] := by
    constructor
    · rintro ⟨hu,hv⟩
      have he := (mem_words.mp hu).1
      exact ⟨accepted_iff_length.mpr (by simp [hv,L,he]),hv⟩
    · rintro ⟨ha,hv⟩
      have he := accepted_iff_length.mp ha
      simp [hv,L] at he
      apply And.intro (mem_words.mpr ⟨he,?_⟩) hv
      intro p hp
      obtain ⟨x,hx,hl⟩ := accepted_letters ha p hp
      exact lt_of_le_of_lt hl (hL _ hx)
  rw [range_cut]
  change ((vacant (L++i::R) w).head?=some i ↔ good i u) ∧ _
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro hf
    have hand : i∈vacant (L++i::R) w := List.mem_of_mem_head? (by simp [hf])
    have hA := B.1.mp hand
    have hv := (B.2 hA).1
    rw [hv] at hf
    apply G.mpr ⟨hA,?_⟩
    cases hh : vacant L u with
    | nil => rfl
    | cons x xs =>
      have hmem : x∈vacant L u := by simp [hh]
      have hx := hL x ((vacant_sublist _ _).subset hmem)
      change ((vacant L u)++i::_).head?=some i at hf
      simp [hh] at hf
      omega
  · intro hg
    obtain ⟨ha,hv⟩ := G.mp hg
    have eq := (B.2 ha).1
    change vacant L u=[] at hv
    rw [show vacant L (low (i+1) w)=[] from hv] at eq
    simp [eq]
  · intro hg d
    have ha := (G.mp hg).1
    have eq := (B.2 ha).2 (i+1+d) (by omega)
    rw [upper_eq] at eq
    exact eq.trans (lucky_shift (i+1) d (List.range b) _)

theorem park_self_gone {j : ℕ} {L : List ℕ} (hs : L.Pairwise (·<·)) (hj : j∈L) :
    j∉park j L := by
  induction L with
  | nil => simp at hj
  | cons x xs ih =>
    obtain ⟨hx,hr⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hj with rfl|hj
    · simp [park]
      exact fun hh ↦ lt_irrefl _ (hx _ hh)
    · have he := hx _ hj
      simp [park,he.not_ge,he.ne',ih hr hj]

theorem not_lucky_of_vacant {j : ℕ} {L w : List ℕ} (hs : L.Pairwise (·<·))
    (h : j∈vacant L w) : lucky j L w=false := by
  induction w generalizing L with
  | nil => rfl
  | cons p ps ih =>
    have ha : j∈park p L := (vacant_sublist _ _).subset h
    have hrec := ih (hs.sublist (park_sublist p L)) h
    by_cases e : p=j
    · subst p
      exact False.elim (park_self_gone hs ((park_sublist j L).subset ha) ha)
    · simp [lucky,e,hrec]

end LuckySpots
