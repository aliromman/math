module

public import conjectures.FangSubwordLength.Statement
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.Fintype.Sum

@[expose] public section

namespace FangSubwordLength

variable {α β : Type*}

def join (a : List α) (b : List β) : List (α ⊕ β) :=
  a.map Sum.inl ++ b.map Sum.inr

def UniqueMode [BEq α] (w v : List α) : Prop :=
  ∀ u, u ≠ v → occurrences w u < occurrences w v

private def combine (p : List β × List α) : List (α ⊕ β) := join p.2 p.1

private theorem combine_injective : Function.Injective (combine (α := α) (β := β)) := by
  rintro ⟨u,v⟩ ⟨u',v'⟩ h
  have h1 := congrArg (List.filterMap Sum.getLeft?) h
  have h2 := congrArg (List.filterMap Sum.getRight?) h
  simp [combine, join, List.filterMap_map, Function.comp_def] at h1 h2
  exact Prod.ext h2 h1

private theorem sublists_join (a : List α) (b : List β) :
    (join a b).sublists = (b.sublists.product a.sublists).map combine := by
  simp [join, combine, List.sublists_append, List.sublists_map, List.product,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

private theorem count_product [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a : List α) (b : List β) (x : α) (y : β) :
    (a.product b).count (x,y) = a.count x * b.count y := by
  induction a with
  | nil => simp [List.product]
  | cons z a ih =>
    change (b.map (Prod.mk z) ++ a.product b).count (x,y) = _
    rw [List.count_append, ih]
    by_cases h : z = x
    · subst z
      have hmap := List.count_map_of_injective b (Prod.mk x) (fun _ _ e => (Prod.mk.inj e).2) y
      simp [hmap, Nat.add_mul, Nat.add_comm]
    · have hn : (x,y) ∉ b.map (Prod.mk z) := by simp [h]
      simp [List.count_eq_zero.mpr hn, h]

theorem occurrences_join [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (a u : List α) (b v : List β) :
    occurrences (join a b) (join u v) = occurrences a u * occurrences b v := by
  unfold occurrences
  rw [sublists_join]
  change List.count (combine (v,u)) _ = _
  rw [List.count_map_of_injective _ _ combine_injective, count_product, Nat.mul_comm]

private theorem uniqueMode_le [BEq α] [LawfulBEq α] {w v : List α} (h : UniqueMode w v)
    (u : List α) : occurrences w u ≤ occurrences w v := by
  by_cases he : u = v
  · exact he ▸ le_rfl
  · exact (h u he).le

theorem uniqueMode_join [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a u : List α} {b v : List β}
    (h₁ : UniqueMode a u) (h₂ : UniqueMode b v)
    (p₁ : 0 < occurrences a u) (p₂ : 0 < occurrences b v) :
    UniqueMode (join a b) (join u v) := by
  intro z hz
  rw [occurrences_join]
  by_cases hmem : z ∈ (join a b).sublists
  · rw [sublists_join] at hmem
    obtain ⟨⟨v',u'⟩,_,rfl⟩ := List.mem_map.mp hmem
    change occurrences (join a b) (join u' v') < _
    rw [occurrences_join]
    by_cases hu : u' = u
    · subst u'
      have hv : v' ≠ v := by intro e; apply hz; rw [e]; rfl
      exact Nat.mul_lt_mul_of_pos_left (h₂ _ hv) p₁
    · exact (Nat.mul_le_mul_left _ (uniqueMode_le h₂ v')).trans_lt
        (Nat.mul_lt_mul_of_pos_right (h₁ _ hu) p₂)
  · rw [show occurrences (join a b) z = 0 from List.count_eq_zero.mpr hmem]
    exact Nat.mul_pos p₁ p₂

def block : List Bool := [false,true,false,true,false]
def motif : List Bool := [false,true,false]

private theorem block_frequency : occurrences block motif = 4 := by decide

theorem block_mode : UniqueMode block motif := by
  have table : ∀ u ∈ block.sublists, u ≠ motif → occurrences block u < 4 := by decide
  intro u hu
  rw [block_frequency]
  by_cases h : u ∈ block.sublists
  · exact table _ h hu
  · rw [show occurrences block u = 0 from List.count_eq_zero.mpr h]
    decide

/-- The gap above the proposed length bound grows without limit as the alphabet grows. -/
theorem block_family (r : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (_ : BEq α) (_ : LawfulBEq α) (w v : List α),
      w.length = 5*r ∧ v.length = 3*r ∧ occurrences w v = 4^r ∧ UniqueMode w v := by
  induction r with
  | zero =>
    refine ⟨Unit,inferInstance,inferInstance,inferInstance,[],[],rfl,rfl,rfl,?_⟩
    intro u hu
    cases u with
    | nil => contradiction
    | cons a u => simp [occurrences]
  | succ r ih =>
    obtain ⟨α,I,E,L,w,v,hw,hv,hf,hm⟩ := ih
    let _ := I
    let _ := E
    let _ := L
    refine ⟨α ⊕ Bool,inferInstance,inferInstance,inferInstance,join w block,join v motif,?_,?_,?_,?_⟩
    · simp [join, block, hw, Nat.mul_succ]
    · simp [join, motif, hv, Nat.mul_succ]
    · rw [occurrences_join, hf, block_frequency, pow_succ]
    · exact uniqueMode_join hm block_mode (hf ▸ Nat.pow_pos (by decide)) (by decide)

def binaryWord : List Bool :=
  [false,true,false,true,false,false,false,true,true,true,false,true,false,true]

def binaryMotif : List Bool := [false,true,false,false,true,true,false,true]

private def countFast : List Bool → List Bool → ℕ
  | [], v => if v.isEmpty then 1 else 0
  | _ :: _, [] => 1
  | a :: w, b :: v => countFast w (b :: v) + if a = b then countFast w v else 0

private theorem countFast_spec (w v : List Bool) : countFast w v = occurrences w v := by
  induction w generalizing v with
  | nil => cases v <;> rfl
  | cons a w ih =>
    unfold occurrences
    rw [(List.sublists_cons_perm_append a w).count_eq v, List.count_append]
    cases v with
    | nil =>
      have h : ([] : List Bool) ∉ List.map (List.cons a) w.sublists := by simp
      have he : countFast w [] = 1 := by cases w <;> rfl
      simpa [countFast, List.count_eq_zero.mpr h, occurrences, he] using ih []
    | cons b v =>
      by_cases he : a = b
      · subst b
        rw [List.count_map_of_injective _ (List.cons a) (fun _ _ e => (List.cons.inj e).2) v]
        simp [countFast, ih, occurrences]
      · have h : b :: v ∉ List.map (List.cons a) w.sublists := by simp [he]
        simp [countFast, ih, occurrences, he, List.count_eq_zero.mpr h]

theorem binary_frequency : occurrences binaryWord binaryMotif = 144 := by
  rw [← countFast_spec]
  decide +kernel

private def after (a : Bool) : List Bool → Option (List Bool)
  | [] => none
  | b :: w => if a = b then some w else after a w

private def candidates : ℕ → List Bool → List (List Bool)
  | 0, _ => [[]]
  | n+1, w => [] :: [false,true].flatMap fun a =>
    (after a w).toList.flatMap fun t => (candidates n t).map (List.cons a)

private theorem after_sub {a : Bool} {u w : List Bool} (h : (a :: u).Sublist w) :
    ∃ t, after a w = some t ∧ u.Sublist t := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    by_cases e : a = b
    · subst b
      exact ⟨w,by simp [after],List.cons_sublist_cons.mp h⟩
    · have h' := (List.cons_sublist_cons'.mp h).resolve_right (fun h => e h.1)
      obtain ⟨t,ht,hu⟩ := ih h'
      exact ⟨t,by simpa [after,e] using ht,hu⟩

private theorem mem_candidates {n : ℕ} {w u : List Bool} (h : u.Sublist w) (hl : u.length ≤ n) :
    u ∈ candidates n w := by
  induction n generalizing u w with
  | zero =>
    have he : u = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he,candidates]
  | succ n ih =>
    cases u with
    | nil => simp [candidates]
    | cons a u =>
      obtain ⟨t,ht,hu⟩ := after_sub h
      simp only [candidates, List.mem_cons, List.mem_flatMap, List.mem_map]
      right
      refine ⟨a,by cases a <;> simp, t,by simp [ht], u,ih hu (by simpa using hl),rfl⟩

set_option maxHeartbeats 0 in
private theorem binary_table : ∀ v ∈ candidates 14 binaryWord,
    (v ≠ binaryMotif → countFast binaryWord v < 144) ∧
    (v.length ≤ 7 → countFast binaryWord v ≤ 136) := by decide +kernel

theorem binary_unique : UniqueMode binaryWord binaryMotif := by
  intro u hu
  rw [binary_frequency]
  by_cases hm : u ∈ binaryWord.sublists
  · rw [← countFast_spec]
    exact (binary_table u (mem_candidates (List.mem_sublists.mp hm) (List.mem_sublists.mp hm).length_le)).1 hu
  · rw [show occurrences binaryWord u = 0 from List.count_eq_zero.mpr hm]
    decide

theorem binary_short_bound {u : List Bool} (hu : u.length ≤ 7) :
    occurrences binaryWord u ≤ 136 := by
  by_cases hm : u ∈ binaryWord.sublists
  · rw [← countFast_spec]
    exact (binary_table u (mem_candidates (List.mem_sublists.mp hm) (List.mem_sublists.mp hm).length_le)).2 hu
  · rw [show occurrences binaryWord u = 0 from List.count_eq_zero.mpr hm]
    decide

theorem binary_short_maximum :
    occurrences binaryWord [false,true,false,true,false,true] = 136 := by
  rw [← countFast_spec]
  decide +kernel

theorem not_conjecture : ¬ Conjecture := by
  intro h
  obtain ⟨v,hv,hL⟩ := h (Bool ⊕ Bool) (join block block) (by decide)
  have hu := uniqueMode_join block_mode block_mode
    (show 0 < occurrences block motif by decide) (show 0 < occurrences block motif by decide)
  have he : v = join motif motif := by
    by_contra hn
    exact (Nat.not_lt_of_ge (hv (join motif motif))) (hu v hn)
  subst v
  exact (by decide : ¬ (join motif motif).length ≤ ((join block block).length + 1) / 2) hL

/-- info: 'FangSubwordLength.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end FangSubwordLength
