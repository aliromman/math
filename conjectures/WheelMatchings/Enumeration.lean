module

public import conjectures.WheelMatchings.Statement

public section

namespace WheelMatchings

/-- A perfect matching lists the partner of each first remaining vertex. -/
inductive Pairs {α : Type} [DecidableEq α] : List α → List (Edge α) → Prop
  | nil : Pairs [] []
  | cons {a b : α} {tail : List α} {M} (hb : b ∈ tail) (rest : Pairs (tail.erase b) M) :
      Pairs (a :: tail) ((a,b) :: M)

theorem mem_matchings {α : Type} [DecidableEq α] {m : ℕ} {xs : List α} {M : List (Edge α)} :
    M ∈ matchings m xs ↔ Pairs xs M ∧ M.length = m := by
  induction m generalizing xs M with
  | zero =>
    cases xs with
    | nil =>
      constructor
      · simp only [matchings, List.mem_singleton]
        rintro rfl
        exact ⟨.nil, rfl⟩
      · rintro ⟨h, _⟩
        cases h
        simp [matchings]
    | cons a xs =>
      constructor
      · simp [matchings]
      · rintro ⟨h, hm⟩
        cases h
        simp at hm
  | succ m ih =>
    cases xs with
    | nil =>
      constructor
      · simp [matchings]
      · rintro ⟨h, hm⟩
        cases h
        simp at hm
    | cons a xs =>
      simp only [matchings, List.mem_flatMap, List.mem_map, ih]
      constructor
      · rintro ⟨b, hb, M, ⟨h, hm⟩, rfl⟩
        exact ⟨.cons hb h, by simp [hm]⟩
      · rintro ⟨h, hm⟩
        cases h with
        | cons hb h => exact ⟨_, hb, _, ⟨h, by simpa using hm⟩, rfl⟩

theorem matchings_nodup {α : Type} [DecidableEq α] {xs : List α} (h : xs.Nodup) (m : ℕ) :
    (matchings m xs).Nodup := by
  induction m generalizing xs with
  | zero => cases xs <;> simp [matchings]
  | succ m ih =>
    cases xs with
    | nil => simp [matchings]
    | cons a xs =>
      rw [matchings, List.nodup_flatMap]
      refine ⟨fun b _ ↦ (ih ((List.nodup_cons.mp h).2.erase b)).map (fun _ _ he ↦ (List.cons.inj he).2), ?_⟩
      apply (List.nodup_cons.mp h).2.imp
      intro b c hbc M h₁ h₂
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨_, _, he⟩ := List.mem_map.mp h₂
      exact hbc (Prod.mk.inj (List.cons.inj he).1).2.symm

end WheelMatchings
