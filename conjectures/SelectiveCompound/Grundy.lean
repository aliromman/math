module

public import conjectures.SelectiveCompound.Statement

public section
namespace SelectiveCompound.Game
variable {α : Type*} (G : Game α)

@[expose] def Attains (p : α × ℕ) (n : ℕ) : Prop :=
  ∃ q, G.Option p q ∧ G.grundy q = n

theorem mex_eq (p : α × ℕ) : G.grundy p = sInf {n | ¬ G.Attains p n} := by
  rw [grundy]
  simp [Attains]

theorem bounds (p : α × ℕ) :
    ¬ G.Attains p (G.depth p.1 + p.2) ∧ G.grundy p ≤ G.depth p.1 + p.2 := by
  have absent : ¬ G.Attains p (G.depth p.1 + p.2) := by
    rintro ⟨q, move, hit⟩
    have bound := (bounds q).2
    have smaller := G.option_decreases move
    omega
  exact ⟨absent, (G.mex_eq p).trans_le (Nat.sInf_le absent)⟩
termination_by G.depth p.1 + p.2
decreasing_by exact G.option_decreases ‹_›

theorem excluded (p : α × ℕ) : ¬ G.Attains p (G.grundy p) := by
  rw [G.mex_eq p]
  exact Nat.sInf_mem (s := {n | ¬ G.Attains p n}) ⟨_, (G.bounds p).1⟩

theorem reaches {p : α × ℕ} {n : ℕ} (h : n < G.grundy p) : G.Attains p n := by
  by_contra missing
  have := (G.mex_eq p).trans_le (Nat.sInf_le (s := {n | ¬ G.Attains p n}) missing)
  omega

theorem increase (a : α) {k l : ℕ} (h : k < l) :
    G.grundy (a,k) < G.grundy (a,l) := by
  by_contra! le
  apply G.excluded (a,l)
  obtain eq | lt := eq_or_lt_of_le le
  · exact ⟨(a,k), Or.inl ⟨rfl,h⟩, eq.symm⟩
  · obtain ⟨q, move, hit⟩ := G.reaches lt
    refine ⟨q, ?_, hit⟩
    obtain ⟨same,short⟩ | ⟨legal,short⟩ := move
    · exact Or.inl ⟨same, lt_trans short h⟩
    · exact Or.inr ⟨legal, (lt_of_le_of_lt short h).le⟩

theorem heap_le (a : α) (k : ℕ) : k ≤ G.grundy (a,k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (G.increase a (Nat.lt_succ_self k)))

theorem offset_mono (a : α) {i k : ℕ} (h : i ≤ k) :
    G.grundy (a,i) + k ≤ G.grundy (a,k) + i := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    have step : G.grundy (a,k) < G.grundy (a,k+1) := G.increase a (Nat.lt_succ_self k)
    omega

theorem mex_le {p : α × ℕ} {n : ℕ} (h : ¬ G.Attains p n) : G.grundy p ≤ n :=
  (G.mex_eq p).trans_le (Nat.sInf_le (s := {n | ¬ G.Attains p n}) h)

end SelectiveCompound.Game
