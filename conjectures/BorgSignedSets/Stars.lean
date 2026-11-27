module

public import conjectures.BorgSignedSets.WordCount

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} [DecidableEq ι] {k : ℕ} [NeZero k]

/-- All signed sets with the specified coordinate and label. -/
def star (i : ι) (a : ZMod k) : Family ι k := fun B =>
  if hi : i ∈ B then Finset.univ.filter (fun b => b ⟨i, hi⟩ = a) else ∅

theorem mem_star (i : ι) (a : ZMod k) (B : Finset ι) (b : Word B k) :
    b ∈ star i a B ↔ ∃ hi : i ∈ B, b ⟨i, hi⟩ = a := by
  by_cases hi : i ∈ B <;> simp [star, hi]

theorem star_intersecting (F : Finset (Finset ι)) (i : ι) (a : ZMod k) :
    Intersecting F (star i a) := by
  intro B _ b hb C _ c hc
  obtain ⟨hi, he⟩ := (mem_star i a B b).mp hb
  obtain ⟨hj, hf⟩ := (mem_star i a C c).mp hc
  exact ⟨i, hi, hj, he.trans hf.symm⟩

theorem size_star (F : Finset (Finset ι)) (i : ι) (a : ZMod k) :
    size F (star i a) = degree F k i := by
  classical
  apply Finset.sum_congr rfl
  intro B _
  by_cases hi : i ∈ B
  · let j : B := ⟨i, hi⟩
    let C : Finset B := {j}
    let b : Word C k := fun _ => a
    have he : star i a B = extensions C {b} := by
      ext x
      rw [mem_star, mem_extensions, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hx⟩
        funext c
        have hj : c.val = j := Finset.mem_singleton.mp c.property
        exact (congrArg x hj).trans hx
      · intro hx
        exact ⟨hi, congrFun hx ⟨j, Finset.mem_singleton_self _⟩⟩
    rw [he, card_extensions]
    simp [C, hi]
  · simp [star, hi]

end BorgSignedSets
