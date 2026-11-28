module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic

/-! Borg, *Intersecting Systems of Signed Sets*, Conjecture 1.4 (2007). -/

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

/-- An assignment of one label to each element of a support. -/
abbrev Word (B : Finset ι) (k : ℕ) := B → ZMod k

abbrev Family (ι : Type*) (k : ℕ) := (B : Finset ι) → Finset (Word B k)

def Intersecting (F : Finset (Finset ι)) (A : Family ι k) : Prop :=
  ∀ B ∈ F, ∀ b ∈ A B, ∀ C ∈ F, ∀ c ∈ A C,
    ∃ i, ∃ hi : i ∈ B, ∃ hj : i ∈ C, b ⟨i, hi⟩ = c ⟨i, hj⟩

def size (F : Finset (Finset ι)) (A : Family ι k) : ℕ := ∑ B ∈ F, (A B).card

/-- The size of a star with coordinate `i` and any specified label. -/
def degree (F : Finset (Finset ι)) (k : ℕ) (i : ι) : ℕ :=
  ∑ B ∈ F, if i ∈ B then k ^ (B.card - 1) else 0

def IsStar (F : Finset (Finset ι)) (A : Family ι k) : Prop :=
  ∃ i : ι, ∃ a : ZMod k, ∀ B ∈ F, ∀ b : Word B k,
    b ∈ A B ↔ ∃ hi : i ∈ B, b ⟨i, hi⟩ = a

def SameSupports (F : Finset (Finset ι)) (i j : ι) : Prop :=
  ∀ B ∈ F, i ∈ B ↔ j ∈ B

/-- Three coordinates occur together in all supports, and their stars are largest. -/
def Exceptional (F : Finset (Finset ι)) (k : ℕ) : Prop :=
  k = 2 ∧ ∃ i j l : ι, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
    SameSupports F i j ∧ SameSupports F i l ∧ ∀ q : ι, degree F k q ≤ degree F k i

/-- Borg's bound and his classification of the supports with a nonstar maximum. -/
def Conjecture : Prop :=
  ∀ (n k : ℕ) [NeZero k], 2 ≤ k → ∀ F : Finset (Finset (Fin n)),
    F.Nonempty → (∀ B ∈ F, B.Nonempty) →
      (∃ H : Family (Fin n) k, Intersecting F H ∧ IsStar F H ∧
        ∀ A : Family (Fin n) k, Intersecting F A → size F A ≤ size F H) ∧
      ((∃ A : Family (Fin n) k, Intersecting F A ∧ ¬ IsStar F A ∧
          ∀ i : Fin n, degree F k i ≤ size F A) ↔ Exceptional F k)

end BorgSignedSets
