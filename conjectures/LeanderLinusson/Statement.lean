module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace LeanderLinusson
open Finset

/-- A sample lists the tail and head of each of the `m` directed edges. -/
abbrev Sample (V : Type*) (m : ℕ) := Fin m × Bool → V

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

def Valid (g : Sample V m) : Prop :=
  (∀ i, g (i, false) ≠ g (i, true)) ∧ ∀ i j, i ≠ j →
    (g (i, false), g (i, true)) ≠ (g (j, false), g (j, true)) ∧
    (g (i, false), g (i, true)) ≠ (g (j, true), g (j, false))

instance (g : Sample V m) : Decidable (Valid g) := by
  unfold Valid
  infer_instance

def samples (V : Type*) [Fintype V] [DecidableEq V] (m : ℕ) : Finset (Sample V m) :=
  univ.filter Valid

/-- Induction on the length adds the heads of all edges from the current set. -/
def reached (g : Sample V m) (s : V) : ℕ → Finset V
  | 0 => {s}
  | l+1 =>
    let prev := reached g s l
    prev ∪ ((univ.filter fun i ↦ g (i, false) ∈ prev).image fun i ↦ g (i, true))

def PathEvent (g : Sample V m) (s a : V) : Prop := a ∈ reached g s (Fintype.card V)

instance (g : Sample V m) (s a : V) : Decidable (PathEvent g s a) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Each oriented graph with `m` edges occurs in exactly `m!` orders. -/
noncomputable def probability (V : Type*) [Fintype V] [DecidableEq V] (m : ℕ)
    (P : Sample V m → Prop) [DecidablePred P] : ℝ :=
  ((samples V m).filter P).card / ((samples V m).card : ℝ)

noncomputable def covariance (V : Type*) [Fintype V] [DecidableEq V] (m : ℕ) (s a t b : V) : ℝ :=
  probability V m (fun g ↦ PathEvent g s a ∧ PathEvent g t b) -
    probability V m (fun g ↦ PathEvent g s a) * probability V m (fun g ↦ PathEvent g t b)

/-- The paper uses the complementary events that the two paths are absent. -/
noncomputable def failureCovariance (V : Type*) [Fintype V] [DecidableEq V]
    (m : ℕ) (s a t b : V) : ℝ :=
  probability V m (fun g ↦ ¬PathEvent g s a ∧ ¬PathEvent g t b) -
    probability V m (fun g ↦ ¬PathEvent g s a) * probability V m (fun g ↦ ¬PathEvent g t b)

/-- Conjecture 2 concerns the uniform fixed-edge model and four distinct vertices. -/
def Conjecture : Prop :=
  ∀ n ≥ 4, ∀ m, m ≤ n.choose 2 → ∀ s a t b : Fin n,
    [s,a,t,b].Nodup → 0 < failureCovariance (Fin n) m s a t b

end LeanderLinusson
