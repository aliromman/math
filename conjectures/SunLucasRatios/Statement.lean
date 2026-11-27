module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section

namespace SunLucasRatios

/-- The Lucas sequence with parameters `a` and `b`. -/
def lucas (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * lucas a b (n + 1) - b * lucas a b n

noncomputable def root (u : ℕ → ℤ) (n : ℕ) : ℝ := (u n : ℝ) ^ (n : ℝ)⁻¹

noncomputable def ratio (u : ℕ → ℤ) (n : ℕ) : ℝ := root u (n + 1) / root u n

/-- Conjecture 3.1 in Sun, *Conjectures involving arithmetical sequences* (2013). -/
def Conjecture : Prop :=
  StrictMonoOn (root (fun n => Nat.fib n)) (Set.Ici 2) ∧
  StrictAntiOn (ratio (fun n => Nat.fib n)) (Set.Ici 4) ∧
  ∀ a b : ℤ, 1 < a → b ≠ 0 → 4 * b < a ^ 2 → (2 < a ∨ -9 ≤ b) →
    StrictAntiOn (ratio (lucas a b)) (Set.Ici 4) ∧
    Filter.Tendsto (ratio (lucas a b)) Filter.atTop (nhds 1)

end SunLucasRatios
