module

public import conjectures.MissingSumFringes.Basic

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

def run (n : ℕ) (A : Finset ℕ) (w l : ℕ) : Prop :=
  w+l≤width n ∧ ∀ x, w≤x → x<w+l → x∈A+A

/-- The left endpoint of any interval of greatest length in the sumset. -/
def longest (n : ℕ) (A : Finset ℕ) (w : ℕ) : Prop :=
  ∃ l, run n A w l ∧ ∀ v j, run n A v j → j≤l

def admissible (W : ℕ → Finset ℕ → ℕ) : Prop :=
  ∀ n, ∀ A ⊆ range n, longest n A (W n A)

/-- Conjecture 8.2 of Lazarev, Miller and O'Bryant. The inner limit is taken first. -/
def Conjecture : Prop := ∀ W, admissible W → ∃ e : ℕ → ℝ,
  (∀ k, Tendsto (fun n ↦ conditionalMean n k W) atTop (𝓝 (e k))) ∧
  ∃ c : ℝ, 0<c ∧ Tendsto (fun k : ℕ ↦ e k / k) atTop (𝓝 c)

end MissingSumFringes
