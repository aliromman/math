module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section
namespace LuckySpots
open Finset Filter Polynomial
open scoped Topology Classical

/-- All lists of k preferences in an alphabet of m parking spots, numbered from zero. -/
def words (m : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k+1 => ((range m) ×ˢ (words m k)).map
    ⟨fun p ↦ p.1::p.2, fun ⟨_,_⟩ ⟨_,_⟩ h ↦ by simpa using h⟩

/-- Remove the first available spot at or beyond the preferred position. -/
def park (p : ℕ) : List ℕ → List ℕ
  | [] => []
  | u::us => if p≤u then us else u::park p us

def vacant (free prefs : List ℕ) : List ℕ := prefs.foldl (fun v p ↦ park p v) free

/-- A spot is lucky when a car prefers that spot while it is still available. -/
def lucky (j : ℕ) : List ℕ → List ℕ → Bool
  | _, [] => false
  | free, p::ps => (p=j && free.contains j) || lucky j (park p free) ps

/-- Count successful words for which the one-based spot j is lucky. -/
def luckyNumber (n j : ℕ) : ℕ :=
  ((words n n).filter fun w ↦ vacant (List.range n) w=[] ∧ lucky (j-1) (List.range n) w).card

def totalNumber (n : ℕ) : ℕ := ((words n n).filter fun w ↦ vacant (List.range n) w=[]).card

/-- The first spot is always lucky. Every later fixed spot has the stated polynomial
count and limiting probability (Butler et al., Conjecture 13). -/
def Conjecture : Prop := (∀ n, 0<n → luckyNumber n 1 = totalNumber n) ∧
  ∀ j : ℕ, 2≤j → ∃ f : ℚ[X], f.natDegree=j-2 ∧
    (∀ n, j≤n → (luckyNumber n j:ℚ) =
      ((j:ℚ)+1)/(2*j) * (n+1:ℚ)^(n-1) - f.eval (n:ℚ) *((n-j+1:ℕ):ℚ)^(n-j+1)) ∧
    ∃ c : ℚ, Tendsto (fun n : ℕ ↦ (luckyNumber n j:ℝ)/totalNumber n) atTop
      (𝓝 (((j:ℝ)+1)/(2*j)-(c:ℝ)*Real.exp (-(j:ℝ))))

end LuckySpots
