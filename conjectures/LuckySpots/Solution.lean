module

public import conjectures.LuckySpots.Asymptotics
public import conjectures.LuckySpots.Binomial
public import conjectures.LuckySpots.Global

@[expose] public section
namespace LuckySpots
open Finset

/-- The exact count for the one-based lucky spot j, for every 1 ≤ j ≤ n. -/
theorem closed_formula {n j : ℕ} (hj : 0<j) (hn : j≤n) :
    2*(j:ℚ)*luckyNumber n j = ((j:ℚ)+1)*(n+1:ℚ)^(n-1) -
      ∑ h∈range (j-1),(n.choose h:ℚ)*(j:ℚ)^h*((n-j+1:ℕ):ℚ)^(n-1-h) :=
  binomial_finish hj hn (fun _ h ↦ small_expansion h) (large_expansion hj hn)

theorem resolution : Conjecture := of_closed_formula closed_formula total_card

/-- info: 'LuckySpots.closed_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closed_formula

/-- info: 'LuckySpots.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end LuckySpots
