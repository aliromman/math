module

public import conjectures.KurzBanzhaf.Seeds
import Mathlib.Tactic.IntervalCases

public section
namespace KurzBanzhaf

/-- Two starting rules cover the two parities. -/
private theorem repeatable (n : ℕ) (hn : 9≤n) : Profile n true := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases large : 11≤n
      · have eq : n-2+2=n := by omega
        exact eq ▸ Seeds.extend (ih (n-2) (by omega) (by omega))
      · interval_cases n
        · exact Seeds.seed9
        · exact Seeds.seed10

theorem resolution : Conjecture := by
  intro n hn
  apply Profile.vector hn
  by_cases h : 9≤n
  · exact (repeatable n h).forget
  · interval_cases n
    · exact Seeds.seed6
    · exact Seeds.seed7
    · exact Seeds.seed8

/-- info: 'KurzBanzhaf.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end KurzBanzhaf
