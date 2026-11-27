module

public import conjectures.FeketeEquidistribution.Sieve
public import conjectures.FeketeEquidistribution.Frequencies
import Mathlib.Tactic.NormNum.Prime

public section
namespace FeketeEquidistribution
open Polynomial
private abbrev primes : List ℕ := [3,37,67,151]

private theorem factors : PrimeFactors primes := by
  norm_num [primes,PrimeFactors,List.prod, Nat.Coprime]

private theorem frequencies (s : ℕ) : residueCount 1122987 63 s =
    fastCount primes 1122987 63 1 (s%63) := residue_eq_fast factors 63 s

/-- One period of the residue frequencies for the odd counterexample. -/
def row (r : ℕ) : ℕ :=
  if r%3=0 then 0 else if r ∈ ([1,2,5,7,10,11] : List ℕ) then 16972 else 16971

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem table : ∀ i : Fin 63, fastCount primes 1122987 63 1 i.val = row (i.val%21) := by decide

theorem odd_frequency (i : ℕ) (hi : i<63) : residueCount 1122987 63 i = row (i%21) := by
  rw [frequencies,Nat.mod_eq_of_lt hi]
  exact table ⟨i,hi⟩

theorem odd_factor : cyclotomic 63 ℤ ∣ fekete 1122987 := by
  apply factor_of_period (m:=3) (t:=21) (by decide) (by decide) (by decide)
  intro i hi
  rw [odd_frequency i hi,odd_frequency (i%21) (by omega),Nat.mod_mod]

theorem odd_witness : Squarefree 1122987 ∧ Odd 1122987 ∧
    cyclotomic 63 ℤ ∣ fekete 1122987 ∧ ¬Equidistributed 1122987 63 := by
  refine ⟨squarefree_prod factors,by decide,odd_factor,?_⟩
  intro uniform
  have eq := uniform 1 (by decide) (by decide) 4 (by decide) (by decide)
  rw [odd_frequency 1 (by decide),odd_frequency 4 (by decide)] at eq
  exact (by decide : row (1%21) ≠ row (4%21)) eq

end FeketeEquidistribution
