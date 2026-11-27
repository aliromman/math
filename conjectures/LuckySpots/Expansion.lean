module

public import conjectures.LuckySpots.Statement

@[expose] public section
namespace LuckySpots
open Finset

def K (j : ℕ) : ℚ := (j+1:ℚ)/(2*j)

def E (j l : ℕ) : ℚ := K j*(j:ℚ)^l -
  ∑ i∈range (j-1), (l.choose i:ℚ)*(totalNumber i:ℚ)*K (j-i-1)*((j-i-1:ℕ):ℚ)^(l-i)

end LuckySpots
