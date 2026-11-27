module

public import conjectures.SplitMatroidFlags.InputData

@[expose] public section

namespace SplitMatroidFlags

open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma connected : ConnectedPairs linesA ∧ ConnectedPairs linesB := by decide +kernel

lemma splitA : ConnectedSplit univ (bases linesA) :=
  example_split (by decide +kernel) (by decide +kernel) connected.1

lemma splitB : ConnectedSplit univ (bases linesB) :=
  example_split (by decide +kernel) (by decide +kernel) connected.2

private lemma ma : matchAll (rawData maskA) = true := by decide +kernel
private lemma mb : matchAll (rawData maskB) = true := by decide +kernel

lemma matchesA : ∀ b ∈ bases linesA, HasMatches (bases linesA) b :=
  checked_matches (match_all_ok ((raw_data_eq masksA) ▸ ma))

lemma matchesB : ∀ b ∈ bases linesB, HasMatches (bases linesB) b :=
  checked_matches (match_all_ok ((raw_data_eq masksB) ▸ mb))

end SplitMatroidFlags
