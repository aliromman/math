module

public import conjectures.SplitMatroidFlags.Blocks

@[expose] public section

namespace SplitMatroidFlags

set_option maxRecDepth 200000
set_option maxHeartbeats 0

verify_batch part0 in maskA at 0 gives #[4186,8,146,687,1633,2391,2324,1520,651,170,23,1]
verify_batch part1 in maskA at 1 gives #[4186,8,137,606,1327,1746,1478,805,267,47,3,0]
verify_batch part2 in maskA at 2 gives #[4131,8,125,479,890,980,684,298,74,8,0,0]
verify_batch part3 in maskA at 3 gives #[4241,8,98,356,679,810,636,325,102,17,1,0]
verify_batch part4 in maskA at 4 gives #[4060,8,77,232,380,399,275,119,29,3,0,0]
verify_batch part5 in maskA at 5 gives #[4015,8,112,434,864,1045,808,397,117,18,1,0]
verify_batch part6 in maskA at 6 gives #[3954,8,119,433,777,816,523,199,40,3,0,0]
verify_batch part7 in maskA at 7 gives #[4137,8,98,331,554,538,314,106,18,1,0,0]
verify_batch part8 in maskA at 8 gives #[4308,8,69,202,302,263,137,40,5,0,0,0]
verify_batch part9 in maskA at 9 gives #[4181,8,89,289,473,455,266,91,16,1,0,0]
verify_batch part10 in maskA at 10 gives #[4000,8,96,308,470,394,184,44,4,0,0,0]
verify_batch part11 in maskA at 11 gives #[4505,8,62,165,210,139,46,6,0,0,0,0]
verify_batch part12 in maskA at 12 gives #[4291,8,71,187,242,177,73,15,1,0,0,0]
verify_batch part13 in maskA at 13 gives #[4125,8,71,185,221,134,39,4,0,0,0,0]
verify_batch part14 in maskA at 14 gives #[4371,8,40,70,55,19,2,0,0,0,0,0]
verify_batch part15 in maskA at 15 gives #[4210,8,55,120,118,57,13,1,0,0,0,0]
verify_batch part16 in maskA at 16 gives #[4371,8,34,47,26,5,0,0,0,0,0,0]
verify_batch part17 in maskA at 17 gives #[4615,8,19,15,3,0,0,0,0,0,0,0]

lemma censusA : census (rawData maskA) =
    #[75887,144,1518,5146,9224,10368,7802,3970,1324,268,28,1] := by
  apply census_of_batches _ 18 (by decide +kernel)
  simp only [batches,part0,part1,part2,part3,part4,part5,part6,part7,part8,
    part9,part10,part11,part12,part13,part14,part15,part16,part17]
  decide +kernel

end SplitMatroidFlags
