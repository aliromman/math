module

public import conjectures.SplitMatroidFlags.Blocks

@[expose] public section

namespace SplitMatroidFlags

set_option maxRecDepth 200000
set_option maxHeartbeats 0

verify_batch part0 in maskB at 0 gives #[4230,8,144,686,1642,2404,2324,1506,637,164,22,1]
verify_batch part1 in maskB at 1 gives #[4353,8,130,579,1292,1729,1474,800,263,46,3,0]
verify_batch part2 in maskB at 2 gives #[4044,8,125,485,928,1056,765,356,102,16,1,0]
verify_batch part3 in maskB at 3 gives #[3909,8,98,335,586,625,428,185,46,5,0,0]
verify_batch part4 in maskB at 4 gives #[4150,8,77,240,409,456,351,184,62,12,1,0]
verify_batch part5 in maskB at 5 gives #[4302,8,118,471,955,1162,894,434,126,19,1,0]
verify_batch part6 in maskB at 6 gives #[4041,8,111,409,751,814,544,218,47,4,0,0]
verify_batch part7 in maskB at 7 gives #[3963,8,100,327,511,446,224,61,7,0,0,0]
verify_batch part8 in maskB at 8 gives #[4150,8,72,204,298,265,151,54,11,1,0,0]
verify_batch part9 in maskB at 9 gives #[4199,8,89,301,512,507,302,104,18,1,0,0]
verify_batch part10 in maskB at 10 gives #[4096,8,86,269,405,336,155,36,3,0,0,0]
verify_batch part11 in maskB at 11 gives #[4295,8,62,152,186,130,52,11,1,0,0,0]
verify_batch part12 in maskB at 12 gives #[4242,8,89,272,377,273,105,19,1,0,0,0]
verify_batch part13 in maskB at 13 gives #[4253,8,61,136,136,67,15,1,0,0,0,0]
verify_batch part14 in maskB at 14 gives #[4462,8,54,121,126,65,15,1,0,0,0,0]
verify_batch part15 in maskB at 15 gives #[4150,8,49,90,69,22,2,0,0,0,0,0]
verify_batch part16 in maskB at 16 gives #[4371,8,35,52,34,10,1,0,0,0,0,0]
verify_batch part17 in maskB at 17 gives #[4678,8,18,17,7,1,0,0,0,0,0,0]

lemma censusB : census (rawData maskB) =
    #[75888,144,1518,5146,9224,10368,7802,3970,1324,268,28,1] := by
  apply census_of_batches _ 18 (by decide +kernel)
  simp only [batches,part0,part1,part2,part3,part4,part5,part6,part7,part8,
    part9,part10,part11,part12,part13,part14,part15,part16,part17]
  decide +kernel

end SplitMatroidFlags
