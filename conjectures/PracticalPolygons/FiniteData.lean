module

public import conjectures.PracticalPolygons.Bitset

@[expose] public section
namespace PracticalPolygons

/-- Positive multiples through the indicated bound. -/
def multiples (m t : ℕ) : List ℕ := (List.range t).map (fun j ↦ m*(j+1))

def smallPracticals : List ℕ :=
  ((List.range 6).flatMap fun a ↦ multiples (2^a) (min (2^(a+1)) 32)) ++
  multiples 6 12 ++ multiples 30 72 ++ multiples 150 300

def smallBits (s : ℕ) : ℕ :=
  let v := (polyList s 633).filter (·≤400000)
  shiftSum (shiftSum (shiftSum 1 smallPracticals) v) v

set_option maxRecDepth 8192 in
private theorem small_check (s : ℕ) (hs : Orders s) :
    ((2^400001-1) &&& (smallBits s ||| 1))=2^400001-1 := by
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem small_values {s n : ℕ} (hs : Orders s) (hn : 0<n) (hn' : n≤400000) :
    ∃ p∈smallPracticals, ∃ x y, n=p+polygonal s x+polygonal s y := by
  have b := mask_covers (small_check s hs) (n:=n) (by
    simp only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]; omega)
  rw [Nat.testBit_or,Bool.or_eq_true] at b
  obtain h|h := b
  · obtain ⟨b,hb,j,hj,rfl⟩ := bit_shiftSum h
    obtain ⟨a,ha,i,hi,rfl⟩ := bit_shiftSum hj
    obtain ⟨p,hp,zeroIndex,oneBit,eqn⟩ := bit_shiftSum hi
    subst i
    simp only [List.mem_filter,List.mem_map,polyList,fastPolygon_eq] at ha hb
    obtain ⟨⟨x,_,rfl⟩,_⟩ := ha
    obtain ⟨⟨y,_,rfl⟩,_⟩ := hb
    refine ⟨p,hp,x,y,?_⟩
    have iz : zeroIndex=0 := one_bit oneBit
    exact congrArg (fun z ↦ z+p+polygonal s x+polygonal s y) iz |>.trans (by rw [Nat.zero_add])
  · exact False.elim (by have := one_bit h; omega)

set_option maxRecDepth 8192 in
theorem moderate_check {s : ℕ} (hs : Orders s) :
    (((2^750-1) &&& residueBits s 223 750)=2^750-1) ∧
    (((2^3750-1) &&& residueBits s 411 3750)=2^3750-1) ∧
    (((2^18750-1) &&& residueBits s 1204 18750)=2^18750-1) := by
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end PracticalPolygons
