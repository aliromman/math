module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

@[expose] public section
namespace CFPLogDensity
open Finset

/-- A dense dyadic block contains two positions a prescribed distance apart,
up to the density factor. -/
theorem dyadic_pair {I : Finset ℕ} (c j k : ℕ)
    (pos : ∀ x∈I, x<2^(c+1+j+k)) (many : 2^(1+j+k)≤I.card) :
    ∃ a∈I, ∃ b∈I, a+2^j ≤ b ∧ b≤a+2^(c+1+j) := by
  let w : ℕ := 2^(c+1+j)
  let f := fun x : ℕ => x/w
  have wp : 0<w := by dsimp [w]; positivity
  have mp (x) (hx : x∈I) : f x ∈ range (2^k) := by
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul wp).mpr
    simpa [w,pow_add,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using pos x hx
  have tne : (range (2^k)).Nonempty := nonempty_range_iff.mpr (by positivity)
  have bound : (range (2^k)).card*2^(1+j) ≤ I.card := by
    simpa [pow_add,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using many
  obtain ⟨v,hv,hV⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (f:=f) mp tne bound
  let V := I.filter fun x => f x=v
  change 2^(1+j)≤V.card at hV
  have se : V.Nonempty := card_pos.mp ((by positivity : 0<2^(1+j)).trans_le hV)
  let a := V.min' se
  let b := V.max' se
  have ha : a∈V := min'_mem _ _
  have hb : b∈V := max'_mem _ _
  have hab : a≤b := V.min'_le_max' se
  have sub : V ⊆ Icc a b := fun x hx => mem_Icc.mpr ⟨V.min'_le x hx,V.le_max' x hx⟩
  have count := (card_le_card sub).trans_eq (Nat.card_Icc a b)
  have fa : a/w=v := (mem_filter.mp ha).2
  have fb : b/w=v := (mem_filter.mp hb).2
  have amin : v*w≤a := (Nat.le_div_iff_mul_le wp).mp fa.ge
  have bmax : b<(v+1)*w := (Nat.div_lt_iff_lt_mul wp).mp (by omega)
  have p : 0<2^j := by positivity
  rw [pow_add] at hV
  rw [Nat.add_mul,Nat.one_mul] at bmax
  exact ⟨a,(mem_filter.mp ha).1,b,(mem_filter.mp hb).1,by omega,by omega⟩

end CFPLogDensity
