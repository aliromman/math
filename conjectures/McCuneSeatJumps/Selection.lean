module

public import conjectures.McCuneSeatJumps.Counting
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace McCuneSeatJumps

/-- The length parameter of the coordinate interval for a state with a old and b new seats. -/
def width (h k l a b : ℕ) : ℤ := (h:ℤ)*((a:ℤ)+1-b)+(k:ℤ)*((a:ℤ)+1-l)

/-- The new seat count forced by a positive rectangle. -/
def newSeats (h k l a : ℕ) := a+1+k*(a+1-l)/h

private theorem int_residue (h k l a : ℕ) (lh : l ≤ h) :
    (residue h k l a : ℤ) = ((k:ℤ)*((a:ℤ)+1-l))%h := by
  unfold residue
  push_cast [Nat.cast_sub (show l ≤ h+1 by omega)]
  rw [show (k:ℤ)*(a+(h+1-l))=k*((a:ℤ)+1-l)+k*h by ring, Int.add_mul_emod_self_right]

private theorem width_mod (h k l a b : ℕ) (lh : l ≤ h) :
    width h k l a b % h = (residue h k l a : ℤ) := by
  rw [int_residue _ _ _ _ lh, width, add_comm, Int.add_mul_emod_self_left]

private theorem raw_sum {h k l a c b d : ℕ} (hl : 0 < l) (ha : a+c+l=h) :
    width h k l a b + width h k l c d =
      (h:ℤ)+2*k-3*k*l + (h:ℤ)*((h:ℤ)+k-(b+d+((l-1:ℕ):ℤ))) := by
  have A : (a:ℤ)+c+l=h := by exact_mod_cast ha
  rw [Nat.cast_sub (by omega : 1≤l), Nat.cast_one, width, width]
  linear_combination ((h:ℤ)+k)*A

private theorem int_room {h k l : ℕ} (hw : 0 < room h k l) :
    (room h k l : ℤ) = (h:ℤ)+2*k-3*k*l := by
  have e : 3*k*l ≤ h+2*k := by unfold room at hw; omega
  simp [room,Nat.cast_sub e]

private theorem room_lt {h k l : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l) :
    room h k l < h := by unfold room; have := Nat.mul_le_mul_left (3*k) hl; omega

private theorem residue_pair {h k l a c : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l)
    (ha : a+c+l=h) (hr : residue h k l a < room h k l) :
    residue h k l c = room h k l - residue h k l a := by
  have lh : l ≤ h := by omega
  have ir := int_room (Nat.zero_le _ |>.trans_lt hr)
  have A : (a:ℤ)+c+l=h := by exact_mod_cast ha
  have modR (v : ℕ) : (residue h k l v : ℤ) ≡ (k:ℤ)*((v:ℤ)+1-l) [ZMOD h] := by
    rw [int_residue _ _ _ _ lh]
    exact Int.emod_emod ..
  have S := (modR a).add (modR c)
  have E : (k:ℤ)*((a:ℤ)+1-l)+k*((c:ℤ)+1-l) =
      (room h k l:ℤ)+((k:ℤ)-1)*h := by rw [ir]; linear_combination (k:ℤ)*A
  rw [E] at S
  have S' : (residue h k l a : ℤ)+residue h k l c ≡
      (residue h k l a:ℤ)+((room h k l:ℤ)-residue h k l a) [ZMOD h] := by
    change _%_ = _%_ at S ⊢
    rw [Int.add_mul_emod_self_right] at S
    simpa only [add_sub_cancel] using S
  have E' := S'.add_left_cancel' (residue h k l a)
  change _%_ = _%_ at E'
  have rc : residue h k l c < h := Nat.mod_lt _ hh
  have wr := room_lt (h:=h) (k:=k) (l:=l) hh hk hl
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast rc),
    Int.emod_eq_of_lt (by omega) (by omega)] at E'
  omega

private theorem loser_le_other {h k l a : ℕ} (hl : 0 < l) (lh : l ≤ h)
    (hr : 0 < residue h k l a) (hrw : residue h k l a < room h k l) : l ≤ a := by
  by_contra! no
  have ir := int_room (hr.trans hrw)
  have e : (k:ℤ)*((a:ℤ)+1-l) ≡ (residue h k l a:ℤ) [ZMOD h] := by
    rw [int_residue _ _ _ _ lh]
    exact (Int.emod_emod ..).symm
  have neg : (k:ℤ)*((a:ℤ)+1-l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
  have low : 0 < (residue h k l a:ℤ) - k*((a:ℤ)+1-l) := by omega
  have bound := Int.le_of_dvd low e.dvd
  have lr : (residue h k l a : ℤ) < room h k l := by exact_mod_cast hrw
  have u : 0 ≤ (k:ℤ)*(2*l-1+a) := mul_nonneg (by positivity) (by omega)
  linarith only [bound,ir,lr,u]

private theorem new_width {h k l a : ℕ} (hl : 0 < l) (lh : l ≤ h)
    (hr : 0 < residue h k l a) (hw : residue h k l a < room h k l) :
    width h k l a (newSeats h k l a) = residue h k l a := by
  have le := loser_le_other hl lh hr hw
  have cn : ((a+1-l:ℕ):ℤ)=(a:ℤ)+1-l := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  rw [width, newSeats, int_residue _ _ _ _ lh, ← cn]
  have ed := Int.emod_add_mul_ediv ((k:ℤ)*(a+1-l:ℕ)) h
  push_cast [Nat.cast_sub (show l ≤ a+1 by omega)] at ed ⊢
  linarith only [ed]

/-- A positive cell selects one new allocation; both widths are its two residue factors. -/
theorem selected_widths {h k l a c : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l)
    (ha : a+c+l=h) (hw : 0 < cellWeight h k l a) :
    newSeats h k l a + newSeats h k l c + (l-1) = h+k ∧
    width h k l a (newSeats h k l a) = residue h k l a ∧
    width h k l c (newSeats h k l c) = (room h k l - residue h k l a : ℕ) := by
  have lh : l ≤ h := by omega
  have ra : 0 < residue h k l a := Nat.pos_of_mul_pos_right hw
  have delta := Nat.pos_of_mul_pos_left (show 0 < residue h k l a*(room h k l-residue h k l a) from hw)
  have raw : residue h k l a < room h k l := Nat.lt_of_sub_pos delta
  have rc := residue_pair hh hk hl ha raw
  have wa := new_width hl lh ra raw
  have wc := new_width (k:=k) (a:=c) hl lh (rc.symm ▸ delta) (by rw [rc]; omega)
  rw [rc] at wc
  refine ⟨?_,wa,wc⟩
  have S := raw_sum (k:=k) (b:=newSeats h k l a) (d:=newSeats h k l c) hl ha
  rw [wa,wc,Nat.cast_sub raw.le, ← int_room (ra.trans raw)] at S
  have z : (h:ℤ)*((h:ℤ)+k-(newSeats h k l a + newSeats h k l c + ((l-1:ℕ):ℤ))) = 0 := by linarith only [S]
  have := (mul_eq_zero.mp z).resolve_left (by exact_mod_cast hh.ne')
  omega

/-- The feasible new allocation is unique, and it exists for each positive weight. -/
theorem selection_iff {h k l a c b d : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l)
    (ha : a+c+l=h) :
    (b+d+(l-1)=h+k ∧ 0 < width h k l a b ∧ 0 < width h k l c d) ↔
      0 < cellWeight h k l a ∧ b = newSeats h k l a ∧ d = newSeats h k l c := by
  have lh : l ≤ h := by omega
  constructor
  · rintro ⟨hb,wa,wc⟩
    have S := raw_sum (k:=k) (b:=b) (d:=d) hl ha
    have B : (b:ℤ)+d+((l-1:ℕ):ℤ)=h+k := by exact_mod_cast hb
    rw [B,sub_self,mul_zero,add_zero] at S
    have pos : 0 < room h k l := by
      unfold room
      have E : (3:ℤ)*k*l < h+2*k := by linarith only [S,wa,wc]
      exact Nat.sub_pos_of_lt (by exact_mod_cast E)
    rw [← int_room pos] at S
    have W := room_lt (h:=h) (k:=k) (l:=l) hh hk hl
    have r (v u : ℕ) (lo : 0 < width h k l v u) (up : width h k l v u < h) :
        width h k l v u = residue h k l v := by
      rw [← width_mod h k l v u lh, Int.emod_eq_of_lt lo.le up]
    have resA := r a b wa (by omega)
    have w : 0 < cellWeight h k l a := Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by omega))
    obtain ⟨_,wa',wc'⟩ := selected_widths hh hk hl ha w
    have wb : width h k l a b = width h k l a (newSeats h k l a) := resA.trans wa'.symm
    have wd : width h k l c d = width h k l c (newSeats h k l c) := by omega
    have inj (v u u' : ℕ) (e : width h k l v u=width h k l v u') : u=u' := by
      unfold width at e
      have Z := mul_left_cancel₀ (show (h:ℤ)≠0 by omega) (add_right_cancel e)
      omega
    exact ⟨w,inj a _ _ wb,inj c _ _ wd⟩
  · rintro ⟨w,rfl,rfl⟩
    obtain ⟨s,wa,wc⟩ := selected_widths hh hk hl ha w
    exact ⟨s,by rw [wa]; exact_mod_cast (Nat.pos_of_mul_pos_right w),
      by rw [wc]; exact_mod_cast (Nat.pos_of_mul_pos_left w)⟩

/-- In each positive cell both other states begin with at least as many seats as the loser. -/
theorem selected_old_bounds {h k l a c : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l)
    (ha : a+c+l=h) (w : 0 < cellWeight h k l a) : l ≤ a ∧ l ≤ c := by
  have ra : 0 < residue h k l a := Nat.pos_of_mul_pos_right w
  have raw : residue h k l a < room h k l := Nat.lt_of_sub_pos (Nat.pos_of_mul_pos_left w)
  have rc := residue_pair hh hk hl ha raw
  exact ⟨loser_le_other hl (by omega) ra raw,
    loser_le_other (h:=h) (k:=k) hl (by omega) (by rw [rc]; omega) (by rw [rc]; omega)⟩

/-- Multiply the two positive integer widths to get the term in the area sum. -/
theorem width_product {h k l a c b d : ℕ} (hh : 0 < h) (hk : 0 < k) (hl : 0 < l)
    (ha : a+c+l=h) (hb : b+d+(l-1)=h+k) (wa : 0 < width h k l a b)
    (wc : 0 < width h k l c d) :
    width h k l a b * width h k l c d = (cellWeight h k l a : ℤ) := by
  obtain ⟨w,rfl,rfl⟩ := (selection_iff hh hk hl ha).mp ⟨hb,wa,wc⟩
  obtain ⟨_,A,C⟩ := selected_widths hh hk hl ha w
  rw [A,C,cellWeight,Nat.cast_mul]

end McCuneSeatJumps
