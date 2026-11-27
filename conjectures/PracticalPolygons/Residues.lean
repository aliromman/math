module

public import conjectures.PracticalPolygons.Hensel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace PracticalPolygons

private theorem square_bound {x L : ℤ} (xd : 0≤x) (xu : x<L) (h : ℕ) :
    (x+L*h)^2 ≤ L^2*(h+1:ℤ)^2 := by
  have pL : 0<L := xd.trans_lt xu
  calc
    _ ≤ (L*(h+1:ℤ))^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by nlinarith)
    _ = _ := by ring

/-- Two polygonal numbers in a fixed residue class have sum less than five sixths
of the square of the selected practical modulus. -/
theorem large_residue {s n d b : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) :
    ∃ x y, let M := 6*d*5^(b+4)
           polygonal s x+polygonal s y ≡ n [MOD M] ∧
           6*(polygonal s x+polygonal s y)<5*M^2 := by
  let L := ((6*d:ℕ):ℤ)*25*5^b
  let M := 6*d*5^(b+4)
  have dpos : 0<d := by rcases hd with rfl|rfl|rfl|rfl <;> decide
  have pL : 0<L := by dsimp [L]; positivity
  have size : (M:ℤ)=L*25 := by dsimp [M,L]; rw [pow_add]; ring
  have h25 : (25:ℤ)∣L := ⟨((6*d:ℕ):ℤ)*5^b,by dsimp [L]; ring⟩
  obtain ⟨x,y,x0,xu,y0,yu,base,cheap⟩ := bounded_root hs hd n b
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp base
  obtain ⟨h,l,corr,cost⟩ := cheap t
  have lifted := lift_pair (L:=L) ht h25 corr
  let X := x+L*h
  let Y := y+L*l
  have X0 : 0≤X := by dsimp [X]; positivity
  have Y0 : 0≤Y := by dsimp [Y]; positivity
  have px : Q s X=(polygonal s (stride s*X.toNat):ℤ) := by
    simpa only [Int.toNat_of_nonneg X0] using quad_polygon hs X.toNat
  have py : Q s Y=(polygonal s (stride s*Y.toNat):ℤ) := by
    simpa only [Int.toNat_of_nonneg Y0] using quad_polygon hs Y.toNat
  have sx : X^2 ≤ L^2*(h+1:ℤ)^2 := square_bound x0 xu h
  have sy : Y^2 ≤ L^2*(l+1:ℤ)^2 := square_bound y0 yu l
  have linear : Q s X+Q s Y ≤ (lead s:ℤ)*(X^2+Y^2) := by
    unfold Q
    nlinarith only [mul_nonneg (Int.natCast_nonneg (lin s)) X0,mul_nonneg (Int.natCast_nonneg (lin s)) Y0]
  have cost' : (lead s:ℤ)*((h+1:ℤ)^2+(l+1:ℤ)^2) ≤ 520 := by exact_mod_cast cost
  have total : Q s X+Q s Y ≤ 520*L^2 := calc
    _ ≤ _ := linear
    _ ≤ (lead s:ℤ)*(L^2*(h+1:ℤ)^2+L^2*(l+1:ℤ)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add sx sy) (Int.natCast_nonneg _)
    _ = (lead s:ℤ)*((h+1:ℤ)^2+(l+1:ℤ)^2)*L^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right cost' (sq_nonneg _)
  have cut : 6*(Q s X+Q s Y)<5*(M:ℤ)^2 := by rw [size]; nlinarith only [total,sq_pos_of_pos pL]
  refine ⟨stride s*X.toNat,stride s*Y.toNat,?_,?_⟩
  · apply Int.natCast_modEq_iff.mp
    change _ ≡ _ [ZMOD (M:ℤ)]
    rw [Nat.cast_add,←px,←py,size]
    exact lifted
  · rw [px,py] at cut
    exact_mod_cast cut

end PracticalPolygons
