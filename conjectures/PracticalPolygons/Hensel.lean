module

public import conjectures.PracticalPolygons.Digits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section
namespace PracticalPolygons

private theorem cheap_congr {s : ℕ} {a b x y : ℤ} (ha : x≡a [ZMOD 25])
    (hb : y≡b [ZMOD 25]) (cheap : Cheap s a b) : Cheap s x y := by
  intro t
  obtain ⟨h,l,high,cost⟩ := cheap t
  exact ⟨h,l,(((deriv_congr s ha).mul_right _).add ((deriv_congr s hb).mul_right _)).trans high,cost⟩

/-- Join the fixed cofactor and the first pair of base-five digits. -/
private theorem mixed_root {s d : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) (n : ℕ) :
    ∃ x y : ℤ, Q s x+Q s y ≡ (n:ℤ) [ZMOD (6*d:ℕ)*25] ∧ Cheap s x y := by
  obtain ⟨i,j,r25,ch⟩ := seed hs n
  obtain ⟨u,v,rc⟩ := cofactor_root hs hd n
  have cop : (6*d).Coprime 25 := by rcases hd with rfl|rfl|rfl|rfl <;> decide
  let x := Nat.chineseRemainder cop u i
  let y := Nat.chineseRemainder cop v j
  have x25 : ((x.val:ℕ):ℤ) ≡ i [ZMOD 25] := Int.natCast_modEq_iff.mpr x.prop.2
  have y25 : ((y.val:ℕ):ℤ) ≡ j [ZMOD 25] := Int.natCast_modEq_iff.mpr y.prop.2
  have xc := Int.natCast_modEq_iff.mpr x.prop.1
  have yc := Int.natCast_modEq_iff.mpr y.prop.1
  refine ⟨x.val,y.val,?_,cheap_congr x25 y25 ch⟩
  exact (Int.modEq_and_modEq_iff_modEq_mul (show ((6*d:ℕ):ℤ).natAbs.Coprime (25:ℤ).natAbs from cop)).mp
    ⟨((quad_congr s xc).add (quad_congr s yc)).trans rc,
    ((quad_congr s x25).add (quad_congr s y25)).trans r25⟩

/-- Repeatedly lift one base-five digit and preserve the two derivatives modulo 25. -/
theorem lifted_root {s d : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) (n b : ℕ) :
    ∃ x y : ℤ, Q s x+Q s y ≡ (n:ℤ) [ZMOD ((6*d:ℕ):ℤ)*25*5^b] ∧ Cheap s x y := by
  induction b with
  | zero => simpa using mixed_root hs hd n
  | succ b ih =>
    obtain ⟨x,y,old,ch⟩ := ih
    let L := ((6*d:ℕ):ℤ)*25*5^b
    have h25 : (25:ℤ)∣L := ⟨((6*d:ℕ):ℤ)*5^b,by dsimp [L]; ring⟩
    obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp old
    obtain ⟨h,l,high,_⟩ := ch t
    have w := lift_pair (L:=L) ht ((by decide : (5:ℤ)∣25).trans h25)
      (Int.ModEq.of_dvd (by decide : (5:ℤ)∣25) high)
    refine ⟨x+L*h,y+L*l,by simpa only [L,pow_succ,←mul_assoc] using w,?_⟩
    exact cheap_congr (Int.add_modEq_left_iff.mpr (h25.mul_right _))
      (Int.add_modEq_left_iff.mpr (h25.mul_right _)) ch

/-- A representative in the first residue box retains the derivative covering. -/
theorem bounded_root {s d : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) (n b : ℕ) :
    let L := ((6*d:ℕ):ℤ)*25*5^b
    ∃ x y : ℤ, 0≤x ∧ x<L ∧ 0≤y ∧ y<L ∧ Q s x+Q s y ≡ (n:ℤ) [ZMOD L] ∧ Cheap s x y := by
  let L := ((6*d:ℕ):ℤ)*25*5^b
  have pd : 0<d := by rcases hd with rfl|rfl|rfl|rfl <;> decide
  have pos : 0<L := by dsimp [L]; positivity
  have h25 : (25:ℤ)∣L := ⟨((6*d:ℕ):ℤ)*5^b,by dsimp [L]; ring⟩
  obtain ⟨x,y,old,ch⟩ := lifted_root hs hd n b
  have hx := Int.mod_modEq x L
  have hy := Int.mod_modEq y L
  exact ⟨x%L,y%L,Int.emod_nonneg _ pos.ne',Int.emod_lt_of_pos _ pos,
    Int.emod_nonneg _ pos.ne',Int.emod_lt_of_pos _ pos,
    ((quad_congr s hx).add (quad_congr s hy)).trans old,
    cheap_congr (Int.ModEq.of_dvd h25 hx) (Int.ModEq.of_dvd h25 hy) ch⟩

end PracticalPolygons
