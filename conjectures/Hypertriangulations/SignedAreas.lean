module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
namespace Hypertriangulations

abbrev Plane := ℝ × ℝ

def orient (a b c : Plane) : ℝ := (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

theorem orient_cycle (a b c : Plane) : orient b c a=orient a b c := by unfold orient; ring

theorem orient_swap (a b c : Plane) : orient b a c= -orient a b c := by unfold orient; ring

@[simp] theorem orient_same (a b : Plane) : orient a a b=0 := by simp [orient]

noncomputable def pos (x : ℝ) : Bool := decide (0<x)
def unit (s : Bool) : ℤ := if s then 1 else -1
def triple (s t u : Bool) : ℤ := if s && t && u then 1 else if !s && !t && !u then -1 else 0

noncomputable def sign (a b c : Plane) : ℤ := if orient a b c=0 then 0 else unit (pos (orient a b c))

/-- The signed indicator of the open triangle. Points on a supporting line have value zero. -/
noncomputable def winding (a b c p : Plane) : ℤ :=
  if orient p a b=0 ∨ orient p b c=0 ∨ orient p c a=0 then 0
  else triple (pos (orient p a b)) (pos (orient p b c)) (pos (orient p c a))

def GeneralPosition {α : Type*} (P : α→Plane) := ∀ a b c, a≠b → a≠c → b≠c → orient (P a) (P b) (P c)≠0

private theorem pos_neg {x : ℝ} (h : x≠0) : pos (-x)= !pos x := by
  by_cases hx : 0<x
  · simp [pos,hx,not_lt_of_ge hx.le]
  · simp [pos,hx,lt_of_le_of_ne (le_of_not_gt hx) h]

private theorem pos_mul {x y : ℝ} (hx : x≠0) (hy : y≠0) : pos (x*y)=decide (pos x=pos y) := by
  rcases lt_or_gt_of_ne hx with x|x <;> rcases lt_or_gt_of_ne hy with y|y
  · simp [pos,not_lt_of_ge x.le,not_lt_of_ge y.le,mul_pos_of_neg_of_neg x y]
  · simp [pos,not_lt_of_ge x.le,y,not_lt_of_ge (mul_neg_of_neg_of_pos x y).le]
  · simp [pos,x,not_lt_of_ge y.le,not_lt_of_ge (mul_neg_of_pos_of_neg x y).le]
  · simp [pos,x,y,mul_pos x y]

private theorem mixed_three {x y z : ℝ} (h : x+y+z=0) (hx : x≠0) :
    ¬(pos x=pos y ∧ pos y=pos z) := by
  intro e
  by_cases a : 0<x <;> by_cases b : 0<y <;> by_cases c : 0<z <;> simp_all [pos] <;> first | linarith | exact hx (by linarith)

private theorem mixed_four {w x y z : ℝ} (h : w+x+y+z=0) (hx : x≠0) :
    ¬(pos w=pos x ∧ pos x=pos y ∧ pos y=pos z) := by
  intro e
  by_cases a : 0<w <;> by_cases b : 0<x <;> by_cases c : 0<y <;> by_cases d : 0<z <;>
    simp_all [pos] <;> first | linarith | exact hx (by linarith)

/-- A point away from the six supporting lines gives zero on the oriented tetrahedron boundary. -/
theorem winding_boundary (a b c d p : Plane)
    (ab : orient p a b≠0) (ac : orient p a c≠0) (ad : orient p a d≠0)
    (bc : orient p b c≠0) (bd : orient p b d≠0) (cd : orient p c d≠0) :
    winding b c d p-winding a c d p+winding a b d p-winding a b c p=0 := by
  have pl : orient p a b*orient p c d+ -(orient p a c*orient p b d)+orient p a d*orient p b c=0 := by
    unfold orient; ring
  have h := mixed_three pl (mul_ne_zero ab cd)
  rw [pos_neg (mul_ne_zero ac bd),pos_mul ab cd,pos_mul ac bd,pos_mul ad bc] at h
  have swap (x y : Plane) : orient p y x= -orient p x y := by unfold orient; ring
  have boole : ∀ a b c d e f : Bool,
      ¬(decide (a=f)= !decide (b=e) ∧ (!decide (b=e))=decide (c=d)) →
      triple d f (!e)-triple b f (!c)+triple a e (!c)-triple a d (!b)=0 := by decide
  simpa only [winding,swap b d,swap a d,swap a c,ab,ac,ad,bc,bd,cd,neg_ne_zero.mpr ad,
    neg_ne_zero.mpr ac,neg_ne_zero.mpr bd,false_or,ite_false,pos_neg ad,pos_neg ac,pos_neg bd] using
    boole _ _ _ _ _ _ h

/-- The four signs and the four tests for the opposite vertex give the ordinary triangulation valuation. -/
theorem active_boundary (a b c d : Plane) (abc : orient a b c≠0) (abd : orient a b d≠0)
    (acd : orient a c d≠0) (bcd : orient b c d≠0) :
    sign b c d - sign a c d + sign a b d - sign a b c +
    2*(winding b c d a-winding a c d b+winding a b d c-winding a b c d)=0 := by
  have rel : orient b c d+ -orient a c d+orient a b d+ -orient a b c=0 := by unfold orient; ring
  have h := mixed_four rel (neg_ne_zero.mpr acd)
  rw [pos_neg acd,pos_neg abc] at h
  have s1 : orient a d b= -orient a b d := by unfold orient; ring
  have s2 : orient b a c= -orient a b c := orient_swap _ _ _
  have s3 : orient b d a=orient a b d := orient_cycle _ _ _
  have s4 : orient c a b=orient a b c := by unfold orient; ring
  have s5 : orient c b d= -orient b c d := orient_swap _ _ _
  have s6 : orient c d a=orient a c d := orient_cycle _ _ _
  have s7 : orient d a b=orient a b d := by unfold orient; ring
  have s8 : orient d b c=orient b c d := by unfold orient; ring
  have s9 : orient d c a= -orient a c d := by unfold orient; ring
  have boole : ∀ w x y z : Bool, ¬(w= !x ∧ (!x)=y ∧ y= !z) →
    unit w-unit x+unit y-unit z+2*(triple z x (!y)-triple (!z) w y+triple z (!w) x-triple y w (!x))=0 := by decide
  simpa only [sign,winding,s1,s2,s3,s4,s5,s6,s7,s8,s9,abc,abd,acd,bcd,neg_ne_zero.mpr abc,
    neg_ne_zero.mpr abd,neg_ne_zero.mpr acd,neg_ne_zero.mpr bcd,false_or,ite_false,
    pos_neg abc,pos_neg abd,pos_neg acd,pos_neg bcd] using boole _ _ _ _ h

theorem sign_cycle (a b c : Plane) : sign b c a=sign a b c := by simp only [sign,orient_cycle a b c]

theorem sign_swap (a b c : Plane) : sign b a c= -sign a b c := by
  rw [sign,sign,orient_swap a b c]
  by_cases h : orient a b c=0
  · simp [h]
  · simp only [h,neg_ne_zero.mpr h,ite_false,pos_neg h]
    cases pos (orient a b c) <;> rfl

@[simp] theorem sign_degenerate (a b : Plane) : sign a a b=0 := by simp [sign]

private theorem orient_reverse (p a b : Plane) : orient p b a= -orient p a b := by unfold orient; ring

theorem winding_cycle (a b c p : Plane) : winding b c a p=winding a b c p := by
  have rotate : ∀ x y z : Bool, triple y z x=triple x y z := by decide
  simp only [winding,rotate (pos (orient p a b)) (pos (orient p b c)) (pos (orient p c a))]
  grind

theorem winding_swap (a b c p : Plane) : winding b a c p= -winding a b c p := by
  have flip : ∀ x y z : Bool, triple (!x) (!z) (!y)= -triple x y z := by decide
  simp only [winding,orient_reverse p a b,orient_reverse p c a,orient_reverse p b c,neg_eq_zero]
  by_cases x : orient p a b=0 <;> by_cases y : orient p b c=0 <;> by_cases z : orient p c a=0 <;>
    simp [x,y,z]; rw [pos_neg x,pos_neg y,pos_neg z,flip]

@[simp] theorem winding_degenerate (a b p : Plane) : winding a a b p=0 := by
  have h : orient p a a=0 := by unfold orient; ring
  simp [winding,h]

@[simp] theorem winding_at_first (a b c : Plane) : winding a b c a=0 := by simp [winding]
@[simp] theorem winding_at_second (a b c : Plane) : winding a b c b=0 := by simp [winding]
@[simp] theorem winding_at_third (a b c : Plane) : winding a b c c=0 := by simp [winding]

def StrictInside (a b c p : Plane) : Prop :=
  (0<orient p a b ∧ 0<orient p b c ∧ 0<orient p c a) ∨
  (orient p a b<0 ∧ orient p b c<0 ∧ orient p c a<0)

noncomputable instance (a b c p : Plane) : Decidable (StrictInside a b c p) := Classical.propDecidable _

theorem winding_inside (a b c p : Plane) : winding a b c p=if StrictInside a b c p then sign a b c else 0 := by
  classical
  have area : orient a b c=orient p a b+orient p b c+orient p c a := by unfold orient;ring
  rcases lt_trichotomy (orient p a b) 0 with x|x|x <;> rcases lt_trichotomy (orient p b c) 0 with y|y|y <;>
    rcases lt_trichotomy (orient p c a) 0 with z|z|z <;>
    simp_all [StrictInside,winding,triple,pos,unit,sign,lt_asymm] <;> split_ifs <;> simp_all <;> grind

end Hypertriangulations
