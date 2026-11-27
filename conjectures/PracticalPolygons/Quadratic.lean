module

public import conjectures.PracticalPolygons.Statement
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section
namespace PracticalPolygons

def lead (s : ℕ) : ℕ := if s%2=0 then (s-2)/2 else 2*(s-2)
def lin (s : ℕ) : ℕ := if s%2=0 then (s-4)/2 else s-4
def stride (s : ℕ) : ℕ := if s%2=0 then 1 else 2

def Q (s : ℕ) (x : ℤ) := (lead s:ℤ)*x^2-(lin s:ℤ)*x
def D (s : ℕ) (x : ℤ) := 2*(lead s:ℤ)*x-(lin s:ℤ)

theorem quad_polygon {s : ℕ} (hs : Orders s) (x : ℕ) :
    Q s x = (polygonal s (stride s*x):ℤ) := by
  have C (a : ℕ) : 2*(a.choose 2:ℤ)=(a:ℤ)^2-a := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      nlinarith
  have h1 := C x
  have h2 := C (2*x)
  push_cast at h2
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [Q,lead,lin,stride,polygonal] <;> nlinarith

theorem quad_congr {M x y : ℤ} (s : ℕ) (h : x≡y [ZMOD M]) : Q s x≡Q s y [ZMOD M] :=
  ((h.pow 2).mul_left _).sub (h.mul_left _)

theorem deriv_congr {M x y : ℤ} (s : ℕ) (h : x≡y [ZMOD M]) : D s x≡D s y [ZMOD M] :=
  (h.mul_left _).sub_right _

/-- Two quadratic increments correct the next block of digits. -/
theorem lift_pair {s : ℕ} {N x y L T t i j : ℤ} (base : N-(Q s x+Q s y)=L*t)
    (hdiv : T∣L) (high : D s x*i+D s y*j ≡ t [ZMOD T]) :
    Q s (x+L*i)+Q s (y+L*j) ≡ N [ZMOD L*T] := by
  obtain ⟨e,he⟩ := hdiv
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp high
  apply Int.modEq_iff_dvd.mpr
  refine ⟨k-(lead s:ℤ)*e*(i^2+j^2),?_⟩
  have expand : Q s (x+L*i)+Q s (y+L*j)
      = Q s x+Q s y+L*(D s x*i+D s y*j)+L^2*(lead s:ℤ)*(i^2+j^2) := by
    unfold Q D
    ring
  rw [expand]
  calc
    _ = L*(t-(D s x*i+D s y*j)) - L*L*(lead s:ℤ)*(i^2+j^2) := by
      linear_combination base
    _ = L*T*(k-(lead s:ℤ)*e*(i^2+j^2)) := by rw [hk,he]; ring

end PracticalPolygons
