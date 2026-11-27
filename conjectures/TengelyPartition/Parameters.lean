module

public import conjectures.TengelyPartition.Counts
public import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace TengelyPartition

/-- A square product has a common factor and two square cofactors. -/
theorem common_square {a b : ℕ} (ha : 0<a) (hb : 0<b) (h : IsSquare (a*b)) :
    ∃ g u v : ℕ, 0<g ∧ 0<u ∧ 0<v ∧ a=g*u^2 ∧ b=g*v^2 := by
  obtain ⟨k,hk⟩ := h
  let d := a.gcd k
  let u := a/d
  let v := k/d
  have dp : 0<d := Nat.gcd_pos_of_pos_left k ha
  have au : d*u=a := Nat.mul_div_cancel' (a.gcd_dvd_left k)
  have kv : d*v=k := Nat.mul_div_cancel' (a.gcd_dvd_right k)
  have up : 0<u := by
    apply Nat.pos_of_ne_zero
    intro e
    rw [e,mul_zero] at au
    omega
  have kp : 0<k := by
    apply Nat.pos_of_ne_zero
    intro e
    rw [e,mul_zero] at hk
    exact (Nat.mul_pos ha hb).ne' hk
  have vp : 0<v := by
    apply Nat.pos_of_ne_zero
    intro e
    rw [e,mul_zero] at kv
    omega
  have cop : u.Coprime v := Nat.coprime_div_gcd_div_gcd dp
  have id : u*b=v^2*d := Nat.mul_left_cancel dp (by
    calc d*(u*b) = a*b := by rw [←au];ring
         _ = k*k := hk
         _ = d*(v^2*d) := by rw [←kv];ring)
  have dv : u ∣ d := (cop.pow_right 2).dvd_of_dvd_mul_left ⟨b,id.symm⟩
  obtain ⟨g,hg⟩ := dv
  have gp : 0<g := by
    apply Nat.pos_of_ne_zero
    intro e
    rw [e,mul_zero] at hg
    omega
  refine ⟨g,u,v,gp,up,vp,?_,?_⟩
  · rw [←au,hg];ring
  · apply Nat.mul_left_cancel up
    rw [id,hg];ring

def scale (g : ℕ) := if g%4=2 then 1 else 0

private theorem residue_of_parity {a c : ℕ} (ha : 3≤a) (bound : 2*c≤a)
    (par : a%2=0 → (a/2+c)%2=0) : ∃ r<a,r/2+(a+r)/2+2=a+c := by
  by_cases even : a%2=0
  · exact ⟨a/2+c-2,by omega,by have := par even;omega⟩
  · exact ⟨a/2+c-1,by omega,by omega⟩

/-- The square-product case admits matching linear coefficients even when a part is twice an odd number. -/
theorem square_residue {g u : ℕ} (gp : 0<g) (ha : 3≤g*u^2) :
    ∃ r<g*u^2,r/2+(g*u^2+r)/2+2=g*u^2+scale g*u := by
  apply residue_of_parity ha
  · unfold scale;split
    · simp only [one_mul]
      have hg : 2≤g := by omega
      exact (Nat.mul_le_mul_right u hg).trans (Nat.mul_le_mul_left g (Nat.le_self_pow (by decide : 2≠0) u))
    · simp
  · have sm : (g*u^2)%4=((g%4)*(u%4)^2)%4 := by simp [Nat.mul_mod, Nat.pow_mod]
    have gg := Nat.mod_lt g (by decide : 0<4)
    have uu := Nat.mod_lt u (by decide : 0<4)
    generalize mid : g%4=j at sm gg
    generalize uk : u%4=k at sm uu
    unfold scale
    rw [mid]
    interval_cases j <;> interval_cases k <;> norm_num at sm ⊢ <;> omega

/-- Positive Pell solutions can be doubled repeatedly to exceed any prescribed second coordinate. -/
private theorem pell_large {D : ℕ} (dp : 0<D) (ns : ¬IsSquare D) (N : ℕ) :
    ∃ x y : ℕ,N<y ∧ 0<x ∧ x^2=1+D*y^2 := by
  induction N with
  | zero =>
    obtain ⟨s,hx,hy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare (d:=(D:ℤ))
      (by exact_mod_cast dp) (fun h ↦ ns (Int.isSquare_natCast_iff.mp h))
    refine ⟨s.x.toNat,s.y.toNat,by omega,by omega,?_⟩
    have h := s.prop_x
    have ex := Int.toNat_of_nonneg (show 0≤s.x by omega)
    have ey := Int.toNat_of_nonneg (show 0≤s.y by omega)
    exact_mod_cast (show (s.x.toNat:ℤ)^2=1+(D:ℤ)*(s.y.toNat:ℤ)^2 by rw [ex,ey];exact h)
  | succ N ih =>
    obtain ⟨x,y,hy,hx,eq⟩ := ih
    refine ⟨1+2*D*y^2,2*x*y,?_,by positivity,?_⟩
    · have h := Nat.mul_le_mul_right y (show 2≤2*x by omega);omega
    · calc
        _ = 1+D*(2*y)^2*(1+D*y^2) := by ring
        _ = _ := by rw [←eq];ring

/-- For a nonsquare product, one Pell orbit supplies common values of both quadratics. -/
theorem nonsquare_parameters {a b c d : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (ns : ¬ IsSquare (a*b)) (N : ℕ) :
    ∃ t u : ℕ, N<t ∧ N<u ∧ a*t^2+c*t=b*u^2+d*u := by
  obtain ⟨x,y,hy,hx,eq⟩ := pell_large (Nat.mul_pos ha hb) ns N
  let t := b*y^2*c+x*y*d
  let u := a*y^2*d+x*y*c
  have xy := Nat.le_mul_of_pos_left y hx
  have ct := Nat.le_mul_of_pos_right (x*y) hc
  have dt := Nat.le_mul_of_pos_right (x*y) hd
  refine ⟨t,u,by dsimp [t];omega,by dsimp [u];omega,?_⟩
  dsimp only [t,u]
  ring_nf
  rw [eq]
  ring

end TengelyPartition
