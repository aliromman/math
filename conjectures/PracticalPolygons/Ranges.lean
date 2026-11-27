module

public import conjectures.PracticalPolygons.Practicals
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace PracticalPolygons

/-- Subtract a smaller polygonal sum in the correct residue class. -/
theorem fill_layer {s n M x y : ℕ} (pos : 0<M)
    (multiples : ∀ t, 0<t → 5*t≤12*M → Practical (M*t))
    (residue : polygonal s x+polygonal s y ≡ n [MOD M])
    (small : polygonal s x+polygonal s y<n) (upper : 5*n≤12*M^2) : Represented s n := by
  let z := polygonal s x+polygonal s y
  change z≡n [MOD M] at residue
  change z<n at small
  obtain ⟨t,eq⟩ := (Nat.modEq_iff_dvd' small.le).mp residue
  have exact_sum : z+M*t=n := by omega
  have pt : 0<t := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at exact_sum
    omega
  have size : 5*t≤12*M := by
    apply Nat.le_of_mul_le_mul_left _ pos
    calc
      M*(5*t) = 5*(M*t) := by ac_rfl
      _ ≤ 5*n := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 12*M^2 := upper
      _ = M*(12*M) := by ring
  exact ⟨M*t,x,y,multiples t pt size, by dsimp only [z] at exact_sum; omega⟩

private def scale (b : ℕ) := 6*5^(b+4)

private theorem scale_succ (b : ℕ) : scale (b+1)=5*scale b := by
  simp only [scale, show b+1+4=b+4+1 by omega, pow_succ]
  ring

/-- Successive square ranges overlap at scale factors 5, 7, 11, 17, and 25. -/
theorem cover_scales {s n : ℕ} (initial : 5*n≤12*18750^2 → Represented s n)
    (residue : ∀ d b : ℕ, (d=1 ∨ d=7 ∨ d=11 ∨ d=17) → ∃ x y,
      let M := 6*d*5^(b+4)
      polygonal s x+polygonal s y ≡ n [MOD M] ∧ 6*(polygonal s x+polygonal s y)<5*M^2) :
    Represented s n := by
  let reaches (M : ℕ) := 5*n≤12*M^2 → Represented s n
  let band (M : ℕ) := 5*M^2≤6*n → reaches M
  have at_scale (d b : ℕ) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) : band (d*scale b) := by
    have eq : d*scale b = 6*d*5^(b+4) := by unfold scale; ac_rfl
    rw [eq]
    intro lower upper
    obtain ⟨x,y,res,low⟩ := residue d b hd
    have pd : 0<d := by omega
    exact fill_layer (by positivity) (scale_practical d (b+4) · hd (by omega))
      res (by omega) upper
  have bridge {D a b : ℕ} (overlap : 25*b^2≤72*a^2) (prev : reaches (a*D))
      (next : band (b*D)) : reaches (b*D) := by
    intro high
    by_cases h : 5*n≤12*(a*D)^2
    · exact prev h
    · have bound : 25*(b*D)^2≤72*(a*D)^2 := by
        simpa only [mul_pow, ←mul_assoc] using Nat.mul_le_mul_right (D^2) overlap
      exact next (by omega) high
  have cover (b : ℕ) : reaches (5*scale b) := by
    induction b with
    | zero => exact initial
    | succ b ih =>
      have seven := bridge (b:=7) (by decide) ih (at_scale 7 b (by decide))
      have eleven := bridge (b:=11) (by decide) seven (at_scale 11 b (by decide))
      have seventeen := bridge (b:=17) (by decide) eleven (at_scale 17 b (by decide))
      have top := at_scale 1 (b+2) (by decide)
      have eq : 1*scale (b+2)=25*scale b := by rw [one_mul,scale_succ,scale_succ]; ring
      rw [eq] at top
      have last := bridge (b:=25) (by decide) seventeen top
      simpa only [scale_succ,←mul_assoc,show 5*5=25 by decide] using last
  apply cover n
  have growth : n < 5^n := Nat.lt_pow_self (by decide : 1<5)
  have eq : 5*scale n = 18750*5^n := by simp [scale,pow_add]; ring
  rw [eq]
  nlinarith only [growth, Nat.le_mul_self (5^n)]

end PracticalPolygons
