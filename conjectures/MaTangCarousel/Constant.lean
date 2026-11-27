module

public import conjectures.MaTangCarousel.Statement
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MaTangCarousel
open Real

/-- Even and odd terms in the sixth zeta value give the carousel's six-cycle density. -/
theorem alpha_six : alpha 6=13/960 := by
  let f (n : ℕ) : ℝ := 1/(n:ℝ)^6
  have bern : bernoulli 6=(1/42:ℚ) := by decide +kernel
  have all : HasSum f (π^6/945) := by
    convert hasSum_zeta_nat (k:=3) (by decide) using 1
    norm_num [bern,Nat.factorial]
    ring
  have even (n : ℕ) : f (2*n)=f n/64 := by simp [f,mul_pow]; ring
  have odd := tsum_even_add_odd (f:=f) (all.summable.comp_injective
    (show Function.Injective (fun n : ℕ ↦ 2*n) from fun _ _ h ↦ by dsimp only at h; omega))
    (all.summable.comp_injective
    (show Function.Injective (fun n : ℕ ↦ 2*n+1) from fun _ _ h ↦ by dsimp only at h; omega))
  simp_rw [even] at odd
  rw [tsum_div_const,all.tsum_eq] at odd
  have so : (∑' n : ℕ,f (2*n+1)) = π^6/960 := by linarith
  have scale (n : ℕ) : (1/(((2*n+1:ℕ):ℝ)*π))^6 = f (2*n+1)/π^6 := by
    simp [f,mul_pow,div_eq_mul_inv,mul_comm]
  unfold alpha
  simp_rw [scale]
  rw [tsum_div_const,so]
  field_simp [pi_ne_zero]
  ring

/-- At triangle density 1/9 the comparison construction has two parts. -/
theorem at_one_ninth : Profile 6 (1/9) ((15550/19683)/64) := by
  let z := (9+√69)/18
  have sq : (√69)^2=69 := Real.sq_sqrt (by norm_num)
  have low : (8:ℝ)<√69 := by nlinarith [Real.sqrt_nonneg 69]
  have high : √69<(9:ℝ) := by nlinarith [Real.sqrt_nonneg 69]
  have zp : 0<z := by dsimp [z]; linarith
  have z1 : z≤1 := by dsimp [z]; linarith
  have floor : ⌊z⁻¹⌋₊=1 := by
    apply (Nat.floor_eq_iff (inv_nonneg.mpr zp.le)).mpr
    constructor
    · simpa using (one_le_inv₀ zp).mpr z1
    · apply (inv_lt_comm₀ zp (by norm_num)).mpr
      dsimp [z]; linarith
  have prod : z*(1-z)=1/27 := by dsimp [z]; nlinarith
  have three : z^3+(1-z)^3=8/9 := by nlinarith
  have six : z^6+(1-z)^6=15550/19683 := by
    calc z^6+(1-z)^6 = (z^3+(1-z)^3)^2-2*(z*(1-z))^3 := by ring
         _ = _ := by rw [three,prod]; norm_num
  refine Or.inr ⟨z,zp,z1,?_,?_⟩ <;> simp [moment,floor,three,six] <;> norm_num

end MaTangCarousel
