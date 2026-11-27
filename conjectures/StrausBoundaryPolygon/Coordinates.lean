module

public import conjectures.StrausBoundaryPolygon.Quadrilateral

@[expose] public section
namespace StrausBoundaryPolygon.Heptagon
open Real Set
noncomputable section

def θ : ℝ := 2*Real.pi/7

private def f (x : ℝ) := 8*x^3+4*x^2-4*x-1

private theorem increasing {a b : ℝ} (ha : 1/2≤a) (hb : a≤b) : f a≤f b := by
  have ab : 0≤a*b := mul_nonneg (by linarith) (by linarith)
  have pos : 0≤8*(a^2+a*b+b^2)+4*(a+b)-4 := by nlinarith [sq_nonneg a,sq_nonneg b]
  unfold f
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) pos]

private theorem first_bounds :
    (62348:ℝ)/100000 ≤ cos θ ∧ cos θ ≤ 62350/100000 ∧
    78182/100000 ≤ sin θ ∧ sin θ ≤ 78184/100000 := by
  have p := pi_pos
  have a : 0<θ := by dsimp [θ]; linarith
  have b : θ<Real.pi/3 := by dsimp [θ]; linarith
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi a.le (show Real.pi/3≤Real.pi by linarith) b
  rw [Real.cos_pi_div_three] at hc
  have one := Real.cos_lt_cos_of_nonneg_of_le_pi (show 0≤(0:ℝ) by norm_num) (show θ≤Real.pi by linarith) a
  rw [cos_zero] at one
  have reflect : 2*(2*θ)=2*Real.pi-3*θ := by unfold θ; ring
  have relation : cos (2*(2*θ))=cos (3*θ) := by rw [reflect,cos_two_pi_sub]
  rw [cos_two_mul,cos_two_mul,cos_three_mul] at relation
  have fact : (cos θ-1)*f (cos θ)=0 := by unfold f; nlinarith only [relation]
  have zero := (mul_eq_zero.mp fact).resolve_left (sub_ne_zero.mpr one.ne)
  have lo : (62348:ℝ)/100000 ≤ cos θ := by
    by_contra! h
    have := increasing hc.le h.le
    rw [zero] at this
    norm_num [f] at this
  have hi : cos θ ≤ (62350:ℝ)/100000 := by
    by_contra! h
    have := increasing (by norm_num : (1:ℝ)/2≤62350/100000) h.le
    rw [zero] at this
    norm_num [f] at this
  have s0 := sin_pos_of_pos_of_lt_pi a (by linarith)
  have s2 := sin_sq_add_cos_sq θ
  have lo₂ := pow_le_pow_left₀ (by norm_num : 0≤(62348:ℝ)/100000) lo 2
  have hi₂ := pow_le_pow_left₀ (by linarith : 0≤cos θ) hi 2
  refine ⟨lo,hi,?_,?_⟩
  · by_contra! h
    have hs := pow_lt_pow_left₀ h s0.le (by decide : 2≠0)
    nlinarith
  · by_contra! h
    have hs := pow_lt_pow_left₀ h (by norm_num) (by decide : 2≠0)
    nlinarith

def coordBox : Fin 7 → (ℤ×ℤ)×(ℤ×ℤ) :=
  ![((10000,10000),(0,0)),((6234,6236),(7817,7820)),((-2227,-2223),(9747,9752)),
    ((-9012,-9007),(4334,4343)),((-9012,-9007),(-4343,-4334)),
    ((-2227,-2223),(-9752,-9747)),((6234,6236),(-7820,-7817))]

/-- Rational enclosures for the regular heptagon. All endpoints have denominator 10000. -/
theorem coordinate_bounds (i : Fin 7) :
    (coordBox i).1.1 ≤ 10000*(regularVertex 7 i).1 ∧
    10000*(regularVertex 7 i).1 ≤ (coordBox i).1.2 ∧
    (coordBox i).2.1 ≤ 10000*(regularVertex 7 i).2 ∧
    10000*(regularVertex 7 i).2 ≤ (coordBox i).2.2 := by
  obtain ⟨cl,cu,sl,su⟩ := first_bounds
  have c0 : 0≤cos θ := by linarith
  have s0 : 0≤sin θ := by linarith
  have cl2 := pow_le_pow_left₀ (by norm_num : 0≤(62348:ℝ)/100000) cl 2
  have cu2 := pow_le_pow_left₀ c0 cu 2
  have cl3 := pow_le_pow_left₀ (by norm_num : 0≤(62348:ℝ)/100000) cl 3
  have cu3 := pow_le_pow_left₀ c0 cu 3
  have sl3 := pow_le_pow_left₀ (by norm_num : 0≤(78182:ℝ)/100000) sl 3
  have su3 := pow_le_pow_left₀ s0 su 3
  have csL := mul_le_mul sl cl (by norm_num : 0≤(62348:ℝ)/100000) s0
  have csU := mul_le_mul su cu c0 (by norm_num : 0≤(78184:ℝ)/100000)
  have v (j : Fin 7) : regularVertex 7 j = (cos (j.val*θ),sin (j.val*θ)) := by
    unfold regularVertex θ
    congr 2 <;> ring
  have a4 : 4*θ=2*Real.pi-3*θ := by unfold θ; ring
  have a5 : 5*θ=2*Real.pi-2*θ := by unfold θ; ring
  have a6 : 6*θ=2*Real.pi-θ := by unfold θ; ring
  rw [v]
  fin_cases i <;> norm_num [coordBox,a4,a5,a6,cos_two_pi_sub,sin_two_pi_sub,cos_two_mul,sin_two_mul,
    cos_three_mul,sin_three_mul] <;> repeat' constructor
  all_goals nlinarith only [cl,cu,sl,su,cl2,cu2,cl3,cu3,sl3,su3,csL,csU]

theorem reflected (i : Fin 7) (hi : 0 < i.val) :
    regularVertex 7 ⟨7-i.val,by omega⟩ = ((regularVertex 7 i).1,-(regularVertex 7 i).2) := by
  unfold regularVertex
  have h : ((7-i.val:ℕ):ℝ)=7-(i.val:ℝ) := by rw [Nat.cast_sub (by omega : i.val≤7)]; norm_num
  norm_num only [Nat.cast_ofNat]
  rw [h,show 2*Real.pi*(7-(i.val:ℝ))/7=2*Real.pi-2*Real.pi*i.val/7 by ring,
    cos_two_pi_sub,sin_two_pi_sub]

end
end StrausBoundaryPolygon.Heptagon
