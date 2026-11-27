module

public import conjectures.ChauveHistoryGrowth.Grammar
public import Mathlib.RingTheory.PowerSeries.Catalan

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries

def seed : S := map (Nat.castRingHom ℝ) (catalanSeries*X)

theorem seed_quad : seed=X+seed*seed := by
  have c := congrArg (fun F : PowerSeries ℕ => map (Nat.castRingHom ℝ) F)
    catalanSeries_sq_mul_X_add_one
  simp only [map_add,map_mul,map_pow,map_X,map_one] at c
  simp only [seed,map_mul,map_X]
  linear_combination -X*c

theorem seed_zero : constantCoeff seed=0 := by simp [seed]
theorem seed_succ (n : ℕ) : coeff (n+1) seed=(catalan n : ℝ) := by
  simp [seed,coeff_map]
def U (A : ℝ) := rescale A seed

theorem Uzero (A : ℝ) : constantCoeff (U A)=0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,U,coeff_rescale,coeff_zero_eq_constantCoeff_apply,seed_zero,mul_zero]
theorem Ucoeff (A : ℝ) (n : ℕ) : coeff (n+1) (U A)=A^(n+1)*catalan n := by
  rw [U,coeff_rescale,seed_succ]
theorem Upos {A : ℝ} (ha : 0≤A) : 0 ≼ U A := by
  rw [zeroBelow]; intro n
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply,Uzero]
  | succ n => rw [Ucoeff]; positivity
theorem Uquad (A : ℝ) : U A=A • X+U A*U A := by
  have h := congrArg (rescale A) seed_quad
  simpa [U,rescale_X,PowerSeries.smul_eq_C_mul] using h

theorem scale_mono {a b : ℝ} {p : S} (h : a≤b) (k : 0 ≼ p) : a • p ≼ b • p := by
  intro n; simp only [map_smul,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right h ((zeroBelow _).mp k _)
theorem scale_series {a : ℝ} {p q : S} (h : 0≤a) (k : p ≼ q) : a • p ≼ a • q := by
  intro n; simp only [map_smul,smul_eq_mul]; exact mul_le_mul_of_nonneg_left (k _) h

theorem scale_pos {a : ℝ} {p : S} (h : 0≤a) (k : 0 ≼ p) : 0 ≼ a • p := by
  simpa using scale_series h k

theorem Xpos : 0 ≼ (X : S) := by
  rw [zeroBelow]; intro n; by_cases h : n=1 <;> simp [coeff_X,h]

theorem Ubound {A : ℝ} (h : 0≤A) : U A*U A ≼ U A := by
  conv_rhs => rw [Uquad]
  simpa using addM (scale_pos h Xpos) (refl (U A*U A))

theorem Uestimate {A : ℝ} (h : 0≤A) (n : ℕ) : coeff n (U A)≤(4*A)^n := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,Uzero]
  | succ n =>
    rw [Ucoeff,mul_pow,mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg h _)
    have hc : catalan n≤4^n := by
      rw [catalan_eq_centralBinom_div]
      exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow _)
    exact_mod_cast hc.trans (Nat.pow_le_pow_right (by decide : 0<4) (Nat.le_succ n))

private theorem supersolution {f h y : S} (eq : h=f+h*h) (hz : constantCoeff h=0)
    (yz : constantCoeff y=0) (hp : 0 ≼ h) (yp : 0 ≼ y) (bound : f+y*y ≼ y) : h ≼ y := by
  apply subP.mp
  apply nonneg_fixed (subP.mpr bound) (addP hp yp) (by simp [hz,yz])
  linear_combination -eq

inductive Budget (A : ℝ) : Tree → ℝ → Prop where
  | tip (y : ℝ) (lo : 0≤y) (hi : y≤1) (seed : 1≤y*A) : Budget A .tip y
  | fork {a b : Tree} {x z : ℝ} (y : ℝ) (lo : 0≤y) (hi : y≤1)
      (left : Budget A a x) (right : Budget A b z) (total : y*y+x+z+x*z≤y) :
      Budget A (.fork a b) y

theorem Budget.pos {A y : ℝ} {t : Tree} (b : Budget A t y) : 0≤y := by cases b <;> assumption

theorem Budget.raise {A B y : ℝ} {t : Tree} (b : Budget A t y) (le : A≤B) : Budget B t y := by
  induction b with
  | tip y lo hi seed => exact .tip _ lo hi (seed.trans (mul_le_mul_of_nonneg_left le lo))
  | fork y lo hi _ _ h l r => exact .fork _ lo hi l r h

theorem Budget.bound {A y : ℝ} {t : Tree} (b : Budget A t y) (ha : 0≤A) : H t ≼ y • U A := by
  have uu := Upos ha
  have sz (q : ℝ) : constantCoeff (q • U A)=0 := by simp [PowerSeries.smul_eq_C_mul,Uzero]
  have mul_scale (x z : ℝ) : (x • U A)*(z • U A)=(x*z) • (U A*U A) := by
    simp [smul_smul,mul_comm]
  induction b with
  | tip y lo hi seed =>
    apply supersolution leaf_grammar (hz _) (sz _) (hp _) (scale_pos lo uu)
    conv_rhs => rw [Uquad]
    rw [smul_add,smul_smul,mul_scale]
    have x : X ≼ (y*A) • (X : S) := by simpa using scale_mono seed Xpos
    exact addM x (scale_mono (by nlinarith) (mulP uu uu))
  | @fork a b x z y lo hi l r total ih jh =>
    have eq : H (.fork a b)=(H a+H b+H a*H b)+H (.fork a b)*H (.fork a b) := by
      linear_combination fork_grammar a b
    apply supersolution eq (hz _) (sz _) (hp _) (scale_pos lo uu)
    have t1 := mulM ih jh (hp _) (scale_pos r.pos uu)
    rw [mul_scale] at t1 ⊢
    have t2 := trans t1 (scale_series (mul_nonneg l.pos r.pos) (Ubound ha))
    have t3 := scale_series (mul_nonneg lo lo) (Ubound ha)
    have sum := addM (addM (addM ih jh) t2) t3
    rw [← add_smul,← add_smul,← add_smul] at sum
    exact trans sum (scale_mono (by linarith) uu)

theorem exists_budget (t : Tree) {y : ℝ} (lo : 0<y) (hi : y≤1/2) :
    ∃ A : ℝ, 1≤A ∧ Budget A t y := by
  induction t generalizing y with
  | tip =>
    refine ⟨1/y,(le_div_iff₀ lo).mpr (by linarith),.tip _ lo.le (by linarith) ?_⟩
    rw [mul_one_div_cancel lo.ne']
  | fork a b ha hb =>
    let w:=y/8
    have wp : 0<w := by dsimp [w]; positivity
    have wu : w≤1/2 := by dsimp [w]; linarith
    obtain ⟨A,A1,la⟩ := ha wp wu
    obtain ⟨B,_,lb⟩ := hb wp wu
    refine ⟨max A B,A1.trans (le_max_left ..),
      .fork _ lo.le (by linarith) (la.raise (le_max_left ..)) (lb.raise (le_max_right ..)) ?_⟩
    dsimp [w]
    nlinarith [mul_nonneg lo.le (sub_nonneg.mpr hi)]

theorem Budget.hi {A y : ℝ} {t : Tree} (b : Budget A t y) : y≤1 := by cases b <;> assumption

theorem Budget.upper {A y : ℝ} {t : Tree} (b : Budget A t y) (ha : 0≤A) (n : ℕ) :
    (count t n : ℝ)≤(4*A)^n := by
  have mono : y • U A ≼ U A := by simpa using scale_mono b.hi (Upos ha)
  rw [← hc]
  exact (trans (b.bound ha) mono n).trans (Uestimate ha n)

def weight (x : ℝ) := (x+x*x)/16

theorem weight_step {x z : ℝ} (hx : 0≤x) (hz : 0≤z) (lim : x+z≤1)
    (xx : x≤2*z) (zz : z≤2*x) :
    weight (x+z)*weight (x+z)+weight x+weight z+weight x*weight z≤weight (x+z) := by
  have pos {s : ℝ} (h : 0≤s) : 0≤weight s := by dsimp [weight]; positivity
  have small {s : ℝ} (h : 0≤s) (h' : s≤1) : weight s ≤ s/8 := by
    dsimp [weight]; nlinarith [mul_nonneg h (sub_nonneg.mpr h')]
  have hs := small (add_nonneg hx hz) lim
  have square := mul_self_le_mul_self (pos (add_nonneg hx hz)) hs
  have prod := mul_le_mul (small hx (by linarith)) (small hz (by linarith)) (pos hz)
    (show 0≤x/8 by positivity)
  have gap : weight (x+z)-weight x-weight z=x*z/8 := by dsimp [weight]; ring
  nlinarith only [square,prod,gap,mul_nonneg (sub_nonneg.mpr xx) (sub_nonneg.mpr zz),mul_nonneg hx hz]

theorem balanced_budget (k : ℕ) {t : Tree} (balanced : t.Balanced) (order : t.leaves≤k) :
    Budget (16*(k : ℝ)) t (weight (t.leaves/k)) := by
  have kpos : 0<(k : ℝ) := by exact_mod_cast t.leaves_pos.trans_le order
  have lower {s : ℝ} (h : 0≤s) : 0≤weight s := by dsimp [weight]; positivity
  have upper {s : ℝ} (h : 0≤s) (h' : s≤1) : weight s≤1 := by
    dsimp [weight]; nlinarith [mul_nonneg h (sub_nonneg.mpr h')]
  induction t with
  | tip =>
    simp only [Tree.leaves,Nat.cast_one]
    refine .tip _ (lower (by positivity)) (upper (by positivity) ((div_le_one kpos).mpr ?_)) ?_
    · exact_mod_cast order
    · dsimp [weight]; field_simp; nlinarith
  | fork a b ha hb =>
    obtain ⟨ba,bb,al,bl⟩ := balanced
    change a.leaves+b.leaves≤k at order
    let x : ℝ := a.leaves/k
    let z : ℝ := b.leaves/k
    have hx : 0≤x := by dsimp [x]; positivity
    have hz : 0≤z := by dsimp [z]; positivity
    have sum : ((Tree.fork a b).leaves : ℝ)/k=x+z := by simp [Tree.leaves,x,z,add_div]
    rw [sum]
    have lim : x+z≤1 := by
      dsimp [x,z]; rw [← add_div,div_le_one kpos]; exact_mod_cast order
    refine .fork _ (lower (add_nonneg hx hz)) (upper (add_nonneg hx hz) lim)
      (ha ba (by omega)) (hb bb (by omega)) (weight_step hx hz lim ?_ ?_)
    · dsimp [x,z]; rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ kpos.le
      exact_mod_cast (show a.leaves≤2*b.leaves by have := b.leaves_pos; omega)
    · dsimp [x,z]; rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ kpos.le
      exact_mod_cast (show b.leaves≤2*a.leaves by have := a.leaves_pos; omega)

end ChauveHistoryGrowth
end
