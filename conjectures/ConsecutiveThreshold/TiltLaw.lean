module

public import conjectures.ConsecutiveThreshold.Series
public import conjectures.ConsecutiveThreshold.Concentration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators

theorem geom_balanced {q : ℝ} (hq : 0≤q) (c : ℕ) : Mass.balanced (geom q c).coeff := by
  intro a b d ab hd
  simp only [geom_coeff]
  by_cases ha : 0≤a ∧ a<(c:ℤ)
  · by_cases hb : 0≤b+d ∧ b+d<(c:ℤ)
    · have p : 0≤a+d ∧ a+d<(c:ℤ) := by omega
      have t : 0≤b ∧ b<(c:ℤ) := by omega
      rw [ite_eq_left ha,ite_eq_left hb,ite_eq_left p,ite_eq_left t,←pow_add,←pow_add]
      have id : a.toNat+(b+d).toNat=(a+d).toNat+b.toNat := by omega
      rw [id]
    · simp only [hb,ite_false,mul_zero]
      split <;> split <;> positivity
  · simp only [ha,ite_false,zero_mul]
    split <;> split <;> positivity

theorem one_balanced : Mass.balanced ((1 : Series).coeff) := by
  have e : geom (1:ℝ) 1 = 1 := by
    simp [geom,AddMonoidAlgebra.one_def]
  exact e ▸ geom_balanced (by norm_num) 1

theorem atOne_sum (P : Series) : atOne P = ∑ i∈P.coeff.support,P.coeff i := by
  calc
    _ = atOne (P.coeff.sum AddMonoidAlgebra.single) := by rw [AddMonoidAlgebra.sum_coeff_single]
    _ = _ := by simp [Finsupp.sum]

noncomputable def rawMass (P : Series) (hP : positiveSeries P) : Mass where
  w := P.coeff
  sites := P.coeff.support
  nonneg := hP
  zero_off _ h := Finsupp.notMem_support_iff.mp h

theorem weight_mul (P Q : Series) (p : positiveSeries P) (q : positiveSeries Q) (i : ℤ) :
    (P*Q).coeff i = ((rawMass P p).conv (rawMass Q q)).w i := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp only [Finsupp.sum,Mass.conv,rawMass,sub_eq_add_neg,add_comm i]

theorem series_balanced_mul (P Q : Series) (p : positiveSeries P) (q : positiveSeries Q)
    (lp : Mass.balanced P.coeff) (lq : Mass.balanced Q.coeff) : Mass.balanced (P*Q).coeff := by
  intro a b d ab hd
  simp only [weight_mul P Q p q]
  exact Mass.balanced_conv (rawMass P p) (rawMass Q q) lp lq a b d ab hd

theorem geom_prod_balanced {α : Type*} (S : Finset α) {q : ℝ} (q0 : 0≤q) (d : α → ℕ) :
    Mass.balanced (∏ i∈S,geom q (d i)).coeff := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_balanced
  | insert i S hi ih =>
    rw [prod_insert hi]
    exact series_balanced_mul _ _ (positive_geom q0 _) (positive_prod _ _ (fun _ _ ↦ positive_geom q0 _))
      (geom_balanced q0 _) ih

noncomputable def normalized (P : Series) (p : positiveSeries P) (z : 0<atOne P) : Mass where
  w t := P.coeff t / atOne P
  sites := P.coeff.support
  nonneg t := div_nonneg (p t) z.le
  zero_off _ h := by rw [Finsupp.notMem_support_iff.mp h,zero_div]

theorem normalized_one (P : Series) (p : positiveSeries P) (z : 0<atOne P) :
    (normalized P p z).total=1 := by
  simp only [Mass.total,normalized,←sum_div,←atOne_sum,div_self z.ne']

theorem normalized_balanced (P : Series) (p : positiveSeries P) (z : 0<atOne P)
    (b : Mass.balanced P.coeff) : Mass.balanced (normalized P p z).w := by
  intro a c d ac hd
  simp only [normalized,div_mul_div_comm]
  exact div_le_div_of_nonneg_right (b a c d ac hd) (mul_nonneg z.le z.le)

theorem normalized_mul (P Q : Series) (p : positiveSeries P) (q : positiveSeries Q)
    (pp : 0<atOne P) (pq : 0<atOne Q) (i : ℤ) :
    ((normalized P p pp).conv (normalized Q q pq)).w i=(P*Q).coeff i/(atOne P*atOne Q) := by
  rw [weight_mul P Q p q]
  simp only [Mass.conv,normalized,rawMass,div_mul_div_comm,sum_div]

theorem conv_peak_upper (P Q : Series) (p : positiveSeries P) (q : positiveSeries Q)
    (b : ℤ) (peak : ∀ i,Q.coeff i≤Q.coeff b) (i : ℤ) :
    (P*Q).coeff i≤atOne P*Q.coeff b := by
  rw [weight_mul _ _ p q,atOne_sum,sum_mul]
  exact sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (peak _) (p j)

/-- A likelihood bound for an event carried by the first convolution factor. -/
theorem slice_bound (P R Y B : Series) (p : positiveSeries P) (r : positiveSeries R)
    (y : positiveSeries Y) (b : positiveSeries B)
    (pp : 0<atOne P) (pr : 0<atOne R)
    (lp : Mass.balanced P.coeff) (lr : Mass.balanced R.coeff)
    (factor : R=P*Y) (m : ℤ) (mode : ∀ i,(P*R).coeff i≤(P*R).coeff m) :
    (B*R).coeff m ≤ 52*(atOne B/atOne P)*(P*R).coeff m := by
  let f := normalized P p pp
  let g := normalized R r pr
  have fu := normalized_one P p pp
  have gu := normalized_one R r pr
  obtain ⟨h,_,fx⟩ := f.exists_peak fu
  obtain ⟨j,gp,gx⟩ := g.exists_peak gu
  have ftop (i) : P.coeff i≤P.coeff h := (div_le_div_iff_of_pos_right pp).mp (fx i)
  have gtop (i) : R.coeff i≤R.coeff j := (div_le_div_iff_of_pos_right pr).mp (gx i)
  have yr : atOne R=atOne P*atOne Y := by rw [factor,map_mul]
  have order : g.w j≤f.w h := by
    apply (div_le_div_iff₀ pr pp).mpr
    have e := conv_peak_upper Y P y p h ftop j
    rw [mul_comm Y P,←factor] at e
    rw [yr]
    nlinarith only [mul_le_mul_of_nonneg_right e pp.le]
  have cm (i) : (f.conv g).w i≤(f.conv g).w m := by
    rw [show (f.conv g).w i=(P*R).coeff i/(atOne P*atOne R) from normalized_mul ..,
      show (f.conv g).w m=(P*R).coeff m/(atOne P*atOne R) from normalized_mul ..]
    exact div_le_div_of_nonneg_right (mode i) (mul_nonneg pp.le pr.le)
  have pc := Mass.peak_comparison f g (normalized_balanced P p pp lp) (normalized_balanced R r pr lr)
    fu gu h j m fx gx gp order cm
  change R.coeff j/atOne R≤52*_ at pc
  rw [show (f.conv g).w m=(P*R).coeff m/(atOne P*atOne R) from normalized_mul ..] at pc
  have scale : R.coeff j*atOne P≤52*(P*R).coeff m := by
    field_simp [pp.ne',pr.ne'] at pc
    linarith
  have bp : 0≤atOne B := by rw [atOne_sum]; exact sum_nonneg fun i _ ↦ b i
  have bound :=  conv_peak_upper B R b r j gtop m
  calc
    _ ≤ atOne B*R.coeff j := bound
    _ ≤ atOne B*(52*(P*R).coeff m/atOne P) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ pp).mpr scale) bp
    _ = _ := by ring

end ConsecutiveThreshold
