module

public import conjectures.LuckySpots.Polynomial
import Mathlib.Topology.Algebra.Order.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section
namespace LuckySpots
open Finset Polynomial Filter
open scoped Topology

private theorem correction_limit {j : ℕ} (hj : 2≤j) :
    Tendsto (fun n : ℕ ↦ (((correction j).eval n:ℚ):ℝ)*((n-j+1:ℕ):ℝ)^(n-j+1)/(n+1:ℝ)^(n-1))
      atTop (𝓝 (((correction j).leadingCoeff:ℝ)*Real.exp (-(j:ℝ)))) := by
  let ι := Rat.castHom ℝ
  let f := (correction j).map ι
  let P : ℝ[X] := f*(X+C 1)^2
  let Q : ℝ[X] := (X+C (1-(j:ℝ)))^j
  obtain ⟨d,nz⟩ := degree_correction hj
  have fm : f≠0 := (Polynomial.map_ne_zero_iff ι.injective).mpr nz
  have md := monic_X_add_C (1:ℝ)
  have mq := monic_X_add_C (1-(j:ℝ))
  have degrees : P.degree=Q.degree := by
    rw [degree_eq_natDegree (mul_ne_zero fm (md.pow 2).ne_zero),degree_eq_natDegree (mq.pow j).ne_zero]
    rw [natDegree_mul fm (md.pow 2).ne_zero,md.natDegree_pow,mq.natDegree_pow,natDegree_X_add_C,
      natDegree_X_add_C,show f.natDegree=j-2 by simp only [f,natDegree_map_eq_of_injective ι.injective,d]]
    congr 1
    omega
  have ratio := (div_tendsto_atTop_leadingCoeff_div_of_degree_eq degrees).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have lead : P.leadingCoeff/Q.leadingCoeff=((correction j).leadingCoeff:ℝ) := by
    simp only [P,Q,f,leadingCoeff_mul,md.pow 2 |>.leadingCoeff,mq.pow j |>.leadingCoeff,
      leadingCoeff_map_of_injective ι.injective,mul_one,div_one]; rfl
  rw [lead] at ratio
  have expo := (Real.tendsto_one_add_div_pow_exp (-(j:ℝ))).comp (tendsto_add_atTop_nat 1)
  apply (ratio.mul expo).congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  have pos : 0<(n:ℝ)+1-(j:ℝ) := by apply sub_pos.mpr; exact_mod_cast (show j<n+1 by omega)
  have one : (n:ℝ)+1 ≠ 0 := by positivity
  have en :(n-j+1)+j=n+1 := by omega
  have en' :(n-1)+2=n+1 := by omega
  have ev : f.eval (n:ℝ)=(((correction j).eval n:ℚ):ℝ) := by
    simp [f,ι]
  simp only [Function.comp_apply,P,Q,eval_mul,eval_pow,eval_add,eval_X,eval_C,ev,Nat.cast_add_one]
  rw [show (n:ℝ)+(1-j)=(n:ℝ)+1-j by ring,show 1+ -(j:ℝ)/((n:ℝ)+1)=((n:ℝ)+1-j)/(n+1) by field_simp; ring,div_pow,show ((n-j:ℕ):ℝ)+1=(n:ℝ)+1-j by rw [Nat.cast_sub hn]; ring]
  rw [show ((n:ℝ)+1-j)^(n+1) = ((n:ℝ)+1-j)^(n-j+1)*((n:ℝ)+1-j)^j by rw [←pow_add,en],
    show ((n:ℝ)+1)^(n+1) = ((n:ℝ)+1)^(n-1)*((n:ℝ)+1)^2 by rw [←pow_add,en']]
  field_simp [one,pos.ne']

/-- The exact binomial-tail formula implies both assertions of Conjecture 13. -/
theorem of_closed_formula
    (formula : ∀ {n j : ℕ}, 0<j → j≤n → 2*(j:ℚ)*luckyNumber n j = ((j:ℚ)+1)*(n+1:ℚ)^(n-1) -
      ∑ h∈range (j-1), (n.choose h:ℚ)*(j:ℚ)^h*((n-j+1:ℕ):ℚ)^(n-1-h))
    (total : ∀ {n : ℕ}, 0<n → totalNumber n=(n+1)^(n-1)) : Conjecture := by
  constructor
  · intro n hn
    have h := formula (n:=n) (j:=1) (by decide) hn
    rw [total hn]
    norm_num at h
    exact_mod_cast (show (luckyNumber n 1:ℚ)=(n+1:ℚ)^(n-1) by linarith)
  intro j hj
  have pos : 0<j := by omega
  refine ⟨correction j,(degree_correction hj).1,?_,(correction j).leadingCoeff,?_⟩
  · intro n hn
    have h := formula pos hn
    rw [←correction_identity hj hn] at h
    field_simp
    linarith
  · apply (tendsto_const_nhds.sub (correction_limit hj)).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    have h := formula pos hn
    rw [←correction_identity hj hn] at h
    have h' : 2*(j:ℝ)*luckyNumber n j=((j:ℝ)+1)*(n+1:ℝ)^(n-1)-
      2*(j:ℝ)*((((correction j).eval n:ℚ):ℝ)*((n-j+1:ℕ):ℝ)^(n-j+1)) := by
      have lifted := congrArg (fun x : ℚ ↦ (x:ℝ)) h
      push_cast at lifted ⊢
      exact lifted
    rw [total (show 0<n by omega)]
    push_cast at h' ⊢
    field_simp
    linarith only [h']

end LuckySpots
