module

public import conjectures.ChauveHistoryGrowth.Grammar

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth

open PowerSeries

def gain (t u : Tree) : S :=
  (input u-input t)*seqS (den (H t) (H u))

theorem gain_factor (t u : Tree) : P u = P t*(1+gain t u) := by
  let d := den (H t) (H u)
  have dz : constantCoeff d=0 := by simp [d,den,hz]
  have eq : P t*(input u-input t)=(H u-H t)*(1-d) := by
    rw [input_eq,input_eq]; dsimp [P,d,den]; ring
  symm
  calc
    P t*(1+gain t u)=P t+(P t*(input u-input t))*seqS d := by dsimp [gain,d]; ring
    _=P t+(H u-H t)*((1-d)*seqS d) := by rw [eq]; ring
    _=P u := by rw [seq_unit dz]; dsimp [P]; ring

theorem gain_unique {t u : Tree} {D : S} (eq : P u = P t*(1+D)) : gain t u =D := by
  have h : P t ≠ 0 := by
    intro bad
    have := congrArg constantCoeff bad
    simp [P,hz] at this
  have h' := mul_left_cancel₀ h ((gain_factor t u).symm.trans eq)
  exact add_left_cancel h'

theorem gain_in {t u : Tree} (h : input t ≼ input u) : 0 ≼ gain t u := by
  apply mulP (subP.mpr h)
  apply seq_pos (addP (addP (mulP (hp _) (hp _)) (hp _)) (mulP (hp _) (hp _)))
  simp [hz]

theorem gain_out {t u : Tree} (h : 0 ≼ gain t u) : H t ≼ H u := by
  have pp := mulP (Ppos t) h
  have eq : H u-H t=P t * gain t u := by
    calc
      H u-H t=P u-P t := by dsimp [P]; ring
      _=P t*gain t u := by rw [gain_factor t u]; ring
  exact subP.mp (eq ▸ pp)

theorem output_mono {t u : Tree} (h : input t ≼ input u) : H t ≼ H u := gain_out (gain_in h)

theorem gain_step {t u : Tree} {D : S} (eq : input u=input t*(1+D)) :
    gain t u = D*multiplier (H t) (H u) := by
  apply gain_unique
  apply multiplier_identity (hz _) (hz _)
  simpa only [← input_eq] using eq

theorem factor_mul_one (t u : Tree) : 1 ≼ multiplier (H t) (H u) :=
  multiplier_one (hp _) (hp _) (hz _) (hz _)

theorem factor_mul_pos (t u : Tree) : 0 ≼ multiplier (H t) (H u) :=
  trans onePos (factor_mul_one t u)

theorem gain_first (t u : Tree) : coeff 1 (gain t u) = (u.leaves : ℝ)-t.leaves := by
  have eq := congrArg (coeff 1) (gain_factor t u)
  have gz : constantCoeff (gain t u)=0 := by simp [gain,input_eq,hz]
  simp [P,coeff_one_mul,coeff_one,hc,leaf_one,hz,gz] at eq
  linarith

theorem mul_coeff_two (a b : S) :
    coeff 2 (a*b) = constantCoeff a*coeff 2 b + coeff 1 a*coeff 1 b + coeff 2 a*constantCoeff b := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i a * coeff j b)]
  simp [Finset.sum_range_succ,coeff_zero_eq_constantCoeff_apply,add_assoc]

theorem factor_first (t u : Tree) :
    coeff 1 (multiplier (H t) (H u)) = (t.leaves : ℝ)+u.leaves := by
  simp [multiplier,num,den,seqS,coeff_one_mul,hc,leaf_one,hz,coeff_one]

theorem gain_second_step {t u v w : Tree} (h : gain v w=gain t u*multiplier (H v) (H w))
    (s : u.leaves=t.leaves+1) :
    coeff 2 (gain v w)=coeff 2 (gain t u)+(v.leaves : ℝ)+w.leaves := by
  have gz : constantCoeff (gain t u)=0 := by simp [gain,input_eq,hz]
  have mz : constantCoeff (multiplier (H v) (H w))=1 := by
    simp [multiplier,num,den,hz]
  rw [h,mul_coeff_two,gz,mz,gain_first,factor_first,s,Nat.cast_add_one]
  ring

theorem base_gain : 0 ≼ gain .tip (.fork .tip .tip) := by
  apply gain_in
  apply subP.mp
  have eq : input (.fork .tip .tip) - input .tip = H .tip+H .tip*H .tip+H .tip*H .tip := by
    change (1+H .tip)*(1+H .tip)-(1+X)=_
    linear_combination leaf_grammar
  rw [eq]
  exact addP (addP (hp _) (mulP (hp _) (hp _))) (mulP (hp _) (hp _))

end ChauveHistoryGrowth
end
