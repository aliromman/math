module

public import conjectures.BellecFritzDice.Law
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace BellecFritzDice
open Set MeasureTheory Finset unitInterval
noncomputable section

private def geom (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range (n+2), x^j
private def prob (n : ℕ) (x : ℝ) : ℝ := geom n (1-x)/(geom n x+geom n (1-x))

private theorem geom_pos (n : ℕ) {x : ℝ} (h : 0≤x) : 0 < geom n x := by
  apply sum_pos' (fun j _ => pow_nonneg h j)
  exact ⟨0,by simp,by simp⟩

private theorem prob_eq (p : I) (h₀ : 0<(p:ℝ)) (h₁ : (p:ℝ)<1) (n : ℕ) :
    chance (die p (n+3)) n = prob n p := by
  rw [chance_die p h₀ h₁]
  let q : ℝ := p
  have left : splitChance p n = q*(1-q)*geom n (1-q) := by
    have eq := geom_sum_mul_neg (1-q) (n+2)
    change geom n (1-q)*(1-(1-q))=1-(1-q)^(n+2) at eq
    change (1-q)-(1-q)^(n+3)=_
    rw [show n+3=(n+2)+1 by omega,pow_succ]
    nlinarith [congrArg (fun z:ℝ => z*(1-q)) eq]
  have right : q-q^(n+3)=q*(1-q)*geom n q := by
    have eq := geom_sum_mul_neg q (n+2)
    change geom n q*(1-q)=1-q^(n+2) at eq
    rw [show n+3=(n+2)+1 by omega,pow_succ]
    nlinarith [congrArg (fun z:ℝ => z*q) eq]
  have total : 1-sameChance p n=q*(1-q)*(geom n q+geom n (1-q)) := by
    have sum : 1-sameChance p n = splitChance p n+(q-q^(n+3)) := by unfold sameChance splitChance q;ring
    rw [sum,left,right];ring
  rw [left,total]
  unfold prob
  change _=geom n (1-q)/(geom n q+geom n (1-q))
  exact mul_div_mul_left _ _ (mul_ne_zero h₀.ne' (sub_pos.mpr h₁).ne')

/-- Every interior value occurs for a bounded nonnegative atomless distribution. -/
theorem attainable_spectrum (n : ℕ) (y : ℝ) :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧ μ (Iio 0)=0 ∧ chance μ n=y) ↔
    1/(n+3:ℝ)<y ∧ y<(n+2:ℝ)/(n+3) := by
  constructor
  · rintro ⟨μ,hμ,hd,_,rfl⟩
    let := hμ
    let := hd
    exact ⟨strict_lower μ n,strict_upper μ n⟩
  · intro hy
    have cont : ContinuousOn (prob n) (Icc 0 1) := by
      apply ContinuousOn.div
      · unfold geom;fun_prop
      · unfold geom;fun_prop
      · intro x hx
        exact (add_pos (geom_pos n hx.1) (geom_pos n (sub_nonneg.mpr hx.2))).ne'
    have endpoints : prob n 0=(n+2:ℝ)/(n+3) ∧ prob n 1=1/(n+3:ℝ) := by
      simp [prob,geom]
      ring_nf
      trivial
    obtain ⟨x,hx,ex⟩ := intermediate_value_Ioo' (f:=prob n) (zero_le_one : (0:ℝ)≤1) cont (by simpa [endpoints.1,endpoints.2] using hy)
    let p : I := ⟨x,⟨hx.1.le,hx.2.le⟩⟩
    exact ⟨die p (n+3),inferInstance,die_diffuse p hx.1 hx.2 (by omega),die_nonnegative _ _,
      (prob_eq p hx.1 hx.2 n).trans ex⟩

/-- With three rolls, the probability is affine in the probability of a leading one. -/
theorem three_rolls (p : I) (h₀ : 0<(p:ℝ)) (h₁ : (p:ℝ)<1) :
    chance (die p 3) 0 = (2-p)/3 := by
  rw [prob_eq p h₀ h₁ 0]
  simp [prob,geom,Finset.sum_range_succ]
  ring

end
end BellecFritzDice

namespace BellecFritzDice
open MeasureTheory Finset

theorem resolution : ¬Attainable := by
  rintro ⟨μ,prob,_,_,eq⟩
  let := prob
  have event : below 3 (0 : Fin 3) = {x | 2*x 0 < x 1+x 2} := by
    ext x
    change (3:ℝ)*x 0 < ∑ j, x j ↔ 2*x 0 < x 1+x 2
    rw [Fin.sum_univ_three]
    constructor <;> intro h <;> linarith
  have h := strict_upper μ 0
  norm_num only [chance,Nat.zero_add,Nat.cast_zero,zero_add] at h
  rw [event,eq] at h
  exact lt_irrefl _ h

/-- info: 'BellecFritzDice.attainable_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms attainable_spectrum

/-- info: 'BellecFritzDice.three_rolls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_rolls

/-- info: 'BellecFritzDice.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BellecFritzDice
