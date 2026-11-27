module

public import conjectures.McCuneSeatJumps.Statement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
open Finset MeasureTheory Set
namespace McCuneSeatJumps

def err (p : Shares) (h : ℕ) (a : Seats) (i : Fin 3) : ℝ := h*p i - a i

def Inside (p : Shares) (h : ℕ) (a : Seats) : Prop :=
  ∑ i, a i = h ∧ ∀ i j, err p h a i - err p h a j < 1

theorem continuous_shares (i : Fin 3) : Continuous (fun x => shares x i) := by
  fin_cases i <;> simp [shares] <;> fun_prop

theorem sum_shares (x : ℝ × ℝ) : ∑ i, shares x i = 1 := by
  simp [Fin.sum_univ_three,shares]

private theorem weak_cell {p : Shares} {h : ℕ} {a : Seats} (ha : Hamilton p h a) (i j) :
    err p h a i - err p h a j ≤ 1 := by
  obtain ⟨_,w,hw,ho⟩ := ha
  have e (k) : err p h a k = Int.fract ((h:ℝ)*p k) - if k ∈ w then 1 else 0 := by
    have H := congrArg (Int.cast (R:=ℝ)) (hw k)
    push_cast at H
    simp only [err,Int.fract]
    split_ifs at H ⊢ <;> linarith
  rw [e,e]
  have hn := Int.fract_nonneg ((h:ℝ)*p j)
  have hl := Int.fract_lt_one ((h:ℝ)*p i)
  by_cases hi : i ∈ w <;> by_cases hj : j ∈ w <;> simp only [hi,hj,ite_true,ite_false] <;>
    first | linarith | linarith [ho j hj i hi]

theorem inside_hamilton {p : Shares} {h : ℕ} {a : Seats} (hs : ∑ i, p i = 1)
    (ha : Inside p h a) : Hamilton p h a := by
  classical
  have he : ∑ i, err p h a i = 0 := by
    simp [err,sum_sub_distrib,← mul_sum,hs,← Nat.cast_sum,ha.1]
  have bounds i : -1 < err p h a i ∧ err p h a i < 1 := by
    have H₁ := sum_lt_sum_of_nonempty (s:=univ) univ_nonempty
      (fun j _ => show err p h a i - 1 < err p h a j by linarith [ha.2 i j])
    have H₂ := sum_lt_sum_of_nonempty (s:=univ) univ_nonempty
      (fun j _ => show err p h a j < err p h a i + 1 by linarith [ha.2 j i])
    simp [he] at H₁ H₂
    constructor <;> linarith
  let w := univ.filter fun i => err p h a i < 0
  have floor (i) : ⌊(h:ℝ)*p i⌋ = (a i:ℤ) - if i ∈ w then 1 else 0 := by
    obtain ⟨lo,hi⟩ := bounds i
    have hw : i ∈ w ↔ err p h a i < 0 := by simp [w]
    by_cases q : err p h a i < 0
    · rw [ite_eq_left (hw.mpr q), Int.floor_eq_iff]
      unfold err at lo hi q
      push_cast
      constructor <;> linarith
    · rw [ite_eq_right (mt hw.mp q), sub_zero, Int.floor_eq_iff]
      unfold err at lo hi q
      push_cast
      constructor <;> linarith
  refine ⟨ha.1,w,fun i => by rw [floor]; omega,?_⟩
  intro i hi j hj
  have h₀ := ha.2 j i
  rw [Int.fract,Int.fract,floor,floor,ite_eq_left hi,ite_eq_right hj]
  push_cast
  unfold err at h₀
  linarith

private theorem no_wall {h : ℕ} (hh : 0 < h) {i j : Fin 3} (hij : i ≠ j) (z : ℤ) :
    volume {x : ℝ × ℝ | (h:ℝ)*(shares x i-shares x j) = z} = 0 := by
  have meas : MeasurableSet {x : ℝ × ℝ | (h:ℝ)*(shares x i-shares x j) = z} :=
    (isClosed_eq (continuous_const.mul ((continuous_shares i).sub (continuous_shares j)))
      continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply meas]
  have H (x : ℝ) : volume {y : ℝ | (h:ℝ)*(shares (x,y) i-shares (x,y) j)=z} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro y hy v hv
    have eq : shares (x,y) i-shares (x,y) j = shares (x,v) i-shares (x,v) j :=
      mul_left_cancel₀ (show (h:ℝ) ≠ 0 by positivity) (hy.trans hv.symm)
    fin_cases i <;> fin_cases j <;> simp_all [shares] <;> linarith
  simp only [show (fun x : ℝ => volume (Prod.mk x ⁻¹'
      {x : ℝ × ℝ | (h:ℝ)*(shares x i-shares x j)=z})) = fun _ => 0 from funext H,
    lintegral_zero]

/-- Ties affect a countable union of lines, which has area zero. -/
theorem ae_inside {h : ℕ} (hh : 0 < h) :
    ∀ᵐ x : ℝ × ℝ, ∀ a, Hamilton (shares x) h a → Inside (shares x) h a := by
  have reg : ∀ᵐ x : ℝ × ℝ, ∀ (i j : Fin 3), i ≠ j →
      ∀ z : ℤ, (h:ℝ)*(shares x i-shares x j) ≠ z := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases eq : i = j
    · exact Filter.Eventually.of_forall fun _ e => (e eq).elim
    · have hz := ae_all_iff.mpr fun z => measure_eq_zero_iff_ae_notMem.mp (no_wall hh eq z)
      filter_upwards [hz] with x hx
      exact fun _ => hx
  filter_upwards [reg] with x hx a ha
  refine ⟨ha.1,fun i j => (weak_cell ha i j).lt_of_ne ?_⟩
  intro eq
  by_cases hij : i=j
  · subst j; simp at eq
  · apply hx i j hij (1 + (a i:ℤ) - a j)
    push_cast
    unfold err at eq
    linarith

end McCuneSeatJumps
