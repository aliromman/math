module

public import conjectures.CFPLogDensity.UpperColor
public import conjectures.CFPLogDensity.UpperMass
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace CFPLogDensity.Upper
open Finset Filter Real
open scoped Topology

private theorem finite_cover {S : Set ℕ} {R c a : ℝ} (R1 : 1<R) (c1 : 1≤c) (gap : c≤R) (a0 : 0<a)
    (coverage : ∀ m∈S, 0<m → log m≤2 ∨ ∃ t : ℕ, a*R^t ≤ log m ∧ log m≤c*(a*R^t))
    (N j : ℕ) (start : a*R^j≤log N) (stop : log N<a*R^(j+1)) :
    logMass S N ≤ (4+j) + coverValue R c*log N := by
  classical
  let K := Icc 1 N
  let small := K.filter fun (n : ℕ) ↦ log n≤2
  let lo := fun t : ℕ ↦ a*R^t
  let part := fun t : ℕ ↦ K.filter fun (n : ℕ) ↦ lo t ≤ log n ∧ log n ≤ min (c*lo t) (log N)
  let target := K.filter (·∈S)
  have sub : target⊆small ∪ (range (j+1)).biUnion part := by
    intro m hm
    obtain ⟨inK,inS⟩ := mem_filter.mp hm
    obtain ⟨pos,cut⟩ := mem_Icc.mp inK
    rcases coverage m inS pos with low|⟨t,lower,upper⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨inK,low⟩)
    · have logCut : log m≤log N := Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast cut)
      have bound : t<j+1 := by
        by_contra! bad
        have high := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ R1.le bad) a0.le
        linarith
      exact mem_union_right _ (mem_biUnion.mpr ⟨t,mem_range.mpr bound,
        mem_filter.mpr ⟨inK,lower,le_min upper logCut⟩⟩)
  have smallBound : mass small ≤ 3 := by
    have h : mass small ≤ 1+(2:ℝ)-0 := by
      apply mass_interval (by norm_num)
      intro n hn
      obtain ⟨hk,hl⟩ := mem_filter.mp hn
      have pos := (mem_Icc.mp hk).1
      exact ⟨pos,Real.log_nonneg (by exact_mod_cast pos),hl⟩
    linarith
  have earlier (t : ℕ) : mass (part t) ≤ 1+(c-1)*lo t := by
    have zero : 0≤lo t := by dsimp [lo]; positivity
    have bnd : mass (part t) ≤ 1+c*lo t-lo t := by
      apply mass_interval (by nlinarith [mul_nonneg (sub_nonneg.mpr c1) zero])
      intro n hn
      obtain ⟨hk,lb,ub⟩ := mem_filter.mp hn
      exact ⟨(mem_Icc.mp hk).1,lb,ub.trans (min_le_left ..)⟩
    linarith
  have last : mass (part j) ≤ 1+min (c*lo j) (log N)-lo j := by
    have zero : 0≤lo j := by dsimp [lo]; positivity
    apply mass_interval (le_min (by nlinarith [mul_nonneg (sub_nonneg.mpr c1) zero]) start)
    intro n hn
    obtain ⟨hk,lb,ub⟩ := mem_filter.mp hn
    exact ⟨(mem_Icc.mp hk).1,lb,ub⟩
  have bound := (mass_mono sub).trans (mass_cover small part (j+1))
  rw [sum_range_succ] at bound
  have ancient := (sum_le_sum (s := range j) (fun t _ ↦ earlier t)).trans (preceding R1 c1 a0.le j)
  have lastLength := geometric_cover (a := lo j) (y := log N) R1 c1 gap
  change mass target ≤ _
  dsimp [lo] at *
  linarith

private theorem periodic_upper {S : Set ℕ} {R c a : ℝ} (R1 : 1<R) (c1 : 1≤c) (gap : c≤R) (a0 : 0<a)
    (coverage : ∀ m∈S, 0<m → log m≤2 ∨ ∃ t : ℕ, a*R^t ≤ log m ∧ log m≤c*(a*R^t)) :
    sampledDensity S ≤ coverValue R c := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro v hv
  let e := v-coverValue R c
  have ep : 0<e := sub_pos.mpr hv
  have tend : Tendsto (fun k : ℕ ↦ (k:ℝ)/R^k) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 R1
  obtain ⟨K,hK⟩ := eventually_atTop.mp (tend.eventually_lt_const (show 0<e*a/5 by positivity))
  let T := max K 1
  have large : ∀ᶠ N : ℕ in atTop, a*R^T≤log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have nonneg : ∀ᶠ N : ℕ in atTop, 0≤logMass S N/log N := by
    filter_upwards [large] with N hN
    have pos : 0<log N := lt_of_lt_of_le (mul_pos a0 (pow_pos (by linarith) T)) hN
    apply div_nonneg _ pos.le
    unfold logMass
    exact sum_nonneg fun _ _ ↦ by positivity
  apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop nonneg)
  filter_upwards [large] with N hN
  have one : 1≤log N/a := by
    apply (le_div_iff₀ a0).mpr
    have ge := one_le_pow₀ R1.le (n := T)
    nlinarith [mul_nonneg a0.le (sub_nonneg.mpr ge)]
  obtain ⟨j,lb,ub⟩ := exists_nat_pow_near one R1
  have start : a*R^j≤log N := by simpa [mul_comm] using (le_div_iff₀ a0).mp lb
  have stop : log N<a*R^(j+1) := by simpa [mul_comm] using (div_lt_iff₀ a0).mp ub
  have tj : T≤j := by
    by_contra! bad
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ R1.le (show j+1≤T by omega)) a0.le
    linarith
  have jl : 1≤j := (le_max_right K 1).trans tj
  have q := (div_lt_iff₀ (pow_pos (by linarith : 0<R) j)).mp (hK j ((le_max_left K 1).trans tj))
  have rem : (4:ℝ)+j ≤ e*(log N) := by
    have onej : (1:ℝ)≤j := by exact_mod_cast jl
    have term := mul_le_mul_of_nonneg_left start ep.le
    nlinarith
  have pos : 0<log N := lt_of_lt_of_le (mul_pos a0 (pow_pos (by linarith) j)) start
  apply (div_le_iff₀ pos).mpr
  have h := finite_cover R1 c1 gap a0 coverage N j start stop
  dsimp [e] at rem
  linarith

end CFPLogDensity.Upper

namespace CFPLogDensity
open Upper Real

/-- The cyclic coloring from Conlon, Fox and Pham's upper bound. -/
theorem upper_coloring {r : ℕ} (hr : 0<r) {b : ℝ} (hb : 1<b) (gap : 2*b≤b^r) :
    ∃ color : ℕ→Fin r, UsesAll color ∧ ∀ i, sampledDensity (subsetSums color i)≤value r b := by
  let color := coloring r hr b hb
  refine ⟨color,coloring_uses_all hr hb,?_⟩
  intro i
  have R1 : 1<b^r := lt_of_lt_of_le (by linarith : 1<2*b) gap
  have density := periodic_upper (S := subsetSums color i) (R := b^r) (c := 2*b) (a := b^i.val)
    R1 (by linarith) gap (pow_pos (by linarith) _) (fun _ h pos ↦ covered hr hb i pos h)
  apply density.trans_eq
  unfold coverValue value
  have pos : 0<b := by linarith
  have diff : b^r-1≠0 := by linarith
  field_simp

end CFPLogDensity
