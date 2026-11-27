module

public import conjectures.CFPLogDensity.Statement
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity.Upper
open Finset Real

noncomputable def block (b : ℝ) (hb : 1<b) (x : ℝ) : ℕ :=
  if h : 1≤x then (exists_nat_pow_near h hb).choose else 0

theorem block_spec {b x : ℝ} (hb : 1<b) (hx : 1≤x) :
    b^block b hb x ≤ x ∧ x < b^(block b hb x+1) := by
  simpa only [block,dite_eq_left hx] using (exists_nat_pow_near hx hb).choose_spec

noncomputable def coloring (r : ℕ) (hr : 0<r) (b : ℝ) (hb : 1<b) (n : ℕ) : Fin r :=
  ⟨block b hb (log n)%r,Nat.mod_lt _ hr⟩

theorem coloring_uses_all {r : ℕ} (hr : 0 < r) {b : ℝ} (hb : 1 < b) :
    UsesAll (coloring r hr b hb) := by
  intro i
  have logpos : 0 < log 2 := log_pos (by norm_num)
  obtain ⟨t,ht⟩ := pow_unbounded_of_one_lt (log 2/(b-1)) hb
  let k := i.val+r*t
  have tk : t ≤ k := by dsimp [k]; nlinarith [Nat.mul_le_mul_right t (show 1 ≤ r from hr)]
  have sep := ((div_lt_iff₀ (sub_pos.mpr hb)).mp ht).trans_le
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb.le tk) (sub_nonneg.mpr hb.le))
  let m := ⌈b^k/log 2⌉₊
  have bp : 0 < b^k := pow_pos (by linarith) _
  have low : b^k ≤ (m:ℝ)*log 2 := (div_le_iff₀ logpos).mp (Nat.le_ceil _)
  have high : (m:ℝ)*log 2 < b^(k+1) := by
    have small := Nat.ceil_lt_add_one (div_pos bp logpos).le
    change (m:ℝ) < b^k/log 2+1 at small
    have sm := mul_lt_mul_of_pos_right small logpos
    rw [add_mul,div_mul_cancel₀ _ logpos.ne',one_mul] at sm
    rw [pow_succ]
    nlinarith
  have eq : log ((2^m:ℕ):ℝ)=(m:ℝ)*log 2 := by push_cast; rw [log_pow]
  have spec := block_spec hb ((one_le_pow₀ hb.le).trans low)
  have lower := (pow_lt_pow_iff_right₀ hb).mp (low.trans_lt spec.2)
  have upper := (pow_lt_pow_iff_right₀ hb).mp (spec.1.trans_lt high)
  have same : block b hb ((m:ℝ)*log 2)=k := by omega
  refine ⟨2^m,by positivity,Fin.ext ?_⟩
  change block b hb (log ((2^m:ℕ):ℝ))%r=i.val
  rw [eq,same]
  simp [k,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt i.isLt]

/-- All terms in a representation are bounded by its largest term, including terms from older blocks. -/
theorem covered {r : ℕ} (hr : 0<r) {b : ℝ} (hb : 1<b) (i : Fin r) {m : ℕ} (hm : 0<m)
    (member : m∈subsetSums (coloring r hr b hb) i) :
    log m≤2 ∨ ∃ t : ℕ, b^i.val*(b^r)^t ≤ log m ∧ log m ≤ (2*b)*(b^i.val*(b^r)^t) := by
  obtain ⟨A,all,rfl⟩ := member
  have ne : A.Nonempty := by
    by_contra! h
    simp [h] at hm
  let x := A.max' ne
  have hx := all x (A.max'_mem ne)
  have pos : 0<x := hx.1
  have le (z) (h : z∈A) : z≤x := A.le_max' _ h
  have size : A.card≤x := by
    calc
      _ ≤ (Icc 1 x).card := card_le_card (fun z hz ↦ mem_Icc.mpr ⟨(all z hz).1,le z hz⟩)
      _ = x := by simp
  have sumle : (∑ z ∈ A,z) ≤ x*x := calc
    _ ≤ ∑ _z ∈ A,x := sum_le_sum le
    _ = A.card*x := by simp
    _ ≤ _ := Nat.mul_le_mul_right x size
  have min : x ≤ ∑ z ∈ A,z := single_le_sum (f := fun n : ℕ ↦ n) (fun _ _ ↦ Nat.zero_le _) (A.max'_mem ne)
  have rp : 0<(x:ℝ) := by exact_mod_cast pos
  have lb : log x ≤ log (∑ z ∈ A,z : ℕ) := Real.log_le_log rp (by exact_mod_cast min)
  have ub : log (∑ z ∈ A,z : ℕ) ≤ 2*log x := calc
    _ ≤ log ((x:ℝ)*x) := Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast sumle)
    _ = _ := by rw [Real.log_mul rp.ne' rp.ne']; ring
  by_cases enough : 1≤log x
  · right
    let k := block b hb (log x)
    have color : k%r=i.val := congrArg Fin.val hx.2
    have expo : k=i.val+r*(k/r) := by simpa [←color] using (Nat.mod_add_div k r).symm
    have factors : b^k=b^i.val*(b^r)^(k/r) := by conv_lhs => rw [expo,pow_add,pow_mul]
    have spec := block_spec hb enough
    change b^k≤_ ∧ _<b^(k+1) at spec
    refine ⟨k/r,?_,?_⟩
    · rw [←factors]
      exact spec.1.trans lb
    · rw [←factors]
      rw [pow_succ] at spec
      nlinarith [spec.2]
  · left
    linarith

end CFPLogDensity.Upper
