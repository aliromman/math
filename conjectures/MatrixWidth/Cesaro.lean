module

public import conjectures.MatrixWidth.Laws
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace MatrixWidth
open Finset Filter
open scoped Topology

private noncomputable def mean (N : ℕ) (f : ℕ→ℝ) := (∑ i ∈ range (N+1),f i)/((N:ℝ)+1)

private theorem mean_mono {N : ℕ} {f g : ℕ→ℝ} (h : ∀ i, f i≤g i) : mean N f≤mean N g :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _ => h i) (by positivity)

private theorem mean_const (N : ℕ) (c : ℝ) : mean N (fun _ => c)=c := by
  simp [mean,show (N:ℝ)+1≠0 by positivity]

private theorem mean_sum (N : ℕ) (s : Finset ℕ) (f : ℕ→ℕ→ℝ) :
    mean N (fun t => ∑ i∈s,f t i)=∑ i∈s,mean N (fun t => f t i) := by
  unfold mean
  rw [sum_comm,Finset.sum_div]

private theorem mean_mul (N : ℕ) (f : ℕ→ℝ) (c : ℝ) : mean N (fun i => f i*c)=mean N f*c := by
  unfold mean
  rw [←sum_mul]
  ring

private theorem tight {μ V : ℕ→ℝ} {C : ℝ} (hm : ∀x,0≤μ x) (hs : HasSum μ 1)
    (hw : ∀ x : ℕ, (x:ℝ)+1≤V x) (sumV : Summable (fun x => μ x*V x)) (bnd : (∑' x,μ x*V x)≤C)
    (b : ℕ) : 1-C/((b:ℝ)+1)≤∑ x∈range b,μ x := by
  let f (x : ℕ) := if x<b then μ x else 0
  have fsum : HasSum f (∑ x∈range b,μ x) := by
    have h : HasSum f (∑ i∈range b,f i) := hasSum_sum_of_ne_finset_zero (s:=range b) (f:=f) (fun x hx => by simp [f,show ¬x<b from fun e => hx (mem_range.mpr e)])
    simpa only [show (∑ i∈range b,f i)=∑ i∈range b,μ i from sum_congr rfl (fun i hi => by simp [f,mem_range.mp hi])] using h
  have h := fsum.add (sumV.hasSum.div_const ((b:ℝ)+1))
  have bp : 0<(b:ℝ)+1 := by positivity
  have pt (x : ℕ) : μ x≤f x+μ x*V x/((b:ℝ)+1) := by
    by_cases e : x<b
    · simp only [f,e,ite_true,le_add_iff_nonneg_right]
      exact div_nonneg (mul_nonneg (hm x) (by linarith only [hw x, Nat.cast_nonneg (α:=ℝ) x])) bp.le
    · have le : (b:ℝ)≤x := by exact_mod_cast (by omega : b≤x)
      simp only [f,e,ite_false,zero_add,le_div_iff₀ bp]
      exact mul_le_mul_of_nonneg_left (by linarith only [hw x,le]) (hm x)
  have a := hs.tsum_eq ▸ (hs.summable.tsum_le_tsum pt h.summable).trans_eq h.tsum_eq
  linarith only [a,div_le_div_of_nonneg_right bnd bp.le]

theorem stationary_exists {P} (hP : Kernel P) (col : ∀ y : ℕ, ∃ b : ℕ, ∀ i : ℕ, b ≤ i → P i y = 0)
    {V : ℕ→ℝ} {D : ℝ} (hw : ∀ x : ℕ, (x:ℝ)+1≤V x)
    (hf : ∀ x,Summable (fun y => P x y*V y)) (hd : ∀x,expect P x V≤V x/2+D) :
    ∃ π,Stationary P π := by
  obtain ⟨C,hC⟩ := laws_moment hP (fun x => by linarith only [hw x,Nat.cast_nonneg (α:=ℝ) x]) hf hd
  let v (N x : ℕ) := mean N (fun t => laws P t x)
  have vr (N x : ℕ) : 0≤v N x ∧ v N x≤1 := by
    constructor
    · exact (mean_const N 0).symm.trans_le (mean_mono (fun t => laws_nonneg hP t x))
    · exact (mean_mono (fun t => laws_le_one hP t x)).trans_eq (mean_const N 1)
  let q (N x : ℕ) : Set.Icc (0:ℝ) 1 := ⟨v N x,vr N x⟩
  obtain ⟨p,φ,hφ,lim⟩ := CompactSpace.tendsto_subseq q
  let π (x : ℕ) : ℝ := p x
  have limx (x : ℕ) : Tendsto (fun t => v (φ t) x) atTop (𝓝 (π x)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp lim x)
  have limsum (b : ℕ) : Tendsto (fun t => ∑ x∈range b,v (φ t) x) atTop (𝓝 (∑ x∈range b,π x)) :=
    tendsto_finsetSum _ fun i _ => limx i
  have upper (b : ℕ) : (∑ x∈range b,π x)≤1 := by
    apply le_of_tendsto' (limsum b)
    intro n
    change (∑ x∈range b,mean (φ n) (fun t => laws P t x))≤1
    rw [←mean_sum]
    exact (mean_mono (fun t => (laws_total hP t).tsum_eq ▸
        (laws_total hP t).summable.sum_le_tsum _ fun x _ => laws_nonneg hP t x)).trans_eq (mean_const _ 1)
  have lower (b : ℕ) : 1-C/((b:ℝ)+1)≤∑ x∈range b,π x := by
    apply ge_of_tendsto' (limsum b)
    intro n
    change 1-C/((b:ℝ)+1)≤∑ x∈range b,mean (φ n) (fun t => laws P t x)
    rw [←mean_sum]
    exact (mean_const _ _).symm.trans_le (mean_mono (fun t => tight (laws_nonneg hP t) (laws_total hP t) hw (hC t).1 (hC t).2 b))
  have norm : HasSum π 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => (p i).2.1)]
    have limC : Tendsto (fun n : ℕ => C/((n:ℝ)+1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using limC.const_sub 1) tendsto_const_nhds lower upper
  refine ⟨π,fun i => (p i).2.1,norm,?_⟩
  intro y
  obtain ⟨b,hb⟩ := col y
  have trunc (f : ℕ→ℝ) : push P f y = ∑ x∈range b,f x*P x y :=
    tsum_eq_sum fun x hx => by rw [hb x (by simpa using hx),mul_zero]
  have hstep (N : ℕ) :
      v N y - (∑ x∈range b,v N x*P x y) =
        (laws P 0 y-laws P (N+1) y)/((N:ℝ)+1) := by
    have hm : (∑ x∈range b,v N x*P x y)= mean N (fun t => laws P (t+1) y) := by
      change _=mean N (fun t => push P (laws P t) y)
      simp_rw [trunc,mean_sum,mean_mul]
      rfl
    rw [hm]
    unfold v mean
    rw [←sub_div,←sum_sub_distrib,sum_range_sub']
  have radius (N : ℕ) : |v N y - ∑ x∈range b,v N x*P x y| ≤ 1/((N:ℝ)+1) := by
    rw [hstep,abs_div,abs_of_pos (by positivity : 0<(N:ℝ)+1)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [abs_le]
    constructor <;> linarith only [laws_nonneg hP 0 y,laws_le_one hP 0 y,laws_nonneg hP (N+1) y,laws_le_one hP (N+1) y]
  have hlim : Tendsto (fun t => |v (φ t) y-∑ x∈range b,v (φ t) x*P x y|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun t => radius (φ t))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have lim2 := ((limx y).sub (tendsto_finsetSum (range b) (fun x _ => (limx x).mul_const (P x y)))).abs
  have zero := tendsto_nhds_unique lim2 hlim
  have eq : π y=∑ x∈range b,π x*P x y := sub_eq_zero.mp (abs_eq_zero.mp zero)
  rw [eq]
  exact hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hb x (by simpa using hx),mul_zero])

end MatrixWidth
