module

public import conjectures.MatrixWidth.Statement
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
namespace MatrixWidth
open Finset

def Kernel (P : ℕ→ℕ→ℝ) : Prop :=
  (∀ x y,0≤P x y) ∧ (∀ x,HasSum (P x) 1)

noncomputable def expect (P : ℕ→ℕ→ℝ) (x : ℕ) (f : ℕ→ℝ) : ℝ := ∑' y,P x y*f y

private theorem weighted {a : ℕ→ℝ} {s C : ℝ} (ha : ∀i,0≤a i) (hs : HasSum a s)
    {f : ℕ→ℝ} (hf : ∀ i,0≤f i) (hc : ∀ i,f i≤C) :
    Summable (fun i => a i*f i) ∧ (∑' i,a i*f i)≤s*C := by
  have hpos := fun i => mul_nonneg (ha i) (hf i)
  have less := fun i => mul_le_mul_of_nonneg_left (hc i) (ha i)
  have rhs := hs.mul_right C
  have h := Summable.of_nonneg_of_le hpos less rhs.summable
  exact ⟨h, (h.tsum_le_tsum less rhs.summable).trans_eq rhs.tsum_eq⟩

theorem expect_bounds {P} (hP : Kernel P) {f : ℕ→ℝ} {C : ℝ} (hf : ∀ i,0≤f i)
    (hc : ∀ i,f i≤C) (x : ℕ) : 0≤expect P x f ∧ expect P x f≤C :=
  ⟨tsum_nonneg fun y => mul_nonneg (hP.1 x y) (hf y),
    (weighted (hP.1 x) (hP.2 x) hf hc).2.trans_eq (one_mul _)⟩

theorem balance {P π} (hP : Kernel P) (hπ : Stationary P π) {f : ℕ→ℝ} {C : ℝ}
    (hf : ∀ i,0≤f i) (hc : ∀ i,f i≤C) :
    (∑' x,π x*expect P x f) = ∑' y,π y*f y := by
  let a := fun x y => π x * (P x y*f y)
  have arow (x : ℕ) : ∑' y,a x y=π x*expect P x f := tsum_mul_left
  have acol (y : ℕ) : ∑' x,a x y=π y*f y := by
    simpa only [a,←mul_assoc] using ((hπ.2.2 y).mul_right (f y)).tsum_eq
  have hb := expect_bounds hP hf hc
  have hs : Summable (Function.uncurry a) := by
    apply (summable_prod_of_nonneg (fun z => mul_nonneg (hπ.1 z.1) (mul_nonneg (hP.1 ..) (hf z.2)))).mpr
    constructor
    · exact fun x => ((weighted (hP.1 x) (hP.2 x) hf hc).1).mul_left (π x)
    · change Summable (fun x => ∑' y,a x y)
      simp_rw [arow]
      exact (weighted hπ.1 hπ.2.1 (fun x => (hb x).1) (fun x => (hb x).2)).1
  simpa only [arow,acol] using hs.tsum_comm.symm

theorem stationary_step {P π} (hP : Kernel P) (hπ : Stationary P π) (x y : ℕ) :
    π x * P x y ≤ π y := by
  rw [←(hπ.2.2 y).tsum_eq]
  exact (hπ.2.2 y).summable.le_tsum x fun i _ => mul_nonneg (hπ.1 i) (hP.1 i y)

theorem avoid_bounds {P} (hP : Kernel P) (a t x : ℕ) :
    0≤avoid P a t x ∧ avoid P a t x≤1 := by
  induction t generalizing x with
  | zero => simp [avoid]
  | succ t ih =>
    have pos (i : ℕ) : 0≤(if i=a then 0 else avoid P a t i) := by split <;> simp_all
    have bnd (i : ℕ) : (if i=a then 0 else avoid P a t i)≤1 := by split <;> simp_all
    simpa [avoid,expect,mul_ite] using expect_bounds hP pos bnd x

theorem recurrent_of_stationary {P π} (hP : Kernel P) (hπ : Stationary P π)
    (hp : ∀i,0<π i) : PositiveRecurrent P := by
  intro a
  let S (t : ℕ) := ∑' x,π x*avoid P a t x
  have S0 : S 0=1 := by simpa [S,avoid] using hπ.2.1.tsum_eq
  have Spos (t : ℕ) : 0≤S t := tsum_nonneg fun x => mul_nonneg (hπ.1 x) (avoid_bounds hP a t x).1
  have diff (t : ℕ) : π a*avoid P a t a=S t-S (t+1) := by
    let f (i : ℕ) := if i=a then 0 else avoid P a t i
    have fpos (i : ℕ) : 0≤f i := by dsimp [f]; split <;> simp [*,(avoid_bounds hP a t i).1]
    have fbnd (i : ℕ) : f i≤1 := by dsimp [f]; split <;> simp [*,(avoid_bounds hP a t i).2]
    have hb : S (t+1) = ∑' y,π y*f y := by
      simpa [S,f,expect,avoid,mul_ite] using balance hP hπ fpos fbnd
    have sing := hasSum_ite_eq a (π a*avoid P a t a)
    have all := (weighted hπ.1 hπ.2.1 fpos fbnd).1.hasSum.add sing
    have total : HasSum (fun x => π x*avoid P a t x) ((∑' y,π y*f y)+π a*avoid P a t a) := by
      apply all.congr_fun
      intro j
      by_cases h : j=a <;> simp [f,h]
    change _ = (∑' x,π x*avoid P a t x)-_
    linarith only [total.tsum_eq,hb]
  apply summable_of_sum_range_le (c:=1/π a) (fun t => (avoid_bounds hP a t a).1)
  intro n
  rw [le_div_iff₀ (hp a),mul_comm,Finset.mul_sum]
  simp_rw [diff]
  rw [Finset.sum_range_sub',S0]
  linarith only [Spos n]

/-- A stationary law integrates an unbounded drift function by testing its bounded truncations. -/
theorem stationary_moment {P π} (hP : Kernel P) (hπ : Stationary P π) {V : ℕ→ℝ} {D : ℝ}
    (hv : ∀ x,0≤V x) (hD : 0≤D) (rows : ∀x,Summable (fun y => P x y*V y))
    (drift : ∀x,expect P x V≤V x/2+D) :
    Summable (fun x => π x*V x) ∧ (∑' x,π x*V x)≤2*D := by
  have bound (s : Finset ℕ) : (∑ x∈s,π x*V x)≤2*D := by
    let M := ∑ i∈s,V i
    let f := fun x => min (V x) M
    have mpos : 0≤M := sum_nonneg fun i _ => hv i
    have fp (x : ℕ) : 0≤f x := le_min (hv x) mpos
    have fb (x : ℕ) : f x≤M := min_le_right ..
    have eb := expect_bounds hP fp fb
    have cmp (x : ℕ) : expect P x f ≤ expect P x V := by
      exact ((weighted (hP.1 x) (hP.2 x) fp fb).1).tsum_le_tsum
        (fun y => mul_le_mul_of_nonneg_left (min_le_left ..) (hP.1 x y)) (rows x)
    have test := (((weighted hπ.1 hπ.2.1 fp fb).1.hasSum).sub
      (weighted hπ.1 hπ.2.1 (fun x => (eb x).1) (fun x => (eb x).2)).1.hasSum).add (hπ.2.1.mul_right D)
    have val : HasSum (fun x => π x*(f x-expect P x f+D)) D := by
      rw [balance hP hπ fp fb] at test
      simpa only [sub_self,one_mul,zero_add, mul_add,mul_sub] using test
    have strong (x : ℕ) (h : V x≤M) :
        π x*V x/2 ≤ π x*(f x-expect P x f+D) := by
      have hle : V x/2 ≤ f x-expect P x f+D := by
        rw [show f x=V x from min_eq_left h]
        linarith only [drift x,cmp x]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hle (hπ.1 x)
    have pos (x : ℕ) : 0≤π x*(f x-expect P x f+D) := by
      by_cases e : V x≤M
      · exact (div_nonneg (mul_nonneg (hπ.1 x) (hv x)) (by norm_num)).trans (strong x e)
      · apply mul_nonneg (hπ.1 x)
        rw [show f x=M from min_eq_right (le_of_not_ge e)]
        linarith only [(eb x).2,hD]
    have h1 := sum_le_sum (s:=s) (fun x hx => strong x (single_le_sum (fun i _ => hv i) hx))
    have h2 := (val.summable.sum_le_tsum s (fun x _ => pos x)).trans_eq val.tsum_eq
    rw [←sum_div] at h1
    linarith
  have hn (x : ℕ) := mul_nonneg (hπ.1 x) (hv x)
  exact ⟨summable_of_sum_le hn bound, Real.tsum_le_of_sum_le hn bound⟩

end MatrixWidth
