module

public import conjectures.ConsecutiveThreshold.LogConcavity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace ConsecutiveThreshold.Mass
open Finset
open scoped BigOperators

theorem sum_le_total (f : Mass) (S : Finset ℤ) : ∑ i∈S,f.w i≤f.total := by
  calc
    _ ≤ ∑ i∈S∪f.sites,f.w i := sum_le_sum_of_subset_of_nonneg subset_union_left fun i _ _ ↦ f.nonneg i
    _ = f.total := (sum_subset subset_union_right (fun i _ hi ↦ f.zero_off i hi)).symm

theorem interval_product (f g : Mass) (A B S : Finset ℤ) (cover : ∀ i∈A,∀ j∈B,i+j∈S) :
    (∑ i∈A,f.w i)*(∑ j∈B,g.w j) ≤ ∑ t∈S,(f.conv g).w t := by
  have shift (i) (hi : i∈A) : ∑ j∈B,g.w j≤∑ t∈S,g.w (t-i) := by
    let E := B.image (·+i)
    have inc : E⊆S := by
      intro t ht
      obtain ⟨j,hj,rfl⟩ := mem_image.mp ht
      simpa only [add_comm i j] using cover i hi j hj
    have e : ∑ t∈E,g.w (t-i)=∑ j∈B,g.w j := by simp [E,sum_image (fun x _ y _ h ↦ add_right_cancel h)]
    exact e.symm.le.trans (sum_le_sum_of_subset_of_nonneg inc (fun t _ _ ↦ g.nonneg _))
  rw [sum_mul]
  calc
    _ ≤ ∑ i∈A,f.w i*∑ t∈S,g.w (t-i) :=
      sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (shift i hi) (f.nonneg i)
    _ = ∑ t∈S,∑ i∈A,f.w i*g.w (t-i) := by simp_rw [mul_sum]; rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro t _
      have eq := conv_on f g t 0 (A∪f.sites) (fun i hi ↦ by simpa only [add_zero] using (mem_union_right A hi))
      rw [sub_zero] at eq
      rw [eq]
      simpa only [sub_zero] using sum_le_sum_of_subset_of_nonneg
        (f := fun i ↦ f.w i*g.w (t-i)) (s:=A) (t:=A∪f.sites) subset_union_left
        (fun i _ _ ↦ mul_nonneg (f.nonneg i) (g.nonneg _))

private theorem mode_right {f : Mass} {h u v : ℤ} (lc : balanced f.w)
    (peak : ∀ i,f.w i≤f.w h) (pos : 0<f.w h) (hu : h≤u) (uv : u≤v) : f.w v≤f.w u := by
  have e := lc h u (v-u) hu (by omega)
  rw [show u+(v-u)=v by omega] at e
  exact (mul_le_mul_iff_of_pos_left pos).mp (e.trans (mul_le_mul_of_nonneg_right (peak _) (f.nonneg _)))

private theorem mode_left {f : Mass} {h u v : ℤ} (lc : balanced f.w)
    (peak : ∀ i,f.w i≤f.w h) (pos : 0<f.w h) (uv : u≤v) (vh : v≤h) : f.w u≤f.w v := by
  have e := lc u (h-(v-u)) (v-u) (by omega) (by omega)
  rw [sub_add_cancel,show u+(v-u)=v by omega] at e
  exact (mul_le_mul_iff_of_pos_right pos).mp (e.trans (mul_le_mul_of_nonneg_left (peak _) (f.nonneg _)))

private theorem half_edge (f : Mass) {h : ℤ} (lc : balanced f.w) (one : f.total=1)
    (peak : ∀ i,f.w i≤f.w h) (pos : 0<f.w h)
    (L : ℕ) (big : 2≤((L:ℝ)+1)*f.w h) :
    2*f.w (h+L)≤f.w h ∧ 2*f.w (h-L)≤f.w h := by
  have side (t : Finset ℤ) (z : ℤ) (count : t.card=L+1) (small : ∀ i∈t,f.w z≤f.w i) :
      2*f.w z≤f.w h := by
    have e := (sum_le_sum small).trans (sum_le_total f t)
    rw [sum_const,count,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,one] at e
    nlinarith only [e,big,show (0:ℝ)<(L:ℝ)+1 by positivity]
  constructor
  · apply side (Icc h (h+L))
    · rw [Int.card_Icc,show h+(L:ℤ)+1-h=(L:ℤ)+1 by omega]; omega
    · intro i hi
      obtain ⟨lo,top⟩ := mem_Icc.mp hi
      exact mode_right lc peak pos lo top
  · apply side (Icc (h-L) h)
    · rw [Int.card_Icc,show h+1-(h-(L:ℤ))=(L:ℤ)+1 by omega]; omega
    · intro i hi
      obtain ⟨lo,top⟩ := mem_Icc.mp hi
      exact mode_left lc peak pos lo top

/-- A log-concave law places at least half of its mass within a distance of
two reciprocal peak heights from a mode, rounded up to an integer. -/
theorem half_interval (f : Mass) {h : ℤ} (lc : balanced f.w) (one : f.total=1)
    (peak : ∀ i,f.w i≤f.w h) (pos : 0<f.w h)
    (L : ℕ) (big : 2≤((L:ℝ)+1)*f.w h) :
    (1/2:ℝ) ≤ ∑ i∈Icc (h-L) (h+L),f.w i := by
  obtain ⟨right,left⟩ := half_edge f lc one peak pos L big
  let I := Icc (h-L) (h+L)
  let T := f.sites \ I
  let move := fun i : ℤ ↦ if i<h then i+L else i-L
  have outside (i) (hi : i∈T) : i<h-L ∨ h+L<i := by
    have no := (mem_sdiff.mp hi).2
    change i∉Icc (h-L) (h+L) at no
    simp only [mem_Icc,not_and_or,not_le] at no
    omega
  have step (i) (hi : i∈T) : 2*f.w i≤f.w (move i) := by
    rcases outside i hi with below|above
    · rw [show move i=i+L by simp [move,show i<h by omega]]
      have e := lc i (h-L) L (by omega) (by omega)
      rw [sub_add_cancel] at e
      apply (mul_le_mul_iff_of_pos_right pos).mp
      nlinarith only [e,mul_le_mul_of_nonneg_left left (f.nonneg (i+L))]
    · rw [show move i=i-L by simp [move,show ¬i<h by omega]]
      have e := lc h (i-L) L (by omega) (by omega)
      rw [sub_add_cancel] at e
      apply (mul_le_mul_iff_of_pos_left pos).mp
      nlinarith only [e,mul_le_mul_of_nonneg_right right (f.nonneg (i-L))]
  have inj : Set.InjOn move T := by
    intro i hi j hj e
    have oi := outside i hi
    have oj := outside j hj
    dsimp [move] at e
    split at e <;> split at e <;> omega
  have tail : 2*(∑ i∈T,f.w i)≤1 := by
    rw [mul_sum]
    calc
      _ ≤ ∑ i∈T,f.w (move i) := sum_le_sum step
      _ = ∑ j∈T.image move,f.w j := (sum_image inj).symm
      _ ≤ 1 := one ▸ sum_le_total f _
  have split := sum_sdiff (s₁:=f.sites∩I) (s₂:=f.sites) inter_subset_left (f:=f.w)
  have diff : f.sites \ (f.sites∩I)=T := by ext z; simp [T]
  rw [diff] at split
  change _ = f.total at split
  have inside := sum_le_sum_of_subset_of_nonneg (f:=f.w) (s:=f.sites∩I) (t:=I) inter_subset_right
    (fun i _ _ ↦ f.nonneg i)
  change (1/2:ℝ)≤∑ i∈I,f.w i
  linarith

theorem exists_peak (f : Mass) (one : f.total=1) :
    ∃ h : ℤ,0<f.w h ∧ ∀ i,f.w i≤f.w h := by
  have has : f.sites.Nonempty := by
    by_contra! no
    simp [total,no] at one
  obtain ⟨h,hS,peak⟩ := f.sites.exists_max_image f.w has
  have pos : 0<f.w h := by
    by_contra! no
    have E := sum_nonpos (s:=f.sites) (fun i hi ↦ (peak i hi).trans no)
    change f.total≤0 at E
    linarith
  exact ⟨h,pos,fun i ↦ by by_cases hi : i∈f.sites; exact peak i hi; rw [f.zero_off i hi]; exact pos.le⟩

/-- Adding an independent log-concave law whose peak is at least as high
decreases the peak of a log-concave law by a factor of at most 52. -/
theorem peak_comparison (f g : Mass) (lf : balanced f.w) (lg : balanced g.w)
    (uf : f.total=1) (ug : g.total=1) (a b m : ℤ)
    (fa : ∀ i,f.w i≤f.w a) (gb : ∀ i,g.w i≤g.w b) (gm : 0<g.w b)
    (order : g.w b≤f.w a) (mode : ∀ i,(conv f g).w i≤(conv f g).w m) :
    g.w b≤52*(conv f g).w m := by
  let P := g.w b
  let L := ⌈2/P⌉₊
  have p1 : P≤1 := by simpa [ug,P] using sum_le_total g {b}
  have pp : 0<P := gm
  have half := (div_le_iff₀ pp).mp (Nat.le_ceil (2/P))
  have big : 2≤((L:ℝ)+1)*P := by dsimp [L]; linarith
  have top := Nat.ceil_lt_add_one (a:=2/P) (by positivity)
  have capL : (L:ℝ)*P ≤ 2+P := by
    have e := mul_le_mul_of_nonneg_right top.le pp.le
    rw [add_mul,div_mul_cancel₀ _ pp.ne',one_mul] at e
    exact e
  let A := Icc (a-L) (a+L)
  let B := Icc (b-L) (b+L)
  let S := Icc (a+b-2*L) (a+b+2*L)
  have hf : (1/2:ℝ) ≤ ∑ i∈A,f.w i :=
    half_interval f lf uf fa (gm.trans_le order) L (big.trans (mul_le_mul_of_nonneg_left order (by positivity)))
  have hg : (1/2:ℝ) ≤ ∑ i∈B,g.w i := half_interval g lg ug gb gm L big
  have both := interval_product f g A B S (by
    intro i hi j hj
    obtain ⟨li,ui⟩ := mem_Icc.mp hi
    obtain ⟨lj,uj⟩ := mem_Icc.mp hj
    apply mem_Icc.mpr
    constructor <;> omega)
  have table : (1/4:ℝ) ≤ ∑ i∈S,(conv f g).w i := by
    exact (by norm_num : (1/4:ℝ)=(1/2)*(1/2)).le.trans
      ((mul_le_mul hf hg (by norm_num) (by linarith only [hf])).trans both)
  have box : S.card=4*L+1 := by
    dsimp only [S]
    rw [Int.card_Icc]
    omega
  have bound := table.trans (sum_le_sum (s:=S) (fun i _ ↦ mode i))
  rw [sum_const,box,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at bound
  have count : (4*(L:ℝ)+1)*P ≤ 13 := by linarith
  have a1 := mul_le_mul_of_nonneg_right bound pp.le
  have a2 := mul_le_mul_of_nonneg_right count ((conv f g).nonneg m)
  change P ≤ _
  nlinarith only [a1,a2]

end ConsecutiveThreshold.Mass
