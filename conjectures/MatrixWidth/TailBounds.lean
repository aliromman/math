module

public import conjectures.MatrixWidth.Recurrence
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace MatrixWidth
open Finset

/-- Mass at offsets at least m, equivalently at physical widths at least k+m. -/
noncomputable def tail (π : ℕ→ℝ) (m : ℕ) : ℝ := ∑' x,if m≤x then π x else 0

private theorem tail_sum {P π} (hπ : Stationary P π) (m : ℕ) :
    Summable (fun x => if m≤x then π x else 0) := by
  apply Summable.of_nonneg_of_le _ _ hπ.2.1.summable
  · intro x
    split <;> simp [hπ.1 x]
  · intro x
    split <;> simp [hπ.1 x]

theorem tail_term {P π} (hπ : Stationary P π) {m y : ℕ} (hy : m≤y) : π y≤tail π m := by
  have h := (tail_sum hπ m).le_tsum y (fun i _ => by split <;> simp [hπ.1 i])
  simpa [hy,tail] using h

theorem tail_upper {k d : ℕ} (hd : 2≤d) (hk : d<k) {β : ℝ}
    (hb : 1<β) (hc : β*((k:ℝ)-d)<(d:ℝ)*((k:ℝ)-1))
    {π : ℕ→ℝ} (hπ : Stationary (transition k d) π) :
    ∃ C : ℝ, 0<C ∧ ∀m, tail π m * weight β m ≤ C := by
  let C := ∑' i,π i * weight β i
  have hs := factorial_moment hd hk hb hc hπ
  have hn (i : ℕ) := mul_nonneg (hπ.1 i) (weight_pos β i).le
  have pos : 0<C := (mul_pos (stationary_positive hd hk hπ 0) (weight_pos β 0)).trans_le
    (hs.le_tsum 0 (fun i _ => hn i))
  refine ⟨C,pos,fun m => ?_⟩
  rw [tail,←tsum_mul_right]
  apply ((tail_sum hπ m).mul_right _).tsum_le_tsum _ hs
  intro i
  by_cases hi : m ≤ i
  · simpa [hi] using mul_le_mul_of_nonneg_left (weight_mono (by linarith : 0≤β) hi) (hπ.1 i)
  · simp [hi,hn i]

private theorem leap {k d : ℕ} (hk : 0<k) (hd : d≤k) {π : ℕ→ℝ}
    (hπ : Stationary (transition k d) π) (x : ℕ) :
    π x ≤ π (x+(k-d)) * ((k+x:ℕ):ℝ)^(d*(k-1)) := by
  have hu : d≤k+x := by omega
  let B : ℝ := (k+x).choose d
  have bp : 0<B := by dsimp [B]; exact_mod_cast Nat.choose_pos hu
  have ps : transition k d x (x+(k-d))=1/B^(k-1) := by
    rw [show x+(k-d)=k+x-d by omega,maximal_jump hk hu]
    change B / B^k=_
    nth_rw 1 [show k=k-1+1 by omega]
    rw [pow_succ]
    field_simp
  have q := stationary_step (transition_kernel k d) hπ x (x+(k-d))
  rw [ps,mul_one_div,div_le_iff₀ (pow_pos bp _)] at q
  apply q.trans
  apply mul_le_mul_of_nonneg_left _ (hπ.1 _)
  rw [pow_mul]
  apply pow_le_pow_left₀ bp.le
  dsimp [B]
  exact_mod_cast Nat.choose_le_pow (k+x) d

private theorem path {k d : ℕ} (hk : 0<k) (hd : d≤k) {π : ℕ→ℝ}
    (hπ : Stationary (transition k d) π) (t U : ℕ) (h : k+t*(k-d)≤U) :
    π 0 ≤ π (t*(k-d))*(U:ℝ)^(d*(k-1)*t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hU : k+t*(k-d)≤U := by rw [Nat.succ_mul] at h; omega
    have le := leap hk hd hπ (t*(k-d))
    have le' := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (show ((k+t*(k-d):ℕ):ℝ)≤U by exact_mod_cast hU) (d*(k-1)))
      (hπ.1 (t*(k-d)+(k-d))))
    rw [Nat.succ_mul,show d*(k-1)*(t+1)=d*(k-1)+d*(k-1)*t by ring,pow_add,←mul_assoc]
    exact (ih hU).trans (mul_le_mul_of_nonneg_right (le.trans le') (by positivity))

/-- Coincident draws along a path yield a finite lower bound at every cutoff. -/
theorem tail_lower {k d : ℕ} (hd : 2≤d) (hk : d<k) {π : ℕ→ℝ}
    (hπ : Stationary (transition k d) π) (m : ℕ) :
    π 0 ≤ tail π m * ((k+(k-d)+m:ℕ):ℝ)^(d*(k-1)*(m/(k-d)+1)) := by
  let h := k-d
  have hp : 0<h := by dsimp [h]; omega
  have rem := Nat.mod_lt m hp
  have H := Nat.div_add_mod' m h
  have lo : m≤(m/h+1)*h := by rw [Nat.add_mul]; omega
  have hi : k+(m/h+1)*h≤k+h+m := by rw [Nat.add_mul]; omega
  have p := path (by omega : 0<k) hk.le hπ (m/h+1) (k+h+m) hi
  exact p.trans (mul_le_mul_of_nonneg_right (tail_term hπ lo) (by positivity))

end MatrixWidth
