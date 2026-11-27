module

public import conjectures.MatrixWidth.Balance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace MatrixWidth
open Finset

noncomputable def push (P : ℕ→ℕ→ℝ) (μ : ℕ→ℝ) (y : ℕ) : ℝ := ∑' x,μ x*P x y

private theorem transport {P : ℕ→ℕ→ℝ} {μ f : ℕ→ℝ} (hp : ∀x y,0≤P x y)
    (hm : ∀x,0≤μ x) (hf : ∀y,0≤f y) (rows : ∀x,Summable (fun y => P x y*f y))
    (total : Summable (fun x => μ x*expect P x f)) :
    HasSum (fun y => push P μ y*f y) (∑' x,μ x*expect P x f) := by
  let a := fun x y => μ x*(P x y*f y)
  have ar (x : ℕ) : (∑' y,a x y)=μ x*expect P x f := tsum_mul_left
  have ac (y : ℕ) : (∑' x,a x y)=push P μ y*f y := by simp only [a,←mul_assoc,tsum_mul_right,push]
  have h : Summable (Function.uncurry a) := by
    apply (summable_prod_of_nonneg (fun z => mul_nonneg (hm z.1) (mul_nonneg (hp ..) (hf z.2)))).mpr
    refine ⟨fun x => (rows x).mul_left (μ x),?_⟩
    change Summable (fun x => ∑' y,a x y)
    simpa only [ar] using total
  have h' := h.prod_symm
  have hnn : 0≤(fun z : ℕ×ℕ => a z.2 z.1) := fun z => mul_nonneg (hm z.2) (mul_nonneg (hp ..) (hf z.1))
  have : Summable (fun y => ∑' x,a x y) := ((summable_prod_of_nonneg hnn).mp h').2
  have equ := h.tsum_comm
  simp only [ar,ac] at this equ
  exact equ ▸ this.hasSum

noncomputable def laws (P : ℕ→ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0 => fun x => if x=0 then 1 else 0
  | t+1 => push P (laws P t)

theorem laws_nonneg {P} (hP : Kernel P) (t x : ℕ) : 0≤laws P t x := by
  induction t generalizing x with
  | zero => dsimp [laws]; split <;> norm_num
  | succ t ih => exact tsum_nonneg fun i => mul_nonneg (ih i) (hP.1 i x)

theorem laws_total {P} (hP : Kernel P) (t : ℕ) : HasSum (laws P t) 1 := by
  induction t with
  | zero => exact hasSum_ite_eq 0 1
  | succ t ih =>
    have he (x : ℕ) : expect P x (fun _ => 1)=1 := by simpa [expect] using (hP.2 x).tsum_eq
    have h := transport (f:=fun _ => 1) hP.1 (laws_nonneg hP t) (fun _ => zero_le_one)
      (fun x => by simpa using (hP.2 x).summable) (by simpa only [he,mul_one] using ih.summable)
    simpa only [laws,he,mul_one,ih.tsum_eq] using h

theorem laws_le_one {P} (hP : Kernel P) (t x : ℕ) : laws P t x≤1 := by
  rw [←(laws_total hP t).tsum_eq]
  exact (laws_total hP t).summable.le_tsum x (fun j _ => laws_nonneg hP t j)

theorem laws_moment {P} (hP : Kernel P) {V : ℕ→ℝ} {D : ℝ} (hv : ∀ x,0≤V x)
    (hf : ∀ x,Summable (fun y => P x y*V y)) (hd : ∀x,expect P x V≤V x/2+D) :
    ∃ C, ∀ t, Summable (fun x => laws P t x*V x) ∧ (∑' x,laws P t x*V x)≤C := by
  let C := max (V 0) (2*D)
  refine ⟨C,?_⟩
  intro t
  induction t with
  | zero =>
    have h : HasSum (fun x => laws P 0 x*V x) (V 0) := by
      apply (hasSum_ite_eq 0 (V 0)).congr_fun
      intro x
      by_cases e : x=0 <;> simp [e,laws]
    exact ⟨h.summable,h.tsum_eq.trans_le (le_max_left ..)⟩
  | succ t ih =>
    let μ := laws P t
    have hp (x : ℕ) : 0≤μ x := laws_nonneg hP t x
    have ep (x : ℕ) : 0≤expect P x V := tsum_nonneg fun y => mul_nonneg (hP.1 ..) (hv y)
    have bound (x : ℕ) : μ x*expect P x V ≤ (μ x*V x)/2 + μ x*D := by
      calc
        _ ≤ μ x*(V x/2+D) := mul_le_mul_of_nonneg_left (hd x) (hp x)
        _ = _ := by ring
    have major := (ih.1.hasSum.div_const 2).add ((laws_total hP t).mul_right D)
    have hs := Summable.of_nonneg_of_le (fun x => mul_nonneg (hp x) (ep x)) bound major.summable
    have m := transport hP.1 hp hv hf hs
    refine ⟨m.summable,m.tsum_eq.trans_le ?_⟩
    have sub := (hs.tsum_le_tsum bound major.summable).trans_eq major.tsum_eq
    linarith only [sub,ih.2,le_max_right (V 0) (2*D)]

end MatrixWidth
