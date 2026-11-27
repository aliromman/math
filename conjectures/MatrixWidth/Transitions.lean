module

public import conjectures.MatrixWidth.Kernel
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity

@[expose] public section
namespace MatrixWidth
open Finset

theorem row_hasSum (k d x : ℕ) : HasSum (transition k d x) 1 := by
  rw [← row_sum k d x]
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  by_contra hn
  have h := (transition_support (lt_of_le_of_ne (transition_nonneg k d x y) (Ne.symm hn))).1
  exact hy (mem_range.mpr (by omega))

theorem transition_le_one (k d x y : ℕ) : transition k d x y ≤ 1 := by
  rw [←(row_hasSum k d x).tsum_eq]
  exact (row_hasSum k d x).summable.le_tsum y (fun i _ => transition_nonneg k d x i)

noncomputable def unionProb (k d x r : ℕ) : ℝ :=
  (Fintype.card (Fiber k d x r):ℝ) / Fintype.card (Outcome k d x)

theorem transition_union {k d x r : ℕ} (hr : r ≤ k+x) :
    transition k d x (k+x-r)=unionProb k d x r := by
  have hf : (univ.filter (fun f : Outcome k d x => next f=k+x-r)) =
      univ.filter (fun f : Outcome k d x => (covered f).card=r) := by
    ext f
    have hb := (covered_bounds f).1
    constructor
    · intro h
      have hv := (mem_filter.mp h).2
      change k+x-(covered f).card=k+x-r at hv
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    · intro h
      exact mem_filter.mpr ⟨mem_univ _,by simp only [next,(mem_filter.mp h).2]⟩
  simp only [transition,unionProb,Fiber,Fintype.card_subtype,hf]

theorem bounded_support {k d x y : ℕ} (h : 0<transition k d x y) :
    y ≤ x+(k+k*d) ∧ x≤y+(k+k*d) := by
  have := transition_support h
  omega

theorem neighbour_up {k d : ℕ} (hd : 0<d) (hk : d<k) (x : ℕ) :
    0<transition k d x (x+1) := by
  have hb : k≤k*d := by simpa using Nat.mul_le_mul_left k hd
  rw [show x+1=k+x-(k-1) by omega]
  exact transition_of_union hd (by omega) (by omega) (by omega)

theorem neighbour_down {k d : ℕ} (hd : 2≤d) (hk : d≤k) (x : ℕ) :
    0<transition k d (x+1) x := by
  have hb : 2*k≤k*d := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hd
  nth_rw 2 [show x=k+(x+1)-(k+1) by omega]
  exact transition_of_union (by omega) (by omega) (by omega) (by omega)

private theorem constant_covered {k d x : ℕ} (hk : 0<k) (s : Draw k d x) :
    covered (fun _ : Fin k => s) = s.val := by
  have : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  ext z
  simp [covered]

theorem max_fiber {k d x : ℕ} (hk : 0<k) (hd : d≤k+x) :
    Fintype.card (Fiber k d x d) = (k+x).choose d := by
  let b : Fiber k d x d ≃ Draw k d x :=
    { toFun := fun f => f.val ⟨0,hk⟩
      invFun := fun s => ⟨fun _ => s, by rw [constant_covered hk, s.property, Nat.min_eq_left hd]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        apply Subtype.ext
        have eqU (j : Fin k) : (f.val j).val=covered f.val :=
          eq_of_subset_of_card_le (component_subset f.val j) (by rw [f.property,(f.val j).property,Nat.min_eq_left hd])
        exact (eqU _).trans (eqU _).symm
      right_inv := fun _ => rfl }
  simpa [Draw,Nat.min_eq_left hd] using Fintype.card_congr b

theorem maximal_jump {k d x : ℕ} (hk : 0<k) (hd : d≤k+x) :
    transition k d x (k+x-d) = ((k+x).choose d : ℝ) / ((k+x).choose d : ℝ)^k := by
  rw [transition_union hd, unionProb,max_fiber hk hd,card_outcome,Nat.min_eq_left hd,Nat.cast_pow]

theorem unionProb_nonneg (k d x r : ℕ) : 0≤unionProb k d x r := by unfold unionProb; positivity

theorem unionProb_zero {k d x r : ℕ} (hk : 0<k) (h : r<min d (k+x)) :
    unionProb k d x r=0 := by
  have : IsEmpty (Fiber k d x r) := ⟨fun f => by
    have h' := covered_ge hk f.val
    rw [f.property] at h'
    omega⟩
  simp [unionProb]

theorem expected_unions (F : ℕ→ℝ) (k d x : ℕ) :
    ∑ y ∈ range (x+k+1), transition k d x y*F y =
    ∑ r ∈ range (k*d+1), unionProb k d x r * F (k+x-r) := by
  let T := Outcome k d x
  let denominator : ℝ := Fintype.card T
  have disint (g : T → ℕ) (b : ℕ) (hg : ∀ f, g f<b) (v : ℕ → ℝ) :
      (∑ i ∈ range b, ((univ.filter (fun f => g f=i)).card:ℝ)/denominator * v i) =
        (∑ f : T, v (g f))/denominator := by
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    rw [← sum_fiberwise_of_maps_to (t:=range b) (g:=g) (s:=univ) (fun f _ => mem_range.mpr (hg f)) (f:=fun f => v (g f))]
    apply sum_congr rfl
    intro i _
    calc
      _ = ∑ _f ∈ univ.filter (fun f => g f=i),v i := by simp
      _ = _ := sum_congr rfl (fun f hf => by rw [(mem_filter.mp hf).2])
  have L := disint next (x+k+1) (by intro f; unfold next; omega) F
  have R := disint (fun f => (covered f).card) (k*d+1)
    (fun f => Nat.lt_succ_of_le (covered_bounds f).2) (fun r => F (k+x-r))
  simpa only [transition,unionProb,Fiber,Fintype.card_subtype] using L.trans R.symm

end MatrixWidth
