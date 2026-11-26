module

public import conjectures.AldousFillAdjacent.Operator
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Topology

variable {m : ℕ}

private theorem translated (t : ℕ) (a x y : Deck m) :
    stopped m t (a*y) (a*x) = stopped m t y x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp [stopped,mul_assoc,ih]

theorem mean_fixed (m t : ℕ) : mean m t = 𝔼 x, stopped m t 1 x := by
  have row (y : Deck m) : (𝔼 x, stopped m t y x) = 𝔼 x, stopped m t 1 x := by
    symm
    apply Fintype.expect_equiv (Equiv.mulLeft y)
    intro x
    simpa using (translated t y x 1).symm
  simp [mean,row]

private theorem stopped_self (t : ℕ) (y : Deck m) : stopped m t y y=0 := by
  cases t <;> simp [stopped]

private theorem stopped_nonneg (t : ℕ) (y x : Deck m) : 0≤stopped m t y x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [stopped]
    split
    · rfl
    · exact add_nonneg zero_le_one (expect_nonneg fun _ _ ↦ ih _)

theorem stopped_mono (y x : Deck m) : Monotone (fun t ↦ stopped m t y x) := by
  apply monotone_nat_of_le_succ
  intro t
  induction t generalizing x with
  | zero => exact stopped_nonneg 1 y x
  | succ t ih =>
    change (if x=y then 0 else 1+(𝔼 i, stopped m t y (x*move i))) ≤
      (if x=y then 0 else 1+(𝔼 i, stopped m (t+1) y (x*move i)))
    split
    · rfl
    · exact add_le_add_right (expect_le_expect fun _ _ ↦ ih _) _

private theorem tendsto_avg {V : Type*} [Fintype V] {u : ℕ → V → ℝ} {a : V → ℝ}
    (h : ∀ x, Tendsto (fun t ↦ u t x) atTop (𝓝 (a x))) :
    Tendsto (fun t ↦ 𝔼 x, u t x) atTop (𝓝 (𝔼 x, a x)) := by
  simp only [Fintype.expect_eq_sum_div_card]
  exact (tendsto_finsetSum univ (fun x _ ↦ h x)).div_const _

/-- A finite limit of the stopped means gives the first-step hitting equations. -/
theorem first_step {τ : ℝ} (ht : Tendsto (mean m) atTop (𝓝 τ)) :
    ∃ h : Deck m → ℝ, h 1=0 ∧ (∀ x≠1, h x=1+P m h x) ∧ (𝔼 x, h x)=τ := by
  have mon : Monotone (mean m) := fun a b hab ↦ by
    rw [mean_fixed,mean_fixed]
    exact expect_le_expect fun x _ ↦ stopped_mono 1 x hab
  have lim (x : Deck m) : BddAbove (Set.range fun t ↦ stopped m t 1 x) := by
    use (Fintype.card (Deck m):ℝ)*τ
    rintro _ ⟨t,rfl⟩
    have h := single_le_sum (fun y _ ↦ stopped_nonneg t 1 y) (mem_univ x)
    apply h.trans
    rw [← Fintype.card_mul_expect,←mean_fixed]
    exact mul_le_mul_of_nonneg_left (mon.ge_of_tendsto ht t) (by positivity)
  let h (x : Deck m) := ⨆ t, stopped m t 1 x
  have conv (x : Deck m) : Tendsto (fun t ↦ stopped m t 1 x) atTop (𝓝 (h x)) :=
    tendsto_atTop_ciSup (stopped_mono _ _) (lim x)
  refine ⟨h,?_,?_,?_⟩
  · simp [h,stopped_self]
  · intro x hx
    have cs := (conv x).comp (tendsto_add_atTop_nat 1)
    have cp := tendsto_avg (fun i : Option (Fin m) ↦ conv (x*move i))
    exact tendsto_nhds_unique cs (by simpa [Function.comp_def,stopped,hx,P_apply]
      using (tendsto_const_nhds (x:=(1:ℝ))).add cp)
  · apply tendsto_nhds_unique (tendsto_avg conv)
    exact ht.congr (fun t ↦ mean_fixed m t)

end AldousFillAdjacent
