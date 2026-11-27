module

public import conjectures.PenneyBias.Statement
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

public section
namespace PenneyBias
open Filter Finset
open scoped Topology

theorem mem_words {v : Word} {n : ℕ} : v∈words n ↔ v.length≤n := by
  induction n generalizing v with
  | zero => simp [words]
  | succ n ih =>
    cases v with
    | nil => simp [words]
    | cons b v =>
      cases b <;> simp [words,ih]

theorem bounded (v w : Word) {p : ℝ} (hp : p∈Set.Icc 0 1) (n : ℕ) (h : Word) :
    0≤byTime v w p n h ∧ byTime v w p n h≤1 := by
  induction n generalizing h with
  | zero => simp only [byTime]; split <;> constructor <;> norm_num
  | succ n ih =>
    cases e : terminal v w h with
    | some b => cases b <;> simp [byTime,e]
    | none =>
      rw [byTime,e]
      have u := ih (false::h)
      have t := ih (true::h)
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) u.1) (mul_nonneg hp.1 t.1)
      · linarith only [mul_le_mul_of_nonneg_left u.2 (sub_nonneg.mpr hp.2),
          mul_le_mul_of_nonneg_left t.2 hp.1]

private theorem increasing (v w : Word) {p : ℝ} (hp : p∈Set.Icc 0 1) (n : ℕ) (h : Word) :
    byTime v w p n h≤byTime v w p (n+1) h := by
  induction n generalizing h with
  | zero =>
    cases e : terminal v w h with
    | some b => cases b <;> simp [byTime,e]
    | none => simpa only [byTime,e,reduceCtorEq,ite_false] using (bounded v w hp 1 h).1
  | succ n ih =>
    cases e : terminal v w h with
    | some b => cases b <;> simp [byTime,e]
    | none =>
      simp only [byTime,e]
      exact add_le_add (mul_le_mul_of_nonneg_left (ih _) (sub_nonneg.mpr hp.2))
        (mul_le_mul_of_nonneg_left (ih _) hp.1)

theorem horizon_tendsto (v w : Word) {p : ℝ} (hp : p∈Set.Icc 0 1) (h : Word) :
    Tendsto (fun n ↦ byTime v w p n h) atTop (𝓝 (⨆ n, byTime v w p n h)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun n ↦ increasing v w hp n h))
    ⟨1,by rintro _ ⟨n,rfl⟩; exact (bounded v w hp n h).2⟩

private theorem horizon_continuous (v w : Word) (n : ℕ) (h : Word) :
    Continuous (fun p ↦ byTime v w p n h) := by
  induction n generalizing h with
  | zero => exact continuous_const
  | succ n ih =>
    cases e : terminal v w h with
    | some b => cases b <;> simp only [byTime,e] <;> exact continuous_const
    | none =>
      simp only [byTime,e]
      exact ((continuous_const.sub continuous_id).mul (ih _)).add (continuous_id.mul (ih _))

/-- Strictly favorable pairs remain favorable under small changes of the bias. -/
theorem favorable_near (v w : Word) {p : ℝ} (hp : p∈Set.Ioo 0 1)
    (h : 1/2 < win v w p) : ∀ᶠ q in 𝓝 p, 1/2 < win v w q := by
  obtain ⟨n,hn⟩ := exists_lt_of_lt_ciSup h
  have openTest := (horizon_continuous v w n []).continuousAt.eventually
    (Ioi_mem_nhds hn)
  filter_upwards [openTest, isOpen_Ioo.mem_nhds hp] with q hq hqp
  exact lt_of_lt_of_le hq (le_ciSup
    (show BddAbove (Set.range (fun t ↦ byTime v w q t [])) from
      ⟨1,by rintro _ ⟨t,rfl⟩; exact (bounded v w ⟨hqp.1.le,hqp.2.le⟩ t []).2⟩) n)

end PenneyBias
