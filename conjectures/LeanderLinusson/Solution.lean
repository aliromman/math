module

public import conjectures.LeanderLinusson.Witness
public import conjectures.LeanderLinusson.Limits
import Mathlib.Tactic.Ring

@[expose] public section
namespace LeanderLinusson
open Finset Filter Function
open scoped Topology

private def pairOf (i : Fin 2) : Fin 1 × Bool ↪ Fin 2 × Bool :=
  (⟨fun _ ↦ i,fun _ _ _ ↦ Subsingleton.elim ..⟩ : Fin 1 ↪ Fin 2).prodMap (Embedding.refl Bool)

private theorem first_sample {n : ℕ} (m : ℕ) (b : Fin 2 × Bool ↪ Fin n) (i : Fin 2) :
    pathSamples m ((pairOf i).trans b) =
      (samples (Fin n) m).filter (fun g ↦ PathEvent g (b (i,false)) (b (i,true))) := by
  classical
  ext g
  simp [pathSamples,pairOf,Fin.forall_fin_succ]
  exact fun _ ↦ Iff.rfl

private theorem both_sample {n : ℕ} (m : ℕ) (b : Fin 2 × Bool ↪ Fin n) :
    pathSamples m b = (samples (Fin n) m).filter (fun g ↦
      PathEvent g (b (0,false)) (b (0,true)) ∧ PathEvent g (b (1,false)) (b (1,true))) := by
  classical
  ext g
  simp [pathSamples,Fin.forall_fin_succ]

/-- With a fixed positive edge count, any two connections on disjoint named
vertex pairs have negative covariance to leading order. -/
theorem sparse_covariance {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (m : ℕ)
    (b : ∀ n, Fin 2 × Bool ↪ Fin (N n)) :
    Tendsto (fun n ↦ (N n:ℝ)^4 * covariance (Fin (N n)) m
      (b n (0,false)) (b n (0,true)) (b n (1,false)) (b n (1,true)))
      atTop (𝓝 (-(m:ℝ))) := by
  have single (i : Fin 2) : Tendsto (fun n ↦ (N n:ℝ)^2 * probability (Fin (N n)) m
        (fun g ↦ PathEvent g (b n (i,false)) (b n (i,true)))) atTop (𝓝 (m:ℝ)) := by
    simpa [first_sample,probability] using disjoint_paths_limit hN m (fun n ↦ (pairOf i).trans (b n))
  have both := disjoint_paths_limit hN m b
  simp only [both_sample] at both
  have h := both.sub ((single 0).mul (single 1))
  have lim : (m.descFactorial 2:ℝ) - (m:ℝ)*m = -(m:ℝ) := by
    cases m <;> simp [Nat.descFactorial_succ]
    ring
  rw [lim] at h
  apply h.congr
  intro n
  dsimp [covariance,probability]
  ring

theorem eventually_negative {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {m : ℕ} (hm : 0<m)
    (b : ∀ n, Fin 2 × Bool ↪ Fin (N n)) : ∀ᶠ n in atTop,
    covariance (Fin (N n)) m (b n (0,false)) (b n (0,true)) (b n (1,false)) (b n (1,true)) < 0 := by
  have hn : -(m:ℝ) < 0 := neg_neg_of_pos (Nat.cast_pos.mpr hm)
  filter_upwards [(sparse_covariance hN m b).eventually_lt_const hn] with n h
  by_contra! hc
  exact (not_lt_of_ge (mul_nonneg (pow_nonneg (Nat.cast_nonneg (N n)) _) hc)) h

/-- info: 'LeanderLinusson.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'LeanderLinusson.sparse_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse_covariance

end LeanderLinusson
