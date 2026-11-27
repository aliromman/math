module

public import conjectures.ConsecutiveThreshold.Conditional
public import conjectures.ConsecutiveThreshold.Asymptotic
public import conjectures.ConsecutiveThreshold.Complement

public section
namespace ConsecutiveThreshold
open Equiv Finset Filter
open scoped BigOperators Topology Classical

/-- Fixed consecutive patterns appear with high probability between their two thresholds. -/
theorem conjecture21 : Conjecture := by
  intro k π m valid lower upper
  cases k with
  | zero =>
    apply tendsto_congr' _ |>.mpr tendsto_const_nhds
    filter_upwards [valid] with n hn
    rw [occurrence_eq_avoiding π hn]
    have hit (σ : Perm (Fin n)) : contains π σ :=
      ⟨0,by omega,fun i ↦ Fin.elim0 i⟩
    simp [hit]
  | succ j =>
    let k := j+1
    let d (n : ℕ) := n.choose 2-m n
    let u (s n t : ℕ) := (1-((t:ℝ)/(t+n))^s/(k.factorial:ℝ))^(n/4/k)
    have hk : 0<k := Nat.succ_pos j
    have hi : Tendsto (fun n ↦ u (inversions π) n (m n)) atTop (𝓝 0) := block_decay hk lower
    have hu : above (inversions (complement π)) d := by simpa only [inversions_complement] using upper
    have hj : Tendsto (fun n ↦ u (inversions (complement π)) n (d n)) atTop (𝓝 0) := block_decay hk hu
    have lim : Tendsto (fun n ↦ 52*(u (inversions π) n (m n)+u (inversions (complement π)) n (d n)))
        atTop (𝓝 0) := by simpa only [add_zero,mul_zero] using (hi.add hj).const_mul 52
    have fail : Tendsto (fun n ↦ 1-occurrence π n (m n)) atTop (𝓝 0) := by
      apply squeeze_zero' _ _ lim
      · filter_upwards [valid] with n hn
        rw [occurrence_eq_avoiding π hn,sub_sub_cancel]
        positivity
      · filter_upwards [valid,eventually_ge_atTop 3] with n hn large
        have size : 2≤n.choose 2 := (by decide : 2≤(3:ℕ).choose 2).trans (Nat.choose_le_choose 2 large)
        have p0 := block_term_nonneg k (inversions π) n (m n)
        have p1 := block_term_nonneg k (inversions (complement π)) n (d n)
        change 0≤u _ _ _ at p0 p1
        by_cases low : 2*m n≤n.choose 2
        · have bound := avoidance_bound π hk size low
          change _≤52*u (inversions π) n (m n) at bound
          linarith
        · rw [occurrence_complement π n (m n) hn]
          have bound := avoidance_bound (complement π) hk size (show 2*d n≤n.choose 2 by dsimp [d]; omega)
          change _≤52*u (inversions (complement π)) n (d n) at bound
          change 1-occurrence (complement π) n (d n) ≤ _
          linarith
    simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub fail

/-- info: 'ConsecutiveThreshold.conjecture21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjecture21

end ConsecutiveThreshold
