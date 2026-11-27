module

public import conjectures.McCuneSeatJumps.Probability
import Mathlib.Tactic.NormNum

open Set Finset
namespace McCuneSeatJumps

private theorem threshold {h k : ℕ} (hh : 0<h) :
    2 ≤ (h-k)/h.gcd k ↔ k<h ∧ ¬ h-k ∣ h := by
  let g := h.gcd k
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ hh
  have dr : g ∣ h-k := Nat.dvd_sub (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)
  rw [Nat.le_div_iff_mul_le gp]
  change 2*g ≤ h-k ↔ _
  constructor
  · intro he
    refine ⟨by omega,fun dv => ?_⟩
    have dk := Nat.dvd_sub dv (dvd_refl (h-k))
    rw [show h-(h-k)=k by omega] at dk
    have dg := Nat.le_of_dvd gp (Nat.dvd_gcd dv dk)
    omega
  · rintro ⟨kh,nd⟩
    obtain ⟨u,hu⟩ := dr
    have p : 0<u := by by_contra! e; simp [Nat.eq_zero_of_le_zero e] at hu; omega
    have n : u≠1 := by
      rintro rfl
      simp only [mul_one] at hu
      exact nd (hu ▸ Nat.gcd_dvd_left h k)
    have m := Nat.mul_le_mul_left g (show 2≤u by omega)
    simpa [hu,mul_comm] using m

/-- The entire support of the loss probability for a positive house and a positive jump. -/
public theorem positive_iff {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < probability h k ↔ k < h ∧ ¬ h-k ∣ h := by
  let T (j : ℕ) := room h k (j+1)/h.gcd k
  have top (j) : T j ≤ (h-k)/h.gcd k := by
    apply Nat.div_le_div_right
    unfold room
    have m := Nat.mul_le_mul_left (3*k) (show 1≤j+1 by omega)
    omega
  have gp := Nat.gcd_pos_of_pos_left k hh
  have coeff : 0 < ((h.gcd k:ℕ):ℝ)^3/(3*h^2*(h+k)^2) := by positivity
  have cube (z : ℝ) : z^3-z=z*(z-1)*(z+1) := by ring
  have term (t : ℕ) : 0 ≤ (t:ℝ)^3-t := by
    cases t with
    | zero => norm_num
    | succ n => rw [cube]; push_cast; simp only [add_sub_cancel_right]; positivity
  have sq0 : T 0 = (h-k)/h.gcd k := by simp [T,room,show h+2*k-3*k=h-k by omega]
  rw [exact_probability hh hk, ENNReal.ofReal_pos, mul_pos_iff_of_pos_left coeff,← threshold hh]
  change (0 < ∑ j ∈ range h, ((T j:ℝ)^3-T j)) ↔ _
  constructor
  · contrapose!
    intro lt
    apply sum_nonpos
    intro j _
    have le : T j≤1 := (top j).trans (by omega)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp le with z|z <;> simp [z]
  · intro two
    apply sum_pos' (fun j _ => term (T j))
    refine ⟨0,mem_range.mpr hh,?_⟩
    have v : (2:ℝ)≤T 0 := by exact_mod_cast (sq0 ▸ two : 2≤T 0)
    rw [cube]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Subtract the least positive nondivisor of the house size to get the largest jump. -/
public theorem maximum_jump {h : ℕ} (hh : 3 ≤ h) :
    ∃ d, IsLeast {r : ℕ | 0 < r ∧ ¬ r ∣ h} d ∧ maxJump h = h-d := by
  classical
  have last : ¬ h-1 ∣ h := by
    intro h'
    have a := Nat.dvd_sub h' (dvd_refl (h-1))
    rw [show h-(h-1)=1 by omega] at a
    have := Nat.le_of_dvd (by decide : 0 < 1) a
    omega
  have ex : ∃ r : ℕ, 0 < r ∧ ¬r ∣ h := ⟨h-1,by omega,last⟩
  let d := Nat.find ex
  have spec : 0 < d ∧ ¬d ∣ h := Nat.find_spec ex
  have least : IsLeast {r : ℕ | 0 < r ∧ ¬r ∣ h} d := ⟨spec,fun _ hy => Nat.find_min' ex hy⟩
  have dl : d ≤ h-1 := least.2 ⟨by omega,last⟩
  have hd : 0 < h-d := by omega
  refine ⟨d,least,IsGreatest.csSup_eq ?_⟩
  refine ⟨⟨hd,(positive_iff (by omega) hd).mpr ⟨by omega,?_⟩⟩,?_⟩
  · rw [show h-(h-d) = d by omega]; exact spec.2
  · intro k hk
    obtain ⟨kh,nd⟩ := (positive_iff (by omega) hk.1).mp hk.2
    have dl' : d ≤ h-k := least.2 ⟨by omega,nd⟩
    omega

/-- Both the odd monotonicity claim and the claimed even tail can fail. -/
public theorem counterexamples : probability 9 6 = 0 ∧ 0 < probability 9 7 ∧
    probability 16 12 = 0 ∧ 0 < probability 16 13 := by
  refine ⟨?_,(positive_iff (by decide) (by decide)).mpr (by decide),?_,
    (positive_iff (by decide) (by decide)).mpr (by decide)⟩
  all_goals
    apply nonpos_iff_eq_zero.mp
    exact le_of_not_gt (fun hp => by have h := (positive_iff (by decide) (by decide)).mp hp; revert h; decide)

public theorem resolution : ¬ Conjecture := by
  intro H
  have M := (H 9 (by decide)).1 (by decide)
  have h := M (a:=6) (b:=7) (by decide) (by decide) (by decide)
  rw [counterexamples.1] at h
  exact (not_lt_of_ge h) counterexamples.2.1

/-- info: 'McCuneSeatJumps.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- The loss probability can rise between positive values for either parity. -/
public theorem positive_reversals :
    probability 27 9 = ENNReal.ofReal (1/648) ∧
    probability 27 10 = ENNReal.ofReal (544/332667) ∧
    probability 30 10 = ENNReal.ofReal (1/720) ∧
    probability 30 11 = ENNReal.ofReal (38/25215) := by
  repeat' constructor
  all_goals rw [exact_probability (by decide) (by decide)]
  all_goals congr 1; norm_num [Finset.sum_range_succ,room]

/-- info: 'McCuneSeatJumps.exact_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_probability

end McCuneSeatJumps
