module

public import conjectures.McCuneSeatJumps.Construction
public import conjectures.McCuneSeatJumps.Obstruction

open Set
namespace McCuneSeatJumps

/-- The entire support of the loss probability for a positive house and a positive jump. -/
public theorem positive_iff {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < probability h k ↔ k < h ∧ ¬ h-k ∣ h :=
  ⟨necessary hh,fun ⟨kh,nd⟩ => sufficient hk kh nd⟩

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
    exact le_of_not_gt (fun hp => by have h := necessary (by decide) hp; revert h; decide)

public theorem resolution : ¬ Conjecture := by
  intro H
  have M := (H 9 (by decide)).1 (by decide)
  have h := M (a:=6) (b:=7) (by decide) (by decide) (by decide)
  rw [counterexamples.1] at h
  exact (not_lt_of_ge h) counterexamples.2.1

/-- info: 'McCuneSeatJumps.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end McCuneSeatJumps
