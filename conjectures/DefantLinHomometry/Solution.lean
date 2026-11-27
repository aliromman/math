module

public import conjectures.DefantLinHomometry.Statement
import all Init.Data.List.Scan.Basic

public section
namespace DefantLinHomometry

private def path : List Bool := [false, false, true, false, true, false, true, true, false, false, false, false, false, true]

private abbrev Edits := List (ℕ × ℕ)

private def first : List (Vec × Edits) := [
  ([0, 0, 0, 5, 1, 3, 2, 3, 5, 5, 5, 5, 4, 4, 5], [(3, 3), (5, 2), (11, 4)]),
  ([5, 5, 0, 3, 1, 2, 2, 3, 5, 5, 5, 4, 4, 4, 5], [(1, 3), (3, 2), (10, 4)]),
  ([5, 3, 0, 2, 1, 2, 2, 3, 5, 5, 4, 4, 4, 4, 5], [(0, 3), (1, 2), (3, 1), (9, 4)]),
  ([3, 2, 0, 1, 1, 2, 2, 3, 5, 4, 4, 4, 4, 4, 5], [(0, 2), (1, 1), (8, 4)]),
  ([2, 1, 0, 1, 1, 2, 2, 3, 4, 4, 4, 4, 4, 4, 5], [(0, 1), (1, 0)]),
  ([1, 0, 0, 1, 1, 5, 2, 3, 5, 5, 5, 5, 5, 4, 5], [(0, 0), (5, 3), (12, 4)])]

private def second : List (Vec × Edits) := [
  ([3, 3, 0, 3, 1, 3, 2, 3, 4, 4, 4, 4, 4, 4, 5], [(1, 0), (3, 1), (5, 2)]),
  ([5, 0, 0, 1, 1, 2, 2, 3, 5, 5, 5, 5, 5, 4, 5], [(0, 3), (12, 4)]),
  ([3, 3, 0, 3, 1, 3, 2, 3, 5, 5, 5, 5, 4, 4, 5], [(1, 0), (3, 1), (5, 2), (11, 4)]),
  ([5, 0, 0, 1, 1, 2, 2, 3, 5, 5, 5, 4, 4, 4, 5], [(0, 3), (10, 4)]),
  ([3, 3, 0, 3, 1, 3, 2, 3, 5, 5, 4, 4, 4, 4, 5], [(1, 0), (3, 1), (5, 2), (9, 4)]),
  ([5, 0, 0, 1, 1, 2, 2, 3, 5, 4, 4, 4, 4, 4, 5], [(0, 3), (8, 4)])]

private def visits (rows : List (Vec × Edits)) : List Visit :=
  rows.map fun (x, edits) => (x, edits.length)

private def coversFor (x : Vec) : List Vec :=
  let edits := ((first ++ second).lookup x).getD []
  edits.map fun (i, h) => x.set i h

/-- An antichain of strict predecessors contains all lower covers exactly when it
dominates every strict predecessor. -/
private def CoverCertificate (B : List Vec) (x : Vec) (C : List Vec) : Prop :=
  C.Nodup ∧
  (∀ c ∈ C, c ∈ B ∧ c ≠ x ∧ below c x = true) ∧
  (∀ c ∈ C, ∀ d ∈ C, below c d = true → c = d) ∧
  (∀ z ∈ B, z ≠ x → below z x = true → ∃ c ∈ C, below z c = true)

private theorem below_trans {a b c : Vec} (hab : below a b = true)
    (hbc : below b c = true) : below a c = true := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp_all [below]
  | cons i a ih =>
    cases b with
    | nil => simp [below] at hab
    | cons j b =>
      cases c with
      | nil => simp [below] at hbc
      | cons k c =>
        simp only [below, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
        exact ⟨Nat.le_trans hab.1 hbc.1, ih hab.2 hbc.2⟩

private theorem below_antisymm {a b : Vec} (hab : below a b = true)
    (hba : below b a = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [below]
  | cons i a ih =>
    cases b with
    | nil => simp [below] at hab
    | cons j b =>
      simp only [below, Bool.and_eq_true, decide_eq_true_eq] at hab hba
      rw [Nat.le_antisymm hab.1 hba.1, ih hab.2 hba.2]

private theorem covers_iff {B : List Vec} {x : Vec} {C : List Vec}
    (h : CoverCertificate B x C) (c : Vec) : c ∈ C ↔ LowerCover B c x := by
  obtain ⟨_, hm, ha, hd⟩ := h
  constructor
  · intro hc
    obtain ⟨hcB, hne, hbelow⟩ := hm c hc
    refine ⟨hcB, hne, hbelow, ?_⟩
    intro z hz hzx hzx' hcz
    obtain ⟨d, hdC, hzd⟩ := hd z hz hzx hzx'
    have hcd := ha c hc d hdC (below_trans hcz hzd)
    rw [← hcd] at hzd
    exact below_antisymm hzd hcz
  · rintro ⟨hcB, hne, hbelow, hmax⟩
    obtain ⟨d, hdC, hcd⟩ := hd c hcB hne hbelow
    obtain ⟨hdB, hne', hbelow'⟩ := hm d hdC
    exact hmax d hdB hne' hbelow' hcd ▸ hdC

private def Check (B : List Vec) (O : List Visit) : Prop :=
  ∀ pair ∈ adjacent O,
    let x := pair.1.1
    let y := pair.2.1
    let C := coversFor x
    let pop := C.foldl meet x
    x ∈ B ∧ y ∈ B ∧ CoverCertificate B x C ∧ C.length = pair.1.2 ∧
      meet x y = pop ∧ ∀ z ∈ B, meet x z = pop → below z y = true

private theorem orbit_of_check {B : List Vec} {O : List Visit}
    (hO : O ≠ []) (hd : (O.map Prod.fst).Nodup) (hc : Check B O) : Orbit B O := by
  refine ⟨hO, hd, ?_⟩
  intro pair hp
  obtain ⟨hx, hy, hcov, hcard, hmeet, hmax⟩ := hc pair hp
  exact ⟨hx, hy, coversFor pair.1.1, hcov.1, covers_iff hcov, hcard, hmeet, hmax⟩

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem first_orbit : Orbit (lattice path) (visits first) := by
  apply orbit_of_check (by decide) (by decide)
  unfold Check CoverCertificate
  decide +kernel

private theorem second_orbit : Orbit (lattice path) (visits second) := by
  apply orbit_of_check (by decide) (by decide)
  unfold Check CoverCertificate
  decide +kernel

theorem resolution : ¬ Homometric := by
  intro conjecture
  have h := conjecture path _ _ first_orbit second_orbit (by decide)
  exact (by decide : degreeSum (visits first) ≠ degreeSum (visits second)) h

/-- info: 'DefantLinHomometry.resolution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end DefantLinHomometry
