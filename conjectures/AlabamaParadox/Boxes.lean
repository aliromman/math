module

public import conjectures.AlabamaParadox.Flag
public import conjectures.AlabamaParadox.Weyl

@[expose] public section
open Finset Filter Set
open scoped Topology
namespace AlabamaParadox

variable {m : ℕ} {p : Fin m → ℝ} {n : ℕ} {i : Fin m}

abbrev Other (i : Fin m) := {j : Fin m // j ≠ i}

/-- An optional state records the only crossing, if there is one. -/
abbrev Label (m : ℕ) := (i : Fin m) × Option (Other i)

noncomputable def lower (p : Fin m → ℝ) (t : Option (Other i)) (j : Other i) :=
  if t = some j then 1-p j else 0

noncomputable def upper (p : Fin m → ℝ) (t : Option (Other i)) (j : Other i) :=
  if t = some j then 1 else 1-p j

def Box (p : Fin m → ℝ) (b : Label m) (n : ℕ) : Prop :=
  Flag p n b.1 ∧ ∀ j : Other b.1,
    Int.fract (offset p n b.1 j) ∈ Ico (lower p b.2 j) (upper p b.2 j)

noncomputable def weight (p : Fin m → ℝ) (b : Label m) :=
  (∏ j : Other b.1, (upper p b.2 j - lower p b.2 j)) / m

theorem box_limit [NeZero m] [Nontrivial (Fin m)] (hpos : ∀ j, 0 < p j)
    (hlt : ∀ j, p j < 1) (hs : ∑ j, p j = 1) (hi : IndependentShares p)
    (b : Label m) : Tendsto (frequency (Box p b)) atTop (𝓝 (weight p b)) := by
  obtain ⟨i,t⟩ := b
  have : Nonempty (Other i) := by
    obtain ⟨j,hj⟩ := exists_ne i
    exact ⟨j,hj⟩
  apply flag_frequency (m:=m) (nonresonant_differences p i hs hi)
  · intro j
    dsimp [lower]
    split <;> linarith [hlt j]
  · intro j
    dsimp [lower,upper]
    split <;> linarith [hpos j, hlt j]
  · intro j
    dsimp [upper]
    split <;> linarith [hpos j]

private theorem records {t : Option (Other i)} (hb : Box p ⟨i,t⟩ n) (j : Other i) :
    1-p j ≤ Int.fract (offset p n i j) ↔ t = some j := by
  have h := hb.2 j
  by_cases e : t = some j
  · refine ⟨fun _ => e, fun _ => ?_⟩
    simpa [lower,e] using h.1
  · have hn : Int.fract (offset p n i j) < 1-p j := by simpa [upper,e] using h.2
    exact ⟨fun h => (not_le.mpr hn h).elim, fun h => (e h).elim⟩

theorem box_unique [Nontrivial (Fin m)] (hs : ∑ i, p i = 1) (hi : IndependentShares p)
    (hn : 0 < n) {b b' : Label m} (h : Box p b n) (h' : Box p b' n) : b = b' := by
  obtain ⟨i,t⟩ := b
  obtain ⟨j,u⟩ := b'
  obtain rfl := flag_unique hs hi hn h.1 h'.1
  have eqv (k : Other i) : t = some k ↔ u = some k := (records h k).symm.trans (records h' k)
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some k => have hn := (eqv k).mpr rfl; contradiction
  | some k =>
    obtain rfl := (eqv k).mp rfl
    rfl

theorem box_no_loss [Nontrivial (Fin m)] (hpos : ∀ j, 0 < p j) (hlt : ∀ j, p j < 1)
    (hs : ∑ i, p i = 1) (hi : IndependentShares p) {b : Label m} (hb : Box p b n) :
    ¬ Loss p n := by
  obtain ⟨i,t⟩ := b
  rintro ⟨hn,a,b,ha,hb',j,hj⟩
  let c := cutoff p n i
  have hc := cutoff_pos hs hi hn i
  have hc' : c ≤ 1 := (Int.fract_lt_one _).le
  have total := flag_total hs hi hn hb.1
  let K (k : Fin m) : ℤ := if 1-p k ≤ Int.fract (offset p n i k) then 1 else 0
  have eqK (k : Fin m) : K k = if t.map Subtype.val = some k then 1 else 0 := by
    by_cases e : k = i
    · subst k
      have hn : t.map Subtype.val ≠ some i := by
        cases t with
        | none => simp
        | some x => simpa using x.property
      rw [ite_eq_right hn]
      simp [K,offset,not_le.mpr (hlt i)]
    · let k' : Other i := ⟨k,e⟩
      have he : t.map Subtype.val = some k ↔ t = some k' := by
        cases t <;> simp [k',Subtype.ext_iff]
      change (if 1-p k' ≤ Int.fract (offset p n i k') then (1:ℤ) else 0) = _
      by_cases g : t = some k'
      · rw [ite_eq_left ((records hb k').mpr g), ite_eq_left (he.mpr g)]
      · rw [ite_eq_right (mt (records hb k').mp g), ite_eq_right (mt he.mp g)]
  have cardK : ∑ k, K k ≤ 1 := by
    simp_rw [eqK]
    cases t <;> simp
  have step (k : Fin m) : frozen p (n+1) c k = frozen p n c k + K k :=
    frozen_step (fun j => (hpos j).le) hlt n i k
  have tt : ∑ k, frozen p (n+1) c k ≤ ↑(n+1 : ℕ) := by
    simp_rw [step]
    rw [sum_add_distrib, total]
    omega
  have old := frozen_eq ha hc hc' total j
  have new := frozen_le hb' hc hc' tt j
  have hk : 0 ≤ K j := by dsimp [K]; split <;> decide
  have mono : a j ≤ frozen p (n+1) c j := by
    rw [← old, step]
    exact le_add_of_nonneg_right hk
  exact (not_lt_of_ge (mono.trans new)) hj

end AlabamaParadox
