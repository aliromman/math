module

public import conjectures.BajnokRestrictedInverse.Statement
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset

public section
namespace BajnokRestrictedInverse

/-- The nonzero squares in the field with 17 elements. -/
def squares17 : Finset (ZMod 17) :=
  (Finset.univ.erase (0 : ZMod 17)).image (fun x => x * x)

set_option maxRecDepth 16000 in
theorem triple_sums : restricted 3 squares17 = Finset.univ.erase (0 : ZMod 17) := by decide

set_option maxRecDepth 16000 in
theorem no_progression : ¬ IsProgression squares17 := by
  unfold IsProgression
  decide

theorem counterexample : ¬ Conjecture := by
  intro claim
  have consequence := (claim (ZMod 17) 3 squares17 (by decide) (by decide)
    (by decide) (by rw [ZMod.card, (by decide : Nat.Prime 17).minFac_eq]; decide)).mp
      (by rw [triple_sums]; decide)
  exact consequence.elim (fun h => (by decide : 3 ≠ 2) h.1) no_progression

/-- info: 'BajnokRestrictedInverse.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample


local notation "F" => ZMod 17

/-- An eight-term progression in the field of order 17. -/
def interval : Finset F := {5,6,7,8,9,10,11,12}

private def dilations (S : Finset F) : Finset (Finset F) :=
  (Finset.univ.erase (0 : F)).image (fun d => S.image (fun x => d*x))

/-- Nonzero dilations of the interval and the nonzero squares. -/
def patterns : Finset (Finset F) := dilations interval ∪ dilations squares17

private def compatible (S : Finset F) (x y : F) : Bool :=
  decide (x = y ∨ -x-y = x ∨ -x-y = y ∨ -x-y ∉ S)

/-- Extend a partial set with `k` vertices. Remove choices that would complete a zero triple. -/
private def grow : ℕ → ℕ → Finset F → List F → List (Finset F)
  | _, 0, S, _ => [S]
  | fuel+1, k+1, S, x::xs => if xs.length < k then [] else
      grow fuel (k+1) S xs ++
        grow fuel k (insert x S) (xs.filter (compatible S x))
  | _, _, _, _ => []

private def allPoints : List F := List.ofFn (fun x : Fin 17 => (x : F))

private theorem compatible_of_missing {A S : Finset F} (hn : 0 ∉ restricted 3 A)
    (hS : S ⊆ A) {x y : F} (hx : x ∈ A) (hy : y ∈ A) : compatible S x y = true := by
  unfold compatible
  apply decide_eq_true
  by_contra! h
  obtain ⟨hne, hzx, hzy, hz⟩ := h
  apply hn
  refine Finset.mem_image.mpr ⟨{x, y, -x-y}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, hx, hy, hS hz, and_self]
  · simp [hne, hzx.symm, hzy.symm]
  · simp [hne, hzx.symm, hzy.symm]

private theorem pool_card {R : Finset F} {xs : List F} (h : ∀ z ∈ R, z ∈ xs) : R.card ≤ xs.length :=
  (Finset.card_le_card (show R ⊆ xs.toFinset from fun z hz => List.mem_toFinset.mpr (h z hz))).trans
    xs.toFinset_card_le

private theorem complete (fuel k : ℕ) (S R : Finset F) (xs : List F)
    (len : xs.length ≤ fuel) (size : R.card = k) (pool : ∀ z ∈ R, z ∈ xs)
    (hn : 0 ∉ restricted 3 (S ∪ R)) : S ∪ R ∈ grow fuel k S xs := by
  induction fuel generalizing k S R xs with
  | zero =>
    have := pool_card pool
    have hzero : R.card = 0 := by omega
    subst k
    rw [Finset.card_eq_zero.mp hzero]
    simp [grow]
  | succ fuel ih =>
    cases k with
    | zero =>
      rw [Finset.card_eq_zero.mp size]
      simp [grow]
    | succ k =>
      cases xs with
      | nil => have hh := pool_card pool; change R.card ≤ 0 at hh; omega
      | cons x xs =>
        have hb := pool_card pool
        simp only [List.length_cons] at hb len
        simp only [grow, show ¬ xs.length < k by omega, ite_false, List.mem_append]
        by_cases hx : x ∈ R
        · right
          have un : insert x S ∪ R.erase x = S ∪ R := by
            ext y
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
            grind
          rw [← un]
          apply ih
          · exact (List.length_filter_le _ _).trans (by omega)
          · rw [Finset.card_erase_of_mem hx, size]; omega
          · intro y hy
            obtain ⟨hne, hyr⟩ := Finset.mem_erase.mp hy
            refine List.mem_filter.mpr ⟨(List.mem_cons.mp (pool y hyr)).resolve_left hne, ?_⟩
            exact compatible_of_missing hn Finset.subset_union_left (Finset.mem_union_right _ hx)
              (Finset.mem_union_right _ hyr)
          · rwa [un]
        · left
          exact ih _ _ _ _ (by omega) size (fun y hy =>
            (List.mem_cons.mp (pool y hy)).resolve_left (fun eq => hx (eq ▸ hy))) hn

/-- Exactly two dilation classes of eight-element sets omit zero from their triple sumset. -/
theorem classify_at_zero (A : Finset F) (size : A.card = 8) :
    0 ∉ restricted 3 A ↔ A ∈ patterns := by
  constructor
  · intro hn
    have hc : A ∈ grow 17 8 ∅ allPoints := by
      simpa using complete 17 8 ∅ A allPoints (by decide) size
        (fun z _ => List.mem_ofFn.mpr ⟨z, rfl⟩) (by simpa using hn)
    have hg : (grow 17 8 ∅ allPoints).all (fun T => decide (T ∈ patterns)) = true := by
      set_option maxRecDepth 16000 in decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hg A hc)
  · intro h
    have hp : patterns.filter (fun T => 0 ∉ restricted 3 T) = patterns := by
      set_option maxRecDepth 16000 in decide
    exact (Finset.mem_filter.mp (hp ▸ h : A ∈ patterns.filter (fun T => 0 ∉ restricted 3 T))).2

/-- Add the same residue to every element of a set. -/
def shift (q : F) (A : Finset F) : Finset F := A.map (Equiv.addRight q).toEmbedding

private theorem shift_restricted (h : ℕ) (A : Finset F) (d : F) :
    restricted h (shift d A) = shift (h • d) (restricted h A) := by
  unfold restricted shift
  rw [Finset.powersetCard_map]
  ext x
  simp only [Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨T, ⟨S, hs, rfl⟩, rfl⟩
    refine ⟨∑ z ∈ S, z, ⟨S, hs, rfl⟩, ?_⟩
    simp [Finset.sum_map, Finset.sum_add_distrib, (Finset.mem_powersetCard.mp hs).2]
  · rintro ⟨_, ⟨S, hs, rfl⟩, rfl⟩
    refine ⟨_, ⟨S, hs, rfl⟩, ?_⟩
    simp [Finset.sum_map, Finset.sum_add_distrib, (Finset.mem_powersetCard.mp hs).2]


/-- Exactly two affine classes of eight-element sets have sixteen distinct triple sums. -/
theorem affine_classification (A : Finset F) (size : A.card = 8) :
    (restricted 3 A).card = 16 ↔ ∃ d : F, shift d A ∈ patterns := by
  constructor
  · intro h
    have lt : (restricted 3 A).card < (Finset.univ : Finset F).card := by
      rw [h]
      decide
    obtain ⟨y, _, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card lt
    refine ⟨-6*y, (classify_at_zero _ (by simpa [shift] using size)).mp ?_⟩
    have hshift : 3 • (-6*y) = -y := (show ∀ u : F, 3 • (-6*u) = -u by decide) y
    rw [shift_restricted, hshift]
    intro hz
    obtain ⟨s, hs, he⟩ := Finset.mem_map.mp hz
    change s + -y = 0 at he
    exact hy ((eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using he) : s = y) ▸ hs)
  · rintro ⟨d, hd⟩
    have all : patterns.filter (fun T => (restricted 3 T).card = 16) = patterns := by
      set_option maxRecDepth 16000 in decide
    have hs := (Finset.mem_filter.mp (all ▸ hd : shift d A ∈
      patterns.filter (fun T => (restricted 3 T).card = 16))).2
    rw [shift_restricted] at hs
    simpa [shift] using hs

/-- info: 'BajnokRestrictedInverse.affine_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_classification

/-- All images under invertible affine transformations of the field of order 17. -/
def affineCopies (S : Finset F) : Finset (Finset F) :=
  Finset.univ.biUnion (fun t : F =>
    (Finset.univ.erase (0 : F)).image (fun d => S.image (fun x => t + d*x)))

set_option maxRecDepth 16000 in
theorem orbit_sizes : (affineCopies interval).card = 136 ∧ (affineCopies squares17).card = 34 ∧
    Disjoint (affineCopies interval) (affineCopies squares17) := by decide +kernel

set_option maxRecDepth 16000 in
/-- A six-element counterexample in the field of order 11. -/
theorem eleven_example : let A : Finset (ZMod 11) := {0,1,3,4,5,9}
    A.card = 6 ∧ restricted 3 A = Finset.univ.erase 0 ∧ ¬ IsProgression A := by
  dsimp only
  unfold IsProgression
  decide

end BajnokRestrictedInverse
