module

public import conjectures.ErdosSuranyi708.Scores
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section
namespace ErdosSuranyi708
open Finset

/-- The lower exponent of the bucket containing a given valuation.
Zero means that no positive exponent in the grid has been reached. -/
def lastCut (C : Finset ℕ) (v : ℕ) : ℕ := (C.filter (· ≤ v)).sup id

def nextCut (C : Finset ℕ) (a : ℕ) : ℕ :=
  if h : (C.filter (a < ·)).Nonempty then (C.filter (a < ·)).min' h else 0

theorem lastCut_le (C : Finset ℕ) (v : ℕ) : lastCut C v ≤ v :=
  Finset.sup_le fun _ h ↦ (mem_filter.mp h).2

theorem le_lastCut {C : Finset ℕ} {a v : ℕ} (h : a ∈ C) (hav : a ≤ v) : a ≤ lastCut C v :=
  Finset.le_sup (f := id) (mem_filter.mpr ⟨h,hav⟩)

theorem lastCut_mem {C : Finset ℕ} (h : 1 ∈ C) {v : ℕ} (hv : 0 < v) : lastCut C v ∈ C := by
  have hn : (C.filter (· ≤ v)).Nonempty := ⟨1, mem_filter.mpr ⟨h,hv⟩⟩
  obtain ⟨b, hb, he⟩ := sup_mem_of_nonempty (f := id) hn
  change b = lastCut C v at he
  simpa only [← he] using (mem_filter.mp hb).1

theorem nextCut_spec {C : Finset ℕ} {a t : ℕ} :
    (nextCut C a = 0 ∨ t < nextCut C a) ↔ ∀ b ∈ C, a < b → t < b := by
  classical
  unfold nextCut
  split
  next h =>
    let U := C.filter (a < ·)
    change U.min' h = 0 ∨ t < U.min' h ↔ _
    have hh : U.min' h ∈ C ∧ a < U.min' h := mem_filter.mp (min'_mem U h)
    constructor
    · intro h1 b hb hab
      have ht := min'_le U b (mem_filter.mpr ⟨hb,hab⟩)
      omega
    · intro h1
      exact Or.inr (h1 _ hh.1 hh.2)
  next h =>
    simp only [true_or, eq_self, true_iff]
    intro b hb hh
    exact False.elim (h ⟨b,mem_filter.mpr ⟨hb,hh⟩⟩)

theorem lastCut_eq_iff {C : Finset ℕ} {v a : ℕ} (ha : a ∈ C) :
    lastCut C v = a ↔ a ≤ v ∧ (nextCut C a = 0 ∨ v < nextCut C a) := by
  rw [nextCut_spec]
  constructor
  · intro hh
    refine ⟨hh ▸ lastCut_le C v, fun b hb hlt ↦ ?_⟩
    by_contra! he
    exact hlt.not_ge (hh ▸ le_lastCut hb he)
  · intro ⟨h1,h2⟩
    apply le_antisymm _ (le_lastCut ha h1)
    exact Finset.sup_le fun b hb ↦ by
      obtain ⟨hb,hv⟩ := mem_filter.mp hb
      by_contra! h
      exact (h2 b hb h).not_ge hv

def codeCuts (E : ℕ) (g : ℕ → ℕ) :=
  insert 1 ((Icc 2 E).filter fun j ↦ g (j-1) < g j)

private theorem codeCuts_positive {E j : ℕ} {g : ℕ → ℕ} (h : j ∈ codeCuts E g) : 0 < j := by
  simp [codeCuts] at h
  omega

private theorem lastCut_code {E : ℕ} {g : ℕ → ℕ} (hg : Monotone g)
    {j : ℕ} (hj : 0 < j) (he : j ≤ E) : g (lastCut (codeCuts E g) j) = g j := by
  have witness : ∀ v : ℕ, 0 < v → v ≤ E → ∃ k ∈ codeCuts E g, k ≤ v ∧ g k = g v := by
    intro v
    induction v with
    | zero => omega
    | succ v ih =>
      intro hv hvE
      by_cases h0 : v = 0
      · subst v
        exact ⟨1,mem_insert_self ..,le_rfl,rfl⟩
      by_cases hup : g v < g (v+1)
      · refine ⟨v+1,mem_insert_of_mem (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hvE⟩,?_⟩),le_rfl,rfl⟩
        simpa using hup
      · obtain ⟨k,hk,hle,hgk⟩ := ih (by omega) (by omega)
        exact ⟨k,hk,by omega,hgk.trans (le_antisymm (hg (by omega)) (le_of_not_gt hup))⟩
  obtain ⟨k,hk,hkj,hgk⟩ := witness j hj he
  exact le_antisymm (hg (lastCut_le _ _)) (hgk ▸ hg (le_lastCut hk hkj))

private theorem codeCuts_card_le {E K : ℕ} {g : ℕ → ℕ} (hg : Monotone g)
    (hb : ∀ j, g j ≤ K) : (codeCuts E g).card ≤ K+1 := by
  have step {i j : ℕ} (hi : i ∈ codeCuts E g) (hj : j ∈ codeCuts E g) (hlt : i < j) : g i < g j := by
    have hi0 := codeCuts_positive hi
    rcases mem_insert.mp hj with heq|hj
    · omega
    · exact (hg (by omega : i ≤ j-1)).trans_lt (mem_filter.mp hj).2
  have hinj : Set.InjOn g ↑(codeCuts E g) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h|h|h
    · exact ((step hi hj h).ne he).elim
    · exact h
    · exact ((step hj hi h).ne he.symm).elim
  rw [← card_image_of_injOn hinj]
  apply (card_le_card (t := range (K+1)) ?_).trans_eq (card_range _)
  intro i hi
  obtain ⟨j,_,rfl⟩ := mem_image.mp hi
  exact mem_range.mpr (Nat.lt_succ_of_le (hb j))

noncomputable def bucketCode (Y K p : ℕ) (w : ℕ → ℝ) (v : ℕ) : ℕ :=
  if p ≤ Y then ⌊(K : ℝ) * min 1 (w p * v)⌋₊ else v

noncomputable def grid (Y K M : ℕ) (w : ℕ → ℝ) (p : ℕ) : Finset ℕ :=
  codeCuts (Nat.log p M) (bucketCode Y K p w)

theorem grid_one (Y K M : ℕ) (w : ℕ → ℝ) (p : ℕ) : 1 ∈ grid Y K M w p := mem_insert_self ..

theorem grid_positive {Y K M p j : ℕ} {w : ℕ → ℝ} (hj : j ∈ grid Y K M w p) : 0 < j :=
  codeCuts_positive hj

private theorem bucketCode_mono {Y K p : ℕ} {w : ℕ → ℝ} (hw : 0 ≤ w p) :
    Monotone (bucketCode Y K p w) := by
  intro i j hij
  unfold bucketCode
  split
  · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left
      (min_le_min le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) hw)) (Nat.cast_nonneg _))
  · exact hij

theorem grid_card_small {Y K M p : ℕ} (w : ℕ → ℝ) (hp : p ≤ Y) (hw : 0 ≤ w p) :
    (grid Y K M w p).card ≤ K+1 := by
  apply codeCuts_card_le (bucketCode_mono hw)
  intro j
  simp only [bucketCode, ite_eq_left hp]
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg K) (min_le_left ..)

theorem grid_le_log {Y K M p j : ℕ} {w : ℕ → ℝ} (hp : 1 < p) (hM : p ≤ M)
    (hj : j ∈ grid Y K M w p) : j ≤ Nat.log p M := by
  rcases mem_insert.mp hj with h|h
  · subst j
    exact Nat.le_log_of_pow_le hp (by simpa using hM)
  · exact (mem_Icc.mp (mem_filter.mp h).1).2

theorem grid_card_large {Y K M p : ℕ} {w : ℕ → ℝ} (hp : 1 < p) (hM : p ≤ M) :
    (grid Y K M w p).card ≤ Nat.log p M := by
  calc
    _ ≤ (Icc 1 (Nat.log p M)).card := card_le_card fun j h ↦
      mem_Icc.mpr ⟨grid_positive h,grid_le_log hp hM h⟩
    _ = _ := by simp

noncomputable def siteExponent (Y K M : ℕ) (w : ℕ → ℝ) (p a : ℕ) : ℕ :=
  lastCut (grid Y K M w p) (a.factorization p)

noncomputable def siteWeight (Y K M : ℕ) (w : ℕ → ℝ) (a p : ℕ) : ℝ :=
  min 1 (w p * siteExponent Y K M w p a)

theorem siteWeight_nonneg {Y K M a p : ℕ} {w : ℕ → ℝ} (hw : 0 ≤ w p) :
    0 ≤ siteWeight Y K M w a p := le_min zero_le_one (mul_nonneg hw (Nat.cast_nonneg _))

theorem siteWeight_le {Y K M a p : ℕ} {w : ℕ → ℝ} (hw : 0 ≤ w p) :
    siteWeight Y K M w a p ≤ min 1 (w p * a.factorization p) :=
  min_le_min le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (lastCut_le ..)) hw)

theorem sourceWeight_le {Y K M a p : ℕ} {w : ℕ → ℝ} (hK : 0 < K) (hw : 0 ≤ w p)
    (hp : p.Prime) (ha : 0 < a) (ham : a ≤ M) (hd : p ∣ a) :
    min 1 (w p * a.factorization p) ≤ siteWeight Y K M w a p + if p ≤ Y then (K : ℝ)⁻¹ else 0 := by
  have hv := hp.factorization_pos_of_dvd ha.ne' hd
  have hvE := Nat.le_log_of_pow_le hp.one_lt ((Nat.le_of_dvd ha (Nat.ordProj_dvd _ _)).trans ham)
  have hg := lastCut_code (bucketCode_mono (Y := Y) (K := K) hw) hv hvE
  change bucketCode Y K p w (siteExponent Y K M w p a) = bucketCode Y K p w (a.factorization p) at hg
  unfold bucketCode at hg
  by_cases h : p ≤ Y
  · simp only [ite_eq_left h] at hg ⊢
    have hnn := mul_nonneg (Nat.cast_nonneg K) (siteWeight_nonneg (Y := Y) (K := K) (M := M) (a := a) hw)
    have h1 := Nat.floor_le hnn
    have h2 := Nat.lt_floor_add_one ((K : ℝ) * min 1 (w p * a.factorization p))
    change ⌊(K : ℝ) * siteWeight Y K M w a p⌋₊ = _ at hg
    rw [← hg] at h2
    have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
    apply (le_of_mul_le_mul_left (a := (K : ℝ)) _ hk)
    rw [mul_add, mul_inv_cancel₀ hk.ne']
    linarith
  · simp only [ite_eq_right h, add_zero] at hg ⊢
    exact le_of_eq (by rw [siteWeight,hg])

end ErdosSuranyi708
