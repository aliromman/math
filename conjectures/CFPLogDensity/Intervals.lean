module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section
namespace CFPLogDensity
open Finset
open scoped Classical

/-- Count positions whose component of the color set has already ended by the next checkpoint. -/
noncomputable def finished (S : Set ℕ) (q t : ℕ) : Finset ℕ :=
  (range (q*t)).filter fun j => j ∈ S ∧ ∃ h, j < h ∧ h < q*(t+1) ∧ h ∉ S

theorem finished_mono (S : Set ℕ) (q : ℕ) {t u : ℕ} (h : t ≤ u) :
    finished S q t ⊆ finished S q u := by
  intro j hj
  obtain ⟨hj,hS,hole,hh,he,hout⟩ := mem_filter.mp hj
  refine mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hj).trans_le (Nat.mul_le_mul_left _ h)),
    hS,hole,hh,he.trans_le ?_,hout⟩
  exact Nat.mul_le_mul_left _ (by omega)

theorem finished_bound (S : Set ℕ) (q t : ℕ) :
    (finished S q t).card ≤ ((range (q*t)).filter (· ∈ S)).card := by
  apply card_le_card
  intro j hj
  exact mem_filter.mpr ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.1⟩

private theorem exists_hole (S : Set ℕ) (N s : ℕ) {C : ℝ} (hC : C < 1)
    (h : ∀ n ≥ N, 1+(((range n).filter (· ∈ S)).card:ℝ) ≤ C*n) :
    ∃ k, s ≤ k ∧ k ∉ S := by
  by_contra! all
  obtain ⟨n,hn⟩ := exists_nat_gt ((s:ℝ)/(1-C)+N+s)
  have pos : 0 < 1-C := by linarith
  have hratio : 0 ≤ (s:ℝ)/(1-C) := by positivity
  have hN : N ≤ n := by exact_mod_cast (show (N:ℝ) ≤ n by linarith [(Nat.cast_nonneg s : 0 ≤ (s:ℝ))])
  have hs : s ≤ n := by exact_mod_cast (show (s:ℝ) ≤ n by linarith [(Nat.cast_nonneg N : 0 ≤ (N:ℝ))])
  have sub : Ico s n ⊆ (range n).filter (· ∈ S) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hj).2,all _ (mem_Ico.mp hj).1⟩
  have card := card_le_card sub
  rw [Nat.card_Ico] at card
  have realcard : (n:ℝ)-s ≤ (((range n).filter (· ∈ S)).card:ℝ) := by
    have hc : ((n-s:ℕ):ℝ) ≤ (((range n).filter (· ∈ S)).card:ℝ) := by exact_mod_cast card
    rwa [Nat.cast_sub hs] at hc
  have big : (s:ℝ)/(1-C) < n := by linarith [(Nat.cast_nonneg N : 0 ≤ (N:ℝ)),(Nat.cast_nonneg s : 0 ≤ (s:ℝ))]
  have := (div_lt_iff₀ pos).mp big
  nlinarith [h n hN]

/-- Extend to the first missing position. Every new position precedes this hole, while every
position counted at the old checkpoint precedes the start of the interval. -/
theorem extend_finished_interval {r p q N t : ℕ} (S : Fin r → Set ℕ) {C : ℝ}
    (hq : 0 < q) (hC : C < 1)
    (cap : ∀ n ≥ N, ∀ i, 1+(((range n).filter (· ∈ S i)).card:ℝ) ≤ C*n)
    (cover : ∃ i, ∀ k, p*t ≤ k → k < q*(t+1) → k ∈ S i) :
    ∃ u > t, ∃ i, (finished (S i) q t).card + (q*u-p*t) ≤ (finished (S i) q u).card := by
  obtain ⟨i,hi⟩ := cover
  have ex := exists_hole (S i) N (p*t) hC (fun n hn => cap n hn i)
  let g := Nat.find ex
  obtain ⟨hstart,hgap⟩ := Nat.find_spec ex
  have full (k : ℕ) (h₀ : p*t ≤ k) (h₁ : k < g) : k ∈ S i := by
    by_contra hn
    exact (Nat.not_le_of_gt h₁) (Nat.find_min' ex ⟨h₀,hn⟩)
  have hg : q*(t+1) ≤ g := by
    by_contra! lt
    exact hgap (hi g hstart lt)
  let u := g/q
  have hu : t+1 ≤ u := (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using hg)
  have hlo : q*u ≤ g := by simpa [u,Nat.mul_comm] using Nat.div_mul_le_self g q
  have hhi : g < q*(u+1) := by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul hq).mp (by dsimp [u]; omega)
  refine ⟨u,hu,i,?_⟩
  let B := Ico (p*t) (q*u)
  have hsub : B ⊆ finished (S i) q u := by
    intro k hk
    obtain ⟨lk,uk⟩ := mem_Ico.mp hk
    exact mem_filter.mpr ⟨mem_range.mpr uk,full k lk (uk.trans_le hlo),g,uk.trans_le hlo,hhi,hgap⟩
  have hd : Disjoint (finished (S i) q t) B := by
    apply disjoint_left.mpr
    intro k hk hB
    obtain ⟨_,_,h,hkh,hend,hole⟩ := mem_filter.mp hk
    exact hole (hi h ((mem_Ico.mp hB).1.trans hkh.le) hend)
  have count := card_le_card (union_subset (finished_mono (S i) q (Nat.le_of_lt hu)) hsub)
  rwa [card_union_of_disjoint hd,show B.card = q*u-p*t from Nat.card_Ico _ _] at count
end CFPLogDensity
