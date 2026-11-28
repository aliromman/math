module

public import conjectures.ErdosSuranyi708.HistoricalLower
public import conjectures.ErdosSuranyi708.Proof
import Mathlib.Tactic.Linarith

/-! # The least sufficient number of selections -/

@[expose] public section
namespace ErdosSuranyi708
open Finset Filter

/-- A budget works for every input of size `n` and every integer interval. -/
def Sufficient (n k : ℕ) : Prop := ∀ (A : Finset ℕ) (hA : A.Nonempty), A.card=n →
  (∀ a∈A, 2≤a) → ∀ x : ℤ, ∃ B ⊆ Ioc x (x+(A.max' hA : ℤ)),
    B.card≤k ∧ (∏a∈A,(a:ℤ)) ∣ ∏b∈B,b

theorem sufficient_exists (n : ℕ) : ∃ k, Sufficient n k := by
  let K := (2*n+1)^3
  have hK : 1≤K := by dsimp [K]; exact Nat.one_le_pow _ _ (by omega)
  refine ⟨K,?_⟩
  intro A hA hcard hp x
  let M := A.max' hA
  have ha (a : ℕ) (h : a∈A) : 0<a ∧ a≤M := ⟨by have := hp a h; omega,A.le_max' a h⟩
  obtain ⟨B,hB,hc,hd⟩ := lift_signed (A:=A) (x:=x) (M:=M) (C:=(K:ℝ)) (by exact_mod_cast hK) (by
    intro y
    by_cases hlarge : (2*A.card)^3≤M
    · obtain ⟨S,hs,hd,hc⟩ := large_height (x:=y) ha hlarge
      have hbound : 2*n ≤ K := (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
      refine ⟨S,hs,hd,?_⟩
      exact_mod_cast hc.trans (hcard ▸ hbound)
    · let S := window y M
      refine ⟨S,Subset.rfl,?_,?_⟩
      · apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr (fun a h => (ha a h).1.ne'))
          (prod_ne_zero_iff.mpr (fun b h => by have := (mem_Ioc.mp h).1; omega))).mp
        intro p
        by_cases hpp : p.Prime
        · rw [Nat.factorization_prod_apply (fun a h => (ha a h).1.ne'),
            Nat.factorization_prod_apply (fun b h => by have := (mem_Ioc.mp h).1; omega)]
          exact_mod_cast valuation_transport (x:=y) (fun a h => mem_Ioc.mpr (by simpa using ha a h))
            hpp (fun t => (t:ℝ)) (fun _ _ h => Nat.cast_le.mpr h) (fun _ => Nat.cast_nonneg _)
        · simp [Nat.factorization_eq_zero_of_not_prime _ hpp]
      · have hs : S.card=M := by simp [S,window]
        have hk : (2*A.card)^3≤K := by rw [hcard]; exact Nat.pow_le_pow_left (by omega) _
        exact_mod_cast (show S.card≤K by omega))
  exact ⟨B,hB,by exact_mod_cast hc,hd⟩

/-- The least universal selection budget in Erdős Problem 708. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.find (sufficient_exists n)

theorem isLeast_budget (n : ℕ) : IsLeast {k | Sufficient n k} (g n) := by
  classical
  exact ⟨Nat.find_spec (sufficient_exists n), fun _ h => Nat.find_min' (sufficient_exists n) h⟩

private theorem lower_for_budget {n k : ℕ} (hk : Sufficient n k)
    {A : Finset ℕ} (hA : A.Nonempty) (hn : A.card=n) (ha : ∀ a∈A, 2≤a)
    (x : ℕ) : ∃ B ⊆ window x (A.max' hA), Covers A B ∧ B.card≤k := by
  obtain ⟨S,hS,hc,hd⟩ := hk A hA hn ha (x:ℤ)
  have hs (z : ℤ) (hz : z∈S) : 0≤z := by have := (mem_Ioc.mp (hS hz)).1; omega
  have hinj : Set.InjOn Int.toNat (S:Set ℤ) := by
    intro z hz w hw he
    have hz0 := hs z hz
    have hw0 := hs w hw
    omega
  refine ⟨S.image Int.toNat,?_,?_,Finset.card_image_le.trans hc⟩
  · rintro _ h
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    obtain ⟨hl,hr⟩ := mem_Ioc.mp (hS hz)
    apply mem_Ioc.mpr
    omega
  · apply Int.natCast_dvd_natCast.mp
    simp only [Nat.cast_prod, Finset.prod_image hinj]
    simpa only [Function.comp_apply] using hd.trans (dvd_of_eq (prod_congr rfl
      (fun z hz => (Int.toNat_of_nonneg (hs z hz)).symm)))

/-- The lower construction and the uniform upper bound give the sharp limit. -/
theorem tendsto_g_div : Tendsto (fun n : ℕ => (g n : ℝ)/n) atTop (nhds 2) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hu⟩ := resolution (ε/2) (by linarith)
  obtain ⟨L,hl⟩ := historical_lower (ε/2) (by linarith)
  refine ⟨max 1 (max N L),?_⟩
  intro n hn
  have hn1 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hk : Sufficient n ⌊(2+ε/2)*n⌋₊ := by
    intro A hA he ha x
    obtain ⟨B,hB,hc,hd⟩ := hu A hA (by omega) ha x
    exact ⟨B,hB,Nat.le_floor (by simpa [he] using hc),hd⟩
  have hupper : (g n:ℝ) ≤ (2+ε/2)*n :=
    (Nat.cast_le.mpr ((isLeast_budget n).2 hk)).trans (Nat.floor_le (by positivity))
  obtain ⟨A,hA,hc,ha,x,hx⟩ := hl n (by omega)
  obtain ⟨B,hB,hd,hb⟩ := lower_for_budget (isLeast_budget n).1 hA hc ha x
  have hlower := (hx B hB hd).trans_le (Nat.cast_le.mpr hb : (B.card:ℝ)≤g n)
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (lt_div_iff₀ hn1).mpr hlower
    linarith
  · have := (div_le_iff₀ hn1).mpr hupper
    linarith

end ErdosSuranyi708
