module

public import conjectures.CFPLogDensity.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace CFPLogDensity
open Finset
open scoped Classical

private theorem gain {r : ℕ} {C g f T U A B : ℝ}
    (hg : 1 < g) (hT : 0 < T) (htu : T ≤ U)
    (curve : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → f*z < 1-C+C*z^r/g)
    (advance : A+U-f*T ≤ B) (cap : B ≤ C*U) :
    g*A < B*(T/U)^r := by
  have hu := hT.trans_le htu
  have gp : 0 < g := by linarith
  let z := T/U
  let a := B/U
  have hz : 0 ≤ z := (div_pos hT hu).le
  have hz' : z ≤ 1 := (div_le_one hu).mpr htu
  have ha : a ≤ C := (div_le_iff₀ hu).mpr cap
  have shrink : z^r/g ≤ 1 := (div_le_one gp).mpr ((pow_le_one₀ hz hz').trans hg.le)
  have line : f*z < 1-a+a*(z^r/g) := by
    have h := curve z hz hz'
    rw [mul_div_assoc] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr shrink)]
  have ratio : A/U ≤ a-1+f*z := by
    dsimp only [a,z]
    field_simp [hu.ne']
    linarith
  have small : A/U < a*z^r/g := by
    rw [mul_div_assoc]
    linarith
  have h := (lt_div_iff₀ gp).mp small
  dsimp only [a,z] at h
  calc
    g*A = ((A/U)*g)*U := by field_simp
    _ < ((B/U)*(T/U)^r)*U := mul_lt_mul_of_pos_right h hu
    _ = B*(T/U)^r := by field_simp

private noncomputable def credit (S : Set ℕ) (q t : ℕ) : ℝ := 1 + ((finished S q t).card : ℝ)

private theorem credit_pos (S : Set ℕ) (q t : ℕ) : 0 < credit S q t := by
  unfold credit
  positivity

/-- Bounded color densities are incompatible with a strict deficit below the curve. -/
theorem schedule_impossible {r p q N : ℕ} {C g : ℝ} (S : Fin r → Set ℕ)
    (hq : 0 < q) (hpq : p ≤ q) (hC : C < 1) (hg : 1 < g)
    (curve : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (p:ℝ)/q*z < 1-C+C*z^r/g)
    (cap : ∀ n ≥ N, ∀ i, 1+(((range n).filter (· ∈ S i)).card:ℝ) ≤ C*n)
    (cover : ∀ t ≥ N, ∃ i, ∀ k, p*t ≤ k → k < q*(t+1) → k ∈ S i) : False := by
  let clock (t : ℕ) : ℝ := q*(t:ℝ)
  let P (t : ℕ) := (∏ i, credit (S i) q t)/(clock t)^r
  have qpos : 0 < (q:ℝ) := by exact_mod_cast hq
  have clock_pos {t : ℕ} (ht : 0 < t) : 0 < clock t := mul_pos qpos (by exact_mod_cast ht)
  have credit_cap {t : ℕ} (ht : N ≤ t) (i : Fin r) : credit (S i) q t ≤ C*(clock t) := by
    have tq : t ≤ q*t := by simpa using Nat.mul_le_mul_right t (show 1 ≤ q from hq)
    have h := cap (q*t) (ht.trans tq) i
    have sub : ((finished (S i) q t).card:ℝ) ≤ (((range (q*t)).filter (· ∈ S i)).card:ℝ) := by
      exact_mod_cast finished_bound (S i) q t
    dsimp only [credit,clock]
    push_cast at h
    linarith
  have bounded {t : ℕ} (ht : N < t) : P t ≤ 1 := by
    have hp := clock_pos (Nat.zero_lt_of_lt ht)
    apply (div_le_one (pow_pos hp _)).mpr
    calc
      _ ≤ ∏ _i : Fin r, clock t := prod_le_prod₀ (fun i _ => (credit_pos ..).le)
        (fun i _ => (credit_cap ht.le i).trans (by nlinarith [mul_le_mul_of_nonneg_right hC.le hp.le]))
      _ = _ := by simp
  have grows (t : ℕ) (ht : N < t) : ∃ u > t, g*P t < P u := by
    obtain ⟨u,htu,i,added⟩ := extend_finished_interval S hq hC cap (cover t ht.le)
    have hp := clock_pos (Nat.zero_lt_of_lt ht)
    have hup := clock_pos (Nat.zero_lt_of_lt htu)
    have clocks : clock t ≤ clock u := mul_le_mul_of_nonneg_left (by exact_mod_cast htu.le) qpos.le
    have lo : p*t ≤ q*u := Nat.mul_le_mul hpq htu.le
    have addReal : ((finished (S i) q t).card:ℝ) + (q*u-p*t : ℕ) ≤ (finished (S i) q u).card := by
      exact_mod_cast added
    push_cast [Nat.cast_sub lo] at addReal
    have inc : credit (S i) q t+clock u-((p:ℝ)/q)*clock t ≤ credit (S i) q u := by
      have cancel : ((p:ℝ)/q)*clock t = (p:ℝ)*t := by dsimp only [clock]; field_simp
      rw [cancel]
      dsimp only [credit,clock]
      linarith
    have one := gain hg hp clocks curve inc (credit_cap (ht.trans htu).le i)
    let rest := (univ : Finset (Fin r)).erase i
    have others : (∏ j ∈ rest, credit (S j) q t) ≤ ∏ j ∈ rest, credit (S j) q u := by
      apply prod_le_prod₀ (fun j _ => (credit_pos ..).le)
      intro j _
      dsimp only [credit]
      have mono : ((finished (S j) q t).card:ℝ) ≤ ((finished (S j) q u).card:ℝ) := by
        exact_mod_cast card_le_card (finished_mono (S j) q htu.le)
      linarith
    have all : g*(∏ j,credit (S j) q t) < (clock t/clock u)^r*(∏ j,credit (S j) q u) := by
      rw [←mul_prod_erase univ (fun j => credit (S j) q t) (mem_univ i),
        ←mul_prod_erase univ (fun j => credit (S j) q u) (mem_univ i)]
      calc
        _ = (g*credit (S i) q t)*(∏ j ∈ rest,credit (S j) q t) := by ring
        _ < (credit (S i) q u*(clock t/clock u)^r)*(∏ j ∈ rest,credit (S j) q t) :=
            mul_lt_mul_of_pos_right one (prod_pos fun _ _ => credit_pos ..)
        _ ≤ (credit (S i) q u*(clock t/clock u)^r)*(∏ j ∈ rest,credit (S j) q u) :=
            mul_le_mul_of_nonneg_left others (mul_nonneg (credit_pos ..).le (pow_nonneg (div_pos hp hup).le _))
        _ = _ := by ring
    refine ⟨u,htu,?_⟩
    dsimp only [P]
    rw [←mul_div_assoc,div_lt_div_iff₀ (pow_pos hp _) (pow_pos hup _)]
    rw [div_pow,div_mul_eq_mul_div,lt_div_iff₀ (pow_pos hup _)] at all
    linarith only [all]
  have base : 0 < P (N+1) := div_pos (prod_pos fun _ _ => credit_pos ..) (pow_pos (clock_pos (by omega)) _)
  have reach (k : ℕ) : ∃ t > N, g^k * P (N+1) ≤ P t := by
    induction k with
    | zero => exact ⟨N+1,by omega,by simp⟩
    | succ k ih =>
      obtain ⟨t,ht,h⟩ := ih
      obtain ⟨u,hu,h'⟩ := grows t ht
      refine ⟨u,ht.trans hu,?_⟩
      rw [pow_succ']
      linarith only [mul_le_mul_of_nonneg_left h (by linarith : 0≤g),h'.le]
  obtain ⟨k,h⟩ := pow_unbounded_of_one_lt (1/P (N+1)) hg
  obtain ⟨t,ht,hk⟩ := reach k
  linarith [(div_lt_iff₀ base).mp h,bounded ht]
end CFPLogDensity
