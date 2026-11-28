module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # A short multiplicative interval containing many primes -/

@[expose] public section
namespace ErdosSuranyi708
open Finset Nat Real

private theorem many_primes (k t : ℕ) (ht : 16*(k+16) ≤ t) :
    (t^2+1)*k+8*t^2 < (primesLE (t^4)).card := by
  have htr : (16:ℝ)*(k+16) ≤ t := by exact_mod_cast ht
  have ht1 : (1:ℝ)<t := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h := Chebyshev.pi_ge_of_four_le (n:=t^4) (by
    have ht4 : 4 ≤ t := by omega
    exact ht4.trans (Nat.le_self_pow (by decide) t))
  have hlog : 0 < log ((t:ℝ)^4) := log_pos (one_lt_pow₀ ht1 (by decide))
  push_cast at h
  have hp := (div_le_iff₀ hlog).mp h
  rw [Real.log_pow] at hp
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hl
  have hscale := mul_le_mul_of_nonneg_left (Real.log_le_self (Nat.cast_nonneg t))
    (show (0:ℝ) ≤ ((t^4).primeCounting:ℝ)*4 by positivity)
  norm_num only [Nat.cast_ofNat] at hp
  have hchain : (t:ℝ)^4*(1/2) ≤ ((t^4).primeCounting:ℝ)*4*t :=
    (mul_le_mul_of_nonneg_left hl (show 0 ≤ (t:ℝ)^4 by positivity)).trans
      (hp.trans (by simpa only [mul_assoc] using hscale))
  have hpi : (t:ℝ)^3 ≤ 8*((t^4).primeCounting:ℝ) := by
    apply le_of_mul_le_mul_left (a := (t:ℝ)) _ (by linarith)
    nlinarith only [hchain]
  rw [primesLE_card_eq_primeCounting]
  have hkt : (k:ℝ) ≤ t^2 := by nlinarith [sq_nonneg ((t:ℝ)-1),Nat.cast_nonneg (α:=ℝ) k]
  have hgap := mul_le_mul_of_nonneg_right htr (sq_nonneg (t:ℝ))
  have hfin : ((t:ℝ)^2+1)*k+8*t^2 < ((t^4).primeCounting:ℝ) := by nlinarith [sq_nonneg (t:ℝ)]
  exact_mod_cast hfin

/-- There are arbitrarily many primes inside a common interval `[a,9a/8]`. -/
theorem prime_cluster (k : ℕ) : ∃ a : ℕ, ∃ P : Finset ℕ, 8 ≤ a ∧ P.card=k ∧
    ∀ p∈P, p.Prime ∧ a≤p ∧ 8*p≤9*a := by
  let t := 16*(k+16)
  let w := t^2
  let all := primesLE (t^4)
  let T := all \ range (8*w)
  have hw : 0 < w := by dsimp [w,t]; positivity
  have htotal : (w+1)*k+8*w < all.card := many_primes k t le_rfl
  have hfilter := card_sdiff_add_card_inter all (range (8*w))
  have hsmall := card_le_card (inter_subset_right (s₁:=all) (s₂:=range (8*w)))
  rw [card_range] at hsmall
  have hm (p : ℕ) (hp : p∈T) : p/w ∈ range (w+1) := by
    have he := le_of_mem_primesLE (mem_sdiff.mp hp).1
    have he' : p ≤ w*w := by simpa [w,pow_succ,pow_two,mul_assoc] using he
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    nlinarith
  obtain ⟨b,_,hb⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hm (n:=k) (by
    rw [card_range]; dsimp only [T]; omega)
  obtain ⟨P,hP,hcard⟩ := exists_subset_card_eq (Nat.le_of_lt hb)
  obtain ⟨q,hq⟩ := card_pos.mp (Nat.zero_lt_of_lt hb)
  obtain ⟨hqT,hbq⟩ := mem_filter.mp hq
  have hql : 8*w ≤ q := by have := (mem_sdiff.mp hqT).2; simpa using this
  have hbl : 8 ≤ b := hbq ▸ (Nat.le_div_iff_mul_le hw).mpr hql
  refine ⟨b*w,P,by nlinarith,hcard,?_⟩
  intro p hp
  obtain ⟨hpT,hpb⟩ := mem_filter.mp (hP hp)
  have hlow : b*w ≤ p := hpb ▸ Nat.div_mul_le_self p w
  have hu : p < (b+1)*w := (Nat.div_lt_iff_lt_mul hw).mp (by omega)
  exact ⟨prime_of_mem_primesLE (mem_sdiff.mp hpT).1,hlow,by nlinarith [Nat.mul_le_mul_right w hbl]⟩

end ErdosSuranyi708
