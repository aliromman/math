module

public import conjectures.ErdosSuranyi708.HistoricalPrimes
public import conjectures.ErdosSuranyi708.HistoricalWindow
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Finset.Sym
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The asymptotic lower bound of Erdős and Surányi

The original inputs are all unordered products of two primes in a short interval.
Products across two disjoint prime sets yield examples of every input size. -/

@[expose] public section
namespace ErdosSuranyi708
open Finset Nat

private theorem demand_le {A B : Finset ℕ} (S : Finset ℕ) (hA : ∀ a∈A, a ≠ 0)
    (hB : ∀ b∈B, b ≠ 0) (hc : Covers A B) :
    (∑a∈A, ∑p∈S, a.factorization p) ≤ ∑b∈B, ∑p∈S, b.factorization p := by
  calc
    _ = ∑p∈S, ∑a∈A, a.factorization p := sum_comm
    _ ≤ ∑p∈S, ∑b∈B, b.factorization p := by
      apply sum_le_sum
      intro p _
      rw [← factorization_prod_apply hA, ← factorization_prod_apply hB]
      exact (factorization_le_iff_dvd (prod_ne_zero_iff.mpr hA) (prod_ne_zero_iff.mpr hB)).mpr hc p
    _ = _ := sum_comm

private theorem prime_product_bounds {a p q : ℕ} {S : Finset ℕ}
    (hS : ∀ r∈S, r.Prime ∧ a≤r ∧ 8*r≤9*a) (hp : p∈S) (hq : q∈S) :
    2≤p*q ∧ 64*(p*q)≤81*a^2 ∧ (∑i∈S,(p*q).factorization i)=2 := by
  obtain ⟨hp',_,hup⟩ := hS p hp
  obtain ⟨hq',_,huq⟩ := hS q hq
  refine ⟨by nlinarith [Nat.mul_le_mul hp'.two_le hq'.two_le], by nlinarith [Nat.mul_le_mul hup huq], ?_⟩
  simp [factorization_mul hp'.ne_zero hq'.ne_zero, hp'.factorization, hq'.factorization,
    Finsupp.single_apply, sum_add_distrib, hp, hq]

private theorem total_pair_factors {A S : Finset ℕ}
    (h : ∀z∈A, (∑p∈S,z.factorization p)=2) :
    (∑z∈A, ∑p∈S,z.factorization p) = 2*A.card := by
  rw [sum_congr rfl h]
  simp [mul_comm]

private theorem prime_pair_card (P : Finset ℕ) (hP : ∀p∈P, p.Prime) :
    (P.sym2.image Sym2.mul).card = P.card*(P.card+1)/2 := by
  have hinj : Set.InjOn (Sym2.mul : Sym2 ℕ → ℕ) (P.sym2 : Set (Sym2 ℕ)) := by
    intro u hu v hv he
    obtain ⟨⟨p,q⟩,rfl⟩ := Sym2.mk_surjective u
    obtain ⟨⟨r,s⟩,rfl⟩ := Sym2.mk_surjective v
    obtain ⟨hp,_⟩ := Finset.mk_mem_sym2_iff.mp hu
    obtain ⟨hr,hs⟩ := Finset.mk_mem_sym2_iff.mp hv
    change p*q = r*s at he
    apply Sym2.eq_iff.mpr
    rcases (hP p hp).dvd_mul.mp (he ▸ dvd_mul_right p q) with hd | hd
    · obtain rfl := (prime_dvd_prime_iff_eq (hP p hp) (hP r hr)).mp hd
      exact Or.inl ⟨rfl,Nat.eq_of_mul_eq_mul_left (hP p hp).pos he⟩
    · obtain rfl := (prime_dvd_prime_iff_eq (hP p hp) (hP s hs)).mp hd
      rw [mul_comm r p] at he
      exact Or.inr ⟨rfl,Nat.eq_of_mul_eq_mul_left (hP p hp).pos he⟩
  rw [Finset.card_image_of_injOn hinj,card_sym2,Nat.choose_two_right,Nat.add_sub_cancel,mul_comm]

/-- Erdős and Surányi, §9. All unordered products of two of the chosen primes,
including the squares, give the triangular input size and the finite lower bound. -/
theorem historical_triangular (l : ℕ) (hl : 0<l) :
    ∃ (a : ℕ) (P : Finset ℕ), 8≤a ∧ P.card=l ∧
      (∀ p∈P, p.Prime ∧ a≤p ∧ 8*p≤9*a) ∧
      ∃ (A : Finset ℕ) (hA : A.Nonempty), A=P.sym2.image Sym2.mul ∧
        A.card=l*(l+1)/2 ∧ (∀ z∈A, 2≤z) ∧
        ∃ x>0, ∀ B ⊆ window x (A.max' hA), Covers A B → l*(l-1)+1 ≤ B.card := by
  obtain ⟨a,P,ha,hc,hP⟩ := prime_cluster l
  let A := P.sym2.image Sym2.mul
  have hne : P.Nonempty := card_pos.mp (hc ▸ hl)
  have hA : A.Nonempty := hne.sym2.image Sym2.mul
  have hcard : A.card = l*(l+1)/2 :=
    (prime_pair_card P (fun p hp => (hP p hp).1)).trans (by rw [hc])
  have hentry (z : ℕ) (hz : z∈A) :
      2≤z ∧ 64*z≤81*a^2 ∧ (∑p∈P,z.factorization p)=2 := by
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    obtain ⟨⟨p,q⟩,rfl⟩ := Sym2.mk_surjective u
    obtain ⟨hp,hq⟩ := Finset.mk_mem_sym2_iff.mp hu
    exact prime_product_bounds hP hp hq
  obtain ⟨x,hx,hbound⟩ := lower_window_sharp P a (A.max' hA) ha hP (hentry _ (A.max'_mem hA)).2.1
  refine ⟨a,P,ha,hc,hP,A,hA,rfl,hcard,fun z hz => (hentry z hz).1,x,hx,?_⟩
  intro B hB hcov
  have H := (demand_le P (fun z hz => by have := (hentry z hz).1; omega)
    (fun z hz => by have := (mem_Ioc.mp (hB hz)).1; omega) hcov).trans (hbound B hB)
  rw [total_pair_factors (fun z hz => (hentry z hz).2.2), hcard, hc,
    mul_comm 2, Nat.div_mul_cancel (Nat.two_dvd_mul_add_one l)] at H
  have he : l*(l+1) = l*(l-1)+2*l := by
    conv_lhs => rw [show l+1=(l-1)+2 by omega, mul_add, mul_comm l 2]
  omega

/-- For every positive input size, some interval requires at least
`2n - 4(⌊√n⌋ + 1)` selections. -/
theorem historical_finite (n : ℕ) (hn : 0<n) :
    ∃ A : Finset ℕ, ∃ hA : A.Nonempty, A.card=n ∧ (∀ a∈A, 2≤a) ∧
      ∃ x : ℕ, ∀ B ⊆ window x (A.max' hA), Covers A B → 2*n≤B.card+4*(n.sqrt+1) := by
  classical
  let m := n.sqrt+1
  obtain ⟨a,S,ha,hs,hS⟩ := prime_cluster (2*m)
  obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq (show m≤S.card by omega)
  let Q := S\P
  have hQc : Q.card=m := by
    dsimp [Q]
    rw [card_sdiff_of_subset hP,hs,hPc]
    omega
  let D := (P ×ˢ Q).image (fun u : ℕ×ℕ => u.1*u.2)
  have hmem {p q : ℕ} (hp:p∈P) (hq:q∈Q) : p ≠ q :=
    fun he => (mem_sdiff.mp hq).2 (he ▸ hp)
  have hcard : D.card=m*m := by
    dsimp [D]
    rw [Finset.card_image_of_injOn, card_product,hPc,hQc]
    rintro ⟨p,q⟩ hu ⟨r,s⟩ hv he
    obtain ⟨hp,hq⟩ := mem_product.mp hu
    obtain ⟨hr,hs'⟩ := mem_product.mp hv
    change p*q=r*s at he
    have hp' := (hS p (hP hp)).1
    have hr' := (hS r (hP hr)).1
    have hs'' := (hS s (mem_sdiff.mp hs').1).1
    have hd : p∣r*s := he ▸ dvd_mul_right p q
    have hpr : p=r := (hp'.dvd_mul.mp hd).elim ((prime_dvd_prime_iff_eq hp' hr').mp)
      (fun hh => False.elim (hmem hp hs' ((prime_dvd_prime_iff_eq hp' hs'').mp hh)))
    subst r
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hp'.pos he)
  obtain ⟨A,hsub,hAc⟩ := exists_subset_card_eq (show n≤D.card by rw [hcard]; exact (Nat.lt_succ_sqrt n).le)
  have hA := card_pos.mp (hAc ▸ hn)
  have hentry (z : ℕ) (hz : z∈A) : 2≤z ∧ 64*z≤81*a^2 ∧ (∑p∈S,z.factorization p)=2 := by
    obtain ⟨⟨p,q⟩,hu,rfl⟩ := mem_image.mp (hsub hz)
    obtain ⟨hp,hq⟩ := mem_product.mp hu
    exact prime_product_bounds hS (hP hp) (mem_sdiff.mp hq).1
  obtain ⟨x,hx⟩ := lower_window S a (A.max' hA) ha hS (hentry _ (A.max'_mem hA)).2.1
  refine ⟨A,hA,hAc,fun z hz => (hentry z hz).1,x,?_⟩
  intro B hB hc
  have H := (demand_le S (fun z hz => by have := (hentry z hz).1; omega)
    (fun z hz => by have := (mem_Ioc.mp (hB hz)).1; omega) hc).trans (hx B hB)
  rw [total_pair_factors (fun z hz => (hentry z hz).2.2), hAc, hs] at H
  dsimp only [m] at H
  omega

/-- The lower bound holds at every sufficiently large cardinality.
Erdős and Surányi proved this bound in 1959, §9, p. 44. -/
theorem historical_lower (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n ≥ N,
    ∃ A : Finset ℕ, ∃ hA : A.Nonempty, A.card=n ∧ (∀ a∈A, 2≤a) ∧
      ∃ x : ℕ, ∀ B ⊆ window x (A.max' hA), Covers A B → (2-ε)*n < B.card := by
  obtain ⟨K,hK⟩ := exists_nat_gt (8/ε)
  refine ⟨(K+1)^2,?_⟩
  intro n hn
  have hq := Nat.le_sqrt'.mpr hn
  have hq1 : 1≤n.sqrt := by omega
  have hn0 : 0<n := by nlinarith
  have hqR : 0<(n.sqrt:ℝ) := by exact_mod_cast (by omega : 0<n.sqrt)
  have hqR1 : 1≤(n.sqrt:ℝ) := by exact_mod_cast hq1
  have hqK : (K:ℝ)≤n.sqrt := by exact_mod_cast (by omega : K≤n.sqrt)
  have hεq : 8 < ε*(n.sqrt:ℝ) := by
    have := (div_lt_iff₀ hε).mp hK
    nlinarith [mul_le_mul_of_nonneg_left hqK hε.le]
  have hsq : (n.sqrt:ℝ)^2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hsmall : 4*((n.sqrt:ℝ)+1)<ε*n := by
    nlinarith only [mul_lt_mul_of_pos_right hεq hqR,mul_le_mul_of_nonneg_left hsq hε.le,hqR1]
  obtain ⟨A,hA,hc,hpos,x,hx⟩ := historical_finite n hn0
  refine ⟨A,hA,hc,hpos,x,?_⟩
  intro B hB hcover
  have hh := hx B hB hcover
  have hR : 2*(n:ℝ) ≤ B.card+4*((n.sqrt:ℝ)+1) := by exact_mod_cast hh
  linarith

end ErdosSuranyi708
