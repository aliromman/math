module

public import conjectures.AscoliDihedralDominance.Large
public import conjectures.AscoliDihedralDominance.Generalized

@[expose] public section
open Finset
namespace AscoliDihedral
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem miss_involution {n : ℕ} (hN : Fintype.card G = 2*n) {g : G} (hg : g ∈ involutions G) :
    (missingQuotients g).card = 3^n := by
  obtain ⟨hn,hg'⟩ := (mem_filter.mp hg).2
  have he := miss_involution_sq hn hg'
  rw [hN,mul_comm 2 n,pow_mul] at he
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) he

private theorem total_product_bound {n : ℕ} (hN : Fintype.card G = 2*n) (hn : 32 ≤ n) :
    (∑ g : G, ((missingProducts g).card:ℚ)) ≤
      (3:ℚ)^n * (Nat.card (Subgroup.center G) +
        (2*(n:ℚ)-Nat.card (Subgroup.center G))*(17/125)) := by
  classical
  let C : Finset G := univ.filter fun g => g∈Subgroup.center G
  have eC : C.card = Nat.card (Subgroup.center G) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have eCc : (Cᶜ.card:ℚ) = 2*(n:ℚ) - Nat.card (Subgroup.center G) := by
    rw [Finset.card_compl,Nat.cast_sub (card_le_univ _), eC, hN]
    norm_cast
  calc
    _ ≤ ∑ g : G, (3:ℚ)^n * (if g ∈ Subgroup.center G then 1 else 17/125) :=
      sum_le_sum fun g _ => product_misses_bound hN hn g
    _ = (3:ℚ)^n * (∑ g : G, (if g ∈ C then 1 else 17/125)) := by
      rw [mul_sum]; apply sum_congr rfl; intro g _; simp [C]
    _ = _ := by
      congr 1
      rw [←Finset.sum_add_sum_compl C]
      have hc : (∑ g ∈ C, (if g∈C then 1 else 17/125 : ℚ)) = (C.card:ℚ) := by
        calc
          _ = ∑ _g ∈ C, (1:ℚ) := sum_congr rfl (fun g hg => by simp [hg])
          _ = _ := by simp
      have hcc : (∑ g ∈ Cᶜ, (if g∈C then 1 else 17/125 : ℚ)) = (Cᶜ.card:ℚ)*(17/125) := by
        calc
          _ = ∑ _g ∈ Cᶜ, (17/125:ℚ) := sum_congr rfl (fun g hg => by simp [mem_compl.mp hg])
          _ = _ := by simp
      rw [hc,hcc,eCc,eC]

private theorem total_pair_bound {n : ℕ} (hN : Fintype.card G = 2*n) (hn : 32 ≤ n)
    (hT : ((involutions G).card:ℚ) ≤ 3*(n:ℚ)/2) :
    (∑ g ∈ involutions G, ∑ h ∈ involutions G,
        ((missingQuotients g ∩ missingQuotients h).card:ℚ)) ≤
        (involutions G).card * ((3:ℚ)^n * (1+9/10)) := by
  let T := involutions G
  let L := (3:ℚ)^n
  let b := ((9/10:ℚ)*L)/(3*(n:ℚ)/2)
  have d : 0 < 3*(n:ℚ)/2 := by
    have : 0<(n:ℚ) := by exact_mod_cast (by omega : 0<n)
    positivity
  have hb : 0 ≤ b := by dsimp [b,L]; positivity
  have tb : T.card*b ≤ (9/10:ℚ)*L := by
    calc
      _ ≤ (3*(n:ℚ)/2)*b := mul_le_mul_of_nonneg_right hT hb
      _ = _ := by dsimp [b]; field_simp
  have row (g : G) (hg : g∈T) : (∑ h ∈ T, ((missingQuotients g∩missingQuotients h).card:ℚ)) ≤
      L*(1+9/10) := by
    calc
      _ ≤ ∑ h ∈ T, ((if h=g then L else 0) + b) := by
        apply sum_le_sum
        intro h hh
        by_cases he : h=g
        · subst h
          simp only [ite_true,inter_self,miss_involution hN hg,Nat.cast_pow,Nat.cast_ofNat]
          change L ≤ L+b
          linarith
        · obtain ⟨hg₀,hg₂⟩ := (mem_filter.mp hg).2
          obtain ⟨hh₀,hh₂⟩ := (mem_filter.mp hh).2
          have H := pair_misses_bound hN hn hg₀ hh₀ hg₂ hh₂ (Ne.symm he)
          simp only [he,ite_false,zero_add]
          apply (le_div_iff₀ d).mpr
          rwa [mul_comm]
      _ = L + T.card*b := by simp [sum_add_distrib,hg]
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ _g ∈ T, (L*(1+9/10)) := sum_le_sum row
    _ = _ := by simp [T,L]

theorem dominance_large {n : ℕ} (hN : Fintype.card G = 2*n) (hn : 32 ≤ n)
    (hcard : (involutions G).card+1 = n + Nat.card (Subgroup.center G))
    (hz : 2*Nat.card (Subgroup.center G) ≤ n) : ProductDominant G := by
  let T := ((involutions G).card:ℚ)
  let z := (Nat.card (Subgroup.center G):ℚ)
  let L := (3:ℚ)^n
  let U := z+(2*(n:ℚ)-z)*(17/125)
  let V := (1+9/10:ℚ)
  have hT : T+1=(n:ℚ)+z := by dsimp [T,z]; exact_mod_cast hcard
  have hZ : 2*z≤(n:ℚ) := by dsimp [z]; exact_mod_cast hz
  have hnn : (32:ℚ)≤n := by exact_mod_cast hn
  have htn : T ≤ 3*(n:ℚ)/2 := by
    dsimp [T] at *
    linarith
  have htpos : 0 < T := by have : 0≤z := Nat.cast_nonneg _; linarith
  have hLg : 0 < L := by dsimp [L]; positivity
  have hGap : U*V<T := by
    have := large_gap (n:ℚ) z hnn hZ
    dsimp [U,V]; linarith
  have hU := total_product_bound hN hn
  have hV := total_pair_bound hN hn htn
  have hF : (∑ g ∈ involutions G, ((missingQuotients g).card:ℚ)) = T*L := by
    calc
      _ = ∑ _g ∈ involutions G, L := by
        apply sum_congr rfl
        intro g hg
        simp [miss_involution hN hg,L]
      _ = _ := by simp [T]
  apply dominance_from_witnesses
  rw [sum_productMiss,square_witnesses,sum_witnesses]
  have hy : 0 ≤ L*U :=
    (Finset.sum_nonneg (fun g _ => Nat.cast_nonneg (missingProducts g).card)).trans hU
  have h₁ := mul_le_mul hU hV
    (Finset.sum_nonneg (fun g _ => Finset.sum_nonneg fun h _ => Nat.cast_nonneg _)) hy
  have h₂ : (L*U)*(T*(L*V)) < (T*L)^2 := by
    calc
      _ = (U*V)*(T*L^2) := by ring
      _ < T*(T*L^2) := mul_lt_mul_of_pos_right hGap (by positivity)
      _ = _ := by ring
  have h := h₁.trans_lt h₂
  rw [←hF] at h
  exact_mod_cast h

theorem generalized_dihedral_large (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ht : ∃ h : H, 3≤addOrderOf h) (hn : 32≤Fintype.card H) : ProductDominant (Dih H) := by
  have hm := Dih.exists_moved ht
  have hC := Nat.card_congr (Dih.centerEquiv hm)
  apply dominance_large (Dih.card H) hn
  · rw [hC]; exact Dih.involutions_card
  · rw [hC]; exact Dih.twoTorsion_bound hm

end AscoliDihedral
