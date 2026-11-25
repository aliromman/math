module

public import conjectures.AscoliDihedralDominance.Uniform

@[expose] public section
namespace AscoliDihedral
open Finset

private theorem decay (n : ℕ) (hn : 128 ≤ n) : (2*(n:ℚ))^4 * (7/9:ℚ)^n ≤ 1 := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (128:ℚ)≤n := by exact_mod_cast hn
    have h₁ : (2*((n:ℚ)+1))^4 ≤ ((129/128:ℚ)*(2*n))^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0≤(7/9:ℚ)^n*(7/9) by positivity)
    push_cast
    rw [pow_succ (7/9:ℚ)]
    refine h₂.trans ?_
    rw [mul_pow]
    nlinarith only [ih,show 0≤(2*(n:ℚ))^4*(7/9:ℚ)^n by positivity]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem sharp_single {n : ℕ} (hn : 128≤n) (hN : Fintype.card G=2*n) (g : G)
    (hc : g ∉ Subgroup.center G) :
    (2*(n:ℚ)) * (missingProducts g).card ≤ (3:ℚ)^n := by
  let L := (3:ℚ)^n
  let u := ((missingProducts g).card:ℚ)/L
  have hf := noncentral_fixed_le g hc
  rw [hN] at hf
  have hU : u^4 ≤ (7/9:ℚ)^n := (product_misses_relative hN g).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have h : ((2*(n:ℚ))*u)^4 ≤ (1:ℚ)^4 := by
    rw [mul_pow,one_pow]
    exact (mul_le_mul_of_nonneg_left hU (by positivity)).trans (decay n hn)
  have hh := le_of_pow_le_pow_left₀ (by decide : 4≠0) (by norm_num : 0≤(1:ℚ)) h
  dsimp [u] at hh
  rw [←mul_div_assoc] at hh
  simpa [L] using (div_le_iff₀ (show 0<L by dsimp [L]; positivity)).mp hh

private theorem sharp_pair {n : ℕ} (hn : 128≤n) (hN : Fintype.card G=2*n) {g h : G}
    (hg : g∈involutions G) (hh : h∈involutions G) (he : g≠h) :
    (2*(n:ℚ))^2 * ((missingQuotients g∩missingQuotients h).card:ℚ) ≤ (3:ℚ)^n := by
  let L := (3:ℚ)^n
  let u := ((missingQuotients g∩missingQuotients h).card:ℚ)/L
  obtain ⟨g₀,g₂⟩ := (mem_filter.mp hg).2
  obtain ⟨h₀,h₂⟩ := (mem_filter.mp hh).2
  have hbound := two_missing_fourth g₀ h₀ g₂ h₂ he
  rw [hN] at hbound
  have hU : u^4 ≤ (7/9:ℚ)^(2*n) := by
    apply relative_fourth (F := 0) (by omega)
    simpa using hbound
  have h : ((2*(n:ℚ))^2*u)^4 ≤ (1:ℚ)^4 := by
    rw [mul_pow,one_pow]
    refine (mul_le_mul_of_nonneg_left hU (by positivity)).trans ?_
    calc
      _ = ((2*(n:ℚ))^4*(7/9:ℚ)^n)^2 := by rw [show 2*n=n*2 by omega,pow_mul]; ring
      _ ≤ 1^2 := by gcongr; exact decay n hn
      _ = _ := one_pow _
  have H := le_of_pow_le_pow_left₀ (by decide : 4≠0) (by norm_num : 0≤(1:ℚ)) h
  dsimp [u] at H
  rw [←mul_div_assoc] at H
  simpa [L] using (div_le_iff₀ (show 0<L by dsimp [L]; positivity)).mp H

private theorem indicator_sum :
    (univ.filter (fun A : Finset G => 0<witnesses A)).card +
      (univ.filter (fun A : Finset G => (products A).card < (quotients A).card)).card ≤
      (∑ A : Finset G, productMiss A) +
      (univ.filter (fun A : Finset G => (quotients A).card < (products A).card)).card ∧
    (univ.filter (fun A : Finset G => (products A).card < (quotients A).card)).card ≤
      ∑ A : Finset G, productMiss A := by
  have H (A : Finset G) :
      (if 0<witnesses A then 1 else 0)+(if (products A).card < (quotients A).card then 1 else 0)
          ≤ productMiss A+(if (quotients A).card < (products A).card then 1 else 0) ∧
      (if (products A).card < (quotients A).card then 1 else 0) ≤ productMiss A := by
    have hw := witnesses_le A
    unfold productMiss quotientMiss at *
    have hp := card_le_univ (products A)
    have hq := card_le_univ (quotients A)
    split_ifs <;> omega
  constructor
  · simpa only [sum_add_distrib,sum_boole,Nat.cast_id] using sum_le_sum (fun A _ => (H A).1)
  · simpa only [sum_boole,Nat.cast_id] using sum_le_sum (fun A _ => (H A).2)

private theorem quantitative_general {n : ℕ} (hn : 128≤n) (hN : Fintype.card G = 2*n)
    (hcard : (involutions G).card+1 = n + Nat.card (Subgroup.center G))
    (hz : 2*Nat.card (Subgroup.center G) ≤ n) :
    (3*n-4) * (univ.filter (fun A : Finset G => (products A).card < (quotients A).card)).card ≤
    (n+2) * (univ.filter (fun A : Finset G => (quotients A).card < (products A).card)).card := by
  classical
  let T := involutions G
  let C : Finset G := univ.filter fun g => g∈Subgroup.center G
  let t := (T.card:ℚ)
  let z := (C.card:ℚ)
  let N := 2*(n:ℚ)
  let L := (3:ℚ)^n
  let W := ((univ.filter fun A : Finset G => 0<witnesses A).card:ℚ)
  let P := ∑ A : Finset G, (productMiss A:ℚ)
  let d := ∑ A : Finset G, (witnesses A:ℚ)^2
  have eC : C.card = Nat.card (Subgroup.center G) := by rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hnn : (128:ℚ)≤n := by exact_mod_cast hn
  have en : 0<N := by dsimp [N]; linarith
  have eL : 0<L := by dsimp [L]; positivity
  have tnon : 0≤t := Nat.cast_nonneg _
  have et : t≤N := by dsimp [t,T,N]; exact_mod_cast ((card_le_univ (involutions G)).trans_eq hN)
  have te : t+1 = (n:ℚ)+z := by dsimp [t,T,z]; rw [eC]; exact_mod_cast hcard
  have ze : 2*z≤(n:ℚ) := by dsimp [z]; rw [eC]; exact_mod_cast hz
  have F : (∑ A : Finset G, (witnesses A:ℚ)) = t*L := by
    rw [←Nat.cast_sum,sum_witnesses,Nat.cast_sum]
    dsimp [t,L,T]
    rw [sum_congr rfl (fun g hg => congrArg (fun i : ℕ => (i:ℚ)) (miss_involution hN hg))]
    simp
  have single : P ≤ (z+1)*L := by
    dsimp [P]
    rw [←Nat.cast_sum,sum_productMiss,Nat.cast_sum]
    calc
      _ ≤ ∑ g : G, ((if g∈C then L else 0)+L/N) := by
        apply sum_le_sum
        intro g _
        by_cases hc : g∈Subgroup.center G
        · have hc' : g∈C := by simpa [C] using hc
          have h := product_misses_bound hN (by omega) g
          simp only [hc,ite_true,mul_one] at h
          simp only [hc',ite_true]
          exact h.trans (le_add_of_nonneg_right (div_nonneg eL.le en.le))
        · have hc' : g∉C := by simpa [C] using hc
          simp only [hc',ite_false,zero_add]
          apply (le_div_iff₀ en).mpr
          rw [mul_comm]
          exact sharp_single hn hN g hc
      _ = _ := by
        simp [sum_add_distrib,hN,nsmul_eq_mul]
        change z*L + N*(L/N) = _
        field_simp
  have double : d≤(t+1)*L := by
    have de : d = ∑ g∈T,∑ h∈T,((missingQuotients g ∩ missingQuotients h).card:ℚ) := by
      dsimp [d,T]
      exact_mod_cast (square_witnesses (G := G))
    rw [de]
    have row (g : G) (hg : g∈T) : (∑ h∈T,((missingQuotients g∩missingQuotients h).card:ℚ)) ≤
        L+t*(L/N^2) := by
      calc
        _ ≤ ∑ h∈T, ((if h=g then L else 0)+L/N^2) := by
          apply sum_le_sum
          intro h hh
          by_cases he : h=g
          · subst h
            simp only [ite_true,inter_self,miss_involution hN hg,Nat.cast_pow,Nat.cast_ofNat]
            exact le_add_of_nonneg_right (div_nonneg eL.le (sq_nonneg _))
          · simp only [he,ite_false,zero_add]
            apply (le_div_iff₀ (sq_pos_of_pos en)).mpr
            rw [mul_comm]
            exact sharp_pair hn hN hg hh (Ne.symm he)
        _ = _ := by simp [sum_add_distrib,hg,t]
    calc
      _ ≤ ∑ _g∈T,(L+t*(L/N^2)) := sum_le_sum row
      _ = t*L + t^2*(L/N^2) := by simp [t]; ring
      _ ≤ t*L + N^2*(L/N^2) := by gcongr
      _ = (t+1)*L := by field_simp
  have CS : (t*L)^2 ≤ W*d := by
    rw [←F]
    dsimp [W,d]
    exact_mod_cast (cauchy_card (univ : Finset (Finset G)) witnesses)
  have witnessed : (t-1)*L ≤ W := by
    apply (mul_le_mul_iff_left₀ (show 0<(t+1)*L by positivity)).mp
    calc
      _ ≤ (t*L)^2 := by nlinarith [sq_nonneg L]
      _ ≤ W*d := CS
      _ ≤ W*((t+1)*L) := mul_le_mul_of_nonneg_left double (Nat.cast_nonneg _)
  let loss := ((univ.filter fun A : Finset G => (products A).card < (quotients A).card).card:ℚ)
  let win := ((univ.filter fun A : Finset G => (quotients A).card < (products A).card).card:ℚ)
  have si : W+loss≤P+win := by dsimp [W,loss,P,win]; exact_mod_cast (indicator_sum (G:=G)).1
  have ne : loss≤P := by dsimp [loss,P]; exact_mod_cast (indicator_sum (G:=G)).2
  have hdiff : ((n:ℚ)-3)*L≤win-loss := by
    have h := congrArg (fun a : ℚ => a*L) te
    nlinarith only [h,witnessed,si,single]
  have hneg : 2*loss≤((n:ℚ)+2)*L := by nlinarith only [ne,single,mul_le_mul_of_nonneg_right ze eL.le]
  have n3 : 0≤(n:ℚ)-3 := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hdiff (show 0≤(n:ℚ)+2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hneg n3
  have comp : ((3*(n:ℚ))-4)*loss≤((n:ℚ)+2)*win := by nlinarith only [h₁,h₂]
  dsimp [loss,win] at comp
  have he : ((3*n-4:ℕ):ℚ) = 3*(n:ℚ)-4 := by
    rw [Nat.cast_sub (show 4≤3*n by omega)]; norm_cast
  rw [←he] at comp
  exact_mod_cast comp

/-- At base order n at least 128, product-dominant subsets outnumber quotient-dominant
subsets by a factor of at least three minus ten divided by n plus two. -/
theorem quantitative (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ht : ∃ h : H, 3 ≤ addOrderOf h) (hn : 128≤Fintype.card H) :
    let n := Fintype.card H
    (3*n-4) * (univ.filter (fun A : Finset (Dih H) => (products A).card < (quotients A).card)).card ≤
    (n+2) * (univ.filter (fun A : Finset (Dih H) => (quotients A).card < (products A).card)).card := by
  have hm := Dih.exists_moved ht
  have hC := Nat.card_congr (Dih.centerEquiv hm)
  apply quantitative_general hn (Dih.card H)
  · rw [hC]; exact Dih.involutions_card
  · rw [hC]; exact Dih.twoTorsion_bound hm

/-- info: 'AscoliDihedral.quantitative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quantitative

end AscoliDihedral
