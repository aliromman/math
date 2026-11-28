module

public import conjectures.ErdosSuranyi708.Statement
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The interval in the lower-bound construction of Erdős and Surányi -/

@[expose] public section
namespace ErdosSuranyi708
open Finset Nat

private theorem window_geometry (a R M p q : ℕ) (ha : 8 ≤ a) (hR : R=a^2-2*a)
    (hM : 64*M ≤ 81*a^2) (hp : a≤p) (hu : 8*p≤9*a) (hq : a≤q) :
    M≤2*R ∧ R+p < p^2 ∧ R < p*q ∧ R ≤ p+p^2 := by
  have he : R+2*a=a^2 := hR ▸ Nat.sub_add_cancel (by nlinarith [Nat.mul_le_mul_left a ha])
  have hpp := Nat.mul_le_mul hp hp
  have hpq := Nat.mul_le_mul hp hq
  constructor
  · nlinarith [Nat.mul_le_mul_left a ha]
  · exact ⟨by nlinarith [hpp], by nlinarith [hpq],by nlinarith [hpp]⟩

private theorem same_of_modEq {a b m : ℕ} (h : a ≡ b [MOD m]) (hab : a < b+m)
    (hba : b < a+m) : a=b := Nat.le_antisymm (h.le_of_lt_add hab) (h.symm.le_of_lt_add hba)

/-- In a centered interval, only its center can use two different labels. For
one prime label the unique possible repeated factor lies one prime below the center. -/
private theorem centered_window (P : Finset ℕ) (a M : ℕ) (ha : 8≤a)
    (hP : ∀p∈P, p.Prime ∧ a≤p ∧ 8*p≤9*a) (hM : 64*M ≤ 81*a^2) :
    ∃ x c : ℕ, ∀ b ∈ window x M,
      (∀p∈P, b.factorization p ≤ (if p∣b then 1 else 0) + (if b+p=c then 1 else 0)) ∧
      (b≠c → (P.filter (· ∣ b)).card ≤ 1) := by
  let R := a^2-2*a
  let m (p : ℕ) := p^3
  let u (p : ℕ) := p+p^2-R
  have hm (p : ℕ) (hp:p∈P) : m p ≠ 0 := pow_ne_zero _ (hP p hp).1.ne_zero
  have hco : Set.Pairwise (P:Set ℕ) (Function.onFun Nat.Coprime m) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (hP p hp).1 (hP q hq).1).mpr hpq).pow _ _
  obtain ⟨x,hx⟩ := Nat.chineseRemainderOfFinset u m P hm hco
  let c := x+R
  have hc (p : ℕ) (hp:p∈P) : c ≡ p+p^2 [MOD p^3] := by
    have hg := window_geometry a R M p p ha rfl hM (hP p hp).2.1 (hP p hp).2.2 (hP p hp).2.1
    simpa [c,u,m,Nat.sub_add_cancel hg.2.2.2] using (hx p hp).add_right R
  have hpc (p : ℕ) (hp:p∈P) : p∣c :=
    ((hc p hp).dvd_iff (dvd_pow_self p (by decide : 3≠0))).mpr (dvd_add (dvd_refl _) (dvd_pow_self _ (by decide : 2≠0)))
  refine ⟨x,c,?_⟩
  intro b hb
  obtain ⟨hxl,hxr⟩ := mem_Ioc.mp hb
  have hb0 : b≠0 := by omega
  constructor
  · intro p hp
    obtain ⟨hpP,hpl,hpu⟩ := hP p hp
    obtain ⟨hrM,hrp,_,_⟩ := window_geometry a R M p p ha rfl hM hpl hpu hpl
    have hsq (hs : p^2∣b) : b+p=c := by
      have hb' : b+p ≡ p [MOD p^2] := by simpa using (Nat.modEq_zero_iff_dvd.mpr hs).add_right p
      have hc' : c ≡ p [MOD p^2] := (hc p hp).of_dvd (pow_dvd_pow p (by decide : 2≤3)) |>.trans (by simp)
      apply same_of_modEq (hb'.trans hc'.symm) <;> dsimp [c] <;> omega
    by_cases hd : p∣b
    · rw [ite_eq_left hd]
      by_cases he : b+p=c
      · rw [ite_eq_left he]
        have hb' : b ≡ p^2 [MOD p^3] := (Nat.ModEq.add_right_cancel' p (by simpa [he,add_comm] using hc p hp))
        have h3 : ¬p^3∣b := by
          intro h
          have hh := Nat.le_of_dvd (pow_pos hpP.pos 2) ((hb'.dvd_iff (dvd_refl _)).mp h)
          exact (Nat.pow_lt_pow_right hpP.one_lt (by decide : 2<3)).not_ge hh
        rw [hpP.pow_dvd_iff_le_factorization hb0] at h3
        omega
      · rw [ite_eq_right he]
        have h2 : ¬p^2∣b := fun h => he (hsq h)
        rw [hpP.pow_dvd_iff_le_factorization hb0] at h2
        omega
    · have h := hpP.dvd_iff_one_le_factorization hb0
      rw [ite_eq_right hd]
      omega
  · intro hbc
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpP,hpb⟩ := mem_filter.mp hp
    obtain ⟨hqP,hqb⟩ := mem_filter.mp hq
    by_contra hpq
    have hcop := (Nat.coprime_primes (hP p hpP).1 (hP q hqP).1).mpr hpq
    have hb' := Nat.modEq_zero_iff_dvd.mpr (hcop.mul_dvd_of_dvd_of_dvd hpb hqb)
    have hc' := Nat.modEq_zero_iff_dvd.mpr (hcop.mul_dvd_of_dvd_of_dvd (hpc p hpP) (hpc q hqP))
    obtain ⟨hrM,_,hrpq,_⟩ := window_geometry a R M p q ha rfl hM (hP p hpP).2.1 (hP p hpP).2.2 (hP q hqP).2.1
    apply hbc
    apply same_of_modEq (hb'.trans hc'.symm) <;> dsimp [c] <;> omega

/-- At most two extra prime factors per prime can supplement one factor per selection. -/
theorem lower_window (P : Finset ℕ) (a M : ℕ) (ha : 8≤a)
    (hP : ∀p∈P, p.Prime ∧ a≤p ∧ 8*p≤9*a) (hM : 64*M ≤ 81*a^2) :
    ∃ x : ℕ, ∀ B ⊆ window x M, (∑ b ∈ B, ∑ p ∈ P, b.factorization p) ≤ B.card+2*P.card := by
  classical
  obtain ⟨x,c,hc⟩ := centered_window P a M ha hP hM
  refine ⟨x,?_⟩
  intro B hB
  have hpoint (b : ℕ) (hb:b∈B) : (∑p∈P, b.factorization p) ≤
      (1+(if b=c then P.card else 0)) + ∑p∈P, (if b=c-p ∧ b+p=c then 1 else 0) := by
    have H := hc b (hB hb)
    refine (sum_le_sum H.1).trans ?_
    rw [sum_add_distrib, sum_boole]
    simp only [Nat.cast_id]
    have hsum : (∑p∈P,if b+p=c then (1:ℕ) else 0) = ∑p∈P,if b=c-p ∧ b+p=c then 1 else 0 := by
      apply sum_congr rfl
      intro p _
      split_ifs <;> omega
    rw [hsum]
    by_cases he : b=c
    · rw [ite_eq_left he]
      have hs := card_le_card (filter_subset (·∣b) P)
      omega
    · rw [ite_eq_right he]
      have hs := H.2 he
      omega
  have extras : (∑ b∈B, ∑p∈P, if b=c-p ∧ b+p=c then 1 else 0) ≤ P.card := by
    rw [sum_comm]
    calc
      _ ≤ ∑p∈P, (1:ℕ) := by
        apply sum_le_sum
        intro p _
        calc
          _ ≤ ∑b∈B, if b=c-p then 1 else 0 := by
            apply sum_le_sum; intro b _; split_ifs <;> omega
          _ ≤ 1 := by simp; split <;> simp
      _ = _ := by simp
  have hcen : (∑b∈B, if b=c then P.card else 0) ≤ P.card := by simp; split <;> simp
  have he := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul,mul_one,Nat.cast_id] at he
  omega

end ErdosSuranyi708
