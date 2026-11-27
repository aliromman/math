module

public import conjectures.LarsonPowerMap.Scores
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
open Finset
namespace LarsonPowerMap

def except (n k : ℕ) : ℕ := ((lengths n).erase k).lcm id

theorem factor_except {n k : ℕ} (hk : k∈lengths n) :
    Monoid.exponent (Sn n) = Nat.lcm k (except n k) := by
  rw [exp_eq_lcm]
  conv_lhs => rw [← insert_erase hk]
  rw [Finset.lcm_insert]
  rfl

theorem except_pos (n k : ℕ) : 0<except n k := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro j hj
  have := (mem_Icc.mp (mem_of_mem_erase hj)).1
  change j≠0
  omega

private theorem prime_coprime {n p : ℕ} (hp : Nat.Prime p) (long : n<2*p) :
    p.Coprime (except n p) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro dvd
  have pr := hp.prime
  obtain ⟨j,hj,pj⟩ := pr.exists_mem_finset_dvd (dvd.trans (((lengths n).erase p).lcm_dvd_prod id))
  have ne := ne_of_mem_erase hj
  obtain ⟨lo,hi⟩ := mem_Icc.mp (mem_of_mem_erase hj)
  change p ∣ j at pj
  obtain ⟨t,rfl⟩ := pj
  rcases t with _|t
  · simp at lo
  · rcases t with _|t
    · simp at ne
    · nlinarith [Nat.zero_le t,hp.pos]

theorem long_prime {n : ℕ} (hn : 3≤n) :
    ∃ p, p.Prime ∧ 3≤p ∧ p≤n ∧ n<2*p := by
  by_cases e : n=3
  · exact ⟨3,by decide,le_rfl,by omega,by omega⟩
  obtain ⟨p,hp,big,small⟩ := Nat.exists_prime_lt_and_le_two_mul (n/2) (by omega)
  exact ⟨p,hp,by omega,by omega,by omega⟩

/-- Invert the p-cycles while fixing every other cycle length. -/
theorem prime_choice {n p : ℕ} (hp : p.Prime) (odd : 3≤p) (up : p≤n) (long : n<2*p) :
    ∃ a, 2≤a ∧ a<Monoid.exponent (Sn n) ∧ bad n a={p} ∧ orderOf (a : ZMod p)=2 := by
  let c := prime_coprime hp long
  let a : ℕ := Nat.chineseRemainder c (p-1) 1
  have ap : a ≡ p-1 [MOD p] := (Nat.chineseRemainder c (p-1) 1).property.1
  have ar : a ≡ 1 [MOD except n p] := (Nat.chineseRemainder c (p-1) 1).property.2
  have hmod : a%p=p-1 := by
    change a%p=(p-1)%p at ap
    rwa [Nat.mod_eq_of_lt (by omega : p-1<p)] at ap
  have ne : ¬ a ≡ 1 [MOD p] := by
    change a%p ≠ 1%p
    rw [hmod,Nat.mod_eq_of_lt (by omega : 1<p)]
    omega
  have low : 2≤a := by
    by_contra! small
    rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  have hm : p∈lengths n := mem_Icc.mpr ⟨by omega,up⟩
  have bound := Nat.chineseRemainder_lt_mul c (p-1) 1 hp.ne_zero (except_pos n p).ne'
  refine ⟨a,low,?_,?_,?_⟩
  · simpa [a,factor_except hm,c.lcm_eq_mul] using bound
  · ext j
    simp only [bad,mem_filter,mem_singleton]
    constructor
    · rintro ⟨hj,hn⟩
      by_contra neq
      exact hn (ar.of_dvd (dvd_lcm (f:=id) (mem_erase.mpr ⟨neq,hj⟩)))
    · rintro rfl; exact ⟨hm,ne⟩
  · have neg : (a : ZMod p) = -1 := by
      have h := (ZMod.natCast_eq_natCast_iff a (p-1) p).mpr ap
      simpa [Nat.cast_sub (by omega : 1≤p)] using h
    apply (orderOf_eq_iff (by decide : 0<2)).mpr
    refine ⟨by rw [neg]; ring,fun t ht hpos ht' => ?_⟩
    have e : t=1 := by omega
    rw [e,pow_one] at ht'
    exact ne ((ZMod.natCast_eq_natCast_iff a 1 p).mp (by simpa using ht'))

theorem strict_reference {n : ℕ} (hn : 3≤n) :
    ∃ a k, 2≤a ∧ a<Monoid.exponent (Sn n) ∧ bad n a={k} ∧
      n.factorial < N n a+(n-1).factorial := by
  obtain ⟨p,hp,odd,up,long⟩ := long_prime hn
  obtain ⟨a,lo,bound,sing,ord⟩ := prime_choice hp odd up long
  refine ⟨a,p,lo,bound,sing,?_⟩
  have e := score_single (by omega : 1≤a) sing
  rw [loss,ord] at e
  have fac : n.factorial=n*(n-1).factorial := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp [Nat.factorial_succ]
  have fr : (n.factorial : ℚ)=n*(n-1).factorial := by exact_mod_cast fac
  have g : (n:ℚ)<2*p := by exact_mod_cast long
  have ordp : 0<(p:ℚ) := by exact_mod_cast hp.pos
  have pos : 0<((n-1).factorial:ℚ) := by positivity
  have tgt : (n.factorial:ℚ) < N n a+((n-1).factorial : ℚ) := by
    rw [e,fr]
    norm_num
    field_simp
    nlinarith [mul_lt_mul_of_pos_right g pos]
  exact_mod_cast tgt

end LarsonPowerMap
