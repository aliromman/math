module

public import conjectures.GallianRusinDice.Statement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import conjectures.GallianRusin.RootProducts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace GallianRusinDice
open GallianRusin Polynomial Finset
open scoped BigOperators

private theorem sign_parity (f : ℤ[X]) : ∃ H : ℤ[X], f.comp (-X)=f+2*H := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨A,hA⟩ := hp
    obtain ⟨B,hB⟩ := hq
    exact ⟨A+B,by rw [add_comp,hA,hB]; ring⟩
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    rcases Nat.even_or_odd n with h|h
    · exact ⟨0,by simp [h.neg_pow]⟩
    · exact ⟨-(C a*X^n),by simp [h.neg_pow]; ring⟩

/-- Every cyclotomic multiplicity in a die with an odd number of faces is at most log₂(m). -/
theorem odd_multiplicity_bound {m d e : ℕ} {P : ℤ[X]} (odd : Odd m) (dpos : 0<d)
    (dm : d∣m) (game : SolutionDie m P) (divides : cyclotomic d ℤ ^ e ∣ P) : 2^e≤m := by
  classical
  let f := cyclotomic d ℤ
  let φ := Int.castRingHom ℂ
  let roots := (f.map φ).roots
  obtain ⟨D,hD⟩ := divides
  obtain ⟨H,hH⟩ := sign_parity f
  let B := H^e*D.comp (-X)
  have rootspec (z : ℂ) (hz : z∈roots) : IsPrimitiveRoot z d := by
    have : NeZero (d : ℂ) := ⟨by exact_mod_cast dpos.ne'⟩
    have hmap : f.map φ=cyclotomic d ℂ := map_cyclotomic_int d ℂ
    exact isRoot_cyclotomic_iff.mp ((mem_roots (cyclotomic.monic d ℂ).ne_zero).mp (hmap ▸ hz))
  have zero (z : ℂ) (hz : z∈roots) : evalC f z=0 := by
    change f.eval₂ φ z=0
    rw [eval₂_eq_eval_map]
    exact (mem_roots ((cyclotomic.monic d ℤ).map φ).ne_zero).mp hz
  have value (z : ℂ) (hz : z∈roots) : evalC P (-z) = (2:ℂ)^e*evalC B z := by
    have he := congrArg (fun T : ℤ[X] ↦ evalC T z) hH
    simp [evalC,eval₂_comp] at he
    change evalC f (-z) = evalC f z + 2*evalC H z at he
    rw [zero z hz,zero_add] at he
    change P=f^e*D at hD
    rw [hD]
    simp [B,evalC,eval₂_comp,eval₂_pow] at he ⊢
    rw [he,mul_pow]
    ring
  have away (z : ℂ) (hz : z∈roots) : evalC P (-z) ≠ 0 := by
    obtain ⟨_,other,_,_,eq⟩ := game
    have zm := (rootspec z hz).pow_eq_one
    have zn : z^m=1 := by obtain ⟨w,rfl⟩ := dm; rw [pow_mul,zm,one_pow]
    have neg : (-z)^m=(-1:ℂ) := by rw [odd.neg_pow,zn]
    have std : evalC (standard m) (-z)≠0 := by
      intro hz
      have g := geom_sum_mul (-z) m
      change eval₂ φ (-z) _=0 at hz
      have st : (∑ i ∈ range m,(-z)^i)=0 := by simpa [standard,eval₂_finsetSum,eval₂_pow] using hz
      rw [st,neg] at g
      norm_num at g
    intro bad
    have eq' := congrArg (fun T : ℤ[X] ↦ evalC T (-z)) eq
    apply pow_ne_zero (other.length+1) std
    simpa [evalC,eval₂_pow,show P.eval₂ (Int.castRingHom ℂ) (-z)=0 from bad] using eq'.symm
  have live (z : ℂ) (hz : z∈roots) : evalC B z≠0 := by
    intro z0
    exact away z hz (by rw [value z hz,z0,mul_zero])
  have low := one_le_normProduct (cyclotomic.monic d ℤ) live
  by_contra! small
  have point (z : ℂ) (hz : z∈roots) : ‖evalC B z‖≤(m:ℝ)/2^e := by
    have bound := die_bound game.1 (z := -z) (by rw [norm_neg,(rootspec z hz).norm'_eq_one dpos.ne'])
    rw [value z hz,norm_mul,norm_pow] at bound
    norm_num at bound
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have upper : (roots.map (fun z ↦ ‖evalC B z‖)).prod≤((m:ℝ)/2^e)^roots.card := by
    apply (Multiset.prod_map_le_prod_map₀ (fun z ↦ ‖evalC B z‖) (fun _ ↦ (m:ℝ)/2^e)
      (fun _ _ ↦ norm_nonneg _) point).trans_eq
    simp
  have pos : 0<roots.card := by
    change 0<(f.map φ).roots.card
    rw [←(IsAlgClosed.splits _).natDegree_eq_card_roots,(cyclotomic.monic d ℤ).natDegree_map φ]
    simpa only [f,natDegree_cyclotomic] using Nat.totient_pos.mpr dpos
  have ratio : (m:ℝ)/2^e<1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast small)
  have strict := pow_lt_one₀ (a := (m:ℝ)/2^e) (by positivity) ratio pos.ne'
  linarith

end GallianRusinDice
