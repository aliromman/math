module

public import conjectures.GallianRusinGame.Statement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace GallianRusinGame
open Polynomial Finset
open scoped BigOperators

private abbrev evalC (P : ℤ[X]) (z : ℂ) := P.eval₂ (Int.castRingHom ℂ) z

private theorem die_bound {P : ℤ[X]} {m} (h : Die m P) {z : ℂ} (unit : ‖z‖=1) :
    ‖evalC P z‖≤m := by
  have total : (m:ℝ)=((P.eval 1:ℤ):ℝ) := by exact_mod_cast h.2.symm
  rw [total,eval_eq_sum_range]
  change ‖P.eval₂ _ z‖≤_
  rw [eval₂_eq_sum_range]
  apply (norm_sum_le ..).trans
  push_cast
  apply sum_le_sum
  intro i _
  simp [norm_pow,unit,Complex.norm_intCast,abs_of_nonneg (show (0:ℝ)≤P.coeff i by exact_mod_cast h.1 i)]

private noncomputable abbrev normProduct (f H : ℤ[X]) : ℝ :=
  (((f.map (Int.castRingHom ℂ)).roots).map (fun z ↦ ‖evalC H z‖)).prod

private theorem normProduct_eq (f H : ℤ[X]) (mf : f.Monic) :
    normProduct f H=|(f.resultant H : ℝ)| := by
  let φ := Int.castRingHom ℂ
  have mf' := mf.map φ
  have eq : ((f.resultant H : ℤ):ℂ) = ((f.map φ).roots.map (evalC H)).prod := by
    change φ (f.resultant H) = _
    rw [←resultant_map_map f H _ _ φ,←mf.natDegree_map φ,
      resultant_eq_prod_eval _ _ _ (natDegree_map_le ..) (IsAlgClosed.splits _),mf'.leadingCoeff]
    simp [eval_map,φ,evalC]
  rw [←Complex.norm_intCast,eq]
  simp [normProduct,φ]

private theorem one_le_normProduct {f H : ℤ[X]} (mf : f.Monic)
    (nonzero : ∀ z∈(f.map (Int.castRingHom ℂ)).roots,evalC H z≠0) : 1≤normProduct f H := by
  have hn : normProduct f H ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro bad
    obtain ⟨z,hz,e⟩ := Multiset.mem_map.mp bad
    exact nonzero z hz (norm_eq_zero.mp e)
  rw [normProduct_eq _ _ mf] at hn ⊢
  have nz : f.resultant H≠0 := fun h ↦ hn (by simp [h])
  exact_mod_cast Int.one_le_abs nz

private theorem normProduct_swap (f g : ℤ[X]) (mf : f.Monic) (mg : g.Monic) :
    normProduct f g=normProduct g f := by
  rw [normProduct_eq _ _ mf,normProduct_eq _ _ mg,resultant_comm]
  simp [abs_mul]

private theorem primitive_of_mem {n} (np : 0<n) {z : ℂ}
    (hz : z∈((cyclotomic n ℤ).map (Int.castRingHom ℂ)).roots) : IsPrimitiveRoot z n := by
  have : NeZero (n:ℂ) := ⟨by exact_mod_cast np.ne'⟩
  rw [map_cyclotomic_int] at hz
  exact isRoot_cyclotomic_iff.mp ((mem_roots (cyclotomic.monic n ℂ).ne_zero).mp hz)

private theorem root_iff {n} (np : 0<n) {z : ℂ} :
    evalC (cyclotomic n ℤ) z=0 ↔ IsPrimitiveRoot z n := by
  have : NeZero (n:ℂ) := ⟨by exact_mod_cast np.ne'⟩
  change (cyclotomic n ℤ).eval₂ _ z=0 ↔ _
  rw [eval₂_eq_eval_map,map_cyclotomic_int]
  exact isRoot_cyclotomic_iff

private theorem card_roots_int {f : ℤ[X]} (mf : f.Monic) :
    (f.map (Int.castRingHom ℂ)).roots.card=f.natDegree := by
  rw [←(IsAlgClosed.splits _).natDegree_eq_card_roots,mf.natDegree_map]

private theorem prime_resultant {d p : ℕ} (hd : 0<d) (hp : Nat.Prime p) (cop : ¬p∣d) :
    (p:ℝ)^d.totient≤normProduct (cyclotomic (d*p) ℤ) (cyclotomic d ℤ) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let f := cyclotomic d ℤ
  let g := cyclotomic (d*p) ℤ
  have reduction : (g-f^(p-1)).map (Int.castRingHom (ZMod p))=0 := by
    simp only [Polynomial.map_sub,Polynomial.map_pow,f,g,map_cyclotomic_int,
      cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) cop,sub_self]
  have div : C (p:ℤ) ∣ g-f^(p-1) := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro i
    have coeff := congrArg (fun T : (ZMod p)[X] ↦ T.coeff i) reduction
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    change (Int.castRingHom (ZMod p)) ((g-f^(p-1)).coeff i)=0
    rw [←coeff_map]
    exact coeff
  obtain ⟨H,eq⟩ := div
  have val (z : ℂ) (hz : z∈(f.map (Int.castRingHom ℂ)).roots) : evalC g z=(p:ℂ)*evalC H z := by
    have hf := (root_iff hd).mpr (primitive_of_mem hd hz)
    have h := congrArg (fun T : ℤ[X] ↦ evalC T z) eq
    simpa [evalC,eval₂_pow,f,zero_pow (show p-1≠0 by have := hp.one_lt; omega),
      show (cyclotomic d ℤ).eval₂ (Int.castRingHom ℂ) z=0 from hf] using h
  have good (z : ℂ) (hz : z∈(f.map (Int.castRingHom ℂ)).roots) : evalC H z≠0 := by
    intro zero
    have gg : evalC g z=0 := by rw [val z hz,zero,mul_zero]
    have h₁ := (root_iff (Nat.mul_pos hd hp.pos)).mp gg
    have e := (primitive_of_mem hd hz).unique h₁
    nlinarith [hp.one_lt]
  have low := one_le_normProduct (cyclotomic.monic d ℤ) good
  rw [normProduct_swap _ _ (cyclotomic.monic _ _) (cyclotomic.monic _ _)]
  change _ ≤ normProduct f g
  have prod : normProduct f g=(p:ℝ)^d.totient*normProduct f H := by
    unfold normProduct
    have pt (z : ℂ) (hz : z∈(f.map (Int.castRingHom ℂ)).roots) : ‖evalC g z‖=(p:ℝ)*‖evalC H z‖ := by
      rw [val z hz,norm_mul,Complex.norm_natCast]
    rw [Multiset.map_congr rfl pt,Multiset.prod_map_mul]
    have cnt := card_roots_int (cyclotomic.monic d ℤ)
    rw [natDegree_cyclotomic] at cnt
    change (f.map (Int.castRingHom ℂ)).roots.card=d.totient at cnt
    simp only [Multiset.map_const',Multiset.prod_replicate,cnt]
  rw [prod]
  nlinarith [mul_nonneg (show (0:ℝ)≤p^d.totient by positivity) (sub_nonneg.mpr low)]

/-- An auxiliary prime gives a bound for every multiplicity, including even numbers of faces. -/
theorem multiplicity_bound {m d e p : ℕ} {P : ℤ[X]} (hp : Nat.Prime p) (cop : ¬p∣m)
    (hd : 0<d) (dm : d∣m) (game : SolutionDie m P) (divides : cyclotomic d ℤ^e ∣ P) :
    p^e≤m^(p-1) := by
  classical
  let f := cyclotomic d ℤ
  let g := cyclotomic (d*p) ℤ
  let roots := (g.map (Int.castRingHom ℂ)).roots
  have gp := Nat.mul_pos hd hp.pos
  obtain ⟨k,hk,dy,others,_,_,hgame⟩ := game
  obtain ⟨D,hD⟩ := divides
  have no (z : ℂ) (hz : z∈roots) : evalC P z≠0 := by
    have prim := primitive_of_mem gp hz
    have zn : z^m≠1 := by
      intro one
      exact cop (dvd_trans (dvd_mul_left p d) (prim.dvd_of_pow_eq_one m one))
    have std : evalC (standard m) z≠0 := by
      intro hz
      have h : (∑ i ∈ range m,z^i)=0 := by simpa [evalC,standard,eval₂_finsetSum,eval₂_pow] using hz
      have s := geom_sum_mul z m
      rw [h,zero_mul] at s
      exact zn (by linear_combination -s)
    intro bad
    have eq' := congrArg (fun T : ℤ[X] ↦ evalC T z) hgame
    apply pow_ne_zero k std
    simpa [evalC,eval₂_pow,show P.eval₂ (Int.castRingHom ℂ) z=0 from bad] using eq'.symm
  have dgood (z : ℂ) (hz : z∈roots) : evalC D z≠0 := by
    intro zero
    exact no z hz (by rw [hD]; simp [evalC,show D.eval₂ (Int.castRingHom ℂ) z=0 from zero])
  have dz := one_le_normProduct (cyclotomic.monic (d*p) ℤ) dgood
  have prod : normProduct g P=normProduct g f^e*normProduct g D := by
    unfold normProduct
    rw [hD]
    simp [evalC,eval₂_pow,Multiset.prod_map_mul,Multiset.prod_map_pow,f]
  have top : normProduct g P≤ (m:ℝ)^(d*p).totient := by
    change (roots.map (fun z ↦ ‖evalC P z‖)).prod≤_
    apply (Multiset.prod_map_le_prod_map₀ _ (fun _ ↦ (m:ℝ)) (fun _ _ ↦ norm_nonneg _)
      (fun z hz ↦ die_bound dy ((primitive_of_mem gp hz).norm'_eq_one gp.ne'))).trans_eq
    have cnt := card_roots_int (cyclotomic.monic (d*p) ℤ)
    rw [natDegree_cyclotomic] at cnt
    change roots.card=(d*p).totient at cnt
    simp only [Multiset.map_const',Multiset.prod_replicate]
    exact congrArg (fun j : ℕ ↦ (m:ℝ)^j) cnt
  have cr := prime_resultant hd hp (fun pd ↦ cop (dvd_trans pd dm))
  change (p:ℝ)^d.totient≤normProduct g f at cr
  have fg : 0≤normProduct g f := (by positivity : (0:ℝ)≤p^d.totient) |>.trans cr
  have lower : ((p:ℝ)^d.totient)^e≤normProduct g P := by
    rw [prod]
    exact (pow_le_pow_left₀ (by positivity) cr e).trans (le_mul_of_one_le_right (pow_nonneg fg _) dz)
  have final := lower.trans top
  have cp : d.Coprime p := (hp.coprime_iff_not_dvd.mpr (fun pd ↦ cop (dvd_trans pd dm))).symm
  rw [Nat.totient_mul cp,Nat.totient_prime hp,Nat.mul_comm d.totient (p-1),pow_mul,
    ←pow_mul,mul_comm d.totient e,pow_mul] at final
  exact_mod_cast (le_of_pow_le_pow_left₀ (Nat.totient_pos.mpr hd).ne' (by positivity) final)

end GallianRusinGame
