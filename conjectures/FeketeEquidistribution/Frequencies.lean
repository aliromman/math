module

public import conjectures.FeketeEquidistribution.Statement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.Ring

public section
namespace FeketeEquidistribution
open Finset Polynomial

private theorem reduced_exponents {n : ℕ} (hn : 1<n) :
    (range n).filter (fun a ↦ a.Coprime n) = unitsTo n := by
  ext a
  simp only [unitsTo,mem_filter,mem_range,mem_Icc]
  constructor
  · rintro ⟨lt,cp⟩
    have nz : a≠0 := by
      rintro rfl
      simp at cp
      omega
    exact ⟨⟨by omega,lt.le⟩,cp⟩
  · rintro ⟨⟨_,le⟩,cp⟩
    have ne : a≠n := by
      rintro rfl
      simp at cp
      omega
    exact ⟨lt_of_le_of_ne le ne,cp⟩

private theorem eval_frequencies {d : ℕ} {z : ℂ} (hd : 0<d) (hz : z^d=1) {n : ℕ} (hn : 1<n) :
    aeval z (fekete n)=∑ s ∈ range d,(residueCount n d s : ℂ)*z^s := by
  rw [fekete,reduced_exponents hn,map_sum]
  simp only [map_pow,aeval_X]
  rw [← sum_fiberwise_of_maps_to (s:=unitsTo n) (t:=range d)
    (fun (i : ℕ) (_ : i ∈ unitsTo n) ↦ mem_range.mpr (Nat.mod_lt i hd)) (fun i ↦ z^i)]
  apply sum_congr rfl
  intro s hs
  have hm := Nat.mod_eq_of_lt (mem_range.mp hs)
  rw [residueCount,hm]
  calc
    ∑ i ∈ (unitsTo n).filter (fun i ↦ i%d=s),z^i =
        ∑ _i ∈ (unitsTo n).filter (fun i ↦ i%d=s),z^s := by
      apply sum_congr rfl
      intro i hi
      have eq := (mem_filter.mp hi).2
      calc z^i = z^(i%d+d*(i/d)) := by rw [Nat.mod_add_div]
           _ = z^s := by rw [pow_add,pow_mul,hz,one_pow,mul_one,eq]
    _ = _ := by simp

private theorem sum_periods (z : ℂ) (t m : ℕ) (w : ℕ → ℂ) :
    ∑ i ∈ range (m*t), w (i%t)*z^i =
    (∑ j ∈ range m,(z^t)^j)*(∑ r ∈ range t,w r*z^r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ,add_mul]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (mem_range.mp hi),pow_add,←pow_mul,Nat.mul_comm t m]
    ring

/-- A frequency vector with a proper period vanishes at primitive roots. -/
theorem factor_of_period {n t m : ℕ} (hn : 1<n) (ht : 0<t) (hm : 1<m)
    (period : ∀ i<m*t, residueCount n (m*t) i = residueCount n (m*t) (i%t)) :
    cyclotomic (m*t) ℤ ∣ fekete n := by
  have hd : 0<m*t := Nat.mul_pos (by omega) ht
  let z := Complex.exp (2 * (Real.pi:ℂ) * Complex.I / (m*t : ℕ))
  have prim : IsPrimitiveRoot z (m*t) := Complex.isPrimitiveRoot_exp _ hd.ne'
  rw [cyclotomic_eq_minpoly prim hd]
  apply minpoly.isIntegrallyClosed_dvd (prim.isIntegral hd)
  rw [eval_frequencies hd prim.pow_eq_one hn]
  calc
    ∑ i ∈ range (m*t), (residueCount n (m*t) i : ℂ)*z^i =
        ∑ i ∈ range (m*t), (residueCount n (m*t) (i%t) : ℂ)*z^i := by
      apply sum_congr rfl
      intro i hi
      rw [period i (mem_range.mp hi)]
    _ = _ := by
      rw [sum_periods z t m (fun r ↦ (residueCount n (m*t) r : ℂ))]
      have nz : z^t≠1 := prim.pow_ne_one_of_pos_of_lt ht.ne' (by nlinarith)
      have prod := geom_sum_mul (z^t) m
      rw [←pow_mul,Nat.mul_comm,prim.pow_eq_one,sub_self] at prod
      rw [(mul_eq_zero.mp prod).resolve_right (sub_ne_zero.mpr nz),zero_mul]

end FeketeEquidistribution
