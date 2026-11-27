module

public import conjectures.LarsonPowerMap.Components
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section
open Finset Function Equiv.Perm
namespace LarsonPowerMap

def lengths (n : ℕ) : Finset ℕ := Icc 1 n

def bad (n a : ℕ) : Finset ℕ := (lengths n).filter fun k => ¬a ≡ 1 [MOD k]

theorem length_bound {n k : ℕ} {x : Sn n} (h : k ∈ x.cycleType) : k ∈ lengths n := by
  have le := (le_card_support_of_mem_cycleType h).trans (card_le_univ x.support)
  exact mem_Icc.mpr ⟨by have := two_le_of_mem_cycleType h; omega,by simpa using le⟩

theorem pow_eq_self_iff {n r : ℕ} (x : Sn n) (hr : 1≤r) :
    x^r=x ↔ ∀ j ∈ x.cycleType, r ≡ 1 [MOD j] := by
  have e (k : ℕ) : r ≡ 1 [MOD k] ↔ k ∣ r-1 :=
    ⟨fun h => (Nat.modEq_iff_dvd' hr).mp h.symm,
      fun h => ((Nat.modEq_iff_dvd' hr).mpr h).symm⟩
  calc
    x^r=x ↔ x^r=x^1 := by rw [pow_one]
    _ ↔ r ≡ 1 [MOD orderOf x] := pow_eq_pow_iff_modEq
    _ ↔ _ := by simp only [e,←lcm_cycleType,Multiset.lcm_dvd]

theorem exp_eq_lcm (n : ℕ) : Monoid.exponent (Sn n) = (lengths n).lcm id := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd.mpr
    intro x
    rw [←lcm_cycleType,Multiset.lcm_dvd]
    intro k hk
    exact dvd_lcm (f:=id) (length_bound hk)
  · apply Finset.lcm_dvd
    intro k hk
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    rcases eq_or_lt_of_le lo with rfl|lt
    · exact one_dvd _
    · let _ : NeZero n := ⟨by omega⟩
      let j : Fin n := ⟨k-1,by omega⟩
      have nz : j ≠ 0 := by
        intro eq
        have e := congrArg Fin.val eq
        change k-1=0 at e
        omega
      have hm : k ∈ j.cycleRange.cycleType := by
        rw [Fin.cycleType_cycleRange nz]
        simp [j,show k-1+1=k by omega]
      exact (dvd_of_mem_cycleType hm).trans (Monoid.order_dvd_exponent _)

theorem bad_nonempty {n a : ℕ} (ha : 2≤a) (he : a<Monoid.exponent (Sn n)) :
    (bad n a).Nonempty := by
  by_contra! h
  have dvd : (lengths n).lcm id ∣ a-1 := by
    apply Finset.lcm_dvd
    intro k hk
    have e : a ≡ 1 [MOD k] := by
      by_contra ne
      exact Finset.notMem_empty k (h ▸ mem_filter.mpr ⟨hk,ne⟩)
    exact (Nat.modEq_iff_dvd' (by omega : 1≤a)).mp e.symm
  rw [←exp_eq_lcm] at dvd
  have := Nat.le_of_dvd (by omega : 0<a-1) dvd
  omega

theorem pow_iterate {G : Type*} [Monoid G] (a t : ℕ) (x : G) :
    (fun y : G => y^a)^[t] x = x^(a^t) := by
  induction t with
  | zero => simp
  | succ t ih => rw [iterate_succ_apply',ih,←pow_mul,pow_succ]

theorem minimalPeriod_single {n a k : ℕ} (ha : 1≤a) (only : bad n a={k}) (x : Sn n) :
    minimalPeriod (fun y : Sn n => y^a) x =
      if k ∈ x.cycleType then orderOf (a : ZMod k) else 1 := by
  classical
  have good {j} (hj : j ∈ x.cycleType) (ne : j≠k) : a ≡ 1 [MOD j] := by
    by_contra hn
    have : j ∈ bad n a := mem_filter.mpr ⟨length_bound hj,hn⟩
    simp [only,ne] at this
  split_ifs with h
  · apply Nat.dvd_antisymm
    all_goals
      have all (t : ℕ) : IsPeriodicPt (fun y : Sn n => y^a) t x ↔ (a : ZMod k)^t=1 := by
        change (fun y : Sn n => y^a)^[t] x=x ↔ _
        rw [pow_iterate,pow_eq_self_iff x (Nat.one_le_pow _ _ ha)]
        have equiv : a^t ≡ 1 [MOD k] ↔ (a : ZMod k)^t=1 := by
          simpa only [Nat.cast_pow,Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (a^t) 1 k).symm
        refine ⟨fun hyp => equiv.mp (hyp k h), fun hyp j hj => ?_⟩
        by_cases e : j=k
        · exact e ▸ equiv.mpr hyp
        · simpa using (good hj e).pow t
    · exact isPeriodicPt_iff_minimalPeriod_dvd.mp ((all _).mpr (pow_orderOf_eq_one _))
    · exact orderOf_dvd_of_pow_eq_one ((all _).mp (isPeriodicPt_minimalPeriod _ _))
  · apply minimalPeriod_eq_one_iff_isFixedPt.mpr
    exact (pow_eq_self_iff x ha).mpr (fun j hj => good hj (fun e => h (e ▸ hj)))

end LarsonPowerMap
