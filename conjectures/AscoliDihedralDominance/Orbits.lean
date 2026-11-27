module

public import conjectures.AscoliDihedralDominance.Cycles
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Fintype.Pi

@[expose] public section

open Equiv Function Finset

namespace AscoliDihedral

variable {X : Type*} [Fintype X]

abbrev Orbit (p : Perm X) := Quotient (Perm.SameCycle.setoid p)

noncomputable instance orbitFintype (p : Perm X) : Fintype (Orbit p) := Fintype.ofFinite _

noncomputable def period (p : Perm X) (x : X) := minimalPeriod (⇑p) x

theorem period_pos (p : Perm X) (x : X) : 0 < period p x := by
  apply minimalPeriod_pos_of_mem_periodicPts
  rw [injective_iff_periodicPts_eq_univ.mp p.injective]
  exact Set.mem_univ _

noncomputable def orbitPoint (p : Perm X) (q : Orbit p) (i : Fin (period p q.out)) :=
  (⇑p)^[i.val] q.out

omit [Fintype X] in
theorem orbitPoint_next (p : Perm X) (q : Orbit p) (i : Fin (period p q.out)) :
    orbitPoint p q (next i) = p (orbitPoint p q i) := by
  change (⇑p)^[(i.val+1) % minimalPeriod (⇑p) q.out] q.out = _
  rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  rfl

noncomputable def orbitFiberEquiv (p : Perm X) (q : Orbit p) :
    Fin (period p q.out) ≃ {x : X // Quotient.mk (Perm.SameCycle.setoid p) x = q} := by
  let project (x : X) : Orbit p := Quotient.mk _ x
  have hc (i : Fin (period p q.out)) : project (orbitPoint p q i) = q := by
    have h : p.SameCycle q.out (orbitPoint p q i) := by
      simpa only [orbitPoint, ← Equiv.Perm.coe_pow] using
        (show p.SameCycle q.out ((p ^ i.val) q.out) from (Perm.SameCycle.refl p q.out).pow_right)
    exact (Quotient.sound (s := Perm.SameCycle.setoid p) h.symm).trans q.out_eq
  refine Equiv.ofBijective (fun i => ⟨orbitPoint p q i,hc i⟩) ⟨?_,?_⟩
  · intro i j h
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (congrArg Subtype.val h)
  · intro y
    have h : p.SameCycle q.out y.val := Quotient.exact (s := Perm.SameCycle.setoid p)
      (q.out_eq.trans y.property.symm)
    obtain ⟨i,hi⟩ := h.exists_nat_pow_eq
    refine ⟨⟨i % period p q.out, Nat.mod_lt _ (period_pos _ _)⟩, Subtype.ext ?_⟩
    exact iterate_mod_minimalPeriod_eq.trans (by simpa only [Equiv.Perm.coe_pow] using hi)

noncomputable def orbitEquiv (p : Perm X) : (Σ q : Orbit p, Fin (period p q.out)) ≃ X :=
  (Equiv.sigmaCongrRight (orbitFiberEquiv p)).trans (Equiv.sigmaFiberEquiv _)

theorem orbitEquiv_apply (p : Perm X) (q : Orbit p) (i : Fin (period p q.out)) :
    orbitEquiv p ⟨q,i⟩ = orbitPoint p q i := rfl

theorem sum_period (p : Perm X) :
    ∑ q : Orbit p, period p q.out = Fintype.card X := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr (orbitEquiv p)

def coloringOK {α : Type*} (p : α → α) (f : α → Bool) : Prop :=
  ∀ x, (!(f x && f (p x))) = true

noncomputable def colorEquiv (p : Perm X) :
    {f : X → Bool // coloringOK p f} ≃
    ((q : Orbit p) → {g : Fin (period p q.out) → Bool // coloringOK next g}) := by
  let e : (X → Bool) ≃ ((q : Orbit p) → Fin (period p q.out) → Bool) :=
    (Equiv.arrowCongr (orbitEquiv p).symm (Equiv.refl _)).trans (Equiv.piCurry (fun (q : Orbit p) (_ : Fin (period p q.out)) => Bool))
  refine (e.subtypeEquiv (p := coloringOK p)
    (q := fun g => ∀ q, coloringOK next (g q)) ?_).trans Equiv.subtypePiEquivPi
  intro f
  change (∀ x, (!(f x && f (p x))) = true) ↔
    ∀ q i, (!(f (orbitPoint p q i) && f (orbitPoint p q (next i)))) = true
  simp only [orbitPoint_next]
  constructor
  · exact fun h _ _ => h _
  · intro h x
    obtain ⟨⟨q,i⟩,rfl⟩ := (orbitEquiv p).surjective x
    exact h q i

theorem card_coloring_next (k : ℕ) (hk : 0 < k) :
    Nat.card {g : Fin k → Bool // coloringOK next g} = lucas k := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← card_cycle k]
  congr 1
  ext f
  simp [coloringOK]

theorem count_cycle_factors (p : Perm X) :
    Nat.card {f : X → Bool // coloringOK p f} = ∏ q : Orbit p, lucas (period p q.out) := by
  classical
  let (q : Orbit p) : Fintype {g : Fin (period p q.out) → Bool // coloringOK next g} := Fintype.ofFinite _
  rw [Nat.card_congr (colorEquiv p), Nat.card_eq_fintype_card, Fintype.card_pi]
  apply prod_congr rfl
  intro q _
  rw [← Nat.card_eq_fintype_card]
  exact card_coloring_next _ (period_pos _ _)

omit [Fintype X] in
theorem twice_fixed_iff (p : Perm X) (x : X) : p (p x) = x ↔ period p x ∣ 2 := by
  change IsPeriodicPt (⇑p) 2 x ↔ _
  exact isPeriodicPt_iff_minimalPeriod_dvd

theorem orbit_period (p : Perm X) (q : Orbit p) (i : Fin (period p q.out)) :
    period p ((orbitEquiv p) ⟨q,i⟩) = period p q.out := by
  apply minimalPeriod_apply_iterate
  rw [injective_iff_periodicPts_eq_univ.mp p.injective]
  exact Set.mem_univ _

noncomputable def fixedTwice (p : Perm X) : ℕ := by
  classical
  exact (univ.filter fun x => p (p x) = x).card

private theorem fixedTwice_eq (p : Perm X) :
    fixedTwice p = ∑ q : Orbit p, if period p q.out ∣ 2 then period p q.out else 0 := by
  classical
  rw [fixedTwice, card_filter,
    ← (orbitEquiv p).sum_comp (fun x => if p (p x) = x then 1 else 0), Fintype.sum_sigma]
  simp_rw [twice_fixed_iff, orbit_period]
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp_all

/-- Every cycle of length at least three contributes at most seven choices per
four vertices. Cycles of length one or two contribute at most nine. -/
theorem coloring_fourth_bound (p : Perm X) :
    (Nat.card {f : X → Bool // coloringOK p f})^4 ≤
      9^(fixedTwice p) * 7^(Fintype.card X - fixedTwice p) := by
  classical
  let a (q : Orbit p) := if period p q.out ∣ 2 then period p q.out else 0
  let b (q : Orbit p) := if period p q.out ∣ 2 then 0 else period p q.out
  have hab (q : Orbit p) : a q + b q = period p q.out := by simp [a,b]; split <;> simp_all
  have ha : ∑ q, a q = fixedTwice p := (fixedTwice_eq p).symm
  have hb : ∑ q, b q = Fintype.card X - fixedTwice p := by
    have s : ∑ q, a q + ∑ q, b q = Fintype.card X := by
      rw [← sum_add_distrib]; simpa only [hab] using sum_period p
    omega
  rw [count_cycle_factors, ← Finset.prod_pow, ← hb, ← ha, ← prod_pow_eq_pow_sum,
    ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  apply prod_le_prod
  intro q _
  have hk := period_pos p q.out
  dsimp [a,b]
  split_ifs with hd
  · have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    generalize period p q.out = k at *
    interval_cases k <;> decide
  · have hh : 3 ≤ period p q.out := by
      by_contra! h
      interval_cases e : period p q.out <;> simp_all
    simpa using lucas_fourth_le _ hh

theorem matching_card_sq (p : Perm X) (h₂ : ∀ x, p (p x) = x) (h₁ : ∀ x, p x ≠ x) :
    (Nat.card {f : X → Bool // coloringOK p f})^2 = 3^(Fintype.card X) := by
  have hper (q : Orbit p) : period p q.out = 2 := by
    have hd := (twice_fixed_iff p q.out).mp (h₂ q.out)
    have hb := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hpos := period_pos p q.out
    have hne : period p q.out ≠ 1 := fun he =>
      h₁ q.out (minimalPeriod_eq_one_iff_isFixedPt.mp he)
    omega
  rw [count_cycle_factors, ← sum_period p, ← prod_pow_eq_pow_sum, ← Finset.prod_pow]
  apply prod_congr rfl
  intro q _
  rw [hper]
  decide

end AscoliDihedral
