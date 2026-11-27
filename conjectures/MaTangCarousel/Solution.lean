module

public import conjectures.MaTangCarousel.Orders
public import conjectures.MaTangCarousel.Constant
import Mathlib.Util.AssertNoSorry
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
namespace MaTangCarousel

/-- The triangle density is independent of the size of each nonempty part. -/
theorem triangles (m : ℕ) (hm : 0<m) : density (threeParts m) 3=1/9 := by
  have pos : (0:ℝ)<m := by exact_mod_cast hm
  simp [density,triangle_count,mul_pow]
  field_simp
  ring

/-- All three-part tournaments satisfy this uniform six-cycle bound. -/
theorem six_cycles (m : ℕ) (hm : 0<m) : density (threeParts m) 6≤5/486 := by
  have pos : (0:ℝ)<m := by exact_mod_cast hm
  have h : 2*(homCount (threeParts m) 6 : ℝ) ≤ 15*(m:ℝ)^6 := by exact_mod_cast six_count m
  simp only [density,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,mul_pow]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- The six-cycle densities approach the stated upper bound. -/
theorem six_cycle_limit : Filter.Tendsto (fun m ↦ density (threeParts m) 6)
    Filter.atTop (nhds (5/486)) := by
  have lim : Filter.Tendsto (fun m : ℕ ↦ (5/486:ℝ)*(1-5/(m:ℝ))^6) Filter.atTop (nhds (5/486)) := by
    simpa using (tendsto_const_nhds (x:=(5/486:ℝ))).mul
      (((tendsto_const_nhds (x:=(1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (5:ℝ))).pow 6)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lim tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 6] with m hm
    have hm5 : 5≤m := by omega
    have hc := six_count_lower m
    rw [show m+1-6=m-5 by omega] at hc
    have realc : 15*((m-5:ℕ):ℝ)^6≤2*(homCount (threeParts m) 6:ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub hm5] at realc
    have pos : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    simp only [density,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,mul_pow]
    field_simp
    norm_num at realc ⊢
    linarith only [realc]
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact six_cycles m hm

/-- At triangle density one ninth, the conjectured lower bound exceeds every example's
six-cycle density by at least this positive rational amount. -/
theorem gap (m : ℕ) (hm : 0<m) : ∃ g : ℝ, Profile 6 (density (threeParts m) 3) g ∧
    density (threeParts m) 6+1/2500 < 2^6*alpha 6*g := by
  refine ⟨(15550/19683)/64,by rw [triangles m hm]; exact at_one_ninth,?_⟩
  rw [alpha_six]
  linarith [six_cycles m hm]

theorem resolution : ¬Conjecture := by
  intro C
  obtain ⟨N,H⟩ := C 6 (by decide) (by decide) (1/2500) (by norm_num)
  let m := N+1
  obtain ⟨g,prof,less⟩ := gap m (by omega)
  have card : N ≤ Fintype.card (Fin 3 × Fin m) := by simp [m]; omega
  exact less.not_ge (H (Fin 3 × Fin m) (threeParts m) card g prof)

/-- info: 'MaTangCarousel.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution
assert_no_sorry resolution

end MaTangCarousel
