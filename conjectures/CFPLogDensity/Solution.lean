module

public import conjectures.CFPLogDensity.Dense
public import conjectures.CFPLogDensity.Optimum

public section
namespace CFPLogDensity
open Filter

theorem resolution : Conjecture := by
  intro r hr
  refine ⟨unique_root r hr, fun b hb => ?_⟩
  dsimp only
  rw [←printed_value hr hb]
  apply optimum_of_intervals hr _ hb
  intro color
  obtain ⟨D,hD,large⟩ := dense_interval r (by omega)
  refine ⟨D,hD,?_⟩
  filter_upwards [large] with n h
  obtain ⟨i,hi⟩ := h color
  refine ⟨i,fun x low high => ?_⟩
  have hmul := (Nat.le_div_iff_mul_le hD).mp high
  obtain ⟨A,ha,sum⟩ := hi x low (by simpa [Nat.mul_comm] using hmul)
  exact ⟨A,fun a mem => ⟨(Nat.two_pow_pos n).trans_le (ha a mem).1,(ha a mem).2.2⟩,sum⟩

/-- info: 'CFPLogDensity.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end CFPLogDensity
