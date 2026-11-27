module

public import conjectures.TanWuHon.Lower
public import conjectures.TanWuHon.Odd

public section
namespace TanWuHon
open Multiset

theorem resolution : Conjecture := by
  intro f r L hf hr hL threshold
  by_cases short : r≤L*(sample f-1)
  · exact initial_cases hf hr hL threshold short
  have holds {t : ℕ} (rt : r≤t) {P : Multiset ℕ} (p : Partition f (f+t) P)
      (eq : P.card=rho f (f+t)) : Stable f L P := by
    have wt := base_lower hf (by omega : 0<t) hL
    rw [←eq] at wt
    apply stable hf hL p.1 p.2.2 (by rw [p.2.1]; omega)
    · by_contra! bad
      have k : P.card≤2*(f-1) := by omega
      have := Nat.mul_le_mul_left L k
      rw [Nat.mul_comm (2*(f-1))] at threshold
      omega
    · by_contra! bad
      have k : P.card≤sample f-1 := by omega
      have := Nat.mul_le_mul_left L k
      omega
  obtain ⟨P,p,cp⟩ := optimum hf (by omega : f<f+r)
  have sp := holds le_rfl p cp
  have plus : Partition f (f+r+L) (L ::ₘ P) := by
    refine ⟨?_,by rw [sum_cons,p.2.1]; omega,add_least hL.1 p.2.2 ((le_max_right _ _).trans sp)⟩
    intro x hx
    rcases mem_cons.mp hx with rfl|hx
    · exact hL.1
    · exact p.1 x hx
  have lower := card_le_rho plus
  rw [card_cons,cp] at lower
  obtain ⟨R,g,cr⟩ := optimum hf (by omega : f<f+(r+L))
  have st := holds (Nat.le_add_right r L) g cr
  have mem : L∈R := count_pos.mp (lt_of_lt_of_le (by decide : 0<1) ((le_max_left _ _).trans st))
  obtain ⟨T,rfl⟩ := exists_cons_of_mem mem
  have mass := g.2.1
  rw [sum_cons] at mass
  have part : Partition f (f+r) T := ⟨fun x hx ↦ g.1 x (mem_cons_of_mem hx),by omega,
    avoids_mono g.2.2 (le_cons_self _ _)⟩
  have upper := card_le_rho part
  rw [card_cons,←Nat.add_assoc] at cr
  omega

/-- info: 'TanWuHon.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end TanWuHon
