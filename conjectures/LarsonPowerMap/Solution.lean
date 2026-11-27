module

public import conjectures.LarsonPowerMap.Selection
public import conjectures.LarsonPowerMap.LocalOrder
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
open Finset
namespace LarsonPowerMap

/-- The loss for one optimal residue at length k, expressed in integers and rationals. -/
def weight (k : ℕ) : ℚ :=
  if k=2 then 1/k else if k.Prime then 1/(2*k) else (1-(k.minFac : ℚ)⁻¹)/k

def preferred (k a : ℕ) : Bool := decide (¬k.Prime ∨ k=2 ∨ a ≡ k-1 [MOD k])

def candidates (n : ℕ) : Finset (ℕ × ℕ) :=
  (options n).filter fun z => preferred z.1 z.2

/-- Compute every maximizing exponent using only the integers from 1 to n,
their least common multiples, and rational comparisons. -/
def answer (n : ℕ) : Finset ℕ :=
  ((candidates n).filter (fun z => ∀ y ∈ candidates n, weight z.1 ≤ weight y.1)).image Prod.snd

private theorem residue {p a : ℕ} (hp : p.Prime) (lo : 1≤p) (ne : ¬a ≡ 1 [MOD p]) :
    a ≡ p-1 [MOD p] ↔ orderOf (a : ZMod p)=2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hne : (a : ZMod p)≠1 := fun e => ne ((ZMod.natCast_eq_natCast_iff ..).mp (by simpa using e))
  have val : ((p-1 : ℕ) : ZMod p)= -1 := by simp [Nat.cast_sub lo]
  rw [←ZMod.natCast_eq_natCast_iff,val,orderOf_eq_prime_iff,sq_eq_one_iff]
  tauto

private theorem local_eq {n k a : ℕ} (x : (k,a)∈candidates n) :
    loss k a = weight k := by
  obtain ⟨good,pref⟩ := mem_filter.mp x
  obtain ⟨lo,_,h⟩ := mem_options.mp good
  have m : k∈bad n a := h ▸ mem_singleton_self k
  have ne := (mem_filter.mp m).2
  have tk := (single_bounds h).1
  by_cases two : k=2
  · subst k
    have z : (a : ZMod 2)=0 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mpr
      apply Nat.dvd_of_mod_eq_zero
      change ¬a%2=1%2 at ne
      have lt := Nat.mod_lt a (by decide : 0<2)
      omega
    simp [loss,weight,z]
  by_cases prime : k.Prime
  · have eq : a ≡ k-1 [MOD k] := by simpa [preferred,prime,two] using pref
    have ord := (residue prime (by omega) ne).mp eq
    simp [loss,weight,two,prime,ord]; ring
  · simp [loss,weight,two,prime,composite_order lo h prime]

private theorem strict_half {k d : ℕ} (lo : 0<k) (h1 : d≠1) (h2 : d≠2) :
    (1:ℚ)/(2*k) < (1-(d:ℚ)⁻¹)/k := by
  have kp : (0:ℚ)<k := by exact_mod_cast lo
  by_cases h0 : d=0
  · rw [h0]; simp only [Nat.cast_zero,inv_zero,sub_zero]
    exact div_lt_div_of_pos_left one_pos kp (by linarith)
  · have gt : 2<d := by omega
    have gp : (2:ℚ)<d := by exact_mod_cast gt
    have dp : (0:ℚ)<d := by linarith
    field_simp
    nlinarith [mul_pos (sub_pos.mpr gp) kp]

private theorem improve {n k a : ℕ} (x : (k,a)∈options n) (notPref : ¬preferred k a) :
    ∃ b, (k,b)∈candidates n ∧ loss k b < loss k a := by
  obtain ⟨_,_,h⟩ := mem_options.mp x
  obtain ⟨tk,up,long⟩ := single_bounds h
  simp only [preferred,decide_eq_true_eq,not_or,not_not] at notPref
  obtain ⟨prime,two,badResidue⟩ := notPref
  have m : k∈bad n a := h ▸ mem_singleton_self k
  have ne := (mem_filter.mp m).2
  have no2 := (residue prime (by omega) ne).not.mp badResidue
  have no1 : orderOf (a : ZMod k)≠1 := by
    intro one
    exact ne ((ZMod.natCast_eq_natCast_iff _ 1 _).mp (by simpa using orderOf_eq_one_iff.mp one))
  obtain ⟨b,lo,ub,sing,ord⟩ := prime_choice prime (by omega) up long
  have mb : k∈bad n b := sing ▸ mem_singleton_self k
  have good := (residue prime (by omega) (mem_filter.mp mb).2).mpr ord
  have c : (k,b)∈candidates n := mem_filter.mpr ⟨mem_options.mpr ⟨lo,ub,sing⟩,
    by simp [preferred,good]⟩
  refine ⟨b,c,?_⟩
  rw [local_eq c,weight,ite_eq_right two,ite_eq_left prime]
  exact strict_half (by omega) no1 no2

theorem exact_answer : ExactAnswer answer := by
  intro n a
  rw [← resolution n a]
  constructor
  · intro h
    obtain ⟨⟨k,b⟩,sel,rfl⟩ := mem_image.mp h
    obtain ⟨c,small⟩ := mem_filter.mp sel
    have cg : (k,b)∈options n := (mem_filter.mp c).1
    refine mem_image.mpr ⟨(k,b),mem_filter.mpr ⟨cg,?_⟩,rfl⟩
    rintro ⟨j,u⟩ hu
    by_cases pref : preferred j u
    · have good : (j,u)∈candidates n := mem_filter.mpr ⟨hu,pref⟩
      rw [local_eq c,local_eq good]
      exact small (j,u) good
    · obtain ⟨v,hv,lt⟩ := improve hu pref
      apply le_trans _ lt.le
      rw [local_eq c,local_eq hv]
      exact small (j,v) hv
  · intro h
    obtain ⟨⟨k,b⟩,sel,rfl⟩ := mem_image.mp h
    obtain ⟨x,small⟩ := mem_filter.mp sel
    have c : (k,b)∈candidates n := by
      apply mem_filter.mpr
      refine ⟨x,?_⟩
      by_contra miss
      obtain ⟨u,hu,lt⟩ := improve x miss
      exact lt.not_ge (small (k,u) (mem_filter.mp hu).1)
    refine mem_image.mpr ⟨(k,b),mem_filter.mpr ⟨c,?_⟩,rfl⟩
    rintro ⟨j,u⟩ hu
    rw [←local_eq c,←local_eq hu]
    exact small (j,u) (mem_filter.mp hu).1

theorem count_for_candidate {n k a : ℕ} (h : (k,a)∈candidates n) :
    (N n a : ℚ) = n.factorial*(1-weight k) := by
  obtain ⟨lo,_,single⟩ := mem_options.mp (mem_filter.mp h).1
  rw [score_single (by omega : 1≤a) single,local_eq h]

theorem eight : answer 8={421} ∧ N 8 421=37800 := by
  refine ⟨by decide +kernel,?_⟩
  have h := count_for_candidate (show (8,421)∈candidates 8 by decide +kernel)
  norm_num [weight,Nat.factorial,show (8:ℕ).minFac=2 by decide] at h
  exact_mod_cast h

/-- info: 'LarsonPowerMap.exact_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_answer

end LarsonPowerMap
