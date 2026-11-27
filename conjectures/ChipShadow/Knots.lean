module

public import conjectures.ChipShadow.Observable
public import conjectures.ChipShadow.Pascal
import Mathlib.Tactic.Positivity
import Mathlib.Data.Multiset.Range

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

def segment (a m : ℕ) : Multiset ℕ := ∑ i ∈ range m, {a+i}

theorem segment_last (a m : ℕ) : segment a (m+1) = (a+m) ::ₘ segment a m := by
  rw [segment,sum_range_succ,add_comm]
  rfl

theorem segment_first (a m : ℕ) : segment a (m+1) = a ::ₘ segment (a+1) m := by
  rw [segment,sum_range_succ',Nat.add_zero,add_comm]
  simp only [segment]
  rw [←Multiset.singleton_add]
  apply congrArg (fun s : Multiset ℕ ↦ {a}+s)
  apply sum_congr rfl;intro i _
  rw [show a+(i+1)=a+1+i by omega]

theorem shifted_segment (a q r : ℕ) :
    (∑ t ∈ range (q+r+2), ({if a+t≤a+q then a+t+1 else a+t-1} : Multiset ℕ)) =
       (a+q) ::ₘ (a+q+1) ::ₘ segment (a+1) (q+r) := by
  rw [show q+r+2=(q+1)+(r+1) by omega,sum_range_add]
  have left : (∑ t ∈ range (q+1), ({if a+t≤a+q then a+t+1 else a+t-1} : Multiset ℕ))=
      segment (a+1) (q+1) := by
    apply sum_congr rfl;intro t ht
    have h := mem_range.mp ht
    rw [ite_eq_left (show a+t≤a+q by omega),show a+t+1=a+1+t by omega]
  rw [left]
  have right : (∑ t ∈ range (r+1),
      ({if a+(q+1+t)≤a+q then a+(q+1+t)+1 else a+(q+1+t)-1} : Multiset ℕ))=
      segment (a+q) (r+1) := by
    apply sum_congr rfl;intro t _
    rw [ite_eq_right (show ¬a+(q+1+t)≤a+q by omega),show a+(q+1+t)-1=a+q+t by omega]
  have cat : segment (a+1) (q+r)=segment (a+1) q+segment (a+q+1) r := by
    simp only [segment,sum_range_add]
    simp_rw [show ∀ i, a+1+(q+i)=a+q+1+i by intro i;omega]
  rw [right,segment_last,segment_first (a+q),cat,show a+1+q=a+q+1 by omega]
  simp only [←Multiset.singleton_add]
  abel

theorem observable_segment {N a : ℕ} (d k : ℕ) (h : a+d+2≤N) :
    observable N k (segment a (d+2))=0 := by
  have ends (a d : ℕ) : ((d+1:ℕ):ℚ)*observable N k (segment a (d+2))=
      observable N k (segment (a+1) (d+1))-observable N k (segment a (d+1)) := by
    conv_lhs => rw [segment_first,segment_last]
    conv_rhs => rw [segment_last,segment_first a]
    rw [show a+1+d=a+(d+1) by omega,←two_knots]
    simp
  have eq := ends a d
  induction d generalizing a with
  | zero =>
    have s (t : ℕ) : segment t 1=Multiset.replicate 1 t := by simp [segment]
    rw [s,s,observable_constant _ (by omega),observable_constant _ (by omega),sub_self] at eq
    simpa using eq
  | succ d ih =>
    rw [ih (by omega) (ends (a+1) d),ih (by omega) (ends a d),sub_self] at eq
    exact (mul_eq_zero.mp eq).resolve_left (by positivity)

theorem observable_terminal {N a : ℕ} (bound : a+1<N) (l r k : ℕ) :
    observable N k (Multiset.replicate l a+Multiset.replicate r (a+1))=corner l r k := by
  cases l with
  | zero => simp [corner,unitCoord,observable_constant _ bound]
  | succ l =>
    cases r with
    | zero =>
      simp only [Multiset.replicate_zero,add_zero,corner,unitCoord]
      exact observable_constant _ (by omega) _ _
    | succ r =>
      have eq := two_knots N k a (a+1) (Multiset.replicate l a+Multiset.replicate r (a+1))
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_mul] at eq
      rw [corner,←observable_terminal bound l (r+1) k,←observable_terminal bound (l+1) r k]
      rw [Multiset.cons_swap a (a+1)] at eq
      simpa only [Multiset.replicate_succ, Multiset.cons_add,Multiset.add_cons] using eq
termination_by l+r

end ChipShadow
end
