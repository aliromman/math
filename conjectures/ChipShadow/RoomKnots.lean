module

public import conjectures.ChipShadow.Runs
public import conjectures.ChipShadow.Knots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

def knots {n : ℕ} (w : State n) : Multiset ℕ := ∑ j,{w j}
def mass {n : ℕ} (k : ℕ) (w : State n) : ℚ := observable (n+1) k (knots w)

/-- Read the ranks of a run in reverse order. -/
private theorem reverse_slice {M : Type*} [AddCommMonoid M] {n : ℕ} (B : Block n)
    (hb : B.1≤B.2) (f : Fin (n+1) → M) (v : ℕ → M)
    (eq : ∀ j∈Icc B.1 B.2,f j=v (B.2.val-j.val)) :
    ∑ j∈Icc B.1 B.2,f j = ∑ i∈range (span B+1),v i := by
  apply sum_bij (fun (j : Fin (n+1)) _ ↦ B.2.val-j.val)
  · intro j hj
    obtain ⟨l,u⟩ := mem_Icc.mp hj
    change B.1.val≤j.val at l
    change j.val≤B.2.val at u
    apply mem_range.mpr
    unfold span
    omega
  · intro i hi j hj eq
    have a : i.val≤B.2.val := (mem_Icc.mp hi).2
    have b : j.val≤B.2.val := (mem_Icc.mp hj).2
    exact Fin.ext (by omega)
  · intro i hi
    have b := mem_range.mp hi
    have le : B.1.val≤B.2.val := hb
    unfold span at b
    let j : Fin (n+1) := ⟨B.2.val-i,by have := B.2.isLt;omega⟩
    have jv : j.val=B.2.val-i := rfl
    exact ⟨j,mem_Icc.mpr ⟨show B.1.val≤j.val by omega,show j.val≤B.2.val by omega⟩,by omega⟩
  · exact eq

private theorem partition_knots {n : ℕ} (w : State n) (B : Block n) :
    knots w = (∑ j∈Icc B.1 B.2,({w j} : Multiset ℕ))+
      ∑ j∈univ\Icc B.1 B.2,({w j} : Multiset ℕ) := by
  rw [add_comm,sum_sdiff (subset_univ _)]
  rfl

private theorem run_multisets {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B) :
    ∃ K : Multiset ℕ, knots w=w B.2 ::ₘ (w B.2+span B) ::ₘ K ∧
      ∀ i<span B, knots (push w B i)=(w B.2+i) ::ₘ (w B.2+i+1) ::ₘ K := by
  let d := span B-1
  have len : span B=d+1 := by have a : B.1.val<B.2.val := h.1;dsimp [d,span];omega
  let S := ∑ j∈univ\Icc B.1 B.2,({w j} : Multiset ℕ)
  let a := w B.2
  have val {j : Fin (n+1)} (mem : j∈Icc B.1 B.2) : w j=a+(B.2.val-j.val) := by
    have eq := suite_in h (mem_Icc.mp mem)
    have b : j.val≤B.2.val := (mem_Icc.mp mem).2
    dsimp [a]
    omega
  refine ⟨segment (a+1) d+S,?_,?_⟩
  · rw [partition_knots w B]
    change (∑ j∈Icc B.1 B.2,({w j} : Multiset ℕ))+S=_
    rw [reverse_slice B h.1.le _ (fun t ↦ ({a+t} : Multiset ℕ)) (fun j hj ↦ by rw [val hj])]
    change segment a (span B+1)+S=_
    rw [len,segment_first,segment_last,show a+1+d=a+(d+1) by omega]
    simp only [Multiset.cons_add,a]
  · intro i hi
    rw [partition_knots _ B]
    have outside : (∑ j∈univ\Icc B.1 B.2,({push w B i j} : Multiset ℕ))=S := by
      apply sum_congr rfl
      intro j hj
      have b := (mem_sdiff.mp hj).2
      simp only [mem_Icc] at b
      simp [push,b]
    rw [outside,reverse_slice B h.1.le _ (fun t ↦
      ({if a+t≤a+i then a+t+1 else a+t-1} : Multiset ℕ)) (fun j hj ↦ by
        simp only [push,ite_eq_left (mem_Icc.mp hj),val hj,a])]
    have left : span B+1=i+(d-i)+2 := by omega
    rw [left,shifted_segment,show i+(d-i)=d by omega]
    simp only [Multiset.cons_add,a]

theorem harmonic_run {n : ℕ} {w : State n} {B : Block n} (h : IsBlock w B) (k : ℕ) :
    ∑ i∈range (span B),mass k (push w B i)=span B*mass k w := by
  obtain ⟨K,old,new⟩ := run_multisets h
  simp only [mass,old]
  rw [sum_congr rfl (fun i hi ↦ congrArg (observable (n+1) k) (new i (mem_range.mp hi)))]
  exact split_sum ..

theorem mass_initial {n : ℕ} (hn : 0<n) (k : ℕ) : mass k (initial n)=0 := by
  have e : knots (initial n)=segment 0 (n+1) := by
    unfold knots segment
    let B : Block n := (0,Fin.last n)
    have U : Icc B.1 B.2=univ := by
      ext i;simp [B,Fin.le_last]
    rw [←U]
    apply reverse_slice B (by simp [B]) _ (fun i ↦ ({0+i} : Multiset ℕ))
    intro j _
    simp [initial,B]
  rw [mass,e,show n+1=(n-1)+2 by omega]
  exact observable_segment _ _ (by omega)

theorem mass_shadow {n : ℕ} {w : State n} {r : Fin n} (s : shadow r w)
    (bound : w 0+1<n+1) (k : ℕ) : mass k w=corner (r.val+1) (n-r.val) k := by
  have e : knots w=Multiset.replicate (r.val+1) (w 0)+Multiset.replicate (n-r.val) (w 0+1) := by
    unfold knots
    rw [sum_congr rfl (fun j _ ↦ congrArg (fun x : ℕ ↦ ({x} : Multiset ℕ)) (s j))]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ( {if i≤r.val then w 0 else w 0+1} : Multiset ℕ)),
      show range (n+1)=range ((r.val+1)+(n-r.val)) by congr 1;have := r.isLt;omega,sum_range_add]
    apply congrArg₂ (·+·)
    · calc
        _ = ∑ _i∈range (r.val+1),({w 0} : Multiset ℕ) := by
          apply sum_congr rfl;intro i hi;rw [ite_eq_left (show i≤r.val by have := mem_range.mp hi;omega)]
        _ = _ := by simp only [sum_const,card_range,Multiset.nsmul_singleton]
    · simp only [show ∀ i,¬r.val+1+i≤r.val by intro i;omega,ite_false]
      simp only [sum_const,card_range,Multiset.nsmul_singleton]
  rw [mass,e,observable_terminal bound]

end ChipShadow
end
