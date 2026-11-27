module

public import conjectures.LuckySpots.Pollak
public import conjectures.LuckySpots.Moments

@[expose] public section
namespace LuckySpots
open Finset
open scoped Classical

private theorem A_large {j l : ℕ} (hj : 0<j) (hl : j≤l) : A j l=E j l := by
  have h := local_count hj l
  rw [Circle.U_value hj hl] at h
  unfold E
  apply eq_sub_of_add_eq
  convert h using 2
  apply sum_congr rfl
  intro i hi
  have bound := mem_range.mp hi
  rw [Circle.U_value (by omega) (by omega)]
  ring

private theorem A_small {j l : ℕ} (h : l<j) : A j l=0 := by
  calc
    _ = W j l (fun _ ↦ 0) := by
      apply W_congr
      intro w hw
      have vac := vacant_capacity (List.range j) w
      have len := (mem_words.mp hw).1
      have nf : ¬filled j w := by
        intro e
        change vacant (List.range j) w=[] at e
        simp [e,len] at vac
        omega
      simp [wt,nf]
    _ = 0 := by simp [W_const]

private theorem W_wt (n k : ℕ) (P : List ℕ → Prop) [DecidablePred P] :
    W n k (fun w ↦ wt (P w))=(((words n k).filter P).card:ℚ) := by
  calc
    _ = ∑ w∈words n k, if P w then (1:ℚ) else 0 :=
      W_congr fun w _ ↦ by by_cases h : P w <;> simp [wt,h]
    _ = _ := Finset.sum_boole _ _

private theorem whole_cut (j b : ℕ) (hj : 0<j) :
    (luckyNumber (j+b) j:ℚ) =
    ∑ l∈range (j+b+1), ((j+b).choose l:ℚ)*A j l*
      W b (j+b-l) (fun w ↦ wt (accepted (List.range b) w)) := by
  have count : (luckyNumber (j+b) j:ℚ)= W (j+b) (j+b)
      (fun w ↦ wt (filled (j+b) w ∧ lucky (j-1) (List.range (j+b)) w=true)) := by
    exact (W_wt _ _ (fun w ↦ vacant (List.range (j+b)) w=[] ∧ lucky (j-1) (List.range (j+b)) w=true)).symm
  rw [count]
  let P := fun u v ↦ wt (filled j u ∧ lastLucky j u)*wt (accepted (List.range b) v)
  have eq : W (j+b) (j+b) (fun w ↦ wt (filled (j+b) w ∧ lucky (j-1) (List.range (j+b)) w=true)) =
      W (j+b) (j+b) (fun w ↦ P (low j w) (high j w)) := by
    apply W_congr
    intro w hw
    have success := full_cut j b w (mem_words.mp hw).1
    have luck := lower_luck j (j-1) (by omega) (List.range j) ((List.range b).map (j+·)) w
      (fun _ ↦ List.mem_range.mp) (by
        intro x hx
        obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
        omega)
    rw [←List.range_add] at luck
    simp only [P,filled,lastLucky,success,luck,←wt_and]
    apply congrArg wt
    apply propext
    tauto
  rw [eq,split_sum j b (j+b) P]
  apply sum_congr rfl
  intro l _
  simp only [P,W_mul]
  rw [show W j l (fun u ↦ wt (filled j u ∧ lastLucky j u)*
      W b (j+b-l) (fun w ↦ wt (accepted (List.range b) w))) =
    W b (j+b-l) (fun w ↦ wt (accepted (List.range b) w))*A j l by simp only [A,←W_mul,mul_comm]]
  ring

theorem large_expansion {n j : ℕ} (hj : 0<j) (hn : j≤n) :
    (luckyNumber n j:ℚ)=∑ l∈range (n+1), if j≤l then
      (n.choose l:ℚ)*((l:ℚ)-j+1)*E j l*((n-j+1:ℕ):ℚ)^(n-l)/((n-j+1:ℕ):ℚ) else 0 := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [whole_cut j b hj]
  apply sum_congr rfl
  intro l hl
  have len := mem_range.mp hl
  by_cases e : j≤l
  · rw [ite_eq_left e,A_large hj e,Circle.accepted_count _ _ (by omega),Nat.add_sub_cancel_left]
    rw [Nat.cast_sub (by omega : l≤j+b)]
    push_cast
    ring
  · simp [e,A_small (lt_of_not_ge e)]

theorem total_card {n : ℕ} (hn : 0<n) : totalNumber n=(n+1)^(n-1) := by
  have eq : W n n (fun w ↦ wt (accepted (List.range n) w))=(totalNumber n:ℚ) := by
    calc
      _ = W n n (fun w ↦ wt (vacant (List.range n) w=[])) := by
        apply W_congr
        intro w hw
        have len := (mem_words.mp hw).1
        simp [accepted_iff_length,len]
      _ = _ := W_wt _ _ (fun w ↦ vacant (List.range n) w=[])
  have e := Circle.accepted_count n n (by omega)
  rw [eq] at e
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  push_cast at e
  rw [pow_succ] at e
  simp only [Nat.succ_sub_one]
  exact_mod_cast (show (totalNumber (k+1):ℚ) = (k+1+1:ℚ)^k by
    rw [e]
    field_simp
    ring)

end LuckySpots
