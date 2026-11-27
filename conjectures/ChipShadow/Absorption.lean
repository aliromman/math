module

public import conjectures.ChipShadow.Runs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

theorem active_of_block {n : ℕ} {w : State n} {B : Block n} (hb : B∈blocks w) : 0<choices w := by
  have h : B.1.val<B.2.val := (mem_blocks.mp hb).1
  have lower : span B≤choices w := single_le_sum (fun _ _ ↦ Nat.zero_le _) hb
  unfold span at lower
  omega

theorem block_of_active {n : ℕ} {w : State n} (h : choices w≠0) : ∃ B∈blocks w,0<span B := by
  by_contra! empty
  apply h
  unfold choices
  exact sum_eq_zero (fun B hb ↦ Nat.eq_zero_of_le_zero (empty B hb))

theorem terminal_shadow {n : ℕ} (hn : 0<n) {w : State n} (g : Good w) (stop : choices w=0) :
    ∃ r : Fin n,shadow r w ∧ w 0+1<n+1 := by
  classical
  have mono : Monotone w := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have neq : suite w i.castSucc≠suite w i.succ := by
      intro eq
      obtain ⟨_,hb,_⟩ := has_block g.sorted i eq
      have := active_of_block hb
      omega
    have lt := lt_of_le_of_ne (g.sorted i.castSucc_lt_succ.le) neq
    change w i.castSucc+i.val < w i.succ+(i.val+1) at lt
    omega
  have grow : ∃ i j,i<j ∧ w i<w j := by
    rcases g.marked with initial|mark
    · subst w
      let i : Fin n := ⟨0,hn⟩
      have eq : suite (ChipShadow.initial n) i.castSucc=suite (ChipShadow.initial n) i.succ := by
        change n-0+0=n-1+1
        omega
      obtain ⟨_,hb,_⟩ := has_block g.sorted _ eq
      have := active_of_block hb
      omega
    · exact mark
  obtain ⟨i,j,_,rise⟩ := grow
  let S := univ.filter fun j ↦ w 0<w j
  have mem (i : Fin (n+1)) : i∈S ↔ w 0<w i := by simp [S]
  have nonempty : S.Nonempty := ⟨j,(mem j).mpr ((mono (Fin.zero_le i)).trans_lt rise)⟩
  let c := S.min' nonempty
  have wc : w 0<w c := (mem c).mp (S.min'_mem nonempty)
  have cz : 0<c.val := by
    by_contra! eq
    have ja : c=0 := Fin.ext (by change c.val=0;omega)
    simp [ja] at wc
  let r : Fin n := ⟨c.val-1,by have := c.isLt;omega⟩
  have rv : r.val=c.val-1 := rfl
  refine ⟨r,?_,by have := g.bounded c;omega⟩
  intro j
  have lower := mono (Fin.zero_le j)
  have upper := g.width 0 j (Fin.zero_le j)
  by_cases lo : j.val≤r.val
  · rw [ite_eq_left lo]
    by_contra! ne
    have memj := (mem j).mpr (lt_of_le_of_ne lower ne.symm)
    have le : c.val≤j.val := S.min'_le _ memj
    omega
  · rw [ite_eq_right lo]
    have cj : c≤j := show c.val≤j.val by omega
    have high := mono cj
    omega

theorem shadow_unique {n : ℕ} {w : State n} {r s : Fin n} (a : shadow r w) (b : shadow s w) :
    r=s := by
  have compare {r s : Fin n} (a : shadow r w) (b : shadow s w) : ¬r<s := by
    intro h
    have h' : r.val<s.val := h
    have x := a r.succ
    have y := b r.succ
    rw [ite_eq_right (show ¬r.succ.val≤r.val by change ¬r.val+1≤r.val;omega)] at x
    rw [ite_eq_left (show r.succ.val≤s.val by change r.val+1≤s.val;omega)] at y
    omega
  exact le_antisymm (le_of_not_gt (compare b a)) (le_of_not_gt (compare a b))

def energy {n : ℕ} (w : State n) : ℕ := ∑ i,2^i.val*w i

private theorem prefix_weight {n : ℕ} (c : Fin (n+1)) :
    (∑ i : Fin (n+1),if i.val<c.val then 2^i.val else 0)+1=2^c.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i<c.val then 2^i else 0)]
  have splitRange (x : ℕ) (hx : c.val≤x) :
      (∑ i∈range x,if i<c.val then 2^i else 0)=∑ i∈range c.val,2^i := by
    conv_lhs => rw [show x=c.val+(x-c.val) by omega,sum_range_add]
    have lo : (∑ i∈range c.val,if i<c.val then 2^i else 0)=∑ i∈range c.val,2^i := by
      apply sum_congr rfl;intro i hi;rw [ite_eq_left (mem_range.mp hi)]
    rw [lo]
    simp
  rw [splitRange _ c.isLt.le]
  have formula (a : ℕ) : (∑ i∈range a,2^i)+1=2^a := by
    induction a with
    | zero => simp
    | succ a ih => rw [sum_range_succ,pow_succ];omega
  exact formula _

theorem energy_increases {n : ℕ} {w : State n} {B : Block n} (hb : IsBlock w B)
    {r : ℕ} (hr : r<span B) : energy w < energy (push w B r) := by
  let c : Fin (n+1) := ⟨B.2.val-r,by have := B.2.isLt;omega⟩
  have cv : c.val=B.2.val-r := rfl
  have lt : r<B.2.val-B.1.val := hr
  have cin : B.1≤c ∧ c≤B.2 := by change B.1.val≤c.val ∧ c.val≤B.2.val;omega
  have wc := suite_in hb cin
  have bound (i : Fin (n+1)) :
      2^i.val*w i+(if i=c then 2^i.val else 0)≤
        2^i.val*push w B r i+(if i.val<c.val then 2^i.val else 0) := by
    by_cases low : i.val<c.val
    · have ne : i≠c := fun eq ↦ by subst i;omega
      have a : w i≤push w B r i+1 := by simp only [push];split_ifs <;> omega
      simpa only [ite_eq_right ne,ite_eq_left low,Nat.mul_add,Nat.mul_one,Nat.add_zero]
        using (show 2^i.val*w i+(if i=c then 2^i.val else 0)≤
          2^i.val*(push w B r i+1) by
            rw [ite_eq_right ne,Nat.add_zero];exact Nat.mul_le_mul_left _ a)
    · simp only [ite_eq_right low,Nat.add_zero]
      by_cases eq : i=c
      · subst i
        have e : push w B r c=w c+1 := by
          simp only [push,ite_eq_left cin,ite_eq_left (show w c≤w B.2+r by omega)]
        simp only [ite_true,e,Nat.mul_add,Nat.mul_one,le_refl]
      · simp only [ite_eq_right eq,Nat.add_zero]
        apply Nat.mul_le_mul_left
        by_cases inside : B.1≤i ∧ i≤B.2
        · have wi := suite_in hb inside
          simp only [push,ite_eq_left inside,ite_eq_left (show w i≤w B.2+r by omega)]
          omega
        · simp [push,inside]
  have total := sum_le_sum (s:=univ) (fun i _ ↦ bound i)
  rw [sum_add_distrib,sum_add_distrib,sum_ite_eq',ite_eq_left (mem_univ _)] at total
  change energy w+_≤energy (push w B r)+_ at total
  have sum := prefix_weight c
  omega

def remaining {n : ℕ} (w : State n) := (∑ i : Fin (n+1),2^i.val)*n-energy w

theorem remaining_decreases {n : ℕ} {w : State n} (g : Good w) {B : Block n}
    (hb : IsBlock w B) {r : ℕ} (hr : r<span B) : remaining (push w B r)<remaining w := by
  have bounded {v : State n} (good : Good v) : energy v≤(∑ i : Fin (n+1),2^i.val)*n := by
    rw [sum_mul]
    exact sum_le_sum (fun i _ ↦ Nat.mul_le_mul_left _ (good.bounded i))
  have a := energy_increases hb hr
  have u := bounded (pushed_good g hb hr)
  unfold remaining
  omega

/-- Once all paths have stopped, payoffs that agree at stable states have the same expectation. -/
theorem terminal_expect {n : ℕ} (f g : State n → ℚ)
    (agree : ∀ w,Good w → choices w=0 → f w=g w) (t : ℕ) {w : State n} (good : Good w)
    (time : remaining w≤t) : expect f t w=expect g t w := by
  induction t generalizing w with
  | zero =>
    apply agree w good
    by_contra active
    obtain ⟨B,hb,hr⟩ := block_of_active active
    have := remaining_decreases good (mem_blocks.mp hb) hr
    omega
  | succ t ih =>
    by_cases stop : choices w=0
    · simpa [expect,stop] using agree w good stop
    · simp only [expect,ite_eq_right stop]
      congr 1
      apply sum_congr rfl;intro B hb
      apply sum_congr rfl;intro r hr
      have h := mem_blocks.mp hb
      have lt := mem_range.mp hr
      have := remaining_decreases good h lt
      exact ih (pushed_good good h lt) (by omega)

end ChipShadow
end
