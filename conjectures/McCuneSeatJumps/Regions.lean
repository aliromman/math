module

public import conjectures.McCuneSeatJumps.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

@[expose] public section
open MeasureTheory Finset Set
namespace McCuneSeatJumps

theorem cycle_sum {R : Type*} [AddCommMonoid R] (f : Fin 3 → R) (i : Fin 3) :
    f i + f (i+1) + f (i+2) = ∑ j, f j := by
  rw [Fin.sum_univ_three]
  fin_cases i
  · rfl
  · change (f 1 + f 2) + f 0 = (f 0 + f 1) + f 2
    rw [add_comm _ (f 0),add_assoc]
  · change (f 2 + f 0) + f 1 = (f 0 + f 1) + f 2
    rw [add_assoc,add_comm (f 2) (f 0 + f 1)]

theorem cycle_cases (i j : Fin 3) : j = i ∨ j = i+1 ∨ j = i+2 := by decide +revert

private theorem neighbors (i : Fin 3) : i+1 ≠ i ∧ i+2 ≠ i ∧ i+2 ≠ i+1 := by decide +revert

def allocations (i : Fin 3) (l a c : ℕ) : Seats := fun j =>
  if j = i then l else if j = i+1 then a else c

@[simp] theorem allocations_here (i : Fin 3) (l a c) : allocations i l a c i = l := by
  simp [allocations]

@[simp] theorem allocations_next (i : Fin 3) (l a c) : allocations i l a c (i+1) = a := by
  simp [allocations,(neighbors i).1]

@[simp] theorem allocations_last (i : Fin 3) (l a c) : allocations i l a c (i+2) = c := by
  simp [allocations,(neighbors i).2]

theorem sum_errors {p : Shares} {a : Seats} {h : ℕ} (hs : ∑ i, p i = 1)
    (ha : ∑ i, a i = h) : ∑ i, err p h a i = 0 := by
  simp [err,sum_sub_distrib,← mul_sum,hs,← Nat.cast_sum,ha]

private theorem err_bounds {p : Shares} {a : Seats} {h : ℕ} (hs : ∑ i, p i = 1)
    (ha : Inside p h a) (i : Fin 3) : -2 < 3 * err p h a i ∧ 3 * err p h a i < 2 := by
  have sum := (cycle_sum (err p h a) i).trans (sum_errors hs ha.1)
  constructor
  · linarith only [sum,ha.2 (i+1) i,ha.2 (i+2) i]
  · linarith only [sum,ha.2 i (i+1),ha.2 i (i+2)]

theorem loss_one {h k : ℕ} {a b : Seats} {p : Shares} (hs : ∑ i, p i = 1)
    (hp : ∀ i, 0 < p i) (ha : Inside p h a) (hb : Inside p (h+k) b)
    {i : Fin 3} (hi : b i < a i) : b i + 1 = a i := by
  have old := (err_bounds hs ha i).1
  have new := (err_bounds hs hb i).2
  have d : (a i : ℝ) - b i < 2 := by
    unfold err at old new
    push_cast at new
    nlinarith only [old,new,mul_nonneg (by positivity : (0:ℝ) ≤ k) (hp i).le]
  have dd : (a i : ℤ) - b i < 2 := by exact_mod_cast d
  omega

theorem loss_unique {h k : ℕ} {a b : Seats} {p : Shares} (hs : ∑ i, p i = 1)
    (hp : ∀ i, 0 < p i) (ha : Inside p h a) (hb : Inside p (h+k) b)
    {i j : Fin 3} (hi : b i < a i) (hj : b j < a j) : i = j := by
  have high (t : Fin 3) (ht : b t < a t) : 1 < 3 * err p (h+k) b t := by
    have old := (err_bounds hs ha t).1
    have d : (b t:ℝ)+1 = a t := by exact_mod_cast loss_one hs hp ha hb ht
    unfold err at old ⊢
    push_cast
    nlinarith only [old,d,mul_nonneg (by positivity : (0:ℝ) ≤ k) (hp t).le]
  rcases cycle_cases i j with H|H|H
  · exact H.symm
  all_goals subst j
  all_goals have s := (cycle_sum (err p (h+k) b) i).trans (sum_errors hs hb.1)
  · linarith only [s,high _ hi,high _ hj,(err_bounds hs hb (i+2)).1]
  · linarith only [s,high _ hi,high _ hj,(err_bounds hs hb (i+1)).1]

theorem inside_unique {p : Shares} {a b : Seats} {h : ℕ}
    (ha : Inside p h a) (hb : Inside p h b) : a = b := by
  have le (a b : Seats) (ha : Inside p h a) (hb : Inside p h b) : ∀ i, a i ≤ b i := by
    intro i
    by_contra! hi
    have ex : ∃ j, a j < b j := by
      by_contra! no
      have lt := Finset.sum_lt_sum (s:=univ) (fun j _ => no j) ⟨i,mem_univ _,hi⟩
      rw [ha.1,hb.1] at lt
      exact lt_irrefl _ lt
    obtain ⟨j,hj⟩ := ex
    have ir : (b i:ℝ)+1 ≤ a i := by exact_mod_cast hi
    have jr : (a j:ℝ)+1 ≤ b j := by exact_mod_cast hj
    have u := ha.2 j i
    have v := hb.2 i j
    unfold err at u v
    linarith only [ir,jr,u,v]
  exact funext fun i => (le a b ha hb i).antisymm (le b a hb ha i)

def region (h k : ℕ) (i : Fin 3) (l a : ℕ) : Set (ℝ × ℝ) := {x |
  (∀ j, 0 < shares x j) ∧ ∃ A B, Inside (shares x) h A ∧ Inside (shares x) (h+k) B ∧
    B i < A i ∧ A i = l ∧ A (i+1) = a}

theorem region_unique {h k i j l t a c x} (u : x ∈ region h k i l a)
    (v : x ∈ region h k j t c) : i = j ∧ l = t ∧ a = c := by
  obtain ⟨hp,A,B,ha,hb,hi,rfl,rfl⟩ := u
  obtain ⟨_,A',B',ha',hb',hj,rfl,rfl⟩ := v
  obtain rfl := inside_unique ha ha'
  obtain rfl := inside_unique hb hb'
  obtain rfl := loss_unique (sum_shares x) hp ha hb hi hj
  exact ⟨rfl,rfl,rfl⟩

end McCuneSeatJumps
