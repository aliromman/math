module

public import conjectures.HaslegraveBipartite.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section
namespace HaslegraveBipartite

/-- A displacement reached in r steps has at most r occurrences of each signed difference. -/
def Box (D : Finset ℤ) (r : ℕ) (z : ℤ) : Prop :=
  ∃ c : D → ℤ, (∀ a, |c a| ≤ (r:ℤ)) ∧ z = ∑ a, c a * a.val

theorem box_zero (D : Finset ℤ) : Box D 0 0 := ⟨fun _ => 0, by simp, by simp⟩

theorem Box.mono {D r s z} (h : Box D r z) (le : r ≤ s) : Box D s z := by
  obtain ⟨c,cap,dot⟩ := h
  exact ⟨c,fun a => (cap a).trans (by exact_mod_cast le),dot⟩

theorem Box.step {D r z delta} (h : Box D r z) (mem : |delta| ∈ D) : Box D (r+1) (z+delta) := by
  classical
  obtain ⟨c,cap,dot⟩ := h
  let a : D := ⟨|delta|,mem⟩
  let s : ℤ := if 0≤delta then 1 else -1
  have unit : |s| ≤ 1 := by dsimp [s]; split <;> decide
  have sign : s*a.val = delta := by
    dsimp [s,a]
    split
    next h => simp [abs_of_nonneg h]
    next h => simp [abs_of_neg (by omega : delta<0)]
  refine ⟨fun t => c t + if a=t then s else 0, ?_, ?_⟩
  · intro t
    apply (abs_add_le ..).trans
    have ht := cap t
    push_cast
    split
    · exact add_le_add ht unit
    · simp only [abs_zero,add_zero]; omega
  · simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [←dot,sign]

theorem box_count {D : Finset ℤ} {r n : ℕ} (f : Fin n → ℤ)
    (inj : Function.Injective f) (inside : ∀ i, Box D r (f i)) :
    n ≤ (2*r+1)^D.card := by
  classical
  choose c cap dot using inside
  let enc (i : Fin n) (a : D) : Fin (2*r+1) :=
    ⟨(c i a+r).toNat, by have := abs_le.mp (cap i a); omega⟩
  have uniq : Function.Injective enc := by
    intro i j e
    apply inj
    rw [dot i,dot j]
    apply Finset.sum_congr rfl
    intro a _
    have h := congrArg Fin.val (congrFun e a)
    change (c i a+r).toNat=(c j a+r).toNat at h
    have l := abs_le.mp (cap i a)
    have l' := abs_le.mp (cap j a)
    rw [show c i a = c j a by omega]
  simpa using Fintype.card_le_of_injective enc uniq

end HaslegraveBipartite
