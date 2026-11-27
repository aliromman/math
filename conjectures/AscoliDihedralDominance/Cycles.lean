module

public import conjectures.AscoliDihedralDominance.Arithmetic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace AscoliDihedral

def pathOK : (n : ℕ) → Bool → Bool → (Fin n → Bool) → Bool
  | 0, l, r, _ => !(l && r)
  | n+1, l, r, f => !(l && f 0) && pathOK n (f 0) r (fun i => f i.succ)

private def pathCount (n : ℕ) (l r : Bool) : ℕ :=
  ∑ f : Fin n → Bool, if pathOK n l r f then 1 else 0

theorem sum_by_first (n : ℕ) (g : (Fin (n+1) → Bool) → ℕ) :
    ∑ f, g f = (∑ t, g (Fin.cons true t)) + ∑ t, g (Fin.cons false t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp g, Fintype.sum_prod_type,
    Fintype.sum_bool]
  rfl

private theorem pathCount_succ (n : ℕ) (l r : Bool) :
    pathCount (n+1) l r = pathCount n false r + if l then 0 else pathCount n true r := by
  unfold pathCount
  rw [sum_by_first]
  cases l <;> simp [pathOK, add_comm]

private theorem pathCount_add_two (n : ℕ) (l r : Bool) :
    pathCount (n+2) l r = pathCount n l r + pathCount (n+1) l r := by
  cases l <;> simp only [pathCount_succ, Bool.false_eq_true, ↓reduceIte, add_zero] <;> omega

/-- The number of independent subsets of a circular chain of positive length. -/
private theorem ring_count (n : ℕ) :
    pathCount n false false + pathCount n true true = lucas (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    change _ = lucas (n+2) at h₁
    rw [pathCount_add_two, pathCount_add_two]
    change _ = lucas (n+1) + lucas (n+2)
    omega

/-- The next position in a circular chain. -/
def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private def vertex {n : ℕ} (l r : Bool) (f : Fin n → Bool) (i : ℕ) : Bool :=
  if i = 0 then l else if h : i-1 < n then f ⟨i-1,h⟩ else r

private theorem vertex_succ (n : ℕ) (l r : Bool) (f : Fin (n+1) → Bool) (i : ℕ) :
    vertex l r f (i+1) = vertex (f 0) r (fun j => f j.succ) i := by
  cases i with
  | zero => simp [vertex]
  | succ i =>
    simp only [vertex, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_one_sub_one, Nat.add_lt_add_iff_right]
    split <;> rfl

private theorem pathOK_iff (n : ℕ) (l r : Bool) (f : Fin n → Bool) :
    pathOK n l r f ↔ ∀ i < n+1, (!(vertex l r f i && vertex l r f (i+1))) = true := by
  induction n generalizing l with
  | zero => simp [pathOK, vertex]
  | succ n ih =>
    rw [pathOK, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h₀,h⟩ (i|i) hi
      · simpa [vertex] using h₀
      · simpa only [vertex_succ] using h i (by omega)
    · intro h
      refine ⟨by simpa [vertex] using h 0 (by omega), fun i hi => ?_⟩
      simpa only [vertex_succ] using h (i+1) (by omega)

private theorem vertex_cycle {n : ℕ} (f : Fin (n+1) → Bool) (i : ℕ) (hi : i ≤ n+1) :
    vertex (f 0) (f 0) (fun j : Fin n => f j.succ) i =
      f ⟨i % (n+1), Nat.mod_lt _ (by omega)⟩ := by
  cases i with
  | zero => simp [vertex]
  | succ i =>
    by_cases h : i < n
    · simp [vertex,h, Nat.mod_eq_of_lt (show i+1 < n+1 by omega), Fin.succ]
    · have e : i = n := by omega
      subst i
      simp [vertex]

theorem cycle_iff {n : ℕ} (f : Fin (n+1) → Bool) :
    pathOK n (f 0) (f 0) (fun i => f i.succ) ↔ ∀ i, (!(f i && f (next i))) = true := by
  rw [pathOK_iff]
  constructor
  · intro h i
    have e := h i.val i.isLt
    have hmod : (⟨i.val % (n+1), Nat.mod_lt _ (by omega)⟩ : Fin (n+1)) = i :=
      Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [vertex_cycle f _ (by omega), vertex_cycle f _ (by omega), hmod] at e
    exact e
  · intro h i hi
    have hmod : (⟨i % (n+1), Nat.mod_lt _ (by omega)⟩ : Fin (n+1)) = ⟨i,hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    rw [vertex_cycle f _ (by omega), vertex_cycle f _ (by omega), hmod]
    exact h ⟨i,hi⟩

theorem card_cycle (n : ℕ) :
    (Finset.univ.filter fun f : Fin (n+1) → Bool => ∀ i, (!(f i && f (next i))) = true).card =
      lucas (n+1) := by
  rw [Finset.card_filter, ← ring_count]
  simp_rw [← cycle_iff]
  rw [sum_by_first]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact Nat.add_comm _ _

end AscoliDihedral
