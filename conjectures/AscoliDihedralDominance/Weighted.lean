module

public import conjectures.AscoliDihedralDominance.Orbits

@[expose] public section
open Finset Equiv
namespace AscoliDihedral

def colorWeight {X : Type*} [Fintype X] (B : ℕ) (f : X → Bool) : ℕ :=
  ∏ x, if f x then B else 1

theorem colorWeight_cons (B n : ℕ) (v : Bool) (f : Fin n → Bool) :
    colorWeight B (Fin.cons v f) = (if v then B else 1) * colorWeight B f := by
  simp [colorWeight,Fin.prod_univ_succ]

private def pathWeight (B n : ℕ) (l r : Bool) : ℕ :=
  ∑ f : Fin n → Bool, if pathOK n l r f then colorWeight B f else 0

private theorem pathWeight_succ (B n : ℕ) (l r : Bool) :
    pathWeight B (n+1) l r = pathWeight B n false r + if l then 0 else B * pathWeight B n true r := by
  unfold pathWeight
  rw [sum_by_first]
  cases l <;> simp [colorWeight_cons,pathOK,mul_sum,mul_ite,add_comm]

private theorem pathWeight_add_two (B n : ℕ) (l r : Bool) :
    pathWeight B (n+2) l r = B * pathWeight B n l r + pathWeight B (n+1) l r := by
  cases l <;> simp only [pathWeight_succ,Bool.false_eq_true,ite_false,ite_true,add_zero] <;> ring

/-- Count weighted independent subsets of a cycle, including a loop or a single edge. -/
def cycleWeight (B : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n+2 => B * cycleWeight B n + cycleWeight B (n+1)

private theorem pathWeight_circle (B n : ℕ) :
    pathWeight B n false false + B*pathWeight B n true true = cycleWeight B (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pathWeight,pathOK,cycleWeight,colorWeight]
  | one =>
    rw [pathWeight_succ,pathWeight_succ]
    simp [pathWeight,pathOK,cycleWeight,colorWeight]
    ring
  | more n h₀ h₁ =>
    change _ = cycleWeight B (n+2) at h₁
    rw [pathWeight_add_two,pathWeight_add_two]
    change _ = B*cycleWeight B (n+1) + cycleWeight B (n+2)
    rw [←h₀,←h₁]
    ring

instance {X : Type*} [Fintype X] (p : X → X) (f : X → Bool) : Decidable (coloringOK p f) := by
  unfold coloringOK
  infer_instance

theorem cycleWeight_eq (B n : ℕ) :
    (∑ f : Fin (n+1) → Bool, if coloringOK next f then colorWeight B f else 0) = cycleWeight B (n+1) := by
  classical
  rw [←pathWeight_circle]
  unfold pathWeight
  have hh (f : Fin (n+1) → Bool) : coloringOK next f ↔
      pathOK n (f 0) (f 0) (fun j => f j.succ) := (cycle_iff f).symm
  simp_rw [hh]
  rw [sum_by_first]
  simp [colorWeight_cons,mul_sum,mul_ite,add_comm]

variable {X : Type*} [Fintype X] [DecidableEq X]

def weightPerm (B : ℕ) (p : X → X) := ∑ f : X → Bool,
  if coloringOK p f then colorWeight B f else 0

theorem weightPerm_subtype (B : ℕ) (p : X → X) :
    weightPerm B p = ∑ f : {f : X → Bool // coloringOK p f}, colorWeight B f.val := by
  classical
  unfold weightPerm
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro x; simp) _

private theorem weightPerm_next (B k : ℕ) (hk : 0<k) : weightPerm B (@next k) = cycleWeight B k := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact cycleWeight_eq B k

omit [DecidableEq X] in
private theorem colorWeight_pieces (B : ℕ) (p : Perm X) (f : {f : X → Bool // coloringOK p f}) :
    colorWeight B f.val = ∏ q : Orbit p, colorWeight B (colorEquiv p f q).val := by
  unfold colorWeight
  calc
    _ = ∏ qi, (if f.val (orbitEquiv p qi) then B else 1) :=
      ((orbitEquiv p).prod_comp (fun x => if f.val x then B else 1)).symm
    _ = _ := by rw [Fintype.prod_sigma]; rfl

theorem weighted_cycle_factors (B : ℕ) (p : Perm X) :
    weightPerm B p = ∏ q : Orbit p, cycleWeight B (period p q.out) := by
  classical
  let T (q : Orbit p) := {f : Fin (period p q.out) → Bool // coloringOK next f}
  rw [weightPerm_subtype]
  calc
    _ = ∑ f : (q : Orbit p) → T q, ∏ q, colorWeight B (f q).val :=
      Fintype.sum_equiv (colorEquiv p) _ _ (colorWeight_pieces B p)
    _ = ∏ q, ∑ f : T q, colorWeight B f.val := (Fintype.prod_sum (κ := T) (fun (q : Orbit p) (f : T q) => colorWeight B f.val)).symm
    _ = _ := prod_congr rfl (fun q _ =>
      (weightPerm_subtype B (@next (period p q.out))).symm.trans
        (weightPerm_next B (period p q.out) (period_pos p q.out)))

end AscoliDihedral
