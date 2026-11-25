module

public import conjectures.YangYergerZhouCube.Statement

public section
namespace YangYergerZhouCube

open Finset

variable {V ι : Type*} {edge : V → V → Prop} {A B C D : Multiset V}

theorem Moves.frame (h : Moves edge A B) (R : Multiset V) : Moves edge (A + R) (B + R) := by
  induction h with
  | refl => exact .refl _
  | step rest adj => simpa [add_assoc, add_comm, add_left_comm] using Moves.step (rest + R) adj
  | trans _ _ ih jh => exact ih.trans jh

theorem Supplies.refl (A : Multiset V) : Supplies edge A A := ⟨0, by simpa using Moves.refl (edge := edge) A⟩

theorem Supplies.trans (h : Supplies edge A B) (k : Supplies edge B C) : Supplies edge A C := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := k
  exact ⟨s+r, by simpa [add_assoc] using hr.trans (hs.frame r)⟩

theorem Supplies.drop (R : Multiset V) : Supplies edge (A+R) A := ⟨R,.refl _⟩

theorem Supplies.add (h : Supplies edge A B) (k : Supplies edge C D) : Supplies edge (A+C) (B+D) := by
  obtain ⟨r,hr⟩ := h
  obtain ⟨s,hs⟩ := k
  refine ⟨r+s,(hr.frame C).trans ?_⟩
  simpa [add_assoc, add_comm, add_left_comm] using hs.frame (B+r)

theorem Supplies.sum (s : Finset ι) (f g : ι → Multiset V) (h : ∀ x ∈ s, Supplies edge (f x) (g x)) :
    Supplies edge (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact .refl _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun x hx => h x (by simp [hx]))

theorem Supplies.one {u v : V} (e : edge u v) : Supplies edge (Multiset.replicate 2 u) {v} :=
  ⟨0, by simpa using Moves.step 0 e⟩

theorem Supplies.transfer {u v : V} (h : edge u v) (t : ℕ) :
    Supplies edge (Multiset.replicate (2*t) u) (Multiset.replicate t v) := by
  induction t with
  | zero => simp; exact .refl _
  | succ t ih =>
    simpa only [Nat.mul_succ, Nat.succ_eq_add_one, Multiset.replicate_add, Multiset.replicate_one] using ih.add (Supplies.one h)

theorem pack_split [DecidableEq ι] (s : Finset ι) {i : ι} (hi : i ∉ s) (node : Finset ι → V) (p : Finset ι → ℕ) :
    pack (insert i s) node p = pack s node p + pack s (fun x => node (insert i x)) (fun x => p (insert i x)) := by
  simp [pack, Finset.sum_powerset_insert hi]

theorem pack_add (s : Finset ι) (node : Finset ι → V) (p q : Finset ι → ℕ) :
    pack s node (fun x => p x + q x) = pack s node p + pack s node q := by
  simp [pack,Multiset.replicate_add,Finset.sum_add_distrib]

theorem pack_transfer [DecidableEq ι] (s : Finset ι) (node far : Finset ι → V) (p q take : Finset ι → ℕ)
    (e : ∀ x ∈ s.powerset, edge (far x) (node x)) (h : ∀ x ∈ s.powerset, 2 * take x ≤ q x) :
    Supplies edge (pack s node p + pack s far q)
      (pack s node (fun x => p x + take x) + pack s far (fun x => q x - 2 * take x)) := by
  let rem x := q x - 2 * take x
  have balance : pack s far q = pack s far (fun x => 2 * take x) + pack s far rem := by
    rw [← pack_add]
    apply Finset.sum_congr rfl
    intro x hx
    have := h x hx
    congr 1
    dsimp [rem]
    omega
  have transfer := Supplies.sum s.powerset _ _ (fun x hx => Supplies.transfer (e x hx) (take x))
  rw [balance,pack_add]
  simpa only [pack,add_assoc,rem] using (Supplies.refl (edge := edge) (pack s node p)).add
    (transfer.add (Supplies.refl (pack s far rem)))

end YangYergerZhouCube
