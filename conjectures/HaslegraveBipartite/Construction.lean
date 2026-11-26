module

public import conjectures.HaslegraveBipartite.Growth
import Mathlib.Tactic.Ring

@[expose] public section
namespace HaslegraveBipartite

abbrev Side (N : ℕ) := Fin (N+1)
abbrev Vertex (N : ℕ) := Side N ⊕ Side N

def shifts (B d : ℕ) := insert 0 ((Finset.range d).image (B ^ ·))

def across (B d : ℕ) {N : ℕ} (x y : Side N) : Prop :=
  ∃ s ∈ shifts B d, y.val = x.val + s

def adjacent (B d : ℕ) {N : ℕ} : Vertex N → Vertex N → Prop
  | .inl x, .inr y | .inr y, .inl x => across B d x y
  | _, _ => False

def graph (B d N : ℕ) : SimpleGraph (Vertex N) where
  Adj := adjacent B d
  symm := ⟨by rintro (x|x) (y|y) h <;> exact h⟩
  loopless := ⟨by rintro (x|x) <;> exact id⟩

theorem bipartite (B d N : ℕ) : (graph B d N).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) ?_⟩
  rintro (x|x) (y|y) h
  · exact False.elim h
  · exact zero_ne_one
  · exact one_ne_zero
  · exact False.elim h

theorem connected {B d N : ℕ} (dim : 0<d) : (graph B d N).Connected := by
  let G := graph B d N
  have one : 1∈shifts B d := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr dim,pow_zero _⟩)
  have rung (x : Side N) : G.Adj (.inl x) (.inr x) :=
    ⟨0,Finset.mem_insert_self ..,by simp⟩
  have lhs (i : Side N) : G.Reachable (.inl 0) (.inl i) := by
    induction i using Fin.induction with
    | zero => exact .refl _
    | succ i ih =>
      have step : G.Adj (.inl i.castSucc) (.inr i.succ) := ⟨1,one,rfl⟩
      exact (ih.trans step.reachable).trans (rung i.succ).symm.reachable
  have both (v : Vertex N) : G.Reachable (.inl 0) v := by
    cases v with
    | inl i => exact lhs i
    | inr i => exact (lhs i).trans (rung i).reachable
  exact ⟨fun x y => (both x).symm.trans (both y)⟩

private theorem edge_labels {B d N} (f : Vertex N ↪ ℤ) (op : ℤ → ℤ → ℤ)
    (comm : ∀ x y, op x y = op y x) {D : Finset ℤ}
    (h : ∀ x y, across B d x y → op (f (.inl x)) (f (.inr y)) ∈ D) :
    ∀ x y, (graph B d N).Adj x y → op (f x) (f y) ∈ D := by
  rintro (x|x) (y|y) e
  · exact False.elim e
  · exact h _ _ e
  · rw [comm]; exact h _ _ e
  · exact False.elim e

private def sumLabel (N : ℕ) : Vertex N ↪ ℤ where
  toFun := Sum.elim (fun x => (x.val:ℤ)) (fun y => -(y.val:ℤ)-1)
  inj' := by
    rintro (x|x) (y|y) h <;> simp only [Sum.elim_inl,Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))

private def diffLabel (N : ℕ) : Vertex N ↪ ℤ where
  toFun := Sum.elim (fun x => 2*(x.val:ℤ)) (fun y => 2*(y.val:ℤ)-1)
  inj' := by
    rintro (x|x) (y|y) h <;> simp only [Sum.elim_inl,Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))

theorem admits_sum (B d N : ℕ) : Admits (graph B d N) (· + ·) (d+1) := by
  let palette := (shifts B d).image fun (s : ℕ) => -(s:ℤ)-1
  refine ⟨sumLabel N,palette,?_,edge_labels _ _ Int.add_comm ?_⟩
  · apply Finset.card_image_le.trans
    exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right
      (Finset.card_image_le.trans_eq (Finset.card_range d)) _)
  · rintro x y ⟨s,hs,e⟩
    apply Finset.mem_image.mpr
    refine ⟨s,hs,?_⟩
    change -(s:ℤ)-1 = (x.val:ℤ) + (-(y.val:ℤ)-1)
    omega

theorem admits_diff (B d N : ℕ) (pos : 0<B) (dim : 0<d) :
    Admits (graph B d N) (fun a b => |a-b|) d := by
  let D := (Finset.range d).image fun i => 2*((B^i:ℕ):ℤ)-1
  refine ⟨diffLabel N,D,Finset.card_image_le.trans_eq (Finset.card_range d),
    edge_labels _ _ abs_sub_comm ?_⟩
  rintro x y ⟨s,hs,e⟩
  rcases Finset.mem_insert.mp hs with zero | member
  · refine Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr dim,?_⟩
    change 2*((B^0:ℕ):ℤ)-1 = |2*(x.val:ℤ)-(2*(y.val:ℤ)-1)|
    simp only [pow_zero,Nat.cast_one]
    rw [abs_of_nonneg (by omega)]
    omega
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp member
    refine Finset.mem_image.mpr ⟨i,hi,?_⟩
    have p := Nat.pow_pos pos (n := i)
    change 2*((B^i:ℕ):ℤ)-1 = |2*(x.val:ℤ)-(2*(y.val:ℤ)-1)|
    rw [abs_of_nonpos (by omega)]
    omega

end HaslegraveBipartite
