module

public import conjectures.RestrictedUMinimum.TreeGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

@[expose] public section

namespace RestrictedUMinimum.Tree

/-- Two pinned spin sums with the field weight of the root removed. -/
def spin : Tree → ℤ × ℤ
  | .point => (1, 1)
  | .plant t => let (u, v) := t.spin; (17 * u + 2 * v, 34 * u + v)
  | .merge a b => (a.spin.1 * b.spin.1, a.spin.2 * b.spin.2)

def field : Bool → ℤ | true => 17 | false => 1
def bond (a b : Bool) : ℤ := if a = b then 1 else 2

def edgeWeight (t : Tree) (color : ℕ → Bool) : ℤ :=
  (t.edges.map fun e => bond (color e.1) (color e.2)).prod

private def edgeBond {V : Type*} (c : V → Bool) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => bond (c a) (c b), fun a b => by simp [bond, eq_comm]⟩

private theorem edgeWeight_eq_prod (t : Tree) (c : ℕ → Bool) :
    t.edgeWeight c = ∏ e : t.graph.edgeSet, edgeBond (c ∘ Fin.val) e.val := by
  classical
  rw [edgeWeight, ← Fin.prod_univ_fun_getElem]
  exact Fintype.prod_equiv (Equiv.ofBijective _ (edgeAt_bijective t)) _ _ fun _ => rfl

/-- An unrooted graph isomorphism preserves the edge factors of a spin assignment. -/
theorem edgeWeight_iso {s t : Tree} (f : s.graph ≃g t.graph) {c d : ℕ → Bool}
    (h : ∀ v : Fin s.order, c v.val = d (f v).val) : s.edgeWeight c = t.edgeWeight d := by
  classical
  rw [edgeWeight_eq_prod, edgeWeight_eq_prod]
  apply Fintype.prod_equiv f.mapEdgeSet
  rintro ⟨e, he⟩
  revert he
  induction e using Sym2.inductionOn with
  | _ a b =>
    intro he
    change bond (c a.val) (c b.val) = bond (d (f a).val) (d (f b).val)
    rw [h a, h b]

private theorem weight_congr {t : Tree} {c d : ℕ → Bool} (h : ∀ i ≤ t.branchesSize, c i = d i) :
    t.edgeWeight c = t.edgeWeight d := by
  unfold edgeWeight
  congr 1
  apply List.map_congr_left
  intro e he
  have hb := t.edge_bounds he
  rw [h e.1 (by omega), h e.2 hb.2]

private def shades {n : ℕ} (root : Bool) (c : Fin n → Bool) : ℕ → Bool
  | 0 => root
  | i + 1 => if h : i < n then c ⟨i,h⟩ else false

private def sites {n : ℕ} (c : Fin n → Bool) : ℤ := ∏ i, field (c i)

private def pinnedWeight (t : Tree) (b : Bool) (c : Fin t.branchesSize → Bool) : ℤ :=
  sites c * t.edgeWeight (shades b c)

private theorem weight_plant (t : Tree) (b d : Bool) (c : Fin t.branchesSize → Bool) :
    pinnedWeight t.plant b (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) d c) = field d * bond b d * pinnedWeight t d c := by
  have hshift : t.edgeWeight (fun i => shades b (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) d c) (i + 1)) =
      t.edgeWeight (shades d c) := by
    apply weight_congr
    rintro (_|i) hi
    · simp [shades, Fin.cons_zero]
    · have hb : i < t.branchesSize := by omega
      have ht : i + 1 < t.branchesSize + 1 := by omega
      simp only [shades, dite_eq_left hb, dite_eq_left ht]
      exact Fin.cons_succ (α := fun _ => Bool) d c ⟨i, hb⟩
  have he : t.plant.edgeWeight (shades b (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) d c)) =
      bond b d * t.edgeWeight (shades d c) := by
    rw [← hshift]
    simp [edgeWeight, edges, shades, List.map_map, Function.comp_def]
  change (∏ i : Fin (t.branchesSize+1), field (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) d c i)) * t.plant.edgeWeight (shades b (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) d c)) = _
  rw [he]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, pinnedWeight, sites]
  ring

private theorem weight_merge (a b : Tree) (root : Bool)
    (c : Fin a.branchesSize → Bool) (d : Fin b.branchesSize → Bool) :
    pinnedWeight (a.merge b) root (Fin.append c d) = pinnedWeight a root c * pinnedWeight b root d := by
  let merged := shades root (Fin.append c d)
  have ha : a.edgeWeight merged = a.edgeWeight (shades root c) := by
    apply weight_congr
    rintro (_|i) hi
    · rfl
    · have hc : i < a.branchesSize := by omega
      have ht : i < a.branchesSize+b.branchesSize := by omega
      simp only [merged, shades, dite_eq_left hc, dite_eq_left ht]
      exact Fin.append_left c d ⟨i,hc⟩
  have hb : b.edgeWeight (merged ∘ shift a.branchesSize) = b.edgeWeight (shades root d) := by
    apply weight_congr
    rintro (_|i) hi
    · rfl
    · have hc : i < b.branchesSize := by omega
      have ht : a.branchesSize+i < a.branchesSize+b.branchesSize := by omega
      simp only [Function.comp_apply, merged, shades, shift_succ, dite_eq_left hc, dite_eq_left ht]
      exact Fin.append_right c d ⟨i,hc⟩
  have he : (a.merge b).edgeWeight merged = a.edgeWeight (shades root c) * b.edgeWeight (shades root d) := by
    rw [← ha, ← hb]
    simp [edgeWeight, edges, List.map_map, Function.comp_def]
  change (∏ i, field (Fin.append c d i)) * (a.merge b).edgeWeight merged = _
  rw [he, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, pinnedWeight, sites]
  ring

private def fixed (t : Tree) (b : Bool) : ℤ := ∑ c, pinnedWeight t b c

private theorem fixed_plant (t : Tree) (b : Bool) :
    fixed t.plant b = 17 * bond b true * fixed t true + bond b false * fixed t false := by
  unfold fixed
  change (∑ c : Fin (t.branchesSize + 1) → Bool, _) = _
  rw [← (Fin.consEquiv (fun _ : Fin (t.branchesSize + 1) => Bool)).sum_comp (pinnedWeight t.plant b),
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, weight_plant, field, one_mul, Finset.mul_sum]

private theorem fixed_merge (a b : Tree) (root : Bool) :
    fixed (a.merge b) root = fixed a root * fixed b root := by
  unfold fixed
  change (∑ c : Fin (a.branchesSize + b.branchesSize) → Bool, _) = _
  rw [← (Fin.appendEquiv a.branchesSize b.branchesSize).sum_comp (pinnedWeight (a.merge b) root), Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  simp [Fin.appendEquiv, weight_merge]

private theorem fixed_spin : ∀ t : Tree, fixed t true = t.spin.1 ∧ fixed t false = t.spin.2
  | .point => by
    have h (b : Bool) : fixed .point b = 1 := by
      change (∑ c : Fin 0 → Bool, (∏ i : Fin 0, field (c i)) * (1:ℤ)) = 1
      simp
    exact ⟨h _, h _⟩
  | .plant t => by
    obtain ⟨hp, hm⟩ := fixed_spin t
    simp only [fixed_plant, hp, hm, spin, bond]
    norm_num
  | .merge a b => by
    obtain ⟨hp, hm⟩ := fixed_spin a
    obtain ⟨hq, hn⟩ := fixed_spin b
    simp [fixed_merge, spin, hp, hm, hq, hn]

private def readColor {n : ℕ} (c : Fin n → Bool) (i : ℕ) : Bool :=
  if hi : i < n then c ⟨i, hi⟩ else false

private def colorWeight (t : Tree) (c : Fin t.order → Bool) : ℤ :=
  (∏ i, field (c i)) * t.edgeWeight (readColor c)

private theorem weight_cons (t : Tree) (b : Bool) (tail : Fin t.branchesSize → Bool) :
    colorWeight t (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) b tail) =
      field b * pinnedWeight t b tail := by
  have he : t.edgeWeight (readColor (Fin.cons (α := fun _ : Fin (t.branchesSize + 1) => Bool) b tail)) =
      t.edgeWeight (shades b tail) := by
    apply weight_congr
    rintro (_ | i) hi
    · simp [readColor, shades]
    · have ht : i < t.branchesSize := by omega
      have hu : i + 1 < t.branchesSize + 1 := by omega
      simp only [readColor, shades, dite_eq_left ht, dite_eq_left hu]
      exact Fin.cons_succ (α := fun _ => Bool) b tail ⟨i, ht⟩
  change (∏ i : Fin (t.branchesSize + 1), field (Fin.cons (α := fun _ => Bool) b tail i)) *
    t.edgeWeight (@readColor (t.branchesSize + 1) (Fin.cons (α := fun _ => Bool) b tail)) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, pinnedWeight, sites]
  rw [he]
  ring

private theorem sum_colorWeight (t : Tree) :
    (∑ c, colorWeight t c) = 17 * t.spin.1 + t.spin.2 := by
  change (∑ c : Fin (t.branchesSize + 1) → Bool, colorWeight t c) = _
  rw [← (Fin.consEquiv (fun _ : Fin (t.branchesSize + 1) => Bool)).sum_comp (colorWeight t),
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, weight_cons, field, one_mul, ← Finset.mul_sum]
  exact congrArg₂ (· + ·) (congrArg (17 * ·) (fixed_spin t).1) (fixed_spin t).2

/-- The sum over all spin assignments is an invariant of the unrooted graph. -/
theorem spin_iso {s t : Tree} (h : s.iso t) :
    17 * s.spin.1 + s.spin.2 = 17 * t.spin.1 + t.spin.2 := by
  obtain ⟨f⟩ := h
  rw [← sum_colorWeight, ← sum_colorWeight]
  let e := Equiv.arrowCongr f.toEquiv (Equiv.refl Bool)
  apply Fintype.sum_equiv e
  intro c
  have hc (i : Fin s.order) : c i = e c (f i) := by
    change c i = c (f.symm (f i))
    simp
  apply congrArg₂ (· * ·)
  · exact Fintype.prod_equiv f.toEquiv _ _ (fun i => congrArg field (hc i))
  · apply edgeWeight_iso f
    intro v
    simpa only [readColor, dite_eq_left v.isLt, dite_eq_left (f v).isLt] using hc v

end RestrictedUMinimum.Tree
