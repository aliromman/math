module
public import conjectures.HwangPermanent.Counts
public import conjectures.HwangPermanent.Border
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace HwangPermanent

open Polynomial Finset Equiv

private def initial {R : Type*} [CommSemiring R] : R[X] :=
  5 + 269 * X + 1818 * X ^ 2 + 5250 * X ^ 3 + 7536 * X ^ 4 + 5280 * X ^ 5 + 1440 * X ^ 6

private theorem degree_gen {n} (A : Matrix (Fin n) (Fin n) ℤ) : (gen A).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ ↦
      (natDegree_add_le (C (A (σ i) i)) X).trans (by simp)
    _ = n := by simp

set_option maxRecDepth 100000 in
private theorem initial_identity :
    gen (board 8 witness) = gen (board 8 (antidiagonal 8 4)) + initial := by
  apply eq_of_natDegree_lt_card_of_eval_eq _ _
    (f := fun i : Fin 9 ↦ ((i : ℕ) : ℤ)) (by intro i j h; exact Fin.ext (Int.ofNat_inj.mp h))
  · intro i
    rw [eval_gen, eval_add, eval_gen]
    rw [ryser (n := 8) (fun a b ↦ board 8 witness a b + (i : ℕ)),
      ryser (n := 8) (fun a b ↦ board 8 (antidiagonal 8 4) a b + (i : ℕ))]
    simp only [initial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow]
    revert i
    decide +kernel
  · have hd : (initial : ℤ[X]).natDegree ≤ 8 := by unfold initial; compute_degree; decide
    have ha := degree_gen (board 8 (antidiagonal 8 4))
    have hb := degree_gen (board 8 witness)
    have hc := (natDegree_add_le (gen (board 8 (antidiagonal 8 4))) initial).trans (max_le ha hd)
    simpa only [Fintype.card_fin] using (lt_of_le_of_lt (max_le hb hc) (by decide : 8 < 9))

/-- The last new index is `none`, the first is `some none`, and the old indices lie in between. -/
private def coords (n : ℕ) : Option (Option (Fin n)) ≃ Fin (n + 2) :=
  ((finSuccEquiv n).symm.optionCongr).trans (finSuccEquiv' (Fin.last (n+1))).symm

private theorem coords_none {n} : coords n none = Fin.last (n+1) := by
  rfl

private theorem coords_first {n} : coords n (some none) = 0 := by
  change (Fin.last (n+1)).succAbove ((finSuccEquiv n).symm none) = 0
  rw [finSuccEquiv_symm_none, Fin.succAbove_last]
  rfl

private theorem coords_mid {n} (i : Fin n) : coords n (some (some i)) = i.succ.castSucc := by
  change (Fin.last (n+1)).succAbove ((finSuccEquiv n).symm (some i)) = _
  rw [finSuccEquiv_symm_some, Fin.succAbove_last]

private def old {α : Type*} : α ↪ Option (Option α) :=
  ⟨fun i ↦ some (some i), by intro a b e; simpa using e⟩

private theorem old_apply {α} (a : α) : old a = some (some a) := rfl

private def padded {n} (s : Finset (Fin n × Fin n)) : Finset (Fin (n+2) × Fin (n+2)) :=
  (insert (some none, none) (s.map (old.prodMap old))).map
    ((coords n).prodCongr (coords n)).toEmbedding

private theorem mem_padded {n} (s : Finset (Fin n × Fin n)) (i j : Option (Option (Fin n))) :
    (coords n i, coords n j) ∈ padded s ↔ match i, j with
    | some none, none => True
    | some (some a), some (some b) => (a,b) ∈ s
    | _, _ => False := by
  change (coords n |>.prodCongr (coords n)) (i,j) ∈
    (insert (some none, none) (s.map (old.prodMap old))).map _ ↔ _
  rw [mem_map_equiv]
  simp only [symm_apply_apply, mem_insert, mem_map]
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp [old_apply]


private theorem card_padded {n} (s : Finset (Fin n × Fin n)) :
    (padded s).card = s.card + 1 := by
  unfold padded
  rw [card_map, card_insert_of_notMem, card_map]
  simp [mem_map, old_apply]

private theorem upper_padded {n} (s : Finset (Fin n × Fin n))
    (h : ∀ p ∈ s, p.1 < p.2) : ∀ p ∈ padded s, p.1 < p.2 := by
  rintro ⟨a,b⟩ hp
  obtain ⟨i,rfl⟩ := (coords n).surjective a
  obtain ⟨j,rfl⟩ := (coords n).surjective b
  rw [mem_padded] at hp
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp_all [coords_none, coords_first, coords_mid]
  change 0 < n+1
  omega

private theorem antidiagonal_padded {n d} (hd : 2*d ≤ n) :
    antidiagonal (n+2) (d+1) = padded (antidiagonal n d) := by
  ext ⟨a,b⟩
  obtain ⟨i,rfl⟩ := (coords n).surjective a
  obtain ⟨j,rfl⟩ := (coords n).surjective b
  rw [mem_padded]
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp [antidiagonal, coords_none, coords_first, coords_mid] <;> omega

private theorem board_padded {n} (s : Finset (Fin n × Fin n)) :
    (board (n+2) (padded s)).submatrix (coords n) (coords n) = wrap (board n s) := by
  ext i j
  have hm := mem_padded s i j
  rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
    simp_all [board, wrap, border, edge, coords_none, coords_first, coords_mid,
      Matrix.submatrix_apply]
  exact Fin.le_last _

private theorem gen_padded {n} (s : Finset (Fin n × Fin n)) :
    gen (board (n+2) (padded s)) = step (gen (board n s)) := by
  rw [← gen_reindex (coords n), board_padded, gen_wrap]

private theorem step_map (P : ℕ[X]) :
    (step P).map (Nat.castRingHom ℤ) = step (P.map (Nat.castRingHom ℤ)) := by
  simp [step, triangular, derivative_map]

private def gap : ℕ → ℕ[X]
  | 0 => initial
  | r+1 => step (gap r)

private theorem gap_pos (r : ℕ) : 0 < (gap r).eval 0 := by
  induction r with
  | zero => simp [gap, initial]
  | succ r ih => simp [gap, step, triangular]; omega

private def cells : (r : ℕ) → Finset (Fin (2*(r+4)) × Fin (2*(r+4)))
  | 0 => witness
  | r+1 => padded (cells r)

private theorem cells_card (r : ℕ) : (cells r).card = r+4 := by
  induction r with
  | zero => decide
  | succ r ih => rw [cells, card_padded, ih]

private theorem cells_upper (r : ℕ) : ∀ p ∈ cells r, p.1 < p.2 := by
  induction r with
  | zero => decide
  | succ r ih => exact upper_padded _ ih

private theorem identity (r : ℕ) : gen (board _ (cells r)) =
    gen (board _ (antidiagonal (2*(r+4)) (r+4))) + (gap r).map (Nat.castRingHom ℤ) := by
  induction r with
  | zero => simpa [cells, gap, initial] using initial_identity
  | succ r ih =>
    change gen (board _ (padded (cells r))) =
      gen (board _ (antidiagonal (2*(r+4)+2) (r+4+1))) + (step (gap r)).map _
    rw [antidiagonal_padded (le_refl _), gen_padded, gen_padded, ih, step_add, step_map]

/-- At every even order from eight onward, the antidiagonal fails at the allowed endpoint. -/
theorem even_counterexamples (r : ℕ) :
    ∃ s : Finset (Fin (2*(r+4)) × Fin (2*(r+4))), s.card = r+4 ∧
      (∀ p ∈ s, p.1 < p.2) ∧
      (board _ (antidiagonal (2*(r+4)) (r+4))).permanent < (board _ s).permanent := by
  refine ⟨cells r, cells_card r, cells_upper r, ?_⟩
  have he := congrArg (Polynomial.eval (0 : ℤ)) (identity r)
  have ev {n} (A : Matrix (Fin n) (Fin n) ℤ) : (gen A).eval 0 = A.permanent := by
    rw [eval_gen]
    simp
  change (gen _).eval 0 = (gen _ + _).eval 0 at he
  rw [eval_add, ev, ev, ← coeff_zero_eq_eval_zero, coeff_map] at he
  change _ = _ + (((gap r).coeff 0 : ℕ) : ℤ) at he
  rw [he]
  apply lt_add_of_pos_right
  exact_mod_cast (coeff_zero_eq_eval_zero (gap r) ▸ gap_pos r)

/-- info: 'HwangPermanent.even_counterexamples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_counterexamples

theorem resolution : ¬ Conjecture := by
  intro h
  have hle := h 8 4 (by decide) (by decide) witness (by decide) (by decide)
  rw [exact_permanents.1, exact_permanents.2] at hle
  contradiction

/-- info: 'HwangPermanent.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end HwangPermanent
end
