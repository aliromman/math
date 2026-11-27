module

public import conjectures.WheelMatchings.Statement

@[expose] public section

namespace WheelMatchings

abbrev Turn (n : ℕ) := Fin n → Fin n → Fin n → Bool

/-- Extend signs on increasing triples to all orders by alternation. -/
def extend {n : ℕ} (s : Turn n) (a b c : Fin n) : Bool :=
  if a = b ∨ b = c ∨ c = a then false
  else if a < b then
    if b < c then s a b c else if a < c then !s a c b else s c a b
  else if a < c then !s b a c else if b < c then s b c a else !s c b a

def opposite {n : ℕ} (L : Turn n) (a b c d : Fin n) : Bool :=
  (L a b c && L b a d) || (L b a c && L a b d)

def crossCode {n : ℕ} (L : Turn n) (e f : Edge (Fin n)) : Bool :=
  opposite L e.1 e.2 f.1 f.2 && opposite L f.1 f.2 e.1 e.2

def countCode {m : ℕ} (L : Turn (2*m)) (k : ℕ) : ℕ :=
  (matchings m (List.finRange (2*m))).countP fun M ↦ crossingNumber (crossCode L) M == k

private theorem swap (a b c : Point) : orient b a c = -orient a b c := by
  unfold orient
  ring

private theorem cycle (a b c : Point) : orient b c a = orient a b c := by
  unfold orient
  ring

private theorem negate_iff (z : ℝ) {b : Bool} (h : if b then 0 < z else z < 0) :
    (0 < z ↔ b = true) ∧ (z < 0 ↔ (!b) = true) := by
  cases b <;> simp_all [not_lt_of_gt]

private theorem extend_spec {n : ℕ} {p : Fin n → Point} {s : Turn n}
    (h : ∀ i j k, i < j → j < k → if s i j k then 0 < orient (p i) (p j) (p k)
      else orient (p i) (p j) (p k) < 0) (a b c : Fin n) :
    extend s a b c = true ↔ 0 < orient (p a) (p b) (p c) := by
  unfold extend
  split_ifs with he hab hbc hac hac hbc
  · rcases he with rfl | rfl | rfl <;> simp [orient, mul_comm]
  · exact (negate_iff _ (h _ _ _ hab hbc)).1.symm
  · rw [cycle, swap (p a) (p c), neg_pos]
    exact (negate_iff _ (h _ _ _ hac (by omega))).2.symm
  · rw [cycle (p c)]
    exact (negate_iff _ (h _ _ _ (by omega) hab)).1.symm
  · rw [swap (p b) (p a), neg_pos]
    exact (negate_iff _ (h _ _ _ (by omega) hac)).2.symm
  · rw [← cycle]
    exact (negate_iff _ (h _ _ _ hbc (by omega))).1.symm
  · have hr : orient (p a) (p b) (p c) = -orient (p c) (p b) (p a) := by
      unfold orient
      ring
    rw [hr, neg_pos]
    exact (negate_iff _ (h _ _ _ (by omega) (by omega))).2.symm

theorem count_by_signs {m : ℕ} (p : Fin (2*m) → Point) (s : Turn (2*m))
    (h : ∀ i j k, i < j → j < k → if s i j k then 0 < orient (p i) (p j) (p k)
      else orient (p i) (p j) (p k) < 0) (k : ℕ) : count p k = countCode (extend s) k := by
  classical
  have hc : (fun e f ↦ decide (crosses p e f)) = crossCode (extend s) := by
    funext e f
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, crosses, mul_neg_iff, crossCode, opposite,
      Bool.and_eq_true, Bool.or_eq_true, extend_spec h]
    rw [swap (p e.1) (p e.2), swap (p e.1) (p e.2), swap (p f.1) (p f.2), swap (p f.1) (p f.2)]
    simp only [neg_pos]
  unfold count countCode
  rw [hc]

end WheelMatchings
