module

public import conjectures.SelectiveCompound.Grundy

@[expose] public section
namespace SelectiveCompound.Extremal

inductive State where
  | heap (n : ℕ)
  | delay (m : ℕ)

open State

def previous (q : ℕ) : ℕ → State
  | 0 => heap q
  | m+1 => delay m

def depth (q : ℕ) : State → ℕ
  | heap n => n
  | delay m => q+m+1

inductive Move (q : ℕ) : State → State → Prop
  | heap_step {j n} : j<n → Move q (heap n) (heap j)
  | predecessor (m) : Move q (delay m) (previous q m)
  | filler {j m} : j<m → Move q (delay m) (heap j)

/-- The delayed states form a chain above a heap of size q. -/
def game (q : ℕ) : Game State where
  move := Move q
  depth := depth q
  shorter {a b} edge := by
    cases edge with
    | heap_step h => exact h
    | predecessor m => cases m <;> simp [previous,depth]
    | filler h => simp only [depth]; omega
  deepest a h := by
    cases a with
    | heap n =>
        cases n with
        | zero => exact (Nat.lt_irrefl 0 h).elim
        | succ n => exact ⟨heap n,Move.heap_step (by omega),rfl⟩
    | delay m =>
        refine ⟨previous q m,Move.predecessor m,?_⟩
        cases m <;> simp [previous,depth,Nat.add_assoc]

theorem heap_value (q n k : ℕ) : (game q).grundy (heap n,k) = k+n := by
  have base (n : ℕ) : (game q).grundy (heap n,0) = n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
        have ub := ((game q).bounds (heap n,0)).2
        change (game q).grundy (heap n,0) ≤ n + 0 at ub
        by_contra! ne
        have lt : (game q).grundy (heap n,0)<n := by omega
        exact (game q).excluded (heap n,0) ⟨(heap _,0),Or.inr ⟨Move.heap_step lt,le_rfl⟩,ih _ lt⟩
  have lo := (game q).offset_mono (heap n) (Nat.zero_le k)
  have hi := ((game q).bounds (heap n,k)).2
  change (game q).grundy (heap n,k) ≤ n+k at hi
  rw [base] at lo
  omega

private theorem delay_lower (q m k : ℕ) : k+m ≤ (game q).grundy (delay m,k) := by
  have base : m ≤ (game q).grundy (delay m,0) := by
    by_contra! lt
    apply (game q).excluded (delay m,0)
    exact ⟨(heap _,0),Or.inr ⟨Move.filler lt,le_rfl⟩,by simpa using heap_value q _ 0⟩
  have := (game q).offset_mono (delay m) (Nat.zero_le k)
  omega

/-- The offset is m below the threshold and m+q+1 from the threshold onward. -/
theorem delay_value (q m k : ℕ) : (game q).grundy (delay m,k) =
    if k<(m+1)*q then k+m else k+m+1+q := by
  induction m using Nat.strong_induction_on generalizing k with
  | ind m outer =>
      have pred (i : ℕ) : (game q).grundy (previous q m,i) =
          if i<m*q then i+m-1 else i+m+q := by
        cases m with
        | zero => simp [previous,heap_value]
        | succ j =>
            rw [previous,outer j (by omega)]
            split <;> omega
      induction k using Nat.strong_induction_on with
      | ind k inner =>
          have low := delay_lower q m k
          have cut : (m+1)*q = m*q+q := Nat.succ_mul _ _
          split
          next early =>
            apply le_antisymm _ low
            apply (game q).mex_le
            rintro ⟨⟨b,i⟩,legal,hit⟩
            obtain ⟨rfl,hi⟩ | ⟨step,hi⟩ := legal
            · change i<k at hi
              rw [inner i hi,ite_eq_left (by omega)] at hit
              omega
            · change Move q (delay m) b at step
              change i≤k at hi
              cases step with
              | predecessor =>
                  rw [pred] at hit
                  split at hit
                  next small =>
                    have : 0<m := by
                      by_contra! zero
                      have eq : m=0 := by omega
                      simp [eq] at small
                    omega
                  next => omega
              | filler smaller =>
                  rw [heap_value] at hit
                  omega
          next late =>
            have high := ((game q).bounds (delay m,k)).2
            change (game q).grundy (delay m,k) ≤ q+m+1+k at high
            by_contra! ne
            let g := (game q).grundy (delay m,k)
            have below : g ≤ k+m+q := by dsimp [g]; omega
            have above : k+m ≤ g := low
            have avail : g-(m+q) ≤ k := by omega
            have inLate : ¬(g-(m+q)<m*q) := by omega
            apply (game q).excluded (delay m,k)
            refine ⟨(previous q m,g-(m+q)),Or.inr ⟨Move.predecessor m,avail⟩,?_⟩
            rw [pred,ite_eq_right inLate]
            change g-(m+q)+m+q = g
            omega

/-- At depth p+q the first heap that attains the full depth offset can be exactly pq. -/
theorem exact_threshold (p q : ℕ) : ∃ a : State, (game q).depth a = p+q ∧
    ∀ k, (game q).grundy (a,k) = k+(game q).depth a ↔ p*q ≤ k := by
  cases p with
  | zero =>
      refine ⟨heap q,by change q = 0+q; omega,?_⟩
      intro k
      change (game q).grundy (heap q,k) = k+q ↔ 0*q≤k
      simp [heap_value]
  | succ m =>
      refine ⟨delay m,by change q+m+1 = (m+1)+q; omega,?_⟩
      intro k
      change (game q).grundy (delay m,k) = k+(q+m+1) ↔ (m+1)*q≤k
      rw [delay_value]
      split <;> omega

private theorem balanced_product (p q : ℕ) (h : q=p ∨ q=p+1) :
    p*q=(p+q)^2/4 := by
  rcases h with rfl | rfl <;>
    simp only [pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] <;> omega

/-- For any smaller proposed cutoff, a depth-d position still fails at the last heap below d²/4. -/
theorem sharp_cutoff (d K : ℕ) (h : K<d^2/4) : ∃ (G : Game State) (a : State),
    G.depth a=d ∧ K≤d^2/4-1 ∧ G.grundy (a,d^2/4-1) ≠ d^2/4-1+d ∧
    ∀ k, G.grundy (a,k)=k+d ↔ d^2/4 ≤ k := by
  let p := d/2
  let q := d-p
  have total : p+q=d := by dsimp [p,q]; omega
  have balance : q=p ∨ q=p+1 := by dsimp [p,q]; omega
  have prod : p*q=d^2/4 := (balanced_product p q balance).trans (by rw [total])
  obtain ⟨a,da,cut⟩ := exact_threshold p q
  rw [total] at da
  simp only [da,prod] at cut
  exact ⟨game q,a,da,by omega,fun eq ↦ (show ¬d^2/4≤d^2/4-1 by omega) ((cut _).mp eq),cut⟩

/-- info: 'SelectiveCompound.Extremal.exact_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_threshold

/-- info: 'SelectiveCompound.Extremal.sharp_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharp_cutoff

end SelectiveCompound.Extremal
