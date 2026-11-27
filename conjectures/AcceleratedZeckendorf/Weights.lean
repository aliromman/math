module

public import conjectures.AcceleratedZeckendorf.Statement
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace AcceleratedZeckendorf
open Finset Multiset

def total (f : ℕ → ℕ) (p : Position) : ℕ := (p.map f).sum

def mass := total coin

def weight : ℕ → ℕ
  | 0 => 5
  | i+1 => 2*(i+1)+6

def work := total weight

@[simp] theorem total_zero (f : ℕ → ℕ) : total f 0 = 0 := rfl

@[simp] theorem total_cons (f : ℕ → ℕ) (i : ℕ) (p : Position) :
    total f (i ::ₘ p) = f i + total f p := by simp [total]

@[simp] theorem total_add (f : ℕ → ℕ) (p q : Position) :
    total f (p+q) = total f p + total f q := by simp [total]

@[simp] theorem total_smul (f : ℕ → ℕ) (k : ℕ) (p : Position) :
    total f (k • p) = k * total f p := by
  induction k with
  | zero => simp
  | succ k ih => simp [succ_nsmul, ih, Nat.succ_mul]

private theorem coin_rec (i : ℕ) : coin (i+2) = coin i + coin (i+1) := Nat.fib_add_two

private theorem mass_move (r : Rule) : total coin (output r) = total coin (input r) := by
  obtain ⟨i,b⟩ := r
  cases b with
  | true => simp only [input, output, total_cons, total_zero, add_zero]; exact coin_rec i
  | false =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ j =>
        simp only [input, output, total_cons, total_zero, add_zero]
        have h := coin_rec j
        have hh : coin (j+3) = coin (j+1) + coin (j+2) := coin_rec (j+1)
        change coin j + coin (j+3) = coin (j+2) + coin (j+2)
        omega

private theorem work_move (r : Rule) : total weight (output r)+1 ≤ total weight (input r) := by
  obtain ⟨i,b⟩ := r
  cases b with
  | true => cases i <;> simp only [input, output, total_cons, total_zero, add_zero, weight] <;> omega
  | false =>
    rcases i with _ | _ | _ | j <;> simp only [input, output, total_cons, total_zero, add_zero, weight] <;> omega

theorem input_le {p : Position} {r : Rule} {k : ℕ} (hk : k ≤ cap p r) : k • input r ≤ p := by
  obtain ⟨i,b⟩ := r
  rw [Multiset.le_iff_count]
  intro z
  cases b with
  | true =>
    simp only [cap, le_min_iff] at hk
    by_cases h : z=i
    · subst z; simpa [input] using hk.1
    · by_cases h' : z=i+1
      · subst z; simpa [input] using hk.2
      · simp [input, h, h']
  | false =>
    simp only [cap] at hk
    by_cases h : z=i
    · subst z
      simp [input]
      omega
    · simp [input, h]

private theorem play_balance (f : ℕ → ℕ) {p : Position} {r : Rule} {k : ℕ}
    (hk : k≤cap p r) :
    total f (play p r k) + k * total f (input r) = total f p + k * total f (output r) := by
  have h := congrArg (total f) (tsub_add_cancel_of_le (input_le hk))
  simp only [total_add, total_smul] at h
  simp only [play, total_add, total_smul]
  omega

theorem play_mass {p : Position} {r : Rule} {k : ℕ} (hk : k≤cap p r) :
    mass (play p r k) = mass p := by
  have h := play_balance coin hk
  rw [mass_move] at h
  exact Nat.add_right_cancel h

theorem play_work {p : Position} {r : Rule} {k : ℕ} (hk : k≤cap p r) :
    work (play p r k) + k ≤ work p := by
  have h := play_balance weight hk
  have h' := Nat.mul_le_mul_left k (work_move r)
  rw [Nat.mul_add, Nat.mul_one] at h'
  unfold work
  omega

def width (n : ℕ) := 2*(Nat.log 2 (n+1)+1)

private theorem coin_mono : Monotone coin := fun _ _ h => Nat.fib_mono (Nat.add_le_add_right h 2)

private theorem power_le_coin (i : ℕ) : 2^i ≤ coin (2*i) := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Nat.mul_succ, coin_rec, pow_succ]
    have h : coin (2*i) ≤ coin (2*i+1) := coin_mono (Nat.le_succ (2*i))
    omega

private theorem single_le_total (f : ℕ → ℕ) (p : Position) {i : ℕ} (hi : i∈p) :
    f i ≤ total f p := by
  induction p using Multiset.induction_on with
  | empty => simp at hi
  | cons j p ih =>
    simp only [total_cons, Multiset.mem_cons] at *
    rcases hi with rfl | h
    · omega
    · have := ih h; omega

theorem index_lt {p : Position} {i : ℕ} (hi : i∈p) : i < width (mass p) := by
  have h₁ := power_le_coin (i/2)
  have h₂ : coin (2*(i/2)) ≤ coin i := coin_mono (by omega)
  have h₃ : coin i ≤ mass p := single_le_total coin p hi
  have h₄ := Nat.le_log_of_pow_le (by decide : 1 < 2) (show 2^(i/2)≤mass p+1 by omega)
  unfold width
  omega

theorem support_le (p : Position) : p.toFinset.card ≤ width (mass p) := by
  calc
    _ ≤ (Finset.range (width (mass p))).card := Finset.card_le_card (fun i hi =>
      Finset.mem_range.mpr (index_lt (Multiset.mem_toFinset.mp hi)))
    _ = _ := Finset.card_range _

theorem work_le (p : Position) : work p ≤ (2 * width (mass p) + 6) * p.card := by
  let M := 2 * width (mass p) + 6
  have ht : ∀ i ∈ p, weight i ≤ M := by
    intro i hi
    have h := index_lt hi
    cases i <;> simp [weight, M]
    omega
  suffices h : ∀ (q : Position), (∀ i ∈ q, weight i ≤ M) → work q ≤ M*q.card from h p ht
  intro q
  induction q using Multiset.induction_on with
  | empty => simp [work]
  | cons i q ih =>
    intro hq
    have h₁ := hq i (by simp)
    have h₂ := ih (fun j hj => hq j (by simp [hj]))
    simp only [work, total_cons, Multiset.card_cons, Nat.mul_succ] at *
    omega

end AcceleratedZeckendorf
