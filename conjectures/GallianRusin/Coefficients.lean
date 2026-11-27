module

public import conjectures.GallianRusin.Die
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusin
open Polynomial Finset

/-- Read the list of integer coefficients in ascending degree order. -/
noncomputable def polynomial : List ℤ → ℤ[X]
  | [] => 0
  | a :: s => C a + X * polynomial s

def plus : List ℤ → List ℤ → List ℤ
  | [], v => v
  | v, [] => v
  | a :: v, b :: w => (a + b) :: plus v w

def times : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: s, t => plus (t.map (a * ·)) (0 :: times s t)

def power (s : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => times (power s k) s

theorem polynomial_add (s t : List ℤ) : polynomial (plus s t) = polynomial s + polynomial t := by
  induction s generalizing t with
  | nil => simp [plus, polynomial]
  | cons a s ih =>
    cases t with
    | nil => simp [plus, polynomial]
    | cons b t => simp [plus, polynomial, ih]; ring

theorem polynomial_scale (s : List ℤ) (a : ℤ) : polynomial (s.map (a * ·)) = C a * polynomial s := by
  induction s with
  | nil => simp [polynomial]
  | cons b s ih => simp [polynomial, ih]; ring

theorem polynomial_mul (s t : List ℤ) : polynomial (times s t) = polynomial s * polynomial t := by
  induction s with
  | nil => simp [times, polynomial]
  | cons a s ih => simp [times, polynomial_add, polynomial, polynomial_scale, ih]; ring

theorem polynomial_power (s : List ℤ) (k : ℕ) : polynomial (power s k) = polynomial s ^ k := by
  induction k with
  | zero => simp [polynomial, power]
  | succ k ih => rw [power, polynomial_mul, ih, pow_succ]

@[simp] theorem coefficient (s : List ℤ) (j : ℕ) : (polynomial s).coeff j = s[j]?.getD 0 := by
  induction s generalizing j with
  | nil => simp [polynomial]
  | cons a s ih =>
    cases j with
    | zero => simp [polynomial]
    | succ j =>
      simp [polynomial, ih, coeff_X_mul]
      exact coeff_C_of_ne_zero (Nat.succ_ne_zero _)

theorem polynomial_standard (m : ℕ) : polynomial (List.replicate m 1) = standard m := by
  induction m with
  | zero => simp [standard, polynomial]
  | succ m ih =>
    rw [List.replicate_succ, polynomial, ih]
    simp only [standard, sum_range_succ', C_1, pow_zero]
    rw [mul_sum]
    simp [pow_succ', add_comm]

def multiply : List (List ℤ) → List ℤ
  | [] => [1]
  | s :: t => times s (multiply t)

theorem polynomial_multiply (v : List (List ℤ)) :
    polynomial (multiply v) = (v.map polynomial).prod := by
  induction v with
  | nil => simp [multiply, polynomial]
  | cons a v ih => simp [multiply, polynomial_mul, ih]

theorem table_product (table : ℕ → List ℤ) {m} (s : List ℕ)
    (h : multiply (s.map table) = List.replicate m 1) :
    (s.map (fun d ↦ polynomial (table d))).prod = standard m := by
  rw [←polynomial_standard, ←h, polynomial_multiply, List.map_map]
  rfl

def horner (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: s => a + b * horner b s

@[simp] theorem evaluate_list (s : List ℤ) (x : ℤ) : (polynomial s).eval x = horner x s := by
  induction s with
  | nil => simp [polynomial, horner]
  | cons a s ih => simp [polynomial, horner, ih]

theorem horner_one (s : List ℤ) : horner 1 s = s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [horner, ih]

theorem nonnegative_iff (s : List ℤ) :
    (∀ j, 0 ≤ (polynomial s).coeff j) ↔ ∀ x ∈ s, 0 ≤ x := by
  induction s with
  | nil => simp [polynomial]
  | cons a s ih =>
    constructor
    · intro non x hx
      obtain rfl|hx := List.mem_cons.mp hx
      · simpa using non 0
      · exact ih.mp (fun j ↦ by simpa using non (j + 1)) x hx
    · intro all j
      cases j with
      | zero => simpa using all a (by simp)
      | succ j => simpa using ih.mpr (fun x hx ↦ all x (List.mem_cons_of_mem _ hx)) j

/-- Check that each of the first `k` base-256 digits is less than 128. -/
def smallBytes : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, z => decide (z % 256 < 128) && smallBytes k (z / 256)

theorem admissible_bytes {s : List ℤ} (non : ∀ t ∈ s, 0 ≤ t) (total : s.sum < 128) (k : ℕ) :
    smallBytes k (horner 256 s).toNat = true := by
  have hn (s : List ℤ) (hs : ∀ t ∈ s, 0 ≤ t) : 0 ≤ horner 256 s := by
    induction s with
    | nil => decide
    | cons a s ih =>
      have ha := hs a (by simp)
      have ht := ih (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx))
      simp only [horner]
      omega
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases s with
    | nil =>
      simpa [horner, smallBytes] using ih (s := []) (by simp) (by decide)
    | cons a s =>
      have ha := non a (by simp)
      have ht (x) (hx : x ∈ s) := non x (List.mem_cons_of_mem _ hx)
      have pos := List.sum_nonneg ht
      have bound : a < 128 := by simp only [List.sum_cons] at total; omega
      have tail := hn s ht
      have enc : (horner 256 (a :: s)).toNat = a.toNat + 256 * (horner 256 s).toNat := by
        simp only [horner]
        omega
      have tailSum : s.sum < 128 := by simp only [List.sum_cons] at total; omega
      rw [smallBytes, enc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide),
        Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add, ih ht tailSum]
      simp [show a.toNat < 128 by omega]

theorem die_of_counts {m : ℕ} (s : List ℤ)
    (pass : s.all (fun z ↦ decide (0 ≤ z)) = true ∧ s.sum = m) :
    Die m (polynomial s) :=
  ⟨(nonnegative_iff _).mpr (by simpa using pass.1), by simpa [horner_one] using pass.2⟩

end GallianRusin
