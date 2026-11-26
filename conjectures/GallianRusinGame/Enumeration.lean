module

public import conjectures.GallianRusinGame.Factors
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace GallianRusinGame
open Polynomial Finset

def horner (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::s => a+b*horner b s

@[simp] theorem evaluate_list (s : List ℤ) (x : ℤ) : (polynomial s).eval x=horner x s := by
  induction s with
  | nil => simp [polynomial,horner]
  | cons a s ih => simp [polynomial,horner,ih]

private theorem horner_one (s : List ℤ) : horner 1 s=s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [horner,ih]

private theorem nonnegative_iff (s : List ℤ) :
    (∀ j,0≤(polynomial s).coeff j) ↔ ∀ x∈s,0≤x := by
  induction s with
  | nil => simp [polynomial]
  | cons a s ih =>
    constructor
    · intro non x hx
      obtain rfl|hx := List.mem_cons.mp hx
      · simpa using non 0
      · exact ih.mp (fun j ↦ by simpa using non (j+1)) x hx
    · intro all j
      cases j with
      | zero => simpa using all a (by simp)
      | succ j => simpa using ih.mpr (fun x hx ↦ all x (List.mem_cons_of_mem _ hx)) j

def smallBytes : ℕ → ℕ → Bool
  | 0,_ => true
  | k+1,z => decide (z%256<128) && smallBytes k (z/256)

private theorem admissible_bytes {s : List ℤ} (non : ∀ t∈s,0≤t) (total : s.sum≤30) (k : ℕ) :
    smallBytes k (horner 256 s).toNat=true := by
  have hn (s : List ℤ) (hs : ∀ t∈s,0≤t) : 0≤horner 256 s := by
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
      simpa [horner,smallBytes] using ih (s := []) (by simp) (by decide)
    | cons a s =>
      have ha := non a (by simp)
      have ht (x) (hx : x∈s) := non x (List.mem_cons_of_mem _ hx)
      have pos := List.sum_nonneg ht
      have bound : a≤30 := by simp only [List.sum_cons] at total; omega
      have tail := hn s ht
      have enc : (horner 256 (a::s)).toNat=a.toNat+256*(horner 256 s).toNat := by
        simp only [horner]
        omega
      have tailSum : s.sum≤30 := by simp only [List.sum_cons] at total; omega
      rw [smallBytes,enc,Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ (by decide),
        Nat.mod_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega),Nat.zero_add,ih ht tailSum]
      simp [show a.toNat<128 by omega]

def key (c : Code) : ℤ := horner 256 (table 2) * (horner 256 (table 3) *
  (horner 256 (table 5) * (horner 256 (table 6)^c.a * (horner 256 (table 10)^c.b *
  (horner 256 (table 15)^c.c * horner 256 (table 30)^c.d)))))

theorem key_eq (c : Code) : key c=(assemble c).eval 256 := by
  rw [assemble_eq,←table2,←table3,←table5,←table6,←table10,←table15,←table30]
  simp [key,eval_pow]

/-- Each of the three prime-sided dice can have either of the other primes in its increment. -/
def shape (mask : ℕ) : Code :=
  let bit (j : ℕ) := mask/2^j%2
  ⟨bit 0+bit 2,bit 1+bit 4,bit 3+bit 5,bit 0*bit 1+bit 2*bit 3+bit 4*bit 5⟩

def exception : Code := ⟨3,0,0,0⟩

def choices : Finset Code := (range 64).image shape ∪
  {exception,⟨3,0,1,1⟩,⟨3,1,0,1⟩,⟨3,1,1,2⟩}

set_option maxRecDepth 4096

theorem number : choices.card=44 := by decide

set_option maxHeartbeats 2000000 in
private theorem byte_certificate : ∀ a b c d : Fin 11,
    smallBytes 16 (key ⟨a,b,c,d⟩).toNat=true → (⟨a,b,c,d⟩ : Code)∈choices := by decide

theorem valid_choice {c : Code} (p : Die 30 (assemble c))
    (a : c.a<11) (b : c.b<11) (k : c.c<11) (d : c.d<11) : c∈choices := by
  have non := (nonnegative_iff _).mp p.1
  have sum : (coefficients c).sum≤30 := by
    rw [←horner_one,←evaluate_list]
    exact p.2.le
  have digit := admissible_bytes non sum 16
  have eq : key c=horner 256 (coefficients c) := (key_eq c).trans (evaluate_list ..)
  rw [←eq] at digit
  exact byte_certificate ⟨_,a⟩ ⟨_,b⟩ ⟨_,k⟩ ⟨_,d⟩ digit

private theorem die_of_counts (s : List ℤ) (pass : s.all (fun z ↦ decide (0≤z))=true ∧ s.sum=30) :
    Die 30 (polynomial s) :=
  ⟨(nonnegative_iff _).mpr (by simpa using pass.1),by simpa [horner_one] using pass.2⟩

set_option maxHeartbeats 4000000 in
private theorem face_certificate : ∀ c∈choices,
    (coefficients c).all (fun z ↦ decide (0≤z))=true ∧ (coefficients c).sum=30 := by decide

theorem choices_are_dice {c : Code} (h : c∈choices) : Die 30 (assemble c) :=
  die_of_counts _ (face_certificate c h)

theorem distinct_keys : ∀ c∈choices,∀ b∈choices,key c=key b → c=b := by decide

theorem partners : ∀ t∈choices, t≠exception → ∃ u∈choices,∃ v∈choices,
    t.a+u.a+v.a=3 ∧ t.b+u.b+v.b=3 ∧ t.c+u.c+v.c=3 ∧ t.d+u.d+v.d=3 := by decide

theorem exception_no_triple : ∀ u∈choices, ∀ v∈choices,
    key exception * key u * key v ≠ key ⟨1,1,1,1⟩^3 := by decide

end GallianRusinGame
