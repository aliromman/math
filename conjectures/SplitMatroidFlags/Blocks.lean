module

public import conjectures.SplitMatroidFlags.InputData

@[expose] public section

namespace SplitMatroidFlags

@[simp] lemma census_size (D : List BasisData) : (census D).size = 12 := by simp [census]

private lemma census_sum (D : List BasisData) (i : ℕ) (h : i < 12) :
    (census D)[i]'(by simpa using h) = (D.map fun b => (basisTags b).countP (bin i)).sum := by
  refine (accumulate_value D (Array.replicate 12 0) i (by simpa using h)).trans ?_
  simp

private lemma census_append (D T : List BasisData) :
    census (D ++ T) = Array.zipWith (·+·) (census D) (census T) := by
  apply Array.ext (by simp)
  intro i hi _
  have small : i < 12 := by simpa using hi
  simp only [Array.getElem_zipWith,census_sum _ i small,List.map_append,List.sum_append]

def batch (D : List BasisData) (n : ℕ) := census ((D.drop (8*n)).take 8)

def batches (D : List BasisData) : ℕ → Array ℕ
  | 0 => Array.replicate 12 0
  | n+1 => Array.zipWith (· + ·) (batches D n) (batch D n)

private lemma batches_eq (D : List BasisData) (n : ℕ) : batches D n = census (D.take (8*n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [batches,ih,Nat.mul_succ,List.take_add,census_append]
    rfl

lemma census_of_batches (D : List BasisData) {v : Array ℕ} (n : ℕ) (length : D.length ≤ 8*n)
    (values : batches D n = v) : census D = v := by
  rwa [batches_eq,List.take_of_length_le length] at values

/-- Check a batch of eight bases against its twelve face and incidence counts. -/
macro "verify_batch " id:ident " in " L:ident " at " i:num " gives " v:term : command =>
  `(private theorem $id : batch (rawData $L) $i = $v := by decide +kernel)

end SplitMatroidFlags
