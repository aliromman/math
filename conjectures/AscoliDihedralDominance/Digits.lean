module

public import conjectures.AscoliDihedralDominance.Moments

@[expose] public section
open Finset
namespace AscoliDihedral

variable {X : Type*} [Fintype X]

def familyWeight (B : ℕ) (S : Finset (Finset X)) : ℕ := ∑ A ∈ S, B^A.card

def slice (S : Finset (Finset X)) (m : ℕ) := S.filter fun A => A.card=m

def digit (B m a : ℕ) := a / B^m % B

theorem digit_sum_range (B N m : ℕ) (f : ℕ→ℕ) (h : m<N) (hc : ∀k,f k<B) :
    digit B m (∑ t ∈ range N, f t*B^t) = f m := by
  have hb : 0<B := (Nat.zero_le _).trans_lt (hc 0)
  let encode (k : ℕ) := ∑ t ∈ range k, f t*B^t
  have hlow (k : ℕ) : encode k < B^k := by
    induction k with
    | zero => simp [encode]
    | succ k ih =>
      change (∑ t ∈ range (k+1), f t*B^t) < _
      rw [sum_range_succ,pow_succ]
      change encode k + f k*B^k < _
      have hm := Nat.mul_le_mul_right (B^k) (Nat.succ_le_of_lt (hc k))
      rw [Nat.succ_mul] at hm
      nlinarith
  have hsplit : ∃ u, encode N =
      encode m + f m*B^m + u*B^(m+1) := by
    induction N,h using Nat.le_induction with
    | base => exact ⟨0,by simp [encode,sum_range_succ]⟩
    | succ k _ ih =>
      obtain ⟨u,hu⟩ := ih
      have hk : m+1≤k := by omega
      use u+f k*B^(k-(m+1))
      change (∑ t ∈ range (k+1), f t*B^t) = _
      rw [sum_range_succ,show (∑ t ∈ range k, f t*B^t) = encode k from rfl, hu]
      rw [add_mul,mul_assoc,←pow_add,Nat.sub_add_cancel hk]
      omega
  obtain ⟨u,hu⟩ := hsplit
  change digit B m (encode N) = f m
  rw [digit,hu,pow_succ B m]
  have he : encode m+f m*B^m+u*(B^m*B) = encode m+(f m+u*B)*B^m := by ring
  rw [he,Nat.add_mul_div_right _ _ (pow_pos hb m),Nat.div_eq_of_lt (hlow m),zero_add,
    Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (hc m)]

theorem familyWeight_expansion (B : ℕ) (S : Finset (Finset X)) :
    familyWeight B S = ∑ k ∈ range (Fintype.card X + 1), (slice S k).card * B^k := by
  have H := Finset.sum_fiberwise_of_maps_to' (s := S) (t := range (Fintype.card X+1))
    (g := Finset.card) (fun A _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ A))) (fun k => B^k)
  simpa [familyWeight,slice] using H.symm

theorem packed_digit {Y : Type*} (B : ℕ) (T : Finset Y) (R : Y → Finset (Finset X)) (m : ℕ)
    (hm : m≤Fintype.card X) (hB : T.card*2^Fintype.card X<B) :
    digit B m (∑ y∈T,familyWeight B (R y)) = ∑ y∈T,(slice (R y) m).card := by
  have H : (∑ y∈T,familyWeight B (R y)) =
      ∑ k∈range (Fintype.card X+1), (∑ y∈T,(slice (R y) k).card)*B^k := by
    simp_rw [familyWeight_expansion]
    rw [sum_comm]
    simp only [sum_mul]
  rw [H]
  apply digit_sum_range _ _ _ _ (by omega)
  intro k
  apply lt_of_le_of_lt _ hB
  calc
    _ ≤ ∑ _y∈T,2^Fintype.card X := sum_le_sum fun y _ => by simpa using card_le_univ (slice (R y) k)
    _ = _ := by simp

end AscoliDihedral
