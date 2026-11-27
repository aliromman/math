module

public import conjectures.WangLocalDensity.Enumeration
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace WangLocalDensity
open Finset
open scoped BigOperators
variable {n : ℕ}

def decode (a : BitVec n) : Finset (Fin n) := univ.filter fun i ↦ a.getLsbD i.val

@[simp] theorem mem_decode {a : BitVec n} {i : Fin n} : i ∈ decode a ↔ a.getLsbD i.val := by
  simp [decode]

theorem decode_injective (n : ℕ) : Function.Injective (@decode n) := by
  intro a b e
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have h : (⟨i,hi⟩:Fin n)∈decode a ↔ ⟨i,hi⟩∈decode b := by rw [e]
  simpa using h

def oneBit (i : Fin n) : BitVec n := (1 : BitVec n) <<< i.val

@[simp] theorem decode_one (j : Fin n) : decode (oneBit j) = {j} := by
  ext i
  rw [mem_decode,mem_singleton]
  change (1#n <<< j.val).getLsbD i.val = true ↔ i=j
  rw [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one]
  have hn : 0<n := Nat.zero_lt_of_lt j.isLt
  simp [hn,i.isLt,Fin.ext_iff]
  omega

@[simp] theorem decode_or (a b : BitVec n) : decode (a ||| b) = decode a ∪ decode b := by
  ext i
  simp

theorem bits_subset (a b : BitVec n) : decode a ⊆ decode b ↔ a &&& b = a := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h i hi
    have h' : a.getLsbD i → b.getLsbD i :=
      fun e ↦ mem_decode.mp (h (x:=⟨i,hi⟩) (mem_decode.mpr e))
    simp only [BitVec.getLsbD_and]
    cases h₁ : a.getLsbD i <;> cases h₂ : b.getLsbD i <;> simp_all
  · intro h i e
    have H := h i.val i.isLt
    simp only [BitVec.getLsbD_and,mem_decode.mp e,Bool.true_and] at H
    exact mem_decode.mpr H

def maskDensity (F : Finset (BitVec n)) (a : BitVec n) : ℚ :=
  let U := F.filter (fun b ↦ a &&& b = a)
  ((∑ b∈U,((decode b).card-(decode a).card)) : ℕ) / ((U.card*(n-(decode a).card) : ℕ) : ℚ)

theorem density_image (F : Finset (BitVec n)) (a : BitVec n) :
    familyDensity (F.image decode) (decode a) = maskDensity F a := by
  classical
  unfold familyDensity maskDensity
  rw [filter_image]
  simp only [bits_subset,Fintype.card_fin,card_image_of_injective _ (decode_injective n)]
  rw [Finset.sum_image]
  exact (decode_injective n).injOn

end WangLocalDensity
