module

public import conjectures.MissingSumFringes.Basic
public import conjectures.MissingSumFringes.FiniteCoins
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

def extent (n : ℕ) (A : Finset ℕ) : ℕ := (missing n A).sup (·+1)

def reflect (n : ℕ) (A : Finset ℕ) : Finset ℕ := A.image (fun x ↦ n-1-x)

theorem extent_le (n : ℕ) (A : Finset ℕ) : extent n A ≤ n := by
  apply Finset.sup_le
  intro x hx
  exact mem_range.mp (mem_sdiff.mp hx).1

theorem present_of_extent {n x : ℕ} {A : Finset ℕ} (lo : extent n A ≤ x) (hi : x<n) :
    x∈A+A := by
  by_contra bad
  have h : x ∈ missing n A := mem_sdiff.mpr ⟨mem_range.mpr hi,bad⟩
  have ex := le_sup (f := fun y : ℕ ↦ y+1) h
  change x+1≤extent n A at ex
  omega

theorem below_extent {n : ℕ} {A : Finset ℕ} (h : 0<extent n A) : extent n A-1 ∈ missing n A := by
  by_contra no
  have he : extent n A≤extent n A-1 := by
    apply Finset.sup_le
    intro x hx
    have hx' := le_sup (f := fun y : ℕ ↦ y+1) hx
    change x+1 ≤ extent n A at hx'
    have : x ≠ extent n A-1 := fun eq ↦ no (eq ▸ hx)
    omega
  omega

theorem reflect_twice {n} {A : Finset ℕ} (hA : A⊆range n) : reflect n (reflect n A)=A := by
  unfold reflect
  rw [image_image]
  calc
    _ = A.image id := by
      apply image_congr
      intro x hx
      have := mem_range.mp (hA hx)
      dsimp
      omega
    _ = _ := by simp

theorem reflect_sum {n x : ℕ} {A : Finset ℕ} (hA : A⊆range n) (hn : 0<n) (hx : x<width n) :
    x∈reflect n A + reflect n A ↔ width n-1-x∈A+A := by
  unfold width at *
  simp only [reflect,Finset.mem_add,mem_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,e⟩
    have := mem_range.mp (hA ha)
    have := mem_range.mp (hA hb)
    exact ⟨a,ha,b,hb,by omega⟩
  · rintro ⟨a,ha,b,hb,e⟩
    have := mem_range.mp (hA ha)
    have := mem_range.mp (hA hb)
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,by omega⟩

end MissingSumFringes
