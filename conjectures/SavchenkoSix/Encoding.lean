module

public import conjectures.SavchenkoSix.Minors

@[expose] public section
namespace SavchenkoSix

/-- Triangular numbering of the fifteen signs left after the first row is fixed. -/
def edgeIndex (i j : Fin 7) : Fin 15 :=
  ⟨(((j.val-1)*(j.val-2))/2+(i.val-1))%15, Nat.mod_lt _ (by decide)⟩

def upperEntry (bits : Fin 15 → Bool) (i j : Fin 7) : ℤ :=
  if i=0 then 1 else if bits (edgeIndex i j) then -1 else 1

/-- A switched seven-vertex sign matrix with its first row positive off the diagonal. -/
def bitsMatrix (bits : Fin 15 → Bool) : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j ↦ if i < j then upperEntry bits i j else if j < i then -(upperEntry bits j i) else 0

theorem bitsMatrix_lt (bits : Fin 15 → Bool) {i j : Fin 7} (h : i < j) :
    bitsMatrix bits i j = if i=0 then 1 else if bits (edgeIndex i j) then -1 else 1 := by
  simp [bitsMatrix, upperEntry, h]

theorem bitsMatrix_first (bits : Fin 15 → Bool) {j : Fin 7} (hj : 0 < j) :
    bitsMatrix bits 0 j = 1 := by simp [bitsMatrix_lt bits hj]

theorem bitsMatrix_upper (bits : Fin 15 → Bool) {i j : Fin 7} (hi : 0 < i) (hij : i < j) :
    bitsMatrix bits i j = if bits (edgeIndex i j) then -1 else 1 := by
  simp [bitsMatrix_lt bits hij, ne_of_gt hi]

theorem bitsMatrix_flip (bits : Fin 15 → Bool) (i j : Fin 7) :
    bitsMatrix bits j i = -bitsMatrix bits i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [bitsMatrix, h, not_lt_of_gt h]
  · simp [h, bitsMatrix]
  · simp [bitsMatrix, h, not_lt_of_gt h]

end SavchenkoSix
