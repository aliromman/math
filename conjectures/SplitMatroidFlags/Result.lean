module

public import conjectures.SplitMatroidFlags.Matroids
public import conjectures.SplitMatroidFlags.TableCorrect
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags

def result (flags : ℕ) : Array ℕ := #[flags,144,1518,5146,9224,10368,7802,3970,1324,268,28,1]

private lemma read_result {H : Lines} {L : List ℕ} {n : ℕ} (input : L.toFinset = H.image mask)
    (out : census (rawData L) = result n) (i : Fin 12) :
    (result n)[i.val]! = if i = 0 then table H false 4 else table H true (i.val-1) := by
  rw [raw_data_eq input] at out
  have left : (result n)[i.val]! = (census (basisData H))[i.val]'(by simp [census]) := by
    exact (congrArg (fun v : Array ℕ => v[i.val]!) out.symm).trans (getElem!_pos _ _ (by simp [census]))
  exact left.trans (census_value H i)

theorem different_flags (ca : census (rawData maskA) = result 75887) (cb : census (rawData maskB) = result 75888) :
    ¬ Conjecture := by
  intro h
  have a := read_result masksA ca
  have b := read_result masksB cb
  have same : ∀ k, (faces (bases linesA) k).card = (faces (bases linesB) k).card := by
    intro k
    rw [table_faces matchesA connected.1,table_faces matchesB connected.2]
    by_cases small : k < 11
    · let i : Fin 12 := ⟨k+1,by omega⟩
      have ne : i ≠ 0 := fun e => by have := congrArg Fin.val e; dsimp [i] at this; omega
      have eq : ∀ j : Fin 12, j ≠ 0 → (result 75887)[j.val]! = (result 75888)[j.val]! := by decide +kernel
      have both := (a i).symm.trans ((eq i ne).trans (b i))
      simpa [ne,i] using both
    · rw [table_above (by omega),table_above (by omega)]
  have e := h G G Finset.univ Finset.univ (bases linesA) (bases linesB) splitA splitB same [4,0] (by decide)
  rw [table_flags matchesA connected.1,table_flags matchesB connected.2] at e
  have fa : 75887 = table linesA false 4 := by simpa [result] using a 0
  have fb : 75888 = table linesB false 4 := by simpa [result] using b 0
  omega

end SplitMatroidFlags
