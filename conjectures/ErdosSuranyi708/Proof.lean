module

public import conjectures.ErdosSuranyi708.Transfer
public import conjectures.ErdosSuranyi708.Signed
import Mathlib.Tactic.Linarith

namespace ErdosSuranyi708

public theorem resolution : Conjecture := signed_of_transfer transfer (by decide : 0 < 2)

public theorem positive_inputs : IntegerIntervalBound 1 := signed_of_transfer transfer (by decide)

public theorem erdos_1992 : Erdos1992 := by
  intro ε hε
  obtain ⟨N,hN⟩ := positive_of_transfer transfer (ε/2) (by linarith)
  refine ⟨N, ?_⟩
  intro A hA hn hp x
  obtain ⟨B,hB,hcov,hc⟩ := hN A (M := A.max' hA) hn.le
    (fun a ha ↦ Finset.mem_Ioc.mpr ⟨by have := hp a ha; omega, by simpa using A.le_max' a ha⟩) x
  have hcard : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  exact ⟨B,hB,by nlinarith [mul_pos hε hcard],hcov⟩

end ErdosSuranyi708
