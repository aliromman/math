module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

@[expose] public section
namespace SavchenkoSix
open Finset Matrix

variable {V : Type*} [Fintype V]
private theorem sum_cons (n : ℕ) (f : (Fin (n+1)→V)→ℤ) :
    ∑ x,f x = ∑ a,∑ p : Fin n→V, f (Fin.cons a p) := by
  simpa [Fin.consEquiv,Fintype.sum_prod_type] using
    ((Fin.consEquiv (fun _ ↦ V)).sum_comp f).symm

theorem sum_four (g : V→V→V→V→ℤ) :
    ∑ x : Fin 4→V, g (x 0) (x 1) (x 2) (x 3) = ∑ a,∑ b,∑ c,∑ d,g a b c d := by
  simp only [sum_cons,Fintype.sum_unique]
  rfl

theorem sum_six (g : V→V→V→V→V→V→ℤ) :
    ∑ x : Fin 6→V, g (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) =
    ∑ a,∑ b,∑ c,∑ d,∑ e,∑ f,g a b c d e f := by
  simp only [sum_cons,Fintype.sum_unique]
  rfl

/-- Relabeling the positions of an ordered tuple preserves its sum. -/
theorem sum_rotate {m : ℕ} (e : Fin m ≃ Fin m) (g : (Fin m→V)→ℤ) :
    ∑ x : Fin m→V,g (x∘e) = ∑ x : Fin m→V,g x :=
  (e.symm.arrowCongr (Equiv.refl V)).sum_comp g

theorem sum_injections [DecidablePred (fun f : Fin 6→V ↦ Function.Injective f)] (g : (Fin 6→V)→ℤ) :
    ∑ f : Fin 6 ↪ V,g f = ∑ f : Fin 6→V, if Function.Injective f then g f else 0 := by
  classical
  rw [←sum_filter]
  apply sum_bij (fun (f : Fin 6 ↪ V) _ ↦ (f : Fin 6→V))
  · intro f _
    exact mem_filter.mpr ⟨mem_univ _,f.injective⟩
  · intro _ _ _ _ eq
    exact DFunLike.coe_injective eq
  · intro f hf
    exact ⟨⟨f,(mem_filter.mp hf).2⟩,mem_univ _,rfl⟩
  · intro _ _
    rfl

variable [DecidableEq V]
def closed6 (A : Matrix V V ℤ) (a b c d e f : V) : ℤ :=
  A a b * A b c * A c d * A d e * A e f * A f a

def closed4 (A : Matrix V V ℤ) (a b c d : V) : ℤ :=
  A a b * A b c * A c d * A d a

theorem trace6 (A : Matrix V V ℤ) :
    (A^6).trace = ∑ a,∑ b,∑ c,∑ d,∑ e,∑ f,closed6 A a b c d e f := by
  change ∑ i, (A^6) i i = _
  rw [show A^6=A*(A*(A*(A*(A*A)))) by noncomm_ring]
  simp only [Matrix.mul_apply,Finset.mul_sum,closed6,mul_assoc]

theorem trace4 (A : Matrix V V ℤ) :
    (A^4).trace = ∑ a,∑ b,∑ c,∑ d,closed4 A a b c d := by
  change ∑ i, (A^4) i i = _
  rw [show A^4=A*(A*(A*A)) by noncomm_ring]
  simp only [Matrix.mul_apply,Finset.mul_sum,closed4,mul_assoc]

end SavchenkoSix
