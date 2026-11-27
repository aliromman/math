import conjectures.BorgSignedSets.Statement
import conjectures.BorgSignedSets.Product
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

def restrictWord (B : Finset ι) (x : Cube ι (ZMod k)) : Word B k := fun i => x i

def extensions (B : Finset ι) (W : Finset (Word B k)) : Finset (Cube ι (ZMod k)) :=
  Finset.univ.filter fun x => restrictWord B x ∈ W

@[simp] theorem mem_extensions (B : Finset ι) (W : Finset (Word B k)) (x : Cube ι (ZMod k)) :
    x ∈ extensions B W ↔ restrictWord B x ∈ W := by simp [extensions]

theorem card_extensions (B : Finset ι) (W : Finset (Word B k)) :
    (extensions B W).card = W.card * k^(Fintype.card ι-B.card) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ B) (fun _ => ZMod k)
  have eq : (extensions B W).map e.toEmbedding =
      W ×ˢ (Finset.univ : Finset ({i : ι // i ∉ B} → ZMod k)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hp
      exact Finset.mem_product.mpr ⟨(mem_extensions _ _ _).mp hx, Finset.mem_univ _⟩
    · intro hp
      apply Finset.mem_map.mpr
      refine ⟨e.symm p, (mem_extensions _ _ _).mpr ?_, e.apply_symm_apply _⟩
      have he := congrArg Prod.fst (e.apply_symm_apply p)
      change restrictWord B (e.symm p) = p.1 at he
      rw [he]
      exact (Finset.mem_product.mp hp).1
  have card := congrArg Finset.card eq
  simpa only [Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_coe] using card

def shiftWord (t : ZMod k) (x : Cube ι (ZMod k)) : Cube ι (ZMod k) := fun i => x i+t

def orbitScore (k : ℕ) (z : ZMod k) : ℚ := (if z=0 then (k : ℚ) else 0)-1

@[simp] theorem orbitScore_zero (k : ℕ) : orbitScore k 0 = (k : ℚ)-1 := by simp [orbitScore]

omit [NeZero k] in
theorem orbitScore_nonzero {z : ZMod k} (hz : z ≠ 0) : orbitScore k z = -1 := by
  simp [orbitScore, hz]

theorem sum_orbitScore (k : ℕ) [NeZero k] : (∑ t : ZMod k, orbitScore k t) = 0 := by
  simp [orbitScore, Finset.sum_sub_distrib]

theorem sum_orbitScore_sq (k : ℕ) [NeZero k] :
    (∑ t : ZMod k, (orbitScore k t)^2) = (k : ℚ)*((k : ℚ)-1) := by
  have e (t : ZMod k) : (orbitScore k t)^2 = (if t=0 then (k : ℚ)*((k : ℚ)-2) else 0)+1 := by
    by_cases h : t=0
    · simp [orbitScore, h]
      ring
    · simp [orbitScore, h]
  simp only [e, Finset.sum_add_distrib]
  simp
  ring

end BorgSignedSets
