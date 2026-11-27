module

public import conjectures.CFPLogDensity.DenseShape
public import conjectures.CFPLogDensity.DenseSpan

@[expose] public section
namespace CFPLogDensity
open Finset
namespace ColorPairs

variable {r c n : ℕ} {χ : ℕ → Fin r} (F : ColorPairs c n χ)

def lower (i : ℕ) := F.base+F.d*F.stride*i

def upper (i : ℕ) := F.lower i+F.d

def stock := F.indices.biUnion fun i => {F.lower i,F.upper i}

theorem lower_mem {i : ℕ} (hi : i∈F.indices) : F.lower i∈F.stock :=
  mem_biUnion.mpr ⟨i,hi,by simp⟩

theorem upper_mem {i : ℕ} (hi : i∈F.indices) : F.upper i∈F.stock :=
  mem_biUnion.mpr ⟨i,hi,by simp⟩

theorem stock_spec {x : ℕ} (hx : x∈F.stock) : 2^n≤x ∧ x<2*2^n ∧ χ x=F.color := by
  obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
  have h := F.edge i hi
  change 2^n≤F.lower i ∧ F.upper i<2*2^n ∧ χ (F.lower i)=F.color ∧ χ (F.upper i)=F.color at h
  have le : F.lower i ≤ F.upper i := Nat.le_add_right _ _
  rcases mem_insert.mp hx with h₁|h₂
  · exact h₁ ▸ ⟨h.1,le.trans_lt h.2.1,h.2.2.1⟩
  · exact (mem_singleton.mp h₂) ▸ ⟨h.1.trans le,h.2.1,h.2.2.2⟩

theorem lower_inj : Function.Injective F.lower := by
  intro a b he
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos F.step_pos F.stride_pos)
  exact Nat.add_left_cancel he

theorem upper_inj : Function.Injective F.upper :=
  fun _a _b h => F.lower_inj (Nat.add_right_cancel h)

def available (U : Finset ℕ) := (F.indices.filter fun z => F.lower z∉U).filter fun z => F.upper z∉U

theorem available_spec {U : Finset ℕ} {z : ℕ} (hz : z∈F.available U) :
    z∈F.indices ∧ F.lower z∉U ∧ F.upper z∉U :=
  ⟨(mem_filter.mp (mem_filter.mp hz).1).1,(mem_filter.mp (mem_filter.mp hz).1).2,(mem_filter.mp hz).2⟩

private theorem avoid_card (I U : Finset ℕ) (f : ℕ → ℕ) (inj : Function.Injective f) :
    I.card≤(I.filter fun z => f z∉U).card+U.card := by
  have hb : (I.filter fun z => f z∈U).card≤U.card :=
    card_le_card_of_injOn f (fun z hz => (mem_filter.mp hz).2) inj.injOn
  have h := card_filter_add_card_filter_not (s:=I) (fun z => f z∈U)
  omega

theorem available_card (U : Finset ℕ) :
    F.indices.card≤(F.available U).card+2*U.card := by
  have h₁ := avoid_card F.indices U F.lower F.lower_inj
  have h₂ := avoid_card (F.indices.filter fun z => F.lower z∉U) U F.upper F.upper_inj
  change _ ≤ _+_ at h₂
  dsimp [available]
  omega

end ColorPairs
end CFPLogDensity
