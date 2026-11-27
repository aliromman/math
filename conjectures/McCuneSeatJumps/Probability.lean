module

public import conjectures.McCuneSeatJumps.Area
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
open Finset Set MeasureTheory
namespace McCuneSeatJumps

private abbrev Key (h : ℕ) := Fin 3 × ((j : Fin h) × Fin (h-(j.val+1)+1))

private def part {h : ℕ} (k : ℕ) (t : Key h) :=
  region h k t.1 (t.2.1.val+1) t.2.2.val

private theorem cover {h k : ℕ} (hh : 0<h) :
    loss h k =ᵐ[volume] ⋃ t : Key h, part k t := by
  filter_upwards [ae_inside hh,ae_inside (show 0<h+k by omega)] with x old new
  constructor
  · rintro ⟨hp,A,B,hA,hB,i,lose⟩
    have s := (cycle_sum A i).trans hA.1
    let l : Fin h := ⟨A i-1,by omega⟩
    have le : l.val+1=A i := by dsimp [l]; omega
    let a : Fin (h-(l.val+1)+1) := ⟨A (i+1),by omega⟩
    exact Set.mem_iUnion.mpr ⟨(i,⟨l,a⟩),hp,A,B,old A hA,new B hB,lose,le.symm,rfl⟩
  · intro hx
    obtain ⟨t,hp,A,B,hA,hB,lose,_,_⟩ := Set.mem_iUnion.mp hx
    exact ⟨hp,A,B,inside_hamilton (sum_shares x) hA,inside_hamilton (sum_shares x) hB,t.1,lose⟩

private theorem disjoint_parts {h k : ℕ} : Pairwise (Function.onFun Disjoint (@part h k)) := by
  intro x y ne
  apply Set.disjoint_left.mpr
  intro p hx hy
  obtain ⟨a,b,c⟩ := region_unique hx hy
  apply ne
  obtain ⟨i,j,s⟩ := x
  obtain ⟨i',j',s'⟩ := y
  dsimp at a b c
  subst i'
  have eq : j=j' := Fin.ext (by omega)
  subst j'
  exact congrArg (fun v => (i,⟨j,v⟩) : Fin (h-(j.val+1)+1) → Key h) (Fin.ext c)

private noncomputable def factor (h k : ℕ) : ℝ := (3*h^2*(h+k)^2:ℝ)⁻¹

private theorem measure_loss {h k : ℕ} (hh : 0<h) (hk : 0<k) :
    volume (loss h k) = ENNReal.ofReal (3 * factor h k *
      ∑ j ∈ range h, ((∑ a ∈ range (h-(j+1)+1), cellWeight h k (j+1) a : ℕ):ℝ)) := by
  classical
  have sums (t : Key h) : t.2.2.val + (h-(t.2.1.val+1)-t.2.2.val) + (t.2.1.val+1)=h := by
    have := t.2.1.isLt
    have := t.2.2.isLt
    omega
  rw [measure_congr (cover hh),measure_iUnion disjoint_parts
    (fun t => measurable_region hh hk (by omega) (sums t) _),tsum_fintype]
  simp_rw [part,fun t : Key h => volume_region hh hk (by omega) (sums t) t.1]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro _ _; positivity)]
  congr 1
  have ff : (3*(h:ℝ)^2*(h+k)^2)⁻¹ = factor h k := rfl
  simp_rw [div_eq_mul_inv,ff,mul_comm _ (factor h k),← mul_sum]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have row (j : Fin h) : (∑ a : Fin (h-(j.val+1)+1), (cellWeight h k (j.val+1) a.val:ℝ)) =
      ((∑ a ∈ range (h-(j.val+1)+1), cellWeight h k (j.val+1) a : ℕ):ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun a => (cellWeight h k (j.val+1) a:ℝ)), Nat.cast_sum]
  simp_rw [row]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((∑ a ∈ range (h-(j+1)+1), cellWeight h k (j+1) a : ℕ):ℝ))]
  push_cast
  ring

/-- Exact uniform three-state probability for all positive house sizes and increases. -/
theorem exact_probability {h k : ℕ} (hh : 0<h) (hk : 0<k) : probability h k =
    ENNReal.ofReal (((h.gcd k:ℕ):ℝ)^3/(3*h^2*(h+k)^2) *
      ∑ j ∈ range h, let t : ℝ := (room h k (j+1)/h.gcd k:ℕ); t^3-t) := by
  have row (j) (hj : j ∈ range h) := sum_cellWeight_real hh hk (Nat.succ_pos j)
    (show j+1 ≤ h by simpa using hj)
  rw [probability,measure_loss hh hk,
    show (2:ENNReal)=ENNReal.ofReal 2 by norm_num,← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [sum_congr rfl row]
  simp_rw [div_eq_mul_inv,← sum_mul,← mul_sum]
  unfold factor
  ring
end McCuneSeatJumps
