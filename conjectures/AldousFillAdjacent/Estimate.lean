module

public import conjectures.AldousFillAdjacent.Hitting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Matrix Topology

variable {m : ℕ}

theorem poisson_eq (h : Deck m → ℝ) (hs : ∀ x≠1, h x=1+P m h x) :
    L m h = 1-(Fintype.card (Deck m):ℝ) • δ m := by
  have off (x : Deck m) (hx : x≠1) : L m h x=1 := by
    change h x - P m h x=1; linarith [hs x hx]
  have sm : (∑ x, (L m h x-1)) = -(Fintype.card (Deck m):ℝ) := by
    change (∑ x, (h x-P m h x-1))=_
    simp [sum_sub_distrib,sum_P]
  rw [sum_eq_single_of_mem 1 (mem_univ _) (fun x _ hx ↦ by rw [off x hx];ring)] at sm
  ext x
  by_cases hx : x=1
  · subst x; change h 1 - P m h 1 - 1 = _ at sm; simp [delta_value]; linarith
  · simp [delta_value,hx,off x hx]

/-- The two-step variational bound. One step can leave the deck fixed, and a
second identical choice always restores the starting deck. -/
theorem finite_lower {τ : ℝ} (ht : Tendsto (mean m) atTop (𝓝 τ)) :
    1+2/((m:ℝ)+1)-4/(m.factorial:ℝ) ≤ τ/m.factorial := by
  obtain ⟨h,h0,hs,hh⟩ := first_step ht
  let N : ℝ := Fintype.card (Deck m)
  let e := δ m
  let q := e+P m e
  have npos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have cardN : (m.factorial:ℝ)=N := by simp [N,Deck,Fintype.card_perm]
  have hL : L m h = 1 - N • e := poisson_eq h hs
  have qL : L m q = e-P m (P m e) := by
    change e + P m e-P m (e+P m e)=_
    rw [map_add]; abel
  have se : (∑ x, e x)=1 := by simp [e,delta_value]
  have ed (v : Deck m → ℝ) : v ⬝ᵥ e=v 1 := dotProduct_single_one _ _
  have de (v : Deck m → ℝ) : e ⬝ᵥ v=v 1 := single_one_dotProduct _ _
  have ee : e 1=1 := by simp [e,delta_value]
  have sq : (∑ x, q x)=2 := by simp only [q,Pi.add_apply,sum_add_distrib,sum_P,se];norm_num
  have hE : h ⬝ᵥ L m h = N*τ := by
    rw [hL,dotProduct_sub,dotProduct_one,dotProduct_smul,ed,h0,smul_zero,sub_zero,
      ←Fintype.card_mul_expect,hh]
  have qE : q ⬝ᵥ L m q = 1+P m e 1-P m (P m e) 1-P m (P m (P m e)) 1 := by
    rw [qL,dotProduct_sub,ed]
    simp only [q,Pi.add_apply,ee,add_dotProduct,←dot_P,de]
    ring
  have qH : q ⬝ᵥ L m h = 2-N*(1+P m e 1) := by
    rw [hL,dotProduct_sub,dotProduct_one,dotProduct_smul,ed,sq]
    simp only [q,Pi.add_apply,ee,smul_eq_mul]
  have hQ : h ⬝ᵥ L m q = q ⬝ᵥ L m h := (dot_L h q).trans (dotProduct_comm _ _)
  have v := energy (h+N • q)
  simp only [map_add,map_smul,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,hE,hQ,qH,qE] at v
  have d : N*(1+P m e 1+P m (P m e) 1+P m (P m (P m e)) 1)-4 ≤ τ := by
    apply le_of_mul_le_mul_left _ npos
    linarith
  have pos3 := p_nonneg (p_nonneg (p_nonneg (delta_nonneg (m:=m)))) (1:Deck m)
  have diff : 1+2/((m:ℝ)+1) ≤ 1+P m e 1+P m (P m e) 1+P m (P m (P m e)) 1 := by
    change _≤1+P m (δ m) 1+P m (P m (δ m)) 1+P m (P m (P m (δ m))) 1
    rw [show (2:ℝ)/((m:ℝ)+1)=1/(m+1)+1/(m+1) by ring]
    linarith [return1 (m:=m),return2 (m:=m)]
  rw [cardN]
  apply (le_div_iff₀ npos).mpr
  have h := mul_le_mul_of_nonneg_left diff npos.le
  have eq : (1+2/((m:ℝ)+1)-4/N)*N=N*(1+2/((m:ℝ)+1))-4 := by field_simp
  rw [eq]
  linarith

end AldousFillAdjacent
