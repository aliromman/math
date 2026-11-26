module

public import conjectures.AldousFillAdjacent.FiniteMean
public import conjectures.AldousFillAdjacent.Estimate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace AldousFillAdjacent
open Finset Filter
open scoped BigOperators Matrix Topology

variable {m : ℕ}

noncomputable def evolve (m : ℕ) : ℕ → (Deck m → ℝ) →ₗ[ℝ] (Deck m → ℝ)
  | 0 => LinearMap.id
  | k+1 => (P m).comp (evolve m k)

theorem evolve_zero (f : Deck m → ℝ) : evolve m 0 f=f := rfl
theorem evolve_succ (k : ℕ) (f : Deck m → ℝ) : evolve m (k+1) f=P m (evolve m k f) := rfl

private theorem evo_P (k : ℕ) (f : Deck m → ℝ) :
    evolve m k (P m f)=P m (evolve m k f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [evolve_succ,ih,evolve_succ]

private theorem P_one : P m (1 : Deck m → ℝ)=1 := by ext x; simp [P_apply]

private theorem evo_one (k : ℕ) : evolve m k (1 : Deck m → ℝ)=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [evolve_succ,ih,P_one]

private theorem sum_evo (k : ℕ) (f : Deck m → ℝ) : (∑ x,evolve m k f x)=∑ x,f x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [evolve_succ,sum_P,ih]

noncomputable def returnProb (m k : ℕ) : ℝ := evolve m k (δ m) 1

theorem return_nonneg (m k : ℕ) : 0≤returnProb m k := by
  have h (j : ℕ) (x : Deck m) : 0≤evolve m j (δ m) x := by
    induction j generalizing x with
    | zero => exact delta_nonneg x
    | succ j ih => exact p_nonneg ih x
  exact h k 1

private theorem mass_delta (k : ℕ) : (∑ x, evolve m k (δ m) x)=1 := by
  rw [sum_evo];simp [delta_value]

private theorem dot_evo (i j : ℕ) :
    evolve m i (δ m) ⬝ᵥ evolve m j (δ m) = returnProb m (i+j) := by
  induction i generalizing j with
  | zero => simp [evolve_zero,δ,returnProb]
  | succ i ih =>
    rw [evolve_succ,←dot_P,←evolve_succ,ih]
    congr 1;omega

private theorem centered_dot (i j : ℕ) :
    let a : ℝ := 1/Fintype.card (Deck m)
    (evolve m i (δ m)-a • (1:Deck m→ℝ)) ⬝ᵥ (evolve m j (δ m)-a • (1:Deck m→ℝ)) =
      returnProb m (i+j)-a := by
  dsimp only
  have pos : (Fintype.card (Deck m):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sub_dotProduct, dotProduct_sub, dotProduct_smul, dotProduct_one, mass_delta, smul_dotProduct,
    dotProduct_sub, one_dotProduct, mass_delta, dotProduct_smul, one_dotProduct_one, dot_evo]
  simp only [smul_eq_mul]
  field_simp
  ring

private theorem energy_drop (f : Deck m → ℝ) :
    f ⬝ᵥ L m f - P m f ⬝ᵥ L m (P m f) =
    L m f ⬝ᵥ L m f + L m f ⬝ᵥ P m (L m f) := by
  change f ⬝ᵥ (f-P m f)-P m f ⬝ᵥ (P m f-P m (P m f)) =
    (f-P m f) ⬝ᵥ (f-P m f)+(f-P m f) ⬝ᵥ P m (f-P m f)
  simp only [map_sub,sub_dotProduct,dotProduct_sub,dot_P]
  ring

private theorem remainder (f : Deck m → ℝ) (cent : ∑ x, f x=0) :
    f ⬝ᵥ L m f ≤ (2*(m:ℝ)^2)^2*((m:ℝ)+1)*(L m f ⬝ᵥ L m f) := by
  have h := sum_mul_sq_le_sq_mul_sq univ f (L m f)
  have pc := poincare f cent
  have n : 0≤L m f ⬝ᵥ L m f := sum_nonneg fun x _ ↦ mul_self_nonneg _
  change (f ⬝ᵥ L m f)^2 ≤ (∑ x, f x^2)*(∑ x, L m f x^2) at h
  simp only [pow_two] at h
  change (f ⬝ᵥ L m f)*(f ⬝ᵥ L m f) ≤ (f ⬝ᵥ f)*(L m f ⬝ᵥ L m f) at h
  have h' := h.trans (mul_le_mul_of_nonneg_right pc n)
  by_cases z : f ⬝ᵥ L m f=0
  · rw [z]; positivity
  · have g := (energy f).lt_of_ne' z
    exact le_of_mul_le_mul_left (by linarith) g

/-- A finite return expansion with a remainder bounded by one further return probability. -/
theorem return_expansion (m r : ℕ) :
    let N : ℝ := m.factorial
    0 ≤ stationaryTime m/N - (∑ j ∈ range (2*r), (returnProb m j-1/N)) ∧
    stationaryTime m/N - (∑ j ∈ range (2*r), (returnProb m j-1/N)) ≤
      (2*(m:ℝ)^2)^2*(m+1)*returnProb m (2*r) := by
  let N : ℝ := m.factorial
  have cardN : (Fintype.card (Deck m):ℝ)=N := by simp [N,Deck,Fintype.card_perm]
  have pos : 0<N := Nat.cast_pos.mpr (Nat.factorial_pos _)
  let a := 1/N
  obtain ⟨h,h0,hs,hh⟩ := first_step (mean_tendsto m)
  let τ := stationaryTime m
  let u : Deck m → ℝ := a • (τ • (1:Deck m→ℝ)-h)
  have lh : L m h = 1-N • δ m := by rw [←cardN];exact poisson_eq h hs
  have lo : L m (1:Deck m→ℝ)=0 := by change 1-P m (1:Deck m→ℝ)=0;rw [P_one,sub_self]
  have lu : L m u=δ m-a • (1:Deck m→ℝ) := by
    simp only [u,map_smul,map_sub,lo,smul_zero,zero_sub,lh]
    ext x
    simp only [Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,Pi.one_apply,smul_eq_mul,a]
    field_simp;ring
  have hsum : (∑ x,h x)=N*τ := by rw [←Fintype.card_mul_expect,hh,cardN]
  have ucent : ∑ x,u x=0 := by
    simp only [u,Pi.smul_apply,Pi.sub_apply,Pi.one_apply,smul_eq_mul,mul_one,←mul_sum,sum_sub_distrib,
      sum_const,card_univ,nsmul_eq_mul,cardN,hsum,sub_self,mul_zero]
  have eu : u ⬝ᵥ L m u=τ/N := by
    rw [lu,dotProduct_sub,dotProduct_smul,dotProduct_one,ucent,smul_zero,sub_zero]
    simp only [δ,dotProduct_single_one,u,Pi.smul_apply,Pi.sub_apply,Pi.one_apply,smul_eq_mul,
      mul_one,h0,sub_zero,a];ring
  let v (j : ℕ) := evolve m j u
  have lv (j : ℕ) : L m (v j)= evolve m j (δ m)-a • (1:Deck m→ℝ) := by
    have z : L m (v j)=evolve m j (L m u) := by
      change evolve m j u - P m (evolve m j u)=evolve m j (u-P m u)
      rw [map_sub,evo_P]
    rw [z,lu,map_sub,map_smul,evo_one]
  have rest (j : ℕ) : τ/N-(∑ i∈range (2*j), (returnProb m i-a))=v j ⬝ᵥ L m (v j) := by
    induction j with
    | zero => simpa [v,evolve_zero] using eu.symm
    | succ j ih =>
      have step := energy_drop (v j)
      have nextv : P m (v j)=v (j+1) := rfl
      rw [nextv,lv,map_sub,map_smul,P_one,←evolve_succ] at step
      have eq (i k : ℕ) := centered_dot (m:=m) i k
      simp only [cardN] at eq
      rw [eq,eq] at step
      rw [show 2*(j+1)=2*j+1+1 by omega,sum_range_succ,sum_range_succ]
      simp only [show j+j=2*j by omega,show j+(j+1)=2*j+1 by omega] at step
      rw [←lv] at step
      change v j ⬝ᵥ L m (v j)-v (j+1) ⬝ᵥ L m (v (j+1))=
        returnProb m (2*j)-a+(returnProb m (2*j+1)-a) at step
      linarith
  change 0≤τ/N-_ ∧ τ/N-_≤_
  rw [rest r]
  refine ⟨energy _,?_⟩
  have ub := remainder (v r) (by change ∑ x, evolve m r u x=0;rw [sum_evo,ucent])
  rw [lv,show a=1/(Fintype.card (Deck m):ℝ) by rw [cardN],centered_dot,cardN,
    show r+r=2*r by omega] at ub
  have one : 0≤1/N := by positivity
  have c : 0≤(2*(m:ℝ)^2)^2*(m+1) := by positivity
  rw [lv]
  exact ub.trans (mul_le_mul_of_nonneg_left (sub_le_self _ one) c)

end AldousFillAdjacent
