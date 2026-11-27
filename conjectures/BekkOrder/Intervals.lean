module

public import conjectures.BekkOrder.Comparison
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

private theorem top_weight (B : Basis n m) {p : ℝ} (hp : p∈Set.Ioo 0 1) : 0≤weight B p n := by
  let Q := ∏ i,pairPoly (B.start i)
  have deg : Q.natDegree≤2*m := by
    have h := natDegree_prod_le univ (fun i ↦ pairPoly (B.start i))
    have k := sum_le_sum (s:=univ) (fun i _ ↦ pair_degree (B.start i))
    apply h.trans
    simpa [Nat.mul_comm] using k
  have integral : 0≤avg n p (fun x ↦ Q.eval (x:ℝ)) := by
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (binWeight_pos (by have h := mem_range.mp hx;omega) hp.1 hp.2).le
      (by dsimp [Q]; rw [eval_prod];exact prod_nonneg (fun i _ ↦ pair_nonneg _ _))
  have eq := quadrature B p Q deg
  rw [sum_eq_single n] at eq
  · have top : 0<Q.eval (n:ℝ) := by
      dsimp [Q];rw [eval_prod]
      apply prod_pos
      intro i _
      have h := B.below i
      exact pair_pos (by omega) (by omega)
    exact (mul_nonneg_iff_of_pos_right top).mp (eq ▸ integral)
  · intro x hx ne
    obtain ⟨i,h⟩ := ((B.mem_nodes _).mp hx).resolve_left ne
    have zero : Q.eval (x:ℝ)=0 := by
      dsimp [Q];rw [eval_prod];exact prod_eq_zero (mem_univ i) (pair_zero h)
    rw [zero,mul_zero]
  · intro h
    exact (h ((B.mem_nodes _).mpr (Or.inl rfl))).elim

theorem connected (B : Basis n m) : (InteriorFeasible B).OrdConnected := by
  constructor
  intro p hp r hr q hq
  obtain ⟨pq,qr⟩ := hq
  rcases eq_or_lt_of_le pq with e|pq
  · simpa only [←e] using hp
  rcases eq_or_lt_of_le qr with e|qr
  · simpa only [e] using hr
  have inside : q∈Set.Ioo (0:ℝ) 1 := ⟨hp.1.1.trans pq,qr.trans hr.1.2⟩
  refine ⟨inside,(feasible_iff _ _).mpr ?_⟩
  intro x hx
  rcases (B.mem_nodes _).mp hx with rfl|⟨i,hi⟩
  · exact top_weight B inside
  let k (x : ℕ) := (kernelPoly B i).eval (x:ℝ)
  have hpos (u : ℕ) (hu : u=B.start i ∨ u=B.start i+1) : 0<k u := kernel_pos B i hu
  have b := B.below i
  have weightp := (feasible_iff B p).mp hp.2 (B.start i+1) ((B.mem_nodes _).mpr (.inr ⟨i,Or.inr rfl⟩))
  have weightr := (feasible_iff B r).mp hr.2 (B.start i) ((B.mem_nodes _).mpr (.inr ⟨i,Or.inl rfl⟩))
  rcases hi with rfl|rfl
  · have pos := hpos (B.start i) (Or.inl rfl)
    by_contra! neg
    have hq' : 0≤avg n q (fun x ↦ ((x:ℝ)-(B.start i+1:ℕ))*k x) := by
      change 0≤avg n q (fun x ↦ ((x:ℝ)-(B.start i+1:ℕ))*(kernelPoly B i).eval (x:ℝ))
      rw [left_mass]; exact mul_nonneg (neg_nonneg.mpr neg.le) pos.le
    have cross := avg_crossing inside.1 qr hr.1.2 (fun x hx ↦ kernel_nonneg B i hx)
      (show ∃ x≤n, x≠B.start i+1 ∧ 0<k x from ⟨B.start i,by omega,by omega,pos⟩) hq'
    change 0<avg n r (fun x ↦ ((x:ℝ)-(B.start i+1:ℕ))*(kernelPoly B i).eval (x:ℝ)) at cross
    rw [left_mass] at cross
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr weightr) pos.le).not_gt cross
  · have pos := hpos (B.start i+1) (Or.inr rfl)
    have hp' : 0≤avg n p (fun x ↦ ((x:ℝ)-B.start i)*k x) := by
      change 0≤avg n p (fun x ↦ ((x:ℝ)-B.start i)*(kernelPoly B i).eval (x:ℝ))
      rw [right_mass];exact mul_nonneg weightp pos.le
    have cross := avg_crossing hp.1.1 pq inside.2 (fun x hx ↦ kernel_nonneg B i hx)
      (show ∃ x≤n, x≠B.start i ∧ 0<k x from ⟨B.start i+1,b.le,by omega,pos⟩) hp'
    change 0<avg n q (fun x ↦ ((x:ℝ)-B.start i)*(kernelPoly B i).eval (x:ℝ)) at cross
    rw [right_mass] at cross
    exact ((mul_pos_iff_of_pos_right pos).mp cross).le

/-- Taking the closure of a nondegenerate feasible interval includes its limiting endpoints. -/
theorem intervals : OrderedIntervals := by
  intro n m _ _
  constructor
  · intro B hB
    obtain ⟨a,b,ab,sub⟩ := hB
    have ha := (sub (Set.left_mem_Icc.mpr ab.le)).1.1
    have hb := (sub (Set.right_mem_Icc.mpr ab.le)).1.2
    let u := (2*a+b)/3
    let v := (a+2*b)/3
    have au : a<u := by dsimp [u];linarith
    have uv : u<v := by dsimp [u,v];linarith
    have vb : v<b := by dsimp [v];linarith
    have hu : u∈InteriorFeasible B := ⟨⟨ha.trans_lt au, (uv.trans vb).trans_le hb⟩,
      (sub (show u∈Set.Icc a b from ⟨au.le,(uv.trans vb).le⟩)).2⟩
    have hv : v∈InteriorFeasible B := ⟨⟨ha.trans_lt (au.trans uv), vb.trans_le hb⟩,
      (sub (show v∈Set.Icc a b from ⟨(au.trans uv).le,vb.le⟩)).2⟩
    let S := closure (InteriorFeasible B)
    have bounds : S ⊆ Set.Icc (0:ℝ) 1 := closure_minimal (fun x hx ↦ ⟨hx.1.1.le,hx.1.2.le⟩) isClosed_Icc
    have lower : BddBelow S := ⟨0,fun x hx ↦ (bounds hx).1⟩
    have upper : BddAbove S := ⟨1,fun x hx ↦ (bounds hx).2⟩
    have hc : IsConnected (InteriorFeasible B) := ⟨⟨u,hu⟩,(connected B).isPreconnected⟩
    refine ⟨sInf S,sSup S,(csInf_le lower (subset_closure hu)).trans_lt (uv.trans_le (le_csSup upper (subset_closure hv))),?_⟩
    exact eq_Icc_csInf_csSup_of_connected_bdd_closed hc.closure lower upper isClosed_closure
  · intro A B _ _ ab p hp q hq
    have h (x : ℝ) (hx : x∈InteriorFeasible A) : closure (InteriorFeasible B)⊆Set.Ici x :=
      closure_minimal (fun y hy ↦ ordered ab hx hy) isClosed_Ici
    exact (closure_minimal (s:=InteriorFeasible A) (t:=Set.Iic q) (fun x hx ↦ h x hx hq) isClosed_Iic) hp

end BekkOrder
end
