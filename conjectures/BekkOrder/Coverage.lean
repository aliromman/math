module

public import conjectures.BekkOrder.Pairing
public import conjectures.BekkOrder.Intervals
import Mathlib.Topology.Separation.Basic

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

instance : Finite (Basis n m) := by
  let f (B : Basis n m) (i : Fin m) : Fin n := ⟨B.start i,by have h := B.below i;omega⟩
  apply Finite.of_injective f
  intro A B h
  have e : A.start=B.start := funext fun i ↦ congrArg Fin.val (congrFun h i)
  cases A;cases B;congr

private theorem node_le (B : Basis n m) {x : ℕ} (hx : x∈B.nodes) : x≤n := by
  rcases (B.mem_nodes x).mp hx with h|⟨i,h⟩
  · omega
  · have hi := B.below i;omega

private theorem cardinal_eval (B : Basis n m) {u x : ℕ} (hu : u∈B.nodes) (hx : x∈B.nodes) :
    (lag B u).eval (x:ℝ)=if x=u then 1 else 0 := by
  by_cases e : x=u
  · subst x
    simp only [ite_true]
    exact Lagrange.eval_basis_self (fun _ _ _ _ h ↦ Nat.cast_injective h) hu
  · simp only [e,↓reduceIte]
    exact Lagrange.eval_basis_of_ne (Ne.symm e) hx

private theorem average_top (B : Basis n m) (p : ℝ) {P : ℝ[X]} (deg : P.natDegree≤2*m)
    (top : P.eval (n:ℝ)=1) (zeros : ∀ x∈B.nodes,x≠n → P.eval (x:ℝ)=0) :
    avg n p (fun x ↦ P.eval (x:ℝ))=weight B p n := by
  rw [←quadrature B p P deg,sum_eq_single n]
  · rw [top,mul_one]
  · intro x hx ne;rw [zeros x hx ne,mul_zero]
  · intro h;exact (h ((B.mem_nodes n).mpr (Or.inl rfl))).elim

private def facePoly (B : Basis n m) : ℝ[X] := ∏ i,pairPoly (B.start i)

private theorem face_degree (B : Basis n m) : (facePoly B).natDegree≤2*m := by
  apply (natDegree_prod_le univ (fun i ↦ pairPoly (B.start i))).trans
  simpa [Nat.mul_comm] using sum_le_sum (s:=univ) (fun i _ ↦ pair_degree (B.start i))

private theorem face_zero (B : Basis n m) {x : ℕ} (hx : x∈B.nodes) (xn : x≠n) :
    (facePoly B).eval (x:ℝ)=0 := by
  obtain ⟨i,h⟩ := ((B.mem_nodes x).mp hx).resolve_left xn
  rw [facePoly,eval_prod];exact prod_eq_zero (mem_univ i) (pair_zero h)

private theorem face_pos (B : Basis n m) {x : ℕ} (hx : x=n ∨ x∉B.nodes) :
    0<(facePoly B).eval (x:ℝ) := by
  rw [facePoly,eval_prod];apply prod_pos
  intro i _
  rcases hx with rfl|hx
  · have h := B.below i;exact pair_pos (by omega) (by omega)
  · exact pair_pos (fun e ↦ hx ((B.mem_nodes x).mpr (.inr ⟨i,.inl e⟩)))
      (fun e ↦ hx ((B.mem_nodes x).mpr (.inr ⟨i,.inr e⟩)))

/-- Moving a dual polynomial to its next grid contact lowers its expectation if a basic mass is negative. -/
private theorem pivot {p : ℝ} (hp : p∈Set.Ioo 0 1) (B : Basis n m) {u : ℕ}
    (hu : u∈B.nodes) (neg : weight B p u<0) : ∃ D : Basis n m,weight D p n < weight B p n := by
  classical
  let G := facePoly B
  let Q := C (G.eval (n:ℝ))⁻¹*G
  let L := lag B u
  have nt : n∈B.nodes := (B.mem_nodes n).mpr (.inl rfl)
  have gp : 0<G.eval (n:ℝ) := face_pos B (.inl rfl)
  have qe (x : ℕ) : Q.eval (x:ℝ)=(G.eval (n:ℝ))⁻¹*G.eval (x:ℝ) := by simp [Q]
  have qt : Q.eval (n:ℝ)=1 := by rw [qe,inv_mul_cancel₀ gp.ne']
  have qz (x : ℕ) (hx : x∈B.nodes) (ne : x≠n) : Q.eval (x:ℝ)=0 := by
    rw [qe,show G.eval (x:ℝ)=0 from face_zero B hx ne,mul_zero]
  have qd : Q.natDegree≤2*m := (natDegree_C_mul_le ..).trans (face_degree B)
  have qnn (x : ℕ) : 0≤Q.eval (x:ℝ) := by
    rw [qe];apply mul_nonneg (inv_pos.mpr gp).le
    change 0≤(facePoly B).eval (x:ℝ)
    rw [facePoly,eval_prod];exact prod_nonneg (fun i _ ↦ pair_nonneg _ _)
  have aq := average_top B p qd qt qz
  have topnn : 0≤weight B p n := by
    rw [←aq]
    exact sum_nonneg (fun x hx ↦ mul_nonneg (binWeight_pos (by have := mem_range.mp hx;omega) hp.1 hp.2).le (qnn x))
  have un : u≠n := by rintro rfl;linarith
  let S := (range (n+1)).filter fun x : ℕ ↦ L.eval (x:ℝ)<0
  have non : S.Nonempty := by
    by_contra h
    have nonneg (x : ℕ) (hx : x∈range (n+1)) : 0≤L.eval (x:ℝ) := by
      by_contra! lt
      exact h ⟨x,mem_filter.mpr ⟨hx,lt⟩⟩
    exact (not_lt_of_ge (show 0≤weight B p u from sum_nonneg (fun x hx ↦
      mul_nonneg (binWeight_pos (by have := mem_range.mp hx;omega) hp.1 hp.2).le (nonneg x hx)))) neg
  let ratio (x : ℕ) := Q.eval (x:ℝ) / (-L.eval (x:ℝ))
  obtain ⟨z,hz,minimal⟩ := S.exists_min_image ratio non
  have lz := (mem_filter.mp hz).2
  have zB : z∉B.nodes := by
    intro h
    have e := cardinal_eval B hu h
    change (lag B u).eval (z:ℝ)<0 at lz
    rw [e] at lz;split at lz <;> linarith
  have qpos : 0<Q.eval (z:ℝ) := by
    rw [qe];exact mul_pos (inv_pos.mpr gp) (face_pos B (.inr zB))
  let d := ratio z
  have dp : 0<d := div_pos qpos (neg_pos.mpr lz)
  let P := Q+C d*L
  have pe (x : ℕ) : P.eval (x:ℝ)=Q.eval (x:ℝ)+d*L.eval (x:ℝ) := by simp [P]
  have pd : P.natDegree≤2*m := (natDegree_add_le ..).trans (max_le qd ((natDegree_C_mul_le ..).trans (lag_degree B hu).le))
  have pt : P.eval (n:ℝ)=1 := by
    rw [pe,qt,show L.eval (n:ℝ)=0 by simpa [un.symm] using cardinal_eval B hu nt];ring
  have pz : P.eval (z:ℝ)=0 := by
    have e := div_mul_cancel₀ (Q.eval (z:ℝ)) (neg_ne_zero.mpr lz.ne)
    change d*(-L.eval (z:ℝ))=Q.eval (z:ℝ) at e
    rw [pe];linarith
  have nn (x : ℕ) (hx : x<n) : 0≤P.eval (x:ℝ) := by
    rw [pe]
    by_cases l : L.eval (x:ℝ)<0
    · have t := minimal x (mem_filter.mpr ⟨mem_range.mpr (by omega),l⟩)
      have ineq : d*(-L.eval (x:ℝ))≤Q.eval (x:ℝ) := (le_div_iff₀ (neg_pos.mpr l)).mp t
      linarith
    · exact add_nonneg (qnn x) (mul_nonneg dp.le (le_of_not_gt l))
  let s := insert z ((B.nodes.erase n).erase u)
  have zn : z<n := by
    have h := mem_range.mp (mem_filter.mp hz).1
    have ne : z≠n := fun e ↦ zB (e ▸ nt)
    omega
  have sz : s.card=2*m := by
    have zu : z∉(B.nodes.erase n).erase u := fun h ↦ zB (mem_erase.mp (mem_erase.mp h).2).2
    have um : u∈B.nodes.erase n := mem_erase.mpr ⟨un,hu⟩
    rw [show s=insert z ((B.nodes.erase n).erase u) from rfl,card_insert_of_notMem zu,
      card_erase_of_mem um,card_erase_of_mem nt,B.nodes_card]
    have pos : 1<(B.nodes).card := by
      have ss := card_pos.mpr (show (B.nodes.erase n).Nonempty from ⟨u,um⟩)
      rw [card_erase_of_mem nt] at ss;omega
    rw [B.nodes_card] at pos;omega
  have sub : s⊆range n := by
    intro x hx;rcases mem_insert.mp hx with rfl|hx
    · exact mem_range.mpr zn
    · obtain ⟨_,h⟩ := mem_erase.mp hx
      obtain ⟨ne,h⟩ := mem_erase.mp h
      exact mem_range.mpr (lt_of_le_of_ne (node_le B h) ne)
  have zero (x : ℕ) (hx : x∈s) : P.eval (x:ℝ)=0 := by
    rcases mem_insert.mp hx with rfl|hx
    · exact pz
    · obtain ⟨xu,h⟩ := mem_erase.mp hx
      obtain ⟨xn,h⟩ := mem_erase.mp h
      rw [pe,qz x h xn,show L.eval (x:ℝ)=0 by simpa [xu] using cardinal_eval B hu h];ring
  obtain ⟨D,hd⟩ := pairing s sub sz P pd pt zero nn
  refine ⟨D,?_⟩
  have ap := average_top D p pd pt (fun x hx ne ↦ zero x ((mem_insert.mp (hd ▸ hx)).resolve_left ne))
  have linear : avg n p (fun x ↦ P.eval (x:ℝ))=avg n p (fun x ↦ Q.eval (x:ℝ))+d*weight B p u := by
    unfold weight avg
    simp only [pe,mul_add,sum_add_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro x _
    dsimp only [L]
    ring
  rw [←ap,linear,aq]
  linarith [mul_neg_of_pos_of_neg dp neg]

/-- At each interior bias at least one adjacent-pair basis has nonnegative quadrature weights. -/
theorem exists_feasible (bound : 2*m<n) {p : ℝ} (hp : p∈Set.Ioo 0 1) : ∃ B : Basis n m,Feasible B p := by
  classical
  let := Fintype.ofFinite (Basis n m)
  let first : Basis n m := ⟨fun i ↦ 2*i.val,fun i j h ↦ by change _<_ at h;omega,
    fun i ↦ by have h := i.isLt;omega⟩
  obtain ⟨B,_,minim⟩ := (univ : Finset (Basis n m)).exists_min_image (fun A ↦ weight A p n) ⟨first,mem_univ _⟩
  refine ⟨B,(feasible_iff B p).mpr ?_⟩
  intro u hu
  by_contra! neg
  obtain ⟨D,hd⟩ := pivot hp B hu neg
  exact (minim D (mem_univ D)).not_gt hd

/-- Every bias is in the closure of a feasible interval of positive length. -/
theorem coverage : Covers := by
  classical
  intro n m _ bound
  let good := {B : Basis n m // Realizable B}
  let bad := {B : Basis n m // ¬ Realizable B}
  let U : Set ℝ := ⋃ B : good, closure (InteriorFeasible B.1)
  let E : Set ℝ := ⋃ B : bad, InteriorFeasible B.1
  have closedU : IsClosed U := isClosed_iUnion_of_finite (fun _ ↦ isClosed_closure)
  have subsingle (B : bad) : (InteriorFeasible B.1).Subsingleton := by
    intro x hx y hy
    by_contra ne
    have makes {a b : ℝ} (ha : a∈InteriorFeasible B.1) (hb : b∈InteriorFeasible B.1) (ab : a<b) :
        Realizable B.1 := by
      refine ⟨a,b,ab,?_⟩
      intro z hz
      have h := (connected B.1).out ha hb hz
      exact ⟨⟨h.1.1.le,h.1.2.le⟩,h.2⟩
    rcases lt_or_gt_of_ne ne with h|h
    · exact B.2 (makes hx hy h)
    · exact B.2 (makes hy hx h)
  have finiteE : E.Finite := Set.finite_iUnion (fun B ↦ (subsingle B).finite)
  have dense : Dense Eᶜ := by
    rw [Set.compl_eq_univ_sdiff]
    exact (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite finiteE
  have sub : Set.Ioo (0:ℝ) 1 ∩ Eᶜ ⊆ U := by
    rintro p ⟨hp,he⟩
    obtain ⟨B,h⟩ := exists_feasible bound hp
    by_cases b : Realizable B
    · exact Set.mem_iUnion.mpr ⟨⟨B,b⟩,subset_closure (show p∈InteriorFeasible B from ⟨hp,h⟩)⟩
    · exact (he (Set.mem_iUnion.mpr ⟨(⟨B,b⟩:bad),⟨hp,h⟩⟩)).elim
  have inner : Set.Ioo (0:ℝ) 1 ⊆ U :=
    (dense.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal sub closedU)
  have all : Set.Icc (0:ℝ) 1 ⊆ U := by
    rw [←closure_Ioo (by norm_num : (0:ℝ)≠1)]
    exact closure_minimal inner closedU
  intro p hp
  obtain ⟨B,h⟩ := Set.mem_iUnion.mp (all hp)
  exact ⟨B.1,B.2,h⟩

end BekkOrder
end
