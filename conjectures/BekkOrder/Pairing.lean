module

public import conjectures.BekkOrder.PairTests
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BekkOrder
open Finset Polynomial
variable {n m : ℕ}

private def appendPair (B : Basis n m) (N : ℕ) (bound : n+1<N) : Basis N (m+1) where
  start := Fin.snoc B.start n
  separated i j := by
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simp only [Fin.snoc_castSucc,Fin.snoc_last];exact fun _ ↦ B.below i
    | cast j =>
      induction i using Fin.lastCases with
      | last => intro h; exact False.elim ((Fin.castSucc_lt_last j).asymm h)
      | cast i => simpa only [Fin.snoc_castSucc,Fin.castSucc_lt_castSucc_iff] using B.separated i j
  below i := by
    induction i using Fin.lastCases with
    | last => simpa using bound
    | cast i => simpa using (B.below i).trans (by omega : n<N)

/-- On the integer grid an even set of simple roots with nonnegative product consists of adjacent pairs. -/
private theorem pair_roots (m n : ℕ) (s : Finset ℕ) (sub : s⊆range n) (sz : s.card=2*m)
    (pos : ∀ x<n,0≤∏ y∈s,((x:ℝ)-y)) : ∃ B : Basis n m, B.nodes=insert n s := by
  induction m generalizing n s with
  | zero =>
    have empty : s=∅ := card_eq_zero.mp (by simpa using sz)
    refine ⟨⟨Fin.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0⟩,?_⟩
    ext x
    simp [Basis.mem_nodes,empty]
  | succ m ih =>
    have hn : s.Nonempty := card_pos.mp (by omega)
    let t := s.max' hn
    have ht : t∈s := s.max'_mem hn
    let R := s.erase t
    have rc : R.card=2*m+1 := by dsimp [R];rw [card_erase_of_mem ht];omega
    have rn : R.Nonempty := card_pos.mp (by omega)
    let v := R.max' rn
    have hv : v∈R := R.max'_mem rn
    let U := R.erase v
    have us : U.card=2*m := by dsimp [U];rw [card_erase_of_mem hv];omega
    have vt : v<t := lt_of_le_of_ne (s.le_max' _ (mem_erase.mp hv).2) (mem_erase.mp hv).1
    have tn : t<n := mem_range.mp (sub ht)
    have uv : U⊆range v := by
      intro y hy
      exact mem_range.mpr (lt_of_le_of_ne (R.le_max' _ (mem_erase.mp hy).2) (mem_erase.mp hy).1)
    have split (x : ℕ) : ∏ y∈s,((x:ℝ)-y) = ((x:ℝ)-t)*((x:ℝ)-v)*∏ y∈U,((x:ℝ)-y) := by
      rw [←s.mul_prod_erase (fun y ↦ (x:ℝ)-y) ht]
      change _* (∏y∈R,((x:ℝ)-y))=_
      rw [←R.mul_prod_erase (fun y ↦ (x:ℝ)-y) hv,mul_assoc]
    have adjacent : t=v+1 := by
      by_contra ne
      have gap : v+1<t := by omega
      have h := pos (v+1) (by omega)
      rw [split] at h
      have p : 0<∏y∈U,(((v+1:ℕ):ℝ)-y) := prod_pos fun y hy ↦ sub_pos.mpr (by
        exact_mod_cast (show y<v+1 by have k := mem_range.mp (uv hy);omega))
      have a : ((v+1:ℕ):ℝ)-t<0 := sub_neg.mpr (by exact_mod_cast gap)
      have b : 0<((v+1:ℕ):ℝ)-v := by push_cast;linarith
      exact (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos a b) p).not_ge h
    have reduced (x : ℕ) (hx : x<v) : 0≤∏ y∈U,((x:ℝ)-y) := by
      have h := pos x (by omega)
      rw [split] at h
      have ht' : (x:ℝ)-t<0 := sub_neg.mpr (by exact_mod_cast (hx.trans vt))
      have hv' : (x:ℝ)-v<0 := sub_neg.mpr (by exact_mod_cast hx)
      exact (mul_nonneg_iff_of_pos_left (mul_pos_of_neg_of_neg ht' hv')).mp h
    obtain ⟨B,eq⟩ := ih v U uv us reduced
    let C := appendPair B n (by omega)
    refine ⟨C,?_⟩
    have bd (x : ℕ) : (∃ i, x=B.start i ∨ x=B.start i+1) ↔ x∈U := by
      have hx := B.mem_nodes x
      rw [eq,mem_insert] at hx
      by_cases xv : x=v
      · constructor
        · rintro ⟨i,hi⟩
          have h := B.below i;omega
        · intro h;have e := mem_range.mp (uv h);omega
      · simpa [xv] using hx.symm
    ext x
    rw [C.mem_nodes,Fin.exists_fin_succ',mem_insert]
    simp only [C,appendPair,Fin.snoc_castSucc,Fin.snoc_last,bd,←adjacent]
    have uset : U=(s.erase t).erase v := rfl
    rw [uset,mem_erase,mem_erase]
    have vs := (mem_erase.mp hv).2
    by_cases xv : x=v
    · subst x; simp [vs]
    · by_cases xt : x=t
      · subst x; simp [ht]
      · simp [xv,xt]

/-- A degree bound converts nonnegative polynomials on the grid into the adjacent-pair bases. -/
theorem pairing (s : Finset ℕ) (sub : s⊆range n) (sz : s.card=2*m) (P : ℝ[X])
    (deg : P.natDegree≤2*m) (pole : P.eval (n:ℝ)=1) (zeros : ∀ x∈s,P.eval (x:ℝ)=0)
    (positive : ∀ x<n,0≤P.eval (x:ℝ)) : ∃ B : Basis n m,B.nodes=insert n s := by
  let G : ℝ[X] := ∏ y∈s,(X-C (y:ℝ))
  have gev (x : ℕ) : G.eval (x:ℝ)=∏ y∈s,((x:ℝ)-y) := by simp [G,eval_prod]
  have gp : 0<G.eval (n:ℝ) := by
    rw [gev];exact prod_pos (fun y hy ↦ sub_pos.mpr (by exact_mod_cast (mem_range.mp (sub hy))))
  let H := C (G.eval (n:ℝ))⁻¹*G
  have gd : G.natDegree≤2*m := by
    apply (natDegree_prod_le s (fun y ↦ X-C (y:ℝ))).trans
    simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,sz,le_refl]
  have hdeg : H.natDegree≤2*m := (natDegree_C_mul_le ..).trans gd
  have nt : n∉s := fun h ↦ (Nat.lt_irrefl n) (mem_range.mp (sub h))
  have card : (insert n s).card=2*m+1 := by rw [card_insert_of_notMem nt,sz]
  have degree {F : ℝ[X]} (hf : F.natDegree≤2*m) : F.degree<((insert n s).card:WithBot ℕ) :=
    F.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (show F.natDegree<(insert n s).card by omega))
  have eq : P=H := by
    apply eq_of_degrees_lt_of_eval_index_eq (v:=fun t : ℕ ↦ (t:ℝ)) (insert n s)
      (fun _ _ _ _ h ↦ Nat.cast_injective h) (degree deg) (degree hdeg)
    intro x hx
    rcases mem_insert.mp hx with rfl|hx
    · simp [H,pole,gp.ne']
    · have zero : G.eval (x:ℝ)=0 := by rw [gev];exact prod_eq_zero hx (sub_self _)
      simp [H,zeros x hx,zero]
  apply pair_roots m n s sub sz
  intro x hx
  have h := positive x hx
  rw [eq,show H.eval (x:ℝ)=(G.eval (n:ℝ))⁻¹*G.eval (x:ℝ) by simp [H],gev x] at h
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr gp)).mp h

end BekkOrder
end
