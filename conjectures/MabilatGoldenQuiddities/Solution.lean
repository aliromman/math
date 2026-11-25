module

public import conjectures.MabilatGoldenQuiddities.Ear
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section
namespace MabilatGoldenQuiddities
noncomputable section
open Real
local notation "φ" => goldenRatio

private theorem matrix_append (a b : List ℤ) : matrix (a++b) = matrix b * matrix a := by
  simp [matrix]

private theorem quiddity_rot {w v : List ℤ} (h : w.IsRotated v) (q : Quiddity w) : Quiddity v := by
  obtain ⟨k,hk,rfl⟩ := List.isRotated_iff_mod.mp h
  refine ⟨by simpa using q.1,?_⟩
  rw [List.rotate_eq_drop_append_take hk,matrix_append]
  have decomp : matrix (w.drop k) * matrix (w.take k) = matrix w := by
    rw [← matrix_append,List.take_append_drop]
  rcases q.2 with plus|minus
  · exact Or.inl (mul_eq_one_comm.mp (decomp.trans plus))
  · right
    have hn : (-(matrix (w.drop k)))*matrix (w.take k)=1 := by rw [neg_mul,decomp,minus,neg_neg]
    have hn' := mul_eq_one_comm.mp hn
    rw [mul_neg] at hn'
    exact neg_eq_iff_eq_neg.mp hn'

private theorem edge_entries {w : List ℤ} (q : Quiddity w) :
    matrix w 0 1=0 ∧ matrix w 1 0=0 ∧ (matrix w 1 1=1 ∨ matrix w 1 1= -1) := by
  rcases q.2 with h|h <;> simp [h]

private theorem no_three (x y z : ℤ) : ¬ Quiddity [x,y,z] := by
  intro h
  have e := (edge_entries h).2.2
  simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at e
  have hp := one_lt_goldenRatio
  rcases lt_trichotomy y 0 with hy|rfl|hy
  · have c : (y:ℝ) ≤ -1 := by exact_mod_cast (show y≤ -1 by omega)
    have := mul_le_mul_of_nonneg_right c goldenRatio_pos.le
    rcases e with ee|ee <;> linarith
  · simp at e
  · have c : (1:ℝ) ≤ y := by exact_mod_cast (show 1≤y by omega)
    have := mul_le_mul_of_nonneg_right c goldenRatio_pos.le
    rcases e with ee|ee <;> linarith

private theorem zero_quartet (k : ℤ) : Quiddity [0,k,0,-k] := by
  refine ⟨by simp,Or.inl ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]

private theorem zero_four {x y z : ℤ} (q : Quiddity [0,x,y,z]) : y=0 ∧ z= -x := by
  obtain ⟨e₁,e₂,_⟩ := edge_entries q
  simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at e₁ e₂
  have ey : y=0 := by
    rcases e₂ with h|h
    · exact h
    · exfalso; linarith [Real.sqrt_nonneg 5]
  subst y
  simp at e₁
  have : (z:ℝ)*φ= -(x:ℝ)*φ := by linarith
  have e := (mul_right_cancel₀ goldenRatio_ne_zero this)
  exact ⟨rfl,by exact_mod_cast e⟩

private theorem three_equal_matrix (s : ℤ) (hs : s=1 ∨ s= -1) :
    matrix [s,s,s] = !![(s:ℝ), -φ; φ, -(s:ℝ)*φ] := by
  have h₂ := goldenRatio_sq
  have h₃ : φ^3=2*φ+1 := by rw [pow_succ, goldenRatio_sq]; nlinarith
  rcases hs with rfl|rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith

private theorem four_equal_matrix (s : ℤ) (hs : s=1 ∨ s= -1) :
    matrix [s,s,s,s] = !![0, -(s:ℝ); (s:ℝ), -φ] := by
  change matrix ([s,s,s]++[s])=_
  rw [matrix_append,three_equal_matrix _ hs]
  rcases hs with rfl|rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith [goldenRatio_sq]

private theorem five_equal (s : ℤ) (hs : s=1 ∨ s= -1) : Quiddity [s,s,s,s,s] := by
  refine ⟨by simp,?_⟩
  change matrix ([s,s,s,s]++[s])=1 ∨ matrix ([s,s,s,s]++[s])= -1
  rw [matrix_append,four_equal_matrix _ hs]
  rcases hs with rfl|rfl
  · right; ext i j; fin_cases i <;> fin_cases j <;> norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]
  · left; ext i j; fin_cases i <;> fin_cases j <;> norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]

private theorem no_four_starts_three (s a : ℤ) (hs : s=1 ∨ s= -1) :
    ¬ Quiddity [s,s,s,a] := by
  intro q
  have e := (edge_entries q).2.1
  change matrix ([s,s,s]++[a]) 1 0 = 0 at e
  rw [matrix_append, three_equal_matrix _ hs] at e
  rcases hs with rfl|rfl <;> norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at e

private theorem five_starts_three {s a b : ℤ} (hs : s=1 ∨ s= -1)
    (q : Quiddity [s,s,s,a,b]) : a=s ∧ b=s := by
  have bl := (edge_entries q).2.1
  change matrix ([s,s,s]++[a,b]) 1 0 = 0 at bl
  rw [matrix_append,three_equal_matrix _ hs] at bl
  have ea : a=s := by
    rcases hs with rfl|rfl <;> simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at bl
    · have : ((a:ℝ)-1)*φ = 0 := by linarith
      exact_mod_cast (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right goldenRatio_ne_zero))
    · have : ((a:ℝ)+1)*φ = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_right goldenRatio_ne_zero
      exact_mod_cast (eq_neg_of_add_eq_zero_left this)
  subst a
  have tr := (edge_entries q).1
  change matrix ([s,s,s,s]++[b]) 0 1 = 0 at tr
  rw [matrix_append,four_equal_matrix _ hs] at tr
  refine ⟨rfl,?_⟩
  rcases hs with rfl|rfl <;> simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at tr
  · have : ((b:ℝ)-1)*φ = 0 := by linarith
    exact_mod_cast (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right goldenRatio_ne_zero))
  · have : ((b:ℝ)+1)*φ = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right goldenRatio_ne_zero
    exact_mod_cast (eq_neg_of_add_eq_zero_left this)

private theorem split_interior {r : List ℤ} (hl : 3≤r.length) :
    ∃ x u y, r = x::u++[y] ∧ u≠[] := by
  cases r with
  | nil => simp at hl
  | cons x r =>
    induction r using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton r y _ =>
      refine ⟨x,r,y,rfl,?_⟩
      intro e
      simp [e] at hl

private theorem reduce_at {w r v : List ℤ} {c d : ℤ} (rot : w.IsRotated (r++v))
    (hl : 3≤r.length) (hv : v≠[]) (hb : Quiddity (c::v++[d])) : Reducible w := by
  obtain ⟨x,u,y,rfl,hu⟩ := split_interior hl
  refine ⟨x-d,y-c,c,d,u,v,hu,hv,hb,Or.inl ?_⟩
  simpa [List.append_assoc] using rot

private theorem zero_at_front {w : List ℤ} (h : 0 ∈ w) :
    ∃ r, w.IsRotated (0::r) := by
  obtain ⟨a,b,rfl⟩ := List.mem_iff_append.mp h
  exact ⟨b++a,List.isRotated_append⟩

private theorem starts_at_infix {w u : List ℤ} (h : u.IsInfix w) :
    ∃ r, w.IsRotated (u++r) := by
  obtain ⟨a,b,rfl⟩ := h
  exact ⟨b++a,by simpa [List.append_assoc] using (List.isRotated_append (l:=a) (l':=u++b))⟩

private theorem fourth_orbit {w : List ℤ} (k : ℤ) (h : w.IsRotated [0,k,0,-k]) :
    ∃ t : ℤ, w=[0,t,0,-t] ∨ w=[t,0,-t,0] := by
  obtain ⟨j,hj,rfl⟩ := List.isRotated_iff_mod.mp h.symm
  change j≤4 at hj
  interval_cases j
  · exact ⟨k,Or.inl rfl⟩
  · exact ⟨k,Or.inr rfl⟩
  · exact ⟨-k,Or.inl (by simp [List.rotate])⟩
  · exact ⟨-k,Or.inr (by simp [List.rotate])⟩
  · exact ⟨k,Or.inl (by simp [List.rotate])⟩

private theorem constant_orbit {w : List ℤ} (s : ℤ) (h : w.IsRotated [s,s,s,s,s]) :
    w=[s,s,s,s,s] := by
  obtain ⟨j,rfl⟩ := h.symm
  exact List.rotate_replicate s 5 j

private theorem classify {w : List ℤ} (h : Irreducible w) :
    w = [1,1,1,1,1] ∨ w = [-1,-1,-1,-1,-1] ∨ ∃ k : ℤ, w = [0,k,0,-k] ∨ w = [k,0,-k,0] := by
  obtain ⟨hl,hq,hir⟩ := h
  rcases obstruction hq with hz | ⟨s,hs,ear⟩
  · obtain ⟨r,rot⟩ := zero_at_front hz
    have len := rot.perm.length_eq
    have q := quiddity_rot rot hq
    cases r with
    | nil => simp_all
    | cons x r =>
      have short : r.length < 3 := by
        by_contra! big
        exact hir (reduce_at (rot.trans (List.isRotated_append (l:=[0,x]) (l':=r))) big
          (by simp) (zero_quartet x |> quiddity_rot (List.isRotated_append (l:=[0,x,0]) (l':=[-x]))))
      cases r with
      | nil => simp_all
      | cons y r =>
        cases r with
        | nil => exact (no_three 0 x y q).elim
        | cons z r =>
          have er : r=[] := by apply List.length_eq_zero_iff.mp; simp at short; omega
          subst r
          obtain ⟨rfl,rfl⟩ := zero_four q
          exact Or.inr (Or.inr (fourth_orbit x rot))
  · obtain ⟨r,rot⟩ := starts_at_infix ear
    have q := quiddity_rot rot hq
    have short : r.length < 3 := by
      by_contra! big
      exact hir (reduce_at (rot.trans List.isRotated_append) big (by simp) (five_equal s hs))
    cases r with
    | nil => exact (no_three s s s q).elim
    | cons a r =>
      cases r with
      | nil => exact (no_four_starts_three s a hs q).elim
      | cons b r =>
        have er : r=[] := by apply List.length_eq_zero_iff.mp; simp at short; omega
        subst r
        obtain ⟨ea,eb⟩ := five_starts_three hs q
        subst a
        subst b
        have e := constant_orbit s rot
        rcases hs with rfl|rfl
        · exact Or.inl e
        · exact Or.inr (Or.inl e)

private theorem dihedral_length {w v : List ℤ} (h : Dihedral w v) : w.length=v.length := by
  rcases h with h|h
  · exact h.perm.length_eq
  · simpa using h.perm.length_eq

private theorem dihedral_mem {w v : List ℤ} (h : Dihedral w v) (a : ℤ) : a∈w ↔ a∈v := by
  rcases h with h|h
  · exact h.mem_iff
  · simpa using (h.mem_iff (a:=a))

private theorem irreducible_four {w : List ℤ} (hlen : w.length=4) (hq : Quiddity w) :
    Irreducible w := by
  refine ⟨by omega,hq,?_⟩
  rintro ⟨a,b,c,d,u,v,hu,hv,hb,hd⟩
  have len := dihedral_length hd
  have pp := List.ne_nil_iff_length_pos.mp hu
  have pv := List.ne_nil_iff_length_pos.mp hv
  simp only [List.length_cons,List.length_append] at len
  obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp (show v.length=1 by omega)
  exact no_three c x d hb

private theorem no_four_middle_units (c d s : ℤ) (hs : s=1 ∨ s= -1) :
    ¬ Quiddity [c,s,s,d] := by
  intro q
  have diag := (edge_entries q).2.2
  rcases hs with rfl|rfl <;> norm_num [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at diag <;>
    rcases diag with h|h <;> nlinarith [goldenRatio_sq,one_lt_goldenRatio,Real.sqrt_nonneg 5]

private theorem irreducible_five (s : ℤ) (hs : s=1 ∨ s= -1) : Irreducible [s,s,s,s,s] := by
  refine ⟨by simp,five_equal s hs,?_⟩
  rintro ⟨a,b,c,d,u,v,hu,hv,hb,hd⟩
  have len := dihedral_length hd
  have pp := List.ne_nil_iff_length_pos.mp hu
  have pv := List.ne_nil_iff_length_pos.mp hv
  simp only [List.length_cons,List.length_append,List.length_nil] at len
  have members (i : ℤ) (hi : i∈v) : i=s := by
    have h := (dihedral_mem hd i).mpr (by simp [hi])
    simpa using h
  rcases (show v.length=1 ∨ v.length=2 by omega) with h1|h2
  · obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp h1
    exact no_three c x d hb
  · obtain ⟨x,y,rfl⟩ : ∃ x y, v=[x,y] := ⟨_,_,List.eq_getElem_of_length_eq_two v h2⟩
    have ex := members x (by simp)
    have ey := members y (by simp)
    change Quiddity [c,x,y,d] at hb
    exact no_four_middle_units c d s hs (by simpa only [ex,ey] using hb)

theorem resolution : Conjecture := by
  intro w
  refine ⟨classify,?_⟩
  rintro (rfl|rfl|⟨k,rfl|rfl⟩)
  · exact irreducible_five 1 (Or.inl rfl)
  · exact irreducible_five (-1) (Or.inr rfl)
  · exact irreducible_four rfl (zero_quartet k)
  · exact irreducible_four rfl (quiddity_rot (List.isRotated_append (l:=[0]) (l':=[k,0,-k]))
      (zero_quartet k))

/-- info: 'MabilatGoldenQuiddities.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end
end MabilatGoldenQuiddities
