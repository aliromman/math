module

public import conjectures.MabilatGoldenQuiddities.Ear
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace MabilatGoldenQuiddities
noncomputable section
open Real

private theorem matrix_append (x : ℝ) (a b : List ℤ) : matrix x (a++b) = matrix x b * matrix x a := by
  simp [matrix]

private theorem edge_entries {x : ℝ} {w : List ℤ} (q : Quiddity x w) :
    matrix x w 0 1=0 ∧ matrix x w 1 0=0 ∧ (matrix x w 1 1=1 ∨ matrix x w 1 1= -1) := by
  rcases q.2 with h|h <;> simp [h]

private theorem sign_power {s : ℤ} (hs : UnitSign s) (k : ℕ) :
    (s:ℝ)^k=1 ∨ (s:ℝ)^k= -1 := by
  rcases hs with rfl|rfl
  · simp
  · simpa using neg_one_pow_eq_or ℝ k

private theorem atom_power (m k : ℕ) (s : ℤ) (hs : UnitSign s) :
    (atom (parameter m) s)^(k+1) =
    (s:ℝ)^k • !![(s:ℝ)*sine m (k+2), -sine m (k+1); sine m (k+1), -(s:ℝ)*sine m k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [atom]
  | succ k ih =>
    rw [pow_succ',ih]
    have hrec := sine_rec m (k+1)
    change sine m (k+3) = parameter m * sine m (k+2) - sine m (k+1) at hrec
    ext i j
    fin_cases i <;> fin_cases j <;> rcases hs with rfl|rfl <;>
      simp [atom,Matrix.mul_apply,Fin.sum_univ_two,pow_succ,hrec,sine_rec m k] <;> ring

@[simp] private theorem matrix_replicate (x : ℝ) (k : ℕ) (s : ℤ) :
    matrix x (List.replicate k s) = (atom x s)^k := by simp [matrix]

private theorem near_matrix (m : ℕ) (s : ℤ) (hs : UnitSign s) :
    matrix (parameter m) (List.replicate (m+2) s) =
    (s:ℝ)^(m+1) • !![(s:ℝ), -(parameter m); parameter m, -(s:ℝ)*sine m (m+1)] := by
  rw [matrix_replicate,atom_power m (m+1) s hs]
  simp

private theorem penultimate_matrix (m : ℕ) (s : ℤ) (hs : UnitSign s) :
    matrix (parameter m) (List.replicate (m+3) s) =
    (s:ℝ)^(m+2) • !![0, -1; 1, -(s:ℝ)*parameter m] := by
  rw [matrix_replicate,atom_power m (m+2) s hs]
  simp

private theorem polygon (m : ℕ) (s : ℤ) (hs : UnitSign s) :
    Quiddity (parameter m) (List.replicate (m+4) s) := by
  refine ⟨by simp,?_⟩
  rw [List.replicate_succ',matrix_append, penultimate_matrix m s hs]
  have E : matrix (parameter m) [s] *
      ((s:ℝ)^(m+2) • !![0,-1;1,-(s:ℝ)*parameter m]) = (-(s:ℝ)^(m+2)) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]
    ring
  rw [E]
  rcases sign_power hs (m+2) with h|h
  · exact Or.inr (by simp [h])
  · exact Or.inl (by simp [h])

private theorem no_short_polygon (m : ℕ) (s : ℤ) (hs : UnitSign s) :
    ¬ Quiddity (parameter m) (List.replicate (m+2) s) := by
  intro q
  have z := (edge_entries q).2.1
  rw [near_matrix m s hs] at z
  have np : (s:ℝ)^(m+1) ≠ 0 := by rcases sign_power hs (m+1) with h|h <;> simp [h]
  exact (mul_ne_zero np ((one_lt_parameter m).trans' zero_lt_one).ne') z

private theorem no_one_more (m : ℕ) (s a : ℤ) (hs : UnitSign s) :
    ¬ Quiddity (parameter m) (List.replicate (m+2) s++[a]) := by
  intro q
  have z := (edge_entries q).2.1
  rw [matrix_append,near_matrix m s hs] at z
  have np : (s:ℝ)^(m+1) ≠ 0 := by rcases sign_power hs (m+1) with h|h <;> simp [h]
  have sp : (s:ℝ)≠0 := by rcases hs with rfl|rfl <;> norm_num
  exact mul_ne_zero np sp (by simpa [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] using z)

private theorem two_more (m : ℕ) {s a b : ℤ} (hs : UnitSign s)
    (q : Quiddity (parameter m) (List.replicate (m+2) s++[a,b])) : a=s ∧ b=s := by
  have pos := ((one_lt_parameter m).trans' zero_lt_one).ne'
  have np : (s:ℝ)^(m+1) ≠ 0 := by rcases sign_power hs (m+1) with h|h <;> simp [h]
  have b₁ := (edge_entries q).2.1
  have e : (s:ℝ)^(m+1)*parameter m*((a:ℝ)*(s:ℝ)-1)=0 := by
    convert b₁ using 1
    rw [matrix_append,near_matrix m s hs]
    simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]
    ring
  have u := (mul_eq_zero.mp e).resolve_left (mul_ne_zero np pos)
  have ea : a=s := by
    rcases hs with rfl|rfl <;> norm_num at u
    · exact_mod_cast (sub_eq_zero.mp u)
    · have : (a:ℝ)= -1 := by linarith
      exact_mod_cast this
  subst a
  have tr := (edge_entries q).1
  rw [show List.replicate (m+2) s++[s,b] = (List.replicate (m+2) s++[s])++[b] by simp [List.append_assoc]] at tr
  rw [← List.replicate_succ',matrix_append,penultimate_matrix m s hs] at tr
  have np' : (s:ℝ)^(m+2) ≠ 0 := by rcases sign_power hs (m+2) with h|h <;> simp [h]
  have e' : (s:ℝ)^(m+2)*parameter m*((s:ℝ)-(b:ℝ))=0 := by
    convert tr using 1
    simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]
    ring
  have eb := sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_left (mul_ne_zero np' pos))
  exact ⟨rfl,by exact_mod_cast eb.symm⟩

private theorem no_short_interior (m k : ℕ) (hk : k≤m) (s c d : ℤ) (hs : UnitSign s) :
    ¬ Quiddity (parameter m) (c :: List.replicate (k+1) s ++ [d]) := by
  intro q
  have dia := (edge_entries q).2.2
  have hmag : |matrix (parameter m) (c :: List.replicate (k+1) s ++ [d]) 1 1| = 1 := by
    rcases dia with h|h <;> rw [h] <;> norm_num
  have value : matrix (parameter m) (c :: List.replicate (k+1) s ++ [d]) 1 1 =
      -(s:ℝ)^k*((s:ℝ)*sine m (k+2)) := by
    change matrix (parameter m) ([c]++List.replicate (k+1) s++[d]) 1 1=_
    rw [matrix_append,matrix_append,matrix_replicate,atom_power m k s hs]
    simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]
  have pone : |(s:ℝ)^k|=1 := by rcases sign_power hs k with h|h <;> simp [h]
  have sone : |(s:ℝ)|=1 := by rcases hs with rfl|rfl <;> norm_num
  have large : 1<sine m (k+2) := sine_interior (by omega) (by omega)
  rw [value,abs_mul,abs_neg,pone,one_mul,abs_mul,sone,one_mul,abs_of_pos (zero_lt_one.trans large)] at hmag
  linarith


private theorem quiddity_rot {x : ℝ} {w v : List ℤ} (h : w.IsRotated v) (q : Quiddity x w) :
    Quiddity x v := by
  obtain ⟨k,hk,rfl⟩ := List.isRotated_iff_mod.mp h
  refine ⟨by simpa using q.1,?_⟩
  rw [List.rotate_eq_drop_append_take hk,matrix_append]
  have decomp : matrix x (w.drop k) * matrix x (w.take k) = matrix x w := by
    rw [← matrix_append,List.take_append_drop]
  rcases q.2 with plus|minus
  · exact Or.inl (mul_eq_one_comm.mp (decomp.trans plus))
  · right
    have hn : (-(matrix x (w.drop k)))*matrix x (w.take k)=1 := by rw [neg_mul,decomp,minus,neg_neg]
    have hn' := mul_eq_one_comm.mp hn
    rw [mul_neg] at hn'
    exact neg_eq_iff_eq_neg.mp hn'

private theorem no_three (m : ℕ) (x y z : ℤ) : ¬ Quiddity (parameter m) [x,y,z] := by
  intro h
  have e := (edge_entries h).2.2
  simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two] at e
  have hp := one_lt_parameter m
  have pos : 0≤parameter m := zero_le_one.trans hp.le
  rcases lt_trichotomy y 0 with hy|rfl|hy
  · have c : (y:ℝ) ≤ -1 := by exact_mod_cast (show y≤ -1 by omega)
    have := mul_le_mul_of_nonneg_right c pos
    rcases e with ee|ee <;> linarith
  · simp at e
  · have c : (1:ℝ) ≤ y := by exact_mod_cast (show 1≤y by omega)
    have := mul_le_mul_of_nonneg_right c pos
    rcases e with ee|ee <;> linarith

private theorem zero_quartet (x : ℝ) (k : ℤ) : Quiddity x [0,k,0,-k] := by
  refine ⟨by simp,Or.inl ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two]

private theorem zero_four {m : ℕ} {x y z : ℤ} (q : Quiddity (parameter m) [0,x,y,z]) :
    y=0 ∧ z= -x := by
  obtain ⟨e₁,e₂,_⟩ := edge_entries q
  have hp := ((one_lt_parameter m).trans' zero_lt_one).ne'
  simp [matrix,atom,Matrix.mul_apply,Fin.sum_univ_two,hp] at e₁ e₂
  subst y
  simp at e₁
  have : (z:ℝ)*parameter m= -(x:ℝ)*parameter m := by linarith
  have e := (mul_right_cancel₀ hp this)
  exact ⟨rfl,by exact_mod_cast e⟩

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

private theorem reduce_at {x : ℝ} {w r v : List ℤ} {c d : ℤ} (rot : w.IsRotated (r++v))
    (hl : 3≤r.length) (hv : v≠[]) (hb : Quiddity x (c::v++[d])) : Reducible x w := by
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

private theorem dihedral_length {w v : List ℤ} (h : Dihedral w v) : w.length=v.length := by
  rcases h with h|h
  · exact h.perm.length_eq
  · simpa using h.perm.length_eq

private theorem dihedral_mem {w v : List ℤ} (h : Dihedral w v) (a : ℤ) : a∈w ↔ a∈v := by
  rcases h with h|h
  · exact h.mem_iff
  · simpa using (h.mem_iff (a:=a))

private theorem irreducible_four {m : ℕ} {w : List ℤ} (hlen : w.length=4) (hq : Quiddity (parameter m) w) :
    Irreducible (parameter m) w := by
  refine ⟨by omega,hq,?_⟩
  rintro ⟨a,b,c,d,u,v,hu,hv,hb,hd⟩
  have len := dihedral_length hd
  have pp := List.ne_nil_iff_length_pos.mp hu
  have pv := List.ne_nil_iff_length_pos.mp hv
  simp only [List.length_cons,List.length_append] at len
  obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp (show v.length=1 by omega)
  exact no_three m c x d hb


private theorem classify (m : ℕ) {w : List ℤ} (h : Irreducible (parameter m) w) :
    w = List.replicate (m+4) 1 ∨ w = List.replicate (m+4) (-1) ∨
    ∃ k : ℤ, w = [0,k,0,-k] ∨ w = [k,0,-k,0] := by
  obtain ⟨hl,hq,hir⟩ := h
  rcases obstruction m hq with hz | ⟨s,hs,ear⟩
  · obtain ⟨r,rot⟩ := zero_at_front hz
    have len := rot.perm.length_eq
    have q := quiddity_rot rot hq
    cases r with
    | nil => simp_all
    | cons x r =>
      have short : r.length < 3 := by
        by_contra! big
        exact hir (reduce_at (rot.trans (List.isRotated_append (l:=[0,x]) (l':=r))) big (by simp)
          (quiddity_rot (List.isRotated_append (l:=[0,x,0]) (l':=[-x])) (zero_quartet _ x)))
      cases r with
      | nil => simp_all
      | cons y r =>
        cases r with
        | nil => exact (no_three m 0 x y q).elim
        | cons z r =>
          have er : r=[] := by apply List.length_eq_zero_iff.mp; simp at short; omega
          subst r
          obtain ⟨rfl,rfl⟩ := zero_four q
          exact Or.inr (Or.inr (fourth_orbit x rot))
  · obtain ⟨r,rot⟩ := starts_at_infix ear
    have q := quiddity_rot rot hq
    have face : s::List.replicate (m+2) s++[s] = List.replicate (m+4) s := by
      rw [List.replicate_succ' (n:=m+3)]
      rfl
    have short : r.length < 3 := by
      by_contra! big
      exact hir (reduce_at (rot.trans List.isRotated_append) big (by simp)
        (face ▸ polygon m s hs))
    cases r with
    | nil => exact (no_short_polygon m s hs (by simpa using q)).elim
    | cons a r =>
      cases r with
      | nil => exact (no_one_more m s a hs q).elim
      | cons b r =>
        have er : r=[] := by apply List.length_eq_zero_iff.mp; simp at short; omega
        subst r
        obtain ⟨ea,eb⟩ := two_more m hs q
        subst a
        subst b
        have full : w.IsRotated (List.replicate (m+4) s) := by
          convert rot using 1
          rw [show m+4=(m+2)+2 by omega,List.replicate_add]
          rfl
        obtain ⟨j,rfl⟩ := full.symm
        have e := List.rotate_replicate s (m+4) j
        rcases hs with rfl|rfl
        · exact Or.inl e
        · exact Or.inr (Or.inl e)

private theorem irreducible_polygon (m : ℕ) (s : ℤ) (hs : UnitSign s) :
    Irreducible (parameter m) (List.replicate (m+4) s) := by
  refine ⟨by simp,polygon m s hs,?_⟩
  rintro ⟨a,b,c,d,u,v,hu,hv,hb,hd⟩
  have len := dihedral_length hd
  have pp := List.ne_nil_iff_length_pos.mp hu
  have pv := List.ne_nil_iff_length_pos.mp hv
  simp only [List.length_cons,List.length_append,List.length_replicate] at len
  have all : v=List.replicate v.length s := List.eq_replicate_iff.mpr ⟨rfl,fun i hi =>
    List.eq_of_mem_replicate ((dihedral_mem hd i).mpr (by simp [hi]))⟩
  obtain ⟨k,hk⟩ : ∃ k, v.length=k+1 := ⟨v.length-1,by omega⟩
  rw [hk] at all
  rw [all] at hb
  exact no_short_interior m k (by omega) s c d hs hb

/-- Classify all signed quiddities for every real Hecke parameter with q ≥ 4. -/
theorem hecke_classification : HeckeClassification := by
  intro q hq w
  obtain ⟨m,rfl⟩ : ∃ m, q=m+4 := ⟨q-4,by omega⟩
  rw [Nat.cast_add,Nat.cast_ofNat]
  refine ⟨classify m,?_⟩
  rintro (rfl|rfl|⟨k,rfl|rfl⟩)
  · exact irreducible_polygon m 1 (Or.inl rfl)
  · exact irreducible_polygon m (-1) (Or.inr rfl)
  · exact irreducible_four (m:=m) rfl (zero_quartet _ k)
  · exact irreducible_four (m:=m) rfl
      (quiddity_rot (List.isRotated_append (l:=[0]) (l':=[k,0,-k])) (zero_quartet _ k))

theorem resolution : Conjecture := by
  intro w
  have eq : 2*cos (π/5) = goldenRatio := by rw [cos_pi_div_five]; unfold goldenRatio; ring
  have h := hecke_classification 5 (by decide) w
  norm_num only [Nat.cast_ofNat] at h
  rw [eq] at h
  exact h

/-- info: 'MabilatGoldenQuiddities.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

/-- info: 'MabilatGoldenQuiddities.hecke_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hecke_classification

end
end MabilatGoldenQuiddities
