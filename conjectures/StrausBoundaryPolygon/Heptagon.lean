module

public import conjectures.StrausBoundaryPolygon.HeptagonArea

@[expose] public section
namespace StrausBoundaryPolygon.Heptagon
open Set Real MeasureTheory
noncomputable section

def index (i : Fin 4) : Fin 7 := ⟨2*i.val,by omega⟩

def quadrilateral (i : Fin 4) : Plane := V (index i)

private def circle (t : ℝ) : Plane := (cos t,sin t)

private theorem q_circle (i : Fin 4) : quadrilateral i=circle (2*i.val*θ) := by
  unfold quadrilateral V index regularVertex circle θ
  push_cast
  congr 2 <;> ring

private theorem orientation {a b c : ℝ} (hab : a<b) (hbc : b<c) (span : c-a<2*Real.pi) :
    0<orient (circle a) (circle b) (circle c) := by
  have area : orient (circle a) (circle b) (circle c)=
      4*sin ((b-a)/2)*sin ((c-a)/2)*sin ((c-b)/2) := by
    unfold orient det circle
    simp only [Prod.fst_sub,Prod.snd_sub,cos_sub_cos,sin_sub_sin]
    rw [show (c-b)/2=(c+a)/2-(b+a)/2 by ring,Real.sin_sub]
    ring
  rw [area]
  have h₁ := sin_pos_of_pos_of_lt_pi (x:=(b-a)/2) (by linarith) (by linarith)
  have h₂ := sin_pos_of_pos_of_lt_pi (x:=(c-a)/2) (by linarith) (by linarith)
  have h₃ := sin_pos_of_pos_of_lt_pi (x:=(c-b)/2) (by linarith) (by linarith)
  positivity

private theorem on_frontier (i : Fin 7) : V i∈frontier R := by
  have unit (j : Fin 7) : (V j).1^2+(V j).2^2=1 := by
    unfold V regularVertex
    dsimp only
    linarith [sin_sq_add_cos_sq (2*Real.pi*j.val/7)]
  apply supporting_frontier (v:=V i) (subset_convexHull ℝ _ (mem_range_self i)) _ (by linarith [unit i])
  apply hull_support V
  intro j
  nlinarith [sq_nonneg ((V i).1-(V j).1),sq_nonneg ((V i).2-(V j).2),unit i,unit j]

private theorem chord (a b : ℝ) : det (circle a) (circle b)=sin (b-a) := by
  simp [det,circle,Real.sin_sub]
  ring

theorem quad_area : polygonArea quadrilateral = (3*sin (2*θ)+sin θ)/2 := by
  unfold polygonArea
  rw [Fin.sum_univ_four]
  change |det (quadrilateral 0) (quadrilateral 1)+det (quadrilateral 1) (quadrilateral 2)+
    det (quadrilateral 2) (quadrilateral 3)+det (quadrilateral 3) (quadrilateral 0)|/2=_
  simp only [q_circle,chord]
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,
    mul_zero,mul_one,zero_mul,sub_zero,zero_sub]
  rw [show ((2:Fin 4).val:ℝ)=2 by norm_num,show ((3:Fin 4).val:ℝ)=3 by norm_num]
  have last : -(2*3*θ)=θ-2*Real.pi := by unfold θ; ring
  rw [show 2*2*θ-2*θ=2*θ by ring, show 2*3*θ-2*2*θ=2*θ by ring,last,Real.sin_sub_two_pi]
  have A : 0<sin θ := sin_pos_of_pos_of_lt_pi (by dsimp [θ]; linarith [pi_pos]) (by dsimp [θ]; linarith [pi_pos])
  have B : 0<sin (2*θ) := sin_pos_of_pos_of_lt_pi (by dsimp [θ]; linarith [pi_pos]) (by dsimp [θ]; linarith [pi_pos])
  rw [abs_of_pos (by positivity)]
  ring

theorem area_lower : 185/100 < polygonArea quadrilateral := by
  have a := (coordinate_bounds 1).2.2.1
  have b := (coordinate_bounds 2).2.2.1
  norm_num [coordBox,regularVertex] at a b
  rw [quad_area]
  dsimp [θ]
  rw [show 2*(2*Real.pi/7) = 2*Real.pi*2/7 by ring]
  linarith

theorem inscribed : Inscribed R quadrilateral := by
  refine ⟨?_,fun i ↦ on_frontier (index i),?_,by linarith [area_lower]⟩
  · intro i j eq
    have h := congrArg Prod.fst eq
    have a := coordinate_bounds (index i)
    have b := coordinate_bounds (index j)
    fin_cases i <;> fin_cases j <;> first | rfl |
      (exfalso; norm_num [quadrilateral,V,index,coordBox] at a b h; linarith only [h,a.1,a.2.1,b.1,b.2.1])
  · intro i j k ij jk
    simp only [q_circle]
    apply (orientation _ _ _).le
    · have h : (i.val:ℝ)<j.val := by exact_mod_cast ij
      exact mul_lt_mul_of_pos_right (by linarith) (by dsimp [θ]; linarith [pi_pos])
    · have h : (j.val:ℝ)<k.val := by exact_mod_cast jk
      exact mul_lt_mul_of_pos_right (by linarith) (by dsimp [θ]; linarith [pi_pos])
    · have low : (0:ℝ) ≤ (i.val:ℝ) := by positivity
      have high : (k.val:ℝ) ≤ 3 := by exact_mod_cast (show k.val≤3 by omega)
      dsimp [θ]
      nlinarith [mul_nonneg low (le_of_lt pi_pos),mul_nonneg (sub_nonneg.mpr high) (le_of_lt pi_pos),pi_pos]

end
end StrausBoundaryPolygon.Heptagon
