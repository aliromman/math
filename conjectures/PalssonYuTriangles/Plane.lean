module

public import conjectures.PalssonYuTriangles.Statement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
open Complex
namespace PalssonYu
noncomputable section

theorem D_comm (u v : ℂ) : D u v = D v u := by unfold D; rw [← neg_sub v u, normSq_neg]

theorem D_pos {u v : ℂ} (h : u ≠ v) : 0 < D u v :=
  lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun e => h (sub_eq_zero.mp (normSq_eq_zero.mp e)))

def coord (a b x : ℂ) := (x-a)/(b-a)

theorem coord_inj {a b : ℂ} (ab : a≠b) : Function.Injective (coord a b) := by
  intro x y h
  exact sub_left_injective (div_left_inj₀ (sub_ne_zero.mpr ab.symm) |>.mp h)

theorem scaled {a b : ℂ} (x y : ℂ) :
    D (coord a b x) (coord a b y) = D x y / D b a := by
  unfold D coord
  rw [← sub_div,sub_sub_sub_cancel_right, Complex.normSq_div]

theorem coords {a b : ℂ} (ab : a≠b) (x : ℂ) :
    normSq (coord a b x) = D x a/D b a ∧ normSq (coord a b x-1) = D x b/D b a := by
  have za : coord a b a=0 := by simp [coord]
  have ob : coord a b b=1 := by simp [coord,sub_ne_zero.mpr ab.symm]
  exact ⟨by simpa [D,za] using scaled (a:=a) (b:=b) x a,
    by simpa only [D,ob] using scaled (a:=a) (b:=b) x b⟩

theorem same_coords {x y : ℂ} (h : normSq x=normSq y)
    (k : normSq (x-1)=normSq (y-1)) : x.re=y.re ∧ (x.im=y.im ∨ x.im= -y.im) := by
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero] at h k
  have re : x.re=y.re := by linarith only [h,k]
  rw [re] at h
  exact ⟨re,eq_or_eq_neg_of_sq_eq_sq _ _ (by nlinarith only [h])⟩

theorem two_circles {a b x y z : ℂ} (ab : a≠b) (xy : x≠y)
    (eax : D x a=D z a) (ebx : D x b=D z b)
    (eay : D y a=D z a) (eby : D y b=D z b) : z=x ∨ z=y := by
  have eq (t : ℂ) (ha : D t a=D z a) (hb : D t b=D z b) :=
    same_coords ((coords ab t).1.trans (ha ▸ (coords ab z).1.symm))
      ((coords ab t).2.trans (hb ▸ (coords ab z).2.symm))
  obtain ⟨xr,hx⟩ := eq x eax ebx
  obtain ⟨yr,hy⟩ := eq y eay eby
  rcases hx with hi|hi
  · exact Or.inl ((coord_inj ab (ext xr hi)).symm)
  rcases hy with hj|hj
  · exact Or.inr ((coord_inj ab (ext yr hj)).symm)
  exact (xy (coord_inj ab (ext (xr.trans yr.symm) (hi.trans hj.symm)))).elim

theorem no_tetrahedron {a b x y : ℂ} (ab : a≠b) (xy : x≠y)
    (ax : D x a=D b a) (bx : D x b=D b a) (ay : D y a=D b a) (by' : D y b=D b a)
    (e : D x y=D b a) : False := by
  have H := (D_pos ab.symm).ne'
  have val (v) (v₁ : D v a=D b a) (v₂ : D v b=D b a) :
      (coord a b v).re=1/2 ∧ (coord a b v).im^2=3/4 := by
    obtain ⟨h,j⟩ := coords ab v
    rw [v₁,div_self H] at h
    rw [v₂,div_self H] at j
    simp only [normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero] at h j
    have re : (coord a b v).re=1/2 := by linarith
    exact ⟨re,by rw [re] at h; nlinarith⟩
  obtain ⟨xr,xi⟩ := val x ax bx
  obtain ⟨yr,yi⟩ := val y ay by'
  have ij := eq_or_eq_neg_of_sq_eq_sq _ _ (xi.trans yi.symm)
  rcases ij with same|op
  · exact xy (coord_inj ab (ext (xr.trans yr.symm) same))
  · have sq := scaled (a:=a) (b:=b) x y
    rw [e,div_self H] at sq
    simp only [D,normSq_apply,sub_re,sub_im,xr,yr,op] at sq
    nlinarith only [sq,yi]

/-- Three points equidistant from two centers lie on their perpendicular bisector.
An isosceles triple on that line has its apex at the midpoint. -/
theorem bisector_midpoint {a b u v x : ℂ} (ab : a≠b) (uv : u≠v) (eu : D u a=D u b)
    (ev : D v a=D v b) (ex : D x a=D x b) (eq : D x u=D x v) : 2*x=u+v := by
  have half (z) (h : D z a=D z b) : (coord a b z).re=1/2 := by
    have s := (coords ab z).1.trans (h ▸ (coords ab z).2.symm)
    simp only [normSq_apply,sub_re,sub_im,one_re,one_im,sub_zero] at s
    linarith only [s]
  have ur := half u eu
  have vr := half v ev
  have xr := half x ex
  have n : (coord a b u).im ≠ (coord a b v).im := fun hi =>
    uv (coord_inj ab (ext (ur.trans vr.symm) hi))
  have d := (scaled (a:=a) (b:=b) x u).trans (eq ▸ (scaled (a:=a) (b:=b) x v).symm)
  simp only [D,normSq_apply,sub_re,sub_im,ur,vr,xr] at d
  have prod : ((coord a b u).im-(coord a b v).im) *
      (2*(coord a b x).im-(coord a b u).im-(coord a b v).im)=0 := by nlinarith only [d]
  have h := (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr n)
  have c : 2*coord a b x=coord a b u+coord a b v := by
    apply ext <;> simp [two_mul,ur,vr,xr]; linarith
  unfold coord at c
  field_simp at c
  linear_combination c

end
end PalssonYu
