module

public import conjectures.BaranyFurediCover.Squares
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace BaranyFurediCover
open Set

private theorem signed_bound {a b x y w : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hx : x≤ -1 ∨ 1≤x) (hy : y≤ -1 ∨ 1≤y)
    (hf : |a*x+b*y|≤w) (hs : |a*y-b*x|≤w) : a+b≤w := by
  obtain ⟨fl,fu⟩ := abs_le.mp hf
  obtain ⟨sl,su⟩ := abs_le.mp hs
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · linarith [mul_le_mul_of_nonneg_left hx ha,mul_le_mul_of_nonneg_left hy hb]
  · linarith [mul_le_mul_of_nonneg_left hy ha,mul_le_mul_of_nonneg_left hx hb]
  · linarith [mul_le_mul_of_nonneg_left hy ha,mul_le_mul_of_nonneg_left hx hb]
  · linarith [mul_le_mul_of_nonneg_left hx ha,mul_le_mul_of_nonneg_left hy hb]

private theorem int_sign (x : ℤ) (h : x ≠ 0) : (x : ℝ) ≤ -1 ∨ 1 ≤ (x : ℝ) := by
  rcases (show x≤ -1 ∨ 1≤x by omega) with t|t
  · left; exact_mod_cast t
  · right; exact_mod_cast t

private theorem linear_bounds {a b w : ℝ} (ha : 0≤a) (hb : 0≤b) (i j : ℤ)
    (nz : i≠0 ∨ j≠0) (hf : |a*i+b*j|≤w) (hs : |a*j-b*i|≤w) : a≤w := by
  by_cases hi : i=0
  · subst i
    have hj := int_sign j (nz.resolve_left (by simp))
    have p : |a*(j : ℝ)|≤w := by simpa using hs
    rw [abs_mul,abs_of_nonneg ha] at p
    have e : (1:ℝ)≤|(j:ℝ)| := by
      rcases hj with h|h
      · linarith [neg_le_abs (j:ℝ)]
      · exact h.trans (le_abs_self _)
    linarith [mul_le_mul_of_nonneg_left e ha]
  by_cases hj : j=0
  · subst j
    have p : |a*(i : ℝ)|≤w := by simpa using hf
    rw [abs_mul,abs_of_nonneg ha] at p
    obtain s|s := int_sign i hi
    · linarith [mul_le_mul_of_nonneg_left (neg_le_abs (i:ℝ)) ha,mul_le_mul_of_nonneg_left s ha]
    · linarith [mul_le_mul_of_nonneg_left (le_abs_self (i:ℝ)) ha,mul_le_mul_of_nonneg_left s ha]
  exact le_trans (by linarith) (signed_bound ha hb (int_sign i hi) (int_sign j hj) hf hs)

theorem length_bound {a b k : ℕ} (ha : 0<a) (hk : k∈lengths (square a b)) :
    (k:ℝ)*a ≤ D a b := by
  obtain ⟨z,v,nz,h0,h1⟩ := hk
  obtain ⟨f0,s0⟩ := (mem_square_iff ha _).mp h0
  obtain ⟨f1,s1⟩ := (mem_square_iff ha _).mp h1
  have diff (x y : ℝ) (h : x∈Icc 0 (D a b)) (g : y∈Icc 0 (D a b)) :
      |y-x|≤D a b := abs_le.mpr ⟨by linarith [h.2,g.1],by linarith [g.2,h.1]⟩
  have f := diff _ _ f0 f1
  have s := diff _ _ s0 s1
  have coords : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra! both
    exact nz (by ext i; fin_cases i <;> simp [both])
  apply linear_bounds (a:=(k:ℝ)*a) (b:=(k:ℝ)*b) (by positivity) (by positivity) _ _ coords
  · convert f using 2; simp [first,pt]; ring
  · convert s using 2; simp [second,pt]; ring

theorem lengths_bounded {a b : ℕ} (ha : 0<a) : BddAbove (lengths (square a b)) := by
    refine ⟨a^2+b^2,fun k hk => ?_⟩
    have e := length_bound ha hk
    have h : (1:ℝ)≤a := by exact_mod_cast ha
    have v : (k:ℝ)≤D a b := by nlinarith [mul_nonneg (show (0:ℝ)≤k by positivity) (sub_nonneg.mpr h)]
    unfold D at v
    exact_mod_cast v

theorem string_lower {a b : ℕ} (ha : 0<a) : a≤stringDiameter (square a b) := by
  apply le_csSup (lengths_bounded ha)
  refine ⟨![0,(b:ℤ)],![1,0],?_,?_,?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · apply (mem_square_iff ha _).mpr
    simp only [first,second,pt,D,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_zero,Int.cast_natCast,mul_zero,zero_add,sub_zero,mem_Icc]
    constructor <;> constructor <;> nlinarith [sq_nonneg ((a:ℝ)-b),sq_nonneg (a:ℝ),sq_nonneg (b:ℝ),mul_nonneg (show (0:ℝ)≤a by positivity) (show (0:ℝ)≤b by positivity)]
  · apply (mem_square_iff ha _).mpr
    simp [first,second,pt,D,pow_two,mul_comm]
    positivity

@[simp] private theorem first_add (a b : ℕ) (x y : Plane) :
    first a b (x+y)=first a b x+first a b y := by simp [first]; ring
@[simp] private theorem second_add (a b : ℕ) (x y : Plane) :
    second a b (x+y)=second a b x+second a b y := by simp [second]; ring
@[simp] private theorem first_smul (a b : ℕ) (r : ℝ) (x : Plane) :
    first a b (r•x)=r*first a b x := by simp [first]; ring
@[simp] private theorem second_smul (a b : ℕ) (r : ℝ) (x : Plane) :
    second a b (r•x)=r*second a b x := by simp [second]; ring

private noncomputable def center (a b : ℕ) : Plane := ![((a:ℝ)-b)/2,((a:ℝ)+b)/2]
@[simp] private theorem first_center (a b : ℕ) : first a b (center a b)=D a b/2 := by
  simp [first,center,D]; ring
@[simp] private theorem second_center (a b : ℕ) : second a b (center a b)=D a b/2 := by
  simp [second,center,D]; ring

private theorem half_sign (z : ℤ) : 1-2*(z:ℝ)≤ -1 ∨ 1≤1-2*(z:ℝ) := by
  rcases (show 1≤z ∨ z≤0 by omega) with h|h
  · left; have : (1:ℝ)≤z := by exact_mod_cast h
    linarith
  · right; have : (z:ℝ)≤0 := by exact_mod_cast h
    linarith

private theorem cover_lower {a b : ℕ} (ha : 0<a) {r : ℝ} (hr : 0<r)
    (cover : Covers (square a b) r) : (a:ℝ)+b≤r*D a b := by
  obtain ⟨z,y,hy,e⟩ := cover (r • center a b + ![(1/2:ℝ),1/2])
  obtain ⟨fy,sy⟩ := (mem_square_iff ha _).mp hy
  have strip (w:ℝ) (hw : w∈Icc 0 (D a b)) : |r*(2*w-D a b)|≤r*D a b := by
    rw [abs_mul,abs_of_nonneg hr.le]
    apply mul_le_mul_of_nonneg_left _ hr.le
    exact abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have f := congrArg (first a b) e
  have s := congrArg (second a b) e
  simp only [first_add,second_add,first_smul,second_smul,first_center,second_center] at f s
  apply signed_bound (by positivity) (by positivity) (half_sign (z 0)) (half_sign (z 1))
  · convert strip _ fy using 2
    simp [first,pt] at f ⊢
    linear_combination 2*f
  · convert strip _ sy using 2
    simp [second,pt] at s ⊢
    linear_combination 2*s

private theorem bounded_forms {a b : ℕ} (u : Plane) (h : ∀ i, |u i|≤1/2) :
    |first a b u|≤((a:ℝ)+b)/2 ∧ |second a b u|≤((a:ℝ)+b)/2 := by
  have H (x : ℕ) (i : Fin 2) : |(x:ℝ)*u i|≤x*(1/2) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(x:ℝ))]
    exact mul_le_mul_of_nonneg_left (h i) (by positivity)
  exact ⟨(abs_add_le ..).trans (by linarith [H a 0,H b 1]),
    (abs_sub ..).trans (by linarith [H a 1,H b 0])⟩

theorem square_radius {a b : ℕ} (ha : 0<a) : radius (square a b) = ((a:ℝ)+b)/D a b := by
  let r := ((a:ℝ)+b)/D a b
  have dp := d_pos (b:=b) ha
  have rp : 0<r := div_pos (by positivity) dp
  have rd : r*D a b=(a:ℝ)+b := div_mul_cancel₀ _ dp.ne'
  have cov : Covers (square a b) r := by
    intro x
    let z : Lattice := fun i => ⌊x i - r*center a b i + 1/2⌋
    let u := x-r•center a b-pt z
    have hu (i) : |u i|≤1/2 := by
      change |x i-r*center a b i-(z i:ℝ)|≤1/2
      exact abs_le.mpr ⟨by dsimp [z]; linarith [Int.floor_le (x i-r*center a b i+1/2)],
        by dsimp [z]; linarith [Int.lt_floor_add_one (x i-r*center a b i+1/2)]⟩
    let y := r⁻¹ • (x-pt z)
    have ry : r•y=x-pt z := by simp [y,smul_smul,rp.ne']
    refine ⟨z,y,(mem_square_iff ha _).mpr ?_,by rw [ry]; abel⟩
    have eq : r•y=r•center a b+u := by rw [ry]; dsimp [u]; abel
    have get (v w : ℝ) (he : r*v=r*(D a b/2)+w) (hw : |w|≤((a:ℝ)+b)/2) :
        v∈Icc 0 (D a b) := by
      obtain ⟨h₁,h₂⟩ := abs_le.mp hw
      constructor
      · by_contra! ne
        nlinarith [mul_neg_of_pos_of_neg rp ne]
      · by_contra! ne
        nlinarith [mul_pos rp (sub_pos.mpr ne)]
    obtain ⟨hf,hs⟩ := bounded_forms (a:=a) (b:=b) u hu
    exact ⟨get _ _ (by simpa using congrArg (first a b) eq) hf,
      get _ _ (by simpa using congrArg (second a b) eq) hs⟩
  change sInf _ = r
  have mem : r∈{x : ℝ | 0<x ∧ Covers (square a b) x} := ⟨rp,cov⟩
  have lb {x : ℝ} (hx : x∈{x : ℝ | 0<x ∧ Covers (square a b) x}) : r≤x :=
    (div_le_iff₀ dp).mpr (cover_lower ha hx.1 hx.2)
  exact le_antisymm (csInf_le ⟨r,fun _ hx => lb hx⟩ mem) (le_csInf ⟨r,mem⟩ (fun _ hx => lb hx))

end BaranyFurediCover
