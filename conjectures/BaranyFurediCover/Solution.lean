module

public import conjectures.BaranyFurediCover.Sharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace BaranyFurediCover
open Set

theorem square_product {a b : ℕ} (ha : 0<a) : area (square a b)*radius (square a b) = a+b := by
  rw [square_area,square_radius ha]
  field_simp [(d_pos (b:=b) ha).ne']

/-- A square of area five has covering radius three fifths and lattice diameter two. -/
theorem five : area (square 2 1)=5 ∧ radius (square 2 1)=3/5 ∧ diameter (square 2 1)=2 := by
  refine ⟨by norm_num [square_area,D],by norm_num [square_radius (by decide : 0<2),D],?_⟩
  norm_num [square_diameter (by decide : 0<2) (by decide : 1≤2)]

theorem sharp_bound {a b : ℕ} (ha : 0<a) (hb : b≤a) :
    area (square a b)*radius (square a b) ≤ (3/2:ℝ)*diameter (square a b) := by
  have e : (2:ℝ)*(a+b)≤3*diameter (square a b) := by exact_mod_cast sharp_squares ha hb
  rw [square_product ha]
  linarith

private theorem sqrt_bound : Real.sqrt 2<2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem polygon_resolution : ¬PolygonConjecture := by
  intro h
  have le := h _ (square_polygon 2 1) (square_interior (by decide))
  rw [square_product (by decide),five.2.2] at le
  norm_num at le
  linarith [sqrt_bound]

theorem resolution : ¬Conjecture := by
  intro h
  have le := h _ (square_compact 2 1) (square_convex _ _) (square_interior (by decide))
  rw [square_product (by decide),five.2.2] at le
  norm_num at le
  linarith [sqrt_bound]

/-- Successive positive solutions of p² + 1 = 2q², starting at (7,5). -/
private def sequence : ℕ → ℕ × ℕ
  | 0 => (7,5)
  | n+1 => let (p,q) := sequence n; (3*p+4*q,2*p+3*q)

private theorem pell (n : ℕ) :
    let (p,q) := sequence n
    p^2+1=2*q^2 ∧ q≤p ∧ 2≤q ∧ n≤q := by
  induction n with
  | zero => decide
  | succ n ih =>
    generalize e : sequence n = v at ih ⊢
    obtain ⟨p,q⟩ := v
    rw [sequence,e]
    obtain ⟨eq,pq,lo,big⟩ := ih
    dsimp only
    refine ⟨?_,by omega,by omega,by omega⟩
    nlinarith

private theorem large_square {p q : ℕ} (hq : 2≤q) (hpq : q≤p) (pell : p^2+1=2*q^2) :
    (1+Real.sqrt 2)/2 * diameter (square q (p-q)) < area (square q (p-q))*radius (square q (p-q)) := by
  have qpos : 0<q := by omega
  have eq : (p:ℝ)^2+1=2*(q:ℝ)^2 := by exact_mod_cast pell
  have qpos' : (0:ℝ)<q := by exact_mod_cast qpos
  have qle : p≤2*q := by nlinarith
  have de : D q (p-q) + 1 = (q:ℝ)*(4*q-2*p) := by
    rw [D,Nat.cast_sub hpq]
    nlinarith
  let M := 4*q - 2*p
  have posM : 0<M := by
    by_contra! no
    have ze : M=0 := by omega
    have eqM : (M:ℝ)=4*q-2*p := by
      dsimp [M]; rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [ze] at eqM
    norm_num at eqM
    nlinarith [sq_nonneg (q:ℝ)]
  have castM : (M:ℝ)=4*q-2*p := by
    dsimp [M]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have upper : diameter (square q (p-q))≤M-1 := by
    rw [diameter_eq_string (square_convex _ _) (lengths_bounded qpos)]
    apply csSup_le'
    intro k hk
    have h := length_bound qpos hk
    have lt : (k:ℝ)<M := by
      by_contra! ne
      rw [←castM] at de
      nlinarith [mul_le_mul_of_nonneg_right ne qpos'.le]
    have : k<M := by exact_mod_cast lt
    omega
  have qlo : (2:ℝ)≤q := by exact_mod_cast hq
  have key : 4*(q:ℝ)-1 < 2*Real.sqrt 2*p := by
    apply lt_of_pow_lt_pow_left₀ (n:=2) <;> try positivity
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
    nlinarith
  have root := Real.sq_sqrt (by norm_num : 0≤(2:ℝ))
  have pr : 0≤Real.sqrt 2 := Real.sqrt_nonneg _
  have pr' : 0<1+Real.sqrt 2 := by positivity
  have bound : (1+Real.sqrt 2)/2 * (4*(q:ℝ)-2*p-1) < p := by
    nlinarith [mul_pos pr' (sub_pos.mpr key),congrArg (fun x : ℝ => x*(p:ℝ)) root]
  rw [square_product qpos,Nat.cast_sub hpq]
  have upper' : (diameter (square q (p-q)) : ℝ) ≤ (M:ℝ)-1 := by
    have e : (diameter (square q (p-q)) : ℝ)+1≤M := by
      exact_mod_cast (show diameter (square q (p-q))+1≤M by omega)
    linarith
  rw [castM] at upper'
  nlinarith [mul_le_mul_of_nonneg_left upper' (div_nonneg pr'.le (by norm_num : (0:ℝ)≤2))]

/-- The proposed constant fails at arbitrarily large lattice diameters. -/
theorem unbounded (N : ℕ) : ∃ C : Set Plane, LatticePolygon C ∧ (interior C).Nonempty ∧
    N ≤ diameter C ∧ (1+Real.sqrt 2)/2 * diameter C < area C * radius C := by
  have h := pell N
  generalize sequence N = v at h
  obtain ⟨p,q⟩ := v
  obtain ⟨eq,pq,lo,big⟩ := h
  have qpos : 0<q := by omega
  refine ⟨_,square_polygon _ _,square_interior qpos,?_,large_square lo pq eq⟩
  rw [diameter_eq_string (square_convex _ _) (lengths_bounded qpos)]
  exact big.trans (string_lower qpos)

/-- info: 'BaranyFurediCover.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution
/-- info: 'BaranyFurediCover.unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded

/-- info: 'BaranyFurediCover.sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharp_bound

end BaranyFurediCover
