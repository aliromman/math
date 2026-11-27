module

public import conjectures.UlasStern.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace UlasStern

variable {R : Type*} [CommRing R]

private theorem pair_even (t : R) (i : ℕ) :
    pair t (2*i) = (t*(pair t i).1, (pair t i).1+(pair t i).2) := by
  unfold pair
  apply Nat.evenOddRec_even
  simp

private theorem pair_odd (t : R) (i : ℕ) :
    pair t (2*i+1) = ((pair t i).1+(pair t i).2, t*(pair t i).2) := by
  unfold pair
  apply Nat.evenOddRec_odd
  simp

private theorem neighbor (t : R) (n : ℕ) : (pair t n).2 = stern (n+1) t := by
  unfold stern
  induction n using Nat.evenOddRec with
  | h0 => rw [show 0+1=2*0+1 by decide, pair_odd]; simp [pair]
  | h_even i ih => rw [pair_even,pair_odd]
  | h_odd i ih =>
    rw [show 2*i+1+1=2*(i+1) by omega, pair_odd, pair_even]
    simp [ih]

/-- The scalar values satisfy the defining recurrence in the paper. -/
theorem stern_spec (t : R) : stern 0 t = 0 ∧ stern 1 t = 1 ∧
    ∀ i : ℕ, stern (2*i) t = t*stern i t ∧
      stern (2*i+1) t = stern i t + stern (i+1) t := by
  refine ⟨by simp [stern,pair],?_,fun i => ⟨?_,?_⟩⟩
  · change (pair t (2*0+1)).1=1
    rw [pair_odd]
    simp [pair]
  · exact congrArg Prod.fst (pair_even t i)
  · change (pair t (2*i+1)).1 = _
    rw [pair_odd]
    exact congrArg ((pair t i).1 + ·) (neighbor t i)

/-- Append n copies of the same two binary digits. -/
private def blocks (digit : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n+1, x => 4*blocks digit n x + digit

private theorem blocks_index (n : ℕ) : 2*blocks 1 n (blocks 2 n 0)+1 = index n := by
  have geom (d x j : ℕ) : 3*blocks d j x+d=4^j*(3*x+d) := by
    induction j with
    | zero => simp [blocks]
    | succ j ih => simp only [blocks,pow_succ]; nlinarith only [ih]
  have hu := geom 2 0 n
  have hv := geom 1 (blocks 2 n 0) n
  simp only [Nat.mul_zero, Nat.zero_add] at hu
  have hp : 0<4^n := pow_pos (by decide) _
  have sub : 4^n-1+1 = 4^n := by omega
  have he : 3 * (2*blocks 1 n (blocks 2 n 0)) = 2*(4^n-1)*(4^n*2+1) := by
    nlinarith only [hv,hu,congrArg (fun z : ℕ => 4^n*z) hu,
      congrArg (fun z : ℕ => (4^n*2+1)*z) sub]
  rw [index,pow_succ,pow_mul,show 2^2=4 by decide,←he,Nat.mul_div_cancel_left _ (by decide)]

/-- Coefficients of the two-bit transfer matrix in the basis of itself and the identity. -/
def coeff (t : R) : ℕ → R × R
  | 0 => (0,1)
  | n+1 => ((2*t+1)*(coeff t n).1+(coeff t n).2, -t^2*(coeff t n).1)

private theorem block_pair (t : R) (n i : ℕ) :
    let a := (coeff t n).1
    let b := (coeff t n).2
    let x := (pair t i).1
    let y := (pair t i).2
    pair t (blocks 2 n i) = (a*t*(x+y)+b*x, a*(x+(1+t)*y)+b*y) ∧
    pair t (blocks 1 n i) = (a*((1+t)*x+y)+b*x, a*t*(x+y)+b*y) := by
  dsimp only
  induction n with
  | zero => simp [blocks,coeff]
  | succ n ih =>
    obtain ⟨left,right⟩ := ih
    simp only [blocks,coeff]
    rw [show 4*blocks 2 n i+2=2*(2*blocks 2 n i+1) by omega,pair_even,pair_odd,left]
    rw [show 4*blocks 1 n i+1=2*(2*blocks 1 n i)+1 by omega,pair_odd,pair_even,right]
    constructor <;> apply Prod.ext <;> dsimp <;> ring

/-- An Eisenstein norm for every pair of alternating blocks. -/
theorem eisenstein_identity (n : ℕ) (t : R) :
    let a := (coeff t n).1
    let b := (coeff t n).2
    let u := b+(t+1)*a
    let v := t*a
    stern (index n) t = u^2+u*v+v^2 := by
  dsimp only
  rw [←blocks_index,stern,pair_odd,(block_pair t n _).2,(block_pair t n 0).1]
  simp only [pair, Nat.evenOddRec_zero]
  ring

/-- The two alternating binary blocks give a positive quadratic form. -/
theorem square_identity (n : ℕ) (t : R) :
    4*stern (index n) t =
      (2*(coeff t n).2+(3*t+2)*(coeff t n).1)^2 + 3*(t*(coeff t n).1)^2 := by
  rw [eisenstein_identity]
  ring

theorem coeff_at_zero (n : ℕ) : (coeff (0 : R) n).1+(coeff (0 : R) n).2=1 := by
  induction n with
  | zero => simp [coeff]
  | succ n ih => simpa [coeff] using ih

theorem coeff_nonsingular [IsDomain R] {t : R} (ht : t ≠ 0) (n : ℕ) :
    (coeff t n).1=0 → (coeff t n).2≠0 := by
  induction n with
  | zero => simp [coeff]
  | succ n ih =>
    intro h1 h2
    have ha : (coeff t n).1=0 := (mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr (pow_ne_zero _ ht))
    exact ih ha (by simpa [coeff,ha] using h1)

theorem positive (n : ℕ) (t : ℝ) : 0 < stern (index n) t := by
  have eq := square_identity n t
  by_cases ht : t=0
  · subst t
    have sq := congrArg (fun z : ℝ => z^2) (coeff_at_zero (R := ℝ) n)
    nlinarith only [sq,eq]
  · by_contra! small
    have vanish : t*(coeff t n).1=0 := by
      by_contra h
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (2*(coeff t n).2+(3*t+2)*(coeff t n).1)]
    have ha := (mul_eq_zero.mp vanish).resolve_left ht
    have hb := coeff_nonsingular ht n ha
    rw [ha] at eq
    nlinarith [sq_pos_of_ne_zero hb]

theorem resolution : Conjecture := fun n t => (positive n t).ne'

/-- info: 'UlasStern.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end UlasStern
