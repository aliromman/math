module

public import conjectures.MissingSumFringes.Cover
public import conjectures.MissingSumFringes.Reflection
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

private theorem count_boxes (q m t : ℕ) :
    ((boxes q m t).card:ℝ)≤((q^3+2:ℕ):ℝ)*((t:ℝ)+1)^(q^3+1)*(2:ℝ)^binWidth q t := by
  have bound := boxes_card q m t
  have one : 1≤(t+1)*(2^binWidth q t*(t+1)^(q^3)) := Nat.succ_le_of_lt (by positivity)
  have integral : (boxes q m t).card≤(q^3+2)*(t+1)^(q^3+1)*2^binWidth q t := by
    rw [pow_succ (t+1) (q^3)]
    nlinarith only [bound,one]
  exact_mod_cast integral

private theorem window_pre {q : ℕ} (hq : 0<q) (m t : ℕ) :
    window m t≤((q^3+2:ℕ):ℝ)*((t:ℝ)+1)^(q^3+1)*
      (2:ℝ)^(-(m:ℝ)/2-((t:ℝ)-m)/8+3*t/q+2*(q:ℝ)^2+1) := by
  let w := binWidth q t
  let E : ℝ := 7*(t:ℝ)/8-3*(m:ℝ)/8+3*(w:ℝ)/4+3*((t:ℝ)/q)/8+1/8
  let G := (range t).powerset.filter fun A => (missing t A).card=m ∧ (t=0 ∨ t-1∈missing t A)
  have qr : 0<(q:ℝ) := by exact_mod_cast hq
  have cover : G⊆(boxes q m t).biUnion (reflected t) := by
    intro A hA
    obtain ⟨sub,count,last⟩ := mem_filter.mp hA
    obtain ⟨C,hC,inC⟩ := exists_box hq (mem_powerset.mp sub) count
    refine mem_biUnion.mpr ⟨C,hC,?_⟩
    exact mem_filter.mpr ⟨mem_powerset.mpr inC,by
      rcases last with rfl|last
      · have empty : A=∅ := by simpa using mem_powerset.mp sub
        simp [empty]
      · exact (mem_sdiff.mp last).2⟩
  have total : (G.card:ℝ)≤∑ C∈boxes q m t, ((reflected t C).card:ℝ) := by
    exact_mod_cast (card_mono cover).trans card_biUnion_le
  have per : ∀ C∈boxes q m t, ((reflected t C).card:ℝ)≤(2:ℝ)^E := by
    intro C hC
    obtain ⟨sub,cap⟩ := (mem_filter.mp hC).2
    have cap' : (2*(C.card:ℝ)+m)*q≤2*t*q+2*(w:ℝ)*q+t := by exact_mod_cast cap
    have bound : 2*(C.card:ℝ)+m≤2*t+2*(w:ℝ)+(t:ℝ)/q := by
      apply (mul_le_mul_iff_of_pos_right qr).mp
      nlinarith only [cap',div_mul_cancel₀ (t:ℝ) qr.ne']
    apply (reflected_card sub).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    dsimp [E]
    linarith
  have pop : (G.card:ℝ)≤ ((q^3+2:ℕ):ℝ)*((t:ℝ)+1)^(q^3+1)*(2:ℝ)^w*(2:ℝ)^E :=
    total.trans ((sum_le_sum per).trans (by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (count_boxes q m t) (by positivity)))
  have wi : w*q≤t+q^3 := by
    dsimp [w,binWidth,scale]
    nlinarith only [Nat.div_mul_le_self t (q^3)]
  have wr : (w:ℝ)≤(t:ℝ)/q+(q:ℝ)^2 := by
    apply (mul_le_mul_iff_of_pos_right qr).mp
    have wi' : (w:ℝ)*q≤t+(q:ℝ)^3 := by exact_mod_cast wi
    nlinarith only [wi',div_mul_cancel₀ (t:ℝ) qr.ne']
  change (G.card:ℝ)/(2:ℝ)^t ≤ _
  calc
    _ ≤ ((q^3+2:ℕ):ℝ)*((t:ℝ)+1)^(q^3+1)*(2:ℝ)^((w:ℝ)+E-t) := by
      apply (div_le_iff₀ (by positivity)).mpr
      rw [Real.rpow_sub (by norm_num),Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_natCast]
      convert pop using 1
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [E]
      have nn := div_nonneg (Nat.cast_nonneg t : (0:ℝ)≤t) qr.le
      rw [show 3*(t:ℝ)/q=3*((t:ℝ)/q) by ring]
      nlinarith only [wr,nn,sq_nonneg (q:ℝ)]

private theorem polynomial_envelope (d : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ K : ℝ, 0<K ∧ ∀ t : ℕ, ((t:ℝ)+1)^d≤K*(2:ℝ)^(δ*t) := by
  let r := (2:ℝ)^δ
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨B,hB⟩ := (tendsto_pow_const_div_const_pow_of_one_lt d hr).bddAbove_range
  refine ⟨(max B 1)*r,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right ..)) (by linarith),?_⟩
  intro t
  have bound := hB (Set.mem_range_self (t+1))
  change ((t+1:ℕ):ℝ)^d/r^(t+1)≤B at bound
  rw [Nat.cast_add,Nat.cast_one] at bound
  have pos : 0<r := by linarith
  have out := (div_le_iff₀ (pow_pos pos _)).mp (bound.trans (le_max_left B 1))
  rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
  change ((t:ℝ)+1)^d≤max B 1*r*r^t
  simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using out

/-- The cost of the final missing sum depends on its distance past the other gaps. -/
theorem window_bound (ε : ℝ) (he : 0<ε) : ∃ K : ℝ, 0<K ∧ ∀ m t : ℕ,
    window m t≤K*(2:ℝ)^(-(m:ℝ)/2-((t:ℝ)-m)/8+ε*t) := by
  obtain ⟨q,hlarge⟩ := exists_nat_gt (6/ε+1)
  have qr : 0<(q:ℝ) := by linarith [div_pos (by norm_num : (0:ℝ)<6) he]
  have hq : 0<q := by exact_mod_cast qr
  have small : 3/(q:ℝ)≤ε/2 := by
    apply (div_le_iff₀ qr).mpr
    have low : 6/ε < (q:ℝ) := by linarith
    nlinarith only [(div_lt_iff₀ he).mp low]
  obtain ⟨P,hP,poly⟩ := polynomial_envelope (q^3+1) (half_pos he)
  let D : ℝ := ((q^3+2:ℕ):ℝ)
  let B : ℝ := 2*(q:ℝ)^2+1
  refine ⟨D*P*(2:ℝ)^B,by dsimp [D]; positivity,?_⟩
  intro m t
  let X : ℝ := -(m:ℝ)/2-((t:ℝ)-m)/8
  have err := mul_le_mul_of_nonneg_right small (Nat.cast_nonneg t : (0:ℝ)≤t)
  have comb : ε/2*t+(X+3*t/q+2*q^2+1) ≤ B+(X+ε*t) := by
    dsimp [B]
    rw [show 3*(t:ℝ)/q=3/q*t by ring]
    linarith
  calc
    window m t ≤ D*((t:ℝ)+1)^(q^3+1)*(2:ℝ)^(X+3*t/q+2*(q:ℝ)^2+1) := window_pre hq m t
    _ ≤ D*(P*(2:ℝ)^(ε/2*t))*(2:ℝ)^(X+3*t/q+2*(q:ℝ)^2+1) := by
      gcongr
      exact poly t
    _ = D*P*((2:ℝ)^(ε/2*t+(X+3*t/q+2*(q:ℝ)^2+1))) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2) (ε/2*t) (X+3*t/q+2*(q:ℝ)^2+1)]
      ring
    _ ≤ D*P*((2:ℝ)^(B+(X+ε*t))) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) comb)
        (mul_nonneg (by dsimp [D]; positivity) hP.le)
    _ = _ := by rw [Real.rpow_add (by norm_num)]; ring

end MissingSumFringes
