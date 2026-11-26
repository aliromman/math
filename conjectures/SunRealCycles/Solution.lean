module

public import conjectures.SunRealCycles.Statement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

public section
namespace SunRealCycles

private theorem inj_four {α} (f : Fin 4 → α) (h : f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 0 ≠ f 3 ∧
    f 1 ≠ f 2 ∧ f 1 ≠ f 3 ∧ f 2 ≠ f 3) : Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private def edge (p : Fin 4 → Fin 4) (i a b : Fin 4) : Prop :=
  p i = a ∧ p (finRotate 4 i) = b

private def edgeEither (p : Fin 4 → Fin 4) (i a b : Fin 4) : Prop :=
  edge p i a b ∨ edge p i b a

set_option maxRecDepth 20000 in
private theorem cycle_shape (p : Fin 4 → Fin 4) (hp : Function.Injective p) :
    (∃ i j, i ≠ j ∧ edgeEither p i 0 3 ∧ edgeEither p j 1 2) ∨
    (∃ i j, i ≠ j ∧ ((edge p i 0 2 ∧ edge p j 2 3) ∨ (edge p i 3 2 ∧ edge p j 2 0))) := by
  unfold edgeEither edge
  revert p
  decide

private theorem obstructed (x : Fin 4 → ℝ) (hp : x 0 * x 3 = x 1 * x 2)
    (hs : x 0 + x 3 = 2 * x 2) : ¬ HasCircle x (· - ·) := by
  rintro ⟨p, hd, hm⟩
  rcases cycle_shape p p.injective with ⟨i,j,ne,e,e'⟩ | ⟨i,j,ne,e⟩
  · apply ne; apply hm
    rcases e with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases e' with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;>
      simp only [ha,hb,hc,hd] <;> linarith [mul_comm (x 3) (x 0), mul_comm (x 2) (x 1)]
  · apply ne; apply hd
    rcases e with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ | ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ <;>
      simp only [ha,hb,hc,hd] <;> linarith

/-- These two equations characterize all failures on four positive numbers in increasing order. -/
theorem positive_four_iff (a b c d : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ¬ HasCircle ![a,b,c,d] (· - ·) ↔ a*d = b*c ∧ a+d = 2*c := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hd := hc.trans hcd
  have prod_order : a*b < a*c ∧ a*c < b*c ∧ a*c < a*d ∧ b*c < b*d ∧
      a*d < b*d ∧ b*d < c*d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> gcongr
  obtain ⟨p₁,p₂,p₃,p₄,p₅,p₆⟩ := prod_order
  constructor
  · intro fail
    have first : a+d = b+c ∨ a*d = b*c := by
      by_contra! h
      obtain ⟨h₁,h₂⟩ := h
      apply fail
      refine ⟨Equiv.swap (1 : Fin 4) 2, inj_four _ ?_, inj_four _ ?_⟩ <;>
        norm_num [finRotate_apply, Equiv.swap_apply_def] <;>
        and_intros <;> intro he <;> first | linarith | exact h₁ (by linarith) | exact h₂ (by linarith)
    have second : a+d = 2*b ∨ a+d = 2*c := by
      by_contra! h
      obtain ⟨h₁,h₂⟩ := h
      apply fail
      refine ⟨Equiv.swap (2 : Fin 4) 3, inj_four _ ?_, inj_four _ ?_⟩ <;>
        norm_num [finRotate_apply, Equiv.swap_apply_def] <;>
        and_intros <;> intro he <;> first | linarith | exact h₁ (by linarith) | exact h₂ (by linarith)
    rcases first with heq | hp
    · rcases second with h | h <;> exfalso <;> linarith
    · refine ⟨hp, second.resolve_left ?_⟩
      intro heq
      have hn := mul_pos hb (sub_pos.mpr hbc)
      have hd' : d = 2*b-a := by linarith
      rw [hd'] at hp
      nlinarith [sq_nonneg (a-b)]
  · rintro ⟨hp,hs⟩
    exact obstructed _ hp hs

/-- The middle values in every positive obstruction are the harmonic and arithmetic means. -/
theorem means_iff (a b c d : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ¬ HasCircle ![a,b,c,d] (· - ·) ↔ b = 2*a*d/(a+d) ∧ c = (a+d)/2 := by
  rw [positive_four_iff a b c d ha hab hbc hcd, eq_div_iff (by linarith : a+d ≠ 0),
    eq_div_iff (by norm_num : (2:ℝ) ≠ 0)]
  constructor
  · rintro ⟨hp,hs⟩
    rw [hs]
    constructor <;> linarith
  · rintro ⟨hp,hs⟩
    rw [← hs] at hp ⊢
    constructor <;> linarith

/-- Every circular ordering of 2, 3, 4 and 6 repeats a difference or a product. -/
theorem counterexample : ¬ Conjecture := by
  intro claim
  let x : Fin 4 → ℝ := ![2, 3, 4, 6]
  have hx : Function.Injective x := inj_four _ (by norm_num [x])
  have hpos (i) : 0 < x i := by fin_cases i <;> norm_num [x]
  have hexc : ¬ TwoOppositePairs x := by
    rintro ⟨_, s, t, hr⟩
    have hs : s ∈ Set.range x := hr.symm ▸ (by simp)
    have hnegs : -s ∈ Set.range x := hr.symm ▸ (by simp)
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨j, hj⟩ := hnegs
    exact (not_lt_of_ge (hpos i).le) (neg_pos.mp (hj ▸ hpos j))
  have existsCircle := (claim 4 x hx (fun i => (hpos i).ne')).2 (by decide) hexc
  exact ((positive_four_iff 2 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)) existsCircle

/-- info: 'SunRealCycles.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

/-- info: 'SunRealCycles.means_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms means_iff

end SunRealCycles
