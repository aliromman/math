module

public import conjectures.WagnerTreeInducibility.Statement
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
open Filter Topology
namespace WagnerTreeInducibility

/-- Moving the first branch of a fork to the root changes only the copies split across it. -/
theorem rotation (A B C : Tree) :
    ((Tree.fork A (.fork B C)).copies : ℝ) - (Tree.fork (.fork A B) C).copies =
    (A.leaves : ℝ) * B.leaves * C.leaves * ((B.leaves : ℝ) - 1) *
      ((C.leaves : ℝ) - A.leaves) / 4 := by
  simp only [Tree.copies, Tree.quartets, Tree.leaves, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two]
  ring

private def Share (T : ℕ → Tree) (x : ℝ) : Prop :=
  Tendsto (fun n => ((T n).leaves : ℝ) / n) atTop (𝓝 x)

private theorem share_fork {A B : ℕ → Tree} {a b : ℝ} (hA : Share A a) (hB : Share B b) :
    Share (fun n => .fork (A n) (B n)) (a + b) := by
  simpa [Share, Tree.leaves, add_div] using hA.add hB

private theorem even_leaves (n : ℕ) (hn : 0 < n) : (Tree.even n).leaves = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [Tree.even]
    split_ifs with h
    · simp only [Tree.leaves, ih (n / 2) (by omega) (by omega),
        ih (n - n / 2) (by omega) (by omega)]
      omega
    · have : n = 1 := by omega
      simp [Tree.leaves, this]

private theorem branch_share {x : ℝ} (hx : 0 < x) : Share (branch x) x := by
  apply ((tendsto_nat_floor_mul_div_atTop hx.le).comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [(tendsto_nat_floor_mul_atTop x hx).eventually_ge_atTop 1] with n hn
  simp [branch, even_leaves _ hn]

private theorem even_rotation {x : ℝ} (hx : 0 < x) :
    ∃ L R : ℕ → Tree, Share L (x / 2) ∧ Share R (x / 2) ∧
      ∀ᶠ n in atTop, branch x n = .fork (L n) (R n) := by
  let L := branch (x / 2)
  let R := fun n : ℕ => Tree.even (⌊x * n⌋₊ - ⌊x * n⌋₊ / 2)
  have hl : Share L (x / 2) := branch_share (by positivity)
  have split : ∀ᶠ n : ℕ in atTop, branch x n = .fork (L n) (R n) := by
    filter_upwards [(tendsto_nat_floor_mul_atTop x hx).eventually_ge_atTop 2] with n hn
    simp only [branch, L, R]
    rw [Tree.even, show x / 2 * n = x * n / 2 by ring, Nat.floor_div_ofNat]
    simp [hn]
  refine ⟨L, R, hl, ?_, split⟩
  have h := (branch_share hx).sub hl
  rw [show x - x / 2 = x / 2 by ring] at h
  apply h.congr'
  filter_upwards [split] with n he
  simp [he, Tree.leaves, add_div]

private def AsymptoticallyOptimal (T : ℕ → Tree) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ U : Tree, U.leaves = (T n).leaves →
    (U.copies : ℝ) ≤ (T n).copies + ε * ((T n).leaves.choose 5 : ℝ)

private theorem optimal_of_attainment {T : ℕ → Tree} {I : ℝ}
    (hs : Tendsto (fun n => (T n).leaves) atTop atTop) (hI : IsInducibility I)
    (hT : Tendsto (fun n => density (T n)) atTop (𝓝 I)) : AsymptoticallyOptimal T := by
  obtain ⟨f, hmax, hf⟩ := hI
  have gap := (hf.comp hs).sub hT
  rw [sub_self] at gap
  intro ε hε
  filter_upwards [gap.eventually_lt_const hε, hs.eventually_ge_atTop 5] with n hn hn5
  intro U he
  have hm := (hmax (T n).leaves (by omega)).2
    (show density U ∈ {d | ∃ T' : Tree, T'.leaves = (T n).leaves ∧ density T' = d} from
      ⟨U,he,rfl⟩)
  have hpos : 0 < (((T n).leaves.choose 5 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hn5
  change f (T n).leaves - density (T n) < ε at hn
  have hd : density U ≤ density (T n) + ε := by linarith
  unfold density at hd
  rw [he,div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne'] at hd
  exact hd

private theorem rotation_improves {A B C T : ℕ → Tree} {a b c : ℝ}
    (hA : Share A a) (hB : Share B b) (hC : Share C c)
    (ha : 0 < a) (hb : 0 < b) (hac : a < c)
    (align : ∀ᶠ n in atTop,
      (T n).leaves = (Tree.fork (.fork (A n) (B n)) (C n)).leaves ∧
      (T n).copies = (Tree.fork (.fork (A n) (B n)) (C n)).copies) :
    ¬ AsymptoticallyOptimal T := by
  intro opt
  let U := fun n => Tree.fork (A n) (.fork (B n) (C n))
  let g := a * b * c * b * (c-a) / 4
  have hc := ha.trans hac
  have hg : 0 < g := by dsimp [g]; positivity
  have hs : 0 < (a+b+c)^5 := by positivity
  have htotal := share_fork (share_fork hA hB) hC
  have invn := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have rwlim := (((hA.mul hB).mul hC).mul (hB.sub invn)).mul (hC.sub hA)
  have gain : Tendsto (fun n : ℕ => (((U n).copies : ℝ) - (T n).copies) / (n : ℝ)^5)
      atTop (𝓝 g) := by
    rw [sub_zero] at rwlim
    apply (rwlim.div_const 4).congr'
    filter_upwards [align, eventually_ge_atTop 1] with n hn he
    simp only [U, hn.2, rotation]
    field_simp
  let ε := g / (2 * (a+b+c)^5)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hle : g ≤ ε * (a+b+c)^5 := by
    apply le_of_tendsto_of_tendsto gain (tendsto_const_nhds.mul (htotal.pow 5))
    filter_upwards [opt ε hε, align, eventually_ge_atTop 1] with n hopt hmatch hn
    have he : (U n).leaves = (T n).leaves := by
      rw [hmatch.1]
      simp [U, Tree.leaves, Nat.add_assoc]
    have bound := hopt (U n) he
    have binom : (((T n).leaves.choose 5 : ℕ) : ℝ) ≤ ((T n).leaves : ℝ)^5 := by
      exact_mod_cast Nat.choose_le_pow (T n).leaves 5
    have hw := mul_le_mul_of_nonneg_left binom hε.le
    have hpow : (0 : ℝ) < (n : ℝ)^5 := by positivity
    rw [div_le_iff₀ hpow]
    rw [hmatch.1] at hw bound
    simpa [div_pow, mul_assoc, hpow.ne'] using (show
      ((U n).copies : ℝ) - (T n).copies ≤ ε * ((Tree.fork (.fork (A n) (B n)) (C n)).leaves : ℝ)^5
      by linarith)
  have half : ε * (a+b+c)^5 = g / 2 := by
    dsimp [ε]
    field_simp
  linarith

theorem counterexample : ¬ Conjecture := by
  rintro ⟨x, y, z, w, I, hx, hy, hz, hw, _, hI, hT⟩
  have sizes : Tendsto (fun n => (candidate x y z w n).leaves) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [(tendsto_nat_floor_mul_atTop x hx).eventually_ge_atTop (max 1 k)] with n hn
    simp only [candidate, Tree.leaves, branch, even_leaves _ (show 0 < ⌊x * n⌋₊ by omega)]
    omega
  have opt := optimal_of_attainment sizes hI hT
  let ZW := fun n => Tree.fork (branch z n) (branch w n)
  let YZW := fun n => Tree.fork (branch y n) (ZW n)
  have hzw : Share ZW (z+w) := share_fork (branch_share hz) (branch_share hw)
  have hyzw : Share YZW (y+(z+w)) := share_fork (branch_share hy) hzw
  by_cases h : x ≤ y + (z + w)
  · obtain ⟨L, R, hl, hr, split⟩ := even_rotation hx
    apply rotation_improves hl hr hyzw (by positivity) (by positivity) (by linarith) ?_ opt
    filter_upwards [split] with n he
    simp [candidate, YZW, ZW, he]
  · apply rotation_improves (branch_share hy) hzw (branch_share hx) hy (by positivity)
          (by linarith) ?_ opt
    filter_upwards with n
    simp [candidate, ZW, Tree.leaves, Tree.copies]; omega

/-- info: 'WagnerTreeInducibility.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end WagnerTreeInducibility
