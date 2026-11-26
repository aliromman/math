module

public import conjectures.WordPacking121.Statement
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

namespace WordPacking121

open Filter Topology

/-- Split off the first maximal strictly increasing run. Its last letter is `z`. -/
private theorem firstRun (a : ℕ) (w : List ℕ) :
    ∃ p z s, a :: w = p ++ z :: s ∧ (p ++ [z]).IsChain (· < ·) ∧
      ∀ b ∈ s.head?, b ≤ z := by
  induction w generalizing a with
  | nil => exact ⟨[], a, [], by simp⟩
  | cons b t ih =>
    by_cases h : a < b
    · obtain ⟨p, z, s, hw, hp, hs⟩ := ih b
      refine ⟨a :: p, z, s, by simp [hw], ?_, hs⟩
      apply List.isChain_cons.mpr
      refine ⟨?_, hp⟩
      cases p <;> simp_all
    · exact ⟨[], a, b :: t, by simp [Nat.le_of_not_gt h]⟩

/-- There is no occurrence entirely inside a rising run. Each of its letters except the last
can start one occurrence for each copy of that letter in the suffix. -/
private theorem occurrences_run (p : List ℕ) (z : ℕ) (s : List ℕ)
    (hp : (p ++ [z]).Pairwise (· < ·)) (hs : ∀ b ∈ s.head?, b ≤ z) :
    occurrences (p ++ z :: s) = (p.map (fun x => s.count x)).sum + occurrences s := by
  induction p with
  | nil =>
    cases s with
    | nil => rfl
    | cons b t => simp_all [occurrences, Nat.not_lt.mpr]
  | cons a p ih =>
    obtain ⟨ha, hp⟩ := List.pairwise_cons.mp hp
    have hzero : (p ++ [z]).count a = 0 := List.count_eq_zero.mpr (fun h => (lt_irrefl a) (ha a h))
    have hc : (p ++ z :: s).count a = s.count a := by
      change ((p ++ ([z] ++ s)).count a) = _
      rw [← List.append_assoc, List.count_append, hzero, Nat.zero_add]
    rw [List.cons_append]
    change (match p ++ z :: s with
      | [] => 0
      | b :: _ => if a < b then (p ++ z :: s).count a else 0) + occurrences (p ++ z :: s) = _
    have hhead : (match p ++ z :: s with
      | [] => 0
      | b :: _ => if a < b then (p ++ z :: s).count a else 0) = s.count a := by
      cases p with
      | nil => simp_all
      | cons b t => have hab := ha b (by simp); simpa [hab] using hc
    rw [hhead, ih hp]
    simp [Nat.add_assoc]

private theorem sum_counts_le (p s : List ℕ) (hp : p.Nodup) :
    (p.map (fun x => s.count x)).sum ≤ s.length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have h : (p.map (fun x => (a :: s).count x)).sum =
        p.count a + (p.map (fun x => s.count x)).sum := by
      clear hp ih
      induction p with
      | nil => simp
      | cons x p ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        by_cases e : a = x
        · subst x
          simp; omega
        · simp [e, Ne.symm e]; omega
    have hone := List.nodup_iff_count.mp hp a
    simp only [h, List.length_cons]
    omega

/-- `d` counts the rising runs with at least two letters. Each such run contains a letter
unequal to any prescribed `x`. -/
private theorem run_bound (w : List ℕ) : ∃ d : ℕ,
    2 * d ≤ w.length ∧ (∀ x : ℕ, w.count x + d ≤ w.length) ∧
    2 * occurrences w + 3 * d ^ 2 + d ≤ 2 * w.length * d := by
  generalize hg : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    subst n
    cases w with
    | nil => exact ⟨0, by simp [occurrences]⟩
    | cons a t =>
      obtain ⟨p, z, s, hw, hchain, hs⟩ := firstRun a t
      have hp : (p ++ [z]).Pairwise (· < ·) := hchain.pairwise
      have hlen := congrArg List.length hw
      simp only [List.length_cons, List.length_append] at hlen
      obtain ⟨d, hd, hc, hh⟩ := ih s.length (by simp only [List.length_cons]; omega) s rfl
      rw [hw, occurrences_run p z s hp hs]
      have hnd : (p ++ [z]).Nodup := hp.imp (fun h => Nat.ne_of_lt h)
      have hlen' : (p ++ z :: s).length = p.length + 1 + s.length := by simp; omega
      rw [hlen']
      cases p with
      | nil =>
        refine ⟨d, by simp only [List.length_nil]; omega, ?_, ?_⟩
        · intro x
          have hcx := hc x
          simp [List.count_cons]; split <;> omega
        · simpa using (show 2 * occurrences s + 3 * d ^ 2 + d ≤ 2 * (0 + 1 + s.length) * d by nlinarith)
      | cons b p =>
        refine ⟨d + 1, ?_, ?_, ?_⟩
        · simp; omega
        · intro x
          have hx := List.nodup_iff_count.mp hnd x
          have hcx := hc x
          change ((b :: p) ++ z :: s).count x + (d + 1) ≤ _
          change (((b :: p) ++ ([z] ++ s)).count x) + (d + 1) ≤ _
          rw [← List.append_assoc, List.count_append]
          simp only [List.length_cons]; omega
        · cases p with
          | nil =>
            have hcb := hc b
            simp only [List.map_cons, List.map_nil, List.sum_singleton, List.length_cons, List.length_nil]
            nlinarith
          | cons c p =>
            have hs' := sum_counts_le (b :: c :: p) s (List.nodup_append.mp hnd).1
            simp only [List.length_cons]
            nlinarith [Nat.zero_le (p.length * d)]

private def binaryWord (d r : ℕ) : List ℕ :=
  match d with
  | 0 => List.replicate r 0
  | d + 1 => 0 :: 1 :: binaryWord d r

private theorem no_rise (z : ℕ) (s : List ℕ) (hs : ∀ b ∈ s, b ≤ z) :
    occurrences (z :: s) = occurrences s := by
  cases s with
  | nil => rfl
  | cons b t => simp [occurrences, Nat.not_lt.mpr (hs b (by simp))]

private theorem binary_stats (d r : ℕ) :
    (binaryWord d r).length = 2 * d + r ∧
    (∀ x ∈ binaryWord d r, x ≤ 1) ∧ (binaryWord d r).count 0 = d + r ∧
    2 * occurrences (binaryWord d r) + d = d ^ 2 + 2 * d * r := by
  induction d with
  | zero =>
    have hz (t : ℕ) : occurrences (List.replicate t 0) = 0 := by
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [List.replicate_succ, no_rise, ih]
        simp +contextual
    simp [binaryWord, hz]
  | succ d ih =>
    obtain ⟨hl, ha, hc, hh⟩ := ih
    change (0 :: 1 :: binaryWord d r).length = _ ∧ _
    refine ⟨by simp [hl]; omega, ?_, ?_, ?_⟩
    · simpa [binaryWord] using ha
    · simp [binaryWord, hc]; omega
    · have h : occurrences (0 :: 1 :: binaryWord d r) =
          (binaryWord d r).count 0 + occurrences (binaryWord d r) := by
        change (if 0 < 1 then (1 :: binaryWord d r).count 0 else 0) +
          occurrences (1 :: binaryWord d r) = _
        simp [no_rise 1 _ ha]
      change 2 * occurrences (0 :: 1 :: binaryWord d r) + _ = _
      rw [h, hc]; nlinarith

private theorem le_maximum (k : ℕ) (w : List ℕ) (hw : ∀ a ∈ w, a < k) :
    occurrences w ≤ maximum k w.length := by
  let f : Fin w.length → Fin k := fun i => ⟨w.get i, hw _ (List.get_mem w i)⟩
  have h := Finset.le_sup (f := fun u : Fin w.length → Fin k =>
    occurrences ((List.ofFn u).map Fin.val)) (Finset.mem_univ f)
  simpa [maximum, f, List.map_ofFn, Function.comp_def] using h

private theorem binary_max (d r k : ℕ) (hk : 2 ≤ k) :
    occurrences (binaryWord d r) ≤ maximum k (2 * d + r) := by
  obtain ⟨hl, ha, _⟩ := binary_stats d r
  rw [← hl]
  exact le_maximum _ _ fun x hx => by have := ha x hx; omega

private theorem numerator (n : ℕ) : n * (n - 1) + n = n ^ 2 := by
  cases n with
  | zero => rfl
  | succ n => simp; ring

private theorem maximum_upper (k n : ℕ) : maximum k n ≤ n * (n - 1) / 6 := by
  apply Finset.sup_le
  intro u _
  let w := (List.ofFn u).map Fin.val
  have hw : w.length = n := by simp [w]
  obtain ⟨d, _, _, hu⟩ := run_bound w
  rw [hw] at hu
  change occurrences w ≤ _
  rw [Nat.le_div_iff_mul_le (by decide)]
  have hn := numerator n
  zify at hu hn ⊢
  let x : ℤ := (n : ℤ) - 3 * d
  have hx : 0 ≤ x * (x - 1) := by
    by_cases h : 0 < x
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  dsimp [x] at hx
  nlinarith

private theorem maximum_lower (k n : ℕ) (hk : 2 ≤ k) : n ^ 2 ≤ 6 * maximum k n + n + 2 := by
  let d := n / 3
  let t := n % 3
  have ht : t ≤ 2 := by dsimp [t]; omega
  have h : n = 3 * d + t := by dsimp [t,d]; omega
  let r := d + t
  have hr : 2 * d + r = n := by dsimp [r]; omega
  obtain ⟨_, _, _, he⟩ := binary_stats d r
  have hb := binary_max d r k hk
  rw [hr] at hb
  dsimp only [r] at he
  have ht' : t ^ 2 ≤ t + 2 := by nlinarith
  nlinarith

/-- Two letters attain the exact maximum for every word length. -/
public theorem maximum_formula (k n : ℕ) (hk : 2 ≤ k) :
    maximum k n = n * (n - 1) / 6 := by
  exact le_antisymm (maximum_upper k n) (by have := numerator n; have := maximum_lower k n hk; omega)

private theorem maximum_small (k n : ℕ) (hk : k < 2) : maximum k n = 0 := by
  apply Nat.le_zero.mp
  apply Finset.sup_le
  intro u _
  have hz : ∀ a ∈ (List.ofFn u).map Fin.val, a = 0 := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    have := b.isLt
    omega
  generalize hw : (List.ofFn u).map Fin.val = w at *
  clear hw
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha := hz a (by simp)
    have he : ∀ b ∈ w, b ≤ a := by
      intro b hb
      have := hz b (by simp [hb]); omega
    rw [no_rise _ _ he]
    apply ih
    · intro b hb; exact hz b (by simp [hb])

private theorem density_bounds (n : ℕ) :
    1 / 3 ≤ density 2 (n + 3) ∧
    density 2 (n + 3) ≤ 1 / 3 + (2 / 3) * (1 / ((n : ℝ) + 1)) := by
  let m := maximum 2 (n + 3)
  have hu := maximum_upper 2 (n + 3)
  rw [Nat.le_div_iff_mul_le (by decide)] at hu
  have hl := maximum_lower 2 (n + 3) (by decide)
  have hm : (maximum 2 (n + 3)) = m := rfl
  rw [hm] at hu hl
  have sub : n + 3 - 1 = n + 2 := by omega
  rw [sub] at hu
  have hu' : (m : ℝ) * 6 ≤ ((n : ℝ) + 3) * (n + 2) := by exact_mod_cast hu
  have hl' : ((n : ℝ) + 3) ^ 2 ≤ 6 * m + ((n : ℝ) + 3) + 2 := by exact_mod_cast hl
  have hC : (n + 2).choose 2 * 2 = (n + 2) * (n + 1) := by
    simpa using (Nat.add_one_mul_choose_eq (n + 1) 1).symm
  have hC' : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * (n + 1) / 2 := by
    have : ((n + 2).choose 2 : ℝ) * 2 = ((n : ℝ) + 2) * (n + 1) := by exact_mod_cast hC
    linarith
  simp only [density, sub, hm, hC']
  have hp : 0 < ((n : ℝ) + 2) * (n + 1) / 2 := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  · calc
      _ ≤ (((n : ℝ) + 3) * (n + 2) / 6) / (((n : ℝ) + 2) * (n + 1) / 2) := by
        apply (div_le_div_iff_of_pos_right hp).mpr
        linarith
      _ = _ := by field_simp; ring

private theorem density_tendsto : Tendsto (density 2) atTop (𝓝 (1 / 3)) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  apply tendsto_const_nhds.squeeze (h := fun n : ℕ => 1 / 3 + (2 / 3 : ℝ) * (1 / ((n : ℝ) + 1)))
  · simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  · exact fun n => (density_bounds n).1
  · exact fun n => (density_bounds n).2

private theorem density_eq (k n : ℕ) (hk : 2 ≤ k) : density k n = density 2 n := by
  simp only [density, maximum_formula k n hk, maximum_formula 2 n (by decide)]

public theorem resolution : Conjecture := by
  constructor
  · refine ⟨fun k => if 2 ≤ k then 1 / 3 else 0, ?_, ?_⟩
    · intro k
      by_cases h : 2 ≤ k
      · simp only [ite_eq_left h]
        simpa only [funext fun n => density_eq k n h] using density_tendsto
      · simp only [ite_eq_right h]
        have he (n : ℕ) : density k n = 0 := by simp [density, maximum_small k n (by omega)]
        simpa only [funext he] using (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 2] with k hk using (ite_eq_left hk).symm
  · refine ⟨density 2, ?_, density_tendsto⟩
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with k hk using (density_eq k n hk).symm

end WordPacking121


/-- info: 'WordPacking121.maximum_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WordPacking121.maximum_formula
/-- info: 'WordPacking121.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WordPacking121.resolution
