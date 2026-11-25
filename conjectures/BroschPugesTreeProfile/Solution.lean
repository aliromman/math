module

public import conjectures.BroschPugesTreeProfile.Statement
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
open Filter Topology Asymptotics
namespace BroschPugesTreeProfile
open BroschPugesTreeProfile.Tree

private def isCat : Tree → Bool
  | leaf => true
  | fork leaf T => isCat T
  | fork T leaf => isCat T
  | fork _ _ => false

@[simp] private theorem cat_leaves (n : ℕ) : (cat n).leaves = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cat, leaves, ih, Nat.add_comm]

private theorem in_caterpillar (n : ℕ) (S : Tree) :
    (cat n).copies S = if isCat S then (n+1).choose S.leaves else 0 := by
  induction n generalizing S with
  | zero =>
    cases S with
    | leaf => rfl
    | fork A B =>
      have pos (T : Tree) : 0 < T.leaves := by
        induction T with
        | leaf => decide
        | fork _ _ ih _ => simpa [leaves] using Nat.add_pos_left ih _
      simp [cat, copies, leaves, Nat.choose_eq_zero_of_lt (show 1 < A.leaves+B.leaves by
        have := pos A; have := pos B; omega)]
  | succ n ih =>
    cases S with
    | leaf => simp [cat, copies, leaves, isCat, ih, Nat.add_comm]
    | fork A B =>
      have pas (P : Prop) [Decidable P] (k : ℕ) :
          (if P then (n+1).choose (k+1) else 0) + (if P then (n+1).choose k else 0) =
          (if P then (n+1+1).choose (k+1) else 0) := by
        by_cases h : P
        · simp only [ite_eq_left h]
          exact (Nat.add_comm ..).trans (Nat.choose_succ_succ (n+1) k).symm
        · simp [h]
      cases A <;> cases B <;>
        simp only [cat, copies, ih, isCat, same, leaves, ite_true, ite_false, Nat.zero_mul,
          Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.one_add, Bool.false_eq_true]
      · exact (Nat.add_comm ..).trans (Nat.choose_succ_succ (n+1) 1).symm
      · exact pas _ _
      · exact pas _ _
      · simp

/-- Normalize a pattern count by the leading term in the number of subsets. -/
private noncomputable def scaled (a k n : ℕ) : ℝ :=
  (a:ℝ) * k.factorial / (200*(n:ℝ))^k

private theorem scaled_add (a b k n : ℕ) :
    scaled (a+b) k n = scaled a k n + scaled b k n := by simp [scaled, add_mul, add_div]

private theorem scaled_mul (a b i j n : ℕ) :
    scaled (a*b) (i+j) n = ((i+j).choose i : ℝ) * scaled a i n * scaled b j n := by
  have H : (((i+j).choose i : ℝ) * i.factorial * j.factorial) = (i+j).factorial := by
    exact_mod_cast (by simpa using (Nat.choose_mul_factorial_mul_factorial (n := i+j)
      (k := i) (by omega)) : (i+j).choose i * i.factorial * j.factorial = (i+j).factorial)
  simp only [scaled, Nat.cast_mul, ← H, pow_add, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem choose_limit (a b k : ℕ) (ha : 0 < a) :
    Tendsto (fun n => scaled ((a*n+b).choose k) k n) atTop (𝓝 (((a:ℝ)/200)^k)) := by
  have zg : ∀ᶠ n : ℕ in atTop, (n:ℝ)^k/k.factorial ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  have ht : Tendsto (fun n : ℕ => a*n+b) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun t => ?_
    exact ⟨t, fun n hn => by have := Nat.mul_le_mul_right n ha; omega⟩
  have hh := ((isEquivalent_iff_tendsto_one zg).mp (isEquivalent_choose k)).comp ht
  have hL : Tendsto (fun n : ℕ => ((a*n+b:ℕ):ℝ)/(200*(n:ℝ))) atTop (𝓝 ((a:ℝ)/200)) := by
    have hh := (tendsto_const_nhds (x := (a:ℝ))).add
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b:ℝ))
    rw [mul_zero, add_zero] at hh
    apply (hh.div_const 200).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    push_cast
    field_simp
  rw [← one_mul (((a:ℝ)/200)^k)]
  apply (hh.mul (hL.pow k)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change (↑((a*n+b).choose k) / (((a*n+b:ℕ):ℝ)^k/k.factorial)) *
    (((a*n+b:ℕ):ℝ)/(200*(n:ℝ)))^k = _
  have hpos : 0 < a*n+b := by positivity
  simp only [scaled, div_pow]
  field_simp

private def HasLimits (T : ℕ → Tree) (f : Tree → ℝ) : Prop :=
  ∀ S, Tendsto (fun n => scaled ((T n).copies S) S.leaves n) atTop (𝓝 (f S))

private noncomputable def branch (a : ℕ) (S : Tree) : ℝ :=
  if isCat S then ((a:ℝ)/200)^S.leaves else 0

private theorem branch_limits (a : ℕ) (ha : 0 < a) :
    HasLimits (fun n => cat (a*n)) (branch a) := by
  intro S
  simp only [in_caterpillar, branch]
  split
  · exact choose_limit a 1 _ ha
  · simp [scaled]

private noncomputable def join (f g : Tree → ℝ) (S : Tree) : ℝ :=
  f S + g S + match S with
  | leaf => 0
  | fork A B => ((A.leaves+B.leaves).choose A.leaves : ℝ) * f A * g B +
      if same A B then 0 else ((B.leaves+A.leaves).choose B.leaves : ℝ) * f B * g A

private theorem join_limits {L R : ℕ → Tree} {f g : Tree → ℝ}
    (hf : HasLimits L f) (hg : HasLimits R g) :
    HasLimits (fun n => fork (L n) (R n)) (join f g) := by
  intro S
  cases S with
  | leaf =>
    simpa [copies, scaled_add, join] using (hf leaf).add (hg leaf)
  | fork A B =>
    have hmain := (hf (fork A B)).add (hg (fork A B))
    have hab := ((hf A).const_mul (((A.leaves+B.leaves).choose A.leaves : ℝ))).mul (hg B)
    have hba := ((hf B).const_mul (((B.leaves+A.leaves).choose B.leaves : ℝ))).mul (hg A)
    by_cases h : same A B = true
    · simpa [copies, h, scaled_add, scaled_mul, leaves, join] using hmain.add hab
    · have sw n : scaled ((L n).copies B*(R n).copies A) (A.leaves+B.leaves) n =
          ((B.leaves+A.leaves).choose B.leaves : ℝ) * scaled ((L n).copies B) B.leaves n *
          scaled ((R n).copies A) A.leaves n := by
        rw [Nat.add_comm A.leaves B.leaves, scaled_mul]
      simpa [copies, h, scaled_add, leaves, sw, scaled_mul, join] using
        hmain.add (hab.add hba)

private noncomputable def inner := join (branch 47) (branch 47)
private noncomputable def witness := join (branch 106) inner

private theorem witness_profile (A B : Tree) : InProfile A B (witness A) (witness B) := by
  let T (n : ℕ) := fork (cat (106*n)) (fork (cat (47*n)) (cat (47*n)))
  have size n : (T n).leaves = 200*n+3 := by simp [T, leaves]; omega
  have h := join_limits (branch_limits 106 (by decide))
    (join_limits (branch_limits 47 (by decide)) (branch_limits 47 (by decide)))
  have hD (S : Tree) : Tendsto (fun n => S.density (T n)) atTop (𝓝 (witness S)) := by
    have hden := choose_limit 200 3 S.leaves (by decide)
    norm_num at hden
    have H := (h S).div hden (by norm_num)
    rw [div_one] at H
    apply H.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    change scaled ((T n).copies S) S.leaves n / scaled ((200*n+3).choose S.leaves) S.leaves n =
      S.density (T n)
    rw [density, size]
    simp only [scaled, div_div_div_cancel_right₀ (by positivity : (200*(n:ℝ))^S.leaves ≠ 0),
      mul_div_mul_right _ _ (by positivity : (S.leaves.factorial:ℝ) ≠ 0)]
  refine ⟨T, ?_, fun S => ⟨_,hD S⟩, hD A, hD B⟩
  intro i j hij
  simp only [size]
  omega

private theorem branch_cat (a n : ℕ) : branch a (cat n) = ((a:ℝ)/200)^(n+1) := by
  have hh : isCat (cat n) = true := by induction n with
    | zero => rfl
    | succ n ih => exact ih
  simp [branch, hh]

/-- A caterpillar that uses both branches has one leaf on one side. -/
private theorem join_cat (f g : Tree → ℝ) (n : ℕ) :
    join f g (cat (n+2)) = f (cat (n+2)) + g (cat (n+2)) +
      ((n:ℝ)+3) * (f leaf * g (cat (n+1)) + f (cat (n+1)) * g leaf) := by
  rw [show cat (n+2) = fork leaf (cat (n+1)) from rfl]
  have no : same leaf (cat (n+1)) = false := rfl
  simp [join, no, leaves, cat_leaves, Nat.one_add]
  ring

private theorem witness_even :
    witness evenSix = 5/16 + 18048673/3200000000000 := by
  norm_num [witness, inner, join, branch, evenSix, cat, leaves, same, isCat, Nat.choose]

private theorem edges_le_binomial (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a^(n+3)+b^(n+3)+((n:ℝ)+3)*(a*b^(n+2)+a^(n+2)*b) ≤ (a+b)^(n+3) := by
  induction n with
  | zero => push_cast; ring_nf; rfl
  | succ n ih =>
    calc
      _ ≤ (a^(n+3)+b^(n+3)+((n:ℝ)+3)*(a*b^(n+2)+a^(n+2)*b))*(a+b) := by
        have e : (a^(n+3)+b^(n+3)+((n:ℝ)+3)*(a*b^(n+2)+a^(n+2)*b))*(a+b) =
            a^(n+1+3)+b^(n+1+3)+((n:ℝ)+1+3)*(a*b^(n+1+2)+a^(n+1+2)*b) +
            ((n:ℝ)+3)*(a^2*b^(n+2)+a^(n+2)*b^2) := by ring
        rw [e]
        push_cast
        exact le_add_of_nonneg_right (by positivity)
      _ ≤ _ := by
        simpa only [pow_succ (a+b) (n+3)] using
          (mul_le_mul_of_nonneg_right ih (add_nonneg ha hb))

private noncomputable abbrev u : ℝ := 53/100
private noncomputable abbrev v : ℝ := 47/200

private theorem inner_leaf : inner leaf = 2*v := by norm_num [inner, join, branch, isCat, leaves, v]
private theorem branch_leaf (a : ℕ) : branch a leaf = (a:ℝ)/200 := by simp [branch, isCat, leaves]

private theorem inner_cat (n : ℕ) :
    inner (cat (n+2)) = v^(n+3)+v^(n+3)+((n:ℝ)+3)*(v*v^(n+2)+v^(n+2)*v) := by
  rw [inner, join_cat, branch_cat, branch_cat, branch_leaf]
  norm_num [v]

private theorem inner_bound (n : ℕ) : inner (cat (n+2)) ≤ (2*v)^(n+3) := by
  rw [inner_cat, two_mul]
  exact edges_le_binomial v v (by norm_num [v]) (by norm_num [v]) n

private theorem witness_cat (n : ℕ) :
    witness (cat (n+3)) = u^(n+4) + inner (cat (n+3)) + ((n:ℝ)+4) *
      (u * inner (cat (n+2)) + u^(n+3)*(2*v)) := by
  unfold witness
  rw [join_cat _ _ (n+1), branch_cat, branch_cat, branch_leaf, inner_leaf]
  push_cast
  norm_num [u]
  left; ring

private theorem witness_bound (n : ℕ) : witness (cat (n+3)) ≤ 1 := by
  rw [witness_cat]
  calc
    _ ≤ u^(n+4) + (2*v)^(n+4) + ((n:ℝ)+4) * (u*(2*v)^(n+3)+u^(n+3)*(2*v)) := by
      gcongr
      · exact inner_bound (n+1)
      · exact inner_bound n
    _ ≤ (u+2*v)^(n+4) := by
      have H := edges_le_binomial u (2*v) (by norm_num [u]) (by norm_num [v]) (n+1)
      convert H using 1; push_cast; ring
    _ = 1 := by norm_num [u,v]

private theorem witness_lower (n : ℕ) :
    ((n:ℝ)+15) / 2^(n+13) ≤ witness (cat (n+13)) := by
  rw [witness_cat (n+10)]
  have hh (t : ℕ) : 0 ≤ inner (cat (t+2)) := by rw [inner_cat]; positivity
  have base : 1 ≤ (47/100:ℝ)*(53/50)^(n+13) := by
    calc
      _ ≤ (47/100:ℝ)*(53/50)^13 := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by norm_num)
  have h : (((n:ℝ)+15) / 2^(n+13)) ≤ ((n:ℝ)+15)*(2*v)*u^(n+13) := by
    rw [div_le_iff₀ (by positivity)]
    have H := mul_le_mul_of_nonneg_left base (by positivity : (0:ℝ) ≤ n+15)
    rw [show (53/50:ℝ) = u*2 by norm_num [u], mul_pow] at H
    convert H using 1 <;> ring
  calc
    _ ≤ ((n:ℝ)+15)*(2*v)*u^(n+13) := h
    _ ≤ _ := by
      have e : (u^(n+14) + inner (cat (n+13)) + ((n:ℝ)+14) *
          (u*inner (cat (n+12))+u^(n+13)*(2*v))) - ((n:ℝ)+15)*(2*v)*u^(n+13) =
            (u-2*v)*u^(n+13) + inner (cat (n+13)) + ((n:ℝ)+14)*u*inner (cat (n+12)) := by ring
      have hh13 := hh (n+11)
      have hh12 := hh (n+10)
      have hc : 0 ≤ u-2*v := by norm_num [u,v]
      push_cast
      apply sub_nonneg.mp
      have G : 0 ≤ (u-2*v)*u^(n+13) + inner (cat (n+13)) + ((n:ℝ)+14)*u*inner (cat (n+12)) :=
        add_nonneg (add_nonneg (mul_nonneg hc (by positivity)) hh13) (mul_nonneg (by positivity) hh12)
      rw [← e] at G
      convert G using 1; ring

private theorem double_le (p : ℝ) (hp : p ∈ Set.Icc 0 1) : doubleEven p ≤ 5/16 := by
  have h : p*(1-p) ≤ 1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have h0 : 0 ≤ p*(1-p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  calc
    _ = 20*(p*(1-p))^3 := by simp [doubleEven]; ring
    _ ≤ 20*(1/4:ℝ)^3 := by gcongr
    _ = _ := by norm_num

/-- The same sequence of three caterpillars defeats the claimed upper boundary at every k ≥ 14. -/
theorem fails_from_fourteen (k : ℕ) (hk : 14 ≤ k) :
    ∃ p ∈ Set.Icc (0:ℝ) 1, ∃ y, InProfile (cat (k-1)) evenSix (doubleCat k p) y ∧
      doubleEven p < y := by
  obtain ⟨n,rfl⟩ : ∃ n, k = n+14 := ⟨k-14,by omega⟩
  have lo : doubleCat (n+14) (1/2) = ((n:ℝ)+15)/2^(n+13) := by
    simp only [doubleCat, show (1:ℝ)-1/2 = 1/2 by norm_num, show n+14-1 = n+13 by omega,
      div_pow, one_pow, Nat.cast_add, Nat.cast_ofNat]
    rw [show n+14=(n+13)+1 by omega, pow_succ]
    ring
  have hi : doubleCat (n+14) 1 = 1 := by simp [doubleCat]
  have mem : witness (cat (n+13)) ∈ Set.Icc (doubleCat (n+14) (1/2)) (doubleCat (n+14) 1) := by
    rw [lo,hi]
    exact ⟨witness_lower n, witness_bound (n+10)⟩
  obtain ⟨p,hp,E⟩ := intermediate_value_Icc (show (1/2:ℝ) ≤ 1 by norm_num)
    (show ContinuousOn (doubleCat (n+14)) _ by unfold doubleCat; fun_prop) mem
  have h01 : p ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans (by norm_num) hp.1,hp.2⟩
  refine ⟨p,h01,witness evenSix,?_,(double_le p h01).trans_lt ?_⟩
  · rw [E, show n+14-1 = n+13 by omega]
    exact witness_profile _ _
  · rw [witness_even]; norm_num

theorem not_conjecture : ¬ Conjecture := by
  intro H
  obtain ⟨p,hp,y,hy,hlt⟩ := fails_from_fourteen 14 le_rfl
  exact hlt.not_ge ((H 14 (by decide) p hp).2 hy)

/-- info: 'BroschPugesTreeProfile.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end BroschPugesTreeProfile
