module

public import conjectures.ErdosSuranyi708.SeedIndex
public import conjectures.ErdosSuranyi708.SeedArithmetic
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708
open Finset

namespace SeedIndex
variable {P : Finset ℕ} {C : ℕ → Finset ℕ}

def divisor (i : SeedIndex P C) := bucketDivisor i.required i.exponent
def level (M : ℕ) (i : SeedIndex P C) := M / i.divisor
def weights (w : ℕ → ℝ) (i : SeedIndex P C) (p : ℕ) : ℝ := min 1 (w p * i.exponent p)
def retained (Y M : ℕ) (i : SeedIndex P C) : Prop :=
  i.divisor * i.second ≤ M ∧ (i.second ≤ Y ∨ (i.red.card : ℝ) ≤ (Real.log (i.level M))^2)

noncomputable def coefficient (Y M : ℕ) (s : ℝ) (w : ℕ → ℝ) (i : SeedIndex P C) : ℝ := by
  classical
  exact if i.retained Y M then seedWeight s (i.weights w) i.top i.second i.red else 0

noncomputable def term (Y M : ℕ) (s : ℝ) (w : ℕ → ℝ) (i : SeedIndex P C) (b : ℕ) : ℝ :=
  i.coefficient Y M s w * seedPolynomial (i.level M) s C i.required i.exponent i.tail b

theorem divisor_eq (i : SeedIndex P C) :
    i.divisor = seedDivisor (fun r ↦ r^i.exponent r) i.top i.second i.red := by
  simp only [divisor,bucketDivisor,required,requiredLabels,prod_insert i.top_not_second_red,
    prod_insert i.second_not_red,seedDivisor,mul_assoc]

theorem tail_lt (i : SeedIndex P C) {r : ℕ} (hr : r ∈ i.tail) : r < i.second :=
  (mem_filter.mp (mem_sdiff.mp hr).1).2

theorem tail_sub (i : SeedIndex P C) : i.tail ⊆ P := (sdiff_subset.trans (filter_subset ..))

theorem weight_nonneg (i : SeedIndex P C) {w : ℕ → ℝ} (hw : ∀ p ∈ P, 0 ≤ w p)
    {r : ℕ} (hr : r ∈ i.required) : 0 ≤ i.weights w r :=
  le_min zero_le_one (mul_nonneg (hw r (i.req_sub hr)) (Nat.cast_nonneg _))

theorem coefficient_bounds (i : SeedIndex P C) (Y M : ℕ) {s : ℝ} {w : ℕ → ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hw : ∀ p ∈ P, 0 ≤ w p) :
    0 ≤ i.coefficient Y M s w ∧ i.coefficient Y M s w ≤ 1 := by
  classical
  simp only [coefficient]
  split
  · have h1 := i.weight_nonneg hw (mem_insert_self .. : i.top ∈ i.required)
    have h2 := i.weight_nonneg hw (mem_insert_of_mem (mem_insert_self ..) : i.second ∈ i.required)
    exact ⟨mul_nonneg (pow_nonneg hs _) (crossingLength_nonneg h1 h2),
      (mul_le_of_le_one_left (crossingLength_nonneg h1 h2) (pow_le_one₀ hs hs1)).trans
        ((crossingLength_le h1).trans (min_le_left ..))⟩
  · exact ⟨le_rfl,zero_le_one⟩

theorem retained_of_nonzero (i : SeedIndex P C) {Y M : ℕ} {s : ℝ} {w : ℕ → ℝ}
    (h : i.coefficient Y M s w ≠ 0) : i.retained Y M := by
  by_contra hn
  simp [coefficient,hn] at h

theorem required_weight_le (i : SeedIndex P C) {Y M : ℕ} {s : ℝ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ P, 0 ≤ w p) (h : i.coefficient Y M s w ≠ 0) :
    ∑ r ∈ i.required, i.weights w r ≤ 3 := by
  have hh := i.retained_of_nonzero h
  have h1 := i.weight_nonneg hw (mem_insert_self .. : i.top ∈ i.required)
  have h2 := i.weight_nonneg hw (mem_insert_of_mem (mem_insert_self ..) : i.second ∈ i.required)
  have hred : ∑ r ∈ i.red, i.weights w r < 1 := by
    by_contra! hr
    simp [coefficient,hh,seedWeight,crossingLength_of_one_le hr h1 h2] at h
  rw [required,requiredLabels,sum_insert i.top_not_second_red,sum_insert i.second_not_red]
  have htop : i.weights w i.top ≤ 1 := min_le_left ..
  have hq : i.weights w i.second ≤ 1 := min_le_left ..
  linarith only [hred,htop,hq]

theorem divisor_pos (i : SeedIndex P C) (hp : ∀ r ∈ P, r.Prime) : 0 < i.divisor :=
  bucketDivisor_pos _ (fun r hr ↦ hp r (i.req_sub hr))

theorem second_le_level (i : SeedIndex P C) {Y M : ℕ} (hp : ∀ r ∈ P, r.Prime)
    (hr : i.retained Y M) : i.second ≤ i.level M :=
  (Nat.le_div_iff_mul_le (i.divisor_pos hp)).mpr ((Nat.mul_comm ..).trans_le hr.1)

end SeedIndex

theorem sum_terms {Y K M : ℕ} {P : Finset ℕ} (w : ℕ → ℝ) (s : ℝ)
    (hp : ∀ p ∈ P, p.Prime) {a : ℕ} (ha : 0 < a) :
    (∑ i : SeedIndex P (grid Y K M w), i.term Y M s w a) = transferSum Y K M s P w a := by
  classical
  let T := activeLabels P a
  let v := siteWeight Y K M w a
  let c := siteCost Y K M w a
  let f := fun (p q : ℕ) (V : Finset ℕ) ↦ if goodSeed Y M c p q V then
    seedValue M s v c (earlier T q) p q V else 0
  change (∑ i : SeedIndex P (grid Y K M w), i.term Y M s w a) =
    ∑ p ∈ T, ∑ q ∈ earlier T p, ∑ V ∈ (earlier T q).powerset, f p q V
  apply project_seed_sum (fun p _ ↦ grid_one ..) hp ha
  · intro i hmatch
    have hc (r : ℕ) (hr : r ∈ i.required) : r ^ i.exponent r = c r := by
      change r ^ i.exponent r = r ^ lastCut _ (a.factorization r)
      rw [(hmatch r hr).2]
    have hv (r : ℕ) (hr : r ∈ i.required) : i.weights w r = v r := by
      change min 1 (_ * (i.exponent r : ℝ)) = min 1 (_ * (lastCut _ (a.factorization r) : ℝ))
      rw [(hmatch r hr).2]
    have htop : i.top ∈ i.required := mem_insert_self ..
    have hq : i.second ∈ i.required := mem_insert_of_mem (mem_insert_self ..)
    have hV : i.red ⊆ i.required := fun _ hr ↦ mem_insert_of_mem (mem_insert_of_mem hr)
    have hd : i.divisor = seedDivisor c i.top i.second i.red := by
      rw [i.divisor_eq]
      simp only [seedDivisor]
      rw [hc _ htop,hc _ hq,prod_congr rfl (fun r hr ↦ hc r (hV hr))]
    have hww : seedWeight s (i.weights w) i.top i.second i.red = seedWeight s v i.top i.second i.red := by
      rw [seedWeight,seedWeight,hv _ htop,hv _ hq,sum_congr rfl (fun r hr ↦ hv r (hV hr))]
    have htail : i.tail.filter (· ∣ a) = earlier T i.second \ i.red := by
      ext r
      simp [SeedIndex.tail,T,activeLabels,earlier,and_assoc,and_left_comm,and_comm]
    have hb : bucketMatch (grid Y K M w) i.required i.exponent a := hmatch
    simp only [SeedIndex.term,SeedIndex.coefficient,SeedIndex.retained,SeedIndex.level,seedPolynomial,
      f,goodSeed,seedValue,hd,hww,hb,ite_true,htail]
    split_ifs <;> grind
  · intro i hn
    have hnot : ¬bucketMatch (grid Y K M w) i.required i.exponent a := hn
    simp [SeedIndex.term,seedPolynomial,hnot]

end ErdosSuranyi708
