import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BorgSignedSets

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev Cube (ι κ : Type*) := ι → κ

def avg {α : Type*} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ x, f x) / Fintype.card α

def energy {α : Type*} [Fintype α] (f : α → ℚ) : ℚ := avg (fun x => f x ^ 2)

theorem avg_sum {α β : Type*} [Fintype α] (S : Finset β) (g : β → α → ℚ) :
    avg (fun x => ∑ i ∈ S, g i x) = ∑ i ∈ S, avg (g i) := by
  simp only [avg, div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem avg_comm {α β : Type*} [Fintype α] [Fintype β] (g : α → β → ℚ) :
    avg (fun x => avg (g x)) = avg (fun y => avg (fun x => g x y)) := by
  simp only [avg, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem avg_mul_left {α : Type*} [Fintype α] (a : ℚ) (g : α → ℚ) :
    avg (fun x => a * g x) = a * avg g := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

theorem avg_mul_right {α : Type*} [Fintype α] (g : α → ℚ) (a : ℚ) :
    avg (fun x => g x * a) = avg g * a := by
  simpa only [mul_comm a] using avg_mul_left a g

@[simp] theorem avg_zero {α : Type*} [Fintype α] : avg (fun _ : α => (0:ℚ)) = 0 := by
  simp [avg]

@[simp] theorem avg_const {α : Type*} [Fintype α] [Nonempty α] (a : ℚ) :
    avg (fun _ : α => a) = a := by
  have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [avg, nsmul_eq_mul, hn]

theorem energy_eq_zero {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) :
    energy f = 0 ↔ ∀ x, f x = 0 := by
  have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [energy, avg, div_eq_zero_iff, hn, or_false]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (f x))]
  simp

private def kernel (a b : κ) : ℚ :=
  (if a = b then (Fintype.card κ : ℚ) else 0) - 1

def component (f : Cube ι κ → ℚ) (S : Finset ι) (x : Cube ι κ) : ℚ :=
  avg (fun y => f y * ∏ i ∈ S, kernel (x i) (y i))

/-- Average over the full words that have the same labels as `x` on `B`. -/
def sectionMean (f : Cube ι κ → ℚ) (B : Finset ι) (x : Cube ι κ) : ℚ :=
  avg (fun y => f y * ∏ i ∈ B, (1 + kernel (x i) (y i)))

theorem sectionMean_components (f : Cube ι κ → ℚ) (B : Finset ι) (x : Cube ι κ) :
    sectionMean f B x = ∑ S ∈ B.powerset, component f S x := by
  simp only [sectionMean, component, avg, Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem energy_nonneg {α : Type*} [Fintype α] (f : α → ℚ) : 0 ≤ energy f := by
  unfold energy avg
  positivity

theorem component_depends (f : Cube ι κ → ℚ) (S : Finset ι) {x y : Cube ι κ}
    (h : ∀ i ∈ S, x i = y i) : component f S x = component f S y := by
  unfold component
  congr 1
  funext z
  congr 1
  exact Finset.prod_congr rfl (fun i hi => by rw [h i hi])

@[simp] theorem component_empty (f : Cube ι κ → ℚ) (x : Cube ι κ) :
    component f ∅ x = avg f := by simp [component]

omit [DecidableEq κ] in
private theorem prod_factors (g : ι → κ → ℚ) :
    avg (fun x : Cube ι κ => ∏ i, g i (x i)) = ∏ i, avg (g i) := by
  simp only [avg, Cube, ← Fintype.prod_sum, Fintype.card_fun, Nat.cast_pow,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

private theorem kernel_average (a : κ) : avg (fun b => kernel b a) = 0 := by
  simp [kernel, avg, Finset.sum_sub_distrib]

variable [Nonempty κ]

private theorem kernel_normalized (a : κ) : avg (fun b => 1 + kernel a b) = 1 := by
  have hn : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (b : κ) : 1 + kernel a b = if a = b then (Fintype.card κ : ℚ) else 0 := by
    simp [kernel]
  simp [avg, he, hn]

private theorem product_mem (S : Finset ι) (g : ι → ℚ) :
    (∏ i ∈ S, g i) = ∏ i, if i ∈ S then g i else 1 := by
  simp

theorem sectionMean_const (f : Cube ι κ → ℚ) (B : Finset ι) (x : Cube ι κ) (a : ℚ)
    (ha : ∀ y : Cube ι κ, (∀ i ∈ B, y i = x i) → f y = a) : sectionMean f B x = a := by
  let w (y : Cube ι κ) := ∏ i ∈ B, (1 + kernel (x i) (y i))
  have replace (y) : f y * w y = a * w y := by
    by_cases h : ∀ i ∈ B, y i = x i
    · rw [ha y h]
    · push Not at h
      obtain ⟨i, hi, he⟩ := h
      have zero : w y = 0 := Finset.prod_eq_zero hi (by simp [kernel, Ne.symm he])
      rw [zero, mul_zero, mul_zero]
  have mean : avg w = 1 := by
    simp only [w, product_mem B]
    rw [prod_factors (fun i (b : κ) => if i ∈ B then 1+kernel (x i) b else 1)]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ B
    · simpa [hi] using kernel_normalized (x i)
    · have hn : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [hi, avg, hn]
  change avg (fun y => f y * w y) = a
  simp only [replace, avg, ← Finset.mul_sum, mul_div_assoc]
  change a * avg w = a
  rw [mean, mul_one]

@[simp] theorem sectionMean_univ (f : Cube ι κ → ℚ) (x : Cube ι κ) :
    sectionMean f Finset.univ x = f x := by
  apply sectionMean_const
  intro y hy
  have he : y = x := funext (fun i => hy i (Finset.mem_univ i))
  rw [he]

omit [Nonempty κ] in
private theorem product_orthogonal {S T : Finset ι} (hne : S ≠ T) (y z : Cube ι κ) :
    avg (fun x : Cube ι κ =>
      (∏ i ∈ S, kernel (x i) (y i)) * ∏ i ∈ T, kernel (x i) (z i)) = 0 := by
  let g (i : ι) (b : κ) := (if i ∈ S then kernel b (y i) else 1) *
    (if i ∈ T then kernel b (z i) else 1)
  have hprod (x : Cube ι κ) :
      (∏ i ∈ S, kernel (x i) (y i)) * (∏ i ∈ T, kernel (x i) (z i)) =
        ∏ i, g i (x i) := by
    rw [product_mem S, product_mem T, ← Finset.prod_mul_distrib]
  simp only [hprod]
  rw [prod_factors g]
  have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
    by_contra! he
    exact hne (Finset.ext he)
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hs : i ∈ S
  · have ht : i ∉ T := fun h => hi (iff_of_true hs h)
    simpa only [g, ite_eq_left hs, ite_eq_right ht, mul_one] using kernel_average (y i)
  · have ht : i ∈ T := Classical.byContradiction (fun h => hi (iff_of_false hs h))
    simpa only [g, ite_eq_right hs, ite_eq_left ht, one_mul] using kernel_average (z i)

omit [Nonempty κ] in
theorem components_orthogonal (f g : Cube ι κ → ℚ) {S T : Finset ι} (hne : S ≠ T) :
    avg (fun x => component f S x * component g T x) = 0 := by
  let a (x y : Cube ι κ) := ∏ i ∈ S, kernel (x i) (y i)
  let b (x z : Cube ι κ) := ∏ i ∈ T, kernel (x i) (z i)
  change avg (fun x => avg (fun y => f y * a x y) * avg (fun z => g z * b x z)) = 0
  simp only [← avg_mul_right]
  rw [avg_comm]
  have hz (y : Cube ι κ) :
      avg (fun x => f y*a x y * avg (fun z => g z*b x z)) = 0 := by
    simp only [← avg_mul_left]
    rw [avg_comm]
    have herr (z : Cube ι κ) : avg (fun x => f y*a x y*(g z*b x z)) = 0 := by
      have he (x) : f y*a x y*(g z*b x z) = (f y*g z)*(a x y*b x z) := by ring
      simp only [he, avg_mul_left, a, b, product_orthogonal hne, mul_zero]
    simp only [herr, avg_zero]
  simp only [hz, avg_zero]

theorem avg_component_nonempty (f : Cube ι κ → ℚ) {S : Finset ι} (hs : S.Nonempty) :
    avg (component f S) = 0 := by
  simpa only [component_empty, avg_const, mul_one] using
    components_orthogonal f (fun _ => 1) hs.ne_empty

theorem avg_sectionMean (f : Cube ι κ → ℚ) (B : Finset ι) :
    avg (sectionMean f B) = avg f := by
  have he : sectionMean f B = fun x => ∑ S ∈ B.powerset, component f S x :=
    funext (sectionMean_components f B)
  rw [he, avg_sum B.powerset (component f),
    Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_powerset B)
      (fun _ _ h => avg_component_nonempty f (Finset.nonempty_iff_ne_empty.mpr h))]
  have hempty : component f ∅ = fun _ => avg f := funext (component_empty f)
  rw [hempty, avg_const]

omit [Nonempty κ] in
theorem energy_sectionMean (f : Cube ι κ → ℚ) (B : Finset ι) :
    energy (sectionMean f B) = ∑ S ∈ B.powerset, energy (component f S) := by
  simp only [energy, sectionMean_components, pow_two, Finset.sum_mul, Finset.mul_sum,
    avg_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact Finset.sum_eq_single_of_mem S hS
    (fun T _ h => components_orthogonal f f h)

theorem energy_components (f : Cube ι κ → ℚ) :
    energy f = ∑ S : Finset ι, energy (component f S) := by
  have h : sectionMean f Finset.univ = f := funext (sectionMean_univ f)
  simpa only [h, Finset.powerset_univ] using
    energy_sectionMean f Finset.univ

end

end BorgSignedSets
