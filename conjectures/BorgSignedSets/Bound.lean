module

public import conjectures.BorgSignedSets.Statement
public import conjectures.BorgSignedSets.Product
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

/-- The mean and section bounds of a selector of global shift orbits. -/
structure SelectorFacts (F : Finset (Finset ι)) (A : Family ι k) (h : Cube ι (ZMod k) → ℚ) :
    Prop where
  mean_zero : avg h = 0
  total_energy : energy h = (k : ℚ) - 1
  values : ∀ x, h x = (k : ℚ) - 1 ∨ h x = -1
  forced : ∀ B ∈ F, ∀ b ∈ A B, ∀ x : Cube ι (ZMod k), (∀ i : B, x i = b i) →
    h x = (k : ℚ) - 1
  bound : ∀ B ∈ F, ((A B).card : ℚ) * ((k : ℚ) - 1) ≤
    (k ^ (B.card-1) : ℕ) * energy (sectionMean h B)

def commonDegree (F : Finset (Finset ι)) (k : ℕ) (S : Finset ι) : ℕ :=
  ∑ B ∈ F, if S ⊆ B then k ^ (B.card - 1) else 0

omit [Fintype ι] in
theorem commonDegree_le (F : Finset (Finset ι)) (k : ℕ) {S : Finset ι} {i : ι} (hi : i ∈ S) :
    commonDegree F k S ≤ degree F k i := by
  unfold commonDegree degree
  apply Finset.sum_le_sum
  intro B _
  by_cases h : S ⊆ B
  · simp [h, h hi]
  · simp [h]

omit [Fintype ι] in
theorem commonDegree_incidence (F : Finset (Finset ι)) {S : Finset ι} {i : ι} (hi : i ∈ S)
    (heq : commonDegree F k S = degree F k i) {B : Finset ι} (hB : B ∈ F) (hBi : i ∈ B) :
    S ⊆ B := by
  by_contra hn
  have lt : commonDegree F k S < degree F k i := by
    apply Finset.sum_lt_sum
    · intro C _
      by_cases hc : S ⊆ C
      · simp [hc, hc hi]
      · simp [hc]
    · exact ⟨B, hB, by simp [hn, hBi, pow_pos (NeZero.pos k)]⟩
  exact (Nat.ne_of_lt lt) heq

private theorem distribute (F : Finset (Finset ι)) (k : ℕ) (e : Finset ι → ℚ) :
    ∑ B ∈ F, (k ^ (B.card-1) : ℕ) * (∑ S ∈ B.powerset, e S) =
    ∑ S, e S * (commonDegree F k S : ℚ) := by
  simp only [commonDegree, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  have he : Finset.univ.filter (fun S : Finset ι => S ⊆ B) = B.powerset := by ext; simp
  rw [he]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm ..)

private theorem weighted_bound (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) :
    (size F A : ℚ) * ((k : ℚ)-1) ≤
      ∑ S, energy (component h S) * (commonDegree F k S : ℚ) := by
  rw [← distribute, size, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun B hB => (cert.bound B hB).trans_eq (by rw [energy_sectionMean]))

private theorem empty_energy (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) :
    energy (component h ∅) = 0 := by simp [energy, cert.mean_zero]

private theorem term_bound (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) (j : ι)
    (hmax : ∀ i, degree F k i ≤ degree F k j) (S : Finset ι) :
    energy (component h S) * (commonDegree F k S : ℚ) ≤
    energy (component h S) * (degree F k j : ℚ) := by
  obtain hs | ⟨i, hi⟩ := S.eq_empty_or_nonempty
  · simp [hs, empty_energy F A h cert]
  · apply mul_le_mul_of_nonneg_left _ (energy_nonneg _)
    exact_mod_cast (commonDegree_le F k hi).trans (hmax i)

theorem size_le_largest_star (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) (hk : 2 ≤ k) (j : ι)
    (hmax : ∀ i, degree F k i ≤ degree F k j) : size F A ≤ degree F k j := by
  have htotal := (weighted_bound F A h cert).trans (Finset.sum_le_sum fun S _ =>
    term_bound F A h cert j hmax S)
  rw [← Finset.sum_mul, ← energy_components, cert.total_energy, mul_comm ((k : ℚ)-1)] at htotal
  exact_mod_cast (le_of_mul_le_mul_right htotal (by exact_mod_cast (show 0 < (k:ℤ)-1 by omega)))

theorem positive_component_degree (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) (j : ι)
    (hmax : ∀ i, degree F k i ≤ degree F k j) (hext : degree F k j ≤ size F A)
    (hk : 2 ≤ k) {S : Finset ι} (hs : 0 < energy (component h S)) :
    commonDegree F k S = degree F k j := by
  have sne : S.Nonempty := by
    by_contra! he
    simp [he, empty_energy F A h cert] at hs
  obtain ⟨i, hi⟩ := sne
  have hle := (commonDegree_le F k hi).trans (hmax i)
  apply hle.antisymm
  by_contra! hlt
  have hsum : (∑ T, energy (component h T) * (commonDegree F k T : ℚ)) <
      ∑ T, energy (component h T) * (degree F k j : ℚ) :=
    Finset.sum_lt_sum (fun T _ => term_bound F A h cert j hmax T)
      ⟨S, Finset.mem_univ _, mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hs⟩
  rw [← Finset.sum_mul, ← energy_components, cert.total_energy, mul_comm ((k : ℚ)-1)] at hsum
  have hbad := (weighted_bound F A h cert).trans_lt hsum
  have hle' : (degree F k j : ℚ) ≤ size F A := by exact_mod_cast hext
  have pos : 0 < (k:ℚ)-1 := by exact_mod_cast (show 0 < (k:ℤ)-1 by omega)
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hle' pos.le)) hbad

end BorgSignedSets
