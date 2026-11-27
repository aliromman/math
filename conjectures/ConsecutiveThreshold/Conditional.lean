module

public import conjectures.ConsecutiveThreshold.Transfer
public import conjectures.ConsecutiveThreshold.Mode
public import conjectures.ConsecutiveThreshold.Blocks

public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped BigOperators Classical

private theorem mahonian_mode {n m : ℕ} (hn : 2≤n.choose 2) (hm : 2*m≤n.choose 2) :
    ∃ q : ℝ, 0<q ∧ q≤1 ∧ (m:ℝ)/(m+n)≤q ∧
      ∀ z : ℤ, (full n q).coeff z ≤ (full n q).coeff (m:ℤ) := by
  apply modal_choice (full n) (fun j ↦ ((codeLayer n j).card:ℝ)) n (n.choose 2) m hn hm
  · intro i hi
    exact_mod_cast layer_positive hi
  · intro i hi
    exact_mod_cast layer_symmetric hi
  · intro i
    exact_mod_cast mahonian_ratio n i
  · intro q i
    simp [full_coefficient]
  · intro q hq
    exact geom_prod_balanced univ hq _

private theorem block_base_nonneg (k s : ℕ) {q : ℝ} (hq : 0≤q) (hq' : q≤1) :
    0 ≤ 1-q^s/(k.factorial:ℝ) := by
  apply sub_nonneg.mpr
  exact (div_le_one (by positivity)).mpr
    ((pow_le_one₀ hq hq').trans (by exact_mod_cast Nat.factorial_pos k))

theorem block_term_nonneg (k s n m : ℕ) :
    0 ≤ (1-((m:ℝ)/(m+n))^s/(k.factorial:ℝ))^(n/4/k) := by
  apply pow_nonneg
  apply block_base_nonneg k s (by positivity)
  exact div_le_one_of_le₀ (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- Uniform avoidance bound throughout the lower half of the inversion spectrum. -/
theorem avoidance_bound {k n m : ℕ} (π : Perm (Fin k)) (hk : 0<k) (hn : 2≤n.choose 2)
    (hm : 2*m≤n.choose 2) :
    1-occurrence π n m ≤
      52*(1-((m:ℝ)/(m+n))^(inversions π)/(k.factorial:ℝ))^(n/4/k) := by
  obtain ⟨q,pq,uq,low,mode⟩ := mahonian_mode hn hm
  obtain ⟨B,avoids,depends,weight⟩ := block_estimate (n:=n) π hk q pq uq
  have dep (e f : Code n) (h : ∀ i∈slice n,e i=f i) : B e ↔ B f :=
    depends e f fun i h₁ h₂ ↦ h i (mem_filter.mpr ⟨mem_univ _,h₁,h₂⟩)
  have count := conditional_event_bound pq B dep mode
  have mass : 0<∑ e : Code n,q^(∑ i,(e i).val) :=
    sum_pos' (fun _ _ ↦ (pow_pos pq _).le) ⟨encode (1 : Perm (Fin n)),mem_univ _,pow_pos pq _⟩
  have base : (1-q^(inversions π)/(k.factorial:ℝ))^(n/4/k) ≤
      (1-((m:ℝ)/(m+n))^(inversions π)/(k.factorial:ℝ))^(n/4/k) := by
    apply pow_le_pow_left₀ (block_base_nonneg k _ pq.le uq)
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) low _) (by positivity)
  have chance := ((div_le_iff₀ mass).mpr weight).trans base
  have bad : ((codeLayer n m).filter (fun e ↦ ¬contains π ((codeEquiv n).symm e))).card ≤
      ((codeLayer n m).filter B).card := by
    apply card_le_card
    intro e he
    obtain ⟨in_layer,ha⟩ := mem_filter.mp he
    have yes := avoids ((codeEquiv n).symm e) ha
    have decode : encode ((codeEquiv n).symm e)=e := (codeEquiv n).apply_symm_apply e
    exact mem_filter.mpr ⟨in_layer,by simpa only [decode] using yes⟩
  have card_pos : (0:ℝ) < (codeLayer n m).card := by exact_mod_cast layer_positive (by omega : m≤n.choose 2)
  rw [occurrence_eq_avoiding π (by omega), sub_sub_cancel]
  apply (div_le_iff₀ card_pos).mpr
  calc
    _ ≤ (((codeLayer n m).filter B).card:ℝ) := by exact_mod_cast bad
    _ ≤ _ := count
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left chance (by norm_num)) card_pos.le

end ConsecutiveThreshold
