module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708

/-- A positive branch stops before its next prime could exceed the level. -/
def stops (L d j p : ℕ) : Prop := Even (j+1) ∧ L < d*p*p

instance (L d j p : ℕ) : Decidable (stops L d j p) :=
  inferInstanceAs (Decidable (Even (j+1) ∧ L < d*p*p))

def prefixWeight (L : ℕ) (s : ℝ) (d j : ℕ) : List ℕ → ℝ
  | [] => (-s)^j
  | p :: ps => if stops L d j p then 0 else prefixWeight L s (d*p) (j+1) ps

private def sieveValue (L : ℕ) (s : ℝ) (d j : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ E ∈ T.powerset, prefixWeight L s d j (E.sort (· ≥ ·))

/-- The coefficient at one squarefree divisor. -/
def sieveCoeff (L : ℕ) (s : ℝ) (E : Finset ℕ) : ℝ :=
  prefixWeight L s 1 0 (E.sort (· ≥ ·))

/-- The lower exponential sieve on the labels present at a site. -/
def lowerSieve (L : ℕ) (s : ℝ) (T : Finset ℕ) : ℝ :=
  ∑ E ∈ T.powerset, sieveCoeff L s E

private lemma empty_value (L : ℕ) (s : ℝ) (d j : ℕ) :
    sieveValue L s d j ∅ = (-s)^j := by simp [sieveValue, prefixWeight]

private lemma insert_value {T : Finset ℕ} {p : ℕ} (hp : ∀ r ∈ T, r < p)
    (L : ℕ) (s : ℝ) (d j : ℕ) :
    sieveValue L s d j (insert p T) = sieveValue L s d j T +
      if stops L d j p then 0 else sieveValue L s (d*p) (j+1) T := by
  classical
  have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
  unfold sieveValue
  rw [Finset.sum_powerset_insert hn]
  congr 1
  have he (E) (hE : E ∈ T.powerset) :
      (insert p E).sort (· ≥ ·) = p :: E.sort (· ≥ ·) :=
    Finset.sort_insert _ (fun r hr => (hp r (Finset.mem_powerset.mp hE hr)).le)
      (fun h => hn (Finset.mem_powerset.mp hE h))
  by_cases hc : stops L d j p
  · rw [ite_eq_left hc]
    exact Finset.sum_eq_zero fun E hE => by rw [he E hE, prefixWeight, ite_eq_left hc]
  · rw [ite_eq_right hc]
    exact Finset.sum_congr rfl fun E hE => by rw [he E hE, prefixWeight, ite_eq_right hc]

private lemma split_power (s : ℝ) (j k : ℕ) :
    (-s)^j * (1-s)^(k+1) = (-s)^j * (1-s)^k + (-s)^(j+1) * (1-s)^k := by
  rw [pow_succ, pow_succ (-s)]
  ring

private lemma upper_value (L : ℕ) (s : ℝ) (hs : s ≤ 1) (T : Finset ℕ) (d j : ℕ) :
    sieveValue L s d j T ≤ (-s)^j * (1-s)^T.card := by
  induction T using Finset.induction_on_max generalizing d j with
  | empty => simp [empty_value]
  | insert p T hp ih =>
    have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
    rw [insert_value hp, Finset.card_insert_of_notMem hn, split_power]
    apply add_le_add (ih d j)
    split_ifs with hc
    · exact mul_nonneg (hc.1.pow_nonneg _) (pow_nonneg (sub_nonneg.mpr hs) _)
    · exact ih (d*p) (j+1)

lemma lowerSieve_le (L : ℕ) {s : ℝ} (hs : s ≤ 1) (T : Finset ℕ) :
    lowerSieve L s T ≤ (1-s)^T.card := by
  simpa [lowerSieve, sieveCoeff, sieveValue] using upper_value L s hs T 1 0

private lemma exact_value (L : ℕ) (s : ℝ) (T : Finset ℕ) (b d j : ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ r) (hmax : ∀ r ∈ T, r ≤ b)
    (hfit : d*(∏ r ∈ T, r)*b ≤ L) :
    sieveValue L s d j T = (-s)^j * (1-s)^T.card := by
  induction T using Finset.induction_on_max generalizing d j with
  | empty => simp [empty_value]
  | insert p T hp ih =>
    have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
    have hpt : 1 ≤ p := hpos _ (Finset.mem_insert_self ..)
    have hpb : p ≤ b := hmax _ (Finset.mem_insert_self ..)
    have h₁ : ∀ r ∈ T, 1 ≤ r := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
    have h₂ : ∀ r ∈ T, r ≤ b := fun r hr => hmax r (Finset.mem_insert_of_mem hr)
    have hP : 1 ≤ ∏ r ∈ T, r := Nat.succ_le_of_lt (Finset.prod_pos (f := id) fun r hr => h₁ r hr)
    rw [Finset.prod_insert hn] at hfit
    have htake : d*p*(∏ r ∈ T, r)*b ≤ L := by simpa [Nat.mul_assoc] using hfit
    have hskip : d*(∏ r ∈ T, r)*b ≤ L := by
      calc
        _ ≤ d*(p*(∏ r ∈ T, r))*b := by gcongr; simpa using Nat.mul_le_mul_right (∏ r ∈ T, r) hpt
        _ ≤ _ := hfit
    have hcut : ¬ stops L d j p := by
      intro hc
      have hle : d*p*p ≤ d*p*(∏ r ∈ T, r)*b := by
        calc
          _ ≤ d*p*b := by gcongr
          _ ≤ _ := Nat.mul_le_mul_right _ (by simpa using Nat.mul_le_mul_left (d*p) hP)
      exact (Nat.not_lt_of_ge (hle.trans htake)) hc.2
    rw [insert_value hp, ite_eq_right hcut, Finset.card_insert_of_notMem hn, split_power,
      ih _ _ h₁ h₂ hskip, ih _ _ h₁ h₂ htake]

lemma lowerSieve_exact (L : ℕ) (s : ℝ) (T : Finset ℕ) (b : ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ r) (hmax : ∀ r ∈ T, r ≤ b)
    (hfit : (∏ r ∈ T, r)*b ≤ L) : lowerSieve L s T = (1-s)^T.card := by
  simpa [lowerSieve, sieveCoeff, sieveValue] using
    exact_value L s T b 1 0 hpos hmax (by simpa using hfit)

private lemma error_value (L : ℕ) (s : ℝ) (T : Finset ℕ) (d j : ℕ)
    (hpos : ∀ r ∈ T, 1 ≤ r) (hfit : d*(∏ r ∈ T, r) ≤ L) :
    (-s)^j*(1-s)^T.card - sieveValue L s d j T = 0 ∨
    ∃ k, 1 ≤ k ∧ k ≤ T.card ∧ Even (j+k) ∧
      (-s)^j*(1-s)^T.card - sieveValue L s d j T = (-s)^(j+k)*(1-s)^(T.card-k) := by
  induction T using Finset.induction_on_max generalizing d j with
  | empty => simp [empty_value]
  | insert p T hp ih =>
    have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
    have h₁ : ∀ r ∈ T, 1 ≤ r := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hn] at hfit
    have htake : d*p*(∏ r ∈ T, r) ≤ L := by simpa [Nat.mul_assoc] using hfit
    have skip := exact_value L s T p d j h₁ (fun r hr => (hp r hr).le)
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfit)
    rw [insert_value hp, skip, Finset.card_insert_of_notMem hn, split_power]
    by_cases hc : stops L d j p
    · right
      refine ⟨1, by omega, by omega, hc.1, ?_⟩
      simp [hc]
    · rw [ite_eq_right hc]
      rcases ih _ _ h₁ htake with he | ⟨k,hk,ht,hpar,he⟩
      · left
        linarith only [he]
      · right
        refine ⟨k+1,by omega,by omega,?_,?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpar
        · have index : j+(k+1) = j+1+k := by omega
          have remn : T.card+1-(k+1) = T.card-k := by omega
          rw [index, remn]
          linarith only [he]

lemma lowerSieve_lower (L : ℕ) {s : ℝ} (hs : 0 < s) (hhalf : s < 1/2)
    (T : Finset ℕ) (hpos : ∀ r ∈ T, 1 ≤ r) (hfit : (∏ r ∈ T, r) ≤ L) :
    (1-(s/(1-s))^2)*(1-s)^T.card ≤ lowerSieve L s T := by
  have hu : 0 < 1-s := by linarith
  have hr : 0 ≤ s/(1-s) := by positivity
  have hle : s/(1-s) ≤ 1 := (div_le_one hu).mpr (by linarith)
  change _ ≤ sieveValue L s 1 0 T
  rcases error_value L s T 1 0 hpos (by simpa using hfit) with h | ⟨k, hposk, hik, heven, h⟩
  · simp only [pow_zero, one_mul] at h
    nlinarith [mul_nonneg (sq_nonneg (s/(1-s))) (pow_nonneg hu.le T.card)]
  · simp only [Nat.zero_add] at heven
    simp only [pow_zero, one_mul, Nat.zero_add, heven.neg_pow] at h
    have hk : 2 ≤ k := by obtain ⟨i,hi⟩ := heven; omega
    have bound := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr hle hk) (pow_nonneg hu.le T.card)
    have ident : (s/(1-s))^k*(1-s)^T.card = s^k*(1-s)^(T.card-k) := by
      conv_lhs => rw [← Nat.add_sub_of_le hik, pow_add, div_pow]
      field_simp
    rw [ident] at bound
    linarith only [h,bound]

private lemma prefix_weight_values (L d j : ℕ) (s : ℝ) (xs : List ℕ) :
    prefixWeight L s d j xs = 0 ∨ prefixWeight L s d j xs = (-s)^(j+xs.length) := by
  induction xs generalizing d j with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    rw [prefixWeight]
    split_ifs with h
    · exact Or.inl rfl
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (d*p) (j+1)

lemma sieveCoeff_values (L : ℕ) (s : ℝ) (E : Finset ℕ) :
    sieveCoeff L s E = 0 ∨ sieveCoeff L s E = (-s)^E.card := by
  simpa [sieveCoeff] using prefix_weight_values L 1 0 s (E.sort (· ≥ ·))

private lemma prefix_fits {L : ℕ} {s : ℝ} (ps : List ℕ) (d j : ℕ)
    (ordered : ps.Pairwise (· ≥ ·)) (positive : ∀ p ∈ ps, 1 ≤ p) (hd : d ≤ L)
    (evenFit : Even j → ∀ p ∈ ps, d*p ≤ L) (h : prefixWeight L s d j ps ≠ 0) :
    d*ps.prod ≤ L := by
  induction ps generalizing d j with
  | nil => simpa using hd
  | cons p ps ih =>
    obtain ⟨hmax,ord⟩ := List.pairwise_cons.mp ordered
    have hp := positive p List.mem_cons_self
    have hrest : ∀ q ∈ ps, 1 ≤ q := fun q hq => positive q (List.mem_cons_of_mem _ hq)
    have hn : ¬stops L d j p := by intro hc; exact h (by simp [prefixWeight, hc])
    have high (he : Even (j+1)) : d*p*p ≤ L := Nat.le_of_not_gt fun hg => hn ⟨he,hg⟩
    have next : d*p ≤ L := by
      by_cases he : Even j
      · exact evenFit he p List.mem_cons_self
      · exact le_trans (show d*p ≤ d*p*p by simpa using Nat.mul_le_mul_left (d*p) hp) (high (Nat.even_add_one.mpr he))
    have fit (he : Even (j+1)) : ∀ q ∈ ps, d*p*q ≤ L :=
      fun q hq => (Nat.mul_le_mul_left _ (hmax q hq)).trans (high he)
    have result := ih (d*p) (j+1) ord hrest next fit (by simpa [prefixWeight, hn] using h)
    simpa [Nat.mul_assoc] using result

lemma sieveCoeff_supported {L : ℕ} {s : ℝ} {E : Finset ℕ} (hL : 1 ≤ L)
    (hp : ∀ p ∈ E, 1 ≤ p ∧ p ≤ L) (h : sieveCoeff L s E ≠ 0) : (∏ p ∈ E, p) ≤ L := by
  have r := prefix_fits (E.sort (· ≥ ·)) 1 0 (E.pairwise_sort (· ≥ ·))
    (fun p h => (hp p (by simpa using h)).1) hL
    (fun _ p h => by simpa using (hp p (by simpa using h)).2) h
  have hprod : (∏ p ∈ E, p) = (E.sort (· ≥ ·)).prod := by
    simpa using List.prod_toFinset id (E.sort_nodup (· ≥ ·))
  rw [hprod]
  simpa using r

end ErdosSuranyi708
