module

public import conjectures.ErdosSuranyi708.Sieve
import Mathlib.Tactic

@[expose] public section
namespace ErdosSuranyi708

/-- The contribution of a score above one. -/
def hinge (x : ℝ) : ℝ := max (x-1) 0

/-- The change in the hinge on adding one score. -/
def increment (x a : ℝ) : ℝ := hinge (x+a) - hinge x

/-- The length of the interval crossed by the second score. -/
def crossingLength (x a b : ℝ) : ℝ := increment (x+b) a - increment x a

lemma increment_nonneg {x a : ℝ} (ha : 0 ≤ a) : 0 ≤ increment x a := by
  unfold increment hinge
  grind

lemma increment_le {x a : ℝ} (ha : 0 ≤ a) : increment x a ≤ a := by
  unfold increment hinge
  grind

lemma increment_mono {x y a : ℝ} (hxy : x ≤ y) (ha : 0 ≤ a) :
    increment x a ≤ increment y a := by
  unfold increment hinge
  grind

lemma crossingLength_nonneg {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ crossingLength x a b := sub_nonneg.mpr (increment_mono (by linarith) ha)

lemma crossingLength_le {x a b : ℝ} (ha : 0 ≤ a) : crossingLength x a b ≤ a := by
  unfold crossingLength
  linarith [increment_le (x := x+b) ha, increment_nonneg (x := x) ha]

lemma crossingLength_of_one_le {x a b : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    crossingLength x a b = 0 := by
  unfold crossingLength increment hinge
  grind

/-- Select the labels in a finite set independently with probability `s`. -/
def bernMean (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ V ∈ T.powerset, s^V.card*(1-s)^(T.card-V.card)*f (∑ v ∈ V, w v)

private lemma mean_empty (s : ℝ) (w : ℕ → ℝ) (f : ℝ → ℝ) :
    bernMean s w ∅ f = f 0 := by simp [bernMean]

private lemma mean_insert {T : Finset ℕ} {p : ℕ} (hn : p ∉ T) (s : ℝ) (w : ℕ → ℝ)
    (f : ℝ → ℝ) : bernMean s w (insert p T) f =
      (1-s)*bernMean s w T f + s*bernMean s w T (fun x => f (x+w p)) := by
  classical
  unfold bernMean
  rw [Finset.sum_powerset_insert hn, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro V hV
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hV)
    rw [Finset.card_insert_of_notMem hn, show T.card+1-V.card = T.card-V.card+1 by omega, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro V hV
    have hpn : p ∉ V := fun h => hn (Finset.mem_powerset.mp hV h)
    rw [Finset.card_insert_of_notMem hn, Finset.card_insert_of_notMem hpn, Finset.sum_insert hpn,
      show T.card+1-(V.card+1) = T.card-V.card by omega, pow_succ]
    rw [add_comm (w p)]
    ring

private lemma mean_sub (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (f g : ℝ → ℝ) :
    bernMean s w T (fun x => f x-g x) = bernMean s w T f-bernMean s w T g := by
  simp [bernMean, mul_sub, Finset.sum_sub_distrib]

private lemma mean_const (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (c : ℝ) :
    bernMean s w T (fun _ => c) = c := by
  induction T using Finset.induction_on with
  | empty => simp [mean_empty]
  | insert p T hn ih => rw [mean_insert hn, ih]; ring

private lemma mean_mono {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 1) (w : ℕ → ℝ) (T : Finset ℕ)
    {f g : ℝ → ℝ} (h : ∀ V ⊆ T, f (∑ v ∈ V, w v) ≤ g (∑ v ∈ V, w v)) :
    bernMean s w T f ≤ bernMean s w T g := by
  unfold bernMean
  exact Finset.sum_le_sum fun V hV => mul_le_mul_of_nonneg_left (h V (Finset.mem_powerset.mp hV))
    (mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hu) _))

/-- All prime labels strictly below the indicated label. -/
def earlier (T : Finset ℕ) (p : ℕ) : Finset ℕ := T.filter (· < p)

private lemma earlier_insert_max {T : Finset ℕ} {p : ℕ} (hp : ∀ r ∈ T, r < p) :
    earlier (insert p T) p = T := by ext r; simp [earlier]; grind

private lemma earlier_insert_of_le (T : Finset ℕ) {p q : ℕ} (h : q ≤ p) :
    earlier (insert p T) q = earlier T q := by ext r; simp [earlier]; grind

private lemma earlier_earlier (T : Finset ℕ) {p q : ℕ} (h : q < p) :
    earlier (earlier T p) q = earlier T q := by ext r; simp [earlier]; omega

private lemma mean_telescoping (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (f : ℝ → ℝ) :
    bernMean s w T f = f 0+s*∑ p ∈ T,
      bernMean s w (earlier T p) (fun x => f (x+w p)-f x) := by
  induction T using Finset.induction_on_max with
  | empty => simp [mean_empty]
  | insert p T hp ih =>
    have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
    rw [mean_insert hn, Finset.sum_insert hn, earlier_insert_max hp]
    have rewriteOthers : (∑ q ∈ T, bernMean s w (earlier (insert p T) q)
        (fun x => f (x+w q)-f x)) = ∑ q ∈ T, bernMean s w (earlier T q)
        (fun x => f (x+w q)-f x) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [earlier_insert_of_le T (hp q hq).le]
    rw [rewriteOthers, mean_sub]
    linear_combination ih

private lemma mean_id (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) :
    bernMean s w T id = s*∑ p ∈ T, w p := by
  rw [mean_telescoping]
  simp [mean_const]

private lemma mean_hinge_upper {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 1) (w : ℕ → ℝ)
    (T : Finset ℕ) (hw : ∀ i ∈ T, 0 ≤ w i) :
    bernMean s w T hinge ≤ s*hinge (∑ p ∈ T, w p) := by
  induction T using Finset.induction_on_max with
  | empty => simp [mean_empty, hinge]
  | insert p T hp ih =>
    have hn : p ∉ T := fun h => (Nat.lt_irrefl p) (hp p h)
    have h₁ := hw p (Finset.mem_insert_self ..)
    have ht : ∀ i ∈ T, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have diff := mean_mono hs hu w T (f := fun x => hinge (x+w p)-hinge x)
      (g := fun _ => increment (∑ i ∈ T, w i) (w p)) (fun V hV =>
      increment_mono (Finset.sum_le_sum_of_subset_of_nonneg hV (fun i hi _ => ht i hi)) h₁)
    rw [mean_sub, mean_const] at diff
    unfold increment at diff
    rw [mean_insert hn, Finset.sum_insert hn, add_comm (w p)]
    nlinarith [ih ht, mul_le_mul_of_nonneg_left diff hs]

/-- The probability factor and the positive crossing length on one seed. -/
def seedWeight (s : ℝ) (w : ℕ → ℝ) (p q : ℕ) (V : Finset ℕ) : ℝ :=
  s^(V.card+1) * crossingLength (∑ i ∈ V, w i) (w p) (w q)

/-- The modulus needed to witness a first crossing. -/
def seedDivisor (cost : ℕ → ℕ) (p q : ℕ) (V : Finset ℕ) : ℕ :=
  cost p * cost q * ∏ r ∈ V, cost r

/-- The exact contribution of a fixed ordered pair of labels. -/
def pairValue (s : ℝ) (w : ℕ → ℝ) (U : Finset ℕ) (p q : ℕ) : ℝ :=
  ∑ V ∈ U.powerset, seedWeight s w p q V * (1-s)^(U \ V).card

/-- The contribution of a seed after the lower sieve. -/
def seedValue (M : ℕ) (s : ℝ) (w : ℕ → ℝ) (cost : ℕ → ℕ)
    (U : Finset ℕ) (p q : ℕ) (V : Finset ℕ) : ℝ :=
  let d := seedDivisor cost p q V
  if d*q ≤ M then seedWeight s w p q V * lowerSieve (M/d) s (U\V) else 0

/-- The finite sum over all present first-crossing seeds. -/
def crossing (M : ℕ) (s : ℝ) (T : Finset ℕ) (cost : ℕ → ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ T, ∑ q ∈ earlier T p, ∑ V ∈ (earlier T q).powerset,
    seedValue M s w cost (earlier T q) p q V

lemma pairValue_eq (s : ℝ) (w : ℕ → ℝ) (U : Finset ℕ) (p q : ℕ) :
    pairValue s w U p q = s * bernMean s w U (fun x => crossingLength x (w p) (w q)) := by
  unfold pairValue seedWeight bernMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hV), pow_succ]
  ring

private lemma marginal_pairs (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (p : ℕ) (hw : w p ≤ 1) :
    bernMean s w (earlier T p) (fun x => increment x (w p)) =
      ∑ q ∈ earlier T p, pairValue s w (earlier T q) p q := by
  rw [mean_telescoping]
  have zero : increment 0 (w p) = 0 := by simp [increment, hinge, max_eq_right (sub_nonpos.mpr hw)]
  rw [zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [earlier_earlier T (Finset.mem_filter.mp hq).2, pairValue_eq]
  rfl

lemma hinge_pairs (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) (hw : ∀ p ∈ T, w p ≤ 1) :
    bernMean s w T hinge = s * ∑ p ∈ T, ∑ q ∈ earlier T p,
      pairValue s w (earlier T q) p q := by
  rw [mean_telescoping]
  have hz : hinge 0 = 0 := by norm_num [hinge]
  rw [hz, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun p hp => marginal_pairs s w T p (hw p hp)

lemma seedValue_le {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 1) (w : ℕ → ℝ) (cost : ℕ → ℕ)
    (M p q : ℕ) (U V : Finset ℕ) (hp : 0 ≤ w p) (hq : 0 ≤ w q) :
    seedValue M s w cost U p q V ≤ seedWeight s w p q V * (1-s)^(U\V).card := by
  have hw : 0 ≤ seedWeight s w p q V := mul_nonneg (pow_nonneg hs _) (crossingLength_nonneg hp hq)
  simp only [seedValue]
  split
  · exact mul_le_mul_of_nonneg_left (lowerSieve_le _ hu _) hw
  · exact mul_nonneg hw (pow_nonneg (sub_nonneg.mpr hu) _)

lemma crossing_pairs_le {s : ℝ} (hs : 0 < s) (hu : s ≤ 1) (T : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1) :
    (∑ p ∈ T, ∑ q ∈ earlier T p, pairValue s w (earlier T q) p q) ≤ hinge (∑ i ∈ T, w i) := by
  have raw := mean_hinge_upper hs.le hu w T (fun i h => (hw i h).1)
  rw [hinge_pairs s w T (fun i h => (hw i h).2)] at raw
  exact (mul_le_mul_iff_right₀ hs).mp raw

lemma crossing_le {s : ℝ} (hs : 0 < s) (hu : s ≤ 1) (T : Finset ℕ) (cost : ℕ → ℕ)
    (w : ℕ → ℝ) (M : ℕ) (hw : ∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1) :
    crossing M s T cost w ≤ hinge (∑ i ∈ T, w i) := by
  refine le_trans ?_ (crossing_pairs_le hs hu T w hw)
  exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
    Finset.sum_le_sum fun V _ => seedValue_le hs.le hu _ _ _ _ _ _ _ (hw p hp).1
      (hw q (Finset.mem_filter.mp hq).1).1

private lemma seed_bounds {T : Finset ℕ} {p q : ℕ} {V : Finset ℕ} {M : ℕ}
    {cost : ℕ → ℕ} (hp : p ∈ T) (hq : q ∈ earlier T p) (hV : V ⊆ earlier T q)
    (hw : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i) (hf : (∏ r ∈ T, cost r) ≤ M) :
    0 < seedDivisor cost p q V ∧
      seedDivisor cost p q V*(∏ r ∈ earlier T q\V, r) ≤ M ∧
      ∀ l ∈ T, q < l → l ≠ p → seedDivisor cost p q V*(∏ r ∈ earlier T q\V, r)*q ≤ M := by
  classical
  let U := earlier T q
  let B := insert p (insert q U)
  have hqt := (Finset.mem_filter.mp hq).1
  have hqp := (Finset.mem_filter.mp hq).2
  have hUT : U ⊆ T := Finset.filter_subset ..
  have hBT : B ⊆ T := Finset.insert_subset hp (Finset.insert_subset hqt hUT)
  have hqU : q ∉ U := fun h => (Nat.lt_irrefl q) (Finset.mem_filter.mp h).2
  have hpU : p ∉ insert q U := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · have hg := (Finset.mem_filter.mp h).2
      omega
  have hc : ∀ i ∈ T, 1 ≤ cost i := fun i h => (hw i h).1.trans (hw i h).2
  have hprod : (∏ r ∈ U\V, r) ≤ ∏ r ∈ U\V, cost r :=
    Finset.prod_le_prod fun r hr => (hw r (hUT (Finset.mem_sdiff.mp hr).1)).2
  have whole : seedDivisor cost p q V*(∏ r ∈ U\V, r) ≤ ∏ r ∈ B, cost r := by
    change _ ≤ ∏ r ∈ insert p (insert q U), cost r
    rw [Finset.prod_insert hpU, Finset.prod_insert hqU, ← Finset.prod_sdiff hV]
    calc
      _ ≤ seedDivisor cost p q V*(∏ r ∈ U\V, cost r) := Nat.mul_le_mul_left _ hprod
      _ = _ := by unfold seedDivisor; ring
  have posV : 0 < ∏ r ∈ V, cost r :=
    Finset.prod_pos fun r hr => hc r (hUT (hV hr))
  refine ⟨Nat.mul_pos (Nat.mul_pos (hc p hp) (hc q hqt)) posV, ?_, ?_⟩
  · exact whole.trans ((Finset.prod_le_prod_of_subset_of_one_le hBT (fun i hi _ => hc i hi)).trans hf)
  · intro l hl hql hpl
    have hlB : l ∉ B := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hpl h
      rcases Finset.mem_insert.mp h with h | h
      · omega
      · have hlq := (Finset.mem_filter.mp h).2
        omega
    have hlT := Finset.insert_subset hl hBT
    calc
      _ ≤ (∏ r ∈ B, cost r)*cost l := Nat.mul_le_mul whole (hql.le.trans (hw l hl).2)
      _ = ∏ r ∈ insert l B, cost r := by rw [Finset.prod_insert hlB, Nat.mul_comm]
      _ ≤ ∏ r ∈ T, cost r := Finset.prod_le_prod_of_subset_of_one_le hlT (fun i hi _ => hc i hi)
      _ ≤ M := hf

lemma seedValue_nonneg {s : ℝ} (hs : 0 < s) (hh : s < 1/2) {T : Finset ℕ} {p q M : ℕ}
    {V : Finset ℕ} {w : ℕ → ℝ} {cost : ℕ → ℕ} (hp : p ∈ T) (hq : q ∈ earlier T p)
    (hV : V ⊆ earlier T q) (hw : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i)
    (hf : (∏ r ∈ T, cost r) ≤ M) (ha : 0 ≤ w p) (hb : 0 ≤ w q) :
    0 ≤ seedValue M s w cost (earlier T q) p q V := by
  obtain ⟨hd,ht,_⟩ := seed_bounds hp hq hV hw hf
  have hpos : ∀ i ∈ earlier T q\V, 1 ≤ i :=
    fun i hi => (hw i (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1).1
  have fit := (Nat.le_div_iff_mul_le hd).mpr ((Nat.mul_comm ..) ▸ ht)
  have bound := lowerSieve_lower _ hs hh _ hpos fit
  have hu : 0 < 1-s := by linarith
  have hr : s/(1-s) ≤ 1 := (div_le_one hu).mpr (by linarith)
  have hr₀ : 0 ≤ s/(1-s) := by positivity
  have hr₂ : (s/(1-s))^2 ≤ 1 := pow_le_one₀ hr₀ hr
  have hlow := le_trans (mul_nonneg (sub_nonneg.mpr hr₂) (pow_nonneg hu.le _)) bound
  simp only [seedValue]
  split
  · exact mul_nonneg (mul_nonneg (pow_nonneg hs.le _) (crossingLength_nonneg ha hb)) hlow
  · rfl

lemma seedValue_spare {s : ℝ} {T : Finset ℕ} {p q M : ℕ} {V : Finset ℕ} {cost : ℕ → ℕ}
    (w : ℕ → ℝ) (hp : p ∈ T) (hq : q ∈ earlier T p) (hV : V ⊆ earlier T q)
    (hw : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i) (hf : (∏ r ∈ T, cost r) ≤ M)
    {l : ℕ} (hl : l ∈ T) (hql : q < l) (hlp : l ≠ p) :
    seedValue M s w cost (earlier T q) p q V =
      seedWeight s w p q V*(1-s)^(earlier T q\V).card := by
  obtain ⟨hd,_,hsp⟩ := seed_bounds hp hq hV hw hf
  have hpos : ∀ i ∈ earlier T q\V, 1 ≤ i :=
    fun i hi => (hw i (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1).1
  have hmax : ∀ i ∈ earlier T q\V, i ≤ q :=
    fun i hi => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2.le
  have hP : 1 ≤ ∏ r ∈ earlier T q\V, r := Nat.succ_le_of_lt (Finset.prod_pos (f := id) hpos)
  have htop := hsp l hl hql hlp
  have hfit : seedDivisor cost p q V*q ≤ M :=
    (Nat.mul_le_mul_right q (show seedDivisor cost p q V ≤ _ by
      simpa using Nat.mul_le_mul_left (seedDivisor cost p q V) hP)).trans htop
  have extra : (∏ r ∈ earlier T q\V, r)*q ≤ M/seedDivisor cost p q V :=
    (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htop)
  simp [seedValue,hfit,lowerSieve_exact _ s _ q hpos hmax extra]

lemma crossing_nonneg {s : ℝ} (hs : 0 < s) (hh : s < 1/2) {M : ℕ} {T : Finset ℕ}
    {w : ℕ → ℝ} {cost : ℕ → ℕ} (hc : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i)
    (hf : (∏ r ∈ T, cost r) ≤ M) (hw : ∀ i ∈ T, 0 ≤ w i) :
    0 ≤ crossing M s T cost w :=
  Finset.sum_nonneg fun p hp => Finset.sum_nonneg fun q hq => Finset.sum_nonneg fun _ hV =>
    seedValue_nonneg hs hh hp hq (Finset.mem_powerset.mp hV) hc hf (hw p hp)
      (hw q (Finset.mem_filter.mp hq).1)

private def deficit (x : ℝ) : ℝ := max (1-x) 0

private lemma deficit_identity (s : ℝ) (w : ℕ → ℝ) (T : Finset ℕ) :
    bernMean s w T deficit = bernMean s w T hinge-s*(∑ i ∈ T, w i)+1 := by
  have key : deficit = fun x : ℝ => hinge x - (x-1) := by
    funext x
    unfold deficit hinge
    grind
  rw [key, mean_sub]
  have aux : bernMean s w T (fun x : ℝ => x-1) = s*(∑ i ∈ T, w i)-1 := by
    rw [show (fun x : ℝ => x-1) = (fun x => id x - (fun _ : ℝ => (1:ℝ)) x) by rfl,
      mean_sub, mean_id, mean_const]
  rw [aux]
  ring

private lemma mean_def_nonneg {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 1) (w : ℕ → ℝ)
    (T : Finset ℕ) (a : ℝ) : 0 ≤ bernMean s w T (fun x => deficit (x+a)) := by
  rw [← mean_const s w T 0]
  exact mean_mono hs hu w T fun _ _ => le_max_right _ _

private lemma last_pair_bound {s : ℝ} (hs : 0 < s) (hh : s < 1/2) (w : ℕ → ℝ)
    (T : Finset ℕ) {p q : ℕ} (hp : p ∉ insert q T) (hq : q ∉ T) :
    s * pairValue s w T p q ≤ bernMean s w (insert p (insert q T)) deficit := by
  have ho : s ≤ 1 := by linarith
  have hu : 0 ≤ 1-s := by linarith
  let f := fun x : ℝ => deficit x + deficit (x+w q+w p)
  have hc := mean_mono hs.le ho w T (f := fun x => crossingLength x (w p) (w q)) (g := f)
    (fun V _ => by unfold f crossingLength increment hinge deficit; grind)
  have fadd : bernMean s w T f = bernMean s w T deficit +
      bernMean s w T (fun x => deficit (x+w q+w p)) := by
    simp [f,bernMean,mul_add,Finset.sum_add_distrib]
  rw [fadd] at hc
  have h₀ : 0 ≤ bernMean s w T deficit := by simpa using mean_def_nonneg hs.le ho w T 0
  have h₁ := mean_def_nonneg hs.le ho w T (w p)
  have h₂ := mean_def_nonneg hs.le ho w T (w q)
  have scaled := mul_le_mul_of_nonneg_left hc (sq_nonneg s)
  have diff : 0 ≤ (1-2*s)*bernMean s w T deficit := mul_nonneg (by linarith) h₀
  have other₁ := mul_nonneg (mul_nonneg hs.le hu) h₁
  have other₂ := mul_nonneg (mul_nonneg hs.le hu) h₂
  rw [pairValue_eq, mean_insert hp, mean_insert hq, mean_insert hq]
  nlinarith only [scaled,diff,other₁,other₂]

private lemma uncut_gap {s : ℝ} (hs : 0 < s) (hh : s < 1/2) {M : ℕ} (T : Finset ℕ)
    (w : ℕ → ℝ) (cost : ℕ → ℕ) (hc : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i)
    (hw : ∀ i ∈ T, 0 ≤ w i) (hfit : (∏ r ∈ T, cost r) ≤ M) {a b : ℕ}
    (ha : a ∈ T) (hb : b ∈ earlier T a)
    (spare : ∀ i ∈ T, ∀ j ∈ earlier T i, (i ≠ a ∨ j ≠ b) → ∃ l ∈ T, j < l ∧ l ≠ i) :
    (∑ i ∈ T, ∑ j ∈ earlier T i, pairValue s w (earlier T j) i j) ≤
      crossing M s T cost w + pairValue s w (earlier T b) a b := by
  classical
  let A i j := ∑ V ∈ (earlier T j).powerset, seedValue M s w cost (earlier T j) i j V
  let C := pairValue s w (earlier T b) a b
  have point (i) (hi : i ∈ T) (j) (hj : j ∈ earlier T i) :
      pairValue s w (earlier T j) i j ≤ A i j + if i=a then (if j=b then C else 0) else 0 := by
    by_cases h : i=a ∧ j=b
    · obtain ⟨rfl,rfl⟩ := h
      have hA : 0 ≤ A i j := Finset.sum_nonneg fun _ hV => seedValue_nonneg hs hh hi hj
        (Finset.mem_powerset.mp hV) hc hfit (hw i hi) (hw j (Finset.mem_filter.mp hj).1)
      simpa [C] using le_add_of_nonneg_left (a := pairValue s w (earlier T j) i j) hA
    · have hij : i ≠ a ∨ j ≠ b := by tauto
      obtain ⟨l,hl,hjl,hli⟩ := spare i hi j hj hij
      have eq : pairValue s w (earlier T j) i j = A i j :=
        Finset.sum_congr rfl fun _ hV => (seedValue_spare w hi hj (Finset.mem_powerset.mp hV) hc
          hfit hl hjl hli).symm
      rcases hij with h | h <;> simp [eq,h]
  have full := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => point i hi j hj
  simp_rw [Finset.sum_add_distrib] at full
  simpa [ha,hb,A,C,crossing] using full

lemma hinge_le_crossing {s : ℝ} (hs : 0 < s) (hh : s < 1/2) (T : Finset ℕ) (cost : ℕ → ℕ)
    (w : ℕ → ℝ) (M : ℕ) (hc : ∀ i ∈ T, 1 ≤ i ∧ i ≤ cost i)
    (hw : ∀ i ∈ T, 0 ≤ w i ∧ w i ≤ 1) (hfit : (∏ i ∈ T, cost i) ≤ M) :
    max ((∑ i ∈ T, w i)-1/s) 0 ≤ crossing M s T cost w := by
  have hnn := crossing_nonneg hs hh hc hfit (fun i hi => (hw i hi).1)
  apply max_le _ hnn
  induction T using Finset.induction_on_max with
  | empty => simpa [crossing] using (neg_nonpos.mpr (show 0 ≤ 1/s by positivity))
  | insert p S hp _ =>
    induction S using Finset.induction_on_max with
    | empty =>
      have hlow := (hw p (Finset.mem_insert_self ..)).2
      have hunit : (1:ℝ) ≤ 1/s := (le_div_iff₀ hs).mpr (by linarith)
      simp only [Finset.notMem_empty, not_false_eq_true, Finset.sum_insert, Finset.sum_empty, add_zero]
      linarith
    | insert q U hq _ =>
      let T := insert p (insert q U)
      have hpn : p ∉ insert q U := fun h => (Nat.lt_irrefl p) (hp p h)
      have hqn : q ∉ U := fun h => (Nat.lt_irrefl q) (hq q h)
      have hqp := hp q (Finset.mem_insert_self ..)
      have hpT : p ∈ T := Finset.mem_insert_self ..
      have hqT : q ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
      have hbelow : earlier T q = U := (earlier_insert_of_le _ hqp.le).trans (earlier_insert_max hq)
      have hgap := uncut_gap hs hh T w cost hc (fun i hi => (hw i hi).1) hfit hpT
        (show q ∈ earlier T p from Finset.mem_filter.mpr ⟨hqT,hqp⟩) (by
          intro i hi j hj hij
          obtain ⟨hjT,hji⟩ := Finset.mem_filter.mp hj
          by_cases hip : i=p
          · subst i
            refine ⟨q,hqT,?_,hqp.ne⟩
            have hjq : j ≠ q := hij.resolve_left (by simp)
            rcases Finset.mem_insert.mp hjT with rfl | hrest
            · omega
            rcases Finset.mem_insert.mp hrest with rfl | hrest
            · contradiction
            · exact hq j hrest
          · refine ⟨p,hpT,?_,Ne.symm hip⟩
            have hi' := (Finset.mem_insert.mp hi).resolve_left hip
            exact hji.trans (hp i hi'))
      rw [hbelow] at hgap
      have hlast := last_pair_bound hs hh w U hpn hqn
      have hmean := hinge_pairs s w T (fun i hi => (hw i hi).2)
      have hdef := deficit_identity s w T
      change s * pairValue s w U p q ≤ bernMean s w T deficit at hlast
      have total := mul_le_mul_of_nonneg_left hgap hs.le
      change (∑ i ∈ T, w i)-1/s ≤ crossing M s T cost w
      apply (mul_le_mul_iff_right₀ hs).mp
      field_simp [ne_of_gt hs]
      nlinarith only [total,hlast,hmean,hdef]

end ErdosSuranyi708
