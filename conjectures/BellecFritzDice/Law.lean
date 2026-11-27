module

public import conjectures.BellecFritzDice.Digits
public import conjectures.BellecFritzDice.Bounds
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section

namespace BellecFritzDice
open Set MeasureTheory MeasureTheory.Measure Finset Filter unitInterval ProbabilityTheory
open scoped ENNReal Topology
noncomputable section

abbrev coin (p : I) := bernoulliMeasure true false p
abbrev streams (p : I) := infinitePi (fun _ : ℕ => coin p)
abbrev columns (p : I) (n : ℕ) := infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin (n+3) => coin p))
def die (p : I) (m : ℕ) := (streams p).map (code m)

instance (p : I) (m : ℕ) : IsProbabilityMeasure (die p m) :=
  inferInstanceAs (IsProbabilityMeasure ((streams p).map (code m)))

/-- The rows of an array of independent columns are independent streams. -/
theorem transpose (p : I) (n : ℕ) :
    (columns p n).map (fun s i j => s j i) = Measure.pi (fun _ : Fin (n+3) => streams p) := by
  let m := n+3
  let f := (MeasurableEquiv.curry ℕ (Fin m) Bool).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : Fin m × ℕ => Bool) (Equiv.prodComm ℕ (Fin m))
  let h := MeasurableEquiv.curry (Fin m) ℕ Bool
  have A : (columns p n).map f = infinitePi (fun _ : ℕ × Fin m => coin p) := by
    simpa only [f,Measure.infinitePi_eq_pi (fun _ : Fin m => coin p)] using
      Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (_ : Fin m) => coin p)
  have B := Measure.infinitePi_map_piCongrLeft (fun _ : Fin m × ℕ => coin p) (Equiv.prodComm ℕ (Fin m))
  have C := Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : ℕ) => coin p)
  have e : (fun (s : ℕ → Column n) i j => s j i) = h ∘ g ∘ f := by rfl
  rw [e,←map_map h.measurable (g.measurable.comp f.measurable),←map_map g.measurable f.measurable,A,B,C]
  exact Measure.infinitePi_eq_pi _

theorem law_of_columns (p : I) (n : ℕ) :
    (columns p n).map (fun s i => code (n+3) (fun j => s j i)) = rolls (die p (n+3)) (n+3) := by
  have measurable_rows : Measurable (fun (s : ℕ → Column n) i j => s j i) := by fun_prop
  unfold rolls die
  rw [← Measure.pi_map_pi (fun _ : Fin (n+3) => (measurable_code (n+3)).aemeasurable),
      ←transpose p n,Measure.map_map (by fun_prop) measurable_rows]
  rfl

end
end BellecFritzDice

namespace BellecFritzDice
open Set MeasureTheory MeasureTheory.Measure Finset Filter unitInterval ProbabilityTheory
open scoped ENNReal Topology
noncomputable section

theorem coin_one (p : I) : (coin p).real {true}=(p:ℝ) := by simp [coin]
theorem coin_zero (p : I) : (coin p).real {false}=1-(p:ℝ) := by simp [coin]

theorem stream_diffuse (p : I) (h₁ : 0<(p:ℝ)) (h₂ : (p:ℝ)<1) : NullSingletonClass (streams p) := by
  constructor
  intro x
  let c := max (p:ℝ) (1-p)
  have cs : c<1 := max_lt h₂ (by linarith)
  have cm : 0≤c := le_trans h₁.le (le_max_left _ _)
  have bound (n : ℕ) : (streams p).real {x} ≤ c^n := by
    let S := Set.pi (range n : Finset ℕ) (fun j => {x j})
    have sub : {x} ⊆ S := by
      rintro y rfl
      exact fun _ _ => rfl
    apply (measureReal_mono sub).trans
    dsimp only [S,Measure.real]
    rw [infinitePi_pi _ (fun _ _ => measurableSet_singleton _),ENNReal.toReal_prod]
    calc
      _ ≤ ∏ _j ∈ range n,c := by
        apply Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg)
        intro j _
        change (coin p).real {x j} ≤ c
        cases x j
        · rw [coin_zero];exact le_max_right _ _
        · rw [coin_one];exact le_max_left _ _
      _ = c^n := by simp
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  apply le_antisymm _ measureReal_nonneg
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_pow_atTop_nhds_zero_of_lt_one cm cs) bound

theorem die_diffuse (p : I) (h₁ : 0<(p:ℝ)) (h₂ : (p:ℝ)<1) {m : ℕ} (hm : 0<m) :
    NullSingletonClass (die p m) := by
  let := stream_diffuse p h₁ h₂
  constructor
  intro y
  rw [die,map_apply (measurable_code _) (measurableSet_singleton y)]
  exact ((Set.subsingleton_singleton.preimage (code_injective m hm))).measure_zero _

theorem die_nonnegative (p : I) (m : ℕ) : die p m (Iio 0)=0 := by
  rw [die,map_apply (measurable_code _) measurableSet_Iio]
  have h : code m ⁻¹' Iio 0=∅ := by ext x; simp [not_lt.mpr (code_nonneg m x)]
  simp [h]

theorem die_bounded (p : I) (m : ℕ) : die p m (Ioi 2)=0 := by
  rw [die,map_apply (measurable_code _) measurableSet_Ioi]
  have h : code m ⁻¹' Ioi 2=∅ := by ext x; simp [not_lt.mpr (code_le_two m x)]
  simp [h]

end
end BellecFritzDice

namespace BellecFritzDice
open MeasureTheory MeasureTheory.Measure Finset Filter unitInterval
open scoped ENNReal Topology
noncomputable section

abbrev colLaw (p : I) (n : ℕ) := Measure.pi (fun _ : Fin (n+3) => coin p)
def sameChance (p : I) (n : ℕ) : ℝ := (1-p:ℝ)^(n+3)+(p:ℝ)^(n+3)
def splitChance (p : I) (n : ℕ) : ℝ := (1-p:ℝ)-(1-p:ℝ)^(n+3)

private theorem one_column (p : I) (n : ℕ) (b : Bool) :
    (colLaw p n).real {fun _ => b}=((coin p).real {b})^(n+3) := by
  simp [Measure.real,Measure.pi_singleton]

theorem same_probability (p : I) (n : ℕ) :
    (colLaw p n).real {z | uniform z}=sameChance p n := by
  let a : Column n := fun _ => false
  let b : Column n := fun _ => true
  have eq : {z | uniform z} = ({a} : Set (Column n)) ∪ {b} := by
    ext z
    constructor
    · intro h
      cases e : z 0
      · exact Or.inl (funext (fun i => (h i).trans e))
      · exact Or.inr (funext (fun i => (h i).trans e))
    · rintro (rfl|rfl) <;> exact fun _ => rfl
  have ne : a≠b := fun e => Bool.false_ne_true (congrFun e 0)
  rw [eq,measureReal_union (by simpa using ne) (measurableSet_singleton _)]
  dsimp only [a,b,sameChance]
  rw [one_column,one_column,coin_zero,coin_one]

theorem split_probability (p : I) (n : ℕ) :
    (colLaw p n).real winColumn=splitChance p n := by
  let a : Column n := fun _ => false
  let Z : Set (Column n) := {z | z 0=false}
  have sub : {a} ⊆ Z := by rintro z rfl; rfl
  have eq : winColumn = Z \ {a} := by
    ext z
    change (z 0=false ∧ ¬uniform z) ↔ z 0=false ∧ z≠a
    constructor
    · rintro ⟨h,u⟩
      exact ⟨h,fun e => u (e ▸ fun _ => rfl)⟩
    · rintro ⟨h,e⟩
      exact ⟨h,fun u => e (funext (fun i => (u i).trans h))⟩
  have hz : (colLaw p n).real Z=1-p := by
    have := (measurePreserving_eval (fun _ : Fin (n+3) => coin p) 0).measure_preimage
      (measurableSet_singleton false).nullMeasurableSet
    exact (congrArg ENNReal.toReal this).trans (coin_zero p)
  rw [eq,measureReal_sdiff sub (measurableSet_singleton _),hz]
  dsimp only [a,splitChance]
  rw [one_column,coin_zero]

private def site (n d j : ℕ) : Set (Column n) := if j=d then winColumn else {z | uniform z}

private theorem first_rect (n d : ℕ) :
    firstWin (n:=n) d = Set.pi (range (d+1) : Finset ℕ) (site n d) := by
  ext s
  constructor
  · rintro ⟨pre,win⟩ j hj
    have hj' : j<d+1 := mem_range.mp hj
    by_cases e : j=d
    · simpa [site,e] using win
    · simpa [site,e] using pre j (by omega)
  · intro h
    constructor
    · intro j hj
      simpa [site,Nat.ne_of_lt hj] using h j (mem_range.mpr (show j<d+1 by omega))
    · simpa [site] using h d (mem_range.mpr (Nat.lt_succ_self d))

private theorem first_prob (p : I) (n d : ℕ) :
    (columns p n).real (firstWin d) = sameChance p n ^ d * splitChance p n := by
  rw [first_rect,Measure.real,infinitePi_pi _ (fun _ _ => .of_discrete),ENNReal.toReal_prod,prod_range_succ]
  change (∏ i∈range d,(colLaw p n).real (site n d i)) * (colLaw p n).real (site n d d)=_
  simp only [site,ite_true,split_probability]
  congr 1
  calc
    _ = ∏ _i∈range d,sameChance p n := prod_congr rfl (fun i hi => by
      rw [ite_eq_right (Nat.ne_of_lt (mem_range.mp hi)),same_probability])
    _ = _ := by simp

theorem same_lt_one (p : I) (h₀ : 0<(p:ℝ)) (h₁ : (p:ℝ)<1) (n : ℕ) :
    sameChance p n < 1 := by
  have a : (p:ℝ)^(n+3) < p := by
    simpa using pow_lt_pow_right_of_lt_one₀ h₀ h₁ (show 1<n+3 by omega)
  have b : (1-p:ℝ)^(n+3)<1-p := by
    simpa using pow_lt_pow_right_of_lt_one₀ (by linarith : 0<1-(p:ℝ)) (by linarith : 1-(p:ℝ)<1) (show 1<n+3 by omega)
  unfold sameChance
  linarith

/-- The first column at which the rolls differ determines which rolls lie below the mean. -/
theorem chance_die (p : I) (h₀ : 0<(p:ℝ)) (h₁ : (p:ℝ)<1) (n : ℕ) :
    chance (die p (n+3)) n = splitChance p n / (1-sameChance p n) := by
  have me (d : ℕ) : MeasurableSet (firstWin (n:=n) d) := by
    rw [first_rect]
    exact .pi (Finset.countable_toSet _) (fun _ _ => .of_discrete)
  have A : 0≤sameChance p n := by rw [←same_probability p n];exact measureReal_nonneg
  rw [chance,←law_of_columns,map_measureReal_apply (by fun_prop) (open_below _).measurableSet]
  change (columns p n).real {s | wins s} = _
  rw [wins_set,Measure.real,measure_iUnion (firstWin_disjoint n) me,ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  change (∑' d, (columns p n).real (firstWin d))=_
  simp_rw [first_prob]
  rw [tsum_mul_right,tsum_geometric_of_lt_one A (same_lt_one p h₀ h₁ n),div_eq_inv_mul]

end
end BellecFritzDice
