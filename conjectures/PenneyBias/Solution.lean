module

public import conjectures.PenneyBias.Witness
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

public section
namespace PenneyBias
open Filter Finset Set
open scoped Topology

private noncomputable def score (p : ℝ) :=
  let u := p*(1-p)
  2*(p^2+p*u+u^2)+u-1

private theorem favored_iff {p : ℝ} (hp : p∈Set.Ioo 0 1) :
    1/2 < win longer shorter p ↔ 0<score p := by
  rw [witness_probability hp, lt_div_iff₀ (show 0<1-p*(1-p) by nlinarith [sq_nonneg (p-1/2)])]
  unfold score
  constructor <;> intro h <;> linarith

private theorem score_increases {a b : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1/2) :
    score a < score b := by
  have za : 0≤a*(1-a) := mul_nonneg ha (by linarith)
  have zb : a*(1-a)<b*(1-b) := by
    nlinarith only [mul_pos (sub_pos.mpr hab) (show 0<1-a-b by linarith)]
  have p := mul_le_mul hab.le zb.le za (ha.trans hab.le)
  have s := (sq_le_sq₀ ha (ha.trans hab.le)).mpr hab.le
  have u := (sq_le_sq₀ za (za.trans zb.le)).mpr zb.le
  unfold score
  linarith only [p,s,u,zb]

private theorem threshold : ∃ r : ℝ, r∈Set.Ioo 0 (1/2) ∧ score r=0 := by
  have cont : Continuous score := by unfold score; fun_prop
  have root := intermediate_value_Icc (by norm_num : (0:ℝ)≤1/2) cont.continuousOn
    (show (0:ℝ)∈Set.Icc (score 0) (score (1/2)) by norm_num [score])
  obtain ⟨r,⟨lo,hi⟩,h⟩ := root
  refine ⟨r,⟨lt_of_le_of_ne lo ?_,lt_of_le_of_ne hi ?_⟩,h⟩
  · rintro rfl; norm_num [score] at h
  · rintro rfl; norm_num [score] at h

/-- The same bias gives an upward change for every length cap from four onward. -/
theorem common_increase : ∃ r : ℝ, r∈Set.Ioo 0 (1/2) ∧ ∀ n : ℕ, 4≤n →
    ∀ᶠ q in 𝓝[>] r, q∈Set.Ioo 0 (1/2) ∧ (favored n r).card < (favored n q).card := by
  classical
  obtain ⟨r,hr,root⟩ := threshold
  refine ⟨r,hr,?_⟩
  intro n hn
  have persist : ∀ᶠ q in 𝓝 r, favored n r ⊆ favored n q := by
    apply (favored n r).eventually_all.mpr
    intro z hz
    have mem := mem_filter.mp hz
    filter_upwards [favorable_near z.1 z.2 ⟨hr.1,by linarith [hr.2]⟩ mem.2.2] with q hq
    exact mem_filter.mpr ⟨mem.1,mem.2.1,hq⟩
  filter_upwards [persist.filter_mono nhdsWithin_le_nhds, Ioo_mem_nhdsGT hr.2] with q sub hq
  have good : q∈Set.Ioo 0 (1/2) := ⟨hr.1.trans hq.1,hq.2⟩
  refine ⟨good,card_lt_card ((Finset.ssubset_iff_of_subset sub).mpr ?_)⟩
  refine ⟨(longer,shorter),?_,?_⟩
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_words.mpr hn,mem_words.mpr (show 3≤n by omega)⟩,by decide,?_⟩
    apply (favored_iff ⟨good.1,by linarith [good.2]⟩).mpr
    exact root ▸ score_increases hr.1.le hq.1 good.2.le
  · intro h
    have strict := (favored_iff ⟨hr.1,by linarith [hr.2]⟩).mp (mem_filter.mp h).2.2
    linarith

theorem not_conjecture : ¬Conjecture := by
  intro claimed
  obtain ⟨r,hr,increase⟩ := common_increase
  obtain ⟨n,h₁,h₂⟩ := (claimed.and (eventually_ge_atTop 4)).exists
  obtain ⟨q,⟨hq,more⟩,gt⟩ := ((increase n h₂).and self_mem_nhdsWithin).exists
  exact more.not_ge (h₁ hr hq (le_of_lt gt))

/-- info: 'PenneyBias.not_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_conjecture

end PenneyBias
