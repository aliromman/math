module

public import conjectures.MissingSumFringes.First.Statement
public import conjectures.MissingSumFringes.CoreTransfer
public import conjectures.MissingSumFringes.CorePositive
import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

theorem firstPresent_spec {A : Finset ℕ} (h : A.Nonempty) :
    firstPresent A∈A+A ∧ ∀ x∈A+A,firstPresent A≤x := by
  rw [firstPresent,dite_eq_left h]
  constructor
  · exact Finset.mem_add.mpr ⟨_,A.min'_mem h,_,A.min'_mem h,by omega⟩
  · intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    have aa := A.min'_le a ha
    have bb := A.min'_le b hb
    omega

theorem coreAvg_const (n k : ℕ) (x : ℝ) :
    coreAvg n k (fun _ => x)=x*coreAvg n k (fun _ => 1) := by
  unfold coreAvg
  simp
  ring

theorem firstPresent_shift (u : ℕ) {B : Finset ℕ} (hb : 0∈B) : firstPresent (shift u B)=2*u := by
  have ub : u∈shift u B := mem_image.mpr ⟨0,hb,Nat.add_zero _⟩
  obtain ⟨mem,least⟩ := firstPresent_spec (show (shift u B).Nonempty from ⟨u,ub⟩)
  have low := least (2*u) (Finset.mem_add.mpr ⟨u,ub,u,ub,by omega⟩)
  rw [shift_sums] at mem
  obtain ⟨x,_,e⟩ := mem_image.mp mem
  change 2*u+x=firstPresent (shift u B) at e
  omega

theorem wordAvg_first {n k : ℕ} (large : k+1<n) : wordAvg n k (fun A => (firstPresent A:ℝ)) =
    ∑ a∈range (k/2+1),marginWeight a*((a:ℝ)*coreAvg (n-a) (k-2*a) (fun _ => 1)) := by
  rw [wordAvg_split large]
  apply sum_congr rfl
  intro a _
  rw [←add_zero ((a:ℝ)*_),←margin_row]
  apply sum_congr rfl
  intro u _
  rw [add_zero,←coreAvg_const]
  congr 1
  apply coreAvg_congr
  intro B hB
  exact_mod_cast firstPresent_shift u (mem_filter.mp hB).2.1

theorem word_first_limit {D : ℕ → ℝ}
    (d : ∀ j, Tendsto (fun N => coreAvg N j (fun _ => 1)) atTop (𝓝 (D j))) (k : ℕ) :
    Tendsto (fun n => wordAvg n k (fun A => (firstPresent A:ℝ))) atTop
      (𝓝 (marginMoment D (fun _ => 0) k)) := by
  have add := tendsto_finsetSum (range (k/2+1)) (fun a _ =>
    (((d (k-2*a)).comp (tendsto_sub_atTop_nat a)).const_mul (a:ℝ)).const_mul (marginWeight a))
  simp only [marginMoment,add_zero]
  apply add.congr'
  filter_upwards [eventually_gt_atTop (k+1)] with n hn
  exact (wordAvg_first hn).symm

theorem first_mean_from_core {D : ℕ → ℝ} (nd : ∀ j,0≤D j) (p0 : 0<D 0) (p1 : 0<D 1)
    (d : ∀ j, Tendsto (fun N => coreAvg N j (fun _ => 1)) atTop (𝓝 (D j))) (k : ℕ) :
    Tendsto (fun n => conditionalMean n k (fun _ A => firstPresent A)) atTop
      (𝓝 (marginMoment D (fun _ => 0) k/marginMass D k)) := by
  have h := (word_first_limit d k).div (word_mass_limit d k) (marginMass_pos _ nd p0 p1 k).ne'
  exact h.congr' (Eventually.of_forall fun n => (conditionalMean_eq n k _).symm)

/-- The limiting first sum differs from half the hole count by a bounded amount. -/
theorem first_location : ∃ e : ℕ → ℝ,
    (∀ k, Tendsto (fun n ↦ conditionalMean n k (fun _ A ↦ firstPresent A)) atTop (𝓝 (e k))) ∧
    (∃ C : ℝ, ∀ k : ℕ, |e k-(k:ℝ)/2|≤C) ∧
    Tendsto (fun k : ℕ ↦ e k/k) atTop (𝓝 (1/2:ℝ)) := by
  let D := coreD (atom true)
  have nd := coreD_nonneg (atom_nonneg true)
  obtain ⟨p0,p1⟩ := coreD_base_positive
  have summ := (core_summable (atom_nonneg true) atom_le_normWindow
    (fun m t h ↦ @atom_zero_of_lt m t true h)).1
  have z : Summable (fun j : ℕ ↦ tilt j*(0:ℝ)) := by simp
  exact ⟨fun k ↦ marginMoment D (fun _ ↦ 0) k / marginMass D k,
    first_mean_from_core nd p0 p1 coreD_limit,
    margin_limit nd (fun _ ↦ le_rfl) p0 p1 summ z⟩

theorem first_resolution : FirstConjecture := by
  obtain ⟨e,finite,_,limit⟩ := first_location
  exact ⟨e,finite,1/2,by norm_num,limit⟩

/-- info: 'MissingSumFringes.first_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_location

/-- info: 'MissingSumFringes.first_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_resolution

end MissingSumFringes
