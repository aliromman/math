module

public import conjectures.MissingSumFringes.Tail
import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Pointwise Classical Topology

def side (anchor : Bool) (q m t : ℕ) (A : Finset ℕ) : Prop :=
  (anchor=true → 0∈A) ∧ (missing q A).card=m ∧ extent q A=t

noncomputable def sideMass (b : Bool) (q m t : ℕ) := prob (range q) (side b q m t)

theorem side_local (b : Bool) (q m t : ℕ) (A : Finset ℕ) (pos : 0<q) :
    side b q m t (A∩range q) ↔ side b q m t A := by
  simp [side,missing_restrict,extent_restrict,pos]

theorem side_cut {b : Bool} {q n m t : ℕ} {A : Finset ℕ} (hqn : q≤n) (he : extent n A≤q) :
    side b n m t A ↔ side b q m t A := by
  have e := extent_sizes hqn he
  simp only [side,extent,e]

theorem side_down {b : Bool} {q n m t : ℕ} {A : Finset ℕ} (hqn : q≤n) (ht : t≤q)
    (h : side b n m t A) : side b q m t A :=
  (side_cut hqn (h.2.2.le.trans ht)).mp h

theorem sideMass_anti (b : Bool) (m t : ℕ) : Antitone (fun n ↦ sideMass b (n+(t+1)) m t) := by
  intro i j hij
  dsimp only [sideMass]
  rw [←restrict_prob (range_mono (Nat.add_le_add_right hij (t+1))) (side b (i+(t+1)) m t)]
  apply prob_mono
  intro A _ h
  apply (side_local b _ _ _ A (by omega)).mpr
  exact side_down (by omega) (by omega) h

/-- Limiting probability of one prescribed fringe count and last missing position. -/
noncomputable def atom (b : Bool) (m t : ℕ) : ℝ := ⨅ n : ℕ, sideMass b (n+(t+1)) m t

theorem sideMass_limit (b : Bool) (m t : ℕ) :
    Tendsto (fun n ↦ sideMass b n m t) atTop (𝓝 (atom b m t)) := by
  apply (tendsto_add_atTop_iff_nat (t+1)).mp
  apply tendsto_atTop_ciInf (sideMass_anti b m t)
  exact ⟨0,Set.forall_mem_range.mpr (fun _ ↦ prob_nonneg ..)⟩

theorem atom_nonneg (b : Bool) (m t : ℕ) : 0≤atom b m t :=
  ge_of_tendsto' (sideMass_limit b m t) (fun _ ↦ prob_nonneg ..)

theorem atom_zero_of_lt {m t : ℕ} (b : Bool) (h : t<m) : atom b m t=0 := by
  apply tendsto_nhds_unique (sideMass_limit b m t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop t] with n hn
  symm
  unfold sideMass prob
  apply (avg_congr (range n) (g := fun _ ↦ (0:ℝ)) ?_).trans (avg_const _ _)
  intro A _
  split
  · next hit =>
      have eq := extent_sizes hn (hit.2.2.le)
      have le : (missing t A).card ≤ t :=
        (card_mono (sdiff_subset : missing t A ⊆ range t)).trans_eq (card_range t)
      rw [←eq,hit.2.1] at le
      omega
  · rfl

theorem refl_range (n : ℕ) : reflect n (range n)=range n := by
  apply Subset.antisymm (reflect_subset Subset.rfl)
  intro x hx
  apply mem_image.mpr
  have b := mem_range.mp hx
  exact ⟨n-1-x,mem_range.mpr (by omega),by omega⟩

theorem prob_refl (n : ℕ) (p : Finset ℕ → Prop) :
    prob (range n) (fun A ↦ p (reflect n A))=prob (range n) p := by
  have h := avg_image (range n) (fun x ↦ n-1-x) (fun x ↦ n-1-x)
    (fun x hx ↦ show n-1-(n-1-x)=x by have := mem_range.mp hx; omega) (fun A ↦ if p A then 1 else 0)
  change prob (reflect n (range n)) p=prob (range n) (fun A ↦ p (reflect n A)) at h
  rwa [refl_range,eq_comm] at h

theorem prob_far_right (q n : ℕ) :
    prob (range n) (fun A ↦ q<extent (n-1) (reflect n A)) ≤ decay^q/(1-decay) := by
  rw [prob_refl n (fun A ↦ q<extent (n-1) A)]
  calc
    _ = prob (range n) (fun A ↦ q<extent (n-1) (A∩range (n-1))) := by
      apply prob_congr
      intro A _
      rw [extent_restrict]
    _ = _ := restrict_prob (range_mono (Nat.sub_le n 1)) (fun A ↦ q<extent (n-1) A)
    _ ≤ _ := prob_far q (n-1)

noncomputable def joint (b : Bool) (n m t j s : ℕ) : ℝ :=
  prob (range n) (fun A ↦ side b n m t A ∧ side b (n-1) j s (reflect n A))

private theorem trunc_eq {n q : ℕ} (cap : q+q≤n) (pos : 0<q) (b : Bool) (m t j s : ℕ) :
    prob (range n) (fun A ↦ side b q m t A ∧ side b q j s (reflect n A)) =
      sideMass b q m t * sideMass b q j s := by
  unfold sideMass
  rw [←two_ends cap (side b q m t) (side b q j s)]
  apply prob_congr
  intro A _
  rw [side_local _ _ _ _ _ pos,side_local _ _ _ _ _ pos]

private theorem joint_close {n q m t j s : ℕ} (b : Bool) (pos : 0<q) (cap : q+q≤n)
    (ht : t≤q) (hs : s≤q) : |joint b n m t j s - sideMass b q m t * sideMass b q j s| ≤
      2*(decay^q/(1-decay)) := by
  rw [←trunc_eq cap pos]
  have dom : joint b n m t j s ≤ prob (range n) (fun A ↦ side b q m t A ∧ side b q j s (reflect n A)) := by
    apply prob_mono
    intro A _ h
    exact ⟨side_down (by omega) ht h.1,side_down (by omega) hs h.2⟩
  rw [abs_of_nonpos (sub_nonpos.mpr dom)]
  let u := fun A ↦ side b q m t A ∧ side b q j s (reflect n A)
  let v := fun A ↦ side b n m t A ∧ side b (n-1) j s (reflect n A)
  have diff : prob (range n) u ≤ prob (range n) v + prob (range n) (fun A ↦ q<extent n A) +
      prob (range n) (fun A ↦ q<extent (n-1) (reflect n A)) := by
    unfold prob avg
    rw [←expect_add_distrib,←expect_add_distrib]
    apply expect_le_expect
    intro A _
    by_cases l : q<extent n A <;> by_cases r : q<extent (n-1) (reflect n A)
    all_goals try {simp only [l,r,ite_true,ite_false]; split <;> split <;> norm_num}
    have iff : u A ↔ v A := (and_congr (side_cut (by omega) (by omega : extent n A≤q))
      (side_cut (by omega) (by omega : extent (n-1) (reflect n A)≤q))).symm
    simp only [iff,l,r,ite_false,add_zero]
    by_cases h : v A <;> simp [h]
  have L := prob_far q n
  have R := prob_far_right q n
  change prob (range n) u ≤ joint b n m t j s + _ + _ at diff
  linarith

theorem joint_limit (b : Bool) (m t j s : ℕ) :
    Tendsto (fun n ↦ joint b n m t j s) atTop (𝓝 (atom b m t*atom b j s)) := by
  have grow : Tendsto (fun n : ℕ ↦ n/2) atTop atTop :=
    tendsto_atTop.mpr (fun N ↦ (eventually_ge_atTop (2*N)).mono (fun n hn ↦ by omega))
  have both := ((sideMass_limit b m t).mul (sideMass_limit b j s)).comp grow
  apply Filter.Tendsto.congr_dist both
  have z := ((tendsto_pow_atTop_nhds_zero_of_lt_one decay_pos.le decay_lt).comp grow).div_const (1-decay)
  have z' := z.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    (g := fun n : ℕ ↦ 2*(decay^(n/2)/(1-decay)))
  · filter_upwards [eventually_ge_atTop (2*(t+s+1))] with n hn
    rw [Real.dist_eq,abs_sub_comm]
    exact joint_close (m := m) (t := t) (j := j) (s := s) (n := n) (q := n/2) b (by omega) (by omega) (by omega) (by omega)
  · simpa using z'

end MissingSumFringes
