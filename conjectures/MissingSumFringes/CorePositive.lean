module

public import conjectures.MissingSumFringes.CoreAtoms
public import conjectures.MissingSumFringes.CoreMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

private theorem prob_complement (s : Finset ℕ) (p : Finset ℕ → Prop) :
    prob s (fun A => ¬p A)+prob s p=1 := by
  rw [prob_count,prob_count,←add_div]
  have count := @card_filter_add_card_filter_not _ s.powerset p (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _)
  rw [add_comm] at count
  rw [←Nat.cast_add]
  calc
    _ = (s.powerset.card:ℝ)/2^s.card := congrArg (fun n : ℕ => (n:ℝ)/2^s.card) count
    _ = 1 := by simp

private theorem prob_subset {E P : Finset ℕ} (sub : E⊆P) :
    prob P (fun B => B⊆E)=(2:ℝ)^E.card/2^P.card := by
  rw [prob_count]
  have same : @Finset.filter _ (fun B => B⊆E) (fun _ => Classical.propDecidable _) P.powerset=E.powerset := by
    ext B
    simp only [mem_filter,mem_powerset]
    exact ⟨And.right,fun h => ⟨h.trans sub,h⟩⟩
  have e := congrArg (fun x : Finset (Finset ℕ) => (x.card:ℝ)/2^P.card) same
  simpa only [card_powerset,Nat.cast_pow,Nat.cast_ofNat] using e

private theorem prob_exact {E P : Finset ℕ} (sub : E⊆P) :
    prob P (fun B => B=E)=1/(2:ℝ)^P.card := by
  rw [prob_count]
  have same : @Finset.filter _ (fun B => B=E) (fun _ => Classical.propDecidable _) P.powerset={E} := by
    ext B
    simp only [mem_filter,mem_powerset,mem_singleton]
    exact ⟨And.right,fun h => ⟨h ▸ sub,h⟩⟩
  have e := congrArg (fun x : Finset (Finset ℕ) => (x.card:ℝ)/2^P.card) same
  simpa only [card_singleton,Nat.cast_one] using e

private theorem extent_anti {A B : Finset ℕ} (sub : A⊆B) (n : ℕ) : extent n B≤extent n A := by
  apply sup_mono
  exact sdiff_subset_sdiff_right _ (add_subset_add sub sub)

/-- A prescribed prefix with at most one omitted site has positive limiting mass
provided that the far tail has probability below one quarter. -/
private theorem positive_pattern {b m t : ℕ} {E : Finset ℕ} (hb : 0<b)
    (sub : E⊆range b) (cost : b≤E.card+1) (shape : side true b m t E)
    (rare : 2*(decay^b/(1-decay))≤1/2) : 0<atom true m t := by
  let P := range b
  have fixed : prob P (fun B => B=E)=1/(2:ℝ)^b := by simpa [P] using prob_exact sub
  have half : (1/2:ℝ)≤prob P (fun B => B⊆E) := by
    rw [prob_subset sub,card_range,le_div_iff₀ (by positivity)]
    have bound := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) cost
    rw [pow_succ] at bound
    linarith
  have unif {n : ℕ} (bn : b≤n) : (1/(2:ℝ)^b)/2 ≤ sideMass true n m t := by
    let R := range n \ P
    let bad := fun B : Finset ℕ => b<extent n (E∪B)
    let good := fun B : Finset ℕ => ¬bad B
    have ps : P⊆range n := range_mono bn
    have full : P∪R=range n := union_sdiff_of_subset ps
    have dis : Disjoint P R := disjoint_sdiff_self_right
    have split (A : Finset ℕ) (ss : A⊆range n) : (A∩P)∪(A∩R)=A := by
      rw [←inter_union_distrib_left,full,inter_eq_left.mpr ss]
    have decrease : prob P (fun B => B⊆E)*prob R bad≤decay^b/(1-decay) := by
      rw [←pair_prob dis full.subset]
      apply (prob_mono _ ?_).trans (prob_far b n)
      intro A ha both
      obtain ⟨hp,hole⟩ := both
      have smaller : A⊆E∪(A∩R) := by
        simpa only [split A ha] using (union_subset_union hp (Subset.rfl : A∩R⊆A∩R))
      exact hole.trans_le (extent_anti smaller n)
    have low : (1/2:ℝ)≤prob R good := by
      have comp := prob_complement R bad
      change prob R good+prob R bad=1 at comp
      nlinarith only [comp,rare,decrease,mul_le_mul_of_nonneg_right half (prob_nonneg R bad)]
    have under : prob P (fun B => B=E)*prob R good≤sideMass true n m t := by
      rw [←pair_prob dis full.subset]
      apply prob_mono
      intro A ha cond
      obtain ⟨eq,well⟩ := cond
      have select : A=E∪(A∩R) := by simpa only [eq] using (split A ha).symm
      have he : extent n A≤b := by
        change ¬b<extent n (E∪(A∩R)) at well
        rw [select]
        omega
      exact (side_cut bn he).mpr ((side_local true b m t A hb).mp (eq ▸ shape))
    apply le_trans _ under
    rw [fixed,div_eq_mul_inv _ 2]
    exact mul_le_mul_of_nonneg_left (by simpa using low) (by positivity)
  have positive : 0<(1/(2:ℝ)^b)/2 := by positivity
  apply positive.trans_le (ge_of_tendsto (sideMass_limit true m t) ?_)
  filter_upwards [eventually_ge_atTop b] with n hn
  exact unif hn

private theorem two_shapes {b : ℕ} (hb : 2≤b) :
    side true b 0 0 (range b) ∧ side true b 1 2 ((range b).erase 1) := by
  let P := range b
  let E := P.erase 1
  have origin : 0∈P := mem_range.mpr (by omega)
  have present : 0∈E := mem_erase.mpr ⟨by decide,origin⟩
  have first : missing b P=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨xp,absent⟩ := mem_sdiff.mp hx
    exact absent (mem_add.mpr ⟨0,origin,x,xp,zero_add _⟩)
  have second : missing b E={1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨xp,absent⟩ := mem_sdiff.mp hx
      by_contra neq
      have xe : x∈E := mem_erase.mpr ⟨fun e => neq (mem_singleton.mpr e),xp⟩
      exact absent (mem_add.mpr ⟨0,present,x,xe,zero_add _⟩)
    · intro hx
      obtain rfl := mem_singleton.mp hx
      apply mem_sdiff.mpr ⟨mem_range.mpr (by omega),?_⟩
      rintro bad
      obtain ⟨a,ha,c,hc,eq⟩ := mem_add.mp bad
      have a1 := (mem_erase.mp ha).1
      have c1 := (mem_erase.mp hc).1
      omega
  constructor
  · change (_ → 0∈P) ∧ (missing b P).card=0 ∧ (missing b P).sup (·+1)=0
    simp [origin,first]
  · change (_ → 0∈E) ∧ (missing b E).card=1 ∧ (missing b E).sup (·+1)=2
    simp [present,second]

theorem atom_base_positive : 0<atom true 0 0 ∧ 0<atom true 1 2 := by
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one decay_pos.le decay_lt
  have fade : Tendsto (fun b : ℕ => 2*(decay^b/(1-decay))) atTop (𝓝 0) := by
    simpa using (lim.div_const (1-decay)).const_mul 2
  obtain ⟨b,hb,small⟩ := ((eventually_ge_atTop 2).and (fade.eventually_lt_const (by norm_num : (0:ℝ)<1/2))).exists
  obtain ⟨first,second⟩ := two_shapes hb
  refine ⟨positive_pattern (by omega) Subset.rfl (by simp) first small.le,
    positive_pattern (by omega) (erase_subset ..) ?_ second small.le⟩
  rw [card_erase_add_one (mem_range.mpr (by omega : 1<b)),card_range]

theorem coreD_base_positive : 0<coreD (atom true) 0 ∧ 0<coreD (atom true) 1 := by
  obtain ⟨h0,h1⟩ := atom_base_positive
  have van := fun m t h => @atom_zero_of_lt m t true h
  exact ⟨coreD_pos_of (atom_nonneg true) atom_le_normWindow van (m:=0) (by decide) h0 h0,
    coreD_pos_of (atom_nonneg true) atom_le_normWindow van (m:=0) (by decide) h0 h1⟩

end MissingSumFringes
