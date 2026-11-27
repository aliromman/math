module

public import conjectures.YangYergerZhouCube.Faces
public import conjectures.YangYergerZhouCube.Geometry

public section
namespace YangYergerZhouCube
open Finset
open scoped symmDiff

variable {V ι : Type*} [DecidableEq ι] {edge : V → V → Prop}

theorem coordinate_weight [Fintype ι] (a : Finset ι) (p : Finset ι → ℕ) :
    distanceWeight a p = weight univ (fun x => p (a ∆ x)) := by
  unfold distanceWeight
  rw [← coordinate_sum a]
  simp [weight,inverseWeight,coordinate_distance,div_eq_mul_inv]

private theorem bounded_weight (s : Finset ι) (node : Finset ι → V) (es : cubeEdges edge s node)
    (r : V) (e0 : edge (node ∅) r) (p : Finset ι → ℕ) (uns : ¬Supplies edge (pack s node p) {r}) :
    weight s p ≤ weight s (fun _ => 1) := by
  induction s using Finset.strongInductionOn generalizing node p with
  | _ s ih =>
    have small : p ∅ ≤ 1 := by
      by_contra! h
      have two : p ∅ = 2 + (p ∅-2) := by omega
      have sum := Finset.add_sum_erase s.powerset (fun x => Multiset.replicate (p x) (node x))
        (show ∅∈s.powerset by simp)
      apply uns
      unfold pack
      rw [← sum]
      apply (Supplies.drop _).trans
      rw [two,Multiset.replicate_add]
      exact (Supplies.drop _).trans (Supplies.one e0)
    have ceiling : ceilingMass s p ≤ 2^s.card := by
      by_contra! h
      exact uns (((chung s node es p).2 h).trans (Supplies.one e0))
    have smaller (i) (hi : i∈s) : weight (s.erase i) (fold i p) ≤ weight (s.erase i) (fun _ => 1) := by
      let t := s.erase i
      have hni : i∉t := Finset.notMem_erase i s
      have back : insert i t=s := Finset.insert_erase hi
      have edges : cubeEdges edge (insert i t) node := back ▸ es
      have pass := pack_transfer t node (fun x => node (insert i x)) p (fun x => p (insert i x))
        (fun x => p (insert i x)/2) (cube_cross hni edges) (fun x _ => by omega)
      apply ih t (Finset.erase_ssubset hi) node (cube_near edges) e0 (fold i p)
      intro reach
      apply uns
      rw [←back,pack_split t hni]
      exact (pass.trans (.drop _)).trans reach
    have compare := add_le_add (Finset.sum_le_sum smaller) (show (ceilingMass s p : ℚ) ≤ (2^s.card:ℕ) by exact_mod_cast ceiling)
    have ones := face_balance s (fun _ => 1) (by decide)
    have unchanged (i : ι) : fold i (fun _ => 1) = fun _ => 1 := by funext x; norm_num [fold]
    simp [unchanged,ceilingMass] at ones
    rw [face_balance s p small] at compare
    have rhs : (∑ i ∈ s, weight (s.erase i) (fun _ => 1)) + (2^s.card:ℕ) =
        (s.card+1:ℚ)*weight s (fun _ => 1) := by simpa using ones
    rw [rhs] at compare
    exact (le_of_mul_le_mul_left compare (by exact_mod_cast (show 0<s.card+1 by omega)))

theorem resolution : CubeWeightConjecture := by
  intro m _ a
  refine ⟨rfl,fun x => ?_,fun p atRoot uns => ?_⟩
  · have hd := coordinate_distance a (a ∆ x)
    rw [symmDiff_symmDiff_cancel_left] at hd
    simp [inverseWeight,hd]
    exact_mod_cast (show 0 < (a ∆ x).card+1 by omega)
  · let node (x : Finset (Fin m)) := some (a ∆ x)
    let q (x : Finset (Fin m)) := p (a ∆ x)
    have es : cubeEdges (Adj a) univ node := fun x _ _ _ h => coordinate_edge a x h
    have noRoot : ¬ Supplies (Adj a) (pack univ node q) {none} := by
      intro reached
      apply uns
      rw [add_comm]
      apply (Supplies.drop _).trans
      simpa only [cube,pack,node,q,coordinate_sum a (fun x => Multiset.replicate (p x) (some x))] using reached
    have valid := bounded_weight univ node es none (by simp [node,Adj]) q noRoot
    simpa only [coordinate_weight,q] using valid

/-- info: 'YangYergerZhouCube.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end YangYergerZhouCube
