module

public import conjectures.SplitMatroidFlags.LocalCodes
public import conjectures.SplitMatroidFlags.Families
public import conjectures.SplitMatroidFlags.RankThree

@[expose] public section

namespace SplitMatroidFlags

open Finset

private lemma edge_columns (a : Three G) (R : Three (Finset G)) :
    (a.edges R).image Prod.snd = R.unionCols := by
  ext j
  simp only [mem_image,Prod.exists,Three.mem_edges,Three.unionCols,mem_union]
  grind

private lemma mask_overlap (X Y : Finset G) : ((mask X &&& mask Y) != 0) = decide (X ∩ Y).Nonempty := by
  rw [← mask_and]
  apply Bool.eq_iff_iff.mpr
  simp [mask_zero,nonempty_iff_ne_empty]

private lemma code_rank {H a T r} (ha : a ∈ charts H) (ts : T ⊆ univ \ a.coords)
    (live : ∀ j ∉ a.coords, ∃ i, Swap (bases H) a.coords i j) (hr : r ∈ slice H a T) :
    Module.finrank ℝ (directions (edgeCode a r)) = T.card + overlapCount r := by
  have supp := slice_support ha ts live hr
  obtain ⟨h,rfl⟩ := mem_slice.mp hr
  let R := (leastRows (rows H a) h).restrictSets T
  change Module.finrank ℝ (directions (edgeCode a R.masks)) = T.card + overlapCount R.masks
  change (edgeCode a R.masks).image Prod.snd = T at supp
  rw [edgeCode,decode_masks,edge_columns] at supp
  have dis : Disjoint a.coords R.unionCols := by
    rw [supp]
    exact disjoint_left.mpr fun j hj hT => (mem_sdiff.mp (ts hT)).2 hj
  rw [edgeCode,decode_masks,Three.row_dimension a (distinct_of_sorted (chart_in.mp ha).1) R dis,supp]
  simp [overlapCount,Three.masks,Three.map,mask_overlap,Three.merged]

private lemma no_lower (i : G) (V : Finset G) :
    (mask (univ.filter (· < i)) &&& mask V) = 0 ↔ ∀ j ∈ V, i.val ≤ j.val := by
  rw [← mask_and,mask_zero]
  constructor
  · intro empty j hj
    by_contra! bad
    have h : j ∈ univ.filter (· < i) ∩ V := mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,bad⟩,hj⟩
    rw [empty] at h
    exact notMem_empty _ h
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨low,hv⟩ := mem_inter.mp hj
    exact (not_lt_of_ge (h j hv)) (mem_filter.mp low).2

private lemma code_up {H a T r} (hr : r ∈ slice H a T) :
    ascending (lowRows a) r = true ↔ uphill Fin.val (edgeCode a r) := by
  obtain ⟨h,rfl⟩ := mem_slice.mp hr
  let R := (leastRows (rows H a) h).restrictSets T
  change ascending (lowRows a) R.masks = true ↔ _
  rw [edgeCode,decode_masks]
  change _ ↔ uphill Fin.val (a.edges R)
  simp only [ascending,lowRows,Three.masks,Three.map,Bool.and_eq_true,beq_iff_eq,no_lower]
  constructor
  · rintro ⟨⟨hx,hy⟩,hz⟩ ⟨i,j⟩ he
    rcases (Three.mem_edges _ _).mp he with ⟨rfl,hj⟩|⟨rfl,hj⟩|⟨rfl,hj⟩
    · exact hx _ hj
    · exact hy _ hj
    · exact hz _ hj
  · intro hh
    exact ⟨⟨fun j hj => hh _ ((Three.mem_edges a.x j).mpr (Or.inl ⟨rfl,hj⟩)),
      fun j hj => hh _ ((Three.mem_edges a.y j).mpr (Or.inr (Or.inl ⟨rfl,hj⟩)))⟩,
      fun j hj => hh _ ((Three.mem_edges a.z j).mpr (Or.inr (Or.inr ⟨rfl,hj⟩)))⟩

private lemma codes_inj {H a} (ha : a ∈ charts H) : Set.InjOn (edgeCode a) (allCodes H a) := by
  intro p hp q hq eq
  obtain ⟨S,_,hs⟩ := mem_biUnion.mp hp
  obtain ⟨T,_,ht⟩ := mem_biUnion.mp hq
  obtain ⟨u,rfl⟩ := mem_slice.mp hs
  obtain ⟨v,rfl⟩ := mem_slice.mp ht
  let U := (leastRows (rows H a) u).restrictSets S
  let V := (leastRows (rows H a) v).restrictSets T
  change edgeCode a U.masks = edgeCode a V.masks at eq
  rw [edgeCode,edgeCode,decode_masks,decode_masks] at eq
  have row (i j : G) : (i,j) ∈ a.edges U ↔ (i,j) ∈ a.edges V := eq ▸ Iff.rfl
  obtain ⟨xy,xz,yz⟩ := distinct_of_sorted (chart_in.mp ha).1
  have x : U.x = V.x := by ext j; simpa [Three.mem_edges,xy.symm,xz.symm] using row a.x j
  have y : U.y = V.y := by ext j; simpa [Three.mem_edges,xy,yz.symm] using row a.y j
  have z : U.z = V.z := by ext j; simpa [Three.mem_edges,xz,yz] using row a.z j
  change U.masks = V.masks
  simp [Three.masks,Three.map,x,y,z]

set_option maxHeartbeats 1000000 in
lemma local_count {H a} (ha : a ∈ charts H) (hm : HasMatches (bases H) a.coords)
    (live : ∀ j ∉ a.coords, ∃ i, Swap (bases H) a.coords i j) (first : Bool) (k : ℕ) :
    ((faces (bases H) k).filter (incident Fin.val first a.coords)).card = localTable H a first k := by
  classical
  let dim (r : Three ℕ) := ((edgeCode a r).image Prod.snd).card + overlapCount r
  rw [count_patterns (allCodes H a) (edgeCode a) dim (ascending (lowRows a)) Fin.val hm
    (codes_inj ha) (codes_represent ha hm) (fun r hr => ?_) (fun r hr => ?_) first k]
  · let ok (r : Three ℕ) := dim r = k ∧ (first = true → ascending (lowRows a) r = true)
    have join : (allCodes H a).filter ok =
        (univ \ a.coords).powerset.biUnion fun T => (slice H a T).filter ok := by
      ext r
      simp [allCodes]
      grind
    change ((allCodes H a).filter ok).card = _
    rw [join,card_biUnion]
    · unfold localTable
      apply sum_congr rfl
      intro T hT
      have ts := mem_powerset.mp hT
      have d (r) (hr : r ∈ slice H a T) : dim r = T.card + overlapCount r := by
        simp [dim,slice_support ha ts live hr]
      by_cases good : T.card ≤ k ∧ k ≤ T.card+2
      · rw [ite_eq_left good]
        apply congrArg Finset.card
        ext r
        simp only [mem_filter]
        change (r ∈ slice H a T ∧ _) ↔ (r ∈ slice H a T ∧ _)
        exact and_congr_right fun hr => by simp only [ok,d r hr]
      · rw [ite_eq_right good,card_eq_zero]
        apply eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hin,hd,_⟩ := mem_filter.mp hr
        change dim r = k at hd
        rw [d _ hin] at hd
        have small : overlapCount r ≤ 2 := min_le_left ..
        omega
    · intro S hS T hT ne
      apply disjoint_left.mpr
      intro r hs ht
      exact ne ((slice_support ha (mem_powerset.mp hS) live (mem_filter.mp hs).1).symm.trans
        (slice_support ha (mem_powerset.mp hT) live (mem_filter.mp ht).1))
  · obtain ⟨T,hT,hr⟩ := mem_biUnion.mp hr
    have ts := mem_powerset.mp hT
    simp [dim,code_rank ha ts live hr,slice_support ha ts live hr]
  · obtain ⟨_,_,hr⟩ := mem_biUnion.mp hr
    exact code_up hr

lemma table_faces {H : Lines} (hm : ∀ b ∈ bases H, HasMatches (bases H) b) (conn : ConnectedPairs H) (k : ℕ) :
    (faces (bases H) k).card = table H true k := by
  rw [counts_from_vertices (bases H) k Fin.val Fin.val_injective hm]
  let f (b : Finset G) := ((faces (bases H) k).filter (minimumAt Fin.val b)).card
  change (∑ b ∈ bases H, f b) = _
  rw [bases_as_charts H,sum_image (charts_inj H)]
  apply sum_congr rfl
  intro a ha
  have h := local_count ha (hm _ (chart_base ha)) (live_outside conn (hm _ (chart_base ha))) true k
  have e : incident Fin.val true a.coords = minimumAt Fin.val a.coords := by
    funext F
    apply propext
    simp [incident,minimumAt]
  refine Eq.trans ?_ h
  apply congrArg Finset.card
  exact filter_congr fun F _ => Iff.of_eq (congrFun e F).symm

lemma table_flags {H : Lines} (hm : ∀ b ∈ bases H, HasMatches (bases H) b) (conn : ConnectedPairs H) (k : ℕ) :
    flags (bases H) [k,0] (bases H) = table H false k := by
  rw [flags_from_vertices k hm]
  let f (b : Finset G) := ((faces (bases H) k).filter (b ∈ ·)).card
  change (∑ b ∈ bases H, f b) = _
  rw [bases_as_charts H,sum_image (charts_inj H)]
  apply sum_congr rfl
  intro a ha
  have h := local_count ha (hm _ (chart_base ha)) (live_outside conn (hm _ (chart_base ha))) false k
  have e : incident Fin.val false a.coords = (a.coords ∈ ·) := by
    funext F
    apply propext
    simp [incident]
  refine Eq.trans ?_ h
  apply congrArg Finset.card
  exact filter_congr fun F _ => Iff.of_eq (congrFun e F).symm

end SplitMatroidFlags
