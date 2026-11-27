module

public import conjectures.BrownCameronEvenTrees.Statement
import conjectures.BrownCameronEvenTrees.CoefficientBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

open Finset
open BrownCameron (root_bound mem_layer choose_le_layer maximalLayer
  mem_maximal add_indep consecutive diff_injective diff_nonempty)

namespace BrownCameronEvenTrees

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem maximal_bound {j : ℕ} {S : Finset V} (hS : G.IsIndepSet S) (hj : j < S.card) :
    (maximalLayer G j).card + 1 ≤ 2 ^ (Fintype.card V - S.card) := by
  classical
  let O := univ \ S
  have hin : (maximalLayer G j).card ≤ (O.powerset.erase ∅).card := by
    apply card_le_card_of_injOn (fun t => t \ S) _ (diff_injective S hS)
    intro t ht
    exact mem_erase.mpr ⟨(diff_nonempty hS hj ht).ne_empty, mem_powerset.mpr
      (fun v hv => mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hv).2⟩)⟩
  have ho : O.card = Fintype.card V - S.card := by simp [O, card_sdiff_of_subset]
  have he : (O.powerset.erase ∅).card + 1 = O.powerset.card :=
    card_erase_add_one (by simp)
  rw [card_powerset, ho] at he
  omega

private def side (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → (v ∈ s ↔ w ∉ s)

omit [Fintype V] in
private theorem side_of_indep {t u : Finset V} (ht : G.IsIndepSet t) (hu : G.IsIndepSet u)
    (he : ∀ v, v ∈ t ↔ v ∉ u) : side G t := by
  intro v w adj
  constructor
  · exact fun hv hw => ht hv hw adj.ne adj
  · intro hw
    apply (he v).2
    exact fun hv => hu hv (by by_contra h; exact hw ((he w).2 h)) adj.ne adj

omit [Fintype V] in
private theorem unique_side {a : V} {s t : Finset V} (hc : G.Connected)
    (hs : side G s) (ht : side G t) (ha : a ∈ s ↔ a ∈ t) : s = t := by
  ext x
  obtain ⟨p⟩ := hc.preconnected a x
  induction p with
  | nil => exact ha
  | @cons a b x h p ih =>
    apply ih
    have x := hs h.symm
    have y := ht h.symm
    tauto

private theorem complementary [Nontrivial V] (hc : G.Connected) {k : ℕ}
    (hn : Fintype.card V = 2*k) {S t u : Finset V}
    (hS : G.IsIndepSet S) (ht : G.IsNIndepSet k t) (hu : G.IsNIndepSet k u)
    (hout : ∀ v ∉ S, v ∈ t ↔ v ∉ u) : ∀ v, v ∈ t ↔ v ∉ u := by
  classical
  have dis : Disjoint t u := by
    rw [disjoint_left]
    intro v hvt hvu
    have hvs : v ∈ S := by
      by_contra h
      exact (hout v h).1 hvt hvu
    obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
    have hws : w ∉ S := fun h => hS hvs h hw.ne hw
    by_cases hwu : w ∈ u
    · exact hu.isIndepSet hvu hwu hw.ne hw
    · exact ht.isIndepSet hvt ((hout w hws).2 hwu) hw.ne hw
  have he : t = uᶜ := eq_of_subset_of_card_le (by
    intro v h
    exact mem_compl.mpr (fun h' => disjoint_left.mp dis h h')) (by
    rw [card_compl,hn,ht.card_eq,hu.card_eq]
    omega)
  simp [he]

private def normalize (O : Finset V) (a : V) (t : Finset V) : Finset V := by
  classical
  exact O.filter (fun v => (v ∈ t ↔ a ∉ t))

omit [Fintype V] in
private theorem mem_normalize {O t : Finset V} {a v : V} :
    v ∈ normalize O a t ↔ v ∈ O ∧ (v ∈ t ↔ a ∉ t) := by
  classical
  simp [normalize]

private theorem outside_proper [Nontrivial V] {S t : Finset V} (hG : G.Connected)
    (hS : G.IsIndepSet S) (ht : G.IsIndepSet t) (hcard : (univ \ S).card < t.card) :
    ∃ v ∉ S, v ∉ t := by
  by_contra! hn
  have hs : t ⊆ univ \ S := by
    intro v hv
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hvs
    obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial v
    have hws : w ∉ S := fun xp => hS hvs xp hw.ne hw
    exact ht hv (hn w hws) hw.ne hw
  exact (not_le.mpr hcard) (card_le_card hs)

private theorem middle_maximal [Nontrivial V] (hc : G.Connected) {k : ℕ} (hk : 3 ≤ k)
    (hn : Fintype.card V = 2*k) {S : Finset V} (hS : G.IsIndepSet S) (hsize : S.card=k+1) :
    (maximalLayer G k).card ≤ 2^(k-2) := by
  classical
  let O := univ \ S
  have hO : O.card = k-1 := by
    simp [O,card_sdiff_of_subset,hn,hsize]
    omega
  obtain ⟨a,ha⟩ : O.Nonempty := card_pos.mp (by omega)
  have nempty {t} (ht : t ∈ maximalLayer G k) : (normalize O a t).Nonempty := by
    obtain ⟨it,_⟩ := mem_maximal.mp ht
    by_cases hat : a ∈ t
    · obtain ⟨v,hs,hnv⟩ := outside_proper hc hS it.isIndepSet (by
        change O.card < t.card
        rw [hO,it.card_eq]; omega)
      exact ⟨v,mem_normalize.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hs⟩,by tauto⟩⟩
    · obtain ⟨v,hv⟩ := diff_nonempty hS (by omega) ht
      obtain ⟨hvt,hvs⟩ := mem_sdiff.mp hv
      exact ⟨v,mem_normalize.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hvs⟩,by tauto⟩⟩
  let special (t : Finset V) := side G t ∧ a ∈ t
  let f (t : Finset V) := if special t then ∅ else normalize O a t
  have hcard : (maximalLayer G k).card ≤ (O.erase a).powerset.card := by
    apply card_le_card_of_injOn f
    · intro t _
      apply mem_powerset.mpr
      by_cases he : special t
      · simp [f,he]
      · simp only [f,he,ite_false]
        intro v hv
        obtain ⟨ho,hl⟩ := mem_normalize.mp hv
        apply mem_erase.mpr
        refine ⟨?_,ho⟩
        rintro rfl
        tauto
    · intro t ht u hu hef
      replace ht : t ∈ maximalLayer G k := ht
      replace hu : u ∈ maximalLayer G k := hu
      change f t = f u at hef
      by_cases sp : special t <;> by_cases sq : special u
      · exact unique_side (a := a) hc sp.1 sq.1 ⟨fun _ => sq.2,fun _ => sp.2⟩
      · exact False.elim ((nempty hu).ne_empty (by simpa [f,sp,sq] using hef.symm))
      · exact False.elim ((nempty ht).ne_empty (by simpa [f,sp,sq] using hef))
      · have eh : normalize O a t = normalize O a u := by simpa [f,sp,sq] using hef
        have parity (v) (hv : v ∉ S) : (v ∈ t ↔ a ∉ t) ↔ (v ∈ u ↔ a ∉ u) := by
          have ho : v ∈ O := mem_sdiff.mpr ⟨mem_univ _,hv⟩
          have h : v ∈ normalize O a t ↔ v ∈ normalize O a u := eh ▸ Iff.rfl
          simpa only [mem_normalize,ho,true_and] using h
        by_cases hp : a ∈ t ↔ a ∈ u
        · apply diff_injective S hS ht hu
          ext v
          simp only [mem_sdiff]
          by_cases hv : v ∈ S
          · simp [hv]
          · have q := parity v hv; tauto
        · have rev (v) (hv : v ∉ S) : v ∈ t ↔ v ∉ u := by
            have q := parity v hv; tauto
          have ct := (mem_maximal.mp ht).1
          have cu := (mem_maximal.mp hu).1
          have rel := complementary hc hn hS ct cu rev
          have t2 := side_of_indep ct.isIndepSet cu.isIndepSet rel
          have u2 := side_of_indep cu.isIndepSet ct.isIndepSet (fun v => by
            have q := rel v; tauto)
          by_cases hat : a ∈ t
          · exact False.elim (sp ⟨t2,hat⟩)
          · exact False.elim (sq ⟨u2,by tauto⟩)
  simpa [card_powerset,card_erase_of_mem ha,hO,Nat.sub_sub] using hcard
omit [Fintype V] [DecidableEq V] in
private theorem side_indep {s : Finset V} (hs : side G s) : G.IsIndepSet s := by
  intro x hx y hy _ adj
  exact (hs adj).1 hx hy

private theorem side_compl {s : Finset V} (hs : side G s) : side G sᶜ := by
  intro x y adj
  simp only [mem_compl, not_not]
  have h := hs adj
  tauto

omit [DecidableEq V] in
private theorem tree_side (T : G.IsTree) : ∃ s, side G s := by
  classical
  let c := T.coloringTwo
  refine ⟨univ.filter (fun v => c v=0),?_⟩
  intro v w adj
  have h := c.valid adj
  simp
  omega

private theorem choose_two {a j : ℕ} (hj : 0 < j) (ha : j < a) : 2 ≤ a.choose j := by
  have h := Nat.choose_pos ha.le
  have hn : a.choose j ≠ 1 := fun hc => by
    rcases Nat.choose_eq_one_iff.mp hc with rfl | e <;> omega
  omega

private theorem part_swap [Nontrivial V] (T : G.IsTree) {k : ℕ} (hk : 3≤k)
    (hn : Fintype.card V=2*k) {s : Finset V} (h : side G s) (hs : s.card=k) :
    ∃ t ∈ layer G k, (t∩s).card=1 ∧ (t∩sᶜ).card=k-1 := by
  classical
  have part : G.IsBipartiteWith (s : Set V) (↑(sᶜ) : Set V) := by
    constructor
    · exact Set.disjoint_left.mpr (fun _ hv hw => (mem_compl.mp hw) hv)
    · intro v w adj
      have q := h adj
      simp
      tauto
  have total := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges part
  have count := T.card_edgeFinset
  have leaf : ∃ v ∈ s, G.degree v = 1 := by
    by_contra! hne
    have bl : ∑ v ∈ s, 2 ≤ ∑ v ∈ s, G.degree v := by
      apply sum_le_sum
      intro v hv
      have pos := T.connected.preconnected.degree_pos_of_nontrivial v
      specialize hne v hv
      omega
    simp [hs] at bl
    omega
  obtain ⟨v,hv,deg⟩ := leaf
  obtain ⟨w,hvw,uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp deg
  have hw : w ∈ sᶜ := mem_compl.mpr ((h hvw).1 hv)
  have hv' : v ∉ sᶜ := by simp [hv]
  have ws : sᶜ.card = k := by rw [card_compl,hn,hs]; omega
  let t := insert v (sᶜ.erase w)
  refine ⟨t,mem_layer.mpr ⟨?_,?_⟩,?_,?_⟩
  · apply add_indep ((side_indep (side_compl h)).mono (erase_subset w _))
    intro x hx adj
    exact (mem_erase.mp hx).1 (uniq x adj)
  · have ve : v ∉ sᶜ.erase w := fun hx => hv' (mem_erase.mp hx).2
    simp [t,ve,card_erase_of_mem hw,ws]
    omega
  · simp [t,insert_inter_of_mem hv, erase_inter]
  · simp [t,insert_inter_of_notMem hv',erase_inter,card_erase_of_mem hw,ws]

private theorem balanced_four [Nontrivial V] (T : G.IsTree) {k : ℕ} (hk : 3≤k)
    (hn : Fintype.card V=2*k) {s : Finset V} (h : side G s) (hs : s.card=k)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) : 4 ≤ (layer G j).card := by
  classical
  have hs' : sᶜ.card=k := by rw [card_compl,hn,hs]; omega
  have hc := side_compl h
  by_cases eq : j = k
  · subst j
    let f (x : Finset V) := (x ∩ s).card
    obtain ⟨t,ht,ht1,_⟩ := part_swap T hk hn h hs
    obtain ⟨u,hu,_,hu1⟩ := part_swap T hk hn hc hs'
    have u1 : f u = k-1 := by simpa [f] using hu1
    have hh : ({0,1,k-1,k} : Finset ℕ) ⊆ (layer G k).image f := by
      simp only [insert_subset_iff, singleton_subset_iff]
      refine ⟨mem_image.mpr ⟨sᶜ,mem_layer.mpr ⟨side_indep hc,hs'⟩,by simp [f]⟩,
        mem_image.mpr ⟨t,ht,ht1⟩, mem_image.mpr ⟨u,hu,u1⟩,
        mem_image.mpr ⟨s,mem_layer.mpr ⟨side_indep h,hs⟩,by simp [f,hs]⟩⟩
    have h4 : ({0,1,k-1,k} : Finset ℕ).card=4 := by
      simp [show 0 ≠ k-1 by omega,show 0≠k by omega,show 1≠k-1 by omega,
        show 1≠k by omega, show k-1≠k by omega]
    exact h4 ▸ (card_le_card hh).trans card_image_le
  · have p : s.powersetCard j ∪ sᶜ.powersetCard j ⊆ layer G j := by
      intro t ht
      rcases mem_union.mp ht with hs | hs
      · obtain ⟨sub,card⟩ := mem_powersetCard.mp hs
        exact mem_layer.mpr ⟨(side_indep h).mono sub,card⟩
      · obtain ⟨sub,card⟩ := mem_powersetCard.mp hs
        exact mem_layer.mpr ⟨(side_indep hc).mono sub,card⟩
    have dj : Disjoint (s.powersetCard j) (sᶜ.powersetCard j) := by
      rw [disjoint_left]
      intro t ht hu
      obtain ⟨sub,ct⟩ := mem_powersetCard.mp ht
      obtain ⟨sub',_⟩ := mem_powersetCard.mp hu
      obtain ⟨v,hv⟩ : t.Nonempty := card_pos.mp (ct ▸ hj)
      exact (mem_compl.mp (sub' hv)) (sub hv)
    have bound := card_le_card p
    rw [card_union_of_disjoint dj,card_powersetCard,card_powersetCard,hs,hs'] at bound
    have bt := choose_two hj (by omega : j<k)
    omega
private theorem pow_gap (t m : ℕ) (hm : t ≤ m) : (m-t) + 2^t ≤ 2^m := by
  induction m with
  | zero => simp_all
  | succ m ih =>
    by_cases h : t=m+1
    · simp [h]
    · have i := ih (by omega)
      have p : 0 < 2^m := by positivity
      rw [pow_succ]
      omega

private theorem ratio_bound [Nontrivial V] (T : G.IsTree) (k : ℕ) (hk : 3≤k)
    (hn : Fintype.card V=2*k) {j : ℕ} (hj : j<G.indepNum) :
    (layer G j).card ≤ (2^(k-2)+k+1) * (layer G (j+1)).card := by
  classical
  obtain ⟨S,ind⟩ := G.exists_isNIndepSet_indepNum
  have hl : j < S.card := by simpa only [ind.card_eq] using hj
  have ha : S.card ≤ 2*k := by simpa [hn] using (card_le_univ S)
  obtain ⟨s,hs⟩ := tree_side T
  have a1 := (side_indep hs).card_le_indepNum
  have a2 := (side_indep (side_compl hs)).card_le_indepNum
  rw [card_compl,hn] at a2
  rw [← ind.card_eq] at a1 a2
  have hc := consecutive G j
  have hm := maximal_bound ind.isIndepSet hl
  rw [hn] at hm
  let A := (layer G (j+1)).card
  have ch := choose_le_layer S ind.isIndepSet (j+1)
  change S.card.choose (j+1) ≤ A at ch
  have hpos : 0 < A := (Nat.choose_pos (by omega)).trans_le ch
  change (layer G j).card ≤ A*(j+1) + (maximalLayer G j).card at hc
  change (layer G j).card ≤ (2^(k-2)+k+1)*A
  by_cases big : k+2 ≤ S.card
  · have gap := pow_gap (2*k-S.card) (k-2) (by omega)
    have small : j+1+(maximalLayer G j).card ≤ 2^(k-2)+k+1 := by omega
    have m := Nat.le_mul_of_pos_right (maximalLayer G j).card hpos
    nlinarith [Nat.mul_le_mul_right A small]
  have enough (hb : (maximalLayer G j).card ≤ 2^(k-2)*A) : (layer G j).card ≤
      (2^(k-2)+k+1)*A := by
    have m := Nat.mul_le_mul_left A (show j+1≤k+1 by omega)
    nlinarith
  have ep : 2^(k-1) = 2*2^(k-2) := by
    rw [show k-1=(k-2)+1 by omega,pow_succ,Nat.mul_comm]
  by_cases midsize : S.card=k+1
  · by_cases two : 2≤A
    · have l : 2*k-S.card=k-1 := by omega
      rw [l,ep] at hm
      apply enough
      nlinarith [Nat.mul_le_mul_left (2^(k-2)) two]
    · have jj : j=k := by
        by_contra hh
        have c := choose_two (by omega : 0 < j+1) (by omega : j+1<S.card)
        omega
      subst j
      apply enough
      have m := middle_maximal T.connected hk hn ind.isIndepSet midsize
      have o : A=1 := by omega
      simpa [o] using m
  · have eq : S.card=k := by omega
    have es : s.card=k := by omega
    have four := balanced_four T hk hn hs es (Nat.zero_lt_succ j) (by omega)
    change 4≤A at four
    have l : 2*k-S.card=k := by omega
    have e : 2^k = 4*2^(k-2) := by
      calc 2^k = 2^((k-2)+2) := by congr 1; omega
           _ = _ := by rw [pow_add]; ring
    rw [l,e] at hm
    apply enough
    nlinarith [Nat.mul_le_mul_left (2^(k-2)) four]

public theorem resolution : Conjecture := by
  intro k hk T ht z hz
  have : Nontrivial (Fin (2*k)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨S,ind⟩ := T.exists_isNIndepSet_indepNum
  apply root_bound (fun j => (layer T j).card) (2^(k-2)+k+1) T.indepNum (Nat.zero_lt_succ _)
      (card_pos.mpr ⟨S,mem_layer.mpr ind⟩) _ z hz
  intro j hj
  exact ratio_bound ht k hk (Fintype.card_fin _) hj

/-- info: 'BrownCameronEvenTrees.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BrownCameronEvenTrees
