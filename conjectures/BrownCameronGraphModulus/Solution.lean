module

public import conjectures.BrownCameronGraphModulus.Statement
import conjectures.BrownCameronEvenTrees.CoefficientBounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset
open BrownCameron (root_bound mem_layer choose_le_layer maximalLayer
  mem_maximal add_indep consecutive diff_injective diff_nonempty)

namespace BrownCameronGraphModulus

private theorem product_pos {L : List ℕ} (h : ∀ p ∈ L, 0 < p) : 0 < L.prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    exact Nat.mul_pos (h _ (by simp)) (ih (fun q hq => h q (by simp [hq])))

private theorem no_ones (L : List ℕ) (h : ∀ p ∈ L, 0 < p) (hs : 2 ≤ L.sum) :
    ∃ R : List ℕ, (∀ p ∈ R, 2 ≤ p) ∧ R.sum = L.sum ∧
      L.prod + L.length ≤ R.prod + R.length := by
  by_cases ho : 1 ∈ L
  · have hp := List.perm_cons_erase ho
    cases eq : L.erase 1 with
    | nil =>
      have e := hp.sum_eq
      simp [eq] at e
      omega
    | cons p R =>
      rw [eq] at hp
      have pos (v) (hv : v ∈ 1 :: p :: R) := h v (hp.mem_iff.mpr hv)
      have pp := pos p (by simp)
      have P := product_pos (L := R) (fun x hx => pos x (by simp [hx]))
      have ls := hp.sum_eq
      have lp := hp.prod_eq
      have ll := hp.length_eq
      simp at ls lp ll
      let W := (p+1)::R
      have pW : ∀ a ∈ W, 0<a := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · exact pos a (by simp [ha])
      have sw : W.sum = L.sum := by simp [W,ls]; omega
      have ltlen : W.length < L.length := by simp [W,ll]
      obtain ⟨Q,hq,qs,qb⟩ := no_ones W pW (sw ▸ hs)
      refine ⟨Q,hq,qs.trans sw, le_trans ?_ qb⟩
      simp [W,lp,ll]
      nlinarith
  · exact ⟨L,fun v hv => by
        have hvp := h v hv
        have ne : v ≠ 1 := fun hv1 => ho (hv1 ▸ hv)
        omega,rfl,le_rfl⟩
termination_by L.length

private theorem split_part (p : ℕ) (h : 2 ≤ p) :
    ∃ a b : ℕ, 2*a+3*b=p ∧ p ≤ 2^a*3^b ∧ 1 ≤ a+b := by
  by_cases hp : p ≤ 3
  · interval_cases p
    · exact ⟨1,0,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  · obtain ⟨a,b,hs,hp',hl⟩ := split_part (p-2) (by omega)
    refine ⟨a+1,b,by omega,?_,by omega⟩
    rw [pow_succ]
    have e : p-2+2=p := by omega
    nlinarith
termination_by p

private theorem split_parts (R : List ℕ) (h : ∀ p ∈ R, 2≤p) :
    ∃ a b : ℕ, 2*a+3*b=R.sum ∧ R.prod ≤ 2^a*3^b ∧ R.length ≤ a+b := by
  induction R with
  | nil => exact ⟨0,0,by decide,by decide,by decide⟩
  | cons p R ih =>
    obtain ⟨a,b,x,y,z⟩ := split_part p (h p (by simp))
    obtain ⟨c,d,x',y',z'⟩ := ih (fun i hi => h i (by simp [hi]))
    refine ⟨a+c,b+d,by simp; omega,?_,by simp; omega⟩
    simp only [List.prod_cons,pow_add]
    nlinarith [Nat.mul_le_mul y y']

private theorem few_twos (a b : ℕ) : ∃ c d : ℕ, c ≤ 2 ∧ 2*a+3*b=2*c+3*d ∧
    2^a*3^b+a+b ≤ 2^c*3^d+c+d := by
  by_cases h : a ≤ 2
  · exact ⟨a,b,h,rfl,le_rfl⟩
  obtain ⟨c,d,le,eq,bound⟩ := few_twos (a-3) (b+2)
  refine ⟨c,d,le,by omega,le_trans ?_ bound⟩
  calc
    2^a*3^b+a+b = 2^(a-3)*8*3^b+a+b := by
      conv_lhs => arg 1; arg 1; arg 1; rw [show a=a-3+3 by omega, pow_add]
      ring
    _ ≤ 2^(a-3)*3^(b+2)+(a-3)+(b+2) := by
      rw [pow_add]
      have hp : 0 < 2^(a-3)*3^b := by positivity
      nlinarith [show a-3+3=a by omega]
termination_by a

private theorem partition_bound (n : ℕ) (hn : 3 ≤ n) (L : List ℕ)
    (h : ∀ p ∈ L, 0 < p) (hs : L.sum = n-1) : L.prod + L.length ≤ bound n := by
  obtain ⟨R,hr,rs,rb⟩ := no_ones L h (by omega)
  obtain ⟨a,b,ab,hprod,hlen⟩ := split_parts R hr
  obtain ⟨c,d,hc,e,le⟩ := few_twos a b
  apply rb.trans ((Nat.add_le_add hprod hlen).trans (by omega : 2^a*3^b + (a+b) ≤ 2^c*3^d+c+d)) |>.trans
  unfold bound
  interval_cases c
  · simp [show n%3=1 by omega,show (n-1)/3=d by omega]
  · simp [show n%3=0 by omega,show (n-3)/3=d by omega,show n/3=d+1 by omega]
    omega
  · simp [show n%3=2 by omega,show (n-5)/3=d by omega,show (n+1)/3=d+2 by omega]
    omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private noncomputable def subsetsWithin (G : SimpleGraph V) (U : Finset V) : Finset (Finset V) := by
  classical
  exact U.powerset.filter (fun t : Finset V => G.IsIndepSet t)

omit [Fintype V] in
private theorem mem_within {U t : Finset V} :
    t ∈ subsetsWithin G U ↔ t ⊆ U ∧ G.IsIndepSet t := by
  classical
  simp [subsetsWithin]

omit [Fintype V] in
private theorem independent_product (r : ℕ) (U : Finset V)
    (h : ∀ t ∈ subsetsWithin G U, t.card ≤ r) :
    ∃ L : List ℕ, (∀ p ∈ L, 0<p) ∧ L.length = r ∧ L.sum = U.card+r ∧
      (subsetsWithin G U).card ≤ L.prod := by
  classical
  have empty_bound : (subsetsWithin G (∅ : Finset V)).card ≤ 1 := by
    calc
      _ ≤ (∅ : Finset V).powerset.card := card_filter_le _ _
      _ = 1 := by simp
  induction r generalizing U with
  | zero =>
    have emp : U = ∅ := by
      by_contra! ne
      obtain ⟨v,hv⟩ := ne
      have ind : G.IsIndepSet ({v} : Finset V) := by simp [SimpleGraph.isIndepSet_iff]
      have bad := h {v} (mem_within.mpr ⟨by simpa using hv,ind⟩)
      simp at bad
    subst U
    exact ⟨[],by simp,by simp,by simp,by simpa using empty_bound⟩
  | succ r ih =>
    by_cases nempty : U.Nonempty
    · let H := subsetsWithin G U
      let hits (w : V) := H.filter (w ∈ ·)
      obtain ⟨v,hv,best⟩ := U.exists_max_image (fun w => (hits w).card) nempty
      let N := U.filter (fun u => u≠v ∧ ¬G.Adj v u)
      let W := U \ N
      have subNU : N ⊆ U := filter_subset _ _
      have avoid : v ∉ N := by simp [N]
      have hin : ∀ t ∈ subsetsWithin G N, t.card ≤ r := by
        intro t ht
        obtain ⟨ts,ti⟩ := mem_within.mp ht
        have hv' : v ∉ t := fun x => avoid (ts x)
        have ins : G.IsIndepSet (insert v t : Finset V) :=
          add_indep ti (fun w hw => (mem_filter.mp (ts hw)).2.2)
        have hj := h (insert v t) (mem_within.mpr ⟨insert_subset hv (ts.trans subNU),ins⟩)
        simpa [hv'] using hj
      obtain ⟨L,lp,ll,ls,lb⟩ := ih N hin
      have hv_le : (hits v).card ≤ (subsetsWithin G N).card := by
        apply card_le_card_of_injOn (fun t => t.erase v)
        · intro t ht
          obtain ⟨h0,hv'⟩ := mem_filter.mp ht
          obtain ⟨ts,ti⟩ := mem_within.mp h0
          refine mem_within.mpr ⟨?_,ti.mono (erase_subset v _)⟩
          intro w hw
          obtain ⟨hne,hm⟩ := mem_erase.mp hw
          exact mem_filter.mpr ⟨ts hm,hne,ti hv' hm hne.symm⟩
        · intro t ht u hu he
          have hv1 := (mem_filter.mp ht).2
          have hv2 := (mem_filter.mp hu).2
          simpa [hv1,hv2] using congrArg (insert v) he
      have cover : H ⊆ subsetsWithin G N ∪ W.biUnion hits := by
        intro t ht
        obtain ⟨su,si⟩ := mem_within.mp ht
        by_cases sub : t ⊆ N
        · exact mem_union_left _ (mem_within.mpr ⟨sub,si⟩)
        · obtain ⟨w,hw,hwn⟩ := not_subset.mp sub
          exact mem_union_right _ (mem_biUnion.mpr
            ⟨w,mem_sdiff.mpr ⟨su hw,hwn⟩,mem_filter.mpr ⟨ht,hw⟩⟩)
      have union_le : (W.biUnion hits).card ≤ W.card * (subsetsWithin G N).card :=
        card_biUnion_le_card_mul _ _ _ (fun w hw => (best w (mem_sdiff.mp hw).1).trans hv_le)
      have total := (card_le_card cover).trans (card_union_le _ _)
      refine ⟨(W.card+1)::L,?_,by simp [ll],?_,?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hm
        · omega
        · exact lp p hm
      · have wo : W.card = U.card-N.card := card_sdiff_of_subset subNU
        have no := card_le_card subNU
        simp [ls]; omega
      · simp only [List.prod_cons]
        change H.card ≤ _
        nlinarith [Nat.mul_le_mul_left W.card lb]
    · have emp := not_nonempty_iff_eq_empty.mp nempty
      subst U
      refine ⟨List.replicate (r+1) 1,by simp,by simp,by simp,?_⟩
      simpa using empty_bound

private theorem maximal_outside {j : ℕ} {S : Finset V} (hS : G.IsIndepSet S) (hj : j < S.card) :
    (maximalLayer G j).card + 1 ≤ (subsetsWithin G (univ \ S)).card := by
  classical
  let F := subsetsWithin G (univ \ S)
  have inc : (maximalLayer G j).card ≤ (F.erase ∅).card := by
    apply card_le_card_of_injOn (fun t => t \ S) _ (diff_injective S hS)
    intro t ht
    apply mem_erase.mpr
    refine ⟨(diff_nonempty hS hj ht).ne_empty, mem_within.mpr ⟨?_,?_⟩⟩
    · intro v hv
      exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hv).2⟩
    · exact (mem_maximal.mp ht).1.isIndepSet.mono sdiff_subset
  have emp : ∅ ∈ F := mem_within.mpr ⟨empty_subset _,by simp [SimpleGraph.isIndepSet_iff]⟩
  have e := card_erase_add_one emp
  change _ ≤ F.card
  omega
private theorem shrink (L : List ℕ) (h : ∀ p ∈ L, 0<p) : L.prod=1 ∨
    ∃ R : List ℕ, (∀ p ∈ R, 0<p) ∧ R.length=L.length ∧ R.sum+1=L.sum ∧ L.prod≤2*R.prod := by
  by_cases one : ∀ p ∈ L, p=1
  · exact Or.inl (List.prod_eq_one one)
  push Not at one
  obtain ⟨p,hp,np⟩ := one
  have pos := h _ hp
  let Q := L.erase p
  have pe : L.Perm (p::Q) := List.perm_cons_erase hp
  refine Or.inr ⟨(p-1)::Q,?_,?_,?_,?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · omega
    · exact h a (pe.mem_iff.mpr (by simp [hm]))
  · simpa using pe.length_eq.symm
  · have e := pe.sum_eq
    simp at e ⊢; omega
  · have e := pe.prod_eq
    simp at e ⊢
    have t : p≤2*(p-1) := by omega
    nlinarith [Nat.mul_le_mul_right Q.prod t]

private theorem ratio (n : ℕ) (hn : 3≤n) (card : Fintype.card V=n) (j : ℕ)
    (hj : j<G.indepNum) : (layer G j).card ≤ bound n*(layer G (j+1)).card := by
  classical
  obtain ⟨S,it⟩ := G.exists_isNIndepSet_indepNum
  let O := univ \ S
  have hO : O.card = n-S.card := by simp [O,card_sdiff_of_subset,card]
  have sc : S.card ≤ n := by simpa [card] using card_le_univ S
  have hl : j<S.card := it.card_eq ▸ hj
  let A := (layer G (j+1)).card
  have ch := choose_le_layer S it.isIndepSet (j+1)
  change S.card.choose (j+1) ≤ A at ch
  have pos : 0<A := (Nat.choose_pos (by omega)).trans_le ch
  have m := maximal_outside it.isIndepSet hl
  change _ ≤ (subsetsWithin G O).card at m
  have hbase := consecutive G j
  change (layer G j).card ≤ A*(j+1)+(maximalLayer G j).card at hbase
  change (layer G j).card ≤ bound n*A
  by_cases hA : 2≤A
  · obtain ⟨L,lp,ll,ls,lb⟩ := independent_product S.card O (fun t ht =>
      it.card_eq ▸ (mem_within.mp ht).2.card_le_indepNum)
    rcases shrink L lp with prod | ⟨R,rp,rl,rs,rh⟩
    · have nb : n ≤ bound n := by
        have v := partition_bound n hn (List.replicate (n-1) 1) (by simp) (by simp)
        simp at v
        omega
      have v := Nat.mul_le_mul_left A (show j+1≤bound n by omega)
      rw [prod] at lb
      nlinarith
    · have s : R.sum=n-1 := by omega
      have b := partition_bound n hn R rp s
      have hlen : j+1≤R.length := by omega
      have one := Nat.mul_le_mul_left A hlen
      have two := Nat.mul_le_mul_right R.prod hA
      have total := Nat.mul_le_mul_right A b
      nlinarith
  · have eq : A=1 := by omega
    have last : j+1=S.card := by
      by_contra ne
      have nz := Nat.choose_pos (show j+1≤S.card by omega)
      have p : S.card.choose (j+1)=1 := by omega
      rcases Nat.choose_eq_one_iff.mp p with q | q <;> omega
    have hO' : ∀ t ∈ subsetsWithin G O, t.card ≤ S.card-1 := by
      intro t ht
      obtain ⟨hs,hi⟩ := mem_within.mp ht
      have le := hi.card_le_indepNum
      rw [← it.card_eq] at le
      by_contra! fail
      have equal : t.card=S.card := by omega
      have ht' : t ∈ layer G (j+1) := mem_layer.mpr ⟨hi,by omega⟩
      have hs' : S ∈ layer G (j+1) := mem_layer.mpr ⟨it.isIndepSet,last.symm⟩
      have singleton : (layer G (j+1)).card≤1 := eq.le
      have e := card_le_one.mp singleton t ht' S hs'
      obtain ⟨v,hv⟩ : S.Nonempty := card_pos.mp (by omega)
      exact (mem_sdiff.mp (hs (e ▸ hv))).2 hv
    obtain ⟨L,lp,ll,ls,lb⟩ := independent_product (S.card-1) O hO'
    have s : L.sum = n-1 := by omega
    have b := partition_bound n hn L lp s
    rw [eq,Nat.one_mul] at hbase
    rw [eq,Nat.mul_one]
    omega

public theorem resolution : Conjecture := by
  intro n hn G z hz
  classical
  obtain ⟨S,it⟩ := G.exists_isNIndepSet_indepNum
  have rb : 0 < bound n := by
    have v := partition_bound n hn (List.replicate (n-1) 1) (by simp) (by simp)
    simpa using lt_of_lt_of_le (by simp) v
  apply root_bound (fun j => (layer G j).card) (bound n) G.indepNum rb
      (card_pos.mpr ⟨S,mem_layer.mpr it⟩) _ z hz
  intro j hj
  exact ratio n hn (Fintype.card_fin _) j hj

/-- info: 'BrownCameronGraphModulus.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BrownCameronGraphModulus
