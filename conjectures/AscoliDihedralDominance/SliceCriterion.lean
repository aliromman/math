module

public import conjectures.AscoliDihedralDominance.Gain
public import conjectures.AscoliDihedralDominance.SignedMoments

@[expose] public section
namespace AscoliDihedral
open Finset
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def good (dis : G→Finset (Finset G)) (g : G) := missingQuotients g \ dis g

def bad (dis : G→Finset (Finset G)) (g : G) := missingProducts g \ dis g

def pairFamily (dis : G→Finset (Finset G)) (gh : G×G) :=
  if gh.1=gh.2 then good dis gh.1 else missingQuotients gh.1 ∩ missingQuotients gh.2

def atLabel (T : Finset G) (R : G→Finset (Finset G)) (A : Finset G) :=
  T.filter fun g => A∈R g

omit [Group G] in
private theorem at_sdiff (S T : G→Finset (Finset G)) (A : Finset G) :
    atLabel univ (fun g => S g \ T g) A = atLabel univ S A \ atLabel univ T A := by
  ext; simp [atLabel]

omit [Group G] in
private theorem at_subset {R T : G→Finset (Finset G)} (hs : ∀g,R g ⊆ T g) (A : Finset G) :
    atLabel univ R A ⊆ atLabel univ T A := by
  intro g hg
  exact mem_filter.mpr ⟨mem_univ _,hs g (mem_filter.mp hg).2⟩

private theorem trimmed_cmp (dis : G→Finset (Finset G))
    (hd : ∀ g, dis g ⊆ missingQuotients g ∩ missingProducts g) (A : Finset G) :
    let q := (atLabel univ (good dis) A).card
    let p := (atLabel univ (bad dis) A).card
    (p<q ↔ (quotients A).card < (products A).card) ∧ (q<p ↔ (products A).card < (quotients A).card) := by
  have hp := at_subset (fun g => (hd g).trans inter_subset_right) A
  have hq := at_subset (fun g => (hd g).trans inter_subset_left) A
  have pbase : atLabel univ missingProducts A = (products A)ᶜ := by ext; simp [atLabel,missingProducts]
  have qbase : atLabel univ missingQuotients A = (quotients A)ᶜ := by ext; simp [atLabel,missingQuotients]
  have hpC := card_le_card hp
  have hqC := card_le_card hq
  have cq : (atLabel univ (good dis) A).card =
      (Fintype.card G - (quotients A).card) - (atLabel univ dis A).card := by
    change (atLabel univ (fun g => missingQuotients g \ dis g) A).card = _
    rw [at_sdiff,card_sdiff_of_subset hq,qbase,card_compl]
  have cp : (atLabel univ (bad dis) A).card =
      (Fintype.card G - (products A).card) - (atLabel univ dis A).card := by
    change (atLabel univ (fun g => missingProducts g \ dis g) A).card = _
    rw [at_sdiff,card_sdiff_of_subset hp,pbase,card_compl]
  simp only [cq,cp]
  rw [pbase,card_compl] at hpC
  rw [qbase,card_compl] at hqC
  have p := card_le_univ (products A)
  have q := card_le_univ (quotients A)
  omega

omit [Group G] in
private theorem slice_stratum (R : Finset (Finset G)) (m : ℕ) :
    R ∩ univ.powersetCard m = slice R m := by
  ext A; simp [slice]

def packBase (N : ℕ) := (N+1)^2 * 2^N + 1

omit [Group G] [DecidableEq G] in
private theorem base_ok (T : Finset G) : T.card * 2^(Fintype.card G) < packBase (Fintype.card G) := by
  have h := card_le_univ T
  unfold packBase
  apply Nat.lt_succ_of_le
  apply Nat.mul_le_mul_right
  nlinarith

omit [Group G] [DecidableEq G] in
private theorem base_pairs (T : Finset G) :
    (T×ˢT).card * 2^(Fintype.card G) < packBase (Fintype.card G) := by
  rw [card_product]
  have h := card_le_univ T
  unfold packBase
  apply Nat.lt_succ_of_le
  apply Nat.mul_le_mul_right
  exact (Nat.mul_le_mul h h).trans (by nlinarith)

theorem slice_bound (dis : G→Finset (Finset G)) (hd : ∀g, dis g ⊆ missingQuotients g ∩ missingProducts g)
    (m : ℕ) (hm : m≤Fintype.card G) :
    let T := involutions G
    let B := packBase (Fintype.card G)
    momentLower ((Fintype.card G).choose m)
      (digit B m (∑ g∈T, familyWeight B (good dis g)))
      (digit B m (∑ gh∈T×ˢT, familyWeight B (pairFamily dis gh)))
      (digit B m (∑ g : G, familyWeight B (bad dis g))) ≤ gainAt G m := by
  let S := (univ : Finset G).powersetCard m
  let T := involutions G
  let q A := (atLabel univ (good dis) A).card
  let p A := (atLabel univ (bad dis) A).card
  let w A := (atLabel T (good dis) A).card
  dsimp only
  rw [packed_digit _ T _ m hm (base_ok T),packed_digit _ _ _ m hm (base_pairs T),
    packed_digit _ _ _ m hm (base_ok univ)]
  have hw (A : Finset G) (_ : A∈S) : w A≤q A := by
    apply card_le_card
    exact filter_subset_filter _ (subset_univ _)
  have hW : (∑ A∈S,w A) = ∑ g∈T,(slice (good dis g) m).card := by
    change (∑ A∈S,(T.filter _).card) = _
    rw [incidence_on]
    simp only [S,slice_stratum]
  have hP : (∑ A∈S,p A) = ∑ g : G,(slice (bad dis g) m).card := by
    change (∑ A∈S,(univ.filter _).card) = _
    rw [incidence_on]
    simp only [S,slice_stratum]
  have hD : (∑ A∈S,w A^2) ≤ ∑ gh∈T×ˢT,(slice (pairFamily dis gh) m).card := by
    change (∑ A∈S,(T.filter _).card^2) ≤ _
    rw [pair_incidence_on,sum_product]
    apply sum_le_sum
    intro g _
    apply sum_le_sum
    intro h _
    apply card_le_card
    rw [←slice_stratum]
    apply inter_subset_inter_right
    by_cases he : g=h
    · subst h
      simp [pairFamily]
    · simp only [pairFamily,he,ite_false]
      exact inter_subset_inter sdiff_subset sdiff_subset
  have L := signed_lower S p q w hw _ hD
  rw [hW,hP] at L
  have hcard : S.card=(Fintype.card G).choose m := by simp [S]
  rw [hcard] at L
  have hpq (A : Finset G) : p A<q A ↔ (quotients A).card < (products A).card := (trimmed_cmp dis hd A).1
  have hqp (A : Finset G) : q A<p A ↔ (products A).card < (quotients A).card := (trimmed_cmp dis hd A).2
  simpa only [hpq,hqp,gainAt,S] using L

theorem dominance_from_gains (h : 0 < ∑ m∈range (Fintype.card G+1), gainAt G m) : ProductDominant G := by
  have parts (R : Finset G→Prop) [DecidablePred R] :
      (∑ m∈range (Fintype.card G+1), ((univ.powersetCard m).filter R).card) = (univ.filter R).card := by
    let T : Finset (Finset G) := univ.filter R
    have H := sum_fiberwise_of_maps_to' (s := T) (t := range (Fintype.card G+1)) (g := Finset.card)
      (fun A _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ A))) (fun _ => (1:ℕ))
    simp only [sum_const,smul_eq_mul,mul_one] at H
    convert H using 2 with m
    congr 1
    ext; simp [T,and_comm]
  unfold gainAt at h
  rw [sum_sub_distrib,←Nat.cast_sum,←Nat.cast_sum,parts,parts] at h
  unfold ProductDominant
  omega

end AscoliDihedral
