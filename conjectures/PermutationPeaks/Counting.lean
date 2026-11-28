module

public import conjectures.PermutationPeaks.PermutationOrders

/-! Definitions and lemmas from Alex Chengyu Li’s proof of coefficient concavity.
Adapted from the MIT-licensed archive, DOI 10.5281/zenodo.22661864. -/

@[expose] public section
namespace PermutationPeaks

namespace PeakPolynomials

noncomputable def constrainedBlockEquiv {a b : ℕ}
    (A : Equiv.Perm (Fin a) → Prop) (B : Equiv.Perm (Fin b) → Prop) :
    {π : Equiv.Perm (Fin (a+b)) // A (standardizedFirst π) ∧ B (standardizedSecond π)} ≃
      ValueChoice a b × {α : Equiv.Perm (Fin a) // A α} ×
        {β : Equiv.Perm (Fin b) // B β} where
  toFun π := ⟨(splitBlocks π.val).1, ⟨standardizedFirst π.val,π.property.1⟩,
    ⟨standardizedSecond π.val,π.property.2⟩⟩
  invFun d := ⟨assembleBlocks ⟨d.1,d.2.1.val,d.2.2.val⟩,by
    have h := split_assemble (a:=a) (b:=b) ⟨d.1,d.2.1.val,d.2.2.val⟩
    have hA := congrArg (fun z : BlockData a b => z.2.1) h
    have hB := congrArg (fun z : BlockData a b => z.2.2) h
    change standardizedFirst _ = d.2.1.val at hA
    change standardizedSecond _ = d.2.2.val at hB
    exact ⟨hA.symm ▸ d.2.1.property,hB.symm ▸ d.2.2.property⟩⟩
  left_inv π := by
    apply Subtype.ext
    exact assemble_split π.val
  right_inv d := by
    dsimp only
    have h := split_assemble (a:=a) (b:=b) ⟨d.1,d.2.1.val,d.2.2.val⟩
    apply Prod.ext
    · exact congrArg (fun z : BlockData a b => z.1) h
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z : BlockData a b => z.2.1) h
      · apply Subtype.ext
        exact congrArg (fun z : BlockData a b => z.2.2) h

theorem constrained_block_count {a b : ℕ}
    (A : Equiv.Perm (Fin a) → Prop) (B : Equiv.Perm (Fin b) → Prop)
    [DecidablePred A] [DecidablePred B] :
    Fintype.card {π : Equiv.Perm (Fin (a+b)) //
      A (standardizedFirst π) ∧ B (standardizedSecond π)} =
      (a+b).choose a * Fintype.card {α : Equiv.Perm (Fin a) // A α} *
        Fintype.card {β : Equiv.Perm (Fin b) // B β} := by
  rw [Fintype.card_congr (constrainedBlockEquiv A B)]
  simp only [Fintype.card_prod,valueChoice_card]
  exact (Nat.mul_assoc _ _ _).symm

end PeakPolynomials
namespace PeakPolynomials

theorem fromFin_value {n : ℕ} (π : Equiv.Perm (Fin n)) (j : ℕ) (hj : j<n) :
    valueAt (fromFinPermutation π) (j+1) = (π ⟨j,hj⟩).val+1 := by
  have h : j+1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  simp [valueAt,h,fromFinPermutation,positionFin]

def TriplePeak {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) (hi : i+2<n) : Prop :=
  π ⟨i,by omega⟩ < π ⟨i+1,by omega⟩ ∧ π ⟨i+2,hi⟩ < π ⟨i+1,by omega⟩

theorem triplePeak_literal {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) (hi : i+2<n) :
    IsPeak (fromFinPermutation π) (i+2) ↔ TriplePeak π i hi := by
  unfold IsPeak TriplePeak
  have hsub : i+2-1=i+1 := by omega
  rw [hsub,fromFin_value π i (by omega),fromFin_value π (i+1) (by omega),
    fromFin_value π (i+2) hi]
  simp only [Fin.lt_def,Nat.add_lt_add_iff_right]
  omega

theorem first_triplePeak {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (hi : i+2<a) :
    TriplePeak (standardizedFirst π) i hi ↔ TriplePeak π i (by omega) := by
  unfold TriplePeak
  rw [first_comparison_preserved,first_comparison_preserved]
  rfl

theorem second_triplePeak {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (hi : i+2<b) :
    TriplePeak (standardizedSecond π) i hi ↔ TriplePeak π (a+i) (by omega) := by
  unfold TriplePeak
  rw [second_comparison_preserved,second_comparison_preserved]
  simp only [Nat.add_assoc]
  rfl

theorem first_peak_preserved {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (hi : i+2<a) :
    IsPeak (fromFinPermutation (standardizedFirst π)) (i+2) ↔
      IsPeak (fromFinPermutation π) (i+2) := by
  rw [triplePeak_literal _ _ hi,triplePeak_literal _ _ (by omega),first_triplePeak]

theorem second_peak_preserved {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (hi : i+2<b) :
    IsPeak (fromFinPermutation (standardizedSecond π)) (i+2) ↔
      IsPeak (fromFinPermutation π) (a+(i+2)) := by
  rw [triplePeak_literal _ _ hi,← Nat.add_assoc,
    triplePeak_literal _ _ (by omega),second_triplePeak]

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem first_peak_at {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (h2 : 2 ≤ i) (hi : i<a) :
    IsPeak (fromFinPermutation (standardizedFirst π)) i ↔
      IsPeak (fromFinPermutation π) i := by
  have h := first_peak_preserved π (i-2) (by omega)
  have he : i-2+2=i := by omega
  simpa only [he] using h

theorem second_peak_at {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (i : ℕ) (h2 : 2 ≤ i) (hi : i<b) :
    IsPeak (fromFinPermutation (standardizedSecond π)) i ↔
      IsPeak (fromFinPermutation π) (a+i) := by
  have h := second_peak_preserved π (i-2) (by omega)
  have he : i-2+2=i := by omega
  simpa only [he] using h

theorem block_peak_partition {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (T : Finset ℕ)
    (hfirst : peaks (fromFinPermutation (standardizedFirst π))=T)
    (hsecond : peaks (fromFinPermutation (standardizedSecond π))=∅) :
    peaks (fromFinPermutation π) = T ∪ (peaks (fromFinPermutation π) ∩ {a,a+1}) := by
  ext i
  constructor
  · intro hi
    have hp := (mem_peaks _ _).mp hi
    by_cases hia : i<a
    · apply mem_union.mpr; left
      rw [← hfirst,mem_peaks]
      exact (first_peak_at π i hp.1 hia).mpr hp
    · by_cases hj : i=a ∨ i=a+1
      · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hi,by simpa using hj⟩))
      · have h2 : 2 ≤ i-a := by omega
        have hb : i-a<b := by have := hp.2.1; omega
        have hshift : a+(i-a)=i := by omega
        have hs : IsPeak (fromFinPermutation (standardizedSecond π)) (i-a) := by
          apply (second_peak_at π (i-a) h2 hb).mpr
          simpa only [hshift] using hp
        have hem := (mem_peaks _ _).mpr hs
        rw [hsecond] at hem
        simp at hem
  · intro hi
    rcases mem_union.mp hi with ht | hj
    · rw [← hfirst,mem_peaks] at ht
      exact (mem_peaks _ _).mpr ((first_peak_at π i ht.1 ht.2.1).mp ht)
    · exact (mem_inter.mp hj).1

theorem join_three_alternatives {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (T : Finset ℕ)
    (hfirst : peaks (fromFinPermutation (standardizedFirst π))=T)
    (hsecond : peaks (fromFinPermutation (standardizedSecond π))=∅) :
    peaks (fromFinPermutation π)=T ∨
      peaks (fromFinPermutation π)=insert a T ∨
      peaks (fromFinPermutation π)=insert (a+1) T := by
  have hpart := block_peak_partition π T hfirst hsecond
  let P := peaks (fromFinPermutation π)
  have hsep : ∀ i ∈ P, i+1 ∉ P := (peaks_admissible _).2
  by_cases ha : a∈P
  · have hb : a+1∉P := hsep a ha
    right; left
    rw [hpart]
    ext i
    simp only [mem_union,mem_inter,mem_insert,mem_singleton]
    constructor
    · rintro (ht | ⟨hp,he | he⟩)
      · exact Or.inr ht
      · exact Or.inl he
      · subst i; exact False.elim (hb hp)
    · rintro (rfl | ht)
      · exact Or.inr ⟨ha,Or.inl rfl⟩
      · exact Or.inl ht
  · by_cases hb : a+1∈P
    · right; right
      rw [hpart]
      ext i
      simp only [mem_union,mem_inter,mem_insert,mem_singleton]
      constructor
      · rintro (ht | ⟨hp,he | he⟩)
        · exact Or.inr ht
        · subst i; exact False.elim (ha hp)
        · exact Or.inl he
      · rintro (rfl | ht)
        · exact Or.inr ⟨hb,Or.inr rfl⟩
        · exact Or.inl ht
    · left
      rw [hpart]
      ext i
      simp only [mem_union,mem_inter,mem_insert,mem_singleton]
      constructor
      · rintro (ht | ⟨hp,he | he⟩)
        · exact ht
        · subst i; exact False.elim (ha hp)
        · subst i; exact False.elim (hb hp)
      · exact Or.inl

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem blocks_of_peak_containment {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (T : Finset ℕ) (hT : ∀ i ∈ T, 2 ≤ i ∧ i<a)
    (hlo : T ⊆ peaks (fromFinPermutation π))
    (hhi : peaks (fromFinPermutation π) ⊆ T ∪ {a,a+1}) :
    peaks (fromFinPermutation (standardizedFirst π))=T ∧
      peaks (fromFinPermutation (standardizedSecond π))=∅ := by
  constructor
  · ext i
    constructor
    · intro hi
      have hp := (mem_peaks _ _).mp hi
      have hg := (mem_peaks _ _).mpr ((first_peak_at π i hp.1 hp.2.1).mp hp)
      rcases mem_union.mp (hhi hg) with ht | hj
      · exact ht
      · simp only [mem_insert,mem_singleton] at hj
        have := hp.2.1
        omega
    · intro hi
      have ht := hT i hi
      exact (mem_peaks _ _).mpr ((first_peak_at π i ht.1 ht.2).mpr
        ((mem_peaks _ _).mp (hlo hi)))
  · apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hp := (mem_peaks _ _).mp hi
    have hg := (mem_peaks _ _).mpr ((second_peak_at π i hp.1 hp.2.1).mp hp)
    rcases mem_union.mp (hhi hg) with ht | hj
    · have := (hT (a+i) ht).2
      omega
    · simp only [mem_insert,mem_singleton] at hj
      have := hp.1
      omega

theorem block_condition_iff_three {a b : ℕ} (π : Equiv.Perm (Fin (a+b)))
    (T : Finset ℕ) (hT : ∀ i ∈ T, 2 ≤ i ∧ i<a) :
    (peaks (fromFinPermutation (standardizedFirst π))=T ∧
      peaks (fromFinPermutation (standardizedSecond π))=∅) ↔
    (peaks (fromFinPermutation π)=T ∨
      peaks (fromFinPermutation π)=insert a T ∨
      peaks (fromFinPermutation π)=insert (a+1) T) := by
  constructor
  · rintro ⟨hf,hs⟩
    exact join_three_alternatives π T hf hs
  · intro h
    apply blocks_of_peak_containment π T hT
    · rcases h with h | h | h <;> rw [h]
      · exact subset_insert _ _
      · exact subset_insert _ _
    · rcases h with h | h | h <;> rw [h]
      · exact subset_union_left
      · intro i hi
        rcases mem_insert.mp hi with rfl | ht
        · simp
        · exact mem_union.mpr (Or.inl ht)
      · intro i hi
        rcases mem_insert.mp hi with rfl | ht
        · simp
        · exact mem_union.mpr (Or.inl ht)

end PeakPolynomials
namespace PeakPolynomials
open Finset

def literalPermutationEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ Permutation n where
  toFun := fromFinPermutation
  invFun := finPermutation
  left_inv π := by ext i; simp [fromFinPermutation,finPermutation]
  right_inv := finPermutation_roundtrip

theorem fin_peak_count (n : ℕ) (S : Finset ℕ) :
    Fintype.card {π : Equiv.Perm (Fin n) // peaks (fromFinPermutation π)=S} =
      peakCount n S := by
  let e : {π : Equiv.Perm (Fin n) // peaks (fromFinPermutation π)=S} ≃
      {π : Permutation n // peaks π=S} :=
    (literalPermutationEquiv n).subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr e,Fintype.card_subtype]
  rfl

theorem three_fiber_count {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (x y z : β) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    Fintype.card {t : α // f t=x ∨ f t=y ∨ f t=z} =
      Fintype.card {t : α // f t=x} + Fintype.card {t : α // f t=y} +
        Fintype.card {t : α // f t=z} := by
  classical
  simp only [Fintype.card_subtype,filter_or]
  have h1 : Disjoint (univ.filter (fun t => f t=x))
      (univ.filter (fun t => f t=y) ∪ univ.filter (fun t => f t=z)) := by
    simp only [disjoint_left,mem_filter,mem_univ,true_and,mem_union]
    rintro t hx (hy | hz)
    · exact hxy (hx.symm.trans hy)
    · exact hxz (hx.symm.trans hz)
  have h2 : Disjoint (univ.filter (fun t => f t=y)) (univ.filter (fun t => f t=z)) := by
    simp only [disjoint_left,mem_filter,mem_univ,true_and]
    intro t hy hz
    exact hyz (hy.symm.trans hz)
  rw [card_union_of_disjoint h1,card_union_of_disjoint h2,Nat.add_assoc]

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem literal_block_counting_recurrence (a b : ℕ) (T : Finset ℕ)
    (hT : ∀ i ∈ T, 2 ≤ i ∧ i<a) :
    peakCount (a+b) T + peakCount (a+b) (insert a T) +
      peakCount (a+b) (insert (a+1) T) =
      (a+b).choose a * peakCount a T * peakCount b ∅ := by
  classical
  have ha : a ∉ T := by intro h; have := (hT a h).2; omega
  have hb : a+1 ∉ T := by intro h; have := (hT (a+1) h).2; omega
  have hxy : T ≠ insert a T := by
    intro h
    exact ha (h ▸ mem_insert_self a T)
  have hxz : T ≠ insert (a+1) T := by
    intro h
    exact hb (h ▸ mem_insert_self (a+1) T)
  have hyz : insert a T ≠ insert (a+1) T := by
    intro h
    have hh : a ∈ insert (a+1) T := h ▸ mem_insert_self a T
    simp only [mem_insert] at hh
    rcases hh with hh | hh
    · omega
    · exact ha hh
  let e := Equiv.subtypeEquivRight (fun π : Equiv.Perm (Fin (a+b)) =>
    block_condition_iff_three π T hT)
  have hc := Fintype.card_congr e
  have ht := three_fiber_count (fun π : Equiv.Perm (Fin (a+b)) =>
    peaks (fromFinPermutation π)) T (insert a T) (insert (a+1) T) hxy hxz hyz
  have hbcount := constrained_block_count (a:=a) (b:=b)
    (fun π => peaks (fromFinPermutation π)=T)
    (fun π => peaks (fromFinPermutation π)=∅)
  rw [fin_peak_count,fin_peak_count,fin_peak_count] at ht
  rw [fin_peak_count,fin_peak_count] at hbcount
  exact ht.symm.trans (hc.symm.trans hbcount)

end PeakPolynomials
namespace PeakPolynomials

def finValue {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if hi : i<n then (π ⟨i,hi⟩).val else n

theorem finValue_injective {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j : ℕ} (hi : i<n) (hj : j<n) (h : finValue π i=finValue π j) : i=j := by
  simp only [finValue,dite_eq_left hi,dite_eq_left hj] at h
  exact congrArg Fin.val (π.injective (Fin.ext h))

theorem no_peak_turn {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : peaks (fromFinPermutation π)=∅) (i : ℕ) (hi : i+2<n) :
    ¬ (finValue π i < finValue π (i+1) ∧ finValue π (i+2)<finValue π (i+1)) := by
  intro ht
  have ht' : TriplePeak π i hi := by
    simpa only [TriplePeak,Fin.lt_def,finValue,dite_eq_left hi,
      dite_eq_left (show i<n by omega),dite_eq_left (show i+1<n by omega)] using ht
  have hp := (mem_peaks _ _).mpr ((triplePeak_literal π i hi).mpr ht')
  rw [h] at hp
  simp at hp

theorem peak_free_ascent_chain {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : peaks (fromFinPermutation π)=∅) (i : ℕ)
    (ha : finValue π i<finValue π (i+1)) (t : ℕ) (ht : i+t+1<n) :
    finValue π (i+t)<finValue π (i+t+1) := by
  induction t with
  | zero => simpa using ha
  | succ t ih =>
    have hprev := ih (by omega)
    have hturn := no_peak_turn π h (i+t) (by omega)
    have hne : finValue π (i+t+2)≠finValue π (i+t+1) := by
      intro he
      have := finValue_injective π (by omega) (by omega) he
      omega
    have hinc : finValue π (i+t+1)<finValue π (i+t+2) := by omega
    exact hinc

theorem peak_free_valley {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : peaks (fromFinPermutation π)=∅) (k : ℕ) (hk : k<n)
    (hmin : finValue π k=0) :
    (∀ i, i<k → finValue π (i+1)<finValue π i) ∧
    (∀ i, k ≤ i → i+1<n → finValue π i<finValue π (i+1)) := by
  constructor
  · intro i hi
    by_contra hn
    have hne : finValue π i≠finValue π (i+1) := by
      intro he
      have := finValue_injective π (by omega) (by omega) he
      omega
    have ha : finValue π i<finValue π (i+1) := by omega
    have hc := peak_free_ascent_chain π h i ha (k-i-1) (by omega)
    have he : i+(k-i-1)+1=k := by omega
    rw [he,hmin] at hc
    omega
  · intro i hi hin
    have hnz : finValue π (k+1)≠0 := by
      intro he
      have heq : finValue π (k+1)=finValue π k := he.trans hmin.symm
      have := finValue_injective π (by omega) hk heq
      omega
    have ha : finValue π k<finValue π (k+1) := by omega
    have hc := peak_free_ascent_chain π h k ha (i-k) (by omega)
    have he : k+(i-k)=i := by omega
    simpa only [he] using hc

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem subset_total {n : ℕ} (S : Finset (Fin n)) : S.card+Sᶜ.card=n := by
  simp

noncomputable def valleyPermutation {n : ℕ} (S : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (finCongr (subset_total S).symm).trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr
        (Fin.revPerm.trans (S.orderIsoOfFin rfl).toEquiv)
        (Sᶜ.orderIsoOfFin rfl).toEquiv).trans (subsetGlue S)))

theorem valleyPermutation_left {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    valleyPermutation S ⟨i.val,by have := subset_total S; have := i.isLt; omega⟩ =
      (S.orderIsoOfFin rfl i.rev).val := by
  have he : (finCongr (subset_total S).symm)
      ⟨i.val,by have := subset_total S; have := i.isLt; omega⟩ = Fin.castAdd Sᶜ.card i := rfl
  simp only [valleyPermutation,Equiv.trans_apply,he,finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem valleyPermutation_right {n : ℕ} (S : Finset (Fin n)) (i : Fin Sᶜ.card) :
    valleyPermutation S ⟨S.card+i.val,by have := subset_total S; have := i.isLt; omega⟩ =
      (Sᶜ.orderIsoOfFin rfl i).val := by
  have he : (finCongr (subset_total S).symm)
      ⟨S.card+i.val,by have := subset_total S; have := i.isLt; omega⟩ = Fin.natAdd S.card i := rfl
  simp only [valleyPermutation,Equiv.trans_apply,he,finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem valley_left_decreasing {n : ℕ} (S : Finset (Fin n))
    (i j : Fin S.card) (hij : i<j) :
    valleyPermutation S ⟨j.val,by have := subset_total S; have := j.isLt; omega⟩ <
      valleyPermutation S ⟨i.val,by have := subset_total S; have := i.isLt; omega⟩ := by
  rw [valleyPermutation_left,valleyPermutation_left]
  exact (S.orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hij)

theorem valley_right_increasing {n : ℕ} (S : Finset (Fin n))
    (i j : Fin Sᶜ.card) (hij : i<j) :
    valleyPermutation S ⟨S.card+i.val,by have := subset_total S; have := i.isLt; omega⟩ <
      valleyPermutation S ⟨S.card+j.val,by have := subset_total S; have := j.isLt; omega⟩ := by
  rw [valleyPermutation_right,valleyPermutation_right]
  exact (Sᶜ.orderIsoOfFin rfl).strictMono hij

end PeakPolynomials
namespace PeakPolynomials
open Finset

theorem valley_complement_min {n : ℕ} (S : Finset (Fin (n+1))) (hS : 0 ∉ S) :
    ∃ hpos : 0<Sᶜ.card, (Sᶜ.orderIsoOfFin rfl ⟨0,hpos⟩).val=0 := by
  have hmem : (0 : Fin (n+1)) ∈ Sᶜ := mem_compl.mpr hS
  have hpos : 0<Sᶜ.card := card_pos.mpr ⟨0,hmem⟩
  refine ⟨hpos,?_⟩
  have hle := (Sᶜ.orderIsoOfFin rfl).monotone
    (show (⟨0,hpos⟩ : Fin Sᶜ.card) ≤ (Sᶜ.orderIsoOfFin rfl).symm ⟨0,hmem⟩ from Nat.zero_le _)
  have hv : (Sᶜ.orderIsoOfFin rfl ⟨0,hpos⟩).val ≤ (0 : Fin (n+1)) := by
    exact (show (Sᶜ.orderIsoOfFin rfl ⟨0,hpos⟩) ≤ ⟨0,hmem⟩ by simpa only [OrderIso.apply_symm_apply] using hle)
  exact le_antisymm hv (Fin.zero_le _)

theorem valley_constructed_min {n : ℕ} (S : Finset (Fin (n+1))) (hS : 0 ∉ S) :
    S.card<n+1 ∧ finValue (valleyPermutation S) S.card=0 := by
  obtain ⟨hpos,hmin⟩ := valley_complement_min S hS
  have hk : S.card<n+1 := by have := subset_total S; omega
  refine ⟨hk,?_⟩
  unfold finValue
  rw [dite_eq_left hk]
  have hv := valleyPermutation_right S ⟨0,hpos⟩
  simp only [Nat.add_zero] at hv
  rw [hv,hmin]
  rfl

theorem valley_constructed_no_peaks {n : ℕ} (S : Finset (Fin (n+1))) (hS : 0 ∉ S) :
    peaks (fromFinPermutation (valleyPermutation S))=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpeak := (mem_peaks _ _).mp hp
  have h2 := hpeak.1
  have hn := hpeak.2.1
  have he : p-2+2=p := by omega
  have ht := (triplePeak_literal (valleyPermutation S) (p-2) (by omega)).mp
    (by simpa only [he] using hpeak)
  change _ < _ ∧ _ < _ at ht
  by_cases hleft : p-1<S.card
  · have hd := valley_left_decreasing S
      ⟨p-2,by omega⟩ ⟨p-1,hleft⟩ (by change p-2<p-1; omega)
    have hm : p-2+1=p-1 := by omega
    simp only [hm] at ht
    exact lt_asymm ht.1 hd
  · by_cases hmid : p-1=S.card
    · have hmin := (valley_constructed_min S hS).2
      have hk := (valley_constructed_min S hS).1
      simp only [finValue,dite_eq_left hk] at hmin
      have hm : p-2+1=S.card := by omega
      have htval := ht.1
      change (_ : Fin (n+1)).val < (valleyPermutation S ⟨p-2+1,by omega⟩).val at htval
      simp only [hm,hmin] at htval
      omega
    · have hi : S.card ≤ p-1 := by omega
      have htcard := subset_total S
      have hd := valley_right_increasing S
        ⟨p-1-S.card,by omega⟩ ⟨p-S.card,by omega⟩ (by change p-1-S.card<p-S.card; omega)
      have he1 : S.card+(p-1-S.card)=p-2+1 := by omega
      have he2 : S.card+(p-S.card)=p-2+2 := by omega
      simp only [he1,he2] at hd
      exact lt_asymm ht.2 hd

end PeakPolynomials
namespace PeakPolynomials
open Finset

def leftOfMinimum {n : ℕ} (π : Equiv.Perm (Fin (n+1))) : Finset (Fin (n+1)) :=
  univ.filter (fun x => (π.symm x).val < (π.symm 0).val)

@[simp] theorem mem_leftOfMinimum {n : ℕ} (π : Equiv.Perm (Fin (n+1))) (x : Fin (n+1)) :
    x ∈ leftOfMinimum π ↔ (π.symm x).val < (π.symm 0).val := by simp [leftOfMinimum]

theorem zero_not_leftOfMinimum {n : ℕ} (π : Equiv.Perm (Fin (n+1))) :
    0 ∉ leftOfMinimum π := by simp

theorem leftOfMinimum_card {n : ℕ} (π : Equiv.Perm (Fin (n+1))) :
    (leftOfMinimum π).card=(π.symm 0).val := by
  have he : leftOfMinimum π =
      (univ.filter (fun i : Fin (n+1) => i.val < (π.symm 0).val)).image π := by
    ext x
    simp only [mem_leftOfMinimum,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · intro h
      exact ⟨π.symm x,h,π.apply_symm_apply x⟩
    · rintro ⟨i,hi,rfl⟩
      simpa using hi
  rw [he,card_image_of_injective _ π.injective,Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt (π.symm 0).isLt)

theorem valley_minimum_position {n : ℕ} (S : Finset (Fin (n+1))) (hS : 0 ∉ S) :
    ((valleyPermutation S).symm 0).val=S.card := by
  obtain ⟨hk,hmin⟩ := valley_constructed_min S hS
  simp only [finValue,dite_eq_left hk] at hmin
  have hz : valleyPermutation S ⟨S.card,hk⟩=0 := Fin.ext hmin
  have hi := congrArg (valleyPermutation S).symm hz
  simp only [Equiv.symm_apply_apply] at hi
  exact (congrArg Fin.val hi).symm

theorem valley_left_set {n : ℕ} (S : Finset (Fin (n+1))) (hS : 0 ∉ S) :
    leftOfMinimum (valleyPermutation S)=S := by
  ext x
  rw [mem_leftOfMinimum,valley_minimum_position S hS]
  constructor
  · intro hi
    have hv := valleyPermutation_left S ⟨((valleyPermutation S).symm x).val,hi⟩
    have he : (⟨((valleyPermutation S).symm x).val,
      by have := subset_total S; omega⟩ : Fin (n+1)) = (valleyPermutation S).symm x := rfl
    rw [he,Equiv.apply_symm_apply] at hv
    rw [hv]
    exact (S.orderIsoOfFin rfl _).property
  · intro hx
    let j := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
    have hv := valleyPermutation_left S j.rev
    simp only [Fin.rev_rev] at hv
    have hj : (S.orderIsoOfFin rfl j).val=x := by simp [j]
    rw [hj] at hv
    have hi := congrArg (valleyPermutation S).symm hv
    simp only [Equiv.symm_apply_apply] at hi
    have hh := congrArg Fin.val hi
    rw [← hh]
    exact j.rev.isLt

end PeakPolynomials
namespace PeakPolynomials
open Finset

def prefixValues {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  univ.filter (fun x => (π.symm x).val<k)

@[simp] theorem mem_prefixValues {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (x : Fin n) :
    x ∈ prefixValues π k ↔ (π.symm x).val<k := by simp [prefixValues]

noncomputable def prefixValueEquiv {n : ℕ} (π : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) : Fin k ≃ ↥(prefixValues π k) :=
  Equiv.ofBijective (fun i => ⟨π ⟨i.val,lt_of_lt_of_le i.isLt hk⟩,by simp [i.isLt]⟩) (by
    constructor
    · intro i j h
      have hh := congrArg Fin.val (π.injective (congrArg Subtype.val h))
      exact Fin.ext hh
    · intro x
      have hx := (mem_prefixValues π k x.val).mp x.property
      refine ⟨⟨(π.symm x.val).val,hx⟩,Subtype.ext ?_⟩
      exact π.apply_symm_apply x.val)

theorem prefixValues_card {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (prefixValues π k).card=k := by
  have hc := Fintype.card_congr (prefixValueEquiv π k hk)
  simpa only [Fintype.card_fin,Fintype.card_coe] using hc.symm

theorem decreasing_prefix_rank {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (hanti : ∀ i j : Fin k, i<j →
      π ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ < π ⟨i.val,lt_of_lt_of_le i.isLt hk⟩)
    (i : Fin k) :
    π ⟨i.val,lt_of_lt_of_le i.isLt hk⟩ =
      ((prefixValues π k).orderIsoOfFin (prefixValues_card π k hk) i.rev).val := by
  let e := Fin.revPerm.trans (prefixValueEquiv π k hk)
  have hm : StrictMono e := by
    intro i j hij
    exact hanti j.rev i.rev (Fin.rev_lt_rev.mpr hij)
  let eo : Fin k ≃o ↥(prefixValues π k) := { e with map_rel_iff' := hm.le_iff_le }
  have he : eo=(prefixValues π k).orderIsoOfFin (prefixValues_card π k hk) := Subsingleton.elim _ _
  have hi := congrArg (fun f : Fin k ≃o ↥(prefixValues π k) => (f i.rev).val) he
  change π ⟨i.rev.rev.val,lt_of_lt_of_le i.rev.rev.isLt hk⟩ = _ at hi
  simpa only [Fin.rev_rev] using hi

end PeakPolynomials
namespace PeakPolynomials
open Finset

noncomputable def suffixValueEquiv {n : ℕ} (π : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k ≤ n) : Fin (n-k) ≃ ↥((prefixValues π k)ᶜ : Finset (Fin n)) :=
  Equiv.ofBijective (fun i => ⟨π ⟨k+i.val,by have := i.isLt; omega⟩,by
    rw [mem_compl,mem_prefixValues]
    simp only [Equiv.symm_apply_apply]
    omega⟩) (by
    constructor
    · intro i j h
      have hh := congrArg Fin.val (π.injective (congrArg Subtype.val h))
      apply Fin.ext
      change k+i.val=k+j.val at hh
      omega
    · intro x
      have hx : k ≤ (π.symm x.val).val := by
        have := mem_compl.mp x.property
        rw [mem_prefixValues] at this
        omega
      refine ⟨⟨(π.symm x.val).val-k,by have := (π.symm x.val).isLt; omega⟩,Subtype.ext ?_⟩
      have he : k+((π.symm x.val).val-k)=(π.symm x.val).val := by omega
      have hi : (⟨k+((π.symm x.val).val-k),by have := (π.symm x.val).isLt; omega⟩ : Fin n)=π.symm x.val := Fin.ext he
      dsimp only
      rw [hi]
      exact π.apply_symm_apply x.val)

theorem suffixValues_card {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ((prefixValues π k)ᶜ).card=n-k := by
  rw [card_compl,prefixValues_card π k hk,Fintype.card_fin]

theorem increasing_suffix_rank {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (hmono : ∀ i j : Fin (n-k), i<j →
      π ⟨k+i.val,by have := i.isLt; omega⟩ < π ⟨k+j.val,by have := j.isLt; omega⟩)
    (i : Fin (n-k)) :
    π ⟨k+i.val,by have := i.isLt; omega⟩ =
      (((prefixValues π k)ᶜ).orderIsoOfFin (suffixValues_card π k hk) i).val := by
  let e := suffixValueEquiv π k hk
  have hm : StrictMono e := hmono
  let eo : Fin (n-k) ≃o ↥((prefixValues π k)ᶜ : Finset (Fin n)) :=
    { e with map_rel_iff' := hm.le_iff_le }
  have he : eo=((prefixValues π k)ᶜ).orderIsoOfFin (suffixValues_card π k hk) := Subsingleton.elim _ _
  exact congrArg (fun f : Fin (n-k) ≃o ↥((prefixValues π k)ᶜ : Finset (Fin n)) => (f i).val) he

end PeakPolynomials
namespace PeakPolynomials

theorem fin_strictMono_from_adjacent {α : Type*} [Preorder α] {k : ℕ} (f : Fin k → α)
    (h : ∀ i j, i.val+1=j.val → f i<f j) : StrictMono f := by
  cases k with
  | zero => intro i; exact Fin.elim0 i
  | succ k =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact h i.castSucc i.succ rfl

theorem fin_strictAnti_from_adjacent {α : Type*} [Preorder α] {k : ℕ} (f : Fin k → α)
    (h : ∀ i j, i.val+1=j.val → f j<f i) : StrictAnti f :=
  @fin_strictMono_from_adjacent αᵒᵈ _ k f h

theorem peak_free_prefix_order {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : peaks (fromFinPermutation π)=∅) (k : ℕ) (hk : k<n)
    (hmin : finValue π k=0) :
    StrictAnti (fun i : Fin k => π ⟨i.val,lt_trans i.isLt hk⟩) := by
  apply fin_strictAnti_from_adjacent
  intro i j hij
  have hv := (peak_free_valley π h k hk hmin).1 i.val i.isLt
  have hin : i.val<n := lt_trans i.isLt hk
  have hjn : j.val<n := lt_trans j.isLt hk
  rw [hij] at hv
  simpa only [finValue,dite_eq_left hin,dite_eq_left hjn,Fin.lt_def] using hv

theorem peak_free_suffix_order {n : ℕ} (π : Equiv.Perm (Fin n))
    (h : peaks (fromFinPermutation π)=∅) (k : ℕ) (hk : k<n)
    (hmin : finValue π k=0) :
    StrictMono (fun i : Fin (n-k) => π ⟨k+i.val,by have := i.isLt; omega⟩) := by
  apply fin_strictMono_from_adjacent
  intro i j hij
  have hji : k+i.val+1=k+j.val := by omega
  have hin : k+i.val<n := by have := i.isLt; omega
  have hjn : k+j.val<n := by have := j.isLt; omega
  have hv := (peak_free_valley π h k hk hmin).2 (k+i.val) (by omega) (by omega)
  rw [hji] at hv
  simpa only [finValue,dite_eq_left hin,dite_eq_left hjn,Fin.lt_def] using hv

end PeakPolynomials
namespace PeakPolynomials

theorem ordered_value_congr {n k : ℕ} (S T : Finset (Fin n)) (h : S=T)
    (hS : S.card=k) (hT : T.card=k) (i : Fin k) :
    (S.orderIsoOfFin hS i).val=(T.orderIsoOfFin hT i).val := by
  subst T
  rfl

theorem minimum_value {n : ℕ} (π : Equiv.Perm (Fin (n+1))) :
    finValue π (π.symm 0).val=0 := by
  simp [finValue,(π.symm 0).isLt]

theorem peak_free_left_set_unique {n : ℕ} (π ρ : Equiv.Perm (Fin (n+1)))
    (hπ : peaks (fromFinPermutation π)=∅) (hρ : peaks (fromFinPermutation ρ)=∅)
    (hS : leftOfMinimum π=leftOfMinimum ρ) : π=ρ := by
  have hk := congrArg Finset.card hS
  rw [leftOfMinimum_card,leftOfMinimum_card] at hk
  let k := (π.symm 0).val
  have hkn : k<n+1 := (π.symm 0).isLt
  have hpmin : finValue π k=0 := minimum_value π
  have hrmin : finValue ρ k=0 := by simpa only [k,hk] using minimum_value ρ
  have hs : prefixValues π k=prefixValues ρ k := by
    change prefixValues π (π.symm 0).val=prefixValues ρ (ρ.symm 0).val at hS
    simpa only [k,hk] using hS
  have hpa := peak_free_prefix_order π hπ k hkn hpmin
  have hra := peak_free_prefix_order ρ hρ k hkn hrmin
  have hpm := peak_free_suffix_order π hπ k hkn hpmin
  have hrm := peak_free_suffix_order ρ hρ k hkn hrmin
  apply Equiv.ext
  intro i
  by_cases hi : i.val<k
  · have hp := decreasing_prefix_rank π k (Nat.le_of_lt hkn) hpa ⟨i.val,hi⟩
    have hr := decreasing_prefix_rank ρ k (Nat.le_of_lt hkn) hra ⟨i.val,hi⟩
    have hc := ordered_value_congr _ _ hs (prefixValues_card π k (Nat.le_of_lt hkn))
      (prefixValues_card ρ k (Nat.le_of_lt hkn)) (⟨i.val,hi⟩ : Fin k).rev
    exact hp.trans (hc.trans hr.symm)
  · have hj : i.val-k<n+1-k := by have := i.isLt; omega
    have hp := increasing_suffix_rank π k (Nat.le_of_lt hkn) hpm ⟨i.val-k,hj⟩
    have hr := increasing_suffix_rank ρ k (Nat.le_of_lt hkn) hrm ⟨i.val-k,hj⟩
    have hc := ordered_value_congr _ _ (congrArg (fun S : Finset (Fin (n+1)) => Sᶜ) hs)
      (suffixValues_card π k (Nat.le_of_lt hkn))
      (suffixValues_card ρ k (Nat.le_of_lt hkn)) ⟨i.val-k,hj⟩
    have he : k+(i.val-k)=i.val := by omega
    simpa only [he] using hp.trans (hc.trans hr.symm)

theorem peak_free_reconstruct {n : ℕ} (π : Equiv.Perm (Fin (n+1)))
    (hπ : peaks (fromFinPermutation π)=∅) :
    valleyPermutation (leftOfMinimum π)=π := by
  apply peak_free_left_set_unique
  · exact valley_constructed_no_peaks _ (zero_not_leftOfMinimum π)
  · exact hπ
  · exact valley_left_set _ (zero_not_leftOfMinimum π)

end PeakPolynomials
namespace PeakPolynomials
open Finset

noncomputable def peakFreeSubsetEquiv (n : ℕ) :
    {π : Equiv.Perm (Fin (n+1)) // peaks (fromFinPermutation π)=∅} ≃
      {S : Finset (Fin (n+1)) // 0 ∉ S} where
  toFun π := ⟨leftOfMinimum π.val,zero_not_leftOfMinimum π.val⟩
  invFun S := ⟨valleyPermutation S.val,valley_constructed_no_peaks S.val S.property⟩
  left_inv π := Subtype.ext (peak_free_reconstruct π.val π.property)
  right_inv S := Subtype.ext (valley_left_set S.val S.property)

theorem subsets_avoiding_zero_card (n : ℕ) :
    Fintype.card {S : Finset (Fin (n+1)) // 0 ∉ S}=2^n := by
  let e : {S : Finset (Fin (n+1)) // 0 ∉ S} ≃
      ↥(((univ : Finset (Fin (n+1))).erase 0).powerset) :=
    Equiv.subtypeEquivRight (fun S => by simp [subset_erase])
  rw [Fintype.card_congr e,Fintype.card_coe,card_powerset,
    card_erase_of_mem (mem_univ 0),card_univ,Fintype.card_fin]
  simp

theorem peakCount_empty_succ (n : ℕ) : peakCount (n+1) ∅=2^n := by
  rw [← fin_peak_count]
  exact (Fintype.card_congr (peakFreeSubsetEquiv n)).trans (subsets_avoiding_zero_card n)

theorem peakCount_empty_positive (n : ℕ) (hn : 0<n) : peakCount n ∅=2^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using peakCount_empty_succ k

theorem literal_block_recurrence_with_empty_count (a b : ℕ) (hb : 0<b) (T : Finset ℕ)
    (hT : ∀ i ∈ T, 2 ≤ i ∧ i<a) :
    peakCount (a+b) T + peakCount (a+b) (insert a T) +
      peakCount (a+b) (insert (a+1) T) =
      (a+b).choose a * peakCount a T * 2^(b-1) := by
  rw [literal_block_counting_recurrence a b T hT,peakCount_empty_positive b hb]

end PeakPolynomials
namespace ReflectedNewton

def slope (a : ℤ → ℝ) (i : ℤ) : ℝ := a i-a (i-1)

structure SymmetricConcave (a : ℤ → ℝ) (N : ℤ) : Prop where
  length_nonneg : 0 ≤ N
  left_zero : a (-1)=0
  right_zero : a (N+1)=0
  reflected : ∀ i, -1 ≤ i → i ≤ N+1 → a (N-i)=a i
  concave : ∀ i, 0 ≤ i → i ≤ N → a (i-1)+a (i+1) ≤ 2*a i

theorem slopes_antitone {a : ℤ → ℝ} {N : ℤ} (h : SymmetricConcave a N)
    {i j : ℤ} (hi : 0 ≤ i) (hij : i ≤ j) (hj : j ≤ N+1) : slope a j ≤ slope a i := by
  induction j, hij using Int.leInduction with
  | base => exact le_refl _
  | succ j hij ih =>
    have hprev := ih (by omega)
    have hc := h.concave j (by omega) (by omega)
    dsimp [slope] at hprev ⊢
    have heq : j+1-1=j := by omega
    rw [heq]
    linarith

theorem slope_reflection {a : ℤ → ℝ} {N : ℤ} (h : SymmetricConcave a N)
    {i : ℤ} (hi : 0 ≤ i) (hiN : i ≤ N+1) : slope a (N+1-i)= -slope a i := by
  have h1 := h.reflected i (by omega) hiN
  have h2 := h.reflected (i-1) (by omega) (by omega)
  have heq1 : N+1-i=N-(i-1) := by omega
  have heq2 : N+1-i-1=N-i := by omega
  unfold slope
  rw [heq2,heq1,h1,h2]
  ring

theorem slope_nonneg_left {a : ℤ → ℝ} {N : ℤ} (h : SymmetricConcave a N)
    {i : ℤ} (hi : 0 ≤ i) (hic : 2*i ≤ N+1) : 0 ≤ slope a i := by
  have hs := slopes_antitone h hi (show i ≤ N+1-i by omega) (by omega)
  rw [slope_reflection h hi (by omega)] at hs
  linarith

theorem sequence_monotone_left {a : ℤ → ℝ} {N : ℤ} (h : SymmetricConcave a N)
    {i j : ℤ} (hi : -1 ≤ i) (hij : i ≤ j) (hjc : 2*j ≤ N+1) : a i ≤ a j := by
  induction j, hij using Int.leInduction with
  | base => exact le_refl _
  | succ j hij ih =>
    have hprev := ih (by omega)
    have hs := slope_nonneg_left h (i := j+1) (by omega) hjc
    dsimp [slope] at hs
    have heq : j+1-1=j := by omega
    rw [heq] at hs
    linarith

end ReflectedNewton
namespace ReflectedNewton

def kernel (m k j : ℤ) : ℤ :=
  max 0 (min (min (k + 1) (j + 1)) (min (m - 1 - k) (m - 1 - j)))

theorem kernel_nonneg (m k j : ℤ) : 0 ≤ kernel m k j := by
  exact le_max_left _ _

theorem kernel_reflection (m k j : ℤ) :
    kernel m (m - 2 - k) j = kernel m k j := by
  unfold kernel
  omega

theorem kernel_curvature {m k j : ℤ} (hm : 2 ≤ m)
    (hk : 0 ≤ k ∧ k ≤ m - 2) (hj : 0 ≤ j ∧ j ≤ m - 2) :
    2 * kernel m k j - kernel m (k - 1) j - kernel m (k + 1) j =
      (if k = j then 1 else 0) + (if k = m - 2 - j then 1 else 0) := by
  unfold kernel
  split_ifs <;> omega

end ReflectedNewton

end PermutationPeaks
