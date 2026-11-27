module

public import conjectures.AscoliDihedralDominance.Statement
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

@[expose] public section
namespace AscoliDihedral
open Finset

/-- The elementary divisors are the actual cyclic orders. All enumerated orders exceed one. -/
def AbelianModel : List ℕ → Type
  | [] => ZMod 1
  | d::ds => ZMod (d-1+1) × AbelianModel ds

instance modelGroup : (ds : List ℕ) → AddCommGroup (AbelianModel ds)
  | [] => inferInstanceAs (AddCommGroup (ZMod 1))
  | d::ds => letI := modelGroup ds; inferInstanceAs (AddCommGroup (ZMod (d-1+1) × AbelianModel ds))

instance modelFinite : (ds : List ℕ) → Fintype (AbelianModel ds)
  | [] => inferInstanceAs (Fintype (ZMod 1))
  | d::ds => letI := modelFinite ds; inferInstanceAs (Fintype (ZMod (d-1+1) × AbelianModel ds))

instance modelEq : (ds : List ℕ) → DecidableEq (AbelianModel ds)
  | [] => inferInstanceAs (DecidableEq (ZMod 1))
  | d::ds => letI := modelEq ds; inferInstanceAs (DecidableEq (ZMod (d-1+1) × AbelianModel ds))

/-- Enumerate the coordinates from left to right in their residue orders. -/
def modelElements : (ds : List ℕ) → List (AbelianModel ds)
  | [] => [0]
  | d::ds => (List.finRange (d-1+1)).product (modelElements ds)

theorem modelElements_nodup (ds : List ℕ) : (modelElements ds).Nodup := by
  induction ds with
  | nil => exact List.nodup_singleton _
  | cons d ds ih => exact (List.nodup_finRange _).product ih

private theorem mem_modelElements (ds : List ℕ) (x : AbelianModel ds) : x ∈ modelElements ds := by
  induction ds with
  | nil => exact List.mem_singleton.mpr (Subsingleton.elim (α := ZMod 1) _ _)
  | cons d ds ih => exact List.mem_product.mpr ⟨List.mem_finRange x.1,ih x.2⟩

theorem modelElements_toFinset_univ (ds : List ℕ) : (modelElements ds).toFinset = univ := by
  ext x
  simp [mem_modelElements]

/-- Sorted prime-power products with at most the given length and product at most the budget. -/
def choices : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | k+1, lo, budget =>
      [] :: (List.range (budget+1)).flatMap fun d ↦
        if lo≤d ∧ d.primeFactors.card=1 then
          (choices k d (budget/d)).map (d::·)
        else []

/-- The 43 possible elementary-divisor lists of order below 32 with exponent greater than two. -/
def smallModels : List (List ℕ) :=
  (choices 4 2 31).filter fun ds ↦ ds.any (fun d ↦ decide (3≤d))

private theorem image_pairs {G K : Type*} [DecidableEq G] [DecidableEq K] (e : G ≃ K)
    (f : G → G → G) (g : K → K → K) (hf : ∀ a b, e (f a b)=g (e a) (e b)) (A : Finset G) :
    ((A ×ˢ A).image (fun p ↦ f p.1 p.2)).map e.toEmbedding =
      (e.finsetCongr A ×ˢ e.finsetCongr A).image (fun p ↦ g p.1 p.2) := by
  ext x
  simp only [mem_map,mem_image,Prod.exists,mem_product,Equiv.finsetCongr_apply,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨y,⟨a,b,⟨ha,hb⟩,rfl⟩,rfl⟩
    exact ⟨e a,e b,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,(hf a b).symm⟩
  · rintro ⟨_,_,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,rfl⟩
    exact ⟨_,⟨a,b,⟨ha,hb⟩,rfl⟩,hf a b⟩

private theorem compare_count {G K : Type*} [Group G] [Group K] [Fintype G] [Fintype K]
    [DecidableEq G] [DecidableEq K] (e : G ≃* K) (r : ℕ → ℕ → Prop) [DecidableRel r] :
    (univ.filter fun A : Finset G ↦ r (products A).card (quotients A).card).card =
    (univ.filter fun A : Finset K ↦ r (products A).card (quotients A).card).card := by
  apply card_equiv e.toEquiv.finsetCongr
  intro A
  have p := image_pairs e.toEquiv (·*·) (·*·) e.map_mul A
  have q := image_pairs e.toEquiv (fun a b ↦ a*b⁻¹) (fun a b ↦ a*b⁻¹)
    (fun a b ↦ by simp) A
  have hmem : r (products A).card (quotients A).card ↔
      r (products (e.toEquiv.finsetCongr A)).card (quotients (e.toEquiv.finsetCongr A)).card := by
    unfold products quotients
    rw [←p,←q,card_map,card_map]
  constructor
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,hmem.mp (mem_filter.mp h).2⟩
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,hmem.mpr (mem_filter.mp h).2⟩

theorem productDominant_congr {G K : Type*} [Group G] [Group K] [Fintype G] [Fintype K]
    [DecidableEq G] [DecidableEq K] (e : G ≃* K) : ProductDominant G ↔ ProductDominant K := by
  unfold ProductDominant
  rw [compare_count e (·<·),compare_count e (·>·)]

def Dih.congr {G K : Type*} [AddCommGroup G] [AddCommGroup K] (e : G ≃+ K) :
    Dih G ≃* Dih K where
  toFun x := ⟨x.reflection,e x.position⟩
  invFun y := ⟨y.reflection,e.symm y.position⟩
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    change Dih.mk (b ^^ c) (e (if b then x-y else x+y)) = Dih.mk (b ^^ c) (if b then e x-e y else e x+e y)
    cases b <;> simp

private def splitPi {k : ℕ} (f : Fin (k+1) → ℕ) :
    ((i : Fin (k+1)) → ZMod (f i)) ≃+ ZMod (f 0) × ((i : Fin k) → ZMod (f i.succ)) where
  toEquiv := (Fin.consEquiv (fun i ↦ ZMod (f i))).symm
  map_add' _ _ := rfl

private theorem piModels (k : ℕ) (p e : Fin k → ℕ) (hp : ∀ i, (p i).Prime) :
    ∃ ds : List ℕ, (∀ d ∈ ds, IsPrimePow d) ∧
      Nonempty (((i : Fin k) → ZMod (p i ^ e i)) ≃+ AbelianModel ds) := by
  induction k with
  | zero =>
      refine ⟨[],by simp,?_⟩
      exact ⟨(AddEquiv.ofUnique : ((i : Fin 0) → ZMod (p i ^ e i)) ≃+ ZMod 1)⟩
  | succ k ih =>
      obtain ⟨ds,hds,⟨eqv⟩⟩ := ih (fun i ↦ p i.succ) (fun i ↦ e i.succ) (fun i ↦ hp i.succ)
      let cut := splitPi (fun i ↦ p i ^ e i)
      by_cases h : e 0 = 0
      · have h1 : p 0 ^ e 0 = 1 := by simp [h]
        exact ⟨ds,hds,⟨cut.trans (((ZMod.ringEquivCongr h1).toAddEquiv.prodCongr eqv).trans
          AddEquiv.uniqueProd)⟩⟩
      · have hd := (hp 0).isPrimePow.pow h
        have h1 : p 0 ^ e 0 = p 0 ^ e 0 - 1 + 1 := by have := hd.two_le; omega
        refine ⟨p 0 ^ e 0 :: ds,?_,⟨cut.trans ((ZMod.ringEquivCongr h1).toAddEquiv.prodCongr eqv)⟩⟩
        exact List.forall_mem_cons.mpr ⟨hd,hds⟩

private theorem elementary_divisors (H : Type*) [AddCommGroup H] [Fintype H] :
    ∃ ds : List ℕ, (∀ d ∈ ds, IsPrimePow d) ∧ Nonempty (H ≃+ AbelianModel ds) := by
  classical
  obtain ⟨ι,_,p,hp,e,⟨iso⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite H
  let E := Fintype.equivFin ι
  obtain ⟨ds,hds,⟨K⟩⟩ := piModels _ (fun i ↦ p (E.symm i)) (fun i ↦ e (E.symm i))
    (fun i ↦ hp (E.symm i))
  exact ⟨ds,hds,⟨iso.trans ((DirectSum.addEquivProd _).trans
    (((RingEquiv.piCongrLeft' _ E).toAddEquiv).trans K))⟩⟩

private theorem model_perm {l s : List ℕ} (h : l.Perm s) :
    Nonempty (AbelianModel l ≃+ AbelianModel s) := by
  induction h with
  | nil => exact ⟨AddEquiv.refl _⟩
  | cons d _ ih =>
      obtain ⟨e⟩ := ih
      exact ⟨(AddEquiv.refl (ZMod (d-1+1))).prodCongr e⟩
  | swap x y l =>
      exact ⟨AddEquiv.prodAssoc.symm.trans
        ((AddEquiv.prodComm.prodCongr (AddEquiv.refl (AbelianModel l))).trans AddEquiv.prodAssoc)⟩
  | trans _ _ ih ij =>
      obtain ⟨e⟩ := ih
      obtain ⟨f⟩ := ij
      exact ⟨e.trans f⟩

private theorem model_card {ds : List ℕ} (hs : ∀ d ∈ ds, IsPrimePow d) :
    Fintype.card (AbelianModel ds) = ds.prod := by
  induction ds with
  | nil => exact ZMod.card 1
  | cons d ds ih =>
      obtain ⟨hd,ht⟩ := List.forall_mem_cons.mp hs
      change Fintype.card (ZMod (d-1+1) × AbelianModel ds) = d * ds.prod
      rw [Fintype.card_prod,ZMod.card,ih ht]
      have := hd.two_le
      congr 1
      omega

private theorem two_pow_length {ds : List ℕ} (hs : ∀ d ∈ ds, IsPrimePow d) :
    2 ^ ds.length ≤ ds.prod := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      obtain ⟨hd,ht⟩ := List.forall_mem_cons.mp hs
      simpa [pow_succ',List.prod_cons] using Nat.mul_le_mul hd.two_le (ih ht)

private theorem mem_choices {l : List ℕ} (fuel lo budget : ℕ) (hlen : l.length ≤ fuel)
    (hs : l.Pairwise (·≤·)) (hpow : ∀ d ∈ l, IsPrimePow d) (hlo : ∀ d ∈ l, lo ≤ d)
    (hb : l.prod ≤ budget) : l ∈ choices fuel lo budget := by
  induction fuel generalizing l lo budget with
  | zero => have : l = [] := List.length_eq_zero_iff.mp (by omega); simp [this,choices]
  | succ k ih =>
      cases l with
      | nil => simp [choices]
      | cons d ds =>
          obtain ⟨hd,hp⟩ := List.forall_mem_cons.mp hpow
          obtain ⟨hld,_⟩ := List.forall_mem_cons.mp hlo
          obtain ⟨hmin,hsort⟩ := List.pairwise_cons.mp hs
          have dp := lt_of_lt_of_le (Nat.two_pow_pos ds.length) (two_pow_length hp)
          have dpos := hd.one_lt
          change d*ds.prod ≤ budget at hb
          have hdb : d ≤ budget := (Nat.le_mul_of_pos_right _ dp).trans hb
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨d,List.mem_range.mpr (by omega),?_⟩
          rw [ite_eq_left ⟨hld,isPrimePow_iff_card_primeFactors_eq_one.mp hd⟩]
          apply List.mem_map.mpr
          refine ⟨ds,ih d (budget/d) (by simpa using hlen) hsort hp hmin ?_,rfl⟩
          exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hb)

private theorem model_double {ds : List ℕ} (hs : ∀ d ∈ ds, d=2) (x : AbelianModel ds) :
    2 • x = 0 := by
  induction ds with
  | nil => exact Subsingleton.elim (α := ZMod 1) _ _
  | cons d ds ih =>
      obtain ⟨rfl,ht⟩ := List.forall_mem_cons.mp hs
      change (2 • x.1,2 • x.2) = (0,0)
      exact Prod.ext ((by decide : ∀ z : ZMod 2, 2 • z = 0) x.1) (ih ht x.2)

/-- Every group in the small range with an element of order at least three has a listed model. -/
theorem small_classification (H : Type*) [AddCommGroup H] [Fintype H]
    (hn : Fintype.card H < 32) (ht : ∃ h : H, 3 ≤ addOrderOf h) :
    ∃ ds ∈ smallModels, Nonempty (H ≃+ AbelianModel ds) := by
  obtain ⟨l,hl,⟨e⟩⟩ := elementary_divisors H
  let ds := l.mergeSort (·≤·)
  have perm : ds.Perm l := List.mergeSort_perm l _
  obtain ⟨f⟩ := model_perm perm.symm
  let E := e.trans f
  have hp : ∀ d ∈ ds, IsPrimePow d := fun d hd ↦ hl _ (perm.mem_iff.mp hd)
  have hb : ds.prod ≤ 31 := by rw [←model_card hp,←Fintype.card_congr E.toEquiv]; omega
  refine ⟨ds,List.mem_filter.mpr ⟨?_,?_⟩,⟨E⟩⟩
  · apply mem_choices _ _ _ _ (List.pairwise_mergeSort' _ l) hp (fun d hd ↦ (hp d hd).two_le) hb
    change ds.length ≤ 4
    by_contra! h
    have := (Nat.pow_le_pow_right (by decide : 0<2) (show 5 ≤ ds.length by omega)).trans
      (two_pow_length hp)
    omega
  · apply List.any_eq_true.mpr
    by_contra! h
    have h2 : ∀ d ∈ ds, d=2 := by
      intro d hd
      have hh := h d hd
      have hp2 := (hp d hd).two_le
      simp at hh
      omega
    obtain ⟨x,hx⟩ := ht
    have x0 : 2 • x = 0 := E.injective (by simpa only [map_nsmul,map_zero] using model_double h2 (E x))
    have := Nat.le_of_dvd (by decide : 0<2) (addOrderOf_dvd_of_nsmul_eq_zero x0)
    omega

theorem small_of_models (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
    (hn : Fintype.card H < 32) (ht : ∃ h : H, 3 ≤ addOrderOf h)
    (cert : ∀ ds ∈ smallModels, ProductDominant (Dih (AbelianModel ds))) :
    ProductDominant (Dih H) := by
  obtain ⟨ds,hd,⟨e⟩⟩ := small_classification H hn ht
  exact (productDominant_congr (Dih.congr e)).mpr (cert ds hd)

end AscoliDihedral
