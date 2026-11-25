module

public import conjectures.AscoliDihedralDominance.GroupModels
public import conjectures.AscoliDihedralDominance.Gain
import Mathlib.Data.Nat.Bitwise

@[expose] public section
namespace AscoliDihedral
open Finset

private def pairMask (f : ℕ → ℕ → ℕ) (A : Finset ℕ) : ℕ :=
  A.fold (· ||| ·) 0 (fun x ↦ A.fold (· ||| ·) 0 (fun y ↦ 2 ^ f x y))

private def bitCount (n v : ℕ) : ℕ := ((range n).filter fun i ↦ v.testBit i).card

private theorem bit_fold {G : Type*} [DecidableEq G] (s : Finset G) (f : G → ℕ) (i : ℕ) :
    (Finset.fold (fun a b : ℕ ↦ a ||| b) (0 : ℕ) f s).testBit i = true ↔ ∃ a ∈ s, (f a).testBit i = true := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.fold_insert ha,ih]

private theorem card_encoded {G : Type*} [DecidableEq G] (A : Finset G)
    (e : G ↪ ℕ) (n : ℕ) (he : ∀ x, e x < n) (f : G → G → G) (g : ℕ → ℕ → ℕ)
    (hg : ∀ x y, e (f x y)=g (e x) (e y)) :
    ((A ×ˢ A).image (fun p ↦ f p.1 p.2)).card = bitCount n (pairMask g (A.map e)) := by
  unfold bitCount
  rw [← card_map (f := e)]
  apply congrArg Finset.card
  apply Finset.ext
  intro i
  rw [Finset.mem_filter,mem_range]
  simp only [mem_map,mem_image,Prod.exists,mem_product,pairMask,bit_fold,
    Nat.testBit_two_pow,decide_eq_true_eq]
  constructor
  · rintro ⟨_,⟨a,b,⟨ha,hb⟩,rfl⟩,rfl⟩
    exact ⟨he _,e a,⟨a,ha,rfl⟩,e b,⟨b,hb,rfl⟩,(hg a b).symm⟩
  · rintro ⟨_,_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨_,⟨a,b,⟨ha,hb⟩,rfl⟩,hg a b⟩

/-- The high digits are binary. Only the last coordinate can change sign under inversion. -/
private def label (h d : ℕ) (quot : Bool) (i j : ℕ) : ℕ :=
  let sub := if quot then decide ((i < h) ↔ (j < h)) else decide (h ≤ i)
  ((i/d) ^^^ (j/d))*d + (if sub then (i % d + d - j % d) % d else (i % d + j % d) % d)

private def bytePop (v : ℕ) : ℕ :=
  let t := v % 256
  let a := (t &&& 85) + ((t >>> 1) &&& 85)
  let b := (a &&& 51) + ((a >>> 2) &&& 51)
  (b &&& 15) + ((b >>> 4) &&& 15)

private def pop24 (v : ℕ) := bytePop v + (bytePop (v >>> 8) + bytePop (v >>> 16))

private theorem bytePop_eq (v : ℕ) : bitCount 8 v = bytePop v := by
  have all : ∀ i : Fin 256, bitCount 8 i = bytePop i := by decide +kernel
  have hc : bitCount 8 v = bitCount 8 (v % 256) := by
    apply congrArg card
    apply filter_congr
    intro i hi
    have lt := mem_range.mp hi
    change v.testBit i = true ↔ (v % 2^8).testBit i = true
    rw [Nat.testBit_mod_two_pow v 8 i]
    simp [lt]
  rw [hc,all ⟨v % 256,Nat.mod_lt _ (by decide)⟩]
  simp [bytePop]

private theorem bitCount_split (a b v : ℕ) :
    bitCount (a+b) v = bitCount a v + bitCount b (v >>> a) := by
  simp only [bitCount,card_filter,sum_range_add,Nat.testBit_shiftRight]

private theorem pop24_eq (v : ℕ) : bitCount 24 v = pop24 v := by
  rw [bitCount_split 8 16,bitCount_split 8 8]
  simp only [bytePop_eq,←Nat.shiftRight_add,pop24]

private def evalSize (h d m : ℕ) : ℤ :=
  ∑ A ∈ (range (2*h)).powersetCard m,
    let p := pop24 (pairMask (label h d false) A)
    let q := pop24 (pairMask (label h d true) A)
    (if q < p then 1 else 0) - (if p < q then 1 else 0)

private theorem gain_encoded {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (h d : ℕ) (hn : 2*h≤24) (e : G ↪ ℕ) (eu : (univ : Finset G).map e = range (2*h))
    (pm : ∀ x y, e (x*y)=label h d false (e x) (e y))
    (qm : ∀ x y, e (x*y⁻¹)=label h d true (e x) (e y)) (m : ℕ) :
    gainAt G m = evalSize h d m := by
  have hb (x : G) : e x < 24 := (mem_range.mp (eu ▸ mem_map.mpr ⟨x,mem_univ _,rfl⟩)).trans_le hn
  unfold gainAt evalSize
  rw [←sum_boole,←sum_boole,←sum_sub_distrib,←eu,powersetCard_map,sum_map]
  apply sum_congr rfl
  intro A _
  change ((if (quotients A).card < (products A).card then 1 else 0) -
      (if (products A).card < (quotients A).card then 1 else 0) : ℤ) = _
  rw [products,quotients,card_encoded A e _ hb _ _ pm,card_encoded A e _ hb _ _ qm,pop24_eq,pop24_eq]
  rfl


private def code6 (x : Dih (AbelianModel [2,3])) :=
  (if x.reflection then 6 else 0) + 3*x.position.1.val + x.position.2.1.val

private def code8 (x : Dih (AbelianModel [2,4])) :=
  (if x.reflection then 8 else 0) + 4*x.position.1.val + x.position.2.1.val

private def code12 (x : Dih (AbelianModel [2,2,3])) :=
  (if x.reflection then 12 else 0) + 6*x.position.1.val + 3*x.position.2.1.val + x.position.2.2.1.val

private def embed6 : Dih (AbelianModel [2,3]) ↪ ℕ := by
  have inj : ∀ x y, code6 x = code6 y → x=y := by decide +kernel
  exact ⟨code6,fun {x y} ↦ inj x y⟩

private theorem gain6 (m : ℕ) : gainAt (Dih (AbelianModel [2,3])) m = evalSize 6 3 m :=
  gain_encoded 6 3 (by decide) embed6 (by decide +kernel) (by decide +kernel) (by decide +kernel) m

private def embed8 : Dih (AbelianModel [2,4]) ↪ ℕ := by
  have inj : ∀ x y, code8 x = code8 y → x=y := by decide +kernel
  exact ⟨code8,fun {x y} ↦ inj x y⟩

private theorem gain8 (m : ℕ) : gainAt (Dih (AbelianModel [2,4])) m = evalSize 8 4 m :=
  gain_encoded 8 4 (by decide) embed8 (by decide +kernel) (by decide +kernel) (by decide +kernel) m

private def embed12 : Dih (AbelianModel [2,2,3]) ↪ ℕ := by
  have inj : ∀ x y, code12 x = code12 y → x=y := by decide +kernel
  exact ⟨code12,fun {x y} ↦ inj x y⟩

private theorem gain12 (m : ℕ) : gainAt (Dih (AbelianModel [2,2,3])) m = evalSize 12 3 m :=
  gain_encoded 12 3 (by decide) embed12 (by decide +kernel) (by decide +kernel) (by decide +kernel) m

set_option maxRecDepth 200000 in
theorem low_gain_six : ∑ m ∈ range 4, gainAt (Dih (AbelianModel [2,3])) m = 144 := by
  simp_rw [gain6]
  decide +kernel

set_option maxRecDepth 200000 in
theorem low_gain_eight : ∑ m ∈ range 6, gainAt (Dih (AbelianModel [2,4])) m = 2928 := by
  simp_rw [gain8]
  decide +kernel

set_option maxRecDepth 200000 in
theorem low_gain_twelve : ∑ m ∈ range 5, gainAt (Dih (AbelianModel [2,2,3])) m = 7320 := by
  simp_rw [gain12]
  decide +kernel

end AscoliDihedral
