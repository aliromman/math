module

public import conjectures.CFPLogDensity.DenseGrowth
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity
open Finset
namespace ColorPairs
variable {r c n : ℕ} {χ : ℕ → Fin r} (F : ColorPairs c n χ)

private theorem sum_upper {S : Finset ℕ} (hS : S ⊆ F.stock) : S.sum id≤S.card*(2*2^n) := by
  calc
    S.sum id ≤ ∑ _x∈S,2*2^n := sum_le_sum (fun x hx => (F.stock_spec (hS hx)).2.1.le)
    _ = _ := by simp

private theorem sum_lower {S : Finset ℕ} (hS : S ⊆ F.stock) : S.card*2^n≤S.sum id := by
  calc
    _ = ∑ _x∈S,2^n := by simp
    _ ≤ S.sum id := sum_le_sum (fun x hx => (F.stock_spec (hS hx)).1)

/-- Up to d−1 spare terms in one invertible residue fill all residues modulo d. -/
private theorem remove_step (P : Span F.d F.stock) (V : Finset ℕ)
    (sv : V⊆F.stock) (res : ∀ v∈V, (v : ZMod F.d)=F.base) (dv : F.d≤V.card)
    (dis : Disjoint P.used V) (x : ℕ) (low : P.start+F.d*(2*2^n)≤x)
    (high : x≤P.start+F.d*P.length) : represent (P.used∪V) x := by
  let : NeZero F.d := ⟨F.step_pos.ne'⟩
  let z : ZMod F.d := ((x : ZMod F.d)-P.start)*(F.base : ZMod F.d)⁻¹
  let j := z.val
  have jlt : j<F.d := z.val_lt
  obtain ⟨S,ss,sc⟩ := exists_subset_card_eq (jlt.le.trans dv)
  have small : S.sum id≤F.d*(2*2^n) := (F.sum_upper (ss.trans sv)).trans (sc ▸ Nat.mul_le_mul_right _ jlt.le)
  have congr : ((S.sum id : ℕ) : ZMod F.d)=(x : ZMod F.d)-P.start := by
    calc
      _ = ∑ v∈S,(v : ZMod F.d) := by push_cast; rfl
      _ = ∑ _v∈S,(F.base : ZMod F.d) := sum_congr rfl (fun v hv => res v (ss hv))
      _ = (j : ZMod F.d)*F.base := by simp [sc,nsmul_eq_mul]
      _ = _ := by
        change (z.val : ZMod F.d)*F.base=_
        rw [ZMod.natCast_zmod_val]
        dsimp [z]
        rw [mul_assoc,mul_comm ((F.base:ZMod F.d)⁻¹),ZMod.coe_mul_inv_eq_one _ F.coprime,mul_one]
  let y := x-P.start-S.sum id
  have eq : P.start+y+S.sum id=x := by dsimp [y]; omega
  have zy : (y : ZMod F.d)=0 := by
    have e := congrArg (fun t : ℕ => (t : ZMod F.d)) eq
    simp only [Nat.cast_add] at e
    rw [congr] at e
    linear_combination e
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp zy
  have kw : k≤P.length := le_of_mul_le_mul_left (a:=F.d) (by omega) F.step_pos
  have sums := represent_add_disjoint dis (P.covers k kw) (show represent V (S.sum id) from ⟨S,ss,rfl⟩)
  rwa [←hk,eq] at sums

/-- A long progression becomes an interval. Add the remaining large terms to extend its upper end. -/
theorem fill (P : Span F.d F.stock) (long : 4*2^n≤P.length)
    (enough : P.used.card+F.d≤F.indices.card) :
    ∃ lo hi : ℕ, lo≤(P.used.card+F.d)*(2*2^n) ∧
      (F.indices.card-P.used.card-F.d)*2^n ≤ hi ∧
      ∀ x, lo≤x → x≤hi → represent F.stock x := by
  let L := F.indices.image F.lower
  have size : L.card=F.indices.card := card_image_of_injective _ F.lower_inj
  have sub : L ⊆ F.stock := by rintro x hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact F.lower_mem hi
  let H := L \ P.used
  have hH : F.indices.card≤H.card+P.used.card := by
    have h := card_sdiff_add_card_inter L P.used
    have le := card_le_card (inter_subset_right : L∩P.used⊆P.used)
    dsimp [H]
    omega
  obtain ⟨V,sv,vc⟩ := exists_subset_card_eq (show F.d≤H.card by omega)
  have hv : V ⊆ F.stock := sv.trans (sdiff_subset.trans sub)
  have Hdis : Disjoint P.used H := disjoint_left.mpr fun _ h m => (mem_sdiff.mp m).2 h
  have dv : Disjoint P.used V := Hdis.mono_right sv
  have res (v) (hi : v∈V) : (v : ZMod F.d)=F.base := by
    obtain ⟨u,_,rfl⟩ := mem_image.mp (mem_sdiff.mp (sv hi)).1
    simp [lower]
  let lo := P.start+F.d*(2*2^n)
  let top := lo+2*2^n
  have ht : top≤P.start+F.d*P.length := by
    have large := Nat.mul_le_mul_left F.d long
    have hdn := Nat.le_mul_of_pos_left (2^n) F.step_pos
    dsimp [lo,top]
    nlinarith only [large,hdn]
  have interval (x) (lx : lo≤x) (xh : x≤top) : represent (P.used∪V) x :=
    F.remove_step P V hv res vc.ge dv x lx (xh.trans ht)
  let R := H\V
  have rv : R⊆F.stock := sdiff_subset.trans (sdiff_subset.trans sub)
  have dr : Disjoint (P.used∪V) R := by
    apply disjoint_left.mpr
    intro a h hr
    rcases mem_union.mp h with u|v
    · exact (mem_sdiff.mp (mem_sdiff.mp hr).1).2 u
    · exact (mem_sdiff.mp hr).2 v
  have grow := extend_interval dr interval (fun a ha => by
    have u := (F.stock_spec (rv ha)).2.1
    dsimp [top]
    omega)
  refine ⟨lo,top+R.sum id,?_,?_,fun x l h => represent_mono (union_subset (union_subset P.subset hv) rv) (grow x l h)⟩
  · have start := P.start_le (fun _ ha => (F.stock_spec ha).2.1.le)
    dsimp [lo]
    rw [Nat.add_mul]
    omega
  · have rem : R.card+F.d=H.card := vc ▸ card_sdiff_add_card_eq_card sv
    have count : F.indices.card-P.used.card-F.d≤R.card := by omega
    exact ((Nat.mul_le_mul_right _ count).trans (F.sum_lower rv)).trans (Nat.le_add_left _ _)

end ColorPairs
end CFPLogDensity
