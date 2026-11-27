module

public import conjectures.MissingSumFringes.Container
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Classical Pointwise

def scale (q t : ℕ) := t/q^3+1
def binWidth (q t : ℕ) := q^2*scale q t

/-- One of the bins that contain the highest missing sums has enough equations. -/
private theorem band_exists {q t m : ℕ} (hq : 0<q) {H : Finset ℕ} (sub : H⊆range t)
    (count : H.card=m) (hm : binWidth q t≤m) :
    ∃ s≤t, ∃ S⊆H, S⊆Ico (s-binWidth q t) s ∧ q*scale q t≤S.card ∧ m≤s+binWidth q t := by
  let w := binWidth q t
  let h := scale q t
  have hp : 0<h := Nat.zero_lt_succ _
  have wp : 0<w := Nat.mul_pos (pow_pos hq _) hp
  have cover : t<q*w := by
    have := Nat.lt_mul_div_succ t (pow_pos hq 3)
    simpa [w,binWidth,scale,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using this
  let B := H \ range (m-w)
  have many : w≤B.card := by
    have lost := card_le_card (inter_subset_right (s₁:=H) (s₂:=range (m-w)))
    have split := card_sdiff_add_card_inter H (range (m-w))
    simp only [card_range] at lost
    change B.card+(H∩range (m-w)).card=H.card at split
    omega
  have maps : ∀ x∈B, x/w∈range q := by
    intro x hx
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul wp).mpr
    exact (mem_range.mp (sub (mem_sdiff.mp hx).1)).trans cover
  obtain ⟨j,_,mass⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to maps
    (nonempty_range_iff.mpr (Nat.ne_of_gt hq)) (n:=q*h) (by
      rw [card_range]
      simpa [w,binWidth,h,pow_two,Nat.mul_assoc] using many)
  let S := B.filter fun x => x/w=j
  let s := min t ((j+1)*w)
  have band : S⊆Ico (s-w) s := by
    intro x hx
    obtain ⟨hxB,idx⟩ := mem_filter.mp hx
    have xl := mem_range.mp (sub (mem_sdiff.mp hxB).1)
    have lo : j*w≤x := by simpa [idx] using Nat.div_mul_le_self x w
    have hi : x<(j+1)*w := by simpa [idx,Nat.mul_comm] using Nat.lt_mul_div_succ x wp
    apply mem_Ico.mpr ⟨?_,lt_min xl hi⟩
    have bound : s≤j*w+w := by simp [s,Nat.add_mul]
    omega
  have hn : S.Nonempty := card_pos.mp ((Nat.mul_pos hq hp).trans_le mass)
  obtain ⟨x,hx⟩ := hn
  have lower := (mem_sdiff.mp (mem_filter.mp hx).1).2
  have upper := (mem_Ico.mp (band hx)).2
  simp only [mem_range,not_lt] at lower
  exact ⟨s,min_le_left ..,S,(filter_subset ..).trans sdiff_subset,band,mass,by omega⟩

def smallSets (t k : ℕ) := (range (k+1)).biUnion fun r => (range t).powersetCard r

private theorem smallSets_card (t k : ℕ) : (smallSets t k).card≤(k+1)*(t+1)^k := by
  apply (card_biUnion_le_card_mul _ _ ((t+1)^k) ?_).trans_eq
    (by rw [card_range])
  intro r hr
  rw [card_powersetCard,card_range]
  exact (Nat.choose_le_pow ..).trans ((Nat.pow_le_pow_left (Nat.le_succ t) r).trans
    (Nat.pow_le_pow_right (Nat.zero_lt_succ t) (by simpa [Nat.lt_succ_iff] using hr)))

def augmented (t s h : ℕ) (S F : Finset ℕ) := box s h S F ∪ Ico s t

def rawBoxes (q t : ℕ) :=
  (range (t+1)).biUnion fun s =>
    (Ico (s-binWidth q t) s).powerset.biUnion fun S =>
      (smallSets t (q^3)).image (augmented t s (scale q t) S)

def boxes (q m t : ℕ) : Finset (Finset ℕ) :=
  (insert (range t) (rawBoxes q t)).filter fun C =>
    C⊆range t ∧ (2*C.card+m)*q≤2*t*q+2*binWidth q t*q+t

theorem boxes_card (q m t : ℕ) :
    (boxes q m t).card≤1+(t+1)*(2^binWidth q t*((q^3+1)*(t+1)^(q^3))) := by
  apply (card_filter_le ..).trans ((card_insert_le ..).trans ?_)
  rw [Nat.add_comm 1]
  apply Nat.add_le_add_right
  apply (card_biUnion_le_card_mul _ _ _ ?_).trans_eq (by rw [card_range])
  intro s _
  apply (card_biUnion_le_card_mul _ _ _ ?_).trans
  · rw [card_powerset,Nat.card_Ico]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  · intro S _
    exact card_image_le.trans (smallSets_card ..)

/-- A set with m omitted sums lies inside one of the counted boxes. -/
theorem exists_box {q m t : ℕ} (hq : 0<q) {A : Finset ℕ} (sub : A⊆range t)
    (hm : (missing t A).card=m) : ∃ C∈boxes q m t, A⊆C := by
  let h := scale q t
  let w := binWidth q t
  by_cases few : m<w
  · refine ⟨range t,mem_filter.mpr ⟨mem_insert_self ..,Subset.rfl,?_⟩,sub⟩
    rw [card_range]
    change (2*t+m)*q ≤ 2*t*q+2*w*q+t
    nlinarith [Nat.mul_le_mul_right q few.le]
  obtain ⟨s,st,S,hs,band,dense,loc⟩ := band_exists hq (H:=missing t A) sdiff_subset hm (Nat.le_of_not_gt few)
  let a := A∩range s
  have avoids : ∀ x∈a, ∀ y∈a, x+y∉S := by
    intro x hx y hy ex
    have gap := (mem_sdiff.mp (hs ex)).2
    exact gap (mem_add.mpr ⟨x,(mem_inter.mp hx).1,y,(mem_inter.mp hy).1,rfl⟩)
  obtain ⟨F,fs,cost,inc⟩ := fingerprint (h:=h) (show a⊆range s from inter_subset_right) avoids
  have hp : 0<h := Nat.zero_lt_succ _
  have fp : F.card≤q^3 := by
    have above := Nat.lt_mul_div_succ t (pow_pos hq 3)
    change t<q^3*h at above
    exact (Nat.lt_of_mul_lt_mul_right (cost.trans_lt (st.trans_lt above))).le
  have fin : F∈smallSets t (q^3) := mem_biUnion.mpr
    ⟨F.card,mem_range.mpr (Nat.lt_succ_of_le fp),mem_powersetCard.mpr ⟨fs.trans (inter_subset_left.trans sub),rfl⟩⟩
  let C := augmented t s h S F
  have candidate : C∈rawBoxes q t := mem_biUnion.mpr ⟨s,mem_range.mpr (Nat.lt_succ_of_le st),
    mem_biUnion.mpr ⟨S,mem_powerset.mpr band,mem_image_of_mem _ fin⟩⟩
  have contained : A⊆C := by
    intro x hx
    by_cases xx : x<s
    · exact mem_union_left _ (inc (mem_inter.mpr ⟨hx,mem_range.mpr xx⟩))
    · exact mem_union_right _ (mem_Ico.mpr ⟨Nat.le_of_not_gt xx,mem_range.mp (sub hx)⟩)
  have csub : C⊆range t := union_subset ((box_sub ..).trans (range_mono st))
    (fun x hx => mem_range.mpr (mem_Ico.mp hx).2)
  have comb := box_size (h:=h) band F
  have posS : 0<S.card := (Nat.mul_pos hq hp).trans_le dense
  have cap : 2*(box s h S F).card*q≤(s+w)*q+s := by
    apply Nat.le_of_mul_le_mul_right (c:=S.card) _ posS
    change 2*(box s h S F).card*S.card≤(s+w)*S.card+s*h at comb
    nlinarith only [Nat.mul_le_mul_right q comb,Nat.mul_le_mul_left s dense]
  have union := card_union_le (box s h S F) (Ico s t)
  rw [Nat.card_Ico] at union
  change C.card≤(box s h S F).card+(t-s) at union
  have length := Nat.sub_add_cancel st
  refine ⟨C,mem_filter.mpr ⟨mem_insert_of_mem candidate,csub,?_⟩,contained⟩
  change m≤s+w at loc
  change (2*C.card+m)*q≤2*t*q+2*w*q+t
  nlinarith only [Nat.mul_le_mul_right q union,cap,Nat.mul_le_mul_right q loc,
    congrArg (fun v => v*q) length,st]

end MissingSumFringes
