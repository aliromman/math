module

public import conjectures.SplitMatroidFlags.Counting
public import conjectures.SplitMatroidFlags.Tables
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags

open Finset

def trimSets (X Y Z : Finset G) (u v w : Fin 3) :=
  (X \ (if v < u then Y else ∅)) \ (if w < u then Z else ∅)

def leastRows (N : Three (Finset G)) (h : Three (Fin 3)) : Three (Finset G) :=
  ⟨trimSets N.x N.y N.z h.x h.y h.z,trimSets N.y N.x N.z h.y h.x h.z,trimSets N.z N.x N.y h.z h.x h.y⟩

lemma mask_trim (X Y Z : Finset G) (u v w : Fin 3) :
    mask (trimSets X Y Z u v w) = trim (mask X) (mask Y) (mask Z) u v w := by
  by_cases a : v < u <;> by_cases b : w < u <;>
    simp only [trimSets,trim,mask_diff,a,b,ite_true,ite_false,show mask ∅ = 0 from rfl]

lemma mask_least (N : Three (Finset G)) (h : Three (Fin 3)) :
    (leastRows N h).masks = fullCode N.masks h := by simp [leastRows,fullCode,Three.masks,Three.map,mask_trim]

lemma trim_mem (X Y Z : Finset G) (u v w : Fin 3) (j : G) :
    j ∈ trimSets X Y Z u v w ↔ j ∈ X ∧ (j ∈ Y → u ≤ v) ∧ (j ∈ Z → u ≤ w) := by
  by_cases a : v < u <;> by_cases b : w < u <;> simp [trimSets,a,b] <;> grind

def decodeMask (n : ℕ) : Finset G := univ.filter fun i => n.testBit i.val

def decode (r : Three ℕ) : Three (Finset G) := r.map decodeMask

lemma decode_mask (U : Finset G) : decodeMask (mask U) = U := by ext i; simp [decodeMask]

lemma decode_masks (R : Three (Finset G)) : decode R.masks = R := by simp [decode,Three.masks,Three.map,decode_mask]

def edgeCode (a : Three G) (r : Three ℕ) := a.edges (decode r)

def slice (H : Lines) (a : Three G) (T : Finset G) :=
  (codes H a).image (fun r => r.restrict (mask T))

lemma mem_slice {H a T r} : r ∈ slice H a T ↔
    ∃ h : Three (Fin 3), ((leastRows (rows H a) h).restrictSets T).masks = r := by
  simp only [slice,codes,mem_image,mem_tuples,true_and]
  constructor
  · rintro ⟨s,⟨h,rfl⟩,rfl⟩
    exact ⟨h,by rw [Three.masks_restrict,mask_least]⟩
  · rintro ⟨h,rfl⟩
    exact ⟨_,⟨h,rfl⟩,by rw [Three.masks_restrict,mask_least]⟩

lemma rows_match {H : Lines} {a : Three G} (ha : a ∈ charts H) (h : Three (Fin 3)) (T : Finset G) :
    a.edges ((leastRows (rows H a) h).restrictSets T) =
      pattern (bases H) a.coords T (fun i => (a.atCoord h i).val) := by
  obtain ⟨xy,xz,yz⟩ := distinct_of_sorted (chart_in.mp ha).1
  obtain ⟨ex,ey,ez⟩ := atCoord_rows a (distinct_of_sorted (chart_in.mp ha).1) h
  ext ⟨i,j⟩
  have sw (k : G) : j ∈ univ.filter (permittedSwap H a.coords k) ↔ Swap (bases H) a.coords k j := by
    simp [swap_iff (chart_base ha)]
  have cond : (∀ k ∈ neighbors (bases H) a.coords j, (a.atCoord h i).val ≤ (a.atCoord h k).val) ↔
      (Swap (bases H) a.coords a.x j → (a.atCoord h i).val ≤ h.x.val) ∧
      (Swap (bases H) a.coords a.y j → (a.atCoord h i).val ≤ h.y.val) ∧
      (Swap (bases H) a.coords a.z j → (a.atCoord h i).val ≤ h.z.val) := by
    constructor
    · intro q
      exact ⟨fun s => ex ▸ q a.x (mem_neighbors.mpr s),fun s => ey ▸ q a.y (mem_neighbors.mpr s),
        fun s => ez ▸ q a.z (mem_neighbors.mpr s)⟩
    · rintro ⟨hx,hy,hz⟩ k hk
      have s := mem_neighbors.mp hk
      have sk := s.1
      simp only [Three.coords,mem_insert,mem_singleton] at sk
      rcases sk with rfl|rfl|rfl
      · simpa only [ex] using hx s
      · simpa only [ey] using hy s
      · simpa only [ez] using hz s
  have ins : Swap (bases H) a.coords i j → i = a.x ∨ i = a.y ∨ i = a.z := fun q =>
    by simpa only [Three.coords,mem_insert,mem_singleton] using q.1
  rw [Three.mem_edges,mem_pattern,cond]
  simp only [Three.restrictSets,Three.map,leastRows,rows,mem_inter,trim_mem,sw,Fin.le_def]
  grind

lemma pattern_support {B : Finset (Finset G)} {b T : Finset G} (u : G → ℕ)
    (live : ∀ j ∈ T, ∃ i, Swap B b i j) :
    (pattern B b T u).image Prod.snd = T := by
  ext j
  constructor
  · intro h
    obtain ⟨⟨i,j⟩,he,rfl⟩ := mem_image.mp h
    exact ((mem_pattern i j).mp he).1
  · intro hj
    obtain ⟨i,hi⟩ := live j hj
    obtain ⟨k,hk,min⟩ := exists_min_image (neighbors B b j) u ⟨i,mem_neighbors.mpr hi⟩
    exact mem_image.mpr ⟨(k,j),(mem_pattern k j).mpr ⟨hj,mem_neighbors.mp hk,min⟩,rfl⟩

lemma slice_support {H a T r} (ha : a ∈ charts H) (hs : T ⊆ univ \ a.coords)
    (live : ∀ j ∉ a.coords, ∃ i, Swap (bases H) a.coords i j) (hr : r ∈ slice H a T) :
    (edgeCode a r).image Prod.snd = T := by
  obtain ⟨h,rfl⟩ := mem_slice.mp hr
  rw [edgeCode,decode_masks,rows_match ha]
  exact pattern_support _ (fun j hj => live j (mem_sdiff.mp (hs hj)).2)

def allCodes (H : Lines) (a : Three G) :=
  (univ \ a.coords).powerset.biUnion (slice H a)

lemma codes_represent {H : Lines} {a : Three G} (ha : a ∈ charts H) (hm : HasMatches (bases H) a.coords)
    (P : Finset (G × G)) : represented (bases H) a.coords P ↔ ∃ r ∈ allCodes H a, edgeCode a r = P := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨T,hs,ht⟩ := every_pattern hm hw
    let u (i : G) : Fin 3 := ⟨level a.coords w i % 3,Nat.mod_lt _ (by decide)⟩
    let h := a.map u
    have dd := distinct_of_sorted (chart_in.mp ha).1
    obtain ⟨ex,ey,ez⟩ := atCoord_rows a dd h
    have agree (i) (hi : i ∈ a.coords) : (a.atCoord h i).val = level a.coords w i := by
      have lt := level_lt (w := w) hi
      rw [(mem_bases.mp (chart_base ha)).1] at lt
      have e : a.atCoord h i = u i := by
        simp only [Three.coords,mem_insert,mem_singleton] at hi
        rcases hi with rfl|rfl|rfl
        · exact ex
        · exact ey
        · exact ez
      rw [e]
      exact Nat.mod_eq_of_lt lt
    let r := ((leastRows (rows H a) h).restrictSets T).masks
    refine ⟨r,mem_biUnion.mpr ⟨T,mem_powerset.mpr hs,mem_slice.mpr ⟨h,rfl⟩⟩,?_⟩
    rw [edgeCode,show r = _ from rfl,decode_masks,rows_match ha,ht]
    ext ⟨i,j⟩
    rw [mem_pattern,mem_pattern]
    refine and_congr_right fun _ => and_congr_right fun sw => ?_
    apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    rw [agree i sw.1,agree k (mem_neighbors.mp hk).1]
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨T,_,hr⟩ := mem_biUnion.mp hr
    obtain ⟨h,rfl⟩ := mem_slice.mp hr
    rw [edgeCode,decode_masks,rows_match ha]
    exact realize_pattern (chart_base ha) hm _ _

end SplitMatroidFlags
