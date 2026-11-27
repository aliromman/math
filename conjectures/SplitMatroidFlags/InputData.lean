module

public import conjectures.SplitMatroidFlags.Histogram
public import conjectures.SplitMatroidFlags.Families

@[expose] public section

namespace SplitMatroidFlags

open Finset

def bit (i : G) := 2^i.val

private lemma mask_insert (i : G) (S : Finset G) : mask (insert i S) = bit i ||| mask S := by
  rw [← singleton_union,mask_or]
  simp [mask,bit]

private lemma mask_three (x y z : G) : mask {x,y,z} = bit x ||| bit y ||| bit z := by
  rw [mask_insert,mask_insert]
  simp [mask,bit,Nat.or_assoc]

def permitted (L : List ℕ) (x y z : G) :=
  let m := bit x ||| bit y ||| bit z
  L.all fun line => (m &&& line) != m

private lemma permitted_iff {L : List ℕ} {H : Lines} (ok : L.toFinset = H.image mask) (x y z : G) :
    permitted L x y z = true ↔ allowed H {x,y,z} := by
  have mem (n : ℕ) : n ∈ L ↔ ∃ h ∈ H, mask h = n := by
    rw [← List.mem_toFinset,ok,mem_image]
  simp only [permitted,List.all_eq_true,bne_iff_ne,← mask_three,mem,forall_exists_index,and_imp]
  constructor
  · intro p line hl sub
    apply p (mask line) line hl rfl
    rw [← mask_and,inter_eq_left.mpr sub]
  · intro a n line hl eq he
    subst n
    apply a line hl
    exact inter_eq_left.mp (mask_inj ((mask_and _ _).trans he))

def collectBits : List G → ℕ
  | [] => 0
  | i :: t => bit i ||| collectBits t

private lemma collect_bits_eq (t : List G) : collectBits t = mask t.toFinset := by
  induction t with
  | nil => rfl
  | cons i t ih => simp [collectBits,mask_insert,ih]

def rawRows (L : List ℕ) (a : Three G) : Three ℕ :=
  let out := outside a
  let row (i j : G) := collectBits (out.filter fun k => permitted L k i j)
  ⟨row a.y a.z,row a.x a.z,row a.x a.y⟩

private lemma raw_rows_eq {L : List ℕ} {H : Lines} (ok : L.toFinset = H.image mask)
    {a : Three G} (ha : sorted a) : rawRows L a = (rows H a).masks := by
  obtain ⟨x,y,z⟩ := a
  obtain ⟨hxy,hxz,hyz⟩ := distinct_of_sorted ha
  change x ≠ y at hxy
  change x ≠ z at hxz
  change y ≠ z at hyz
  have ex : ({x,y,z} : Finset G).erase x = {y,z} := by ext q; simp; grind
  have ey : ({x,y,z} : Finset G).erase y = {x,z} := by ext q; simp; grind
  have ez : ({x,y,z} : Finset G).erase z = {x,y} := by ext q; simp; grind
  simp only [rawRows,rows,Three.masks,Three.map,Three.mk.injEq,collect_bits_eq]
  refine ⟨congrArg mask ?_,congrArg mask ?_,congrArg mask ?_⟩
  all_goals
    ext j
    simp only [List.mem_toFinset,List.mem_filter,permitted_iff ok,outside,List.mem_finRange,true_and,decide_eq_true_eq,
      mem_filter,mem_univ,permittedSwap,Three.coords,mem_insert,mem_singleton,ex,ey,ez]
    grind

def rawData (L : List ℕ) : List BasisData :=
  ((triples 11).filter fun a => decide (sorted a) && permitted L a.x a.y a.z).map fun a => (a,rawRows L a)

lemma raw_data_eq {L : List ℕ} {H : Lines} (ok : L.toFinset = H.image mask) :
    rawData L = basisData H := by
  have chk (a : Three G) : (decide (sorted a) && permitted L a.x a.y a.z) =
      decide (sorted a ∧ allowed H a.coords) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true,decide_eq_true_iff,permitted_iff ok]
    exact decide_eq_true_iff.symm
  simp only [rawData,basisData,chartList,chk]
  apply List.map_congr_left
  intro a ha
  rw [raw_rows_eq ok (of_decide_eq_true (List.mem_filter.mp ha).2).1]

def admits (b : BasisData) (c : Three G) :=
  (perms c).any fun p =>
    (p.x == b.1.x || b.2.x.testBit p.x.val) &&
    (p.y == b.1.y || b.2.y.testBit p.y.val) &&
    (p.z == b.1.z || b.2.z.testBit p.z.val)

def matchAll (D : List BasisData) :=
  let C := D.map Prod.fst
  D.all fun b => C.all (admits b)

lemma match_all_ok {H : Lines} (h : matchAll (basisData H) = true) : matchTest H := by
  intro a ha
  dsimp only
  intro c hc
  have mem (v : Three G) (hv : v ∈ charts H) : (v,(rows H v).masks) ∈ basisData H := by
    apply List.mem_map.mpr
    exact ⟨v,List.mem_toFinset.mp ((chartList_set H).symm ▸ hv),rfl⟩
  have q := List.all_eq_true.mp h _ (mem a ha)
  have p := List.all_eq_true.mp q c (List.mem_map.mpr ⟨_,mem c hc,rfl⟩)
  simpa [admits,and_assoc] using p

def maskA : List ℕ := [35,69,25,394,660,1888]
def maskB : List ℕ := [7,56,448,585,1170,1828]

lemma masksA : maskA.toFinset = linesA.image mask := by decide +kernel
lemma masksB : maskB.toFinset = linesB.image mask := by decide +kernel

end SplitMatroidFlags
