module

public import conjectures.SplitMatroidFlags.Masks
public import conjectures.SplitMatroidFlags.Exchange
import Mathlib.Tactic.Tauto

@[expose] public section

namespace SplitMatroidFlags

open Finset

abbrev Lines := Finset (Finset G)

def linesA : Lines :=
  {{0,1,5}, {0,2,6}, {0,3,4}, {1,3,7,8}, {2,4,7,9}, {5,6,8,9,10}}

def linesB : Lines :=
  {{0,1,2}, {3,4,5}, {6,7,8}, {0,3,6,9}, {1,4,7,10}, {2,5,8,9,10}}

def allowed (H : Lines) (b : Finset G) : Prop := ∀ L ∈ H, ¬ b ⊆ L

instance (H : Lines) (b : Finset G) : Decidable (allowed H b) := inferInstanceAs (Decidable (∀ _ ∈ H, _))

def bases (H : Lines) : Finset (Finset G) := (univ.powersetCard 3).filter (allowed H)

lemma mem_bases {b : Finset G} {H : Lines} : b ∈ bases H ↔ b.card = 3 ∧ allowed H b := by
  simp [bases]

def tuples {α : Type} [Fintype α] [DecidableEq α] : Finset (Three α) :=
  (univ : Finset (α × α × α)).map ⟨fun t => ⟨t.1,t.2.1,t.2.2⟩,by
    rintro ⟨x,y,z⟩ ⟨a,b,c⟩ e
    simpa using e⟩

lemma mem_tuples {α : Type} [Fintype α] [DecidableEq α] (a : Three α) : a ∈ tuples :=
  mem_map.mpr ⟨(a.x,a.y,a.z),mem_univ _,rfl⟩

def sorted (a : Three G) : Prop := a.x < a.y ∧ a.y < a.z

instance (a : Three G) : Decidable (sorted a) := inferInstanceAs (Decidable (_ ∧ _))

def charts (H : Lines) : Finset (Three G) := tuples.filter fun a => sorted a ∧ allowed H a.coords

lemma chart_in {H : Lines} {a : Three G} : a ∈ charts H ↔ sorted a ∧ allowed H a.coords := by
  simp [charts,mem_tuples]

lemma distinct_of_sorted {a : Three G} (h : sorted a) : a.disjointCoords :=
  ⟨h.1.ne,(h.1.trans h.2).ne,h.2.ne⟩

lemma chart_base {H : Lines} {a : Three G} (h : a ∈ charts H) : a.coords ∈ bases H := by
  obtain ⟨ord,ha⟩ := chart_in.mp h
  obtain ⟨hxy,hxz,hyz⟩ := distinct_of_sorted ord
  exact mem_bases.mpr ⟨by simp [Three.coords,hxy,hxz,hyz],ha⟩

private lemma sorted_exists (b : Finset G) (hb : b.card = 3) :
    ∃ a ∈ (tuples : Finset (Three G)), sorted a ∧ a.coords = b := by
  obtain ⟨x,y,z,ne₁,ne₂,ne₃,rfl⟩ := card_eq_three.mp hb
  have build (a b c : G) (hab : a < b) (hbc : b < c) (eq : ({a,b,c} : Finset G) = {x,y,z}) :
      ∃ t ∈ (tuples : Finset (Three G)), sorted t ∧ t.coords = {x,y,z} :=
    ⟨⟨a,b,c⟩,mem_tuples _,⟨hab,hbc⟩,eq⟩
  by_cases hxy : x < y
  · by_cases hyz : y < z
    · exact build x y z hxy hyz rfl
    · by_cases hxz : x < z
      · apply build x z y hxz (lt_of_le_of_ne (le_of_not_gt hyz) ne₃.symm)
        ext; simp; tauto
      · apply build z x y (lt_of_le_of_ne (le_of_not_gt hxz) ne₂.symm) hxy
        ext; simp; tauto
  · by_cases hxz : x < z
    · apply build y x z (lt_of_le_of_ne (le_of_not_gt hxy) ne₁.symm) hxz
      ext; simp; tauto
    · by_cases hyz : y < z
      · apply build y z x hyz (lt_of_le_of_ne (le_of_not_gt hxz) ne₂.symm)
        ext; simp; tauto
      · apply build z y x (lt_of_le_of_ne (le_of_not_gt hyz) ne₃.symm) (lt_of_le_of_ne (le_of_not_gt hxy) ne₁.symm)
        ext; simp; tauto

lemma bases_as_charts (H : Lines) : bases H = (charts H).image Three.coords := by
  ext t
  refine ⟨fun h => ?_,fun h => ?_⟩
  · obtain ⟨r,ha⟩ := mem_bases.mp h
    obtain ⟨a,_,hord,eq⟩ := sorted_exists t r
    exact mem_image.mpr ⟨a,chart_in.mpr ⟨hord,eq.symm ▸ ha⟩,eq⟩
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact chart_base ha

private lemma coords_inj_sorted : ∀ x y z a b c : G,
    x < y → y < z → a < b → b < c → ({x,y,z} : Finset G) = {a,b,c} → x = a ∧ y = b ∧ z = c := by
  intro x y z a b c hxy hyz hab hbc eq
  have both (i : G) : i = x ∨ i = y ∨ i = z ↔ i = a ∨ i = b ∨ i = c := by
    simpa using (SetLike.ext_iff.mp eq i)
  have xs := (both x).mp (Or.inl rfl)
  have ys := (both y).mp (Or.inr (Or.inl rfl))
  have zs := (both z).mp (Or.inr (Or.inr rfl))
  simp only [Fin.lt_def, Fin.ext_iff] at xs ys zs hxy hyz hab hbc ⊢
  omega

lemma charts_inj (H : Lines) : Set.InjOn (Three.coords (α := G)) (↑(charts H) : Set (Three G)) := by
  rintro ⟨x,y,z⟩ hx ⟨a,b,c⟩ ha eq
  obtain ⟨xord,_⟩ := chart_in.mp hx
  obtain ⟨aord,_⟩ := chart_in.mp ha
  obtain ⟨rfl,rfl,rfl⟩ := coords_inj_sorted x y z a b c xord.1 xord.2 aord.1 aord.2 eq
  rfl

def permittedSwap (H : Lines) (b : Finset G) (i j : G) : Prop :=
  i ∈ b ∧ j ∉ b ∧ allowed H (insert j (b.erase i))

instance (H : Lines) (b : Finset G) (i j : G) : Decidable (permittedSwap H b i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma swap_iff {H : Lines} {b : Finset G} (hb : b ∈ bases H) (i j : G) :
    Swap (bases H) b i j ↔ permittedSwap H b i j := by
  constructor
  · rintro ⟨hi,hj,hs⟩
    exact ⟨hi,hj,(mem_bases.mp hs).2⟩
  · rintro ⟨hi,hj,hs⟩
    refine ⟨hi,hj,mem_bases.mpr ⟨?_,hs⟩⟩
    rw [card_insert_of_notMem (fun h => hj (mem_erase.mp h).2),card_erase_of_mem hi,(mem_bases.mp hb).1]

def perms (a : Three G) : List (Three G) :=
  [⟨a.x,a.y,a.z⟩,⟨a.x,a.z,a.y⟩,⟨a.y,a.x,a.z⟩,⟨a.y,a.z,a.x⟩,⟨a.z,a.x,a.y⟩,⟨a.z,a.y,a.x⟩]

def Three.atCoord {α : Type} (a : Three G) (v : Three α) (i : G) :=
  if i = a.x then v.x else if i = a.y then v.y else v.z

lemma atCoord_rows {α : Type} (a : Three G) (hd : a.disjointCoords) (v : Three α) :
    a.atCoord v a.x = v.x ∧ a.atCoord v a.y = v.y ∧ a.atCoord v a.z = v.z := by
  obtain ⟨hxy,hxz,hyz⟩ := hd
  simp [Three.atCoord,hxy.symm,hxz.symm,hyz.symm]

def canMatch (H : Lines) (a c : Three G) : Prop :=
  let ok (i j : G) := j = i ∨ permittedSwap H a.coords i j
  ∃ p ∈ perms c, ok a.x p.x ∧ ok a.y p.y ∧ ok a.z p.z

instance (H : Lines) (a c : Three G) : Decidable (canMatch H a c) := by
  unfold canMatch
  dsimp only
  infer_instance

lemma chosen_match {H : Lines} {a c : Three G} (ha : a ∈ charts H) (hc : c ∈ charts H)
    (can : canMatch H a c) : ∃ f, Matches (bases H) a.coords c.coords f := by
  obtain ⟨p,hp,okx,oky,okz⟩ := can
  have ac := distinct_of_sorted (chart_in.mp ha).1
  have cc := distinct_of_sorted (chart_in.mp hc).1
  have prop : p.coords = c.coords ∧ p.disjointCoords := by
    obtain ⟨xy,xz,yz⟩ := cc
    simp only [perms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [Three.coords,Three.disjointCoords,Finset.insert_comm,ne_comm]
    all_goals ext q; simp only [mem_insert,mem_singleton,or_left_comm,or_comm]
  let f := a.atCoord p
  obtain ⟨fx,fy,fz⟩ := atCoord_rows a ac p
  refine ⟨f,?_,?_,?_⟩
  · rw [← prop.1]
    simp [Three.coords,f,fx,fy,fz]
  · intro i hi j hj he
    obtain ⟨pxy,pxz,pyz⟩ := prop.2
    simp only [Three.coords,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hi hj
    change a.atCoord p i = a.atCoord p j at he
    grind
  · intro i hi
    simp only [Three.coords,mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [f,fx,swap_iff (chart_base ha)] using okx
    · simpa [f,fy,swap_iff (chart_base ha)] using oky
    · simpa [f,fz,swap_iff (chart_base ha)] using okz

lemma all_matches {H : Lines} (test : ∀ a ∈ charts H, ∀ c ∈ charts H, canMatch H a c) :
    ∀ b ∈ bases H, HasMatches (bases H) b := by
  intro b hb t ht
  rw [bases_as_charts] at hb ht
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
  obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
  exact chosen_match ha hc (test a ha c hc)

end SplitMatroidFlags
