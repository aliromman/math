module

public import conjectures.SplitMatroidFlags.Bipartite
public import conjectures.SplitMatroidFlags.Masks
import Mathlib.Tactic

@[expose] public section

namespace SplitMatroidFlags.Three

open Finset

def pairs (a : Three G) (xy xz yz : Bool) :=
  (if xy then [(a.x,a.y)] else []) ++ (if xz then [(a.x,a.z)] else []) ++ (if yz then [(a.y,a.z)] else [])

def merged (xy xz yz : Bool) := min 2 (xy.toNat + xz.toNat + yz.toNat)

private lemma pair_spec (a : Three G) (xy xz yz : Bool) (i j : G) :
    (i,j) ∈ (pairs a xy xz yz).toFinset ↔
    (xy = true ∧ i=a.x ∧ j=a.y) ∨ (xz = true ∧ i=a.x ∧ j=a.z) ∨ (yz = true ∧ i=a.y ∧ j=a.z) := by
  cases xy <;> cases xz <;> cases yz <;> simp [pairs]

private lemma small_components (a : Three G) (xy xz yz : Bool) (hd : a.disjointCoords) :
    let r := roots (a.pairs xy xz yz)
    (∀ i ∈ a.coords, r i ∈ a.coords) ∧ (∀ i ∉ a.coords, r i = i) ∧
      (univ.filter (fun i => r i ≠ i)).card = merged xy xz yz := by
  obtain ⟨x,y,z⟩ := a
  obtain ⟨hxy,hxz,hyz⟩ := hd
  change x ≠ y at hxy
  change x ≠ z at hxz
  change y ≠ z at hyz
  have hyx := hxy.symm
  have hzx := hxz.symm
  have hzy := hyz.symm
  let a : Three G := ⟨x,y,z⟩
  let r := roots (a.pairs xy xz yz)
  have away (i : G) (hi : i ∉ a.coords) : r i = i := by
    simp only [a,coords,mem_insert,mem_singleton,not_or] at hi
    obtain ⟨ix,iy,iz⟩ := hi
    cases xy <;> cases xz <;> cases yz <;> simp_all [r,a,pairs,roots,SplitMatroidFlags.join]
  have into (i : G) (hi : i ∈ a.coords) : r i ∈ a.coords := by
    simp only [a,coords,mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> cases xy <;> cases xz <;> cases yz <;>
      simp_all [r,a,pairs,roots,SplitMatroidFlags.join,coords]
  refine ⟨into,away,?_⟩
  change (univ.filter (fun i => r i ≠ i)).card = _
  have he : univ.filter (fun i => r i ≠ i) = a.coords.filter (fun i => r i ≠ i) := by
    ext i
    by_cases hi : i ∈ a.coords <;> simp [hi,away]
  rw [he]
  cases xy <;> cases xz <;> cases yz <;>
    simp_all [r,a,pairs,roots,SplitMatroidFlags.join,coords,merged,filter_insert,filter_singleton]

lemma row_dimension (a : Three G) (hd : a.disjointCoords) (R : Three (Finset G))
    (apart : Disjoint a.coords R.unionCols) :
    Module.finrank ℝ (directions (edges a R)) = R.unionCols.card +
      merged (decide (R.x ∩ R.y).Nonempty) (decide (R.x ∩ R.z).Nonempty) (decide (R.y ∩ R.z).Nonempty) := by
  classical
  let xy := decide (R.x ∩ R.y).Nonempty
  let xz := decide (R.x ∩ R.z).Nonempty
  let yz := decide (R.y ∩ R.z).Nonempty
  let L := a.pairs xy xz yz
  have loc := small_components a xy xz yz hd
  rw [← loc.2.2]
  apply bipartite_rank (P := edges a R) (Q := L.toFinset) (r := roots L) apart
  · rintro ⟨i,j⟩ h
    rw [mem_edges] at h
    rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> simp [coords,unionCols,h]
  · intro j hj
    simp only [unionCols,mem_union] at hj
    rcases hj with (hx|hy)|hz
    · exact ⟨a.x,(mem_edges _ _).mpr (Or.inl ⟨rfl,hx⟩)⟩
    · exact ⟨a.y,(mem_edges _ _).mpr (Or.inr (Or.inl ⟨rfl,hy⟩))⟩
    · exact ⟨a.z,(mem_edges _ _).mpr (Or.inr (Or.inr ⟨rfl,hz⟩))⟩
  · intro i j ne
    simp only [L,pair_spec,xy,xz,yz,decide_eq_true_eq,mem_edges,Finset.Nonempty,mem_inter]
    grind
  · intro i
    rw [pair_spec]
    obtain ⟨hxy,hxz,hyz⟩ := hd
    grind
  · exact roots_correct L
  · exact loc.1
  · exact loc.2.1

end SplitMatroidFlags.Three
