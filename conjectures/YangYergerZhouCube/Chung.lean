module

public import conjectures.YangYergerZhouCube.Moves

@[expose] public section
namespace YangYergerZhouCube

open Finset

variable {V ι : Type*} [DecidableEq ι] {edge : V → V → Prop}

def cubeEdges (edge : V → V → Prop) (s : Finset ι) (node : Finset ι → V) : Prop :=
  ∀ x ⊆ s, ∀ i ∈ s, i ∉ x → edge (node (insert i x)) (node x)

def total (s : Finset ι) (p : Finset ι → ℕ) := ∑ x ∈ s.powerset, p x

def ceilingMass (s : Finset ι) (p : Finset ι → ℕ) := ∑ x ∈ s.powerset, (p x+1)/2

private theorem partial_sum {α : Type*} (s : Finset α) (p : α → ℕ) (t : ℕ) (h : t ≤ ∑ x ∈ s, p x) :
    ∃ u : α → ℕ, (∀ x ∈ s, u x ≤ p x) ∧ (∑ x ∈ s, u x) = t := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => exact ⟨fun _ => 0, by simp, by simpa using (show t=0 by simpa using h).symm⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx] at h
    let k := min t (p x)
    obtain ⟨u,hu,hs⟩ := ih (t-k) (by dsimp [k]; omega)
    let v y := if y=x then k else u y
    refine ⟨v,?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · simp [v,k]
      · simp [v,ne_of_mem_of_not_mem hy hx,hu y hy]
    · have eq : ∑ y ∈ s, v y = ∑ y ∈ s, u y := Finset.sum_congr rfl fun y hy => by
        simp [v,ne_of_mem_of_not_mem hy hx]
      rw [Finset.sum_insert hx,eq,hs]
      simp only [v,ite_eq_left rfl]
      dsimp [k]
      omega

private theorem pile {u : V} {n m : ℕ} (h : n≤m) :
    Supplies edge (Multiset.replicate m u) (Multiset.replicate n u) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk,Multiset.replicate_add]
  exact .drop _

omit [DecidableEq ι] in

private theorem counts (s : Finset ι) (p : Finset ι → ℕ) :
    total s (fun x => p x/2) + ceilingMass s p = total s p ∧
    ceilingMass s p ≤ total s (fun x => p x/2) + 2^s.card ∧ ceilingMass s p ≤ total s p := by
  unfold total ceilingMass
  constructor
  · rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by omega
  constructor
  · calc
      _ ≤ ∑ x ∈ s.powerset, (p x/2+1) := Finset.sum_le_sum fun x _ => by omega
      _ = _ := by simp [Finset.sum_add_distrib]
  · exact Finset.sum_le_sum fun x _ => by omega

theorem cube_near {s : Finset ι} {i : ι} {node : Finset ι → V}
    (es : cubeEdges edge (insert i s) node) : cubeEdges edge s node := by
  intro x hx j hj h
  exact es x (hx.trans (Finset.subset_insert ..)) j (Finset.mem_insert_of_mem hj) h

theorem cube_far {s : Finset ι} {i : ι} (hi : i∉s) {node : Finset ι → V}
    (es : cubeEdges edge (insert i s) node) : cubeEdges edge s (fun x => node (insert i x)) := by
  intro x hx j hj h
  have ji := ne_of_mem_of_not_mem hj hi
  simpa [Finset.insert_comm] using es (insert i x) (Finset.insert_subset_insert _ hx) j
    (Finset.mem_insert_of_mem hj) (by simp [ji,h])

theorem cube_cross {s : Finset ι} {i : ι} (hi : i∉s) {node : Finset ι → V}
    (es : cubeEdges edge (insert i s) node) (x : Finset ι) (hx : x ∈ s.powerset) :
    edge (node (insert i x)) (node x) := by
  have sub := Finset.mem_powerset.mp hx
  exact es x (sub.trans (Finset.subset_insert ..)) i (Finset.mem_insert_self ..) (fun h => hi (sub h))

/-- Chung's one-pebble and odd two-pebble bounds for a cube, with an explicit sequence of moves. -/
theorem chung (s : Finset ι) (node : Finset ι → V) (es : cubeEdges edge s node) (p : Finset ι → ℕ) :
    (2^s.card ≤ total s p → Supplies edge (pack s node p) {node ∅}) ∧
    (2^s.card < ceilingMass s p → Supplies edge (pack s node p) (Multiset.replicate 2 (node ∅))) := by
  induction s using Finset.induction_on generalizing node p with
  | empty =>
    simp only [Finset.card_empty,pow_zero,total,ceilingMass,pack,Finset.powerset_empty,Finset.sum_singleton]
    constructor <;> intro h
    · simpa only [Multiset.replicate_one] using (pile (edge := edge) (u := node ∅) h)
    · exact pile (by omega)
  | insert i s hi ih =>
    let q x := p (insert i x)
    let far x := node (insert i x)
    let d := 2^s.card
    have en : cubeEdges edge s node := cube_near es
    have ef : cubeEdges edge s far := cube_far hi es
    have ec := cube_cross hi es
    have e0 : edge (far ∅) (node ∅) := ec ∅ (by simp)
    have hn := counts s p
    have hf := counts s q
    rw [pack_split s hi node p]
    change (_ → Supplies edge (pack s node p + pack s far q) _) ∧ (_ → Supplies edge (pack s node p + pack s far q) _)
    have size : 2^(insert i s).card=2*d := by simp [hi,pow_succ,d,Nat.mul_comm]
    have nt : total (insert i s) p=total s p + total s q := by simp [total,Finset.sum_powerset_insert hi,q]
    have ct : ceilingMass (insert i s) p=ceilingMass s p + ceilingMass s q := by
      simp [ceilingMass,Finset.sum_powerset_insert hi,q]
    rw [size,nt,ct]
    constructor
    · intro h
      by_cases hb : d < ceilingMass s q
      · have pass := ((ih far ef q).2 hb).trans (Supplies.one e0)
        rw [add_comm]
        exact (Supplies.drop _).trans pass
      · let u x := q x/2
        have move := pack_transfer s node far p q u ec (fun x _ => by dsimp [u]; omega)
        have ready : d ≤ total s (fun x => p x+u x) := by
          simp only [total,Finset.sum_add_distrib] at *
          change d ≤ _ + ∑ x ∈ s.powerset, q x / 2
          omega
        exact (move.trans (.drop _)).trans ((ih node en _).1 ready)
    · intro h
      by_cases ha : d < ceilingMass s p
      · exact (Supplies.drop _).trans ((ih node en p).2 ha)
      · let t := d-total s p
        have cap : t ≤ total s (fun x => q x/2) := by dsimp [t,d] at *; omega
        obtain ⟨u,hu,hs⟩ := partial_sum s.powerset (fun x => q x/2) t cap
        have fits (x) (hx : x∈s.powerset) : 2*u x ≤ q x := by have := hu x hx; omega
        have move := pack_transfer s node far p q u ec fits
        have nearReady : d ≤ total s (fun x => p x+u x) := by
          simp only [total,Finset.sum_add_distrib,hs]
          dsimp [t,total]
          omega
        have remainEq : ceilingMass s (fun x => q x-2*u x) + t = ceilingMass s q := by
          rw [← hs]
          simp only [ceilingMass,← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x hx => by have := fits x hx; omega
        have farReady : d < ceilingMass s (fun x => q x-2*u x) := by dsimp [t] at *; omega
        have a := (ih node en _).1 nearReady
        have b := ((ih far ef _).2 farReady).trans (Supplies.one e0)
        exact move.trans (by simpa only [show Multiset.replicate 2 (node ∅) = {node ∅} + {node ∅} from rfl] using a.add b)

end YangYergerZhouCube
