module

public import conjectures.BorgSignedSets.Statement
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic

@[expose] public section
namespace BorgSignedSets

variable {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ] {k : ℕ} [NeZero k]

private abbrev Meets (D : Finset (τ → ZMod k)) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∃ i, x i = y i

/-- Every transversal of the word cube meets a maximum intersecting family. -/
private theorem hits_rows (D : Finset (τ → ZMod k)) (hi : Meets D)
    (hc : D.card = k ^ (Fintype.card τ - 1))
    (row : ZMod k → τ → ZMod k) (hinj : ∀ j, Function.Injective (fun t => row t j)) :
    ∃ t, row t ∈ D := by
  classical
  let shift (u : D × ZMod k) : τ → ZMod k := fun j => u.1.val j - row u.2 j
  have hshift : Function.Injective shift := by
    rintro ⟨⟨x,hx⟩,t⟩ ⟨⟨y,hy⟩,s⟩ heq
    obtain ⟨j,hj⟩ := hi x hx y hy
    have he := congrFun heq j
    change x j - row t j = y j - row s j at he
    have ht : t = s := hinj j (by simpa [hj] using he)
    subst s
    have hxy : x = y := by
      funext j
      exact sub_left_inj.mp (congrFun heq j)
    subst y
    rfl
  have ht : 0 < Fintype.card τ := Fintype.card_pos
  have hsize : Fintype.card (D × ZMod k) = Fintype.card (τ → ZMod k) := by
    simp only [Fintype.card_prod, Fintype.card_coe, ZMod.card, Fintype.card_fun, hc]
    rw [← pow_succ, Nat.sub_add_cancel ht]
  obtain ⟨⟨⟨x,hx⟩,t⟩,hxt⟩ := ((Fintype.bijective_iff_injective_and_card shift).2 ⟨hshift,hsize⟩).2 (fun _ => 0)
  have hrow : x = row t := by
    funext j
    exact sub_eq_zero.mp (congrFun hxt j)
  exact ⟨t, hrow ▸ hx⟩

omit [Fintype τ] [DecidableEq τ] [Nonempty τ] [NeZero k] in
/-- Two words that disagree everywhere extend to a transversal. -/
private theorem extend_rows (hk : 2 ≤ k) (x y : τ → ZMod k) (hd : ∀ j, x j ≠ y j) :
    ∃ row : ZMod k → τ → ZMod k, row 0 = x ∧ row 1 = y ∧
      ∀ j, Function.Injective (fun t => row t j) := by
  let : Fact (1 < k) := ⟨hk⟩
  let row (t : ZMod k) (j : τ) := Equiv.swap 1 (y j - x j) t + x j
  refine ⟨row, ?_, ?_, ?_⟩
  · funext j
    have hne : (0 : ZMod k) ≠ y j - x j := Ne.symm (sub_ne_zero.mpr (Ne.symm (hd j)))
    simp [row, Equiv.swap_apply_of_ne_of_ne zero_ne_one hne]
  · funext j
    simp [row]
  · intro j a b hab
    exact (Equiv.swap 1 (y j - x j)).injective (add_right_cancel hab)

/-- Swapping a single column between two rows preserves the occupied row count. -/
private theorem propagate (D : Finset (τ → ZMod k)) (hi : Meets D)
    (hc : D.card = k ^ (Fintype.card τ - 1)) (hk : 2 ≤ k) (i : τ)
    (x y : τ → ZMod k) (hd : ∀ j, x j ≠ y j) (hx : x ∈ D)
    (hx' : Function.update x i (y i) ∉ D) : Function.update y i (x i) ∈ D := by
  classical
  obtain ⟨row, hz, ho, hr⟩ := extend_rows hk x y hd
  let other (t : ZMod k) (j : τ) := if j = i then row ((Equiv.swap 0 1) t) j else row t j
  have hj (j : τ) : Function.Injective (fun t => other t j) := by
    by_cases h : j = i
    · intro a b hab
      apply (Equiv.swap (0 : ZMod k) 1).injective
      apply hr i
      simpa [other, h] using hab
    · simpa [other, h] using hr j
  obtain ⟨t,ht⟩ := hits_rows D hi hc other hj
  by_cases h₀ : t=0
  · subst t
    have hz' : other 0 = Function.update x i (y i) := by
      funext j
      by_cases hj : j=i <;> simp [other, hj, hz, ho, Function.update]
    exact False.elim (hx' (hz' ▸ ht))
  by_cases h₁ : t=1
  · subst t
    have ho' : other 1 = Function.update y i (x i) := by
      funext j
      by_cases hj : j=i <;> simp [other, hj, hz, ho, Function.update]
    exact ho' ▸ ht
  have hfix : (Equiv.swap 0 1) t = t := Equiv.swap_apply_of_ne_of_ne h₀ h₁
  obtain ⟨j,hj⟩ := hi (other t) ht x hx
  have hrow : row t j = row 0 j := by simpa [other, hfix, hz] using hj
  exact False.elim (h₀ (hr j hrow))

omit [Nonempty τ] in
private theorem boundary (D : Finset (τ → ZMod k)) (hi : Meets D) (hk : 2 ≤ k)
    (hc : D.card = k ^ (Fintype.card τ - 1)) :
    ∃ x ∈ D, ∃ (i : τ) (b : ZMod k), Function.update x i b ∉ D := by
  classical
  let : Fact (1 < k) := ⟨hk⟩
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < D.card by rw [hc]; exact pow_pos (by omega) _)
  by_contra! h
  let y (j : τ) := x j + 1
  have hybrid (S : Finset τ) : (fun j => if j ∈ S then y j else x j) ∈ D := by
    induction S using Finset.induction_on with
    | empty => simpa using hx
    | @insert i S _ ih =>
      have heq : (fun j => if j ∈ insert i S then y j else x j) =
          Function.update (fun j => if j ∈ S then y j else x j) i (y i) := by
        funext j
        by_cases he : j=i <;> simp [he, Function.update]
      rw [heq]
      exact h _ ih i (y i)
  have hy : y ∈ D := by simpa using hybrid Finset.univ
  obtain ⟨j,hj⟩ := hi x hx y hy
  simp [y] at hj

private theorem move (D : Finset (τ → ZMod k)) (hi : Meets D)
    (hc : D.card = k ^ (Fintype.card τ - 1)) (hk : 2 ≤ k) (i : τ)
    (x z : τ → ZMod k) (b : ZMod k) (hab : x i ≠ b)
    (hd : ∀ j, j ≠ i → x j ≠ z j) (hx : x ∈ D)
    (hx' : Function.update x i b ∉ D) :
    Function.update z i (x i) ∈ D ∧ Function.update z i b ∉ D := by
  let y := Function.update z i b
  have hdis (j : τ) : x j ≠ y j := by
    by_cases hj : j=i
    · simpa [y,hj] using hab
    · simpa [y,hj] using hd j hj
  have hxb : Function.update x i (y i) ∉ D := by simpa [y] using hx'
  constructor
  · simpa [y] using propagate D hi hc hk i x y hdis hx hxb
  · intro hy
    obtain ⟨j,hj⟩ := hi x hx y hy
    exact hdis j hj

private theorem third_label (hk : 3 ≤ k) (a b : ZMod k) :
    ∃ c : ZMod k, c ≠ a ∧ c ≠ b := by
  classical
  have hpair : ({a,b} : Finset (ZMod k)).card ≤ 2 := Finset.card_insert_le ..
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a,b} : Finset (ZMod k)).card < Finset.univ.card by simpa using hpair.trans_lt hk)
  exact ⟨c, by simpa using hc⟩

private theorem full_slab (D : Finset (τ → ZMod k)) (hi : Meets D)
    (hc : D.card = k ^ (Fintype.card τ - 1)) (hk : 2 ≤ k)
    (good : 3 ≤ k ∨ Fintype.card τ ≤ 2) (i : τ) (x : τ → ZMod k) (b : ZMod k)
    (hx : x ∈ D) (hx' : Function.update x i b ∉ D) :
    ∀ z : τ → ZMod k, z i = x i → z ∈ D := by
  classical
  have hab : x i ≠ b := by
    rintro rfl
    exact hx' (by simpa using hx)
  intro z hz
  rcases good with hk3 | hτ
  · choose w hwx hwz using (fun j => third_label hk3 (x j) (z j))
    have hfirst := move D hi hc hk i x w b hab (fun j _ => (hwx j).symm) hx hx'
    let u := Function.update w i (x i)
    have hu : u i = x i := by simp [u]
    have hu' : Function.update u i b ∉ D := by simpa [u] using hfirst.2
    have hm := (move D hi hc hk i u z b (hu ▸ hab)
      (fun j hj => by simpa [u, hj] using hwz j) hfirst.1 hu').1
    simpa [hu, ← hz] using hm
  · by_cases he : x = z
    · simpa [← he] using hx
    obtain ⟨t,ht⟩ : ∃ t, x t ≠ z t := Function.ne_iff.mp he
    have hti : t ≠ i := fun h => ht (h ▸ hz.symm)
    have hd (j : τ) (hj : j ≠ i) : x j ≠ z j := by
      have hjt : j = t := by
        by_contra hne
        have hlarge := Finset.card_le_univ ({i,t,j} : Finset τ)
        simp [Ne.symm hti, Ne.symm hj, Ne.symm hne] at hlarge
        omega
      simpa [hjt] using ht
    have hm := (move D hi hc hk i x z b hab hd hx hx').1
    simpa [← hz] using hm

/-- At alphabet size greater than two, a maximum intersecting family of words is a star.
The same conclusion holds for at most two coordinates. -/
theorem fullSupport_star (k : ℕ) [NeZero k] (hk : 2 ≤ k) (D : Finset (τ → ZMod k))
    (hi : ∀ x ∈ D, ∀ y ∈ D, ∃ i, x i = y i)
    (hc : D.card = k ^ (Fintype.card τ - 1)) :
    (∃ i : τ, ∃ a : ZMod k, ∀ x, x ∈ D ↔ x i = a) ∨ (k = 2 ∧ 3 ≤ Fintype.card τ) := by
  classical
  let : Fact (1 < k) := ⟨hk⟩
  by_cases hbad : k = 2 ∧ 3 ≤ Fintype.card τ
  · exact Or.inr hbad
  left
  have good : 3 ≤ k ∨ Fintype.card τ ≤ 2 := by omega
  obtain ⟨x,hx,i,b,hb⟩ := boundary D hi hk hc
  have hslab := full_slab D hi hc hk good i x b hx hb
  refine ⟨i, x i, fun z => ⟨?_, hslab z⟩⟩
  intro hz
  by_contra hne
  let w := Function.update (fun j => z j + 1) i (x i)
  have hw : w ∈ D := hslab w (by simp [w])
  obtain ⟨j,hj⟩ := hi z hz w hw
  by_cases he : j = i
  · exact hne (by simpa [w, he] using hj)
  · simp [w, he] at hj

end BorgSignedSets
