module

public import conjectures.AscoliDihedralDominance.Statement
public import conjectures.AscoliDihedralDominance.Matchings
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

@[expose] public section

open Equiv Finset
namespace AscoliDihedral

variable {X : Type*} [Fintype X] [DecidableEq X]

def bitsEquiv (X : Type*) [Fintype X] [DecidableEq X] : Finset X ≃ (X → Bool) where
  toFun A x := decide (x ∈ A)
  invFun f := univ.filter fun x => f x = true
  left_inv A := by ext; simp
  right_inv f := by funext x; simp

def avoids (p : X → X) (A : Finset X) : Prop := ∀ x ∈ A, p x ∉ A

omit [Fintype X] [DecidableEq X] in
theorem avoids_and {p q : X → X} {A : Finset X} :
    avoids p A ∧ avoids q A ↔ ∀ x ∈ A, p x ∉ A ∧ q x ∉ A := by
  unfold avoids
  exact ⟨fun h x hx => ⟨h.1 _ hx,h.2 _ hx⟩,fun h => ⟨fun x hx => (h x hx).1,fun x hx => (h x hx).2⟩⟩

theorem avoids_bits (p : X → X) (A : Finset X) :
    avoids p A ↔ coloringOK p (bitsEquiv X A) := by
  simp [avoids,coloringOK,bitsEquiv]
  exact forall_congr' (fun _ => imp_iff_not_or)

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def productStep (g : G) : Perm G where
  toFun x := x⁻¹ * g
  invFun x := g * x⁻¹
  left_inv x := by group
  right_inv x := by group

def quotientStep (g : G) := Equiv.mulLeft g

omit [Fintype G] in
theorem missing_product (g : G) (A : Finset G) :
    g ∉ products A ↔ avoids (productStep g) A := by
  simp only [products,mem_image,mem_product,Prod.exists,not_exists]
  constructor
  · intro h x hx hy
    exact h x (x⁻¹*g) ⟨⟨hx,hy⟩,by group⟩
  · intro h x y ⟨hxy,he⟩
    apply h x hxy.1
    change x⁻¹ * g ∈ A
    rw [←he]
    simpa using hxy.2

omit [Fintype G] in
theorem missing_quotient (g : G) (A : Finset G) :
    g ∉ quotients A ↔ avoids (quotientStep g) A := by
  simp only [quotients,mem_image,mem_product,Prod.exists,not_exists]
  constructor
  · intro h y hy hx
    exact h (g*y) y ⟨⟨hx,hy⟩,by group⟩
  · intro h x y ⟨hxy,he⟩
    apply h y hxy.2
    change g*y ∈ A
    rw [←he]
    simpa using hxy.1

private theorem count_by_equiv (T : Finset X → Prop) [DecidablePred T]
    (U : (X → Bool) → Prop) (h : ∀ A, T A ↔ U (bitsEquiv X A)) :
    (univ.filter T).card = Nat.card {f : X → Bool // U f} := by
  classical
  rw [←Fintype.card_subtype, ←Nat.card_eq_fintype_card]
  exact Nat.card_congr ((bitsEquiv X).subtypeEquiv h)

def missingProducts (g : G) : Finset (Finset G) := univ.filter fun A => g ∉ products A

def missingQuotients (g : G) : Finset (Finset G) := univ.filter fun A => g ∉ quotients A

theorem missingProducts_card (g : G) :
    (missingProducts g).card = Nat.card {f : G → Bool // coloringOK (productStep g) f} :=
  count_by_equiv _ _ (fun A => (missing_product g A).trans (avoids_bits _ A))

theorem missingQuotients_card (g : G) :
    (missingQuotients g).card = Nat.card {f : G → Bool // coloringOK (quotientStep g) f} :=
  count_by_equiv _ _ (fun A => (missing_quotient g A).trans (avoids_bits _ A))

theorem miss_involution_sq {g : G} (hne : g ≠ 1) (hg : g*g = 1) :
    (missingQuotients g).card ^ 2 = 3^Fintype.card G := by
  rw [missingQuotients_card]
  apply matching_card_sq
  · intro x
    change g*(g*x) = x
    rw [←mul_assoc,hg,one_mul]
  · intro x h
    apply hne
    exact mul_right_cancel (show g*x = 1*x by simpa [quotientStep] using h)

omit [DecidableEq G] in
theorem productStep_fixedTwice (g : G) :
    fixedTwice (productStep g) = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  classical
  have he (x : G) : productStep g (productStep g x) = x ↔
      x ∈ Subgroup.centralizer ({g} : Set G) := by
    change (x⁻¹*g)⁻¹*g = x ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_rev, inv_inv, mul_assoc]
    exact inv_mul_eq_iff_eq_mul
  rw [fixedTwice, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp [he]

omit [DecidableEq G] in
theorem noncentral_fixed_le (g : G) (hg : g ∉ Subgroup.center G) :
    2 * fixedTwice (productStep g) ≤ Fintype.card G := by
  let K := Subgroup.centralizer ({g} : Set G)
  have hn : K ≠ ⊤ := by
    intro hK
    apply hg
    rw [Subgroup.mem_center_iff]
    intro x
    have ht := Subgroup.mem_top x
    rw [←hK] at ht
    exact Subgroup.mem_centralizer_singleton_iff.mp ht
  have ht : 2 ≤ K.index := by
    have h₁ := K.index_ne_zero
    have h₂ : K.index ≠ 1 := fun h => hn (Subgroup.index_eq_one.mp h)
    omega
  rw [productStep_fixedTwice, ←Nat.card_eq_fintype_card, ←K.index_mul_card]
  exact Nat.mul_le_mul_right _ ht

omit [Fintype G] [DecidableEq G] in
private def matchGraph (g h : G) (g₀ : g ≠ 1) (h₀ : h ≠ 1)
    (g₂ : g*g = 1) (h₂ : h*h = 1) : SimpleGraph G where
  Adj x y := y = g*x ∨ y = h*x
  symm := by
    constructor
    rintro x y (rfl|rfl)
    · exact Or.inl (by rw [←mul_assoc,g₂,one_mul])
    · exact Or.inr (by rw [←mul_assoc,h₂,one_mul])
  loopless := ⟨fun x he => by
    rcases he with he|he
    · exact g₀ (mul_right_cancel (show g*x = 1*x by simpa using he.symm))
    · exact h₀ (mul_right_cancel (show h*x = 1*x by simpa using he.symm))⟩

theorem two_missing_fourth {g h : G} (g₀ : g ≠ 1) (h₀ : h ≠ 1)
    (g₂ : g*g = 1) (h₂ : h*h = 1) (gh : g ≠ h) :
    (missingQuotients g ∩ missingQuotients h).card ^ 4 ≤ 7^(Fintype.card G) := by
  let K := matchGraph g h g₀ h₀ g₂ h₂
  have deg (x : G) : (K.neighborSet x).ncard = 2 := by
    have he : K.neighborSet x = {g*x,h*x} := by ext; rfl
    rw [he, Set.ncard_pair (fun h' => gh (mul_right_cancel h'))]
  have eq : missingQuotients g ∩ missingQuotients h =
      univ.filter (fun A : Finset G => g ∉ quotients A ∧ h ∉ quotients A) := by
    ext A
    simp [missingQuotients]
  rw [eq]
  convert independent_fourth_bound K deg using 2
  apply count_by_equiv
  intro A
  rw [missing_quotient,missing_quotient,avoids_bits,avoids_bits]
  constructor
  · rintro ⟨h₁,h₂⟩ x y (rfl|rfl)
    · exact h₁ x
    · exact h₂ x
  · intro H
    exact ⟨fun x => H _ _ (Or.inl rfl),fun x => H _ _ (Or.inr rfl)⟩

end AscoliDihedral
