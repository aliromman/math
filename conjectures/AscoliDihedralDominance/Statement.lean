module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

namespace AscoliDihedral

/-- The semidirect product for the inversion action of the group of order two. -/
structure Dih (H : Type*) where
  reflection : Bool
  position : H
  deriving DecidableEq, Fintype

namespace Dih
variable {H : Type*} [AddCommGroup H]

def multiply (x y : Dih H) : Dih H := ⟨x.reflection ^^ y.reflection,
  if x.reflection then x.position - y.position else x.position + y.position⟩

def identity : Dih H := ⟨false,0⟩

def inverse (x : Dih H) : Dih H := ⟨x.reflection,if x.reflection then x.position else -x.position⟩

instance : Group (Dih H) where
  one := identity
  mul := multiply
  inv := inverse
  mul_assoc a b c := by
    change multiply (multiply a b) c = multiply a (multiply b c)
    obtain ⟨a,x⟩ := a
    obtain ⟨b,y⟩ := b
    obtain ⟨c,z⟩ := c
    cases a <;> cases b <;> cases c <;> simp [multiply,sub_eq_add_neg,add_assoc,add_comm,add_left_comm]
  one_mul a := by
    change multiply identity a = a
    obtain ⟨a,x⟩ := a
    cases a <;> simp [multiply,identity]
  mul_one a := by
    change multiply a identity = a
    obtain ⟨a,x⟩ := a
    cases a <;> simp [multiply,identity]
  inv_mul_cancel a := by
    change multiply (inverse a) a = identity
    obtain ⟨a,x⟩ := a
    cases a <;> simp [multiply,inverse,identity]

end Dih

/-- All products of two members of the set. -/
def products {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A ×ˢ A).image fun p => p.1 * p.2

/-- All right quotients of two members of the set. -/
def quotients {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A ×ˢ A).image fun p => p.1 * p.2⁻¹

/-- A uniform subset is more often product-dominant than quotient-dominant. -/
def ProductDominant (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Prop :=
  (Finset.univ.filter fun A : Finset G => (products A).card < (quotients A).card).card <
  (Finset.univ.filter fun A : Finset G => (quotients A).card < (products A).card).card

/-- Ascoli et al., Conjecture 1.6. -/
def Conjecture.{u} : Prop :=
  ∀ (H : Type u) [AddCommGroup H] [Fintype H] [DecidableEq H], (∃ h : H, 3 ≤ addOrderOf h) →
    ProductDominant (Dih H)

end AscoliDihedral
