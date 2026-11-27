module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
namespace MaTangCarousel
open Finset Real

structure Tournament (V : Type*) where
  arc : V → V → Bool
  loopless : ∀ x, arc x x = false
  orientation : ∀ {x y}, x≠y → arc x y = !(arc y x)

def next {l : ℕ} (i : Fin l) : Fin l :=
  ⟨(i.val+1)%l,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def hom {V : Type*} (T : Tournament V) {l : ℕ} (x : Fin l→V) : Bool :=
  decide (∀ i,T.arc (x i) (x (next i))=true)

def homCount {V : Type*} [Fintype V] (T : Tournament V) (l : ℕ) : ℕ :=
  ∑ x : Fin l→V, if hom T x then 1 else 0

noncomputable def density {V : Type*} [Fintype V] (T : Tournament V) (l : ℕ) : ℝ :=
  (homCount T l : ℝ)/(Fintype.card V : ℝ)^l

/-- The cycle density of the carousel limit, equation (11), for lengths congruent to two modulo four. -/
noncomputable def alpha (l : ℕ) : ℝ :=
  1/2^l-2*∑' k : ℕ,(1/(((2*k+1 : ℕ):ℝ)*π))^l

/-- All large blocks have mass z; any remaining mass forms the last block. -/
noncomputable def moment (l : ℕ) (z : ℝ) : ℝ :=
  (⌊z⁻¹⌋₊ : ℝ)*z^l+(1-(⌊z⁻¹⌋₊ : ℝ)*z)^l

/-- The defining graph of g_l, including its value at zero. -/
def Profile (l : ℕ) (d v : ℝ) : Prop :=
  (d=0 ∧ v=0) ∨ ∃ z : ℝ, 0<z ∧ z≤1 ∧ d=moment 3 z/8 ∧ v=moment l z/2^l

/-- Ma and Tang, Conjecture 5.2, with the uniform asymptotic error in epsilon form. -/
def Conjecture : Prop :=
  ∀ l : ℕ, 6≤l → l%4=2 → ∀ ε : ℝ, 0<ε → ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] (T : Tournament V), N≤Fintype.card V →
      ∀ g : ℝ, Profile l (density T 3) g → 2^l*alpha l*g≤density T l+ε

end MaTangCarousel
