module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Range

@[expose] public section
namespace BarequetRectangularPolyomino

abbrev Cell := ℕ × ℕ
abbrev Cells := Finset Cell

def east (p : Cell) : Cell := (p.1+1,p.2)
def north (p : Cell) : Cell := (p.1,p.2+1)

def adjacent (p q : Cell) : Prop := p=east q ∨ q=east p ∨ p=north q ∨ q=north p

instance (p q : Cell) : Decidable (adjacent p q) := by unfold adjacent; infer_instance

/-- Begin with one cell and attach cells along shared sides. -/
inductive Connected : Cells → Prop where
  | one (p : Cell) : Connected {p}
  | attach {P : Cells} {p q : Cell} (old : Connected P) (fresh : p∉P) (mem : q∈P)
      (side : adjacent p q) : Connected (insert p P)

def left (P : Cells) (p : Cell) : Prop := 0<p.1 ∧ (p.1-1,p.2)∈P
def below (P : Cells) (p : Cell) : Prop := 0<p.2 ∧ (p.1,p.2-1)∈P

instance (P : Cells) (p : Cell) : Decidable (left P p) := by unfold left; infer_instance
instance (P : Cells) (p : Cell) : Decidable (below P p) := by unfold below; infer_instance

/-- A run begins at an occupied cell whose predecessor on the line is empty. -/
def rowStarts (P : Cells) (y : ℕ) := P.filter fun p => p.2=y ∧ ¬left P p
def colStarts (P : Cells) (x : ℕ) := P.filter fun p => p.1=x ∧ ¬below P p

/-- Every row and column of the bounding rectangle has at least t gaps. -/
def Admissible (t w h : ℕ) (P : Cells) : Prop :=
  Connected P ∧ 0<w ∧ 0<h ∧ (∀ p∈P, p.1<w ∧ p.2<h) ∧
  (∀ y<h, t+1≤(rowStarts P y).card) ∧ (∀ x<w, t+1≤(colStarts P x).card)

def Minimum (t : ℕ) (P : Cells) : Prop :=
  ∀ w h : ℕ, ∀ Q : Cells, Admissible t w h Q → P.card≤Q.card

/-- Barequet, Madras and Peters, Section 3.3. -/
def Existence : Prop := ∃ t w h : ℕ, ∃ P : Cells,
  3<t ∧ w≠h ∧ Admissible t w h P ∧ Minimum t P

end BarequetRectangularPolyomino
