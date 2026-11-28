module

public import conjectures.GallianRusin.ThreePrimes
import Mathlib.Tactic.NormNum

@[expose] public section
namespace GallianRusinDice
open GallianRusin Polynomial Finset

/-- Coefficient lists for the nontrivial cyclotomic factors of a standard die. -/
def table : ℕ → List ℤ
  | 7 => [1,1,1,1,1,1,1]
  | 21 => [1,-1,0,1,-1,0,1,0,-1,1,0,-1,1]
  | 35 => [1,-1,0,0,0,1,-1,1,-1,0,1,-1,1,-1,1,0,-1,1,-1,1,0,0,0,-1,1]
  | 105 => [1,1,1,0,0,-1,-1,-2,-1,-1,0,0,1,1,1,1,1,1,0,0,-1,0,-1,0,-1,0,-1,0,-1,0,0,1,1,1,1,1,1,0,0,-1,-1,-2,-1,-1,0,0,1,1,1]
  | i => commonFactor i

theorem table3 : polynomial (table 3)=cyclotomic 3 ℤ :=
  commonFactor_3

theorem table5 : polynomial (table 5)=cyclotomic 5 ℤ :=
  commonFactor_5

theorem table7 : polynomial (table 7)=cyclotomic 7 ℤ :=
  polynomial_prime 7 (by decide)

theorem table15 : polynomial (table 15)=cyclotomic 15 ℤ :=
  commonFactor_15

theorem table21 : polynomial (table 21)=cyclotomic 21 ℤ := by
  have a := table_product table (m := 21) [21,3,7] (by decide)
  have b := standard_factors (m := 21) (by decide) [21,3,7] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table3,table7] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

theorem table35 : polynomial (table 35)=cyclotomic 35 ℤ := by
  have a := table_product table (m := 35) [35,5,7] (by decide)
  have b := standard_factors (m := 35) (by decide) [35,5,7] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table5,table7] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

theorem table105 : polynomial (table 105)=cyclotomic 105 ℤ := by
  have a := table_product table (m := 105) [105,3,5,7,15,21,35] (by decide)
  have b := standard_factors (m := 105) (by decide) [105,3,5,7,15,21,35] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table3,table5,table7,table15,table21,table35] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

export GallianRusin (Code instDecidableEqCode)

namespace Code
export GallianRusin.Code (mk a b c d rec recOn casesOn noConfusion noConfusionType ctorIdx)
namespace mk
export GallianRusin.Code.mk (inj injEq noConfusion sizeOf_spec)
end mk
end Code

def coefficients (c : Code) : List ℤ := multiply [table 3,table 5,table 7,
  power (table 15) c.a,power (table 21) c.b,power (table 35) c.c,power (table 105) c.d]

noncomputable def assemble (c : Code) : ℤ[X] := polynomial (coefficients c)

theorem assemble_eq (c : Code) : assemble c = cyclotomic 3 ℤ * (cyclotomic 5 ℤ *
    (cyclotomic 7 ℤ * (cyclotomic 15 ℤ ^ c.a * (cyclotomic 21 ℤ ^ c.b *
    (cyclotomic 35 ℤ ^ c.c * cyclotomic 105 ℤ ^ c.d))))) := by
  simp [assemble,coefficients,polynomial_multiply,polynomial_power,table3,table5,table7,
    table15,table21,table35,table105]

theorem standard_eq : standard 105=assemble ⟨1,1,1,1⟩ := by
  rw [assemble_eq,←standard_factors (m := 105) (by decide) [3,5,7,15,21,35,105] (by decide) (by decide)]
  simp

end GallianRusinDice
