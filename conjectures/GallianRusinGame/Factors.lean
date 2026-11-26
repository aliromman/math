module

public import conjectures.GallianRusinGame.Coefficients
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum

@[expose] public section
namespace GallianRusinGame
open Polynomial Finset

/-- Coefficient lists for the nontrivial cyclotomic factors of a standard die. -/
def table : ℕ → List ℤ
  | 2 => [1,1]
  | 3 => [1,1,1]
  | 5 => [1,1,1,1,1]
  | 6 => [1,-1,1]
  | 10 => [1,-1,1,-1,1]
  | 15 => [1,-1,0,1,-1,1,0,-1,1]
  | 30 => [1,1,0,-1,-1,-1,0,1,1]
  | _ => []

def multiply : List (List ℤ) → List ℤ
  | [] => [1]
  | s::t => times s (multiply t)

theorem polynomial_multiply (v : List (List ℤ)) :
    polynomial (multiply v)=(v.map polynomial).prod := by
  induction v with
  | nil => simp [multiply,polynomial]
  | cons a v ih => simp [multiply,polynomial_mul,ih]

private theorem standard_factors {m} (pos : 0<m) (s : List ℕ) (hs : s.Nodup)
    (eq : s.toFinset=m.divisors.erase 1) : (s.map (cyclotomic · ℤ)).prod=standard m := by
  rw [←List.prod_toFinset _ hs,eq,prod_cyclotomic_eq_geom_sum pos ℤ]
  rfl

private theorem table_product {m} (s : List ℕ) (h : multiply (s.map table)=List.replicate m 1) :
    (s.map (fun d ↦ polynomial (table d))).prod=standard m := by
  rw [←polynomial_standard,←h,polynomial_multiply,List.map_map]
  rfl

theorem table2 : polynomial (table 2)=cyclotomic 2 ℤ := by
  have a := table_product (m := 2) [2] (by decide)
  have b := standard_factors (m := 2) (by decide) [2] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  exact a.trans b.symm

theorem table3 : polynomial (table 3)=cyclotomic 3 ℤ := by
  have a := table_product (m := 3) [3] (by decide)
  have b := standard_factors (m := 3) (by decide) [3] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  exact a.trans b.symm

theorem table5 : polynomial (table 5)=cyclotomic 5 ℤ := by
  have a := table_product (m := 5) [5] (by decide)
  have b := standard_factors (m := 5) (by decide) [5] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  exact a.trans b.symm

theorem table6 : polynomial (table 6)=cyclotomic 6 ℤ := by
  have a := table_product (m := 6) [6,2,3] (by decide)
  have b := standard_factors (m := 6) (by decide) [6,2,3] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table2,table3] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

theorem table10 : polynomial (table 10)=cyclotomic 10 ℤ := by
  have a := table_product (m := 10) [10,2,5] (by decide)
  have b := standard_factors (m := 10) (by decide) [10,2,5] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table2,table5] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

theorem table15 : polynomial (table 15)=cyclotomic 15 ℤ := by
  have a := table_product (m := 15) [15,3,5] (by decide)
  have b := standard_factors (m := 15) (by decide) [15,3,5] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table3,table5] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

theorem table30 : polynomial (table 30)=cyclotomic 30 ℤ := by
  have a := table_product (m := 30) [30,2,3,5,6,10,15] (by decide)
  have b := standard_factors (m := 30) (by decide) [30,2,3,5,6,10,15] (by decide) (by decide)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at a b
  rw [table2,table3,table5,table6,table10,table15] at a
  apply mul_right_cancel₀ _ (a.trans b.symm)
  apply_rules [mul_ne_zero,Polynomial.cyclotomic_ne_zero]

structure Code where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

def coefficients (c : Code) : List ℤ := multiply [table 2,table 3,table 5,
  power (table 6) c.a,power (table 10) c.b,power (table 15) c.c,power (table 30) c.d]

noncomputable def assemble (c : Code) : ℤ[X] := polynomial (coefficients c)

theorem assemble_eq (c : Code) : assemble c = cyclotomic 2 ℤ * (cyclotomic 3 ℤ *
    (cyclotomic 5 ℤ * (cyclotomic 6 ℤ ^ c.a * (cyclotomic 10 ℤ ^ c.b *
    (cyclotomic 15 ℤ ^ c.c * cyclotomic 30 ℤ ^ c.d))))) := by
  simp [assemble,coefficients,polynomial_multiply,polynomial_power,table2,table3,table5,
    table6,table10,table15,table30]

theorem standard_eq : standard 30=assemble ⟨1,1,1,1⟩ := by
  rw [assemble_eq,←standard_factors (m := 30) (by decide) [2,3,5,6,10,15,30] (by decide) (by decide)]
  simp

end GallianRusinGame
