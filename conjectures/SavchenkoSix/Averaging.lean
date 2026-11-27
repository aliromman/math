module

public import conjectures.SavchenkoSix.Transport
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace SavchenkoSix
open Finset Matrix

theorem excess_eq {V : Type*} [Fintype V] [DecidableEq V] (T : Tournament V) (k : ℕ) :
    excessOn T.sign univ k=minorSum T k-((Fintype.card V).choose k:ℤ) := by
  simp [excessOn,excess,minorSum,sum_sub_distrib,card_powersetCard]

/-- Each six-set lies in n−6 seven-sets. Each four-set lies in binom(n−4,3). -/
theorem averaged_bound {n : ℕ} (T : Tournament (Fin n)) (hn : 7≤n)
    (cert : ∀ b : Fin 15→Bool, excessOn (bitsMatrix b) univ 6≤3*excessOn (bitsMatrix b) univ 4) :
    excessOn T.sign univ 6≤((n-4).choose 2:ℤ)*excessOn T.sign univ 4 := by
  let X : Finset (Fin n) := univ
  have localBound (U : Finset (Fin n)) (hU : U∈X.powersetCard 7) :
      excessOn T.sign U 6≤3*excessOn T.sign U 4 := by
    let e := (U.orderEmbOfFin (mem_powersetCard.mp hU).2).toEmbedding
    have eu : univ.map e=U := U.map_orderEmbOfFin_univ _
    obtain ⟨b,h⟩ := normalize_seven T e
    rw [←eu,excessOn_map,excessOn_map,h 4,h 6]
    exact cert b
  have h := sum_le_sum localBound
  rw [←mul_sum] at h
  have six := sevenfold_sum X 6 (by decide) (excess T.sign)
  have four := sevenfold_sum X 4 (by decide) (excess T.sign)
  change (∑ U∈X.powersetCard 7,excessOn T.sign U 6) = _ at six
  change (∑ U∈X.powersetCard 7,excessOn T.sign U 4) = _ at four
  rw [six,four] at h
  have xc : X.card=n := by simp [X]
  simp only [xc,show 7-6=1 by decide,show 7-4=3 by decide,Nat.choose_one_right] at h
  change ((n-6:ℕ):ℤ)*excessOn T.sign univ 6≤3*(((n-4).choose 3:ℤ)*excessOn T.sign univ 4) at h
  have choose : ((n-4).choose 3:ℤ)*3=((n-4).choose 2:ℤ)*((n-6:ℕ):ℤ) := by
    exact_mod_cast (show (n-4).choose 3*3=(n-4).choose 2*(n-6) by
      simpa only [Nat.sub_sub] using Nat.choose_succ_right_eq (n-4) 2)
  rw [show 3*(((n-4).choose 3:ℤ)*excessOn T.sign univ 4)=
    ((n-6:ℕ):ℤ)*(((n-4).choose 2:ℤ)*excessOn T.sign univ 4) by
      linear_combination excessOn T.sign univ 4 * choose] at h
  exact (mul_le_mul_iff_right₀ (show 0<((n-6:ℕ):ℤ) by omega)).mp h

theorem choose_margin (n : ℕ) (hn : 7≤n) :
    (n.choose 2:ℤ)-14-((n-4).choose 2:ℤ)=4*(n:ℤ)-24 := by
  have id (m : ℕ) : (m.choose 2:ℤ)*2=(m:ℤ)*((m-1:ℕ):ℤ) := by
    exact_mod_cast (show m.choose 2*2=m*(m-1) by simpa using Nat.choose_succ_right_eq m 1)
  have a := id n
  have b := id (n-4)
  simp only [Nat.cast_sub (show 1≤n by omega),Nat.cast_one] at a
  simp only [Nat.cast_sub (show 1≤n-4 by omega),Nat.cast_sub (show 4≤n by omega),
    Nat.cast_one,Nat.cast_ofNat] at b
  linarith only [a,b]

end SavchenkoSix
end
