module

public import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

namespace SavchenkoSix.Seven

def entry4 (a b c d e f : ℤ) := (a*f-b*e+c*d)
def entry6 (a b c d e f g h i j k l m n o : ℤ) :=
  a*entry4 j k l m n o -b*entry4 g h i m n o+c*entry4 f h i k l o-d*entry4 f g i j l n+e*entry4 f g h j k m

def score (bits : Fin 15 → Bool) : ℤ :=
  let x12 : ℤ := if bits 0 then -1 else 1
  let x13 : ℤ := if bits 1 then -1 else 1
  let x23 : ℤ := if bits 2 then -1 else 1
  let x14 : ℤ := if bits 3 then -1 else 1
  let x24 : ℤ := if bits 4 then -1 else 1
  let x34 : ℤ := if bits 5 then -1 else 1
  let x15 : ℤ := if bits 6 then -1 else 1
  let x25 : ℤ := if bits 7 then -1 else 1
  let x35 : ℤ := if bits 8 then -1 else 1
  let x45 : ℤ := if bits 9 then -1 else 1
  let x16 : ℤ := if bits 10 then -1 else 1
  let x26 : ℤ := if bits 11 then -1 else 1
  let x36 : ℤ := if bits 12 then -1 else 1
  let x46 : ℤ := if bits 13 then -1 else 1
  let x56 : ℤ := if bits 14 then -1 else 1
  let f4 := (entry4 1 1 1 x12 x13 x23)^2 +
    (entry4 1 1 1 x12 x14 x24)^2 +
    (entry4 1 1 1 x12 x15 x25)^2 +
    (entry4 1 1 1 x12 x16 x26)^2 +
    (entry4 1 1 1 x13 x14 x34)^2 +
    (entry4 1 1 1 x13 x15 x35)^2 +
    (entry4 1 1 1 x13 x16 x36)^2 +
    (entry4 1 1 1 x14 x15 x45)^2 +
    (entry4 1 1 1 x14 x16 x46)^2 +
    (entry4 1 1 1 x15 x16 x56)^2 +
    (entry4 1 1 1 x23 x24 x34)^2 +
    (entry4 1 1 1 x23 x25 x35)^2 +
    (entry4 1 1 1 x23 x26 x36)^2 +
    (entry4 1 1 1 x24 x25 x45)^2 +
    (entry4 1 1 1 x24 x26 x46)^2 +
    (entry4 1 1 1 x25 x26 x56)^2 +
    (entry4 1 1 1 x34 x35 x45)^2 +
    (entry4 1 1 1 x34 x36 x46)^2 +
    (entry4 1 1 1 x35 x36 x56)^2 +
    (entry4 1 1 1 x45 x46 x56)^2 +
    (entry4 x12 x13 x14 x23 x24 x34)^2 +
    (entry4 x12 x13 x15 x23 x25 x35)^2 +
    (entry4 x12 x13 x16 x23 x26 x36)^2 +
    (entry4 x12 x14 x15 x24 x25 x45)^2 +
    (entry4 x12 x14 x16 x24 x26 x46)^2 +
    (entry4 x12 x15 x16 x25 x26 x56)^2 +
    (entry4 x13 x14 x15 x34 x35 x45)^2 +
    (entry4 x13 x14 x16 x34 x36 x46)^2 +
    (entry4 x13 x15 x16 x35 x36 x56)^2 +
    (entry4 x14 x15 x16 x45 x46 x56)^2 +
    (entry4 x23 x24 x25 x34 x35 x45)^2 +
    (entry4 x23 x24 x26 x34 x36 x46)^2 +
    (entry4 x23 x25 x26 x35 x36 x56)^2 +
    (entry4 x24 x25 x26 x45 x46 x56)^2 +
    (entry4 x34 x35 x36 x45 x46 x56)^2
  let f6 := (entry6 1 1 1 1 1 x12 x13 x14 x15 x23 x24 x25 x34 x35 x45)^2 +
    (entry6 1 1 1 1 1 x12 x13 x14 x16 x23 x24 x26 x34 x36 x46)^2 +
    (entry6 1 1 1 1 1 x12 x13 x15 x16 x23 x25 x26 x35 x36 x56)^2 +
    (entry6 1 1 1 1 1 x12 x14 x15 x16 x24 x25 x26 x45 x46 x56)^2 +
    (entry6 1 1 1 1 1 x13 x14 x15 x16 x34 x35 x36 x45 x46 x56)^2 +
    (entry6 1 1 1 1 1 x23 x24 x25 x26 x34 x35 x36 x45 x46 x56)^2 +
    (entry6 x12 x13 x14 x15 x16 x23 x24 x25 x26 x34 x35 x36 x45 x46 x56)^2
  3*(f4-35)-(f6-7)

/-- The five fixed entries are the edges of a directed path on the six remaining vertices. -/
private def unpack (b : Fin 10 → Bool) : Fin 15 → Bool :=
  ![false,b 0,false,b 1,b 2,false,b 3,b 4,b 5,false,b 6,b 7,b 8,b 9,false]

private def pack (b : Fin 15 → Bool) : Fin 10 → Bool :=
  ![b 1,b 3,b 4,b 6,b 7,b 8,b 10,b 11,b 12,b 13]

private def codeBits (n : ℕ) (i : Fin 10) : Bool := n.testBit i

/-- Check the interval of length 2^d that starts at lo. -/
private def check (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => p lo
  | d+1 => check p lo d && check p (lo+2^d) d

private theorem checked {p : ℕ → Bool} {d lo n : ℕ} (h : check p lo d = true)
    (hl : lo ≤ n) (hr : n < lo+2^d) : p n = true := by
  induction d generalizing lo with
  | zero =>
    have eq : lo=n := by simp only [pow_zero] at hr;omega
    simpa [check,eq] using h
  | succ d ih =>
    have both := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hr
    by_cases left : n < lo+2^d
    · exact ih both.1 hl left
    · exact ih both.2 (by omega) (by omega)

set_option maxHeartbeats 0 in
private theorem finite_check : check (fun n ↦ decide (0 ≤ score (unpack (codeBits n)))) 0 10 = true := by decide +kernel

private theorem packed_nonneg (bits : Fin 10 → Bool) : 0 ≤ score (unpack bits) := by
  let code := BitVec.ofBoolListLE (List.ofFn bits)
  have h : code.toNat < 2^10 := by
    simpa only [List.length_ofFn] using code.isLt
  have eq : codeBits code.toNat = bits := by
    funext i
    change (BitVec.ofBoolListLE (List.ofFn bits)).getLsbD i = _
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp only [List.length_ofFn];exact i.isLt),List.getElem_ofFn]
    rfl
  have q := checked finite_check (Nat.zero_le code.toNat) (by simpa using h)
  exact eq ▸ of_decide_eq_true q

theorem score_nonneg (bits : Fin 15 → Bool) (h0 : bits 0=false) (h2 : bits 2=false)
    (h5 : bits 5=false) (h9 : bits 9=false) (h14 : bits 14=false) : 0 ≤ score bits := by
  have eq : unpack (pack bits) = bits := by
    funext i
    fin_cases i <;> first | rfl | exact h0.symm | exact h2.symm | exact h5.symm | exact h9.symm | exact h14.symm
  rw [←eq]
  exact packed_nonneg _

end SavchenkoSix.Seven
