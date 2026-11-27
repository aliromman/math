module

public import conjectures.PracticalPolygons.Statement
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace PracticalPolygons
open Finset

private def Covers (n b : ℕ) : Prop := ∀ k ≤ b, DivisorSum n k

/-- Join two divisor representations after multiplying the second set by a scale. -/
private theorem combine {n m N x y d : ℕ} (hx : DivisorSum n x) (hy : DivisorSum m y)
    (hd : 0 < d) (hn : n ∣ N) (hm : d*m ∣ N) (sep : x < d ∨ ¬d ∣ n) :
    DivisorSum N (x + d*y) := by
  obtain ⟨A,hA,a⟩ := hx
  obtain ⟨B,hB,b⟩ := hy
  let C := B.image (d*·)
  have dis : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro u hu hv
    obtain ⟨v,hBv,rfl⟩ := mem_image.mp hv
    rcases sep with small | missing
    · have le : d*v ≤ ∑ i∈A,i := single_le_sum (f:=id) (fun _ _ ↦ Nat.zero_le _) hu
      have pos := (hB v hBv).1
      rw [a] at le
      nlinarith
    · exact missing ((dvd_mul_right d v).trans (hA _ hu).2)
  refine ⟨A ∪ C, ?_, ?_⟩
  · intro i hi
    rcases mem_union.mp hi with h | h
    · exact ⟨(hA i h).1, (hA i h).2.trans hn⟩
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      exact ⟨Nat.mul_pos hd (hB v hv).1, (Nat.mul_dvd_mul_left d (hB v hv).2).trans hm⟩
  · rw [sum_union dis, a]
    congr 1
    dsimp only [C]
    rw [sum_image (fun _ _ _ _ eq ↦ Nat.eq_of_mul_eq_mul_left hd eq), ←mul_sum, b]

/-- Two disjoint sets of divisors cover overlapping intervals at consecutive scales. -/
private theorem join {n m N d a b : ℕ} (ha : Covers n a) (hb : Covers m b)
    (hd : 0 < d) (width : d ≤ a+1) (hn : n ∣ N) (hm : d*m ∣ N) (sep : ¬d ∣ n) :
    Covers N (a+d*b) := by
  intro k hk
  by_cases small : k/d ≤ b
  · have eq := Nat.mod_add_div k d
    exact eq ▸ combine (ha (k%d) (by have := Nat.mod_lt k hd; omega)) (hb _ small)
      hd hn hm (Or.inr sep)
  · have le : d*b ≤ k := (Nat.mul_le_mul_left d (by omega : b≤k/d)).trans (Nat.mul_div_le k d)
    have eq : (k-d*b)+d*b=k := Nat.sub_add_cancel le
    exact eq ▸ combine (ha _ (by omega)) (hb _ le_rfl) hd hn hm (Or.inr sep)

/-- A small remainder uses only divisors below the multiplier. -/
private theorem multiplier {n t b : ℕ} (covered : Covers n b) (hn : 0<n) (hb : n≤b)
    (ht : 0<t) (limit : t≤b+1) : Practical (n*t) := by
  refine ⟨Nat.mul_pos hn ht, fun k _ hk ↦ ?_⟩
  have q : k/t ≤ n := (Nat.div_le_div_right hk).trans_eq (Nat.mul_div_cancel n ht)
  have r := Nat.mod_lt k ht
  have eq := Nat.mod_add_div k t
  exact eq ▸ combine (covered (k%t) (by omega)) (covered (k/t) (q.trans hb))
    ht (dvd_mul_right n t) (by rw [Nat.mul_comm]) (Or.inl r)

private theorem one_covers : Covers 1 1 := by
  intro k hk
  rcases (by omega : k=0 ∨ k=1) with rfl|rfl
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

private theorem six_covers : Covers 6 12 := by
  have cert : ∀ k : Fin 13, ∃ A ∈ ({1,2,3,6} : Finset ℕ).powerset, (∑ d∈A,d)=k.val := by decide
  intro k hk
  obtain ⟨A,hA,eq⟩ := cert ⟨k,by omega⟩
  refine ⟨A,?_,eq⟩
  intro i hi
  have mem := mem_powerset.mp hA hi
  simp only [mem_insert, mem_singleton] at mem
  rcases mem with rfl|rfl|rfl|rfl <;> decide

theorem six_practical (t : ℕ) (ht : 0<t) (h : t≤12) : Practical (6*t) :=
  multiplier six_covers (by decide) (by decide) ht (by omega)

private theorem binary_covers (a : ℕ) : Covers (2^a) (2*2^a-1) := by
  induction a with
  | zero => exact one_covers
  | succ a ih =>
    have h := join one_covers ih (d:=2) (N:=2^(a+1)) (by decide) (by decide)
      (one_dvd _) (by rw [pow_succ, mul_comm]) (by decide)
    have p : 0 < 2^a := by positivity
    simpa only [pow_succ, show 1+2*(2*2^a-1)=2*(2^a*2)-1 by omega] using h

theorem twoPower_practical (a t : ℕ) (ht : 0<t) (h : t≤2^(a+1)) : Practical (2^a*t) := by
  have p : 0<2^a := by positivity
  rw [pow_succ] at h
  exact multiplier (binary_covers a) p (by omega) ht (by omega)

private theorem five_covers (a : ℕ) : Covers (6*5^a) (15*5^a-3) := by
  induction a with
  | zero => exact six_covers
  | succ a ih =>
    have h := join six_covers ih (d:=5) (N:=6*5^(a+1)) (by decide) (by decide)
      (dvd_mul_right ..) ((show 5 * (6*5^a) = 6*5^(a+1) by rw [pow_succ]; ac_rfl) ▸ dvd_refl _) (by decide)
    have p : 0<5^a := by positivity
    simpa only [pow_succ, show 12+5*(15*5^a-3)=15*(5^a*5)-3 by omega] using h

/-- The moduli in the covering argument have enough small practical multiples. -/
theorem scale_practical (d a t : ℕ) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17)
    (ha : 0<a) (ht : 0<t) (h : 5*t ≤ 12*(6*d*5^a)) : Practical (6*d*5^a*t) := by
  have pow5 : 5≤5^a := by simpa using Nat.pow_le_pow_right (by decide : 0<5) (show 1≤a by omega)
  have core := five_covers a
  rcases hd with rfl|hd
  · simp only [mul_one] at h ⊢
    exact multiplier core (by positivity) (by omega) ht (by omega)
  · have cp6 : d.Coprime 6 := by rcases hd with rfl|rfl|rfl <;> decide
    have cp5 : d.Coprime 5 := by rcases hd with rfl|rfl|rfl <;> decide
    have cop := cp6.mul_right (cp5.pow_right a)
    have sep : ¬d ∣ 6*5^a := by
      intro h
      have eq := Nat.eq_one_of_dvd_coprimes cop (dvd_refl d) h
      rcases hd with rfl|rfl|rfl <;> omega
    have pd : 0<d := by omega
    have H := join core core (d:=d) (N:=6*d*5^a) pd (by omega)
      (by exact ⟨d, by ac_rfl⟩) (by simpa only [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using dvd_refl (6*d*5^a)) sep
    rcases hd with rfl|rfl|rfl <;> apply multiplier H (by positivity) _ ht _ <;> omega

end PracticalPolygons
