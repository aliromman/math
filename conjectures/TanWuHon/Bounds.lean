module

public import conjectures.TanWuHon.Partitions
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section
namespace TanWuHon
open Multiset

/-- Compare each part with a fixed cutoff t, and add its deficit when it is smaller. -/
theorem weight_bound (P : Multiset ℕ) (s t : ℕ) (hlo : ∀ x∈P, s≤x) (cap : ℕ → ℕ)
    (hc : ∀ j∈Finset.Ico s t, P.count j≤cap j) :
    t*P.card≤P.sum+∑ j ∈ Finset.Ico s t, (t-j)*cap j := by
  suffices exactBound : t*P.card≤P.sum+∑ j ∈ Finset.Ico s t, (t-j)*P.count j by
    exact exactBound.trans (Nat.add_le_add_left (Finset.sum_le_sum
      (fun j hj ↦ Nat.mul_le_mul_left _ (hc j hj))) _)
  induction P using Multiset.induction_on with
  | empty => simp
  | cons x P ih =>
    have prev := ih (fun y hy ↦ hlo y (mem_cons_of_mem hy)) (fun j hj ↦
      (Multiset.count_le_of_le j (Multiset.le_cons_self P x)).trans (hc j hj))
    have counts (j) : (x ::ₘ P).count j=P.count j+(if j=x then 1 else 0) := by
      by_cases e : j=x <;> simp [e,count_cons_of_ne]
    simp only [card_cons,sum_cons,Nat.mul_succ,counts,Nat.mul_add,Finset.sum_add_distrib]
    have val : (∑ j ∈ Finset.Ico s t, (t-j)*(if j=x then 1 else 0))=
        (if x∈Finset.Ico s t then t-x else 0) := by simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']
    rw [val]
    have hx := hlo x (by simp)
    by_cases small : x<t
    · rw [ite_eq_left (Finset.mem_Ico.mpr ⟨hx,small⟩)]
      omega
    · rw [ite_eq_right (fun h ↦ small (Finset.mem_Ico.mp h).2)]
      omega

def deficit (L : ℕ) : ℕ := ∑ j ∈ Finset.Ico 1 L, (L+1-j)*(2*L-2)

def Stable (f L : ℕ) (P : Multiset ℕ) : Prop :=
  max 1 (f/L) ≤ P.count L

theorem short_counts {f L : ℕ} {P : Multiset ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (pos : ∀ x∈P, 0<x) (hn : Avoids f P) (budget : P.sum≤L*P.card+f)
    (many : 2*f-1≤P.card) {s : ℕ} (spos : 0<s) (sl : s<L) : P.count s≤2*L-2 := by
  let M := 2*L-1
  have L2 : 2≤L := by
    have pos := hL.1; have nd := hL.2.1
    by_contra! bad; have : L=1 := by omega
    simp [this] at nd
  have sM : s≤M := by dsimp [M]; omega
  by_contra! bad
  let Q := P.filter (·≤M)
  have sub : Q≤P := Multiset.filter_le _ _
  have cc : M≤Q.count s := by simp [Q,sM,M]; omega
  have few := few_bounded spos (hL.2.2 s spos sl) (P:=Q)
    (fun x hx ↦ pos x (subset_of_le sub hx)) (fun x hx ↦ (Multiset.mem_filter.mp hx).2) (avoids_mono hn sub) cc
  let R := P.filter (fun x ↦ ¬x≤M)
  have split : Q+R=P := Multiset.filter_add_not _ _
  have smallMass := card_le_mass (P:=Q) (fun x hx ↦ pos x (subset_of_le sub hx))
  have largeMass := mass_lower (P:=R) (m:=M+1) (fun x hx ↦
    Nat.lt_of_not_ge (Multiset.mem_filter.mp hx).2)
  have mass := congrArg Multiset.sum split
  have cards := congrArg Multiset.card split
  simp only [sum_add,card_add] at mass cards
  have m1 : M+1=2*L := by dsimp [M]; omega
  rw [m1] at largeMass
  have bound := Nat.mul_le_mul_left L many
  have fc := Nat.mul_le_mul_left (2*L-1) (show Q.card≤f-1 by omega)
  have mm : 2*L-1+1=2*L := by omega
  have ff : f-1+1=f := by omega
  have kk : 2*f-1+1=2*f := by omega
  nlinarith [congrArg (· * Q.card) mm, congrArg (· * (f-1)) mm,
    congrArg (L * ·) kk,congrArg ((2*L)*·) ff,congrArg (L*·) cards]

theorem stable_large {f L : ℕ} {P : Multiset ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (pos : ∀ x∈P, 0<x) (hn : Avoids f P) (budget : P.sum≤L*P.card+f)
    (many : 2*f-1≤P.card) (high : deficit L + f/L < f) (fL : L≤f) : Stable f L P := by
  change max 1 (f/L)≤P.count L
  by_contra! bad
  have lower : 1≤f/L := (Nat.le_div_iff_mul_le hL.1).mpr (by simpa)
  have cnt : P.count L < f/L := by simpa [max_eq_right lower] using bad
  let caps (j : ℕ) := if j=L then f/L-1 else 2*L-2
  have wb := weight_bound P 1 (L+1) pos caps (by
    intro j hj
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hj
    by_cases eq : j=L
    · subst j; simp [caps]; omega
    · simpa [caps,eq] using short_counts hf hL pos hn budget many (s:=j) lo (by omega))
  have sub : (∑ j ∈ Finset.Ico 1 (L+1), (L+1-j)*caps j)=deficit L+(f/L-1) := by
    have h := Finset.sum_Ico_succ_top (show 1≤L from hL.1) (fun j ↦ (L+1-j)*caps j)
    rw [h]
    simp only [caps,ite_true,Nat.add_sub_cancel_left,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [ne_of_lt (Finset.mem_Ico.mp hi).2]
  rw [sub,Nat.add_mul,one_mul] at wb
  omega

open Finset

theorem deficit_upper (L : ℕ) : deficit L≤2*L^3 := by
  have bound := Finset.sum_le_sum (s:=Finset.Ico 1 L) (g:=fun _ ↦ L*(2*L)) (fun j hj ↦
    Nat.mul_le_mul (show L+1-j≤L by have := (Finset.mem_Ico.mp hj).1; omega) (Nat.sub_le (2*L) 2))
  simp only [sum_const,Nat.card_Ico,nsmul_eq_mul] at bound
  calc deficit L ≤ (L-1)*(L*(2*L)) := bound
       _ ≤ L*(L*(2*L)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
       _ = _ := by ring

theorem lcm_growth {f L : ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (large : 13≤L) : 4*L^3≤f := by
  let D (j : ℕ) := (Finset.Ico 1 j).lcm id
  have minor (j : ℕ) (hj : j≤L) : D j≤f := Nat.le_of_dvd hf (Finset.lcm_dvd
    (fun x hx ↦ hL.2.2 x (Finset.mem_Ico.mp hx).1 ((Finset.mem_Ico.mp hx).2.trans_le hj)))
  by_cases small : L≤16
  · exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left small 3)).trans
      ((by decide : 4*16^3≤D 13).trans (minor 13 large))
  by_cases medium : L≤50
  · exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left medium 3)).trans
      ((by decide : 4*50^3≤D 17).trans (minor 17 (by omega)))
  by_cases last : L≤1000
  · exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left last 3)).trans
      ((by decide : 4*1000^3≤D 31).trans (minor 31 (by omega)))
  let power (a : ℕ) := a^(Nat.log a (L-1))
  have pl (a : ℕ) (ha : 1<a) : L≤a*power a := by
    have := Nat.lt_pow_succ_log_self ha (L-1)
    rw [pow_succ'] at this
    dsimp [power]
    omega
  have div (a : ℕ) (ha : 0<a) : power a ∣ f := hL.2.2 _
    (pow_pos ha _) (by have := Nat.pow_log_le_self a (show L-1≠0 by omega); dsimp [power]; omega)
  have cp (p q : ℕ) (a : p.Prime) (b : q.Prime) (ne : p≠q) : (power p).Coprime (power q) :=
    Nat.coprime_pow_primes _ _ a b ne
  have product : power 2*power 3*power 5*power 7∣f := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ (div 7 (by decide))
    · simp only [Nat.coprime_mul_iff_left]
      exact ⟨⟨cp 2 7 (by decide) (by decide) (by decide),cp 3 7 (by decide) (by decide) (by decide)⟩,
        cp 5 7 (by decide) (by decide) (by decide)⟩
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ (div 5 (by decide))
      · exact Nat.coprime_mul_iff_left.mpr ⟨cp 2 5 (by decide) (by decide) (by decide),
          cp 3 5 (by decide) (by decide) (by decide)⟩
      · exact (cp 2 3 (by decide) (by decide) (by decide)).mul_dvd_of_dvd_of_dvd
          (div 2 (by decide)) (div 3 (by decide))
  have powers := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pl 2 (by decide))
      (pl 3 (by decide))) (pl 5 (by decide))) (pl 7 (by decide))
  have quartic : L^4≤210*f := calc
    _ = L*L*L*L := by ring
    _ ≤ _ := powers
    _ = 210*(power 2*power 3*power 5*power 7) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_of_dvd hf product)
  have b := Nat.mul_le_mul_right (L^3) (show 1000≤L by omega)
  rw [←pow_succ'] at b
  change 1000*L^3≤L^4 at b
  omega

theorem small_when_needed {f L : ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (need : ¬(deficit L + f/L < f ∧ L≤f)) : L≤12 := by
  have l2 : 2≤L := by
    have p := hL.1
    by_contra! no
    have eq : L=1 := by omega
    exact hL.2.1 (by simp [eq])
  have d := deficit_upper L
  by_contra! huge
  have v := lcm_growth hf hL huge
  have thirds : f/L≤f/3 := Nat.div_le_div_left (by omega) (by decide)
  have u : L≤L^3 := Nat.le_self_pow (by decide) L
  apply need
  constructor <;> omega

end TanWuHon
