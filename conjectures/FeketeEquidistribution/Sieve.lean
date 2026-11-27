module

public import conjectures.FeketeEquidistribution.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

@[expose] public section
namespace FeketeEquidistribution
open Finset

/-- The sifted integers in one residue class after multiplication by a scale. -/
def bucket (b n d k s : ℕ) : Finset ℕ :=
  (Icc 1 b).filter fun a ↦ a.Coprime n ∧ k*a % d = s

private theorem count_prime (b n d k s p : ℕ) (hp : p.Prime) (hc : p.Coprime n) :
    (bucket b (p*n) d k s).card = (bucket b n d k s).card -
      (bucket (b/p) n d (k*p) s).card := by
  let A := bucket b n d k s
  have left : A.filter (fun a ↦ ¬p∣a) = bucket b (p*n) d k s := by
    ext a
    simp only [A,bucket,mem_filter,Nat.coprime_mul_iff_right,← hp.coprime_iff_not_dvd]
    rw [Nat.coprime_comm (n:=p)]
    tauto
  have scaled : (bucket (b/p) n d (k*p) s).card = (A.filter fun a ↦ p∣a).card := by
    apply card_bij (fun a _ ↦ p*a)
    · intro a ha
      simp only [A,bucket,mem_filter,mem_Icc] at ha ⊢
      refine ⟨⟨⟨Nat.mul_pos hp.pos ha.1.1,?_⟩,Nat.coprime_mul_iff_left.mpr ⟨hc,ha.2.1⟩,?_⟩,dvd_mul_right _ _⟩
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp ha.1.2
      · simpa [Nat.mul_assoc] using ha.2.2
    · intro a _ a' _ eq
      exact Nat.eq_of_mul_eq_mul_left hp.pos eq
    · intro v hv
      simp only [A,bucket,mem_filter,mem_Icc] at hv
      obtain ⟨t,rfl⟩ := hv.2
      refine ⟨t,?_,rfl⟩
      simp only [bucket,mem_filter,mem_Icc,Nat.coprime_mul_iff_left] at hv ⊢
      refine ⟨⟨?_,(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [Nat.mul_comm] using hv.1.1.2)⟩,hv.1.2.1.2,?_⟩
      · by_contra! e
        have : t=0 := by omega
        simp [this] at hv
      · simpa [Nat.mul_assoc] using hv.1.2.2
  have partition := A.card_filter_add_card_filter_not (fun a ↦ p∣a)
  rw [left, ←scaled] at partition
  dsimp only [A] at partition
  omega

private theorem range_period {f : ℕ → ℕ} {d : ℕ} (per : ∀ i, f (d+i)=f i) (q r : ℕ) :
    ∑ i ∈ range (q*d+r), f i = q*(∑ i ∈ range d, f i)+∑ i ∈ range r,f i := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,show q*d+d+r=d+(q*d+r) by omega, sum_range_add]
    simp_rw [per]
    rw [ih,Nat.succ_mul]
    omega

/-- Count full periods and the final incomplete period. -/
def unfilteredCount (b d k s : ℕ) : ℕ :=
  (b/d)*(∑ i ∈ range d, if k*(i+1)%d=s then 1 else 0) +
  ∑ i ∈ range (b%d), if k*(i+1)%d=s then 1 else 0

private theorem single_period (b d k s : ℕ) : (bucket b 1 d k s).card = unfilteredCount b d k s := by
  let f (i : ℕ) := if k*(i+1)%d=s then 1 else 0
  have per (i : ℕ) : f (d+i)=f i := by
    dsimp only [f]
    rw [show k*(d+i+1) = k*d+k*(i+1) by ring,Nat.mul_add_mod_self_right]
  have count : (bucket b 1 d k s).card = ∑ i ∈ range b, f i := by
    rw [show bucket b 1 d k s=(Icc 1 b).filter (fun i ↦ k*i%d=s) by ext;simp [bucket]]
    rw [card_eq_sum_ones,sum_filter]
    symm
    apply sum_bij (fun i _ ↦ i+1)
    · intro i hi
      simp only [mem_range,mem_Icc] at hi ⊢
      omega
    · intro _ _ _ _ h
      omega
    · intro i hi
      simp only [mem_Icc] at hi
      exact ⟨i-1,mem_range.mpr (by omega),by omega⟩
    · intro i _
      rfl
  rw [count, unfilteredCount]
  convert range_period per (b/d) (b%d) using 2
  rw [Nat.mul_comm,Nat.div_add_mod]

def fastCount : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | [], b,d,k,s => unfilteredCount b d k s
  | p::ps, b,d,k,s => fastCount ps b d k s - fastCount ps (b/p) d (k*p) s

def PrimeFactors : List ℕ → Prop
  | [] => True
  | p::ps => p.Prime ∧ p.Coprime ps.prod ∧ PrimeFactors ps

theorem count_eq_fast {ps : List ℕ} (hp : PrimeFactors ps) (b d k s : ℕ) :
    (bucket b ps.prod d k s).card = fastCount ps b d k s := by
  induction ps generalizing b k with
  | nil => exact single_period b d k s
  | cons p ps ih =>
    rw [List.prod_cons,count_prime b _ d k s p hp.1 hp.2.1]
    simp only [fastCount, ih hp.2.2]

theorem squarefree_prod {ps : List ℕ} (hp : PrimeFactors ps) : Squarefree ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.prod_cons,Nat.squarefree_mul hp.2.1]
    exact ⟨hp.1.squarefree,ih hp.2.2⟩

theorem residue_eq_fast {ps : List ℕ} (hp : PrimeFactors ps) (d s : ℕ) :
    residueCount ps.prod d s = fastCount ps ps.prod d 1 (s%d) := by
  rw [← count_eq_fast hp]
  unfold residueCount
  apply congrArg card
  ext i
  simp [unitsTo,bucket,and_assoc]

end FeketeEquidistribution
