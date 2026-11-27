module

public import conjectures.LuckySpots.Statement
import Mathlib.Tactic.Ring

@[expose] public section
namespace LuckySpots
open Finset

def W (m k : ℕ) (f : List ℕ → ℚ) : ℚ := ∑ w∈words m k, f w

theorem mem_words {m k : ℕ} {w : List ℕ} : w∈words m k ↔ w.length=k ∧ ∀ x∈w,x<m := by
  induction k generalizing w with
  | zero =>
    simp only [words,mem_singleton,List.length_eq_zero_iff]
    constructor
    · rintro rfl
      simp
    · exact And.left
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons p ps =>
      constructor
      · intro h
        obtain ⟨⟨a,u⟩, hau, heq⟩ := Finset.mem_map.mp h
        change a::u = p::ps at heq
        obtain ⟨rfl,rfl⟩ := List.cons.inj heq
        obtain ⟨ha,hu⟩ := Finset.mem_product.mp hau
        obtain ⟨hlen,hlt⟩ := ih.mp hu
        change u.length = k at hlen
        change ∀ x∈u, x<m at hlt
        simpa [hlen, Finset.mem_range.mp ha] using hlt
      · rintro ⟨hlen,hlt⟩
        apply Finset.mem_map.mpr
        refine ⟨(p,ps),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hlt p (by simp)), ih.mpr ⟨by simpa using hlen, ?_⟩⟩,rfl⟩
        exact fun x hx ↦ hlt x (by simp [hx])

theorem W_zero (m : ℕ) (f : List ℕ → ℚ) : W m 0 f=f [] := by simp [W,words]

theorem W_succ (m k : ℕ) (f : List ℕ → ℚ) :
    W m (k+1) f = ∑ a∈range m,W m k (fun w ↦ f (a::w)) := by
  simp only [W, words, Finset.sum_map, Finset.sum_product]
  rfl

theorem W_congr {m k : ℕ} {f g : List ℕ → ℚ} (h : ∀ w∈words m k, f w=g w) : W m k f=W m k g :=
  Finset.sum_congr rfl h

theorem W_const (m k : ℕ) (c : ℚ) : W m k (fun _ ↦ c)=(m:ℚ)^k*c := by
  induction k with
  | zero => simp [W_zero]
  | succ k ih => rw [W_succ]; simp [ih,pow_succ]; ring

theorem W_add (m k : ℕ) (f g : List ℕ → ℚ) : W m k (fun w ↦ f w+g w)=W m k f+W m k g :=
  Finset.sum_add_distrib

theorem W_mul (m k : ℕ) (c : ℚ) (f : List ℕ → ℚ) : W m k (fun w ↦ c*f w)=c*W m k f :=
  (Finset.mul_sum ..).symm

theorem W_swap {m k : ℕ} {α : Type*} (S : Finset α) (f : α→List ℕ→ℚ) :
    (∑ a∈S,W m k (f a))=W m k (fun w ↦ ∑ a∈S,f a w) := Finset.sum_comm

def low (m : ℕ) (w : List ℕ) := w.filter (·<m)
def high (m : ℕ) (w : List ℕ) := (w.filter (m≤·)).map (·-m)

private theorem choose_step (k : ℕ) (f : ℕ → ℕ → ℚ) :
    (∑ i∈range (k+1),(k.choose i:ℚ)*f (i+1) (k-i))+
    (∑ i∈range (k+1),(k.choose i:ℚ)*f i (k-i+1)) =
    ∑ i∈range (k+2),((k+1).choose i:ℚ)*f i (k+1-i) := by
  rw [sum_range_succ (f:=fun i ↦ (k.choose i:ℚ)*f (i+1) (k-i))]
  rw [sum_range_succ' (f:=fun i ↦ (k.choose i:ℚ)*f i (k-i+1))]
  rw [sum_range_succ (f:=fun i ↦ ((k+1).choose i:ℚ)*f i (k+1-i))]
  rw [sum_range_succ' (f:=fun i ↦ ((k+1).choose i:ℚ)*f i (k+1-i))]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,Nat.choose_zero_right,Nat.sub_zero,
    Nat.succ_sub_succ_eq_sub]
  have mid : (∑ i∈range k,(k.choose i:ℚ)*f (i+1) (k-i))+
      (∑ i∈range k,(k.choose (i+1):ℚ)*f (i+1) (k-(i+1)+1)) =
      ∑ i∈range k,((k+1).choose (i+1):ℚ)*f (i+1) (k-i) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have il := mem_range.mp hi
    rw [show k-(i+1)+1=k-i by omega,Nat.choose_succ_succ,Nat.cast_add,add_mul]
  linarith

private def blocks (m b i j : ℕ) (f : List ℕ → List ℕ → ℚ) : ℚ :=
  W m i (fun u ↦ W b j (f u))

/-- Split words at a cut in the alphabet and preserve the order on both sides. -/
theorem split_sum (m b k : ℕ) (f : List ℕ → List ℕ → ℚ) :
    W (m+b) k (fun w ↦ f (low m w) (high m w)) =
    ∑ i∈range (k+1),(k.choose i:ℚ)*W m i (fun u ↦ W b (k-i) (f u)) := by
  induction k generalizing f with
  | zero => simp [W_zero,low,high]
  | succ k ih =>
    have first (x) (hx : x<m) : W (m+b) k (fun w ↦ f (low m (x::w)) (high m (x::w))) =
        ∑ i∈range (k+1),(k.choose i:ℚ)*blocks m b i (k-i) (fun u v ↦ f (x::u) v) := by
      simpa only [low,high,List.filter_cons_of_pos (p:=fun z : ℕ ↦ decide (z<m)) (by simpa using hx),
        List.filter_cons_of_neg (p:=fun z : ℕ ↦ decide (m≤z)) (by simpa using Nat.not_le_of_lt hx),
        blocks] using ih (fun u v ↦ f (x::u) v)
    have last (x) : W (m+b) k (fun w ↦ f (low m ((m+x)::w)) (high m ((m+x)::w))) =
        ∑ i∈range (k+1),(k.choose i:ℚ)*blocks m b i (k-i) (fun u v ↦ f u (x::v)) := by
      simpa [low,high,blocks] using ih (fun u v ↦ f u (x::v))
    rw [W_succ,sum_range_add]
    simp_rw [last]
    rw [sum_congr rfl (fun x h ↦ first x (mem_range.mp h)),sum_comm]
    rw [sum_comm (s:=range b)]
    simp_rw [←mul_sum]
    have left (i : ℕ) : (∑ x∈range m,blocks m b i (k-i) (fun u v ↦ f (x::u) v)) =
        blocks m b (i+1) (k-i) f := (W_succ m i (fun u ↦ W b (k-i) (f u))).symm
    have right (i : ℕ) : (∑ x∈range b,blocks m b i (k-i) (fun u v ↦ f u (x::v))) =
        blocks m b i (k-i+1) f := by
      unfold blocks
      rw [W_swap]
      simp only [W_succ]
    simp_rw [left,right]
    exact choose_step k (fun i j ↦ blocks m b i j f)

end LuckySpots
