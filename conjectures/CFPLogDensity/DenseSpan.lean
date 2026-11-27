module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity
open Finset

def represent (U : Finset ℕ) (x : ℕ) : Prop := ∃ S ⊆ U, S.sum id=x

theorem represent_mono {U V : Finset ℕ} {x : ℕ} (h : U⊆V) :
    represent U x → represent V x := fun ⟨S,hS,hs⟩ => ⟨S,hS.trans h,hs⟩

theorem represent_insert {U : Finset ℕ} {x y : ℕ} (hx : x∉U) :
    represent U y → represent (insert x U) (y+x) := by
  rintro ⟨S,hS,hs⟩
  refine ⟨insert x S,insert_subset_insert _ hS,?_⟩
  rw [sum_insert (fun h => hx (hS h)),hs]
  exact Nat.add_comm _ _

theorem represent_add_disjoint {U V : Finset ℕ} {x y : ℕ} (dis : Disjoint U V) :
    represent U x → represent V y → represent (U∪V) (x+y) := by
  rintro ⟨S,hS,hs⟩ ⟨T,hT,ht⟩
  exact ⟨S∪T,union_subset_union hS hT,by rw [sum_union (dis.mono hS hT),hs,ht]⟩

/-- All points in a finite arithmetic progression are subset sums. -/
structure Span (d : ℕ) (A : Finset ℕ) where
  used : Finset ℕ
  subset : used⊆A
  start : ℕ
  length : ℕ
  covers : ∀ j≤length, represent used (start+d*j)

def Span.empty (d : ℕ) (A : Finset ℕ) : Span d A where
  used := ∅
  subset := empty_subset _
  start := 0
  length := 0
  covers j hj := by obtain rfl := Nat.eq_zero_of_le_zero hj; exact ⟨∅,by simp,by simp⟩

def Span.addPair {d : ℕ} {A : Finset ℕ} (P : Span d A) (u v k : ℕ)
    (hu : u∈A) (hv : v∈A) (fu : u∉P.used) (fv : v∉P.used)
    (shift : v=u+d*k) (overlap : k≤P.length+1) : Span d A where
  used := insert u (insert v P.used)
  subset := insert_subset hu (insert_subset hv P.subset)
  start := P.start+u
  length := P.length+k
  covers j hj := by
    by_cases earlier : j≤P.length
    · have h := represent_insert fu (P.covers j earlier)
      have sub : insert u P.used ⊆ insert u (insert v P.used) :=
        insert_subset_insert _ (subset_insert _ _)
      exact represent_mono sub (by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h)
    · have jk : k≤j := by omega
      have h := represent_insert fv (P.covers (j-k) (by omega))
      have e : P.start+d*(j-k)+v=P.start+u+d*j := by
        rw [shift,show j=(j-k)+k from (Nat.sub_add_cancel jk).symm] at *
        simp [Nat.mul_add]
        omega
      exact represent_mono (subset_insert u _) (e ▸ h)

theorem Span.addPair_card {d : ℕ} {A : Finset ℕ} (P : Span d A) (u v k : ℕ)
    (hu : u∈A) (hv : v∈A) (fu : u∉P.used) (fv : v∉P.used)
    (shift : v=u+d*k) (overlap : k≤P.length+1) :
    (P.addPair u v k hu hv fu fv shift overlap).used.card≤P.used.card+2 := by
  dsimp [Span.addPair]
  have := card_insert_le u (insert v P.used)
  have := card_insert_le v P.used
  omega

theorem Span.start_le {d M : ℕ} {A : Finset ℕ} (P : Span d A) (bd : ∀ x∈A, x≤M) :
    P.start≤P.used.card*M := by
  obtain ⟨S,hS,he⟩ := P.covers 0 (Nat.zero_le _)
  simp at he
  change S.sum id=P.start at he
  rw [←he]
  calc
    S.sum id ≤ ∑ _x∈S,M := sum_le_sum (fun x hx => bd x (P.subset (hS hx)))
    _ ≤ P.used.card*M := by simpa using Nat.mul_le_mul_right M (card_le_card hS)

/-- An attained interval can absorb any number up to its length plus one. -/
theorem extend_interval {U R : Finset ℕ} {lo hi : ℕ} (dis : Disjoint U R)
    (hcover : ∀ x, lo≤x → x≤hi → represent U x)
    (hb : ∀ r∈R, lo+r≤hi+1) :
    ∀ x, lo≤x → x≤hi+R.sum id → represent (U∪R) x := by
  induction R using Finset.induction_on with
  | empty => simpa using hcover
  | @insert a R ha ih =>
    have ds : Disjoint U R := dis.mono_right (subset_insert _ _)
    have au : a∉U := fun h => disjoint_left.mp dis h (mem_insert_self _ _)
    have capt := ih ds (fun r h => hb r (mem_insert_of_mem h))
    have ba := hb a (mem_insert_self _ _)
    intro x xl xh
    rw [sum_insert ha] at xh
    rw [union_insert]
    by_cases earlier : x≤hi+R.sum id
    · exact represent_mono (subset_insert _ _) (capt x xl earlier)
    · have ax : a≤x := by omega
      have mem : a∉U∪R := by simp [au,ha]
      simp only [id_eq] at xh
      have upper : x-a ≤ hi+R.sum id := by simpa only [id_eq] using (show x-a≤hi+∑ z∈R,z by omega)
      have old := represent_insert mem (capt (x-a) (by omega) upper)
      simpa [Nat.sub_add_cancel ax] using old

end CFPLogDensity
