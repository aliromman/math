module

public import conjectures.TanWuHon.Bounds
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

@[expose] public section
namespace TanWuHon
open Multiset

private def Represents (b : ℕ) (S : Multiset ℕ) : Prop :=
  ∀ x, b.testBit x → ∃ T≤S, T.sum=x

def extend (s : ℕ) : ℕ → ℕ → ℕ
  | 0,b => b
  | c+1,b => let v := extend s c b; v ||| (v <<< s)

private theorem extend_ok {s b : ℕ} {S : Multiset ℕ} (ok : Represents b S) (c : ℕ) :
    Represents (extend s c b) (replicate c s+S) := by
  induction c with
  | zero => simpa [extend] using ok
  | succ c ih =>
    intro x hx
    simp only [extend,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq] at hx
    rw [replicate_succ,cons_add]
    rcases hx with hit|⟨le,hit⟩
    · obtain ⟨T,leT,e⟩ := ih x hit
      exact ⟨T,leT.trans (Multiset.le_cons_self _ _),e⟩
    · obtain ⟨T,leT,e⟩ := ih (x-s) hit
      exact ⟨s ::ₘ T,cons_le_cons _ leT,by rw [sum_cons,e]; omega⟩

/-- If the prefix makes f-js, at most j-1 more copies of s can occur. -/
def capAux (f s b base : ℕ) : ℕ → ℕ
  | 0 => base
  | j+1 => if b.testBit (f-(j+1)*s) then min j (capAux f s b base j) else capAux f s b base j

def cap (f s b base : ℕ) := capAux f s b base (f/s)

private theorem cap_ok {f s b base : ℕ} {S P : Multiset ℕ} (sp : 0<s) (ok : Represents b S)
    (hn : Avoids f (S+P)) (ub : P.count s≤base) : P.count s≤cap f s b base := by
  suffices aux : ∀ n≤f/s, P.count s≤capAux f s b base n from aux _ le_rfl
  intro n
  induction n with
  | zero => exact fun _ ↦ ub
  | succ j ih =>
    intro lim
    have prev := ih (by omega)
    rw [capAux]
    split
    next hit =>
      refine le_min_iff.mpr ⟨?_,prev⟩
      by_contra! high
      obtain ⟨T,hT,e⟩ := ok _ hit
      apply hn (T+replicate (j+1) s) (add_le_add hT (le_count_iff_replicate_le.mp high))
      have maxS := (Nat.le_div_iff_mul_le sp).mp lim
      rw [sum_add,e,sum_replicate]
      exact Nat.sub_add_cancel maxS
    next => exact prev

def heavy (f lo hi b k W : ℕ) (limits : ℕ→ℕ) : Bool :=
  (List.range (hi+1)).any fun t ↦ decide (lo≤t ∧
    W+(∑ j ∈ Finset.Ico lo t, (t-j)*cap f j b (min k (limits j)))<t*k)

/-- A true value certifies that the remaining parts cannot satisfy the bounds. -/
def rejects (f hi : ℕ) (limits : ℕ→ℕ) (exactWeight : Bool) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | fuel,lo,b,k,W =>
    if k=0 then exactWeight && decide (W≠0)
    else if heavy f lo hi b k W limits then true
    else match fuel with
    | 0 => false
    | u+1 => (List.range (cap f lo b (min k (limits lo))+1)).all fun c ↦
      decide (W<c*lo) || rejects f hi limits exactWeight u (lo+1) (extend lo c b) (k-c) (W-c*lo)

private theorem rejects_ok {f hi : ℕ} {limits : ℕ→ℕ} {exactWeight : Bool}
    (fuel lo b k W : ℕ) (op : 0<lo) (yes : rejects f hi limits exactWeight fuel lo b k W=true)
    {S P : Multiset ℕ} (ok : Represents b S) (hn : Avoids f (S+P))
    (low : ∀ x∈P, lo≤x) (lim : ∀ s,P.count s≤limits s)
    (size : P.card=k) (budget : P.sum≤W) (ex : exactWeight=true → P.sum=W) : False := by
  induction fuel generalizing lo b k W S P
  all_goals
    rw [rejects] at yes
    split at yes
    next k0 =>
      have hp : P=0 := card_eq_zero.mp (by omega)
      have h := ex (Bool.and_eq_true_iff.mp yes).1
      simp [hp] at h
      simp [h] at yes
    split at yes
    next hh =>
      obtain ⟨t,_,hit⟩ := List.any_eq_true.mp hh
      have ⟨_,bad⟩ := of_decide_eq_true hit
      have wb := weight_bound P lo t low (fun j ↦ cap f j b (min k (limits j))) (by
        intro j hj
        apply cap_ok (by have := (Finset.mem_Ico.mp hj).1; omega) ok hn
        exact le_min_iff.mpr ⟨(count_le_card _ _).trans_eq size,lim j⟩)
      rw [size] at wb
      omega
  case zero => contradiction
  case succ u ih _ _ =>
    let c := P.count lo
    obtain ⟨Q,eq⟩ := Multiset.le_iff_exists_add.mp (le_count_iff_replicate_le.mp (le_refl c))
    have sq := congrArg Multiset.sum eq
    have cq := congrArg Multiset.card eq
    have zero := congrArg (Multiset.count lo) eq
    simp only [sum_add,sum_replicate,nsmul_eq_mul] at sq
    change P.sum=c*lo+Q.sum at sq
    simp only [card_add,card_replicate] at cq
    simp only [count_add,count_replicate_self] at zero
    have z : Q.count lo=0 := by change c=c+_ at zero; omega
    have capC := cap_ok (f:=f) op ok hn
      (le_min_iff.mpr ⟨(count_le_card lo P).trans_eq size,lim lo⟩)
    have yy := List.all_eq_true.mp yes c (List.mem_range.mpr (by omega))
    simp only [Bool.or_eq_true,decide_eq_true_eq] at yy
    rcases yy with impossible|yy
    · omega
    have sub : Q≤P := eq ▸ Multiset.le_add_left _ _
    apply ih (lo+1) (extend lo c b) (k-c) (W-c*lo) (by omega) yy (S:=replicate c lo+S)
      (P:=Q) (extend_ok ok c) (by simpa only [eq,add_assoc,add_left_comm,add_comm] using hn)
    · intro x hx
      have := low x (subset_of_le sub hx)
      have ne : x≠lo := by rintro rfl; exact (count_eq_zero.mp z) hx
      omega
    · exact fun j ↦ (count_le_of_le j sub).trans (lim j)
    · omega
    · omega
    · intro flag; have := ex flag; omega

theorem no_partition {f hi k W : ℕ} {limits : ℕ→ℕ} {exactWeight : Bool} (fuel : ℕ)
    (yes : rejects f hi limits exactWeight fuel 1 1 k W=true)
    {P : Multiset ℕ} (hn : Avoids f P) (pos : ∀ x∈P, 0<x) (lim : ∀ s,P.count s≤limits s)
    (size : P.card=k) (budget : P.sum≤W) (ex : exactWeight=true → P.sum=W) : False := by
  apply rejects_ok fuel 1 1 k W (by decide) yes (S:=0) (P:=P) _ (by simpa using hn) pos lim size budget ex
  intro x hit
  have e := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hit
  exact ⟨0,le_rfl,by simp [e]⟩

end TanWuHon
