module

public import conjectures.TanWuHon.Certificate
public import conjectures.TanWuHon.Bounds
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace TanWuHon
open Multiset

/-- Only four values of f require a longer starting sample. -/
def sample (f : ℕ) : ℕ :=
  match f with
  | 1 => 2
  | 2 => 6
  | 4 => 9
  | 6 => 15
  | _ => 2*f-1

def limits (f L : ℕ) (s : ℕ) := if s<L then 2*L-2 else
  if s=L then max 1 (f/L)-1 else sample f

def step (L : ℕ) := (Finset.Ico 1 L).lcm id

def residual : List (ℕ×ℕ) := (List.range 13).flatMap fun L ↦
  ((List.range ((2*deficit L+L)/step L+1)).map fun k ↦ (k*step L,L)).filter fun z ↦
    decide (0<z.1 ∧ 2≤L ∧ ¬L∣z.1 ∧ ¬(deficit L+z.1/L<z.1 ∧ L≤z.1))

private theorem listed {f L : ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (need : ¬(deficit L + f/L<f ∧ L≤f)) : (f,L)∈residual := by
  have small := small_when_needed hf hL need
  have l2 : 2≤L := by
    have := hL.1
    by_contra! bad
    have e : L=1 := by omega
    exact hL.2.1 (by simp [e])
  have halves : f/L≤f/2 := Nat.div_le_div_left l2 (by decide)
  have ub : f≤2*deficit L+L := by omega
  have dvd : step L∣f := Finset.lcm_dvd fun j hj ↦ hL.2.2 j (Finset.mem_Ico.mp hj).1
    (Finset.mem_Ico.mp hj).2
  have ps := Nat.pos_of_dvd_of_pos dvd hf
  obtain ⟨k,eq⟩ := dvd
  have ge : k≤(2*deficit L+L)/step L := (Nat.le_div_iff_mul_le ps).mpr
    ((Nat.mul_comm _ _).le.trans (eq ▸ ub))
  apply List.mem_flatMap.mpr ⟨L,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),?_⟩,?_⟩
  · exact Prod.ext ((Nat.mul_comm _ _).trans eq.symm) rfl
  · exact decide_eq_true ⟨hf,l2,hL.2.1,need⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem residual_check : ∀ z∈residual,
    rejects z.1 (2*z.2+2) (limits z.1 z.2) false (z.2+2) 1 1 (sample z.1)
      (z.2*sample z.1+z.1)=true := by decide

private theorem smaller_sample {f L k : ℕ} (P : Multiset ℕ) (hk : k≤P.card)
    (budget : P.sum≤L*P.card+f) : ∃ Q≤P, Q.card=k ∧ Q.sum≤L*k+f := by
  induction P using Multiset.strongInductionOn with | _ P ih =>
    by_cases e : k=P.card
    · exact ⟨P,le_rfl,e.symm,e ▸ budget⟩
    have many : 0<P.card := by omega
    obtain ⟨x,hx,choice⟩ : ∃ x∈P, L≤x ∨ ∀y∈P, y≤L := by
      by_cases high : ∃ x∈P,L≤x
      · obtain ⟨x,hx,v⟩ := high; exact ⟨x,hx,.inl v⟩
      · obtain ⟨x,hx⟩ := card_pos_iff_exists_mem.mp many
        exact ⟨x,hx,.inr fun y hy ↦ Nat.le_of_not_ge fun v ↦ high ⟨y,hy,v⟩⟩
    obtain ⟨R,split⟩ := exists_cons_of_mem hx
    have lt : R<P := split ▸ lt_cons_self _ _
    have c : P.card=R.card+1 := by rw [split,card_cons]
    have sr := congrArg Multiset.sum split
    simp only [sum_cons] at sr
    have br : R.sum≤L*R.card+f := by
      rcases choice with high|small
      · rw [c,Nat.mul_succ] at budget; omega
      · have v := R.sum_le_card_nsmul L (fun y hy ↦ small y (split ▸ mem_cons_of_mem hy))
        change R.sum≤R.card*L at v
        rw [Nat.mul_comm] at v
        omega
    obtain ⟨Q,sub,cq,mass⟩ := ih R lt (by omega) br
    exact ⟨Q,sub.trans lt.le,cq,mass⟩

theorem stable {f L : ℕ} {P : Multiset ℕ} (hf : 0<f) (hL : LeastNondivisor f L)
    (pos : ∀ x∈P, 0<x) (hn : Avoids f P) (budget : P.sum≤L*P.card+f)
    (many : 2*f-1≤P.card) (large : sample f≤P.card) : Stable f L P := by
  by_cases high : deficit L + f/L<f ∧ L≤f
  · exact stable_large hf hL pos hn budget many high.1 high.2
  have check := residual_check (f,L) (listed hf hL high)
  obtain ⟨Q,hQ,size,mass⟩ := smaller_sample P large budget
  change max 1 (f/L)≤P.count L
  by_contra! bad
  apply no_partition (L+2) check (avoids_mono hn hQ) (fun x hx ↦ pos x (subset_of_le hQ hx))
    _ size mass (by simp)
  intro s
  have monotone := count_le_of_le s hQ
  by_cases below : s<L
  · by_cases sp : s=0
    · subst s
      have zero : Q.count 0=0 := count_eq_zero.mpr fun h ↦ (pos 0 (subset_of_le hQ h)).false
      simp [limits,zero]
    · simpa [limits,below] using monotone.trans (short_counts hf hL pos hn budget many (by omega) below)
  · by_cases eq : s=L
    · subst s; simp [limits]; omega
    · simpa [limits,eq,below] using (count_le_card s Q).trans_eq size

def extras (f n L : ℕ) : List ℕ :=
  match f,n%L with
  | 1,1 => [3]
  | 2,1 => [1]
  | 2,2 => [1,4]
  | 4,1 => [2,5]
  | 4,2 => [2]
  | 6,0 => [1,3]
  | 6,1 => [1]
  | 6,2 => [5,5]
  | 6,3 => [3]
  | _,_ => []

def witness (f n L : ℕ) : List ℕ :=
  let e := extras f n L
  e ++ List.replicate ((n-e.sum)/L) L

def subsetMask : List ℕ → ℕ
  | [] => 1
  | x::xs => let b := subsetMask xs; b ||| (b <<< x)

private theorem mask_hit (l : List ℕ) {Q : Multiset ℕ} (sub : Q≤(l : Multiset ℕ)) :
    (subsetMask l).testBit Q.sum := by
  induction l generalizing Q with
  | nil =>
    have eq : Q=0 := le_bot_iff.mp sub
    simp [eq,subsetMask]
  | cons x xs ih =>
    simp only [subsetMask,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq]
    by_cases mx : x∈Q
    · obtain ⟨T,rfl⟩ := exists_cons_of_mem mx
      have hit := ih ((cons_le_cons_iff x).mp sub)
      right
      simp [sum_cons,hit]
    · exact .inl (ih ((le_cons_of_notMem mx).mp sub))

def best (f n : ℕ) (l : List ℕ) : Bool :=
  decide (l.sum=n) && (l.all (fun x ↦ decide (0<x))) && !(subsetMask l).testBit f &&
    (List.range (n+1)).all fun k ↦ decide (k≤l.length) ||
      rejects f (f+2) (fun _ ↦ k) true (f+1) 1 1 k n

private theorem best_eq {f n : ℕ} (hf : 0<f) (hn : f<n) {l : List ℕ} (ok : best f n l=true) :
    rho f n=l.length := by
  simp only [best,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨sum,positive⟩,miss⟩,upper⟩ := ok
  have parts : Partition f n (l:Multiset ℕ) := by
    refine ⟨fun x hx ↦ of_decide_eq_true (List.all_eq_true.mp positive x hx),sum,?_⟩
    intro Q sub e
    have hit := mask_hit l sub
    rw [e,miss] at hit
    contradiction
  apply le_antisymm _ (card_le_rho parts)
  obtain ⟨P,hP,size⟩ := optimum hf hn
  have kj : P.card≤n := (card_le_mass hP.1).trans_eq hP.2.1
  have v := List.all_eq_true.mp upper P.card (List.mem_range.mpr (by omega))
  rcases Bool.or_eq_true_iff.mp v with le|rej
  · exact size ▸ of_decide_eq_true le
  · exact (no_partition (f+1) rej hP.2.2 hP.1 (fun j ↦ count_le_card j _) rfl hP.2.1.le
      (fun _ ↦ hP.2.1)).elim

def initial : List (ℕ×ℕ×ℕ) := [(1,2),(2,3),(4,3),(6,4)].flatMap fun z ↦
  ((List.range (z.2*(sample z.1-1)+1)).filter fun r ↦
    decide (z.1≤r ∧ 2*(z.1-1)*z.2<r)).map fun r ↦ (z.1,r,z.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem initial_check : ∀ z∈initial,
    let f := z.1; let r := z.2.1; let L := z.2.2
    let p := witness f (f+r) L; let q := witness f (f+r+L) L
    best f (f+r) p=true ∧ best f (f+r+L) q=true ∧ q.length=p.length+1 := by decide

theorem initial_cases {f r L : ℕ} (hf : 0<f) (hr : f≤r) (hL : LeastNondivisor f L)
    (threshold : 2*(f-1)*L<r) (low : r≤L*(sample f-1)) :
    rho f (f+r+L)=rho f (f+r)+1 := by
  have base : (f,L)∈([(1,2),(2,3),(4,3),(6,4)] : List (ℕ×ℕ)) := by
    have size : f=1 ∨ f=2 ∨ f=4 ∨ f=6 := by
      by_contra! bad
      have eq : sample f=2*f-1 := by unfold sample; split <;> omega
      rw [eq] at low
      have h : 2*(f-1)=2*f-1-1 := by omega
      rw [h,Nat.mul_comm] at threshold
      omega
    have val := hL.2.2
    have nd := hL.2.1
    rcases size with rfl|rfl|rfl|rfl
    · have ub : L≤2 := by by_contra! lt; exact (by decide : ¬2∣1) (val 2 (by decide) lt)
      interval_cases L <;> simp_all
    · have ub : L≤3 := by by_contra! lt; exact (by decide : ¬3∣2) (val 3 (by decide) lt)
      interval_cases L <;> simp_all
    · have ub : L≤3 := by by_contra! lt; exact (by decide : ¬3∣4) (val 3 (by decide) lt)
      interval_cases L <;> simp_all
    · have ub : L≤4 := by by_contra! lt; exact (by decide : ¬4∣6) (val 4 (by decide) lt)
      interval_cases L <;> simp_all
  have mem : (f,r,L)∈initial := List.mem_flatMap.mpr ⟨(f,L),base,
    List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le low),decide_eq_true ⟨hr,threshold⟩⟩,rfl⟩⟩
  obtain ⟨p,q,e⟩ := initial_check _ mem
  have h1 : rho f (f+r)=(witness f (f+r) L).length :=
    best_eq (f:=f) (n:=f+r) (l:=witness f (f+r) L) hf (by omega) p
  have h2 : rho f (f+r+L)=(witness f (f+r+L) L).length :=
    best_eq (f:=f) (n:=f+r+L) (l:=witness f (f+r+L) L) hf (by omega) q
  rw [h2,h1]
  exact e

end TanWuHon
