module

public import conjectures.TanWuHon.Partitions
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

public section
namespace TanWuHon
open Multiset

private def Complete (P : Multiset ℕ) := ∀ j≤P.sum, ∃ S≤P, S.sum=j

private theorem grow (A R : Multiset ℕ) (complete : Complete A) :
    ∃ B T, A+R=B+T ∧ A.sum≤B.sum ∧ Complete B ∧ ∀x∈T, B.sum+2≤x := by
  induction R using Multiset.strongInductionOn generalizing A with | _ R ih =>
    by_cases eligible : ∃x∈R, x≤A.sum+1
    · obtain ⟨x,hx,small⟩ := eligible
      obtain ⟨Q,eq⟩ := exists_cons_of_mem hx
      have enlarged : Complete (x ::ₘ A) := by
        intro j hj
        by_cases low : j≤A.sum
        · obtain ⟨S,sub,wt⟩ := complete j low
          exact ⟨S,sub.trans (le_cons_self _ _),wt⟩
        · rw [sum_cons] at hj
          obtain ⟨S,sub,wt⟩ := complete (j-x) (by omega)
          exact ⟨x ::ₘ S,cons_le_cons _ sub,by rw [sum_cons,wt]; omega⟩
      obtain ⟨B,T,split,wt,filled,lo⟩ := ih Q (eq ▸ lt_cons_self _ _) (x ::ₘ A) enlarged
      exact ⟨B,T,by simpa [eq] using split,(by simp : A.sum≤(x ::ₘ A).sum).trans wt,filled,lo⟩
    · exact ⟨A,R,rfl,le_rfl,complete,fun x hx ↦ by by_contra! small; exact eligible ⟨x,hx,by omega⟩⟩

private theorem one_gap {f : ℕ} {P : Multiset ℕ} (pos : ∀x∈P, 0<x)
    (avoid : Avoids f P) (many : f<P.card) (one : 1∈P) : 2*P.card+f≤P.sum+1 := by
  obtain ⟨R,split⟩ := exists_cons_of_mem one
  have full : Complete {1} := by
    intro j hj
    simp only [sum_singleton] at hj
    rcases show j=0 ∨ j=1 by omega with rfl|rfl
    · exact ⟨0,Multiset.zero_le _,rfl⟩
    · exact ⟨{1},le_rfl,rfl⟩
  obtain ⟨A,T,eq,posA,complete,lo⟩ := grow {1} R full
  have peq : P=A+T := by simpa [split] using eq
  have sub : A≤P := peq ▸ Multiset.le_add_right _ _
  have small : A.sum<f := by
    by_contra! high
    obtain ⟨U,le,weight⟩ := complete f high
    exact avoid U (le.trans sub) weight
  have ca := card_le_mass (P:=A) fun x hx ↦ pos x (subset_of_le sub hx)
  have ct := mass_lower lo
  simp only [sum_singleton] at posA
  have cards := congrArg Multiset.card peq
  have total := congrArg Multiset.sum peq
  rw [card_add] at cards
  rw [sum_add] at total
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le posA
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le (show A.sum+1≤f by omega)
  have wt := Nat.mul_le_mul_left A.sum (show f+1≤A.sum+T.card by omega)
  nlinarith [Nat.zero_le (a*b),congrArg (A.sum*·) hb,congrArg (·*b) ha]

private theorem odd_weight {f : ℕ} (fo : Odd f) (P : Multiset ℕ) (pos : ∀x∈P, 0<x)
    (avoid : Avoids f P) (many : f<P.card) (so : Odd P.sum) : 2*P.card+f≤P.sum := by
  induction f using Nat.strong_induction_on generalizing P with | ind f ih =>
    have of := Nat.odd_iff.mp fo
    have os := Nat.odd_iff.mp so
    by_cases one : 1∈P
    · have := one_gap pos avoid many one
      omega
    have low (x) (hx : x∈P) : 2≤x := by
      have := pos x hx
      by_contra! bad
      have eq : x=1 := by omega
      exact one (eq ▸ hx)
    have w2 := mass_lower low
    by_contra! light
    have two : 2∈P := by
      by_contra no
      have w := mass_lower (P:=P) (m:=3) (fun x hx ↦ by
        have := low x hx
        by_contra! small
        have eq : x=2 := by omega
        exact no (eq ▸ hx))
      omega
    obtain ⟨S,es⟩ := exists_cons_of_mem two
    obtain ⟨b,hb,large⟩ : ∃ b∈S, 2<b := by
      by_contra! all
      have w := S.sum_le_card_nsmul 2 all
      change S.sum≤S.card*2 at w
      simp only [es,card_cons,sum_cons] at w2 os
      omega
    obtain ⟨T,et⟩ := exists_cons_of_mem hb
    let Q := (b-2) ::ₘ T
    have peq : P=2 ::ₘ b ::ₘ T := by rw [es,et]
    have qt : Q.sum+4=P.sum := by simp [Q,peq]; omega
    have qc : Q.card+1=P.card := by simp [Q,peq,Nat.add_assoc]
    have ff : 2<f := by omega
    have positive : ∀x∈Q, 0<x := by
      intro x hx
      rcases mem_cons.mp hx with eq|mt
      · omega
      · exact pos x (peq ▸ mem_cons_of_mem (mem_cons_of_mem mt))
    have av : Avoids (f-2) Q := by
      intro U sub wt
      by_cases hit : b-2∈U
      · obtain ⟨V,rfl⟩ := exists_cons_of_mem hit
        have st := (cons_le_cons_iff _).mp sub
        have lifts : b ::ₘ V≤P := peq ▸ (cons_le_cons _ st).trans (le_cons_self _ _)
        apply avoid _ lifts
        rw [sum_cons] at wt ⊢
        omega
      · have st : U≤T := (le_cons_of_notMem hit).mp sub
        apply avoid (2 ::ₘ U) (peq ▸ cons_le_cons _ (st.trans (le_cons_self _ _)))
        rw [sum_cons,wt]; omega
    have := ih (f-2) (by omega) (Nat.odd_iff.mpr (by omega)) Q positive av (by omega)
      (Nat.odd_iff.mpr (by omega))
    omega

private theorem least_two {f : ℕ} (fo : Odd f) : LeastNondivisor f 2 := by
  refine ⟨by decide,?_,?_⟩
  · have := Nat.odd_iff.mp fo
    rintro ⟨j,hj⟩
    omega
  · intro s hs sl
    rw [show s=1 by omega]
    exact one_dvd _

/-- The exact optimum for odd f and either parity of the total. -/
theorem odd_exact {f r : ℕ} (fo : Odd f) (hr : f≤r) :
    rho f (f+r) = if Odd r then (f+r)/2 else max f (r/2) := by
  have of := Nat.odd_iff.mp fo
  have hf : 0<f := by omega
  obtain ⟨P,p,pk⟩ := optimum hf (by omega : f<f+r)
  by_cases ro : Odd r
  · rw [ite_eq_left ro]
    have er := Nat.odd_iff.mp ro
    have mass : (f+r)/2*2=f+r := by omega
    have twos : Partition f (f+r) (replicate ((f+r)/2) 2) := by
      refine ⟨fun x hx ↦ by rw [eq_of_mem_replicate hx]; decide,by simpa using mass,?_⟩
      intro U sub hit
      obtain ⟨k,_,rfl⟩ := le_replicate_iff.mp sub
      have eq : k*2=f := by simpa using hit
      omega
    have lb := card_le_rho twos
    rw [card_replicate] at lb
    by_contra! unequal
    have many : f<P.card := by omega
    by_cases one : 1∈P
    · have v := one_gap p.1 p.2.2 many one
      rw [p.2.1] at v
      omega
    · have v := mass_lower (P:=P) (m:=2) (fun x hx ↦ by
        have := p.1 x hx
        by_contra! small
        have e : x=1 := by omega
        exact one (e ▸ hx))
      rw [p.2.1] at v
      omega
  · rw [ite_eq_right ro]
    have er : r%2≠1 := fun h ↦ ro (Nat.odd_iff.mpr h)
    have lower := base_lower hf (by omega : 0<r) (least_two fo)
    have ones := ones_lower hf hr
    apply le_antisymm _ (max_le_iff.mpr ⟨ones,by omega⟩)
    by_cases many : f<P.card
    · have v := odd_weight fo P p.1 p.2.2 many (Nat.odd_iff.mpr (by rw [p.2.1]; omega))
      rw [p.2.1] at v
      exact (show rho f (f+r)≤r/2 by omega).trans (le_max_right _ _)
    · exact (show rho f (f+r)≤f by omega).trans (le_max_left _ _)

/-- The last failed step is exactly 2f−2 for every odd f≥3. -/
theorem odd_threshold {f : ℕ} (fo : Odd f) (hf : 3≤f) :
    LeastNondivisor f 2 ∧ rho f (3*f)≠rho f (3*f-2)+1 ∧
      ∀ r, 2*f-2<r → rho f (f+r+2)=rho f (f+r)+1 := by
  have of := Nat.odd_iff.mp fo
  have a := odd_exact (r:=2*f-2) fo (by omega)
  have b := odd_exact (r:=2*f) fo (by omega)
  rw [ite_eq_right (by intro h; have := Nat.odd_iff.mp h; omega)] at a b
  rw [show f+(2*f-2)=3*f-2 by omega] at a
  rw [show f+2*f=3*f by omega] at b
  refine ⟨least_two fo,by omega,?_⟩
  intro r high
  have c := odd_exact (r:=r) fo (by omega)
  have d := odd_exact (r:=r+2) fo (by omega)
  rw [←Nat.add_assoc] at d
  by_cases ro : Odd r
  · have ro2 := Nat.odd_iff.mpr (show (r+2)%2=1 by have := Nat.odd_iff.mp ro; omega)
    rw [ite_eq_left ro] at c
    rw [ite_eq_left ro2] at d
    omega
  · have ro2 : ¬Odd (r+2) := by intro h; apply ro; apply Nat.odd_iff.mpr; have := Nat.odd_iff.mp h; omega
    rw [ite_eq_right ro] at c
    rw [ite_eq_right ro2] at d
    have er : r%2≠1 := fun h ↦ ro (Nat.odd_iff.mpr h)
    omega

/-- info: 'TanWuHon.odd_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_exact

/-- info: 'TanWuHon.odd_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_threshold

end TanWuHon
