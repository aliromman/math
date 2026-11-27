module

public import conjectures.TanWuHon.Statement
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.ModEq

public section
namespace TanWuHon
open Multiset

theorem mass_lower {P : Multiset ℕ} {m : ℕ} (h : ∀ x∈P, m≤x) : m*P.card≤P.sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons x P ih =>
    have hx := h x (by simp)
    have hP := ih (fun y hy ↦ h y (mem_cons_of_mem hy))
    simp only [sum_cons,card_cons,Nat.mul_succ]
    omega

theorem card_le_mass {P : Multiset ℕ} (h : ∀ x∈P, 0<x) : P.card≤P.sum := by
  simpa using mass_lower (m:=1) h

theorem card_le_rho {f n : ℕ} {P : Multiset ℕ} (h : Partition f n P) : P.card≤rho f n := by
  classical
  exact Nat.le_findGreatest ((card_le_mass h.1).trans_eq h.2.1) ⟨P,h,rfl⟩

theorem avoids_mono {P Q : Multiset ℕ} {f : ℕ} (h : Avoids f P) (le : Q≤P) : Avoids f Q :=
  fun _ hu ↦ h _ (hu.trans le)

theorem avoids_large {P : Multiset ℕ} {f t : ℕ} (ht : f<t) (h : Avoids f P) :
    Avoids f (t ::ₘ P) := by
  intro U hu e
  by_cases mt : t∈U
  · have := Multiset.single_le_sum (fun x (_ : x∈U) ↦ Nat.zero_le x) t mt
    omega
  · exact h U ((le_cons_of_notMem mt).mp hu) e

theorem optimum {f n : ℕ} (hf : 0<f) (hn : f<n) : ∃ P, Partition f n P ∧ P.card=rho f n := by
  classical
  have single : Partition f n {n} := by
    refine ⟨by simpa using (hf.trans hn),by simp,?_⟩
    exact avoids_large (P:=0) hn (by intro U hu; have he : U=0 := le_bot_iff.mp hu; simpa [he] using hf.ne)
  exact Nat.findGreatest_spec (P:=fun k ↦ ∃ P, Partition f n P ∧ P.card=k)
    (by omega : 1≤n) ⟨{n},single,by simp⟩

theorem base_lower {f r L : ℕ} (hf : 0<f) (hr : 0<r) (hL : LeastNondivisor f L) :
    r≤L*rho f (f+r) := by
  let j := (r-1)/L
  have jl : j*L≤r-1 := Nat.div_mul_le_self _ _
  have rem : r≤(j+1)*L := by have h := (Nat.div_lt_iff_lt_mul hL.1).mp (Nat.lt_succ_self ((r-1)/L)); change r-1<((r-1)/L+1)*L at h; dsimp [j]; omega
  let t := f+(r-j*L)
  have ht : f<t := by dsimp [t]; omega
  have hP : Partition f (f+r) (t ::ₘ replicate j L) := by
    refine ⟨?_,?_,avoids_large ht ?_⟩
    · intro x hx
      rcases mem_cons.mp hx with rfl|hx
      · omega
      · rw [eq_of_mem_replicate hx]; exact hL.1
    · simp [t]; omega
    · intro U hu h
      obtain ⟨k,_,rfl⟩ := le_replicate_iff.mp hu
      exact hL.2.1 ⟨k,by simpa [mul_comm] using h.symm⟩
  have v := card_le_rho hP
  simp only [card_cons,card_replicate] at v
  exact rem.trans ((Nat.mul_le_mul_right L v).trans_eq (Nat.mul_comm _ _))

theorem add_least {f L : ℕ} {P : Multiset ℕ} (hL : 0<L) (h : Avoids f P)
    (count : f/L≤P.count L) : Avoids f (L ::ₘ P) := by
  intro Q hQ eq
  by_cases hit : L∈Q
  · obtain ⟨U,rfl⟩ := exists_cons_of_mem hit
    have hU := (cons_le_cons_iff L).mp hQ
    have eq' : L+U.sum=f := by simpa using eq
    have copies : U.count L*L≤U.sum := by
      obtain ⟨R,e⟩ := Multiset.le_iff_exists_add.mp (le_count_iff_replicate_le.mp (le_refl (U.count L)))
      conv_rhs => rw [e]
      simp
    have lt : U.count L<P.count L := by
      by_contra! bad
      have le := Nat.mul_le_mul_right L (count.trans bad)
      have div := (Nat.div_lt_iff_lt_mul hL).mp (Nat.lt_succ_self (f/L))
      rw [Nat.succ_mul] at div
      omega
    apply h _ (Multiset.le_iff_count.mpr ?_) eq
    intro x
    by_cases ex : x=L
    · subst x; rw [count_cons_self]; omega
    · simpa [count_cons_of_ne ex] using Multiset.count_le_of_le x hU
  · exact h Q ((le_cons_of_notMem hit).mp hQ) eq

private theorem zero_block {s : ℕ} (hs : 0<s) (P : Multiset ℕ) (count : s≤P.card) :
    ∃ U≤P, 0<U.card ∧ U.card≤s ∧ s∣U.sum := by
  induction P using Quotient.inductionOn with | _ l =>
    change s≤l.length at count
    let residues (i : Fin (s+1)) : Fin s := ⟨(l.take i.val).sum%s,Nat.mod_lt _ hs⟩
    obtain ⟨i,j,ne,e⟩ := Fintype.exists_ne_map_eq_of_card_lt residues (by simp)
    have step (i j : Fin (s+1)) (ord : i<j) (e : residues i=residues j) :
        ∃ U≤(l:Multiset ℕ), 0<U.card ∧ U.card≤s ∧ s∣U.sum := by
      let q := (l.take j.val).drop i.val
      have concat : l.take i.val ++ q=l.take j.val := by
        simpa [q,List.take_take,Nat.min_eq_left ord.le] using (List.take_append_drop i.val (l.take j.val))
      have hd : s∣q.sum := by
        have h : (l.take i.val).sum ≡ (l.take j.val).sum [MOD s] := Fin.val_eq_of_eq e
        rw [←concat,List.sum_append] at h
        exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_left_cancel' _
          (show (l.take i.val).sum+0 ≡ (l.take i.val).sum+q.sum [MOD s] by simpa using h)).symm)
      have qi : i.val<j.val := ord
      have jp := j.isLt
      refine ⟨(q : Multiset ℕ),?_,?_,?_,hd⟩
      · exact Multiset.coe_le.mpr ((List.drop_sublist _ _).trans (List.take_sublist _ _)).subperm
      · change 0<q.length
        simp only [q,List.length_drop,List.length_take]
        omega
      · change q.length≤s
        simp only [q,List.length_drop,List.length_take]
        omega
    rcases lt_or_gt_of_ne ne with lo|hi
    · exact step i j lo e
    · exact step j i hi e.symm

private def Covers (s k : ℕ) (P : Multiset ℕ) : Prop :=
  ∀ j≤k, ∃ U≤P, U.sum=j*s

private theorem filled {s M : ℕ} (hs : 0<s) (P : Multiset ℕ) (hP : ∀ x∈P, x≤M) :
    ∃ A R k, P=A+R ∧ R.card<s ∧ A.sum=k*s ∧ Covers s (M+k) (replicate M s+A) := by
  induction P using Multiset.strongInductionOn with | _ P ih =>
    by_cases small : P.card<s
    · refine ⟨0,P,0,by simp,small,by simp,?_⟩
      intro j hj
      exact ⟨replicate j s,by simpa using replicate_mono s (by simpa using hj),by simp⟩
    · obtain ⟨U,leU,pos,len,dvd⟩ := zero_block hs P (by omega)
      obtain ⟨T,e⟩ := Multiset.le_iff_exists_add.mp leU
      have lt : T<P := by
        rw [e]
        exact lt_add_of_pos_left T (lt_of_le_of_ne (Multiset.zero_le _) (Ne.symm (Multiset.card_pos.mp pos)))
      obtain ⟨A,R,k,eq,rc,sum,cov⟩ := ih T lt (fun x hx ↦ hP x (e ▸ mem_add.mpr (.inr hx)))
      obtain ⟨u,ueq⟩ := dvd
      have um : u≤M := by
        have v := U.sum_le_card_nsmul M (fun x hx ↦ hP x (subset_of_le leU hx))
        rw [ueq] at v
        change s*u≤U.card*M at v
        have := v.trans (Nat.mul_le_mul_right M len)
        exact Nat.le_of_mul_le_mul_left this hs
      refine ⟨U+A,R,k+u,by rw [e,eq,add_assoc],rc,by rw [sum_add,sum,ueq,Nat.add_mul,Nat.mul_comm s u,add_comm],?_⟩
      intro j hj
      by_cases jlow : j≤M+k
      · obtain ⟨V,hV,v⟩ := cov j jlow
        exact ⟨V,hV.trans (by rw [add_left_comm (replicate M s)]; exact Multiset.le_add_left _ _),v⟩
      · have ju : u≤j := by omega
        obtain ⟨V,hV,v⟩ := cov (j-u) (by omega)
        refine ⟨U+V,by rw [add_left_comm (replicate M s)]; exact add_le_add_right hV U,?_⟩
        rw [sum_add,v,ueq,Nat.sub_mul,Nat.mul_comm s u]
        have := Nat.mul_le_mul_right s ju
        omega

/-- Remove blocks of total weight divisible by s until fewer than s parts remain. -/
theorem split_residues {s : ℕ} (hs : 0<s) (P : Multiset ℕ) :
    ∃ A R k, P=A+R ∧ R.card<s ∧ A.sum=k*s := by
  obtain ⟨A,R,k,eq,rc,mass,_⟩ := filled (M:=P.sum) hs P fun x hx ↦
    Multiset.single_le_sum (fun y (_ : y∈P) ↦ Nat.zero_le y) x hx
  exact ⟨A,R,k,eq,rc,mass⟩

theorem few_bounded {f s M : ℕ} (hs : 0<s) (df : s∣f) {P : Multiset ℕ}
    (pos : ∀ x∈P, 0<x) (bounded : ∀ x∈P, x≤M) (hn : Avoids f P)
    (cnt : M≤P.count s) : P.card<f := by
  obtain ⟨Q,e⟩ := Multiset.le_iff_exists_add.mp (le_count_iff_replicate_le.mp cnt)
  obtain ⟨A,R,k,eq,rc,mass,cov⟩ := filled hs Q
    (fun x hx ↦ bounded x (e ▸ mem_add.mpr (.inr hx)))
  obtain ⟨n,fn⟩ := df
  have cap : M+k<n := by
    by_contra! le
    obtain ⟨U,ule,su⟩ := cov n le
    apply hn U (ule.trans (by rw [e,eq,←add_assoc]; exact Multiset.le_add_right _ _))
    rw [su,fn,Nat.mul_comm]
  have sub : replicate M s+A≤P := by rw [e,eq,←add_assoc]; exact Multiset.le_add_right _ _
  have low := card_le_mass (P:=replicate M s+A) (fun x hx ↦ pos x (subset_of_le sub hx))
  simp only [sum_add,sum_replicate,nsmul_eq_mul,mass,card_add,card_replicate] at low
  change M+A.card≤M*s+k*s at low
  have cs : (M+k+1)*s≤n*s := Nat.mul_le_mul_right s (show M+k+1≤n by omega)
  rw [Nat.add_mul,Nat.add_mul,one_mul,Nat.mul_comm n s,←fn] at cs
  rw [e,eq,card_add,card_add,card_replicate]
  omega

/-- Use f−1 ones and one part larger than f. -/
theorem ones_lower {f r : ℕ} (hf : 0<f) (hr : f≤r) : f≤rho f (f+r) := by
  have p : Partition f (f+r) ((r+1) ::ₘ replicate (f-1) 1) := by
    refine ⟨?_,by simp; omega,avoids_large (by omega) ?_⟩
    · intro x hx
      rcases mem_cons.mp hx with eq|small
      · omega
      · rw [eq_of_mem_replicate small]; decide
    · intro U hu mass
      obtain ⟨k,hk,rfl⟩ := le_replicate_iff.mp hu
      have eq : k=f := by simpa using mass
      omega
  simpa only [card_cons,card_replicate,Nat.sub_add_cancel hf] using card_le_rho p

end TanWuHon
