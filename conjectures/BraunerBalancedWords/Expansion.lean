module

public import conjectures.BraunerBalancedWords.Statement
import Mathlib.Tactic.Ring

public section
namespace BraunerBalancedWords
open Finset

theorem count_succ {n : ℕ} (w : Word n) (a : Fin n) (x : ℤ) (N : ℕ) :
    count w a x (N+1)=count w a x N+(if w (x+N)=a then 1 else 0) := by
  simp [count,sum_range_succ]

theorem count_telescope {n : ℕ} {w : Word n} {a : Fin n} (F : ℤ → ℤ)
    (inc : ∀ x : ℤ, F (x+1)=F x+(if w x=a then 1 else 0)) (x : ℤ) (N : ℕ) :
    count w a x N=F (x+N)-F x := by
  induction N with
  | zero => simp [count]
  | succ n ih =>
    rw [count_succ,ih]
    push_cast
    rw [←add_assoc,inc]
    omega

theorem blocks {n D : ℕ} {w : Word n} (period : Periodic w D) (a : Fin n) (k : ℕ) :
    count w a 0 (k*D)=k*count w a 0 D := by
  have shift (x : ℤ) (j : ℕ) : w (x+(j:ℤ)*D)=w x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ,add_mul,one_mul,←add_assoc,period,ih]
  induction k with
  | zero => simp [count]
  | succ k ih =>
    rw [Nat.succ_mul]
    unfold count at *
    rw [sum_range_add]
    simp only [zero_add,Nat.cast_add,Nat.cast_succ,Nat.cast_mul,add_mul,one_mul] at ih ⊢
    rw [ih]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [add_comm,shift]

theorem quotient_tick (z d : ℤ) (hd : 0<d) :
    (z+1)/d=z/d+(if z%d=d-1 then 1 else 0) := by
  by_cases one : d=1
  · simp [one]
  have h1 : 1%d=1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h0 : 1/d=0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have r0:=Int.emod_nonneg z (by omega : d≠0)
  have r1:=Int.emod_lt_of_pos z hd
  rw [Int.add_ediv_of_pos hd,h1,h0]
  by_cases h : z%d=d-1 <;> simp (disch := omega) [h]; omega

theorem Substitution.project {m n : ℕ} {v : Word m} {w : Word n}
    (s : Substitution v w) (x : ℤ) : s.parent (w x)=v x :=
  ((s.occurs x (w x)).mp rfl).1.symm

theorem Substitution.count_dvd {m n D : ℕ} {v : Word m} {w : Word n}
    (s : Substitution v w) (hw : Periodic w D) (b : Fin n) :
    count w b 0 D ∣ count v (s.parent b) 0 D := by
  let a:=s.parent b
  let h:=s.stride b
  let I:=s.index a
  let p:=s.phase b
  have pos : (0:ℤ)<h:=by exact_mod_cast s.positive b
  have occ (x : ℤ) : w x=b ↔ v x=a ∧ (I x+p)%(h:ℤ)=(h:ℤ)-1:=s.occurs x b
  have num:=s.numbering a
  change I 0=0 ∧ _ at num
  have step (x : ℤ) : (I (x+1)+p)/(h:ℤ)=(I x+p)/(h:ℤ)+(if w x=b then 1 else 0) := by
    rw [show I (x+1)=I x+(if v x=a then 1 else 0) from num.2 x]
    by_cases yes : v x=a
    · rw [ite_eq_left yes,show I x+1+p=I x+p+1 by ring,quotient_tick _ _ pos]
      simp [occ,yes]
    · simp [occ,yes]
  have hv : Periodic v D := by intro x; rw [←s.project,hw,s.project]
  have base:=count_telescope I num.2 0 (h*D)
  have lifts:=count_telescope (fun z => (I z+p)/(h:ℤ)) step 0 (h*D)
  rw [blocks hv _ h] at base
  rw [blocks hw _ h] at lifts
  simp only [zero_add,num.1,sub_zero] at base lifts
  rw [←base,Int.mul_add_ediv_left _ _ (by omega : (h:ℤ)≠0)] at lifts
  refine ⟨h,?_⟩
  change count v a 0 D = count w b 0 D * (h:ℤ)
  rw [mul_comm]
  omega

theorem Expansion.project {m n D : ℕ} {v : Word m} {w : Word n}
    (build : Expansion v w) (hp : Periodic w D) :
    ∃ f : Fin n → Fin m, (∀ x, f (w x)=v x) ∧
      ∀ b, count w b 0 D ∣ count v (f b) 0 D := by
  induction build with
  | refl => exact ⟨id,fun _ => rfl,fun _ => dvd_refl _⟩
  | step old s ih =>
    obtain ⟨f,link,freq⟩:=ih (fun x => by rw [←s.project,hp,s.project])
    exact ⟨f ∘ s.parent,fun x => by simp [Function.comp_apply,s.project,link],
      fun b => dvd_trans (s.count_dvd hp b) (freq _)⟩

end BraunerBalancedWords
