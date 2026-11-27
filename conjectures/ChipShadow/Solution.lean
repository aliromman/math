module

public import conjectures.ChipShadow.Absorption
public import conjectures.ChipShadow.RoomKnots
public import conjectures.ChipShadow.Rooms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

@[expose] public section
noncomputable section
namespace ChipShadow
open Finset

private theorem expect_of_run {n : ℕ} (f : State n→ℚ)
    (h : ∀ w,∀ B∈blocks w,∑ i∈range (span B), f (push w B i)=span B*f w)
    (t : ℕ) (w : State n) : expect f t w=f w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    by_cases z : choices w=0
    · simp [expect,z]
    · simp only [expect,ite_eq_right z,ih]
      rw [sum_congr rfl (h w),←sum_mul]
      have casts : (∑ B∈blocks w,(span B:ℚ))=(choices w:ℚ) := by simp [choices]
      rw [casts,mul_comm, mul_div_cancel_right₀ _ (by exact_mod_cast z)]

private theorem expect_const {n : ℕ} (a : ℚ) (t : ℕ) (w : State n) :
    expect (fun _ ↦ a) t w=a :=
  expect_of_run _ (by intro w B _;simp) t w

theorem expect_mass {n : ℕ} (k t : ℕ) (w : State n) : expect (mass k) t w=mass k w :=
  expect_of_run _ (fun _ _ h ↦ harmonic_run (mem_blocks.mp h) k) t w

private theorem expect_linear {ι : Type*} {n : ℕ} (s : Finset ι)
    (c : ι→ℚ) (f : ι→State n→ℚ) (t : ℕ) (w : State n) :
    expect (fun v ↦ ∑ x∈s,c x*f x v) t w=∑ x∈s,c x*expect (f x) t w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    by_cases z : choices w=0
    · simp [expect,z]
    · simp only [expect,ite_eq_right z,ih,mul_div_assoc',←sum_div]
      congr 1
      calc
        _ = ∑ B∈blocks w,∑ x∈s,∑ i∈range (span B),c x*expect (f x) t (push w B i) := by
          apply sum_congr rfl;intro B _;exact sum_comm
        _ = _ := by rw [sum_comm];simp only [mul_sum]

private theorem read_shadow {n : ℕ} {w : State n} {r : Fin n} (h : shadow r w)
    (c : Fin n → ℚ) : (∑ i,c i*indicator i w)=c r := by
  classical
  rw [sum_eq_single r]
  · simp [indicator,h]
  · intro j _ neq
    simp [indicator,show ¬shadow j w from fun b ↦ neq (shadow_unique b h)]
  · simp

/-- At every time beyond the bound, each of the n possible double gaps has probability 1/n. -/
theorem uniform {n : ℕ} (hn : 0<n) {t : ℕ} (ht : remaining (initial n)≤t) (r : Fin n) :
    expect (indicator r) t (initial n)=1/(n:ℚ) := by
  classical
  let p (i : ℕ) : ℚ := if hi : i<n then expect (indicator ⟨i,hi⟩) t (initial n) else 0
  have lookup (j : Fin n) : p j.val=expect (indicator j) t (initial n) := by simp [p,j.isLt]
  have eq (k : ℕ) : diagonal n k p=0 := by
    let c (j : Fin n) := corner (j.val+1) (n-j.val) k
    have matchPayoff (w : State n) (g : Good w) (stop : choices w=0) :
        (∑ j,c j*indicator j w)=mass k w := by
      obtain ⟨j,s,b⟩ := terminal_shadow hn g stop
      rw [read_shadow s,mass_shadow s b]
    have law := terminal_expect _ _ matchPayoff t (initial_good n) ht
    change expect (fun w ↦ ∑ j,c j*indicator j w) t (initial n)=expect (mass k) t (initial n) at law
    rw [expect_linear,expect_mass,mass_initial hn] at law
    rw [diagonal,←Fin.sum_univ_eq_sum_range (fun i ↦ p i*corner (i+1) (n-i) k)]
    simpa only [lookup,c,mul_comm] using law
  have equal := diagonal_constant n p eq
  have each (i : Fin n) : expect (indicator i) t (initial n)=p 0 := (lookup i).symm.trans (equal _ i.isLt)
  have total : expect (fun w ↦ ∑ j : Fin n,(1:ℚ)*indicator j w) t (initial n)=
      expect (fun _ ↦ 1) t (initial n) := by
    apply terminal_expect _ _ _ t (initial_good n) ht
    intro w g stop
    obtain ⟨j,s,_⟩ := terminal_shadow hn g stop
    exact read_shadow s (fun _ ↦ 1)
  rw [expect_linear,expect_const] at total
  simp only [each,one_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  rw [each,eq_div_iff (by exact_mod_cast hn.ne')]
  simpa only [mul_comm] using total

theorem resolution : Conjecture :=
  fun n hn r ↦ ⟨remaining (initial n),fun _ ht ↦ uniform hn ht r⟩

/-- info: 'ChipShadow.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end ChipShadow
end
