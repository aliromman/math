module

public import conjectures.KurzWeighted.Influence
import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace KurzWeighted
open Finset Equiv
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def deviation (f : Rule V) (d : V) (B : ℝ) : ℝ :=
  ∑ i ∈ univ.erase d, |swings f i-B|

private theorem perm_cost {f : Rule V} (comp : Complete f) (B : ℝ) (p : Perm V) :
    distance f (rename p f) ≤ 2*∑ i ∈ p.support, |swings f i-B| := by
  let v := fun i ↦ |swings f i-B|
  have inductionBound (n : ℕ) (P : Perm V) (sz : P.support.card=n) :
      distance f (rename P f) ≤ 2*∑ i ∈ P.support, v i := by
    induction n using Nat.strong_induction_on generalizing P with
    | ind n ih =>
      by_cases hp : P=1
      · subst P
        simp [distance,rename,Perm.one_def,Equiv.finsetCongr_refl]
      obtain ⟨i,hi,largest⟩ := exists_max_image P.support v (Finset.nonempty_iff_ne_empty.mpr (fun e ↦ hp (Perm.support_eq_empty_iff.mp e)))
      let s := swap i (P i)
      let Q := s*P
      have sub : Q.support ⊆ P.support.erase i := by
        intro t h
        obtain ⟨ht,ne⟩ := Perm.mem_support_swap_mul_imp_mem_support_ne h
        exact mem_erase.mpr ⟨ne,ht⟩
      have lower : Q.support.card < n := by simpa [sz] using Perm.card_support_swap_mul (Perm.mem_support.mp hi)
      have bound := ih _ lower Q rfl
      have sumle : (∑ t ∈ Q.support, v t) ≤ ∑ t ∈ P.support.erase i, v t :=
        sum_le_sum_of_subset_of_nonneg sub (fun t _ _ ↦ abs_nonneg _)
      have cost : distance f (rename s f) ≤ 2*v i := by
        rw [dist_swap comp]
        have a := abs_sub_le (swings f i) B (swings f (P i))
        rw [abs_sub_comm B] at a
        have b := largest (P i) (Perm.apply_mem_support.mpr hi)
        change |swings f i-swings f (P i)|≤2*v i
        dsimp [v] at a b ⊢
        linarith
      have same : s*Q=P := by simp [s,Q,←mul_assoc]
      have tri := dist_triangle f (rename Q f) (rename Q (rename s f))
      rw [dist_rename,←rename_mul,same] at tri
      have partition := add_sum_erase P.support v hi
      linarith
  exact inductionBound _ p rfl

noncomputable def fixers (d : V) : Subgroup (Perm V) where
  carrier := {p | p d=d}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; exact (congrArg a hb).trans ha
  inv_mem' := by intro a ha; exact (a.symm_apply_eq.mpr ha.symm)

noncomputable instance (d : V) : Fintype (fixers d) := Fintype.ofFinite _

noncomputable def votes (d : V) (f : Rule V) (S : Finset V) : ℝ :=
  ∑ p : fixers d, rename p.val f S

/-- Take the majority decision over all relabelings that fix the distinguished voter. -/
noncomputable def rounded (d : V) (f : Rule V) : Rule V := fun S ↦
  if (Fintype.card (fixers d) : ℝ) ≤ 2*votes d f S then 1 else 0

omit [DecidableEq V] in
theorem rounded_binary (d : V) (f : Rule V) (S : Finset V) : rounded d f S=0 ∨ rounded d f S=1 := by
  unfold rounded
  split <;> simp

omit [DecidableEq V] in
theorem rounded_mono (d : V) {f : Rule V} (mon : Monotone f) : Monotone (rounded d f) := by
  intro S T sub
  have h : votes d f S ≤ votes d f T := sum_le_sum fun x _ ↦ mon (map_subset_map.mpr sub)
  unfold rounded
  split <;> split <;> norm_num
  linarith

omit [DecidableEq V] in
theorem rounded_symmetric (d : V) (f : Rule V) (p : Perm V) (fix : p d=d) (S : Finset V) :
    rounded d f (p.finsetCongr S) = rounded d f S := by
  let a : fixers d := ⟨p,fix⟩
  have eq : votes d f (p.finsetCongr S)=votes d f S := by
    calc
      _ = ∑ b : fixers d, rename (b*a).val f S := by
        apply sum_congr rfl
        intro b _
        exact congrFun (rename_mul b.val p f).symm S
      _ = _ := Equiv.sum_comp (Equiv.mulRight a) (fun b : fixers d ↦ rename b.val f S)
  simp only [rounded,eq]

omit [DecidableEq V] in
private theorem round_one (d : V) {f : Rule V} (binary : ∀ S,f S=0 ∨ f S=1) (S : Finset V) :
    (Fintype.card (fixers d) : ℝ)*|f S-rounded d f S| ≤
      2*∑ p : fixers d, |f S-rename p.val f S| := by
  let M : ℝ := Fintype.card (fixers d)
  have bounds (p : fixers d) : 0≤rename p.val f S ∧ rename p.val f S≤1 := by
    change 0≤f (p.val.finsetCongr S) ∧ f (p.val.finsetCongr S)≤1
    rcases binary (p.val.finsetCongr S) with h|h <;> rw [h] <;> norm_num
  rcases binary S with hv|hv
  · rw [hv]
    simp_rw [zero_sub,abs_neg,abs_of_nonneg (bounds _).1]
    have nonneg : 0≤rounded d f S := by rcases rounded_binary d f S with h|h <;> simp [h]
    rw [abs_of_nonneg nonneg]
    change M*rounded d f S≤2*votes d f S
    unfold rounded
    split
    · simpa [M]
    · rw [mul_zero]
      exact mul_nonneg (by norm_num) (sum_nonneg fun p _ ↦ (bounds p).1)
  · rw [hv]
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (bounds _).2),sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one]
    change M*|1-rounded d f S|≤2*(M-votes d f S)
    have vbound : votes d f S ≤ M := by
      calc
        _ ≤ ∑ _ : fixers d, (1:ℝ) := sum_le_sum fun p _ ↦ (bounds p).2
        _ = M := by simp [M]
    unfold rounded
    split <;> simp <;> dsimp [M] at * <;> linarith

theorem rounding_bound (d : V) (f : Rule V) (binary : ∀ S, f S=0 ∨ f S=1)
    (comp : Complete f) (B : ℝ) : distance f (rounded d f) ≤ 4*deviation f d B := by
  let M : ℝ := Fintype.card (fixers d)
  have positive : 0<M := by
    dsimp [M]
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (fixers d))
  have avg : M*distance f (rounded d f) ≤ 2*∑ p : fixers d, distance f (rename p.val f) := by
    unfold distance
    rw [sum_comm,mul_sum,mul_sum]
    apply sum_le_sum
    intro S _
    exact round_one d binary S
  have each (p : fixers d) : distance f (rename p.val f) ≤ 2*deviation f d B := by
    apply (perm_cost comp B p.val).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply sum_le_sum_of_subset_of_nonneg _ (fun t _ _ ↦ abs_nonneg _)
    intro t ht
    exact mem_erase.mpr ⟨fun h ↦ Perm.mem_support.mp ht (h ▸ p.property),mem_univ _⟩
  have sumle : (∑ p : fixers d, distance f (rename p.val f)) ≤ M*(2*deviation f d B) := by
    simpa [M] using (sum_le_sum (s := univ) fun p _ ↦ each p)
  change distance f (rounded d f) ≤ 4*deviation f d B
  apply (le_of_mul_le_mul_left _ positive)
  linarith

end KurzWeighted
