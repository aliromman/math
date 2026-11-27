module

public import conjectures.KurzWeighted.Statement
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

@[expose] public section
namespace KurzWeighted
open Finset Equiv
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def distance (f g : Rule V) : ℝ := ∑ S, |f S - g S|

def rename (p : Perm V) (f : Rule V) : Rule V := fun S ↦ f (p.finsetCongr S)

omit [Fintype V] [DecidableEq V] in
theorem rename_mul (p q : Perm V) (f : Rule V) : rename (p*q) f = rename q (rename p f) := by
  funext S
  simp [rename,finsetCongr_apply,map_map,Function.Embedding.trans]
  rfl

omit [DecidableEq V] in
theorem dist_triangle (f g h : Rule V) : distance f h ≤ distance f g + distance g h := by
  rw [distance,distance,distance,←sum_add_distrib]
  exact sum_le_sum fun i _ ↦ abs_sub_le _ _ _

omit [DecidableEq V] in
theorem dist_rename (p : Perm V) (f g : Rule V) : distance (rename p f) (rename p g)=distance f g :=
  p.finsetCongr.sum_comp (fun S ↦ |f S-g S|)

private def flip (i : V) (S : Finset V) := if i ∈ S then S.erase i else insert i S

omit [Fintype V] in
private theorem flip_twice (i : V) (S : Finset V) : flip i (flip i S)=S := by
  by_cases h : i∈S <;> simp [flip,h]

private def flipPerm (i : V) : Perm (Finset V) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_twice i
  right_inv := flip_twice i

def sign (i : V) (S : Finset V) : ℝ := if i∈S then 1 else -1

theorem swings_signed (f : Rule V) (i : V) : swings f i=∑ S, sign i S*f S := by
  let a : Finset V → ℝ := fun S ↦ if i∈S then f S else 0
  let b : Finset V → ℝ := fun S ↦ if i∈S then 0 else f S
  have eq : swings f i = ∑ S, (a (flipPerm i S)-b S) := by
    apply sum_congr rfl
    intro S _
    by_cases h : i∈S <;> simp [a,b,flipPerm,flip,h]
  rw [eq,sum_sub_distrib,Equiv.sum_comp (flipPerm i) a,←sum_sub_distrib]
  apply sum_congr rfl
  intro S _
  by_cases h : i∈S <;> simp [a,b,sign,h]

theorem swing_lipschitz (f g : Rule V) (i : V) : |swings f i-swings g i|≤distance f g := by
  rw [swings_signed,swings_signed,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro S _
  by_cases h : i∈S <;> simp [sign,h]
  grind [abs_sub_comm]

omit [Fintype V] in
theorem map_swap_of_same (S : Finset V) {i j : V} (h : i∈S ↔ j∈S) :
    (swap i j).finsetCongr S = S := by
  ext a
  simp only [finsetCongr_apply,mem_map_equiv,symm_swap]
  by_cases ai : a=i
  · subst a; simpa using h.symm
  by_cases aj : a=j
  · subst a; simpa using h
  simp [swap_apply_of_ne_of_ne ai aj]

omit [Fintype V] in
theorem map_swap_of_mem (S : Finset V) {i j : V} (hi : i∈S) (hj : j∉S) :
    (swap i j).finsetCongr S = insert j (S.erase i) := by
  have neq : i≠j := by aesop
  ext a
  simp only [finsetCongr_apply,mem_map_equiv,symm_swap,mem_insert,mem_erase]
  by_cases ai : a=i
  · subst a; simp [neq,hj]
  by_cases aj : a=j
  · subst a; simp [hi]
  simp [swap_apply_of_ne_of_ne ai aj,ai,aj]

omit [Fintype V] in
/-- Replacing an absent voter by a voter of at least equal weight preserves a win. -/
theorem weighted_swap {w : V → ℝ} (q : ℝ) {i j : V} (hij : w j≤w i) (S : Finset V)
    (hi : i∈S) (hj : j∉S) : rename (swap i j) (weighted w q) S ≤ weighted w q S := by
  have e : ∑ a ∈ S, w a = w i + ∑ a ∈ S.erase i, w a := (add_sum_erase S w hi).symm
  have hj' : j∉S.erase i := fun h ↦ hj (mem_of_mem_erase h)
  simp only [rename,map_swap_of_mem S hi hj,weighted,sum_insert hj',e]
  split <;> split <;> norm_num
  linarith

private theorem swings_rename (p : Perm V) (f : Rule V) (i : V) :
    swings (rename p f) i = swings f (p i) := by
  rw [swings_signed,swings_signed,←p.finsetCongr.sum_comp (fun S ↦ sign (p i) S*f S)]
  apply sum_congr rfl
  intro S _
  simp [rename,sign,finsetCongr_apply]

theorem dist_swap_ordered (f : Rule V) {i j : V}
    (ord : ∀ S, i∈S → j∉S → rename (swap i j) f S≤f S) :
    distance f (rename (swap i j) f) = swings f i - swings f j := by
  let g := rename (swap i j) f
  change distance f g = swings f i - swings f j
  have raw : swings g i=swings f j := by simpa [g] using swings_rename (swap i j) f i
  rw [←raw,swings_signed,swings_signed,←sum_sub_distrib]
  apply sum_congr rfl
  intro S _
  by_cases hi : i∈S <;> by_cases hj : j∈S
  · have eq : g S=f S := by simp [g,rename,map_swap_of_same S (show i∈S ↔ j∈S by simp [hi,hj])]
    simp [eq]
  · have le : g S≤f S := ord S hi hj
    simp [sign,hi,abs_of_nonneg (sub_nonneg.mpr le)]
  · have le : f S≤g S := by
      have si : i∈(swap i j).finsetCongr S := by simpa [finsetCongr_apply] using hj
      have sj : j∉(swap i j).finsetCongr S := by simpa [finsetCongr_apply] using hi
      have inv : (swap i j).finsetCongr ((swap i j).finsetCongr S) = S := by
        simpa only [Equiv.finsetCongr_symm, symm_swap] using ((swap i j).finsetCongr.symm_apply_apply S)
      simpa only [g,rename,inv] using ord ((swap i j).finsetCongr S) si sj
    simp [sign,hi,abs_of_nonpos (sub_nonpos.mpr le)]
    linarith
  · have eq : g S=f S := by simp [g,rename,map_swap_of_same S (show i∈S ↔ j∈S by simp [hi,hj])]
    simp [eq]

/-- A game is complete if either voter in each pair can replace the other in any winning coalition. -/
def Complete (f : Rule V) : Prop := ∀ i j : V,
  (∀ S, i∈S → j∉S → rename (swap i j) f S≤f S) ∨
  (∀ S, j∈S → i∉S → rename (swap j i) f S≤f S)

omit [Fintype V] in
theorem weighted_complete (w : V→ℝ) (q : ℝ) : Complete (weighted w q) := by
  intro i j
  rcases le_total (w j) (w i) with h|h
  · exact Or.inl (weighted_swap q h)
  · exact Or.inr (weighted_swap q h)

theorem dist_swap {f : Rule V} (comp : Complete f) (i j : V) :
    distance f (rename (swap i j) f) = |swings f i-swings f j| := by
  rcases comp i j with h|h
  · have eq := dist_swap_ordered f h
    have nonneg : 0≤distance f (rename (swap i j) f) := sum_nonneg fun _ _ ↦ abs_nonneg _
    rw [←eq,abs_of_nonneg nonneg]
  · rw [swap_comm,abs_sub_comm]
    have eq := dist_swap_ordered f h
    have nonneg : 0≤distance f (rename (swap j i) f) := sum_nonneg fun _ _ ↦ abs_nonneg _
    rw [←eq,abs_of_nonneg nonneg]

end KurzWeighted
