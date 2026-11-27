module

public import conjectures.ChauveHistoryGrowth.Majorant
public import Mathlib.Analysis.Subadditive

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries Finset Filter Topology
open Set

theorem square_below (t : Tree) : H t*H t ≼ H t := by
  cases t with
  | tip =>
    conv_rhs => rw [leaf_grammar]
    simpa using addM Xpos (refl (H .tip*H .tip))
  | fork a b =>
    conv_rhs => rw [fork_grammar]
    simpa using addM (refl (H (.fork a b)*H (.fork a b)))
      (addP (mulP (hp a) (hp b)) (addP (hp a) (hp b)))

theorem count_super (t : Tree) (i j : ℕ) : count t i*count t j≤count t (i+j) := by
  have m := square_below t (i+j)
  rw [coeff_mul,hc] at m
  have s : coeff i (H t)*coeff j (H t) ≤
      ∑ k ∈ antidiagonal (i+j), coeff k.1 (H t)*coeff k.2 (H t) :=
    single_le_sum (f := fun k : ℕ×ℕ => coeff k.1 (H t)*coeff k.2 (H t))
      (fun k _ => mul_nonneg ((zeroBelow _).mp (hp t) _) ((zeroBelow _).mp (hp t) _))
      (show (i,j)∈antidiagonal (i+j) from mem_antidiagonal.mpr rfl)
  rw [hc,hc] at s
  exact_mod_cast s.trans m

theorem count_pos (t : Tree) {n : ℕ} (h : 0<n) : 0<count t n := by
  induction n,h using Nat.le_induction with
  | base => rw [leaf_one]; exact t.leaves_pos
  | succ n hn ih => exact (Nat.mul_pos ih (leaf_one t ▸ t.leaves_pos)).trans_le (count_super t n 1)

theorem root_upper {t : Tree} {B : ℝ} (hb : 0≤B) (bound : ∀ n, (count t n : ℝ) ≤ B^n)
    {n : ℕ} (hn : n≠0) : nthRoot t n≤B := by
  unfold nthRoot
  rw [one_div,← Real.pow_rpow_inv_natCast hb hn]
  apply Real.rpow_le_rpow (by positivity) (bound n) (by positivity)

theorem general_upper (t : Tree) : ∃ B : ℝ, 1≤B ∧ ∀ n, (count t n : ℝ)≤B^n := by
  obtain ⟨A,Al,b⟩ := exists_budget t (y:=1/2) (by norm_num) le_rfl
  exact ⟨4*A,by linarith,b.upper (by linarith)⟩

theorem root_set_bounded (t : Tree) : BddAbove {x | ∃ n : ℕ, 0<n ∧ x=nthRoot t n} := by
  obtain ⟨B,h,bd⟩ := general_upper t
  exact ⟨B,fun _ ⟨n,hp,eq⟩ => eq ▸ root_upper (by linarith) bd hp.ne'⟩

theorem root_le_growth (t : Tree) {n : ℕ} (h : 0<n) : nthRoot t n≤growth t :=
  le_csSup (root_set_bounded t) ⟨n,h,rfl⟩

theorem growth_limit (t : Tree) : Tendsto (nthRoot t) atTop (𝓝 (growth t)) := by
  let v (n : ℕ) := -Real.log (count t n)
  have pos {n : ℕ} (h : 0<n) : 0<(count t n : ℝ) := by exact_mod_cast count_pos t h
  have sub : Subadditive v := by
    intro i j
    by_cases a : i=0
    · subst i; simp [v,count]
    by_cases b : j=0
    · subst j; simp [v,count]
    have ai := pos (Nat.pos_of_ne_zero a)
    have bj := pos (Nat.pos_of_ne_zero b)
    have h := Real.log_le_log (mul_pos ai bj)
      (show (count t i : ℝ)*count t j≤count t (i+j) by exact_mod_cast count_super t i j)
    rw [Real.log_mul ai.ne' bj.ne'] at h
    dsimp [v]; linarith
  obtain ⟨B,B1,bd⟩ := general_upper t
  have lb : BddBelow (Set.range fun n : ℕ => v n/n) := by
    refine ⟨-Real.log B,?_⟩
    rintro _ ⟨n,rfl⟩
    by_cases z : n=0
    · subst n; simp [Real.log_nonneg B1]
    have np : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero z
    have h := Real.log_le_log (pos (Nat.pos_of_ne_zero z)) (bd n)
    rw [Real.log_pow] at h
    apply (le_div_iff₀ np).mpr
    dsimp [v]; linarith
  let c := Real.exp (-sub.lim)
  have form {n : ℕ} (h : 0<n) : nthRoot t n=Real.exp (-(v n/n)) := by
    rw [nthRoot,Real.rpow_def_of_pos (pos h)]; dsimp [v]; congr 1; ring
  have converge : Tendsto (nthRoot t) atTop (𝓝 c) := by
    apply (Real.continuous_exp.continuousAt.tendsto.comp (sub.tendsto_lim lb).neg).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn using (form hn).symm
  have above : growth t≤c := by
    refine csSup_le ⟨nthRoot t 1,1,by decide,rfl⟩ ?_
    rintro _ ⟨n,hn,rfl⟩
    rw [form hn]
    exact Real.exp_le_exp.mpr (neg_le_neg (sub.lim_le_div lb hn.ne'))
  have below : c≤growth t := by
    exact le_of_tendsto converge ((eventually_gt_atTop 0).mono fun _ h => root_le_growth t h)
  rwa [le_antisymm below above] at converge

theorem size_le_growth (t : Tree) : (t.leaves : ℝ)≤growth t := by
  simpa [nthRoot,leaf_one] using root_le_growth t (n:=1) (by decide)

theorem balanced_growth {t : Tree} (h : t.Balanced) : growth t≤64*t.leaves := by
  have b := balanced_budget t.leaves h le_rfl
  unfold growth
  refine csSup_le ?_ ?_
  · exact ⟨nthRoot t 1,1,by decide,rfl⟩
  rintro _ ⟨n,hn,rfl⟩
  have h' := root_upper (t:=t) (B:=4*(16*(t.leaves:ℝ))) (by positivity)
    (b.upper (by positivity)) hn.ne'
  linarith

end ChauveHistoryGrowth
end
