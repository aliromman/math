module

public import conjectures.ChauveHistoryGrowth.Growth
public import conjectures.ChauveHistoryGrowth.Extrema
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth

open PowerSeries

def graft : Tree → Tree → Tree
  | .tip, u => u
  | .fork a b, u => .fork (graft a u) (graft b u)

def seedInput (t : Tree) := input t-1

theorem seedInput_zero (t : Tree) : constantCoeff (seedInput t)=0 := by simp [seedInput,input_eq,hz]
theorem seedInput_pos (t : Tree) : 0 ≼ seedInput t := by
  cases t with
  | tip => simpa [seedInput,input] using Xpos
  | fork a b =>
    have eq : seedInput (.fork a b)=H a+H b+H a*H b := by dsimp [seedInput,input,P]; ring
    exact eq ▸ addP (addP (hp _) (hp _)) (mulP (hp _) (hp _))

theorem unique_quad {f x y : S} (xz : constantCoeff x=0) (yz : constantCoeff y=0)
    (fx : x=f+x*x) (fy : y=f+y*y) : x=y := by
  have e : (x-y)*(1-x-y)=0 := by linear_combination fx-fy
  have nz : 1-x-y≠0 := by
    intro bad
    have := congrArg constantCoeff bad
    simp [xz,yz] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right nz)

theorem graft_subst (t u : Tree) : H (graft t u)=PowerSeries.subst (seedInput u) (H t) := by
  let V:=seedInput u
  have vz : constantCoeff V=0 := seedInput_zero _
  have valid := HasSubst.of_constantCoeff_zero' vz
  have zero (s : Tree) : constantCoeff (PowerSeries.subst V (H s))=0 :=
    constantCoeff_subst_eq_zero vz (H s) (hz s)
  induction t with
  | tip =>
    apply unique_quad (hz _) (zero .tip) (f:=V)
    · change H u=seedInput u+H u*H u
      rw [seedInput,input_eq]; ring
    · nth_rw 1 [leaf_grammar]
      rw [subst_add valid,subst_mul valid,subst_X valid]
  | fork a b ha hb =>
    apply unique_quad (hz _) (zero _) (f:=H (graft a u)*H (graft b u)+(H (graft a u)+H (graft b u)))
    · simp only [graft]
      linear_combination fork_grammar (graft a u) (graft b u)
    · conv_lhs => rw [fork_grammar]
      rw [subst_add valid,subst_mul valid,subst_add valid,subst_mul valid,subst_add valid,ha,hb]
      ring

theorem pow_below {a b : S} (pa : 0 ≼ a) (h : a ≼ b) (n : ℕ) : 0 ≼ a^n ∧ a^n ≼ b^n := by
  induction n with
  | zero => simp only [pow_zero]; exact ⟨onePos,refl _⟩
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact ⟨mulP ih.1 pa,mulM ih.2 h ih.1 (trans pa h)⟩

theorem subst_mono {a b f g : S} (az : constantCoeff a=0) (bz : constantCoeff b=0)
    (ap : 0 ≼ a) (ab : a ≼ b) (fp : 0 ≼ f) (fg : f ≼ g) :
    PowerSeries.subst a f ≼ PowerSeries.subst b g := by
  intro n
  have aa := HasSubst.of_constantCoeff_zero' az
  have bb := HasSubst.of_constantCoeff_zero' bz
  rw [coeff_subst' aa,coeff_subst' bb]
  apply finsum_le_finsum (coeff_subst_finite' aa _ _) (coeff_subst_finite' bb _ _)
  intro i
  have pow := pow_below ap ab i
  exact mul_le_mul (fg _) (pow.2 _) ((zeroBelow _).mp pow.1 _) ((zeroBelow _).mp (trans fp fg) _)

def geometric (r : ℝ) : S := PowerSeries.mk fun n => r^n

theorem geometric_eq (r : ℝ) : geometric r=1+(r • X)*geometric r := by
  ext n
  cases n with
  | zero => simp [geometric,coeff_zero_eq_constantCoeff_apply,PowerSeries.smul_eq_C_mul]
  | succ n =>
    rw [smul_mul_assoc,map_add,map_smul,coeff_succ_X_mul]
    simp [geometric,coeff_one,pow_succ,mul_comm]

theorem seed_lower (u : Tree) : (u.leaves : ℝ) • X ≼ seedInput u := by
  intro n
  by_cases one : n=1
  · subst n
    simp [seedInput,input_eq,hz,coeff_one_mul,hc,leaf_one,coeff_one]
  · simpa [coeff_X,one] using (zeroBelow _).mp (seedInput_pos u) n

def affineInput (m C : ℝ) : S := (m • X)*geometric C

theorem affine_zero (m C : ℝ) : constantCoeff (affineInput m C)=0 := by
  simp [affineInput,PowerSeries.smul_eq_C_mul]

theorem affine_coeff (m C : ℝ) (n : ℕ) : coeff (n+1) (affineInput m C)=m*C^n := by
  simp [affineInput,coeff_succ_X_mul,geometric]

theorem seed_upper (u : Tree) : ∃ C : ℝ, 0≤C ∧
    seedInput u ≼ affineInput u.leaves C := by
  obtain ⟨B,B1,bd⟩ := general_upper u
  refine ⟨B^2,sq_nonneg _,?_⟩
  have raw : seedInput u ≼ H u := by
    rw [seedInput,input_eq]
    apply subP.mp
    convert mulP (hp u) (hp u) using 1; ring
  intro n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,seedInput_zero,affine_zero]
  | succ n =>
    rw [affine_coeff]
    cases n with
    | zero => simp [seedInput,input_eq,coeff_one_mul,hz,hc,leaf_one,coeff_one]
    | succ n =>
      have s := (raw (n+2)).trans ((hc u (n+2)).le.trans (bd _))
      have e : n+2≤2*(n+1) := by omega
      have le := pow_le_pow_right₀ B1 e
      rw [pow_mul] at le
      exact (s.trans le).trans (le_mul_of_one_le_left (by positivity)
        (by exact_mod_cast u.leaves_pos))

theorem affine_subst_bound {m C r : ℝ} (cm : 0≤m) (cc : 0≤C) (cr : 0≤r) :
    PowerSeries.subst (affineInput m C) (geometric r) ≼ geometric (C+r*m) := by
  let V:=affineInput m C
  let F:=PowerSeries.subst V (geometric r)
  have va := HasSubst.of_constantCoeff_zero' (affine_zero m C)
  have vf : F=1+(r • V)*F := by
    dsimp [F]
    conv_lhs => rw [geometric_eq r]
    rw [subst_add va,subst_mul va,subst_smul va,subst_X va,← coe_substAlgHom va,map_one]
  have vq : V*((1:S)-C • X)=m • X := by
    have g := geometric_eq C
    dsimp [V,affineInput]
    linear_combination (m • X)*g
  have fe : F=1-C • X+((C+r*m) • X)*F := by
    have e := congrArg (fun z : S => z*(1-C • X)) vf
    simp only [add_smul,mul_smul] at *
    simp only [smul_eq_C_mul] at *
    linear_combination e+(PowerSeries.C r)*F*vq
  apply subP.mp
  apply nonneg_fixed (scale_pos cc Xpos)
    (scale_pos (add_nonneg cc (mul_nonneg cr cm)) Xpos)
    (by simp [PowerSeries.smul_eq_C_mul])
  linear_combination geometric_eq (C+r*m) - fe

theorem growth_geom (t : Tree) : H t ≼ geometric (growth t) := by
  intro n
  rw [hc,geometric,coeff_mk]
  by_cases hz : n=0
  · subst n; norm_num [count]
  · have a := pow_le_pow_left₀ (Real.rpow_nonneg (show 0≤(count t n : ℝ) by positivity) _)
      (root_le_growth t (Nat.pos_of_ne_zero hz)) n
    change (nthRoot t n)^n≤_ at a
    rwa [nthRoot,one_div,Real.rpow_inv_natCast_pow (by positivity) hz] at a

theorem growth_graft (u : Tree) : ∃ C : ℝ, 0≤C ∧ ∀ t : Tree,
    u.leaves*growth t≤growth (graft t u) ∧ growth (graft t u)≤C+growth t*u.leaves := by
  obtain ⟨C,cp,upper⟩ := seed_upper u
  refine ⟨C,cp,fun t => ?_⟩
  have m : 0≤(u.leaves : ℝ) := by positivity
  have r : 0≤growth t := (show 0≤(t.leaves : ℝ) by positivity).trans (size_le_growth t)
  have z : constantCoeff ((u.leaves : ℝ) • (X : S))=0 := by simp [smul_eq_C_mul]
  have lower := subst_mono z (seedInput_zero u) (scale_pos m Xpos) (seed_lower u) (hp t) (refl _)
  rw [← rescale_eq_subst,← graft_subst] at lower
  have upper' := subst_mono (seedInput_zero u) (affine_zero _ _) (seedInput_pos u) upper
    (hp t) (growth_geom t)
  rw [← graft_subst] at upper'
  have full := trans upper' (affine_subst_bound m cp r)
  constructor
  · apply le_of_tendsto (tendsto_const_nhds.mul (growth_limit t))
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply le_trans _ (root_le_growth _ hn)
    have h := lower n
    rw [coeff_rescale,hc,hc] at h
    have k := Real.rpow_le_rpow (mul_nonneg (pow_nonneg m _) (Nat.cast_nonneg _)) h
      (show 0≤(n:ℝ)⁻¹ by positivity)
    rw [Real.mul_rpow (pow_nonneg m _) (Nat.cast_nonneg _),Real.pow_rpow_inv_natCast m hn.ne'] at k
    simpa [nthRoot,one_div] using k
  · unfold growth
    refine csSup_le ?_ ?_
    · exact ⟨nthRoot _ 1,1,by decide,rfl⟩
    rintro _ ⟨n,hn,rfl⟩
    exact root_upper (add_nonneg cp (mul_nonneg r m)) (fun k => by
      simpa [geometric,hc] using full k) hn.ne'

end ChauveHistoryGrowth
end
