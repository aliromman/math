module

public import conjectures.ChauveHistoryGrowth.Graft
public import Mathlib.Data.Nat.Log

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries Filter Topology

def balancedFactor (k : ℕ) := growth (bal (k-1))

theorem growth_mono {t u : Tree} (h : H t ≼ H u) : growth t≤growth u := by
  apply le_of_tendsto_of_tendsto' (growth_limit _) (growth_limit _)
  intro n
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  simpa [hc] using h n

theorem factor_of_balanced {t : Tree} (h : t.Balanced) : growth t=balancedFactor t.leaves := by
  have e := same_bal h
  exact le_antisymm (growth_mono (e ▸ refl _)) (growth_mono (e ▸ refl _))

theorem factor_mono : Monotone balancedFactor := by
  intro i j ij
  apply growth_mono
  intro n
  apply (monotone_nat_of_le_succ (fun k => (gain_out (bal_pos k)) n)) (Nat.sub_le_sub_right ij 1)

def complete : ℕ → Tree
  | 0 => .tip
  | h+1 => .fork (complete h) (complete h)

theorem graft_complete (u : Tree) (bu : u.Balanced) (h : ℕ) :
    (graft (complete h) u).Balanced ∧ (graft (complete h) u).leaves=u.leaves*2^h := by
  induction h with
  | zero => simpa [complete,graft] using bu
  | succ h ih =>
    change ((graft (complete h) u).fork (graft (complete h) u)).Balanced ∧ _
    refine ⟨⟨ih.1,ih.1,by omega,by omega⟩,?_⟩
    simp [complete,graft,Tree.leaves,ih.2,pow_succ]
    ring

theorem complete_shape (h : ℕ) : (complete h).Balanced ∧ (complete h).leaves=2^h := by
  induction h with
  | zero => exact ⟨trivial,rfl⟩
  | succ h ih =>
    refine ⟨⟨ih.1,ih.1,by omega,by omega⟩,?_⟩
    simp [complete,Tree.leaves,ih.2,pow_succ]
    omega

theorem factor_dilate (m : ℕ) (hm : 0<m) : ∃ C : ℝ, 0≤C ∧ ∀ h : ℕ,
    (m:ℝ)*balancedFactor (2^h)≤balancedFactor (m*2^h) ∧
    balancedFactor (m*2^h)≤C+balancedFactor (2^h)*m := by
  let u:=bal (m-1)
  have size : u.leaves=m := (bal_leaves _).trans (by omega)
  have shp : u.Balanced:=bal_shape _
  obtain ⟨C,cp,args⟩:=growth_graft u
  refine ⟨C,cp,fun h => ?_⟩
  have co:=complete_shape h
  have gr:=graft_complete u shp h
  have a:=args (complete h)
  rwa [factor_of_balanced co.1,co.2,factor_of_balanced gr.1,gr.2,size] at a

def ratio (h : ℕ) := balancedFactor (2^h)/(2:ℝ)^h

theorem ratio_mono : Monotone ratio := by
  obtain ⟨_,_,d⟩:=factor_dilate 2 (by decide)
  apply monotone_nat_of_le_succ
  intro h
  have k := (d h).1
  rw [show 2*(2:ℕ)^h=2^(h+1) by ring] at k
  dsimp [ratio]
  rw [div_le_div_iff₀ (by positivity) (by positivity),pow_succ]
  push_cast at k
  nlinarith [mul_le_mul_of_nonneg_right k (show 0≤(2:ℝ)^h by positivity)]

theorem ratio_bounds (h : ℕ) : 1≤ratio h ∧ ratio h≤64 := by
  let t:=complete h
  have s:=(complete_shape h).2
  have b:=(complete_shape h).1
  have lo:=size_le_growth (complete h)
  have hi:=balanced_growth b
  rw [factor_of_balanced b,s,Nat.cast_pow,Nat.cast_ofNat] at lo hi
  exact ⟨(le_div_iff₀ (by positivity)).mpr (by simpa using lo),
    (div_le_iff₀ (by positivity)).mpr hi⟩

def slope : ℝ := ⨆ h,ratio h

theorem ratio_limit : Tendsto ratio atTop (𝓝 slope) :=
  tendsto_atTop_ciSup ratio_mono ⟨64,fun _ ⟨h,eq⟩ => eq ▸ (ratio_bounds h).2⟩

theorem slope_positive : 0<slope := by
  have h : 1≤slope := le_of_tendsto_of_tendsto' tendsto_const_nhds ratio_limit
    fun i => (ratio_bounds i).1
  linarith

theorem grid_limit (m : ℕ) (hm : 0<m) :
    Tendsto (fun h : ℕ => balancedFactor (m*2^h)/(2:ℝ)^h) atTop (𝓝 (m*slope)) := by
  obtain ⟨C,_,d⟩:=factor_dilate m hm
  have lo := tendsto_const_nhds.mul ratio_limit (a:=(m:ℝ))
  have van : Tendsto (fun h : ℕ => C/(2:ℝ)^h) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hi := van.add lo
  rw [zero_add] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo hi
  · intro h
    have key := div_le_div_of_nonneg_right (d h).1 (show 0≤(2:ℝ)^h by positivity)
    simpa [ratio,mul_div_assoc] using key
  · intro h
    have key := div_le_div_of_nonneg_right (d h).2 (show 0≤(2:ℝ)^h by positivity)
    simpa [ratio,add_div,mul_div_assoc,mul_comm (balancedFactor _) (m:ℝ)] using key

end ChauveHistoryGrowth
end
