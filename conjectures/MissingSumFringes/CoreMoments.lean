module

public import conjectures.MissingSumFringes.Margin
public import conjectures.MissingSumFringes.Normalized
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
namespace MissingSumFringes
open Finset

noncomputable def coreD (p : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m∈range (k+1),∑' z : ℕ × ℕ,p m z.1*p (k-m) z.2

noncomputable def coreH (p : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m∈range (k+1),∑' z : ℕ × ℕ,(z.1:ℝ)*(p m z.1*p (k-m) z.2)

theorem coreD_nonneg {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t) (k : ℕ) : 0≤coreD p k :=
  sum_nonneg fun _ _ => tsum_nonneg fun _ => mul_nonneg (hn ..) (hn ..)

theorem coreH_nonneg {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t) (k : ℕ) : 0≤coreH p k :=
  sum_nonneg fun _ _ => tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hn ..) (hn ..))

private theorem tilt_add (m n : ℕ) : tilt (m+n)=tilt m*tilt n := by
  unfold tilt
  rw [Nat.cast_add,add_div,Real.rpow_add (by norm_num)]

private noncomputable def extMass (p : ℕ → ℕ → ℝ) (m t : ℕ) := ((t:ℝ)+1)*p m t

private theorem extMass_nonneg {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t) (m t : ℕ) :
    0≤extMass p m t := mul_nonneg (by positivity) (hn ..)

private theorem fringe_moment {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t)
    (dom : ∀ m t,p m t≤normWindow m t) (empty : ∀ m t,t<m → p m t=0) :
    (∀ m,Summable (extMass p m)) ∧
    Summable (fun m : ℕ => tilt m*((m:ℝ)+1)*(∑' t,extMass p m t)) := by
  obtain ⟨C,hC,norm⟩ := normWindow_bound
  let r := (2:ℝ)^(-1/512:ℝ)
  let f := fun t : ℕ => ((t:ℝ)+1)*r^t
  let B := fun m : ℕ => C*(2:ℝ)^(-(m:ℝ)/2)*r^m
  have hr : 0<r := Real.rpow_pos_of_pos (by norm_num) _
  have r1 : r<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have sf : Summable f := by
    have geo := summable_geometric_of_lt_one hr.le r1
    have lin := summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_eq_abs,abs_of_pos hr] : ‖r‖<1)
    exact (lin.add geo).congr fun t => by dsimp [f]; ring
  have bn (m : ℕ) : 0≤B m := by dsimp [B]; positivity
  have split (m t : ℕ) : p m t≤B m*r^t := by
    by_cases mt : m≤t
    · have factor : (2:ℝ)^(-(m:ℝ)/2-(t:ℝ)/256) =
          (2:ℝ)^(-(m:ℝ)/2)*r^t*r^t := by
        unfold r
        rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2),
          ←Real.rpow_add (by norm_num),←Real.rpow_add (by norm_num)]
        congr 1
        ring
      have raw := (dom m t).trans (norm m t)
      rw [factor] at raw
      apply raw.trans
      dsimp [B]
      have shrink := pow_le_pow_of_le_one hr.le r1.le mt
      calc
        _ = C*((2:ℝ)^(-(m:ℝ)/2))*r^t*r^t := by ring
        _ ≤ _ := by gcongr
    · rw [empty m t (by omega)]
      exact mul_nonneg (bn _) (pow_nonneg hr.le _)
  have envelope (m t : ℕ) : extMass p m t≤B m*f t := by
    calc
      _ ≤ ((t:ℝ)+1)*(B m*r^t) := mul_le_mul_of_nonneg_left (split ..) (by positivity)
      _ = _ := by dsimp [f]; ring
  have se (m : ℕ) : Summable (extMass p m) :=
    (sf.mul_left (B m)).of_nonneg_of_le (extMass_nonneg hn m) (envelope m)
  refine ⟨se,?_⟩
  let T := ∑' t,f t
  have trunc (m : ℕ) : (∑' t,extMass p m t)≤B m*T :=
    ((se m).tsum_le_tsum (envelope m) (sf.mul_left _)).trans_eq (tsum_mul_left ..)
  have cancel (m : ℕ) : tilt m*(2:ℝ)^(-(m:ℝ)/2)=1 := by
    rw [tilt,←Real.rpow_add (by norm_num),show (m:ℝ)/2+ -(m:ℝ)/2=0 by ring,Real.rpow_zero]
  apply (sf.mul_left (C*T)).of_nonneg_of_le
  · intro m
    exact mul_nonneg (mul_nonneg (tilt_pos _).le (by positivity)) (tsum_nonneg (extMass_nonneg hn m))
  · intro m
    calc
      _ ≤ tilt m*((m:ℝ)+1)*(B m*T) := mul_le_mul_of_nonneg_left (trunc m) (mul_nonneg (tilt_pos _).le (by positivity))
      _ = (C*T)*f m := by
        dsimp [f,B]
        linear_combination (C*T*((m:ℝ)+1)*r^m)*(cancel m)

private theorem pair_bound {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t)
    (se : ∀ m,Summable (extMass p m)) (m n : ℕ) (g : ℕ × ℕ → ℝ)
    (ng : ∀ z,0≤g z) (eg : ∀ z,g z≤extMass p m z.1*extMass p n z.2) :
    Summable g ∧ (∑' z,g z)≤(∑' x,extMass p m x)*(∑' y,extMass p n y) := by
  have pair := Summable.mul_of_nonneg (se m) (se n) (extMass_nonneg hn m) (extMass_nonneg hn n)
  have sg := pair.of_nonneg_of_le ng eg
  exact ⟨sg,(sg.tsum_le_tsum eg pair).trans_eq ((se m).tsum_mul_tsum (se n) pair).symm⟩

/-- The geometric bound for the last gap gives both required tilted moments of the
two independent fringes. -/
theorem core_summable {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t)
    (dom : ∀ m t,p m t≤normWindow m t) (empty : ∀ m t,t<m → p m t=0) :
    (Summable fun k : ℕ => tilt k*((k:ℝ)+1)*coreD p k) ∧
      Summable fun k : ℕ => tilt k*coreH p k := by
  obtain ⟨se,su⟩ := fringe_moment hn dom empty
  let L := fun m : ℕ => ∑' t,extMass p m t
  let U := fun m : ℕ => tilt m*((m:ℝ)+1)*L m
  have nl (m : ℕ) : 0≤L m := tsum_nonneg (extMass_nonneg hn m)
  have nu (m : ℕ) : 0≤U m := mul_nonneg (mul_nonneg (tilt_pos _).le (by positivity)) (nl _)
  have ss := summable_sum_mul_range_of_summable_mul (f:=U) (g:=U)
    (Summable.mul_of_nonneg su su nu nu)
  have one (a t : ℕ) : p a t≤extMass p a t :=
    le_mul_of_one_le_left (hn ..) (by linarith [(Nat.cast_nonneg t : (0:ℝ)≤t)])
  have more (m n : ℕ) (z : ℕ × ℕ) : (z.1:ℝ)*(p m z.1*p n z.2)≤extMass p m z.1*extMass p n z.2 := by
    rw [←mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith : (z.1:ℝ)≤(z.1:ℝ)+1) (hn ..))
      (one ..) (hn ..) (extMass_nonneg hn ..)
  have bounds (m n : ℕ) :
      (∑' z : ℕ × ℕ,p m z.1*p n z.2)≤L m*L n ∧
      (∑' z : ℕ × ℕ,(z.1:ℝ)*(p m z.1*p n z.2))≤L m*L n := by
    exact ⟨(pair_bound hn se m n _ (fun _ => mul_nonneg (hn ..) (hn ..))
      (fun _ => mul_le_mul (one ..) (one ..) (hn ..) (extMass_nonneg hn ..))).2,
      (pair_bound hn se m n _ (fun _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hn ..) (hn ..))) (more m n)).2⟩
  have mulUp {k m : ℕ} (hm : m∈range (k+1)) :
      tilt k*((k:ℝ)+1)*(L m*L (k-m))≤U m*U (k-m) := by
    have mk : m≤k := by simpa [Nat.lt_succ_iff] using hm
    have wt : tilt k=tilt m*tilt (k-m) := by rw [←tilt_add]; congr 1; omega
    have bound : (k:ℝ)+1≤((m:ℝ)+1)*(((k-m:ℕ):ℝ)+1) := by
      have pos := mul_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m) (Nat.cast_nonneg (k-m) : (0:ℝ)≤(k-m:ℕ))
      push_cast [Nat.cast_sub mk] at pos ⊢
      nlinarith only [pos]
    dsimp [U]
    rw [wt]
    calc
      _ ≤ (tilt m*tilt (k-m))*(((m:ℝ)+1)*(((k-m:ℕ):ℝ)+1))*(L m*L (k-m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (mul_nonneg (tilt_pos _).le (tilt_pos _).le))
          (mul_nonneg (nl _) (nl _))
      _ = _ := by ring
  constructor
  · apply ss.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (tilt_pos _).le (by positivity)) (coreD_nonneg hn _))
    intro k
    unfold coreD
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    exact (mul_le_mul_of_nonneg_left (bounds m (k-m)).1 (mul_nonneg (tilt_pos _).le (by positivity))).trans (mulUp hm)
  · apply ss.of_nonneg_of_le (fun k => mul_nonneg (tilt_pos _).le (coreH_nonneg hn _))
    intro k
    unfold coreH
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    apply (mul_le_mul_of_nonneg_left (bounds m (k-m)).2 (tilt_pos _).le).trans
    apply le_trans _ (mulUp hm)
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (nl _) (nl _))
    exact le_mul_of_one_le_right (tilt_pos _).le (by linarith [(Nat.cast_nonneg k : (0:ℝ)≤k)])

/-- A single pair of attainable fringe types has positive mass in its convolution. -/
theorem coreD_pos_of {p : ℕ → ℕ → ℝ} (hn : ∀ m t,0≤p m t)
    (dom : ∀ m t,p m t≤normWindow m t) (empty : ∀ m t,t<m → p m t=0)
    {k m t s : ℕ} (mk : m≤k) (left : 0<p m t) (right : 0<p (k-m) s) :
    0<coreD p k := by
  obtain ⟨se,_⟩ := fringe_moment hn dom empty
  have sp (j : ℕ) : Summable (p j) := (se j).of_nonneg_of_le (hn _) (fun i =>
    le_mul_of_one_le_left (hn j i) (le_add_of_nonneg_left (Nat.cast_nonneg i)))
  have pair := Summable.mul_of_nonneg (sp m) (sp (k-m)) (hn _) (hn _)
  have entry := pair.le_tsum (t,s) (fun z _ => mul_nonneg (hn ..) (hn ..))
  have row := single_le_sum (s:=range (k+1)) (f:=fun i => ∑' z : ℕ×ℕ,p i z.1*p (k-i) z.2)
    (fun i _ => tsum_nonneg (fun z => mul_nonneg (hn ..) (hn ..)))
    (mem_range.mpr (Nat.lt_succ_of_le mk))
  exact (mul_pos left right).trans_le (entry.trans row)

end MissingSumFringes
