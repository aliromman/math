module

public import conjectures.ChauveHistoryGrowth.Dyadic

public section
noncomputable section
namespace ChauveHistoryGrowth
open Filter Topology

private theorem bracket (m H n : ℕ) (hm : 0<m) (hn : 2^H*m≤n) :
    ∃ h j : ℕ, H≤h ∧ m≤j ∧ j≤2*m ∧ j*2^h≤n ∧ n<(j+1)*2^h := by
  let d:=n/m
  let h:=Nat.log 2 d
  let j:=n/2^h
  have hd : 2^H≤d := (Nat.le_div_iff_mul_le hm).mpr hn
  have dp : d≠0 := ((pow_pos (by decide : 0<(2:ℕ)) H).trans_le hd).ne'
  have hH : H≤h := (Nat.le_log_iff_pow_le (by decide) dp).mpr hd
  have hp : 0<(2:ℕ)^h := by positivity
  have mx := (Nat.le_div_iff_mul_le hm).mp (Nat.pow_log_le_self 2 dp)
  have dx : d<2^h*2 := by simpa [h,pow_succ] using Nat.lt_pow_succ_log_self (b:=2) (by decide) d
  have nn : n<(d+1)*m := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self d)
  have jlo : m≤j := (Nat.le_div_iff_mul_le hp).mpr (by simpa [h,mul_comm] using mx)
  have nup : n<(2*m)*2^h := by
    calc n < (d+1)*m := nn
         _ ≤ (2^h*2)*m := Nat.mul_le_mul_right m dx
         _ = _ := by ring
  exact ⟨h,j,hH,jlo,((Nat.div_lt_iff_lt_mul hp).mpr nup).le,
    Nat.div_mul_le_self n _,(Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self j)⟩

private theorem bracket_event {m : ℕ} (hm : 0<m) {p : ℕ → ℕ → Prop}
    (cases : ∀ j, m≤j → j≤2*m → ∀ᶠ h in atTop, p j h) :
    ∀ᶠ n in atTop, ∃ h j : ℕ, m≤j ∧ j*2^h≤n ∧ n<(j+1)*2^h ∧ p j h := by
  have uniform := (eventually_all_finset (Finset.Icc m (2*m))).mpr
    (fun j hj => cases j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
  obtain ⟨H,tail⟩:=eventually_atTop.mp uniform
  refine eventually_atTop.mpr ⟨2^H*m,fun n hn => ?_⟩
  obtain ⟨h,j,hH,lo,hi,a,b⟩:=bracket m H n hm hn
  exact ⟨h,j,lo,a,b,tail h hH j (Finset.mem_Icc.mpr ⟨lo,hi⟩)⟩

private theorem factor_nonneg (n : ℕ) : 0≤balancedFactor n :=
  (Nat.cast_nonneg _).trans (size_le_growth _)

/-- The exponential factor on balanced trees is asymptotic to a fixed
positive multiple of the leaf count. -/
theorem balanced_slope : 0<slope ∧
    Tendsto (fun n : ℕ => balancedFactor n / n) atTop (𝓝 slope) := by
  refine ⟨slope_positive,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro L hl
    by_cases neg : L<0
    · exact Eventually.of_forall fun n => neg.trans_le (div_nonneg (factor_nonneg n) (Nat.cast_nonneg _))
    have lpos:=le_of_not_gt neg
    obtain ⟨M,Mlo⟩:=exists_nat_gt (L/(slope-L))
    let m:=M+1
    have mp : 0<m := by omega
    have gap : L<(m:ℝ)*(slope-L) := by
      have := (div_lt_iff₀ (sub_pos.mpr hl)).mp Mlo
      dsimp [m]; push_cast; linarith
    have ev := bracket_event (p:=fun j h => L*(j+1)<balancedFactor (j*2^h)/(2:ℝ)^h)
      mp (fun j jm _ => (grid_limit j (mp.trans_le jm)).eventually (lt_mem_nhds (by
        have k := mul_le_mul_of_nonneg_right (show (m:ℝ)≤j by exact_mod_cast jm) (sub_nonneg.mpr hl.le)
        linarith)))
    filter_upwards [ev,eventually_gt_atTop 0] with n hn npos
    obtain ⟨h,j,_,left,right,low⟩:=hn
    apply (lt_div_iff₀ (by exact_mod_cast npos : (0:ℝ)<n)).mpr
    have left' := factor_mono left
    have right' : (n:ℝ)≤(j+1)*(2:ℝ)^h := by exact_mod_cast right.le
    have q := (lt_div_iff₀ (by positivity)).mp low
    calc
      L*n ≤ L*((j+1)*(2:ℝ)^h) := mul_le_mul_of_nonneg_left right' lpos
      _ < balancedFactor (j*2^h) := by simpa [mul_assoc] using q
      _ ≤ _ := left'
  · intro U hu
    have up : 0<U := slope_positive.trans hu
    obtain ⟨M,Mlo⟩:=exists_nat_gt (slope/(U-slope))
    let m:=M+1
    have mp : 0<m := by omega
    have gap : slope<(m:ℝ)*(U-slope) := by
      have := (div_lt_iff₀ (sub_pos.mpr hu)).mp Mlo
      dsimp [m]; push_cast; linarith
    have ev := bracket_event (p:=fun j h => balancedFactor ((j+1)*2^h)/(2:ℝ)^h<U*j)
      mp (fun j jm _ => (grid_limit (j+1) (by omega)).eventually (gt_mem_nhds (by
        have k := mul_le_mul_of_nonneg_right (show (m:ℝ)≤j by exact_mod_cast jm) (sub_nonneg.mpr hu.le)
        push_cast; linarith)))
    filter_upwards [ev,eventually_gt_atTop 0] with n hn npos
    obtain ⟨h,j,_,left,right,high⟩:=hn
    apply (div_lt_iff₀ (by exact_mod_cast npos : (0:ℝ)<n)).mpr
    have left' : (j:ℝ)*(2:ℝ)^h≤(n:ℝ) := by exact_mod_cast left
    have q := (div_lt_iff₀ (by positivity)).mp high
    calc
      balancedFactor n ≤ balancedFactor ((j+1)*2^h) := factor_mono right.le
      _ < U*((j:ℝ)*(2:ℝ)^h) := by simpa [mul_assoc] using q
      _ ≤ _ := mul_le_mul_of_nonneg_left left' up.le

/-- info: 'ChauveHistoryGrowth.balanced_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms balanced_slope

end ChauveHistoryGrowth
end
