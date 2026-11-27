module

public import conjectures.ChauveHistoryGrowth.Gains

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth

open PowerSeries

def cat : ℕ → Tree
  | 0 => .tip
  | n+1 => .fork .tip (cat n)

def bal : ℕ → Tree
  | 0 => .tip
  | n+1 => .fork (bal (n/2)) (bal ((n+1)/2))
termination_by n => n
decreasing_by all_goals omega

theorem bal_odd (j : ℕ) : bal (2*j+1)=.fork (bal j) (bal j) := by
  rw [bal]
  congr 2 <;> omega

theorem bal_even (j : ℕ) : bal (2*j+2)=.fork (bal j) (bal (j+1)) := by
  rw [bal]
  congr 2 <;> omega

theorem cat_leaves (n : ℕ) : (cat n).leaves=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cat,Tree.leaves,ih,Nat.add_comm]

theorem bal_leaves (n : ℕ) : (bal n).leaves=n+1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _|n
    · rw [bal]; rfl
    · rw [bal,Tree.leaves,ih (n/2) (by omega),ih ((n+1)/2) (by omega)]
      omega

theorem cat_shape (n : ℕ) : (cat n).Caterpillar := by
  induction n with
  | zero => trivial
  | succ n ih => exact Or.inl ⟨rfl,ih⟩

theorem bal_shape (n : ℕ) : (bal n).Balanced := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _|n
    · rw [bal]; trivial
    · rw [bal,Tree.Balanced]
      exact ⟨ih _ (by omega),ih _ (by omega),by rw [bal_leaves,bal_leaves]; omega,
        by rw [bal_leaves,bal_leaves]; omega⟩

def step (f : ℕ → Tree) (n : ℕ) := gain (f n) (f (n+1))

theorem cat_step (n : ℕ) : step cat (n+1) =
    step cat n*multiplier (H (cat (n+1))) (H (cat (n+2))) := by
  apply gain_step
  change P .tip*P (cat (n+1))=(P .tip*P (cat n))*(1+step cat n)
  rw [gain_factor (cat n) (cat (n+1))]
  dsimp [step]; ring

theorem bal_step_odd (j : ℕ) : step bal (2*j+1)=
    step bal j*multiplier (H (bal (2*j+1))) (H (bal (2*j+2))) := by
  apply gain_step
  change input (bal (2*j+2))=input (bal (2*j+1))*(1+step bal j)
  rw [bal_even,bal_odd]
  change P (bal j)*P (bal (j+1))=(P (bal j)*P (bal j))*(1+step bal j)
  rw [gain_factor (bal j) (bal (j+1))]; dsimp [step]; ring

theorem bal_step_even (j : ℕ) : step bal (2*j+2)=
    step bal j*multiplier (H (bal (2*j+2))) (H (bal (2*j+3))) := by
  apply gain_step
  change input (bal (2*j+3))=input (bal (2*j+2))*(1+step bal j)
  rw [show 2*j+3=2*(j+1)+1 by omega,bal_odd,bal_even]
  change P (bal (j+1))*P (bal (j+1))=(P (bal j)*P (bal (j+1)))*(1+step bal j)
  rw [gain_factor (bal j) (bal (j+1))]; dsimp [step]; ring

theorem cat_pos (n : ℕ) : 0 ≼ step cat n := by
  induction n with
  | zero => exact base_gain
  | succ n ih => rw [cat_step]; exact mulP ih (factor_mul_pos _ _)

theorem bal_pos (n : ℕ) : 0 ≼ step bal n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _|n
    · change 0 ≼ gain (bal 0) (bal 1)
      rw [show 1=2*0+1 by decide,bal_odd,bal]
      exact base_gain
    · by_cases he : n%2=0
      · rw [show n+1=2*(n/2)+1 by omega,bal_step_odd]
        exact mulP (ih _ (by omega)) (factor_mul_pos _ _)
      · rw [show n+1=2*(n/2)+2 by omega,bal_step_even]
        exact mulP (ih _ (by omega)) (factor_mul_pos _ _)

theorem step_mul_le {a : S} (h : 0 ≼ a) (t u : Tree) : a ≼ a*multiplier (H t) (H u) := by
  simpa using mulM (refl a) (factor_mul_one t u) h (factor_mul_pos t u)

theorem cat_increasing (n : ℕ) : step cat n ≼ step cat (n+1) := by
  rw [cat_step]; exact step_mul_le (cat_pos _) _ _

theorem bal_increasing (n : ℕ) : step bal n ≼ step bal (n+1) := by
  have mono (i : ℕ) : H (bal i) ≼ H (bal (i+1)) := gain_out (bal_pos i)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _|n
    · rw [show 0+1=2*0+1 by decide,bal_step_odd]
      exact step_mul_le (bal_pos _) _ _
    · by_cases he : n%2=0
      · let j := n/2
        rw [show n+1=2*j+1 by dsimp [j]; omega,bal_step_odd,bal_step_even]
        exact mulM (refl _) (multiplier_mono (hp _) (hp _) (mono _) (mono _)
          (hz _) (hz _) (hz _) (hz _)) (bal_pos _) (factor_mul_pos _ _)
      · let j := n/2
        rw [show n+1=2*j+2 by dsimp [j]; omega,bal_step_even,
          show 2*j+2+1=2*(j+1)+1 by omega,bal_step_odd]
        apply mulM (ih j (by dsimp [j]; omega)) _ (bal_pos _) (factor_mul_pos _ _)
        apply multiplier_mono (hp _) (hp _)
        · convert mono (2*j+2) using 2
        · convert mono (2*j+3) using 2
        all_goals apply hz

theorem cat_strict (n : ℕ) : coeff 2 (step cat n) < coeff 2 (step cat (n+1)) := by
  have h := gain_second_step (cat_step n) (by rw [cat_leaves,cat_leaves])
  change coeff 2 (step cat (n+1)) = _ at h
  rw [h,cat_leaves,cat_leaves]
  push_cast
  dsimp [step]
  linarith

theorem bal_strict (n : ℕ) : coeff 2 (step bal n) < coeff 2 (step bal (n+1)) := by
  have odd (j : ℕ) : coeff 2 (step bal (2*j+1)) = coeff 2 (step bal j)+
      ((bal (2*j+1)).leaves : ℝ)+(bal (2*j+2)).leaves := gain_second_step (bal_step_odd j) (by rw [bal_leaves,bal_leaves])
  have even (j : ℕ) : coeff 2 (step bal (2*j+2)) = coeff 2 (step bal j)+
      ((bal (2*j+2)).leaves : ℝ)+(bal (2*j+3)).leaves := gain_second_step (bal_step_even j) (by rw [bal_leaves,bal_leaves])
  simp only [bal_leaves,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at odd even
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _|n
    · convert (show coeff 2 (step bal 0)<coeff 2 (step bal (2*0+1)) by rw [odd]; norm_num; linarith)
    · by_cases he : n%2=0
      · let j := n/2
        rw [show n+1=2*j+1 by dsimp [j]; omega,odd,even]
        linarith
      · let j := n/2
        rw [show n+1=2*j+2 by dsimp [j]; omega,even,
          show 2*j+2+1=2*(j+1)+1 by omega,odd]
        have h := ih j (by dsimp [j]; omega)
        push_cast
        linarith

end ChauveHistoryGrowth
end
