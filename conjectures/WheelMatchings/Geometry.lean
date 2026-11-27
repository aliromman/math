module

public import conjectures.WheelMatchings.Coordinates

@[expose] public section

namespace WheelMatchings

def convexSigns (n : ℕ) : Turn n := fun _ _ _ ↦ true

def wheelSigns (m : ℕ) : Turn (2*m) := fun a b c ↦
  decide (a.val ≠ 0 ∨ 2 * (c.val - b.val) < 2*m-1)

def parabola {n : ℕ} (i : Fin n) : Point := ((i.val : ℝ), (i.val : ℝ)^2)

private theorem parabola_signs {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    0 < orient (parabola i) (parabola j) (parabola k) := by
  have h₁ : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have h₂ : (j.val : ℝ) < k.val := by exact_mod_cast hjk
  have he : orient (parabola i) (parabola j) (parabola k) =
      (j.val-i.val : ℝ)*(k.val-i.val)*(k.val-j.val) := by unfold orient parabola; ring
  rw [he]
  exact mul_pos (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr (lt_trans h₁ h₂))) (sub_pos.mpr h₂)

theorem parabola_general (n : ℕ) : General (@parabola n) := by
  refine ⟨fun i j h ↦ Fin.ext ?_, fun i j k hij hjk ↦ (parabola_signs i j k hij hjk).ne'⟩
  have he : (i.val : ℝ) = j.val := congrArg Prod.fst h
  exact_mod_cast he

theorem parabola_count (m k : ℕ) : count (m := m) parabola k = countCode (m := m) (extend (convexSigns _)) k :=
  count_by_signs parabola (convexSigns _) (fun i j l hij hjl ↦ parabola_signs i j l hij hjl) k

private noncomputable def circle (t : ℝ) : Point := (Real.cos t, Real.sin t)

private theorem circle_area (a b c : ℝ) : orient (circle a) (circle b) (circle c) =
    4 * Real.sin ((b-a)/2) * Real.sin ((c-a)/2) * Real.sin ((c-b)/2) := by
  unfold orient circle
  simp only [Real.cos_sub_cos, Real.sin_sub_sin]
  have he : (c-b)/2 = (c+a)/2 - (b+a)/2 := by ring
  rw [he, Real.sin_sub]
  ring

private theorem circle_sign {a b c : ℝ} (hab : a < b) (hbc : b < c) (hac : c-a < 2*Real.pi) :
    0 < orient (circle a) (circle b) (circle c) := by
  rw [circle_area]
  have hs₁ := Real.sin_pos_of_pos_of_lt_pi (x := (b-a)/2) (by linarith) (by linarith)
  have hs₂ := Real.sin_pos_of_pos_of_lt_pi (x := (c-a)/2) (by linarith) (by linarith)
  have hs₃ := Real.sin_pos_of_pos_of_lt_pi (x := (c-b)/2) (by linarith) (by linarith)
  positivity

private theorem spoke_area (b c : ℝ) : orient (0,0) (circle b) (circle c) = Real.sin (c-b) := by
  simp [orient, circle, Real.sin_sub]
  ring

private theorem angle_sign {m : ℕ} (hm : 2 ≤ m) (i j k : Fin (2*m)) (hij : i < j) (hjk : j < k) :
    if wheelSigns m i j k then 0 < orient (wheel m i) (wheel m j) (wheel m k)
    else orient (wheel m i) (wheel m j) (wheel m k) < 0 := by
  let N : ℝ := 2*(m : ℝ)-1
  let t (a : Fin (2*m)) := 2*Real.pi*a.val/N
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < (2*m : ℤ)-1 by omega)
  have hj : j.val ≠ 0 := by omega
  have hk : k.val ≠ 0 := by omega
  have hw (a : Fin (2*m)) (ha : a.val ≠ 0) : wheel m a = circle (t a) := by simp [wheel, circle, N, t, ha]
  have ht (a b : Fin (2*m)) (hab : a < b) : t a < t b := by
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by exact_mod_cast hab) (by positivity)) hN
  have hdiff (a b : Fin (2*m)) : t b - t a = 2 * Real.pi * (b.val - a.val : ℝ) / N := by dsimp [t]; ring
  rw [hw j hj, hw k hk]
  by_cases hi : i.val = 0
  · simp only [wheel, hi, ↓reduceIte]
    rw [spoke_area, hdiff]
    have hjkr : (j.val : ℝ) < k.val := by exact_mod_cast hjk
    have hkN : (k.val : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (show (k.val : ℤ) ≤ 2*(m : ℤ)-1 by omega)
    have hjr : 0 < (j.val : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hlow : 0 < 2 * Real.pi * (k.val - j.val : ℝ) / N := by positivity
    have hupp : 2 * Real.pi * (k.val - j.val : ℝ) / N < 2*Real.pi := by
      rw [div_lt_iff₀ hN]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
    by_cases h : 2 * (k.val - j.val) < 2*m-1
    · simp only [wheelSigns, hi, ne_eq, not_true_eq_false, false_or, h, decide_true, ↓reduceIte]
      apply Real.sin_pos_of_pos_of_lt_pi hlow
      rw [div_lt_iff₀ hN]
      have hhalf : (2:ℝ)*(k.val-j.val) < N := by
        dsimp [N]; exact_mod_cast (show (2:ℤ)*((k.val:ℤ)-j.val) < 2*(m:ℤ)-1 by omega)
      nlinarith [mul_lt_mul_of_pos_left hhalf Real.pi_pos]
    · simp only [wheelSigns, hi, ne_eq, not_true_eq_false, false_or, h, decide_false]
      have hmore : Real.pi < 2 * Real.pi * (k.val - j.val : ℝ) / N := by
        rw [lt_div_iff₀ hN]
        have hhalf : N < (2:ℝ)*(k.val-j.val) := by
          dsimp [N]; exact_mod_cast (show 2*(m:ℤ)-1 < (2:ℤ)*((k.val:ℤ)-j.val) by omega)
        nlinarith [mul_lt_mul_of_pos_left hhalf Real.pi_pos]
      have hpos := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hmore) (by linarith : _ - Real.pi < Real.pi)
      rwa [Real.sin_sub_pi, neg_pos] at hpos
  · simp only [wheelSigns, hi, ne_eq, not_false_eq_true, true_or, decide_true, ↓reduceIte, hw i hi]
    apply circle_sign (ht i j hij) (ht j k hjk)
    rw [hdiff, div_lt_iff₀ hN]
    apply mul_lt_mul_of_pos_left _ (by positivity)
    dsimp [N]
    exact_mod_cast (show (k.val:ℤ)-i.val < 2*(m:ℤ)-1 by omega)

theorem regular_wheel_count (m k : ℕ) (hm : 2 ≤ m) :
    count (wheel m) k = countCode (extend (wheelSigns m)) k :=
  count_by_signs _ _ (angle_sign hm) k

end WheelMatchings
