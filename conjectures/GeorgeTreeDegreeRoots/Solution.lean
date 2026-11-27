module

public import conjectures.GeorgeTreeDegreeRoots.Statement
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GeorgeTreeDegreeRoots

private theorem abs_im_pow_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    |(z ^ k).im| ≤ k * |z.im| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hRe : |(z ^ k).re| ≤ 1 := (Complex.abs_re_le_norm _).trans <|
      (norm_pow z k).le.trans (pow_le_one₀ (norm_nonneg _) hz)
    rw [pow_succ, Complex.mul_im]
    calc
      _ ≤ |(z ^ k).re * z.im| + |(z ^ k).im * z.re| := abs_add_le _ _
      _ ≤ 1 * |z.im| + (k * |z.im|) * 1 := by
        simp only [abs_mul]
        gcongr
        exact (Complex.abs_re_le_norm z).trans hz
      _ = _ := by push_cast; ring

private theorem scaled_im_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hi : z.im ≠ 0)
    (d : ℕ) (hd : 0 < d) : (z ^ d / z ^ 2).im / z.im ≤ (d : ℝ) - 2 := by
  have hn : z ≠ 0 := by rintro rfl; exact hi rfl
  cases d with
  | zero => exact (Nat.lt_irrefl _ hd).elim
  | succ d =>
    cases d with
    | zero =>
      have hSq := Complex.normSq_pos.mpr hn
      have hSq' : Complex.normSq z ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_one₀ (norm_nonneg _) hz
      have hInv : z / z ^ 2 = z⁻¹ := by field_simp
      rw [pow_one, hInv, Complex.inv_im]
      calc
        _ = -(1 / Complex.normSq z) := by field_simp
        _ ≤ _ := by
          norm_num
          exact (one_le_inv₀ hSq).mpr hSq'
    | succ k =>
      have hpow : z ^ (k + 2) / z ^ 2 = z ^ k := by rw [pow_add]; field_simp
      rw [hpow]
      have hbound : |(z ^ k).im / z.im| ≤ (k : ℝ) := by
        rw [abs_div, div_le_iff₀ (abs_pos.mpr hi)]
        exact abs_im_pow_le hz k
      push_cast
      linarith [(le_abs_self _).trans hbound]

/-- Each root in the closed unit disk is real, including any root on the boundary. -/
public theorem im_eq_zero {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) {z : ℂ} (hroot : degreeValue G z = 0) (hz : ‖z‖ ≤ 1) : z.im = 0 := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hV =>
    have := hG.connected.nonempty
    simp [degreeValue, Fintype.card_ne_zero] at hroot
  | inr hV =>
    by_contra hi
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ =>
      scaled_im_le hz hi (G.degree v)
        ((G.degree_pos_iff_exists_adj v).mpr (hG.preconnected.exists_adj_of_nontrivial v)))
    have he : ((G.edgeFinset.card : ℕ) : ℝ) + 1 = Fintype.card V := by
      exact_mod_cast hG.card_edgeFinset
    have hs : ∑ v, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hzero : ∑ v, (z ^ G.degree v / z ^ 2).im / z.im = 0 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Complex.im_sum]
      change (degreeValue G z * _).im * _ = 0
      simp [hroot]
    rw [hzero, Finset.sum_sub_distrib, hs] at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    linarith

public theorem result : Conjecture := by
  constructor
  · rintro z ⟨n, G, ht, hzero⟩ hz
    exact im_eq_zero ht hzero hz.le
  · intro hd
    let U : Set ℂ := {z | ‖z‖ < 1} ∩ {z | 0 < z.im}
    have hopen : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hex : U.Nonempty := by
      refine ⟨Complex.I / 2, ?_, ?_⟩
      · norm_num [norm_div]
      · norm_num [Complex.div_im]
    obtain ⟨z, ⟨hn, hi⟩, n, G, ht, hzero⟩ := hd.inter_open_nonempty U hopen hex
    exact hi.ne' (im_eq_zero ht hzero hn.le)

/-- info: 'GeorgeTreeDegreeRoots.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result

end GeorgeTreeDegreeRoots
