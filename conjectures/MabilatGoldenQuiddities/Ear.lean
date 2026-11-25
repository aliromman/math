module

public import conjectures.MabilatGoldenQuiddities.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace MabilatGoldenQuiddities
noncomputable section
open Real

/-- Use q=m+4. The normalized sines satisfy S(k+2)=λ S(k+1)-S(k). -/
def angle (m : ℕ) : ℝ := π / (m+4)
def parameter (m : ℕ) := 2*cos (angle m)
def sine (m k : ℕ) := sin (k*angle m)/sin (angle m)

private theorem angle_mul (m : ℕ) : ((m:ℝ)+4)*angle m=π := by
  unfold angle
  field_simp

private theorem angle_pos (m : ℕ) : 0<angle m := div_pos pi_pos (by positivity)

private theorem angle_lt_pi (m : ℕ) : angle m<π := by
  have four : (1:ℝ)<m+4 := by linarith [Nat.cast_nonneg (α:=ℝ) m]
  nlinarith only [mul_lt_mul_of_pos_right four (angle_pos m),angle_mul m]

private theorem sin_angle_pos (m : ℕ) : 0<sin (angle m) :=
  sin_pos_of_pos_of_lt_pi (angle_pos m) (angle_lt_pi m)

@[simp] theorem sine_zero (m : ℕ) : sine m 0 = 0 := by simp [sine]

@[simp] theorem sine_one (m : ℕ) : sine m 1 = 1 := by simp [sine,(sin_angle_pos m).ne']

theorem sine_rec (m k : ℕ) : sine m (k+2) = parameter m * sine m (k+1) - sine m k := by
  have sub (x y : ℝ) : sin (x+y) = 2*cos y*sin x-sin (x-y) := by
    rw [sin_add,sin_sub]; ring
  have plus : ((k:ℝ)+2)*angle m = ((k:ℝ)+1)*angle m+angle m := by ring
  have minus : ((k:ℝ)+1)*angle m-angle m = k*angle m := by ring
  simp only [sine,parameter,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,plus]
  rw [sub,minus]
  ring

@[simp] theorem sine_two (m : ℕ) : sine m 2 = parameter m := by
  simpa using sine_rec m 0

private theorem sine_pos {m k : ℕ} (hk : 0<k) (hu : k<m+4) : 0 < sine m k := by
  have lt : (k:ℝ) < m+4 := by exact_mod_cast hu
  have hi : (k:ℝ)*angle m < π := by simpa [angle_mul] using
    (mul_lt_mul_of_pos_right lt (angle_pos m))
  apply div_pos _ (sin_angle_pos m)
  exact sin_pos_of_pos_of_lt_pi (mul_pos (by exact_mod_cast hk) (angle_pos m)) hi

@[simp] theorem sine_end (m : ℕ) : sine m (m+4) = 0 := by simp [sine,angle_mul]

private theorem sine_nonneg {m k : ℕ} (hk : k≤m+4) : 0≤sine m k := by
  rcases eq_or_lt_of_le hk with rfl|hl
  · simp
  · rcases Nat.eq_zero_or_pos k with rfl|hp
    · simp
    · exact (sine_pos hp hl).le

@[simp] theorem sine_penultimate (m : ℕ) : sine m (m+3)=1 := by
  have eq : ((m:ℝ)+3)*angle m=π-angle m := by linarith [angle_mul m]
  simp [sine,eq,sin_pi_sub,(sin_angle_pos m).ne']

@[simp] theorem sine_antepenultimate (m : ℕ) : sine m (m+2)=parameter m := by
  have h := sine_rec m (m+2)
  change sine m (m+4) = parameter m * sine m (m+3) - sine m (m+2) at h
  simp at h
  linarith

theorem sine_interior {m k : ℕ} (hlo : 2≤k) (hhi : k≤m+2) : 1<sine m k := by
  have lo : 1<(k:ℝ) := by exact_mod_cast (show 1<k by omega)
  have hi : (k:ℝ) < (m:ℝ)+3 := by exact_mod_cast (show k<m+3 by omega)
  let θ := angle m
  have a : θ < k*θ := by simpa using (mul_lt_mul_of_pos_right lo (angle_pos m))
  have b : k*θ < π-θ := by
    have aux := mul_lt_mul_of_pos_right hi (angle_pos m)
    change (k:ℝ)*θ < ((m:ℝ)+3)*θ at aux
    have h := angle_mul m
    change ((m:ℝ)+4)*θ=π at h
    linarith
  have p : 0<θ := angle_pos m
  have c : 0<cos ((k*θ+θ)/2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith⟩
  have d : 0<sin ((k*θ-θ)/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have inc : sin θ < sin (k*θ) := by
    apply sub_pos.mp
    rw [sin_sub_sin]
    positivity
  exact (one_lt_div (sin_angle_pos m)).mpr inc

theorem one_lt_parameter (m : ℕ) : 1<parameter m := by
  simpa using (sine_interior (m:=m) (k:=2) (by decide) (by omega))


abbrev UnitSign (s : ℤ) := s=1 ∨ s= -1

private def run (s : ℤ) : List ℤ → ℕ
  | [] => 0
  | k :: w => if k=s then run s w + 1 else 0

private theorem run_prefix (j : ℕ) (s : ℤ) (w : List ℤ) (h : j≤run s w) :
    (List.replicate j s).IsPrefix w := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    cases w with
    | nil => simp [run] at h
    | cons k w =>
      by_cases hk : k=s
      · subst k
        obtain ⟨b,eb⟩ := ih w (by simpa [run] using h)
        exact ⟨b,by simp [List.replicate_succ,eb]⟩
      · simp [run,hk] at h

private def Safe (m : ℕ) (w : List ℤ) : Prop :=
  0 ∉ w ∧ ∀ s, UnitSign s → ¬ (List.replicate (m+2) s).IsInfix w

private theorem safe_tail {m : ℕ} {k : ℤ} {w : List ℤ} (h : Safe m (k :: w)) : Safe m w :=
  ⟨fun h₀ => h.1 (List.mem_cons_of_mem _ h₀),fun s hs hₛ => h.2 s hs (List.infix_cons hₛ)⟩

private theorem run_bound {m : ℕ} {s : ℤ} {w : List ℤ} (hs : UnitSign s) (h : Safe m w) :
    run s w≤m+1 := by
  by_contra! e
  exact h.2 s hs (run_prefix (m+2) s w (by omega)).isInfix

private def cap (m j : ℕ) : ℝ := sine m (j+1)/sine m (j+2)

private theorem cap_limits {m j : ℕ} (hj : j≤m+1) :
    0<cap m j ∧ cap m j≤parameter m := by
  have h₁ : 0<sine m (j+1) := sine_pos (by omega) (by omega)
  have h₂ : 0<sine m (j+2) := sine_pos (by omega) (by omega)
  refine ⟨div_pos h₁ h₂,(div_le_iff₀ h₂).mpr ?_⟩
  have hrec := sine_rec m (j+1)
  have h₃ : 0≤sine m (j+3) := sine_nonneg (by omega)
  change sine m (j+3) = parameter m*sine m (j+2)-sine m (j+1) at hrec
  linarith

private theorem cap_step {m j : ℕ} (hj : j≤m) :
    0 < parameter m-cap m j ∧ (parameter m-cap m j)⁻¹=cap m (j+1) := by
  have h₂ : 0<sine m (j+2) := sine_pos (by omega) (by omega)
  have h₃ : 0<sine m (j+3) := sine_pos (by omega) (by omega)
  have hrec := sine_rec m (j+1)
  change sine m (j+3) = parameter m*sine m (j+2)-sine m (j+1) at hrec
  have diff : parameter m-cap m j = sine m (j+3)/sine m (j+2) := by
    unfold cap
    rw [hrec]; field_simp
  rw [diff]
  exact ⟨div_pos h₃ h₂,inv_div _ _⟩

private def bounds (m : ℕ) (w : List ℤ) (r : ℝ) :=
  ∀ s, UnitSign s → (s:ℝ)*r ≤ cap m (run s w)

private theorem advance {m : ℕ} {k s : ℤ} {w : List ℤ} {r : ℝ} (hs : UnitSign s)
    (hsk : 0 < s*k) (hw : Safe m (k::w)) (hr : bounds m w r) :
    0 < (s:ℝ)*((k:ℝ)*parameter m-r) ∧
    ((s:ℝ)*((k:ℝ)*parameter m-r))⁻¹ ≤ cap m (run s (k::w)) := by
  have pos := (one_lt_parameter m).trans' zero_lt_one
  have rs := hr s hs
  have D : (s:ℝ)*((k:ℝ)*parameter m-r) = ((s*k:ℤ):ℝ)*parameter m-(s:ℝ)*r := by push_cast; ring
  rw [D]
  by_cases eq : k=s
  · subst k
    have ss : s*s = 1 := by rcases hs with rfl|rfl <;> decide
    rw [ss,Int.cast_one,one_mul]
    have run_small : run s w≤m := by simpa [run] using run_bound hs hw
    obtain ⟨hp,hi⟩ := cap_step run_small
    have le : parameter m-cap m (run s w) ≤ parameter m-(s:ℝ)*r := by linarith
    exact ⟨hp.trans_le le,by simpa [hi,run] using (inv_anti₀ hp le)⟩
  · have big : 2 ≤ s*k := by rcases hs with rfl|rfl <;> simp_all <;> omega
    have bound := rs.trans (cap_limits (run_bound hs (safe_tail hw))).2
    have hi : (2:ℝ) ≤ ((s*k:ℤ):ℝ) := by exact_mod_cast big
    have le : parameter m ≤ ((s*k:ℤ):ℝ)*parameter m-(s:ℝ)*r := by
      nlinarith [mul_le_mul_of_nonneg_right hi pos.le]
    exact ⟨pos.trans_le le,by simpa [run,eq,cap] using (inv_anti₀ pos le)⟩

private def forward (m : ℕ) (w : List ℤ) := (w.map (atom (parameter m))).prod

private theorem advanceCol (m : ℕ) (k : ℤ) (w : List ℤ) :
    forward m (k::w) 0 0 = (k:ℝ)*parameter m * forward m w 0 0 - forward m w 1 0 ∧
    forward m (k::w) 1 0 = forward m w 0 0 := by
  simp [forward,atom,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

private theorem continuant_safe (m : ℕ) (w : List ℤ) (h : Safe m w) :
    forward m w 0 0 ≠ 0 ∧ bounds m w (forward m w 1 0 / forward m w 0 0) := by
  induction w with
  | nil =>
    refine ⟨by simp [forward],fun s _ => ?_⟩
    simpa [forward,Matrix.one_apply,run] using (cap_limits (j:=0) (by omega : 0≤m+1)).1.le
  | cons k w ih =>
    obtain ⟨hx,hr⟩ := ih (safe_tail h)
    let r := forward m w 1 0 / forward m w 0 0
    have kn : k≠0 := fun he => h.1 (by simp [he])
    obtain ⟨s,sg,sk⟩ : ∃ s : ℤ, UnitSign s ∧ 0 < s*k := by
      rcases lt_or_gt_of_ne kn with hk | hk
      · exact ⟨-1,Or.inr rfl,by omega⟩
      · exact ⟨1,Or.inl rfl,by omega⟩
    obtain ⟨pos,bnd⟩ := advance sg sk h hr
    have nz : (k:ℝ)*parameter m-r ≠ 0 := by
      intro e; change 0 < (s:ℝ)*((k:ℝ)*parameter m-r) at pos; simp [e] at pos
    let x := forward m w 0 0
    have col := advanceCol m k w
    have top : forward m (k::w) 0 0 = ((k:ℝ)*parameter m-r)*x := by
      rw [col.1]; dsimp [r,x]; field_simp
    refine ⟨top.trans_ne (mul_ne_zero nz hx),?_⟩
    have nxt : forward m (k::w) 1 0 / forward m (k::w) 0 0 = ((k:ℝ)*parameter m-r)⁻¹ := by
      rw [col.2,top]; dsimp [x]; field_simp
    rw [nxt]
    intro t st
    have invs : (s:ℝ)⁻¹ = (s:ℝ) := by rcases sg with rfl|rfl <;> norm_num
    have rel : (s:ℝ)*((k:ℝ)*parameter m-r)⁻¹ = ((s:ℝ)*((k:ℝ)*parameter m-r))⁻¹ := by
      rw [mul_inv_rev,invs,mul_comm]
    by_cases eq : t=s
    · subst t; rw [rel]; exact bnd
    · have eh : t= -s := by rcases sg with rfl|rfl <;> rcases st with rfl|rfl <;> omega
      rw [eh,Int.cast_neg,neg_mul,rel]
      exact (neg_nonpos.mpr (inv_pos.mpr pos).le).trans (cap_limits (run_bound (eh ▸ st) h)).1.le

theorem obstruction (m : ℕ) {w : List ℤ} (hq : Quiddity (parameter m) w) :
    0 ∈ w ∨ ∃ s : ℤ, UnitSign s ∧ (List.replicate (m+2) s).IsInfix w := by
  by_contra! no
  have safe : Safe m w.reverse := by
    refine ⟨by simpa using no.1,fun s hs h => ?_⟩
    exact no.2 s hs (by simpa using h.reverse)
  obtain ⟨a,v,eq⟩ : ∃ a v, w.reverse = a::v := List.exists_cons_of_ne_nil
    (by simp only [ne_eq,List.reverse_eq_nil_iff]; intro e; have hp := hq.1; simp [e] at hp)
  rw [eq] at safe
  have nz := (continuant_safe m v (safe_tail safe)).1
  have zero : matrix (parameter m) w 1 0 = 0 := by rcases hq.2 with h|h <;> simp [h]
  change forward m w.reverse 1 0 = 0 at zero
  rw [eq,(advanceCol m a v).2] at zero
  contradiction


end
end MabilatGoldenQuiddities
