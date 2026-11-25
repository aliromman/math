module

public import conjectures.MabilatGoldenQuiddities.Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace MabilatGoldenQuiddities
noncomputable section
open Real
local notation "φ" => goldenRatio

private abbrev UnitSign (s : ℤ) := s=1 ∨ s= -1

private def cap (s : ℤ) (w : List ℤ) : ℝ :=
  if w.head? = some s then (if w.tail.head? = some s then φ else 1) else φ⁻¹

private theorem cap_limits (s : ℤ) (w : List ℤ) : 0 < cap s w ∧ cap s w ≤ φ := by
  have H := one_lt_goldenRatio
  have h₀ := inv_pos.mpr goldenRatio_pos
  have h₁ := inv_lt_one_of_one_lt₀ H
  simp only [cap]
  split
  · split <;> constructor <;> linarith
  · exact ⟨h₀,h₁.le.trans H.le⟩

private def Safe (w : List ℤ) : Prop :=
  0 ∉ w ∧ ∀ s, UnitSign s → ¬ [s,s,s].IsInfix w

private theorem safe_tail {k : ℤ} {w : List ℤ} (h : Safe (k :: w)) : Safe w :=
  ⟨fun h₀ => h.1 (List.mem_cons_of_mem _ h₀),fun s hs hₛ =>
    h.2 s hs (by obtain ⟨a,b,rfl⟩ := hₛ; exact ⟨k::a,b,rfl⟩)⟩

private theorem not_triple {s : ℤ} {w : List ℤ} (h : Safe (s :: w)) (hs : UnitSign s)
    (hw : w.head? = some s) : w.tail.head? ≠ some s := by
  rintro ht
  cases w with
  | nil => simp at hw
  | cons a w =>
    have ea : a=s := by simpa using hw
    subst a
    cases w with
    | nil => simp at ht
    | cons b w =>
      have eb : b=s := by simpa using ht
      subst b
      exact h.2 s hs ⟨[],w,rfl⟩

private def bounds (w : List ℤ) (r : ℝ) := ∀ s, UnitSign s → (s:ℝ)*r ≤ cap s w

private theorem advance {k s : ℤ} {w : List ℤ} {r : ℝ} (hs : UnitSign s)
    (hsk : 0 < s*k) (hw : Safe (k::w)) (hr : bounds w r) :
    (0 < (s:ℝ)*((k:ℝ)*φ-r)) ∧ ((s:ℝ)*((k:ℝ)*φ-r))⁻¹ ≤ cap s (k::w) := by
  have H := one_lt_goldenRatio
  have A := goldenRatio_pos
  have B : φ-φ⁻¹ = 1 := by rw [inv_goldenRatio,← one_sub_goldenConj]; ring
  have C : φ-1 = φ⁻¹ := by linarith
  have rs := hr s hs
  have D : (s:ℝ)*((k:ℝ)*φ-r) = ((s*k:ℤ):ℝ)*φ-(s:ℝ)*r := by push_cast; ring
  rw [D]
  by_cases eq : k=s
  · subst k
    have ss : s*s = 1 := by rcases hs with rfl|rfl <;> decide
    rw [ss,Int.cast_one,one_mul]
    by_cases prev : w.head? = some s
    · have no := not_triple hw hs prev
      have rr : (s:ℝ)*r ≤ 1 := by simpa only [cap,ite_eq_left prev,ite_eq_right no] using rs
      have L : φ⁻¹ ≤ φ - (s:ℝ)*r := by linarith
      have hpos := (inv_pos.mpr A).trans_le L
      exact ⟨hpos,by simpa [cap,prev] using (inv_anti₀ (inv_pos.mpr A) L)⟩
    · have rr : (s:ℝ)*r ≤ φ⁻¹ := by simpa [cap,prev] using rs
      have L : 1 ≤ φ-(s:ℝ)*r := by linarith
      exact ⟨by linarith,by simpa [cap,prev] using (inv_anti₀ zero_lt_one L)⟩
  · have big : 2 ≤ s*k := by rcases hs with rfl|rfl <;> simp_all <;> omega
    have bound := (rs.trans (cap_limits _ _).2)
    have hi : (2:ℝ) ≤ ((s*k:ℤ):ℝ) := by exact_mod_cast big
    have L : φ ≤ ((s*k:ℤ):ℝ)*φ-(s:ℝ)*r := by nlinarith [mul_le_mul_of_nonneg_right hi A.le]
    exact ⟨A.trans_le L,by simpa [cap,eq] using (inv_anti₀ A L)⟩

private def forward (w : List ℤ) := (w.map atom).prod

private theorem advanceCol (k : ℤ) (w : List ℤ) :
    forward (k::w) 0 0 = (k:ℝ)*φ * forward w 0 0 - forward w 1 0 ∧
    forward (k::w) 1 0 = forward w 0 0 := by
  simp [forward,atom,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

private theorem continuant_safe (w : List ℤ) (h : Safe w) :
    forward w 0 0 ≠ 0 ∧ bounds w (forward w 1 0 / forward w 0 0) := by
  induction w with
  | nil =>
    have b (s : ℤ) : 0 < cap s [] := (cap_limits s []).1
    exact ⟨by simp [forward],fun s _ => by simpa [forward,Matrix.one_apply] using (b s).le⟩
  | cons k w ih =>
    obtain ⟨hx,hr⟩ := ih (safe_tail h)
    let r := forward w 1 0 / forward w 0 0
    have kn : k≠0 := fun he => h.1 (by simp [he])
    obtain ⟨s,sg,sk⟩ : ∃ s : ℤ, UnitSign s ∧ 0 < s*k := by
      rcases lt_or_gt_of_ne kn with hk | hk
      · exact ⟨-1,Or.inr rfl,by omega⟩
      · exact ⟨1,Or.inl rfl,by omega⟩
    obtain ⟨pos,bnd⟩ := advance sg sk h hr
    have nz : (k:ℝ)*φ-r ≠ 0 := by intro e; change 0 < (s:ℝ)*((k:ℝ)*φ-r) at pos; simp [e] at pos
    let x := forward w 0 0
    have col := advanceCol k w
    have top : forward (k::w) 0 0 = ((k:ℝ)*φ-r)*x := by rw [col.1]; dsimp [r,x]; field_simp
    refine ⟨top.trans_ne (mul_ne_zero nz hx),?_⟩
    have nxt : forward (k::w) 1 0 / forward (k::w) 0 0 = ((k:ℝ)*φ-r)⁻¹ := by
      rw [col.2,top]
      dsimp [x]
      field_simp
    rw [nxt]
    intro t st
    have invs : (s:ℝ)⁻¹ = (s:ℝ) := by rcases sg with rfl|rfl <;> norm_num
    have rel : (s:ℝ)*((k:ℝ)*φ-r)⁻¹ = ((s:ℝ)*((k:ℝ)*φ-r))⁻¹ := by
      rw [mul_inv_rev,invs,mul_comm]
    by_cases eq : t=s
    · subst t; rw [rel]; exact bnd
    · have eh : t= -s := by rcases sg with rfl|rfl <;> rcases st with rfl|rfl <;> omega
      rw [eh,Int.cast_neg,neg_mul,rel]
      exact (neg_nonpos.mpr (inv_pos.mpr pos).le).trans (cap_limits _ _).1.le

theorem obstruction {w : List ℤ} (hq : Quiddity w) :
    0 ∈ w ∨ ∃ s : ℤ, (s=1 ∨ s= -1) ∧ [s,s,s].IsInfix w := by
  by_contra! no
  have safe : Safe w.reverse := by
    refine ⟨by simpa using no.1,fun s hs h => ?_⟩
    exact no.2 s hs (by simpa using h.reverse)
  obtain ⟨a,v,eq⟩ : ∃ a v, w.reverse = a::v := List.exists_cons_of_ne_nil
    (by simp only [ne_eq,List.reverse_eq_nil_iff]; intro e; have hp := hq.1; simp [e] at hp)
  rw [eq] at safe
  have nz := (continuant_safe v (safe_tail safe)).1
  have zero : matrix w 1 0 = 0 := by rcases hq.2 with h|h <;> simp [h]
  change forward w.reverse 1 0 = 0 at zero
  rw [eq,(advanceCol a v).2] at zero
  contradiction

end
end MabilatGoldenQuiddities
