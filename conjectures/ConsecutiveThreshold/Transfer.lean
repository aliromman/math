module

public import conjectures.ConsecutiveThreshold.Spectrum
public import conjectures.ConsecutiveThreshold.TiltLaw

public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators Classical

/-- At a mode of the tilted inversion distribution, conditioning costs at most a universal
factor for every event determined by the middle quarter of the digits. -/
theorem conditional_event_bound {n m : ℕ} {q : ℝ} (hq : 0<q) (B : Code n → Prop)
    (depends : ∀ e f : Code n, (∀ i∈slice n,e i=f i) → (B e ↔ B f))
    (mode : ∀ j : ℤ, (∏ i : Fin n,geom q (n-i.val)).coeff j ≤
      (∏ i : Fin n,geom q (n-i.val)).coeff (m:ℤ)) :
    (((codeLayer n m).filter B).card:ℝ) ≤
      52*((∑ e : Code n,if B e then q^(∑ i,(e i).val) else 0) /
        (∑ e : Code n,q^(∑ i,(e i).val))) * ((codeLayer n m).card:ℝ) := by
  classical
  let S := slice n
  let P := ∏ i ∈ S,geom q (n-i.val)
  let R := ∏ i ∈ Sᶜ,geom q (n-i.val)
  let W := ∏ i : Fin n,geom q (n-i.val)
  have splitW : P*R=W := prod_mul_prod_compl S _
  have pp (T : Finset (Fin n)) : 0<atOne (∏ i∈T,geom q (n-i.val)) := by
    rw [map_prod]
    exact prod_pos fun i _ => atOne_geom_pos hq.le (by have := i.isLt; omega)
  have lp (T : Finset (Fin n)) : Mass.balanced (∏ i∈T,geom q (n-i.val)).coeff :=
    geom_prod_balanced T hq.le _
  have pos (T : Finset (Fin n)) : positiveSeries (∏ i∈T,geom q (n-i.val)) :=
    positive_prod T _ fun _ _ => positive_geom hq.le _
  obtain ⟨Y,yp,y⟩ := paired_residual n hq.le
  obtain ⟨E,ep,factor⟩ := event_factor hq.le S B depends
  change eventSeries q B=E*R at factor
  have md (j : ℤ) : (P*R).coeff j≤(P*R).coeff (m:ℤ) := splitW ▸ mode j
  have bound := slice_bound P R Y E (pos S) (pos Sᶜ) yp ep (pp S) (pp Sᶜ)
    (lp S) (lp Sᶜ) y (m:ℤ) md
  have all : eventSeries q (fun _ : Code n => True)=W := by
    unfold eventSeries
    simp only [ite_true]
    exact weight_all q (fun i : Fin n => n-i.val)
  have whole : atOne W=∑ e : Code n,q^(∑ i,(e i).val) := by
    rw [← all,event_atOne]
    simp
  have ev : atOne (eventSeries q B)=∑ e : Code n,if B e then q^(∑ i,(e i).val) else 0 := by
    rw [event_atOne,sum_filter]
  have mass : atOne W=atOne P*atOne R := by rw [←splitW,map_mul]
  have ratio : atOne E/atOne P =
      (∑ e : Code n,if B e then q^(∑ i,(e i).val) else 0)/(∑ e : Code n,q^(∑ i,(e i).val)) := by
    rw [←whole,←ev,factor,map_mul,mass]
    exact (mul_div_mul_right _ _ (pp Sᶜ).ne').symm
  have wc : W.coeff (m:ℤ)=((codeLayer n m).card:ℝ)*q^m := by
    change (full n q).coeff (m:ℤ)=_
    rw [full_coefficient]
    simp [mul_comm]
  rw [←factor,event_coeff,splitW,wc,ratio] at bound
  apply (mul_le_mul_iff_of_pos_right (pow_pos hq m)).mp
  simpa only [mul_assoc] using bound

end ConsecutiveThreshold
