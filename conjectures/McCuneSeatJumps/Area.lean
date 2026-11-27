module

public import conjectures.McCuneSeatJumps.Regions
public import conjectures.McCuneSeatJumps.Selection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
open MeasureTheory Finset Set
namespace McCuneSeatJumps

private noncomputable def lo (h k l b : ℕ) : ℝ := ((b:ℝ)-l)/(h+k)
private noncomputable def up (h l a : ℕ) : ℝ := ((a:ℝ)-l+1)/h

private theorem width_eq (h k l a b : ℕ) :
    (width h k l a b : ℝ) = (h+k:ℝ)*(a-l+1) - h*(b-l:ℝ) := by
  unfold width; push_cast; ring

private theorem interval_length {h k : ℕ} (hh : 0<h) (l a b : ℕ) :
    up h l a-lo h k l b = (width h k l a b:ℝ)/(h*(h+k)) := by
  rw [width_eq]; unfold up lo
  field_simp

private theorem old_new_bounds {h k l a b : ℕ} (hh : 0<h)
    (w : (width h k l a b:ℝ)<h) {s : ℝ} (hs : s ∈ Ioo (lo h k l b) (up h l a)) :
    0 < h*s-a+l ∧ h*s-a+l<1 ∧ 0 < (b:ℝ)-l+1-(h+k)*s ∧ (b:ℝ)-l+1-(h+k)*s<1 := by
  have H : (0:ℝ)<h := by exact_mod_cast hh
  have M : (0:ℝ)<h+k := by positivity
  rw [width_eq] at w
  have left : ((a:ℝ)-l)/h < lo h k l b := by
    apply (div_lt_div_iff₀ H M).mpr
    nlinarith only [w,Nat.cast_nonneg (α:=ℝ) k]
  have right : up h l a < ((b:ℝ)-l+1)/(h+k) := by
    apply (div_lt_div_iff₀ H M).mpr
    nlinarith only [w]
  have p := (div_lt_iff₀ H).mp (left.trans hs.1)
  have q := (lt_div_iff₀ H).mp hs.2
  have r := (div_lt_iff₀ M).mp hs.1
  have t := (lt_div_iff₀ M).mp (hs.2.trans right)
  constructor
  · linarith
  refine ⟨?_,?_,?_⟩ <;> linarith

private theorem span_of_neighbors {i : Fin 3} {e : Fin 3 → ℝ}
    (j : 0 < e (i+1)-e i ∧ e (i+1)-e i < 1)
    (t : 0 < e (i+2)-e i ∧ e (i+2)-e i < 1) : ∀ p q, e p-e q < 1 := by
  intro p q
  rcases cycle_cases i p with ep|ep|ep <;> rcases cycle_cases i q with eq|eq|eq <;> rw [ep,eq] <;>
    linarith [j.1,j.2,t.1,t.2]

private noncomputable def selectedBox (h k : ℕ) (i : Fin 3) (l a c : ℕ) :=
  box i (lo h k l (newSeats h k l a)) (up h l a)
        (lo h k l (newSeats h k l c)) (up h l c)

private theorem region_box {h k l a c : ℕ} (hh : 0<h) (hk : 0<k) (hl : 0<l)
    (sum : a+c+l=h) (i : Fin 3) (x : ℝ × ℝ) :
    x ∈ region h k i l a ↔ 0<cellWeight h k l a ∧ x ∈ selectedBox h k i l a c := by
  have H : (0:ℝ)<h := by exact_mod_cast hh
  have M : (0:ℝ)<h+k := by positivity
  constructor
  · rintro ⟨hp,A,B,hA,hB,lose,Al,Aa⟩
    have Bi : B i+1=A i := loss_one (sum_shares x) hp hA hB lose
    have SA := (cycle_sum A i).trans hA.1
    have SB := (cycle_sum B i).trans hB.1
    have Ac : A (i+2)=c := by omega
    have bound (j : Fin 3) : shares x j-shares x i ∈
          Ioo (lo h k l (B j)) (up h l (A j)) := by
      have v := hA.2 j i
      have w := hB.2 i j
      have Bl : (B i:ℝ)+1=l := by exact_mod_cast Bi.trans Al
      unfold err at v w
      rw [Al] at v
      push_cast at w
      exact ⟨(div_lt_iff₀ M).mpr (by nlinarith only [w,Bl]),(lt_div_iff₀ H).mpr (by linarith only [v])⟩
    have p := bound (i+1)
    have q := bound (i+2)
    rw [Aa] at p
    rw [Ac] at q
    have pos {y u v} (hy : y ∈ Ioo (lo h k l v) (up h l u)) : 0 < width h k l u v := by
      have w := sub_pos.mpr (hy.1.trans hy.2)
      rw [interval_length hh] at w
      exact_mod_cast (div_pos_iff_of_pos_right (by positivity)).mp w
    obtain ⟨weight,j,t⟩ := (selection_iff hh hk hl sum).mp
      ⟨by omega,pos p,pos q⟩
    rw [j] at p
    rw [t] at q
    exact ⟨weight,p,q⟩
  · rintro ⟨weight,p,q⟩
    let b := newSeats h k l a
    let d := newSeats h k l c
    let A := allocations i l a c
    let B := allocations i (l-1) b d
    have ⟨bs,wp,wq⟩ := (selection_iff (b:=b) (d:=d) hh hk hl sum).mpr ⟨weight,rfl,rfl⟩
    have ⟨_,eqp,eqq⟩ := selected_widths hh hk hl sum weight
    have rh : room h k l ≤ h := by
      have kl := Nat.mul_le_mul_left (3*k) hl
      unfold room; omega
    have wa : (width h k l a b:ℝ)<h := by
      have lt := Nat.mod_lt (k*(a+(h+1-l))) hh
      exact_mod_cast (eqp.trans_lt (by exact_mod_cast lt))
    have wc : (width h k l c d:ℝ)<h := by
      have R := Nat.pos_of_mul_pos_right (show 0 < residue h k l a*(room h k l-residue h k l a) from weight)
      have diff : room h k l-residue h k l a < h := by omega
      exact_mod_cast (eqq.trans_lt (by exact_mod_cast diff))
    have pa := old_new_bounds hh wa p
    have pc := old_new_bounds hh wc q
    have hA : Inside (shares x) h A := by
      refine ⟨by rw [← cycle_sum A i]; simpa [A,add_comm,add_left_comm,add_assoc] using sum,?_⟩
      apply span_of_neighbors (i:=i)
      · simp only [A,err,allocations_next,allocations_here]
        constructor <;> linarith only [pa.1,pa.2.1]
      · simp only [A,err,allocations_last,allocations_here]
        constructor <;> linarith only [pc.1,pc.2.1]
    have hB : Inside (shares x) (h+k) B := by
      refine ⟨by rw [← cycle_sum B i]; simpa [B,add_comm,add_left_comm,add_assoc] using bs,?_⟩
      have spread := span_of_neighbors (i:=i) (e:=fun j => -err (shares x) (h+k) B j)
      have Bl : ((l-1:ℕ):ℝ)=(l:ℝ)-1 := by rw [Nat.cast_sub hl]; norm_num
      simp only [B,err,allocations_next,allocations_last,allocations_here,Nat.cast_add,Bl] at spread
      have v := spread (by constructor <;> linarith only [pa.2.2.1,pa.2.2.2])
        (by constructor <;> linarith only [pc.2.2.1,pc.2.2.2])
      intro r t
      unfold err
      push_cast
      linarith only [v t r]
    have bounds := selected_old_bounds hh hk hl sum weight
    have hp (j) : 0 < shares x j := by
      have aj : 0 < A j := by
        rcases cycle_cases i j with rfl|rfl|rfl <;> simp [A] <;> omega
      have s := (cycle_sum (err (shares x) h A) j).trans (sum_errors (sum_shares x) hA.1)
      have e : -1 < err (shares x) h A j := by
        linarith only [s,hA.2 (j+1) j,hA.2 (j+2) j]
      have n : (1:ℝ)≤A j := by exact_mod_cast aj
      unfold err at e
      exact pos_of_mul_pos_right (by linarith : 0 < (h:ℝ)*shares x j) H.le
    exact ⟨hp,A,B,hA,hB,by simp [B,A]; omega,by simp [A],by simp [A]⟩

private theorem region_eq {h k l a c : ℕ} (hh : 0<h) (hk : 0<k) (hl : 0<l)
    (sum : a+c+l=h) (i : Fin 3) : region h k i l a =
    if 0<cellWeight h k l a then selectedBox h k i l a c else ∅ := by
  ext x
  rw [region_box hh hk hl sum]
  split_ifs with h <;> simp [h]

theorem measurable_region {h k l a c : ℕ} (hh : 0<h) (hk : 0<k) (hl : 0<l)
    (sum : a+c+l=h) (i : Fin 3) : MeasurableSet (region h k i l a) := by
  rw [region_eq hh hk hl sum]
  split_ifs
  · exact (open_box ..).measurableSet
  · exact MeasurableSet.empty

theorem volume_region {h k l a c : ℕ} (hh : 0<h) (hk : 0<k) (hl : 0<l)
    (sum : a+c+l=h) (i : Fin 3) : volume (region h k i l a) =
    ENNReal.ofReal ((cellWeight h k l a:ℝ)/(3*h^2*(h+k)^2)) := by
  rw [region_eq hh hk hl sum]
  split_ifs with w
  · rw [selectedBox,volume_box,interval_length hh,interval_length hh]
    obtain ⟨b,v,z⟩ := (selection_iff hh hk hl sum).mpr ⟨w,rfl,rfl⟩
    have prod := width_product hh hk hl sum b v z
    have prodR : (width h k l a (newSeats h k l a):ℝ) *
        (width h k l c (newSeats h k l c):ℝ) = cellWeight h k l a := by exact_mod_cast prod
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul]
    · congr 1
      rw [← prodR]
      field_simp
    · positivity
  · simp [Nat.eq_zero_of_not_pos w]

end McCuneSeatJumps
