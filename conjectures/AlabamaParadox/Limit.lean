module

public import conjectures.AlabamaParadox.Weyl
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace AlabamaParadox
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def allocate (q : ι → ℝ) (h : ℤ) (a : ι → ℤ) : Prop :=
  ∑ i, a i = h ∧ ∃ W : Finset ι,
    (∀ i, a i = ⌊q i⌋ + if i ∈ W then 1 else 0) ∧
    ∀ i ∈ W, ∀ j ∉ W, Int.fract (q j) ≤ Int.fract (q i)

private def phaseLoss (q p : ι → ℝ) : Prop :=
  ∃ a b, allocate q 0 a ∧ allocate (q+p) 1 b ∧ ∃ i, b i < a i

private theorem allocate_shift (q : ι → ℝ) (h : ℤ) (a l : ι → ℤ) :
    allocate (fun i => q i + (l i : ℝ)) (h + ∑ i, l i) (a+l) ↔ allocate q h a := by
  simp only [allocate,Pi.add_apply,Finset.sum_add_distrib,Int.floor_add_intCast,
    Int.fract_add_intCast,add_left_inj]
  constructor <;> rintro ⟨hs,W,hw,ho⟩ <;> refine ⟨hs,W,fun i => ?_,ho⟩ <;> have := hw i <;> omega

private theorem loss_phase {p q : ι → ℝ} {n : ℕ} (hn : 0 < n) (l : ι → ℤ)
    (hs : ∑ i, l i = (n : ℤ)) (he : ∀ i, (n:ℝ)*p i = q i + l i) :
    Loss p n ↔ phaseLoss q p := by
  have ho (a : ι → ℤ) : Hamilton p n (a+l) ↔ allocate q 0 a := by
    convert allocate_shift q 0 a l using 1
    simp only [zero_add,hs,Hamilton,allocate,← he]
  have ht (b : ι → ℤ) : Hamilton p (n+1) (b+l) ↔ allocate (q+p) 1 b := by
    convert allocate_shift (q+p) 1 b l using 1
    have hn' i : (↑(n+1:ℕ):ℝ)*p i = (q+p) i + (l i:ℝ) := by
      push_cast
      simp only [Pi.add_apply]
      linarith [he i]
    simp only [Hamilton,allocate,← hn',hs,Nat.cast_add,Nat.cast_one,add_comm (1:ℤ)]
  constructor
  · rintro ⟨_,a,b,ha,hb,i,hi⟩
    refine ⟨a-l,b-l,(ho _).mp (by simpa using ha),(ht _).mp (by simpa using hb),i,?_⟩
    simpa using hi
  · rintro ⟨a,b,ha,hb,i,hi⟩
    exact ⟨hn,a+l,b+l,(ho _).mpr ha,(ht _).mpr hb,i,by simpa using hi⟩

private def extend {G : Type*} [AddCommGroup G] (z : ι → G) (i : Option ι) : G :=
  i.elim (-(∑ j, z j)) z

private def char (i : Option ι) : UnitAddTorus ι →+ UnitAddCircle where
  toFun x := extend x i
  map_zero' := by cases i <;> simp [extend]
  map_add' x y := by cases i <;> simp [extend,Finset.sum_add_distrib,add_comm]

omit [DecidableEq ι] in
private theorem cont_char (i : Option ι) : Continuous (char i : UnitAddTorus ι → UnitAddCircle) := by
  cases i <;> simp [char,extend] <;> fun_prop

private def rep (z : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 (0:ℝ) z : ℝ)
private def quotas (x : UnitAddTorus ι) : Option ι → ℝ := extend (rep ∘ x)

omit [DecidableEq ι] in
private theorem char_quota (x : UnitAddTorus ι) (i : Option ι) : mkCircle (quotas x i) = char i x := by
  cases i <;> simp [quotas,char,extend,rep,mkCircle]

private theorem rep_coe (t : ℝ) : rep (mkCircle t) = Int.fract t := by
  change rep (t : UnitAddCircle) = _
  rw [← AddCircle.coe_fract t]
  have hh : Int.fract t ∈ Ico (0:ℝ) (0+1) := ⟨Int.fract_nonneg _,by simpa using Int.fract_lt_one t⟩
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hh)

omit [DecidableEq ι] in
private theorem char_line (v : ι → ℝ) (i : Option ι) (s : ℝ) :
    char i (fun j => mkCircle (s * v j)) = mkCircle (s * extend v i) := by
  cases i <;> simp [char,extend,Finset.mul_sum,mkCircle]

omit [DecidableEq ι] in
private theorem fiber_null (f : UnitAddTorus ι →+ UnitAddCircle) (hf : Continuous f)
    (v : ι → ℝ) (d : ℝ) (hd : d ≠ 0)
    (he : ∀ s, f (fun j => mkCircle (s*v j)) = mkCircle (s*d)) (b : UnitAddCircle) :
    torusHaar ι {x | f x = b} = 0 := by
  have sur : Function.Surjective f := by
    intro u
    refine ⟨fun j => mkCircle ((rep u / d) * v j), ?_⟩
    rw [he,div_mul_cancel₀ _ hd]
    exact AddCircle.coe_equivIco
  let : (torusHaar ι).IsAddHaarMeasure := by unfold torusHaar; infer_instance
  have h : MeasurePreserving f (torusHaar ι) AddCircle.haarAddCircle :=
    AddMonoidHom.measurePreserving hf sur (by simp)
  rw [show {x | f x = b} = f ⁻¹' {b} by ext; simp]
  simpa using h.measure_preimage (s := {b}) (measurableSet_singleton b).nullMeasurableSet

private def step (p : Option ι → ℝ) (two : Bool) (i : Option ι) : ℝ :=
  if two then p i else 0

private def quotaAt (p : Option ι → ℝ) (u : Bool) (x : UnitAddTorus ι) (i : Option ι) : ℝ :=
  quotas x i + step p u i

private def regular (p : Option ι → ℝ) (x : UnitAddTorus ι) : Prop :=
  ∀ u i, mkCircle (quotaAt p u x i) ≠ 0 ∧
    ∀ j, i ≠ j → mkCircle (quotaAt p u x i) ≠ mkCircle (quotaAt p u x j)

omit [DecidableEq ι] in
private theorem char_at (p : Option ι → ℝ) (u : Bool) (x : UnitAddTorus ι) (i : Option ι) :
    mkCircle (quotaAt p u x i) = char i x + mkCircle (step p u i) := by
  exact (AddCircle.coe_add ..).trans (congrArg (· + _) (char_quota x i))

omit [DecidableEq ι] in
private theorem regular_ae [Nonempty ι] (p : Option ι → ℝ) : ∀ᵐ x ∂torusHaar ι, regular p x := by
  classical
  let v (i : ι) : ℝ := (Fintype.equivFin ι i).val + 1
  have vp i : 0 < v i := by dsimp [v]; positivity
  have vn : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => vp i) Finset.univ_nonempty
  have nonzero (i : Option ι) : extend v i ≠ 0 := by
    cases i with
    | none => exact (neg_lt_zero.mpr vn).ne
    | some i => exact (vp i).ne'
  have inj : Function.Injective (extend v) := by
    intro i j h
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact ((neg_lt_zero.mpr vn).trans (vp j)).ne h |>.elim
    | some i =>
      cases j with
      | none => exact ((neg_lt_zero.mpr vn).trans (vp i)).ne h.symm |>.elim
      | some j =>
        change (_ : ℝ) + 1 = _ + 1 at h
        exact congrArg some ((Fintype.equivFin ι).injective (Fin.ext (by exact_mod_cast add_right_cancel h)))
  apply ae_all_iff.2
  intro u
  apply ae_all_iff.2
  intro i
  apply Filter.Eventually.and
  · rw [ae_iff]
    apply measure_mono_null _ (fiber_null (char i) (cont_char i) v _ (nonzero i)
      (char_line v i) (-mkCircle (step p u i)))
    intro x hx
    have h : mkCircle (quotaAt p u x i) = 0 := not_ne_iff.mp hx
    rw [char_at] at h
    exact eq_neg_of_add_eq_zero_left h
  · apply ae_all_iff.2
    intro j
    by_cases ij : i = j
    · exact .of_forall fun _ h => (h ij).elim
    · have hline (s : ℝ) : (char i - char j) (fun k => mkCircle (s * v k)) =
          mkCircle (s * (extend v i - extend v j)) := by
        simp only [AddMonoidHom.sub_apply,char_line,mul_sub]
        rfl
      rw [ae_iff]
      apply measure_mono_null _ (fiber_null (char i - char j) ((cont_char i).sub (cont_char j)) v _
        (sub_ne_zero.mpr (fun h => ij (inj h))) hline (mkCircle (step p u j) - mkCircle (step p u i)))
      intro x hx
      have h : mkCircle (quotaAt p u x i) = mkCircle (quotaAt p u x j) := by
        by_contra h
        exact hx (fun _ => h)
      rw [char_at,char_at] at h
      change char i x - char j x = _
      exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using h)

omit [DecidableEq ι] in
private theorem quota_cont {p : Option ι → ℝ} {x : UnitAddTorus ι} (hx : regular p x)
    (u : Bool) (i : Option ι) : ContinuousAt (fun y => quotaAt p u y i) x := by
  have hj (j : ι) : x j ≠ 0 := by
    have h := (hx false (some j)).1
    simpa [char_at,char,extend,step] using h
  have hc (j : ι) : ContinuousAt (fun y : UnitAddTorus ι => rep (y j)) x :=
    continuousAt_subtype_val.comp ((AddCircle.continuousAt_equivIco 1 (0:ℝ)
      (by simpa using hj j)).comp (continuous_apply j).continuousAt)
  apply ContinuousAt.add _ continuousAt_const
  cases i with
  | none => exact (tendsto_finsetSum _ fun j _ => (hc j).tendsto).neg
  | some i => exact hc i

omit [DecidableEq ι] in
private theorem quota_noninteger {p : Option ι → ℝ} {x : UnitAddTorus ι} (hx : regular p x)
    (u : Bool) (i : Option ι) : quotaAt p u x i ≠ (⌊quotaAt p u x i⌋ : ℤ) := by
  intro h
  apply (hx u i).1
  conv_lhs => rw [h]
  unfold mkCircle
  rw [← AddCircle.coe_fract]
  simp

private theorem allocate_congr {q r : ι → ℝ} {h : ℤ} {a : ι → ℤ}
    (hf : ∀ i, ⌊q i⌋ = ⌊r i⌋)
    (ho : ∀ i j, Int.fract (q i) ≤ Int.fract (q j) ↔ Int.fract (r i) ≤ Int.fract (r j)) :
    allocate q h a ↔ allocate r h a := by
  simp only [allocate,hf,ho]

private theorem local_loss {p : Option ι → ℝ} {x : UnitAddTorus ι} (hx : regular p x) :
    ∀ᶠ y in 𝓝 x, phaseLoss (quotas y) p ↔ phaseLoss (quotas x) p := by
  have floors (u : Bool) (i : Option ι) : ∀ᶠ y in 𝓝 x,
      ⌊quotaAt p u y i⌋ = ⌊quotaAt p u x i⌋ := by
    have h := Ico_mem_nhds ((Int.floor_le _).lt_of_ne (quota_noninteger hx u i).symm)
      (Int.lt_floor_add_one (quotaAt p u x i))
    exact ((quota_cont hx u i).eventually h).mono fun _ hy => Int.floor_eq_iff.mpr hy
  have fractcont (u : Bool) (i : Option ι) :
      ContinuousAt (fun y => Int.fract (quotaAt p u y i)) x :=
    (continuousAt_fract (quota_noninteger hx u i)).comp (f := fun y : UnitAddTorus ι => quotaAt p u y i) (quota_cont hx u i)
  have order (u : Bool) (i j : Option ι) : ∀ᶠ y in 𝓝 x,
      Int.fract (quotaAt p u y i) ≤ Int.fract (quotaAt p u y j) ↔
      Int.fract (quotaAt p u x i) ≤ Int.fract (quotaAt p u x j) := by
    rcases eq_or_ne i j with rfl | hij
    · exact .of_forall fun _ => iff_of_true le_rfl le_rfl
    have hn : Int.fract (quotaAt p u x i) ≠ Int.fract (quotaAt p u x j) := by
      intro he
      apply (hx u i).2 j hij
      simpa [mkCircle] using congrArg mkCircle he
    rcases lt_or_gt_of_ne hn with H | H
    · exact ((fractcont u i).eventually_lt (fractcont u j) H).mono fun _ h => iff_of_true h.le H.le
    · exact ((fractcont u j).eventually_lt (fractcont u i) H).mono fun _ h => iff_of_false h.not_ge H.not_ge
  have F := Filter.eventually_all.2 fun u => Filter.eventually_all.2 (floors u)
  have O := Filter.eventually_all.2 fun u => Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 (order u i)
  filter_upwards [F,O] with y hF hO
  have old (a : Option ι → ℤ) : allocate (quotas y) 0 a ↔ allocate (quotas x) 0 a :=
    allocate_congr (by simpa [quotaAt,step] using hF false) (by simpa [quotaAt,step] using hO false)
  have new (b : Option ι → ℤ) : allocate (quotas y + p) 1 b ↔ allocate (quotas x + p) 1 b :=
    allocate_congr (hF true) (hO true)
  simp only [phaseLoss,old,new]

private def losing (p : Option ι → ℝ) : Set (UnitAddTorus ι) := {x | phaseLoss (quotas x) p}

private theorem loss_boundary [Nonempty ι] (p : Option ι → ℝ) : torusHaar ι (frontier (losing p)) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [regular_ae p] with x hx
  rw [frontier_eq_closure_inter_closure]
  rcases em (x ∈ losing p) with h | h
  · exact fun hf => (mem_closure_iff_frequently.mp hf.2) ((local_loss hx).mono fun _ he => fun hny => hny (he.mpr h))
  · exact fun hf => (mem_closure_iff_frequently.mp hf.1) ((local_loss hx).mono fun _ he => (h ∘ he.mp))

private theorem freq_mono {A B : ℕ → Prop} (hab : ∀ n, A n → B n) (N : ℕ) :
    frequency A N ≤ frequency B N := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right _ (fun n _ => hab n))

private theorem phase_none_zero (p : ι → ℝ) (hp : ∀ i, 0 < p i) : ¬ phaseLoss 0 p := by
  rintro ⟨a,b,⟨hs,W,hw,_⟩,⟨_,V,hv,_⟩,i,hi⟩
  have apos j : 0 ≤ a j := by
    rw [hw j]
    simp only [Pi.zero_apply, Int.floor_zero, zero_add]
    split <;> decide
  have az := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => apos j)).1 hs i (Finset.mem_univ _)
  have bh := hv i
  simp only [zero_add] at bh
  have := Int.floor_nonneg.mpr (hp i).le
  split at bh <;> omega

private theorem loss_orbit (p : Option ι → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (n : ℕ) :
    Loss p n ↔ n • (fun j => mkCircle (p (some j))) ∈ losing p := by
  let v (j : ι) := mkCircle (p (some j))
  have hrep : rep (0 : UnitAddCircle) = 0 := by simpa [mkCircle] using rep_coe 0
  by_cases hn : n = 0
  · subst n
    have z : quotas (0 : UnitAddTorus ι) = 0 := by
      ext i
      cases i <;> simp [quotas,extend,hrep]
    simp [Loss,losing,z,phase_none_zero p hp]
  · let f (j : ι) : ℤ := ⌊(n:ℝ)*p (some j)⌋
    let l (i : Option ι) : ℤ := i.elim ((n:ℤ) - ∑ j, f j) f
    apply loss_phase (Nat.pos_of_ne_zero hn) l
    · simp [l,Fintype.sum_option]
    · have someq (j : ι) : quotas (n • v) (some j) = Int.fract ((n:ℝ)*p (some j)) := by
        change rep (n • mkCircle (p (some j))) = _
        simpa only [← AddCircle.coe_nsmul,nsmul_eq_mul] using rep_coe ((n:ℝ)*p (some j))
      have someHe (j : ι) : (n:ℝ)*p (some j) = quotas (n • v) (some j) + (f j : ℝ) := by
        rw [someq,Int.fract]; simp [f]
      intro i
      cases i with
      | some i => exact someHe i
      | none =>
        have hnq : quotas (n • v) none = -∑ j : ι, quotas (n • v) (some j) := rfl
        rw [Fintype.sum_option] at hs
        have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun j _ => someHe j
        rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
        change (n:ℝ)*p none = quotas (n • v) none + ((↑n - ∑ j, f j : ℤ):ℝ)
        rw [hnq]
        push_cast
        nlinarith [congrArg ((n:ℝ)*·) hs]

private theorem option_limit [Nonempty ι] (p : Option ι → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (hd : Nonresonant (fun j => p (some j))) :
    ∃ q : ℝ, Tendsto (frequency (Loss p)) atTop (𝓝 q) := by
  let S := losing p
  let v (j : ι) := mkCircle (p (some j))
  have hv := direction_of_nonresonant hd
  have hb := loss_boundary p
  have hI := weyl_frequency v hv (interior S) isOpen_interior.measurableSet
    (measure_mono_null frontier_interior_subset hb)
  have hC := weyl_frequency v hv (closure S) isClosed_closure.measurableSet
    (measure_mono_null frontier_closure_subset hb)
  have hI' : (torusHaar ι).real (interior S) = (torusHaar ι).real S :=
    congrArg ENNReal.toReal (measure_interior_of_null_frontier hb)
  have hC' : (torusHaar ι).real (closure S) = (torusHaar ι).real S :=
    congrArg ENNReal.toReal (measure_closure_of_null_frontier hb)
  rw [hI'] at hI
  rw [hC'] at hC
  exact ⟨_,tendsto_of_tendsto_of_tendsto_of_le_of_le hI hC
    (freq_mono (fun n h => (loss_orbit p hp hs n).2 (interior_subset h)))
    (freq_mono (fun n h => subset_closure ((loss_orbit p hp hs n).1 h)))⟩

private theorem hamilton_pull {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {p : κ → ℝ} {n : ℕ} {a : κ → ℤ} (ha : Hamilton p n a) :
    Hamilton (p ∘ e) n (a ∘ e) := by
  obtain ⟨hs,W,hw,ho⟩ := ha
  have mem (i : ι) : i ∈ W.map e.symm.toEmbedding ↔ e i ∈ W := by simp
  refine ⟨(e.sum_comp a).trans hs,W.map e.symm.toEmbedding,fun i => ?_,fun i hi j hj => ?_⟩
  · simpa only [Function.comp_apply,mem] using hw (e i)
  · exact ho _ ((mem i).mp hi) _ (fun h => hj ((mem j).mpr h))

private theorem loss_pull {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {p : κ → ℝ} {n : ℕ}
    (hl : Loss p n) : Loss (p ∘ e) n := by
  obtain ⟨hn,a,b,ha,hb,i,hi⟩ := hl
  exact ⟨hn,_,_,hamilton_pull e ha,hamilton_pull e hb,e.symm i,by simpa using hi⟩

/-- A single state receives every seat. -/
theorem frequency_subsingleton [Subsingleton ι] (p : ι → ℝ) : frequency (Loss p) = fun _ => 0 := by
  have never (n : ℕ) : ¬ Loss p n := by
    rintro ⟨_,a,b,ha,hb,i,hi⟩
    have total (a : ι → ℤ) : ∑ j, a j = a i :=
      Finset.sum_eq_single i (fun j _ ne => (ne (Subsingleton.elim _ _)).elim) (by simp)
    have h₀ := ha.1
    have h₁ := hb.1
    rw [total] at h₀ h₁
    omega
  exact funext fun N => by simp [frequency,never]

/-- Under Hamilton's rule, the positive house sizes at which a state loses a seat
have a limiting natural density. -/
theorem frequency_exists (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hind : IndependentShares p) : ∃ q : ℝ, Tendsto (frequency (Loss p)) atTop (𝓝 q) := by
  classical
  rcases subsingleton_or_nontrivial ι with h | h
  · exact ⟨0, frequency_subsingleton p ▸ tendsto_const_nhds⟩
  · let q : ι := Classical.arbitrary ι
    obtain ⟨j,hj⟩ := exists_ne q
    let : Nonempty {i : ι // i ≠ q} := ⟨⟨j,hj⟩⟩
    let e := Equiv.optionSubtypeNe q
    have H := option_limit (p ∘ e) (fun i => hp (e i)) ((e.sum_comp p).trans hs)
      (nonresonant_without_one p q hs hind)
    have E : Loss (p ∘ e) = Loss p := by
      funext n
      apply propext
      exact ⟨fun h => by simpa [Function.comp_def] using loss_pull e.symm h,loss_pull e⟩
    rwa [E] at H

/-- info: 'AlabamaParadox.frequency_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frequency_exists

end
end AlabamaParadox
