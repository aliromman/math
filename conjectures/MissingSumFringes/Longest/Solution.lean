module

public import conjectures.MissingSumFringes.Longest.Statement
public import conjectures.MissingSumFringes.CoreTransfer
public import conjectures.MissingSumFringes.CorePositive
import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

private theorem centre {n : ℕ} {A : Finset ℕ} (hn : 0<n) (hA : A⊆range n) :
    run n A (extent n A) (width n-extent n A-extent (n-1) (reflect n A)) := by
  let l := extent n A
  let r := extent (n-1) (reflect n A)
  have hl : l≤n := extent_le ..
  have hr : r≤n-1 := extent_le ..
  change l + (width n-l-r) ≤ width n ∧ _
  constructor
  · unfold width; omega
  · intro x h₁ h₂
    change l≤x at h₁
    change x<l+(width n-l-r) at h₂
    by_cases h : x<n
    · exact present_of_extent h₁ h
    have hx : width n-1-x < n-1 := by unfold width at *; omega
    have left : r≤width n-1-x := by unfold width at *; omega
    have hit := present_of_extent left hx
    have bound : width n-1-x<width n := by unfold width; omega
    have eq : width n-1-(width n-1-x)=x := by unfold width at *; omega
    exact eq ▸ (reflect_sum hA hn bound).mp hit

theorem longest_eq {n q w : ℕ} {A : Finset ℕ} (hn : 0<n) (hA : A⊆range n)
    (hw : longest n A w) (hl : extent n A≤q) (hr : extent (n-1) (reflect n A)≤q)
    (small : 3*q<width n) : w=extent n A := by
  let l := extent n A
  let r := extent (n-1) (reflect n A)
  obtain ⟨j,hj,large⟩ := hw
  have long : width n-l-r≤j := large _ _ (centre hn hA)
  obtain ⟨fit,full⟩ := hj
  change l≤q at hl
  change r≤q at hr
  have lb : l≤w := by
    by_contra! h
    have miss := (mem_sdiff.mp (below_extent (n := n) (A := A) (by change 0<l; omega))).2
    apply miss
    exact full (l-1) (by omega) (by omega)
  by_contra neq
  change w≠l at neq
  have rpos : 0<r := by omega
  have miss := (mem_sdiff.mp (below_extent (n := n-1) (A := reflect n A) rpos)).2
  apply miss
  have rb : r-1<width n := by omega
  apply (reflect_sum hA hn rb).mpr
  exact full _ (by omega) (by omega)

theorem longest_bound {n w} {A : Finset ℕ} (hn : 0<n) (hA : A⊆range n)
    (hw : longest n A w) : w≤3*(extent n A + extent (n-1) (reflect n A)) := by
  let q := extent n A + extent (n-1) (reflect n A)
  by_cases h : 3*q < width n
  · rw [longest_eq hn hA hw (q := q) (by dsimp [q]; omega) (by dsimp [q]; omega) h]
    omega
  · obtain ⟨j,hj,_⟩ := hw
    have := hj.1
    change w≤3*q
    omega

theorem cell_weight_limit {W : ℕ → Finset ℕ → ℕ} (good : admissible W) (m t j s : ℕ) :
    Tendsto (fun n ↦ cellWeight n m t j s (fun A ↦ (W n A : ℝ))) atTop
      (𝓝 ((t:ℝ) * (atom true m t * atom true j s))) := by
  apply ((joint_limit true m t j s).const_mul (t:ℝ)).congr'
  filter_upwards [eventually_ge_atTop (3*(t+s+1))] with n hn
  unfold cellWeight joint prob avg
  rw [mul_expect]
  apply expect_congr rfl
  intro A hA
  by_cases ok : side true n m t A ∧ side true (n-1) j s (reflect n A)
  · have h := longest_eq (n := n) (A := A) (w := W n A) (q := t+s) (by omega)
      (mem_powerset.mp hA) (good n A (mem_powerset.mp hA)) (by rw [ok.1.2.2]; omega)
      (by rw [ok.2.2.2]; omega) (by dsimp [width]; omega)
    simp [ok,h,ok.1.2.2]
  · simp [ok]

theorem coreAvg_add_const (n k : ℕ) (x : ℝ) (f : Finset ℕ → ℝ) :
    coreAvg n k (fun B => x+f B)=x*coreAvg n k (fun _ => 1)+coreAvg n k f := by
  unfold coreAvg
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,add_div]
  simp
  ring

private theorem run_up {N n u w l : ℕ} {B : Finset ℕ} (pos : 0<N) (fit : u+N≤n) (h : run N B w l) :
    run n (shift u B) (2*u+w) l := by
  obtain ⟨room,filled⟩ := h
  constructor
  · unfold width at *
    omega
  · intro x lo hi
    rw [shift_sums]
    exact mem_image.mpr ⟨x-2*u,filled _ (by omega) (by omega),by omega⟩

private theorem longest_down {N n u w : ℕ} {B : Finset ℕ} (bs : B⊆range N) (b0 : 0∈B)
    (fit : u+N≤n) (h : longest n (shift u B) w) :
    2*u≤w ∧ longest N B (w-2*u) := by
  have np : 0<N := mem_range.mp (bs b0)
  have one : run N B 0 1 := by
    constructor
    · unfold width; omega
    · intro x _ hi
      have : x=0 := by omega
      exact this ▸ Finset.mem_add.mpr ⟨0,b0,0,b0,rfl⟩
  obtain ⟨l,⟨fit',fill⟩,big⟩ := h
  have lp : 1≤l := big _ _ (run_up np fit one)
  have first := fill w (by omega) (by omega)
  have last := fill (w+l-1) (by omega) (by omega)
  rw [shift_sums] at first last
  obtain ⟨x,_,ex⟩ := mem_image.mp first
  obtain ⟨y,hy,ey⟩ := mem_image.mp last
  change 2*u+x=w at ex
  change 2*u+y=w+l-1 at ey
  have bound := mem_range.mp (sums_in_range bs hy)
  refine ⟨by omega,l,⟨by omega,?_⟩,?_⟩
  · intro z lo hi
    have piece := fill (2*u+z) (by omega) (by omega)
    rw [shift_sums] at piece
    obtain ⟨v,hv,eq⟩ := mem_image.mp piece
    exact Nat.add_left_cancel eq ▸ hv
  · intro v j hh
    exact big _ _ (run_up np fit hh)

/-- The selector induced on a core of length N after u left and a−u right gaps. -/
def shiftSelector (W : ℕ → Finset ℕ → ℕ) (a u N : ℕ) (B : Finset ℕ) : ℕ :=
  if 0∈B then W (N+a) (shift u B)-2*u else W N B

theorem admissible_shift {W : ℕ → Finset ℕ → ℕ} (good : admissible W) {a u : ℕ} (ua : u≤a) :
    admissible (shiftSelector W a u) := by
  intro N B sub
  by_cases first : 0∈B
  · rw [shiftSelector,ite_eq_left first]
    have fit : u+N≤N+a := by omega
    exact (longest_down sub first fit (good _ _ (shift_sub sub fit))).2
  · rw [shiftSelector,ite_eq_right first]
    exact good N B sub

private theorem shiftSelector_eq {W : ℕ → Finset ℕ → ℕ} (good : admissible W) {n a u : ℕ}
    (an : a≤n) (ua : u≤a) {B : Finset ℕ} (sub : B⊆range (n-a)) (first : 0∈B) :
    W n (shift u B)=2*u+shiftSelector W a u (n-a) B := by
  have fit : u+(n-a)≤n := by omega
  have low := (longest_down sub first fit (good _ _ (shift_sub sub fit))).1
  rw [shiftSelector,ite_eq_left first,Nat.sub_add_cancel an]
  omega

theorem wordAvg_longest {n k : ℕ} (large : k+1<n) {W : ℕ → Finset ℕ → ℕ} (good : admissible W) :
    wordAvg n k (fun A => (W n A:ℝ)) =
      ∑ a∈range (k/2+1),∑ u∈range (a+1),
        ((2:ℝ)*u*coreAvg (n-a) (k-2*a) (fun _ => 1) +
          coreAvg (n-a) (k-2*a) (fun B => (shiftSelector W a u (n-a) B:ℝ)))/(2:ℝ)^a := by
  rw [wordAvg_split large]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro u hu
  rw [←coreAvg_add_const]
  congr 1
  apply coreAvg_congr
  intro B hB
  obtain ⟨sub,b0,_,_⟩ := mem_filter.mp hB
  have aa := mem_range.mp ha
  have uu := mem_range.mp hu
  exact_mod_cast shiftSelector_eq good (a:=a) (u:=u) (by omega) (by omega) (mem_powerset.mp sub) b0

theorem word_longest_limit {D H : ℕ → ℝ}
    (d : ∀ j, Tendsto (fun N => coreAvg N j (fun _ => 1)) atTop (𝓝 (D j)))
    (h : ∀ V, admissible V → ∀ j, Tendsto (fun N => coreAvg N j (fun A => (V N A:ℝ))) atTop (𝓝 (H j)))
    {W : ℕ → Finset ℕ → ℕ} (good : admissible W) (k : ℕ) :
    Tendsto (fun n => wordAvg n k (fun A => (W n A:ℝ))) atTop (𝓝 (marginMoment D H k)) := by
  have row (a : ℕ) : Tendsto (fun n =>
      ∑ u∈range (a+1),((2:ℝ)*u*coreAvg (n-a) (k-2*a) (fun _ => 1)+
        coreAvg (n-a) (k-2*a) (fun B => (shiftSelector W a u (n-a) B:ℝ)))/(2:ℝ)^a) atTop
      (𝓝 (marginWeight a*((a:ℝ)*D (k-2*a)+H (k-2*a)))) := by
    rw [←margin_row]
    apply tendsto_finsetSum
    intro u hu
    have ua : u≤a := by simpa [Nat.lt_succ_iff] using hu
    exact ((((d _).comp (tendsto_sub_atTop_nat a)).const_mul ((2:ℝ)*u)).add
      ((h _ (admissible_shift good ua) _).comp (tendsto_sub_atTop_nat a))).div_const _
  have add := tendsto_finsetSum (range (k/2+1)) (fun a _ => row a)
  apply add.congr'
  filter_upwards [eventually_gt_atTop (k+1)] with n hn
  exact (wordAvg_longest hn good).symm

theorem longest_mean_from_core {D H : ℕ → ℝ} (nd : ∀ j,0≤D j) (p0 : 0<D 0) (p1 : 0<D 1)
    (d : ∀ j, Tendsto (fun N => coreAvg N j (fun _ => 1)) atTop (𝓝 (D j)))
    (h : ∀ V, admissible V → ∀ j, Tendsto (fun N => coreAvg N j (fun A => (V N A:ℝ))) atTop (𝓝 (H j)))
    {W : ℕ → Finset ℕ → ℕ} (good : admissible W) (k : ℕ) :
    Tendsto (fun n => conditionalMean n k W) atTop (𝓝 (marginMoment D H k/marginMass D k)) := by
  have lim := (word_longest_limit d h good k).div (word_mass_limit d k) (marginMass_pos _ nd p0 p1 k).ne'
  exact lim.congr' (Eventually.of_forall fun n => (conditionalMean_eq n k _).symm)

/-- Every finite sumset admits a longest-interval selector. -/
theorem admissible_exists : ∃ W, admissible W := by
  have per (n : ℕ) (A : Finset ℕ) : ∃ w, longest n A w := by
    let possible := (range (width n+1)).filter fun l ↦ ∃ w, run n A w l
    have nonempty : possible.Nonempty := ⟨0,mem_filter.mpr ⟨by simp,0,by simp [run]⟩⟩
    obtain ⟨w,good⟩ := (mem_filter.mp (max'_mem possible nonempty)).2
    refine ⟨w,possible.max' nonempty,good,?_⟩
    intro v j h
    exact le_max' possible j (mem_filter.mpr ⟨mem_range.mpr (by have := h.1; omega),v,h⟩)
  exact ⟨fun n A ↦ (per n A).choose,fun n A _ ↦ (per n A).choose_spec⟩

theorem coreH_limit {W : ℕ → Finset ℕ → ℕ} (good : admissible W) (k : ℕ) :
    Tendsto (fun n ↦ coreAvg n k (fun A ↦ (W n A:ℝ))) atTop (𝓝 (coreH (atom true) k)) := by
  apply core_weight_limit (g := fun m t j s ↦ (t:ℝ)*(atom true m t*atom true j s))
  · exact cell_weight_limit good
  · intro n hn A hA
    refine ⟨Nat.cast_nonneg _,?_⟩
    have h := longest_bound hn hA (good n A hA)
    exact_mod_cast (show W n A ≤ 3*(extent n A+extent (n-1) (reflect n A)+1) by omega)

/-- The same limiting mean works for all tie rules and differs from k/2 by O(1). -/
theorem longest_location : ∃ e : ℕ → ℝ,
    (∀ W, admissible W → ∀ k, Tendsto (fun n ↦ conditionalMean n k W) atTop (𝓝 (e k))) ∧
    (∃ C : ℝ, ∀ k : ℕ, |e k-(k:ℝ)/2|≤C) ∧
    Tendsto (fun k : ℕ ↦ e k/k) atTop (𝓝 (1/2:ℝ)) := by
  let D := coreD (atom true)
  let H := coreH (atom true)
  have nd := coreD_nonneg (atom_nonneg true)
  have nh := coreH_nonneg (atom_nonneg true)
  obtain ⟨p0,p1⟩ := coreD_base_positive
  obtain ⟨sD,sH⟩ := core_summable (atom_nonneg true) atom_le_normWindow
    (fun m t h ↦ @atom_zero_of_lt m t true h)
  exact ⟨fun k ↦ marginMoment D H k / marginMass D k,
    fun _ hw ↦ longest_mean_from_core nd p0 p1 coreD_limit (fun _ h ↦ coreH_limit h) hw,
    margin_limit nd nh p0 p1 sD sH⟩

theorem longest_resolution : Conjecture := by
  intro W hw
  obtain ⟨e,finite,_,limit⟩ := longest_location
  exact ⟨e,finite W hw,1/2,by norm_num,limit⟩

/-- info: 'MissingSumFringes.admissible_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms admissible_exists

/-- info: 'MissingSumFringes.longest_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms longest_location

/-- info: 'MissingSumFringes.longest_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms longest_resolution

end MissingSumFringes
