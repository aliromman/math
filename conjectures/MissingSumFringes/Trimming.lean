module

public import conjectures.MissingSumFringes.Endpoints
public import conjectures.MissingSumFringes.Margin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

def words (n k : ℕ) :=
  (range n).powerset.filter fun A => (missing (width n) A).card=k

def coreWords (n k : ℕ) :=
  (range n).powerset.filter fun A => 0∈A ∧ n-1∈A ∧ (missing (width n) A).card=k

noncomputable def wordAvg (n k : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  (∑ A∈words n k,f A)/(2:ℝ)^n

noncomputable def coreAvg (n k : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  (∑ A∈coreWords n k,f A)/(2:ℝ)^n

theorem coreAvg_eq (n k : ℕ) (f : Finset ℕ → ℝ) : coreAvg n k f =
    avg (range n) (fun A => if 0∈A ∧ n-1∈A ∧ (missing (width n) A).card=k then f A else 0) := by
  simp [coreAvg,coreWords,avg,expect_eq_sum_div_card,sum_filter]

theorem wordAvg_eq (n k : ℕ) (f : Finset ℕ → ℝ) : wordAvg n k f =
    avg (range n) (fun A => if (missing (width n) A).card=k then f A else 0) := by
  simp [wordAvg,words,avg,expect_eq_sum_div_card,sum_filter]

theorem conditionalMean_eq (n k : ℕ) (W : ℕ → Finset ℕ → ℕ) :
    conditionalMean n k W=wordAvg n k (fun A => (W n A:ℝ))/wordAvg n k (fun _ => 1) := by
  simp [conditionalMean,wordAvg,words,expect_eq_sum_div_card,div_div_div_cancel_right₀]

def shift (u : ℕ) (A : Finset ℕ) := A.image (fun x => u+x)

theorem shift_sub {n u N : ℕ} {B : Finset ℕ} (sub : B⊆range N) (fit : u+N≤n) :
    shift u B⊆range n := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  have := mem_range.mp (sub hx)
  apply mem_range.mpr
  omega

theorem shift_sums (u : ℕ) (B : Finset ℕ) : shift u B+shift u B=shift (2*u) (B+B) := by
  ext x
  simp only [shift,Finset.mem_add,mem_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩
    exact ⟨a+b,⟨a,ha,b,hb,rfl⟩,by omega⟩
  · rintro ⟨_,⟨a,ha,b,hb,rfl⟩,rfl⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,by omega⟩

theorem sums_in_range {A : Finset ℕ} {n : ℕ} (sub : A⊆range n) : A+A⊆range (width n) := by
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have aa := mem_range.mp (sub ha)
  have bb := mem_range.mp (sub hb)
  unfold width
  apply mem_range.mpr
  omega

theorem missing_shift {n u N : ℕ} {B : Finset ℕ} (small : B⊆range N) (pos : 0<N)
    (fit : u+N≤n) : (missing (width n) (shift u B)).card =
      2*(n-N)+(missing (width N) B).card := by
  unfold missing
  rw [card_sdiff_of_subset (sums_in_range (shift_sub small fit)),card_sdiff_of_subset (sums_in_range small),
    card_range,card_range,shift_sums,shift,card_image_of_injective _ (fun _ _ eq => Nat.add_left_cancel eq)]
  have c := (card_mono (sums_in_range small)).trans_eq (card_range _)
  unfold width at *
  omega

private theorem shift_inj {u : ℕ} {B D : Finset ℕ} (e : shift u B=shift u D) : B=D := by
  ext x
  have := Finset.ext_iff.mp e (u+x)
  simpa [shift] using this

private theorem parts_unique {u v N M : ℕ} {B D : Finset ℕ} (bs : B⊆range N) (ds : D⊆range M)
    (b0 : 0∈B) (d0 : 0∈D) (b1 : N-1∈B) (d1 : M-1∈D) (e : shift u B=shift v D) :
    u=v ∧ N=M ∧ B=D := by
  have bot (x : ℕ) (S : Finset ℕ) (z : 0∈S) : x∈shift x S := by
    exact mem_image.mpr ⟨0,z,Nat.add_zero _⟩
  have top (u v N M : ℕ) (B D : Finset ℕ) (ds : D⊆range M)
      (b1 : N-1∈B) (eq : shift u B=shift v D) : u+(N-1)<v+M := by
    have h : u+(N-1)∈shift v D := eq ▸ mem_image_of_mem (fun x => u+x) b1
    obtain ⟨z,hz,ez⟩ := mem_image.mp h
    have := mem_range.mp (ds hz)
    omega
  obtain ⟨i,_,eq1⟩ := mem_image.mp (e ▸ bot u B b0 : u∈shift v D)
  obtain ⟨j,_,eq2⟩ := mem_image.mp (e.symm ▸ bot v D d0 : v∈shift u B)
  change v+i=u at eq1
  change u+j=v at eq2
  obtain rfl : u=v := by omega
  have a := top _ _ _ _ _ _ ds b1 e
  have b := top _ _ _ _ _ _ bs d1 e.symm
  exact ⟨rfl,by omega,shift_inj e⟩

private theorem untrim {n k : ℕ} (large : k+1<n) {A : Finset ℕ} (hw : A∈words n k) :
    ∃ a≤k/2,∃ u≤a,∃ B∈coreWords (n-a) (k-2*a),shift u B=A := by
  obtain ⟨ha,hk⟩ := mem_filter.mp hw
  have sub := mem_powerset.mp ha
  have nonempty : A.Nonempty := by
    by_contra! no
    simp [no,missing,width] at hk
    omega
  let u := A.min' nonempty
  let top := A.max' nonempty
  let N := top-u+1
  let a := n-N
  let B := A.image (fun x => x-u)
  have left : u∈A := A.min'_mem _
  have right : top∈A := A.max'_mem _
  have lo (x : ℕ) (hx : x∈A) : u≤x := A.min'_le x hx
  have hi (x : ℕ) (hx : x∈A) : x≤top := A.le_max' x hx
  have ord := lo top right
  have fin := mem_range.mp (sub right)
  have fit : u+N≤n := by dsimp [N]; omega
  have pos : 0<N := Nat.zero_lt_succ _
  have base : n-a=N := by dsimp [a]; omega
  have core : B⊆range N := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have := hi y hy
    apply mem_range.mpr
    dsimp [N]
    omega
  have b0 : 0∈B := mem_image.mpr ⟨u,left,Nat.sub_self _⟩
  have b1 : N-1∈B := mem_image.mpr ⟨top,right,by simp [N]⟩
  have build : shift u B=A := by
    ext x
    simp only [shift,B,mem_image]
    constructor
    · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
      rwa [Nat.add_sub_of_le (lo y hy)]
    · intro hx
      exact ⟨_,⟨x,hx,rfl⟩,Nat.add_sub_of_le (lo x hx)⟩
  have gaps := missing_shift core pos fit
  rw [build,hk] at gaps
  change k=2*a+(missing (width N) B).card at gaps
  refine ⟨a,by omega,u,by dsimp [a]; omega,B,?_,build⟩
  rw [base]
  exact mem_filter.mpr ⟨mem_powerset.mpr core,b0,b1,by omega⟩

/-- Split a finite word at its first and last selected positions. -/
theorem word_sum_split {n k : ℕ} (large : k+1<n) (f : Finset ℕ → ℝ) :
    ∑ A∈words n k,f A=∑ a∈range (k/2+1),∑ u∈range (a+1),
      ∑ B∈coreWords (n-a) (k-2*a),f (shift u B) := by
  let rows := (range (k/2+1)).sigma (fun a => (range (a+1)).product (coreWords (n-a) (k-2*a)))
  have bij : (∑ z∈rows,f (shift z.2.1 z.2.2))=∑ A∈words n k,f A := by
    apply sum_bij (fun z _ => shift z.2.1 z.2.2)
    · rintro ⟨a,u,B⟩ hz
      change shift u B∈words n k
      have row : a∈range (k/2+1) ∧ (u,B)∈(range (a+1)).product (coreWords (n-a) (k-2*a)) := mem_sigma.mp hz
      obtain ⟨ha,hb⟩ := row
      obtain ⟨hu,hw⟩ := mem_product.mp hb
      obtain ⟨sub,_,_,hc⟩ := mem_filter.mp hw
      simp only [mem_range] at ha hu
      have fit : u+(n-a)≤n := by omega
      have s := mem_powerset.mp sub
      have cnt := missing_shift (B:=B) (N:=n-a) s (by omega) fit
      rw [hc] at cnt
      exact mem_filter.mpr ⟨mem_powerset.mpr (shift_sub s fit),by omega⟩
    · rintro ⟨a,u,B⟩ hB ⟨b,v,D⟩ hD e
      change shift u B=shift v D at e
      have br : a∈range (k/2+1) ∧ (u,B)∈(range (a+1)).product (coreWords (n-a) (k-2*a)) := mem_sigma.mp hB
      obtain ⟨ha,hbu⟩ := br
      obtain ⟨_,hb⟩ := mem_product.mp hbu
      obtain ⟨i,b0,b1,_⟩ := mem_filter.mp hb
      have dr : b∈range (k/2+1) ∧ (v,D)∈(range (b+1)).product (coreWords (n-b) (k-2*b)) := mem_sigma.mp hD
      obtain ⟨hd,hdv⟩ := dr
      obtain ⟨_,hd'⟩ := mem_product.mp hdv
      obtain ⟨j,d0,d1,_⟩ := mem_filter.mp hd'
      obtain ⟨rfl,eq,rfl⟩ := parts_unique (mem_powerset.mp i) (mem_powerset.mp j) b0 d0 b1 d1 e
      simp only [mem_range] at ha hd
      have : a=b := by omega
      subst b
      rfl
    · intro A ha
      obtain ⟨a,ak,u,ua,B,bc,sh⟩ := untrim large ha
      exact ⟨⟨a,u,B⟩,mem_sigma.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ak),
        mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ua),bc⟩⟩,sh⟩
    · intros; rfl
  rw [←bij]
  simp only [rows,sum_sigma]
  apply sum_congr rfl
  intro a _
  exact sum_product _ _ (fun z => f (shift z.1 z.2))

theorem wordAvg_split {n k : ℕ} (large : k+1<n) (f : Finset ℕ → ℝ) :
    wordAvg n k f = ∑ a∈range (k/2+1),∑ u∈range (a+1),
      coreAvg (n-a) (k-2*a) (fun B => f (shift u B))/(2:ℝ)^a := by
  unfold wordAvg coreAvg
  rw [word_sum_split large,sum_div]
  apply sum_congr rfl
  intro a ha
  have an : a≤n := by have := mem_range.mp ha; omega
  rw [sum_div]
  apply sum_congr rfl
  intro u _
  rw [div_div,←pow_add,Nat.sub_add_cancel an]

theorem coreAvg_congr {n k : ℕ} {f g : Finset ℕ → ℝ} (e : ∀ B∈coreWords n k,f B=g B) :
    coreAvg n k f=coreAvg n k g := by unfold coreAvg; rw [sum_congr rfl e]

/-- Summing the 2u term over positions u=0,…,a gives mean a. -/
theorem margin_row (a : ℕ) (D H : ℝ) :
    (∑ u∈range (a+1),((2:ℝ)*u*D+H)/(2:ℝ)^a)=marginWeight a*((a:ℝ)*D+H) := by
  have tri := sum_range_id_mul_two (a+1)
  rw [Nat.add_sub_cancel] at tri
  have tr : (∑ u∈range (a+1),(u:ℝ))*2=((a:ℝ)+1)*a := by
    have cast := congrArg (fun x : ℕ => (x:ℝ)) tri
    push_cast at cast
    exact cast
  rw [←sum_div,sum_add_distrib,←sum_mul,←mul_sum,sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  unfold marginWeight
  field_simp
  nlinarith only [congrArg (fun z => z*D) tr]

theorem wordAvg_mass {n k : ℕ} (large : k+1<n) : wordAvg n k (fun _ => 1) =
    ∑ a∈range (k/2+1),marginWeight a*coreAvg (n-a) (k-2*a) (fun _ => 1) := by
  rw [wordAvg_split large]
  apply sum_congr rfl
  intro a _
  rw [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,marginWeight]
  ring

/-- The finite unnormalized mass converges after the empty margins are restored. -/
theorem word_mass_limit {D : ℕ → ℝ}
    (d : ∀ j, Tendsto (fun N => coreAvg N j (fun _ => 1)) atTop (𝓝 (D j))) (k : ℕ) :
    Tendsto (fun n => wordAvg n k (fun _ => 1)) atTop (𝓝 (marginMass D k)) := by
  have add := tendsto_finsetSum (range (k/2+1)) (fun a _ =>
    ((d (k-2*a)).comp (tendsto_sub_atTop_nat a)).const_mul (marginWeight a))
  apply add.congr'
  filter_upwards [eventually_gt_atTop (k+1)] with n hn
  exact (wordAvg_mass hn).symm

end MissingSumFringes
