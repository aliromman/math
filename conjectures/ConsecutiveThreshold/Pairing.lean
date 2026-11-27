module

public import conjectures.ConsecutiveThreshold.Series

@[expose] public section
namespace ConsecutiveThreshold
open Finset
open scoped BigOperators

/-- A quarter of the digits whose doubled capacities occur outside this interval. -/
def slice (n : ℕ) : Finset (Fin n) :=
  univ.filter fun i => n-2*(n/4)≤i.val ∧ i.val<n-n/4

private def partner {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n-2*(n-i.val),by have := i.isLt; omega⟩

private theorem partner_capacity {n : ℕ} {i : Fin n} (hi : i∈slice n) :
    n-(partner i).val=2*(n-i.val) := by
  have bounds := (mem_filter.mp hi).2
  change n-(n-2*(n-i.val))=_
  omega

private noncomputable def bitFactor (q : ℝ) (d : ℕ) : Series :=
  1+AddMonoidAlgebra.single (d:ℤ) (q^d)

private theorem geom_double (q : ℝ) (d : ℕ) :
    geom q (2*d)=geom q d*bitFactor q d := by
  unfold geom bitFactor
  rw [two_mul,sum_range_add,mul_add,mul_one,sum_mul]
  congr 1
  apply sum_congr rfl
  intro j _
  simp [AddMonoidAlgebra.single_mul_single,pow_add,mul_comm]

private theorem bit_positive {q : ℝ} (hq : 0≤q) (d : ℕ) :
    positiveSeries (bitFactor q d) := by
  intro z
  change 0≤(1:Series).coeff z + (Finsupp.single (d:ℤ) (q^d)) z
  apply add_nonneg (positive_one z)
  rw [Finsupp.single_apply]
  split
  · exact pow_nonneg hq _
  · exact le_rfl

/-- The untouched digits contain a convolution factor equal to the tested digits. -/
theorem paired_residual (n : ℕ) {q : ℝ} (hq : 0≤q) : ∃ Y : Series, positiveSeries Y ∧
    (∏ i ∈ (slice n)ᶜ,geom q (n-i.val))=(∏ i∈slice n,geom q (n-i.val))*Y := by
  let S := slice n
  let D := S.image partner
  have contained : D⊆Sᶜ := by
    rintro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    apply mem_compl.mpr
    intro impossible
    have h₁ := (mem_filter.mp hi).2
    have h₂ := (mem_filter.mp impossible).2
    simp only [partner] at h₂
    omega
  have inj : Set.InjOn partner (↑S : Set (Fin n)) := by
    intro i hi j hj eq
    have pi := partner_capacity hi
    have pj := partner_capacity hj
    rw [eq] at pi
    exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  let unused := ∏ i ∈ Sᶜ \ D,geom q (n-i.val)
  let bits := ∏ i ∈ S,bitFactor q (n-i.val)
  refine ⟨unused*bits,positive_mul (positive_prod _ _ fun i _ => positive_geom hq _)
    (positive_prod _ _ fun i _ => bit_positive hq _),?_⟩
  have pairs : (∏ i∈D,geom q (n-i.val))=(∏ i∈S,geom q (n-i.val))*bits := by
    rw [show D=S.image partner from rfl,prod_image inj]
    unfold bits
    rw [←prod_mul_distrib]
    exact prod_congr rfl fun i hi => by rw [partner_capacity hi,geom_double]
  change (∏ i∈Sᶜ,geom q (n-i.val))=_
  rw [← prod_sdiff contained,pairs]
  change unused*((∏ i∈S,geom q (n-i.val))*bits)=_*(unused*bits)
  ac_rfl

end ConsecutiveThreshold
