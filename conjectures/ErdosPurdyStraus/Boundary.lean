module

public import conjectures.ErdosPurdyStraus.Statement
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.Linarith

public section
namespace ErdosPurdyStraus
open Set Filter
open scoped Topology

/-- A bound on an affine function along a vertical section follows from the two boundary endpoints. -/
private theorem on_section {K : Set Plane} (h : IsCompact K) {p : Plane} (hp : p∈K) (a b M : ℝ)
    (bound : ∀ y, (p.1,y)∈frontier K → |a*y+b|≤M) : |a*p.2+b|≤M := by
  let F := Prod.mk p.1 ⁻¹' K
  have ne : F.Nonempty := ⟨p.2,hp⟩
  have sub : F⊆Prod.snd '' K := fun y hy ↦ ⟨(p.1,y),hy,rfl⟩
  have f := h.image continuous_snd
  have closed : IsClosed F := h.isClosed.preimage (continuous_const.prodMk continuous_id)
  have lo := f.bddBelow.mono sub
  have hi := f.bddAbove.mono sub
  have pLo : (p.1,sInf F)∈frontier K := by
    apply (mem_frontier_iff_notMem_interior (s:=K) (x:=(p.1,sInf F)) (closed.csInf_mem ne lo : (p.1,sInf F)∈K)).mpr
    intro inK
    have nb : F∈𝓝 (sInf F) := (continuous_const.prodMk continuous_id).continuousAt (mem_interior_iff_mem_nhds.mp inK)
    obtain ⟨y,hy,ly⟩ := (((Filter.Eventually.filter_mono nhdsWithin_le_nhds nb): ∀ᶠ y in 𝓝[<] (sInf F), y∈F).and self_mem_nhdsWithin).exists
    exact (not_lt_of_ge (csInf_le lo hy)) ly
  have pHi : (p.1,sSup F)∈frontier K := by
    apply (mem_frontier_iff_notMem_interior (s:=K) (x:=(p.1,sSup F)) (closed.csSup_mem ne hi : (p.1,sSup F)∈K)).mpr
    intro inK
    have nb : F∈𝓝 (sSup F) := (continuous_const.prodMk continuous_id).continuousAt (mem_interior_iff_mem_nhds.mp inK)
    obtain ⟨y,hy,ly⟩ := (((Filter.Eventually.filter_mono nhdsWithin_le_nhds nb): ∀ᶠ y in 𝓝[>] (sSup F), y∈F).and self_mem_nhdsWithin).exists
    exact (not_lt_of_ge (le_csSup hi hy)) ly
  have l := abs_le.mp (bound _ pLo)
  have u := abs_le.mp (bound _ pHi)
  have ylo := csInf_le lo (show p.2∈F from hp)
  have yhi := le_csSup hi (show p.2∈F from hp)
  apply abs_le.mpr
  rcases le_total 0 a with pos|neg
  · constructor <;> linarith only [l.1,u.2,mul_le_mul_of_nonneg_left ylo pos,mul_le_mul_of_nonneg_left yhi pos]
  · constructor <;> linarith only [u.1,l.2,mul_le_mul_of_nonpos_left ylo neg,mul_le_mul_of_nonpos_left yhi neg]

private theorem boundary_vertex {K : Set Plane} (h : IsCompact K) {p : Plane} (hp : p∈K) (q r : Plane) (M : ℝ)
    (bound : ∀ a∈frontier K,|cross a q r|≤M) : |cross p q r|≤M := by
  have e (y : ℝ) : cross (p.1,y) q r=(r.1-q.1)*y+((q.1-p.1)*r.2-(r.1-p.1)*q.2) := by unfold cross; ring
  have line := on_section h hp (r.1-q.1) ((q.1-p.1)*r.2-(r.1-p.1)*q.2) M (fun y hy ↦ e y ▸ bound _ hy)
  rwa [←e p.2] at line

/-- Taking the largest triangle among boundary triples gives the same bound as allowing all points. -/
theorem boundary_bound_iff {K : Set Plane} (h : IsCompact K) (M : ℝ) :
    (∀ p∈frontier K, ∀ q∈frontier K, ∀ r∈frontier K, |cross p q r|≤M) ↔
    (∀ p∈K, ∀ q∈K, ∀ r∈K, |cross p q r|≤M) := by
  have cycle (p q r : Plane) : cross q r p=cross p q r := by unfold cross; ring
  constructor
  · intro B p hp q hq r hr
    apply boundary_vertex h hp q r
    intro a ha
    rw [←cycle a q r]
    apply boundary_vertex h hq r a
    intro b hb
    rw [←cycle b r a]
    apply boundary_vertex h hr a b
    intro c hc
    simpa only [cycle c a b] using B a ha b hb c hc
  · intro B p hp q hq r hr
    have sub : frontier K⊆K := frontier_subset_iff_isClosed.mpr h.isClosed
    exact B p (sub hp) q (sub hq) r (sub hr)

end ErdosPurdyStraus
