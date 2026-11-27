module

public import conjectures.SidonSetSystems.Probes
public import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

@[expose] public section
namespace SidonSetSystems
open Finset Filter
open scoped Classical
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem high_attained {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι→ℚ) : ∃ i, f i=high f := by
  obtain ⟨i,_,h⟩ := Finset.exists_mem_eq_sup' univ_nonempty f
  exact ⟨i,h.symm⟩

namespace Figure
variable (A : Figure V)

theorem support_attained (f : Probe V) : ∃ x∈A.sites, f.read x=A.support f := by
  obtain ⟨i,h⟩ := high_attained (fun i : A.sites => f.read i)
  exact ⟨i,i.2,h⟩

theorem read_le_support (f : Probe V) {x : V} (hx : x∈A.sites) : f.read x≤A.support f :=
  le_high (fun i : A.sites => f.read i) ⟨x,hx⟩

theorem support_constant {f : Probe V} {t : ℚ} (h : ∀ x∈A.sites, f.read x=t) : A.support f=t := by
  obtain ⟨x,hx,eq⟩ := A.support_attained f
  exact eq.symm.trans (h x hx)

theorem support_offset {f g : Probe V} {t : ℚ} (h : ∀ x∈A.sites, f.read x=g.read x+t) :
    A.support f=A.support g+t := by
  obtain ⟨x,hx,ex⟩ := A.support_attained f
  obtain ⟨y,hy,ey⟩ := A.support_attained g
  exact le_antisymm (by linarith [h x hx,A.read_le_support g hx])
    (by linarith [h y hy,A.read_le_support f hy])

@[simp] theorem support_zero : A.support 0=0 := A.support_constant (by simp)

noncomputable def face (f : Probe V) : Figure V where
  sites := A.sites.filter fun x => f.read x=A.support f
  exists_site := by
    obtain ⟨x,hx,he⟩ := A.support_attained f
    exact ⟨x,mem_filter.mpr ⟨hx,he⟩⟩

theorem face_subset (f : Probe V) : (A.face f).sites⊆A.sites := filter_subset _ _

theorem face_of_constant {f : Probe V} {t : ℚ} (h : ∀ x∈A.sites, f.read x=t) : A.face f=A := by
  have hsup := A.support_constant h
  apply Figure.ext
  exact filter_eq_self.mpr (fun x hx => (h x hx).trans hsup.symm)

theorem free_of_subset {B : Figure V} (h : A.Free) (sub : B.sites⊆A.sites) : B.Free := by
  classical
  intro w
  let w' (x : A.sites) : ℚ := if mem : x.val∈B.sites then w ⟨x,mem⟩ else 0
  obtain ⟨f,hf⟩ := h w'
  exact ⟨f,fun x => by simpa [w',x.2] using hf ⟨x,sub x.2⟩⟩

@[simp] theorem read_smul (a : ℚ) (f : Probe V) (x : V) : (a • f).read x=a*f.read x := by
  simp [Probe.read,mul_add]

/-- For large weights, maximize the first reading before using the second one. -/
theorem leading (p q : Probe V) : ∀ᶠ n : ℕ in atTop,
    A.support ((n:ℚ) • p+q)=n*A.support p+(A.face p).support q := by
  classical
  have each (x : A.sites) : ∀ᶠ n : ℕ in atTop,
      (n:ℚ)*p.read x+q.read x ≤ n*A.support p+(A.face p).support q := by
    rcases lt_or_eq_of_le (A.read_le_support p x.2) with h|h
    · obtain ⟨N,hN⟩ := exists_nat_gt ((q.read x-(A.face p).support q)/(A.support p-p.read x))
      filter_upwards [eventually_ge_atTop N] with n hn
      have l : ((N:ℕ):ℚ)≤n := by exact_mod_cast hn
      have z := (div_lt_iff₀ (sub_pos.mpr h)).mp (hN.trans_le l)
      linarith
    · have help := (A.face p).read_le_support q (mem_filter.mpr ⟨x.2,h⟩)
      filter_upwards with n
      rw [h]
      exact add_le_add_right help _
  filter_upwards [eventually_all.mpr each] with n many
  obtain ⟨x,hx,ex⟩ := (A.face p).support_attained q
  obtain ⟨y,hy,ey⟩ := A.support_attained ((n:ℚ) • p+q)
  have m := many ⟨y,hy⟩
  obtain ⟨hx,px⟩ := mem_filter.mp hx
  have low := A.read_le_support ((n:ℚ) • p+q) hx
  simp only [Probe.read_add,read_smul] at ey low
  rw [px,ex] at low
  exact le_antisymm (ey.symm.trans_le m) low

end Figure
end SidonSetSystems
