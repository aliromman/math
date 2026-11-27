module

public import conjectures.ErdosPurdyStraus.Normalized
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace ErdosPurdyStraus
open Set

/-- A supporting side separates the body from the half-plane behind it. -/
theorem supported {B : Set Plane} (cv : Convex ℝ B) (lo : baseLo ∈ B) (hi : baseHi ∈ B)
    (top : apex ∈ B) (edge : (0:Plane)∉interior B) : ∀ p∈B, 0≤p.1 := by
  have base {t : ℝ} (ht : -1/2≤t) (hu : t≤1/2) : (0,t) ∈ B := by
    have h := cv lo hi (a:=1/2-t) (b:=1/2+t) (by linarith) (by linarith) (by ring)
    convert h using 1
    ext <;> simp [baseLo,baseHi]; ring
  have rect : Ioo (1/4:ℝ) (1/2) ×ˢ Ioo (-1/8:ℝ) (1/8) ⊆ B := by
    rintro ⟨u,v⟩ ⟨hu,hv⟩
    change 1/4<u ∧ u<1/2 at hu
    change -1/8<v ∧ v<1/8 at hv
    have pos : 0<1-u := by linarith
    have anchor : (0,v/(1-u))∈B := base
      ((le_div_iff₀ pos).mpr (by linarith)) ((div_le_iff₀ pos).mpr (by linarith))
    have h := cv top anchor (a:=u) (b:=1-u) (by linarith) pos.le (by ring)
    convert h using 1
    ext <;> simp [apex]; field_simp
  have ii : (interior B).Nonempty := by
    have openRect : IsOpen (Ioo (1/4:ℝ) (1/2) ×ˢ Ioo (-1/8:ℝ) (1/8)) := isOpen_Ioo.prod isOpen_Ioo
    exact ⟨(3/8,0),interior_maximal rect openRect (by norm_num)⟩
  obtain ⟨f,hf,limit⟩ := geometric_hahn_banach_of_nonempty_interior_point cv edge ii
  have lim {z : Plane} (hz : z∈B) : f z≤0 := by simpa using limit z hz
  let e : Plane := (0,1)
  have split (p : Plane) : f p=p.1*f apex + p.2*f e := by
    have eq : p=p.1 • apex +p.2 • e := by ext <;> simp [apex,e]
    calc
      _ = f (p.1 • apex +p.2 • e) := congrArg f eq
      _ = _ := by rw [map_add,map_smul,map_smul]; rfl
  have hfl := lim lo
  have hfh := lim hi
  rw [split] at hfl hfh
  simp only [zero_mul,zero_add] at hfl hfh
  have ef : f e=0 := by linarith
  have af : f apex<0 := lt_of_le_of_ne (lim top) (by
    intro eq
    apply hf
    apply ContinuousLinearMap.ext
    intro p
    rw [split,eq,ef]
    simp)
  intro p hp
  have h := lim hp
  rw [split,ef,mul_zero,add_zero] at h
  exact nonneg_of_mul_nonpos_left h af

end ErdosPurdyStraus
