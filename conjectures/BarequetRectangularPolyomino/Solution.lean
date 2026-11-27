module

public import conjectures.BarequetRectangularPolyomino.Geometry
public import conjectures.BarequetRectangularPolyomino.Certificate

public section
namespace BarequetRectangularPolyomino
open Template

/-- The two side lengths differ by two at every order above three. -/
theorem rectangular_minimum (t : ℕ) (ht : 3<t) : ∃ P : Cells,
    Admissible t (3*t+4) (3*t+2) P ∧ P.card=6*(t+1)^2-1 ∧ Minimum t P := by
  let u:=t+1
  have u5 : 5≤u := by dsimp [u]; omega
  have good : RegularGrid u:=fun _ _ hx hy => laws_of_check checked u5 hx hy
  have n:=(cells_card u5 good)
  refine ⟨region u,?_,n,?_⟩
  · have w : 3*t+4=3*u+1 := by dsimp [u]; omega
    have h : 3*t+2=3*u-1 := by dsimp [u]; omega
    rw [w,h]
    refine ⟨shape_connected u5 good,by omega,by omega,?_,?_,?_⟩
    · intro p hp; have b:=occupied_in (mem_region.mp hp); omega
    · intro y hy; rw [row_runs u5 good y hy]
    · intro x hx; rw [col_runs u5 good x hx]
  · intro w h Q ok
    rw [n]
    exact area_lower (by omega) ok

theorem resolution : Existence := by
  obtain ⟨P,ok,_,least⟩:=rectangular_minimum 4 (by decide)
  exact ⟨4,16,14,P,by decide,by decide,ok,least⟩

/-- info: 'BarequetRectangularPolyomino.rectangular_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rectangular_minimum

/-- info: 'BarequetRectangularPolyomino.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BarequetRectangularPolyomino
