module

public import conjectures.BarequetRectangularPolyomino.Tiles
import Mathlib.Tactic.FinCases

@[expose] public section
namespace BarequetRectangularPolyomino.Template

def sample (a b c : ℕ) (flip : Bool) :=
  compact (frame (a+b+c : ℕ) (if flip then (a+b : ℕ) else a)
    (if flip then a else (a+b : ℕ)))

private theorem old_clip (x k v : ℤ) (bound : -2≤k ∧ k≤2) (test : -1≤v ∧ v≤1) :
    clip 5 x+k=v ↔ x+k=v := by dsimp [clip]; omega

private theorem old_nonneg (x k : ℤ) (bound : -2≤k ∧ k≤2) :
    0≤clip 5 x+k ↔ 0≤x+k := by dsimp [clip]; omega

private theorem old_clip3 (x k : ℤ) (bound : -2≤k ∧ k≤2) :
    clip 3 (clip 5 x+k)=clip 3 (x+k) := by dsimp [clip]; omega

private theorem old_max (x a b : ℤ) (ha : -1≤a ∧ a≤1) (hb : -1≤b ∧ b≤1) :
    max (clip 5 x+a) b-max (clip 5 x) 0=max (x+a) b-max x 0 := by dsimp [clip]; omega

private theorem collapse_shift {f : Frame} {a b : ℤ} (ha : -1≤a ∧ a≤1) (hb : -1≤b ∧ b≤1)
    (r s : ℕ) :
    mark (shift (compact f) a b) r s=mark (shift f a b) r s ∧
    info (shift (compact f) a b) r s=info (shift f a b) r s ∧
    areaOff (shift (compact f) a b) s=areaOff (shift f a b) s := by
  simp (disch := omega) only [compact,shift,mark,inside,tile,info,border,areaOff,sub_eq_add_neg,
    add_assoc,ne_eq,old_clip,old_nonneg,old_clip3, and_self]

theorem view_compact {f : Frame} {x y : ℤ} (hx : -1≤x ∧ x≤3) (hy : -1≤y ∧ y≤3) :
    view (compact f) x y=view f x y := by
  have ha : -1≤x/3 ∧ x/3≤1:=by omega
  have hb : -1≤y/3 ∧ y/3≤1:=by omega
  obtain ⟨m,i,ar⟩:=collapse_shift (f:=f) ha hb (x%3).toNat (y%3).toNat
  dsimp only [view]
  rw [m,i,ar]
  simp only [compact,old_max _ _ _ ha hb]

private theorem check_compact (f : Frame) (r s : Fin 3) :
    localCheck (compact f) r s=localCheck f r s := by
  have ar : ((r.val:ℕ):ℤ)<3 := by exact_mod_cast r.isLt
  have as' : ((s.val:ℕ):ℤ)<3 := by exact_mod_cast s.isLt
  have eq0 (x:ℤ) : clip 5 x=0 ↔ x=0 := by dsimp [clip]; omega
  have nn (x:ℤ) : 0≤clip 5 x ↔ 0≤x := by dsimp [clip]; omega
  simp (disch := omega) only [localCheck,view_compact]
  simp only [inside,compact,ne_eq,eq0,nn]

set_option maxHeartbeats 800000 in
theorem checked_of_finite
    (finite_check : ∀ a b c : Fin 7, 5≤a.val+b.val+c.val → ∀ flip : Bool,
      ∀ r s : Fin 3, localCheck (sample a b c flip) r s) (u i j : ℕ) (lo : 5≤u) (hi : i≤u) (hj : j≤u) (r s : Fin 3) :
    localCheck (frame u i j) r s := by
  rw [← check_compact]
  rcases le_total i j with ij|ji
  · let a : Fin 7:=⟨min i 6,by omega⟩
    let b : Fin 7:=⟨min (j-i) 6,by omega⟩
    let c : Fin 7:=⟨min (u-j) 6,by omega⟩
    have eq : compact (frame u i j)=sample a b c false := by
      dsimp [a,b,c,sample,frame,compact,clip]
      congr 1 <;> omega
    rw [eq]
    exact finite_check _ _ _ (by dsimp [a,b,c]; omega) _ _ _
  · let a : Fin 7:=⟨min j 6,by omega⟩
    let b : Fin 7:=⟨min (i-j) 6,by omega⟩
    let c : Fin 7:=⟨min (u-i) 6,by omega⟩
    have eq : compact (frame u i j)=sample a b c true := by
      dsimp [a,b,c,sample,frame,compact,clip]
      congr 1 <;> omega
    rw [eq]
    exact finite_check _ _ _ (by dsimp [a,b,c]; omega) _ _ _

end BarequetRectangularPolyomino.Template

public section
namespace BarequetRectangularPolyomino.Template

private def Slice (a : Fin 7) : Prop :=
  ∀ b c : Fin 7, 5≤a.val+b.val+c.val → ∀ flip : Bool,
    ∀ r s : Fin 3, localCheck (sample a b c flip) r s

set_option maxHeartbeats 0
private theorem row0 : Slice 0 := by unfold Slice; decide +kernel
private theorem row1 : Slice 1 := by unfold Slice; decide +kernel
private theorem row2 : Slice 2 := by unfold Slice; decide +kernel
private theorem row3 : Slice 3 := by unfold Slice; decide +kernel
private theorem row4 : Slice 4 := by unfold Slice; decide +kernel
private theorem row5 : Slice 5 := by unfold Slice; decide +kernel
private theorem row6 : Slice 6 := by unfold Slice; decide +kernel

theorem checked (u i j : ℕ) (lo : 5≤u) (hi : i≤u) (hj : j≤u) (r s : Fin 3) :
    localCheck (frame u i j) r s := by
  apply checked_of_finite _ u i j lo hi hj r s
  intro a
  change Slice a
  fin_cases a
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6

end BarequetRectangularPolyomino.Template
