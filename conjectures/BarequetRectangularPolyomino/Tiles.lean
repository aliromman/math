module

public import conjectures.BarequetRectangularPolyomino.LowerBound

@[expose] public section
namespace BarequetRectangularPolyomino
namespace Template
open Finset

/-- Distances to the four sides in block coordinates, and the signed distance to the diagonal. -/
structure Frame where
  x : ℤ
  xr : ℤ
  y : ℤ
  yr : ℤ
  d : ℤ
  deriving DecidableEq, Repr

def frame (u i j : ℤ) : Frame := ⟨i,u-i,j,u-1-j,i-j⟩
def shift (f : Frame) (a b : ℤ) : Frame := ⟨f.x+a,f.xr-a,f.y+b,f.yr-b,f.d+a-b⟩
def clip (m n : ℤ) := max (-m) (min m n)
def compact (f : Frame) : Frame :=
  ⟨clip 5 f.x,clip 5 f.xr,clip 5 f.y,clip 5 f.yr,clip 5 f.d⟩

def inside (f : Frame) (r s : ℕ) : Bool := decide
  (0≤f.x ∧ 0≤f.xr ∧ 0≤f.y ∧ 0≤f.yr ∧ (f.xr≠0 ∨ r=0) ∧ (f.yr≠0 ∨ s<2))

/-- Occupancy in one three-by-three block. Its low bit is the lower left cell. -/
def tile (f : Frame) : ℕ :=
  if f.xr=0 then (if f.yr=0 then 73 else 65)
  else if f.x=0 then (if f.y=0 then 286 else if f.y=1 then 303 else 378)
  else if f.yr=0 then (if f.d=0 then 286 else if f.d= -1 then 495 else 221)
  else if f.d=0 then 286 else if f.d=1 then 125 else if f.d= -1 then 471 else 245

def mark (f : Frame) (r s : ℕ) : Bool := inside f r s && (tile f).testBit (3*s+r)

def border (a b : ℤ) : ℕ :=
  if a=0 then 0 else if a=1 then 1 else if b=0 then 4 else if b=1 then 3 else 2

def masks : Array Nat := #[
  255140228282379342167387259704, 213959369742512124827040576568, 215467615382907134889324823731,
  215506774573949223882245915812, 253902288242985840308469220152, 255062807445080442667094623415,
  255101511960774042279265551160, 255139774640013017520702866227, 255139774640013017520702866232,
  255140216476467641891437003703, 255140228282307266981163287352, 255140228282379342141617455924,
  255140228282379342167387259703, 255140237727121318129589928887, 293845206792112927919201420088,
  294734482412865072093965959992, 294773641751481113693743334182, 294773661811885235420553982775,
  294773661816893219512939823928, 294773661820283887698692414018, 294773661829649123113596273344,
  294773661829649123114133144256, 294773661829649123371390780084, 294773661829651338888394423096,
  371874133782785484850034488120, 374001349442823009299681362867, 374040508633865098309782324136,
  382710925935625299283272123192, 459461091796622842961755511362, 459461245863829364176133442104,
  463174911913900271232712622784, 463174911913900271233249493696, 463176123791487308769055654584,
  463176123791487308769592525496]

def ids : Array Nat := #[
  0, 0, 0, 14, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 27, 27, 0, 0, 0, 0, 0,
  27, 4, 0, 0, 0, 0, 0, 18, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 32, 33, 29, 0, 0, 0, 0, 32, 33, 0, 0, 0, 0, 0,
  22, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 0, 0, 0, 0, 3, 2, 2,
  30, 31, 28, 24, 26, 25, 25, 30, 31, 28, 24, 0, 0, 0, 20, 21, 19, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 8, 15, 0, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 0, 25, 25,
  0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6,
  0, 0, 0, 0, 0, 12, 5, 0, 0, 0, 0, 0, 12, 9, 0, 0, 0, 0, 0, 9, 12,
  0, 0, 0, 0, 13, 0, 0]

def info (f : Frame) (r s : ℕ) : ℕ :=
  let k := (5*border f.x f.xr+border f.y f.yr)*7+(clip 3 f.d+3).toNat
  (masks[ids[k]!]! >>> (11*(3*s+r))) % 2048

structure Value where
  occupied : Bool
  row : ℤ
  col : ℤ
  cells : ℤ
  rank : ℤ
  area : ℤ
  deriving DecidableEq, Repr

def areaOff (f : Frame) (s : ℕ) : ℤ :=
  if f.yr=0 ∧ s=2 then 1 else if f.y=0 then s else if f.y=1 then
    (if s=0 then -1 else s) else (s:ℤ)-2

/-- Read a cell relative to the current block. Counters omit their common origin. -/
def view (f : Frame) (x y : ℤ) : Value :=
  let a:=x/3
  let b:=y/3
  let r:=(x%3).toNat
  let s:=(y%3).toNat
  let g:=shift f a b
  let w:=info g r s
  ⟨mark g r s,a+(w/32%4:ℕ)-1,b+(w/128%2:ℕ),2*a+(w/256:ℕ)-3,
    12*(max (f.d+a) b-max f.d 0)+(w%32:ℕ),2*b+areaOff g s⟩

def localCheck (f : Frame) (r s : ℕ) : Bool := Id.run do
  let q:=view f r s
  let w:=view f ((r:ℤ)-1) s
  let e:=view f ((r:ℤ)+1) s
  let n:=view f r ((s:ℤ)+1)
  let v:=view f r ((s:ℤ)-1)
  let root := f.x=0 ∧ f.y=0 ∧ r=1 ∧ s=0
  let x0 := f.x=0 ∧ r=0
  let y0 := f.y=0 ∧ s=0
  let lastX := f.xr=0 ∧ r=0
  let lastY := f.yr=0 ∧ s=1
  return !inside f r s || decide (
    e.row=q.row+(if q.occupied && !w.occupied then 1 else 0) ∧
    n.col=q.col+(if q.occupied && !v.occupied then 1 else 0) ∧
    e.cells=q.cells+(if q.occupied then 1 else 0) ∧
    (x0 → q.row=0 ∧ q.cells=0) ∧ (y0 → q.col=0) ∧
    (lastX → e.row=0 ∧ e.cells=n.area-q.area) ∧ (lastY → n.col=1) ∧
    (q.occupied → root ∨ (w.occupied ∧ w.rank<q.rank) ∨ (e.occupied ∧ e.rank<q.rank) ∨
      (v.occupied ∧ v.rank<q.rank) ∨ (n.occupied ∧ n.rank<q.rank)))

end Template
end BarequetRectangularPolyomino

@[expose] public section
namespace BarequetRectangularPolyomino.Template

def read (u x y : ℤ) : Value :=
  let i:=x/3
  let j:=y/3
  let r:=(x%3).toNat
  let s:=(y%3).toNat
  let f:=frame u i j
  let w:=info f r s
  ⟨mark f r s,i+(w/32%4:ℕ)-1,j+(w/128%2:ℕ),2*i+(w/256:ℕ)-3,
    12*max i j+(w%32:ℕ),2*j+areaOff f s⟩

def translate (i j : ℤ) (v : Value) : Value :=
  ⟨v.occupied,i+v.row,j+v.col,2*i+v.cells,12*max i j+v.rank,2*j+v.area⟩

theorem read_eq (u i j x y : ℤ) :
    read u (3*i+x) (3*j+y)=translate i j (view (frame u i j) x y) := by
  dsimp only [read,translate,view]
  rw [show (3*i+x)/3=i+x/3 by omega,show (3*j+y)/3=j+y/3 by omega,
    show (3*i+x)%3=x%3 by omega,show (3*j+y)%3=y%3 by omega]
  have sh : frame u (i+x/3) (j+y/3)=shift (frame u i j) (x/3) (y/3) := by
    dsimp [frame,shift]; congr 1 <;> omega
  rw [sh]
  congr 1 <;> dsimp only [frame] <;> omega

end BarequetRectangularPolyomino.Template
