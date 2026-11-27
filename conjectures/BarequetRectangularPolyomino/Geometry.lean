module

public import conjectures.BarequetRectangularPolyomino.Tiles
import Mathlib.Data.Finset.Max

@[expose] public section
namespace BarequetRectangularPolyomino.Template

structure Laws (u x y : ℤ) : Prop where
  row : (read u (x+1) y).row=(read u x y).row+
    (if (read u x y).occupied && !(read u (x-1) y).occupied then 1 else 0)
  col : (read u x (y+1)).col=(read u x y).col+
    (if (read u x y).occupied && !(read u x (y-1)).occupied then 1 else 0)
  cells : (read u (x+1) y).cells=(read u x y).cells+(if (read u x y).occupied then 1 else 0)
  row0 : x=0 → (read u x y).row=0 ∧ (read u x y).cells=0
  col0 : y=0 → (read u x y).col=0
  endX : x=3*u → (read u (x+1) y).row=u ∧
    (read u (x+1) y).cells=2*u+(read u x (y+1)).area-(read u x y).area
  endY : y=3*u-2 → (read u x (y+1)).col=u
  path : (read u x y).occupied → (x=1 ∧ y=0) ∨
    ((read u (x-1) y).occupied ∧ (read u (x-1) y).rank<(read u x y).rank) ∨
    ((read u (x+1) y).occupied ∧ (read u (x+1) y).rank<(read u x y).rank) ∨
    ((read u x (y-1)).occupied ∧ (read u x (y-1)).rank<(read u x y).rank) ∨
    ((read u x (y+1)).occupied ∧ (read u x (y+1)).rank<(read u x y).rank)

theorem laws_of_check {u x y : ℕ}
    (checked : ∀ u i j : ℕ, 5≤u → i≤u → j≤u → ∀ r s : Fin 3, localCheck (frame u i j) r s) (u5 : 5≤u) (xB : x<3*u+1) (yB : y<3*u-1) : Laws u x y := by
  let i:=x/3
  let j:=y/3
  let r : Fin 3:=⟨x%3,by omega⟩
  let s : Fin 3:=⟨y%3,by omega⟩
  let f:=frame u i j
  let q:=view f r s
  let w:=view f ((r:ℤ)-1) s
  let e:=view f ((r:ℤ)+1) s
  let n:=view f r ((s:ℤ)+1)
  let v:=view f r ((s:ℤ)-1)
  have xi : (x:ℤ)=3*(i:ℤ)+(r:ℤ) := by dsimp [i,r]; omega
  have yi : (y:ℤ)=3*(j:ℤ)+(s:ℤ) := by dsimp [j,s]; omega
  have inb : inside f r s := by simp [inside,f,frame,i,j,r,s]; omega
  have checks := checked u i j u5 (by dsimp [i]; omega) (by dsimp [j]; omega) r s
  change localCheck f r s at checks
  simp only [localCheck,inb,Bool.not_true,Bool.false_or] at checks
  have data:=of_decide_eq_true checks
  change e.row=q.row+_ ∧ n.col=q.col+_ ∧ e.cells=q.cells+_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at data
  obtain ⟨hr,hc,he,h0r,h0c,hlr,hlc,path⟩:=data
  have Q : read u x y=translate i j q := by rw [xi,yi]; exact read_eq ..
  have W : read u ((x:ℤ)-1) y=translate i j w := by
    rw [xi,yi,show 3*(i:ℤ)+(r:ℤ)-1=3*(i:ℤ)+((r:ℤ)-1) by omega]; exact read_eq ..
  have E : read u ((x:ℤ)+1) y=translate i j e := by
    rw [xi,yi,add_assoc]; exact read_eq ..
  have N : read u x ((y:ℤ)+1)=translate i j n := by
    rw [xi,yi,add_assoc]; exact read_eq ..
  have V : read u x ((y:ℤ)-1)=translate i j v := by
    rw [xi,yi,show 3*(j:ℤ)+(s:ℤ)-1=3*(j:ℤ)+((s:ℤ)-1) by omega]; exact read_eq ..
  constructor
  · simpa only [E,Q,W,translate,add_assoc,add_right_inj] using congrArg (fun z : ℤ => (i:ℤ)+z) hr
  · simpa only [N,Q,V,translate,add_assoc,add_right_inj] using congrArg (fun z : ℤ => (j:ℤ)+z) hc
  · simpa only [E,Q,translate,add_assoc] using congrArg (fun z : ℤ => 2*(i:ℤ)+z) he
  · intro x0
    have ix : i=0 := by dsimp [i]; omega
    have z:=h0r (show f.x=0 ∧ r.val=0 by dsimp [f,frame,i,r]; omega)
    simpa [Q,translate,ix] using z
  · intro y0
    have jy : j=0 := by dsimp [j]; omega
    have z:=h0c (show f.y=0 ∧ s.val=0 by dsimp [f,frame,j,s]; omega)
    simpa [Q,translate,jy] using z
  · intro xend
    have iu : i=u := by dsimp [i]; omega
    obtain ⟨a,b⟩:=hlr (show f.xr=0 ∧ r.val=0 by dsimp [f,frame,i,r]; omega)
    change e.row=0 at a
    change e.cells=n.area-q.area at b
    simp only [E,N,Q,translate]
    constructor <;> omega
  · intro yend
    have b:=hlc (show f.yr=0 ∧ s.val=1 by dsimp [f,frame,j,s]; omega)
    change n.col=1 at b
    simp only [N,translate]
    have jj : (j:ℤ)+1=u := by dsimp [j]; omega
    omega
  · simp only [W,E,N,V,Q,translate,add_lt_add_iff_left]
    intro occupied
    have h:=path occupied
    rcases h with root|other
    · left; dsimp [f,frame,i,j,r,s] at root; omega
    · exact Or.inr other

end BarequetRectangularPolyomino.Template

@[expose] public section
namespace BarequetRectangularPolyomino.Template
open Finset

def region (u : ℕ) : Cells :=
  ((range (3*u+1)) ×ˢ (range (3*u-1))).filter fun p => (read u p.1 p.2).occupied

theorem occupied_in {u x y : ℤ} (mem : (read u x y).occupied) :
    0≤x ∧ x≤3*u ∧ 0≤y ∧ y≤3*u-2 := by
  change mark (frame u (x/3) (y/3)) (x%3).toNat (y%3).toNat at mem
  obtain ⟨first,_⟩:=Bool.and_eq_true_iff.mp mem
  change inside (frame u (x/3) (y/3)) (x%3).toNat (y%3).toNat = true at first
  have conditions := of_decide_eq_true first
  dsimp only [frame] at conditions
  omega

theorem mem_region {u : ℕ} {p : Cell} : p∈region u ↔ (read u p.1 p.2).occupied := by
  simp only [region,mem_filter,mem_product,mem_range]
  apply and_iff_right_of_imp
  intro mem
  have h:=occupied_in mem
  omega

theorem has_root {u : ℕ} (large : 5≤u) : (1,0)∈region u := by
  apply mem_region.mpr
  change mark (frame u 0 0) 1 0
  have nz : u≠0:=by omega
  have pos : 1≤u:=by omega
  simpa [mark,inside,frame,tile,nz,pos] using (show (286:ℕ).testBit 1 by decide)

theorem left_iff {u x y : ℕ} :
    left (region u) (x,y) ↔ (read u ((x:ℤ)-1) y).occupied := by
  unfold left
  dsimp only
  by_cases x0 : x=0
  · subst x
    simp only [lt_irrefl,false_and,false_iff]
    intro h; have :=occupied_in h; omega
  · rw [and_iff_right (by omega),mem_region]
    simp only [Nat.cast_sub (show 1≤x by omega),Nat.cast_one]

theorem below_iff {u x y : ℕ} :
    below (region u) (x,y) ↔ (read u x ((y:ℤ)-1)).occupied := by
  unfold below
  dsimp only
  by_cases y0 : y=0
  · subst y
    simp only [lt_irrefl,false_and,false_iff]
    intro h; have :=occupied_in h; omega
  · rw [and_iff_right (by omega),mem_region]
    simp only [Nat.cast_sub (show 1≤y by omega),Nat.cast_one]

theorem row_card {u y : ℕ} :
    (rowStarts (region u) y).card=((range (3*u+1)).filter (fun x : ℕ =>
      (read u x y).occupied && !(read u ((x:ℤ)-1) y).occupied)).card := by
  let p (x : ℕ) : Cell:=(x,y)
  rw [←card_image_of_injective _ (show Function.Injective p from fun _ _ h => congrArg Prod.fst h)]
  congr 1
  ext ⟨x,z⟩
  have bound (h : (read u x z).occupied) : x<3*u+1 := by have := occupied_in h; omega
  simp (config := {contextual:=true}) [p,rowStarts,mem_region,left_iff]
  grind

theorem col_card {u x : ℕ} :
    (colStarts (region u) x).card=((range (3*u-1)).filter (fun y : ℕ =>
      (read u x y).occupied && !(read u x ((y:ℤ)-1)).occupied)).card := by
  let p (y : ℕ) : Cell:=(x,y)
  rw [←card_image_of_injective _ (show Function.Injective p from fun _ _ h => congrArg Prod.snd h)]
  congr 1
  ext ⟨z,y⟩
  have bound (h : (read u z y).occupied) : y<3*u-1 := by have := occupied_in h; omega
  simp (config := {contextual:=true}) [p,colStarts,mem_region,below_iff]
  grind

theorem slice_card {u y : ℕ} :
    ((region u).filter (fun p => p.2=y)).card=((range (3*u+1)).filter (fun x : ℕ =>
      (read u x y).occupied)).card := by
  let p (x : ℕ) : Cell:=(x,y)
  rw [←card_image_of_injective _ (show Function.Injective p from fun _ _ h => congrArg Prod.fst h)]
  congr 1
  ext ⟨x,z⟩
  have bound (h : (read u x z).occupied) : x<3*u+1 := by have := occupied_in h; omega
  simp (config := {contextual:=true}) [p,mem_region]
  grind

theorem prefix_card (F : ℕ → ℤ) (test : ℕ → Bool) (N : ℕ)
    (step : ∀ i<N,F (i+1)=F i+(if test i then 1 else 0)) :
    (((range N).filter fun i => test i).card : ℤ)=F N-F 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one,filter_insert]
    have prev:=ih (fun i hi => step i (by omega))
    have inc:=step n (by omega)
    by_cases h : test n <;> simp [h] at * <;> omega

end BarequetRectangularPolyomino.Template

public section
namespace BarequetRectangularPolyomino
open Finset

theorem connected_of_descent (P : Cells) (o : Cell) (rank : Cell → ℤ) (root : o∈P)
    (step : ∀ p∈P, p≠o → ∃ q∈P, adjacent p q ∧ rank q<rank p) : Connected P := by
  induction P using Finset.strongInductionOn with
  | _ P ih =>
    by_cases single : P={o}
    · rw [single]; exact .one o
    have ne : (P.erase o).Nonempty := by
      by_contra! h
      apply single
      ext q
      simpa only [mem_singleton] using (show q∈P ↔ q=o by
        constructor
        · intro hq
          by_contra diff
          have : q∈P.erase o := mem_erase.mpr ⟨diff,hq⟩
          simp [h] at this
        · rintro rfl; exact root)
    obtain ⟨p,hp,maximal⟩:=exists_max_image (P.erase o) rank ne
    obtain ⟨po,pm⟩:=mem_erase.mp hp
    obtain ⟨q,qm,side,lt⟩:=step p pm po
    have smaller := ih (P.erase p) (erase_ssubset pm) (mem_erase.mpr ⟨Ne.symm po,root⟩) (by
      intro a ha other
      obtain ⟨b,hb,ab,lt'⟩:=step a (mem_erase.mp ha).2 other
      refine ⟨b,mem_erase.mpr ⟨?_,hb⟩,ab,lt'⟩
      intro bp
      have le:=maximal a (mem_erase.mpr ⟨other,(mem_erase.mp ha).2⟩)
      subst b
      omega)
    rw [←insert_erase pm]
    exact .attach smaller (notMem_erase p P) (mem_erase.mpr ⟨fun h => by subst q; omega,qm⟩) side

end BarequetRectangularPolyomino

public section
namespace BarequetRectangularPolyomino.Template
open Finset

variable {u : ℕ}

def RegularGrid (u : ℕ) : Prop :=
  ∀ x y : ℕ, x<3*u+1 → y<3*u-1 → Laws u x y

theorem row_runs (u5 : 5≤u) (good : RegularGrid u) (y : ℕ) (yb : y<3*u-1) :
    (rowStarts (region u) y).card=u := by
  rw [row_card]
  let F (x : ℕ):=(read u x y).row
  have c:=prefix_card F (fun x => (read u x y).occupied && !(read u ((x:ℤ)-1) y).occupied)
    (3*u+1) (fun x xb => by simpa [F] using (good x y xb yb).row)
  have init:=(good 0 y (by omega) yb).row0 rfl
  have last:=(good (3*u) y (by omega) yb).endX (by push_cast; rfl)
  dsimp [F] at c
  push_cast at c init last
  omega

theorem col_runs (u5 : 5≤u) (good : RegularGrid u) (x : ℕ) (xb : x<3*u+1) :
    (colStarts (region u) x).card=u := by
  rw [col_card]
  let F (y : ℕ):=(read u x y).col
  have c:=prefix_card F (fun y => (read u x y).occupied && !(read u x ((y:ℤ)-1)).occupied)
    (3*u-1) (fun y yb => by simpa [F] using (good x y xb yb).col)
  have init:=(good x 0 xb (by omega)).col0 rfl
  have last:=(good x (3*u-2) xb (by omega)).endY (by omega)
  dsimp [F] at c
  rw [show ((3*u-1 : ℕ):ℤ)=((3*u-2:ℕ):ℤ)+1 by omega] at c
  push_cast at init
  omega

theorem cells_card (u5 : 5≤u) (good : RegularGrid u) : (region u).card=6*u^2-1 := by
  let slice (y : ℕ) := ((region u).filter fun p => p.2=y).card
  let A (y : ℕ) := (read u (3*u) y).area
  have increment (y : ℕ) (yb : y<3*u-1) : (slice y : ℤ)=2*u+A (y+1)-A y := by
    dsimp only [slice]
    rw [slice_card]
    let F (x : ℕ) := (read u x y).cells
    have c:=prefix_card F (fun x => (read u x y).occupied) (3*u+1)
      (fun x xb => by simpa [F] using (good x y xb yb).cells)
    have init:=(good 0 y (by omega) yb).row0 rfl
    have last:=(good (3*u) y (by omega) yb).endX (by push_cast; rfl)
    dsimp [F] at c
    dsimp [A]
    push_cast at *
    omega
  have cumulative (N : ℕ) (hn : N≤3*u-1) :
      ((∑ y∈range N,slice y : ℕ):ℤ)=2*(u:ℤ)*N+A N-A 0 := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h:=ih (by omega)
      have inc:=increment n (by omega)
      push_cast
      nlinarith
  have total:=cumulative (3*u-1) (by omega)
  dsimp only [slice] at total
  rw [fibers_card (region u) Prod.snd (3*u-1) (by
    intro p hp
    have := occupied_in (mem_region.mp hp)
    omega)] at total
  have ini : A 0=0 := by
    dsimp [A,read,areaOff,frame]
    simp (disch := omega)
  have fin : A (3*u-1)=2*((u:ℤ)-1)+1 := by
    have castH : ((3*u-1:ℕ):ℤ)=3*(u:ℤ)-1 := by omega
    dsimp only [A,read]
    rw [castH,show (3*(u:ℤ)-1)/3=(u:ℤ)-1 by omega,show (3*(u:ℤ)-1)%3=2 by omega]
    simp [areaOff,frame]
  rw [ini,fin] at total
  have castH : ((3*u-1:ℕ):ℤ)=3*(u:ℤ)-1 := by omega
  rw [castH] at total
  have c : ((region u).card:ℤ)+1=6*(u:ℤ)^2 := by nlinarith
  have s : (region u).card+1=6*u^2 := by exact_mod_cast c
  omega

theorem shape_connected (u5 : 5≤u) (good : RegularGrid u) : Connected (region u) := by
  apply connected_of_descent (region u) (1,0) (fun p => (read u p.1 p.2).rank) (has_root u5)
  intro ⟨x,y⟩ occ other
  have occ':=mem_region.mp occ
  have bounds:=occupied_in occ'
  have path:=(good x y (by omega) (by omega)).path occ'
  rcases path with o|⟨m,l⟩|⟨m,l⟩|⟨m,l⟩|⟨m,l⟩
  · exact (other (Prod.ext (by dsimp; omega) (by dsimp; omega))).elim
  · have b:=occupied_in m
    have eq : ((x-1 : ℕ):ℤ)=(x:ℤ)-1 := by omega
    refine ⟨(x-1,y),mem_region.mpr (by simpa only [eq] using m),Or.inl ?_,?_⟩
    · apply Prod.ext <;> dsimp [east]; omega
    · simpa only [eq] using l
  · refine ⟨(x+1,y),mem_region.mpr (by simpa using m),Or.inr (Or.inl rfl),?_⟩
    simpa using l
  · have b:=occupied_in m
    have eq : ((y-1 : ℕ):ℤ)=(y:ℤ)-1 := by omega
    refine ⟨(x,y-1),mem_region.mpr (by simpa only [eq] using m),Or.inr (Or.inr (Or.inl ?_)),?_⟩
    · apply Prod.ext <;> dsimp [north]; omega
    · simpa only [eq] using l
  · refine ⟨(x,y+1),mem_region.mpr (by simpa using m),Or.inr (Or.inr (Or.inr rfl)),?_⟩
    simpa using l

end BarequetRectangularPolyomino.Template
