module

public import conjectures.BarequetRectangularPolyomino.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace BarequetRectangularPolyomino
open Finset

def hor (P : Cells) := P.filter (left P)
def ver (P : Cells) := P.filter (below P)

theorem hor_mono {P Q : Cells} (h : P⊆Q) : hor P⊆hor Q := by
  rintro p hp
  obtain ⟨m,lo,prev⟩:=mem_filter.mp hp
  exact mem_filter.mpr ⟨h m,lo,h prev⟩

theorem ver_mono {P Q : Cells} (h : P⊆Q) : ver P⊆ver Q := by
  rintro p hp
  obtain ⟨m,lo,prev⟩:=mem_filter.mp hp
  exact mem_filter.mpr ⟨h m,lo,h prev⟩

theorem edge_lower {P : Cells} (hw : Connected P) : P.card≤(hor P).card+(ver P).card+1 := by
  induction hw with
  | one p => simp
  | @attach P p q _ fresh qm side ih =>
    let Q:=insert p P
    have sub : P⊆Q:=subset_insert ..
    have H:=hor_mono sub
    have V:=ver_mono sub
    have bigger : hor P ⊂ hor Q ∨ ver P ⊂ ver Q := by
      rcases side with e|e|e|e
      · subst p
        apply Or.inl
        apply (ssubset_iff_of_subset H).mpr
        exact ⟨east q,mem_filter.mpr ⟨mem_insert_self ..,by simp [east],
          by simpa [east] using sub qm⟩,fun h => fresh (mem_filter.mp h).1⟩
      · subst q
        apply Or.inl
        apply (ssubset_iff_of_subset H).mpr
        refine ⟨east p,mem_filter.mpr ⟨sub qm,by simp [east],?_⟩,?_⟩
        · simp [east,Q]
        · intro h; exact fresh (by simpa [east,left] using (mem_filter.mp h).2.2)
      · subst p
        apply Or.inr
        apply (ssubset_iff_of_subset V).mpr
        exact ⟨north q,mem_filter.mpr ⟨mem_insert_self ..,by simp [north],
          by simpa [north] using sub qm⟩,fun h => fresh (mem_filter.mp h).1⟩
      · subst q
        apply Or.inr
        apply (ssubset_iff_of_subset V).mpr
        refine ⟨north p,mem_filter.mpr ⟨sub qm,by simp [north],?_⟩,?_⟩
        · simp [north,Q]
        · intro h; exact fresh (by simpa [north,below] using (mem_filter.mp h).2.2)
    rw [card_insert_of_notMem fresh]
    change _≤(hor Q).card+(ver Q).card+1
    rcases bigger with big|big
    · have := card_lt_card big; have := card_le_card V; omega
    · have := card_lt_card big; have := card_le_card H; omega

theorem fibers_card (P : Cells) (coord : Cell → ℕ) (d : ℕ) (bound : ∀ p∈P,coord p<d) :
    ∑ j ∈ range d,(P.filter (fun p => coord p=j)).card=P.card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  apply filter_eq_self.mpr
  exact fun p hp => mem_range.mpr (bound p hp)

theorem run_lower {P : Cells} {t w h : ℕ} (ok : Admissible t w h P) :
    (t+1)*(w+h)≤P.card+1 := by
  obtain ⟨cn,_,_,box,rows,cols⟩:=ok
  have splitX := card_filter_add_card_filter_not (s:=P) (left P)
  have splitY := card_filter_add_card_filter_not (s:=P) (below P)
  have fx := fibers_card (P.filter fun p => ¬left P p) Prod.snd h (fun p hp => (box p (mem_filter.mp hp).1).2)
  have fy := fibers_card (P.filter fun p => ¬below P p) Prod.fst w (fun p hp => (box p (mem_filter.mp hp).1).1)
  simp only [filter_filter] at fx fy
  have r : h*(t+1)≤(P.filter fun p => ¬left P p).card := by
    rw [← fx]
    calc
      h*(t+1) = ∑ _ ∈ range h,(t+1) := by simp
      _ ≤ _ := sum_le_sum fun i hi => by simpa [rowStarts,and_comm] using rows i (mem_range.mp hi)
  have c : w*(t+1)≤(P.filter fun p => ¬below P p).card := by
    rw [← fy]
    calc
      w*(t+1) = ∑ _ ∈ range w,(t+1) := by simp
      _ ≤ _ := sum_le_sum fun i hi => by simpa [colStarts,and_comm] using cols i (mem_range.mp hi)
  have e:=edge_lower cn
  dsimp [hor,ver] at e
  rw [mul_add,mul_comm (t+1) w,mul_comm (t+1) h]
  omega

end BarequetRectangularPolyomino

@[expose] public section
namespace BarequetRectangularPolyomino
open Finset

def missing (P : Cells) (w h : ℕ) : Cells := (range w ×ˢ range h) \ P

def strip (P : Cells) (w h x : ℕ) : Cells :=
  (missing P w h).filter fun p => p.1=x ∧ 0<p.2 ∧ p.2+1<h

theorem col_gaps {P : Cells} {w h x t : ℕ} (box : ∀ p∈P,p.1<w ∧ p.2<h)
    (runs : t+1≤(colStarts P x).card) : t≤(strip P w h x).card := by
  let A:=colStarts P x
  let early:=A.filter fun p => p.2<2
  let rest:=A.filter fun p => ¬p.2<2
  have first : early.card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨pa,py⟩:=mem_filter.mp hp
    obtain ⟨qa,qy⟩:=mem_filter.mp hq
    obtain ⟨pm,px,pn⟩:=mem_filter.mp pa
    obtain ⟨qm,qx,qn⟩:=mem_filter.mp qa
    apply Prod.ext (px.trans qx.symm)
    by_contra ne
    rcases lt_or_gt_of_ne ne with pq|qp
    · exact qn ⟨by omega,by rwa [show (q.1,q.2-1)=p from Prod.ext (qx.trans px.symm) (by omega)]⟩
    · exact pn ⟨by omega,by rwa [show (p.1,p.2-1)=q from Prod.ext (px.trans qx.symm) (by omega)]⟩
  have split : early.card+rest.card=A.card:=card_filter_add_card_filter_not ..
  let pred (p : Cell) : Cell:=(p.1,p.2-1)
  have inj : Set.InjOn pred rest := by
    intro p hp q hq eq
    have a:=(mem_filter.mp hp).2
    have b:=(mem_filter.mp hq).2
    have e1:=congrArg Prod.fst eq
    have e2:=congrArg Prod.snd eq
    change p.1=q.1 at e1
    apply Prod.ext e1
    change p.2-1=q.2-1 at e2
    omega
  have inc : rest.image pred⊆strip P w h x := by
    rintro z hz
    obtain ⟨p,pr,rfl⟩:=mem_image.mp hz
    obtain ⟨pa,py⟩:=mem_filter.mp pr
    obtain ⟨pm,px,pn⟩:=mem_filter.mp pa
    obtain ⟨xb,yb⟩:=box p pm
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_product.mpr ?_,?_⟩,px,?_,?_⟩
    · exact ⟨mem_range.mpr xb,mem_range.mpr (by dsimp [pred]; omega)⟩
    · exact fun bad => pn ⟨by omega,bad⟩
    · dsimp [pred]; omega
    · dsimp [pred]; omega
  have size:=card_le_card inc
  rw [card_image_iff.mpr inj] at size
  change t+1≤A.card at runs
  omega

def flipped (P : Cells) := P.map (Equiv.prodComm ℕ ℕ).toEmbedding

@[simp] theorem mem_flip {P : Cells} {p : Cell} : p∈flipped P ↔ p.swap∈P := by
  rcases p with ⟨x,y⟩
  simp [flipped]

theorem flip_rows (P : Cells) (y : ℕ) : colStarts (flipped P) y=flipped (rowStarts P y) := by
  ext p; rcases p with ⟨x,v⟩
  simp [colStarts,rowStarts,below,left,mem_flip]

theorem flip_missing (P : Cells) (w h : ℕ) : missing (flipped P) h w=flipped (missing P w h) := by
  ext p; rcases p with ⟨x,y⟩
  simp [missing,and_comm]

theorem hole_bound {P : Cells} {t w h : ℕ} (hy : 1<h)
    (box : ∀ p∈P,p.1<w ∧ p.2<h) (rows : ∀ y<h,t+1≤(rowStarts P y).card)
    (cols : ∀ x<w,t+1≤(colStarts P x).card) : t*w+2*t≤(missing P w h).card := by
  let M:=missing P w h
  let mid:=M.filter (fun p => 0<p.2 ∧ p.2+1<h)
  have midbox : ∀ p∈mid,p.1<w ∧ p.2<h := by
    intro p hp
    have := mem_product.mp (mem_sdiff.mp (mem_filter.mp hp).1).1
    exact ⟨mem_range.mp this.1,mem_range.mp this.2⟩
  have middle : t*w≤mid.card := by
    rw [← fibers_card mid Prod.fst w (fun p hp => (midbox p hp).1)]
    calc
      t*w = ∑ _ ∈ range w,t := by simp [mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro x xw
        have := col_gaps box (cols x (mem_range.mp xw))
        simpa only [mid,strip,M,filter_filter,and_comm] using this
  have flipbox : ∀ p∈flipped P,p.1<h ∧ p.2<w := by
    intro p hp
    have b:=box p.swap (mem_flip.mp hp)
    exact ⟨b.2,b.1⟩
  have side (y : ℕ) (yh : y<h) : t≤(M.filter fun p => p.2=y).card := by
    have rs : t+1≤(colStarts (flipped P) y).card := by
      rw [flip_rows,flipped,card_map]; exact rows y yh
    have k:=col_gaps flipbox rs
    have inc : strip (flipped P) h w y ⊆ flipped (M.filter fun p => p.2=y) := by
      intro p hp
      obtain ⟨a,b,_,_⟩:=mem_filter.mp hp
      exact mem_flip.mpr (mem_filter.mpr ⟨mem_flip.mp (flip_missing P w h ▸ a),b⟩)
    have card:=k.trans (card_le_card inc)
    simpa only [flipped,card_map] using card
  let bottom:=M.filter fun p => p.2=0
  let top:=M.filter fun p => p.2=h-1
  have bot : t≤bottom.card:=side 0 (by omega)
  have last : t≤top.card:=side _ (by omega)
  have d : Disjoint bottom top := by
    apply disjoint_left.mpr; intro p a b
    have := (mem_filter.mp a).2; have := (mem_filter.mp b).2; omega
  have d' : Disjoint (bottom∪top) mid := by
    apply disjoint_left.mpr; intro p pm hm
    have mm:=(mem_filter.mp hm).2
    rcases mem_union.mp pm with a|b
    · have := (mem_filter.mp a).2; omega
    · have := (mem_filter.mp b).2; omega
  have sub : (bottom∪top)∪mid ⊆ M := union_subset (union_subset (filter_subset ..) (filter_subset ..)) (filter_subset ..)
  have k:=card_le_card sub
  rw [card_union_of_disjoint d',card_union_of_disjoint d] at k
  change t*w+2*t≤M.card
  omega

theorem flip_cols (P : Cells) (x : ℕ) : rowStarts (flipped P) x=flipped (colStarts P x) := by
  ext p; rcases p with ⟨v,y⟩
  simp [colStarts,rowStarts,below,left,mem_flip]

theorem col_width {P : Cells} {w h : ℕ} (box : ∀ p∈P,p.1<w ∧ p.2<h) (x : ℕ) :
    (colStarts P x).card≤h := by
  let s:=colStarts P x
  have inj : Set.InjOn (Prod.snd : Cell → ℕ) (s : Set Cell) := by
    intro p hp q hq eq
    exact Prod.ext ((mem_filter.mp hp).2.1.trans (mem_filter.mp hq).2.1.symm) eq
  have inc : s.image Prod.snd ⊆ range h := by
    rintro y hy
    obtain ⟨p,pv,rfl⟩:=mem_image.mp hy
    exact mem_range.mpr (box p (mem_filter.mp pv).1).2
  have := card_le_card inc
  rwa [card_image_iff.mpr inj,card_range] at this

theorem area_constraints {P : Cells} {t w h : ℕ} (ht : 3≤t) (ok : Admissible t w h P) :
    P.card+t*w+2*t≤w*h ∧ P.card+t*h+2*t≤w*h := by
  obtain ⟨_,wx,hy,box,rows,cols⟩:=ok
  have flipbox : ∀ p∈flipped P,p.1<h ∧ p.2<w := fun p hp =>
    ⟨(box _ (mem_flip.mp hp)).2,(box _ (mem_flip.mp hp)).1⟩
  have sw (x : ℕ) (xw : x<w) : t+1≤(rowStarts (flipped P) x).card := by
    rw [flip_cols,flipped,card_map]; exact cols x xw
  have sh (y : ℕ) (yh : y<h) : t+1≤(colStarts (flipped P) y).card := by
    rw [flip_rows,flipped,card_map]; exact rows y yh
  have w1 := (sh 0 hy).trans (col_width flipbox _)
  have h1 := (cols 0 wx).trans (col_width box _)
  have m:=hole_bound (by omega) box rows cols
  have n:=hole_bound (by omega) flipbox sw sh
  rw [flip_missing,flipped,card_map] at n
  have subset : P⊆range w ×ˢ range h := fun p hp =>
    mem_product.mpr ⟨mem_range.mpr (box p hp).1,mem_range.mpr (box p hp).2⟩
  have count:=card_sdiff_add_card_eq_card subset
  rw [card_product,card_range,card_range] at count
  change (missing P w h).card+P.card=w*h at count
  omega

private theorem perimeter (T W H N : ℤ) (t : 3≤T) (h : H≤W) (Wpos : 0≤W) (Hpos : 0≤H)
    (lower : (T+1)*(W+H)≤N+1) (upper : N+T*W+2*T≤W*H) : 6*(T+1)^2≤N+1 := by
  have factor := mul_nonneg (show 0≤T by omega) (sub_nonneg.mpr h)
  have size : 6*T+6≤W+H := by
    by_contra! bad
    by_cases short : W+H≤6*T+4
    · have prod := mul_nonneg (show 0≤W+H by omega) (show 0≤6*T+4-(W+H) by omega)
      nlinarith [sq_nonneg (W-H)]
    · have eq : W+H=6*T+5 := by omega
      have sep : 1≤W-H := by omega
      have d2 := mul_nonneg (show 0≤W-H-1 by omega) (show 0≤W-H+1 by omega)
      have dt := mul_nonneg (show 0≤T by omega) (show 0≤W-H-1 by omega)
      have prod : (W+H)*(W+H-6*T-5)=0 := by rw [eq]; ring
      nlinarith
  nlinarith [mul_nonneg (show 0≤T+1 by omega) (sub_nonneg.mpr size)]

theorem area_lower {P : Cells} {t w h : ℕ} (ht : 3≤t) (ok : Admissible t w h P) :
    6*(t+1)^2-1≤P.card := by
  obtain ⟨H,V⟩:=area_constraints ht ok
  have low:=run_lower ok
  have result : 6*((t:ℤ)+1)^2≤(P.card : ℤ)+1 := by
    by_cases ord : h≤w
    · apply perimeter t w h _ (by exact_mod_cast ht) (by exact_mod_cast ord)
        (by positivity) (by positivity) (by exact_mod_cast low) (by exact_mod_cast H)
    · rw [Nat.add_comm w h] at low
      rw [Nat.mul_comm w h] at V
      apply perimeter t h w _ (by exact_mod_cast ht) (by exact_mod_cast Nat.le_of_not_ge ord)
        (by positivity) (by positivity) (by exact_mod_cast low) (by exact_mod_cast V)
  have result' : 6*(t+1)^2≤P.card+1 := by exact_mod_cast result
  omega

end BarequetRectangularPolyomino
