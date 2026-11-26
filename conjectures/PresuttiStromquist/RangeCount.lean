module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel

@[expose] public section
namespace PresuttiStromquist
namespace Discrete

abbrev Pos := ℕ × ℕ

structure Frame where
  xl : ℕ
  xr : ℕ
  yl : ℕ
  yr : ℕ
  weight : ℕ
  deriving DecidableEq

def Frame.union (f g : Frame) : Frame :=
  ⟨min f.xl g.xl, max f.xr g.xr, min f.yl g.yl, max f.yr g.yr, f.weight+g.weight⟩

/-- A rectangle stores the total weight and the coordinate bounds of its leaves. -/
inductive Cloud
  | leaf (p : Pos) (w : ℕ)
  | node (f : Frame) (a b : Cloud)

def Cloud.frame : Cloud → Frame
  | .leaf p w => ⟨p.1,p.1,p.2,p.2,w⟩
  | .node f _ _ => f

def Cloud.valid : Cloud → Bool
  | .leaf .. => true
  | .node f a b => decide (f = a.frame.union b.frame) && a.valid && b.valid

def Cloud.points : Cloud → Set Pos
  | .leaf p _ => {p}
  | .node _ a b => a.points ∪ b.points

def Frame.contains (f : Frame) (p : Pos) : Prop :=
  f.xl ≤ p.1 ∧ p.1 ≤ f.xr ∧ f.yl ≤ p.2 ∧ p.2 ≤ f.yr

theorem Cloud.contains (c : Cloud) (h : c.valid) {p : Pos} (hp : p ∈ c.points) :
    c.frame.contains p := by
  induction c with
  | leaf u w =>
    have he : p=u := hp
    simp [he, frame, Frame.contains]
  | node f a b ia ib =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl,ha⟩,hb⟩
    rcases hp with h|h
    · rcases ia ha h with ⟨h1,h2,h3,h4⟩
      exact ⟨(min_le_left ..).trans h1, h2.trans (le_max_left ..),
        (min_le_left ..).trans h3, h4.trans (le_max_left ..)⟩
    · rcases ib hb h with ⟨h1,h2,h3,h4⟩
      exact ⟨(min_le_right ..).trans h1, h2.trans (le_max_right ..),
        (min_le_right ..).trans h3, h4.trans (le_max_right ..)⟩

def Cloud.fold {A : Type*} [AddMonoid A] (c : Cloud) (f : Pos → A) : A :=
  match c with
  | .leaf p w => w • f p
  | .node _ a b => a.fold f + b.fold f

theorem Cloud.fold_add {A : Type*} [AddCommMonoid A] (c : Cloud) (f g : Pos → A) :
    c.fold (fun p => f p + g p) = c.fold f + c.fold g := by
  induction c with
  | leaf p w => simp [fold, nsmul_add]
  | node _ a b ia ib => simp only [fold,ia,ib]; abel

theorem Cloud.fold_congr {A : Type*} [AddMonoid A] (c : Cloud) {f g : Pos → A}
    (h : ∀ p ∈ c.points, f p = g p) : c.fold f = c.fold g := by
  induction c with
  | leaf p w => simp [fold,h p (by simp [points])]
  | node _ a b ia ib =>
    unfold fold
    exact congrArg₂ (· + ·) (ia fun p hp => h p (Or.inl hp)) (ib fun p hp => h p (Or.inr hp))

theorem Cloud.fold_const {A : Type*} [AddMonoid A] (c : Cloud) (h : c.valid) (v : A) :
    c.fold (fun _ => v) = c.frame.weight • v := by
  induction c with
  | leaf _ _ => rfl
  | node f a b ia ib =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl,ha⟩,hb⟩
    simp [fold, frame, Frame.union, ia ha, ib hb, add_nsmul]

def order (a b c d : Pos) : Prop :=
  a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 ∧ c.2 < a.2 ∧ a.2 < d.2 ∧ d.2 < b.2
instance (a b c d : Pos) : Decidable (order a b c d) := by unfold order; infer_instance

/-- The weighted number of ordered selections with pattern 2413. -/
def quad (a b c d : Cloud) : ℕ :=
  a.fold (fun p => b.fold (fun q => c.fold (fun r => d.fold (fun s =>
    if order p q r s then 1 else 0))))

def solid (a b c d : Frame) : Bool :=
  a.xr < b.xl && b.xr < c.xl && c.xr < d.xl &&
    c.yr < a.yl && a.yr < d.yl && d.yr < b.yl

private theorem quad_solid (a b c d : Cloud) (ha : a.valid) (hb : b.valid)
    (hc : c.valid) (hd : d.valid) (hs : solid a.frame b.frame c.frame d.frame) :
    quad a b c d = a.frame.weight*b.frame.weight*c.frame.weight*d.frame.weight := by
  simp only [solid, Bool.and_eq_true, decide_eq_true_eq] at hs
  have horder (p q r s : Pos) (hp : p ∈ a.points) (hq : q ∈ b.points)
      (hr : r ∈ c.points) (ht : s ∈ d.points) : order p q r s := by
    have P := a.contains ha hp
    have Q := b.contains hb hq
    have R := c.contains hc hr
    have S := d.contains hd ht
    unfold Frame.contains at P Q R S
    unfold order
    omega
  unfold quad
  calc
    _ = a.fold (fun _ => b.fold (fun _ => c.fold (fun _ => d.fold (fun _ => (1:ℕ))))) := by
      refine a.fold_congr fun p hp => b.fold_congr fun q hq => c.fold_congr fun r hr =>
        d.fold_congr fun s ht => ?_
      simp [horder p q r s hp hq hr ht]
    _ = _ := by simp [Cloud.fold_const,ha,hb,hc,hd,Nat.mul_assoc]

/-- A failed inequality can be discarded. Each remaining comparison determines which box to split. -/
def dead (a b c d : Frame) : Bool :=
  b.xr ≤ a.xl || c.xr ≤ b.xl || d.xr ≤ c.xl ||
    a.yr ≤ c.yl || d.yr ≤ a.yl || b.yr ≤ d.yl

def width (xlo xhi ylo : ℕ) : ℕ :=
  if xhi < ylo then 0 else xhi - xlo

def choose (a b c d : Frame) : Fin 4 :=
  let sa := max (width a.xl a.xr b.xl)
    (max (width a.yl a.yr d.yl) (if c.yr < a.yl then 0 else a.yr-a.yl))
  let sb := max (width b.xl b.xr c.xl)
    (max (if a.xr < b.xl then 0 else b.xr-b.xl) (if d.yr < b.yl then 0 else b.yr-b.yl))
  let sc := max (width c.xl c.xr d.xl)
    (max (width c.yl c.yr a.yl) (if b.xr < c.xl then 0 else c.xr-c.xl))
  let sd := max (width d.yl d.yr b.yl)
    (max (if c.xr < d.xl then 0 else d.xr-d.xl) (if a.yr < d.yl then 0 else d.yr-d.yl))
  if sb ≤ sa && sc ≤ sa && sd ≤ sa then 0 else if sc ≤ sb && sd ≤ sb then 1
  else if sd ≤ sc then 2 else 3

def lower : ℕ → Cloud → Cloud → Cloud → Cloud → ℕ
  | 0, _, _, _, _ => 0
  | n+1, a,b,c,d =>
    let A := a.frame; let B := b.frame; let C := c.frame; let D := d.frame
    if dead A B C D then 0 else if solid A B C D then A.weight*B.weight*C.weight*D.weight else
    match choose A B C D with
    | 0 => match a with
      | .node _ l r => lower n l b c d + lower n r b c d
      | _ => 0
    | 1 => match b with
      | .node _ l r => lower n a l c d + lower n a r c d
      | _ => 0
    | 2 => match c with
      | .node _ l r => lower n a b l d + lower n a b r d
      | _ => 0
    | 3 => match d with
      | .node _ l r => lower n a b c l + lower n a b c r
      | _ => 0

theorem lower_le_quad (n) (a b c d : Cloud) (ha : a.valid) (hb : b.valid)
    (hc : c.valid) (hd : d.valid) : lower n a b c d ≤ quad a b c d := by
  induction n generalizing a b c d with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    unfold lower
    dsimp only
    split
    · exact Nat.zero_le _
    split
    · exact (quad_solid a b c d ha hb hc hd (by assumption)).symm.le
    split
    · cases a with
      | leaf => exact Nat.zero_le _
      | node f l r =>
        simp only [Cloud.valid,Bool.and_eq_true] at ha
        exact Nat.add_le_add (ih l b c d ha.1.2 hb hc hd) (ih r b c d ha.2 hb hc hd)
    · cases b with
      | leaf => exact Nat.zero_le _
      | node f l r =>
        simp only [Cloud.valid,Bool.and_eq_true] at hb
        simpa only [quad,Cloud.fold,Cloud.fold_add] using
          Nat.add_le_add (ih a l c d ha hb.1.2 hc hd) (ih a r c d ha hb.2 hc hd)
    · cases c with
      | leaf => exact Nat.zero_le _
      | node f l r =>
        simp only [Cloud.valid,Bool.and_eq_true] at hc
        simpa only [quad,Cloud.fold,Cloud.fold_add] using
          Nat.add_le_add (ih a b l d ha hb hc.1.2 hd) (ih a b r d ha hb hc.2 hd)
    · cases d with
      | leaf => exact Nat.zero_le _
      | node f l r =>
        simp only [Cloud.valid,Bool.and_eq_true] at hd
        simpa only [quad,Cloud.fold,Cloud.fold_add] using
          Nat.add_le_add (ih a b c l ha hb hc hd.1.2) (ih a b c r ha hb hc hd.2)

end Discrete
end PresuttiStromquist
