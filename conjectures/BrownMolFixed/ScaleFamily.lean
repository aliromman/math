module

public import conjectures.BrownMolFixed.ScaleBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
namespace BrownMolFixed
open Finset

private def q (t j : ℕ) := 16^(t-1-j)
private def count (t : ℕ) := 3*t+4
private def largeBase (t : ℕ) := 2^(count t)+2

/-- Each block places two smaller layers before its anchor. The last three layers are singletons. -/
private def exponent (t l : ℕ) : ℕ :=
  if l=0 then 64*16^t
  else if (l-1)/3<t then (if (l-1)%3=2 then 32 else 4)*q t ((l-1)/3)
  else 0

private def widths (t : ℕ) (i : Fin (count t)) := (largeBase t)^(exponent t i.val)
private def anchor {t : ℕ} (j : Fin t) : Fin (count t) := ⟨3*j.val+3,by dsimp [count]; omega⟩

private theorem power_ge (t j : ℕ) : 0<q t j := by dsimp [q]; positivity

private theorem scale_spaced {t i j : ℕ} (lt : i<j) (jt : j<t) : 16*q t j≤q t i := by
  unfold q
  rw [←pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem block_values {t : ℕ} (j : Fin t) :
    exponent t (3*j.val+1)=4*q t j.val ∧
    exponent t (3*j.val+2)=4*q t j.val ∧
    exponent t (3*j.val+3)=32*q t j.val := by
  have idx (c : ℕ) (hc : c<3) : (3*j.val+c)/3=j.val := by omega
  have rem (c : ℕ) (hc : c<3) : (3*j.val+c)%3=c := by omega
  have eval (c : ℕ) (hc : c<3) : exponent t (3*j.val+1+c)=
      (if c=2 then 32 else 4)*q t j.val := by
    rw [exponent,ite_eq_right_of_eq_false _ _ (eq_false (by omega)),show 3*j.val+1+c-1=3*j.val+c by omega,
      idx _ hc,ite_eq_left_of_eq_true _ _ (eq_true j.isLt),rem _ hc]
  exact ⟨by simpa using eval 0 (by decide),by simpa [Nat.add_assoc] using eval 1 (by decide),
    by simpa [Nat.add_assoc] using eval 2 (by decide)⟩

private theorem prefix_scales {t : ℕ} (j : Fin t) (i : Fin (count t)) :
    (i≤anchor j → 3*q t j.val+1≤exponent t i.val) ∧
    (anchor j< i → exponent t i.val+1≤3*q t j.val) := by
  have qp := power_ge t j.val
  have start : q t j.val ≤ 16^t := Nat.pow_le_pow_right (by decide) (by omega : t-1-j.val≤t)
  let b := (i.val-1)/3
  constructor
  · intro h
    have hle : i.val≤3*j.val+3 := h
    by_cases hz : i.val=0
    · rw [hz,exponent,ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      omega
    · have bj : b≤j.val := by dsimp [b];omega
      have bt : b<t := by omega
      have mono : q t j.val≤q t b := Nat.pow_le_pow_right (by decide) (by omega : t-1-j.val≤t-1-b)
      simp only [exponent,hz,ite_false,show (i.val-1)/3<t from bt,ite_true]
      change _≤(if _ then 32 else 4)*q t b
      split <;> omega
  · intro h
    have hle : 3*j.val+3< i.val := h
    have hz : i.val≠0 := by omega
    have bj : j.val<b := by dsimp [b];omega
    rw [exponent,ite_eq_right_of_eq_false _ _ (eq_false hz)]
    by_cases bt : b<t
    · have next := scale_spaced bj bt
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show (i.val-1)/3<t from bt))]
      change (if _ then 32 else 4)*q t b+1≤_
      split <;> omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(i.val-1)/3<t from bt))]
      omega

private theorem scale_signs {t : ℕ} (j : Fin t) :
    layerValue (widths t) (scaleProb (largeBase t) (12*q t j.val)) <
        scaleProb (largeBase t) (12*q t j.val) ∧
    scaleProb (largeBase t) (3*q t j.val) <
        layerValue (widths t) (scaleProb (largeBase t) (3*q t j.val)) := by
  have base : 2≤largeBase t := Nat.le_add_left ..
  have number : 2^(count t)<largeBase t := by dsimp [largeBase];omega
  have qp := power_ge t j.val
  let root : Fin (count t) := ⟨0,by dsimp [count];omega⟩
  let i : Fin (count t) := ⟨3*j.val+1,by dsimp [count];omega⟩
  let l : Fin (count t) := ⟨3*j.val+2,by dsimp [count];omega⟩
  let e := fun x : Fin (count t) => exponent t x.val
  have eb := block_values j
  have qle : q t j.val ≤ 16^t := Nat.pow_le_pow_right (by decide) (by omega : t-1-j.val≤t)
  constructor
  · apply scale_below (c:=8*q t j.val) base number (by omega) e root i l (anchor j)
    · intro h;have eq := congrArg Fin.val h;dsimp [i,l] at eq;omega
    · exact (by dsimp [root,i];omega : root.val≤ i.val)
    · exact (by dsimp [anchor,i];omega : i.val≤(anchor j).val)
    · exact (by dsimp [root,l];omega : root.val≤l.val)
    · exact (by dsimp [anchor,l];omega : l.val≤(anchor j).val)
    · change _ ≤ 64*16^t
      omega
    · change _≤exponent t (3*j.val+3)
      rw [eb.2.2];omega
    · change exponent t (3*j.val+1)+_≤_
      rw [eb.1];omega
    · change exponent t (3*j.val+2)+_≤_
      rw [eb.2.1];omega
  · exact scale_above (s:=3*q t j.val) base number (by omega) e (anchor j) (fun x => (prefix_scales j x).1) (fun x => (prefix_scales j x).2)

private theorem many_scale_roots (t : ℕ) : ∃ f : Fin t ↪ ℝ,∀ j : Fin t,
    f j∈Set.Ioo 0 1 ∧ reliability (chain (widths t)) (f j)=f j := by
  let B := largeBase t
  have b : 1<B := (by decide : 1<2).trans_le (Nat.le_add_left ..)
  let lo := fun j : Fin t => scaleProb B (12*q t j.val)
  let hi := fun j : Fin t => scaleProb B (3*q t j.val)
  have cont : Continuous (fun p : ℝ => layerValue (widths t) p - p) :=
    (continuous_value _).sub continuous_id
  have roots (j : Fin t) : ∃ z∈Set.Ioo (lo j) (hi j), layerValue (widths t) z-z=0 := by
    have qp := power_ge t j.val
    have ord : lo j<hi j := scale_strict b (by omega)
    have h := scale_signs j
    exact root_between ord cont (.inl ⟨sub_neg.mpr h.1,sub_pos.mpr h.2⟩)
  choose f hf eq using roots
  have mono : StrictMono f := by
    intro i j ij
    have gap := scale_spaced (show i.val<j.val from ij) j.isLt
    have qp := power_ge t j.val
    exact (hf i).2.trans ((scale_strict b (show 12*q t j.val<3*q t i.val by omega)).trans (hf j).1)
  refine ⟨⟨f,mono.injective⟩,fun j => ⟨⟨(scale_pos (by omega : 0<B) _).trans (hf j).1,?_⟩,?_⟩⟩
  · exact (hf j).2.trans_le (scale_le_one (by omega : 1≤B) _)
  · rw [reliability_chain]
    exact sub_eq_zero.mp (eq j)

private theorem all_live {n : ℕ} (nz : 0<n) (w : Fin n→ℕ) (hw : ∀i,0<w i) :
    Connected (chain w) (fun _ => true) := by
  rw [connected_iff]
  have occ (i : Fin n) : occupied (w:=w) (fun _=>true) i=true := by
    apply decide_eq_true
    exact ⟨⟨0,hw i⟩,rfl⟩
  exact ⟨⟨⟨0,nz⟩,occ _⟩,fun _ _ i _ _ _ _ => occ i⟩

private theorem singleton_cut {n : ℕ} (w : Fin n→ℕ) (hw : ∀i,0<w i)
    (l i r : Fin n) (hl : l < i) (hr : i<r) (hi : w i=1) :
    Cut (chain w) ⟨i,⟨0,hw i⟩⟩ := by
  let v : Vertex w := ⟨i,⟨0,hw i⟩⟩
  apply cut_of_disconnect (u:=⟨l,⟨0,hw l⟩⟩) (all_live (Nat.zero_lt_of_lt i.isLt) w hw)
    (fun eq ↦ hl.ne (congrArg Sigma.fst eq))
  change ¬Connected (chain w) (fun x => decide (x≠v))
  rw [connected_iff]
  intro h
  have ok (j : Fin n) (hj : j≠i) : occupied (fun x => decide (x≠v)) j=true := by
    apply decide_eq_true
    refine ⟨⟨0,hw j⟩,decide_eq_true ?_⟩
    exact fun eq => hj (congrArg Sigma.fst eq)
  have miss := h.2 l r i (ok l hl.ne) (ok r hr.ne') hl.le hr.le
  obtain ⟨u,hne⟩ := of_decide_eq_true miss
  have u0 : u.val=0 := by have vlt := u.isLt; omega
  exact (of_decide_eq_true hne) (congrArg (fun x : Fin (w i) => (⟨i,x⟩ : Vertex w)) (Fin.ext u0))

/-- Connected graphs with two cut vertices can have arbitrarily many distinct interior fixed points. -/
theorem unbounded_fixed_points (t : ℕ) : ∃ (n : ℕ) (w : Fin n→ℕ),
    Connected (chain w) (fun _=>true) ∧
    (∃ u v : Vertex w, u≠v ∧ Cut (chain w) u ∧ Cut (chain w) v) ∧
    ∃ f : Fin t ↪ ℝ, ∀ j, f j∈Set.Ioo 0 1 ∧ reliability (chain w) (f j)=f j := by
  have wp (i : Fin (count t)) : 0<widths t i := by dsimp [widths,largeBase];positivity
  let left : Fin (count t) := ⟨0,by dsimp [count];omega⟩
  let a : Fin (count t) := ⟨3*t+1,by dsimp [count];omega⟩
  let b : Fin (count t) := ⟨3*t+2,by dsimp [count];omega⟩
  let right : Fin (count t) := ⟨3*t+3,by dsimp [count];omega⟩
  have one (i : Fin (count t)) (h : 3*t< i.val) : widths t i=1 := by
    have nz : i.val≠0 := by omega
    have out : ¬(i.val-1)/3<t := by omega
    simp [widths,exponent,nz,out]
  refine ⟨count t,widths t,all_live (by dsimp [count];omega) _ wp,?_,many_scale_roots t⟩
  refine ⟨⟨a,⟨0,wp a⟩⟩,⟨b,⟨0,wp b⟩⟩,?_,?_,?_⟩
  · intro eq
    have idx := congrArg (fun x : Vertex (widths t) => x.1.val) eq
    dsimp [a,b] at idx
    omega
  · exact singleton_cut _ wp left a right (by change 0<3*t+1;omega)
      (by change 3*t+1<3*t+3;omega) (one _ (by change 3*t<3*t+1;omega))
  · exact singleton_cut _ wp left b right (by change 0<3*t+2;omega)
      (by change 3*t+2<3*t+3;omega) (one _ (by change 3*t<3*t+2;omega))

/-- info: 'BrownMolFixed.unbounded_fixed_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded_fixed_points

end BrownMolFixed
