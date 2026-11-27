module

public import conjectures.PracticalPolygons.Statement
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.ModEq

@[expose] public section
namespace PracticalPolygons

def shiftSum (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => (base <<< x) ||| shiftSum base xs

theorem bit_shiftSum {base n : ℕ} {xs : List ℕ} (h : (shiftSum base xs).testBit n) :
    ∃ x∈xs, ∃ i, base.testBit i ∧ n=i+x := by
  induction xs with
  | nil => simp [shiftSum] at h
  | cons a xs ih =>
    simp only [shiftSum,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftLeft,
      Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨ha,h⟩ | h := h
    · exact ⟨a,List.mem_cons_self,n-a,h,by omega⟩
    · obtain ⟨x,hx,i,hi,eqn⟩ := ih h
      exact ⟨x,List.mem_cons_of_mem _ hx,i,hi,eqn⟩

def fastPolygon (s x : ℕ) := (s-2)*(x*(x-1)/2)+x

@[simp] theorem fastPolygon_eq (s x : ℕ) : fastPolygon s x = polygonal s x := by
  simp only [polygonal,fastPolygon,Nat.choose_two_right]

def polyList (s H : ℕ) := (List.range (H+1)).map (fastPolygon s)

/-- A low binary digit of a mask remains set in every number that contains the mask. -/
theorem mask_covers {mask b n : ℕ} (eqn : (mask &&& b)=mask) (h : mask.testBit n) : b.testBit n := by
  have w := congrArg (fun x : ℕ => x.testBit n) eqn
  simpa [Nat.testBit_and,h] using w

theorem one_bit {n : ℕ} (h : Nat.testBit 1 n) : n=0 := by
  by_contra hn
  have : 1<2^n := Nat.one_lt_two_pow hn
  simp [Nat.testBit_lt_two_pow this] at h

def residueBits (s H M : ℕ) : ℕ :=
  let v := (polyList s H).map (·%M)
  let b := shiftSum (shiftSum 1 v) v
  b ||| (b >>> M)

theorem residue_cover {s H M : ℕ} (h : ((2^M-1) &&& residueBits s H M)=2^M-1)
    (n : ℕ) (pM : 0<M) :
    ∃ x≤H, ∃ y≤H, polygonal s x+polygonal s y ≡ n [MOD M] := by
  let r := n%M
  have small : r<M := Nat.mod_lt _ pM
  have bit := mask_covers h (by simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using small)
  let v := (polyList s H).map (·%M)
  let b := shiftSum (shiftSum 1 v) v
  change ((b ||| (b >>> M)).testBit r) at bit
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true] at bit
  have extract {t : ℕ} (hit : b.testBit t) : ∃ x≤H, ∃ y≤H, polygonal s x+polygonal s y ≡ t [MOD M] := by
    obtain ⟨z,hz,i,hi,et⟩ := bit_shiftSum hit
    obtain ⟨w,hw,j,hj,ei⟩ := bit_shiftSum hi
    simp only [v,polyList,List.mem_map,List.mem_range,fastPolygon_eq] at hz hw
    obtain ⟨_,⟨x,hx,rfl⟩,rfl⟩ := hw
    obtain ⟨_,⟨y,hy,rfl⟩,rfl⟩ := hz
    rw [one_bit hj,zero_add] at ei
    rw [et,ei]
    exact ⟨x,by omega,y,by omega,(Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm⟩
  obtain h|h := bit
  · obtain ⟨x,hx,y,hy,eqn⟩ := extract h
    exact ⟨x,hx,y,hy,eqn.trans (Nat.mod_modEq _ _)⟩
  · obtain ⟨x,hx,y,hy,eqn⟩ := extract h
    refine ⟨x,hx,y,hy,eqn.trans ?_⟩
    dsimp [r]
    simp only [Nat.ModEq,Nat.add_mod_left,Nat.mod_mod]

end PracticalPolygons
