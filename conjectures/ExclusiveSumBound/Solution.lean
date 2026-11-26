module

public import conjectures.ExclusiveSumBound.Ternary
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

public section
namespace ExclusiveSumBound

private def words {s} (i : Fin s) : Finset (Fin s → Fin 3) :=
  Finset.univ.filter fun w => w i = 2

private theorem word_count {s} (i : Fin s) : (words i).card ≤ 3^(s-1) := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ n =>
    let all := (Finset.univ : Finset (Fin n → Fin 3)).image (fun w => i.insertNth (α := fun _ => Fin 3) 2 w)
    have subset : words i ⊆ all := by
      intro w hw
      have eq := (Finset.mem_filter.mp hw).2
      exact Finset.mem_image.mpr ⟨i.removeNth w,Finset.mem_univ _,eq ▸ i.insertNth_self_removeNth w⟩
    exact (Finset.card_le_card subset).trans (Finset.card_image_le.trans_eq (by simp))

private theorem separate {T u v : ℕ} {a b : ℤ} (hu : u<T) (hv : v<T)
    (h : a*T+u=b*T+v) : a=b ∧ u=v := by
  have sep (x y : ℤ) (lt : x<y) : x*T+(T:ℤ) ≤ y*T := by
    have p := mul_le_mul_of_nonneg_right (show x+1≤y by omega) (Int.natCast_nonneg T)
    simpa [add_mul] using p
  have eq : a=b := by
    rcases lt_trichotomy a b with lt|eq|lt
    · have := sep a b lt; omega
    · exact eq
    · have := sep b a lt; omega
  exact ⟨eq,by subst b; omega⟩

private theorem convert_labels {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V ↪ ℤ)
    (s : ℕ) (S : Fin s → ℤ) (cover : ∀ x y, G.Adj x y → ∃ i, f x+f y=S i) :
    ExclusiveLabels G (s*3^(s-1)) := by
  classical
  let bit (x : V) (i : Fin s) : ℕ := if ∃ y, G.Adj x y ∧ f x+f y=S i then 1 else 0
  have short (x i) : bit x i≤1 := by dsimp [bit]; split <;> decide
  let T := 3^s
  let K : ℤ := 1+∑ x : V, |f x|
  have positive (x) : 0 < f x+K := by
    have h := Finset.single_le_sum (f := fun v => |f v|) (fun v _ => abs_nonneg _) (Finset.mem_univ x)
    have := neg_abs_le (f x)
    dsimp [K]; omega
  have tagsmall (x) : encode s (bit x) < T := encode_lt _ _ (fun i => by have := short x i; omega)
  let label (x : V) : ℤ := (f x+K)*T+encode s (bit x)
  have inj : Function.Injective label := by
    intro x y e
    have eq := (separate (tagsmall x) (tagsmall y) e).1
    exact f.injective (add_right_cancel eq)
  have pos (x) : 0<label x := by
    have t : 0<(T:ℤ) := by exact_mod_cast (pow_pos (by decide : 0<3) s)
    exact add_pos_of_pos_of_nonneg (mul_pos (positive x) t) (Int.natCast_nonneg _)
  let digits (x y : V) (i : Fin s) : Fin 3 :=
    ⟨bit x i+bit y i,by have := short x i; have := short y i; omega⟩
  have pair (x y) : label x+label y =
      (f x+f y+2*K)*T + ((encode s (fun i => (digits x y i).val):ℕ):ℤ) := by
    dsimp [label,digits]
    rw [encode_add,Nat.cast_add]
    ring
  let key (i : Fin s) (w : Fin s → Fin 3) : ℤ :=
    (S i+2*K)*T + encode s (fun j => (w j).val)
  let candidates := (Finset.univ : Finset (Fin s)).biUnion (fun i => (words i).image (key i))
  let palette := candidates.filter (0<·)
  refine ⟨⟨label,inj⟩,pos,palette,fun _ ht => (Finset.mem_filter.mp ht).2,?_,?_⟩
  · apply (Finset.card_filter_le ..).trans
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _i : Fin s, 3^(s-1) := Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (word_count i)
      _ = s*3^(s-1) := by simp
  · intro x y _
    change G.Adj x y ↔ label x+label y ∈ palette
    constructor
    · intro edge
      obtain ⟨i,col⟩ := cover x y edge
      have bx : bit x i=1 := ite_eq_left ⟨y,edge,col⟩
      have by' : bit y i=1 := ite_eq_left ⟨x,edge.symm,(add_comm ..).trans col⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩,add_pos (pos x) (pos y)⟩
      refine Finset.mem_image.mpr ⟨digits x y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · apply Fin.ext
        change bit x i+bit y i=2
        omega
      · rw [pair,col]
    · intro mem
      obtain ⟨i,_,present⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp mem).1
      obtain ⟨w,marked,e⟩ := Finset.mem_image.mp present
      have match_ := (Finset.mem_filter.mp marked).2
      change w i=2 at match_
      rw [pair] at e
      have parts := separate (encode_lt s (fun j => (w j).val) (fun j => (w j).isLt))
        (encode_lt s (fun j => (digits x y j).val) (fun j => (digits x y j).isLt)) e
      have eq := encode_inj _ _ _ (fun j => (w j).isLt) (fun j => (digits x y j).isLt) parts.2
      have digit := congrFun eq i
      change (w i).val=bit x i+bit y i at digit
      rw [match_] at digit
      have bx : bit x i=1 := by have := short x i; have := short y i; change 2=_ at digit; omega
      have hit : ∃ z, G.Adj x z ∧ f x+f z=S i := by
        by_contra no
        simp [bit,no] at bx
      obtain ⟨z,hz,old⟩ := hit
      have hi := parts.1
      have same : z=y := f.injective (by omega)
      simpa [same] using hz

private theorem feasible {V : Type*} [Fintype V] (G : SimpleGraph V) :
    {k | SumLabels G k}.Nonempty := by
  classical
  let f : V ↪ ℤ := ⟨fun x => ((Fintype.equivFin V x).val:ℤ),by
    intro x y h
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    exact Int.natCast_inj.mp h⟩
  let all := (Finset.univ : Finset (V×V)).image fun p => f p.1+f p.2
  exact ⟨all.card,f,all,le_rfl,fun x y _ => Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩⟩

theorem bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    exclusiveNumber G ≤ sumIndex G * 3^(sumIndex G-1) := by
  classical
  have opt : SumLabels G (sumIndex G) := Nat.sInf_mem (feasible G)
  obtain ⟨f,D,le,cover⟩ := opt
  let e := Fintype.equivFin (↥D)
  let s := Fintype.card (↥D)
  have result := convert_labels G f s (fun i => (e.symm i).val) (by
    intro x y h
    let t : D := ⟨_,cover x y h⟩
    exact ⟨e t,by simp [t]⟩)
  have hs : s≤sumIndex G := by simpa [s] using le
  exact (Nat.sInf_le (s := {k | ExclusiveLabels G k}) result).trans
    (Nat.mul_le_mul hs (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hs _)))

theorem resolution : ¬ UnboundedExclusive := by
  rintro ⟨k,unbounded⟩
  obtain ⟨V,inst,G,h,greater⟩ := unbounded (k*3^(k-1))
  let _ := inst
  have := (bound G).trans (Nat.mul_le_mul h (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right h 1)))
  omega

/-- info: 'ExclusiveSumBound.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound
/-- info: 'ExclusiveSumBound.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution
end ExclusiveSumBound
