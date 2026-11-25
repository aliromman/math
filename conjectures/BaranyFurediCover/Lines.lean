module

public import conjectures.BaranyFurediCover.Statement
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace BaranyFurediCover
open Set

private theorem parametrize {s : Finset Lattice} (size : 1<s.card)
    (col : Collinear ℝ (pt '' (s : Set Lattice))) :
    ∃ p v : Lattice, ∃ f : Lattice → ℤ, v≠0 ∧ ∀ x∈s, x=p+f x • v := by
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp size
  obtain ⟨d,H⟩ := (collinear_iff_of_mem (mem_image_of_mem pt hp)).mp col
  obtain ⟨r,rr⟩ := H _ (mem_image_of_mem pt hq)
  let X := q 0-p 0
  let Y := q 1-p 1
  have nz : X≠0 ∨ Y≠0 := by
    by_contra! h
    apply ne
    have h0 : q 0=p 0 := sub_eq_zero.mp h.1
    have h1 : q 1=p 1 := sub_eq_zero.mp h.2
    ext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
  have gpos : 0<Int.gcd X Y := by
    rcases nz with hx|hy
    · exact Int.gcd_pos_of_ne_zero_left _ hx
    · rw [Int.gcd_comm]; exact Int.gcd_pos_of_ne_zero_left _ hy
  obtain ⟨g,u,v,hg,one,eu,ev⟩ := Int.exists_gcd_one' gpos
  let A := Int.gcdA u v
  let B := Int.gcdB u v
  have bez : u*A+v*B=1 := by simpa [A,B,one] using (Int.gcd_eq_gcd_ab u v).symm
  let f (x : Lattice) := A*(x 0-p 0)+B*(x 1-p 1)
  refine ⟨p,![u,v],f,?_,?_⟩
  · intro zero
    have e₀ := congrFun zero 0
    have e₁ := congrFun zero 1
    simp at e₀ e₁
    simp [e₀,e₁] at bez
  intro x hx
  obtain ⟨t,rt⟩ := H _ (mem_image_of_mem pt hx)
  have det : X*(x 1-p 1)=Y*(x 0-p 0) := by
    dsimp [X,Y]
    apply Int.cast_injective (α:=ℝ)
    push_cast
    have q0 := congrFun rr 0; have q1 := congrFun rr 1
    have x0 := congrFun rt 0; have x1 := congrFun rt 1
    change (q 0:ℝ)=r*d 0+p 0 at q0
    change (q 1:ℝ)=r*d 1+p 1 at q1
    change (x 0:ℝ)=t*d 0+p 0 at x0
    change (x 1:ℝ)=t*d 1+p 1 at x1
    rw [q0,q1,x0,x1]
    ring
  have cross : u*(x 1-p 1)=v*(x 0-p 0) := by
    apply mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g:ℤ) ≠ 0)
    rw [eu,ev] at det
    linear_combination det
  ext i
  fin_cases i
  · change x 0 = p 0 + f x * u
    dsimp [f]
    linear_combination -(x 0-p 0)*bez-B*cross
  · change x 1 = p 1 + f x * v
    dsimp [f]
    linear_combination -(x 1-p 1)*bez+A*cross

private theorem count_le_string {C : Set Plane} (hb : BddAbove (lengths C))
    {s : Finset Lattice} (inside : ∀ z∈s, pt z∈C) (col : Collinear ℝ (pt '' (s : Set Lattice))) :
    s.card-1≤stringDiameter C := by
  classical
  by_cases small : s.card≤1
  · omega
  obtain ⟨p,v,f,nz,eq⟩ := parametrize (by omega) col
  have nonempty := Finset.card_pos.mp (by omega : 0<s.card)
  obtain ⟨x,hx,lo⟩ := s.exists_min_image f nonempty
  obtain ⟨y,hy,hi⟩ := s.exists_max_image f nonempty
  have inj : Set.InjOn f (s : Set Lattice) := by
    intro z hz w hw h
    exact (eq z hz).trans ((congrArg (fun i : ℤ => p+i•v) h).trans (eq w hw).symm)
  have sub : s.image f ⊆ Finset.Icc (f x) (f y) := by
    rintro _ h
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_Icc.mpr ⟨lo _ hz,hi _ hz⟩
  have num := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj,Int.card_Icc] at num
  have order := lo y hy
  let k := (f y-f x).toNat
  have kint : (k:ℤ) = f y-f x := Int.toNat_of_nonneg (sub_nonneg.mpr order)
  have le : s.card-1≤k := by dsimp [k]; omega
  apply le.trans (le_csSup hb ?_)
  refine ⟨x,v,nz,inside _ hx,?_⟩
  have endpt : x+k•v=y := by
    rw [eq x hx,eq y hy]
    ext i
    change p i+f x*v i+(k:ℤ)*v i = p i+f y*v i
    rw [kint]
    ring
  rw [endpt]
  exact inside _ hy

private theorem string_mem {C : Set Plane} (conv : Convex ℝ C) {k : ℕ}
    (hk : k∈lengths C) : k∈lineLengths C := by
  obtain ⟨z,v,nz,hz,he⟩ := hk
  let f (i : ℕ) := z+i•v
  let s := (Finset.range (k+1)).image f
  have idx : ∃ i, v i≠0 := by
    by_contra! h
    exact nz (funext h)
  obtain ⟨j,hj⟩ := idx
  have inj : Function.Injective f := by
    intro i l h
    have eq := congrFun h j
    change z j + (i:ℤ)*v j=z j+(l:ℤ)*v j at eq
    have h' := mul_right_cancel₀ hj (add_left_cancel eq)
    exact_mod_cast h'
  have inC {i} (hi : i≤k) : pt (f i)∈C := by
    by_cases hk0 : k=0
    · have : i=0 := by omega
      simpa [this,f] using hz
    have pk : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hi' : (i:ℝ)≤k := by exact_mod_cast hi
    have t : (i:ℝ)/k∈Icc 0 1 := ⟨by positivity,(div_le_one pk).mpr hi'⟩
    convert conv.add_smul_sub_mem hz he t using 1
    ext j
    simp [f,pt]; field_simp [pk.ne']
  refine ⟨s,?_,?_,?_⟩
  · simp [s,Finset.card_image_of_injective _ inj]
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    exact inC (by simpa using Finset.mem_range.mp hi)
  · apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨pt z,pt v,?_⟩
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨(i:ℝ),?_⟩
    ext j
    simp [pt,f,add_comm]

theorem diameter_eq_string {C : Set Plane} (conv : Convex ℝ C) (hb : BddAbove (lengths C)) :
    diameter C = stringDiameter C := by
  have bound : ∀ k∈lineLengths C, k≤stringDiameter C := by
    rintro _ ⟨s,rfl,inside,col⟩
    exact count_le_string hb inside col
  exact le_antisymm (csSup_le' bound)
    (csSup_le' fun _ hk => le_csSup ⟨_,bound⟩ (string_mem conv hk))

end BaranyFurediCover
