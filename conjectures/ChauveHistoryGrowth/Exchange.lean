module

public import conjectures.ChauveHistoryGrowth.Shapes

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries

structure Bound (a b : S) (condition : Prop) : Prop where
  le : a ≼ b
  lt : condition → coeff 2 a<coeff 2 b

theorem bound_self (a : S) : Bound a a False := ⟨refl _,False.elim⟩

theorem Bound.weaken {a b : S} {p q : Prop} (h : Bound a b p) (hp : q → p) :
    Bound a b q := ⟨h.le,h.lt ∘ hp⟩

theorem Bound.chain {a b c : S} {p q : Prop} (f : Bound a b p) (g : Bound b c q) :
    Bound a c (p ∨ q) := by
  refine ⟨trans f.le g.le,?_⟩
  rintro (hp|hq)
  · exact (f.lt hp).trans_le (g.le _)
  · exact (f.le _).trans_lt (g.lt hq)

structure Convex (f : ℕ → Tree) : Prop where
  size : ∀ i, (f i).leaves=i+1
  rising : ∀ i, step f i ≼ step f (i+1)
  strict : ∀ i, coeff 2 (step f i) < coeff 2 (step f (i+1))

theorem convex_cat : Convex cat := ⟨cat_leaves,cat_increasing,cat_strict⟩
theorem convex_bal : Convex bal := ⟨bal_leaves,bal_increasing,bal_strict⟩

def product (f : ℕ → Tree) (i j : ℕ) := P (f i)*P (f j)

theorem gain_zero (a b : Tree) : constantCoeff (gain a b)=0 := by simp [gain,input_eq,hz]

theorem transfer {f : ℕ → Tree} (h : Convex f) (i j : ℕ) (le : i≤j) :
    Bound (product f (i+1) j) (product f i (j+1)) (i<j) := by
  let U := P (f i)*P (f j)
  let d := step f j-step f i
  have eq : product f i (j+1)-product f (i+1) j=U*d := by
    dsimp [product,U,d,step]
    rw [gain_factor (f i) (f (i+1)),gain_factor (f j) (f (j+1))]
    ring
  have dp : 0 ≼ d := by
    apply subP.mpr
    intro n
    exact (monotone_nat_of_le_succ fun k => h.rising k n) le
  refine ⟨subP.mp (eq ▸ mulP (mulP (Ppos _) (Ppos _)) dp),?_⟩
  intro hi
  have dz : constantCoeff d=0 := by simp [d,step,gain_zero]
  have dc : coeff 1 d=0 := by simp [d,step,gain_first,h.size]
  have cc : constantCoeff U=1 := by simp [U,P,hz]
  have eq' := congrArg (coeff 2) eq
  simp only [map_sub,mul_coeff_two,cc,one_mul,dc,mul_zero,dz,add_zero] at eq'
  have dpos := (strictMono_nat_of_lt_succ h.strict) hi
  dsimp [d] at eq'
  rw [map_sub] at eq'
  linarith

theorem minimum_split {f : ℕ → Tree} (h : Convex f) (i j : ℕ) (ij : i≤j) :
    Bound (product f ((i+j)/2) ((i+j+1)/2)) (product f i j) (i+1<j) := by
  by_cases close : j ≤ i+1
  · rw [show (i+j)/2=i by omega,show (i+j+1)/2=j by omega]
    exact (bound_self _).weaken (by omega)
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
    have prev := minimum_split h (i+1) l (by omega)
    have curr := transfer h i l (by omega)
    simp only [show i+1+l=i+(l+1) by omega] at prev
    exact (prev.chain curr).weaken fun _ => Or.inr (by omega)
termination_by j

theorem maximum_split {f : ℕ → Tree} (h : Convex f) (i j : ℕ) (ij : i≤j) :
    Bound (product f i j) (product f 0 (i+j)) (i≠0) := by
  induction i generalizing j with
  | zero => simpa using bound_self (product f 0 j)
  | succ i ih =>
    have cur := transfer h i j (by omega)
    have last := ih (j+1) (by omega)
    rw [show i+1+j=i+(j+1) by omega]
    exact (cur.chain last).weaken fun _ => Or.inl (by omega)

end ChauveHistoryGrowth
end
