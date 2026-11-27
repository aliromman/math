module

public import conjectures.ChauveHistoryGrowth.Exchange

@[expose] public section
noncomputable section
namespace ChauveHistoryGrowth
open PowerSeries Finset

theorem input_gap (t u : Tree) :
    H u-H t = (input u-input t)+(H t+H u)*(H u-H t) := by
  rw [input_eq,input_eq]; ring

theorem bound_output {t u : Tree} {p : Prop} (b : Bound (input t) (input u) p) :
    Bound (H t) (H u) p := by
  have m := output_mono b.le
  refine ⟨m,fun h => ?_⟩
  have x := (zeroBelow _).mp (mulP (addP (hp t) (hp u)) (subP.mpr m)) 2
  have y := congrArg (coeff 2) (input_gap t u)
  simp only [map_add,map_sub] at y
  linarith [b.lt h]

theorem strict_all {t u : Tree} {p : Prop} (b : Bound (input t) (input u) p) (h : p)
    {n : ℕ} (hn : 2≤n) : count t n < count u n := by
  let F := H t+H u
  let d := H u-H t
  have fp := (zeroBelow _).mp (addP (hp t) (hp u))
  have dp := (zeroBelow _).mp (subP.mpr (output_mono b.le))
  have f1 : 0<coeff 1 F := by
    simp only [F,map_add,hc,leaf_one]
    exact_mod_cast add_pos t.leaves_pos u.leaves_pos
  have pos : 0<coeff n d := by
    induction n,hn using Nat.le_induction with
    | base => simpa [d] using sub_pos.mpr ((bound_output b).lt h)
    | succ j hj ih =>
      have term : coeff 1 F*coeff j d ≤ coeff (j+1) (F*d) := by
        rw [coeff_mul]
        exact single_le_sum (f := fun ij : ℕ × ℕ => coeff ij.1 F*coeff ij.2 d)
          (fun ij _ => mul_nonneg (fp _) (dp _))
          (show (1,j) ∈ antidiagonal (j+1) from mem_antidiagonal.mpr (by omega))
      have eq := congrArg (coeff (j+1)) (input_gap t u)
      change coeff (j+1) d = coeff (j+1) ((input u-input t)+F*d) at eq
      rw [eq,map_add,map_sub]
      linarith [b.le (j+1),mul_pos f1 ih]
  simpa [d,hc] using pos

theorem child_product {a b x y : Tree} {s t : Prop} (e : a.leaves=x.leaves)
    (f : b.leaves=y.leaves) (h : Bound (H a) (H x) s) (k : Bound (H b) (H y) t) :
    Bound (P a*P b) (P x*P y) (s∨t) := by
  refine ⟨mulM (addM (refl _) h.le) (addM (refl _) k.le) (Ppos _) (Ppos _),?_⟩
  simp only [mul_coeff_two,P,map_add,map_one,hz,add_zero,coeff_one,hc,leaf_one,e,f]
  have h' := h.le 2
  have k' := k.le 2
  simp only [hc] at h' k'
  rintro (bad|bad)
  · have lt := h.lt bad; simp only [hc] at lt; norm_num; linarith
  · have lt := k.lt bad; simp only [hc] at lt; norm_num; linarith

def index (t : Tree) := t.leaves-1

theorem index_size (t : Tree) : index t+1=t.leaves := by
  have := t.leaves_pos; dsimp [index]; omega

theorem fork_index (a b : Tree) : index (.fork a b)=index a+index b+1 := by
  change a.leaves+b.leaves-1=(a.leaves-1)+(b.leaves-1)+1
  have := a.leaves_pos; have := b.leaves_pos; omega

theorem product_swap (f : ℕ → Tree) (i j : ℕ) : product f i j=product f j i := mul_comm ..

theorem low_input (a b : Tree) : Bound (input (bal (index (.fork a b))))
    (product bal (index a) (index b)) (a.leaves+1<b.leaves ∨ b.leaves+1<a.leaves) := by
  rw [fork_index,bal]
  change Bound (product bal _ _) _ _
  let i:=index a
  let j:=index b
  have si := index_size a
  have sj := index_size b
  by_cases h : i≤j
  · exact (minimum_split convex_bal _ _ h).weaken (by dsimp [i,j] at h; omega)
  · have key := minimum_split convex_bal j i (by omega)
    rw [product_swap bal j i,show j+i=i+j by omega] at key
    exact key.weaken (by dsimp [i,j] at *; omega)

theorem high_input (a b : Tree) : Bound (product cat (index a) (index b))
    (input (cat (index (.fork a b)))) (a≠.tip ∧ b≠.tip) := by
  rw [fork_index,cat]
  change Bound _ (product cat 0 (index a+index b)) _
  have nt (t : Tree) (h : t≠.tip) : index t≠0 := by
    cases t with
    | tip => contradiction
    | fork l r => rw [fork_index]; omega
  by_cases h : index a≤ index b
  · exact (maximum_split convex_cat _ _ h).weaken fun z => nt a z.1
  · have key := maximum_split convex_cat (index b) (index a) (by omega)
    rw [product_swap cat (index b) (index a), Nat.add_comm (index b) (index a)] at key
    exact key.weaken fun z => nt b z.2

theorem extrema_bounds (t : Tree) :
    Bound (input (bal (index t))) (input t) (¬ t.Balanced) ∧
    Bound (input t) (input (cat (index t))) (¬ t.Caterpillar) := by
  induction t with
  | tip =>
    change Bound (input (bal 0)) (input .tip) (¬ True) ∧
      Bound (input .tip) (input .tip) (¬ True)
    rw [bal]
    exact ⟨(bound_self _).weaken fun h => h trivial,(bound_self _).weaken fun h => h trivial⟩
  | fork a b ha hb =>
    have low := child_product (by rw [bal_leaves,index_size]) (by rw [bal_leaves,index_size])
      (bound_output ha.1) (bound_output hb.1)
    have high := child_product (by rw [cat_leaves,index_size]) (by rw [cat_leaves,index_size])
      (bound_output ha.2) (bound_output hb.2)
    refine ⟨((low_input a b).chain low).weaken ?_,(high.chain (high_input a b)).weaken ?_⟩
    · intro bad
      by_cases x : a.Balanced
      · by_cases y : b.Balanced
        · exact Or.inl (by by_contra h; exact bad ⟨x,y,by omega,by omega⟩)
        · exact Or.inr (Or.inr y)
      · exact Or.inr (Or.inl x)
    · simp only [Tree.Caterpillar]
      intro bad
      by_cases x : a=.tip
      · exact Or.inl (Or.inr fun h => bad (Or.inl ⟨x,h⟩))
      by_cases y : b=.tip
      · exact Or.inl (Or.inl fun h => bad (Or.inr ⟨y,h⟩))
      exact Or.inr ⟨x,y⟩

theorem same_output {a b : Tree} (h : input a=input b) : H a=H b := by
  ext n
  exact le_antisymm (output_mono (h ▸ refl _) n) (output_mono (h ▸ refl _) n)

theorem same_bal {t : Tree} (h : t.Balanced) : H t=H (bal (index t)) := by
  induction t with
  | tip => change H .tip=H (bal 0); rw [bal]
  | fork a b ha hb =>
    obtain ⟨ba,bb,al,bl⟩ := h
    apply same_output
    rw [fork_index,bal]
    change (1+H a)*(1+H b)=product bal _ _
    rw [ha ba,hb bb]
    have x := index_size a
    have y := index_size b
    by_cases hab : index a≤ index b
    · rw [show (index a+index b)/2=index a by omega,
        show (index a+index b+1)/2=index b by omega]; rfl
    · rw [show (index a+index b)/2=index b by omega,
        show (index a+index b+1)/2=index a by omega]; exact mul_comm ..

theorem same_cat {t : Tree} (h : t.Caterpillar) : H t=H (cat (index t)) := by
  induction t with
  | tip => rfl
  | fork a b ha hb =>
    apply same_output
    rw [fork_index,cat]
    change (1+H a)*(1+H b)=(1+H .tip)*(1+H (cat (index a+index b)))
    rcases h with ⟨rfl,h⟩|⟨rfl,h⟩
    · rw [hb h,show index .tip=0 by rfl,zero_add]
    · rw [ha h,show index .tip=0 by rfl,add_zero]; exact mul_comm ..

theorem structural {n : ℕ} (hn : 2≤n) (t : Tree) :
    (t.Caterpillar ↔ ∀ u : Tree, u.leaves=t.leaves → count u n≤count t n) ∧
    (t.Balanced ↔ ∀ u : Tree, u.leaves=t.leaves → count t n≤count u n) := by
  have indices (u : Tree) (h : u.leaves=t.leaves) : index u=index t := by simp [index,h]
  constructor
  · constructor
    · intro h u eq
      have m := (bound_output (extrema_bounds u).2).le n
      rw [indices u eq,← same_cat h] at m
      simpa [hc] using m
    · intro m
      by_contra h
      exact (strict_all (extrema_bounds t).2 h hn).not_ge
        (m _ ((cat_leaves _).trans (index_size _)))
  · constructor
    · intro h u eq
      have m := (bound_output (extrema_bounds u).1).le n
      rw [indices u eq,← same_bal h] at m
      simpa [hc] using m
    · intro m
      by_contra h
      exact (strict_all (extrema_bounds t).1 h hn).not_ge
        (m _ ((bal_leaves _).trans (index_size _)))

end ChauveHistoryGrowth
end
