module

public import conjectures.BraunerBalancedWords.Construction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace BraunerBalancedWords

private def flag {m : ℕ} (a b : Fin m) : ℤ := if a=b then 1 else 0

private theorem grouping {m : ℕ} {w : Word 4} {v : Word m} {f : Fin 4 → Fin m}
    (proj : ∀x, f (w x)=v x) (c : Fin m) (x : ℤ) (N : ℕ) :
    count v c x N= flag (f 0) c*count w 0 x N + flag (f 1) c*count w 1 x N +
      flag (f 2) c*count w 2 x N + flag (f 3) c*count w 3 x N := by
  have unit (z : ℤ) : (if v z=c then (1:ℤ) else 0)=
      flag (f 0) c*(if w z=0 then 1 else 0)+flag (f 1) c*(if w z=1 then 1 else 0)+
      flag (f 2) c*(if w z=2 then 1 else 0)+flag (f 3) c*(if w z=3 then 1 else 0) := by
    rw [←proj]
    generalize w z=q
    fin_cases q <;> simp [flag]
  induction N with
  | zero => simp [count]
  | succ N ih =>
    simp only [count_succ,ih,unit]
    ring

private theorem sparse_halves {k : ℕ} (hk : 2≤k) :
    count (exampleWord k) 2 2 (2*k)=1 ∧ count (exampleWord k) 3 2 (2*k)=1 ∧
    count (exampleWord k) 2 (weight k+3) (2*k)=0 ∧
    count (exampleWord k) 3 (weight k+3) (2*k)=0 := by
  let a:=weight k
  let P:ℤ:=width k
  obtain ⟨ag,pg⟩:=parameters hk
  change 3≤a at ag
  change P=2*a+2 at pg
  have el : ((2*k:ℕ):ℤ)=a+1 := by dsimp [a,weight]; omega
  simp only [count_formula hk,el]
  change ((2+(a+1))*1-3)/P-(2*1-3)/P=1 ∧
    ((2+(a+1))*1+(-a-3))/P-(2*1+(-a-3))/P=1 ∧
    ((a+3+(a+1))*1-3)/P-((a+3)*1-3)/P=0 ∧
    ((a+3+(a+1))*1+(-a-3))/P-((a+3)*1+(-a-3))/P=0
  have zero (z : ℤ) (h : 0≤z ∧ z<P) : z/P=0:=Int.ediv_eq_zero_of_lt h.1 h.2
  have neg (z : ℤ) (h : -P≤z ∧ z<0) : z/P= -1 :=
    (Int.ediv_eq_iff_of_pos (by omega)).mpr (by simp; omega)
  simp (disch := omega) only [mul_one,zero,neg]
  decide

theorem no_expansion {k : ℕ} (hk : 2≤k) {v : Word 2} (bv : Balanced v)
    (build : Expansion v (exampleWord k)) : False := by
  obtain ⟨f,link,divides⟩:=build.project periodic_example
  let a:=weight k
  have a3 : 3≤a:=(parameters hk).1
  have apart (i : Fin 4) (hi : i.val<2) : f 2≠f i ∧ f 3≠f i := by
    let c:=f i
    have d:=divides i
    rw [full_count hk] at d
    change (if i.val<2 then a else 1) ∣ count v c 0 (width k) at d
    rw [ite_eq_left hi,grouping link] at d
    simp only [full_count hk] at d
    change a ∣ flag (f 0) c*a+flag (f 1) c*a+flag (f 2) c*1+flag (f 3) c*1 at d
    have left : a ∣ flag (f 0) c*a+flag (f 1) c*a := Int.dvd_add (Int.dvd_mul_left ..) (Int.dvd_mul_left ..)
    have rest := Int.dvd_sub d left
    have q : a∣flag (f 2) c+flag (f 3) c := by
      convert rest using 1; ring
    change f 2≠c ∧ f 3≠c
    by_cases c2 : f 2=c <;> by_cases c3 : f 3=c <;> simp [flag,c2,c3] at q ⊢
    all_goals have :=Int.le_of_dvd (by decide) q; omega
  obtain ⟨ca,da⟩:=apart 0 (by decide)
  obtain ⟨cb,_⟩:=apart 1 (by decide)
  have cd : f 3=f 2 := by
    have eq (s t p : Fin 2) (sp : s≠p) (tp : t≠p) : s=t := by
      fin_cases s <;> fin_cases t <;> fin_cases p <;> simp_all
    exact eq _ _ _ da ca
  have rareCount (x : ℤ) (n : ℕ) : count v (f 2) x n=
      count (exampleWord k) 2 x n+count (exampleWord k) 3 x n := by
    rw [grouping link]
    simp [flag,Ne.symm ca,Ne.symm cb,cd]
  have bound:=bv (f 2) 2 (weight k+3) (2*k)
  rw [rareCount,rareCount] at bound
  obtain ⟨c,d,c',d'⟩:=sparse_halves hk
  omega

theorem least_period {k D : ℕ} (hk : 2≤k) (hp : Periodic (exampleWord k) D) : width k ∣ D := by
  have hit := (rare hk 2).1.mpr (Int.ModEq.refl _)
  have back := (rare hk (2+D)).1.mp ((hp 2).trans hit)
  rw [Int.modEq_iff_dvd] at back
  have eq : (2:ℤ)-(2+D)= -(D:ℤ) := by ring
  rw [eq,Int.dvd_neg] at back
  exact_mod_cast back

end BraunerBalancedWords

public section
namespace BraunerBalancedWords

/-- Four letters support arbitrarily long least periods outside the expansion class. -/
theorem unbounded (B : ℕ) : ∃ w : Word 4, Balanced w ∧
    (¬ ∃ v : Word 2, Balanced v ∧ Expansion v w) ∧
    (∃ D : ℕ, 0<D ∧ Periodic w D) ∧ ∀ D : ℕ, 0<D → Periodic w D → B<D := by
  let k:=B+4
  have hk : 2≤k:= by dsimp [k]; omega
  refine ⟨exampleWord k,balanced_example hk,?_,⟨width k,by dsimp [width,k]; omega,periodic_example⟩,?_⟩
  · rintro ⟨v,bv,build⟩
    exact no_expansion hk bv build
  · intro D pos per
    have low:=Nat.le_of_dvd pos (least_period hk per)
    dsimp [width,k] at low
    omega

private theorem translate_periods {n D : ℕ} {w v : Word n} (same : Translate w v) :
    Periodic w D ↔ Periodic v D := by
  obtain ⟨s,eq⟩:=same
  constructor
  · intro hw x
    have h:=hw (x-s)
    rwa [eq,eq,show x-s+(D:ℤ)+s=x+D by omega,show x-s+s=x by omega] at h
  · intro hv x
    rw [eq,eq,show x+(D:ℤ)+s=x+s+D by omega,hv]

private theorem list_period_bound {n : ℕ} (L : List (Word n)) : ∃ B : ℕ,
    ∀ v∈L, (∃ D : ℕ, 0<D ∧ Periodic v D) → ∃ D : ℕ, 0<D ∧ D≤B ∧ Periodic v D := by
  induction L with
  | nil => exact ⟨0,by simp⟩
  | cons w L ih =>
    obtain ⟨B,cap⟩:=ih
    by_cases hp : ∃ D : ℕ, 0<D ∧ Periodic w D
    · obtain ⟨p,pos,per⟩:=hp
      refine ⟨max p B,?_⟩
      intro v hv has
      rcases List.mem_cons.mp hv with rfl|mem
      · exact ⟨p,pos,by omega,per⟩
      · obtain ⟨d,positive,db,ok⟩:=cap v mem has
        exact ⟨d,positive,by omega,ok⟩
    · refine ⟨B,?_⟩
      intro v hv has
      rcases List.mem_cons.mp hv with rfl|mem
      · exact (hp has).elim
      · exact cap v mem has

theorem infinitely_many_exceptions : ¬FiniteExceptions 4 := by
  rintro ⟨L,cover⟩
  obtain ⟨B,cap⟩:=list_period_bound L
  obtain ⟨w,bal,ex,⟨p,pos,per⟩,large⟩:=unbounded B
  obtain ⟨v,mem,same⟩:=cover w bal ex
  obtain ⟨d,dp,db,dv⟩:=cap v mem ⟨p,pos,(translate_periods same).mp per⟩
  exact (Nat.not_lt_of_ge db) (large d dp ((translate_periods same).mpr dv))

theorem resolution : ¬ShortPeriod := by
  intro conj
  rcases conj 4 (exampleWord 4) (balanced_example (by decide)) with ⟨v,bv,e⟩|⟨D,d,small,per⟩
  · exact no_expansion (by decide) bv e
  · have low:=Nat.le_of_dvd d (least_period (by decide : 2≤4) per)
    change 16≤D at low
    omega

/-- info: 'BraunerBalancedWords.infinitely_many_exceptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinitely_many_exceptions

/-- info: 'BraunerBalancedWords.unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded

/-- info: 'BraunerBalancedWords.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end BraunerBalancedWords
