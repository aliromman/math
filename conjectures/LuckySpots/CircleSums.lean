module

public import conjectures.LuckySpots.Circle

@[expose] public section
namespace LuckySpots.Circle
open Finset
open scoped Classical
variable {m : ℕ}

/-- Sum a function over all words of a fixed length on m letters. -/
def C (m : ℕ) : ℕ → (List (Fin m) → ℚ) → ℚ
  | 0,f => f []
  | k+1,f => ∑ p : Fin m, C m k (fun w ↦ f (p::w))

theorem C_congr (k : ℕ) {f g : List (Fin m) → ℚ}
    (h : ∀ w, w.length=k → f w=g w) : C m k f=C m k g := by
  induction k generalizing f g with
  | zero => exact h [] rfl
  | succ k ih =>
    simp only [C]
    apply sum_congr rfl
    intro p _
    exact ih fun w hw ↦ h (p::w) (by simp [hw])

theorem C_const (k : ℕ) (c : ℚ) : C m k (fun _ ↦ c)=(m:ℚ)^k*c := by
  induction k with
  | zero => simp [C]
  | succ k ih => simp [C,ih,pow_succ]; ring

theorem C_add (k : ℕ) (f g : List (Fin m) → ℚ) :
    C m k (fun w ↦ f w+g w)=C m k f+C m k g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih => simp [C,ih,sum_add_distrib]

theorem C_sum (k : ℕ) (f : Fin m → List (Fin m) → ℚ) :
    C m k (fun w ↦ ∑ a,f a w)=∑ a,C m k (f a) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [C]
    conv => lhs; arg 2; ext p; rw [ih (fun a w ↦ f a (p::w))]
    exact sum_comm

theorem C_words (k : ℕ) (f : List ℕ → ℚ) :
    C m k (fun w ↦ f (w.map Fin.val))=W m k f := by
  induction k generalizing f with
  | zero => simp [C,W_zero]
  | succ k ih =>
    simp only [C,List.map_cons,W_succ]
    calc
      _ = ∑ p : Fin m,W m k (fun w ↦ f (p.val::w)) :=
        sum_congr rfl (fun p _ ↦ ih (fun w ↦ f (p.val::w)))
      _ = _ := Fin.sum_univ_eq_sum_range (fun p ↦ W m k (fun w ↦ f (p::w))) m

variable [NeZero m]

theorem C_shift (k : ℕ) (a : Fin m) (f : List (Fin m) → ℚ) :
    C m k (fun w ↦ f (w.map (·+a)))=C m k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    simp only [C,List.map_cons]
    calc
      _ = ∑ p : Fin m,C m k (fun w ↦ f ((p+a)::w)) :=
        sum_congr rfl (fun p _ ↦ ih (fun w ↦ f ((p+a)::w)))
      _ = _ := Equiv.sum_comp (Equiv.addRight a) (fun p ↦ C m k (fun w ↦ f (p::w)))

theorem rotate_average (k : ℕ) (f : Fin m → List (Fin m) → Prop)
    (cov : ∀ i a w, f (i+a) (w.map (·+a)) ↔ f i w) (j : Fin m) :
    (m:ℚ)*C m k (fun w ↦ wt (f j w))=C m k (fun w ↦ ∑ i : Fin m,wt (f i w)) := by
  have same (i : Fin m) : C m k (fun w ↦ wt (f i w))=C m k (fun w ↦ wt (f j w)) := by
    rw [←C_shift k (i-j) (fun w ↦ wt (f i w))]
    apply C_congr
    intro w _
    have h := cov j (i-j) w
    rw [add_sub_cancel ..] at h
    rw [h]
  rw [C_sum _ (fun i w ↦ wt (f i w))]
  simp_rw [same]
  simp

omit [NeZero m] in

private theorem wt_mem (F : Finset (Fin m)) : (∑ p : Fin m,wt (p∈F))=(F.card:ℚ) := by
  have row (p : Fin m) : wt (p∈F)=if p∈F then (1:ℚ) else 0 := by by_cases h : p∈F <;> simp [wt,h]
  simp_rw [row]
  rw [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem vacancy_mean (j : Fin m) (k : ℕ) :
    (m:ℚ)*C m k (fun w ↦ wt (j∈vacancies univ w))=(m:ℚ)^k*((m-k:ℕ):ℚ) := by
  have cov (i a : Fin m) (w : List (Fin m)) :
      i+a∈vacancies univ (w.map (·+a)) ↔ i∈vacancies univ w := by
    rw [←shift_univ a,vacancies_shift,mem_shift,shift_univ]
  rw [rotate_average k (fun i w ↦ i∈vacancies univ w) cov j,←C_const k ((m-k:ℕ):ℚ)]
  apply C_congr
  intro w hw
  rw [wt_mem,vacancies_card,card_univ,Fintype.card_fin,hw]

private theorem hit_cons_sum (F : Finset (Fin m)) (p : Fin m) (w : List (Fin m)) :
    (∑ i : Fin m,wt (hit i F (p::w)))=wt (p∈F)+∑ i : Fin m,wt (hit i (step F p) w) := by
  have h (i : Fin m) : wt (hit i F (p::w)) =
      (if p=i then wt (p∈F) else 0)+wt (hit i (step F p) w) := by
    by_cases e : p=i
    · subst i
      by_cases hp : p∈F
      · have hn := no_hit (j:=p) (F:=step F p) (by simp [step,target_self hp]) w
        simp [hit,wt,hp,hn]
      · simp [hit,wt,hp]
    · simp [hit,e]
  simp_rw [h,sum_add_distrib]
  simp

private theorem full_mean (F : Finset (Fin m)) (k : ℕ) (hk : F.card≤k) :
    C m k (fun w ↦ ∑ i : Fin m,wt (hit i F w))=
      (m:ℚ)^k*F.card*((F.card:ℚ)+1)/(2*m) := by
  have hm : (m:ℚ)≠0 := by exact_mod_cast NeZero.ne m
  induction k generalizing F with
  | zero =>
    have e : F=∅ := card_eq_zero.mp (by omega)
    simp [e,C,hit,wt]
  | succ k ih =>
    by_cases e : F=∅
    · subst F
      rw [show C m (k+1) (fun w ↦ ∑ i : Fin m,wt (hit i ∅ w))=C m (k+1) (fun _ ↦ 0) from
        C_congr _ (fun w _ ↦ by simp [wt,no_hit])]
      simp [C_const]
    have Fpos : 1≤F.card := card_pos.mpr (nonempty_iff_ne_empty.mpr e)
    simp only [C,hit_cons_sum,C_add,C_const]
    have val (p : Fin m) : C m k (fun w ↦ ∑ i, wt (hit i (step F p) w))=
        (m:ℚ)^k*((F.card:ℚ)-1)*F.card/(2*m) := by
      rw [ih _ (by rw [step_card];omega),step_card,Nat.cast_sub Fpos,Nat.cast_one]
      ring
    simp_rw [val,sum_add_distrib]
    rw [←mul_sum]
    rw [wt_mem]
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,pow_succ]
    field_simp
    ring

theorem lucky_mean (j : Fin m) (k : ℕ) (hm : m≤k) :
    (m:ℚ)*C m k (fun w ↦ wt (hit j univ w)) =
      (m:ℚ)^k*m*((m:ℚ)+1)/(2*m) := by
  have cov (i a : Fin m) (w : List (Fin m)) :
      hit (i+a) univ (w.map (·+a)) ↔ hit i univ w := by
    simpa only [shift_univ] using hit_shift univ w i a
  rw [rotate_average k (fun i w ↦ hit i univ w) cov j,full_mean _ _ (by simpa using hm)]
  simp

end LuckySpots.Circle
