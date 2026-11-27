module

public import conjectures.LuckySpots.Cut
public import conjectures.LuckySpots.FirstEmpty

@[expose] public section
namespace LuckySpots
open Finset
open scoped Classical

noncomputable def wt (P : Prop) : ℚ := if P then 1 else 0

def emptyFirst (j i : ℕ) (w : List ℕ) := (vacant (List.range j) w).head?=some i

def lastLucky (j : ℕ) (w : List ℕ) := lucky (j-1) (List.range j) w=true

def filled (j : ℕ) (w : List ℕ) := vacant (List.range j) w=[]

noncomputable def U (j l : ℕ) := W j l (fun w ↦ wt (lastLucky j w))

noncomputable def A (j l : ℕ) := W j l (fun w ↦ wt (filled j w ∧ lastLucky j w))

theorem W_good (i k : ℕ) : W (i+1) k (fun u ↦ wt (good i u)) =
    if k=i then (totalNumber i:ℚ) else 0 := by
  simp only [W,wt,Finset.sum_boole]
  by_cases h : k=i
  · subst k
    simp only [ite_true,totalNumber]
    apply congrArg (fun s : Finset (List ℕ) ↦ (s.card:ℚ))
    apply Finset.ext
    intro u
    constructor
    · exact fun h ↦ Finset.mem_filter.mpr (Finset.mem_filter.mp h).2
    · intro h
      obtain ⟨hu,hv⟩ := Finset.mem_filter.mp h
      obtain ⟨len,bnd⟩ := mem_words.mp hu
      exact Finset.mem_filter.mpr ⟨mem_words.mpr ⟨len,fun x hx ↦ Nat.lt_succ_of_lt (bnd x hx)⟩,hu,hv⟩
  · simp only [h,ite_false,Nat.cast_eq_zero,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    rintro u hu ⟨hv,_⟩
    exact h ((mem_words.mp hu).1.symm.trans (mem_words.mp hv).1)

theorem first_weight (i b l : ℕ) (f : List ℕ → ℚ) :
    W (i+1+b) l (fun w ↦ wt (emptyFirst (i+1+b) i w)*f (high (i+1) w)) =
      (l.choose i:ℚ)*totalNumber i*W b (l-i) f := by
  have same (w : List ℕ) : wt (emptyFirst (i+1+b) i w)=wt (good i (low (i+1) w)) := by
    rw [show emptyFirst (i+1+b) i w ↔ good i (low (i+1) w) from (first_empty i b w).1]
  simp_rw [same]
  rw [split_sum (i+1) b l (fun u v ↦ wt (good i u)*f v)]
  have term (k : ℕ) : (l.choose k:ℚ)* W (i+1) k (fun u ↦ W b (l-k) (fun v ↦ wt (good i u)*f v)) =
      if k=i then (l.choose i:ℚ)*totalNumber i*W b (l-i) f else 0 := by
    simp only [W_mul]
    rw [show W (i+1) k (fun u ↦ wt (good i u)*W b (l-k) f) =
      W b (l-k) f*W (i+1) k (fun u ↦ wt (good i u)) by simp only [←W_mul,mul_comm]]
    rw [W_good]
    split <;> rename_i he
    · subst k; ring
    · ring
  simp_rw [term]
  by_cases h : i≤l
  · simp [h]
  · simp [Nat.choose_eq_zero_of_lt (by omega : l < i)]

/-- The number of times a fixed letter occurs across all words. -/
theorem W_count (m k p : ℕ) (hp : p<m) :
    W m k (fun w ↦ (w.count p:ℚ))=(k:ℚ)*(m:ℚ)^k/m := by
  have hm : (m:ℚ)≠0 := by exact_mod_cast (by omega : m≠0)
  induction k with
  | zero => simp [W_zero]
  | succ k ih =>
    rw [W_succ]
    have row (x : ℕ) : W m k (fun w ↦ ((x::w).count p:ℚ)) =
        (if x=p then (m:ℚ)^k else 0)+(k:ℚ)*(m:ℚ)^k/m := by
      by_cases e : x=p
      · subst x
        simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one]
        rw [show W m k (fun w ↦ (w.count p:ℚ)+1) =
          W m k (fun w ↦ (w.count p:ℚ))+W m k (fun _ ↦ 1) from W_add ..,ih,W_const]
        simp
        ring
      · simp [e,ih]
    simp_rw [row]
    rw [sum_add_distrib]
    simp [hp,pow_succ]
    field_simp
    ring

theorem wt_and (P Q : Prop) : wt (P ∧ Q)=wt P*wt Q := by
  by_cases p : P <;> by_cases q : Q <;> simp [wt,p,q]

private theorem first_or_full (j : ℕ) (w : List ℕ) (f : List ℕ → ℚ) :
    wt (filled j w)*f w + ∑ i∈range j,wt (emptyFirst j i w)*f w=f w := by
  by_cases h : filled j w
  · have eq : vacant (List.range j) w=[] := h
    simp [h,wt,emptyFirst,eq]
  · obtain ⟨i,is,eq⟩ := List.exists_cons_of_ne_nil (show vacant (List.range j) w≠[] from h)
    have hh : i∈vacant (List.range j) w := by rw [eq]; simp
    have hi : i<j := List.mem_range.mp ((vacant_sublist _ _).subset hh)
    simp [h,wt,emptyFirst,eq,hi]

theorem partition_words (j l : ℕ) (f : List ℕ → ℚ) :
    W j l (fun w ↦ wt (filled j w)*f w) +
        ∑ i∈range j,W j l (fun w ↦ wt (emptyFirst j i w)*f w) = W j l f := by
  rw [W_swap,←W_add]
  exact W_congr (fun w _ ↦ first_or_full j w f)

theorem first_luck_count {j i : ℕ} (hi : i<j-1) (l : ℕ) :
    W j l (fun w ↦ wt (emptyFirst j i w)*wt (lastLucky j w)) =
      (l.choose i:ℚ)*totalNumber i*U (j-i-1) (l-i) := by
  let b := j-i-1
  have eb : i+1+b=j := by dsimp [b]; omega
  have sj : i+1+(b-1)=j-1 := by dsimp [b]; omega
  calc
    _ = W (i+1+b) l (fun w ↦ wt (emptyFirst (i+1+b) i w)*wt (lastLucky b (high (i+1) w))) := by
      rw [eb]
      apply W_congr
      intro w _
      by_cases h : emptyFirst j i w
      · have good' := ((first_empty i b w).1).mp (by simpa [eb,emptyFirst] using h)
        have e := (first_empty i b w).2 good' (b-1)
        rw [eb,sj] at e
        simp [lastLucky,e]
      · simp [wt,h]
    _ = _ := first_weight i b l (fun v ↦ wt (lastLucky b v))

theorem local_count {j : ℕ} (hj : 0<j) (l : ℕ) :
    A j l+∑ i∈range (j-1),(l.choose i:ℚ)*totalNumber i*U (j-i-1) (l-i) = U j l := by
  have h := partition_words j l (fun w ↦ wt (lastLucky j w))
  have lastTerm : W j l (fun w ↦ wt (emptyFirst j (j-1) w)*wt (lastLucky j w))=0 := by
    calc
      _ = W j l (fun _ ↦ 0) := by
        apply W_congr
        intro w _
        by_cases he : emptyFirst j (j-1) w
        · have hh : (j-1)∈vacant (List.range j) w := List.mem_of_mem_head? (by change (vacant (List.range j) w).head?=some (j-1) at he; rw [he]; rfl)
          have hl := not_lucky_of_vacant List.pairwise_lt_range hh
          simp [wt,lastLucky,hl]
        · simp [wt,he]
      _ = 0 := by simp [W_const]
  rw [show j=(j-1)+1 by omega] at h
  conv at h => lhs; rhs; rw [sum_range_succ]
  simp only [show j-1+1=j by omega,lastTerm,add_zero] at h
  convert h using 1
  · congr 1
    · simp only [A,wt_and]
    · exact (sum_congr rfl (fun i hi ↦ first_luck_count (mem_range.mp hi) l)).symm

  · rfl

end LuckySpots
