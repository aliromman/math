module

public import conjectures.LuckySpots.Expansion
public import conjectures.LuckySpots.CountCut

@[expose] public section
namespace LuckySpots
open Finset
open scoped Classical

private theorem small_partition {j l : ℕ} (hl : l<j-1) (f : List ℕ → ℚ) :
    ∑ i∈range (j-1),W j l (fun w ↦ wt (emptyFirst j i w)*f w)=W j l f := by
  have zero_of (P : List ℕ → Prop) (h : ∀ w∈words j l, ¬P w) :
      W j l (fun w ↦ wt (P w)*f w)=0 := by
    calc
      _ = W j l (fun _ ↦ 0) := W_congr (fun w hw ↦ by simp [wt,h w hw])
      _ = 0 := by simp [W_const]
  have hf : W j l (fun w ↦ wt (filled j w)*f w)=0 := zero_of _ (by
    intro w hw h
    have hh := vacant_capacity (List.range j) w
    have len := (mem_words.mp hw).1
    change vacant (List.range j) w=[] at h
    simp [h,len] at hh
    omega)
  have he : W j l (fun w ↦ wt (emptyFirst j (j-1) w)*f w)=0 := zero_of _ (by
    intro w hw h
    have hfirst := ((first_empty (j-1) 0 w).1).mp (by
      simpa only [Nat.add_zero,show j-1+1=j by omega,emptyFirst] using h)
    have hwlen := (mem_words.mp hfirst.1).1
    have len := (mem_words.mp hw).1
    have lenle := List.length_filter_le (fun (z : ℕ) ↦ decide (z<j-1+1)) w
    change (low (j-1+1) w).length≤w.length at lenle
    omega)
  have h := partition_words j l f
  rw [hf,zero_add] at h
  conv at h => lhs; arg 1; rw [show j=(j-1)+1 by omega]
  rw [sum_range_succ,he,add_zero] at h
  exact h

private theorem first_count_symbol {j i : ℕ} (hi : i<j-1) (l : ℕ) :
    W j l (fun w ↦ wt (emptyFirst j i w)*(w.count (j-1):ℚ)) =
      (l.choose i:ℚ)*totalNumber i*((l-i:ℕ):ℚ)*((j-i-1:ℕ):ℚ)^(l-i)/((j-i-1:ℕ):ℚ) := by
  let b := j-i-1
  have eb : i+1+b=j := by dsimp [b]; omega
  have po : 0<b := by dsimp [b]; omega
  have ct (w : List ℕ) : w.count (j-1)=(high (i+1) w).count (b-1) := by
    induction w with
    | nil => rfl
    | cons x xs ih =>
      by_cases e : i+1≤x
      · have e' : x-(i+1)=b-1 ↔ x=j-1 := by dsimp [b]; omega
        have hi' : high (i+1) (x::xs)=(x-(i+1))::high (i+1) xs := by
          simp only [high,List.filter_cons_of_pos (p:=fun z : ℕ ↦ decide (i+1≤z)) (by simpa using e),List.map_cons]
        rw [hi']
        by_cases g : x=j-1
        · rw [show x-(i+1)=b-1 from e'.2 g,g]
          simp [ih]
        · simp [g,show x-(i+1)≠b-1 from fun h ↦ g (e'.1 h),ih]
      · have ne : x≠j-1 := by omega
        have hi' : high (i+1) (x::xs)=high (i+1) xs := by
          simp only [high,List.filter_cons_of_neg (p:=fun z : ℕ ↦ decide (i+1≤z)) (by simpa using e)]
        simp [hi',ne,ih]
  have h := first_weight i b l (fun w ↦ (w.count (b-1):ℚ))
  rw [eb,W_count _ _ _ (by omega)] at h
  calc
    _ = W j l (fun w ↦ wt (emptyFirst j i w)*((high (i+1) w).count (b-1):ℚ)) :=
      W_congr (fun w _ ↦ by rw [ct w])
    _ = _ := by rw [h]; ring

private def mass (j l i : ℕ) : ℚ :=
  (l.choose i:ℚ)*totalNumber i*((j-i-1:ℕ):ℚ)^(l-i)

private theorem mass_sum {j l : ℕ} (hl : l<j-1) :
    ∑ i∈range (j-1),mass j l i=(j:ℚ)^l := by
  have h := small_partition hl (fun _ ↦ 1)
  rw [W_const,mul_one] at h
  rw [←h]
  apply sum_congr rfl
  intro i hi
  have ne := mem_range.mp hi
  have eq : i+1+(j-i-1)=j := by omega
  have e := first_weight i (j-i-1) l (fun _ ↦ 1)
  rw [eq,W_const,mul_one] at e
  exact e.symm

/-- Before the lot can have only one vacancy, the first vacant site gives two exact
moments: the total mass and the number of occurrences of the last preference. -/
theorem small_expansion {j l : ℕ} (hl : l<j-1) :
    ((l:ℚ)-j+1)*E j l=(j:ℚ)^l/(2*j) := by
  have jpos : 0<(j:ℚ) := by exact_mod_cast (show 0<j by omega)
  let d : ℚ := (l:ℚ)-j+1
  have moments := small_partition hl (fun w ↦ (w.count (j-1):ℚ))
  rw [W_count _ _ _ (by omega)] at moments
  have mean : (∑ i∈range (j-1),(mass j l i+d*(mass j l i/((j-i-1:ℕ):ℚ)))) =
      (l:ℚ)*(j:ℚ)^l/j := by
    rw [←moments]
    apply sum_congr rfl
    intro i hi
    have b := mem_range.mp hi
    rw [first_count_symbol b]
    by_cases h : i≤l
    · have bi : i+1≤j := by omega
      have bn : ((j-i-1:ℕ):ℚ)=(j:ℚ)-i-1 := by
        rw [Nat.cast_sub (by omega : 1≤j-i), Nat.cast_sub (by omega : i≤j)]
        norm_num
      have bd : 0<((j-i-1:ℕ):ℚ) := by exact_mod_cast (show 0<j-i-1 by omega)
      simp only [mass,Nat.cast_sub h]
      dsimp [d]
      field_simp [bd.ne']
      rw [bn]
      ring
    · simp [mass,Nat.choose_eq_zero_of_lt (by omega : l < i)]
  rw [sum_add_distrib,mass_sum hl,←mul_sum] at mean
  have shape : E j l=K j*(j:ℚ)^l-((j:ℚ)^l+∑ i∈range (j-1),mass j l i/((j-i-1:ℕ):ℚ))/2 := by
    unfold E
    congr 1
    rw [←mass_sum hl,←sum_add_distrib,div_eq_mul_inv,Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    have positive : 0<((j-i-1:ℕ):ℚ) := by exact_mod_cast (show 0<j-i-1 by have := mem_range.mp hi; omega)
    unfold mass K
    field_simp
  rw [shape]
  change d*(K j*(j:ℚ)^l-(_+_)/2)=_
  have m : d*(∑ i∈range (j-1),mass j l i/((j-i-1:ℕ):ℚ))=(l:ℚ)*(j:ℚ)^l/j-(j:ℚ)^l := by linarith
  calc
    _ = d*((j:ℚ)^l/j)/2 - d*(∑ i∈range (j-1),mass j l i/((j-i-1:ℕ):ℚ))/2 := by
      unfold K
      field_simp
      ring
    _ = _ := by rw [m]; dsimp [d]; field_simp; ring

end LuckySpots
