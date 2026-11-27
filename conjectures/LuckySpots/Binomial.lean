module

public import conjectures.LuckySpots.Expansion
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace LuckySpots
open Finset

private def bin (n l : ℕ) (a b : ℚ) := (n.choose l:ℚ)*a^l*b^(n-l)

private theorem total_bin (n : ℕ) (a b : ℚ) :
    ∑ l∈range (n+1),bin n l a b=(a+b)^n := by
  rw [add_pow]
  apply sum_congr rfl
  intro l _
  unfold bin
  ring

private theorem moment (n : ℕ) (a b : ℚ) :
    ∑ l∈range (n+1),(l:ℚ)*bin n l a b=(n:ℚ)*a*(a+b)^(n-1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero,zero_mul,add_zero,Nat.succ_sub_one,←total_bin]
    rw [mul_sum]
    apply sum_congr rfl
    intro l _
    have c : (n+1:ℚ)*(n.choose l:ℚ)=((n+1).choose (l+1):ℚ)*(l+1:ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n l
    simp only [bin,pow_succ,Nat.cast_add,Nat.cast_one,Nat.succ_sub_succ_eq_sub]
    linear_combination a^l*a*b^(n-l)*(-c)

private theorem centered (n : ℕ) (a b d : ℚ) :
    (∑ l∈range (n+1),((l:ℚ)+d)*bin n l a b)=
      (n:ℚ)*a*(a+b)^(n-1)+d*(a+b)^n := by
  simp only [add_mul,sum_add_distrib,←mul_sum,moment,total_bin]

private def coeff (n j l : ℕ) (b : ℚ) := (n.choose l:ℚ)*((l:ℚ)-j+1)*b^(n-l)/b

private theorem main_sum {n j : ℕ} (hj : 0<j) (hn : j≤n) :
    (∑ l∈range (n+1),coeff n j l (n-j+1:ℕ)*(j:ℚ)^l)=(n+1:ℚ)^(n-1) := by
  let b : ℚ := (n-j+1:ℕ)
  have eb : b=(n:ℚ)-j+1 := by simp [b,Nat.cast_sub hn]
  have bp : 0<b := by dsimp [b]; positivity
  have p : (j:ℚ)+b=n+1 := by rw [eb]; ring
  have pos := lt_of_lt_of_le hj hn
  have pp : (n+1:ℚ)^n=(n+1:ℚ)^(n-1)*(n+1:ℚ) := by
    conv => lhs; arg 2; rw [show n=(n-1)+1 by omega]
    rw [pow_succ]
  have e := centered n (j:ℚ) b (1-j)
  rw [p,pp] at e
  calc
    _ = (∑ l∈range (n+1),((l:ℚ)+(1-j))*bin n l j b)/b := by
      rw [div_eq_mul_inv,sum_mul]
      apply sum_congr rfl
      intro l _
      change coeff n j l b*(j:ℚ)^l=_
      unfold coeff bin
      ring
    _ = _ := by rw [e]; field_simp; rw [eb]; ring

/-- With i prescribed letters, the remaining n-i choices have mean j-i-1.
The signed first moment of every correction term is zero. -/
private theorem killed {n j i : ℕ} (hn : j≤n) (hi : i<j-1) (c : ℚ) :
    ∑ l∈range (n+1),coeff n j l (n-j+1:ℕ)*
      ((l.choose i:ℚ)*c*((j-i-1:ℕ):ℚ)^(l-i))=0 := by
  let a : ℚ := (j-i-1:ℕ)
  let b : ℚ := (n-j+1:ℕ)
  have ea : a=(j:ℚ)-i-1 := by
    simp [a,Nat.cast_sub (by omega : 1≤j-i),Nat.cast_sub (by omega : i≤j)]
  have eb : b=(n:ℚ)-j+1 := by simp [b,Nat.cast_sub hn]
  have m : a+b=((n-i:ℕ):ℚ) := by rw [ea,eb,Nat.cast_sub (by omega)]; ring
  let term := fun l ↦ coeff n j l b*((l.choose i:ℚ)*c*a^(l-i))
  change ∑ l∈range (n+1),term l=0
  rw [show n+1=i+(n-i+1) by omega,sum_range_add]
  have zero : ∑ l∈range i,term l=0 := sum_eq_zero (fun l hl ↦ by
    simp [term,Nat.choose_eq_zero_of_lt (mem_range.mp hl)])
  rw [zero,zero_add]
  have eq (s : ℕ) : term (i+s)= ((n.choose i:ℚ)*c/b)*(((s:ℚ)+(-a))*bin (n-i) s a b) := by
    have q : (n.choose (i+s):ℚ)*((i+s).choose i:ℚ)=(n.choose i:ℚ)*((n-i).choose s:ℚ) := by
      exact_mod_cast (show n.choose (i+s)*(i+s).choose i = n.choose i*(n-i).choose s by
        simpa using Nat.choose_mul (n:=n) (Nat.le_add_right i s))
    have ind : n-(i+s)=n-i-s := by omega
    dsimp [term,coeff,bin]
    rw [ind,Nat.add_sub_cancel_left,Nat.cast_add]
    rw [ea] at *
    linear_combination (c*(s+i-j+1)*(((j:ℚ)-i-1)^s)*b^(n-i-s)/b)*q
  simp_rw [eq,←mul_sum,centered]
  rw [m]
  have pos : 0<n-i := by omega
  have pp : ((n-i:ℕ):ℚ)^(n-i)=((n-i:ℕ):ℚ)^(n-i-1)*((n-i:ℕ):ℚ) := by
    conv => lhs; arg 2; rw [show n-i=(n-i-1)+1 by omega]
    rw [pow_succ]
  rw [pp]
  ring

private theorem full_sum {n j : ℕ} (hj : 0<j) (hn : j≤n) :
    (∑ l∈range (n+1),coeff n j l (n-j+1:ℕ)*E j l)=K j*(n+1:ℚ)^(n-1) := by
  let b : ℚ := (n-j+1:ℕ)
  unfold E
  simp only [mul_sub,sum_sub_distrib]
  have lead : (∑ l∈range (n+1),coeff n j l b*(K j*(j:ℚ)^l))=K j*(n+1:ℚ)^(n-1) := by
    rw [←main_sum hj hn,Finset.mul_sum]
    apply sum_congr rfl
    intro l _
    ring
  change (∑ l∈range (n+1),coeff n j l b*(K j*(j:ℚ)^l))-_ = _
  rw [lead,sub_eq_self]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro i hi
  convert killed hn (mem_range.mp hi) ((totalNumber i:ℚ)*K (j-i-1)) using 1
  apply sum_congr rfl
  intro l _
  ring

theorem binomial_finish {n j : ℕ} (hj : 0<j) (hn : j≤n)
    (small : ∀ l, l<j-1 → ((l:ℚ)-j+1)*E j l=(j:ℚ)^l/(2*j))
    (large : (luckyNumber n j:ℚ)=∑ l∈range (n+1), if j≤l then
      (n.choose l:ℚ)*((l:ℚ)-j+1)*E j l*((n-j+1:ℕ):ℚ)^(n-l)/((n-j+1:ℕ):ℚ) else 0) :
    2*(j:ℚ)*luckyNumber n j=((j:ℚ)+1)*(n+1:ℚ)^(n-1)-
      ∑ h∈range (j-1),(n.choose h:ℚ)*(j:ℚ)^h*((n-j+1:ℕ):ℚ)^(n-1-h) := by
  let b : ℚ := (n-j+1:ℕ)
  let V := fun l ↦ coeff n j l b*E j l
  let T := fun l ↦ (n.choose l:ℚ)*(j:ℚ)^l*b^(n-1-l)
  have hj' : (0:ℚ)<j := by exact_mod_cast hj
  have bp : 0<b := by dsimp [b]; positivity
  have tall : (luckyNumber n j:ℚ)=∑ l∈range (n+1),if j≤l then V l else 0 := by
    rw [large]
    apply sum_congr rfl
    intro l _
    by_cases e : j≤l <;> simp [e,V,coeff,b]; ring
  have trunc : (∑ l∈range (n+1),if l<j-1 then T l else 0)=∑ l∈range (j-1),T l := by
    rw [←sum_filter]
    congr 1
    ext l
    simp only [mem_filter,mem_range]
    omega
  have row (l : ℕ) : V l=(if j≤l then V l else 0)+(1/(2*(j:ℚ)))*(if l<j-1 then T l else 0) := by
    by_cases e : j≤l
    · simp [e,show ¬l<j-1 by omega]
    by_cases f : l<j-1
    · simp only [e,ite_false,f,ite_true,zero_add]
      have power : b^(n-l)=b^(n-1-l)*b := by
        conv => lhs; arg 2; rw [show n-l=(n-1-l)+1 by omega]
        rw [pow_succ]
      have sm := small l f
      unfold V T coeff
      rw [power]
      field_simp at sm ⊢
      linear_combination (n.choose l:ℚ)*sm
    · have lj : l+1=j := by omega
      have e0 : (l:ℚ)-j+1=0 := by exact_mod_cast (show (l:ℤ)-j+1=0 by omega)
      simp [V,coeff,e0,e,f]
  have partition : K j*(n+1:ℚ)^(n-1)=(luckyNumber n j:ℚ)+(1/(2*(j:ℚ)))*∑ l∈range (j-1),T l := by
    rw [←full_sum hj hn]
    change (∑ l∈range (n+1),V l)=_
    calc
      _ = ∑ l∈range (n+1), ((if j≤l then V l else 0)+(1/(2*(j:ℚ)))*(if l<j-1 then T l else 0)) := sum_congr rfl (fun l _ ↦ row l)
      _ = _ := by rw [sum_add_distrib,←mul_sum,←tall,trunc]
  unfold K at partition
  change 2*(j:ℚ)*luckyNumber n j=((j:ℚ)+1)*(n+1:ℚ)^(n-1)-∑ l∈range (j-1),T l
  field_simp at partition
  linarith

end LuckySpots
