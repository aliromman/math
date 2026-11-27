module

public import conjectures.BraunerBalancedWords.Expansion
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
namespace BraunerBalancedWords

def width (k : ℕ) := 4*k
def weight (k : ℕ) : ℤ := 2*(k:ℤ)-1

def exampleWord (k : ℕ) : Word 4 := fun x =>
  let a:=weight k
  let r:=x*a%(width k)
  if r<a then 0 else if r<2*a then 1 else if r=2*a then 2 else 3

theorem parameters {k : ℕ} (hk : 2≤k) :
    3≤weight k ∧ (width k:ℤ)=2*weight k+2 := by dsimp [weight,width]; omega

theorem periodic_example {k : ℕ} : Periodic (exampleWord k) (width k) := by
  intro x
  simp [exampleWord,add_mul,Int.add_mul_emod_self_left]

private theorem cancel_odd {k : ℕ} (x y : ℤ) :
    x*weight k ≡ y*weight k [ZMOD (width k)] ↔ x ≡ y [ZMOD (width k)] := by
  have inv : weight k*weight k ≡ 1 [ZMOD (width k)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨1-(k:ℤ),?_⟩
    simp [width,weight]
    ring
  constructor
  · intro h
    have s:=h.mul_right (weight k)
    rw [mul_assoc,mul_assoc] at s
    exact (by simpa using (inv.mul_left x).symm.trans (s.trans (inv.mul_left y)))
  · intro h; exact h.mul_right _

theorem rare {k : ℕ} (hk : 2≤k) (x : ℤ) :
    (exampleWord k x=2 ↔ x ≡ 2 [ZMOD (width k)]) ∧
    (exampleWord k x=3 ↔ x ≡ weight k+2 [ZMOD (width k)]) := by
  let a:=weight k
  let P:ℤ:=width k
  obtain ⟨ag,pg⟩:=parameters hk
  change 3≤a at ag
  change P=2*a+2 at pg
  let R:=x*a%P
  have r0 : 0≤R:=Int.emod_nonneg _ (by omega)
  have r1 : R<P:=Int.emod_lt_of_pos _ (by omega)
  have top : 2*a%P=2*a := Int.emod_eq_of_lt (by omega) (by omega)
  have top1 : (2*a+1)%P=2*a+1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h1 : (a+2)*a ≡ 2*a+1 [ZMOD P] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨1-(k:ℤ),?_⟩
    dsimp [a,P,weight,width]
    ring
  have h0 := cancel_odd (k:=k) x 2
  have h2 := cancel_odd (k:=k) x (a+2)
  have q0 : R=2*a ↔ x ≡ 2 [ZMOD P] := by
    rw [←h0]
    change R=2*a ↔ R=(2*a)%P
    rw [top]
  have q2 : R=2*a+1 ↔ x ≡ a+2 [ZMOD P] := by
    rw [←h2]
    change R=2*a+1 ↔ R=((a+2)*a)%P
    rw [show ((a+2)*a)%P=(2*a+1)%P from h1,top1]
  rw [←q0,←q2]
  change ((if R<a then 0 else if R<2*a then 1 else if R=2*a then 2 else 3 : Fin 4)=2 ↔ _) ∧
    ((if R<a then 0 else if R<2*a then 1 else if R=2*a then 2 else 3 : Fin 4)=3 ↔ _)
  split_ifs <;> norm_num <;> omega

theorem common {k : ℕ} (hk : 2≤k) (x : ℤ) :
    (exampleWord k x=0 ↔ x*weight k%(width k)<weight k) ∧
    (exampleWord k x=1 ↔ ((x-1)*weight k)%(width k)<weight k) := by
  let a:=weight k
  let P:ℤ:=width k
  obtain ⟨ag,pg⟩:=parameters hk
  change 3≤a at ag
  change P=2*a+2 at pg
  let R:=x*a%P
  have r0 : 0≤R:=Int.emod_nonneg _ (by omega)
  have r1 : R<P:=Int.emod_lt_of_pos _ (by omega)
  have prev : ((x-1)*a)%P=(R-a)%P := by rw [sub_mul,one_mul,Int.emod_sub_emod]
  have test : (R-a)%P<a ↔ a≤R ∧ R<2*a := by
    by_cases low : R<a
    · rw [←Int.add_emod_right (R-a) P,Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  change ((if R<a then 0 else if R<2*a then 1 else if R=2*a then 2 else 3 : Fin 4)=0 ↔ R<a) ∧
    ((if R<a then 0 else if R<2*a then 1 else if R=2*a then 2 else 3 : Fin 4)=1 ↔ ((x-1)*a)%P<a)
  rw [prev,test]
  split_ifs <;> norm_num <;> omega

/-- Start at C. The first alternating block has k-1 pairs and the second has k pairs. -/
theorem spelling {k : ℕ} (hk : 2≤k) (j : ℤ) (lo : 0≤j) (hi : j<(width k:ℤ)) :
    exampleWord k (j+2)=
      if j=0 then 2 else if j=weight k then 3
      else if j<weight k then (if j%2=1 then 0 else 1)
      else (if j%2=0 then 0 else 1) := by
  let a:=weight k
  let P:ℤ:=width k
  obtain ⟨ag,pg⟩:=parameters hk
  change 3≤a at ag
  change P=2*a+2 at pg
  change j<P at hi
  have ap : a=2*(k:ℤ)-1 := rfl
  let r:=(j+2)*a%P
  change (if r<a then 0 else if r<2*a then 1 else if r=2*a then 2 else 3 : Fin 4)=
    (if j=0 then 2 else if j=a then 3 else if j<a then (if j%2=1 then 0 else 1)
      else (if j%2=0 then 0 else 1))
  have rem (v q : ℤ) (eq : (j+2)*a=v+q*P) (bounds : 0≤v ∧ v<P) : r=v := by
    dsimp only [r]
    rw [eq,Int.add_mul_emod_self_right,Int.emod_eq_of_lt bounds.1 bounds.2]
  by_cases even : j%2=0
  · have jh : j=2*(j/2) := by omega
    have val : r=2*a-j := rem _ _ (by
      calc (j+2)*a = (2*(j/2)+2)*a := by rw [←jh]
        _ = 2*a-2*(j/2)+(j/2)*P := by rw [pg]; ring
        _ = 2*a-j+(j/2)*P := by rw [←jh]) (by omega)
    rw [val]
    split_ifs <;> norm_num <;> omega
  · have jh : j=2*(j/2)+1 := by omega
    have eq : (j+2)*a=(a-j-1)+(j/2+1)*P := by
      calc (j+2)*a=(2*(j/2)+1+2)*a := by rw [←jh]
        _=(a-(2*(j/2)+1)-1)+(j/2+1)*P := by rw [pg]; ring
        _=(a-j-1)+(j/2+1)*P := by rw [←jh]
    by_cases side : j<a
    · rw [rem _ _ eq (by omega)]
      split_ifs <;> norm_num <;> omega
    · have next : (j+2)*a=(P+a-j-1)+(j/2)*P := by rw [eq]; ring
      rw [rem _ _ next (by omega)]
      split_ifs <;> norm_num <;> omega

end BraunerBalancedWords

@[expose] public section
namespace BraunerBalancedWords

def mass (k : ℕ) (b : Fin 4) : ℤ := if b.val<2 then weight k else 1

def offset (k : ℕ) (b : Fin 4) : ℤ :=
  if b=0 then -weight k else if b=1 then -2*weight k else if b=2 then -3 else -weight k-3

theorem clocks {k : ℕ} (hk : 2≤k) (b : Fin 4) (x : ℤ) :
    0≤mass k b ∧ mass k b<(width k:ℤ) ∧
    (exampleWord k x=b ↔ (x*mass k b+offset k b+mass k b)%(width k)<mass k b) := by
  let a:=weight k
  let P:ℤ:=width k
  obtain ⟨ag,pg⟩:=parameters hk
  change 3≤a at ag
  change P=2*a+2 at pg
  have congruence (s : ℤ) : x ≡ s [ZMOD P] ↔ (x-s)%P<1 := by
    rw [Int.modEq_comm,Int.modEq_iff_dvd,Int.dvd_iff_emod_eq_zero]
    have :=Int.emod_nonneg (x-s) (by omega : P≠0)
    omega
  rcases common hk x with ⟨first,second⟩
  rcases rare hk x with ⟨third,fourth⟩
  fin_cases b
  · change 0≤a ∧ a<P ∧ (exampleWord k x=0 ↔ (x*a+-a+a)%P<a)
    simpa only [neg_add_cancel_right] using And.intro (by omega : 0≤a) (And.intro (by omega : a<P) first)
  · change 0≤a ∧ a<P ∧ (exampleWord k x=1 ↔ (x*a+-2*a+a)%P<a)
    rw [show x*a+-2*a+a=(x-1)*a by ring]
    exact ⟨by omega,by omega,second⟩
  · change 0≤(1:ℤ) ∧ 1<P ∧ (exampleWord k x=2 ↔ (x*1+-3+1)%P<1)
    rw [show x*1+-3+1=x-2 by ring,←congruence]
    exact ⟨by omega,by omega,third⟩
  · change 0≤(1:ℤ) ∧ 1<P ∧ (exampleWord k x=3 ↔ (x*1+(-a-3)+1)%P<1)
    rw [show x*1+(-a-3)+1=x-(a+2) by ring,←congruence]
    exact ⟨by omega,by omega,fourth⟩

private theorem crossing (z d P : ℤ) (hp : 0<P) (hd : 0≤d) (small : d<P) :
    z/P=(z-d)/P+(if z%P<d then 1 else 0) := by
  have r0:=Int.emod_nonneg z (by omega : P≠0)
  have r1:=Int.emod_lt_of_pos z hp
  have repr : z-d=(z/P)*P+(z%P-d) := by have r:=Int.emod_add_ediv_mul z P; omega
  rw [repr,Int.mul_add_ediv_right _ _ (by omega : P≠0)]
  by_cases low : z%P<d
  · have q : (z%P-d)/P= -1 := (Int.ediv_eq_iff_of_pos hp).mpr (by constructor <;> nlinarith)
    simp [low,q]
  · have q : (z%P-d)/P=0:=Int.ediv_eq_zero_of_lt (by omega) (by omega)
    simp [low,q]

theorem count_formula {k : ℕ} (hk : 2≤k) (b : Fin 4) (x : ℤ) (n : ℕ) :
    count (exampleWord k) b x n =
      ((x+n)*mass k b+offset k b)/(width k)-(x*mass k b+offset k b)/(width k) := by
  apply count_telescope (fun z => (z*mass k b+offset k b)/(width k))
  intro z
  obtain ⟨hd,hp,occ⟩:=clocks hk b z
  simp only [occ]
  rw [show (z+1)*mass k b+offset k b=z*mass k b+offset k b+mass k b by ring]
  simpa using crossing (z*mass k b+offset k b+mass k b) (mass k b) (width k) (by omega) hd hp

theorem balanced_example {k : ℕ} (hk : 2≤k) : Balanced (exampleWord k) := by
  intro b x y n
  rw [count_formula hk,count_formula hk]
  have one (s : ℤ) :
      (n:ℤ)*mass k b/(width k)≤((s+n)*mass k b+offset k b)/(width k)-(s*mass k b+offset k b)/(width k) ∧
      ((s+n)*mass k b+offset k b)/(width k)-(s*mass k b+offset k b)/(width k)≤(n:ℤ)*mass k b/(width k)+1 := by
    obtain ⟨hd,hp,_⟩:=clocks hk b s
    rw [show (s+n)*mass k b+offset k b=(s*mass k b+offset k b)+(n:ℤ)*mass k b by ring,
      Int.add_ediv_of_pos (by omega : (0:ℤ)<width k)]
    split <;> omega
  have :=one x
  have :=one y
  omega

theorem full_count {k : ℕ} (hk : 2≤k) (b : Fin 4) :
    count (exampleWord k) b 0 (width k)=mass k b := by
  rw [count_formula hk]
  simp only [zero_add,zero_mul]
  rw [Int.mul_add_ediv_left _ _ (by obtain ⟨_,P⟩:=parameters hk; dsimp [width]; omega)]
  omega

end BraunerBalancedWords
