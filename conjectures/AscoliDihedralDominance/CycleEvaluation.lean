module

public import conjectures.AscoliDihedralDominance.Weighted

@[expose] public section
open Function Finset Equiv
namespace AscoliDihedral

def weightedPair (B : ℕ) : ℕ → ℕ × ℕ
  | 0 => (2,1)
  | k+1 => let t := weightedPair B k; (t.2,B*t.1+t.2)

theorem weightedPair_eq (B k : ℕ) :
    weightedPair B k = (cycleWeight B k,cycleWeight B (k+1)) := by
  induction k with
  | zero => rfl
  | succ k h => rw [weightedPair,h]; rfl

variable {X : Type*} [Fintype X] [DecidableEq X]

def firstReturn (p : X → X) (x : X) : ℕ → X → ℕ
  | 0,_ => 0
  | k+1,y => if p y=x then 1 else firstReturn p x k (p y) + 1

omit [Fintype X] in
private theorem firstReturn_eq (p : X → X) (x y : X) (d k : ℕ) (hd : d+1≤k)
    (hh : p^[d+1] y=x) (hm : ∀ i : ℕ, (0 < i) → (i < d+1) → p^[i] y ≠ x) : firstReturn p x k y = d+1 := by
  induction d generalizing y k with
  | zero =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    have h : p y=x := by simpa using hh
    simp [firstReturn,h]
  | succ d ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    have hn : p y≠x := by simpa using hm 1 (by decide) (by omega)
    simp only [firstReturn,hn,ite_false]
    rw [ih (p y) j (by omega)]
    · simpa only [iterate_succ_apply] using hh
    · intro i hi hi'
      simpa only [iterate_succ_apply] using hm (i+1) (by omega) (by omega)

def periodValue (p : Perm X) (x : X) : ℕ := firstReturn p x (Fintype.card X) x

theorem periodValue_eq (p : Perm X) (x : X) : periodValue p x = period p x := by
  have hn := period_pos p x
  have hle : period p x≤Fintype.card X := minimalPeriod_le_card
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [hd]
  apply firstReturn_eq _ _ _ _ _ (by omega)
  · change (⇑p)^[d.succ] x=x
    rw [←hd]
    exact isPeriodicPt_minimalPeriod _ _
  · intro i hi hi' he
    have hdiv := (isPeriodicPt_iff_minimalPeriod_dvd (f := (⇑p)) (x := x)).mp he
    have hlt : period p x ≤ i := Nat.le_of_dvd hi hdiv
    omega

/-- The number of points of a given period divided by that period counts its cycles. -/
def evaluatePerm (B : ℕ) (p : Perm X) : ℕ :=
  ∏ k ∈ univ.image (periodValue p),
    (weightedPair B k).1 ^ ((univ.filter fun x => periodValue p x=k).card / k)

theorem evaluatePerm_eq (B : ℕ) (p : Perm X) : evaluatePerm B p = weightPerm B p := by
  classical
  rw [weighted_cycle_factors,evaluatePerm]
  have fm (q : Orbit p) (_ : q∈(univ : Finset (Orbit p))) :
      period p q.out ∈ univ.image (periodValue p) :=
    mem_image.mpr ⟨q.out,mem_univ _,periodValue_eq p q.out⟩
  rw [←Finset.prod_fiberwise_of_maps_to' fm (cycleWeight B)]
  apply prod_congr rfl
  intro k hk
  have hcount : (univ.filter (fun x => periodValue p x = k)).card =
      (univ.filter (fun q : Orbit p => period p q.out=k)).card*k := by
    simp_rw [periodValue_eq]
    rw [card_filter,←(orbitEquiv p).sum_comp (fun x => if period p x = k then 1 else 0),Fintype.sum_sigma]
    simp_rw [orbit_period]
    rw [card_filter,sum_mul]
    apply sum_congr rfl
    intro q _
    split_ifs with he <;> simp_all
  obtain ⟨x,_,hx⟩ := mem_image.mp hk
  have hpos : 0<k := by rw [←hx,periodValue_eq]; exact period_pos _ _
  rw [hcount,Nat.mul_div_cancel _ hpos,weightedPair_eq]
  simp

end AscoliDihedral
