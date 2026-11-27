module

public import conjectures.MarkovNearestFour.Statement
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace MarkovNearestFour

private theorem continuants_append (ds : List ℕ) (k : ℕ) :
    continuants (ds++[k]) =
      ((continuants ds).2,(k*(continuants ds).2.1+(continuants ds).1.1,
        k*(continuants ds).2.2+(continuants ds).1.2)) := by
  simp [continuants,List.foldl_append]

private theorem alternating (ds : List ℕ) :
    let (prev,cur) := continuants ds
    if ds.length%2=0 then cur.1*prev.2=cur.2*prev.1+1
    else cur.2*prev.1=cur.1*prev.2+1 := by
  induction ds using List.reverseRecOn with
  | nil => decide
  | append_singleton ds k ih =>
    rw [continuants_append]
    rcases h : continuants ds with ⟨⟨p,q⟩,b,a⟩
    rw [h] at ih
    change (if ds.length%2=0 then b*q=a*p+1 else a*p=b*q+1) at ih
    simp only [List.length_append,List.length_cons,List.length_nil]
    split at ih <;> rename_i parity
    · rw [ite_eq_right (show (ds.length+(0+1))%2≠0 by omega)]
      simp only [Nat.add_mul]
      nlinarith
    · rw [ite_eq_left (show (ds.length+(0+1))%2=0 by omega)]
      simp only [Nat.add_mul]
      nlinarith

private theorem previous_le {ds : List ℕ} (nonempty : ds≠[]) (pos : ∀ k∈ds,0<k) :
    (continuants ds).1.1≤(continuants ds).2.1 ∧
    (continuants ds).1.2≤(continuants ds).2.2 := by
  induction ds using List.reverseRecOn with
  | nil => contradiction
  | append_singleton ds k _ =>
    have hk : 1≤k := pos k (by simp)
    rw [continuants_append]
    exact ⟨by dsimp; nlinarith [Nat.mul_le_mul_right (continuants ds).2.1 hk],
      by dsimp; nlinarith [Nat.mul_le_mul_right (continuants ds).2.2 hk]⟩

private theorem coprime_of_det {a b p q : ℕ} (h : b*q=a*p+1 ∨ a*p=b*q+1) :
    a.Coprime b := by
  let d := a.gcd b
  have ha : d∣a*p := dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) _
  have hb : d∣b*q := dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) _
  change d=1
  apply Nat.dvd_one.mp
  rcases h with h|h
  · exact (Nat.dvd_add_right ha).1 (h ▸ hb)
  · exact (Nat.dvd_add_right hb).1 (h ▸ ha)

/-- Reflection of the penultimate convergent gives the first lattice line
above the Newton edge. Its equation is b i + a j = ab + 1. -/
theorem convergent_location {ds : List ℕ} (pos : ∀ k∈ds,0<k) {p q b a : ℕ}
    (hn : continuants ds=((p,q),(b,a))) (ha : 1<a) :
    a.Coprime b ∧
    if ds.length%2=0 then b*q+a*(b-p)=a*b+1 else b*(a-q)+a*p=a*b+1 := by
  have neq : ds≠[] := by
    rintro rfl
    simp [continuants] at hn
    omega
  have hpq := previous_le neq pos
  rw [hn] at hpq
  change p≤b ∧ q≤a at hpq
  have h := alternating ds
  rw [hn] at h
  change (if ds.length%2=0 then b*q=a*p+1 else a*p=b*q+1) at h
  split at h <;> rename_i parity
  · refine ⟨coprime_of_det (Or.inl h),?_⟩
    rw [ite_eq_left parity]
    have := congrArg (a*·) (Nat.sub_add_cancel hpq.1)
    simp only [Nat.mul_add] at this
    omega
  · refine ⟨coprime_of_det (Or.inr h),?_⟩
    rw [ite_eq_right parity]
    have := congrArg (b*·) (Nat.sub_add_cancel hpq.2)
    simp only [Nat.mul_add] at this
    rw [Nat.mul_comm b a] at this
    omega

end MarkovNearestFour
