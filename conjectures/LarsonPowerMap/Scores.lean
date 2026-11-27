module

public import conjectures.LarsonPowerMap.Powers
public import conjectures.LarsonPowerMap.CycleCounts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
open Finset Function
namespace LarsonPowerMap

/-- The proportion of components lost when only the cycles of length k change. -/
noncomputable def loss (k a : ℕ) : ℚ := (1-(orderOf (a : ZMod k) : ℚ)⁻¹)/k

theorem single_bounds {n a k : ℕ} (h : bad n a = {k}) : 2≤k ∧ k≤n ∧ n<2*k := by
  have mem : k ∈ bad n a := h ▸ mem_singleton_self k
  obtain ⟨hk,ne⟩ := mem_filter.mp mem
  obtain ⟨pos,upper⟩ := mem_Icc.mp hk
  have two : 2≤k := by
    contrapose! ne
    have : k=1 := by omega
    simp [this,Nat.ModEq,Nat.mod_one]
  refine ⟨two,upper,?_⟩
  by_contra! ht
  have hm : 2*k ∈ bad n a := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, ht⟩,
    fun e => ne (e.of_dvd (dvd_mul_left k 2))⟩
  rw [h,mem_singleton] at hm
  omega

theorem score_single {n a k : ℕ} (ha : 1≤a) (hb : bad n a={k}) :
    (N n a : ℚ) = n.factorial * (1-loss k a) := by
  classical
  obtain ⟨two,up,long⟩ := single_bounds hb
  let T := univ.filter (fun x : Sn n => k ∈ x.cycleType)
  have size : T.card*k = n.factorial := by
    have main := card_hasCycle_mul (α:=Fin n) (k:=k) (by simp; omega) (by simpa)
    simp only [Fintype.card_fin] at main
    rw [←main]
    apply congrArg (fun s : Finset (Sn n) => s.card*k)
    ext x
    simp [T,hasCycle_iff_mem_cycleType two]
  let T' := univ.filter (fun x : Sn n => k ∉ x.cycleType)
  have total : T.card+T'.card=n.factorial := by
    simpa [T,T',Fintype.card_perm] using card_filter_add_card_filter_not
      (s:=(univ : Finset (Sn n))) (fun x => k ∈ x.cycleType)
  have count : (N n a : ℚ) =
      ∑ x : Sn n, if k ∈ x.cycleType then (orderOf (a : ZMod k) : ℚ)⁻¹ else 1 := by
    unfold N
    rw [componentCount_eq_sum_inv_period]
    apply sum_congr rfl
    intro x _
    rw [minimalPeriod_single ha hb]
    split <;> simp
  rw [count,sum_ite]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  change (T.card : ℚ)*(orderOf (a : ZMod k) : ℚ)⁻¹ + T'.card = _
  have eq₁ : (T.card : ℚ)*k = n.factorial := by exact_mod_cast size
  have eq₂ : (T.card : ℚ)+T'.card = n.factorial := by exact_mod_cast total
  have ne : (k : ℚ)≠0 := by exact_mod_cast (by omega : k≠0)
  unfold loss
  let r := (orderOf (a : ZMod k) : ℚ)⁻¹
  have cancel : (n.factorial : ℚ)*((1-r)/k) = T.card*(1-r) := by
    rw [←eq₁]
    field_simp
  change (T.card : ℚ)*r+T'.card = n.factorial*(1-(1-r)/k)
  rw [mul_sub,mul_one,cancel]
  linarith

/-- Two exceptional lengths already force the loss of at least (n−1)! components. -/
theorem multi_bound {n a : ℕ} (hn : 0<n) (hb : 2≤(bad n a).card) :
    N n a + (n-1).factorial ≤ n.factorial := by
  classical
  let o : Fin n := ⟨0,hn⟩
  let L (x : Sn n) := cycleLength x o
  let s := univ.filter (fun x => L x ∈ bad n a)
  have counts {k} (hk : k ∈ bad n a) :
      (s.filter (fun x => L x=k)).card = (n-1).factorial := by
    obtain ⟨lo,up⟩ := mem_Icc.mp (mem_filter.mp hk).1
    have eq : s.filter (fun x => L x=k) = univ.filter (fun x => L x=k) := by
      ext x
      simp only [s,mem_filter,mem_univ,true_and,and_iff_right_iff_imp]
      exact fun e => e ▸ hk
    rw [eq]
    simpa [L] using (card_cycleLength o lo (by simpa))
  have size : s.card=(bad n a).card*(n-1).factorial := by
    rw [card_eq_sum_card_fiberwise (s:=s) (f:=L) (t:=bad n a) (fun _ h => (mem_filter.mp h).2)]
    exact (sum_congr rfl (fun k hk => counts hk)).trans (by simp)
  let f (x : Sn n) := x^a
  have sub : s ⊆ moved f := by
    intro x hx
    have ne := (mem_filter.mp (mem_filter.mp hx).2).2
    simp only [moved,mem_filter,mem_univ,true_and]
    intro eq
    apply ne
    have e : x^a = x^1 := by simpa [f] using eq
    exact (pow_eq_pow_iff_modEq.mp e).of_dvd (cycleLength_dvd_orderOf x o)
  have le := card_le_card sub
  have m : 2*(n-1).factorial ≤ s.card := by rw [size]; gcongr
  have total : (moved f).card + 2 * N n a ≤ 2 * n.factorial := by
    simpa [N,f,Fintype.card_perm] using moved_bound f
  omega

end LarsonPowerMap
