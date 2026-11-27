module

public import conjectures.LarsonPowerMap.PrimeCycle
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

@[expose] public section
open Finset
namespace LarsonPowerMap

/-- Try one changed length and one multiple of the lcm of the other lengths. -/
def options (n : ℕ) : Finset (ℕ × ℕ) :=
  (lengths n).biUnion fun k =>
    (((Icc 1 k).image fun j => (k,1+j*except n k))).filter
      fun z => z.2 < (lengths n).lcm id ∧ ¬ z.2 ≡ 1 [MOD k]

theorem mem_options {n k a : ℕ} :
    (k,a)∈options n ↔ 2≤a ∧ a<Monoid.exponent (Sn n) ∧ bad n a={k} := by
  constructor
  · intro h
    obtain ⟨l,hl,h⟩ := mem_biUnion.mp h
    obtain ⟨hm,he,ne⟩ := mem_filter.mp h
    obtain ⟨j,hj,e⟩ := mem_image.mp hm
    obtain rfl := congrArg Prod.fst e
    have ea : 1+j*except n l=a := congrArg Prod.snd e
    have pos := (mem_Icc.mp hj).1
    have low : 2≤a := by nlinarith [Nat.mul_pos pos (except_pos n l)]
    refine ⟨low,by simpa [exp_eq_lcm] using he,?_⟩
    ext i
    simp only [bad,mem_filter,mem_singleton]
    constructor
    · rintro ⟨hi,neq⟩
      by_contra split
      have di : i∣except n l := dvd_lcm (f:=id) (mem_erase.mpr ⟨split,hi⟩)
      have d : i∣a-1 := by rw [←ea]; simpa using di.trans (dvd_mul_left _ j)
      exact neq ((Nat.modEq_iff_dvd' (by omega : 1≤a)).mpr d).symm
    · rintro rfl
      exact ⟨hl,ne⟩
  · rintro ⟨lo,upper,only⟩
    have m : k∈bad n a := only ▸ mem_singleton_self k
    obtain ⟨hk,ne⟩ := mem_filter.mp m
    have d : except n k ∣ a-1 := by
      apply Finset.lcm_dvd
      intro i hi
      obtain ⟨different,inL⟩ := mem_erase.mp hi
      have e : a ≡ 1 [MOD i] := by
        by_contra h
        have inB : i∈bad n a := mem_filter.mpr ⟨inL,h⟩
        exact different (mem_singleton.mp (only ▸ inB))
      exact (Nat.modEq_iff_dvd' (by omega : 1≤a)).mp e.symm
    obtain ⟨j,hj⟩ := d
    have form : 1+j*except n k=a := by rw [mul_comm,←hj]; omega
    have nonzero : 1≤j := by
      by_contra! small
      have zero : j=0 := by omega
      rw [zero,zero_mul,add_zero] at form
      omega
    have pos := (mem_Icc.mp hk).1
    have pk := except_pos n k
    have bound : Monoid.exponent (Sn n) ≤ k*except n k := by
      rw [factor_except hk]
      exact Nat.le_of_dvd (Nat.mul_pos pos pk) (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    have jl : j≤k := by
      by_contra! large
      have := Nat.mul_le_mul_right (except n k) large.le
      omega
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr
      ⟨mem_image.mpr ⟨j,mem_Icc.mpr ⟨nonzero,jl⟩,Prod.ext rfl form⟩,by rwa [←exp_eq_lcm],ne⟩⟩

noncomputable def leastLoss (n : ℕ) : Finset (ℕ × ℕ) := (options n).filter
  fun z => ∀ w ∈ options n, loss z.1 z.2 ≤ loss w.1 w.2

noncomputable def optimalExponents (n : ℕ) : Finset ℕ := (leastLoss n).image Prod.snd

private theorem compare_options {n k a l b : ℕ} (hx : (k,a)∈options n) (hy : (l,b)∈options n) :
    N n a ≤ N n b ↔ loss l b ≤ loss k a := by
  obtain ⟨low,_,one⟩ := mem_options.mp hx
  obtain ⟨low',_,two⟩ := mem_options.mp hy
  have s := score_single (by omega : 1≤a) one
  have t := score_single (by omega : 1≤b) two
  have pos : (0:ℚ)<n.factorial := by positivity
  rw [← Nat.cast_le (α:=ℚ),s,t,mul_le_mul_iff_right₀ pos,sub_le_sub_iff_left]

private theorem exists_option_min {n : ℕ} (nonempty : (options n).Nonempty) :
    (leastLoss n).Nonempty := by
  obtain ⟨x,hx,h⟩ := Finset.exists_min_image (options n) (fun z => loss z.1 z.2) nonempty
  exact ⟨x,mem_filter.mpr ⟨hx,h⟩⟩

theorem counted {n : ℕ} (hn : 3≤n) : (optimalExponents n).Nonempty := by
  obtain ⟨a,k,lo,up,sing,_⟩ := strict_reference hn
  exact (exists_option_min ⟨(k,a),mem_options.mpr ⟨lo,up,sing⟩⟩).image _

set_option maxHeartbeats 1500000 in
theorem resolution : ExactAnswer optimalExponents := by
  intro n a
  by_cases small : n<3
  · have no : ∀ b, ¬ (2≤b ∧ b<Monoid.exponent (Sn n)) := by
      intro b
      rw [exp_eq_lcm]
      have bound : (lengths n).lcm id ≤ 2 := by interval_cases n <;> decide
      omega
    constructor
    · intro ha
      obtain ⟨⟨k,b⟩,h,rfl⟩ := mem_image.mp ha
      exact (no b ⟨(mem_options.mp (mem_filter.mp h).1).1,(mem_options.mp (mem_filter.mp h).1).2.1⟩).elim
    · exact fun h => (no a ⟨h.1,h.2.1⟩).elim
  have hn : 3≤n := by omega
  obtain ⟨r,p,rl,ru,rs,strict⟩ := strict_reference hn
  have ref : (p,r) ∈ options n := mem_options.mpr ⟨rl,ru,rs⟩
  have separated {b : ℕ} (bl : 2≤b) (bu : b<Monoid.exponent (Sn n))
      (h : ¬∃ k, bad n b={k}) : N n b<N n r := by
    have z := card_pos.mpr (bad_nonempty bl bu)
    have num : 2≤(bad n b).card := by
      have ne : (bad n b).card≠1 := fun e => h (card_eq_one.mp e)
      omega
    have bound := multi_bound (by omega : 0<n) num
    omega
  constructor
  · intro ha
    obtain ⟨⟨k,b⟩,h,rfl⟩ := mem_image.mp ha
    change (k,b) ∈ leastLoss n at h
    obtain ⟨good,best⟩ := mem_filter.mp h
    change ∀ w ∈ options n, loss k b ≤ loss w.1 w.2 at best
    obtain ⟨lo,up,_⟩ := mem_options.mp good
    refine ⟨lo,up,fun u bl bu => ?_⟩
    by_cases single : ∃ j, bad n u={j}
    · obtain ⟨j,hj⟩ := single
      have here : (j,u) ∈ options n := mem_options.mpr ⟨bl,bu,hj⟩
      exact (@compare_options n j u k b here good).mpr (best (j,u) here)
    · exact (separated bl bu single).le.trans ((@compare_options n p r k b ref good).mpr (best (p,r) ref))
  · rintro ⟨lo,up,best⟩
    have sing : ∃ k, bad n a={k} := by
      by_contra ne
      exact (separated lo up ne).not_ge (best r rl ru)
    obtain ⟨k,hk⟩ := sing
    have here : (k,a) ∈ options n := mem_options.mpr ⟨lo,up,hk⟩
    apply mem_image.mpr
    refine ⟨(k,a),mem_filter.mpr ⟨here,?_⟩,rfl⟩
    rintro ⟨j,b⟩ h
    obtain ⟨bl,bu,_⟩ := mem_options.mp h
    exact (@compare_options n j b k a h here).mp (best b bl bu)

/-- info: 'LarsonPowerMap.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end LarsonPowerMap
