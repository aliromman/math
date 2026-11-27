module

public import Mathlib.Combinatorics.Additive.CauchyDavenport

@[expose] public section
open scoped Pointwise

namespace BajnokRestrictedMinimum

private abbrev H := ZMod 12
private abbrev K := ZMod 37
private abbrev G := H × K

private def support (A : Finset G) : Finset H := A.image Prod.fst

private def fiber (A : Finset G) (x : H) : Finset K :=
  (A.filter fun u => u.1=x).image Prod.snd

private theorem mem_fiber (A : Finset G) (x : H) (y : K) :
    y ∈ fiber A x ↔ (x,y) ∈ A := by
  simp [fiber, Finset.mem_image, Prod.exists]

private theorem mem_support (A : Finset G) (x : H) :
    x ∈ support A ↔ (fiber A x).Nonempty := by
  simp [support, Finset.Nonempty, mem_fiber, Prod.exists]

private theorem count_fibers (A : Finset G) :
    ∑ x ∈ support A, (fiber A x).card = A.card := by
  conv_rhs => rw [Finset.card_eq_sum_card_image Prod.fst A]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.card_image_of_injOn
  intro u hu v hv he
  exact Prod.ext ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm) he

private theorem add_fibers (A : Finset G) (x y : H) :
    fiber A x + fiber A y ⊆ fiber (A+A) (x+y) := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hw
  exact (mem_fiber _ _ _).mpr (Finset.mem_add.mpr
    ⟨(x,a), (mem_fiber _ _ _).mp ha, (y,b), (mem_fiber _ _ _).mp hb, rfl⟩)

private theorem add_support (A : Finset G) : support (A+A) = support A + support A := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (mem_support (A+A) z).mp hz
    obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp ((mem_fiber _ _ _).mp hw)
    apply Finset.mem_add.mpr
    exact ⟨u.1, Finset.mem_image_of_mem _ hu, v.1, Finset.mem_image_of_mem _ hv,
      congrArg Prod.fst he⟩
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a,ha⟩ := (mem_support A x).mp hx
    obtain ⟨b,hb⟩ := (mem_support A y).mp hy
    exact (mem_support _ _).mpr ⟨a+b, add_fibers A x y (Finset.mem_add.mpr ⟨a,ha,b,hb,rfl⟩)⟩

private theorem fiber_growth (A : Finset G) (hA : A.card = 19)
    (x y : H) (hx : x ∈ support A) (hy : y ∈ support A) :
    (fiber A x).card + (fiber A y).card - 1 ≤ (fiber (A+A) (x+y)).card := by
  have bound (i : H) : (fiber A i).card ≤ 19 := by
    rw [← hA]
    exact (Finset.card_image_le.trans (Finset.card_filter_le ..))
  have hab := ZMod.cauchy_davenport (by decide : Nat.Prime 37)
    ((mem_support _ _).mp hx) ((mem_support _ _).mp hy)
  rw [min_eq_right (by have := bound x; have := bound y; omega)] at hab
  exact hab.trans (Finset.card_le_card (add_fibers _ _ _))

private theorem shift_subset (S : Finset H) {x : H} (hx : x ∈ S) :
    S.image (x+·) ⊆ S+S := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_add.mpr ⟨x,hx,z,hz,rfl⟩

private theorem growth_bound (A : Finset G) (hA : A.card = 19) (x : H) (hx : x ∈ support A) :
    19 + (support A).card * ((fiber A x).card-1) +
      ((support A+support A).card-(support A).card) ≤ (A+A).card := by
  let S := support A
  let T := S.image (x+·)
  let F := fun z => (fiber (A+A) z).card
  have hsub : T ⊆ support (A+A) := (add_support A) ▸ shift_subset S hx
  have hT : T.card = S.card := Finset.card_image_of_injective _ (add_right_injective x)
  have hsum : 19 + S.card*((fiber A x).card-1) ≤ ∑ z ∈ T, F z := by
    rw [Finset.sum_image (fun _ _ _ _ e => add_left_cancel e)]
    have hg : ∀ y ∈ S, (fiber A y).card + ((fiber A x).card-1) ≤ F (x+y) := by
      intro y hy
      have h := fiber_growth A hA x y hx hy
      have hx' := Finset.card_pos.mpr ((mem_support _ _).mp hx)
      dsimp [F]
      omega
    have he := Finset.sum_le_sum hg
    simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, count_fibers, S, hA] using he
  have rest : (support (A+A) \ T).card ≤ ∑ z ∈ support (A+A) \ T, F z := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro z hz
    exact Finset.card_pos.mpr ((mem_support _ _).mp (Finset.mem_sdiff.mp hz).1)
  have join := Finset.sum_sdiff hsub (f := F)
  rw [Finset.card_sdiff_of_subset hsub, hT] at rest
  have denom : ∑ z ∈ support (A+A), F z = (A+A).card := count_fibers _
  change 19 + S.card * ((fiber A x).card-1) + ((S+S).card-S.card) ≤ _
  have hsize : (support (A+A)).card = (S+S).card := congrArg Finset.card (add_support A)
  rw [hsize] at rest
  omega

private theorem dense_sums (S : Finset H) (hS : 7 ≤ S.card) : S+S = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro z
  let T := S.image (z-·)
  have ht : T.card = S.card := Finset.card_image_of_injective _ sub_right_injective
  have meet : ¬ Disjoint S T := by
    intro h
    have lim := (S ∪ T).card_le_univ
    rw [Finset.card_union_of_disjoint h, ht, ZMod.card] at lim
    omega
  obtain ⟨x,hx,hx'⟩ := Finset.not_disjoint_iff.mp meet
  obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hx'
  exact Finset.mem_add.mpr ⟨x,hx,y,hy,sub_eq_iff_eq_add.mp e |>.symm⟩

private theorem five_sums (S : Finset H) (hs : S.card = 5) : 6 ≤ (S+S).card := by
  by_contra! small
  have eq (x : H) (hx : x ∈ S) : S.image (x+·) = S+S := by
    apply Finset.eq_of_subset_of_card_le (shift_subset S hx)
    rw [Finset.card_image_of_injective _ (add_right_injective x), hs]
    omega
  have elem_sum (x : H) (hx : x ∈ S) : ∑ z ∈ S+S, z = 5*x+∑ z ∈ S, z := by
    rw [← eq x hx, Finset.sum_image (fun _ _ _ _ e => add_left_cancel e),
      Finset.sum_add_distrib, Finset.sum_const, hs]
    simp [nsmul_eq_mul]
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have e := add_right_cancel ((elem_sum a ha).symm.trans (elem_sum b hb))
  have twice := congrArg (fun z : H => 5*z) e
  change (5:H)*(5*a) = 5*(5*b) at twice
  rw [← mul_assoc, ← mul_assoc, show (5:H)*5=1 by decide, one_mul, one_mul] at twice
  exact hab twice

private theorem two_per_fiber (A : Finset G) (hA : A.card = 19)
    (hm : ∀ y ∈ support A, (fiber A y).card ≤ 2) : 36 ≤ (A+A).card := by
  let S := support A
  let D := S.filter fun y => 2 ≤ (fiber A y).card
  have hd : D ⊆ S := Finset.filter_subset _ _
  have u : ∑ y ∈ D, (fiber A y).card ≤ D.card*2 := by
    calc _ ≤ ∑ _ ∈ D, 2 := Finset.sum_le_sum fun y hy => hm y (hd hy)
         _ = _ := by simp
  have w : ∑ y ∈ S \ D, (fiber A y).card ≤ (S\D).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro y hy
    have ⟨hyS,hn⟩ := Finset.mem_sdiff.mp hy
    have hh : ¬ 2 ≤ (fiber A y).card := fun he => hn (Finset.mem_filter.mpr ⟨hyS,he⟩)
    omega
  have tot := Finset.sum_sdiff (f := fun y => (fiber A y).card) hd
  have ct : ∑ y ∈ S, (fiber A y).card = 19 := (count_fibers A).trans hA
  have sz : S.card ≤ 12 := by simpa using S.card_le_univ
  rw [Finset.card_sdiff_of_subset hd] at w
  have d7 : 7 ≤ D.card := by omega
  have sums := dense_sums D d7
  have high (z : H) : 3 ≤ (fiber (A+A) z).card := by
    have hz : z ∈ D+D := sums ▸ Finset.mem_univ z
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hh := fiber_growth A hA x y (hd hx) (hd hy)
    omega
  have full : support (A+A) = Finset.univ := Finset.eq_univ_of_forall fun z =>
    (mem_support _ _).mpr (Finset.card_pos.mp (lt_of_lt_of_le (by decide) (high z)))
  have all := count_fibers (A+A)
  rw [full] at all
  calc 36 = ∑ _ ∈ (Finset.univ : Finset H), 3 := by simp
       _ ≤ ∑ z ∈ Finset.univ, (fiber (A+A) z).card := Finset.sum_le_sum fun z _ => high z
       _ = _ := all

private theorem small_cases (r m : ℕ) (hr : r ≤ 12) (capacity : 19 ≤ r*m)
    (small : r*(m-1) < 16) : m=2 ∨ (r=7 ∧ m=3) ∨ (r=5 ∧ m=4) := by
  have hm : 2 ≤ m := by
    by_contra! h
    have hle := Nat.mul_le_mul_left r (show m ≤ 1 by omega)
    simp only [Nat.mul_one] at hle
    omega
  by_cases h : m ≤ 4
  · rcases (show m=2 ∨ m=3 ∨ m=4 by omega) with rfl | rfl | rfl <;> omega
  · have he : r*m = r*(m-1)+r := by
      rw [← Nat.mul_succ, show (m-1).succ = m by omega]
    have hbig := Nat.mul_le_mul (by omega : 4 ≤ r) (by omega : 4 ≤ m-1)
    omega

private theorem product_lower (A : Finset G) (hA : A.card = 19) : 35 ≤ (A+A).card := by
  have hn : (support A).Nonempty := (Finset.card_pos.mp (by omega : 0 < A.card)).image _
  obtain ⟨x,hx,maximal⟩ := Finset.exists_max_image (support A) (fun z => (fiber A z).card) hn
  let r := (support A).card
  let m := (fiber A x).card
  have hc := Finset.sum_le_sum maximal
  rw [count_fibers, hA, Finset.sum_const, smul_eq_mul] at hc
  change 19 ≤ r*m at hc
  have hr : r ≤ 12 := by simpa [r] using (support A).card_le_univ
  have bound := growth_bound A hA x hx
  change 19+r*(m-1)+((support A+support A).card-r) ≤ _ at bound
  by_cases done : 16 ≤ r*(m-1)
  · omega
  rcases small_cases r m hr hc (by omega) with hm | ⟨hr7,hm⟩ | ⟨hr5,hm⟩
  · apply le_trans (by decide : 35 ≤ 36)
    apply two_per_fiber A hA
    intro y hy
    exact (maximal y hy).trans hm.le
  · have eq := dense_sums (support A) (by change 7 ≤ r; omega)
    rw [eq, Finset.card_univ, ZMod.card, hr7, hm] at bound
    omega
  · have hs := five_sums (support A) hr5
    rw [hr5, hm] at bound
    omega

/-- Every ordinary double sumset of nineteen residues modulo 444 has at least
35 elements. The bound suffices to distinguish the conjectured minimum. -/
theorem ordinary_lower (A : Finset (ZMod 444)) (hA : A.card = 19) : 35 ≤ (A+A).card := by
  let e : ZMod 444 ≃+* G := ZMod.chineseRemainder (m := 12) (n := 37) (by decide)
  let B := A.image e
  have hB : B.card = 19 := (Finset.card_image_of_injective _ e.injective).trans hA
  have he : B+B = (A+A).image e := by
    ext z
    constructor
    · intro h
      obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨a+b,Finset.mem_add.mpr ⟨a,ha,b,hb,rfl⟩,map_add e _ _⟩
    · intro h
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hy
      exact Finset.mem_add.mpr ⟨e a,Finset.mem_image_of_mem _ ha,
        e b,Finset.mem_image_of_mem _ hb,(map_add e _ _).symm⟩
  have bound := product_lower B hB
  rwa [he, Finset.card_image_of_injective _ e.injective] at bound

end BajnokRestrictedMinimum
