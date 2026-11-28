module

public import conjectures.BorgSignedSets.Bound
public import conjectures.BorgSignedSets.WordCount

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

/-- Each translated cylinder contributes a known square to the section energy. -/
theorem section_bound_of_label (F : Finset (Finset ι)) (A : Family ι k) (hk : 2 ≤ k)
    (L : Cube ι (ZMod k) → ZMod k)
    (hshift : ∀ t x, L (shiftWord t x) = L x + t)
    (hforce : ∀ B ∈ F, ∀ b ∈ A B, ∀ x : Cube ι (ZMod k),
      (∀ i : B, x i = b i) → L x = 0) (B : Finset ι) (hB : B ∈ F) (hne : B.Nonempty) :
    ((A B).card : ℚ) * ((k : ℚ)-1) ≤ (k^(B.card-1) : ℕ) *
      energy (sectionMean (fun x => orbitScore k (L x)) B) := by
  classical
  let E := extensions B (A B)
  let f := sectionMean (fun x => orbitScore k (L x)) B
  let translate (u : E × ZMod k) : Cube ι (ZMod k) := shiftWord u.2 u.1.val
  have belongs (x : E) : restrictWord B x.val ∈ A B := by
    simpa [E, extensions] using x.property
  have zero (x : E) : L x.val = 0 :=
    hforce B hB _ (belongs x) _ (fun _ => rfl)
  have label (u : E × ZMod k) : L (translate u) = u.2 := by
    simp only [translate, hshift, zero, zero_add]
  have inject : Function.Injective translate := by
    rintro ⟨x,t⟩ ⟨y,s⟩ h
    have hts : t = s := by simpa only [label] using congrArg L h
    subst s
    congr 1
    apply Subtype.ext
    funext j
    exact add_right_cancel (congrFun h j)
  have value (u : E × ZMod k) : f (translate u) = orbitScore k u.2 := by
    apply sectionMean_const
    intro y hy
    have hz : L (shiftWord (-u.2) y) = 0 := by
      apply hforce B hB (restrictWord B u.1.val) (belongs u.1)
      intro j
      have hj := hy j.val j.property
      change y j.val = u.1.val j.val + u.2 at hj
      change y j.val + -u.2 = u.1.val j.val
      simp [hj]
    rw [hshift] at hz
    exact congrArg (orbitScore k) (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz))
  have subset_bound : (∑ u : E × ZMod k, (f (translate u))^2) ≤ ∑ x, (f x)^2 := by
    calc
      _ = ∑ x ∈ Finset.univ.image translate, (f x)^2 := (Finset.sum_image inject.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg (f x))
  have total : (E.card : ℚ) * ((k : ℚ)*((k:ℚ)-1)) ≤ ∑ x, (f x)^2 := by
    simpa only [value, Fintype.sum_prod_type, sum_orbitScore_sq,
      Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using subset_bound
  have hcard : E.card = (A B).card * k^(Fintype.card ι - B.card) := by
    exact card_extensions B (A B)
  have hsplit : Fintype.card ι = (B.card-1) + (Fintype.card ι-B.card) + 1 := by
    have := Finset.card_le_univ B
    have := Finset.card_pos.mpr hne
    omega
  have hpow : (k : ℚ)^(Fintype.card ι) = (k : ℚ)^(B.card-1) * (k : ℚ)^(Fintype.card ι-B.card) * k := by
    calc
      _ = (k : ℚ)^((B.card-1) + (Fintype.card ι-B.card) + 1) := congrArg _ hsplit
      _ = _ := by rw [pow_succ, pow_add]
  change ((A B).card : ℚ) * ((k:ℚ)-1) ≤ (k^(B.card-1) : ℕ) * energy f
  simp only [energy, avg, Cube, Fintype.card_fun, ZMod.card, Nat.cast_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos (by exact_mod_cast (show 0 < k by omega)) _)).2
  calc
    _ = (k : ℚ)^(B.card-1) * ((E.card : ℚ) * ((k:ℚ)*((k:ℚ)-1))) := by
      rw [hpow, hcard, Nat.cast_mul, Nat.cast_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left total (by positivity)

end BorgSignedSets
