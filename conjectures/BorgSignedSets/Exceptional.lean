module

public import conjectures.BorgSignedSets.Statement

/-! The binary majority construction in the exceptional case of Borg's conjecture. -/

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} [DecidableEq ι]

private def majority (a b c : ZMod 2) : Prop :=
  (a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0)

private theorem majority_agree :
    ∀ a b c d e f : ZMod 2, majority a b c → majority d e f → a = d ∨ b = e ∨ c = f := by
  grind [majority]

private theorem majority_flip :
    ∀ a b c : ZMod 2, majority a b c ↔ ¬ majority (a + 1) (b + 1) (c + 1) := by
  unfold majority
  decide

private def accepted (i j l : ι) (B : Finset ι) (b : Word B 2) : Prop :=
  ∃ hi : i ∈ B, ∃ hj : j ∈ B, ∃ hl : l ∈ B, majority (b ⟨i, hi⟩) (b ⟨j, hj⟩) (b ⟨l, hl⟩)

private noncomputable def majorityFamily (i j l : ι) : Family ι 2 := by
  classical
  exact fun B => Finset.univ.filter (accepted i j l B)

private theorem mem_majority {i j l : ι} {B : Finset ι} {b : Word B 2} :
    b ∈ majorityFamily i j l B ↔ accepted i j l B b := by
  classical
  simp [majorityFamily]

private theorem majority_intersecting (F : Finset (Finset ι)) (i j l : ι) :
    Intersecting F (majorityFamily i j l) := by
  intro B _ b hb C _ c hc
  obtain ⟨hi, hj, hl, hb⟩ := mem_majority.mp hb
  obtain ⟨hi', hj', hl', hc⟩ := mem_majority.mp hc
  rcases majority_agree _ _ _ _ _ _ hb hc with h | h | h
  · exact ⟨i, hi, hi', h⟩
  · exact ⟨j, hj, hj', h⟩
  · exact ⟨l, hl, hl', h⟩

private theorem majority_card {i j l : ι} {B : Finset ι}
    (hi : i ∈ B) (hj : j ∈ B) (hl : l ∈ B) :
    (majorityFamily i j l B).card = 2 ^ (B.card - 1) := by
  classical
  let P := accepted i j l B
  let flip (b : Word B 2) : Word B 2 := fun x => b x + 1
  have invol : Function.Involutive flip := by
    intro b
    funext x
    exact (by decide : ∀ a : ZMod 2, a + 1 + 1 = a) (b x)
  have hf (b : Word B 2) : P b ↔ ¬ P (flip b) := by
    simpa only [P, accepted, exists_prop_of_true hi, exists_prop_of_true hj,
      exists_prop_of_true hl, flip] using
      (majority_flip (b ⟨i, hi⟩) (b ⟨j, hj⟩) (b ⟨l, hl⟩))
  have equal : (Finset.univ.filter P).card = (Finset.univ.filter (fun b => ¬ P b)).card := by
    apply Finset.card_bijective flip invol.bijective
    intro b
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hf b
  have whole := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := P)
  have power : (2 : ℕ) ^ B.card = 2 ^ (B.card - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    have positive := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe] at whole
  change (Finset.univ.filter P).card = _
  omega

private theorem largest_used {F : Finset (Finset ι)} {i : ι}
    (hF : F.Nonempty) (hne : ∀ B ∈ F, B.Nonempty) (htop : ∀ q, degree F 2 q ≤ degree F 2 i) :
    ∃ B ∈ F, i ∈ B := by
  classical
  obtain ⟨B, hB⟩ := hF
  obtain ⟨q, hq⟩ := hne B hB
  by_contra! h
  have hi : degree F 2 i = 0 := by
    apply Finset.sum_eq_zero
    exact fun C hC => by simp [h C hC]
  have hp : 0 < degree F 2 q := by
    apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    exact ⟨B, hB, by simp [hq]⟩
  have := htop q
  omega

/-- A binary majority on three co-occurring largest-star coordinates gives a maximum nonstar. -/
theorem exceptional_witness {k : ℕ} [NeZero k] {F : Finset (Finset ι)}
    (hF : F.Nonempty) (hne : ∀ B ∈ F, B.Nonempty) (hexc : Exceptional F k) :
    ∃ A : Family ι k, Intersecting F A ∧ ¬ IsStar F A ∧ ∀ q, degree F k q ≤ size F A := by
  classical
  obtain ⟨rfl, i, j, l, hij, hil, hjl, hsj, hsl, htop⟩ := hexc
  refine ⟨majorityFamily i j l, majority_intersecting F i j l, ?_, ?_⟩
  · obtain ⟨B, hB, hi⟩ := largest_used hF hne htop
    have hj := (hsj B hB).mp hi
    have hl := (hsl B hB).mp hi
    rintro ⟨p, a, hstar⟩
    let b : Word B 2 := fun x => if x.val = p then a + 1 else 0
    have hb : majority (b ⟨i, hi⟩) (b ⟨j, hj⟩) (b ⟨l, hl⟩) := by
      by_cases hip : i = p
      · subst p
        exact Or.inr (Or.inr ⟨by simp [b, hij.symm], by simp [b, hil.symm]⟩)
      by_cases hjp : j = p
      · subst p
        exact Or.inr (Or.inl ⟨by simp [b, hip], by simp [b, hjl.symm]⟩)
      exact Or.inl ⟨by simp [b, hip], by simp [b, hjp]⟩
    obtain ⟨hp, he⟩ := (hstar B hB b).mp (mem_majority.mpr ⟨hi, hj, hl, hb⟩)
    simp [b] at he
  · have eq : size F (majorityFamily i j l) = degree F 2 i := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hi : i ∈ B
      · simp only [hi, ↓reduceIte]
        exact majority_card hi ((hsj B hB).mp hi) ((hsl B hB).mp hi)
      · simp only [hi, ↓reduceIte, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨h, _⟩ := mem_majority.mp hb
        exact hi h
    exact fun q => eq ▸ htop q

end BorgSignedSets
