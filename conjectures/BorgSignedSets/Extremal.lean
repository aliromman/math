import conjectures.BorgSignedSets.ActiveClass
import conjectures.BorgSignedSets.Rigidity
import conjectures.BorgSignedSets.WordCount

namespace BorgSignedSets

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

private def extendWord (B : Finset ι) (b : Word B k) : Cube ι (ZMod k) :=
  fun i => if hi : i ∈ B then b ⟨i, hi⟩ else 0

omit [Fintype ι] [NeZero k] in
@[simp] private theorem extendWord_mem (B : Finset ι) (b : Word B k) (i : B) :
    extendWord B b i = b i := by simp [extendWord]

private def wins (h : Cube ι (ZMod k) → ℚ) (B : Finset ι) : Finset (Word B k) :=
  Finset.univ.filter fun b => h (extendWord B b) = (k : ℚ)-1

omit [NeZero k] in
private theorem winning_card {α : Type*} [Fintype α] (h : α → ℚ)
    (hm : avg h = 0) (hr : ∀ x, h x = (k : ℚ)-1 ∨ h x = -1) :
    (Finset.univ.filter (fun x => h x = (k : ℚ)-1)).card * k = Fintype.card α := by
  have he (x) : h x = (if h x = (k : ℚ)-1 then (k : ℚ) else 0) - 1 := by
    by_cases pos : h x = (k : ℚ)-1
    · simp [pos]
    · rcases hr x with e | e
      · contradiction
      · rw [ite_eq_right pos, e]
        norm_num
  have sumzero : ∑ x, h x = 0 := by
    by_cases hn : Fintype.card α = 0
    · let _ := Fintype.card_eq_zero_iff.mp hn
      simp
    · have hn' : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast hn
      exact (div_eq_zero_iff.mp hm).resolve_right hn'
  rw [Finset.sum_congr rfl (fun x _ => he x)] at sumzero
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter] at sumzero
  exact_mod_cast (show
    ((Finset.univ.filter (fun x => h x = (k : ℚ)-1)).card * k : ℚ) = (Fintype.card α : ℚ) by
      simpa [nsmul_eq_mul] using sub_eq_zero.mp sumzero)

private theorem wins_size (h : Cube ι (ZMod k) → ℚ) (B : Finset ι) (hB : B.Nonempty)
    (dep : DependsOn B h) (hm : avg h = 0) (hr : ∀ x, h x = (k : ℚ)-1 ∨ h x = -1) :
    (wins h B).card = k ^ (B.card-1) := by
  have eqsets : extensions B (wins h B) = Finset.univ.filter (fun x => h x = (k : ℚ)-1) := by
    ext x
    have he : h (extendWord B (restrictWord B x)) = h x :=
      dep _ _ (fun i hi => by simp [extendWord, restrictWord, hi])
    simp [wins, he]
  have wc := winning_card h hm hr
  rw [← eqsets, card_extensions, Fintype.card_fun, ZMod.card] at wc
  have ble : B.card ≤ Fintype.card ι := B.card_le_univ
  have bn := Finset.card_pos.mpr hB
  have hh : (k^(B.card-1) * k^(Fintype.card ι-B.card)) * k = k^Fintype.card ι := by
    rw [← pow_add, ← pow_succ, show B.card-1+(Fintype.card ι-B.card)+1 = Fintype.card ι by omega]
  rw [← hh] at wc
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos k) _)
    (Nat.eq_of_mul_eq_mul_right (NeZero.pos k) wc)

omit [Fintype ι] [DecidableEq ι] [NeZero k] in
private theorem depends_mono {C B : Finset ι} {h : Cube ι (ZMod k) → ℚ}
    (dep : DependsOn C h) (hc : C ⊆ B) : DependsOn B h :=
  fun x y hxy => dep x y fun i hi => hxy i (hc hi)

private theorem impossible_disjoint (F : Finset (Finset ι)) (A : Family ι k)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h) (hk : 2 ≤ k)
    {C B : Finset ι} (dep : DependsOn C h) (dis : Disjoint C B) (hB : B ∈ F) :
    A B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have all (x : Cube ι (ZMod k)) : h x = (k : ℚ)-1 := by
    let y := C.piecewise x (extendWord B b)
    have e : h x = h y := dep _ _ (fun i hi => (Finset.piecewise_eq_of_mem _ _ _ hi).symm)
    rw [e]
    apply cert.forced B hB b hb
    intro i
    have no : i.val ∉ C := fun c => Finset.disjoint_left.mp dis c i.property
    simp [y, no]
  have he := cert.mean_zero
  rw [funext all, avg_const] at he
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  linarith

omit [Fintype ι] in
private theorem exists_support_of_max (F : Finset (Finset ι)) (hF : F.Nonempty)
    (hne : ∀ B ∈ F, B.Nonempty) (i : ι) (himax : ∀ q, degree F k q ≤ degree F k i) :
    ∃ B ∈ F, i ∈ B := by
  obtain ⟨B, hB⟩ := hF
  obtain ⟨q, hq⟩ := hne B hB
  have pos : 0 < degree F k q := by
    apply Finset.sum_pos'
    · intro _ _
      exact Nat.zero_le _
    · exact ⟨B, hB, by simp [hq, pow_pos (NeZero.pos k)]⟩
  by_contra! hn
  have he : degree F k i = 0 := Finset.sum_eq_zero (fun T ht => by simp [hn T ht])
  exact (ne_of_gt (pos.trans_le (himax q))) he

private theorem saturated (F : Finset (Finset ι)) (A : Family ι k) (h : Cube ι (ZMod k) → ℚ)
    (cert : SelectorFacts F A h) (hk : 2 ≤ k) (i : ι) (C : Finset ι)
    (same : ∀ q ∈ C, SameSupports F i q) (dep : DependsOn C h)
    (largest : degree F k i ≤ size F A) :
    ∀ B ∈ F, i ∈ B → A B = wins h B := by
  have inside {B : Finset ι} (hB : B ∈ F) (hb : i ∈ B) : C ⊆ B :=
    fun q hq => (same q hq B hB).mp hb
  have subset (B : Finset ι) (hB : B ∈ F) : A B ⊆ wins h B := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert.forced B hB b hb _
      (fun q => extendWord_mem B b q)⟩
  have cw {B : Finset ι} (hB : B ∈ F) (hb : i ∈ B) :
      (wins h B).card = k ^ (B.card-1) :=
    wins_size h B ⟨i, hb⟩ (depends_mono dep (inside hB hb)) cert.mean_zero cert.values
  have upper (B : Finset ι) (hB : B ∈ F) : (A B).card ≤ if i ∈ B then k ^ (B.card-1) else 0 := by
    by_cases hb : i ∈ B
    · simpa only [ite_eq_left hb, ← cw hB hb] using Finset.card_le_card (subset B hB)
    · have dis : Disjoint C B := Finset.disjoint_left.mpr fun q hq hqb =>
        hb ((same q hq B hB).mpr hqb)
      simp [hb, impossible_disjoint F A h cert hk dep dis hB]
  intro B hB hb
  apply Finset.eq_of_subset_of_card_le (subset B hB)
  rw [cw hB hb]
  by_contra! lt
  have bad : size F A < degree F k i :=
    Finset.sum_lt_sum upper ⟨B, hB, by simpa [hb] using lt⟩
  exact (not_lt_of_ge largest) bad

omit [Fintype ι] in
private theorem lifted_winner (h : Cube ι (ZMod k) → ℚ) {C B : Finset ι} (dep : DependsOn C h)
    (hc : C ⊆ B) (b : Word B k) :
    b ∈ wins h B ↔ (fun q : C => b ⟨q, hc q.property⟩) ∈ wins h C := by
  have he : h (extendWord B b) = h (extendWord C (fun q : C => b ⟨q, hc q.property⟩)) :=
    dep _ _ (fun q hq => by simp [extendWord, hq, hc hq])
  simp [wins, he]

omit [Fintype ι] in
private theorem local_intersection (F : Finset (Finset ι)) (A : Family ι k)
    (ha : Intersecting F A) (hk : 2 ≤ k) (h : Cube ι (ZMod k) → ℚ)
    {C B : Finset ι} (dep : DependsOn C h) (hc : C ⊆ B) (hB : B ∈ F)
    (sat : A B = wins h B) :
    ∀ x ∈ wins h C, ∀ y ∈ wins h C, ∃ q : C, x q = y q := by
  let _ : Fact (1 < k) := ⟨by omega⟩
  let lift (u : Word C k) (v : ZMod k) : Word B k := fun q =>
    if hq : q.val ∈ C then u ⟨q, hq⟩ else v
  have member (u : Word C k) (hu : u ∈ wins h C) (a : ZMod k) : lift u a ∈ A B := by
    rw [sat, lifted_winner h dep hc]
    simpa [lift] using hu
  intro x hx y hy
  obtain ⟨j, hj, hj', eq⟩ := ha B hB _ (member x hx 0) B hB _ (member y hy 1)
  by_cases c : j ∈ C
  · exact ⟨⟨j,c⟩, by simpa [lift, c] using eq⟩
  · simp [lift, c] at eq

theorem star_or_exception (F : Finset (Finset ι)) (A : Family ι k)
    (hk : 2 ≤ k) (hF : F.Nonempty) (hn : ∀ B ∈ F, B.Nonempty) (ha : Intersecting F A)
    (h : Cube ι (ZMod k) → ℚ) (cert : SelectorFacts F A h)
    (j : ι) (hmax : ∀ t, degree F k t ≤ degree F k j) (hext : degree F k j ≤ size F A) :
    IsStar F A ∨ Exceptional F k := by
  obtain ⟨i, C, hi, imax, same, dep⟩ := active_class F A h cert hk j hmax hext
  have sat := saturated F A h cert hk i C same dep ((hmax i).trans hext)
  obtain ⟨B, hB, hb⟩ := exists_support_of_max F hF hn i imax
  have inside (B : Finset ι) (hB : B ∈ F) (hb : i ∈ B) : C ⊆ B :=
    fun q hq => (same q hq B hB).mp hb
  let _ : Nonempty C := ⟨⟨i, hi⟩⟩
  have cw := wins_size h C ⟨i, hi⟩ dep cert.mean_zero cert.values
  have inter := local_intersection F A ha hk h dep (inside B hB hb) hB (sat B hB hb)
  rcases fullSupport_star k hk (wins h C) inter (by simpa using cw) with
    ⟨q, a, dictator⟩ | ⟨bin, triple⟩
  · left
    refine ⟨q, a, ?_⟩
    intro B hB b
    by_cases hb : i ∈ B
    · have cq := inside B hB hb
      rw [sat B hB hb, lifted_winner h dep cq, dictator]
      simp [cq q.property]
    · have dis : Disjoint C B := Finset.disjoint_left.mpr fun q hq hqb =>
        hb ((same q hq B hB).mpr hqb)
      have nq : q.val ∉ B := fun he => Finset.disjoint_left.mp dis q.property he
      simp [impossible_disjoint F A h cert hk dep dis hB, nq]
  · right
    have hcard : 2 < C.card := by
      simp only [Fintype.card_coe] at triple
      omega
    obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := Finset.two_lt_card_iff.mp hcard
    have du : degree F k u = degree F k i := by
      apply Finset.sum_congr rfl
      intro B hB
      simp only [(same u hu B hB).symm]
    exact ⟨bin, u, v, w, huv, huw, hvw,
      fun B hB => (same u hu B hB).symm.trans (same v hv B hB),
      fun B hB => (same u hu B hB).symm.trans (same w hw B hB),
      fun q => (imax q).trans du.ge⟩

end BorgSignedSets
