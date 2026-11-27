module

public import conjectures.BorgSignedSets.Bound

@[expose] public section
namespace BorgSignedSets

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

def DependsOn (C : Finset ι) (f : Cube ι κ → ℚ) : Prop :=
  ∀ x y, (∀ i ∈ C, x i = y i) → f x = f y

private theorem separated_two_values (C : Finset ι) (f g r : Cube ι κ → ℚ)
    (split : ∀ x, f x = g x + r x) (hg : DependsOn C g) (hr : DependsOn Cᶜ r)
    (u v : ℚ) (two : ∀ x, f x = u ∨ f x = v)
    (varies : ∃ a b, g a ≠ g b) : DependsOn C f := by
  have ranges (x y : Cube ι κ) : g x + r y = u ∨ g x + r y = v := by
    let z := C.piecewise x y
    have eg : g z = g x := hg z x (fun i hi => Finset.piecewise_eq_of_mem C x y hi)
    have er : r z = r y := hr z y (fun i hi =>
      Finset.piecewise_eq_of_notMem C x y (Finset.mem_compl.mp hi))
    simpa only [split, eg, er] using two z
  obtain ⟨a, b, hab⟩ := varies
  have constant (c d : Cube ι κ) : r c = r d := by
    rcases ranges a c with e₁ | e₁ <;> rcases ranges a d with e₂ | e₂ <;>
      rcases ranges b c with e₃ | e₃ <;> rcases ranges b d with e₄ | e₄ <;> grind
  intro x y hxy
  rw [split, split, hg x y hxy, constant x y]

variable {k : ℕ} [NeZero k]

/-- In an extremal family the selector is determined by one class of coordinates
that occur in exactly the same supports. All stars in this class are largest. -/
theorem active_class (F : Finset (Finset ι)) (A : Family ι k) (h : Cube ι (ZMod k) → ℚ)
    (cert : SelectorFacts F A h) (hk : 2 ≤ k) (j : ι)
    (hmax : ∀ t, degree F k t ≤ degree F k j) (hext : degree F k j ≤ size F A) :
    ∃ i : ι, ∃ C : Finset ι, i ∈ C ∧ (∀ t, degree F k t ≤ degree F k i) ∧
      (∀ q ∈ C, SameSupports F i q) ∧ DependsOn C h := by
  classical
  let e (S : Finset ι) := energy (component h S)
  have pos : 0 < energy h := by
    rw [cert.total_energy]
    exact_mod_cast (show 0 < (k : ℤ)-1 by omega)
  have exists_active : ∃ S, 0 < e S := by
    by_contra! hn
    have hn' := Finset.sum_nonpos (s := (Finset.univ : Finset (Finset ι))) (fun S _ => hn S)
    exact (not_le_of_gt pos) ((energy_components h).le.trans hn')
  have active_ne {S : Finset ι} (hs : 0 < e S) : S.Nonempty := by
    by_contra! he
    simp [e, he, energy, cert.mean_zero] at hs
  have degrees {T : Finset ι} (ht : 0 < e T) {i : ι} (hi : i ∈ T) :
      commonDegree F k T = degree F k i := by
    have he := positive_component_degree F A h cert j hmax hext hk ht
    exact (commonDegree_le F k hi).antisymm ((hmax i).trans he.ge)
  have same {T : Finset ι} (ht : 0 < e T) {u v : ι} (hu : u ∈ T) (hv : v ∈ T) :
      SameSupports F u v := by
    intro B hB
    exact ⟨fun hBu => commonDegree_incidence F hu (degrees ht hu) hB hBu hv,
      fun hBv => commonDegree_incidence F hv (degrees ht hv) hB hBv hu⟩
  obtain ⟨S, hs⟩ := exists_active
  obtain ⟨i, hi⟩ := active_ne hs
  let C := Finset.univ.filter fun q => SameSupports F i q
  have memC (q : ι) : q ∈ C ↔ SameSupports F i q := by simp [C]
  have sC : S ⊆ C := fun q hq => (memC q).mpr (same hs hi hq)
  have imax : degree F k i = degree F k j :=
    (degrees hs hi).symm.trans (positive_component_degree F A h cert j hmax hext hk hs)
  refine ⟨i, C, sC hi, fun t => (hmax t).trans imax.ge, fun q hq => (memC q).mp hq, ?_⟩
  let others := (Finset.univ : Finset (Finset ι)).filter fun T => ¬ T ⊆ C
  let r (x : Cube ι (ZMod k)) := ∑ T ∈ others, component h T x
  have heC : Finset.univ.filter (fun T : Finset ι => T ⊆ C) = C.powerset := by ext; simp
  have split (x : Cube ι (ZMod k)) : h x = sectionMean h C x + r x := by
    rw [sectionMean_components, ← heC]
    change h x = (∑ T with T ⊆ C, component h T x) + ∑ T with ¬ T ⊆ C, component h T x
    rw [Finset.sum_filter_add_sum_filter_not, ← sectionMean_univ h x, sectionMean_components,
      Finset.powerset_univ]
  have depC : DependsOn C (sectionMean h C) := by
    intro x y hxy
    simp only [sectionMean_components]
    exact Finset.sum_congr rfl fun T hT => component_depends h T
      (fun q hq => hxy q ((Finset.mem_powerset.mp hT) hq))
  have depRest : DependsOn Cᶜ r := by
    intro x y hxy
    apply Finset.sum_congr rfl
    intro T hT
    by_cases act : 0 < e T
    · apply component_depends
      intro q hq
      apply hxy q
      rw [Finset.mem_compl]
      intro hqC
      apply (Finset.mem_filter.mp hT).2
      intro u hu
      apply (memC u).mpr
      intro B hB
      exact ((memC q).mp hqC B hB).trans (same act hq hu B hB)
    · have zero := (energy_eq_zero (component h T)).mp
          ((not_lt.mp act).antisymm (energy_nonneg _))
      rw [zero, zero]
  have posC : 0 < energy (sectionMean h C) := by
    rw [energy_sectionMean]
    exact hs.trans_le (Finset.single_le_sum (fun T _ => energy_nonneg (component h T))
      (Finset.mem_powerset.mpr sC))
  have varies : ∃ x y, sectionMean h C x ≠ sectionMean h C y := by
    by_contra! hall
    let base : Cube ι (ZMod k) := fun _ => 0
    have hc : sectionMean h C = fun _ => sectionMean h C base := funext (hall · base)
    have bzero : sectionMean h C base = 0 := by
      have hh := (avg_sectionMean h C).trans cert.mean_zero
      rwa [hc, avg_const] at hh
    have ez := (energy_eq_zero (sectionMean h C)).mpr (fun x => (hall x base).trans bzero)
    exact (ne_of_gt posC) ez
  exact separated_two_values C h (sectionMean h C) r split depC depRest _ _ cert.values varies

end BorgSignedSets
