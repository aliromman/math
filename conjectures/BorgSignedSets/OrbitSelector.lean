module

public import conjectures.BorgSignedSets.WordCount
public import Mathlib.Tactic.Abel

@[expose] public section
namespace BorgSignedSets

variable {ι : Type*} {k : ℕ}

private def occupied (F : Finset (Finset ι)) (A : Family ι k) (x : Cube ι (ZMod k)) : Prop :=
  ∃ B ∈ F, restrictWord B x ∈ A B

private theorem unique_shift (F : Finset (Finset ι)) (A : Family ι k) (hA : Intersecting F A)
    (x : Cube ι (ZMod k)) (s t : ZMod k)
    (hs : occupied F A (shiftWord s x)) (ht : occupied F A (shiftWord t x)) : s=t := by
  obtain ⟨B,hB,hb⟩ := hs
  obtain ⟨C,hC,hc⟩ := ht
  obtain ⟨i,_,_,eq⟩ := hA B hB _ hb C hC _ hc
  exact add_left_cancel (show x i+s=x i+t from eq)

private noncomputable def chosen (F : Finset (Finset ι)) (A : Family ι k) (x : Cube ι (ZMod k)) :
    ZMod k := by
  classical
  exact if h : ∃ t, occupied F A (shiftWord t x) then h.choose else 0

private theorem chosen_eq (F : Finset (Finset ι)) (A : Family ι k) (hA : Intersecting F A)
    (x : Cube ι (ZMod k)) (t : ZMod k) (h : occupied F A (shiftWord t x)) :
    chosen F A x = t := by
  classical
  have exists' : ∃ s, occupied F A (shiftWord s x) := ⟨t,h⟩
  simp only [chosen, dite_eq_left_of_eq_true (eq_true exists')]
  exact unique_shift F A hA x _ t exists'.choose_spec h

/-- Assign labels equivariantly to all full words. Every word extending a
selected partial word receives label zero. -/
theorem exists_orbit_label (i₀ : ι) (F : Finset (Finset ι)) (A : Family ι k)
    (hA : Intersecting F A) :
    ∃ L : Cube ι (ZMod k) → ZMod k, (∀ t x, L (shiftWord t x) = L x + t) ∧
      ∀ B ∈ F, ∀ b ∈ A B, ∀ x : Cube ι (ZMod k), (∀ i : B, x i=b i) → L x=0 := by
  let base := fun (x : Cube ι (ZMod k)) (i : ι) => x i - x i₀
  let L := fun x : Cube ι (ZMod k) => x i₀ - chosen F A (base x)
  refine ⟨L, ?_, ?_⟩
  · intro t x
    have he : base (shiftWord t x) = base x := by
      funext i
      change x i + t - (x i₀+t) = x i-x i₀
      abel
    change x i₀+t-chosen F A (base (shiftWord t x)) = x i₀-chosen F A (base x)+t
    rw [he]
    abel
  · intro B hB b hb x hx
    have he : shiftWord (x i₀) (base x) = x := by
      funext i
      exact sub_add_cancel _ _
    have occ : occupied F A (shiftWord (x i₀) (base x)) := by
      rw [he]
      refine ⟨B, hB, ?_⟩
      rwa [show restrictWord B x = b from funext hx]
    exact sub_eq_zero.mpr (chosen_eq F A hA (base x) (x i₀) occ).symm

private def shiftEquiv (t : ZMod k) : Cube ι (ZMod k) ≃ Cube ι (ZMod k) where
  toFun := shiftWord t
  invFun := shiftWord (-t)
  left_inv x := by funext i; simp [shiftWord]
  right_inv x := by funext i; simp [shiftWord]

variable [Fintype ι] [DecidableEq ι] [NeZero k]

private theorem avg_label (L : Cube ι (ZMod k) → ZMod k)
    (hs : ∀ t x, L (shiftWord t x)=L x+t) (f : ZMod k → ℚ) :
    avg (fun x => f (L x)) = avg f := by
  have ho (x : Cube ι (ZMod k)) : avg (fun t => f (L x+t)) = avg f := by
    unfold avg
    congr 1
    exact Equiv.sum_comp (Equiv.addLeft (L x)) f
  have hi (t : ZMod k) : avg (fun x => f (L x+t)) = avg (fun x => f (L x)) := by
    simp only [avg, ← hs]
    congr 1
    exact Equiv.sum_comp (shiftEquiv t) (fun x => f (L x))
  calc
    _ = avg (fun t : ZMod k => avg (fun x => f (L x+t))) := by simp only [hi, avg_const]
    _ = avg (fun x => avg (fun t : ZMod k => f (L x+t))) := avg_comm _
    _ = _ := by simp only [ho, avg_const]

theorem orbit_mean (L : Cube ι (ZMod k) → ZMod k) (hs : ∀ t x, L (shiftWord t x)=L x+t) :
    avg (fun x => orbitScore k (L x)) = 0 := by
  rw [avg_label _ hs, avg, sum_orbitScore, zero_div]

theorem orbit_energy (L : Cube ι (ZMod k) → ZMod k) (hs : ∀ t x, L (shiftWord t x)=L x+t) :
    energy (fun x => orbitScore k (L x)) = (k : ℚ)-1 := by
  unfold energy
  rw [avg_label L hs (fun z => (orbitScore k z)^2), avg, sum_orbitScore_sq, ZMod.card]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast NeZero.ne k)

end BorgSignedSets
