module

public import conjectures.ConsecutiveThreshold.BlockMass

@[expose] public section
namespace ConsecutiveThreshold
open Equiv Finset
open scoped BigOperators Classical

/-- Failure on disjoint test blocks depends only on the middle-quarter digits. -/
theorem block_estimate {n k : ℕ} (π : Perm (Fin k)) (_hk : 0<k)
    (q : ℝ) (hq0 : 0<q) (hq1 : q≤1) :
    ∃ B : Code n → Prop, (∀ σ, ¬contains π σ → B (encode σ)) ∧
      (∀ e f, (∀ i : Fin n, n-2*(n/4) ≤ i.val → i.val < n-(n/4) → e i=f i) → (B e ↔ B f)) ∧
      (∑ e : Code n, if B e then q^(∑ i,(e i).val) else 0) ≤
        (1-q^(inversions π)/(k.factorial:ℝ))^(n/4/k)*(∑ e : Code n, q^(∑ i,(e i).val)) := by
  classical
  let a := n/4
  let base := n-2*a
  let L := a/k
  let start (b : Fin L) := base+b.val*k
  have end_bound : base+L*k ≤ n-a := by
    have := Nat.div_mul_le_self a k
    dsimp [L,base,a] at *
    omega
  have last (b : Fin L) : start b + k ≤ n-a := by
    have h := Nat.mul_le_mul_right k b.isLt
    rw [Nat.succ_mul] at h
    dsimp [start]
    omega
  have room (b : Fin L) : start b+k ≤ n := (last b).trans (Nat.sub_le ..)
  let hits (b : Fin L) (σ : Perm (Fin n)) := blockHit π (start b) (room b) σ
  let P (j : ℕ) (σ : Perm (Fin n)) := ∀ b : Fin L, b.val<j → ¬hits b σ
  let B (e : Code n) := P L ((codeEquiv n).symm e)
  have decode (e : Code n) : encode ((codeEquiv n).symm e) = e := (codeEquiv n).apply_symm_apply e
  have encode' (σ : Perm (Fin n)) : (codeEquiv n).symm (encode σ) = σ := (codeEquiv n).symm_apply_apply σ
  refine ⟨B,?_,?_,?_⟩
  · intro σ hσ
    change P L ((codeEquiv n).symm (encode σ))
    rw [encode']
    exact fun b _ hh ↦ hσ ⟨start b,room b,hh⟩
  · intro e f he
    have localHit (b : Fin L) : hits b ((codeEquiv n).symm e) ↔ hits b ((codeEquiv n).symm f) := by
      apply blockHit_local
      intro i lo hi
      have hlo : base ≤ i.val := (Nat.le_add_right base (b.val*k)).trans lo
      have hhi := lt_of_lt_of_le hi (last b)
      change (encode ((codeEquiv n).symm e) i).val = (encode ((codeEquiv n).symm f) i).val
      rw [decode,decode,he i hlo hhi]
    constructor
    · exact fun h b hb hh ↦ h b hb ((localHit b).mpr hh)
    · exact fun h b hb hh ↦ h b hb ((localHit b).mp hh)
  · let c : ℝ := 1-q^inversions π/(k.factorial:ℝ)
    have hc : 0 ≤ c := by
      have hpow := pow_le_pow_of_le_one hq0.le hq1 (Nat.zero_le (inversions π))
      have hf : (1:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
      have hf' : 0 < (k.factorial:ℝ) := by positivity
      apply sub_nonneg.mpr
      rw [div_le_iff₀ hf', one_mul]
      exact (by simpa using hpow : q^inversions π≤1).trans hf
    have bound (j : ℕ) (hj : j≤L) :
        permMass q (P j) ≤ c^j * permMass q (fun _ : Perm (Fin n) ↦ True) := by
      induction j with
      | zero => simp [P,permMass]
      | succ j ih =>
        let t : Fin L := ⟨j, by omega⟩
        have invP (σ : Perm (Fin n)) (ρ : Perm (Fin k)) (hP : P j σ) :
            P j (σ * blockReorder (start t) (room t) ρ) := by
          intro b hb hit
          apply hP b hb
          have sep : start b+k ≤ start t := by
            have hm := Nat.mul_le_mul_right k hb
            rw [Nat.succ_mul] at hm
            dsimp [t,start]
            omega
          have hsame (i : Fin k) :
              blockReorder (start t) (room t) ρ (blockPos (start b) (room b) i)
                = blockPos (start b) (room b) i := by
            apply reorder_outside
            have := i.isLt
            simp only [inBlock,blockPos]
            omega
          intro i l
          simpa only [Perm.mul_apply,hsame] using hit i l
        have eqP : P (j+1) = (fun σ ↦ P j σ ∧ ¬hits t σ) := by
          funext σ
          apply propext
          constructor
          · exact fun h ↦ ⟨fun b hb ↦ h b (by omega),h t (by exact Nat.lt_succ_self j)⟩
          · rintro ⟨h,ht⟩ b hb
            by_cases he : b.val=j
            · have eq : b=t := Fin.ext he
              exact eq ▸ ht
            · exact h b (by omega)
        rw [eqP]
        calc
          _ ≤ c*permMass q (P j) := step_mass π (start t) (room t) q hq0 hq1 (P j) invP
          _ ≤ c*(c^j * permMass q (fun _ : Perm (Fin n) ↦ True)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hc
          _ = _ := by rw [pow_succ]; ring
    have weight (σ : Perm (Fin n)) : ∑ i,(((codeEquiv n) σ) i).val = inversions σ := rfl
    have lhs : (∑ e : Code n, if B e then q^(∑ i,(e i).val) else 0) = permMass q (P L) := by
      rw [← Equiv.sum_comp (codeEquiv n) (fun e ↦ if B e then q^(∑ i,(e i).val) else 0)]
      simp only [B, Equiv.symm_apply_apply, weight, permMass]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : P L σ <;> simp [h]
    have rhs : (∑ e : Code n, q^(∑ i,(e i).val)) = permMass q (fun _ : Perm (Fin n) ↦ True) := by
      rw [← Equiv.sum_comp (codeEquiv n) (fun e ↦ q^(∑ i,(e i).val))]
      simp only [weight, permMass, ↓reduceIte]
    have H := (lhs.le.trans (bound L (le_refl _))).trans_eq (congrArg (c^L * ·) rhs.symm)
    convert! H using 1
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : B e <;> simp [h]

end ConsecutiveThreshold
