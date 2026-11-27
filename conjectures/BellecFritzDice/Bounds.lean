module

public import conjectures.BellecFritzDice.Statement
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

namespace BellecFritzDice
open Set MeasureTheory Finset Filter
open scoped Topology

theorem open_below {m : ℕ} (i : Fin m) : IsOpen (below m i) :=
  isOpen_lt (continuous_const.mul (continuous_apply i)) (continuous_finsetSum _ (fun i _ => continuous_apply i))

noncomputable def count {m : ℕ} (x : Fin m → ℝ) : ℕ :=
  by classical exact (Finset.univ.filter (fun i => x∈below m i)).card

theorem count_le {m : ℕ} (hm : 0<m) (x : Fin m → ℝ) : count x < m := by
  classical
  have missing : ∃ i, x∉below m i := by
    by_contra! h
    have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i∈Finset.univ) => (show (m:ℝ)*x i < ∑ j, x j from h i))
    change ∑ i, (m:ℝ)*x i < ∑ _i : Fin m, ∑ j, x j at hlt
    simp only [←Finset.mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨i,hi⟩ := missing
  have ss : (univ.filter (fun j => x∈below m j)) ⊂ univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, fun eq =>
      hi (by have := Finset.ext_iff.mp eq i; simpa using this)⟩
  simpa [count] using Finset.card_lt_card ss

theorem count_le_of_above {m : ℕ} {i j : Fin m} (ne : i≠j) {x : Fin m → ℝ}
    (hi : x∉below m i) (hj : x∉below m j) : count x≤m-2 := by
  classical
  have sub : (univ.filter (fun k => x∈below m k)) ⊆ (univ.erase i).erase j := by
    intro k hk
    have h := (mem_filter.mp hk).2
    exact mem_erase.mpr ⟨fun e => hj (e ▸ h),mem_erase.mpr ⟨fun e => hi (e ▸ h),Finset.mem_univ _⟩⟩
  simpa [count,card_erase_of_mem,ne.symm,Nat.sub_sub] using Finset.card_le_card sub

theorem chance_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ) (i : Fin (n+3)) :
    (rolls μ (n+3)).real (below (n+3) i)=chance μ n := by
  classical
  let e := Equiv.swap i 0
  have hp := measurePreserving_piCongrLeft (fun _ : Fin (n+3) => μ) e
  have h := hp.measure_preimage (open_below (0 : Fin (n+3))).measurableSet.nullMeasurableSet
  have pre : MeasurableEquiv.piCongrLeft (fun _ : Fin (n+3) => ℝ) e ⁻¹' below (n+3) 0 =
      below (n+3) i := by
    ext x
    have aux (j : Fin (n+3)) : MeasurableEquiv.piCongrLeft (fun _ : Fin (n+3) => ℝ) e x j = x (e.symm j) := by
      simpa only [Equiv.apply_symm_apply] using MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ => ℝ) e x (e.symm j)
    simp only [Set.mem_preimage,below,Set.mem_ofPred_eq,aux]
    rw [e.symm.sum_comp x]
    simp [e]
  rw [pre] at h
  exact congrArg ENNReal.toReal h

theorem count_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) :
    Integrable (fun x : Fin m → ℝ => (count x : ℝ)) (rolls μ m) := by
  classical
  have rep (x : Fin m → ℝ) : (count x : ℝ) =
      ∑ i, (below m i).indicator (fun _ => (1:ℝ)) x := by
    simp [count,Set.indicator_apply]
  simp only [rep]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (1:ℝ)).indicator (open_below i).measurableSet)

theorem expected_count {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ x, (count x : ℝ) ∂rolls μ (n+3) = (n+3:ℕ)*chance μ n := by
  classical
  have rep (x : Fin (n+3) → ℝ) : (count x : ℝ) =
      ∑ i, (below (n+3) i).indicator (fun _ => (1:ℝ)) x := by
    simp [count,Set.indicator_apply]
  simp only [rep,integral_finsetSum _ (fun i _ => (integrable_const (1:ℝ)).indicator
    (open_below i).measurableSet),integral_indicator_const (1:ℝ) (open_below _).measurableSet,smul_eq_mul,mul_one,
    chance_eq n,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

end BellecFritzDice

namespace BellecFritzDice
open Set MeasureTheory Finset Filter
open scoped Topology

private theorem open_mass {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℕ}
    {x : Fin m → ℝ} {U : Set (Fin m → ℝ)} (hu : IsOpen U) (hx : x∈U)
    (h : ∀ i, x i∈μ.support) : 0 < rolls μ m U := by
  obtain ⟨r,hr,sub⟩ := Metric.isOpen_iff.mp hu x hx
  apply lt_of_lt_of_le _ (measure_mono sub)
  rw [rolls,Measure.pi_ball _ x hr]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ =>
    ((Measure.mem_support_iff_forall _).mp (h i) _ (Metric.ball_mem_nhds _ hr)).ne'))

private theorem two_high {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : a∈μ.support) (hb : b∈μ.support) (hab : a<b) (n : ℕ) :
    0 < rolls μ (n+3) {x | count x ≤ n+1} := by
  let v : Fin (n+3) → ℝ := fun i => if i=0 then a else b
  let i₁ : Fin (n+3) := ⟨1,by omega⟩
  let i₂ : Fin (n+3) := ⟨2,by omega⟩
  have h1 : i₁≠0 := fun e => by have := congrArg Fin.val e; simp [i₁] at this
  have h2 : i₂≠0 := fun e => by have := congrArg Fin.val e; simp [i₂] at this
  let U : Set (Fin (n+3) → ℝ) := {x | (∑ j, x j) < (n+3:ℕ)*x i₁} ∩
    {x | (∑ j, x j) < (n+3:ℕ)*x i₂}
  have hU : IsOpen U := by
    apply IsOpen.inter <;> apply isOpen_lt <;> fun_prop
  have hx : v∈U := by
    have sum : ∑ i, v i = a+(n+2:ℕ)*b := by
      rw [Fin.sum_univ_succ]
      simp [v]
    simp only [U,mem_inter_iff,mem_ofPred_eq,sum,v,ite_eq_right h1,ite_eq_right h2]
    push_cast
    constructor <;> nlinarith
  apply lt_of_lt_of_le (open_mass (μ:=μ) hU hx (fun i => by dsimp only [v]; split <;> assumption))
  apply measure_mono
  intro x hx
  have ne : i₁ ≠ i₂ := fun e => by have := congrArg Fin.val e; simp [i₁,i₂] at this
  have h1' : (∑ j, x j) < (n+3:ℕ)*x i₁ := hx.1
  have h2' : (∑ j, x j) < (n+3:ℕ)*x i₂ := hx.2
  have h := count_le_of_above ne (x:=x) (fun low => h1'.not_gt low) (fun low => h2'.not_gt low)
  simpa using h

private theorem chance_zero_of_subsingleton {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : μ.support.Subsingleton) (n : ℕ) : chance μ n=0 := by
  have hh (i : Fin (n+3)) : ∀ᵐ x ∂rolls μ (n+3),x i∈μ.support :=
    (Measure.quasiMeasurePreserving_eval (fun _ => μ) i).ae Measure.support_mem_ae
  have null : ∀ᵐ x ∂rolls μ (n+3), x∉below (n+3) 0 := by
    filter_upwards [ae_all_iff.mpr hh] with x hx
    have all (i : Fin (n+3)) : x i=x 0 := h (hx i) (hx 0)
    change ¬(n+3:ℕ)*x 0 < ∑ j, x j
    rw [Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => all i)]
    simp
  have z : rolls μ (n+3) (below (n+3) 0)=0 := by simpa using ae_iff.mp null
  simp [chance,Measure.real,z]

/-- Fewer than m−1 observations lie below their sample mean on a set of positive mass. -/
theorem strict_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    chance μ n < (n+2:ℝ)/(n+3) := by
  rcases μ.support.subsingleton_or_nontrivial with h|h
  · rw [chance_zero_of_subsingleton h n]
    positivity
  obtain ⟨a,ha,b,hb,hab⟩ := h.exists_lt
  have pos := two_high ha hb hab n
  let ν := rolls μ (n+3)
  let f := fun x : Fin (n+3) → ℝ => (count x:ℝ)
  have fI : Integrable f ν := count_integrable _
  have gI : Integrable (fun _ : Fin (n+3) → ℝ => (n+2:ℝ)) ν := integrable_const _
  have le : f ≤ᵐ[ν] fun _ => (n+2:ℝ) := by
    apply ae_of_all
    intro x
    dsimp [f]
    exact_mod_cast (show count x≤n+2 by have := count_le (show 0<n+3 by omega) x; omega)
  have strict : ∫ x, f x ∂ν < ∫ _x, (n+2:ℝ) ∂ν := by
    apply lt_of_le_of_ne (integral_mono_ae fI gI le)
    intro eq
    have aeq := (integral_eq_iff_of_ae_le fI gI le).mp eq
    have null : ∀ᵐ x ∂ν, ¬ count x≤n+1 := by
      filter_upwards [aeq] with x hx
      change (count x:ℝ)=(n:ℝ)+2 at hx
      exact_mod_cast (show ¬(count x:ℝ)≤(n:ℝ)+1 by linarith)
    exact pos.ne' (by simpa [ν] using ae_iff.mp null)
  change ∫ x, (count x:ℝ) ∂rolls μ (n+3) < ∫ _x, (n+2:ℝ) ∂rolls μ (n+3) at strict
  rw [expected_count,integral_const] at strict
  simp only [probReal_univ,one_smul,Nat.cast_add,Nat.cast_ofNat] at strict
  exact (lt_div_iff₀ (by positivity)).2 (by linarith)

end BellecFritzDice

namespace BellecFritzDice
open Set MeasureTheory MeasureTheory.Measure Finset Filter
noncomputable section

private theorem no_tie (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ x ∂rolls μ (n+3), (↑(n+3:ℕ):ℝ)*x 0 ≠ ∑ j,x j := by
  let τ := rolls μ (n+2)
  let U : Set (ℝ × (Fin (n+2) → ℝ)) := {z | z.1 ≠ (∑ i,z.2 i)/(n+2:ℕ)}
  have hm : MeasurableSet U := by
    exact (measurableSet_eq_fun (f:=fun z : ℝ × (Fin (n+2) → ℝ) => z.1) (g:=fun z => (∑ i,z.2 i)/(n+2:ℕ)) (by fun_prop) (by fun_prop)).compl
  have h : ∀ᵐ z ∂μ.prod τ,z∈U := (ae_prod_iff_ae_ae hm).mpr
    ((Measure.ae_ae_comm (μ:=μ) (ν:=τ) (p:=fun (x : ℝ) (y : Fin (n+2) → ℝ) => x≠(∑ i,y i)/(n+2:ℕ)) hm).mpr
      (ae_of_all _ (fun y => μ.ae_ne ((∑ i,y i)/(n+2:ℕ)))))
  have law := measurePreserving_piFinSuccAbove (fun _ : Fin ((n+2)+1) => μ) 0
  filter_upwards [law.quasiMeasurePreserving.ae h] with x hx
  change x 0 ≠ (∑ j,x ((0 : Fin ((n+2)+1)).succAbove j))/(n+2:ℕ) at hx
  simp only [Fin.zero_succAbove] at hx
  intro eq
  apply hx
  apply (eq_div_iff (by positivity)).mpr
  rw [Fin.sum_univ_succ] at eq
  push_cast at eq ⊢
  nlinarith

theorem strict_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (n : ℕ) :
    1/(n+3:ℝ) < chance μ n := by
  let τ := μ.map (fun x : ℝ => -x)
  have h := strict_upper τ n
  have eq : chance τ n = 1-chance μ n := by
    have meas : Measurable (fun x : Fin (n+3) → ℝ => fun i => -x i) := by fun_prop
    change (Measure.pi (fun _ : Fin (n+3) => μ.map Neg.neg)).real (below (n+3) 0)=_
    rw [←pi_map_pi (fun _ => measurable_neg.aemeasurable),map_measureReal_apply meas (open_below _).measurableSet]
    have same : (fun (x : Fin (n+3) → ℝ) i => -x i) ⁻¹' below (n+3) 0 =ᵐ[rolls μ (n+3)] (below (n+3) 0)ᶜ := by
      filter_upwards [no_tie μ n] with x hx
      change (↑(n+3:ℕ)*(-x 0) < ∑ i, -x i) ↔ ¬ ↑(n+3:ℕ)*x 0 < ∑ i, x i
      rw [mul_neg,sum_neg_distrib,neg_lt_neg_iff]
      exact ⟨fun e => e.not_gt,fun u => lt_of_le_of_ne (not_lt.mp u) hx.symm⟩
    rw [measureReal_congr same,measureReal_compl (open_below _).measurableSet,probReal_univ]
    rfl
  rw [eq] at h
  have positive : 0<(n:ℝ)+3 := by positivity
  apply (div_lt_iff₀ positive).mpr
  have := (lt_div_iff₀ positive).mp h
  nlinarith

end
end BellecFritzDice
