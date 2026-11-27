module

public import conjectures.MissingSumFringes.Window
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section
namespace MissingSumFringes
open Finset
open scoped Pointwise Classical

/-- Subsets that omit the last sum of the interval. -/
def reflected (t : ℕ) (C : Finset ℕ) := C.powerset.filter fun A => t-1∉A+A

private theorem mirror_lt {t x : ℕ} (hx : x<t) : t-1-x<t := by omega
private theorem mirror_twice {t x : ℕ} (hx : x<t) : t-1-(t-1-x)=x := by omega

private theorem mirror_image_card {t : ℕ} {B : Finset ℕ} (sub : B⊆range t) :
    (B.image (fun x => t-1-x)).card=B.card := by
  apply card_image_of_injOn
  intro x hx y hy h
  have ax := mem_range.mp (sub hx)
  have ay := mem_range.mp (sub hy)
  change t-1-x=t-1-y at h
  omega

/-- A reflection pair permits three choices rather than four. The fixed point costs
at most one position in the estimate for the number of pairs. -/
theorem reflected_card {t : ℕ} {C : Finset ℕ} (sub : C⊆range t) :
    ((reflected t C).card:ℝ) ≤ (2:ℝ)^((3/4:ℝ)*C.card+t/8+1/8) := by
  let p := fun x => t-1-x
  let P := C.filter fun x => x<p x ∧ p x∈C
  let Q := P.image p
  let D := C \ (P∪Q)
  have psub : P⊆C := filter_subset ..
  have qsub : Q⊆C := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp hx).2.2
  have dis : Disjoint P Q := by
    refine disjoint_left.mpr ?_
    intro z hz hq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
    have xlt := mem_range.mp (sub (psub hx))
    have a := (mem_filter.mp hx).2.1
    have b := (mem_filter.mp hz).2.1
    change x<t-1-x at a
    change t-1-x<t-1-(t-1-x) at b
    omega
  have qcard : Q.card=P.card := mirror_image_card (psub.trans sub)
  have split : D.card+2*P.card=C.card := by
    have h := card_sdiff_add_card_eq_card (union_subset psub qsub)
    rw [card_union_of_disjoint dis,qcard] at h
    change D.card+(P.card+P.card)=C.card at h
    omega
  have absent : ∀ x∈D, x≠(t-1)/2 → p x∉C := by
    intro x hx hmid hpx
    have hc := (mem_sdiff.mp hx).1
    have no := (mem_sdiff.mp hx).2
    have xl := mem_range.mp (sub hc)
    have inv : p (p x)=x := mirror_twice xl
    by_cases h : x<p x
    · exact no (mem_union_left _ (mem_filter.mpr ⟨hc,h,hpx⟩))
    · have rev : p x<x := by
        change t-1-x<x
        change ¬x<t-1-x at h
        omega
      have hp : p x∈P := mem_filter.mpr ⟨hpx,by simpa only [inv] using rev,by simpa only [inv] using hc⟩
      exact no (mem_union_right _ (mem_image.mpr ⟨p x,hp,inv⟩))
  have inject : ((D.erase ((t-1)/2)).image p).card=(D.erase ((t-1)/2)).card :=
    mirror_image_card ((erase_subset ..).trans (sdiff_subset.trans sub))
  have missingPartners : (D.erase ((t-1)/2)).image p⊆range t \ C := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨ne,hd⟩ := mem_erase.mp hx
    exact mem_sdiff.mpr ⟨mem_range.mpr (mirror_lt (mem_range.mp (sub (mem_sdiff.mp hd).1))),absent x hd ne⟩
  have bound := card_mono missingPartners
  rw [inject,card_sdiff_of_subset sub,card_range] at bound
  have erase := Finset.pred_card_le_card_erase (s:=D) (a:=(t-1)/2)
  have cmax : C.card≤t := by simpa using card_mono sub
  have pairs : 2*C.card≤t+2*P.card+1 := by omega
  let state (A : Finset ℕ) (x : ℕ) : Fin 3 :=
    if x∈A then 1 else if p x∈A then 2 else 0
  let code (A : ↥(reflected t C)) : (↥P → Fin 3) × ↥D.powerset :=
    (fun x => state A.val x.val, ⟨A.val∩D, mem_powerset.mpr inter_subset_right⟩)
  have forced : ∀ A∈reflected t C, ∀ x∈P, x∈A → p x∉A := by
    intro A hA x hx ha hp
    have xl := mem_range.mp (sub (psub hx))
    have bad := (mem_filter.mp hA).2
    apply bad
    refine mem_add.mpr ⟨x,ha,p x,hp,?_⟩
    change x+(t-1-x)=t-1
    omega
  have code_inj : Function.Injective code := by
    intro A B h
    have d : A.val∩D=B.val∩D := congrArg (fun z => z.2.val) h
    have stat : ∀ x∈P, state A.val x=state B.val x := fun x hx =>
      congrArg (fun z => z.1 ⟨x,hx⟩) h
    have left : ∀ x∈P, x∈A.val ↔ x∈B.val := by
      intro x hx
      have h := stat x hx
      have one (E : Finset ℕ) : state E x=1 ↔ x∈E := by
        by_cases a : x∈E <;> by_cases b : p x∈E <;> simp [state,a,b]
      rw [← one A.val,h,one B.val]
    have right : ∀ x∈P, p x∈A.val ↔ p x∈B.val := by
      intro x hx
      by_cases ha : x∈A.val
      · have hb := (left x hx).mp ha
        simp [forced _ A.property _ hx ha,forced _ B.property _ hx hb]
      · have hb := (left x hx).not.mp ha
        have h := stat x hx
        by_cases oa : p x∈A.val <;> by_cases ob : p x∈B.val <;> simp_all [state]
    apply Subtype.ext
    ext x
    by_cases hp : x∈P
    · exact left x hp
    by_cases hq : x∈Q
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hq
      exact right y hy
    by_cases hc : x∈C
    · have hd : x∈D := mem_sdiff.mpr ⟨hc,by simpa using And.intro hp hq⟩
      simpa [hd] using Finset.ext_iff.mp d x
    · have na : x∉A.val := fun h => hc (mem_powerset.mp (mem_filter.mp A.property).1 h)
      have nb : x∉B.val := fun h => hc (mem_powerset.mp (mem_filter.mp B.property).1 h)
      simp [na,nb]
  have size := Fintype.card_le_of_injective code code_inj
  have integral : (reflected t C).card≤3^P.card*2^D.card := by simpa using size
  have pow3 : (3:ℝ) ≤ (2:ℝ)^(7/4:ℝ) := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (z:=4) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have exp : (3:ℝ)^P.card * 2^D.card ≤ 2^((7/4:ℝ)*P.card+D.card) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_mul (by norm_num),Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) pow3 _) (by positivity)
  refine le_trans (by exact_mod_cast integral) (exp.trans ?_)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hsplit : (D.card:ℝ)+2*P.card=C.card := by exact_mod_cast split
  have hpairs : 2*(C.card:ℝ)≤t+2*P.card+1 := by exact_mod_cast pairs
  linarith

end MissingSumFringes
