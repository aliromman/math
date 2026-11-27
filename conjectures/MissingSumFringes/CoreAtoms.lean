module

public import conjectures.MissingSumFringes.SideLaw
public import conjectures.MissingSumFringes.Normalized

@[expose] public section
namespace MissingSumFringes
open Finset Filter
open scoped Classical Pointwise Topology

theorem atom_le_normWindow (m t : ℕ) : atom true m t ≤ normWindow m t := by
  apply le_of_tendsto (sideMass_limit true m t)
  filter_upwards [eventually_ge_atTop (t+1)] with n hn
  let p := fun B : Finset ℕ ↦ (missing t B).card=m ∧ (t=0 ∨ t-1∈missing t B) ∧ (t=0 ∨ 0∈B)
  have e : normWindow m t=prob (range t) p := by
    rw [prob_count,card_range]
    unfold normWindow
    have same : normStrings m t=(range t).powerset.filter p := by
      ext A
      simp only [normStrings,mem_filter,p]
    rw [same]
    congr 2
    apply congrArg Finset.card
    ext A
    simp only [mem_filter]
  rw [e,←restrict_prob (range_mono (show t≤n by omega)) p]
  apply prob_mono
  intro A _ ha
  have E := extent_sizes (n := n) (A := A) (q := t) (by omega) ha.2.2.le
  change (missing t (A∩range t)).card=m ∧ _
  rw [missing_restrict]
  refine ⟨E ▸ ha.2.1,?_,?_⟩
  · by_cases ht : t=0
    · exact Or.inl ht
    · right
      rw [←E,←ha.2.2]
      exact below_extent (by rw [ha.2.2]; omega)
  · by_cases ht : t=0
    · exact Or.inl ht
    · exact Or.inr (mem_inter.mpr ⟨ha.1 rfl,mem_range.mpr (by omega)⟩)

theorem reflected_zero {n : ℕ} {A : Finset ℕ} (hA : A⊆range n) (hn : 0<n) :
    0∈reflect n A ↔ n-1∈A := by
  constructor
  · intro h
    obtain ⟨a,ha,e⟩ := mem_image.mp h
    have := mem_range.mp (hA ha)
    rwa [show n-1=a by omega]
  · intro h
    exact mem_image.mpr ⟨n-1,h,by omega⟩

theorem full_card {n : ℕ} (hn : 0<n) {A : Finset ℕ} (hA : A⊆range n) :
    (missing (width n) A).card=(missing n A).card+(missing (n-1) (reflect n A)).card := by
  let R := missing (n-1) (reflect n A)
  let v := fun x : ℕ ↦ width n-1-x
  have small (x) (h : x∈R) : x<n-1 := mem_range.mp (mem_sdiff.mp h).1
  have refl (x) (hx : x<width n) : v (v x)=x := by dsimp [v,width] at *; omega
  have dis : Disjoint (missing n A) (R.image v) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hyR,rfl⟩ := mem_image.mp hy
    have a := small y hyR
    have b := mem_range.mp (mem_sdiff.mp hx).1
    dsimp [v,width] at b
    omega
  have eq : missing (width n) A = missing n A ∪ R.image v := by
    ext x
    constructor
    · intro hx
      obtain ⟨within,absent⟩ := mem_sdiff.mp hx
      have w := mem_range.mp within
      by_cases before : x<n
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_range.mpr before,absent⟩)
      · apply mem_union_right _ (mem_image.mpr ⟨v x,?_,refl x w⟩)
        have h : v x < n-1 := by dsimp [v,width] at *; omega
        have z : v x < width n := by dsimp [v,width] at *; omega
        apply Finset.mem_sdiff.mpr
        refine ⟨mem_range.mpr h,?_⟩
        intro hit
        exact absent (refl x w ▸ (reflect_sum hA hn z).mp hit)
    · intro hx
      rcases mem_union.mp hx with low|high
      · obtain ⟨xn,no⟩ := mem_sdiff.mp low
        exact mem_sdiff.mpr ⟨range_mono (show n≤width n by dsimp [width]; omega) xn,no⟩
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp high
        have yr := small y hy
        have yw : y<width n := by dsimp [width]; omega
        exact mem_sdiff.mpr ⟨mem_range.mpr (by dsimp [v,width]; omega),
          fun hit ↦ (mem_sdiff.mp hy).2 ((reflect_sum hA hn yw).mpr hit)⟩
  rw [eq,card_union_of_disjoint dis,card_image_of_injOn]
  intro a ha b hb ab
  have wa : a<width n := by have := small a ha; dsimp [width]; omega
  have wb : b<width n := by have := small b hb; dsimp [width]; omega
  exact (refl _ wa).symm.trans ((congrArg v ab).trans (refl _ wb))

noncomputable def cellWeight (n m t j s : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  avg (range n) (fun A ↦ if side true n m t A ∧ side true (n-1) j s (reflect n A) then f A else 0)

noncomputable def anchoredWeight (n k : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  avg (range n) (fun A ↦ if 0∈A ∧ n-1∈A ∧ (missing (width n) A).card=k then f A else 0)

theorem anchored_sum {n k : ℕ} (hn : 0<n) (f : Finset ℕ → ℝ) :
    anchoredWeight n k f = ∑ m∈range (k+1), ∑ z∈(range (n+1) ×ˢ range (n+1)),
      cellWeight n m z.1 (k-m) z.2 f := by
  unfold cellWeight anchoredWeight
  simp_rw [←avg_sum]
  apply avg_congr
  intro A hA
  let m₀ := (missing n A).card
  let t₀ := extent n A
  let s₀ := extent (n-1) (reflect n A)
  let included := 0∈A ∧ n-1∈A ∧ (missing (width n) A).card=k
  have tu : t₀≤n := extent_le ..
  have su : s₀≤n := (extent_le _ _).trans (Nat.sub_le ..)
  have card := full_card hn hA
  change (missing (width n) A).card=m₀+(missing (n-1) (reflect n A)).card at card
  have sig (m : ℕ) (hm : m∈range (k+1)) (z : ℕ×ℕ) :
      (side true n m z.1 A ∧ side true (n-1) (k-m) z.2 (reflect n A)) ↔
        included ∧ m=m₀ ∧ z=(t₀,s₀) := by
    simp only [side,true_implies,reflected_zero hA hn]
    have mcap := mem_range.mp hm
    change (0∈A ∧ m₀=m ∧ t₀=z.1) ∧
      (n-1∈A ∧ (missing (n-1) (reflect n A)).card=k-m ∧ s₀=z.2) ↔ _
    dsimp only [included]
    constructor
    · rintro ⟨⟨h₀,mm,tt⟩,h₁,kk,ss⟩
      exact ⟨⟨h₀,h₁,by omega⟩,mm.symm,Prod.ext tt.symm ss.symm⟩
    · rintro ⟨⟨h₀,h₁,kk⟩,rfl,rfl⟩
      exact ⟨⟨h₀,rfl,rfl⟩,h₁,by omega,rfl⟩
  have mem : (t₀,s₀)∈range (n+1) ×ˢ range (n+1) :=
    mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
  change (if included then f A else 0)=_
  symm
  calc
    _ = ∑ m∈range (k+1), ∑ z∈range (n+1) ×ˢ range (n+1),
        if included ∧ m=m₀ ∧ z=(t₀,s₀) then f A else 0 := by
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro z _
      by_cases h : included ∧ m=m₀ ∧ z=(t₀,s₀)
      · simp only [ite_eq_left ((sig m hm z).mpr h),ite_eq_left h]
      · simp only [ite_eq_right ((sig m hm z).not.mpr h),ite_eq_right h]
    _ = _ := by
      by_cases h : included
      · have mk : m₀∈range (k+1) := mem_range.mpr (by have := h.2.2; omega)
        simp [h,ite_and,mem,mk]
      · simp [h]

end MissingSumFringes
