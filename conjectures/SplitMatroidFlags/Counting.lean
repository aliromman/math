module

public import conjectures.SplitMatroidFlags.Patterns
public import conjectures.SplitMatroidFlags.GraphRank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

namespace SplitMatroidFlags

open Finset

variable {E : Type} [Fintype E] [DecidableEq E] {B : Finset (Finset E)} {b t : Finset E}

omit [Fintype E] in
lemma mem_faces {F : Finset (Finset E)} {k : ℕ} : F ∈ faces B k ↔ IsFace B F ∧ dimension F = k := by
  classical
  have supp (h : IsFace B F) : F ⊆ B := fun x hx => ((h.2.choose_spec x).mp hx).1
  simp only [faces,mem_filter,mem_powerset]
  exact ⟨And.right,fun h => ⟨supp h.1,h⟩⟩

omit [Fintype E] in

lemma inside {F : Finset (Finset E)} {k : ℕ} (h : F ∈ faces B k) : F ⊆ B := by
  intro x hx
  exact (((mem_faces.mp h).1.2.choose_spec x).mp hx).1

lemma dimension_tight {w : E → ℝ} (hm : HasMatches B b) (hb : Maximizes B w b) :
    dimension (exposed B w) = Module.finrank ℝ (directions (activeEdges B b w)) := by
  rw [dimension,direction_space hm hb]
  have eq : edgeSpan B b w = directions (activeEdges B b w) := by
    unfold edgeSpan directions
    apply congrArg (Submodule.span ℝ)
    ext z
    constructor
    · rintro ⟨i,j,h,eq⟩
      exact ⟨(i,j),(mem_activeEdges i j).mpr h,eq⟩
    · rintro ⟨⟨i,j⟩,h,eq⟩
      exact ⟨i,j,(mem_activeEdges i j).mp h,eq⟩
  rw [eq]

def represented (B : Finset (Finset E)) (b : Finset E) (P : Finset (E × E)) : Prop :=
  ∃ w : E → ℝ, Maximizes B w b ∧ activeEdges B b w = P

def score (label : E → ℕ) (b : Finset E) := ∑ i ∈ b, label i

def minimumAt (label : E → ℕ) (b : Finset E) (F : Finset (Finset E)) : Prop :=
  b ∈ F ∧ ∀ t ∈ F, score label b ≤ score label t

instance (label : E → ℕ) (b : Finset E) (F : Finset (Finset E)) : Decidable (minimumAt label b F) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ ∈ F, _))

def uphill (label : E → ℕ) (P : Finset (E × E)) : Prop := ∀ e ∈ P, label e.1 ≤ label e.2

lemma minimum_iff {w : E → ℝ} (hm : HasMatches B b) (hb : Maximizes B w b) (label : E → ℕ) :
    minimumAt label b (exposed B w) ↔ uphill label (activeEdges B b w) := by
  constructor
  · intro h ⟨i,j⟩ hE
    obtain ⟨hs,he⟩ := (mem_activeEdges i j).mp hE
    have le := h.2 _ ((swap_mem_exposed hb hs).mpr he)
    let v (i : E) : ℤ := label i
    have e := swap_diff hs v
    have le' : (∑ k ∈ b, v k) ≤ ∑ k ∈ insert j (b.erase i), v k := by
      dsimp only [v]
      unfold score at le
      exact_mod_cast le
    change label i ≤ label j
    have z : v i ≤ v j := by omega
    dsimp only [v] at z
    exact_mod_cast z
  · refine fun h => ⟨mem_exposed.mpr hb,fun t ht => ?_⟩
    obtain ⟨tb,eq⟩ := (mem_exposed_iff_eq hb).mp ht
    obtain ⟨f,hf⟩ := hm t tb
    have hh := (hf.equal_iff ((maximizes_iff hb.1 hm).mp hb)).mp eq
    unfold score
    rw [hf.sum_eq label]
    apply sum_le_sum
    intro i hi
    rcases hf.permitted i hi with self | hs
    · rw [self]
    · exact h (i,f i) ((mem_activeEdges i _).mpr ⟨hs,hh i hi⟩)

lemma minimum_unique {F : Finset (Finset E)} (hF : IsFace B F) (allm : ∀ b ∈ B, HasMatches B b)
    {label : E → ℕ} (hinj : Function.Injective label) (hb : minimumAt label b F)
    (ht : minimumAt label t F) : b = t := by
  obtain ⟨w,rfl⟩ := face_eq_exposed hF
  have bm := mem_exposed.mp hb.1
  obtain ⟨tb,eq⟩ := (mem_exposed_iff_eq bm).mp ht.1
  obtain ⟨f,hf⟩ := allm b bm.1 t tb
  have hh := (hf.equal_iff ((maximizes_iff bm.1 (allm b bm.1)).mp bm)).mp eq
  have up := (minimum_iff (allm b bm.1) bm label).mp hb
  have le (i) (hi : i ∈ b) : label i ≤ label (f i) := by
    rcases hf.permitted i hi with he | hs
    · rw [he]
    · exact up (i,_) ((mem_activeEdges i _).mpr ⟨hs,hh i hi⟩)
  have se := (hb.2 _ ht.1).antisymm (ht.2 _ hb.1)
  unfold score at se
  rw [hf.sum_eq label] at se
  have eqs := (sum_eq_sum_iff_of_le le).mp se
  rw [← hf.image_eq]
  symm
  exact image_congr (by intro i hi; exact (hinj (eqs i hi)).symm) |>.trans image_id

lemma counts_from_vertices (B : Finset (Finset E)) (k : ℕ) (label : E → ℕ) (inj : Function.Injective label)
    (allm : ∀ b ∈ B, HasMatches B b) :
    (faces B k).card = ∑ b ∈ B, ((faces B k).filter (minimumAt label b)).card := by
  classical
  let S := faces B k
  have one (F) (hF : F ∈ S) : (B.filter fun b => minimumAt label b F).card = 1 := by
    have ne := (mem_faces.mp hF).1.1
    obtain ⟨b,hb,min⟩ := exists_min_image F (score label) ne
    apply card_eq_one.mpr
    refine ⟨b,eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨inside hF hb,hb,min⟩,?_⟩⟩
    intro a ha
    exact minimum_unique (mem_faces.mp hF).1 allm inj (mem_filter.mp ha).2 ⟨hb,min⟩
  have ex : (∑ b ∈ B, (S.filter (minimumAt label b)).card) =
      ∑ F ∈ S, (B.filter fun b => minimumAt label b F).card := by
    simp only [card_filter]
    rw [sum_comm]
  change S.card = _
  rw [ex,sum_congr rfl (fun F hF => one F hF)]
  simp


def incident (label : E → ℕ) (first : Bool) (b : Finset E) (F : Finset (Finset E)) : Prop :=
  b ∈ F ∧ (first = true → minimumAt label b F)

instance (label : E → ℕ) (first : Bool) (b : Finset E) (F : Finset (Finset E)) :
    Decidable (incident label first b F) := inferInstanceAs (Decidable (_ ∧ (_ → _)))

lemma count_patterns {C : Type*} [DecidableEq C] (S : Finset C) (edges : C → Finset (E × E))
    (dim : C → ℕ) (up : C → Bool) (label : E → ℕ) (hm : HasMatches B b)
    (inj : Set.InjOn edges S)
    (rep : ∀ P, represented B b P ↔ ∃ c ∈ S, edges c = P)
    (rank : ∀ c ∈ S, dim c = Module.finrank ℝ (directions (edges c)))
    (order : ∀ c ∈ S, up c = true ↔ uphill label (edges c)) (first : Bool) (k : ℕ) :
    ((faces B k).filter (incident label first b)).card =
      (S.filter (fun c => dim c = k ∧ (first = true → up c = true))).card := by
  classical
  have ex (c) (hc : c ∈ S) : represented B b (edges c) := (rep _).mpr ⟨c,hc,rfl⟩
  choose! w hw hE using ex
  have sameE {v u : E → ℝ} (hv : Maximizes B v b) (hu : Maximizes B u b) :
      exposed B v = exposed B u ↔ activeEdges B b v = activeEdges B b u := by
    rw [exposed_eq_iff hm hv hu]
    constructor
    · intro he
      ext ⟨i,j⟩
      simpa only [mem_activeEdges] using he i j
    · intro he i j
      rw [← mem_activeEdges,← mem_activeEdges,he]
  symm
  apply card_bij fun c _ => exposed B (w c)
  · intro c hc
    obtain ⟨hS,kc,uc⟩ := mem_filter.mp hc
    have hd := dimension_tight hm (hw c hS)
    rw [hE c hS,← rank c hS,kc] at hd
    refine mem_filter.mpr ⟨mem_faces.mpr ⟨exposed_face (hw c hS),hd⟩,mem_exposed.mpr (hw c hS),fun h => ?_⟩
    apply (minimum_iff hm (hw c hS) label).mpr
    rw [hE c hS]
    exact (order c hS).mp (uc h)
  · intro c hc d hd he
    obtain ⟨cs,_⟩ := mem_filter.mp hc
    obtain ⟨ds,_⟩ := mem_filter.mp hd
    have eq := (sameE (hw c cs) (hw d ds)).mp he
    rw [hE c cs,hE d ds] at eq
    exact inj cs ds eq
  · intro F hF
    obtain ⟨hk,hbF,hu⟩ := mem_filter.mp hF
    obtain ⟨hface,hk⟩ := mem_faces.mp hk
    obtain ⟨z,rfl⟩ := face_eq_exposed hface
    have hzb := mem_exposed.mp hbF
    obtain ⟨c,hc,he⟩ := (rep _).mp ⟨z,hzb,rfl⟩
    have eq := (sameE (hw c hc) hzb).mpr ((hE c hc).trans he)
    refine ⟨c,mem_filter.mpr ⟨hc,?_,fun h => ?_⟩,eq⟩
    · rw [rank c hc,he,← dimension_tight hm hzb,hk]
    · apply (order c hc).mpr
      rw [he]
      exact (minimum_iff hm hzb label).mp (hu h)

omit [Fintype E] in
private lemma vertex_injective : Function.Injective (vertex (E := E)) := by
  intro s t h
  ext i
  have entry (S : Finset E) : vertex S i = if i ∈ S then 1 else 0 := by
    simp [vertex,unit,Finset.sum_apply]
  have eq := congrFun h i
  rw [entry,entry] at eq
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

lemma zero_faces (allm : ∀ b ∈ B, HasMatches B b) (F : Finset (Finset E)) :
    F ∈ faces B 0 ↔ ∃ b ∈ B, F = {b} := by
  classical
  constructor
  · intro h
    obtain ⟨hf,hd⟩ := mem_faces.mp h
    obtain ⟨b,hb⟩ := hf.1
    have sub := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp hd)
    refine ⟨b,inside h hb,eq_singleton_iff_unique_mem.mpr ⟨hb,fun t ht => ?_⟩⟩
    exact vertex_injective (sub ⟨t,ht,rfl⟩ ⟨b,hb,rfl⟩)
  · rintro ⟨b,hb,rfl⟩
    let w (i : E) : ℝ := if i ∈ b then 1 else 0
    have hmax := (maximizes_iff hb (allm b hb) (w := w)).mpr (fun i j hs => by simp [w,hs.1,hs.2.1])
    have he : exposed B w = {b} := by
      apply eq_singleton_iff_unique_mem.mpr
      refine ⟨mem_exposed.mpr hmax,fun t ht => ?_⟩
      obtain ⟨tb,wt⟩ := (mem_exposed_iff_eq hmax).mp ht
      obtain ⟨f,hf⟩ := allm b hb t tb
      have eq := (hf.equal_iff ((maximizes_iff hb (allm b hb)).mp hmax)).mp wt
      rw [← hf.image_eq]
      refine (image_congr (g := id) ?_).trans image_id
      intro i hi
      have hh := eq i hi
      rcases hf.permitted i hi with self | hs
      · exact self
      · simp [w,hs.1,hs.2.1] at hh
    refine mem_faces.mpr ⟨he ▸ exposed_face hmax,?_⟩
    simp [dimension]

lemma flags_from_vertices (k : ℕ) (allm : ∀ b ∈ B, HasMatches B b) :
    flags B [k,0] B = ∑ b ∈ B, ((faces B k).filter (b ∈ ·)).card := by
  classical
  have small (F : Finset (Finset E)) (hF : F ⊆ B) :
      ((faces B 0).filter (· ⊆ F)).card = F.card := by
    symm
    apply card_bij fun t _ => ({t} : Finset (Finset E))
    · intro t ht
      exact mem_filter.mpr ⟨(zero_faces allm _).mpr ⟨t,hF ht,rfl⟩,by simpa using ht⟩
    · intro a _ b _ eq
      simpa using eq
    · intro G hG
      obtain ⟨g,_,rfl⟩ := (zero_faces allm _).mp (mem_filter.mp hG).1
      exact ⟨g,(mem_filter.mp hG).2 (mem_singleton_self _),rfl⟩
  have eq : (faces B k).filter (· ⊆ B) = faces B k := filter_eq_self.mpr fun _ h => inside h
  simp only [flags,eq,sum_const,smul_eq_mul,mul_one]
  rw [sum_congr rfl (fun F hf => small F (inside hf))]
  have swap : (∑ b ∈ B, ((faces B k).filter (b ∈ ·)).card) =
      ∑ F ∈ faces B k, (B.filter (· ∈ F)).card := by
    simp only [card_filter]
    rw [sum_comm]
  rw [swap]
  apply sum_congr rfl
  intro F hf
  congr 1
  ext b
  simp only [mem_filter]
  exact ⟨fun hb => ⟨inside hf hb,hb⟩,And.right⟩

end SplitMatroidFlags
