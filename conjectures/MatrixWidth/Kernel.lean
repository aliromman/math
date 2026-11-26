module

public import conjectures.MatrixWidth.Statement
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity

@[expose] public section
namespace MatrixWidth
open Finset

theorem card_outcome (k d x : ℕ) :
    Fintype.card (Outcome k d x) = (k+x).choose (min d (k+x)) ^ k := by
  simp [Outcome, Draw]

theorem card_outcome_pos (k d x : ℕ) : 0 < Fintype.card (Outcome k d x) := by
  rw [card_outcome]
  exact pow_pos (Nat.choose_pos (min_le_right _ _)) _

theorem component_subset {k d x : ℕ} (f : Outcome k d x) (i : Fin k) : (f i).val ⊆ covered f :=
  fun _ hz => mem_biUnion.mpr ⟨i,mem_univ _,hz⟩

theorem covered_bounds {k d x : ℕ} (f : Outcome k d x) :
    (covered f).card ≤ k+x ∧ (covered f).card ≤ k*d := by
  constructor
  · simpa only [Fintype.card_fin] using Finset.card_le_univ (covered f)
  · calc
      _ ≤ ∑ i : Fin k, (f i).val.card := card_biUnion_le
      _ = k * min d (k+x) := by simp_rw [(f _).property]; simp
      _ ≤ _ := Nat.mul_le_mul_left _ (min_le_left ..)

theorem covered_ge {k d x : ℕ} (hk : 0<k) (f : Outcome k d x) :
    min d (k+x) ≤ (covered f).card := by
  rw [←(f ⟨0,hk⟩).property]
  exact Finset.card_le_card (component_subset f ⟨0,hk⟩)

theorem transition_nonneg (k d x y : ℕ) : 0≤transition k d x y := by
  unfold transition
  positivity

theorem transition_pos {k d x y : ℕ} :
    0<transition k d x y ↔ ∃ f : Outcome k d x, next f = y := by
  have h : (0:ℝ)<Fintype.card (Outcome k d x) := by exact_mod_cast card_outcome_pos k d x
  rw [transition, div_pos_iff_of_pos_right h, Nat.cast_pos, card_pos]
  simp [Finset.Nonempty]

theorem transition_support {k d x y : ℕ} (h : 0<transition k d x y) :
    y ≤ x+k ∧ x ≤ y+k*d := by
  obtain ⟨f,rfl⟩ := transition_pos.mp h
  have hb := covered_bounds f
  unfold next
  omega

theorem row_sum (k d x : ℕ) : ∑ y ∈ range (x+k+1), transition k d x y=1 := by
  have hs : ∑ j ∈ range (x+k+1), (univ.filter (fun f : Outcome k d x => next f=j)).card =
      Fintype.card (Outcome k d x) := by
    have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Outcome k d x))
      (range (x+k+1)) next
    simpa [show ∀ f : Outcome k d x, next f<x+k+1 by intro f; unfold next; omega] using h
  have hpos : (Fintype.card (Outcome k d x):ℝ) ≠ 0 := by exact_mod_cast (card_outcome_pos k d x).ne'
  simp only [transition, ← sum_div, ← Nat.cast_sum, hs, div_self hpos]

private def segment {u d r : ℕ} (hd : d≤r) (hr : r≤u) (i : ℕ) : Fin d ↪ Fin u where
  toFun j := ⟨min (i*d) (r-d)+j.val, by
    have hm := Nat.min_le_right (i*d) (r-d)
    omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)

theorem union_size_attainable {k d x r : ℕ} (hd : 0<d) (hdu : d≤r)
    (hru : r≤k+x) (hrk : r≤k*d) : ∃ f : Outcome k d x, (covered f).card=r := by
  let f : Outcome k d x := fun i =>
    ⟨univ.map (segment hdu hru i.val), by simp [Nat.min_eq_left (hdu.trans hru)]⟩
  refine ⟨f,?_⟩
  have hset : covered f = univ.map (Fin.castLEEmb hru) := by
    ext y
    constructor
    · intro hy
      rcases mem_biUnion.mp hy with ⟨i,_,hi⟩
      rcases mem_map.mp hi with ⟨j,_,hj⟩
      have hm := Nat.min_le_right (i.val*d) (r-d)
      have hval : y.val=min (i.val*d) (r-d)+j.val := (congrArg Fin.val hj).symm
      refine mem_map.mpr ⟨⟨y.val,by omega⟩,mem_univ _,Fin.ext rfl⟩
    · intro hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hy
      have hi : a.val/d<k := Nat.div_lt_iff_lt_mul hd |>.mpr (by omega)
      let i : Fin k := ⟨a.val/d, hi⟩
      let t := min (i.val*d) (r-d)
      have htd : t≤a.val := (Nat.min_le_left ..).trans (Nat.div_mul_le_self ..)
      have hu : a.val<t+d := by
        have hrem := Nat.mod_lt a.val hd
        have hmul := Nat.mod_add_div a.val d
        dsimp [t,i]
        have hn : a.val / d * d + a.val % d = a.val := Nat.div_add_mod' ..
        omega
      apply mem_biUnion.mpr
      refine ⟨i,mem_univ _,mem_map.mpr ⟨⟨a.val-t,by omega⟩,mem_univ _,?_⟩⟩
      apply Fin.ext
      change t+(a.val-t)=a.val
      omega
  simp [hset]

theorem transition_of_union {k d x r : ℕ} (hd : 0<d) (hdu : d≤r)
    (hru : r≤k+x) (hrk : r≤k*d) : 0<transition k d x (k+x-r) := by
  obtain ⟨f,hf⟩ := union_size_attainable hd hdu hru hrk
  exact transition_pos.mpr ⟨f, by simp [next,hf]⟩

abbrev Fiber (k d x r : ℕ) := {f : Outcome k d x // (covered f).card=r}

private abbrev UnionCode (k x r : ℕ) :=
  Σ s : {s : Finset (Fin (k+x)) // s.card=r}, (Fin k → Finset s.val)

private def encode {k d x r : ℕ} (f : Fiber k d x r) : UnionCode k x r :=
  ⟨⟨covered f.val, f.property⟩,fun i => (f.val i).val.subtype (·∈covered f.val)⟩

private def readCode {k x r : ℕ} (v : UnionCode k x r) (i : Fin k) : Finset (Fin (k+x)) :=
  (v.2 i).map (Function.Embedding.subtype _)

private theorem read_encode {k d x r : ℕ} (f : Fiber k d x r) (i : Fin k) :
    readCode (encode f) i = (f.val i).val := by
  ext z
  simp [readCode, encode]
  exact @component_subset _ _ _ f.val i z

theorem fiber_bound (k d x r : ℕ) : Fintype.card (Fiber k d x r) ≤ (k+x).choose r*(2^r)^k := by
  calc
    _ ≤ Fintype.card (UnionCode k x r) := Fintype.card_le_of_injective encode (by
      intro a b h
      apply Subtype.ext
      funext i
      apply Subtype.ext
      simpa only [read_encode] using congrArg (fun v => readCode v i) h)
    _ = _ := by
      simp only [UnionCode,Fintype.card_sigma,Fintype.card_fun,Fintype.card_finset,
        Fintype.card_coe,Fintype.card_fin]
      have h (s : {s : Finset (Fin (k+x)) // s.card=r}) : s.val.card=r := s.property
      simp [h]

end MatrixWidth
