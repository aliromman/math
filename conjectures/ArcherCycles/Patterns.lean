module

public import conjectures.ArcherCycles.Blocks

@[expose] public section
namespace ArcherCycles
open Finset

private theorem origin {p q : Word} {e} (he : e ∈ edges (join q p)) :
    (∃ f ∈ edges q, high p.length f=e) ∨ (∃ f ∈ edges p, low f=e) := by
  simpa [edges_join, Finset.mem_image] using he

private theorem injectHigh {p q : Word} {e} (he : e ∈ edges q) :
    high p.length e ∈ edges (join q p) := by
  rw [edges_join]
  exact mem_union_left _ (mem_image_of_mem _ he)

private theorem injectLow {p q : Word} {e} (he : e ∈ edges p) :
    low e ∈ edges (join q p) := by
  rw [edges_join]
  exact mem_union_right _ (mem_image_of_mem _ he)

private theorem low_col (a b : Edge) : (low a).2 < (low b).2 ↔ a.2 < b.2 := by
  simp only [low]
  split_ifs <;> omega

private theorem high_row (r : ℕ) (a b : Edge) :
    (high r a).1 < (high r b).1 ↔ a.1 < b.1 := by
  simp only [high]
  split_ifs <;> omega

private theorem high_col (r : ℕ) (a b : Edge) :
    (high r a).2 < (high r b).2 ↔ a.2 < b.2 := by
  simp only [high]
  split_ifs <;> omega

private theorem four_high (r : ℕ) (a b c d : Edge) :
    Four (high r a) (high r b) (high r c) (high r d) ↔ Four a b c d := by
  simp only [Four, high_col, high_row]

private theorem four_low (a b c d : Edge) : Four (low a) (low b) (low c) (low d) ↔
    Four a b c d := by
  simp only [Four, low_col]
  simp [low]

private theorem high_shape (r : ℕ) (e : Edge) :
    ((high r e).1=0 ∨ r+1 < (high r e).1) ∧ ((high r e).2=1 ∨ r+1 < (high r e).2) := by
  simp only [high]
  split_ifs <;> omega

private theorem low_shape {p : Word} (bp : Bounded p) {e} (he : e ∈ edges p) :
    0 < (low e).1 ∧ (low e).1 ≤ p.length+1 ∧ (low e).2 ≤ p.length+1 ∧
    ((low e).2=0 ∨ 1<(low e).2) := by
  obtain ⟨_,_⟩ := bounded_edge bp he
  simp only [low]
  split_ifs <;> omega

private theorem low_zero (e : Edge) : (low e).2=0 ↔ e.2=0 := by
  simp [low]

private theorem high_first {p q : Word} {e} (he : e ∈ edges q)
    (hr : p.length+1 < (high p.length e).1) : q≠[] := by
  rintro rfl
  simp [edges, path] at he
  subst e
  simp [high] at hr

private theorem last_source (a : ℕ) (w : Word) {e f : Edge}
    (he : e ∈ path a (w.map Nat.succ) 0) (hf : f ∈ path a (w.map Nat.succ) 0)
    (ez : e.2=0) (fz : f.2=0) : e.1=f.1 := by
  induction w generalizing a with
  | nil => simp [path] at he hf; simp [he,hf]
  | cons x t ih =>
    rcases mem_insert.mp he with rfl|he
    · simp at ez
    rcases mem_insert.mp hf with rfl|hf
    · simp at fz
    exact ih _ he hf

private theorem crossed {p q : Word} (bp : Bounded p) {a b c d}
    (ha : a∈edges p) (hb : b∈edges p) (hc : c∈edges p) (hd : d∈edges q)
    (h : Four (low a) (low b) (low c) (high p.length d)) : q≠[] ∧ HasEarly p := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := h
  obtain ⟨hr,hs⟩ := high_shape p.length d
  obtain ⟨_,_,_,_⟩ := low_shape bp ha
  obtain ⟨_,_,_,_⟩ := low_shape bp hc
  refine ⟨high_first (p:=p) hd (by omega),a,ha,b,hb,c,hc,?_,?_,(low_col _ _).mp h₆,
    (low_zero _).mp (by omega)⟩
  · simpa [low] using h₁
  · simpa [low] using h₂

local macro "shapes" x:ident "at" hx:ident "in" p:ident bp:ident : tactic =>
  `(tactic| first
    | (have := low_shape $bp $hx)
    | (have := high_shape (List.length $p) $x))

theorem contains_join {p q : Word} (bp : Bounded p) :
    Has3412 (join q p) ↔ Has3412 q ∨ Has3412 p ∨ (q≠[] ∧ HasEarly p) := by
  constructor
  · rintro ⟨aa,haa,bb,hbb,cc,hcc,dd,hdd,h⟩
    obtain ⟨a,ha,rfl⟩|⟨a,ha,rfl⟩ := origin haa <;>
      obtain ⟨b,hb,rfl⟩|⟨b,hb,rfl⟩ := origin hbb <;>
      obtain ⟨c,hc,rfl⟩|⟨c,hc,rfl⟩ := origin hcc <;>
      obtain ⟨d,hd,rfl⟩|⟨d,hd,rfl⟩ := origin hdd
    case inl.inl.inl.inl => exact Or.inl ⟨a,ha,b,hb,c,hc,d,hd,(four_high ..).mp h⟩
    all_goals first
      | exact Or.inr (Or.inl ⟨a,ha,b,hb,c,hc,d,hd,(four_low ..).mp h⟩)
      | exact Or.inr (Or.inr (crossed bp ha hb hc hd h))
      | (shapes a at ha in p bp; shapes b at hb in p bp
         shapes c at hc in p bp; shapes d at hd in p bp
         obtain ⟨_,_,_,_,_,_⟩ := h; exfalso; omega)
  · rintro (⟨a,ha,b,hb,c,hc,d,hd,h⟩|⟨a,ha,b,hb,c,hc,d,hd,h⟩|⟨hq,a,ha,b,hb,c,hc,h⟩)
    · exact ⟨_,injectHigh ha,_,injectHigh hb,_,injectHigh hc,_,injectHigh hd,(four_high ..).mpr h⟩
    · exact ⟨_,injectLow ha,_,injectLow hb,_,injectLow hc,_,injectLow hd,(four_low ..).mpr h⟩
    · obtain ⟨v,hv,hd⟩ := (root_facts q hq).2.1
      obtain ⟨r,s,t,u⟩ := h
      have bc := bounded_edge bp hc
      refine ⟨_,injectLow ha,_,injectLow hb,_,injectLow hc,_,injectHigh hd,
        ?_,?_,?_,?_,?_,(low_col ..).mpr t⟩
      · simpa [low] using r
      · simpa [low] using s
      · simp [high,low,Nat.ne_of_gt hv]
        omega
      · simp [high,low,u]
      · have nz : a.2≠0 := fun h ↦ (by omega : a.1≠c.1) (last_source 0 p ha hc h u)
        simp [high,low,nz]
        omega

private theorem early_low (a b c : Edge) : Early (low a) (low b) (low c) ↔ Early a b c := by
  simp only [Early, low_col, low_zero]
  simp [low]

private theorem crossed_early {p q : Word} (bp : Bounded p) {a b c}
    (ha : a∈edges q) (hb : b∈edges p) (hc : c∈edges p)
    (h : Early (high p.length a) (low b) (low c)) : q=[] ∧ p≠[] := by
  obtain ⟨h₁,h₂,h₃,_⟩ := h
  obtain ⟨hr,hv⟩ := high_shape p.length a
  obtain ⟨_,_,_,_⟩ := low_shape bp hb
  have row : (high p.length a).1=0 := by omega
  have col : (high p.length a).2=1 := by omega
  have aa : a=(0,0) := by
    apply Prod.ext <;> simp only [high] at row col <;> split_ifs at row col <;> omega
  constructor
  · by_contra nq
    exact (root_facts q nq).1 (aa ▸ ha)
  · rintro rfl
    simp [edges,path] at hb hc
    subst b c
    simp at h₂

theorem early_join {p q : Word} (bp : Bounded p) :
    HasEarly (join q p) ↔ HasEarly p ∨ (q=[] ∧ p≠[]) := by
  constructor
  · rintro ⟨aa,haa,bb,hbb,cc,hcc,h⟩
    obtain ⟨a,ha,rfl⟩|⟨a,ha,rfl⟩ := origin haa <;>
      obtain ⟨b,hb,rfl⟩|⟨b,hb,rfl⟩ := origin hbb <;>
      obtain ⟨c,hc,rfl⟩|⟨c,hc,rfl⟩ := origin hcc
    all_goals first
      | exact Or.inl ⟨a,ha,b,hb,c,hc,(early_low ..).mp h⟩
      | exact Or.inr (crossed_early bp ha hb hc h)
      | (shapes a at ha in p bp; shapes b at hb in p bp; shapes c at hc in p bp
         obtain ⟨_,_,_,_⟩ := h; exfalso; omega)
  · rintro (⟨a,ha,b,hb,c,hc,h⟩|⟨rfl,np⟩)
    · exact ⟨_,injectLow ha,_,injectLow hb,_,injectLow hc,(early_low ..).mpr h⟩
    · obtain ⟨_,⟨u,hu,hi⟩,v,hv,ho⟩ := root_facts p np
      have root : (0,0)∈edges [] := by simp [edges,path]
      exact ⟨_,injectHigh root,_,injectLow ho,_,injectLow hi,by simp [Early,high,low,hu,Nat.ne_of_gt hv,hv]⟩

end ArcherCycles
