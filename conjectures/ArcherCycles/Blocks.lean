module

public import conjectures.ArcherCycles.Statement

@[expose] public section
namespace ArcherCycles
open Finset

/-- Put the higher labels before the new minimum and the lower labels after it. -/
def join (q p : Word) : Word :=
  q.map (fun x ↦ p.length+1+x) ++ 0 :: p.map Nat.succ

def Bounded (w : Word) : Prop := ∀ x ∈ w, x < w.length

def Early (a b c : Edge) : Prop := a.1 < b.1 ∧ b.1 < c.1 ∧ a.2 < b.2 ∧ c.2=0

def HasEarly (w : Word) : Prop := ∃ a ∈ edges w, ∃ b ∈ edges w, ∃ c ∈ edges w, Early a b c

def low (e : Edge) : Edge := (e.1+1, if e.2=0 then 0 else e.2+1)

def high (r : ℕ) (e : Edge) : Edge :=
  (if e.1=0 then 0 else r+1+e.1, if e.2=0 then 1 else r+1+e.2)

private theorem splitPath (a : ℕ) (u v : Word) (b c : ℕ) :
    path a (u ++ b::v) c = path a u b ∪ path b v c := by
  induction u generalizing a with
  | nil => simp [path]
  | cons h t ih => simp [path, ih]

private theorem mapPath (f g : ℕ → ℕ) (u : Word) (a b : ℕ) (agree : ∀ x ∈ u, f x=g x) :
    (path a u b).image (fun e ↦ (f e.1,g e.2)) = path (f a) (u.map f) (g b) := by
  induction u generalizing a with
  | nil => simp [path]
  | cons h t ih => simp [path, agree h (by simp), ih h (fun x hx ↦ agree x (by simp [hx]))]

theorem edges_join (q p : Word) :
    edges (join q p) = (edges q).image (high p.length) ∪ (edges p).image low := by
  let f (x : ℕ) := if x=0 then 0 else p.length+1+x
  let g (x : ℕ) := if x=0 then 1 else p.length+1+x
  let h (x : ℕ) := if x=0 then 0 else x+1
  have H := mapPath f g (q.map Nat.succ) 0 0 (by simp [f,g])
  have L := mapPath Nat.succ h (p.map Nat.succ) 0 0 (by simp [h])
  change _ = (path 0 _ 0).image (fun e ↦ (f e.1,g e.2)) ∪
    (path 0 _ 0).image (fun e ↦ (Nat.succ e.1,h e.2))
  rw [H,L]
  simp [edges, join, List.map_append, List.map_map, Function.comp_def, f,g,h, splitPath,
    Nat.add_assoc]

private theorem boundPath {a b n : ℕ} {u : Word} (ha : a≤n) (hb : b≤n)
    (hu : ∀ x ∈ u, x≤n) : ∀ e ∈ path a u b, e.1≤n ∧ e.2≤n := by
  induction u generalizing a with
  | nil => simpa [path] using And.intro ha hb
  | cons h t ih =>
    intro e he
    rcases mem_insert.mp he with rfl|he
    · exact ⟨ha,hu _ (by simp)⟩
    · exact ih (hu _ (by simp)) (fun x hx ↦ hu x (by simp [hx])) e he

theorem bounded_edge {w : Word} (h : Bounded w) {e} (he : e ∈ edges w) :
    e.1≤w.length ∧ e.2≤w.length :=
  boundPath (a:=0) (b:=0) (u:=w.map Nat.succ) (Nat.zero_le _) (Nat.zero_le _)
    (by simpa [Bounded] using h) e he

private theorem positive_starts (a : ℕ) (w : Word) (ha : 0<a) :
    ∀ e ∈ path a (w.map Nat.succ) 0, 0<e.1 := by
  induction w generalizing a with
  | nil => simpa [path] using ha
  | cons x t ih =>
    intro e he
    rcases mem_insert.mp he with rfl|he
    · exact ha
    · exact ih _ (by omega) _ he

private theorem returns (a : ℕ) (w : Word) (ha : 0<a) :
    ∃ v>0, (v,0) ∈ path a (w.map Nat.succ) 0 := by
  induction w generalizing a with
  | nil => exact ⟨a,ha,by simp [path]⟩
  | cons x t ih =>
    obtain ⟨v,h,hv⟩ := ih (x+1) (by omega)
    exact ⟨v,h,mem_insert_of_mem hv⟩

theorem root_facts (w : Word) (h : w≠[]) :
    (0,0) ∉ edges w ∧ (∃ v>0, (v,0) ∈ edges w) ∧ (∃ v>0, (0,v)∈edges w) := by
  obtain ⟨x,t,rfl⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨v,hv,hm⟩ := returns (x+1) t (by omega)
  refine ⟨?_,⟨v,hv,mem_insert_of_mem hm⟩,⟨x+1,by omega,mem_insert_self ..⟩⟩
  intro he
  rcases mem_insert.mp he with eq|he
  · simp at eq
  · exact (by decide : ¬0<0) (positive_starts _ _ (by omega) (0,0) he)

end ArcherCycles
