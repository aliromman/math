module

public import conjectures.FerroniFacePrefix.Facets
public import conjectures.FerroniFacePrefix.Relabel
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace FerroniFacePrefix

open Finset

abbrev Label (m : ℕ) := Fin (m + 4)
abbrev Cell (m : ℕ) := Finset (Label m) × Label m × Bool

def toggle {T : Type} [DecidableEq T] (r : T) (S : Finset T) :=
  if r ∈ S then S.erase r else insert r S

lemma toggle_back {T : Type} [DecidableEq T] (r : T) : Function.Involutive (toggle r) := by
  intro S
  by_cases h : r ∈ S <;> simp [toggle,h]

private lemma toggle_away {T : Type} [DecidableEq T] {i r : T} (h : i ≠ r) (S : Finset T) :
    i ∈ toggle r S ↔ i ∈ S := by
  by_cases hr : r ∈ S <;> simp [toggle,hr,h]

def oddSize {T : Type} (S : Finset T) := decide (S.card % 2 = 1)

lemma toggle_odd {T : Type} [DecidableEq T] (r : T) (S : Finset T) :
    oddSize (toggle r S) = !oddSize S := by
  by_cases hr : r ∈ S
  · have hh : 0 < S.card := card_pos.mpr ⟨r,hr⟩
    simp only [oddSize,toggle,hr,↓reduceIte,card_erase_of_mem hr]
    by_cases h : S.card % 2 = 1 <;> simp [h] <;> omega
  · simp only [oddSize,toggle,hr,↓reduceIte,card_insert_of_notMem hr]
    by_cases h : S.card % 2 = 1 <;> simp [h] <;> omega

def color {m : ℕ} (x : Cell m) := x.1
def mark {m : ℕ} (x : Cell m) := x.2.1
def move {m : ℕ} (r : Label m) (x : Cell m) : Cell m := (toggle r (color x),x.2)

lemma move_back {m : ℕ} (r : Label m) : Function.Involutive (move r) := by
  rintro ⟨S,j,b⟩
  simp [move,color,toggle_back r S]

def ground (m : ℕ) (p : Bool) : Finset (Cell m) :=
  univ.filter fun x => mark x ∈ color x ∧ oddSize (color x) = p

lemma mem_ground {m : ℕ} {p : Bool} {x : Cell m} :
    x ∈ ground m p ↔ mark x ∈ color x ∧ oddSize (color x) = p := by simp [ground]

lemma move_mem {m : ℕ} {p : Bool} {x : Cell m} {r : Label m}
    (hx : x ∈ ground m p) (h : mark x ≠ r) : move r x ∈ ground m (!p) := by
  obtain ⟨hm,hp⟩ := mem_ground.mp hx
  exact mem_ground.mpr ⟨(toggle_away h _).mpr hm, (toggle_odd r _).trans (congrArg Bool.not hp)⟩

noncomputable def missing {m : ℕ} (J : Finset (Label m)) : Label m :=
  if h : ∃ r, r ∉ J then Classical.choose h else 0

lemma missing_notMem {m : ℕ} (J : Finset (Label m)) (h : J.card < m + 4) : missing J ∉ J := by
  classical
  have he : ∃ r, r ∉ J := by
    by_contra! hh
    have hU : J = univ := eq_univ_iff_forall.mpr hh
    simp [hU] at h
  simpa [missing,he] using Classical.choose_spec he

lemma ground_card (m : ℕ) : (ground m false).card = (ground m true).card := by
  let swap : Cell m → Cell m := fun x => move (missing {mark x}) x
  have hh (x : Cell m) : mark x ≠ missing {mark x} := by
    intro he
    exact missing_notMem {mark x} (by simp) (by simp [← he])
  have inv : Function.Involutive swap := fun x => move_back (missing {mark x}) x
  exact card_nbij' swap swap (fun x hx => move_mem hx (hh x)) (fun x hx => move_mem hx (hh x))
    (fun x _ => inv x) (fun x _ => inv x)

lemma duplicated {m : ℕ} {p : Bool} (x : Cell m) (hx : x ∈ ground m p) :
    ∃ y ∈ ground m p, y ≠ x ∧ color y = color x := by
  obtain ⟨S,j,b⟩ := x
  refine ⟨(S,j,!b),mem_ground.mpr (show j ∈ S ∧ oddSize S = p from (mem_ground.mp hx)),?_,rfl⟩
  cases b <;> simp

def choices (m : ℕ) (p : Bool) : Finset (Finset (Label m)) :=
  univ.filter fun S => oddSize S = p

private lemma colors (m : ℕ) (p : Bool) :
    (ground m p).image color = (choices m p).erase ∅ := by
  ext S
  constructor
  · intro hs
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
    obtain ⟨hj,hp⟩ := mem_ground.mp hx
    exact mem_erase.mpr ⟨(show (color x).Nonempty from ⟨_,hj⟩).ne_empty,by simpa [choices] using hp⟩
  · intro hs
    obtain ⟨hn,hp⟩ := mem_erase.mp hs
    obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr hn
    exact mem_image.mpr ⟨(S,j,false),mem_ground.mpr ⟨hj,by simpa [choices,color] using hp⟩,rfl⟩

lemma color_count (m : ℕ) :
    ((ground m false).image color).card + 1 = ((ground m true).image color).card := by
  let r : Label m := 0
  have eq : (choices m false).card = (choices m true).card := by
    apply card_nbij' (toggle r) (toggle r)
    · intro S hS
      simpa [choices,toggle_odd] using hS
    · intro S hS
      simpa [choices,toggle_odd] using hS
    · exact fun S _ => toggle_back r S
    · exact fun S _ => toggle_back r S
  have hin : ∅ ∈ choices m false := by simp [choices,oddSize]
  have hout : ∅ ∉ choices m true := by simp [choices,oddSize]
  rw [colors,colors,card_erase_of_mem hin,erase_eq_of_notMem hout]
  have hpos := card_pos.mpr (show (choices m false).Nonempty from ⟨_,hin⟩)
  omega

lemma enough_colors (m : ℕ) (p : Bool) : 3 ≤ ((ground m p).image color).card := by
  have hodd : m + 4 ≤ ((ground m true).image color).card := by
    have h : (univ : Finset (Label m)).card ≤ ((ground m true).image color).card := by
      apply card_le_card_of_injOn (fun j => {j})
      · intro j _
        exact mem_image.mpr ⟨({j},j,false),mem_ground.mpr ⟨by simp [mark,color],by simp [oddSize,color]⟩,rfl⟩
      · intro a _ b _ he
        simpa using he
    simpa using h
  have he := color_count m
  cases p <;> omega

def markers {m : ℕ} (F : Finset (Finset (Cell m))) := (F.biUnion id).image mark

private lemma same_markers {m : ℕ} (r : Label m) (F : Finset (Finset (Cell m))) :
    markers (relabel (move r) F) = markers F := by
  rw [markers,relabel_support,image_image]
  rfl

noncomputable def swapFace {m : ℕ} (F : Finset (Finset (Cell m))) :=
  relabel (move (missing (markers F))) F

private lemma swap_back {m : ℕ} : Function.Involutive (@swapFace m) := by
  intro F
  simp only [swapFace,same_markers]
  exact relabel_involutive (move_back _) F

lemma prefix_equal (m k : ℕ) (hk : k + 2 < m + 4) :
    faceNumber (bases color (ground m false)) k = faceNumber (bases color (ground m true)) k := by
  have transport (p : Bool) (F : Finset (Finset (Cell m))) (h : F ∈ faces (bases color (ground m p)) k) :
      swapFace F ∈ faces (bases color (ground m (!p))) k := by
    obtain ⟨hF,hd⟩ := mem_faces.mp h
    have hs : (markers F).card < m+4 := by
      have hc : (markers F).card ≤ (F.biUnion id).card := card_image_le
      have hb := support_bound hF
      omega
    let r := missing (markers F)
    have hmove (x) (hx : x ∈ F.biUnion id) : move r x ∈ ground m (!p) := by
      have havoid : mark x ≠ r := by
        intro h
        apply missing_notMem (markers F) hs
        change r ∈ markers F
        rw [← h]
        exact mem_image_of_mem mark hx
      obtain ⟨t,ht,xt⟩ := mem_biUnion.mp hx
      obtain ⟨_,w,hw⟩ := hF
      have tsub := (mem_powersetCard.mp (mem_filter.mp ((hw t).mp ht).1).1).1
      exact move_mem (tsub xt) havoid
    obtain ⟨new,dim⟩ := relabel_face (move_back r).injective (toggle_back r).injective
      (fun _ => rfl) hF hmove
    exact mem_faces.mpr ⟨new,dim.trans hd⟩
  change (faces (bases color (ground m false)) k).card = (faces (bases color (ground m true)) k).card
  exact card_nbij' swapFace swapFace (fun F h => transport false F h) (fun F h => transport true F h)
    (fun F _ => swap_back F) (fun F _ => swap_back F)

end FerroniFacePrefix
