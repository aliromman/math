module

public import conjectures.MarkovFactorFour.Farey
public import conjectures.MarkovFactorFour.Nilpotent

@[expose] public section
namespace MarkovFactorFour

variable {R : Type*} [CommRing R]

private def character (x x' y y' : R) (a b : ℕ) : R := x^a*y^b + x'^a*y'^b

private theorem character_step (x x' y y' : R) (a b c d : ℕ) :
    character x x' y y' a b * character x x' y y' (a+c) (b+d) -
      (x*x')^a * (y*y')^b * character x x' y y' c d =
    character x x' y y' (a+(a+c)) (b+(b+d)) := by
  simp only [character, pow_add, mul_pow]
  ring

private def good (φ : Poly →+* R) (s t : R) (p : Vertex) : Prop :=
  let L := 1+φ u+φ v
  L * φ p.num = character s (L-s) (L-t) t p.a p.b

private theorem good_extend (φ : Poly →+* R) (s t : R)
    (hs : s*(1+φ u+φ v-s)=φ u) (ht : (1+φ u+φ v-t)*t=φ v)
    (p q : Vertex) (m : Poly) (hp : good φ s t p) (hq : good φ s t q)
    (hm : good φ s t ⟨p.a+q.a, p.b+q.b, m⟩) :
    good φ s t ⟨p.a+(p.a+q.a), p.b+(p.b+q.b), extend p q m⟩ := by
  let L := 1+φ u+φ v
  change L * φ p.num = _ at hp
  change L * φ q.num = _ at hq
  change L * φ m = _ at hm
  change L * φ (extend p q m) = _
  calc
    _ = (L*φ p.num)*(L*φ m) - (φ u)^p.a*(φ v)^p.b*(L*φ q.num) := by
      simp only [extend, map_sub, map_mul, map_add, map_one, map_pow, L]
      ring
    _ = _ := by
      rw [hp, hq, hm]
      have h := character_step s (L-s) (L-t) t p.a p.b q.a q.b
      change s*(L-s)=φ u at hs
      change (L-t)*t=φ v at ht
      rwa [hs,ht] at h

private theorem good_follow (φ : Poly →+* R) (s t : R)
    (hs : s*(1+φ u+φ v-s)=φ u) (ht : (1+φ u+φ v-t)*t=φ v)
    (path : List Bool) (T : Triangle)
    (hT : good φ s t T.left ∧ good φ s t T.right ∧ good φ s t (center T)) :
    good φ s t (center (follow T path)) := by
  induction path generalizing T with
  | nil => exact hT.2.2
  | cons dir path ih =>
    rcases hT with ⟨hl,hr,hm⟩
    cases dir with
    | false =>
      exact ih (leftChild T) ⟨hl, hm, good_extend φ s t hs ht T.left T.right T.middle hl hr hm⟩
    | true =>
      apply ih (rightChild T)
      refine ⟨hm, hr, ?_⟩
      have hm' : good φ s t ⟨T.right.a+T.left.a,T.right.b+T.left.b,T.middle⟩ := by
        simpa [center, Nat.add_comm] using hm
      simpa [center, rightChild, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        good_extend φ s t hs ht T.right T.left T.middle hr hl hm'

/-- The two characters give the trace for every reduced slope in a ring with 4=0. -/
theorem trace_identity (φ : Poly →+* R) (hfour : (4 : R)=0) (s t : R)
    (hs : s*(1+φ u+φ v-s)=φ u) (ht : t*(1+φ u+φ v-t)=φ v)
    (hsnil : IsNilpotent s) (htnil : IsNilpotent t)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (hc : a.Coprime b) :
    let L := 1+φ u+φ v
    L*φ (numerator a b) = s^a*(L-t)^b+(L-s)^a*t^b := by
  have init : good φ s t initial.left ∧ good φ s t initial.right ∧ good φ s t (center initial) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [good, initial, character]
    · simp [good, initial, character]
    · simpa [good, initial, center, character] using mixed_trace hfour hs ht hsnil htnil
  have h := good_follow φ s t hs (by simpa [mul_comm] using ht) (path b a) initial init
  obtain ⟨h1,h2⟩ := selected_coordinates a b ha hb hc
  dsimp only [good] at h
  rw [h1,h2] at h
  exact h

end MarkovFactorFour
