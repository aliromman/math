module

public import conjectures.GallianRusinGame.Enumeration
public import conjectures.GallianRusinGame.Extraction
import Mathlib.Tactic.Ring

public section
namespace GallianRusinGame
open GallianRusin Polynomial Finset

set_option maxRecDepth 4096

private theorem triple {t u v : Code} (a : t.a+u.a+v.a=3) (b : t.b+u.b+v.b=3)
    (c : t.c+u.c+v.c=3) (d : t.d+u.d+v.d=3) :
    assemble t*assemble u*assemble v=standard 30^3 := by
  rw [standard_eq,assemble_eq,assemble_eq,assemble_eq,assemble_eq]
  calc
    _ = (cyclotomic 2 ℤ * cyclotomic 3 ℤ * cyclotomic 5 ℤ)^3 *
      (cyclotomic 6 ℤ)^(t.a+u.a+v.a) * (cyclotomic 10 ℤ)^(t.b+u.b+v.b) *
      (cyclotomic 15 ℤ)^(t.c+u.c+v.c) * (cyclotomic 30 ℤ)^(t.d+u.d+v.d) := by
        simp only [pow_add]
        ring
    _ = _ := by rw [a,b,c,d]; ring

private theorem ordinary : Die 30 (standard 30) := by
  rw [standard_eq]
  exact choices_are_dice (by decide)

private theorem pad {P : ℤ[X]} {k t : ℕ} (g : Plays 30 k P) (h : k≤t) : Plays 30 t P := by
  induction t,h using Nat.le_induction with
  | base => exact g
  | succ t _ ih =>
    obtain ⟨dp,others,len,faces,product⟩ := ih
    refine ⟨dp,standard 30::others,by simp [←len],?_,?_⟩
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl|inList
      · exact ordinary
      · exact faces _ inList
    · simp only [List.prod_cons,pow_succ]
      rw [←product]
      ring

private theorem play_three {P Q R : ℤ[X]} (p : Die 30 P) (q : Die 30 Q) (r : Die 30 R)
    (prod : P*Q*R=standard 30^3) : Plays 30 3 P := by
  refine ⟨p,[Q,R],rfl,?_,?_⟩
  · intro Z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> assumption
  · simpa [mul_assoc] using prod

private theorem extract_choices {P : ℤ[X]} (game : SolutionDie 30 P) : ∃ t∈choices,assemble t=P := by
  obtain ⟨t,a,b,c,d,rfl⟩ := extraction game
  exact ⟨_,valid_choice game.1 a b c d,rfl⟩

private theorem others_three {P : ℤ[X]} (g : Plays 30 3 P) :
    ∃ Q R, SolutionDie 30 Q ∧ SolutionDie 30 R ∧ P*Q*R=standard 30^3 := by
  obtain ⟨p,others,len,faces,product⟩ := g
  cases others with
  | nil => simp at len
  | cons Q others =>
    cases others with
    | nil => simp at len
    | cons R rest =>
      have empty : rest=[] := by simpa using len
      subst rest
      have q := faces Q (by simp)
      have r := faces R (by simp)
      simp only [List.prod_cons,List.prod_nil,mul_one] at product
      refine ⟨Q, R, solutionDie_iff_plays.mpr ⟨3, by decide, ?_⟩,
        solutionDie_iff_plays.mpr ⟨3, by decide, ?_⟩, by simpa [mul_assoc] using product⟩
      · exact play_three q p r (by rw [←product]; ring)
      · exact play_three r p q (by rw [←product]; ring)

private theorem exception_four : Plays 30 4 (assemble exception) := by
  let u : Code := ⟨0,1,1,1⟩
  let v : Code := ⟨1,2,2,2⟩
  have du : Die 30 (assemble u) := choices_are_dice (by decide)
  have dv : Die 30 (assemble v) := choices_are_dice (by decide)
  refine ⟨choices_are_dice (by decide),[assemble u,assemble u,assemble v],rfl,?_,?_⟩
  · intro Q hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with e|e|e
    · exact e ▸ du
    · exact e ▸ du
    · exact e ▸ dv
  · simp only [List.prod_cons,List.prod_nil,mul_one,standard_eq,assemble_eq,u,v,exception]
    ring

private theorem exception_fails : ¬Plays 30 3 (assemble exception) := by
  intro h
  obtain ⟨Q,R,q,r,prod⟩ := others_three h
  obtain ⟨u,hu,rfl⟩ := extract_choices q
  obtain ⟨v,hv,rfl⟩ := extract_choices r
  apply exception_no_triple u hu v hv
  simpa [key_eq,standard_eq] using congrArg (fun P : ℤ[X] ↦ P.eval 256) prod

/-- Only one solution die needs more than three dice. -/
theorem unique_exception {P : ℤ[X]} (g : SolutionDie 30 P) :
    ¬Plays 30 3 P ↔ P=assemble exception := by
  constructor
  · intro no
    obtain ⟨t,ht,rfl⟩ := extract_choices g
    by_contra neq
    have h : t≠exception := fun e ↦ neq (congrArg assemble e)
    obtain ⟨u,hu,v,hv,a,b,c,d⟩ := partners t ht h
    exact no (play_three (choices_are_dice ht) (choices_are_dice hu) (choices_are_dice hv) (triple a b c d))
  · rintro rfl
    exact exception_fails

/-- The coefficient at j-1 gives the number of faces labeled j. -/
theorem exception_faces : assemble exception=polynomial [1,0,2,2,3,3,4,4,3,3,2,2,0,1] :=
  congrArg polynomial (by decide : coefficients exception=[1,0,2,2,3,3,4,4,3,3,2,2,0,1])

theorem exactly_forty_four : Set.ncard {P : ℤ[X] | SolutionDie 30 P}=44 := by
  classical
  have eq : {P : ℤ[X] | SolutionDie 30 P}=(choices.image assemble : Finset ℤ[X]) := by
    ext P
    simp only [Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_image]
    refine ⟨extract_choices,?_⟩
    rintro ⟨t,ht,rfl⟩
    by_cases h : t=exception
    · rw [h]
      exact solutionDie_iff_plays.mpr ⟨4,by decide,exception_four⟩
    obtain ⟨u,hu,v,hv,a,b,c,d⟩ := partners t ht h
    exact solutionDie_iff_plays.mpr ⟨3,by decide,play_three (choices_are_dice ht) (choices_are_dice hu)
      (choices_are_dice hv) (triple a b c d)⟩
  rw [eq,Set.ncard_coe_finset,Finset.card_image_of_injOn]
  · exact number
  · intro t ht u hu h
    apply distinct_keys t ht u hu
    rw [key_eq,key_eq,h]

theorem resolution : Conjecture := by
  constructor
  · intro P g
    by_cases h : Plays 30 3 P
    · exact ⟨3,by decide,h⟩
    · rw [(unique_exception g).mp h]
      exact ⟨4,by decide,exception_four⟩
  · exact ⟨_,exception_four,fun k hk h ↦ exception_fails (pad h (by omega))⟩

/-- info: 'GallianRusinGame.multiplicity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multiplicity_bound

/-- info: 'GallianRusinGame.unique_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unique_exception

/-- info: 'GallianRusinGame.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end GallianRusinGame
