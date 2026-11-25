module

public import conjectures.HurKimFairDice.Statement

@[expose] public section
namespace HurKimFairDice

/-- Three eight-sided dice, in increasing order of their face labels. -/
def witness : Word := [0,0,1,2,2,2,0,1,1,2,2,0,1,1,1,1,2,0,0,0,0,1,2,2]

theorem fair_witness : Fair witness := by unfold Fair; decide

theorem isolated {w : Word} (h : Similar witness w) : w = witness := by
  have a : ∀ i j : Fin (witness.length+1), exchange witness i j = witness := by decide
  have b : ∀ (i j : Fin (witness.length+1)) (f : Bool), shift witness i j f = witness := by decide
  induction h with
  | refl => rfl
  | tail _ step ih =>
    subst_vars
    cases step with
    | exchange i j => exact a i j
    | shift i j f => exact b i j f

/-- No permutation-palindrome block can start with two equal letters. -/
theorem no_block (x y z : Die) (h : [x,y,z].Nodup) (v : Word) :
    ¬ Similar witness ([x,y,z,z,y,x] ++ v) := by
  intro e
  have eq := isolated e
  change x :: y :: _ = 0 :: 0 :: _ at eq
  have eq' := List.cons.inj eq
  exact h.notMem ((List.mem_cons.mpr (Or.inl (eq'.1.trans (List.cons.inj eq'.2).1.symm))))

theorem resolution : ¬ Conjecture := by
  intro h
  obtain ⟨x,y,z,k,hn,e⟩ := (h witness fair_witness).2
  cases k with
  | zero => have he := isolated e; simp [witness] at he
  | succ k =>
    rw [List.replicate_succ, List.flatten_cons] at e
    exact no_block x y z hn _ e

/-- info: 'HurKimFairDice.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end HurKimFairDice
