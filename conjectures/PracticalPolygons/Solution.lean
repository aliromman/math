module

public import conjectures.PracticalPolygons.Ranges
public import conjectures.PracticalPolygons.Residues
public import conjectures.PracticalPolygons.FiniteData
import Mathlib.Tactic.NormNum

public section
namespace PracticalPolygons

private theorem small_practical {p : ℕ} (hp : p∈smallPracticals) : Practical p := by
  simp only [smallPracticals,multiples,List.mem_append,List.mem_flatMap,List.mem_map,
    List.mem_range,or_assoc] at hp
  rcases hp with ⟨a,_,j,hj,rfl⟩ | ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
  · exact twoPower_practical a (j+1) (by omega) (by omega)
  · exact six_practical (j+1) (by omega) (by omega)
  · exact scale_practical 1 1 (j+1) (by decide) (by decide) (by omega) (by omega)
  · exact scale_practical 1 2 (j+1) (by decide) (by decide) (by omega) (by omega)

private theorem moderate {s n M H : ℕ} (hs : Orders s) (pos : 0<M)
    (practical : ∀ t, 0<t → 5*t≤12*M → Practical (M*t))
    (mask : ((2^M-1) &&& residueBits s H M)=2^M-1)
    (lo : 2*polygonal 10 H<n) (hi : 5*n≤12*M^2) : Represented s n := by
  obtain ⟨x,hx,y,hy,res⟩ := residue_cover mask n pos
  have size : s≤10 := by rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have bound {i : ℕ} (h : i≤H) : polygonal s i≤polygonal 10 H :=
    Nat.add_le_add (Nat.mul_le_mul (Nat.sub_le_sub_right size 2) (Nat.choose_le_choose 2 h)) h
  exact fill_layer pos practical res (by have := bound hx; have := bound hy; omega) hi

/-- Every positive integer is a practical number plus two polygonal numbers of the given order. -/
theorem conjecture14 : Conjecture := by
  intro s hs n hn
  apply cover_scales (s:=s) (n:=n) ?_ (fun _ _ hd ↦ large_residue hs hd)
  intro upper
  by_cases small : n≤400000
  · obtain ⟨p,hp,x,y,eq⟩ := small_values hs hn small
    exact ⟨p,x,y,small_practical hp,eq⟩
  obtain ⟨first,second,third⟩ := moderate_check hs
  by_cases h₁ : n≤1350000
  · apply moderate (M:=750) (H:=223) hs (by decide) (scale_practical 1 3 · (by decide) (by decide)) first
    · exact lt_of_le_of_lt (by norm_num [polygonal,Nat.choose_two_right]) (Nat.lt_of_not_ge small)
    · exact (Nat.mul_le_mul_left 5 h₁).trans (by decide)
  by_cases h₂ : n≤33750000
  · apply moderate (M:=3750) (H:=411) hs (by decide) (scale_practical 1 4 · (by decide) (by decide)) second
    · exact lt_of_le_of_lt (by norm_num [polygonal,Nat.choose_two_right]) (Nat.lt_of_not_ge h₁)
    · exact (Nat.mul_le_mul_left 5 h₂).trans (by decide)
  exact moderate (M:=18750) (H:=1204) hs (by decide) (scale_practical 1 5 · (by decide) (by decide)) third
    (lt_of_le_of_lt (by norm_num [polygonal,Nat.choose_two_right]) (Nat.lt_of_not_ge h₂)) upper

/-- info: 'PracticalPolygons.conjecture14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjecture14

end PracticalPolygons
