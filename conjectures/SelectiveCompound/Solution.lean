module

public import conjectures.SelectiveCompound.Extremal
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

public section
namespace SelectiveCompound.Game
variable {α : Type*} (G : Game α)

-- At most b + l − v values above v can be missing from this increasing sequence.
private theorem gap_count {f : ℕ → ℕ} (strict : StrictMono f) {b l v : ℕ}
    (upper : ∀ i, f i ≤ i+b) (start : v ≤ f l) (s : Finset ℕ)
    (above : ∀ x ∈ s, v ≤ x) (missing : ∀ x ∈ s, ∀ i, f i ≠ x) :
    s.card + v ≤ b + l := by
  let z := l + v + s.sup id + 1
  let t := (Finset.Ico l z).image f
  have disjoint : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro x hx ht
    obtain ⟨i,_,hit⟩ := Finset.mem_image.mp ht
    exact missing x hx i hit
  have contained : s ∪ t ⊆ Finset.Ico v (z+b) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hs | ht
    · have h := Finset.le_sup (f := id) hs
      exact Finset.mem_Ico.mpr ⟨above _ hs, by dsimp [z] at *; omega⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨low,high⟩ := Finset.mem_Ico.mp hi
      exact Finset.mem_Ico.mpr ⟨start.trans (strict.monotone low), by have := upper i; omega⟩
  have count := Finset.card_le_card contained
  rw [Finset.card_union_of_disjoint disjoint, Finset.card_image_of_injective _ strict.injective,
    Nat.card_Ico, Nat.card_Ico] at count
  dsimp [z] at count
  omega

/-- Any unsaturated entry gives a rectangle whose side lengths add to the depth. -/
private theorem deficit (a : α) (k : ℕ) (low : G.grundy (a,k) < k + G.depth a) :
    ∃ m : ℕ, 0 < m ∧ m ≤ G.grundy (a,k)-k+1 ∧ m ≤ G.depth a ∧
      k+1 ≤ m * (G.depth a-m) := by
  classical
  let f := fun i => G.grundy (a,i)
  have fs : StrictMono f := fun _ _ h => G.increase a h
  have ge := G.heap_le a k
  obtain ⟨b,legal,depth⟩ := G.deepest a (by omega)
  let g := fun j => G.grundy (b,j)
  have gs : StrictMono g := fun _ _ h => G.increase b h
  have gu (j) : g j ≤ j+G.depth b := by
    have h := (G.bounds (b,j)).2
    simpa [g,Nat.add_comm] using h
  let shared := (Finset.range (k+1)).filter fun i => ∃ j, f i = g j
  by_cases hs : shared.Nonempty
  · let i := shared.max' hs
    have hi := Finset.mem_filter.mp (shared.max'_mem hs)
    obtain ⟨j,equal⟩ := hi.2
    change f i = g j at equal
    have ik : i ≤ k := by have := Finset.mem_range.mp hi.1; omega
    have ij : i < j := by
      by_contra! ji
      exact G.excluded (a,i) ⟨(b,j),Or.inr ⟨legal,ji⟩,equal.symm⟩
    have monotone := G.offset_mono a ik
    change f i + k ≤ f k + i at monotone
    have lo : g j < j + G.depth b := by change f k < k + G.depth a at low; omega
    obtain ⟨m,mp,moff,md,rectangle⟩ := deficit b j lo
    change m ≤ g j-j+1 at moff
    have missing (x) (hx : x ∈ (Finset.Ioc i k).image f) (u) : g u ≠ x := by
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨it,tk⟩ := Finset.mem_Ioc.mp ht
      intro he
      have mem : t ∈ shared := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),u,he.symm⟩
      exact (Nat.not_le_of_lt it) (shared.le_max' t mem)
    have above (x) (hx : x ∈ (Finset.Ioc i k).image f) : g j+1 ≤ x := by
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      exact equal ▸ fs (Finset.mem_Ioc.mp ht).1
    have gap := gap_count gs gu (v := g j+1) (l := j+1)
        (gs (Nat.lt_succ_self j)) _ above missing
    rw [Finset.card_image_of_injective _ fs.injective,Nat.card_Ioc] at gap
    refine ⟨m+1,by omega,?_,by omega,?_⟩
    · change m+1 ≤ f k-k+1
      have := G.heap_le b j
      change j ≤ g j at this
      omega
    · have eq : G.depth a - (m+1) = G.depth b-m := by omega
      rw [eq, Nat.add_mul, Nat.one_mul]
      have := G.heap_le b j
      change j ≤ g j at this
      omega
  · have missing (x) (hx : x ∈ (Finset.range (k+1)).image f) (u) : g u ≠ x := by
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      exact fun he => hs ⟨t,Finset.mem_filter.mpr ⟨ht,u,he.symm⟩⟩
    have gap := gap_count gs gu (v := 0) (l := 0) (Nat.zero_le _) _
      (fun _ _ => Nat.zero_le _) missing
    rw [Finset.card_image_of_injective _ fs.injective,Finset.card_range] at gap
    exact ⟨1,by decide,by omega,by omega,by rw [Nat.one_mul]; omega⟩
termination_by G.depth a
decreasing_by exact G.shorter ‹_›

/-- Every finite-depth impartial game saturates by a quarter of the squared depth. -/
theorem saturation (a : α) (k : ℕ) (hk : G.depth a ^ 2 / 4 ≤ k) :
    G.grundy (a,k) = k + G.depth a := by
  have cap := (G.bounds (a,k)).2
  change G.grundy (a,k) ≤ G.depth a + k at cap
  by_contra wrong
  obtain ⟨m,_,_,md,rect⟩ := G.deficit a k (by omega)
  have product : 4 * (m * (G.depth a-m)) ≤ G.depth a ^ 2 := by
    let s := G.depth a-m
    have eq : G.depth a = m+s := by dsimp [s]; omega
    change 4 * (m*s) ≤ G.depth a ^ 2
    rw [eq]
    have square := sq_nonneg ((m:ℤ)-(s:ℤ))
    exact_mod_cast (show 4*((m:ℤ)*s) ≤ ((m:ℤ)+s)^2 by nlinarith)
  omega

theorem resolution (a : α) : G.Stabilizes a :=
  ⟨G.depth a ^ 2 / 4, fun k h => G.saturation a k h.le⟩

/-- info: 'SelectiveCompound.Game.saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms saturation
/-- info: 'SelectiveCompound.Game.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end SelectiveCompound.Game
