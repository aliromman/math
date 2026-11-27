module
public import conjectures.SidonSetSystems.Translation

public section
namespace SidonSetSystems
open Finset
open scoped Pointwise Classical

theorem shapes_card (k n : ℕ) (hk : 0<k) (hn : 0<n) :
    (shapes k n).card = (n-1).choose (k-1) := by
  have h := card_filter_powersetCard_subset ({0}:Finset ℕ) (range n) k
    (by simpa using hn) (by simp; omega)
  simpa [shapes] using h

theorem le_extremal {k n : ℕ} {F : Finset (Finset ℕ)} (valid : F ⊆ (Icc 1 n).powersetCard k)
    (sidon : IsSidon F) : F.card≤extremal k n := by
  exact le_sup (f:=Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr valid,sidon⟩)

/-- Color labels distinguish all the summands of each nontrivial collision. -/
theorem translate_family {k n D : ℕ} {G : Finset (Finset ℕ)}
    (sub : G⊆shapes k n) (degree : ∀ a∈G,(neighbors G a).card≤D) :
    G.card≤extremal k (n+3^D) := by
  obtain ⟨f,bd,proper⟩ := finite_coloring G D degree
  let g := fun A : Finset ℕ => shift (3^(f A)) A
  have info {A : Finset ℕ} (h : A∈G) : A⊆range n ∧ A.card=k ∧ 0∈A := by
    obtain ⟨s,z⟩ := mem_filter.mp (sub h)
    exact ⟨(mem_powersetCard.mp s).1,(mem_powersetCard.mp s).2,z⟩
  have count : (G.image g).card=G.card := card_image_of_injOn (fun _ ha _ hb he =>
    (shift_rigid (info ha).2.2 (info hb).2.2 he).2)
  rw [←count]
  apply le_extremal
  · intro A hA
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    apply mem_powersetCard.mpr
    refine ⟨?_,(card_shift _ _).trans (info ha).2.1⟩
    intro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    have low : 0<3^(f a) := by positivity
    have high := Nat.pow_le_pow_right (by decide : 0<3) (bd a ha)
    have zlt := mem_range.mp ((info ha).1 hz)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro A hA B hB C hC E hE eq
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hB
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hC
    obtain ⟨e,he,rfl⟩ := mem_image.mp hE
    change shift _ a + shift _ b = shift _ c + shift _ e at eq
    rw [shift_add,shift_add] at eq
    have zero {u v : Finset ℕ} (hu : u∈G) (hv : v∈G) : 0∈u+v :=
      mem_add.mpr ⟨0,(info hu).2.2,0,(info hv).2.2,rfl⟩
    obtain ⟨labels,same⟩ := shift_rigid (zero ha hb) (zero hc he) eq
    suffices original : (a=c ∧ b=e) ∨ (a=e ∧ b=c) by
      rcases original with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
    by_contra notpair
    have bad : Bad a b c e := ⟨same,notpair⟩
    let clique : Finset (Finset ℕ) := {a,b,c,e}
    have inG : clique⊆G := by
      intro x hx
      simp only [clique,mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl <;> assumption
    have inj : Set.InjOn f clique := by
      intro x hx y hy eq
      by_contra ne
      have adj : y∈neighbors G x := mem_filter.mpr ⟨inG hy,ne,a,ha,b,hb,c,hc,e,he,bad,hx,hy⟩
      exact proper x (inG hx) y adj eq
    rcases tags_sidon _ _ _ _ labels with ⟨l,r⟩|⟨l,r⟩
    · exact notpair (Or.inl ⟨inj (by simp [clique]) (by simp [clique]) l,
        inj (by simp [clique]) (by simp [clique]) r⟩)
    · exact notpair (Or.inr ⟨inj (by simp [clique]) (by simp [clique]) l,
        inj (by simp [clique]) (by simp [clique]) r⟩)

theorem lower_estimate {k : ℕ} (hk : 3≤k) (sp : SparseShapes k) :
    ∃ D : ℕ, ∀ n : ℕ, (n.choose (k-1))≤extremal k (n+(1+3^D)) + D*(n+2)^(k-2) := by
  obtain ⟨D,good⟩ := sp
  refine ⟨D,fun n => ?_⟩
  obtain ⟨G,sub,size,deg⟩ := good (n+1)
  rw [shapes_card _ _ (by omega) (by omega),Nat.add_sub_cancel] at size
  have lo := translate_family sub deg
  rw [Nat.add_assoc] at lo
  exact size.trans (Nat.add_le_add_right lo _)

end SidonSetSystems
