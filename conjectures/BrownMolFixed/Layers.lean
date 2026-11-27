module

public import conjectures.BrownMolFixed.Statement
public import Mathlib.Data.Fintype.Sigma

@[expose] public section
namespace BrownMolFixed
variable {n : ℕ}

theorem cut_of_disconnect {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (connected : Connected G (fun _ ↦ true)) (other : u≠v)
    (disconnect : ¬Connected G (fun x ↦ decide (x≠v))) : Cut G v := by
  by_contra no
  apply disconnect
  refine ⟨⟨u,decide_eq_true other⟩,?_⟩
  intro color same x y hx hy
  by_contra different
  apply no
  exact ⟨x,of_decide_eq_true hx,y,of_decide_eq_true hy,
    fun c h ↦ connected.2 c h x y rfl rfl,fun h ↦ different (h color same)⟩

abbrev Vertex (w : Fin n→ℕ) := Σ i,Fin (w i)

/-- Each layer is a clique; consecutive layers are completely joined. -/
def chain (w : Fin n→ℕ) : SimpleGraph (Vertex w) where
  Adj x y := x≠y ∧ x.1.val≤y.1.val+1 ∧ y.1.val≤x.1.val+1
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

def occupied {w : Fin n→ℕ} (f : Vertex w→Bool) (i : Fin n) : Bool :=
  decide (∃ j,f ⟨i,j⟩=true)

def IntervalSupport (b : Fin n→Bool) : Prop :=
  (∃i,b i=true) ∧ ∀ i j k, b i=true → b j=true → i≤k → k≤j → b k=true

instance (b : Fin n→Bool) : Decidable (IntervalSupport b) := by unfold IntervalSupport;infer_instance

theorem connected_iff {w : Fin n→ℕ} (f : Vertex w→Bool) :
    Connected (chain w) f ↔ IntervalSupport (occupied f) := by
  have occ (i : Fin n) : occupied f i=true ↔ ∃ j,f ⟨i,j⟩=true := by simp [occupied]
  constructor
  · rintro ⟨⟨⟨i,u⟩,hu⟩,connected⟩
    refine ⟨⟨i,(occ i).mpr ⟨u,hu⟩⟩,?_⟩
    intro a b k ha hb ak kb
    by_contra missing
    have al : a.val<k.val := lt_of_le_of_ne ak (fun h ↦ missing (Fin.ext h ▸ ha))
    have bl : k.val<b.val := lt_of_le_of_ne kb (fun h ↦ missing (Fin.ext h ▸ hb))
    let color (v : Vertex w) := decide (v.1.val<k.val)
    have adjacent (x y : Vertex w) (hx : f x=true) (hy : f y=true) (edge : (chain w).Adj x y) :
        color x=color y := by
      have xk : x.1.val≠k.val := fun h ↦ missing (Fin.ext h ▸ (occ x.1).mpr ⟨x.2,hx⟩)
      have yk : y.1.val≠k.val := fun h ↦ missing (Fin.ext h ▸ (occ y.1).mpr ⟨y.2,hy⟩)
      obtain ⟨_,l,r⟩ := edge
      dsimp [color]
      by_cases h : x.1.val<k.val
      · simp [h,show y.1.val<k.val by omega]
      · simp [h,show ¬y.1.val<k.val by omega]
    obtain ⟨x,hx⟩ := (occ a).mp ha
    obtain ⟨y,hy⟩ := (occ b).mp hb
    have eq := connected color adjacent ⟨a,x⟩ ⟨b,y⟩ hx hy
    change decide (a.val<k.val)=decide (b.val<k.val) at eq
    rw [decide_eq_true al,decide_eq_false (by omega)] at eq
    contradiction
  · intro ⟨⟨i,hi⟩,interval⟩
    obtain ⟨u,hu⟩ := (occ i).mp hi
    refine ⟨⟨⟨i,u⟩,hu⟩,?_⟩
    intro color same
    have near (x y : Vertex w) (hx : f x=true) (hy : f y=true)
        (l : x.1.val≤y.1.val+1) (r : y.1.val≤x.1.val+1) : color x=color y := by
      by_cases e : x=y
      · rw [e]
      · exact same x y hx hy ⟨e,l,r⟩
    have through (x y : Vertex w) (hx : f x=true) (hy : f y=true) (xy : x.1≤y.1) : color x=color y := by
      have left := (occ x.1).mpr ⟨x.2,hx⟩
      have right := (occ y.1).mpr ⟨y.2,hy⟩
      have step (s : ℕ) (xs : x.1.val≤s) (sy : s≤y.1.val) :
          ∀ z : Vertex w,z.1.val=s → f z=true → color x=color z := by
        induction s, xs using Nat.le_induction with
        | base =>
          intro z hz live
          exact near x z hx live (by omega) (by omega)
        | succ s xs ih =>
          intro z hz live
          let j : Fin n := ⟨s,by have h := y.1.isLt;omega⟩
          have ok := interval x.1 y.1 j left right xs (show s≤y.1.val by omega)
          obtain ⟨v,hv⟩ := (occ j).mp ok
          exact (ih (by omega) ⟨j,v⟩ rfl hv).trans (near ⟨j,v⟩ z hv live (by change s≤_;omega) (by change _≤s+1;omega))
      exact step y.1.val xy le_rfl y rfl hy
    intro x y hx hy
    rcases le_total x.1 y.1 with xy|yx
    · exact through x y hx hy xy
    · exact (through y x hy hx yx).symm

end BrownMolFixed
