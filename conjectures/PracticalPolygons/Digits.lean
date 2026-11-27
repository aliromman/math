module

public import conjectures.PracticalPolygons.Quadratic

@[expose] public section
namespace PracticalPolygons

private def seeds : ℕ → List (ℕ×ℕ)
  | 4 => [(1,7),(1,5),(4,6),(2,7),(2,5),(1,2),(5,9),(1,9),(3,7),(3,5),(1,3),(5,6),(1,6),(2,3),(5,8),(1,8),(4,5),(1,4),(2,8),(5,12),(1,12),(5,11),(1,11),(2,12),(5,7)]
  | 5 => [(1,5),(0,3),(0,9),(3,9),(2,22),(0,1),(1,3),(0,22),(3,22),(2,7),(0,6),(3,6),(0,7),(3,7),(2,4),(0,10),(3,10),(0,4),(3,4),(4,9),(0,5),(3,5),(0,19),(2,3),(2,9)]
  | 6 => [(3,15),(0,1),(2,16),(0,4),(1,4),(0,18),(0,2),(1,2),(4,18),(2,4),(0,15),(0,17),(1,17),(4,15),(4,17),(0,3),(0,6),(1,6),(3,4),(4,6),(0,5),(0,16),(1,16),(4,5),(4,16)]
  | 7 => [(1,14),(0,13),(2,14),(1,23),(0,12),(1,4),(0,3),(2,4),(1,13),(0,2),(1,19),(0,18),(2,19),(1,3),(0,17),(1,9),(0,8),(2,9),(1,18),(0,7),(1,24),(0,23),(2,24),(1,8),(0,22)]
  | 8 => [(4,14),(0,1),(3,13),(2,15),(2,3),(0,10),(0,13),(1,13),(0,2),(1,2),(0,14),(0,16),(1,16),(2,10),(2,13),(0,4),(0,11),(1,11),(2,14),(2,16),(0,15),(0,3),(1,3),(2,4),(2,11)]
  | 10 => [(2,12),(0,1),(0,3),(1,3),(8,9),(0,15),(1,15),(0,24),(1,8),(3,8),(0,2),(1,2),(0,13),(1,13),(3,13),(0,12),(1,12),(0,14),(1,14),(3,14),(0,10),(1,10),(0,23),(1,9),(3,9)]
  | _ => []

private theorem checked_seeds {s : ℕ} (hs : Orders s) : ∀ r : Fin 25,
    let z := (seeds s)[r.val]?.getD (0,0)
    Q s z.1 + Q s z.2 ≡ (r.val:ℤ) [ZMOD 25] ∧
    ∀ t : Fin 25, ∃ h l : Fin 10,
      D s z.1 * h.val + D s z.2 * l.val ≡ (t.val:ℤ) [ZMOD 25] ∧
      lead s*((h.val+1)^2+(l.val+1)^2)≤520 := by
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- Every residue has a solution whose two derivatives cover all 25 high digits at low cost. -/
def Cheap (s : ℕ) (x y : ℤ) : Prop := ∀ t : ℤ, ∃ h l : ℕ,
  D s x*h+D s y*l ≡ t [ZMOD 25] ∧ lead s*((h+1)^2+(l+1)^2)≤520

theorem seed {s : ℕ} (hs : Orders s) (n : ℕ) :
    ∃ x y : ℕ, Q s x+Q s y ≡ (n:ℤ) [ZMOD 25] ∧ Cheap s x y := by
  let r : Fin 25 := ⟨n%25,Nat.mod_lt _ (by decide)⟩
  obtain ⟨root,high⟩ := checked_seeds hs r
  refine ⟨_,_,root.trans (Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)),?_⟩
  intro t
  let j : Fin 25 := ⟨(t%25).toNat,by have := Int.emod_lt_of_pos t (by decide : (0:ℤ)<25); omega⟩
  obtain ⟨h,l,w,sz⟩ := high j
  have eqn : (j.val:ℤ)=t%25 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  exact ⟨h.val,l.val,w.trans (eqn ▸ Int.mod_modEq t 25),sz⟩

private theorem small_roots {s d : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) :
    ∀ r : Fin (6*d), ∃ x y : Fin (6*d), Q s x.val+Q s y.val ≡ (r.val:ℤ) [ZMOD (6*d:ℕ)] := by
  rcases hd with rfl|rfl|rfl|rfl <;> rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem cofactor_root {s d : ℕ} (hs : Orders s) (hd : d=1 ∨ d=7 ∨ d=11 ∨ d=17) (n : ℕ) :
    ∃ x y : ℕ, Q s x+Q s y ≡ (n:ℤ) [ZMOD (6*d:ℕ)] := by
  have hp : 0<6*d := by rcases hd with rfl|rfl|rfl|rfl <;> decide
  obtain ⟨x,y,hw⟩ := small_roots hs hd ⟨n%(6*d),Nat.mod_lt _ hp⟩
  exact ⟨x.val,y.val,hw.trans (Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _))⟩

end PracticalPolygons
