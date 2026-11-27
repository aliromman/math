module

public import conjectures.TengelyPartition.Parameters
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring

@[expose] public section
namespace TengelyPartition

private theorem argument_large {a r t N : ℕ} (ha : 0<a) (ht : N<t) :
    N<a*(2*t-1)+r := by
  have h := Nat.le_mul_of_pos_left (2*t-1) ha
  omega

/-- Both partition arguments can be taken above any prescribed bound. -/
theorem simultaneous {a b : ℕ} (ha : 3≤a) (hb : 3≤b) (N : ℕ) :
    ∃ x y : ℕ, N<x ∧ N<y ∧ parts a x=parts b y := by
  by_cases h : IsSquare (a*b)
  · obtain ⟨g,u,v,gp,up,vp,au,bv⟩ := common_square (by omega) (by omega) h
    obtain ⟨r,hr,cr⟩ := square_residue gp (au ▸ ha)
    obtain ⟨s,hs,cs⟩ := square_residue gp (bv ▸ hb)
    let t := v*(N+1)
    let w := u*(N+1)
    have nt : N<t := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_mul_of_pos_left _ vp)
    have nw : N<w := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_mul_of_pos_left _ up)
    refine ⟨a*(2*t-1)+r,b*(2*w-1)+s,argument_large (by omega) nt,argument_large (by omega) nw,?_⟩
    rw [au,bv,block_value hr cr (by omega : 0<t),block_value hs cs (by omega : 0<w)]
    dsimp [t,w];ring
  · obtain ⟨r,hr,c,hc,cr⟩ := top_residue ha
    obtain ⟨s,hs,d,hd,cs⟩ := top_residue hb
    obtain ⟨t,u,nt,nu,eq⟩ := nonsquare_parameters (by omega) (by omega) hc hd h N
    exact ⟨a*(2*t-1)+r,b*(2*u-1)+s,argument_large (by omega) nt,argument_large (by omega) nu,
      (block_value hr cr (by omega)).trans (eq.trans (block_value hs cs (by omega)).symm)⟩

theorem resolution : Conjecture := by
  intro a b ha hab finite
  obtain ⟨N,bound⟩ := (finite.image Prod.fst).bddAbove
  obtain ⟨x,y,hx,hy,eq⟩ := simultaneous ha (by omega : 3≤b) N
  have inSet : (x,y)∈{v : ℕ×ℕ | 0<v.1 ∧ 0<v.2 ∧ parts a v.1=parts b v.2} := ⟨by omega,by omega,eq⟩
  exact hx.not_ge (bound (Set.mem_image_of_mem Prod.fst inSet))

/-- info: 'TengelyPartition.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end TengelyPartition
