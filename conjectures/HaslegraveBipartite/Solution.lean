module

public import conjectures.HaslegraveBipartite.Construction
import Mathlib.Tactic.Ring

public section
namespace HaslegraveBipartite

private def idx (N x : ℕ) : Side N := ⟨min x N, by omega⟩

private def left (N x : ℕ) : Vertex N := .inl (idx N x)

private theorem walk_pair {B d N} (f : Vertex N ↪ ℤ) {D : Finset ℤ}
    (labels : ∀ x y, (graph B d N).Adj x y → |f x-f y| ∈ D)
    {x s r : ℕ} (mem : s ∈ shifts B d) (cap : x+s≤N)
    (h : Box D r (f (left N x)-f (left N 0))) :
    Box D (r+2) (f (left N (x+s))-f (left N 0)) := by
  let y : Vertex N := .inr (idx N (x+s))
  have a : (graph B d N).Adj y (left N x) := by
    refine ⟨s,mem,?_⟩
    change min (x+s) N=min x N+s
    simp [Nat.min_eq_left cap,Nat.min_eq_left (by omega : x≤N)]
  have b : (graph B d N).Adj (left N (x+s)) y := by
    exact ⟨0,Finset.mem_insert_self ..,by simp⟩
  have h' := (h.step (labels _ _ a)).step (labels _ _ b)
  convert h' using 1
  ring

private theorem reachable {B d N} (base : 0 < B) (Nbig : B^d ≤ N)
    (f : Vertex N ↪ ℤ) {D : Finset ℤ}
    (labels : ∀ x y, (graph B d N).Adj x y → |f x-f y| ∈ D)
    (j : ℕ) (jd : j ≤ d) (x : ℕ) (cap : x < B^j) :
    Box D (2*j*B) (f (left N x)-f (left N 0)) := by
  induction j generalizing x with
  | zero =>
    have eq : x=0 := by simpa using cap
    simp [eq,box_zero]
  | succ j ih =>
    let stride := B^j
    let rem := x%stride
    let q := x/stride
    have pos : 0<stride := pow_pos base j
    have split : rem + q*stride = x := Nat.mod_add_div' x stride
    have qr : q < B := (Nat.div_lt_iff_lt_mul pos).mpr (by simpa [pow_succ,stride,Nat.mul_comm] using cap)
    have small : rem<stride := Nat.mod_lt _ pos
    have sstep : stride∈shifts B d :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩)
    have major : x ≤ N := cap.le.trans ((Nat.pow_le_pow_right base jd).trans Nbig)
    have stages (t : ℕ) (ht : t≤q) :
        Box D (2*j*B+2*t) (f (left N (rem+t*stride))-f (left N 0)) := by
      induction t with
      | zero => simpa using ih (by omega) rem small
      | succ t prev =>
        have within : rem+t*stride+stride ≤ N := by
          have hmul := Nat.mul_le_mul_right stride ht
          rw [Nat.succ_mul] at hmul
          omega
        have step := walk_pair f labels sstep within (prev (by omega))
        rw [show rem+(t+1)*stride=rem+t*stride+stride by ring,
          show 2*j*B+2*(t+1)=2*j*B+2*t+2 by ring]
        exact step
    have last := stages q le_rfl
    rw [split] at last
    apply last.mono
    rw [Nat.mul_succ,Nat.add_mul]
    omega

private theorem size_bound {B d} (base : 0<B) (k : ℕ)
    (adm : Admits (graph B d (B^d)) (fun a b => |a-b|) k) :
    B^d ≤ (4*d*B+1)^k := by
  obtain ⟨f,D,ck,labels⟩ := adm
  let val (x : Fin (B^d)) := f (left (B^d) x.val)-f (left (B^d) 0)
  have inject : Function.Injective val := by
    intro x y equal
    have same : left (B^d) x.val=left (B^d) y.val := f.injective (sub_left_inj.mp equal)
    have he := congrArg Fin.val (Sum.inl.inj same)
    apply Fin.ext
    simpa [idx,Nat.min_eq_left x.isLt.le,Nat.min_eq_left y.isLt.le] using he
  have inside (x : Fin (B^d)) : Box D (2*d*B) (val x) :=
    reachable base le_rfl f labels d le_rfl x.val x.isLt
  have count := box_count val inject inside
  rw [show 2*(2*d*B)+1 = 4*d*B+1 by ring] at count
  exact count.trans (Nat.pow_le_pow_right (by omega) ck)

private theorem difference_exact (d : ℕ) :
    let n := d+1
    let B := (4*n+1)^d+2
    diffIndex (graph B n (B^n)) = n := by
  dsimp only
  let B := (4*(d+1)+1)^d+2
  let G := graph B (d+1) (B^(d+1))
  change diffIndex G = d+1
  have bp : 0<B := by dsimp [B]; omega
  have adm := admits_diff B (d+1) (B^(d+1)) bp (by omega)
  have ub : diffIndex G ≤ d+1 := Nat.sInf_le (s := {k | Admits G (fun a b => |a-b|) k}) adm
  have opt : Admits G (fun a b => |a-b|) (diffIndex G) :=
    Nat.sInf_mem (s := {k | Admits G (fun a b => |a-b|) k}) ⟨_,adm⟩
  by_contra ne
  have card := size_bound bp _ opt
  have md : diffIndex G ≤ d := by omega
  have le : 4*(d+1)*B+1 ≤ (4*(d+1)+1)*B := by rw [Nat.add_mul,Nat.one_mul]; omega
  have bad := calc
    B^(d+1) ≤ (4*(d+1)*B+1)^(diffIndex G) := card
    _ ≤ (4*(d+1)*B+1)^d := Nat.pow_le_pow_right (by omega) md
    _ ≤ ((4*(d+1)+1)*B)^d := Nat.pow_le_pow_left le _
    _ = (4*(d+1)+1)^d * B^d := Nat.mul_pow ..
    _ < B * B^d := Nat.mul_lt_mul_of_pos_right (by dsimp [B]; omega) (pow_pos bp _)
    _ = B^(d+1) := (pow_succ' ..).symm
  exact lt_irrefl _ bad

private theorem sum_exact {B d : ℕ} (big : 2 ≤ B) :
    sumIndex (graph B d (B^d)) = d+1 := by
  let G := graph B d (B^d)
  have yes := admits_sum B d (B^d)
  have ub : sumIndex G ≤ d+1 := Nat.sInf_le (s := {k | Admits G (·+·) k}) yes
  have opt : Admits G (·+·) (sumIndex G) :=
    Nat.sInf_mem (s := {k | Admits G (·+·) k}) ⟨_,yes⟩
  obtain ⟨f,D,ck,labels⟩ := opt
  have capped (s) (mem : s ∈ shifts B d) : s ≤ B^d := by
    rcases Finset.mem_insert.mp mem with rfl | hi
    · omega
    · obtain ⟨i,hiRange,hpow⟩ := Finset.mem_image.mp hi
      rw [←hpow]
      exact Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hiRange).le
  let star (s : shifts B d) := f (left (B^d) 0) + f (.inr (idx (B^d) s.val))
  have inside (s) : star s ∈ D := by
    apply labels
    exact ⟨s.val,s.property,by simp [idx,Nat.min_eq_left (capped _ s.property)]⟩
  have inject : Function.Injective (fun s => (⟨star s,inside s⟩ : D)) := by
    intro i j same
    have he : star i = star j := congrArg Subtype.val same
    have h := f.injective (add_left_cancel he)
    have h' := congrArg Fin.val (Sum.inr.inj h)
    apply Subtype.ext
    simpa [idx,Nat.min_eq_left (capped _ i.property),Nat.min_eq_left (capped _ j.property)] using h'
  have count := Fintype.card_le_of_injective _ inject
  simp only [Fintype.card_coe] at count
  have nz : 0 ∉ (Finset.range d).image (B ^ ·) := by
    rintro e
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp e
    have := pow_pos (by omega : 0<B) i
    omega
  rw [shifts,Finset.card_insert_of_notMem nz,Finset.card_image_of_injective _ (Nat.pow_right_injective big),
    Finset.card_range] at count
  exact le_antisymm ub (count.trans ck)

/-- For every positive dimension this bipartite graph has consecutive difference and sum indices. -/
theorem exact_indices (d : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧ Nontrivial V ∧ G.Colorable 2 ∧ diffIndex G = d+1 ∧ sumIndex G = d+2 := by
  let B := (4*(d+1)+1)^d+2
  exact ⟨Vertex (B^(d+1)),inferInstance,graph B (d+1) (B^(d+1)),connected (by omega),inferInstance,bipartite ..,
    difference_exact d,sum_exact (by dsimp [B]; omega)⟩

theorem resolution : UnboundedGap := by
  intro K
  obtain ⟨V,inst,G,conn,nt,bip,diff,sum⟩ := exact_indices (2*K+2)
  refine ⟨V,inst,G,conn,nt,bip,?_⟩
  rw [diff,sum]
  omega

/-- info: 'HaslegraveBipartite.exact_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_indices

/-- info: 'HaslegraveBipartite.resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resolution

end HaslegraveBipartite
