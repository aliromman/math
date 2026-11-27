module

public import conjectures.PalssonYuTriangles.Plane
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

@[expose] public section
open Complex Finset
open scoped ComplexConjugate
namespace PalssonYu
noncomputable section

/-- The shorter number of edges between two vertices of a seven-cycle. -/
def gap (i j : Fin 7) : Fin 4 := ⟨min (i-j).val (j-i).val,by decide +revert⟩

private def codes : Finset (Multiset (Fin 4)) :=
  univ.biUnion fun a : Fin 7 => univ.biUnion fun b : Fin 7 => univ.biUnion fun c : Fin 7 =>
    if a≠b ∧ b≠c ∧ c≠a then {{gap a b,gap b c,gap c a}} else ∅

private theorem four_codes : codes.card=4 := by decide

theorem mem_types {S : Finset ℂ} {m : Multiset ℝ} : m ∈ triangleTypes S ↔
    ∃ a∈S, ∃ b∈S, ∃ c∈S, a≠b ∧ b≠c ∧ c≠a ∧ m=triangle a b c := by
  classical
  simp only [triangleTypes,mem_biUnion]
  apply exists_congr; intro a
  apply and_congr_right; intro _
  apply exists_congr; intro b
  apply and_congr_right; intro _
  apply exists_congr; intro c
  apply and_congr_right; intro _
  by_cases h : a≠b ∧ b≠c ∧ c≠a
  · rw [ite_eq_left h]; simp [h.1,h.2.1,h.2.2]
  · rw [ite_eq_right h]; simp only [notMem_empty,false_iff]
    rintro ⟨ab,bc,ca,_⟩
    exact h ⟨ab,bc,ca⟩

private theorem mem_codes {m : Multiset (Fin 4)} : m ∈ codes ↔
    ∃ a b c : Fin 7, a≠b ∧ b≠c ∧ c≠a ∧ m={gap a b,gap b c,gap c a} := by
  simp only [codes, mem_biUnion,mem_univ,true_and]
  apply exists_congr; intro a
  apply exists_congr; intro b
  apply exists_congr; intro c
  by_cases h : a≠b ∧ b≠c ∧ c≠a
  · rw [ite_eq_left h]; simp [h.1,h.2.1,h.2.2]
  · rw [ite_eq_right h]; simp only [notMem_empty,false_iff]
    rintro ⟨ab,bc,ca,_⟩
    exact h ⟨ab,bc,ca⟩

private theorem chord_inj {r : ℂ} (hr : IsPrimitiveRoot r 7) :
    Function.Injective (fun k : Fin 4 => D (r^k.val) 1) := by
  have norm (n : ℕ) : normSq (r^n)=1 := by simp [normSq_eq_norm_sq,hr.norm'_eq_one (by decide)]
  intro i j e
  obtain ⟨re,im|im⟩ := same_coords ((norm i.val).trans (norm j.val).symm) e
  · exact Fin.ext (hr.pow_inj (by omega) (by omega) (ext re im))
  · have eq : r^i.val = conj (r^j.val) := ext re im
    have prod : r^(i.val+j.val)=1 := by rw [pow_add,eq,mul_comm,mul_conj,norm]; norm_num
    have s := hr.dvd_of_pow_eq_one _ prod
    have low : i.val+j.val<7 := by omega
    have z := Nat.eq_zero_of_dvd_of_lt s low
    exact Fin.ext (by omega)

private theorem chord_rule (c z r : ℂ) (hr : IsPrimitiveRoot r 7) (i j : Fin 7) :
    D (c+z*r^i.val) (c+z*r^j.val) = normSq z * D (r^(gap i j).val) 1 := by
  have add (a b : Fin 7) : r^(a+b).val=r^a.val*r^b.val := by
    change r^((a.val+b.val)%7)=_
    rw [← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hr.pow_eq_one
  have norm (n : ℕ) : normSq (r^n)=1 := by simp [normSq_eq_norm_sq,hr.norm'_eq_one (by decide)]
  have step (a b : Fin 7) : D (c+z*r^(a+b).val) (c+z*r^a.val) = normSq z*D (r^b.val) 1 := by
    rw [add]
    unfold D
    rw [show c+z*(r^a.val*r^b.val)-(c+z*r^a.val)=z*r^a.val*(r^b.val-1) by ring]
    simp [norm]
  let d : Fin 7 := ⟨(gap i j).val,by have := (gap i j).isLt; omega⟩
  have dir : i=j+d ∨ j=i+d := by exact (by decide : ∀ i j : Fin 7, i=j+
      ⟨(gap i j).val,by have := (gap i j).isLt; omega⟩ ∨ j=i+⟨(gap i j).val,by have := (gap i j).isLt; omega⟩) i j
  rcases dir with e|e
  · simpa only [←e] using step j d
  · rw [D_comm]; simpa only [←e] using step i d

theorem regular_size_types {S : Finset ℂ} (h : RegularHeptagon S) :
    S.card=7 ∧ (triangleTypes S).card=4 := by
  classical
  obtain ⟨c,z,r,zn,hr,rfl⟩ := h
  let p (i : Fin 7) := c+z*r^i.val
  let f (k : Fin 4) := normSq z * D (r^k.val) 1
  have inj : Function.Injective p := fun i j e =>
    Fin.ext (hr.pow_inj i.isLt j.isLt (mul_left_cancel₀ zn (add_left_cancel e)))
  have fi : Function.Injective f := fun i j e =>
    chord_inj hr (mul_left_cancel₀ (fun h => zn (normSq_eq_zero.mp h)) e)
  have tri (i j k : Fin 7) : triangle (p i) (p j) (p k) =
      Multiset.map f {gap i j,gap j k,gap k i} := by
    simp [triangle,p,chord_rule _ _ _ hr,f]
  change (univ.image p).card=7 ∧ (triangleTypes (univ.image p)).card=4
  have eq : triangleTypes (univ.image p) = codes.image (Multiset.map f) := by
    ext m
    rw [mem_types,mem_image]
    constructor
    · rintro ⟨_,ha,_,hb,_,hc,ab,bc,ca,rfl⟩
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := mem_image.mp hb
      obtain ⟨k,_,rfl⟩ := mem_image.mp hc
      exact ⟨_,mem_codes.mpr ⟨i,j,k,fun e => ab (congrArg p e),
        fun e => bc (congrArg p e),fun e => ca (congrArg p e),rfl⟩,(tri i j k).symm⟩
    · rintro ⟨m,hm,rfl⟩
      obtain ⟨i,j,k,ij,jk,ki,rfl⟩ := mem_codes.mp hm
      exact ⟨_,mem_image_of_mem p (mem_univ i),_,mem_image_of_mem p (mem_univ j),_,
        mem_image_of_mem p (mem_univ k),inj.ne ij,inj.ne jk,inj.ne ki,(tri i j k).symm⟩
  rw [eq,card_image_of_injective _ inj,card_image_of_injective _ (Multiset.map_injective fi),four_codes]
  simp

/-- Each nonzero distance from a vertex of a regular heptagon occurs twice. -/
theorem twice_at_vertex {S : Finset ℂ} (h : RegularHeptagon S) {x y : ℂ} (hx : x∈S)
    (hy : y∈S) (ne : x≠y) : (S.filter fun u => D x u = D x y).card = 2 := by
  classical
  obtain ⟨c,z,r,zn,hr,rfl⟩ := h
  let p (i : Fin 7) := c+z*r^i.val
  change x ∈ univ.image p at hx
  change y ∈ univ.image p at hy
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := mem_image.mp hy
  have inj : Function.Injective p := fun i j e =>
    Fin.ext (hr.pow_inj i.isLt j.isLt (mul_left_cancel₀ zn (add_left_cancel e)))
  have counts : ∀ i j : Fin 7, i≠j → (univ.filter (fun k => gap i k=gap i j)).card=2 := by decide
  have equiv (k : Fin 7) : D (p i) (p k)=D (p i) (p j) ↔ gap i k=gap i j := by
    simp only [p,chord_rule c z r hr]
    exact ⟨fun e => chord_inj hr (mul_left_cancel₀ (fun h => zn (normSq_eq_zero.mp h)) e),
      fun e => by rw [e]⟩
  change ((univ.image p).filter (fun u => D (p i) u=D (p i) (p j))).card=2
  rw [Finset.filter_image,card_image_of_injective _ inj]
  simpa only [equiv] using counts i j (fun e => ne (congrArg p e))

end
end PalssonYu
