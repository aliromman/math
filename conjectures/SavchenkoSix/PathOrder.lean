module

public import conjectures.SavchenkoSix.Transport
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Chain

@[expose] public section
namespace SavchenkoSix
open Finset Matrix

private def insertAlong {α : Type*} (R : α → α → Prop) [DecidableRel R] (v : α) :
    List α → List α
  | [] => [v]
  | a::l => if R v a then v::a::l else a::insertAlong R v l

private theorem insert_perm {α : Type*} (R : α → α → Prop) [DecidableRel R] (v : α)
    (l : List α) : (insertAlong R v l).Perm (v::l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    rw [insertAlong]
    split
    · exact List.Perm.refl _
    · exact (ih.cons a).trans (List.Perm.swap v a l)

private theorem insert_chain {α : Type*} {R : α → α → Prop} [DecidableRel R]
    (total : ∀ a b, R a b ∨ R b a) (v : α) (l : List α) (hc : l.IsChain R) :
    (insertAlong R v l).IsChain R := by
  induction l with
  | nil => simp [insertAlong]
  | cons a l ih =>
    by_cases ha : R v a
    · simp only [insertAlong, ha, ↓reduceIte]
      exact List.isChain_cons_cons.mpr ⟨ha,hc⟩
    · simp only [insertAlong, ha, ↓reduceIte]
      have av := (total v a).resolve_left ha
      refine List.isChain_cons.mpr ⟨?_,ih (List.isChain_cons.mp hc).2⟩
      cases l with
      | nil => simpa [insertAlong] using av
      | cons b l =>
        by_cases hb : R v b
        · simpa [insertAlong,hb] using av
        · simpa [insertAlong,hb] using (List.isChain_cons_cons.mp hc).1

private theorem path_list {α : Type*} {R : α → α → Prop} [DecidableRel R]
    (total : ∀ a b, R a b ∨ R b a) (l : List α) : ∃ p : List α, p.Perm l ∧ p.IsChain R := by
  induction l with
  | nil => exact ⟨[],List.Perm.refl _,by simp⟩
  | cons a l ih =>
    obtain ⟨p,hp,hc⟩ := ih
    exact ⟨insertAlong R a p,(insert_perm R a p).trans (hp.cons a),insert_chain total a p hc⟩

private theorem bits_unit (b : Fin 15 → Bool) (i j : Fin 7) (ne : i≠j) :
    bitsMatrix b i j=1 ∨ bitsMatrix b i j= -1 := by
  have upper {x y : Fin 7} (h : x<y) : bitsMatrix b x y=1 ∨ bitsMatrix b x y= -1 := by
    rw [bitsMatrix_lt b h]
    split_ifs <;> simp
  rcases lt_or_gt_of_ne ne with h|h
  · exact upper h
  · rw [bitsMatrix_flip b j i]
    rcases upper h with u|u <;> simp [u]

/-- Reorder the six nonroot vertices along a directed Hamiltonian path. -/
theorem seven_path (bits : Fin 15 → Bool) : ∃ b : Fin 15 → Bool,
    b 0=false ∧ b 2=false ∧ b 5=false ∧ b 9=false ∧ b 14=false ∧
    ∀ k, excessOn (bitsMatrix bits) univ k = excessOn (bitsMatrix b) univ k := by
  classical
  let R (i j : Fin 6) := i=j ∨ bitsMatrix bits i.succ j.succ=1
  have total (i j : Fin 6) : R i j ∨ R j i := by
    by_cases h : i=j
    · exact Or.inl (Or.inl h)
    · rcases bits_unit bits i.succ j.succ (fun e ↦ h (Fin.succ_injective _ e)) with u|u
      · exact Or.inl (Or.inr u)
      · exact Or.inr (Or.inr (by rw [bitsMatrix_flip bits i.succ j.succ,u]; decide))
  obtain ⟨l,hp,hc⟩ := path_list total (List.finRange 6)
  have len : l.length=6 := by simpa using hp.length_eq
  have nd := hp.nodup_iff.mpr (List.nodup_finRange 6)
  have all (i : Fin 6) : i∈l := hp.mem_iff.mpr (List.mem_finRange i)
  let p : Equiv.Perm (Fin 6) := (finCongr len.symm).trans (List.Nodup.getEquivOfForallMemList l nd all)
  have path (j : Fin 5) : bitsMatrix bits (p j.castSucc).succ (p j.succ).succ=1 := by
    have hj := j.isLt
    have chain : R (p j.castSucc) (p j.succ) :=
      List.isChain_iff_getElem.mp hc j.val (by omega)
    exact chain.resolve_left (fun e ↦ (show j.castSucc≠j.succ by intro h; have h' := congrArg Fin.val h; simp at h') (p.injective e))
  let e : Equiv.Perm (Fin 7) := ((finSuccEquiv 6).trans p.optionCongr).trans (finSuccEquiv 6).symm
  have e0 : e 0=0 := by simp [e]
  have es (i : Fin 6) : e i.succ=(p i).succ := by simp [e]
  let M := (bitsMatrix bits).submatrix e e
  have root (j : Fin 7) (h : 0<j) : M 0 j=1 := by
    change bitsMatrix bits (e 0) (e j)=1
    rw [e0]
    apply bitsMatrix_first
    exact Fin.pos_iff_ne_zero.mpr (fun h' ↦ h.ne' (e.injective (h'.trans e0.symm)))
  obtain ⟨b,hb⟩ := recover_bits M (fun i j ↦ bitsMatrix_flip bits (e i) (e j))
    (fun i j h ↦ bits_unit bits (e i) (e j) (e.injective.ne h)) root
  have consecutive (j : Fin 5) : b (edgeIndex j.castSucc.succ j.succ.succ)=false := by
    have pe := path j
    have he : bitsMatrix b j.castSucc.succ j.succ.succ=1 := by
      rw [hb]; change bitsMatrix bits (e j.castSucc.succ) (e j.succ.succ)=1
      simpa [es] using pe
    have lt : j.castSucc.succ<j.succ.succ := by apply Fin.succ_lt_succ_iff.mpr; exact j.castSucc_lt_succ
    rw [bitsMatrix_upper b (Fin.succ_pos _) lt] at he
    split at he <;> simp_all
  refine ⟨b,consecutive 0,consecutive 1,consecutive 2,consecutive 3,consecutive 4,?_⟩
  intro k
  have inv := excessOn_map (bitsMatrix bits) e.toEmbedding univ k
  rw [map_univ_equiv] at inv
  rw [hb]
  exact inv

end SavchenkoSix
