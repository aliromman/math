module

public import conjectures.ExclusiveSumBound.Statement
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
namespace ExclusiveSumBound

/-- Interpret a fixed number of digits in base three, least significant digit first. -/
def encode : (s : ℕ) → (Fin s → ℕ) → ℕ
  | 0, _ => 0
  | s+1, f => f 0 + 3 * encode s (fun i => f i.succ)

theorem encode_add (s : ℕ) (f g : Fin s → ℕ) :
    encode s (fun i => f i+g i) = encode s f + encode s g := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [encode,ih]; omega

theorem encode_lt (s : ℕ) (f : Fin s → ℕ) (small : ∀ i, f i<3) : encode s f < 3^s := by
  induction s with
  | zero => simp [encode]
  | succ s ih =>
    have := ih (fun i => f i.succ) (fun i => small i.succ)
    have := small 0
    rw [encode,pow_succ]
    omega

theorem encode_inj (s : ℕ) (f g : Fin s → ℕ) (hf : ∀ i, f i < 3) (hg : ∀ i, g i < 3)
    (h : encode s f = encode s g) : f = g := by
  induction s with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ s ih =>
    have small := hf 0
    have small' := hg 0
    simp only [encode] at h
    have eq : f 0 = g 0 := by omega
    have tails := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hf i.succ) (fun i => hg i.succ)
      (by omega)
    exact funext (Fin.cases eq (fun i => congrFun tails i))

end ExclusiveSumBound
