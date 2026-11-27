module

public import conjectures.CFPLogDensity.DenseStock
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace CFPLogDensity
open Finset
namespace ColorPairs
variable {r c n : ℕ} {χ : ℕ → Fin r} (F : ColorPairs c n χ)

def batchSize (c : ℕ) := 4*2^(c+2)

def work (s : ℕ) := 2*(batchSize c*F.stride)+2*batchSize c*s

private theorem free {U : Finset ℕ} {b h : ℕ} (room : 2*b+h≤F.indices.card) (cap : U.card≤b) :
    h≤(F.available U).card := by
  have := F.available_card U
  omega

private theorem seed (t : ℕ) (room : 2*(2*t)+1≤F.indices.card) :
    ∃ P : Span F.d F.stock, P.used.card≤2*t ∧ t≤P.length := by
  induction t with
  | zero => exact ⟨Span.empty _ _,by simp [Span.empty],by simp⟩
  | succ t ih =>
    obtain ⟨P,hp,hl⟩ := ih (by omega)
    obtain ⟨a,ha⟩ := card_pos.mp (F.free (b:=2*t) (h:=1) (by omega) hp)
    obtain ⟨inI,lo,hi⟩ := F.available_spec ha
    have shift : F.upper a=F.lower a+F.d*1 := by simp [upper]
    let T := P.addPair _ _ _ (F.lower_mem inI) (F.upper_mem inI) lo hi shift (by omega)
    have cost := P.addPair_card _ _ _ (F.lower_mem inI) (F.upper_mem inI) lo hi shift (by omega)
    exact ⟨T,by dsimp [T]; omega,by change t+1 ≤ P.length+1; omega⟩

private theorem batch (s j : ℕ) (hn : n=c+2+s) (hj : j≤s) (P : Span F.d F.stock)
    (wide : F.stride*2^(c+2+j)≤P.length) (t : ℕ)
    (room : 2*(P.used.card+2*t)+2^(1+s)≤F.indices.card) :
    ∃ R : Span F.d F.stock, R.used.card≤P.used.card+2*t ∧
      P.length+t*(F.stride*2^j)≤R.length := by
  induction t with
  | zero => exact ⟨P,by simp,by simp⟩
  | succ t ih =>
    obtain ⟨R,cost,long⟩ := ih (by omega)
    let I := F.available R.used
    have size : 2^(1+s)≤I.card := F.free (b:=P.used.card+2*t) (by omega) cost
    have e : c+1+1+j+(s-j)=n := by omega
    obtain ⟨a,ha,b,hb,h₁,h₂⟩ := dyadic_pair (I:=I) (c+1) j (s-j)
      (fun z hz => e ▸ F.indexed z (F.available_spec hz).1)
      (by simpa only [show 1+j+(s-j)=1+s by omega] using size)
    obtain ⟨ai,af,_⟩ := F.available_spec ha
    obtain ⟨bi,bf,_⟩ := F.available_spec hb
    let gap := F.stride*(b-a)
    have positive : 0<2^j := by positivity
    change b≤a+2^(c+2+j) at h₂
    have b₀ : a≤b := (Nat.le_add_right _ _).trans h₁
    have sh : F.lower b=F.lower a+F.d*gap := by
      change F.base+F.d*F.stride*b=F.base+F.d*F.stride*a+F.d*(F.stride*(b-a))
      calc
        _ = F.base+F.d*F.stride*(a+(b-a)) := by rw [Nat.add_sub_of_le b₀]
        _ = _ := by ring
    have bound : gap≤R.length+1 := by
      have h := Nat.mul_le_mul_left F.stride (show b-a≤2^(c+2+j) by omega)
      dsimp [gap]
      omega
    have gain := Nat.mul_le_mul_left F.stride (show 2^j≤b-a by omega)
    let T := R.addPair _ _ _ (F.lower_mem ai) (F.lower_mem bi) af bf sh bound
    have cnt := R.addPair_card _ _ _ (F.lower_mem ai) (F.lower_mem bi) af bf sh bound
    refine ⟨T,?_,?_⟩
    · dsimp [T]
      omega
    · change _≤R.length+gap
      rw [Nat.succ_mul]
      dsimp [gap]
      omega

/-- Use a fixed number of pairs at each dyadic scale. The number of
used terms grows linearly in the number of scales. -/
theorem long_span (s : ℕ) (hn : n=c+2+s) (room : 2*F.work s+2^(1+s)≤F.indices.card) :
    ∃ P : Span F.d F.stock, P.used.card≤F.work s ∧ 4*2^n≤P.length := by
  let K := batchSize c
  have positive : 0<2^(1+s) := by positivity
  obtain ⟨P,cs,sz⟩ := F.seed (K*F.stride) (by dsimp [work,K] at *; omega)
  have stage (j : ℕ) (hj : j≤s) : ∃ R : Span F.d F.stock,
      R.used.card≤2*(K*F.stride)+2*K*j ∧ K*F.stride*2^j≤R.length := by
    induction j with
    | zero => exact ⟨P,by simpa using cs,by simpa using sz⟩
    | succ j ih =>
      obtain ⟨R,rs,rh⟩ := ih (by omega)
      have eq : K*F.stride*2^j = 4*(F.stride*2^(c+2+j)) := by dsimp [K,batchSize]; rw [pow_add]; ring
      have wide : F.stride*2^(c+2+j)≤R.length := by omega
      obtain ⟨T,ts,th⟩ := F.batch s j hn (by omega) R wide K (by
        dsimp [work] at room
        have mono := Nat.mul_le_mul_left (2*K) hj
        change 2*K*(j+1) ≤ 2*K*s at mono
        rw [Nat.mul_succ] at mono
        change 2*(K*F.stride)+2*K*j≥R.used.card at rs
        change 2*(2*(K*F.stride)+2*K*s)+_≤_ at room
        omega)
      refine ⟨T,?_,?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [pow_succ,←Nat.mul_assoc]
        have e : K*(F.stride*2^j)=K*F.stride*2^j := (Nat.mul_assoc _ _ _).symm
        rw [e] at th
        omega
  obtain ⟨R,a,b⟩ := stage s (le_refl _)
  refine ⟨R,a,?_⟩
  have power : 2^n=2^(c+2)*2^s := by rw [hn,pow_add]
  have e : K*F.stride*2^s=4*2^n*F.stride := by dsimp [K,batchSize]; rw [power]; ring
  rw [e] at b
  exact (Nat.le_mul_of_pos_right _ F.stride_pos).trans b

end ColorPairs
end CFPLogDensity
