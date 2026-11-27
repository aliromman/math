module

public import conjectures.PenneyBias.Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
namespace PenneyBias
open Filter
open scoped Topology

def longer : Word := [true,true,false,false]
def shorter : Word := [false,false,false]

private inductive Stage
  | start | zero | zeros | one | ones | tail | won | lost
  deriving DecidableEq

private def stage : Word → Stage
  | false::false::false::_ => .lost
  | false::false::true::true::_ => .won
  | false::false::_ => .zeros
  | false::true::true::_ => .tail
  | false::_ => .zero
  | true::true::_ => .ones
  | true::_ => .one
  | [] => .start

private def stop : Stage → Option Bool
  | .won => some true
  | .lost => some false
  | _ => none

private def down : Stage → Stage
  | .start | .one => .zero
  | .zero => .zeros
  | .zeros => .lost
  | .ones => .tail
  | .tail => .won
  | s => s

private def up : Stage → Stage
  | .one | .ones => .ones
  | .lost => .lost
  | .won => .won
  | _ => .one

private def rep : Stage → Word
  | .start => []
  | .zero => [false]
  | .zeros => [false,false]
  | .one => [true]
  | .ones => [true,true]
  | .tail => [false,true,true]
  | .won => [false,false,true,true]
  | .lost => [false,false,false]

private theorem rep_stage (s : Stage) : stage (rep s)=s := by cases s <;> rfl

private theorem transitions (h : Word) :
    terminal longer shorter h = stop (stage h) ∧
    (stop (stage h)=none → stage (false::h)=down (stage h) ∧ stage (true::h)=up (stage h)) := by
  rcases h with _ | ⟨_ | _,h⟩ <;> try exact ⟨rfl,fun _ ↦ ⟨rfl,rfl⟩⟩
  all_goals rcases h with _ | ⟨_ | _,h⟩ <;> try exact ⟨rfl,fun _ ↦ ⟨rfl,rfl⟩⟩
  all_goals rcases h with _ | ⟨_ | _,h⟩ <;> try exact ⟨rfl,fun _ ↦ ⟨rfl,rfl⟩⟩
  all_goals rcases h with _ | ⟨_ | _,h⟩ <;> first | exact ⟨rfl,fun _ ↦ ⟨rfl,rfl⟩⟩ | exact ⟨rfl,by intro impossible; cases impossible⟩

private def run (p : ℝ) : ℕ → Stage → ℝ
  | 0, s => if stop s=some true then 1 else 0
  | n+1, s => match stop s with
    | some true => 1
    | some false => 0
    | none => (1-p)*run p n (down s)+p*run p n (up s)

private theorem by_stage (p : ℝ) (n : ℕ) (h : Word) :
    byTime longer shorter p n h=run p n (stage h) := by
  induction n generalizing h with
  | zero => simp only [byTime,run,(transitions h).1]
  | succ n ih =>
    obtain ⟨same,next⟩ := transitions h
    cases e : stop (stage h) with
    | some b => cases b <;> simp only [byTime,run,same,e]
    | none =>
      obtain ⟨d,u⟩ := next e
      simp only [byTime,run,same,e,ih,d,u]

/-- The exact win probability for 1100 against 000, from its six unfinished states. -/
theorem witness_probability {p : ℝ} (hp : p∈Set.Ioo 0 1) :
    win longer shorter p = (p^2+p*(p*(1-p))+(p*(1-p))^2)/(1-p*(1-p)) := by
  let V (s : Stage) := ⨆ n,run p n s
  have limit (s : Stage) : Tendsto (fun n ↦ run p n s) atTop (𝓝 (V s)) := by
    simpa only [by_stage,rep_stage,V] using
      (horizon_tendsto longer shorter (show p∈Set.Icc 0 1 from ⟨hp.1.le,hp.2.le⟩) (rep s))
  have step (s : Stage) (hs : stop s=none) : V s=(1-p)*V (down s)+p*V (up s) := by
    apply tendsto_nhds_unique ((limit s).comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def,run,hs] using
      ((limit (down s)).const_mul (1-p)).add ((limit (up s)).const_mul p)
  have finish (s : Stage) (b : Bool) (hs : stop s=some b) : V s=if b then 1 else 0 := by
    apply tendsto_nhds_unique ((limit s).comp (tendsto_add_atTop_nat 1))
    cases b <;> simp only [Function.comp_def,run,hs] <;> exact tendsto_const_nhds
  have ew : V .won=1 := finish .won true rfl
  have el : V .lost=0 := finish .lost false rfl
  have eS := step .start rfl
  have e0 := step .zero rfl
  have e00 := step .zeros rfl
  have e1 := step .one rfl
  have e11 := step .ones rfl
  have et := step .tail rfl
  simp only [down,up,ew,el,mul_zero,zero_add,mul_one] at eS e0 e00 e1 e11 et
  have q : 0<1-p := sub_pos.mpr hp.2
  have den : 0<1-p*(1-p) := by nlinarith [sq_nonneg (p-1/2)]
  have e : V .ones=V .tail := by
    apply (mul_left_cancel₀ q.ne' : (1-p)*V .ones=(1-p)*V .tail → _)
    linarith only [e11]
  rw [e,et,e0,e00] at e1
  have cancel : (1-p)*((1-p*(1-p))*V .one-p)=0 := by linarith only [e1]
  have one : V .one=p/(1-p*(1-p)) := (eq_div_iff den.ne').mpr
    (by have := (mul_eq_zero.mp cancel).resolve_left q.ne'; linarith)
  change (⨆ n,byTime longer shorter p n [])=_
  simp only [by_stage]
  change V .start=_
  rw [eS,e0,e00,one]
  field_simp
  ring

end PenneyBias
