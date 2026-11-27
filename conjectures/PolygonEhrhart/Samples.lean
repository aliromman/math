module

public import conjectures.PolygonEhrhart.Transfer

@[expose] public section
namespace PolygonEhrhart
open Finset Matrix

private def prefixes (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => (z+x)::prefixes (z+x) xs

private def suffixes : List ℕ → ℕ × List ℕ
  | [] => (0,[])
  | x::xs =>
    let (z,ys) := suffixes xs
    (x+z,(x+z)::ys)

private theorem prefixes_ofFn {n : ℕ} (z : ℕ) (f : Fin n → ℕ) :
    prefixes z (List.ofFn f) = List.ofFn (fun i ↦ z + ∑ j : Fin n, if j≤i then f j else 0) := by
  induction n generalizing z with
  | zero => simp [prefixes]
  | succ n ih =>
    rw [List.ofFn_succ,prefixes,List.ofFn_succ,ih]
    congr 1
    · simp
    · congr 1;funext i;simp [Fin.sum_univ_succ,add_assoc]

private theorem suffixes_ofFn {n : ℕ} (f : Fin n → ℕ) :
    suffixes (List.ofFn f) = (∑j,f j, List.ofFn (fun i ↦ ∑ j : Fin n, if i≤j then f j else 0)) := by
  induction n with
  | zero => simp [suffixes]
  | succ n ih =>
    rw [List.ofFn_succ,suffixes,ih,List.ofFn_succ,Fin.sum_univ_succ]
    simp only [Prod.mk.injEq,true_and,List.cons.injEq]
    constructor
    · simp [Fin.sum_univ_succ]
    · congr 1;funext i;simp [Fin.sum_univ_succ]

private def fastRow {w : ℕ} (s : Fin (w+1)) : ℕ → List ℕ
  | 0 => List.ofFn (fun j : Fin (w+1) ↦ if s=j then 1 else 0)
  | k+1 => (suffixes (prefixes 0 (fastRow s k))).2

private theorem fastRow_power {w : ℕ} (s : Fin (w+1)) (k : ℕ) :
    fastRow s k = List.ofFn ((kernel w ^ k) s) := by
  induction k with
  | zero => simp [fastRow,Matrix.one_apply]
  | succ k ih =>
    rw [fastRow,ih,prefixes_ofFn,suffixes_ofFn,pow_succ]
    dsimp only
    apply congrArg List.ofFn
    funext j
    simp only [zero_add,Matrix.mul_apply,←edge_choices,mul_sum,mul_ite,mul_one,mul_zero]
    rw [sum_comm]
    apply sum_congr rfl;intro i _
    by_cases h : j≤i <;> simp [h]

private def traceCount (w : ℕ) : ℕ := ∑ s : Fin (w+1), (fastRow s 13).getD s.val 0

private theorem traceCount_eq (w : ℕ) : traceCount w = crownCount 13 w := by
  rw [crown_thirteen]
  unfold traceCount
  apply sum_congr rfl;intro i _
  rw [fastRow_power,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp only [List.length_ofFn];exact i.isLt),List.getElem_ofFn]
  rfl

private def widths : Array ℕ :=
  #[1,271443,1385407029,
    874569107071,154424192534978,11590981980134136,
    471109005712845073,12073893516637797647,216054227528911051598,
    2899588931289770319928,30747252105854418602807,267900870986039891665533,
    1976658261038065237688965,12646583259151935165028659,71505544338055517905383002,
    362852466483982941465664294,1673644967862052696066138463,7091534775916075003484209649,
    27850704697432295249191815709,102151810477267331847970867095,352204279293140920190902505756,
    1147947037059968833062938517298,3554264799119307289506871036659,10498698066409011044245276217901,
    29697044023575712453995735900724,80710316446302004065351530568318,211382155607852560741336416052863,
    534907644994676627454203692327477,1310960487246736777485104974336647]

def samples (i : Fin 29) : ℕ :=
  (#[1,271445,1385949918,
    877340735462,156177488055984,11902459615510642,
    494757747455810373,13051506551933907751,241662482885323056727,
    3369862390508482525631,37245314403986060597342,339021637403503530334586,
    2617456221441086237760795,17542474064630604110215663,103973036245875639888053533,
    553256064911103617131555697,2676184061438384290441196324,11890646833881739967235046600,
    48955814303757390893220712585,188172792250900373667177245665,679594049491184276632036284501,
    2318962343791437012659833840635,7512595437210997038194502433428,23204926597039568107974447244122,
    68594301780443851631750127955540,194693993410150139220877339235276,532175840647708987551340966567875,
    1404565332879944463336008286227951,3587915312358916716605780580224674] : Array ℕ).getD i.val 0

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem width_values : ∀ i : Fin 29, traceCount i.val = widths.getD i.val 0 := by
  decide +kernel

private theorem layer_values (i : Fin 29) : (∑ lo : Fin (i.val+1),∑ hi : Fin (i.val+1),
    if lo≤hi then widths.getD (hi.val-lo.val) 0 else 0) = samples i := by
  revert i
  decide +kernel

theorem sample_counts (i : Fin 29) : pointCount 13 i.val = samples i := by
  rw [pointCount_layers,←layer_values]
  apply sum_congr rfl;intro lo _
  apply sum_congr rfl;intro hi _
  split_ifs
  · let z : Fin 29 := ⟨hi.val-lo.val,by have := hi.isLt;have := i.isLt;omega⟩
    exact (traceCount_eq z).symm.trans (width_values z)
  · rfl

end PolygonEhrhart
