module

public import conjectures.BilleyFahrbachTalmageClassification.BinomialBound
public import conjectures.BilleyFahrbachTalmageClassification.Kernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Polynomial bounds for the last four gaps of size two -/

@[expose] public section
namespace BilleyFahrbachTalmageClassification

/-- The cubic correction in the squared prefix coordinate. -/
noncomputable def fourCorrections (x : ℝ) : ℂ :=
  ⟨(-601297/36864) + x * ((134125/36864) + x * ((-7685/12288) + x * ((2755/36864)))),
   (2366435/147456) + x * ((-2383655/147456) + x * ((131167/49152) + x * ((-132095/1032192))))⟩

/-- The odd part of the degree-eleven binomial approximation at both endpoints. -/
noncomputable def lowApprox (x : ℝ) : ℂ :=
  ⟨(2871691423945/139519328256) + x * ((-5463474519175/124017180672) + x * ((258970896856465/53575422050304) + x * ((160017039424769155/9000670904451072) + x * ((1138715711272034935/96007156314144768) + x * ((1210571387472835319347/228113003402407968768)))))),
   (-431028477115/69759664128) + x * ((-638063036575/76101451776) + x * ((867364161979475/26787711025152) + x * ((3754488185981035/562541931528192) + x * ((-5979892142289833755/1296096610240954368) + x * ((-5436447001027982407/740626634423402496))))))⟩

/-- The degree-five binomial approximation at the upper endpoint, with the cubic correction. -/
noncomputable def highApprox (x : ℝ) : ℂ :=
  ⟨(6397/2304) + x * (0 + x * ((-1605/64) + x * (0 + x * ((25375/1152) + x * (0 + x * ((19285/576) + x * ((-2755/288)))))))),
   (156367/64512) + x * (0 + x * ((-19965/256) + x * (0 + x * ((764875/4608) + x * (0 + x * ((-132095/2304) + x * ((132095/8064))))))))⟩

/-- A nonnegative sum in the Bernstein basis certifies the norm bound on a whole interval. -/
private theorem norm_le_of_slack {u v b : ℝ} (hb : 0 ≤ b) (h : 0 ≤ b^2 - (u*u+v*v)) :
    ‖(⟨u,v⟩ : ℂ)‖ ≤ b := by
  apply (sq_le_sq₀ (norm_nonneg _) hb).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  linarith

theorem lowApprox_bound (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/4) :
    ‖lowApprox x‖ ≤ 23 := by
  have ha : 0 ≤ 4*x := by positivity
  have hb : 0 ≤ 1-4*x := by linarith
  have cert : 0 ≤
    (1307571297560332886556619/19465642957005480001536) * (4*x)^0 * (1-4*x)^10 +
    (146720902555052228910609035/133478694562323291439104) * (4*x)^1 * (1-4*x)^9 +
    (151520850183489984777808075285/22424420686470312961769472) * (4*x)^2 * (1-4*x)^8 +
    (113269940457039257932461989588365/5023070233769350103436361728) * (4*x)^3 * (1-4*x)^7 +
    (16955445938336086564432233203024965/361661056831393207447418044416) * (4*x)^4 * (1-4*x)^6 +
    (12328407671199168241002814144851643549/190957038006975613532236727451648) * (4*x)^5 * (1-4*x)^5 +
    (119912079084608786462521014858616218378785/1990952797722183560435015072543145984) * (4*x)^6 * (1-4*x)^4 +
    (19875578296309085793359837220115994556219535/525611538598656459954843979151390539776) * (4*x)^7 * (1-4*x)^3 +
    (6761283460910978774960546895623677863049304795/440366903611383448631258373805383201325056) * (4*x)^8 * (1-4*x)^2 +
    (282958478037153809311690271988547877581232906305/77504575035603486959101473789747443433209856) * (4*x)^9 * (1-4*x)^1 +
    (21107947248346410255281357603693847934662320419591/54563220825064854819207437547982200176979738624) * (4*x)^10 * (1-4*x)^0 := by positivity
  unfold lowApprox
  apply norm_le_of_slack (by linarith)
  linear_combination cert

theorem highApprox_bound (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/4) :
    ‖highApprox x‖ ≤ 111/8 - 44*x := by
  have ha : 0 ≤ 4*x := by positivity
  have hb : 0 ≤ 1-4*x := by linarith
  have cert : 0 ≤
    (744677990671/4161798144) * (4*x)^0 * (1-4*x)^14 +
    (653935927567/297271296) * (4*x)^1 * (1-4*x)^13 +
    (14825365910177/1189085184) * (4*x)^2 * (1-4*x)^12 +
    (12830723137751/297271296) * (4*x)^3 * (1-4*x)^11 +
    (430815950394967/4227858432) * (4*x)^4 * (1-4*x)^10 +
    (471292178838301/2717908992) * (4*x)^5 * (1-4*x)^9 +
    (66676743676180411/304405807104) * (4*x)^6 * (1-4*x)^8 +
    (98585390826682199/473520144384) * (4*x)^7 * (1-4*x)^7 +
    (1452589822253680841/9740985827328) * (4*x)^8 * (1-4*x)^6 +
    (387946512588928393/4870492913664) * (4*x)^9 * (1-4*x)^5 +
    (133974537890898167/4329327034368) * (4*x)^10 * (1-4*x)^4 +
    (650084906273993843/77927886618624) * (4*x)^11 * (1-4*x)^3 +
    (127164080528654023/89060441849856) * (4*x)^12 * (1-4*x)^2 +
    (79915100078384747/623423092948992) * (4*x)^13 * (1-4*x)^1 +
    (57153950560782631/17455846602571776) * (4*x)^14 * (1-4*x)^0 := by positivity
  unfold highApprox
  apply norm_le_of_slack (by linarith)
  linear_combination cert

end BilleyFahrbachTalmageClassification
