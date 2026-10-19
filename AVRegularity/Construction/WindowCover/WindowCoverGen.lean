-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Weighted.DriftCoefficientEmbedding
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.CycleWords.ConstructedNormalizedSpatialJets
import AVRegularity.Velocity.Port.Section2FlowInverseBounds
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
/-! One level-generic preparation cover, with numeric smallness supplied by each caller.
The drift constants and radius cap are fixed before every order request. All metric
bounds are restricted to the per-chart anchor windows.

The degenerate cases are included: identity metric and zero drift satisfy the respective
field certificates with zero envelopes. For the nonzero construction the numeric lower bound
on g is positive, so g=0 is not an admissible instance; no artificial positive lower bound
is imposed on an abstract metric certificate. Level m=2 is included. At the left
endpoint of a renewal block P=2; otherwise P=3. The radius may equal its admissible
upper bound. No positive jet-order request or component nonemptiness is required. -/
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.WindowCover

/-- Order-independent geometric base for the normalized constructed drift. -/
def windowCoverB0 : ℝ := 4 * Real.pi

/-- Order-independent coefficient price, including the drift embedding. -/
def windowCoverCd : ℝ := 2 * Real.pi * max 1 ‖Weighted.driftCoefficientEmbedding‖

/-- Radius cap fixed before jet orders, accuracy, window length and schedules. -/
def windowCoverRadiusCap : ℝ := min 1 (1 / (2 * windowCoverB0))

/-- One background and metric deviation envelope, independent of the metric jet order. -/
def windowCoverCg : ℝ := max 78000 (2 * CycleComparison.Charts.metricDevConst 0) + 1

/-- A fixed second background derivative price. -/
def windowCoverCb : ℝ := 2 ^ (40 : ℕ)

/-- The all-order metric jet prices are chosen before the data. -/
def windowCoverCG (j : ℕ) : ℝ := CycleComparison.Charts.metricDevConst j

/-- Numeric and construction inputs at one level. Every smallness premise is scalar;
there is no assumed cover, metric regularity, drift jet bound or solution certificate. -/
structure WindowCoverFrame (α s q : ℝ) (ζ : ℝ → ℝ) where
  hα₀ : 0 < α
  hα₁ : α < 1 / 3
  hs₀ : 0 < s
  hs₁ : s < (1 - α) / 2
  hq : IsAdmissibleQ α s q
  hζ : IsFastProfile ζ
  Λ : ℕ
  hΛ : 128 ≤ Λ
  M' : ℕ
  κ : ℕ → ℝ
  hband : IsOCBandChain α q Λ ζ M' κ
  m : ℕ
  hm2 : 2 ≤ m
  hmM : m ≤ M'
  ν : ℝ
  B : ℝ
  hν : κ m = ν
  hB : κ (m - 1) = B
  Φ : ℕ → ℝ → Vec 2 → ℝ
  hΦ : IsOCStreamSeq α q Λ ζ Φ
  hφ : IsAdmissibleStream (Φ (m - 1))
  tS : ℝ
  ρs : ℝ
  g : ℝ
  g₀ : ℝ
  a : ℝ
  rho_pos : 0 < ρs
  rho_cap : ρs ≤ windowCoverRadiusCap * ocEpsilon q Λ m
  rho_R : ρs ≤ Real.sqrt (B * ocTauPP α q Λ m)
  g_nonneg : 0 ≤ g
  g_upper : g ≤ g₀
  g_lower : windowCoverCg * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) ≤ g
  a_nonneg : 0 ≤ a
  a_lower : windowCoverCd * ocA α q Λ m * ocEpsilon q Λ m ^ 2 / ν ≤ a
  drift_scale : windowCoverB0 * (ρs / ocEpsilon q Λ m) ≤ 1 / 2
  drift_small : a * windowCoverB0 * (ρs / ocEpsilon q Λ m) ^ 2 ≤ 1 / 8

/-- The first core block, with the half-open ownership convention. -/
def windowCoverFirstBlock {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : ℤ :=
  ⌊F.tS / ocTauPP α q F.Λ F.m + 1 / 2⌋

/-- Two core blocks at an exact left endpoint, three otherwise. -/
def windowCoverBlockCount {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : ℕ :=
  if F.tS = ((windowCoverFirstBlock F : ℝ) - 1 / 2) * ocTauPP α q F.Λ F.m then 2 else 3

/-- The complete shared producer interface. The separation threshold is uniform in
levels, terminal index, stream, diffusivity data, window, centres and every jet request.
The constants above are fixed even before α,s,q,ζ, so the radius cap precedes all
accuracy and schedule requests. Terminal and cascade callers supply their own explicit
numeric lower/upper bounds through WindowCoverFrame. The window has CH=2. -/
def WindowCoverGenStatement : Prop :=
  ∀ (α s q : ℝ) (ζ : ℝ → ℝ),
    0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
    IsAdmissibleQ α s q → IsFastProfile ζ →
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ (F : WindowCoverFrame α s q ζ), Λ₀ ≤ F.Λ →
      ∀ (qJ Kmax : ℕ) (y₀ : Vec 2),
      IsWindowCover α q F.Λ F.m ζ F.Φ F.hφ F.ν F.B F.tS
        (F.tS + 2 * ocTauPP α q F.Λ F.m) F.ρs F.g F.g₀ F.a windowCoverB0 1
        windowCoverCb qJ Kmax windowCoverCG (windowCoverFirstBlock F) (windowCoverBlockCount F) y₀

/-- Scale fields whose common separation threshold is independent of the level. -/
structure WindowCoverScaleFields {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : Prop where
  ν_pos : 0 < F.ν
  B_pos : 0 < F.B
  RE : Real.sqrt (F.B * ocTauPP α q F.Λ F.m) ≤ ocEpsilon q F.Λ (F.m - 1)
  ellT : ocEll q F.Λ F.m F.ν ^ 2 ≤ ocTauPP α q F.Λ F.m
  dur : Real.sqrt (ocTauPP α q F.Λ F.m) * ocEll q F.Λ F.m F.ν / ocTau α q F.Λ F.m *
    Real.exp (-(Real.pi ^ 2 * ocTau α q F.Λ F.m) / (3 * ocEll q F.Λ F.m F.ν ^ 2)) ≤ 1

/-- Global background derivative estimates, which in particular hold on the anchor hull. -/
structure WindowCoverBackgroundFields {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : Prop where
  short1 : ∀ t y, ocTauPP α q F.Λ F.m * ‖fderiv ℝ (streamVel (F.Φ (F.m - 1)) t) y‖ ≤ F.g
  short2 : ∀ t y, ocTauPP α q F.Λ F.m *
    ‖fderiv ℝ (fderiv ℝ (streamVel (F.Φ (F.m - 1)) t)) y‖ ≤
      windowCoverCb * F.g / ocEpsilon q F.Λ (F.m - 1)

/-- Windowed metric certificates, uniform in chart labels and centres. -/
structure WindowCoverMetricFields {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : Prop where
  near : ∀ (l : ℤ) (yc : Vec 2) (t : ℝ),
    |ocEll q F.Λ F.m F.ν ^ 2 * t - (l : ℝ) * ocTauPP α q F.Λ F.m| ≤ ocTauPP α q F.Λ F.m →
    ∀ z (ξ : Vec 2), |∑ a', ∑ k, ξ a' *
      (ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z - 1) a' k * ξ k| ≤
        F.g * ∑ a', ξ a' ^ 2
  smooth : ∀ (l : ℤ) (yc : Vec 2) (t : ℝ) (j : ℕ) (a' k : Fin 2),
    ContDiff ℝ j (fun z => ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z a' k)
  jets : ∀ (l : ℤ) (yc : Vec 2) (t : ℝ),
    |ocEll q F.Λ F.m F.ν ^ 2 * t - (l : ℝ) * ocTauPP α q F.Λ F.m| ≤ ocTauPP α q F.Λ F.m →
    ∀ z (j : ℕ), 1 ≤ j → ∀ a' k : Fin 2,
      ‖iteratedFDeriv ℝ j (fun z' => ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z' a' k) z‖ ≤
        windowCoverCG j * F.g * (ocEpsilon q F.Λ F.m / ocEpsilon q F.Λ (F.m - 1)) ^ j

/-- All-order normalized drift estimates at the same order-independent constants. -/
structure WindowCoverDriftFields {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : Prop where
  jets : ∀ (yc : Vec 2) (t : ℝ) (l : ℕ), 1 ≤ l → ∀ z,
    ‖coefficientDerivativeArray (driftCoefficient (ocCellDrift α q F.Λ ζ F.m F.ν yc t)) l z‖ ≤
      F.a * windowCoverB0 ^ l * (l.factorial : ℝ)

/-- Floor arithmetic for the two-renewal window. -/
structure WindowCoverBlockFields {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) : Prop where
  pos : 1 ≤ windowCoverBlockCount F
  window : ((windowCoverFirstBlock F : ℝ) - 1 / 2) * ocTauPP α q F.Λ F.m ≤ F.tS ∧
    F.tS < ((windowCoverFirstBlock F : ℝ) + 1 / 2) * ocTauPP α q F.Λ F.m ∧
    ((windowCoverFirstBlock F : ℝ) + windowCoverBlockCount F - 3 / 2) * ocTauPP α q F.Λ F.m <
      F.tS + 2 * ocTauPP α q F.Λ F.m ∧
    F.tS + 2 * ocTauPP α q F.Λ F.m ≤
      ((windowCoverFirstBlock F : ℝ) + windowCoverBlockCount F - 1 / 2) * ocTauPP α q F.Λ F.m

/-- The only common asymptotic choice, uniform before all finite requests and data. -/
def WindowCoverScalesStatement : Prop :=
  ∀ (α s q : ℝ) (ζ : ℝ → ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
    IsAdmissibleQ α s q → IsFastProfile ζ → ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ (F : WindowCoverFrame α s q ζ), Λ₀ ≤ F.Λ → WindowCoverScaleFields F

private theorem anchor_age {c h tA tZ t : ℝ} (hc : 0 < c) (l : ℝ)
    (ht : t ∈ Set.Icc (max tA ((l - 1) * h) / c) (min tZ ((l + 1) * h) / c)) :
    |c * t - l * h| ≤ h := by
  have ha := (div_le_iff₀ hc).mp ht.1
  have hb := (le_div_iff₀ hc).mp ht.2
  have hlo := (le_max_right tA ((l - 1) * h)).trans ha
  have hhi := hb.trans (min_le_right tZ ((l + 1) * h))
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi]

/-- Assemble the window cover from its field groups: scales, background, metric, drift and
blocks. -/
theorem windowCoverGen_of_ingredients
    (hscales : WindowCoverScalesStatement)
    (hbackground : ∀ {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ), WindowCoverBackgroundFields F)
    (hmetric : ∀ {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ), WindowCoverMetricFields F)
    (hdrift : ∀ {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ), WindowCoverDriftFields F)
    (hblocks : ∀ {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ), WindowCoverBlockFields F) :
    WindowCoverGenStatement := by
  intro α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₀, hΛ₀, hsc⟩ := hscales α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro F hΛ qJ Kmax y₀
  have hS := hsc F hΛ
  have hc : 0 < ocEll q F.Λ F.m F.ν ^ 2 := by
    unfold ocEll
    exact sq_pos_of_pos (div_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ F.Λ))
      (Real.sqrt_pos.mpr hS.ν_pos))
  have hcap : windowCoverRadiusCap ≤ 1 := min_le_left _ _
  refine {
    pos := ⟨hS.ν_pos, hS.B_pos, F.rho_pos⟩
    P_pos := (hblocks F).pos
    RE := hS.RE
    ellT := hS.ellT
    rho_e := F.rho_cap.trans ?_
    rho_R := F.rho_R
    dur := hS.dur
    short1 := fun t _ y => (hbackground F).short1 t y
    short2 := fun t _ y => (hbackground F).short2 t y
    window := (hblocks F).window
    g_range := ⟨F.g_nonneg, F.g_upper⟩
    metric_near := fun i t ht => (hmetric F).near _ _ t (anchor_age hc _ ht)
    metric_smooth := fun i t _ a' k => (hmetric F).smooth _ _ t qJ a' k
    metric_jets := fun i t ht z j hj _ a' k => (hmetric F).jets _ _ t (anchor_age hc _ ht) z j hj a' k
    drift_pos := ⟨F.a_nonneg, ?_, zero_lt_one⟩
    drift_jets := fun i l hl _ t _ z => by simpa only [one_zpow, mul_one] using (hdrift F).jets _ t l hl z
    drift_scale := by simpa only [div_one] using F.drift_scale
    drift_small := F.drift_small }
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap
      (Construction.Stream.ocEpsilon_pos (q := q) (n := F.m) (by omega : 1 ≤ F.Λ)).le
  · unfold windowCoverB0
    have := Real.pi_gt_three
    linarith

end AVRegularity.Construction.WindowCover
end
end

section
/-! Half-open core ownership and the exact two-renewal window. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.WindowCover

/-- The left-endpoint case uses the smallest possible number of core blocks. -/
theorem windowCoverBlocks {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) :
    WindowCoverBlockFields F := by
  have h128 := F.hΛ
  have hh : 0 < ocTauPP α q F.Λ F.m := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ F.Λ)
  have hf := Int.floor_le (F.tS / ocTauPP α q F.Λ F.m + 1 / 2)
  have hf' := Int.lt_floor_add_one (F.tS / ocTauPP α q F.Λ F.m + 1 / 2)
  change (windowCoverFirstBlock F : ℝ) ≤ _ at hf
  change _ < (windowCoverFirstBlock F : ℝ) + 1 at hf'
  have hlo : ((windowCoverFirstBlock F : ℝ) - 1 / 2) * ocTauPP α q F.Λ F.m ≤ F.tS := by
    apply (le_div_iff₀ hh).mp
    linarith only [hf]
  have hhi : F.tS < ((windowCoverFirstBlock F : ℝ) + 1 / 2) * ocTauPP α q F.Λ F.m := by
    apply (div_lt_iff₀ hh).mp
    linarith only [hf']
  refine ⟨?_, hlo, hhi, ?_, ?_⟩
  · unfold windowCoverBlockCount
    split_ifs <;> norm_num
  · unfold windowCoverBlockCount
    split_ifs with he
    · norm_num only [Nat.cast_ofNat]
      nlinarith only [he, hh]
    · have hs := lt_of_le_of_ne hlo (Ne.symm he)
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hs]
  · unfold windowCoverBlockCount
    split_ifs with he
    · norm_num only [Nat.cast_ofNat]
      nlinarith only [he]
    · norm_num only [Nat.cast_ofNat]
      nlinarith only [hhi]

end AVRegularity.Construction.WindowCover
end
end

section
/-! Background bounds on every time, hence on the complete chart-anchor hull. -/
@[expose] public noncomputable section
open Homogenization AVenhance
open AVRegularity.Velocity.Port.Section2FlowHigherDerivative
namespace AVRegularity.Construction.WindowCover

private theorem background_second_price {A E : ℝ} (hA : 0 ≤ A) (hE : 0 < E) :
    (2 : ℝ) ^ (2 : ℕ) * (8192 * A * E * (2 : ℕ).factorial *
      (256 * E⁻¹) ^ (2 : ℕ) / ((2 : ℝ) + 1) ^ 2) ≤ 2 ^ (40 : ℕ) * A / E := by
  have heq : (2 : ℝ) ^ (2 : ℕ) * (8192 * A * E * (2 : ℕ).factorial *
      (256 * E⁻¹) ^ (2 : ℕ) / ((2 : ℝ) + 1) ^ 2) = (2 ^ (32 : ℕ) / 9) * A / E := by
    norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ (32 : ℕ) / 9 ≤ 2 ^ (40 : ℕ)) hA) hE.le

/-- Both short-flow estimates hold uniformly on the entire anchor hull. -/
theorem windowCoverBackground {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) :
    WindowCoverBackgroundFields F := by
  have h128 := F.hΛ
  have hΛ : 1 ≤ F.Λ := by omega
  have he : 0 < ocEpsilon q F.Λ (F.m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hA : 0 < ocA α q F.Λ (F.m - 1) := Real.rpow_pos_of_pos he _
  have hh : 0 < ocTauPP α q F.Λ F.m := Construction.Stream.ocTauPP_pos hΛ
  have hm := F.hm2
  have hCg1 : 1 ≤ windowCoverCg := by
    unfold windowCoverCg
    have hc := le_max_left (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
    linarith only [hc]
  have hCg : (78000 : ℝ) ≤ windowCoverCg := by
    unfold windowCoverCg
    have hc := le_max_left (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
    linarith only [hc]
  have hAg : ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m ≤ F.g := by
    calc
      _ ≤ windowCoverCg * (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) :=
        le_mul_of_one_le_left (mul_nonneg hA.le hh.le) hCg1
      _ ≤ F.g := F.g_lower
  constructor
  · intro t y
    have hb := Applications.streamVel_slice_fderiv_le α s F.hα₀ F.hα₁ F.hs₀ F.hs₁ q F.hq
      ζ F.hζ F.Λ F.hΛ F.Φ F.hΦ (F.m - 1) t y
    calc
      _ ≤ ocTauPP α q F.Λ F.m * (78000 * ocA α q F.Λ (F.m - 1)) :=
        mul_le_mul_of_nonneg_left hb hh.le
      _ ≤ windowCoverCg * (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) := by
        nlinarith only [mul_le_mul_of_nonneg_right hCg (mul_nonneg hA.le hh.le)]
      _ ≤ F.g := F.g_lower
  · intro t y
    let v := streamVel (F.Φ (F.m - 1)) t
    have hφ := Velocity.streamSeq_admissible F.hζ F.hΛ F.hΦ (F.m - 1)
    have hv : ContDiff ℝ (⊤ : ℕ∞) v :=
      (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.comp
        (contDiff_const.prodMk contDiff_id)
    have hs := Preservation.Buffer.actual_stream_drift_snorm α s F.hα₀ F.hα₁ F.hs₀ F.hs₁ q F.hq
      ζ F.hζ F.Λ F.hΛ F.Φ F.hΦ (F.m - 1) (by omega) t 2 (by omega)
    have hb : ‖iteratedFDeriv ℝ 2 v y‖ ≤
        (2 : ℝ) ^ (2 : ℕ) * (8192 * ocA α q F.Λ (F.m - 1) * ocEpsilon q F.Λ (F.m - 1) *
          (2 : ℕ).factorial * (256 * (ocEpsilon q F.Λ (F.m - 1))⁻¹) ^ (2 : ℕ) /
          ((2 : ℝ) + 1) ^ 2) := by
      apply Infra.Section4.amnr_multilinear_norm_le_two_pow_basis 2 _ (by positivity)
      intro w
      have hw := orderedPartial_pointwise_of_snorm hv
        (mul_pos (by norm_num) (inv_pos.mpr he))
        (mul_nonneg (mul_nonneg (by norm_num) hA.le) he.le) hs w y
      rw [orderedPartial_eq_iteratedFDeriv hv y w] at hw
      exact hw
    have hb' : ‖fderiv ℝ (fderiv ℝ v) y‖ ≤ windowCoverCb * ocA α q F.Λ (F.m - 1) /
        ocEpsilon q F.Λ (F.m - 1) := by
      rw [← norm_iteratedFDeriv_one (fderiv ℝ v), norm_iteratedFDeriv_fderiv]
      exact hb.trans (background_second_price hA.le he)
    calc
      _ ≤ ocTauPP α q F.Λ F.m * (windowCoverCb * ocA α q F.Λ (F.m - 1) /
          ocEpsilon q F.Λ (F.m - 1)) := mul_le_mul_of_nonneg_left hb' hh.le
      _ = windowCoverCb * (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) /
          ocEpsilon q F.Λ (F.m - 1) := by ring
      _ ≤ windowCoverCb * F.g / ocEpsilon q F.Λ (F.m - 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAg (by unfold windowCoverCb; positivity)) he.le

end AVRegularity.Construction.WindowCover
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.WindowCover

/-! The actual material metric in cell variables, restricted to each anchor window. -/

private theorem quadratic_entries (A : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Vec 2)
    (D : ℝ) (hD : 0 ≤ D) (hA : ∀ i j, |A i j| ≤ D) :
    |∑ i, ∑ j, ξ i * A i j * ξ j| ≤ 2 * D * ∑ i, ξ i ^ 2 := by
  have h := CycleDamping.quadratic_entry_error (fun i j => (A i j : ℂ)) ξ D hD
    (fun i j => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hA i j)
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_eq_abs] using h

private theorem unscale_jet {E e C n : ℝ} (hE : 0 < E) (he : 0 < e) (j : ℕ)
    (h : (E / e) ^ j * n ≤ C) : n ≤ C * (e / E) ^ j := by
  have hc : (e / E) ^ j * (E / e) ^ j = 1 := by
    rw [← mul_pow]
    field_simp
    simp only [one_pow]
  calc
    n = (e / E) ^ j * ((E / e) ^ j * n) := by rw [← mul_assoc, hc, one_mul]
    _ ≤ (e / E) ^ j * C := mul_le_mul_of_nonneg_left h (pow_nonneg (div_pos he hE).le _)
    _ = C * (e / E) ^ j := mul_comm _ _

/-- Metric closeness and all jets hold on the chart's own anchor neighbourhood. -/
theorem windowCoverMetric {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) :
    WindowCoverMetricFields F := by
  have h128 := F.hΛ
  have he : 0 < ocEpsilon q F.Λ F.m := Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ F.Λ)
  have hE : 0 < ocEpsilon q F.Λ (F.m - 1) := Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ F.Λ)
  have hA : 0 < ocA α q F.Λ (F.m - 1) := Real.rpow_pos_of_pos hE _
  have hh : 0 < ocTauPP α q F.Λ F.m := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ F.Λ)
  have hγ : 0 ≤ ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m := mul_nonneg hA.le hh.le
  have hCg1 : 1 ≤ windowCoverCg := by
    unfold windowCoverCg
    have := le_max_left (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
    linarith
  have hCg0 : 2 * CycleComparison.Charts.metricDevConst 0 ≤ windowCoverCg := by
    unfold windowCoverCg
    have := le_max_right (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
    linarith
  have hbase : ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m ≤ F.g :=
    (le_mul_of_one_le_left hγ hCg1).trans F.g_lower
  refine ⟨?_, ?_, ?_⟩
  · intro l yc t ht z ξ
    have hd := CycleComparison.Charts.ocMaterialMetric_deviation α s F.hα₀ F.hα₁ F.hs₀ F.hs₁
      q F.hq ζ F.hζ F.Λ F.hΛ F.Φ F.hΦ F.m F.hm2 F.hφ l
      (ocEll q F.Λ F.m F.ν ^ 2 * t) ht 0
    have hb (i j : Fin 2) :
        |(ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z - 1) i j| ≤
          CycleComparison.Charts.metricDevConst 0 *
            (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) := by
      simpa only [ocCellMetric, Matrix.sub_apply, Matrix.one_apply, pow_zero,
        one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        (hd i j).bound (yc + ocEpsilon q F.Λ F.m • z) 0 le_rfl
    have hn := quadratic_entries _ ξ _
      (mul_nonneg (CycleComparison.Charts.metricDevConst_nonneg 0) hγ) hb
    refine hn.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc
      _ = (2 * CycleComparison.Charts.metricDevConst 0) *
          (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) := by ring
      _ ≤ windowCoverCg * (ocA α q F.Λ (F.m - 1) * ocTauPP α q F.Λ F.m) :=
        mul_le_mul_of_nonneg_right hCg0 hγ
      _ ≤ F.g := F.g_lower
  · intro l yc t j a' k
    exact ((CycleWords.ocCellMetric_joint_contDiff α q F.Λ F.m F.hφ l F.ν yc a' k).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  · intro l yc t ht z j hj a' k
    let f : Vec 2 → ℝ := fun y => ocMaterialMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l
      (ocEll q F.Λ F.m F.ν ^ 2 * t) y a' k - (if a' = k then 1 else 0)
    have hd := CycleComparison.Charts.ocMaterialMetric_deviation α s F.hα₀ F.hα₁ F.hs₀ F.hs₁
      q F.hq ζ F.hζ F.Λ F.hΛ F.Φ F.hΦ F.m F.hm2 F.hφ l
      (ocEll q F.Λ F.m F.ν ^ 2 * t) ht j a' k
    have haff := CycleJointProofs.affineSample_scaled_jet_identity j f hd.contDiff
      (ocEpsilon q F.Λ F.m) (ocEpsilon q F.Λ (F.m - 1)) he yc z
    have hb := haff.trans_le (hd.bound (yc + ocEpsilon q F.Λ F.m • z) j le_rfl)
    have hu := unscale_jet hE he j hb
    have hs : ContDiff ℝ (j : ℕ∞)
        (fun z => ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z a' k) :=
      ((CycleWords.ocCellMetric_joint_contDiff α q F.Λ F.m F.hφ l F.ν yc a' k).comp
        (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have heq := Preservation.FullLift.norm_iteratedFDeriv_sub_const_of_ne j (by omega)
      _ hs (if a' = k then (1 : ℝ) else 0) z
    change ‖iteratedFDeriv ℝ j (fun z' => ocCellMetric α q F.Λ F.m (F.Φ (F.m - 1)) F.hφ l F.ν yc t z' a' k) z‖ ≤ _
    rw [← heq]
    change ‖iteratedFDeriv ℝ j (fun z' => f (yc + ocEpsilon q F.Λ F.m • z')) z‖ ≤ _
    refine hu.trans ?_
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_pos he hE).le _)
    exact mul_le_mul_of_nonneg_left hbase (CycleComparison.Charts.metricDevConst_nonneg j)

/-! One separation threshold for the spatial radius, cell clock and duration fields. -/

private theorem small_power {E C δ L : ℝ} (hE : 0 < E) (hC : 0 < C) (hδ : 0 < δ)
    (hL : 0 < L) (hEL : E ≤ L⁻¹) (hLC : (81 * C) ^ (1 / (2 * δ)) ≤ L) :
    81 * C * E ^ (2 * δ) ≤ 1 := by
  have hR : (81 * C * E ^ (2 * δ)) * E ≤ (81 * C) * E ^ (1 + 2 * δ) := by
    rw [Real.rpow_add hE, Real.rpow_one]
    apply le_of_eq
    ring
  have h := CycleComparison.Assembly.le_of_powerLaw_of_small hE
    (mul_pos (by norm_num) hC) (mul_pos (by norm_num) hδ) hL hEL hLC hR
  exact (mul_le_mul_iff_left₀ hE).mp (by simpa only [mul_comm, one_mul, mul_one] using h)

private theorem prefactor_bound {E C δ L r : ℝ} (hE : 0 < E) (_hC : 0 ≤ C)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hLbound : L ≤ 9 * E ^ (-δ))
    (hrbound : r ≤ C * E ^ (4 * δ)) (hsmall : 81 * C * E ^ (2 * δ) ≤ 1) :
    L ^ 2 * r ≤ 1 := by
  have hpow : (E ^ (-δ)) ^ 2 * E ^ (4 * δ) = E ^ (2 * δ) := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
    ring
  calc
    L ^ 2 * r ≤ (9 * E ^ (-δ)) ^ 2 * (C * E ^ (4 * δ)) :=
      mul_le_mul (pow_le_pow_left₀ hL hLbound 2) hrbound hr (sq_nonneg _)
    _ = 81 * C * ((E ^ (-δ)) ^ 2 * E ^ (4 * δ)) := by ring
    _ = 81 * C * E ^ (2 * δ) := by rw [hpow]
    _ ≤ 1 := hsmall

private theorem duration_bound {T τ ell : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ) (hell : 0 < ell)
    (h : T * ell ^ 2 ≤ τ ^ 2) :
    Real.sqrt T * ell / τ * Real.exp (-(Real.pi ^ 2 * τ) / (3 * ell ^ 2)) ≤ 1 := by
  have hp : (Real.sqrt T * ell) ^ 2 ≤ τ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hT]
    exact h
  have hs : Real.sqrt T * ell ≤ τ :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hell.le) hτ.le).mp hp
  have hpre : Real.sqrt T * ell / τ ≤ 1 := (div_le_one hτ).mpr hs
  have hexp : Real.exp (-(Real.pi ^ 2 * τ) / (3 * ell ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hτ.le)) (by positivity))
  exact (mul_le_mul_of_nonneg_left hexp (div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) hell.le) hτ.le)).trans (by simpa only [mul_one] using hpre)

/-- All three scale constraints hold at every level 2<=m<=M' after one separation choice. -/
theorem windowCoverScales : WindowCoverScalesStatement := by
  intro α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨C, hC, Λ₁, hΛ₁, hlaws⟩ :=
    CycleComparison.Assembly.scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  refine ⟨max Λ₁ ⌈(81 * C) ^ (1 / (2 * ocDelta α q))⌉₊,
    hΛ₁.trans (le_max_left _ _), ?_⟩
  intro F hΛ
  have hΛ₁F : Λ₁ ≤ F.Λ := (le_max_left _ _).trans hΛ
  have h128 := F.hΛ
  have hm := F.hm2
  have hΛpos : 0 < (F.Λ : ℝ) := by exact_mod_cast (by omega : 0 < F.Λ)
  have he : 0 < ocEpsilon q F.Λ F.m := Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ F.Λ)
  have hE : 0 < ocEpsilon q F.Λ (F.m - 1) := Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ F.Λ)
  have hE1 : ocEpsilon q F.Λ (F.m - 1) ≤ 1 := (Scales.epsilon_basic hq.1 F.hΛ).2.1
  have hh : 0 < ocTauPP α q F.Λ F.m := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ F.Λ)
  have hτ : 0 < ocTau α q F.Λ F.m := Construction.Stream.ocTau_pos (by omega : 1 ≤ F.Λ)
  have hS := hlaws F.Λ hΛ₁F F.M' F.κ F.hband F.m F.hm2 F.hmM F.ν F.B F.hν F.hB
  have hell : 0 < ocEll q F.Λ F.m F.ν := div_pos he (Real.sqrt_pos.mpr hS.ν_pos)
  have hB : 0 < F.B := F.hB ▸ CycleReference.bandChain_pos (by omega : 1 ≤ F.Λ) F.hζ F.hband
    (by have := F.hmM; omega : F.m - 1 ≤ F.M')
  have hEL := CycleReference.epsilon_le_inv_separation hq.1 F.hΛ (by omega : 1 ≤ F.m - 1)
  have hLC : (81 * C) ^ (1 / (2 * ocDelta α q)) ≤ (F.Λ : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hΛ))
  have hsmall := small_power hE hCp hδ hΛpos hEL hLC
  have htime := Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq F.hΛ (by omega : 1 ≤ F.m)
  have h5 := htime.1
  have hL1 : (1 : ℝ) ≤ (ocL α q F.Λ F.m : ℝ) := by exact_mod_cast (by omega : 1 ≤ ocL α q F.Λ F.m)
  have hLpos : 0 < (ocL α q F.Λ F.m : ℝ) := zero_lt_one.trans_le hL1
  have hclock : ocTauPP α q F.Λ F.m = ocTau α q F.Λ F.m * (ocL α q F.Λ F.m : ℝ) ^ 2 := by
    rw [ocTau]
    field_simp
  have hrpos : 0 ≤ ocEll q F.Λ F.m F.ν ^ 2 / ocTau α q F.Λ F.m := div_nonneg (sq_nonneg _) hτ.le
  have hrbound : ocEll q F.Λ F.m F.ν ^ 2 / ocTau α q F.Λ F.m ≤
      C * ocEpsilon q F.Λ (F.m - 1) ^ (4 * ocDelta α q) := by
    have hp := (le_div_iff₀ (pow_pos hell 2)).mp hS.quiet_ge
    have hc : (C * ocEpsilon q F.Λ (F.m - 1) ^ (4 * ocDelta α q)) *
        (C⁻¹ * ocEpsilon q F.Λ (F.m - 1) ^ (-(4 * ocDelta α q))) = 1 := by
      calc
        _ = (C * C⁻¹) * (ocEpsilon q F.Λ (F.m - 1) ^ (4 * ocDelta α q) *
            ocEpsilon q F.Λ (F.m - 1) ^ (-(4 * ocDelta α q))) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hCp.ne', ← Real.rpow_add hE]; simp
    apply (div_le_iff₀ hτ).mpr
    calc
      _ = (C * ocEpsilon q F.Λ (F.m - 1) ^ (4 * ocDelta α q)) *
          ((C⁻¹ * ocEpsilon q F.Λ (F.m - 1) ^ (-(4 * ocDelta α q))) *
            ocEll q F.Λ F.m F.ν ^ 2) := by rw [← mul_assoc, hc, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp
        (mul_nonneg hCp.le (Real.rpow_nonneg hE.le _))
  have hratio : (ocL α q F.Λ F.m : ℝ) ^ 2 *
      (ocEll q F.Λ F.m F.ν ^ 2 / ocTau α q F.Λ F.m) ≤ 1 :=
    prefactor_bound hE hCp.le hLpos.le hrpos htime.2.2.1 hrbound hsmall
  have hpref : ocTauPP α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2 ≤ ocTau α q F.Λ F.m ^ 2 := by
    rw [hclock]
    have hh' := (div_le_iff₀ hτ).mp (show (ocL α q F.Λ F.m : ℝ) ^ 2 * ocEll q F.Λ F.m F.ν ^ 2 /
      ocTau α q F.Λ F.m ≤ 1 by simpa only [mul_div_assoc] using hratio)
    nlinarith only [hh', hτ]
  have hellτ : ocEll q F.Λ F.m F.ν ^ 2 ≤ ocTau α q F.Λ F.m := by
    have hLsq : 1 ≤ (ocL α q F.Λ F.m : ℝ) ^ 2 := one_le_pow₀ hL1
    have hr1 : ocEll q F.Λ F.m F.ν ^ 2 / ocTau α q F.Λ F.m ≤ 1 :=
      (le_mul_of_one_le_left hrpos hLsq).trans hratio
    simpa only [one_mul] using (div_le_iff₀ hτ).mp hr1
  have hτh : ocTau α q F.Λ F.m ≤ ocTauPP α q F.Λ F.m := by
    rw [hclock]
    exact le_mul_of_one_le_right hτ.le (one_le_pow₀ hL1)
  exact ⟨hS.ν_pos, hB, hS.radius_le, hellτ.trans hτh, duration_bound hh.le hτ hell hpref⟩

end AVRegularity.Construction.WindowCover
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.WindowCover

/-! All normalized drift arrays at constants independent of the derivative order. -/

/-- The constructed cell drift has one geometric all-order array envelope. -/
theorem windowCoverDrift {α s q : ℝ} {ζ : ℝ → ℝ} (F : WindowCoverFrame α s q ζ) :
    WindowCoverDriftFields F := by
  have h128 := F.hΛ
  have hΛ : 1 ≤ F.Λ := by omega
  have hν : 0 < F.ν := F.hν ▸ CycleReference.bandChain_pos hΛ F.hζ F.hband F.hmM
  have he : 0 < ocEpsilon q F.Λ F.m := Construction.Stream.ocEpsilon_pos hΛ
  have hA : 0 < ocA α q F.Λ F.m := Real.rpow_pos_of_pos he _
  have hell : ocEll q F.Λ F.m F.ν ^ 2 = ocEpsilon q F.Λ F.m ^ 2 / F.ν := by
    rw [ocEll, div_pow, Real.sq_sqrt hν.le]
  constructor
  intro yc t l _hl z
  have hs := CycleWords.constructed_spatial_contDiff (α := α) (q := q) (m := F.m) hΛ F.hζ F.ν yc t
  have hv : ‖iteratedFDeriv ℝ l (ocCellDrift α q F.Λ ζ F.m F.ν yc t) z‖ ≤
      |2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2| * (2 * Real.pi) ^ l := by
    apply CycleWords.vec2_iteratedFDeriv_bound_of_components _ l (hs.of_le (by simp)) z _
      (mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
    intro i
    exact CycleWords.constructed_spatial_component_jet_bound hΛ F.hζ F.ν yc t i l z
  have hcard : (Fintype.card (DerivativeWord2 l) : ℝ) = (2 : ℝ) ^ l := by
    simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpos : 0 ≤ 2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2 := by positivity
  have hmax := le_max_right (1 : ℝ) ‖Weighted.driftCoefficientEmbedding‖
  have hprice : ‖Weighted.driftCoefficientEmbedding‖ *
      (2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2) ≤ F.a := by
    calc
      _ ≤ max 1 ‖Weighted.driftCoefficientEmbedding‖ *
          (2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2) :=
        mul_le_mul_of_nonneg_right hmax hpos
      _ = windowCoverCd * ocA α q F.Λ F.m * ocEpsilon q F.Λ F.m ^ 2 / F.ν := by
        rw [hell]
        unfold windowCoverCd
        ring
      _ ≤ F.a := F.a_lower
  have hb : 0 ≤ windowCoverB0 ^ l := pow_nonneg (by unfold windowCoverB0; positivity) _
  calc
    _ ≤ ((Fintype.card (DerivativeWord2 l) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖) *
        ‖iteratedFDeriv ℝ l (ocCellDrift α q F.Λ ζ F.m F.ν yc t) z‖ :=
      Weighted.driftCoefficient_array_norm_le_iterated _ l (hs.of_le (by simp)) z
    _ ≤ ((2 : ℝ) ^ l * ‖Weighted.driftCoefficientEmbedding‖) *
        (|2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2| * (2 * Real.pi) ^ l) := by
      rw [hcard]
      exact mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (‖Weighted.driftCoefficientEmbedding‖ *
        (2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2)) *
        ((2 : ℝ) ^ l * (2 * Real.pi) ^ l) := by
      rw [abs_of_nonneg hpos]
      ring
    _ = (‖Weighted.driftCoefficientEmbedding‖ *
        (2 * Real.pi * ocA α q F.Λ F.m * ocEll q F.Λ F.m F.ν ^ 2)) * windowCoverB0 ^ l := by
      rw [← mul_pow, show (2 : ℝ) * (2 * Real.pi) = windowCoverB0 by
        unfold windowCoverB0; ring]
    _ ≤ F.a * windowCoverB0 ^ l := mul_le_mul_of_nonneg_right hprice hb
    _ ≤ F.a * windowCoverB0 ^ l * (l.factorial : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg F.a_nonneg hb) (by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos l)))

end AVRegularity.Construction.WindowCover
end
end

section
public section
namespace AVRegularity.Construction.WindowCover

/-! The shared level-generic window cover, with all field groups discharged. -/

/-- A two-renewal cover at every admissible level, with constants fixed before all data. -/
theorem windowCoverGen : WindowCoverGenStatement :=
  windowCoverGen_of_ingredients windowCoverScales windowCoverBackground
    windowCoverMetric windowCoverDrift windowCoverBlocks

end AVRegularity.Construction.WindowCover
end
end
