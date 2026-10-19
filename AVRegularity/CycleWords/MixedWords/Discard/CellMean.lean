-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WCrudeObjects
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # The discard inputs of `cycle_mixed_words`: the pieces (statements only)

The three statements `ChainFullFieldStatement`, `QuietHighStatement` and `MarksBandStatement` are
reduced to the statements of this file. The route is
at the fibre level: the stage curves of the amplitude identification (the Bloch parts of the
moments `y^β u_j`, at every real plane frequency of the zone), tested against adjoint curves.

* Shared: `IsFibreKernel` (an `L²` decay kernel of the homogeneous fibre equation),
  `CellKernelHsStatement`, `CellAdjointKernelHsStatement` (the homogeneous propagators in `H^j`,
  from the cell-equation regularity), `PlainKernelStatement`, `MarksKernelStatement`, `StageFamilyZoneStatement` (the
  transform families at every frequency of the zone), `PlainStageStatement` (the plain
  pass: every stage against smooth tests, at every time).
* Positive orders on a terminal window: `CellForcedHsStatement`, `CellNegativeSmoothingStatement`,
  `StageSourceHsStatement`, and the fibre form of the full-field bound `FullFieldFibreStatement`.
* The two decays: `MarksBandFibreStatement`, `QuietHighFibreStatement`.
* From the fibres to the plane: `StageDatumStatement`, `BlochOutputStatement`,
  `BandOutputStatement`.
* Rough data: `ChainFullFieldCompactStatement`, `ChainWeakContinuityStatement`. -/

universe u v

/-! ## The homogeneous fibre equation -/

/-- `κ` is an `L²` decay kernel of the homogeneous fibre equation of `C` on `[a, b]`, with
comparison constant `A`: every homogeneous curve on `[r, s]` has `‖u(s)‖ ≤ κ(r,s)‖u(r)‖`, the
kernel is positive, at most one, almost multiplicative, almost decreasing in its right end, and
loses at most `A` when the interval is shortened by at most one at each end. Examples: `κ = 1`
(`L²` contraction at a real frequency); `κ(r,s) = 2^{-n(r,s)}`, `n` the number of complete marks
of one orientation in `[r, s]` (high band). -/
structure IsFibreKernel (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (a b A : ℝ) (κ : ℝ → ℝ → ℝ) : Prop where
  pos : ∀ r s, 0 < κ r s
  le_one : ∀ r s, κ r s ≤ 1
  self : ∀ r, κ r r = 1
  mul_le : ∀ r s t, a ≤ r → r ≤ s → s ≤ t → t ≤ b → κ r s * κ s t ≤ A * κ r t
  anti : ∀ r s t, a ≤ r → r ≤ s → s ≤ t → t ≤ b → κ r t ≤ A * κ r s
  shrink : ∀ r r' t' t, a ≤ r → r ≤ r' → r' ≤ r + 1 → r' ≤ t' → t' ≤ t → t ≤ t' + 1 → t ≤ b →
    κ r' t' ≤ A * κ r t
  decay : ∀ r s, a ≤ r → r ≤ s → s ≤ b → ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve r s u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) 0 0) →
    ‖u s‖ ≤ κ r s * ‖u r‖

/-- **The homogeneous propagator in `H^j`, every duration, with a kernel.** For the fibre
equation with a smooth drift (real shift `|θ| ≤ ρ`, drift jets of order `≤ j + 1` at most `L`): `H^j` is
propagated to every later time with the kernel, and after a time `τ ≤ 1` the curve is in `H^j`
with `τ^{-j/2}` times the kernel times its initial `L²` norm. -/
def CellKernelHsStatement : Prop :=
  ∀ (j : ℕ) (ρ A : ℝ), 0 ≤ ρ → 1 ≤ A → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ κ : ℝ → ℝ → ℝ,
    IsFibreKernel ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb a b A κ →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice t) 0 0) →
    (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b,
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
        ‖w‖ ≤ C * (1 + L) ^ Q * κ a t * ‖w₀‖) ∧
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ t ∈ Set.Icc a b, a + τ ≤ t →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
        ‖w‖ ≤ C * (1 + L) ^ Q * τ ^ (-(j : ℝ) / 2) * κ a t * ‖u a‖)

/-- **The adjoint propagator in `H^j`, every duration, with a kernel.** The adjoint curves of
the same equation (the curves of `adjointCurve_exists`), read backward from `b`. The kernel is the
kernel of the forward equation. -/
def CellAdjointKernelHsStatement : Prop :=
  ∀ (j : ℕ) (ρ A : ℝ), 0 ≤ ρ → 1 ≤ A → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ κ : ℝ → ℝ → ℝ,
    IsFibreKernel ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb a b A κ →
  ∀ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b Ψv Ψs (fun r =>
      -cellDualDerivative (cellAdjointCoefficients ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩) hG V
        (cellDrift_neg hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) →
    (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = Ψv b → ∀ r ∈ Set.Icc a b,
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = Ψv r ∧
        ‖w‖ ≤ C * (1 + L) ^ Q * κ r b * ‖w₀‖) ∧
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ r ∈ Set.Icc a b, r + τ ≤ b →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = Ψv r ∧
        ‖w‖ ≤ C * (1 + L) ^ Q * τ ^ (-(j : ℝ) / 2) * κ r b * ‖Ψv b‖)

/-- **The plain kernel.** At a real frequency the constant `1` is a kernel (the `L²`
contraction, `cellDriftWeakContraction`). -/
def PlainKernelStatement : Prop :=
  ∀ (a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    IsFibreKernel ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb a b 1 (fun _ _ => 1)

/-- **The marks kernel** (from the package's `high_marks`, `marks_in`, `marks_sep`, `marks_count`,
`contraction`). On a complete block, at a real frequency of
the zone with `|ξ| ≥ ξ_lo` (`|θ| ≥ ξ_lo √η`), there is a kernel of the homogeneous fibre equation
which is at most `A e^{-cS}` over the block. -/
def MarksKernelStatement : Prop :=
  ∀ K : ScalarConstants, ∃ (A c : ℝ), 1 ≤ A ∧ 0 < c ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
  ∀ (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2),
    0 < η → η ≤ 1 → 1 ≤ S →
  ∀ θ : Vec 2, θ ∈ freqCube → K.ξlo * Real.sqrt η ≤ Real.sqrt (vecDot θ θ) →
    ∃ κ : ℝ → ℝ → ℝ,
      IsFibreKernel ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t₀ (t₀ + S) A κ ∧
      κ t₀ (t₀ + S) ≤ A * Real.exp (-c * S)

/-! ## The stage system at a frequency of the zone -/

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The scaled value of the stage `i` at time `t` and plane frequency `θ`:
`π_x^{-1/2} ϖ^{|β|}/β! A_j⁻¹ B_θ(y^β ⟨b, u_j x(t)⟩)`. -/
def stageScaled {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i : B1WIndex ι h Nw m Ks) (t : ℝ) : Vec 2 → ℂ :=
  fun y => b1wScale F.π F.ϖ F.ηg F.letters i * b1wStageVal F θ i t y

/-- `W` is a family of `L²` representatives of the scaled stage values at time `t`. -/
def IsScaledStage {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (t : ℝ)
    (W : B1WIndex ι h Nw m Ks → ComplexCellL2) : Prop :=
  ∀ i, (W i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i t

end Frame

/-- The cell Fourier coefficient `∫_cell f(z) e^{-2πi n·z} dz`. -/
def cellFourierCoeff (f : Vec 2 → ℂ) (n : Fin 2 → ℤ) : ℂ :=
  ∫ z in AVenhance.unitCube,
    f z * Complex.exp (-(2 * Real.pi * Complex.I * ((n 0 : ℂ) * (z 0 : ℂ) + (n 1 : ℂ) * (z 1 : ℂ))))

/-- The square of the `H^k` norm of the part of a Bloch fibre at the plane frequencies
`|2πn + θ| ≥ ρ`: `∑_{n : |2πn+θ| ≥ ρ} (1 + |2πn+θ|²)^k |f̂(n)|²`. `ρ = 0`: the whole fibre.
`ρ = π/4` and `θ` in the zone: every nonconstant mode, and the mean when `|θ| ≥ π/4`. -/
def cellBandSq (k : ℕ) (ρ : ℝ) (θ : Vec 2) (f : Vec 2 → ℂ) : ℝ≥0∞ :=
  ∑' n : Fin 2 → ℤ,
    if ρ ^ 2 ≤ vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) then
      ENNReal.ofReal ((1 + vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n)) ^ k *
        ‖cellFourierCoeff f n‖ ^ 2)
    else 0

section FrameSums

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- The squared `L²` norms of the scaled stage values at the start of the frame, summed over the
stages (only the level-`0` stages contribute: the datum's moments of order `≤ m + ∑K_i`). -/
def stageDatumSq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ) (Ks : Fin Nw → ℕ)
    (θ : Vec 2) : ℝ≥0∞ :=
  ∑ i : B1WIndex ι h Nw m Ks, ∫⁻ z in AVenhance.unitCube,
    ENNReal.ofReal (‖stageScaled F θ i F.a z‖ ^ 2)

/-- The band norms of the terminal stages (level `N_w`, moments `≤ m`) at the end of the frame. -/
def stageTerminalBandSq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ) (Ks : Fin Nw → ℕ)
    (k : ℕ) (ρ : ℝ) (θ : Vec 2) : ℝ≥0∞ :=
  ∑ i : B1WIndex ι h Nw m Ks,
    if i.1 = Fin.last Nw then cellBandSq k ρ θ (stageScaled F θ i F.b) else 0

/-- The squared cell means of the terminal stages at the end of the frame. -/
def stageTerminalMeanSq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ) (Ks : Fin Nw → ℕ)
    (θ : Vec 2) : ℝ≥0∞ :=
  ∑ i : B1WIndex ι h Nw m Ks,
    if i.1 = Fin.last Nw then
      ENNReal.ofReal (‖cellFourierCoeff (stageScaled F θ i F.b) 0‖ ^ 2) else 0

end FrameSums

/-- **The transform families at every frequency of the zone** (the transform bounds through
`b1w_family_provider`, with the hypothesis `|θ_k| ≤ ρ` in place of `|ξ| ≤ ρ`; the proofs of
the transform bounds use only `|θ_k| ≤ ρ`, `theta_abs_le`). -/
def StageFamilyZoneStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (s₀ : ℕ), (Finset.univ.sup d) + 3 ≤ s₀ →
  ∃ B : ℝ, 0 ≤ B ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    b1wLadderTop s₀ d Ks m + (Finset.univ.sup d) ≤ F.J →
    (∀ k, |θ k| ≤ ρ) →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k k' : ℕ), k' < k →
  ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
    ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
      (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
          ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wTestTransform F θ i i' r (fun y => star
              (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2

/-- **The plain pass** (the chain-level estimate, in tested form, at every time). On a frame
(a word chain on a piece from compactly supported data), at a real plane frequency of the zone and
for a kernel `κ` of the homogeneous fibre equation: at every time `t` the stages of order `k`,
tested against a family of `H^{s_k}` tests (`s_k` the ladder of the word fibre facts), are bounded by
`C P_e^Q (1 + (t - a))^Q κ(a, t)` times the `L²` norms of the stage values at the start.

For `N_w = 0` and moment `0` the bound is `|⟨𝒰_θ(t,a)f̂, ψ⟩| ≤ κ(a,t)‖f̂‖‖ψ‖` (the kernel itself).
For `t = a` it is Cauchy-Schwarz with `κ(a,a) = 1`. For a zero datum it reads `0 ≤ 0` (levels `≥ 1`
vanish at `a`). For one letter and `κ = 1`, `⟨u₁(t), ψ⟩ = ∫_a^t ⟨u₀(r), T Ψ(r)⟩ dr`, with
`‖TΨ(r)‖_{H^{s₀}} ≤ B C P_e^Q ‖ψ‖_{H^{s₁}}`, so the bound is `(t - a) B C P_e^Q`. The constants
`C, Q` are chosen after the shape, the ladder base and the comparison constant of the kernel, and
before the frame, the frequency, the kernel and the tests. -/
def PlainStageStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (s₀ : ℕ) (A : ℝ),
    (Finset.univ.sup d) + 3 ≤ s₀ → 1 ≤ A →
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    b1wLadderTop s₀ d Ks m + (Finset.univ.sup d) ≤ F.J →
    θ ∈ freqCube →
  ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (κ : ℝ → ℝ → ℝ),
    IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ →
  ∀ W₀ : B1WIndex ι h Nw m Ks → ComplexCellL2, IsScaledStage F θ F.a W₀ →
  ∀ t ∈ Icc F.a F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2, IsScaledStage F θ t W →
  ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
    ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
      C * peFactor F.η ^ Q * (1 + (t - F.a)) ^ Q * κ F.a t *
        Real.sqrt (∑ i, ‖W₀ i‖ ^ 2) * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)

/-! ## Positive orders on a terminal window -/

/-- **A forced fibre curve in `H^j` on a unit window.** If the tested forcing of a fibre
curve is represented at almost every time by an `H^j` element `σ(t)` with `‖σ(t)‖ ≤ f(t)`, and its
initial value is in `H^j`, then the curve stays in `H^j`, with
`‖w(t)‖ ≤ C(1+L)^Q (‖w₀‖ + ∫_a^t f)`.

For `σ = 0` this is clause (G) of the cell-equation regularity. For `v = 0`, `G = I` the heat
semigroup is a contraction of `H^j`, so `C = 1`. For `j = 0` it is the `L²` Duhamel bound of a
contraction. -/
def CellForcedHsStatement : Prop :=
  ∀ (j : ℕ) (ρ : ℝ), 0 ≤ ρ → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → b ≤ a + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (S : ℝ → ComplexCellL2)
    (F : ℝ → Fin 2 → ComplexCellL2),
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice t) (S t) (F t)) →
  ∀ (σ : ℝ → TorusHk j ℂ) (f : ℝ → ℝ), IntegrableOn f (Set.Icc a b) →
    (∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖σ t‖ ≤ f t ∧ ∀ z : TorusHk 1 ℂ,
      cellComplexSource (fun k => (θ k : ℂ)) (S t) (F t) z =
        cellComplexPair (torusHkValueCLM (σ t)) (torusHkValueCLM z)) →
  ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b,
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
      ‖w‖ ≤ C * (1 + L) ^ Q * (‖w₀‖ + ∫ r in a..t, f r)

/-- **Smoothing from a negative order.** A homogeneous fibre curve on a unit window whose
initial value is bounded against `H^s` tests by `M` is in `H^j` after a time `τ`, with norm at
most `C(1+L)^Q τ^{-(j+s)/2} M` (dual of the adjoint smoothing on the first half, forward
smoothing on the second half).

For `s = 0` this is clause (S) of the cell-equation regularity at a short time, with `M = ‖u(a)‖`.
For `v = 0`, `G = I` one has `‖e^{τΔ_θ}‖_{H^{-s} → H^j} ≤ C τ^{-(j+s)/2}` for `τ ≤ 1`. -/
def CellNegativeSmoothingStatement : Prop :=
  ∀ (j s : ℕ) (ρ : ℝ), 0 ≤ ρ → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → b ≤ a + 1 → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ j + s + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s' _ => G s', v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice t) 0 0) →
  ∀ M : ℝ, 0 ≤ M →
    (∀ ψ : TorusHk s ℂ, ‖cellComplexPair (u a) (torusHkValueCLM ψ)‖ ≤ M * ‖ψ‖) →
  ∀ τ : ℝ, 0 < τ → ∀ t ∈ Set.Icc a b, a + τ ≤ t →
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧
      ‖w‖ ≤ C * (1 + L) ^ Q * τ ^ (-((j + s : ℕ) : ℝ) / 2) * M

section PositiveLadder

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The positive ladder of the terminal window: `K_f + ∑_{l ≥ j} d_l + (n_j - |β|)`. A same-level
step to a lower moment gains one order, a letter step to the previous level gains `d_l`; its top
(level `0`, moment `0`) is `K_f + ∑d_i + m + ∑K_i ≤ K_*`. -/
def b1wPosLadder (Kf : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) : ℕ :=
  Kf + (∑ l : Fin Nw, if i.1.val ≤ l.val then d l else 0) +
    (b1wLevelMoments m Ks i.1 - (i.2.2.1.1.1 + i.2.2.1.1.2))

end PositiveLadder

/-- **The sources of a stage in positive order** (the transposed transforms of the transform
families). For almost every time of a frame, at a frequency of the zone: if the scaled values of the
stages of order `< k` are in `H^{n(i')}` (the positive ladder), the tested forcing of every stage
`i` of order `k` is represented by an `H^{n(i)}` element, with an `ℓ²` bound over the stage.

At level `0` with moment `0` the forcing is `0` and `σ = 0`. For a same-level term the flux is
`ϖ(G+Gᵀ)e_k` times the stage one moment lower, one derivative is lost and the ladder gives one.
For one letter of order `d` with coefficient `c(z)`, `σ = D_θ·(c D_θ^α X)` with `|α| ≤ d - 1`, and
`n(i') ≥ n(i) + d`. The constant `B` is chosen after the shape and `K_f`, and before the frame. -/
def StageSourceHsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m Kf : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ B : ℝ, 0 ≤ B ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveKstar Kf (wordReserveN m Ks) d + (Finset.univ.sup d) ≤ F.J →
    θ ∈ freqCube →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k : ℕ)
    (X : ∀ i' : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i') ℂ),
    (∀ i', b1wSt i' < k → (torusHkValueCLM (X i') : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i' r) →
  ∀ (S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2),
    (∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y) →
    (∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j) →
    ∃ σ : ∀ i : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i) ℂ,
      (∀ i ∈ stageSet b1wSt k, ∀ z : TorusHk 1 ℂ,
        cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) z =
          cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
      ∑ i ∈ stageSet b1wSt k, ‖σ i‖ ^ 2 ≤
        B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2

/-- **The full-field bound at the fibre level** (Lemma 11.12 of the paper). On a frame
of duration at least one, at every frequency of the zone, the terminal stages are in `H^{K_f}` of
the cell at the end of the frame, with norm at most `C P_e^Q (1 + (b - a))^Q` times the `L²` norms
of the stage values at the start.

For `N_w = 0` one has `‖𝒰_θ(b,a)f̂‖_{H^{K_f}} ≤ C P_e^Q ‖f̂‖` (contraction, then clause (S) of
the cell-equation regularity on the last unit of time), and the same for the moments, whose forcing is the lower
moments with the bounded coefficients `ϖ v`, `ϖ(G+Gᵀ)`. For a zero datum the bound reads `0 ≤ 0`.
For `K_f = 0`, `m = 0` and one letter it is the plain pass with the test of the terminal window.
The constants `C, Q` are chosen after the shape and `K_f`, and before the frame and the
frequency. -/
def FullFieldFibreStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ F.J →
    F.a + 1 ≤ F.b → θ ∈ freqCube →
    stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + (F.b - F.a)) ^ Q) ^ 2) * stageDatumSq F m Ks θ

/-! ## The two decays -/

/-- **The marks-band bound at the fibre level** (Lemma 11.12 of the paper). On a complete block,
at a
frequency of the zone with `|θ| ≥ ξ_lo √η`, the cell means of the terminal stages are at most
`C P_e^Q (1+S)^Q e^{-cS}` times the `L²` norms of the stage values at the start (the plain pass
with the marks kernel and the test `1`).

For `N_w = 0` and moment `0` one has `|⟨𝒰_θ f̂, 1⟩| ≤ κ(t₀, t₀+S)‖f̂‖ ≤ A e^{-cS}‖f̂‖`. For a
zero datum the bound reads `0 ≤ 0`, and for `S = 1` it is a constant. The constants `C, c, Q` are
chosen after the shape and before the block. -/
def MarksBandFibreStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ F.J →
    ScalarPackage K F.η F.G F.v F.t₀ F.Sw F.ϖ F.reg → F.a = F.t₀ → F.b = F.t₀ + F.Sw →
    1 ≤ F.Sw → θ ∈ freqCube → K.ξlo * Real.sqrt F.η ≤ Real.sqrt (vecDot θ θ) →
    stageTerminalMeanSq F m Ks θ ≤
      ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + F.Sw) ^ Q * Real.exp (-c * F.Sw)) ^ 2) *
        stageDatumSq F m Ks θ

/-- **The quiet high-band bound at the fibre level**. On a frame whose last stretch
`[b - D_q, b]`, `D_q ≥ 1`, is quiet (zero drift, quiet times of the regions, so the letters are
fast independent there), at every frequency of the zone the part of the terminal stages at the
plane frequencies `|2πn + θ| ≥ π/4` is in `H^{K_f}` of the cell at the end, with norm at most
`C P_e^Q (1 + (b - a))^Q e^{-c D_q}` times the `L²` norms of the stage values at the start.

For `N_w = 0`, moment `0` and `a = b - D_q`, each mode is multiplied by
`e^{-∫(2πn+θ)ᵀG(2πn+θ)}`, at most `e^{-|2πn+θ|²D_q/2}`, and `(1+y²)^{K_f}e^{-y²D_q} ≤ C e^{-cD_q}`
for `y ≥ π/4`, `D_q ≥ 1`. For a zero datum the bound reads `0 ≤ 0`. The constants `C, c, Q` are
chosen after the shape and `K_f`, and before the frame, the frequency and `D_q`. -/
def QuietHighFibreStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C c : ℝ) (Q : ℕ), 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ F.J →
    θ ∈ freqCube →
  ∀ Dq : ℝ, 1 ≤ Dq → F.a ≤ F.b - Dq → Icc (F.b - Dq) F.b ⊆ F.reg.quiet →
    (∀ t ∈ Icc (F.b - Dq) F.b, ∀ z, F.v t z = 0) →
    stageTerminalBandSq F m Ks Kf (Real.pi / 4) θ ≤
      ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + (F.b - F.a)) ^ Q * Real.exp (-c * Dq)) ^ 2) *
        stageDatumSq F m Ks θ

/-! ## From the fibres to the plane -/

/-- **The datum.** The stage values at the start of a frame, integrated over the zone, are
bounded by the moment norm of the datum (Parseval for the Bloch sums of a compactly supported
field, `lintegral_cube_parseval`, and `levelZeroData`). -/
def StageDatumStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (Ks : Fin Nw → ℕ), ∃ C : ℝ, 0 < C ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁),
    (∀ l, (F.letters l).slow = Ks l) →
    ∫⁻ θ in freqCube, stageDatumSq F m Ks θ ≤
      ENNReal.ofReal C * momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ ^ 2

section Output

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The fibre quantity of the output norm of a plane field `U` at the frequency `θ`: the band
norms of the Bloch parts of its moments of order `≤ m`, with the weights of `jetOutputNorm`. -/
def outBandSq (π : ι → ℝ) (ϖ : ℝ) (m k : ℕ) (ρ : ℝ) (θ : Vec 2) (U : ∀ x, Vec 2 → h x) :
    ℝ≥0∞ :=
  ∑ x, ∑ β ∈ momentIndices m, ∑ b : Fin (Module.finrank ℝ (h x)),
    ENNReal.ofReal ((π x)⁻¹ *
      (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
      cellBandSq k ρ θ (planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y)))

/-- The same with the cell means only. -/
def outMeanSq (π : ι → ℝ) (ϖ : ℝ) (m : ℕ) (θ : Vec 2) (U : ∀ x, Vec 2 → h x) : ℝ≥0∞ :=
  ∑ x, ∑ β ∈ momentIndices m, ∑ b : Fin (Module.finrank ℝ (h x)),
    ENNReal.ofReal ((π x)⁻¹ *
      (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 *
      ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y))) 0‖ ^ 2)

end Output

/-- **The output norm from the fibres**. For a plane field `U` with integrable
moments of order `≤ m` and a smooth compactly supported even multiplier `μ` equal to one on
`|θ| < ρ`: the molecular output norm of `U - μ(D)U` is at most `C` times the `L²` norm over the
zone of the band norms `|2πn + θ| ≥ ρ` of the Bloch parts of its moments. `μ = 0`, `ρ = 0`: the
output norm of `U` itself (`ChainFullFieldStatement`). `μ` the zone factor, `ρ = π/4`:
`QuietHighStatement`.

For `m = K_f = 0`, `μ = 0` this is Parseval for the Bloch transform,
`‖U‖₂² = (2π)⁻² ∫_zone ‖B_θ U‖²_{L²(cell)}`, and for `U = 0` it reads `0 ≤ 0`. The constant `C` is
chosen after the orders, `C_out`, `ρ` and the bound of the jets of `μ`, and before the field. -/
def BlochOutputStatement : Prop :=
  ∀ (Kf m : ℕ) (Cout ρ Bμ : ℝ), 0 < Cout → 0 ≤ ρ → 0 ≤ Bμ → ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (ϖ rstar : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 < rstar → rstar ≤ Cout →
  ∀ μ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ (l : ℕ) θ, l ≤ m + Kf → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) →
    (∀ θ, vecDot θ θ < ρ ^ 2 → μ θ = 1) →
  ∀ (κN : ι → ℕ), (∀ x, Kf ≤ κN x) → ∀ U : ∀ x, PlaneHk Set.univ (κN x) (h x),
    (∀ x, ∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (U x) y)) →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (U x) a wd z -
          orderedDerivative wd (fourierCutoff μ (planeValue (U x))) z) ≤
      ENNReal.ofReal C *
        (∫⁻ θ in freqCube, outBandSq π ϖ m Kf ρ θ (fun x => planeValue (U x))) ^ (1 / 2 : ℝ)

/-- **The output norm of a band part from the cell means.** For a smooth even multiplier
supported in `ρ₁ ≤ |θ| ≤ π/2` whose jets of order `l ≤ m` are at most `B_μ ϖ^{-l}`: the molecular
output norm of `μ(D)U` is at most `C B_μ` times the `L²` norm over the band of the cell means of
the Bloch parts of the moments of `U` (the plane Fourier transform of `U` and its `θ`-jets).

For `m = K_f = 0` one has `‖μ(D)U‖₂ ≤ sup|μ| (2π)⁻¹ ‖Û‖_{L²(band)}`. For the marks band,
`μ = b(θ)(1 - χ_lo(θ/√η))` has jets `≤ C η^{-l/2} ≤ C ϖ^{-l}`. The constant `C` is chosen after the
orders and `C_out`. -/
def BandOutputStatement : Prop :=
  ∀ (Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (ϖ rstar ρ₁ Bμ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 < rstar → rstar ≤ Cout → 0 ≤ ρ₁ → 0 ≤ Bμ →
  ∀ μ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ θ, μ θ ≠ 0 → ρ₁ ^ 2 ≤ vecDot θ θ ∧ vecDot θ θ ≤ (Real.pi / 2) ^ 2) →
    (∀ (l : ℕ) θ, l ≤ m → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ / ϖ ^ l) →
  ∀ U : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (U x) volume) →
    (∀ x, ∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • U x y)) →
    jetOutputNorm π m Kf ϖ rstar
        (fun x _ wd z => orderedDerivative wd (fourierCutoff μ (U x)) z) ≤
      ENNReal.ofReal (C * Bμ) *
        (∫⁻ θ in freqCube, if ρ₁ ^ 2 ≤ vecDot θ θ then outMeanSq π ϖ m θ U else 0) ^
          (1 / 2 : ℝ)

/-! ## Rough data -/

/-- **The full-field bound on compact data**: `ChainFullFieldStatement` for chains from smooth
compactly supported data. -/
def ChainFullFieldCompactStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H Kf m : ℕ) (Cout : ℝ), 0 < Cout → ∀ (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg rstar t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
    0 < rstar → rstar ≤ Cout →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) →
    IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsCompactDatum f →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z) ≤
      ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

/-- **Weak continuity of the endpoint on rough data** (smooth approximation in the input moment norm
and the common negative-space construction extend the endpoint to rough data). For every chain of a
block whose datum has `n` moments, the endpoint tested against a smooth compactly supported field is
bounded by the moment norm of the datum, with a constant that may depend on the block and the test.
The pairing of the letter flux of such a chain with a rapidly decaying test is integrable (the
Taylor factor is a polynomial), which is all the duality step needs; the flux itself need not be
square integrable.

For `N_w = 0` one has `|⟨𝒰f, Φ⟩| ≤ ‖f‖₂‖Φ‖₂`. For a zero datum the endpoint vanishes (uniqueness of
plane chains). The constant `C` is chosen after the block and the test, and before the chain. -/
def ChainWeakContinuityStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H Kf m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool)
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions), ScalarPackage K η G v t₀ S ϖ reg →
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg →
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J →
  ∀ (X₀ : Vec 2) (Φ : ∀ x, Vec 2 → h x),
    (∀ x, ContDiff ℝ (⊤ : ℕ∞) (Φ x) ∧ HasCompactSupport (Φ x)) →
  ∃ C : ℝ, 0 ≤ C ∧
  ∀ (κ : Fin (Nw + 1) → ι → ℕ), (∀ x, Kf ≤ κ (Fin.last Nw) x) → IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
    ENNReal.ofReal |∑ x, (π x)⁻¹ *
        ∫ z, inner ℝ (planeValue (u (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
      ENNReal.ofReal C * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))

/-! ## The assemblies (open; the dependency structure of the pieces)

Each assembly is an implication between the statements above; its proof may also use the proved
results (the amplitude identification, the stage expansion, the duality step
`afw_fast`, the adjoint curves, the cell-equation regularity, the quiet Fourier evolution, the density and the chain
combination). -/

/-- The plain pass from the transform families of the zone and the adjoint kernels. -/
def PlainStageAssembly : Prop :=
  StageFamilyZoneStatement.{u, v} → CellAdjointKernelHsStatement → PlainStageStatement.{u, v}

/-- The marks band at the fibre level: the plain pass with the marks kernel, tested against `1`. -/
def MarksBandFibreAssembly : Prop :=
  PlainStageStatement.{u, v} → MarksKernelStatement → MarksBandFibreStatement.{u, v}

/-- The quiet stretch at the fibre level: the plain pass at the entrance, then the stage system in
the cell Fourier modes (`quietFourier_evolution`), with the transform families on mode tests. -/
def QuietHighFibreAssembly : Prop :=
  PlainStageStatement.{u, v} → PlainKernelStatement → StageFamilyZoneStatement.{u, v} →
    QuietHighFibreStatement.{u, v}

/-- The full-field bound at the fibre level: the plain pass up to the terminal window, then the
positive ladder on nested windows of the last unit of time. -/
def FullFieldFibreAssembly : Prop :=
  PlainStageStatement.{u, v} → PlainKernelStatement → StageFamilyZoneStatement.{u, v} →
    CellKernelHsStatement → CellAdjointKernelHsStatement → CellForcedHsStatement →
    CellNegativeSmoothingStatement → StageSourceHsStatement.{u, v} →
    FullFieldFibreStatement.{u, v}

/-- The full-field bound on compact data from the fibres. -/
def ChainFullFieldCompactAssembly : Prop :=
  FullFieldFibreStatement.{u, v} → BlochOutputStatement.{u, v} → StageDatumStatement.{u, v} →
    ChainFullFieldCompactStatement.{u, v}

/-- The full-field bound on rough data: compact approximants, weak continuity, and the lower
semicontinuity of the output norm. -/
def ChainFullFieldAssembly : Prop :=
  ChainFullFieldCompactStatement.{u, v} → ChainWeakContinuityStatement.{u, v} →
    ChainFullFieldStatement.{u, v}

/-- `QuietHighStatement` from the fibres: the quiet decay when the buffer is at least two (with
`D_q` half the buffer), the full-field bound at the fibre level otherwise. -/
def QuietHighAssembly : Prop :=
  QuietHighFibreStatement.{u, v} → FullFieldFibreStatement.{u, v} →
    BlochOutputStatement.{u, v} → StageDatumStatement.{u, v} → QuietHighStatement.{u, v}

/-- `MarksBandStatement` from the fibres. -/
def MarksBandAssembly : Prop :=
  MarksBandFibreStatement.{u, v} → BandOutputStatement.{u, v} → StageDatumStatement.{u, v} →
    MarksBandStatement.{u, v}

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # adjoint curves, reflection in both directions, and the adjoint decay by duality

* `curve_congr_coeff`: a homogeneous curve for equal coefficients.
* `reflect_adjoint_conv`: the converse of `CellWeakHilbertCurve.reflected_adjoint`: an adjoint
  curve `Ψ` gives the forward curve `t ↦ conj Ψ(-t)` of the reversed equation.
* `adjoint_decay`: if the forward curves decay with `κ`, the adjoint curves decay backward
  with the same `κ` (pairing with a forward curve started at `Ψ r`). -/

theorem curve_congr_coeff {C₁ C₂ : CellCoefficients} (e : C₁ = C₂)
    (hG₁ : IsCellMetric C₁.G) (hG₂ : IsCellMetric C₂.G) (V : ℝ)
    (hv₁ : Measurable (fun p : ℝ × Vec 2 => C₁.v p.1 p.2))
    (hv₂ : Measurable (fun p : ℝ × Vec 2 => C₂.v p.1 p.2))
    (hb₁ : ∀ t x, ∑ i, C₁.v t x i ^ 2 ≤ V ^ 2) (hb₂ : ∀ t x, ∑ i, C₂.v t x i ^ 2 ≤ V ^ 2)
    {p q : ℝ} {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve p q u slice
      (fun t => cellDualDerivative C₁ hG₁ V hv₁ hb₁ t (slice t) 0 0)) :
    CellWeakHilbertCurve p q u slice
      (fun t => cellDualDerivative C₂ hG₂ V hv₂ hb₂ t (slice t) 0 0) := by
  subst e
  exact h

/-- The converse of `CellWeakHilbertCurve.reflected_adjoint`. -/
theorem reflect_adjoint_conv {a b : ℝ}
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ)
    {Ψ : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b Ψ slice (fun r =>
      -cellDualDerivative (cellAdjointCoefficients ⟨G, v, θ, 0⟩) hG V
        (cellDrift_neg hv).1 (cellDrift_neg_bound hb) r (slice r) 0 0)) :
    CellWeakHilbertCurve (-b) (-a)
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (Ψ (-t)))
      (fun t => cellH1Conj (slice (-t)))
      (fun t => cellDualDerivative ⟨fun s x => G (-s) x, fun s x => -v (-s) x,
        fun j => -θ j, 0⟩ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t
        (cellH1Conj (slice (-t))) 0 0) := by
  let Ca : CellCoefficients := cellAdjointCoefficients ⟨G, v, θ, 0⟩
  have hGa : IsCellMetric Ca.G := hG
  have hva := (cellDrift_neg hv).1
  have hba := cellDrift_neg_bound hb
  have h1 := h.timeReverse
  have h2 : CellWeakHilbertCurve (-b) (-a) (fun t => Ψ (-t)) (fun t => slice (-t))
      (fun t => cellDualDerivative (cellReverseTimeCoefficients Ca) (cellMetric_timeReverse hGa) V
        (hva.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
        (fun s x => hba (-s) x) t (slice (-t)) 0 0) := by
    apply h1.dual_congr
    exact Filter.Eventually.of_forall (fun t => by
      beta_reduce
      rw [neg_neg]
      exact (cellDualDerivative_reverse_time Ca hGa V hva hba t (slice (-t)) 0 0).symm)
  have h3 := h2.conjugate_homogeneous (cellReverseTimeCoefficients Ca) (cellMetric_timeReverse hGa)
    V (hva.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
    (fun s x => hba (-s) x)
  refine curve_congr_coeff ?_ _ _ V _ _ _ _ h3
  simp only [Ca, cellReverseTimeCoefficients, cellConjugateCoefficients, cellAdjointCoefficients,
    star_star]
  rfl

/-- **Adjoint decay by duality.** -/
theorem adjoint_decay {r s : ℝ} (hrs : r ≤ s) (C : CellCoefficients)
    (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ0 : C.κ = 0) (κ : ℝ) (hκ : 0 ≤ κ)
    (hdec : ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve r s u slice
        (fun t => cellDualDerivative C hG V hv.1 hb t (slice t) 0 0) → ‖u s‖ ≤ κ * ‖u r‖)
    {Ψ : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hΨ : CellWeakHilbertCurve r s Ψ slice (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (slice t) 0 0)) :
    ‖Ψ r‖ ≤ κ * ‖Ψ s‖ := by
  obtain ⟨u, us, hu, hu0⟩ := cellActual_exists_Hilbert hrs C hG V 0 hv.1 hb
    (hκ0 ▸ measurable_const) (fun _ => by simp [hκ0]) (fun _ _ => 0) (fun _ _ => 0)
    measurable_const measurable_const (by simp [cellL2Norm]) (by simp [cellL2Norm]) (Ψ r)
  have hu' : CellWeakHilbertCurve r s u us (fun t =>
      cellDualDerivative C hG V hv.1 hb t (us t) 0 0) := by
    simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
      show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hu
  have hpair := cellWeakAdjointPairing_forced hrs C hG V hv hb (S := fun _ => 0)
    (F := fun _ => 0) hu' hΨ
  have hz : ∀ t, cellComplexSource C.θ 0 0 (slice t) = 0 := fun t =>
    cellComplexSource_zero C.θ (slice t)
  simp only [hz, intervalIntegral.integral_zero] at hpair
  rw [hu0] at hpair
  have hself : cellComplexPair (Ψ r) (Ψ r) = ((‖Ψ r‖ ^ 2 : ℝ) : ℂ) := by
    rw [cellComplexPair_eq_inner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h1 : ‖Ψ r‖ ^ 2 ≤ ‖u s‖ * ‖Ψ s‖ := by
    have := cellComplexPair_norm_le (u s) (Ψ s)
    have h2 : cellComplexPair (u s) (Ψ s) = ((‖Ψ r‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hself]; linear_combination hpair
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at this
    exact this
  have h3 := hdec u us hu'
  rw [hu0] at h3
  rcases (norm_nonneg (Ψ r)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have h4 : ‖Ψ r‖ ^ 2 ≤ (κ * ‖Ψ s‖) * ‖Ψ r‖ := by
      calc ‖Ψ r‖ ^ 2 ≤ ‖u s‖ * ‖Ψ s‖ := h1
        _ ≤ (κ * ‖Ψ r‖) * ‖Ψ s‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = (κ * ‖Ψ s‖) * ‖Ψ r‖ := by ring
    nlinarith

end AVRegularity.CycleWords.Discard
end

section
open Homogenization
namespace AVRegularity.CycleWords.Discard

/-! # the two elementary inequalities for the shifted weights `(1 + |2πn + θ|²)^k`

For `|θ_i| ≤ π`: `(1 + |2πn + θ|²)^k ≤ c^k · 2^k · ∑_{a ≤ k} |2πn|^{2a}` with `c = 1 + 4π²`. -/

/-- `(1 + t)^k ≤ 2^k ∑_{a ≤ k} t^a` for `t ≥ 0`. -/
theorem one_add_pow_le' (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    (1 + t) ^ k ≤ 2 ^ k * ∑ a ∈ Finset.range (k + 1), t ^ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hS : ∑ a ∈ Finset.range (k + 2), t ^ a = 1 + t * ∑ a ∈ Finset.range (k + 1), t ^ a := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ', pow_zero]
      ring
    have hSk : 0 ≤ ∑ a ∈ Finset.range (k + 1), t ^ a :=
      Finset.sum_nonneg (fun a _ => pow_nonneg ht a)
    have hle : ∑ a ∈ Finset.range (k + 1), t ^ a ≤ ∑ a ∈ Finset.range (k + 2), t ^ a :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro x hx; simp at hx ⊢; omega)
        (fun a _ _ => pow_nonneg ht a)
    have h2 : (1 + t) * ∑ a ∈ Finset.range (k + 1), t ^ a ≤
        2 * ∑ a ∈ Finset.range (k + 2), t ^ a := by
      rw [hS] at hle ⊢
      nlinarith
    calc (1 + t) ^ (k + 1) = (1 + t) * (1 + t) ^ k := by ring
      _ ≤ (1 + t) * (2 ^ k * ∑ a ∈ Finset.range (k + 1), t ^ a) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = 2 ^ k * ((1 + t) * ∑ a ∈ Finset.range (k + 1), t ^ a) := by ring
      _ ≤ 2 ^ k * (2 * ∑ a ∈ Finset.range (k + 2), t ^ a) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (k + 1) * ∑ a ∈ Finset.range (k + 2), t ^ a := by ring

/-- The shifted square `|2πn + θ|²` is at most `1 + 4π²` times `1 + |2πn|²` (minus one). -/
theorem shift_le (n : Fin 2 → ℤ) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi) :
    1 + (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ≤
      (1 + 4 * Real.pi ^ 2) * (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) := by
  have h : ∀ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2 ≤
      2 * (2 * Real.pi * (n i : ℝ)) ^ 2 + 2 * Real.pi ^ 2 := by
    intro i
    have h1 : θ i ^ 2 ≤ Real.pi ^ 2 := by
      have := sq_le_sq' (by linarith [abs_le.mp (hθ i)]) (abs_le.mp (hθ i)).2
      simpa using this
    nlinarith [sq_nonneg (2 * Real.pi * (n i : ℝ) - θ i)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hQ : 0 ≤ ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0 < Real.pi ^ 2 := by positivity
  push_cast at hs
  have h1 : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [mul_le_mul_of_nonneg_right h1 hQ]

/-- Combined: `(1 + |2πn+θ|²)^k ≤ (1+4π²)^k 2^k ∑_{a ≤ k} |2πn|^{2a}`. -/
theorem weight_le'' (k : ℕ) (n : Fin 2 → ℤ) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi) :
    (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k ≤
      ((1 + 4 * Real.pi ^ 2) * 2) ^ k *
        ∑ a ∈ Finset.range (k + 1), (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a := by
  have hQ : 0 ≤ ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc : 0 ≤ 1 + 4 * Real.pi ^ 2 := by positivity
  calc _ ≤ ((1 + 4 * Real.pi ^ 2) * (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2)) ^ k :=
        pow_le_pow_left₀ (by positivity) (shift_le n θ hθ) k
    _ = (1 + 4 * Real.pi ^ 2) ^ k * (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ k :=
        mul_pow _ _ _
    _ ≤ (1 + 4 * Real.pi ^ 2) ^ k * (2 ^ k * ∑ a ∈ Finset.range (k + 1),
          (∑ i : Fin 2, (2 * Real.pi * (n i : ℝ)) ^ 2) ^ a) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le' _ hQ k) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # The Bloch output: the two lemmas

`BlochOutputStatement` is reduced to two statements:

* `BridgeStatement`: the plane integral of the band integrand of a transform equals the
  integral over the zone of the band norms of the Bloch parts (tiling of the plane by the lattice
  translates `2πn + zone` and `cellFourierCoeff (planeBlochC θ g) n = ĝ(2πn + θ)`).
* `PlaneStatement`: Plancherel on the plane for `y^β ∂^w (U − μ(D)U)`, by components, with the
  moments of `U` of order `≤ m` only integrable: the weighted `L²` norm of each jet of the
  difference is at most `C` times the band integrand of the transforms of the moments `y^{β'} U`,
  `β' ≤ β`.

For `PlaneStatement` with `m = Kf = 0`, `μ = 0`, the bound is `‖U‖₂² ≤ C ∫ |Û|²` (Plancherel, with
`C = (2π)⁻²`); for `U = 0` it reads `0 ≤ 0`; the left side is `∞` only when the right side is.
-/

universe u v

/-- The plane transform `ĝ(ξ) = ∫ e^{-iξ·y} g(y) dy` (radian convention) of a real function. -/
def planeTransform (g : Vec 2 → ℝ) (ξ : Vec 2) : ℂ :=
  ∫ y, Complex.exp (-(Complex.I * (vecDot ξ y : ℂ))) * (g y : ℂ)

/-- The band integrand `1_{|ξ| ≥ ρ} (1 + |ξ|²)^k |ĝ(ξ)|²`. -/
def BandIntegrand (k : ℕ) (ρ : ℝ) (g : Vec 2 → ℝ) (ξ : Vec 2) : ℝ≥0∞ :=
  if ρ ^ 2 ≤ vecDot ξ ξ then ENNReal.ofReal ((1 + vecDot ξ ξ) ^ k * ‖planeTransform g ξ‖ ^ 2) else 0

/-- **The bridge** from the plane to the fibres. -/
def BridgeStatement : Prop :=
  ∀ (k : ℕ) (ρ : ℝ) (g : Vec 2 → ℝ), Integrable g →
    ∫⁻ θ in freqCube, cellBandSq k ρ θ (planeBlochC θ g) = ∫⁻ ξ, BandIntegrand k ρ g ξ

/-- **Plancherel with moments** for the jets of `U − μ(D)U`. -/
def PlaneStatement : Prop :=
  ∀ (Kf m : ℕ) (ρ Bμ : ℝ), 0 ≤ ρ → 0 ≤ Bμ → ∃ C : ℝ, 0 < C ∧
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ (l : ℕ) θ, l ≤ m + Kf → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) →
    (∀ θ, vecDot θ θ < ρ ^ 2 → μ θ = 1) →
  ∀ (κ : ℕ), Kf ≤ κ → ∀ U : PlaneHk Set.univ κ E,
    (∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue U y)) →
  ∀ β ∈ momentIndices m, ∀ a ≤ Kf,
    ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * ∑ w : DerivativeWord2 a,
        ‖planeJetOrder U a w z - orderedDerivative w (fourierCutoff μ (planeValue U)) z‖ ^ 2) ≤
      ENNReal.ofReal C *
        ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2),
          ∑ b : Fin (Module.finrank ℝ E),
            ∫⁻ ξ, BandIntegrand Kf ρ
              (fun y => momentWeight β' y * inner ℝ (stdOrthonormalBasis ℝ E b) (planeValue U y)) ξ

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard.BandJets

/-! # moment pairs against cell means

For a plane field with integrable moments the squared moment amplitude pair
`‖∫ cos(θ·y) y^β g‖² + ‖∫ sin(θ·y) y^β g‖²` is the sum over an orthonormal basis of the squared
cell means `|ĝ_b(θ)|²` of the Bloch parts of the coordinates `y^β ⟨e_b, g⟩`
(`integral_phase_mul_eq_cell_planeBlochC`). Hence `momentAmpNorm ≤ β! · outMeanSq^{1/2}`. -/

/-- A bounded measurable multiplier keeps integrability. -/
theorem integrable_mul_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Vec 2 → E} (hg : Integrable g) {f : Vec 2 → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) : Integrable (fun y => f y • g y) := by
  refine (hg.norm.const_mul C).mono' (hf.aestronglyMeasurable.smul hg.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)

theorem cos_continuous (θ : Vec 2) : Continuous fun y : Vec 2 => Real.cos (vecDot θ y) :=
  Real.continuous_cos.comp (by unfold vecDot; fun_prop)

theorem sin_continuous (θ : Vec 2) : Continuous fun y : Vec 2 => Real.sin (vecDot θ y) :=
  Real.continuous_sin.comp (by unfold vecDot; fun_prop)

/-- The zero cell mode of the Bloch part of a real integrable `g` is the plane Fourier transform:
its squared modulus is the sum of the squares of the cosine and sine transforms. -/
theorem cellCoeff_sq {g : Vec 2 → ℝ} (hg : Integrable g) (θ : Vec 2) :
    ‖cellFourierCoeff (planeBlochC θ g) 0‖ ^ 2 =
      (∫ y, Real.cos (vecDot θ y) * g y) ^ 2 + (∫ y, Real.sin (vecDot θ y) * g y) ^ 2 := by
  have hper : AVenhance.IsZ2Periodic (fun _ : Vec 2 => (1 : ℂ)) := fun _ _ => rfl
  have h1 := integral_phase_mul_eq_cell_planeBlochC θ hg (φ := fun _ => (1 : ℂ))
    aestronglyMeasurable_const (B := 1) (fun _ => by simp) hper
  have hc : cellFourierCoeff (planeBlochC θ g) 0 =
      ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) := by
    simp only [mul_one] at h1
    rw [h1]
    unfold cellFourierCoeff
    simp
  have hci : Integrable fun y => Real.cos (vecDot θ y) * g y := by
    simpa using integrable_mul_bdd hg (cos_continuous θ) (C := 1)
      (fun y => Real.abs_cos_le_one _)
  have hsi : Integrable fun y => Real.sin (vecDot θ y) * g y := by
    simpa using integrable_mul_bdd hg (sin_continuous θ) (C := 1)
      (fun y => Real.abs_sin_le_one _)
  have hexp : ∀ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) =
      ((Real.cos (vecDot θ y) * g y : ℝ) : ℂ) - Complex.I * ((Real.sin (vecDot θ y) * g y : ℝ) : ℂ) := by
    intro y
    rw [show -(Complex.I * (vecDot θ y : ℂ)) = ((-vecDot θ y : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hc]
  simp only [hexp]
  have hI1 : Integrable (fun y => ((Real.cos (vecDot θ y) * g y : ℝ) : ℂ)) := hci.ofReal
  have hI2 : Integrable (fun y => Complex.I * ((Real.sin (vecDot θ y) * g y : ℝ) : ℂ)) :=
    hsi.ofReal.const_mul _
  rw [integral_sub hI1 hI2, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring


universe u v

section Vec

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [CompleteSpace H]

/-- The squared norm of an integral is the sum over an orthonormal basis of the squared
integrals of the coordinates. -/
theorem vec_norm_sq {F : Vec 2 → H} (hF : Integrable F) :
    ‖∫ y, F y‖ ^ 2 = ∑ b, (∫ y, inner ℝ (stdOrthonormalBasis ℝ H b) (F y)) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ H).sum_sq_norm_inner_right (∫ y, F y)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_inner hF, Real.norm_eq_abs, sq_abs]

/-- The moment pair of a vector field is the sum of the squared cell means of its coordinates. -/
theorem vec_pair_sq {V : Vec 2 → H} (β : ℕ × ℕ)
    (hV : Integrable (fun y => momentWeight β y • V y)) (ϖ : ℝ) (θ : Vec 2) :
    ‖∫ y, (Real.cos (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • V y‖ ^ 2 +
      ‖∫ y, (Real.sin (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • V y‖ ^ 2 =
    (ϖ ^ (β.1 + β.2)) ^ 2 * ∑ b : Fin (Module.finrank ℝ H),
      ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ H b) (V y))) 0‖ ^ 2 := by
  have hg : ∀ b, Integrable (fun y => momentWeight β y *
      inner ℝ (stdOrthonormalBasis ℝ H b) (V y)) := by
    intro b
    have := (innerSL ℝ (stdOrthonormalBasis ℝ H b)).integrable_comp hV
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [innerSL_apply_apply]
  have hrew : ∀ (ψ : ℝ → ℝ) (y : Vec 2), (ψ (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • V y =
      (ϖ ^ (β.1 + β.2) * ψ (vecDot θ y)) • (momentWeight β y • V y) := by
    intro ψ y
    rw [smul_smul]
    congr 1
    unfold momentWeight
    rw [pow_add]
    ring
  have key : ∀ (ψ : ℝ → ℝ) (hψc : Continuous fun y : Vec 2 => ψ (vecDot θ y))
      (hψb : ∀ z, |ψ z| ≤ 1),
      ‖∫ y, (ψ (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • V y‖ ^ 2 =
        (ϖ ^ (β.1 + β.2)) ^ 2 * ∑ b, (∫ y, ψ (vecDot θ y) * (momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ H b) (V y))) ^ 2 := by
    intro ψ hψc hψb
    have hint : Integrable fun y => (ϖ ^ (β.1 + β.2) * ψ (vecDot θ y)) •
        (momentWeight β y • V y) :=
      integrable_mul_bdd hV (continuous_const.mul hψc) (C := |ϖ ^ (β.1 + β.2)|) (fun y => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hψb _))
    simp only [hrew]
    rw [vec_norm_sq hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ y, inner ℝ (stdOrthonormalBasis ℝ H b)
        ((ϖ ^ (β.1 + β.2) * ψ (vecDot θ y)) • (momentWeight β y • V y)) =
        ϖ ^ (β.1 + β.2) * (ψ (vecDot θ y) * (momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ H b) (V y))) := by
      intro y
      rw [real_inner_smul_right, real_inner_smul_right]
      ring
    simp only [this, integral_const_mul]
    ring
  rw [key Real.cos (cos_continuous θ) Real.abs_cos_le_one,
    key Real.sin (sin_continuous θ) Real.abs_sin_le_one, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cellCoeff_sq (hg b) θ]

end Vec

section Family

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The moment pair is a cell-mean term.** For `β ∈ momentIndices m`, the moment amplitude norm
is at most `β! · outMeanSq^{1/2}`. -/
theorem momentAmp_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (ϖ : ℝ) {m : ℕ} {β : ℕ × ℕ}
    (hβ : β ∈ momentIndices m) (θ : Vec 2) (U : ∀ x, Vec 2 → h x)
    (hint : ∀ x, ∀ γ ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ γ.1 * y 1 ^ γ.2) • U x y)) :
    momentAmpNorm π ϖ β U θ ≤
      ENNReal.ofReal ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * (outMeanSq π ϖ m θ U) ^ (1 / 2 : ℝ) := by
  set f : ℝ := ((β.1.factorial * β.2.factorial : ℕ) : ℝ) with hf
  have hfpos : 0 < f := by rw [hf]; positivity
  have hx : ∀ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal (‖∫ y, (Real.cos (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • U x y‖ ^ 2) +
        ENNReal.ofReal (‖∫ y, (Real.sin (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • U x y‖ ^ 2)) =
      ENNReal.ofReal (f ^ 2) * ∑ b : Fin (Module.finrank ℝ (h x)),
        ENNReal.ofReal ((π x)⁻¹ * (ϖ ^ (β.1 + β.2) / f) ^ 2 *
          ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β y *
            inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y))) 0‖ ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (inv_nonneg.2 (hπ x).le),
      vec_pair_sq β (hint x β hβ) ϖ θ,
      ← ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (mul_nonneg (inv_nonneg.2 (hπ x).le) (sq_nonneg _)) (sq_nonneg _)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  have hsum : ∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal (‖∫ y, (Real.cos (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • U x y‖ ^ 2) +
        ENNReal.ofReal (‖∫ y, (Real.sin (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • U x y‖ ^ 2)) ≤
      ENNReal.ofReal (f ^ 2) * outMeanSq π ϖ m θ U := by
    simp only [hx]
    rw [← Finset.mul_sum]
    refine mul_le_mul' le_rfl ?_
    unfold outMeanSq
    refine Finset.sum_le_sum fun x _ => ?_
    exact Finset.single_le_sum (f := fun β' : ℕ × ℕ => ∑ b : Fin (Module.finrank ℝ (h x)),
      ENNReal.ofReal ((π x)⁻¹ * (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2 *
        ‖cellFourierCoeff (planeBlochC θ (fun y => momentWeight β' y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y))) 0‖ ^ 2))
      (fun _ _ => zero_le) hβ
  unfold momentAmpNorm
  refine (ENNReal.rpow_le_rpow hsum (by norm_num)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hfpos.le, sq_rpow_half]

end Family

end AVRegularity.CycleWords.Discard.BandJets
end
