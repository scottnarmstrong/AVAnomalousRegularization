-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.NativeCoupledFluxLinearReadouts
public import AVRegularity.CycleWords.SlowTaylorTimeCoefficient
import AVRegularity.CycleWords.PeriodicClassicalLiftReadout
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TaylorIntegral

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Fixed boundedness estimates for actual cell H1 frequency readouts. -/

theorem centeredCellBlochValueField_norm_le
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ‖centeredCellBlochValueField u‖ ≤ ‖cellComplexH1ValueCLM‖ * ‖u‖ :=
  cellComplexH1ValueCLM.norm_compLp_le u

theorem centeredCellBlochGradientField_norm_le
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    ‖centeredCellBlochGradientField u i‖ ≤
      (‖cellComplexH1DerivativeCLM i‖ + 2 * Real.pi * ‖cellComplexH1ValueCLM‖) * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(centeredCellBlochGradient_memLp u i).coeFn_toLp,
    centeredPhysicalBlochPhase_norm_le i] with θ hθ hp
  change centeredCellBlochGradientField u i θ =
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv (u θ)) at hθ
  rw [hθ]
  change ‖cellComplexH1DerivativeCLM i (u θ) +
    (Complex.I * planePhysicalBlochShift θ i) • cellComplexH1ValueCLM (u θ)‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hd := (cellComplexH1DerivativeCLM i).le_opNorm (u θ)
  have hv := cellComplexH1ValueCLM.le_opNorm (u θ)
  have hphase := mul_le_mul hp hv (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.pi)
  calc
    _ ≤ ‖cellComplexH1DerivativeCLM i‖ * ‖u θ‖ +
        (2 * Real.pi) * (‖cellComplexH1ValueCLM‖ * ‖u θ‖) := add_le_add hd hphase
    _ = _ := by ring

theorem centeredCellBlochTorusValue_norm_le
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ‖centeredCellBlochTorusValue u‖ ≤ ‖cellComplexH1ValueCLM‖ * ‖u‖ := by
  rw [centeredCellBlochTorusValue, (scalarCellToTorusField centeredPlaneFrequencyMeasure).norm_map]
  exact centeredCellBlochValueField_norm_le u

theorem centeredCellBlochTorusGradient_norm_le
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    ‖centeredCellBlochTorusGradient u i‖ ≤
      (‖cellComplexH1DerivativeCLM i‖ + 2 * Real.pi * ‖cellComplexH1ValueCLM‖) * ‖u‖ := by
  rw [centeredCellBlochTorusGradient,
    (scalarCellToTorusField centeredPlaneFrequencyMeasure).norm_map]
  exact centeredCellBlochGradientField_norm_le u i

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Normalized molecular rows produce a linear inverse mass density estimate,
with their original row prices and polynomial moment growth retained. -/

variable {ι : Type*} [Fintype ι] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeFlux_normalized_row_density_budget {K : ℕ}
    (ρ : ℝ) (V : ι → PlaneHk Set.univ K E)
    (π : ι → ℝ) (hπ : ∀ u, 0 < π u) (v : ι)
    (p : ι → ℝ) (hp : ∀ u, 0 ≤ p u) (θ : ℝ)
    (hrow : (∑ u, Real.sqrt (π u / π v) * p u) ≤ θ)
    (w : Vec 2 → ℝ) (hw : ∀ x, 0 ≤ w x)
    (G : ι → Vec 2 → ℝ) (hG : ∀ u x, 0 ≤ G u x)
    (hb : ∀ u, ∀ᵐ x ∂volume, planeFactorialDensity ρ (V u) x ≤
      (p u) ^ 2 * (w x * G u x)) :
    ∀ᵐ x ∂volume, (π v)⁻¹ * planeFactorialDensity ρ (∑ u, V u) x ≤
      θ * w x * ∑ u, (Real.sqrt (π u / π v) * p u) * ((π u)⁻¹ * G u x) := by
  filter_upwards [nativeFactorialDensity_sum_variable_price_le ρ V p hp
    (fun u x => w x * G u x) (fun u x => mul_nonneg (hw x) (hG u x)) hb] with x hx
  have hh := finite_mass_row_square_le π hπ v p hp θ hrow
    (fun u => w x * G u x) (fun u => mul_nonneg (hw x) (hG u x))
    (planeFactorialDensity ρ (∑ u, V u) x) hx
  have he : (∑ u, (Real.sqrt (π u / π v) * p u) * ((π u)⁻¹ * (w x * G u x))) =
      w x * ∑ u, (Real.sqrt (π u / π v) * p u) * ((π u)⁻¹ * G u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he] at hh
  simpa only [mul_assoc] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology Pointwise
namespace AVRegularity.CycleWords

/-! Compact smooth approximation converges strongly in every continuously weighted stored jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_compact_smooth_weighted_jet_approximation {K : ℕ} (U : PlaneHk Set.univ K E)
    (A : Set (Vec 2)) (hA : IsCompact A)
    (hu : ∀ᵐ x ∂volume, x ∉ A → planeValue U x = 0)
    (q : Vec 2 → ℝ) (hq : Continuous q) :
    ∃ UN : ℕ → PlaneHk Set.univ K E, ∃ fN : ℕ → Vec 2 → E,
      Tendsto UN atTop (𝓝 U) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n) ∧ HasCompactSupport (fN n)) ∧
      (∀ n, planeValue (UN n) =ᵐ[volume] fN n) ∧
      ∀ a : JetIndex2 K,
        ∃ hmem : ∀ n, MemLp (fun x => q x • (UN n).toFunction.jet a x) 2 volume,
        ∃ hU : MemLp (fun x => q x • U.toFunction.jet a x) 2 volume,
          Tendsto (fun n => (hmem n).toLp (fun x => q x • (UN n).toFunction.jet a x))
            atTop (𝓝 (hU.toLp (fun x => q x • U.toFunction.jet a x))) := by
  obtain ⟨UN, fN, ht, hd, hc, hv, hs⟩ := exists_compact_smooth_planeHk_approximation U A hA hu
  let B := A + Metric.closedBall (0 : Vec 2) 2
  have hB : IsCompact B := hA.add (isCompact_closedBall _ _)
  have hAB : A ⊆ B := by
    intro x hx
    exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  have hUN (n : ℕ) : ∀ᵐ x ∂volume, x ∉ B → planeValue (UN n) x = 0 := by
    filter_upwards [hv n] with x hx
    intro hout
    rw [hx]
    by_contra hn
    exact hout (hs n hn)
  have hU0 : ∀ᵐ x ∂volume, x ∉ B → planeValue U x = 0 := by
    filter_upwards [hu] with x hx
    intro hout
    exact hx (fun ha => hout (hAB ha))
  refine ⟨UN, fN, ht, fun n => ⟨hd n, hc n⟩, hv, ?_⟩
  intro a
  obtain ⟨W, hw⟩ := exists_compactWeightedJetReadout (E := E) K a B hB q hq
  have hm (n : ℕ) : MemLp (fun x => q x • (UN n).toFunction.jet a x) 2 volume :=
    (Lp.memLp (W (UN n))).ae_eq (hw (UN n) (hUN n))
  have hm0 : MemLp (fun x => q x • U.toFunction.jet a x) 2 volume :=
    (Lp.memLp (W U)).ae_eq (hw U hU0)
  have he (n : ℕ) : (hm n).toLp (fun x => q x • (UN n).toFunction.jet a x) = W (UN n) := by
    apply Lp.ext
    exact ((hm n).coeFn_toLp).trans (hw (UN n) (hUN n)).symm
  have he0 : hm0.toLp (fun x => q x • U.toFunction.jet a x) = W U := by
    apply Lp.ext
    exact hm0.coeFn_toLp.trans (hw U hU0).symm
  refine ⟨hm, hm0, ?_⟩
  simp only [he, he0]
  exact (W.continuous.tendsto U).comp ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native frequency readouts of the actual cell generator at a fixed time. -/

def cellFrequencyMetricField (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i j : Fin 2) :
    Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure :=
  (cellScalarCLM (G t i j : ℂ)).compLp (centeredCellBlochGradientField u i)

def cellFrequencyDriftField (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure :=
  (cellDriftEntryCLM ⟨fun t _ => G t, v, 0, 0⟩ V hv hb t i).compLp
    (centeredCellBlochGradientField u i)

theorem cellFrequencyGenerator_readout_ae
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u z : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb t
        (cellComplexH1RealEquiv (u θ)) (cellComplexH1RealEquiv (z θ)) =
          -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ (cellFrequencyMetricField G t u i j θ)
            (centeredCellBlochGradientField z j θ)) -
          ∑ i : Fin 2, inner ℝ (cellFrequencyDriftField G v V hv hb t u i θ)
            (centeredCellBlochValueField z θ) := by
  have hu := ae_all_iff.mpr (fun i => (centeredCellBlochGradient_memLp u i).coeFn_toLp)
  have hz := ae_all_iff.mpr (fun i => (centeredCellBlochGradient_memLp z i).coeFn_toLp)
  have hm := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
    (cellScalarCLM (G t i j : ℂ)).coeFn_compLp (centeredCellBlochGradientField u i)))
  have hd := ae_all_iff.mpr (fun i =>
    (cellDriftEntryCLM ⟨fun t _ => G t, v, 0, 0⟩ V hv hb t i).coeFn_compLp
      (centeredCellBlochGradientField u i))
  filter_upwards [hu, hz, hm, hd, cellComplexH1ValueCLM.coeFn_compLp z]
    with θ huθ hzθ hmθ hdθ hvθ
  have hstar : (fun i => star (planePhysicalBlochShift θ i)) = planePhysicalBlochShift θ :=
    funext (planePhysicalBlochShift_real θ)
  change ∀ i, centeredCellBlochGradientField u i θ =
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv (u θ)) at huθ
  change ∀ i, centeredCellBlochGradientField z i θ =
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv (z θ)) at hzθ
  change ∀ i j, cellFrequencyMetricField G t u i j θ =
    cellScalarCLM (G t i j : ℂ) (centeredCellBlochGradientField u i θ) at hmθ
  change ∀ i, cellFrequencyDriftField G v V hv hb t u i θ =
    cellDriftEntryCLM ⟨fun t _ => G t, v, 0, 0⟩ V hv hb t i
      (centeredCellBlochGradientField u i θ) at hdθ
  change centeredCellBlochValueField z θ = cellComplexH1ValueCLM (z θ) at hvθ
  simp only [cellGeneratorForm, cellDiffusionForm, add_apply, sub_apply, neg_apply, sum_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, hstar, cellConstantMetricEntryCLM,
    hmθ, hdθ, huθ, hzθ, hvθ, cellComplexH1ValueCLM_eq, cellScalarCLM_smul, Pi.zero_apply, zero_smul,
    inner_zero_left, add_zero]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact integrated native L2 form of the real-frequency cell generator. -/

theorem cellFrequencyGenerator_integral
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u z : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    (∫ θ, cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb t
      (cellComplexH1RealEquiv (u θ)) (cellComplexH1RealEquiv (z θ))
      ∂centeredPlaneFrequencyMeasure) =
        -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ (cellFrequencyMetricField G t u i j)
          (centeredCellBlochGradientField z j)) -
        ∑ i : Fin 2, inner ℝ (cellFrequencyDriftField G v V hv hb t u i)
          (centeredCellBlochValueField z) := by
  have hm i j := L2.integrable_inner (𝕜 := ℝ) (cellFrequencyMetricField G t u i j)
    (centeredCellBlochGradientField z j)
  have hd i := L2.integrable_inner (𝕜 := ℝ) (cellFrequencyDriftField G v V hv hb t u i)
    (centeredCellBlochValueField z)
  have hms : Integrable (fun θ => ∑ i : Fin 2, ∑ j : Fin 2,
      inner ℝ (cellFrequencyMetricField G t u i j θ) (centeredCellBlochGradientField z j θ))
      centeredPlaneFrequencyMeasure :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm i j))
  have hds : Integrable (fun θ => ∑ i : Fin 2,
      inner ℝ (cellFrequencyDriftField G v V hv hb t u i θ) (centeredCellBlochValueField z θ))
      centeredPlaneFrequencyMeasure := integrable_finsetSum _ (fun i _ => hd i)
  have hneg : Integrable (fun θ => -(∑ i : Fin 2, ∑ j : Fin 2,
      inner ℝ (cellFrequencyMetricField G t u i j θ) (centeredCellBlochGradientField z j θ)))
      centeredPlaneFrequencyMeasure := hms.neg
  have hmi (i : Fin 2) :
      (∫ θ, ∑ j : Fin 2, inner ℝ (cellFrequencyMetricField G t u i j θ)
        (centeredCellBlochGradientField z j θ) ∂centeredPlaneFrequencyMeasure) =
      ∑ j : Fin 2, inner ℝ (cellFrequencyMetricField G t u i j)
        (centeredCellBlochGradientField z j) := by
    rw [integral_finsetSum _ (fun j _ => hm i j)]
    rfl
  calc
    _ = ∫ θ, -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ (cellFrequencyMetricField G t u i j θ)
        (centeredCellBlochGradientField z j θ)) -
      (∑ i : Fin 2, inner ℝ (cellFrequencyDriftField G v V hv hb t u i θ)
        (centeredCellBlochValueField z θ)) ∂centeredPlaneFrequencyMeasure :=
      integral_congr_ae (cellFrequencyGenerator_readout_ae G hG v V hv hb t u z)
    _ = _ := by
      rw [integral_sub hneg hds, integral_neg,
        integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm i j)),
        integral_finsetSum _ (fun i _ => hd i)]
      simp_rw [hmi]
      rfl

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Adjacent native Sobolev reserves interpolate multiplicatively without losing the small lower norm. -/

theorem torusHigher_ordered_gradient_multiplicative_interpolation
    (q : ℕ) (U : TorusHk (q + 2) ℂ) (r : Fin (q + 1)) (w : DerivativeWord2 r.val) (i : Fin 2) :
      ‖cellDerivativeCLM i (derivativeTorusHk (K := 1) w
        (truncateTorusHk (by simpa only [Nat.add_comm 1 r.val] using Nat.add_le_add_right (Nat.le_of_lt_succ r.isLt) 1 : 1 + r.val ≤ q + 1) (truncateTorusHk (Nat.add_le_add_left (by decide : 1 ≤ 2) q) U)))‖ ^ 2 ≤ ‖truncateTorusHk (Nat.le_add_right q 2) U‖ * ‖U‖ := by
  let T : TorusHk (q + 1) ℂ := truncateTorusHk (Nat.add_le_add_left (by decide : 1 ≤ 2) q) U
  let L : TorusHk q ℂ := truncateTorusHk (Nat.le_add_right q 2) U
  let Z : TorusHk 2 ℂ := derivativeTorusHk (K := 2) w
    (truncateTorusHk (by simpa only [Nat.add_comm 2 r.val] using Nat.add_le_add_right (Nat.le_of_lt_succ r.isLt) 2 : 2 + r.val ≤ q + 2) U)
  have hv : torusHkValueCLM Z = L.val (⟨⟨r.val, r.isLt⟩, w⟩ : JetIndex2 q) := by
    change U.val (truncateJetIndex _ (prefixJetIndex w (valueIndex2 2))) =
      U.val (truncateJetIndex _ ⟨⟨r.val, r.isLt⟩, w⟩)
    apply congrArg U.val
    simp only [prefixJetIndex, valueIndex2, valueIndex, truncateJetIndex,
      Fin.val_zero, Nat.add_zero, Fin.append_elim0]
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (by funext j; rfl)
  have hlow : ‖torusHkValueCLM Z‖ ≤ ‖L‖ := by
    rw [hv]
    exact PiLp.norm_apply_le L.val ⟨⟨r.val, r.isLt⟩, w⟩
  have hhigh : ‖Z‖ ≤ ‖U‖ :=
    (derivativeTorusHk_norm_le (K := 2) w _).trans (truncateTorusHk_norm_le _ U)
  exact (cellDerivative_higher_multiplicative_interpolation i Z).trans
    (mul_le_mul hlow hhigh (norm_nonneg _) (norm_nonneg _))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Full value traces transport the finite native error under a change of label. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {L : Type*} [Fintype L]

theorem planeValue_nativeErrorDatum_ae {K : ℕ}
    (U : PlaneHk Set.univ K E) (Z : L → PlaneHk Set.univ K E) :
    planeValue (nativeErrorDatum U Z) =ᵐ[volume]
      (fun z => planeValue U z - ∑ j, planeValue (Z j) z) := by
  classical
  filter_upwards [planeValue_sub_ae U (∑ j, Z j),
    planeJetOrder_finite_sum_ae (Nat.zero_le K) Z (fun i : Fin 0 => Fin.elim0 i)] with z hz hs
  exact hz.trans (congrArg (fun w => planeValue U z - w) hs)

theorem nativeErrorDatum_pullback {K : ℕ} (X : Vec 2 → Vec 2)
    (hX : Measure.QuasiMeasurePreserving X volume volume)
    (U V : PlaneHk Set.univ K E) (Z W : L → PlaneHk Set.univ K E)
    (hU : planeValue V =ᵐ[volume] fun z => planeValue U (X z))
    (hZ : ∀ j, planeValue (W j) =ᵐ[volume] fun z => planeValue (Z j) (X z)) :
    planeValue (nativeErrorDatum V W) =ᵐ[volume]
      (fun z => planeValue (nativeErrorDatum U Z) (X z)) := by
  classical
  filter_upwards [planeValue_nativeErrorDatum_ae V W,
    hX.ae (planeValue_nativeErrorDatum_ae U Z), hU, ae_all_iff.mpr hZ] with z hn ho hu hz
  rw [hn, ho, hu]
  exact congrArg (fun w => planeValue U (X z) - w) (Finset.sum_congr rfl (fun j _ => hz j))

theorem nativeErrorDatum_initial_zero {J K : ℕ} (F : PlaneHk Set.univ K E)
    (Z : Fin (J + 1) → PlaneHk Set.univ K E) (hZ : ∀ j, Z j = if j = 0 then F else 0) :
    nativeErrorDatum F Z = 0 := by
  classical
  unfold nativeErrorDatum
  have hs : (∑ j, Z j) = F := by
    simp only [hZ]
    simp
  rw [hs, sub_self]
end

/-! The literal sampled slow remainder has a finite normalized mixed-jet budget. -/

theorem slowSample_remainder_jet_budget (K J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → Vec 2 → ℝ),
      ContDiff ℝ (J + (K + 1) : ℕ) (Function.uncurry f) →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ a b : ℕ, a + b ≤ J → ∀ X z,
        ρ ^ (a + b) * |δ| ^ a *
          ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
      ∀ j ≤ J, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          f (δ • z) z - taylorSlow 0 K (fun X' => f X' z) 0 (δ • z)) z‖ ≤
          C * B * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := integralMultilinear_scaled_normalized_jet_budget (K + 1) J
  refine ⟨(K.factorial : ℝ)⁻¹ * C * 4 ^ J, by positivity, ?_⟩
  intro f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hjet j hj z
  let τ : ℝ → ℝ := fun t => max 0 (min 1 t)
  have ht0 (t : ℝ) : 0 ≤ τ t := le_max_left _ _
  have ht1 (t : ℝ) : τ t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  let a := fun t (z : Vec 2) => ((1 - τ t) ^ K * ζ ^ (K + 1)) •
    iteratedFDeriv ℝ (K + 1) (fun X' => f X' z) ((τ t * δ) • z)
  have hfield := Weighted.joint_partialIteratedFDeriv_left_contDiff J (K + 1) (Function.uncurry f) hf
  have ha (t : ℝ) : ContDiff ℝ (J : ℕ) (a t) :=
    (hfield.comp ((contDiff_id.const_smul (τ t * δ)).prodMk contDiff_id)).const_smul _
  have hab (t : ℝ) (w : DerivativeWord2 (K + 1)) (k : ℕ) (hk : k ≤ J) (x : Vec 2) :
      ρ ^ k * ‖iteratedFDeriv ℝ k (fun x => a t x (fun i => basisVec (w i))) x‖ ≤
        4 ^ J * B * ζ ^ (K + 1) := by
    have hc : ContDiff ℝ (k : ℕ) (fun x : Vec 2 =>
        iteratedFDeriv ℝ (K + 1) (fun X' => f X' x) ((τ t * δ) • x)
          (fun i => basisVec (w i))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (K + 1) => Vec 2) ℝ
        (fun i => basisVec (w i))).contDiff.comp
        ((hfield.of_le (by exact_mod_cast hk)).comp
          ((contDiff_id.const_smul (τ t * δ)).prodMk contDiff_id))
    change ρ ^ k * ‖iteratedFDeriv ℝ k (fun x => ((1 - τ t) ^ K * ζ ^ (K + 1)) •
      iteratedFDeriv ℝ (K + 1) (fun X' => f X' x) ((τ t * δ) • x)
        (fun i => basisVec (w i))) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, norm_smul,
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr (ht1 t)) K) (pow_nonneg hζ (K + 1)))]
    have hh := sampledSlowCoefficient_jet_le hf w ρ δ (τ t) B hρ.le (ht0 t) (ht1 t) hB hjet k hk x
    have hh' := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (pow_nonneg (sub_nonneg.mpr (ht1 t)) K) (pow_nonneg hζ (K + 1)))
    have hs := mul_le_mul_of_nonneg_right (pow_le_one₀ (sub_nonneg.mpr (ht1 t))
      (by linarith [ht0 t]) (n := K)) (mul_nonneg (by positivity : 0 ≤ 4 ^ J * B) (pow_nonneg hζ (K + 1)))
    apply le_trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hh')
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using hs
  have hm (x : Vec 2) : Measurable (fun t => a t x (fun _ => ϖ • x)) := by
    have ht : Continuous τ := continuous_const.max (continuous_const.min continuous_id)
    apply Continuous.measurable
    exact ((((continuous_const.sub ht).pow K).mul continuous_const).smul
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (K + 1) => Vec 2) ℝ
        (fun _ => ϖ • x)).continuous.comp
        (hfield.continuous.comp (((ht.mul continuous_const).smul continuous_const).prodMk continuous_const))))
  let F := fun x : Vec 2 => ∫ t, a t x (fun _ => ϖ • x) ∂μ
  have he : (fun z : Vec 2 => f (δ • z) z - taylorSlow 0 K (fun X' => f X' z) 0 (δ • z)) =
      fun z => (K.factorial : ℝ)⁻¹ • F z := by
    funext y
    have hs : ContDiff ℝ (K + 1 : ℕ) (fun X' => f X' y) :=
      (hf.of_le (by exact_mod_cast Nat.le_add_left (K + 1) J)).comp
        (contDiff_id.prodMk contDiff_const)
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := fun X' => f X' y)
      (x := 0) (y := δ • y) (n := K) (fun t _ => hs.contDiffAt)
    have hp : taylorSlow 0 K (fun X' => f X' y) 0 (δ • y) =
        ∑ k ∈ Finset.range (K + 1), (k.factorial : ℝ)⁻¹ •
          iteratedFDeriv ℝ k (fun X' => f X' y) 0 (fun _ => δ • y) := by
      simp only [taylorSlow, ← Nat.range_succ_eq_Icc_zero, smul_eq_mul]
    rw [hp]
    simp only [zero_add] at ht
    rw [ht, add_sub_cancel_left]
    congr 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htau : τ t = t := by
      dsimp only [τ]
      rw [min_eq_right ht.2, max_eq_right ht.1.le]
    dsimp only [F, μ, a]
    rw [htau, smul_apply, mul_smul, hδ, mul_smul]
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
  have hFs : ContDiff ℝ (J : ℕ∞) F := by
    have hf' (t : ℝ) : ContDiff ℝ (J : ℕ∞) (fun x => a t x (fun _ => ϖ • x)) :=
      (Weighted.multilinear_diagonal_contDiff J (a t) (ha t) ϖ).of_le (by exact_mod_cast le_refl J)
    obtain ⟨C', hC', hb'⟩ := variableMultilinear_scaled_normalized_jet_budget (K + 1) J
    let price := fun k => C' * (4 ^ J * B * ζ ^ (K + 1)) *
      (1 + 2 * |ϖ|) ^ (K + 1) / ρ ^ k
    apply parameter_integral_contDiff_growth μ J _ hm hf' price
      (fun k => by dsimp only [price]; positivity) (K + 1)
    intro k hk t x
    dsimp only [price]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hρ k)).mpr
    have hh := hb' a ha ϖ ρ (4 ^ J * B * ζ ^ (K + 1)) hϖ hρ.le hscale (by positivity) hab t k hk x
    have hr := pow_le_pow_left₀ (by unfold polynomialMomentRoot; positivity)
      (polynomialMomentRoot_growth_le ϖ x) (K + 1)
    rw [mul_pow] at hr
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hr
      (mul_nonneg hC' (by positivity)))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  rw [he, iteratedFDeriv_const_smul_apply' ((hFs.of_le (by exact_mod_cast hj)).contDiffAt),
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hh := hb μ a ϖ ρ (4 ^ J * B * ζ ^ (K + 1)) hm ha hϖ hρ hscale (by positivity) hab j hj z
  have hmass : μ.real Set.univ = 1 := by simp [μ, measureReal_def, Real.volume_Ioc]
  rw [hmass, mul_one] at hh
  convert mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg K.factorial)) using 1 <;> ring

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Adjacent native Sobolev reserves interpolate multiplicatively without losing the small lower norm. -/

def torusAdjacentInterpolationPrice (q : ℕ) : ℝ :=
  1 + ∑ r : Fin (q + 1), ∑ _w : DerivativeWord2 r.val, ∑ _i : Fin 2, (1 : ℝ)

theorem torusHigher_adjacent_multiplicative_interpolation (q : ℕ) (U : TorusHk (q + 2) ℂ) :
    ‖truncateTorusHk (Nat.add_le_add_left (by decide : 1 ≤ 2) q : q + 1 ≤ q + 2) U‖ ^ 2 ≤
      torusAdjacentInterpolationPrice q *
        (‖truncateTorusHk (Nat.le_add_right q 2 : q ≤ q + 2) U‖ * ‖U‖) := by
  let T : TorusHk (q + 1) ℂ := truncateTorusHk (Nat.add_le_add_left (by decide : 1 ≤ 2) q : q + 1 ≤ q + 2) U
  let L : TorusHk q ℂ := truncateTorusHk (Nat.le_add_right q 2 : q ≤ q + 2) U
  have hvalue : ‖torusHkValueCLM T‖ ^ 2 ≤ ‖L‖ * ‖U‖ := by
    have hlow : ‖torusHkValueCLM T‖ ≤ ‖L‖ := by
      change ‖L.val (valueIndex2 q)‖ ≤ ‖L.val‖
      exact PiLp.norm_apply_le L.val (valueIndex2 q)
    have hhigh : ‖torusHkValueCLM T‖ ≤ ‖U‖ := by
      change ‖U.val (valueIndex2 (q + 2))‖ ≤ ‖U.val‖
      exact PiLp.norm_apply_le U.val (valueIndex2 (q + 2))
    simpa only [pow_two] using mul_le_mul hlow hhigh (norm_nonneg _) (norm_nonneg _)
  change ‖T‖ ^ 2 ≤ _
  rw [torusHigher_norm_sq_eq_value_gradient q T]
  unfold torusAdjacentInterpolationPrice
  rw [add_mul, one_mul, Finset.sum_mul]
  simp_rw [Finset.sum_mul, one_mul]
  apply add_le_add hvalue
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro w _
  exact Finset.sum_le_sum (fun i _ => torusHigher_ordered_gradient_multiplicative_interpolation q U r w i)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The sampled slow remainder budget is uniform in the absolute slow anchor. -/

theorem centeredSlow_remainder_jet_budget (K J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → Vec 2 → ℝ),
      ContDiff ℝ (J + (K + 1) : ℕ) (Function.uncurry f) →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ a b : ℕ, a + b ≤ J → ∀ X z,
        ρ ^ (a + b) * |δ| ^ a *
          ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
      ∀ X0 j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          f (X0 + δ • z) z - taylorSlow 0 K (fun X' => f X' z) X0 (δ • z)) z‖ ≤
          C * B * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  obtain ⟨C, hC, hb⟩ := slowSample_remainder_jet_budget K J
  refine ⟨C, hC, ?_⟩
  intro f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hjet X0 j hj z
  let F := fun X z => f (X0 + X) z
  have hF : ContDiff ℝ (J + (K + 1) : ℕ) (Function.uncurry F) :=
    hf.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  have hbound (a b : ℕ) (hab : a + b ≤ J) (X z : Vec 2) :
      ρ ^ (a + b) * |δ| ^ a *
        ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (F X') z) X‖ ≤ B := by
    change ρ ^ (a + b) * |δ| ^ a *
      ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f (X0 + X')) z) X‖ ≤ B
    rw [iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun X' => iteratedFDeriv ℝ b (f X') z) (K + 1 + a) X0 X]
    exact hjet a b hab (X0 + X) z
  have he (y : Vec 2) : taylorSlow 0 K (fun X' => F X' y) 0 (δ • y) =
      taylorSlow 0 K (fun X' => f X' y) X0 (δ • y) := by
    unfold taylorSlow
    apply Finset.sum_congr rfl
    intro r _
    change (r.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ r (fun X' => f (X0 + X') y) 0 (fun _ => δ • y) = _
    rw [iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun X' => f X' y) r X0 0, add_zero]
  have hh := hb F hF ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hbound j hj z
  simp_rw [he] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Subtracting a finite family of actual weak equations yields the native
error equation, preserving all endpoint, spatial, and time integrability. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]

theorem nativeWeakIdentity_sub_sum {L : Type*} [Fintype L] (K : ℕ) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (U f : PlaneHk Set.univ K H)
    (Z fZ : L → PlaneHk Set.univ K H) (Uw : ℝ → PlaneHk Set.univ (K + 1) H)
    (Zw : L → ℝ → PlaneHk Set.univ (K + 1) H)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (B : L → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (ψ : PlaneHk Set.univ 1 H)
    (hU : CoupledWeakIdentity volume ν a t v (U.toFunction.jet (valueIndex2 K))
      (f.toFunction.jet (valueIndex2 K)) (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (Uw r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩) A 0 0)
    (hZ : ∀ j, CoupledWeakIdentity volume ν a t v ((Z j).toFunction.jet (valueIndex2 K))
      ((fZ j).toFunction.jet (valueIndex2 K)) (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩) (B j) 0 0) :
    CoupledWeakIdentity volume ν a t v ((U - ∑ j, Z j).toFunction.jet (valueIndex2 K))
      ((f - ∑ j, fZ j).toFunction.jet (valueIndex2 K)) (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (Uw r - ∑ j, Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (A - ∑ j, B j) 0 0 := by
  classical
  let φ := ψ.toFunction.jet (valueIndex2 1)
  let dφ := fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩
  let du := fun r k => (Uw r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ -
    ∑ j, (Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩
  let du' := fun r k => (Uw r - ∑ j, Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩
  have hsum := coupledWeakIdentity_finset_sum Finset.univ volume ν a t v
    (fun j => (Z j).toFunction.jet (valueIndex2 K)) (fun j => (fZ j).toFunction.jet (valueIndex2 K))
    φ dφ (fun j r k => (Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    B (fun _ => 0) (fun _ => 0) (fun j _ => hZ j)
  simp only [Finset.sum_const_zero] at hsum
  have hh := coupledWeakIdentity_sub volume ν a t v _ _ _ _ φ dφ _ _ A (∑ j, B j) 0 0 0 0 hU hsum
  simp only [sub_self] at hh
  have hue : (U.toFunction.jet (valueIndex2 K) - ∑ j, (Z j).toFunction.jet (valueIndex2 K)) =
      (fun z => U.toFunction.jet (valueIndex2 K) z - ∑ j, (Z j).toFunction.jet (valueIndex2 K) z) := by
    funext z
    simp only [Pi.sub_apply, Finset.sum_apply]
  have hfe : (f.toFunction.jet (valueIndex2 K) - ∑ j, (fZ j).toFunction.jet (valueIndex2 K)) =
      (fun z => f.toFunction.jet (valueIndex2 K) z - ∑ j, (fZ j).toFunction.jet (valueIndex2 K) z) := by
    funext z
    simp only [Pi.sub_apply, Finset.sum_apply]
  have hde : ((fun r k => (Uw r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩) -
      ∑ j, fun r k => (Zw j r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩) = du := by
    funext r k z
    simp only [du, Pi.sub_apply, Finset.sum_apply]
  rw [hue, hfe, hde] at hh
  have he := coupledWeakIdentity_value_congr volume ν a t v _ _ _ _ φ dφ du
    (A - ∑ j, B j) 0 0 hh
    (planeStoredJet_sub_sum_ae U Z (valueIndex2 K)).symm
    (planeStoredJet_sub_sum_ae f fZ (valueIndex2 K)).symm
  have hd (r : ℝ) (k : Fin 2) : du r k =ᵐ[volume] du' r k := by
    filter_upwards [planeStoredJet_sub_sum_ae (Uw r) (fun j => Zw j r) ⟨⟨1, by omega⟩, fun _ => k⟩] with z hz
    simpa only [du, du', Pi.sub_apply, Finset.sum_apply] using hz.symm
  have hi (r : ℝ) (hr : r ∈ Set.Ioc a t) : Integrable (fun z =>
      -(∑ k : Fin 2, v r z k * inner ℝ (du' r k z) (φ z)) -
        ν * ∑ k : Fin 2, inner ℝ (du' r k z) (dφ k z) -
        ∑ k : Fin 2, inner ℝ ((A - ∑ j, B j) r z k + (0 : PiLp 2 (fun _ : Fin 2 => H)) k) (dφ k z) +
        inner ℝ (0 : H) (φ z)) volume := by
    apply (he.2.2.1 r hr).congr
    filter_upwards [ae_all_iff.mpr (hd r)] with z hz
    simp only [du, du'] at hz ⊢
    simp_rw [hz]
    simp only [Pi.zero_apply]
  exact coupledWeakIdentity_gradient_flux_ae_time_congr volume ν a t v _ _ φ dφ du du'
    (A - ∑ j, B j) 0 (A - ∑ j, B j) 0 0 he
    (Filter.Eventually.of_forall hd) (Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))) hi

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! Recursive adjacent interpolation supplies all spatial orders with contrast-independent constants. -/

def adjacentGapPrice (C : ℕ → ℝ) (B : ℝ) : ℕ → ℝ
  | 0 => B
  | j + 1 => Real.sqrt (torusAdjacentInterpolationPrice j * adjacentGapPrice C B j * C (j + 2))

theorem adjacentGapPrice_nonneg (C : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (j : ℕ) :
    0 ≤ adjacentGapPrice C B j := by
  cases j with
  | zero => exact hB
  | succ j => exact Real.sqrt_nonneg _

theorem adjacent_polynomial_gap_hierarchy (A C : ℕ → ℝ) (B p x γ D : ℝ)
    (hA : ∀ j, 0 ≤ A j) (hC : ∀ j, 0 ≤ C j) (hB : 0 ≤ B) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hinterp : ∀ j, A (j + 1) ^ 2 ≤ torusAdjacentInterpolationPrice j * (A j * A (j + 2)))
    (hhigh : ∀ j, A j ≤ C j * p ^ (2 * j) * x)
    (hzero : A 0 ≤ B * x * Real.exp (-γ * D)) :
    ∀ j, A j ≤ adjacentGapPrice C B j * p ^ (2 * j) * x *
      Real.exp (-(γ / (2 : ℝ) ^ j) * D) := by
  intro j
  induction j with
  | zero => simpa only [adjacentGapPrice, Nat.mul_zero, pow_zero, mul_one, div_one] using hzero
  | succ j ih =>
    have hN : 0 ≤ torusAdjacentInterpolationPrice j := by
      unfold torusAdjacentInterpolationPrice
      positivity
    have he := adjacent_polynomial_gap_price j (A (j + 1)) (A j) (A (j + 2))
      (torusAdjacentInterpolationPrice j) (adjacentGapPrice C B j) (C (j + 2)) p x
      (γ / (2 : ℝ) ^ j) D (hA _) (hA _) hN (adjacentGapPrice_nonneg C B hB j)
      (hC _) hp hx (hinterp j) ih (hhigh (j + 2))
    have hexp : -(γ / (2 : ℝ) ^ j) * D / 2 = -(γ / (2 : ℝ) ^ (j + 1)) * D := by
      rw [pow_succ]
      field_simp
    simpa only [adjacentGapPrice, hexp] using he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Taylor coefficients retain every original slow derivative price and constituent identity. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def molecularTaylorPrefixPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Kmax : ℕ) (dom : F.Domain) (ν e E ρ : ℝ) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (j : ℕ) : ℝ :=
  (Kmax.factorial : ℝ) ^ 2 * E ^ j * molecularRealPrice ν ρ (K v) (d - 2)
    (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))

theorem familyMolecular_taylor_coefficient (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      ∀ (dom : F.Domain) (ν e E ρ : ℝ), 0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      let cc := slowTaylorTimeCoefficient Ks
        (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
      (∀ z, Measurable (fun t => cc t z)) ∧
        (∀ t, ContDiff ℝ (K v : ℕ) (cc t)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
          (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
            CT * (∑ r ∈ Finset.range (Ks + 1),
              molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) * polynomialMomentRoot ϖ z ^ Ks) := by
  obtain ⟨CT, hCT, hTaylor⟩ := slowTaylor_time_coefficient_budget Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow
  let f := fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k
  have hm (X z : Vec 2) : Measurable (fun t => f t X z) :=
    ((measurable_pi_iff.mp (hmeas p c v u γ d I X (z + φ))) k).comp
      ((measurable_const (a := s)).mul measurable_id)
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (Ks + K v : ℕ) (Function.uncurry (f t)) := by
    have h0 := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c (s * t) (hwindow t ht) v u γ d I
    have h1 : ContDiff ℝ (Ks + K v : ℕ)
        (Function.uncurry (F.flux p c v u γ d I (s * t))) :=
      h0.of_le (by exact_mod_cast (by omega : Ks + K v ≤ K v + J))
    exact (ContinuousLinearMap.proj k).contDiff.comp
      (h1.comp (contDiff_fst.prodMk (contDiff_snd.add (contDiff_const (c := φ)))))
  have hprice (r : ℕ) : 0 ≤ molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r := by
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hR : 0 < derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    unfold derivativeReserveFactor
    positivity
  have hjet : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r ≤ Ks, ∀ j ≤ K v, ∀ X z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤
        molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r /
          derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    have hall : ∀ r, ∀ᵐ t ∂volume.restrict (Set.Icc a b), r ≤ Ks →
        ∀ j ≤ K v, ∀ X z, (ρ / e) ^ j *
          ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤
            molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r /
              derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
      intro r
      by_cases hr : r ≤ Ks
      · have hb := familyMolecular_ae_scalar_mixed_budget F π hπ K Kmax hK dom ν e E ρ
          hν he hE hρ C J b₀ henv v u γ hγ d hd I r (hr.trans hKs) p c
        have hb' := ae_restrict_of_ae (s := Set.Icc a b) (ae_real_time_dilation s hs _ hb)
        filter_upwards [hb', ae_restrict_mem measurableSet_Icc] with t ht htI
        intro _ j hj X z
        simpa only [f, molecularTaylorPrefixPrice, Nat.add_zero, zero_add, pow_zero, mul_one] using
          ht (hwindow t htI) φ k 0 j (by omega) X z
      · exact Filter.Eventually.of_forall (fun _ hr' => (hr hr').elim)
    exact ae_all_iff.mpr hall
  exact hTaylor (K v) (hK v) f a b X0 ϖ (ρ / e) (e / E) ζ
    (derivativeReserveFactor (ρ / e) (K v) (d - 2)) hm hf hϖ (div_pos hρ he).le
    hscale hζ hζ1 hR hδ _ hprice hjet

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! All bounded component slots share one literal slow remainder insertion constant. -/

theorem slowRemainder_uniform_reserved_budget (K Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≤ Nmax, ∀ (f : Vec 2 → Vec 2 → ℝ),
      ContDiff ℝ (N + (K + 1) : ℕ) (Function.uncurry f) →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 →
        0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ a b : ℕ, a + b ≤ N → ∀ X z,
        ρ ^ (a + b) * |δ| ^ a *
          ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
      ∀ X0 j, j ≤ N → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => f (X0 + δ • z) z -
          taylorSlow 0 K (fun X' => f X' z) X0 (δ • z)) z‖ ≤
          C * B * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  classical
  have hs (N : ℕ) := centeredSlow_remainder_jet_budget K N
  choose C₀ hC₀ h₀ using hs
  let C := ∑ N ∈ Finset.range (Nmax + 1), C₀ N
  refine ⟨C, Finset.sum_nonneg (fun N _ => hC₀ N), ?_⟩
  intro N hN f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hb X0 j hj z
  have hh := h₀ N f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hb X0 j hj z
  have hCN : C₀ N ≤ C := Finset.single_le_sum (fun N _ => hC₀ N)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCN hB) (pow_nonneg hζ (K + 1)))
    (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) (K + 1)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Taylor coefficients retain every original slow derivative price and constituent identity. -/

theorem familyMolecular_taylor_coefficient_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      ∀ (dom : F.Domain) (ν e E ρ : ℝ), 0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      let cc := slowTaylorTimeCoefficient Ks
        (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
      (∀ z, Measurable (fun t => cc t z)) ∧
        (∀ t, ContDiff ℝ (K v : ℕ) (cc t)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
          (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
            CT * (∑ r ∈ Finset.range (Ks + 1),
              molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) * polynomialMomentRoot ϖ z ^ Ks) := by
  obtain ⟨CT, hCT, hTaylor⟩ := slowTaylor_time_coefficient_budget Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι h _ _ D P Ctx F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow
  let f := fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k
  have hm (X z : Vec 2) : Measurable (fun t => f t X z) :=
    ((measurable_pi_iff.mp (hmeas p c v u γ d I X (z + φ))) k).comp
      ((measurable_const (a := s)).mul measurable_id)
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (Ks + K v : ℕ) (Function.uncurry (f t)) := by
    have h0 := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c (s * t) (hwindow t ht) v u γ d I
    have h1 : ContDiff ℝ (Ks + K v : ℕ)
        (Function.uncurry (F.flux p c v u γ d I (s * t))) :=
      h0.of_le (by exact_mod_cast (by omega : Ks + K v ≤ K v + J))
    exact (ContinuousLinearMap.proj k).contDiff.comp
      (h1.comp (contDiff_fst.prodMk (contDiff_snd.add (contDiff_const (c := φ)))))
  have hprice (r : ℕ) : 0 ≤ molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r := by
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hR : 0 < derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    unfold derivativeReserveFactor
    positivity
  have hjet : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r ≤ Ks, ∀ j ≤ K v, ∀ X z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤
        molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r /
          derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
    have hall : ∀ r, ∀ᵐ t ∂volume.restrict (Set.Icc a b), r ≤ Ks →
        ∀ j ≤ K v, ∀ X z, (ρ / e) ^ j *
          ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤
            molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r /
              derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
      intro r
      by_cases hr : r ≤ Ks
      · have hb := familyMolecular_ae_scalar_mixed_budget F π hπ K Kmax hK dom ν e E ρ
          hν he hE hρ C J b₀ henv v u γ hγ d hd I r (hr.trans hKs) p c
        have hb' := ae_restrict_of_ae (s := Set.Icc a b) (ae_real_time_dilation s hs _ hb)
        filter_upwards [hb', ae_restrict_mem measurableSet_Icc] with t ht htI
        intro _ j hj X z
        simpa only [f, molecularTaylorPrefixPrice, Nat.add_zero, zero_add, pow_zero, mul_one] using
          ht (hwindow t htI) φ k 0 j (by omega) X z
      · exact Filter.Eventually.of_forall (fun _ hr' => (hr hr').elim)
    exact ae_all_iff.mpr hall
  exact hTaylor (K v) (hK v) f a b X0 ϖ (ρ / e) (e / E) ζ
    (derivativeReserveFactor (ρ / e) (K v) (d - 2)) hm hf hϖ (div_pos hρ he).le
    hscale hζ hζ1 hR hδ _ hprice hjet

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Genuine coherent periodic jets inherit all-order exponential forgetting from their zero-order trace. -/

theorem torusHigher_coherent_truncate (U : ∀ j, TorusHk j ℂ)
    (hcoherent : ∀ j, torusHkValueCLM (U j) = torusHkValueCLM (U 0))
    {j k : ℕ} (hjk : j ≤ k) : truncateTorusHk hjk (U k) = U j := by
  apply TorusHk.ext_value
  change torusHkValueCLM (truncateTorusHk hjk (U k)) = torusHkValueCLM (U j)
  rw [torusHigher_truncate_value, hcoherent k, hcoherent j]

theorem torusHigher_polynomial_gap_hierarchy (U : ∀ j, TorusHk j ℂ)
    (hcoherent : ∀ j, torusHkValueCLM (U j) = torusHkValueCLM (U 0))
    (C : ℕ → ℝ) (B p x γ D : ℝ) (hC : ∀ j, 0 ≤ C j)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hhigh : ∀ j, ‖U j‖ ≤ C j * p ^ (2 * j) * x)
    (hzero : ‖U 0‖ ≤ B * x * Real.exp (-γ * D)) :
    ∀ j, ‖U j‖ ≤ adjacentGapPrice C B j * p ^ (2 * j) * x *
      Real.exp (-(γ / (2 : ℝ) ^ j) * D) := by
  apply adjacent_polynomial_gap_hierarchy (fun j => ‖U j‖) C B p x γ D
    (fun j => norm_nonneg (U j)) hC hB hp hx _ hhigh hzero
  intro j
  have he := torusHigher_adjacent_multiplicative_interpolation j (U (j + 2))
  rw [torusHigher_coherent_truncate U hcoherent,
    torusHigher_coherent_truncate U hcoherent] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The logarithmic gradient and exact metric flux share the chart weight rate. -/

theorem adjointPolynomial_metric_gradient {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C K : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (yc : Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (t : ℝ) (z : Vec 2) (hG : ∀ i j : Fin 2, |G t z i j| ≤ 5 / 4) :
    let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc n
    (∑ i : Fin 2, (fderiv ℝ (W t) z (basisVec i)) ^ 2) / W t z ^ 2 +
      (∑ i : Fin 2, metricCorrectionFlux (W t) (G t) z i ^ 2) / W t z ^ 2 ≤
        adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T) := by
  dsimp only
  let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc n
  have hgW := adjointCellPolynomialWeight_gradient_budget (α := α) (q := q) (m := m)
    hΛ hζ hν hB hT hC he yc n t z
  have hφ := metricCorrectionFlux_sq_sum_bound (W t) (G t) z hG
  have hdiv := div_le_div_of_nonneg_right hφ (sq_nonneg (W t z))
  rw [mul_div_assoc] at hdiv
  have hh := mul_le_mul_of_nonneg_left hgW (show (0 : ℝ) ≤ 65 by norm_num)
  have hr := mul_le_mul_of_nonneg_right (adjointWeightRate_gradient hC hK n)
    (div_nonneg (sq_nonneg (ocEll q Λ m ν)) hT.le)
  have hi : 65 * ((n : ℝ) ^ 2 * (32 * C) * (ocEll q Λ m ν ^ 2 / T)) ≤
      adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T) := by
    simpa only [mul_assoc] using hr
  linarith only [hdiv, hh, hi]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleWords

/-! Actual compact smooth compositions converge to the native weighted pullback under polynomial chart growth. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_smooth_pullback_sequence_limit {K : ℕ} (U : PlaneHk Set.univ K E)
    (UN : ℕ → PlaneHk Set.univ K E) (fN : ℕ → Vec 2 → E)
    (hUN : Tendsto UN atTop (𝓝 U))
    (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n) ∧ HasCompactSupport (fN n))
    (hv : ∀ n, planeValue (UN n) =ᵐ[volume] fN n)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 1 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ K ≤ L * qin (X z))
    (RN : ℕ → PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hRN : ∀ n a, RN n a =ᵐ[volume] (fun x => qin x • (UN n).toFunction.jet a x))
    (hc : CauchySeq RN) :
    ∃ V : PlaneHk Set.univ K E, planeValue V =ᵐ[volume] planeValue U ∘ X ∧
      ∀ a : JetIndex2 K, MemLp (fun x => qout x • V.toFunction.jet a x) 2 volume := by
  let WN n := smoothCompactPlanePullback K (fN n) (hs n).1 (hs n).2 X hX
  have hW (n : ℕ) : planeValue (WN n) =ᵐ[volume] fN n ∘ X :=
    smoothCompactPlanePullback_value_ae K (fN n) (hs n).1 (hs n).2 X hX
  have hm (n : ℕ) (a : JetIndex2 K) :
      MemLp (fun x => qout x • (WN n).toFunction.jet a x) 2 volume := by
    have ha := Nat.le_of_lt_succ a.1.isLt
    obtain ⟨hp, _hb⟩ := weighted_composition_jet_array_bound (UN n) (hs n).1 (hv n) hX hμ
      qout qin P hqout (fun z => zero_le_one.trans (hout z)) hin B a.1.val ha a.2 L hL hP
      (fun j hj hn => hB j hj (hn.trans ha))
      (fun j hj hn => hb j hj (hn.trans ha))
      (fun z => (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hP z) ha)
        (zero_le_one.trans (hout z))).trans (hweight z)) (RN n) (hRN n)
    have he := weighted_smooth_jet_ae (WN n) ((hs n).1.comp hX) (hW n) qout ha a.2
    exact hp.ae_eq he.symm
  let TN n : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) :=
    WithLp.toLp 2 (fun a => (hm n a).toLp (fun x => qout x • (WN n).toFunction.jet a x))
  have hTN (n : ℕ) (a : JetIndex2 K) :
      TN n a =ᵐ[volume] (fun x => qout x • (WN n).toFunction.jet a x) := (hm n a).coeFn_toLp
  have hct := weighted_composition_array_cauchy UN WN fN (fun n => (hs n).1) hv hX hμ hW
    qout qin P hqout (fun z => zero_le_one.trans (hout z)) hin B L hL hP hB hb hweight
    RN TN hRN hTN hc
  obtain ⟨V, T, hV, _hT, ht⟩ := weightedJetArray_cauchy_limit WN qout hout TN hTN hct
  let A := planeHkValueOperator (E := E) K
  have heN n : A (WN n) = Lp.compMeasurePreserving X hμ (A (UN n)) := by
    apply planeValueLp_transport_eq
    exact (hW n).trans (hμ.quasiMeasurePreserving.ae_eq_comp (hv n)).symm
  have hl : Tendsto (fun n => A (WN n)) atTop (𝓝 (A V)) := (A.continuous.tendsto V).comp hV
  have hr : Tendsto (fun n => Lp.compMeasurePreserving X hμ (A (UN n))) atTop
      (𝓝 (Lp.compMeasurePreserving X hμ (A U))) :=
    ((Lp.compMeasurePreservingₗᵢ ℝ X hμ).continuous.tendsto (A U)).comp
      ((A.continuous.tendsto U).comp hUN)
  have he : A V = Lp.compMeasurePreserving X hμ (A U) :=
    tendsto_nhds_unique hl (hr.congr (fun n => (heN n).symm))
  refine ⟨V, ?_, fun a => (Lp.memLp (T a)).ae_eq (ht a)⟩
  have hv' : planeValue V =ᵐ[volume] (Lp.compMeasurePreserving X hμ (A U) : Vec 2 → E) := by
    rw [← he]
    exact (planeValueLp_ae V).symm
  exact hv'.trans ((Lp.coeFn_compMeasurePreserving (A U) hμ).trans
    (hμ.quasiMeasurePreserving.ae_eq_comp (planeValueLp_ae U)))

end AVRegularity.CycleWords
end
