-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneBlochEnergyOperator
import AVRegularity.CycleWords.L2StrongOperatorContinuity
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleDamping.BandHighDecay
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Frequency-dependent measurable data produce measurable actual fibre evolutions. -/

theorem planeBlochEnergyFamily_continuous {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) :
    Continuous (planeBlochEnergyFamily hab G hG v V hv hb d) :=
  continuous_iff_continuousAt.mpr (fun ζ =>
    (planeBlochEnergyFamily_analyticAt hab G hG v V hv hb d ζ).continuousAt)

theorem planeBlochEnergyFamily_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : X → CellFiniteEnergyDatum a b) (hd : StronglyMeasurable d)
    (ζ : X → Fin 2 → ℂ) (hζ : Measurable ζ) :
    StronglyMeasurable (fun x => planeBlochEnergyFamily hab G hG v V hv hb (d x) (ζ x)) := by
  have hc (e : CellFiniteEnergyDatum a b) :
      Continuous (fun y => planeBlochEnergyOperator hab G hG v V hv hb y e) := by
    simpa only [planeBlochEnergyOperator_apply] using
      planeBlochEnergyFamily_continuous hab G hG v V hv hb e
  simpa only [planeBlochEnergyOperator_apply] using
    strongOperatorFamily_stronglyMeasurable
      (planeBlochEnergyOperator hab G hG v V hv hb) hc d hd ζ hζ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Uniform native bounds on the actual full Galerkin sequence pass to its continuous trace. -/

theorem CellGalerkinLimitData.full_trace_native_of_uniform_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (initial : ComplexCellL2) (D : CellGalerkinLimitData a b hab C hG V hv hb 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative C hG V hv hb t (D.limit t) 0 0))
    (hinitial : U a = initial) (J : ℕ) (t : ℝ) (ht : t ∈ Icc a b)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ N, ‖cellGalerkinNativeLiftCLM N J (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ B) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤ B := by
  apply cellNative_exists_of_bounded_moments J
    (fun n => cellGalerkinNativeLiftCLM (D.subsequence n) J
      (extendCurve hab (D.curve (D.subsequence n)) t)) (U t) B hB
    (fun n => hbound (D.subsequence n))
  intro z
  simpa only [cellGalerkinNativeLiftCLM_value] using
    cellFullGalerkin_trace_moments_tendsto hab C hG V k hv hb hκ hκb initial D U hU hinitial z t ht

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Bounded frequency sets carry genuine L2 fields of cell energy solutions. -/

theorem planeBlochEnergyFamily_aestronglyMeasurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : X → CellFiniteEnergyDatum a b) (hd : AEStronglyMeasurable d μ)
    (ζ : X → Fin 2 → ℂ) (hζ : Measurable ζ) :
    AEStronglyMeasurable (fun x => planeBlochEnergyFamily hab G hG v V hv hb (d x) (ζ x)) μ := by
  have hm := (planeBlochEnergyFamily_stronglyMeasurable hab G hG v V hv hb
    (hd.mk d) hd.stronglyMeasurable_mk ζ hζ).aestronglyMeasurable (μ := μ)
  apply hm.congr
  filter_upwards [hd.ae_eq_mk] with x hx
  rw [hx]

theorem planeBlochEnergyFamily_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : X → CellFiniteEnergyDatum a b) (hd : MemLp d 2 μ)
    (ζ : X → Fin 2 → ℂ) (hζ : Measurable ζ)
    (R : ℝ) (hR : ∀ᵐ x ∂μ, ∑ j, ‖ζ x j‖ ^ 2 ≤ R) :
    MemLp (fun x => planeBlochEnergyFamily hab G hG v V hv hb (d x) (ζ x)) 2 μ := by
  let K := Real.sqrt (20 * (b - a + 2) *
    Real.exp (300 * (1 + R + V ^ 2) * (b - a)))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  apply (hd.const_smul K).of_le
    (planeBlochEnergyFamily_aestronglyMeasurable μ hab G hG v V hv hb d
      hd.aestronglyMeasurable ζ hζ)
  filter_upwards [hR] with x hx
  change ‖planeBlochEnergyFamily hab G hG v V hv hb (d x) (ζ x)‖ ≤ ‖K • d x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
  exact planeBlochEnergyFamily_norm_le hab G hG v V hv hb (d x) (ζ x) R hx

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual homogeneous energy and continuous-time trace operators. -/

def cellHomogeneousDatumCLM (a b : ℝ) : ComplexCellL2 →L[ℂ] CellFiniteEnergyDatum a b :=
  ContinuousLinearMap.inl ℂ ComplexCellL2
    (Lp ComplexCellL2 2 (volume.restrict (Icc a b)) ×
      (Fin 2 → Lp ComplexCellL2 2 (volume.restrict (Icc a b))))

def planeBlochHomogeneousEnergyOperator {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (ζ : Fin 2 → ℂ) :
    ComplexCellL2 →L[ℂ] CellEnergySpace a b :=
  (planeBlochEnergyOperator hab G hG v V hv hb ζ).comp (cellHomogeneousDatumCLM a b)

def cellEnergyTraceAtCLM (a b : ℝ) (t : CellCompactTime a b) :
    CellEnergySpace a b →L[ℂ] ComplexCellL2 :=
  (ContinuousMap.evalCLM (R := ℂ) t).comp (cellEnergySpaceTraceCLM a b)

theorem cellEnergyTraceAtCLM_apply (a b : ℝ) (t : CellCompactTime a b)
    (z : CellEnergySpace a b) : cellEnergyTraceAtCLM a b t z = z.val.1 t := rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! The committed full homogeneous limit sequence satisfies the actual finite strong-time equation. -/

theorem cellGalerkinForcing_zero (N : ℕ) :
    cellGalerkinForcing (E := ℂ) N 0 = 0 := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  rw [map_zero, LinearMap.zero_apply]
  change inner ℝ (cellGalerkinValue N (cellGalerkinForcing N 0)) (cellGalerkinValue N z) = 0
  exact cellGalerkinForcing_pairing N 0 z

theorem cellRawSourceFunctional_zero (θ : Fin 2 → ℂ) (t : ℝ) :
    cellRawSourceFunctional θ 0 0 t = 0 := by
  apply LinearMap.ext
  intro z
  exact cellRawSourceFunctional_zero_apply θ t z

theorem CellGalerkinLimitData.full_homogeneous_strongTime {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (initial : ComplexCellL2) (D : CellGalerkinLimitData a b hab C hG V hv hb 0 0 initial)
    (N : ℕ) :
    StrongTimeRegularity a b (extendCurve hab (D.curve N)) (fun t =>
      cellGalerkinOperator N (cellGeneratorB C hG V hv hb t)
        (extendCurve hab (D.curve N) t)) := by
  apply cellGalerkin_value_strongTime_pullback N
  simpa only [linearRhs, cellRawSourceFunctional_zero, cellGalerkinForcing_zero, add_zero] using
    (D.variational N).time

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Joint measurability of the actual continuous energy trace in time and frequency. -/

theorem cellEnergyJointTrace_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    {a b : ℝ} (hab : a ≤ b) (F : X → CellEnergySpace a b) (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun p : X × ℝ => cellEnergySpaceTrace hab (F p.1) p.2) := by
  have hc : ∀ θ, Continuous (fun t => cellEnergySpaceTrace hab (F θ) t) := by
    intro θ
    exact ((F θ).val.1.continuous).comp continuous_projIcc
  have hm : ∀ t : ℝ, StronglyMeasurable (fun θ => cellEnergySpaceTrace hab (F θ) t) := by
    intro t
    exact (cellEnergyTraceAtCLM a b (projIcc a b hab t)).continuous.comp_stronglyMeasurable hF
  have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hm
  exact h.comp_measurable measurable_swap

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Frequency-integrated energy traces are continuous in time in the actual L2 norm. -/

theorem cellEnergyTraceAtCLM_apply_norm_le (a b : ℝ) (t : CellCompactTime a b)
    (z : CellEnergySpace a b) : ‖cellEnergyTraceAtCLM a b t z‖ ≤ ‖z‖ := by
  rw [cellEnergyTraceAtCLM_apply]
  exact (z.val.1.norm_coe_le_norm t).trans (norm_fst_le z.val)

theorem cellEnergyTraceAtCLM_continuous (a b : ℝ) (z : CellEnergySpace a b) :
    Continuous (fun t => cellEnergyTraceAtCLM a b t z) := z.val.1.continuous

theorem cellEnergyTraceLp_continuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a b : ℝ) (F : Lp (CellEnergySpace a b) 2 μ) :
    Continuous (fun t => (cellEnergyTraceAtCLM a b t).compLp F) :=
  L2StrongOperator_continuous_of_bound μ (cellEnergyTraceAtCLM a b) 1 (by norm_num)
    (fun t z => by simpa only [one_mul] using cellEnergyTraceAtCLM_apply_norm_le a b t z)
    (cellEnergyTraceAtCLM_continuous a b) F

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_ordered_dual_memLp_of_flux_lower_integral
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, (∫⁻ t in Set.Icc a b, ENNReal.ofReal (‖F i t‖ ^ 2)) < ⊤)
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι) (α : JetIndex2 (κ i.1 i.2)) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    MemLp (fun t => planeSourceDual (planeJetReadoutOperator (κ i.1 i.2) α (H t))
      (planeJetFluxOperator (κ i.1 i.2) α (S t))) 2 (volume.restrict (Set.Icc a b)) := by
  dsimp only
  let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
  let Q := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (fun _ => 0)
  let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
  have hH : MemLp H 2 (volume.restrict (Set.Icc a b)) :=
    scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
      hV ha hB hlam hbv hjets (w i) (hsln.2.1 i)
  have hQ : MemLp Q 2 (volume.restrict (Set.Icc a b)) :=
    scalarSobolevMetricSource_zero_memLp hab G hGm (hG i) (M i) (hb i)
      (w i) (hsln.2.1 i)
  have hsplit : S = fun t => Q t + F i t := by
    funext t
    simp only [S, Q, scalarSobolevMetricSource, add_zero]
  have hm := scalarChain_ordered_dual_aestronglyMeasurable a b hab κ Kmax hκ v hv
    V strain B lam hbv hjets G hG M hb g hg4 hGnear hGs f F u w hsln i α
  change AEStronglyMeasurable (fun t => planeSourceDual
    (planeJetReadoutOperator (κ i.1 i.2) α (H t))
    (planeJetFluxOperator (κ i.1 i.2) α (S t))) (volume.restrict (Set.Icc a b)) at hm
  have hdual := planeJetSourceDual_memLp_of_measurable_lower_integral H Q (F i) S hH hQ (hF i) (congrFun hsplit) α hm
  exact hdual
end

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_ordered_curve_of_flux_lower_integral
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, (∫⁻ t in Set.Icc a b, ENNReal.ofReal (‖F i t‖ ^ 2)) < ⊤)
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι) (α : JetIndex2 (κ i.1 i.2)) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    PlaneWeakHilbertCurve a b (fun t => planeJetReadoutOperator (κ i.1 i.2) α (u i t))
      (fun t => planeWordH1SliceOperator (κ i.1 i.2) α (w i t))
      (fun t => planeSourceDual (planeJetReadoutOperator (κ i.1 i.2) α (H t))
        (planeJetFluxOperator (κ i.1 i.2) α (S t))) := by
  dsimp only
  let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
  let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
  have hdual := scalarChain_ordered_dual_memLp_of_flux_lower_integral a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i α
  apply plane_ordered_source_curve_of_dual_memLp (u i) H (w i) S
    (hsln.1 i) (hsln.2.1 i)
  · filter_upwards [hsln.2.2.1 i] with t ht
    exact ht.symm
  · intro s hs t ht hst Z
    have hi := scalarChainTrace_increment a b hab κ v G f F u w hsln i hs ht Z
    refine hi.trans ?_
    apply intervalIntegral.integral_congr
    intro r hr
    exact (scalarSobolevSource_pair_eq_raw (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) g hg4 hGnear hGs (w i) (F i) r
      (Set.Icc_subset_Icc hs.1 ht.2 (by simpa only [Set.uIcc_of_le hst] using hr)) Z).symm
  · exact hdual
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Actual homogeneous traces inherit proved bounds on the committed finite approximations. -/

theorem cellActualWeak_native_of_finite_bound {a b : ℝ} (hab : a < b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hk : ∀ t, ‖C.κ t‖ ≤ k)
    (initial : ComplexCellL2) (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) 0 0))
    (hinitial : U a = initial) (J : ℕ) (t : ℝ) (ht : t ∈ Icc a b)
    (B : ℝ) (hB : 0 ≤ B)
    (hfinite : ∀ N (y : ℝ → CellGalerkinSpace (E := ℂ) N),
      StrongTimeRegularity a b y (fun r => cellGalerkinOperator N
        (cellGeneratorB C hG V hv hb r) (y r)) →
      cellGalerkinValue N (y a) = cellGalerkinValue N (cellGalerkinL2Initial N initial) →
      ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤ B) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤ B := by
  obtain ⟨D⟩ := cellGalerkin_actual_limit_data hab.le C hG V k hv hb hκ hk
    0 0 measurable_zero measurable_zero (by simp [cellL2Norm]) (by simp [cellL2Norm]) initial
  obtain ⟨Z, hZ, hi⟩ := D.exists_continuous_trace hab k hκ hk (by apply MemLp.zero) (by apply MemLp.zero)
  have hz : CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv hb t (D.limit t) 0 0) := by
    change CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv hb t (D.limit t)
        (cellSourceSlice 0 t) (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hZ
    simpa only [PiLp.zero_apply, Pi.zero_def, cellSourceSlice_zero] using hZ
  have heq := cellActualWeak_unique hab.le C hG V k hv hb hk 0 0 U
    (extendCurve hab.le Z) slice D.limit hU hz (hinitial.trans hi.symm) t ht
  obtain ⟨W, hwv, hwb⟩ := CellGalerkinLimitData.full_trace_native_of_uniform_bound
    hab.le C hG V k hv hb hκ hk initial D (extendCurve hab.le Z) hz hi J t ht B hB
    (fun N => hfinite N (extendCurve hab.le (D.curve N))
      (CellGalerkinLimitData.full_homogeneous_strongTime hab.le C hG V hv hb initial D N)
      (D.initial_value N))
  exact ⟨W, hwv.trans heq.symm, hwb⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Full transport consumes one higher spatial reserve with a polynomial contrast price. -/

 theorem torusHigherShiftedFirstCLM_adjacent_apply (K : ℕ) (θ : Fin 2 → ℂ) (i : Fin 2)
    (U : TorusHk (K + 2) ℂ) :
    torusHigherShiftedFirstCLM K θ i U = torusHigherBlochDerivativeCLM K θ i
      (truncateTorusHk (by omega : K + 1 ≤ K + 2) U) := by
  simp only [torusHigherShiftedFirstCLM, torusHigherFirstCLM, add_apply,
    ContinuousLinearMap.comp_apply, torusHigherBlochDerivativeCLM_apply, torusHigher_truncate_comp]

 theorem torusHigherShiftedFirstCLM_adjacent_bound (K : ℕ) (θ : Fin 2 → ℂ)
    (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R) (i : Fin 2)
    (U : TorusHk (K + 2) ℂ) :
    ‖torusHigherShiftedFirstCLM K θ i U‖ ≤
      (1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖)) *
        ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖ := by
  rw [torusHigherShiftedFirstCLM_adjacent_apply]
  exact (torusHigherBlochDerivativeCLM_norm_le K θ i _).trans
    (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ))
      (mul_le_mul_of_nonneg_right (hθ i)
        (by positivity : 0 ≤ 1 + ‖torusHigherScalarCLM K Complex.I‖))) (norm_nonneg _))

 def constructedAdvectionAdjacentPrice (K : ℕ) (R : ℝ) : ℝ :=
  2 * constructedEntryUniversalNativePrice K * (1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖))

 theorem constructedHigherAdvectionCLM_adjacent_polynomial_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    ‖constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t U‖ ≤
      (constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) *
        ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖ := by
  have hp : 0 ≤ constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν) :=
    mul_nonneg (constructedEntryUniversalNativePrice_nonneg K) (by unfold peFactor; positivity)
  have hi (i : Fin 2) :
      ‖constructedDriftEntryNativeCLM K hΛ hζ ν y₀ hv i t (torusHigherShiftedFirstCLM K θ i U)‖ ≤
      (constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) *
        ((1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖)) *
          ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖) :=
    (constructedDriftEntryNativeCLM_polynomial_bound K hΛ hζ hν hr y₀ hv i t _).trans
      (mul_le_mul_of_nonneg_left (torusHigherShiftedFirstCLM_adjacent_bound K θ R hθ i U) hp)
  simp only [constructedHigherAdvectionCLM, Fin.sum_univ_two, add_apply, ContinuousLinearMap.comp_apply]
  exact ((norm_add_le _ _).trans (add_le_add (hi 0) (hi 1))).trans_eq
    (by unfold constructedAdvectionAdjacentPrice; ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual higher transverse sources consume coefficient jets only on the relevant time window. -/

section
variable (K : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

def torusHigherTransverseWindowSource (t : ℝ) (U : TorusHk (K + 2) ℂ) : TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K G (fun j => (Real.sqrt η : ℂ) * ξ j) t U -
    torusHigherScalarCLM K Complex.I (torusNormalizedDriftWindowMultiplier a b η hv ξ hc A hA hb t
      (truncateTorusHk (by omega : K ≤ K + 2) U)) +
    torusHigherScalarCLM K (κ t) (truncateTorusHk (by omega : K ≤ K + 2) U)

theorem torusHigherTransverseWindowSource_memLp (hG : IsCellMetric (fun t _ => G t))
    (hκ : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (U : ℝ → TorusHk (K + 2) ℂ) (hU : MemLp U 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => torusHigherTransverseWindowSource K a b η G hv ξ hc A hA hb κ t (U t)) 2
      (volume.restrict (Icc a b)) := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  have hbase : MemLp (fun t => truncateTorusHk (by omega : K ≤ K + 2) (U t)) 2
      (volume.restrict (Icc a b)) :=
    (truncateTorusHk (E := ℂ) (K := K) (L := K + 2) (by omega)).comp_memLp' hU
  have hdiff := torusHigherStrongDiffusion_memLp K G hG
    (fun j => (Real.sqrt η : ℂ) * ξ j) U hU
  have hmul := torusNormalizedDriftWindowMultiplier_memLp a b η hv ξ hc A hA hb _ hbase
  have hcoupling := (torusHigherScalarCLM K Complex.I).comp_memLp' hmul
  have hpotential := torusHigherScalar_time_memLp K κ hκ _ hbase
  change MemLp (fun t => torusHigherStrongDiffusionCLM K G
    (fun j => (Real.sqrt η : ℂ) * ξ j) t (U t) -
    torusHigherScalarCLM K Complex.I (torusNormalizedDriftWindowMultiplier a b η hv ξ hc A hA hb t
      (truncateTorusHk (by omega : K ≤ K + 2) (U t))) +
    torusHigherScalarCLM K (κ t) (truncateTorusHk (by omega : K ≤ K + 2) (U t))) 2 _
  apply MemLp.add
  · exact hdiff.sub hcoupling
  · exact hpotential

theorem torusHigherTransverseWindowSource_value (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (t : ℝ) (ht : t ∈ Icc a b) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (torusHigherTransverseWindowSource K a b η G hv ξ hc A hA hb κ t U) =
      cellTransverseStrongSource η Cw hCw G hv hw ξ κ t
        (truncateTorusHk (by omega : 2 ≤ K + 2) U) := by
  rw [torusHigherTransverseWindowSource, map_add, map_sub,
    torusHigherStrongDiffusionCLM_value, torusHigherScalarCLM_value,
    torusHigherScalarCLM_value, torusNormalizedDriftWindowMultiplier_value a b η hv ξ hc A hA hb
      Cw hCw hw t ht]
  rfl
end

/-! Actual higher transverse sources consume coefficient jets only on the relevant time window. -/

section
variable (K : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

def torusHigherTransverseWindowSourceCLM (t : ℝ) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K G (fun j => (Real.sqrt η : ℂ) * ξ j) t -
    (torusHigherScalarCLM K Complex.I).comp
      ((torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t).comp
        (truncateTorusHk (by omega : K ≤ K + 2))) +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

theorem torusHigherTransverseWindowSourceCLM_apply (t : ℝ) (u : TorusHk (K + 2) ℂ) :
    torusHigherTransverseWindowSourceCLM K a b η G hv ξ hc A hA hb κ t u =
      torusHigherTransverseWindowSource K a b η G hv ξ hc A hA hb κ t u := rfl
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual package symbol is uniformly quadratic for every complex low frequency. -/

local instance scalarPackageSymbolQuadraticBoundProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem scalarPackageSymbol_quadratic_bound {K : ScalarConstants} {η t0 S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    ‖fibreSeriesC data.lam ξ t‖ ≤ (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 := by
  let D := fibreSeriesJet data.r ξ
  let b := fibreDriftCoupling η v ξ t
  have hd : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube) :=
    (scalarPackageGraph_memLp data ξ hξ t)
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)
  have hB := fibreDriftCoupling_norm_le η K.Cw v hw ξ t
  have hm := cellMultiplier_memLp b (cellValue D t) (K.Cw * fibreNorm ξ) hb hB hd
  have hnmean := (cellMean_enorm_le_cellL2Norm _ hm).trans
    ((cellL2Norm_mul_le b (cellValue D t) (K.Cw * fibreNorm ξ)
      (hb.aestronglyMeasurable.mul hd.aestronglyMeasurable)
      (Filter.Eventually.of_forall hB)).trans
      (mul_le_mul' le_rfl ((cellValue_cellL2Norm_le_energy D t).trans
        (data.graph.2.1 ξ hξ).2.2.2.2)))
  have hn : ‖cellMean (fun x => b x * cellValue D t x)‖ ≤
      (K.Cw * fibreNorm ξ) * (K.Cg * fibreNorm ξ) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul
      (mul_nonneg hCw (fibreNorm_nonneg ξ))] at hnmean
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ))
        (mul_nonneg hCg (fibreNorm_nonneg ξ)))).mp hnmean
  have hq := fibreQuad_norm_le_eight (G t)
    (fun i j => cellMetric_entry_bound hG t 0 i j) ξ
  have hηn : ‖(η : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0] using hη1
  rw [(data.graph.2.1 ξ hξ).2.2.2.1 t]
  calc
    _ ≤ ‖-(η : ℂ) * fibreQuad (G t) ξ‖ +
      ‖Complex.I * cellMean (fun x => b x * cellValue D t x)‖ := norm_sub_le _ _
    _ ≤ 8 * fibreNorm ξ ^ 2 + (K.Cw * fibreNorm ξ) * (K.Cg * fibreNorm ξ) := by
      apply add_le_add
      · rw [norm_mul, norm_neg]
        exact (mul_le_mul hηn hq (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simpa only [norm_mul, Complex.norm_I, one_mul] using hn
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Quadratic symbol control follows from the genuine graph, before a scalar package exists. -/

local instance fibreGraphSymbolQuadraticBoundProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem fibreGraph_symbol_quadratic_bound {η ξ₀ Cg Cw : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hCg : 0 ≤ Cg) (hCw : 0 ≤ Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀) (t : ℝ) :
    ‖fibreSeriesC lam ξ t‖ ≤ (8 + Cw * Cg) * fibreNorm ξ ^ 2 := by
  let D := fibreSeriesJet r ξ
  let b := fibreDriftCoupling η v ξ t
  have hd : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube) :=
    ((((hgraph.2.1 ξ hξ).2.2.1).1.2.2.1 t (Set.mem_univ t)).1)
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ t
  have hm := cellMultiplier_memLp b (cellValue D t) (Cw * fibreNorm ξ) hb hB hd
  have hnmean := (cellMean_enorm_le_cellL2Norm _ hm).trans
    ((cellL2Norm_mul_le b (cellValue D t) (Cw * fibreNorm ξ)
      (hb.aestronglyMeasurable.mul hd.aestronglyMeasurable)
      (Filter.Eventually.of_forall hB)).trans
      (mul_le_mul' le_rfl ((cellValue_cellL2Norm_le_energy D t).trans
        (hgraph.2.1 ξ hξ).2.2.2.2)))
  have hn : ‖cellMean (fun x => b x * cellValue D t x)‖ ≤
      (Cw * fibreNorm ξ) * (Cg * fibreNorm ξ) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul
      (mul_nonneg hCw (fibreNorm_nonneg ξ))] at hnmean
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ))
        (mul_nonneg hCg (fibreNorm_nonneg ξ)))).mp hnmean
  have hq := fibreQuad_norm_le_eight (G t)
    (fun i j => cellMetric_entry_bound hG t 0 i j) ξ
  have hηn : ‖(η : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0] using hη1
  rw [(hgraph.2.1 ξ hξ).2.2.2.1 t]
  calc
    _ ≤ ‖-(η : ℂ) * fibreQuad (G t) ξ‖ +
      ‖Complex.I * cellMean (fun x => b x * cellValue D t x)‖ := norm_sub_le _ _
    _ ≤ 8 * fibreNorm ξ ^ 2 + (Cw * fibreNorm ξ) * (Cg * fibreNorm ξ) := by
      apply add_le_add
      · rw [norm_mul, norm_neg]
        exact (mul_le_mul hηn hq (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simpa only [norm_mul, Complex.norm_I, one_mul] using hn
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! The actual moving-centre renewal transfers polynomial factorial energies with a uniform constant. -/

theorem cellTransition_polynomial_factorial_energy_uniform (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l₀ : ℤ) (y₀ : Vec 2) (i : ℕ) (ϖ : ℝ) (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K Kmax : ℕ} (hK : K ≤ Kmax) (U V : AVRegularity.Sobolev.PlaneHk Set.univ K E)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : planeValue V =ᵐ[volume] fun z => planeValue U
      (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i + 1)) z)) :
    weightedFactorialNormSq n ϖ 0 r K V ≤
      ENNReal.ofReal (uniformPullbackSquareBudget cellTransitionJetBudget Kmax *
        (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ n) *
        weightedFactorialNormSq n ϖ 0 r K U := by
  let he := (Scales.epsilon_basic (m := m) hq.1 hΛ).1.ne'
  let X := cellTransitionHomeomorph α q Λ m hφ (l₀ + i)
    (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
    (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i + 1)) he
  have hX : MeasurePreserving X volume volume :=
    cellTransition_measurePreserving α q Λ m hφ _ _ _ he
  have hL := cellTransition_inverse_lipschitz α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hseq m hm hφ (l₀ + i)
    (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
    (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i + 1))
  have h0 : X 0 = 0 := cellTransition_centre_zero α q Λ m hφ l₀ y₀ i
  have hs : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2) :=
    cellTransition_contDiff α q Λ m hφ _ _ _
  have hj : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ cellTransitionJetBudget j := by
    intro j hj _ z
    exact cellTransition_uniform_jet_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
      Φ hseq m hm hφ _ _ _ j hj z
  exact centredSobolev_pullback_energy_uniform hK U V X hs hX cellTransitionJetBudget hj hv
    _ hL h0 r hr hr1 ϖ n

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A single transport price covers every reserved polynomial moment. -/

def cellTransitionMomentBudget (Kmax M : ℕ) : ℝ :=
  1 + uniformPullbackSquareBudget cellTransitionJetBudget Kmax *
    (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ M

theorem cellTransitionMomentBudget_ge_one (Kmax M : ℕ) : 1 ≤ cellTransitionMomentBudget Kmax M := by
  unfold cellTransitionMomentBudget
  exact le_add_of_nonneg_right (mul_nonneg (uniformPullbackSquareBudget_nonneg _ _) (by positivity))

theorem cellTransition_polynomial_factorial_energy_reserved (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l₀ : ℤ) (y₀ : Vec 2) (i : ℕ) (ϖ : ℝ) (n M : ℕ) (hn : n ≤ M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K Kmax : ℕ} (hK : K ≤ Kmax) (U V : AVRegularity.Sobolev.PlaneHk Set.univ K E)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : planeValue V =ᵐ[volume] fun z => planeValue U
      (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i + 1)) z)) :
    weightedFactorialNormSq n ϖ 0 r K V ≤
      ENNReal.ofReal (cellTransitionMomentBudget Kmax M) *
        weightedFactorialNormSq n ϖ 0 r K U := by
  have hh := cellTransition_polynomial_factorial_energy_uniform α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hseq m hm hφ l₀ y₀ i ϖ n hK U V r hr hr1 hv
  have hp : (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ n ≤
      (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ M :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity : 0 ≤ 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2)) hn
  have hc : uniformPullbackSquareBudget cellTransitionJetBudget Kmax *
      (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ n ≤ cellTransitionMomentBudget Kmax M := by
    exact (mul_le_mul_of_nonneg_left hp (uniformPullbackSquareBudget_nonneg _ _)).trans
      (le_add_of_nonneg_left zero_le_one)
  exact hh.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual higher transverse sources consume coefficient jets only on the relevant time window. -/

section
variable (K : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

theorem torusHigherTransverseWindowSourceCLM_uniform_bound
    (hG : IsCellMetric (fun t _ => G t)) (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
      ‖torusHigherTransverseWindowSourceCLM K a b η G hv ξ hc A hA hb κ t‖ ≤ D := by
  obtain ⟨D, hD, hd⟩ := torusHigherStrongDiffusionCLM_uniform_bound K G hG
    (fun j => (Real.sqrt η : ℂ) * ξ j)
  obtain ⟨M, hM, hm⟩ := torusNormalizedDriftWindowMultiplierCLM_uniform_bound a b η hv ξ hc A hA hb
  let T : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
    truncateTorusHk (E := ℂ) (K := K) (L := K + 2) (by omega)
  let I := torusHigherScalarCLM K Complex.I
  have hk : 0 ≤ k := (norm_nonneg (κ 0)).trans (hκ 0)
  refine ⟨D + ‖I‖ * (M * ‖T‖) + (k * (1 + ‖I‖)) * ‖T‖, by positivity, ?_⟩
  intro t
  have hmT : ‖(torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t).comp T‖ ≤ M * ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hm t) (norm_nonneg _))
  have hIM : ‖I.comp ((torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t).comp T)‖ ≤
      ‖I‖ * (M * ‖T‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hmT (norm_nonneg _))
  have hκT : ‖(torusHigherScalarCLM K (κ t)).comp T‖ ≤ (k * (1 + ‖I‖)) * ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      (torusHigherScalarCLM_norm_le K (κ t) k (hκ t)) (norm_nonneg _))
  let F := torusHigherStrongDiffusionCLM K G (fun j => (Real.sqrt η : ℂ) * ξ j) t
  let M' := I.comp ((torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t).comp T)
  let P' := (torusHigherScalarCLM K (κ t)).comp T
  change ‖F - M' + P'‖ ≤ _
  exact (norm_add_le (F - M') P').trans (add_le_add
    ((norm_sub_le F M').trans (add_le_add (hd t) hIM)) hκT)
end

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

section
variable (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
  (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

def cellTransverseGalerkinOperator (t : ℝ) :
    CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N :=
  (cellGalerkinL2InitialCLM N).comp ((torusHkValueCLM (E := ℂ) (K := 0)).comp
    ((torusHigherTransverseWindowSourceCLM 0 a b η G hv ξ hc A hA hb κ t).comp
      (cellGalerkinHigherStateCLM N 1)))

theorem cellTransverseGalerkinOperator_image_memLp
    (hG : IsCellMetric (fun t _ => G t)) (hκ : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (u : CellGalerkinSpace (E := ℂ) N) :
    MemLp (fun t => cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u) 2
      (volume.restrict (Icc a b)) := by
  let : NormedAddCommGroup (TorusHk 2 ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk 0 ℂ) := inferInstance
  let : NormedAddCommGroup ComplexCellL2 := inferInstance
  let : NormedAddCommGroup (CellGalerkinSpace (E := ℂ) N) := inferInstance
  simp only [cellTransverseGalerkinOperator, ContinuousLinearMap.comp_apply,
    torusHigherTransverseWindowSourceCLM_apply]
  have hU : MemLp (fun _ : ℝ => cellGalerkinHigherStateCLM N 1 u) 2
      (volume.restrict (Icc a b)) :=
    continuousOn_memLp_Icc _ continuousOn_const
  have hs := torusHigherTransverseWindowSource_memLp 0 a b η G hv ξ hc A hA hb κ hG hκ _ hU
  exact (cellGalerkinL2InitialCLM N).comp_memLp'
    ((torusHkValueCLM (E := ℂ) (K := 0)).comp_memLp' hs)

theorem cellTransverseGalerkinOperator_aestronglyMeasurable
    (hG : IsCellMetric (fun t _ => G t)) (hκ : MemLp κ ⊤ (volume.restrict (Icc a b))) :
    AEStronglyMeasurable (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)
      (volume.restrict (Icc a b)) := by
  apply finiteOperator_aestronglyMeasurable (Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N))
  intro i
  exact (cellTransverseGalerkinOperator_image_memLp N a b η G hv ξ hc A hA hb κ hG hκ _).aestronglyMeasurable
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! The actual moving-centre renewal transfers polynomial factorial energies with a uniform constant. -/

theorem cellTransition_family_data_norm (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l₀ : ℤ) (y₀ : Vec 2) (i : ℕ) (ϖ : ℝ) (n : ℕ)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, InnerProductSpace ℝ (h x)]
    [∀ x, FiniteDimensional ℝ (h x)] [∀ x, MeasurableSpace (h x)]
    [∀ x, BorelSpace (h x)] [∀ x, CompleteSpace (h x)]
    (π : ι → ℝ) (Kslot : ι → ℕ) (Kmax : ℕ) (hK : ∀ x, Kslot x ≤ Kmax)
    (U V : ∀ x, AVRegularity.Sobolev.PlaneHk Set.univ (Kslot x) (h x))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : ∀ x, planeValue (V x) =ᵐ[volume] fun z => planeValue (U x)
      (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i + 1)) z)) :
    geometryDataNorm π Kslot n ϖ 0 r V ≤
      ENNReal.ofReal ((uniformPullbackSquareBudget cellTransitionJetBudget Kmax *
        (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ n) ^ (1 / 2 : ℝ)) *
        geometryDataNorm π Kslot n ϖ 0 r U := by
  apply geometryDataNorm_component_budget π Kslot n ϖ 0 r U V
  · exact mul_nonneg (uniformPullbackSquareBudget_nonneg _ _) (by positivity)
  · intro x
    exact cellTransition_polynomial_factorial_energy_uniform α s hα₀ hα₁ hs₀ hs₁ q hq
      ζ hζ Λ hΛ Φ hseq m hm hφ l₀ y₀ i ϖ n (hK x) (U x) (V x) r hr hr1 (hv x)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

variable (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
  (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

theorem cellTransverseGalerkinOperator_pairing (t : ℝ)
    (u z : CellGalerkinSpace (E := ℂ) N) :
    inner ℝ (cellGalerkinValue N (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
      (cellGalerkinValue N z) =
    inner ℝ (torusHkValueCLM (torusHigherTransverseWindowSource 0 a b η G hv ξ hc A hA hb κ t
      (cellGalerkinHigherStateCLM N 1 u))) (cellGalerkinValue N z) := by
  simp only [cellTransverseGalerkinOperator, ContinuousLinearMap.comp_apply,
    torusHigherTransverseWindowSourceCLM_apply, cellGalerkinL2InitialCLM_apply]
  exact cellGalerkinL2Initial_pairing N _ z

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Local complete-core drops for the actual raw solutions used by interior marks. -/

open AVRegularity.CycleDamping

theorem constructed_core_raw_contraction_time (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d : ℝ, 0 < d ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (_hG : IsCellMetric (fun t _ => G t))
        (_hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (_hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Vec 2), (∀ i, |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i| ≤ Real.pi) →
      ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2) →
      ∀ j : Fin 2, ξlo / 2 ≤ |ξ j| →
      ∀ (a b : ℝ), a ≤ b → d ≤ b - a →
      ∀ (l n : ℤ), IsOCCompleteCore α q Λ m l n →
      n % 4 = (if j = 0 then 3 else 1) →
      (∀ t ∈ Icc a b, ocEll q Λ m ν ^ 2 * t ∈
        Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m)) →
      ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Icc a b)
          (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
            (ocCellDrift α q Λ ζ m ν y₀) (fun i => (ξ i : ℂ)) (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellValue D b) ≤ ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D a) := by
  obtain ⟨d, hd, hdrop⟩ := complete_core_contraction_time ξlo hlo
  refine ⟨d, hd, ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hθ hξ j hj a b hab hlong l n hcore hn hinside D h
  have hh := h
  rw [real_fibre_coefficients] at hh
  have hw := raw_homogeneous_weak_curve hab (fun t _ => G t) hG
    (ocCellDrift α q Λ ζ m ν y₀) V hv.1 hb _ D hh
  have he := hdrop α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hθ hξ j hj
    a b hab hlong l n hcore hn hinside (cellRawTrace D) (cellH1Slice D) hw
  rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D _ (h.2.2.1 _ ⟨hab, le_rfl⟩).1),
    cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D _ (h.2.2.1 _ ⟨le_rfl, hab⟩).1)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ENNReal.ofReal_le_ofReal he

end AVRegularity.CycleWords
end
end
