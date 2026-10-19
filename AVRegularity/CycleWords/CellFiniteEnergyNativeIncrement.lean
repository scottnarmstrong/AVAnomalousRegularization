-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedNormalizedSpatialJets
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.CycleDamping.ReferenceSourceMode
public import AVRegularity.CycleEvolution.CellWeakProjectedFeedbackDecay
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_scalarSobolevSource_word_residual_ae {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (hCell : IsCellMetric G)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb)
    (hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (α : JetIndex2 K) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := cellMetricIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      hCell
    (planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) =ᵐ[volume]
      (fun x => -planeDriftCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        (v t) (W t).toFunction.jet α.2 x) ∧
    (∀ k : Fin 2, (planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) k =ᵐ[volume]
      fun x => metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        (G t) (W t).toFunction.jet α.2 x k + (F t).val α x k) := by
  let τ := Set.projIcc ta tb hab t
  dsimp only
  constructor
  · have hd := scalarDriftCarrier_word_residual_ae hK
      (planeIntervalCoefficient ta tb hab v t) (hv τ τ.property) V (hbv τ τ.property)
      strain B lam (hjets τ τ.property)
      (planeIntervalVelocity_continuous ta tb hab v
        (fun r hr => (hv r hr).continuous) t) (max V 0) (le_max_right _ _)
      (planeIntervalVelocity_bound ta tb hab v V hbv t) (W t) α
    refine hd.trans (Filter.Eventually.of_forall (fun x => ?_))
    rw [planeIntervalCoefficient_of_mem ta tb hab v t ht]
  · intro k
    have hd := scalarMetricCarrier_word_residual_ae
      (planeIntervalCoefficient ta tb hab G t) (hG τ τ.property) M (hb τ τ.property)
      (planeIntervalMetric_continuous ta tb hab G
        (fun r hr k j => (hG1 r hr k j).continuous) t) 2 (by norm_num)
      (cellMetricInterval_entry_bound ta tb hab G hCell t) (W t) α (F t) k
    refine hd.trans (Filter.Eventually.of_forall (fun x => ?_))
    rw [planeIntervalCoefficient_of_mem ta tb hab G t ht]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Unscaled transport coefficients retain their genuine finite spatial jet prices. -/

 def constructedDriftEntryCoefficient (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (ν : ℝ) (y₀ : Vec 2) (i : Fin 2) (t : ℝ) (x : Vec 2) : ℂ →L[ℝ] ℂ :=
  realScalarMultiplierMap (ocCellDrift α q Λ ζ m ν y₀ t x i)

 def constructedDriftEntryJetPrice (α q : ℝ) (Λ m : ℕ) (ν : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖ *
    (|2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| * (2 * Real.pi) ^ n)

 theorem constructedDriftEntryCoefficient_contDiff
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (i : Fin 2) (t : ℝ) (n : ℕ) :
    ContDiff ℝ (n : ℕ) (constructedDriftEntryCoefficient α q Λ m ζ ν y₀ i t) := by
  have hv : ContDiff ℝ (n : ℕ) (ocCellDrift α q Λ ζ m ν y₀ t) := (constructed_spatial_contDiff hΛ hζ ν y₀ t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  exact realScalarMultiplierMap.contDiff.comp ((contDiff_apply ℝ ℝ i).comp hv)

 theorem constructedDriftEntryCoefficient_periodic
    (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (y₀ : Vec 2)
    (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (i : Fin 2) (t : ℝ) :
    IsZ2Periodic (constructedDriftEntryCoefficient α q Λ m ζ ν y₀ i t) := by
  intro k x
  unfold constructedDriftEntryCoefficient
  rw [hv.2.2.1 t k x]

 theorem constructedDriftEntryCoefficient_array_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (i : Fin 2) (t : ℝ) (n : ℕ) (x : Vec 2) :
    ‖coefficientDerivativeArray (constructedDriftEntryCoefficient α q Λ m ζ ν y₀ i t) n x‖ ≤
      constructedDriftEntryJetPrice α q Λ m ν n := by
  have hv : ContDiff ℝ (n : ℕ) (fun x => ocCellDrift α q Λ ζ m ν y₀ t x i) := by
    simpa only [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp
      ((constructed_spatial_contDiff hΛ hζ ν y₀ t).of_le (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)))
  have hb := realScalarMultiplier_jet_array_bound _ n hv x
  exact hb.trans (mul_le_mul_of_nonneg_left
    (constructed_spatial_component_jet_bound hΛ hζ ν y₀ t i n x) (by positivity))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Unscaled constructed transport jets have a linear contrast price at every order. -/

 theorem constructed_amplitude_polynomial_price
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) :
    |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| ≤
      constructedSpatialJetPrice 0 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
  have hB : 0 < ocMeanFlux α q Λ ζ m ν :=
    hν.trans_le (CycleReference.meanFlux_ge_input hΛ hζ hν)
  have hη : 0 < Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) :=
    Real.sqrt_pos.mpr (div_pos hν hB)
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : 0 ≤ 2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
    unfold ocA
    positivity
  have hs : Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| ≤ constructedSpatialJetPrice 0 := by
    rw [abs_of_nonneg ha]
    have hb := mul_le_mul_of_nonneg_left
      (CycleDamping.corrector_amplitude_bound (α := α) (q := q) (m := m) hΛ hζ hν hr)
      (by positivity : 0 ≤ 2 * Real.pi)
    simp only [constructedSpatialJetPrice, pow_zero, mul_one]
    convert hb using 1; ring
  have hd : |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| ≤
      constructedSpatialJetPrice 0 / Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) :=
    (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hs)
  apply hd.trans
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (constructedSpatialJetPrice_nonneg 0)
  unfold peFactor
  exact le_add_of_nonneg_left (by norm_num)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Each original jet coordinate of smooth Bloch diffusion has its genuine H2 readout. -/

 theorem finiteSmoothDiffusion_jet_coordinate (K : ℕ) (a : JetIndex2 K)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ) :
    (torusHigherStrongDiffusionCLM K G θ t
      (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (by simp)) hp)).val a =
      cellConstantMetricStrongDiffusionCLM G θ t
        (finiteSmoothPeriodicHk 2 (orderedDerivative a.2 f)
          (orderedDerivative_contDiff a.2 2 f (hf.of_le (by simp)))
          (orderedDerivative_periodic a.2 f (hf.of_le (by simp)) hp)) := by
  rw [← torusHigher_jet_coordinate a,
    torusHigherStrongDiffusionCLM_truncate, finiteSmoothPeriodicHk_truncate (f := f) (hf := hf)]
  exact finiteSmoothPeriodicHk_diffusion_derivative_strong_value (K := 0) a.2 f hf hp G θ t

 theorem finiteSmoothValue_jet_coordinate (K : ℕ) (a : JetIndex2 K)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    (finiteSmoothPeriodicHk K f (hf.of_le (by simp)) hp).val a =
      torusHkValueCLM (finiteSmoothPeriodicHk 2 (orderedDerivative a.2 f)
        (orderedDerivative_contDiff a.2 2 f (hf.of_le (by simp)))
        (orderedDerivative_periodic a.2 f (hf.of_le (by simp)) hp)) := by
  rw [← torusHigher_jet_coordinate a, finiteSmoothPeriodicHk_truncate (f := f) (hf := hf)]
  rw [finiteSmoothPeriodicHk_derivative (K := 0) a.2 f (hf.of_le (by simp)) hp]
  apply Lp.ext
  have hl := finiteSmoothPeriodicHk_jet_ae 0 (orderedDerivative a.2 f)
    (orderedDerivative_contDiff a.2 0 f (hf.of_le (by simp)))
    (orderedDerivative_periodic a.2 f (hf.of_le (by simp)) hp) (valueIndex2 0)
  have hr := finiteSmoothPeriodicHk_jet_ae 2 (orderedDerivative a.2 f)
    (orderedDerivative_contDiff a.2 2 f (hf.of_le (by simp)))
    (orderedDerivative_periodic a.2 f (hf.of_le (by simp)) hp) (valueIndex2 2)
  exact hl.trans hr.symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleWords

/-! Smoothness, periodicity, zero mean and weak divergence freedom of the actual pulse extension. -/

theorem interiorSinglePulseDrift_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) :
    Continuous (fun p : ℝ × Vec 2 => interiorSinglePulseDrift α q Λ ζ m ν y₀ k p.1 p.2) := by
  apply continuous_pi
  intro i
  have hp : Continuous (fun p : ℝ × Vec 2 =>
      ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1)) :=
    (CycleReference.ocPulse_continuous hζ k).comp (by fun_prop)
  have hs := (CycleDamping.cell_shear_component_contDiff (α := α) (q := q)
    (Λ := Λ) (m := m) hk y₀ i).continuous.comp (continuous_snd : Continuous (Prod.snd : ℝ × Vec 2 → Vec 2))
  change Continuous (fun p : ℝ × Vec 2 => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
    (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * p.1) *
      ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • p.2) i))
  exact continuous_const.mul (hp.mul hs)

theorem interiorSinglePulseDrift_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (interiorSinglePulseDrift α q Λ ζ m ν y₀ k t) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_const.mul
    (CycleDamping.cell_shear_component_contDiff hk y₀ i))

theorem interiorSinglePulseDrift_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (t : ℝ) :
    IsZ2Periodic (interiorSinglePulseDrift α q Λ ζ m ν y₀ k t) := by
  intro n z
  ext i
  simp only [interiorSinglePulseDrift, Pi.smul_apply, smul_eq_mul]
  have he := CycleDamping.cell_shear_component_periodic
    (α := α) (q := q) (m := m) hΛ hk y₀ i n z
  exact congrArg (fun r : ℝ => ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
    (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) * r)) he

theorem interiorSinglePulseDrift_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (t : ℝ) (j : Fin 2) :
    cellMean (fun z => (interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z j : ℂ)) = 0 := by
  rw [cellMean, integral_complex_ofReal]
  simp only [interiorSinglePulseDrift, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
  rw [integral_const_mul, CycleDamping.cell_shear_mean_zero hΛ hk, mul_zero]
  rfl

theorem interiorSinglePulseDrift_weak_divergence {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (ψ : AVRegularity.Sobolev.TorusHkFunction 1 ℝ) :
    (∫ x in unitCube, ∑ i : Fin 2, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x i *
      ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) = 0 := by
  have hweak := CycleDamping.smooth_divergence_free_weak
    (fun z => ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z))
    (CycleDamping.cell_shear_component_contDiff hk y₀)
    (CycleDamping.cell_shear_component_periodic hΛ hk y₀)
    (fun x => by simp_rw [CycleDamping.cell_shear_diagonal_derivative_zero hk]; simp) ψ
  simp only [interiorSinglePulseDrift, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_assoc (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
    ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)), ← Finset.mul_sum]
  rw [integral_const_mul, hweak, mul_zero]

/-! Every pulse extension inherits the full drift's bound without an increased scaled price. -/

theorem interiorSinglePulseDrift_eq_actual_or_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (t : ℝ) :
    interiorSinglePulseDrift α q Λ ζ m ν y₀ k t = ocCellDrift α q Λ ζ m ν y₀ t ∨
      interiorSinglePulseDrift α q Λ ζ m ν y₀ k t = 0 := by
  by_cases hp : ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0
  · right
    funext z
    simp only [interiorSinglePulseDrift, hp, zero_smul, smul_zero, Pi.zero_apply]
  · left
    funext z
    simp only [interiorSinglePulseDrift, ocCellDrift,
      CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp]

theorem interiorSinglePulseDrift_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (V : ℝ) (hb : ∀ t z, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t z i ^ 2 ≤ V ^ 2) :
    ∀ t z, ∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z i ^ 2 ≤ V ^ 2 := by
  intro t z
  rcases interiorSinglePulseDrift_eq_actual_or_zero hΛ hζ ν y₀ hk t with he | he
  · rw [he]
    exact hb t z
  · simp only [he, Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    exact sq_nonneg V

theorem interiorSinglePulseDrift_scaled_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t z, Real.sqrt η * Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t z i ^ 2) ≤ Cw) :
    ∀ t z, Real.sqrt η * Real.sqrt
      (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z i ^ 2) ≤ Cw := by
  intro t z
  rcases interiorSinglePulseDrift_eq_actual_or_zero hΛ hζ ν y₀ hk t with he | he
  · rw [he]
    exact hw t z
  · simpa only [he, Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, Real.sqrt_zero, mul_zero] using hCw

theorem interiorSinglePulseDrift_isCellDrift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) :
    IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k) := by
  obtain ⟨V, hb⟩ := hv.2.1
  exact ⟨(interiorSinglePulseDrift_joint_continuous hζ ν y₀ hk).measurable,
    ⟨V, interiorSinglePulseDrift_bound hΛ hζ ν y₀ hk V hb⟩,
    interiorSinglePulseDrift_periodic hΛ ν y₀ hk,
    fun t ψ => interiorSinglePulseDrift_weak_divergence hΛ ν t y₀ hk ψ⟩

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution AVRegularity.CycleDamping
namespace AVRegularity.CycleWords

/-! Brillouin dissipation controls the mean-free part of every Fourier approximant. -/

theorem projected_meanFree_shifted_sharp_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) (N : ℕ) :
    Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2 ≤
      ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2 := by
  let p := galerkinProj N u
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hq : ContDiff ℝ 1 q := (smoothFourierJet_contDiff N u _).of_le (by simp)
  have hp : AVenhance.IsZ2Periodic q := smoothFourierJet_periodic N u _
  have hq0 : ContDiff ℝ 1 (cellQ0 q) := hq.sub contDiff_const
  have hp0 : AVenhance.IsZ2Periodic (cellQ0 q) := by
    intro n x; dsimp only [cellQ0]; rw [hp n x]
  have hval : torusHkValueCLM p =ᵐ[volume.restrict AVenhance.unitCube] q :=
    galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hm : cellMean (torusHkValueCLM p) = cellMean q := integral_congr_ae hval
  have hQ : cellQ0CLM (torusHkValueCLM p) =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 q := by
    filter_upwards [cellQ0CLM_ae (torusHkValueCLM p), hval] with x hx hv
    rw [hx]; dsimp only [cellQ0]; rw [hv, hm]
  have hz : (∫ x in unitCell 2, cellQ0 q x) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact cellQ0_mean (smoothFourierJet_memLp (L := 1) N u (valueIndex2 1))
  have hs (j : Fin 2) : cellQ0CLM (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p) =ᵐ[
      volume.restrict AVenhance.unitCube] smoothShiftedDerivative θ j (cellQ0 q) := by
    filter_upwards [cellQ0CLM_ae (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p),
      projected_shifted_derivative_ae θ u N j] with x hx hd
    rw [hx]; dsimp only [cellQ0]
    rw [hd, cellShiftedDerivative_mean, hm]
    dsimp only [smoothShiftedDerivative, coordDeriv, cellQ0]
    have hdq : fderiv ℝ (cellQ0 q) x = fderiv ℝ q x := by
      change fderiv ℝ (fun y => q y - cellMean q) x = fderiv ℝ q x
      exact fderiv_sub_const _
    rw [hdq]
    dsimp only [q]
    ring
  have hl : (∫ x in unitCell 2, ‖cellQ0 q x‖ ^ 2) =
      ‖cellQ0CLM (torusHkValueCLM p)‖ ^ 2 := by
    rw [integral_unitCell_eq_unitCube, ← cellL2_norm_sq_integral]
    exact integral_congr_ae (hQ.mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm))
  have he (j : Fin 2) : (∫ x in unitCell 2, ‖smoothShiftedDerivative θ j (cellQ0 q) x‖ ^ 2) =
      ‖cellQ0CLM (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)‖ ^ 2 := by
    rw [integral_unitCell_eq_unitCube, ← cellL2_norm_sq_integral]
    exact integral_congr_ae ((hs j).mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm))
  have hg := smoothShiftedGradient_meanZero_gap θ hθ hq0 hp0 hz
  rw [hl] at hg
  simp_rw [he] at hg
  apply hg.trans
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _)
    (cellQ0CLM_norm_le_one (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)) 2

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Mean-free shifted-gradient control for arbitrary weak H¹ cell fields. -/

theorem cellH1_meanFree_shifted_sharp_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) :
    Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2 ≤
      ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2 := by
  have hp := galerkinProj_tendsto u
  have hl : Tendsto (fun N => Real.pi ^ 2 *
      ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2) atTop
      (𝓝 (Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2)) := tendsto_const_nhds.mul
    (((cellQ0CLM.comp torusHkValueCLM).continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  have hr : Tendsto (fun N => ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2) atTop
      (𝓝 (∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro j _
    exact (((cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  exact le_of_tendsto_of_tendsto' hl hr (projected_meanFree_shifted_sharp_gap θ hθ u)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_scalarSobolevSource_word_energy_readout {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (hCell : IsCellMetric G)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb)
    (hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (U : PlaneHk Set.univ K E) (hU : U = truncatePlaneHk (Nat.le_succ K) (W t))
    (ρ : ℝ) (q : Vec 2 → ℝ) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := cellMetricIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      hCell
    let R := fun α : JetIndex2 K => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let L := fun α : JetIndex2 K => planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * (‖R α x‖ * ‖planeJetReadoutOperator K α U x‖))) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x *
          (‖planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) (v t)
            (W t).toFunction.jet w x‖ *
            ‖(W t).toFunction.jet ⟨⟨j.val, by omega⟩, w⟩ x‖))) ∧
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x *
          ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t)
            (W t).toFunction.jet w x + (F t).toFunction.jet ⟨j, w⟩ x‖ ^ 2)) := by
  dsimp only
  have hr (α : JetIndex2 K) := cellMetric_scalarSobolevSource_word_residual_ae hK hab v hv
    V strain B lam hbv hjets G hG M hb hCell W F t ht hG1 α
  constructor
  · rw [storedWord_sum_weighted (fun j : Fin (K + 1) => factorialWeight ρ j.val)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    apply weightedValueProduct_readout q _ _ _ _ (hr ⟨j, w⟩).1
    rw [hU, planeWord_truncate_value, planeWordH1Slice_value]
    exact AVRegularity.Analysis.Convolution.univToPlane_ae _
  · rw [storedWord_sum_weighted (fun j : Fin (K + 1) => factorialWeight ρ j.val)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    apply weightedFluxEnergy_readout q _ _
    intro k
    exact (hr ⟨j, w⟩).2 k

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Zero native source classes give an actual homogeneous weak curve. -/

theorem cellFiniteEnergyHomogeneousCurve {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (f : ComplexCellL2) (z : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb (f, 0, 0) z) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative C hG V hv hb t (slice t) 0 0) ∧
      u a = f ∧ ∀ t : CellCompactTime a b, z.val.1 t = u t.val := by
  obtain ⟨u, slice, hu, hi, ht⟩ := hz
  refine ⟨u, slice, hu.dual_congr ?_, hi, ht⟩
  have he := Lp.coeFn_zero ComplexCellL2 2 (volume.restrict (Icc a b))
  filter_upwards [he] with t he'
  change cellDualDerivative C hG V hv hb t (slice t)
      ((0 : Lp ComplexCellL2 2 (volume.restrict (Icc a b))) t)
      (fun _ => (0 : Lp ComplexCellL2 2 (volume.restrict (Icc a b))) t) = _
  rw [he']
  rfl

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Compact support of the actual value gives all polynomial factorial moments. -/

theorem weightedFactorialNormSq_compact_value_ne_top {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (f : PlaneHk Set.univ K E)
    {A : Set (Vec 2)} (hA : IsCompact A)
    (hf : ∀ᵐ x ∂volume, x ∉ A → f.toFunction.jet (valueIndex2 K) x = 0) :
    weightedFactorialNormSq n ϖ zc ρ K f ≠ ⊤ := by
  rw [weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_compact_value_ne_top ρ _ f hA hf
  apply Continuous.continuousOn
  unfold planeMomentPolynomial
  fun_prop

/-! A true componentwise budget gives the public geometry energy norm. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryEnergyNorm_of_component_lower_bounds (π : ι → ℝ) (Kslot : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r a b : ℝ)
    (f : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
    (A : ℝ) (hA : 0 ≤ A)
    (hbudget : ∀ i,
      (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (u i t)) +
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc r (Kslot i) (w i t)) ≤
      ENNReal.ofReal A * (weightedFactorialNormSq n ϖ zc r (Kslot i) (f i) +
        16 * ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t))) :
    geometryEnergyNorm π Kslot n ϖ zc r a b u w ≤
      ENNReal.ofReal ((16 * A) ^ (1 / 2 : ℝ)) *
        (geometryDataNorm π Kslot n ϖ zc r f + geometryFluxNorm π Kslot n ϖ zc r a b F) := by
  have hh := family_weighted_lower_energy_budget (volume.restrict (Set.Icc a b))
    (fun i => ENNReal.ofReal ((π i)⁻¹)) (fun _ => ENNReal.ofReal_ne_top)
    (fun i => (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (u i t)) +
      ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc r (Kslot i) (w i t))
    (fun i => weightedFactorialNormSq n ϖ zc r (Kslot i) (f i))
    (fun i t => weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t)) (ENNReal.ofReal A)
    hbudget
  exact family_energy_square_root hA hh
end

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual scalar weak time curve satisfies the clipped compact energy growth inequality. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeWeak_clipped_value_energy_growth
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual
        (planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) M hvb t)
        (cellMetricIntervalDiffusion a b hab G (fun t ht k j => (hG t ht k j).continuous)
          hCell t) (slice t) (F t) (H t)))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) :
    ∃ P : ℝ → ℝ,
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) P ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        P t + (∫ x, (1 / 2) * χ x ^ 2 * clipWeight B (W.W m t x) *
          ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice t) i x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
        18 * W.lam m * (∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
        8 * (∫ x, clipWeight B (W.W m t x) *
          ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        (4096 * η ^ 2 + 16 * M * η) * (∫ x, clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
        2 * (∫ x, (χ x ^ 2 * clipWeight B (W.W m t x)) * (‖H t x‖ * ‖u t x‖))) := by
  obtain ⟨A, hA, htime⟩ := planeWeak_clipped_value_energy_time hab _ _ F H h
    (fun p => W.W m p.1 p.2) (W.smooth m hm).1
    (fun p => W.pos m hm p.1 p.2) χ hχ hsχ B hB
  refine ⟨_, htime, ?_⟩
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t hut ht
  have htW : t ∈ Icc t₀ (t₀ + S) := ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hs := cellMetric_planeScalarDual_clipped_value_estimate W m hm t htW B hB hCell
    (hv t ht) (hdiv t ht) (hGs t ht) (hG t ht) χ hχ hsχ hM hη hχ0 hχ1
    (hvb t ht) hdχ (slice t) (A t (slice t)) (F t) (H t) (hA t ht (slice t))
  have hvcomp k x : |v t x k| ≤ M := by
    simpa only [← Real.norm_eq_abs] using (norm_le_pi_norm (v t x) k).trans (hvb t ht x)
  have hGb k j x : |G t x k j| ≤ 2 :=
    CycleEvolution.cellMetric_entry_bound hCell t x k j
  have hT := planeIntervalTransport_eq_of_mem (E := E) a b hab v
    (fun t ht => (hv t ht).continuous) M hM hvb t ht
    (fun k => (contDiff_pi.mp (hv t ht) k).continuous) hvcomp
  have hD := cellMetricIntervalDiffusion_eq_of_mem (E := E) a b hab G
    (fun t ht k j => (hG t ht k j).continuous) hCell t ht
    (fun k j => (hG t ht k j).continuous) hGb
  rw [hut, hT, hD]
  dsimp only at hs
  rw [planeValueForcedDual_pair, mul_add] at hs
  have hp := planeValueForcing_pair_of_value (H t) (A t (slice t))
    (planeHkValueOperator (E := E) 1 (slice t))
    (fun x => χ x ^ 2 * clipWeight B (W.W m t x)) (hA t ht (slice t))
  rw [ContinuousLinearMap.adjoint_inner_left] at hp
  rw [hp] at hs
  exact hs

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The single-pulse extension agrees with the full drift on the whole buffered region. -/

theorem interiorSinglePulseDrift_agrees_when_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (t : ℝ) (hq : ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) (z : Vec 2) :
    interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z = ocCellDrift α q Λ ζ m ν y₀ t z := by
  rcases interiorSinglePulseDrift_eq_actual_or_zero hΛ hζ ν y₀ hk t with he | he
  · exact congrFun he z
  · simp only [he, Pi.zero_apply, hq z]

theorem interiorBufferedPulse_window (τ a b D : ℝ) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (interiorBufferedPulseLo τ a D n) (interiorBufferedPulseHi τ b D n)) :
    |t - (2 * (n : ℝ) + 1) * τ| ≤ 3 / 4 * τ := by
  have hlo := (le_max_right _ _).trans ht.1
  have hhi := ht.2.trans (min_le_right _ _)
  apply abs_le.mpr
  constructor <;> linarith

theorem interiorSinglePulseDrift_buffered_agrees {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) (a b D : ℝ)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hleft : ∀ t ∈ Set.Ico a (a + D), ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0)
    (hright : ∀ t ∈ Set.Ioc (b - D) b, ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0)
    (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc
      (interiorBufferedPulseLo (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a D n - D)
      (interiorBufferedPulseHi (ocTau α q Λ m / ocEll q Λ m ν ^ 2) b D n + D)) (z : Vec 2) :
    interiorSinglePulseDrift α q Λ ζ m ν y₀ (2 * n + 1) t z =
      ocCellDrift α q Λ ζ m ν y₀ t z := by
  have hk : Odd (2 * n + 1) := ⟨n, by ring⟩
  by_cases hlo : interiorBufferedPulseLo (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a D n ≤ t
  · by_cases hhi : t ≤ interiorBufferedPulseHi (ocTau α q Λ m / ocEll q Λ m ν ^ 2) b D n
    · apply interiorSinglePulseDrift_agrees hΛ hζ ν y₀ hk _ z
      have hs := scaled_pulse_window hL (interiorBufferedPulse_window _ _ _ _ n ⟨hlo, hhi⟩)
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hs
    · exact interiorSinglePulseDrift_agrees_when_quiet hΛ hζ ν y₀ hk t
        (interiorBufferedPulse_right_quiet hΛ hζ ν y₀ hL b D hD hright n
          ⟨lt_of_not_ge hhi, ht.2⟩) z
  · exact interiorSinglePulseDrift_agrees_when_quiet hΛ hζ ν y₀ hk t
      (interiorBufferedPulse_left_quiet hΛ hζ ν y₀ hL a D hD hleft n
        ⟨ht.1, lt_of_not_ge hlo⟩) z

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual plane H1 reconstruction of a square-integrable cell H1 field. -/

def centeredCellBlochH1Reconstruct
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) : PlaneHk Set.univ 1 ℂ :=
  planeBlochReconstructH1 centeredPlaneFrequencyBase 1 (by norm_num)
    (centeredCellBlochTorusValue u) (centeredCellBlochTorusGradient u)
    (centeredCellBlochTorus_fourierDerivative u)

theorem centeredCellBlochH1Reconstruct_value
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    planeHkValueOperator 1 (centeredCellBlochH1Reconstruct u) =
      planeScalarBlochReconstruct centeredPlaneFrequencyBase 1 (by norm_num)
        (centeredCellBlochTorusValue u) :=
  planeBlochReconstructH1_value _ _ _ _ _ _

theorem centeredCellBlochH1Reconstruct_norm_sq
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ‖centeredCellBlochH1Reconstruct u‖ ^ 2 =
      ‖centeredCellBlochTorusValue u‖ ^ 2 +
        ∑ i : Fin 2, ‖centeredCellBlochTorusGradient u i‖ ^ 2 :=
  planeBlochReconstructH1_norm_sq _ _ _ _ _ _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWord_clipped_compact_energy_growth {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (α : JetIndex2 K)
    (hcurve : PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) :
    let u := fun t => planeJetReadoutOperator K α (U t)
    let slice := fun t => planeWordH1SliceOperator K α (W t)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let F := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
    let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
    ∃ P : ℝ → ℝ,
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, χ x ^ 2 * clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) P ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        P t + (∫ x, χ x ^ 2 * clipWeight B (C.W m t x) *
          ‖(WithLp.toLp 2 (fun k => planeH1GradientOperator (slice t) k x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
        18 * C.lam m * (∫ x, χ x ^ 2 * clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) +
        8 * (∫ x, clipWeight B (C.W m t x) *
          ‖(WithLp.toLp 2 (fun k => F t k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        (4096 * η ^ 2 + 16 * Mv * η) * (∫ x, clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) +
        2 * (∫ x, χ x ^ 2 * clipWeight B (C.W m t x) * (‖R t x‖ * ‖u t x‖))) := by
  dsimp only
  exact planeWeak_clipped_value_energy_growth a b hab v hv hdiv Mv hMv hvb G hG g hg4
    hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb _ _ _ _
    (planeSourceCurve_scalar_residual _ _ _ _ _ _ hcurve)
    χ hχ hsχ hχ0 hχ1 η hη hdχ B hB

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Real linearity of the genuine plane H1 reconstruction. -/

theorem planeComplexH1_value_injective :
    Function.Injective (planeHkValueOperator (E := ℂ) 1) := by
  intro u v h
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  exact h

theorem centeredCellBlochH1Reconstruct_add
    (u v : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    centeredCellBlochH1Reconstruct (u + v) =
      centeredCellBlochH1Reconstruct u + centeredCellBlochH1Reconstruct v := by
  apply planeComplexH1_value_injective
  rw [map_add, centeredCellBlochH1Reconstruct_value, centeredCellBlochH1Reconstruct_value,
    centeredCellBlochH1Reconstruct_value]
  have hv : centeredCellBlochValueField (u + v) =
      centeredCellBlochValueField u + centeredCellBlochValueField v :=
    (cellComplexH1ValueCLM.compLpL 2 centeredPlaneFrequencyMeasure).map_add u v
  simp only [centeredCellBlochTorusValue, hv, map_add]

theorem centeredCellBlochH1Reconstruct_smul
    (c : ℝ) (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    centeredCellBlochH1Reconstruct (c • u) = c • centeredCellBlochH1Reconstruct u := by
  apply planeComplexH1_value_injective
  rw [map_smul, centeredCellBlochH1Reconstruct_value, centeredCellBlochH1Reconstruct_value]
  have hv : centeredCellBlochValueField (c • u) = c • centeredCellBlochValueField u :=
    ((cellComplexH1ValueCLM.restrictScalars ℝ).compLpL 2
      centeredPlaneFrequencyMeasure).map_smul c u
  simp only [centeredCellBlochTorusValue, hv, map_smul]

end AVRegularity.CycleWords
end

section
open Homogenization Set
namespace AVRegularity.CycleWords

/-! Closing a quiet pulse endpoint before substituting indexed region geometry. -/

theorem interiorSinglePulseDrift_quiet_closed {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k)
    (lo D : ℝ) (hD : 0 < D)
    (hquiet : ∀ t ∈ Ico (lo - D) lo, ∀ x, ocCellDrift α q Λ ζ m ν y₀ t x = 0) :
    ∀ t ∈ Icc (lo - D) lo, ∀ x, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x = 0 := by
  intro t ht x
  have hmap : Continuous (fun s : ℝ => (s, x)) :=
    (continuous_id : Continuous (fun s : ℝ => s)).prodMk
      (continuous_const : Continuous (fun _ : ℝ => x))
  have hjoint := interiorSinglePulseDrift_joint_continuous (α := α) (q := q)
    (Λ := Λ) (m := m) hζ ν y₀ hk
  have hc : Continuous (fun s : ℝ => interiorSinglePulseDrift α q Λ ζ m ν y₀ k s x) :=
    by
      have he := hjoint.comp hmap
      simpa only [Function.comp_def] using he
  have hzero : ∀ s ∈ Ico (lo - D) lo,
      interiorSinglePulseDrift α q Λ ζ m ν y₀ k s x = 0 := by
    intro s hs
    exact (interiorSinglePulseDrift_agrees_when_quiet hΛ hζ ν y₀ hk s (hquiet s hs) x).trans
      (hquiet s hs x)
  exact continuous_quiet_interval (fun s => interiorSinglePulseDrift α q Λ ζ m ν y₀ k s x)
    hc lo D hD hzero t ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A positive-radius polynomial Sobolev energy controls the unweighted carrier norm pointwise. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem rawWeightedFactorialEnergy_one {K : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    rawWeightedFactorialEnergy ρ (fun _ => 1) U.toFunction.jet = factorialNormSq ρ U.val := by
  unfold rawWeightedFactorialEnergy factorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Measure.restrict_univ, one_mul]
  rfl

theorem weightedFactorialNormSq_unweighted_lower {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    ENNReal.ofReal (factorialWeightMin ρ K * ‖U‖ ^ 2) ≤
      weightedFactorialNormSq n ϖ zc ρ K U := by
  have hp x : 1 ≤ planeMomentPolynomial n ϖ zc x := by
    apply one_le_pow₀
    exact le_add_of_nonneg_right (by positivity)
  rw [weightedFactorialNormSq_stored_readout]
  have hmono : storedChartFactorialEnergy ρ (fun _ => 1) U ≤
      storedChartFactorialEnergy ρ (planeMomentPolynomial n ϖ zc) U := by
    unfold storedChartFactorialEnergy chartScalarEnergy
    apply Finset.sum_le_sum
    intro α _
    gcongr
    exact hp _
  have hbound := ENNReal.ofReal_le_ofReal (factorialNormSq_lower ρ U.val)
  have hone := storedChartFactorialEnergy_eq_ofReal ρ (fun _ : Vec 2 => 1)
    continuous_const (B := 1) (fun _ => by norm_num) (fun _ => by norm_num) U
  rw [rawWeightedFactorialEnergy_one] at hone
  change ENNReal.ofReal (factorialWeightMin ρ K * ‖U.val‖ ^ 2) ≤ _
  exact hbound.trans (hone.symm.le.trans hmono)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A fixed bound for genuine plane H1 reconstruction on the centered frequency cell. -/

def centeredCellBlochH1Bound : ℝ := Real.sqrt
  (‖cellComplexH1ValueCLM‖ ^ 2 + ∑ i : Fin 2,
    (‖cellComplexH1DerivativeCLM i‖ + 2 * Real.pi * ‖cellComplexH1ValueCLM‖) ^ 2)

theorem centeredCellBlochH1Reconstruct_norm_le
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ‖centeredCellBlochH1Reconstruct u‖ ≤ centeredCellBlochH1Bound * ‖u‖ := by
  have h0 := pow_le_pow_left₀ (norm_nonneg (centeredCellBlochTorusValue u))
    (centeredCellBlochTorusValue_norm_le u) 2
  have hi (i : Fin 2) := pow_le_pow_left₀ (norm_nonneg (centeredCellBlochTorusGradient u i))
    (centeredCellBlochTorusGradient_norm_le u i) 2
  have hn : 0 ≤ ‖cellComplexH1ValueCLM‖ ^ 2 + ∑ i : Fin 2,
      (‖cellComplexH1DerivativeCLM i‖ + 2 * Real.pi * ‖cellComplexH1ValueCLM‖) ^ 2 := by
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mp
  rw [centeredCellBlochH1Reconstruct_norm_sq]
  calc
    _ ≤ (‖cellComplexH1ValueCLM‖ * ‖u‖) ^ 2 + ∑ i : Fin 2,
        ((‖cellComplexH1DerivativeCLM i‖ + 2 * Real.pi * ‖cellComplexH1ValueCLM‖) * ‖u‖) ^ 2 :=
      add_le_add h0 (Finset.sum_le_sum (fun i _ => hi i))
    _ = (centeredCellBlochH1Bound * ‖u‖) ^ 2 := by
      simp only [mul_pow, ← Finset.sum_mul, ← add_mul,
        centeredCellBlochH1Bound, Real.sq_sqrt hn]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite literal weighted flux energy controls its unweighted lower-integral norm without a measurability premise. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedSobolev_lower_norm_integral_finite {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure ℝ) (F : ℝ → PlaneHk Set.univ K E)
    (he : (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (F t) ∂μ) ≠ ⊤) :
    (∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂μ) < ⊤ := by
  have hc : 0 < factorialWeightMin ρ K := factorialWeightMin_pos ρ hρ
  have hi : ENNReal.ofReal (factorialWeightMin ρ K) *
      (∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂μ) < ⊤ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lt_of_le_of_lt _ (lt_top_iff_ne_top.mpr he)
    apply lintegral_mono
    intro t
    dsimp only
    rw [← ENNReal.ofReal_mul hc.le]
    exact weightedFactorialNormSq_unweighted_lower n ϖ zc ρ (F t)
  apply lt_top_iff_ne_top.mpr
  intro hh
  rw [hh, ENNReal.mul_top ((ENNReal.ofReal_pos.mpr hc).ne')] at hi
  exact (lt_irrefl ⊤) hi

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual carrier trace has its weak increment with the native H1 time state. -/

theorem cellFiniteEnergyHomogeneous_nativeIncrement {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (f : ComplexCellL2) (z : CellEnergySpace a b)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb (f, 0, 0) z)
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val) (test : TorusHk 1 ℂ) :
    inner ℝ (z.val.1 t) (torusHkValueCLM test) -
      inner ℝ (z.val.1 s) (torusHkValueCLM test) =
        ∫ r in s.val..t.val, inner ℝ
          (cellDualDerivative C hG V hv hb r (cellEnergySpaceState hab z r) 0 0) test := by
  obtain ⟨u, slice, hu, _, ht⟩ := cellFiniteEnergyHomogeneousCurve C hG V hv hb f z hz
  have hs := cellFiniteEnergyTimeStateCLM_ae hab u slice _ hu z ht
  rw [ht t, ht s]
  apply (hu.increment s.val s.property t.val t.property hst test).trans
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  apply integral_congr_ae
  have hs' := hs.filter_mono (ae_mono (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.property.1 t.property.2)) le_rfl))
  filter_upwards [hs'] with r hr
  change inner ℝ (cellDualDerivative C hG V hv hb r (slice r) 0 0) test =
    inner ℝ (cellDualDerivative C hG V hv hb r
      (cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab z r)) 0 0) test
  rw [hr]

end AVRegularity.CycleWords
end
