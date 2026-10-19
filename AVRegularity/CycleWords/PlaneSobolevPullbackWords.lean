-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneRealDriftMultiplierCongr
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
public import AVRegularity.EntryWeak.SobolevSummableMajorantBound
public import AVRegularity.Weighted.PlaneH1SpectralCutoff
import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Exact real L2 pairings and integrability of the literal rough transport product. -/

theorem planeRealDriftMultiplier_pair (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeRealDriftMultiplier v hv t i C hC f) g =
      ∫ x, v t x i * inner ℝ (f x) (g x) := by
  change (∫ x, inner ℝ (planeRealDriftMultiplier v hv t i C hC f x) (g x)) = _
  apply integral_congr_ae
  filter_upwards [planeRealDriftMultiplier_ae v hv t i C hC f] with x hx
  rw [hx, Real.inner_apply, Real.inner_apply, mul_assoc]

theorem planeRealDriftMultiplier_pair_integrable
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Integrable (fun x => v t x i * inner ℝ (f x) (g x)) volume := by
  apply (L2.integrable_inner (planeRealDriftMultiplier v hv t i C hC f) g).congr
  filter_upwards [planeRealDriftMultiplier_ae v hv t i C hC f] with x hx
  rw [hx, Real.inner_apply, Real.inner_apply, mul_assoc]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native values at every order determine one smooth periodic representative and its exact jet carriers. -/

theorem torusHigher_all_order_smooth_representative (u : ComplexCellL2)
    (hex : ∀ K : ℕ, ∃ U : TorusHk K ℂ, torusHkValueCLM U = u) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (u : Vec 2 → ℂ) := by
  classical
  choose U hU using hex
  let f := torusHigherClassicalValue 2 (U 2)
  have hf : Continuous f := (torusHigherClassicalValue_contDiff 2 0 (by omega) (U 2)).continuous
  have hp : AVenhance.IsZ2Periodic f := torusHigherClassicalValue_periodic 2 (U 2)
  have he : f =ᵐ[volume.restrict AVenhance.unitCube] (u : Vec 2 → ℂ) := by
    simpa only [hU] using torusHigherClassicalValue_ae 2 (by omega) (U 2)
  refine ⟨f, ?_, hp, he⟩
  apply contDiff_infty.mpr
  intro n
  have hg := torusHigherClassicalValue_contDiff (n + 2) n (by omega) (U (n + 2))
  have hge : torusHigherClassicalValue (n + 2) (U (n + 2)) =ᵐ[volume.restrict AVenhance.unitCube]
      (u : Vec 2 → ℂ) := by
    simpa only [hU] using torusHigherClassicalValue_ae (n + 2) (by omega) (U (n + 2))
  have hfg : f = torusHigherClassicalValue (n + 2) (U (n + 2)) :=
    periodicContinuous_eq_of_cell_ae f _ hf hg.continuous hp
      (torusHigherClassicalValue_periodic _ _) (he.trans hge.symm)
  rw [hfg]
  exact hg

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The constant-metric source lifts to every genuine higher torus carrier. -/

def torusHigherStrongDiffusionCLM (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  (∑ j : Fin 2, ∑ k : Fin 2, (torusHigherScalarCLM K (G t j k : ℂ)).comp
    (torusHigherSecondCLM K j k)) +
  (∑ j : Fin 2, (torusHigherScalarCLM K (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k)).comp
    (torusHigherFirstCLM K j)) +
  (torusHigherScalarCLM K (-(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k))).comp
    (truncateTorusHk (by omega : K ≤ K + 2))

theorem torusHigherStrongDiffusionCLM_value (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ)
    (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (torusHigherStrongDiffusionCLM K G θ t U) =
      cellConstantMetricStrongDiffusionCLM G θ t (truncateTorusHk (by omega : 2 ≤ K + 2) U) := by
  simp only [torusHigherStrongDiffusionCLM, cellConstantMetricStrongDiffusionCLM,
    Fin.sum_univ_two, add_apply, ContinuousLinearMap.comp_apply, map_add,
    torusHigherScalarCLM_value, torusHigherFirstCLM_value, torusHigherSecondCLM_value]
  rfl

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual finite coefficient state has compatible native lifts including order zero. -/

def cellGalerkinNativeLiftCLM (N K : ℕ) :
    CellGalerkinSpace (E := ℂ) N →L[ℝ] TorusHk K ℂ :=
  (truncateTorusHk (by omega : K ≤ K + 1)).comp (cellGalerkinHigherStateCLM N K)

theorem cellGalerkinNativeLiftCLM_value (N K : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    torusHkValueCLM (cellGalerkinNativeLiftCLM N K u) = cellGalerkinValue N u :=
  cellGalerkinHigherStateCLM_value N K u

theorem cellGalerkinNativeLiftCLM_eq_range {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinNativeLiftCLM N K u = rangeSmoothFourierLiftCLM hK N u := by
  apply TorusHk.ext_value
  exact (cellGalerkinNativeLiftCLM_value N K u).trans (cellGalerkinRangeHigher_value hK N u).symm

theorem cellGalerkinNativeLiftCLM_one (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinNativeLiftCLM N 1 u = u.val :=
  cellGalerkinHigherStateCLM_truncate N 1 u

theorem cellGalerkinNativeLiftCLM_zero_norm_sq (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    ‖cellGalerkinNativeLiftCLM N 0 u‖ ^ 2 = ‖cellGalerkinValue N u‖ ^ 2 := by
  have he := torusHigher_norm_sq_eq_ordered_values 0 (cellGalerkinHigherStateCLM N 0 u)
  simpa only [cellGalerkinNativeLiftCLM, ContinuousLinearMap.comp_apply,
    cellGalerkinHigherStateCLM_value, Finset.univ_eq_empty, Finset.sum_empty, add_zero] using he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus Filter
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Genuine Bloch intertwining for bounded measurable periodic coefficients. -/

local instance planeBlochMeasurableMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance planeBlochMeasurableMultiplierProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem planeBloch_measurableMultiplier (a : Vec 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) (b : UnitAddTorus (Fin 2) → ℂ)
    (hb : Measurable b) (C : ℝ) (hC : 0 < C) (hbC : ∀ x, ‖b x‖ ≤ C) :
    planeScalarBlochTransform a 1 (by norm_num)
      (planeMeasurableTorusSymbolMultiplication b hb C hbC f) =
      (measurableTorusSymbolMultiplication b hb C hbC).compLp
        (planeScalarBlochTransform a 1 (by norm_num) f) := by
  have hb2 : MemLp b 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
    MemLp.of_bound hb.aestronglyMeasurable C (Eventually.of_forall hbC)
  have hb2C : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin 2))), ‖hb2.toLp b x‖ ≤ C := by
    filter_upwards [hb2.coeFn_toLp] with x hx
    rw [hx]
    exact hbC x
  obtain ⟨c, hc, ht⟩ := boundedTorusSymbol_continuous_approximation (hb2.toLp b) C hC hb2C
  have htc : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin 2))),
      Tendsto (fun n => c n x) atTop (𝓝 (b x)) := by
    filter_upwards [ht, hb2.coeFn_toLp] with x hx he
    simpa only [he] using hx
  have htp := scalarTorus_ae_plane_pullback htc
  have hl := tendsto_continuousTorusSymbolMultiplication volume torusQuotient
    measurePreserving_torusQuotient_cell.measurable c b hb C hC.le hc hbC htp f
  have hl' := (planeScalarBlochTransform a 1 (by norm_num)).continuous.continuousAt.tendsto.comp hl
  have hr : Tendsto (fun n => (scalarTorusSymbolMultiplication (c n)).compLp
      (planeScalarBlochTransform a 1 (by norm_num) f)) atTop
      (𝓝 ((measurableTorusSymbolMultiplication b hb C hbC).compLp
        (planeScalarBlochTransform a 1 (by norm_num) f))) := by
    apply tendsto_L2OperatorLift (fun n => scalarTorusSymbolMultiplication (c n))
      (measurableTorusSymbolMultiplication b hb C hbC) C hC.le
    · intro n
      exact continuousTorusSymbolMultiplication_norm_le_bound volume id measurable_id (c n) C hC.le (hc n)
    · exact L2Multiplier.operator_norm_le _ _ hC.le (Eventually.of_forall hbC)
    · intro u
      exact tendsto_continuousTorusSymbolMultiplication volume id measurable_id c b hb C hC.le hc hbC htc u
  have he (n : ℕ) := planeBloch_continuousMultiplier a f (c n)
  apply tendsto_nhds_unique hl'
  simpa only [Function.comp_def, ← he, planePeriodicSymbolMultiplication] using hr

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal sampled cell coefficients have measurable time extensions with their original molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def cellSampleScalar (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (s δ a b : ℝ) (X0 φ : Vec 2) (k : Fin 2) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then F.flux p c v u γ d I (s * t) (X0 + δ • z) (z + φ) k else 0

theorem familyMolecular_cell_sample_coefficient (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (s a b : ℝ) (hs : s ≠ 0) (X0 φ : Vec 2) (k : Fin 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) :
    let cc := cellSampleScalar F p c v u γ d I s (e / E) a b X0 φ k
    (∀ z, Measurable (fun t => cc t z)) ∧
      (∀ t, ContDiff ℝ (K v : ℕ) (cc t)) ∧
      (∀ᵐ t ∂volume, ∀ j ≤ K v, ∀ z, (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
        (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
          molecularRealPrice ν ρ (K v) (d - 2)
            (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2)) := by
  classical
  let cc := cellSampleScalar F p c v u γ d I s (e / E) a b X0 φ k
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) : ContDiff ℝ (K v : ℕ)
      (fun z => F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ)) := by
    have hh : ContDiff ℝ (K v : ℕ)
        (Function.uncurry (F.flux p c v u γ d I (s * t))) :=
      (molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
        henv.1 p c (s * t) (hwindow t ht) v u γ d I).of_le
          (by exact_mod_cast Nat.le_add_right (K v) J)
    exact hh.comp (((contDiff_const (c := X0)).add (contDiff_id.const_smul (e / E))).prodMk
      (contDiff_id.add (contDiff_const (c := φ))))
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hm := ((measurable_pi_iff.mp
      (hmeas p c v u γ d I (X0 + (e / E) • z) (z + φ))) k).comp
      ((measurable_const (a := s)).mul measurable_id)
    exact hm.piecewise measurableSet_Icc measurable_const
  · intro t
    by_cases ht : t ∈ Set.Icc a b
    · have hcoef : cellSampleScalar F p c v u γ d I s (e / E) a b X0 φ k t =
          (fun z => F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ) k) := by
        funext z
        simp only [cellSampleScalar, ite_eq_left ht]
      rw [hcoef]
      exact (ContinuousLinearMap.proj k).contDiff.comp (hf t ht)
    · have hcoef : cellSampleScalar F p c v u γ d I s (e / E) a b X0 φ k t =
          (fun _ : Vec 2 => (0 : ℝ)) := by
        funext z
        simp only [cellSampleScalar, ite_eq_right ht]
      rw [hcoef]
      exact contDiff_const
  · have ha := familyMolecular_ae_sample_budget F π hπ K Kmax hK dom ν e E ρ hν he hE hρ
      C J b₀ henv v u γ hγ d hd I p c
    have ha' := ae_real_time_dilation s hs _ ha
    filter_upwards [ha'] with t ht
    intro j hj z
    by_cases hI : t ∈ Set.Icc a b
    · have hh := ht (hwindow t hI) X0 φ j hj z
      have hc := iteratedJet_coordinate_norm_le _ (hf t hI) hj k z
      have hcoef : cc t = (fun z => F.flux p c v u γ d I (s * t)
          (X0 + (e / E) • z) (z + φ) k) := by
        funext z
        simp only [cc, cellSampleScalar, ite_eq_left hI]
      dsimp only [cc] at hcoef
      rw [hcoef]
      exact (mul_le_mul_of_nonneg_left hc (pow_nonneg (div_pos hρ he).le j)).trans hh
    · have hcoef : cc t = (fun _ : Vec 2 => (0 : ℝ)) := by
        funext z
        simp only [cc, cellSampleScalar, ite_eq_right hI]
      dsimp only [cc] at hcoef
      rw [hcoef]
      simp
      exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _))
        (by unfold derivativeReserveFactor; positivity)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The literal higher diffusion source is a finite sum of real metric coefficients and fixed maps. -/

theorem torusHigherStrongDiffusionCLM_expansion (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ)
    (U : TorusHk (K + 2) ℂ) :
    torusHigherStrongDiffusionCLM K G θ t U =
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • torusHigherSecondCLM K j k U) +
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • torusHigherScalarCLM K (2 * Complex.I * θ k)
        (torusHigherFirstCLM K j U)) +
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • torusHigherScalarCLM K (-(θ j * θ k))
        (truncateTorusHk (by omega : K ≤ K + 2) U)) := by
  have hfirst (j : Fin 2) : (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k) =
      (G t j 0 : ℂ) * (2 * Complex.I * θ 0) + (G t j 1 : ℂ) * (2 * Complex.I * θ 1) := by
    simp only [Fin.sum_univ_two]
    ring
  have hzero : -(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) =
      ((G t 0 0 : ℂ) * (-(θ 0 * θ 0)) + (G t 0 1 : ℂ) * (-(θ 0 * θ 1))) +
      ((G t 1 0 : ℂ) * (-(θ 1 * θ 0)) + (G t 1 1 : ℂ) * (-(θ 1 * θ 1))) := by
    simp only [Fin.sum_univ_two]
    ring
  simp only [torusHigherStrongDiffusionCLM, add_apply, ContinuousLinearMap.comp_apply, sum_apply]
  simp_rw [hfirst, hzero]
  simp only [Fin.sum_univ_two, torusHigherScalarCLM_add, torusHigherScalarCLM_mul,
    torusHigherScalarCLM_real]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Literal row differences preserve their actual Hilbert norm under coefficient replacement. -/

theorem cellL2Norm_fibreRow_difference_congr
    (r r' s s' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hr : ∀ p t, r p t =ᵐ[volume.restrict AVenhance.unitCube] r' p t)
    (hs : ∀ p t, s p t =ᵐ[volume.restrict AVenhance.unitCube] s' p t)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fun x => fibreSeriesFun r ξ t x - fibreSeriesFun s ξ t x) =
      cellL2Norm (fun x => fibreSeriesFun r' ξ t x - fibreSeriesFun s' ξ t x) := by
  apply eLpNorm_congr_ae
  exact (fibreSeriesFun_congr_ae r r' hr ξ t).sub (fibreSeriesFun_congr_ae s s' hs ξ t)

theorem cellL2Norm_difference_of_source_slices (f g : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (g t) 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (fun x => f t x - g t x) =
      ENNReal.ofReal ‖cellSourceSlice f t - cellSourceSlice g t‖ := by
  apply cellL2Norm_eq_of_class
  exact (Lp.coeFn_sub _ _).trans ((cellSourceSlice_ae f t hf).sub (cellSourceSlice_ae g t hg))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Strong measurability in time of multiplication by the actual measurable velocity. -/

theorem planeRealDriftMultiplier_fixedStronglyMeasurable
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (i : Fin 2) (C : ℝ)
    (hC : ∀ t z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    StronglyMeasurable (fun t => planeRealDriftMultiplier v hv t i C (hC t) f) := by
  let : SecondCountableTopology (Lp ℝ 2 (volume : Measure (Vec 2))) :=
    by
      let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
      exact Lp.SecondCountableTopology
  have hm (t : ℝ) : Measurable (fun x => v t x i) :=
    (measurable_pi_apply i).comp (hv.1.comp (measurable_const.prodMk measurable_id))
  have hb (t : ℝ) (x : Vec 2) : ‖v t x i‖ ≤ C := by
    simpa only [cellDriftTorusSymbol_plane v hv t i x, Complex.norm_real] using
      hC t (AVRegularity.Analysis.Convolution.torusQuotient x)
  have hmem (t : ℝ) : MemLp (fun x => v t x i * f x) 2 volume :=
    (memLp_top_of_bound (hm t).aestronglyMeasurable C
      (Filter.Eventually.of_forall (hb t))).mul (Lp.memLp f)
  have hj : StronglyMeasurable (fun p : ℝ × Vec 2 => v p.1 p.2 i * f p.2) :=
    ((measurable_pi_apply i).comp hv.1).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  have hs := bochnerL2Slice_stronglyMeasurable volume (fun t x => v t x i * f x) hj hmem
  have he : (fun t => planeRealDriftMultiplier v hv t i C (hC t) f) =
      (fun t => (hmem t).toLp (fun x => v t x i * f x)) := by
    funext t
    apply Lp.ext
    exact (planeRealDriftMultiplier_ae v hv t i C (hC t) f).trans
      (hmem t).coeFn_toLp.symm
  rw [he]
  exact hs

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual higher constant-metric diffusion source is Bochner L2 with measurable-time metric. -/

theorem torusHigher_metric_entry_memLp {μ : Measure ℝ} (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (j k : Fin 2) (U : ℝ → TorusHk K ℂ) (hU : MemLp U 2 μ) :
    MemLp (fun t => G t j k • U t) 2 μ := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  have hm : Measurable (fun t => G t j k) :=
    (cellMetric_entry_measurable hG j k).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have hg : MemLp (fun t => G t j k) ∞ μ := memLp_top_of_bound hm.aestronglyMeasurable 2
    (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG t 0 j k))
  exact hg.smul hU

theorem torusHigherStrongDiffusion_memLp {μ : Measure ℝ} (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (U : ℝ → TorusHk (K + 2) ℂ) (hU : MemLp U 2 μ) :
    MemLp (fun t => torusHigherStrongDiffusionCLM K G θ t (U t)) 2 μ := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  have hsecond : MemLp (fun t => ∑ j : Fin 2, ∑ k : Fin 2,
      G t j k • torusHigherSecondCLM K j k (U t)) 2 μ := by
    apply memLp_finsetSum
    intro j _
    apply memLp_finsetSum
    intro k _
    exact torusHigher_metric_entry_memLp K G hG j k _
      ((torusHigherSecondCLM K j k).comp_memLp' hU)
  have hfirst : MemLp (fun t => ∑ j : Fin 2, ∑ k : Fin 2,
      G t j k • torusHigherScalarCLM K (2 * Complex.I * θ k) (torusHigherFirstCLM K j (U t))) 2 μ := by
    apply memLp_finsetSum
    intro j _
    apply memLp_finsetSum
    intro k _
    exact torusHigher_metric_entry_memLp K G hG j k _
      ((torusHigherScalarCLM K (2 * Complex.I * θ k)).comp_memLp'
        ((torusHigherFirstCLM K j).comp_memLp' hU))
  have hzero : MemLp (fun t => ∑ j : Fin 2, ∑ k : Fin 2,
      G t j k • torusHigherScalarCLM K (-(θ j * θ k))
        (truncateTorusHk (by omega : K ≤ K + 2) (U t))) 2 μ := by
    apply memLp_finsetSum
    intro j _
    apply memLp_finsetSum
    intro k _
    exact torusHigher_metric_entry_memLp K G hG j k _
      ((torusHigherScalarCLM K (-(θ j * θ k))).comp_memLp'
        ((truncateTorusHk (E := ℂ) (K := K) (L := K + 2)
          (by omega : K ≤ K + 2)).comp_memLp' hU))
  simp_rw [torusHigherStrongDiffusionCLM_expansion]
  apply MemLp.add
  · apply MemLp.add
    · exact hsecond
    · exact hfirst
  · exact hzero

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Smooth value representatives preserve the full public cell energy solution. -/

theorem cellSolution_value_representative_replacement (I : Set ℝ) (C : CellCoefficients)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (f : ℝ → Vec 2 → ℂ)
    (hD : IsCellSolution I C src F D)
    (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (hm : AEStronglyMeasurable (fun z : ℝ × Vec 2 => f z.1 z.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (he : ∀ t, f t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    IsCellSolution I C src F (fun t => cellValueRepresentativeJet (D t) (f t)) := by
  let E := fun t => cellValueRepresentativeJet (D t) (f t)
  have hv : cellValue E = f := by
    funext t
    exact cellValueRepresentativeJet_value (D t) (f t)
  have hg : (fun t k => cellGradComp (E t) k) = fun t k => cellGradComp (D t) k := by
    funext t k
    exact cellValueRepresentativeJet_gradComp (D t) (f t) k
  refine ⟨hD.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.2.1] with t ht
    exact cellValueRepresentativeJet_periodicWeak (D t) (f t) ht (hp t) (he t)
  · intro t ht
    rw [hv]
    exact ⟨((hD.2.2.1 t ht).1).ae_eq (he t).symm, hp t⟩
  · intro a
    by_cases ha : a = valueIndex2 1
    · subst a
      change AEStronglyMeasurable (fun z : ℝ × Vec 2 => cellValue E z.1 z.2) _
      rw [hv]
      exact hm
    · have heq : (fun z : ℝ × Vec 2 => E z.1 a z.2) = fun z => D z.1 a z.2 := by
        funext z
        simp only [E, cellValueRepresentativeJet, ite_eq_right ha]
      rw [heq]
      exact hD.2.2.2.1 a
  · intro t0 ht0
    rw [hv]
    have heq : (fun t => ∫⁻ x in AVenhance.unitCube, ‖f t x - f t0 x‖ₑ ^ 2) =
        fun t => ∫⁻ x in AVenhance.unitCube, ‖cellValue D t x - cellValue D t0 x‖ₑ ^ 2 := by
      funext t
      apply lintegral_congr_ae
      filter_upwards [he t, he t0] with x hx hy
      rw [hx, hy]
    rw [heq]
    exact hD.2.2.2.2.1 t0 ht0
  · intro a ha b hb
    change (∫⁻ τ in Icc a b,
      cellL2Norm (cellGradient (cellValueRepresentativeJet (D τ) (f τ))) ^ 2) < ⊤
    simp only [cellValueRepresentativeJet_gradient]
    exact hD.2.2.2.2.2.1 a ha b hb
  · intro s hs t ht hst ψ
    rw [hv, hg]
    exact cellWeakIdentity_value_congr_sections C s t _ _ _ _ _ _ _ _ _ _ _
      (he s).symm (he t).symm (Filter.Eventually.of_forall (fun r => (he r).symm))
      (hD.2.2.2.2.2.2 s hs t ht hst ψ)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The genuine Bloch derivative on native higher cell spaces retains the constant-state frequency gain. -/

def torusHigherBlochDerivativeCLM (K : ℕ) (θ : Fin 2 → ℂ) (j : Fin 2) :
    TorusHk (K + 1) ℂ →L[ℝ] TorusHk K ℂ :=
  derivativeTorusHk (K := K) (fun _ : Fin 1 => j) +
    (torusHigherScalarCLM K (Complex.I * θ j)).comp
      (truncateTorusHk (E := ℂ) (by omega : K ≤ K + 1))

theorem torusHigherBlochDerivativeCLM_apply (K : ℕ) (θ : Fin 2 → ℂ) (j : Fin 2)
    (U : TorusHk (K + 1) ℂ) :
    torusHigherBlochDerivativeCLM K θ j U = derivativeTorusHk (fun _ : Fin 1 => j) U +
      torusHigherScalarCLM K (Complex.I * θ j) (truncateTorusHk (by omega : K ≤ K + 1) U) := rfl

theorem torusHigherBlochDerivativeCLM_norm_le (K : ℕ) (θ : Fin 2 → ℂ) (j : Fin 2)
    (U : TorusHk (K + 1) ℂ) :
    ‖torusHigherBlochDerivativeCLM K θ j U‖ ≤
      (1 + ‖θ j‖ * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ := by
  rw [torusHigherBlochDerivativeCLM_apply]
  have hc : ‖Complex.I * θ j‖ = ‖θ j‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hs := (torusHigherScalarCLM K (Complex.I * θ j)).le_opNorm
    (truncateTorusHk (by omega : K ≤ K + 1) U)
  have hcoef := torusHigherScalarCLM_norm_le K (Complex.I * θ j) ‖θ j‖ hc.le
  have hsc : ‖torusHigherScalarCLM K (Complex.I * θ j)
      (truncateTorusHk (by omega : K ≤ K + 1) U)‖ ≤
      (‖θ j‖ * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ :=
    hs.trans (mul_le_mul hcoef (truncateTorusHk_norm_le _ U) (norm_nonneg _) (by positivity))
  exact ((norm_add_le _ _).trans (add_le_add (derivativeTorusHk_norm_le _ U) hsc)).trans_eq (by ring)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The complex canonical Fourier readout has a uniform native-to-classical derivative bound. -/

def torusHigherClassicalSobolevConstant (K n : ℕ) : ℝ :=
  ‖Complex.ofRealCLM‖ * classicalSobolevConstant n *
    (‖mapTorusHkCLM K Complex.reCLM‖ + ‖mapTorusHkCLM K Complex.imCLM‖)

theorem torusHigherClassicalValue_derivative_norm_le (K n : ℕ) (hn : n + 2 ≤ K)
    (U : TorusHk K ℂ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (torusHigherClassicalValue K U) x‖ ≤
      torusHigherClassicalSobolevConstant K n * ‖U‖ := by
  let r := realClassicalLift K (mapTorusHk Complex.reCLM U)
  let s := realClassicalLift K (mapTorusHk Complex.imCLM U)
  have hr : ContDiffAt ℝ (n : ℕ∞) r x :=
    (realClassicalLift_contDiff K n hn _).contDiffAt
  have hs : ContDiffAt ℝ (n : ℕ∞) s x :=
    (realClassicalLift_contDiff K n hn _).contDiffAt
  have hcr := Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
  have hcs := Complex.ofRealCLM.contDiff.contDiffAt.comp x hs
  have hC : 0 ≤ classicalSobolevConstant n := by unfold classicalSobolevConstant; positivity
  have hmap (L : ℂ →L[ℝ] ℝ) : ‖mapTorusHk L U‖ ≤ ‖mapTorusHkCLM K L‖ * ‖U‖ := by
    simpa only [mapTorusHkCLM_apply] using (mapTorusHkCLM K L).le_opNorm U
  have hb (L : ℂ →L[ℝ] ℝ) :
      ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ realClassicalLift K (mapTorusHk L U)) x‖ ≤
        ‖Complex.ofRealCLM‖ * classicalSobolevConstant n * ‖mapTorusHkCLM K L‖ * ‖U‖ := by
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left
      (realClassicalLift_contDiff K n hn _).contDiffAt le_rfl]
    have hh := (Complex.ofRealCLM.norm_compContinuousMultilinearMap_le
      (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk L U)) x)).trans
      (mul_le_mul_of_nonneg_left (realClassicalLift_derivative_norm_le K (mapTorusHk L U) n hn x)
        (norm_nonneg _))
    calc
      _ ≤ ‖Complex.ofRealCLM‖ * (classicalSobolevConstant n * ‖mapTorusHk L U‖) := hh
      _ ≤ ‖Complex.ofRealCLM‖ * (classicalSobolevConstant n *
          (‖mapTorusHkCLM K L‖ * ‖U‖)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hmap L) hC) (norm_nonneg Complex.ofRealCLM)
      _ = _ := by ring
  change ‖iteratedFDeriv ℝ n (fun y => (Complex.ofRealCLM ∘ r) y +
    Complex.I • (Complex.ofRealCLM ∘ s) y) x‖ ≤ _
  have hadd := iteratedFDeriv_add_apply (f := Complex.ofRealCLM ∘ r)
    (g := fun y => Complex.I • (Complex.ofRealCLM ∘ s) y) hcr (hcs.const_smul Complex.I)
  change ‖iteratedFDeriv ℝ n ((Complex.ofRealCLM ∘ r) +
    (fun y => Complex.I • (Complex.ofRealCLM ∘ s) y)) x‖ ≤ _
  rw [hadd, iteratedFDeriv_const_smul_apply' hcs]
  have ha := norm_add_le
    (iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ r) x)
    (Complex.I • iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ s) x)
  rw [norm_smul, Complex.norm_I, one_mul] at ha
  exact ha.trans ((add_le_add (hb Complex.reCLM) (hb Complex.imCLM)).trans_eq (by
    dsimp only [torusHigherClassicalSobolevConstant]
    ring))

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Measurable-time cell metrics give a uniform bound for the genuine higher diffusion operator. -/

theorem torusHigherStrongDiffusionCLM_uniform_bound (K : ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, ‖torusHigherStrongDiffusionCLM K G θ t‖ ≤ D := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : NormedSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 2) ℂ) := inferInstance
  let : NormedSpace ℝ (TorusHk (K + 2) ℂ) := inferInstance
  let B₂ : Fin 2 → Fin 2 → (TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ) := torusHigherSecondCLM K
  let B₁ : Fin 2 → Fin 2 → (TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ) := fun j k =>
    (torusHigherScalarCLM K (2 * Complex.I * θ k)).comp (torusHigherFirstCLM K j)
  let B₀ : Fin 2 → Fin 2 → (TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ) := fun j k =>
    (torusHigherScalarCLM K (-(θ j * θ k))).comp
      (truncateTorusHk (E := ℂ) (K := K) (L := K + 2) (by omega))
  let D₂ := ∑ j : Fin 2, ∑ k : Fin 2, 2 * ‖B₂ j k‖
  let D₁ := ∑ j : Fin 2, ∑ k : Fin 2, 2 * ‖B₁ j k‖
  let D₀ := ∑ j : Fin 2, ∑ k : Fin 2, 2 * ‖B₀ j k‖
  refine ⟨D₂ + D₁ + D₀, by dsimp [D₂, D₁, D₀]; positivity, ?_⟩
  intro t
  have he : torusHigherStrongDiffusionCLM K G θ t =
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • B₂ j k) +
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • B₁ j k) +
      (∑ j : Fin 2, ∑ k : Fin 2, G t j k • B₀ j k) := by
    apply ContinuousLinearMap.ext
    intro u
    dsimp only [B₂, B₁, B₀]
    simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]
    exact torusHigherStrongDiffusionCLM_expansion K G θ t u
  rw [he]
  have hs (B : Fin 2 → Fin 2 → (TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ)) :
      ‖∑ j : Fin 2, ∑ k : Fin 2, G t j k • B j k‖ ≤ ∑ j : Fin 2, ∑ k : Fin 2, 2 * ‖B j k‖ := by
    apply (norm_sum_le Finset.univ (fun j => ∑ k : Fin 2, G t j k • B j k)).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le Finset.univ (fun k => G t j k • B j k)).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (cellMetric_entry_bound hG t 0 j k) (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (hs B₂) (hs B₁))) (hs B₀))

end AVRegularity.CycleWords
end

section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The bilinear cell integral is complex linear in its row argument. -/

theorem cellFiberConj_smul (a : ℂ) (u : ComplexCellL2) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap (a • u) =
      star a • cellFiberCLM Complex.conjCLE.toContinuousLinearMap u := by
  apply Lp.ext
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (a • u),
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL u,
    Lp.coeFn_smul a u,
    Lp.coeFn_smul (star a) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u)]
    with x ha hu hs ht
  change cellFiberCLM Complex.conjCLE.toContinuousLinearMap (a • u) x = star ((a • u) x) at ha
  change cellFiberCLM Complex.conjCLE.toContinuousLinearMap u x = star (u x) at hu
  rw [ha, ht]
  simp only [Pi.smul_apply, smul_eq_mul] at hs ⊢
  rw [hs, star_mul, hu, mul_comm]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Measurable drift multiplication preserves the actual Bochner L2 time class. -/

theorem planeRealDriftMultiplier_norm_apply_le
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    ‖planeRealDriftMultiplier v hv t i C hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [planeRealDriftMultiplier_ae v hv t i C hC f] with x hx
  rw [hx, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [cellDriftTorusSymbol_plane v hv t i x, Complex.norm_real] using
    hC (AVRegularity.Analysis.Convolution.torusQuotient x)

theorem planeRealDriftMultiplier_timeMemLp
    (μ : Measure ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (i : Fin 2) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2))) (hu : MemLp u 2 μ) :
    MemLp (fun t => planeRealDriftMultiplier v hv t i C (hC t) (u t)) 2 μ := by
  let : MeasurableSpace (Lp ℝ 2 (volume : Measure (Vec 2))) := borel _
  let : BorelSpace (Lp ℝ 2 (volume : Measure (Vec 2))) := ⟨rfl⟩
  let : SecondCountableTopology (Lp ℝ 2 (volume : Measure (Vec 2))) :=
    by
      let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
      exact Lp.SecondCountableTopology
  have hm := caratheodoryFamily_stronglyMeasurable
    (fun t f => planeRealDriftMultiplier v hv t i C (hC t) f)
    (fun t => (planeRealDriftMultiplier v hv t i C (hC t)).continuous)
    (planeRealDriftMultiplier_fixedStronglyMeasurable v hv i C hC)
    (hu.aestronglyMeasurable.mk u) hu.aestronglyMeasurable.stronglyMeasurable_mk
  have hae : AEStronglyMeasurable
      (fun t => planeRealDriftMultiplier v hv t i C (hC t) (u t)) μ :=
    hm.aestronglyMeasurable.congr
      (hu.aestronglyMeasurable.ae_eq_mk.mono (fun t ht => congrArg
        (planeRealDriftMultiplier v hv t i C (hC t)) ht.symm))
  apply (hu.norm.const_mul C).of_le hae
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0,
      abs_of_nonneg (norm_nonneg _)] using
      planeRealDriftMultiplier_norm_apply_le v hv t i C (hC t) (u t))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! The finite ordered-word budget survives the strong native Sobolev limit. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeJetLpTransport_ae {K j : ℕ} (hj : j ≤ K) (U : PlaneHk Set.univ K E)
    (w : DerivativeWord2 j) (X : Vec 2 → Vec 2) (hμ : MeasurePreserving X volume volume) :
    Lp.compMeasurePreserving X hμ
      (Weighted.planeJetReadoutOperator K ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ U) =ᵐ[volume]
        fun z => planeJetOrder U j w (X z) :=
  (Lp.coeFn_compMeasurePreserving _ hμ).trans
    (hμ.quasiMeasurePreserving.ae_eq_comp (planeJetLpReadout_ae hj U w))

theorem planeSobolev_pullback_word_budget_of_smooth_limit {K : ℕ}
    (U V : PlaneHk Set.univ K E) (UN : ℕ → PlaneHk Set.univ K E) (fN : ℕ → Vec 2 → E)
    (ht : Tendsto UN atTop (𝓝 U)) (hs : ∀ N, ContDiff ℝ (⊤ : ℕ∞) (fN N))
    (hv : ∀ N, planeValue (UN N) =ᵐ[volume] fN N)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hV : Tendsto (fun N => smoothPlanePullback (UN N) (fN N) (hs N) (hv N) X hX hμ B hb)
      atTop (𝓝 V)) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ∀ᵐ z ∂volume, ‖planeJetOrder V n w z‖ ≤
      ∑ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
        (∏ i : Fin a.1.length, B (a.1.partSize i)) *
          ‖planeJetOrder U a.1.length a.2 (X z)‖ := by
  let J := Σ c : OrderedFinpartition n, DerivativeWord2 c.length
  let A := Weighted.planeJetReadoutOperator (E := E) K ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩
  let G (a : J) := Weighted.planeJetReadoutOperator (E := E) K
    ⟨⟨a.1.length, Nat.lt_succ_of_le (a.1.length_le.trans hn)⟩, a.2⟩
  let VN N := smoothPlanePullback (UN N) (fN N) (hs N) (hv N) X hX hμ B hb
  let qN N := A (VN N)
  let gN N (a : J) := Lp.compMeasurePreserving X hμ (G a (UN N))
  let q := A V
  let g (a : J) := Lp.compMeasurePreserving X hμ (G a U)
  let c (a : J) := ∏ i : Fin a.1.length, B (a.1.partSize i)
  have hq : Tendsto qN atTop (𝓝 q) := (A.continuous.tendsto V).comp hV
  have hg a : Tendsto (fun N => gN N a) atTop (𝓝 (g a)) :=
    ((Lp.compMeasurePreservingₗᵢ ℝ X hμ).continuous.tendsto (G a U)).comp
      (((G a).continuous.tendsto U).comp ht)
  have hba N : ∀ᵐ z ∂volume, ‖qN N z‖ ≤ ∑ a : J, c a * ‖gN N a z‖ := by
    have hi : ∀ᵐ z ∂volume, ∀ a : J,
        gN N a z = planeJetOrder (UN N) a.1.length a.2 (X z) :=
      ae_all_iff.mpr (fun a => planeJetLpTransport_ae (a.1.length_le.trans hn) (UN N) a.2 X hμ)
    filter_upwards [hi, planeJetLpReadout_ae hn (VN N) w,
      smoothPlanePullback_word_budget_ae (UN N) (fN N) (hs N) (hv N) X hX hμ B hb n hn w]
      with z hi ho hz
    simpa only [qN, A, ho, hi, c, gN] using hz
  have hfinal := finite_norm_majorant_closed volume qN gN q g c hq hg hba
  have hi : ∀ᵐ z ∂volume, ∀ a : J, g a z = planeJetOrder U a.1.length a.2 (X z) :=
    ae_all_iff.mpr (fun a => planeJetLpTransport_ae (a.1.length_le.trans hn) U a.2 X hμ)
  filter_upwards [hfinal, hi, planeJetLpReadout_ae hn V w] with z hz hi ho
  simpa only [q, A, ho, hi, c, g] using hz

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Polarization gives the genuine moving-test pairing formula for two plane energy curves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeH1Pair_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (d z : ℝ → PlaneHk Set.univ 1 E)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hz : MemLp z 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun r => inner ℝ (d r) (z r)) volume s t := by
  have hp : Integrable (fun r => ‖d r‖ * ‖z r‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hd.norm.mul hz.norm : MemLp _ 1 _)
  have hi : Integrable (fun r => inner ℝ (d r) (z r)) (volume.restrict (Icc a b)) :=
    hp.mono' (hd.aestronglyMeasurable.inner hz.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun r => norm_inner_le_norm (d r) (z r)))
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact hi.mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

theorem planeWeakPair_increment {a b s t : ℝ}
    {u v : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual slice' dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (h' : PlaneWeakHilbertCurve a b v slice' dual')
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    inner ℝ (u t) (v t) - inner ℝ (u s) (v s) =
      ∫ r in s..t, inner ℝ (dual r) (slice' r) + inner ℝ (dual' r) (slice r) := by
  have haa := planeH1Pair_intervalIntegrable hs ht hst dual slice h.dual_mem h.state
  have hbb := planeH1Pair_intervalIntegrable hs ht hst dual' slice' h'.dual_mem h'.state
  have hab := planeH1Pair_intervalIntegrable hs ht hst dual slice' h.dual_mem h'.state
  have hba := planeH1Pair_intervalIntegrable hs ht hst dual' slice h'.dual_mem h.state
  have hi : (∫ r in s..t, 2 * inner ℝ (dual r - dual' r) (slice r - slice' r)) =
      (∫ r in s..t, 2 * inner ℝ (dual r) (slice r)) +
        (∫ r in s..t, 2 * inner ℝ (dual' r) (slice' r)) -
          2 * (∫ r in s..t, inner ℝ (dual r) (slice' r) + inner ℝ (dual' r) (slice r)) := by
    have he : (fun r => 2 * inner ℝ (dual r - dual' r) (slice r - slice' r)) =
        fun r => (2 * inner ℝ (dual r) (slice r) + 2 * inner ℝ (dual' r) (slice' r)) -
          2 * (inner ℝ (dual r) (slice' r) + inner ℝ (dual' r) (slice r)) := by
      funext r
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [he, intervalIntegral.integral_sub ((haa.const_mul 2).add (hbb.const_mul 2))
      ((hab.add hba).const_mul 2), intervalIntegral.integral_add (haa.const_mul 2) (hbb.const_mul 2)]
    simp only [intervalIntegral.integral_const_mul]
  have he := (h.sub h').energy_increment_between hs ht hst
  rw [norm_sub_sq_real, norm_sub_sq_real, hi] at he
  linarith [h.energy_increment_between hs ht hst, h'.energy_increment_between hs ht hst]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Uniform classical jet bounds hold for every smooth periodic representative of a native value. -/

theorem torusHigher_periodic_representative_derivative_norm_le (K n : ℕ) (hn : n + 2 ≤ K)
    (U : TorusHk K ℂ) (f : Vec 2 → ℂ) (hf : Continuous f)
    (hp : AVenhance.IsZ2Periodic f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] (torusHkValueCLM U : Vec 2 → ℂ))
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ torusHigherClassicalSobolevConstant K n * ‖U‖ := by
  have hK : 2 ≤ K := by omega
  have hrep : torusHigherClassicalValue K U = f :=
    periodicContinuous_eq_of_cell_ae _ f
      (torusHigherClassicalValue_contDiff K 0 (by omega) U).continuous hf
      (torusHigherClassicalValue_periodic K U) hp ((torusHigherClassicalValue_ae K hK U).trans he.symm)
  rw [← hrep]
  exact torusHigherClassicalValue_derivative_norm_le K n hn U x

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Contrast uniform coordinate budgets from the enhancement numerator. -/

theorem epsilon_enhancement_power (e α : ℝ) (he : 0 ≤ e) :
    (e ^ (1 + α)) ^ (2 : ℕ) = e ^ (2 * (1 + α)) := by
  rw [mul_comm (2 : ℝ), Real.rpow_mul he]
  exact (Real.rpow_two _).symm

theorem adjointCoordinate_gradient_enhancement {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B C : ℝ} (hν : 0 < ν)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (t : ℝ) (y : Vec 2) (j i : Fin 2) :
    ν * (fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i)) ^ 2 ≤
      2 * C * B := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : 0 ≤ ocEpsilon q Λ m ^ (1 + α) := (Real.rpow_pos_of_pos hep _).le
  have hb := adjointCoordinate_gradient_bound (α := α) (q := q) (m := m) hΛ hζ hν t y j i
  unfold ocMu at hb
  rw [shear_frequency_memory_cancel _ _ _ hep hν, abs_of_nonneg ha] at hb
  have hs : (fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i)) ^ 2 ≤
      (1 + ocEpsilon q Λ m ^ (1 + α) / ν) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hb
    simpa only [sq_abs] using hh
  apply (mul_le_mul_of_nonneg_left hs hν.le).trans
  apply enhanced_shear_gradient_budget hν
  simpa only [epsilon_enhancement_power _ _ hep.le] using he

theorem adjointCoordinate_displacement_enhancement {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B C : ℝ} (hν : 0 < ν)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    (adjointCoordinate α q Λ ζ m ν t y j - y j) ^ 2 ≤
      C * B * (ocEpsilon q Λ m ^ 2 / ν) := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : 0 ≤ ocEpsilon q Λ m ^ (1 + α) := (Real.rpow_pos_of_pos hep _).le
  have hb := adjointCoordinate_displacement_bound (α := α) (q := q) (m := m) hΛ hζ hν t y j
  unfold ocMu at hb
  rw [shear_displacement_memory_cancel _ _ _ hep hν] at hb
  have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hb
  simp only [sq_abs] at hs
  apply hs.trans
  apply enhanced_shear_displacement_budget hep hν ha hB hC
  simpa only [epsilon_enhancement_power _ _ hep.le] using he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The zero Sobolev order is exactly the actual cell L2 norm. -/

theorem cellSobolevNorm_zero_eq (f : Vec 2 → ℂ) (hf : Continuous f) :
    cellSobolevNorm 0 f = cellL2Norm f := by
  simp only [cellSobolevNorm, zero_add, Finset.sum_range_one, norm_iteratedFDeriv_zero]
  exact eLpNorm_norm f hf.measurable.aestronglyMeasurable

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! The assembled gradient carrier has the literal weighted factorial gradient norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem planeGradientTensor_word_readout {K : ℕ} (U : PlaneHk Set.univ (K + 1) E)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (planeGradientTensor U) j w =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : Fin 2 => planeJetOrder U (j + 1) (Fin.snoc w k) x)) := by
  have hh := Weighted.planeGradientTensor_jet_ae U ⟨j, Nat.lt_succ_of_le hj⟩ w
  have hhv : (planeGradientTensor U).val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        U.val ⟨⟨j + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hj)⟩, Fin.snoc w k⟩ x)) := by
    simpa only [Measure.restrict_univ] using hh
  rw [planeJetOrder_eq_stored hj]
  have he : ∀ k, planeJetOrder U (j + 1) (Fin.snoc w k) =
      U.toFunction.jet ⟨⟨j + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hj)⟩, Fin.snoc w k⟩ :=
    fun k => planeJetOrder_eq_stored (Nat.add_le_add_right hj 1) U (Fin.snoc w k)
  simp_rw [he]
  exact hhv

theorem planeGradientTensor_weightedFactorialNormSq {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (U : PlaneHk Set.univ (K + 1) E) :
    weightedFactorialNormSq n ϖ zc ρ K (planeGradientTensor U) =
      weightedGradFactorialNormSq n ϖ zc ρ K U := by
  unfold weightedFactorialNormSq weightedGradFactorialNormSq
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply lintegral_congr_ae
  have hh : ∀ᵐ x ∂volume, ∀ w : DerivativeWord2 j,
      planeJetOrder (planeGradientTensor U) j w x =
        WithLp.toLp 2 (fun k : Fin 2 => planeJetOrder U (j + 1) (Fin.snoc w k) x) := by
    apply ae_all_iff.mpr
    intro w
    exact planeGradientTensor_word_readout U j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) w
  filter_upwards [hh] with x hx
  simp_rw [hx, PiLp.norm_sq_eq_of_L2]
  congr 2
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : Fin 2 × DerivativeWord2 j =>
    ‖planeJetOrder U (j + 1) (Fin.snoc p.2 p.1) x‖ ^ 2)]
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin 2))
    (fun p : Fin 2 × DerivativeWord2 j => ‖planeJetOrder U (j + 1) (Fin.snoc p.2 p.1) x‖ ^ 2)
    (fun w : DerivativeWord2 (j + 1) => ‖planeJetOrder U (j + 1) w x‖ ^ 2)
    (fun _ => rfl))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! The finite classical chain rule budget holds for every native weak Sobolev renewal. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSobolev_pullback_word_budget {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X) (n : ℕ) (hn : n ≤ K)
    (w : DerivativeWord2 n) :
    ∀ᵐ z ∂volume, ‖planeJetOrder V n w z‖ ≤
      ∑ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
        (∏ i : Fin a.1.length, B (a.1.partSize i)) *
          ‖planeJetOrder U a.1.length a.2 (X z)‖ := by
  obtain ⟨UN, fN, ht, hs, hvalue⟩ := exists_smooth_planeHk_approximation U
  obtain ⟨V', hlimit, hv', _⟩ :=
    planeSobolev_pullback_sequence_limit U UN fN ht hs hvalue X hX hμ B hb
  have he : V' = V := planeHk_eq_of_planeValue_ae (hv'.trans hv.symm)
  rw [he] at hlimit
  exact planeSobolev_pullback_word_budget_of_smooth_limit U V UN fN ht hs hvalue
    X hX hμ B hb hlimit n hn w

end AVRegularity.CycleWords
end
