-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import AVRegularity.CycleWords.MolecularEnvelopeReadout
public import AVRegularity.Weighted.PlaneJetFluxOperator
public import AVRegularity.CycleEvolution.CellJetSlices

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! The actual expanding cutoff acts strongly on every finitely weighted stored jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem expandingPlaneCoefficient_weighted_raw_tendsto {K : ℕ}
    (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hw : JetMemL2On Set.univ (fun b x => q x • D b x))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ n l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l)
    (hb0 : ∀ l x, ‖coefficientDerivativeArray
      (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) l.val x‖ ≤ A l) (a : JetIndex2 K) :
    Tendsto (fun n => (weighted_multiplicationRawJet_memLp
      (expandingPlaneCoefficient (E := E) n)
      ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) D q hw A (hb n) a).toLp
        (fun x => q x • multiplicationRawJet (expandingPlaneCoefficient (E := E) n) D a x))
      atTop (𝓝 ((weighted_multiplicationRawJet_memLp
        (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) contDiff_const D q hw A hb0 a).toLp
          (fun x => q x • multiplicationRawJet (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
            D a x))) := by
  refine weightedRawProduct_toLp_tendsto (expandingPlaneCoefficient (E := E))
    (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
    (fun n => (expandingPlaneCoefficient_contDiff n).of_le (by simp))
    contDiff_const D q hw A hA hb hb0 ?_ a
  intro l w x e
  have he := expandingPlaneCutoff_coefficient_jet_eventually_eq (E := E) x l.val w
  have hae : (fun n => orderedCoefficientDerivative (expandingPlaneCoefficient (E := E) n)
      l.val w x e) =ᶠ[atTop]
      (fun _ => orderedCoefficientDerivative (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
        l.val w x e) := he.mono (fun _ hn => congrArg (fun L : E →L[ℝ] E => L e) hn)
  exact tendsto_const_nhds.congr' hae.symm

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The normalized shear potential is a fixed frequency-linear readout of the actual drift. -/

def normalizedDriftCoefficientEmbedding (ξ : Fin 2 → ℂ) : Vec 2 →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  ∑ j : Fin 2, (ContinuousLinearMap.proj j).smulRight (ContinuousLinearMap.mul ℝ ℂ (ξ j))

theorem normalizedDriftCoefficientEmbedding_apply (ξ : Fin 2 → ℂ) (a : Vec 2) (z : ℂ) :
    normalizedDriftCoefficientEmbedding ξ a z = (∑ j : Fin 2, (a j : ℂ) * ξ j) * z := by
  simp only [normalizedDriftCoefficientEmbedding, Fin.sum_univ_two, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_apply,
    ContinuousLinearMap.mul_apply', Complex.real_smul]
  ring

theorem normalizedDriftCoefficientEmbedding_coupling (η : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    normalizedDriftCoefficientEmbedding ξ (Real.sqrt η • v t x) =
      ContinuousLinearMap.mul ℝ ℂ (fibreDriftCoupling η v ξ t x) := by
  ext z
  rw [normalizedDriftCoefficientEmbedding_apply]
  simp only [fibreDriftCoupling, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, ContinuousLinearMap.mul_apply']
  ring

theorem normalizedDriftCoefficientEmbedding_norm_le (ξ : Fin 2 → ℂ) :
    ‖normalizedDriftCoefficientEmbedding ξ‖ ≤ 2 * fibreNorm ξ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (fibreNorm_nonneg ξ))
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) (fibreNorm_nonneg ξ)) (norm_nonneg a))
  intro z
  rw [normalizedDriftCoefficientEmbedding_apply, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  calc
    ‖∑ j : Fin 2, (a j : ℂ) * ξ j‖ ≤ ∑ j : Fin 2, ‖(a j : ℂ) * ξ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, ‖a‖ * fibreNorm ξ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (norm_le_pi_norm a j) (fibreNorm_coordinate_le ξ j)
        (norm_nonneg _) (norm_nonneg _)
    _ = 2 * fibreNorm ξ * ‖a‖ := by simp only [Fin.sum_univ_two]; ring

end AVRegularity.CycleWords
end

section
open MeasureTheory UnitAddTorus Homogenization
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual bounded multiplication by continuous torus symbols, with operator norm control. -/

local instance continuousTorusSymbolMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

variable {X : Type*} [MeasurableSpace X]

def continuousTorusSymbolMultiplication (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2).comp
    (continuousTorusSymbolPullbackCLM μ q hq)

theorem continuousTorusSymbolMultiplication_ae (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) (f : Lp ℂ 2 μ) :
    continuousTorusSymbolMultiplication μ q hq b f =ᵐ[μ] fun x => b (q x) * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (continuousTorusSymbolPullback μ q hq b) f (r := 2)
  filter_upwards [h, continuousTorusSymbolPullback_ae μ q hq b] with x hx hb
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2
    (continuousTorusSymbolPullback μ q hq b) f x = _
  rw [hx, hb]
  rfl

def planePeriodicSymbolMultiplication : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ]
    (Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec 2))) :=
  continuousTorusSymbolMultiplication volume torusQuotient
    measurePreserving_torusQuotient_cell.measurable

def scalarTorusSymbolMultiplication :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] (ScalarTorusL2 →L[ℂ] ScalarTorusL2) :=
  continuousTorusSymbolMultiplication volume id measurable_id

theorem planePeriodicSymbolMultiplication_mode (m : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planePeriodicSymbolMultiplication (mFourier m) f = planeIntegerModulationOperator m f := by
  apply Lp.ext
  filter_upwards [continuousTorusSymbolMultiplication_ae volume torusQuotient
    measurePreserving_torusQuotient_cell.measurable (mFourier m) f,
    planeIntegerModulationOperator_ae m f] with x h₁ h₂
  change planePeriodicSymbolMultiplication (mFourier m) f x =
    mFourier m (torusQuotient x) * f x at h₁
  rw [h₁, h₂, cellComplexFourierMode_eq]
  rfl

theorem scalarTorusSymbolMultiplication_mode (m : Fin 2 → ℤ) (u : ScalarTorusL2) :
    scalarTorusSymbolMultiplication (mFourier m) u = scalarTorusIntegerModulationOperator m u := by
  apply Lp.ext
  filter_upwards [continuousTorusSymbolMultiplication_ae volume id measurable_id (mFourier m) u,
    scalarTorusIntegerModulationOperator_ae m u] with z h₁ h₂
  change scalarTorusSymbolMultiplication (mFourier m) u z =
    mFourier m (id z) * u z at h₁
  rw [h₁, h₂, id_eq]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Actual real parts of complex plane Sobolev carriers and their native readouts. -/

def planeComplexRealPart (K : ℕ) : PlaneHk Set.univ K ℂ →L[ℝ] PlaneHk Set.univ K ℝ :=
  mapPlaneHkOperator K Complex.reCLM

def planeComplexRealPartL2 : Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Vec 2)) := Complex.reCLM.compLpL 2 volume

theorem planeComplexRealPart_component (K : ℕ) (u : PlaneHk Set.univ K ℂ) (a : JetIndex2 K) :
    univToPlane ((planeComplexRealPart K u).val a) =
      planeComplexRealPartL2 (univToPlane (u.val a)) := by
  rw [planeComplexRealPart, mapPlaneHkOperator_apply, mapPlaneHk_component, univToPlane_fiberMap]
  rfl

theorem planeComplexRealPart_value (K : ℕ) (u : PlaneHk Set.univ K ℂ) :
    planeHkValueOperator K (planeComplexRealPart K u) =
      planeComplexRealPartL2 (planeHkValueOperator K u) := by
  rw [planeHkValueOperator_apply, planeComplexRealPart_component, planeHkValueOperator_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Native plane value readouts commute with fixed fiber maps. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeHkFiberValue (K : ℕ) (L : E →L[ℝ] F) (u : PlaneHk Set.univ K E) :
    planeHkValueOperator K (mapPlaneHk L u) =
      L.compLpL 2 volume (planeHkValueOperator K u) := by
  rw [planeHkValueOperator_apply, mapPlaneHk_component, univToPlane_fiberMap,
    planeHkValueOperator_apply]

theorem planeHkFiberTruncate {J K : ℕ} (hJK : J ≤ K) (L : E →L[ℝ] F)
    (u : PlaneHk Set.univ K E) :
    mapPlaneHk L (truncatePlaneHk hJK u) =
      truncatePlaneHk hJK (mapPlaneHk L u) := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  simp only [mapPlaneHk_component, truncatePlaneHk_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The existing adjoint reconstruction is the two-sided genuine Bloch inverse. -/

theorem planeScalarBlochTransform_reconstruct (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P))) :
    planeScalarBlochTransform a P hP (planeScalarBlochReconstruct a P hP F) = F := by
  obtain ⟨f, rfl⟩ := planeScalarBlochTransform_surjective a P hP F
  rw [planeScalarBlochReconstruct_transform]

theorem planeScalarBlochReconstruct_norm (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P))) :
    ‖planeScalarBlochReconstruct a P hP F‖ = ‖F‖ := by
  rw [← planeScalarBlochTransform_norm a P hP (planeScalarBlochReconstruct a P hP F),
    planeScalarBlochTransform_reconstruct]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Literal native L2 multipliers for bounded measurable torus symbols and their plane pullbacks. -/

local instance measurableTorusSymbolMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem measurableTorusSymbol_memLp_top
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b) (C : ℝ)
    (hC : ∀ x, ‖b x‖ ≤ C) : MemLp b ∞ (volume : Measure (UnitAddTorus (Fin 2))) :=
  memLp_top_of_bound hb.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem measurableTorusSymbol_plane_memLp_top
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b) (C : ℝ)
    (hC : ∀ x, ‖b x‖ ≤ C) :
    MemLp (fun x : Vec 2 => b (torusQuotient x)) ∞ volume :=
  memLp_top_of_bound (hb.comp measurePreserving_torusQuotient_cell.measurable).aestronglyMeasurable
    C (Filter.Eventually.of_forall fun x => hC (torusQuotient x))

def measurableTorusSymbolMultiplication
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b) (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) :
    ScalarTorusL2 →L[ℂ] ScalarTorusL2 :=
  L2Multiplier.operator b (measurableTorusSymbol_memLp_top b hb C hC)

def planeMeasurableTorusSymbolMultiplication
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b) (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec 2)) :=
  L2Multiplier.operator (fun x => b (torusQuotient x))
    (measurableTorusSymbol_plane_memLp_top b hb C hC)

theorem continuousTorusSymbolMultiplication_eq_operator
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) :
    continuousTorusSymbolMultiplication μ q hq b =
      L2Multiplier.operator (fun x => b (q x)) (continuousTorusSymbolPullback_memLp μ q hq b) := by
  ext1 f
  apply Lp.ext
  exact (continuousTorusSymbolMultiplication_ae μ q hq b f).trans
    (L2Multiplier.operator_ae _ _ f).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Real plane testing is the literal real part of complex plane testing. -/

theorem planeComplexRealPartL2_ofRealL2 (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    planeComplexRealPartL2 (ofRealL2 volume f) = f := reL2_ofRealL2 volume f

theorem planeComplexRealPairing (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ f (ofRealL2 volume g) = inner ℝ (planeComplexRealPartL2 f) g := by
  change (∫ x, inner ℝ (f x) (ofRealL2 volume g x)) =
    ∫ x, inner ℝ (planeComplexRealPartL2 f x) (g x)
  apply integral_congr_ae
  filter_upwards [ofRealL2_ae volume g, Complex.reCLM.coeFn_compLpL f] with x hg hf
  change (planeComplexRealPartL2 f x) = (f x).re at hf
  rw [hg, hf, real_inner_eq_re_inner ℂ]
  rw [RCLike.inner_apply, Real.inner_apply]
  simp [mul_comm]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Fiber coordinates of native L2 fluxes commute with the actual component readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

def planeFluxFiberCoordinateCLM (e : E) : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => Lp ℝ 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => (planeFiberCoordinateCLM e).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) i))

omit [BorelSpace E] in
theorem planeFluxFiberCoordinateCLM_apply (e : E) (S : PlaneFluxL2 E) (i : Fin 2) :
    planeFluxFiberCoordinateCLM e S i = planeFiberCoordinateCLM e (S i) := rfl

omit [BorelSpace E] in
theorem planeFluxFiberCoordinateCLM_ae (e : E) (S : PlaneFluxL2 E) (i : Fin 2) :
    planeFluxFiberCoordinateCLM e S i =ᵐ[volume] fun x => inner ℝ e (S i x) :=
  (InnerProductSpace.toDual ℝ E e).coeFn_compLpL (S i)

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Finite full cell traces recover strong time regularity of their actual coefficient states. -/

theorem cellGalerkinL2Initial_value_fixed (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinL2Initial N (cellGalerkinValue N u) = u := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N (cellGalerkinValue N u)))
    (cellGalerkinValue N z) = inner ℝ (cellGalerkinValue N u) (cellGalerkinValue N z)
  exact cellGalerkinL2Initial_pairing N _ z

theorem cellGalerkin_value_strongTime_pullback (N : ℕ) {a b : ℝ}
    {y dy : ℝ → CellGalerkinSpace (E := ℂ) N}
    (h : StrongTimeRegularity a b (fun t => cellGalerkinValue N (y t))
      (fun t => cellGalerkinValue N (dy t))) :
    StrongTimeRegularity a b y dy := by
  have hm := h.map (cellGalerkinL2InitialCLM N)
  simpa only [cellGalerkinL2InitialCLM_apply, cellGalerkinL2Initial_value_fixed] using hm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.CoupledEnergyPlane
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A genuine bounded coefficient acting on a Fourier basis vector shifts its Fourier coefficients. -/

local instance torusMultiplierFourierBasisMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance torusMultiplierFourierBasisProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem measurableTorusSymbolMultiplication_basis_coeff
    (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) (n k : Fin 2 → ℤ) :
    mFourierCoeff (measurableTorusSymbolMultiplication b hb C hC
      (mFourierBasis (d := Fin 2) n)) k = mFourierCoeff b (k - n) := by
  let hm : MemLp b 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
    (measurableTorusSymbol_memLp_top b hb C hC).mono_exponent (by simp)
  let q : ScalarTorusL2 := hm.toLp b
  have hq : q =ᵐ[volume] b := hm.coeFn_toLp
  have hbase : (mFourierBasis (d := Fin 2) n : ScalarTorusL2) =ᵐ[volume] mFourier n := by
    simpa only [coe_mFourierBasis] using coeFn_mFourierLp 2 n
  have he : measurableTorusSymbolMultiplication b hb C hC
      (mFourierBasis (d := Fin 2) n) = scalarTorusIntegerModulationOperator n q := by
    apply Lp.ext
    filter_upwards [L2Multiplier.operator_ae b
      (measurableTorusSymbol_memLp_top b hb C hC) (mFourierBasis (d := Fin 2) n),
      scalarTorusIntegerModulationOperator_ae n q, hq, hbase] with x hmultip hmod hqx hbx
    change measurableTorusSymbolMultiplication b hb C hC
      (mFourierBasis (d := Fin 2) n) x = b x * (mFourierBasis (d := Fin 2) n) x at hmultip
    rw [hmultip, hmod, hqx, hbx, mul_comm]
  rw [he, scalarTorusIntegerModulationOperator_fourierCoeff]
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hq] with x hx
  rw [hx]

end AVRegularity.CycleWords
end

section
open MeasureTheory UnitAddTorus Filter
open AVRegularity.CoupledEnergyPlane
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Strong convergence of actual continuous torus multipliers to a measurable symbol. -/

local instance continuousTorusMultiplierStrongLimitMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

variable {X : Type*} [MeasurableSpace X]

theorem tendsto_continuousTorusSymbolMultiplication
    (μ : Measure X) (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (c : ℕ → C(UnitAddTorus (Fin 2), ℂ)) (b : UnitAddTorus (Fin 2) → ℂ)
    (hb : Measurable b) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n x, ‖c n x‖ ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => c n (q x)) atTop (𝓝 (b (q x))))
    (f : Lp ℂ 2 μ) :
    Tendsto (fun n => continuousTorusSymbolMultiplication μ q hq (c n) f) atTop
      (𝓝 (L2Multiplier.operator (fun x => b (q x))
        (memLp_top_of_bound (hb.comp hq).aestronglyMeasurable C
          (Eventually.of_forall fun x => hbC (q x))) f)) := by
  have hh := tendsto_L2Multiplier_of_ae (fun n x => c n (q x)) (fun x => b (q x))
    (fun n => continuousTorusSymbolPullback_memLp μ q hq (c n))
    (memLp_top_of_bound (hb.comp hq).aestronglyMeasurable C
      (Eventually.of_forall fun x => hbC (q x))) C hC
    (fun n => Eventually.of_forall fun x => hc n (q x))
    (Eventually.of_forall fun x => hbC (q x)) ht f
  apply (tendsto_congr (fun n => ?_)).mpr hh
  exact congrArg (fun L => L f)
    (continuousTorusSymbolMultiplication_eq_operator μ q hq (c n))

theorem continuousTorusSymbolMultiplication_norm_le_bound
    (μ : Measure X) (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (c : C(UnitAddTorus (Fin 2), ℂ)) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ x, ‖c x‖ ≤ C) :
    ‖continuousTorusSymbolMultiplication μ q hq c‖ ≤ C := by
  rw [continuousTorusSymbolMultiplication_eq_operator]
  exact L2Multiplier.operator_norm_le _ _ hC (Eventually.of_forall fun x => hc (q x))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original charted constituents inherit the molecular cell reserve budget on whole-label slices. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyMolecular_ae_mixed_reserve (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ᵐ t ∂volume, ∀ a b : ℕ, a + b ≤ K v →
      (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' =>
          iteratedFDeriv ℝ b (F.flux p c v u γ d I t X') z) X‖ *
          derivativeReserveFactor (ρ / e) (K v) (d - 2) ≤
        ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
          ((ν * ρ ^ (d - 2)) *
            (((K v).factorial : ℝ) / ((K v + (d - 2)).factorial : ℝ)))) *
          (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)).toReal := by
  have hM := molecularEnvelope_constituent_jet_ne_top F π hπ K dom ν e E ρ hν he hρ
    C J b₀ henv v u γ hγ d hd I j hj
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro b
  by_cases hab : a + b ≤ K v
  · have hf (t : ℝ) (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p c) :
        IsBoxSmooth (j + a) b (F.flux p c v u γ d I t) := by
      apply Weighted.isBoxSmooth_of_joint_contDiff
      have hh := molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
        henv.1 p c t ht v u γ d I
      exact hh.of_le (by exact_mod_cast (by omega : j + a + b ≤ K v + J))
    have hh := molecularNative_ae_mixed_reserve ν e E ρ hν he hE hρ (K v) (d - 2)
      j a b hab (fun x : F.Index => dom x.1 x.2)
      (fun x => F.flux x.1 x.2 v u γ d I) ⟨p, c⟩ hf hM
    filter_upwards [hh] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _ h => (hab h).elim)

end AVRegularity.CycleWords
end
