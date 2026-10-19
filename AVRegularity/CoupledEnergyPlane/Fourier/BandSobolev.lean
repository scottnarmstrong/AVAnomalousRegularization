-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertNaturality
public import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual L² frequency projections for the source spectral approximation.
The spatial carrier remains `Vec 2`. Mathlib's frequency coordinate is cycles
per unit length, so angular frequency balls include the explicit factor 2π.
These ordinary helpers do not assert real-valued preservation or the Sobolev
derivative bounds, which are separate proof obligations. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Literal conjugation of a measurable frequency indicator by the Fourier unitary. -/
def spectralProjection (s : Set (Vec 2)) (hs : MeasurableSet s) :
    Lp F 2 (volume : Measure (Vec 2)) →L[ℂ] Lp F 2 (volume : Measure (Vec 2)) :=
  fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((L2Indicator.operator s hs).comp
      fourierL2.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The Fourier transform of the projection is exactly the indicator multiplier. -/
theorem fourier_spectralProjection (s : Set (Vec 2)) (hs : MeasurableSet s)
    (f : Lp F 2 (volume : Measure (Vec 2))) :
    fourierL2 (spectralProjection s hs f) = L2Indicator.operator (𝕜 := ℂ) s hs (fourierL2 f) :=
  fourierL2.apply_symm_apply _

theorem spectralProjection_norm_apply_le (s : Set (Vec 2)) (hs : MeasurableSet s)
    (f : Lp F 2 (volume : Measure (Vec 2))) : ‖spectralProjection s hs f‖ ≤ ‖f‖ := by
  rw [← fourierL2_norm (spectralProjection s hs f), fourier_spectralProjection]
  exact (L2Indicator.value_norm_le s hs (fourierL2 f)).trans_eq (fourierL2_norm f)

theorem spectralProjection_idempotent (s : Set (Vec 2)) (hs : MeasurableSet s)
    (f : Lp F 2 (volume : Measure (Vec 2))) :
    spectralProjection s hs (spectralProjection s hs f) = spectralProjection s hs f := by
  apply fourierL2.injective
  simp only [fourier_spectralProjection, L2Indicator.operator_idempotent]

theorem spectralProjection_inner (s : Set (Vec 2)) (hs : MeasurableSet s)
    (f g : Lp F 2 (volume : Measure (Vec 2))) :
    inner ℂ (spectralProjection s hs f) g = inner ℂ f (spectralProjection s hs g) := by
  rw [← fourierL2_inner (spectralProjection s hs f) g,
    ← fourierL2_inner f (spectralProjection s hs g),
    fourier_spectralProjection, fourier_spectralProjection]
  exact L2Indicator.operator_inner s hs _ _

theorem tendsto_spectralProjection_of_eventually_mem (s : ℕ → Set (Vec 2))
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ∀ ξ, ∀ᶠ n in atTop, ξ ∈ s n)
    (f : Lp F 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => spectralProjection (s n) (hs n) f) atTop (𝓝 f) := by
  have h := fourierL2.symm.continuous.tendsto (fourierL2 f) |>.comp
    (L2Indicator.tendsto_operator_of_eventually_mem (𝕜 := ℂ) s hs hcover (fourierL2 f))
  simpa only [spectralProjection, ContinuousLinearMap.comp_apply, Function.comp_def,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- The source ball of angular frequencies of size at most N. -/
def frequencyBall (N : ℕ) : Set (Vec 2) :=
  {ξ | 2 * Real.pi * ‖coordinateHilbertEquiv.symm ξ‖ ≤ (N : ℝ)}

theorem frequencyBall_measurableSet (N : ℕ) : MeasurableSet (frequencyBall N) := by
  exact (isClosed_le
    ((continuous_norm.comp coordinateHilbertEquiv.symm.continuous).const_mul (2 * Real.pi))
    continuous_const).measurableSet

theorem frequencyBall_neg (N : ℕ) (ξ : Vec 2) : -ξ ∈ frequencyBall N ↔ ξ ∈ frequencyBall N := by
  change 2 * Real.pi * ‖coordinateHilbertEquiv.symm (-ξ)‖ ≤ (N : ℝ) ↔ _
  rw [map_neg, norm_neg]
  rfl

theorem eventually_mem_frequencyBall (ξ : Vec 2) : ∀ᶠ N in atTop, ξ ∈ frequencyBall N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * Real.pi * ‖coordinateHilbertEquiv.symm ξ‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (Nat.cast_le.mpr hn)

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory SchwartzMap
open scoped FourierTransform Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Reflection of actual L² functions and the inverse Fourier transform. -/

section Measure
variable {V F : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableNeg V]
  {μ : Measure V} [μ.IsNegInvariant] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Literal reflection x ↦ −x as an isometry on L². -/
def reflectL2 : Lp F 2 μ →ₗᵢ[ℂ] Lp F 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (Measure.measurePreserving_neg μ)

theorem reflectL2_ae (f : Lp F 2 μ) :
    reflectL2 f =ᵐ[μ] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg μ)

theorem reflectL2_conjugate (f : Lp ℂ 2 μ) :
    reflectL2 (conjugateL2 μ f) = conjugateL2 μ (reflectL2 f) := by
  apply Lp.ext
  have h := (Measure.measurePreserving_neg μ).quasiMeasurePreserving.ae
    (conjugateL2_ae μ f)
  filter_upwards [reflectL2_ae (conjugateL2 μ f), conjugateL2_ae μ (reflectL2 f),
    reflectL2_ae f, h] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, h₃]

end Measure

section Schwartz
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem reflectL2_toLp (f : 𝓢(V, F)) : reflectL2 (f.toLp 2 (volume : Measure V)) =
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V)) f).toLp 2 (volume : Measure V) := by
  apply Lp.ext
  have h := (Measure.measurePreserving_neg (volume : Measure V)).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 (volume : Measure V))
  filter_upwards [reflectL2_ae (f.toLp 2 (volume : Measure V)), h,
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V)) f).coeFn_toLp 2 (volume : Measure V)]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

variable [CompleteSpace F]

theorem fourierInv_eq_reflectL2_fourier (f : Lp F 2 (volume : Measure V)) :
    𝓕⁻ f = reflectL2 (𝓕 f) := by
  let p := fun f : Lp F 2 (volume : Measure V) => 𝓕⁻ f = reflectL2 (𝓕 f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (F := F) (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ V F).symm.continuous
    · exact reflectL2.continuous.comp (Lp.fourierTransformₗᵢ V F).continuous
  · intro g
    change 𝓕⁻ (g.toLp 2) = reflectL2 (𝓕 (g.toLp 2))
    rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq, reflectL2_toLp,
      SchwartzMap.fourierInv_apply_eq]

theorem fourier_conjugateL2_reflection (f : Lp ℂ 2 (volume : Measure V)) :
    𝓕 (conjugateL2 volume f) = reflectL2 (conjugateL2 volume (𝓕 f)) := by
  rw [fourier_conjugateL2, fourierInv_eq_reflectL2_fourier, reflectL2_conjugate]

end Schwartz

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform SchwartzMap ENNReal
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The actual directional derivative of a bounded-frequency L² approximation.
This internal Hilbert-coordinate statement includes its compact-test identity;
transport to the source Vec coordinates and Sobolev graph is a subsequent step. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The source angular-frequency region in auxiliary Hilbert coordinates. -/
def angularBand (N : ℕ) : Set V := {ξ | 2 * Real.pi * ‖ξ‖ ≤ N}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem angularBand_measurableSet (N : ℕ) : MeasurableSet (angularBand (V := V) N) :=
  (isClosed_le (continuous_const.mul continuous_norm) continuous_const).measurableSet

/-- The literal angular-frequency derivative multiplier, cut off on the stated band. -/
def bandDirectionSymbol (N : ℕ) (v : V) : V → ℂ :=
  (angularBand N).indicator (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ v : ℂ))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem bandDirectionSymbol_bound (N : ℕ) (v ξ : V) :
    ‖bandDirectionSymbol N v ξ‖ ≤ N * ‖v‖ := by
  by_cases hξ : ξ ∈ angularBand N
  · rw [bandDirectionSymbol, Set.indicator_of_mem hξ, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one]
    have hc : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    rw [hc]
    calc
      2 * Real.pi * ‖inner ℝ ξ v‖ ≤ 2 * Real.pi * (‖ξ‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm ξ v) (by positivity)
      _ = (2 * Real.pi * ‖ξ‖) * ‖v‖ := (mul_assoc _ _ _).symm
      _ ≤ N * ‖v‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  · rw [bandDirectionSymbol, Set.indicator_of_notMem hξ, norm_zero]
    positivity

theorem bandDirectionSymbol_memLp (N : ℕ) (v : V) :
    MemLp (bandDirectionSymbol N v) ∞ (volume : Measure V) := by
  have hc : Continuous (fun ξ : V => (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ v : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.inner continuous_const))
  exact memLp_top_of_bound (hc.aestronglyMeasurable.indicator (angularBand_measurableSet N))
    ((N : ℝ) * ‖v‖) (Filter.Eventually.of_forall (bandDirectionSymbol_bound N v))

theorem band_direction_product_ae (N : ℕ) (v : V) (f : Lp ℂ 2 (volume : Measure V)) :
    L2Multiplier.operator (bandDirectionSymbol N v) (bandDirectionSymbol_memLp N v) f =ᵐ[volume]
      fun ξ => (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ v : ℂ) *
        (L2Indicator.operator (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) f) ξ := by
  filter_upwards [L2Multiplier.operator_ae (bandDirectionSymbol N v)
    (bandDirectionSymbol_memLp N v) f,
    L2Indicator.operator_ae (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) f] with ξ hx hy
  rw [hx, hy]
  by_cases hξ : ξ ∈ angularBand N
  · simp only [bandDirectionSymbol, Set.indicator_of_mem hξ]
  · simp only [bandDirectionSymbol, Set.indicator_of_notMem hξ, zero_mul, mul_zero]

theorem lineDerivOp_fourierInv_band (N : ℕ) (v : V) (f : Lp ℂ 2 (volume : Measure V)) :
    ∂_{v} ((𝓕⁻ (L2Indicator.operator (𝕜 := ℂ) (angularBand N)
      (angularBand_measurableSet N) f) : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) =
      ((𝓕⁻ (L2Multiplier.operator (bandDirectionSymbol N v)
        (bandDirectionSymbol_memLp N v) f) : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) :=
  lineDerivOp_fourierInv_L2 _ _ v (band_direction_product_ae N v f)

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped FourierTransform SchwartzMap ENNReal
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Every finite ordered coordinate derivative of the actual spectral cutoff,
including the exact N^m bound. -/

/-- The literal bounded-frequency ordered derivative symbol. -/
def bandWordSymbol (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) : HilbertTwo → ℂ :=
  (angularBand N).indicator (fun ξ => ∏ j : Fin m,
    (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ (coordinateVector (w j)) : ℂ))

theorem bandWordSymbol_zero (N : ℕ) (w : Fin 0 → Fin 2) :
    bandWordSymbol N w = (angularBand N).indicator (fun _ => (1 : ℂ)) := by
  funext ξ
  simp only [bandWordSymbol, Fin.prod_univ_zero]

theorem bandWordSymbol_snoc (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (ξ : HilbertTwo) :
    bandWordSymbol N (Fin.snoc w i) ξ =
      ((2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ (coordinateVector i) : ℂ)) *
        bandWordSymbol N w ξ := by
  by_cases hξ : ξ ∈ angularBand N
  · simp only [bandWordSymbol, Set.indicator_of_mem hξ, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    exact mul_comm _ _
  · simp only [bandWordSymbol, Set.indicator_of_notMem hξ, mul_zero]

theorem bandWordSymbol_bound (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (ξ : HilbertTwo) :
    ‖bandWordSymbol N w ξ‖ ≤ (N : ℝ) ^ m := by
  by_cases hξ : ξ ∈ angularBand N
  · rw [bandWordSymbol, Set.indicator_of_mem hξ, norm_prod]
    calc
      _ ≤ ∏ _j : Fin m, (N : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        have h := bandDirectionSymbol_bound N (coordinateVector (w j)) ξ
        simpa only [bandDirectionSymbol, Set.indicator_of_mem hξ,
          coordinateVector_norm, mul_one] using h
      _ = _ := by simp
  · rw [bandWordSymbol, Set.indicator_of_notMem hξ, norm_zero]
    positivity

theorem bandWordSymbol_memLp (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) :
    MemLp (bandWordSymbol N w) ∞ (volume : Measure HilbertTwo) := by
  have hc : Continuous (fun ξ : HilbertTwo => ∏ j : Fin m,
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ (coordinateVector (w j)) : ℂ)) := by
    apply continuous_finsetProd
    intro j _
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_id.inner continuous_const))
  exact memLp_top_of_bound (hc.aestronglyMeasurable.indicator (angularBand_measurableSet N))
    ((N : ℝ) ^ m) (Filter.Eventually.of_forall (bandWordSymbol_bound N w))

theorem bandWord_operator_zero (N : ℕ) (w : Fin 0 → Fin 2)
    (f : Lp ℂ 2 (volume : Measure HilbertTwo)) :
    L2Multiplier.operator (bandWordSymbol N w) (bandWordSymbol_memLp N w) f =
      L2Indicator.operator (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) f := by
  apply Lp.ext
  filter_upwards [L2Multiplier.operator_ae (bandWordSymbol N w)
    (bandWordSymbol_memLp N w) f,
    L2Indicator.operator_ae (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) f] with ξ hx hy
  rw [hx, hy, bandWordSymbol_zero]
  by_cases hξ : ξ ∈ angularBand N
  · simp only [Set.indicator_of_mem hξ, one_mul]
  · simp only [Set.indicator_of_notMem hξ, zero_mul]

theorem lineDerivOp_fourierInv_bandWord (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) (i : Fin 2)
    (f : Lp ℂ 2 (volume : Measure HilbertTwo)) :
    ∂_{coordinateVector i} ((𝓕⁻ (L2Multiplier.operator (bandWordSymbol N w)
      (bandWordSymbol_memLp N w) f) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
      ((𝓕⁻ (L2Multiplier.operator (bandWordSymbol N (Fin.snoc w i))
        (bandWordSymbol_memLp N (Fin.snoc w i)) f) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  apply lineDerivOp_fourierInv_L2
  filter_upwards [L2Multiplier.operator_ae (bandWordSymbol N w)
    (bandWordSymbol_memLp N w) f,
    L2Multiplier.operator_ae (bandWordSymbol N (Fin.snoc w i))
    (bandWordSymbol_memLp N (Fin.snoc w i)) f] with ξ hx hy
  rw [hx, hy, bandWordSymbol_snoc, mul_assoc]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Spectral cutoff commutes with an existing L² weak derivative. The
frequency identity is derived from the distribution derivative hypothesis. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_derivative_ae (f g : Lp ℂ 2 (volume : Measure V)) (v : V)
    (hfg : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ))) :
    𝓕 g =ᵐ[volume] fun ξ =>
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ v : ℂ) * (𝓕 f : Lp ℂ 2 volume) ξ := by
  apply frequency_product_ae_of_toTemperedDistribution
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq,
    ← hfg, TemperedDistribution.fourier_lineDerivOp_eq]
theorem band_derivative_multiplier_eq (N : ℕ) (f g : Lp ℂ 2 (volume : Measure V))
    (v : V) (hfg : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ))) :
    L2Multiplier.operator (bandDirectionSymbol N v) (bandDirectionSymbol_memLp N v) (𝓕 f) =
      L2Indicator.operator (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) (𝓕 g) := by
  apply Lp.ext
  filter_upwards [L2Multiplier.operator_ae (bandDirectionSymbol N v)
    (bandDirectionSymbol_memLp N v) (𝓕 f),
    L2Indicator.operator_ae (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N) (𝓕 g),
    fourier_derivative_ae f g v hfg] with ξ hx hy hz
  rw [hx, hy]
  by_cases hξ : ξ ∈ angularBand N
  · rw [bandDirectionSymbol, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, hz]
  · rw [bandDirectionSymbol, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, zero_mul]

theorem lineDerivOp_band_projection (N : ℕ) (f g : Lp ℂ 2 (volume : Measure V))
    (v : V) (hfg : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ))) :
    ∂_{v} ((𝓕⁻ (L2Indicator.operator (𝕜 := ℂ) (angularBand N)
      (angularBand_measurableSet N) (𝓕 f)) : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) =
      ((𝓕⁻ (L2Indicator.operator (𝕜 := ℂ) (angularBand N)
        (angularBand_measurableSet N) (𝓕 g)) : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) := by
  rw [lineDerivOp_fourierInv_band, band_derivative_multiplier_eq N f g v hfg]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Symmetric frequency projections commute with actual complex conjugation
and therefore preserve real scalar data. -/

theorem coordinateL2Equiv_conjugate (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (conjugateL2 volume f) = conjugateL2 volume (coordinateL2Equiv f) := by
  apply Lp.ext
  have h := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
    (conjugateL2_ae volume f)
  filter_upwards [coordinateL2Equiv_ae (conjugateL2 volume f),
    conjugateL2_ae volume (coordinateL2Equiv f), coordinateL2Equiv_ae f, h]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, h₃]

theorem coordinateL2Equiv_reflect (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (reflectL2 f) = reflectL2 (coordinateL2Equiv f) := by
  apply Lp.ext
  have h := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae (reflectL2_ae f)
  have hn := (Measure.measurePreserving_neg (volume : Measure HilbertTwo)).quasiMeasurePreserving.ae
    (coordinateL2Equiv_ae f)
  filter_upwards [coordinateL2Equiv_ae (reflectL2 f), reflectL2_ae (coordinateL2Equiv f), h, hn]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₂, h₄]
  rfl

theorem fourierL2_conjugate (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    fourierL2 (conjugateL2 volume f) = reflectL2 (conjugateL2 volume (fourierL2 f)) := by
  apply coordinateL2Equiv.injective
  rw [coordinate_fourierL2, coordinateL2Equiv_conjugate, fourier_conjugateL2_reflection,
    coordinateL2Equiv_reflect, coordinateL2Equiv_conjugate, coordinate_fourierL2]

theorem indicator_conjugate (s : Set (Vec 2)) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    L2Indicator.operator (𝕜 := ℂ) s hs (conjugateL2 volume f) =
      conjugateL2 volume (L2Indicator.operator (𝕜 := ℂ) s hs f) := by
  apply Lp.ext
  filter_upwards [L2Indicator.operator_ae (𝕜 := ℂ) s hs (conjugateL2 volume f),
    conjugateL2_ae volume (L2Indicator.operator (𝕜 := ℂ) s hs f),
    conjugateL2_ae volume f, L2Indicator.operator_ae (𝕜 := ℂ) s hs f]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₄]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h₃]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, star_zero]

theorem indicator_reflect (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    L2Indicator.operator (𝕜 := ℂ) s hs (reflectL2 f) =
      reflectL2 (L2Indicator.operator (𝕜 := ℂ) s hs f) := by
  apply Lp.ext
  have h := (Measure.measurePreserving_neg (volume : Measure (Vec 2))).quasiMeasurePreserving.ae
    (L2Indicator.operator_ae (𝕜 := ℂ) s hs f)
  filter_upwards [L2Indicator.operator_ae (𝕜 := ℂ) s hs (reflectL2 f),
    reflectL2_ae (L2Indicator.operator (𝕜 := ℂ) s hs f), reflectL2_ae f, h]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₄]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((heven x).mpr hx), h₃]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hneg => hx ((heven x).mp hneg))]

theorem spectralProjection_conjugate (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    spectralProjection s hs (conjugateL2 volume f) = conjugateL2 volume (spectralProjection s hs f) := by
  apply fourierL2.injective
  rw [fourier_spectralProjection, fourierL2_conjugate, fourierL2_conjugate,
    fourier_spectralProjection, indicator_reflect s hs heven, indicator_conjugate]

/-- The literal projection preserves the real subspace of complex L². -/
theorem spectralProjection_real (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (hf : conjugateL2 volume f = f) :
    conjugateL2 volume (spectralProjection s hs f) = spectralProjection s hs f := by
  rw [← spectralProjection_conjugate s hs heven, hf]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The symmetric frequency projection on actual real scalar L² data.
Its characterization is proved through the literal inclusion into complex L². -/

section Values
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Literal inclusion of real-valued L² classes into complex-valued classes. -/
def ofRealL2 : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

/-- Literal real part of an L² class. -/
def reL2 : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

theorem ofRealL2_ae (f : Lp ℝ 2 μ) : ofRealL2 μ f =ᵐ[μ] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem reL2_ae (f : Lp ℂ 2 μ) : reL2 μ f =ᵐ[μ] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

theorem reL2_ofRealL2 (f : Lp ℝ 2 μ) : reL2 μ (ofRealL2 μ f) = f := by
  apply Lp.ext
  filter_upwards [reL2_ae μ (ofRealL2 μ f), ofRealL2_ae μ f] with x hx hy
  rw [hx, hy]
  rfl

theorem ofRealL2_injective : Function.Injective (ofRealL2 μ) := by
  intro f g h
  have hi := congrArg (reL2 μ) h
  simpa only [reL2_ofRealL2] using hi

theorem ofRealL2_norm (f : Lp ℝ 2 μ) : ‖ofRealL2 μ f‖ = ‖f‖ := by
  have heq : ∀ᵐ x ∂μ, ‖ofRealL2 μ f x‖ = ‖f x‖ := by
    filter_upwards [ofRealL2_ae μ f] with x hx
    rw [hx, Complex.norm_real]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.ge))

theorem ofRealL2_inner_re (f g : Lp ℝ 2 μ) :
    (inner ℂ (ofRealL2 μ f) (ofRealL2 μ g)).re = inner ℝ f g := by
  have h := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (𝕜 := ℂ) (ofRealL2 μ f) (ofRealL2 μ g)
  rw [← map_add, ofRealL2_norm, ofRealL2_norm, ofRealL2_norm] at h
  exact h.trans (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two f g).symm

theorem conjugateL2_ofRealL2 (f : Lp ℝ 2 μ) : conjugateL2 μ (ofRealL2 μ f) = ofRealL2 μ f := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae μ (ofRealL2 μ f), ofRealL2_ae μ f] with x hx hy
  rw [hx, hy]
  simp

theorem ofRealL2_reL2_of_conjugate_eq (f : Lp ℂ 2 μ) (hf : conjugateL2 μ f = f) :
    ofRealL2 μ (reL2 μ f) = f := by
  apply Lp.ext
  have h := conjugateL2_ae μ f
  rw [hf] at h
  filter_upwards [ofRealL2_ae μ (reL2 μ f), reL2_ae μ f, h] with x hx hy hz
  rw [hx, hy]
  have him := congrArg Complex.im hz
  change (f x).im = -(f x).im at him
  apply Complex.ext
  · rfl
  · change 0 = (f x).im
    linarith only [him]

end Values

/-- The actual real scalar spectral projection on a symmetric measurable region. -/
def realSpectralProjection (s : Set (Vec 2)) (hs : MeasurableSet s)
    (_heven : ∀ x, -x ∈ s ↔ x ∈ s) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  (reL2 volume).comp (((spectralProjection s hs).restrictScalars ℝ).comp (ofRealL2 volume))

/-- Complete characterization as the restriction of the Fourier indicator to real data. -/
theorem ofRealL2_realSpectralProjection (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    ofRealL2 volume (realSpectralProjection s hs heven f) = spectralProjection s hs (ofRealL2 volume f) :=
  ofRealL2_reL2_of_conjugate_eq volume _
    (spectralProjection_real s hs heven _ (conjugateL2_ofRealL2 volume f))

theorem realSpectralProjection_norm_apply_le (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    ‖realSpectralProjection s hs heven f‖ ≤ ‖f‖ := by
  rw [← ofRealL2_norm volume (realSpectralProjection s hs heven f),
    ofRealL2_realSpectralProjection s hs heven]
  exact (spectralProjection_norm_apply_le s hs _).trans_eq (ofRealL2_norm volume f)

theorem realSpectralProjection_idempotent (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    realSpectralProjection s hs heven (realSpectralProjection s hs heven f) =
      realSpectralProjection s hs heven f := by
  apply ofRealL2_injective volume
  rw [ofRealL2_realSpectralProjection s hs heven, ofRealL2_realSpectralProjection s hs heven,
    spectralProjection_idempotent]

theorem realSpectralProjection_inner (s : Set (Vec 2)) (hs : MeasurableSet s)
    (heven : ∀ x, -x ∈ s ↔ x ∈ s) (f g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (realSpectralProjection s hs heven f) g =
      inner ℝ f (realSpectralProjection s hs heven g) := by
  rw [← ofRealL2_inner_re volume, ofRealL2_realSpectralProjection s hs heven,
    spectralProjection_inner, ← ofRealL2_realSpectralProjection s hs heven,
    ofRealL2_inner_re]

theorem tendsto_realSpectralProjection (s : ℕ → Set (Vec 2)) (hs : ∀ n, MeasurableSet (s n))
    (heven : ∀ n x, -x ∈ s n ↔ x ∈ s n)
    (hcover : ∀ ξ, ∀ᶠ n in atTop, ξ ∈ s n) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => realSpectralProjection (s n) (hs n) (heven n) f) atTop (𝓝 f) := by
  have h := (reL2 volume).continuous.tendsto (ofRealL2 volume f) |>.comp
    (tendsto_spectralProjection_of_eventually_mem s hs hcover (ofRealL2 volume f))
  simpa only [realSpectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Function.comp_def, reL2_ofRealL2] using h

theorem tendsto_realFrequencyBall_projection (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Tendsto (fun N => realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
      (frequencyBall_neg N) f)
      atTop (𝓝 f) :=
  tendsto_realSpectralProjection frequencyBall frequencyBall_measurableSet
    frequencyBall_neg eventually_mem_frequencyBall f

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv Filter
open scoped SchwartzMap Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Closedness of the actual distribution derivative under strong L² limits. -/

theorem coordinate_distribution_tendsto
    {u : ℕ → Lp ℝ 2 (volume : Measure (Vec 2))} {v : Lp ℝ 2 (volume : Measure (Vec 2))}
    (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ((coordinateL2Equiv (ofRealL2 volume (u n)) : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ))) atTop
        (𝓝 ((coordinateL2Equiv (ofRealL2 volume v) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) := by
  have hc := ((ofRealL2 volume).continuous.tendsto v).comp h
  have hh := (coordinateL2Equiv.continuous.tendsto (ofRealL2 volume v)).comp hc
  exact ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.tendsto _).comp hh

theorem coordinate_lineDerivOp_closed
    {fn gn : ℕ → Lp ℝ 2 (volume : Measure (Vec 2))}
    {f g : Lp ℝ 2 (volume : Measure (Vec 2))} (i : Fin 2)
    (hf : Tendsto fn atTop (𝓝 f)) (hg : Tendsto gn atTop (𝓝 g))
    (hfg : ∀ n, ∂_{coordinateVector i}
      ((coordinateL2Equiv (ofRealL2 volume (fn n)) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) =
        ((coordinateL2Equiv (ofRealL2 volume (gn n)) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (ofRealL2 volume f) : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) =
        ((coordinateL2Equiv (ofRealL2 volume g) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  have hl := ((lineDerivOpCLM ℂ 𝓢'(HilbertTwo, ℂ) (coordinateVector i)).continuous.tendsto _).comp
    (coordinate_distribution_tendsto hf)
  have hr : Tendsto (fun n => ∂_{coordinateVector i}
      ((coordinateL2Equiv (ofRealL2 volume (fn n)) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)))
      atTop (𝓝 ((coordinateL2Equiv (ofRealL2 volume g) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) := by
    simpa only [hfg] using coordinate_distribution_tendsto hg
  exact tendsto_nhds_unique hl hr

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The actual real plane Fourier projection on an arbitrary finite Hilbert fiber. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Orthogonal real cutoff on a Hilbert-valued spatial L² class. -/
def hilbertProjection (N : ℕ) : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    Lp E 2 (volume : Measure (Vec 2)) :=
  hilbertLift (realSpectralProjection (frequencyBall N)
    (frequencyBall_measurableSet N) (frequencyBall_neg N))

theorem hilbertProjection_coordinate (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (k : Fin (Module.finrank ℝ E)) :
    fiberCoordinate k (hilbertProjection N u) =
      realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) (fiberCoordinate k u) := hilbertLift_coordinate _ _ _

theorem hilbertProjection_idempotent (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (hilbertProjection N u) = hilbertProjection N u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertProjection_coordinate, realSpectralProjection_idempotent]

theorem hilbertProjection_inner (N : ℕ) (u v : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (hilbertProjection N u) v = inner ℝ u (hilbertProjection N v) := by
  rw [fiberL2_inner, fiberL2_inner]
  simp only [hilbertProjection_coordinate, realSpectralProjection_inner]

theorem hilbertProjection_norm_le (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    ‖hilbertProjection N u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u)).mp
  rw [fiberL2_normSq, fiberL2_normSq]
  apply Finset.sum_le_sum
  intro k _
  rw [hilbertProjection_coordinate]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (realSpectralProjection_norm_apply_le _ _ _ _)

theorem tendsto_hilbertProjection (u : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun N => hilbertProjection N u) atTop (𝓝 u) := by
  have ht : Tendsto (fun N => hilbertProjection N u) atTop
      (𝓝 (hilbertLift (ContinuousLinearMap.id ℝ _) u)) := by
    simp only [hilbertProjection, hilbertLift, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    change Tendsto (fun N => ∑ k : Fin (Module.finrank ℝ E),
      fiberInjection k (realSpectralProjection (frequencyBall N)
        (frequencyBall_measurableSet N) (frequencyBall_neg N) (fiberCoordinate k u)))
      atTop (𝓝 (∑ k : Fin (Module.finrank ℝ E), fiberInjection k (fiberCoordinate k u)))
    apply tendsto_finsetSum
    intro k _
    exact (fiberInjection k).continuous.tendsto _ |>.comp
      (tendsto_realFrequencyBall_projection (fiberCoordinate k u))
  simpa only [hilbertLift_id] using ht

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Smooth real representatives give actual distribution derivatives after
the measure-preserving coordinate identification used by the Fourier transform. -/

theorem coordinate_ofRealL2_ae (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (ofRealL2 volume f) =ᵐ[volume]
      fun x : HilbertTwo => (f (WithLp.ofLp x) : ℂ) := by
  filter_upwards [coordinateL2Equiv_ae (ofRealL2 volume f),
    (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae (ofRealL2_ae volume f)]
    with x hx hy
  exact hx.trans hy

/-- The real source coordinate derivative agrees with the Hilbert-coordinate distribution. -/
theorem coordinate_lineDerivOp_of_smooth_real
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (F : Vec 2 → ℝ) (hF : Differentiable ℝ F)
    (hf : f =ᵐ[volume] F)
    (hg : g =ᵐ[volume] fun x => fderiv ℝ F x (basisVec i)) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (ofRealL2 volume f) : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) =
        ((coordinateL2Equiv (ofRealL2 volume g) : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  let G : HilbertTwo → ℂ := fun x => (F (coordinateHilbertEquiv x) : ℂ)
  have hG : Differentiable ℝ G :=
    Complex.ofRealCLM.differentiable.comp (hF.comp coordinateHilbertEquiv.differentiable)
  have hD (x : HilbertTwo) :
      fderiv ℝ G x (coordinateVector i) = (fderiv ℝ F (WithLp.ofLp x) (basisVec i) : ℂ) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x
      ((hF (coordinateHilbertEquiv x)).hasFDerivAt.comp x coordinateHilbertEquiv.hasFDerivAt)
    exact congrArg (fun A : HilbertTwo →L[ℝ] ℂ => A (coordinateVector i)) h.fderiv
  apply lineDerivOp_L2_of_smooth_representative _ _ _ G hG
  · filter_upwards [coordinate_ofRealL2_ae f,
      (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae hf] with x hx hy
    rw [hx, hy]
    rfl
  · filter_upwards [coordinate_ofRealL2_ae g,
      (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae hg] with x hx hy
    rw [hx, hy, hD]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CoupledEnergyPlane

/-! Exact L² pairings for the Fourier derivative multipliers used in the
projected weak equation. No integration-by-parts identity is assumed. -/

theorem L2Multiplier.operator_inner_neg_of_star_eq_neg
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℂ) (ha : MemLp a ∞ μ) (hstar : ∀ᵐ x ∂μ, star (a x) = -a x)
    (f g : Lp ℂ 2 μ) :
    inner ℂ (L2Multiplier.operator a ha f) g = -inner ℂ f (L2Multiplier.operator a ha g) := by
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [L2Multiplier.operator_ae a ha f, L2Multiplier.operator_ae a ha g, hstar]
    with x hf hg hs
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul]
  change (g x) * (star (a x) * star (f x)) = -((a x * g x) * star (f x))
  rw [hs]
  ring

namespace Fourier

theorem reL2_inner_eq_re_inner_ofReal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : Lp ℂ 2 μ) (g : Lp ℝ 2 μ) :
    inner ℝ (reL2 μ f) g = (inner ℂ f (ofRealL2 μ g)).re := by
  rw [L2.inner_def, L2.inner_def]
  change (∫ x, inner ℝ (reL2 μ f x) (g x) ∂μ) =
    RCLike.re (∫ x, inner ℂ (f x) (ofRealL2 μ g x) ∂μ)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f (ofRealL2 μ g))]
  apply integral_congr_ae
  filter_upwards [reL2_ae μ f, ofRealL2_ae μ g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, conj_trivial]
  change g x * (f x).re = ((g x : ℂ) * (starRingEnd ℂ) (f x)).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.conj_re]

theorem real_inner_reL2_eq_re_inner_ofReal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : Lp ℝ 2 μ) (g : Lp ℂ 2 μ) :
    inner ℝ f (reL2 μ g) = (inner ℂ (ofRealL2 μ f) g).re := by
  rw [real_inner_comm, reL2_inner_eq_re_inner_ofReal]
  exact inner_re_symm (𝕜 := ℂ) g (ofRealL2 μ f)

theorem bandWordSymbol_single_star (N : ℕ) (i : Fin 2) (ξ : HilbertTwo) :
    star (bandWordSymbol N (fun _ : Fin 1 => i) ξ) =
      -bandWordSymbol N (fun _ : Fin 1 => i) ξ := by
  by_cases hξ : ξ ∈ angularBand N
  · simp only [bandWordSymbol, Set.indicator_of_mem hξ, Fin.prod_univ_one]
    change (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I *
      (inner ℝ ξ (coordinateVector i) : ℂ)) = _
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  · simp only [bandWordSymbol, Set.indicator_of_notMem hξ, star_zero, neg_zero]

end Fourier

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Literal L² derivative classes of the real spectral approximation, with
the exact coordinate weak identities at every finite order. -/

/-- The actual complex Fourier realization of a cutoff coordinate derivative. -/
def bandWordComplex (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) : Lp ℂ 2 (volume : Measure (Vec 2)) :=
  coordinateL2Equiv.symm (𝓕⁻ (L2Multiplier.operator (bandWordSymbol N w)
    (bandWordSymbol_memLp N w) (𝓕 (coordinateL2Equiv f))))

theorem coordinate_bandWordComplex (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (bandWordComplex N w f) =
      𝓕⁻ (L2Multiplier.operator (bandWordSymbol N w) (bandWordSymbol_memLp N w)
        (𝓕 (coordinateL2Equiv f))) := coordinateL2Equiv.apply_symm_apply _

theorem bandWordComplex_distribution_derivative (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (i : Fin 2) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (bandWordComplex N w f) : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv (bandWordComplex N (Fin.snoc w i) f) : Lp ℂ 2 volume) :
        𝓢'(HilbertTwo, ℂ)) := by
  simp only [coordinate_bandWordComplex]
  exact lineDerivOp_fourierInv_bandWord N w i _

/-- The actual real derivative class, obtained by taking the real part of the Fourier formula. -/
def bandWordReal (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) : Lp ℝ 2 (volume : Measure (Vec 2)) :=
  reL2 volume (bandWordComplex N w (ofRealL2 volume f))

theorem bandWordReal_ae (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N w f =ᵐ[volume] fun x => (bandWordComplex N w (ofRealL2 volume f) x).re :=
  reL2_ae volume _

theorem bandWordReal_hasWeakPartialDeriv (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (i : Fin 2) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    HasWeakPartialDerivOn Set.univ i (bandWordReal N w f) (bandWordReal N (Fin.snoc w i) f) := by
  have h := hasWeakPartialDerivOn_re_of_distribution
    (bandWordComplex N w (ofRealL2 volume f)) (bandWordComplex N (Fin.snoc w i) (ofRealL2 volume f))
    i (bandWordComplex_distribution_derivative N w i _)
  apply AVRegularity.Sobolev.hasWeakPartialDerivOn_congr_ae _ _ h
  · simpa only [Measure.restrict_univ] using (bandWordReal_ae N w f).symm
  · simpa only [Measure.restrict_univ] using (bandWordReal_ae N (Fin.snoc w i) f).symm

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The zeroth component of the derivative formula is exactly the source real Fourier
projection characterized above. -/

theorem coordinate_frequency_indicator (N : ℕ) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (L2Indicator.operator (𝕜 := ℂ) (frequencyBall N)
      (frequencyBall_measurableSet N) f) =
      L2Indicator.operator (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N)
        (coordinateL2Equiv f) := by
  apply Lp.ext
  have hp := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae
    (L2Indicator.operator_ae (𝕜 := ℂ) (frequencyBall N) (frequencyBall_measurableSet N) f)
  filter_upwards [coordinateL2Equiv_ae (L2Indicator.operator (𝕜 := ℂ) (frequencyBall N)
    (frequencyBall_measurableSet N) f), coordinateL2Equiv_ae f,
    L2Indicator.operator_ae (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N)
      (coordinateL2Equiv f), hp] with ξ hx hy hz hp
  rw [hx, hp, hz]
  have hm : WithLp.ofLp ξ ∈ frequencyBall N ↔ ξ ∈ angularBand N := Iff.rfl
  by_cases hξ : ξ ∈ angularBand N
  · rw [Set.indicator_of_mem (hm.mpr hξ), Set.indicator_of_mem hξ, hy]
  · rw [Set.indicator_of_notMem (fun h => hξ (hm.mp h)), Set.indicator_of_notMem hξ]

theorem coordinate_frequency_projection (N : ℕ) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (spectralProjection (frequencyBall N) (frequencyBall_measurableSet N) f) =
      𝓕⁻ (L2Indicator.operator (𝕜 := ℂ) (angularBand N) (angularBand_measurableSet N)
        (𝓕 (coordinateL2Equiv f))) := by
  apply (Lp.fourierTransformₗᵢ HilbertTwo ℂ).injective
  change 𝓕 (coordinateL2Equiv (spectralProjection _ _ f)) =
    (Lp.fourierTransformₗᵢ HilbertTwo ℂ) ((Lp.fourierTransformₗᵢ HilbertTwo ℂ).symm _)
  rw [LinearIsometryEquiv.apply_symm_apply, ← coordinate_fourierL2,
    fourier_spectralProjection, coordinate_frequency_indicator, coordinate_fourierL2]

theorem bandWordComplex_zero (N : ℕ) (w : Fin 0 → Fin 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    bandWordComplex N w f = spectralProjection (frequencyBall N) (frequencyBall_measurableSet N) f := by
  apply coordinateL2Equiv.injective
  rw [coordinate_bandWordComplex, bandWord_operator_zero, coordinate_frequency_projection]

theorem bandWordReal_zero (N : ℕ) (w : Fin 0 → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordReal N w f = realSpectralProjection (frequencyBall N)
      (frequencyBall_measurableSet N) (frequencyBall_neg N) f := by
  rw [bandWordReal, bandWordComplex_zero]
  rfl

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Bounded linear realizations of the literal cutoff derivatives. These
operators are used before forming the projected coupled PDE; they assume no
solution or energy identity. -/

/-- The literal complex Fourier multiplier, as a bounded linear map. -/
def bandWordComplexOperator (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec 2)) :=
  coordinateL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Lp.fourierTransformₗᵢ HilbertTwo ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((L2Multiplier.operator (bandWordSymbol N w) (bandWordSymbol_memLp N w)).comp
        ((Lp.fourierTransformₗᵢ HilbertTwo ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
          coordinateL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap)))

/-- The same actual derivative on real scalar fields. -/
def bandWordRealOperator (N : ℕ) {m : ℕ} (w : Fin m → Fin 2) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  (reL2 volume).comp (((bandWordComplexOperator N w).restrictScalars ℝ).comp (ofRealL2 volume))

/-- Real restriction preserves the exact earlier source derivative class. -/
theorem bandWordRealOperator_apply (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandWordRealOperator N w f = bandWordReal N w f := rfl

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The literal full-plane carrier bridge commutes with every fixed fiber map. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [MeasurableSpace F]

theorem planeToUniv_fiberMap (L : E →L[ℝ] F)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeToUniv (L.compLpL 2 volume u) =
      L.compLpL 2 (volume.restrict Set.univ) (planeToUniv u) := by
  apply Lp.ext
  have hL := ContinuousLinearMap.coeFn_compLpL L u
  have hR := ContinuousLinearMap.coeFn_compLpL L (planeToUniv u)
  simp only [Measure.restrict_univ] at hR ⊢
  filter_upwards [planeToUniv_ae (L.compLpL 2 volume u), hL, hR,
    planeToUniv_ae u] with x hl hm hr hu
  rw [hl, hm, hr, hu]

theorem univToPlane_fiberMap (L : E →L[ℝ] F)
    (u : ComponentL2 (volume.restrict Set.univ) E) :
    univToPlane (L.compLpL 2 (volume.restrict Set.univ) u) =
      L.compLpL 2 volume (univToPlane u) := by
  apply Lp.ext
  have hL := ContinuousLinearMap.coeFn_compLpL L u
  simp only [Measure.restrict_univ] at hL
  filter_upwards [univToPlane_ae (L.compLpL 2 (volume.restrict Set.univ) u), hL,
    ContinuousLinearMap.coeFn_compLpL L (univToPlane u), univToPlane_ae u] with x hl hm hr hu
  rw [hl, hm, hr, hu]


omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] in
theorem planeToUniv_inner (u v : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeToUniv u) (planeToUniv v) = inner ℝ u v := by
  simp only [L2.inner_def, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [planeToUniv_ae u, planeToUniv_ae v] with x hu hv
  rw [hu, hv]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual integration by parts for the bounded spectral derivative.
The real pairing is derived from the imaginary Fourier symbol. -/

theorem fourier_coordinate_bandWordComplex (N : ℕ) {m : ℕ} (w : Fin m → Fin 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    (Lp.fourierTransformₗᵢ HilbertTwo ℂ) (coordinateL2Equiv (bandWordComplex N w f)) =
      L2Multiplier.operator (bandWordSymbol N w) (bandWordSymbol_memLp N w)
        ((Lp.fourierTransformₗᵢ HilbertTwo ℂ) (coordinateL2Equiv f)) := by
  rw [coordinate_bandWordComplex]
  exact (Lp.fourierTransformₗᵢ HilbertTwo ℂ).apply_symm_apply _

theorem bandWordComplex_single_inner (N : ℕ) (i : Fin 2)
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) :
    inner ℂ (bandWordComplex N (fun _ : Fin 1 => i) f) g =
      -inner ℂ f (bandWordComplex N (fun _ : Fin 1 => i) g) := by
  rw [← coordinateL2Equiv.inner_map_map, ← coordinateL2Equiv.inner_map_map f]
  rw [← (Lp.fourierTransformₗᵢ HilbertTwo ℂ).inner_map_map,
    ← (Lp.fourierTransformₗᵢ HilbertTwo ℂ).inner_map_map (coordinateL2Equiv f)]
  rw [fourier_coordinate_bandWordComplex, fourier_coordinate_bandWordComplex]
  exact L2Multiplier.operator_inner_neg_of_star_eq_neg _ _
    (Filter.Eventually.of_forall (bandWordSymbol_single_star N i)) _ _

theorem bandWordReal_single_inner (N : ℕ) (i : Fin 2)
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandWordReal N (fun _ : Fin 1 => i) f) g =
      -inner ℝ f (bandWordReal N (fun _ : Fin 1 => i) g) := by
  change inner ℝ (reL2 volume (bandWordComplex N (fun _ : Fin 1 => i)
    (ofRealL2 volume f))) g =
      -inner ℝ f (reL2 volume (bandWordComplex N (fun _ : Fin 1 => i) (ofRealL2 volume g)))
  rw [reL2_inner_eq_re_inner_ofReal, real_inner_reL2_eq_re_inner_ofReal,
    bandWordComplex_single_inner, Complex.neg_re]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Every finite derivative of the actual real Fourier cutoff belongs to the
accepted closed weak Sobolev graph, with its exact coordinate frequency bound. -/

/-- Literal ordered derivative classes of the source Fourier cutoff. -/
def bandProjectionJet (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K ℝ :=
  WithLp.toLp 2 (fun a => planeToUniv (bandWordReal N a.2 f))

theorem bandProjectionJet_component_ae (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (a : JetIndex 2 K) :
    bandProjectionJet N K f a =ᵐ[volume] bandWordReal N a.2 f := planeToUniv_ae _

theorem bandProjectionJet_mem_graph (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    bandProjectionJet N K f ∈ planeHkGraph (E := ℝ) Set.univ K := by
  rw [mem_planeHkGraph_iff]
  intro j w i e
  have hw : HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (bandWordReal N w f x))
      (fun x => inner ℝ e (bandWordReal N (Fin.snoc w i) f x)) := by
    intro φ hs hc hsub
    have h := bandWordReal_hasWeakPartialDeriv N w i f φ hs hc hsub
    simp only [Real.inner_apply, mul_assoc, integral_const_mul]
    rw [h, mul_neg]
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · simpa only [Measure.restrict_univ, Function.comp_def, lowerIndex2, lowerIndex, planeJetRepresentative] using
      (bandProjectionJet_component_ae N K f (lowerIndex2 j w)).symm.fun_comp (inner ℝ e)
  · simpa only [Measure.restrict_univ, Function.comp_def, nextIndex2, nextIndex, planeJetRepresentative] using
      (bandProjectionJet_component_ae N K f (nextIndex2 j w i)).symm.fun_comp (inner ℝ e)

/-- The actual spectral projection, promoted only after all weak derivatives are proved. -/
def bandProjectionHk (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    PlaneHk (Set.univ : Set (Vec 2)) K ℝ :=
  ⟨bandProjectionJet N K f, bandProjectionJet_mem_graph N K f⟩

/-- Every derivative in the promoted graph is its literal Fourier derivative class. -/
theorem bandProjectionHk_component (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (a : JetIndex 2 K) :
    (bandProjectionHk N K f).val a = planeToUniv (bandWordReal N a.2 f) := rfl

/-- The value of the promoted graph is exactly the already defined real spectral projection. -/
theorem bandProjectionHk_value (N K : ℕ) (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    (bandProjectionHk N K f).val (valueIndex2 K) =
      planeToUniv (realSpectralProjection (frequencyBall N)
        (frequencyBall_measurableSet N) (frequencyBall_neg N) f) := by
  rw [bandProjectionHk_component]
  change planeToUniv (bandWordReal N (Fin.elim0 : Fin 0 → Fin 2) f) = _
  rw [bandWordReal_zero]

end AVRegularity.CoupledEnergyPlane.Fourier
end
