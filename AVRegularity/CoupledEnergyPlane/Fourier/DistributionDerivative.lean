-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public noncomputable section

section
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Auxiliary Hilbert coordinates for Fourier analysis; physical variables remain Vec 2. -/

abbrev HilbertTwo := PiLp 2 (fun _ : Fin 2 => ℝ)

def coordinateHilbertEquiv : HilbertTwo ≃L[ℝ] Homogenization.Vec 2 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)

def coordinateVector (k : Fin 2) : HilbertTwo := WithLp.toLp 2 (Pi.single k 1)

theorem coordinateVector_norm (k : Fin 2) : ‖coordinateVector k‖ = 1 := by
  change ‖PiLp.single (β := fun _ : Fin 2 => ℝ) 2 k (1 : ℝ)‖ = 1
  rw [PiLp.norm_single, norm_one]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.L2Indicator

/-! Literal measurable frequency cutoffs on L² and their orthogonality. -/

variable {X 𝕜 E : Type*} [MeasurableSpace X] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {μ : Measure X}

/-- Multiplication by the indicator of a measurable set, on actual L² classes. -/
def value (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) : Lp E 2 μ :=
  (MemLp.indicator hs (Lp.memLp f)).toLp (s.indicator f)

theorem value_ae (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    value s hs f =ᵐ[μ] s.indicator f := (MemLp.indicator hs (Lp.memLp f)).coeFn_toLp

theorem value_norm_le (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖value s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [value_ae s hs f] with x hx
  rw [hx]
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, norm_zero]
    exact norm_nonneg _

/-- The literal indicator as a contractive bounded linear operator. -/
def operator (s : Set X) (hs : MeasurableSet s) : Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := value s hs
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [value_ae s hs (f + g), value_ae s hs f, value_ae s hs g,
          Lp.coeFn_add f g, Lp.coeFn_add (value s hs f) (value s hs g)] with x hfg hf hg ha hb
        rw [hfg, hb]
        change s.indicator (⇑(f + g)) x = value s hs f x + value s hs g x
        rw [hf, hg]
        by_cases h : x ∈ s
        · simp only [indicator_of_mem h]
          exact ha
        · simp only [indicator_of_notMem h, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [value_ae s hs (c • f), value_ae s hs f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (value s hs f)] with x hcf hf ha hb
        change value s hs (c • f) x = (c • value s hs f) x
        rw [hcf, hb]
        change s.indicator (⇑(c • f)) x = c • value s hs f x
        rw [hf]
        by_cases h : x ∈ s
        · simp only [indicator_of_mem h]
          exact ha
        · simp only [indicator_of_notMem h, smul_zero] }
    1 (fun f => by
      change ‖value s hs f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact value_norm_le s hs f)

theorem operator_ae (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    operator (𝕜 := 𝕜) s hs f =ᵐ[μ] s.indicator f := value_ae s hs f

theorem operator_norm_le (s : Set X) (hs : MeasurableSet s) :
    ‖operator (𝕜 := 𝕜) (E := E) (μ := μ) s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖value s hs f‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact value_norm_le s hs f

theorem operator_idempotent (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    operator (𝕜 := 𝕜) s hs (operator (𝕜 := 𝕜) s hs f) = operator (𝕜 := 𝕜) s hs f := by
  apply Lp.ext
  filter_upwards [operator_ae (𝕜 := 𝕜) s hs (operator (𝕜 := 𝕜) s hs f),
    operator_ae (𝕜 := 𝕜) s hs f]
    with x hx hy
  rw [hx]
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, hy, indicator_of_notMem h]

theorem operator_inner (s : Set X) (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    inner 𝕜 (operator (𝕜 := 𝕜) s hs f) g = inner 𝕜 f (operator (𝕜 := 𝕜) s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae (𝕜 := 𝕜) s hs f, operator_ae (𝕜 := 𝕜) s hs g] with x hx hy
  rw [hx, hy]
  by_cases h : x ∈ s
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h, inner_zero_left, inner_zero_right]

include 𝕜 in
/-- The L² square norm is the actual integral of the pointwise square norm. -/
theorem norm_sq_eq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner 𝕜, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

theorem operator_sub_norm_sq (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖operator (𝕜 := 𝕜) s hs f - f‖ ^ 2 =
      ∫ x, ‖s.indicator f x - f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral (𝕜 := 𝕜)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (operator (𝕜 := 𝕜) s hs f) f,
    operator_ae (𝕜 := 𝕜) s hs f] with x hx hy
  rw [hx]
  change ‖operator (𝕜 := 𝕜) s hs f x - f x‖ ^ 2 = _
  rw [hy]

/-- Exhausting measurable frequency regions converge strongly to the identity. -/
theorem tendsto_operator_of_eventually_mem (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ∀ x, ∀ᶠ n in atTop, x ∈ s n) (f : Lp E 2 μ) :
    Tendsto (fun n => operator (𝕜 := 𝕜) (s n) (hs n) f) atTop (𝓝 f) := by
  let err := fun n x => ‖(s n).indicator f x - f x‖ ^ 2
  have hmeas : ∀ n, AEStronglyMeasurable (err n) μ := fun n =>
    (((Lp.aestronglyMeasurable f).indicator (hs n)).sub (Lp.aestronglyMeasurable f)).norm.pow 2
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖err n x‖ ≤ ‖f x‖ ^ 2 := by
    intro n
    apply Eventually.of_forall
    intro x
    dsimp [err]
    rw [abs_of_nonneg (sq_nonneg _)]
    by_cases h : x ∈ s n
    · simp only [indicator_of_mem h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · simp only [indicator_of_notMem h, zero_sub, norm_neg, le_refl]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => err n x) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [hcover x] with n hn
    simp only [err, indicator_of_mem hn, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hint := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ ^ 2)
    hmeas ((Lp.memLp f).norm.integrable_sq) hbound hlim
  have hsq : Tendsto (fun n => ‖operator (𝕜 := 𝕜) (s n) (hs n) f - f‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [operator_sub_norm_sq, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto (fun n => Real.sqrt (‖operator (𝕜 := 𝕜) (s n) (hs n) f - f‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

end AVRegularity.CoupledEnergyPlane.L2Indicator
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! L² Fourier analysis in the existing spatial `Vec 2` coordinates.
The auxiliary Hilbert coordinate carrier is related by a proved measure
preserving identity on coordinate values. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Identity on coordinate values gives an actual L² linear isometric equivalence. -/
def coordinateL2Equiv :
    Lp F 2 (volume : Measure (Vec 2)) ≃ₗᵢ[ℂ] Lp F 2 (volume : Measure HilbertTwo) :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ _ (PiLp.volume_preserving_ofLp (Fin 2)))
    (Lp.compMeasurePreservingₗᵢ ℂ _ (PiLp.volume_preserving_toLp (Fin 2))).toLinearMap
    (by
      apply LinearMap.ext
      intro f
      change Lp.compMeasurePreserving _ (PiLp.volume_preserving_ofLp (Fin 2))
        (Lp.compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 2)) f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      exact Lp.compMeasurePreserving_id_apply f)
    (by
      apply LinearMap.ext
      intro f
      change Lp.compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 2))
        (Lp.compMeasurePreserving _ (PiLp.volume_preserving_ofLp (Fin 2)) f) = f
      rw [← Lp.compMeasurePreserving_comp_apply]
      exact Lp.compMeasurePreserving_id_apply f)

theorem coordinateL2Equiv_ae (f : Lp F 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv f =ᵐ[volume] fun x : HilbertTwo => f (WithLp.ofLp x) :=
  Lp.coeFn_compMeasurePreserving f (PiLp.volume_preserving_ofLp (Fin 2))

variable [CompleteSpace F]

/-- The existing L² Fourier unitary, transported to the actual `Vec 2` coordinates. -/
def fourierL2 : Lp F 2 (volume : Measure (Vec 2)) ≃ₗᵢ[ℂ]
    Lp F 2 (volume : Measure (Vec 2)) :=
  coordinateL2Equiv.trans
    ((Lp.fourierTransformₗᵢ HilbertTwo F).trans coordinateL2Equiv.symm)

/-- Full source characterization through the measure-preserving coordinate map. -/
theorem coordinate_fourierL2 (f : Lp F 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (fourierL2 f) = 𝓕 (coordinateL2Equiv f) := by
  exact coordinateL2Equiv.apply_symm_apply _

theorem fourierL2_norm (f : Lp F 2 (volume : Measure (Vec 2))) : ‖fourierL2 f‖ = ‖f‖ :=
  fourierL2.norm_map f

theorem fourierL2_inner (f g : Lp F 2 (volume : Measure (Vec 2))) :
    inner ℂ (fourierL2 f) (fourierL2 g) = inner ℂ f g := fourierL2.inner_map_map f g

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory SchwartzMap
open scoped FourierTransform Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual conjugation of scalar L² functions and compatibility with Fourier
transformation. These identities are used to retain real solutions under the
symmetric spectral truncations in the coupled energy proof. -/

section L2
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Pointwise complex conjugation on actual L² classes. -/
def conjugateL2 : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ

theorem conjugateL2_ae (f : Lp ℂ 2 μ) :
    conjugateL2 μ f =ᵐ[μ] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

end L2

section Schwartz
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem conjugateL2_toLp (f : 𝓢(V, ℂ)) :
    conjugateL2 volume (f.toLp 2) =
      (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f).toLp 2 := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae volume (f.toLp 2), f.coeFn_toLp 2,
    (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f).coeFn_toLp 2]
    with x hx hy hz
  rw [hx, hy, hz]
  rfl

theorem fourier_function_conjugate (f : V → ℂ) (ξ : V) :
    𝓕 (fun x => star (f x)) ξ = star (𝓕⁻ f ξ) := by
  change 𝓕 (fun x => (starRingEnd ℂ) (f x)) ξ = (starRingEnd ℂ) (𝓕⁻ f ξ)
  rw [Real.fourier_eq, Real.fourierInv_eq, ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [Circle.smul_def, smul_eq_mul, map_mul,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

theorem fourier_schwartz_conjugate (f : 𝓢(V, ℂ)) :
    𝓕 (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f) =
      SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap (𝓕⁻ f) := by
  apply SchwartzMap.ext
  intro ξ
  change 𝓕 (fun x => star (f x)) ξ = star ((𝓕⁻ f) ξ)
  rw [SchwartzMap.fourierInv_coe]
  exact fourier_function_conjugate f ξ

theorem fourier_conjugateL2 (f : Lp ℂ 2 (volume : Measure V)) :
    𝓕 (conjugateL2 volume f) = conjugateL2 volume (𝓕⁻ f) := by
  let p := fun f : Lp ℂ 2 (volume : Measure V) =>
    𝓕 (conjugateL2 volume f) = conjugateL2 volume (𝓕⁻ f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ V ℂ).continuous.comp (conjugateL2 volume).continuous
    · exact (conjugateL2 volume).continuous.comp (Lp.fourierTransformₗᵢ V ℂ).symm.continuous
  · intro g
    change 𝓕 (conjugateL2 volume (g.toLp 2)) = conjugateL2 volume (𝓕⁻ (g.toLp 2))
    rw [conjugateL2_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq,
      conjugateL2_toLp, fourier_schwartz_conjugate]

end Schwartz

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Actual distributional differentiation of inverse L² Fourier transforms.
The frequency product is an ae identity, and compact-test weak identities
are derived from Mathlib's proved distributional Fourier calculus. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem toTemperedDistribution_frequency_product (f g : Lp ℂ 2 (volume : Measure V))
    (v : V) (hfg : g =ᵐ[volume] fun x =>
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x v : ℂ) * f x) :
    (g : 𝓢'(V, ℂ)) = (2 * (Real.pi : ℂ) * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ (fun x => (inner ℝ x v : ℂ)) (f : 𝓢'(V, ℂ)) := by
  have hgrowth : (fun x : V => (inner ℝ x v : ℂ)).HasTemperateGrowth := by fun_prop
  ext ψ
  change (g : 𝓢'(V, ℂ)) ψ = (2 * (Real.pi : ℂ) * Complex.I) •
    ((TemperedDistribution.smulLeftCLM ℂ (fun x => (inner ℝ x v : ℂ))
      (f : 𝓢'(V, ℂ))) ψ)
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply hgrowth, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]
  ring

theorem lineDerivOp_fourierInv_L2 (f g : Lp ℂ 2 (volume : Measure V)) (v : V)
    (hfg : g =ᵐ[volume] fun x =>
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x v : ℂ) * f x) :
    ∂_{v} ((𝓕⁻ f : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) =
      ((𝓕⁻ g : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) := by
  rw [← Lp.fourierInv_toTemperedDistribution_eq,
    TemperedDistribution.lineDerivOp_fourierInv_eq,
    ← toTemperedDistribution_frequency_product f g v hfg,
    Lp.fourierInv_toTemperedDistribution_eq]

theorem compact_test_identity_of_lineDerivOp (f g : Lp ℂ 2 (volume : Measure V))
    (v : V) (hfg : ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)))
    (ψ : V → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ x, fderiv ℝ ψ x v * f x) = -(∫ x, ψ x * g x) := by
  have h := congrArg (fun T : 𝓢'(V, ℂ) => T (hc.toSchwartzMap hs)) hfg
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul] at h
  change (∫ x, -(fderiv ℝ ψ x v) * f x) = ∫ x, ψ x * g x at h
  simp only [neg_mul, integral_neg] at h
  exact neg_eq_iff_eq_neg.mp h

end AVRegularity.CoupledEnergyPlane.Fourier
end
