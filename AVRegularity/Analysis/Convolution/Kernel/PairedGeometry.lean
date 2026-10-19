-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.FourierTransform
public import Homogenization.Ambient.HilbertFinite

section
public noncomputable section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.Analysis.Convolution

/-! Concrete approximation ingredients for the weak-to-Fourier derivative bridge. -/

theorem exists_normalized_smooth_kernel :
    ∃ κ : Vec 2 → ℝ, HasCompactSupport κ ∧ ContDiff ℝ (⊤ : ℕ∞) κ ∧
      Integrable κ (volume : Measure (Vec 2)) ∧ (∫ z, κ z) = 1 := by
  let φ : ContDiffBump (0 : Vec 2) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨φ.normed volume, φ.hasCompactSupport_normed, φ.contDiff_normed,
    φ.integrable_normed, φ.integral_normed⟩

theorem exists_shrinking_linearEquiv :
    ∃ R : ℕ → Vec 2 ≃L[ℝ] Vec 2,
      ∀ z, Tendsto (fun n => (R n).toLinearEquiv.toAddHom z) atTop (𝓝 0) := by
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hcn (n : ℕ) : c n ≠ 0 := by dsimp [c]; positivity
  let R (n : ℕ) : Vec 2 ≃L[ℝ] Vec 2 :=
    Units.mk0 (c n) (hcn n) • ContinuousLinearEquiv.refl ℝ (Vec 2)
  refine ⟨R, fun z => ?_⟩
  change Tendsto (fun n => c n • z) atTop (𝓝 0)
  simpa only [zero_smul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const z

end AVRegularity.Analysis.Convolution
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! Ordered directional derivatives of smooth compactly supported kernels. -/

/-- The ordered derivative differentiating the last word direction next. -/
def orderedKernelDerivative (κ : Vec 2 → ℝ) : (m : ℕ) → (Fin m → Vec 2) → Vec 2 → ℝ
  | 0, _ => κ
  | m + 1, a => fun z => (fderiv ℝ (orderedKernelDerivative κ m (Fin.init a)) z)
      (a (Fin.last m))

theorem orderedKernelDerivative_snoc (κ : Vec 2 → ℝ) {m : ℕ}
    (a : Fin m → Vec 2) (v : Vec 2) :
    orderedKernelDerivative κ (m + 1) (Fin.snoc a v) =
      fun z => (fderiv ℝ (orderedKernelDerivative κ m a) z) v := by
  simp only [orderedKernelDerivative, Fin.init_snoc, Fin.snoc_last]

theorem contDiff_orderedKernelDerivative {κ : Vec 2 → ℝ}
    (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (m : ℕ) (a : Fin m → Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (orderedKernelDerivative κ m a) := by
  induction m with
  | zero => exact hd
  | succ m ih => exact ((ih (Fin.init a)).fderiv_right (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_orderedKernelDerivative {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (m : ℕ) (a : Fin m → Vec 2) :
    HasCompactSupport (orderedKernelDerivative κ m a) := by
  induction m with
  | zero => exact hc
  | succ m ih => exact (ih (Fin.init a)).fderiv_apply (𝕜 := ℝ) (a (Fin.last m))

theorem integrable_orderedKernelDerivative {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (m : ℕ)
    (a : Fin m → Vec 2) : Integrable (orderedKernelDerivative κ m a) :=
  (contDiff_orderedKernelDerivative hd m a).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_orderedKernelDerivative hc m a)

/-! Compact-test directional weak derivatives on the Euclidean cover. -/

/-- Scalar weak differentiation in a fixed constant direction. -/
def HasWeakDirectionalDeriv (v : Vec 2) (u g : Vec 2 → ℝ) : Prop :=
  ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, u x * (fderiv ℝ φ x) v) = -(∫ x, g x * φ x)

theorem hasWeakDirectionalDeriv_basis_iff (i : Fin 2) (u g : Vec 2 → ℝ) :
    HasWeakDirectionalDeriv (basisVec i) u g ↔ HasWeakPartialDerivOn Set.univ i u g := by
  constructor
  · intro h φ hs hc _
    simpa only [setIntegral_univ] using h φ hs hc
  · intro h φ hs hc
    simpa only [setIntegral_univ] using h φ hs hc (Set.subset_univ _)

theorem hasWeakDirectionalDeriv_congr_ae {v : Vec 2} {u f g h : Vec 2 → ℝ}
    (hu : u =ᵐ[volume] f) (hg : g =ᵐ[volume] h)
    (hw : HasWeakDirectionalDeriv v u g) : HasWeakDirectionalDeriv v f h := by
  intro φ hs hc
  calc
    (∫ x, f x * (fderiv ℝ φ x) v) = ∫ x, u x * (fderiv ℝ φ x) v := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
    _ = -(∫ x, g x * φ x) := hw φ hs hc
    _ = -(∫ x, h x * φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

theorem hasWeakDirectionalDeriv_of_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (v : Vec 2) :
    HasWeakDirectionalDeriv v f (fun x => (fderiv ℝ f x) v) := by
  intro φ hs hc
  have hdφ := (hs.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have hdf := (hf.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hf.continuous.mul hdφ).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) v).mul_left)
    ((hf.continuous.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hs.differentiable (by simp)).differentiableAt)

theorem hasWeakDirectionalDeriv_translate {v : Vec 2} {u g : Vec 2 → ℝ}
    (h : HasWeakDirectionalDeriv v u g) (z : Vec 2) :
    HasWeakDirectionalDeriv v (fun x => u (x-z)) (fun x => g (x-z)) := by
  intro φ hφ hc
  let ψ : Vec 2 → ℝ := fun x => φ (x+z)
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcomp : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addRight z)
  have hw := h ψ hs hcomp
  have hd (x : Vec 2) : fderiv ℝ ψ x = fderiv ℝ φ (x+z) := fderiv_comp_add_right z
  calc
    (∫ x, u (x-z) * (fderiv ℝ φ x) v) =
        ∫ x, u x * (fderiv ℝ φ (x+z)) v := by
      have ht := integral_add_right_eq_self (μ := volume)
        (fun x : Vec 2 => u (x-z) * (fderiv ℝ φ x) v) z
      simpa only [add_sub_cancel_right] using ht.symm
    _ = -(∫ x, g x * ψ x) := by simpa only [hd] using hw
    _ = -(∫ x, g (x-z) * φ x) := by
      congr 1
      have ht := integral_add_right_eq_self (μ := volume)
        (fun x : Vec 2 => g (x-z) * φ x) z
      simpa only [ψ, add_sub_cancel_right] using ht

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open scoped FourierTransform
namespace AVRegularity.Analysis.Convolution

/-! One-frequency characteristic integrals for moment recovery.
Normalization is exp(-2π i t Lz), hence the frequency 2πtL in the convention exp(-iξ·z).
No Fourier-defined averaging operator or Sobolev carrier is introduced. -/

/-- A literal one-frequency characteristic integral. Mathlib uses `exp(2π i t)`,
so this equals the transform with kernel `exp(-iξ·z)` at the covector `ξ = 2π t L`.
It is used only to recover moments, not to redefine the averaging operator. -/
def projectionFourier (q : Vec 2 → ℝ) (L : Vec 2 →L[ℝ] ℝ) : ℝ → ℂ :=
  fun t => ∫ z : Vec 2, (𝐞 (-L z * t) : ℂ) * (q z : ℂ)

/-- The genuine bilinear pairing `(z,t) ↦ L(z)t` for the public Fourier derivative API. -/
def projectionPairing (L : Vec 2 →L[ℝ] ℝ) : Vec 2 →L[ℝ] ℝ →L[ℝ] ℝ :=
  L.smulRight (ContinuousLinearMap.id ℝ ℝ)

theorem projectionPairing_apply (L : Vec 2 →L[ℝ] ℝ) (z : Vec 2) (t : ℝ) :
    projectionPairing L z t = L z * t := rfl

 theorem projectionFourier_eq_vectorFourier (q : Vec 2 → ℝ) (L : Vec 2 →L[ℝ] ℝ) :
    projectionFourier q L = VectorFourier.fourierIntegral 𝐞 volume
      (projectionPairing L).toLinearMap₁₂ (fun z => (q z : ℂ)) := by
  funext t
  unfold projectionFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change (𝐞 (-L z * t) : ℂ) * (q z : ℂ) = 𝐞 (-(projectionPairing L z t)) • (q z : ℂ)
    rw [Circle.smul_def, projectionPairing_apply, neg_mul, smul_eq_mul]

 theorem projectionFourier_zero (q : Vec 2 → ℝ) (L : Vec 2 →L[ℝ] ℝ) :
    projectionFourier q L 0 = (∫ z, q z : ℝ) := by
  unfold projectionFourier
  simp only [mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  exact integral_ofReal

 theorem integrable_norm_pow_mul_norm {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hq : Continuous q) (m : ℕ) :
    Integrable (fun z : Vec 2 => ‖z‖ ^ m * ‖q z‖) :=
  ((continuous_norm.pow m).mul hq.norm).integrable_of_hasCompactSupport hc.norm.mul_left

 theorem projectionFourier_contDiff {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hq : Continuous q) (L : Vec 2 →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (projectionFourier q L) := by
  rw [projectionFourier_eq_vectorFourier]
  apply VectorFourier.contDiff_fourierIntegral
  intro m _
  simpa only [Complex.norm_real] using integrable_norm_pow_mul_norm hc hq m

theorem projectionFourier_iteratedDeriv {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hq : Continuous q) (L : Vec 2 →L[ℝ] ℝ) (m : ℕ) :
    iteratedDeriv m (projectionFourier q L) 0 =
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ m * ((∫ z, (L z) ^ m * q z : ℝ) : ℂ) := by
  have hi : Integrable (fun z : Vec 2 => (q z : ℂ)) :=
    (hq.integrable_of_hasCompactSupport hc).ofReal
  have hw (k : ℕ) : Integrable (fun z : Vec 2 => ‖z‖ ^ k * ‖(q z : ℂ)‖) := by
    simpa only [Complex.norm_real] using integrable_norm_pow_mul_norm hc hq k
  rw [projectionFourier_eq_vectorFourier, iteratedDeriv_eq_iteratedFDeriv,
    VectorFourier.iteratedFDeriv_fourierIntegral (projectionPairing L)
      (N := (⊤ : ℕ∞)) (fun k _ => hw k) hi.aestronglyMeasurable (by simp)]
  rw [VectorFourier.fourierIntegral_continuousMultilinearMap_apply Real.continuous_fourierChar
    (VectorFourier.integrable_fourierPowSMulRight (projectionPairing L) (hw m) hi.aestronglyMeasurable)]
  unfold VectorFourier.fourierIntegral
  change (∫ v : Vec 2, 𝐞 (-(L v * 0)) •
    (VectorFourier.fourierPowSMulRight (projectionPairing L) (fun v => (q v : ℂ)) v m) (fun _ => 1)) = _
  simp only [VectorFourier.fourierPowSMulRight_apply, projectionPairing_apply, mul_one,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.real_smul, smul_eq_mul]
  rw [integral_const_mul]
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    push_cast
    ring

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! Almost-everywhere locality and Euclidean radius bounds for paired averages. -/

section
/-- An invertible affine displacement preserves Lebesgue-null exceptional sets. -/
theorem affineDisplacement_quasiMeasurePreserving (S : Vec 2 ≃L[ℝ] Vec 2)
    (c : Vec 2) :
    Measure.QuasiMeasurePreserving (fun x : Vec 2 => c - S x) volume volume := by
  have hdet : (S.toContinuousLinearMap).det ≠ 0 := by
    exact S.toLinearEquiv.isUnit_det'.ne_zero
  have hS : Measure.QuasiMeasurePreserving (fun x : Vec 2 => S x) volume volume :=
    Measure.ContinuousLinearMap.quasiMeasurePreserving volume
      S.toContinuousLinearMap hdet
  have hneg : Measure.QuasiMeasurePreserving (fun x : Vec 2 => -x) volume volume :=
    (Measure.measurePreserving_neg (volume : Measure (Vec 2))).quasiMeasurePreserving
  have hadd : Measure.QuasiMeasurePreserving (fun x : Vec 2 => c + x) volume volume :=
    (measurePreserving_add_left (volume : Measure (Vec 2)) c).quasiMeasurePreserving
  convert hadd.comp (hneg.comp hS) using 1
  funext x
  simp [sub_eq_add_neg]

section CarrierRepresentation

end CarrierRepresentation
end

/-! The spanning-column inverse gives the coordinate coefficients used in the gain. -/

section
abbrev HilbertTwo := HilbertVec 2

def coordinateHilbertEquiv : HilbertTwo ≃L[ℝ] Vec 2 :=
  HilbertVec.continuousLinearEquivVec 2

def coordinateVector (i : Fin 2) : HilbertTwo := HilbertVec.ofVec (basisVec i)

def spatialHilbertOperator (T : HilbertTwo →L[ℝ] HilbertTwo) : Vec 2 →L[ℝ] Vec 2 :=
  coordinateHilbertEquiv.toContinuousLinearMap.comp
    (T.comp coordinateHilbertEquiv.symm.toContinuousLinearMap)

/-- The value map of `r T`, represented on the project vector carrier. -/
def scaledSpatialEquiv (T : HilbertTwo ≃L[ℝ] HilbertTwo) (r : ℝ) (hr : r ≠ 0) :
    Vec 2 ≃L[ℝ] Vec 2 :=
  (((coordinateHilbertEquiv.symm.trans T).trans coordinateHilbertEquiv).toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Vec 2) r hr)).toContinuousLinearEquiv

@[simp] theorem coordinateVector_apply (i j : Fin 2) : coordinateVector i j = basisVec i j := by
  rfl

theorem coordinateVector_norm (i : Fin 2) : ‖coordinateVector i‖ = 1 := by
  change ‖PiLp.single (β := fun _ : Fin 2 => ℝ) 2 i (1 : ℝ)‖ = 1
  rw [PiLp.norm_single, norm_one]

theorem spatialHilbertOperator_apply (T : HilbertTwo →L[ℝ] HilbertTwo) (x : Vec 2) :
    spatialHilbertOperator T x = coordinateHilbertEquiv (T (coordinateHilbertEquiv.symm x)) := rfl

theorem scaledSpatialEquiv_apply (T : HilbertTwo ≃L[ℝ] HilbertTwo) (r : ℝ) (hr : r ≠ 0)
    (x : Vec 2) : scaledSpatialEquiv T r hr x = r • spatialHilbertOperator T x := rfl

theorem scaledSpatialEquiv_symm_apply (T : HilbertTwo ≃L[ℝ] HilbertTwo) (r : ℝ)
    (hr : r ≠ 0) (x : Vec 2) :
  coordinateHilbertEquiv.symm (scaledSpatialEquiv T r hr x) =
      r • T (coordinateHilbertEquiv.symm x) := by
  apply coordinateHilbertEquiv.injective
  simp [scaledSpatialEquiv, coordinateHilbertEquiv, HilbertVec.continuousLinearEquivVec]

theorem inverse_column_coefficients (H₁ H₂ : HilbertTwo →L[ℝ] HilbertTwo)
    (V : HilbertTwo ≃L[ℝ] HilbertTwo)
    (h₁ : V (coordinateVector 0) = H₁ (coordinateVector 0))
    (h₂ : V (coordinateVector 1) = H₂ (coordinateVector 1)) (i : Fin 2) :
    (V.symm (coordinateVector i)) 0 • H₁ (coordinateVector 0) +
      (V.symm (coordinateVector i)) 1 • H₂ (coordinateVector 1) = coordinateVector i := by
  have hV (x : HilbertTwo) : V x = x 0 • H₁ (coordinateVector 0) +
      x 1 • H₂ (coordinateVector 1) := by
    have hx : x = x 0 • coordinateVector 0 + x 1 • coordinateVector 1 := by
      apply PiLp.ext
      intro j
      fin_cases j <;> simp [coordinateVector, basisVec]
    calc
      V x = V (x 0 • coordinateVector 0 + x 1 • coordinateVector 1) := congrArg V hx
      _ = x 0 • V (coordinateVector 0) + x 1 • V (coordinateVector 1) := by
        simp only [map_add, map_smul]
      _ = x 0 • H₁ (coordinateVector 0) + x 1 • H₂ (coordinateVector 1) := by rw [h₁, h₂]
  calc
    _ = V (V.symm (coordinateVector i)) := (hV _).symm
    _ = coordinateVector i := V.apply_symm_apply _

theorem inverse_column_coefficient_bound (V : HilbertTwo ≃L[ℝ] HilbertTwo)
    (hV : ‖V.symm.toContinuousLinearMap‖ ≤ 2) (i k : Fin 2) :
    |(V.symm (coordinateVector i)) k| ≤ 2 := by
  calc
    |(V.symm (coordinateVector i)) k| ≤ ‖V.symm (coordinateVector i)‖ :=
      HilbertVec.abs_apply_le_norm _ _
    _ ≤ ‖V.symm.toContinuousLinearMap‖ * ‖coordinateVector i‖ :=
      V.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ 2 := by rw [coordinateVector_norm, mul_one]; exact hV

theorem inverse_column_spatial_coefficients (H₁ H₂ : HilbertTwo →L[ℝ] HilbertTwo)
    (V : HilbertTwo ≃L[ℝ] HilbertTwo)
    (h₁ : V (coordinateVector 0) = H₁ (coordinateVector 0))
    (h₂ : V (coordinateVector 1) = H₂ (coordinateVector 1)) (i : Fin 2) :
    (V.symm (coordinateVector i)) 0 • spatialHilbertOperator H₁ (basisVec 0) +
      (V.symm (coordinateVector i)) 1 • spatialHilbertOperator H₂ (basisVec 1) = basisVec i := by
  have h := congrArg coordinateHilbertEquiv (inverse_column_coefficients H₁ H₂ V h₁ h₂ i)
  have hb (j : Fin 2) : coordinateHilbertEquiv.symm (basisVec j) = coordinateVector j := by
    rfl
  rw [spatialHilbertOperator_apply, spatialHilbertOperator_apply, hb, hb]
  have hbi : coordinateHilbertEquiv (coordinateVector i) = basisVec i := rfl
  rw [← hbi]
  simpa only [map_add, map_smul] using h

def inverseColumnCoeff (V : HilbertTwo ≃L[ℝ] HilbertTwo) (r : ℝ) (i : Fin 2) : ℝ :=
  (V.symm (coordinateVector i)) 0 / r

def inverseRowCoeff (V : HilbertTwo ≃L[ℝ] HilbertTwo) (r : ℝ) (i : Fin 2) : ℝ :=
  (V.symm (coordinateVector i)) 1 / r

theorem inverse_column_scaled_spatial_coefficients
    (H₁ H₂ : HilbertTwo ≃L[ℝ] HilbertTwo) (V : HilbertTwo ≃L[ℝ] HilbertTwo)
    (h₁ : V (coordinateVector 0) = H₁ (coordinateVector 0))
    (h₂ : V (coordinateVector 1) = H₂ (coordinateVector 1)) {r : ℝ} (hr : 0 < r)
    (i : Fin 2) :
    inverseColumnCoeff V r i • scaledSpatialEquiv H₁ r hr.ne' (basisVec 0) +
      inverseRowCoeff V r i • scaledSpatialEquiv H₂ r hr.ne' (basisVec 1) = basisVec i := by
  have h := inverse_column_spatial_coefficients H₁.toContinuousLinearMap
    H₂.toContinuousLinearMap V h₁ h₂ i
  apply coordinateHilbertEquiv.symm.injective
  rw [map_add, map_smul, map_smul, scaledSpatialEquiv_symm_apply,
    scaledSpatialEquiv_symm_apply]
  have hb : coordinateHilbertEquiv.symm (basisVec i) = coordinateVector i := by rfl
  rw [hb]
  unfold inverseColumnCoeff inverseRowCoeff
  rw [smul_smul, smul_smul, div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne']
  exact inverse_column_coefficients H₁.toContinuousLinearMap H₂.toContinuousLinearMap V h₁ h₂ i

theorem inverse_column_scaled_coefficients_bound
    (V : HilbertTwo ≃L[ℝ] HilbertTwo) (hV : ‖V.symm.toContinuousLinearMap‖ ≤ 2)
    {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    |inverseColumnCoeff V r i| ≤ 2/r ∧ |inverseRowCoeff V r i| ≤ 2/r := by
  constructor
  · unfold inverseColumnCoeff
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (inverse_column_coefficient_bound V hV i 0) (le_of_lt hr)
  · unfold inverseRowCoeff
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (inverse_column_coefficient_bound V hV i 1) (le_of_lt hr)

section ForData

end ForData
end

end AVRegularity.Analysis.Convolution
end
end
end
