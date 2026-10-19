-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs.Assembly

/-! The mean projection and its bounds on periodic factorial Sobolev norms. -/

theorem meanProjection_cell_volume : volume AVenhance.unitCube = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance meanProjectionCellFinite : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp [meanProjection_cell_volume]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem torus_value_integrable {K : ℕ} (f : TorusHk K E) :
    Integrable (f.toFunction.jet (valueIndex2 K)) (volume.restrict AVenhance.unitCube) :=
  (f.toFunction.hasPeriodicWeakJet.2.1 _).integrable (by norm_num)

/-- The cell mean is a linear map on every carrier order. -/
def torusMeanLinearMap (K : ℕ) : TorusHk K E →ₗ[ℝ] E where
  toFun := torusMean
  map_add' f g := by
    unfold torusMean
    rw [← integral_add (torus_value_integrable f) (torus_value_integrable g)]
    exact integral_congr_ae ((periodicJetRepresentative_add_global f.val g.val
      (valueIndex2 K)).restrict)
  map_smul' c f := by
    unfold torusMean
    rw [← integral_smul]
    exact integral_congr_ae ((periodicJetRepresentative_smul_global c f.val
      (valueIndex2 K)).restrict)

/-- Constant carriers, as a linear map from their value space. -/
def torusConstantLinearMap (K : ℕ) : E →ₗ[ℝ] TorusHk K E where
  toFun := torusConstantCarrier K
  map_add' c d := by
    apply TorusHk.ext_value
    apply Lp.ext
    filter_upwards [torusConstantCarrier_jet_ae K (c + d) (valueIndex2 K),
      torusConstantCarrier_jet_ae K c (valueIndex2 K),
      torusConstantCarrier_jet_ae K d (valueIndex2 K),
      Lp.coeFn_add ((torusConstantCarrier K c).val (valueIndex2 K))
        ((torusConstantCarrier K d).val (valueIndex2 K))] with x hcd hc hd ha
    change _ = (((torusConstantCarrier K c).val (valueIndex2 K) +
      (torusConstantCarrier K d).val (valueIndex2 K)) : ComponentL2 _ E) x
    simp only [ha, Pi.add_apply, hcd, hc, hd, torusConstantRawJet_value]
  map_smul' c d := by
    apply TorusHk.ext_value
    apply Lp.ext
    filter_upwards [torusConstantCarrier_jet_ae K (c • d) (valueIndex2 K),
      torusConstantCarrier_jet_ae K d (valueIndex2 K),
      Lp.coeFn_smul c ((torusConstantCarrier K d).val (valueIndex2 K))] with x hcd hd ha
    change _ = ((c • (torusConstantCarrier K d).val (valueIndex2 K)) : ComponentL2 _ E) x
    simp only [ha, Pi.smul_apply, hcd, hd, torusConstantRawJet_value]

/-- Projection to the constant mode, allowing different input and output orders. -/
def meanProjection (K L : ℕ) : TorusHk K E →ₗ[ℝ] TorusHk L E :=
  (torusConstantLinearMap L).comp (torusMeanLinearMap K)

/-- Remove the constant mode. -/
def meanComplement (K : ℕ) : TorusHk K E →ₗ[ℝ] TorusHk K E :=
  LinearMap.id - meanProjection K K

@[simp] theorem meanProjection_apply (K L : ℕ) (f : TorusHk K E) :
    meanProjection K L f = torusConstantCarrier L (torusMean f) := rfl

@[simp] theorem meanComplement_apply (K : ℕ) (f : TorusHk K E) :
    meanComplement K f = f - torusConstantCarrier K (torusMean f) := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem torusMean_constant (K : ℕ) (c : E) :
    torusMean (torusConstantCarrier K c) = c := by
  unfold torusMean
  rw [integral_congr_ae (torusConstantCarrier_raw_value_ae K c)]
  simp [Measure.real, meanProjection_cell_volume]

omit [FiniteDimensional ℝ E] in
@[simp] theorem torusMean_truncate {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) :
    torusMean (truncateTorusHk hKL f) = torusMean f := rfl

@[simp] theorem meanComplement_constant (K : ℕ) (c : E) :
    meanComplement K (torusConstantCarrier K c) = 0 := by
  simp only [meanComplement_apply, torusMean_constant, sub_self]

@[simp] theorem torusMean_complement (K : ℕ) (f : TorusHk K E) :
    torusMean (meanComplement K f) = 0 := by
  change torusMeanLinearMap K (f - torusConstantCarrier K (torusMean f)) = 0
  rw [map_sub]
  simp only [torusMeanLinearMap, LinearMap.coe_mk, AddHom.coe_mk, torusMean_constant, sub_self]

theorem truncate_meanComplement {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) :
    truncateTorusHk hKL (meanComplement L f) = meanComplement K (truncateTorusHk hKL f) := by
  simp only [meanComplement_apply, map_sub, torusMean_truncate, torusConstantCarrier_truncate]

omit [FiniteDimensional ℝ E] in
/-- The factorial square of a constant has only its order-zero summand. -/
theorem constant_factorialNormSq (K : ℕ) (ρ : ℝ) (c : E) :
    factorialNormSq ρ (torusConstantCarrier K c).val = ‖c‖ ^ 2 := by
  have hz : ∀ a : JetIndex2 K, 0 < a.1.val → (torusConstantCarrier K c).val a = 0 :=
    fun a ha => torusConstantCarrier_positive_jet_zero K c a ha
  have hv : ‖(torusConstantCarrier K c).val (valueIndex2 K)‖ ^ 2 = ‖c‖ ^ 2 := by
    calc
      _ = ∫ x in AVenhance.unitCube, ‖((torusConstantCarrier K c).val (valueIndex2 K)) x‖ ^ 2 := by
        simpa only [Lp.toLp_coeFn] using
          normSq_toLp_eq_integral (Lp.memLp ((torusConstantCarrier K c).val (valueIndex2 K)))
      _ = ∫ x in AVenhance.unitCube, ‖c‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [torusConstantCarrier_jet_ae K c (valueIndex2 K)] with x hx
        rw [hx, torusConstantRawJet_value]
      _ = _ := by simp [Measure.real, meanProjection_cell_volume]
  unfold factorialNormSq
  rw [Finset.sum_eq_single (0 : Fin (K + 1))]
  · simpa only [Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul,
      derivativeNormSq_zero_eq_value] using hv
  · intro j _ hj
    have hjp : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    have hjets : ∀ w, (torusConstantCarrier K c).val ⟨j, w⟩ = 0 := fun w => hz ⟨j, w⟩ hjp
    simp only [derivativeNormSq, hjets, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero]
  · exact fun hn => (hn (Finset.mem_univ _)).elim

@[simp] theorem torusHkNorm_constant {K L : ℕ} (ρ : ℝ) (hKL : K ≤ L) (c : E) :
    torusHkNorm ρ hKL (torusConstantCarrier L c) = ‖c‖ := by
  unfold torusHkNorm
  rw [torusConstantCarrier_truncate, constant_factorialNormSq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

@[simp] theorem torusConstant_zero_norm (c : E) : ‖torusConstantCarrier 0 c‖ = ‖c‖ := by
  rw [← torusHkNorm_zero_input 1, torusHkNorm_constant]

omit [FiniteDimensional ℝ E] in
/-- At order zero pairing with a constant is pairing with the cell mean. -/
theorem inner_constant_zero (c : E) (f : TorusHk 0 E) :
    inner ℝ (torusConstantCarrier 0 c) f = inner ℝ c (torusMean f) := by
  change inner ℝ (torusConstantCarrier 0 c).val f.val = _
  rw [PiLp.inner_apply]
  have he : (∑ a : JetIndex2 0, inner ℝ ((torusConstantCarrier 0 c).val a) (f.val a)) =
      inner ℝ ((torusConstantCarrier 0 c).val (valueIndex2 0)) (f.val (valueIndex2 0)) := by
    apply Finset.sum_eq_single (valueIndex2 0)
    · intro b _ hb
      exact (hb (zeroJetIndex_eq b)).elim
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  rw [he, L2.inner_def]
  calc
    _ = ∫ x in AVenhance.unitCube, inner ℝ c (f.toFunction.jet (valueIndex2 0) x) := by
      apply integral_congr_ae
      filter_upwards [periodicJetRepresentative_ae (torusConstantCarrier 0 c).val (valueIndex2 0),
        torusConstantCarrier_raw_value_ae 0 c, periodicJetRepresentative_ae f.val (valueIndex2 0)]
        with x hc hcc hf
      change inner ℝ ((torusConstantCarrier 0 c).val (valueIndex2 0) x)
        (f.val (valueIndex2 0) x) = inner ℝ c (f.toFunction.jet (valueIndex2 0) x)
      exact congrArg₂ (inner ℝ) (hc.symm.trans hcc) hf.symm
    _ = _ := integral_inner (torus_value_integrable f) c

theorem torusMean_norm_le_zero (f : TorusHk 0 E) : ‖torusMean f‖ ≤ ‖f‖ := by
  have h := (real_inner_le_norm (torusConstantCarrier 0 (torusMean f)) f)
  rw [inner_constant_zero, real_inner_self_eq_norm_sq, torusConstant_zero_norm] at h
  by_cases hz : ‖torusMean f‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖torusMean f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith


theorem torusMean_norm_le {K L : ℕ} (ρ : ℝ) (hKL : K ≤ L) (f : TorusHk L E) :
    ‖torusMean f‖ ≤ torusHkNorm ρ hKL f := by
  rw [← torusMean_truncate (Nat.zero_le L) f]
  exact (torusMean_norm_le_zero _).trans (torusHk_value_le_modelNorm ρ hKL f)

theorem meanComplement_orthogonal (c : E) (f : TorusHk 0 E) :
    inner ℝ (torusConstantCarrier 0 c) (meanComplement 0 f) = 0 := by
  rw [inner_constant_zero, torusMean_complement, inner_zero_right]

theorem mean_decomposition_sq (f : TorusHk 0 E) :
    ‖torusMean f‖ ^ 2 + ‖meanComplement 0 f‖ ^ 2 = ‖f‖ ^ 2 := by
  have h := norm_add_sq_real (torusConstantCarrier 0 (torusMean f)) (meanComplement 0 f)
  rw [meanComplement_orthogonal, mul_zero, add_zero, torusConstant_zero_norm] at h
  simpa only [meanComplement_apply, add_sub_cancel] using h.symm

theorem meanComplement_zero_contract (f : TorusHk 0 E) : ‖meanComplement 0 f‖ ≤ ‖f‖ := by
  have h := mean_decomposition_sq f
  have hsq : ‖meanComplement 0 f‖ ^ 2 ≤ ‖f‖ ^ 2 := by nlinarith [sq_nonneg ‖torusMean f‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [FiniteDimensional ℝ E] in
/-- The factorial norm triangle inequality, also for radius zero. -/
theorem torusHkNorm_add {K L : ℕ} (ρ : ℝ) (hKL : K ≤ L) (f g : TorusHk L E) :
    torusHkNorm ρ hKL (f + g) ≤ torusHkNorm ρ hKL f + torusHkNorm ρ hKL g := by
  unfold torusHkNorm
  rw [map_add]
  change Real.sqrt (factorialNormSq ρ ((truncateTorusHk hKL f).val +
    (truncateTorusHk hKL g).val)) ≤ _
  simp only [← factorialWeightedJet_norm, factorialWeightedJet_add]
  exact norm_add_le _ _

theorem torusHkNorm_complement {K L : ℕ} (ρ : ℝ) (hKL : K ≤ L) (f : TorusHk L E) :
    torusHkNorm ρ hKL (meanComplement L f) ≤ 2 * torusHkNorm ρ hKL f := by
  have he : meanComplement L f = f + torusConstantCarrier L (-torusMean f) := by
    rw [meanComplement_apply, sub_eq_add_neg]
    exact congrArg (fun z => f + z) ((torusConstantLinearMap L).map_neg _).symm
  rw [he]
  exact (torusHkNorm_add ρ hKL _ _).trans (by
    rw [torusHkNorm_constant, norm_neg]
    linarith [torusMean_norm_le ρ hKL f])

end AVRegularity.CycleJointProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! Normalization of the individual diagonal and source blocks by the cell mean. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Fix constants on the diagonal and remove both mean modes from its raw response. -/
def meanNormalizedDiagonal (K : ι → ℕ) (Mout : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (v : ι) : TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  meanProjection 0 (max Mout (K v)) +
    (meanComplement _).comp ((Pd v).comp (meanComplement 0))

/-- Every normalized positive source block annihilates constants. -/
def meanNormalizedSource (K : ι → ℕ) (Mout : ℕ)
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (n : ℕ) (v u : ι) : TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  (meanComplement _).comp ((Pg n v u).comp (meanComplement 0))

private theorem meanNormalized_l2_numeric (a b c d δ : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hδ : 1 ≤ δ)
    (hq : c ≤ δ * b) (hd : a ^ 2 + b ^ 2 = d ^ 2) :
    a ^ 2 + c ^ 2 ≤ (δ * d) ^ 2 := by
  have hδsq : 1 ≤ δ ^ 2 := one_le_pow₀ hδ
  have hsq : c ^ 2 ≤ (δ * b) ^ 2 :=
    (sq_le_sq₀ hc (mul_nonneg (zero_le_one.trans hδ) hb)).mpr hq
  calc
    a ^ 2 + c ^ 2 ≤ a ^ 2 + δ ^ 2 * b ^ 2 := by nlinarith only [hsq]
    _ ≤ δ ^ 2 * a ^ 2 + δ ^ 2 * b ^ 2 := by nlinarith only [hδsq, sq_nonneg a]
    _ = (δ * d) ^ 2 := by rw [← mul_add, hd, mul_pow]

omit [DecidableEq ι] [Fintype ι] in
/-- Orthogonality retains the raw diagonal L2 bound under mean normalization. -/
theorem meanNormalizedDiagonal_l2 (K : ι → ℕ) (Mout : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (δ : ℝ) (hδ : 1 ≤ δ)
    (hb : ∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤ δ * ‖f‖) (v : ι)
    (f : TorusHk 0 (h v)) :
    torusHkNorm 1 (Nat.zero_le _) (meanNormalizedDiagonal K Mout Pd v f) ≤ δ * ‖f‖ := by
  let z := truncateTorusHk (Nat.zero_le _) (Pd v (meanComplement 0 f))
  have he : truncateTorusHk (Nat.zero_le _) (meanNormalizedDiagonal K Mout Pd v f) =
      torusConstantCarrier 0 (torusMean f) + meanComplement 0 z := by
    simp only [meanNormalizedDiagonal, LinearMap.add_apply, LinearMap.comp_apply,
      meanProjection_apply]
    rw [map_add, torusConstantCarrier_truncate, truncate_meanComplement]
  have hz : ‖meanComplement 0 z‖ ≤ δ * ‖meanComplement 0 f‖ :=
    (meanComplement_zero_contract z).trans (by
      simpa only [torusHkNorm_order_zero] using hb v (meanComplement 0 f))
  rw [torusHkNorm_order_zero, he]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hδ) (norm_nonneg _))).mp
  rw [norm_add_sq_real, meanComplement_orthogonal, mul_zero, add_zero,
    torusConstant_zero_norm]
  exact meanNormalized_l2_numeric _ _ _ _ δ (norm_nonneg _) (norm_nonneg _) hδ hz
    (mean_decomposition_sq f)

omit [DecidableEq ι] [Fintype ι] in
/-- The normalized diagonal has factorial bound one plus twice the raw bound. -/
theorem meanNormalizedDiagonal_jets (K : ι → ℕ) (Mout : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (ρ C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ v f, torusHkNorm ρ (le_max_left Mout (K v)) (Pd v f) ≤ C * ‖f‖)
    (v : ι) (f : TorusHk 0 (h v)) :
    torusHkNorm ρ (le_max_left Mout (K v)) (meanNormalizedDiagonal K Mout Pd v f) ≤
      (1 + 2 * C) * ‖f‖ := by
  simp only [meanNormalizedDiagonal, LinearMap.add_apply, LinearMap.comp_apply, meanProjection_apply]
  apply (torusHkNorm_add ρ _ _ _).trans
  rw [torusHkNorm_constant]
  have hd := torusHkNorm_complement ρ (le_max_left Mout (K v)) (Pd v (meanComplement 0 f))
  have hraw := (hb v (meanComplement 0 f)).trans
    (mul_le_mul_of_nonneg_left (meanComplement_zero_contract f) hC)
  calc
    _ ≤ ‖f‖ + 2 * (C * ‖f‖) := add_le_add (torusMean_norm_le_zero f)
      (hd.trans (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2)))
    _ = _ := by ring

omit [DecidableEq ι] [Fintype ι] in
/-- Source normalization costs two in a factorial bound. -/
theorem meanNormalizedSource_jets (K : ι → ℕ) (Mout : ℕ)
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (ρ C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (n : ℕ) (v u : ι)
    (hb : ∀ f, torusHkNorm ρ (le_max_left Mout (K v)) (Pg n v u f) ≤ C * a * ‖f‖)
    (f : TorusHk 0 (h u)) :
    torusHkNorm ρ (le_max_left Mout (K v)) (meanNormalizedSource K Mout Pg n v u f) ≤
      (1 + 2 * C) * a * ‖f‖ := by
  change torusHkNorm ρ _ (meanComplement _ (Pg n v u (meanComplement 0 f))) ≤ _
  have hd := torusHkNorm_complement ρ (le_max_left Mout (K v)) (Pg n v u (meanComplement 0 f))
  have hraw := (hb (meanComplement 0 f)).trans
    (mul_le_mul_of_nonneg_left (meanComplement_zero_contract f) (mul_nonneg hC ha))
  calc
    _ ≤ 2 * (C * a * ‖f‖) :=
      hd.trans (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2))
    _ ≤ 2 * (C * a * ‖f‖) + a * ‖f‖ :=
      le_add_of_nonneg_right (mul_nonneg ha (norm_nonneg _))
    _ = _ := by ring

/-- The normalized blocks satisfy the full joint model, with the prescribed constants. -/
theorem meanNormalizedBlocks_model {D' : ℕ} {P' : Type*} {Ctx : P' → Type*}
    (F : ChartedFamily ι h D' P' Ctx) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (Mout H : ℕ) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (Θ E Pacc ρ C CP Cth : ℝ) (hC : 0 ≤ C) (hCP : 0 ≤ CP) (hE : 0 ≤ E) (hCth : 0 ≤ Cth)
    (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ Cth * Θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ Cth * Θ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hr : IsRawTriangularModel K Mout H F A E Pacc ρ C CP Pd Pg) :
    IsJointModel π K Mout H F A Θ E Pacc ρ
      (jointModelConstant (1 + 2 * C) Cth H) (4 * CP)
      (meanNormalizedDiagonal K Mout Pd) (meanNormalizedSource K Mout Pg) := by
  have hrp : 0 ≤ E ^ Pacc := Real.rpow_nonneg hE _
  have hδ : 1 ≤ 1 + CP * E ^ Pacc := le_add_of_nonneg_right (mul_nonneg hCP hrp)
  apply isJointModel_of_positive_blocks F K Mout H π hπ A hA (1 + 2 * C) Cth Θ E Pacc ρ (4 * CP)
    (by positivity) hCth hΘ₀ hΘ₁ (by positivity) hrow hcol
    (meanNormalizedDiagonal K Mout Pd) (meanNormalizedSource K Mout Pg)
  · intro n hn hnH v u hpath
    simp only [meanNormalizedSource, hr.1 n hn hnH v u hpath,
      LinearMap.zero_comp, LinearMap.comp_zero]
  · intro v f
    exact (meanNormalizedDiagonal_l2 K Mout Pd (1 + CP * E ^ Pacc) hδ
      (fun v f => by simpa only [torusHkNorm_zero_input] using hr.2.1 v f) v f).trans
      (mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith only [hCP] : CP ≤ 4 * CP) hrp))
        (norm_nonneg _))
  · exact meanNormalizedDiagonal_jets K Mout Pd ρ C hC
      (fun v f => by simpa only [torusHkNorm_zero_input] using hr.2.2.1 v f)
  · intro n hn hnH v u f
    exact meanNormalizedSource_jets K Mout Pg ρ C ((A ^ n) v u) hC
      (positiveMatrix_pow_nonneg A hA n v u) n v u
      (fun f => by simpa only [torusHkNorm_zero_input] using hr.2.2.2 n hn hnH v u f) f
  · intro v c
    change torusConstantCarrier _ (torusMean (torusConstantCarrier 0 c)) +
      meanComplement _ (Pd v (meanComplement 0 (torusConstantCarrier 0 c))) = _
    simp only [torusMean_constant, meanComplement_constant, map_zero, add_zero]
  · intro n _ _ v u c
    change meanComplement _ (Pg n v u (meanComplement 0 (torusConstantCarrier 0 c))) = 0
    simp only [meanComplement_constant, map_zero]

omit [DecidableEq ι] in
/-- The normalized family operator is its constant mode plus the double-complemented raw operator. -/
theorem jointOperator_meanNormalized (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (f : ∀ v, TorusHk 0 (h v)) (v : ι) :
    jointOperator K Mout H (meanNormalizedDiagonal K Mout Pd) (meanNormalizedSource K Mout Pg) f v =
      torusConstantCarrier _ (torusMean (f v)) +
        meanComplement _ (jointOperator K Mout H Pd Pg (fun u => meanComplement 0 (f u)) v) := by
  simp only [jointOperator, meanNormalizedDiagonal, meanNormalizedSource, LinearMap.add_apply,
    LinearMap.comp_apply, meanProjection_apply, map_add, map_sum, add_assoc]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Linearity of the joint operator in its full input family. -/
theorem jointOperator_sub (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (f g : ∀ v, TorusHk 0 (h v)) (v : ι) :
    jointOperator K Mout H Pd Pg (f - g) v =
      jointOperator K Mout H Pd Pg f v - jointOperator K Mout H Pd Pg g v := by
  simp only [jointOperator, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
  abel

omit [DecidableEq ι] in
/-- Read the normalized joint operator at the physical slot. -/
theorem meanNormalized_physical (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (g : ∀ j, TorusHk 0 (h j)) (i : ι) :
    truncateTorusHk (le_max_right Mout (K i))
      (jointOperator K Mout H (meanNormalizedDiagonal K Mout Pd) (meanNormalizedSource K Mout Pg) g i) =
      torusConstantCarrier (K i) (torusMean (g i)) + meanComplement (K i)
        (truncateTorusHk (le_max_right Mout (K i)) (jointOperator K Mout H Pd Pg g i) -
          truncateTorusHk (le_max_right Mout (K i)) (jointOperator K Mout H Pd Pg
            (fun j => torusConstantCarrier 0 (torusMean (g j))) i)) := by
  let gc : ∀ j, TorusHk 0 (h j) := fun j => torusConstantCarrier 0 (torusMean (g j))
  have hinput : jointOperator K Mout H Pd Pg (fun j => meanComplement 0 (g j)) i =
      jointOperator K Mout H Pd Pg g i - jointOperator K Mout H Pd Pg gc i :=
    jointOperator_sub K Mout H Pd Pg g gc i
  have hb := congrArg (truncateTorusHk (le_max_right Mout (K i)))
    (jointOperator_meanNormalized K Mout H Pd Pg g i)
  rw [map_add, torusConstantCarrier_truncate, truncate_meanComplement] at hb
  exact hb.trans (congrArg
    (fun z : TorusHk (max Mout (K i)) (h i) =>
      torusConstantCarrier (K i) (torusMean (g i)) +
        meanComplement (K i) (truncateTorusHk (le_max_right Mout (K i)) z)) hinput |>.trans
      (by rw [map_sub]))

private theorem mean_error_algebra {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] V) (U c a b : V) (hU : Q U = U - c) (hc : Q c = 0) :
    U - (c + Q (a - b)) = Q (U - a) - Q (c - b) := by
  rw [map_sub, map_sub, map_sub, hU, hc]
  abel

omit [DecidableEq ι] in
/-- Mean conservation expresses normalized error through two raw errors. -/
theorem meanNormalized_error_identity (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (g : ∀ j, TorusHk 0 (h j)) (i : ι) (U : TorusHk (K i) (h i))
    (hm : torusMean U = torusMean (g i)) :
    U - truncateTorusHk (le_max_right Mout (K i))
      (jointOperator K Mout H (meanNormalizedDiagonal K Mout Pd) (meanNormalizedSource K Mout Pg) g i) =
      meanComplement (K i) (U - truncateTorusHk (le_max_right Mout (K i))
        (jointOperator K Mout H Pd Pg g i)) -
      meanComplement (K i) (torusConstantCarrier (K i) (torusMean (g i)) -
        truncateTorusHk (le_max_right Mout (K i)) (jointOperator K Mout H Pd Pg
          (fun j => torusConstantCarrier 0 (torusMean (g j))) i)) := by
  rw [meanNormalized_physical]
  exact mean_error_algebra (meanComplement (K i)) U _ _ _
    (by rw [meanComplement_apply, hm]) (meanComplement_constant _ _)

end AVRegularity.CycleJointProofs.Assembly
end
