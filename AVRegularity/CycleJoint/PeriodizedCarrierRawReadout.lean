-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.NormalizedCoefficientSeminormFinite
public import AVRegularity.CycleWords.GeometryPieceNonempty
import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
import AVRegularity.KernelEnergy.TorusMultiplierCLM
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
public import AVRegularity.Statements.Intermediate.CycleJoint.TorusHkNorm
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The covering-plane localization depends linearly on the actual torus datum. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}

theorem localizeTorusCarrier_add (u v : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) :
    localizeTorusCarrier (u + v) C hC hc =
      localizeTorusCarrier u C hC hc + localizeTorusCarrier v C hC hc := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have he : ∀ b, (u + v).toFunction.jet b =ᵐ[volume]
      (u.toFunction.jet + v.toFunction.jet) b :=
    fun b => periodicJetRepresentative_add_global u.val v.val b
  have hp := multiplicationRawJet_congr_ae C _ _ he a
  have ha := Lp.coeFn_add ((localizeTorusCarrier u C hC hc).val a)
    ((localizeTorusCarrier v C hC hc).val a)
  simp only [Measure.restrict_univ] at ha
  filter_upwards [localizeTorusCarrier_jet_ae (u + v) C hC hc a,
    localizeTorusCarrier_jet_ae u C hC hc a, localizeTorusCarrier_jet_ae v C hC hc a,
    ha, hp] with x hsum hu hv hadd hprod
  change _ = (((localizeTorusCarrier u C hC hc).val a +
    (localizeTorusCarrier v C hC hc).val a) : Lp F 2 (volume.restrict Set.univ)) x
  change ((localizeTorusCarrier (u + v) C hC hc).val a) x = _ at hsum
  change ((localizeTorusCarrier u C hC hc).val a) x = _ at hu
  change ((localizeTorusCarrier v C hC hc).val a) x = _ at hv
  simp only [Pi.add_apply] at hadd
  rw [hadd, hsum, hu, hv, hprod]
  exact congrFun (congrFun (multiplicationRawJet_add C u.toFunction.jet v.toFunction.jet) a) x

theorem localizeTorusCarrier_smul (c : ℝ) (u : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) :
    localizeTorusCarrier (c • u) C hC hc = c • localizeTorusCarrier u C hC hc := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have he : ∀ b, (c • u).toFunction.jet b =ᵐ[volume] (c • u.toFunction.jet) b :=
    fun b => periodicJetRepresentative_smul_global c u.val b
  have hp := multiplicationRawJet_congr_ae C _ _ he a
  have ha := Lp.coeFn_smul c ((localizeTorusCarrier u C hC hc).val a)
  simp only [Measure.restrict_univ] at ha
  filter_upwards [localizeTorusCarrier_jet_ae (c • u) C hC hc a,
    localizeTorusCarrier_jet_ae u C hC hc a,
    ha, hp] with x hsum hu hsmul hprod
  change _ = ((c • (localizeTorusCarrier u C hC hc).val a) :
    Lp F 2 (volume.restrict Set.univ)) x
  change ((localizeTorusCarrier (c • u) C hC hc).val a) x = _ at hsum
  change ((localizeTorusCarrier u C hC hc).val a) x = _ at hu
  simp only [Pi.smul_apply] at hsmul
  rw [hsmul, hsum, hu, hprod]
  exact congrFun (congrFun (multiplicationRawJet_smul C c u.toFunction.jet) a) x

def localizeTorusLinear (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) :
    TorusHk K E →ₗ[ℝ] PlaneHk Set.univ K F where
  toFun u := localizeTorusCarrier u C hC hc
  map_add' u v := localizeTorusCarrier_add u v C hC hc
  map_smul' c u := localizeTorusCarrier_smul c u C hC hc

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Cell change of variables preserves integrability, including every spatial atom of a weak equation. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem integrable_plane_affine {f : Vec 2 → E}
    (hf : Integrable f (volume : Measure (Vec 2)))
    (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    Integrable (fun z : Vec 2 => f (y + e • z)) volume := by
  have hm := hf.smul_measure (c := ENNReal.ofReal |(e ^ 2)⁻¹|) ENNReal.ofReal_ne_top
  rw [← CycleWords.map_cell_affine_volume e he y] at hm
  exact hm.comp_measurable (by fun_prop)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The quadratic near-identity hypothesis controls the literal difference entries, with its original smallness parameter. -/

theorem symmetricMetric_difference_entry_abs_le (M : Matrix (Fin 2) (Fin 2) ℝ)
    (g : ℝ) (hsym : M.IsSymm)
    (hquad : ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) (i j : Fin 2) :
    |(M - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤ g := by
  have hsym' : M 1 0 = M 0 1 := by
    change M.transpose = M at hsym
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hsym
  have h00 := hquad ![1, 0]
  have h11 := hquad ![0, 1]
  have hp := hquad ![1, 1]
  have hm := hquad ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11 hp hm
  norm_num at h00 h11 hp hm
  rw [hsym'] at hp hm
  rw [abs_le] at h00 h11 hp hm
  fin_cases i <;> fin_cases j <;> simp only [Matrix.sub_apply, Matrix.one_apply] <;> norm_num
  · exact abs_le.mpr h00
  · rw [abs_le]
    constructor <;> linarith only [hp.1, hp.2, hm.1, hm.2]
  · rw [hsym', abs_le]
    constructor <;> linarith only [hp.1, hp.2, hm.1, hm.2]
  · exact abs_le.mpr h11

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Lower stored orders retain their factorial bound with exactly the same radius and constant. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_truncate_le {μ : Measure (Vec 2)} {K L : ℕ}
    (hKL : K ≤ L) (ρ : ℝ) (D : JetL2 μ L E) :
    factorialNormSq ρ (truncateJet hKL D) ≤ factorialNormSq ρ D := by
  classical
  rw [factorialNormSq_eq_sum_indices, factorialNormSq_eq_sum_indices]
  simp only [truncateJet_apply]
  let price := fun a : JetIndex2 L => factorialWeight ρ a.1.val * ‖D a‖ ^ 2
  change (∑ a : JetIndex2 K, price (truncateJetIndex hKL a)) ≤ ∑ a : JetIndex2 L, price a
  calc
    _ = ∑ a ∈ Finset.univ.image (truncateJetIndex hKL), price a := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact truncateJetIndex_injective hKL hab
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => mul_nonneg (factorialWeight_nonneg ρ a.1.val) (sq_nonneg _))

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Measurability of the time-clamped metric used in native energy estimates. -/

theorem metricClamp_time_slice_measurable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ z i j, Measurable (fun t => G t z i j))
    (a b : ℝ) (z : Vec 2) (i j : Fin 2) :
    Measurable (fun t => CycleWords.metricClamp a b G t z i j) := by
  exact (hG z i j).comp (measurable_const.max (measurable_id.min measurable_const))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Integration of the literal tensor identity for compact coefficients and periodic jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem periodic_multiplicationTerm_integral_sumSq {K j : ℕ} (hj : j ≤ K)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hc : HasCompactSupport C) (D : RawJet2 K E)
    (hD : HasPeriodicOrderedWeakJet D) (m : PositionMask j) :
    (∑ w : DerivativeWord2 j, ∫ x, ‖multiplicationTerm hj C D m w x‖ ^ 2 ∂volume) =
      ∑ v : DerivativeWord2 (maskRightLength j m), ∫ x,
        ‖coefficientDerivativeArray C (maskLeftLength j m) x
          (D ⟨⟨maskRightLength j m,
            Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x)‖ ^ 2 ∂volume := by
  have hi (w : DerivativeWord2 j) :=
    (periodic_compact_multiplicationTerm_memLp hj C hC hc D hD m w).norm.integrable_sq
  have hs : ContDiff ℝ (maskLeftLength j m : ℕ) C :=
    hC.of_le (by exact_mod_cast (maskLeftLength_le j m).trans hj)
  have ha (v : DerivativeWord2 (maskRightLength j m)) :=
    (periodic_compact_operator_memLp
      (D ⟨⟨maskRightLength j m,
        Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩)
      (hD.2.1 _) (hD.1 _)
      (fun x => coefficientDerivativeArray C (maskLeftLength j m) x)
      (coefficientDerivativeArray_continuous C _ hs)
      (coefficientDerivativeArray_compact C hc _)).norm.integrable_sq
  rw [← integral_finsetSum Finset.univ (fun w _ => hi w),
    ← integral_finsetSum Finset.univ (fun v _ => ha v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (multiplicationTerm_sumSq_eq_array hj C D m)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact ordered drift arrays scale by inverse viscosity in diffusion time. -/

/-- Constant velocity scaling agrees with scaling the literal drift coefficient. -/
theorem driftCoefficient_const_smul (c : ℝ) (v : Vec 2 → Vec 2) :
    driftCoefficient (fun x => c • v x) = fun x => c • driftCoefficient v x := by
  funext x
  simp only [driftCoefficient, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- A physical ordered-array bound retains its exact inverse-viscosity price. -/
theorem timeNormalizedVelocity_coefficientArray_norm_le {ν M : ℝ} (hν : 0 < ν)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (j : ℕ) (x : Vec 2)
    (hb : ‖coefficientDerivativeArray (driftCoefficient (v (ν⁻¹ * t))) j x‖ ≤ M) :
    ‖coefficientDerivativeArray (driftCoefficient (timeNormalizedVelocity ν v t)) j x‖ ≤
      ν⁻¹ * M := by
  change ‖coefficientDerivativeArray (driftCoefficient (fun x => ν⁻¹ • v (ν⁻¹ * t) x)) j x‖ ≤ _
  rw [driftCoefficient_const_smul, coefficientDerivativeArray_const_smul,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hν)]
  exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hν.le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Summable actual plane weak jets close in the Hilbert graph on any localization domain. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {U : Set (Vec 2)} {K : ℕ}

def planeJetComponentCLM (a : JetIndex2 K) :
    PlaneHk U K E →L[ℝ] Lp E 2 (volume.restrict U) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => Lp E 2 (volume.restrict U)) a).comp
    (planeHkGraph (E := E) U K).toSubmodule.subtypeL

theorem planeWeakJet_tsum {J : Type*} [Countable J]
    (D : J → RawJet2 K E) (hm : ∀ j, JetMemL2On U (D j))
    (hw : ∀ j, HasOrderedWeakJetOn U (D j))
    (hs : (∑' j, ∑ a : JetIndex2 K, eLpNorm (D j a) 2 (volume.restrict U)) < ⊤) :
    JetMemL2On U (fun a x => ∑' j, D j a x) ∧
      HasOrderedWeakJetOn U (fun a x => ∑' j, D j a x) := by
  classical
  let u : J → PlaneHk U K E := fun j => (PlaneHkFunction.mk (D j) (hm j) (hw j)).toHk
  have hu (j : J) : ‖u j‖ₑ ≤ ∑ a : JetIndex2 K, eLpNorm (D j a) 2 (volume.restrict U) := by
    have he (a : JetIndex2 K) : ‖(u j).val a‖ₑ = eLpNorm (D j a) 2 (volume.restrict U) := by
      change ‖(hm j a).toLp (D j a)‖ₑ = _
      exact Lp.enorm_toLp _
    change ‖(u j).val‖ₑ ≤ _
    simpa only [he] using CycleEvolution.cellFiniteArray_enorm_le_sum (u j).val
  have hus : (∑' j, ‖u j‖ₑ) < ⊤ := (ENNReal.tsum_le_tsum hu).trans_lt hs
  have hsummable : Summable u := Summable.of_enorm hus.ne
  have ha (a : JetIndex2 K) : (∑' j, ‖planeJetComponentCLM a (u j)‖ₑ) < ⊤ := by
    have he (j : J) : ‖planeJetComponentCLM a (u j)‖ₑ =
        eLpNorm (D j a) 2 (volume.restrict U) := by
      change ‖(hm j a).toLp (D j a)‖ₑ = _
      exact Lp.enorm_toLp _
    simp_rw [he]
    refine (ENNReal.tsum_le_tsum (fun j => ?_)).trans_lt hs
    exact Finset.single_le_sum (fun a _ => (bot_le : (0 : ℝ≥0∞) ≤
      eLpNorm (D j a) 2 (volume.restrict U))) (Finset.mem_univ a)
  have hrep (a : JetIndex2 K) :
      (((∑' j, u j).val a) : Vec 2 → E) =ᵐ[volume.restrict U] (fun x => ∑' j, D j a x) := by
    change (planeJetComponentCLM a (∑' j, u j) : Vec 2 → E) =ᵐ[_] _
    rw [(planeJetComponentCLM a).map_tsum hsummable]
    have hall : ∀ᵐ x ∂volume.restrict U, ∀ j, planeJetComponentCLM a (u j) x = D j a x :=
      ae_all_iff.mpr (fun j => (hm j a).coeFn_toLp)
    filter_upwards [Lp.coeFn_tsum (ha a).ne, hall] with x hx hx'
    exact hx.trans (tsum_congr (fun j => hx' j))
  refine ⟨fun a => (Lp.memLp _).ae_eq (hrep a), ?_⟩
  exact hasOrderedWeakJetOn_congr_ae (fun a => hrep a) (∑' j, u j).toFunction.hasWeakJet

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The raw weak spatial form has the exact inverse diffusion-time factor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every atom of the weak spatial form scales by the same inverse diffusion factor. -/
theorem planeWeakSpatialRhs_time_normalization {ν : ℝ} (hν : ν ≠ 0)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E) (t : ℝ) (x : Vec 2) :
    planeWeakSpatialRhs 1 (timeNormalizedVelocity ν v) φ dφ
      (fun r => du (ν⁻¹ * r))
      (fun r y => ν⁻¹ • flux (ν⁻¹ * r) y)
      (fun r y => ν⁻¹ • F (ν⁻¹ * r) y)
      (fun r y => ν⁻¹ • g (ν⁻¹ * r) y) t x =
      ν⁻¹ * planeWeakSpatialRhs ν v φ dφ du flux F g (ν⁻¹ * t) x := by
  simp only [planeWeakSpatialRhs, timeNormalizedVelocity, Pi.smul_apply,
    smul_eq_mul, PiLp.smul_apply, ← smul_add, real_inner_smul_left,
    mul_assoc, ← Finset.mul_sum, one_mul]
  rw [mul_add, mul_sub, mul_sub, mul_neg, ← mul_assoc ν⁻¹ ν,
    inv_mul_cancel₀ hν, one_mul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Finite coefficient regularity survives exact cell coordinates and time dilation. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_affine_time_scaling_ne_top
    (ρ r : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b ν : ℝ) (hν : 0 < ν)
    (c e : ℝ) (y : Vec 2) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤) :
    coefficientSeminorm r K (ν * a) (ν * b)
      (fun t z => c • A (ν⁻¹ * t) (y + e • z)) ≠ ⊤ := by
  apply coefficientSeminorm_ne_top_of_array_bound r K (ν * a) (ν * b) _
    (fun j => ‖c‖ * ‖e ^ j.val‖ * (coefficientOrderSup a b A j.val).toReal)
  intro j t ht z
  rw [coefficientDerivativeArray_const_smul, coefficientDerivativeArray_affine,
    norm_smul, norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (coefficientOrderSup_derivative_bound ρ hρ K a b A hA j.val
      (Nat.le_of_lt_succ j.isLt) _ (inv_mul_mem_Icc_of_scaled hν ht) _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem affineTimeScaledCoefficient_contDiff (K : ℕ) (a b ν : ℝ) (hν : 0 < ν)
    (c e : ℝ) (y : Vec 2) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) :
    ContDiff ℝ (K : ℕ) (fun z => c • A (ν⁻¹ * t) (y + e • z)) :=
  ((hc _ (inv_mul_mem_Icc_of_scaled hν ht)).comp
    (contDiff_const.add (contDiff_id.const_smul e))).const_smul c

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Conversion of the prepared datum radius pays only its finite derivative reserve. -/

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialNormSq_mono_radius {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (D : JetL2 μ K E) : factorialNormSq r D ≤ factorialNormSq R D := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (derivativeNormSq_nonneg D j)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hrR (2 * j.val)) (sq_nonneg _)

theorem factorialNormSq_radius_reserve (r L : ℝ) (hL : 1 ≤ L)
    (D : JetL2 μ K E) :
    factorialNormSq r D ≤ L ^ (2 * K) * factorialNormSq (r / L) D := by
  unfold factorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (Weighted.factorial_radius_weight_le r L hL (Nat.le_of_lt_succ j.isLt))
    (derivativeNormSq_nonneg D j)

theorem factorialNormSq_radius_conversion {r R L : ℝ} (hr : 0 ≤ r) (hL : 1 ≤ L)
    (hrR : r ≤ L * R) (D : JetL2 μ K E) :
    factorialNormSq r D ≤ L ^ (2 * K) * factorialNormSq R D := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  exact (factorialNormSq_radius_reserve r L hL D).trans
    (mul_le_mul_of_nonneg_left
      (factorialNormSq_mono_radius (div_nonneg hr hLp.le)
        ((div_le_iff₀ hLp).mpr (by simpa [mul_comm] using hrR)) D) (by positivity))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Positive block majorants control the exact inverse-mass family energy. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem mass_normalized_square (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (i : ι) (x : ℝ) :
    (x / Real.sqrt (π i)) ^ 2 = (π i)⁻¹ * x ^ 2 := by
  rw [div_pow, Real.sq_sqrt (hπ i).le, div_eq_mul_inv, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem mass_normalized_block_bound_identity (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (v u : ι) (C a x : ℝ) :
    C * a * x / Real.sqrt (π v) =
      C * (Real.sqrt (π u / π v) * a) * (x / Real.sqrt (π u)) := by
  rw [Real.sqrt_div (hπ u).le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (hπ u)), ne_of_gt (Real.sqrt_pos.mpr (hπ v))]

omit [DecidableEq ι] in
theorem massBlockSchur_norm_sq
    {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (C θ : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (T : ∀ v u, E u → F v) (hT : ∀ v u f, ‖T v u f‖ ≤ C * A v u * ‖f‖)
    (f : ∀ u, E u) :
    (∑ v, (π v)⁻¹ * ‖∑ u, T v u (f u)‖ ^ 2) ≤
      (C * θ) ^ 2 * ∑ u, (π u)⁻¹ * ‖f u‖ ^ 2 := by
  let b := massConjugatedMatrix π A
  have hb (v u : ι) : 0 ≤ b v u :=
    mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  have hbound (v : ι) :
      ‖∑ u, T v u (f u)‖ / Real.sqrt (π v) ≤
        ∑ u, (C * b v u) * (‖f u‖ / Real.sqrt (π u)) := by
    calc
      ‖∑ u, T v u (f u)‖ / Real.sqrt (π v) ≤
          (∑ u, ‖T v u (f u)‖) / Real.sqrt (π v) :=
        div_le_div_of_nonneg_right (norm_sum_le _ _) (Real.sqrt_nonneg _)
      _ ≤ (∑ u, C * A v u * ‖f u‖) / Real.sqrt (π v) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hT v u (f u)))
          (Real.sqrt_nonneg _)
      _ = ∑ u, (C * b v u) * (‖f u‖ / Real.sqrt (π u)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun u _ => mass_normalized_block_bound_identity π hπ v u C _ _)
  have hr (v : ι) : ∑ u, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow v) hC
  have hc (u : ι) : ∑ v, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol u) hC
  have hs := KernelEnergy.finiteRootSchur (fun v u => C * b v u)
    (fun u => ‖f u‖ / Real.sqrt (π u))
    (fun v => ‖∑ u, T v u (f u)‖ / Real.sqrt (π v)) 1 (C * θ) (by norm_num)
    (fun v u => mul_nonneg hC (hb v u)) hr hc
    (fun v => ⟨div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), by
      simpa only [one_mul] using hbound v⟩)
  simpa only [one_mul, mass_normalized_square π hπ] using hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual plane carrier arithmetic agrees almost everywhere with the literal raw jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrier_jet_add_ae (f g : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (f + g).toFunction.jet a =ᵐ[volume] fun x => f.toFunction.jet a x + g.toFunction.jet a x := by
  have he := Lp.coeFn_add (f.val a) (g.val a)
  simp only [Measure.restrict_univ] at he
  have hv := (planeJetComponentCLM (U := Set.univ) a).map_add f g
  change (f + g).val a = f.val a + g.val a at hv
  change (((f + g).val a) : Vec 2 → E) =ᵐ[volume] fun x => f.val a x + g.val a x
  rw [hv]
  exact he

theorem planeCarrier_jet_smul_ae (c : ℝ) (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (c • f).toFunction.jet a =ᵐ[volume] fun x => c • f.toFunction.jet a x := by
  have he := Lp.coeFn_smul c (f.val a)
  simp only [Measure.restrict_univ] at he
  have hv := (planeJetComponentCLM (U := Set.univ) a).map_smul c f
  change (c • f).val a = c • f.val a at hv
  change (((c • f).val a) : Vec 2 → E) =ᵐ[volume] fun x => c • f.val a x
  rw [hv]
  exact he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual solution and its coupled error supply the retained curve's
continuous trace and its lower-order agreement with the gradient carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupled_error_retained_trace
    (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (D : ℕ) (K : ι → ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (uH u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) uH wH)
    (he : IsCoupledWeakSolutionPlane ν a b v D K A (fun _ => 0) ferr (fun _ _ => 0)
      (fun i t => uH i t - u i t) (fun i t => wH i t - w i t)) :
    (∀ i, ContinuousOn (u i) (Set.Icc a b)) ∧
    (∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t) := by
  constructor
  · intro i
    have hc := (hs.1 i).sub (he.1 i)
    change ContinuousOn (fun t => uH i t - (uH i t - u i t)) (Set.Icc a b) at hc
    simpa only [sub_sub_cancel] using hc
  · intro i
    filter_upwards [hs.2.2.1 i, he.2.2.1 i] with t ht heq
    rw [map_sub, ht] at heq
    have hh := congrArg (fun V : PlaneHk Set.univ (K i) (h i) => uH i t - V) heq
    simpa only [sub_sub_cancel] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Extend the stored native jet by zero outside its finite Sobolev reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeNativeJetExtension {K : ℕ} (U : PlaneHk Set.univ K E)
    (x : Vec 2) (r : ℕ) (I : DerivativeWord2 r) : E :=
  if hr : r ≤ K then U.toFunction.jet ⟨⟨r, Nat.lt_succ_of_le hr⟩, I⟩ x else 0

theorem planeNativeJetExtension_index {K : ℕ} (U : PlaneHk Set.univ K E)
    (x : Vec 2) (j : JetIndex2 K) :
    planeNativeJetExtension U x j.1.val j.2 = U.toFunction.jet j x := by
  simp only [planeNativeJetExtension, dite_eq_left (Nat.le_of_lt_succ j.1.isLt)]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A weighted higher-order lift is controlled by its value and gradient energies. -/

/-- Decreasing nonnegative weights allow every positive level to be charged to the gradient sum. -/
theorem ennreal_weighted_successor_sum_le (a X : ℕ → ℝ≥0∞) (N : ℕ)
    (ha : ∀ j, a (j + 1) ≤ a j) :
    (∑ j ∈ Finset.range (N + 2), a j * X j) ≤
      (∑ j ∈ Finset.range (N + 1), a j * X j) +
        ∑ j ∈ Finset.range (N + 1), a j * X (j + 1) := by
  rw [Finset.sum_range_succ']
  have hs : (∑ j ∈ Finset.range (N + 1), a (j + 1) * X (j + 1)) ≤
      ∑ j ∈ Finset.range (N + 1), a j * X (j + 1) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul' (ha j) le_rfl
  have h0 : a 0 * X 0 ≤ ∑ j ∈ Finset.range (N + 1), a j * X j :=
    Finset.single_le_sum (f := fun j => a j * X j) (fun j _ => bot_le) (Finset.mem_range.mpr (Nat.zero_lt_succ N))
  exact (add_le_add hs h0).trans_eq (add_comm _ _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- At a radius at most one, the full lift's polynomial energy costs its value and gradient energies. -/
theorem weightedFactorialNormSq_lift_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (W : PlaneHk Set.univ (K + 1) E) :
    weightedFactorialNormSq n ϖ zc ρ (K + 1) W ≤
      weightedFactorialNormSq n ϖ zc ρ K W + weightedGradFactorialNormSq n ϖ zc ρ K W := by
  let X (j : ℕ) := ∫⁻ z, ENNReal.ofReal
    ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
      ∑ w : DerivativeWord2 j, ‖planeJetOrder W j w z‖ ^ 2)
  change (∑ j ∈ Finset.range (K + 2), ENNReal.ofReal (factorialWeight ρ j) * X j) ≤
    (∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialWeight ρ j) * X j) +
      ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialWeight ρ j) * X (j + 1)
  apply ennreal_weighted_successor_sum_le
  intro j
  exact ENNReal.ofReal_le_ofReal (factorialWeight_decreasing_order ρ hρ hρ1 (Nat.le_succ j))

/-- Truncation preserves every retained polynomial factorial moment exactly. -/
theorem weightedFactorialNormSq_truncate {K L : ℕ} (hKL : K ≤ L)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (W : PlaneHk Set.univ L E) :
    weightedFactorialNormSq n ϖ zc ρ K (truncatePlaneHk hKL W) =
      weightedFactorialNormSq n ϖ zc ρ K W := by
  have he (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) (z : Vec 2) :
      planeJetOrder (truncatePlaneHk hKL W) j w z = planeJetOrder W j w z := by
    simp only [planeJetOrder, dite_eq_left hj, dite_eq_left (hj.trans hKL)]
    rfl
  unfold weightedFactorialNormSq
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  congr 1
  apply lintegral_congr
  intro z
  simp_rw [he j hjK]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native affine time and space changes retain restricted joint coefficient measurability. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineTimeScaledCoefficient_joint_measurable
    (a b σ c e : ℝ) (hσ : 0 < σ) (yc : Vec 2)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2)) :
    Measurable (fun p : Set.Icc (σ * a) (σ * b) × Vec 2 =>
      c • A (σ⁻¹ * p.1) (yc + e • p.2)) := by
  let T : Set.Icc (σ * a) (σ * b) × Vec 2 → Set.Icc a b :=
    fun p => ⟨σ⁻¹ * p.1, inv_mul_mem_Icc_of_scaled hσ p.1.property⟩
  have hT : Measurable T :=
    (measurable_const.mul (measurable_subtype_coe.comp measurable_fst)).subtype_mk
  have hZ : Measurable (fun p : Set.Icc (σ * a) (σ * b) × Vec 2 => yc + e • p.2) :=
    measurable_const.add (measurable_snd.const_smul e)
  exact (hA.comp (hT.prodMk hZ)).const_smul c

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Actual flux vectors obey both original-mass Schur budgets before introducing an operator domain. -/

variable {ι : Type*} [Fintype ι]

theorem massRowSchur_norm_sq
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (C θ : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (Y : ∀ v _u : ι, F v) (x : ι → ℝ)
    (hY : ∀ v u, ‖Y v u‖ ≤ C * A v u * x u) :
    (∑ v, (π v)⁻¹ * ‖∑ u, Y v u‖ ^ 2) ≤
      (C * θ) ^ 2 * ∑ u, (π u)⁻¹ * x u ^ 2 := by
  let b := massConjugatedMatrix π A
  have hb (v u : ι) : 0 ≤ b v u :=
    mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  have hbound (v : ι) :
      ‖∑ u, Y v u‖ / Real.sqrt (π v) ≤
        ∑ u, (C * b v u) * (x u / Real.sqrt (π u)) := by
    calc
      ‖∑ u, Y v u‖ / Real.sqrt (π v) ≤
          (∑ u, ‖Y v u‖) / Real.sqrt (π v) :=
        div_le_div_of_nonneg_right (norm_sum_le _ _) (Real.sqrt_nonneg _)
      _ ≤ (∑ u, C * A v u * x u) / Real.sqrt (π v) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hY v u))
          (Real.sqrt_nonneg _)
      _ = ∑ u, (C * b v u) * (x u / Real.sqrt (π u)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun u _ => mass_normalized_block_bound_identity π hπ v u C _ _)
  have hr (v : ι) : ∑ u, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow v) hC
  have hc (u : ι) : ∑ v, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol u) hC
  have hs := KernelEnergy.finiteRootSchur (fun v u => C * b v u)
    (fun u => x u / Real.sqrt (π u))
    (fun v => ‖∑ u, Y v u‖ / Real.sqrt (π v)) 1 (C * θ) (by norm_num)
    (fun v u => mul_nonneg hC (hb v u)) hr hc
    (fun v => ⟨div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), by
      simpa only [one_mul] using hbound v⟩)
  simpa only [one_mul, mass_normalized_square π hπ] using hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Fixed native input/output coordinate operators have dimension-independent bounds. -/

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem native_coordinate_operator_norm_le (r : ℕ) (C : U →L[ℝ] V)
    (k : Fin 2) (A : DerivativeWord2 r) :
    ‖(Weighted.fluxCoordinateInjection k C).comp
      (PiLp.proj 2 (fun _ : DerivativeWord2 r => U) A)‖ ≤ ‖C‖ := by
  have hp : ‖(PiLp.proj 2 (fun _ : DerivativeWord2 r => U) A :
      PiLp 2 (fun _ : DerivativeWord2 r => U) →L[ℝ] U)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le g A
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul_of_nonneg_right
    (CycleWords.fluxCoordinateInjection_norm_le k C) (norm_nonneg _)).trans
      (mul_le_of_le_one_right (norm_nonneg C) hp)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Separate literal native forcing constructions determine one curve retaining every finite polynomial moment. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Separate moment constructions with the same literal forcing readout give one native curve. -/
theorem planeForcing_exists_every_moment {K : ℕ} (ϖ ρ : ℝ) (zc : Vec 2)
    (μ : Measure ℝ) (H : ℝ → Vec 2 → E)
    (h : ∀ m, ∃ V : ℝ → PlaneHk Set.univ K E,
      MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq m ϖ zc ρ K (V t) ∂μ) ≠ ⊤ ∧
      ∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] H t) :
    ∃ V : ℝ → PlaneHk Set.univ K E,
      MemLp V 2 μ ∧
      (∀ m, (∫⁻ t, weightedFactorialNormSq m ϖ zc ρ K (V t) ∂μ) ≠ ⊤) ∧
      ∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] H t := by
  obtain ⟨V, hV, _, hv⟩ := h 0
  refine ⟨V, hV, ?_, hv⟩
  intro m
  obtain ⟨W, _, he, hw⟩ := h m
  have heq : V =ᵐ[μ] W := by
    filter_upwards [hv, hw] with t ht ht'
    exact planeHk_eq_of_planeValue_ae (ht.trans ht'.symm)
  have hi := lintegral_congr_ae (heq.fun_comp
    (fun U => weightedFactorialNormSq m ϖ zc ρ K U))
  simp only [Function.comp_apply] at hi
  rw [hi]
  exact he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Certified short natural flows preserve the slow displacement used in each original source Taylor expansion. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_natural_flow_fderiv_norm_le
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m) (y : Vec 2) :
    ‖fderiv ℝ (fun x => streamFlow φ hφ r x σ) y‖ ≤ 1 + max (Cchart 0) 0 / 2 := by
  have hd : ‖fderiv ℝ (fun x => streamFlow φ hφ r x σ) y -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ max (Cchart 0) 0 / 2 := by
    simpa only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one]
      using preparation_flow_fderiv_deviation_jets hc ha r σ hr hσ hage 0 (Nat.zero_le _) y
  calc
    _ = ‖(fderiv ℝ (fun x => streamFlow φ hφ r x σ) y - ContinuousLinearMap.id ℝ (Vec 2)) +
        ContinuousLinearMap.id ℝ (Vec 2)‖ := by rw [sub_add_cancel]
    _ ≤ ‖fderiv ℝ (fun x => streamFlow φ hφ r x σ) y - ContinuousLinearMap.id ℝ (Vec 2)‖ +
        ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
    _ ≤ max (Cchart 0) 0 / 2 + 1 := add_le_add hd ContinuousLinearMap.norm_id_le
    _ = _ := add_comm _ _

theorem preparation_natural_flow_displacement_le
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m) (x y : Vec 2) :
    ‖streamFlow φ hφ r y σ - streamFlow φ hφ r x σ‖ ≤
      (1 + max (Cchart 0) 0 / 2) * ‖y - x‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ((streamFlow_spatial_smooth hφ r σ).differentiable (by simp)) z)
    (fun z _ => preparation_natural_flow_fderiv_norm_le hc ha r σ hr hσ hage z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)

theorem preparation_natural_flow_cell_displacement_le
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m) (yc z : Vec 2) (e : ℝ) :
    ‖streamFlow φ hφ r (yc + e • z) σ - streamFlow φ hφ r yc σ‖ ≤
      (1 + max (Cchart 0) 0 / 2) * (|e| * ‖z‖) := by
  simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using
    preparation_natural_flow_displacement_le hc ha r σ hr hσ hage yc (yc + e • z)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every factorial model bound controls the literal order-zero operator norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {μ : Measure (Vec 2)} {K L : ℕ}

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem derivativeNormSq_zero_eq_value (D : JetL2 μ K E) :
    derivativeNormSq D (0 : Fin (K + 1)) = ‖D (valueIndex2 K)‖ ^ 2 := by
  change (∑ w : DerivativeWord2 0, ‖D ⟨(0 : Fin (K + 1)), w⟩‖ ^ 2) =
    ‖D ⟨(0 : Fin (K + 1)), Fin.elim0⟩‖ ^ 2
  apply Finset.sum_eq_single (Fin.elim0 : DerivativeWord2 0)
  · intro b _ hb
    exact (hb (Subsingleton.elim _ _)).elim
  · exact fun hn => (hn (Finset.mem_univ _)).elim

theorem torusHk_value_le_factorial (ρ : ℝ) (f : TorusHk K E) :
    ‖truncateTorusHk (Nat.zero_le K) f‖ ≤ Real.sqrt (factorialNormSq ρ f.val) := by
  have hv : ‖truncateTorusHk (Nat.zero_le K) f‖ ^ 2 ≤ factorialNormSq ρ f.val := by
    change ‖(truncateTorusHk (Nat.zero_le K) f).val‖ ^ 2 ≤ _
    rw [zeroOrderJet_norm_sq, truncateTorusHk_apply]
    change ‖f.val (valueIndex2 K)‖ ^ 2 ≤ _
    rw [← derivativeNormSq_zero_eq_value]
    exact CoupledEnergy.Variational.derivativeNormSq_zero_le_factorial ρ _
  have hs := Real.sqrt_le_sqrt hv
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs

theorem torusHk_value_le_modelNorm (ρ : ℝ) (hKL : K ≤ L) (f : TorusHk L E) :
    ‖truncateTorusHk (Nat.zero_le L) f‖ ≤ torusHkNorm ρ hKL f := by
  have he : truncateTorusHk (Nat.zero_le K) (truncateTorusHk hKL f) =
      truncateTorusHk (Nat.zero_le L) f := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rw [zeroJetIndex_eq a]
    rfl
  rw [← he]
  exact torusHk_value_le_factorial ρ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! All chronological order-lowering factors of a jointly smooth chart are jointly smooth. -/

theorem transitionT_joint_smooth (K : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => K z.1 z.2 i j)) :
    ∀ I A : List (Fin 2), ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => transitionT (K z.1) I A z.2) := by
  intro I
  induction I with
  | nil =>
    intro A
    cases A <;> exact contDiff_const
  | cons i I ih =>
    intro A
    have hd := Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff
      (fun z : ℝ × Vec 2 => transitionT (K z.1) I A z.2) (ih A)
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 =>
        ∑ b : Fin 2, K z.1 z.2 b i *
          fderiv ℝ (transitionT (K z.1) I A) z.2 (basisVec b)) := by
      exact ContDiff.sum (fun b _ => (hK b i).mul (hd.clm_apply contDiff_const))
    cases A with
    | nil => simpa only [transitionT, add_zero] using hs
    | cons a A =>
      simpa only [transitionT] using hs.add ((hK a i).mul (ih A))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Diffusion time normalization preserves every integrability field of the weak identity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A viscous integrated weak identity becomes the identity with unit diffusion. -/
theorem coupledWeakIdentity_time_normalization (μ : Measure (Vec 2))
    {ν a b : ℝ} (hν : 0 < ν) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (u₀ f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity μ ν a b v u₀ f φ dφ du flux F g) :
    CoupledWeakIdentity μ 1 (ν * a) (ν * b) (timeNormalizedVelocity ν v)
      u₀ f φ dφ (fun r => du (ν⁻¹ * r))
      (fun r y => ν⁻¹ • flux (ν⁻¹ * r) y)
      (fun r y => ν⁻¹ • F (ν⁻¹ * r) y)
      (fun r y => ν⁻¹ • g (ν⁻¹ * r) y) := by
  let R := planeWeakSpatialRhs ν v φ dφ du flux F g
  let N := planeWeakSpatialRhs 1 (timeNormalizedVelocity ν v) φ dφ
    (fun r => du (ν⁻¹ * r))
    (fun r y => ν⁻¹ • flux (ν⁻¹ * r) y)
    (fun r y => ν⁻¹ • F (ν⁻¹ * r) y)
    (fun r y => ν⁻¹ • g (ν⁻¹ * r) y)
  have he (r : ℝ) (x : Vec 2) : N r x = ν⁻¹ * R (ν⁻¹ * r) x :=
    planeWeakSpatialRhs_time_normalization hν.ne' v φ dφ du flux F g r x
  have hi (r : ℝ) : (∫ x, N r x ∂μ) = ν⁻¹ * ∫ x, R (ν⁻¹ * r) x ∂μ := by
    simp_rw [he]
    exact integral_const_mul _ _
  change Integrable (fun x => inner ℝ (u₀ x) (φ x)) μ ∧
    Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
    (∀ s ∈ Set.Ioc (ν * a) (ν * b), Integrable (N s) μ) ∧
    IntegrableOn (fun s => ∫ x, N s x ∂μ) (Set.Ioc (ν * a) (ν * b)) ∧
    (∫ x, inner ℝ (u₀ x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc (ν * a) (ν * b), ∫ x, N s x ∂μ
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · intro r hr
    have hmem : ν⁻¹ * r ∈ Set.Ioc a b := by
      rw [show ν⁻¹ * r = r / ν by rw [div_eq_mul_inv, mul_comm]]
      exact ⟨(lt_div_iff₀ hν).mpr (by simpa only [mul_comm] using hr.1),
        (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using hr.2)⟩
    have hm := (h.2.2.1 _ hmem).const_mul ν⁻¹
    have hex : N r = fun x => ν⁻¹ * R (ν⁻¹ * r) x := funext (he r)
    rw [hex]
    exact hm
  · simp_rw [hi]
    exact integrableOn_comp_inv_mul_Ioc hν h.2.2.2.1
  · rw [show (∫ r in Set.Ioc (ν * a) (ν * b), ∫ x, N r x ∂μ) =
        ∫ r in Set.Ioc a b, ∫ x, R r x ∂μ by
      simp_rw [hi]
      exact setIntegral_inv_mul_comp_inv_mul_Ioc hν hab (fun r => ∫ x, R r x ∂μ)]
    exact h.2.2.2.2

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Radius conversion in the actual torus factorial norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusHkNorm_radius_conversion {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E)
    {r R a : ℝ} (hr : 0 ≤ r) (ha : 1 ≤ a) (hrR : r ≤ a * R) :
    torusHkNorm r hKL f ≤ a ^ K * torusHkNorm R hKL f := by
  unfold torusHkNorm
  calc
    Real.sqrt (factorialNormSq r (truncateTorusHk hKL f).val) ≤
        Real.sqrt (a ^ (2 * K) * factorialNormSq R (truncateTorusHk hKL f).val) :=
      Real.sqrt_le_sqrt (factorialNormSq_radius_conversion hr ha hrR _)
    _ = a ^ K * Real.sqrt (factorialNormSq R (truncateTorusHk hKL f).val) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ a ^ (2 * K)), Nat.mul_comm 2 K, pow_mul,
        Real.sqrt_sq (pow_nonneg (by linarith : 0 ≤ a) K)]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A finite value bound and gradient dissipation give finite weighted energy of the actual lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The genuine higher-order lift has finite integrated polynomial factorial energy. -/
theorem weightedFactorialNormSq_lift_time_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ a b : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (ha : ∀ᵐ t ∂volume.restrict (Icc a b), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (C : ℝ) (hb : ∀ t ∈ Icc a b, weightedFactorialNormSq n ϖ zc ρ K (u t) ≤ ENNReal.ofReal C)
    (hg : (∫⁻ t in Icc a b, weightedGradFactorialNormSq n ϖ zc ρ K (w t)) ≠ ⊤) :
    (∫⁻ t in Icc a b, weightedFactorialNormSq n ϖ zc ρ (K + 1) (w t)) ≠ ⊤ := by
  have he : (∫⁻ t in Icc a b, weightedFactorialNormSq n ϖ zc ρ (K + 1) (w t)) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal C + weightedGradFactorialNormSq n ϖ zc ρ K (w t) := by
    apply lintegral_mono_ae
    filter_upwards [ha, ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hh := weightedFactorialNormSq_lift_le n ϖ zc ρ hρ hρ1 (w t)
    rw [← weightedFactorialNormSq_truncate (Nat.le_succ K) n ϖ zc ρ (w t), ht] at hh
    exact hh.trans (add_le_add (hb t hmem) le_rfl)
  apply ne_top_of_le_ne_top _ he
  rw [lintegral_add_left measurable_const, lintegral_const]
  have hμ : (volume.restrict (Icc a b) : Measure ℝ) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ, hg⟩

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Locally summable lattice images of a plane weak jet define a genuine torus Sobolev witness. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def periodizeRawJet (D : RawJet2 K E) : RawJet2 K E := fun a => latticePeriodization (D a)

theorem periodizeRawJet_hasPeriodicWeakJet (D : RawJet2 K E)
    (hw : HasOrderedWeakJetOn Set.univ D)
    (hcell : (∑' n : Fin 2 → ℤ, ∑ a : JetIndex2 K,
      eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2
        (volume.restrict AVenhance.unitCube)) < ⊤)
    (hballs : ∀ R : ℝ, 0 < R → (∑' n : Fin 2 → ℤ, ∑ a : JetIndex2 K,
      eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2
        (volume.restrict (Metric.ball (0 : Vec 2) R))) < ⊤) :
    HasPeriodicOrderedWeakJet (periodizeRawJet D) := by
  classical
  have hs (μ : Measure (Vec 2))
      (hh : (∑' n : Fin 2 → ℤ, ∑ a : JetIndex2 K,
        eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2 μ) < ⊤)
      (a : JetIndex2 K) :
      (∑' n : Fin 2 → ℤ, eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2 μ) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun n => Finset.single_le_sum
      (fun b _ => (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm
        (fun x => D b (x + AVenhance.latticeShift n)) 2 μ)) (Finset.mem_univ a))).trans_lt hh
  refine ⟨fun a => latticePeriodization_periodic (D a), ?_, ?_⟩
  · intro a
    exact (CycleEvolution.cellLpSeries_memLp_bound _ _ (hs _ hcell a)).1
  · apply orderedWeakJet_global_of_balls
    intro R hR
    apply (planeWeakJet_tsum (fun n a x => D a (x + AVenhance.latticeShift n))
      (fun n a => (ENNReal.le_tsum n).trans_lt (hs _ (hballs R hR) a))
      (fun n => orderedWeakJet_restrict (orderedWeakJet_translate hw (AVenhance.latticeShift n)) _)
      (hballs R hR)).2

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The cell readout of an actual periodized carrier identifies its raw jet on the whole plane. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodizedCarrier_rawJet_ae (f : PlaneHk Set.univ K E) (U : TorusHk K E)
    (a : JetIndex2 K)
    (h : U.val a =ᵐ[volume.restrict AVenhance.unitCube] periodizeRawJet f.toFunction.jet a) :
    U.toFunction.jet a =ᵐ[volume] periodizeRawJet f.toFunction.jet a := by
  change periodicJetRepresentative U.val a =ᵐ[volume] _
  exact periodic_ae_eq_global _ _ (periodicJetRepresentative_periodic U.val a)
    (latticePeriodization_periodic (f.toFunction.jet a))
    ((periodicJetRepresentative_ae U.val a).trans h)

end AVRegularity.CycleJointProofs
end
end
