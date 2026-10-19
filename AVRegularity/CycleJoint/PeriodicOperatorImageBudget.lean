-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PeriodicOperatorLocalization
public import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.CoupledEnergyPlane.LowerReadout
import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
import AVRegularity.CycleJoint.CompactWeakCorrectionIntegrability
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Compact periodic testing makes every actual coupled weak RHS atom plane-integrable. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compact_weakIdentityRhs_integrable (ν s : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hv : Continuous (v s)) (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (hφ : MemLp φ 2 (volume.restrict AVenhance.unitCube))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict AVenhance.unitCube))
    (hdu : ∀ k, MemLp (du s k) 2 (volume.restrict AVenhance.unitCube))
    (hflux : ∀ k, MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube))
    (hF : ∀ k, MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (g s) 2 (volume.restrict AVenhance.unitCube))
    (hφp : AVenhance.IsZ2Periodic φ) (hdφp : ∀ k, AVenhance.IsZ2Periodic (dφ k))
    (hdup : ∀ k, AVenhance.IsZ2Periodic (du s k))
    (hflp : AVenhance.IsZ2Periodic (flux s)) (hFp : AVenhance.IsZ2Periodic (F s))
    (hgp : AVenhance.IsZ2Periodic (g s))
    (χ : Vec 2 → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => weakIdentityRhs ν v φ dφ du flux F g s x * χ x) volume := by
  have hdrift (k : Fin 2) : Integrable (fun x =>
      (v s x k * inner ℝ (du s k x) (φ x)) * χ x) volume := by
    let C : Vec 2 → E →L[ℝ] E := fun x => v s x k • ContinuousLinearMap.id ℝ E
    have hC : Continuous C := (continuous_apply k |>.comp hv).smul continuous_const
    have hbC (x : Vec 2) : ‖C x‖ ≤ V := by
      calc
        _ = ‖v s x k‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
        _ ≤ ‖v s x k‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ V := by simpa only [mul_one] using (norm_le_pi_norm (v s x) k).trans (hbv x)
    have hi := periodic_compact_coefficient_pairing_integrable _ _ (hdu k) hφ
      (hdup k) hφp C hC V hV hbC χ hχ hcχ
    simpa only [C, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hi
  have hid := fun (f g : Vec 2 → E)
      (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
      (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
      (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g) =>
    periodic_compact_coefficient_pairing_integrable f g hf hg hfp hgp
      (fun _ => ContinuousLinearMap.id ℝ E) continuous_const 1 (by norm_num)
      (fun _ => ContinuousLinearMap.norm_id_le) χ hχ hcχ
  have hdiff (k : Fin 2) : Integrable (fun x => inner ℝ (du s k x) (dφ k x) * χ x) volume := by
    simpa only [ContinuousLinearMap.id_apply] using hid _ _ (hdu k) (hdφ k) (hdup k) (hdφp k)
  have hfl (k : Fin 2) : Integrable (fun x =>
      inner ℝ (flux s x k + F s x k) (dφ k x) * χ x) volume := by
    have hp : AVenhance.IsZ2Periodic (fun x => flux s x k + F s x k) := by
      intro n x
      change flux s (x + AVenhance.latticeShift n) k + F s (x + AVenhance.latticeShift n) k = _
      rw [hflp n x, hFp n x]
    simpa only [ContinuousLinearMap.id_apply, Pi.add_apply] using hid _ _ ((hflux k).add (hF k)) (hdφ k) hp (hdφp k)
  have hgφ : Integrable (fun x => inner ℝ (g s x) (φ x) * χ x) volume := by
    simpa only [ContinuousLinearMap.id_apply] using hid _ _ hg hφ hgp hφp
  have hi := (((integrable_finsetSum Finset.univ (fun k _ => hdrift k)).neg.sub
    ((integrable_finsetSum Finset.univ (fun k _ => hdiff k)).const_mul ν)).sub
    (integrable_finsetSum Finset.univ (fun k _ => hfl k))).add hgφ
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, weakIdentityRhs, Fin.sum_univ_two]
  ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! A measurable bounded physical coefficient pairs an L2 time curve integrably. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem plane_coefficient_pairing_time_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (u : X → Lp E 2 (volume : Measure (Vec 2))) (hu : MemLp u 2 μ)
    (v : Lp F 2 (volume : Measure (Vec 2))) :
    Integrable (fun t => inner ℝ v (planeCoefficientOperator (C t) (hc t) hMC (hC t) (u t))) μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  have hm := memLp_operator_action (fun t => planeCoefficientOperator (C t) (hc t) hMC (hC t))
    (fun x => planeCoefficientOperator_stronglyMeasurable C hc hj hMC hC x) hu hMC
    (fun t => planeCoefficientOperator_norm_le (C t) (hc t) hMC (hC t))
  exact ((innerSL ℝ v).comp_memLp' hm).integrable (by norm_num)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Higher native torus carriers are dense in every lower stored order, including L². -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Literal shrinking smooth averages provide the higher-order native lifts. -/
theorem truncateTorusHk_denseRange {K L : ℕ} (hKL : K ≤ L) :
    DenseRange (truncateTorusHk (E := E) hKL) := by
  intro U
  obtain ⟨κ, hc, hd, _, hmass⟩ := exists_normalized_smooth_kernel
  obtain ⟨R, hzero⟩ := exists_shrinking_linearEquiv
  let f := cellToTorus (U.val (valueIndex2 K))
  let UN n := periodicSmoothing (K := K) (R n) κ hc hd f
  have ht : Tendsto UN atTop (𝓝 U) :=
    tendsto_periodicSmoothing R hzero hc hd hmass U
  have hr (n : ℕ) : UN n ∈ Set.range (truncateTorusHk (E := E) hKL) := by
    refine ⟨periodicSmoothing (K := L) (R n) κ hc hd f, ?_⟩
    apply TorusHk.ext_value
    change (periodicSmoothing (K := L) (R n) κ hc hd f).val (valueIndex2 L) =
      (periodicSmoothing (K := K) (R n) κ hc hd f).val (valueIndex2 K)
    rw [periodicSmoothing_value, periodicSmoothing_value]
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall hr)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Periodic image bounds control the total energy of compact operator patches. -/

variable {E F J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype J]

theorem periodic_operator_image_integral_budget
    (C : J → Vec 2 → E →L[ℝ] F) (hc : ∀ j, Continuous (C j))
    (hcs : ∀ j, HasCompactSupport (C j)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, (∑ j, ∑' n : Fin 2 → ℤ,
      ENNReal.ofReal (‖C j (x + AVenhance.latticeShift n)‖ ^ 2)) ≤ ENNReal.ofReal B)
    (f : Vec 2 → E) (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hp : AVenhance.IsZ2Periodic f) :
    (∑ j, ∫ x, ‖C j x (f x)‖ ^ 2 ∂volume) ≤
      B * ∫ x in AVenhance.unitCube, ‖f x‖ ^ 2 ∂volume := by
  have hi (j : J) := (periodic_compact_operator_memLp f hf hp (C j) (hc j) (hcs j)).norm.integrable_sq
  have ht := periodic_weight_integral_budget
    (fun j x => ENNReal.ofReal (‖C j x‖ ^ 2))
    (fun j => ((hc j).norm.measurable.pow_const 2).ennreal_ofReal)
    (ENNReal.ofReal B) hb (fun x => ENNReal.ofReal (‖f x‖ ^ 2))
    (hm.norm.pow_const 2).ennreal_ofReal
    (fun n x => by
      change ENNReal.ofReal (‖f (x + AVenhance.latticeShift n)‖ ^ 2) = _
      rw [hp n x])
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB
    (integral_nonneg (fun _ => sq_nonneg _)))).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))]
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hi _)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  rw [ENNReal.ofReal_mul hB, ofReal_integral_eq_lintegral_ofReal hf.norm.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  rw [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube] at ht
  apply le_trans _ ht
  apply Finset.sum_le_sum
  intro j _
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (‖C j x (f x)‖ ^ 2) ≤
    ENNReal.ofReal (‖C j x‖ ^ 2) * ENNReal.ofReal (‖f x‖ ^ 2)
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm (C j x) (f x)) 2

end AVRegularity.CycleJointProofs
end
