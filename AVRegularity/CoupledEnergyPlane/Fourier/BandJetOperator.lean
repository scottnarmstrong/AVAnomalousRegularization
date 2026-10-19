-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
import AVRegularity.Analysis.Convolution.Kernel.Commutation.Torus
public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertSobolevOperator
import Homogenization.Sobolev.H1.BasicLemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open AVRegularity.Analysis.Convolution
open scoped SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Classical derivatives of the actual mollifications of a weak derivative
pair. Weak derivative uniqueness identifies the smooth derivative, rather
than adding a differentiability premise on the original L² input. -/

theorem averagingOperator_weakPartial_literal_derivative
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hw : HasWeakPartialDerivOn Set.univ i f g)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) :
    averagingOperator R.toLinearEquiv.toAddHom R.continuous κ
      (hd.continuous.integrable_of_hasCompactSupport hc) g =ᵐ[volume]
        fun x => fderiv ℝ (fun y => ∫ z : Vec 2, κ z • f (y - R z)) x (basisVec i) := by
  let hκ : Integrable κ (volume : Measure (Vec 2)) :=
    hd.continuous.integrable_of_hasCompactSupport hc
  let fb := averagingOperator R.toLinearEquiv.toAddHom R.continuous κ hκ f
  let gb := averagingOperator R.toLinearEquiv.toAddHom R.continuous κ hκ g
  let F : Vec 2 → ℝ := fun x => ∫ z : Vec 2, κ z • f (x - R z)
  have hs : ∀ e : ℝ, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f x)) (fun x => inner ℝ e (g x)) := by
    intro e φ hφ hcomp hsub
    simp only [Real.inner_apply, mul_assoc, integral_const_mul]
    rw [hw φ hφ hcomp hsub, mul_neg]
  have hb : HasWeakPartialDerivOn Set.univ i fb gb := by
    simpa only [Real.inner_apply, one_mul] using
      averagingOperator_hasWeakPartialDeriv hs R.toLinearEquiv.toAddHom R.continuous hκ (1 : ℝ)
  have hfae : fb =ᵐ[volume] F := averagingOperator_plane_literal_ae R hκ f
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_literalAverage R hc hd ((Lp.memLp f).locallyIntegrable (by norm_num))
  have hwF : HasWeakPartialDerivOn Set.univ i F gb :=
    hasWeakPartialDerivOn_congr_ae (by simpa only [Measure.restrict_univ] using hfae)
      (Filter.Eventually.of_forall fun _ => rfl) hb
  have hD : Continuous fun x => fderiv ℝ F x (basisVec i) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have heq := HasWeakPartialDerivOn.ae_eq isOpen_univ
    (locallyIntegrableOn_univ.mpr ((Lp.memLp gb).locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_univ.mpr hD.locallyIntegrable) hwF
    (HasWeakPartialDerivOn.of_contDiff (hF.of_le (by simp)))
  simpa only [Measure.restrict_univ] using heq

/-- Mollifying the actual weak pair gives its actual distribution derivative. -/
theorem coordinate_lineDerivOp_averaging_weak
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hw : HasWeakPartialDerivOn Set.univ i f g)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) :
    ∂_{coordinateVector i} ((coordinateL2Equiv (ofRealL2 volume
      (averagingOperator R.toLinearEquiv.toAddHom R.continuous κ
        (hd.continuous.integrable_of_hasCompactSupport hc) f)) : Lp ℂ 2 volume) :
          𝓢'(HilbertTwo, ℂ)) =
      ((coordinateL2Equiv (ofRealL2 volume
        (averagingOperator R.toLinearEquiv.toAddHom R.continuous κ
          (hd.continuous.integrable_of_hasCompactSupport hc) g)) : Lp ℂ 2 volume) :
            𝓢'(HilbertTwo, ℂ)) := by
  apply coordinate_lineDerivOp_of_smooth_real _ _ i
    (fun y => ∫ z : Vec 2, κ z • f (y - R z))
  · exact (contDiff_literalAverage R hc hd
      ((Lp.memLp f).locallyIntegrable (by norm_num))).differentiable (by simp)
  · exact averagingOperator_plane_literal_ae R
      (hd.continuous.integrable_of_hasCompactSupport hc) f
  · exact averagingOperator_weakPartial_literal_derivative f g i hw R hc hd

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The full true plane cutoff jet as a bounded linear readout from spatial L². -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def bandJetOperator (N K : ℕ) : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    JetL2 (volume.restrict Set.univ) K E :=
  (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL.comp (hilbertBandHkOperator N K)

@[simp] theorem bandJetOperator_apply (N K : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandJetOperator N K u = (hilbertBandHk N K u).val := rfl

end AVRegularity.CoupledEnergyPlane.Fourier
end
