-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.ChartDerivativeBounded
import AVenhance.Infra.Flow.MeasurePreservation
public import AVenhance.Statements.FlowDefs.FlowIsFlow
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
public import AVenhance.Infra.Flow.Laws
import AVenhance.Infra.Construction.StreamAdmissible

@[expose] public section

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Measure preservation and integral transport for renewal charts. -/

noncomputable def streamFlowHomeomorph {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) : Vec 2 ≃ₜ Vec 2 where
  toFun := fun x => AVRegularity.streamFlow φ hφ t x s
  invFun := fun x => AVRegularity.streamFlow φ hφ s x t
  left_inv := by
    intro x
    have hX := flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
    exact (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX x s t s).trans (hX.1 x s)
  right_inv := by
    intro x
    have hX := flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
    exact (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX x t s t).trans (hX.1 x t)
  continuous_toFun := (streamFlow_spatial_smooth hφ t s).continuous
  continuous_invFun := (streamFlow_spatial_smooth hφ s t).continuous

theorem streamFlow_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) :
    MeasurePreserving (fun x => AVRegularity.streamFlow φ hφ t x s) volume volume := by
  exact Infra.Flow.flow_measurePreserving_of_divergence_free
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ)
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz)
    (AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero hφ)
    s t

theorem integral_streamFlow {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (u : Vec 2 → ℝ) :
    ∫ y, u (AVRegularity.streamFlow φ hφ t y s) = ∫ x, u x := by
  exact (streamFlow_measurePreserving hφ t s).integral_comp
    (streamFlowHomeomorph hφ t s).measurableEmbedding u

theorem chart_integral (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ) (u : Vec 2 → ℝ) :
    ∫ y, u (ocChart α q Λ m φ hφ l t y) = ∫ x, u x :=
  integral_streamFlow hφ t _ u

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleReference

/-! Smooth, compactly supported spatial derivatives of space-time tests. -/

theorem joint_spaceGrad_smooth {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => spaceGrad (η p.1) p.2 i) := by
  exact (AVRegularity.Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff _ hη).clm_apply
    contDiff_const

theorem joint_spaceGrad_compact {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) (i : Fin 2) :
    HasCompactSupport (fun p : ℝ × Vec 2 => spaceGrad (η p.1) p.2 i) := by
  have he (p : ℝ × Vec 2) : spaceGrad (η p.1) p.2 i =
      fderiv ℝ (fun z : ℝ × Vec 2 => η z.1 z.2) p (0, basisVec i) := by
    have hd := (hη.differentiable (by simp) p).hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Vec 2) p.1 p.2)
    have hd' : HasFDerivAt (η p.1)
        ((fderiv ℝ (fun z : ℝ × Vec 2 => η z.1 z.2) p).comp
          (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) p.2 := by
      simpa only [Function.comp_def] using hd
    unfold spaceGrad
    rw [hd'.fderiv]
    rfl
  simp_rw [he]
  exact (hc.fderiv ℝ).comp_left (g := fun L : (ℝ × Vec 2) →L[ℝ] ℝ => L (0, basisVec i)) rfl

theorem memL2_mul_compact_test_integrable {u η : ℝ × Vec 2 → ℝ}
    {S : Set (ℝ × Vec 2)} (hu : MemLp u 2 (volume.restrict S))
    (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun p => u p * η p) (volume.restrict S) := by
  have ht := hη.memLp_of_hasCompactSupport hc (p := (2 : ENNReal))
    (μ := (volume : Measure (ℝ × Vec 2)))
  exact hu.integrable_mul (ht.mono_measure Measure.restrict_le_self)

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Integrability of compactly tested space-time L² gradients. -/

theorem spacetime_gradient_pair_integrable {D V : ℝ × Vec 2 → Vec 2}
    {S : Set (ℝ × Vec 2)} (hD : ∀ i : Fin 2, MemLp (fun p => D p i) 2 (volume.restrict S))
    (hV : ∀ i : Fin 2, Continuous (fun p => V p i))
    (hc : ∀ i : Fin 2, HasCompactSupport (fun p => V p i)) :
    Integrable (fun p => vecDot (D p) (V p)) (volume.restrict S) := by
  have hi (i : Fin 2) := memL2_mul_compact_test_integrable (hD i) (hV i) (hc i)
  exact integrable_finsetSum Finset.univ (fun i _ => hi i)

theorem joint_rotated_gradient_smooth {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (sigmaMat.mulVec (spaceGrad (η p.1) p.2)) i) := by
  fin_cases i
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      (joint_spaceGrad_smooth hη 1).neg
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      joint_spaceGrad_smooth hη 0

theorem joint_rotated_gradient_compact {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) (i : Fin 2) :
    HasCompactSupport (fun p : ℝ × Vec 2 => (sigmaMat.mulVec (spaceGrad (η p.1) p.2)) i) := by
  fin_cases i
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.neg_def] using
      (joint_spaceGrad_compact hη hc 1).neg
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      joint_spaceGrad_compact hη hc 0

end AVRegularity.CycleReference
end
