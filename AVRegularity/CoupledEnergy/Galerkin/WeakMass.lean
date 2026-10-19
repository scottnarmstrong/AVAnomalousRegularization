-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.ODE.Linear.Existence
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

section
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Absolutely continuous ODE paths for finite-dimensional Galerkin systems. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The bounded measurable operator and integrable source of a finite-dimensional linear system. -/
structure FiniteGalerkinODEData (a b : ℝ) (hab : a ≤ b) where
  operator : ℝ → V →L[ℝ] V
  forcing : ℝ → V
  initial : V
  operatorBound : ℝ
  operatorBound_nonneg : 0 ≤ operatorBound
  operator_aestronglyMeasurable : AEStronglyMeasurable operator volume
  operator_norm_le : ∀ t, ‖operator t‖ ≤ operatorBound
  forcing_intervalIntegrable : IntervalIntegrable forcing volume a b

namespace FiniteGalerkinODEData

/-- Convert finite-range coefficient data to the upstream measurable linear ODE interface. -/
noncomputable def toLinearODE {a b : ℝ} (hab : a ≤ b)
    (D : FiniteGalerkinODEData (V := V) a b hab) :
    AVenhance.Infra.ODE.LinearODEData (E := V) a b hab where
  A := D.operator
  f := D.forcing
  y₀ := D.initial
  operatorBound := D.operatorBound
  operatorBound_nonneg := D.operatorBound_nonneg
  operator_aestronglyMeasurable := D.operator_aestronglyMeasurable
  operator_norm_le := D.operator_norm_le
  forcing_intervalIntegrable := D.forcing_intervalIntegrable

/-- A bounded measurable linear Galerkin ODE has a unique absolutely continuous integral path. -/
theorem existsUnique_absolutelyContinuous {a b : ℝ} (hab : a ≤ b)
    (D : FiniteGalerkinODEData (V := V) a b hab) :
    ∃! y : C(Icc a b, V),
      AVenhance.Infra.ODE.IsLinearIntegralSolution D.operator D.forcing D.initial a b
          (AVenhance.Infra.ODE.extendCurve hab y) ∧
        AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b := by
  exact (D.toLinearODE hab).existsUnique_absolutelyContinuous_integralSolution

end FiniteGalerkinODEData

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
/-! Finite-dimensional mass forms convert weak linear systems to ordinary ODEs. -/

@[expose] public section

noncomputable section

namespace AVRegularity.CoupledEnergy.Galerkin

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A nondegenerate finite-dimensional weak mass form is an isomorphism onto the algebraic dual.
The injectivity premise is discharged for Fourier ranges by positivity of the L² value pairing. -/
noncomputable def weakMassEquiv (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) : V ≃ₗ[ℝ] V →ₗ[ℝ] ℝ := by
  haveI : FiniteDimensional ℝ (V →ₗ[ℝ] ℝ) := inferInstance
  have hdim : Module.finrank ℝ V = Module.finrank ℝ (V →ₗ[ℝ] ℝ) := by
    rw [Module.finrank_linearMap_self]
  exact LinearMap.linearEquivOfInjective M hM hdim

/-- The ordinary generator associated with an operator-valued weak form. -/
def weakMassGenerator (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V :=
  (weakMassEquiv M hM).symm.toLinearMap.comp B

/-- The ordinary source associated with a weak forcing functional. -/
def weakMassSource (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) (b : V →ₗ[ℝ] ℝ) : V :=
  (weakMassEquiv M hM).symm b

@[simp] theorem weakMassGenerator_mass (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x : V) :
    M (weakMassGenerator M hM B x) = B x := by
  change weakMassEquiv M hM ((weakMassEquiv M hM).symm (B x)) = B x
  exact LinearEquiv.apply_symm_apply _ _

@[simp] theorem weakMassSource_mass (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) (b : V →ₗ[ℝ] ℝ) :
    M (weakMassSource M hM b) = b := by
  change weakMassEquiv M hM ((weakMassEquiv M hM).symm b) = b
  exact LinearEquiv.apply_symm_apply _ _

end AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CoupledEnergy.Galerkin

/-- Finite dimensionality makes the weak-form generator a continuous operator for the ODE API. -/
noncomputable def weakMassGeneratorCLM {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (weakMassGenerator M hM B)

end AVRegularity.CoupledEnergy.Galerkin

end
end
end
