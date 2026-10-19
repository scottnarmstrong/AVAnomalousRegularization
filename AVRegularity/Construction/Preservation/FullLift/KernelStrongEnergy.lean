-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Analysis.Convolution.Kernel.PairedSource
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.Construction.Preservation.Buffer.KernelSchurTimeRestriction
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.KernelEnergy.TorusKernelComponentSup
public import AVRegularity.EntryWeak.JointSourceCongruence
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
public import AVRegularity.Statements.Intermediate.CycleComparison.CellInner
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Velocity.IncrementProvider
import AVRegularity.Construction.Scales.Times

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Transfer scalar convolution regularizers to any finite real Hilbert fiber by Parseval.
Together with the scalar retraction this is the root-space transfer required here. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F]

omit [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F] in
private theorem lp_basis_coordinate_synthesis {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F)
    (f : ι → Lp ℝ 2 μ) (i : ι) :
    (innerSL ℝ (b i)).compLpL 2 μ
      (∑ j, (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 μ (f j)) = f i := by
  classical
  apply Lp.ext
  have he := ae_all_iff.mpr fun j =>
    (ContinuousLinearMap.toSpanSingleton ℝ (b j)).coeFn_compLpL (f j)
  filter_upwards [(innerSL ℝ (b i)).coeFn_compLpL
    (∑ j, (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 μ (f j)), he,
    Lp.coeFn_fun_finsetSum Finset.univ (fun j =>
      (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 μ (f j))] with x hx hy hs
  rw [hx]
  change inner ℝ (b i) _ = _
  rw [hs]
  simp [inner_sum, hy, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]

omit [FiniteDimensional ℝ F] in
private theorem torus_sum_jet {K : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → TorusHk K F) (a : JetIndex2 K) :
    (∑ i, f i).val a = ∑ i, (f i).val a := by
  exact map_sum ((PiLp.proj (𝕜 := ℝ) 2
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) F) a).comp
    (torusHkGraph (E := F) K).toSubmodule.subtypeL) f Finset.univ

omit [FiniteDimensional ℝ F] in
private theorem torus_basis_coordinate_synthesis {K : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (f : ι → TorusHk K ℝ) (i : ι) :
    mapTorusHk (innerSL ℝ (b i))
      (∑ j, mapTorusHk (ContinuousLinearMap.toSpanSingleton ℝ (b j)) (f j)) = f i := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [mapTorusHk_jet_eq_compLp, torus_sum_jet]
  simp_rw [mapTorusHk_jet_eq_compLp]
  exact lp_basis_coordinate_synthesis _ b (fun j => (f j).val a) i

/-- Scalar regularization transfers to a finite real Hilbert space with identical constants. -/
theorem kernel_regularizer_of_scalar
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec)
    {ρ a b : ℝ} {k Dm : ℕ} {c : ℕ → ℝ}
    (hS : IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b c S.width (S.op φ₀ hφ₀)) :
    IsSpatialRegularizerTorus (G := F) ρ k Dm a b c S.width (S.op φ₀ hφ₀) := by
  classical
  let B := stdOrthonormalBasis ℝ F
  let μ := volume.restrict AVenhance.unitCube
  refine ⟨?_, fun t _ z => kernelSpec_commutes_first_derivatives φ₀ hφ₀ S t z, hS.2.2.1, ?_⟩
  · intro z
    have hm : StronglyMeasurable (fun t : Set.Icc a b =>
        ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (B i)).compLpL 2 μ
          (S.op φ₀ hφ₀ t ((innerSL ℝ (B i)).compLpL 2 μ z))) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro i _
      exact (ContinuousLinearMap.toSpanSingleton ℝ (B i)).compLpL 2 μ |>.continuous.comp_stronglyMeasurable
        (hS.1 ((innerSL ℝ (B i)).compLpL 2 μ z))
    have heq : (fun t : Set.Icc a b =>
        ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (B i)).compLpL 2 μ
          (S.op φ₀ hφ₀ t ((innerSL ℝ (B i)).compLpL 2 μ z))) =
        (fun t : Set.Icc a b => S.op φ₀ hφ₀ t z) := by
      funext t
      calc
        _ = ∑ i, S.op φ₀ hφ₀ t ((ContinuousLinearMap.toSpanSingleton ℝ (B i)).compLpL 2 μ
            ((innerSL ℝ (B i)).compLpL 2 μ z)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact kernelSpec_op_fiberMap _ φ₀ hφ₀ S t _
        _ = _ := by rw [← map_sum, lp_coordinates_reconstruct]
    exact heq ▸ hm
  · intro t ht j hj z
    have hex i := hS.2.2.2 t ht j hj (mapTorusHk (innerSL ℝ (B i)) z)
    choose Y hvalue hbound using hex
    let Z : TorusHk (k + j) F :=
      ∑ i, mapTorusHk (ContinuousLinearMap.toSpanSingleton ℝ (B i)) (Y i)
    refine ⟨Z, ?_, ?_⟩
    · change (∑ i, mapTorusHk (ContinuousLinearMap.toSpanSingleton ℝ (B i)) (Y i)).val _ = _
      rw [torus_sum_jet]
      simp_rw [mapTorusHk_jet_eq_compLp, hvalue, mapTorusHk_jet_eq_compLp,
        kernelSpec_op_fiberMap]
      rw [← map_sum, lp_coordinates_reconstruct]
    · rw [← derivFactorialNormSq_coordinates j B ρ Z]
      have hcoord i : mapTorusHk (innerSL ℝ (B i)) Z = Y i :=
        torus_basis_coordinate_synthesis B Y i
      simp_rw [hcoord]
      calc
        _ ≤ ∑ i, (c j / S.width ^ j) ^ 2 *
            factorialNormSq ρ (mapTorusHk (innerSL ℝ (B i)) z).val :=
          Finset.sum_le_sum fun i _ => hbound i
        _ = _ := by rw [← Finset.mul_sum, factorialNormSq_coordinates]

/-- transfer between nontrivial root spaces, componentwise and with no loss in constants. -/
theorem kernel_regularizer_transfer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec)
    {ρ a b : ℝ} {k Dm : ℕ} {c : ℕ → ℝ}
    (hS : IsSpatialRegularizerTorus (G := E) ρ k Dm a b c S.width (S.op φ₀ hφ₀)) :
    IsSpatialRegularizerTorus (G := F) ρ k Dm a b c S.width (S.op φ₀ hφ₀) := by
  exact kernel_regularizer_of_scalar φ₀ hφ₀ S (kernel_regularizer_to_scalar φ₀ hφ₀ S hS)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Identify the existing paired weak smoother with the literal native kernel operator. -/

section
open AVRegularity.Analysis.Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem averagingOperator_torus_congr_map {ρ σ : Vec 2 →+ UnitAddTorus (Fin 2)}
    (hρ : Continuous ρ) (hσ : Continuous σ) (h : ρ = σ)
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) :
    averagingOperator (E := E) (μ := torusMeasure) ρ hρ κ hκ =
      averagingOperator σ hσ κ hκ := by
  subst σ
  rfl

theorem kernelSpec_paired_realization_value (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (S : KernelSpec) (t : ℝ) (R T : Vec 2 ≃L[ℝ] Vec 2)
    (hR : R.toLinearEquiv.toAddHom = displacement S.width (S.H₁ t))
    (hT : T.toLinearEquiv.toAddHom = displacement S.width (S.H₂ t))
    (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • T (basisVec 1) = basisVec i)
    (k : ℕ) (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    (pairedWeakSmoothingTorus (K := k) R T (momentKernel φ₀ S.order)
      (hasCompactSupport_momentKernel hc S.order) (contDiff_momentKernel hc hd S.order)
      cH cV hcoeff (cellToTorus z)).val (valueIndex2 k) = S.op φ₀ hφ₀ t z := by
  rw [pairedWeakSmoothingTorus_value]
  let A := averagingOperator (E := E) (μ := torusMeasure)
    (torusQuotient.comp (displacement S.width (S.H₁ t)))
    (continuous_torusQuotient.comp (continuous_displacement S.width (S.H₁ t)))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order)
  let B := averagingOperator (E := E) (μ := torusMeasure)
    (torusQuotient.comp (displacement S.width (S.H₂ t)))
    (continuous_torusQuotient.comp (continuous_displacement S.width (S.H₂ t)))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order)
  have hA := averagingOperator_torus_congr_map (E := E)
    (ρ := torusQuotient.comp R.toLinearEquiv.toAddHom)
    (σ := torusQuotient.comp (displacement S.width (S.H₁ t)))
    (continuous_torusQuotient.comp R.continuous)
    (continuous_torusQuotient.comp (continuous_displacement S.width (S.H₁ t)))
    (by apply AddMonoidHom.ext; intro z; exact congrArg torusQuotient (congrArg (fun δ => δ z) hR))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order)
  have hB := averagingOperator_torus_congr_map (E := E)
    (ρ := torusQuotient.comp T.toLinearEquiv.toAddHom)
    (σ := torusQuotient.comp (displacement S.width (S.H₂ t)))
    (continuous_torusQuotient.comp T.continuous)
    (continuous_torusQuotient.comp (continuous_displacement S.width (S.H₂ t)))
    (by apply AddMonoidHom.ext; intro z; exact congrArg torusQuotient (congrArg (fun δ => δ z) hT))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order)
  rw [hA, hB]
  change torusToCell (A (B (cellToTorus z))) =
    torusToCell (A (cellToTorus (torusToCell (B (cellToTorus z)))))
  rw [cellToTorus_torusToCell]
end

/-! Actual paired moving kernels have regularizer certificates from their spanning coordinates. -/

section
open AVRegularity.Analysis.Convolution

theorem exists_kernelSpec_paired_regularizer_constants (φ₀ : Vec 2 → ℝ)
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [CompleteSpace E],
    ∀ (S : KernelSpec), S.order = n → 0 < S.width →
      Measurable S.H₁ → Measurable S.H₂ →
    ∀ (R T : ℝ → Vec 2 ≃L[ℝ] Vec 2),
      (∀ t, (R t).toLinearEquiv.toAddHom = displacement S.width (S.H₁ t)) →
      (∀ t, (T t).toLinearEquiv.toAddHom = displacement S.width (S.H₂ t)) →
    ∀ (cH cV : ℝ → Fin 2 → ℝ),
      (∀ t i, cH t i • R t (basisVec 0) + cV t i • T t (basisVec 1) = basisVec i) →
      (∀ t i, |cH t i| ≤ 2 / S.width) → (∀ t i, |cV t i| ≤ 2 / S.width) →
    ∀ (ρ a b : ℝ) (k Dm : ℕ),
      IsSpatialRegularizerTorus (G := E) ρ k Dm a b c S.width
        (S.op φ₀ (hd.continuous.integrable_of_hasCompactSupport hc)) := by
  classical
  have hg (j : ℕ) := exists_paired_kernel_zero_gain
    (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n) j
  choose c hcn hg using hg
  refine ⟨c, hcn, ?_⟩
  intro E _ _ _ _ _ _ S hn hr hH₁ hH₂ R T hR hT cH cV hcoeff hH hV ρ a b k Dm
  let hφ₀ : Integrable φ₀ := hd.continuous.integrable_of_hasCompactSupport hc
  have hzero : IsSpatialRegularizerTorus (G := E) ρ 0 Dm a b c S.width
      (S.op φ₀ hφ₀) := by
    refine ⟨?_, ?_, fun j _ => hcn j, ?_⟩
    · intro z
      exact (kernelSpec_op_stronglyMeasurable φ₀ hφ₀ S hH₁ hH₂
        (contDiff_momentKernel hc hd S.order).continuous.measurable z).comp_measurable
          measurable_subtype_coe
    · intro t _ z
      exact kernelSpec_commutes_first_derivatives φ₀ hφ₀ S t z
    · intro t _ j _ z
      let Y := pairedWeakSmoothingTorus (K := 0 + j) (R t) (T t)
        (momentKernel φ₀ S.order) (hasCompactSupport_momentKernel hc S.order)
        (contDiff_momentKernel hc hd S.order) (cH t) (cV t) (hcoeff t)
        (cellToTorus (z.val (valueIndex2 0)))
      refine ⟨Y, ?_, ?_⟩
      · exact kernelSpec_paired_realization_value φ₀ hφ₀ hc hd S t (R t) (T t)
          (hR t) (hT t) (cH t) (cV t) (hcoeff t) (0 + j) (z.val (valueIndex2 0))
      · have hh := hg j E (R t) (T t) (cH t) (cV t) (hcoeff t) S.width hr
          (hH t) (hV t) (cellToTorus (z.val (valueIndex2 0))) ρ
        rw [← hn] at hh
        rw [cellToTorus.norm_map] at hh
        rw [factorialNormSq_order_zero]
        exact hh
  exact spatial_regularizer_all_orders ρ Dm a b c S.width (S.op φ₀ hφ₀) hzero k
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Inverse-column coordinates on the project's ordinary vector carrier. -/

theorem vector_inverse_column_coordinates (H₁ H₂ : Vec 2 →L[ℝ] Vec 2)
    (V : Vec 2 ≃L[ℝ] Vec 2)
    (h₁ : V (basisVec 0) = H₁ (basisVec 0))
    (h₂ : V (basisVec 1) = H₂ (basisVec 1)) (i : Fin 2) :
    (V.symm (basisVec i)) 0 • H₁ (basisVec 0) +
      (V.symm (basisVec i)) 1 • H₂ (basisVec 1) = basisVec i := by
  have hV (x : Vec 2) : V x = x 0 • H₁ (basisVec 0) + x 1 • H₂ (basisVec 1) := by
    have hx : x = x 0 • basisVec 0 + x 1 • basisVec 1 := by
      funext j
      fin_cases j <;> simp [basisVec]
    calc
      V x = V (x 0 • basisVec 0 + x 1 • basisVec 1) := congrArg V hx
      _ = x 0 • V (basisVec 0) + x 1 • V (basisVec 1) := by
        simp only [map_add, map_smul]
      _ = _ := by rw [h₁, h₂]
  exact (hV (V.symm (basisVec i))).symm.trans (V.apply_symm_apply _)

theorem vector_inverse_column_bound (V : Vec 2 ≃L[ℝ] Vec 2)
    (hV : ‖V.symm.toContinuousLinearMap‖ ≤ 2) (i j : Fin 2) :
    |V.symm (basisVec i) j| ≤ 2 := by
  calc
    |V.symm (basisVec i) j| = ‖V.symm (basisVec i) j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖V.symm (basisVec i)‖ := norm_le_pi_norm _ _
    _ ≤ ‖V.symm.toContinuousLinearMap‖ * ‖(basisVec i : Vec 2)‖ :=
      V.symm.toContinuousLinearMap.le_opNorm _
    _ = ‖V.symm.toContinuousLinearMap‖ := by simp [basisVec, Pi.norm_single]
    _ ≤ 2 := hV

def scaledVectorEquiv (H : Vec 2 ≃L[ℝ] Vec 2) (r : ℝ) (hr : r ≠ 0) :
    Vec 2 ≃L[ℝ] Vec 2 :=
  (H.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ (Vec 2) r hr)).toContinuousLinearEquiv

theorem vector_inverse_scaled_coordinates (H₁ H₂ V : Vec 2 ≃L[ℝ] Vec 2)
    (h₁ : V (basisVec 0) = H₁ (basisVec 0))
    (h₂ : V (basisVec 1) = H₂ (basisVec 1)) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    ((V.symm (basisVec i)) 0 / r) • scaledVectorEquiv H₁ r hr.ne' (basisVec 0) +
      ((V.symm (basisVec i)) 1 / r) • scaledVectorEquiv H₂ r hr.ne' (basisVec 1) =
        basisVec i := by
  change ((V.symm (basisVec i)) 0 / r) • (r • H₁ (basisVec 0)) +
    ((V.symm (basisVec i)) 1 / r) • (r • H₂ (basisVec 1)) = basisVec i
  rw [smul_smul, smul_smul, div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne']
  exact vector_inverse_column_coordinates H₁.toContinuousLinearMap H₂.toContinuousLinearMap
    V h₁ h₂ i

theorem vector_inverse_scaled_bound (V : Vec 2 ≃L[ℝ] Vec 2)
    (hV : ‖V.symm.toContinuousLinearMap‖ ≤ 2) {r : ℝ} (hr : 0 < r) (i j : Fin 2) :
    |V.symm (basisVec i) j / r| ≤ 2 / r := by
  rw [abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (vector_inverse_column_bound V hV i j) hr.le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Supply the paired regularizer coordinates from the ordinary vector geometry. -/

open AVRegularity.Analysis.Convolution

theorem exists_kernelSpec_vector_regularizer_constants (φ₀ : Vec 2 → ℝ)
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [CompleteSpace E],
    ∀ (S : KernelSpec), S.order = n → 0 < S.width →
      Measurable S.H₁ → Measurable S.H₂ →
    ∀ (H₁ H₂ V : ℝ → Vec 2 ≃L[ℝ] Vec 2),
      (∀ t, S.H₁ t = (H₁ t).toContinuousLinearMap) →
      (∀ t, S.H₂ t = (H₂ t).toContinuousLinearMap) →
      (∀ t, V t (basisVec 0) = H₁ t (basisVec 0)) →
      (∀ t, V t (basisVec 1) = H₂ t (basisVec 1)) →
      (∀ t, ‖(V t).symm.toContinuousLinearMap‖ ≤ 2) →
    ∀ (ρ a b : ℝ) (k Dm : ℕ),
      IsSpatialRegularizerTorus (G := E) ρ k Dm a b c S.width
        (S.op φ₀ (hd.continuous.integrable_of_hasCompactSupport hc)) := by
  obtain ⟨c, hcn, hreg⟩ := exists_kernelSpec_paired_regularizer_constants φ₀ hc hd n
  refine ⟨c, hcn, ?_⟩
  intro E _ _ _ _ _ _ S hn hr hmeas₁ hmeas₂ H₁ H₂ V hH₁ hH₂ hv₁ hv₂ hv ρ a b k Dm
  refine hreg E S hn hr hmeas₁ hmeas₂
    (fun t => scaledVectorEquiv (H₁ t) S.width hr.ne')
    (fun t => scaledVectorEquiv (H₂ t) S.width hr.ne') ?_ ?_
    (fun t => (fun i => (V t).symm (basisVec i) 0 / S.width))
    (fun t => (fun i => (V t).symm (basisVec i) 1 / S.width)) ?_ ?_ ?_ ρ a b k Dm
  · intro t
    apply AddHom.ext
    intro z
    change S.width • (H₁ t).toContinuousLinearMap z =
      S.width • S.H₁ t z
    rw [hH₁ t]
  · intro t
    apply AddHom.ext
    intro z
    change S.width • (H₂ t).toContinuousLinearMap z =
      S.width • S.H₂ t z
    rw [hH₂ t]
  · exact fun t i => vector_inverse_scaled_coordinates (H₁ t) (H₂ t)
      (V t) (hv₁ t) (hv₂ t) hr i
  · exact fun t i => vector_inverse_scaled_bound (V t) (hv t) hr i 0
  · exact fun t i => vector_inverse_scaled_bound (V t) (hv t) hr i 1

end AVRegularity.Construction.Preservation.FullLift
end
end

section
section
/-! Nonsingularity of the actual transported sampled ellipse. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem scaled_refFlux_diagSqrt_det_isUnit {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a)
    (t : ℝ) : IsUnit (diagSqrt (a⁻¹ • ocRefFlux α q Λ ζ m ν t)).det := by
  apply isUnit_iff_ne_zero.mpr
  apply diagSqrt_det_ne_zero
  intro i
  change 0 < a⁻¹ * ocRefFlux α q Λ ζ m ν t i i
  exact mul_pos (inv_pos.mpr ha)
    (hν.trans_le (CycleReference.refFlux_diagonal_molecular_lower hΛ hζ hν t i))

theorem sampledEllipse_det_isUnit (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκb : 0 < D.κ b) (hκnext : 0 < D.κ (b + 1)) (s ti : ℝ) (li : ℤ) :
    IsUnit (sampledEllipse D b s ti li).det := by
  rw [sampledEllipse, Matrix.det_mul]
  have hj : (jacMatrix (fun y => D.flowOf b s y
      ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)))
      (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1))
        (D.flowOf b ti 0 s) ti)).det = 1 :=
    CycleReference.streamFlow_jacMatrix_det_one (D.hΦ b) _ _ _
  rw [hj, one_mul]
  exact scaled_refFlux_diagSqrt_det_isUnit hΛ hζ hκnext hκb ti

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual fresh axes admit continuous linear equivalence realizations. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

def matrixContinuousLinearEquiv (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : IsUnit A.det) :
    Vec 2 ≃L[ℝ] Vec 2 := by
  letI := Matrix.invertibleOfIsUnitDet A hA
  exact (Matrix.toLinearEquiv' A inferInstance).toContinuousLinearEquiv

theorem matrixContinuousLinearEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsUnit A.det) (x : Vec 2) :
    matrixContinuousLinearEquiv A hA x = Matrix.toLin' A x := rfl

theorem exists_fresh_quiet_margin (D : OCData) (b : ℕ) (hΛ : 1 ≤ D.Λ) (t : ℝ) :
    ∃ l : ℤ, t ∈ Set.Ico
      (((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1))
      (((l : ℝ) + 3 / 2) * ocTauPP D.α D.q D.Λ (b + 1)) := by
  let h := ocTauPP D.α D.q D.Λ (b + 1)
  have hh : 0 < h := Stream.ocTauPP_pos hΛ
  refine ⟨⌊t / h - 1 / 2⌋, ?_, ?_⟩
  · have hf := Int.floor_le (t / h - 1 / 2)
    have he : (⌊t / h - 1 / 2⌋ : ℝ) + 1 / 2 ≤ t / h := by linarith
    exact (le_div_iff₀ hh).mp he
  · have hf := Int.lt_floor_add_one (t / h - 1 / 2)
    have he : t / h < (⌊t / h - 1 / 2⌋ : ℝ) + 3 / 2 := by linarith
    exact (div_lt_iff₀ hh).mp he

theorem fresh_axes_exists_equivalences (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκb : 0 < D.κ b) (hκnext : 0 < D.κ (b + 1))
    (H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2) (haxes : IsFreshAxes D b H₁ H₂) (t : ℝ) :
    ∃ R T : Vec 2 ≃L[ℝ] Vec 2,
      R.toContinuousLinearMap = H₁ t ∧ T.toContinuousLinearMap = H₂ t := by
  obtain ⟨l, ht⟩ := exists_fresh_quiet_margin D b hΛ t
  obtain ⟨tH, tV, lH, lV, _, hmat⟩ := haxes l
  obtain ⟨hH₁, hH₂⟩ := hmat t ht
  let s := ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
  let J := jacMatrix (fun y => D.flowOf b t y s) 0
  have hJ : J.det = 1 := CycleReference.streamFlow_jacMatrix_det_one (D.hΦ b) t s 0
  have hunit (ti : ℝ) (li : ℤ) : IsUnit (J * sampledEllipse D b s ti li).det := by
    rw [Matrix.det_mul, hJ, one_mul]
    exact sampledEllipse_det_isUnit D b hΛ hζ hκb hκnext s ti li
  refine ⟨matrixContinuousLinearEquiv _ (hunit tH lH),
    matrixContinuousLinearEquiv _ (hunit tV lV), ?_, ?_⟩
  · rw [hH₁]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  · rw [hH₂]
    apply ContinuousLinearMap.ext
    intro x
    rfl

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Exact duality of each reserved covariance polynomial on finite classical fields. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covariancePolynomial_cellInner_adjoint (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) (p : ℕ) (a : ℕ → ℝ) (u q : Vec 2 → E)
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hq : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) q)
    (hpu : AVenhance.IsZ2Periodic u) (hpq : AVenhance.IsZ2Periodic q) :
    cellInner (covariancePolynomial Hc p a u) q =
      cellInner u (covariancePolynomial Hc p a q) := by
  have hcont (f : Vec 2 → E) (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f)
      (l : ℕ) (hl : l ∈ Finset.range (p + 1)) : Continuous ((covOperator Hc)^[l] f) := by
    have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    apply (covOperator_iterate_contDiff Hc l 0 f _).continuous
    exact hf.of_le (by exact_mod_cast (by omega : 0 + 2 * l ≤ 2 * p))
  unfold covariancePolynomial
  rw [cellInner_finset_sum_left (Finset.range (p + 1))
    (fun l x => a l • ((covOperator Hc)^[l] u) x) q
    (fun l hl => continuous_const.smul (hcont u hu l hl)) hq.continuous,
    cellInner_finset_sum_right (Finset.range (p + 1)) u
    (fun l x => a l • ((covOperator Hc)^[l] q) x) hu.continuous
    (fun l hl => continuous_const.smul (hcont q hq l hl))]
  simp_rw [cellInner_smul_left, cellInner_smul_right]
  apply Finset.sum_congr rfl
  intro l hl
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  exact congrArg (fun z => a l * z) (covOperator_power_cellInner_adjoint Hc hH l u q
    (hu.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p)))
    (hq.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))) hpu hpq)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Reuse the scalar Fourier Sobolev representative theorem on finite Hilbert coordinates. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem hilbert_classicalRep_exists (K r : ℕ) (hKr : r + 2 ≤ K) (W : TorusHk K E) :
    ∃ a : Vec 2 → E, IsClassicalRep W a r := by
  classical
  have hscalar (i : Fin (Module.finrank ℝ E)) := Providers.torusHk_classicalRep_exists K r hKr
    (KernelEnergy.mapTorusHk (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)) W)
  choose a ha using hscalar
  exact ⟨fun x => ∑ i, a i x • stdOrthonormalBasis ℝ E i,
    classical_coordinate_assembly (by omega) W a ha⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A finite classical periodic Hilbert field has a genuine Sobolev carrier with the same jets. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def classicalHilbertHk (K : ℕ) (a : Vec 2 → E)
    (ha : ContDiff ℝ (K : ℕ∞) a) (hp : AVenhance.IsZ2Periodic a) : TorusHk K E :=
  ∑ i : Fin (Module.finrank ℝ E),
    KernelEnergy.mapTorusHk ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E i))
      (EntryWeakProofs.classicalFiniteHk K
        (fun x => inner ℝ (stdOrthonormalBasis ℝ E i) (a x))
        ((InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)).contDiff.comp ha)
        (fun n x => congrArg (fun y => inner ℝ (stdOrthonormalBasis ℝ E i) y) (hp n x))).toHk

theorem classicalHilbertHk_rep (K : ℕ) (a : Vec 2 → E)
    (ha : ContDiff ℝ (K : ℕ∞) a) (hp : AVenhance.IsZ2Periodic a) :
    IsClassicalRep (classicalHilbertHk K a ha hp) a K := by
  let coord (i : Fin (Module.finrank ℝ E)) := fun x => inner ℝ (stdOrthonormalBasis ℝ E i) (a x)
  have hc (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ (K : ℕ∞) (coord i) :=
    (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)).contDiff.comp ha
  have hpc (i : Fin (Module.finrank ℝ E)) : AVenhance.IsZ2Periodic (coord i) :=
    fun n x => congrArg (fun y => inner ℝ (stdOrthonormalBasis ℝ E i) y) (hp n x)
  have hr (i : Fin (Module.finrank ℝ E)) := classicalRep_map
    (EntryWeakProofs.classicalFiniteHk K (coord i) (hc i) (hpc i)).toHk (coord i)
    (classical_scalarHk_rep K (coord i) (hc i) (hpc i))
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E i))
  have hs := classicalRep_sum le_rfl _ _ hr
  have heq : (fun x => ∑ i : Fin (Module.finrank ℝ E), coord i x • stdOrthonormalBasis ℝ E i) = a := by
    funext x
    exact (stdOrthonormalBasis ℝ E).sum_repr' (a x)
  change IsClassicalRep (classicalHilbertHk K a ha hp)
    (fun x => ∑ i : Fin (Module.finrank ℝ E), coord i x • stdOrthonormalBasis ℝ E i) K at hs
  rw [heq] at hs
  exact hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The sampled horizontal maximum is at least the mean reference diffusivity. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

theorem refFlux_mean_le_horizontal_max {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν J : ℝ} (hν : 0 < ν)
    (hmax : ∀ t, ocRefFlux α q Λ ζ m ν t 0 0 ≤ J) :
    ocMeanFlux α q Λ ζ m ν ≤ J := by
  let T := 4 * ocTauPP α q Λ m
  have hT : 0 < T := mul_pos (by norm_num) (Stream.ocTauPP_pos hΛ)
  have hi := CycleReference.refFlux_entry_intervalIntegrable (α := α) (q := q) (m := m)
    hΛ hζ hν (0 : Fin 2) (0 : Fin 2) 0 T
  have hb : (∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 0 0) ≤ J * T := by
    have hb := intervalIntegral.integral_mono_on hT.le hi
      (show IntervalIntegrable (fun _ : ℝ => J) volume 0 T from intervalIntegrable_const)
      (fun t _ => hmax t)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hb
  have hm := CycleReference.refFlux_full_period_mean_entry (α := α) (q := q) (m := m)
    hΛ hζ hν (0 : Fin 2) (0 : Fin 2)
  simp only [Matrix.one_apply, ite_true, mul_one] at hm
  change T⁻¹ * (∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 0 0) = _ at hm
  rw [← hm]
  calc
    _ ≤ T⁻¹ * (J * T) := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hT).le
    _ = J := by field_simp

theorem pulseSample_normalized_long_axis_ge_one (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : b + 1 ≤ D.term)
    (s tH tV : ℝ) (lH lV : ℤ) (hsample : IsPulseSample D b s tH tV lH lV) :
    1 ≤ (Real.sqrt (D.κ b))⁻¹ * Real.sqrt
      (ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0) := by
  have hκb := CycleReference.bandChain_pos hΛ hζ hband (show b ≤ D.term by omega)
  have hκnext := CycleReference.bandChain_pos hΛ hζ hband hb
  have hmax := refFlux_mean_le_horizontal_max hΛ hζ hκnext hsample.2.1
  have hstep := hband.2 (b + 1) (by omega) hb
  simp only [Nat.add_sub_cancel] at hstep
  rw [← hstep] at hmax
  have hs := Real.sqrt_le_sqrt hmax
  have hp := Real.sqrt_pos.mpr hκb
  calc
    1 = (Real.sqrt (D.κ b))⁻¹ * Real.sqrt (D.κ b) := by rw [inv_mul_cancel₀ hp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Uniform parent flow closeness on every fixed multiple of a child quiet margin. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.FullLift

theorem uniform_parent_flow_derivative_deviation
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Ctime η : ℝ) (hCtime : 0 ≤ Ctime) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ),
    ∀ m : ℕ, m₀ ≤ m → ∀ s₀ t : ℝ,
      |t - s₀| ≤ Ctime * ocTauPP α q Λ m → ∀ x : Vec 2,
      ‖fderiv ℝ (fun y => AVRegularity.streamFlow (Φ (m - 1))
        (Velocity.streamSeq_admissible hζ hΛ hΦ (m - 1)) t y s₀) x - 1‖ ≤ η := by
  have hC : 0 ≤ 2 * 1048576 * Ctime := mul_nonneg (by norm_num) hCtime
  obtain ⟨m₀, hm₀, hprice⟩ := parent_drift_time_eventually_small
    hα₀ hα₁ hs₀ hs₁ hq hΛ (2 * 1048576 * Ctime) hC η hη
  refine ⟨m₀, hm₀, ?_⟩
  intro Φ hΦ m hm s₀ t ht x
  have hm1 : 1 ≤ m - 1 := by omega
  have he : 0 < ocEpsilon q Λ (m - 1) := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 ≤ ocA α q Λ (m - 1) := (Real.rpow_pos_of_pos he _).le
  have hcost : 2 * (1048576 * ocA α q Λ (m - 1)) * |t - s₀| ≤ η := by
    calc
      _ ≤ 2 * (1048576 * ocA α q Λ (m - 1)) *
          (Ctime * ocTauPP α q Λ m) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) ha))
      _ = (2 * 1048576 * Ctime) * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by ring
      _ ≤ η := hprice m hm
  have hsmall : (1048576 * ocA α q Λ (m - 1)) * |t - s₀| ≤ 1 := by
    linarith
  exact (actual_stream_flow_derivative_deviation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hΦ (m - 1) hm1 s₀ t hsmall x).trans hcost

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The literal scalar in the actual paired columns is at least one. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem pulseSample_long_scale_ge_one (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : b + 1 ≤ D.term)
    (s tH tV : ℝ) (lH lV : ℤ) (hsample : IsPulseSample D b s tH tV lH lV) :
    1 ≤ Real.sqrt ((D.κ b)⁻¹ *
      ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0) := by
  have hκb := CycleReference.bandChain_pos hΛ hζ hband (show b ≤ D.term by omega)
  calc
    1 ≤ (Real.sqrt (D.κ b))⁻¹ *
        Real.sqrt (ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0) :=
      pulseSample_normalized_long_axis_ge_one D b hΛ hζ hband hb s tH tV lH lV hsample
    _ = _ := by rw [Real.sqrt_mul (inv_nonneg.mpr hκb.le), Real.sqrt_inv]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The paired vertical sample has exactly the horizontal sampled long-axis size. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem refFlux_half_shift_vertical_horizontal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) :
    ocRefFlux α q Λ ζ m ν (t + 2 * ocTauPP α q Λ m) 1 1 =
      ocRefFlux α q Λ ζ m ν t 0 0 := by
  rw [CycleReference.refFlux_time_shift_two hΛ hζ ν t (ocTauPP α q Λ m) rfl]
  simp [Matrix.vecMul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    AVenhance.sigmaMat, Matrix.of_apply]
  rfl

theorem pulseSample_vertical_eq_horizontal (D : OCData) (b : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : 0 < D.κ (b + 1))
    (s tH tV : ℝ) (lH lV : ℤ) (hsample : IsPulseSample D b s tH tV lH lV) :
    ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tV 1 1 =
      ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0 := by
  rw [hsample.2.2.1]
  split_ifs
  · exact refFlux_half_shift_vertical_horizontal hΛ hζ _ _
  · have hh := CycleReference.refFlux_half_shift_00_11 (α := D.α) (q := D.q) (m := b + 1) hΛ hζ
      (t := tH - 2 * ocTauPP D.α D.q D.Λ (b + 1)) hκ
    have he : tH - 2 * ocTauPP D.α D.q D.Λ (b + 1) +
        2 * ocTauPP D.α D.q D.Λ (b + 1) = tH := sub_add_cancel _ _
    rw [he] at hh
    exact hh.symm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Every sampled renewal anchor lies within five child time scales of the quiet margin centre. -/
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem pulseSample_vertical_mem_quiet_margin (D : OCData) (b : ℕ)
    (s tH tV : ℝ) (lH lV : ℤ) (hsample : IsPulseSample D b s tH tV lH lV) :
    tV ∈ Set.Ico s (s + 4 * ocTauPP D.α D.q D.Λ (b + 1)) := by
  have ht := hsample.1
  rw [hsample.2.2.1]
  split_ifs with h
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [ht.1, ht.2]

theorem pulseSample_renewal_anchor_distance (D : OCData) (b : ℕ)
    (s tH tV : ℝ) (lH lV : ℤ) (hsample : IsPulseSample D b s tH tV lH lV) :
    |s - (lH : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)| ≤
      5 * ocTauPP D.α D.q D.Λ (b + 1) ∧
    |s - (lV : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)| ≤
      5 * ocTauPP D.α D.q D.Λ (b + 1) := by
  let h := ocTauPP D.α D.q D.Λ (b + 1)
  have hpos : 0 < h := by have ht := hsample.1; change s ≤ tH ∧ tH < s + 4 * h at ht; linarith
  have hdist (a : ℝ) (l : ℤ) (ha : a ∈ Set.Ico s (s + 4 * h))
      (hr : |a - (l : ℝ) * h| ≤ h / 2) : |s - (l : ℝ) * h| ≤ 5 * h := by
    have has : |s - a| ≤ 4 * h := abs_le.mpr ⟨by linarith [ha.2], by linarith [ha.1]⟩
    calc
      _ = |(s - a) + (a - (l : ℝ) * h)| := by congr 1; ring
      _ ≤ |s - a| + |a - (l : ℝ) * h| := abs_add_le _ _
      _ ≤ 4 * h + h / 2 := add_le_add has hr
      _ ≤ 5 * h := by linarith
  exact ⟨hdist tH lH hsample.1 hsample.2.2.2.1,
    hdist tV lV (pulseSample_vertical_mem_quiet_margin D b s tH tV lH lV hsample)
      hsample.2.2.2.2⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Literal columns of the sampled ellipse, with the scalar long-axis factor exposed. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem jacMatrix_toContinuousLinearMap (f : Vec 2 → Vec 2) (y : Vec 2) :
    (Matrix.toLin' (jacMatrix f y)).toContinuousLinearMap = fderiv ℝ f y := by
  have h : jacMatrix f y = LinearMap.toMatrix' (fderiv ℝ f y : Vec 2 →ₗ[ℝ] Vec 2) := by
    ext i j
    simp [jacMatrix, LinearMap.toMatrix'_apply, basisVec]
  rw [h, Matrix.toLin'_toMatrix']
  rfl

theorem diagSqrt_apply_basis (J : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    Matrix.toLin' (diagSqrt J) (basisVec i) = Real.sqrt (J i i) • basisVec i := by
  ext a
  fin_cases i <;> fin_cases a <;>
    simp [diagSqrt, Matrix.toLin'_apply, Matrix.mulVec, basisVec, Matrix.diagonal_apply]

theorem sampledEllipse_apply_basis (D : OCData) (b : ℕ) (s ti : ℝ) (li : ℤ) (i : Fin 2) :
    Matrix.toLin' (sampledEllipse D b s ti li) (basisVec i) =
      Real.sqrt ((D.κ b)⁻¹ * ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) ti i i) •
        fderiv ℝ (fun y => D.flowOf b s y
          ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)))
          (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)) (D.flowOf b ti 0 s) ti)
          (basisVec i) := by
  rw [sampledEllipse, Matrix.toLin'_mul_apply, diagSqrt_apply_basis, map_smul]
  have hj := jacMatrix_toContinuousLinearMap
    (fun y => D.flowOf b s y ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)))
    (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)) (D.flowOf b ti 0 s) ti)
  exact congrArg (fun L : Vec 2 →L[ℝ] Vec 2 =>
    Real.sqrt ((D.κ b)⁻¹ * ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) ti i i) •
      L (basisVec i)) hj

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Both sampled long columns have one common scalar size. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

def sampledFlowDerivative (D : OCData) (b : ℕ) (s ti : ℝ) (li : ℤ) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => D.flowOf b s y ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)))
    (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)) (D.flowOf b ti 0 s) ti)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Transport the literal sampled columns through a further spatial Jacobian. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem transported_sampledEllipse_apply_basis (D : OCData) (b : ℕ)
    (s ti : ℝ) (li : ℤ) (i : Fin 2) (f : Vec 2 → Vec 2) (y : Vec 2) :
    Matrix.toLin' (jacMatrix f y * sampledEllipse D b s ti li) (basisVec i) =
      Real.sqrt ((D.κ b)⁻¹ * ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) ti i i) •
        fderiv ℝ f y (sampledFlowDerivative D b s ti li (basisVec i)) := by
  rw [Matrix.toLin'_mul_apply, sampledEllipse_apply_basis, map_smul]
  exact congrArg (fun L : Vec 2 →L[ℝ] Vec 2 =>
    Real.sqrt ((D.κ b)⁻¹ * ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) ti i i) •
      L (sampledFlowDerivative D b s ti li (basisVec i)))
    (jacMatrix_toContinuousLinearMap f y)

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform closeness of the two actual sampled renewal derivatives. -/

theorem uniform_sampled_flow_derivative_deviation
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ b : ℕ, m₀ ≤ b + 1 → ∀ (s₀ tH tV : ℝ) (lH lV : ℤ),
      IsPulseSample D b s₀ tH tV lH lV →
      ‖sampledFlowDerivative D b s₀ tH lH - 1‖ ≤ η ∧
      ‖sampledFlowDerivative D b s₀ tV lV - 1‖ ≤ η := by
  obtain ⟨m₀, hm₀, hd⟩ := uniform_parent_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁
    hq ζ hζ Λ hΛ 5 η (by norm_num) hη hη1
  refine ⟨m₀, hm₀, ?_⟩
  intro D hDα hDq hDΛ hΦ b hb s₀ tH tV lH lV hsample
  obtain ⟨hH, hV⟩ := pulseSample_renewal_anchor_distance D b s₀ tH tV lH lV hsample
  have hget (ti : ℝ) (li : ℤ)
      (ht : |s₀ - (li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)| ≤
        5 * ocTauPP D.α D.q D.Λ (b + 1)) :
      ‖sampledFlowDerivative D b s₀ ti li - 1‖ ≤ η := by
    have ht' : |s₀ - (li : ℝ) * ocTauPP α q Λ (b + 1)| ≤
        5 * ocTauPP α q Λ (b + 1) := by simpa only [hDα, hDq, hDΛ] using ht
    have hh := hd D.Φ hΦ (b + 1) hb ((li : ℝ) * ocTauPP α q Λ (b + 1)) s₀ ht'
      (D.flowOf b ((li : ℝ) * ocTauPP D.α D.q D.Λ (b + 1)) (D.flowOf b ti 0 s₀) ti)
    rw [show b + 1 - 1 = b by omega] at hh
    simpa only [sampledFlowDerivative, OCData.flowOf, hDα, hDq, hDΛ] using hh
  exact ⟨hget tH lH hH, hget tV lV hV⟩


theorem uniform_quiet_margin_flow_derivative_deviation
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ b : ℕ, m₀ ≤ b + 1 → ∀ s₀ t : ℝ,
      |t - s₀| ≤ ocTauPP D.α D.q D.Λ (b + 1) → ∀ x : Vec 2,
      ‖fderiv ℝ (fun y => D.flowOf b t y s₀) x - 1‖ ≤ η := by
  obtain ⟨m₀, hm₀, hd⟩ := uniform_parent_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁
    hq ζ hζ Λ hΛ 1 η (by norm_num) hη hη1
  refine ⟨m₀, hm₀, ?_⟩
  intro D hDα hDq hDΛ hΦ b hb s₀ t ht x
  have ht' : |t - s₀| ≤ 1 * ocTauPP α q Λ (b + 1) := by
    simpa only [one_mul, hDα, hDq, hDΛ] using ht
  have hh := hd D.Φ hΦ (b + 1) hb s₀ t ht' x
  rw [show b + 1 - 1 = b by omega] at hh
  simpa only [OCData.flowOf] using hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The finite ambient source cap gives one scalar coefficient budget before any slot is selected. -/

open CycleComparison.Lift

def nativeLiftScalarBudget (P Q D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  1 + ∑ d : Fin (D + 1), ∑ hh : Fin (H + 1), ∑ n : Fin (N + 1),
    ambientCoefficientScalarBudget P Q d.1 H (N + d.1) N hh.1 n.1 CG Cw Cj

theorem nativeLiftScalarBudget_ge_one (P Q D H N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    1 ≤ nativeLiftScalarBudget P Q D H N CG Cw Cj := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)))

theorem ambientCoefficientScalarBudget_le_native (P Q D H N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (d hh n : ℕ) (hd : d ≤ D) (hhh : hh ≤ H) (hn : n ≤ N) :
    ambientCoefficientScalarBudget P Q d H (N + d) N hh n CG Cw Cj ≤
      nativeLiftScalarBudget P Q D H N CG Cw Cj := by
  let f : ℕ → ℕ → ℕ → ℝ := fun d hh n =>
    ambientCoefficientScalarBudget P Q d H (N + d) N hh n CG Cw Cj
  have hf (d hh n : ℕ) : 0 ≤ f d hh n :=
    ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _
  have h1 : f d hh n ≤ ∑ j : Fin (N + 1), f d hh j.1 :=
    Finset.single_le_sum (fun (j : Fin (N + 1)) _ => hf d hh j.1)
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (N + 1)))
  have h2 : (∑ j : Fin (N + 1), f d hh j.1) ≤
      ∑ i : Fin (H + 1), ∑ j : Fin (N + 1), f d i.1 j.1 :=
    Finset.single_le_sum (fun (i : Fin (H + 1)) _ =>
      Finset.sum_nonneg (fun (j : Fin (N + 1)) _ => hf d i.1 j.1))
      (Finset.mem_univ (⟨hh, by omega⟩ : Fin (H + 1)))
  have h3 : (∑ i : Fin (H + 1), ∑ j : Fin (N + 1), f d i.1 j.1) ≤
      ∑ k : Fin (D + 1), ∑ i : Fin (H + 1), ∑ j : Fin (N + 1), f k.1 i.1 j.1 :=
    Finset.single_le_sum (fun (k : Fin (D + 1)) _ =>
      Finset.sum_nonneg (fun (i : Fin (H + 1)) _ => Finset.sum_nonneg (fun (j : Fin (N + 1)) _ => hf k.1 i.1 j.1)))
      (Finset.mem_univ (⟨d, by omega⟩ : Fin (D + 1)))
  exact (h1.trans (h2.trans h3)).trans (le_add_of_nonneg_left zero_le_one)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.FullLift

/-! Retain the literal positive context witness when extracting the native complex bound. -/

open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_complex_witness_bound
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (mres : ℝ) (hm : 0 ≤ mres) (hm2 : mres ≤ 2) (L : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (f : GenSort.Sem .ctx)
    (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D bw j₀ G.level p.1 f (F p))
    (hsize : ctxSize D bw j₀ G.level F mres L ≤ ENNReal.ofReal θ)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (t : ℝ),
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) :
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1, ∀ (z : Vec 2) (Z : Fin 2 → ℂ),
      (∑ a, |(Z a).im|) < (1 + mres / 4) * (1 / 100) * D.eps (G.level - 1) →
      ‖F p ⟨G.level - 1, [p.1]⟩ 0 t
        (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))‖ ≤ θ := by
  intro t ht z Z hZ
  have ha (Y : Vec 2) : IsAdmissibleChain D bw j₀ G.level p.1
      ⟨G.level - 1, [p.1], Y, []⟩ :=
    nativeChain_isCarrier D bw j₀ G.level p.1 2 hi hj p.2 Y
  apply native_complex_context_norm_le D bw hb j₀ G.level p hε f F hF ha t ht
    mres hm hm2 L θ hθ hsize
    (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _) _ Z hZ
  intro Y
  have hp := native_context_sem_periodic G hi hj p v u γ d I c t f
    (fun ctx X w => he ctx t ht X w) Y
  have hpz : IsZ2Periodic (fun w => f t ⟨G.level - 1, [p.1], Y, []⟩ (z + w)) := by
    intro n w
    change f t ⟨G.level - 1, [p.1], Y, []⟩ (z + (w + latticeShift n)) = _
    rw [← add_assoc]
    exact hp n (z + w)
  have hper := CycleComparison.Lift.coordinate_line_periodic _ hpz (transverseIndex p.1)
  have heq (s : ℝ) : F p ⟨G.level - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a),
        (fun a => (z a : ℂ)) + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) =
      (f t ⟨G.level - 1, [p.1], Y, []⟩ (z + s • basisVec (transverseIndex p.1)) : ℂ) := by
    have hh := hF.2.2 ⟨G.level - 1, [p.1], Y, []⟩ t ht
      (z + s • basisVec (transverseIndex p.1)) (ha Y)
    change F p ⟨G.level - 1, [p.1]⟩ 0 t
      ((⟨G.level - 1, [p.1], Y, []⟩ : RealChain).paramsC
        (z + s • basisVec (transverseIndex p.1))) = _ at hh
    rw [native_paramsC_phase_line] at hh
    exact hh
  intro s
  dsimp only
  rw [heq, heq]
  exact congrArg (fun x : ℝ => (x : ℂ)) (hper s)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! The compiled kernel component-sup theorem controls the literal strong energy. -/

open AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))



include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_strongEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w) :
    strongEnergy ρ ν P.π a b u w ≤
      ENNReal.ofReal (Real.sqrt (2 * massNormSq ρ P.π (fun i => (f i).val))) := by
  have hs := P.kernelForcedWeakSolution_component_sups v hv hvp αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hsol
  rw [strongEnergy_component_integral P.diffusivity_pos.le P.π u w hsol.2.1]
  calc
    _ ≤ (ENNReal.ofReal (2 * massNormSq ρ P.π (fun i => (f i).val))) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hs.2 (by norm_num)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (by norm_num) (massNormSq_nonneg ρ P.π P.hπ _)) (by norm_num)]

end TorusKernelOperator

end AVRegularity.Construction.Preservation.FullLift
end
end
