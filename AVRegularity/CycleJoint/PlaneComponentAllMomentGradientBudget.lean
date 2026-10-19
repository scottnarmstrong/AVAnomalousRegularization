-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlanePolynomialJetMultiplierDensity
public import AVRegularity.CycleJoint.FamilyNaturalTimeRemainderReservedJets
import AVRegularity.CycleWords.CellTransverseGalerkinCorrectionLocalGrowthEnergy
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
public import AVRegularity.CycleWords.OriginalConstituentPriceReindex
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
import AVRegularity.CycleJoint.ScalarPlaneUniformMassSquaredEnergy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Every actual active native source row transfers to the common preparation chart on rough carriers, with all continuity, periodicity, and pullback bounds derived from the preparation inputs. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparation_active_piece_reference_scalar_row_transfer
    (F : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (p : (F.locally_finite t t).toFinset) (v u : ι) (γ : F.Γ v u)
    (J : ℕ) (hD : (F.identity v u γ).maxOrder ≤ J + 1) (hJ : J ≤ Jchart + 1)
    (k : Fin 2) (U : PlaneHk Set.univ J (h u)) :
    activePieceReferenceScalarRowOperator F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν e E actual p v u γ t a b n hs hT he ht p.property J k
        (mapPlaneHk (F.identity v u γ).map U) =
      ∑ i : Fin 2, planeFluxChartComponentMultiplier hφ t ((l₀ : ℝ) * ocTauPP α q Λ m) k i
        (Lp.compMeasurePreservingₗᵢ ℝ
          (fun y => streamFlow φ hφ t y ((l₀ : ℝ) * ocTauPP α q Λ m))
          (streamFlow_measurePreserving hφ t ((l₀ : ℝ) * ocTauPP α q Λ m))
          (activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he t ht p v u γ J i
            (mapPlaneHk (F.identity v u γ).map
              (preparationReferenceHkInverse hprep hcover hTau ha J hJ t ht U)))) := by
  let s := (l₀ : ℝ) * ocTauPP α q Λ m
  let hb := streamFlow_jacMatrix_bounded hφ t s
  exact planePeriodicNativeRow_reference_fiber_transfer
    ((F.piece p).material t) (streamFlowHomeomorph hφ t s)
    ((F.piece p).material_smooth t) ((F.piece p).material_symm_smooth t)
    (streamFlow_spatial_smooth hφ t s) (streamFlow_spatial_smooth hφ s t)
    (streamFlow_measurePreserving hφ t s) (streamFlow_measurePreserving hφ s t)
    (F.identity v u γ).maxOrder hD
    (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k
    (active_pieceReferenceNativeScalarJetCoefficient_continuous F hφ s ν e E actual p v u γ t
      a b n hs ht p.property J k)
    (pieceReferenceNativeScalarJetCoefficient_periodic F hφ s ν e E actual p v u γ t hT he J k)
    (active_piece_native_scalar_rows_continuous F ν e E a b n hs t ht p (actual p) v u γ J).2
    (fun i z => pieceTransportedNativeScalarJetCoefficient_periodic F ν e E actual hT he
      p v u γ t J i z)
    (fun i => chartJac_inverse_entry_continuous_slice hφ s t k i)
    (fun _ => hb.choose) (fun _ => hb.choose_spec.1)
    (fun i y => unitDet_inverse_entry_bound (chartJac hφ s t y)
      (streamFlow_jacMatrix_det_one hφ t s y) hb.choose (hb.choose_spec.2 y) k i)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x => preparation_reference_inverse_flow_jets hprep hcover hTau ha t ht
      j hj (hjJ.trans hJ) x)
    (F.identity v u γ).map U
end

/-! Every actual active native source row transfers to the common preparation chart on rough carriers, with all continuity, periodicity, and pullback bounds derived from the preparation inputs. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparation_active_piece_window_reference_scalar_row_transfer
    (F : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (p : (F.locally_finite t t).toFinset) (v u : ι) (γ : F.Γ v u)
    (J : ℕ) (hD : (F.identity v u γ).maxOrder ≤ J + 1) (hJ : J ≤ Jchart + 1)
    (k : Fin 2) (U : PlaneHk Set.univ J (h u)) :
    activePieceReferenceScalarRowOperator F hφ σ
      ν e E actual p v u γ t a b n hs hT he ht p.property J k
        (mapPlaneHk (F.identity v u γ).map U) =
      ∑ i : Fin 2, planeFluxChartComponentMultiplier hφ t σ k i
        (Lp.compMeasurePreservingₗᵢ ℝ
          (fun y => streamFlow φ hφ t y σ)
          (streamFlow_measurePreserving hφ t σ)
          (activePieceTransportedScalarRowOperator F ν e E a b n hs actual hT he t ht p v u γ J i
            (mapPlaneHk (F.identity v u γ).map
              (preparationWindowReferenceHkInverse hprep hcover σ hσ ha J hJ t ht U)))) := by
  let s := σ
  let hb := streamFlow_jacMatrix_bounded hφ t s
  exact planePeriodicNativeRow_reference_fiber_transfer
    ((F.piece p).material t) (streamFlowHomeomorph hφ t s)
    ((F.piece p).material_smooth t) ((F.piece p).material_symm_smooth t)
    (streamFlow_spatial_smooth hφ t s) (streamFlow_spatial_smooth hφ s t)
    (streamFlow_measurePreserving hφ t s) (streamFlow_measurePreserving hφ s t)
    (F.identity v u γ).maxOrder hD
    (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k
    (active_pieceReferenceNativeScalarJetCoefficient_continuous F hφ s ν e E actual p v u γ t
      a b n hs ht p.property J k)
    (pieceReferenceNativeScalarJetCoefficient_periodic F hφ s ν e E actual p v u γ t hT he J k)
    (active_piece_native_scalar_rows_continuous F ν e E a b n hs t ht p (actual p) v u γ J).2
    (fun i z => pieceTransportedNativeScalarJetCoefficient_periodic F ν e E actual hT he
      p v u γ t J i z)
    (fun i => chartJac_inverse_entry_continuous_slice hφ s t k i)
    (fun _ => hb.choose) (fun _ => hb.choose_spec.1)
    (fun i y => unitDet_inverse_entry_bound (chartJac hφ s t y)
      (streamFlow_jacMatrix_det_one hφ t s y) hb.choose (hb.choose_spec.2 y) k i)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x => preparation_window_reference_time_inverse_flow_jets hprep hcover σ hσ ha t ht
      j hj (hjJ.trans hJ) x)
    (F.identity v u γ).map U
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Physical return of native errors respects the original component masses,
directly in the polynomial energy used by the native coupled endpoint estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparationWindowReferenceCellReturn_polynomial_mass_error_le
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (n : ℕ) (ϖ : ℝ) (U V : ∀ i, PlaneHk univ (K i) (h i)) :
    ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (U i - preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha
        (K i) (hK i) e he yc t ht (V i)).val) ≤
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) * |e|) ^ 2) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (planeCarrierAffine e he yc
          (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i)) - V i) := by
  have hm := preparationWindowReferenceCellReturn_mass_error_le hc hcover σ hσ ha K hK π hπ
    hE e he yc t ht hρ hρE U V
  apply (ENNReal.ofReal_le_ofReal hm).trans
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  apply mul_le_mul' le_rfl
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (inv_nonneg.mpr (hπ i).le) (factorialNormSq_nonneg _ _))]
  apply Finset.sum_le_sum
  intro i _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (hπ i).le)]
  exact mul_le_mul' le_rfl (factorialNormSq_le_weightedFactorialNormSq n ϖ 0 (ρ / e) _)
end

/-! Returning a retained native endpoint preserves linearity before the datum is selected. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)

/-- The exact inverse chart and dilation act on each retained endpoint slot. -/
def preparationWindowReferenceRetainedEndpointLinearMap
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) :
    X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha
      (K i) (hK i) e he yc t ht).toLinearMap.comp ((LinearMap.proj i).comp T))

theorem preparationWindowReferenceRetainedEndpointLinearMap_polynomial_mass_error_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hE : 0 < ocEpsilon q Λ (m - 1))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (n : ℕ) (ϖ : ℝ)
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (ξ : X) (U : ∀ i, PlaneHk univ (K i) (h i)) :
    ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (U i - preparationWindowReferenceRetainedEndpointLinearMap hc hcover σ hσ ha
        K hK e he yc t ht T ξ i).val) ≤
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) * |e|) ^ 2) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (planeCarrierAffine e he yc
          (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i)) - T ξ i) := by
  exact preparationWindowReferenceCellReturn_polynomial_mass_error_le hc hcover σ hσ ha
    K hK π hπ hE e he yc t ht hρ hρE n ϖ U (T ξ)
end

/-! The returned operator error is controlled by the literal native curve error at the corresponding time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)

theorem preparationWindowReferenceRetainedEndpointLinearMap_native_curve_error_le
    (ν : ℝ) (hν : ν ≠ 0) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hE : 0 < ocEpsilon q Λ (m - 1))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (n : ℕ) (ϖ : ℝ)
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (ξ : X) (U : ∀ i, ℝ → PlaneHk univ (K i) (h i)) :
    ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (U i t - preparationWindowReferenceRetainedEndpointLinearMap hc hcover σ hσ ha
        K hK e he yc t ht T ξ i).val) ≤
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) * |e|) ^ 2) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha (K i) (hK i) ν e he yc
          (U i) ((e⁻¹) ^ 2 * (ν * t)) - T ξ i) := by
  have hcurve : ∀ i, preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha (K i) (hK i)
      ν e he yc (U i) ((e⁻¹) ^ 2 * (ν * t)) =
      planeCarrierAffine e he yc
        (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i t)) := by
    intro i
    exact preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover σ hσ ha
      (K i) (hK i) ν hν e he yc (U i) t
  simpa only [hcurve] using
    preparationWindowReferenceRetainedEndpointLinearMap_polynomial_mass_error_le hc hcover σ hσ ha
      K hK e he yc t ht π hπ hE hρ hρE n ϖ T ξ (fun i => U i t)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The literal metric remainder constructs a native all-moment forcing map with the first omitted degree. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance metricRemainderMomentNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance metricRemainderMomentModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

theorem exists_metricRemainder_allMoment_linearMap
    (Ks Kmax : ℕ) (M : ℕ → ℝ) (K : ℕ) (hK : K ≤ Kmax)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ)
    (hm : ∀ X k l, Measurable (fun t => G t X k l))
    (hf : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (hϖ : 0 < ϖ) (hρ : 0 < ρ) (hscale : ρ * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hg : 0 ≤ g)
    (hjet : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r →
      r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ M r * g * (ζ * ϖ) ^ r) :
    ∃ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T := by
  let μ := volume.restrict (Set.Icc a b)
  let U := fun x t => planeTimeAllMomentCarrierToLp (E := E) (K + 1) ϖ ρ 0 μ x t
  let C := fun t z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z
  obtain ⟨hadd, hsmul⟩ := planeMatrixGradientFlux_curve_superposition μ C U
    (planeTimeAllMomentCarrier_add (K + 1) ϖ ρ 0 μ)
    (planeTimeAllMomentCarrier_smul (K + 1) ϖ ρ 0 μ)
  apply exists_planeRaw_allMoment_linearMap K ϖ ρ 0 μ
    (fun x t => planeMatrixGradientFlux (C t) (U x t)) hadd hsmul
  intro x n
  obtain ⟨C0, _, hnative⟩ := metricRemainderMatrix_native_flux_exists_uniform Ks Kmax M
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift (n + (Ks + 1)) ϖ 0 ρ hρ μ (U x)
    (planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ x (n + (Ks + 1)))
  obtain ⟨V, hV, hVe, hv, _⟩ := hnative K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale
    hζ hζ1 hg hjet n (U x) (planeTimeAllMomentCarrier_memLp (K + 1) ϖ ρ 0 μ x) he
  exact ⟨V, hV, hVe, hv⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual homogeneous plane solution transfers to the actual torus fields under compact testing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem periodizedHomogeneous_compact_weakIdentity (K : ι → ℕ) (D : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (hv : ∀ s ∈ Set.Icc a b, Continuous (v s)) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hp : IsPeriodizedFamilyPair K a b u w U W)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤)
    (i : ι)
    (hc : ∀ i' d s, s ∈ Set.Icc a b → Continuous (A i i' d s))
    (hj : ∀ i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ) (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d s, s ∈ Set.Icc a b → ∀ x, ‖A i i' d s x‖ ≤ MC i' d)
    (t : ℝ) (ht : t ∈ Set.Icc a b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (φ : TorusHk 1 (h i)) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    CoupledWeakIdentity volume ν a t v
      ((U i t).toFunction.jet (valueIndex2 (K i)))
      ((U i a).toFunction.jet (valueIndex2 (K i)))
      (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun s k => (W i s).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun s => torusRawCouplingFlux K D s A (fun j => W j s) i) 0 0 := by
  dsimp only
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
  let φ0 := ψ.toFunction.jet (valueIndex2 1)
  let dφ := fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩
  let du := fun s k => (W i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let flux := fun s => torusRawCouplingFlux K D s A (fun j => W j s) i
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun s hs' => ⟨hs'.1.le, hs'.2.trans ht.2⟩
  have hμ : volume.restrict (Set.Ioc a t) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono_set volume hsub
  have hSae : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), s ∈ Set.Icc a b :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun s hs' => hsub hs')
  obtain ⟨M, hM⟩ := exists_finiteGeometry_radial_lift_budget π hπ K a b ϖ hϖ z ρ hρ u w
    hs.2.1 hs.2.2.1 he
  have hbudget := homogeneousIntegralAtoms_actual_time_transfer_of_restricted K D i
    (volume.restrict (Set.Ioc a t)) (Set.Icc a b) measurableSet_Icc hSae
    ν v hv hvm V hV hbv A hc hj MC hMC hbA (fun i' d s _ => hAp i i' d s)
    w (fun i' => MemLp.mono_measure hμ (hs.2.1 i')) z M
    (fun i' => MemLp.mono_measure hμ (hM i').1)
    (fun i' α => ae_restrict_of_ae_restrict_of_subset hsub ((hM i').2.1 α))
    (fun i' α => ae_restrict_of_ae_restrict_of_subset hsub
      ((hM i').2.2.mono (fun _ hb' => hb' α)))
    W (fun i' α => ae_restrict_of_ae_restrict_of_subset hsub
      ((periodizedFamily_lift_global_ae K a b u w U W hp i').mono (fun _ hs' => hs' α))) hζ φ
  obtain ⟨C, _, hbU, _⟩ := finite_geometry_energy_component π hπ K 4 ϖ z ρ a b u w he i
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hzero := hs.2.2.2.1 i
  have heU : weightedFactorialNormSq 4 ϖ z ρ (K i) (u i t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbU t ht)
  have heF : weightedFactorialNormSq 4 ϖ z ρ (K i) (f i) ≠ ⊤ := by
    rw [← hzero]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbU a ha)
  have hrF := periodizedFamily_trace_global_ae K a b u w U W hp i a ha (valueIndex2 (K i))
  rw [hzero] at hrF
  obtain ⟨huSeries, huReadout⟩ := polynomial_periodized_compact_pairing
    (Metric.ball (0 : Vec 2) 2) 2 (by norm_num) Set.Subset.rfl
    (u i t) (U i t) ϖ hϖ z ρ hρ heU (valueIndex2 (K i))
    (periodizedFamily_trace_global_ae K a b u w U W hp i t ht _) ψ (valueIndex2 1)
    (unitPatchLocalization_jet_ball_support_ae hζ 1 φ _)
  obtain ⟨hfSeries, hfReadout⟩ := polynomial_periodized_compact_pairing
    (Metric.ball (0 : Vec 2) 2) 2 (by norm_num) Set.Subset.rfl
    (f i) (U i a) ϖ hϖ z ρ hρ heF (valueIndex2 (K i)) hrF ψ (valueIndex2 1)
    (unitPatchLocalization_jet_ball_support_ae hζ 1 φ _)
  have hdirs (s : ℝ) (hs' : s ∈ Set.Ioc a t) :=
    torusHomogeneous_directional_pairings_integrable K D s v (hv s (hsub hs')) (hvp s)
      V hV (hbv s (hsub hs')) A i (fun i' d => hc i' d s (hsub hs'))
      MC hMC (fun i' d => hbA i' d s (hsub hs')) (fun i' d => hAp i i' d s) W hζ φ
  have hiu := (periodic_unitPatch_test_pairings_integrable
    ((U i t).toFunction.jet (valueIndex2 (K i))) (periodicJetRepresentative_memL2 (U i t).val _)
    (periodicJetRepresentative_periodic (U i t).val _) hζ φ).1
  have hif := (periodic_unitPatch_test_pairings_integrable
    ((U i a).toFunction.jet (valueIndex2 (K i))) (periodicJetRepresentative_memL2 (U i a).val _)
    (periodicJetRepresentative_periodic (U i a).val _) hζ φ).1
  have hir (s : ℝ) (hs' : s ∈ Set.Ioc a t) : Integrable
      (weakIdentityRhs ν v φ0 dφ du flux 0 0 s) volume := by
    have hd := hdirs s hs'
    have hi := (((integrable_finsetSum Finset.univ (fun k _ => hd.1 k)).neg.sub
      ((integrable_finsetSum Finset.univ (fun k _ => hd.2.1 k)).const_mul ν)).sub
      (integrable_finsetSum Finset.univ (fun k _ => hd.2.2 k)))
    apply hi.congr
    filter_upwards [] with x
    simp [weakIdentityRhs, φ0, dφ, du, flux, ψ]
    rfl
  refine coupledWeakIdentity_integral_image_assembly volume ν a t v _ _ φ0 dφ du flux 0 0
    hiu hif hir Finset.univ _ _ huSeries hfSeries huReadout hfReadout
    (fun j n => planeHomogeneousIntegralAtom K D ν v A
      (fun i s => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (w i s)) i ψ j)
    (fun j _ => (hbudget j).1) (fun j _ => (hbudget j).2.1) ?_
    (torusHomogeneousIntegralAtom K D ν v A W i ψ)
    (fun j _ => (hbudget j).2.2.1) (fun j _ => (hbudget j).2.2.2) ?_
  · intro n
    exact planeHomogeneous_image_integral_atom_equation K D ν a b v hvp A hAp f u w hs i t ht ψ
      (fun s hs' => hv s (hsub hs'))
      (fun s hs' => ⟨V, hV, hbv s (hsub hs')⟩)
      (fun s hs' i' d => hc i' d s (hsub hs')) (fun _ => MC)
      (fun _ _ => hMC) (fun s hs' i' d => hbA i' d s (hsub hs')) n
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
    have hd := hdirs s hs'
    exact homogeneousWeakRhs_integral_readout volume ν s v φ0 dφ du flux hd.1 hd.2.1 hd.2.2

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual metric remainder maps retain their uniform omitted-degree smallness and moment cost. -/

theorem metricRemainder_allMoment_linearMap_budget_uniform (Ks Kmax : ℕ) (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r →
        r ≤ Ks + 1 + Kmax → ∀ y k l,
          ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      ∀ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
          (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T →
      ∀ x n,
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K
          (planeTimeAllMomentCarrierToLp K ϖ ρ 0 (volume.restrict (Set.Icc a b)) (T x) t)) ≤
        ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ ^ (Ks + 1))) ^ 2) *
          ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 ρ K
            (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) x t) := by
  obtain ⟨C, hC, hnative⟩ := metricRemainderMatrix_native_flux_exists_uniform Ks Kmax M
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet T hT x n
  let μ := volume.restrict (Set.Icc a b)
  let U := fun t => planeTimeAllMomentCarrierToLp (E := E) (K + 1) ϖ ρ 0 μ x t
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift (Ks + 1) ϖ 0 ρ hρ μ U
    (planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ x (Ks + 1))
  obtain ⟨V, _, _, hv, hdens⟩ := hnative K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale
    hζ hζ1 hg hjet 0 U (planeTimeAllMomentCarrier_memLp (K + 1) ϖ ρ 0 μ x) (by simpa using he)
  have hrep := planeRaw_allMoment_map_represents K ϖ ρ 0 μ _ T hT x V hv
  have hi := lintegral_congr_ae (hrep.fun_comp (fun Q => weightedFactorialNormSq n ϖ 0 ρ K Q))
  simp only [Function.comp_apply] at hi
  rw [hi]
  exact nativeFlux_time_moment_shift_budget n (Ks + 1) ϖ ρ
    (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ ^ (Ks + 1))) μ V U hdens

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The central metric, its positive Taylor polynomial, and its genuine
remainder are constructed together on the native all-moment domain. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_metricTaylor_remainder_allMoment_maps
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r)
    (K : ℕ) (hK : K ≤ Kmax)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ)
    (hm : ∀ X k l, Measurable (fun t => G t X k l))
    (hf : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (hϖ : 0 < ϖ) (hρ : 0 < ρ) (hscale : ρ * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (G t 0).IsSymm)
    (hnear : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (G t 0 - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2)
    (hlow : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * g * (ζ * ϖ) ^ r)
    (hhigh : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r →
      r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * g * (ζ * ϖ) ^ r) :
    ∃ diag T Rm : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) diag ∧
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T ∧
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) Rm := by
  obtain ⟨diag, hdiag⟩ := exists_planeCentralMetric_allMoment_map (E := E) K a b ϖ ρ hϖ hρ
    (fun t => G t 0) (hm 0) g hg hsym hnear
  obtain ⟨T, hT⟩ := exists_metricTaylor_allMoment_linearMap (E := E) Ks Kmax Cjet hCjet K hK
    G a b ϖ ρ (ζ * ϖ) ζ g hm
    (fun t ht k l => (hf t ht k l).of_le (by exact_mod_cast (show Ks ≤ Ks + 1 + Kmax by omega)))
    hϖ hρ hscale hζ hζ1 hg rfl hlow
  obtain ⟨Rm, hRm⟩ := exists_metricRemainder_allMoment_linearMap (E := E) Ks Kmax Cjet K hK
    G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hhigh
  exact ⟨diag, T, Rm, hdiag, hT, hRm⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Pointwise molecular prices retain the original identities in the source
remainder Schur sum. The only repeated coordinate count is two. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def pointwiseOriginalRemainderPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (v u : ι)
    (α : OriginalSourceIndex F v u) : ℝ :=
  (Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1)) *
    (E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (α.2.1.1 - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u α.1 α.2.1.1 α.2.2.1))) *
    ‖(F.identity v u α.1).map‖

theorem pointwiseOriginalRemainderPrice_nonneg (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR ζ : ℝ)
    (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ)
    (v u : ι) (α : OriginalSourceIndex F v u) :
    0 ≤ pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α := by
  unfold pointwiseOriginalRemainderPrice
  have hM := molecularRealPrice_nonneg ν ρ hν hρ (K v) (α.2.1.1 - 2)
    (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u α.1 α.2.1.1 α.2.2.1))
  positivity

theorem pointwiseOriginalRemainderPrice_sum_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ CR ζ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ) (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (hKs : Ks + 1 ≤ J) (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) :
    Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u,
        pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α) ≤
      (2 * Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 *
        ζ ^ (Ks + 1) * |C (Ks + 1)|) * b v u := by
  classical
  let q := fun (γ : F.Γ v u) d (I : DerivativeWord2 (d - 1)) =>
    E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let A := Real.sqrt (multiplicationDensityBudget (K v)) * CR *
    (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1)
  have hA : 0 ≤ 2 * A := by dsimp only [A]; positivity
  have hs := originalConstituent_price_sum_eq F v u q A
  have hh := mul_le_mul_of_nonneg_left
    (pointwiseMolecularRealEnvelope_scaled_sum_le F π K dom ν e E ρ hν hE hρ C J b henv
      v u hb (Ks + 1) hKs) hA
  change Real.sqrt (π u / π v) *
    (∑ α : OriginalSourceIndex F v u, A * q α.1 α.2.1.1 α.2.2.1 * ‖(F.identity v u α.1).map‖) ≤ _
  rw [hs]
  convert hh using 1 <;> dsimp only [A, q] <;> ring
end

/-! Identity prices retain the original molecular sum before assembling edges. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def pointwiseOriginalIdentityRemainderPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (v u : ι) (γ : F.Γ v u) : ℝ :=
  (Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1)) *
    (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))) * ‖(F.identity v u γ).map‖

theorem pointwiseOriginalIdentityRemainderPrice_nonneg (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR ζ : ℝ)
    (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ)
    (v u : ι) (γ : F.Γ v u) :
    0 ≤ pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u γ := by
  unfold pointwiseOriginalIdentityRemainderPrice
  apply mul_nonneg _ (norm_nonneg _)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro d _
  apply Finset.sum_nonneg
  intro I _
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (pow_nonneg hE _) (molecularRealPrice_nonneg ν ρ hν hρ _ _ _)

theorem pointwiseOriginalIdentityRemainderPrice_sum_eq (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (v u : ι) :
    (∑ γ : F.Γ v u, pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u γ) =
    ∑ α : OriginalSourceIndex F v u, pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α := by
  classical
  let q := fun (γ : F.Γ v u) d (I : DerivativeWord2 (d - 1)) =>
    E ^ (Ks + 1) * molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let A := Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1)
  change _ = ∑ α : OriginalSourceIndex F v u, A * q α.1 α.2.1.1 α.2.2.1 * ‖(F.identity v u α.1).map‖
  rw [originalConstituent_price_sum_eq F v u q A, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  change A * (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, q γ d I) * ‖(F.identity v u γ).map‖ = _
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  ring
end

/-! The original Taylor graph estimate preserves an arbitrary supplied mass row and column bound, including zero. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def pointwiseOriginalRemainderGraphConstant (Ks Kmax : ℕ) (CR : ℝ) (C : ℕ → ℝ) : ℝ :=
  2 * (∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N)) *
    |CR| * (Kmax.factorial : ℝ) ^ 2 * |C (Ks + 1)|

theorem pointwiseOriginalRemainderGraphConstant_nonneg (Ks Kmax : ℕ) (CR : ℝ) (C : ℕ → ℝ) :
    0 ≤ pointwiseOriginalRemainderGraphConstant Ks Kmax CR C := by
  unfold pointwiseOriginalRemainderGraphConstant
  positivity

theorem pointwiseOriginalRemainderPrice_graph_budget_with_mass (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks + 1 ≤ J)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (θ : ℝ) (hrow : ∀ v, ∑ u, b v u ≤ θ)
    (hcol : ∀ u, ∑ v, b v u ≤ θ) :
    (∀ v, ∑ u, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α) ≤
        ζ ^ (Ks + 1) * (pointwiseOriginalRemainderGraphConstant Ks Kmax CR C * θ)) ∧
    (∀ u, ∑ v, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α) ≤
        ζ ^ (Ks + 1) * (pointwiseOriginalRemainderGraphConstant Ks Kmax CR C * θ)) := by
  classical
  have hv (v : ι) : Real.sqrt (multiplicationDensityBudget (K v)) ≤
      ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N) :=
    Finset.single_le_sum (fun N _ => Real.sqrt_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK v)))
  have hpoint (v u : ι) : Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u,
        pointwiseOriginalRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u α) ≤
        ζ ^ (Ks + 1) * pointwiseOriginalRemainderGraphConstant Ks Kmax CR C * b v u := by
    have hh := pointwiseOriginalRemainderPrice_sum_envelope_le F π K Ks Kmax dom ν e E ρ CR ζ
      hν hE hρ hCR hζ C J b hKs henv v u (hb v u)
    have hc := mul_le_mul_of_nonneg_left (hv v)
      (by positivity : 0 ≤ 2 * CR * (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1) * |C (Ks + 1)|)
    have hc' : 2 * Real.sqrt (multiplicationDensityBudget (K v)) * CR *
        (Kmax.factorial : ℝ) ^ 2 * ζ ^ (Ks + 1) * |C (Ks + 1)| ≤
        ζ ^ (Ks + 1) * pointwiseOriginalRemainderGraphConstant Ks Kmax CR C := by
      simpa only [pointwiseOriginalRemainderGraphConstant, abs_of_nonneg hCR,
        mul_assoc, mul_comm, mul_left_comm] using hc
    exact hh.trans (mul_le_mul_of_nonneg_right hc' (hb v u))
  constructor
  · intro v
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    have hmono := mul_le_mul_of_nonneg_left (hrow v)
      (mul_nonneg (pow_nonneg hζ (Ks + 1)) (pointwiseOriginalRemainderGraphConstant_nonneg Ks Kmax CR C))
    exact hh.trans (by simpa only [mul_assoc] using hmono)
  · intro u
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    have hmono := mul_le_mul_of_nonneg_left (hcol u)
      (mul_nonneg (pow_nonneg hζ (Ks + 1)) (pointwiseOriginalRemainderGraphConstant_nonneg Ks Kmax CR C))
    exact hh.trans (by simpa only [mul_assoc] using hmono)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual metric remainder maps obey the original family mass bound with the first omitted-degree gain. -/

theorem metricRemainder_family_map_mass_moment_budget_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)],
      ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) →
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      ∀ (π : ι → ℝ)
        (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
            (volume.restrict (Set.Icc a b))),
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) (T i)) →
      ∀ (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b))) (n : ℕ),
      planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
        K n ϖ ρ (volume.restrict (Set.Icc a b)) π (fun i => T i (W i)) ≤
        ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (C * g * ζ ^ (Ks + 1)) ^ 2) *
          planeAllMomentFamilyGradientEnergy (E := E) K (n + (Ks + 1)) ϖ ρ
            (volume.restrict (Set.Icc a b)) π W := by
  obtain ⟨C, hC, hb⟩ := metricRemainder_allMoment_linearMap_budget_uniform Ks Kmax M
  refine ⟨C, hC, ?_⟩
  intro ι _ E _ _ _ _ _ _ K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet π T hT W n
  let μ := volume.restrict (Set.Icc a b)
  let F := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := PiLp 2 (fun _ : Fin 2 => E i))
      (K i) ϖ ρ 0 μ (T i (W i)) t)
  let Q := fun i t => weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t)
  have hF (i : ι) : AEMeasurable (F i) μ :=
    AVRegularity.Weighted.weightedFactorialNormSq_time_aemeasurable
      (E := PiLp 2 (fun _ : Fin 2 => E i)) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := PiLp 2 (fun _ : Fin 2 => E i))
        (K i) ϖ ρ 0 μ (T i (W i)))
  have hQ (i : ι) : AEMeasurable (Q i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) (n + (Ks + 1)) ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  apply finite_mass_time_integral_budget μ (fun i => ENNReal.ofReal ((π i)⁻¹))
    F Q _ hF hQ
  intro i
  have hi := hb (K i) (hK i) G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet
    (T i) (hT i) (W i) n
  exact hi.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (metricTaylor_density_price_le (K i) Kmax (hK i) (C * g * ζ ^ (Ks + 1)))) zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Fixed order counts are absorbed into the chart price before original
identity sums, preserving the molecular graph weights. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseOriginalIdentityRemainderPrice_mul_chart_price
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ CR ζ a : ℝ) (v u : ι) (γ : F.Γ v u) :
    pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ (a * CR) ζ v u γ =
      a * pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u γ := by
  unfold pointwiseOriginalIdentityRemainderPrice
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Localized torus data give every polynomial moment of the actual transformed
initial datum for the first preparation block. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCell_localized_initial_moments
    (hab : a ≤ b) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → ℤ) (f : TorusHk J E)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (n : ℕ) (ϖ ρ : ℝ) :
    weightedFactorialNormSq n ϖ 0 (ρ / e) J
      (planeCarrierAffine e he yc
        (preparationReferenceHkWindowPull hc hcover hTau ha J hJ a
          (spatialPatchLocalization hζ N hN j J f))) ≠ ⊤ := by
  rw [weightedFactorialNormSq_affine_centered]
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
  exact planeHkSmoothPullback_polynomial_energy_ne_top_of_compact_support
    _ _ _ _ _ _ _ _ (spatialPatchCutoff_compact hζ N hN j)
    (spatialPatchLocalization_jet_support_ae hζ N hN j J f) n (ϖ / e) yc ρ

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Quantitative initial polynomial energy in the actual preparation reference
chart, with the center chosen as the inverse image of the physical patch center. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem preparationReference_localized_energy_le
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1) (t : ℝ) (ht : t ∈ Icc a b)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (f : TorusHk J E)
    (n : ℕ) (ϖ R ρ : ℝ) (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R)
    (hmesh : ϖ / (N : ℝ) ≤ R) (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) :
    weightedFactorialNormSq n ϖ
      (streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (spatialPatchCenter N k) t)
      ρ J (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t
        (spatialPatchLocalization hζ N hN k J f)) ≤
      ENNReal.ofReal ((1 + 2 * (preparationPieceFlowJetBudget Cchart
        (ocEpsilon q Λ (m - 1)) 1 * R) ^ 2) ^ n) *
      ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart) J) ^ 2) *
      ENNReal.ofReal (factorialNormSq ρ (spatialPatchLocalization hζ N hN k J f).val) := by
  let B := preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1))
  let L : NNReal := ⟨B 1, abs_nonneg _⟩
  let X := streamFlowHomeomorph hφ t ((l₀ : ℝ) * ocTauPP α q Λ m)
  have hL : LipschitzWith L X.symm := by
    apply lipschitzWith_of_first_jet_bound _
      ((streamFlow_spatial_smooth hφ ((l₀ : ℝ) * ocTauPP α q Λ m) t).differentiable (by norm_num)) L
    intro x
    exact preparation_reference_inverse_flow_jets hc hcover hTau ha t ht 1
      (le_refl 1) (Nat.succ_le_succ (Nat.zero_le Jchart)) x
  have hscale j (_ : 1 ≤ j) (_ : j ≤ J) :
      ρ ^ (j - 1) * B j ≤ preparationFlowJetConstant Cchart j := by
    dsimp only [B, preparationPieceFlowJetBudget]
    rw [abs_of_nonneg (mul_nonneg (preparationFlowJetConstant_nonneg Cchart j)
      (pow_nonneg (inv_nonneg.mpr hE.le) _))]
    exact preparation_scaled_flow_budget hE hρ hρE Cchart j
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact spatialPatch_scaled_pullback_energy_le X (streamFlow_spatial_smooth hφ t _)
    (streamFlow_measurePreserving hφ t _) B (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x => preparation_reference_flow_jets hc hcover hTau ha t ht j hj
      (hjJ.trans hJ) x) hρ (preparationFlowJetConstant Cchart) hscale hζ N hN k f
    L hL n ϖ R hϖ hR hmesh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Genuine frozen-metric component response maps satisfy the scalar polynomial gradient budget
on their native representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance componentBudgetFluxNormed : NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E)) :=
  componentCertificateFluxNormed
local instance componentBudgetFluxInner : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E)) :=
  componentCertificateFluxInner

theorem planeComponentAllMomentResponse_gradient_budget
    (a b : ℝ) (hab : a ≤ b) (K Kmax : ℕ) (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (hm : m ≤ N)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (R : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (hR : IsPlaneComponentAllMomentResponse M v K a b ϖ ρ R)
    (x : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
      (volume.restrict (Icc a b))) :
    (∫⁻ t in Icc a b, weightedGradFactorialNormSq m ϖ 0 ρ K
      (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 (volume.restrict (Icc a b)) (R x) t)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (16 * ∫⁻ t in Icc a b, weightedFactorialNormSq m ϖ 0 ρ K
          (planeTimeAllMomentCarrierToLp K ϖ ρ 0 (volume.restrict (Icc a b)) x t)) := by
  obtain ⟨F, u, w, hs, hinput, houtput⟩ := hR x
  have hF : MemLp F 2 (volume.restrict (Icc a b)) :=
    (planeTimeAllMomentCarrier_memLp K ϖ ρ 0 (volume.restrict (Icc a b)) x).ae_eq hinput
  have he := frozenMetricScalar_polynomial_factorial_supremum (h := fun _ : Unit => E)
    a b hab (fun _ _ => K) Kmax (fun _ => hK) v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym (fun _ => 0) (fun _ => F) (fun _ => hF)
    (fun p => u p.2) (fun p => w p.2) hs (0, Unit.unit)
    t₀ S ϖ 0 N m Cw C hm ρ L hρ hL hsmall hstrainSmall hreserve hdiv hwa hwb
  have hi := lintegral_congr_ae (hinput.fun_comp
    (fun Q => weightedFactorialNormSq m ϖ 0 ρ K Q))
  have ho := lintegral_congr_ae (houtput.fun_comp
    (fun Q => weightedGradFactorialNormSq m ϖ 0 ρ K Q))
  simp only [Function.comp_apply] at hi ho
  simp only [weightedFactorialNormSq_zero_carrier, zero_add] at he
  rw [← hi] at he
  rw [ho]
  exact (le_add_self : _ ≤ _ + _).trans he

end AVRegularity.CycleJointProofs
end
end
