-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneHomogeneousMaterialWeakCurve
public import AVRegularity.CycleJoint.PlaneForcedZeroInitialEndpointEnergy
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CycleJoint.OriginalFamilyNaturalRemainderDescendingIdentity
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVenhance.Infra.Classical.Drift

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The constructed finite response approximates the genuine homogeneous coupled preparation with the three original-mass residual budgets. -/

theorem planeRetained_constructed_error_endpoint_energy.{u, v}
    (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ (0 : Vec 2) n Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (_hr1 : rstar ≤ 1)
        (V₀ : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
        (_hf : ∀ i, weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (V₀ i) ≠ ⊤)
        (uH : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (wH : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (_hH : IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) V₀ (fun _ _ => 0) (fun _ _ => 0) uH wH)
        (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb)))
        (u0 : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (w0 : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)))
    (_hdiagA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1) i j d) ≠ ⊤)
    (_hfullA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb (planeMetricSourceCoefficient Kslot D G A i j d) ≠ ⊤)
    (_hdiagC : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1) i j d t))
    (_hfullC : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (planeMetricSourceCoefficient Kslot D G A i j d t))
    {P : Type*} {Ctx : P → Type*}
    (family : ChartedFamily ι h D P Ctx)
    (J : ℕ) (_hdepth : family.HasDepthAtMost H)
    (_hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (Kslot i) ta tb ϖ rstar (R i))
    (_hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ i) (fun _ _ _ => 0) (fun _ i => u0 i) (fun _ i => w0 i))
    (_hZ : ∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb))
      (Z i) (w0 i))
    (Lfull Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)))
    (_hfull : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t (planeMetricSourceCoefficient Kslot D G A)
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Lfull i))
    (_hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t
        (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Ldiag i))
        (Rm Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (_hsplit : ∀ i, Lfull i = Ldiag i + (Lmetric i).comp (LinearMap.proj i) +
          nativeFamilyEdgeForcingMap Ledge i + Rm i + Rs i),
        let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
        let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
        let Tret := ∑ k ∈ Finset.range (H + 1), U J k
        let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
        ∀ Bm Bs Bt : ℝ≥0∞,
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rm i Wret) ≤ Bm →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i Wret) ≤ Bs →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Lmetric i (Tret i)) ≤ Bt →
        ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
          (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i)),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0)
            (fun i t => -(F i t - planeCouplingFluxRow _ht rstar _hrstar Kslot D
              (planeMetricSourceCoefficient Kslot D G A) _hfullA _hfullC w i t +
              planeCouplingFluxRow _ht rstar _hrstar Kslot D
                (planeDiagonalGradientCoefficient Kslot D (fun _ t _ => M t - 1)) _hdiagA _hdiagC w i t))
            (fun _ _ => 0) (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Q i) (F i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret i) (w i)) ∧
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH i tp - u i tp)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) * (Bm + Bs + Bt)) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth hS hR hbase hZ Lfull Ldiag hfull hdiag Rm Rs hsplit
  dsimp only
  let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
    (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
  let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
  let Tret := ∑ k ∈ Finset.range (H + 1), U J k
  let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
  intro Bm Bs Bt hm hs ht'
  obtain ⟨F, u, w, herror, hr, hrep⟩ :=
    planeComponentAllMomentResponse_retained_native_error_solution M v Kslot ta tb ϖ rstar R
      Lmetric Ledge V₀ u0 w0 Z ht hrstar hD (planeMetricSourceCoefficient Kslot D G A)
      hdiagA hfullA hdiagC hfullC family H J hdepth hS hR hbase hZ
      Lfull Ldiag hfull hdiag uH wH hH
  let X := fun i => -(Q i - Lfull i Wret + Ldiag i Wret)
  let ferr := fun i t => -(F i t - planeCouplingFluxRow ht rstar hrstar Kslot D
    (planeMetricSourceCoefficient Kslot D G A) hfullA hfullC w i t +
    planeCouplingFluxRow ht rstar hrstar Kslot D
      (planeDiagonalGradientCoefficient Kslot D (fun _ t _ => M t - 1)) hdiagA hdiagC w i t)
  have hb := planeRetained_error_endpoint_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf
    uH u wH w hH X ferr hrep Wret (fun i => (hr i).2) herror
  have hres := planeAllMoment_native_residual_energy_budget Kslot n ϖ rstar
    (volume.restrict (Set.Icc ta tb)) π Lfull Ldiag
    (fun i => (Lmetric i).comp (LinearMap.proj i)) (nativeFamilyEdgeForcingMap Ledge)
    Rm Rs hsplit Wret Tret Bm Bs Bt hm hs ht'
  change planeAllMomentFamilyEnergy Kslot n ϖ rstar
    (volume.restrict (Set.Icc ta tb)) π X ≤ 4 * (Bm + Bs + Bt) at hres
  refine ⟨F, u, w, herror, (fun i => (hr i).1), (fun i => (hr i).2), ?_⟩
  intro tp htp
  apply (hb tp htp).trans
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hres (show (0 : ℝ≥0∞) ≤ 64 *
      ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) from zero_le))
    (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) from zero_le)
  apply hm.trans_eq
  ring

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual preparation inputs construct the complete native source map on
any normalized subwindow, without a separately assumed sampled envelope. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CoupledEnergyPlane.Variational

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSource_allMoment_map_of_pointwise
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (K : ι → ℕ) (Kmax Jm : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (u0 u1 ϖ r : ℝ) (hu : u0 ≤ u1) (hr : 0 < r)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    ∃ T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ r 0
      (volume.restrict (Set.Icc u0 u1))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ r 0
        (volume.restrict (Set.Icc u0 u1)),
      ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ r 0 (volume.restrict (Set.Icc u0 u1))
        (fun W t => planeRawCouplingFlux K D t
          (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
            ν e (ocEpsilon q Λ (m - 1)) actual K yc)
          (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ r 0
            (volume.restrict (Set.Icc u0 u1)) (W j) t) i) (T i) := by
  obtain ⟨Cprep, _, hsamp⟩ := preparation_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsample := hsamp α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv
  have hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (henv.1 p c v u γ d I tY htY z).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have he : 0 < e := hρ.trans_le hρe
  have hE : 0 < ocEpsilon q Λ (m - 1) := he.trans_le heE
  exact preparationReferenceCellSource_allMoment_map F hc ν e (ocEpsilon q Λ (m - 1)) hν
    he.ne' hE.ne' K hs hmeas hwmeas actual ((l₀ : ℝ) * ocTauPP α q Λ m) yc
    π hπ ρ r Cprep hρ hr B hsample u0 u1 ϖ hu hsub

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual preparation inputs construct the complete native source map on
any normalized subwindow, without a separately assumed sampled envelope. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CoupledEnergyPlane.Variational

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem preparationReferenceCellSource_pointwise_subwindow_data
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (K : ι → ℕ) (Kmax Jm : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (u0 u1 r : ℝ)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    let A := preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    (∀ v u d, coefficientSeminorm r (K v) u0 u1 (A v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc u0 u1 → ContDiff ℝ (K v : ℕ) (A v u d t)) ∧
    (∀ v u d, Measurable (fun p : Set.Icc u0 u1 × Vec 2 => A v u d p.1 p.2)) ∧
    (∀ v u, ¬ Nonempty (F.Γ v u) → ∀ d t z, t ∈ Set.Icc u0 u1 → A v u d t z = 0) := by
  obtain ⟨Cprep, _, hsamp⟩ := preparation_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsample := hsamp α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv
  have hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (henv.1 p c v u γ d I tY htY z).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have he : 0 < e := hρ.trans_le hρe
  exact preparationReferenceCellSourceCoefficient_subwindow_data F hc ν e (ocEpsilon q Λ (m - 1))
    hν he.ne' (he.trans_le heE).ne' K hs hmeas hwmeas actual
    ((l₀ : ℝ) * ocTauPP α q Λ m) yc π hπ ρ r Cprep hρ B hsample u0 u1 hsub

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual frozen-metric response solutions preserve the moments needed for subsequent Taylor forcing. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_frozenMetricScalarChain_with_polynomial_reserve (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))

    (hnear : IsMetricNearIdentity (fun t _ => M t) εg)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ zc N Cw) 
    (L : ℕ → ℝ) (hL : ∀ m ≤ N, 1 ≤ L m) (hρ1 : ρ ≤ 1)
    (hreserve : ∀ m ≤ N, Real.exp (18 * Cw m) / (L m) ^ 2 ≤ 1 / 16)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (hf : ∀ m ≤ N, ∀ i, weightedFactorialNormSq m ϖ zc ρ (K i) (f i) ≠ ⊤)
    (hFe : ∀ m ≤ N, ∀ i, (∫⁻ s in Set.Icc a b,
      weightedFactorialNormSq m ϖ zc ρ (K i) (F i s)) ≠ ⊤)
 :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ m ≤ N, ∀ i,
        ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq m ϖ zc ρ (K i) (u i t)) +
          ∫⁻ s in Set.Icc a b, weightedGradFactorialNormSq m ϖ zc ρ (K i) (w i s)) ≠ ⊤ ∧
        (∫⁻ s in Set.Icc a b,
        weightedFactorialNormSq m ϖ zc ρ (K i + 1) (w i s)) ≠ ⊤ := by
  obtain ⟨u, w, hs⟩ := exists_frozenMetricScalarChain K Kmax hK ρ strain B lam hρ hstrain0
    hB hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets M hM εg hεg hεgsmall hsym hquad
    F hF f hvm
  refine ⟨u, w, hs, ?_⟩
  intro m hm i
  refine ⟨?_, ?_⟩
  · exact frozenMetricScalar_weighted_value_gradient_energy_ne_top a b hab (fun _ => K) Kmax
      (fun p => hK p.2) v hvm hv V strain B lam hV hstrain0 hB hlam hbv hjets
      M hM εg hεg (by linarith) hnear hsym
      (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
      (fun p => u p.2) (fun p => w p.2) hs (0, i)
      t₀ S ϖ zc N m Cw C hm ρ (L m) hρ (hL m hm) hsmall hstrain (hreserve m hm) hdiv hwa hwb
      (hf m hm i) (hFe m hm i)
  · exact frozenMetricScalar_weighted_lift_time_energy_ne_top a b hab (fun _ => K) Kmax
      (fun p => hK p.2) v hvm hv V strain B lam hV hstrain0 hB hlam hbv hjets
      M hM εg hεg (by linarith) hnear hsym
      (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
      (fun p => u p.2) (fun p => w p.2) hs (0, i)
      t₀ S ϖ zc N m Cw C hm ρ (L m) hρ (hL m hm) hsmall hstrain (hreserve m hm) hdiv hwa hwb hρ1
      (hf m hm i) (hFe m hm i)
end

/-! Every actual frozen scalar response propagates the supplied polynomial moment reserve using only native-window metric bounds. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem frozenMetricScalarChain_on_window_polynomial_reserve (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))

    (ϖ : ℝ) (zc : Vec 2) (N : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v a (b - a) ϖ zc N Cw) 
    (L : ℕ → ℝ) (hL : ∀ m ≤ N, 1 ≤ L m) (hρ1 : ρ ≤ 1)
    (hreserve : ∀ m ≤ N, Real.exp (18 * Cw m) / (L m) ^ 2 ≤ 1 / 16)
    (hf : ∀ m ≤ N, ∀ i, weightedFactorialNormSq m ϖ zc ρ (K i) (f i) ≠ ⊤)
    (hFe : ∀ m ≤ N, ∀ i, (∫⁻ s in Set.Icc a b,
      weightedFactorialNormSq m ϖ zc ρ (K i) (F i s)) ≠ ⊤)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i)) :
      ∀ m ≤ N, ∀ i,
        ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq m ϖ zc ρ (K i) (u i t)) +
          ∫⁻ s in Set.Icc a b, weightedGradFactorialNormSq m ϖ zc ρ (K i) (w i s)) ≠ ⊤ ∧
        (∫⁻ s in Set.Icc a b,
        weightedFactorialNormSq m ϖ zc ρ (K i + 1) (w i s)) ≠ ⊤ := by
  let Mc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => M (max a (min t b))
  have hMc : Measurable Mc := matrix_time_clamp_measurable hM a b
  have hnear : IsMetricNearIdentity (fun t _ => Mc t) εg :=
    fun t _ ξ => hquad _ (clampTime_mem hab t) ξ
  have hsymc : ∀ t ∈ Set.Icc a b, (Mc t).IsSymm :=
    fun t _ => hsym _ (clampTime_mem hab t)
  have hCc : ChartWeights (fun t _ => Mc t) v a (b - a) ϖ zc N Cw :=
    chartWeightsMetricClamp C
  have hsc : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => Mc t))
      (fun _ i => K i) a b v (fun _ i => f i) (fun _ i => F i)
      (fun _ i => u i) (fun _ i => w i) := by
    apply isPlaneChainFrom_geometryScalarData_congr _ hs
    intro t ht
    exact metricClamp_of_mem (fun t _ => M t) ht
  intro m hm i
  refine ⟨?_, ?_⟩
  · exact frozenMetricScalar_weighted_value_gradient_energy_ne_top a b hab (fun _ => K) Kmax
      (fun p => hK p.2) v hvm hv V strain B lam hV hstrain0 hB hlam hbv hjets
      Mc hMc εg hεg (by linarith) hnear hsymc
      (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
      (fun p => u p.2) (fun p => w p.2) hsc (0, i)
      a (b - a) ϖ zc N m Cw hCc hm ρ (L m) hρ (hL m hm) hsmall hstrain
      (hreserve m hm) hdiv (le_refl a) (by rw [add_sub_cancel]) (hf m hm i) (hFe m hm i)
  · exact frozenMetricScalar_weighted_lift_time_energy_ne_top a b hab (fun _ => K) Kmax
      (fun p => hK p.2) v hvm hv V strain B lam hV hstrain0 hB hlam hbv hjets
      Mc hMc εg hεg (by linarith) hnear hsymc
      (fun p => f p.2) (fun p => F p.2) (fun p => hF p.2)
      (fun p => u p.2) (fun p => w p.2) hsc (0, i)
      a (b - a) ϖ zc N m Cw hCc hm ρ (L m) hρ (hL m hm) hsmall hstrain
      (hreserve m hm) hdiv (le_refl a) (by rw [add_sub_cancel]) hρ1
      (hf m hm i) (hFe m hm i)
end

/-! Frozen response existence uses only the native window metric bound and retains every polynomial moment. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_frozenMetricScalarChain_on_window_with_polynomial_reserve (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))

    (ϖ : ℝ) (zc : Vec 2) (N : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v a (b - a) ϖ zc N Cw) 
    (L : ℕ → ℝ) (hL : ∀ m ≤ N, 1 ≤ L m) (hρ1 : ρ ≤ 1)
    (hreserve : ∀ m ≤ N, Real.exp (18 * Cw m) / (L m) ^ 2 ≤ 1 / 16)
    (hf : ∀ m ≤ N, ∀ i, weightedFactorialNormSq m ϖ zc ρ (K i) (f i) ≠ ⊤)
    (hFe : ∀ m ≤ N, ∀ i, (∫⁻ s in Set.Icc a b,
      weightedFactorialNormSq m ϖ zc ρ (K i) (F i s)) ≠ ⊤)
 :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
      ∀ m ≤ N, ∀ i,
        ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq m ϖ zc ρ (K i) (u i t)) +
          ∫⁻ s in Set.Icc a b, weightedGradFactorialNormSq m ϖ zc ρ (K i) (w i s)) ≠ ⊤ ∧
        (∫⁻ s in Set.Icc a b,
        weightedFactorialNormSq m ϖ zc ρ (K i + 1) (w i s)) ≠ ⊤ := by
  let Mc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t => M (max a (min t b))
  have hMc : Measurable Mc := matrix_time_clamp_measurable hM a b
  have hnear : IsMetricNearIdentity (fun t _ => Mc t) εg :=
    fun t _ ξ => hquad _ (clampTime_mem hab t) ξ
  have hsymc : ∀ t ∈ Set.Icc a b, (Mc t).IsSymm :=
    fun t _ => hsym _ (clampTime_mem hab t)
  have hCc : ChartWeights (fun t _ => Mc t) v a (b - a) ϖ zc N Cw :=
    chartWeightsMetricClamp C
  obtain ⟨u, w, hs, he⟩ := exists_frozenMetricScalarChain_with_polynomial_reserve
    K Kmax hK ρ strain B lam hρ hstrain0 hB hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets
    Mc hMc εg hεg hεgsmall hsymc (fun t _ ξ => hnear t 0 ξ) F hF f hvm hnear
    a (b - a) ϖ zc N Cw hCc L hL hρ1 hreserve (le_refl a)
    (by rw [add_sub_cancel]) hf hFe
  refine ⟨u, w, ?_, he⟩
  apply isPlaneChainFrom_geometryScalarData_congr _ hs
  intro t ht
  exact (metricClamp_of_mem (fun t _ => M t) ht).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Existence for the actual stream drift: the auxiliary energy radius is chosen internally. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_actualPreparation_planeWeakSolution (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ) (hab : a ≤ b)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) f F g u w := by
  obtain ⟨Cprep, _, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hfwd : IsSampledEnvelope family π K actual a b ν e E ρ Cprep A := by
    subst E
    exact hsample α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ
      hν hρ hρe heE family π hπ K hK actual A hA hprep hpointwise
  have hs : family.IsSmoothOn (ChartedFamily.Domain.onWindow family (Set.Icc a b)) E K := by
    intro p ctx v u γ d I tY htY z
    exact (hpointwise.1 p ctx v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hcur := streamSeq_current_admissible hΦ m
  have hvfull := Infra.Classical.streamVel_smoothPeriodic (Φ m) hcur
  obtain ⟨V, hV, hVbound⟩ := admissible_stream_spatial_jet_bound (Φ m) hcur 0
  have hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖AVenhance.streamVel (Φ m) t x‖ ≤ V := by
    intro t _ x
    simpa only [norm_iteratedFDeriv_zero] using hVbound t x
  have hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (Φ m) t) := by
    intro t _
    exact hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hvm : Measurable (fun p : Set.Icc a b × Vec 2 => AVenhance.streamVel (Φ m) p.1 p.2) :=
    hvfull.smooth.continuous.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  have hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2,
      fderiv ℝ (AVenhance.streamVel (Φ m) t) x (basisVec k) k = 0 := by
    intro t _ x
    have he := Infra.Classical.streamVel_vecDiv_eq_zero (Φ m) hcur t x
    unfold AVenhance.vecDiv AVenhance.spaceGrad at he
    have hd : DifferentiableAt ℝ (AVenhance.streamVel (Φ m) t) x :=
      ((hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x
    simp only [fderiv_apply hd, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply] at he
    exact he
  obtain ⟨M, hM, hMbound⟩ := admissible_stream_coefficient_array_budget (Φ m) hcur Kmax
  obtain ⟨r, hr, hrρ, hrhalf, hrsmall⟩ := exists_auxiliary_absorption_radius ρ ν M hρ hν hM
  have hfinite i j d := coefficientSeminorm_radius_ne_top r ρ hr.le hrρ (K i) a b _
    (sampledEnvelope_edge_seminorm_ne_top family π hπ K actual a b ν e E ρ Cprep hν hρ A hfwd i j d)
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (AVenhance.streamVel (Φ m) t)) l x‖ ≤
        M * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro t _ l _ hl x
    simp only [one_pow, one_zpow, mul_one]
    have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos l)
    exact (hMbound l hl t x).trans (le_mul_of_one_le_right hM hfac)
  exact exists_physicalPlaneWeakSolution_of_finite_seminorms K Kmax hK r M 1 1 ν
    hr hM (le_refl 1) zero_lt_one hν (by simpa using hrhalf) (by simpa using hrsmall)
    a b hab (AVenhance.streamVel (Φ m)) hv V hV hbv hdiv hjets D family H hdepth
    α q Λ m φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual
    hs hmeas hwmeas hfinite F g hF hg f hvm
end

/-! The true preparation plane equation has solutions for arbitrary data on every chronological subwindow of the original certificate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_actualPreparation_planeWeakSolution_arbitrary_subwindow (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (c tZ : ℝ) (hac : a ≤ c) (hcd : c ≤ tZ) (hdb : tZ ≤ b)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc c tZ)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc c tZ)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν c tZ (AVenhance.streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) f F g u w := by
  have hsub : Set.Icc c tZ ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨hac.trans ht.1, ht.2.trans hdb⟩
  obtain ⟨Cprep, _, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hfwd : IsSampledEnvelope family π K actual a b ν e E ρ Cprep A := by
    subst E
    exact hsample α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ
      hν hρ hρe heE family π hπ K hK actual A hA hprep hpointwise
  have hs : family.IsSmoothOn (ChartedFamily.Domain.onWindow family (Set.Icc a b)) E K := by
    intro p ctx v u γ d I tY htY z
    exact (hpointwise.1 p ctx v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hcur := streamSeq_current_admissible hΦ m
  have hvfull := Infra.Classical.streamVel_smoothPeriodic (Φ m) hcur
  obtain ⟨V, hV, hVbound⟩ := admissible_stream_spatial_jet_bound (Φ m) hcur 0
  have hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖AVenhance.streamVel (Φ m) t x‖ ≤ V := by
    intro t _ x
    simpa only [norm_iteratedFDeriv_zero] using hVbound t x
  have hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (Φ m) t) := by
    intro t _
    exact hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hvm : Measurable (fun p : Set.Icc a b × Vec 2 => AVenhance.streamVel (Φ m) p.1 p.2) :=
    hvfull.smooth.continuous.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  have hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2,
      fderiv ℝ (AVenhance.streamVel (Φ m) t) x (basisVec k) k = 0 := by
    intro t _ x
    have he := Infra.Classical.streamVel_vecDiv_eq_zero (Φ m) hcur t x
    unfold AVenhance.vecDiv AVenhance.spaceGrad at he
    have hd : DifferentiableAt ℝ (AVenhance.streamVel (Φ m) t) x :=
      ((hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x
    simp only [fderiv_apply hd, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply] at he
    exact he
  obtain ⟨M, hM, hMbound⟩ := admissible_stream_coefficient_array_budget (Φ m) hcur Kmax
  obtain ⟨r, hr, hrρ, hrhalf, hrsmall⟩ := exists_auxiliary_absorption_radius ρ ν M hρ hν hM
  have hfiniteFull i j d := coefficientSeminorm_radius_ne_top r ρ hr.le hrρ (K i) a b _
    (sampledEnvelope_edge_seminorm_ne_top family π hπ K actual a b ν e E ρ Cprep hν hρ A hfwd i j d)
  have hfinite i j d := ne_top_of_le_ne_top (hfiniteFull i j d)
    (coefficientSeminorm_time_mono r (K i) c tZ a b hsub
      (edgeCoefficient family ν e E actual K i j d))
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (AVenhance.streamVel (Φ m) t)) l x‖ ≤
        M * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro t _ l _ hl x
    simp only [one_pow, one_zpow, mul_one]
    have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos l)
    exact (hMbound l hl t x).trans (le_mul_of_one_le_right hM hfac)
  have hC i j d t ht := edgeCoefficient_spatial_smooth family hprep ν e E K hs actual K i j d t ht
  have hAm i j d := jointMeasurable_subwindow c tZ a b hsub
    (edgeCoefficient family ν e E actual K i j d)
    (edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d)
  have hvmSmall := jointMeasurable_subwindow c tZ a b hsub (streamVel (Φ m)) hvm
  have hrank i j (hij : ¬ sourceDepthRank family H j < sourceDepthRank family H i) d :
      edgeCoefficient family ν e E actual K i j d = 0 :=
    physicalCoefficient_zero_of_rank family H hdepth ν e E actual i j d.val hij
  exact exists_triangularPlaneWeakSolution K Kmax hK r M 1 1 ν
    hr hM (le_refl 1) zero_lt_one hν (by simpa using hrhalf) (by simpa using hrsmall)
    c tZ hcd (AVenhance.streamVel (Φ m)) (fun t ht => hv t (hsub ht))
    V hV (fun t ht => hbv t (hsub ht)) (fun t ht => hdiv t (hsub ht))
    (fun t ht => hjets t (hsub ht)) D
    (edgeCoefficient family ν e E actual K) hfinite
    (fun i j d t ht => hC i j d t (hsub ht))
    (sourceDepthRank family H) (fun i j hij d => hrank i j hij d)
    F g hF hg f hvmSmall hAm
end

/-! The true preparation plane equation has solutions for arbitrary data on every chronological subwindow of the original certificate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_actualPreparation_planeWeakSolution_arbitrary_subwindow_family (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (c tZ : ℝ) (hac : a ≤ c) (hcd : c ≤ tZ) (hdb : tZ ≤ b)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc c tZ)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc c tZ)))
    {X : Type*} (f : X → ∀ i, PlaneHk Set.univ (K i) (h i))
    :
    ∃ (u : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      ∀ x, IsCoupledWeakSolutionPlane ν c tZ (AVenhance.streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) (f x) F g (u x) (w x) := by
  have hex (x : X) := exists_actualPreparation_planeWeakSolution_arbitrary_subwindow
    K Kmax hK ρ ν hρ hν a b D family H hdepth α q Λ m Φ ζ hΦ φ hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual hmeas hwmeas hE hρe heE
    Jm hchart hmol Cm π hπ A hA hpointwise c tZ hac hcd hdb F g hF hg (f x)
  exact ⟨fun x => (hex x).choose, fun x => (hex x).choose_spec.choose,
    fun x => (hex x).choose_spec.choose_spec⟩
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual preparation data supply the quantitative source inputs for native
homogeneous stability, uniformly over the covered reference time. -/

universe u v w x

theorem preparation_reference_source_energy_data
    (D Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
      IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ (yc : Vec 2) (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H →
    let A := preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    (∀ i j d, coefficientSeminorm (ρ / e) (K i) a b (A i j d) ≠ ⊤) ∧
    (∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t)) ∧
    (∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) ∧
    (∀ i, ∑ j, schurMatrix 1 (ρ / e) π K D a b A i j ≤ Cprep * θ) ∧
    (∀ j, ∑ i, schurMatrix 1 (ρ / e) π K D a b A i j ≤ Cprep * θ) ∧
    (∀ i, sourceDepthRank F H i ≤ H) ∧
    (∀ i j, ¬ sourceDepthRank F H j < sourceDepthRank F H i → ∀ d, A i j d = 0) := by
  obtain ⟨Cprep, hCprep, hschur⟩ := preparation_reference_cell_source_subwindow_schur_budget
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ P' Ctx F π hπ K hK actual B hB hprep hmeas hwmeas henv
    yc a b θ hsub hrow hcol H hdepth A
  obtain ⟨hfinite, hsmooth, hmeasA, _⟩ := preparationReferenceCellSource_pointwise_subwindow_data
    F hprep ν e ρ hν hρ hρe heE K Kmax Jm hK hchart hmol Cm
    hmeas hwmeas actual yc π hπ B hB henv a b (ρ / e) hsub
  have hentry := hschur α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ
    hν hρ hρe heE F π hπ K hK actual B hB hprep henv yc a b hsub
  refine ⟨hfinite, hsmooth, hmeasA, ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      _ ≤ ∑ j, Cprep * B i j := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = Cprep * ∑ j, B i j := (Finset.mul_sum _ _ _).symm
      _ ≤ Cprep * θ := mul_le_mul_of_nonneg_left (hrow i) (le_trans zero_le_one hCprep)
  · intro j
    calc
      _ ≤ ∑ i, Cprep * B i j := Finset.sum_le_sum (fun i _ => hentry i j)
      _ = Cprep * ∑ i, B i j := (Finset.mul_sum _ _ _).symm
      _ ≤ Cprep * θ := mul_le_mul_of_nonneg_left (hcol j) (le_trans zero_le_one hCprep)
  · exact sourceDepthRank_le F H
  · intro i j hij d
    exact preparationReferenceCellSourceCoefficient_zero_of_rank F hφ H hdepth
      ((l₀ : ℝ) * ocTauPP α q Λ m) ν e (ocEpsilon q Λ (m - 1)) actual K yc i j d hij

end AVRegularity.CycleJointProofs
end
end

section
/-! Constructing all original weighted natural remainder maps and assembling
 their mass moment estimate, with constants fixed before the family and scales. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.ChartTransport
  AVRegularity.CycleWords AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem exists_naturalFamilyRemainder_maps_mass_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (hKs : Ks + 1 ≤ J) (hb : ∀ v u, 0 ≤ b₀ v u)
    (θ : ℝ) (hθ : 0 ≤ θ) (hrow : ∀ v, ∑ u, b₀ v u ≤ θ)
    (hcol : ∀ u, ∑ v, b₀ v u ≤ θ)
    (S : Finset P) (ctx : ∀ p : S, Ctx p.val)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (anchor : S → ℝ) (σ : ℝ)
    (hr : ∀ p, anchor p ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : ∀ p, |anchor p - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ) (hn : ∀ v, K v ≤ Jchart + 1)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    (N : ℕ) (hN : N ≤ Jchart)
    (hKN : ∀ v u γ, K v + (F.identity v u γ).maxOrder ≤ N)
    (hcellE : 0 < ocEpsilon q Λ (m - 1)) (yc : Vec 2) (μ : Measure ℝ) :
    ∃ T : ∀ v u, F.Γ v u → Fin D → S →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    (∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (ctx p) v u γ
        timeScale a b hφ (anchor p) σ e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) (j.val + 1) I z)))
      (T v u γ j p)) ∧
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    let CR := nativeArrayUniformTransportPrice N D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ
        (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v Z) τ) ∂μ) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) C * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u) (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (Z u) τ) ∂μ := by
  classical
  have hex (v u : ι) (γ : F.Γ v u) (j : Fin D) (p : S) :=
    exists_originalFamilyNaturalRemainder_descending_identity_density_map Ks F hw hm π hπ K Kmax hK
      W ν e E ρ hν he hE hρ C J b₀ henv v u γ hKs p.val (ctx p)
      (rjet := j.val + 1) hdesc (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt) hc ha
      (anchor p) σ (hr p) hσ (hage p) hsE ϖ ζ hϖ hscale hζ hδ (hn v)
      timeScale a b htime N hN (hKN v u γ) hcellE yc μ
  choose T hT hdens using hex
  refine ⟨T, ?_, ?_⟩
  · intro v u γ j p
    exact hT v u γ j p
  · dsimp only
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow N * Cflow
    have hCf : 1 ≤ Cflow := one_le_jetConst _ _
    have hCp : 0 ≤ Cpiola := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
    have hCR := mul_nonneg (nativeArrayUniformTransportPrice_nonneg N D Kmax Cpiola hCp)
      (naturalRemainderChartPrice_nonneg Ks Kmax Jchart Cchart)
    intro Z n
    exact pointwiseOriginalRemainder_piece_order_mass_moment_budget F π hπ K Ks Kmax D hK
      (ChartedFamily.Domain.onWindow F W) ν e E ρ _ ζ hCR hζ hν hE hρ C J b₀ hKs henv
      hb θ hθ hrow hcol ϖ μ S timeScale T Z hdens n

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual coupled coefficient array splits its certified native map into metric and original source maps. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance centralMetricMapIdentificationNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance centralMetricMapIdentificationModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem planeCentralMetric_family_map_identification
    (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (diag : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hLdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t
        (planeDiagonalGradientCoefficient K D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (Ldiag i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (diag i)) :
    ∀ i, Ldiag i = (diag i).comp (LinearMap.proj i) := by
  intro i
  have hd : IsPlaneTimeAllMomentRawLinearMap
      (X := ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t
        (planeDiagonalGradientCoefficient K D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i)
      ((diag i).comp (LinearMap.proj i)) := by
    intro X
    filter_upwards [hdiag i (X i)] with t ht
    apply ht.trans
    exact Filter.Eventually.of_forall (fun z =>
      (planeRawCouplingFlux_diagonal_matrix_flux K D hD (fun _ t _ => M t - 1)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i t z).symm)
  apply planeRaw_allMoment_map_unique (K i) ϖ ρ 0 μ _ _ _ _ (hLdiag i) hd
  intro X
  exact Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
end

/-! The actual coupled coefficient array splits its certified native map into metric and original source maps. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance metricSourceMapConstructNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance metricSourceMapConstructModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem planeMetricSource_allMoment_map_construction
    (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (source : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (metric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (source i))
    (hmetric : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun z => G t z - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (metric i)) :
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i)
      ((metric i).comp (LinearMap.proj i) + source i) := by
  intro i
  have hm : IsPlaneTimeAllMomentRawLinearMap
      (X := ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun z => G t z - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ (X i) t))
      ((metric i).comp (LinearMap.proj i)) := by
    intro X
    exact hmetric i (X i)
  have hs := planeRaw_allMoment_linearMap_add
    (X := ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ)
    (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ _ _
    ((metric i).comp (LinearMap.proj i)) (source i) hm (hsource i)
  intro X
  filter_upwards [hs X] with t ht
  apply ht.trans
  apply Filter.Eventually.of_forall
  intro z
  change _ = planeRawCouplingFlux K D t
    (fun i j d t z => planeDiagonalGradientCoefficient K D
      (fun _ t z => G t z - 1) i j d t z + A i j d t z)
    (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i z
  rw [planeRawCouplingFlux_add, planeRawCouplingFlux_diagonal_matrix_flux K D hD]
end

end AVRegularity.CycleJointProofs
end
end
