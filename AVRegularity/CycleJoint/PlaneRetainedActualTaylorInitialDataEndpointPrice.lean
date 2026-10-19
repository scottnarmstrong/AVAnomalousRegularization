-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PreparationReferenceNormalizedHilbertCurve
public import AVRegularity.CycleJoint.PlaneHomogeneousMaterialWeakCurve
import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The normalized homogeneous material curve uses the true computed velocity and the exact coupled-array L2 flux, with no operator identification premise. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_normalized_hilbert_curve_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' o, coefficientSeminorm ρ (K i) c d (edgeCoefficient F ν e E actual K i i' o) ≠ ⊤)
    (hc : ∀ i i' o t, t ∈ Icc c d → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' o t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc c d, Continuous (v t))
    (hvm : Measurable (fun p : Icc c d × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc c d, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' o, Measurable (fun p : Icc c d × Vec 2 => edgeCoefficient F ν e E actual K i i' o p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν c d v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    PlaneWeakHilbertCurve (ν * c) (ν * d)
      (fun t => planeHkValueOperator (K i) (U i (ν⁻¹ * t)))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
      (fun t => planeWeakDualRepresentative
        (planeIntervalTransport (ν * c) (ν * d) (mul_le_mul_of_nonneg_left hcd hν.le)
          (normalizedMaterialVelocity hφ σ ν v)
          (fun r _ => normalizedMaterialVelocity_continuous hφ σ ν v hv r)
          (normalizedMaterialVelocityBudget hφ σ ν c d v hv hp)
          (normalizedMaterialVelocity_norm_le hφ σ hν c d v hv hp) t)
        (ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
        (preparationWindowReferenceSubwindowNormalizedFlux F K c d hcd hprep hcover σ hσ ha hK ν e E n hsmooth
          actual hT he W i t)) := by
  dsimp only
  have hcurve := preparation_window_reference_normalized_homogeneous_weak_curve_subwindow F hcd hsub ρ hρ K hdesc
    hprep hcover σ hσ ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i
  apply planeWeakHilbertCurve_dual_congr_on hcurve
  intro t ht
  rw [planeMaterialTransport_diffusion_time_normalization hcd hν hφ
    σ v hv hp t ht]
  rfl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The actual cover propagates finite moments for any frozen scalar response without a weight or reserve-size premise. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_moment_propagation (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (N : ℕ) (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (hFe : ∀ n ≤ N, ∀ x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤)
    (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (hs : let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x)) :
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  classical
  let Cenv := max 0 ((ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν) / B)
  have hC : 0 ≤ Cenv := le_max_left _ _
  have henv : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ Cenv * B :=
    (div_le_iff₀ cov.pos.2.1).mp (le_max_right _ _)
  obtain ⟨Kcut, hKcut, hcut⟩ := CycleReference.cutoff_derivative_uniform_bound
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  let G := fun t (_ : Vec 2) => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0
  have hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc ∨
      G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0 := Or.inr rfl
  let W := windowCover_subwindowChartWeights hΛ hζ hφ cov hg0 hC henv
    (ocTauPP α q Λ m) rfl (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ)
    Kcut hKcut.le (hcut α q Λ m hΛ) i G hG u0 u1 hu hwindow hlength N
  let Cw : ℕ → ℝ := adjointWeightConstant Cenv Kcut
  have hres (n : ℕ) := exists_scalar_square_reserve (Real.exp (18 * Cw n))
    (Real.exp_pos _).le
  let L : ℕ → ℝ := fun n => Classical.choose (hres n)
  have hL : ∀ n ≤ N, 1 ≤ L n := fun n _ => (Classical.choose_spec (hres n)).1
  have hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / (L n) ^ 2 ≤ 1 / 16 :=
    fun n _ => (Classical.choose_spec (hres n)).2
  subst ϖ
  exact windowCover_frozen_response_reserve_propagation hΛ hζ hφ cov K hK i u0 u1 hu.le
    hwindow hgsmall N (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    Cw W L hL hreserve F hF f hf hFe u w hs
end

/-! The actual cover constructs frozen scalar responses with finite moments from native initial and forcing data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_moment_construction (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (N : ℕ) (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (hFe : ∀ n ≤ N, ∀ x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x) ∧
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  let Cenv := max 0 ((ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν) / B)
  have hC : 0 ≤ Cenv := le_max_left _ _
  have henv : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ Cenv * B :=
    (div_le_iff₀ cov.pos.2.1).mp (le_max_right _ _)
  obtain ⟨Kcut, hKcut, hcut⟩ := CycleReference.cutoff_derivative_uniform_bound
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  let G := fun t (_ : Vec 2) => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0
  have hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc ∨
      G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0 := Or.inr rfl
  let W := windowCover_subwindowChartWeights hΛ hζ hφ cov hg0 hC henv
    (ocTauPP α q Λ m) rfl (Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ)
    Kcut hKcut.le (hcut α q Λ m hΛ) i G hG u0 u1 hu hwindow hlength N
  subst ϖ
  exact windowCover_frozen_response_finite_moments hΛ hζ hφ cov K hK i u0 u1 hu.le hwindow hgsmall
    N (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (adjointWeightConstant Cenv Kcut)
    W F hF f hf hFe
end

/-! The zeroth response is a genuine homogeneous frozen scalar solution retaining the full initial moment reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_homogeneous_response_moment_construction (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (N : ℕ) (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ _ _ => 0) (fun _ x => u x) (fun _ x => w x) ∧
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  exact windowCover_frozen_response_moment_construction hΛ hζ hφ cov K hK i u0 u1 hu hwindow
    hgsmall hg0 hlength N ϖ hϖ (fun _ _ => 0)
    (fun x => planeHk_zero_time_memLp (K x) (volume.restrict (Set.Icc u0 u1))) f hf
    (fun _ _ _ => by
      simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.ChartTransport
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Subtracting the constructed original remainder from the actual native
source map gives precisely the natural Taylor source, with an exact map split. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem exists_preparationReferenceCellSourceMaps_with_remainder_budget
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (hdesc : F.IsDescending K) (Ks : ℕ)
    (yc : Vec 2) (a b ϖ : ℝ) (hab : a ≤ b)
    (Kmax Jm : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (hsub : Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)))
    (hKs : Ks + 1 ≤ Jm) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, B v u ≤ θ) (hcol : ∀ u, ∑ v, B v u ≤ θ)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1) (hζ : 0 ≤ ζ)
    (hδ : e / ocEpsilon q Λ (m - 1) = ζ * ϖ)
    (htime : ∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) :
    ∃ T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Lfull v)) ∧
    let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
    ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : (F.locally_finite tS tZ).toFinset,
        naturalFamilyTaylorNativeArray Ks F p.val (actual p.val) v u γ (ν⁻¹ * e ^ 2) hφ
          (F.piece p.val).anchor ((l₀ : ℝ) * ocTauPP α q Λ m) e (ocEpsilon q Λ (m - 1)) yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
              (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z)))
      (Lfull v - Rs v) ∧ Lfull v = (Lfull v - Rs v) + Rs v) ∧
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
        (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) Cm * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b) := by
  have he : 0 < e := hρ.trans_le hρe
  have hE : 0 < ocEpsilon q Λ (m - 1) := he.trans_le heE
  have hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e :=
    div_le_div_of_nonneg_right (hρe.trans heE) he.le
  have hN : Kmax + D ≤ Jchart := by omega
  obtain ⟨T, hT, hmass⟩ := exists_preparationNaturalRemainder_maps_mass_budget Ks F hwmeas hmeas
    π hπ K Kmax hK hdesc ν e (ocEpsilon q Λ (m - 1)) ρ hν he hE hρ Cm Jm B henv
    hKs hB θ hθ hrow hcol actual hc hTau ha hsE ϖ ζ hϖ hscale hζ hδ
    (ν⁻¹ * e ^ 2) a b (fun τ ht => by simpa only [mul_assoc] using htime τ ht)
    hN hE yc (volume.restrict (Set.Icc a b))
  obtain ⟨Lfull, hfull, htaylor⟩ := exists_preparationReferenceCellSourceMap_natural_split F hc ν e ρ
    hν hρ hρe heE actual K hdesc Ks yc a b ϖ hab Kmax Jm hK hchart hmol Cm hmeas hwmeas
    π hπ B hB henv hsub htime T hT
  exact ⟨T, Lfull, ⟨hfull, htaylor⟩, hmass⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine homogeneous physical coupled solution transfers to the full coupled weak solution class in normalized reference coordinates, with the explicitly computed coefficient array. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_normalized_coupled_solution
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 (ν * a) (ν * b)
      (normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v) D K
      (preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K)
      (fun j => preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) a (f j))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => U j (ν⁻¹ * t)) (fun j t => W j (ν⁻¹ * t)) := by
  dsimp only
  let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
    preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
      (by have hh := hK j; omega) t (u j t)
  let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
    preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
      (Nat.add_le_add_right (hK j) 1) t (w j t)
  have hdata (i : ι) := preparation_reference_normalized_trace_data hs hν F hprep hcover hTau ha hK i
  apply planeCoupledSolution_of_rawFlux_hilbertCurves
    (mul_le_mul_of_nonneg_left hab hν.le) 1 K D
    (preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K)
    (normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v)
    (fun r _ => normalizedMaterialVelocity_continuous hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v hv r)
    (normalizedMaterialVelocityBudget hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν a b v hv hp)
    (normalizedMaterialVelocity_norm_le hφ ((l₀ : ℝ) * ocTauPP α q Λ m) hν a b v hv hp)
    (fun j => preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
      (by have hh := hK j; omega) a (f j))
    (fun j t => U j (ν⁻¹ * t)) (fun j t => W j (ν⁻¹ * t))
    (fun i => (hdata i).1) (fun i => (hdata i).2.1)
    (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
    (preparationReferenceNormalizedFlux F K hab hprep hcover hTau ha hK ν e E n hsmooth actual hT he W)
  · intro i t ht k
    exact preparationReferenceNormalizedFlux_ae F K hab hprep hcover hTau ha hK ν e E n hsmooth
      actual hT he W i t hD hdesc hν ht k
  · intro i
    simpa only [one_smul] using preparation_reference_normalized_hilbert_curve F hab ρ hρ K hdesc
      hprep hcover hTau ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine metric and original-source Taylor residual estimates feed the constructed coupled error endpoint. -/

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance actualTaylorPriceEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance actualTaylorPriceEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance actualTaylorPriceEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance actualTaylorPriceEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeRetained_actualTaylor_constructed_error_endpoint_price
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)],
    ∀ (n D H N : ℕ) (Cw : ℕ → ℝ) (Cprep Cgraph θsrc : ℝ), 0 ≤ θsrc →
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ Cjet j * g * δ ^ j)
        (tw S ϖ : ℝ) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ (0 : Vec 2) N Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
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
    (Hraw : ∀ v u, family.Γ v u →
      PlaneTimeAllMomentCarrier (E := h u) (Kslot u + 1) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (_hHzero : ∀ v u γ, ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), Hraw v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (_hTaylorRaw : ∀ v, IsPlaneTimeAllMomentRawLinearMap (Kslot v) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t z => ∑ u, ∑ γ, Hraw v u γ (X u) t z) (nativeFamilyEdgeForcingMap Ledge v))
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
        (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (diag Rmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (_hMcenter : M = fun t => G t 0)
        (_hSourceRaw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeRawCouplingFlux Kslot D t A
            (fun j => planeTimeAllMomentCarrierToLp (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Rmetric i))
        (_WM : ChartWeights (fun t _ => M t) v tw S ϖ 0 N Cw)
        (L ζslow : ℝ) (_hL : 1 ≤ L) (_hζslow : 0 ≤ ζslow) (_hζslow1 : ζslow ≤ 1)
        (_hϖ : 0 < ϖ) (_hscale : rstar * ϖ ≤ 1) (_hδslow : δ = ζslow * ϖ)
        (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
        (_hMm : Measurable M)
        (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
        (_hGhigh : ∀ t ∈ Set.Icc ta tb, ∀ k l,
          ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
        (_hGlowjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
          ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * g * δ ^ r)
        (_hGhighjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, Ks + 1 ≤ r →
          r ≤ Ks + 1 + Kmax → ∀ y k l,
            ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * g * (ζslow * ϖ) ^ r)
        (_hrem : ∀ X k, planeAllMomentFamilyEnergy Kslot k ϖ rstar
          (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i X) ≤
          ENNReal.ofReal ((ζslow ^ (Ks + 1) * (Cgraph * θsrc)) ^ 2) *
          planeAllMomentFamilyGradientEnergy Kslot (k + (Ks + 1)) ϖ rstar
            (volume.restrict (Set.Icc ta tb)) π X)
        (_hgain : ENNReal.ofReal (CT * g * ζslow) ≤ 1)
        (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θsrc) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θsrc
        let ζ := ENNReal.ofReal ζslow
        let η := ENNReal.ofReal (Cterminal * g * ζslow)
        let G0 := planeAllMomentFamilyGradientEnergy Kslot N ϖ rstar
          (volume.restrict (Set.Icc ta tb)) π Z
        let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
        let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
        let Tret := ∑ k ∈ Finset.range (H + 1), U J k
        let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
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
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0)) := by
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hbudgets⟩ :=
    planeComponentAllMomentResponse_actualTaylor_originalEdge_three_residual_budgets_uniform
      Ks Kmax Cjet hCjet
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ n D H N Cw Cprep Cgraph θsrc hθsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve
    hMm hGm hGhigh hGlowjet hGhighjet hrem hgain hN
  have hn : n ≤ N := by omega
  have hMnear : IsMetricNearIdentity (fun t _ => M t) g := by
    rw [hMcenter]
    exact fun t _ ξ => hG_near t 0 ξ
  have hMsym : ∀ t ∈ Set.Icc ta tb, (M t).IsSymm := by
    rw [hMcenter]
    exact fun t ht => hG_symm t ht 0
  obtain ⟨V, hVbound⟩ := hv_bdd
  obtain ⟨hm, hs, htres⟩ := hbudgets (E := h)
    ta tb ht Kslot hKslot v hv_meas hv_smooth (max V 0) strain B₀ lam
    (le_max_right _ _) ha hB₀ hlam
    (fun t ht z => (hVbound t ht z).trans (le_max_left _ _))
    (fun t ht l hl hlmax z => hjets l hl hlmax t ht z)
    M hMm g hg hg4 hMnear hMsym tw S ϖ N Cw WM rstar L hrstar hL hB hab
    hreserve hv_div htw htb π R hR hπ G δ ζslow g hGm
    (fun t ht k l => (hGhigh t ht k l).of_le (by exact_mod_cast (show Ks ≤ Ks + 1 + Kmax by omega)))
    hϖ hscale hζslow hζslow1 hg hδslow hGlowjet
    Lmetric hPositive D A hA hc Ledge Cprep Cgraph θsrc hθsrc hrow hcol Rs hrem
    hSourceRaw hGhigh hGhighjet Rmetric hMetricRemainder hgain Z n J H hN
  have hout := planeRetained_literal_constructed_error_endpoint_price
    n Kmax Cjet Cw D H Ks (Cprep * θsrc) π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ v ⟨V, hVbound⟩ hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets tw S ϖ htw htb (chartWeightsReserveRestriction W hn) hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder
  dsimp only at hout ⊢
  exact hout
    (scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)))
    (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2))
    (ENNReal.ofReal ((Cgraph * θsrc) ^ 2))
    (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
    (ENNReal.ofReal θsrc) (ENNReal.ofReal θsrc) (ENNReal.ofReal ζslow)
    (ENNReal.ofReal (Cterminal * g * ζslow))
    (planeAllMomentFamilyGradientEnergy Kslot N ϖ rstar
      (volume.restrict (Set.Icc ta tb)) π Z) le_rfl hm hs htres

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine homogeneous physical coupled solution transfers to the full coupled weak solution class in normalized reference coordinates, with the explicitly computed coefficient array. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_normalized_coupled_solution_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' o, coefficientSeminorm ρ (K i) c d (edgeCoefficient F ν e E actual K i i' o) ≠ ⊤)
    (hc : ∀ i i' o t, t ∈ Icc c d → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' o t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc c d, Continuous (v t))
    (hvm : Measurable (fun p : Icc c d × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc c d, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' o, Measurable (fun p : Icc c d × Vec 2 => edgeCoefficient F ν e E actual K i i' o p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν c d v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 (ν * c) (ν * d)
      (normalizedMaterialVelocity hφ σ ν v) D K
      (preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K)
      (fun j => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) c (f j))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => U j (ν⁻¹ * t)) (fun j t => W j (ν⁻¹ * t)) := by
  dsimp only
  let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
    preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
      (by have hh := hK j; omega) t (u j t)
  let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
    preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
      (Nat.add_le_add_right (hK j) 1) t (w j t)
  have hdata (i : ι) := preparation_window_reference_normalized_trace_data_subwindow hs hν F hprep hcover σ hσ ha hK hsub i
  apply planeCoupledSolution_of_rawFlux_hilbertCurves
    (mul_le_mul_of_nonneg_left hcd hν.le) 1 K D
    (preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K)
    (normalizedMaterialVelocity hφ σ ν v)
    (fun r _ => normalizedMaterialVelocity_continuous hφ σ ν v hv r)
    (normalizedMaterialVelocityBudget hφ σ ν c d v hv hp)
    (normalizedMaterialVelocity_norm_le hφ σ hν c d v hv hp)
    (fun j => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
      (by have hh := hK j; omega) c (f j))
    (fun j t => U j (ν⁻¹ * t)) (fun j t => W j (ν⁻¹ * t))
    (fun i => (hdata i).1) (fun i => (hdata i).2.1)
    (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
    (preparationWindowReferenceSubwindowNormalizedFlux F K c d hcd hprep hcover σ hσ ha hK ν e E n hsmooth actual hT he W)
  · intro i t ht k
    exact preparationWindowReferenceSubwindowNormalizedFlux_ae F K c d hcd hprep hcover σ hσ ha hK ν e E n hsmooth
      actual hT he W i t hsub hD hdesc hν ht k
  · intro i
    simpa only [one_smul] using preparation_window_reference_normalized_hilbert_curve_subwindow F hcd hsub ρ hρ K hdesc
      hprep hcover σ hσ ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine metric and original-source Taylor residual estimates feed the constructed coupled error endpoint. -/

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance actualTaylorInitialEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance actualTaylorInitialEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance actualTaylorInitialEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance actualTaylorInitialEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeRetained_actualTaylor_initial_data_endpoint_price
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)],
    ∀ (n D H N : ℕ) (Cw : ℕ → ℝ) (Cprep Cgraph θsrc : ℝ), 0 ≤ θsrc →
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ Cjet j * g * δ ^ j)
        (ϖ : ℝ)
        (_W : ChartWeights G v ta (tb - ta) ϖ (0 : Vec 2) N Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
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
    (Hraw : ∀ v u, family.Γ v u →
      PlaneTimeAllMomentCarrier (E := h u) (Kslot u + 1) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (_hHzero : ∀ v u γ, ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), Hraw v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (_hTaylorRaw : ∀ v, IsPlaneTimeAllMomentRawLinearMap (Kslot v) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t z => ∑ u, ∑ γ, Hraw v u γ (X u) t z) (nativeFamilyEdgeForcingMap Ledge v))
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
        (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (diag Rmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (_hMcenter : M = fun t => G t 0)
        (_hSourceRaw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeRawCouplingFlux Kslot D t A
            (fun j => planeTimeAllMomentCarrierToLp (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Rmetric i))
        (_WM : ChartWeights (fun t _ => M t) v ta (tb - ta) ϖ 0 N Cw)
        (L ζslow : ℝ) (_hL : 1 ≤ L) (_hζslow : 0 ≤ ζslow) (_hζslow1 : ζslow ≤ 1)
        (_hϖ : 0 < ϖ) (_hscale : rstar * ϖ ≤ 1) (_hδslow : δ = ζslow * ϖ)
        (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
        (_hMm : Measurable M)
        (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
        (_hGhigh : ∀ t ∈ Set.Icc ta tb, ∀ k l,
          ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
        (_hGlowjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
          ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * g * δ ^ r)
        (_hGhighjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, Ks + 1 ≤ r →
          r ≤ Ks + 1 + Kmax → ∀ y k l,
            ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * g * (ζslow * ϖ) ^ r)
        (_hrem : ∀ X k, planeAllMomentFamilyEnergy Kslot k ϖ rstar
          (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i X) ≤
          ENNReal.ofReal ((ζslow ^ (Ks + 1) * (Cgraph * θsrc)) ^ 2) *
          planeAllMomentFamilyGradientEnergy Kslot (k + (Ks + 1)) ϖ rstar
            (volume.restrict (Set.Icc ta tb)) π X)
        (_hgain : ENNReal.ofReal (CT * g * ζslow) ≤ 1)
        (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θsrc) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θsrc
        let ζ := ENNReal.ofReal ζslow
        let η := ENNReal.ofReal (Cterminal * g * ζslow)
        let G0 := ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rstar (Kslot i) (V₀ i)
        let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
        let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
        let Tret := ∑ k ∈ Finset.range (H + 1), U J k
        let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
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
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0)) := by
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    planeRetained_actualTaylor_constructed_error_endpoint_price Ks Kmax Cjet hCjet
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ n D H N Cw Cprep Cgraph θsrc hθsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    ϖ W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve
    hMm hGm hGhigh hGlowjet hGhighjet hrem hgain hN
  have hMnear : IsMetricNearIdentity (fun t _ => M t) g := by
    rw [hMcenter]
    exact fun t _ ξ => hG_near t 0 ξ
  have hMsym : ∀ t ∈ Set.Icc ta tb, (M t).IsSymm := by
    rw [hMcenter]
    exact fun t ht => hG_symm t ht 0
  have hbaseEnergy := (frozenWindowHomogeneousGradientConstant_spec.{u, v} N Kmax Cw).2
    Kslot hKslot ta tb rstar ht hrstar v hv_meas hv_smooth hv_bdd hv_div
    strain B₀ lam ha hB₀ hlam hjets hB hab M hMm g hg hg4 hMsym
    (fun t _ ξ => hMnear t 0 ξ) ϖ WM π V₀ u0 w0 Z hbase hZ
  obtain ⟨Fout, uout, wout, hsol, hF, hW, hbound⟩ := hendpoint
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    ta (tb - ta) ϖ le_rfl (by rw [add_sub_cancel]) W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve
    hMm hGm hGhigh hGlowjet hGhighjet hrem hgain hN
  dsimp only at hbound ⊢
  refine ⟨Fout, uout, wout, hsol, hF, hW, ?_⟩
  intro tp htp
  exact (hbound tp htp).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbaseEnergy zero_le) zero_le) zero_le)

end AVRegularity.CycleJointProofs
end
