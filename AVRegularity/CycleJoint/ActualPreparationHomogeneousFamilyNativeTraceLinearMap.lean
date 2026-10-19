-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneRetainedActualTaylorInitialDataEndpointPrice
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Every covered time trace of a scalar response with all-moment forcing has finite polynomial energy. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_endpoint_all_moments (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (Q : ∀ x, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x))
      (K x) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)))
    (hQ : ∀ x, PlaneTimeAllMomentRepresents (K x) ϖ (ρs / ocEpsilon q Λ m) 0
      (volume.restrict (Set.Icc u0 u1)) (Q x) (F x))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n x, weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (hs : let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x)) :
    ∀ n x τ, τ ∈ Set.Icc u0 u1 →
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (u x τ) ≠ ⊤ := by
  have hF (x : ι) : MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)) :=
    (planeTimeAllMomentCarrier_memLp (K x) ϖ (ρs / ocEpsilon q Λ m) 0
      (volume.restrict (Set.Icc u0 u1)) (Q x)).ae_eq (hQ x)
  have hFe (n : ℕ) (x : ι) : (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤ := by
    have he : (fun t => weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x)
        (planeTimeAllMomentCarrierToLp (K x) ϖ (ρs / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc u0 u1)) (Q x) t)) =ᵐ[volume.restrict (Set.Icc u0 u1)]
        fun t => weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t) := by
      filter_upwards [hQ x] with t ht
      rw [ht]
    rw [← lintegral_congr_ae he]
    exact planeTimeAllMomentCarrier_moment (K x) ϖ (ρs / ocEpsilon q Λ m) 0
      (volume.restrict (Set.Icc u0 u1)) (Q x) n
  intro n x τ hτ
  have hh := windowCover_frozen_response_moment_propagation hΛ hζ hφ cov K hK i
    u0 u1 hu hwindow hgsmall hg0 hlength n ϖ hϖ F hF f
    (fun r _ j => hf r j) (fun r _ j => hFe r j) u w hs n (le_refl n) x
  apply ne_top_of_le_ne_top hh.1
  have hb : weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (u x τ) ≤
      ⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
        (ρs / ocEpsilon q Λ m) (K x) (u x t) :=
    le_iSup_of_le τ (le_iSup_of_le hτ le_rfl)
  exact hb.trans (le_add_of_nonneg_right (by positivity))
end

/-! The actual zeroth response of all-moment initial data gives a native time-domain element for finite causal source sums. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

variable (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)

include hΛ hζ cov hK hu hwindow hgsmall hg0 hlength hϖ hf in
theorem windowCover_frozen_homogeneous_all_moment_response :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ (Z : ∀ x, PlaneTimeAllMomentCarrier (E := h x) (K x + 1) ϖ
        (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)))
      (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ _ _ => 0) (fun _ x => u x) (fun _ x => w x) ∧
      ∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc u0 u1)) (Z x) (w x) := by
  classical
  obtain ⟨u, w, hs, _⟩ := windowCover_frozen_homogeneous_response_moment_construction
    hΛ hζ hφ cov K hK i u0 u1 hu hwindow hgsmall hg0 hlength 0 ϖ hϖ f
    (fun n _ x => hf n x)
  have hmoment (n : ℕ) := windowCover_frozen_response_moment_propagation
    hΛ hζ hφ cov K hK i u0 u1 hu hwindow hgsmall hg0 hlength n ϖ hϖ (fun _ _ => 0)
    (fun x => planeHk_zero_time_memLp (K x) (volume.restrict (Set.Icc u0 u1))) f
    (fun n _ x => hf n x)
    (fun _ _ _ => by
      simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top) u w hs
  have hc := scalarPlaneChain_diagonalMetric_solution K u0 u1
    (ocCellDrift α q Λ ζ m ν (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
    (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0)
    f (fun _ _ => 0) u w hs
  let Z := fun x => planeTimeAllMomentCarrierOfCurve (K x + 1) ϖ
    (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)) (w x) (hc.2.1 x)
    (fun n => (hmoment n n (le_refl n) x).2)
  exact ⟨Z, u, w, hs, fun x => planeTimeAllMomentCarrierOfCurve_represents (K x + 1) ϖ
    (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)) (w x) (hc.2.1 x)
    (fun n => (hmoment n n (le_refl n) x).2)⟩
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Windowed metric data suffice for the genuine coupled Taylor error endpoint:
the metric clamp is internal, and the output retains the original coupled
equation, literal residual forcing and all-moment retained curve. -/

universe u v w x

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance actualTaylorWindowEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance actualTaylorWindowEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance actualTaylorWindowEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance actualTaylorWindowEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance actualTaylorWindowEndpointScalarCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance actualTaylorWindowEndpointScalarCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance actualTaylorWindowEndpointFluxCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance actualTaylorWindowEndpointFluxCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem planeRetained_actualTaylor_window_initial_data_endpoint_bound
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
        (_hG_near : CycleWords.IsMetricNearIdentityOn (Set.Icc ta tb) G g)
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
    {P : Type w} {Ctx : P → Type x}
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
        (fun j => planeTimeAllMomentReadout (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Lfull i))
    (_hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t
        (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentReadout (E := h j) (Kslot j + 1) ϖ rstar 0
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
            (fun j => planeTimeAllMomentReadout (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
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
        ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb))
            (-(Q i - Lfull i Wret + Ldiag i Wret)) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret i) (w i)) ∧
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH i tp - u i tp)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0)) := by
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    planeRetained_actualTaylor_initial_data_endpoint_price.{u, v, w, x} Ks Kmax Cjet hCjet
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
  let Gc := metricClamp ta tb G
  let Mc := fun t => M (max ta (min t tb))
  have hGeq t (ht : t ∈ Set.Icc ta tb) : Gc t = G t := metricClamp_of_mem G ht
  have hMeq t (ht : t ∈ Set.Icc ta tb) : Mc t = M t := by
    dsimp only [Mc]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hGcm : Measurable (fun p : Set.Icc ta tb × Vec 2 => Gc p.1 p.2) := by
    convert hG_meas using 1
    funext p
    exact congrFun (hGeq p.1 p.1.2) p.2
  have hGcsym t (ht : t ∈ Set.Icc ta tb) z : (Gc t z).IsSymm := by
    rw [hGeq t ht]
    exact hG_symm t ht z
  have hGcsmooth t (ht : t ∈ Set.Icc ta tb) (k l : Fin 2) :
      ContDiff ℝ (max Kmax 1 : ℕ) (fun z => Gc t z k l) := by
    rw [hGeq t ht]
    exact hG_smooth t ht k l
  have hGcjets t (ht : t ∈ Set.Icc ta tb) z j (hj : 1 ≤ j) (hjmax : j ≤ Kmax) k l :
      ‖iteratedFDeriv ℝ j (fun z' => Gc t z' k l) z‖ ≤ Cjet j * g * δ ^ j := by
    rw [hGeq t ht]
    exact hG_jets t ht z j hj hjmax k l
  have hHc := planeMetricSource_coupled_solution_metricClamp hH
  obtain ⟨hfullAc, hfullCc⟩ := planeMetricSource_coefficient_data_metricClamp
    rstar ta tb hfullA hfullC
  have hdiagEq i j d t (ht : t ∈ Set.Icc ta tb) :
      planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => Mc t - 1) i j d t =
        planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1) i j d t := by
    funext z
    simp only [planeDiagonalGradientCoefficient, hMeq t ht]
  have hdiagAc i j d : coefficientSeminorm rstar (Kslot i) ta tb
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => Mc t - 1) i j d) ≠ ⊤ := by
    rw [coefficientSeminorm_window_congr rstar (Kslot i) ta tb _ _ (hdiagEq i j d)]
    exact hdiagA i j d
  have hdiagCc i j d t (ht : t ∈ Set.Icc ta tb) : ContDiff ℝ (Kslot i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => Mc t - 1) i j d t) := by
    rw [hdiagEq i j d t ht]
    exact hdiagC i j d t ht
  have hRc i := planeComponentAllMomentResponse_metric_window_congr M Mc v
    (Kslot i) ta tb ϖ rstar (R i) (hR i) hMeq
  have hbasec := isPlaneChainFrom_geometryScalarData_congr
    (G := fun t _ => M t) (G' := fun t _ => Mc t)
    (κ := fun _ i => Kslot i)
    (fun t ht => funext (fun _ => hMeq t ht)) hbase
  have hfullc i := planeMetricSource_raw_map_window_congr
    (h := h) (K := Kslot) (D := D) (G := G) (G' := Gc) (A := A)
    (fun (X : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))) j t =>
      planeTimeAllMomentReadout (Kslot j + 1) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) (X j) t)
    i ϖ rstar 0 ta tb (Lfull i) (hfull i) hGeq
  have hdiagc i := planeRaw_coupling_map_window_congr
    (h := h) (K := Kslot) (D := D)
    (A := planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1))
    (A' := planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => Mc t - 1))
    (fun (X : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))) j t =>
      planeTimeAllMomentReadout (Kslot j + 1) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) (X j) t)
    i ϖ rstar 0 ta tb (Ldiag i) (hdiag i) hdiagEq
  have hmetricMapsc i := planeMetric_three_raw_maps_window_congr (E := h i)
    (Kslot i) Ks ϖ rstar ta tb G Gc M Mc hGeq hMeq
    (diag i) (Lmetric i) (Rmetric i) (hDiagComponent i) (hPositive i) (hMetricRemainder i)
  have hdiagComponentc i := (hmetricMapsc i).1
  have hpositivec i := (hmetricMapsc i).2.1
  have hmetricRemc i := (hmetricMapsc i).2.2
  have hMcenterC : Mc = fun t => Gc t 0 := by
    funext t
    exact congrFun hMcenter (max ta (min t tb))
  have hMcm : Measurable Mc := matrix_time_clamp_measurable hMm ta tb
  have hGcHigh t (ht : t ∈ Set.Icc ta tb) k l :
      ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => Gc t z k l) := by
    rw [hGeq t ht]
    exact hGhigh t ht k l
  have hGcLowJet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => Gc t z k l) 0‖ ≤ Cjet r * g * δ ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hGlowjet] with t ht hj
    rw [hGeq t ht]
    exact hj
  have hGcHighJet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, Ks + 1 ≤ r →
      r ≤ Ks + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => Gc t z k l) y‖ ≤ Cjet r * g * (ζslow * ϖ) ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hGhighjet] with t ht hj
    rw [hGeq t ht]
    exact hj
  obtain ⟨Fout, uout, wout, hsol, hFout, hwout, hbound⟩ := hendpoint (ι := ι) (h := h)
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    Gc g hg hg4 hGcm hGcsym (isMetricNearIdentity_metricClamp ht hG_near)
    hGcsmooth hGcjets ϖ (chartWeightsMetricClamp W)
    hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hHc
    Mc R Lmetric Ledge u0 w0 Z hdiagAc hfullAc hdiagCc hfullCc
    family J hdepth Hraw hHzero hTaylorRaw hRc hbasec hZ Lfull Ldiag hfullc hdiagc
    Rs diag Rmetric hMcenterC hSourceRaw hdiagComponentc hpositivec hmetricRemc
    (chartWeightsMetricClamp WM) L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve
    hMcm (metricClamp_time_slice_measurable hGm ta tb) hGcHigh hGcLowJet hGcHighJet
    hrem hgain hN
  let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
    (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
  let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
  let Tret := ∑ k ∈ Finset.range (H + 1), U J k
  let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
  have hcoeffEq i j d t (ht : t ∈ Set.Icc ta tb) :
      planeMetricSourceCoefficient Kslot D G A i j d t =
        planeMetricSourceCoefficient Kslot D Gc A i j d t :=
    planeMetricSourceCoefficient_congr_time (h := h) (K := Kslot) (D := D)
      (G := Gc) (G' := G) (A := A) (hGeq t ht).symm i j d
  have herrorTransfer := planeRaw_coupled_error_window_transfer (h := h)
    Kslot D ta tb ϖ rstar ht hrstar v
    (planeMetricSourceCoefficient Kslot D Gc A)
    (planeMetricSourceCoefficient Kslot D G A)
    (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => Mc t - 1))
    hfullAc hfullCc hdiagAc hdiagCc
    hcoeffEq
    Lfull Ldiag hfullc hdiagc Wret Q Fout wout hFout hwout
    (fun i t => uH i t - uout i t) (fun i t => wH i t - wout i t)
  obtain ⟨ferr, hsolOriginal, hferr⟩ := herrorTransfer hsol
  refine ⟨uout, wout, ferr, ?_, ?_, ?_, ?_⟩
  · exact hsolOriginal
  · exact hferr
  · exact hwout
  · exact hbound

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_cell_coupled_solution
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
    (hcell : e ≠ 0) (yc : Vec 2)
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
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))
      (fun t z => e • normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v
        (e ^ 2 * t) (yc + e • z)) D K
      (fun i i' d t z => (e * (e ^ (d.1 - 1))⁻¹) •
        preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K
          i i' d (e ^ 2 * t) (yc + e • z))
      (fun j => planeCarrierAffine e hcell yc (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) a (f j)))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hr := preparation_reference_normalized_coupled_solution F hab ρ hρ K hdesc hD
    hprep hcover hTau ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs
  exact planeHomogeneous_cell_solution K D (ν * a) (ν * b) e hcell yc
    (normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v)
    (preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K)
    (fun j => preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
      (by have hh := hK j; omega) a (f j))
    (fun j t => preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
      (by have hh := hK j; omega) (ν⁻¹ * t) (u j (ν⁻¹ * t)))
    (fun j t => preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
      (Nat.add_le_add_right (hK j) 1) (ν⁻¹ * t) (w j (ν⁻¹ * t))) hr
end

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_cell_coupled_solution_subwindow
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
    (hcell : e ≠ 0) (yc : Vec 2)
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
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * c)) ((e⁻¹) ^ 2 * (ν * d))
      (fun t z => e • normalizedMaterialVelocity hφ σ ν v
        (e ^ 2 * t) (yc + e • z)) D K
      (fun i i' d t z => (e * (e ^ (d.1 - 1))⁻¹) •
        preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K
          i i' d (e ^ 2 * t) (yc + e • z))
      (fun j => planeCarrierAffine e hcell yc (preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) c (f j)))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hr := preparation_window_reference_normalized_coupled_solution_subwindow F hcd hsub ρ hρ K hdesc hD
    hprep hcover σ hσ ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs
  exact planeHomogeneous_cell_solution K D (ν * c) (ν * d) e hcell yc
    (normalizedMaterialVelocity hφ σ ν v)
    (preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K)
    (fun j => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
      (by have hh := hK j; omega) c (f j))
    (fun j t => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
      (by have hh := hK j; omega) (ν⁻¹ * t) (u j (ν⁻¹ * t)))
    (fun j t => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
      (Nat.add_le_add_right (hK j) 1) (ν⁻¹ * t) (w j (ν⁻¹ * t))) hr
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every actual cover chart supplies the drift and windowed metric data for
 the quantitative homogeneous native endpoint estimate. -/

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρ g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_homogeneous_endpoint_energy
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (ic : Fin (P + 2)) (a b : ℝ) (hab : a ≤ b)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic)
    (hqJ : max Kmax 1 ≤ qJ) (hg4 : g ≤ 1 / 4)
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D H n : ℕ) (hD : 2 ≤ D) (Cw : ℕ → ℝ) (ϖ : ℝ) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let Cjet := fun j => max (CG j) 0
    ∀ (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h i))
      (_hA : ∀ i j d, coefficientSeminorm r (K i) a b (A i j d) ≠ ⊤)
      (_hc : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
      (_hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
      (Bsrc : ℝ)
      (_hrow : ∀ i, ∑ j, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (_hcol : ∀ j, ∑ i, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
      (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
      (V₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (V₀ i) ≠ ⊤)
      (V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Vw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
    ∀ t ∈ Set.Icc a b,
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V i t)) ≤
        ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D Bsrc) ^ (2 * H)) *
          (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) *
            ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V₀ i)) := by
  intro yc G v r Cjet W A hA hc hAm Bsrc hrow hcol rank hrank hzero V₀ hinit V Vw hsol t ht
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hr : 0 < r := div_pos cov.pos.2.2 he
  have hr1 : r ≤ 1 := (div_le_one₀ he).mpr cov.rho_e
  have hδ : 0 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) := div_nonneg he.le hE.le
  have hrδ : r * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ≤ 1 := by
    dsimp only [r]
    rw [div_mul_div_cancel₀ he.ne']
    exact (div_le_one₀ hE).mpr (cov.rho_e.trans heE)
  obtain ⟨hv_bdd, hv_meas, hv_smooth, hv_div, hjets⟩ := windowCover_native_drift_data hΛ hζ hφ cov ic a b hwindow
  obtain ⟨hGnear, hGmeas, _, hGsymm, hGsmooth, hGjets⟩ := windowCover_native_metric_data hΛ hφ cov ic a b hwindow
  exact planeHomogeneous_rank_discounted_endpoint_energy_on n Kmax Cjet Cw D H Bsrc
    π hπ K hK a b hab r (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) hr hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam cov.drift_pos.1 cov.drift_pos.2.1
    cov.drift_pos.2.2 hjets cov.drift_scale cov.drift_small G g cov.g_range.1 hg4
    hGmeas (fun t _ z => hGsymm t z) hGnear
    (fun t ht i j => (hGsmooth t ht i j).of_le (by exact_mod_cast hqJ))
    (fun t ht z j hj hjK i k => hGjets t ht z j hj (hjK.trans ((le_max_left Kmax 1).trans hqJ)) i k)
    ϖ 0 W hr1 hD A hA hc hAm hrow hcol rank hrank hzero V₀ hinit V Vw hsol t ht

end AVRegularity.CycleJointProofs
end
end

section
/-! The same actual preparation source carries both its Schur estimate and its
original natural Taylor remainder estimate. The Schur constant precedes all
family data and even the chosen Taylor order. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem preparation_reference_cell_source_maps_with_schur_and_remainder (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b ϖ : ℝ) (_hab : a ≤ b),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        0 ≤ ocTauPP α q Λ m → 0 ≤ ocA α q Λ (m - 1) →
        ∀ ζ : ℝ, 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ →
        e / ocEpsilon q Λ (m - 1) = ζ * ϖ →
        (∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) →
    ∃ T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    (((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
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
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π
      (fun v => Lfull v W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hschur⟩ := preparation_reference_cell_source_subwindow_schur_budget
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB hc henv
    yc a b ϖ hab hsub θ hrow hcol Ks hdesc hKs hθ hTau ha ζ hϖ hscale hζ hδ htime
  obtain ⟨T, Lfull, hsplit, hrem⟩ := exists_preparationReferenceCellSourceMaps_with_remainder_budget
    F hc ν e ρ hν hρ hρe heE actual K hdesc Ks yc a b ϖ hab Kmax Jm hK hchart _hmol
    Cm hmeas hwmeas π hπ B hB henv hsub hKs θ hθ hrow hcol hTau ha ζ hϖ hscale hζ hδ htime
  have he : 0 < e := hρ.trans_le hρe
  have hr : 0 < ρ / e := div_pos hρ he
  obtain ⟨hA, hC, _, _⟩ := preparationReferenceCellSource_pointwise_subwindow_data F hc ν e ρ
    hν hρ hρe heE K Kmax Jm hK hchart _hmol Cm hmeas hwmeas actual yc π hπ B hB henv
    a b (ρ / e) hsub
  have hentry := hschur α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv yc a b hsub
  have hrow' v : ∑ u, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ := by
    calc
      _ ≤ ∑ u, Cprep * B v u := Finset.sum_le_sum (fun u _ => hentry v u)
      _ = Cprep * ∑ u, B v u := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow v) (zero_le_one.trans hCprep)
  have hcol' u : ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ := by
    calc
      _ ≤ ∑ v, Cprep * B v u := Finset.sum_le_sum (fun v _ => hentry v u)
      _ = Cprep * ∑ v, B v u := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol u) (zero_le_one.trans hCprep)
  refine ⟨T, Lfull, ⟨hsplit, hrem⟩, ?_, hrow', hcol'⟩
  intro W n
  exact planeRaw_allMoment_coupling_mass_budget hab ϖ (ρ / e) hr K D _ hA hC Lfull hsplit.1
    π hπ (Cprep * θ) hrow' hcol' W n

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_cell_metric_source_coupled_solution
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
    (hcell : e ≠ 0) (yc : Vec 2)
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
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))
      (fun t z => e • normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v
        (e ^ 2 * t) (yc + e • z)) D K
      (planeMetricSourceCoefficient K D
        (fun t z => CycleReference.chartMetric hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e E actual K yc))
      (fun j => planeCarrierAffine e hcell yc (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) a (f j)))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hh := preparation_reference_cell_coupled_solution F hab ρ hρ K hdesc hD
    hprep hcover hTau ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm
    hcell yc f u w hs
  have hcoeff : (fun i i' d t z => (e * (e ^ (d.1 - 1))⁻¹) •
        preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K
          i i' d (e ^ 2 * t) (yc + e • z)) = (planeMetricSourceCoefficient K D
        (fun t z => CycleReference.chartMetric hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e E actual K yc)) := by
    exact preparationReferenceCellCoefficient_eq_metricSource F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν e E actual K yc hcell
  rw [hcoeff] at hh
  exact hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Every covered time trace of the actual homogeneous preparation family is linear. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_homogeneous_family_native_trace_linearMap (K : ι → ℕ) (Kmax : ℕ)
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
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (u : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : ∀ x, IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x))
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hcover : Set.Icc a b ⊆ ⋃ p, (family.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (he : e ≠ 0) (yc : Vec 2) :

    ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ x i, T x i = preparationReferenceCellNativeCurve hprep hcover hTau ha
        (K i) (by have hh := hK i; omega) ν e he yc (u x i) ((e⁻¹) ^ 2 * (ν * t)) := by
  obtain ⟨Tp, hTp⟩ := actualPreparation_homogeneous_family_trace_linearMap K Kmax hK
    ρ ν hρ hν a b hab D family H hdepth α q Λ m Φ ζ hΦ φ hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual hmeas hwmeas hE hρe heE
    Jm hchart hmol Cm π hπ A hA hpointwise lf u w hsol t ht
  refine ⟨preparationReferenceCellTraceLinearMap hprep hcover hTau ha K
    (fun i => by have hh := hK i; omega) e he yc t ht Tp, ?_⟩
  intro x i
  exact preparationReferenceCellTraceLinearMap_native_curve hprep hcover hTau ha K
    (fun i => by have hh := hK i; omega) e he yc t ht Tp u hTp ν hν.ne' x i

end AVRegularity.CycleJointProofs
end
end
