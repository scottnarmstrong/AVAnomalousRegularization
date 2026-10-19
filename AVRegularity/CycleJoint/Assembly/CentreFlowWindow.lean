-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellMetricStoredWordResidualTimeIntegrability
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
import AVRegularity.CycleJoint.ScalarWeightedJetSumMemL2
public import AVRegularity.CycleJoint.PeriodizedCompactCoefficientPairingIntegrable
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Weighted.BoundedWeightRoot
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.Gronwall

section
/-! **Level B of the route to `cycle_joint`: the core from patches**.

`RawJointStatement` (the core of level A) follows from five statements about one level `m`,
one family and its premises, bundled in `JointPremises`:

* `PatchJointStatement`: for every patch `j` of the torus
  partition at mesh `1/N ≍ R/8` (`R = √(B τ'')`), ONE linear patch model `M_j` from torus `L²`
  data to plane fields with
  - scaled jets at radius `c R` through order `Mout`, weighted by `⟨(x - y'_j)/R⟩^{2n}` around the
    transported patch centre `y'_j` (the position at `t_p` of the particle at the centre at
    `t_S`);
  - for the plane solution from the patch-localized datum: the physical error at radius `ρ_*`,
    with weight `⟨(x - y'_j)/R⟩^{2n}`, of size `C_P E^P` times the localized prepared norm
    (the seam discard and the native geometry error are both moment-weighted);
  - the same error bound at slot `0` for families without edges.
  
* `PlaneTorusStatement`: plane solutions from the patch-localized data exist with finite
  radial moments, and the torus solution at `t_p` is the sum of their lattice periodizations
  (`periodizeRadialPlaneCarrier`).
* `PeriodizedSumStatement`: the factorial norms of a sum of periodizations of plane fields
  around centres obeying the counting bound are at most the counting constant times the weighted
  norms (pointwise Cauchy–Schwarz).
* `CentreCountingStatement`: the transported patch centres obey the counting bound.
* `ScalarContractionStatement`: torus solutions without sources are `L²` contractions.

The model and the error are both summed by `PeriodizedSumStatement` with the weight `⟨⋅/R⟩^{2n}`, so no patch-count
factor is lost. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The transported centre of the patch `j`: the position at `t_p` of the particle that sits at
the patch centre `j/N` at `t_S` (background flow of the stream `Φ (m-1)`). -/
noncomputable def patchOutputCentre (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (tS tp : ℝ) (N : ℕ) (j : Fin 2 → Fin N) : Vec 2 :=
  streamFlow φ hφ tp (spatialPatchCentre N (fun i => (j i : ℤ))) tS

/-- The premises of `cycle_joint` at one level, for one family, with duration `2 τ''`
(the binders of `RawJointStatement` after the constants, bundled). -/
structure JointPremises (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ) : Prop where
  hπ : ∀ x, 0 < π x
  hK : ∀ x, K x ≤ Kmax
  hΦ : IsOCStreamSeq α q Λ ζ Φ
  hband : IsOCBandChain α q Λ ζ M' κ
  hm2 : 2 ≤ m
  hmStar : mStar ≤ m
  hmM : m ≤ M'
  hν : κ m = ν
  hB : κ (m - 1) = B
  cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
    (ocRhoMol α q Λ m cMol ν) g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀
  hwmeas : ∀ p, Measurable (F.weight p)
  hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
    tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F
  hdepth : F.HasDepthAtMost H
  hdesc : F.IsDescending K
  htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1))
  hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output
  hmeas : F.IsTimeMeasurable
  hΘ₀ : 0 ≤ Θ
  hΘ₁ : Θ ≤ 1
  henv : IsEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
    (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm
  hpointwise : IsPointwiseMolecularEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
    Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)
  htrans : F.IsTransverseOnPulses
    (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
      (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1)
  hquiet : F.IsFastIndependentOn
    (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
  hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
    ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)
  hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤ Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))

/-- **The premises at an abstract radius**: `JointPremises`
with the cascade radius `ocRhoMol α q Λ m cMol ν` replaced by a radius `r` (window cover,
envelopes) and the prepared radius `ρold` constrained by `0 < ρold`, `ρold ≤ COld √(B τ'')` and
the ratio `r / ρold ≤ Crat ε_{m−1}^{−qδ}`. -/
structure JointPremisesGen (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ) : Prop where
  hπ : ∀ x, 0 < π x
  hK : ∀ x, K x ≤ Kmax
  hΦ : IsOCStreamSeq α q Λ ζ Φ
  hband : IsOCBandChain α q Λ ζ M' κ
  hm2 : 2 ≤ m
  hmStar : mStar ≤ m
  hmM : m ≤ M'
  hν : κ m = ν
  hB : κ (m - 1) = B
  cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
    r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀
  hwmeas : ∀ p, Measurable (F.weight p)
  hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
    tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F
  hdepth : F.HasDepthAtMost H
  hdesc : F.IsDescending K
  htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1))
  hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output
  hmeas : F.IsTimeMeasurable
  hΘ₀ : 0 ≤ Θ
  hΘ₁ : Θ ≤ 1
  henv : IsEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
    (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm
  hpointwise : IsPointwiseMolecularEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
    Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)
  htrans : F.IsTransverseOnPulses
    (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
      (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1)
  hquiet : F.IsFastIndependentOn
    (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
  hρpos : 0 < ρold
  hρR : ρold ≤ COld * Real.sqrt (B * ocTauPP α q Λ m)
  hρrat : r / ρold ≤ Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))

section PatchClauses

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- Componentwise truncation of plane fields to lower orders. -/
noncomputable def planeFamilyTruncation (K L : ι → ℕ) (hKL : ∀ i, K i ≤ L i) :
    (∀ i, PlaneHk Set.univ (L i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
  LinearMap.pi fun i => (truncatePlaneHk (hKL i)).toLinearMap.comp (LinearMap.proj i)

/-- The error clause of one patch model `M` for the plane solutions from the localized datum at
slots `K`: the error at `t_p`, at radius `ρs`, with weight `⟨(x - y)/R⟩^{2n}`, is `ε²` times the
`ρold`-prepared norm of the localized datum (mass-weighted). -/
def IsPatchError (π : ι → ℝ) (K : ι → ℕ) (Mout D : ℕ) (ν tS tp ρs ρold R ε : ℝ) (n : ℕ)
    (y : Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (loc : ∀ i, TorusHk (K i) (h i) →ₗ[ℝ] PlaneHk Set.univ (K i) (h i))
    (M : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i))) : Prop :=
  ∀ (f : ∀ i, TorusHk (K i) (h i))
    (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane ν tS tp b D K A (fun i => loc i (f i))
      (fun _ _ => 0) (fun _ _ => 0) U W →
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y ρs (K i)
        (U i tp - truncatePlaneHk (le_max_right Mout (K i))
          (M (fun i => truncateTorusHk (Nat.zero_le _) (f i)) i)) ≤
      ENNReal.ofReal (ε ^ 2 * ∑ i, (π i)⁻¹ * factorialNormSq ρold (loc i (f i)).val)

end PatchClauses

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The conclusion of `PatchJointStatement` for one family at one level, over generic window data: the scale `R`,
the endpoint `tp`, the radii `ρs`, `ρold`, the accuracy `ε`, the patch output centres `y`, the
drift `b`, the coefficients at slots `K` and `0`, and the edge-freeness `edgeFree`. For every patch
mesh `8 ≤ N R ≤ 9` and every patch `j`: ONE linear patch model with the weighted model bound,
radial moments, and the weighted physical errors at slots `K` and (edge-free) `0`. -/
def PatchModelsGen {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Mout D : ℕ) (C c ε : ℝ) (n : ℕ)
    (π : ι → ℝ) (K : ι → ℕ) (ν tS tp ρs ρold R : ℝ)
    (y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop) : Prop :=
  ∀ (N : ℕ) (hN : 0 < N), 8 ≤ (N : ℝ) * R → (N : ℝ) * R ≤ 9 →
    ∀ j : Fin 2 → Fin N,
    ∃ Mj : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)),
      (∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n R⁻¹ (y N j) (c * R) Mout (Mj f i) ≤
        ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
          ‖spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f i)‖ ^ 2)) ∧
      (∀ f i, CycleJointProofs.HasRadialPlaneMoments (Mj f i) (y N j)) ∧
      IsPatchError π K Mout D ν tS tp ρs ρold R ε n (y N j) b A
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i)) Mj ∧
      (edgeFree →
        IsPatchError π (fun _ => 0) Mout D ν tS tp ρs ρold R ε n (y N j) b A0
          (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0)
          ((planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
            (fun _ => max_le_max le_rfl (Nat.zero_le _))) ∘ₗ Mj))

/-- The conclusion of `PlaneTorusStatement` for one family at one level, over generic window data, at one patch
mesh `N`. -/
def PlaneTorusGen {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (D : ℕ) (K : ι → ℕ) (ν tS tp : ℝ)
    (N : ℕ) (hN : 0 < N) (y : (Fin 2 → Fin N) → Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop) : Prop :=
  (∀ f : ∀ i, TorusHk (K i) (h i),
    ∃ (U : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (W : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      (∀ j, IsCoupledWeakSolutionPlane ν tS tp b D K A
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
        (fun _ _ => 0) (fun _ _ => 0) (U j) (W j)) ∧
      ∃ hmU : ∀ j i, CycleJointProofs.HasRadialPlaneMoments (U j i tp) (y j),
      ∀ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
        IsCoupledWeakSolutionTorus ν tS tp b D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
        ∀ i, u i tp = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j i tp) (y j)
          (hmU j i)) ∧
  (edgeFree → ∀ f : ∀ i, TorusHk 0 (h i),
    (∃ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
      IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0) (fun _ _ => 0)
        u w) ∧
    ∃ (U : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ 0 (h i))
      (W : (Fin 2 → Fin N) → ∀ i, ℝ → PlaneHk Set.univ 1 (h i)),
      (∀ j, IsCoupledWeakSolutionPlane ν tS tp b D (fun _ => 0) A0
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 (f i))
        (fun _ _ => 0) (fun _ _ => 0) (U j) (W j)) ∧
      ∃ hmU : ∀ j i, CycleJointProofs.HasRadialPlaneMoments (U j i tp) (y j),
      ∀ (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
        IsCoupledWeakSolutionTorus ν tS tp b D (fun _ => 0) A0 f (fun _ _ => 0)
          (fun _ _ => 0) u w →
        ∀ i, u i tp = ∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (U j i tp) (y j)
          (hmU j i))

end Generic

/-- The conclusion of `PatchJointStatement` for one family at one level (the generic form at the window data of
`cycle_joint`). -/
abbrev PatchModelsAt (α q : ℝ) (Λ : ℕ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Pacc : ℝ) (Mout D : ℕ)
    (cMol C CP c : ℝ) (n : ℕ) {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS : ℝ) (l₀ : ℤ)
    {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (ρold : ℝ) : Prop :=
  PatchModelsGen hζ Mout D C c (CP * ocEpsilon q Λ (m - 1) ^ Pacc) n π K ν tS
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold
    (Real.sqrt (B * ocTauPP α q Λ m))
    (fun N j => patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
    (streamVel (Φ m)) (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
    (∀ v u, IsEmpty (F.Γ v u))

/-- **One patch.** The constants precede the family and the patch; the
patch model is ONE linear operator carrying the model bound and both error clauses. -/
def PatchJointStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 / 8 ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
        0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar n : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧ 4 ≤ n ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ),
        JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
          Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
          A Θ T ρold →
        PatchModelsAt α q Λ hζ Pacc Mout D cMol C CP c n π K Φ m ν B hφ tS l₀ F actual ρold

/-- The conclusion of `PlaneTorusStatement` for one family at one level and one patch mesh `N` (the generic form
at the window data of `cycle_joint`). -/
abbrev PlaneTorusAt (α q : ℝ) (Λ : ℕ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (D : ℕ)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (ν : ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (tS : ℝ) (l₀ : ℤ) {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
    (actual : ∀ p, Ctx p) (N : ℕ) (hN : 0 < N) : Prop :=
  PlaneTorusGen hζ D K ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N hN
    (fun j => patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
    (streamVel (Φ m)) (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
    (∀ v u, IsEmpty (F.Γ v u))

/-- **Plane solutions and periodization.** At one level and for one family with the
premises: for every torus datum, plane solutions from the patch-localized data exist with finite
radial moments at `t_p` around the transported patch centres, and every torus solution at `t_p` is
the sum over the patches of their lattice periodizations; the same at slot `0` for families
without edges, where the torus solution is also asserted to exist. -/
def PlaneTorusStatement : Prop :=
  ∀ (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (_hΛ : 128 ≤ Λ) (g₀ : ℝ)
    (H D Kmax Ks Ls Jm qJ Jchart : ℕ) (_hD : 2 ≤ D)
    (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    (_hcMol : 0 < cMol)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)
    (_hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T ρold)
    (N : ℕ) (hN : 0 < N),
    PlaneTorusAt α q Λ hζ D K Φ m ν hφ tS l₀ F actual N hN

/-- The counting weight `(1 + ϖ² |z + n - y|²)^{-n}` of the lattice image `n` of a centre `y`. -/
noncomputable def latticeCountWeight (ϖ : ℝ) (n : ℕ) (z y : Vec 2) (k : Fin 2 → ℤ) : ℝ :=
  ((1 + ϖ ^ 2 * ((z 0 + k 0 - y 0) ^ 2 + (z 1 + k 1 - y 1) ^ 2)) ^ n)⁻¹

/-- **Periodized sums.** A linear family of plane fields with finite weighted norms around
centres whose lattice images obey the counting bound `Cc` at scale `R ≤ 1` has a linear torus
periodization `Y`: the lattice series converge a.e. on the cell, `Y v` has the jets of their sum,
and every truncated factorial norm of `Y v` is at most `Cc` times the sum of the weighted norms
(pointwise Cauchy–Schwarz against the counting weights, then unfolding of the lattice sum). -/
def PeriodizedSumStatement : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {V : Type w} [AddCommGroup V] [Module ℝ V]
    {J : Type} [Fintype J] (y : J → Vec 2) (R Cc : ℝ) (n : ℕ) (_hR : 0 < R) (_hR1 : R ≤ 1)
    (_hn : 2 ≤ n)
    (_hcount : ∀ z : Vec 2, Summable (fun p : J × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y p.1) p.2) ∧
      ∑' p : J × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y p.1) p.2 ≤ Cc)
    (K : ℕ) (G : J → V →ₗ[ℝ] PlaneHk Set.univ K E)
    (_hG : ∀ j v, weightedFactorialNormSq n R⁻¹ (y j) 1 K (G j v) ≠ ⊤),
    ∃ Y : V →ₗ[ℝ] TorusHk K E,
      (∀ v j α', ∀ᵐ z ∂(volume.restrict AVenhance.unitCube),
        Summable (fun k : Fin 2 → ℤ =>
          (G j v).toFunction.jet α' (z + AVenhance.latticeShift k))) ∧
      (∀ v α', (Y v).val α' =ᵐ[volume.restrict AVenhance.unitCube]
        fun z => ∑ j, periodizeRawJet ((G j v).toFunction.jet) α' z) ∧
      ∀ v (k : ℕ) (hk : k ≤ K) (r : ℝ),
        ENNReal.ofReal (factorialNormSq r (truncateTorusHk hk (Y v)).val) ≤
          ENNReal.ofReal Cc * ∑ j, weightedFactorialNormSq n R⁻¹ (y j) r k (G j v)

/-- **Periodized sums (radial form, used by the level-B assembly).** For plane fields with finite radial moments around centres whose
lattice images obey the counting bound `Cc` at scale `R ≤ 1`, every truncated factorial norm of
the sum of their lattice periodizations is at most `Cc` times the sum of their weighted norms
(pointwise Cauchy–Schwarz against the counting weights, then unfolding of the lattice sum). -/
def PeriodizedRadialSumStatement : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {J : Type} [Fintype J] (y : J → Vec 2) (R Cc : ℝ) (n : ℕ) (_hR : 0 < R) (_hR1 : R ≤ 1)
    (_hn : 2 ≤ n)
    (_hcount : ∀ z : Vec 2, Summable (fun p : J × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y p.1) p.2) ∧
      ∑' p : J × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y p.1) p.2 ≤ Cc)
    (K : ℕ) (G : J → PlaneHk Set.univ K E)
    (hm : ∀ j, CycleJointProofs.HasRadialPlaneMoments (G j) (y j)) (k : ℕ) (hk : k ≤ K) (r : ℝ)
    (_hr : 0 < r),
    ENNReal.ofReal (factorialNormSq r
        (truncateTorusHk hk (∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j) (hm j))).val) ≤
      ENNReal.ofReal Cc * ∑ j, weightedFactorialNormSq n R⁻¹ (y j) r k (G j)

/-- **Counting of the transported patch centres.** For an admissible stream whose
velocity gradient is at most `g ≤ 1/8` in units of `1/T` on `[tS, tp]`, `tp - tS ≤ 2T`, and a
patch mesh `8 ≤ N R ≤ 9`, the lattice images of the transported centres obey the counting bound
with a constant depending only on `n`. -/
def CentreCountingStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (tS tp T g R : ℝ) (N : ℕ),
      tS ≤ tp → tp - tS ≤ 2 * T → 0 < T → 0 ≤ g → g ≤ 1 / 8 →
      (∀ t ∈ Set.Icc tS tp, ∀ y : Vec 2, T * ‖fderiv ℝ (streamVel φ t) y‖ ≤ g) →
      0 < R → 8 ≤ (N : ℝ) * R → (N : ℝ) * R ≤ 9 →
      ∀ z : Vec 2,
        Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) =>
          latticeCountWeight R⁻¹ n z (patchOutputCentre φ hφ tS tp N p.1) p.2) ∧
        ∑' p : (Fin 2 → Fin N) × (Fin 2 → ℤ),
          latticeCountWeight R⁻¹ n z (patchOutputCentre φ hφ tS tp N p.1) p.2 ≤ Cc

/-- **Scalar `L²` contraction.** A torus solution of the source-free equation with a stream
drift does not increase the `L²` norm of any component. -/
def ScalarContractionStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (φ : ℝ → Vec 2 → ℝ) (_hφ : IsAdmissibleStream φ) (ν t₀ t₁ : ℝ) (_hν : 0 < ν) (D : ℕ)
    (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
    IsCoupledWeakSolutionTorus ν t₀ t₁ (streamVel φ) D (fun _ => 0) (fun _ _ _ _ _ => 0) f
      (fun _ _ => 0) (fun _ _ => 0) u w →
    ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖u i t‖ ≤ ‖f i‖

/-- **Scalar `L²` contraction (vanishing-coefficient form, used by the level-B assembly).** A torus solution of the
source-free equation (all coupling coefficients vanish) with a stream drift does not increase the `L²` norm of any component. -/
def ScalarContractionVanishingStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (φ : ℝ → Vec 2 → ℝ) (_hφ : IsAdmissibleStream φ) (ν t₀ t₁ : ℝ) (_hν : 0 < ν) (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (_hA : ∀ i i' d t z, A i i' d t z = 0)
    (f : ∀ i, TorusHk 0 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i)) (w : ∀ i, ℝ → TorusHk 1 (h i)),
    IsCoupledWeakSolutionTorus ν t₀ t₁ (streamVel φ) D (fun _ => 0) A f
      (fun _ _ => 0) (fun _ _ => 0) u w →
    ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖u i t‖ ≤ ‖f i‖


/-- **The one-patch statement at an abstract radius** (the generic form of `PatchModelsAt`): the error radius is `r`. -/
abbrev PatchModelsAtGen (α q : ℝ) (Λ : ℕ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Pacc : ℝ) (Mout D : ℕ)
    (C CP c : ℝ) (n : ℕ) {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS : ℝ) (l₀ : ℤ)
    {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (r ρold : ℝ) : Prop :=
  PatchModelsGen hζ Mout D C c (CP * ocEpsilon q Λ (m - 1) ^ Pacc) n π K ν tS
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) r ρold
    (Real.sqrt (B * ocTauPP α q Λ m))
    (fun N j => patchOutputCentre (Φ (m - 1)) hφ tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) N j)
    (streamVel (Φ m)) (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (fun _ => 0))
    (∀ v u, IsEmpty (F.Γ v u))

/-- **The one-patch statement at an abstract radius**: `PatchJointStatement` over `JointPremisesGen`, concluding
the patch models at the error radius `r`. The constants precede the family and the radius;
`PatchJointStatement` is its instance at the cascade radius (`patchJoint_of_gen`). -/
def PatchJointGenStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 / 8 ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
      ∃ (C CP c : ℝ) (mStar n : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧ 4 ≤ n ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ),
        JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
          Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
          A Θ T r ρold →
        PatchModelsAtGen α q Λ hζ Pacc Mout D C CP c n π K Φ m ν B hφ tS l₀ F actual r ρold

/-- **The plane-solution statement at an abstract radius**: `PlaneTorusStatement` over `JointPremisesGen` (the conclusion has
no radius); it follows from `PlaneTorusStatement` (`planeTorusGen_of`). -/
def PlaneTorusGenStatement : Prop :=
  ∀ (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (_hΛ : 128 ≤ Λ) (g₀ : ℝ)
    (H D Kmax Ks Ls Jm qJ Jchart : ℕ) (_hD : 2 ≤ D)
    (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (_hprem : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (N : ℕ) (hN : 0 < N),
    PlaneTorusAt α q Λ hζ D K Φ m ν hφ tS l₀ F actual N hN

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The joint premises at slot `0` for an edge-free family**.

The slots enter the joint premises only through the edges of the family: descent
(`IsDescending`), the molecular and pointwise envelopes (sums over the edges and the smoothness
of the edge fluxes). For a family without edges they hold at every slot assignment, in particular
at slot `0`, which is where the edge-free `L²` clause is posed.

The empty family has no edges, so the conditions hold vacuously. -/

@[expose] public section

open Homogenization AVenhance

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- **The joint premises at slot `0` for an edge-free family.** -/
theorem JointPremisesGen.slotZero
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hedge : ∀ v u, IsEmpty (F.Γ v u)) :
    JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π (fun _ => 0) Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F
      actual A Θ T r ρold :=
  { hp with
    hK := fun _ => Nat.zero_le _
    hdesc := fun v u γ => (hedge v u).elim γ
    henv :=
      { nonneg := hp.henv.nonneg
        row_sum := hp.henv.row_sum
        col_sum := hp.henv.col_sum
        analytic := hp.henv.analytic
        molecular := ⟨fun _ _ v u γ => (hedge v u).elim γ, fun v u j _ => by
          simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, zero_le]⟩ }
    hpointwise := ⟨fun _ _ v u γ => (hedge v u).elim γ, fun v u j _ => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, zero_le]⟩ }

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! Weighted Cauchy--Schwarz for the actual countable lattice series. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Finite weighted vector sums retain the exact reciprocal-weight counting constant. -/
theorem finite_weighted_norm_sq {I : Type*} (s : Finset I) (f : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, (w i)⁻¹) * ∑ i ∈ s, w i * ‖f i‖ ^ 2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i _ => (inv_pos.mpr (hw i)).le)
    (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
  intro i _
  rw [← mul_assoc, inv_mul_cancel₀ (hw i).ne', one_mul]

omit [NormedSpace ℝ E] in
/-- Finite reciprocal weight and finite weighted energy give absolute convergence. -/
theorem weighted_series_summable {I : Type*} (f : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (hweight : Summable (fun i => (w i)⁻¹))
    (henergy : Summable (fun i => w i * ‖f i‖ ^ 2)) : Summable f := by
  let a := fun i => Real.sqrt ((w i)⁻¹)
  let b := fun i => Real.sqrt (w i * ‖f i‖ ^ 2)
  have ha : Summable (fun i => a i ^ (2 : ℝ)) := hweight.congr (fun i => by
    dsimp only [a]
    rw [Real.rpow_two, Real.sq_sqrt (inv_nonneg.mpr (hw i).le)])
  have hb : Summable (fun i => b i ^ (2 : ℝ)) := henergy.congr (fun i => by
    dsimp only [b]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw i).le (sq_nonneg _))])
  have hs := Real.summable_mul_of_Lp_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (fun i => Real.sqrt_nonneg ((w i)⁻¹)) (fun i => Real.sqrt_nonneg (w i * ‖f i‖ ^ 2)) ha hb
  have he (i : I) : a i * b i = ‖f i‖ := by
    dsimp only [a, b]
    rw [← Real.sqrt_mul (inv_nonneg.mpr (hw i).le), ← mul_assoc,
      inv_mul_cancel₀ (hw i).ne', one_mul, Real.sqrt_sq (norm_nonneg _)]
  exact Summable.of_norm (hs.congr he)

omit [NormedSpace ℝ E] in
/-- The convergent series satisfies the same exact bound as its finite partial sums. -/
theorem weighted_series_norm_sq {I : Type*} (f : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (hweight : Summable (fun i => (w i)⁻¹))
    (henergy : Summable (fun i => w i * ‖f i‖ ^ 2)) :
    ‖∑' i, f i‖ ^ 2 ≤ (∑' i, (w i)⁻¹) * ∑' i, w i * ‖f i‖ ^ 2 := by
  classical
  have hs := weighted_series_summable f w hw hweight henergy
  apply le_of_tendsto (hs.hasSum.norm.pow 2)
  apply Filter.Eventually.of_forall
  intro s
  apply (finite_weighted_norm_sq s f w hw).trans
  exact mul_le_mul
    (hweight.sum_le_tsum s (fun i _ => (inv_pos.mpr (hw i)).le))
    (henergy.sum_le_tsum s (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)))
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)))
    (tsum_nonneg (fun i => (inv_pos.mpr (hw i)).le))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **Word sums as linear maps**.

The old word chains of the two-block theorem are linear in the datum word by word. `wordSumPi s f` sums the word
maps `f w` over a word set `s` on the extended datum space `List Bool → X` (one datum per word),
and `wordDiag s` puts the same datum on every word of `s`. On `wordDiag s ξ` the sum is the sum of
the `f w ξ`; on `Pi.single w ξ` it is `f w ξ` alone. This is how the future chains of the two-block theorem are
started from one old word at a time while the error estimates see the summed datum.
`weightedFactorialNormSq_finset_sum_ne_top`: finite sums keep finite moments. -/

section Maps

variable {X V : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]

/-- The same datum on every word of `s`, zero on the other words. -/
def wordDiag (s : Finset (List Bool)) : X →ₗ[ℝ] (List Bool → X) :=
  ∑ w ∈ s, LinearMap.single ℝ (fun _ : List Bool => X) w

theorem wordDiag_apply (s : Finset (List Bool)) (ξ : X) :
    wordDiag s ξ = ∑ w ∈ s, Pi.single w ξ := by
  simp only [wordDiag, LinearMap.sum_apply, LinearMap.coe_single]

theorem wordDiag_apply_of_mem (s : Finset (List Bool)) (ξ : X) {w : List Bool} (hw : w ∈ s) :
    wordDiag s ξ w = ξ := by
  rw [wordDiag_apply, Finset.sum_apply, Finset.sum_eq_single w]
  · exact Pi.single_eq_same (M := fun _ : List Bool => X) w ξ
  · intro w' _ hw'
    exact Pi.single_eq_of_ne' (M := fun _ : List Bool => X) hw' ξ
  · exact fun h => absurd hw h

/-- A word map that is additive and homogeneous on the words of `s` vanishes at `0` there. -/
theorem wordMap_zero (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ')
    {w : List Bool} (hw : w ∈ s) : f w 0 = 0 := by
  have h := hf w hw 1 0 0
  rw [smul_zero, add_zero, one_smul] at h
  exact left_eq_add.mp h

/-- The sum over the words of `s` of the word maps, one datum per word. -/
def wordSumPi (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ') :
    (List Bool → X) →ₗ[ℝ] V where
  toFun η := ∑ w ∈ s, f w (η w)
  map_add' η η' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h := hf w hw 1 (η w) (η' w)
    rw [one_smul, one_smul] at h
    exact h
  map_smul' c η := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h := hf w hw c (η w) 0
    rw [add_zero, wordMap_zero s f hf hw, add_zero] at h
    exact h

theorem wordSumPi_apply (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ')
    (η : List Bool → X) : wordSumPi s f hf η = ∑ w ∈ s, f w (η w) := rfl

theorem wordSumPi_diag (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ') (ξ : X) :
    wordSumPi s f hf (wordDiag s ξ) = ∑ w ∈ s, f w ξ := by
  rw [wordSumPi_apply]
  exact Finset.sum_congr rfl fun w hw => by rw [wordDiag_apply_of_mem s ξ hw]

/-- The sum over the words of `s` of the word maps, one datum for all words. -/
def wordSum (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ') :
    X →ₗ[ℝ] V where
  toFun ξ := ∑ w ∈ s, f w ξ
  map_add' ξ ξ' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h := hf w hw 1 ξ ξ'
    rw [one_smul, one_smul] at h
    exact h
  map_smul' c ξ := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h := hf w hw c ξ 0
    rw [add_zero, wordMap_zero s f hf hw, add_zero] at h
    exact h

theorem wordSum_apply (s : Finset (List Bool)) (f : List Bool → X → V)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (ξ ξ' : X), f w (c • ξ + ξ') = c • f w ξ + f w ξ') (ξ : X) :
    wordSum s f hf ξ = ∑ w ∈ s, f w ξ := rfl

end Maps

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Finite sums keep finite weighted moments. -/
theorem weightedFactorialNormSq_finset_sum_ne_top {α : Type*} {K : ℕ} (n : ℕ) (ϖ : ℝ)
    (zc : Vec 2) (ρ : ℝ) (s : Finset α) (U : α → PlaneHk Set.univ K E)
    (hU : ∀ a ∈ s, weightedFactorialNormSq n ϖ zc ρ K (U a) ≠ ⊤) :
    weightedFactorialNormSq n ϖ zc ρ K (∑ a ∈ s, U a) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Weighted.weightedFactorialNormSq_zero_carrier]
    exact ENNReal.zero_ne_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine ne_top_of_le_ne_top ?_ (CycleWords.weightedFactorialNormSq_add_le n ϖ zc ρ _ _)
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.mpr
      ⟨hU a (Finset.mem_insert_self a s),
        ih fun b hb => hU b (Finset.mem_insert_of_mem hb)⟩)

/-- A word map that is linear on the words of `s` commutes with finite sums of data, for maps
with values in `PlaneHk`, stated with the arithmetic elaborated on `PlaneHk` itself (as in the
word-chain statements), so that their linearity clauses apply without converting instance
paths. -/
theorem planeWordMap_finset_sum {Y : Type*} [AddCommGroup Y] [Module ℝ Y] {k : ℕ}
    (s : Finset (List Bool)) (f : List Bool → Y → PlaneHk Set.univ k E)
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y), f w (c • η + η') = c • f w η + f w η')
    {w : List Bool} (hw : w ∈ s) {α : Type*} (t : Finset α) (η : α → Y) :
    f w (∑ a ∈ t, η a) = ∑ a ∈ t, f w (η a) := by
  classical
  have h0 : f w 0 = 0 := by
    have h := hf w hw 1 0 0
    rw [smul_zero, add_zero, one_smul] at h
    exact left_eq_add.mp h
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have h := hf w hw 1 (η a) (∑ b ∈ t, η b)
    rw [one_smul, one_smul] at h
    exact h

/-- Summing the single-word data over the words of `s` gives the diagonal datum `wordDiag s ξ`,
for maps with values in `PlaneHk` (see `planeWordMap_finset_sum`). -/
theorem planeWordSum_single_comm {X : Type*} [AddCommGroup X] [Module ℝ X] {k : ℕ}
    (s t : Finset (List Bool)) (f : List Bool → (List Bool → X) → PlaneHk Set.univ k E)
    (hf : ∀ w ∈ t, ∀ (c : ℝ) (η η' : List Bool → X), f w (c • η + η') = c • f w η + f w η')
    (ξ : X) :
    ∑ wo ∈ s, ∑ wf ∈ t, f wf (Pi.single (M := fun _ : List Bool => X) wo ξ) =
      ∑ wf ∈ t, f wf (wordDiag s ξ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun wf hwf => ?_
  rw [wordDiag_apply]
  exact (planeWordMap_finset_sum t f hf hwf s _).symm

end Moments

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Finite weighted factorial budgets control the complete plane Hilbert carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Asking for orders above the stored order adds only zero jets. -/
theorem planeModel_energy_above_order {K L : ℕ} (hKL : K ≤ L)
    (n : ℕ) (ϖ r : ℝ) (y : Vec 2) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ y r L U = weightedFactorialNormSq n ϖ y r K U := by
  classical
  unfold weightedFactorialNormSq
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hKL))
  intro j _ hj
  have h : ¬ j ≤ K := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  simp only [planeJetOrder, dite_eq_right h, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero, ENNReal.ofReal_zero, lintegral_zero]

/-- Positive factorial coefficients and the spatial weight dominate the Hilbert norm. -/
theorem planeModel_norm_sq_le_energy {K L : ℕ} (hKL : K ≤ L)
    (n : ℕ) (ϖ r : ℝ) (y : Vec 2) (U : PlaneHk Set.univ K E) :
    ENNReal.ofReal (factorialWeightMin r K * ‖U‖ ^ 2) ≤
      weightedFactorialNormSq n ϖ y r L U := by
  rw [planeModel_energy_above_order hKL]
  exact (ENNReal.ofReal_le_ofReal (factorialNormSq_lower r U.val)).trans
    (factorialNormSq_le_weightedFactorialNormSq n ϖ y r U)

/-- The same finite energy supplies fourth radial moments for every stored jet. -/
theorem planeModel_radial_moments {K L : ℕ} (hKL : K ≤ L)
    (n : ℕ) (hn : 4 ≤ n) (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (y : Vec 2) (U : PlaneHk Set.univ K E)
    (he : weightedFactorialNormSq n ϖ y r L U ≠ ⊤) : HasRadialPlaneMoments U y := by
  rw [planeModel_energy_above_order hKL] at he
  exact hasRadialPlaneMoments_of_finite_polynomial U ϖ hϖ y r hr
    (ne_top_of_le_ne_top he (CycleWords.weightedFactorialNormSq_moment_mono hn ϖ y r K U))

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A finite mass-weighted energy estimate implies a uniform Hilbert operator bound.
The input map can be a product truncation or the identity. -/
theorem planeModel_exists_norm_bound {X : Type*}
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (M : ι → ℕ) (Mb n : ℕ)
    (hM : ∀ i, M i ≤ Mb) (ϖ r C : ℝ) (hr : 0 < r) (y : Vec 2)
    (ℓ : ∀ i, TorusHk 0 (h i) →L[ℝ] PlaneHk Set.univ 0 (h i))
    (g : X → ∀ i, TorusHk 0 (h i)) (F : X → ∀ i, PlaneHk Set.univ (M i) (h i))
    (hF : ∀ x, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (F x i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖ℓ i (g x i)‖ ^ 2)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖F x‖ ≤ A * ‖g x‖ := by
  classical
  let L : ℝ := ∑ i, (π i)⁻¹ * ‖ℓ i‖ ^ 2
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (hπ i).le) (sq_nonneg _))
  let a := fun i => (π i)⁻¹ * factorialWeightMin r (M i)
  have ha (i : ι) : 0 < a i := mul_pos (inv_pos.mpr (hπ i)) (factorialWeightMin_pos r hr)
  let d := fun i => C ^ 2 * L / a i
  have hd (i : ι) : 0 ≤ d i := div_nonneg (mul_nonneg (sq_nonneg _) hL) (ha i).le
  let A := 1 + ∑ i, Real.sqrt (d i)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, fun x => (pi_norm_le_iff_of_nonneg (mul_nonneg hA (norm_nonneg _))).mpr ?_⟩
  intro i
  have hs : ∑ j, (π j)⁻¹ * ‖ℓ j (g x j)‖ ^ 2 ≤ L * ‖g x‖ ^ 2 := by
    dsimp only [L]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hh := (ℓ j).le_opNorm (g x j)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (g x) j) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh' 2)
      (inv_nonneg.mpr (hπ j).le)).trans_eq (by ring)
  have he : ENNReal.ofReal (a i * ‖F x i‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * L * ‖g x‖ ^ 2) := by
    calc
      _ = ENNReal.ofReal ((π i)⁻¹) *
          ENNReal.ofReal (factorialWeightMin r (M i) * ‖F x i‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hπ i).le)]
        congr 1
        dsimp only [a]
        ring
      _ ≤ ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (F x i) :=
        mul_le_mul' le_rfl (planeModel_norm_sq_le_energy (hM i) n ϖ r y (F x i))
      _ ≤ ∑ j, ENNReal.ofReal ((π j)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (F x j) :=
        Finset.single_le_sum (f := fun j => ENNReal.ofReal ((π j)⁻¹) *
          weightedFactorialNormSq n ϖ y r Mb (F x j)) (fun _ _ => bot_le) (Finset.mem_univ i)
      _ ≤ _ := (hF x).trans (ENNReal.ofReal_le_ofReal (by
        exact (mul_le_mul_of_nonneg_left hs (sq_nonneg C)).trans_eq (mul_assoc _ _ _).symm))
  have he' : a i * ‖F x i‖ ^ 2 ≤ C ^ 2 * L * ‖g x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have hsq : ‖F x i‖ ^ 2 ≤ d i * ‖g x‖ ^ 2 := by
    dsimp only [d]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (ha i)).mpr
    simpa only [mul_comm (a i)] using he'
  have hi : ‖F x i‖ ≤ Real.sqrt (d i) * ‖g x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (hd i)] using hsq
  apply hi.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (d j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (by norm_num))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal Topology
namespace AVRegularity.CycleJointProofs.Assembly

/-! Weighted plane energy sublevels are closed, by continuous bounded clips. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
/-- A bounded positive scalar energy is a continuous quadratic form on plane L². -/
theorem planeModel_bounded_energy_continuous (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) (B : ℝ) (hb : ∀ x, q x ≤ B) :
    Continuous (chartScalarEnergy (E := E) q) := by
  let T := planeScalarMultiplier (E := E) (fun x => Real.sqrt (q x)) hq.sqrt
    (Real.sqrt_nonneg B) (fun x => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hb x))
  have he (U : Lp E 2 (volume : Measure (Vec 2))) :
      chartScalarEnergy q U = ENNReal.ofReal (‖T U‖ ^ 2) := by
    convert chartScalarEnergy_eq_weighted_representative_norm (fun x => Real.sqrt (q x))
      U (T U) (planeScalarMultiplier_ae _ _ _ _ U) using 1
    congr 1
    funext x
    exact (Real.sq_sqrt (hq0 x)).symm
  rw [show chartScalarEnergy (E := E) q = (fun U => ENNReal.ofReal (‖T U‖ ^ 2)) from funext he]
  exact ENNReal.continuous_ofReal.comp (T.continuous.norm.pow 2)

/-- Positive continuous weights have continuous bounded rational clips. -/
theorem planeModel_clip_continuous (q : Vec 2 → ℝ) (hq : Continuous q)
    (hqpos : ∀ x, 0 < q x) (b : ℕ) :
    Continuous (fun x => clipWeight ((b : ℝ) + 1) (q x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_clipWeight (by positivity) (hqpos x)).continuousAt.comp hq.continuousAt

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A finite weighted energy budget with continuous right side is a closed property. -/
theorem planeModel_energy_property_closed {X : Type*} [TopologicalSpace X]
    (π : ι → ℝ) (M : ι → ℕ) (Mb n : ℕ) (hM : ∀ i, M i ≤ Mb)
    (ϖ r : ℝ) (y : Vec 2)
    (F : X → ∀ i, PlaneHk Set.univ (M i) (h i)) (hF : Continuous F)
    (R : X → ℝ) (hR : Continuous R) :
    IsClosed {g | ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ y r Mb (F g i) ≤ ENNReal.ofReal (R g)} := by
  classical
  let q := planeMomentPolynomial n ϖ y
  have hq : Continuous q := by unfold q planeMomentPolynomial; fun_prop
  have hp (x : Vec 2) : 0 < q x := by unfold q planeMomentPolynomial; positivity
  let qB := fun b : ℕ => fun x => clipWeight ((b : ℝ) + 1) (q x)
  have hc (b : ℕ) : Continuous (qB b) := planeModel_clip_continuous q hq hp b
  let B := fun b : ℕ => fun g : X => ∑ i, ENNReal.ofReal ((π i)⁻¹) *
    storedChartFactorialEnergy r (qB b) (F g i)
  have hBc (b : ℕ) : Continuous (B b) := by
    apply continuous_finsetSum
    intro i _
    apply (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    apply continuous_finsetSum
    intro a _
    apply (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    exact (planeModel_bounded_energy_continuous (E := h i) (qB b) (hc b)
      (fun x => (clipWeight_pos (by positivity) (hp x)).le) ((b : ℝ) + 1)
      (fun x => clipWeight_le_bound (by positivity) (hp x))).comp
        ((planeJetReadoutOperator (M i) a).continuous.comp ((continuous_apply i).comp hF))
  have ht (g : X) : Tendsto (fun b => B b g) atTop
      (𝓝 (∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ y r Mb (F g i))) := by
    simp_rw [planeModel_energy_above_order (hM _), weightedFactorialNormSq_stored_readout]
    apply tendsto_finsetSum
    intro i _
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_finsetSum
    intro a _
    exact ENNReal.Tendsto.const_mul
      (chartScalarEnergy_clipping_tendsto q hp (fun b => (hc b).measurable)
        (planeJetReadoutOperator (M i) a (F g i))) (Or.inr ENNReal.ofReal_ne_top)
  have he : {g | ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ y r Mb (F g i) ≤ ENNReal.ofReal (R g)} =
      ⋂ b : ℕ, {g | B b g ≤ ENNReal.ofReal (R g)} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hg b
      apply le_trans _ hg
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul' le_rfl
      rw [planeModel_energy_above_order (hM i), weightedFactorialNormSq_stored_readout]
      exact storedChartFactorialEnergy_mono r (qB b) q
        (fun x => clipWeight_le_value (by positivity) (hp x)) (F g i)
    · intro hg
      exact le_of_tendsto (ht g) (Eventually.of_forall hg)
  rw [he]
  exact isClosed_iInter (fun b => isClosed_le (hBc b) (ENNReal.continuous_ofReal.comp hR))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVenhance.Infra.Flow
namespace AVRegularity.CycleJointProofs.Assembly

/-! The centre counting argument consumes a gradient bound only on its stated time window. -/

/-- Forward Grönwall with a spatial bound restricted to the traversed time interval. -/
theorem flow_window_forward (b : ℝ → Vec 2 → Vec 2)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (L s t : ℝ) (hst : s ≤ t)
    (hL : ∀ u ∈ Set.Icc s t, ∀ x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    (x y : Vec 2) :
    ‖X t x s - X t y s‖ ≤ Real.exp (L * (t - s)) * ‖x - y‖ := by
  let f := fun u => X u x s - X u y s
  let f' := fun u => b u (X u x s) - b u (X u y s)
  have hd (u : ℝ) : HasDerivAt f (f' u) u := (hX.2 x s u).sub (hX.2 y s u)
  have hc : ContinuousOn f (Set.Icc s t) := HasDerivAt.continuousOn (fun u _ => hd u)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le (K := L) (ε := 0) hc
    (fun u _ => (hd u).hasDerivWithinAt)
    (show ‖f s‖ ≤ ‖x - y‖ by simp only [f, hX.1]; exact le_rfl)
    (fun u hu => by simpa only [f, f', add_zero] using hL u ⟨hu.1, hu.2.le⟩ (X u x s) (X u y s))
    t ⟨hst, le_rfl⟩
  simpa only [f, gronwallBound_ε0, mul_comm] using hh

/-- Backward Grönwall needs the same window, by reversing time. -/
theorem flow_window_backward (b : ℝ → Vec 2 → Vec 2)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (L s t : ℝ) (hst : s ≤ t)
    (hL : ∀ u ∈ Set.Icc s t, ∀ x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖)
    (x y : Vec 2) :
    ‖X s x t - X s y t‖ ≤ Real.exp (L * (t - s)) * ‖x - y‖ := by
  let br := fun u z => -b (-u) z
  let xr := fun u z v => X (-u) z (-v)
  have hr : IsFlow br xr := by
    refine ⟨fun z v => hX.1 z (-v), ?_⟩
    intro z v u
    have hd : HasDerivAt (fun r => X r z (-v))
        (b (0 - u) (X (0 - u) z (-v))) (0 - u) := by
      simpa only [zero_sub] using hX.2 z (-v) (-u)
    simpa only [br, xr, zero_sub] using hd.comp_const_sub 0 u
  have hh := flow_window_forward br hr L (-t) (-s) (by linarith)
    (fun u hu x y => by
      have hut : -u ∈ Set.Icc s t := by constructor <;> linarith [hu.1, hu.2]
      simpa only [br, neg_sub_neg, norm_neg, norm_sub_rev] using hL (-u) hut x y) x y
  have ht : (-s) - (-t) = t - s := by ring
  simpa only [xr, neg_neg, ht] using hh

/-- The inverse centre flow has a uniform Lipschitz constant on the window. -/
theorem centre_inverse_flow_bound (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (s t T g : ℝ) (hst : s ≤ t) (hdt : t - s ≤ 2 * T) (hT : 0 < T)
    (_hg : 0 ≤ g) (hg1 : g ≤ 1 / 8)
    (hgrad : ∀ u ∈ Set.Icc s t, ∀ y : Vec 2, T * ‖fderiv ℝ (streamVel φ u) y‖ ≤ g)
    (x y : Vec 2) :
    ‖streamFlow φ hφ s x t - streamFlow φ hφ s y t‖ ≤ Real.exp (1 / 4) * ‖x - y‖ := by
  have hsmooth := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hL : ∀ u ∈ Set.Icc s t, ∀ a c,
      ‖streamVel φ u a - streamVel φ u c‖ ≤ (g / T) * ‖a - c‖ := by
    intro u hu a c
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ((hsmooth.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by simp) z))
      (fun z _ => (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hgrad u hu z))
      convex_univ (Set.mem_univ c) (Set.mem_univ a)
  have hh := flow_window_backward (streamVel φ)
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz) (g / T) s t hst hL x y
  have he : (g / T) * (t - s) ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hg1 (sub_nonneg.mpr hst)
    have hmul2 := mul_le_mul_of_nonneg_left hdt (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hT).mpr
    linarith only [hmul, hmul2]
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg _))

end AVRegularity.CycleJointProofs.Assembly
end
end
