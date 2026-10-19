-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.ApproxIdentity
public import AVRegularity.CycleComparison.Reconstruction.TorusSlices
import AVRegularity.CycleComparison.Reconstruction.FiniteRankIdentity
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of the glued lift of a Galerkin approximant**.
See `ApproxIdentity` for the residual presentation `(approxFlux, approxForce)`. The finite-rank identity of the glued lift
(`glued_finiteRank_identity_closed`) of the approximant `a_n = coarseTraj n W`, with its coarse
defect field split by `coarse_defect_split`, the lifted divergence of the flux approximant in
cleanup form (`glued_liftFlux`) and one periodic integration by parts (`cell_ibp_div`), is the
weak identity of the coupled system with edge flux `edgeFluxOf` (`approx_weak_identity`). The
continuity of the pieces on the cell (used only for the integrability of the tested pieces) is
assumed. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The weak identity of the glued lift of a Galerkin approximant with its residual
presentation.** -/
theorem approx_weak_identity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseqΦ : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m) (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) {ρ E : ℝ}
    (hρ : 0 < ρ) {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*} (F : ChartedFamily ι h D Pc Ctx)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (htorus : IsTorusCompatible F actual E) (T : F.Atlas) {tA tZ : ℝ} (htAZ : tA ≤ tZ)
    (hTcons : T.IsConsecutiveClosed (Icc tA tZ))
    (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Icc tA tZ))
    (hTq : T.IsQuiet ν (ocEpsilon q Λ m) E)
    (hTact : ∀ p q' (hpq : T.adjacent p q'),
      ((F.piece p).output ∩ (F.piece q').output ∩ Icc tA tZ).Nonempty →
        T.sameCtx p q' hpq (actual p) (actual q'))
    (pp : ℤ → Pc)
    (hpp : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
      (∀ t, ⇑((F.piece (pp k)).material t) = ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q
        Λ m k) t) ∧
      ocPulseWindow α q Λ m k ∩ Icc tA tZ ⊆ (F.piece (pp k)).output)
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ)) {Cpart : ℝ}
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Icc tA tZ))
    {π : ι → ℝ} {e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : ℤ → Fin 2}
    {V : ℤ → ℝ → ℝ → ℝ} {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) π
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2)
        e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ (par k) (V k) H N K₀ k₀ L qs qf CG Cw Cj edgeM Θ)
    (hDsZ : D ≤ max (k₀ + 1) (L + 2)) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (hseq : ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k)
        (actual (pp k)))) (K₀ + D + 2) (max (k₀ + 1) (L + 2))
        (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2) N H (Cc k))
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K₀ + D + 2) (hZ : sZc ≤ max (k₀ + 1) (L + 2))
    -- the coarse family
    {Bc : ℝ} {Dl kc Nf r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 Dl, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 Dl), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f0 : ∀ v, TorusHk Nf (h v)}
    {W : ∀ v, ℝ → TorusHk (kc + 1 + Dl) (h v)}
    {Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v))}
    (hcd : IsCoarseDefect tA tZ Bc (streamVel (Φ (m - 1))) Dl H kc Nf AD CE Jm f0 W Fc)
    (aRep : ℝ → Vec 2 → ∀ i, h i)
    (hrep : ∀ s ∈ Icc tA tZ, ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hDl : 2 ≤ Dl) (hDr : Dl ≤ r₀) (hrK : r₀ ≤ kc + 1 + Dl)
    (hmean : ∀ r ∈ Finset.range (H + 1), IsMeanPresentation (Icc tA tZ) Dl r AD CE Jm
      (gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
        (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ
          (ρ / E) k (F.fiber (pp k) (actual (pp k)))) Cc
        (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))))
    (hAD : ∀ s ∈ Icc tA tZ, ∀ d, ContDiff ℝ 1 (AD d s))
    (hADp : ∀ s ∈ Icc tA tZ, ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ s ∈ Icc tA tZ, ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hCEp : ∀ s ∈ Icc tA tZ, ∀ r ∈ Finset.Icc 1 H, ∀ v u d,
      AVenhance.IsZ2Periodic (CE r v u d s))
    (hbc : ∀ s, Continuous (streamVel (Φ (m - 1)) s))
    (hbp : ∀ s, AVenhance.IsZ2Periodic (streamVel (Φ (m - 1)) s))
    (hbm : ∀ s, Continuous (streamVel (Φ m) s))
    -- the approximant and its cleanup chains
    (n : ℕ) (Vc : ℤ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H →
      ∀ τ ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXc sZc Acl
        (tailScalarField (fun _ => 0) N D (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W)
          (coarseMode n) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (ocEll q Λ m ν ^ 2) ρ) τ)
        (tailFluxField (fun n' => tailFluxCoefficient (par k) (pulseLiftData α q Λ m ζ (Φ (m - 1))
          hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) (Cc k) N hh n') N D
          (ocDStar q Λ m ν B / ρ) (chartField (coarseCoeff n W) (coarseMode n)
            (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocEll q Λ m ν ^ 2) ρ)
                τ)
        (fun j => Vc k hh j τ))
    (sXl sZl : ℕ) (hXl : 1 ≤ sXl) (hZl : 1 ≤ sZl)
    (Vn : ℤ → ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hVn : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ∀ hh, hh ≤ H → ∀ n', n' < N →
      ∀ τ ∈ Icc (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tA / ocEll q Λ m ν ^ 2)
        (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tZ / ocEll q Λ m ν ^ 2),
      IsCleanupChain sXl sZl Acl
        (liftApply (n' + 1) (Cc k hh (n' + 1)) (fun s X => fluxApproxDiv n Fc (ocEll q Λ m ν ^ 2 *
            s)
          (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) (ocEll q Λ m ν ^ 2 * s)
            (ρ • X))) τ)
        (fun _ _ _ => 0) (fun j => Vn k hh n' j τ))
    -- the continuity of the pieces on the cell
    (hUc : ∀ s ∈ Icc tA tZ, ∀ v, ContDiff ℝ 1 (fun y =>
      obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (coarseTraj n W) s y v))
    (hEc : ∀ s ∈ Icc tA tZ, ∀ v, Continuous (fun x => edgeFluxOf K
      (edgeCoefficient F ν (ocEpsilon q Λ m) E actual K) s
      (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (coarseTraj n W) s) v x))
    (hTFc : ∀ s ∈ Icc tA tZ, ∀ v (a₀ : Fin 2), Continuous (fun x =>
      gluedTailFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x a₀ v))
    (hTfc : ∀ s ∈ Icc tA tZ, ∀ v, Continuous (fun x =>
      gluedTailForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x v))
    (hLFc : ∀ s ∈ Icc tA tZ, ∀ v (a₀ : Fin 2), Continuous (fun x =>
      gluedLiftFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x a₀ v))
    (hLfc : ∀ s ∈ Icc tA tZ, ∀ v, Continuous (fun x =>
      gluedLiftForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
        (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x v))
    (hEN : ∀ s ∈ Icc tA tZ, ContDiff ℝ (N : ℕ∞)
      (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep s))
    (hENc : ∀ s ∈ Icc tA tZ, ∀ v, Continuous (fun x =>
      obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep) s x v))
    (hGc : ∀ s ∈ Icc tA tZ, ∀ v, Continuous (fun x =>
      obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (fluxApproxDiv n Fc) s x v))
    (hPc : ∀ s ∈ Icc tA tZ, ∀ v, ∀ k ∈ ocObsPulses α q Λ m tA tZ,
      deriv (F.weight (pp k)) s ≠ 0 → Continuous (fun x =>
      pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
        (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x
        v)) :
    ∀ t ∈ Icc tA tZ, ∀ v, ∀ φ : Vec 2 → h v, ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict unitCube) ν tA t (streamVel (Φ m))
        (fun x => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
          (coarseTraj n W) t x v)
        (fun x => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
          (coarseTraj n W) tA x v)
        φ (fun k x => fderiv ℝ φ x (basisVec k))
        (fun s k x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ
          (fun k => F.weight (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k))
        (fun s x => edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) E actual K) s
          (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
            (coarseTraj n W) s) v x)
        (approxFlux α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) H N Acl Vc Vn
          n Fc v)
        (approxForce α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) H N Acl Cc Vc
          Vn n (streamVel (Φ (m - 1))) Dl AD CE Jm W aRep v) := by
  intro t ht v φ hφ hφp
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc0 : 0 < ocEll q Λ m ν ^ 2 := by positivity
  have hprim := glued_finiteRank_identity_closed hseqΦ hm hΛ hζ hφs hν hB hρ F actual K hdesc
    htorus T htAZ hTcons hTcov hTq hTact pp hpp hppinj hpart hquiet P hDsZ Cc hseq sXc sZc Acl
    hAcl hXc hZc hX hZ (coarseCoeff n W)
    (coarseCoeffDot n Bc (streamVel (Φ (m - 1))) Dl H AD CE Jm W Fc) (coarseMode n)
    (coarseMode_contDiff n) (coarseMode_periodic n) tA tZ le_rfl le_rfl
    (coarseCoeff_prim hcd htAZ n) Vc hV v φ hφ1 hφp
  -- continuity facts
  have hφc : Continuous φ := hφ1.continuous
  have hdφc : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ φ x (basisVec k)) := fun k =>
    cell_continuous_partial hφ1 k
  have hint : ∀ {f g : Vec 2 → h v}, Continuous f → Continuous g →
      Integrable (fun x => inner ℝ (f x) (g x)) (volume.restrict unitCube) := fun hf hg =>
    cell_integrable_inner_continuous hf hg
  have hsumint : ∀ {f : Fin 2 → Vec 2 → h v}, (∀ k, Continuous (f k)) →
      Integrable (fun x => ∑ k : Fin 2, inner ℝ (f k x) (fderiv ℝ φ x (basisVec k)))
        (volume.restrict unitCube) := fun hf =>
    integrable_finsetSum _ fun k _ => hint (hf k) (hdφc k)
  -- the approximant field
  have hUv : ∀ s, (fun x' => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s •
      obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H (coarseCoeff n W) (coarseMode n) k s x' v) =
      fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (coarseTraj n W) s y v := fun s => by
    funext y
    simp only [obsGlued, gluedLift, Finset.sum_apply, Pi.smul_apply]
    rfl
  -- the tested pieces at one time
  have hcont : ∀ f : Vec 2 → ℝ, Continuous f → Integrable f (volume.restrict unitCube) :=
    fun f hf => AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable f hf
  have iB : ∀ s ∈ Icc tA tZ, Integrable (fun x => ∑ k : Fin 2, streamVel (Φ m) s x k *
      inner ℝ (fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight
          (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k)) (φ x))
      (volume.restrict unitCube) := fun s hs =>
    hcont _ (continuous_finsetSum _ fun k _ => ((continuous_apply k).comp (hbm s)).mul
      ((cell_continuous_partial (hUc s hs v) k).inner hφc))
  have iD : ∀ s ∈ Icc tA tZ, Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight
          (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k))
        (fderiv ℝ φ x (basisVec k))) (volume.restrict unitCube) := fun s hs =>
    hsumint fun k => cell_continuous_partial (hUc s hs v) k
  have iE : ∀ s ∈ Icc tA tZ, Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) E actual K) s
        (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc (coarseTraj
            n W) s) v x k) (fderiv ℝ φ x (basisVec k))) (volume.restrict unitCube) := fun s hs =>
    hsumint fun k => (PiLp.continuous_apply 2 _ k).comp (hEc s hs v)
  have iF1 : ∀ s ∈ Icc tA tZ, Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (gluedTailFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x k v)
        (fderiv ℝ φ x (basisVec k))) (volume.restrict unitCube) := fun s hs =>
    hsumint fun k => hTFc s hs v k
  have iF2 : ∀ s, Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (fluxApprox n (fun v => Fc v s) x k v) (fderiv ℝ φ x (basisVec k))) (volume.restrict
          unitCube) :=
    fun s => hsumint fun k => (fluxApprox_component_contDiff n (fun v => Fc v s) k v).continuous
  have iF3 : ∀ s ∈ Icc tA tZ, Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (gluedLiftFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x k v)
        (fderiv ℝ φ x (basisVec k))) (volume.restrict unitCube) := fun s hs =>
    hsumint fun k => hLFc s hs v k
  have ig1 : ∀ s ∈ Icc tA tZ, Integrable (fun x => inner ℝ
      (gluedTailForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k => ocChartInv α
          q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x v) (φ x))
            (volume.restrict unitCube) :=
    fun s hs => hint (hTfc s hs v) hφc
  have ig2 : ∀ s ∈ Icc tA tZ, Integrable (fun x => inner ℝ
      (gluedLiftForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k => ocChartInv α
          q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x v) (φ x))
            (volume.restrict unitCube) :=
    fun s hs => hint (hLfc s hs v) hφc
  have ig3 : ∀ s ∈ Icc tA tZ, Integrable (fun x => inner ℝ
      (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
          (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep) s x v) (φ x))
      (volume.restrict unitCube) := fun s hs => hint (hENc s hs v) hφc
  have hP4c : ∀ s ∈ Icc tA tZ, Continuous (fun x => (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv
      (F.weight (pp k)) s •
      pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
        (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x)
        v) := fun s hs => by
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine continuous_finsetSum _ fun k hk => ?_
    by_cases hd : deriv (F.weight (pp k)) s = 0
    · simp only [hd, zero_smul]
      exact continuous_const
    · exact (hPc s hs v k hk hd).const_smul _
  have ig4 : ∀ s ∈ Icc tA tZ, Integrable (fun x => inner ℝ
      ((∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (F.weight (pp k)) s •
        pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s
          x) v) (φ x)) (volume.restrict unitCube) := fun s hs => hint (hP4c s hs) hφc
  refine coupledWeakIdentity_of_isPrimOn (μ := volume.restrict unitCube) (streamVel (Φ m))
    (fun s x => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
      (coarseTraj n W) s x v) φ (fun k x => fderiv ℝ φ x (basisVec k))
    (fun s k x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ
      (fun k => F.weight (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k))
    (fun s x => edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) E actual K) s
      (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
        (coarseTraj n W) s) v x)
    (approxFlux α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) H N Acl Vc Vn
      n Fc v)
    (approxForce α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) H N Acl Cc Vc
      Vn n (streamVel (Φ (m - 1))) Dl AD CE Jm W aRep v) _ hprim ?_ ?_ ?_ t ht
  · intro s hs
    have hsI : s ∈ Icc tA tZ := Ioc_subset_Icc_self hs
    -- the defect field of the approximant at the time `s`
    have hsplit : (fun x' => (∑ j, coarseCoeffDot n Bc (streamVel (Φ (m - 1))) Dl H AD CE Jm W
          Fc j s • coarseMode n j x' + ∑ j, coarseCoeff n W j s •
            fderiv ℝ (coarseMode n j) x' (streamVel (Φ (m - 1)) s x')) +
          ∑ r ∈ Finset.range (H + 1), gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp
              k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m
              ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) Cc (fun k =>
              ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α
              q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x') =
        fun x' => defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep s x' +
          fluxApproxDiv n Fc s x' :=
      funext fun x' => coarse_defect_split (M := fun r => gluedMean (ocObsPulses α q Λ m tA tZ) (fun
          k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (fun k =>
          pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k))))
          Cc (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))) hmean hsI hDl hDr hrK
        (hrep s hsI) (hAD s hsI) (hADp s hsI) (hCE s hsI) (hCEp s hsI) (hbc s) (hbp s) n x'
    have hχs : ∀ k ∈ ocObsPulses α q Λ m tA tZ, ContDiff ℝ (⊤ : ℕ∞)
        (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) := fun k _ =>
      (Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m k)).comp
        (contDiff_const.prodMk contDiff_id)
    have hGpt : ∀ x, gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν
        ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k => ocChart α q Λ m (Φ (m -
        1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs
        (ocPulseChartIndex α q Λ m k)) (fun t' x' => (∑ j, coarseCoeffDot n Bc
          (streamVel (Φ (m - 1))) Dl H AD CE Jm W Fc j t' • coarseMode n j x' +
          ∑ j, coarseCoeff n W j t' • fderiv ℝ (coarseMode n j) x'
            (streamVel (Φ (m - 1)) t' x')) +
          ∑ r ∈ Finset.range (H + 1), gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp
              k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m
              ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) Cc (fun k =>
              ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α
              q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑ j', coarseCoeff
              n W j' t'' • coarseMode n j' x'') t' x') s x v =
        obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
            (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep) s x v +
          gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ
              (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k => ocChart α q Λ m (Φ (m - 1))
              hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφs
              (ocPulseChartIndex α q Λ m k)) (fluxApproxDiv n Fc) s x v := by
      intro x
      rw [gluedLift_congr_time _ _ hc0.ne' _ _ _ _ _ _ _ _
        (b := fun t' x' => defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep t' x' +
          fluxApproxDiv n Fc t' x') hsplit x,
        gluedLift_add_input _ _ hc0.ne' _ _ _ _ _ _ _ _ hχs _ _ (hEN s hsI)
          ((fluxApproxDiv_contDiff n Fc s).of_le (by exact_mod_cast le_top)) x]
      rfl
    -- the lifted divergence of the flux approximant in cleanup form
    have hLF := glued_liftFlux hΛ hφs hν hρ (fun k => F.fiber (pp k) (actual (pp k)))
      (fun k => F.weight (pp k)) hpart P (K₀ + D + 2) (max (k₀ + 1) (L + 2)) Cc hseq sXl sZl Acl
      hAcl hXl hZl (fluxApproxDiv n Fc)
      (fun k _ => pulse_edge_slow_invariant α q Λ m ζ hφs ν B hρ.ne' k htorus (pp k)) Vn hVn hsI
      (fluxApproxDiv_contDiff n Fc s).continuous (fluxApproxDiv_periodic n Fc s) v φ hφ1 hφp
    -- one periodic integration by parts
    have hIBP := cell_ibp_div (F := fun x k => fluxApprox n (fun v => Fc v s) x k v)
      (fun k => (fluxApprox_component_contDiff n (fun v => Fc v s) k v).of_le
        (by exact_mod_cast le_top))
      (fun k => fluxApprox_component_periodic n (fun v => Fc v s) k v) hφ1 hφp
    have hG : (∫ x in unitCube, inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k => F.weight
        (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc (fun k =>
        ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α q Λ m
        (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t' x' => (∑ j, coarseCoeffDot n Bc
          (streamVel (Φ (m - 1))) Dl H AD CE Jm W Fc j t' • coarseMode n j x' +
          ∑ j, coarseCoeff n W j t' • fderiv ℝ (coarseMode n j) x'
            (streamVel (Φ (m - 1)) t' x')) +
          ∑ r ∈ Finset.range (H + 1), gluedMean (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp
              k)) (ocEll q Λ m ν ^ 2) ρ (ocDStar q Λ m ν B / ρ) N r (fun k => pulseLiftData α q Λ m
              ζ (Φ (m - 1)) hφs ν B ρ (ρ / E) k (F.fiber (pp k) (actual (pp k)))) Cc (fun k =>
              ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k => ocChartInv α
              q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun t'' x'' => ∑ j', coarseCoeff
              n W j' t'' • coarseMode n j' x'') t' x') s x v) (φ x)) =
        (∫ x in unitCube, inner ℝ (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight
            (pp k)) N H Cc (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE
          Jm W aRep) s x v) (φ x))
        - (∫ x in unitCube, ∑ k : Fin 2, inner ℝ (fluxApprox n (fun v => Fc v s) x k v)
          (fderiv ℝ φ x (basisVec k)))
        - (∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ ((∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k)
            s •
          liftFluxPhys (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N
            Acl (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) s x a₀) v)
          (fderiv ℝ φ x (basisVec a₀)))
        + ∫ x in unitCube, inner ℝ ((∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s •
          liftForcePhys (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N
            Acl (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) s x) v)
          (φ x) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [hGpt x, inner_add_left])]
      have igd : Integrable (fun x => inner ℝ (gluedLift (ocObsPulses α q Λ m tA tZ) (fun k =>
          F.weight (pp k)) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (fluxApproxDiv n Fc) s x
          v)
          (φ x)) (volume.restrict unitCube) := hint (hGc s hsI v) hφc
      rw [integral_add (ig3 s hsI) igd]
      rw [hLF]
      have hIBP' : (∫ x in unitCube, inner ℝ (fluxApproxDiv n Fc s x v) (φ x)) =
          -∫ x in unitCube, ∑ k : Fin 2, inner ℝ (fluxApprox n (fun v => Fc v s) x k v)
            (fderiv ℝ φ x (basisVec k)) := hIBP
      rw [hIBP']
      ring
    -- the partition terms
    have hP : (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (fun s => F.weight (pp k) s) s *
        ∫ x in unitCube, inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H (coarseCoeff n W)
            (coarseMode n) k s x v) (φ x)) =
        ∫ x in unitCube, inner ℝ ((∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (F.weight (pp k)) s •
          pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H (Cc
              k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocChartInv α q Λ m
              (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x) v) (φ x) := by
      have hpt : ∀ x, inner ℝ ((∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (F.weight (pp k)) s •
          pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H (Cc
              k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocChartInv α q Λ m
              (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x) v) (φ x) =
          ∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (fun s => F.weight (pp k) s) s * inner ℝ (obsLift α
              q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H (coarseCoeff n W) (coarseMode n) k s x v) (φ x) :=
        fun x => by
          simp only [Finset.sum_apply, Pi.smul_apply, sum_inner, real_inner_smul_left]
          rfl
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_finsetSum (f := fun k x => deriv (fun s => F.weight (pp k) s) s *
          inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H (coarseCoeff n W) (coarseMode n) k s
              x v) (φ x)) _
          fun k hk => by
            by_cases hd : deriv (F.weight (pp k)) s = 0
            · have hz : (fun x => deriv (fun s => F.weight (pp k) s) s *
                  inner ℝ (obsLift α q Λ m (Φ (m - 1)) hφs ν B ρ Cc N H (coarseCoeff n W)
                    (coarseMode n) k s x v) (φ x)) = fun _ => 0 := by
                funext x
                simp only [show deriv (fun s => F.weight (pp k) s) s = 0 from hd, zero_mul]
              rw [hz]
              exact integrable_zero _ _ _
            · exact (hint (hPc s hsI v k hk hd) hφc).const_mul _]
      exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    -- the drift term
    have hT1 : (∫ x in unitCube, inner ℝ (∑ j : Fin 2, streamVel (Φ m) s x j •
        fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N
            H Cc (coarseTraj n W) s y v) x (basisVec j)) (φ x)) =
        ∫ x in unitCube, ∑ k : Fin 2, streamVel (Φ m) s x k *
          inner ℝ (fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k =>
              F.weight (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k)) (φ x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [sum_inner, real_inner_smul_left])
    refine Eq.trans ?_ (integral_weakRhs_split (μ := volume.restrict unitCube) ν (streamVel (Φ m))
      (fun s k x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k =>
          F.weight (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k))
      (fun s x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K s
        (fun y => ∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s • obsLift α q Λ m (Φ (m - 1))
            hφs ν B ρ Cc N H (coarseCoeff n W) (coarseMode n) k s y) v x)
      (fun x a₀ => (∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s • tailFluxPhys (ocChartInv α
          q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N Acl (ocDStar q Λ m ν B / ρ)
          (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) s x
        a₀) v)
      (fun x a₀ => fluxApprox n (fun v => Fc v s) x a₀ v)
      (fun x a₀ => (∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s • liftFluxPhys (ocChartInv α
          q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N Acl (ocDStar q Λ m ν B / ρ)
          (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) s x
        a₀) v)
      (fun x => (∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s • tailForcePhys (ocChartInv α q
          Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N Acl (ocDStar q Λ m ν B / ρ)
          (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vc k) s x) v)
      (fun x => (∑ k ∈ ocObsPulses α q Λ m tA tZ, F.weight (pp k) s • liftForcePhys (ocChartInv α q
          Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k) s) H N Acl (ocDStar q Λ m ν B / ρ)
          (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (Vn k) s x) v)
      (fun x => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
          (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep) s x v)
      (fun x => (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (F.weight (pp k)) s • pulsePhysicalLift
          (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H (Cc k) (ocChart α q Λ
          m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (ocChartInv α q Λ m (Φ (m - 1)) hφs
          (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s x) v)
      φ (fun k x => fderiv ℝ φ x (basisVec k)) s (iB s hsI) (iD s hsI) (iE s hsI) (iF1 s hsI)
      (iF2 s) (iF3 s hsI) (ig1 s hsI) (ig2 s hsI) (ig3 s hsI) (ig4 s hsI)).symm
    beta_reduce
    rw [hUv s, hT1, hG, hP]
    ring
  · intro t' ht'
    exact hint (hUc t' ht' v).continuous hφc
  · intro s hs
    have hsI : s ∈ Icc tA tZ := Ioc_subset_Icc_self hs
    exact integrable_weakRhs_split ν (streamVel (Φ m))
      (fun s k x => fderiv ℝ (fun y => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k =>
          F.weight (pp k)) N H Cc (coarseTraj n W) s y v) x (basisVec k))
      (fun s x => edgeFluxOf K (edgeCoefficient F ν (ocEpsilon q Λ m) E actual K) s
        (obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc (coarseTraj
            n W) s) v x)
      (fun x a₀ => gluedTailFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x a₀ v)
      (fun x a₀ => fluxApprox n (fun v => Fc v s) x a₀ v)
      (fun x a₀ => gluedLiftFlux (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x a₀ v)
      (fun x => gluedTailForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vc s x v)
      (fun x => gluedLiftForce (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k)) (fun k =>
          ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) H N Acl
        (ocDStar q Λ m ν B / ρ) (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) Vn s x v)
      (fun x => obsGlued α q Λ m (Φ (m - 1)) hφs ν B ρ tA tZ (fun k => F.weight (pp k)) N H Cc
          (defectRemainder n (streamVel (Φ (m - 1))) Dl H AD CE Jm W aRep) s x v)
      (fun x => (∑ k ∈ ocObsPulses α q Λ m tA tZ, deriv (F.weight (pp k)) s •
        pulsePhysicalLift (ocEll q Λ m ν ^ 2) ρ (ocEpsilon q Λ m) (ocDStar q Λ m ν B / ρ) N H
          (Cc k) (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k))
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m k)) (coarseTraj n W) s
          x) v)
      φ (fun k x => fderiv ℝ φ x (basisVec k)) s (iB s hsI) (iD s hsI) (iE s hsI) (iF1 s hsI)
      (iF2 s) (iF3 s hsI) (ig1 s hsI) (ig2 s hsI) (ig3 s hsI) (ig4 s hsI)

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The data of a reconstruction window**. The hypotheses of the physical
reconstruction (`cycle_comparison_physical_lift`) that the reconstruction of the glued lift uses,
bundled for the window `[t_p, t_p + T_obs]`: the scales and the OC stream, the charted family with
its atlas and the observed pulses with their partition, the lift settings and lift sequences of the
observed pulses (at the orders `(K_lift, L_lift)`), the coarse setting, the coarse defect equation
with its classical representative and the mean presentations (`ReconWindow`). -/

/-- **The data of a reconstruction window, at a lift length `ρ`, a radius `ρc` of the coarse
setting and a constant flux matrix `Jm`**. `E = ε_{m-1}` and the cell
time is `c = ℓ²`. The lift length `ρ` enters the lift data, the lift settings and sequences, the
glued means and, downstream, the glued lifts and the energies; `ρc` enters the coarse setting
only; `Jm` is the constant matrix of the coarse defect equation.
- Cascade (`ReconWindow`): `ρ = ρc = √(Bτ_m'')`, `Jm = ocRefFlux`.
- Weak passage: `ρ = ε_{m-1}` (the slow length of the weak lifts), `ρc = c ε_{m-1}` with
  the plan's radius `c` (the drift conditions of `IsCoarseSetting` fail at `ε_{m-1}`), `Jm = κ_M I`
  (the degree-two eddy term is the letter `𝔇_2`, in `AD`). -/
structure ReconWindowAt {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
    (α s q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B tp Tobs ρs ρ ρc : ℝ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {D : ℕ}
    (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ) (T : F.Atlas)
    (pp : ℤ → P') (π : ι → ℝ) (Cpart : ℝ) (H Nc Klift Llift qs qf : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (CGl Cw : ℕ → ℝ) (Ca : ℝ) (bM : ι → ι → ℝ) (Sb : ℝ)
    (aC B₀C lamC : ℝ) (pc Jc kc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Aedge : Matrix ι ι ℝ) (Cstar Θc : ℝ) (f0 : ∀ v, TorusHk
      (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v))
    (W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v))
    (Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v)))
    (aRep : ℝ → Vec 2 → ∀ i, h i) (r₀ : ℕ) : Prop where
  -- the exponents and the construction
  hα₀ : 0 < α
  hα₁ : α < 1 / 3
  hs₀ : 0 < s
  hs₁ : s < (1 - α) / 2
  hq : IsAdmissibleQ α s q
  hζ : IsFastProfile ζ
  hΛ : 128 ≤ Λ
  hΦ : IsOCStreamSeq α q Λ ζ Φ
  hm : 2 ≤ m
  -- the scales of the window
  hν : 0 < ν
  hB : 0 < B
  hTobs : 0 < Tobs
  hρs : 0 < ρs
  hρs_e : ρs ≤ ocEpsilon q Λ m
  hρs_R : ρs ≤ ρ
  hRE : ρ ≤ ocEpsilon q Λ (m - 1)
  -- the charted family, its atlas and the observed pulses
  hdesc : F.IsDescending K
  htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1))
  hTcons : T.IsConsecutiveClosed (Set.Icc tp (tp + Tobs))
  hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs))
  hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
  hTact : ∀ p q' (hpq : T.adjacent p q'),
    ((F.piece p).output ∩ (F.piece q').output ∩ Set.Icc tp (tp + Tobs)).Nonempty →
      T.sameCtx p q' hpq (actual p) (actual q')
  hpp : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
    (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
    (∀ t, ⇑((F.piece (pp k)).material t) =
      ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) ∧
    ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output
  hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tp (tp + Tobs))
  hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
    (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs))
    (ocTau α q Λ m) Cpart
  hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs))
  -- the lift settings and the lift sequences of the observed pulses
  hsetting : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
    IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
        ρ
        (ρ / ocEpsilon q Λ (m - 1)) k
        (F.fiber (pp k) (actual (pp k)))) π
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m) ν B ρ (ocEpsilon q Λ (m - 1))
      (ocEll q Λ m ν) (ocDStar q Λ m ν B)
      (ocDStar q Λ m ν B / ρ)
      (ρ / ocEpsilon q Λ (m - 1))
      (par k) (V k) H Nc Klift Llift Llift qs qf CGl Cw (fun _ _ => Ca) bM Sb
  hseq : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
    IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
        ρ
        (ρ / ocEpsilon q Λ (m - 1)) k
        (F.fiber (pp k) (actual (pp k))))
      (Klift + D + 2) (max (Llift + 1) (Llift + 2))
      (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
      (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) Nc H (Cc k)
  -- the coarse setting, the coarse defect equation and its classical representative
  hcs : IsCoarseSetting tp (tp + Tobs) ρc B aC B₀C lamC
    (streamVel (Φ (m - 1))) (Nc + D) H pc Jc kc ((Nc + D) + 8 * pc + 4)
    (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) Jm AD CE π Aedge
    Cstar Θc
  hcd : IsCoarseDefect tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H kc
    (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE Jm f0 W Fc
  hrep : ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
    IsClassicalRep (W v t) (fun x => aRep t x v) r₀
  hr₀ : r₀ ≤ kc + 1 + (Nc + D)
  hDr : Nc + D ≤ r₀
  hmean : ∀ r ∈ Finset.range (H + 1), IsMeanPresentation (Set.Icc tp (tp + Tobs)) (Nc + D) r
    AD CE Jm
    (gluedMean (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
      (ocEll q Λ m ν ^ 2) ρ
      (ocDStar q Λ m ν B / ρ) Nc r
      (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
        ρ
        (ρ / ocEpsilon q Λ (m - 1)) k
        (F.fiber (pp k) (actual (pp k)))) Cc
      (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
      (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)))


/-- **The data of a reconstruction window** of the cascade: `ReconWindowAt` at the lift length and
coarse radius `ρ = ρc = √(Bτ_m'')` and at the reference flux `Jm = ocRefFlux`. An abbreviation, so
that every field and every theorem on `ReconWindow` keeps its type. -/
abbrev ReconWindow {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {P' : Type*} {Ctx : P' → Type*}
    (α s q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B tp Tobs ρs : ℝ) {D : ℕ}
    (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p) (K : ι → ℕ) (T : F.Atlas)
    (pp : ℤ → P') (π : ι → ℝ) (Cpart : ℝ) (H Nc Klift Llift qs qf : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (CGl Cw : ℕ → ℝ) (Ca : ℝ) (bM : ι → ι → ℝ) (Sb : ℝ)
    (aC B₀C lamC : ℝ) (pc Jc kc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Aedge : Matrix ι ι ℝ) (Cstar Θc : ℝ) (f0 : ∀ v, TorusHk
      (kc + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) (h v))
    (W : ∀ v, ℝ → TorusHk (kc + 1 + (Nc + D)) (h v))
    (Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v)))
    (aRep : ℝ → Vec 2 → ∀ i, h i) (r₀ : ℕ) : Prop :=
  ReconWindowAt α s q Λ ζ Φ m hφ ν B tp Tobs ρs (Real.sqrt (B * ocTauPP α q Λ m))
    (Real.sqrt (B * ocTauPP α q Λ m)) (ocRefFlux α q Λ ζ m ν) F actual K T pp π Cpart H Nc Klift
    Llift qs qf Cc par V CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep r₀

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleComparison.Lift
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Coarse.JointOps
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Joint measurability of the building blocks of the residual of an approximant**.
The residual pieces of `approxFlux` and `approxForce` are sampled at the physical time `t` and the position `x`; their joint measurability in `(t, x)` follows from:

* the samples of a chain or of a lift action that is jointly measurable in clamped cell time and
  `(X, z)` (`measurable_tailFluxPhys_joint`, `measurable_tailForcePhys_joint`,
  `measurable_liftFluxPhys_joint`, `measurable_liftForcePhys_joint`,
  `measurable_pulseLift_clamped`), the inverse charts entering through their Jacobians
  (`continuous_chartInvJacobian_joint`);
* the clamping is invisible where the partition weight of the pulse does not vanish
  (`tailFluxPhys_clamp_eq`, …, `pulsePhysicalLift_eq_sum`, `measurable_weight_smul_of_ne`);
* the coarse fields on the window `[tA, tZ]` (`JointlyMeas`): the approximant
  (`jointlyMeas_coarseTraj`), the flux approximant and its divergence
  (`jointlyMeas_fluxApprox`, `jointlyMeas_fluxApproxDiv`), and the commutator remainder
  (`jointlyMeas_defectRemainder`) from the joint measurability of the classical representative,
  the drift and the coefficients (`jointlyMeas_classicalDefectField`, with jointly measurable
  `C^r` families `JMF` and their ordered derivatives `jmf_orderedDerivative`);
* the chart-frame field of a jointly measurable coarse field is measurable in clamped cell time
  (`chartFrame_clamped_measurable`). -/

/-! ### Gluing and charts -/

/-- A weighted family is measurable when it agrees with a measurable family wherever the weight
does not vanish. -/
theorem measurable_weight_smul_of_ne {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {w : S → ℝ} (hw : Measurable w)
    {F G : S → E} (hG : Measurable G) (hFG : ∀ p, w p ≠ 0 → F p = G p) :
    Measurable fun p => w p • F p := by
  have e : (fun p => w p • F p) = fun p => w p • G p := by
    funext p
    by_cases h0 : w p = 0
    · rw [h0, zero_smul, zero_smul]
    · rw [hFG p h0]
  rw [e]
  exact hw.fun_smul hG

/-- The entries of the inverse Jacobian of a jointly smooth family of charts with jointly smooth
inverses are jointly continuous. -/
theorem continuous_chartInvJacobian_joint {χ ψ : ℝ → Vec 2 → Vec 2}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => χ p.1 p.2)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => ψ p.1 p.2)
    (hψχ : ∀ t y, ψ t (χ t y) = y) (hχψ : ∀ t x, χ t (ψ t x) = x) (a₀ i₀ : Fin 2) :
    Continuous fun p : ℝ × Vec 2 => chartInvJacobian (ψ p.1) p.2 a₀ i₀ := by
  have hχt : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (χ t) := fun t =>
    hχ.comp (contDiff_const.prodMk contDiff_id)
  have hψt : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (ψ t) := fun t =>
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun p : ℝ × Vec 2 => chartInvJacobian (ψ p.1) p.2 a₀ i₀) =
      fun p => fderiv ℝ (χ p.1) (ψ p.1 p.2) (basisVec i₀) a₀ := by
    funext p
    rw [chartInvJacobian_eq_of_inverse ((hχt p.1).differentiable (by simp))
      ((hψt p.1).differentiable (by simp)) (hψχ p.1) (hχψ p.1) p.2]
    rfl
  rw [he]
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry fun (p : ℝ × Vec 2) (y : Vec 2) => χ p.1 y) :=
    hχ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hF : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => fderiv ℝ (χ p.1) (ψ p.1 p.2) :=
    hf.fderiv hψ (by simp)
  exact (continuous_apply a₀).comp (hF.continuous.clm_apply continuous_const)

/-- The physical tail flux only sees the chains at the cell time: clamping the chains to a
window containing the cell time does not change it. -/
theorem tailFluxPhys_clamp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ) {a b : ℝ} (hab : a ≤ b)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b)
    (x : Vec 2) (a₀ : Fin 2) :
    tailFluxPhys ψ H N Acl ε c ρs es (fun hh j τ => Vc hh j (Set.projIcc a b hab τ)) t x a₀ =
      tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ := by
  have e : (Set.projIcc a b hab (c⁻¹ * t) : ℝ) = c⁻¹ * t := projIcc_val_of_mem hab ht
  simp only [tailFluxPhys, tailFluxLabel, cleanupFlux, diagSample, e]

/-- The physical tail force only sees the chains at the cell time. -/
theorem tailForcePhys_clamp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ) {a b : ℝ} (hab : a ≤ b)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b)
    (x : Vec 2) :
    tailForcePhys ψ H N Acl ε c ρs es (fun hh j τ => Vc hh j (Set.projIcc a b hab τ)) t x =
      tailForcePhys ψ H N Acl ε c ρs es Vc t x := by
  have e : (Set.projIcc a b hab (c⁻¹ * t) : ℝ) = c⁻¹ * t := projIcc_val_of_mem hab ht
  simp only [tailForcePhys, cleanupRemainder, diagSample, e]

/-- The physical lifted coarse flux only sees the chains at the cell time. -/
theorem liftFluxPhys_clamp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ) {a b : ℝ} (hab : a ≤ b)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b)
    (x : Vec 2) (a₀ : Fin 2) :
    liftFluxPhys ψ H N Acl ε c ρs es (fun hh n j τ => Vn hh n j (Set.projIcc a b hab τ)) t x
        a₀ = liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ := by
  have e : (Set.projIcc a b hab (c⁻¹ * t) : ℝ) = c⁻¹ * t := projIcc_val_of_mem hab ht
  simp only [liftFluxPhys, tailFluxPhys, tailFluxLabel, cleanupFlux, diagSample, e]

/-- The physical lifted coarse force only sees the chains at the cell time. -/
theorem liftForcePhys_clamp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ) {a b : ℝ} (hab : a ≤ b)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b)
    (x : Vec 2) :
    liftForcePhys ψ H N Acl ε c ρs es (fun hh n j τ => Vn hh n j (Set.projIcc a b hab τ)) t x =
      liftForcePhys ψ H N Acl ε c ρs es Vn t x := by
  have e : (Set.projIcc a b hab (c⁻¹ * t) : ℝ) = c⁻¹ * t := projIcc_val_of_mem hab ht
  simp only [liftForcePhys, tailForcePhys, cleanupRemainder, diagSample, e]

/-! ### Joint measurability of the sampled pieces -/

/-- **The physical tail flux of jointly measurable chains is jointly measurable** in the
physical time and the position. -/
theorem measurable_tailFluxPhys_joint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {θ : ℝ × Vec 2 → ℝ} (hθ : Measurable θ)
    {Ψ : ℝ → Vec 2 → Vec 2} (hΨ : Measurable fun p : ℝ × Vec 2 => Ψ p.1 p.2)
    (hK : ∀ a₀ i₀ : Fin 2, Measurable fun p : ℝ × Vec 2 => chartInvJacobian (Ψ p.1) p.2 a₀ i₀)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hV : ∀ hh, hh ≤ H → ∀ j, j < Acl →
      Measurable fun q : ℝ × Vec 2 × Vec 2 => Vc hh j q.1 q.2.1 q.2.2)
    (a₀ : Fin 2) :
    Measurable fun p : ℝ × Vec 2 => tailFluxPhys (Ψ (θ p)) H N Acl ε c ρs es Vc (θ p) p.2 a₀ := by
  have hθx : Measurable fun p : ℝ × Vec 2 => (θ p, p.2) := hθ.prodMk measurable_snd
  have hy : Measurable fun p : ℝ × Vec 2 => Ψ (θ p) p.2 := hΨ.comp hθx
  have hq : Measurable fun p : ℝ × Vec 2 =>
      (c⁻¹ * θ p, ρs⁻¹ • Ψ (θ p) p.2, es⁻¹ • Ψ (θ p) p.2) :=
    (hθ.const_mul c⁻¹).prodMk (((continuous_const_smul ρs⁻¹).measurable.comp hy).prodMk
      ((continuous_const_smul es⁻¹).measurable.comp hy))
  have hj : ∀ hh ∈ Finset.range (H + 1), ∀ i₀ : Fin 2, Measurable fun p : ℝ × Vec 2 =>
      ∑ j ∈ Finset.range Acl, (es / ρs) ^ j •
        Vc hh j (c⁻¹ * θ p) (ρs⁻¹ • Ψ (θ p) p.2) (es⁻¹ • Ψ (θ p) p.2) i₀ := fun hh hhm i₀ =>
    Finset.measurable_sum _ fun j hj => ((measurable_pi_apply i₀).comp
      ((hV hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) j
        (Finset.mem_range.1 hj)).comp hq)).fun_const_smul ((es / ρs) ^ j)
  have hl : ∀ i₀ : Fin 2, Measurable fun p : ℝ × Vec 2 =>
      ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) • (es • ∑ j ∈ Finset.range Acl,
        (es / ρs) ^ j • Vc hh j (c⁻¹ * θ p) (ρs⁻¹ • Ψ (θ p) p.2) (es⁻¹ • Ψ (θ p) p.2) i₀) :=
    fun i₀ => Finset.measurable_sum _ fun hh hhm =>
      (((hj hh hhm i₀).fun_const_smul es).fun_const_smul (ε ^ (N + 1))).fun_const_smul c⁻¹
  have hK' : ∀ i₀ : Fin 2, Measurable fun p : ℝ × Vec 2 =>
      chartInvJacobian (Ψ (θ p)) p.2 a₀ i₀ := fun i₀ => by
    have h1 := (hK a₀ i₀).comp hθx
    simp only [Function.comp_def] at h1
    exact h1
  show Measurable fun p : ℝ × Vec 2 => ∑ i₀ : Fin 2, chartInvJacobian (Ψ (θ p)) p.2 a₀ i₀ •
    tailFluxLabel H N Acl ε c ρs es Vc (θ p) (Ψ (θ p) p.2) i₀
  exact Finset.measurable_sum _ fun i₀ _ => (hK' i₀).fun_smul (hl i₀)

/-- **The physical tail force of jointly measurable last sources is jointly measurable.** -/
theorem measurable_tailForcePhys_joint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {θ : ℝ × Vec 2 → ℝ} (hθ : Measurable θ)
    {Ψ : ℝ → Vec 2 → Vec 2} (hΨ : Measurable fun p : ℝ × Vec 2 => Ψ p.1 p.2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hS : ∀ hh, hh ≤ H → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      cleanupSource (fun j => Vc hh j q.1) Acl q.2.1 q.2.2) :
    Measurable fun p : ℝ × Vec 2 => tailForcePhys (Ψ (θ p)) H N Acl ε c ρs es Vc (θ p) p.2 := by
  have hy : Measurable fun p : ℝ × Vec 2 => Ψ (θ p) p.2 := hΨ.comp (hθ.prodMk measurable_snd)
  have hq : Measurable fun p : ℝ × Vec 2 =>
      (c⁻¹ * θ p, ρs⁻¹ • Ψ (θ p) p.2, es⁻¹ • Ψ (θ p) p.2) :=
    (hθ.const_mul c⁻¹).prodMk (((continuous_const_smul ρs⁻¹).measurable.comp hy).prodMk
      ((continuous_const_smul es⁻¹).measurable.comp hy))
  have hs : ∀ hh ∈ Finset.range (H + 1), Measurable fun p : ℝ × Vec 2 =>
      cleanupSource (fun j => Vc hh j (c⁻¹ * θ p)) Acl (ρs⁻¹ • Ψ (θ p) p.2)
        (es⁻¹ • Ψ (θ p) p.2) := fun hh hhm => by
    have h1 := (hS hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))).comp hq
    simp only [Function.comp_def] at h1
    exact h1
  show Measurable fun p : ℝ × Vec 2 => ∑ hh ∈ Finset.range (H + 1), c⁻¹ • ε ^ (N + 1) •
    cleanupRemainder c⁻¹ ρs es Acl (Vc hh) (θ p) (Ψ (θ p) p.2)
  exact Finset.measurable_sum _ fun hh hhm =>
    (((hs hh hhm).fun_const_smul ((es / ρs) ^ Acl)).fun_const_smul (ε ^ (N + 1))).fun_const_smul
      c⁻¹

/-- **The physical lifted coarse flux of jointly measurable chains is jointly measurable.** -/
theorem measurable_liftFluxPhys_joint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {θ : ℝ × Vec 2 → ℝ} (hθ : Measurable θ)
    {Ψ : ℝ → Vec 2 → Vec 2} (hΨ : Measurable fun p : ℝ × Vec 2 => Ψ p.1 p.2)
    (hK : ∀ a₀ i₀ : Fin 2, Measurable fun p : ℝ × Vec 2 => chartInvJacobian (Ψ p.1) p.2 a₀ i₀)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hV : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ j, j < Acl →
      Measurable fun q : ℝ × Vec 2 × Vec 2 => Vn hh n j q.1 q.2.1 q.2.2)
    (a₀ : Fin 2) :
    Measurable fun p : ℝ × Vec 2 => liftFluxPhys (Ψ (θ p)) H N Acl ε c ρs es Vn (θ p) p.2 a₀ := by
  show Measurable fun p : ℝ × Vec 2 => ∑ n ∈ Finset.range N,
    c • tailFluxPhys (Ψ (θ p)) H n Acl ε c ρs es (fun hh => Vn hh n) (θ p) p.2 a₀
  exact Finset.measurable_sum _ fun n hn => (measurable_tailFluxPhys_joint hθ hΨ hK H n Acl ε c
    ρs es (fun hh => Vn hh n) (fun hh hhh j hj => hV hh hhh n (Finset.mem_range.1 hn) j hj)
    a₀).fun_const_smul c

/-- **The physical lifted coarse force of jointly measurable last sources is jointly
measurable.** -/
theorem measurable_liftForcePhys_joint {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {θ : ℝ × Vec 2 → ℝ} (hθ : Measurable θ)
    {Ψ : ℝ → Vec 2 → Vec 2} (hΨ : Measurable fun p : ℝ × Vec 2 => Ψ p.1 p.2)
    (H N Acl : ℕ) (ε c ρs es : ℝ) (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hS : ∀ hh, hh ≤ H → ∀ n, n < N → Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      cleanupSource (fun j => Vn hh n j q.1) Acl q.2.1 q.2.2) :
    Measurable fun p : ℝ × Vec 2 => liftForcePhys (Ψ (θ p)) H N Acl ε c ρs es Vn (θ p) p.2 := by
  show Measurable fun p : ℝ × Vec 2 => ∑ n ∈ Finset.range N,
    c • tailForcePhys (Ψ (θ p)) H n Acl ε c ρs es (fun hh => Vn hh n) (θ p) p.2
  exact Finset.measurable_sum _ fun n hn => (measurable_tailForcePhys_joint hθ hΨ H n Acl ε c ρs
    es (fun hh => Vn hh n) (fun hh hhh => hS hh hhh n (Finset.mem_range.1 hn))).fun_const_smul c

/-- The physical lift of a pulse as a double sum of lift actions read at the label. -/
theorem pulsePhysicalLift_eq_sum {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t x =
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), εc ^ n •
        liftApply n (Cc hh n) (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) (c⁻¹ * t)
          (ρ⁻¹ • label t x) (e⁻¹ • label t x) := by
  simp only [pulsePhysicalLift, diagSample]

/-- **The physical lift of a pulse with clamped cell time is jointly measurable** when its lift
actions are jointly measurable in clamped cell time and `(X, z)`. -/
theorem measurable_pulseLift_clamped {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    {a b : ℝ} (hab : a ≤ b) {θ : ℝ × Vec 2 → ℝ} (hθ : Measurable θ) {Ψ : ℝ → Vec 2 → Vec 2}
    (hΨ : Measurable fun p : ℝ × Vec 2 => Ψ p.1 p.2) (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (A : ℝ → Vec 2 → ∀ i, h i)
    (hL : ∀ hh, hh ≤ H → ∀ n, n ≤ N → ∀ v, Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      liftApply n (Cc hh n) A (Set.projIcc a b hab q.1) q.2.1 q.2.2 v) :
    Measurable fun p : ℝ × Vec 2 => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
      εc ^ n • liftApply n (Cc hh n) A (Set.projIcc a b hab (c⁻¹ * θ p))
        (ρ⁻¹ • Ψ (θ p) p.2) (e⁻¹ • Ψ (θ p) p.2) := by
  have hy : Measurable fun p : ℝ × Vec 2 => Ψ (θ p) p.2 := hΨ.comp (hθ.prodMk measurable_snd)
  have hq : Measurable fun p : ℝ × Vec 2 =>
      (c⁻¹ * θ p, ρ⁻¹ • Ψ (θ p) p.2, e⁻¹ • Ψ (θ p) p.2) :=
    (hθ.const_mul c⁻¹).prodMk (((continuous_const_smul ρ⁻¹).measurable.comp hy).prodMk
      ((continuous_const_smul e⁻¹).measurable.comp hy))
  refine Finset.measurable_sum _ fun hh hhm => Finset.measurable_sum _ fun n hn => ?_
  have hL' : Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      liftApply n (Cc hh n) A (Set.projIcc a b hab q.1) q.2.1 q.2.2 :=
    Measurable.of_eval fun v => hL hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) v
  have h1 := hL'.comp hq
  simp only [Function.comp_def] at h1
  exact h1.fun_const_smul (εc ^ n)

/-! ### Coarse fields on the window -/

/-- A jointly measurable field on the window, read at the clamped time. -/
theorem jointlyMeas_comp_projIcc {F : Type*} [MeasurableSpace F] {tA tZ : ℝ} (htAZ : tA ≤ tZ)
    {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas tA tZ Ψ) :
    Measurable fun p : ℝ × Vec 2 => Ψ (Set.projIcc tA tZ htAZ p.1) p.2 :=
  Measurable.comp hΨ (((continuous_projIcc (h := htAZ)).measurable.comp measurable_fst).prodMk
    measurable_snd)

/-- **The chart-frame field of a jointly measurable coarse field is measurable in clamped cell
time.** -/
theorem chartFrame_clamped_measurable {F : Type*} [MeasurableSpace F] {tA tZ a b c ρ : ℝ}
    (hab : a ≤ b) (hwin : ∀ τ ∈ Set.Icc a b, c * τ ∈ Set.Icc tA tZ) {f : ℝ → Vec 2 → F}
    (hf : JointlyMeas tA tZ f) {χ : ℝ → Vec 2 → Vec 2}
    (hχ : Continuous fun p : ℝ × Vec 2 => χ p.1 p.2) (X : Vec 2) :
    Measurable fun τ =>
      f (c * Set.projIcc a b hab τ) (χ (c * Set.projIcc a b hab τ) (ρ • X)) := by
  have hθc : Continuous fun τ => c * (Set.projIcc a b hab τ : ℝ) :=
    continuous_const.mul (continuous_subtype_val.comp (continuous_projIcc (h := hab)))
  have hθ : Continuous fun τ => (⟨c * (Set.projIcc a b hab τ : ℝ),
      hwin _ (Set.projIcc a b hab τ).2⟩ : Set.Icc tA tZ) := hθc.subtype_mk _
  have hy : Continuous fun τ => χ (c * Set.projIcc a b hab τ) (ρ • X) :=
    hχ.comp (hθc.prodMk continuous_const)
  exact Measurable.comp hf (hθ.measurable.prodMk hy.measurable)

section Coarse

/-- **The approximant is jointly measurable on the window** when its coefficients are
measurable in time. -/
theorem jointlyMeas_coarseTraj {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (hcm : ∀ r : CoupledFourierModeIndex (h := h) n,
      Measurable fun s : Set.Icc tA tZ => coarseCoeff n W r s) :
    JointlyMeas tA tZ (coarseTraj n W) := by
  show Measurable fun q : Set.Icc tA tZ × Vec 2 =>
    ∑ r : CoupledFourierModeIndex (h := h) n, coarseCoeff n W r q.1 • coarseMode n r q.2
  exact Finset.measurable_sum _ fun r _ => ((hcm r).comp measurable_fst).fun_smul
    ((coarseMode_contDiff n r).continuous.measurable.comp measurable_snd)

/-- **The flux approximant is jointly measurable on the window** when its coefficients are
measurable in time. -/
theorem jointlyMeas_fluxApprox {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} (n : ℕ) {kc : ℕ}
    (Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v)))
    (hFm : ∀ r : CoupledFourierModeIndex (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n,
      Measurable fun s : Set.Icc tA tZ => coarseModeCoeff n (fun v => Fc v s) r)
    (j : Fin 2) (v : ι) :
    JointlyMeas tA tZ fun s x => fluxApprox n (fun v => Fc v s) x j v := by
  set L : (∀ i, PiLp 2 (fun _ : Fin 2 => h i)) →L[ℝ] h v :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h v) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => PiLp 2 (fun _ : Fin 2 => h i)) v)
    with hL
  have e : (fun q : Set.Icc tA tZ × Vec 2 => fluxApprox n (fun v => Fc v q.1) q.2 j v) =
      fun q => ∑ r : CoupledFourierModeIndex (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n,
        coarseModeCoeff n (fun v => Fc v q.1) r • L (coarseMode n r q.2) := by
    funext q
    show L (∑ r : CoupledFourierModeIndex (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n,
        coarseModeCoeff n (fun v => Fc v q.1) r • coarseMode n r q.2) = _
    simp only [map_sum, map_smul]
  show Measurable fun q : Set.Icc tA tZ × Vec 2 => fluxApprox n (fun v => Fc v q.1) q.2 j v
  rw [e]
  exact Finset.measurable_sum _ fun r _ => ((hFm r).comp measurable_fst).fun_smul
    ((L.continuous.comp (coarseMode_contDiff n r).continuous).measurable.comp measurable_snd)

/-- **The divergence of the flux approximant is jointly measurable on the window.** -/
theorem jointlyMeas_fluxApproxDiv {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} (n : ℕ) {kc : ℕ}
    (Fc : ∀ v, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => h v)))
    (hFm : ∀ r : CoupledFourierModeIndex (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n,
      Measurable fun s : Set.Icc tA tZ => coarseModeCoeff n (fun v => Fc v s) r) :
    JointlyMeas tA tZ (fluxApproxDiv n Fc) := by
  have hc : ∀ (v : ι) (j : Fin 2),
      JMF tA tZ (0 + 1) fun s y => fluxApprox n (fun v => Fc v s) y j v := fun v j =>
    ⟨jointlyMeas_fluxApprox n Fc hFm j v, fun s _ =>
      (fluxApprox_component_contDiff n (fun v => Fc v s) j v).of_le
        (order_natCast_le_top _)⟩
  show Measurable fun q : Set.Icc tA tZ × Vec 2 => fun v =>
    ∑ j : Fin 2, fderiv ℝ (fun y => fluxApprox n (fun v => Fc v q.1) y j v) q.2 (basisVec j)
  exact Measurable.of_eval fun v => (JMF.sum _ fun j _ => (hc v j).dbasis j).1

end Coarse

/-! ### Jointly measurable `C^r` families: ordered derivatives -/

section Words

variable {tA tZ : ℝ}

/-- Derivatives along a list of directions, innermost first, of a jointly measurable `C^r`
family. -/
theorem jmf_foldl_word {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (l : List (Fin 2)) :
    ∀ (r : ℕ) (Φ : ℝ → Vec 2 → F), JMF tA tZ (r + l.length) Φ →
      JMF tA tZ r fun s => l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) (Φ s) := by
  induction l with
  | nil => intro r Φ h; simpa using h
  | cons i l ih =>
    intro r Φ h
    have h1 : JMF tA tZ (r + l.length) fun s x => fderiv ℝ (Φ s) x (basisVec i) :=
      JMF.dbasis (h.mono (by simp only [List.length_cons]; omega)) i
    exact ih r _ h1

/-- **Ordered derivatives of a jointly measurable `C^{r+m}` family** form a jointly measurable
`C^r` family. -/
theorem jmf_orderedDerivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {r m : ℕ}
    {Φ : ℝ → Vec 2 → F} (α : DerivativeWord2 m) (hΦ : JMF tA tZ (r + m) Φ) :
    JMF tA tZ r fun s => orderedDerivative α (Φ s) :=
  jmf_foldl_word (List.ofFn α) r Φ (by simpa using hΦ)

/-- The Euclidean vector of a finite family of jointly measurable `C^r` families. -/
theorem jmf_toLp_pi {κ : Type*} [Fintype κ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {r : ℕ} {Φ : κ → ℝ → Vec 2 → E}
    (hΦ : ∀ i, JMF tA tZ r (Φ i)) :
    JMF tA tZ r fun s x => WithLp.toLp 2 (fun i => Φ i s x) :=
  ⟨(WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i => (hΦ i).1),
    fun s hs => (contDiff_piLp 2).2 fun i => (hΦ i).2 s hs⟩

end Words

/-! ### The commutator remainder -/

section Defect

/-- **The classical defect field of a jointly measurable `C^{D_l}` field is jointly measurable**
when the drift, the matrix `𝖩` and the coefficients `A_d`, `C^{[r]}` are, and the coefficients are
`C¹` in space on the window. -/
theorem jointlyMeas_classicalDefectField {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} {b : ℝ → Vec 2 → Vec 2} {Dl H : ℕ}
    {AD : ∀ d : Finset.Icc 2 Dl, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 Dl), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hDl : 2 ≤ Dl)
    (hbm : Measurable fun q : Set.Icc tA tZ × Vec 2 => b q.1 q.2)
    (hbc : ∀ s, Continuous (b s)) (hJm : ∀ i j, Measurable fun t => Jm t i j)
    (hADm : ∀ d, Measurable fun q : Set.Icc tA tZ × Vec 2 => AD d q.1 q.2)
    (hAD : ∀ s ∈ Set.Icc tA tZ, ∀ d, ContDiff ℝ 1 (AD d s))
    (hCEm : ∀ r ∈ Finset.Icc 1 H, ∀ v u d,
      Measurable fun q : Set.Icc tA tZ × Vec 2 => CE r v u d q.1 q.2)
    (hCE : ∀ s ∈ Set.Icc tA tZ, ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (a : ℝ → Vec 2 → ∀ i, h i) (ha : ∀ v, JMF tA tZ Dl fun s x => a s x v) (v : ι) :
    JointlyMeas tA tZ fun s x => classicalDefectField b Dl H AD CE Jm a s v x := by
  have hgrade : ∀ r ∈ Finset.range (H + 1), ∀ j : Fin 2,
      JMF tA tZ 1 fun s x => classicalGradeFlux Dl r AD CE Jm a v s x j := by
    intro r hr j
    by_cases hr0 : r = 0
    · simp only [classicalGradeFlux, ite_eq_left hr0]
      refine JMF.add (JMF.sum _ fun l _ => ?_) (JMF.sum _ fun d _ => JMF.sum _ fun α _ => ?_)
      · exact JMF.smul_time (c := fun s => Jm s j l) ((hJm j l).comp measurable_subtype_coe)
          (JMF.dbasis ((ha v).mono (by omega)) l)
      · have hdD : (d : ℕ) ≤ Dl := (Finset.mem_Icc.1 d.2).2
        have hAD1 : JMF tA tZ 1 (AD d) :=
          ⟨hADm d, fun s hs => by exact_mod_cast hAD s hs d⟩
        exact JMF.smul_coeff (JMF.proj (JMF.clm_apply hAD1 (JMF.const _)) j)
          (jmf_orderedDerivative α ((ha v).mono (by omega)))
    · have hrI : r ∈ Finset.Icc 1 H := Finset.mem_Icc.2
        ⟨Nat.one_le_iff_ne_zero.2 hr0, Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)⟩
      simp only [classicalGradeFlux, ite_eq_right hr0]
      refine JMF.sum _ fun u _ => JMF.sum _ fun d _ => ?_
      have hdD : (d : ℕ) ≤ Dl := (Finset.mem_Icc.1 d.2).2
      have hCE1 : JMF tA tZ 1 (CE r v u d) :=
        ⟨hCEm r hrI v u d, fun s hs => by exact_mod_cast hCE s hs r hrI v u d⟩
      exact JMF.proj (JMF.clm_apply hCE1
        (jmf_toLp_pi fun α => jmf_orderedDerivative α ((ha u).mono (by omega)))) j
  have hflux : ∀ j : Fin 2, JMF tA tZ 1 fun s x => classicalTotalFlux Dl H AD CE Jm a s v x j :=
    fun j => by
      show JMF tA tZ 1 fun s x =>
        ∑ r ∈ Finset.range (H + 1), classicalGradeFlux Dl r AD CE Jm a v s x j
      exact JMF.sum _ fun r hr => hgrade r hr j
  have hdiv : JMF tA tZ 0 fun s x => ∑ j : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux Dl H AD CE Jm a s v y j) x (basisVec j) :=
    JMF.sum _ fun j _ => JMF.dbasis (hflux j) j
  have hb : ∀ j : Fin 2, JMF tA tZ 0 fun s x => b s x j := fun j =>
    ⟨(measurable_pi_apply j).comp hbm, fun s _ => by
      exact_mod_cast (contDiff_zero.2 ((continuous_apply j).comp (hbc s)) :
        ContDiff ℝ 0 fun x => b s x j)⟩
  have hdrift : JMF tA tZ 0 fun s x => ∑ j : Fin 2,
      b s x j • fderiv ℝ (fun y => a s y v) x (basisVec j) :=
    JMF.sum _ fun j _ => JMF.smul_coeff (hb j) (JMF.dbasis ((ha v).mono (by omega)) j)
  exact (hdrift.neg.add hdiv).1

/-- **The Galerkin projection of a jointly measurable family of fields is jointly measurable.** -/
theorem jointlyMeas_coarseProjField {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} (n : ℕ) (g : ℝ → ∀ v, Vec 2 → h v)
    (hg : ∀ v, JointlyMeas tA tZ fun s x => g s v x) :
    JointlyMeas tA tZ fun s x => coarseProjField n (g s) x := by
  have hc : ∀ r : CoupledFourierModeIndex (h := h) n, Measurable fun s : Set.Icc tA tZ =>
      ∫ y in AVenhance.unitCube, inner ℝ (g s r.1 y) (coupledModeJet n r r.1 0 Fin.elim0 y) := by
    intro r
    have hcont : Continuous fun y => coupledModeJet n r r.1 0 Fin.elim0 y :=
      (continuous_apply r.1).comp (coarseMode_contDiff n r).continuous
    have hj : Measurable fun q : Set.Icc tA tZ × Vec 2 =>
        inner ℝ (g q.1 r.1 q.2) (coupledModeJet n r r.1 0 Fin.elim0 q.2) :=
      Measurable.inner (hg r.1) (hcont.measurable.comp measurable_snd)
    exact (hj.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict AVenhance.unitCube)).measurable
  show Measurable fun q : Set.Icc tA tZ × Vec 2 => ∑ r : CoupledFourierModeIndex (h := h) n,
    (∫ y in AVenhance.unitCube, inner ℝ (g q.1 r.1 y) (coupledModeJet n r r.1 0 Fin.elim0 y)) •
      coarseMode n r q.2
  exact Finset.measurable_sum _ fun r _ => ((hc r).comp measurable_fst).fun_smul
    ((coarseMode_contDiff n r).continuous.measurable.comp measurable_snd)

/-- **The commutator remainder of a Galerkin approximant is jointly measurable on the window**
when the classical representative, the drift, the matrix `𝖩` and the coefficients are, and the
Galerkin coefficients are measurable in time. -/
theorem jointlyMeas_defectRemainder {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {tA tZ : ℝ} (n : ℕ) {b : ℝ → Vec 2 → Vec 2} {Dl H : ℕ}
    {AD : ∀ d : Finset.Icc 2 Dl, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 Dl), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) {r₀ : ℕ} (hDl : 2 ≤ Dl) (hDr : Dl ≤ r₀)
    (hbm : Measurable fun q : Set.Icc tA tZ × Vec 2 => b q.1 q.2)
    (hbc : ∀ s, Continuous (b s)) (hJm : ∀ i j, Measurable fun t => Jm t i j)
    (hADm : ∀ d, Measurable fun q : Set.Icc tA tZ × Vec 2 => AD d q.1 q.2)
    (hAD : ∀ s ∈ Set.Icc tA tZ, ∀ d, ContDiff ℝ 1 (AD d s))
    (hCEm : ∀ r ∈ Finset.Icc 1 H, ∀ v u d,
      Measurable fun q : Set.Icc tA tZ × Vec 2 => CE r v u d q.1 q.2)
    (hCE : ∀ s ∈ Set.Icc tA tZ, ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hcm : ∀ r : CoupledFourierModeIndex (h := h) n,
      Measurable fun s : Set.Icc tA tZ => coarseCoeff n W r s)
    (haRm : Measurable fun q : Set.Icc tA tZ × Vec 2 => aRep q.1 q.2)
    (hrep : ∀ s ∈ Set.Icc tA tZ, ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀) :
    JointlyMeas tA tZ (defectRemainder n b Dl H AD CE Jm W aRep) := by
  have haJ : ∀ v, JMF tA tZ Dl fun s x => aRep s x v := fun v =>
    ⟨(measurable_pi_apply v).comp haRm, fun s hs =>
      (hrep s hs v).2.1.of_le (by exact_mod_cast hDr)⟩
  have hTJ : ∀ v, JMF tA tZ Dl fun s x => coarseTraj n W s x v := fun v =>
    ⟨(measurable_pi_apply v).comp (jointlyMeas_coarseTraj n W hcm), fun s _ =>
      (contDiff_pi.1 (coarseTraj_contDiff n W s) v).of_le (order_natCast_le_top _)⟩
  have h1 : Measurable fun q : Set.Icc tA tZ × Vec 2 =>
      coarseProjField n (classicalDefectField b Dl H AD CE Jm aRep q.1) q.2 :=
    jointlyMeas_coarseProjField n (fun s => classicalDefectField b Dl H AD CE Jm aRep s)
      fun v => jointlyMeas_classicalDefectField hDl hbm hbc hJm hADm hAD hCEm hCE aRep haJ v
  have h2 : Measurable fun q : Set.Icc tA tZ × Vec 2 =>
      (fun v => classicalDefectField b Dl H AD CE Jm (coarseTraj n W) q.1 v q.2 : ∀ v, h v) :=
    Measurable.of_eval fun v =>
      jointlyMeas_classicalDefectField hDl hbm hbc hJm hADm hAD hCEm hCE (coarseTraj n W) hTJ v
  exact Measurable.fun_sub h1 h2

end Defect

end AVRegularity.CycleComparison.Reconstruction
end
