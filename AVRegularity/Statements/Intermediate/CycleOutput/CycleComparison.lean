-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Proofs.Intermediate.CycleOutput.CycleComparison
public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseWindow
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseChartIndex
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation
public import AVRegularity.Statements.Intermediate.CycleOutput.ObsErrorNorm
public import AVRegularity.Statements.Intermediate.CycleOutput.CompBill
public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveK
public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveMout
public import AVRegularity.Statements.Intermediate.CycleJoint.JointOperator
public import AVRegularity.Statements.Intermediate.CycleJoint.TorusHkNorm
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.FamilyAtlas
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponses
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
public import AVRegularity.Statements.Intermediate.CycleComparison.CovarianceMatrix
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CycleReference.OcRefFlux
public import AVRegularity.Statements.Intermediate.CycleReference.OcChart
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.OcDelta
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible

/-! The comparison proposition of one cycle: the coarse family and the physical error.

`hquiet` asserts fast independence on the trimmed quiet times `ocTrimmedQuietTimes` of `I` (the
times whose `τ_m/24`-neighbourhood is quiet), and the quiet transitions of the atlas (`hTq`,
`ChartedFamily.IsQuietTransition`) carry the transport identity summed over the permutations of the
word. The proof term does not mention the named hypotheses behind the quantifiers, hence the
`set_option linter.unusedVariables false` above the theorem.

Premises: the common `(t_p, P)` of the joint preparation `cycle_joint` is the pair of
hypotheses `hjm : IsJointModel …`, `hje : IsJointError …` (the joint's conclusion for the
supplied constants `Cj, CPj, cj` and the model order `Mout` of the reserve formula); the observation
window `I = [t_p, t_p + T_obs]` of algebraic length (`hTobs`); both independent envelopes (`henv`),
the forward molecular envelope (`hfwd`, `IsSampledEnvelope`), the
chart and quiet hypotheses on the entire later window (`cov`, `htrans`, `hquiet`), the fine drift
energy conditions at `ρ_*` (`hjets`, `hB₂ρ`, `hab`), the descending slots, the actual equations
(the solution class of the coupled energy estimate `coupled_energy_torus`, with the drift `𝐛_m`),
the prepared inputs.

Quantifier order: construction `→` accuracy, depth, orders, slots, the window exponent
`→` finite order choices `(A', N', J', p')`, `M_out` (the reserve formula `compReserveMout`), the
reserves and lift output orders `→` supplied bounds and the joint's constants `→` constants and the
starting level `→` the data (level, window, family, `t_p`, `P`) `→` the lifts `Cc`, the time
partition `ϖ`, the coarse letters `(AD, CE)` (the witnesses of the family, before the datum) `→`
the datum `f` and the actual solution `u` `→` the coarse family `U, W`, its classical
representative `aRep`, the lift `û = 𝒯 W`, and the residual presentation `(R, q)`.

Conclusion: the lift sequences of the pulses of the window (`IsLiftSequence` of `pulseLiftData`, on
the lift window of the pulse clipped to `I`: the new lift coefficients start from zero at the quiet
`t_p`), the time partition (`IsLiftPartition`), the letters presenting the glued means
(`IsMeanPresentation` of `gluedMean`), the means bound (entrywise, orders `E` and `R`), the diagonal
size `α_R ≤ C E^{2δ}`; for the datum: the finite causal family of genuine forced equations with
principal operator `L_c = ∂_t + 𝐛_{m-1}·∇ - BΔ` (`IsCoarseResponses`, `IsCoarseWitness`,
`IsCoarseDefect`: the retained vector `a = W` with `a(t_p) = Pf`), the triangular physical lift
`û = 𝒯a` (`gluedLift`, on the classical representative `IsClassicalRep`), the error bound
(`obsErrorNorm`), and the residual presentation `(R, q)` of `û` in the actual equation (the forced
solution class) bounded by `C 𝔅 F_π` (`compBill`). The statement does not include prescribed
differentiated residual presentations.

Charted families: the coarse family is a charted family `F` (independent chart representatives with
retained contexts, `actual` the selected contexts, time partition `weight`).
* `hcover`: the output intervals `J_p` of the pieces cover `[t_S, t_p + T_obs]` (so the partition
  sums to one and the physical coefficient `edgeCoefficient` of the equations is the assembly of
  the pieces); `0 < T_obs` (the essential time supremum of the envelopes needs a window of
  positive measure).
* `henv`, `hfwd`: the analytic and molecular envelopes uniform over the declared domain
  `Domain.onWindow F I` (all pieces at their own output times in `I = [t_p, t_p + T_obs]`, all
  retained contexts, all slow labels: anchor paths and Taylor segments are inside) and the sampled
  forward envelope of the Piola-assembled physical coefficient on `I`, with the same matrix `A`;
  these are supplied, not outputs of preparation.
* `htrans`, `hquiet`, `T`, `hTcons`, `hTcov`, `hTq`: transversality on the enlarged pulses and
  fast independence on the trimmed quiet times of `I` (independent fields, all pieces and
  contexts); the atlas `T` stores the chart transitions between the consecutive renewal labels
  whose outputs meet `I`, with overlaps containing every common quiet time of `I`, and on them
  the quiet Piola transport, summed over the permutations of the word, holds with the
  context identification.
* `pp`, `hpp`: the piece of each observed pulse `k` is the natural renewal chart
  `ocPulseChartIndex k`, its material map is `ocChart`, and its output interval contains the
  pulse window clipped to `I`; the lift of the pulse is built from the chart-frame fiber
  `F.fiber (pp k) (actual (pp k))`.
* `htorus`: torus compatibility of the family (`IsTorusCompatible`): the material
  charts commute with integer translations and each selected flux is `E⁻¹ℤ²`-periodic in the
  normalized slow variable, with `E = ε_{m-1}`; this gives `ℤ²`-periodic physical edge
  coefficients. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity

set_option linter.unusedVariables false in
/-- **The coarse family and physical error.** -/
theorem cycle_comparison (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (H D Kmax : ℕ), 2 ≤ D → ∀ (Aobs Cobs : ℝ),
      ∃ (Ac Nc Jc pc Mout : ℕ) (_ : Mout = compReserveMout Ac Nc Jc pc D H Kmax)
        (hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mout)
        (Ks Ls Jm qJ Klift Llift : ℕ),
        max (Mout + Ac + Kmax + 2) (Ac + 2 + Kmax + D * (H + 1) * Nc) ≤ Klift ∧
        Kmax + D * (H + 1) * Nc ≤ Llift ∧
      ∀ (Ca Cfw Cth Cb cMol Cj CPj cj Cpart : ℝ) (Cm CG : ℕ → ℝ), 0 < cMol → 0 < cj →
      ∃ (C CP cb : ℝ) (CK : ℕ → ℝ) (mStar : ℕ), 0 < cb ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (hm2 : 2 ≤ m) (hmStar : mStar ≤ m) (hmM : m ≤ M') (ν B : ℝ)
        (hν : κ m = ν) (hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tp Tobs : ℝ) (htS : tS < tp) (hTobs₀ : 0 < Tobs)
        (hTobs : Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs))
        (htpq : tp ∈ ocQuietTimes α q Λ ζ m)
        (g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) (ocRhoMol α q Λ m cMol ν) g g₀ a
          B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (hdepth : F.HasDepthAtMost H) (hdesc : F.IsDescending K)
        (htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (hcover : Set.Icc tS (tp + Tobs) ⊆ ⋃ p, (F.piece p).output)
        (hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1)
        (henv : IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
        (hpointwiseMol : IsPointwiseMolecularEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u))
        (hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls (fun v u => Real.sqrt (π u / π v) * A v u))
        (hfwd : IsSampledEnvelope F π K actual tp (tp + Tobs) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν) Cfw
          (fun v u => Real.sqrt (π u / π v) * A v u))
        (htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (T : F.Atlas)
        (hTcons : T.IsConsecutiveClosed (Set.Icc tp (tp + Tobs)))
        (hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs)))
        (hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (hTact : ∀ p q (hpq : T.adjacent p q),
          ((F.piece p).output ∩ (F.piece q).output ∩ Set.Icc tp (tp + Tobs)).Nonempty →
            T.sameCtx p q hpq (actual p) (actual q))
        (pp : ℤ → P')
        (hpp : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
          (∀ t, ⇑((F.piece (pp k)).material t) =
            ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) ∧
          ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output)
        (hppinj : Set.InjOn pp (↑(ocObsPulses α q Λ m tp (tp + Tobs)) : Set ℤ))
        (hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs))
          (ocTau α q Λ m) Cpart)
        (a₂ B₂ lam₂ : ℝ) (ha₂ : 0 ≤ a₂) (hB₂ : 1 ≤ B₂) (hlam₂ : 0 < lam₂)
        (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ m) t)) l x‖ ≤
            a₂ * B₂ ^ l * (l.factorial : ℝ) * lam₂ ^ ((1 : ℤ) - l))
        (hB₂ρ : B₂ * ocRhoMol α q Λ m cMol ν / lam₂ ≤ 1 / 2)
        (hab : a₂ * B₂ * ocRhoMol α q Λ m cMol ν ^ 2 ≤ ν / 8)
        (ρold : ℝ)
        (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (hjm : IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
          (cj * Real.sqrt (B * ocTauPP α q Λ m)) Cj CPj Pd Pg)
        (hje : IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
          (ocEpsilon q Λ (m - 1)) Pacc CPj (streamVel (Φ m))
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg),
      ∃ (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
        (AD : ∀ d : Finset.Icc 2 (Nc + D), ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (Nc + D)), ℝ → Vec 2 →
          (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
            (PiLp 2 (fun _ : Fin 2 => h v))),
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
            (Real.sqrt (B * ocTauPP α q Λ m))
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k))))
            (Klift + D + 2) (Llift + 2)
            (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2)
            (min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) (tp + Tobs) / ocEll q Λ m ν ^ 2) Nc H
            (Cc k)) ∧
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc tp (tp + Tobs)) (Nc + D) r AD CE
          (ocRefFlux α q Λ ζ m ν)
          (gluedMean (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k)) (ocEll q Λ m ν ^ 2)
            (Real.sqrt (B * ocTauPP α q Λ m))
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) Nc r
            (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
              (Real.sqrt (B * ocTauPP α q Λ m))
              (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)))) ∧
        (∀ r, 1 ≤ r → r ≤ H → ∀ K' : ℕ,
          K' ≤ compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) → ∀ v u,
          ENNReal.ofReal (Real.sqrt (π u / π v)) *
            ((∑ d : Finset.Icc 2 (Nc + D),
                coefficientSeminorm (ocEpsilon q Λ (m - 1)) K' tp (tp + Tobs) (CE r v u d) *
                  (ENNReal.ofReal (B * ocEpsilon q Λ (m - 1) ^ (d.1 - 2)))⁻¹) +
              ∑ d : Finset.Icc 2 (Nc + D),
                coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m)) K' tp (tp + Tobs)
                  (CE r v u d) *
                  (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹) ≤
            ENNReal.ofReal (CK K' * (Real.sqrt (π u / π v) * (A ^ r) v u))) ∧
        (∑ d : Finset.Icc 2 (Nc + D),
            coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m))
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
              tp (tp + Tobs) (AD d) *
              (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹) ≤
          ENNReal.ofReal (C * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) ∧
        compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc ≤
          C * ocEpsilon q Λ (m - 1) ^ Pacc ∧
        ∀ (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ),
          (∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) →
            ∃ (U : ∀ (i j : ℕ) (v : ι), ℝ →
                TorusHk (coarseSlot (compReserveK Ac Nc D H Kmax) Jc H
                  ((Nc + D) + 8 * pc + 4) i j) (h v))
              (Uw : ∀ (i j : ℕ) (v : ι), ℝ →
                TorusHk (coarseSlot (compReserveK Ac Nc D H Kmax) Jc H
                  ((Nc + D) + 8 * pc + 4) i j + 1) (h v))
              (G : ∀ (i j : ℕ) (v : ι), ℝ →
                TorusHk (coarseSlot (compReserveK Ac Nc D H Kmax) Jc H
                  ((Nc + D) + 8 * pc + 4) i j) (PiLp 2 (fun _ : Fin 2 => h v)))
              (W : ∀ v, ℝ → TorusHk (compReserveK Ac Nc D H Kmax + 1 + (Nc + D)) (h v))
              (Fc : ∀ v, ℝ → TorusHk (compReserveK Ac Nc D H Kmax)
                (PiLp 2 (fun _ : Fin 2 => h v)))
              (aRep : ℝ → Vec 2 → ∀ i, h i)
              (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
              (Rres : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
              (qres : ∀ v, ℝ → TorusHk (K v) (h v)),
              IsCoarseResponses tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
                (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4)
                (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
                (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp)
                (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                  (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                    v)) U Uw G ∧
              IsCoarseWitness tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
                (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4) AD CE
                (ocRefFlux α q Λ ζ m ν) (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp) U W Fc ∧
              IsCoarseDefect tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H
                (compReserveK Ac Nc D H Kmax)
                (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
                (ocRefFlux α q Λ ζ m ν)
                (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                  (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                    v)) W Fc ∧
              (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
                IsClassicalRep (W v t) (fun x => aRep t x v)
                  (compReserveK Ac Nc D H Kmax + (Nc + D) - 1)) ∧
              (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
                (û v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
                  fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
                    (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ m)
                    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) Nc H Cc
                    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    aRep t x v) ∧
              IsCoupledWeakSolutionTorus ν tp (tp + Tobs) (streamVel (Φ m)) D K
                (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
                (fun v => û v tp) Rres qres û ŵ ∧
              residualNorm ν π (Set.Icc tp (tp + Tobs))
                  (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 (K v)) x) k)
                  (fun t x v => (qres v t).toFunction.jet (valueIndex2 (K v)) x) ≤
                ENNReal.ofReal (C * compBill α q Λ m ν B Tobs cb
                  (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc *
                  Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)) ∧
              ∀ (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v)),
                IsCoupledWeakSolutionTorus ν tS (tp + Tobs) (streamVel (Φ m)) D K
                  (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) f
                  (fun _ _ => 0) (fun _ _ => 0) u w →
                obsErrorNorm ν π K tp (tp + Tobs) (fun v t => u v t - û v t)
                  (fun v t => w v t - ŵ v t) ≤
                  ENNReal.ofReal (CP * ocEpsilon q Λ (m - 1) ^ Pacc *
                    Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)) :=
  by exact AVRegularity.Providers.cycle_comparison α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity
