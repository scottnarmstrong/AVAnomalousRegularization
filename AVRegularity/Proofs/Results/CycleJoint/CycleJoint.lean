-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfOpen
import AVRegularity.CycleWords.Seam.S3CycleSeam
import AVRegularity.CycleWords.Seam.B1PlainStage
public import AVRegularity.Definitions.Construction.ScheduleFloor
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Pointwise molecular bounds of the retained preserved solution, from the
context certificates and the shared all-history Cauchy/Fourier envelope theorem.

Special cases: identity metric, minimum jet orders, singleton, EMPTY component types and
edgeless seeds retain the exact hypotheses; root spaces may be trivial. -/

open AVRegularity.Construction.Preservation.Assembly

/-- **Pointwise molecular envelope of the preserved solution**. -/
theorem preservation_pointwise_molecular_envelope (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (mStar : ℕ) (Cpt : ℕ → ℝ),
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      ∀ (tA tB : ℝ) (K : CompIn (G'.retained m H J).comps → ℕ),
        (∀ v, K v ≤ kI.Ks) →
      IsPointwiseMolecularEnvelope (G'.retained m H J).fam
        ((G'.retained m H J).mass law) K
        ((G'.retained m H J).innerDomain (Set.Icc tA tB) kI.mEnv)
        (D.kap (G'.retained m H J).level) (D.eps (G'.retained m H J).level)
        (D.eps ((G'.retained m H J).level - 1))
        (rhoStar D kI.c₀ (G'.retained m H J).level) Cpt kI.Jm
        (recordMajorant ((G'.retained m H J).mass law) (G'.retained m H J).fam) := by
  exact preservation_pointwise_molecular_envelope_of_ingredients α s q ζ
    (retained_pointwise_context_inputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Proof of `cycle_joint`.

`cycle_joint` is `cycleJoint_of_quietMarginDatum` (module `CycleWords.Seam.S3CycleSeam`:
`cycle_joint_of_cycleSeam` at the statement of `cycle_seam`) at `quietMarginDatum`. -/

/-- **The joint cycle**. Proposition 11.7 of the paper follows from it by a comparison of norms. -/
theorem cycle_joint (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ) (CH : ℝ), 0 < CH ∧ CH = 2 ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
        0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + CH * ocTauPP α q Λ m)
          (ocRhoMol α q Λ m cMol ν) g g₀ a B₀
          lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + CH * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ (tp : ℝ) (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
        tp ∈ Set.Ioc tS (tS + CH * ocTauPP α q Λ m) ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
        Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
        ∀ (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
          (_henv : IsEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
          (_hpointwise : IsPointwiseMolecularEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)),
          IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
            (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP Pd Pg ∧
          IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
            (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg :=
  CycleWords.Seam.cycleJoint_of_quietMarginDatum CycleWords.Seam.quietMarginDatum α s hα₀ hα₁ hs₀
    hs₁ q hq ζ hζ

end AVRegularity.Providers
end
end
