-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Diagonal.Main
import AVRegularity.CycleComparison.Reconstruction.PhysicalLiftProof
import AVRegularity.CycleComparison.Assembly.TrimmedStatement
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponses
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
public import AVRegularity.Statements.Intermediate.CycleOutput.CompBill
public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveMout
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation
public import AVRegularity.Statements.Intermediate.CycleOutput.ObsErrorNorm
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible

@[expose] public section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_comparison_diagonal_mean`, from
`AVRegularity.CycleComparison.Diagonal.pulse_diagonal_two` and the explicit form of the
order-two diagonal letter (`diagonalMeanLetter_two_apply`). -/

/-- **The order-two diagonal mean of one pulse against the reference flux**. -/
theorem cycle_comparison_diagonal_mean (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (CGI : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (ν B ρ lam : ℝ) (kp : ℤ) (edge : ConstituentEdges D h) (π : ι → ℝ)
        (t₀ t₁ E dstar εc : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (b : ι → ι → ℝ)
        (Θ g : ℝ),
        IsFastProfile ζ → 1 ≤ Λ → Odd kp →
        IsLiftSetting (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) π t₀ t₁ (ocEpsilon q Λ m)
          ν B ρ E (ocEll q Λ m ν) dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
        0 ≤ g →
        (∀ r, r ≤ qs →
          (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2,
            ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
              (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).G t X' i j -
                (if i = j then 1 else 0)) X‖ₑ)
            ≤ ENNReal.ofReal (CGI r * g * lam ^ r)) →
        (∀ t ∈ Set.Icc t₀ t₁, ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m kp) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
          IsLiftSequence (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) (K + D + 2)
            (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
          ∀ (α' : DerivativeWord2 1) (l : Fin 2) (v : ι) (j : ℕ), j ≤ K →
            ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
            ‖iteratedFDeriv ℝ j (fun X' =>
                B • (fieldCellMean (fun z =>
                    (Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).η *
                      (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).v t z l) •
                      Cc 0 1 1 α' t X' z v v) +
                  (-(pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).η *
                    (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).G t X' l (α' 0)) •
                      ContinuousLinearMap.id ℝ (h v)) +
                  ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) •
                    ContinuousLinearMap.id ℝ (h v)) X‖ ≤
              C * B * g * lam ^ j +
                (if j = 0 then ocMu q Λ m ν * ocHStar α q Λ m ν *
                  ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀) else 0) := by
  obtain ⟨C, hC, hpd⟩ := CycleComparison.Diagonal.pulse_diagonal_two N K k L D H CG Cw Cj CGI
  refine ⟨C, hC, ?_⟩
  intro ι _ _ h _ _ _ _ α q Λ m ζ φ hφ ν B ρ lam kp edge π t₀ t₁ E dstar εc par V qs qf b Θ g hζ
    hΛ hk P hg hGI hwin Cc hseq α' l v j hj t ht X
  have e : (fun X' => B • (fieldCellMean (fun z =>
        (Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).η *
          (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).v t z l) •
          Cc 0 1 1 α' t X' z v v) +
      (-(pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).η *
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).G t X' l (α' 0)) •
          ContinuousLinearMap.id ℝ (h v)) +
      ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) •
        ContinuousLinearMap.id ℝ (h v)) =
      fun X' => B • CycleComparison.LiftMeanEntrywise.diagonalMeanLetter
          (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) Cc 2 2 α' t X' l v v +
        ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) •
          ContinuousLinearMap.id ℝ (h v) := by
    funext X'
    rw [CycleComparison.Diagonal.diagonalMeanLetter_two_apply,
      CycleComparison.LiftMeanEntrywise.blockIdentityEntry_self]
  rw [e]
  exact hpd α q Λ m ζ φ hφ ν B ρ lam kp edge π t₀ t₁ E dstar εc par V qs qf b Θ g hζ hΛ hk P hg
    hGI hwin Cc hseq α' l v j hj t ht X

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_comparison_physical_lift`: the physical
reconstruction of the comparison window, proved in
`CycleComparison.Reconstruction.physicalLift_proof`. -/

/-- **The physical reconstruction of the comparison window**. -/
theorem cycle_comparison_physical_lift (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ g₀ : ℝ, 0 < g₀ → g₀ ≤ 1 / 4 →
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (H D Kmax : ℕ), 2 ≤ D → ∀ (Aobs Cobs : ℝ),
      ∀ (Ac Nc Jc pc Mout : ℕ) (_ : Mout = compReserveMout Ac Nc Jc pc D H Kmax)
        (hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mout)
        (Ks Ls Jm qJ Klift Llift : ℕ),
        max (Mout + Ac + Kmax + 2) (Ac + 2 + Kmax + D * (H + 1) * Nc) ≤ Klift →
        Kmax + D * (H + 1) * Nc + 1 ≤ Llift → 1 ≤ Ac → 1 ≤ Nc → 1 ≤ pc →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ Ks → Llift + 2 + H * D + 2 * Nc + 2 * D ≤ Ls →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ qJ →
      ∀ (Ca Cfw Cth Cb cMol Cj CPj cj Cpart : ℝ) (Cm CG : ℕ → ℝ), 0 < cMol → 0 < cj →
      ∀ (C4 Cstar Θc : ℝ),
      ∃ (C cb : ℝ) (mStar : ℕ), 0 < cb ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tp Tobs : ℝ) (_htS : tS < tp) (_hTobs₀ : 0 < Tobs)
        (_hTobs : Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs))
        (_htpq : tp ∈ ocQuietTimes α q Λ ζ m)
        (g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) (ocRhoMol α q Λ m cMol ν) g g₀ a
          B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tp + Tobs) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_henv : IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
        (_hpointwiseMol : IsPointwiseMolecularEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u))
        (_hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls (fun v u => Real.sqrt (π u / π v) * A v u))
        (_hfwd : IsSampledEnvelope F π K actual tp (tp + Tobs) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν) Cfw
          (fun v u => Real.sqrt (π u / π v) * A v u))
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tp (tp + Tobs)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (_hTact : ∀ p q (hpq : T.adjacent p q),
          ((F.piece p).output ∩ (F.piece q).output ∩ Set.Icc tp (tp + Tobs)).Nonempty →
            T.sameCtx p q hpq (actual p) (actual q))
        (pp : ℤ → P')
        (_hpp : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
          (∀ t, ⇑((F.piece (pp k)).material t) =
            ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) ∧
          ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output)
        (_hppinj : Set.InjOn pp (↑(ocObsPulses α q Λ m tp (tp + Tobs)) : Set ℤ))
        (_hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs))
          (ocTau α q Λ m) Cpart)
        (a₂ B₂ lam₂ : ℝ) (_ha₂ : 0 ≤ a₂) (_hB₂ : 1 ≤ B₂) (_hlam₂ : 0 < lam₂)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ m) t)) l x‖ ≤
            a₂ * B₂ ^ l * (l.factorial : ℝ) * lam₂ ^ ((1 : ℤ) - l))
        (_hB₂ρ : B₂ * ocRhoMol α q Λ m cMol ν / lam₂ ≤ 1 / 2)
        (_hab : a₂ * B₂ * ocRhoMol α q Λ m cMol ν ^ 2 ≤ ν / 8)
        (ρold : ℝ)
        (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (_hjm : IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
          (cj * Real.sqrt (B * ocTauPP α q Λ m)) Cj CPj Pd Pg)
        (_hje : IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
          (ocEpsilon q Λ (m - 1)) Pacc CPj (streamVel (Φ m))
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg),
      ∀ (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
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
            (Cc k)) →
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc tp (tp + Tobs)) (Nc + D) r AD CE
          (ocRefFlux α q Λ ζ m ν)
          (gluedMean (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2)
            (Real.sqrt (B * ocTauPP α q Λ m))
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) Nc r
            (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
              (Real.sqrt (B * ocTauPP α q Λ m))
              (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)))) →
        (∑ d : Finset.Icc 2 (Nc + D),
            coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m))
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
              tp (tp + Tobs) (AD d) *
              (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹) ≤
          ENNReal.ofReal (C4 * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) →
        ∀ (a B₀ lam : ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting tp (tp + Tobs) (Real.sqrt (B * ocTauPP α q Λ m)) B a B₀ lam
          (streamVel (Φ (m - 1))) (Nc + D) H pc Jc (compReserveK Ac Nc D H Kmax)
          ((Nc + D) + 8 * pc + 4)
          (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
          (ocRefFlux α q Λ ζ m ν) AD CE π Aedge Cstar Θc →
        ∀ (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ),
          (∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) →
            ∀ (U : ∀ (i j : ℕ) (v : ι), ℝ →
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
              (aRep : ℝ → Vec 2 → ∀ i, h i),
            IsCoarseResponses tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
              (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4)
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
              (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp)
              (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                  v)) U Uw G →
            IsCoarseWitness tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
              (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4) AD CE
              (ocRefFlux α q Λ ζ m ν) (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp) U W Fc →
            IsCoarseDefect tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H
              (compReserveK Ac Nc D H Kmax)
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
              (ocRefFlux α q Λ ζ m ν)
              (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                  v)) W Fc →
            (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
              IsClassicalRep (W v t) (fun x => aRep t x v)
                (compReserveK Ac Nc D H Kmax + (Nc + D) - 1)) →
            ∃ (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
              (Rres : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
              (qres : ∀ v, ℝ → TorusHk (K v) (h v)),
              (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
                (û v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
                  fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
                    (fun k => F.weight (pp k))
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
              (∀ v, û v tp = truncateTorusHk (le_max_right Mout (K v))
                (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)) ∧
              (∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
              (∀ v, Integrable (qres v) (volume.restrict (Set.Icc tp (tp + Tobs)))) ∧
              ν⁻¹ * ∫ s in Set.Icc tp (tp + Tobs),
                  massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K)
                    (ocRhoMol α q Λ m cMol ν) π (fun v => (Rres v s).val) ≤
                (C * compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card
                  Ac Nc Jc pc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)) ^ 2 ∧
              ∫ s in Set.Icc tp (tp + Tobs),
                  Real.sqrt (massNormSq (E := h) (K := K) (ocRhoMol α q Λ m cMol ν) π
                    (fun v => (qres v s).val)) ≤
                C * compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card
                  Ac Nc Jc pc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) :=
  CycleComparison.Reconstruction.physicalLift_proof α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Proof of `cycle_comparison_reconstruction`: the physical
reconstruction (`CycleComparison.Reconstruction.physicalLift_proof`) with the error clause
(`CycleComparison.Assembly.reconstruction_of_physicalLift`), assembled in
`CycleComparison.Assembly.reconstruction_holds`. -/

/-- **The reconstruction of the comparison window**. -/
theorem cycle_comparison_reconstruction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ g₀ : ℝ, 0 < g₀ → g₀ ≤ 1 / 4 →
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (H D Kmax : ℕ), 2 ≤ D → ∀ (Aobs Cobs : ℝ),
      ∀ (Ac Nc Jc pc Mout : ℕ) (_ : Mout = compReserveMout Ac Nc Jc pc D H Kmax)
        (hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mout)
        (Ks Ls Jm qJ Klift Llift : ℕ),
        max (Mout + Ac + Kmax + 2) (Ac + 2 + Kmax + D * (H + 1) * Nc) ≤ Klift →
        Kmax + D * (H + 1) * Nc + 1 ≤ Llift → 1 ≤ Ac → 1 ≤ Nc → 1 ≤ pc →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ Ks → Llift + 2 + H * D + 2 * Nc + 2 * D ≤ Ls →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ qJ →
      ∀ (Ca Cfw Cth Cb cMol Cj CPj cj Cpart : ℝ) (Cm CG : ℕ → ℝ), 0 < cMol → 0 < cj →
      ∀ (C4 Cstar Θc : ℝ),
      ∃ (C CP cb : ℝ) (mStar : ℕ), 0 < cb ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tp Tobs : ℝ) (_htS : tS < tp) (_hTobs₀ : 0 < Tobs)
        (_hTobs : Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs))
        (_htpq : tp ∈ ocQuietTimes α q Λ ζ m)
        (g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) (ocRhoMol α q Λ m cMol ν) g g₀ a
          B₀ lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tp + Tobs) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_henv : IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
        (_hpointwiseMol : IsPointwiseMolecularEnvelope F π K
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
          Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u))
        (_hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls (fun v u => Real.sqrt (π u / π v) * A v u))
        (_hfwd : IsSampledEnvelope F π K actual tp (tp + Tobs) ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν) Cfw
          (fun v u => Real.sqrt (π u / π v) * A v u))
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tp (tp + Tobs)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (_hTact : ∀ p q (hpq : T.adjacent p q),
          ((F.piece p).output ∩ (F.piece q).output ∩ Set.Icc tp (tp + Tobs)).Nonempty →
            T.sameCtx p q hpq (actual p) (actual q))
        (pp : ℤ → P')
        (_hpp : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          (F.piece (pp k)).label = ocPulseChartIndex α q Λ m k ∧
          (∀ t, ⇑((F.piece (pp k)).material t) =
            ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) ∧
          ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output)
        (_hppinj : Set.InjOn pp (↑(ocObsPulses α q Λ m tp (tp + Tobs)) : Set ℤ))
        (_hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
          (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tp (tp + Tobs))
          (ocTau α q Λ m) Cpart)
        (a₂ B₂ lam₂ : ℝ) (_ha₂ : 0 ≤ a₂) (_hB₂ : 1 ≤ B₂) (_hlam₂ : 0 < lam₂)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc tp (tp + Tobs), ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ m) t)) l x‖ ≤
            a₂ * B₂ ^ l * (l.factorial : ℝ) * lam₂ ^ ((1 : ℤ) - l))
        (_hB₂ρ : B₂ * ocRhoMol α q Λ m cMol ν / lam₂ ≤ 1 / 2)
        (_hab : a₂ * B₂ * ocRhoMol α q Λ m cMol ν ^ 2 ≤ ν / 8)
        (ρold : ℝ)
        (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (_hjm : IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
          (cj * Real.sqrt (B * ocTauPP α q Λ m)) Cj CPj Pd Pg)
        (_hje : IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
          (ocEpsilon q Λ (m - 1)) Pacc CPj (streamVel (Φ m))
          (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg),
      ∀ (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
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
            (Cc k)) →
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc tp (tp + Tobs)) (Nc + D) r AD CE
          (ocRefFlux α q Λ ζ m ν)
          (gluedMean (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2)
            (Real.sqrt (B * ocTauPP α q Λ m))
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) Nc r
            (fun k => pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B
              (Real.sqrt (B * ocTauPP α q Λ m))
              (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
            (F.fiber (pp k) (actual (pp k)))) Cc
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k)))) →
        (∑ d : Finset.Icc 2 (Nc + D),
            coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m))
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
              tp (tp + Tobs) (AD d) *
              (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹) ≤
          ENNReal.ofReal (C4 * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) →
        ∀ (a B₀ lam : ℝ) (Aedge : Matrix ι ι ℝ),
        IsCoarseSetting tp (tp + Tobs) (Real.sqrt (B * ocTauPP α q Λ m)) B a B₀ lam
          (streamVel (Φ (m - 1))) (Nc + D) H pc Jc (compReserveK Ac Nc D H Kmax)
          ((Nc + D) + 8 * pc + 4)
          (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
          (ocRefFlux α q Λ ζ m ν) AD CE π Aedge Cstar Θc →
        ∀ (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ),
          (∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) →
            ∀ (U : ∀ (i j : ℕ) (v : ι), ℝ →
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
              (aRep : ℝ → Vec 2 → ∀ i, h i),
            IsCoarseResponses tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
              (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4)
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
              (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp)
              (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                  v)) U Uw G →
            IsCoarseWitness tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H pc
              (compReserveK Ac Nc D H Kmax) Jc ((Nc + D) + 8 * pc + 4) AD CE
              (ocRefFlux α q Λ ζ m ν) (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B tp) U W Fc →
            IsCoarseDefect tp (tp + Tobs) B (streamVel (Φ (m - 1))) (Nc + D) H
              (compReserveK Ac Nc D H Kmax)
              (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) AD CE
              (ocRefFlux α q Λ ζ m ν)
              (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
                (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v))
                  v)) W Fc →
            (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
              IsClassicalRep (W v t) (fun x => aRep t x v)
                (compReserveK Ac Nc D H Kmax + (Nc + D) - 1)) →
            ∃ (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
              (Rres : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
              (qres : ∀ v, ℝ → TorusHk (K v) (h v)),
              (∀ t ∈ Set.Icc tp (tp + Tobs), ∀ v,
                (û v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
                  fun x => gluedLift (ocObsPulses α q Λ m tp (tp + Tobs))
                    (fun k => F.weight (pp k))
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
                  ENNReal.ofReal (CP * (ocEpsilon q Λ (m - 1) ^ Pacc +
                    compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card
                      Ac Nc Jc pc) * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2))  :=
  CycleComparison.Assembly.reconstruction_holds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
