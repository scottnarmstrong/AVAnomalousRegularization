-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation
public import AVRegularity.Statements.Intermediate.CycleOutput.CompBill
public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveMout
public import AVRegularity.Statements.Intermediate.Families.IsEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponses
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseDefect
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.CycleComparison.Reconstruction.PhysicalLiftPartition
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.CycleComparison.Assembly.OfPhysicalLift
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
import Mathlib.Algebra.Order.Star.Real

/-! **The physical reconstruction of the comparison window** (proof of
`cycle_comparison_physical_lift`). The constants are those of the lift settings
(`LiftSetting.lift_setting`), the lift grading (`Providers.cycle_lift_grading`), the partition
terms (`partition_window_input`) with the pulse count absorbed by the quiet exponential
(`card_exp_le_of_scaleLaws`, `cb = c/2`), the coarse energies on the coarse setting rescaled to
the actual drift scales (`coarse_drift_small`, `IsCoarseSetting.rescale`, `coarse_energy_bill`,
`coarse_flux_small`, `coarse_flux_offdiag`) and the joint model (`jointModel_massNormSq_le`). On
each window the premises give a reconstruction window (`ReconWindow`) at the orders
`ReconOrders` (`A_cl = A_c ≥ 1`), and `ReconWindowAt.physical_lift` gives the
conclusion with the bill `𝔅 = compBill` and `M = (∑ π⁻¹ F_v²)^{1/2}`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleComparison.Reconstruction

/-- **The physical reconstruction of the comparison window** (proof of
`cycle_comparison_physical_lift`). -/
theorem physicalLift_proof (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
  by
  classical
  -- the constants of the scales and of the lift settings, before `Λ`
  choose Λ₁ Cw hΛ₁ hG6 using CycleComparison.LiftSetting.lift_setting.{u_1, u_2, u_3, u_4} α s
    hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose Λ₂ B₀d C₁ _hΛ₂ hB₀d hC₁ hdrift using
    Assembly.coarse_drift_small α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose Λ₃ C₂ _hΛ₃ hC₂ hflux using Assembly.coarse_flux_small α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose Λ₄ C₃ _hΛ₄ hC₃ hoff using coarse_flux_offdiag α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose C₀ hC₀ Λ₅ _hΛ₅ hlaws using Assembly.scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λ₁ (max Λ₂ (max Λ₃ (max Λ₄ Λ₅))), hΛ₁.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ g₀ hg₀ hg₀4 Pacc hPacc H D Kmax hD Aobs Cobs Ac Nc Jc pc Mout hMout hN Ks Ls Jm qJ
    Klift Llift hK1 hL1 hAc hNc hpc hKs hLs hqJ Ca Cfw Cth Cb cMol Cj CPj cj Cpart Cm CG hcMol hcj
    C4 Cstar Θc
  simp only [max_le_iff] at hΛ
  have hΛ1 : Λ₁ ≤ Λ := hΛ.1
  have hΛ2 : Λ₂ ≤ Λ := hΛ.2.1
  have hΛ3 : Λ₃ ≤ Λ := hΛ.2.2.1
  have hΛ4 : Λ₄ ≤ Λ := hΛ.2.2.2.1
  have hΛ5 : Λ₅ ≤ Λ := hΛ.2.2.2.2
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ1
  choose CGl hG6' using hG6 Λ hΛ1 g₀ Ca CG hg₀4
  have hkc : compReserveK Ac Nc D H Kmax = 4 * (Nc + D) + 2 * Ac + 16 + Kmax + H * (D - 2) :=
    rfl
  have hK1b := (le_max_right _ _).trans hK1
  -- the constants of the grading, the partition terms, the pulse count and the coarse bill
  choose Cg hCg hgrad using Providers.cycle_lift_grading.{u_1, u_2} Nc Klift Llift Llift D H CGl
    Cw (fun _ _ => Ca)
  choose Cpt cpt hCpt hcpt hpartb using partition_window_input.{u_1, u_2, u_3, u_4} Ac Nc D H
    Kmax Klift Llift CGl Cw Ca Cpart hAc
  choose Kcard _hKcard hcard using card_exp_le_of_scaleLaws α s hα₀ hα₁ hs₀ hs₁ q hq Λ h128 C₀
    hC₀ Aobs Cobs cpt hcpt
  choose Ccb hCcb hcoarse using coarse_window_bill.{u_1, u_2} (Nc + D) H pc Jc
    (compReserveK Ac Nc D H Kmax) C₁ C₂ C₃ C4 Cstar Θc B₀d hB₀d hC₁ hC₂
  choose Sb hSbd using (⟨_, rfl⟩ : ∃ x : ℝ, x = max Cth 0)
  have hSb : 0 ≤ Sb := by rw [hSbd]; exact le_max_right _ _
  have hA0 : 0 ≤ Ccb * (C₁ + max C4 0) := mul_nonneg hCcb (add_nonneg hC₁ (le_max_right _ _))
  have hQ0 : 0 ≤ Ccb * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r :=
    mul_nonneg hCcb (Finset.sum_nonneg fun r _ =>
      pow_nonneg (mul_nonneg (abs_nonneg _) (le_max_right _ _)) r)
  have hCjm0 : 0 ≤ jointModelConst Cj Sb H
      (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) cj⁻¹ :=
    jointModelConst_nonneg Cj hSb H _ _
  have hsig := coarseSig_nonneg hA0 hQ0 Jc H
  have hbr : 0 ≤ coarseBracketConst (Ccb * (C₁ + max C4 0))
      (Ccb * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) C₂ C₃ Jc pc H := by
    unfold coarseBracketConst
    have := hC₃
    positivity
  choose Cs hCsd using (⟨_, rfl⟩ : ∃ x : ℝ, x = Ccb * coarseSig (Ccb * (C₁ + max C4 0))
    (Ccb * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) Jc H * jointModelConst Cj Sb H
      (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) cj⁻¹)
  choose Cy hCyd using (⟨_, rfl⟩ : ∃ x : ℝ, x = Ccb * coarseBracketConst (Ccb * (C₁ + max C4 0))
    (Ccb * ∑ r ∈ Finset.Icc 1 H, (|Cstar| * max Θc 0) ^ r) C₂ C₃ Jc pc H * jointModelConst Cj Sb H
      (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)) cj⁻¹)
  have hCs : 0 ≤ Cs := by rw [hCsd]; exact mul_nonneg (mul_nonneg hCcb hsig) hCjm0
  have hCy : 0 ≤ Cy := by rw [hCyd]; exact mul_nonneg (mul_nonneg hCcb hbr) hCjm0
  have hCpx : 0 ≤ Cpt * (1 + Sb) ^ H * Real.sqrt Kcard :=
    mul_nonneg (mul_nonneg hCpt (pow_nonneg (by linarith) _)) (Real.sqrt_nonneg _)
  refine ⟨reconBillConst H Nc D Ac Kmax (Ac + 1 + Kmax + 2 * Nc + D) (Ac + 3 + Kmax + Nc)
    (Ac + 2 + Kmax + 2 * Nc + D) Klift Llift CGl Cw Ca Sb Cg Cs Cy
    (Cpt * (1 + Sb) ^ H * Real.sqrt Kcard * Cs), cpt / 2, 0, half_pos hcpt, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π hπ K hK Φ hΦ M' κ hband m hm2 _ hmM ν B hν hB hφ tS tp Tobs htS
    hTobs₀ hTobs htpq g a B₀ lam l₀ P y₀ cov P' Ctx F actual hdepth hdesc htorus hcover hmeas A Θ
    hΘ₀ hΘ₁ henv hpointwiseMol hpointwiseAn hfwd htrans hquiet T hTcons hTcov hTq hTact pp hpp
    hppinj hpart a₂ B₂ lam₂ ha₂ hB₂ hlam₂ hjets hB₂ρ hab ρold Pd Pg hjm hje Cc AD CE hseq hmean
    hADsum aC B₀C lamC Aedge hcs f Fv hf U Uw G W Fc aRep hresp hwit hdef hrep
  -- the scales of the window
  have hνpos : 0 < ν := cov.pos.1
  have hBpos : 0 < B := cov.pos.2.1
  have hρm : 0 < ocRhoMol α q Λ m cMol ν := cov.pos.2.2
  have hρ : 0 < Real.sqrt (B * ocTauPP α q Λ m) := lt_of_lt_of_le hρm cov.rho_R
  have hL := hlaws Λ hΛ5 M' κ hband m hm2 hmM ν B hν hB
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
  have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hδ : 0 < ocDelta α q :=
    (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hΛ1' : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1'
  have hℓ : 0 < ocEll q Λ m ν := div_pos he (Real.sqrt_pos.2 hνpos)
  have htt : 0 ≤ ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q * ((Jc : ℝ) + 1)) +
      ocEpsilon q Λ (m - 1) ^ (ocDelta α q * (pc : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hE.le _) (Real.rpow_nonneg hE.le _)
  have heρ : ocEpsilon q Λ m ≤ Real.sqrt (B * ocTauPP α q Λ m) := by
    have hℓ2 : ocEll q Λ m ν ^ 2 = ocEpsilon q Λ m ^ 2 / ν := by
      unfold ocEll
      rw [div_pow, Real.sq_sqrt hνpos.le]
    have h1 := cov.ellT
    have hτ0 : 0 ≤ ocTauPP α q Λ m := le_trans (sq_nonneg _) h1
    rw [hℓ2, div_le_iff₀ hνpos] at h1
    have h2 : ocEpsilon q Λ m ^ 2 ≤ B * ocTauPP α q Λ m := by
      calc ocEpsilon q Λ m ^ 2 ≤ ocTauPP α q Λ m * ν := h1
        _ ≤ ocTauPP α q Λ m * B := mul_le_mul_of_nonneg_left hL.ν_le hτ0
        _ = B * ocTauPP α q Λ m := mul_comm _ _
    exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
  -- the edge matrix of the envelope
  have hbnn : ∀ v u, 0 ≤ Real.sqrt (π u / π v) * A v u := henv.nonneg
  have hAnn : ∀ v u, 0 ≤ A v u := fun v u =>
    (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v)))).1 (hbnn v u)
  have hCthΘ : Cth * Θ ≤ Sb := by
    rw [hSbd]
    rcases le_total 0 Cth with h0 | h0
    · exact (mul_le_of_le_one_right h0 hΘ₁).trans (le_max_left _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg h0 hΘ₀).trans (le_max_right _ _)
  have hrowS : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ Sb := fun v =>
    (henv.row_sum v).trans hCthΘ
  have hcolS : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ Sb := fun u =>
    (henv.col_sum u).trans hCthΘ
  -- the lift settings of the observed pulses
  choose! par V hset using fun k (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) =>
    hG6' H D Nc Klift Llift Llift (Klift + 4 * (H + 1) * (Nc + D) ^ 2)
      (max Llift (Llift + 2) + H * D + 2 * Nc + 2 * D) Ks Ls qJ Kmax hD hNc rfl rfl hKs
      (by rw [max_eq_right (by omega)]; exact hLs) hqJ π hπ Φ M' κ hband m hm2 hmM ν B hν hB
      hφ tp Tobs (ocRhoMol α q Λ m cMol ν) g a B₀ lam Cb l₀ P y₀ cov F actual hdepth hmeas
      (fun v u => Real.sqrt (π u / π v) * A v u) Sb hbnn hrowS hcolS hpointwiseAn htrans hquiet
      pp k hk (hpp k hk).2.2
  choose! parP VP hsetP using fun k (hk : k ∈ ocObsPulses α q Λ m tp (tp + Tobs)) =>
    hG6' H D Nc (Ac + 2 + Kmax + D * (H + 1) * Nc) (2 + Kmax + D * (H + 1) * Nc)
      (0 + Kmax + D * (H + 1) * Nc)
      ((Ac + 2 + Kmax + D * (H + 1) * Nc) + 4 * (H + 1) * (Nc + D) ^ 2)
      (max (2 + Kmax + D * (H + 1) * Nc) (0 + Kmax + D * (H + 1) * Nc + 2) + H * D + 2 * Nc +
        2 * D) Ks Ls qJ Kmax hD hNc rfl rfl (by omega)
      (by rw [max_eq_left (by omega)]; omega) (by omega) π hπ Φ M' κ hband m hm2 hmM ν B hν hB
      hφ tp Tobs (ocRhoMol α q Λ m cMol ν) g a B₀ lam Cb l₀ P y₀ cov F actual hdepth hmeas
      (fun v u => Real.sqrt (π u / π v) * A v u) Sb hbnn hrowS hcolS hpointwiseAn htrans hquiet
      pp k hk (hpp k hk).2.2
  -- the reconstruction window and its orders
  have o := reconOrders_of_reserves hD hAc hNc hN hK1 hL1
  have w : ReconWindow α s q Λ ζ Φ m hφ ν B tp Tobs (ocRhoMol α q Λ m cMol ν) F actual K T pp π
      Cpart H Nc Klift Llift (Klift + 4 * (H + 1) * (Nc + D) ^ 2)
      (max Llift (Llift + 2) + H * D + 2 * Nc + 2 * D) Cc par V CGl Cw Ca
      (fun v u => Real.sqrt (π u / π v) * A v u) Sb aC B₀C lamC pc Jc
      (compReserveK Ac Nc D H Kmax) AD CE Aedge Cstar Θc
      (fun v => truncateTorusHk (le_trans hN (le_max_left Mout (K v)))
        (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))
      W Fc aRep (compReserveK Ac Nc D H Kmax + (Nc + D) - 1) :=
    { hα₀ := hα₀, hα₁ := hα₁, hs₀ := hs₀, hs₁ := hs₁, hq := hq, hζ := hζ, hΛ := h128,
      hΦ := hΦ, hm := hm2, hν := hνpos, hB := hBpos, hTobs := hTobs₀, hρs := hρm,
      hρs_e := cov.rho_e, hρs_R := cov.rho_R, hRE := cov.RE, hdesc := hdesc, htorus := htorus,
      hTcons := hTcons, hTcov := hTcov, hTq := hTq, hTact := hTact, hpp := hpp,
      hppinj := hppinj, hpart := hpart, hquiet := hquiet, hsetting := hset,
      hseq := fun k hk => isLiftSequence_mono (hseq k hk) le_rfl (max_le (by omega) le_rfl),
      hcs := hcs, hcd := hdef, hrep := hrep, hr₀ := (by omega), hDr := (by omega),
      hmean := fun r hr => hmean r (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)) }
  -- the coarse energies
  choose a' lam' ha' hlam' hscale' hsmall' hsmallE hjets' _hd1 _hd2 _hd3 _hd4 _hd5 using
    hdrift Λ hΛ2 Φ hΦ M' κ hband m hm2 hmM ν B hν hB
  have hEbb := hcoarse tp (tp + Tobs) (Real.sqrt (B * ocTauPP α q Λ m)) B aC B₀C lamC a' lam'
    (ocEpsilon q Λ (m - 1)) (ocDelta α q) (streamVel (Φ (m - 1))) ((Nc + D) + 8 * pc + 4)
    (compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4))
    (ocRefFlux α q Λ ζ m ν) AD CE π Aedge hcs ha' hlam' hjets' hscale' hsmall' hsmallE
    (hflux Λ hΛ3 M' κ hband m hm2 hmM ν B hν hB tp (tp + Tobs)).2.2.2.2
    (hoff Λ hΛ4 M' κ hband m hm2 hmM ν B hν hB tp (tp + Tobs)) hADsum hE hE1 hδ _ U Uw G hresp W
    Fc hwit
  -- the joint model
  have hjmb := jointModel_massNormSq_le_cj π hπ K Mout H F A hAnn Θ (ocEpsilon q Λ (m - 1)) Pacc
    cj (Real.sqrt (B * ocTauPP α q Λ m)) Cj CPj Pd Pg hjm hrowS hcolS hSb hρ hcj hN
    (fun v => le_trans hN (le_max_left Mout (K v))) f Fv hf
  -- the bill
  have hbt := compBill_ge_terms α q Λ m ν B Tobs (cpt / 2)
    (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc he.le hE.le
  have habs := card_exp_absorb (N := ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ))
    (Nat.cast_nonneg _) hℓ.le hτ (hcard m ν B hL tp Tobs hTobs₀ hTobs)
  have hadm : IsAdmissibleStream (Φ m) := by
    have := (hΦ.2 (m + 1) (by omega)).fst
    simpa using this
  have hedge := edgeCoefficient_bound_of_sampled F π hπ K actual hνpos hρm
    (Assembly.isSampledEnvelope_mono hbnn (le_max_left Cfw 0) hfwd)
    (fun v u => mul_nonneg (le_max_right _ _) (hbnn v u))
  have hVb : ∀ t ∈ Set.Ioc tp (tp + Tobs), ∀ x k,
      |streamVel (Φ m) t x k| ≤ AVRegularity.Applications.velBound α q Λ := by
    intro t _ x k
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (streamVel (Φ m) t x) k).trans
      (AVRegularity.Applications.streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ m
        t x)
  have hXp : 0 ≤ Cpt * (1 + Sb) ^ H * ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
      ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
      Real.exp (-(cpt * ocTau α q Λ m / ocEll q Λ m ν ^ 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCpt
      (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)) hℓ.le) (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  -- the physical reconstruction on the window
  exact w.physical_lift (rs := ocRhoMol α q Λ m cMol ν) (ord := 4 * (Nc + D) + 2 * Ac + 16 + Kmax)
    (M := Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2))
    (bill := compBill α q Λ m ν B Tobs (cpt / 2) (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc
      Jc pc) (Cs := Cs) (Cy := Cy) (Cpx := Cpt * (1 + Sb) ^ H * Real.sqrt Kcard) o hK hSb hCg
    (fun k hk hh hhH n hn hnN m'' hm1 hmn j hj => (hgrad _ π _ _ _ _ _ _ _ _ _ _ _ (par k) (V k)
      _ _ _ _ (hset k hk) (Cc k) (w.hseq k hk) hh hhH n hn hnN m'' hm1 hmn j
      (by have := o.hK; omega)).1)
    hρm cov.rho_e cov.rho_R
    (fun v => coarseWitness_W_continuousOn hresp hwit
      (IsCoarseSetting.J_intervalIntegrable hcs (by omega)) (by omega) v)
    (fun n r' => coarseFc_modeCoeff_measurable hcs hresp hwit n r')
    (fun v => coarseFc_aestronglyMeasurable hcs hresp hwit v)
    (fun t _ k => ((continuous_apply k).comp (hadm.vel_continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    hVb
    hedge.choose_spec.1 hedge.choose_spec.2
    (fun t ht v u d => (edgeCoefficient_continuous_of_sampled F π K actual hfwd v u d
      ht).aestronglyMeasurable)
    (by exact mul_nonneg (mul_nonneg hCcb hsig) (Real.sqrt_nonneg _))
    (by exact mul_nonneg (mul_nonneg hCcb (Real.sqrt_nonneg _)) (mul_nonneg hbr htt))
    (Real.sqrt_nonneg _) htt hCs hCy hCpx (by omega) hXp
    (hpartb w parP VP _ _ hsetP hK1b hL1 hSb heρ _ hρm cov.rho_e)
    ((strongEnergyUpTo_mono_order (by omega) _ _ _ _ _ W).trans hEbb.1)
    ((strongEnergyUpTo_mono_order (by omega) _ _ _ _ _ W).trans hEbb.1) hEbb.2
    (by
      rw [hCsd]
      exact (mul_le_mul_of_nonneg_left hjmb (mul_nonneg hCcb hsig)).trans (le_of_eq (by ring)))
    (by
      rw [hCyd]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjmb hCcb)
        (mul_nonneg hbr htt)).trans (le_of_eq (by ring)))
    (by
      have hc0 : 0 ≤ Cpt * (1 + Sb) ^ H := mul_nonneg hCpt (pow_nonneg (by linarith) _)
      calc _ = Cpt * (1 + Sb) ^ H * (((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) *
              ocEll q Λ m ν * Real.sqrt (1 / ocTau α q Λ m) *
              Real.exp (-(cpt * ocTau α q Λ m / ocEll q Λ m ν ^ 2))) := by ring
        _ ≤ Cpt * (1 + Sb) ^ H * (Real.sqrt Kcard * (ocEll q Λ m ν *
              Real.sqrt (((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) / ocTau α q Λ m) *
              Real.exp (-(cpt / 2 * ocTau α q Λ m / ocEll q Λ m ν ^ 2)))) :=
            mul_le_mul_of_nonneg_left habs hc0
        _ ≤ Cpt * (1 + Sb) ^ H * (Real.sqrt Kcard *
              compBill α q Λ m ν B Tobs (cpt / 2) (ocObsPulses α q Λ m tp (tp + Tobs)).card
                Ac Nc Jc pc) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbt.2.2.2.2.2
              (Real.sqrt_nonneg _)) hc0
        _ = _ := by ring)
    hbt.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.1 hbt.2.2.2.2.1 (fun v => max Mout (K v))
    (fun v => jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)
    (fun v => le_trans hN (le_max_left Mout (K v))) (fun v => le_max_right Mout (K v))
    (fun _ => rfl)

end AVRegularity.CycleComparison.Reconstruction
