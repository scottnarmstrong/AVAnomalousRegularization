-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
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
public import AVRegularity.Statements.Intermediate.CycleOutput.ObsErrorNorm
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
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.Families.TorusCompatible.WeakStage

section
/-! **Assembly of `cycle_comparison` from the reconstruction statement**. The statement
follows from `cycle_comparison_reconstruction`
(clause 6 (e)–(h): the physical reconstruction, its residual and the error), whose statement
is the hypothesis `hG4` verbatim (the universe variables of the two statements are shared).
All other ingredients are proved:
* clauses 1–3: `oc_means` (the lift settings with the edge majorant masked by the family's
  edges, `cycle_lift_exists`, the letters, the actual means, the means bound);
* clause 4: `oc_diagonal` (the per-pulse comparison with the reference flux, the chart
  deviation, the higher orders, the switching price);
* clause 5: `bill_bound`;
* clause 6 (a)–(d): `IsCoarseSetting` (`coarse_drift_fields`, `coarse_flux_fields`, the
  letter fields, the masked majorant), `cycle_coarse_exists`, `cycle_coarse_defect`, and the
  classical representatives `torusHk_classicalRep_exists_vec`.
The proof of `cycle_comparison` from the reconstruction statement is
`cycle_comparison_of_ingredients`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleComparison.Assembly

open AVRegularity.CycleComparison.ActualMeans

/-- The bill is nonnegative. -/
theorem compBill_nonneg (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {ν : ℝ} (hν : 0 < ν)
    (B Tobs cb : ℝ) (Bp Ac Nc Jc pc : ℕ) :
    0 ≤ compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc := by
  have hℓ : 0 < ocEll q Λ m ν := by
    unfold ocEll
    exact div_pos (Construction.Stream.ocEpsilon_pos hΛ) (Real.sqrt_pos.2 hν)
  have hd : 0 ≤ ocDStar q Λ m ν B := by
    rw [LiftSetting.dstar_eq q Λ m hν.le B]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg _)
  have hεc : 0 ≤ ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) :=
    div_nonneg hd (Real.sqrt_nonneg _)
  have he : 0 ≤ ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) :=
    div_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _)
  have hE : 0 ≤ ocEpsilon q Λ (m - 1) := (Construction.Stream.ocEpsilon_pos hΛ).le
  have hZ : 0 ≤ 1 + Real.sqrt Tobs / ocEll q Λ m ν *
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) ^ Ac :=
    add_nonneg zero_le_one (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hℓ.le) (pow_nonneg he _))
  unfold compBill
  exact add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hεc _) hZ)
    (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hεc _) hZ))
      (add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _))))
    (mul_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le)

/-- If `a (X + Y)` is bounded by a real number and `a ≠ 0`, then `Y` is finite. -/
theorem ne_top_of_mul_add_le {a X Y : ℝ≥0∞} {c : ℝ} (ha : a ≠ 0)
    (h : a * (X + Y) ≤ ENNReal.ofReal c) : Y ≠ ⊤ := by
  intro hY
  rw [hY, add_top, ENNReal.mul_top ha] at h
  exact ENNReal.ofReal_ne_top (top_le_iff.1 h)

/-- The terms of a finite sum of seminorms over finite positive weights are finite. -/
theorem ne_top_of_sum_inv_ne_top {N' : ℕ} (x : Finset.Icc 2 N' → ℝ≥0∞)
    (S : Finset.Icc 2 N' → ℝ) (h : ∑ d, x d * (ENNReal.ofReal (S d))⁻¹ ≠ ⊤)
    (d : Finset.Icc 2 N') : x d ≠ ⊤ := by
  intro hx
  apply h
  rw [ENNReal.sum_eq_top]
  exact ⟨d, Finset.mem_univ d, by
    rw [hx, ENNReal.top_mul (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)]⟩

/-- The statement of the `cycle_comparison_reconstruction`, verbatim (with named
universes). -/
def ReconstructionStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
      (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
      (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
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
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
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
                      Ac Nc Jc pc) * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2))

/-- The statement of `cycle_comparison` with the premise `hquiet` on the times
`Qs α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)`: for `Qs = ocTrimmedQuietTimes` the statement of
`cycle_comparison` (with named universes), for `Qs = ocQuietTimes` the statement with fast
independence on all quiet times. -/
def ComparisonStatementOn (Qs : ℝ → ℝ → ℕ → (ℝ → ℝ) → ℕ → Set ℝ) : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
      (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
      (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (H D Kmax : ℕ), 2 ≤ D → ∀ (Aobs Cobs : ℝ),
      ∃ (Ac Nc Jc pc Mout : ℕ) (_ : Mout = compReserveMout Ac Nc Jc pc D H Kmax)
        (hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Mout)
        (Ks Ls Jm qJ Klift Llift : ℕ),
        max (Mout + Ac + Kmax + 2) (Ac + 2 + Kmax + D * (H + 1) * Nc) ≤ Klift ∧
        Kmax + D * (H + 1) * Nc ≤ Llift ∧
      ∀ (Ca Cfw Cth Cb cMol Cj CPj cj Cpart : ℝ) (Cm CG : ℕ → ℝ), 0 < cMol → 0 < cj →
      ∃ (C CP cb : ℝ) (CK : ℕ → ℝ) (mStar : ℕ), 0 < cb ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
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
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
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
        (_hquiet : F.IsFastIndependentOn (Qs α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
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
          (gluedMean (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2)
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
                    Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2))

/-- The statement of `cycle_comparison` verbatim (with named universes): the premise `hquiet` is
fast independence on the trimmed quiet times
`ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)`. -/
def ComparisonStatement : Prop :=
  ComparisonStatementOn.{u, v, w, x} ocTrimmedQuietTimes

/-- **`cycle_comparison` from the reconstruction statement**, with `hquiet` on any times containing
the trimmed quiet times: `cycle_comparison` for `ocTrimmedQuietTimes`, the statement on all quiet
times for `ocQuietTimes`. -/
theorem cycle_comparison_of_ingredients (hG4 : ReconstructionStatement.{u, v, w, x})
    (Qs : ℝ → ℝ → ℕ → (ℝ → ℝ) → ℕ → Set ℝ)
    (hQs : ∀ α q Λ ζ m, 1 ≤ Λ → ocTrimmedQuietTimes α q Λ ζ m ⊆ Qs α q Λ ζ m) :
    ComparisonStatementOn.{u, v, w, x} Qs := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  classical
  choose ΛM hΛM hOM using oc_means α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose ΛD hΛD hOD using oc_diagonal α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose ΛB hΛB hBill using bill_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose ΛG hΛG hG using hG4 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose ΛR B₀c hΛR hB₀c hDrift using coarse_drift_fields α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose ΛF hΛF hFlux using coarse_flux_fields α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max ΛM (max ΛD (max ΛB (max ΛG (max ΛR ΛF)))), hΛM.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  have hΛM' : ΛM ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛD' : ΛD ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛB' : ΛB ≤ Λ :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  have hΛG' : ΛG ≤ Λ := ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  have hΛR' : ΛR ≤ Λ := (((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  have hΛF' : ΛF ≤ Λ := (((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hΛ
  have hΛ128 : 128 ≤ Λ := hΛM.trans hΛM'
  have hΛ1 : 1 ≤ Λ := by omega
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro Pacc hPacc H D Kmax hD Aobs Cobs
  choose Ac₀ Nc₀ Jc pc₀ hthr using hBill Λ hΛB' Pacc hPacc Aobs Cobs
  choose Ac hAc1 hAcge using (⟨max Ac₀ 1, le_max_right _ _, le_max_left _ _⟩ :
    ∃ n : ℕ, 1 ≤ n ∧ Ac₀ ≤ n)
  choose Nc hNc1 hNcge using (⟨max Nc₀ 1, le_max_right _ _, le_max_left _ _⟩ :
    ∃ n : ℕ, 1 ≤ n ∧ Nc₀ ≤ n)
  choose pc hpc1 hpcge using (⟨max pc₀ 1, le_max_right _ _, le_max_left _ _⟩ :
    ∃ n : ℕ, 1 ≤ n ∧ pc₀ ≤ n)
  have hN : compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤
      compReserveMout Ac Nc Jc pc D H Kmax := by
    unfold compReserveMout
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  choose Klift hK1 hK2 using (⟨max (compReserveMout Ac Nc Jc pc D H Kmax + Ac + Kmax + 2)
      (Ac + 2 + Kmax + D * (H + 1) * Nc), le_max_left _ _, le_max_right _ _⟩ :
    ∃ n : ℕ, compReserveMout Ac Nc Jc pc D H Kmax + Ac + Kmax + 2 ≤ n ∧
      Ac + 2 + Kmax + D * (H + 1) * Nc ≤ n)
  choose Llift hL1 using (⟨Kmax + D * (H + 1) * Nc + 1, le_rfl⟩ :
    ∃ n : ℕ, Kmax + D * (H + 1) * Nc + 1 ≤ n)
  refine ⟨Ac, Nc, Jc, pc, compReserveMout Ac Nc Jc pc D H Kmax, rfl, hN,
    Klift + 4 * (H + 1) * (Nc + D) ^ 2, Llift + 2 + H * D + 2 * Nc + 2 * D, 0,
    Klift + 4 * (H + 1) * (Nc + D) ^ 2, Klift, Llift, max_le hK1 hK2,
    Nat.le_of_succ_le hL1, ?_⟩
  let Nbig : ℕ := compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4)
  have hNbigK : Nbig ≤ Klift := by
    show compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 4) ≤ Klift
    omega
  intro Ca Cfw Cth Cb cMol Cj CPj cj Cpart Cm CG hcMol hcj
  choose CGl Cw C₂ C₁ Ct hC₂ _hC₁ hCt hM using hOM Λ hΛM' (1 / 4) Ca CG (by norm_num) H D
    Nc Klift Llift (Klift + 4 * (H + 1) * (Nc + D) ^ 2) (Llift + 2 + H * D + 2 * Nc + 2 * D)
    (Klift + 4 * (H + 1) * (Nc + D) ^ 2) Kmax hD hNc1 le_rfl le_rfl le_rfl
  choose C4 _hC4 hDg using hOD Λ hΛD' CGl Cw Ca C₂ H D Nc Klift Llift hD hC₂
  choose Cstar hCstar using (⟨_, rfl⟩ : ∃ x : ℝ, x = max 1
    (2 * ((Nc + D : ℕ) : ℝ) ^ 2 * ((Nbig : ℝ) + 1) * (Ct * C₂)))
  choose Θc hΘc using (⟨_, rfl⟩ : ∃ x : ℝ, x = max Cth 0)
  choose CG4 CP4 cb mStar hcb hR using hG Λ hΛG' (1 / 4) (by norm_num) le_rfl Pacc hPacc H
    D Kmax hD Aobs Cobs Ac Nc Jc pc (compReserveMout Ac Nc Jc pc D H Kmax) rfl hN
    (Klift + 4 * (H + 1) * (Nc + D) ^ 2)
    (Llift + 2 + H * D + 2 * Nc + 2 * D) 0 (Klift + 4 * (H + 1) * (Nc + D) ^ 2) Klift Llift
    (max_le hK1 hK2) hL1 hAc1 hNc1 hpc1 le_rfl le_rfl le_rfl Ca Cfw Cth Cb cMol Cj CPj cj Cpart Cm
    CG hcMol hcj C4 Cstar Θc
  choose Cbill _hCbill hbillC using hthr Ac Nc Jc pc hAcge hNcge le_rfl hpcge cb hcb
  refine ⟨max C4 (max Cbill CG4), max CP4 0 * (1 + Cbill), cb,
    fun K' => 2 * ((Nc + D : ℕ) : ℝ) ^ 2 * ((K' : ℝ) + 1) * (Ct * C₂), mStar, hcb, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ tS tp Tobs
    htS hTobs₀ hTobs htpq g a B₀ lam l₀ P y₀ cov P' Ctx F actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ henv hpointwiseMol hpointwiseAn hfwd htrans hquiet T hTcons hTcov hTq hTact pp
    hpp hppinj hpart a₂ B₂ lam₂ ha₂ hB₂ hlam₂ hjets hB₂ρ hab ρold Pd Pg hjm hje
  replace hquiet : F.IsFastIndependentOn
      (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)) :=
    isFastIndependentOn_mono F (Set.inter_subset_inter_left _ (hQs α q Λ ζ m hΛ1)) hquiet
  -- scales
  have hνpos : 0 < ν := LiftSetting.ν_pos cov
  have hBpos : 0 < B := LiftSetting.B_pos cov
  have hρ : 0 < Real.sqrt (B * ocTauPP α q Λ m) := LiftSetting.ρ_pos α q hΛ1 m hBpos
  have hE : 0 < ocEpsilon q Λ (m - 1) := LiftSetting.E_pos q hΛ1 m
  have hA : ∀ v u, 0 ≤ A v u := fun v u =>
    nonneg_of_mul_nonneg_right (henv.nonneg v u) (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v)))
  have hS : Cth * Θ ≤ Θc := by
    rcases le_total 0 Cth with hC | hC
    · calc Cth * Θ ≤ Cth * 1 := mul_le_mul_of_nonneg_left hΘ₁ hC
        _ = Cth := mul_one _
        _ ≤ Θc := hΘc ▸ le_max_left _ _
    · calc Cth * Θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hΘ₀
        _ ≤ Θc := hΘc ▸ le_max_right _ _
  -- clauses 1 to 3
  have hout : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
      ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output :=
    fun k hk => (hpp k hk).2.2
  choose Cc Lb Lsc hset hCc hLb _hsc0 hscC hscR hAM hC3 using hM π hπ Φ hΦ M' κ hband m hm2
    hmM ν B hν hB hφ tp Tobs (ocRhoMol α q Λ m cMol ν) g a B₀ lam Cb l₀ P y₀ cov F actual hdepth
    htorus hmeas A (Cth * Θ) henv.nonneg henv.row_sum henv.col_sum hpointwiseAn htrans hquiet pp
    hout Cpart hpart
  choose! par V hset' using hset
  -- clause 4
  have hD4 := hDg π Φ hΦ M' κ hband m hm2 hmM ν B hν hB hφ tp Tobs (ocRhoMol α q Λ m cMol ν) g a
    B₀ lam Cb (1 / 4) (Klift + 4 * (H + 1) * (Nc + D) ^ 2) Kmax CG l₀ P y₀ cov htpq F actual pp
    (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) (Cth * Θ)
    (Klift + 4 * (H + 1) * (Nc + D) ^ 2) (max 0 (Llift + 2) + H * D + 2 * Nc + 2 * D) par V
    hset' Cc Lb Lsc hCc hLb hscR hscC Cpart hpart _ hNbigK
  -- the letters
  generalize adLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
    (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lsc (ocRefFlux α q Λ ζ m ν) = AD
    at hAM hD4
  generalize ceLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
    (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lb = CE at hAM hC3
  have hcl2 := hAM.1
  -- the masked majorant
  have hAedge_conj : (Matrix.of fun v' u' => Real.sqrt (π u' / π v') *
      Coarse.maskedEdgeMatrix (familyAdj F) A v' u') =
      Matrix.of (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) := by
    ext v u
    rw [Matrix.of_apply, Matrix.of_apply, familyMask_eq_conj F π A v u]
  -- the coarse setting
  choose ac lamc hac0 hlamc hscale hsmall hdj hdsm hddiv hdper hdbdd hdmeas using
    hDrift Λ hΛR' Φ hΦ M' κ hband m hm2 hmM ν B hν hB
  have hFl := hFlux Λ hΛF' M' κ hband m hm2 hmM ν B hν hB tp
    (tp + Tobs)
  have hKt : ((Nbig : ℕ) : WithTop ℕ∞) ≤ (((Klift + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : Nbig ≤ Klift + 1)
  have hCEfin : ∀ r ∈ Finset.Icc 1 H, ∀ v u (d : Finset.Icc 2 (Nc + D)),
      coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m)) Nbig tp (tp + Tobs)
        (CE r v u d) ≠ ⊤ := by
    intro r hr v u d
    have hr' := Finset.mem_Icc.1 hr
    have h3 := hC3 r hr'.1 hr'.2 Nbig (by omega) v u
    refine ne_top_of_sum_inv_ne_top _ _ (ne_top_of_mul_add_le ?_ h3) d
    exact (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v)))).ne'
  have hCS : IsCoarseSetting tp (tp + Tobs) (Real.sqrt (B * ocTauPP α q Λ m)) B ac B₀c lamc
      (streamVel (Φ (m - 1))) (Nc + D) H pc Jc (compReserveK Ac Nc D H Kmax)
      ((Nc + D) + 8 * pc + 4) Nbig (ocRefFlux α q Λ ζ m ν) AD CE π
      (Matrix.of (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u))) Cstar Θc :=
    { window := by linarith
      rho_pos := hρ
      B_pos := hBpos
      D_ge := by omega
      p_pos := hpc1
      L_eq := rfl
      N_eq := rfl
      mass_pos := hπ
      drift_bdd := hdbdd tp (tp + Tobs)
      drift_meas := hdmeas tp (tp + Tobs)
      drift_smooth := fun t _ => hdsm t
      drift_div := fun t _ x => hddiv t x
      drift_per := fun t _ => hdper t
      a_nonneg := hac0
      B₀_ge := hB₀c
      lam_pos := hlamc
      drift_jets := fun l hl _ t _ x => hdj l hl t x
      drift_scale := hscale
      drift_small := hsmall
      J_symm := hFl.1
      J_meas := hFl.2.1
      J_bdd := hFl.2.2.1
      cov_small := hFl.2.2.2
      AD_meas := hAM.2.2.2.1
      AD_smooth := fun d t ht => (hAM.2.2.1 d t ht).of_le hKt
      AD_per := hAM.2.2.2.2.1
      AD_fin := fun d => ne_top_of_sum_inv_le _ _ hD4 d
      CE_meas := hAM.2.2.2.2.2.2.1
      CE_smooth := fun r hr v u d t ht => (hAM.2.2.2.2.2.1 r hr v u d t ht).of_le hKt
      CE_per := hAM.2.2.2.2.2.2.2.1
      CE_fin := hCEfin
      edge_nonneg := fun v u => familyMask_nonneg F henv.nonneg v u
      edge_row := fun v => (familyMask_row_le F henv.nonneg henv.row_sum v).trans hS
      edge_col := fun u => (familyMask_col_le F henv.nonneg henv.col_sum u).trans hS
      edge_acyclic := familyMask_pow_eq_zero F hdepth _
      edge_mean := by
        intro r hr v u
        have hr' := Finset.mem_Icc.1 hr
        have h3 := hC3 r hr'.1 hr'.2 Nbig (by omega) v u
        have h := edge_mean_of_bound hπ
          (Coarse.maskedEdgeMatrix_nonneg (familyAdj F) A hA) (le_of_eq hCstar.symm) hr'.1 h3
        rw [hAedge_conj] at h
        exact h }
  refine ⟨Cc, AD, CE, hCc, hcl2, ?_, ?_, ?_, ?_⟩
  · -- clause 3
    intro r hr1 hrH K' hK' v u
    refine (hC3 r hr1 hrH K' (hK'.trans (by omega)) v u).trans (ENNReal.ofReal_le_ofReal ?_)
    have hK0 : 0 ≤ 2 * ((Nc + D : ℕ) : ℝ) ^ 2 * ((K' : ℝ) + 1) * (Ct * C₂) :=
      mul_nonneg (by positivity) (mul_nonneg hCt hC₂)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (maskedEdgeMatrix_pow_le (familyAdj F) hA r v u) (Real.sqrt_nonneg _)) hK0
  · -- clause 4
    refine hD4.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hE.le _)
  · -- clause 5
    refine (hbillC M' κ hband m hm2 hmM ν B hν hB tp Tobs hTobs₀ hTobs).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
      (Real.rpow_nonneg hE.le _)
  · -- clause 6
    intro f Fv hF
    choose Cce _hCce hce using Providers.cycle_coarse_exists (Nc + D) H pc Jc
      (compReserveK Ac Nc D H Kmax)
    choose Ccd _hCcd hcd using Providers.cycle_coarse_defect (Nc + D) H pc Jc
      (compReserveK Ac Nc D H Kmax)
    have hCstar0 : 0 ≤ Cstar := hCstar ▸ zero_le_one.trans (le_max_left _ _)
    have hΘc0 : 0 ≤ Θc := hΘc ▸ le_max_right _ _
    choose U Uw G hU using hce B₀c Cstar Θc hB₀c hCstar0 hΘc0 tp (tp + Tobs)
      (Real.sqrt (B * ocTauPP α q Λ m)) B ac lamc (streamVel (Φ (m - 1)))
      ((Nc + D) + 8 * pc + 4) _ (ocRefFlux α q Λ ζ m ν) AD CE π _ hCS
      (fun v => truncateTorusHk
        (le_trans hN (le_max_left (compReserveMout Ac Nc Jc pc D H Kmax) (K v)))
        (jointOperator K (compReserveMout Ac Nc Jc pc D H Kmax) H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))
    choose W Fc hWit hDef using hcd B₀c Cstar Θc hB₀c hCstar0 hΘc0 tp (tp + Tobs)
      (Real.sqrt (B * ocTauPP α q Λ m)) B ac lamc (streamVel (Φ (m - 1)))
      ((Nc + D) + 8 * pc + 4) _ (ocRefFlux α q Λ ζ m ν) AD CE π _ hCS
      (fun v => truncateTorusHk
        (le_trans hN (le_max_left (compReserveMout Ac Nc Jc pc D H Kmax) (K v)))
        (jointOperator K (compReserveMout Ac Nc Jc pc D H Kmax) H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))
      U Uw G hU
    have hrepex : ∀ (t : ℝ) (v : ι), ∃ a' : Vec 2 → h v,
        IsClassicalRep (W v t) a' (compReserveK Ac Nc D H Kmax + (Nc + D) - 1) :=
      fun t v => torusHk_classicalRep_exists_vec _ _ (by omega) (W v t)
    choose aR haR using hrepex
    choose û ŵ Rres qres he hf hg hh using hR π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM
      ν B hν hB hφ tS tp Tobs htS hTobs₀ hTobs htpq g a B₀ lam l₀ P y₀ cov F actual hdepth hdesc
      htorus hcover hmeas A Θ hΘ₀ hΘ₁ henv hpointwiseMol hpointwiseAn hfwd htrans hquiet T hTcons
      hTcov hTq hTact pp hpp hppinj hpart a₂ B₂ lam₂ ha₂ hB₂ hlam₂ hjets hB₂ρ hab ρold Pd Pg hjm
      hje Cc AD CE hCc hcl2 hD4 ac B₀c lamc _ hCS f Fv hF U Uw G W Fc
      (fun t x v => aR t v x) hU hWit hDef (fun t _ v => haR t v)
    have hbill0 := compBill_nonneg α q hΛ1 m hνpos B Tobs cb
      (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc
    have hF0 : 0 ≤ Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) := Real.sqrt_nonneg _
    refine ⟨U, Uw, G, W, Fc, fun t x v => aR t v x, û, ŵ, Rres, qres, hU, hWit, hDef,
      fun t _ v => haR t v, he, hf, ?_, ?_⟩
    · refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) hbill0) hF0
    · intro u w hu
      refine (hh u w hu).trans (ENNReal.ofReal_le_ofReal ?_)
      have hbillE := hbillC M' κ hband m hm2 hmM ν B hν hB tp Tobs hTobs₀ hTobs
      have hEP : 0 ≤ ocEpsilon q Λ (m - 1) ^ Pacc := Real.rpow_nonneg hE.le _
      have hsum0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ Pacc +
          compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc :=
        add_nonneg hEP hbill0
      calc CP4 * (ocEpsilon q Λ (m - 1) ^ Pacc +
            compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc) *
            Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)
          ≤ max CP4 0 * (ocEpsilon q Λ (m - 1) ^ Pacc +
            Cbill * ocEpsilon q Λ (m - 1) ^ Pacc) * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _)
              (add_le_add le_rfl hbillE) hsum0 (le_max_right _ _)) hF0
        _ = max CP4 0 * (1 + Cbill) * ocEpsilon q Λ (m - 1) ^ Pacc *
            Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) := by ring

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! **The reconstruction from the physical lift**.
The `cycle_comparison_reconstruction` (clause 6 (e)–(h) of `cycle_comparison`) follows from
`cycle_comparison_physical_lift` (the reconstruction: clauses (e)–(g), the start `û(t_p) = 𝑷f` and
the residual bounds in every slot `K_v`), whose statement is the hypothesis `hG5` verbatim.
Clause (h), the physical energy error, is proved here: on the observation window the error
`u - û` solves the actual system forced by the residual from `u(t_p) - 𝑷f`
(`Error.isCoupledWeakSolutionTorus_restrict_right`, `Error.isCoupledWeakSolutionTorus_sub`); the
joint error `IsJointError` bounds the start, the residual bounds of the physical
lift the forcing, and `Error.comparison_error_bound` (the coupled energy estimate at rank-rescaled masses with the
forward envelope) gives the error norm. The actual edge coefficient is jointly measurable on the
window because only the observed pulses carry weight there
(`Error.weight_eq_zero_of_not_mem`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleComparison.Assembly

/-- An envelope with a larger constant (the matrix is nonnegative). -/
theorem isSampledEnvelope_mono {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {actual : ∀ p, Ctx p}
    {t₀ t₁ ν e E ρ C C' : ℝ} {b : ι → ι → ℝ} (hb : ∀ v u, 0 ≤ b v u) (hC : C ≤ C')
    (hfwd : IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C b) :
    IsSampledEnvelope F π K actual t₀ t₁ ν e E ρ C' b :=
  ⟨hfwd.1, fun v u => (hfwd.2 v u).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (hb v u)))⟩

/-- The final real inequality of the error clause. -/
theorem error_constant_le (Q CPj C e β Fπ : ℝ) (hQ : 0 ≤ Q) (he : 0 ≤ e) (hβ : 0 ≤ β)
    (hF : 0 ≤ Fπ) :
    Q * (CPj * e * Fπ + 2 * (C * β * Fπ)) ≤
      Q * (max CPj 0 + 2 * max C 0) * (e + β) * Fπ := by
  have h1 : CPj * e * Fπ ≤ max CPj 0 * ((e + β) * Fπ) := by
    calc CPj * e * Fπ = CPj * (e * Fπ) := by ring
      _ ≤ max CPj 0 * (e * Fπ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg he hF)
      _ ≤ max CPj 0 * ((e + β) * Fπ) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) hF) (le_max_right _ _)
  have h2 : C * β * Fπ ≤ max C 0 * ((e + β) * Fπ) := by
    calc C * β * Fπ = C * (β * Fπ) := by ring
      _ ≤ max C 0 * (β * Fπ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hβ hF)
      _ ≤ max C 0 * ((e + β) * Fπ) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) hF) (le_max_right _ _)
  calc Q * (CPj * e * Fπ + 2 * (C * β * Fπ))
      ≤ Q * (max CPj 0 * ((e + β) * Fπ) + 2 * (max C 0 * ((e + β) * Fπ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hQ
    _ = Q * (max CPj 0 + 2 * max C 0) * (e + β) * Fπ := by ring

/-- The statement of the `cycle_comparison_physical_lift`, verbatim (with named
universes). -/
def PhysicalLiftStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
      (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
      (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
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
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
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
                  Ac Nc Jc pc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)

/-- **`cycle_comparison_reconstruction` from `cycle_comparison_physical_lift`.** -/
theorem reconstruction_of_physicalLift (hG5 : PhysicalLiftStatement.{u, v, w, x}) :
    ReconstructionStatement.{u, v, w, x} := by
  classical
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  choose Λ₅ hΛ₅ h5 using hG5 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₅, hΛ₅, ?_⟩
  intro Λ hΛ g₀ hg₀ hg₀' Pacc hPacc H D Kmax hD Aobs Cobs Ac Nc Jc pc Mout hMout hN Ks Ls Jm qJ
    Klift Llift hKl hLl hAc hNc hpc hKs hLs hqJ Ca Cfw Cth Cb cMol Cj CPj cj Cpart Cm CG hcMol hcj
    C4 Cstar Θc
  have hΛ128 : 128 ≤ Λ := hΛ₅.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  choose C cb mStar hcb h5' using h5 Λ hΛ g₀ hg₀ hg₀' Pacc hPacc H D Kmax hD Aobs Cobs Ac Nc Jc
    pc Mout hMout hN Ks Ls Jm qJ Klift Llift hKl hLl hAc hNc hpc hKs hLs hqJ Ca Cfw Cth Cb cMol
    Cj CPj cj Cpart Cm CG hcMol hcj C4 Cstar Θc
  refine ⟨C, 8 * (8 * (max Cfw 0 * max Cth 0) + 1) ^ H * (max CPj 0 + 2 * max C 0), cb, mStar,
    hcb, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ tS tp Tobs
    htS hTobs₀ hTobs htpq g a B₀ lam l₀ P y₀ cov P' Ctx F actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ henv hpointwiseMol hpointwiseAn hfwd htrans hquiet T hTcons hTcov hTq hTact pp
    hpp hppinj hpart a₂ B₂ lam₂ ha₂ hB₂ hlam₂ hjets hB₂ρ hab ρold Pd Pg hjm hje
    Cc AD CE hC1 hC2 hC4 a' B₀' lam' Aedge hcs f Fv hFv U Uw G W Fc aRep hresp hwit hdef hrep
  choose û ŵ R qr hcl using h5' π hπ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ tS tp
    Tobs htS hTobs₀ hTobs htpq g a B₀ lam l₀ P y₀ cov F actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ henv hpointwiseMol hpointwiseAn hfwd htrans hquiet T hTcons hTcov hTq hTact pp
    hpp hppinj hpart a₂ B₂ lam₂ ha₂ hB₂ hlam₂ hjets hB₂ρ hab ρold Pd Pg hjm hje
    Cc AD CE hC1 hC2 hC4 a' B₀' lam' Aedge hcs f Fv hFv U Uw G W Fc aRep hresp hwit hdef hrep
  refine ⟨û, ŵ, R, qr, hcl.1, hcl.2.1, hcl.2.2.1, ?_⟩
  intro u w hsol
  have hνpos : 0 < ν := LiftSetting.ν_pos cov
  have hE : 0 < ocEpsilon q Λ (m - 1) := LiftSetting.E_pos q hΛ1 m
  have hρs : 0 < ocRhoMol α q Λ m cMol ν := by
    unfold ocRhoMol ocA
    exact mul_pos hcMol (Real.sqrt_pos.2 (div_pos hνpos
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ1) _)))
  have htp : tp ≤ tp + Tobs := le_add_of_nonneg_right hTobs₀.le
  have hdr := Error.actual_drift_fields α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ m tp
    (tp + Tobs)
  have hwin : ∀ p : P', (∀ t ∈ Set.Icc tp (tp + Tobs), F.weight p t = 0) ∨
      (Continuous (F.weight p) ∧ ∃ l : ℤ, ∀ t, ⇑((F.piece p).material t) =
        ocChart α q Λ m (Φ (m - 1)) hφ l t) := by
    intro p
    by_cases hp : ∃ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), pp k = p
    · obtain ⟨k, hk, hkp⟩ := hp
      subst hkp
      exact Or.inr ⟨(hpart.2.1 k hk).continuous, ocPulseChartIndex α q Λ m k, (hpp k hk).2.1⟩
    · simp only [not_exists, not_and] at hp
      exact Or.inl (Error.weight_eq_zero_of_not_mem F _ pp hppinj (Set.Icc tp (tp + Tobs))
        ((Set.Icc_subset_Icc htS.le le_rfl).trans hcover) (fun t ht => hpart.2.2.1 t ht) p hp)
  have hS : Cth * Θ ≤ max Cth 0 := by
    rcases le_total 0 Cth with hC | hC
    · calc Cth * Θ ≤ Cth * 1 := mul_le_mul_of_nonneg_left hΘ₁ hC
        _ = Cth := mul_one _
        _ ≤ max Cth 0 := le_max_left _ _
    · calc Cth * Θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hΘ₀
        _ ≤ max Cth 0 := le_max_right _ _
  have hfwd' := isSampledEnvelope_mono (fun v u => henv.nonneg v u) (le_max_left Cfw 0) hfwd
  have hje' := hje f Fv hFv u w (Error.isCoupledWeakSolutionTorus_restrict_left htp hsol)
  have hb := Error.comparison_error_bound α q Λ m (Φ (m - 1)) hφ H Kmax hD (max Cfw 0)
    (max Cth 0) (le_max_right _ _) (le_max_right _ _) π hπ K hK ν hνpos (streamVel (Φ m)) tS tp
    (tp + Tobs) htS.le htp hdr.1 hdr.2.1 hdr.2.2.1 hdr.2.2.2.1 hdr.2.2.2.2 a₂ B₂ lam₂
    (ocRhoMol α q Λ m cMol ν) ha₂ hB₂ hlam₂ hρs hjets hB₂ρ hab F actual hdepth (ocEpsilon q Λ m)
    (ocEpsilon q Λ (m - 1)) (TorusCompatible.ocEpsilon_inv_natCast q Λ m) htorus (fun _ => Ks + Ls)
    hpointwiseAn.1 hmeas hwin A (fun v u => henv.nonneg v u)
    (fun v => (henv.row_sum v).trans hS) (fun u => (henv.col_sum u).trans hS) hfwd'
    (fun v => truncateTorusHk (le_max_right Mout (K v))
      (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))
    f u w hsol _ hje' û ŵ R qr hcl.2.1 hcl.2.2.2.1 hcl.2.2.2.2.1 hcl.2.2.2.2.2.1 _
    hcl.2.2.2.2.2.2.1 hcl.2.2.2.2.2.2.2
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact error_constant_le _ CPj C _ _ _
    (mul_nonneg (by norm_num) (pow_nonneg (by
      nlinarith [mul_nonneg (le_max_right Cfw 0) (le_max_right Cth 0)]) _))
    (Real.rpow_nonneg hE.le _)
    (compBill_nonneg α q hΛ1 m hνpos B Tobs cb _ Ac Nc Jc pc) (Real.sqrt_nonneg _)

end AVRegularity.CycleComparison.Assembly
end
end
