-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Proofs.Results.CycleJoint.PreparationChartSchedule
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Assembly

/-! Retained certificates supply the three analytic inputs of the full-lift assembly.
All scale thresholds and readout constants are selected before the data and fields. -/

open AVRegularity.Construction.Preservation.FullLift

private theorem retained_absorption_threshold {q τ : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hτ : 0 < τ) (A CI : ℝ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ τ) < 1 / 8 := by
  have hl : Tendsto (fun m : ℕ => A * (CI * ocEpsilon q Λ (m - 1) ^ τ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (Buffer.preparation_parent_power_tendsto_zero hq hΛ hτ))
  exact eventually_atTop.1
    (hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)))

private theorem retained_level_thresholds (mc mr md mo ma mExist mEnergy j₀ m : ℕ)
    (hm : max mc (max mr (max md (max (mo + 3)
      (max ma (max mExist (max mEnergy (j₀ + 3))))))) ≤ m) (hmr : 2 ≤ mr) :
    mc ≤ m ∧ mr ≤ m ∧ md ≤ m ∧ mo + 1 ≤ m - 1 ∧ ma ≤ m ∧
      mExist ≤ m ∧ mEnergy ≤ m ∧ j₀ ≤ m ∧ j₀ ≤ m - 1 ∧ 2 ≤ m ∧ 1 ≤ m - 1 := by
  omega

private def RetainedCertificatesAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (mStar : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      let Gr := G'.retained m H J
      Gr.IsNatural Mnat ∧ Gr.IsShiftInvariant ∧ Gr.IsSlotTransverse ∧
        Gr.IsContextCertified kI ∧
        markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
          CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ∧
        (∀ v u (γ : Gr.fam.Γ v u),
          (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            v u γ).width = (Gr.fam.identity v u γ).record.width ∧
          ∀ ρ : ℝ, 0 < ρ → IsSpatialRegularizerTorus ρ 0
            (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
            (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              v u γ).width
            (Gr.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              φ₀ hφ₀ v u γ))

private def RetainedProductionAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ)
    (Q T₀ CQ Cpr : ℝ) (Naux Nout k : ℕ) (hk : k + N + 2 * p ≤ Naux)
    (mExist mEnergy mStar : ℕ) (Cread : ℝ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    IncomingLiftGeometryStatement G kI (succSchedR r₀ J H) mExist mEnergy ∧
      RetainedHigherValuesStatement (G'.retained m H J) Naux tp tf Y ∧
      RetainedReadoutBudgetStatement law G (G'.retained m H J) m p Naux N k hk
        (succEta0 α q s) kI.cr tp tf Cread Ain Y Yw

private def UniformRecordLengths (α q : ℝ) (ζ : ℝ → ℝ) (Λ₀ : ℕ) : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.ζ = ζ → Λ₀ ≤ D.Λ →
    IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (Mn : SuccMenu)
      (Cw cr σ₀ η₀ : ℝ) (N p : ℕ), cr ≤ 1 →
    ∀ seed G : GenStage D hr Dm bw j₀,
    seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p) →
    (∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level) →
    seed.level ≤ D.term →
    IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G → 1 ≤ G.level →
    ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level

private def EnhancedRadiusAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀ cr : ℝ) (m₀ : ℕ) : Prop :=
  ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ m : ℕ, m₀ ≤ m → m ≤ D.term → rhoEnh D cr m ≤ rhoStar D c₀ (m - 1)

private def EnhancedDriftAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (cr : ℝ) (m₀ : ℕ) : Prop :=
  ∀ Φ : ℕ → ℝ → Vec 2 → ℝ,
        IsOCStreamSeq α q Λ ζ Φ → ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        let ρ := cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)
        0 < κ (m - 1) ∧ 0 < ρ ∧
        1024 * ρ / ocEpsilon q Λ (m - 1) ≤ 1 / 2 ∧
        (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) * 1024 * ρ ^ 2 ≤
          κ (m - 1) / 8 ∧
        ∀ t : ℝ, ∀ j : ℕ, 1 ≤ j → ∀ x : Vec 2,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ (m - 1)) t)) j x‖ ≤
            (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) *
              1024 ^ j * (j.factorial : ℝ) *
                (ocEpsilon q Λ (m - 1)) ^ ((1 : ℤ) - j)

private def NativeKernelOperatorsAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (bw : ℝ) (n Dm : ℕ)
    (c : ℕ → ℝ) (A : ℝ) (m₀ : ℕ) : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
        [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → G.IsShiftInvariant → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      ∀ (P : ProvParams) (seedK freshK : ℕ → KernelSpec),
      (∀ v u γ, (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width) →
      ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (a b ρ Sbound : ℝ) (π marker : CompIn G.comps → ℝ),
      a ≤ b → 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∀ v, 0 < π v) → (∀ v, 0 < marker v) → markedLedger π marker G.fam ≤ Sbound →
      A * Sbound ≤ 1 / 8 →
      (∀ v u γ, IsSpatialRegularizerTorus ρ 0 Dm a b c
        (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ)) →
      ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = marker →
      ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
          (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ (D.kap G.level) n Dm,
        R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
          (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
        R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
          ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
        R.S = G.sysS P seedK freshK φ₀ hφ₀ ∧ R.π = (fun v => π v / w v ^ 2) ∧
        R.r = (fun v u γ => (G.kernelOf P seedK freshK v u γ).width) ∧ R.c = c ∧ R.θ = A * Sbound

private def RetainedAnalyticTailStatement : Prop :=
  ∀ {α s q : ℝ}, 0 < α → 0 < s → IsAdmissibleQ α s q → ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀ volume)
  (bw : ℝ), 0 < bw → ∀ (Q Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI :
  InvConsts) (CI Cw : ℝ) (j₀ k : ℕ) (hk : k + N + 2 * p ≤ Naux) (CQ Cpr : ℝ), Naux + 3 + 2 * p + 2 ≤ Nout → ∀
  (A : ℝ), let c := fun j => max (kI.cker j) 0; let Cread := max 0 (√(↑(wordsUpTo (succAlphabetOf r₀ D₀ H J N
  p npad) (J + 1)).card + 1) * √2 * Cpr); ∀ (D : OCData) (Mnat : ℕ) (law : BirthLaw), IsSuccessorLaw α q s
  (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law → ∀ {hr : ℕ → Type} [_inst : (r : ℕ) →
  NormedAddCommGroup (hr r)] [_inst_1 : (r : ℕ) → InnerProductSpace ℝ (hr r)] [_inst_2 : ∀ (r : ℕ),
  FiniteDimensional ℝ (hr r)] [_inst_3 : (r : ℕ) → MeasurableSpace (hr r)] [_inst_4 : ∀ (r : ℕ), BorelSpace (hr
  r)] [_inst_5 : ∀ (r : ℕ), CompleteSpace (hr r)] (seedK freshK : ℕ → KernelSpec) (seed : GenStage D hr
  (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ), IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀
  (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ Mnat kS seed n tS tf Ce τe r₀ D₀ → ∀ (m : ℕ) (s₀ : ℝ) (G G' :
  GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀), IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α
  q s) N p) (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G → G.level = m → IsActualSuccessor
  D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q
  s)) G G' → ∀ (tp : ℝ) (Preg : ((v : CompIn G.comps) → TorusHk 0 (hr v.1.root)) →ₗ[ℝ] (v : CompIn G.comps) →
  TorusHk Nout (hr v.1.root)), IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
  seedK freshK φ₀ hφ₀ G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg → ∀ (f : (v : CompIn G.comps) → TorusHk 0 (hr
  v.1.root)) (Ain : ℝ), weightedNorm 1 (GenStage.mass law G) (GenStage.marker law G) f ≤ Ain → ∀ (Y0 : (v' :
  CompIn (G'.retained m H J).comps) → TorusHk Naux (hr v'.1.root)) (Y : (v : CompIn (G'.retained m H
  J).comps) → ℝ → TorusHk Naux (hr v.1.root)) (Yw : (v : CompIn (G'.retained m H J).comps) → ℝ → TorusHk
  (Naux + 1) (hr v.1.root)) (Yk : (v u : CompIn (G'.retained m H J).comps) → (G'.retained m H J).fam.Γ v u →
  ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)), IsRetainedTrace G (G'.retained m H J) m
  p tp (Preg f) Y0 → GenStage.IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
  φ₀ hφ₀ (G'.retained m H J) (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk → 2 ≤ m → 1 < D.q → 128 ≤ D.Λ → IsFastProfile D.ζ → let P := (succProvParams D Cw kI.cr σ₀
  (succEta0 α q s) N p); let Gr := G'.retained m H J; Gr.level = m - 1 → GenStage.IsNatural Mnat (G'.retained m
  H J) → (G'.retained m H J).IsSlotTransverse → GenStage.IsContextCertified kI (G'.retained m H J) → (∀ (v :
  CompIn Gr.comps), 0 ≤ compReserve kI v.1) → (∀ (v : CompIn Gr.comps), compReserve kI v.1 ≤ 2) → (∀ (l : ℕ), 0
  < D.eps l) → rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) → (∀ (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u),
  IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0 (succSchedD D₀ N p (H + 1)) tp tf c (GenStage.kernelOf P
  seedK freshK Gr v u γ).width (GenStage.sysS P seedK freshK φ₀ hφ₀ Gr v u γ)) → A * (CI * D.eps (m - 1) ^ min
  (ocDelta α q / 4) τe) < 1 / 8 → (∀ (w : CompIn Gr.comps → ℝ), (w = fun _ => 1) ∨ w = GenStage.marker law Gr
  → ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn Gr.comps => hr v.1.root) (Γ := Gr.fam.Γ) (G :=
  fun _ u _ => hr u.1.root) tp tf (rhoEnh D kI.cr m) (D.κ (m - 1)) Naux (succSchedD D₀ N p (H + 1)), (R.B =
  fun (v u : CompIn Gr.comps) (γ : Gr.fam.Γ v u)
    (d : ↥(Finset.Icc 2 (succSchedD D₀ N p (H + 1)))) => Gr.physCoeff v u γ d.1) ∧ (R.C = fun (v u : CompIn Gr.comps) (_ : Gr.fam.Γ v u) => ContinuousLinearMap.id ℝ (hr u.1.root)) ∧ R.S =
  GenStage.sysS P seedK freshK φ₀ hφ₀ Gr ∧ (R.π = fun v => GenStage.mass law Gr v / w v ^ 2) ∧ (R.r = fun v u
  γ => (GenStage.kernelOf P seedK freshK Gr v u γ).width) ∧ (R.c = fun j => max (kI.cker j) 0) ∧ R.θ = A * (CI
  * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)) → IsAdmissibleStream (D.Φ (m - 1)) → let αv := (
  Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)); 0 ≤ αv → 1024 * rhoEnh D kI.cr m / D.eps (m - 1) ≤ 1 / 2
  → αv * 1024 * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8 → (∀ t ∈ Set.Icc tp tf, ∀ (j : ℕ), 1 ≤ j → j ≤ Naux + 3
  → ∀ (x : Vec 2), ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) j x‖ ≤ αv * 1024
  ^ j * ↑j.factorial * D.eps (m - 1) ^ ((1 : ℤ) - j)) → j₀ ≤ Gr.level → RetainedHigherValuesStatement Gr Naux
  tp tf Y ∧ RetainedReadoutBudgetStatement law G Gr m p Naux N k hk (succEta0 α q s) kI.cr tp tf Cread Ain Y
  Yw

private theorem retained_analytic_tail : RetainedAnalyticTailStatement := by
  intro α s q hα₀ hs₀ hq Λ φ₀ hφ₀ bw hbw Q Ce τe kS r₀ D₀ H J N p Naux Nout npad sX sZ σ₀ kI CI Cw j₀ k hk
    CQ Cpr hreserve A c Cread D Mnat law hlaw hr _ _ _ _ _ _ seedK freshK seed n tS tf hseed m s₀ G G'
    hcascade hlevel hactual tp Preg hprep f Ain hf Y0 Y Yw Yk htrace hsol hm2 hqD hΛD hζD P Gr hGrlevel
    hnat hslot hctx hmGr hm2Gr he hρE hSzero hsmall hop' hφ αv hαv hsmallD hstrain hjets hjGr
  classical
  subst m
  let m := G.level
  have hlevel : G.level = m := rfl
  obtain ⟨R, hB, hC, hS, _hπ, hrR, hcR, hθ⟩ := hop' (fun _ => 1) (Or.inl rfl)
  have hsR : ∀ i j γ, IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf R.c (R.r i j γ) (R.S i j γ) := by
    simpa only [hS, hrR, hcR] using hSzero
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  have hhigher : RetainedHigherValuesStatement Gr Naux tp tf Y := by
    exact native_retained_solution_higher_extension_of_same_order_operator P seedK freshK φ₀ hφ₀ Gr
      (by omega : Naux ≤ Naux + 3) R hB hC hS (hθ ▸ hsmall) hsR hctx hslot hnat
      (by omega) (by omega) hbw (he _) hρE hmGr hm2Gr hφ αv 1024 (D.eps (m - 1))
      hαv (by norm_num) (he _) hsmallD hstrain hjets Y0 Y Yw Yk hsol G m p Nout
      hreserve
      (by omega) hζD (Preg f) htrace
  refine ⟨hhigher, ?_⟩
  · have hη : 0 < succEta0 α q s := succEta0_pos_of_admissible hα₀ hs₀ hq
    have hcH : law.cH ≤ 1 := by
      have hx := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 128) (-(succEta0 α q s / 2))
      linarith only [hlaw.2.2.2.1, hx]
    have hηB : 0 ≤ law.etaB := by rw [hlaw.2.1]; positivity
    have hη0 : 0 ≤ law.eta0 := by rw [hlaw.1]; exact hη.le
    have hiota : 0 ≤ law.iota := by rw [hlaw.2.2.1]; positivity
    have hST : G.comps ⊆ Gr.comps := incoming_mem_retained_of_cascade hseed.2.1 hcascade hactual hlevel
    have hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale := by
      intro v hv e he'
      rw [← hlevel]
      exact (InitialValue.cascade_invariant hseed.2.1 hcascade v hv).1 e he'
    have hf1 := ordinary_input_from_marked G hqD hΛD law hiota 1 f hf
    have hread (wgt : Comp → ℝ) (hwgt : wgt = (fun _ => 1) ∨ wgt = compMarker D.q D.Λ law)
        (hfgt : weightedNorm 1 (G.mass law) (fun v => wgt v.1) f ≤ Ain) :
        readoutEnergy law G Gr m law.eta0 (rhoEnh D kI.cr m) hk
          (fun v => wgt v.1) tp tf Y Yw ≤ ENNReal.ofReal (Cread * Ain) := by
      have hwgt' : (fun v : CompIn Gr.comps => wgt v.1) = (fun _ => 1) ∨
          (fun v : CompIn Gr.comps => wgt v.1) = Gr.marker law := by
        rcases hwgt with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨Rw, hBw, hCw, hSw, hπw, _hrw, _hcw, _hθw⟩ := hop' (fun v => wgt v.1) hwgt'
      have hh := common_preparation_readout_budget_fixed_constant law P seedK freshK φ₀ hφ₀
        G Gr G' Mn hactual rfl (by omega) hold hqD hΛD hcH hηB hη0 hiota hk hlevel hST
        Preg hprep wgt hwgt f Ain hfgt Y0 htrace Rw hBw hCw hSw hπw hφ
        αv 1024 (D.eps (m - 1)) hαv (by norm_num) (he _)
        (by simpa only [hlevel] using hsmallD) (by simpa only [hlevel] using hstrain)
        (fun t ht j hj hj' x => hjets t ht j hj (by omega) x)
        Y Yw Yk hsol hsol.2.1 Cread (le_max_right _ _)
      simpa only [hlevel] using hh
    intro w hw
    rcases hw with rfl | rfl
    · rw [← hlaw.1]
      exact hread (fun _ => 1) (Or.inl rfl) hf1
    · rw [← hlaw.1]
      exact hread (compMarker D.q D.Λ law) (Or.inr rfl) hf

private theorem retained_production_at_data {α s q : ℝ}
    (hα₀ : 0 < α) (hs₀ : 0 < s) (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ) (hbw : 0 < bw)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ k : ℕ) (hk : k + N + 2 * p ≤ Naux)
    (CQ Cpr : ℝ) (mExist mEnergy mc : ℕ)
    (hreserve : Naux + 3 + 2 * p + 2 ≤ Nout)
    (hc : RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md) (A : ℝ) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Naux (succSchedD D₀ N p (H + 1))
      (fun j => max (kI.cker j) 0) A mo) (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8) :
    RetainedProductionAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀
      Q T₀ CQ Cpr Naux Nout k hk mExist mEnergy
      (max mc (max mr (max md (max (mo + 3) (max ma (max mExist (max mEnergy (j₀ + 3))))))))
      (max 0 (Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card + 1) *
        Real.sqrt 2 * Cpr)) := by
  classical
  let c : ℕ → ℝ := fun j => max (kI.cker j) 0
  let Cread := max 0 (Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad)
    (J + 1)).card + 1) * Real.sqrt 2 * Cpr)
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf
    Y0 Y Yw Yk htrace hsol
  have hm' : max mc (max mr (max md (max (mo + 3)
      (max ma (max mExist (max mEnergy (j₀ + 3))))))) ≤ m := hm
  obtain ⟨hmc, hmr', hmd', hmo', hma, hge, hgu, hjG', hjGr', hm2, hiGr'⟩ :=
    retained_level_thresholds mc mr md mo ma mExist mEnergy j₀ m hm' hmr
  have hm1 : 1 ≤ m := (by decide : 1 ≤ 2).trans hm2
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [hlevel, succMenu, Mn, Gr, P] using IsCascadeStage.step hcascade hactual
  have hprod' : kI.Hprod = kI.G0 + Mn.H + 1 := hprod
  have hmG v : 0 ≤ compReserve kI (v : CompIn G.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcascade kI hprod' v).le
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod' v).le
  have hm2G v : compReserve kI (v : CompIn G.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade (hlevel.symm ▸ hm1)
  have hlenGr := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed Gr hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcGr (hGrlevel.symm ▸ hiGr')
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf c
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    apply spatial_regularizer_constants_mono
      (Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub)
    · rw [(hker v u γ).1]
      exact (Gr.fam.identity v u γ).record.width_pos.le
    · intro j _
      exact le_max_left _ _
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  have hφ : IsAdmissibleStream (D.Φ (m - 1)) := (hseq.2 m hm1).choose
  let αv := Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)
  have hαv : 0 ≤ αv := mul_nonneg Buffer.actualDriftJetConstant_nonneg
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hsmallD : 1024 * rhoEnh D kI.cr m / D.eps (m - 1) ≤ 1 / 2 := by
    simpa only [rhoEnh, OCData.eps, hDα, hDq, hDΛ] using hd.2.2.1
  have hstrain : αv * 1024 * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8 := by
    simpa only [αv, rhoEnh, hDα, hDq, hDΛ] using hd.2.2.2.1
  have hjets : ∀ t ∈ Set.Icc tp tf, ∀ j, 1 ≤ j → j ≤ Naux + 3 → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) j x‖ ≤
        αv * 1024 ^ j * (j.factorial : ℝ) * D.eps (m - 1) ^ ((1 : ℤ) - j) := by
    intro t _ j hj _ x
    simpa only [αv, OCData.eps, hDq, hDΛ] using hd.2.2.2.2 t j hj x
  have hρG := hrs m hmterm
  have hdepth := Providers.CascadeInvariants.cascade_depth_of_generatedSeed hseed hcascade
  have hgeom : IncomingLiftGeometryStatement G kI (succSchedR r₀ J H) mExist mEnergy := by
    refine ⟨hlevel.symm ▸ hge, hlevel.symm ▸ hgu, ?_, hlevel.symm ▸ hjG',
      ?_, hmG, hm2G, hlenG, hlevel.symm ▸ hρG.1, hlevel.symm ▸ hρG.2⟩
    · rw [hlevel, hterm]
      exact hn.trans_lt hnM
    · simpa only [succMenu] using hdepth
  suffices hrest : RetainedHigherValuesStatement Gr Naux tp tf Y ∧
      RetainedReadoutBudgetStatement law G Gr m p Naux N k hk (succEta0 α q s) kI.cr
        tp tf Cread Ain Y Yw by exact ⟨hgeom, hrest⟩
  have hjGr : j₀ ≤ Gr.level := hGrlevel.symm ▸ hjGr'
  have htail := @retained_analytic_tail α s q hα₀ hs₀ hq Λ φ₀ hφ₀ bw hbw Q Ce τe kS r₀ D₀ H J N p Naux Nout npad sX sZ σ₀ kI CI Cw j₀ k hk
    CQ Cpr hreserve A
  have htailD := @htail D Mnat law hlaw hr (by infer_instance) (by infer_instance) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) seedK freshK seed n tS tf hseed
  have htailG := htailD m s₀ G G' hcascade hlevel hactual tp Preg hprep f Ain hf
  have htailY := htailG Y0 Y Yw Yk htrace hsol
  exact htailY hm2 hqD hΛD hζD hGrlevel
    hnat hslot hctx hmGr hm2Gr he hρE hSzero hsmall hop' hφ hαv hsmallD hstrain hjets hjGr

theorem retained_production_bundle_of_certificates {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (hcert : RetainedStageCertificatesStatement α s q ζ) :
    RetainedProductionBundleStatement α s q ζ := by
  classical
  refine Exists.elim hcert fun Λc hc0 => ?_
  have hΛc := hc0.1
  have hc := hc0.2
  refine (uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ).elim fun Λl hl0 => ?_
  have hΛl := hl0.1
  have hlength := hl0.2
  change UniformRecordLengths α q ζ Λl at hlength
  refine (uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ).elim
    fun Λr hr0 => ?_
  have hΛr := hr0.1
  have hradius := hr0.2
  refine (actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ).elim fun Λd hd0 => ?_
  have hΛd := hd0.1
  have hdrift := hd0.2
  intro Λbase hΛbase
  refine ⟨max Λbase (max Λc (max Λl (max Λr Λd))), by omega, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  refine (hc Λ (by omega)).elim fun cmax hc1 => ?_
  have hcmax := hc1.1
  have hc := hc1.2
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine (hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX
    hsZ).elim fun thr h1 => h1.elim fun CH h2 => h2.elim fun Υ hc2 => ?_
  have hCH := hc2.1
  have hΥ := hc2.2.1
  have hc := hc2.2.2
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  refine (hc kI hkI).elim fun CIthr h1 => h1.elim fun Cwthr hc => ?_
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart k hk CQ Cpr mExist mEnergy hmExist hmEnergy
  refine (hc CI Cw j₀ hledger hstart).elim fun mc hc => ?_
  change RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
    σ₀ kI CI Cw j₀ mc at hc
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Buffer.preparation_schedule_order_ge_two D₀ N p H
  refine (hradius Λ (by omega) kI.c₀ kI.cr hc0pos hcrpos).elim fun mr hr1 => ?_
  have hmr := hr1.1
  have hradius := hr1.2
  change EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr at hradius
  refine (hdrift Λ (by omega) kI.cr hcrpos).elim fun md hd1 => ?_
  have hdrift := hd1.2
  change EnhancedDriftAt α q ζ Λ kI.cr md at hdrift
  let c : ℕ → ℝ := fun j => max (kI.cker j) 0
  refine (uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Naux
    (succSchedD D₀ N p (H + 1)) hDm c (fun _ _ => le_max_right _ _)).elim fun A hA1 =>
    hA1.2.elim fun mo hmo1 => ?_
  have hop := hmo1.2
  change NativeKernelOperatorsAt α q ζ Λ bw Naux (succSchedD D₀ N p (H + 1)) c A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  refine (retained_absorption_threshold hq.1 h128 hτ A CI).elim fun ma habs => ?_
  let Cread := max 0 (Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad)
    (J + 1)).card + 1) * Real.sqrt 2 * Cpr)
  let mStar := max mc (max mr (max md (max (mo + 3)
    (max ma (max mExist (max mEnergy (j₀ + 3)))))))
  refine ⟨Cread, mStar, le_max_left _ _, ?_⟩
  change RetainedProductionAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀
    Q T₀ CQ Cpr Naux Nout k hk mExist mEnergy mStar Cread
  exact retained_production_at_data hα₀ hs₀ hq hζ Λl Λ hlength (by omega) h128
    φ₀ hφ₀ bw hbw Q T₀ Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ k hk
    CQ Cpr mExist mEnergy mc
    (successor_lift_gradient_trace_reserve hα₀ hα₁ hs₀ hs₁ hq hQ hsched) hc
    hprod hc0pos hc0le hcrle mr hmr hradius md hdrift A mo hop ma habs

end AVRegularity.Construction.Preservation.Assembly
end
end

section
/-! Time consumption and chart-certificate assembly for common preparation.
The shared window cover stays a single input; no cover estimate is proved here.

Neither proof uses an edge, a positive component dimension, or a quiet-transition identity,
so an empty component type or an edgeless seed preserves the time argument and chart
certificate as well. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
universe u v w x
namespace AVRegularity.Construction.Preservation.Assembly

private theorem preservation_joint_endpoint_le_four {s tp T CH : ℝ}
    (hCH : CH = 2) (hT : 0 ≤ T) (htp : tp ≤ s + CH * T) : tp ≤ s + 4 * T := by
  subst CH
  exact htp.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by norm_num) hT))

/-- Consume the duration equality from the joint preparation `cycle_joint`, preserving all its
witnesses.
The resulting preparation endpoint lies in the four-scale budget. -/
theorem cycle_joint_preparation_of_inputs
    (hJoint : PreservationCycleJointStatement.{u, v, w, x}) :
    CycleJointPreparationStatement.{u, v, w, x} := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hJoint⟩ := hJoint α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨g₀, hg₀, hJoint⟩ := hJoint Λ hΛ
  refine ⟨g₀, hg₀, ?_⟩
  intro Pacc hPacc Mout H D Kmax hD
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, CH, hCH, hCHtwo, hJoint⟩ :=
    hJoint Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, CH, hCH, hCHtwo, ?_⟩
  intro Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld
  obtain ⟨C, CP, c, mStar, hc, hJoint⟩ :=
    hJoint Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld
  refine ⟨C, CP, c, mStar, hc, ?_⟩
  intro ι _ _ h _ _ _ _ _ _ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ
    tS g a B₀ lam l₀ P y₀ hcov P' Ctx F hwmeas hprep actual hdepth hdesc htorus
    hcover hmeas A Θ hΘ₀ hΘ₁ htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  obtain ⟨tp, Pd, Pg, htp, hqtp, hquietMargin, hall⟩ := hJoint K hK Φ hΦ M' κ hband
    m hm2 hmStar hmM ν B hν hB hφ tS g a B₀ lam l₀ P y₀ hcov F hwmeas hprep actual hdepth hdesc
    htorus hcover hmeas A Θ hΘ₀ hΘ₁ htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  have htime : 0 ≤ ocTauPP α q Λ m :=
    (Construction.Stream.ocTauPP_pos ((by norm_num : 1 ≤ 128).trans (hΛ₀.trans hΛ))).le
  exact ⟨tp, Pd, Pg, htp, htp.1.le,
    preservation_joint_endpoint_le_four hCHtwo htime htp.2, hqtp, hquietMargin, hall⟩

/-- Assemble the full preparation chart certificate from the schedule construction and
existing level-generic flow jets. The constants precede the stage, start time and datum. -/
theorem preservation_preparation_chart_certificate
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ), 0 ≤ Cpad ∧ 0 < Cage ∧
    ∃ mStar : ℕ, 2 ≤ mStar ∧
    ∀ (data : OCData), data.α = α → data.q = q → data.Λ = Λ →
    ∀ (Mnat m : ℕ), 2 ≤ m → mStar ≤ m → m ≤ Mnat →
    ∀ (tS : ℝ) (l₀ : ℤ) (P : ℕ), 1 ≤ P →
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tS →
      tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m →
      tS + 2 * ocTauPP α q Λ m ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m →
    ∀ {ι : Type u} {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
      {D : ℕ} {Ctx : OddSlot → Type w} (F : ChartedFamily ι h D OddSlot Ctx),
      (∀ p, IsNaturalPiece data Mnat m p.val (F.piece p)) →
      IsOCStreamSeq α q Λ ζ data.Φ →
      ∀ Jchart : ℕ,
      IsPreparationChartCertificate α q Λ m (data.Φ (m - 1)) (data.hΦ (m - 1))
        tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F := by
  obtain ⟨C, _, hFlow⟩ := EntryTerminal.Ingredients.prep_flow_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Cpad, Cage, Npad, ms, hpad, hage, hSch⟩ :=
    Providers.preparation_chart_schedule α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ 2 (by norm_num)
  obtain ⟨mf, hmf, hFlow⟩ := hFlow Λ hΛ Cage hage
  refine ⟨Cpad, Cage, Npad, EntryTerminal.Ingredients.prepChartConst C, hpad, hage,
    max ms mf, hmf.trans (le_max_right _ _), ?_⟩
  intro data hDα hDq hDΛ Mnat m hm2 hm hmM tS l₀ P hP hleft hright hend ι h _ _ D Ctx F hnat hΦ Jchart
  exact ⟨hSch data hDα hDq hDΛ Mnat m hm2 ((le_max_left _ _).trans hm) hmM
      tS l₀ P hP hleft hright hend F hnat,
    hFlow data.Φ hΦ m ((le_max_right _ _).trans hm) (data.hΦ (m - 1)) tS
      (tS + 2 * ocTauPP α q Λ m) Cpad Jchart⟩

end AVRegularity.Construction.Preservation.Assembly
end
end
