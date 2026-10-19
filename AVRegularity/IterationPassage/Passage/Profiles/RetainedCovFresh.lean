-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Passage.Profiles.SmoothRep
import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleReference.TorusChartEquation
public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
section
/-! **The discarded profiles: the named steps**.

`PassageDiscardedProfilesStatement` is assembled (`passageDiscardedProfiles_of`) from four named
steps.

* `DiscMomentStatement` (abstract): moment cancellation of the fresh kernel on a family of
  weighted `H^M` fields: the defect `a - S a` has an `H^k` realization `W` with
  `‖W‖_{ρ,k;π'} <= C (r/ρ)^L ‖Y‖_{ρ,M;π'}`, `k + L + 2 <= M` (from `kernelDefect` per component).
* `DiscDEStatement` (abstract): the profile `𝓘_{E,K;s}(F 𝖱(P_p - I) f)` of the readout of the
  covariance correction of a classical field `f` with an `H^{K+2+2p}` realization `w` is at most
  `C μ (∑_j E^{j-s}ρ^{-j-1}) ‖w‖_{ρ,K+2+2p;π'}` when `fbCovConst ρ H (K+2+2p) <= μ <= 1`.
* `DiscScalesStatement`: the scales of a band chain: `r = ρ E^{σ₀}`, `ρ >= c E^{1+c₁}`,
  `ρ <= 1`, and the comparison of `e = ε_m` with `ρ`, `E`.
* `DiscDeStep` (stage level, under `DiscPrefix`): the lift profile `𝓘_{e,K;s}(D_e)` of the readout
  of the covariance image of a defect with an `H^{K+N+2+2p}` realization.

`DiscPrefix`: the prefix of `PassageDiscardedProfilesStatement` with the choices of the other
profile modules fixed (`thr = kS`, `CH = Υ = 1`, ledger thresholds `0`, `SX = SZ = Kneed = 0`), so
that steps with the same prefix can be merged; `discPrefix_main` gives the statement from a tail
proved for all prefixes.

Special cases: `p = 0` (`P_p - I = 0`); the realization `w = 0` (the fields vanish); `K` minimal. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- **Step 1: moment cancellation** (per component by `kernelDefect`; the weights are the masses). -/
def DiscMomentStatement : Prop :=
  ∀ (φ₀ : Vec 2 → ℝ), Integrable φ₀ → ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (k L : ℕ) (n : ℕ+) (Γ : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ {S' : Finset Comp} (π' : CompIn S' → ℝ), (∀ v, 0 < π' v) →
    ∀ (Sr : KernelSpec) (t ρ : ℝ), Sr.order = n → Sr.IsAdmissible Γ L → 0 < Sr.width →
      Sr.width ≤ ρ →
    ∀ (M : ℕ), k + L + 2 ≤ M →
    ∀ (Yn : ∀ v : CompIn S', TorusHk M (ScalarH v.1.root))
      (a : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root), Continuous a → IsZ2Periodic a →
      (∀ v, (Yn v).toFunction.jet (valueIndex2 M) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => a x v) →
    ∃ W : ∀ v : CompIn S', TorusHk k (ScalarH v.1.root),
      (∀ v, IsClassicalRep (W v) (fun x => (a x - Sr.applyClassical φ₀ t a x) v) k) ∧
      weightedNorm ρ π' (fun _ => 1) W ≤
        C * (Sr.width / ρ) ^ L * weightedNorm ρ π' (fun _ => 1) Yn

/-- **Step 2: the covariance correction in the profile norm** (carrier of `(P_p - I)𝖱 w`, adjoint
tail bound at order `K+2`, then `sobolevProfile`). -/
def DiscDEStatement : Prop :=
  ∀ (K p : ℕ) (Cn : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (D : OCData) (m : ℕ) {S S' : Finset Comp} (π : CompIn S → ℝ) (π' : CompIn S' → ℝ),
      (∀ v, 0 < π v) → (∀ v, 0 < π' v) →
    ∀ (E η₀ s ρ μ t : ℝ), 0 < ρ → ρ ≤ 1 → 0 < E →
      ‖readoutCLM m E η₀ π π'‖ ≤ Cn →
      (∀ i j, covPrimitive D m t i j = covPrimitive D m t j i) →
      CycleComparison.Coarse.fbCovConst ρ (covPrimitive D m t) (K + 2 + 2 * p) ≤ μ → μ ≤ 1 →
    ∀ (w : ∀ v : CompIn S', TorusHk (K + 2 + 2 * p) (ScalarH v.1.root))
      (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root),
      (∀ v, IsClassicalRep (w v) (fun x => f x v) (K + 2 + 2 * p)) →
      profileNorm E K s (compField π (fieldReadout (S := S) m E η₀
          (fun _ x => covPolyP (covPrimitive D m t) p f x - f x) t)) ≤
        ENNReal.ofReal (C * μ * (∑ j ∈ Finset.range (K + 1), E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1)) *
          weightedNorm ρ π' (fun _ => 1) w)

/-- **Step 3: the scales of the band chain** (`ρ = rhoEnh`, `r = freshWidth`, `E = ε_{m-1}`,
`e = ε_m`, `ρ_L = liftLength`). -/
def DiscScalesStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → 0 ≤ ocC α q ∧
  (∀ c : ℝ, 0 < c → ∃ m₁ : ℕ, ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
    ∀ m : ℕ, m₁ ≤ m → D.eps (m - 1) ≤ c) ∧
  ∀ cr : ℝ, 0 < cr → cr ≤ 1 → ∃ C : ℝ, 1 ≤ C ∧
  ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
  ∀ M : ℕ, IsOCBandChain α q Λ ζ M D.κ → D.term = M →
  ∀ m : ℕ, 2 ≤ m → m ≤ M →
    rhoEnh D cr m = freshLength D cr (m - 1) ∧ (D.eps (m - 1) ≤ C⁻¹ → rhoEnh D cr m ≤ 1) ∧
    C⁻¹ * D.eps (m - 1) ^ (1 + ocC α q) ≤ rhoEnh D cr m ∧
    C⁻¹ * D.eps (m - 1) ^ q ≤ rhoEnh D cr m ∧
    C⁻¹ * D.eps (m - 1) ^ q ≤ D.eps m

/-- The prefix of `PassageDiscardedProfilesStatement`, bundled (choices fixed as for the retained
profiles). -/
structure DiscParams (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) where
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀
  hφpos : ∀ z, 0 ≤ φ₀ z
  hφint : ∫ z, φ₀ z = 1
  hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  bw : ℝ
  hbw : 0 < bw
  hbw' : bw ≤ 1 / 10000
  K : ℕ
  Pacc : ℝ
  hK : 3 ≤ K
  hPacc : 0 < Pacc
  Q : ℝ
  T₀ : ℝ
  hQ : 0 < Q
  hT₀ : 0 < T₀
  hQb : Pacc + q * iterZ α q s K + 4 < Q / 2
  r₀ : ℕ
  D₀ : ℕ
  τe : ℝ
  lamE : ℝ
  σE : ℝ
  hτe : 0 < τe
  hlamE : 0 < lamE
  hσE : 0 < σE
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  nk : ℕ
  Lc : ℕ
  Lf : ℕ
  Lpr : ℕ
  Acl : ℕ
  Naux : ℕ
  Nout : ℕ
  Kres : ℕ
  npad : ℕ
  σ₀ : ℝ
  a : ℝ
  σ : ℝ
  hsched : IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout
  hNaux : Naux ≤ Kres
  hNout : Kres + 2 * p ≤ Nout
  L : ℕ
  hL : IsPassageOrders α q s K Pacc σ₀ L N p nk Naux
  hwid : IsCascadeWidths α q lamE a σ (succDstar D₀ N p H)
  sX : ℕ
  sZ : ℕ
  Ce : ℝ
  kS : InvConsts
  hCe : 1 ≤ Ce
  hc₀ : 0 < kS.c₀
  hc₀max : kS.c₀ ≤ c₀max
  hcr : 0 < kS.cr
  hcr1 : kS.cr ≤ 1
  hσf : kS.σf = σE
  hlamC : kS.lamC = lamE
  halloc : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf
  kI : InvConsts
  hkI : IsInvariantAdmissible kS kS kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q)
  CI : ℝ
  Cw : ℝ
  j₀ : ℕ
  hledger : IsLedgerAdmissible Ce CI Cw 0 0
  hstart : IsCarrierStart α q Λ bw 1 1 j₀
  Cn : ℝ

/-- A statement about all prefixes, with the thresholds `Λ₀`, `c₀max` existentially. -/
def DiscPrefix (α s q : ℝ) (ζ : ℝ → ℝ)
    (Tail : ∀ (Λ : ℕ) (c₀max : ℝ), DiscParams α s q ζ Λ c₀max → Prop) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ P : DiscParams α s q ζ Λ c₀max, Tail Λ c₀max P


/-- **Step 4: the lift profile `D_e`** (glued word bound of the lift, Schur budget, scaled Sobolev
sup bounds at the orders `i <= K + N`). -/
def DiscDeData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ)
    (H J N p nk npad : ℕ) (σ₀ : ℝ) (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ)
    (j₀ : ℕ) (Cn Cd : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law) ((G'.retained m H J).mass law)‖ ≤ Cn →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root) (t : ℝ),
      s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
    ∀ (w : ∀ v : CompIn (G'.retained m H J).comps, TorusHk (K + N + 2 + 2 * p) (ScalarH v.1.root)),
      (∀ v, IsClassicalRep (w v)
        (fun x => (aY t x - fieldKernel φ₀ (freshK (m - 1)) aY t x) v) (K + N + 2 + 2 * p)) →
      profileNorm (D.eps m) K s (((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 3 0) ≤
        ENNReal.ofReal (Cd * D.eps m ^ (-s) * (rhoEnh D kI.cr m)⁻¹ *
          weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) (fun _ => 1) w)


/-- The step `D_e` with its prefix. -/
def DiscDeStep (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  DiscPrefix α s q ζ fun Λ _ P => ∃ (Cd : ℝ) (mS : ℕ), 0 ≤ Cd ∧
    DiscDeData α s q ζ Λ P.φ₀ P.hφ₀ P.bw P.K P.T₀ P.r₀ P.D₀ P.τe P.H P.J P.N P.p P.nk
      P.npad P.σ₀ P.sX P.sZ P.Ce P.kS P.kI P.CI P.Cw P.j₀ P.Cn Cd mS

/-- The main statement from a tail proved for all prefixes. -/
theorem discPrefix_main {α s q : ℝ} {ζ : ℝ → ℝ}
    (h : DiscPrefix α s q ζ fun Λ _ P => ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
      PassageDiscardedProfilesData α s q ζ Λ P.φ₀ P.hφ₀ P.bw P.K P.Pacc P.T₀ P.r₀ P.D₀ P.τe P.H
        P.J P.N P.p P.nk P.Naux P.npad P.σ₀ P.sX P.sZ P.Ce P.kS P.kI P.CI P.Cw P.j₀ P.Cn C mStar) :
    PassageDiscardedProfilesStatement α s q ζ := by
  obtain ⟨Λ₀, h128, hh⟩ := h
  refine ⟨Λ₀, h128, fun Λ hΛ => ?_⟩
  obtain ⟨c₀max, hc, hP⟩ := hh Λ hΛ
  refine ⟨c₀max, hc, ?_⟩
  intro φ₀ hφ₀ hφs hφpos hφint hφsupp bw hbw hbw' K Pacc hK hPacc Q T₀ hQ hT₀ hQb r₀ D₀ τe lamE σE
    hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout L hL hwid
  refine ⟨0, 0, 0, ?_⟩
  intro sX sZ _ _ Ce kS hCe hc₀ hc₀max hcr hcr1 hσf hlamC halloc _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart Cn
  exact hP ⟨φ₀, hφ₀, hφs, hφpos, hφint, hφsupp, bw, hbw, hbw', K, Pacc, hK, hPacc, Q, T₀, hQ, hT₀,
    hQb, r₀, D₀, τe, lamE, σE, hτe, hlamE, hσE, H, J, N, p, nk, Lc, Lf, Lpr, Acl, Naux, Nout, Kres,
    npad, σ₀, a, σ, hsched, hNaux, hNout, L, hL, hwid, sX, sZ, Ce, kS, hCe, hc₀, hc₀max, hcr, hcr1,
    hσf, hlamC, halloc, kI, hkI, CI, Cw, j₀, hledger, hstart, Cn⟩

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The error profile**: `passageErrorProfile`.

Route: `sobolevProfile` at `λ = ε_m`, `ρ = ρ_⋆` (positive masses, `0 < ρ_⋆ ≤ 1` as `c₀ ≤ c₀max = 1`),
then `errorProfile_rhoStar_lower` (`ρ_⋆ ≥ (c₀/C) ε_m^{1+c}`, from the band-chain ledger
`κ_m ≍ ε_m^{1+α+γ}`) and `errorProfile_scale_sum_le` with `ε_{m-1}^q ≤ 2 ε_m`.
Constants: `m_* = 2`, `C₀ = C_K (K+1) (C_ℓ/c₀)^{K+1} 2^{Z_K}` with `c₀ = kI.c₀`. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open scoped ENNReal

theorem passageErrorProfile (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageErrorProfileStatement α s q ζ := by
  obtain ⟨Cl, hCl, Λl, hΛl, hled⟩ :=
    CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  have hq1 : 1 < q := hq.1
  have hγ := ocGamma_pos_of_admissible hα₀ hq
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  have hc : 0 < ocC α q := ocC_pos_of_admissible hα₀ hq
  refine ⟨Λl, hΛl, fun Λ hΛ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ K Pacc hK _ Q T₀ _ _ _ r₀ D₀ τe lamE σE _ _ _ H J N p nk Lc Lf Lpr
    Acl Naux Nout Kres npad σ₀ a σ _ _ _ L _ _
  refine ⟨0, 0, 0, ?_⟩
  intro sX sZ _ _ Ce kS _ hc0 hc1 _ _ _ _ _ _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hadm
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _
  obtain ⟨CK, hCK0, hSob⟩ := sobolevProfile K
  have hc₀ : kI.c₀ = kS.c₀ := hadm.1
  have hk0 : 0 < kI.c₀ := hc₀ ▸ hc0
  have hk1 : kI.c₀ ≤ 1 := hc₀ ▸ hc1
  have hCl0 : 0 < Cl := by linarith
  have hΛ128 : 128 ≤ Λ := hΛl.trans hΛ
  have hΛled : Λl ≤ Λ := hΛ
  refine ⟨CK * ((K : ℝ) + 1) * ((Cl / kI.c₀) ^ (K + 1) * 2 ^ (iterZ α q s K)), 2, ?_⟩
  intro C hC D hDα hDq hDΛ hDζ _ M hbc hterm Mnat _ law _ seedK freshK _ seed n tS tf _ _ m hm hmn
    hnM tA s₀ _ _ _ _ G G' _ _ _ _ g t _ _ hFC hFP En B hjet hB
  have hm2 : 2 ≤ m := (show 2 ≤ m from hm)
  have hM1 : 1 ≤ M := by omega
  have hEq : ∀ k, D.eps k = ocEpsilon q Λ k := fun k => by rw [OCData.eps, hDq, hDΛ]
  have hκ := (hled Λ hΛled M hM1 D.κ hbc).1 m (by omega) (by omega)
  have hκ' : ocAsymp Cl (D.κ m)
      (ocEpsilon D.q D.Λ m ^ ((1 + D.α) + ocGamma D.α D.q)) := by
    rw [hDα, hDq, hDΛ]; exact hκ
  have hlow := (errorProfile_rhoStar_lower (D := D) (m := m) (by rw [hDq]; exact hq1)
    (by rw [hDΛ]; exact hΛ128) hCl hk0 hk1 (by rw [hDα, hDq]; exact hδ.le)
    (by rw [hDα, hDq]; exact hγ.le) hκ')
  rw [hDα, hDq] at hlow
  obtain ⟨hlow, hρ1⟩ := hlow
  obtain ⟨he0, he1, -⟩ := Scales.epsilon_basic (m := m) hq1 hΛ128
  obtain ⟨hE0, hE1, -⟩ := Scales.epsilon_basic (m := m - 1) hq1 hΛ128
  rw [← hEq] at he0 he1 hE0 hE1
  have hee : D.eps (m - 1) ^ q ≤ 2 * D.eps m := by
    rw [hEq, hEq]; exact errorProfile_eps_step_lower hq1 hΛ128 hm2
  have ha0 : 0 < kI.c₀ / Cl := div_pos hk0 hCl0
  have ha1 : kI.c₀ / Cl ≤ 1 := (div_le_one hCl0).mpr (hk1.trans hCl)
  have hρ0 : 0 < rhoStar D kI.c₀ m :=
    lt_of_lt_of_le (mul_pos ha0 (Real.rpow_pos_of_pos he0 _)) hlow
  have hmass : ∀ v, 0 < G.mass law v := by
    intro v
    unfold GenStage.mass
    exact Construction.Preservation.Buffer.birth_compMass_pos (by rw [hDq]; exact hq1)
      (by rw [hDΛ]; exact hΛ128) law v.1
  have hprof := hSob (G.mass law) hmass (rhoStar D kI.c₀ m) (D.eps m) s hρ0 hρ1 he0 En g hFC hFP
    hjet
  have hT := errorProfile_scale_sum_le (e := D.eps m) (E := D.eps (m - 1))
    (ρ := rhoStar D kI.c₀ m) (a := kI.c₀ / Cl) (c := ocC α q) (s := s) (q := q) (K := K)
    he0 he1 hE0 ha0 ha1 hc.le hs₀.le hlow hee
  set W := weightedNorm (rhoStar D kI.c₀ m) (G.mass law) (fun _ => 1) En with hWdef
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := hW0.trans hB
  have hz : iterZ α q s K = 1 + s + ocC α q * ((K : ℝ) + 1) := rfl
  have hEz : 0 ≤ D.eps (m - 1) ^ (-(q * iterZ α q s K)) := (Real.rpow_pos_of_pos hE0 _).le
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (K + 1),
      D.eps m ^ ((j : ℝ) - s) * (rhoStar D kI.c₀ m) ^ (-(j : ℝ) - 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  refine hprof.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hz] at hEz ⊢
  have h1a : (1 / (kI.c₀ / Cl)) = Cl / kI.c₀ := by rw [one_div_div]
  rw [h1a] at hT
  calc CK * (∑ j ∈ Finset.range (K + 1),
        D.eps m ^ ((j : ℝ) - s) * (rhoStar D kI.c₀ m) ^ (-(j : ℝ) - 1)) * W
      ≤ CK * (((K : ℝ) + 1) * ((Cl / kI.c₀) ^ (K + 1) * (2 ^ (1 + s + ocC α q * ((K : ℝ) + 1)) *
          D.eps (m - 1) ^ (-(q * (1 + s + ocC α q * ((K : ℝ) + 1))))))) * B := by gcongr
    _ = CK * ((K : ℝ) + 1) * ((Cl / kI.c₀) ^ (K + 1) * 2 ^ (iterZ α q s K)) *
          D.eps (m - 1) ^ (-(q * (1 + s + ocC α q * ((K : ℝ) + 1)))) * B := by rw [hz]; ring
    _ ≤ C * D.eps (m - 1) ^ (-(q * (1 + s + ocC α q * ((K : ℝ) + 1)))) * B := by
        gcongr

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The glued positive word bound, componentwise**.

The positive part of a glued lift (coefficients of degree `n ≥ 1` only,
`positiveLiftCoefficients`) costs one factor `ε_c = d_*/ρ` and sees only the positive jets of the
input: for a spatial word `β` of order `r`,

`r_s^r |∂^β (T⁺a)_v(x)| ≤ ε_c (∑_{n<N} C_{n+1}) ∑_u (∑_{h≤H} M_h(v,u)) ∑_{1≤j≤P₀+N} ρ^j |D^j a_u(x)|`.

* `positive_glued_word_bound_of_data`: the general form, the positive analogue of
  `glued_word_bound_of_data` (the pulses are glued by `gluedLift_spatial_word_norm_le`, each pulse
  is `positive_pulse_fixed_matrix_word_bound_of_data` at the frozen time);
* `nativeStageLiftFamily_positive_glued_word_bound`: the native family of the slot lifts of a
  stage, with the fixed matrix of `nativeSlotLift_uniform_coefficient_data`; the order-zero
  coefficients vanish by `nativeSlotLift_zero_order_eq_zero`.

Special cases: `N = 0` (no positive degree: both sides vanish); no active pulse (the glued field is
the empty sum); `a τ` constant (the positive jets vanish, and so does the positive part). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison.Lift
  AVRegularity.Finite

namespace AVRegularity.IterationPassage.Passage

section General

variable {ι : Type*} [Fintype ι] {hv : ι → Type*}
  [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)]

/-- Positive pulses glue at arbitrary radii with one factor `ε_c` and no zero jet of the input. -/
theorem positive_glued_word_bound_of_data
    {par : ℤ → Fin 2} {tlo thi : ℤ → ℝ} {lam : ℝ} {P₀ Q N H : ℕ}
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι hv) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u)
    (kset : Finset ℤ) (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ Q) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : ι, hv v) (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) {C ρ : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 → ChartTransport.JetBound (chart j τ) (P₀ + N) C ρ)
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ChartTransport.JetBound (label j τ) r C ρ)
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r) (x : Vec 2)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 → c⁻¹ * τ ∈ Set.Icc (tlo j) (thi j))
    (hwindow : ∀ j ∈ kset, ϖ j τ ≠ 0 → tlo j ≤ thi j)
    (data : ∀ (j : ℤ) (hj : j ∈ kset) (hwj : ϖ j τ ≠ 0), ∀ hh ≤ H, ∀ n ≤ N,
      AmbientLiftCoefficientData (par j) (tlo j) (thi j) (hwindow j hj hwj)
        lam n P₀ Q (Cc j hh n) (M hh))
    (hzero : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N →
      ∀ α : DerivativeWord2 0, ∀ X z v u, Cc j hh n 0 α (c⁻¹ * τ) X z v u = 0)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (v : ι) :
    rs ^ r * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c ρ e εc N H (positiveLiftCoefficients Cc)
        chart label a τ Y v) x‖ ≤
      εc * (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖) := by
  classical
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hreg : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞)
      (fun Y => pulsePhysicalLift c ρ e εc N H (positiveLiftCoefficients Cc j)
        (chart j) (label j) a τ Y v) := by
    intro j hj hwj
    rw [pulsePhysicalLift_freeze_time, hclock]
    apply pulsePhysicalLift_static_contDiff_of_boxes c ρ e εc N H r
      (positiveLiftCoefficients Cc j) (chart j τ) (label j τ) (a τ) τ
      (ha.of_le (by exact_mod_cast Nat.add_le_add_right hrP N))
      ((hchart j hj hwj).of_le (by exact_mod_cast Nat.add_le_add_right hrP N)) (hlabel j hj hwj)
    intro hh hhh n hn m hm α v' u'
    by_cases hn0 : n = 0
    · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
      exact IsBoxSmooth.zero
    · simp only [positiveLiftCoefficients, hn0, ite_false]
      exact ((data j hj hwj hh hhh n hn).mono hrP hrQ).box m hm α v' u' _ (ht j hj hwj)
  have hB : 0 ≤
      εc * (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            ρ ^ j * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖) := by
    apply mul_nonneg (mul_nonneg hεc
      (Finset.sum_nonneg fun n _ => nativeChartTransportConstant_nonneg hC _ _ _))
    apply Finset.sum_nonneg
    intro u _
    exact mul_nonneg
      (Finset.sum_nonneg fun hh hhh => hM hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) v u)
      (Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (pow_nonneg (hrs.trans_le (hrse.trans heρ)).le _) (norm_nonneg _))
  apply gluedLift_spatial_word_norm_le kset ϖ c ρ e εc N H (positiveLiftCoefficients Cc)
    chart label a τ v hw hs hreg hrs.le hB β x
  intro j hj hwj
  rw [pulsePhysicalLift_freeze_time, hclock]
  exact positive_pulse_fixed_matrix_word_bound_of_data (positiveLiftCoefficients Cc j) M hM
    (fun hh hhh n hn1 hn => by
      have hn0 : n ≠ 0 := by omega
      simpa only [positiveLiftCoefficients, hn0, ite_false] using data j hj hwj hh hhh n hn)
    hlam hlam1 r hrP hrQ (a τ) ha (chart j τ) (hchart j hj hwj) hC (hJ j hj hwj) hrs hrse heρ
    (label j τ) (hlabel j hj hwj) (hJlabel j hj hwj) β x (hinv j hj hwj) c εc τ hεc hεc1
    (ht j hj hwj)
    (fun hh _ => by simp only [positiveLiftCoefficients, ite_true])
    (fun hh hhh n hn1 hn α X z v' u' => by
      have hn0 : n ≠ 0 := by omega
      simpa only [positiveLiftCoefficients, hn0, ite_false] using
        hzero j hj hwj hh hhh n hn1 hn α X z v' u') v

end General

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- The positive part of the glued native lift of a stage, with the fixed native matrix. -/
theorem nativeStageLiftFamily_positive_glued_word_bound
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ (r : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) r C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (β : DerivativeWord2 r) (x : Vec 2)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → chart j τ (label j τ x) = x)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    rs ^ r * ‖orderedDerivative β (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H
        (positiveLiftCoefficients (nativeStageLiftFamily slotLifts))
        chart label a τ Y v) x‖ ≤
      εc * (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
        (∑ u, (∑ hh ∈ Finset.range (H + 1),
          nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
          ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            (liftLength D G.level) ^ j * ‖iteratedFDeriv ℝ j (fun X => a τ X u) x‖) := by
  classical
  refine positive_glued_word_bound_of_data (par := fun j => EntryWeakProofs.pulseParallel j)
    (nativeStageLiftFamily slotLifts)
    (fun hh v u => nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u)
    (fun hh hhh v u => (nativeSlotLift_uniform_coefficient_data
      (slotLifts ⟨1, by decide⟩) P₀ (hreserve _) hh hhh 0 (Nat.zero_le N)).nonneg v u)
    kset r hrP hrQ ϖ c εc τ hc hεc hεc1 a ha chart label hC hchart hJ
    hrs hrse heρ hlabel hJlabel hw hs β x hinv ht
    (fun j hj _ => (slotLifts ⟨j, hodd j hj⟩).setting.window) ?_ ?_
    (div_nonneg (slotLifts ⟨1, by decide⟩).setting.ρ_pos.le
      (slotLifts ⟨1, by decide⟩).setting.E_pos.le) (slotLifts ⟨1, by decide⟩).setting.lam_le v
  · intro j hj hwj hh hhh n hn
    simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
    exact (nativeSlotLift_uniform_coefficient_data
      (slotLifts ⟨j, hodd j hj⟩) P₀ (hreserve _) hh hhh n hn).mono
      (show P₀ ≤ ambientDegreeSlowReserve P₀ (N + (slotLifts ⟨j, hodd j hj⟩).cap) n by
        unfold ambientDegreeSlowReserve; omega)
      (show max k (L + 2) ≤ ambientDegreeFastReserve (max k (L + 2))
          (slotLifts ⟨j, hodd j hj⟩).cap H (N + (slotLifts ⟨j, hodd j hj⟩).cap) hh n by
        unfold ambientDegreeFastReserve; omega)
  · intro j hj hwj hh hhh n hn1 _hn α X z v' u'
    simp only [nativeStageLiftFamily, dite_eq_left (hodd j hj)]
    exact nativeSlotLift_zero_order_eq_zero (slotLifts ⟨j, hodd j hj⟩) hh hhh n hn1 α _
      (ht j hj hwj) X z v' u'

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **The five profile fields: regularity and the split**.

At one time `t`, from `aU t`, `aY t` of class `C^{K+N+2p+2}` and periodic, and the regularity of the
lift as one hypothesis (`regularLift_contDiff_periodic`, supplied by the assembly):

* `regularProfiles_regular`: each of the five fields of `passageProfiles` is `C^K` and periodic
  (the kernel keeps the order, `P_p` consumes `2p`, the readout is constant, the lift consumes `N`
  and keeps `K + 2`);
* `regularProfiles_split`: the five fields sum to `F(aU) - 𝖱F'(aY)`.

Special cases: `p = 0`; `aY t = 0`; an empty family. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.IterationPassage.Passage

section Normalized

theorem regularCompField_contDiff {S : Finset Comp} (π : CompIn S → ℝ)
    {b : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root} {n : ℕ} (hb : ContDiff ℝ (n : ℕ∞) b) :
    ContDiff ℝ (n : ℕ∞) (compField π b) := by
  have h : compField π b = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn S => ℝ)).symm ∘
      (fun x v => (Real.sqrt (π v))⁻¹ * b x v) := rfl
  rw [h]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn S => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr fun v => contDiff_const.mul (contDiff_pi.mp hb v))

theorem regularCompField_periodic {S : Finset Comp} (π : CompIn S → ℝ)
    {b : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root} (hb : IsZ2Periodic b) :
    IsZ2Periodic (compField π b) := by
  intro n x
  simp only [compField, hb n x]

theorem regular_periodic_sub {β : Type*} [AddCommGroup β] {f g : Vec 2 → β}
    (hf : IsZ2Periodic f) (hg : IsZ2Periodic g) : IsZ2Periodic (f - g) := by
  intro n x
  simp only [Pi.sub_apply, hf n x, hg n x]

end Normalized

section Regular

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `𝖱 (P_p X - X)` is `C^K` and periodic for a `C^{K+N+2p+2}` periodic slice. -/
theorem regularFields_RPX (D : OCData) (m p K N : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (X : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ)
    (hX : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (X t)) (hp : IsZ2Periodic (X t)) :
    ContDiff ℝ (K : ℕ∞) (fieldReadout (S := S) m E η₀ (fieldCov D m p X - X) t) ∧
      IsZ2Periodic (fieldReadout (S := S) m E η₀ (fieldCov D m p X - X) t) := by
  have hX' : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) (X t) :=
    hX.of_le (by exact_mod_cast (by omega : K + 2 * p ≤ K + N + 2 * p + 2))
  have hX2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (X t) :=
    hX.of_le (by exact_mod_cast (by omega : 2 * p ≤ K + N + 2 * p + 2))
  have hc : ContDiff ℝ (K : ℕ∞) ((fieldCov D m p X - X) t) :=
    (regularCov_contDiff (covPrimitive D m t) p K hX').sub
      (hX.of_le (by exact_mod_cast (by omega : K ≤ K + N + 2 * p + 2)))
  have hcp : IsZ2Periodic ((fieldCov D m p X - X) t) :=
    regular_periodic_sub (regularCov_periodic (covPrimitive D m t) p hX2 hp) hp
  exact ⟨regularReadout_contDiff m E η₀ _ t hc, regularReadout_periodic m E η₀ _ t hcp⟩

/-- The slice `P_p 𝖱 X` is `C^{K+2+N}` and periodic. -/
theorem regularFields_PRX (D : OCData) (m p K N : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (X : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ)
    (hX : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (X t)) (hp : IsZ2Periodic (X t)) :
    ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (fieldCov D m p (fieldReadout (S := S) m E η₀ X) t) ∧
      IsZ2Periodic (fieldCov D m p (fieldReadout (S := S) m E η₀ X) t) := by
  have hR : ContDiff ℝ ((K + 2 + N + 2 * p : ℕ) : ℕ∞) (fieldReadout (S := S) m E η₀ X t) :=
    regularReadout_contDiff m E η₀ X t
      (hX.of_le (by exact_mod_cast (by omega : K + 2 + N + 2 * p ≤ K + N + 2 * p + 2)))
  have hRp : IsZ2Periodic (fieldReadout (S := S) m E η₀ X t) := regularReadout_periodic m E η₀ X t hp
  exact ⟨regularCov_contDiff (covPrimitive D m t) p (K + 2 + N) hR,
    regularCov_periodic (covPrimitive D m t) p
      (hR.of_le (by exact_mod_cast (by omega : 2 * p ≤ K + 2 + N + 2 * p))) hRp⟩

/-- `T P_p 𝖱 X - P_p 𝖱 X` is `C^K` and periodic, given the regularity of the lift. -/
theorem regularFields_TPRX (D : OCData) (m p K N depth : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn S) (fun v => ScalarH v.1.root))
    (X : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ)
    (hX : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (X t)) (hp : IsZ2Periodic (X t))
    (hT : ∀ a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root,
      ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (a t) → IsZ2Periodic (a t) →
      ContDiff ℝ (K : ℕ∞) (passageLift D m N depth CcT a t) ∧
        IsZ2Periodic (passageLift D m N depth CcT a t)) :
    ContDiff ℝ (K : ℕ∞) (((passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout (S := S) m E η₀ X)) : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) -
        fieldCov D m p (fieldReadout (S := S) m E η₀ X)) t) ∧
      IsZ2Periodic (((passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout (S := S) m E η₀ X)) : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) -
        fieldCov D m p (fieldReadout (S := S) m E η₀ X)) t) := by
  obtain ⟨hP, hPp⟩ := regularFields_PRX D m p K N E η₀ X t hX hp
  obtain ⟨h1, h2⟩ := hT _ hP hPp
  exact ⟨h1.sub (hP.of_le (by exact_mod_cast (by omega : K ≤ K + 2 + N))),
    regular_periodic_sub h2 hPp⟩

/-- `U - T P_p 𝖱 X` is `C^K` and periodic. -/
theorem regularFields_UTPRX (D : OCData) (m p K N depth : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn S) (fun v => ScalarH v.1.root))
    (U : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (X : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ)
    (hU : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (U t)) (hUp : IsZ2Periodic (U t))
    (hX : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (X t)) (hp : IsZ2Periodic (X t))
    (hT : ∀ a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root,
      ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (a t) → IsZ2Periodic (a t) →
      ContDiff ℝ (K : ℕ∞) (passageLift D m N depth CcT a t) ∧
        IsZ2Periodic (passageLift D m N depth CcT a t)) :
    ContDiff ℝ (K : ℕ∞) ((U - passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout (S := S) m E η₀ X))) t) ∧
      IsZ2Periodic ((U - passageLift D m N depth CcT (fieldCov D m p (fieldReadout (S := S) m E η₀ X))) t) := by
  obtain ⟨hP, hPp⟩ := regularFields_PRX D m p K N E η₀ X t hX hp
  obtain ⟨h1, h2⟩ := hT _ hP hPp
  exact ⟨(hU.of_le (by exact_mod_cast (by omega : K ≤ K + N + 2 * p + 2))).sub h1,
    regular_periodic_sub hUp h2⟩

/-- **The five profile fields are `C^K` and periodic.** -/
theorem regularProfiles_regular {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth K : ℕ) (η₀ : ℝ)
    (Sr : KernelSpec) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ)
    (haU : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aU t)) (haUp : IsZ2Periodic (aU t))
    (haY : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (aY t)) (haYp : IsZ2Periodic (aY t))
    (hT : ∀ a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root,
      ContDiff ℝ ((K + 2 + N : ℕ) : ℕ∞) (a t) → IsZ2Periodic (a t) →
      ContDiff ℝ (K : ℕ∞) (passageLift D m N depth CcT a t) ∧
        IsZ2Periodic (passageLift D m N depth CcT a t)) :
    ProfilesRegular D law G Gr m p N depth K η₀ φ₀ Sr CcT aU aY t := by
  have hS : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) (fieldKernel φ₀ Sr aY t) ∧
      IsZ2Periodic (fieldKernel φ₀ Sr aY t) :=
    regularKernel_contDiff_periodic hφs hφsupp Sr t haY haYp
  have hDY : ContDiff ℝ ((K + N + 2 * p + 2 : ℕ) : ℕ∞) ((aY - fieldKernel φ₀ Sr aY) t) ∧
      IsZ2Periodic ((aY - fieldKernel φ₀ Sr aY) t) :=
    ⟨haY.sub hS.1, regular_periodic_sub haYp hS.2⟩
  intro q hq
  simp only [passageProfiles, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := regularFields_RPX D m p K N (D.eps (m - 1)) η₀ (fieldKernel φ₀ Sr aY) t hS.1 hS.2
    exact ⟨regularCompField_contDiff _ h1, regularCompField_periodic _ h2⟩
  · obtain ⟨h1, h2⟩ := regularFields_TPRX D m p K N depth (D.eps (m - 1)) η₀ CcT
      (fieldKernel φ₀ Sr aY) t hS.1 hS.2 hT
    exact ⟨regularCompField_contDiff _ h1, regularCompField_periodic _ h2⟩
  · obtain ⟨h1, h2⟩ := regularFields_RPX D m p K N (D.eps (m - 1)) η₀ (aY - fieldKernel φ₀ Sr aY) t
      hDY.1 hDY.2
    exact ⟨regularCompField_contDiff _ h1, regularCompField_periodic _ h2⟩
  · obtain ⟨h1, h2⟩ := regularFields_TPRX D m p K N depth (D.eps (m - 1)) η₀ CcT
      (aY - fieldKernel φ₀ Sr aY) t hDY.1 hDY.2 hT
    exact ⟨regularCompField_contDiff _ h1, regularCompField_periodic _ h2⟩
  · obtain ⟨h1, h2⟩ := regularFields_UTPRX D m p K N depth (D.eps (m - 1)) η₀ CcT aU aY t haU haUp
      haY haYp hT
    exact ⟨regularCompField_contDiff _ h1, regularCompField_periodic _ h2⟩

/-- **The exact split**: the five profiles sum to `F(aU) - 𝖱F'(aY)`. -/
theorem regularProfiles_split {φ₀ : Vec 2 → ℝ}
    (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth : ℕ) (η₀ : ℝ)
    (Sr : KernelSpec) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ)
    (hc : D.cellScaleSq m ≠ 0) (hπ' : ∀ v, 0 < Gr.mass law v)
    (haY : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) (aY t))
    (hS : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) (fieldKernel φ₀ Sr aY t)) :
    ProfilesSplit D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t := by
  classical
  intro x
  simp only [passageProfiles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    compField]
  generalize fieldKernel φ₀ Sr aY = sY at hS ⊢
  have hS2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (sY t) :=
    hS.of_le (by exact_mod_cast (by omega : 2 * p ≤ N + 2 * p))
  have hD : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) ((aY - sY) t) := haY.sub hS
  have hRs : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞) (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY t) :=
    regularReadout_contDiff m _ η₀ sY t hS
  have hRd : ContDiff ℝ ((N + 2 * p : ℕ) : ℕ∞)
      (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY) t) :=
    regularReadout_contDiff m _ η₀ (aY - sY) t hD
  have h2s : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY t) :=
    hRs.of_le (by exact_mod_cast (by omega : 2 * p ≤ N + 2 * p))
  have h2d : ContDiff ℝ ((2 * p : ℕ) : ℕ∞)
      (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY) t) :=
    hRd.of_le (by exact_mod_cast (by omega : 2 * p ≤ N + 2 * p))
  have hD2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) ((aY - sY) t) :=
    hD.of_le (by exact_mod_cast (by omega : 2 * p ≤ N + 2 * p))
  have c1 : regularReadoutFull (S := G.comps) m (D.eps (m - 1)) η₀ (fieldCov D m p sY t x) =
      fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY) t x := by
    rw [← fieldReadout_eq_full]
    exact regularReadout_cov_comm D m p _ η₀ sY t hS2 x
  have c2 : regularReadoutFull (S := G.comps) m (D.eps (m - 1)) η₀ (fieldCov D m p (aY - sY) t x) =
      fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY)) t x := by
    rw [← fieldReadout_eq_full]
    exact regularReadout_cov_comm D m p _ η₀ (aY - sY) t hD2 x
  have e : fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ aY) t =
      fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY) t +
        fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY)) t := by
    change covPolyP (covPrimitive D m t) p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ aY t) =
      covPolyP (covPrimitive D m t) p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY t) +
        covPolyP (covPrimitive D m t) p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY) t)
    rw [← regularCov_add _ p h2s h2d]
    congr 1
    funext y
    simp only [Pi.add_apply, fieldReadout_eq_full, Pi.sub_apply, map_sub]
    abel
  have hA1 : ContDiff ℝ (N : ℕ∞) (fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY) t) :=
    regularCov_contDiff (covPrimitive D m t) p N hRs
  have hA2 : ContDiff ℝ (N : ℕ∞)
      (fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY)) t) :=
    regularCov_contDiff (covPrimitive D m t) p N hRd
  have c3 : passageLift D m N depth CcT (fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ aY)) t x =
      passageLift D m N depth CcT (fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY)) t x +
        passageLift D m N depth CcT
          (fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY))) t x := by
    have hcong := regularLift_congr_time (D := D) m N depth CcT hc
      (a := fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ aY))
      (a' := fun s y => fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ sY) s y +
        fieldCov D m p (fieldReadout (S := G.comps) m (D.eps (m - 1)) η₀ (aY - sY)) s y) (t := t) e
    rw [congrFun hcong x]
    exact regularLift_add (D := D) m N depth CcT hc hA1 hA2 x
  rw [regularReadout_normalized m _ η₀ _ _ hπ']
  rw [← toCompSpace_sub]
  simp only [← toCompSpace_add]
  congr 1
  simp only [fieldReadout_eq_full, Pi.sub_apply, map_sub]
  rw [c1, c2, c3]
  abel

end Regular

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The covariance correction in the profile norm**:
`discDE : DiscDEStatement`.

For each component the readout carrier `Z_v` of order `K+2+2p` has the classical representative
`(𝖱 f)_v`; the covariance carrier `W_v` of `P_p` and `W_v - Z_v|_{K+2}` represents
`P_p(𝖱f)_v - (𝖱f)_v` (`discCoarse_carrier`), of norm at most `p μ |Z_v|` (`disc_cov_difference_le`).
Then `|Z|_{ρ;π} <= ‖readoutCLM‖ |w|_{ρ;π'}` (`discCoarse_readout_weightedNorm_le`) and
`sobolevProfile` converts the carrier norm to the profile.

Special cases: `p = 0` (zero correction); `w = 0`; `μ = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage
open AVRegularity.Construction.Preservation.FullLift CycleComparison.Coarse

/-- Scalar carrier of the covariance correction. -/
theorem discCoarse_carrier {ρ μ : ℝ} {p K : ℕ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hsym : ∀ i j, Hc i j = Hc j i) (hM : fbCovConst ρ Hc (K + 2 + 2 * p) ≤ μ) (hμ1 : μ ≤ 1)
    (Z : TorusHk (K + 2 + 2 * p) ℝ) (u : Vec 2 → ℝ) (hZ : IsClassicalRep Z u (K + 2 + 2 * p)) :
    ∃ X : TorusHk (K + 2) ℝ, IsClassicalRep X (fun x => covPolyP Hc p u x - u x) (K + 2) ∧
      Real.sqrt (factorialNormSq ρ X.val) ≤ p * μ * Real.sqrt (factorialNormSq ρ Z.val) := by
  obtain ⟨W, hI, hWrep⟩ := covPolyP_carrier_exists Hc hsym p (K + 2) Z u hZ
  refine ⟨W - truncateTorusHk (Nat.le_add_right (K + 2) (2 * p)) Z, ?_,
    disc_cov_difference_le hρ Hc hM hμ1 Z W hI⟩
  exact CycleComparison.Reconstruction.isClassicalRep_sub hWrep
    (classicalRep_truncate _ le_rfl Z u (classicalRep_order_mono Z u hZ (by omega)))

theorem discCoarse_weightedNorm_le_of_sqrt {S : Finset Comp} (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (ρ c : ℝ) (hc : 0 ≤ c) {k l : ℕ}
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (Z : ∀ v : CompIn S, TorusHk l (ScalarH v.1.root))
    (h : ∀ v, Real.sqrt (factorialNormSq ρ (X v).val) ≤ c * Real.sqrt (factorialNormSq ρ (Z v).val)) :
    weightedNorm ρ π (fun _ => 1) X ≤ c * weightedNorm ρ π (fun _ => 1) Z := by
  have key : weightedNorm ρ π (fun _ => 1) X ^ 2 ≤
      (c * weightedNorm ρ π (fun _ => 1) Z) ^ 2 := by
    rw [mul_pow, discCoarse_weightedNorm_sq π hπ, discCoarse_weightedNorm_sq π hπ, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 : factorialNormSq ρ (X v).val ≤ c ^ 2 * factorialNormSq ρ (Z v).val := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) (h v) 2
      rwa [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
        Real.sq_sqrt (factorialNormSq_nonneg _ _)] at this
    calc (π v)⁻¹ * factorialNormSq ρ (X v).val ≤ (π v)⁻¹ * (c ^ 2 * factorialNormSq ρ (Z v).val) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hπ v).le)
      _ = _ := by ring
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).1 key

theorem discCoarse_field_eq {S S' : Finset Comp} (Hc : Matrix (Fin 2) (Fin 2) ℝ) (m p : ℕ)
    (E η₀ t : ℝ) (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) (x : Vec 2) (v : CompIn S) :
    fieldReadout (S := S) m E η₀ (fun _ x => covPolyP Hc p f x - f x) t x v =
      covPolyP Hc p (fun y => regularReadoutFull (S := S) m E η₀ (f y) v) x -
        regularReadoutFull (S := S) m E η₀ (f x) v := by
  rw [fieldReadout_eq_full]
  let Ψ : (∀ v' : CompIn S', ScalarH v'.1.root) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj v).comp (regularReadoutFull (S := S) m E η₀)
  have h := ErrorJets.liftId_covPolyP_clm Hc Ψ p f hf x
  change (regularReadoutFull (S := S) m E η₀ (covPolyP Hc p f x - f x)) v = _
  rw [map_sub]
  exact congrArg₂ (· - ·) h rfl

theorem discCoarse_compField_facts {S : Finset Comp} (π : CompIn S → ℝ) {K : ℕ}
    (X : ∀ v : CompIn S, TorusHk (K + 2) (ScalarH v.1.root))
    (g : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (hX : ∀ v, IsClassicalRep (X v) (fun x => g x v) (K + 2)) :
    ContDiff ℝ (K : ℕ∞) (compField π g) ∧ IsZ2Periodic (compField π g) ∧
      ∀ v, (X v).toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict unitCube]
        fun x => g x v := by
  have hKK : ((K : ℕ∞) : WithTop ℕ∞) ≤ (((K + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_add_right K 2
  refine ⟨discCoarse_contDiff_compField π g fun v => (hX v).2.1.of_le hKK, ?_,
    fun v => classicalRep_value_ae (X v) _ (hX v)⟩
  intro n x
  have : g (x + latticeShift n) = g x := funext fun v => (hX v).2.2.1 n x
  simp only [compField, this]

theorem discCoarse_g_eq {S S' : Finset Comp} (Hc : Matrix (Fin 2) (Fin 2) ℝ) (m p : ℕ)
    (E η₀ t : ℝ) (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) :
    fieldReadout (S := S) m E η₀ (fun _ x => covPolyP Hc p f x - f x) t =
      fun x v => covPolyP Hc p (fun y => regularReadoutFull (S := S) m E η₀ (f y) v) x -
        regularReadoutFull (S := S) m E η₀ (f x) v := by
  funext x v
  exact discCoarse_field_eq Hc m p E η₀ t f hf x v

theorem discCoarse_weightedNorm_nonneg {S : Finset Comp} (π : CompIn S → ℝ) (ρ : ℝ) {k : ℕ}
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) : 0 ≤ weightedNorm ρ π (fun _ => 1) X :=
  Real.sqrt_nonneg _

theorem discCoarse_final_arith {CK T a b c p μ : ℝ} (hCK : 0 ≤ CK) (hT : 0 ≤ T)
    (h : a ≤ p * μ * (c * b)) : CK * T * a ≤ CK * p * c * μ * T * b := by
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hCK hT)
  linarith [this, show CK * T * (p * μ * (c * b)) = CK * p * c * μ * T * b by ring]

/-- The carrier family of the correction and its two norm bounds. -/
theorem discCoarse_family {S S' : Finset Comp} (D : OCData) (m : ℕ) (K p : ℕ)
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ : ∀ v, 0 < π v) (hπ' : ∀ v, 0 < π' v)
    (E η₀ ρ μ t Cn : ℝ) (hρ : 0 < ρ) (hCn : ‖readoutCLM m E η₀ π π'‖ ≤ Cn)
    (hsym : ∀ i j, covPrimitive D m t i j = covPrimitive D m t j i)
    (hM : CycleComparison.Coarse.fbCovConst ρ (covPrimitive D m t) (K + 2 + 2 * p) ≤ μ)
    (hμ1 : μ ≤ 1)
    (w : ∀ v : CompIn S', TorusHk (K + 2 + 2 * p) (ScalarH v.1.root))
    (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (hw : ∀ v, IsClassicalRep (w v) (fun x => f x v) (K + 2 + 2 * p)) :
    ∃ X : ∀ v : CompIn S, TorusHk (K + 2) (ScalarH v.1.root),
      (∀ v, IsClassicalRep (X v) (fun x => covPolyP (covPrimitive D m t) p
          (fun y => regularReadoutFull (S := S) m E η₀ (f y) v) x -
            regularReadoutFull (S := S) m E η₀ (f x) v) (K + 2)) ∧
      weightedNorm ρ π (fun _ => 1) X ≤
        p * μ * (max Cn 0 * weightedNorm ρ π' (fun _ => 1) w) := by
  have hμ0 : 0 ≤ μ := (fbCovConst_nonneg hρ _ _).trans hM
  let Z := succReadout (S := S) m E η₀ (K + 2 + 2 * p) w
  have hZ : ∀ v, IsClassicalRep (Z v)
      (fun x => regularReadoutFull (S := S) m E η₀ (f x) v) (K + 2 + 2 * p) := fun v =>
    discCoarse_succReadout_rep m E η₀ w f hw v
  choose X hXrep hXb using fun v => discCoarse_carrier hρ (covPrimitive D m t) hsym hM hμ1
    (Z v) (fun x => regularReadoutFull (S := S) m E η₀ (f x) v) (hZ v)
  refine ⟨X, hXrep, ?_⟩
  have h2 := discCoarse_weightedNorm_le_of_sqrt π hπ ρ (p * μ)
    (mul_nonneg (Nat.cast_nonneg _) hμ0) X Z hXb
  have h3 := discCoarse_readout_weightedNorm_le m E η₀ π π' hπ hπ' ρ w f hw
  have hn := discCoarse_weightedNorm_nonneg π' ρ w
  have h3' : weightedNorm ρ π (fun _ => 1) Z ≤ max Cn 0 * weightedNorm ρ π' (fun _ => 1) w :=
    h3.trans (mul_le_mul_of_nonneg_right (hCn.trans (le_max_left _ _)) hn)
  exact h2.trans (mul_le_mul_of_nonneg_left h3' (mul_nonneg (Nat.cast_nonneg _) hμ0))

/-- **`D_E`: the covariance correction of the readout in the profile norm.** -/
theorem discDE : DiscDEStatement := by
  intro K p Cn
  obtain ⟨CK, hCK0, hCK⟩ := sobolevProfile K
  refine ⟨CK * p * max Cn 0, mul_nonneg (mul_nonneg hCK0 (Nat.cast_nonneg _)) (le_max_right _ _),
    ?_⟩
  intro D m S S' π π' hπ hπ' E η₀ s ρ μ t hρ hρ1 hE hCn hsym hM hμ1 w f hw
  have hf : ContDiff ℝ ((K + 2 + 2 * p : ℕ) : ℕ∞) f := contDiff_pi.2 fun v => (hw v).2.1
  have hf2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f :=
    hf.of_le (by exact_mod_cast (show 2 * p ≤ K + 2 + 2 * p by omega))
  rw [discCoarse_g_eq (covPrimitive D m t) m p E η₀ t f hf2]
  obtain ⟨X, hXrep, hXb⟩ := discCoarse_family D m K p π π' hπ hπ' E η₀ ρ μ t Cn hρ hCn hsym hM hμ1
    w f hw
  obtain ⟨hC, hper, hX⟩ := discCoarse_compField_facts π X _ hXrep
  have h1 := hCK π hπ ρ E s hρ hρ1 hE X _ hC hper hX
  have hT : 0 ≤ ∑ j ∈ Finset.range (K + 1), E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg hE.le _) (Real.rpow_nonneg hρ.le _)
  exact h1.trans (ENNReal.ofReal_le_ofReal (discCoarse_final_arith hCK0 hT hXb))

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The fresh kernel of a passage: admissibility and commutation with normalized coordinates**

* (a) `retCov_fresh_admissible`: for `m₀ ≤ m ≤ D.term` the fresh kernel `S` born at `m - 1`
  (`IsFreshKernel`) is `S.IsAdmissible Γ L` for every `L` with `L + 1 ≤ 2 nk`, with `Γ ≥ 2` chosen
  before the level, and `0 < S.width` when `0 < cr`.
* (c) `retCov_kernel_clm_comm`, `retCov_compField_kernel`: the paired kernel average commutes with
  a continuous linear map, in particular with the normalization `toCompSpace`;
  `retCov_compField_readout`, `retCov_compField_cov`: the same for `𝖱` and `𝒫_p`.

Special cases: `L = 0`; the zero field. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Providers AVRegularity.Providers.KernelSup
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.IterationPassage.Passage

/-- **(a) Admissibility of the fresh kernel.** -/
theorem retCov_fresh_admissible (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ Γ : ℝ, 2 ≤ Γ ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (cr σ₀ : ℝ), 0 < cr → ∀ (nk : ℕ+) (L : ℕ), L + 1 ≤ 2 * (nk : ℕ) →
    ∀ m : ℕ, m₀ ≤ m → m ≤ D.term → ∀ S : KernelSpec, IsFreshKernel D cr σ₀ nk (m - 1) S →
      S.IsAdmissible Γ L ∧ 0 < S.width := by
  obtain ⟨Λ₀, hΛ₀, haxes⟩ := uniform_fresh_axes_norm_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  obtain ⟨Γ, _hΓ, ma, hma, haxes⟩ := haxes Λ hΛ
  obtain ⟨mi, _hmi, hinv⟩ := uniform_fresh_spanning_inverse_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128
  refine ⟨max Γ 2, le_max_right _ _, max ma mi, by omega, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq hband cr σ₀ hcr nk L hL m hm hmt S hS
  have hm2 : 2 ≤ m := by omega
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hupper := haxes D hDα hDq hDΛ hDζ hseq hband (m - 1) (by omega) (by omega) S hS.2.2
  have hinverse := hinv D hDα hDq hDΛ hDζ hseq hband (m - 1) (by omega) (by omega) S hS.2.2
  have hmeas := fresh_axes_measurable D (m - 1) hΛD S.H₁ S.H₂ hS.2.2
  refine ⟨⟨hmeas.1, hmeas.2, ?_, ?_⟩, ?_⟩
  · intro t
    exact ⟨(hupper t).1.trans (le_max_left _ _), (hupper t).2.trans (le_max_left _ _),
      (hinverse t).1, (hinverse t).2.trans (le_max_right _ _)⟩
  · rw [hS.2.1]; exact hL
  · rw [hS.1]
    have hκ := CycleReference.bandChain_pos hΛD hζD hband (by omega : m - 1 ≤ D.term)
    have hτ : 0 < ocTauPP D.α D.q D.Λ (m - 1 + 1) := Construction.Stream.ocTauPP_pos hΛD
    have hε : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos hΛD
    unfold freshWidth freshLength
    exact mul_pos (mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hκ hτ))) (Real.rpow_pos_of_pos hε _)

/-- **(c)** The paired kernel average commutes with a continuous linear map. -/
theorem retCov_kernel_clm_comm {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (S : KernelSpec) (t : ℝ)
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {f : Vec 2 → E} (hf : Continuous f) (hp : IsZ2Periodic f) (y : Vec 2) :
    T (S.applyClassical φ₀ t f y) = S.applyClassical φ₀ t (fun x => T (f x)) y := by
  have hφc := hasCompactSupport_of_unitBall hφsupp
  have hkK : IsKer (tensorKer (momentKernel φ₀ S.order)) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs S.order) (hasCompactSupport_momentKernel hφc S.order)
  obtain ⟨B, hB⟩ := bdd_of_periodic hf hp
  have hTf : Continuous fun x => T (f x) := T.continuous.comp hf
  have hB' : ∀ y, ‖T (f y)‖ ≤ ‖T‖ * B := fun y =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _))
  rw [applyClassical_eq_op S _ rfl hkK t hf hB, applyClassical_eq_op S _ rfl hkK t hTf hB']
  unfold Op
  have hint := integrable_op (μ := (volume : Measure (Vec 2 × Vec 2))) hkK
    (kerMap S.width (S.H₁ t) (S.H₂ t)) hf hB y
  rw [← T.integral_comp_comm hint]
  congr 1
  funext z
  simp [map_smul]

/-- The normalization `toCompSpace` as a continuous linear map. -/
def retCovNormCLM {S : Finset Comp} (π : CompIn S → ℝ) :
    (∀ v : CompIn S, ScalarH v.1.root) →L[ℝ] CompSpace S :=
  LinearMap.toContinuousLinearMap
    { toFun := toCompSpace π
      map_add' := fun z w => toCompSpace_add π z w
      map_smul' := fun c z => by ext v; simp [toCompSpace, mul_left_comm] }

/-- **(c)** The kernel average commutes with the normalization into `CompSpace`. -/
theorem retCov_compField_kernel {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (Sr : KernelSpec) (t : ℝ)
    {S : Finset Comp} (π : CompIn S → ℝ) {a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root}
    (ha : Continuous a) (hp : IsZ2Periodic a) :
    compField π (Sr.applyClassical φ₀ t a) =
      Sr.applyClassical φ₀ t (compField π a) := by
  funext y
  have := retCov_kernel_clm_comm hφs hφsupp Sr t (retCovNormCLM π) ha hp y
  exact this

/-- **(c)** The readout in normalized coordinates is the matrix `readoutCLM`. -/
theorem retCov_compField_readout (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ' : ∀ v', 0 < π' v')
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ) (x : Vec 2) :
    compField π (fieldReadout (S := S) m E η₀ a t) x =
      readoutCLM m E η₀ π π' (compField π' (a t) x) := by
  rw [fieldReadout_eq_full_slice]
  exact (regularReadout_normalized m E η₀ π π' hπ' (a t x)).symm

/-- **(c)** The covariance polynomial commutes with the normalization. -/
theorem retCov_compField_cov (D : OCData) (m p : ℕ) {S : Finset Comp} (π : CompIn S → ℝ)
    (a : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (a t)) :
    compField π (fieldCov D m p a t) = covPolyP (covPrimitive D m t) p (compField π (a t)) := by
  funext x
  exact ErrorJets.liftId_covPolyP_clm _ (retCovNormCLM π) p (a t) ha x

theorem retCov_rpow_split {ε δ σ : ℝ} (hε : 0 < ε) :
    ε ^ (δ - 2 * σ) * (ε ^ σ) ^ 2 = ε ^ δ := by
  rw [sq, ← Real.rpow_add hε, ← Real.rpow_add hε]
  congr 1; ring

/-- **(b), (d) The covariance and the width of the fresh kernel at a passage.** For `2 ≤ m ≤ M`,
`|H_{ij}| ≤ ε r²` with `ε = (C/c_r²) E^{δ-2σ₀}` and `r = freshWidth D c_r σ₀ (m-1)`; also
`ε ≤ C/c_r²` (when `2σ₀ ≤ δ`) and `r ≤ C E`. -/
theorem retCov_cov_scales (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
    ∀ M : ℕ, IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (cr σ₀ : ℝ), 0 < cr → cr ≤ 1 → 0 ≤ σ₀ → 2 * σ₀ ≤ ocDelta α q →
    ∀ m : ℕ, 2 ≤ m → m ≤ M →
      D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀) ≤ 1 ∧
      freshWidth D cr σ₀ (m - 1) ≤ C * D.eps (m - 1) ∧
      ∀ (t : ℝ) (i j : Fin 2), |covPrimitive D m t i j| ≤
        (C / cr ^ 2 * D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀)) * freshWidth D cr σ₀ (m - 1) ^ 2 := by
  obtain ⟨C, hC, Λ₀, hΛ₀, h⟩ := CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨C, hC, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ D hDα hDq hDΛ hDζ M hband hterm cr σ₀ hcr hcr1 hσ₀ hσδ m hm2 hmM
  have hΛ1 : 1 ≤ Λ := by omega
  have hk := (h Λ hΛ M (by omega) D.κ hband).2 m hm2 hmM (D.κ m) (D.κ (m - 1)) rfl rfl
  obtain ⟨_, _, _, _, hrh, _, _, _, _, _, _, _, _, _, _, hcov⟩ := hk
  have heps : D.eps (m - 1) = ocEpsilon q Λ (m - 1) := by
    unfold OCData.eps; rw [hDq, hDΛ]
  have hε0 : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : ocEpsilon q Λ (m - 1) ≤ 1 := ocEpsilon_le_one hΛ1 _
  have hCpos : 0 < C := by linarith
  have hκ : 0 < D.κ (m - 1) := by
    have hζD : IsFastProfile ζ := hζ
    exact CycleReference.bandChain_pos hΛ1 hζD hband (by omega)
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ1
  have hρ : 0 < ocRh α q Λ m (D.κ (m - 1)) := Real.sqrt_pos.mpr (mul_pos hκ hτ)
  have hfw : freshWidth D cr σ₀ (m - 1) =
      cr * ocRh α q Λ m (D.κ (m - 1)) * ocEpsilon q Λ (m - 1) ^ σ₀ := by
    unfold freshWidth freshLength ocRh
    rw [hDα, hDq, hDΛ, show m - 1 + 1 = m by omega, heps]
  rw [heps]
  have hδ : ocEpsilon q Λ (m - 1) ^ (ocDelta α q - 2 * σ₀) ≤ 1 :=
    Real.rpow_le_one hε0.le hε1 (by linarith)
  refine ⟨hδ, ?_, ?_⟩
  · rw [hfw]
    have h1 : ocRh α q Λ m (D.κ (m - 1)) ≤ C * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) := hrh.2
    have h2 : ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) ≤ ocEpsilon q Λ (m - 1) := by
      rw [Real.rpow_add hε0, Real.rpow_one]
      exact mul_le_of_le_one_right hε0.le (Real.rpow_le_one hε0.le hε1
        (ocC_pos_of_admissible hα₀ hq).le)
    have h3 : ocEpsilon q Λ (m - 1) ^ σ₀ ≤ 1 := Real.rpow_le_one hε0.le hε1 hσ₀
    have h4 : 0 ≤ ocEpsilon q Λ (m - 1) ^ σ₀ := Real.rpow_nonneg hε0.le _
    calc cr * ocRh α q Λ m (D.κ (m - 1)) * ocEpsilon q Λ (m - 1) ^ σ₀
        ≤ 1 * (C * ocEpsilon q Λ (m - 1)) * 1 := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hCpos.le)
      _ = _ := by ring
  · intro t i j
    have hc := (hcov 0 t i j).2.2.2
    have hcv : covPrimitive D m t = ocCovariance α q Λ ζ m (D.κ m) (D.κ (m - 1)) 0 t := by
      unfold covPrimitive; rw [hDα, hDq, hDΛ, hDζ]
    rw [hcv]
    rw [div_le_iff₀ (pow_pos hρ 2)] at hc
    rw [hfw]
    have e1 : (C / cr ^ 2 * ocEpsilon q Λ (m - 1) ^ (ocDelta α q - 2 * σ₀)) *
        (cr * ocRh α q Λ m (D.κ (m - 1)) * ocEpsilon q Λ (m - 1) ^ σ₀) ^ 2 =
        C * (ocEpsilon q Λ (m - 1) ^ (ocDelta α q - 2 * σ₀) * (ocEpsilon q Λ (m - 1) ^ σ₀) ^ 2) *
          ocRh α q Λ m (D.κ (m - 1)) ^ 2 := by
      field_simp
    rw [e1, retCov_rpow_split hε0]
    linarith

end AVRegularity.IterationPassage.Passage
end
end
end
