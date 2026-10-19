-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedLedger
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.Proofs.WeakGen.Comparison.GateInputs

section
section
/-! Statements for the word-length rows `WordLengthRowsStatement` of the frontier.

The row for length `l` is the flux of the fresh edges from the columns of length `l - 1` into
the rows of length `l`. Three pieces are separated:

* `FreshEdgeProvenanceStatement F l` (frame level): no retained column of length below `l - 1`
  has a coefficient into a row of length `l`.
* `FreshPrefixPriceStatement F l C` (frame level): the fresh edges, with all other coefficients
  set to zero, carry a Schur operator of size `C * eps^theta_l`, where `theta_l = theta1` for
  `l = 1` and `theta2` otherwise. This is the only place where the ledger gain enters.
* `WordLengthRowOfPriceStatement` (stage level, true for every frame): the two pieces above and
  time integrability of the unknown give `WordLengthRowStatement F l C`.

The first two hold at the data level only (they are false for arbitrary frames); they are
collected in `LengthFreshProductionStatement`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Assembly KernelEnergy
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The kernel operator on the columns and rows of the extended stage, as in the grade rows. -/
abbrev Frame.KernelOp (F : Frame D hr Dm bw j₀) : Type _ :=
  TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
    (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
    F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm

/-- The rows of length `l` (and grade at most `H`) of the omitted family. -/
def Frame.IsLengthRow (F : Frame D hr Dm bw j₀) (l : ℕ) (c : Comp) : Prop :=
  compGrade c ≤ F.H ∧ (compWord F.m c).length = l

/-- A fresh edge into a row of length `l`: from a retained column of length exactly `l - 1`. -/
def Frame.IsFreshEdge (F : Frame D hr Dm bw j₀) (l : ℕ) (v u : CompIn F.G'.comps) : Prop :=
  F.IsLengthRow l v.1 ∧ IsRetained F.m F.H (l - 1) u.1 ∧ (compWord F.m u.1).length = l - 1

/-- The exponent of the price of length `l`: `theta1` for `l = 1`, `theta2` after. -/
def Frame.lengthExponent (F : Frame D hr Dm bw j₀) (l : ℕ) : ℝ :=
  if l = 1 then F.θ₁ else F.θ₂

/-- The coefficients of the fresh edges into length `l`, zero elsewhere. -/
def Frame.freshCoeff (F : Frame D hr Dm bw j₀) (l : ℕ) (v u : CompIn F.G'.comps)
    (γ : F.G'.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) :=
  if F.IsFreshEdge l v u then F.G'.physCoeff v u γ d.1 else 0

/-- Actual provenance. A retained column of
length below `l - 1` has no coefficient into a row of length `l` (fresh letters add exactly
one letter). The degenerate cases are included: `l = 1` is vacuous (retained columns of length at
most `0` have length `0 = l - 1`); empty families, `k = 0`, zero data and edgeless seeds have no
such coefficient. It holds at the data level, not for an arbitrary frame. -/
def FreshEdgeProvenanceStatement (F : Frame D hr Dm bw j₀) (l : ℕ) : Prop :=
  ∀ (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u), F.IsLengthRow l v.1 →
    IsRetained F.m F.H (l - 1) u.1 → (compWord F.m u.1).length ≠ l - 1 →
      ∀ d ∈ Finset.Icc 2 Dm, F.G'.physCoeff v u γ d = 0

/-- The fresh-prefix operator at the data level: the fresh-prefix price, without provenance. There
is a kernel operator with the same regularizers `S` as the supplied higher lifts (the relation
`hy` of the grade rows), unit identification `C = id`, mass weights `mass / marker^2`, coefficients
the fresh edges into length `l` only, and Schur size at most `C * eps(m-1)^theta_l` (`theta1` for
`l = 1`, `theta2` after). The ledger gives the fresh-edge Schur size `Bt * eps^theta1`
(`fresh_diagonal_factor_le`); for `l >= 2` the exponent `theta2` is larger than `theta1`.
The degenerate cases are included: empty and singleton families (Schur size `0`), `J = 0` (only
`l = 1`), `k = 0`, the zero datum, edgeless seeds. -/
def FreshPrefixOperatorStatement (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ) : Prop :=
  ∃ P : F.KernelOp,
    P.B = F.freshCoeff l ∧
    P.C = (fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
    P.π = (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) ∧
    0 ≤ P.θ ∧ P.θ ≤ C * D.eps (F.m - 1) ^ F.lengthExponent l ∧
    ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))

/-- The price statement (the input of `length_rows_production_of_price`): actual provenance
together with the fresh-prefix operator, at the data level; it is false for an arbitrary frame. -/
def FreshPrefixPriceStatement (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ) : Prop :=
  FreshEdgeProvenanceStatement F l ∧ FreshPrefixOperatorStatement F l C

/-- Stage level, true for every frame (proved in `word_length_row_of_price`): the stage row of
length `l` from provenance, price and time integrability of the retained unknown. -/
def WordLengthRowOfPriceStatement (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ) : Prop :=
  1 ≤ l → l ≤ F.J + 1 → FreshPrefixPriceStatement F l C →
    (∀ u, MemLp (F.Yw u) 2 (volume.restrict (Set.Icc F.tp F.tf))) →
      WordLengthRowStatement F l C

/-- Data-level statements of the length rows: provenance and price at every length `1..J+1`,
under exactly the hypotheses of `FrontierAnalyticProductionDataStatement`. -/
def LengthFreshProductionDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
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
    ∀ k ≤ Kres,
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root),
      (∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
        ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
          (yom v u γ s).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
            G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ v u γ s
              ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ s).val (valueIndex2 (k + 1)))) →
    let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
      { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
        cr := kI.cr, η := succEta0 α q s,
        θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
        θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
        tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
    ∀ l : ℕ, 1 ≤ l → l ≤ J + 1 → FreshPrefixPriceStatement F l C

/-- Uniform data-level length statements (constants chosen before the stage). -/
def LengthFreshProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    LengthFreshProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! Assembly of the length-row production from the named ingredients: the stage-level row
from provenance and price, and the data-level provenance and price. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier

/-- The stage-level statement for every frame. -/
def WordLengthRowOfPriceGeneralStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ), WordLengthRowOfPriceStatement F l C

/-- The length-row production, from the stage statement and the data-level provenance and price.
The degenerate cases are included: the range of lengths is `1..J+1`, never empty; `J = 0` has only
`l = 1`. -/
theorem length_rows_production_of_ingredients {α s q : ℝ} {ζ : ℝ → ℝ}
    (hstage : WordLengthRowOfPriceGeneralStatement)
    (hdata : LengthFreshProductionStatement α s q ζ) :
    FrontierAnalyticProductionStatement α s q ζ false (fun rows _readout _source => rows) := by
  classical
  obtain ⟨Λ₀, hΛ₀, h⟩ := hdata
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, h⟩ := h Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨C, mStar, h⟩ := h CI Cw j₀ hledger hstart CQ Cpr
  refine ⟨C, mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom
  have hrows := h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  exact outside_length_rows_of_prefix_rows F C fun l hl1 hlJ =>
    hstage F l C hl1 hlJ (hrows l hl1 hlJ) hsol.2.1

end AVRegularity.Construction.Preservation.Frontier
end
end
end

section
section
/-! Zero extension of the retained unknown to the columns of length exactly `l - 1`, and the
facts about it used by the stage-level length row. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open KernelEnergy FullLift
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The retained unknown restricted to the columns of length `l - 1`, zero elsewhere. -/
def Frame.lengthUnknown (F : Frame D hr Dm bw j₀) (l : ℕ) (u : CompIn F.G'.comps) (t : ℝ) :
    TorusHk (F.k + 1) (hr u.1.root) :=
  if hu : IsRetained F.m F.H F.J u.1 ∧ (compWord F.m u.1).length = l - 1 then
    F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu.1⟩⟩ t else 0

/-- The supplied higher lifts in the columns of length `l - 1`, zero elsewhere. -/
def Frame.lengthHigher (F : Frame D hr Dm bw j₀) (l : ℕ)
    (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) (t : ℝ) :
    TorusHk (F.k + Dm - 1) (hr u.1.root) :=
  if IsRetained F.m F.H F.J u.1 ∧ (compWord F.m u.1).length = l - 1 then F.yom v u γ t else 0

theorem length_unknown_memLp (F : Frame D hr Dm bw j₀) (l : ℕ)
    (hw : ∀ u, MemLp (F.Yw u) 2 (volume.restrict (Set.Icc F.tp F.tf))) :
    ∀ u, MemLp (F.lengthUnknown l u) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
  intro u
  change MemLp (fun t => F.lengthUnknown l u t) 2 _
  by_cases hu : IsRetained F.m F.H F.J u.1 ∧ (compWord F.m u.1).length = l - 1
  · simpa only [Frame.lengthUnknown, dite_eq_left hu] using
      hw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu.1⟩⟩
  · simp only [Frame.lengthUnknown, dite_eq_right hu]
    exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero (F.k + 1) _

/-- The kernel values of the length-restricted lifts. -/
theorem length_kernel_values (F : Frame D hr Dm bw j₀) (l : ℕ) (P : F.KernelOp)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ v u γ,
      (F.lengthHigher l v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
        P.S v u γ t ((P.C v u γ).compLp
          ((F.lengthUnknown l u t).val (valueIndex2 (F.k + 1)))) := by
  apply ae_all_iff.mpr
  intro v
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro γ
  by_cases hu : IsRetained F.m F.H F.J u.1 ∧ (compWord F.m u.1).length = l - 1
  · filter_upwards [hy v u γ hu.1] with t ht
    simpa only [Frame.lengthHigher, ite_eq_left hu, Frame.lengthUnknown,
      dite_eq_left hu, hC, AVRegularity.Providers.WeakGen.Comparison.id_compLp_eq] using ht
  · filter_upwards [] with t
    simp only [Frame.lengthHigher, ite_eq_right hu, Frame.lengthUnknown,
      dite_eq_right hu, Submodule.coe_zero, WithLp.ofLp_zero, Pi.zero_apply]
    rw [show (P.C v u γ).compLp (0 : Lp (hr u.1.root) 2
        (volume.restrict unitCube)) = 0 from ((P.C v u γ).compLpₗ 2 (volume.restrict unitCube)).map_zero, map_zero]

/-- The restricted extension has the marked gradient square of the length-`l - 1` retained
columns. -/
theorem length_extended_gradient_mass (F : Frame D hr Dm bw j₀) (l : ℕ) (t : ℝ) :
    massGradNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
      (fun v => (F.lengthUnknown l v t).val) =
    massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
      (rhoEnh D F.cr F.m)
      (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => if (compWord F.m v.1).length = l - 1 then (F.Yw v t).val else 0) := by
  unfold massGradNormSq
  rw [finite_own_component_sum (show F.Gr.comps ⊆ F.G'.comps from Finset.filter_subset _ _) _ ?_]
  · apply Finset.sum_congr rfl
    intro v _
    have hv := (Finset.mem_filter.1 v.2).2
    by_cases hl : (compWord F.m v.1).length = l - 1
    · have hh : IsRetained F.m F.H F.J v.1 ∧ (compWord F.m v.1).length = l - 1 := ⟨hv, hl⟩
      simp only [Frame.lengthUnknown]
      rw [dite_eq_left hh, ite_eq_left hl]
      rfl
    · have hh : ¬ (IsRetained F.m F.H F.J v.1 ∧ (compWord F.m v.1).length = l - 1) :=
        fun h => hl h.2
      simp only [Frame.lengthUnknown]
      rw [dite_eq_right hh, ite_eq_right hl]
      rfl
  · intro v hv
    have hn : ¬ (IsRetained F.m F.H F.J v.1 ∧ (compWord F.m v.1).length = l - 1) := fun hh =>
      hv (Finset.mem_filter.2 ⟨v.2, hh.1⟩)
    simp only [Frame.lengthUnknown, dite_eq_right hn, Submodule.coe_zero, gradFactorialNormSq,
      WithLp.ofLp_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, mul_zero]

/-- Selecting output rows by any predicate can only decrease the mass square. -/
theorem length_selected_mass_le (F : Frame D hr Dm bw j₀) (sel : Comp → Prop)
    (hπ : ∀ v : CompIn F.G'.comps, 0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (V : ∀ v : CompIn F.G'.comps, TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    massNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
      (fun v => (if sel v.1 then V v else 0).val) ≤
    massNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (V v).val) := by
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : sel v.1
  · simp only [ite_eq_left hv, le_refl]
  · simp only [ite_eq_right hv, Submodule.coe_zero, CycleComparison.Coarse.factorialNormSq_zero_jet,
      mul_zero]
    exact mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _)

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The stage-level length row: given provenance and the fresh-prefix price, the row of length
`l` is the flux of the kernel operator on the unknown restricted to the columns of length
`l - 1`. Only the price is a hypothesis; there is no equation for the extended unknown. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open KernelEnergy AVRegularity.CoupledEnergy.Variational
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The omitted flux into the rows of length `l` is the supplied flux of the fresh-edge
operator on the restricted lifts, at every time. -/
theorem length_flux_raw (F : Frame D hr Dm bw j₀) (l : ℕ) (hlJ : l ≤ F.J + 1)
    (hprov : FreshEdgeProvenanceStatement F l) (P : F.KernelOp) (hB : P.B = F.freshCoeff l)
    (v : CompIn F.G'.comps) (hv : F.IsLengthRow l v.1) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf) :
    (gradeRowSuppliedFlux P (F.lengthHigher l) v t).toFunction.jet (valueIndex2 F.k)
      =ᵐ[volume.restrict AVenhance.unitCube]
        omittedFlux F.G' F.k (IsRetained F.m F.H (l - 1)) F.yom v t := by
  filter_upwards [grade_row_supplied_flux_raw P (F.lengthHigher l) v t ht] with x hx
  refine hx.trans ?_
  unfold omittedFlux
  apply Finset.sum_congr rfl
  intro u _
  by_cases he : F.IsFreshEdge l v u
  · have hret := he.2.1
    have hc : IsRetained F.m F.H F.J u.1 ∧ (compWord F.m u.1).length = l - 1 :=
      ⟨⟨hret.1, hret.2.trans (by omega)⟩, he.2.2⟩
    rw [ite_eq_left hret]
    apply Finset.sum_congr rfl
    intro γ _
    apply Finset.sum_congr rfl
    intro d _
    simp only [hB, Frame.freshCoeff, ite_eq_left he, Frame.lengthHigher, ite_eq_left hc]
  · calc _ = (0 : PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
          Finset.sum_eq_zero fun γ _ => Finset.sum_eq_zero fun d _ => by
            simp only [hB, Frame.freshCoeff, ite_eq_right he, zero_apply,
              Pi.zero_apply]
      _ = _ := by
          by_cases hret : IsRetained F.m F.H (l - 1) u.1
          · rw [ite_eq_left hret]
            have hlen : (compWord F.m u.1).length ≠ l - 1 := fun h => he ⟨hv, hret, h⟩
            exact (Finset.sum_eq_zero fun γ _ => Finset.sum_eq_zero fun d _ => by
              simp only [hprov v u γ hv hret hlen d.1 d.2, Pi.zero_apply,
                zero_apply]).symm
          · rw [ite_eq_right hret]

/-- The stage-level length row from provenance, price and time integrability.
The degenerate cases are included: empty and singleton families, `l = 1` (empty words), `J = 0`,
`k = 0`, zero data and edgeless seeds; no division by a norm (only by the positive diffusivity). -/
theorem word_length_row_of_price (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ) :
    WordLengthRowOfPriceStatement F l C := by
  intro hl1 hlJ hpp hw
  obtain ⟨hprov, P, hB, hC, hπ, hθ0, hθC, hy⟩ := hpp
  have hvalues := length_kernel_values F l P hC hy
  let OF : F.RowFlux := fun v t => if F.IsLengthRow l v.1 then
    gradeRowSuppliedFlux P (F.lengthHigher l) v t else 0
  have hLp : ∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
    intro v
    by_cases hv : F.IsLengthRow l v.1
    · simp only [OF, ite_eq_left hv]
      exact grade_row_supplied_flux_memLp P (F.lengthHigher l) (F.lengthUnknown l)
        (length_unknown_memLp F l hw) hvalues v
    · simp only [OF, ite_eq_right hv]
      exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero F.k _
  refine ⟨OF, ?_, hLp, ?_⟩
  · intro v t ht
    by_cases hv : F.IsLengthRow l v.1
    · have hv' : compGrade v.1 ≤ F.H ∧ (compWord F.m v.1).length = l := hv
      simp only [OF, ite_eq_left hv, ite_eq_left hv']
      exact length_flux_raw F l hlJ hprov P hB v hv t ht
    · have hv' : ¬ (compGrade v.1 ≤ F.H ∧ (compWord F.m v.1).length = l) := hv
      simp only [OF, ite_eq_right hv, ite_eq_right hv']
      filter_upwards [torusHk_toFunction_jet_ae
          (0 : TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) (valueIndex2 F.k),
        (Lp.coeFn_zero (E := PiLp 2 (fun _ : Fin 2 => hr v.1.root)) (p := 2)
          (μ := volume.restrict unitCube))] with x hx hz
      exact hx.trans hz
  · have hν : 0 < D.κ (F.m - 1) := P.diffusivity_pos
    have hmass (v : CompIn F.G'.comps) :
        0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2 := by simpa only [hπ] using P.hπ v
    have hs : (D.κ (F.m - 1) * P.θ) ^ 2 ≤
        (D.κ (F.m - 1) * (C * D.eps (F.m - 1) ^ F.lengthExponent l)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hν.le hθ0) (mul_le_mul_of_nonneg_left hθC hν.le) 2
    have hbound : ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        massNormSq (E := fun v : CompIn F.G'.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
          (K := fun _ => F.k) (rhoEnh D F.cr F.m)
          (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val) ≤
        (D.κ (F.m - 1) * (C * D.eps (F.m - 1) ^ F.lengthExponent l)) ^ 2 *
          massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
            (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
            (fun v => if (compWord F.m v.1).length = l - 1 then (F.Yw v t).val else 0) := by
      filter_upwards [hvalues, ae_restrict_mem measurableSet_Icc] with t hvt ht
      have he : ∀ v, gradeRowSuppliedFlux P (F.lengthHigher l) v t =
          P.flux t ht (fun u => F.lengthUnknown l u t) v := fun v =>
        (grade_row_supplied_flux_eq_canonical P (F.lengthHigher l) (F.lengthUnknown l) t ht hvt v).trans
          (P.carrierFlux_of_mem (F.lengthUnknown l) v t ht)
      have hselect := length_selected_mass_le F (F.IsLengthRow l) hmass
        (fun v => gradeRowSuppliedFlux P (F.lengthHigher l) v t)
      have hflux := P.flux_mass_bound t ht (fun u => F.lengthUnknown l u t)
      rw [hπ, length_extended_gradient_mass] at hflux
      have hgrad0 := massGradNormSq_nonneg
        (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
        (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
        (fun v => hmass ⟨v.1, (Finset.mem_filter.1 v.2).1⟩)
        (fun v => if (compWord F.m v.1).length = l - 1 then (F.Yw v t).val else 0)
      simp only [OF]
      simp_rw [he] at hselect ⊢
      exact hselect.trans (hflux.trans (mul_le_mul_of_nonneg_right hs hgrad0))
    have hOi := CycleComparison.Error.integrable_massNormSq
      (rhoEnh D F.cr F.m) (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) OF hLp
    let wsel : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.k + 1) (hr v.1.root) :=
      fun v t => if (compWord F.m v.1).length = l - 1 then F.Yw v t else 0
    have hwsel : ∀ v, MemLp (wsel v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
      intro v
      by_cases hl : (compWord F.m v.1).length = l - 1
      · simpa only [wsel, ite_eq_left hl] using hw v
      · simp only [wsel, ite_eq_right hl]
        exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero (F.k + 1) _
    have hWi : Integrable (fun s => massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root)
        (K := fun _ => F.k) (rhoEnh D F.cr F.m)
        (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
        (fun v => if (compWord F.m v.1).length = l - 1 then (F.Yw v s).val else 0))
        (volume.restrict (Set.Icc F.tp F.tf)) := (CycleComparison.Error.integrable_massGradNormSq
      (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2) wsel hwsel).congr
      (Filter.Eventually.of_forall fun s => by
        exact congrArg (massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root)
          (K := fun _ => F.k) (rhoEnh D F.cr F.m)
          (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)) (funext fun v => by
            by_cases hl : (compWord F.m v.1).length = l - 1
            · simp only [wsel, ite_eq_left hl]
            · simp only [wsel, ite_eq_right hl, Submodule.coe_zero]))
    have hi := integral_mono_ae hOi
      (hWi.const_mul ((D.κ (F.m - 1) * (C * D.eps (F.m - 1) ^ F.lengthExponent l)) ^ 2)) hbound
    rw [integral_const_mul] at hi
    change (D.κ (F.m - 1))⁻¹ * _ ≤ (C * D.eps (F.m - 1) ^ F.lengthExponent l) ^ 2 * _
    refine (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν.le)).trans_eq ?_
    field_simp

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The length-row production, conditional only on the fresh-prefix price. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Frontier

/-- The stage-level row is proved for every frame. -/
theorem word_length_row_of_price_general : WordLengthRowOfPriceGeneralStatement :=
  fun F l C => word_length_row_of_price F l C

/-- Length rows of the frontier, with the fresh-prefix price as the only input.
The degenerate cases are included: lengths `1..J+1`; `J = 0` has only `l = 1`; empty families,
`k = 0`, zero data. -/
theorem length_rows_production_of_price {α s q : ℝ} {ζ : ℝ → ℝ}
    (hprice : LengthFreshProductionStatement α s q ζ) :
    FrontierAnalyticProductionStatement α s q ζ false (fun rows _readout _source => rows) :=
  length_rows_production_of_ingredients word_length_row_of_price_general hprice

end AVRegularity.Construction.Preservation.Frontier
end
end
end
