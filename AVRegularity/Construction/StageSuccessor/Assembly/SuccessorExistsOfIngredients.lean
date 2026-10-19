-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Definitions.Construction.ScheduleFloor

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor

/-! Qualitative existence of a successor, independently of a cascade or a terminal entry.
The menu keeps its anchor and slow-length factor. Finite path and tag certificates are
explicit because an arbitrary natural stage need not have a finite path-depth bound. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Incoming certificates used by the qualitative construction. There is no restriction
on the covariance anchor, and no strict inequality between the level and the terminal level. -/
structure Input (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) : Prop where
  base : 1 ≤ D.Λ
  profile : IsFastProfile D.ζ
  band : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ
  bandwidth : 0 < b
  level : j₀ + 2 ≤ G.level
  top : G.level ≤ D.term
  order : 1 ≤ Dm
  cutoff : 1 ≤ Mn.N
  length_factor : 0 < Mn.lenFactor
  natural : G.IsNatural Mn.M
  tags : G.HasTags P
  context : ∃ k : InvConsts, G.IsContextCertified k
  old_births : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale
  finite_paths : ∃ H, ∀ h, StagePath G h → h ≤ H
  witness_constant : 0 ≤ P.C
  birth_weights : ∀ i, 0 ≤ P.w i
  birth_scales : ∀ i, 0 < P.eps i
  birth_length : 0 < P.Rb (G.level - 1)
  birth_width : 0 < P.rb (G.level - 1)
  cutoff_eq : P.N = Mn.N
  covariance_eq : P.p = Mn.p
  letter_orders : ∀ l ∈ Mn.A, 2 ≤ letterOrder P.N P.p l ∧ letterOrder P.N P.p l ≤ Dm

/-- One qualitative producer for both the cascade and the terminal passage.
Special cases: empty families require only natural renewal charts; a single component
still has diagonal word children; a seed is allowed whenever its supplied certificates
hold. Zero lift reserves are allowed, since the local solver produces every finite reserve.
The terminal instance takes level D.term, anchor tp and lenFactor cr, rather than the
cascade's anchor zero and factor one. -/
def StageSuccessorExistsStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    Input P Mn G → ∃ G', IsActualSuccessor D P Mn G G'
end

/-! The single field-realization leaf of qualitative successor existence. The formulas
are those in IsActualSuccessor, with the original anchor and original slot windows. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Literal transferred coefficient field, before inserting its finite edge label. -/
def sourceTransferredFlux (G : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (p : OddSlot) (c : StageCtx D b j₀ (G.level - 1) p) (s : SuccSource G)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) : Vec 2 := by
  classical
  exact if IsAdmissibleChain D b j₀ (G.level - 1) p.1
      (c.1.recenter D (D.eps (G.level - 1 - 1) • X)) then
    if s.IsDiag then
      (s.lam G.level Mn.η0 * (D.κ (G.level - 1) * D.eps (G.level - 1) ^ (d - 2))⁻¹) •
        fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
          Mn.N Mn.p Mn.anchor Cc0 t (c.1.recenter D (D.eps (G.level - 1 - 1) • X)) z) d I 0
    else transferAt D G.level p.1 (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
      (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (Cc s)) t
      (c.1.recenter D (D.eps (G.level - 1 - 1) • X)) z d I
  else 0

/-- Witnesses of the actual lift clauses with periodic, correctly supported coefficient fields.
Special cases: an empty source type leaves the field requirements vacuous, but retains the
needed diagonal lift family. The singleton case includes the diagonal child. All times,
not just the comparison window, occur in the structural successor definition. At the
smallest allowed order the support assertion still concerns precisely d above the tag. -/
def TransferFields (G : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu)
    (Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : Prop :=
  (∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)) ∧ IsDiagLifts D Dm b j₀ Mn G.level Cc0 ∧
  (∀ p c s, s.Valid Mn.A Mn.J → ∀ d I t X,
    AVenhance.IsZ2Periodic (sourceTransferredFlux G P Mn Cc Cc0 p c s d I t X)) ∧
  (∀ p c s, s.Valid Mn.A Mn.J → ∀ d I t X z,
    ((s.prov G.level).tags P).order < d →
    sourceTransferredFlux G P Mn Cc Cc0 p c s d I t X z = 0)

/-- Remaining analytic field realization, independent of any outgoing stage.
Special cases are those of TransferFields; seed exports may be nonempty. The anchor is
arbitrary and the terminal level is allowed. -/
def StageTransferFieldsStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀), Input P Mn G →
    ∃ Cc Cc0, TransferFields G P Mn Cc Cc0
end

end AVRegularity.Construction.StageSuccessor
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.StageSuccessor

/-! The exact cascade existence statement from the shared qualitative producer and its
incoming-certificate adapter. No terminal-level exclusion occurs in the shared statement. -/

/-- Supply the stage-generic inputs from the cascade prefix, before choosing a successor.
The empty seed and the empty incoming family are allowed, and no root dimension
is assumed positive. The level floor also supplies the outgoing native contexts at j₀.
The finite path certificate is the cascade depth theorem, not a new acyclicity premise. -/
def CascadeSuccessorInputsStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    ∃ mStar : ℕ,
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
    ∀ G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      Input (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G

/-- The exact conclusion, from the two named ingredients above. -/
theorem successor_exists_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ)
    (hinputs : CascadeSuccessorInputsStatement α s q ζ)
    (hexists : StageSuccessorExistsStatement) :
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
    ∃ mStar : ℕ,
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
    ∀ G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      ∃ G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
        IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
          (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' := by
  obtain ⟨Λ₀, hΛ₀, hinput⟩ := hinputs
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, hinput⟩ := hinput Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hinput⟩ := hinput φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper
    hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hinput⟩ := hinput kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hinput⟩ := hinput CI Cw j₀ hledger hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM G hcascade hlevel hG
  exact hexists _ _ G (hinput D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM G hcascade hlevel hG)

end AVRegularity.Construction.StageSuccessor
end
