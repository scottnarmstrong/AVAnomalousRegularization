-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.CoarseWeak.FirstInput
public import AVRegularity.EntryTerminal.Ingredients.SeedCert.SeedCertPart
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfOpen
import AVRegularity.Construction.Uniqueness.SuccessorFluxWindow
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.EntryTerminal.Ingredients.Recon.CoarseWeak.First3
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
import AVRegularity.CycleComparison.Coarse.Energy.Zero

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The native input of the terminal frame** (step W.b of the coarse weak equation).

`termNativeInput c x ...` is the `NativeInput (termCovFrame c x)`. The fields come from the weak
stage `c.weak` (level, depth, generated, shift, incoming certificate), the successor `c.succ`, the
certificate `x.cert` of `Gt'` with the grades `≤ 1` and `kW.G0 ≤ kW.Hprod`, the terminal stage
input of the terminal successor (the proof of `terminalSuccessor`, extracted at a context), and the truncation of the
retained solution `c.sol` to the order `K̂ - 2`. The kernels are all isotropic paired kernels, hence
admissible with `Γ = 2`, moment order `0`.

Special cases: an edgeless weak stage (depth 0); `j₀ = 0`. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Truncation of zero. -/
theorem truncate_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k k' : ℕ} (hk : k' ≤ k) :
    truncateTorusHk hk (0 : TorusHk k E) = 0 :=
  (truncateTorusHk hk).map_zero

/-- Every kernel of the terminal passage (seed or fresh) is an isotropic paired kernel, hence
admissible with `Γ = 2` and moment order `0`. -/
theorem termKernelOf_admissible (D : OCData) (G : GenStage D ScalarH A.Dt A.bw j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (G.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v u γ).IsAdmissible 2 0 := by
  unfold GenStage.kernelOf
  split
  · exact WeakEntryProofs.isoPairedKernel_isAdmissible _ _ 0 (by have := nW.pos; omega)
  · exact WeakEntryProofs.isoPairedKernel_isAdmissible _ _ 0 (by have := A.nT.pos; omega)

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The stage input at the terminal** (the input of `terminalSuccessor`, at a context). -/
theorem termStageInput (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M) :
    Construction.StageSuccessor.Input (A.Pt c.D Cw cr M) (A.Mt M sXT sZT c.tp cr) c.Gw := by
  have hD := c.data
  have hweak := c.weak
  have hcr : 0 < cr := by rw [x.one]; exact one_pos
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := hD
  have hΛD : 128 ≤ c.D.Λ := by rw [hDΛ]; exact hΛ
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hζ : IsFastProfile c.D.ζ := by rw [hDζ]; exact X.hζ
  have hκ : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hinv := hweak.2.2.2.2.2.2.2.2.2
  have hεpos : ∀ i, 0 < c.D.eps i := fun i => (Scales.epsilon_basic hq1 hΛD).1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (by omega)
  have hρ : 0 < c.D.termRho cr M := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh))
  have hNT := one_le_NT_of_valid A hA
  have hsrc := Construction.StageSuccessor.terminal_source_orders_and_paths c.Gw A.NT A.pT A.DW
    A.dW hNT hweak.2.2.2.1
  exact
    { base := by omega
      profile := hζ
      band := hκ
      bandwidth := hA.2.2.1.1
      level := by have := hweak.2.2.1; omega
      top := by have := hweak.2.2.1; omega
      order := le_trans (by norm_num) (le_max_left _ _)
      cutoff := hNT
      length_factor := hcr
      natural := hinv.1
      tags := hasTags_of_seed hinv.2.1 hweak.2.2.2.2.2.1.1
      context := ⟨kW, hinv.2.2.2.2.2.1⟩
      old_births := fun v hv e he => by
        rw [show v.births = [] from hweak.2.2.2.2.1 ⟨v, hv⟩] at he
        exact absurd he (List.not_mem_nil)
      finite_paths := ⟨A.dW, hsrc.2⟩
      witness_constant := x.cwNonneg
      birth_weights := fun _ => zero_le_one
      birth_scales := hεpos
      birth_length := hρ
      birth_width := mul_pos hρ (Real.rpow_pos_of_pos (hεpos _) _)
      cutoff_eq := rfl
      covariance_eq := rfl
      letter_orders := hsrc.1 }

/-- The retained solution `c.sol` truncated to the frame order `K̂ - 2`. -/
theorem termFrame_solution :
    (c.Gt'.retained M 1 A.RT).IsRegSolution (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
      A.φ₀ A.hφ₀ (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1))) (A.Khat Kout - 2) c.tp (c.a + A.T₀)
      (fun v => truncateTorusHk (Nat.sub_le _ 2) (c.Z₀ v)) (fun _ _ => 0) (fun _ _ => 0)
      (termFrameY c) (fun v t => truncateTorusHk (Nat.succ_le_succ (Nat.sub_le _ 2)) (c.Zw v t))
      (fun v u γ t => truncateTorusHk (by omega) (c.Zk v u γ t)) := by
  have hs := c.sol
  unfold GenStage.IsRegSolution at hs ⊢
  have := Providers.kernel_solution_truncate_torus _ _ _ _ (A.Khat Kout - 2) (A.Khat Kout) A.Dt
    (Nat.sub_le _ 2) _ _ _ _ _ _ _ _ _ hs
  simp only [truncate_zero] at this
  exact this
end

/-! **`NativeInput (termCovFrame c x)`** (step W.b of the coarse weak equation).

The assembly of the fields. The hypotheses are exactly the floors of the prefix `ReconPrefix`:
the base `128 ≤ Λ`, the validity of the data, the level `j₀ + 2 ≤ M`, the window `t_p ≤ a + T₀`
(`termReconTimes` gives the strict form), the carrier start at the pair `(1, 1)` (from the prefix's
pair by `IsCarrierStart.mono`), the auxiliary floor `K_out` and the slow and fast floors `s_X, s_Z`.

Special cases: an edgeless weak stage (depth 0); `j₀ = 0`. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The weak components have no births, hence grade `0`. -/
theorem termWeak_grade_zero
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (v : CompIn c.Gw.comps) : compGrade v.1 = 0 := by
  simp [compGrade, c.weak.2.2.2.2.1 v]

/-- **W.b: the native input of the terminal frame.** -/
def termNativeInput
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (htp : c.tp ≤ c.a + A.T₀) (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hK : 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout)
    (hsX : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    NativeInput (termCovFrame c x) :=
  have hinv := c.weak.2.2.2.2.2.2.2.2.2
  have hD := c.data
  { stage := termStageInput c x hΛ hA hM
    actual := c.succ
    retained := rfl
    level := c.weak.2.2.1
    generated := hinv.2.2.1
    shift := hinv.2.2.2.1
    depth := c.weak.2.2.2.1
    incoming_context := ⟨kW, hinv.2.2.2.2.2.1, fun v =>
      termReserve_nonneg x.reserve1 (by rw [termWeak_grade_zero c v]; omega)⟩
    outgoing_context := ⟨kW, x.cert, fun v =>
      termReserve_nonneg x.reserve1 (termGrade_le_one (termWeak_grade_zero c) c.succ v)⟩
    menuN := rfl
    menup := rfl
    menuH := rfl
    menuJ := rfl
    menuEta := rfl
    menuSlow := rfl
    menuFast := rfl
    window := htp
    carrier_start := fun k hk => by
      obtain ⟨hDα, hDq, hDΛ, -⟩ := hD
      rw [hDα, hDq, hDΛ]
      simpa only [mul_one] using hstart.1 k hk
    auxiliary := by
      have h := le_max_left Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))
      change 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT ≤ A.Khat Kout - 2
      unfold TermArgs.Khat
      omega
    slow := hsX
    fast := hsZ
    integrable := A.hφ₀
    smooth := hA.2.1.1
    nonnegative := hA.2.1.2.1
    mass := hA.2.1.2.2.1
    support := hA.2.1.2.2.2
    kernels := ⟨2, fun v u γ => termKernelOf_admissible (Cw := Cw) (cr := cr) (M := M) (nW := nW)
      c.D c.Gw v u γ⟩
    successorKernels := ⟨2, fun v u γ => termKernelOf_admissible (Cw := Cw) (cr := cr) (M := M)
      (nW := nW) c.D c.Gt' v u γ⟩
    Y0 := fun v => truncateTorusHk (Nat.sub_le _ 2) (c.Z₀ v)
    Yw := fun v t => truncateTorusHk (Nat.succ_le_succ (Nat.sub_le _ 2)) (c.Zw v t)
    Yk := fun v u γ t => truncateTorusHk
      (show A.Khat Kout - 2 + A.Dt - 1 ≤ A.Khat Kout + A.Dt - 1 by omega) (c.Zk v u γ t)
    solution := termFrame_solution c }
end

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Provenance reindexing at the terminal menu. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The terminal incoming components have empty birth histories, so the provenance
reindexing uses exactly the same stage-generic identity as the cascade. -/
theorem terminalReindex
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hK : A.Dt + 2 ≤ Kout) : ReindexOn (termCovFrame c x) := by
  have hin := termStageInput c x hΛ hA hM
  have hlev := c.weak.2.2.1
  let R : ReindexInput (A.Pt c.D Cw cr M) (A.Mt M sXT sZT c.tp cr) c.Gw c.Gt' := {
    act := c.succ
    W := Classical.choice (splitWitness_nonempty c.succ)
    hold := hin.old_births
    hE := Construction.Stream.ocEpsilon_pos hin.base
    hcs := (EntryWeakProofs.weakData_cellScaleSq_pos c.D hin.base hin.profile hin.band c.Gw.level).le
    hτ := Construction.Stream.ocTau_pos hin.base
    hWin := Uniqueness.succWindowData_of_target (reindex_succ_window_data hin.profile _ c.Gw)
    hΩ := fun _ _ hchain => ⟨Providers.GenSem.isOpen_ladderOmega _ _ _ _ _ _ _,
      Providers.GenSem.zero_mem_ladderOmega hin.profile hchain _⟩
    hΦ := fun chain t => ⟨(Providers.GenSem.contDiff_famMapInv chain t).continuous.continuousAt,
      Providers.GenSem.famMapInv_zero hin.profile chain t⟩ }
  intro v t ht y
  have hDm : A.Dt ≤ A.Khat Kout - 2 := by
    have hk : Kout ≤ A.Khat Kout := le_max_left _ _
    omega
  have key := reindex_pointwise R (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀
    hA.2.1.1 hA.2.1.2.2.2 (H := 1) (J := A.RT) (Naux := A.Khat Kout - 2)
    (le_refl A.RT) hDm (c.D.eps (M - 1)) A.η₀
    (Construction.Stream.ocEpsilon_pos hin.base) t
  rw [hlev] at key
  exact key (termFrameY c) x.aY x.aZ (fun w => termFrame_retained c x w t ht)
    (fun w => termFrame_readout c x w t ht) v y

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The terminal split input in the cases where the degree cutoff is not needed. -/
theorem terminalSplitInput
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀) (hDW : 2 ≤ A.DW)
    (hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    SplitInput (A.Pt c.D Cw cr M) (A.Mt M sXT sZT c.tp cr) c.Gw c.Gt' A.dW c.CcT := by
  have hinv := c.weak.2.2.2.2.2.2.2.2.2
  have hlev := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, _hband, _hterm⟩ := c.data
  refine {
    stage := termStageInput c x hΛ hA hM
    successor := c.succ
    lift := ?_
    range := ?_
    edge := ?_
    stream := ?_
    history := ⟨M + A.Jw, stageHistoryInvariant_of_isStageInvariant hinv⟩
    start := ?_
    alpha_pos := by rw [hDα]; exact X.hα₀
    q_gt := by rw [hDq]; exact X.hq.1 }
  · simpa only [hlev, TermArgs.Mt, termMenu] using c.lift.1
  · refine ⟨A.DW, A.NT + A.DW, A.dW, 0, rfl, le_rfl, hDW, ?_, ?_, hsX, hsZ⟩
    · intro p ctx v u γ d I hd
      apply c.Gw.fam.flux_zero
      have hb := (c.weak.2.2.2.2.2.2.1 v u γ).1
      omega
    · intro h π
      have hh := Providers.CascadeInvariants.stagePath_length_le c.weak.2.2.2.1 π
      exact ⟨hh, hh⟩
  · refine ⟨kW, hinv.2.2.2.2.2.1, hinv.2.2.2.2.1, fun v => ?_⟩
    exact QuietEntrance.qe_compReserve_bounds kW (Nat.le_succ_of_le x.reserve1) v.1
      (c.weak.2.2.2.2.1 v)
  · rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  · rw [hDα, hDq, hDΛ]
    exact hstart

/-- The generic core supplies the terminal reconstruction for incoming order at least two. -/
theorem terminalReconstruct_high
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀) (hDW : 2 ≤ A.DW)
    (hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hK : A.NT + A.Dt + 4 * A.pT + 2 ≤ Kout) :
    ReconstructOn (termCovFrame c x) := by
  apply reconstructOn_of_core successorSplitCore
  refine ⟨c.weak.2.2.1, rfl, rfl, rfl, ?_,
    terminalSplitInput c x hΛ hA hM hstart hDW hsX hsZ⟩
  change A.NT + A.Dt + 4 * A.pT ≤ A.Khat Kout - 2
  have hk : Kout ≤ A.Khat Kout := le_max_left _ _
  omega
end

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The remaining terminal split case. Its incoming arrays vanish at every tested
order; positive lift grades must be removed by cell-problem uniqueness. -/
def TerminalLowOrderReconstructStatement : Prop :=
  ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
    {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ},
  ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c),
    128 ≤ A.Λ → A.Valid → j₀ + 2 ≤ M →
    IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀ → A.DW = 1 →
    max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT →
    max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT →
    A.NT + A.Dt + 4 * A.pT + 2 ≤ Kout → ReconstructOn (termCovFrame c x)

/-- At weak order one the incoming graph has no constituent identities. -/
theorem terminal_order_one_no_identity
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (hDW : A.DW = 1) (v u : CompIn c.Gw.comps) (γ : c.Gw.fam.Γ v u) : False := by
  have hlow := (c.Gw.fam.identity v u γ).two_le
  have hhigh := (c.weak.2.2.2.2.2.2.1 v u γ).1
  omega

/-- Consequently the order-one graph has no positive-length path. -/
theorem terminal_order_one_no_path
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (hDW : A.DW = 1) {h : ℕ} (hh : 0 < h) (π : StagePath c.Gw h) : False := by
  exact terminal_order_one_no_identity c hDW _ _ (π.step ⟨0, hh⟩).2.2

/-- Terminal reconstruction by cases, with the generic-core cases discharged. -/
theorem terminalReconstruct_of_low
    (hlow : TerminalLowOrderReconstructStatement)
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hK : A.NT + A.Dt + 4 * A.pT + 2 ≤ Kout) :
    ReconstructOn (termCovFrame c x) := by
  by_cases hDW : 2 ≤ A.DW
  · exact terminalReconstruct_high c x hΛ hA hM hstart hDW hsX hsZ hK
  · have hDW1 : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
    exact hlow c x hΛ hA hM hstart (by omega) hsX hsZ hK
end

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Every fibre of an order-one terminal incoming graph has empty edges. -/
theorem terminal_order_one_empty_edges
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (hDW : A.DW = 1) (k : ℤ) (hk : Odd k)
    (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 A.Dt) :
    (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
      (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))).edge v u d = [] := by
  classical
  have hempty : (Finset.univ : Finset (c.Gw.fam.Γ v u)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ _
    exact terminal_order_one_no_identity c hDW v u γ
  simp only [familyLiftData, liftEdges, ChartedFamily.fiber, hempty,
    Finset.toList_empty, List.filterMap_nil, List.map_nil]

/-- Positive terminal lift grades vanish in the order-one case, on each lift window. -/
theorem terminal_order_one_positive_grade
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hDW : A.DW = 1) (hsZ : 1 ≤ sZT) (k : ℤ) (hk : Odd k)
    (hh : ℕ) (hh0 : hh ≠ 0) (hhD : hh ≤ A.dW) (n m : ℕ) (α : DerivativeWord2 m)
    {t : ℝ} (ht : t ∈ Set.Icc (c.D.slotStart M k / c.D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M))
    (X' z : Vec 2) (v u : CompIn c.Gw.comps) : c.CcT k hh n m α t X' z v u = 0 := by
  classical
  have hin := termStageInput c x hΛ hA hM
  have hlev := c.weak.2.2.1
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos c.D hin.base hin.profile hin.band M
  have hab : c.D.slotStart M k / c.D.cellScaleSq M ≤
      (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M := by
    apply (div_le_div_iff_of_pos_right hcs).2
    unfold OCData.slotStart
    have hτ : 0 ≤ ocTau c.D.α c.D.q c.D.Λ M := (Construction.Stream.ocTau_pos hin.base).le
    exact mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) - 61 / 48 ≤ (k : ℝ) + 61 / 48) hτ
  let π0 : StagePath c.Gw 0 := ⟨Fin.elim0, fun _ hj => by omega⟩
  have hw := Uniqueness.succWindowData_of_target
    (reindex_succ_window_data hin.profile (A.Mt M sXT sZT c.tp cr) c.Gw)
  have hadm : IsAdmissibleChain c.D A.bw j₀ c.Gw.level k (nativeChain c.Gw.level k) := by
    rw [← hin.natural.2.2.1 ⟨k, hk⟩]
    exact (c.Gw.actual ⟨k, hk⟩).2
  have hwin := hw 0 π0 k (nativeChain c.Gw.level k) ⟨hadm, hk⟩
  dsimp only [familyLiftData] at hwin
  simp only [hlev, TermArgs.Mt, termMenu] at hwin
  exact lift_positive_grade_empty_edges
    (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
      (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩)))
    (terminal_order_one_empty_edges c hDW k hk) (c.lift.1 k hk) hab hwin hsZ
    hh hh0 hhD n m α ht X' z v u
end

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The actual terminal data meet the first-source premises even at weak order one. -/
theorem terminalFirstInput
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    FirstSourceInput (A.Pt c.D Cw cr M) (A.Mt M sXT sZT c.tp cr) c.Gw c.Gt' A.dW c.CcT := by
  have hinv := c.weak.2.2.2.2.2.2.2.2.2
  have hlev := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, _hband, _hterm⟩ := c.data
  refine {
    stage := termStageInput c x hΛ hA hM
    successor := c.succ
    lift := ?_
    range := ?_
    edge := ?_
    stream := ?_
    history := ⟨M + A.Jw, stageHistoryInvariant_of_isStageInvariant hinv⟩
    start := ?_
    alpha_pos := by rw [hDα]; exact X.hα₀
    q_gt := by rw [hDq]; exact X.hq.1 }
  · simpa only [hlev, TermArgs.Mt, termMenu] using c.lift.1
  · refine ⟨A.DW, A.NT + A.DW, A.dW, 0, rfl, le_rfl, ?_, ?_, hsX, hsZ⟩
    · intro p ctx v u γ d I hd
      apply c.Gw.fam.flux_zero
      have hb := (c.weak.2.2.2.2.2.2.1 v u γ).1
      omega
    · intro h π
      have hh := Providers.CascadeInvariants.stagePath_length_le c.weak.2.2.2.1 π
      exact ⟨hh, hh⟩
  · refine ⟨kW, hinv.2.2.2.2.2.1, hinv.2.2.2.2.1, fun v => ?_⟩
    exact QuietEntrance.qe_compReserve_bounds kW (Nat.le_succ_of_le x.reserve1) v.1
      (c.weak.2.2.2.2.1 v)
  · rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  · rw [hDα, hDq, hDΛ]
    exact hstart
end

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- With no incoming identities every valid successor source is diagonal. -/
theorem terminal_order_one_plain_diagonal
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (hDW : A.DW = 1)
    (g : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) :
    rootFluxOn (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt' .plain g =
      rootDiagFlux c.Gw c.Gt' g := by
  classical
  obtain ⟨W⟩ := splitWitness_nonempty c.succ
  have hdiag (s : SuccSource c.Gw) (hs : s.Valid (A.Mt M sXT sZT c.tp cr).A
      (A.Mt M sXT sZT c.tp cr).J) : s.IsDiag := by
    cases s with
    | copyDir _ v u γ => exact (terminal_order_one_no_identity c hDW v u γ).elim
    | copyQuad _ h π => exact (terminal_order_one_no_path c hDW (by have := hs.2.2; omega) π).elim
    | letterDiag => trivial
    | letterMean _ _ h π => exact (terminal_order_one_no_path c hDW (by have := hs.2.2; omega) π).elim
    | letterCov _ _ h _ _ π => exact (terminal_order_one_no_path c hDW (by have := hs.2.2; omega) π).elim
  have hprov (v' u' : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v' u') :
      c.Gt'.prov v' u' γ = Prov.letter c.Gw.level WordLetter.diag [] := by
    rw [(W.spec v' u' γ).1]
    exact (rsb_isDiag_iff _ _).1 (hdiag _ (W.e v' u' γ).2.1)
  funext v' t y
  unfold rootFluxOn rootDiagFlux
  refine Finset.sum_congr rfl fun u' _ => ?_
  split_ifs
  · exact Finset.sum_congr rfl fun γ _ => by rw [ite_eq_left (hprov v' u' γ)]
  · rfl

/-- Every positive-grade Eulerian mean is zero in the order-one terminal case. -/
theorem terminal_order_one_mean_zero
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (hDW : A.DW = 1) (hsZ : 1 ≤ sZT)
    (a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root) (t : ℝ) (y : Vec 2)
    (v : CompIn c.Gw.comps) :
    menuMeanFluxE (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT a t y v = 0 := by
  classical
  have hin := termStageInput c x hΛ hA hM
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos c.D hin.base hin.profile hin.band M
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos hin.base
  unfold menuMeanFluxE menuGluedMeanFlux
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun r hr =>
    Finset.sum_eq_zero fun n _ => ?_
  split_ifs with hk
  · by_cases hcut : ocCutoff c.D.α c.D.q c.D.Λ M k t = 0
    · rw [hcut, zero_smul]
    · have htime := CovFluxReg.clock_mem_window c.D M k t hτ hcc hcut
      have hrange := Finset.mem_Icc.1 hr
      have hzero := fun n' m α X' z v' u' =>
        terminal_order_one_positive_grade c x hΛ hA hM hDW hsZ k hk r (by omega)
          hrange.2 n' m α htime X' z v' u'
      have hflux := fun a' X' z j => liftFluxX_empty_grade
        (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
          (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩)))
        (terminal_order_one_empty_edges c hDW k hk) (c.CcT k) r n
        ((c.D.cellScaleSq M)⁻¹ * t) hzero a' X' z j
      have hpulse : pulseMeanFluxEuler (c.D.cellScaleSq M) (cr * liftLength c.D M)
          (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / (cr * liftLength c.D M)) n r
          (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
            (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))) (c.CcT k)
          (fun s' y' => c.D.flowOf (M - 1) s' y' (c.D.slotAnchor M k))
          (fun s' y' => c.D.flowOf (M - 1) (c.D.slotAnchor M k) y' s') a t y v = 0 := by
        unfold pulseMeanFluxEuler
        simp only [hflux, fieldCellMean_zero, smul_zero, Pi.zero_apply, Finset.sum_const_zero]
        rfl
      simp only [TermArgs.Mt, termMenu]
      rw [hpulse, smul_zero]
  · rfl
end

/-! Terminal instantiation of the generic split core when the incoming order is at least two. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The order-one reconstruction: all incoming paths and all positive lift grades vanish,
leaving exactly the first-source diagonal identity. -/
theorem terminalReconstruct_low : TerminalLowOrderReconstructStatement := by
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M
    c x hΛ hA hM hstart hDW hsX hsZ hK
  let Mn := A.Mt M sXT sZT c.tp cr
  have hin := terminalFirstInput c x hΛ hA hM hstart hsX hsZ
  have hlev := c.weak.2.2.1
  have haux : A.NT + A.Dt + 4 * A.pT ≤ A.Khat Kout - 2 := by
    have hk : Kout ≤ A.Khat Kout := le_max_left _ _
    omega
  have haux' : Mn.N + A.Dt + 4 * Mn.p ≤ A.Khat Kout - 2 := haux
  have hsZ1 : 1 ≤ sZT := by omega
  have hrep := fun w s hs => termFrame_readout c x w s hs
  have hdiag := firstSourceIdentity (A.Pt c.D Cw cr M) Mn c.Gw c.Gt' A.dW c.CcT hin
    (A.Khat Kout - 2) haux' c.tp (c.a + A.T₀) x.aZ
    (fun w s hs => ⟨(hrep w s hs).2.1, (hrep w s hs).2.2.1⟩)
  simp only [hlev, termMenu, Mn] at hdiag
  have hplain := terminal_order_one_plain_diagonal c hDW x.aZ
  have hmean (s : ℝ) (v : CompIn c.Gw.comps) :
      (fun y => menuMeanFluxE Mn c.Gw M A.NT A.dW c.CcT
        (menuCovPRep Mn c.D M A.pT x.aZ) s y v) = 0 := by
    funext y
    exact terminal_order_one_mean_zero c x hΛ hA hM hDW hsZ1 _ s y v
  have hreg (v : CompIn c.Gw.comps) (s : ℝ) (hs : s ∈ Set.Icc c.tp (c.a + A.T₀)) :
      (∀ y, menuCovFlux Mn c.Gw M A.NT A.pT A.dW c.CcT x.aZ v s y =
        covTemporalAt Mn c.Gw M A.NT A.pT c.CcT x.aZ v s y) ∧
      Continuous (menuCovFlux Mn c.Gw M A.NT A.pT A.dW c.CcT x.aZ v s) := by
    have hT := CovFluxReg.s47_menuTemporalFlux_contDiff (A.Pt c.D Cw cr M) Mn
      c.Gw c.Gt' A.dW c.CcT hin (A.Khat Kout - 2) haux' x.aZ s
      (fun w => (hrep w s hs).2.1) v
    simp only [hlev, termMenu, Mn] at hT
    have hT' : ContDiff ℝ (2 * A.pT : ℕ) (fun y => menuTemporalFlux Mn c.Gw M A.NT A.pT c.CcT x.aZ s v y) := by
      exact_mod_cast hT
    have hMz : ContDiff ℝ (2 * A.pT : ℕ) (fun y => menuMeanFluxE Mn c.Gw M A.NT A.dW c.CcT
        (menuCovPRep Mn c.D M A.pT x.aZ) s y v) := by rw [hmean]; exact contDiff_const
    obtain ⟨heq, hc⟩ := menuCovFlux_split_of_contDiff Mn c.Gw M A.NT A.pT A.dW c.CcT x.aZ v s hT' hMz
    refine ⟨fun y => ?_, hc⟩
    rw [heq]
    have hz : covMeanAt Mn c.Gw M A.NT A.pT A.dW c.CcT x.aZ v s y = 0 := by
      unfold covMeanAt
      rw [hmean, AVRegularity.CycleComparison.Coarse.covPolyQ_zero_field]
      rfl
    rw [hz, sub_zero]
  intro v t ht φ hφ _hp
  have hsub : ∀ s ∈ Set.Ioc c.tp t, s ∈ Set.Icc c.tp (c.a + A.T₀) :=
    fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  refine testedFlux_of_pointwise ?_ ?_
  · intro s hs y
    change rootReadout (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt'
      .plain M (c.D.eps (M - 1)) A.η₀ x.aZ v s y =
        -menuCovFlux Mn c.Gw M A.NT A.pT A.dW c.CcT x.aZ v s y
    unfold rootReadout
    rw [hplain]
    change diagReadout c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v s y = _
    rw [hdiag v s (hsub s hs) y, (hreg v s (hsub s hs)).1 y]
    rfl
  · intro s hs
    exact fluxPairing_integrable ((hreg v s (hsub s hs)).2.neg) hφ
end

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Provenance reindexing at the terminal menu. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Terminal readout assembly. Only the order-one reconstruction remains open. -/
theorem terminalReadout_of_low
    (hlow : TerminalLowOrderReconstructStatement)
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (htp : c.tp ≤ c.a + A.T₀) (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hK : 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout)
    (hsX : max (A.NT + max 2 A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + max 2 A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    (termCovFrame c x).readoutWeak := by
  have hd : A.DW ≤ max 2 A.DW := le_max_right _ _
  have hd2 : 2 ≤ max 2 A.DW := le_max_left _ _
  have hX : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT := by omega
  have hZ : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT := by omega
  exact native_readoutWeak (termCovFrame c x)
    (termNativeInput c x hΛ hA hM htp hstart hK hX hZ)
    (terminalReindex c x hΛ hA hM (by omega))
    (terminalReconstruct_of_low hlow c x hΛ hA hM hstart (by omega) (by omega) (by omega))
end

/-! Provenance reindexing at the terminal menu. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Numeric floors of the terminal readout assembly, all selected by the prefix. -/
def FloorsAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (_x : TermResAux c) : Prop :=
    128 ≤ A.Λ ∧ A.Valid ∧ j₀ + 2 ≤ M ∧
    IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀ ∧
    4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout ∧
    max (A.NT + max 2 A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT ∧
    max (A.NT + max 2 A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT

/-- The terminal prefix supplies every numeric floor independently of the fields. -/
theorem terminalFloors : ReconPrefix (κ := Unit) fun c x _ _ _ => FloorsAt c x := by
  intro _ℓ X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun _kc _ => ?_⟩⟩
  let S := max (A.NT + max 2 A.DW) (2 * A.pT) + A.Dt + 2
  refine ⟨S, S, 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2,
    fun sXT sZT hX hZ Kout hK => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _hcP
  exact ⟨(), 1, 1, le_rfl, one_pos, fun j₀ hstart =>
    ⟨j₀ + 2, fun M hM c x => ⟨hΛ, hV, hM, hstart, hK, hX, hZ⟩⟩⟩

/-- The coarse equation from the terminal-specific low-order split and the external
native temporal representative. The temporal formula uses its actual regularity clock. -/
theorem termCoarseWeak_of_low_native
    (hlow : TerminalLowOrderReconstructStatement)
    (hNative : NativeTemporalRepresentativesStatement) : TermCoarseWeakStatement := by
  apply (terminalFloors.and termReconTimes.toReconPrefix).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M
    c x _kc _ℓ _k h
  obtain ⟨⟨hΛ, hA, hM, hstart, hK, hX, hZ⟩, _hentrance, htp⟩ := h
  have hd2 : 2 ≤ max 2 A.DW := le_max_left _ _
  have hX2 : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT := by omega
  have hZ2 : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT := by omega
  let F := termCovFrame c x
  have hi := termNativeInput c x hΛ hA hM htp.le hstart hK hX2 hZ2
  obtain ⟨dZ, dRep, dUh, hreg, _hglue⟩ := hNative F hi
  have hadj := frame_covarianceAdjoints F hreg.covarianceSymmetric
  have hid := frame_prepared_eq F dZ dRep dUh hreg
  have hread := readoutStrongEquation F dZ dRep dUh hreg hadj
    (terminalReadout_of_low hlow c x hΛ hA hM htp.le hstart hK hX hZ)
  have htemp := temporal_product F hreg hreg.clock_nonzero hid
  exact (termCoarseWeakAt_iff c x).2
    (macroWeakFromStrong F dZ dRep dUh hreg (covarianceMeanReduction F dZ dRep dUh hreg htemp hread))
end

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Terminal readout equation, including the weak-order-one case. The coarse equation
is reduced only to the external native temporal representative. -/

/-- Step W.d with only the external native temporal representative theorem remaining.
This conditional export does not by itself prove `TermCoarseWeakStatement`. -/
theorem termCoarseWeak_of_native (hNative : NativeTemporalRepresentativesStatement) :
    TermCoarseWeakStatement :=
  termCoarseWeak_of_low_native terminalReconstruct_low hNative

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
