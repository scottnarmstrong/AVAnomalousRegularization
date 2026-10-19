-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.SeedCert.SeedCertPart
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.Construction.StageKernelPrice.Successor
import AVRegularity.EntryTerminal.Assembly.Seed.SeedLedgerAssembly
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Construction.Preservation.Assembly.RetainedMarkedLedgerOfIngredients
public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal

section
section
/-! **The split of `SeedRetainedPart`.**

`SeedRetainedAtM` follows from three statements at the per-level context `SeedCtx`, each under the
certificate `Gt'.IsContextCertified kW` (which `termCertBlock_exists` supplies for `C_w` above its
floor and a carrier start `j₀`):

* `RetainedBaseAtM`: the structural facts of the retained stage the native lemmas need (slot
  transversality, naturality, shift invariance, scale positivity, reserves, `ρ = termRho ≤ ε`);
* `RetainedKernelZeroAtM`: the zero-order regularizer of the kernel of every identity of the
  retained stage, at every radius, at the plan's constants `k_S.c_ker`;
* `RetainedSchurAtM`: the Schur bound `1/8` at every order `≤ K̂` (the price statement).

The block `SeedRetainedBlock` has the shape of `SeedCertBlock`. For an empty retained family all
three statements are vacuous or trivial. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- A statement `Q` about the terminal successor at every certified per-level context. -/
def SeedRetAt {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ)
    (Q : ∀ (D : OCData), ℝ → BirthLaw → ℝ → GenStage D ScalarH A.Dt A.bw j₀ → Prop) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι → Gt'.IsContextCertified kW → Q D a lawT tp Gt'

/-- The structural facts of the retained stage used by the native coefficient lemmas. -/
def RetainedBase {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (kW : InvConsts) (cr : ℝ) (M : ℕ) (D : OCData)
    (G : GenStage D ScalarH Dm b j₀) : Prop :=
  G.IsSlotTransverse ∧ (∃ Mn, G.IsNatural Mn) ∧ G.IsShiftInvariant ∧ 1 ≤ D.Λ ∧ 1 ≤ G.level ∧
    j₀ ≤ G.level ∧ 0 < b ∧ 0 < D.eps (G.level - 1) ∧
    (∀ v : CompIn G.comps, 0 ≤ compReserve kW v.1) ∧ (∀ v : CompIn G.comps, compReserve kW v.1 ≤ 2) ∧
    0 < D.termRho cr M ∧ D.termRho cr M ≤ D.eps (G.level - 1)

/-- **The structural facts** of `Gt'.retained M 1 R_T`. Proof: copies of `termCtx_slotTransverse`,
`termCtx_shiftInvariant` on `TermPassCtx` (they read only `data`, `weak`, `succ`) and
`IsSlotTransverse.restrict`, `IsShiftInvariant.restrict`; naturality is `succ.2.2.2.1` restricted;
reserves from `termReserve_nonneg`, `termGrade_le_one`; `termRho ≤ ε_{M-2}` from the scale lemmas.
-/
def RetainedBaseAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  SeedRetAt A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M fun D _ _ _ Gt' =>
    RetainedBase kW cr M D (Gt'.retained M 1 A.RT)

/-- **The zero-order regularizers**: the zero-order regularizer of every kernel of the retained
stage. Proof: the kernels are `isoPairedKernel` at the two radii (`A.Kw_`, `A.Kn_` are constant), so
`WeakEntryProofs.exists_isoPairedKernel_regularizer_constants` at the floors of the plan
(`SeedFloors.Meets`: `F.cker nW j ≤ kS.cker j`, with `F` chosen after `A`, hence able to cover the
fresh order `A.nT`), then `kernelOf` by cases on the kernel key. -/
def RetainedKernelZeroAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  SeedRetAt A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M fun D a _ tp Gt' =>
    ∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt tp (a + A.T₀) kS.cker
        ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
          v u γ).width
        ((Gt'.retained M 1 A.RT).sysS (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
          A.φ₀ A.hφ₀ v u γ)

/-- **The Schur bound**: the Schur bound `1/8` of the retained stage at every order `≤ K̂`. Proof:
`context_certified_physical_kernel_price` per identity (radius `termRho`), the marked ledger of
`Gt'` under `lawT` (`ledger_all_menu`, `tagged_ledger_recurrence`, `priced_record_ledger_schur`),
`kernel_schur_of_identity_prices`; then `C * S ≤ 1/8` for `M` large. -/
def RetainedSchurAtM {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  SeedRetAt A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M fun D a lawT tp Gt' =>
    ∀ kk ≤ A.Khat Kout, SchurBound (1 / 8) (kernelSchurMatrix
      (ι := CompIn (Gt'.retained M 1 A.RT).comps) (h := fun v => ScalarH v.1.root)
      (Γ := (Gt'.retained M 1 A.RT).fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
      (D.κ (M - 1)) (D.termRho cr M) (fun v => (Gt'.retained M 1 A.RT).mass lawT v) kk A.Dt tp
      (a + A.T₀) kS.cker
      (fun v u γ => ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW)
        (A.Kn_ D M cr) v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => (Gt'.retained M 1 A.RT).physCoeff v u γ d.1))

/-- **`SeedRetainedAtM` from the certificate and the three statements.** -/
theorem seedRetainedAtM_of_split {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT : ℕ}
    {nW : ℕ+} {cr : ℝ} {kS : InvConsts} {CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ}
    {j₀ M : ℕ}
    (hcert : TermCertAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M)
    (ha : RetainedBaseAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M)
    (hb : RetainedKernelZeroAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M)
    (hc : RetainedSchurAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M) :
    SeedRetainedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hG := hcert D a lawW PW Gw aM tp lawT Gt' (TermPassCtx.of_seedCtx hctx)
  obtain ⟨hpar, ⟨Mn, hnat⟩, hshift, hΛ, hi, hj, hb0, hε, hm, hm2, hρ, hρε⟩ :=
    ha D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  exact terminalRetained_of_native lawT (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀
    kS.cker M (A.Khat Kout) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT) (hG.retained M 1 A.RT).2
    hpar hnat hshift hΛ hi hj hb0 hε hm hm2 hρ hρε
    (hb D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG)
    (hc D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG)

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The zero-order regularizer of every kernel of a stage whose two kernel families
are constant isotropic paired kernels.**

`kernelOf` is a match on the kernel key of the provenance, and the terminal families `A.Kw_`,
`A.Kn_` are constant, so every kernel is `isoPairedKernel r₁ n₁` or `isoPairedKernel r₂ n₂`. Both
satisfy the scalar regularizer at every radius and window with constants `c₁`, `c₂`
(`exists_isoPairedKernel_regularizer_constants`); constants below `cker` are enough
(`spatial_regularizer_constants_mono`). For `r₁ = r₂` the comparison is the identity, and with no
identities the statement is vacuous. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- **Zero-order regularizers of the kernels of a stage with constant isotropic families.** -/
theorem kernelOf_zero_regularizer_of_iso {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm b j₀) (P : ProvParams) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (r₁ r₂ : ℝ) (n₁ n₂ : ℕ+) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (c₁ c₂ cker : ℕ → ℝ) (tp tf : ℝ)
    (h₁ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₁ r ((isoPairedKernel r n₁).op φ₀ hφ₀))
    (h₂ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₂ r ((isoPairedKernel r n₂).op φ₀ hφ₀))
    (hc₁ : ∀ j, c₁ j ≤ cker j) (hc₂ : ∀ j, c₂ j ≤ cker j) :
    ∀ v u (γ : G.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 Dm tp tf cker
        (G.kernelOf P (fun _ => isoPairedKernel r₁ n₁) (fun _ => isoPairedKernel r₂ n₂)
          v u γ).width
        (G.sysS P (fun _ => isoPairedKernel r₁ n₁) (fun _ => isoPairedKernel r₂ n₂) φ₀ hφ₀
          v u γ) := by
  intro v u γ ϱ hϱ
  unfold GenStage.sysS GenStage.kernelOf
  generalize ((G.prov v u γ).tags P).kernel = key
  cases key
  · exact AVRegularity.Construction.Preservation.FullLift.spatial_regularizer_constants_mono (h₁ r₁ hr₁ ϱ tp tf 0 Dm) hr₁.le fun j _ => hc₁ j
  · exact AVRegularity.Construction.Preservation.FullLift.spatial_regularizer_constants_mono (h₂ r₂ hr₂ ϱ tp tf 0 Dm) hr₂.le fun j _ => hc₂ j

/-- **The regularizers at one context**: the zero-order regularizers of the retained stage of the terminal
passage, at the constants `cker` above the isotropic constants `c₁` (order `n_W`) and `c₂` (order
`n_T`). -/
theorem retainedKernelZero_of_passCtx {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ}
    {nW : ℕ+} {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hΛ : 128 ≤ A.Λ) (hcr : 0 < cr) (c₁ c₂ cker : ℕ → ℝ)
    (h₁ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₁ r ((isoPairedKernel r nW).op A.φ₀ A.hφ₀))
    (h₂ : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm',
      IsSpatialRegularizerTorus (G := ℝ) ρ k Dm' a b c₂ r ((isoPairedKernel r A.nT).op A.φ₀ A.hφ₀))
    (hc₁ : ∀ j, c₁ j ≤ cker j) (hc₂ : ∀ j, c₂ j ≤ cker j) :
    ∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 A.Dt tp (a + A.T₀) cker
        ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
          v u γ).width
        ((Gt'.retained M 1 A.RT).sysS (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
          A.φ₀ A.hφ₀ v u γ) := by
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx.1
  have hΛ1 : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hε : ∀ i, 0 < D.eps i := fun i => Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < D.termH M := Construction.Stream.ocTauPP_pos hΛ1
  have hρ : 0 < D.termRho cr M := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh))
  exact kernelOf_zero_regularizer_of_iso (Gt'.retained M 1 A.RT) (A.Pt D Cw cr M) A.φ₀ A.hφ₀
    (D.termRW A.σw M) (D.termRNew cr A.tT M) nW A.nT
    (Real.rpow_pos_of_pos (hε M) _) (mul_pos hρ (Real.rpow_pos_of_pos (hε (M - 1)) _))
    c₁ c₂ cker tp (a + A.T₀) h₁ h₂ hc₁ hc₂

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The structural facts of the retained stage** (`RetainedBase`) at a terminal
passage context (`TermPassCtx`): slot transversality and shift invariance (the proofs of
`termCtx_slotTransverse`, `termCtx_shiftInvariant`, which read only `data`, `weak`, `succ`),
naturality, scale positivity, reserves, and `termRho ≤ ε_{M-2}` from `termRho ≤ ε_{M-1}`. For an empty retained family the reserve clauses are vacuous. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- **The structural facts at one context.** -/
theorem retainedBase_of_passCtx {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hA : A.Valid) (hΛ : 128 ≤ A.Λ) (hcr : 0 < cr) {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hGH : kW.G0 ≤ kW.Hprod)
    (hrho : D.termRho cr M ≤ D.eps (M - 1)) :
    RetainedBase kW cr M D (Gt'.retained M 1 A.RT) := by
  have hN : 2 ≤ A.NT := AVRegularity.EntryTerminal.Ingredients.two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hb : 0 < A.bw := hA.2.2.1.1
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx.1
  have hweak := hctx.2.1
  have hsucc := hctx.2.2.2.2.2.2
  have hΛ1 : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < D.q := by rw [hq]; exact X.hq.1
  have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcar' : IsCarrierStart D.α D.q D.Λ A.bw CH Υ j₀ := by rw [hα, hq, hΛD]; exact hcar
  have hlevW : Gw.level = M := hweak.2.2.1
  have hbirth : ∀ w : CompIn Gw.comps, w.1.births = [] := hweak.2.2.2.2.1
  have hlev : Gt'.level = M - 1 := by rw [hsucc.2.1, hlevW]
  have hST := (Providers.GenSem.terminalSuccessor_generation hΛ1 hζ hκ hb hCH hΥ hcar' hterm hweak
    hN hDW hcr.ne' hX hZ hsucc).2
  have hcs : 0 ≤ D.cellScaleSq Gw.level :=
    (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ1 hζ hκ _).le
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ := hweak
  have hSH := Construction.Preservation.FullLift.successor_shift_invariant_of_cellScaleSq_nonneg
    hζ hcs hinv.1 hinv.2.2.2.1 hsucc
  have hnat := hsucc.2.2.2.1
  have hεpos : 0 < D.eps (M - 1 - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < D.termH M := Construction.Stream.ocTauPP_pos hΛ1
  have hres : ∀ w : CompIn (Gt'.retained M 1 A.RT).comps, 0 ≤ compReserve kW w.1 := fun w =>
    termReserve_nonneg hGH (by
      have hw : compGrade w.1 ≤ 1 := (Finset.mem_filter.mp w.2).2.1
      exact hw)
  refine ⟨hST.restrict _ _, ⟨_, ⟨hnat.1, hnat.2.1, hnat.2.2.1, fun v u => hnat.2.2.2 _ _⟩⟩,
    hSH.restrict _ _, hΛ1, ?_, ?_, hb, ?_, hres, fun w =>
    (AVRegularity.Providers.CascadeInvariants.compReserve_le_one kW w.1).trans (by norm_num),
    mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh)), ?_⟩
  · show 1 ≤ Gt'.level
    omega
  · show j₀ ≤ Gt'.level
    omega
  · show 0 < D.eps (Gt'.level - 1)
    rw [hlev]; exact hεpos
  · show D.termRho cr M ≤ D.eps (Gt'.level - 1)
    rw [hlev]
    exact hrho.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1))

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The block assembly of `SeedRetainedPart`** from the Schur bound of the retained family.

`RetainedSchurPart` is the exact form of the Schur-bound statement that the assembly consumes: the
block of `RetainedSchurAtM` with its own `C_w` floor and carrier pair, under the plan hypotheses
of the prefix of `SeedPartPrefix`. `seedRetainedPart_of_schur` combines it with the certificate
(`termCertBlock_exists`), the structural facts `retainedBase_of_passCtx` and the zero-order regularizers `retainedKernelZero_of_passCtx`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- The block of `RetainedSchurAtM`, in the shape of `SeedCertBlock`. -/
def RetainedSchurBlock {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      RetainedSchurAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

/-- **The statement the assembly consumes**: the Schur bound of the retained family, as a
block, under the prefix of the six parts (plan, weak allocation, floors chosen after `A`). -/
def RetainedSchurPart : Prop :=
  SeedPartPrefix fun _ A Kout sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    RetainedSchurBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP

private theorem ocA_nonneg {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (k : ℕ) : 0 ≤ ocA α q Λ k := by
  unfold ocA
  exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _

/-- **`SeedRetainedPart` from the Schur bound of the retained family.** -/
theorem seedRetainedPart_of_schur (hc : RetainedSchurPart) : SeedRetainedPart := by
  intro X
  obtain ⟨Λc, hΛc, hcert⟩ := termCertBlock_exists X
  obtain ⟨Λs, hΛs, hsc⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  obtain ⟨Λr, hΛr, hrs⟩ := hc X
  refine ⟨max Λc (max Λs Λr), le_trans hΛc (le_max_left _ _), fun A hΛ hA Kout => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛs' : Λs ≤ A.Λ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛ
  have hΛr' : Λr ≤ A.Λ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans hΛc hΛc'
  have hΛ1 : 1 ≤ A.Λ := by omega
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := ocA_nonneg hΛ1
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  obtain ⟨SXr, SZr, hr2⟩ := hrs A hΛr' hA Kout
  have hA' := hA
  obtain ⟨-, ⟨hφs, -, -, hφsupp⟩, -, ⟨-, -, -, -, hσw, -, -, -, -⟩, -, hsched, -⟩ := hA'
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  have hreg (n : ℕ+) := WeakEntryProofs.exists_isoPairedKernel_regularizer_constants A.φ₀
    (Providers.hasCompactSupport_of_unitBall hφsupp) hφs A.hφ₀ n
  choose cR hcR0 hcR using hreg
  let F : SeedFloors :=
    { cker := fun n j => max (cR n j) (cR A.nT j)
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨max (max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2) SXr,
    max (max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2) SZr, fun sXT sZT hX hZ => ?_⟩
  have hX1 : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT := le_trans (le_max_left _ _) hX
  have hZ1 : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT := le_trans (le_max_left _ _) hZ
  obtain ⟨KSr, Fr, hr3⟩ := hr2 sXT sZT (le_trans (le_max_right _ _) hX)
    (le_trans (le_max_right _ _) hZ)
  refine ⟨KSr, F.sup Fr, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW halloc cP CP hcP => ?_⟩
  have hplanF : SeedPlan A 0 F Lt nW cr kS :=
    hplan.weaken (Nat.zero_le _) fun h => h.left
  have hplanR : SeedPlan A KSr Fr Lt nW cr kS := hplan.weaken le_rfl fun h => h.right
  have hP := termPlanHyp_of_plan hA hΛ128 hplanF halloc hX1 hZ1
  have hcr0 : 0 < cr := hplan.2.2.2.2.1
  have hcr1 : cr ≤ 1 := hplan.2.2.2.2.2.1
  have hFm := hplanF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcker : ∀ j, F.cker nW j ≤ kS.cker j := hFm.1
  have hR := hr3 Lt nW cr kS hplanR cK CL Cχ kW hcK hkW halloc cP CP hcP
  show SeedRetainedBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP
  intro cH hcH
  obtain ⟨Cw₀, CHc, Υc, hCw₀, hCHc, hΥc, hC'⟩ :=
    hcert A hΛc' sXT sZT nW cr kW CL Cχ cP CP hP hcr0 hcr1 cH hcH
  obtain ⟨Cw₁, CHr, Υr, hCw₁, hCHr, hΥr, hR'⟩ := hR cH hcH
  obtain ⟨Ms, hMs2, hMs⟩ := hsc A.Λ hΛs' cr A.σw A.tT CL hcr0 hσw.le htT.le
  refine ⟨max Cw₀ Cw₁, max CHc CHr, max Υc Υr, le_trans hCw₀ (le_max_left _ _),
    le_trans hCHc (le_max_left _ _), lt_of_lt_of_le (by linarith) (le_max_left _ _),
    fun Cw hCw j₀ hj => ?_⟩
  have hjC : IsCarrierStart X.α X.q A.Λ A.bw CHc Υc j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHc)
      (by linarith) hj
  have hjR : IsCarrierStart X.α X.q A.Λ A.bw CHr Υr j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHr)
      hΥr.le hj
  obtain ⟨Mc, hMc⟩ := hC' Cw (le_trans (le_max_left _ _) hCw) j₀ hjC
  obtain ⟨Mr, hMr⟩ := hR' Cw (le_trans (le_max_right _ _) hCw) j₀ hjR
  refine ⟨max (max Mc Mr) (max Ms (j₀ + 1)), fun M hM => ?_⟩
  have hMc' : Mc ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMr' : Mr ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMs' : Ms ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMj : j₀ + 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hM2 : 2 ≤ M := le_trans hMs2 hMs'
  refine seedRetainedAtM_of_split (hMc M hMc') ?_ ?_ (hMr M hMr')
  · intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
    have hctx' := TermPassCtx.of_seedCtx hctx
    obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx'.1
    exact retainedBase_of_passCtx hctx' hA hΛ128 hcr0 hCHc (by linarith) hjC hX1 hZ1 hMj hM2
      hP.hGH (hMs M hMs' D hα hq hΛD hband).2.1
  · intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
    exact retainedKernelZero_of_passCtx (TermPassCtx.of_seedCtx hctx) hΛ128 hcr0 (cR nW)
      (cR A.nT) kS.cker (hcR nW) (hcR A.nT) (fun j => le_trans (le_max_left _ _) (hcker j))
      (fun j => le_trans (le_max_right _ _) (hcker j))

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **`RetainedSchurAtM` from the identity price and the priced Schur bound.**

`RetainedSchurAtM` follows from two statements about the retained family `Gr` of `Gt'` at a
certified per-level context (the proof is `kernel_schur_of_identity_prices`):

* `RetainedPriceAtM A .. C ..` (open, the identity price): the kernel width of every identity is its record width,
  and the per-identity kernel price at the terminal radius `termRho` and diffusivity `κ_{M-1}`,
  at every order `kk ≤ K̂`, with a constant `C` independent of `M`
  (route: `context_certified_physical_kernel_price` with `ρ = termRho`, `r` the record width,
  `n = kk`, `dout ≤ D̄₀`; the chart jet bounds from the carrier);
* `RetainedPricedSchurAtM A .. C ..` (open, the priced Schur bound): the Schur bound `1/(8C)` of the priced record
  majorant `√(π_u/π_v) Σ_γ ‖map‖ size constituentPrice` of `Gr` under `lawT` (route:
  `priced_record_ledger_schur` from the marked ledger of `Gr` under `lawT`
  (`tagged_ledger_recurrence`-type recurrence for the terminal law), then
  smallness for large `M`). For an empty retained family both clauses are vacuous. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- **The identity price**: widths and the per-identity price at the terminal radius. -/
def RetainedPriceAtM {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (C : ℝ) (j₀ M : ℕ) :
    Prop :=
  SeedRetAt A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M fun D a _ tp Gt' =>
    (∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u),
      ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
        v u γ).width = ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.width) ∧
    ∀ kk ≤ A.Khat Kout, ∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 A.Dt),
        (coefficientSeminorm (D.termRho cr M) kk tp (a + A.T₀)
          ((Gt'.retained M 1 A.RT).physCoeff v u γ d.1)).toReal * kS.cker (d.1 - 2) /
          (D.κ (M - 1) * ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW)
            (A.Kn_ D M cr) v u γ).width ^ (d.1 - 2))) ≤
        C * (‖((Gt'.retained M 1 A.RT).fam.identity v u γ).map‖ *
          ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size *
          constituentPrice ((Gt'.retained M 1 A.RT).fam.identity v u γ).record)

/-- **The priced Schur bound**: the priced record majorant of the retained family is
`1/(8C)`-Schur. -/
def RetainedPricedSchurAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (C : ℝ) (j₀ M : ℕ) : Prop :=
  SeedRetAt A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M fun _ _ lawT _ Gt' =>
    SchurBound (1 / (8 * C)) (fun v u : CompIn (Gt'.retained M 1 A.RT).comps =>
      Real.sqrt ((Gt'.retained M 1 A.RT).mass lawT u / (Gt'.retained M 1 A.RT).mass lawT v) *
        ∑ γ : (Gt'.retained M 1 A.RT).fam.Γ v u,
          ‖((Gt'.retained M 1 A.RT).fam.identity v u γ).map‖ *
            ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size *
            constituentPrice ((Gt'.retained M 1 A.RT).fam.identity v u γ).record)

/-- **The Schur bound at one level from the identity price and the priced Schur bound.** -/
theorem retainedSchurAtM_of_price {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT : ℕ}
    {nW : ℕ+} {cr : ℝ} {kS : InvConsts} {CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw C : ℝ}
    {j₀ M : ℕ} (hΛ : 1 ≤ A.Λ) (hC : 1 ≤ C) (hcker : ∀ j, 0 ≤ kS.cker j)
    (hP : RetainedPriceAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw C j₀ M)
    (hS : RetainedPricedSchurAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw C j₀ M) :
    RetainedSchurAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  obtain ⟨hw, hprice⟩ := hP D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  have hbud := hS D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  have hctx' := TermPassCtx.of_seedCtx hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx'.1
  have hν : 0 < D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ X.hζ hband (Nat.sub_le M 1)
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  intro kk hkk
  have h := AVRegularity.Construction.StageKernelPrice.kernel_schur_of_identity_prices
    (ι := CompIn (Gt'.retained M 1 A.RT).comps) (h := fun v => ScalarH v.1.root)
    (Γ := (Gt'.retained M 1 A.RT).fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
    (D.κ (M - 1)) (D.termRho cr M) (fun v => (Gt'.retained M 1 A.RT).mass lawT v) kk A.Dt tp
    (a + A.T₀) kS.cker
    (fun v u γ => ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW)
      (A.Kn_ D M cr) v u γ).width)
    (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
    (fun v u γ d => (Gt'.retained M 1 A.RT).physCoeff v u γ d.1)
    (fun v u γ => ‖((Gt'.retained M 1 A.RT).fam.identity v u γ).map‖ *
      ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size *
      constituentPrice ((Gt'.retained M 1 A.RT).fam.identity v u γ).record)
    C (1 / (8 * C)) hν
    (fun v u γ => by rw [hw v u γ]; exact ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.width_pos)
    (fun j _ => hcker j) (fun _ _ _ => ContinuousLinearMap.norm_id_le) hC0.le
    (hprice kk hkk) hbud
  have hCS : C * (1 / (8 * C)) = 1 / 8 := by field_simp
  rwa [hCS] at h

/-- The block of the identity price: a `C_w` floor, a carrier pair, then the constant `C` and `M₀`. -/
def RetainedPriceBlock {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ C : ℝ, 1 ≤ C ∧ ∃ M₀ : ℕ,
      ∀ M : ℕ, M₀ ≤ M → RetainedPriceAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw C j₀ M

/-- The block of the priced Schur bound: `M₀` depends on the constant `C` of the identity price. -/
def RetainedPricedSchurBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∀ C : ℝ, 1 ≤ C → ∃ M₀ : ℕ,
      ∀ M : ℕ, M₀ ≤ M → RetainedPricedSchurAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw C j₀ M

/-- **The identity price**, with the prefix of the six parts. -/
def RetainedPricePart : Prop :=
  SeedPartPrefix fun _ A Kout sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    RetainedPriceBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP

/-- **The priced Schur bound**, with the prefix of the six parts. -/
def RetainedPricedSchurPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr _ CL Cχ kW cP CP =>
    RetainedPricedSchurBlock A sXT sZT nW cr CL Cχ kW cP CP

private theorem ocA_nonneg' {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (k : ℕ) : 0 ≤ ocA α q Λ k := by
  unfold ocA
  exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _

/-- **The Schur bound from the identity price and the priced Schur bound.** -/
theorem retainedSchurPart_of_price (hP : RetainedPricePart) (hS : RetainedPricedSchurPart) :
    RetainedSchurPart := by
  intro X
  obtain ⟨Λp, hΛp, hP1⟩ := hP X
  obtain ⟨Λs, hΛs, hS1⟩ := hS X
  refine ⟨max Λp Λs, le_trans hΛp (le_max_left _ _), fun A hΛ hA Kout => ?_⟩
  have hΛp' : Λp ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛs' : Λs ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hΛ1 : 1 ≤ A.Λ := by have := le_trans hΛp hΛp'; omega
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := ocA_nonneg' hΛ1
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  obtain ⟨SXp, SZp, hP2⟩ := hP1 A hΛp' hA Kout
  obtain ⟨SXs, SZs, hS2⟩ := hS1 A hΛs' hA Kout
  refine ⟨max SXp SXs, max SZp SZs, fun sXT sZT hX hZ => ?_⟩
  obtain ⟨KSp, Fp, hP3⟩ := hP2 sXT sZT (le_trans (le_max_left _ _) hX)
    (le_trans (le_max_left _ _) hZ)
  obtain ⟨KSs, Fs, hS3⟩ := hS2 sXT sZT (le_trans (le_max_right _ _) hX)
    (le_trans (le_max_right _ _) hZ)
  let F0 : SeedFloors :=
    { cker := fun _ _ => 0
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨max KSp KSs, F0.sup (Fp.sup Fs), fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW halloc cP CP
    hcP => ?_⟩
  have hplanP : SeedPlan A KSp Fp Lt nW cr kS :=
    hplan.weaken (le_max_left _ _) fun h => (SeedFloors.Meets.right h).left
  have hplanS : SeedPlan A KSs Fs Lt nW cr kS :=
    hplan.weaken (le_max_right _ _) fun h => (SeedFloors.Meets.right h).right
  have hcker : ∀ j, 0 ≤ kS.cker j := fun j =>
    (SeedFloors.Meets.left (hplan.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)).1 j
  have hBP := hP3 Lt nW cr kS hplanP cK CL Cχ kW hcK hkW halloc cP CP hcP
  have hBS := hS3 Lt nW cr kS hplanS cK CL Cχ kW hcK hkW halloc cP CP hcP
  intro cH hcH
  obtain ⟨Cw₀, CHp, Υp, hCw₀, hCHp, hΥp, hP'⟩ := hBP cH hcH
  obtain ⟨Cw₁, CHs, Υs, hCw₁, hCHs, hΥs, hS'⟩ := hBS cH hcH
  refine ⟨max Cw₀ Cw₁, max CHp CHs, max Υp Υs, le_trans hCw₀ (le_max_left _ _),
    le_trans hCHp (le_max_left _ _), lt_of_lt_of_le hΥp (le_max_left _ _),
    fun Cw hCw j₀ hj => ?_⟩
  have hjP : IsCarrierStart X.α X.q A.Λ A.bw CHp Υp j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHp)
      hΥp.le hj
  have hjS : IsCarrierStart X.α X.q A.Λ A.bw CHs Υs j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHs)
      hΥs.le hj
  obtain ⟨C, hC, Mp, hMp⟩ := hP' Cw (le_trans (le_max_left _ _) hCw) j₀ hjP
  obtain ⟨Ms, hMs⟩ := hS' Cw (le_trans (le_max_right _ _) hCw) j₀ hjS C hC
  refine ⟨max Mp Ms, fun M hM => ?_⟩
  exact retainedSchurAtM_of_price hΛ1 hC hcker (hMp M (le_trans (le_max_left _ _) hM))
    (hMs M (le_trans (le_max_right _ _) hM))

/-- **`SeedRetainedPart` from the identity price and the priced Schur bound.** -/
theorem seedRetainedPart_of_price (hP : RetainedPricePart) (hS : RetainedPricedSchurPart) :
    SeedRetainedPart :=
  seedRetainedPart_of_schur (retainedSchurPart_of_price hP hS)

end AVRegularity.EntryTerminal.Route
end
end
end

section
section
/-! **The kernel width of every identity of the retained terminal stage is its record
width, and its record length is at most `ε_{M-2}`.**

The tags of the weak stage are `seed` tags with width `termRW` and length at most `C_L ε_{M+1}`;
the fresh tags are `termRNew`, `termRho`; `succSource_tags_good` transports this to every source
of `Gt'`, whose provenance is `(e v u γ).1.prov M`, and `HasTags` matches the tags to the records. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- The width of a kernel key at the terminal passage. -/
def termKW (D : OCData) (σw cr tT : ℝ) (M : ℕ) : KernelKey → ℝ
  | .seed _ => D.termRW σw M
  | .fresh _ => D.termRNew cr tT M

theorem retained_width_length {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hq1 : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hCL : CL * D.eps (M + 1) ≤ D.eps (M - 1)) (hρ : D.termRho cr M ≤ D.eps (M - 1 - 1)) :
    ∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u),
      ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
        v u γ).width = ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.width ∧
      ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.length ≤ D.eps (M - 1 - 1) := by
  obtain ⟨hdata, hweak, -, -, -, -, hsucc⟩ := hctx
  obtain ⟨-, -, hlev, -, hbirths, ⟨hseedprov, -, -⟩, hrec, -, -, hinv⟩ := hweak
  obtain ⟨-, htags, -⟩ := hinv
  obtain ⟨-, -, -, -, hHT, -, e, Cc, Cc0, -, -, hprov⟩ := hsucc
  have he1 : D.eps (M - 1) ≤ D.eps (M - 1 - 1) :=
    EntryScales.epsilon_antitone hq1 hΛ (Nat.sub_le (M - 1) 1)
  have hgood : ∀ v u (γ : Gw.fam.Γ v u),
      GoodTag (termKW D A.σw cr A.tT M) (D.eps (M - 1 - 1)) ((Gw.prov v u γ).tags (A.Pt D Cw cr M)) := by
    intro v u γ
    obtain ⟨k, tag, hk⟩ := hseedprov v u γ
    have hm := (htags v u γ).1
    obtain ⟨-, hw, hl, -⟩ := hrec v u γ
    rw [hk] at hm ⊢
    simp only [Prov.tags, ProvTags.Matches] at hm
    obtain ⟨-, -, -, hlen, hwid, -⟩ := hm
    refine ⟨?_, ?_⟩
    · show D.termRW A.σw M = tag.width
      rw [← hwid, hw]
    · show tag.length ≤ D.eps (M - 1 - 1)
      rw [← hlen]
      exact hl.trans (hCL.trans he1)
  have hall : ∀ v' u' (γ' : Gt'.fam.Γ v' u'),
      (Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v' u' γ').width =
        (Gt'.fam.identity v' u' γ').record.width ∧
      (Gt'.fam.identity v' u' γ').record.length ≤ D.eps (M - 1 - 1) := by
    intro v' u' γ'
    have hm := (hHT v' u' γ').1
    obtain ⟨hprv, -⟩ := hprov v' u' γ'
    have hg := succSource_tags_good (A.Pt D Cw cr M) (kw := termKW D A.σw cr A.tT M)
      (L := D.eps (M - 1 - 1)) hgood (fun b => rfl) (fun b => hρ) Gw.level (e v' u' γ').1
    rw [← hprv] at hg
    obtain ⟨-, -, -, hlen, hwid, -⟩ := hm
    refine ⟨?_, ?_⟩
    · unfold GenStage.kernelOf
      obtain ⟨hg1, -⟩ := hg
      rw [hwid]
      generalize ((Gt'.prov v' u' γ').tags (A.Pt D Cw cr M)).kernel = key at hg1 ⊢
      cases key
      · exact hg1
      · exact hg1
    · rw [hlen]; exact hg.2
  intro v u γ
  exact hall ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The identity price at one context, from the uniform identity price.**

`UnifPriceAt` is the conclusion of `uniform_native_identity_kernel_price` at `hr = ScalarH` for a
fixed order `n`, with its constant `A` and starting level `m₀`. `retainedPrice_ctx` applies it to
the retained stage `Gt'.retained M 1 R_T` of a terminal passage context: the record-width
equality turns the kernel widths into record widths, the diffusivity `κ_{M-1}` is `kap`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- The conclusion of `uniform_native_identity_kernel_price` at `hr = ScalarH`. -/
def UnifPriceAt (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (bw : ℝ) (n Dm : ℕ) (c : ℕ → ℝ) (A : ℝ) (m₀ : ℕ) :
    Prop :=
  ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (j₀ M : ℕ) (G : GenStage D ScalarH Dm bw j₀) (k : InvConsts),
    G.IsContextCertified k → G.IsNatural M → m₀ + 1 ≤ G.level →
    ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
    0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
    G.IsSlotTransverse → ∀ (a b : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u),
    0 ≤ compReserve k v.1 → compReserve k v.1 ≤ 2 →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
    (3 ≤ (G.fam.identity v u γ).maxOrder →
      (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
    (∑ d : ↥(Finset.Icc 2 Dm),
      ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
        (D.kap G.level * (G.fam.identity v u γ).record.width ^ (d.1 - 2))) ≤
      A * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
        constituentPrice (G.fam.identity v u γ).record)

/-- **The identity price at one context.** -/
theorem retainedPrice_ctx {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kS : InvConsts} {kW : InvConsts} {cP CP cH Cw C : ℝ} {j₀ M : ℕ}
    {D : OCData} {a : ℝ} {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀}
    {aM tp : ℝ} {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hA : A.Valid) (hΛ : 128 ≤ A.Λ) (hcr : 0 < cr) (hG : Gt'.IsContextCertified kW)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hGH : kW.G0 ≤ kW.Hprod)
    (hrho : D.termRho cr M ≤ D.eps (M - 1)) (hCL : CL * D.eps (M + 1) ≤ D.eps (M - 1))
    (hk : ∀ kk ≤ A.Khat Kout, ∃ Ak : ℝ, 0 ≤ Ak ∧ Ak ≤ C ∧ ∃ m₀ : ℕ, m₀ + 2 ≤ M ∧
      UnifPriceAt X.α X.q A.Λ X.ζ A.bw kk A.Dt kS.cker Ak m₀) :
    (∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u),
      ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr)
        v u γ).width = ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.width) ∧
    ∀ kk ≤ A.Khat Kout, ∀ v u (γ : (Gt'.retained M 1 A.RT).fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 A.Dt),
        (coefficientSeminorm (D.termRho cr M) kk tp (a + A.T₀)
          ((Gt'.retained M 1 A.RT).physCoeff v u γ d.1)).toReal * kS.cker (d.1 - 2) /
          (D.κ (M - 1) * ((Gt'.retained M 1 A.RT).kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW)
            (A.Kn_ D M cr) v u γ).width ^ (d.1 - 2))) ≤
        C * (‖((Gt'.retained M 1 A.RT).fam.identity v u γ).map‖ *
          ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size *
          constituentPrice ((Gt'.retained M 1 A.RT).fam.identity v u γ).record) := by
  have hbase := retainedBase_of_passCtx hctx hA hΛ hcr hCH hΥ hcar hX hZ hj hM2 hGH hrho
  obtain ⟨hpar, ⟨Mn, hnat⟩, -, hΛ1, hi, hjl, hb0, hε, hm, hm2, hρ0, hρε⟩ := hbase
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := hctx.1
  have hweak := hctx.2.1
  have hsucc := hctx.2.2.2.2.2.2
  have hlevW : Gw.level = M := hweak.2.2.1
  have hlev : Gt'.level = M - 1 := by rw [hsucc.2.1, hlevW]
  have hq1 : 1 < D.q := by rw [hq]; exact X.hq.1
  have hΛD128 : 128 ≤ D.Λ := by rw [hΛD]; exact hΛ
  have hρε' : D.termRho cr M ≤ D.eps (M - 1 - 1) := by
    change D.termRho cr M ≤ D.eps (Gt'.level - 1) at hρε
    rw [hlev] at hρε
    exact hρε
  have hWL := retained_width_length hctx hq1 hΛD128 hCL hρε'
  have hcertGr := (hG.retained M 1 A.RT).2
  have hlevGr : (Gt'.retained M 1 A.RT).level = M - 1 := hlev
  have hκ : 0 < D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hkap : D.kap (Gt'.retained M 1 A.RT).level = D.κ (M - 1) := by
    unfold OCData.kap
    rw [hlevGr, Nat.min_eq_left (by rw [hterm]; omega)]
  have hE : ∀ i, 0 < D.eps i := fun i => Construction.Stream.ocEpsilon_pos hΛ1
  refine ⟨fun v u γ => (hWL v u γ).1, ?_⟩
  intro kk hkk v u γ
  obtain ⟨Ak, hAk0, hAkC, m0, hm0, hu⟩ := hk kk hkk
  have hν : 0 < D.kap (Gt'.retained M 1 A.RT).level := by rw [hkap]; exact hκ
  have hρ2 : D.termRho cr M ≤ D.eps (Gt'.retained M 1 A.RT).level := by
    rw [hlevGr]; exact hrho
  have hlen : 3 ≤ ((Gt'.retained M 1 A.RT).fam.identity v u γ).maxOrder →
      ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.length ≤
        D.eps ((Gt'.retained M 1 A.RT).level - 1) := fun _ =>
    le_of_le_of_eq (hWL v u γ).2 (by rw [hlevGr])
  have hsum := hu D hα hq hΛD hζD hseq j₀ Mn (Gt'.retained M 1 A.RT) kW hcertGr hnat
    (by rw [hlevGr]; omega) hi hjl (hE _) (hE _) hν hpar tp (a + A.T₀) v u γ (hm v) (hm2 v)
    (D.termRho cr M) hρ0 hρε hρ2 hlen
  have hZ0 : 0 ≤ ‖((Gt'.retained M 1 A.RT).fam.identity v u γ).map‖ *
      ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size *
      constituentPrice ((Gt'.retained M 1 A.RT).fam.identity v u γ).record :=
    mul_nonneg (mul_nonneg (norm_nonneg _) ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.size_nonneg)
      (AVRegularity.Construction.Preservation.FullLift.constituentPrice_nonneg _)
  calc _ = ∑ d : ↥(Finset.Icc 2 A.Dt),
        ((coefficientSeminorm (D.termRho cr M) kk tp (a + A.T₀)
          ((Gt'.retained M 1 A.RT).physCoeff v u γ d.1)).toReal * kS.cker (d.1 - 2)) /
          (D.kap (Gt'.retained M 1 A.RT).level *
            ((Gt'.retained M 1 A.RT).fam.identity v u γ).record.width ^ (d.1 - 2)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [(hWL v u γ).1, hkap]
    _ ≤ Ak * _ := hsum
    _ ≤ C * _ := mul_le_mul_of_nonneg_right hAkC hZ0

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The marked ledger of the retained terminal successor under the terminal law.**

`termRetained_ledger_le`: at a terminal passage context, the marked ledger of
`Gt'.retained M 1 R_T` under `lawT` is at most
`4 (T+1)(C_w+1) S + 2 (T+1)(L+1)(C_w+1) R`, with `S = Cχ ε_M^{χ_w}` the ledger of the weak stage
(which is the same under `lawT` and `lawW`: the weak components have no births) and
`R = (1 + √(|𝔚|/c_H)) ε_{M-1}^{θ_T - η₀/4}` the fresh part. Hypotheses: `1 ≤` the birth diagonal
factors, and the smallness `2 (T+1)(C_w+1) S ≤ 1/2` (both hold for `M` large). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Preservation.Ledger
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Route

/-- The fresh-letter prefactor bound, for both diagonals. -/
theorem birth_bound_any {D : OCData} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (law : BirthLaw)
    (hi : 0 ≤ law.iota) (m : ℕ) {θ₁ θ₂ : ℝ} (hθ : θ₁ = θ₂ - law.etaB / 2 - law.iota)
    (marked : Bool) :
    birthDiagonalFactor D.q D.Λ m law marked * D.eps (m - 1) ^ θ₂ ≤
      (1 + Real.sqrt ((law.wordCount : ℝ) / law.cH)) * D.eps (m - 1) ^ θ₁ := by
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq hΛ
  have hb := birthDiagonalFactor_le hq hΛ m law marked hi
  have hmul := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg he.1.le θ₂)
  have hsq := Real.sqrt_nonneg ((law.wordCount : ℝ) / law.cH)
  have hpow : 0 ≤ D.eps (m - 1) ^ θ₁ := Real.rpow_nonneg he.1.le _
  have hexp : ocEpsilon D.q D.Λ (m - 1) ^ (-law.etaB / 2 - law.iota) * D.eps (m - 1) ^ θ₂ =
      D.eps (m - 1) ^ θ₁ := by
    show ocEpsilon D.q D.Λ (m - 1) ^ (-law.etaB / 2 - law.iota) *
      ocEpsilon D.q D.Λ (m - 1) ^ θ₂ = ocEpsilon D.q D.Λ (m - 1) ^ θ₁
    rw [← Real.rpow_add he.1]
    congr 1; rw [hθ]; ring
  calc _ ≤ Real.sqrt ((law.wordCount : ℝ) / law.cH) *
        ocEpsilon D.q D.Λ (m - 1) ^ (-law.etaB / 2 - law.iota) * D.eps (m - 1) ^ θ₂ := hmul
    _ = Real.sqrt ((law.wordCount : ℝ) / law.cH) * D.eps (m - 1) ^ θ₁ := by
        rw [mul_assoc, hexp]
    _ ≤ _ := by nlinarith

/-- The weak ledger does not see the law beyond the root masses (no births). -/
theorem weak_ledger_lawT {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {Gw : GenStage D ScalarH Dm b j₀} {lawW lawT : BirthLaw} {S : ℝ}
    (hbirths : ∀ v : CompIn Gw.comps, v.1.births = [])
    (hmass : lawT.rootMass = lawW.rootMass)
    (hled : markedLedger (Gw.mass lawW) (Gw.marker lawW) Gw.fam ≤ S) :
    markedLedger (Gw.mass lawT) (Gw.marker lawT) Gw.fam ≤ S := by
  have h1 : Gw.mass lawT = Gw.mass lawW := by
    funext v
    simp [GenStage.mass, compMass, hbirths v, hmass]
  have h2 : Gw.marker lawT = Gw.marker lawW := by
    funext v
    simp [GenStage.marker, compMarker, compBirthSet, hbirths v]
  rw [h1, h2]
  exact hled

/-- **The marked ledger of the retained terminal successor under `lawT`.** -/
theorem termRetained_ledger_le {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hA : A.Valid) (hΛ : 128 ≤ A.Λ) (hCw : 0 ≤ Cw)
    (hF1 : ∀ marked, 1 ≤ birthDiagonalFactor D.q D.Λ M lawT marked)
    (hsmall : AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo A.alph (A.RT + 1)).card * max (Cχ * D.eps M ^ A.χw) 0 ≤ 1 / 2) :
    markedLedger ((Gt'.retained M 1 A.RT).mass lawT) ((Gt'.retained M 1 A.RT).marker lawT)
        (Gt'.retained M 1 A.RT).fam ≤
      4 * (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * (Cw + 1) *
          max (Cχ * D.eps M ^ A.χw) 0 +
        2 * (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * ((A.alph.card : ℝ) + 1) * (Cw + 1) *
          ((1 + Real.sqrt ((lawT.wordCount : ℝ) / lawT.cH)) *
            D.eps (M - 1) ^ (ocDelta X.α X.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ) -
              A.η₀ / 4)) := by
  obtain ⟨hdata, hweak, -, -, -, hlaw, hsucc⟩ := hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hdata
  obtain ⟨-, -, hlev, -, hbirths, ⟨hseedprov, -, -⟩, -, -, -, hinv⟩ := hweak
  obtain ⟨hmass, -, -, hiota, -, hetaB, -⟩ := hlaw
  obtain ⟨-, htags, -, -, -, -, -, hled, -⟩ := hinv
  have hq1 : 1 < D.q := by rw [hq]; exact X.hq.1
  have hΛ128 : 128 ≤ D.Λ := by rw [hΛD]; exact hΛ
  obtain ⟨-, -, -, -, -, hsched, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  have hPeq : A.Pt D Cw cr M = genProvParams D Cw A.η₀ A.NT A.pT
      (fun _ => D.termRho cr M) (fun _ => D.termRNew cr A.tT M) :=
    termProvParams_eq_gen D Cw cr A.tT A.η₀ A.NT A.pT M
  rw [hPeq] at hsucc
  have hG : Gw.HasTags (genProvParams D Cw A.η₀ A.NT A.pT
      (fun _ => D.termRho cr M) (fun _ => D.termRNew cr A.tT M)) :=
    hasTags_of_seed_prov hseedprov htags
  have hold : ∀ v ∈ Gw.comps, ∀ e ∈ v.births, Gw.level ≤ e.scale := by
    intro v hv e he
    have h0 : v.births = [] := hbirths ⟨v, hv⟩
    rw [h0] at he
    exact absurd he (by simp)
  have hrb : (fun _ => D.termRNew cr A.tT M) (Gw.level - 1) =
      (fun _ => D.termRho cr M) (Gw.level - 1) * D.eps (Gw.level - 1) ^ A.tT := by
    rw [hlev]; rfl
  have hbirth : ∀ marked, birthDiagonalFactor D.q D.Λ Gw.level lawT marked *
      D.eps (Gw.level - 1) ^ (ocDelta D.α D.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ)) ≤
      (1 + Real.sqrt ((lawT.wordCount : ℝ) / lawT.cH)) *
        D.eps (Gw.level - 1) ^ (ocDelta X.α X.q - A.η₀ -
          A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4) := by
    intro marked
    refine birth_bound_any hq1 hΛ128 lawT (by rw [hiota]) Gw.level ?_ marked
    rw [hα, hq, hetaB, hiota]; ring
  have hled' : markedLedger (Gw.mass lawT) (Gw.marker lawT) Gw.fam ≤
      max (Cχ * D.eps M ^ A.χw) 0 :=
    (weak_ledger_lawT hbirths hmass hled).trans (le_max_left _ _)
  have hgen := retained_ledger_recurrence_gen (G := Gw) (G' := Gt') (Mn := A.Mt M sXT sZT tp cr)
    (H := 1) (J := A.RT) hq1 hΛ128 hCw htT.le hrb
    (fun l hl => termFresh_letters l hl) lawT (fun marked => by rw [hlev]; exact hF1 marked)
    hbirth hG (fun v hv e he => hold v hv e he) hsucc (le_max_right _ _) hled' hsmall
  rw [hlev] at hgen
  exact hgen

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **Smallness of the retained ledger for large `M`** (the last step of the priced Schur bound).

`small_core` is the scale arithmetic: for fixed positive exponents `χ, θ, η` and constants,
three powers of `ε` are eventually small. The ledger bound of `termRetained_ledger_le` then gives
`SchurBound (1/(8C))` of the priced record majorant. For `C_χ ≤ 0` the weak ledger is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Route

/-- Three eventual smallness statements for the scales `ε_M^χ`, `ε_{M-1}^θ`, `ε_{M-1}^η`. -/
theorem small_core {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {χ θ η : ℝ} (hχ : 0 < χ)
    (hθ : 0 < θ) (hη : 0 < η) (K1 K2 Cχ C cH : ℝ) (wc : ℕ) (hK1 : 0 < K1) (hK2 : 0 < K2)
    (hC : 1 ≤ C) (hcH : 0 < cH) (hwc : 0 < wc) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      cH / (wc : ℝ) * ocEpsilon q Λ (M - 1) ^ η ≤ 1 ∧
      K1 * ((|Cχ| + 1) * ocEpsilon q Λ M ^ χ) ≤ 1 / (16 * C) ∧
      K2 * ocEpsilon q Λ (M - 1) ^ θ ≤ 1 / (16 * C) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hwc' : (0 : ℝ) < wc := by exact_mod_cast hwc
  obtain ⟨Ma, hMa⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq hΛ hχ
    (c := 1 / (16 * C * K1 * (|Cχ| + 1))) (by positivity)
  obtain ⟨Mb, hMb⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq hΛ hθ
    (c := 1 / (16 * C * K2)) (by positivity)
  obtain ⟨Mc, hMc⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq hΛ hη
    (c := (wc : ℝ) / cH) (by positivity)
  refine ⟨max Ma (max (Mb + 1) (Mc + 1)), fun M hM => ?_⟩
  have h1 : Ma ≤ M := le_trans (le_max_left _ _) hM
  have h2 : Mb + 1 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have h3 : Mc + 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  refine ⟨?_, ?_, ?_⟩
  · have := hMc (M - 1) (by omega)
    calc cH / (wc : ℝ) * ocEpsilon q Λ (M - 1) ^ η ≤ cH / (wc : ℝ) * ((wc : ℝ) / cH) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := by field_simp
  · have := hMa M h1
    have hA1 : 0 < |Cχ| + 1 := by positivity
    calc K1 * ((|Cχ| + 1) * ocEpsilon q Λ M ^ χ)
        ≤ K1 * ((|Cχ| + 1) * (1 / (16 * C * K1 * (|Cχ| + 1)))) := by
          gcongr
      _ = 1 / (16 * C) := by field_simp
  · have := hMb (M - 1) (by omega)
    calc K2 * ocEpsilon q Λ (M - 1) ^ θ ≤ K2 * (1 / (16 * C * K2)) := by gcongr
      _ = 1 / (16 * C) := by field_simp

/-- The birth diagonal factor is at least `1` when `ι = 0` and `(c_H/|𝔚|) ε^{η_b} ≤ 1`. -/
theorem birthFactor_ge_one {q : ℝ} {Λ M : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (law : BirthLaw)
    (hi : law.iota = 0)
    (hx : law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (M - 1) ^ law.etaB ≤ 1)
    (marked : Bool) :
    1 ≤ AVRegularity.Construction.Preservation.Ledger.birthDiagonalFactor q Λ M law marked := by
  have he := AVRegularity.Scales.epsilon_basic (m := M - 1) hq hΛ
  have hwc : (0 : ℝ) < law.wordCount := by exact_mod_cast law.wordCount_pos
  have hpos : 0 < law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (M - 1) ^ law.etaB :=
    mul_pos (div_pos law.cH_pos hwc) (Real.rpow_pos_of_pos he.1 _)
  have hsq : 0 < Real.sqrt (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (M - 1) ^ law.etaB) :=
    Real.sqrt_pos.2 hpos
  have hsq1 : Real.sqrt (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (M - 1) ^ law.etaB) ≤ 1 :=
    Real.sqrt_le_one.2 hx
  have hnum : (if marked = true then ocEpsilon q Λ (M - 1) ^ (-law.iota) else 1) = 1 := by
    split_ifs
    · rw [hi]; simp
    · rfl
  unfold AVRegularity.Construction.Preservation.Ledger.birthDiagonalFactor
  rw [hnum]
  exact one_le_one_div hsq hsq1

end AVRegularity.EntryTerminal.Route
end
end

section
/-! The two strict exponent gaps turn retained-ledger decay into seed-ledger decay. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryTerminal.Route

/-- A fixed multiple of a parent-scale power with a larger exponent is eventually small
relative to the requested seed power. -/
theorem parent_power_small {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    {θ τ : ℝ} (hgap : τ < θ) (K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      K * ocEpsilon q Λ (M - 1) ^ θ ≤ c * ocEpsilon q Λ (M - 1) ^ τ := by
  obtain ⟨N, hN⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq hΛ
    (sub_pos.mpr hgap) (c := c / (|K| + 1)) (by positivity)
  refine ⟨N + 1, fun M hM => ?_⟩
  have he := (Scales.epsilon_basic (m := M - 1) hq hΛ).1
  have hn := hN (M - 1) (by omega)
  have hprod : K * ocEpsilon q Λ (M - 1) ^ (θ - τ) ≤ c := calc
    _ ≤ (|K| + 1) * ocEpsilon q Λ (M - 1) ^ (θ - τ) :=
      mul_le_mul_of_nonneg_right (le_trans (le_abs_self K) (by linarith only []))
        (Real.rpow_nonneg he.le _)
    _ ≤ (|K| + 1) * (c / (|K| + 1)) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = c := by field_simp
  have hp : ocEpsilon q Λ (M - 1) ^ θ =
      ocEpsilon q Λ (M - 1) ^ (θ - τ) * ocEpsilon q Λ (M - 1) ^ τ := by
    rw [← Real.rpow_add he]; congr 1; ring
  rw [hp, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg he.le _)

/-- The weak-scale term gains the factor `q` in its exponent. -/
theorem child_power_small {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hq16 : q < 17 / 16)
    (hΛ : 128 ≤ Λ) {χ τ : ℝ} (hχ : 0 < χ) (hgap : τ < q * χ)
    {K : ℝ} (hK : 0 ≤ K) {c : ℝ} (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      K * ocEpsilon q Λ M ^ χ ≤ c * ocEpsilon q Λ (M - 1) ^ τ := by
  obtain ⟨N, hN⟩ := parent_power_small hq hΛ hgap (K * (2 : ℝ) ^ χ) hc
  refine ⟨max N 1, fun M hM => ?_⟩
  have he := (Scales.epsilon_basic (m := M - 1) hq hΛ).1
  have hstep := Scales.epsilon_q_step hq hq16 hΛ ((le_max_right _ _).trans hM)
  have hp := Real.rpow_le_rpow (Scales.epsilon_basic (m := M) hq hΛ).1.le hstep hχ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg he.le _),
    ← Real.rpow_mul he.le] at hp
  exact (mul_le_mul_of_nonneg_left hp hK).trans
    (by rw [← mul_assoc]; exact hN M ((le_max_left _ _).trans hM))

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **`RetainedPricedSchurPart` is proved.** The priced record majorant of the retained
terminal successor is `1/(8C)`-Schur for `M` large: the marked ledger bound of
`termRetained_ledger_le` is at most `1/(8C)` (`small_core`), and
`priced_record_ledger_schur` turns it into the Schur bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Ledger

namespace AVRegularity.EntryTerminal.Route

/-- The arithmetic of the final estimate. -/
theorem bound_arith {T L Cw s C Sw a e Lg : ℝ} (hT : 0 ≤ T) (hCw : 0 ≤ Cw)
    (hC : 1 ≤ C) (hSw : Sw ≤ a)
    (h2 : 4 * (T + 1) * (Cw + 1) * a ≤ 1 / (16 * C))
    (h3 : 2 * (T + 1) * (L + 1) * (Cw + 1) * (1 + s) * e ≤ 1 / (16 * C))
    (hled : Lg ≤ 4 * (T + 1) * (Cw + 1) * Sw + 2 * (T + 1) * (L + 1) * (Cw + 1) * ((1 + s) * e)) :
    Lg ≤ 1 / (8 * C) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have e1 : 4 * (T + 1) * (Cw + 1) * Sw ≤ 4 * (T + 1) * (Cw + 1) * a :=
    mul_le_mul_of_nonneg_left hSw (by positivity)
  have e2 : 2 * (T + 1) * (L + 1) * (Cw + 1) * ((1 + s) * e) =
      2 * (T + 1) * (L + 1) * (Cw + 1) * (1 + s) * e := by ring
  have h8 : 1 / (8 * C) = 1 / (16 * C) + 1 / (16 * C) := by field_simp; ring
  rw [h8]
  linarith

/-- The priced record majorant with unit marker is the explicit matrix. -/
theorem priced_majorant_eq {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {D : OCData}
    (G : GenStage D ScalarH Dm b j₀) (law : BirthLaw) :
    pricedRecordMajorant (fun v => G.mass law v) (fun _ => 1) G.fam =
      (fun v u : CompIn G.comps => Real.sqrt (G.mass law u / G.mass law v) *
        ∑ γ : G.fam.Γ v u, ‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record) := by
  funext v u
  simp only [pricedRecordMajorant, div_one, one_mul]

/-- **The priced Schur bound of the retained family.** -/
theorem retainedPricedSchurPart : RetainedPricedSchurPart := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hA Kout => ⟨0, 0, fun sXT sZT _ _ => ?_⟩⟩
  let F0 : SeedFloors :=
    { cker := fun _ _ => 0
      Γk := fun _ => 0
      Cwid := fun _ => 0
      Ca := fun _ => 0
      Cm := fun _ _ => 0 }
  refine ⟨0, F0, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW halloc cP CP hcP => ?_⟩
  show RetainedPricedSchurBlock A sXT sZT nW cr CL Cχ kW cP CP
  intro cH hcH
  refine ⟨0, 1, 1, le_rfl, le_rfl, one_pos, fun Cw hCw j₀ _ C hC => ?_⟩
  have hA' := hA
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, hχw, hη₀, -⟩, -⟩ := hA'
  have hθ : 0 < ocDelta X.α X.q - A.η₀ - A.tT * (termExcess A.NT A.pT A.alph : ℝ) - A.η₀ / 4 := by
    have h1 := AVRegularity.Construction.Residual.Presentation.termFresh_exponent_facts (A := A) hA
    have h2 : 0 < ocDelta X.α X.q := ocDelta_pos_of_admissible X.hα₀ X.hq
    linarith
  have hwc : 0 < max 1 A.nWords := lt_of_lt_of_le one_pos (le_max_left _ _)
  set T : ℝ := ((wordsUpTo A.alph (A.RT + 1)).card : ℝ) with hT
  set L : ℝ := (A.alph.card : ℝ) with hL
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hCw1 : 0 < Cw + 1 := by linarith
  have hsq : 0 ≤ Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH) := Real.sqrt_nonneg _
  obtain ⟨M₁, hM₁⟩ := small_core X.hq.1 (Nat.le_trans hΛ le_rfl) hχw hθ (half_pos hη₀)
    (4 * (T + 1) * (Cw + 1))
    (2 * (T + 1) * (L + 1) * (Cw + 1) * (1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cH)))
    Cχ C cH (max 1 A.nWords) (by positivity) (by positivity) hC hcH hwc
  refine ⟨M₁, fun M hM => ?_⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hG
  have hctx' := TermPassCtx.of_seedCtx hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx'.1
  obtain ⟨-, -, hcHeq, hiota, hwcEq, hetaB, -⟩ := hctx'.2.2.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := hM₁ M hM
  have hq1 : 1 < D.q := by rw [hq]; exact X.hq.1
  have hΛ128 : 128 ≤ D.Λ := by rw [hΛD]; exact hΛ
  have hepsM : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hq, hΛD]
  have hepsM1 : D.eps (M - 1) = ocEpsilon X.q A.Λ (M - 1) := by simp only [OCData.eps, hq, hΛD]
  have hF1 : ∀ marked, 1 ≤ birthDiagonalFactor D.q D.Λ M lawT marked := by
    intro marked
    refine birthFactor_ge_one hq1 hΛ128 lawT hiota ?_ marked
    rw [hcHeq, hwcEq, hetaB, hq, hΛD]
    exact h1
  have hSw : max (Cχ * D.eps M ^ A.χw) 0 ≤ (|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw := by
    rw [hepsM]
    have he : 0 ≤ ocEpsilon X.q A.Λ M ^ A.χw :=
      Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 hΛ).1.le _
    refine max_le ?_ (by positivity)
    nlinarith [le_abs_self Cχ, abs_nonneg Cχ]
  have hsmall : AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant Cw
      (wordsUpTo A.alph (A.RT + 1)).card * max (Cχ * D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    have hSw0 : 0 ≤ max (Cχ * D.eps M ^ A.χw) 0 := le_max_right _ _
    have hTc : AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant Cw
        (wordsUpTo A.alph (A.RT + 1)).card ≤ 4 * (T + 1) * (Cw + 1) := by
      unfold AVRegularity.Construction.Preservation.Assembly.ledgerTransportConstant
      rw [hT]; nlinarith
    have hC16 : 1 / (16 * C) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc _ ≤ (4 * (T + 1) * (Cw + 1)) * ((|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw) :=
          mul_le_mul hTc hSw hSw0 (by positivity)
      _ ≤ 1 / (16 * C) := h2
      _ ≤ 1 / 2 := hC16
  have hled := termRetained_ledger_le hctx' hA hΛ hCw hF1 hsmall
  rw [hwcEq, hcHeq] at hled
  have hbound : markedLedger ((Gt'.retained M 1 A.RT).mass lawT)
      ((Gt'.retained M 1 A.RT).marker lawT) (Gt'.retained M 1 A.RT).fam ≤ 1 / (8 * C) := by
    rw [hepsM1] at hled
    exact bound_arith hT0 hCw hC hSw h2 h3 hled
  have hπ : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, 0 < (Gt'.retained M 1 A.RT).mass lawT v :=
    fun v => AVRegularity.Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛ128 lawT v.1
  have hw : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, 0 < (Gt'.retained M 1 A.RT).marker lawT v :=
    fun v => AVRegularity.Construction.Preservation.Buffer.birth_compMarker_pos hq1 hΛ128 lawT v.1
  have h := (AVRegularity.Construction.Preservation.FullLift.priced_record_ledger_schur
    (Gt'.retained M 1 A.RT).fam ((Gt'.retained M 1 A.RT).mass lawT)
    ((Gt'.retained M 1 A.RT).marker lawT) hπ hw (1 / (8 * C)) hbound).1
  exact (priced_majorant_eq _ _).symm ▸ h

end AVRegularity.EntryTerminal.Route
end
end
end
