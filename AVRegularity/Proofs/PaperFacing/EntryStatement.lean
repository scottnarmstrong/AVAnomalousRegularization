-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.Basic
import AVRegularity.Proofs.PaperFacing.Parameters
import AVRegularity.Finite.StrongEntry.SeedRepresentation
import AVRegularity.Proofs.Results.Finite.TerminalSeedTransport
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Construction.Stream.NextAdmissible

/-! # The entry statement (Proposition 4.1 of the paper follows from it)

At the parameter choice of the finite assembly (`FiniteAssemblyReady`, whose `base` identifies
`cfg.α = α`, `cfg.s = s`, `cfg.q = q`, `cfg.ζ = ζ`, `cfg.Λ = Λ`, `cfg.Jw = J`, `cfg.t₀ = t₀`,
`cfg.T₀ = T`): for every `M ≥ M_*`, every `D : OCData` for `(α, q, Λ, ζ)` with a stream sequence
and a band chain of terminal level `M`, every weak tag parameter `PW` and every `a`, there are the
entry witnesses with their defining clauses (`PaperEntryWitnessClauses`, verbatim from
`EntryLevelStatement`), `t_e ∈ [a, a + t₀/4]` and a seed which is an admissible seed of level
`M - 1` on `[t_e, a + T]` (`IsPaperSeed`, for every successor law with the seed's roots and every
fresh kernel family), such that for every `f ∈ L²` and every weak solution `θ` of the truncated
problem from `f` at `a`, with the weak reduction of `θ` and its paired solution `V`
(`IsWeakReduction`, `IsWeakPaired`):

* `PaperEntryE1` (E1): a datum `g` of the seed with `‖g‖_π ≤ C‖f‖₂` such that the solution `U` of
  the seed from `g` at `t_e` exists, and for every such solution, every `t ∈ [a + t₀/4, a + T]`
  and every representation `r` of `U(t)` at `ε_{M-1}` (order `K`) of size at most `X`,
  `‖θ(t)‖_{C^s} ≤ C(X + ‖f‖₂)` (for the periodic representative `Θ_t` of `θ(t)`);
* `PaperEntryE2` (E2): with `Z` the terminal solution (from the terminal trace of
  `Π_term V(a_M)`) whose order-0 truncation is `U`, for every
  lifted field `aRep` of `Z` (which exists) and every `t ∈ [a + t₀/4, a + T]`: the identity
  `‖Θ_t - 𝒲_w(T_M P_{p_T} 𝖱_T Z(t))‖_{C^s} ≤ C(ε_M² + ε_{M-1}²)‖f‖₂`, and every representation `r`
  of `U(t)` at `ε_{M-1}` is carried by the terminal lift to a representation `r_T` at `ε_M` of the
  lower order `J N_w + 3` and by the `J` weak lifts to a representation `r_W` at `ε_{M+J}` of
  order `3` whose `𝒲_w`-readout is `𝒲_w(T_M P_{p_T} 𝖱_T Z(t))`, each of size at most `C X(r)`.

`paper_entry_of_ready` proves this for every finite-assembly parameter choice
(`FiniteAssemblyReady`); `paper_entry` is the statement at the parameters of the finite
assembly. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- The order of the terminal family `Z` of the entry. -/
abbrev paperTermOrder (cfg : FiniteParameters) : ℕ :=
  max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))

/-- The floor (14.7) is below the terminal output order: `B ≤ k₀ ≤ 2k₀ + 2 ≤ N_oe`. -/
theorem paper_term_floor_le_order {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    paperTermFloor P.ready.cfg ≤ paperTermOrder P.ready.cfg :=
  P.term_floor.trans ((by omega : P.ready.cfg.k₀ ≤ 2 * P.ready.cfg.k₀ + 2).trans
    ((le_max_left _ _).trans (le_max_right _ _)))

/-- **(E1)** For the entry seed `seed` (roots `rootM, rootR`, seed kernels `seedKc`) at
`t_e = te`, the datum `g` and the weak solution `θ` from `f`: `‖g‖_π ≤ C‖f‖₂` for every law with
the seed's roots; the solution `U` of the seed from `g` at `t_e` exists; and every solution `U`,
time `t ∈ [a + t₀/4, a + T]`, bound `X ≥ 0` and representation `r` of `U(t)` at `ε_{M-1}` of order
`K` and size at most `X` give `Θ_t = θ(t)` a.e., periodic, with `‖Θ_t‖_{C^s} ≤ C(X + ‖f‖₂)`. -/
def PaperEntryE1 (cfg : FiniteParameters) (C : ℝ) {D : OCData} (M : ℕ) (a te : ℝ)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (rootM rootR : ℕ → ℝ)
    (seedKc : ℕ → KernelSpec) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root)) : Prop :=
  (∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    weightedNorm 1 (seed.mass law) (fun _ => 1) g ≤ C * Real.sqrt (l2NormSq f)) ∧
  ∀ freshK : ℕ → KernelSpec,
    (∃ (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
        (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
        (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
          TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
    ∀ (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    ∀ t ∈ Set.Icc (a + cfg.t₀ / 4) (a + cfg.T₀), ∀ X : ℝ, 0 ≤ X →
    ∀ r : Representation (CompSpace seed.comps),
      IsRepresentationAt (D.eps (M - 1)) (paperRepOrder cfg) r →
      IsRepOf (seed.mass law) (fun w => U w t) r.value →
      representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r ≤ ENNReal.ofReal X →
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe cfg.s Θt (C * (X + Real.sqrt (l2NormSq f)))

/-- **(E2)** The identity and the lift costs, for the entry seed and datum of (E1), the weak
construction `stage` with its readouts `W` and root reindexing `ιw` onto the weak family `Gw`
(law `lawW`), the terminal preparation time `tp`, the terminal successor `Gt'` with its seed
re-rooting `ι`, the weak paired solution `V`, and the terminal solution `Z`: `Z` solves the
retained terminal system from the terminal trace of `Π_term V(a_M)` at `t_p`; every seed solution
`U` is the order-0 truncation of `Z` on `[t_e, a + T]`; a lifted field of `Z` exists; and for every lifted field `aRep` and every
`t ∈ [a + t₀/4, a + T]`: `‖Θ_t - 𝒲_w(T_M P_{p_T} 𝖱_T Z(t))‖_{C^s} ≤ C(ε_M² + ε_{M-1}²)‖f‖₂`, and
every representation `r` of `U(t)` at `ε_{M-1}` of order `K` yields `r_T` at `ε_M` (order
`J N_w + 3`) with value `T_M P_{p_T} 𝖱_T Z(t)` and `r_W` at `ε_{M+J}` (order `3`) whose
`𝒲_w`-readout is `𝒲_w(T_M P_{p_T} 𝖱_T Z(t))`, of sizes at most `C X(r)`. -/
def PaperEntryE2 (cfg : FiniteParameters) (C : ℝ) {D : OCData} (M : ℕ) (a te : ℝ)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (rootM rootR : ℕ → ℝ)
    (seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (lawW : BirthLaw)
    (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (aM tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
    (g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
      TorusHk (paperTermOrder cfg) (ScalarH v.1.root)) : Prop :=
  (∃ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps,
        TorusHk (paperTermOrder cfg) (ScalarH v.1.root))
      (Zw : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
        TorusHk (paperTermOrder cfg + 1) (ScalarH v.1.root))
      (Zk : ∀ v u (_ : (Gt'.retained M 1 cfg.RT).fam.Γ v u), ℝ →
        TorusHk (paperTermOrder cfg + paperOrderBound cfg - 1) (ScalarH u.1.root)),
    IsTerminalTrace Gw (Gt'.retained M 1 cfg.RT) (Pterm fun v => V v aM) Z₀ ∧
    (Gt'.retained M 1 cfg.RT).IsRegSolution (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
      (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
      (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT) cfg.φ₀ cfg.hφ₀ (D.termB M)
      (streamVel (D.Φ (M - 1))) (paperTermOrder cfg) tp (a + cfg.T₀) Z₀ (fun _ _ => 0)
      (fun _ _ => 0) Z Zw Zk) ∧
  (∀ (freshK : ℕ → KernelSpec) (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      ∀ w, ∀ t ∈ Set.Icc te (a + cfg.T₀),
        U w t = truncateTorusHk (Nat.zero_le _) (Z (ι.symm w) t)) ∧
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (paperTermOrder cfg - 2 * cfg.pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw (Gt'.retained M 1 cfg.RT) M cfg.pT (paperTermOrder cfg) cfg.NT
      (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp (a + cfg.T₀) cfg.cr Z CcT PZ aRep û) ∧
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (paperTermOrder cfg - 2 * cfg.pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw (Gt'.retained M 1 cfg.RT) M cfg.pT (paperTermOrder cfg) cfg.NT
      (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp (a + cfg.T₀) cfg.cr Z CcT PZ aRep û →
  ∀ t ∈ Set.Icc (a + cfg.t₀ / 4) (a + cfg.T₀),
    (∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe cfg.s (fun x => Θt x - W M t (fun v x' =>
          termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t x' (ιw v)) x)
        (C * (D.eps M ^ 2 + D.eps (M - 1) ^ 2) * Real.sqrt (l2NormSq f))) ∧
    ∀ (freshK : ℕ → KernelSpec) (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    ∀ r : Representation (CompSpace seed.comps),
      IsRepresentationAt (D.eps (M - 1)) (paperRepOrder cfg) r →
      IsRepOf (seed.mass law) (fun w => U w t) r.value →
      ∃ (rT : Representation (CompSpace Gw.comps))
        (rW : Representation (CompSpace (stage (M + cfg.Jw)).comps)),
        IsRepresentationAt (D.eps M) (cfg.Jw * cfg.Nw + 3) rT ∧
        rT.value = compField (Gw.mass lawW)
          (termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) ∧
        representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT ≤
          ENNReal.ofReal C * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r ∧
        IsRepresentationAt (D.eps (M + cfg.Jw)) 3 rW ∧
        (∀ y, compReadoutCLM (fun v => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1)
            (rW.value y) =
          W M t (fun v y' => termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t y' (ιw v))
            y) ∧
        representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
          ENNReal.ofReal C * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r

/-- The defining clauses of the entry witnesses, independent of the datum, verbatim from
`EntryLevelStatement`: the weak construction `stage` (tag parameter `PW`), its encoding `ιw` onto
the weak family `Gw` (law `lawW`), the weak readout lifts `CcR` and the weak readout chain `W`
(the readout `𝒲_w`), the weak stage with start `a_M`; the terminal preparation `(t_p, Π_term)`,
the terminal law `lawT`, the actual terminal successor `Gt'` and the seed re-rooting `ι` of its
retained part onto the seed (roots `rootM, rootR`, seed kernels `seedKc`). -/
def PaperEntryWitnessClauses (cfg : FiniteParameters) {D : OCData} (M : ℕ) (PW : ProvParams)
    (a : ℝ) (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (lawW : BirthLaw)
    (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps) : Prop :=
  IsWeakConstruction D PW (⟨cfg.Nw, cfg.Rw, cfg.sXT, cfg.sZT, cfg.η₀, M + cfg.Jw⟩ : WeakMenu) M
      cfg.Jw (D.termRW cfg.σw M) 0 stage ∧
    IsWeakEncoding cfg.Nw cfg.Jw cfg.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
    (∀ i, M < i → i ≤ M + cfg.Jw →
      IsWeakReadoutLifts i cfg.Nw (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT (stage i) (CcR i)) ∧
    IsWeakReadoutChain M cfg.Jw cfg.Nw 0 cfg.η₀ (fun _ => cfg.Jw * cfg.Rw) stage CcR W ∧
    IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw)
      (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ
      (weakChi cfg.α cfg.q cfg.η₀) Gw aM ∧
    IsTerminalPrepMap M cfg.Kw (paperTermOrder cfg) cfg.c cfg.C Gw aM tp Pterm ∧
    IsTerminalLaw lawW lawT cfg.cH cfg.η₀
      (wordsUpTo (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT).card ∧
    IsActualSuccessor D (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
      (termMenu (M + cfg.Jw) (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
        cfg.RT cfg.NT cfg.pT cfg.sXT cfg.sZT cfg.η₀ tp cfg.cr) Gw Gt' ∧
    IsSeedEncoding (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M) lawT rootM rootR
      (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
      (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT)
      seedKc (Gt'.retained M 1 cfg.RT) seed ι

/-- **The entry statement** at the parameters `cfg`, threshold `M_* = Mstar` and constant `C`
(Proposition 4.1 of the paper follows from it). As in
`EntryLevelStatement`, the weak tag parameter `PW` is arbitrary and precedes the witnesses. -/
def PaperEntryStatement (cfg : FiniteParameters) (Mstar : ℕ) (C : ℝ) : Prop :=
  ∀ M : ℕ, Mstar ≤ M →
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ →
    D.term = M →
  ∀ (PW : ProvParams) (a : ℝ),
  ∃ (te : ℝ) (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (lawW : BirthLaw)
    (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps),
    PaperEntryWitnessClauses cfg M PW a seed rootM rootR seedKc stage Gw lawW ιw aM CcR W tp Pterm
      lawT Gt' ι ∧
    te ∈ Set.Icc a (a + cfg.t₀ / 4) ∧
    (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
    (∃ law : BirthLaw, law.rootMass = rootM ∧ law.rootReadout = rootR ∧
      IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law) ∧
    (∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ freshK : ℕ → KernelSpec,
        IsPaperSeed cfg M (M + cfg.Jw) law seedKc freshK seed (M - 1) te (a + cfg.T₀)) ∧
    ∀ (f : Vec 2 → ℝ), MemL2On unitCube f → ∀ θ : ℝ → Vec 2 → ℝ,
      IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ →
    ∃ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (cfg.Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
        TorusHk (cfg.Kw + paperOrderBound cfg - 1) (ScalarH u.1.root))
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (cfg.Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ →
        TorusHk (cfg.Kw + paperOrderBound cfg - 1) (ScalarH u.1.root))
      (g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
      (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
        TorusHk (paperTermOrder cfg) (ScalarH v.1.root)),
      IsWeakReduction PW cfg.φ₀ cfg.hφ₀ cfg.nW M cfg.Jw cfg.Kw 0 a (a + cfg.T₀) θ stage tq Ur Urw
        Urk ∧
      tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
      IsWeakPaired PW cfg.φ₀ cfg.hφ₀ lawW M cfg.Kw cfg.Lt cfg.nW a cfg.T₀ cfg.σw
        (weakChi cfg.α cfg.q cfg.η₀) cfg.cK cfg.CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
      PaperEntryE1 cfg C M a te seed rootM rootR seedKc f θ g ∧
      PaperEntryE2 cfg C M a te seed rootM rootR seedKc stage Gw lawW ιw W aM tp Pterm Gt' ι f θ
        V g Z

/-! ### Proofs -/

/-- `CsNormLe` is monotone in its bound. -/
private theorem paper_csNormLe_mono {s A B : ℝ} {g : Vec 2 → ℝ} (h : CsNormLe s g A)
    (hAB : A ≤ B) : CsNormLe s g B :=
  fun x y z hyz => (h x y z hyz).trans hAB

/-- The seed start `t_e = t_p + h_M` precedes the end of the window. -/
private theorem paper_entry_sn_le {cfg : FiniteParameters} {D : OCData} {M : ℕ} {a : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} (hΛ : 128 ≤ cfg.Λ) (hDα : D.α = cfg.α)
    (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ) (E : FiniteEntryData cfg D M a f θ) :
    0 ≤ D.termH M ∧ E.tp + D.termH M ≤ a + cfg.T₀ := by
  have hH0 : 0 ≤ D.termH M := by
    unfold OCData.termH
    rw [hDα, hDq, hDΛ]
    exact (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  have h3 : 0 ≤ 3 * ocTau cfg.α cfg.q cfg.Λ (M - 1) :=
    mul_nonneg (by norm_num) (Construction.Stream.ocTau_pos (by omega : 1 ≤ cfg.Λ)).le
  have h4 : 0 ≤ 4 * ocTauPP cfg.α cfg.q cfg.Λ (M - 1) :=
    mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  exact ⟨hH0, by linarith [E.terminal_window]⟩

/-- Existence and identification of the seed solution from `g = (Z(t_e))∘ι⁻¹`, for every
fresh-kernel family, at the cascade's tag parameter. -/
private theorem paper_entry_transport (cfg : FiniteParameters) (hvalid : FiniteLocalValidity cfg)
    (hs₀ : 0 < cfg.s) (hΛ : 128 ≤ cfg.Λ) {M : ℕ} (hbudget : FiniteSeedBudgetLevel cfg M)
    {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ)
    (hDζ : D.ζ = cfg.ζ) (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ)
    (hDterm : D.term = M) {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) (freshK : ℕ → KernelSpec) :
    (∃ (Uw : ∀ w : CompIn E.seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
        (Uk : ∀ w u (_ : E.seed.fam.Γ w u), ℝ →
          TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      E.seed.IsRegSolution (paperProv cfg D) E.seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 (E.tp + D.termH M) (a + cfg.T₀)
        (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M)))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun w t => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) Uw Uk) ∧
    ∀ (U : ∀ w : CompIn E.seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn E.seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : E.seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      E.seed.IsRegSolution (paperProv cfg D) E.seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 (E.tp + D.termH M) (a + cfg.T₀)
        (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M)))
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      ∀ w, ∀ t ∈ Set.Icc (E.tp + D.termH M) (a + cfg.T₀),
        U w t = truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t) := by
  have hη := succEta0_pos_of_admissible hvalid.hα₀ hs₀ hvalid.hq
  have hL := finite_successor_law cfg hη E.rootM E.rootR E.seedClauses.1 E.seedClauses.2.1
  refine hL.elim fun law hlaw => ?_
  have hgenerated := (E.seedClauses.2.2 law hlaw.1 hlaw.2.1).1
  have hsn := paper_entry_sn_le hΛ hDα hDq hDΛ E
  refine E.family.elim fun Z₀ h₁ => h₁.elim fun Zw h₂ => h₂.elim fun Zk hZk => ?_
  have hZ := hZk.2.1
  let R := finite_seed_kernel_operator cfg hvalid M hbudget D hDq hDΛ hDζ hΛ hband hDterm
    law (paperProv cfg D) E.seedKc freshK (E.tp + D.termH M) (a + cfg.T₀) hsn.2 E.seed
    (hgenerated (paperProv cfg D) freshK)
  have hkap : D.kap E.seed.level = D.κ (M - 1) := by
    simp only [OCData.kap, (hgenerated (paperProv cfg D) freshK).1, hDterm,
      min_eq_left (Nat.sub_le M 1)]
  have hν : 0 < D.κ (M - 1) := by rw [← hkap]; exact R.diffusivity_pos
  have hschur := R.hschur
  conv at hschur =>
    arg 2
    arg 1
    rw [hkap]
  exact Providers.terminal_seed_transport (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
    E.lawT E.rootM E.rootR (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
    (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT) E.seedKc cfg.φ₀ cfg.hφ₀
    (E.Gt'.retained M 1 cfg.RT) E.seed E.ι E.seedEncoding M _ E.tp (E.tp + D.termH M)
    (a + cfg.T₀) (by linarith only [hsn.1]) hsn.2 Z₀ E.Z Zw Zk hZ (paperProv cfg D) freshK
    (rhoStar D cfg.kS.c₀ E.seed.level) R.θ R.π R.c R.radius_pos hν R.order_ge_two R.hπ R.hθ
    (fun w u γ d => ⟨R.hB_meas w u γ d, R.hB_smooth w u γ d, R.hB_per w u γ d, R.hB_fin w u γ d⟩)
    (fun w u γ => ⟨R.hr w u γ, R.hS w u γ⟩) hschur

/-- The terminal and weak lifts of a seed-side representation of `Z(t)`. -/
private theorem paper_entry_lift {cfg : FiniteParameters} (hs₀ : 0 < cfg.s) (hs1 : cfg.s < 1)
    {M : ℕ} {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ)
    (hDζ : D.ζ = cfg.ζ) (hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hDterm : D.term = M) {CT CwLift : ℝ}
    (hCw : 0 ≤ CwLift) (hMT : TerminalLiftLevelStatement cfg CT M)
    (hMW : WeakLiftLevelStatement cfg CwLift M) {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn E.Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn E.Gw.comps, ℝ → TorusHk (paperTermOrder cfg - 2 * cfg.pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn E.Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn E.Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hL : IsTerminalLiftedField E.Gw (E.Gt'.retained M 1 cfg.RT) M cfg.pT (paperTermOrder cfg)
      cfg.NT (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ E.tp (a + cfg.T₀) cfg.cr E.Z CcT PZ aRep û)
    (t : ℝ) (ht : t ∈ Set.Icc E.tp (a + cfg.T₀)) (law : BirthLaw) (hroot : law.rootMass = E.rootM)
    (r : Representation (CompSpace E.seed.comps))
    (hr : IsRepresentationAt (D.eps (M - 1)) (paperRepOrder cfg) r)
    (hv : IsRepOf (E.seed.mass law)
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) r.value) :
    ∃ (rT : Representation (CompSpace E.Gw.comps))
      (rW : Representation (CompSpace (E.stage (M + cfg.Jw)).comps)),
      IsRepresentationAt (D.eps M) (cfg.Jw * cfg.Nw + 3) rT ∧
      rT.value = compField (E.Gw.mass E.lawW)
        (termLiftedRep E.Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) ∧
      representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r ∧
      IsRepresentationAt (D.eps (M + cfg.Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1)
          (rW.value y) =
        E.W M t (fun v y' => termLiftedRep E.Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t y'
          (E.ιw v)) y) ∧
      representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
        ENNReal.ofReal (CwLift * CT) * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r := by
  have hmass (v : CompIn (E.Gt'.retained M 1 cfg.RT).comps) :
      E.seed.mass law (E.ι v) = (E.Gt'.retained M 1 cfg.RT).mass E.lawT v := by
    rw [finite_seed_mass E law hroot]
    exact (E.seedEncoding.2.2.1 v).1
  refine (reindex_identified_rep E.ι _ _ hmass _
    (fun v => E.Z v t) (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t))
    (fun v => congrArg (fun u => truncateTorusHk (Nat.zero_le _) (E.Z u t))
      (E.ι.symm_apply_apply v)) cfg.s hs₀ hs1 _ (by change 1 ≤ _ + _ + 4; omega)
      (D.eps (M - 1)) r hr hv).elim fun rT' hT' => ?_
  have hsizeT' := hT'.2.2
  refine (hMT D hDα hDq hDΛ hDζ hDΦ hband hDterm
    E.PW a E.Gw E.lawW E.aM E.weakStage E.tp E.Pterm E.prep E.lawT E.Gt' E.terminalLaw E.actual
    _ E.Z CcT PZ aRep û hL t ht rT' hT'.1 hT'.2.1).elim fun rT hrTall => ?_
  have hrT := hrTall.1
  have hvalueT := hrTall.2.2.2.1
  have hsizeT := hrTall.2.2.2.2
  refine (hMW D hDα hDq hDΛ hDζ hDΦ hband hDterm
    E.PW _ E.stage E.Gw E.lawW E.ιw E.CcR E.W E.construction E.encoding E.lifts E.chain
    t (termLiftedRep E.Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) rT hrT hvalueT).elim
    fun rW hrWall => ?_
  have hrW := hrWall.1
  have hreadout := hrWall.2.1
  have hsizeW := hrWall.2.2
  have hT : representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT ≤
      ENNReal.ofReal CT * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r :=
    hsizeT.trans (mul_le_mul' le_rfl hsizeT')
  refine ⟨rT, rW, hrT, hvalueT, hT, hrW, hreadout, ?_⟩
  calc representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW
      ≤ ENNReal.ofReal CwLift * (ENNReal.ofReal CT *
          representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r) :=
        hsizeW.trans (mul_le_mul' le_rfl hT)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hCw]

/-- The scalar bound of (E1) from a representation `r_W` of the weak lift. -/
private theorem paper_entry_scalar {cfg : FiniteParameters} (hs₀ : 0 < cfg.s) (hs1 : cfg.s < 1)
    {M : ℕ} {D : OCData} {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) (t A B : ℝ) (hA : 0 ≤ A)
    (rW : Representation (CompSpace (E.stage (M + cfg.Jw)).comps))
    (hrW : IsRepresentationAt (D.eps (M + cfg.Jw)) 3 rW)
    (hsize : representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤ ENNReal.ofReal A)
    (g : Vec 2 → ∀ v : CompIn E.Gw.comps, ScalarH v.1.root)
    (hreadout : ∀ y, compReadoutCLM (fun v => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1)
      (rW.value y) = E.W M t (fun v y' => g y' (E.ιw v)) y)
    (Θ : Vec 2 → ℝ) (herr : CsNormLe cfg.s (fun x => Θ x - E.W M t (fun v x' => g x' (E.ιw v)) x) B) :
    CsNormLe cfg.s Θ (3 * A + B) := by
  have hmodel := scalar_rep_readout cfg.s hs₀ hs1 (D.eps (M + cfg.Jw)) A hA rW hrW
    (compReadoutCLM (fun v : CompIn (E.stage (M + cfg.Jw)).comps => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1)
      (fun _ => 1))
    (weak_root_readout_norm D cfg.Nw cfg.Jw cfg.η₀ _ E.construction.2.1.2.1) hsize
  have hsum := csNormLe_add hmodel herr
  have hfun : (fun x => compReadoutCLM (fun v : CompIn (E.stage (M + cfg.Jw)).comps =>
      weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1) (rW.value x) +
      (Θ x - E.W M t (fun v x' => g x' (E.ιw v)) x)) = Θ := by
    funext x
    rw [hreadout x]
    ring
  rw [hfun] at hsum
  exact hsum

/-- The two powers `ε_M^{P_w} + ε_{M-1}^{P_T}` of the identity, at `P_w = P_T = 2`. -/
private theorem paper_entry_pow_le {cfg : FiniteParameters} {D : OCData} {M : ℕ}
    (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) (C₀ C₁ X : ℝ) (hC : |C₀| ≤ C₁) (hX : 0 ≤ X) :
    C₀ * (D.eps M ^ cfg.Pw + D.eps (M - 1) ^ cfg.PT) * X ≤
      C₁ * (D.eps M ^ 2 + D.eps (M - 1) ^ 2) * X := by
  rw [hPw, hPT, Real.rpow_two, Real.rpow_two]
  apply mul_le_mul_of_nonneg_right _ hX
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hC)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The final arithmetic of (E1). -/
private theorem paper_entry_bound_arith (C CwT C₀ X F p : ℝ) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hp2 : p ≤ 2) (h1 : 3 * CwT ≤ C) (h2 : 2 * |C₀| ≤ C) :
    3 * (CwT * X) + |C₀| * p * F ≤ C * (X + F) := by
  have ha : 3 * (CwT * X) ≤ C * X := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 hX
  have hb : |C₀| * p * F ≤ C * F := by
    apply mul_le_mul_of_nonneg_right _ hF
    nlinarith [abs_nonneg C₀]
  linarith

/-- **(E1)** for the entry data (`FiniteEntryData`). -/
private theorem paper_entry_E1 {cfg : FiniteParameters} (hvalid : FiniteLocalValidity cfg)
    (hs₀ : 0 < cfg.s) (hΛ : 128 ≤ cfg.Λ) (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) {M : ℕ}
    (hbudget : FiniteSeedBudgetLevel cfg M) {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q)
    (hDΛ : D.Λ = cfg.Λ) (hDζ : D.ζ = cfg.ζ) (hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hDterm : D.term = M) {CT CwLift C : ℝ}
    (hCT : 0 ≤ CT) (hCw : 0 ≤ CwLift) (hMT : TerminalLiftLevelStatement cfg CT M)
    (hMW : WeakLiftLevelStatement cfg CwLift M) (hC1 : 3 * (CwLift * CT) ≤ C)
    (hC2 : 2 * |cfg.C| ≤ C) (hC3 : |cfg.Centry| ≤ C) {a : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} (E : FiniteEntryData cfg D M a f θ) :
    PaperEntryE1 cfg C M a (E.tp + D.termH M) E.seed E.rootM E.rootR E.seedKc f θ
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M))) := by
  have hs1 : cfg.s < 1 := hvalid.hs₁.trans (by linarith only [hvalid.hα₀])
  have hε (j : ℕ) : 0 ≤ D.eps j ∧ D.eps j ≤ 1 := by
    change 0 ≤ ocEpsilon D.q D.Λ j ∧ ocEpsilon D.q D.Λ j ≤ 1
    rw [hDq, hDΛ]
    exact ⟨ocEpsilon_nonneg (by omega) j, ocEpsilon_le_one (by omega) j⟩
  have hsn := paper_entry_sn_le hΛ hDα hDq hDΛ E
  have hf0 : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  refine ⟨?_, fun freshK => ⟨?_, ?_⟩⟩
  · intro law hroot _
    refine E.family.elim fun _ h₁ => h₁.elim fun _ h₂ => h₂.elim fun _ h₃ =>
      h₃.2.2.2.elim fun fn hfn₀ => ?_
    have hfn := terminal_seed_datum_reindex E.ι _ E.Z (E.tp + D.termH M) fn hfn₀.1
    rw [show E.seed.mass law = fun w => E.rootM w.1.root from funext (finite_seed_mass E law hroot),
      ← hfn]
    exact hfn₀.2.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hC3) hf0)
  · exact (paper_entry_transport cfg hvalid hs₀ hΛ hbudget hDα hDq hDΛ hDζ hband
      hDterm E freshK).1.elim fun Uw h => h.elim fun Uk h' => ⟨_, Uw, Uk, h'⟩
  · intro U Uw Uk hU law hroot _ t ht X hX r hr hv hsize
    have hid := (paper_entry_transport cfg hvalid hs₀ hΛ hbudget hDα hDq hDΛ hDζ hband hDterm E
      freshK).2 U Uw Uk hU
    have hτ : cfg.τ = cfg.t₀ / 4 := hvalid.hτ
    have hts : t ∈ Set.Icc (E.tp + D.termH M) (a + cfg.T₀) :=
      ⟨by linarith only [E.seed_wait, ht.1], ht.2⟩
    have htp : t ∈ Set.Icc E.tp (a + cfg.T₀) := ⟨by linarith only [hts.1, hsn.1], ht.2⟩
    have hv' : IsRepOf (E.seed.mass law)
        (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) r.value := by
      rw [show (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) =
        fun w => U w t from funext fun w => (hid w t hts).symm]
      exact hv
    refine E.identity.1.elim fun CcT h₁ => h₁.elim fun PZ h₂ => h₂.elim fun aRep h₃ =>
      h₃.elim fun û hL => ?_
    refine (paper_entry_lift hs₀ hs1 hDα hDq hDΛ hDζ hDΦ hband hDterm hCw hMT hMW E CcT PZ aRep
      û hL t htp law hroot r hr hv').elim fun rT h₄ => h₄.elim fun rW hlift => ?_
    have hrW := hlift.2.2.2.1
    have hreadout := hlift.2.2.2.2.1
    have hsizeW := hlift.2.2.2.2.2
    have hKw := cfg.hLw
    choose aV haV using fun v => Providers.torusHk_classicalRep_exists cfg.Kw (cfg.Lw + 3)
      (by omega : cfg.Lw + 3 + 2 ≤ cfg.Kw) (E.V v t)
    refine ((E.identity.2 CcT PZ aRep û hL t htp aV haV).2 (by rw [hτ]; exact ht.1)).elim
      fun Θ hΘ₀ => ?_
    have hΘp := hΘ₀.1
    have hΘae := hΘ₀.2.1
    have herr := hΘ₀.2.2
    have hsize' : representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
        ENNReal.ofReal (CwLift * CT * X) := by
      refine hsizeW.trans ?_
      rw [ENNReal.ofReal_mul (mul_nonneg hCw hCT)]
      exact mul_le_mul' le_rfl hsize
    have hΘ := paper_entry_scalar hs₀ hs1 E t (CwLift * CT * X) _ (by positivity) rW hrW hsize'
      _ hreadout Θ herr
    refine ⟨Θ, hΘp, hΘae, paper_csNormLe_mono hΘ ?_⟩
    have hp := paper_entry_pow_le hPw hPT cfg.C (|cfg.C|) (Real.sqrt (l2NormSq f)) le_rfl hf0
      (D := D) (M := M)
    have h1 := pow_le_one₀ (hε M).1 (hε M).2 (n := 2)
    have h1' := pow_le_one₀ (hε (M - 1)).1 (hε (M - 1)).2 (n := 2)
    exact (add_le_add le_rfl hp).trans (paper_entry_bound_arith C (CwLift * CT) cfg.C X _ _ hX hf0
      (by linarith only [h1, h1']) hC1 hC2)

/-- The last clause of (E2) (lifted fields, identity and lift costs). -/
private def paperEntryE2Tail (cfg : FiniteParameters) (C : ℝ) {D : OCData} (M : ℕ) (a te : ℝ)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (rootM rootR : ℕ → ℝ)
    (seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (lawW : BirthLaw)
    (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (_aM tp : ℝ)
    (_Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (_ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (_V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
    (g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
      TorusHk (paperTermOrder cfg) (ScalarH v.1.root)) : Prop :=
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (paperTermOrder cfg - 2 * cfg.pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw (Gt'.retained M 1 cfg.RT) M cfg.pT (paperTermOrder cfg) cfg.NT
      (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp (a + cfg.T₀) cfg.cr Z CcT PZ aRep û →
  ∀ t ∈ Set.Icc (a + cfg.t₀ / 4) (a + cfg.T₀),
    (∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe cfg.s (fun x => Θt x - W M t (fun v x' =>
          termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t x' (ιw v)) x)
        (C * (D.eps M ^ 2 + D.eps (M - 1) ^ 2) * Real.sqrt (l2NormSq f))) ∧
    ∀ (freshK : ℕ → KernelSpec) (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    ∀ r : Representation (CompSpace seed.comps),
      IsRepresentationAt (D.eps (M - 1)) (paperRepOrder cfg) r →
      IsRepOf (seed.mass law) (fun w => U w t) r.value →
      ∃ (rT : Representation (CompSpace Gw.comps))
        (rW : Representation (CompSpace (stage (M + cfg.Jw)).comps)),
        IsRepresentationAt (D.eps M) (cfg.Jw * cfg.Nw + 3) rT ∧
        rT.value = compField (Gw.mass lawW)
          (termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) ∧
        representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT ≤
          ENNReal.ofReal C * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r ∧
        IsRepresentationAt (D.eps (M + cfg.Jw)) 3 rW ∧
        (∀ y, compReadoutCLM (fun v => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1)
            (rW.value y) =
          W M t (fun v y' => termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t y' (ιw v))
            y) ∧
        representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
          ENNReal.ofReal C * representedSize cfg.s (paperRepOrder cfg) (D.eps (M - 1)) r


/-- The last clause of (E2) for the entry data. -/
private theorem paper_entry_E2_tail {cfg : FiniteParameters} (hvalid : FiniteLocalValidity cfg)
    (hs₀ : 0 < cfg.s) (hΛ : 128 ≤ cfg.Λ) (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) {M : ℕ}
    (hbudget : FiniteSeedBudgetLevel cfg M) {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q)
    (hDΛ : D.Λ = cfg.Λ) (hDζ : D.ζ = cfg.ζ) (hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hDterm : D.term = M) {CT CwLift C : ℝ}
    (hCw : 0 ≤ CwLift) (hMT : TerminalLiftLevelStatement cfg CT M)
    (hMW : WeakLiftLevelStatement cfg CwLift M) (hC1 : CT ≤ C) (hC2 : CwLift * CT ≤ C)
    (hC3 : |cfg.C| ≤ C) {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) :
    paperEntryE2Tail cfg C M a (E.tp + D.termH M) E.seed E.rootM E.rootR E.seedKc E.stage E.Gw E.lawW
      E.ιw E.W E.aM E.tp E.Pterm E.Gt' E.ι f θ E.V
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M))) E.Z := by
  have hs1 : cfg.s < 1 := hvalid.hs₁.trans (by linarith only [hvalid.hα₀])
  have hsn := paper_entry_sn_le hΛ hDα hDq hDΛ E
  have hf0 : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  intro CcT PZ aRep û hL t ht
  have hτ : cfg.τ = cfg.t₀ / 4 := hvalid.hτ
  have hts : t ∈ Set.Icc (E.tp + D.termH M) (a + cfg.T₀) :=
    ⟨by linarith only [E.seed_wait, ht.1], ht.2⟩
  have htp : t ∈ Set.Icc E.tp (a + cfg.T₀) := ⟨by linarith only [hts.1, hsn.1], ht.2⟩
  have hKw := cfg.hLw
  choose aV haV using fun v => Providers.torusHk_classicalRep_exists cfg.Kw (cfg.Lw + 3)
    (by omega : cfg.Lw + 3 + 2 ≤ cfg.Kw) (E.V v t)
  refine ⟨((E.identity.2 CcT PZ aRep û hL t htp aV haV).2 (by rw [hτ]; exact ht.1)).elim
    fun Θ hΘ => ⟨Θ, hΘ.1, hΘ.2.1, paper_csNormLe_mono hΘ.2.2
      (paper_entry_pow_le hPw hPT cfg.C C _ hC3 hf0)⟩, ?_⟩
  intro freshK U Uw Uk hU law hroot _ r hr hv
  have hid := (paper_entry_transport cfg hvalid hs₀ hΛ hbudget hDα hDq hDΛ hDζ hband hDterm E
    freshK).2 U Uw Uk hU
  have hv' : IsRepOf (E.seed.mass law)
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) r.value := by
    rw [show (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) =
      fun w => U w t from funext fun w => (hid w t hts).symm]
    exact hv
  exact (paper_entry_lift hs₀ hs1 hDα hDq hDΛ hDζ hDΦ hband hDterm hCw hMT hMW E CcT PZ aRep û hL
    t htp law hroot r hr hv').elim fun rT h₁ => h₁.elim fun rW h => ⟨rT, rW, h.1, h.2.1,
      h.2.2.1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC1) le_rfl), h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC2) le_rfl)⟩

/-- The first and third clauses of (E2) (the terminal solution, a lifted field). -/
private def paperEntryE2Head (cfg : FiniteParameters) (_C : ℝ) {D : OCData} (M : ℕ) (a _te : ℝ)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (_rootM _rootR : ℕ → ℝ)
    (_seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (_lawW : BirthLaw)
    (_ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (_W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (aM tp : ℝ)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (_ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps)
    (_f : Vec 2 → ℝ) (_θ : ℝ → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
    (_g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
      TorusHk (paperTermOrder cfg) (ScalarH v.1.root)) : Prop :=
  (∃ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps,
        TorusHk (paperTermOrder cfg) (ScalarH v.1.root))
      (Zw : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
        TorusHk (paperTermOrder cfg + 1) (ScalarH v.1.root))
      (Zk : ∀ v u (_ : (Gt'.retained M 1 cfg.RT).fam.Γ v u), ℝ →
        TorusHk (paperTermOrder cfg + paperOrderBound cfg - 1) (ScalarH u.1.root)),
    IsTerminalTrace Gw (Gt'.retained M 1 cfg.RT) (Pterm fun v => V v aM) Z₀ ∧
    (Gt'.retained M 1 cfg.RT).IsRegSolution (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
      (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
      (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT) cfg.φ₀ cfg.hφ₀ (D.termB M)
      (streamVel (D.Φ (M - 1))) (paperTermOrder cfg) tp (a + cfg.T₀) Z₀ (fun _ _ => 0)
      (fun _ _ => 0) Z Zw Zk) ∧
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (paperTermOrder cfg - 2 * cfg.pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw (Gt'.retained M 1 cfg.RT) M cfg.pT (paperTermOrder cfg) cfg.NT
      (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp (a + cfg.T₀) cfg.cr Z CcT PZ aRep û)

/-- The second clause of (E2): every seed solution is the order-0 truncation of `Z`. -/
private def paperEntryE2Ident (cfg : FiniteParameters) (_C : ℝ) {D : OCData} (M : ℕ) (a te : ℝ)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (_rootM _rootR : ℕ → ℝ)
    (seedKc : ℕ → KernelSpec)
    (stage : ℕ → GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀) (_lawW : BirthLaw)
    (_ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (_W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (_aM _tp : ℝ)
    (_Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root)))
    (Gt' : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀)
    (ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps)
    (_f : Vec 2 → ℝ) (_θ : ℝ → Vec 2 → ℝ)
    (_V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
    (g : ∀ w : CompIn seed.comps, TorusHk 0 (ScalarH w.1.root))
    (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
      TorusHk (paperTermOrder cfg) (ScalarH v.1.root)) : Prop :=
  (∀ (freshK : ℕ → KernelSpec) (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
      (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
      (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedKc freshK cfg.φ₀ cfg.hφ₀ (D.κ (M - 1))
        (streamVel (D.Φ (M - 1))) 0 te (a + cfg.T₀) g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      ∀ w, ∀ t ∈ Set.Icc te (a + cfg.T₀),
        U w t = truncateTorusHk (Nat.zero_le _) (Z (ι.symm w) t))

/-- The first and third clauses of (E2) for the entry data. -/
private theorem paper_entry_E2_head {cfg : FiniteParameters} {C : ℝ} {M : ℕ} {D : OCData}
    {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) :
    paperEntryE2Head cfg C M a (E.tp + D.termH M) E.seed E.rootM E.rootR E.seedKc E.stage E.Gw E.lawW
      E.ιw E.W E.aM E.tp E.Pterm E.Gt' E.ι f θ E.V
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M))) E.Z := by
  exact ⟨E.family.elim fun Z₀ h₁ => h₁.elim fun Zw h₂ => h₂.elim fun Zk h₃ =>
    ⟨Z₀, Zw, Zk, h₃.1, h₃.2.1⟩, E.identity.1⟩

/-- The second clause of (E2) for the entry data. -/
private theorem paper_entry_E2_ident {cfg : FiniteParameters} (hvalid : FiniteLocalValidity cfg)
    (hs₀ : 0 < cfg.s) (hΛ : 128 ≤ cfg.Λ) {M : ℕ} (hbudget : FiniteSeedBudgetLevel cfg M)
    {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ) (hDζ : D.ζ = cfg.ζ)
    (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hDterm : D.term = M) {C : ℝ}
    {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) :
    paperEntryE2Ident cfg C M a (E.tp + D.termH M) E.seed E.rootM E.rootR E.seedKc E.stage E.Gw E.lawW
      E.ιw E.W E.aM E.tp E.Pterm E.Gt' E.ι f θ E.V
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M))) E.Z := fun freshK => (paper_entry_transport cfg hvalid hs₀ hΛ hbudget hDα hDq hDΛ hDζ hband
  hDterm E freshK).2

/-- **(E2)** for the entry data. -/
private theorem paper_entry_E2 {cfg : FiniteParameters} (hvalid : FiniteLocalValidity cfg)
    (hs₀ : 0 < cfg.s) (hΛ : 128 ≤ cfg.Λ) (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) {M : ℕ}
    (hbudget : FiniteSeedBudgetLevel cfg M) {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q)
    (hDΛ : D.Λ = cfg.Λ) (hDζ : D.ζ = cfg.ζ) (hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hDterm : D.term = M) {CT CwLift C : ℝ}
    (hCw : 0 ≤ CwLift) (hMT : TerminalLiftLevelStatement cfg CT M)
    (hMW : WeakLiftLevelStatement cfg CwLift M) (hC1 : CT ≤ C) (hC2 : CwLift * CT ≤ C)
    (hC3 : |cfg.C| ≤ C) {a : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (E : FiniteEntryData cfg D M a f θ) :
    PaperEntryE2 cfg C M a (E.tp + D.termH M) E.seed E.rootM E.rootR E.seedKc E.stage E.Gw E.lawW
      E.ιw E.W E.aM E.tp E.Pterm E.Gt' E.ι f θ E.V
      (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) (E.tp + D.termH M))) E.Z := by
  have hh := paper_entry_E2_head (C := C) E
  exact ⟨hh.1, paper_entry_E2_ident hvalid hs₀ hΛ hbudget hDα hDq hDΛ hDζ hband hDterm (C := C) E,
    hh.2, paper_entry_E2_tail hvalid hs₀ hΛ hPw hPT hbudget hDα hDq hDΛ hDζ
    hDΦ hband hDterm hCw hMT hMW hC1 hC2 hC3 E⟩

/-- The entry times: `a ≤ t_p` and `t_e = t_p + h_M ≤ a + t₀/4`. -/
private theorem paper_entry_times {cfg : FiniteParameters} {D : OCData} {M : ℕ}
    (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ) (hΛ : 128 ≤ cfg.Λ)
    (hc : 0 < cfg.c)
    (hwait : (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    {PW : ProvParams} {a aM tp : ℝ} {lawW : BirthLaw}
    {Gw : GenStage D ScalarH (paperOrderBound cfg) cfg.bw cfg.j₀}
    {Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (paperTermOrder cfg) (ScalarH v.1.root))}
    (hstage : IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw)
      (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ
      (weakChi cfg.α cfg.q cfg.η₀) Gw aM)
    (hprep : IsTerminalPrepMap M cfg.Kw (paperTermOrder cfg) cfg.c cfg.C Gw aM tp Pterm) :
    0 ≤ D.termH M ∧ a ≤ tp ∧ tp + D.termH M ≤ a + cfg.t₀ / 4 := by
  have hH : 0 ≤ D.termH M := by
    unfold OCData.termH
    rw [hDα, hDq, hDΛ]
    exact (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  have haM := hstage.1
  have haMup := hstage.2.1
  simp only [hDα, hDq, hDΛ] at haMup
  have htplow := hprep.2.1
  have htpup := hprep.2.2.1
  have hclow : 0 ≤ cfg.c * D.termH M := mul_nonneg hc.le hH
  have hCup : cfg.C * D.termH M ≤ |cfg.C| * D.termH M :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hH
  have hH' : D.termH M = ocTauPP cfg.α cfg.q cfg.Λ M := by
    simp only [OCData.termH, hDα, hDq, hDΛ]
  refine ⟨hH, by linarith only [haM, htplow, hclow], ?_⟩
  rw [hH'] at htpup hCup ⊢
  linarith only [htpup, hCup, haMup, hwait]

/-- **The entry statement** for finite-assembly parameters, for every constant `C` above the five
bounds `hC1`–`hC5`. -/
private theorem paper_entry_main {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ready : FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hC1 : 3 * (ready.CwLift * ready.CT) ≤ C) (hC2 : 2 * |ready.cfg.C| ≤ C)
    (hC3 : |ready.cfg.Centry| ≤ C) (hC4 : ready.CT ≤ C) (hC5 : ready.CwLift * ready.CT ≤ C) :
    PaperEntryStatement ready.cfg ready.Mstar C := by
  intro M hM D hDα hDq hDΛ hDζ hDΦ hband hDterm PW a
  have hvalid := ready.valid
  have hs₀c : 0 < ready.cfg.s := by rw [ready.base.2.1]; exact hs₀
  have hΛc : 128 ≤ ready.cfg.Λ := by rw [ready.base.2.2.2.2.1]; exact hΛ
  have hη := succEta0_pos_of_admissible hvalid.hα₀ hs₀c hvalid.hq
  have hlev := ready.levels M hM
  have hC2' : |ready.cfg.C| ≤ C := by linarith [abs_nonneg ready.cfg.C]
  refine (hlev.2.2.2.1 D hDα hDq hDΛ hDζ hDΦ hband hDterm PW a).elim fun stage h₁ =>
    h₁.elim fun Gw h₂ => h₂.elim fun lawW h₃ => h₃.elim fun ιw h₄ => h₄.elim fun aM h₅ =>
    h₅.elim fun CcR h₆ => h₆.elim fun W hA => ?_
  refine hA.2.2.2.2.2.elim fun tp h₇ => h₇.elim fun Pterm h₈ => h₈.elim fun lawT h₉ =>
    h₉.elim fun Gt' h₁₀ => h₁₀.elim fun seed h₁₁ => h₁₁.elim fun rootM h₁₂ =>
    h₁₂.elim fun rootR h₁₃ => h₁₃.elim fun seedKc h₁₄ => h₁₄.elim fun ι hB => ?_
  have htimes := paper_entry_times hDα hDq hDΛ hΛc ready.hc hlev.2.2.1 hA.2.2.2.2.1 hB.1
  have hseed := hB.2.2.2.2.1
  refine ⟨tp + D.termH M, seed, rootM, rootR, seedKc, stage, Gw, lawW, ιw, aM, CcR, W, tp, Pterm,
    lawT, Gt', ι, ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hB.1, hB.2.1, hB.2.2.1,
    hB.2.2.2.1⟩, ⟨by linarith only [htimes.1, htimes.2.1], htimes.2.2⟩, hseed.1, hseed.2.1,
    finite_successor_law ready.cfg hη rootM rootR hseed.1 hseed.2.1,
    fun law hr1 hr2 freshK => ⟨(hseed.2.2 law hr1 hr2).1 _ freshK, (hseed.2.2 law hr1 hr2).2.1,
      by omega, by linarith only [htimes.1, htimes.2.1]⟩, ?_⟩
  intro f _hf θ hθ
  refine (hB.2.2.2.2.2.2 f θ hθ).elim fun tq g₁ => g₁.elim fun Ur g₂ => g₂.elim fun Urw g₃ =>
    g₃.elim fun Urk g₄ => g₄.elim fun U₀ g₅ => g₅.elim fun U g₆ => g₆.elim fun V g₇ =>
    g₇.elim fun Uw g₈ => g₈.elim fun Vw g₉ => g₉.elim fun Uk g₁₀ => g₁₀.elim fun Vk hD' => ?_
  refine hD'.2.2.2.2.2.2.2.elim fun Z hZ => ?_
  let E : FiniteEntryData ready.cfg D M a f θ := {
    PW := PW, stage := stage, Gw := Gw, lawW := lawW, ιw := ιw, CcR := CcR, W := W, aM := aM
    construction := hA.1, encoding := hA.2.1, lifts := hA.2.2.1, chain := hA.2.2.2.1
    weakStage := hA.2.2.2.2.1, tp := tp, Pterm := Pterm, lawT := lawT, Gt' := Gt', prep := hB.1
    terminalLaw := hB.2.1, actual := hB.2.2.1, V := V, Z := Z, identity := hZ.2, seed := seed
    rootM := rootM, rootR := rootR, seedKc := seedKc, ι := ι, seedEncoding := hB.2.2.2.1
    seedClauses := hseed, family := hZ.1, a_le_tp := htimes.2.1, seed_wait := htimes.2.2
    terminal_window := hB.2.2.2.2.2.1 }
  exact ⟨tq, Ur, Urw, Urk, U₀, U, V, Uw, Vw, Uk, Vk, _, Z, hD'.1, hD'.2.1, hD'.2.2.1, hD'.2.2.2.1,
    hD'.2.2.2.2.1,
    paper_entry_E1 hvalid hs₀c hΛc ready.hPw ready.hPT hlev.2.1 hDα hDq hDΛ hDζ hDΦ hband hDterm
      ready.hCT ready.hCwLift hlev.2.2.2.2.1 hlev.2.2.2.2.2 hC1 hC2 hC3 E,
    paper_entry_E2 hvalid hs₀c hΛc ready.hPw ready.hPT hlev.2.1 hDα hDq hDΛ hDζ hDΦ hband hDterm
      ready.hCwLift hlev.2.2.2.2.1 hlev.2.2.2.2.2 hC4 hC5 hC2' E⟩

/-- **The entry statement for finite-assembly parameters.** Every `FiniteAssemblyReady` satisfies
the entry statement with its threshold `M_*` and some constant `C` (Proposition 4.1 of the paper
follows from it). -/
theorem paper_entry_of_ready {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (_ht₀ : 0 < t₀) (_htT : t₀ < T₀)
    (ready : FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀) :
    ∃ C : ℝ, PaperEntryStatement ready.cfg ready.Mstar C :=
  ⟨_, paper_entry_main hs₀ hΛ ready
    (max (3 * (ready.CwLift * ready.CT)) (max (2 * |ready.cfg.C|) (max |ready.cfg.Centry|
      (max ready.CT (ready.CwLift * ready.CT)))))
    (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _))
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _))⟩

/-- **The entry statement** (Proposition 4.1 of the paper follows from it). -/
theorem paper_entry (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
    ∃ (ready : FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀) (C : ℝ),
      PaperEntryStatement ready.cfg ready.Mstar C := by
  obtain ⟨Λ₀, hΛ₀, hP⟩ := paper_parameters_exist α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Jw hJw t₀ T₀ ht₀ htT => ?_⟩
  obtain ⟨P⟩ := hP Λ hΛ Jw hJw t₀ T₀ ht₀ htT
  obtain ⟨C, hC⟩ := paper_entry_of_ready hs₀ (hΛ₀.trans hΛ) ht₀ htT P.ready
  exact ⟨P.ready, C, hC⟩

end AVRegularity.PaperFacing
