-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.EntryStatement
public import AVRegularity.Proofs.PaperFacing.Parameters
import AVRegularity.Proofs.PaperFacing.StageSolutions
import AVRegularity.Finite.StrongEntry.SeedRepresentation
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.FluxFastDiscrepancy

/-! # The cascade, one cycle and one passage

At the parameters `P : PaperParameters` (the finite-assembly parameters extended by the cascade
schedule, the invariant constants and `iteration_passage` at these parameters), with
`m₀ = paperBottom P = max{m_*, m₀^cas, m_E + 1}`, `E = ε_{m-1}`, `‖f‖_G` the marked norm
`weightedNorm 1 π d f`, `‖g‖_π = weightedNorm 1 π 1 g`, `K = paperRepOrder`, and
`χ = min{δ, μ_s}/8`:

* `PaperCycleConclusion` (one cycle): for an admissible family `G` of level `m > m₀` on
  `[t_c - 3τ_m, t_f]` with `t_f ≥ t_c + 4τ''_m` and the retained part `G'` of an actual successor:
  `t_p ∈ [t_c, t_c + 4τ''_m]`; `G'` is admissible on `[t_c, t_f]`; for every datum `f` the solution
  `U` of `G` from `f` at `t_c` and the solution `Y` of `G'` from the retained trace of `Πf` at `t_p`
  exist and are unique; (a) `‖Πf - U(t_p)‖_G ≤ CE^Q‖f‖_G`, `‖Πf‖_G ≤ (1 + CE^Q)‖f‖_G`,
  `‖Πf‖_{G;c_r ρ(m),N_out} ≤ C‖f‖_G`; (b) `‖Y(t)‖_{G'} ≤ (1 + C(E^Q + E^δ))‖f‖_G` on `[t_p, t_f]`,
  and the comparison of `U` with the lift of `Y` (`ComparisonClauses`, error and residual
  `≤ CE^Q‖f‖_G`, through the order-`N_aux` solution `Y^{(N_aux)}` from the same trace).
* `PaperPassageConclusion` (one passage; Proposition 4.4 of the paper): the same `t_p, Π`:
  `U(t), Y(t)` have `C^{K+N+2p+2}` representatives on `[t_p, t_f]`, and every representation `r` of
  `Y(t)` at `E` yields a representation `r'` of `U(t)` at `ε_m` with
  `X_{ε_m}(r') ≤ (1 + CE^χ)X_E(r) + CE‖f‖_G`.
* `PaperCascadeStatement` (the cascade; Proposition 4.2 of the paper follows from it): for
  `M > n > m₀`, a band chain of terminal level `M` and an admissible seed of level `n` on
  `[t_S, t_f]` with `t_S + t₀/2 < t_f ≤ t_S + T`, the solution `U` of the seed from `g` at `t_S`
  exists, is unique, and has for a.e. `t ∈ [t_S + t₀/2, t_f]` a representation at `ε_n` of order `K`
  of size at most `C‖g‖_π`.

`paper_parameters_exist`: the parameters exist for `Λ ≥ Λ₀`, `J ≥ 1`, `0 < t₀ < T`.
`PaperCycleConclusionAt`: one cycle with a free history start `t_A` (the form of
`iteration_passage`; Proposition 4.3 of the paper follows from it), `G` admissible on `[t_A, t_f]`,
`t_A + 3τ_m ≤ t_c`, and `G'` admissible on `[t_A + 3τ_m, t_f]`; `paper_step_frame_of_parameters`
proves it with one passage, for the frame and datum part of `iteration_passage` at the same
`(t_p, Π)`; `paper_cycle_conclusion_of_at` recovers `PaperCycleConclusion` at `t_A = t_c - 3τ_m`.
`PaperPassageConclusionExp`, `PaperPassageConclusionEta`, `paper_passage_eta_proof`: one passage at
an exponent `χ`, and at `η₀ = succEta0` (Proposition 4.4 of the paper in the notation `η`).
`paper_cascade_of_parameters`: the three statements for every choice of parameters.
`paper_cascade_cycle_passage`: in the setting of the entry statement `paper_entry`, one choice of parameters
satisfies the entry statement (with its constant) and the three statements (with their constant and
`m₀`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- The passage exponent `χ = min{δ, μ_s}/8`. -/
abbrev paperChi (cfg : FiniteParameters) : ℝ :=
  min (ocDelta cfg.α cfg.q) (ocMuS cfg.α cfg.q cfg.s) / 8

/-- The solutions of one cycle for the datum `f`: the solution `U` of `G` from `f` at `t_c` and the
solution `Y` of `Gr` from the retained trace of `Πf` at `t_p` exist and are unique (order zero,
`IsRegSolution`, the class of `kernel_energy_torus`). -/
def PaperCycleSolutions (cfg : FiniteParameters) {D : OCData} (seedK freshK : ℕ → KernelSpec)
    (m : ℕ) (tc tp tf : ℝ) (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) : Prop :=
  (∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
  (∀ (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw Uw' : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk Uk' : ∀ v u (_ : G.fam.Γ v u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U' Uw' Uk' →
    ∀ v, ∀ t ∈ Set.Icc tc tf, U v t = U' v t) ∧
  (∃ (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 ∧
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk) ∧
  ∀ (Y0 Y0' : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
    (Y Y' : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw Yw' : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk Yk' : ∀ v u (_ : Gr.fam.Γ v u), ℝ →
      TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0' →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0' (fun _ _ => 0) (fun _ _ => 0) Y' Yw' Yk' →
    ∀ v, ∀ t ∈ Set.Icc tp tf, Y v t = Y' v t

/-- Part (a) of one cycle for the datum `f`, in the marked norm `‖·‖_G = weightedNorm 1 π d`,
`E = ε_{m-1}`: `‖Πf - U(t_p)‖_G ≤ CE^Q‖f‖_G` for the solution `U` of `G` from `f` at `t_c`,
`‖Πf‖_G ≤ (1 + CE^Q)‖f‖_G` and `‖Πf‖_{G;c_r ρ(m),N_out} ≤ C‖f‖_G` at the radius
`c_r ρ(m) = rhoEnh D c_r m = c_r(κ_{m-1}τ''_m)^{1/2}`. -/
def PaperCyclePreparation (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) : Prop :=
  (∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    weightedNorm (hr := ScalarH) (k := 0) 1 (G.mass law) (G.marker law)
        (fun v => truncateTorusHk (Nat.zero_le cfg.Nout) (Preg f v) - U v tp) ≤
      C * D.eps (m - 1) ^ cfg.Q * weightedNorm 1 (G.mass law) (G.marker law) f) ∧
  weightedNorm (hr := ScalarH) (k := 0) 1 (G.mass law) (G.marker law)
      (fun v => truncateTorusHk (Nat.zero_le cfg.Nout) (Preg f v)) ≤
    (1 + C * D.eps (m - 1) ^ cfg.Q) * weightedNorm 1 (G.mass law) (G.marker law) f ∧
  weightedNorm (rhoEnh D cfg.kI.cr m) (G.mass law) (G.marker law) (Preg f) ≤
    C * weightedNorm 1 (G.mass law) (G.marker law) f

/-- Part (b) of one cycle for the datum `f` and every solution `Y` of `Gr` from the retained trace
of `Πf` at `t_p`: `‖Y(t)‖_{G'} ≤ (1 + C(E^Q + E^δ))‖f‖_G` on `[t_p, t_f]`, and, through the
order-`N_aux` solution `Y^{(N_aux)}` from the same trace (whose truncation is `Y`), the comparison
of the solution `U` of `G` from `f` at `t_c` with the lift of `Y` (`ComparisonClauses`: the lifted
field exists, and for every lifted field the residual and the error
`sup ‖U - 𝓛Y‖_π + κ_m^{1/2}‖∇(U - 𝓛Y)‖_{L²(t_p,t_f;π)}` are at most `CE^Q‖f‖_G`). -/
def PaperCycleSuccessor (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) : Prop :=
  ∀ (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    (∀ t ∈ Set.Icc tp tf,
      weightedNorm (hr := ScalarH) (k := 0) 1 (Gr.mass law) (Gr.marker law) (fun v => Y v t) ≤
        (1 + C * (D.eps (m - 1) ^ cfg.Q + D.eps (m - 1) ^ ocDelta cfg.α cfg.q)) *
          weightedNorm 1 (G.mass law) (G.marker law) f) ∧
    ∃ (YN0 : ∀ v : CompIn Gr.comps, TorusHk cfg.Naux (ScalarH v.1.root))
      (YN : ∀ v : CompIn Gr.comps, ℝ → TorusHk cfg.Naux (ScalarH v.1.root))
      (YNw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (cfg.Naux + 1) (ScalarH v.1.root))
      (YNk : ∀ v u (_ : Gr.fam.Γ v u), ℝ →
        TorusHk (cfg.Naux + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      IsRetainedTrace G Gr m cfg.p tp (Preg f) YN0 ∧
      Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
        (streamVel (D.Φ (m - 1))) cfg.Naux tp tf YN0 (fun _ _ => 0) (fun _ _ => 0) YN YNw YNk ∧
      (∀ v, ∀ t ∈ Set.Icc tp tf, truncateTorusHk (Nat.zero_le cfg.Naux) (YN v t) = Y v t) ∧
      ComparisonClauses law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ G Gr m cfg.p cfg.Naux
        cfg.N (succSchedR (paperDepthBound cfg) cfg.J cfg.H) cfg.sX cfg.sZ
        (succEta0 cfg.α cfg.q cfg.s) tc tp tf
        (C * D.eps (m - 1) ^ cfg.Q * weightedNorm 1 (G.mass law) (G.marker law) f)
        (C * D.eps (m - 1) ^ cfg.Q * weightedNorm 1 (G.mass law) (G.marker law) f) f YN

/-- **One cycle**, for the admissible family `G` of level `m`, its retained successor `Gr`, the
preparation time `tp` and the preparation `Preg = Π`: `t_p ∈ [t_c, t_c + 4τ''_m]`, `Gr` is
admissible of level `m - 1` on `[t_c, t_f]`, and for every datum `f` the solutions exist and are
unique and satisfy (a) and (b). -/
def PaperCycleConclusion (cfg : FiniteParameters) (C : ℝ) {D : OCData} (M Mnat : ℕ)
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  tp ∈ Set.Icc tc (tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m) ∧
  IsPaperFamily cfg M Mnat law seedK freshK Gr (m - 1) tc tf ∧
  ∀ f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root),
    PaperCycleSolutions cfg seedK freshK m tc tp tf G Gr Preg f ∧
    PaperCyclePreparation cfg C law seedK freshK m tc tp tf G Preg f ∧
    PaperCycleSuccessor cfg C law seedK freshK m tc tp tf G Gr Preg f

/-- **One cycle with a free history start** `t_A` (the form of `iteration_passage`; Proposition 4.3
of the paper follows from it): for the admissible family `G` of level `m` on `[t_A, t_f]` with
`t_A + 3τ_m ≤ t_c`, its retained successor `Gr`, the preparation time `tp` and the preparation
`Preg = Π`: `t_p ∈ [t_c, t_c + 4τ''_m]`, `Gr` is admissible of level `m - 1` on `[t_A + 3τ_m, t_f]`,
and for every datum `f` the solutions exist and are unique and satisfy (a) and (b).
`PaperCycleConclusion` is the case `t_A = t_c - 3τ_m`. -/
def PaperCycleConclusionAt (cfg : FiniteParameters) (C : ℝ) {D : OCData} (M Mnat : ℕ)
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tA tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  tp ∈ Set.Icc tc (tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m) ∧
  IsPaperFamily cfg M Mnat law seedK freshK Gr (m - 1) (tA + 3 * ocTau cfg.α cfg.q cfg.Λ m) tf ∧
  ∀ f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root),
    PaperCycleSolutions cfg seedK freshK m tc tp tf G Gr Preg f ∧
    PaperCyclePreparation cfg C law seedK freshK m tc tp tf G Preg f ∧
    PaperCycleSuccessor cfg C law seedK freshK m tc tp tf G Gr Preg f

/-- **One passage** (Proposition 4.4 of the paper), for the same `G`, `Gr`, `tp`, `Preg` as one
cycle. -/
def PaperPassageConclusion (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
  ∀ (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    (∃ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      ∀ t ∈ Set.Icc tp tf,
        IsSmoothRep (fun v => U v t) (aU t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2) ∧
        IsSmoothRep (fun v => Y v t) (aY t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2)) ∧
    ∀ t ∈ Set.Icc tp tf, ∀ rY : Representation (CompSpace Gr.comps),
      IsRepresentationAt (D.eps (m - 1)) (paperRepOrder cfg) rY →
      IsRepOf (Gr.mass law) (fun v => Y v t) rY.value →
      ∃ rU : Representation (CompSpace G.comps),
        IsRepresentationAt (D.eps m) (paperRepOrder cfg) rU ∧
        IsRepOf (G.mass law) (fun v => U v t) rU.value ∧
        representedSize cfg.s (paperRepOrder cfg) (D.eps m) rU ≤
          ENNReal.ofReal (1 + C * D.eps (m - 1) ^ paperChi cfg) *
              representedSize cfg.s (paperRepOrder cfg) (D.eps (m - 1)) rY +
            ENNReal.ofReal (C * D.eps (m - 1) * weightedNorm 1 (G.mass law) (G.marker law) f)

/-- **One passage at an exponent `χ`**: `PaperPassageConclusion` with the exponent `paperChi cfg` of
the size bound replaced by `χ` (`PaperPassageConclusion` is the case `χ = paperChi cfg`). -/
def PaperPassageConclusionExp (cfg : FiniteParameters) (C χ : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
      tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
  ∀ (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m cfg.p tp (Preg f) Y0 →
    Gr.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ (m - 1))
      (streamVel (D.Φ (m - 1))) 0 tp tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    (∃ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      ∀ t ∈ Set.Icc tp tf,
        IsSmoothRep (fun v => U v t) (aU t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2) ∧
        IsSmoothRep (fun v => Y v t) (aY t) (paperRepOrder cfg + cfg.N + 2 * cfg.p + 2)) ∧
    ∀ t ∈ Set.Icc tp tf, ∀ rY : Representation (CompSpace Gr.comps),
      IsRepresentationAt (D.eps (m - 1)) (paperRepOrder cfg) rY →
      IsRepOf (Gr.mass law) (fun v => Y v t) rY.value →
      ∃ rU : Representation (CompSpace G.comps),
        IsRepresentationAt (D.eps m) (paperRepOrder cfg) rU ∧
        IsRepOf (G.mass law) (fun v => U v t) rU.value ∧
        representedSize cfg.s (paperRepOrder cfg) (D.eps m) rU ≤
          ENNReal.ofReal (1 + C * D.eps (m - 1) ^ χ) *
              representedSize cfg.s (paperRepOrder cfg) (D.eps (m - 1)) rY +
            ENNReal.ofReal (C * D.eps (m - 1) * weightedNorm 1 (G.mass law) (G.marker law) f)

/-- **One passage at the exponent `η₀ = succEta0`** (Proposition 4.4 of the paper with `η = η₀`):
every
representation `r` of `Y(t)` at `E` yields a representation `r'` of `U(t)` at `ε_m` with
`X_{ε_m}(r') ≤ (1 + CE^{η₀})X_E(r) + CE‖f‖_G`. -/
def PaperPassageConclusionEta (cfg : FiniteParameters) (C : ℝ) {D : OCData} (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec) (m : ℕ) (tc tp tf : ℝ)
    (G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  PaperPassageConclusionExp cfg C (succEta0 cfg.α cfg.q cfg.s) law seedK freshK m tc tp tf G Gr Preg

/-- **One cycle and one passage** at the parameters `cfg`, bottom level `m₀` and constant `C`: for
every
admissible family of level `m > m₀` on `[t_c - 3τ_m, t_f]` with `t_f ≥ t_c + 4τ''_m` and every
actual successor, one preparation `(t_p, Π)` gives both conclusions. -/
def PaperStepStatement (cfg : FiniteParameters) (m₀ : ℕ) (C : ℝ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (m : ℕ), m₀ < m →
  ∀ (tc tf : ℝ) (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    IsPaperFamily cfg M Mnat law seedK freshK G m (tc - 3 * ocTau cfg.α cfg.q cfg.Λ m) tf →
    tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
  ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))),
    PaperCycleConclusion cfg C M Mnat law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J)
      Preg ∧
    PaperPassageConclusion cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg

/-- **The cascade** at the parameters `cfg`, bottom level `m₀` and constant `C` (Proposition 4.2
of the paper follows from it). -/
def PaperCascadeStatement (cfg : FiniteParameters) (m₀ : ℕ) (C : ℝ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ),
    m₀ < n → tS + cfg.t₀ / 2 < tf →
    IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf →
  ∀ g : ∀ v : CompIn seed.comps, TorusHk 0 (ScalarH v.1.root),
    (∃ (U : ∀ v : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : seed.fam.Γ v u), ℝ →
          TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ n) (streamVel (D.Φ n))
        0 tS tf g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
    (∀ (U U' : ∀ v : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw Uw' : ∀ v : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk Uk' : ∀ v u (_ : seed.fam.Γ v u), ℝ →
          TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ n) (streamVel (D.Φ n))
        0 tS tf g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      seed.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ n) (streamVel (D.Φ n))
        0 tS tf g (fun _ _ => 0) (fun _ _ => 0) U' Uw' Uk' →
      ∀ v, ∀ t ∈ Set.Icc tS tf, U v t = U' v t) ∧
    ∀ (U : ∀ v : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : seed.fam.Γ v u), ℝ →
        TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      seed.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ n) (streamVel (D.Φ n))
        0 tS tf g (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      ∀ᵐ t ∂(volume.restrict (Set.Icc (tS + cfg.t₀ / 2) tf)),
        ∃ r : Representation (CompSpace seed.comps),
          IsRepresentationAt (D.eps n) (paperRepOrder cfg) r ∧
          IsRepOf (seed.mass law) (fun v => U v t) r.value ∧
          representedSize cfg.s (paperRepOrder cfg) (D.eps n) r ≤
            ENNReal.ofReal (C * weightedNorm 1 (seed.mass law) (fun _ => 1) g)


/-! ### Proofs -/

/-- A representation of a family with a continuous periodic representative has that
representative as its value. -/
private theorem paper_repOf_value {S : Finset Comp} {k : ℕ} (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (Y : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (aY : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) {K' : ℕ} (hs : IsSmoothRep Y aY K')
    {e : ℝ} {K : ℕ} (r : Representation (CompSpace S)) (hr : IsRepresentationAt e K r)
    (hv : IsRepOf π Y r.value) : r.value = compField π aY := by
  obtain ⟨hcd, hper⟩ := Finite.WeakLift.representation_value_contDiff_periodic r hr
  have hcomp (v : CompIn S) :
      (fun x => WithLp.ofLp (r.value x) v) = fun x => (Real.sqrt (π v))⁻¹ * aY x v := by
    apply CycleComparison.Lift.periodicContinuous_eq_of_cell_ae
    · fun_prop
    · exact continuous_const.mul ((continuous_apply v).comp hs.1.continuous)
    · intro n x
      simp only [hper n x]
    · intro n x
      simp only [hs.2.1 n x]
    · filter_upwards [hv v, hs.2.2 v] with x h1 h2
      have hsq := Real.sqrt_pos.mpr (hπ v)
      rw [← h2, h1, ← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]
  funext x
  change r.value x = WithLp.toLp 2 (fun v => (Real.sqrt (π v))⁻¹ * aY x v)
  rw [← WithLp.toLp_ofLp (p := 2) (r.value x)]
  congr 1
  funext v
  exact congrFun (hcomp v) x

/-- A representation whose value is the normalized field of a smooth representative is a
representation of the family. -/
private theorem paper_repOf_of_value {S : Finset Comp} {k : ℕ} (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (U : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (aU : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) {K' : ℕ} (hs : IsSmoothRep U aU K')
    (F : Vec 2 → CompSpace S) (hF : F = compField π aU) : IsRepOf π U F := by
  intro v
  filter_upwards [hs.2.2 v] with x hx
  rw [hF]
  change _ = Real.sqrt (π v) * ((Real.sqrt (π v))⁻¹ * aU x v)
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne', one_mul]
  exact hx

/-- `weightedNorm` is nonnegative. -/
private theorem paper_weightedNorm_nonneg {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π w : CompIn S → ℝ)
    (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) : 0 ≤ weightedNorm ρ π w X :=
  Real.sqrt_nonneg _

/-- The two facts of the invariant admissibility used for the stage operators. -/
private theorem paperParameters_invariant_facts {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    P.ready.cfg.kI.c₀ = P.ready.cfg.kS.c₀ ∧
      P.ready.cfg.kI.Hprod = P.ready.cfg.kI.G0 + P.ready.cfg.H + 1 := by
  obtain ⟨hc₀eq, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hHprod, _⟩ := P.invariant
  exact ⟨hc₀eq, hHprod⟩

/-- The conclusion of the cascade from a seed representation of the cascade and uniqueness. -/
private theorem paper_seed_rep_conclusion {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (Pp : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (G : GenStage D ScalarH Dm b j₀) (n K : ℕ) (sn delay tf s C₀ C : ℝ)
    (hdelay : 0 ≤ delay) (hC : C₀ ≤ C)
    (g : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (hrep : SeedCascadeRepresentation law Pp seedK freshK φ₀ hφ₀ G n K sn delay tf s C₀ g)
    (huniq : ∀ (U U' : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw Uw' : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk Uk' : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      G.IsRegSolution Pp seedK freshK φ₀ hφ₀ (D.κ n) (streamVel (D.Φ n)) 0 sn tf g
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      G.IsRegSolution Pp seedK freshK φ₀ hφ₀ (D.κ n) (streamVel (D.Φ n)) 0 sn tf g
        (fun _ _ => 0) (fun _ _ => 0) U' Uw' Uk' →
      ∀ v, ∀ t ∈ Set.Icc sn tf, U v t = U' v t) :
    (∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      G.IsRegSolution Pp seedK freshK φ₀ hφ₀ (D.κ n) (streamVel (D.Φ n)) 0 sn tf g
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) ∧
    ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      G.IsRegSolution Pp seedK freshK φ₀ hφ₀ (D.κ n) (streamVel (D.Φ n)) 0 sn tf g
        (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
      ∀ᵐ t ∂(volume.restrict (Set.Icc (sn + delay) tf)),
        ∃ r : Representation (CompSpace G.comps),
          IsRepresentationAt (D.eps n) K r ∧ IsRepOf (G.mass law) (fun v => U v t) r.value ∧
          representedSize s K (D.eps n) r ≤
            ENNReal.ofReal (C * weightedNorm 1 (G.mass law) (fun _ => 1) g) := by
  obtain ⟨U₁, Uw₁, Uk₁, rep, hU₁, hrep, hsize⟩ := hrep
  refine ⟨⟨U₁, Uw₁, Uk₁, hU₁⟩, ?_⟩
  intro U Uw Uk hU
  filter_upwards [hsize, ae_restrict_mem measurableSet_Icc] with t ht htw
  have htS' : t ∈ Set.Icc sn tf := ⟨by linarith [htw.1], htw.2⟩
  have heq : (fun v => U v t) = fun v => U₁ v t :=
    funext fun v => huniq U U₁ Uw Uw₁ Uk Uk₁ hU hU₁ v t htS'
  refine ⟨rep.atTime t, (hrep t htw).1, ?_, ht.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)))⟩
  rw [heq]
  exact (hrep t htw).2

/-- The cascade at an admissible seed: its representations from every datum and the
invariant of the seed on `[t_S, t_f]` with the invariant constants of the parameters. -/
private theorem paper_cascade_seed_data {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) {D : OCData}
    (hDα : D.α = P.ready.cfg.α) (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ)
    (hDζ : D.ζ = P.ready.cfg.ζ)
    (hDΦ : IsOCStreamSeq P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ D.Φ) {M : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ)
    (hterm : D.term = M) {Mnat : ℕ} (hMnat : M ≤ Mnat) {law : BirthLaw}
    (hlaw : IsSuccessorLaw P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s (paperWordCount P.ready.cfg)
      law) {seedK freshK : ℕ → KernelSpec}
    (hfresh : ∀ b', 1 ≤ b' → b' < M →
      IsFreshKernel D P.ready.cfg.kI.cr P.ready.cfg.σ₀ P.ready.cfg.nk.toPNat' b' (freshK b'))
    {seed : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀}
    {n : ℕ} {tS tf : ℝ} (hm₀ : P.ready.cfg.m₀ < n) (htS : tS + P.ready.cfg.t₀ / 2 < tf)
    (hseedP : IsPaperSeed P.ready.cfg M Mnat law seedK freshK seed n tS tf) :
    (∀ fn : ∀ v : CompIn seed.comps, TorusHk 0 (ScalarH v.1.root),
      SeedCascadeRepresentation law (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀
        P.ready.cfg.hφ₀ seed n (paperRepOrder P.ready.cfg) tS (P.ready.cfg.t₀ / 2) tf
        P.ready.cfg.s P.ready.cfg.Ccas fn) ∧
    IsStageInvariant law (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀
      Mnat P.ready.cfg.kI tS tf
      (P.ready.cfg.CI * D.eps n ^ min (ocDelta D.α D.q / 4) P.ready.cfg.τe)
      (P.ready.cfg.CI * D.eps (n - 1) ^ (D.q * min (ocDelta D.α D.q / 4) P.ready.cfg.τe)) seed := by
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hq : 1 < D.q := by rw [hDq]; exact P.ready.valid.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  obtain ⟨stage, ext, hist, st, tp, Preg, hframe, houtput⟩ :=
    P.ready.cascade D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
      seed n tS tf htS hseedP.2.2.2 hseedP.1 hseedP.2.1 hm₀ hseedP.2.2.1
  have hseedAll : ∀ fn : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root),
      SeedCascadeRepresentation law (paperProv P.ready.cfg D) seedK freshK P.ready.cfg.φ₀
        P.ready.cfg.hφ₀ (stage n) n (paperRepOrder P.ready.cfg) tS (P.ready.cfg.t₀ / 2) tf
        P.ready.cfg.s P.ready.cfg.Ccas fn := fun fn =>
    cascade_seed_representation law _ seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀ P.ready.cfg.p
      P.ready.cfg.N (succSchedR (paperDepthBound P.ready.cfg) P.ready.cfg.J P.ready.cfg.H)
      P.ready.cfg.sX P.ready.cfg.sZ (paperRepOrder P.ready.cfg) P.ready.cfg.Naux P.ready.cfg.s
      (succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s)
      (ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s)
      (ocDelta P.ready.cfg.α P.ready.cfg.q - 2 * P.ready.cfg.σ₀) 2 P.ready.cfg.Q P.ready.cfg.Ccas
      P.ready.cfg.kI.cr P.ready.cfg.kI.c₀ n P.ready.cfg.m₀ tS (P.ready.cfg.t₀ / 2) tf stage hist
      st tp Preg fn hm₀.le hframe.2.2.1
      (fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD law v.1) (houtput fn)
  have hinv := (hframe.2.2.2.2.1 n hm₀.le le_rfl).2.2.1
  rw [hframe.1] at hseedAll hinv
  rw [hframe.2.1] at hinv
  exact ⟨hseedAll, hinv⟩

/-- **The cascade** at the parameters, for every constant `C ≥ C_cas`. -/
theorem paper_cascade_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hC : P.ready.cfg.Ccas ≤ C) : PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hn htS hseedP g
  have hm₀ : P.ready.cfg.m₀ < n :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hmE : P.mEnergy + 1 < n :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hdata := paper_cascade_seed_data hΛ P hDα hDq hDΛ hDζ hDΦ hband hterm hMnat hlaw hfresh
    hm₀ htS hseedP
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have ht₀c : 0 < P.ready.cfg.t₀ := by rw [P.ready.base.2.2.2.2.2.2.1]; exact ht₀
  have hq : 1 < D.q := by rw [hDq]; exact P.ready.valid.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hθ : P.ready.cfg.CI *
      D.eps (n - 1) ^ (D.q * min (ocDelta D.α D.q / 4) P.ready.cfg.τe) ≤ 1 / 8 := by
    have h := P.energy_floor (n - 1) (by omega)
    unfold paperTauPrime at h
    rw [← hDq, ← hDΛ, ← hDα] at h
    exact h
  have huniq := (paperStage_solution law (paperProv P.ready.cfg D)
    (paperMenu P.ready.cfg Mnat) seedK freshK P.ready.cfg.φ₀ P.ready.cfg.hφ₀ Mnat P.ready.cfg.kI
    tS tf _ _ seed seed n hseedP.1.1 hdata.2 hseedP.1.2.1 IsCascadeStage.seed
    (paperParameters_invariant_facts P).2 hq hΛD (by omega)
    (P.energy_start.trans (by omega)) (by rw [hterm]; exact hseedP.2.2.1.le) P.ready.valid.hbw
    (CycleReference.bandChain_pos (by omega) P.ready.valid.hζ hband hseedP.2.2.1.le)
    (by rw [(paperParameters_invariant_facts P).1]; exact P.ready.valid.hc₀)
    (by rw [(paperParameters_invariant_facts P).1]; exact P.seed_c₀_le)
    (by change 2 ≤ succSchedD _ _ _ _ + 2 * _ + 4 * _ + 4; omega) hθ tS le_rfl
    (by linarith) g).2
  have hfin := paper_seed_rep_conclusion law (paperProv P.ready.cfg D) seedK freshK
    P.ready.cfg.φ₀ P.ready.cfg.hφ₀ seed n (paperRepOrder P.ready.cfg) tS (P.ready.cfg.t₀ / 2) tf
    P.ready.cfg.s P.ready.cfg.Ccas C (by linarith) hC g (hdata.1 g) huniq
  exact ⟨hfin.1, huniq, hfin.2⟩

/-- `ComparisonClauses` is monotone in its two bounds. -/
private theorem paper_comparison_mono {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {law : BirthLaw}
    {Pp : ProvParams} {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
    {G Gr : GenStage D ScalarH Dm b j₀} {m p Naux N depth sX sZ : ℕ}
    {η₀ s₀ tp tf r₁ e₁ r₂ e₂ : ℝ} {f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)}
    {Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (ScalarH v.1.root)}
    (h : ComparisonClauses law Pp seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η₀ s₀ tp tf
      r₁ e₁ f Y) (hr : r₁ ≤ r₂) (he : e₁ ≤ e₂) :
    ComparisonClauses law Pp seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η₀ s₀ tp tf
      r₂ e₂ f Y := by
  refine ⟨h.1, fun U Uw Uk hU CcT PZ aRep û hL => ?_⟩
  obtain ⟨ŵ, ŷ, R, q, hs, h1, h2⟩ := h.2 U Uw Uk hU CcT PZ aRep û hL
  exact ⟨ŵ, ŷ, R, q, hs, h1.trans (ENNReal.ofReal_le_ofReal hr),
    h2.trans (ENNReal.ofReal_le_ofReal he)⟩

/-- The datum-independent frame of `iteration_passage` at the parameters, for the history start
`t_A` and the start `t_c` of the solution of `G`. -/
abbrev PaperPassageFrameAt (cfg : FiniteParameters) (CQ C : ℝ) {D : OCData} (Mnat : ℕ)
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec)
    (seed G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ)
    (tA tc tf tp : ℝ)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  PassageFrame law (paperProv cfg D) (paperMenu cfg Mnat) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat
    cfg.kI cfg.CI cfg.τe seed G (G'.retained m cfg.H cfg.J) m (succEta0 cfg.α cfg.q cfg.s)
    cfg.Kres (paperWordCount cfg) cfg.p cfg.Nout cfg.Naux cfg.Q CQ C tA tc tf tp Preg

/-- The datum part of `iteration_passage` at the parameters, for the start `t_c` of the solution
of `G`. -/
abbrev PaperPassageOutputAt (cfg : FiniteParameters) (C : ℝ) {D : OCData}
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec)
    (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ) (tc tf tp : ℝ)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))) : Prop :=
  PassageOutput law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ G (G'.retained m cfg.H cfg.J) m
    cfg.p cfg.N (succSchedR (paperDepthBound cfg) cfg.J cfg.H) cfg.sX cfg.sZ (paperRepOrder cfg)
    cfg.Naux cfg.s (succEta0 cfg.α cfg.q cfg.s) (ocMuS cfg.α cfg.q cfg.s)
    (ocDelta cfg.α cfg.q - 2 * cfg.σ₀) 2 cfg.Q C cfg.kI.cr cfg.kI.c₀ tc tp tf (freshK (m - 1)) Preg

/-- `iteration_passage` at the parameters for an admissible family on `[t_A, t_f]`,
`t_A + 3τ_m ≤ t_c`. -/
private theorem paper_passage_at {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) {D : OCData}
    (hDα : D.α = P.ready.cfg.α) (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ)
    (hDζ : D.ζ = P.ready.cfg.ζ)
    (hDΦ : IsOCStreamSeq P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ D.Φ) {M : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ)
    (hterm : D.term = M) {Mnat : ℕ} (hMnat : M ≤ Mnat) {law : BirthLaw}
    (hlaw : IsSuccessorLaw P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s (paperWordCount P.ready.cfg)
      law) {seedK freshK : ℕ → KernelSpec}
    (hfresh : ∀ b', 1 ≤ b' → b' < M →
      IsFreshKernel D P.ready.cfg.kI.cr P.ready.cfg.σ₀ P.ready.cfg.nk.toPNat' b' (freshK b'))
    {m : ℕ} (hm : P.mStar ≤ m) {tA tc tf : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀}
    (hG : IsPaperFamily P.ready.cfg M Mnat law seedK freshK G m tA tf)
    (htA : tA + 3 * ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tc)
    (htf : tc + 4 * ocTauPP P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tf)
    (hτ : 0 ≤ ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m)
    (hsucc : IsActualSuccessor D (paperProv P.ready.cfg D) (paperMenu P.ready.cfg Mnat) G G') :
    ∃ (tS : ℝ) (seed : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw
        P.ready.cfg.j₀) (n : ℕ) (tp : ℝ)
      (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk P.ready.cfg.Nout (ScalarH v.1.root))),
      tS ≤ tA ∧
      IsPaperSeed P.ready.cfg M Mnat law seedK freshK seed n tS tf ∧
      PaperPassageFrameAt P.ready.cfg P.CQpass P.Cpass Mnat law seedK freshK seed G G' m tA tc tf
        tp Preg ∧
      PaperPassageOutputAt P.ready.cfg P.Cpass law seedK freshK G G' m tc tf tp Preg := by
  obtain ⟨tS, seed, n, htS, hseedP, hc, hlev, hI⟩ := hG
  have hmn : m ≤ n := by
    have h := paperStage_level_le hc
    rw [hlev, hseedP.1.1] at h
    exact h
  obtain ⟨tp, Preg, hframe, hout⟩ := P.passage D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat
    law hlaw seedK freshK hfresh seed n tS tf hseedP.1 hseedP.2.1 m hm hmn hseedP.2.2.1 tA tc htS
    htA htf (by linarith [hseedP.2.2.2]) G G' hc hlev hI hsucc
  exact ⟨tS, seed, n, tp, Preg, htS, hseedP, hframe, hout⟩

/-- The preparation time and the admissibility of the retained successor. -/
private theorem paper_cycle_frame_facts {cfg : FiniteParameters} {CQ C : ℝ} {D : OCData}
    (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) (hDΛ : D.Λ = cfg.Λ) {M Mnat : ℕ} {law : BirthLaw}
    {seedK freshK : ℕ → KernelSpec} {m n : ℕ} {tS tA tc tf tp : ℝ}
    {seed G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (htS : tS ≤ tA)
    (hseedP : IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf) (hlev : G.level = m)
    (hsucc : IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G')
    (hτ : 0 ≤ ocTau cfg.α cfg.q cfg.Λ m)
    (hframe : PaperPassageFrameAt cfg CQ C Mnat law seedK freshK seed G G' m tA tc tf tp Preg) :
    tp ∈ Set.Icc tc (tc + 4 * ocTauPP cfg.α cfg.q cfg.Λ m) ∧
      IsPaperFamily cfg M Mnat law seedK freshK (G'.retained m cfg.H cfg.J) (m - 1)
        (tA + 3 * ocTau cfg.α cfg.q cfg.Λ m) tf := by
  have hprep := hframe.1
  refine ⟨⟨hprep.2.1, ?_⟩, tS, seed, n, htS.trans (by linarith), hseedP, hframe.2.2.2.2.1, ?_, ?_⟩
  · have h := hprep.2.2.1
    rw [hlev, hDα, hDq, hDΛ] at h
    exact h
  · change G'.level = m - 1
    rw [hsucc.2.1, hlev]
  · have h := hframe.2.2.2.2.2.1
    rw [hDα, hDq, hDΛ] at h
    exact h

/-- One cycle: existence and uniqueness of the two solutions. -/
private theorem paper_cycle_solutions_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (hΛ : 128 ≤ Λ) {D : OCData}
    (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ) {M Mnat : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ)
    (hterm : D.term = M) {law : BirthLaw} {seedK freshK : ℕ → KernelSpec} {m : ℕ}
    {tA tc tf tp : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk P.ready.cfg.Nout (ScalarH v.1.root))}
    (hG : IsPaperFamily P.ready.cfg M Mnat law seedK freshK G m tA tf)
    (hGr : IsPaperFamily P.ready.cfg M Mnat law seedK freshK (G'.retained m P.ready.cfg.H
      P.ready.cfg.J) (m - 1) (tA + 3 * ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m) tf)
    (hm : P.mEnergy + 2 ≤ m) (hτ : 0 ≤ ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m)
    (htA : tA + 3 * ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tc)
    (htp : tp ∈ Set.Icc tc (tc + 4 * ocTauPP P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m))
    (htf : tc + 4 * ocTauPP P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tf)
    (hout : PaperPassageOutputAt P.ready.cfg P.Cpass law seedK freshK G G' m tc tf tp Preg)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) :
    PaperCycleSolutions P.ready.cfg seedK freshK m tc tp tf G (G'.retained m P.ready.cfg.H
      P.ready.cfg.J) Preg f := by
  have hU := paperFamily_solution P hΛ hDq hDΛ hband hterm Mnat law seedK freshK G m _ tf hG
    (by omega) tc (by linarith) (by linarith [htp.1, htp.2]) f
  obtain ⟨U, Uw, Uk, hUs⟩ := hU.1
  refine ⟨hU.1, hU.2, (hout f _ le_rfl U Uw Uk hUs).1, ?_⟩
  intro Y0 Y0' Y Y' Yw Yw' Yk Yk' htr hY htr' hY'
  have h0 := IterationPassage.ErrorJets.retainedTrace_unique G
    (G'.retained m P.ready.cfg.H P.ready.cfg.J) m P.ready.cfg.p tp (Preg f) Y0 Y0' htr htr'
  subst h0
  exact (paperFamily_solution P hΛ hDq hDΛ hband hterm Mnat law seedK freshK
    (G'.retained m P.ready.cfg.H P.ready.cfg.J) (m - 1) _ tf hGr (by omega) tp
    (htA.trans htp.1) (by linarith [htp.2]) Y0).2 Y Y' Yw Yw' Yk Yk' hY hY'

/-- Part (a) of one cycle: the preparation, in the marked norm. -/
private theorem paper_cycle_preparation_proof {cfg : FiniteParameters} {CQ Cp C : ℝ}
    (hC : |CQ| ≤ C) {D : OCData} {Mnat : ℕ} {law : BirthLaw} {seedK freshK : ℕ → KernelSpec}
    {m : ℕ} {tA tc tf tp : ℝ}
    {seed G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (hlev : G.level = m) (hε : 0 ≤ D.eps (m - 1))
    (hframe : PaperPassageFrameAt cfg CQ Cp Mnat law seedK freshK seed G G' m tA tc tf tp Preg)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) :
    PaperCyclePreparation cfg C law seedK freshK m tc tp tf G Preg f := by
  subst hlev
  obtain ⟨herr, hmodel, hreg, -⟩ := hframe.1.2.2.2.2 (G.marker law) (Or.inr rfl) f
  have hCQ : CQ ≤ C := (le_abs_self _).trans hC
  have hN : 0 ≤ weightedNorm 1 (G.mass law) (G.marker law) f := Real.sqrt_nonneg _
  have hE : 0 ≤ D.eps (G.level - 1) ^ cfg.Q := Real.rpow_nonneg hε _
  refine ⟨fun U Uw Uk hU => (herr U Uw Uk hU).trans ?_, hmodel.trans ?_, hreg.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCQ hE) hN
  · exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCQ hE)) hN
  · exact mul_le_mul_of_nonneg_right hCQ hN

/-- The successor clauses of a passage datum, with a larger constant. -/
private theorem paper_passageDatum_successor {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {law : BirthLaw} {Pp : ProvParams} {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {G Gr : GenStage D ScalarH Dm b j₀} {m p N depth sX sZ K Naux : ℕ}
    {s η₀ mu wexp Pacc Q C cr c₀ A s₀ tp tf : ℝ} {Sr : KernelSpec} {Nout : ℕ}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))}
    {f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)}
    {U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root)}
    {Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root)} (C' δ' : ℝ) (hC : C ≤ C')
    (hA : 0 ≤ A) (hε : 0 ≤ D.eps (m - 1)) (hδ : ocDelta D.α D.q = δ')
    (hd : PassageDatum law Pp seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc
      Q C cr c₀ A s₀ tp tf Sr Preg f U Y) :
    (∀ t ∈ Set.Icc tp tf, weightedNorm 1 (Gr.mass law) (Gr.marker law) (fun v => Y v t) ≤
      (1 + C' * (D.eps (m - 1) ^ Q + D.eps (m - 1) ^ δ')) * A) ∧
    ∃ (YN0 : ∀ v : CompIn Gr.comps, TorusHk Naux (ScalarH v.1.root))
      (YN : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (ScalarH v.1.root))
      (YNw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (ScalarH v.1.root))
      (YNk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (ScalarH u.1.root)),
      IsRetainedTrace G Gr m p tp (Preg f) YN0 ∧
      Gr.IsRegSolution Pp seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf
        YN0 (fun _ _ => 0) (fun _ _ => 0) YN YNw YNk ∧
      (∀ v, ∀ t ∈ Set.Icc tp tf, truncateTorusHk (Nat.zero_le Naux) (YN v t) = Y v t) ∧
      ComparisonClauses law Pp seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η₀ s₀ tp tf
        (C' * D.eps (m - 1) ^ Q * A) (C' * D.eps (m - 1) ^ Q * A) f YN := by
  obtain ⟨hamp, ⟨YN0, YN, YNw, YNk, htr, hsol, htrunc, -, -, hcmp⟩, -⟩ := hd
  subst hδ
  have hEQ : 0 ≤ D.eps (m - 1) ^ Q := Real.rpow_nonneg hε _
  have hX : 0 ≤ D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q :=
    add_nonneg hEQ (Real.rpow_nonneg hε _)
  have hb : C * D.eps (m - 1) ^ Q * A ≤ C' * D.eps (m - 1) ^ Q * A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hEQ) hA
  refine ⟨fun t ht => (hamp t ht).trans ?_, YN0, YN, YNw, YNk, htr, hsol, htrunc,
    paper_comparison_mono hcmp hb hb⟩
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hX)) hA

/-- Part (b) of one cycle: the successor amplitude and the comparison. -/
private theorem paper_cycle_successor_proof {cfg : FiniteParameters} {Cp C : ℝ} (hC : |Cp| ≤ C)
    {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q) {law : BirthLaw}
    {seedK freshK : ℕ → KernelSpec} {m : ℕ} {tc tf tp : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (hε : 0 ≤ D.eps (m - 1))
    (hout : PaperPassageOutputAt cfg Cp law seedK freshK G G' m tc tf tp Preg)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (hUex : ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + paperFamilyOrder cfg - 1) (ScalarH u.1.root)),
      G.IsRegSolution (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ (D.κ m) (streamVel (D.Φ m)) 0
        tc tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk) :
    PaperCycleSuccessor cfg C law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J) Preg f := by
  intro Y0 Y Yw Yk htr hY
  obtain ⟨U, Uw, Uk, hU⟩ := hUex
  exact paper_passageDatum_successor C _ ((le_abs_self _).trans hC) (Real.sqrt_nonneg _) hε
    (by rw [hDα, hDq]) ((hout f _ le_rfl U Uw Uk hU).2 Y0 Y Yw Yk htr hY)

/-- The exponent `χ = min{δ, μ_s}/8` is below the three passage exponents. -/
private theorem paper_chi_le {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ} (hs₀ : 0 < s)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    paperChi P.ready.cfg ≤ 5 * succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 4 ∧
      paperChi P.ready.cfg ≤ ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ∧
      paperChi P.ready.cfg ≤ ocDelta P.ready.cfg.α P.ready.cfg.q - 2 * P.ready.cfg.σ₀ := by
  have hvalid := P.ready.valid
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  have hδ := ocDelta_pos_of_admissible hvalid.hα₀ hvalid.hq
  have hμ := ocMuS_pos_of_admissible hvalid.hα₀ hs₀c hvalid.hq
  have hss := P.schedule.2.2.1
  have hσ₀ : P.ready.cfg.σ₀ = P.schedA + P.schedSigma := hss.2.2.2.2.2.1
  have haσ : P.schedA ≤ P.schedSigma := hss.2.2.2.2.2.2.2.1
  have hw := P.schedule.2.2.2.2.2.2.2.2
  have hDst : (0 : ℝ) ≤ (succDstar (paperOrderBound P.ready.cfg) P.ready.cfg.N P.ready.cfg.p
      P.ready.cfg.H : ℝ) := Nat.cast_nonneg _
  have h3 : 3 * P.schedSigma < ocDelta P.ready.cfg.α P.ready.cfg.q / 8 := by
    refine lt_of_lt_of_le (lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_right _ _))) ?_
    apply div_le_div_of_nonneg_left hδ.le (by norm_num)
    linarith
  have hmin := min_le_left (ocDelta P.ready.cfg.α P.ready.cfg.q)
    (ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s)
  have hmin' := min_le_right (ocDelta P.ready.cfg.α P.ready.cfg.q)
    (ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s)
  refine ⟨?_, ?_, ?_⟩
  · unfold paperChi succEta0
    rcases le_total (ocDelta P.ready.cfg.α P.ready.cfg.q / 8)
      (ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 4) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith
  · unfold paperChi
    linarith
  · unfold paperChi
    linarith

/-- The size bound of one passage from that of `PassageClauses`. -/
private theorem paper_passage_size_bound (E Cp C A a b c χ : ℝ) (X : ℝ≥0∞) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hA : 0 ≤ A) (hC : 3 * |Cp| ≤ C) (ha : χ ≤ a) (hb : χ ≤ b) (hc : χ ≤ c) :
    ENNReal.ofReal (1 + Cp * (E ^ a + E ^ b + E ^ c)) * X + ENNReal.ofReal (Cp * E ^ (2 : ℝ) * A) ≤
      ENNReal.ofReal (1 + C * E ^ χ) * X + ENNReal.ofReal (C * E * A) := by
  have hCp : 0 ≤ |Cp| := abs_nonneg _
  have hχ0 : 0 ≤ E ^ χ := Real.rpow_nonneg hE0.le _
  have hSa := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 ha
  have hSb := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hb
  have hSc := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hc
  have hS0 : 0 ≤ E ^ a + E ^ b + E ^ c := by
    have := Real.rpow_nonneg hE0.le a
    have := Real.rpow_nonneg hE0.le b
    have := Real.rpow_nonneg hE0.le c
    linarith
  have h1 : 1 + Cp * (E ^ a + E ^ b + E ^ c) ≤ 1 + C * E ^ χ := by
    have e1 : Cp * (E ^ a + E ^ b + E ^ c) ≤ |Cp| * (E ^ a + E ^ b + E ^ c) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hS0
    have e2 : |Cp| * (E ^ a + E ^ b + E ^ c) ≤ |Cp| * (3 * E ^ χ) :=
      mul_le_mul_of_nonneg_left (by linarith) hCp
    have e3 : |Cp| * (3 * E ^ χ) ≤ C * E ^ χ := by
      rw [← mul_assoc, mul_comm |Cp| 3]
      exact mul_le_mul_of_nonneg_right hC hχ0
    linarith
  have h2 : Cp * E ^ (2 : ℝ) * A ≤ C * E * A := by
    have hE2 : E ^ (2 : ℝ) ≤ E := by
      have := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (show (1 : ℝ) ≤ 2 by norm_num)
      rwa [Real.rpow_one] at this
    have hE20 : 0 ≤ E ^ (2 : ℝ) := Real.rpow_nonneg hE0.le _
    have hCC : |Cp| ≤ C := by linarith
    apply mul_le_mul_of_nonneg_right _ hA
    calc Cp * E ^ (2 : ℝ) ≤ |Cp| * E ^ (2 : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) hE20
      _ ≤ C * E := mul_le_mul hCC hE2 hE20 (by linarith)
  exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl) (ENNReal.ofReal_le_ofReal h2)

/-- One passage from the datum part of `iteration_passage`. -/
private theorem paper_passage_proof {cfg : FiniteParameters} {Cp C : ℝ} (χ : ℝ) (hC : 3 * |Cp| ≤ C)
    {D : OCData} (hq : 1 < D.q) (hΛD : 128 ≤ D.Λ) {law : BirthLaw}
    {seedK freshK : ℕ → KernelSpec} {m : ℕ} {tc tf tp : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (hε0 : 0 < D.eps (m - 1)) (hε1 : D.eps (m - 1) ≤ 1)
    (hχ : χ ≤ 5 * succEta0 cfg.α cfg.q cfg.s / 4 ∧ χ ≤ ocMuS cfg.α cfg.q cfg.s ∧
      χ ≤ ocDelta cfg.α cfg.q - 2 * cfg.σ₀)
    (hout : PaperPassageOutputAt cfg Cp law seedK freshK G G' m tc tf tp Preg) :
    PaperPassageConclusionExp cfg C χ law seedK freshK m tc tp tf G (G'.retained m cfg.H cfg.J)
      Preg := by
  intro f U Uw Uk hU Y0 Y Yw Yk htr hY
  have hd := (hout f _ le_rfl U Uw Uk hU).2 Y0 Y Yw Yk htr hY
  obtain ⟨-, ⟨YN0, YN, YNw, YNk, -, -, -, -, -, hcmp⟩, hpc, -⟩ := hd
  obtain ⟨CcT, PZ, aRep, û, hL⟩ := hcmp.1
  obtain ⟨⟨aU, aY, haU, haY⟩, hrest⟩ := hpc
  have hmass {S : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀} :
      ∀ v : CompIn S.comps, 0 < S.mass law v :=
    fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD law v.1
  refine ⟨⟨aU, aY, fun t ht => ⟨haU t ht, haY t ht⟩⟩, ?_⟩
  intro t ht rY hrY hYr
  have hval := paper_repOf_value _ hmass (fun v => Y v t) (aY t) (haY t ht) rY hrY hYr
  obtain ⟨-, -, -, hrec⟩ := hrest aU aY haU haY CcT hL.1 t ht
  obtain ⟨hrepU, hvalU, hsizeU⟩ := hrec rY hrY hval
  exact ⟨_, hrepU, paper_repOf_of_value _ hmass (fun v => U v t) (aU t) (haU t ht) _ hvalU,
    hsizeU.trans (paper_passage_size_bound _ _ _ _ _ _ _ _ _ hε0 hε1 (Real.sqrt_nonneg _) hC
      hχ.1 hχ.2.1 hχ.2.2)⟩

/-- The exponent `η₀ = succEta0 = min{δ/8, μ_s/4}` is below the three passage exponents. -/
private theorem paper_eta_le {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ} (hs₀ : 0 < s)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ≤
        5 * succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 4 ∧
      succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ≤
        ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ∧
      succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ≤
        ocDelta P.ready.cfg.α P.ready.cfg.q - 2 * P.ready.cfg.σ₀ := by
  have hvalid := P.ready.valid
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  have hδ := ocDelta_pos_of_admissible hvalid.hα₀ hvalid.hq
  have hμ := ocMuS_pos_of_admissible hvalid.hα₀ hs₀c hvalid.hq
  have hss := P.schedule.2.2.1
  have hσ₀ : P.ready.cfg.σ₀ = P.schedA + P.schedSigma := hss.2.2.2.2.2.1
  have haσ : P.schedA ≤ P.schedSigma := hss.2.2.2.2.2.2.2.1
  have hw := P.schedule.2.2.2.2.2.2.2.2
  have hDst : (0 : ℝ) ≤ (succDstar (paperOrderBound P.ready.cfg) P.ready.cfg.N P.ready.cfg.p
      P.ready.cfg.H : ℝ) := Nat.cast_nonneg _
  have h3 : 3 * P.schedSigma < ocDelta P.ready.cfg.α P.ready.cfg.q / 8 := by
    refine lt_of_lt_of_le (lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_right _ _))) ?_
    apply div_le_div_of_nonneg_left hδ.le (by norm_num)
    linarith
  have hη0 : 0 < succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s := by
    unfold succEta0
    exact lt_min (by linarith) (by linarith)
  have hηδ : succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ≤
      ocDelta P.ready.cfg.α P.ready.cfg.q / 8 := min_le_left _ _
  have hημ : succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s ≤
      ocMuS P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 4 := min_le_right _ _
  refine ⟨by linarith, by linarith, ?_⟩
  linarith

/-- **One passage at the exponent `η₀ = succEta0`** from the datum part of `iteration_passage` at
the parameters, for every constant `C ≥ 3|C_p|` (Proposition 4.4 of the paper). -/
theorem paper_passage_eta_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ} (hs₀ : 0 < s)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) {Cp C : ℝ} (hC : 3 * |Cp| ≤ C) {D : OCData}
    (hq : 1 < D.q) (hΛD : 128 ≤ D.Λ) {law : BirthLaw} {seedK freshK : ℕ → KernelSpec} {m : ℕ}
    {tc tf tp : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk P.ready.cfg.Nout (ScalarH v.1.root))}
    (hε0 : 0 < D.eps (m - 1)) (hε1 : D.eps (m - 1) ≤ 1)
    (hout : PaperPassageOutputAt P.ready.cfg Cp law seedK freshK G G' m tc tf tp Preg) :
    PaperPassageConclusionEta P.ready.cfg C law seedK freshK m tc tp tf G
      (G'.retained m P.ready.cfg.H P.ready.cfg.J) Preg :=
  paper_passage_proof _ hC hq hΛD hε0 hε1 (paper_eta_le hs₀ P) hout

/-- **One cycle with a free history start, and one passage**, at the parameters, for every constant
`C ≥ 3|C_pass|, |C_Q|`, for an admissible family `G` of level `m > m₀` on `[t_A, t_f]`,
`t_A + 3τ_m ≤ t_c`, `t_c + 4τ''_m ≤ t_f`: one preparation `(t_p, Π)` gives both conclusions, and it
is the preparation of a frame and a datum part of `iteration_passage`. -/
theorem paper_step_frame_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hCp : 3 * |P.Cpass| ≤ C) (hCQ : |P.CQpass| ≤ C) {D : OCData}
    (hDα : D.α = P.ready.cfg.α) (hDq : D.q = P.ready.cfg.q) (hDΛ : D.Λ = P.ready.cfg.Λ)
    (hDζ : D.ζ = P.ready.cfg.ζ)
    (hDΦ : IsOCStreamSeq P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ D.Φ) {M : ℕ}
    (hband : IsOCBandChain P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ P.ready.cfg.ζ M D.κ)
    (hterm : D.term = M) {Mnat : ℕ} (hMnat : M ≤ Mnat) {law : BirthLaw}
    (hlaw : IsSuccessorLaw P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s (paperWordCount P.ready.cfg)
      law) {seedK freshK : ℕ → KernelSpec}
    (hfresh : ∀ b', 1 ≤ b' → b' < M →
      IsFreshKernel D P.ready.cfg.kI.cr P.ready.cfg.σ₀ P.ready.cfg.nk.toPNat' b' (freshK b'))
    {m : ℕ} (hm : paperBottom P < m) {tA tc tf : ℝ}
    {G G' : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀}
    (hG : IsPaperFamily P.ready.cfg M Mnat law seedK freshK G m tA tf)
    (htA : tA + 3 * ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tc)
    (htf : tc + 4 * ocTauPP P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m ≤ tf)
    (hsucc : IsActualSuccessor D (paperProv P.ready.cfg D) (paperMenu P.ready.cfg Mnat) G G') :
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk P.ready.cfg.Nout (ScalarH v.1.root))),
      PaperCycleConclusionAt P.ready.cfg C M Mnat law seedK freshK m tA tc tp tf G
        (G'.retained m P.ready.cfg.H P.ready.cfg.J) Preg ∧
      PaperPassageConclusion P.ready.cfg C law seedK freshK m tc tp tf G
        (G'.retained m P.ready.cfg.H P.ready.cfg.J) Preg ∧
      (∃ seed : GenStage D ScalarH (paperFamilyOrder P.ready.cfg) P.ready.cfg.bw P.ready.cfg.j₀,
        PaperPassageFrameAt P.ready.cfg P.CQpass P.Cpass Mnat law seedK freshK seed G G' m tA tc
          tf tp Preg) ∧
      PaperPassageOutputAt P.ready.cfg P.Cpass law seedK freshK G G' m tc tf tp Preg := by
  have hmStar : P.mStar ≤ m := (le_max_left _ _).trans hm.le
  have hmE : P.mEnergy + 2 ≤ m :=
    Nat.succ_le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hm)
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hq : 1 < D.q := by rw [hDq]; exact P.ready.valid.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hε := Scales.epsilon_basic (m := m - 1) hq hΛD
  have hτ : 0 ≤ ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ m :=
    (Construction.Stream.ocTau_pos (by omega)).le
  have hlev : G.level = m := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := hG
    exact h
  obtain ⟨tS, seed, n, tp, Preg, htS, hseedP, hframe, hout⟩ :=
    paper_passage_at P hDα hDq hDΛ hDζ hDΦ hband hterm hMnat hlaw hfresh hmStar hG htA htf hτ
      hsucc
  have hfacts := paper_cycle_frame_facts hDα hDq hDΛ htS hseedP hlev hsucc hτ hframe
  have hCp' : |P.Cpass| ≤ C := by linarith [abs_nonneg P.Cpass]
  refine ⟨tp, Preg, ⟨hfacts.1, hfacts.2, fun f => ⟨?_, ?_, ?_⟩⟩, ?_, ⟨seed, hframe⟩, hout⟩
  · exact paper_cycle_solutions_proof P hΛ hDq hDΛ hband hterm hG hfacts.2 hmE hτ htA hfacts.1
      htf hout f
  · exact paper_cycle_preparation_proof hCQ hlev hε.1.le hframe f
  · exact paper_cycle_successor_proof hCp' hDα hDq hε.1.le hout f
      (paperFamily_solution P hΛ hDq hDΛ hband hterm Mnat law seedK freshK G m _ tf hG (by omega)
        tc (by linarith) (by linarith [hfacts.1.1, hfacts.1.2]) f).1
  · exact paper_passage_proof (paperChi P.ready.cfg) hCp hq hΛD hε.1 hε.2.1 (paper_chi_le hs₀ P)
      hout

/-- `PaperCycleConclusion` is the case `t_A = t_c - 3τ_m` of `PaperCycleConclusionAt`. -/
theorem paper_cycle_conclusion_of_at {cfg : FiniteParameters} {C : ℝ} {D : OCData} {M Mnat : ℕ}
    {law : BirthLaw} {seedK freshK : ℕ → KernelSpec} {m : ℕ} {tc tp tf : ℝ}
    {G Gr : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀}
    {Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))}
    (h : PaperCycleConclusionAt cfg C M Mnat law seedK freshK m
      (tc - 3 * ocTau cfg.α cfg.q cfg.Λ m) tc tp tf G Gr Preg) :
    PaperCycleConclusion cfg C M Mnat law seedK freshK m tc tp tf G Gr Preg := by
  have hGr := h.2.1
  rw [sub_add_cancel] at hGr
  exact ⟨h.1, hGr, h.2.2⟩

/-- **One cycle and one passage** at the parameters, for every constant `C ≥ 3|C_pass|, |C_Q|`: the
case
`t_A = t_c - 3τ_m` of `paper_step_frame_of_parameters`. -/
private theorem paper_step_proof {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (C : ℝ)
    (hCp : 3 * |P.Cpass| ≤ C) (hCQ : |P.CQpass| ≤ C) :
    PaperStepStatement P.ready.cfg (paperBottom P) C := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tc tf G
    G' hG htf hsucc
  obtain ⟨tp, Preg, hcyc, hpass, -⟩ :=
    paper_step_frame_of_parameters hs₀ hΛ P C hCp hCQ hDα hDq hDΛ hDζ hDΦ hband hterm hMnat hlaw
      hfresh hm hG (sub_add_cancel _ _).le htf hsucc
  exact ⟨tp, Preg, paper_cycle_conclusion_of_at hcyc, hpass⟩

/-- **The cascade, one cycle and one passage at the parameters `P`**, with
`m₀ = paperBottom P ≥ m_*`. -/
theorem paper_cascade_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (_htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ C : ℝ, 0 < C ∧ P.mStar ≤ paperBottom P ∧
      PaperStepStatement P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  refine ⟨max (3 * |P.Cpass|) (max |P.CQpass| (max |P.ready.cfg.Ccas| 1)),
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    le_max_left _ _, paper_step_proof hs₀ hΛ P _ (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)),
    paper_cascade_proof hΛ ht₀ P _ ((le_abs_self _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))⟩

/-- **The cascade, one cycle and one passage at one choice of parameters**, in the setting of the
entry statement `paper_entry`: one choice of parameters `P` satisfies the entry statement with
a constant `C_E` and the three statements with a constant `C > 0` and `m₀ = paperBottom P ≥ m_*`. -/
theorem paper_cascade_cycle_passage (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
    ∃ (P : PaperParameters α s q ζ Λ Jw t₀ T₀) (CE C : ℝ),
      PaperEntryStatement P.ready.cfg P.ready.Mstar CE ∧
      0 < C ∧ P.mStar ≤ paperBottom P ∧
      PaperStepStatement P.ready.cfg (paperBottom P) C ∧
      PaperCascadeStatement P.ready.cfg (paperBottom P) C := by
  obtain ⟨Λ₀, hΛ₀, hP⟩ := paper_parameters_exist α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Jw hJw t₀ T₀ ht₀ htT => ?_⟩
  obtain ⟨P⟩ := hP Λ hΛ Jw hJw t₀ T₀ ht₀ htT
  obtain ⟨CE, hE⟩ := paper_entry_of_ready hs₀ (hΛ₀.trans hΛ) ht₀ htT P.ready
  obtain ⟨C, hC, hm, hstep, hcas⟩ := paper_cascade_of_parameters hs₀ (hΛ₀.trans hΛ) ht₀ htT P
  exact ⟨P, CE, C, hE, hC, hm, hstep, hcas⟩

end AVRegularity.PaperFacing
