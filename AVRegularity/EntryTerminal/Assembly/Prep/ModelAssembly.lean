-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients
public import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
public import AVRegularity.Definitions.Families.ActualFamily
import AVRegularity.Construction.Scales.Times

section
/-! **The joint core of `cycle_joint` at an abstract radius** (the form needed by the terminal instance).

`JointPremisesAbs` is `JointPremises` with:
- the cascade radius `ocRhoMol α q Λ m cMol ν` replaced by a radius parameter `r` in the cover,
  the envelope and the pointwise envelope;
- `hρold` replaced by `0 < ρold` and `ρold ≤ COld √(B τ'')` (the patch mesh bound);
- `hρrat` replaced by `r / ρold ≤ Crat ε_{m-1}^{-qδ}`.

All other fields are unchanged. `RawJointAbsStatement` is `RawJointGenStatement` over these
premises, bundled; the bridge from the unbundled statement is an unpacking. Its conclusion
measures the error at the radius `r` against the datum prepared at `ρold`.

The level-C ingredients see the radius only through the five cover clauses `pos`, `rho_e`,
`rho_R`, `drift_scale` and `drift_small`. The ratio clause is the price of measuring at `r` a
datum prepared at `ρold`.

For `r = ρold` the ratio clause reads `1 ≤ Crat ε_{m-1}^{-qδ}`, true for `Crat ≥ 1`, and
`ρold ≤ √(B τ'')` is the cover's `rho_R`, so `COld = 1`. For an edge-free family the `L²`
near-contraction clause applies. The case `m = M'` is allowed (`hmM : m ≤ M'`). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.CycleJointProofs.Assembly

/-- The `JointPremises` at the radius `r`, with the prepared radius `ρold` abstract. -/
structure JointPremisesAbs (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ) : Prop where
  hπ : ∀ x, 0 < π x
  hK : ∀ x, K x ≤ Kmax
  hΦ : IsOCStreamSeq α q Λ ζ Φ
  hband : IsOCBandChain α q Λ ζ M' κ
  hm2 : 2 ≤ m
  hmStar : mStar ≤ m
  hmM : m ≤ M'
  hν : κ m = ν
  hB : κ (m - 1) = B
  cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m) r g g₀ a B₀ lam Cb qJ Kmax
    CG l₀ P y₀
  hwmeas : ∀ p, Measurable (F.weight p)
  hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
    tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F
  hdepth : F.HasDepthAtMost H
  hdesc : F.IsDescending K
  htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1))
  hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output
  hmeas : F.IsTimeMeasurable
  hΘ₀ : 0 ≤ Θ
  hΘ₁ : Θ ≤ 1
  henv : IsEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
    (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm
  hpointwise : IsPointwiseMolecularEnvelope F π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) r
    Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)
  htrans : F.IsTransverseOnPulses
    (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
      (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1)
  hquiet : F.IsFastIndependentOn
    (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m) (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
  hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
  hρold : 0 < ρold
  hρR : ρold ≤ COld * Real.sqrt (B * ocTauPP α q Λ m)
  hρrat : r / ρold ≤ Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))

/-- The conclusion of the joint core for one family: one linear operator `Tm` with the
mass-weighted model bound at `c √(B τ'')`, the `L²` near-contraction for edge-free families, and
the physical error at the radius `r` against the datum prepared at `ρold`, at the endpoint
`t_p = (l₀ + 3/2) τ''`. -/
def RawJointAbsConclusion (α q : ℝ) (Λ : ℕ) (Pacc : ℝ) (Mout D : ℕ) (C CP c : ℝ)
    {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (ν B tS : ℝ) (l₀ : ℤ)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (r ρold : ℝ) : Prop :=
  ∃ Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)),
    IsRawMassModel π K Mout (c * Real.sqrt (B * ocTauPP α q Λ m)) C Tm ∧
    ((∀ v u, IsEmpty (F.Γ v u)) →
      IsRawMassL2 π K Mout (1 + CP * ocEpsilon q Λ (m - 1) ^ Pacc) Tm) ∧
    IsRawMassError π K Mout D ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) r ρold
      (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Tm

/-- The family clause of the joint core at an abstract radius, after the constants: every
family with the premises at the radius `r` and the prepared radius `ρold` has the conclusion. -/
def RawJointAbsFamily (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ Pacc : ℝ)
    (Mout H D Kmax Ks Ls Jm qJ Jchart : ℕ) (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ)
    (Cpad Cage : ℝ) (Npad : ℕ) (C CP c : ℝ) (mStar : ℕ) : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ),
    JointPremisesAbs α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat Cm CG Cchart
      Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold →
    RawJointAbsConclusion α q Λ Pacc Mout D C CP c π K Φ m ν B tS l₀ F actual r ρold

/-- **The joint core at an abstract radius** (open). `RawJointStatement` with the cascade
radius replaced by `r` and the prepared radius abstract. The constants precede the family, the
level and both radii. -/
def RawJointAbsStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ), Kmax + D + 2 ≤ Jchart ∧ Kmax + D + 2 ≤ Jm ∧
      ∀ (Ca Cth Cb COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ),
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ CP ∧
      RawJointAbsFamily.{u, v, w, x} α q Λ ζ g₀ Pacc Mout H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb
        COld Crat Cm CG Cchart Cpad Cage Npad C CP c mStar

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The parts of the capped preparation** (`entry_terminal_preparation`, the preparation of
Proposition 14.10(a) of the paper, in its capped form). The parts are stated over the bundle
`PrepArgs` of the statement's own binders, so that the assembly proves the statement.

| Part | Steps | Instance |
|---|---|---|
| `PrepAnchorPart` | Step 1: the complete cover from the incoming phase to the endpoint `t_p = (l₀ + 3/2) h` of the window `[a_M, a_M + 2h]` (`l₀` the renewal block of `a_M`), quiet and the midpoint of a quiet margin (the renewal quiet margin, half-width `τ'_M = h/L_M`) ending before `a + T₀`, `ch ≤ t_p - a_M ≤ Ch` | preparation chart schedule and quiet endpoint selection; the quiet margin is a parameter |
| `PrepModelPart` | Steps 2-5: the finite source core, weighted energy at the capped radius, patches and assembly, normalization | composite (`prepModel_of_parts`): the joint core at an abstract radius `RawJointAbsStatement` at `r = ρold = ϱ ≤ c_K x`, `m = M`; the joint premises `PrepFamilyPart`; the core `PrepCorePart`; the normalization `PrepNormPart` |
| `PrepInterpPart` | Step 6: same-error interpolation at the reserve `2k₀+2` | proved separately: `‖∇^j w‖ ≤ ‖w‖^{1/2}‖∇^{2j}w‖^{1/2}` on the torus, the paired family's jets, and `x ≤ ρ` |

Constants: the anchor gives `c, C₁`; the model gives `C_M` after them; the interpolation gives `C_I`
after `C_M`; the statement's `C` is their maximum.

For an empty weak family the model is the zero map on an empty product, and the anchor exists by
the cover. A quiet margin of width `0` (`t_p` quiet, `t_p ≤ a + T₀`) is allowed. -/

/-- The data of `entry_terminal_preparation` between `Λ` and `K_out`. -/
structure PrepArgs (X : TermConstruction) where
  Λ : ℕ
  c₀max : ℝ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  bw : ℝ
  Jw : ℕ
  Lw : ℕ
  dW : ℕ
  DW : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  σw : ℝ
  χw : ℝ
  η₀ : ℝ
  PT : ℝ
  NT : ℕ
  pT : ℕ
  RT : ℕ
  AT : ℕ
  k₀ : ℕ
  LcT : ℕ
  LoT : ℕ
  LfT : ℕ
  LpT : ℕ
  tT : ℝ
  QT : ℝ

/-- The hypotheses of `entry_terminal_preparation` on its data, in the statement's order. -/
def PrepArgs.Valid {X : TermConstruction} (PA : PrepArgs X) : Prop :=
  0 < PA.c₀max ∧
  (ContDiff ℝ (⊤ : ℕ∞) PA.φ₀ ∧ (∀ z, 0 ≤ PA.φ₀ z) ∧ ∫ z, PA.φ₀ z = 1 ∧
    Function.support PA.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) ∧
  (0 < PA.bw ∧ PA.bw ≤ 1 / 10000) ∧
  (1 ≤ PA.Jw ∧ 0 < PA.τ ∧ PA.τ < PA.T₀ ∧ 0 < PA.Pw ∧ 0 < PA.σw ∧
    PA.σw < min (ocC X.α X.q) (X.q - 1) ∧ 0 < PA.χw ∧ 0 < PA.η₀ ∧ PA.η₀ ≤ ocDelta X.α X.q / 8) ∧
  0 < PA.PT ∧
  IsTerminalSchedule X.α X.q X.s PA.PT PA.QT PA.σw PA.χw PA.η₀ PA.tT PA.Jw PA.Lw PA.k₀ PA.NT PA.pT
    PA.RT PA.AT PA.LcT PA.LoT PA.LfT PA.LpT (termAlphabet PA.NT PA.pT PA.DW PA.dW)

/-- The hypotheses of the statement on the construction data at level `M`. -/
def IsPrepData (X : TermConstruction) (Λ M : ℕ) (D : OCData) : Prop :=
  D.α = X.α ∧ D.q = X.q ∧ D.Λ = Λ ∧ D.ζ = X.ζ ∧ IsOCStreamSeq X.α X.q Λ X.ζ D.Φ ∧
    IsOCBandChain X.α X.q Λ X.ζ M D.κ ∧ D.term = M


/-- The renewal block `l₀` of `a_M` at the period `h`: `(l₀ - 1/2) h ≤ a_M < (l₀ + 1/2) h`. -/
def prepBlock (h aM : ℝ) : ℤ := ⌊aM / h + 1 / 2⌋

/-- The preparation endpoint `t_p = (l₀ + 3/2) h` of the window `[a_M, a_M + 2h]`
(`RawJointStatement`: the first renewal after `t_S` plus `τ''`). -/
def prepEndpoint (h aM : ℝ) : ℝ := ((prepBlock h aM : ℝ) + 3 / 2) * h

/-- **Anchor at one level** (Step 1): the endpoint `t_p = (l₀ + 3/2) h` of the window is quiet,
with `c h ≤ t_p - a_M ≤ C₁ h`, and is the midpoint of a quiet margin ending before `a + T₀` (the
renewal quiet margin of half-width `τ'_M = h/L_M`; no uniform multiple of `h` is quiet around `t_p`). -/
def PrepAnchorAtM {X : TermConstruction} (PA : PrepArgs X) (nW : ℕ+) (CL Cχ : ℝ) (kW : InvConsts)
    (c C₁ : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∃ tp w : ℝ, tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ M ∧ aM + c * D.termH M ≤ tp ∧
    tp ≤ aM + C₁ * D.termH M ∧ 0 ≤ w ∧
    Set.Icc (tp - w) (tp + w) ⊆ ocQuietTimes D.α D.q D.Λ D.ζ M ∧ tp + w ≤ a + PA.T₀ ∧
    tp = prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM ∧ ocTauP D.α D.q D.Λ M ≤ w

/-- **The model at one level** (Steps 2-5): for an anchor of the part above, a linear map fixing
constant component vectors with the model bound `(e.term.model)` and the model error
`(e.term.model.error)` at the accuracy `Q_T`. -/
def PrepModelAtM {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (_hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (c C₁ CM : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∀ tp w : ℝ, tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ M → aM + c * D.termH M ≤ tp →
    tp ≤ aM + C₁ * D.termH M → 0 ≤ w →
    Set.Icc (tp - w) (tp + w) ⊆ ocQuietTimes D.α D.q D.Λ D.ζ M → tp + w ≤ a + PA.T₀ →
    tp = prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM →
  ∃ Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) (ScalarH v.1.root)),
    (∀ (cv : CompIn Gw.comps → ℝ) (X' : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)),
      (∀ v, (X' v).toFunction.jet (valueIndex2 Kw) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) →
      ∀ v, (Pterm X' v).toFunction.jet (valueIndex2 (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) ∧
    ∀ (f : Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
        (ScalarH u.1.root)),
      IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk
        Vk →
      weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) (Pterm fun v => V v aM) ≤
          CM * Real.sqrt (l2NormSq f) ∧
        weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp) -
              truncateTorusHk (Nat.zero_le (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))) (Pterm (fun v => V v aM) v)) ≤
          CM * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f)

/-- **Interpolation at one level** (Step 6): the two model bounds give the bound at the capped radius
and the slot `k₀`, at the accuracy `Q_T/2`. -/
def PrepInterpAtM {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (CM CI : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) (ScalarH v.1.root))),
    aM ≤ tp → tp ≤ a + PA.T₀ →
  ∀ (f : Vec 2 → ℝ)
    (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
    (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
      (ScalarH u.1.root)),
    IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
    weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) (Pterm fun v => V v aM) ≤
        CM * Real.sqrt (l2NormSq f) →
    weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le Kw) (V v tp) -
          truncateTorusHk (Nat.zero_le (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))) (Pterm (fun v => V v aM) v)) ≤
        CM * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f) →
    weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1)
        (fun v => truncateTorusHk hk₀w (V v tp) -
          truncateTorusHk (k0_le_khat Kout PA.k₀ PA.NT PA.pT) (Pterm (fun v => V v aM) v)) ≤
      CI * D.eps (M - 1) ^ (PA.QT / 2) * Real.sqrt (l2NormSq f)

/-- The prefix of the parts of the capped preparation (the statement's, from the public order to the weak constants). -/
def PrepPartPrefix (B : (X : TermConstruction) → (PA : PrepArgs X) → (Kout Kw Lt : ℕ) → (nW : ℕ+) →
    PA.k₀ ≤ Kw → ℝ → ℝ → ℝ → ℝ → ℝ → InvConsts → Prop) : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ PA : PrepArgs X, Λ₀ ≤ PA.Λ → PA.Valid →
  ∀ Kout : ℕ, ∃ Kneed : ℕ,
  ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : PA.k₀ ≤ Kw) (cr : ℝ), Kneed ≤ Kw → PA.LpT ≤ Lt →
    Lt + 1 ≤ 2 * (nW : ℕ) → 0 < cr → cr ≤ 1 →
  ∀ (cK CK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    Kneed ≤ kW.Ks → Kneed ≤ kW.Kan → Kneed ≤ kW.Lan → Kneed ≤ kW.Jm → Lt ≤ kW.Lker →
  B X PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW

/-- **Part 1, the anchor** (chart schedule and quiet endpoint). The incoming phase may be at the
start of a pulse or at the start of a quiet interval. -/
def PrepAnchorPart : Prop :=
  PrepPartPrefix fun _ PA _ _ _ nW _ _ _ _ CL Cχ kW =>
    ∃ c C₁ : ℝ, 0 < c ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → PrepAnchorAtM PA nW CL Cχ kW c C₁ j₀ M

/-- **Part 2, the model** (composite: copy chain, weighted energy at `c_K x`, the per-patch
preparation, normalization). For zero datum `Pterm (V a_M) = 0`. -/
def PrepModelPart : Prop :=
  PrepPartPrefix fun _ PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW =>
    ∀ c C₁ : ℝ, 0 < c → ∃ CM : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepModelAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M

/-- **Part 3, the interpolation** (routine). For `k₀ = 0` the bound is the
`L²` bound at the radius `c_K x`. -/
def PrepInterpPart : Prop :=
  PrepPartPrefix fun _ PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW =>
    ∀ CM : ℝ, ∃ CI : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepInterpAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW CM CI j₀ M

/-- The capped preparation at one threshold level `M` (the statement's text from the data onwards, over `PrepArgs`). -/
def PrepGoalAtM {X : TermConstruction} (PA : PrepArgs X) (Kout : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : PA.k₀ ≤ Kw) (cr : ℝ) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (kW : InvConsts) (c : ℝ) (C : ℝ) (j₀ : ℕ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = X.α → D.q = X.q → D.Λ = PA.Λ → D.ζ = X.ζ → IsOCStreamSeq X.α X.q PA.Λ X.ζ D.Φ →
    IsOCBandChain X.α X.q PA.Λ X.ζ M D.κ → D.term = M →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw Gw aM →
  ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) (ScalarH v.1.root))),
    IsTerminalPrepMap M Kw (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) c C Gw aM tp Pterm ∧
    ∀ (f : Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1) (ScalarH u.1.root)),
      IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
      IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) PA.k₀ hk₀w (le_trans (by omega : PA.k₀ ≤ 2 * PA.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C PA.QT f Gw aM tp Pterm V

/-! **The capped preparation from its parts** (`preparation_of_parts`): the
statement `entry_terminal_preparation` (its text copy `PreparationStatement`) from the anchor, the
model and the interpolation parts and the positivity of the scales.

The statement's constants are:
- `c` from the anchor;
- `C = max C₁ (max C_M C_I)`.

The location bound `t_p ≤ a_M + C h`, and the three model bounds at `C`, follow from `h ≥ 0` and
`E > 0`. -/

/-- **The three parts at one level give the capped preparation at that level.** -/
theorem prepGoalAtM_of_parts {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (c C₁ CM CI C : ℝ) (j₀ M : ℕ)
    (hc : 0 < c) (hC₁ : C₁ ≤ C) (hCM : CM ≤ C) (hCI : CI ≤ C)
    (hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q PA.Λ k)
    (hεpos : ∀ D : OCData, D.q = X.q → D.Λ = PA.Λ → ∀ k, 0 < D.eps k)
    (hAn : PrepAnchorAtM PA nW CL Cχ kW c C₁ j₀ M)
    (hMo : PrepModelAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M)
    (hIn : PrepInterpAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW CM CI j₀ M) :
    PrepGoalAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C j₀ M := by
  intro D hDα hDq hDΛ hDζ hstream hband hterm a lawW PW Gw aM Ww hW
  have hD : IsPrepData X PA.Λ M D := ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩
  have hh : 0 ≤ D.termH M := by
    show 0 ≤ ocTauPP D.α D.q D.Λ M
    rw [hDα, hDq, hDΛ]
    exact hTnn M
  have hε : 0 < D.eps (M - 1) := hεpos D hDq hDΛ (M - 1)
  obtain ⟨tp, w, hq, hlo, hhi, hw, hcol, htf, htpe, hwτ⟩ := hAn D hD a lawW PW Gw aM hW
  obtain ⟨Pterm, hconst, hbounds⟩ := hMo D hD a lawW PW Gw aM hW tp w hq hlo hhi hw hcol htf htpe
  have hch : 0 ≤ c * D.termH M := mul_nonneg hc.le hh
  have haM : aM ≤ tp := le_trans (le_add_of_nonneg_right hch) hlo
  have htp : tp ≤ a + PA.T₀ := le_trans (le_add_of_nonneg_right hw) htf
  have hhi' : tp ≤ aM + C * D.termH M :=
    le_trans hhi (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC₁ hh))
  -- the quiet margin of half-width `τ'_M` inside the anchor's quiet margin
  have hcolτ : Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M :=
    fun t ht => hcol ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨tp, Pterm, by unfold IsTerminalPrepMap; exact ⟨hq, hlo, hhi', hconst, hcolτ⟩, ?_⟩
  intro f U₀ U V Uw Vw Uk Vk hpaired
  obtain ⟨b1, b2⟩ := hbounds f U₀ U V Uw Vw Uk Vk hpaired
  have b3 := hIn D hD a lawW PW Gw aM hW tp Pterm haM htp f U₀ U V Uw Vw Uk Vk hpaired b1 b2
  have hs : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have he1 : 0 ≤ D.eps (M - 1) ^ PA.QT := Real.rpow_nonneg hε.le _
  have he2 : 0 ≤ D.eps (M - 1) ^ (PA.QT / 2) := Real.rpow_nonneg hε.le _
  unfold IsTerminalPrepBounds
  exact ⟨b1.trans (mul_le_mul_of_nonneg_right hCM hs),
    b2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM he1) hs),
    b3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCI he2) hs)⟩

/-- The constants and thresholds of the capped preparation from the three parts, after the weak constants. -/
theorem prep_consts_of_parts {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts)
    (hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q PA.Λ k)
    (hεpos : ∀ D : OCData, D.q = X.q → D.Λ = PA.Λ → ∀ k, 0 < D.eps k)
    (hA : ∃ c C₁ : ℝ, 0 < c ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepAnchorAtM PA nW CL Cχ kW c C₁ j₀ M)
    (hM : ∀ c C₁ : ℝ, 0 < c → ∃ CM : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepModelAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M)
    (hI : ∀ CM : ℝ, ∃ CI : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepInterpAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW CM CI j₀ M) :
    ∃ (c C : ℝ), 0 < c ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepGoalAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C j₀ M := by
  obtain ⟨c, C₁, hc, hA'⟩ := hA
  obtain ⟨CM, hM'⟩ := hM c C₁ hc
  obtain ⟨CI, hI'⟩ := hI CM
  refine ⟨c, max C₁ (max CM CI), hc, fun j₀ => ?_⟩
  obtain ⟨M1, h1⟩ := hA' j₀
  obtain ⟨M2, h2⟩ := hM' j₀
  obtain ⟨M3, h3⟩ := hI' j₀
  refine ⟨max M1 (max M2 M3), fun M hM => ?_⟩
  exact prepGoalAtM_of_parts PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM CI _ j₀ M hc
    (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _)) hTnn hεpos (h1 M (m2l hM))
    (h2 M (m2l (m2r hM))) (h3 M (m2r (m2r hM)))

/-- The capped preparation over the bundled data, from its parts. -/
theorem prep_bundled_of_parts (hA : PrepAnchorPart) (hM : PrepModelPart) (hI : PrepInterpPart)
    (hsf : ScaleFactsStatement) :
    ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ PA : PrepArgs X, Λ₀ ≤ PA.Λ → PA.Valid →
    ∀ Kout : ℕ, ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : PA.k₀ ≤ Kw) (cr : ℝ), Kneed ≤ Kw → PA.LpT ≤ Lt →
      Lt + 1 ≤ 2 * (nW : ℕ) → 0 < cr → cr ≤ 1 →
    ∀ (cK CK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      Kneed ≤ kW.Ks → Kneed ≤ kW.Kan → Kneed ≤ kW.Lan → Kneed ≤ kW.Jm → Lt ≤ kW.Lker →
    ∃ (c C : ℝ), 0 < c ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepGoalAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C j₀ M := by
  intro X
  obtain ⟨Λ1, h1Λ, hA1⟩ := hA X
  obtain ⟨Λ2, h2Λ, hM1⟩ := hM X
  obtain ⟨Λ3, h3Λ, hI1⟩ := hI X
  refine ⟨max Λ1 (max Λ2 Λ3), le_trans h1Λ (le_max_left _ _), fun PA hΛ hPA Kout => ?_⟩
  obtain ⟨-, hTnn, hεpos⟩ := hsf X PA.Λ (le_trans h1Λ (m2l hΛ))
  obtain ⟨K1, hA2⟩ := hA1 PA (m2l hΛ) hPA Kout
  obtain ⟨K2, hM2⟩ := hM1 PA (m2l (m2r hΛ)) hPA Kout
  obtain ⟨K3, hI2⟩ := hI1 PA (m2r (m2r hΛ)) hPA Kout
  refine ⟨max K1 (max K2 K3), ?_⟩
  intro Kw Lt nW hk₀w cr hKw hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW hKs hKan hLan hJm hLker
  exact prep_consts_of_parts PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW hTnn hεpos
    (hA2 Kw Lt nW hk₀w cr (m2l hKw) hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW (m2l hKs) (m2l hKan)
      (m2l hLan) (m2l hJm) hLker)
    (hM2 Kw Lt nW hk₀w cr (m2l (m2r hKw)) hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW (m2l (m2r hKs))
      (m2l (m2r hKan)) (m2l (m2r hLan)) (m2l (m2r hJm)) hLker)
    (hI2 Kw Lt nW hk₀w cr (m2r (m2r hKw)) hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW (m2r (m2r hKs))
      (m2r (m2r hKan)) (m2r (m2r hLan)) (m2r (m2r hJm)) hLker)

/-- **The capped preparation from its parts.** -/
theorem preparation_of_parts (hA : PrepAnchorPart) (hM : PrepModelPart) (hI : PrepInterpPart)
    (hsf : ScaleFactsStatement) : PreparationStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, h⟩ := prep_bundled_of_parts hA hM hI hsf
    ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  refine ⟨Λ₀, h128, ?_⟩
  intro Λ hΛ c₀max hc0 φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw0 hbw1 Jw Lw dW DW τ T₀ Pw σw χw η₀ hJw hτ
    hτT hPw hσw0 hσw1 hχw hη0 hη1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched Kout
  exact h ⟨Λ, c₀max, φ₀, hφ₀, bw, Jw, Lw, dW, DW, τ, T₀, Pw, σw, χw, η₀, PT, NT, pT, RT, AT, k₀,
      LcT, LoT, LfT, LpT, tT, QT⟩ hΛ
    ⟨hc0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩, ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩,
      hPT, hsched⟩ Kout

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.EntryTerminal.Route

/-! **The parts of the model of the capped preparation** (Steps 2-5 of the capped preparation).
`PrepModelPart` follows from the joint core at an abstract radius
(`RawJointAbsStatement`, instantiated at the radius `ϱ ≤ c_K x`) and five terminal parts.

The joint core is instantiated on the actual-context family `F⋆ = Gw.actualFamily` of the weak
stage: one context per piece, the actual one, with the fields of the stage on the output window of
the piece and zero outside it; the actual contexts are `fun _ => ()`. Its edge coefficients are
those of `Gw` (`GenStage.edgeCoefficient_actualFamily`), so the core clause on `Gw` feeds the
conclusion of the joint core on `F⋆`.
The instance has:
- `m = M' = M`, `ν = κ_M`, `B = κ_{M-1}`;
- the window `[a_M, a_M + 2h]` and the endpoint `t_p = (l₀ + 3/2) h`;
- `r = ρold = ϱ`.

The copy chain of Step 2 is bookkeeping: its copy-sum is the plain coupled torus solution of
`Gw.fam` from the datum `V(a_M)`.

| Part | Step | Instance |
|---|---|---|
| `PrepCoverPart` | the window cover `IsWindowCover` at level `M` on `[a_M, a_M + 2h]` at every radius `ρs ≤ c_cov x`, with a uniform `c_cov > 0` | see the cover note below |
| `PrepChartPart` | the chart certificate `IsPreparationChartCertificate` of `Gw.fam` on the window | schedule: `preparation_chart_schedule` with `CH = 2`, from the natural pieces of `IsWeakStage` (`IsStageInvariant … (M + J_w)`, whose first conjunct is `Gw.IsNatural (M + J_w)`); flow jets: see the note |
| `PrepFamilyPart` | the other premises of the joint core on `F⋆` (`PrepFamilyPremises`): masses, slots, depth, descent, torus compatibility, the cover by the pieces, measurability, the envelopes at `ϱ = min{c_K, c_cov} x`, transversality, fast independence, the atlas | proved: `prepFamilyPart`, each field from `IsWeakStage` through the actual-family adapter. Envelopes: the envelope clause of the stage invariant and `IsSeedPointwiseMolecular`, at `rhoStar = c_K x` (Péclet cap), lowered to `ϱ` at the factor `(c_K/min{c_K, c_cov})^{D_W-2}` (`molecularEnvelope_rescale`; the generic producer is not used, its carrier input is not available for every `j₀`). Slots: `D_W(d_W - rank)`. Cover: the natural partition. Transversality, fast independence, torus compatibility, depth and the atlas (`actualAtlas`): the stage invariant. Measurability: `GenStage.isTimeMeasurable_actualFamily_of_certified` |
| `RawJointAbsStatement` | Steps 3-4: weighted energy at the capped radius, patches, assembly | the joint core (`RawJointGenStatement`) at `r = ρold = ϱ`, `COld = Crat = 1` |
| `PrepCorePart` | Step 2: the finite source core, `‖V(t_p) - u(t_p)‖_π ≤ C x^{χ_w + σ_w L_t}‖f‖` | proved separately |
| `PrepNormPart` | Step 5: normalization on constants and the two model bounds | proved separately (the normalization pattern `Π₀ + Q₀ Tm Q₀` with mean conservation) |

For an empty weak family every clause is about an empty product, and `Pterm = 0`. For an
edge-free weak family `u` solves the scalar equations and the core error is the kernel error. For
`c_K` large, `ϱ = c_cov x < c_K x`, and the datum's norm at `ϱ` is at most its norm at `c_K x`;
for `c_K ≤ c_cov`, `ϱ = c_K x`. For `a_M = (l₀ - 1/2) h` the cover has `P = 2` charts. -/

/-- **The cover at one level.** On the window `[a_M, a_M + 2h]` from any `a_M`, the cover data at
level `M` with the window cover at every radius `ρs ∈ (0, c_cov x]`. -/
def PrepCoverAtM {X : TermConstruction} (PA : PrepArgs X) (ccov g₀ Cb : ℝ) (qJ Kmax : ℕ)
    (CG : ℕ → ℝ) (M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (hφ : IsAdmissibleStream (D.Φ (M - 1))) (aM : ℝ),
  ∃ (g aD B₀ lam : ℝ) (P : ℕ) (y₀ : Vec 2),
  ∀ ρs : ℝ, 0 < ρs → ρs ≤ ccov * ocEpsilon X.q PA.Λ M →
    IsWindowCover X.α X.q PA.Λ M X.ζ D.Φ hφ (D.κ M) (D.κ (M - 1)) aM
      (aM + 2 * ocTauPP X.α X.q PA.Λ M) ρs g g₀ aD B₀ lam Cb qJ Kmax CG
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) P y₀

/-- **The chart certificate at one level.** For the actual weak stage and every number `P` of
core charts whose blocks reach the end of the window, the preparation chart certificate of
`Gw.fam` on `[a_M, a_M + 2h]` from the block `l₀` of `a_M`. -/
def PrepChartAtM {X : TermConstruction} (PA : PrepArgs X) (nW : ℕ+) (CL Cχ : ℝ) (kW : InvConsts)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∀ (hφ : IsAdmissibleStream (D.Φ (M - 1))) (P : ℕ), 1 ≤ P →
    aM + 2 * ocTauPP X.α X.q PA.Λ M ≤
      ((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + P - 1 / 2) * ocTauPP X.α X.q PA.Λ M →
    IsPreparationChartCertificate X.α X.q PA.Λ M (D.Φ (M - 1)) hφ aM
      (aM + 2 * ocTauPP X.α X.q PA.Λ M) Cpad Cage Npad Jchart Cchart
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) P Gw.fam

/-- The premises of the joint core on the actual-context family `F⋆ = Gw.actualFamily` of the weak stage at
level `M` other than the cover and the chart certificate, on the window `[t_S, t_S + 2h]` at the
radius `ϱ`. -/
structure PrepFamilyPremises {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (α q : ℝ) (Λ : ℕ)
    (ζ : ℝ → ℝ) (H Kmax Ks Ls Jm : ℕ) (Ca Cth : ℝ) (Cm : ℕ → ℝ) (M : ℕ) (law : BirthLaw)
    (Gw : GenStage D ScalarH Dm b j₀) (tS : ℝ) (K : CompIn Gw.comps → ℕ)
    (A : Matrix (CompIn Gw.comps) (CompIn Gw.comps) ℝ) (Θ : ℝ) (T : Gw.actualFamily.Atlas)
    (ϱ : ℝ) : Prop where
  hπ : ∀ x, 0 < Gw.mass law x
  hK : ∀ x, K x ≤ Kmax
  hwmeas : ∀ p, Measurable (Gw.actualFamily.weight p)
  hdepth : Gw.actualFamily.HasDepthAtMost H
  hdesc : Gw.actualFamily.IsDescending K
  htorus : IsTorusCompatible Gw.actualFamily (fun _ => ()) (ocEpsilon q Λ (M - 1))
  hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ M) ⊆ ⋃ p, (Gw.actualFamily.piece p).output
  hmeas : Gw.actualFamily.IsTimeMeasurable
  hΘ₀ : 0 ≤ Θ
  hΘ₁ : Θ ≤ 1
  henv : IsEnvelope Gw.actualFamily (Gw.mass law) K
    (ChartedFamily.Domain.onWindow Gw.actualFamily (Set.Icc tS (tS + 2 * ocTauPP α q Λ M)))
    (D.κ M) (ocEpsilon q Λ M) (ocEpsilon q Λ (M - 1)) ϱ
    (fun v u => Real.sqrt (Gw.mass law u / Gw.mass law v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm
  hpointwise : IsPointwiseMolecularEnvelope Gw.actualFamily (Gw.mass law) K
    (ChartedFamily.Domain.onWindow Gw.actualFamily (Set.Icc tS (tS + 2 * ocTauPP α q Λ M)))
    (D.κ M) (ocEpsilon q Λ M) (ocEpsilon q Λ (M - 1)) ϱ
    Cm Jm (fun v u => Real.sqrt (Gw.mass law u / Gw.mass law v) * A v u)
  htrans : Gw.actualFamily.IsTransverseOnPulses
    (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ M)
      (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ M) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ M))
    (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1)
  hquiet : Gw.actualFamily.IsFastIndependentOn
    (ocTrimmedQuietTimes α q Λ ζ M ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ M))
  hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ M))
  hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ M) (Set.Icc tS (tS + 2 * ocTauPP α q Λ M))
  hTq : T.IsQuiet (D.κ M) (ocEpsilon q Λ M) (ocEpsilon q Λ (M - 1))

/-- **The family premises at one level.** For the actual weak stage there are slots, the
matrix, the strength and an atlas of its actual-context family with the premises of
`PrepFamilyPremises` on the window at the radius `ϱ = min{c_K, c_cov} x`. -/
def PrepFamilyAtM {X : TermConstruction} (PA : PrepArgs X) (nW : ℕ+) (cK CL Cχ : ℝ)
    (kW : InvConsts) (ccov : ℝ) (Kmax Ks Ls Jm : ℕ) (Ca Cth : ℝ) (Cm : ℕ → ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∃ (K : CompIn Gw.comps → ℕ) (A : Matrix (CompIn Gw.comps) (CompIn Gw.comps) ℝ) (Θ : ℝ)
    (T : Gw.actualFamily.Atlas),
    PrepFamilyPremises X.α X.q PA.Λ X.ζ PA.dW Kmax Ks Ls Jm Ca Cth Cm M lawW Gw aM K A Θ T
      (min cK ccov * ocEpsilon X.q PA.Λ M)

/-- The core clause: the plain coupled torus solution `u` of `Gw.fam` from the datum `V(a_M)` at
the slots `K` exists on `[a_M, t_p]`, and `V(t_p) - u(t_p)` is `C x^{χ_w + σ_w L_t}‖f‖` in the
mass-weighted `L²` norm. -/
def PrepCoreClause {X : TermConstruction} (PA : PrepArgs X) (Kw Lt : ℕ) {D : OCData} {j₀ : ℕ}
    (M : ℕ) (lawW : BirthLaw) (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀)
    (aM : ℝ) (K : CompIn Gw.comps → ℕ) (hK : ∀ v, K v ≤ Kw)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)) (f : Vec 2 → ℝ)
    (Ccore : ℝ) : Prop :=
  ∃ (u : ∀ v : CompIn Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root))
    (w : ∀ v : CompIn Gw.comps, ℝ → TorusHk (K v + 1) (ScalarH v.1.root)),
    IsCoupledWeakSolutionTorus (D.κ M) aM
      (((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) + 3 / 2) * ocTauPP X.α X.q PA.Λ M)
      (streamVel (D.Φ M)) (termD0bar PA.NT PA.pT PA.DW PA.dW) K
      (edgeCoefficient Gw.fam (D.κ M) (ocEpsilon X.q PA.Λ M) (ocEpsilon X.q PA.Λ (M - 1))
        Gw.actual K)
      (fun v => truncateTorusHk (hK v) (V v aM)) (fun _ _ => 0) (fun _ _ => 0) u w ∧
    weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le Kw) (V v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM)) -
          truncateTorusHk (Nat.zero_le (K v)) (u v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM))) ≤
      Ccore * D.eps M ^ (PA.χw + PA.σw * Lt) * Real.sqrt (l2NormSq f)

/-- **The core at one level** (Step 2). For descending slots within the weak reserve, every
paired weak datum has the core clause. -/
def PrepCoreAtM {X : TermConstruction} (PA : PrepArgs X) (Kw Lt : ℕ) (nW : ℕ+)
    (cK CK CL Cχ : ℝ) (kW : InvConsts) (Ccore : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∀ (K : CompIn Gw.comps → ℕ) (hK : ∀ v, K v ≤ Kw), Gw.fam.IsDescending K →
  ∀ (f : Vec 2 → ℝ)
    (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
    (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
      (ScalarH u.1.root)),
    IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk
      Vk →
    PrepCoreClause PA Kw Lt M lawW Gw aM K hK V f Ccore

/-- **Normalization at one level** (Step 5). From the conclusion of the joint core for the actual-context family
of the weak stage (a raw
whole-family model `Tm` with the model bound at `c_R √(B h)` and the error at the radius
`ϱ ≤ c_K x` against the datum prepared at `ϱ`), a linear map
fixing constant component vectors such that every paired datum with the core clause has the
model bound `(e.term.model)` and the model error `(e.term.model.error)`. -/
def PrepNormAtM {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (CR CP cR Ccore CM : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsPrepData X PA.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW PA.φ₀ PA.hφ₀ M (M + PA.Jw) PA.Jw PA.dW PA.DW nW kW a PA.T₀ PA.σw CL Cχ PA.χw
      Gw aM →
  ∀ (K : CompIn Gw.comps → ℕ) (hK : ∀ v, K v ≤ Kw) (ϱ : ℝ), 0 < ϱ → ϱ ≤ cK * ocEpsilon X.q PA.Λ M →
    RawJointAbsConclusion X.α X.q PA.Λ PA.QT
      (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))
      (termD0bar PA.NT PA.pT PA.DW PA.dW) CR CP cR (Gw.mass lawW) K D.Φ M (D.κ M) (D.κ (M - 1)) aM
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) Gw.actualFamily (fun _ => ()) ϱ ϱ →
  ∃ Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) (ScalarH v.1.root)),
    (∀ (cv : CompIn Gw.comps → ℝ) (X' : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)),
      (∀ v, (X' v).toFunction.jet (valueIndex2 Kw) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) →
      ∀ v, (Pterm X' v).toFunction.jet (valueIndex2 (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))) =ᵐ[volume.restrict AVenhance.unitCube]
        fun _ => cv v) ∧
    ∀ (f : Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar PA.NT PA.pT PA.DW PA.dW) - 1)
        (ScalarH u.1.root)),
      IsWeakPaired PW PA.φ₀ PA.hφ₀ lawW M Kw Lt nW a PA.T₀ PA.σw PA.χw cK CK f Gw aM U₀ U V Uw Vw Uk
        Vk →
      PrepCoreClause PA Kw Lt M lawW Gw aM K hK V f Ccore →
      weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) (Pterm fun v => V v aM) ≤
          CM * Real.sqrt (l2NormSq f) ∧
        weightedNorm 1 (Gw.mass lawW) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le Kw) (V v (prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM)) -
              truncateTorusHk (Nat.zero_le (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2)))) (Pterm (fun v => V v aM) v)) ≤
          CM * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f)

/-- **Part V, the cover** (see the table). After the `g₀`, the metric reserve `q_J` and the slot
bound `K_max`: a uniform radius constant `c_cov > 0`, the constants `C_b`, `C_G` and a threshold.

For `a_M = (l₀ - 1/2) h` the window ends at `(l₀ + 3/2) h`, so `P = 2` charts. The radius
`ρs = c_cov x` is the largest, where `drift_scale` and `drift_small` bind; for `ρs` small every
radius clause is easier, and `rho_R` holds from `rho_e`, `ellT` and `κ_M ≤ κ_{M-1}`. -/
def PrepCoverPart : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ PA : PrepArgs X, Λ₀ ≤ PA.Λ → PA.Valid →
  ∀ g₀ : ℝ, 0 < g₀ → ∀ (qJ Kmax : ℕ),
  ∃ (ccov Cb : ℝ) (CG : ℕ → ℝ) (M₀ : ℕ), 0 < ccov ∧
  ∀ M : ℕ, M₀ ≤ M → PrepCoverAtM PA ccov g₀ Cb qJ Kmax CG M

/-- **The chart certificate** (see the table). After the chart reserve `J_chart`: the
padding, age and chart constants, uniform in the weak constants.

The cover has `P = 2` or `P = 3` charts. For an empty weak family the schedule fields are about
no pieces, and the flow jets remain. For `a_M` at a renewal time `l₀ h`, `t_S = l₀ h` is the
reference anchor. -/
def PrepChartPart : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ PA : PrepArgs X, Λ₀ ≤ PA.Λ → PA.Valid →
  ∀ Jchart : ℕ, ∃ (Cpad Cage : ℝ) (Npad : ℕ) (Cchart : ℕ → ℝ),
  ∀ (nW : ℕ+) (CL Cχ : ℝ) (kW : InvConsts) (j₀ : ℕ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    PrepChartAtM PA nW CL Cχ kW Cpad Cage Npad Jchart Cchart j₀ M

/-- **Part F, the family premises** (composite; see the table). The slot bound `K_max` comes first.
the envelope reserves follow, and the floor of the weak reserve covers them. The envelope
constants are chosen after the weak constants and `c_cov`, before the threshold.

For `c_K` large, `ϱ = c_cov x` and the envelopes are rescaled from `c_K x`; for `c_K ≤ c_cov`,
`ϱ = c_K x` and there is no rescaling. -/
def PrepFamilyPart : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ PA : PrepArgs X, Λ₀ ≤ PA.Λ → PA.Valid →
  ∃ Kmax : ℕ, ∀ (Ks Ls Jm : ℕ), ∃ Kneed : ℕ, Kmax ≤ Kneed ∧
  ∀ (nW : ℕ+) (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    Kneed ≤ kW.Ks → Kneed ≤ kW.Kan → Kneed ≤ kW.Lan → Kneed ≤ kW.Jm →
  ∀ ccov : ℝ, 0 < ccov →
  ∃ (Ca Cth : ℝ) (Cm : ℕ → ℝ), ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    PrepFamilyAtM PA nW cK CL Cχ kW ccov Kmax Ks Ls Jm Ca Cth Cm j₀ M

/-- **Part C, the core** (Step 2). -/
def PrepCorePart : Prop :=
  PrepPartPrefix fun _ PA _ Kw Lt nW _ _ cK CK CL Cχ kW =>
    ∃ Ccore : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepCoreAtM PA Kw Lt nW cK CK CL Cχ kW Ccore j₀ M

/-- **Part N, normalization** (Step 5). The constant is chosen after the constants of the joint core and the
core constant. For `c_R ≥ c_r` no rescaling is needed. -/
def PrepNormPart : Prop :=
  PrepPartPrefix fun _ PA Kout Kw Lt nW _ cr cK CK CL Cχ kW =>
    ∀ (CR CP cR Ccore : ℝ), 0 < cR → 0 ≤ CR → 0 ≤ CP →
    ∃ CM : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepNormAtM PA Kout Kw Lt nW cr cK CK CL Cχ kW CR CP cR Ccore CM j₀ M

/-! **The model of the capped preparation from its parts** (`prepModel_of_parts`): `PrepModelPart` from the joint
core at an abstract radius and the joint, core and normalization parts.

The joint core is instantiated at:
- the accuracy `Pacc = Q_T`, the output order `Mout = K̂`, the depth `H = d_W`, the order
  `D = D̄₀`;
- the slot bound `K_max` of the joint part, the actual-context family `Gw.actualFamily` at level
  `M` (its chart certificate is that of `Gw.fam`, which has the same pieces), and
  `r = ρold = ϱ`.

The model constant of the joint core is `CR` at `cR √(B h)`. The normalization part converts it to the radius
`ρ = c_r √(B h)`. The weak reserve floor is the maximum of the three parts' floors and covers the joint core's
reserves through the joint part. The threshold covers the starting level `mStar`. -/

/-- The accuracy `Q_T` of the terminal schedule is positive. -/
theorem prepArgs_QT_pos {X : TermConstruction} (PA : PrepArgs X) (hPA : PA.Valid) : 0 < PA.QT := by
  obtain ⟨-, h2, -⟩ := hPA.2.2.2.2.2
  have hPT : 0 < PA.PT := hPA.2.2.2.2.1
  have hq : 0 ≤ X.q ^ (PA.Jw + 1) * (1 + X.s) :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one X.hq.1.le) _) (by linarith only [X.hs₀])
  linarith only [h2, hPT, hq]

/-- The chart certificate reads only the pieces, which the actual-context family shares. -/
theorem isPreparationChartCertificate_actualFamily {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (Gw : GenStage D ScalarH Dm b j₀) {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ}
    {hφ : IsAdmissibleStream φ} {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ}
    (h : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P
      Gw.fam) :
    IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P
      Gw.actualFamily := by
  obtain ⟨hs, hf⟩ := h
  refine ⟨?_, hf⟩
  cases hs
  constructor <;> assumption

/-- **The premises of the joint core from the cover, the chart certificate and the family premises**, at
`COld = Crat = 1` and `r = ρold = ϱ`: the ratio is `1 ≤ ε_{M-1}^{-qδ}` and `ϱ ≤ √(B h)` is the
cover's `rho_R`. -/
theorem prepJointPremises_of_parts {X : TermConstruction} (PA : PrepArgs X) {D : OCData} {j₀ : ℕ}
    (M : ℕ) (hD : IsPrepData X PA.Λ M D) (hΛ : 128 ≤ PA.Λ) (hM2 : 2 ≤ M) (mStar : ℕ)
    (hmStar : mStar ≤ M) (g₀ Cb : ℝ) (Kmax Ks Ls Jm qJ Jchart : ℕ) (CG Cchart Cm : ℕ → ℝ)
    (Cpad Cage Ca Cth : ℝ) (Npad : ℕ) (lawW : BirthLaw)
    (Gw : GenStage D ScalarH (termD0bar PA.NT PA.pT PA.DW PA.dW) PA.bw j₀)
    (aM g aD B₀ lam : ℝ) (P : ℕ) (y₀ : Vec 2) (K : CompIn Gw.comps → ℕ)
    (A : Matrix (CompIn Gw.comps) (CompIn Gw.comps) ℝ) (Θ : ℝ) (T : Gw.actualFamily.Atlas)
    (ϱ : ℝ) (hϱ : 0 < ϱ)
    (hcov : IsWindowCover X.α X.q PA.Λ M X.ζ D.Φ (D.hΦ (M - 1)) (D.κ M) (D.κ (M - 1)) aM
      (aM + 2 * ocTauPP X.α X.q PA.Λ M) ϱ g g₀ aD B₀ lam Cb qJ Kmax CG
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) P y₀)
    (hchart : IsPreparationChartCertificate X.α X.q PA.Λ M (D.Φ (M - 1)) (D.hΦ (M - 1)) aM
      (aM + 2 * ocTauPP X.α X.q PA.Λ M) Cpad Cage Npad Jchart Cchart
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) P Gw.fam)
    (hF : PrepFamilyPremises X.α X.q PA.Λ X.ζ PA.dW Kmax Ks Ls Jm Ca Cth Cm M lawW Gw aM K A Θ T
      ϱ) :
    JointPremisesAbs X.α X.q PA.Λ X.ζ g₀ PA.dW (termD0bar PA.NT PA.pT PA.DW PA.dW) Kmax Ks Ls Jm
      qJ Jchart Ca Cth Cb 1 1 Cm CG Cchart Cpad Cage Npad mStar (Gw.mass lawW) K D.Φ M D.κ M
      (D.κ M) (D.κ (M - 1)) (D.hΦ (M - 1)) aM g aD B₀ lam (prepBlock (ocTauPP X.α X.q PA.Λ M) aM)
      P y₀ Gw.actualFamily (fun _ => ()) A Θ T ϱ ϱ := by
  obtain ⟨-, -, -, -, hstream, hband, -⟩ := hD
  obtain ⟨h0, h1, -⟩ := Scales.epsilon_basic (m := M - 1) X.hq.1 hΛ
  have hδ : 0 < ocDelta X.α X.q :=
    (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hq0 : 0 ≤ X.q := le_trans zero_le_one X.hq.1.le
  have hrat : ϱ / ϱ ≤ 1 * ocEpsilon X.q PA.Λ (M - 1) ^ (-(X.q * ocDelta X.α X.q)) := by
    rw [div_self hϱ.ne', one_mul]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1
      (neg_nonpos.mpr (mul_nonneg hq0 hδ.le))
  have hR : ϱ ≤ 1 * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q PA.Λ M) := by
    rw [one_mul]
    exact hcov.rho_R
  exact
    { hπ := hF.hπ, hK := hF.hK, hΦ := hstream, hband := hband, hm2 := hM2, hmStar := hmStar,
      hmM := le_rfl, hν := rfl, hB := rfl, cov := hcov, hwmeas := hF.hwmeas,
      hprep := isPreparationChartCertificate_actualFamily Gw hchart,
      hdepth := hF.hdepth, hdesc := hF.hdesc, htorus := hF.htorus, hcover := hF.hcover,
      hmeas := hF.hmeas, hΘ₀ := hF.hΘ₀, hΘ₁ := hF.hΘ₁, henv := hF.henv,
      hpointwise := hF.hpointwise, htrans := hF.htrans, hquiet := hF.hquiet,
      hTcons := hF.hTcons, hTcov := hF.hTcov, hTq := hF.hTq, hρold := hϱ, hρR := hR,
      hρrat := hrat }

/-- **The parts at one level give the model at that level.** -/
theorem prepModelAtM_of_parts {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ) (nW : ℕ+)
    (hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts) (c C₁ CM : ℝ) (j₀ M : ℕ)
    (g₀ ccov Cb : ℝ) (Kmax Ks Ls Jm qJ Jchart : ℕ) (CG Cchart Cm : ℕ → ℝ)
    (Cpad Cage Ca Cth : ℝ) (Npad : ℕ) (CR CP cR : ℝ) (mStar : ℕ) (Ccore : ℝ)
    (hΛ : 128 ≤ PA.Λ) (hM2 : 2 ≤ M) (hcK : 0 < cK) (hccov : 0 < ccov)
    (hCov : PrepCoverAtM PA ccov g₀ Cb qJ Kmax CG M)
    (hCh : PrepChartAtM PA nW CL Cχ kW Cpad Cage Npad Jchart Cchart j₀ M)
    (hFa : PrepFamilyAtM PA nW cK CL Cχ kW ccov Kmax Ks Ls Jm Ca Cth Cm j₀ M)
    (hfam : RawJointAbsFamily.{0, 0, 0, 0} X.α X.q PA.Λ X.ζ g₀ PA.QT
      (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) PA.dW
      (termD0bar PA.NT PA.pT PA.DW PA.dW) Kmax Ks Ls Jm qJ Jchart Ca Cth Cb 1 1 Cm CG Cchart Cpad
      Cage Npad CR CP cR mStar)
    (hCM : PrepCoreAtM PA Kw Lt nW cK CK CL Cχ kW Ccore j₀ M)
    (hNM : PrepNormAtM PA Kout Kw Lt nW cr cK CK CL Cχ kW CR CP cR Ccore CM j₀ M)
    (hmStar : mStar ≤ M) (hKmax : Kmax ≤ Kw) :
    PrepModelAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M := by
  intro D hD a lawW PW Gw aM hW tp w _ _ _ _ _ _ htpe
  have hε : 0 < ocEpsilon X.q PA.Λ M := (Scales.epsilon_basic X.hq.1 hΛ).1
  have hϱ : 0 < min cK ccov * ocEpsilon X.q PA.Λ M := mul_pos (lt_min hcK hccov) hε
  obtain ⟨g, aD, B₀, lam, P, y₀, hcovall⟩ := hCov D hD (D.hΦ (M - 1)) aM
  have hcov := hcovall _ hϱ (mul_le_mul_of_nonneg_right (min_le_right _ _) hε.le)
  have hchart := hCh D hD a lawW PW Gw aM hW (D.hΦ (M - 1)) P hcov.P_pos hcov.window.2.2.2
  obtain ⟨K, A, Θ, T, hF⟩ := hFa D hD a lawW PW Gw aM hW
  have hP := prepJointPremises_of_parts PA M hD hΛ hM2 mStar hmStar g₀ Cb Kmax Ks Ls Jm qJ Jchart
    CG Cchart Cm Cpad Cage Ca Cth Npad lawW Gw aM g aD B₀ lam P y₀ K A Θ T _ hϱ hcov hchart hF
  have hKw : ∀ v, K v ≤ Kw := fun v => (hF.hK v).trans hKmax
  obtain ⟨Pterm, hconst, hb⟩ := hNM D hD a lawW PW Gw aM hW K hKw _ hϱ
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hε.le)
    (hfam (Gw.mass lawW) K D.Φ M D.κ M (D.κ M) (D.κ (M - 1)) (D.hΦ (M - 1)) aM g aD B₀ lam
      (prepBlock (ocTauPP X.α X.q PA.Λ M) aM) P y₀ Gw.actualFamily (fun _ => ()) A Θ T _ _ hP)
  refine ⟨Pterm, hconst, fun f U₀ U V Uw Vw Uk Vk hpair => ?_⟩
  subst htpe
  exact hb f U₀ U V Uw Vw Uk Vk hpair
    (hCM D hD a lawW PW Gw aM hW K hKw hF.hdesc f U₀ U V Uw Vw Uk Vk hpair)

/-- The model after the weak constants, from the parts at their constants. -/
theorem prepModel_consts_of_parts {X : TermConstruction} (PA : PrepArgs X) (Kout Kw Lt : ℕ)
    (nW : ℕ+) (hk₀w : PA.k₀ ≤ Kw) (cr cK CK CL Cχ : ℝ) (kW : InvConsts)
    (g₀ ccov Cb : ℝ) (Kmax Ks Ls Jm qJ Jchart : ℕ) (CG Cchart Cm : ℕ → ℝ)
    (Cpad Cage Ca Cth : ℝ) (Npad M₀V : ℕ) (hΛ : 128 ≤ PA.Λ) (hcK : 0 < cK) (hccov : 0 < ccov)
    (hKmax : Kmax ≤ Kw)
    (hV : ∀ M : ℕ, M₀V ≤ M → PrepCoverAtM PA ccov g₀ Cb qJ Kmax CG M)
    (hH : ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepChartAtM PA nW CL Cχ kW Cpad Cage Npad Jchart Cchart j₀ M)
    (hF : ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepFamilyAtM PA nW cK CL Cχ kW ccov Kmax Ks Ls Jm Ca Cth Cm j₀ M)
    (hR : ∃ (CR CP cR : ℝ) (mStar : ℕ), 0 < cR ∧ 0 ≤ CR ∧ 0 ≤ CP ∧
      RawJointAbsFamily.{0, 0, 0, 0} X.α X.q PA.Λ X.ζ g₀ PA.QT
        (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) PA.dW
        (termD0bar PA.NT PA.pT PA.DW PA.dW) Kmax Ks Ls Jm qJ Jchart Ca Cth Cb 1 1 Cm CG Cchart
        Cpad Cage Npad CR CP cR mStar)
    (hC : ∃ Ccore : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepCoreAtM PA Kw Lt nW cK CK CL Cχ kW Ccore j₀ M)
    (hN : ∀ (CR CP cR Ccore : ℝ), 0 < cR → 0 ≤ CR → 0 ≤ CP →
      ∃ CM : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        PrepNormAtM PA Kout Kw Lt nW cr cK CK CL Cχ kW CR CP cR Ccore CM j₀ M) :
    ∀ c C₁ : ℝ, 0 < c → ∃ CM : ℝ, ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepModelAtM PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M := by
  intro c C₁ _
  obtain ⟨CR, CP, cR, mStar, hcR, hCR, hCP, hfam⟩ := hR
  obtain ⟨Ccore, hC'⟩ := hC
  obtain ⟨CM, hN'⟩ := hN CR CP cR Ccore hcR hCR hCP
  refine ⟨CM, fun j₀ => ?_⟩
  obtain ⟨MH, hHM⟩ := hH j₀
  obtain ⟨MF, hFM⟩ := hF j₀
  obtain ⟨MC, hCM⟩ := hC' j₀
  obtain ⟨MN, hNM⟩ := hN' j₀
  refine ⟨max (max 2 mStar) (max (max M₀V MH) (max MF (max MC MN))), fun M hM => ?_⟩
  have h1 := m2l hM
  have h2 := m2r hM
  exact prepModelAtM_of_parts PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C₁ CM j₀ M g₀ ccov Cb Kmax
    Ks Ls Jm qJ Jchart CG Cchart Cm Cpad Cage Ca Cth Npad CR CP cR mStar Ccore hΛ (m2l h1) hcK
    hccov (hV M (m2l (m2l h2))) (hHM M (m2r (m2l h2))) (hFM M (m2l (m2r h2))) hfam
    (hCM M (m2l (m2r (m2r h2)))) (hNM M (m2r (m2r (m2r h2)))) (m2r h1) hKmax

/-- **The model of the capped preparation from its parts** (Steps 2-5). -/
theorem prepModel_of_parts (hV : PrepCoverPart) (hH : PrepChartPart) (hF : PrepFamilyPart)
    (hR : RawJointAbsStatement.{0, 0, 0, 0}) (hC : PrepCorePart) (hN : PrepNormPart) :
    PrepModelPart := by
  intro X
  obtain ⟨ΛR, hΛR, hR1⟩ := hR X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  obtain ⟨ΛV, -, hV1⟩ := hV X
  obtain ⟨ΛH, -, hH1⟩ := hH X
  obtain ⟨ΛF, -, hF1⟩ := hF X
  obtain ⟨ΛC, -, hC1⟩ := hC X
  obtain ⟨ΛN, -, hN1⟩ := hN X
  refine ⟨max (max ΛR ΛV) (max (max ΛH ΛF) (max ΛC ΛN)), le_trans hΛR (m2l (le_max_left _ _)),
    fun PA hΛ hPA Kout => ?_⟩
  have hΛa := m2l hΛ
  have hΛb := m2r hΛ
  obtain ⟨g₀, hg₀, hR2⟩ := hR1 PA.Λ (m2l hΛa)
  obtain ⟨Kmax, hF2⟩ := hF1 PA (m2r (m2l hΛb)) hPA
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, -, -, hR3⟩ := hR2 PA.QT (prepArgs_QT_pos PA hPA)
    (max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) PA.dW
    (termD0bar PA.NT PA.pT PA.DW PA.dW) Kmax (le_max_left 2 _)
  obtain ⟨KF, hKF, hF3⟩ := hF2 Ks Ls Jm
  obtain ⟨ccov, Cb, CG, M₀V, hccov, hV2⟩ := hV1 PA (m2r hΛa) hPA g₀ hg₀ qJ Kmax
  obtain ⟨Cpad, Cage, Npad, Cchart, hH2⟩ := hH1 PA (m2l (m2l hΛb)) hPA Jchart
  obtain ⟨KC, hC2⟩ := hC1 PA (m2l (m2r hΛb)) hPA Kout
  obtain ⟨KN, hN2⟩ := hN1 PA (m2r (m2r hΛb)) hPA Kout
  have hΛ128 : 128 ≤ PA.Λ := le_trans hΛR (m2l hΛa)
  refine ⟨max KF (max KC KN), ?_⟩
  intro Kw Lt nW hk₀w cr hKw hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW hKs hKan hLan hJm hLker
  obtain ⟨Ca, Cth, Cm, hF4⟩ :=
    hF3 nW cK CL Cχ kW hcK hkW (m2l hKs) (m2l hKan) (m2l hLan) (m2l hJm) ccov hccov
  exact prepModel_consts_of_parts PA Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW g₀ ccov Cb Kmax Ks Ls Jm
    qJ Jchart CG Cchart Cm Cpad Cage Ca Cth Npad M₀V hΛ128 hcK hccov (le_trans hKF (m2l hKw)) hV2
    (hH2 nW CL Cχ kW) hF4 (hR3 Ca Cth Cb 1 1 Cm CG Cchart Cpad Cage Npad)
    (hC2 Kw Lt nW hk₀w cr (m2l (m2r hKw)) hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW
      (m2l (m2r hKs)) (m2l (m2r hKan)) (m2l (m2r hLan)) (m2l (m2r hJm)) hLker)
    (hN2 Kw Lt nW hk₀w cr (m2r (m2r hKw)) hLp hLn hcr hcr1 cK CK CL Cχ kW hcK hkW
      (m2r (m2r hKs)) (m2r (m2r hKan)) (m2r (m2r hLan)) (m2r (m2r hJm)) hLker)

/-- **The capped preparation from its split parts**: the anchor, the joint core at an abstract radius, the cover,
the chart certificate, the family premises, the core, the normalization, the interpolation and the positivity of the scales. -/
theorem preparation_of_split (hA : PrepAnchorPart) (hV : PrepCoverPart) (hH : PrepChartPart)
    (hF : PrepFamilyPart) (hR : RawJointAbsStatement.{0, 0, 0, 0}) (hC : PrepCorePart)
    (hN : PrepNormPart) (hI : PrepInterpPart) (hsf : ScaleFactsStatement) : PreparationStatement :=
  preparation_of_parts hA (prepModel_of_parts hV hH hF hR hC hN) hI hsf

end AVRegularity.EntryTerminal.Route
end
end
end
