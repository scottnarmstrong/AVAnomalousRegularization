-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.CascadeInvariants.LedgerAll
public import AVRegularity.Proofs.CascadeInvariants.Diag.LedgerCase
import AVRegularity.Proofs.GenSem.First.RepMain
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.Op.FamChart

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! Menu-independent hypotheses for the one-step ledger. The lift radius and the fresh
record length are distinct: a cascade uses the full lift radius and a shorter fresh record,
whereas the terminal menu uses its shorter radius also as its fresh record length. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
  AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Geometric, tag, reserve and stage facts of an arbitrary-menu passage. Here `cr` is the
fresh record length divided by the actual lift radius; it is the cascade's `cr` and is `1`
for a terminal menu. No hypothesis refers to cascade recursion. -/
structure MenuFacts (kI : InvConsts) (G G' : GenStage D hr Dm b j₀) (P : ProvParams)
    (Mn : SuccMenu) (Cu cr : ℝ) (nMax hMax npad : ℕ) : Prop where
  stage : StepFacts kI G G' P Cu
  alphabet : Mn.A = succAlphabet nMax hMax Mn.p npad
  degree : 2 ≤ Mn.N
  degree_cap : Mn.N ≤ nMax
  order_cap : ∀ a ∈ Mn.A, letterOrder Mn.N Mn.p a ≤ Dm
  reserveX : max nMax (2 * Mn.p) + Dm + 2 ≤ Mn.sX
  reserveZ : max nMax (2 * Mn.p) + Dm + 2 ≤ Mn.sZ
  diagonal_reserveX : max (Mn.N + 1) (2 * Mn.p) + Dm + 2 ≤ Mn.sX
  diagonal_reserveZ : max (Mn.N + 1) (2 * Mn.p) + Dm + 2 ≤ Mn.sZ
  depth : G.fam.HasDepthAtMost hMax
  weight : UEnv.liftWt Dm hMax nMax ≤ kI.Lstar
  radius_pos : 0 < Mn.lenFactor
  radius_le : Mn.lenFactor ≤ 1
  record_pos : 0 < cr
  record_le : cr ≤ 1
  tag_degree : P.N = Mn.N
  tag_covariance : P.p = Mn.p
  tag_epsilon : P.eps = D.eps
  tag_delta : P.δ = ocDelta D.α D.q
  tag_eta : P.η0 = Mn.η0
  tag_inflation : P.w (G.level - 1) = 1
  tag_length : P.Rb (G.level - 1) = cr * (Mn.lenFactor * liftLength D G.level)
  displacement : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level) ≤
    Cu * D.eps (G.level - 1) ^ (3 * ocDelta D.α D.q)
  covariance : ∀ (t : ℝ) (i j : Fin 2),
    |ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1))
        Mn.anchor t i j| ≤
      Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q *
        (Mn.lenFactor * liftLength D G.level) ^ 2
  /-- The scheduled language uses anchor-zero primitives and constants. This is the cost
  of representing the shifted primitive by their difference, including its constant term. -/
  covariance_cost : ∀ (t : ℝ) (i j : Fin 2),
    |ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) 0 t i j| +
      |ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1))
        0 Mn.anchor i j| ≤
      Cu * D.eps (G.level - 1) ^ ocDelta D.α D.q *
        (Mn.lenFactor * liftLength D G.level) ^ 2

/-- Numerical constants for the four non-diagonal sources, chosen independently of the
identity and its lift coefficients. The grade-step budget uses `kI.Hprod` directly. -/
structure MenuLedgerBudget (kI : InvConsts) (P : ProvParams) (Mn : SuccMenu)
    (Cu cr : ℝ) (nMax hMax : ℕ) (κc : MajConsts) (b : ℝ) (Dm : ℕ) where
  ar : ℝ
  Δ : ℝ
  K : ℝ
  W : ℝ
  Cold : ℝ
  Wr : ℝ
  S : ℝ≥0
  Kg : ℝ≥0
  Kd : ℝ≥0
  constants : LedgerConsts b Dm kI.Lstar κc ar Δ K W Cold Wr S Kg Kd
  order_step : (Dm : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1)
  letter_step : ((4 * nMax + 10 * Mn.p : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1)
  threshold : ledgerThr Dm hMax nMax Mn.p K W Cold Wr Δ cr Cu
    (fluxMax κc S Kg Kd Dm hMax nMax) (covKMax S Kg nMax Mn.p) ≤ P.C

/-- Constants and elementary scale bounds for the first source at the actual menu radius. -/
structure MenuDiagBudget (kI : InvConsts) (G : GenStage D hr Dm b j₀) (P : ProvParams)
    (Mn : SuccMenu) (Cu cr : ℝ) (κc : MajConsts) where
  Ca : ℝ
  Cown : ℝ
  Cd : ℝ
  Δ : ℝ
  a : ℝ
  a₀ : ℝ
  L₀ : ℕ
  s : ℝ≥0
  Wg : ℝ≥0
  Wc : ℝ≥0
  Wl : ℝ≥0
  Kg : ℝ≥0
  Kd : ℝ≥0
  S : ℝ≥0
  Wr : ℝ
  Cold : ℝ
  Cslow : ℝ
  own_small : ownSize D G.level ≤ 1 / 100
  Ca_nonneg : 0 ≤ Ca
  Cown_nonneg : 0 ≤ Cown
  amplitude_time : ocA D.α D.q D.Λ (G.level - 1) *
      (Mn.lenFactor ^ 2 * ocTauPP D.α D.q D.Λ G.level) ≤
    Ca * D.eps (G.level - 1) ^ ocDelta D.α D.q
  own : ownSize D G.level ≤ Cown * D.eps (G.level - 1) ^ ocDelta D.α D.q
  drift : D.eps G.level ^ (1 + D.α) ≤
    Cd * Real.sqrt (D.kap G.level * D.kap (G.level - 1))
  constants : DiagConsts b kI.Lstar κc Mn.N Mn.p Δ a a₀ L₀ s Wg Wc Wl Kg Kd S Wr Cold Cslow
  reserve_step : ((fsR Mn.N Mn.p (2 * Mn.N + 1) : ℕ) : ℝ) * Δ ≤ 1
  threshold : diagThr (constCtx κc S Kg Kd) Dm Mn.N Mn.p s Wg Wl Wc Cu Ca Cd Cown Wr cr ≤ P.C
end

/-! Sized covariance primitives at arbitrary anchors use the scheduled anchor-zero primitive
minus a constant. Their structural cost includes both absolute values. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {s₀ : ℝ}

/-- Sized family representation of a shifted primitive, including the constant's cost. -/
theorem famAlgQ_covMat_anchor {W : Set (ℝ × RealChain)} {X : GCtx} (hX : X.Ok)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m)
    (hκ : D.kap m = D.κ m) (hκ' : D.kap (m - 1) = D.κ (m - 1)) {C : ℝ≥0}
    (hC : ∀ t ∈ X.T, ∀ a b, |covMat D m 0 t a b| + |covMat D m 0 s₀ a b| ≤ C)
    (a b : Fin 2) :
    famAlgQ D bw j₀ 𝒮 m k W X (fun q => covMat D m s₀ q.1.1 a b) 0 C := by
  have he : ∀ t, (TimeLetter.covPrimitive m 0 a b).eval D t = covMat D m 0 t a b :=
    fun t => by simp only [covMat, TimeLetter.eval, hκ, hκ']
  refine ⟨Gen.add (Gen.time (.covPrimitive m 0 a b))
      (Gen.time (.const (-covMat D m 0 s₀ a b))),
    .add (.timeCov m a b) (.timeConst _), .add (.time _) (.time _),
    ⟨_, .add (.time _) (.time _), fun q => ?_⟩, Or.inr ⟨trivial, trivial⟩,
    fun t ht mres _ => ?_⟩
  · change covMat D m s₀ q.1.1 a b =
      (TimeLetter.covPrimitive m 0 a b).eval D q.1.1 + -covMat D m 0 s₀ a b
    rw [he]
    exact (ocCovariance_anchor D hΛ hζ m hν _ s₀ q.1.1 a b).trans (sub_eq_add_neg _ _)
  · rw [genNorm_add_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      genNorm_time_eq _ _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      genNorm_const_eq _ _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), he, abs_neg,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hC t ht a b)

/-- Sized context representation of a shifted primitive, including the constant's cost. -/
theorem ctxAlgQ_covMat_anchor {i : ℕ} {pc : ℤ} {P : ℝ → RealChain → Vec 2 → Prop}
    {X : CCtx} (hX : X.Ok) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hν : 0 < D.κ (i + 1)) (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    {C : ℝ≥0}
    (hC : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ a b,
      |covMat D (i + 1) 0 t a b| + |covMat D (i + 1) 0 s₀ a b| ≤ C) (a b : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l => covMat D (i + 1) s₀ l.1.1 a b) 0 C := by
  have he : ∀ t, (TimeLetter.covPrimitive (i + 1) 0 a b).eval D t =
      covMat D (i + 1) 0 t a b :=
    fun t => by simp only [covMat, TimeLetter.eval, hκ, Nat.add_sub_cancel, hκ']
  refine ⟨fun t _ _ => covMat D (i + 1) s₀ t a b,
    Gen.add (Gen.time (.covPrimitive (i + 1) 0 a b))
      (Gen.time (.const (-covMat D (i + 1) 0 s₀ a b))), fun _ => rfl,
    ⟨.add (.timeCov _ _ _) (.timeConst _), .add (.time _) (.time _), _,
      .add (.time _) (.time _), fun t ch z _ => ?_⟩,
    Or.inr ⟨trivial, trivial⟩, trivial, fun t ht mres L _ _ _ => ?_⟩
  · symm
    change covMat D (i + 1) s₀ t a b =
      (TimeLetter.covPrimitive (i + 1) 0 a b).eval D t + -covMat D (i + 1) 0 s₀ a b
    rw [he]
    exact (ocCovariance_anchor D hΛ hζ (i + 1) hν _ s₀ t a b).trans (sub_eq_add_neg _ _)
  · rw [genNorm_add_eq _ _ _ _ _ (hX.hshape _ id),
      genNorm_time_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _)),
      genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _)), he, abs_neg,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hC t ht a b)
end

end AVRegularity.Providers.CascadeInvariants.Menu
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal Classical
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! Exact propositions of the generic-menu ledger route. These are conditional helper
statements, not assumptions on the successor construction. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
  AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Ledger of a specified source, with its actual menu lifts and transferred flux. -/
def SourceLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) (s : SuccSource G) : Prop :=
  s.Valid Mn.A Mn.J →
  ∀ (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)),
    s.IsLiftFamily Mn Cc →
    ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
      G'.prov v' u' γ' = s.prov G.level → s.tgtComp G.level = v'.1 →
      (∀ (q : OddSlot) (c : StageCtx D b j₀ G'.level q) (d : ℕ)
        (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux q c v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level q.1
              (c.1.recenter D (D.eps (G'.level - 1) • X))
          then transferAt D G.level q.1 (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
            (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc) t
            (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
          else 0) → LedgerConcl kI κc G' v' u' γ'

/-- Direct-transport case of the generic ledger. -/
def CopyDirLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) : Prop :=
  ∀ (t₀ : List WordLetter) (v₀ u₀ : CompIn G.comps) (γ₀ : G.fam.Γ v₀ u₀),
    SourceLedgerStatement kI κc G G' P Mn (.copyDir t₀ v₀ u₀ γ₀)

/-- Quadratic-path case of the generic ledger. -/
def CopyQuadLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) : Prop :=
  ∀ (t₀ : List WordLetter) (h : ℕ) (π : StagePath G h),
    SourceLedgerStatement kI κc G G' P Mn (.copyQuad t₀ h π)

/-- Mean-letter case of the generic ledger. -/
def LetterMeanLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) : Prop :=
  ∀ (t₀ : List WordLetter) (n h : ℕ) (π : StagePath G h),
    SourceLedgerStatement kI κc G G' P Mn (.letterMean t₀ n h π)

/-- Covariance-letter case of the generic ledger. -/
def LetterCovLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) : Prop :=
  ∀ (t₀ : List WordLetter) (n h a a' : ℕ) (π : StagePath G h),
    SourceLedgerStatement kI κc G G' P Mn (.letterCov t₀ n h a a' π)

/-- Generic first-source ledger, retaining the exact menu radius and covariance anchor. -/
def DiagLedgerStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (Mn : SuccMenu) : Prop :=
  ∀ (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
    IsDiagLifts D Dm b j₀ Mn G.level Cc0 →
    ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
      G'.prov v' u' γ' = .letter G.level .diag [] →
      (∀ (q : OddSlot) (ctx : StageCtx D b j₀ G'.level q) (d : ℕ)
        (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux q ctx v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level q.1
              (ctx.1.recenter D (D.eps (G'.level - 1) • X))
          then (D.eps (G.level - 1) ^ (-Mn.η0) *
              (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) •
            fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
              Mn.N Mn.p Mn.anchor Cc0 t
              (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
          else 0) →
      0 ≤ compReserve kI v'.1 → LedgerConcl kI κc G' v' u' γ'

/-- Complete one-step ledger over an arbitrary menu and tag parameters. -/
def LedgerAllMenuStatement (kI : InvConsts) (κc : MajConsts)
    (G G' : GenStage D hr Dm b j₀) (P : ProvParams) (Mn : SuccMenu) : Prop :=
  ∀ (Cu cr : ℝ) (nMax hMax npad : ℕ), MenuFacts kI G G' P Mn Cu cr nMax hMax npad →
    MenuLedgerBudget kI P Mn Cu cr nMax hMax κc b Dm →
    MenuDiagBudget kI G P Mn Cu cr κc →
    ∀ (CH Υ : ℝ), ChainEnv D b CH Υ j₀ → j₀ ≤ G'.level →
    IsActualSuccessor D P Mn G G' →
    ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
      0 ≤ compReserve kI v'.1 → LedgerConcl kI κc G' v' u' γ'

/-- The complete ledger assembles from its five source cases, independently of menus. -/
theorem ledger_all_menu_of_cases {kI : InvConsts} {κc : MajConsts}
    {G G' : GenStage D hr Dm b j₀} {P : ProvParams} {Mn : SuccMenu}
    (hdir : CopyDirLedgerStatement kI κc G G' P Mn)
    (hquad : CopyQuadLedgerStatement kI κc G G' P Mn)
    (hmean : LetterMeanLedgerStatement kI κc G G' P Mn)
    (hcov : LetterCovLedgerStatement kI κc G G' P Mn)
    (hdiag : DiagLedgerStatement kI κc G G' Mn)
    (hSucc : IsActualSuccessor D P Mn G G')
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hres : 0 ≤ compReserve kI v'.1) : LedgerConcl kI κc G' v' u' γ' := by
  obtain ⟨-, -, -, -, -, -, e, Cc, Cc0, hLF, hDL, hfl⟩ := hSucc
  obtain ⟨hprov, -, hndf, hdf⟩ := hfl v' u' γ'
  by_cases hd : (e v' u' γ').1.IsDiag
  · exact hdiag Cc0 hDL v' u' γ'
      (hprov.trans (prov_of_isDiag _ hd G.level))
      (fun q ctx d I t X z h2 => by
        have h := hdf hd q ctx d I t X z h2
        rw [lam_of_isDiag _ hd] at h
        exact h) hres
  · have hcases : SourceLedgerStatement kI κc G G' P Mn (e v' u' γ').1 := by
      cases hs : (e v' u' γ').1 with
      | copyDir t₀ v₀ u₀ γ₀ => exact hdir t₀ v₀ u₀ γ₀
      | copyQuad t₀ h π => exact hquad t₀ h π
      | letterDiag t₀ u₀ => exact False.elim (hd (hs ▸ trivial))
      | letterMean t₀ n h π => exact hmean t₀ n h π
      | letterCov t₀ n h a a' π => exact hcov t₀ n h a a' π
    exact hcases (e v' u' γ').2.1 (Cc _) (hLF _) v' u' γ' hprov
      (e v' u' γ').2.2.2 (hndf hd)

end AVRegularity.Providers.CascadeInvariants.Menu
end
end

section
/-! The covariance-letter ledger at an arbitrary anchor, using only scheduled anchor-zero
primitives and constants. Existing cascade declarations retain their exact statements. -/

@[expose] public noncomputable section

open Set Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.Providers.GenSem.Menu
open AVRegularity.Providers.GenSem AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

namespace LiftGenSetup

/-- **The coefficients of the covariance letter are sized family functions** over the lift
window. -/
theorem covLetter_famRepQ_anchor (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {X : GCtx} (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ}
    (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (a a' : ℕ) {s₀ : ℝ} (hΛ : 1 ≤ D.Λ) (hν : 0 < D.κ m) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1))
    (hreg2 : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (2 * a + Dm + 2))
    (hρ : 0 < ρ) (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) {cH : ℝ≥0}
    (hH : ∀ t ∈ X.T, ∀ i j, |covMat D m 0 t i j| + |covMat D m 0 s₀ i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    famAlgQ D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁) X (fun q =>
      fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2)
        n a a' q.1.1 q.1.2) d I 0 c) (covLetR n a a')
      (covLetK n a a' X.S X.Kg * (cH ^ (a + a') * (Real.toNNReal (AVRegularity.Providers.GenSem.LiftGenSetup.pmC D m ρ n) *
        (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  set W := liftFamW D m 𝒜 t₀ t₁ with hWdef
  have hR := repAlgQ_famAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := m) (p := k) (W := W) hX
  have hWS : ∀ q ∈ W, q.2.WellSlotted := fun q hq => (hS.hA q.2 hq.1).1
  -- the length scale and the cost of one label derivative
  set w : ℝ≥0 := Real.toNNReal ρ with hwdef
  have hw : w ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  set σ : ℝ≥0 := X.S * w⁻¹ with hσdef
  have hσw : σ * w ≤ X.S := by
    rw [hσdef, mul_assoc, inv_mul_cancel₀ hw, mul_one]
  have hσ : X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ) ≤ σ := by
    have h1 : (w : ℝ≥0∞) * (X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ)) ≤ X.S := by
      have e : ENNReal.ofReal |ρ| = (w : ℝ≥0∞) := by
        rw [abs_of_pos hρ]
        rfl
      rw [← e]
      exact hSl
    have h2 : (σ : ℝ≥0∞) = (X.S : ℝ≥0∞) / (w : ℝ≥0∞) := by
      rw [hσdef, ENNReal.coe_mul, ENNReal.coe_inv hw, div_eq_mul_inv]
    rw [h2, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hw)) (Or.inl ENNReal.coe_ne_top),
      mul_comm]
    exact h1
  set K := 2 * a + (n + 2 * a') with hK
  set K' := max K (d - 1) with hK'
  set cE : ℝ≥0 := Real.toNNReal (AVRegularity.Providers.GenSem.LiftGenSetup.pmC D m ρ n) *
    (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0) with hcE
  -- the leaves
  have hP : ∀ κ, ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (2 * a) (fun q : W =>
      pmArr D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 κ) (n - 1) cE :=
    fun κ => hS.arrJetGQ_pmArr hX hSl hη0 hη1 hed hL₀ h0 hhH hn1 hLn hregn hσ hρ hD0 (2 * a)
      hreg2 κ
  have hHr : ∀ i j, famAlgQ D bw j₀ 𝒮 m k W X (fun q : W => covMat D m s₀ q.1.1 i j) 0
      (cH * w ^ 2) := fun i j =>
    AVRegularity.Providers.CascadeInvariants.Menu.famAlgQ_covMat_anchor hX hΛ hS.hζ hν hκ hκ' hH i j
  have hΨ : ∀ n' r' b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ n'
      (dLabelG j (fun (q : W) y => q.1.2.famMap D q.1.1 y b)) r' X.Kg := fun n' r' b j =>
    (jetRepGQ_dLabel_famMap hX hS.hζ hσ hWS n' b j).mono hR le_rfl (Nat.zero_le _) le_rfl
  have hI : ∀ n' r' b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ n'
      (dLabelG j (fun (q : W) x => q.1.2.famMapInv D q.1.1 x b)) r' (invP X.Kg n') :=
    fun n' r' b j =>
      (jetRepGQ_dLabel_famMapInv hX hS.hζ hσ hWS n' b j).mono hR le_rfl (Nat.zero_le _) le_rfl
  -- the push-forward
  have hB1 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (2 * a) (fun q : W =>
      covB1 D m ρ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n q.1.1 q.1.2 c')
      (n - 1 + n)
      (chartK (2 * a) n (invP X.Kg (2 * a)) (X.S + 2 ^ (2 * a + n) * X.Kg) *
        (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE)) := fun c' =>
    arrJetGQ_push hR hw hσw (fun q : W => contDiff_famMap q.1.2 q.1.1)
      (hΨ (2 * a + n) (n - 1)) le_rfl (fun q : W => contDiff_famMapInv q.1.2 q.1.1)
      (fun q : W => famMapInv_zero hS.hζ q.1.2 q.1.1) (hI (2 * a) (n - 1)) hP c'
  -- composition with the inner covariance operators
  have hB2 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w (0 + 2 * a) (fun q : W =>
      covB2 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n)
      (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
          (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
        (covK a' (2 * a + n) X.S * cH ^ a'))) := fun c' => by
    rw [zero_add]
    exact arrJetGQ_compArr hR hw hσw n
      (ArrJetGQ.mono hR le_rfl (hB1 c') (Nat.le_add_right _ _) le_rfl)
      (ArrJetGQ.mono hR le_rfl
        (arrJetGQ_covArrPow hR hw hσw (H := fun q : W => covMat D m s₀ q.1.1) hHr a' (2 * a + n))
        (by omega) le_rfl)
  -- composition with the outer covariance operators
  have hB4 : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w 0 (fun q : W =>
      covB4 D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n + 2 * a + 2 * a)
      (Real.toNNReal |((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a)| *
        (compK (2 * a) 0 X.S * (covK a 0 X.S * cH ^ a *
          (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
              (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
            (covK a' (2 * a + n) X.S * cH ^ a')))))) := fun c' =>
    arrJetGQ_smul hR _ (arrJetGQ_compArr hR hw hσw (2 * a)
      (ArrJetGQ.mono hR le_rfl
        (arrJetGQ_covArrPow hR hw hσw (H := fun q : W => covMat D m s₀ q.1.1) hHr a 0)
        (by omega) le_rfl)
      (ArrJetGQ.mono hR le_rfl (hB2 c') (Nat.le_add_right _ _) le_rfl))
  -- the pull-back
  have e : ∀ (q : W) (x : Vec 2) (c k : Fin 2),
      (jacMatrix (q.1.2.famMap D q.1.1) x)⁻¹ c k = ((q.1.2.recenter D x).famJac D q.1.1)⁻¹ c k :=
    fun q x c k => by rw [jacMatrix_famMap hS.hζ q.1.2 (hWS q.1 q.2) q.1.1 x]
  have hF : ∀ c', ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X) σ w 0 (fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 c')
      (n - 1 + n + 2 * a' + n + 2 * a + 2 * a + K)
      (chartK 0 K X.Kg (X.S + 2 ^ K * invP X.Kg K) *
        (X.Kg * (Real.toNNReal |((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a)| *
          (compK (2 * a) 0 X.S * (covK a 0 X.S * cH ^ a *
            (compK n (2 * a) X.S * (chartK (2 * a) n (invP X.Kg (2 * a))
                (X.S + 2 ^ (2 * a + n) * X.Kg) * (compC (invP X.Kg (2 * a)) (2 * a) * X.Kg * cE) *
              (covK a' (2 * a + n) X.S * cH ^ a')))))))) := fun c' =>
    arrJetGQ_pull hR hw hσw (fun q : W => famMap_zero q.1.2 q.1.1)
      (fun q : W => (contDiff_famMap q.1.2 q.1.1).of_le (by exact_mod_cast le_top))
      (hΨ 0 _) (fun q : W => contDiff_famMapInv q.1.2 q.1.1)
      (fun b j => by rw [Nat.zero_add]; exact hI K _ b j)
      (by rw [Nat.zero_add])
      (fun c k => (jetRepGQ_jacInv_famMap hX hS.hζ hσ hWS 0 c k).mono hR le_rfl
        (Nat.zero_le _) le_rfl)
      (fun c k q => by
        simp_rw [e]
        exact (contDiff_famJacInv hS.hζ q.1.2 (hWS q.1 q.2) q.1.1 c k).of_le
          (by exact_mod_cast le_top))
      hB4 c'
  -- the value at the label `0`
  have hval := rep_fluxCoeff_applyArrQ hR (K := K') (A := fun q : W => covFin D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2) d I
    (le_max_right _ _) c (fun m' α => (hF c m' α).1.value)
  -- the identity of the letter with its array operator
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
    (contDiff_mono (0 : Vec 2) I).of_le le_top
  have key : (fun q : W => fluxCoeff (covLetterFlux D m ρ s₀
      (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2) d I 0 c) =
      fun q : W => fluxCoeff (fun g y κ => applyArr K' (covFin D m ρ s₀
        (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) n a a' q.1.1 q.1.2 κ) g y 0)
        d I 0 c := by
    funext q
    have hreg : LiftRegular (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2) 0
        ((D.cellScaleSq m)⁻¹ * q.1.1) h n (2 * a + Dm + 2) := hreg2 q.1.2 q.2.1 _ q.2.2
    have hvec : covLetterFlux D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2)) (Cc q.1.2)
        n a a' q.1.1 q.1.2 (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
        fun c' => applyArr K' (covFin D m ρ s₀ (familyLiftData D m k q.1.2 ρ (edge q.1.2))
          (Cc q.1.2) n a a' q.1.1 q.1.2 c') (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
      refine funext fun c' => ?_
      rw [covLetterFlux_applyArr hS.hζ hS.hρ q.1.2 hreg hmono 0 c',
        applyArr_eq_of_supp (le_max_left K (d - 1)) (arrSupp_covFin _ _ _ _ _ _ _ _ _ _ _ c')]
    unfold fluxCoeff
    rw [hvec]
  rw [key]
  refine hR.mono hval (le_of_eq ?_) (le_of_eq ?_)
  · simp only [covLetR, hK]
  · simp only [covLetK, hK]
    rw [pow_add]
    ring

end LiftGenSetup

variable {b : ℝ} {R : ℕ} {s₀ : ℝ}

/-- **The covariance letters are graded slot family functions** (arbitrary anchor,
clamped diffusivities agreeing with the band chain, reserve `2a + Dm + 2 ≤ R`). -/
theorem CutoffLiftSetup.slotFamRep_covLetterP_anchor
    (hset : CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R) (hζ : IsFastProfile D.ζ)
    (hc : 0 < D.cellScaleSq m) {X : GCtx} (hX : X.Ok)
    (hSl : ENNReal.ofReal |ρ| * (X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ)) ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ U : RealChain → Set (Vec 2),
      (∀ A, IsAdmissibleChain D b j₀ m k A → U A ⊆ ladderOmega D b j₀ m k A ρ) →
      ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
        (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
          (D.slotStart m k / D.cellScaleSq m)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
          (fun l Y z => (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
            fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm h N ≤ X.L₀) {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hnR : n + Dm + 2 ≤ R) (a a' : ℕ) (ha : 2 * a + Dm + 2 ≤ R) (hκ : D.kap m = D.κ m)
    (hκ' : D.kap (m - 1) = D.κ (m - 1)) (hΛ : 1 ≤ D.Λ) (hν : 0 < D.κ m) (hρ : 0 < ρ)
    (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) {cH : ℝ≥0}
    (hH : ∀ t ∈ X.T, ∀ i j, |covMat D m 0 t i j| + |covMat D m 0 s₀ i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRepP D b j₀ 𝒮 m k X (fun t A =>
      fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k A ρ (edge A)) (Cc A) n a a' t A)
        d I 0 κ) (covLetR n a a')
      (covLetK n a a' X.S X.Kg * (cH ^ (a + a') *
        (Real.toNNReal (LiftGenSetup.pmC D m ρ n) *
          (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  have hed' : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
        (fun l Y z => (((familyLiftData D m k l.1 ρ (edge' l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u) := fun v u d α c =>
    (hed U (fun A hA => (hU A hA).2.2.1) v u d α c).congr fun l hl Y hY z =>
      (Uniqueness.list_sum_map_forall₂ ((hU l.1 hl.1).2.2.2.1.edge v u d) fun γ γ' hγ => by
        rw [hγ.1, hγ.2 α l.2 Y hY z]).symm
  obtain ⟨e, hs, hf, ⟨fc, hd, hv⟩, hsf, hn⟩ := LiftGenSetup.covLetter_famRepQ_anchor hS hX hSl hη0 hη1 hed' hL₀
    (fun A hA => (hU A hA).2.1) le_rfl hn1 hLn
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ hnR τ hτ 0) a a' hΛ hν hκ hκ'
    (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ ha τ hτ 0) hρ hD0 hH d I κ
  refine ⟨e, hs, hf, ⟨fc, hd, fun A hA t ht => ?_⟩, hsf, hn⟩
  have hq : ((t, A) : ℝ × RealChain) ∈ liftFamW D m {A | IsAdmissibleChain D b j₀ m k A}
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) := by
    refine ⟨hA, ?_, ?_⟩
    · show D.slotStart m k / D.cellScaleSq m ≤ (D.cellScaleSq m)⁻¹ * t
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.1 (inv_nonneg.mpr hc.le)
    · show (D.cellScaleSq m)⁻¹ * t ≤ _
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hc.le)
  have h1 := hv ⟨(t, A), hq⟩
  obtain ⟨hO, h0, -, hag, hCeq, -⟩ := hU A hA
  rw [← h1]
  show fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k A ρ (edge' A)) (Cc' A) n a a' t A)
    d I 0 κ =
    fluxCoeff (covLetterFlux D m ρ s₀ (familyLiftData D m k A ρ (edge A)) (Cc A) n a a' t A)
      d I 0 κ
  rw [fluxCoeff_covLetterFlux_agree D m ρ s₀ hag (Cc A) (Cc' A) n a a' t A hO h0
    ⟨(contDiff_famMapInv A t).continuous.continuousAt, famMapInv_zero hζ A t⟩
    (fun hh' _ n' m' α X hX => (hCeq hh' n' m' α _ X hX).symm) d I]


end AVRegularity.Providers.GenSem.Menu

namespace AVRegularity.Providers.CascadeInvariants.Menu
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- **The covariance letter of a path of the old stage is a graded slot family function.** -/
theorem slotFamRepP_covLetter_of_path_anchor {G : GenStage D hr Dm b j₀} (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 ≤ b)
    (hεn : ∀ k, 0 ≤ D.eps k) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse) {h : ℕ}
    (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ s₀ : ℝ)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hset : CutoffLiftSetup D b j₀ G.exports G.level k ρ (pathEdgesAt G π ⟨k, hk⟩) Cc sX sZ N R)
    (κ : MajConsts) {Δ μ₀ : ℝ} {S Kg Kd : ℝ≥0} (hXok : (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok)
    (hμ : ∀ j : Fin h, μ₀ ≤ compReserve kI (π.step j).1.1)
    (hSl : ENNReal.ofReal |ρ| * (κ.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar)
    {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ kI.Lstar) (hnR : n + Dm + 2 ≤ R)
    (a a' : ℕ) (haR : 2 * a + Dm + 2 ≤ R) (hκκ : D.kap G.level = D.κ G.level)
    (hκκ' : D.kap (G.level - 1) = D.κ (G.level - 1)) (hρ : 0 < ρ)
    (hD0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1))) {cH : ℝ≥0}
    (hH : ∀ t i j, |covMat D G.level 0 t i j| + |covMat D G.level 0 s₀ i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ' : Fin 2) :
    SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κ Δ μ₀ S Kg Kd) (fun t A =>
      fluxCoeff (covLetterFlux D G.level ρ s₀
        (familyLiftData D G.level k A ρ (pathEdgesAt G π ⟨k, hk⟩ A)) (Cc A) n a a' t A) d I 0 κ')
      (covLetR n a a')
      (covLetK n a a' S Kg * (cH ^ (a + a') *
        (Real.toNNReal (LiftGenSetup.pmC D G.level ρ n) *
          (UEnv.fluxXc (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm
            (liftB (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm) h n *
            ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have h1 := AVRegularity.Providers.GenSem.Menu.CutoffLiftSetup.slotFamRep_covLetterP_anchor hset hζ hc hXok hSl hη0 hη1
    (Θ := pathTheta hcert π)
    (fun U hU v u d α c => edgeURepP_of_certified hb hεn hcert hT π ⟨k, hk⟩ rfl rfl hε _ U _ _
      (fun A hA => hA) (fun A hA Y hY => hU A hA hY)
      (fun τ hτ => cellScaleSq_mul_mem_ocPulseWindow hc hτ) κ hXok hμ v u d α c)
    hL₀ hn1 hLn hnR a a' haR hκκ hκκ' hΛ (hκκ ▸ (EntryWeakProofs.weakData_kap_pos D hΛ hζ hκ G.level)) hρ hD0 (fun t _ i j => hH t i j) d I κ'
  rwa [pathW_pathTheta] at h1

open scoped Classical in
/-- **The ledger of a covariance letter.** -/
theorem letterCov_ledger_case_anchor (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hlev : G.level = G'.level + 1) {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ)
    (t₀ : List WordLetter) (n a a' : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.letterCov t₀ n h a a' π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N R)
    (hn : 2 ≤ n) (hR : n + Dm + 2 ≤ R) (haR : 2 * a + Dm + 2 ≤ R) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') (lam : ℝ) (Dγ : ℕ) (hDγ : Dγ ≤ Dm)
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 lam Dγ
          ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ s₀ Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    {Cw : ℝ}
    (hsize' : (G'.fam.identity v' u' γ').record.size = Cw *
      ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level)
    {μ₀ : ℝ} (hμ₀ : ∀ j : Fin h, μ₀ ≤ compReserve kI (π.step j).1.1)
    (hεn : ∀ k, 0 ≤ D.eps k) (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) (hκ : 0 < D.kap G'.level)
    (hκκ : D.kap G.level = D.κ G.level) (hκκ' : D.kap (G.level - 1) = D.κ (G.level - 1))
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hρ : 0 < ρ)
    (hDst0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level)
    (κc : MajConsts) {ar Δ K W Cold Wr Q : ℝ} {S Kg Kd cH : ℝ≥0} (ha3 : 3 * Real.pi * b < ar)
    (hΔ : 0 < Δ) (hgap : compReserve kI v'.1 + (covLetR n a a' : ℝ) * Δ ≤ μ₀)
    (hresΔ : compReserve kI v'.1 + Dm * Δ ≤ 2)
    (hXok : (oldCtx hcert κc Δ μ₀ S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar) (hLn : UEnv.liftWt Dm h n ≤ kI.Lstar)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc ar L ≤ ENNReal.ofReal K)
    (hW : wsum ar 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 ar) ≤ ENNReal.ofReal Wr)
    (hH : ∀ t i j, |covMat D G.level 0 t i j| + |covMat D G.level 0 s₀ i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (hQ0 : 0 ≤ Q)
    (hQ : ∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder → ∀ i',
      (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
        (ρ / D.eps G'.level) ^ (d - 2 + i') ≤ Q)
    (hCw : 4 ^ Dm * (Dm + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
        (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) *
      (((covLetK n a a' S Kg * cH ^ (a + a') *
        UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
          (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n : ℝ≥0) : ℝ) * (Dm : ℝ) ^ h) ≤ Cw) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  -- the finer outputs
  have hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ s₀ Cc k t A)
            d₁ I₁ 0 i₀)
          (covLetR n a a')
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
              (covLetK n a a' S Kg * cH ^ (a + a') *
                UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
                  (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n *
              ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) := by
    intro k hk d₁ _ _ I₁ i₀
    have hCov := slotFamRepP_covLetter_of_path_anchor hΛ hζ hκb hb.le hεn hcert hT π k hk ρ s₀ (Cc k)
      (hset k hk) κc hXok hμ₀ hSl hη0 hη1 hL₀ (by omega) hLn hR a a' haR hκκ hκκ' hρ hDst0 hH
      d₁ I₁ i₀
    refine (hCov.mono hXok le_rfl (le_of_eq ?_)).congr fun A hA t _ => ?_
    · rw [← mul_assoc (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁|),
        toNNReal_pathMeanPref_mul_card D G.level hcs hρ hDst0 n d₁]
      ring
    · simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte,
        pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
      rfl
  refine pathMean_ledger_case hζ hΛ hb hκb hstart G G' hcert hexpU hexp hlev ρ n Dγ lam _ γ' hflux
    hDγ hn κc (a := ar) hfine (fun d₁ _ _ => hgap)
    hε0 hε1 hτ hκ hρ hDst0 hDst ha3 hΔ hresΔ hK0 hW0 hC0 hWr0 hK hW hCold hWr hQ0 hQ ?_
  rw [hsize']
  have hcoef : 0 ≤ 4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) := by
    have : 0 ≤ tConst K Cold Δ := by linarith [one_le_tConst hK0 hC0 hΔ]
    have h3 : 0 ≤ (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2) :=
      pow_nonneg (div_nonneg hDst0 hρ.le) _
    positivity
  refine le_trans (le_of_eq ?_) ((pathSize_le hcert π zero_le_one hℓ hcoef hCw).trans_eq (by rw [one_pow, one_mul]))
  ring


end AVRegularity.Providers.CascadeInvariants.Menu
end
end

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants.Menu

/-! Sized first-source calculus at an arbitrary covariance anchor. The geometric and lift
calculus is reused; only the covariance primitive's anchor is abstracted. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
  AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow

section Strain
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0} {Wg : ℝ≥0} {s₀ : ℝ}
variable (hX : X.Ok) (hζ : IsFastProfile D.ζ)
  (hσ : X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
  (hWg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a L ≤ Wg)
include hX hζ hσ hWg

/-- **Sized jets of the commutator arrays** `𝒥_H`. -/
theorem arrJetGQ_jhArr_anchor (hΛ : 1 ≤ D.Λ)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (n : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ n (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hstr : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ n
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c))
    {cH w : ℝ≥0} (hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc P X
      (fun l => covMat D (i + 1) s₀ l.1.1 a b) 0 (cH * w ^ 2)) (c : Fin 2) :
    ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ w n
      (fun l => jhArr D (i + 1) s₀ l.1.1 l.1.2.1 l.1.2.2 c) 0
      (jhK n Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH w) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  set CS := compC (invP Wg n) n * (Real.toNNReal (ocA D.α D.q D.Λ i) * Wg) with hCS
  have hS := jetRepGQ_strainAtQ (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hX hζ hσ hWg hΛ hP hp' n hreg
  have hHj : ∀ a b, JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l (_ : Vec 2) => covMat D (i + 1) s₀ l.1.1 a b) 0 (cH * w ^ 2) :=
    fun a b => jetRepGQ_labelConst hR (hH a b) n
  have hMj : ∀ a b, JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l x => jhMat D (i + 1) s₀ l.1.1 l.1.2.1 l.1.2.2 x a b) 0
      (jhK n Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH w * w) := by
    intro a b
    have h1 := JetRepGQ.finsetSum hR (n := n) (r := 0) Finset.univ
      (F := fun j l x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a j *
        covMat D (i + 1) s₀ l.1.1 j b)
      (fun j _ l => (hstr l a j).mul contDiff_const)
      (fun j _ => JetRepGQ.mul hR (fun l => hstr l a j) (fun _ => contDiff_const) (hS a j)
        (hHj j b))
    have h2 := JetRepGQ.finsetSum hR (n := n) (r := 0) Finset.univ
      (F := fun j l x => covMat D (i + 1) s₀ l.1.1 a j *
        strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x b j)
      (fun j _ l => contDiff_const.mul (hstr l b j))
      (fun j _ => JetRepGQ.mul hR (fun _ => contDiff_const) (fun l => hstr l b j) (hHj a j)
        (hS b j))
    refine ((JetRepGQ.add hR (fun l => ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const)
      (fun l => ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j)) h1 h2).mono hR le_rfl
      le_rfl (le_of_eq ?_)).congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, jhK]
      push_cast
      ring
    · simp [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hMs : ∀ a b l, ContDiff ℝ n
      (fun x => jhMat D (i + 1) s₀ (l : CtxIdx P).1.1 l.1.2.1 l.1.2.2 x a b) := by
    intro a b l
    simp only [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const).add
      (ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j))
  have h := arrJetGQ_smul hR (-1) (arrJetGQ_matGradArr hR hMj hMs c)
  simp only [abs_neg, abs_one, Real.toNNReal_one, one_mul] at h
  exact h


end Strain

section Generic

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ w s : ℝ≥0} {D : OCData} {bw : ℝ}
  {j₀ Dm m N p : ℕ} {ρ s₀ : ℝ} {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
  {T : Finset ℤ} {cH cJ cF : ℝ≥0} {rF : ℕ}

variable (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) (π : Λ → ℝ × RealChain × Vec 2)
  (hH : ∀ a b, R (fun l => covMat D m s₀ (π l).1 a b) 0 (cH * w ^ 2))
include hR hw hσ hH

/-- **Sized arrays of `𝒞^a 𝒥_H 𝒞^{l-1-a}`.** -/
theorem arrJetGQ_eArrQ_anchor (c : Fin 2)
    (hjh : ArrJetGQ R σ w (4 * p) (fun x => jhArr D m s₀ (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    {l a : ℕ} (hl : l ≤ p) (ha : a < l) :
    ArrJetGQ R σ w (2 * p) (fun x => eArr D m s₀ (π x).1 (π x).2.1 (π x).2.2 l a c) (4 * p + 1)
      (eK p s cH cJ l a) := by
  have hin := arrJetGQ_compArr hR hw hσ (n := 2 * p + 2 * a) 1
    (hjh.mono hR (by omega) (Nat.zero_le (2 * p)) le_rfl)
    ((arrJetGQ_covArrPow hR hw hσ hH (l - 1 - a) (2 * p + 2 * a + 1)).mono hR le_rfl
      (by omega) le_rfl)
  have hout := arrJetGQ_compArr hR hw hσ (n := 2 * p) (2 * a)
    ((arrJetGQ_covArrPow hR hw hσ hH a (2 * p)).mono hR le_rfl (by omega : 0 + 2 * a ≤ 2 * p + 1)
      le_rfl) hin
  exact hout.mono hR le_rfl (by omega) le_rfl

/-- **Sized arrays `wArr`.** -/
theorem arrJetGQ_wArrQ_anchor (c : Fin 2)
    (hjh : ArrJetGQ R σ w (4 * p) (fun x => jhArr D m s₀ (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    (hdf : ArrJetGQ R σ w (2 * p)
      (fun x => dfArr D bw j₀ Dm m ρ N Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) rF cF) :
    ArrJetGQ R σ w (2 * p)
      (fun x => wArr D bw j₀ Dm m ρ N p s₀ Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) (wR N p rF)
      (wK N p s cH cJ cF) := by
  have he := ArrJetGQ.sum hR (Finset.Icc 1 p) fun l hl =>
    arrJetGQ_smul hR ((l.factorial : ℝ)⁻¹) (ArrJetGQ.sum hR (Finset.range l) fun a ha =>
      arrJetGQ_eArrQ_anchor hR hw hσ π hH c hjh (Finset.mem_Icc.mp hl).2 (Finset.mem_range.mp ha))
  have hc := arrJetGQ_compArr hR hw hσ (n := 2 * p) (N + 1)
    (hdf.mono hR le_rfl (Nat.le_add_right rF (2 * p)) le_rfl)
    ((arrJetGQ_polyArr hR hw hσ hH p wPcoef (2 * p + (N + 1))).mono hR le_rfl (by omega) le_rfl)
  exact ArrJetGQ.add hR ((ArrJetGQ.neg hR he).mono hR le_rfl (by unfold wR; omega) le_rfl)
    (hc.mono hR le_rfl (by unfold wR; omega) le_rfl)

/-- **Sized arrays `fsArr`**, from sized jets of the chart of the contexts. -/
theorem arrJetGQ_fsArrQ_anchor (hζ : IsFastProfile D.ζ) (hWs : ∀ x, (π x).2.1.WellSlotted) {Wg : ℝ≥0}
    (hΦj : ∀ b j, JetRepGQ R σ 0 (dLabelG j (fun x y => (π x).2.1.famMap D (π x).1 y b)) 0 Wg)
    (hIj : ∀ b j, JetRepGQ R σ (2 * p + (N + 1 + 2 * p))
      (dLabelG j (fun x y => (π x).2.1.famMapInv D (π x).1 y b)) 0
      (invP Wg (2 * p + (N + 1 + 2 * p))))
    (hMj : ∀ c k, JetRepGQ R σ 0
      (fun x y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) 0 Wg)
    (hjh : ∀ c, ArrJetGQ R σ w (4 * p)
      (fun x => jhArr D m s₀ (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    (hdf : ∀ c, ArrJetGQ R σ w (2 * p)
      (fun x => dfArr D bw j₀ Dm m ρ N Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) rF cF) (c : Fin 2) :
    ArrJetGQ R σ w 0 (fun x => fsArr D bw j₀ Dm m ρ N p s₀ Cc0 T (π x).1 (π x).2.1 (π x).2.2 c)
      (fsR N p rF) (fsK N p s Wg cH cJ cF) := by
  have hB : ∀ k, ArrJetGQ R σ w 0 (fun x => compArr (2 * p)
      (polyArr (covMat D m s₀ (π x).1) p wQcoef)
      (wArr D bw j₀ Dm m ρ N p s₀ Cc0 T (π x).1 (π x).2.1 (π x).2.2 k) 0) (wR N p rF + 2 * p)
      (compK (2 * p) 0 s * (polyK p wQcoef 0 s cH * wK N p s cH cJ cF)) := fun k =>
    arrJetGQ_compArr hR hw hσ (n := 0) (2 * p)
      ((arrJetGQ_polyArr hR hw hσ hH p wQcoef 0).mono hR le_rfl (by unfold wR; omega) le_rfl)
      (by rw [zero_add]; exact arrJetGQ_wArrQ_anchor hR hw hσ π hH k (hjh k) (hdf k))
  have hMs : ∀ c k x, ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞)
      (fun y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) := by
    intro c k x
    have e : (fun y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) =
        fun y => (((π x).2.1.recenter D y).famJac D (π x).1)⁻¹ c k := by
      funext y; rw [jacMatrix_famMap hζ (π x).2.1 (hWs x) (π x).1 y]
    rw [e]
    exact (contDiff_famJacInv hζ (π x).2.1 (hWs x) (π x).1 c k).of_le (by exact_mod_cast le_top)
  exact arrJetGQ_pull hR hw hσ (n := 0) (K := 2 * p + (N + 1 + 2 * p))
    (Φ := fun x => (π x).2.1.famMap D (π x).1) (Φinv := fun x => (π x).2.1.famMapInv D (π x).1)
    (fun x => famMap_zero _ _) (fun x => (contDiff_famMap _ _).of_le (by exact_mod_cast le_top))
    (fun b j => (hΦj b j).mono hR le_rfl (Nat.zero_le _) le_rfl)
    (fun x => contDiff_famMapInv _ _)
    (fun b j => by rw [zero_add]; exact (hIj b j).mono hR le_rfl (Nat.zero_le _) le_rfl) le_rfl
    (fun c k => (hMj c k).mono hR le_rfl (Nat.zero_le _) le_rfl) hMs hB c

end Generic

/-! ### The first source over the sized context calculus -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ} {s₀ : ℝ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0} {Wg : ℝ≥0} {Dm N p : ℕ} {ρ s₀ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- **The coefficients of the first source are sized context functions.** -/
theorem firstSource_ctxAlgQ_anchor (hX : X.Ok) (hζ : IsFastProfile D.ζ)
    (hσ : X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
    (hWg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a L ≤ Wg) (hΛ : 1 ≤ D.Λ) {s : ℝ≥0} (hρ : 0 < ρ)
    (hσw : σ * Real.toNNReal ρ ≤ s) (hN : 1 ≤ N) (T : Finset ℤ)
    (hT : ∀ k, k ∈ T ↔ Odd k ∧ IsScheduledIn D i k pc) {p' : ℤ} (hp' : IsScheduledIn D i p' pc)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    (hSreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
        (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
        ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2))
    {cH : ℝ≥0} (hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc P X
      (fun l => covMat D (i + 1) s₀ l.1.1 a b) 0 (cH * Real.toNNReal ρ ^ 2))
    {rF : ℕ} {cF : ℝ≥0} (hdf : ∀ c, ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ (Real.toNNReal ρ)
      (2 * p) (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 T l.1.1 l.1.2.1 l.1.2.2 c) rF cF)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l =>
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c)
      (fsR N p rF)
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        cF * Real.toNNReal ρ ^ (d - 1)) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  have hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted := fun l => (hP l).1
  -- the strain field in the label variable
  have hstr : ∀ l : CtxIdx P, ∀ a c', ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞)
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') := by
    intro l a c'
    have e : (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') =
        (fun y => contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c')
          ∘ l.1.2.1.famMapInv D l.1.1 := by
      funext x
      simp only [strainAt, Function.comp_apply, Nat.add_sub_cancel, (hP l).2.2]
    have htopV : ∀ (r : ℕ) {g : Vec 2 → Vec 2}, ContDiff ℝ (⊤ : ℕ∞) g →
        ContDiff ℝ (r : WithTop ℕ∞) g := fun r _ hg => hg.of_le (by exact_mod_cast le_top)
    rw [e]
    exact (hSreg l a c').comp (htopV (4 * p) (contDiff_famMapInv _ _))
  have hjh := fun c' => arrJetGQ_jhArr_anchor (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hX hζ hσ hWg hΛ hP hp'
    (4 * p) hSreg hstr hH c'
  have hF : ∀ c', ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ (Real.toNNReal ρ) 0
      (fun l => fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 T l.1.1 l.1.2.1 l.1.2.2 c') (fsR N p rF)
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        cF) := fun c' =>
    arrJetGQ_fsArrQ_anchor hR hw hσw (fun l : CtxIdx P => (l.1.1, l.1.2.1, l.1.2.2)) hH hζ hW
      (fun b j => jetRepGQ_ctx_dLabel_famMapQ hX hζ hσ hWg hW 0 b j)
      (fun b j => jetRepGQ_ctx_dLabel_famMapInvQ hX hζ hσ hWg hW _ b j)
      (fun c k => jetRepGQ_ctx_jacInvQ hX hζ hσ hWg hW 0 c k) hjh hdf c'
  -- the extraction
  set K' := max (2 * p + (N + 1 + 2 * p)) (d - 1) with hK'
  have hA := rep_fluxCoeff_applyArrQ hR (K := K')
    (A := fun l k => fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) d I
    (le_max_right _ _) c (fun m α => (hF c m α).1.value)
  have key : ∀ l : CtxIdx P,
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c =
      fluxCoeff (fun g y k => applyArr K'
        (fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) g y 0) d I 0 c := by
    intro l
    have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
      (contDiff_mono (0 : Vec 2) I).of_le le_top
    have hS' : ∀ k, k ∈ T ↔ Odd k ∧ IsScheduledIn D (i + 1 - 1) k l.1.2.1.slot := by
      intro k; rw [Nat.add_sub_cancel, (hP l).2.2]; exact hT k
    have hvec : firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 l.1.1 l.1.2.1 l.1.2.2
        (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
        fun k => applyArr K' (fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 T l.1.1 l.1.2.1 l.1.2.2 k)
          (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
      refine funext fun k => ?_
      rw [firstSourceFlux_applyArr hζ hρ.ne' hN l.1.1 l.1.2.1 l.1.2.2 T hS' (hstr l) (hreg l)
        hmono 0 k, applyArr_eq_of_supp (le_max_left _ (d - 1))
        (arrSupp_fsArr _ _ _ _ _ _ _ _ _ _ _ _ _ _ k)]
    unfold fluxCoeff
    rw [hvec]
  have e : (fun l : CtxIdx P =>
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c) =
      fun l => fluxCoeff (fun g y k => applyArr K'
        (fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) g y 0) d I 0 c :=
    funext key
  rw [e]
  exact hA


variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {s₀ : ℝ}

/-- **The coefficients of the first source over a slot are sized context functions.** -/
theorem slot_firstSource_ctxAlgQ_anchor {CH Υ : ℝ} (env : ChainEnv D bw CH Υ j₀)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) {ρ : ℝ} (hρ : 0 < ρ) {N p Dm sX sZ R : ℕ}
    (hN : 1 ≤ N) (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hR1 : N + 1 + Dm + 2 ≤ R)
    (hR2 : 2 * p + Dm + 2 ≤ R)
    (hDst : ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) ^ 2 =
      D.kap (i + 1 - 1) * D.cellScaleSq (i + 1))
    (hκm : D.kap (i + 1) = D.κ (i + 1)) (hκi : D.kap i = D.κ i)
    (hκle : D.kap (i + 1) ≤ D.kap i)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D bw j₀ (i + 1) k A →
      IsLiftSequence (diagQ D Dm (i + 1) k A ρ) sX sZ (liftT0 D (i + 1) k) (liftT1 D (i + 1) k)
        N 0 (Cc0 k A))
    (κc : MajConsts) {Δ a a₀ : ℝ} (hΔ : 0 < Δ) {L₀ : ℕ} (hLN : N + 1 ≤ L₀) {σ s : ℝ≥0}
    (hσc : κc.Cold / ENNReal.ofReal (D.eps i * Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
    (hσf : κc.Cslow / ENNReal.ofReal (D.eps i * Δ) ≤ σ)
    (hσw : σ * Real.toNNReal ρ ≤ s) {Wg Wc Wl Kg Kd S : ℝ≥0}
    (hWg : ∀ L, L ≤ L₀ → geoW κc a L ≤ Wg) (hWc : ∀ L, L ≤ L₀ → wsum a L κc.child ≤ Wc)
    (hWl : ∀ L, L ≤ L₀ →
      wsum a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ≤ Wl)
    (hKg : ∀ L, L ≤ L₀ → geoW κc a₀ L ≤ Kg)
    (hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ L₀ → wsum a₀ L (κc.drift k) ≤ Kd)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps i * Δ)) ≤ S)
    {cH : ℝ≥0} (hcov : ∀ t a b, |covMat D (i + 1) 0 t a b| + |covMat D (i + 1) 0 s₀ a b| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    {Cd : ℝ} {cB : ℝ≥0} (hcB : Wl * bleafK D i p Cd ≤ cB * Real.toNNReal ρ)
    (pc : OddSlot) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc.1 (slotCtx D bw j₀ i pc.1)
      (diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd))
      (fun l => fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 l.1.1 l.1.2.1 l.1.2.2)
        d I 0 c)
      (fsR N p (2 * N + 1))
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        (dfK D ((diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd)).toG S Kg Kd) Dm i ρ
          N p s cB Wc) * Real.toNNReal ρ ^ (d - 1)) := by
  set X := diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd) with hXdef
  have hX : X.Ok := diagX_ok hΔ.le
  set P := slotCtx D bw j₀ i pc.1 with hPdef
  set T := schedSlots D i pc.1 with hTdef
  have hΛ := env.hΛ1
  have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) := Construction.Stream.ocTau_pos hΛ
  have hc : 0 < D.cellScaleSq (i + 1) := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ env.hζ hκ _
  have hkap : ∀ k, 0 < D.kap k := EntryWeakProofs.weakData_kap_pos D hΛ env.hζ hκ
  have hstart := startBound_of_carrierStart env.hΛ1 env.hCH env.hΥ env.hcs
  have hNR : N + Dm + 2 ≤ R := by omega
  have B := bridgeCtx_of hΛ env.hζ hκ env.hb0 hstart 𝒮 hρ.ne' hN hRX hRZ hNR hDst Cc0 hDL pc.1
  have hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc.1 :=
    fun l => ⟨l.2.1.2.2.1, l.2.1.1, l.2.1.2.2.2.1⟩
  obtain ⟨p', hp'⟩ := exists_isScheduledIn hΛ i pc.1
  -- the strain field and the lifts
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hSreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc.1 l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c) :=
    fun l a c => (contDiff_contextStrain_recenter D env.hζ i pc.1 l.1.1 l.1.2.1 (hP l).1 l.1.2.2 a
      c).of_le (htop (4 * p))
  have hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
        (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
        ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2) :=
    fun l n _ _ k hk hA hcut => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ
      (hDL k _ ((B.hT k).1 hk).1 hA) (R := 2 * p + Dm + 2) (by omega) (by omega) 0 le_rfl n _
      (B.hgood l k hk hcut).1 0
  have hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc.1 P X (fun l => covMat D (i + 1) s₀ l.1.1 a b) 0
      (cH * Real.toNNReal ρ ^ 2) :=
    ctxAlgQ_covMat_anchor hX hΛ env.hζ (hκm ▸ hkap (i + 1)) hκm hκi fun t _ a b => hcov t a b
  -- the family calculus of the appended children
  have hX' : (X.toG S Kg Kd).Ok := hX.toG hKg hKd
  have hη0 : 0 ≤ D.kap (i + 1) / D.kap (i + 1 - 1) := (div_pos (hkap _) (hkap _)).le
  have hη1 : D.kap (i + 1) / D.kap (i + 1 - 1) ≤ 1 := by
    rw [div_le_one (hkap _)]
    exact hκle
  have hD0 : 0 ≤ ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) :=
    mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _)
  have hchild : ∀ c', ∀ n, 3 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      ArrJetGQ (famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd)) σ (Real.toNNReal ρ)
        (2 * p) (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c') (n - 1 + n)
        (childK D (X.toG S Kg Kd) Dm (i + 1) ρ n (2 * p) s) := by
    intro c' n h3 hn k hk
    have hkodd := ((B.hT k).1 hk).1
    refine arrJetGQ_diagChildQ (B.L k hk).hS hX' hSl hη0 hη1
      (by simp only [UEnv.liftWt, zero_mul, add_zero]; show N ≤ L₀; omega) (by omega)
      (by simp only [UEnv.liftWt, zero_mul, add_zero]; show n ≤ L₀; omega) (2 * p)
      (fun A hA τ hτ' => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ (hDL k A hkodd hA)
        (R := max (2 * p) n + Dm + 2) (by omega) (by omega) 0 le_rfl n τ hτ' 0)
      hσf hρ hσw hD0 ?_ c'
    rintro ⟨t, A⟩ ⟨t', ch, z, hPz, hcut, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨(B.hgood ⟨(t, ch, z), hPz⟩ k hk hcut).2, (B.hgood ⟨(t, ch, z), hPz⟩ k hk hcut).1⟩
  -- the assembled mean arrays
  have hdf : ∀ c', ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc.1 P X) σ (Real.toNNReal ρ) (2 * p)
      (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 T l.1.1 l.1.2.1 l.1.2.2 c') (2 * N + 1)
      (dfK D (X.toG S Kg Kd) Dm i ρ N p s cB Wc) := fun c' =>
    arrJetGQ_dfArrQ hX B (2 * p) (by omega) (by omega) hWl hcB c'
      (bleaf_leaf pc c' fun g r β hr => exists_leafRep hΛ env.hζ hκ env.hb0 hstart 𝒮 hρ.ne' hN
        hRX hRZ hNR hDst Cc0 hDL hκm pc.1 c' g (by omega) (by omega) β) S Kg Kd hWc _
      (hchild c')
  exact firstSource_ctxAlgQ_anchor hX env.hζ hσc hWg hΛ hρ hσw hN T B.hT hp' hP hSreg hreg hH hdf d I c

end AVRegularity.Providers.CascadeInvariants.Menu
end
end
