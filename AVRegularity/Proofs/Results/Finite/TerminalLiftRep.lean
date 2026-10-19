-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Finite.WeakPositive.NativeFacts
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Finite.TerminalLift.PositiveTransfer

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Proof of **the represented weak lifts**, the second
finite-lift estimate.

The weak lifts are the actual ones of the weak construction: the stages `IsWeakConstruction` from
the root `(0, ∅)` at level `M + J_w` down to the terminal level `M`, their lift coefficients
`IsWeakReadoutLifts`, and the composed readouts `IsWeakReadoutChain`
(`𝒲_{i-1} = 𝒲_iΛ_i𝓡_i`, `𝒲_{M+J_w}` the root value). The weak output stage `G_w` is the re-rooting
`IsWeakEncoding` of the level-`M` family (masses `π_w`), and `𝒲_w g = 𝒲_M(g ∘ ι_w)`.

For every time `t`, every classical field `g` on the components of `G_w`, and every representation
`r_T` of `g` (normalized coordinates, masses of the weak law) at the wavelength `x = ε_M` and order
`L_r + 3`, where `L_r ≥ J_wN_w` bounds the derivatives spent by the `J_w` passages (each lift
monomial has tested order `≤ N_w`), there is a representation `r_w` at the wavelength `ε_{M+J_w}`
and order `3` in the component space of the root stage (masses `weakMass`) with

* `𝓡_phys(r_w.value) = 𝒲_w g` pointwise, `𝓡_phys = compReadoutCLM π 1` the physical scalar
  readout of the root stage (evaluation of its single root component), applied once;
* `X_{ε_{M+J_w}}(r_w; 3) ≤ C_w X_x(r_T; L_r + 3)`, with `C_w` fixed after the weak menus and before
  `j₀`, `M`, the phase and the datum.

Composed with `terminal_lift_rep` this gives the second finite-lift estimate with
`C_lifts = C_wC_T`.

**Existence form**: this is the existence of a representation with the stated value and bound; the
iterated construction (per passage `X_{ε_i}(r_i; k_i) ≤ C_iX_{ε_{i-1}}(r_{i-1}; k_i + N_w)`,
`k_i = 3 + (M+J_w-i)N_w`) provides the intended witness, and the conclusion does not pin its copied
prefix or appended lists. Since the root stage has a single component, the readout identity
determines `r_w.value`. The weak lift orders `s_X, s_Z` are asserted above existential floors chosen
after the menus. -/

/-- **The represented weak lifts** (Lemma 14.13(a) of the paper). -/
theorem weak_lift_rep (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cw : ℝ, 0 ≤ Cw ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (Gw : GenStage D ScalarH Dm bw j₀) (lawW : BirthLaw) (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0
        stage →
      IsWeakEncoding Nw Jw η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => Jw * Rw) stage CcR W →
    ∀ (t : ℝ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (rT : Representation (CompSpace Gw.comps)),
      IsRepresentationAt (D.eps M) (Lr + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize s (Lr + 3) (D.eps M) rT :=
  by
    exact Finite.WeakLift.weak_lift_rep_of_positive_factory_and_chart
      (Finite.WeakLift.weak_parent_factory_of_native_coefficients
        Finite.WeakLift.weak_parent_native_coefficient_facts)
      (Finite.WeakLift.weak_positive_derivative_chart_of_pointwise_and_regularity
        Finite.WeakLift.weak_positive_pointwise_chart Finite.WeakLift.weak_positive_chart_regularity)
      α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Proof of **the represented terminal lift**, the first finite-lift estimate (proof
`Finite.TerminalLift.terminal_lift_rep_proved`).

Write `x = ε_M`, `E = ε_{M-1}`, `L_T = N_T + 2p_T` and `K_strong = L_r + L_T + 4` for a readout
order `L_r` (the composition takes `L_r = J_wN_w ≥ L_w`, the derivative count of the `J_w` weak
passages). The terminal readout `𝖱_T` is the constant readout `readoutCLM M E η₀` from the retained
terminal family `G_t` (masses of the terminal law) to the weak output stage `G_w` (masses of the weak
law); the terminal lift `𝓛_T = T_MP_{p_T}𝖱_T` is the actual glued Eulerian lift of
`IsTerminalLiftedField` (`termLiftedRep`), with the covariance anchored at `t_p`.

For every time `t ∈ [t_p, a+T₀]` and every representation `r = (F, [(G_a, λ_a)])` at the
wavelength `E` and order `K_strong` whose value represents the terminal field `Z(t)` (`IsRepOf`),
there is a representation `r_T` at the wavelength `x` and order `L_r + 3` of the lifted field
`𝓛_TZ(t)` with

* base `𝖱_TF` and the copies `(𝖱_TG_a, λ_a)` first (`Representation.map`, labels unchanged), followed
  by appended profiles of label `E` (the pure covariance terms `C_M^ℓ/ℓ! 𝖱_TG_q`, `1 ≤ ℓ ≤ p_T`) and
  of label `x` (the nonidentity lift terms `A_ν C_M^ℓ/ℓ! 𝖱_TG_q`);
* `X_x(r_T; L_r + 3) ≤ C_T X_E(r; K_strong)`, with `C_T` fixed after the menus and the
  datum-independent constants of the entry construction and before `j₀`, `M`, `κ`, the phase and
  the datum.

**Existence form**: this is the existence of a representation with the stated value, copied prefix,
labels and bound; the intended witness is given by the construction, but the existential conclusion
does not specify the appended lists term by term (they may be regrouped). The qualitative lift
orders `s_X^T, s_Z^T` are asserted above existential floors chosen after the menus. The context is
the actual construction: the weak output stage `IsWeakStage`, the capped preparation's quiet
endpoint `IsTerminalPrepMap`, the terminal law `IsTerminalLaw` and the actual terminal successor
`IsActualSuccessor`, exactly as `entry_terminal` produces them; the field `Z` itself is arbitrary
("for every sufficiently regular input representation"). -/

/-- **The represented terminal lift** (Lemma 14.12 of the paper). -/
theorem terminal_lift_rep (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw Lw : ℕ) (T₀ η₀ σw : ℝ), 1 ≤ Jw → 0 < T₀ → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ (PT QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT : ℝ),
      IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT
        LpT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) →
    ∀ Lr : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ (cr : ℝ), 0 < cr → cr ≤ 1 →
    ∀ (Kw Kp : ℕ) (nW : ℕ+) (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH →
    kW.G0 ≤ kW.Hprod + 1 →
    ∃ CT : ℝ, 0 ≤ CT ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ)
      (Gw : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (lawW : BirthLaw)
      (aM : ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ
        (weakChi α q η₀) Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk Kp (ScalarH v.1.root))),
      IsTerminalPrepMap M Kw Kp c C Gw aM tp Pterm →
    ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀),
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT NT pT sXT sZT η₀ tp cr)
        Gw Gt' →
    ∀ (Kz : ℕ) (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk Kz (ScalarH v.1.root))
      (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kz - 2 * pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
      IsTerminalLiftedField Gw (Gt'.retained M 1 RT) M pT Kz NT (Jw * Rw) sXT sZT η₀ tp (a + T₀) cr
        Z CcT PZ aRep û →
    ∀ t ∈ Set.Icc tp (a + T₀),
    ∀ r : Representation (CompSpace (Gt'.retained M 1 RT).comps),
      IsRepresentationAt (D.eps (M - 1)) (Lr + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
    ∃ rT : Representation (CompSpace Gw.comps),
      IsRepresentationAt (D.eps M) (Lr + 3) rT ∧
      rT.base = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 RT).mass lawT))).base ∧
      (∃ Lcov Llift : List ((Vec 2 → CompSpace Gw.comps) × ℝ),
        rT.profiles = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
          ((Gt'.retained M 1 RT).mass lawT))).profiles ++ Lcov ++ Llift ∧
        (∀ g ∈ Lcov, g.2 = D.eps (M - 1)) ∧ ∀ g ∈ Llift, g.2 = D.eps M) ∧
      rT.value = compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) ∧
      representedSize s (Lr + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r :=
  by exact AVRegularity.Finite.TerminalLift.terminal_lift_rep_proved α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
