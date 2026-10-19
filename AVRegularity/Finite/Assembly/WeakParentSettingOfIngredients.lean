-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Finite.StrongEntry.SeedRepresentation
import AVRegularity.Proofs.Results.Finite.TerminalSeedTransport
import AVRegularity.Proofs.Results.Finite.TraceClosure
public import AVRegularity.Finite.WeakPositive.Model
import AVRegularity.Readout.OperatorMap
public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! The terminal raw-jet route separates pure covariance from the positive-degree physical
lift response. The regularity clauses of `TerminalDifferenceBoundsGeneralStatement` and the
general dW/DW/χw telescope are unchanged. -/

/-- Identify the classical covariance polynomial and bound its positive input jets
at the parent wavelength, using the uniform normalized covariance matrix bound. -/
def TerminalCovarianceJetProperty : TerminalProfileProperty :=
  fun s E _e C k kin r _R cov _osc => ContDiff ℝ (k : ℕ) cov ∧ IsZ2Periodic cov ∧
    RawProfileJetBound E k s cov (ENNReal.ofReal C * representedSize s kin E r)

/-- The actual oscillatory difference has exactly the regularity of
`TerminalDifferenceBoundsGeneralStatement`, together with the positive-degree dimensional gain.
No realization is assumed. -/
def TerminalOscillatoryJetProperty : TerminalProfileProperty :=
  fun s E e C k kin r _R _cov osc => ContDiff ℝ (k : ℕ) osc ∧ IsZ2Periodic osc ∧
    RawProfileJetBound e k s osc (ENNReal.ofReal C * ENNReal.ofReal ((e / E) ^ (1 - s)) *
      representedSize s kin E r)

/-- A single constant bounds both fields and absorbs the positive spatial gain. -/
def TerminalRawJetCouplingStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e E s Ccov Cosc : ℝ) (K : ℕ) (X : ℝ≥0∞) (cov osc : Vec 2 → H),
    0 < e → e ≤ E → s < 1 →
    RawProfileJetBound E K s cov (ENNReal.ofReal Ccov * X) →
    RawProfileJetBound e K s osc (ENNReal.ofReal Cosc * ENNReal.ofReal ((e / E) ^ (1 - s)) * X) →
    RawProfileJetBound E K s cov (ENNReal.ofReal (max Ccov Cosc) * X) ∧
    RawProfileJetBound e K s osc (ENNReal.ofReal (max Ccov Cosc) * X)

/-- The pure covariance and positive-degree physical lift transfers with one
joint constant and the original general dW/DW selection order. -/
def TerminalSharedPhysicalTransferStatement : Prop :=
  TerminalUniformProfileStatement (fun s E e C k kin r R cov osc =>
    TerminalCovarianceJetProperty s E e C k kin r R cov osc ∧
    TerminalOscillatoryJetProperty s E e C k kin r R cov osc)

/-- Absorb the positive lift gain, preserving the exact periodic C^(Lr+3) clause of
`TerminalDifferenceBoundsGeneralStatement`. -/
theorem terminal_difference_jets_of_ingredients (hmodel : TerminalSharedPhysicalTransferStatement)
    (hmerge : TerminalRawJetCouplingStatement) : TerminalDifferenceJetBoundsGeneralStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hmodel α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hcpos hcH hkw
  obtain ⟨Cjet, hCjet, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hcpos hcH hkw
  refine ⟨Cjet, hCjet, ?_⟩
  intro j₀
  obtain ⟨M₀, hMt⟩ := hstart j₀
  refine ⟨max 1 M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  obtain ⟨hcj, hoj⟩ := hMt M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage
    tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have he : 0 < D.eps M := by
    change 0 < ocEpsilon D.q D.Λ M
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  have heE : D.eps M ≤ D.eps (M - 1) := by
    change ocEpsilon D.q D.Λ M ≤ ocEpsilon D.q D.Λ (M - 1)
    rw [hDq, hDΛ]
    have hM1 : 1 ≤ M := by omega
    simpa only [Nat.sub_add_cancel hM1] using CycleReference.epsilon_succ_le
      (n := M - 1) hq.1 (hΛ₀.trans hΛ)
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  let X := representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r
  let cov := compField (Gw.mass lawW) (aRep t) - fun x =>
    readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT) (r.value x)
  let osc := compField (Gw.mass lawW) (termLiftedRep Gw M NT dW cr CcT aRep t) -
    compField (Gw.mass lawW) (aRep t)
  change ContDiff ℝ (Lr + 3 : ℕ) cov ∧ IsZ2Periodic cov ∧
    RawProfileJetBound (D.eps (M - 1)) (Lr + 3) s cov (ENNReal.ofReal Cjet * X) at hcj
  change ContDiff ℝ (Lr + 3 : ℕ) osc ∧ IsZ2Periodic osc ∧
    RawProfileJetBound (D.eps M) (Lr + 3) s osc
      (ENNReal.ofReal Cjet * ENNReal.ofReal ((D.eps M / D.eps (M - 1)) ^ (1 - s)) * X) at hoj
  obtain ⟨hcraw, horaw⟩ := hmerge (D.eps M) (D.eps (M - 1)) s Cjet Cjet (Lr + 3)
    X cov osc he heE hs hcj.2.2 hoj.2.2
  rw [max_self] at hcraw horaw
  exact ⟨hcj.1, hcj.2.1, hoj.1, hoj.2.1, hcraw, horaw⟩

/-! Bounded terminal physical transfer: the anchored covariance polynomial and the positive
response use the same general weak depth, order and decay exponent. Numerical constants,
reserves and level floors are combined before any stage, phase or datum is supplied. -/

/-- The anchored covariance polynomial, minus its constant
readout, has uniform positive physical jets and periodic finite-order regularity. -/
def TerminalCovarianceTransferStatement : Prop :=
  TerminalUniformProfileStatement TerminalCovarianceJetProperty

/-- The actual terminal native
lift minus its zero-degree input has uniform positive jets at its terminal wavelength.
The oscillatory regularity clause of `TerminalDifferenceBoundsGeneralStatement` and all
quantifier orders are retained. -/
def TerminalPositiveLiftTransferStatement : Prop :=
  TerminalUniformProfileStatement TerminalOscillatoryJetProperty

private theorem terminal_transfer_pair_bounds {H H' : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (s E e Cc Co : ℝ) (k kin : ℕ) (r : Representation H)
    (R : H →L[ℝ] H') (cov osc : Vec 2 → H')
    (hc : TerminalCovarianceJetProperty s E e Cc k kin r R cov osc)
    (ho : TerminalOscillatoryJetProperty s E e Co k kin r R cov osc) :
    TerminalCovarianceJetProperty s E e (max Cc Co) k kin r R cov osc ∧
      TerminalOscillatoryJetProperty s E e (max Cc Co) k kin r R cov osc := by
  have hb : ENNReal.ofReal Cc * representedSize s kin E r ≤
      ENNReal.ofReal (max Cc Co) * representedSize s kin E r :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
  have hb' : ENNReal.ofReal Co * ENNReal.ofReal ((e / E) ^ (1 - s)) * representedSize s kin E r ≤
      ENNReal.ofReal (max Cc Co) * ENNReal.ofReal ((e / E) ^ (1 - s)) * representedSize s kin E r :=
    mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl) le_rfl
  exact ⟨⟨hc.1, hc.2.1, hc.2.2.1.trans hb, fun β hβ => (hc.2.2.2 β hβ).trans hb⟩,
    ⟨ho.1, ho.2.1, ho.2.2.1.trans hb', fun β hβ => (ho.2.2.2 β hβ).trans hb'⟩⟩

/-- Merge two constant menus at their common maximum, before all level and datum choices. -/
theorem terminal_uniform_profile_merge (Q R : TerminalProfileProperty)
    (hmerge : ∀ {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup H'] [NormedSpace ℝ H']
      (s E e Cc Co : ℝ) (k kin : ℕ) (r : Representation H)
      (L : H →L[ℝ] H') (cov osc : Vec 2 → H'),
      Q s E e Cc k kin r L cov osc → R s E e Co k kin r L cov osc →
      Q s E e (max Cc Co) k kin r L cov osc ∧ R s E e (max Cc Co) k kin r L cov osc)
    (hcov : TerminalUniformProfileStatement Q) (hosc : TerminalUniformProfileStatement R) :
    TerminalUniformProfileStatement (fun s E e C k kin r L cov osc =>
      Q s E e C k kin r L cov osc ∧ R s E e C k kin r L cov osc) := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let wc := hcov α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let Λc := wc.choose
  have hΛc := wc.choose_spec.1
  have hc := wc.choose_spec.2
  let wo := hosc α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let Λo := wo.choose
  have hΛo := wo.choose_spec.1
  have ho := wo.choose_spec.2
  refine ⟨max Λc Λo, hΛc.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  let wcres := hc Λ (le_max_left _ _ |>.trans hΛ) φ₀ hφ₀ hφcd hφnn
    hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ
    PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  let SXc := wcres.choose
  let SZc := wcres.choose_spec.choose
  have hcres := wcres.choose_spec.choose_spec
  let wores := ho Λ (le_max_right _ _ |>.trans hΛ) φ₀ hφ₀ hφcd hφnn
    hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ
    PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  let SXo := wores.choose
  let SZo := wores.choose_spec.choose
  have hores := wores.choose_spec.choose_spec
  refine ⟨max SXc SXo, max SZc SZo, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hcpos hcH hkw
  let wcc := hcres sXT sZT
    (le_max_left _ _ |>.trans hsXT) (le_max_left _ _ |>.trans hsZT)
    cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hcpos hcH hkw
  let Cc := wcc.choose
  have hCc := wcc.choose_spec.1
  have hcstart := wcc.choose_spec.2
  let wco := hores sXT sZT
    (le_max_right _ _ |>.trans hsXT) (le_max_right _ _ |>.trans hsZT)
    cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hcpos hcH hkw
  let Co := wco.choose
  have hostart := wco.choose_spec.2
  refine ⟨max Cc Co, hCc.trans (le_max_left _ _), ?_⟩
  intro j₀
  let wMc := hcstart j₀
  let Mc := wMc.choose
  have hcM := wMc.choose_spec
  let wMo := hostart j₀
  let Mo := wMo.choose
  have hoM := wMo.choose_spec
  refine ⟨max Mc Mo, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  exact hmerge s (D.eps (M - 1)) (D.eps M) Cc Co (Lr + 3)
    (Lr + (NT + 2 * pT) + 4) r
    (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT))
    _ _
    (hcM M (le_max_left _ _ |>.trans hM) D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM
      hstage tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv)
    (hoM M (le_max_right _ _ |>.trans hM) D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM
      hstage tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv)


/-- Combine the two physical transfers without assuming a bound for either difference. -/
theorem terminal_shared_physical_transfer_of_ingredients
    (hcov : TerminalCovarianceTransferStatement) (hosc : TerminalPositiveLiftTransferStatement) :
    TerminalSharedPhysicalTransferStatement := by
  exact terminal_uniform_profile_merge TerminalCovarianceJetProperty TerminalOscillatoryJetProperty
    terminal_transfer_pair_bounds hcov hosc

/-! The covariance part of the terminal transfer has no lift-certificate reserve dependency.
Its classical model and its finite constant-coefficient jet estimate are separated before
any analytic work. Constants are chosen before the level, the time and the represented datum.

The degenerate cases are included: degree zero gives the zero difference; zero datum and an
empty component family also give zero. Equal radii and a single component do not change the
model. The input reserve is exactly k + 2p, bounded by kin. No terminal lift or extra
realization is assumed. -/

/-- The actual classical covariance difference, with uniformly normalized matrix and readout. -/
def TerminalCovarianceModelProperty : TerminalProfileProperty :=
  fun _s E _e C k kin r R cov _osc =>
    ‖R‖ ≤ C ∧ ∃ (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ),
      k + 2 * p ≤ kin ∧ (∀ i j, A i j = A j i) ∧
      (∀ i j, |A i j| ≤ C * E ^ 2) ∧
      cov = covPolyP A p (fun x => R (r.value x)) - fun x => R (r.value x)

/-- Identify the classical representative and use the anchored covariance
and normalized readout bounds. No positive terminal lift is used by this model. -/
def TerminalCovarianceModelStatement : Prop :=
  TerminalUniformProfileStatement TerminalCovarianceModelProperty

/-- The abstract covariance estimate at a fixed input/output order and constant. -/
def TerminalCovarianceCorrectionAt (B C : ℝ) (k kin : ℕ) : Prop :=
  ∀ {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (s E e : ℝ) (r : Representation H) (R : H →L[ℝ] H') (cov osc : Vec 2 → H'),
    0 < s → s < 1 → 0 < E → IsRepresentationAt E kin r →
    TerminalCovarianceModelProperty s E e B k kin r R cov osc →
    TerminalCovarianceJetProperty s E e C k kin r R cov osc

/-- A finite constant-coefficient covariance polynomial minus its identity has
only positive input jets. Its price depends on the fixed orders and matrix bound. -/
def TerminalCovarianceCorrectionBoundsStatement : Prop :=
  ∀ (B : ℝ) (k kin : ℕ), 0 ≤ B →
    ∃ C : ℝ, 0 ≤ C ∧ TerminalCovarianceCorrectionAt B C k kin

/-- The two independent covariance ingredients close the exact physical covariance leaf. -/
theorem terminal_covariance_transfer_of_ingredients
    (hmodel : TerminalCovarianceModelStatement)
    (hjets : TerminalCovarianceCorrectionBoundsStatement) : TerminalCovarianceTransferStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let wΛ := hmodel α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let Λ₀ := wΛ.choose
  have hΛ₀ := wΛ.choose_spec.1
  have htail := wΛ.choose_spec.2
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  let wres := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  let SX := wres.choose
  let SZ := wres.choose_spec.choose
  have hreserve := wres.choose_spec.choose_spec
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  let wc := hreserve sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  let B := wc.choose
  have hB := wc.choose_spec.1
  have hstart := wc.choose_spec.2
  let wout := hjets B (Lr + 3) (Lr + (NT + 2 * pT) + 4) hB
  let Cout := wout.choose
  have hCout := wout.choose_spec.1
  have hjet : TerminalCovarianceCorrectionAt B Cout (Lr + 3)
      (Lr + (NT + 2 * pT) + 4) := wout.choose_spec.2
  refine ⟨Cout, hCout, ?_⟩
  intro j₀
  let wM := hstart j₀
  let M₀ := wM.choose
  have hMt := wM.choose_spec
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hm := hMt M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage
    tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hE : 0 < D.eps (M - 1) := by
    change 0 < ocEpsilon D.q D.Λ (M - 1)
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  exact hjet s (D.eps (M - 1)) (D.eps M) r
    (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT))
    _ _ hs₀ hs hE hr hm

end AVRegularity.Finite.TerminalLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.Assembly

/-! Assembly of the exact `oc_finite` statement from four
inputs. The seed-to-terminal representation transfer, uniform
constant selection, both represented lifts, Sobolev embedding, scalar readout
and trace closure are discharged inside the assembly. -/

/-- Data selected uniformly before the terminal index, diffusivity, phase and datum. -/
structure FiniteAssemblyReady (α s q : ℝ) (ζ : ℝ → ℝ) (Λ Jw : ℕ) (t₀ T₀ : ℝ) where
  cfg : FiniteParameters
  base : cfg.α = α ∧ cfg.s = s ∧ cfg.q = q ∧ cfg.ζ = ζ ∧ cfg.Λ = Λ ∧
    cfg.Jw = Jw ∧ cfg.t₀ = t₀ ∧ cfg.T₀ = T₀
  valid : FiniteLocalValidity cfg
  CT : ℝ
  CwLift : ℝ
  hCT : 0 ≤ CT
  hCwLift : 0 ≤ CwLift
  hc : 0 < cfg.c
  hCcas : 0 < cfg.Ccas
  hPw : cfg.Pw = 2
  hPT : cfg.PT = 2
  hτ : cfg.τ ≤ cfg.t₀
  Mstar : ℕ
  levels : ∀ M, Mstar ≤ M → cfg.m₀ + 2 ≤ M ∧ FiniteSeedBudgetLevel cfg M ∧
    (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4 ∧
    EntryLevelStatement cfg M ∧ TerminalLiftLevelStatement cfg CT M ∧ WeakLiftLevelStatement cfg CwLift M
  cascade : CascadeLevelStatement cfg
  axes : ∀ D : OCData, D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → ∀ M,
    IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ →
    ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2, IsFreshAxes D b' H₁ H₂

/-- Combining four independent eventual thresholds does not change their quantifier order. -/
theorem finite_ready_of_levels (cfg : FiniteParameters) (valid : FiniteLocalValidity cfg) (CT CwLift : ℝ)
    (hCT : 0 ≤ CT) (hCwLift : 0 ≤ CwLift) (hc : 0 < cfg.c) (hCcas : 0 < cfg.Ccas)
    (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) (hτ : cfg.τ ≤ cfg.t₀)
    (ME MT MW Mwait Mseed : ℕ)
    (hseed : ∀ M, Mseed ≤ M → FiniteSeedBudgetLevel cfg M)
    (hwait : ∀ M, Mwait ≤ M → (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (hE : ∀ M, ME ≤ M → EntryLevelStatement cfg M)
    (hT : ∀ M, MT ≤ M → TerminalLiftLevelStatement cfg CT M)
    (hW : ∀ M, MW ≤ M → WeakLiftLevelStatement cfg CwLift M)
    (hCas : CascadeLevelStatement cfg)
    (hA : ∀ D : OCData, D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
      IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → ∀ M,
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ →
      ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2, IsFreshAxes D b' H₁ H₂) :
    Nonempty (FiniteAssemblyReady cfg.α cfg.s cfg.q cfg.ζ cfg.Λ cfg.Jw cfg.t₀ cfg.T₀) := by
  refine ⟨{
    cfg := cfg, base := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    valid := valid, CT := CT, CwLift := CwLift, hCT := hCT, hCwLift := hCwLift, hc := hc, hCcas := hCcas
    hPw := hPw, hPT := hPT, hτ := hτ
    Mstar := max ME (max MT (max MW (max Mwait (max Mseed (cfg.m₀ + 2)))))
    levels := ?_, cascade := hCas, axes := hA }⟩
  intro M hM
  exact ⟨by omega, hseed M (by omega), hwait M (by omega), hE M (by omega), hT M (by omega), hW M (by omega)⟩

/-- Finish the constant selection after the compatible menus and floors are fixed. -/
private def FiniteReadyFromMenusStatement : Prop :=
    ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → ∀ (q : ℝ), IsAdmissibleQ α s q → ∀ (ζ : ℝ → ℝ),
    IsFastProfile ζ → ∀ (Λ Jw : ℕ) (t₀ T₀ : ℝ), 0 < t₀ → t₀ < T₀ → 128 ≤ Λ → 2 ≤ Λ → 0 < ocC α q → ∀ (c₀max : ℝ) (φ₀
    : Vec 2 → ℝ) (hφ₀ : Integrable φ₀ volume), let bw : ℝ := 1 / 20000; let η₀ : ℝ := ocDelta α q / 16; ∀ (Nw Rw Lw
    : ℕ), let σw : ℝ := min (ocC α q) (q - 1) / 2; ∀ (QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT τe lamE : ℝ), 0 < τe →
    let Kstrong : ℕ := Jw * Nw + (NT + 2 * pT) + 4; ∀ (SXT SZT : ℕ), (∀ sXT sZT : ℕ, SXT ≤ sXT → SZT ≤ sZT →
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
      IsRepresentationAt (D.eps (M - 1)) ((Jw * Nw) + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
    ∃ rT : Representation (CompSpace Gw.comps),
      IsRepresentationAt (D.eps M) ((Jw * Nw) + 3) rT ∧
      rT.base = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 RT).mass lawT))).base ∧
      (∃ Lcov Llift : List ((Vec 2 → CompSpace Gw.comps) × ℝ),
        rT.profiles = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
          ((Gt'.retained M 1 RT).mass lawT))).profiles ++ Lcov ++ Llift ∧
        (∀ g ∈ Lcov, g.2 = D.eps (M - 1)) ∧ ∀ g ∈ Llift, g.2 = D.eps M) ∧
      rT.value = compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) ∧
      representedSize s ((Jw * Nw) + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize s ((Jw * Nw) + (NT + 2 * pT) + 4) (D.eps (M - 1)) r) → ∀ (SXW SZW : ℕ), (∀ sX sZ : ℕ, SXW ≤ sX → SZW ≤ sZ →
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
      IsRepresentationAt (D.eps M) ((Jw * Nw) + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize s ((Jw * Nw) + 3) (D.eps M) rT) → ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ aexp σ : ℝ), IsCascadeSchedule α s
    q Kstrong 2 lamE (ocDelta α q) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) Q H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres L σ₀ aexp σ → ∀ (SXC SZC Kneed : ℕ), CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw Kstrong 2 (t₀ / 2) T₀ (termR0bar RT
    (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) τe lamE (ocDelta α q) Q H J N p nk Lc Lf Lpr Naux Nout Kres
    0 SXC SZC Kneed σ₀ → ∀ (nT : ℕ+) (SXE SZE : ℕ), (∀ sXT sZT : ℕ, SXE ≤ sXT → SZE ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta α q ∧ kS.lamC = lamE ∧
      IsSeedAllocation kS (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) H J N p (max Kres Kneed) Lpr Lc Lf ∧
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kS Lt ∧
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (Gw : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (lawW : BirthLaw)
      (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sXT, sZT, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage ∧
      IsWeakEncoding Nw Jw η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sXT sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => (Jw * Rw)) stage CcR W ∧
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀) Gw aM ∧
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) N p (H + 1)) bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) c C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT).card ∧
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M) (termMenu (M + Jw) (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT NT pT sXT sZT η₀ tp cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D Cw cr tT η₀ NT pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        seedKc (Gt'.retained M 1 RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc φ₀ hφ₀ (M + Jw) (M - 1) kS Ce τe (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) seed
        (tp + D.termH M) (a + T₀) ∧
      tp + D.termH M + 3 * ocTau α q Λ (M - 1) + 4 * ocTauPP α q Λ (M - 1) ≤ a + T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
        IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
      ∃ (tq : ℕ → ℝ)
        (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
          TorusHk (Kw + (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) - 1) (ScalarH u.1.root))
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) - 1) (ScalarH u.1.root)),
        IsWeakReduction PW φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk ∧
        tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw (weakChi α q η₀) cK CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a (t₀ / 4) T₀ s 2 cK Cread Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M Kw (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kstrong _))) cr cK C QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr tT η₀ NT pT M)
            (fun _ => isoPairedKernel (D.termRW σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀ lawW lawT rootM M (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + T₀) f Gw (Gt'.retained M 1 RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 RT) M pT (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) Kw Lw NT (Jw * Rw) sXT sZT η₀ tp a (t₀ / 4) T₀ s
            2 2 C cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z) → let sXT : ℕ := max SXE (max SXT SXW); let sZT : ℕ := max SZE (max SZT SZW); (∀ (D : OCData), D.α = α →
    D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ → ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → ∀ (b' : ℕ), 1
    ≤ b' → b' < M → ∃ (H₁ : ℝ → Vec 2 →L[ℝ] Vec 2) (H₂ : ℝ → Vec 2 →L[ℝ] Vec 2), IsFreshAxes D b' H₁ H₂) → Nonempty
    (FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀)

private theorem finite_ready_from_menus : FiniteReadyFromMenusStatement := by
  classical
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ Jw t₀ T₀ ht₀ htT hΛ128 hΛ2 hcpos c₀max φ₀ hφ₀ bw η₀ Nw Rw Lw σw QT NT pT
    RT AT k₀ LcT LoT LfT LpT tT τe lamE hτe Kstrong SXT SZT hTorders SXW SZW hWorders Q H J N p nk Lc Lf Lpr Acl Naux
    Nout Kres L σ₀ aexp σ hschedC SXC SZC Kneed hCasTail nT SXE SZE hEfloor sXT sZT hAxes
  obtain ⟨Kw, Lt, nW, hk₀w, hLw, cr, kS, hplan⟩ :=
    hEfloor sXT sZT (le_max_left _ _) (le_max_left _ _)
  obtain ⟨hLpT, hLt, hkernels, hcr, hkcr, hkc₀, hkc₀max, hcr1, hσf, hlamE, halloc, hweakConstants⟩ := hplan
  obtain ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hkWc₀, hWalloc, hterminalConstants⟩ := hweakConstants
  obtain ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, CHe, Υe, hCHe, hΥe, hEntryTail⟩ := hterminalConstants
  obtain ⟨thr, CH, Υ, hCH, hΥ, hCasInv⟩ := hCasTail Ce kS hCe hkc₀ hkc₀max
    (by rw [hkcr]; exact hcr) hcr1 hσf hlamE
    (finite_seedAllocation_mono (le_max_left _ _) halloc)
    ((le_max_right _ _).trans halloc.2.1)
    ((le_max_right _ _).trans halloc.2.2.1)
    ((le_max_right _ _).trans halloc.2.2.2.1)
    ((le_max_right _ _).trans halloc.2.2.2.2.1)
  obtain ⟨_, _, hsuccsched, _, _, hpassorders, hwidths⟩ := hschedC
  obtain ⟨_, _, _, _, _, hσ₀, hapos, haσ, hσlam, _, _, _, _, hnk, _⟩ := hsuccsched
  have hσ₀pos : 0 < σ₀ := by linarith
  obtain ⟨kI, hkI⟩ := exists_invariantAdmissible kS thr
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw))
    H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) hσ₀pos
    (by rw [hlamE]; exact hσlam) hq.1 hcpos (finite_seedAllocation_mono (le_max_left _ _) halloc) hnk
  obtain ⟨CIthr, Cwthr, hCasLedger⟩ := hCasInv kI hkI
  obtain ⟨CI, CwCas, hledger⟩ := exists_ledgerAdmissible Ce CIthr Cwthr
  obtain ⟨CwLift, hCwLift, CHw, Υw, hCHw, hΥw, hWeakTail⟩ := hWorders sXT sZT
    ((le_max_right SXT SXW).trans (le_max_right SXE _))
    ((le_max_right SZT SZW).trans (le_max_right SZE _))
  obtain ⟨j₀, hj₀⟩ := Providers.carrier_start_exists α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ128 bw (max CH (max CHe CHw)) (max Υ (max Υe Υw)) (by norm_num [bw])
  have hApos (k : ℕ) : 0 ≤ ocA α q Λ k := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)).le _
  have hTpos (k : ℕ) : 0 ≤ ocTauPP α q Λ k :=
    (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le
  have hjCas : IsCarrierStart α q Λ bw CH Υ j₀ :=
    IsCarrierStart.mono hApos hTpos (le_max_left _ _) (le_max_left _ _)
      (zero_le_one.trans hCH) hΥ.le hj₀
  have hjEntry : IsCarrierStart α q Λ bw CHe Υe j₀ :=
    IsCarrierStart.mono hApos hTpos
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
      (zero_le_one.trans hCHe) hΥe.le hj₀
  have hjWeak : IsCarrierStart α q Λ bw CHw Υw j₀ :=
    IsCarrierStart.mono hApos hTpos
      ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
      (zero_le_one.trans hCHw) hΥw.le hj₀
  obtain ⟨Ccas, CQ, Cp, m₀, hCcas, hCascadeLevel⟩ := hCasLedger CI CwCas j₀ hledger hjCas
  have hkw : kW.G0 ≤ kW.Hprod + 1 := by
    have hgap := hWalloc.2.2.2.2.2.1
    have hprod := hWalloc.2.2.2.2.2.2.1
    have hseedprod := halloc.2.2.2.2.2.2.2.2.1
    omega
  obtain ⟨CT, hCT, hTermTail⟩ := hTorders sXT sZT
    ((le_max_left SXT SXW).trans (le_max_right SXE _))
    ((le_max_left SZT SZW).trans (le_max_right SZE _)) cr hcr (by rw [← hkcr]; exact hcr1) Kw (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2)))
    nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨ME, hME⟩ := hEntryTail j₀ hjEntry
  obtain ⟨MT, hMT⟩ := hTermTail j₀
  obtain ⟨MW, hMW⟩ := hWeakTail j₀ hjWeak
  obtain ⟨Mwait, hMwait⟩ := exists_entry_wait hα₀ hα₁ hq hΛ2 C Jw (t₀ / 4) (by positivity)
  let cfg : FiniteParameters := {
    α := α, s := s, q := q, ζ := ζ, Λ := Λ, φ₀ := φ₀, hφ₀ := hφ₀, bw := bw
    Jw := Jw, Nw := Nw, Rw := Rw, Lw := Lw, τ := t₀ / 4, T₀ := T₀, Pw := 2, η₀ := η₀
    σw := σw, PT := 2, QT := QT, NT := NT, pT := pT, RT := RT, AT := AT, k₀ := k₀
    LcT := LcT, LoT := LoT, LfT := LfT, LpT := LpT, tT := tT, τe := τe, lamE := lamE
    σ₀ := σ₀, H := H, J := J, N := N, p := p, Kres := Kres, Lpr := Lpr, Lc := Lc, Lf := Lf
    nT := nT, Kout := Kstrong, sXT := sXT, sZT := sZT, Kw := Kw, Lt := Lt, nW := nW
    hk₀w := hk₀w, hLw := hLw, cr := cr, kS := kS, cK := cK, CK := CK, CL := CL, Cχ := Cχ
    Cread := Cread, Cid := Cid, kW := kW, c := c, C := C, Centry := Centry, cH := cH, Ce := Ce
    Cw := Cw, j₀ := j₀, Q := Q, t₀ := t₀, nk := nk, L := L, Naux := Naux, Nout := Nout
    sX := SXC, sZ := SZC, m₀ := m₀, CI := CI, CwCas := CwCas, Ccas := Ccas, CQ := CQ, Cp := Cp, kI := kI }
  have hvalid : FiniteLocalValidity cfg := {
    hα₀ := hα₀, hα₁ := hα₁, hs₁ := hs₁, hq := hq, hζ := hζ
    hcr := by change 0 < kI.cr; rw [hkI.2.1, hkcr]; exact hcr
    hσ₀ := hσ₀pos, hnk := by change 1 ≤ nk; omega
    horder := rfl, hτ := rfl
    hbw := by norm_num [cfg, bw]
    hc₀ := hkc₀, hτe := hτe
    hHprod := halloc.2.2.2.2.2.2.2.2.1 }
  obtain ⟨Mseed, hMseed⟩ := exists_finite_seed_budget_level cfg hvalid hΛ128
  apply finite_ready_of_levels cfg hvalid CT CwLift hCT hCwLift hc hCcas rfl rfl
    (by change t₀ / 4 ≤ t₀; linarith) ME MT MW Mwait Mseed hMseed
  · exact hMwait
  · dsimp only [EntryLevelStatement, cfg]
    with_reducible exact hME
  · dsimp only [TerminalLiftLevelStatement, cfg]
    with_reducible exact hMT
  · dsimp only [WeakLiftLevelStatement, cfg]
    with_reducible exact hMW
  · dsimp only [CascadeLevelStatement, cfg]
    with_reducible exact hCascadeLevel
  · exact hAxes

/-- The full outer constant and threshold selection from the four estimates. -/
theorem finite_parameters_of_registered_inputs
    (hentry : EntryTerminalStatement) (hcascade : IterationCascadeStatement)
    (hterminal : TerminalLiftRepStatement) (hweak : WeakLiftRepStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw →
    ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ → Nonempty (FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀) := by
  classical
  obtain ⟨ΛE, hΛE, hE⟩ := hentry α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛC, hΛC, hCas⟩ := hcascade α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛT, hΛT, hT⟩ := hterminal α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛW, hΛW, hW⟩ := hweak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛA, hΛA, hA⟩ := Providers.fresh_axes_exist α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max ΛE (max ΛC (max ΛT (max ΛW ΛA))), by omega, ?_⟩
  intro Λ hΛ Jw hJw t₀ T₀ ht₀ htT
  have hΛ128 : 128 ≤ Λ := by omega
  have hΛ2 : 2 ≤ Λ := by omega
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  have hcpos := ocC_pos_of_admissible hα₀ hq
  have hηsucc := succEta0_pos_of_admissible hα₀ hs₀ hq
  have hs1 : s < 1 := by linarith
  obtain ⟨c₀max, hc₀max, hCas0⟩ := hCas Λ (by omega)
  obtain ⟨φ₀, hφ₀, hφsmooth, hφpos, hφmass, hφsupp⟩ := exists_mollifier
  let bw : ℝ := 1 / 20000
  have hbw : 0 < bw := by norm_num [bw]
  have hbw1 : bw ≤ 1 / 10000 := by norm_num [bw]
  let η₀ : ℝ := ocDelta α q / 16
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hηδ : η₀ ≤ ocDelta α q / 8 := by dsimp [η₀]; linarith
  obtain ⟨Nw, Rw, Lw, hNw, hLwNw, hEorders⟩ :=
    hE Λ (by omega) c₀max hc₀max φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp bw hbw hbw1
      Jw (t₀ / 4) T₀ 2 η₀ hJw (by positivity) (by linarith) (by norm_num) hη₀ hηδ
  let σw : ℝ := min (ocC α q) (q - 1) / 2
  have hσw : 0 < σw := by dsimp [σw]; exact div_pos (lt_min hcpos (by linarith [hq.1])) (by norm_num)
  have hσw1 : σw < min (ocC α q) (q - 1) := by dsimp [σw] at *; linarith
  obtain ⟨QT, NT, pT, RT, AT, k₀, LcT, LoT, LfT, LpT, tT, hschedT, hk₀,
    τe, lamE, hexp⟩ := Providers.finite_order_choice α s hα₀ hα₁ hs₀ hs₁ q hq
    Jw Nw Rw Lw η₀ 2 hJw hη₀ hηδ (by norm_num) σw hσw hσw1
  let Kstrong := Jw * Nw + (NT + 2 * pT) + 4
  have hKstrong : 3 ≤ Kstrong := by dsimp [Kstrong]; omega
  obtain ⟨SXT, SZT, hTorders⟩ := hT Λ (by omega) φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp
    bw hbw hbw1 Jw Nw Rw Lw T₀ η₀ σw hJw (by linarith) hη₀ hηδ hσw hσw1
    2 QT NT pT RT AT k₀ LcT LoT LfT LpT tT hschedT (Jw * Nw)
  obtain ⟨SXW, SZW, hWorders⟩ := hW Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw
    hJw hNw hη₀ hηδ hσw hσw1 (Jw * Nw) le_rfl
  obtain ⟨Q, H, J, N, p, nk, Lc, Lf, Lpr, Acl, Naux, Nout, Kres, L, σ₀, aexp, σ,
    hschedC, hCasorders⟩ := hCas0 φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp bw hbw hbw1
    Kstrong 2 (t₀ / 2) T₀ hKstrong (by norm_num) (by positivity) (by linarith)
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw))
    τe lamE (ocDelta α q) hexp.1 (by linarith [hexp.2.2.2.1]) hδ
  obtain ⟨SXC, SZC, Kneed, hCasfloors⟩ := hCasorders 0
  have hCasTail := hCasfloors SXC SZC le_rfl le_rfl
  obtain ⟨nT, hnT⟩ := exists_freshKernelOrder LcT Lpr Lc Lf
  obtain ⟨SXE, SZE, hEfloor⟩ := hEorders σw hσw hσw1 2 (by norm_num)
    NT pT RT AT k₀ LcT LoT LfT LpT tT QT hschedT τe lamE hexp σ₀ H J N p (max Kres Kneed) Lpr Lc Lf nT hnT Kstrong
  let sXT := max SXE (max SXT SXW)
  let sZT := max SZE (max SZT SZW)
  have hAxes := hA Λ (by omega)
  refine finite_ready_from_menus α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ Jw t₀ T₀ ht₀ htT hΛ128 hΛ2 hcpos c₀max φ₀ hφ₀ Nw
    Rw Lw QT NT pT RT AT k₀ LcT LoT LfT LpT tT τe lamE hexp.1 SXT SZT ?_ SXW SZW ?_ Q H J N p nk Lc Lf Lpr
    Acl Naux Nout Kres L σ₀ aexp σ hschedC SXC SZC Kneed hCasTail nT SXE SZE ?_ hAxes
  · with_reducible exact hTorders
  · with_reducible exact hWorders
  · with_reducible exact hEfloor



/-- Applying the numerical package: one local glue ingredient, then readout and trace closure. -/
theorem oc_finite_of_ready
    (htransport : TerminalSeedTransportStatement) (hdatum : FiniteDatumCompositionStatement)
    (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (hs₀ : 0 < s) (hs1 : s < 1)
    (hΛ128 : 128 ≤ Λ) (hηsucc : 0 < succEta0 α q s)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (Jw : ℕ) (t₀ T₀ : ℝ) (ht₀ : 0 < t₀) (htT : t₀ < T₀)
    (ready : FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀) :
    ∃ (Mstar : ℕ) (C : ℝ), ∀ M : ℕ, Mstar ≤ M →
    ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
        (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
    ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + Jw))) κ a (a + T₀) f θ →
    ∀ t ∈ Set.Icc (a + t₀) (a + T₀), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f)) := by
  classical
  rcases ready with ⟨cfg, hbase, hvalid, CT, CwLift, hCT, hCwLift, hc, hCcas, hPw, hPT, hτ, Mstar, hlevels, hCascadeLevel, hA⟩
  rcases hbase with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨Mstar, 3 * (CwLift * CT) * cfg.Ccas * |cfg.Centry| + 2 * |cfg.C|, ?_⟩
  intro M hM κ hκ a f hf θ hθ
  obtain ⟨hMm, hbudget, hwait, hME, hMT, hMW⟩ := hlevels M hM
  obtain ⟨D, hDα, hDq, hDΛ, hDζ, hDΦ, hband, hκM, hDterm⟩ :=
    exists_ocData cfg.α cfg.q cfg.Λ cfg.ζ Φ hΦ M κ hκ
  have hΦD : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ := by rw [hDΦ]; exact hΦ
  have hθD : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ := by
    rw [hDΦ, hκM]
    exact hθ
  have hae := hdatum cfg hvalid htransport hs₀ hs1 hΛ128 hηsucc ht₀ htT hτ hc hCcas hPw hPT
    M hMm hbudget hwait hME
    CT CwLift hCT hCwLift hMT hMW hCascadeLevel
    D hDα hDq hDΛ hDζ hΦD hband hDterm (hA D hDα hDq hDΛ hDζ hΦD M hband) a f hf θ hθD
  have hae' : ∀ᵐ t ∂(volume.restrict (Set.Icc (a + cfg.t₀) (a + cfg.T₀))),
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe cfg.s Θt ((3 * (CwLift * CT) * cfg.Ccas * |cfg.Centry| + 2 * |cfg.C|) * Real.sqrt (l2NormSq f)) := by
    filter_upwards [hae] with t ht
    obtain ⟨S, hS, r, hr, hsize, Θ, hΘp, hΘae, herr⟩ := ht
    let R := compReadoutCLM (fun v : CompIn S => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1)
    have hmodel := scalar_rep_readout cfg.s hs₀ hs1 (D.eps (M + cfg.Jw))
      ((CwLift * CT) * cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f)) (by positivity)
      r hr R (weak_root_readout_norm D cfg.Nw cfg.Jw cfg.η₀ S hS) hsize
    have hsum := csNormLe_add hmodel herr
    have hfun : (fun x => R (r.value x) + (Θ x - R (r.value x))) = Θ := by
      funext x
      ring
    change CsNormLe cfg.s (fun x => R (r.value x) + (Θ x - R (r.value x))) _ at hsum
    rw [hfun] at hsum
    have hbudget : 3 * ((CwLift * CT) * cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f)) +
        2 * |cfg.C| * Real.sqrt (l2NormSq f) =
        (3 * (CwLift * CT) * cfg.Ccas * |cfg.Centry| + 2 * |cfg.C|) * Real.sqrt (l2NormSq f) := by ring
    change CsNormLe cfg.s Θ (3 * ((CwLift * CT) * cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f)) +
      2 * |cfg.C| * Real.sqrt (l2NormSq f)) at hsum
    rw [hbudget] at hsum
    exact ⟨Θ, hΘp, hΘae, hsum⟩
  exact Providers.csNorm_trace_closure cfg.s hs₀ hs1 (streamVel (Φ (M + cfg.Jw))) κ a (a + cfg.T₀) f θ hθ
    (a + cfg.t₀) (a + cfg.T₀) _ (by linarith) (by linarith) le_rfl hae'


/-- Exact `oc_finite`, given four estimates. The seed-transport statement and the
seed-to-terminal representation glue are discharged by the proof of `finite_strong_entry`. -/
theorem oc_finite_of_ingredients
    (hentry : EntryTerminalStatement) (hcascade : IterationCascadeStatement)
    (hterminal : TerminalLiftRepStatement) (hweak : WeakLiftRepStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
    ∀ J : ℕ, 1 ≤ J → ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T →
    ∃ (Mstar : ℕ) (C : ℝ), ∀ M : ℕ, Mstar ≤ M →
    ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
        (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
    ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + J))) κ a (a + T) f θ →
    ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f))  := by
  obtain ⟨Λ₀, hΛ₀, hready⟩ := finite_parameters_of_registered_inputs hentry hcascade hterminal hweak
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Φ hΦ Jw hJw t₀ T₀ ht₀ htT
  obtain ⟨ready⟩ := hready Λ hΛ Jw hJw t₀ T₀ ht₀ htT
  exact oc_finite_of_ready Providers.terminal_seed_transport (finite_datum_composition_of_strong_entry finite_strong_entry) α s q ζ Λ hs₀ (by linarith)
    (hΛ₀.trans hΛ) (succEta0_pos_of_admissible hα₀ hs₀ hq) Φ hΦ Jw t₀ T₀ ht₀ htT ready

end AVRegularity.Finite.Assembly
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory AVenhance
open scoped ENNReal Classical
namespace AVRegularity.Finite.WeakLift

/-! Bounded weak positive-response sub-assembly. The factory selects its entire numeric
request before data. Grading, tested-order identification, physical chart transfer and
weighted path sums are separate statements with fixed mathematical interfaces. -/

open Construction.Preservation.FullLift CycleComparison.Lift

/-- The actual weak construction supplies capped parent-radius settings
and the geometry/source certificates consumed by the shared terminal lift producer.
The effective cap may exceed a small ambient cap; its native polynomial source is preserved. -/
def WeakPlateauParentSettingStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ P : WeakPositiveParameters Nw (Jw * Rw) (Lr + 3),
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu)
        M Jw (D.termRW σw M) 0 stage →
    ∀ i, M < i → i ≤ M + Jw →
      WeakPositiveGeometry P i (stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
        (fun v => weakMass D Nw Jw η₀ v.1) slot)

/-- The scalar-power recurrence supplies the actual mixed
coefficient jets with their fixed path matrices, at every tested n <= N and height <= H. -/
def WeakGradedRecurrenceStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U),
  ∀ (D : OCData) (Dm j₀ : ℕ) (bw : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (π : CompIn G.comps → ℝ) (slot : OddSlot) (ρ : ℝ) (A : WeakPositiveSlot P i G π slot ρ),
    WeakPositiveGraded A

/-- Source, metric and drift identification transfers the arbitrary
native sequence to the slot-lift recurrence; uniqueness identifies its tested coefficients,
and a positive degree has zero coefficient at input order zero. -/
def WeakPositiveSupportIdentificationStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U),
  ∀ (D : OCData) (Dm j₀ : ℕ) (bw : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (π : CompIn G.comps → ℝ) (slot : OddSlot) (ρ : ℝ) (A : WeakPositiveSlot P i G π slot ρ)
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
    IsLiftSequence (weakPositiveNativeData i G slot ρ) sX sZ
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc →
    WeakPositiveIdentified A Cc

/-- Sum the height matrices, by Schur powers, with
one row-and-column budget independent of the number of components and the chosen slot. -/
def WeakWeightedPathSumsStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U),
  ∀ (D : OCData) (Dm j₀ : ℕ) (bw : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (π : CompIn G.comps → ℝ) (slot : OddSlot) (ρ : ℝ) (A : WeakPositiveSlot P i G π slot ρ),
    HasRealSchurBudget (massConjugatedMatrix π (fun v u =>
      ∑ hh ∈ Finset.range (H + 1), weakPositiveMatrix A hh v u)) (weakPositivePathCost P)

/-- Positive input jets through the actual forward and
inverse native charts, with the gain (e/E)^(1-s). The matrix budget is supplied explicitly;
this statement does not assume the final weak estimate, nor any bound on input amplitude. -/
def WeakPositiveDerivativeChartStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U) (s : ℝ), 0 < s → s < 1 →
  ∃ Ct : ℝ, 0 ≤ Ct ∧
  ∀ (D : OCData) (Dm j₀ : ℕ) (bw : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (π : CompIn G.comps → ℝ), (∀ v, 0 < π v) → WeakPositiveGeometry P i G →
  ∀ (A : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
    (∀ slot : OddSlot, WeakPositiveGraded (A slot)) →
    (∀ slot : OddSlot, WeakPositiveIdentified (A slot) (Cc slot.1)) →
  ∀ Cpath : ℝ, 0 ≤ Cpath →
    (∀ slot : OddSlot, HasRealSchurBudget (massConjugatedMatrix π (fun v u =>
      ∑ hh ∈ Finset.range (H + 1), weakPositiveMatrix (A slot) hh v u)) Cpath) →
  ∀ K : ℕ, K ≤ U → ∀ (t : ℝ) (f : CompIn G.comps → Vec 2 → ℝ)
    (r : Representation (CompSpace G.comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField π (fun x v => f v x) →
    let corr := compField π (fun x v =>
      weakGluedLift i N H G (positiveLiftCoefficients Cc) t f v x)
    ContDiff ℝ (K : ℕ) corr ∧ IsZ2Periodic corr ∧
    RawProfileJetBound (D.eps i) K s corr
      (ENNReal.ofReal (Ct * Cpath) * ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) *
        representedSize s (K + N) (D.eps (i - 1)) r)

/-- Close the exact original leaf from five bounded sub-statements. Readout normalization,
its uniform operator norm and representation mapping are discharged by general lemmas. -/
theorem weak_positive_response_jet_of_ingredients
    (hfactory : WeakPlateauParentSettingStatement) (hgraded : WeakGradedRecurrenceStatement)
    (hidentify : WeakPositiveSupportIdentificationStatement)
    (hchart : WeakPositiveDerivativeChartStatement) (hpaths : WeakWeightedPathSumsStatement) :
    WeakPositiveResponseJetStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λf, hΛf, hf⟩ := hfactory α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λr, hΛr, hr⟩ := weak_readout_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λf Λr, by omega, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXf, SZf, hfres⟩ := hf Λ (by omega) bw hbw hbw1 J N R η σ
    hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXr, SZr, hrres⟩ := hr Λ (by omega) bw hbw hbw1 J N R η σ
    hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨max SXf SXr, max SZf SZr, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨P, CHf, Υf, hCHf, hΥf, hp⟩ := hfres sX sZ (by omega) (by omega)
  obtain ⟨Cr, hCr, CHr, Υr, hCHr, hΥr, hrstart⟩ := hrres sX sZ (by omega) (by omega)
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  obtain ⟨Ct, hCt, ht⟩ := hchart N (J * R) (Lr + 3) P s hs₀ hs
  have hpath : 0 ≤ weakPositivePathCost P := mul_nonneg
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
    (Finset.sum_nonneg (fun _ _ => pow_nonneg P.S_nonneg _))
  refine ⟨Ct * weakPositivePathCost P * Cr,
    mul_nonneg (mul_nonneg hCt hpath) hCr, max CHf CHr, max Υf Υr,
    hCHf.trans (le_max_left _ _), hΥf.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  obtain ⟨hjf, hjr⟩ := weak_carrier_start_pair (by omega : 1 ≤ Λ)
    (zero_le_one.trans hCHf) (zero_le_one.trans hCHr) hΥf.le hΥr.le hj₀
  obtain ⟨Mf, hMf⟩ := hp j₀ hjf
  obtain ⟨Mr, hMr⟩ := hrstart j₀ hjr
  refine ⟨max Mf Mr, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hc hl
    i hi hit K hK t g r hin hvalue
  obtain ⟨hgeo, ⟨A⟩⟩ := hMf M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm
    PW Dm stage hc i hi hit
  let π : CompIn (stage i).comps → ℝ := fun v => weakMass D N J η v.1
  let Rout := readoutCLM i (D.eps (i - 1)) η π
    (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
  let f := weakReadoutStep i η (stage i) (stage (i - 1)) g
  have hR : ‖Rout‖ ≤ Cr := hMr M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm
    PW Dm stage CcR hc hl i hi hit
  have hmapped : IsRepresentationAt (D.eps (i - 1)) (K + N) (r.map Rout) :=
    Readout.representation_map_isRepresentationAt r Rout hin
  have hmv : (r.map Rout).value = compField π (fun x v => f v x) := by
    rw [Readout.representation_map_value]
    funext x
    rw [hvalue]
    exact weak_readout_normalized D N J i η hN hJ hgeo.q_gt hgeo.Λ_ge g x
  obtain ⟨hcd, hper, hraw⟩ := ht D Dm j₀ bw i (stage i) π (A ⟨1, by decide⟩).setting.mass_pos
    hgeo A (CcR i) (fun slot => hgraded N (J * R) (Lr + 3) P D Dm j₀ bw i (stage i) π slot (D.eps (i - 1)) (A slot))
    (fun slot => hidentify N (J * R) (Lr + 3) P D Dm j₀ bw i (stage i) π slot (D.eps (i - 1)) (A slot)
      sX sZ (CcR i slot.1) (hl i hi hit slot.1 slot.2)) (weakPositivePathCost P) hpath
    (fun slot => hpaths N (J * R) (Lr + 3) P D Dm j₀ bw i (stage i) π slot (D.eps (i - 1)) (A slot))
    K hK t f (r.map Rout) hmapped hmv
  have hsize : representedSize s (K + N) (D.eps (i - 1)) (r.map Rout) ≤
      ENNReal.ofReal Cr * representedSize s (K + N) (D.eps (i - 1)) r :=
    (Readout.representedSize_map_le r Rout hin).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl)
  let gain := ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s))
  have hy : ENNReal.ofReal (Ct * weakPositivePathCost P) * gain *
      representedSize s (K + N) (D.eps (i - 1)) (r.map Rout) ≤
      ENNReal.ofReal (Ct * weakPositivePathCost P * Cr) * gain *
        representedSize s (K + N) (D.eps (i - 1)) r := by
    calc
      _ ≤ ENNReal.ofReal (Ct * weakPositivePathCost P) * gain *
          (ENNReal.ofReal Cr * representedSize s (K + N) (D.eps (i - 1)) r) :=
        mul_le_mul' le_rfl hsize
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCt hpath)]
        ac_rfl
  exact ⟨hcd, hper, hraw.1.trans hy, fun a ha => (hraw.2 a ha).trans hy⟩

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! The parent-radius factory, split into geometry, actual native fibre facts,
weak-mass Schur sums, and the setting/sequence assembly. Every selector is uniform before
the carrier index, terminal level and actual construction. The common carrier is (1,400). -/

open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs

/-- Scalar construction data fixed before any finite weak menu. -/
structure WeakParentBase where
  α : ℝ
  s : ℝ
  q : ℝ
  ζ : ℝ → ℝ
  hα₀ : 0 < α
  hα₁ : α < 1 / 3
  hs₀ : 0 < s
  hs₁ : s < (1 - α) / 2
  hq : IsAdmissibleQ α s q
  hζ : IsFastProfile ζ

/-- All finite requests, still preceding the construction and datum. -/
structure WeakParentMenu (B : WeakParentBase) where
  Λ : ℕ
  hΛ : 128 ≤ Λ
  bw : ℝ
  hbw : 0 < bw
  hbw1 : bw ≤ 1 / 10000
  J : ℕ
  N : ℕ
  R : ℕ
  η : ℝ
  σ : ℝ
  hJ : 1 ≤ J
  hN : 1 ≤ N
  hη : 0 < η
  hη1 : η ≤ ocDelta B.α B.q / 8
  hσ : 0 < σ
  hσ1 : σ < min (ocC B.α B.q) (B.q - 1)
  Lr : ℕ
  hLr : J * N ≤ Lr

/-- An actual stage covered by the weak-construction premises. -/
structure WeakParentCase {B : WeakParentBase} (R : WeakParentMenu B) (sX sZ : ℕ) where
  j₀ : ℕ
  M : ℕ
  carrier : IsCarrierStart B.α B.q R.Λ R.bw 1 400 j₀
  D : OCData
  hα : D.α = B.α
  hq : D.q = B.q
  hΛ : D.Λ = R.Λ
  hζ : D.ζ = B.ζ
  stream : IsOCStreamSeq B.α B.q R.Λ B.ζ D.Φ
  band : IsOCBandChain B.α B.q R.Λ B.ζ M D.κ
  term : D.term = M
  PW : ProvParams
  Dm : ℕ
  stage : ℕ → GenStage D ScalarH Dm R.bw j₀
  construction : IsWeakConstruction D PW
    (⟨R.N, R.R, sX, sZ, R.η, M + R.J⟩ : WeakMenu) M R.J (D.termRW R.σ M) 0 stage
  i : ℕ
  hi : M < i
  hiJ : i ≤ M + R.J

abbrev WeakParentCase.G {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) := C.stage C.i

def weakParentCap {B : WeakParentBase} (R : WeakParentMenu B) : ℕ := max 2 (1 + R.J * R.N)
def weakParentSlow {B : WeakParentBase} (R : WeakParentMenu B) : ℕ :=
  R.Lr + 3 + (R.N + weakParentCap R)
def weakParentFast {B : WeakParentBase} (R : WeakParentMenu B) : ℕ := R.Lr + 3

def weakParentParameters {B : WeakParentBase} (R : WeakParentMenu B)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S chartC : ℝ) (hS : 0 ≤ S) (hchart : 1 ≤ chartC) :
    WeakPositiveParameters R.N (R.J * R.R) (R.Lr + 3) where
  capMax := weakParentCap R
  cap_ge := le_max_left _ _
  slowOrder := weakParentSlow R
  fastOrder := weakParentFast R
  slow_reserve := Nat.le_add_right _ _
  fast_reserve := le_rfl
  CG := CG
  Cw := Cw
  Cj := Cj
  S := S
  S_nonneg := hS
  chartC := chartC
  chartC_ge := hchart

abbrev weakParentMass {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) : CompIn C.G.comps → ℝ :=
  fun v => weakMass C.D R.N R.J R.η v.1

abbrev weakParentPrice {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) := recordMajorant (weakParentMass C) C.G.fam

/-- Native source regularity and quantitative jets, independently of the price's Schur sums.
The two cap cases record exactly the alternatives required when `Dm` is small. -/
structure WeakParentNativeFacts {B : WeakParentBase} {R : WeakParentMenu B} {sX sZ : ℕ}
    (C : WeakParentCase R sX sZ) (Cj : ℕ → ℕ → ℝ) : Prop where
  cap_nonempty : 1 ≤ R.R → 1 + R.J * R.N ≤ C.Dm
  empty_zero : R.R = 0 → ∀ v u, IsEmpty (C.G.fam.Γ v u)
  mass_pos : ∀ v, 0 < weakParentMass C v
  depth : C.G.fam.HasDepthAtMost (R.J * R.R)
  cap : ∀ slot v u d, weakParentCap R < d.1 →
    (weakPositiveNativeData C.i C.G slot).edge v u d = []
  transverse : ∀ slot v u d, ∀ γ ∈ windowEdges (weakSlotLeft C.D C.i slot.1)
      (weakSlotRight C.D C.i slot.1) (weakPositiveNativeData C.i C.G slot).edge v u d,
    ∀ α, IsTransverseOn (pulseParallel slot.1)
      (Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1)) (γ.coeff α)
  measurable : ∀ slot v u d, ∀ γ ∈ windowEdges (weakSlotLeft C.D C.i slot.1)
      (weakSlotRight C.D C.i slot.1) (weakPositiveNativeData C.i C.G slot).edge v u d,
    ∀ α X z, Measurable fun t => γ.coeff α t X z
  smooth : ∀ slot v u d, ∀ γ ∈ windowEdges (weakSlotLeft C.D C.i slot.1)
      (weakSlotRight C.D C.i slot.1) (weakPositiveNativeData C.i C.G slot).edge v u d,
    ∀ α, ∀ t ∈ Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1),
      IsBoxSmooth (weakParentSlow R + 4 * (R.J * R.R + 1) * (R.N + weakParentCap R) ^ 2)
        (max (weakParentFast R) (weakParentFast R + 2) + R.J * R.R * weakParentCap R +
          2 * R.N + 2 * weakParentCap R) (γ.coeff α t)
  source : ∀ S : ℝ, HasRealSchurBudget (weakParentPrice C) S → ∀ slot,
    IsScaledJetEnvelope (weakParentMass C)
      (windowEdges (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1)
        (weakPositiveNativeData C.i C.G slot).edge)
      (Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1)) 1 Cj
      (weakParentSlow R + 4 * (R.J * R.R + 1) * (R.N + weakParentCap R) ^ 2)
      (max (weakParentFast R) (weakParentFast R + 2) + R.J * R.R * weakParentCap R +
        2 * R.N + 2 * weakParentCap R) (weakParentPrice C) S

/-- Common quantifier order for the four independent numeric selectors. -/
def WeakParentUniformFactStatement
    (Witness : ∀ {B : WeakParentBase}, WeakParentMenu B → Type)
    (claim : ∀ {B : WeakParentBase} (R : WeakParentMenu B), Witness R →
      ∀ {sX sZ : ℕ}, WeakParentCase R sX sZ → Prop)
    (scope : ℕ → Prop := fun _ => True) : Prop :=
  ∀ B : WeakParentBase, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
  ∀ R : WeakParentMenu B, Λ₀ ≤ R.Λ → scope R.J →
  ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
  ∃ w : Witness R, ∀ j₀ : ℕ, ∃ M₀ : ℕ,
  ∀ C : WeakParentCase R sX sZ, C.j₀ = j₀ → M₀ ≤ C.M → claim R w C

/-- Native levels, parent torus law and physical chart jets. -/
def WeakParentGeometryStatement (scope : ℕ → Prop := fun _ => True) : Prop :=
  WeakParentUniformFactStatement (fun {_B} _R => {c : ℝ // 1 ≤ c})
    (fun {_B} R c {_sX _sZ} C => WeakPositiveGeometry
      (weakParentParameters R 0 0 0 0 c.1 le_rfl c.2) C.i C.G) scope

/-- Time measurability, box smoothness, transversality,
positive masses, capped orders and source jets of the actual context. -/
def WeakParentNativeFactsStatement (scope : ℕ → Prop := fun _ => True) : Prop :=
  WeakParentUniformFactStatement (fun {_B} _R => ℕ → ℕ → ℝ)
    (fun {_B} _R Cj {_sX _sZ} C => WeakParentNativeFacts C Cj) scope

/-- Both record-majorant sums at every weak stage. -/
def WeakParentMassSumsStatement (scope : ℕ → Prop := fun _ => True) : Prop :=
  WeakParentUniformFactStatement (fun {_B} _R => {S : ℝ // 0 ≤ S})
    (fun {_B} _R S {_sX _sZ} C => HasRealSchurBudget (weakParentPrice C) S.1) scope

/-- Metric and drift constants and the capped original-window
setting plus both recurrences, from the three separate certificates. -/
def WeakParentSettingAssemblyStatement (scope : ℕ → Prop := fun _ => True) : Prop :=
  WeakParentUniformFactStatement (fun {_B} _R => (ℕ → ℝ) × (ℕ → ℝ))
    (fun {_B} R g {_sX _sZ} C => ∀ (c : {c : ℝ // 1 ≤ c}) (Cj : ℕ → ℕ → ℝ) (S : {S : ℝ // 0 ≤ S}),
      let P := weakParentParameters R g.1 g.2 Cj S.1 c.1 S.2 c.2
      WeakPositiveGeometry P C.i C.G → WeakParentNativeFacts C Cj →
      HasRealSchurBudget (weakParentPrice C) S.1 →
      Nonempty (∀ slot, WeakPositiveSlot P C.i C.G (weakParentMass C) slot)) scope

/-- The factory on a specified number of weak passages. Scope `J=1` is the root stage alone;
scope `True` gives every number of passages. -/
def WeakParentSettingStatementOn (scope : ℕ → Prop) : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr → scope Jw →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ P : WeakPositiveParameters Nw (Jw * Rw) (Lr + 3),
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu)
        M Jw (D.termRW σw M) 0 stage →
    ∀ i, M < i → i ≤ M + Jw →
      WeakPositiveGeometry P i (stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
        (fun v => weakMass D Nw Jw η₀ v.1) slot)

/-- The exact factory from four bounded analytic and geometric ingredients. -/
theorem weak_parent_setting_on_of_ingredients (scope : ℕ → Prop)
    (hgeometry : WeakParentGeometryStatement scope)
    (hnative : WeakParentNativeFactsStatement scope) (hmass : WeakParentMassSumsStatement scope)
    (hsetting : WeakParentSettingAssemblyStatement scope) : WeakParentSettingStatementOn scope := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakParentBase := ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  obtain ⟨Λg, hΛg, hg⟩ := hgeometry B
  obtain ⟨Λn, hΛn, hn⟩ := hnative B
  obtain ⟨Λm, hΛm, hm⟩ := hmass B
  obtain ⟨Λa, hΛa, ha⟩ := hsetting B
  refine ⟨max Λg (max Λn (max Λm Λa)), by omega, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N Rw η σ hJ hN hη hη1 hσ hσ1 Lr hLr hScope
  let R : WeakParentMenu B := ⟨Λ, by omega, bw, hbw, hbw1, J, N, Rw, η, σ,
    hJ, hN, hη, hη1, hσ, hσ1, Lr, hLr⟩
  obtain ⟨SXg, SZg, hg⟩ := hg R (by change Λg ≤ Λ; omega) hScope
  obtain ⟨SXn, SZn, hn⟩ := hn R (by change Λn ≤ Λ; omega) hScope
  obtain ⟨SXm, SZm, hm⟩ := hm R (by change Λm ≤ Λ; omega) hScope
  obtain ⟨SXa, SZa, ha⟩ := ha R (by change Λa ≤ Λ; omega) hScope
  refine ⟨max SXg (max SXn (max SXm SXa)), max SZg (max SZn (max SZm SZa)), ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨c, hg⟩ := hg sX sZ (by omega) (by omega)
  obtain ⟨Cj, hn⟩ := hn sX sZ (by omega) (by omega)
  obtain ⟨S, hm⟩ := hm sX sZ (by omega) (by omega)
  obtain ⟨g, ha⟩ := ha sX sZ (by omega) (by omega)
  let P := weakParentParameters R g.1 g.2 Cj S.1 c.1 S.2 c.2
  refine ⟨P, 1, 400, le_rfl, by norm_num, ?_⟩
  intro j₀ hcarrier
  obtain ⟨Mg, hg⟩ := hg j₀
  obtain ⟨Mn, hn⟩ := hn j₀
  obtain ⟨Mm, hm⟩ := hm j₀
  obtain ⟨Ma, ha⟩ := ha j₀
  refine ⟨max Mg (max Mn (max Mm Ma)), ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage hconstruction i hi hiJ
  let C : WeakParentCase R sX sZ := ⟨j₀, M, hcarrier, D, hDα, hDq, hDΛ, hDζ, hstream,
    hband, hterm, PW, Dm, stage, hconstruction, i, hi, hiJ⟩
  have hG : WeakPositiveGeometry P i (stage i) := hg C rfl (by change Mg ≤ M; omega)
  exact ⟨hG, ha C rfl (by change Ma ≤ M; omega) c Cj S hG (hn C rfl (by change Mn ≤ M; omega)) (hm C rfl (by change Mm ≤ M; omega))⟩

/-- Erase the vacuous scope premise to recover the exact original factory statement. -/
theorem weak_parent_setting_of_ingredients (hgeometry : WeakParentGeometryStatement)
    (hnative : WeakParentNativeFactsStatement) (hmass : WeakParentMassSumsStatement)
    (hsetting : WeakParentSettingAssemblyStatement) : WeakPlateauParentSettingStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := weak_parent_setting_on_of_ingredients (fun _ => True)
    hgeometry hnative hmass hsetting α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  exact htail Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr True.intro

end AVRegularity.Finite.WeakLift
end
