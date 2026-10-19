-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Finite.WeakPositive.NativeAdapter
public import AVRegularity.Finite.Assembly.WeakPositiveChartOfIngredients

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Bounded positive terminal transfer. The original-slot coefficient factory and physical
chart action supply pointwise positive jets; the native recurrence and torus-compatible charts
supply regularity and periodicity. The dimension-free normalization closes the raw
profile bound, including the zero output jet, without an order-zero realization.

Proof: the pointwise input uses the shared terminal lift at rho = cr*liftLength,
StageNativeLiftSourceEnvelope from the weak invariant, the radius-generic graded recurrence
and arbitrary-sequence identification, then the generic positive chart actions and
Schur path sums. The bandChain_terminal_contrast bound absorbs
the factor dStar/e in the actual terminal pulse scale, uniformly before M. Spatial regularity
and periodicity use the same native lift and the pulse regularity and periodicity lemmas.

The degenerate cases are included: NT=0 has only the identity and hence zero correction; an
empty family and zero datum also give zero. One component, Jw=1, smallest orders and cr=1
retain the same argument. All constants precede j0, M, phase and datum; the numerical premise
`G₀ ≤ H_prod + 1` is retained in the shared menu.
-/

/-- The actual terminal correction has positive pointwise physical jets, including its value. -/
def TerminalPositivePointwiseProperty : TerminalProfileProperty :=
  fun _s E e C k kin r _R _cov osc =>
    0 < E ∧ 0 < e ∧ WeakLift.PositivePhysicalJetEstimate e E k kin C r.value osc

/-- The uniform pointwise positive-jet statement; its proof combines the terminal lift, grading
and identification, the chart action and the path sums. -/
def TerminalPositivePointwiseStatement : Prop :=
  TerminalUniformProfileStatement TerminalPositivePointwiseProperty

/-- The original oscillatory regularity and physical torus law. -/
def TerminalPositiveSpatialProperty : TerminalProfileProperty :=
  fun _s _E _e _C k _kin _r _R _cov osc =>
    ContDiff ℝ (k : ℕ) osc ∧ IsZ2Periodic osc

/-- The uniform spatial statement, from the native recurrence and the regularity and periodicity
of the physical charts. -/
def TerminalPositiveSpatialStatement : Prop :=
  TerminalUniformProfileStatement TerminalPositiveSpatialProperty

private theorem terminal_positive_pointwise_mono {H H' : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (s E e C D : ℝ) (k kin : ℕ) (r : Representation H) (R : H →L[ℝ] H')
    (cov osc : Vec 2 → H')
    (h : TerminalPositivePointwiseProperty s E e C k kin r R cov osc) :
    TerminalPositivePointwiseProperty s E e (max C D) k kin r R cov osc := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hsum (x : Vec 2) : 0 ≤ ∑ α ∈ multiIndicesBetween 1 kin,
      E ^ (α 0 + α 1) * ‖partialDerivative α r.value x‖ :=
    Finset.sum_nonneg fun α _ => mul_nonneg (pow_nonneg h.1.le _) (norm_nonneg _)
  have hprice (x : Vec 2) : C * (e / E) *
      (∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α r.value x‖) ≤
      max C D * (e / E) *
      (∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α r.value x‖) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (div_pos h.2.1 h.1).le) (hsum x)
  constructor
  · intro x
    exact (h.2.2.1 x).trans (hprice x)
  · intro α hα x
    exact (h.2.2.2 α hα x).trans (hprice x)

/-- Exact positive-lift leaf from pointwise jets and spatial regularity; norm restoration is proved. -/
theorem terminal_positive_lift_transfer_of_ingredients
    (hpoint : TerminalPositivePointwiseStatement) (hspatial : TerminalPositiveSpatialStatement) :
    TerminalPositiveLiftTransferStatement := by
  have hp := terminal_uniform_profile_merge TerminalPositivePointwiseProperty
    TerminalPositiveSpatialProperty
    (fun s E e C D k kin r R cov osc hpoint hspatial =>
      ⟨terminal_positive_pointwise_mono s E e C D k kin r R cov osc hpoint, hspatial⟩)
    hpoint hspatial
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hp α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cjet, hCjet, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  refine ⟨Cjet * (Lr + (NT + 2 * pT) + 4).factorial,
    mul_nonneg hCjet (Nat.cast_nonneg _), ?_⟩
  intro j₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have h := hMtail M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage
    tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hs1 : s < 1 := hs₁.trans (by linarith only [hα₀] : (1 - α) / 2 < 1)
  have hnorm := WeakLift.positive_chart_norm_restoration (D.eps M) (D.eps (M - 1)) s
    (Lr + 3) (Lr + (NT + 2 * pT) + 4) Cjet h.1.2.1 h.1.1 hs₀ hs1 hCjet r _ hr h.1.2.2
  exact ⟨h.2.1, h.2.2, hnorm⟩

end AVRegularity.Finite.TerminalLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Finite.WeakLift

/-! The native ingredient contains only actual coefficient properties.
All structural ambient-cap alternatives, positivity, depth and finite degree support
are discharged by construction facts. The original family is retained. -/

open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs

/-- Actual clipped coefficient transversality, time measurability, box smoothness and
quantitative source jets. These are the four analytic fields of
`WeakParentNativeFactsStatement`. -/
structure WeakParentNativeCoefficientFacts {B : WeakParentBase} {R : WeakParentMenu B}
    {sX sZ : ℕ} (C : WeakParentCase R sX sZ) (Cj : ℕ → ℕ → ℝ) : Prop where
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

/-- The analytic source input, with constants and floors before the actual construction.
The common-case adapter supplies its real coefficient templates and size certificate. -/
def WeakParentNativeCoefficientFactsStatement : Prop :=
  WeakParentUniformFactStatement (fun {_B} _R => ℕ → ℕ → ℝ)
    (fun {_B} _R Cj {_sX _sZ} C => WeakParentNativeCoefficientFacts C Cj)

/-- Structural native facts require no further analytic premise. -/
theorem weak_parent_native_facts_of_coefficients {B : WeakParentBase} {R : WeakParentMenu B}
    {sX sZ : ℕ} (C : WeakParentCase R sX sZ) (Cj : ℕ → ℕ → ℝ)
    (hc : WeakParentNativeCoefficientFacts C Cj) : WeakParentNativeFacts C Cj := by
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have heps (i : ℕ) : 0 < C.D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  refine {
    cap_nonempty := weak_parent_case_cap C
    empty_zero := weak_parent_case_empty_zero C
    mass_pos := fun v => WeakEntryProofs.weakMass_pos C.D R.N R.J R.η R.hN R.hJ heps v.1
    depth := WeakEntryProofs.weakConstruction_depth C.PW
      (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
      (C.D.termRW R.σ C.M) C.stage C.construction C.i C.hi.le C.hiJ
    cap := weak_parent_case_native_cap C
    transverse := hc.transverse
    measurable := hc.measurable
    smooth := hc.smooth
    source := hc.source }

/-- Exact1b statement from its remaining actual coefficient claim; proved construction
facts are discharged inside the assembly, rather than left as helper hypotheses. -/
theorem weak_parent_native_facts_of_ingredients
    (hc : WeakParentNativeCoefficientFactsStatement) : WeakParentNativeFactsStatement := by
  intro B
  obtain ⟨Λ₀, hΛ₀, hR⟩ := hc B
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro R hΛ hscope
  obtain ⟨SX, SZ, hres⟩ := hR R hΛ hscope
  refine ⟨SX, SZ, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cj, hC⟩ := hres sX sZ hsX hsZ
  refine ⟨Cj, ?_⟩
  intro j₀
  obtain ⟨M₀, hM⟩ := hC j₀
  refine ⟨M₀, ?_⟩
  intro C hj hCM
  exact weak_parent_native_facts_of_coefficients C Cj (hM C hj hCM)

/-- The complete weak parent factory has just one remaining actual coefficient input. -/
theorem weak_parent_factory_of_native_coefficients
    (hc : WeakParentNativeCoefficientFactsStatement) : WeakPlateauParentSettingStatement :=
  weak_parent_setting_of_native (weak_parent_native_facts_of_ingredients hc)

end AVRegularity.Finite.WeakLift
end
