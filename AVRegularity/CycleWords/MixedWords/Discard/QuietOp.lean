-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.WeakContCutCurve
public import AVRegularity.CycleWords.MixedWords.Discard.WeakContFluxTerm
import AVRegularity.CycleWords.MixedWords.Discard.Unit
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
public import AVRegularity.CycleWords.OriginalTaylorPairNativeFluxSupported
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleWords.Discard

/-! # Coordinate duality of a level of an arbitrary chain

`weakCont_component_duality` is `wordChain_component_reversedChain_native_duality` without the
`L²(I; L²)` realization of the letter flux. Hypotheses instead: the flux has `L²(I; L²)`
realizations on balls; with a weight `wt`, `wt⁻¹·flux(r) ∈ L²` with an integrable bound `A(r)`; and
`wt·(Ψ, ∇Ψ)(r) ∈ L²` uniformly in time for the scalar reversed chain `Ψ` of the test.

The proof: the cut pairing of `WeakContCutCurve` for every cutoff, and dominated convergence in
time (`weakCont_limit`), with the limit and the bound at one time from `WeakContFluxTerm`. -/

/-- **Removal of the cutoff by dominated convergence in time.** -/
theorem weakCont_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (e : E) {a b : ℝ} (hab : a ≤ b)
    (cb ca vg va : Lp ℝ 2 (volume : Measure (Vec 2)))
    (sl Ψ1 Xg Yg : ℝ → PlaneHk Set.univ 1 ℝ)
    (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (S : ℕ → ℝ → PlaneFluxL2 E)
    (hslm : MemLp sl 2 (volume.restrict (Icc a b)))
    (hΨm : MemLp Ψ1 2 (volume.restrict (Icc a b))) (Bψ : ℝ) (hBψ : ∀ r ∈ Icc a b, ‖Ψ1 r‖ ≤ Bψ)
    (hXm : MemLp Xg 2 (volume.restrict (Icc a b)))
    (hYm : MemLp Yg 2 (volume.restrict (Icc a b)))
    (hSl : ∀ n, MemLp (S n) 2 (volume.restrict (Icc a b)))
    (hXY : ∀ r, inner ℝ (Xg r) (Ψ1 r) = inner ℝ (Yg r) (sl r))
    (hS : ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2, ∀ᵐ z ∂volume,
      z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) →
        (S n r k : Vec 2 → E) z = Fl r z k)
    (hFm : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2,
      AEStronglyMeasurable (fun z => Fl r z k) volume)
    (wt : Vec 2 → ℝ) (hwc : Continuous wt) (hw1 : ∀ z, 0 < wt z)
    (A : ℝ → ℝ) (hA0 : ∀ r, 0 ≤ A r) (hA : IntegrableOn A (Icc a b))
    (hwt : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2,
      eLpNorm (fun z => (wt z)⁻¹ • Fl r z k) 2 volume ≤ ENNReal.ofReal (A r))
    (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΨv : ∀ r ∈ Icc a b,
      eLpNorm (fun z => wt z * (planeHkValueOperator 1 (Ψ1 r) : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd)
    (hΨg : ∀ r ∈ Icc a b, ∀ k : Fin 2,
      eLpNorm (fun z => wt z * (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd)
    (hpair : ∀ n, inner ℝ (weakContL2Cut n cb) vg - inner ℝ (weakContL2Cut n ca) va =
      ∫ r in a..b, (inner ℝ (Xg r + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S n r)))
        (weakContH1Cut n (Ψ1 r)) - inner ℝ (Yg r) (weakContH1Cut n (sl r)))) :
    (∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2, Integrable (fun z => inner ℝ e (Fl r z k) *
        (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z) volume) ∧
      IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2, inner ℝ e (Fl r z k) *
        (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z) volume a b ∧
      inner ℝ cb vg = inner ℝ ca va -
        ∫ r in a..b, ∫ z, ∑ k : Fin 2, inner ℝ e (Fl r z k) *
          (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z := by
  obtain ⟨Ifun, hIfun⟩ : ∃ Ifun : ℕ → ℝ → ℝ, Ifun = fun n r =>
      inner ℝ (Xg r + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S n r)))
        (weakContH1Cut n (Ψ1 r)) - inner ℝ (Yg r) (weakContH1Cut n (sl r)) := ⟨_, rfl⟩
  obtain ⟨hfun, hhfun⟩ : ∃ hfun : ℝ → ℝ, hfun = fun r => ∫ z, ∑ k : Fin 2,
      inner ℝ e (Fl r z k) * (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z := ⟨_, rfl⟩
  obtain ⟨A0, hA0def⟩ : ∃ A0 : ℝ, A0 = weakContH1Budget 0 + weakContH1Budget 1 := ⟨_, rfl⟩
  have hA0nn : 0 ≤ A0 := by
    rw [hA0def]
    exact add_nonneg (weakContH1Budget_nonneg 0) (weakContH1Budget_nonneg 1)
  obtain ⟨bound, hbound⟩ : ∃ bound : ℝ → ℝ, bound = fun r => A0 * ‖Xg r‖ * Bψ +
      weakContFluxConst * (‖e‖ * A r) * Bd + A0 * (‖Yg r‖ * ‖sl r‖) := ⟨_, rfl⟩
  -- the integrand at almost every time
  have hper0 : ∀ᵐ r ∂volume.restrict (Icc a b),
      (∀ k : Fin 2, Integrable (fun z => inner ℝ e (Fl r z k) *
        (planeH1GradientOperator (Ψ1 r) k : Vec 2 → ℝ) z) volume) ∧
      Tendsto (fun n => Ifun n r) atTop (𝓝 (-hfun r)) ∧ ∀ n, |Ifun n r| ≤ bound r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.mpr hS, hFm, hwt]
      with r hr h1 h2 h3
    obtain ⟨hint, hl, hbnd⟩ := weakCont_integrand_tendsto e (Fl r) wt hwc hw1 h2 (A r) (hA0 r) h3
      (fun n => S n r) h1 (Ψ1 r) Bd hBd (hΨv r hr) (hΨg r hr) (sl r) (Xg r) (Yg r) (hXY r)
    rw [hIfun, hhfun, hbound]
    refine ⟨hint, hl, fun n => (hbnd n).trans ?_⟩
    rw [← hA0def]
    have h4 : A0 * ‖Xg r‖ * ‖Ψ1 r‖ ≤ A0 * ‖Xg r‖ * Bψ :=
      mul_le_mul_of_nonneg_left (hBψ r hr) (mul_nonneg hA0nn (norm_nonneg _))
    have h5 : A0 * ‖Yg r‖ * ‖sl r‖ = A0 * (‖Yg r‖ * ‖sl r‖) := by ring
    linarith
  have hper : ∀ᵐ r ∂volume.restrict (Icc a b),
      Tendsto (fun n => Ifun n r) atTop (𝓝 (-hfun r)) ∧ ∀ n, |Ifun n r| ≤ bound r :=
    hper0.mono fun r hr => hr.2
  -- measurability in time
  have hImeas : ∀ n, AEStronglyMeasurable (Ifun n) (volume.restrict (Icc a b)) := by
    intro n
    have hsrc : MemLp (fun r => planeSourceDual (0 : Lp ℝ 2 (volume : Measure (Vec 2)))
        (planeFluxFiberCoordinateCLM e (S n r))) 2 (volume.restrict (Icc a b)) :=
      planeSourceDual_memLp (fun _ => 0) MemLp.zero' _
        ((planeFluxFiberCoordinateCLM e).comp_memLp' (hSl n))
    have h1 : AEStronglyMeasurable (fun r => inner ℝ
        (Xg r + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S n r)))
        (weakContH1Cut n (Ψ1 r))) (volume.restrict (Icc a b)) :=
      (hXm.aestronglyMeasurable.add hsrc.aestronglyMeasurable).inner
        ((weakContH1Cut n).continuous.comp_aestronglyMeasurable hΨm.aestronglyMeasurable)
    have h2 : AEStronglyMeasurable (fun r => inner ℝ (Yg r) (weakContH1Cut n (sl r)))
        (volume.restrict (Icc a b)) :=
      hYm.aestronglyMeasurable.inner
        ((weakContH1Cut n).continuous.comp_aestronglyMeasurable hslm.aestronglyMeasurable)
    rw [hIfun]
    exact h1.sub h2
  -- the dominating function
  have hbint : Integrable bound (volume.restrict (Icc a b)) := by
    have h1 : Integrable (fun r => ‖Xg r‖) (volume.restrict (Icc a b)) :=
      (hXm.integrable one_le_two).norm
    have h3 : Integrable (fun r => ‖Yg r‖ * ‖sl r‖) (volume.restrict (Icc a b)) :=
      hYm.norm.integrable_mul hslm.norm
    have hA' : Integrable A (volume.restrict (Icc a b)) := hA
    rw [hbound]
    exact (((h1.const_mul A0).mul_const Bψ).add
      (((hA'.const_mul ‖e‖).const_mul weakContFluxConst).mul_const Bd)).add (h3.const_mul A0)
  have hsub : volume.restrict (Set.uIoc a b) ≤ volume.restrict (Icc a b) := by
    rw [uIoc_of_le hab]
    exact Measure.restrict_mono Ioc_subset_Icc_self le_rfl
  have hper' := (ae_restrict_iff' measurableSet_Icc).mp hper
  have hlimI : Tendsto (fun n => ∫ r in a..b, Ifun n r) atTop (𝓝 (∫ r in a..b, -hfun r)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
      (Filter.Eventually.of_forall fun n => (hImeas n).mono_measure hsub)
      (Filter.Eventually.of_forall fun n => by
        filter_upwards [hper'] with r hr hmem
        rw [uIoc_of_le hab] at hmem
        rw [Real.norm_eq_abs]
        exact (hr ⟨hmem.1.le, hmem.2⟩).2 n)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hbint)
      (by
        filter_upwards [hper'] with r hr hmem
        rw [uIoc_of_le hab] at hmem
        exact (hr ⟨hmem.1.le, hmem.2⟩).1)
  have hlimL : Tendsto (fun n => inner ℝ (weakContL2Cut n cb) vg -
      inner ℝ (weakContL2Cut n ca) va) atTop (𝓝 (inner ℝ cb vg - inner ℝ ca va)) :=
    ((weakContL2Cut_tendsto cb).inner tendsto_const_nhds).sub
      ((weakContL2Cut_tendsto ca).inner tendsto_const_nhds)
  have hpair' : ∀ n, inner ℝ (weakContL2Cut n cb) vg - inner ℝ (weakContL2Cut n ca) va =
      ∫ r in a..b, Ifun n r := by
    intro n
    rw [hIfun]
    exact hpair n
  have heq : inner ℝ cb vg - inner ℝ ca va = ∫ r in a..b, -hfun r :=
    tendsto_nhds_unique hlimL (hlimI.congr fun n => (hpair' n).symm)
  -- integrability of the limit
  have hhint : IntervalIntegrable hfun volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hmeasN : AEStronglyMeasurable (fun r => -hfun r) (volume.restrict (Icc a b)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hImeas (hper.mono fun r hr => hr.1)
    have hmeas : AEStronglyMeasurable hfun (volume.restrict (Icc a b)) :=
      hmeasN.neg.congr (Filter.Eventually.of_forall fun r => neg_neg (hfun r))
    refine Integrable.mono' hbint hmeas ?_
    filter_upwards [hper] with r hr
    have h1 : Tendsto (fun n => |Ifun n r|) atTop (𝓝 |-hfun r|) := hr.1.abs
    have h2 := le_of_tendsto h1 (Filter.Eventually.of_forall hr.2)
    rw [abs_neg] at h2
    rw [Real.norm_eq_abs]
    exact h2
  rw [intervalIntegral.integral_neg] at heq
  rw [hhfun] at hhint heq
  refine ⟨hper0.mono fun r hr => hr.1, hhint, ?_⟩
  linarith

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- The scalar `H¹` slice of a coordinate of a level is square integrable in time. -/
theorem weakCont_slice_memLp (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (e : h i.2) :
    MemLp (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
      (coupledPlaneH1Slice Uw i r)) 2 (volume.restrict (Icc a b)) := by
  have hd := coupledWeakSolution_h1_trace_data hsol i
  simpa only [Function.comp_def, mapPlaneHkOperator_apply] using
    (mapPlaneHkOperator 1 (InnerProductSpace.toDual ℝ (h i.2) e)).comp_memLp' hd.2.1

/-- The `H¹` truncation of a reversed chain is bounded and square integrable on the window. -/
theorem weakCont_reversed_bound (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    ∃ Bψ : ℝ, (∀ r ∈ Icc a b, ‖truncatePlaneHk hm (ψ 0 () (-r))‖ ≤ Bψ) ∧
      MemLp (fun r => truncatePlaneHk hm (ψ 0 () (-r))) 2 (volume.restrict (Icc a b)) := by
  have hΨc : ContinuousOn (fun r => truncatePlaneHk hm (ψ 0 () (-r))) (Icc a b) :=
    (truncatePlaneHk hm).continuous.comp_continuousOn
      ((hψ.1 ((0 : Fin 1), ())).comp continuous_neg.continuousOn
        fun _ hr => ⟨neg_le_neg hr.2, neg_le_neg hr.1⟩)
  obtain ⟨Bψ, hBψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨc
  exact ⟨Bψ, hBψ, MemLp.of_bound (hΨc.aestronglyMeasurable measurableSet_Icc) Bψ
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hBψ))⟩

/-- The generator dual of the forward equation against `z` is that of the adjoint equation
against `u`. -/
theorem weakCont_generator_symm (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C) (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (r : ℝ) (u z : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual (G r) v hv r C (hC r) u) z =
      inner ℝ (planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r C'
        (hC' r) z) u := by
  rw [planeRealBlochGeneratorDual_pair, planeRealBlochGeneratorDual_pair]
  exact planeRealBlochGeneratorForm_opposite_drift G hG v hv M hb C hCpos hC C' hC'pos hC' r u z

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The letter flux of a level is measurable in space at almost every time, when it has
realizations on balls. -/
theorem weakCont_flux_aestronglyMeasurable (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2)
    (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ)
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (S : ℕ → ℝ → PlaneFluxL2 (h i.2))
    (hS : ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume,
      z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) → (S n r k : Vec 2 → h i.2) z =
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) :
    ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2, AEStronglyMeasurable
      (fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) volume := by
  filter_upwards [ae_all_iff.mpr hS] with r hr k
  refine weakCont_aestronglyMeasurable_of_balls _ (fun n z => (S n r k : Vec 2 → h i.2) z)
    (fun n => Lp.aestronglyMeasurable _) fun n => ?_
  filter_upwards [hr n k] with z hz hzb
  refine hz (Metric.ball_subset_ball ?_ hzb)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The generator dual of the slice of a level is square integrable in time. -/
theorem weakCont_slice_generator_memLp (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (e : h i.2) :
    MemLp (fun r => planeRealBlochGeneratorDual (G r) v hv r C (hC r)
      (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r))) 2
      (volume.restrict (Icc a b)) :=
  planeRealBlochGeneratorDual_timeMemLp (volume.restrict (Icc a b)) G hG v hv C hCpos.le hC _
    (weakCont_slice_memLp G letters X0 δ κ a b v f U Uw hsol i e)

/-- The adjoint generator dual of a square integrable curve is square integrable in time. -/
theorem weakCont_adjoint_generator_memLp (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (Ψ1 : ℝ → PlaneHk Set.univ 1 ℝ) (hΨm : MemLp Ψ1 2 (volume.restrict (Icc a b))) :
    MemLp (fun r => planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r
      C' (hC' r) (Ψ1 r)) 2 (volume.restrict (Icc a b)) :=
  planeRealBlochGeneratorDual_timeMemLp (volume.restrict (Icc a b)) G hG (fun t x => -v t x)
    (cellDrift_neg hv) C' hC'pos.le hC' Ψ1 hΨm

/-- The cut pairing of `WeakContCutCurve` with the concrete cutoffs. -/
theorem weakCont_component_pairing (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C) (C' : ℝ)
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (e : h i.2) (m : ℕ) (hm : 1 ≤ m)
    (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw)
    (n : ℕ) (S : ℝ → PlaneFluxL2 (h i.2)) (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume,
      z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) → (S r k : Vec 2 → h i.2) z =
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) :
    inner ℝ (weakContL2Cut n
        (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b))))
        (planeHkValueOperator m (g ())) -
      inner ℝ (weakContL2Cut n
        (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i))))
        (planeHkValueOperator m (ψ 0 () (-a))) =
      ∫ r in a..b,
        (inner ℝ (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
            (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
              planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r)))
            (weakContH1Cut n (truncatePlaneHk hm (ψ 0 () (-r)))) -
          inner ℝ (planeRealBlochGeneratorDual (G r) (fun t x => -v t x) (cellDrift_neg hv) r C'
              (hC' r) (truncatePlaneHk hm (ψ 0 () (-r))))
            (weakContH1Cut n (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
              (coupledPlaneH1Slice Uw i r)))) :=
  weakCont_cut_pairing hD G hG letters X0 δ κ a b hab v hv C hCpos hC C' hC' M hb
    f U Uw hsol i (Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1)) S hSl hS e
    (weakContL2Cut n) (weakContH1Cut n) (weakContH1Cut_value n) (weakContL2Cut_inner n)
    (weakContH1Cut_jet_outside n) m hm g ψ ψw hψ

/-- **Coordinate duality with the reversed chain, split-weight form.** -/
theorem weakCont_component_duality (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (hcut : ∀ n : ℕ, ∃ S : ℝ → PlaneFluxL2 (h i.2), MemLp S 2 (volume.restrict (Icc a b)) ∧
      ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((n : ℝ) + 1) → (S r k : Vec 2 → h i.2) z =
          wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k)
    (wt : Vec 2 → ℝ) (hwc : Continuous wt) (hw1 : ∀ z, 0 < wt z)
    (A : ℝ → ℝ) (hA0 : ∀ r, 0 ≤ A r) (hA : IntegrableOn A (Icc a b))
    (hwt : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2,
      eLpNorm (fun z => (wt z)⁻¹ •
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) 2 volume ≤
        ENNReal.ofReal (A r))
    (e : h i.2) (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw)
    (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΨv : ∀ r ∈ Icc a b, eLpNorm (fun z => wt z *
      (planeHkValueOperator 1 (truncatePlaneHk hm (ψ 0 () (-r))) : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd)
    (hΨg : ∀ r ∈ Icc a b, ∀ k : Fin 2, eLpNorm (fun z => wt z *
      (planeH1GradientOperator (truncatePlaneHk hm (ψ 0 () (-r))) k : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd) :
    (∀ᵐ r ∂volume.restrict (Icc a b), ∀ k : Fin 2, Integrable (fun z =>
        inner ℝ e (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) *
          (planeH1GradientOperator (truncatePlaneHk hm (ψ 0 () (-r))) k : Vec 2 → ℝ) z)
        volume) ∧
      IntervalIntegrable (fun r => ∫ z, ∑ k : Fin 2,
        inner ℝ e (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) *
          (planeH1GradientOperator (truncatePlaneHk hm (ψ 0 () (-r))) k : Vec 2 → ℝ) z)
        volume a b ∧
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b)))
          (planeHkValueOperator m (g ())) =
        inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i)))
            (planeHkValueOperator m (ψ 0 () (-a))) -
          ∫ r in a..b, ∫ z, ∑ k : Fin 2,
            inner ℝ e (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z k) *
              (planeH1GradientOperator (truncatePlaneHk hm (ψ 0 () (-r))) k : Vec 2 → ℝ) z := by
  obtain ⟨C, hCpos, hC⟩ := cellDriftTorusSymbol_bound v hv
  obtain ⟨C', hC'pos, hC'⟩ := cellDriftTorusSymbol_bound _ (cellDrift_neg hv)
  obtain ⟨Bψ, hBψ, hΨm⟩ := weakCont_reversed_bound G a b v m hm g ψ ψw hψ
  choose S hSl hS using fun n : ℕ => hcut (2 * n + 2)
  exact weakCont_limit e hab _ _ _ _ _ _ _ _
    (fun r z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r z) S
    (weakCont_slice_memLp G letters X0 δ κ a b v f U Uw hsol i e) hΨm Bψ hBψ
    (weakCont_slice_generator_memLp G hG letters X0 δ κ a b v hv C hCpos hC f U Uw hsol i e)
    (weakCont_adjoint_generator_memLp G hG a b v hv C' hC'pos hC' _ hΨm) hSl
    (fun r => weakCont_generator_symm G hG v hv M hb C hCpos hC C' hC'pos hC' r _ _) hS
    (weakCont_flux_aestronglyMeasurable letters X0 δ κ a b Uw i S hS) wt hwc hw1 A hA0 hA hwt
    Bd hBd hΨv hΨg
    (fun n => weakCont_component_pairing hD G hG letters X0 δ κ a b hab v hv C hCpos hC C' hC' M
      hb f U Uw hsol i e m hm g ψ ψw hψ n (S n) (hSl n) (hS n))

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the full-field bound on rough data, the core

`rff_core`: the full-field bound for a chain with finite moment norm, from the bound `A` on
compact data at the capped slots and weak continuity at the capped slots. Compact approximants
`φ_k` of the datum (`compactDensity`) and their chains (`exists_compactChain_capped`); the
endpoints `V_k` at order `K_f` are Cauchy in `PlaneHk` (the difference of two compact chains is a
compact chain, and the term `β = 0` of the output norm controls each jet in `L²`); weak
continuity, applied to the difference of the rough chain and a compact one, identifies the limit
with the endpoint `T` of the rough chain; Fatou along an almost everywhere convergent
subsequence. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- **The full-field bound on rough data**, with the compact bound `A` and weak continuity at the
capped slots as hypotheses. -/
theorem rff_core {K : ScalarConstants} {g₁ : ℝ} (hg₁ : g₁ ≤ 1 / 4)
    {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw H J Kf m : ℕ} {d Ks : Fin Nw → ℕ} {pos : Fin Nw → Bool} {π : ι → ℝ}
    {letters : Fin Nw → CycleLetter ι h D}
    (hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
      (letters i).positive = pos i)
    {η S ηg rstar t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ}
    {reg : BlockRegions} (pkg : ScalarPackage K η G v t₀ S ϖ reg)
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg)
    (hJ : wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d ≤ J) (X₀ : Vec 2)
    (hrstar : 0 < rstar)
    {κ : Fin (Nw + 1) → ι → ℕ} (hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x) (hκ : IsWordSlots letters κ)
    {f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)}
    {u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hfin : momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤)
    (hch : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
      (fun _ _ _ => 0) u w)
    {A : ℝ≥0∞} (hAtop : A ≠ ⊤)
    (hCb : ∀ (fk : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x))
      (uk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x) (h x))
      (wk : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (cappedWordSlots κ Kf d j x + 1) (h x)),
      IsCompactDatum fk →
      IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kf d) t₀ (t₀ + S) v
        fk (fun _ _ _ => 0) uk wk →
      jetOutputNorm π m Kf ϖ rstar
          (fun x a wd z => planeJetOrder (uk (Fin.last Nw) x (t₀ + S)) a wd z) ≤
        A * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (fk x)))
    (hWb : ∀ Φ : ∀ x, Vec 2 → h x,
      (∀ x, ContDiff ℝ (⊤ : ℕ∞) (Φ x) ∧ HasCompactSupport (Φ x)) →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : ∀ x, PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x))
        (u' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kf d j x) (h x))
        (w' : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (cappedWordSlots κ Kf d j x + 1) (h x)),
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f' x)) < ⊤ →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (cappedWordSlots κ Kf d) t₀ (t₀ + S)
          v f' (fun _ _ _ => 0) u' w' →
        ENNReal.ofReal |∑ x, (π x)⁻¹ *
            ∫ z, inner ℝ (planeValue (u' (Fin.last Nw) x (t₀ + S)) z) (Φ x z)| ≤
          ENNReal.ofReal C * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f' x))) :
    jetOutputNorm π m Kf ϖ rstar
        (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z) ≤
      A * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) := by
  classical
  have hπ : ∀ x, 0 < π x := hB.hπ
  have hd : ∀ i, (letters i).order = d i := fun i => (hletters i).1
  have hle : ∀ j x, cappedWordSlots κ Kf d j x ≤ κ j x := cappedWordSlots_le_original κ Kf d
  have hW' : IsWordSlots letters (cappedWordSlots κ Kf d) :=
    cappedWordSlots_isWordSlots hB.hlet hd hκ Kf
  have hcapf : ∀ x, Kf ≤ cappedWordSlots κ Kf d (Fin.last Nw) x :=
    fun x => (cappedWordSlots_last κ Kf d x (hκf x)).ge
  have hFm : ∀ x, AEStronglyMeasurable (planeValue (f x)) volume :=
    fun x => planeJetOrder_aestronglyMeasurable (f x) 0 _
  -- compact approximants and their chains
  obtain ⟨φs, hφs, hconv⟩ := compactDensity.{u, v}.2 (fun x => planeValue (f x)) hFm
  have hconvN := hconv π (wordReserveN m Ks) ϖ hfin
  have hlift : ∀ k x, ∃ fk : PlaneHk Set.univ (cappedWordSlots κ Kf d 0 x) (h x),
      planeValue fk =ᵐ[volume] φs k x :=
    fun k x => compactDensity.{u, v}.1 _ (φs k x) (hφs k x).1 (hφs k x).2
  choose fk hfk using hlift
  have hcd : ∀ k, IsCompactDatum (fk k) := fun k x => ⟨φs k x, (hφs k x).1, (hφs k x).2, hfk k x⟩
  have hex := fun k => exists_compactChain_capped hg₁ hletters pkg hB hJ X₀ hκf hκ (fk k) (hcd k)
  choose uk wk huk using hex
  have hfkm : ∀ k, momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (fk k x)) =
      momentNorm π (wordReserveN m Ks) ϖ (φs k) :=
    fun k => momentNorm_congr_ae' _ _ _ fun x => hfk k x
  -- the endpoints at order `K_f`
  let V : ℕ → ∀ x, PlaneHk Set.univ Kf (h x) := fun k x =>
    truncatePlaneHk (hcapf x) (uk k (Fin.last Nw) x (t₀ + S))
  let T : ∀ x, PlaneHk Set.univ Kf (h x) := fun x =>
    truncatePlaneHk (hκf x) (u (Fin.last Nw) x (t₀ + S))
  have hVjet : ∀ k x a (wd : DerivativeWord2 a), a ≤ Kf →
      planeJetOrder (V k x) a wd = planeJetOrder (uk k (Fin.last Nw) x (t₀ + S)) a wd :=
    fun k x a wd ha => planeJetOrder_truncate (hcapf x) ha _ wd
  have hTjet : ∀ x a (wd : DerivativeWord2 a), a ≤ Kf →
      planeJetOrder (T x) a wd = planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd :=
    fun x a wd ha => planeJetOrder_truncate (hκf x) ha _ wd
  -- the compact bound
  have hbound : ∀ k, jetOutputNorm π m Kf ϖ rstar
      (fun x a wd z => planeJetOrder (V k x) a wd z) ≤
      A * momentNorm π (wordReserveN m Ks) ϖ (φs k) := by
    intro k
    rw [jetOutputNorm_congr_ae π m Kf ϖ rstar
      (J' := fun x a wd z => planeJetOrder (uk k (Fin.last Nw) x (t₀ + S)) a wd z)
      fun x a wd ha => Filter.Eventually.of_forall fun z => congrFun (hVjet k x a wd ha) z,
      ← hfkm k]
    exact hCb (fk k) (uk k) (wk k) (hcd k) (huk k)
  -- two compact chains
  have hdiffV : ∀ k l, jetOutputNorm π m Kf ϖ rstar
      (fun x a wd z => planeJetOrder (V k x - V l x) a wd z) ≤
      A * momentNorm π (wordReserveN m Ks) ϖ (fun x z => φs k x z - φs l x z) := by
    intro k l
    have hchkl := isPlaneChain_trunc_sub hB.hD G letters X₀ (ϖ * ηg) t₀ (t₀ + S) v
      (cappedWordSlots κ Kf d) (cappedWordSlots κ Kf d) (fun _ _ => le_rfl) hW' hW'
      (fk k) (uk k) (wk k) (fk l) (uk l) (wk l) (huk k) (huk l)
    have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (le_refl _) (fk k x) +
        (-1 : ℝ) • fk l x) =ᵐ[volume] fun z => φs k x z - φs l x z := by
      intro x
      filter_upwards [planeJetOrder_trunc_sub_ae (le_refl _) (fk k x) (fk l x) (Nat.zero_le _)
        (fun i => i.elim0), hfk k x, hfk l x] with z h1 h2 h3
      rw [planeValue, h1]
      change planeValue (fk k x) z - planeValue (fk l x) z = _
      rw [h2, h3]
    have hcdkl : IsCompactDatum (fun x => (1 : ℝ) • truncatePlaneHk (le_refl _) (fk k x) +
        (-1 : ℝ) • fk l x) := fun x =>
      ⟨fun z => φs k x z - φs l x z, (hφs k x).1.sub (hφs l x).1,
        (hφs k x).2.sub (hφs l x).2, hval x⟩
    have hb := hCb _ _ _ hcdkl hchkl
    rw [momentNorm_congr_ae' _ _ _ hval] at hb
    refine le_trans (le_of_eq ?_) hb
    refine jetOutputNorm_congr_ae π m Kf ϖ rstar fun x a wd ha => ?_
    have haK : a ≤ cappedWordSlots κ Kf d (Fin.last Nw) x := ha.trans (hcapf x)
    filter_upwards [planeJetOrder_sub_ae ha (V k x) (V l x) wd,
      planeJetOrder_trunc_sub_ae (le_refl _) (uk k (Fin.last Nw) x (t₀ + S))
        (uk l (Fin.last Nw) x (t₀ + S)) haK wd] with z h1 h2
    rw [h1, h2, hVjet k x a wd ha, hVjet l x a wd ha]
  -- the approximants in the moment norm
  set e : ℕ → ℝ≥0∞ := fun k =>
    momentNorm π (wordReserveN m Ks) ϖ (fun x z => planeValue (f x) z - φs k x z) with hedef
  have hmn : ∀ k l, momentNorm π (wordReserveN m Ks) ϖ (fun x z => φs k x z - φs l x z) ≤
      e k + e l := by
    intro k l
    have he : (fun x z => φs k x z - φs l x z) = fun x z =>
        (planeValue (f x) z - φs l x z) + (φs k x z - planeValue (f x) z) := by
      funext x z
      abel
    rw [he, add_comm (e k)]
    refine (momentNorm_add_le π _ ϖ _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    exact momentNorm_sub_comm π _ ϖ (φs k) (fun x => planeValue (f x))
  -- Cauchy, and the limit
  have hcauchy : ∀ x, CauchySeq fun k => V k x := by
    intro x
    refine rff_cauchySeq (fun k => V k x)
      (fun i => ENNReal.ofReal (i.1.val.factorial * Real.sqrt (π x) / rstar ^ i.1.val) * A)
      (fun i => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop) e hconvN fun k l i => ?_
    have hi : i.1.val ≤ Kf := Nat.lt_succ_iff.1 i.1.isLt
    refine (rff_eLpNorm_jet_le π m Kf ϖ rstar hrstar
      (fun x a wd z => planeJetOrder (V k x - V l x) a wd z) x (hπ x) hi i.2
      (planeJetOrder_aestronglyMeasurable _ _ _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_right ((hdiffV k l).trans (mul_le_mul_right (hmn k l) _)) _
  have hlimit : ∀ x, ∃ L, Tendsto (fun k => V k x) atTop (𝓝 L) :=
    fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  choose L hL using hlimit
  -- the pairing of the value with a test
  have hpair : ∀ x (Φ : Vec 2 → h x), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Tendsto (fun k => ∫ z, inner ℝ (planeValue (V k x - T x) z) (Φ z)) atTop (𝓝 0) := by
    intro x Φ hΦ hΦc
    let Φ' : ∀ x', Vec 2 → h x' := Pi.single x Φ
    have hΦ' : ∀ x', ContDiff ℝ (⊤ : ℕ∞) (Φ' x') ∧ HasCompactSupport (Φ' x') := by
      intro x'
      by_cases hx : x' = x
      · subst hx
        simp only [Φ', Pi.single_eq_same]
        exact ⟨hΦ, hΦc⟩
      · simp only [Φ', Pi.single_eq_of_ne hx]
        exact ⟨contDiff_zero_fun, HasCompactSupport.zero⟩
    obtain ⟨CΦ, hCΦ, hWΦ⟩ := hWb Φ' hΦ'
    have hk : ∀ k, e k < ⊤ →
        |(π x)⁻¹ * ∫ z, inner ℝ (planeValue (V k x - T x) z) (Φ z)| ≤ CΦ * (e k).toReal := by
      intro k hk
      have hdiff := isPlaneChain_trunc_sub hB.hD G letters X₀ (ϖ * ηg) t₀ (t₀ + S) v κ
        (cappedWordSlots κ Kf d) hle hκ hW' f u w (fk k) (uk k) (wk k) hch (huk k)
      have hval : ∀ x, planeValue ((1 : ℝ) • truncatePlaneHk (hle 0 x) (f x) + (-1 : ℝ) • fk k x)
          =ᵐ[volume] fun z => planeValue (f x) z - φs k x z := by
        intro x
        filter_upwards [planeJetOrder_trunc_sub_ae (hle 0 x) (f x) (fk k x) (Nat.zero_le _)
          (fun i => i.elim0), hfk k x] with z h1 h2
        rw [planeValue, h1]
        change planeValue (f x) z - planeValue (fk k x) z = _
        rw [h2]
      have hm'' := momentNorm_congr_ae' π (wordReserveN m Ks) ϖ hval
      have hb := hWΦ _ _ _ (by rw [hm'']; exact hk) hdiff
      rw [hm''] at hb
      have hsum : ∀ (P : ∀ x', PlaneHk Set.univ (cappedWordSlots κ Kf d (Fin.last Nw) x') (h x')),
          ∑ x', (π x')⁻¹ * ∫ z, inner ℝ (planeValue (P x') z) (Φ' x' z) =
            (π x)⁻¹ * ∫ z, inner ℝ (planeValue (P x) z) (Φ z) := by
        intro P
        rw [Finset.sum_eq_single x]
        · simp only [Φ', Pi.single_eq_same]
        · intro x' _ hx
          simp only [Φ', Pi.single_eq_of_ne hx, Pi.zero_apply, inner_zero_right, integral_zero,
            mul_zero]
        · intro hx
          exact absurd (Finset.mem_univ x) hx
      rw [hsum (fun x' => (1 : ℝ) • truncatePlaneHk (hle (Fin.last Nw) x')
        (u (Fin.last Nw) x' (t₀ + S)) + (-1 : ℝ) • uk k (Fin.last Nw) x' (t₀ + S))] at hb
      have hint : ∫ z, inner ℝ (planeValue (V k x - T x) z) (Φ z) =
          -∫ z, inner ℝ (planeValue ((1 : ℝ) • truncatePlaneHk (hle (Fin.last Nw) x)
            (u (Fin.last Nw) x (t₀ + S)) + (-1 : ℝ) • uk k (Fin.last Nw) x (t₀ + S)) z)
            (Φ z) := by
        rw [← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [planeJetOrder_sub_ae (Nat.zero_le Kf) (V k x) (T x) (fun i => i.elim0),
          planeJetOrder_trunc_sub_ae (hle (Fin.last Nw) x) (u (Fin.last Nw) x (t₀ + S))
            (uk k (Fin.last Nw) x (t₀ + S)) (Nat.zero_le _) (fun i => i.elim0)] with z h1 h2
        change inner ℝ (planeJetOrder (V k x - T x) 0 (fun i => i.elim0) z) (Φ z) =
          -inner ℝ (planeJetOrder ((1 : ℝ) • truncatePlaneHk (hle (Fin.last Nw) x)
            (u (Fin.last Nw) x (t₀ + S)) + (-1 : ℝ) • uk k (Fin.last Nw) x (t₀ + S)) 0
              (fun i => i.elim0) z) (Φ z)
        rw [h1, h2, ← inner_neg_left, neg_sub, hVjet k x 0 _ (Nat.zero_le _),
          hTjet x 0 _ (Nat.zero_le _)]
      rw [hint, mul_neg, abs_neg]
      have hne : ENNReal.ofReal CΦ * e k ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hk.ne
      rw [ENNReal.ofReal_le_iff_le_toReal hne, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hCΦ] at hb
      exact hb
    have he0 : Tendsto (fun k => CΦ * (e k).toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvN).const_mul CΦ
    have habs : Tendsto (fun k => |(π x)⁻¹ * ∫ z, inner ℝ (planeValue (V k x - T x) z) (Φ z)|)
        atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun k => abs_nonneg _) ?_ he0
      filter_upwards [hconvN.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with k hk'
      exact hk k hk'
    have h1 := ((tendsto_zero_iff_abs_tendsto_zero _).2 habs).const_mul (π x)
    simp only [mul_zero, ← mul_assoc, mul_inv_cancel₀ (hπ x).ne', one_mul] at h1
    exact h1
  have hLT : ∀ x, L x = T x := fun x => rff_eq_of_pairing_tendsto (hL x) (hpair x)
  -- Fatou
  have hlim := rff_limit_le π m Kf ϖ rstar V T (fun x => hLT x ▸ hL x)
    (fun k => A * momentNorm π (wordReserveN m Ks) ϖ (φs k))
    (A * momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)))
    (ENNReal.Tendsto.const_mul (momentNorm_tendsto π _ ϖ _ φs hfin hconvN) (Or.inr hAtop))
    hbound
  refine le_trans (le_of_eq ?_) hlim
  exact jetOutputNorm_congr_ae π m Kf ϖ rstar fun x a wd ha =>
    Filter.Eventually.of_forall fun z => (congrFun (hTjet x a wd ha) z).symm

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
open Finset
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # `ℓ²` operator bounds of block-triangular matrices

`l2_transpose_bound`: a bound for the conjugate transpose gives the same bound for the matrix.
`blockTriangular_op_bound`: a strictly block-triangular matrix (blocks the level sets of `st`)
whose blocks have operator norm at most `β` has operator norm at most `(M + 1) β`, `M` the top
level. -/

theorem l2_transpose_bound {I J : Type*} (s : Finset I) (s' : Finset J) (A : I → J → ℂ)
    {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ a : I → ℂ, ∑ j ∈ s', ‖∑ i ∈ s, (starRingEnd ℂ) (A i j) * a i‖ ^ 2 ≤
      β ^ 2 * ∑ i ∈ s, ‖a i‖ ^ 2)
    (w : J → ℂ) :
    ∑ i ∈ s, ‖∑ j ∈ s', A i j * w j‖ ^ 2 ≤ β ^ 2 * ∑ j ∈ s', ‖w j‖ ^ 2 := by
  classical
  set v : I → ℂ := fun i => ∑ j ∈ s', A i j * w j with hv
  set N2 : ℝ := ∑ i ∈ s, ‖v i‖ ^ 2 with hN2
  have hN0 : 0 ≤ N2 := sum_nonneg fun _ _ => sq_nonneg _
  set u : J → ℂ := fun j => ∑ i ∈ s, (starRingEnd ℂ) (A i j) * v i with hu
  have hu2 : ∑ j ∈ s', ‖u j‖ ^ 2 ≤ β ^ 2 * N2 := h v
  have hZ : (N2 : ℂ) = ∑ j ∈ s', w j * (starRingEnd ℂ) (u j) := by
    have step : ∀ j, w j * (starRingEnd ℂ) (u j) =
        ∑ i ∈ s, (starRingEnd ℂ) (v i) * (A i j * w j) := by
      intro j
      simp only [hu, map_sum, map_mul, Complex.conj_conj]
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    simp_rw [step]
    rw [sum_comm]
    rw [hN2]; push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum, ← Complex.conj_mul' (v i)]
  have hle : N2 ≤ Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2) * Real.sqrt (∑ j ∈ s', ‖u j‖ ^ 2) := by
    have h1 : (N2 : ℝ) = ‖(N2 : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hN0]
    rw [h1, hZ]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ s', ‖w j * (starRingEnd ℂ) (u j)‖ = ∑ j ∈ s', ‖w j‖ * ‖u j‖ := by
          simp
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hu' : Real.sqrt (∑ j ∈ s', ‖u j‖ ^ 2) ≤ β * Real.sqrt N2 := by
    rw [← Real.sqrt_sq hβ, ← Real.sqrt_mul (sq_nonneg β)]
    exact Real.sqrt_le_sqrt hu2
  by_cases h0 : N2 = 0
  · rw [h0] at hN2
    show N2 ≤ _
    rw [h0]; positivity
  · have hp : 0 < Real.sqrt N2 := Real.sqrt_pos.2 (lt_of_le_of_ne hN0 (Ne.symm h0))
    have h2 : Real.sqrt N2 ≤ β * Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2) := by
      have : Real.sqrt N2 * Real.sqrt N2 ≤ Real.sqrt N2 * (β * Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2)) := by
        rw [Real.mul_self_sqrt hN0]
        calc N2 ≤ Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2) * Real.sqrt (∑ j ∈ s', ‖u j‖ ^ 2) := hle
          _ ≤ Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2) * (β * Real.sqrt N2) :=
            mul_le_mul_of_nonneg_left hu' (Real.sqrt_nonneg _)
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hp
    calc N2 = Real.sqrt N2 ^ 2 := (Real.sq_sqrt hN0).symm
      _ ≤ (β * Real.sqrt (∑ j ∈ s', ‖w j‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]

/-- Convexity: the squared `ℓ²` norm of a sum of `K` vectors is at most `K` times the sum of the
squared norms. -/
theorem sum_norm_sq_le_card {I K : Type*} (s : Finset I) (Kf : Finset K) (y : K → I → ℂ) :
    ∑ i ∈ s, ‖∑ k ∈ Kf, y k i‖ ^ 2 ≤ Kf.card * ∑ k ∈ Kf, ∑ i ∈ s, ‖y k i‖ ^ 2 := by
  classical
  calc ∑ i ∈ s, ‖∑ k ∈ Kf, y k i‖ ^ 2 ≤ ∑ i ∈ s, (Kf.card * ∑ k ∈ Kf, ‖y k i‖ ^ 2) := by
        refine sum_le_sum fun i _ => ?_
        calc ‖∑ k ∈ Kf, y k i‖ ^ 2 ≤ (∑ k ∈ Kf, ‖y k i‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
          _ ≤ _ := sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [← mul_sum, sum_comm]

theorem blockTriangular_op_bound {I : Type*} [Fintype I] (st : I → ℕ) {Mst : ℕ}
    (hst : ∀ i, st i ≤ Mst) (τ : I → I → ℂ) (hT0 : ∀ i i', ¬ st i' < st i → τ i i' = 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (hblk : ∀ k k', k' < k → ∀ a : I → ℂ,
      ∑ i' ∈ univ.filter (fun i' => st i' = k'),
        ‖∑ i ∈ univ.filter (fun i => st i = k), (starRingEnd ℂ) (τ i i') * a i‖ ^ 2 ≤
      β ^ 2 * ∑ i ∈ univ.filter (fun i => st i = k), ‖a i‖ ^ 2)
    (w : I → ℂ) :
    ∑ i, ‖∑ i', τ i i' * w i'‖ ^ 2 ≤ (((Mst + 1) ^ 2) * β) ^ 2 * ∑ i', ‖w i'‖ ^ 2 := by
  classical
  set Ω : ℝ := ∑ i', ‖w i'‖ ^ 2 with hΩ
  have hΩ0 : 0 ≤ Ω := sum_nonneg fun _ _ => sq_nonneg _
  have hlev : ∀ k, ∑ i ∈ univ.filter (fun i => st i = k), ‖∑ i', τ i i' * w i'‖ ^ 2 ≤
      k * (k * (β ^ 2 * Ω)) := by
    intro k
    have hv : ∀ i ∈ univ.filter (fun i => st i = k), ∑ i', τ i i' * w i' =
        ∑ k' ∈ range k, ∑ i' ∈ univ.filter (fun i' => st i' = k'), τ i i' * w i' := by
      intro i hi
      have hik : st i = k := (mem_filter.1 hi).2
      exact sum_eq_sum_stages st k (fun i' => τ i i' * w i') (fun i' hi' => by
        rw [hT0 i i' (by omega), zero_mul])
    calc ∑ i ∈ univ.filter (fun i => st i = k), ‖∑ i', τ i i' * w i'‖ ^ 2
        = ∑ i ∈ univ.filter (fun i => st i = k), ‖∑ k' ∈ range k,
            ∑ i' ∈ univ.filter (fun i' => st i' = k'), τ i i' * w i'‖ ^ 2 :=
          sum_congr rfl fun i hi => by rw [hv i hi]
      _ ≤ (range k).card * ∑ k' ∈ range k, ∑ i ∈ univ.filter (fun i => st i = k),
            ‖∑ i' ∈ univ.filter (fun i' => st i' = k'), τ i i' * w i'‖ ^ 2 :=
          sum_norm_sq_le_card (univ.filter (fun i => st i = k)) (range k)
            (fun k' i => ∑ i' ∈ univ.filter (fun i' => st i' = k'), τ i i' * w i')
      _ ≤ k * ∑ _k' ∈ range k, β ^ 2 * Ω := by
          rw [card_range]
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k' hk' => ?_) (Nat.cast_nonneg _)
          refine (l2_transpose_bound (univ.filter (fun i => st i = k))
            (univ.filter (fun i' => st i' = k')) τ hβ (hblk k k' (mem_range.1 hk')) w).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
      _ = k * (k * (β ^ 2 * Ω)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
  have hsplit : ∑ i, ‖∑ i', τ i i' * w i'‖ ^ 2 = ∑ k ∈ range (Mst + 1),
      ∑ i ∈ univ.filter (fun i => st i = k), ‖∑ i', τ i i' * w i'‖ ^ 2 :=
    (sum_fiberwise_of_maps_to (s := univ) (t := range (Mst + 1)) (g := st)
      (fun i _ => mem_range.2 (Nat.lt_succ_of_le (hst i))) (fun i => ‖∑ i', τ i i' * w i'‖ ^ 2)).symm
  rw [hsplit]
  calc ∑ k ∈ range (Mst + 1), ∑ i ∈ univ.filter (fun i => st i = k), ‖∑ i', τ i i' * w i'‖ ^ 2
      ≤ ∑ _k ∈ range (Mst + 1), ((Mst : ℝ) * ((Mst : ℝ) * (β ^ 2 * Ω))) := by
        refine sum_le_sum fun k hk => (hlev k).trans ?_
        have hk' : (k : ℝ) ≤ Mst := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hk)
        have : 0 ≤ β ^ 2 * Ω := by positivity
        calc (k : ℝ) * ((k : ℝ) * (β ^ 2 * Ω)) ≤ (Mst : ℝ) * ((k : ℝ) * (β ^ 2 * Ω)) :=
              mul_le_mul_of_nonneg_right hk' (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk' this) (Nat.cast_nonneg _)
    _ = ((Mst : ℝ) + 1) * ((Mst : ℝ) * ((Mst : ℝ) * (β ^ 2 * Ω))) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ _ := by
        have h0 : 0 ≤ β ^ 2 * Ω := by positivity
        have hM : (0 : ℝ) ≤ Mst := Nat.cast_nonneg _
        have : ((Mst : ℝ) + 1) * ((Mst : ℝ) * (Mst : ℝ)) ≤ (((Mst : ℝ) + 1) ^ 2) ^ 2 := by nlinarith
        calc ((Mst : ℝ) + 1) * ((Mst : ℝ) * ((Mst : ℝ) * (β ^ 2 * Ω)))
            = (((Mst : ℝ) + 1) * ((Mst : ℝ) * (Mst : ℝ))) * (β ^ 2 * Ω) := by ring
          _ ≤ ((((Mst : ℝ) + 1) ^ 2) ^ 2) * (β ^ 2 * Ω) := mul_le_mul_of_nonneg_right this h0
          _ = _ := by ring

end AVRegularity.CycleWords.Discard
end
end
