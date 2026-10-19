-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.GaugeJetsCore
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
public import AVRegularity.CycleWords.MixedWords.JetToValueStep
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! **Smallness-free Galerkin limit of the reduced transverse equation**.

For the finite transverse systems (no scalar `κ`) with data `cellGalerkinL2Initial N u₀`:

* the window bounds at every order `K` from `transverseRegGalerkin_energy`:
  `‖lift_K y(d)‖² ≤ e^{Γ_K (d - c)} ‖lift_K y(c)‖²` and
  `∫_c^d ‖lift_{K+1} y‖² ≤ 2 e^{Γ_K (d - c)} ‖lift_K y(c)‖²`;
* the `L²` trace and Bochner `H¹` bounds, hence `CellScalarMultiplierLimitData` with no smallness;
* uniqueness of weak solutions with the growth `264 |θ|² + 1 + (C_w |ξ|)²` (no smallness);
* `transverseReg_transfer`: a bound `‖w_N‖² ≤ C` on `H^K` representatives of
  `y_N(t) - c` for every Galerkin solution passes to the given weak solution `u(t) - c`.

For `ξ = 0` the growth constants reduce to the scalar part, and for `K = 0` this is the `L²`
energy. The case `a = b` is excluded from the transfer (`a < b`, since the trace of a weak limit
needs a window). -/

/-- Abstract exponential absorption of a weighted energy inequality. -/
theorem transverseReg_exp_split {Γ s X I Y : ℝ} (hX : 0 ≤ X) (hI : 0 ≤ I)
    (h : Real.exp (-Γ * s) * X + Real.exp (-Γ * s) * ((1 / 2) * I) ≤ Y) :
    X ≤ Real.exp (Γ * s) * Y ∧ I ≤ 2 * Real.exp (Γ * s) * Y := by
  have hEe : Real.exp (Γ * s) * Real.exp (-Γ * s) = 1 := by
    rw [← Real.exp_add, show Γ * s + -Γ * s = 0 by ring, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (Γ * s)).le
  have h3 : Real.exp (Γ * s) * (Real.exp (-Γ * s) * X + Real.exp (-Γ * s) * ((1 / 2) * I)) =
      X + (1 / 2) * I := by
    linear_combination (X + (1 / 2) * I) * hEe
  constructor <;> linarith

/-- The finite transverse system (no scalar `κ`) has strong time regularity. -/
theorem transverseRegGalerkin_strongTime (N : ℕ) {a b η : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (initial : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 initial a b (extendCurve hab y)) :
    StrongTimeRegularity a b (extendCurve hab y) (fun t =>
      (Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0) t
        (extendCurve hab y t)) := by
  obtain ⟨M, hM, hAm, hAb⟩ := cellTransverseGalerkin_window_operator_data
    N G hG hv ξ hc A hA hb 0 MemLp.zero 0 (fun _ => by simp)
  have hr := linearRhs_memLp (a := a) (b := b) _ hAm M hM hAb (extendCurve hab y)
    (continuous_extendCurve hab y).continuousOn 0 MemLp.zero
  have hint : IntervalIntegrable (linearRhs ((Icc a b).indicator
      (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0)) 0 (extendCurve hab y))
      volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    have hi : IntegrableOn (linearRhs ((Icc a b).indicator
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0)) 0 (extendCurve hab y))
        (Icc a b) := hr.integrable (by norm_num)
    exact hi.mono_set Ioc_subset_Icc_self
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  have hd := hy.ae_hasDerivAt hab hint
  rw [uIcc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hd] with t ht
  intro hti
  simpa only [linearRhs, Pi.zero_apply, add_zero] using ht hti

/-- **Window bounds of the finite transverse system at order `K`**, no smallness: growth of the
order-`K` energy and the integrated order-`K + 1` dissipation. -/
theorem transverseRegGalerkin_window_bounds (K N : ℕ) {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (initial : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 initial a b (extendCurve hab y))
    {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) :
    ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y d)‖ ^ 2 ≤
        Real.exp (transverseRegGamma K ρ Cw J * (d - c)) *
          ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y c)‖ ^ 2 ∧
      (∫ t in c..d, ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2) ≤
        2 * Real.exp (transverseRegGamma K ρ Cw J * (d - c)) *
          ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y c)‖ ^ 2 := by
  have hs := (transverseRegGalerkin_strongTime N hab G hG hv ξ hc A hA hb initial y hy).mono
    (by rw [uIcc_of_le hcd, uIcc_of_le hab]; exact hsub)
  have he := finiteObservable_weighted_energy hcd hs (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) (transverseRegGamma K ρ Cw J) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Set.indicator_of_mem (hsub ht)]
      exact transverseRegGalerkin_energy K N a b η hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J hj
        hc A hA hb t (hsub ht) (extendCurve hab y t))
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l c (hsub ⟨le_rfl, hcd⟩) 0)
  have hΓ := transverseRegGamma_nonneg K ρ Cw hρ J hJ0
  have hg : Continuous (fun t => ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2) :=
    ((cellGalerkinNativeLiftCLM N (K + 1)).continuous.comp (continuous_extendCurve hab y)).norm.pow 2
  have hwt : Continuous (fun t => Real.exp (-transverseRegGamma K ρ Cw J * (t - c)) *
      ((1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
      (continuous_const.mul hg)
  have hmono : (∫ t in c..d, Real.exp (-transverseRegGamma K ρ Cw J * (d - c)) *
      ((1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2)) ≤
      ∫ t in c..d, Real.exp (-transverseRegGamma K ρ Cw J * (t - c)) *
        ((1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hcd
      ((continuous_const.mul (continuous_const.mul hg)).intervalIntegrable _ _)
      (hwt.intervalIntegrable _ _) (fun t ht => ?_)
    have hm := mul_le_mul_of_nonneg_left ht.2 hΓ
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hm]))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hI : 0 ≤ ∫ t in c..d, ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hcd (fun t _ => sq_nonneg _)
  exact transverseReg_exp_split (sq_nonneg _) hI (by linarith only [he, hmono])

/-- The Galerkin data from `L²` initial data start at that projection. -/
theorem transverseRegGalerkin_initial (N : ℕ) {a b η : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (initial : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 initial a b (extendCurve hab y)) :
    extendCurve hab y a = initial := by
  simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩

/-- **`L²` trace bound** of the finite transverse system from `L²` data. -/
theorem transverseRegGalerkin_l2_trace (N : ℕ) {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2) (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 (cellGalerkinL2Initial N u₀) a b (extendCurve hab y))
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖cellGalerkinValue N (extendCurve hab y t)‖ ^ 2 ≤
      Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) * ‖u₀‖ ^ 2 := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l t ht 0)
  have hΓ := transverseRegGamma_nonneg 0 ρ Cw hρ J hJ0
  have hg := (transverseRegGalerkin_window_bounds 0 N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J
    hj hc A hA hb _ y hy ht.1 (Icc_subset_Icc le_rfl ht.2)).1
  rw [cellGalerkinNativeLiftCLM_zero_norm_sq, cellGalerkinNativeLiftCLM_zero_norm_sq,
    transverseRegGalerkin_initial N hab G hv ξ hc A hA hb _ y hy] at hg
  have hi := pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N u₀) 2
  have he : Real.exp (transverseRegGamma 0 ρ Cw J * (t - a)) ≤
      Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith only [ht.2]) hΓ)
  exact hg.trans (mul_le_mul he hi (sq_nonneg _) (Real.exp_pos _).le)

/-- **Bochner `H¹` bound** of the finite transverse system from `L²` data. -/
theorem transverseRegGalerkin_bochner (N : ℕ) {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2) (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 (cellGalerkinL2Initial N u₀) a b (extendCurve hab y)) :
    ∃ h : MemLp (fun t => (extendCurve hab y t).val) 2 (volume.restrict (Icc a b)),
      ‖h.toLp (fun t => (extendCurve hab y t).val)‖ ^ 2 ≤
        2 * Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) * ‖u₀‖ ^ 2 := by
  have hcont : Continuous (fun t => (extendCurve hab y t).val) :=
    (cellGalerkinState (E := ℂ) N).continuous.comp (continuous_extendCurve hab y)
  refine ⟨continuousOn_memLp_Icc _ hcont.continuousOn, ?_⟩
  rw [cellTimeL2_norm_sq_integral, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  have hg : (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N 1 (extendCurve hab y t)‖ ^ 2) ≤
      2 * Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) *
        ‖cellGalerkinNativeLiftCLM N 0 (extendCurve hab y a)‖ ^ 2 :=
    (transverseRegGalerkin_window_bounds 0 N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J
      hj hc A hA hb _ y hy hab subset_rfl).2
  simp only [cellGalerkinNativeLiftCLM_one] at hg
  rw [cellGalerkinNativeLiftCLM_zero_norm_sq,
    transverseRegGalerkin_initial N hab G hv ξ hc A hA hb _ y hy] at hg
  have hi := pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N u₀) 2
  exact hg.trans (mul_le_mul_of_nonneg_left hi
    (mul_nonneg (by norm_num) (Real.exp_pos _).le))

/-- **Smallness-free Galerkin limit data** of the reduced transverse equation. -/
theorem transverseReg_limit_data {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2) :
    Nonempty (CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb 0 u₀) := by
  have hex (N : ℕ) := (cellTransverseGalerkin_existsUnique hab N G hG hv ξ hc A hA hb 0
    MemLp.zero 0 (fun _ => by simp) u₀).exists
  choose y he using hex
  have hbound (N : ℕ) := transverseRegGalerkin_bochner N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw
    hfull J hj hc A hA hb u₀ (y N) (he N).1
  choose hy hyb using hbound
  have hn (N : ℕ) : ‖(hy N).toLp (fun t => (extendCurve hab (y N) t).val)‖ ≤
      2 * Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) * ‖u₀‖ ^ 2 + 1 :=
    cellNorm_le_budget_add_one (hyb N)
  obtain ⟨limit, φ, hφ, hlim⟩ := cellHilbert_weak_subsequence_clm
    (fun N => (hy N).toLp (fun t => (extendCurve hab (y N) t).val)) _ hn
  exact ⟨{
    curve := y
    equation := fun N => (he N).1
    stateLp := hy
    budget := 2 * Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) * ‖u₀‖ ^ 2 + 1
    norm_bound := hn
    limit := limit
    subsequence := φ
    monotone := hφ
    weak := hlim }⟩

/-- The moments of the limit slice follow the weak equation, with no smallness. -/
theorem transverseReg_moment_ae {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2) (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb 0 u₀)
    (z : TorusHk 1 ℂ) : ∀ᵐ t ∂volume.restrict (Icc a b),
      inner ℝ (torusHkValueCLM (D.limit t)) (torusHkValueCLM z) =
        inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
          cellScalarMultiplierForm η Cw hCw G hG hv hw ξ 0 r (D.limit r) z := by
  let E := Real.exp (transverseRegGamma 0 ρ Cw J * (b - a)) * ‖u₀‖ ^ 2
  have hE : 0 ≤ E := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  let F := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := 1))
  let p := fun t => inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
    cellScalarMultiplierForm η Cw hCw G hG hv hw ξ 0 r (D.limit r) z
  let state := fun N t => (extendCurve hab (D.curve N) t).val
  have he (n : ℕ) (t : ℝ) : F (state (D.subsequence n) t) =
      inner ℝ (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
        (torusHkValueCLM z) := by
    change inner ℝ (torusHkValueCLM z)
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t)) = _
    exact real_inner_comm _ _
  have hs : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (F (state (D.subsequence n) t)) ^ 2 ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [he]
    have hi := abs_real_inner_le_norm
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)
    have hh := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
    rw [sq_abs, mul_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (transverseRegGalerkin_l2_trace _ hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J hj hc A hA hb
        u₀ _ (D.equation _) t ht) (sq_nonneg _))
  have hl : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n => F (state (D.subsequence n) t)) atTop (𝓝 (p t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [he, p] using D.moment_primitive_tendsto a b η hab G hv ξ hc A hA hb 0 u₀
      hG Cw hCw hw MemLp.zero 0 (fun _ => by simp) z t ht
  have hm := cellWeak_scalar_moment_identification (fun n => state (D.subsequence n))
    (fun n => D.stateLp (D.subsequence n)) D.limit D.weak F p (E * ‖torusHkValueCLM z‖ ^ 2)
    (mul_nonneg hE (sq_nonneg _)) hs hl
  filter_upwards [hm] with t ht
  exact (real_inner_comm _ _).trans ht

/-- **The limit has a continuous `L²` trace** solving the weak equation from `u₀` (no smallness). -/
theorem transverseReg_continuous_trace {a b η : ℝ} (hab' : a < b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2)
    (D : CellScalarMultiplierLimitData a b η hab'.le G hv ξ hc A hA hb 0 u₀) :
    ∃ U : ContinuousMap (Icc a b) ComplexCellL2,
      CellWeakHilbertCurve a b (extendCurve hab'.le U) D.limit
        (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (D.limit t)) ∧
      extendCurve hab'.le U a = u₀ := by
  have hd : CellWeakTimeData a b D.limit
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (D.limit t)) u₀ := by
    refine ⟨Lp.memLp D.limit, ?_, ?_⟩
    · exact cellScalarMultiplierDual_memLp η Cw hCw G hG hv hw ξ 0 MemLp.zero 0
        (fun _ => by simp) D.limit (Lp.memLp D.limit)
    · intro z
      filter_upwards [transverseReg_moment_ae hab'.le hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J hj
        hc A hA hb u₀ D z] with t ht
      simpa only [cellScalarMultiplierDual_pairing] using ht
  exact hd.exists_hilbert_curve hab'

/-- Energy growth of the reduced dual operator, with no smallness of the frequency. -/
theorem transverseReg_dual_energy_growth (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    2 * inner ℝ (cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t u) u ≤
      (264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 1 + (Cw * fibreNorm ξ) ^ 2) *
        ‖torusHkValueCLM u‖ ^ 2 := by
  let S := -cellScalarCLM Complex.I
    (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM u))
  have hg := cellZeroDrift_generator_scalar_source_energy G hG
    (fun j => (Real.sqrt η : ℂ) * ξ j) 0 t u S
  have hs : ‖S‖ ≤ Cw * fibreNorm ξ * ‖torusHkValueCLM u‖ := by
    dsimp only [S]
    rw [norm_neg, cellScalarCLM_norm, Complex.norm_I, one_mul]
    exact cellFibreDriftCouplingCLM_apply_norm_le η Cw hCw hv hw ξ t (torusHkValueCLM u)
  have hs2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg hCw (fibreNorm_nonneg ξ)) (norm_nonneg _))).mpr hs
  rw [mul_pow] at hs2
  have hd : 0 ≤ (3 / 4 : ℝ) * ∑ j : Fin 2, ‖cellDerivativeCLM j u‖ ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp only [Pi.zero_apply, norm_zero, mul_zero, add_zero] at hg
  rw [cellScalarMultiplierDual, cellDualDerivative_pairing]
  change 2 * (cellGeneratorForm _ hG 0 measurable_const _ t u u + cellSourceFunctional _ S 0 u) ≤ _
  nlinarith only [hg, hs2, hd]

/-- **Uniqueness of weak solutions** of the reduced transverse equation, no smallness. -/
theorem transverseReg_weak_unique {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (ξ : Fin 2 → ℂ)
    (u w : ℝ → ComplexCellL2) (slice slice' : ℝ → TorusHk 1 ℂ)
    (hu : CellWeakHilbertCurve a b u slice
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (slice t)))
    (hw' : CellWeakHilbertCurve a b w slice'
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (slice' t)))
    (hinitial : u a = w a) : ∀ t ∈ Icc a b, u t = w t := by
  apply cellWeakHilbert_unique_of_difference_growth hab hu hw' hinitial
    (264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 1 + (Cw * fibreNorm ξ) ^ 2) (by positivity)
  filter_upwards [hu.agrees, hw'.agrees] with t hut hwt
  rw [← cellScalarMultiplierDual_sub, hut, hwt, ← map_sub]
  exact transverseReg_dual_energy_growth η Cw hCw G hG hv hw ξ t (slice t - slice' t)

/-- **Transfer of Galerkin bounds to the weak solution.** If every finite transverse solution from
`cellGalerkinL2Initial N (u a)` has, at time `t`, an `H^K` representative of `y_N(t) - c` with
square norm at most `C`, then so does the given weak solution: `u(t) - c`. -/
theorem transverseReg_transfer (K : ℕ) {a b η : ℝ} (hab' : a < b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hu : CellWeakHilbertCurve a b u slice
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (slice t)))
    (c : ComplexCellL2) (C : ℝ) (hC : 0 ≤ C) (t : ℝ) (ht : t ∈ Icc a b)
    (hgal : ∀ (N : ℕ) (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N)),
      IsLinearIntegralSolution
        ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
        0 (cellGalerkinL2Initial N (u a)) a b (extendCurve hab'.le y) →
      ∃ w : TorusHk K ℂ, torusHkValueCLM w = cellGalerkinValue N (extendCurve hab'.le y t) - c ∧
        ‖w‖ ^ 2 ≤ C) :
    ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t - c ∧ ‖w‖ ^ 2 ≤ C := by
  obtain ⟨D⟩ := transverseReg_limit_data hab'.le hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J hj
    hc A hA hb (u a)
  obtain ⟨U, hU, hi⟩ := transverseReg_continuous_trace hab' hη0 hη G hG hv ξ ρ hξ Cw hCw hw
    hfull J hj hc A hA hb (u a) D
  have he := transverseReg_weak_unique hab'.le η Cw hCw G hG hv hw ξ (extendCurve hab'.le U) u
    D.limit slice hU hu hi
  choose V hV hVb using fun n =>
    hgal (D.subsequence n) (D.curve (D.subsequence n)) (D.equation (D.subsequence n))
  apply cellHigher_pointwise_square_closure K V (u t - c) C hC hVb
  intro z
  have hm := D.trace_moments_tendsto a b η hab'.le G hv ξ hc A hA hb 0 (u a) hG Cw hCw hw
    MemLp.zero 0 (fun _ => by simp) (extendCurve hab'.le U) hU hi z t ht
  rw [he t ht] at hm
  have hl := hm.sub (tendsto_const_nhds (x := inner ℝ c (torusHkValueCLM z)))
  simpa only [hV, inner_sub_left] using hl

end AVRegularity.CycleWords
end
end

section
/-! **(G): growth of the reduced transverse equation on unit windows**.

`‖u(t)‖_{H^j} ≤ e^{Γ_j} ‖w₀‖_{H^j}` for `a ≤ t ≤ a + 1`, `w₀` an `H^j` representative of `u(a)`,
with `Γ_j = transverseRegGamma j ρ C_w J` (no smallness of `|ξ|`). Galerkin: the order-`j` energy
from the projection of `w₀` (`‖lift_j (P_N w₀)‖ ≤ ‖w₀‖`); then `transverseReg_transfer`.

Also the shared helpers of (G), (S) and (C1): the order-`0` coefficient data of a window and the
passage from a squared bound to a norm bound.

For `a = b` one has `t = a` and `w = w₀`; for `j = 0` this is the `L²` growth `e^{Γ_0}`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.CycleWords

/-- From a squared bound to a norm bound, with a constant at least one. -/
theorem transverseReg_le_of_sq {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 1 ≤ C)
    (h : x ^ 2 ≤ C * y ^ 2) : x ≤ C * y := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  apply (sq_le_sq₀ hx (mul_nonneg hC0 hy)).1
  have hm := mul_nonneg (sub_nonneg.2 hC) (mul_nonneg hC0 (sq_nonneg y))
  have hs : C * y ^ 2 ≤ (C * y) ^ 2 := by linarith only [hm]
  exact h.trans hs

/-- The order-`0` smoothness of a window's drift. -/
theorem transverseRegWindow_contDiff_zero {ρ Cw : ℝ} {J : ℕ → ℝ}
    (W : Assembly.TransverseRegWindow ρ Cw J) : ∀ t ∈ Icc W.a W.b, ContDiff ℝ (0 : ℕ) (W.v t) :=
  fun t ht => (W.hsmooth t ht).of_le (by exact_mod_cast le_top)

/-- The `L²` projection of an `H^j` state has native order-`j` norm at most its `H^j` norm. -/
theorem transverseRegGalerkin_initial_lift_norm_le (j N : ℕ) (w₀ : TorusHk j ℂ) :
    ‖cellGalerkinNativeLiftCLM N j (cellGalerkinL2Initial N (torusHkValueCLM w₀))‖ ≤ ‖w₀‖ := by
  cases j with
  | zero =>
    have he := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
      (cellGalerkinNativeLiftCLM_zero_norm_sq N (cellGalerkinL2Initial N (torusHkValueCLM w₀)))
    rw [he]
    exact (cellGalerkinL2Initial_norm_le N _).trans (PiLp.norm_apply_le w₀.val (valueIndex2 0))
  | succ K =>
    have h := galerkinProj_norm_le (E := ℂ) N w₀
    rw [← cellGalerkinL2Initial_higher_lift (by omega : 1 ≤ K + 1),
      ← cellGalerkinNativeLiftCLM_eq_range] at h
    exact h

/-- **(G) for the finite transverse system**: order-`j` growth on a unit window. -/
theorem transverseRegGalerkin_growth (j N : ℕ) {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (w₀ : TorusHk j ℂ) (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 (cellGalerkinL2Initial N (torusHkValueCLM w₀)) a b (extendCurve hab y))
    (t : ℝ) (ht : t ∈ Icc a b) (ht1 : t ≤ a + 1) :
    ‖cellGalerkinNativeLiftCLM N j (extendCurve hab y t)‖ ^ 2 ≤
      Real.exp (transverseRegGamma j ρ Cw J) * ‖w₀‖ ^ 2 := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l t ht 0)
  have hΓ := transverseRegGamma_nonneg j ρ Cw hρ J hJ0
  have hg := (transverseRegGalerkin_window_bounds j N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull J
    hj hc A hA hb _ y hy ht.1 (Icc_subset_Icc le_rfl ht.2)).1
  rw [transverseRegGalerkin_initial N hab G hv ξ hc A hA hb _ y hy] at hg
  have hi := pow_le_pow_left₀ (norm_nonneg _) (transverseRegGalerkin_initial_lift_norm_le j N w₀) 2
  have he : Real.exp (transverseRegGamma j ρ Cw J * (t - a)) ≤
      Real.exp (transverseRegGamma j ρ Cw J) :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hΓ (by linarith only [ht1]))
  exact hg.trans (mul_le_mul he hi (sq_nonneg _) (Real.exp_pos _).le)

end AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

/-- **(G)**: growth on unit windows with the constant `e^{Γ_j}`. -/
theorem transverseRegGrowth : TransverseRegGrowthStatement := by
  intro j ρ Cw J hρ _ hJ
  have hΓ := transverseRegGamma_nonneg j ρ Cw hρ J hJ
  have hE : 1 ≤ Real.exp (transverseRegGamma j ρ Cw J) := Real.one_le_exp_iff.mpr hΓ
  refine ⟨Real.exp (transverseRegGamma j ρ Cw J), Real.exp_pos _, ?_⟩
  intro W w₀ hw₀ t ht ht1
  rcases eq_or_lt_of_le W.hab with hab | hab'
  · have hta : t = W.a := le_antisymm (ht.2.trans hab.ge) ht.1
    exact ⟨w₀, hw₀.trans (congrArg W.u hta.symm), le_mul_of_one_le_left (norm_nonneg _) hE⟩
  · have hc0 := transverseRegWindow_contDiff_zero W
    obtain ⟨w, hwv, hwb⟩ := transverseReg_transfer j hab' W.hη0 W.hη1 W.G W.hG W.hv W.ξ ρ
      W.hfreq Cw W.hCw W.hw W.hsmooth J W.hjets hc0 _
      (normalizedDriftJetBudget_nonneg 0 (fun l => J l.val) W.ξ (fun l => hJ l.val))
      (normalizedDriftJetBudget_window_bound 0 W.a W.b W.η W.v W.ξ hc0 (fun l => J l.val)
        (fun l t ht x => W.hjets l.val t ht x))
      W.u W.slice W.curve 0 (Real.exp (transverseRegGamma j ρ Cw J) * ‖w₀‖ ^ 2)
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) t ht
      (fun N y hy => ⟨cellGalerkinNativeLiftCLM N j (extendCurve hab'.le y t),
        (cellGalerkinNativeLiftCLM_value N j _).trans (sub_zero _).symm,
        transverseRegGalerkin_growth j N hab'.le W.hη0 W.hη1 W.G W.hG W.hv W.ξ ρ W.hfreq Cw
          W.hCw W.hw W.hsmooth J W.hjets hc0 _ _ _ w₀ y (hw₀ ▸ hy) t ht ht1⟩)
    exact ⟨w, hwv.trans (sub_zero _), transverseReg_le_of_sq (norm_nonneg _) (norm_nonneg _) hE hwb⟩

end AVRegularity.CycleWords.Assembly
end
end
