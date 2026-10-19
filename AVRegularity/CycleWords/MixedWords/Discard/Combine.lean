-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.BlochBridge
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.CycleWords.MixedWords.ZeroAmplitudeWordStep
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # measurability and integration helpers for the Bloch output

Small lemmas used by the assembly of `BlochOutputStatement` from the bridge and the plane
statements: `L²` norms as lintegrals, superadditivity of `∫⁻` over finite sums, measurability of
the jets of `U - μ(D)U`. -/

theorem eLpNorm_two_sq'' (f : Vec 2 → ℝ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ z, ENNReal.ofReal (f z ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun z => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    simp_rw [Finset.sum_insert hi]
    calc _ ≤ ∫⁻ a, f i a ∂μ + ∫⁻ a, ∑ i ∈ s, f i a ∂μ := add_le_add_right ih _
      _ ≤ _ := le_lintegral_add _ _

theorem foldl_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (l : List (Fin 2)) (g : Vec 2 → E)
    (hl : l ≠ []) :
    Measurable (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g) := by
  induction l generalizing g with
  | nil => exact absurd rfl hl
  | cons i t ih =>
    by_cases ht : t = []
    · subst ht
      exact measurable_fderiv_apply_const ℝ g (basisVec i)
    · exact ih _ ht

theorem orderedDerivative_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {a : ℕ} (ha : 1 ≤ a)
    (w : DerivativeWord2 a) (g : Vec 2 → E) : Measurable (orderedDerivative w g) := by
  apply foldl_measurable
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem radius' (μ : Vec 2 → ℝ) (hμc : HasCompactSupport μ) :
    ∃ R : ℝ, ∀ ξ : Vec 2, R ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0 := by
  obtain ⟨R, hR⟩ := hμc.isCompact.isBounded.subset_closedBall (0 : Vec 2)
  refine ⟨2 * |R| + 1, fun ξ hξ => ?_⟩
  by_contra hne
  have hmem : ξ ∈ Metric.closedBall (0 : Vec 2) R :=
    hR (subset_tsupport _ (Function.mem_support.2 hne))
  rw [mem_closedBall_zero_iff] at hmem
  have h0 : |ξ 0| ≤ |R| := by
    have := norm_le_pi_norm ξ 0
    rw [Real.norm_eq_abs] at this
    exact (this.trans hmem).trans (le_abs_self R)
  have h1 : |ξ 1| ≤ |R| := by
    have := norm_le_pi_norm ξ 1
    rw [Real.norm_eq_abs] at this
    exact (this.trans hmem).trans (le_abs_self R)
  have hv : vecDot ξ ξ ≤ (2 * |R|) ^ 2 := by
    unfold vecDot
    simp only [Fin.sum_univ_two]
    have a0 : ξ 0 * ξ 0 ≤ |R| ^ 2 := by
      nlinarith [sq_abs (ξ 0), abs_nonneg (ξ 0), abs_nonneg R]
    have a1 : ξ 1 * ξ 1 ≤ |R| ^ 2 := by
      nlinarith [sq_abs (ξ 1), abs_nonneg (ξ 1), abs_nonneg R]
    nlinarith [abs_nonneg R]
  have := Real.sqrt_le_sqrt hv
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

theorem jetDiff_aestronglyMeasurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (μ : Vec 2 → ℝ)
    (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ) {κ : ℕ} (U : PlaneHk Set.univ κ E)
    (a : ℕ) (w : DerivativeWord2 a) :
    AEStronglyMeasurable (fun z => planeJetOrder U a w z -
      orderedDerivative w (fourierCutoff μ (planeValue U)) z) volume := by
  refine (planeJetOrder_aestronglyMeasurable U a w).sub ?_
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨R, hR⟩ := radius' μ hμc
    have h := (fourierCutoff_memLp_of_memLp μ R hR hμ (planeValue_memLp U)).aestronglyMeasurable
    simpa [orderedDerivative] using h
  · exact (orderedDerivative_measurable ha w _).aestronglyMeasurable

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Discard

/-! # smooth periodic functions are dense in `H^1` of the torus

The Fourier truncations `galerkinProj N z` converge to `z` in `H^1` and have smooth periodic
representatives (`cellGalerkinSmoothValue`). -/

theorem h1Density : H1DensityStatement := by
  intro z
  refine ⟨fun N => galerkinProj (E := ℂ) (K := 1) N z, galerkinProj_tendsto z, fun N => ?_⟩
  let u : CellGalerkinSpace (E := ℂ) N := ⟨galerkinProj (E := ℂ) (K := 1) N z, ⟨z, rfl⟩⟩
  exact ⟨cellGalerkinSmoothValue N u, cellGalerkinSmoothValue_contDiff N u,
    cellGalerkinSmoothValue_periodic N u, cellGalerkinSmoothValue_ae N u⟩

end AVRegularity.CycleWords.Discard
end

section
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # the arithmetic of the positive ladder `b1wPosLadder`

The ladder `n(i)` depends only on the stage order `b1wSt i` (it is a function of the level and of
`|β|`), a same-level step to an earlier stage gains at least one order, a letter step from level
`l + 1` to level `l` gains at least `d_l`, and the ladder is at most `K_f + ∑ d + m + ∑ K_s`. -/

universe u v

section Ladder

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The stage order determines the level and the degree. -/
theorem level_deg_of_st_eq {i i' : B1WIndex ι h Nw m Ks} (hs : b1wSt i = b1wSt i') :
    i.1 = i'.1 ∧ b1wDeg i = b1wDeg i' := by
  unfold b1wSt at hs
  have h1 := i.1.isLt
  have h2 := i'.1.isLt
  have hd : b1wDeg i = b1wDeg i' := by
    have := congrArg (· / (Nw + 1)) hs
    rw [mul_comm (b1wDeg i), mul_comm (b1wDeg i')] at this
    rwa [Nat.mul_add_div (Nat.succ_pos Nw), Nat.mul_add_div (Nat.succ_pos Nw),
      Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2] at this
  refine ⟨Fin.ext ?_, hd⟩
  rw [hd] at hs
  omega

theorem mom_le (i : B1WIndex ι h Nw m Ks) :
    i.2.2.1.1.1 + i.2.2.1.1.2 ≤ b1wLevelMoments m Ks i.1 := by
  have := i.2.2.1.2
  simp only [momentIndices, Finset.mem_filter] at this
  exact this.2

theorem ladder_eq_of_st_eq (Kf : ℕ) (d : Fin Nw → ℕ) {i i' : B1WIndex ι h Nw m Ks}
    (hs : b1wSt i = b1wSt i') : b1wPosLadder Kf d i = b1wPosLadder Kf d i' := by
  obtain ⟨hl, hd⟩ := level_deg_of_st_eq hs
  have e0 : b1wPrefix Ks i.1 = b1wPrefix Ks i'.1 := by rw [hl]
  have hmom : i.2.2.1.1.1 + i.2.2.1.1.2 = i'.2.2.1.1.1 + i'.2.2.1.1.2 := by
    unfold b1wDeg at hd
    omega
  have e1 : (∑ l : Fin Nw, if i.1.val ≤ l.val then d l else 0) =
      ∑ l : Fin Nw, if i'.1.val ≤ l.val then d l else 0 := by rw [hl]
  have e2 : b1wLevelMoments m Ks i.1 = b1wLevelMoments m Ks i'.1 := by rw [hl]
  unfold b1wPosLadder
  omega

theorem ladder_le_top (Kf : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) :
    b1wPosLadder Kf d i ≤ Kf + ∑ l, d l + (m + ∑ l, Ks l) := by
  unfold b1wPosLadder
  have h1 : (∑ l : Fin Nw, if i.1.val ≤ l.val then d l else 0) ≤ ∑ l, d l :=
    Finset.sum_le_sum fun l _ => by split_ifs <;> omega
  have h2 : b1wLevelMoments m Ks i.1 ≤ m + ∑ l, Ks l := by
    unfold b1wLevelMoments
    have : (∑ l : Fin Nw, if i.1.val ≤ l.val then Ks l else 0) ≤ ∑ l, Ks l :=
      Finset.sum_le_sum fun l _ => by split_ifs <;> omega
    omega
  omega

theorem ladder_same (Kf : ℕ) (d : Fin Nw → ℕ) {i i' : B1WIndex ι h Nw m Ks}
    (hl : i'.1 = i.1) (hs : b1wSt i' < b1wSt i) :
    b1wPosLadder Kf d i + 1 ≤ b1wPosLadder Kf d i' := by
  have hdeg : b1wDeg i' < b1wDeg i := by
    unfold b1wSt at hs
    have h1 := i'.1.isLt
    by_contra hc
    push Not at hc
    have h2 : b1wDeg i * (Nw + 1) ≤ b1wDeg i' * (Nw + 1) := Nat.mul_le_mul_right _ hc
    have h3 : i.1.val ≤ i'.1.val := by rw [hl]
    omega
  have e0 : b1wPrefix Ks i'.1 = b1wPrefix Ks i.1 := by rw [hl]
  have hmom : i'.2.2.1.1.1 + i'.2.2.1.1.2 < i.2.2.1.1.1 + i.2.2.1.1.2 := by
    unfold b1wDeg at hdeg
    omega
  have hle := mom_le i
  have e1 : (∑ l : Fin Nw, if i'.1.val ≤ l.val then d l else 0) =
      ∑ l : Fin Nw, if i.1.val ≤ l.val then d l else 0 := by rw [hl]
  have e2 : b1wLevelMoments m Ks i'.1 = b1wLevelMoments m Ks i.1 := by rw [hl]
  unfold b1wPosLadder
  omega

theorem levelSum_castSucc {Nw : ℕ} (d : Fin Nw → ℕ) (l : Fin Nw) :
    (∑ l' : Fin Nw, if l.castSucc.val ≤ l'.val then d l' else 0) =
      (∑ l' : Fin Nw, if l.succ.val ≤ l'.val then d l' else 0) + d l := by
  have : ∀ l' : Fin Nw, (if l.castSucc.val ≤ l'.val then d l' else 0) =
      (if l.succ.val ≤ l'.val then d l' else 0) + (if l' = l then d l' else 0) := by
    intro l'
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases h1 : l.val + 1 ≤ l'.val
    · have : l' ≠ l := fun h => by simp [h] at h1
      simp [h1, this]
      omega
    · by_cases h2 : l' = l
      · subst h2; simp
      · have : ¬ l.val ≤ l'.val := by
          have : l'.val ≠ l.val := fun h => h2 (Fin.ext h)
          omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl fun l' _ => this l', Finset.sum_add_distrib]
  simp

theorem ladder_letter (Kf : ℕ) (d : Fin Nw → ℕ) {i i' : B1WIndex ι h Nw m Ks} (l : Fin Nw)
    (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (hs : b1wSt i' < b1wSt i) :
    b1wPosLadder Kf d i + d l ≤ b1wPosLadder Kf d i' := by
  have hdeg : b1wDeg i' ≤ b1wDeg i := by
    unfold b1wSt at hs
    have h1 := i'.1.isLt
    have h3 : i.1.val = l.val + 1 := by rw [hi]; rfl
    have h4 : i'.1.val = l.val := by rw [hi']; rfl
    by_contra hc
    push Not at hc
    have h2 : (b1wDeg i + 1) * (Nw + 1) ≤ b1wDeg i' * (Nw + 1) := Nat.mul_le_mul_right _ hc
    nlinarith
  have hpre : b1wPrefix Ks i.1 = b1wPrefix Ks i'.1 + Ks l := by
    rw [hi, hi', stageExp_prefix_succ]
  have hlm : b1wLevelMoments m Ks i'.1 = b1wLevelMoments m Ks i.1 + Ks l := by
    rw [hi, hi', stageExp_levelMoments_castSucc]
  have hsum : (∑ l' : Fin Nw, if i'.1.val ≤ l'.val then d l' else 0) =
      (∑ l' : Fin Nw, if i.1.val ≤ l'.val then d l' else 0) + d l := by
    rw [hi, hi']
    exact levelSum_castSucc d l
  have hmom : i'.2.2.1.1.1 + i'.2.2.1.1.2 ≤ i.2.2.1.1.1 + i.2.2.1.1.2 + Ks l := by
    unfold b1wDeg at hdeg
    omega
  have hle := mom_le i
  unfold b1wPosLadder
  omega

end Ladder

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the mode Duhamel equation with a scalar source

`quietFourierS_evolution`: the extension of `quietFourier_evolution` by an `L²` scalar source `S`:
for a weak Hilbert curve with source `S` and flux `F`, each cell Fourier coefficient satisfies the
Duhamel equation with forcing `⟨S, e_n⟩ + i ∑_j y_j ⟨F_j, e_n⟩`. -/

local instance SourceMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The forcing of the mode `n`: `⟨S, e_n⟩ + i ∑_j y_j ⟨F_j, e_n⟩`. -/
def quietModeForcing (θ : Vec 2) (n : Fin 2 → ℤ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    ℂ :=
  cellComplexPair S (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) +
    Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
      cellComplexPair (F j) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))

theorem quietFourier_sourceS (θ : Vec 2) (n : Fin 2 → ℤ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) :
    cellComplexSource (fun k => (θ k : ℂ)) S F (cellComplexFourierModeH1 n) =
      quietModeForcing θ n S F := by
  have h0 := quietFourier_source θ n F
  have h1 : cellComplexSource (fun k => (θ k : ℂ)) S F (cellComplexFourierModeH1 n) =
      cellComplexPair S (torusHkValueCLM (cellComplexFourierModeH1 n)) +
        cellComplexSource (fun k => (θ k : ℂ)) 0 F (cellComplexFourierModeH1 n) := by
    simp only [cellComplexSource, cellComplexPair_zero_left, zero_sub]
    ring
  rw [h1, h0, cellComplexFourierModeH1_value]
  rfl

/-- Each actual weak Fourier coefficient solves its measurable scalar inhomogeneous ODE. -/
theorem quietFourierS_strongTime {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (S : ℝ → ComplexCellL2)
    (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) (n : Fin 2 → ℤ) :
    StrongTimeRegularity a b
      (fun t => cellComplexPair (u t) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)))
      (fun t => quietLam G θ n t *
          cellComplexPair (u t) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) +
        quietModeForcing θ n (S t) (F t)) := by
  have hs := h.complex_test_strongTime hab (cellComplexFourierModeH1 n)
  rw [cellComplexFourierModeH1_value] at hs
  refine ⟨hs.ac, ?_⟩
  have hd := hs.derivative
  rw [uIcc_of_le hab] at hd ⊢
  filter_upwards [hd, h.agrees, ae_restrict_mem measurableSet_Icc] with t ht ha hmem
  rw [cellDualComplexPair_actual, quietFourier_generator G hG hv V hb θ t (hquiet t hmem),
    quietFourier_sourceS, ← ha] at ht
  exact ht

/-- The forcing of each mode is integrable on the closed window. -/
theorem quietModeForcing_integrable {a b : ℝ} (hab : a ≤ b) (θ : Vec 2) (n : Fin 2 → ℤ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => quietModeForcing θ n (S t) (F t)) volume a b := by
  have h1 := quietFourier_forcing_integrable hab θ n F hF
  have h2 : IntervalIntegrable (fun t => cellComplexPair (S t)
      (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))) volume a b := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_
    have he : (fun t => cellComplexPair (S t) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))) =
        ((innerSL ℂ (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))).restrictScalars ℝ) ∘
          (fun t => S t) := by
      funext t
      exact cellComplexPair_eq_inner _ _
    rw [he]
    exact (((innerSL ℂ (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))).restrictScalars ℝ).comp_memLp'
      hS).integrable (by norm_num)
  exact h2.add h1

/-- **The mode Duhamel equation with a scalar source.** -/
theorem quietFourierS_evolution {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (S : ℝ → ComplexCellL2)
    (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) (n : Fin 2 → ℤ) :
    cellComplexPair (u b) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) =
      Complex.exp (∫ t in a..b, quietLam G θ n t) *
        cellComplexPair (u a) (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n)) +
      ∫ t in a..b, Complex.exp (∫ r in t..b, quietLam G θ n r) *
        quietModeForcing θ n (S t) (F t) := by
  apply quietForced_scalar_evolution hab
  · have hi := fibreMetricSymbol_intervalIntegrable 1 G hG
      (fun j => (quietFourierFrequency θ n j : ℂ)) a b
    have he : (fun t => -(1 : ℂ) * fibreQuad (G t)
        (fun j => (quietFourierFrequency θ n j : ℂ))) = quietLam G θ n := by
      funext t
      simp only [neg_one_mul, fibreQuad, quietLam]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Complex.ofReal_one, he] at hi
    exact hi
  · exact quietModeForcing_integrable hab θ n S F hS hF
  · exact quietFourierS_strongTime hab G hG hv V hb θ u slice S F h hquiet n

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # `BlochOutputStatement` from the bridge and the plane statements

`blochOutput_of_parts`: the sums over the frame, the moments, the orders and the components,
and the constants (`ϖ ≤ 1`, `r ≤ C_out`), with the two statements `BridgeStatement` and
`PlaneStatement` as hypotheses. -/

universe u v

/-- The weighted norm of the scaled jets as a lintegral. -/
theorem weighted_sq {ϖ r : ℝ} {β : ℕ × ℕ} {a : ℕ} (S : Vec 2 → ℝ) (hS0 : ∀ z, 0 ≤ S z)
    (hS : AEMeasurable S volume) :
    eLpNorm (fun z : Vec 2 => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * r ^ a) * Real.sqrt (S z)) 2
        volume ^ 2 =
      ENNReal.ofReal ((ϖ ^ (β.1 + β.2) * r ^ a) ^ 2) *
        ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * S z) := by
  have hm : AEStronglyMeasurable
      (fun z : Vec 2 => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * r ^ a) * Real.sqrt (S z)) volume := by
    refine AEStronglyMeasurable.mul ?_ hS.sqrt.aestronglyMeasurable
    exact (by fun_prop : Continuous fun z : Vec 2 => (ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * r ^ a).aestronglyMeasurable
  rw [eLpNorm_two_sq'' _ hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [mul_pow, Real.sq_sqrt (hS0 z)]
  unfold momentWeight
  ring

theorem coef_le {Kf m a : ℕ} {CP Cb ϖ r pi : ℝ}
    (hCP : 0 < CP) (hpi : 0 < pi) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hr : 0 < r) (hrC : r ≤ Cb)
    (hCb : 1 ≤ Cb) (haKf : a ≤ Kf) {β β' : ℕ × ℕ} (hβ : β ∈ momentIndices m)
    (hβ' : β'.1 ≤ β.1 ∧ β'.2 ≤ β.2) :
    pi⁻¹ * (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 * CP ≤
      CP * Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2 *
        (pi⁻¹ * (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) := by
  have hq : β.1 + β.2 ≤ m := by
    have := hβ
    unfold momentIndices at this
    exact (by simpa using this : (β.1 ≤ m ∧ β.2 ≤ m) ∧ β.1 + β.2 ≤ m).2
  have hf1 : (1 : ℝ) ≤ ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hfm : ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) ≤ (m.factorial : ℝ) := by
    have h1 := Nat.factorial_mul_factorial_dvd_factorial_add β'.1 β'.2
    have h2 : (β'.1 + β'.2).factorial ≤ m.factorial :=
      Nat.factorial_le (by omega)
    exact_mod_cast (Nat.le_of_dvd (Nat.factorial_pos _) h1).trans h2
  set f' : ℝ := ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) with hf'
  have hϖp : ϖ ^ (β.1 + β.2) ≤ ϖ ^ (β'.1 + β'.2) :=
    pow_le_pow_of_le_one hϖ.le hϖ1 (by omega)
  have hrp : r ^ a ≤ Cb ^ Kf :=
    (pow_le_pow_left₀ hr.le hrC a).trans (pow_le_pow_right₀ hCb haKf)
  have h0 : (ϖ ^ (β.1 + β.2) * r ^ a) ≤ ϖ ^ (β'.1 + β'.2) * Cb ^ Kf :=
    mul_le_mul hϖp hrp (by positivity) (by positivity)
  have h0' : (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 ≤ (ϖ ^ (β'.1 + β'.2) * Cb ^ Kf) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h0 2
  have hratio : 1 ≤ ((m.factorial : ℝ) / f') ^ 2 := by
    have : 1 ≤ (m.factorial : ℝ) / f' := by
      rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  have key : (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 ≤
      Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2 * (ϖ ^ (β'.1 + β'.2) / f') ^ 2 := by
    calc (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 ≤ (ϖ ^ (β'.1 + β'.2) * Cb ^ Kf) ^ 2 := h0'
      _ = Cb ^ (2 * Kf) * (ϖ ^ (β'.1 + β'.2)) ^ 2 := by ring
      _ ≤ Cb ^ (2 * Kf) * (ϖ ^ (β'.1 + β'.2)) ^ 2 * ((m.factorial : ℝ) / f') ^ 2 :=
          le_mul_of_one_le_right (by positivity) hratio
      _ = _ := by field_simp
  calc pi⁻¹ * (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 * CP
      = (pi⁻¹ * CP) * (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 := by ring
    _ ≤ (pi⁻¹ * CP) * (Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2 * (ϖ ^ (β'.1 + β'.2) / f') ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

theorem term_le (hB : BridgeStatement) {n Kf m a : ℕ} {ρ CP Cb ϖ r pi : ℝ}
    (hCP : 0 < CP) (hpi : 0 < pi) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hr : 0 < r) (hrC : r ≤ Cb)
    (hCb : 1 ≤ Cb) (haKf : a ≤ Kf) {β : ℕ × ℕ} (hβ : β ∈ momentIndices m)
    (S : Vec 2 → ℝ) (hS0 : ∀ z, 0 ≤ S z) (hS : AEMeasurable S volume)
    (g : ℕ × ℕ → Fin n → Vec 2 → ℝ)
    (hint : ∀ β' ∈ momentIndices m, ∀ b, Integrable (g β' b))
    (hplane : ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * S z) ≤ ENNReal.ofReal CP *
      ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin n,
        ∫⁻ ξ, BandIntegrand Kf ρ (g β' b) ξ) :
    ENNReal.ofReal pi⁻¹ * eLpNorm (fun z : Vec 2 =>
        ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * r ^ a) * Real.sqrt (S z)) 2 volume ^ 2 ≤
      ENNReal.ofReal (CP * Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2) *
        ∑ β' ∈ momentIndices m, ∑ b : Fin n,
          ∫⁻ θ in freqCube, ENNReal.ofReal (pi⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (g β' b)) := by
  rw [weighted_sq S hS0 hS]
  have hstep : ENNReal.ofReal pi⁻¹ * (ENNReal.ofReal ((ϖ ^ (β.1 + β.2) * r ^ a) ^ 2) *
      ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * S z)) ≤
      ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin n,
        ENNReal.ofReal (pi⁻¹ * (ϖ ^ (β.1 + β.2) * r ^ a) ^ 2 * CP) *
          ∫⁻ θ in freqCube, cellBandSq Kf ρ θ (planeBlochC θ (g β' b)) := by
    calc _ ≤ ENNReal.ofReal pi⁻¹ * (ENNReal.ofReal ((ϖ ^ (β.1 + β.2) * r ^ a) ^ 2) *
          (ENNReal.ofReal CP * ∑ β' ∈ (momentIndices m).filter
            (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin n,
              ∫⁻ ξ, BandIntegrand Kf ρ (g β' b) ξ)) := by gcongr
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun β' hβ' => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hmem := (Finset.mem_filter.1 hβ').1
        rw [← hB Kf ρ (g β' b) (hint β' hmem b)]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
  refine hstep.trans ?_
  rw [Finset.mul_sum]
  calc _ ≤ ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin n,
        ENNReal.ofReal (CP * Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2) *
          ∫⁻ θ in freqCube, ENNReal.ofReal (pi⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (g β' b)) := by
        refine Finset.sum_le_sum fun β' hβ' => Finset.sum_le_sum fun b _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (coef_le hCP hpi hϖ hϖ1 hr hrC hCb haKf hβ
          (Finset.mem_filter.1 hβ').2)) le_rfl
    _ = ENNReal.ofReal (CP * Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2) *
        ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin n,
          ∫⁻ θ in freqCube, ENNReal.ofReal (pi⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (g β' b)) := by
        simp_rw [← Finset.mul_sum]
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        gcongr
        exact Finset.filter_subset _ _

theorem nested_le {ι : Type*} (sv : Finset ι) (sb : Finset (ℕ × ℕ)) {n : ι → ℕ}
    (f : ∀ v, ℕ × ℕ → Fin (n v) → Vec 2 → ℝ≥0∞) (ν : Measure (Vec 2)) :
    ∑ v ∈ sv, ∑ β ∈ sb, ∑ b : Fin (n v), ∫⁻ θ, f v β b θ ∂ν ≤
      ∫⁻ θ, ∑ v ∈ sv, ∑ β ∈ sb, ∑ b : Fin (n v), f v β b θ ∂ν := by
  refine (Finset.sum_le_sum fun v _ => (Finset.sum_le_sum fun β _ =>
    sum_lintegral_le Finset.univ (fun b θ => f v β b θ))).trans ?_
  refine (Finset.sum_le_sum fun v _ =>
    (sum_lintegral_le sb (fun β θ => ∑ b : Fin (n v), f v β b θ))).trans ?_
  exact sum_lintegral_le sv (fun v θ => ∑ β ∈ sb, ∑ b : Fin (n v), f v β b θ)

theorem blochOutput_of_parts (hB : BridgeStatement) (hP : PlaneStatement.{v}) :
    BlochOutputStatement.{u, v} := by
  intro Kf m Cout ρ Bμ hCout hρ hBμ
  obtain ⟨CP, hCP, hPP⟩ := hP Kf m ρ Bμ hρ hBμ
  set Cb : ℝ := max 1 Cout with hCbdef
  have hCb : 1 ≤ Cb := le_max_left _ _
  set Kc : ℝ := CP * Cb ^ (2 * Kf) * ((m.factorial : ℝ)) ^ 2 with hKc
  have hKc0 : 0 < Kc := by positivity
  have hcard : 0 < (momentIndices m).card := by
    apply Finset.card_pos.2
    refine ⟨(0, 0), ?_⟩
    unfold momentIndices
    simp
  set N : ℕ := (momentIndices m).card * (Kf + 1) with hN
  refine ⟨N * Real.sqrt Kc, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ rstar hϖ hϖ1 hr hrC μ hμ hμc hμe hμB hμ1 κN hκ U hmom
  set T : ℝ≥0∞ := ∫⁻ θ in freqCube, outBandSq π ϖ m Kf ρ θ (fun x => planeValue (U x)) with hT
  have hcore : ∀ β ∈ momentIndices m, ∀ a ∈ Finset.range (Kf + 1),
      (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z : Vec 2 =>
        ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * Real.sqrt (∑ w : DerivativeWord2 a,
          ‖planeJetOrder (U v) a w z -
            orderedDerivative w (fourierCutoff μ (planeValue (U v))) z‖ ^ 2)) 2 volume ^ 2) ≤
        ENNReal.ofReal Kc * T := by
    intro β hβ a ha
    have haKf : a ≤ Kf := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have hrC' : rstar ≤ Cb := hrC.trans (le_max_right _ _)
    have hv : ∀ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z : Vec 2 =>
        ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * Real.sqrt (∑ w : DerivativeWord2 a,
          ‖planeJetOrder (U v) a w z -
            orderedDerivative w (fourierCutoff μ (planeValue (U v))) z‖ ^ 2)) 2 volume ^ 2 ≤
        ENNReal.ofReal Kc * ∑ β' ∈ momentIndices m, ∑ b : Fin (Module.finrank ℝ (h v)),
          ∫⁻ θ in freqCube, ENNReal.ofReal ((π v)⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (fun y => momentWeight β' y *
                inner ℝ (stdOrthonormalBasis ℝ (h v) b) (planeValue (U v) y))) := by
      intro v
      refine term_le hB hCP (hπ v) hϖ hϖ1 hr hrC' hCb haKf hβ _ (fun z => by positivity) ?_
        _ ?_ (hPP (E := h v) μ hμ hμc hμe hμB hμ1 (κN v) (hκ v) (U v) (hmom v) β hβ a haKf)
      · exact Finset.aemeasurable_fun_sum _ fun w _ =>
          ((jetDiff_aestronglyMeasurable μ hμ hμc (U v) a w).norm.aemeasurable.pow_const 2)
      · intro β' hβ' b
        have := (innerSL ℝ (stdOrthonormalBasis ℝ (h v) b)).integrable_comp (hmom v β' hβ')
        refine this.congr (Filter.Eventually.of_forall fun y => ?_)
        simp [momentWeight]
    calc _ ≤ ∑ v, ENNReal.ofReal Kc * ∑ β' ∈ momentIndices m, ∑ b : Fin (Module.finrank ℝ (h v)),
          ∫⁻ θ in freqCube, ENNReal.ofReal ((π v)⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (fun y => momentWeight β' y *
                inner ℝ (stdOrthonormalBasis ℝ (h v) b) (planeValue (U v) y))) :=
          Finset.sum_le_sum fun v _ => hv v
      _ = ENNReal.ofReal Kc * ∑ v, ∑ β' ∈ momentIndices m, ∑ b : Fin (Module.finrank ℝ (h v)),
          ∫⁻ θ in freqCube, ENNReal.ofReal ((π v)⁻¹ *
            (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (fun y => momentWeight β' y *
                inner ℝ (stdOrthonormalBasis ℝ (h v) b) (planeValue (U v) y))) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal Kc * T := by
          refine mul_le_mul' le_rfl ?_
          exact nested_le Finset.univ (momentIndices m)
            (fun v β b θ => ENNReal.ofReal ((π v)⁻¹ *
              (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
              cellBandSq Kf ρ θ (planeBlochC θ (fun y => momentWeight β y *
                inner ℝ (stdOrthonormalBasis ℝ (h v) b) (planeValue (U v) y)))) _
  have hterm : ∀ β ∈ momentIndices m, ∀ a ∈ Finset.range (Kf + 1),
      ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z : Vec 2 =>
          ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 * rstar ^ a) * Real.sqrt (∑ w : DerivativeWord2 a,
            ‖planeJetOrder (U v) a w z -
              orderedDerivative w (fourierCutoff μ (planeValue (U v))) z‖ ^ 2)) 2 volume ^ 2) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Kc) * T ^ (1 / 2 : ℝ) := by
    intro β hβ a ha
    have hc : ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      refine inv_le_one_of_one_le₀ ?_
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 := ENNReal.rpow_le_rpow (hcore β hβ a ha) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_rpow_of_nonneg hKc0.le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow] at h2
    calc _ ≤ 1 * _ := mul_le_mul' hc le_rfl
      _ ≤ _ := by rw [one_mul]; exact h2
  unfold jetOutputNorm
  calc _ ≤ ∑ β ∈ momentIndices m, ∑ a ∈ Finset.range (Kf + 1),
        ENNReal.ofReal (Real.sqrt Kc) * T ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun β hβ => Finset.sum_le_sum fun a ha => hterm β hβ a ha
    _ = ((N : ℝ≥0∞)) * (ENNReal.ofReal (Real.sqrt Kc) * T ^ (1 / 2 : ℝ)) := by
        simp [Finset.sum_const, hN, mul_assoc]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity AVRegularity.CycleWords.Discard
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the derivative of the radian transform (step (a) of `FtCalculusStatement`)

`∂_j ĝ = -i FT(y_j g)` when `g` and `y_j g` are integrable (differentiation under the integral). -/

theorem Ft_hasDerivAt {g : Vec 2 → ℝ} (hg : Integrable g) (j : Fin 2)
    (hgj : Integrable (fun y : Vec 2 => y j * g y)) (ξ : Vec 2) :
    HasDerivAt (fun t : ℝ => planeTransform g (ξ + t • basisVec j))
      (-Complex.I * planeTransform (fun y => y j * g y) ξ) 0 := by
  unfold planeTransform
  have hphase : ∀ (t : ℝ) (y : Vec 2), vecDot (ξ + t • basisVec j) y = vecDot ξ y + t * y j := by
    intro t y
    simp only [vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec]
    fin_cases j <;> simp <;> ring
  have hcont : ∀ t : ℝ, Continuous fun y : Vec 2 =>
      Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) := by
    intro t
    have : Continuous fun y : Vec 2 => vecDot (ξ + t • basisVec j) y := by unfold vecDot; fun_prop
    fun_prop
  have hnorm : ∀ (t : ℝ) (y : Vec 2), ‖Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) *
      (g y : ℂ)‖ = ‖g y‖ := by
    intro t y
    rw [norm_mul, Complex.norm_exp]
    simp
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun y : Vec 2 =>
      Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) * (g y : ℂ)) volume :=
    fun t => (hcont t).aestronglyMeasurable.mul hg.ofReal.aestronglyMeasurable
  have hint0 : Integrable (fun y : Vec 2 =>
      Complex.exp (-(Complex.I * (vecDot (ξ + (0 : ℝ) • basisVec j) y : ℂ))) * (g y : ℂ)) volume :=
    hg.norm.mono' (hmeasF 0) (Filter.Eventually.of_forall fun y => (hnorm 0 y).le)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Vec 2)))
    (F := fun (t : ℝ) (y : Vec 2) => Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) * (g y : ℂ))
    (F' := fun (t : ℝ) (y : Vec 2) => (-Complex.I * (y j : ℂ)) *
      (Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) * (g y : ℂ)))
    (x₀ := 0) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hmeasF) hint0
    (by
      have h1 : AEStronglyMeasurable (fun y : Vec 2 => (-Complex.I * (y j : ℂ))) volume :=
        ((Complex.continuous_ofReal.comp (continuous_apply j)).aestronglyMeasurable).const_mul _
      exact h1.mul (hmeasF 0))
    (bound := fun y => ‖y j * g y‖)
    (Filter.Eventually.of_forall fun y t _ => by
      rw [norm_mul, hnorm, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        norm_mul])
    hgj.norm
    (Filter.Eventually.of_forall fun y t _ => by
      have h1 : HasDerivAt (fun t : ℝ => -(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ)))
          (-(Complex.I * (y j : ℂ))) t := by
        have : (fun t : ℝ => -(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) =
            fun t : ℝ => -(Complex.I * ((vecDot ξ y : ℂ) + (t : ℂ) * (y j : ℂ))) := by
          funext t; rw [hphase]; push_cast; ring
        rw [this]
        have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
        have h3 := ((h2.mul_const (y j : ℂ)).const_add (vecDot ξ y : ℂ)).const_mul Complex.I |>.neg
        convert h3 using 1
        rw [one_mul]
      have h4 := (h1.cexp).mul_const (g y : ℂ)
      convert h4 using 1
      ring)
  have e1 : ∫ y, (fun (t : ℝ) (y : Vec 2) => (-Complex.I * (y j : ℂ)) *
      (Complex.exp (-(Complex.I * (vecDot (ξ + t • basisVec j) y : ℂ))) * (g y : ℂ))) 0 y =
      -Complex.I * ∫ y, Complex.exp (-(Complex.I * (vecDot ξ y : ℂ))) * ((y j * g y : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [zero_smul, add_zero]
    push_cast
    ring
  rw [e1] at key
  exact key.2

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # one pair of stage orders from the forward bounds

For two stage orders `k' < k`, the forward bounds `FwdSameStatement` and `FwdLetterStatement`
give, with the ladder
`b1wPosLadder` (constant on each stage order), a family `Y` in the ladder space of the stage `k`
that represents the tested transforms of the stage values of order `k'`: the same-level bound
when the two levels agree, the letter bound when they are adjacent, and `0` otherwise. -/

section
universe u v

section Pair

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem level_mod (i : B1WIndex ι h Nw m Ks) : b1wSt i % (Nw + 1) = i.1.val := by
  unfold b1wSt
  have := i.1.isLt
  rw [add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt this

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem stage_ladder (Kf : ℕ) (d : Fin Nw → ℕ) (k : ℕ) :
    ∃ n0, ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      b1wPosLadder Kf d i = n0 := by
  by_cases hne : (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).Nonempty
  · obtain ⟨i0, hi0⟩ := hne
    refine ⟨b1wPosLadder Kf d i0, fun i hi => ladder_eq_of_st_eq Kf d ?_⟩
    simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi0
    omega
  · exact ⟨0, fun i hi => absurd ⟨i, hi⟩ hne⟩

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem mem_stage {k : ℕ} {i : B1WIndex ι h Nw m Ks} :
    i ∈ stageSet b1wSt k ↔ b1wSt i = k := by
  simp [stageSet]

theorem FwdBody.zero {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {k k' n N : ℕ} {C : ℝ} {T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks →
      (Vec 2 → ℂ) → Vec 2 → ℂ} {dmax : ℕ}
    (hT : ∀ i ∈ stageSet b1wSt k, ∀ i' ∈ stageSet b1wSt k', ∀ φ, T i i' φ = 0) :
    FwdBody F k k' n N C T dmax := by
  intro X
  refine ⟨fun _ => 0, fun i hi φ _ _ => ?_, ?_⟩
  · have h0 : ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y * T i i' φ y = 0 :=
      fun i' hi' => by simp [hT i hi i' hi']
    rw [Finset.sum_eq_zero h0]
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with y hy
      simp only [map_zero]
      rw [show ((0 : ComplexCellL2) : Vec 2 → ℂ) y = 0 from hy]
      simp
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity

theorem FwdBody.mono {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {k k' n N : ℕ} {C C' : ℝ} {T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks →
      (Vec 2 → ℂ) → Vec 2 → ℂ} {dmax : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hB : FwdBody F k k' n N C T dmax) : FwdBody F k k' n N C' T dmax := by
  intro X
  obtain ⟨Y, hY, hb⟩ := hB X
  refine ⟨Y, hY, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCC 2)
    (Finset.sum_nonneg fun _ _ => by positivity)

/-- The forward bound with the ladder spaces of the stage values. -/
def LadderBody (Kf : ℕ) (d : Fin Nw → ℕ)
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k k' n0 : ℕ) (C : ℝ) (dmax : ℕ) : Prop :=
  ∀ X : (i' : B1WIndex ι h Nw m Ks) → TorusHk (b1wPosLadder Kf d i') ℂ,
    ∃ Y : B1WIndex ι h Nw m Ks → TorusHk n0 ℂ,
    (∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ (dmax + 1) φ →
      AVenhance.IsZ2Periodic φ →
      ∫ y in AVenhance.unitCube, (torusHkValueCLM (Y i) : Vec 2 → ℂ) y * φ y =
        ∑ i' ∈ stageSet b1wSt k', b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y *
            b1wTestTransform F θ i i' r φ y) ∧
    ∑ i ∈ stageSet b1wSt k, ‖Y i‖ ^ 2 ≤ C ^ 2 * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2

theorem LadderBody.mono {Kf : ℕ} {d : Fin Nw → ℕ}
    {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁} {θ : Vec 2} {r : ℝ}
    {k k' n0 : ℕ} {C C' : ℝ} {dmax : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hB : LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 C dmax) :
    LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 C' dmax := by
  intro X
  obtain ⟨Y, hY, hb⟩ := hB X
  refine ⟨Y, hY, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCC 2)
    (Finset.sum_nonneg fun _ _ => by positivity)

theorem ladderBody_of_fwd {Kf : ℕ} {d : Fin Nw → ℕ}
    {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁} {θ : Vec 2} {r : ℝ}
    {k k' n0 N : ℕ} {C : ℝ} {T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks →
      (Vec 2 → ℂ) → Vec 2 → ℂ} {dmax : ℕ}
    (hB : FwdBody F k k' n0 N C T dmax)
    (hN : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        N ≤ b1wPosLadder Kf d i')
    (hT : ∀ i ∈ stageSet b1wSt k, ∀ i' ∈ stageSet b1wSt k', ∀ φ,
      T i i' φ = b1wTestTransform F θ i i' r φ) :
    LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 C dmax := by
  classical
  intro X
  let X' : B1WIndex ι h Nw m Ks → TorusHk N ℂ := fun i' =>
    if hN' : N ≤ b1wPosLadder Kf d i' then truncateTorusHk hN' (X i') else 0
  obtain ⟨Y, hY, hb⟩ := hB X'
  refine ⟨Y, fun i hi φ hφ hper => ?_, ?_⟩
  · rw [hY i hi φ hφ hper]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    have hv : (torusHkValueCLM (X' i') : Vec 2 → ℂ) = torusHkValueCLM (X i') := by
      simp only [X', hN i hi i' hi', ↓reduceDIte]
      rfl
    rw [hv, hT i hi i' hi' φ]
  · refine hb.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i' _ => ?_)
      (sq_nonneg _))
    have : ‖X' i'‖ ≤ ‖X i'‖ := by
      simp only [X']
      split_ifs with hN'
      · exact truncateTorusHk_norm_le hN' (X i')
      · simp
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem letter_zero_of_same {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {θ : Vec 2} {i i' : B1WIndex ι h Nw m Ks} (hl : i'.1 = i.1) (r : ℝ) (φ : Vec 2 → ℂ) :
    b1wLetterTransform F θ i i' r φ = 0 := by
  funext z
  simp only [b1wLetterTransform, Pi.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hc : ¬ (i.1 = l.succ ∧ i'.1 = l.castSucc) := by
    rintro ⟨h1, h2⟩
    rw [hl, h1] at h2
    exact absurd h2 (Fin.castSucc_lt_succ (i := l)).ne'
  simp [hc]

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem same_zero_of_ne {θ : Vec 2} {G : Matrix (Fin 2) (Fin 2) ℝ} {vf : Vec 2 → Vec 2}
    {i i' : B1WIndex ι h Nw m Ks} (hl : i'.1 ≠ i.1) (φ : Vec 2 → ℂ) :
    b1wSameTransform θ G vf i i' φ = 0 := by
  funext z
  simp [b1wSameTransform, hl]

/-- **One pair of stage orders.** -/
theorem pair (Kf : ℕ) (d : Fin Nw → ℕ) (dmax : ℕ)
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (CS CL : ℕ → ℝ) (hCS0 : ∀ n, 0 ≤ CS n) (hCL0 : ∀ n, 0 ≤ CL n) (top : ℕ)
    (hSame : ∀ (n k k' : ℕ),
      (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
        ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
          i'.1 = i.1) → ∀ N, n + 1 ≤ N →
      FwdBody (m := m) (Ks := Ks) F k k' n N (CS n)
        (fun i i' φ => b1wSameTransform θ (F.G r) (F.v r) i i' φ) dmax)
    (hLet : ∀ n ≤ top, ∀ (l : Fin Nw) (k k' : ℕ),
      (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
        i.1 = l.succ) →
      (∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        i'.1 = l.castSucc) → ∀ N, n + d l ≤ N →
      FwdBody (m := m) (Ks := Ks) F k k' n N (CL n)
        (fun i i' φ => b1wLetterTransform F θ i i' r φ) dmax)
    {k k' n0 : ℕ} (hkk : k' < k)
    (hn0 : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      b1wPosLadder Kf d i = n0) (hn0top : n0 ≤ top) :
    LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 (CS n0 + CL n0) dmax := by
  classical
  have hlev : ∀ i : B1WIndex ι h Nw m Ks, i ∈ stageSet b1wSt k → i.1.val = k % (Nw + 1) := by
    intro i hi
    rw [← level_mod i, mem_stage.1 hi]
  have hlev' : ∀ i : B1WIndex ι h Nw m Ks, i ∈ stageSet b1wSt k' → i.1.val = k' % (Nw + 1) := by
    intro i hi
    rw [← level_mod i, mem_stage.1 hi]
  have hlt : k % (Nw + 1) < Nw + 1 := Nat.mod_lt _ (Nat.succ_pos Nw)
  have hst : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        b1wSt i' < b1wSt i := fun i hi i' hi' => by
    rw [mem_stage.1 hi, mem_stage.1 hi']
    exact hkk
  by_cases ha : k % (Nw + 1) = k' % (Nw + 1)
  · -- same level
    have hsame : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
        ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
          i'.1 = i.1 := fun i hi i' hi' => Fin.ext (by rw [hlev i hi, hlev' i' hi', ha])
    refine LadderBody.mono (hCS0 n0) (le_add_of_nonneg_right (hCL0 n0)) ?_
    refine ladderBody_of_fwd (hSame n0 k k' hsame (n0 + 1) le_rfl) ?_ ?_
    · intro i hi i' hi'
      have := ladder_same Kf d (hsame i hi i' hi') (hst i hi i' hi')
      rw [hn0 i hi] at this
      exact this
    · intro i hi i' hi' φ
      funext z
      simp only [b1wTestTransform]
      rw [letter_zero_of_same (hsame i hi i' hi')]
      simp
  · by_cases hb : k % (Nw + 1) = k' % (Nw + 1) + 1
    · -- letter step
      have hlN : k' % (Nw + 1) < Nw := by omega
      set l : Fin Nw := ⟨k' % (Nw + 1), hlN⟩ with hl
      have hi : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
          i.1 = l.succ := fun i hi => Fin.ext (by rw [hlev i hi, hb]; simp [hl])
      have hi' : ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
          i'.1 = l.castSucc := fun i' hi' => Fin.ext (by rw [hlev' i' hi']; simp [hl])
      refine LadderBody.mono (hCL0 n0) (le_add_of_nonneg_left (hCS0 n0)) ?_
      refine ladderBody_of_fwd (hLet n0 hn0top l k k' hi hi' (n0 + d l) le_rfl) ?_ ?_
      · intro i hi2 i' hi2'
        have := ladder_letter Kf d l (hi i hi2) (hi' i' hi2') (hst i hi2 i' hi2')
        rw [hn0 i hi2] at this
        exact this
      · intro i hi2 i' hi2' φ
        funext z
        simp only [b1wTestTransform]
        have hne : i'.1 ≠ i.1 := by
          rw [hi i hi2, hi' i' hi2']
          exact (Fin.castSucc_lt_succ (i := l)).ne
        rw [same_zero_of_ne (θ := θ) (G := F.G r) (vf := F.v r) hne]
        simp
    · -- all transforms vanish
      have hz : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
          ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
            ∀ φ, b1wTestTransform F θ i i' r φ = 0 := by
        intro i hi2 i' hi2' φ
        refine b1wTestTransform_zero_of_level F θ i i' ?_ ?_ r φ
        · intro heq
          apply ha
          rw [← hlev i hi2, ← hlev' i' hi2', heq]
        · rintro l ⟨h1, h2⟩
          apply hb
          rw [← hlev i hi2, ← hlev' i' hi2', h1, h2]
          simp
      refine LadderBody.mono (C := 0) le_rfl (add_nonneg (hCS0 n0) (hCL0 n0)) ?_
      exact ladderBody_of_fwd (T := fun i i' φ => b1wTestTransform F θ i i' r φ) (N := 0)
        (FwdBody.zero hz) (fun _ _ _ _ => Nat.zero_le _) (fun _ _ _ _ _ => rfl)
end Pair
end

/-! # the sum over the earlier stage orders, and the extension from smooth tests

* `combine`: the families of the pairs `(k', k)`, `k' < k`, add up to one family in the
  ladder space of the stage `k`, with the square-sum bound `M C²` (`M` the number of stages).
* `eq_of_dense`: two continuous functionals of `H^1` of the torus that agree on the smooth
  periodic representatives of an approximating sequence agree everywhere. -/

section
universe u v

section Combine

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem integrable_mul (f : ComplexCellL2) (φ : Vec 2 → ℂ) (hφ : Continuous φ) :
    Integrable (fun y => f y * φ y) (volume.restrict AVenhance.unitCube) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : AVenhance.unitCube ⊆ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun i => ⟨(hx i).1.le, (hx i).2.le⟩
  have hmeas : MeasurableSet AVenhance.unitCube := by
    unfold AVenhance.unitCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top⟩
  have hf : IntegrableOn (fun y => f y) AVenhance.unitCube volume :=
    (Lp.memLp f).integrable (by norm_num)
  exact hf.mul_continuousOn_of_subset hφ.continuousOn hmeas hK hsub

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem int_sum {α : Type*} (v : α → ComplexCellL2) (s : Finset α) (φ : Vec 2 → ℂ)
    (hφ : Continuous φ) :
    ∫ y in AVenhance.unitCube, ((∑ a ∈ s, v a : ComplexCellL2) : Vec 2 → ℂ) y * φ y =
      ∑ a ∈ s, ∫ y in AVenhance.unitCube, (v a : Vec 2 → ℂ) y * φ y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with y hy
      rw [show ((0 : ComplexCellL2) : Vec 2 → ℂ) y = 0 from hy]
      simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
      ← integral_add (integrable_mul _ φ hφ) (integrable_mul _ φ hφ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (v a) (∑ b ∈ s, v b)] with y hy
    rw [show (((v a + ∑ b ∈ s, v b : ComplexCellL2)) : Vec 2 → ℂ) y =
      (v a : Vec 2 → ℂ) y + ((∑ b ∈ s, v b : ComplexCellL2) : Vec 2 → ℂ) y from hy]
    ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem sum_stage_real (f : B1WIndex ι h Nw m Ks → ℝ) (k₀ : ℕ) :
    ∑ k' ∈ Finset.range k₀, ∑ i' ∈ stageSet b1wSt k', f i' =
      ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k₀), f i' := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := b1wSt) (t := Finset.range k₀)
    fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2]
  refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hh
    exact ⟨hh ▸ Finset.mem_range.1 hk', hh⟩
  · rintro ⟨-, hh⟩
    exact hh

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem stage_empty {k' : ℕ} (hk : b1wM Nw m Ks ≤ k') :
    stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k' = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun i _ hi => ?_
  have := b1wSt_lt i
  omega

/-- **The sum over the earlier stage orders.** -/
theorem combine (Kf : ℕ) (d : Fin Nw → ℕ) (dmax : ℕ)
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k n0 : ℕ) (C : ℝ)
    (pairs : ∀ k' < k, LadderBody (m := m) (Ks := Ks) Kf d F θ r k k' n0 C dmax)
    (X : (i' : B1WIndex ι h Nw m Ks) → TorusHk (b1wPosLadder Kf d i') ℂ) :
    ∃ Y : B1WIndex ι h Nw m Ks → TorusHk n0 ℂ,
      (∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ (dmax + 1) φ →
        AVenhance.IsZ2Periodic φ →
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (Y i) : Vec 2 → ℂ) y * φ y =
          ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
            b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y *
                b1wTestTransform F θ i i' r φ y) ∧
      ∑ i ∈ stageSet b1wSt k, ‖Y i‖ ^ 2 ≤ (b1wM Nw m Ks : ℝ) * C ^ 2 *
        ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2 := by
  classical
  have hex : ∀ k' : ℕ, ∃ Y : B1WIndex ι h Nw m Ks → TorusHk n0 ℂ, k' < k →
      ((∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ (dmax + 1) φ →
        AVenhance.IsZ2Periodic φ →
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (Y i) : Vec 2 → ℂ) y * φ y =
          ∑ i' ∈ stageSet b1wSt k', b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y *
              b1wTestTransform F θ i i' r φ y) ∧
      ∑ i ∈ stageSet b1wSt k, ‖Y i‖ ^ 2 ≤ C ^ 2 * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2) := by
    intro k'
    by_cases hk : k' < k
    · obtain ⟨Y, h1, h2⟩ := pairs k' hk X
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Yk hYk using hex
  set k₀ := min k (b1wM Nw m Ks) with hk₀
  have hk₀k : k₀ ≤ k := min_le_left _ _
  have hk₀M : k₀ ≤ b1wM Nw m Ks := min_le_right _ _
  refine ⟨fun i => ∑ k' ∈ Finset.range k₀, Yk k' i, fun i hi φ hφ hper => ?_, ?_⟩
  · simp only [map_sum]
    rw [int_sum _ _ _ hφ.continuous]
    have hsub : Finset.range k₀ ⊆ Finset.range k := Finset.range_subset_range.2 hk₀k
    have hz : ∀ k' ∈ Finset.range k, k' ∉ Finset.range k₀ →
        (∑ i' ∈ stageSet b1wSt k', b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, (torusHkValueCLM (X i') : Vec 2 → ℂ) y *
            b1wTestTransform F θ i i' r φ y) = 0 := by
      intro k' hk' hk''
      have : b1wM Nw m Ks ≤ k' := by
        have h1 := Finset.mem_range.1 hk'
        have h2 : ¬ k' < k₀ := fun hh => hk'' (Finset.mem_range.2 hh)
        omega
      rw [stage_empty this]
      simp
    rw [← Finset.sum_subset hsub hz]
    refine Finset.sum_congr rfl fun k' hk' => ?_
    exact (hYk k' (lt_of_lt_of_le (Finset.mem_range.1 hk') hk₀k)).1 i hi φ hφ hper
  · have hk₀le : (k₀ : ℝ) ≤ b1wM Nw m Ks := by exact_mod_cast hk₀M
    calc ∑ i ∈ stageSet b1wSt k, ‖∑ k' ∈ Finset.range k₀, Yk k' i‖ ^ 2
        ≤ ∑ i ∈ stageSet b1wSt k, (k₀ : ℝ) * ∑ k' ∈ Finset.range k₀, ‖Yk k' i‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc ‖∑ k' ∈ Finset.range k₀, Yk k' i‖ ^ 2
              ≤ (∑ k' ∈ Finset.range k₀, ‖Yk k' i‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (Finset.range k₀).card * ∑ k' ∈ Finset.range k₀, ‖Yk k' i‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
            _ = _ := by rw [Finset.card_range]
      _ = (k₀ : ℝ) * ∑ k' ∈ Finset.range k₀, ∑ i ∈ stageSet b1wSt k, ‖Yk k' i‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (k₀ : ℝ) * ∑ k' ∈ Finset.range k₀, C ^ 2 * ∑ i' ∈ stageSet b1wSt k', ‖X i'‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k' hk' => ?_) (by positivity)
          exact (hYk k' (lt_of_lt_of_le (Finset.mem_range.1 hk') hk₀k)).2
      _ = (k₀ : ℝ) * C ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k₀),
            ‖X i'‖ ^ 2 := by
          rw [← Finset.mul_sum, mul_assoc,
            sum_stage_real (fun i' => ‖X i'‖ ^ 2) k₀]
      _ ≤ (b1wM Nw m Ks : ℝ) * C ^ 2 *
            ∑ i' ∈ Finset.univ.filter (fun i' => b1wSt i' < k), ‖X i'‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hk₀le (sq_nonneg _)) ?_
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1,
              lt_of_lt_of_le (Finset.mem_filter.1 hi).2 hk₀k⟩)
            (fun _ _ _ => by positivity)

end Combine
end

end AVRegularity.CycleWords.Discard
end
