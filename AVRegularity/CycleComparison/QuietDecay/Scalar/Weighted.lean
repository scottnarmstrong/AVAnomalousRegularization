-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! A dimension-free periodic Sobolev sup bound on `𝕋²` for `C²` fields with values in a normed
space: the pointwise value is bounded by the `L²` norms of the derivatives of order at most `2`
over the unit cell (constant `4`). The proof moves the point into the unit square by periodicity,
applies the two-dimensional sampling bound on the square `[0,1]²`, and takes square roots. -/

theorem rpow_half_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ (1 / 2 : ℝ) ≤ ∑ i ∈ s, f i ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add_right ih _)

theorem sq_le_four_mul_to_rpow (x S : ℝ≥0∞) (h : x ^ 2 ≤ 4 * S) :
    x ≤ 4 * S ^ (1 / 2 : ℝ) := by
  have h1 : x = (x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc x = (x ^ 2) ^ (1 / 2 : ℝ) := h1
    _ ≤ (4 * S) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = 4 ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 4 * S ^ (1 / 2 : ℝ) := by
        gcongr
        calc (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ 4 ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := ENNReal.rpow_one _

theorem lintegral_square_eq_unitCube (f : Vec 2 → ℝ≥0∞) :
    ∫⁻ x in Set.pi univ (fun i => Icc ((0 : Vec 2) i) ((0 : Vec 2) i + 1)), f x =
      ∫⁻ x in AVenhance.unitCube, f x := by
  have e : (fun i : Fin 2 => Icc ((0 : Vec 2) i) ((0 : Vec 2) i + 1)) =
      fun i => Icc ((0 : Vec 2) i) 1 := by
    funext i
    simp
  rw [Sampling.lintegral_unitCube_eq_Ico, e]
  exact (Sampling.lintegral_pi_Ico_eq_Icc f 0 fun _ => 1).symm

/-- Every point is congruent modulo `ℤ²` to a point of the unit square. -/
theorem exists_mem_square (z : Vec 2) :
    ∃ (n : Fin 2 → ℤ) (X : Vec 2), z = X + AVenhance.latticeShift n ∧
      X ∈ Set.pi univ fun i => Icc ((0 : Vec 2) i) ((0 : Vec 2) i + 1) := by
  refine ⟨fun i => ⌊z i⌋, fun i => Int.fract (z i), ?_, ?_⟩
  · ext i
    exact (Int.fract_add_floor (z i)).symm
  · intro i _
    exact ⟨Int.fract_nonneg _, by
      show Int.fract (z i) ≤ (0 : ℝ) + 1
      linarith [Int.fract_lt_one (z i)]⟩

/-- **Periodic Sobolev sup bound** (dimension-free, Banach-valued): constant `4`. -/
theorem periodic_sup_le_sobolev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Vec 2 → E} (hg : ContDiff ℝ 2 g) (hp : AVenhance.IsZ2Periodic g) (z : Vec 2) :
    ‖g z‖ₑ ≤ 4 * ∑ m ∈ Finset.range 3, ∑ β : DerivativeWord2 m,
      (∫⁻ x in AVenhance.unitCube, ‖orderedDerivative β g x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨n, X, hz, hX⟩ := exists_mem_square z
  have hgz : g z = g X := by rw [hz]; exact hp n X
  have hsq := Sampling.enorm_sq_le_square g (by exact_mod_cast hg) (a := 0) (L := 1)
    one_pos hX
  simp only [one_pow, ENNReal.ofReal_one, one_mul, inv_one] at hsq
  simp only [lintegral_square_eq_unitCube] at hsq
  rw [hgz]
  have h4 : ENNReal.ofReal (4 * (1 : ℝ)) = 4 := by norm_num
  rw [h4] at hsq
  refine (sq_le_four_mul_to_rpow _ _ hsq).trans ?_
  refine mul_le_mul' le_rfl ?_
  refine (rpow_half_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun m _ => rpow_half_sum_le _ _

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.QuietDecay

/-! Coefficient congruence for public cell solutions on a time interval, and the extension of a
space-independent elliptic metric from a window to an admissible global cell metric. -/

/-- A public cell solution on `I` only depends on the coefficients at times of `I`. -/
theorem cellSolution_coeff_congr {I : Set ℝ} {C C' : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hG : ∀ t ∈ I, C.G t = C'.G t) (hv : ∀ t ∈ I, C.v t = C'.v t) (hθ : C.θ = C'.θ)
    (hκ : ∀ t ∈ I, C.κ t = C'.κ t) (h : IsCellSolution I C src F D) :
    IsCellSolution I C' src F D := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  intro s hs t ht hst ψ
  have hw := h.2.2.2.2.2.2 s hs t ht hst ψ
  have hsub : Ioc s t ⊆ I := fun r hr => h.1.out hs ht ⟨hr.1.le, hr.2⟩
  let μ := volume.restrict AVenhance.unitCube
  let R := fun τ => cellLiteralRHS C τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ) (F τ)
  let R' := fun τ => cellLiteralRHS C' τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ) (F τ)
  have he : ∀ᵐ τ ∂volume.restrict (Ioc s t), R τ = R' τ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτI := hsub hτ
    funext x
    simp only [R, R', cellLiteralRHS, hG τ hτI, hv τ hτI, hθ, hκ τ hτI]
  have hint : (fun τ => ∫ x, R τ x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun τ => ∫ x, R' τ x ∂μ := he.mono fun τ hr => congrArg (fun f => ∫ x, f x ∂μ) hr
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) μ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R τ) μ) ∧
    IntegrableOn (fun τ => ∫ x, R τ x ∂μ) (Ioc s t) ∧
    (∫ x, cellValue D t x * ψ.jet (valueIndex2 1) x ∂μ) -
      (∫ x, cellValue D s x * ψ.jet (valueIndex2 1) x ∂μ) =
        ∫ τ in Ioc s t, ∫ x, R τ x ∂μ at hw
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) μ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ) ∧
    IntegrableOn (fun τ => ∫ x, R' τ x ∂μ) (Ioc s t) ∧
    (∫ x, cellValue D t x * ψ.jet (valueIndex2 1) x ∂μ) -
      (∫ x, cellValue D s x * ψ.jet (valueIndex2 1) x ∂μ) =
        ∫ τ in Ioc s t, ∫ x, R' τ x ∂μ
  refine ⟨hw.1, hw.2.1, ?_, hw.2.2.2.1.congr hint, ?_⟩
  · filter_upwards [hw.2.2.1, he] with τ h1 h2
    rw [← h2]; exact h1
  · exact hw.2.2.2.2.trans (integral_congr_ae hint)

/-- The global metric agreeing with `G` on `[a,b]` and the identity elsewhere. -/
def windowMetric (a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t _ => if t ∈ Icc a b then G t else 1

theorem windowMetric_isCellMetric {a b : ℝ} (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : ∀ i j, Measurable fun t => G t i j)
    (hGs : ∀ t ∈ Icc a b, ∀ i j, G t i j = G t j i)
    (hGe : ∀ t ∈ Icc a b, ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G t i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) :
    IsCellMetric (windowMetric a b G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : Measurable (fun p : ℝ × Vec 2 => if p.1 ∈ Icc a b then G p.1 else 1) := by
      refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      exact (hGm i j).comp measurable_fst
    exact h1
  · intro t n x
    rfl
  · intro t z
    unfold windowMetric
    split_ifs with ht
    · exact Matrix.IsSymm.ext fun i j => (hGs t ht j i)
    · exact Matrix.isSymm_one
  · intro t z ξ
    unfold windowMetric
    split_ifs with ht
    · obtain ⟨h1, h2⟩ := hGe t ht ξ
      have e : ∑ i, ∑ j, ξ i * G t i j * ξ j = ∑ i, ∑ j, G t i j * ξ i * ξ j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      have : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      constructor <;> linarith
    · have e : ∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j = ∑ i, ξ i ^ 2 := by
        simp [Fin.sum_univ_two, Matrix.one_apply, sq]
      rw [e]
      have : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      constructor <;> linarith

theorem zero_isCellDrift : IsCellDrift (fun _ _ => 0) := by
  refine ⟨measurable_const, ⟨0, fun t z => by simp⟩, fun t n x => rfl, fun t φ => by simp⟩

/-! Real-valued energy estimates for a mean-zero cell solution of a space-independent elliptic
metric with zero drift on the window `[a,b]`, through the Hilbert curve of the solution. -/

section
section

variable {a b : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}

theorem zero_drift_bound (t : ℝ) (x : Vec 2) :
    ∑ i, ((fun (_ : ℝ) (_ : Vec 2) => (0 : Vec 2)) t x i) ^ 2 ≤ (0 : ℝ) ^ 2 := by
  simp

/-- The restricted solution, re-expressed with the global window metric and zero drift. -/
theorem solution_window (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D) :
    IsCellSolution (Icc a b) ⟨windowMetric a b G, fun _ _ => 0, 0, 0⟩ src F D :=
  cellSolution_coeff_congr (C := ⟨fun t _ => G t, v, 0, 0⟩)
    (C' := ⟨windowMetric a b G, fun _ _ => 0, 0, 0⟩)
    (fun t ht => funext fun z => by simp [windowMetric, ht])
    (fun t ht => funext fun z => hv t ht z) rfl (fun t ht => rfl) h

theorem hilbert_curve (hab : a ≤ b) (hM : IsCellMetric (windowMetric a b G))
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun τ => cellDualDerivative ⟨windowMetric a b G, fun _ _ => (0 : Vec 2), 0, 0⟩ hM 0
        zero_isCellDrift.1 zero_drift_bound τ (cellH1Slice D τ) (cellSourceSlice src τ)
        (fun j => cellSourceSlice (fun r x => F r x j) τ)) :=
  cellSolution_to_Hilbert hab ⟨windowMetric a b G, fun _ _ => (0 : Vec 2), 0, 0⟩ hM 0 0
    zero_isCellDrift.1 zero_drift_bound measurable_const (fun t => by simp) src F hsrcL hFL D
    (solution_window hv h)

theorem trace_mean_zero (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0)
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D) :
    ∀ t ∈ Icc a b, cellMean (cellRawTrace D t) = 0 := by
  intro t ht
  rw [← hm t ht]
  unfold cellMean
  exact integral_congr_ae (cellRawTrace_ae D t (h.2.2.1 t ht).1)

theorem forcing_memLp (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (cellSourceSlice src) 2 (volume.restrict (Icc a b)) ∧
      ∀ j, MemLp (fun t => cellSourceSlice (fun r x => F r x j) t) 2 (volume.restrict (Icc a b)) :=
  ⟨cellSourceSlice_memLp (Icc a b) src hsrcL, fun j =>
    cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hFL)⟩

/-- Real endpoint estimate in Hilbert form. -/
theorem real_endpoint (hab : a ≤ b) (hM : IsCellMetric (windowMetric a b G))
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    ‖cellRawTrace D b‖ ^ 2 ≤ Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ ^ 2 +
      ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
        (‖cellSourceSlice src τ‖ ^ 2 +
          8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2) := by
  obtain ⟨hS, hF⟩ := forcing_memLp hsrcL hFL
  exact cellWeakActual_forced_decay hab hM zero_isCellDrift 0 zero_drift_bound
    (cellRawTrace D) (cellH1Slice D) (cellSourceSlice src)
    (fun τ j => cellSourceSlice (fun r x => F r x j) τ) hS hF
    (hilbert_curve hab hM hv hsrcL hFL h) (trace_mean_zero hm h)

theorem weight_shift (a b : ℝ) (f : ℝ → ℝ) :
    ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) * f τ =
      Real.exp (-(Real.pi ^ 2) * (b - a)) *
        ∫ τ in a..b, Real.exp (Real.pi ^ 2 * (τ - a)) * f τ := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Real exponentially weighted local energy estimate in Hilbert form. -/
theorem real_weighted_energy (hab : a ≤ b) (hM : IsCellMetric (windowMetric a b G))
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    (1 / 2) * ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
        ∑ j, ‖cellDerivativeCLM j (cellH1Slice D τ)‖ ^ 2 ≤
      Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ ^ 2 +
        ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2) := by
  obtain ⟨hS, hF⟩ := forcing_memLp hsrcL hFL
  have he := cellWeakActual_weighted_energy hab hM zero_isCellDrift 0 zero_drift_bound
    (cellRawTrace D) (cellH1Slice D) (cellSourceSlice src)
    (fun τ j => cellSourceSlice (fun r x => F r x j) τ) hS hF
    (hilbert_curve hab hM hv hsrcL hFL h) (trace_mean_zero hm h)
  rw [weight_shift a b, weight_shift a b]
  have hc := Real.exp_pos (-(Real.pi ^ 2) * (b - a))
  have hc2 : 0 ≤ Real.exp (-(Real.pi ^ 2) * (b - a)) *
      (Real.exp (Real.pi ^ 2 * (b - a)) * ‖cellRawTrace D b‖ ^ 2) :=
    mul_nonneg hc.le (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left he hc.le
  have e : ∫ τ in a..b, Real.exp (Real.pi ^ 2 * (τ - a)) *
      ((1 / 2) * ∑ j, ‖cellDerivativeCLM j (cellH1Slice D τ)‖ ^ 2) =
      (1 / 2) * ∫ τ in a..b, Real.exp (Real.pi ^ 2 * (τ - a)) *
        ∑ j, ‖cellDerivativeCLM j (cellH1Slice D τ)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  rw [e] at hmul
  nlinarith [hmul, hc2]

end
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Conversion between the Hilbert-space energy estimates and the extended-norm statements:
finiteness of the forcing integral gives product-space `L²` membership, and the Hilbert norms of
the trace, the forcing slices and the gradient slices are the extended `cellL2Norm`s. -/

section
/-- The forcing density of the energy estimates. -/
def forcingDensity (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (σ : ℝ) : ℝ≥0∞ :=
  cellL2Norm (src σ) ^ 2 + 8 * ∑ j : Fin 2, cellL2Norm (fun x => F σ x j) ^ 2

section

variable {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {D : ℝ → RawJet2 1 ℂ} {a b : ℝ}

theorem pilp_norm_le_sum (x : PiLp 2 (fun _ : Fin 2 => ℂ)) : ‖x‖ ≤ ∑ j, ‖x j‖ := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_two]
  nlinarith [mul_nonneg (norm_nonneg (x 0)) (norm_nonneg (x 1))]

theorem memLp_of_finite {I : Set ℝ}
    (hsrc : AEStronglyMeasurable (Function.uncurry src)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hfin : ∫⁻ σ in I, forcingDensity src F σ < ⊤) :
    MemLp (Function.uncurry src) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) ∧
      MemLp (Function.uncurry F) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  refine ⟨cellJoint_memLp_of_cellNorm I src hsrc
    (lt_of_le_of_lt (lintegral_mono fun σ => le_self_add) hfin), ?_⟩
  have hj : ∀ j : Fin 2, MemLp (Function.uncurry fun σ x => F σ x j) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    intro j
    refine cellJoint_memLp_of_cellNorm I (fun σ x => F σ x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).continuous.comp_aestronglyMeasurable hF)
      (lt_of_le_of_lt (lintegral_mono fun σ => ?_) hfin)
    refine (Finset.single_le_sum (f := fun j : Fin 2 => cellL2Norm (fun x => F σ x j) ^ 2)
      (fun _ _ => bot_le) (Finset.mem_univ j)).trans ?_
    exact (le_mul_of_one_le_left bot_le (by norm_num)).trans le_add_self
  have hs : MemLp (fun p : ℝ × Vec 2 => ∑ j : Fin 2, ‖F p.1 p.2 j‖) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    simp only [Fin.sum_univ_two]
    exact (hj 0).norm.add (hj 1).norm
  refine hs.of_le hF (Filter.Eventually.of_forall fun p => ?_)
  show ‖F p.1 p.2‖ ≤ ‖∑ j : Fin 2, ‖F p.1 p.2 j‖‖
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact pilp_norm_le_sum _

theorem cellL2Norm_sq_trace (D : ℝ → RawJet2 1 ℂ) (s : ℝ)
    (hs : MemLp (cellValue D s) 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (cellValue D s) ^ 2 = ENNReal.ofReal (‖cellRawTrace D s‖ ^ 2) := by
  rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D s hs), ENNReal.ofReal_pow (norm_nonneg _)]

theorem forcing_ae {I : Set ℝ} (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ∀ᵐ σ ∂volume.restrict I, ENNReal.ofReal (‖cellSourceSlice src σ‖ ^ 2 +
        8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) σ‖ ^ 2) =
      forcingDensity src F σ := by
  have hFj : ∀ j : Fin 2, MemLp (Function.uncurry fun r x => F r x j) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := fun j =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hFL
  filter_upwards [cellSource_memLp_slices I src hsrcL,
    (ae_all_iff.mpr fun j => cellSource_memLp_slices I (fun r x => F r x j) (hFj j))] with σ h1 h2
  have e1 : cellL2Norm (src σ) = ENNReal.ofReal ‖cellSourceSlice src σ‖ :=
    cellL2Norm_eq_of_class _ _ (cellSourceSlice_ae src σ h1)
  have e2 : ∀ j : Fin 2, cellL2Norm (fun x => F σ x j) =
      ENNReal.ofReal ‖cellSourceSlice (fun r x => F r x j) σ‖ := fun j =>
    cellL2Norm_eq_of_class _ _ (cellSourceSlice_ae (fun r x => F r x j) σ (h2 j))
  unfold forcingDensity
  rw [e1, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [e2, ENNReal.ofReal_pow (norm_nonneg _)]
  norm_num

theorem gradient_ae {C : CellCoefficients}
    (h : IsCellSolution (Icc a b) C src F D) :
    ∀ᵐ σ ∂volume.restrict (Icc a b), ENNReal.ofReal
        (∑ j : Fin 2, ‖cellDerivativeCLM j (cellH1Slice D σ)‖ ^ 2) =
      ∑ j : Fin 2, cellL2Norm (cellGradComp (D σ)  j) ^ 2 := by
  filter_upwards [cellSolution_slice_ae h] with σ hσ
  have e : ∀ j : Fin 2, cellL2Norm (cellGradComp (D σ) j) =
      ENNReal.ofReal ‖cellDerivativeCLM j (cellH1Slice D σ)‖ := fun j =>
    cellL2Norm_eq_of_class _ _ (hσ ⟨⟨1, by decide⟩, fun _ => j⟩)
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  simp only [e, ENNReal.ofReal_pow (norm_nonneg _)]

end
end

/-! Endpoint and gradient energy bounds for a mean-zero cell solution on a finite interval with a
space-independent elliptic metric and zero drift: exponential decay with rate `π²` of the
`L²` norm, and the integrated gradient energy. -/

section
theorem ofReal_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (hf : ∀ τ, 0 ≤ f τ) :
    ENNReal.ofReal (∫ τ in a..b, f τ) ≤ ∫⁻ τ in Icc a b, ENNReal.ofReal (f τ) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  by_cases hi : IntegrableOn f (Icc a b)
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi]
    simp

theorem ofReal_intervalIntegral_eq {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (hf : ∀ τ, 0 ≤ f τ)
    (hi : IntervalIntegrable f volume a b) :
    ENNReal.ofReal (∫ τ in a..b, f τ) = ∫⁻ τ in Icc a b, ENNReal.ofReal (f τ) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi) (Filter.Eventually.of_forall hf)

section

variable {a b : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}

/-- Weighted forcing integral, as a lower bound of the unweighted one. -/
theorem fin_of_weighted {t : ℝ}
    (h : ∫⁻ σ in Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
      forcingDensity src F σ ≠ ⊤) : ∫⁻ σ in Icc a t, forcingDensity src F σ < ⊤ := by
  set c := ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - a))) with hc
  have hc0 : c ≠ 0 := by
    simp only [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hle : c * ∫⁻ σ in Icc a t, forcingDensity src F σ ≤
      ∫⁻ σ in Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
        forcingDensity src F σ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc fun σ hσ => ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) _
    have := mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hσ.1)
    linarith
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.mul_top hc0, top_le_iff] at hle
  exact h hle

/-- The hypotheses of the window estimates, restricted to `[a,t]`. -/
theorem restrict_hyps {t : ℝ} (ht : t ∈ Icc a b)
    (hGm : ∀ i j, Measurable fun t => G t i j)
    (hGs : ∀ t ∈ Icc a b, ∀ i j, G t i j = G t j i)
    (hGe : ∀ t ∈ Icc a b, ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G t i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrc : AEStronglyMeasurable (Function.uncurry src)
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    IsCellMetric (windowMetric a t G) ∧ (∀ s ∈ Icc a t, ∀ z, v s z = 0) ∧
      IsCellSolution (Icc a t) ⟨fun t _ => G t, v, 0, 0⟩ src F D ∧
      (∀ s ∈ Icc a t, cellMean (cellValue D s) = 0) ∧
      AEStronglyMeasurable (Function.uncurry src)
        ((volume.restrict (Icc a t)).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Icc a t)).prod (volume.restrict AVenhance.unitCube)) := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hmono : (volume.restrict (Icc a t)).prod (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  exact ⟨windowMetric_isCellMetric G hGm (fun s hs => hGs s (hsub hs))
      (fun s hs => hGe s (hsub hs)), fun s hs => hv s (hsub hs),
    cellSolution_restrict hsub ordConnected_Icc h, fun s hs => hm s (hsub hs),
    hsrc.mono_measure hmono, hF.mono_measure hmono⟩

theorem endpoint_core (hab : a ≤ b) (hM : IsCellMetric (windowMetric a b G))
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    cellL2Norm (cellValue D b) ^ 2 ≤
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - a))) * cellL2Norm (cellValue D a) ^ 2 +
        ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
          forcingDensity src F σ := by
  rw [cellL2Norm_sq_trace D b (h.2.2.1 b ⟨hab, le_rfl⟩).1,
    cellL2Norm_sq_trace D a (h.2.2.1 a ⟨le_rfl, hab⟩).1]
  have hreal := real_endpoint hab hM hv hsrcL hFL h hm
  have hI0 : 0 ≤ ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
      (‖cellSourceSlice src τ‖ ^ 2 +
        8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2) :=
    intervalIntegral.integral_nonneg hab fun τ _ => by positivity
  have hcongr : ∫⁻ τ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - τ)) *
      (‖cellSourceSlice src τ‖ ^ 2 +
        8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2)) =
      ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
          forcingDensity src F σ := by
    refine lintegral_congr_ae ?_
    filter_upwards [forcing_ae hsrcL hFL] with σ hσ
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, hσ]
  calc ENNReal.ofReal (‖cellRawTrace D b‖ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ ^ 2 +
        ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - a))) *
          ENNReal.ofReal (‖cellRawTrace D a‖ ^ 2) +
        ENNReal.ofReal (∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2)) := by
        rw [ENNReal.ofReal_add (by positivity) hI0, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        refine add_le_add_right ((ofReal_intervalIntegral_le hab _ fun τ => by positivity).trans
          (le_of_eq hcongr)) _

end

variable {a b : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}

theorem cell_endpoint_bound {a b : ℝ} (hab : a ≤ b) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hGm : ∀ i j, Measurable fun t => G t i j)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ i j, G t i j = G t j i)
    (hGe : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G t i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hv : ∀ t ∈ Set.Icc a b, ∀ z, v t z = 0)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : AEStronglyMeasurable (Function.uncurry src)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Set.Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Set.Icc a b, cellMean (cellValue D t) = 0) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    cellL2Norm (cellValue D t) ^ 2 ≤
        ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - a))) * cellL2Norm (cellValue D a) ^ 2 +
      ∫⁻ σ in Set.Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
        (cellL2Norm (src σ) ^ 2 + 8 * ∑ j : Fin 2, cellL2Norm (fun x => F σ x j) ^ 2) := by
  have _ := hab
  obtain ⟨hM, hv', h', hm', hs', hF'⟩ := restrict_hyps ht hGm hGs hGe hv hsrc hF h hm
  by_cases htop : ∫⁻ σ in Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
      forcingDensity src F σ = ⊤
  · change _ ≤ _ + ∫⁻ σ in Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
      forcingDensity src F σ
    rw [htop]
    simp
  · obtain ⟨h1, h2⟩ := memLp_of_finite hs' hF' (fin_of_weighted htop)
    exact endpoint_core ht.1 hM hv' h1 h2 h' hm'
end

/-! The exponentially weighted gradient energy bound (constant `K = 2`) for a mean-zero cell
solution with space-independent elliptic metric and zero drift on the window. -/

section
section

variable {a b : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}

theorem weighted_core (hab : a ≤ b) (hM : IsCellMetric (windowMetric a b G))
    (hv : ∀ t ∈ Icc a b, ∀ z, v t z = 0)
    (hsrcL : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hFL : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (h : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
        ∑ j : Fin 2, cellL2Norm (cellGradComp (D σ) j) ^ 2 ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D a) ^ 2 +
        ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
          forcingDensity src F σ) := by
  rw [cellL2Norm_sq_trace D a (h.2.2.1 a ⟨le_rfl, hab⟩).1]
  have hreal := real_weighted_energy hab hM hv hsrcL hFL h hm
  have hQi := cellTime_gradientSq_intervalIntegrable hab _ (cellSolution_slice_memLp hab h)
  have hwc : ContinuousOn (fun τ : ℝ => Real.exp (-(Real.pi ^ 2) * (b - τ))) (uIcc a b) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(Real.pi ^ 2) * (b - τ))).continuousOn
  have hwQi := hQi.continuousOn_mul hwc
  have hJ0 : 0 ≤ ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
      (‖cellSourceSlice src τ‖ ^ 2 +
        8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2) :=
    intervalIntegral.integral_nonneg hab fun τ _ => by positivity
  have hcongr : ∫⁻ τ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - τ)) *
      (‖cellSourceSlice src τ‖ ^ 2 +
        8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2)) =
      ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
          forcingDensity src F σ := by
    refine lintegral_congr_ae ?_
    filter_upwards [forcing_ae hsrcL hFL] with σ hσ
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, hσ]
  have hL : ∫⁻ σ in Icc a b, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ))) *
        ∑ j : Fin 2, cellL2Norm (cellGradComp (D σ) j) ^ 2 =
      ENNReal.ofReal (∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
        ∑ j, ‖cellDerivativeCLM j (cellH1Slice D τ)‖ ^ 2) := by
    rw [ofReal_intervalIntegral_eq hab _ (fun τ => by positivity) hwQi]
    refine lintegral_congr_ae ((gradient_ae h).mono fun σ hσ => ?_)
    show _ = ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - σ)) *
      ∑ j, ‖cellDerivativeCLM j (cellH1Slice D σ)‖ ^ 2)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, hσ]
  have hQle : (∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
        ∑ j, ‖cellDerivativeCLM j (cellH1Slice D τ)‖ ^ 2) ≤
      2 * (Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ ^ 2 +
        ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2)) := by
    linarith
  rw [hL]
  calc _ ≤ ENNReal.ofReal (2 * (Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ ^ 2 +
        ∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2))) :=
        ENNReal.ofReal_le_ofReal hQle
    _ = ENNReal.ofReal 2 * (ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (b - a))) *
          ENNReal.ofReal (‖cellRawTrace D a‖ ^ 2) +
        ENNReal.ofReal (∫ τ in a..b, Real.exp (-(Real.pi ^ 2) * (b - τ)) *
          (‖cellSourceSlice src τ‖ ^ 2 +
            8 * ∑ j : Fin 2, ‖cellSourceSlice (fun r x => F r x j) τ‖ ^ 2))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) hJ0,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        refine mul_le_mul_right (add_le_add_right ?_ _) _
        exact (ofReal_intervalIntegral_le hab _ fun τ => by positivity).trans (le_of_eq hcongr)

end

/-- Exponentially weighted gradient bound, with the explicit constant `K = 2`. -/
theorem cell_weighted_gradient_bound {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hGm : ∀ i j, Measurable fun t => G t i j)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ i j, G t i j = G t j i)
    (hGe : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2, (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G t i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hv : ∀ t ∈ Set.Icc a b, ∀ z, v t z = 0)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : AEStronglyMeasurable (Function.uncurry src)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Set.Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ src F D)
    (hm : ∀ t ∈ Set.Icc a b, cellMean (cellValue D t) = 0) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∫⁻ σ in Set.Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
        ∑ j : Fin 2, cellL2Norm (cellGradComp (D σ) j) ^ 2 ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - a))) *
          cellL2Norm (cellValue D a) ^ 2 +
        ∫⁻ σ in Set.Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
          (cellL2Norm (src σ) ^ 2 + 8 * ∑ j : Fin 2, cellL2Norm (fun x => F σ x j) ^ 2)) := by
  have _ := hab
  obtain ⟨hM, hv', h', hm', hs', hF'⟩ := restrict_hyps ht hGm hGs hGe hv hsrc hF h hm
  by_cases htop : ∫⁻ σ in Icc a t, ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) *
      forcingDensity src F σ = ⊤
  · change _ ≤ ENNReal.ofReal 2 * (_ + ∫⁻ σ in Icc a t,
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - σ))) * forcingDensity src F σ)
    rw [htop, add_top, ENNReal.mul_top (by norm_num)]
    exact le_top
  · obtain ⟨h1, h2⟩ := memLp_of_finite hs' hF' (fin_of_weighted htop)
    exact weighted_core ht.1 hM hv' h1 h2 h' hm'
end

end AVRegularity.QuietDecay
end
