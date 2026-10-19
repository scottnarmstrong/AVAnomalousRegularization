-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellAffineHomeomorph
public import AVRegularity.CycleWords.ShearFrequencyAlgebra
import AVRegularity.Weighted.PeriodicScalarZeroEnergy
public import AVRegularity.CycleWords.WeightedRawProductAlgebra
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

section
section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Any positive duration accommodates a finite smoothing hierarchy. -/

theorem shortSmoothingStep_budget (J : ℕ) (δ₀ τ A : ℝ)
    (hδ₀ : 0 < δ₀) (hτ : 0 < τ) (hA : 0 ≤ A) (hbudget : A * δ₀ ≤ 1) :
    let δ := min δ₀ (τ / ((J : ℝ) + 1))
    0 < δ ∧ A * δ ≤ 1 ∧ (J : ℝ) * δ ≤ τ := by
  have hj : 0 < (J : ℝ) + 1 := by positivity
  refine ⟨lt_min hδ₀ (div_pos hτ hj),
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hA).trans hbudget, ?_⟩
  calc
    (J : ℝ) * min δ₀ (τ / ((J : ℝ) + 1)) ≤
        (J : ℝ) * (τ / ((J : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg J)
    _ = τ * ((J : ℝ) / ((J : ℝ) + 1)) := by ring
    _ ≤ τ * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one₀ hj).mpr (by linarith)) hτ.le
    _ = τ := mul_one _

/-! Abstract-real conversion from squared smoothing energies to the classical time singularity. -/

theorem smoothingSingularity_square (J : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    (τ ^ (-(J : ℝ) / 2)) ^ 2 = (τ ^ J)⁻¹ := by
  rw [← Real.rpow_two, ← Real.rpow_mul hτ.le]
  have he : (-(J : ℝ) / 2) * 2 = -(J : ℝ) := by ring
  rw [he, Real.rpow_neg hτ.le, Real.rpow_natCast]

theorem smoothingSquare_sum_price (B₀ B₁ u : ℝ)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hu : 0 ≤ u) :
    B₀ + B₁ * u ^ 2 ≤ (Real.sqrt (B₀ + B₁) * (1 + u)) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (add_nonneg hB₀ hB₁)]
  have h1 := mul_nonneg hB₀ (sq_nonneg u)
  have h2 := mul_nonneg (add_nonneg hB₀ hB₁) hu
  nlinarith only [h1, h2, hB₁]

theorem smoothingSingularity_sum_price (J : ℕ) (τ B₀ B₁ : ℝ)
    (hτ : 0 < τ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    B₀ + B₁ / τ ^ J ≤
      (Real.sqrt (B₀ + B₁) * (1 + τ ^ (-(J : ℝ) / 2))) ^ 2 := by
  have he := smoothingSquare_sum_price B₀ B₁ (τ ^ (-(J : ℝ) / 2))
    hB₀ hB₁ (Real.rpow_nonneg hτ.le _)
  rw [smoothingSingularity_square J τ hτ] at he
  simpa only [div_eq_mul_inv] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory Topology TopologicalSpace
namespace AVRegularity.CycleWords

/-! Measurable data under a strongly continuous family of bounded linear operators. -/

theorem strongOperatorFamily_stronglyMeasurable
    {X Z E F 𝕜 : Type*} [MeasurableSpace X]
    [TopologicalSpace Z] [MetrizableSpace Z] [MeasurableSpace Z]
    [SecondCountableTopology Z] [OpensMeasurableSpace Z]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : Z → E →L[𝕜] F) (hA : ∀ e, Continuous (fun z => A z e))
    (d : X → E) (hd : StronglyMeasurable d) (ζ : X → Z) (hζ : Measurable ζ) :
    StronglyMeasurable (fun x => A (ζ x) (d x)) := by
  have hc : ∀ x, Continuous (fun z => A z (d x)) := fun x => hA (d x)
  have hm : ∀ z, StronglyMeasurable (fun x => A z (d x)) :=
    fun z => (A z).continuous.comp_stronglyMeasurable hd
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hm).comp_measurable
    (hζ.prodMk measurable_id)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! The scaled integral remainder coefficient retains its slow-degree smallness. -/

theorem taylorIntegral_coefficient_price (r j K : ℕ) {ϖ ζ t A : ℝ}
    (hϖ : 0 < ϖ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hA : 0 ≤ A) :
    |(1 - t) ^ K * (ϖ ^ r)⁻¹| * |t / ϖ| ^ j *
        (A * (ζ * ϖ) ^ (j + r)) ≤ A * ζ ^ r := by
  have hw : (1 - t) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hp : (t * ζ) ^ j ≤ 1 := pow_le_one₀ (mul_nonneg ht hζ)
    ((mul_le_mul_of_nonneg_left hζ1 ht).trans (by simpa using ht1))
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (by linarith) K) (by positivity)),
    abs_of_nonneg (div_nonneg ht hϖ.le)]
  have he : (1 - t) ^ K * (ϖ ^ r)⁻¹ * (t / ϖ) ^ j *
      (A * (ζ * ϖ) ^ (j + r)) = (1 - t) ^ K * (t * ζ) ^ j * (A * ζ ^ r) := by
    rw [pow_add, mul_pow, div_pow, mul_pow]
    field_simp
    ring
  rw [he]
  have hprod : (1 - t) ^ K * (t * ζ) ^ j ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (pow_nonneg (by linarith) K)).trans (by simpa using hw)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (mul_nonneg hA (pow_nonneg hζ r))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! A two-coordinate linear assembly is independent of its target carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def twoCoordinateComplexMap (u₀ u₁ : E) : (Fin 2 → ℂ) →L[ℂ] E :=
  (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight u₀ +
    (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight u₁

theorem twoCoordinateComplexMap_apply (u₀ u₁ : E) (ν : Fin 2 → ℂ) :
    twoCoordinateComplexMap u₀ u₁ ν = ν 0 • u₀ + ν 1 • u₁ := rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Genuine pointwise linear operator families induce linear maps on native L2 classes. -/

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def variableL2LinearMap (μ : Measure X) (A : X → E →L[ℝ] F)
    (hmem : ∀ f : Lp E 2 μ, MemLp (fun x => A x (f x)) 2 μ) : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun f := (hmem f).toLp (fun x => A x (f x))
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp,
      (hmem g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((hmem f).toLp (fun x => A x (f x)))
        ((hmem g).toLp (fun x => A x (g x)))] with x hfg hf hg hx hy
    rw [hfg, hy, hx]
    simp only [Pi.add_apply]
    rw [hf, hg]
    exact (A x).map_add _ _
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((hmem f).toLp (fun x => A x (f x)))] with x hcf hf hx hy
    rw [hcf, hy, hx]
    simp only [Pi.smul_apply]
    rw [hf]
    exact (A x).map_smul c (f x)

theorem variableL2LinearMap_ae (μ : Measure X) (A : X → E →L[ℝ] F)
    (hmem : ∀ f : Lp E 2 μ, MemLp (fun x => A x (f x)) 2 μ) (f : Lp E 2 μ) :
    variableL2LinearMap μ A hmem f =ᵐ[μ] fun x => A x (f x) := (hmem f).coeFn_toLp

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Enlarging a two-sided weight comparison constant. -/

theorem weight_comparison_enlarge {U V c C : ℝ} (hU : 0 ≤ U) (hc : 0 < c) (hCc : c ≤ C)
    (hlo : c⁻¹ * U ≤ V) (hhi : V ≤ c * U) : C⁻¹ * U ≤ V ∧ V ≤ C * U := by
  have hC := hc.trans_le hCc
  have hi := (inv_le_inv₀ hC hc).2 hCc
  exact ⟨(mul_le_mul_of_nonneg_right hi hU).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hCc hU)⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Literal joint representatives for simple families of native L2 classes. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem bochnerSimpleJoint_stronglyMeasurable (ν : Measure Y)
    (s : SimpleFunc X (Lp E 2 ν)) :
    StronglyMeasurable (fun p : X × Y => s p.1 p.2) := by
  classical
  induction s using SimpleFunc.induction' with
  | const c => exact (Lp.stronglyMeasurable c).comp_measurable measurable_snd
  | @pcw f g s hs hf hg =>
    have hm : StronglyMeasurable ((Prod.fst ⁻¹' s).piecewise
        (fun p : X × Y => f p.1 p.2) (fun p : X × Y => g p.1 p.2)) :=
      hf.piecewise (hs.preimage measurable_fst) hg
    convert hm using 1
    funext p
    simp only [SimpleFunc.coe_piecewise, Set.piecewise, Set.mem_preimage]
    split_ifs <;> rfl

theorem bochnerSimpleJoint_memLp (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (s : SimpleFunc X (Lp E 2 ν)) (hs : MemLp s 2 μ) :
    MemLp (fun p : X × Y => s p.1 p.2) 2 (μ.prod ν) := by
  have hm := bochnerSimpleJoint_stronglyMeasurable ν s
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hm.norm.pow 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (Lp.memLp (s x)).integrable_norm_pow (by decide)), ?_⟩
  have he (x : X) : (∫ y, ‖‖s x y‖ ^ 2‖ ∂ν) = ‖s x‖ ^ 2 := by
    calc
      _ = ∫ y, ‖s x y‖ ^ 2 ∂ν := integral_congr_ae
        (Eventually.of_forall (fun y => Real.norm_of_nonneg (sq_nonneg ‖s x y‖)))
      _ = _ := (lpTwoHilbert_normSq_integral ν (s x)).symm
  change Integrable (fun x => ∫ y, ‖‖s x y‖ ^ 2‖ ∂ν) μ
  simp_rw [he]
  exact hs.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Complex Metric
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Uniform Cauchy circle bounds give quantitative Taylor remainders. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The same circle bound controls every remainder on the half disc. -/
theorem boundedCauchy_partialSum_remainder (f : ℂ → E) (R : ℝ≥0) (hR : 0 < R)
    (M : ℝ) (hM : 0 ≤ M)
    (hf : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ < (R : ℝ) / 2) (n : ℕ) :
    ‖f z - (cauchyPowerSeries f 0 R).partialSum n z‖ ≤
      2 * M * (‖z‖ / R) ^ n := by
  have hr : 0 < (R : ℝ) := hR
  let r := ‖z‖ / (R : ℝ)
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) hr.le
  have hrhalf : r < 1 / 2 := by
    dsimp only [r]
    exact (div_lt_iff₀ hr).mpr (by linarith only [hz])
  have hr1 : r < 1 := hrhalf.trans (by norm_num)
  have hc (k : ℕ) : ‖cauchyPowerSeries f 0 R k (fun _ => z)‖ ≤ M * r ^ k := by
    calc
      _ ≤ ‖cauchyPowerSeries f 0 R k‖ * ∏ _i : Fin k, ‖z‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (M * (R : ℝ)⁻¹ ^ k) * ‖z‖ ^ k := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          mul_le_mul_of_nonneg_right (boundedCauchyCoefficient_norm_le f 0 R M hr.le hb k)
            (pow_nonneg (norm_nonneg z) k)
      _ = M * r ^ k := by dsimp only [r]; rw [div_eq_mul_inv, mul_pow]; ring
  have hzball : z ∈ eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [Metric.eball_coe, mem_ball, dist_zero_right]
    exact hz.trans (half_lt_self hr)
  have hs := hf.hasSum hzball
  simp only [zero_add] at hs
  have hh := norm_sub_le_of_geometric_bound_of_hasSum hr1 hc hs n
  have hden : (1 / 2 : ℝ) ≤ 1 - r := by linarith only [hrhalf]
  have hlast : M * r ^ n / (1 - r) ≤ 2 * M * r ^ n := by
    apply (div_le_iff₀ (by linarith only [hr1] : 0 < 1 - r)).mpr
    have ht := mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hM (pow_nonneg hr0 n)))
    nlinarith only [ht]
  rw [norm_sub_rev]
  exact hh.trans hlast

/-- In particular the linear Taylor remainder is uniformly quadratic. -/
theorem boundedCauchy_linear_remainder (f : ℂ → E) (R : ℝ≥0) (hR : 0 < R)
    (M : ℝ) (hM : 0 ≤ M)
    (hf : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ < (R : ℝ) / 2) :
    ‖f z - f 0 - z • deriv f 0‖ ≤ 2 * M * (‖z‖ / R) ^ 2 := by
  have hs : cauchyPowerSeries f 0 R 1 (fun _ => z) =
      z • cauchyPowerSeries f 0 R 1 (fun _ => 1) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, smul_eq_mul, mul_one]
      using (cauchyPowerSeries f 0 R 1).map_smul_univ (fun _ => z) (fun _ => (1 : ℂ))
  have he : (cauchyPowerSeries f 0 R).partialSum 2 z = f 0 + z • deriv f 0 := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hf.coeff_zero, hs, hf.hasFPowerSeriesAt.deriv]
  have hh := boundedCauchy_partialSum_remainder f R hR M hM hf hb z hz 2
  rw [he] at hh
  simpa only [sub_add_eq_sub_sub] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! Unit-window smoothing for a hierarchy with finite higher growth constants. -/

def energyGrowthSmoothingConstant (A P : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | q + 1 => P (q + 1) * A q * energyGrowthSmoothingConstant A P q

theorem energyGrowthSmoothingConstant_nonneg (A P : ℕ → ℝ)
    (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j) (q : ℕ) :
    0 ≤ energyGrowthSmoothingConstant A P q := by
  induction q with
  | zero => norm_num [energyGrowthSmoothingConstant]
  | succ q ih => exact mul_nonneg (mul_nonneg (hP (q + 1)) (hA q)) ih

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CycleWords

/-! Weak scalar measurability in a separable real Hilbert space. -/

theorem orthonormal_set_countable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology E] (s : Set E)
    (hs : Orthonormal ℝ (fun x : s => (x : E))) : s.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof s).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext x
  constructor
  · intro hx
    have hxy : x = y := by
      by_contra hne
      have hinner := hs.inner_eq_zero (show (⟨x, hx.2⟩ : s) ≠ ⟨y, hy⟩ from
        fun he => hne (congrArg Subtype.val he))
      have hnormx := hs.norm_eq_one (⟨x, hx.2⟩ : s)
      have hnormy := hs.norm_eq_one (⟨y, hy⟩ : s)
      have hsq := norm_sub_sq_real x y
      have hdist : ‖x - y‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx.1
      dsimp only at hinner hnormx hnormy
      nlinarith [norm_nonneg (x - y)]
    exact mem_singleton_iff.mpr hxy
  · intro hx
    rcases mem_singleton_iff.mp hx with rfl
    exact ⟨Metric.mem_ball_self (by norm_num), hy⟩

theorem hilbert_time_aestronglyMeasurable_of_weak
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] (μ : Measure X) (F : X → E)
    (hF : ∀ e : E, AEStronglyMeasurable (fun t => inner ℝ e (F t)) μ) :
    AEStronglyMeasurable F μ := by
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis (𝕜 := ℝ) (E := E)
  have hs : s.Countable := orthonormal_set_countable s (by
    simpa only [hb] using b.orthonormal)
  let : Countable s := hs.to_subtype
  exact hilbert_time_aestronglyMeasurable_of_coordinates b μ F (fun i => hF (b i))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A graded moment reserve solves the descending response recurrence with a
small factor at each metric insertion and no family cardinality dependence. -/

variable {ι : Type*} [Fintype ι]

def ennResponseMassMajorant (R ε : ℝ≥0∞) (d : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => R * d 0
  | j + 1 => R * (d (j + 1) + ε * ennResponseMassMajorant R ε d j)

theorem ennResponse_initial_moment_mass_bounded_le (rank : ι → ℕ) (H J n p M : ℕ) (hreserve : n + (J + H) * p ≤ M)
    (hrank : ∀ v, rank v ≤ H) (b : ι → ι → ℝ≥0∞)
    (hb : ∀ v u, 0 ≤ b v u) (hcol : ∀ u, ∑ v, b v u ≤ 1)
    (hsupport : ∀ v u, b v u ≠ 0 → rank u < rank v)
    (A ε : ℝ≥0∞) (hA : 0 ≤ A) (_hε : 0 ≤ ε)
    (d : ℕ → ι → ℕ → ℝ≥0∞) (hd : ∀ j v q, 0 ≤ d j v q)
    (e : ℕ → ι → ℕ → ℝ≥0∞)
    (hemono : ∀ j v q q', q ≤ q' → e j v q ≤ e j v q')
    (h0 : ∀ v q, q + rank v * p ≤ M → e 0 v q ≤ d 0 v q + A * ∑ u, b v u * e 0 u (q + p))
    (hs : ∀ j v q, j + 1 ≤ J → q + (j + 1 + rank v) * p ≤ M → e (j + 1) v q ≤ d (j + 1) v q + A * ε * e j v (q + p) +
      A * ∑ u, b v u * e (j + 1) u (q + p)) :
    ∀ j ≤ J, (∑ v, e j v (n + (J - j + H - rank v) * p)) ≤
      ennResponseMassMajorant ((1 + A) ^ (H + 1)) ε
        (fun l => ∑ v, d l v (n + (J - l + H - rank v) * p)) j := by
  let R := (1 + A) ^ (H + 1)
  have _hR : 0 ≤ R := by dsimp [R]; positivity
  have hbase : (1 + A) ^ H ≤ R := by
    dsimp [R]
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (le_self_add)
  have hstep : (1 + A) ^ H * A ≤ R := by
    dsimp [R]
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
  have hshift (j : ℕ) (v u : ι) (hvu : rank u < rank v) :
      n + (J - j + H - rank v) * p + p ≤ n + (J - j + H - rank u) * p := by
    have hc : J - j + H - rank v + 1 ≤ J - j + H - rank u := by
      have hv := hrank v
      omega
    have hh := Nat.mul_le_mul_right p hc
    simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using Nat.add_le_add_left hh n
  have hgraph (j : ℕ) (v : ι) :
      (∑ u, b v u * e j u (n + (J - j + H - rank v) * p + p)) ≤
      ∑ u, b v u * e j u (n + (J - j + H - rank u) * p) := by
    apply Finset.sum_le_sum
    intro u _
    by_cases hz : b v u = 0
    · simp only [hz, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left
        (hemono j u _ _ (hshift j v u (hsupport v u hz))) (hb v u)
  intro j
  induction j with
  | zero =>
    intro _
    have henergy (v : ι) : e 0 v (n + (J - 0 + H - rank v) * p) ≤
        d 0 v (n + (J - 0 + H - rank v) * p) +
          A * ∑ u, b v u * e 0 u (n + (J - 0 + H - rank u) * p) := by
      have hc : n + (J - 0 + H - rank v) * p + rank v * p ≤ M := by
        have hv := hrank v
        have heq : J - 0 + H - rank v + rank v = J + H := by omega
        calc
          _ = n + (J - 0 + H - rank v + rank v) * p := by ring
          _ = n + (J + H) * p := by rw [heq]
          _ ≤ M := hreserve
      apply (h0 v _ hc).trans
      apply add_le_add
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_left (hgraph 0 v) hA
    have hh := ennRank_energy_sum_le rank H hrank b hcol hsupport A
      (fun v => e 0 v (n + (J - 0 + H - rank v) * p))
      (fun v => d 0 v (n + (J - 0 + H - rank v) * p)) henergy
    have ht := hh.trans (mul_le_mul_of_nonneg_right hbase
      (Finset.sum_nonneg (s := Finset.univ) (fun v _ => hd 0 v _)))
    simpa only [R, ennResponseMassMajorant, Nat.sub_zero] using ht
  | succ j ih =>
    intro hj
    have hm (v : ι) : n + (J - (j + 1) + H - rank v) * p + p =
        n + (J - j + H - rank v) * p := by
      have hv := hrank v
      have hc : J - (j + 1) + H - rank v + 1 = J - j + H - rank v := by omega
      calc
        _ = n + (J - (j + 1) + H - rank v + 1) * p := by ring
        _ = _ := by rw [hc]
    have henergy (v : ι) : e (j + 1) v (n + (J - (j + 1) + H - rank v) * p) ≤
        d (j + 1) v (n + (J - (j + 1) + H - rank v) * p) +
        A * ε * e j v (n + (J - j + H - rank v) * p) +
          A * ∑ u, b v u * e (j + 1) u (n + (J - (j + 1) + H - rank u) * p) := by
      have hc : n + (J - (j + 1) + H - rank v) * p + (j + 1 + rank v) * p ≤ M := by
        have hv := hrank v
        have heq : J - (j + 1) + H - rank v + (j + 1 + rank v) = J + H := by omega
        calc
          _ = n + (J - (j + 1) + H - rank v + (j + 1 + rank v)) * p := by ring
          _ = n + (J + H) * p := by rw [heq]
          _ ≤ M := hreserve
      have hh := hs j v (n + (J - (j + 1) + H - rank v) * p) hj hc
      have hg := hgraph (j + 1) v
      rw [hm v] at hh hg
      apply hh.trans
      apply add_le_add
      · apply add_le_add
        · exact le_rfl
        · exact le_rfl
      · exact mul_le_mul_of_nonneg_left hg hA
    have hh := ennRank_energy_sum_le rank H hrank b hcol hsupport A
      (fun v => e (j + 1) v (n + (J - (j + 1) + H - rank v) * p))
      (fun v => d (j + 1) v (n + (J - (j + 1) + H - rank v) * p) +
        A * ε * e j v (n + (J - j + H - rank v) * p))
      henergy
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    have hi := mul_le_mul_right (ih (by omega)) (R * ε)
    calc
      _ ≤ _ := hh
      _ = (1 + A) ^ H * (∑ v, d (j + 1) v (n + (J - (j + 1) + H - rank v) * p)) +
          ((1 + A) ^ H * A) * ε * (∑ v, e j v (n + (J - j + H - rank v) * p)) := by ring
      _ ≤ R * (∑ v, d (j + 1) v (n + (J - (j + 1) + H - rank v) * p)) +
          R * ε * (∑ v, e j v (n + (J - j + H - rank v) * p)) :=
        add_le_add (mul_le_mul_left hbase _) (mul_le_mul_left (mul_le_mul_left hstep ε) _)
      _ ≤ R * (∑ v, d (j + 1) v (n + (J - (j + 1) + H - rank v) * p)) +
          R * ε * ennResponseMassMajorant R ε (fun l => ∑ v, d l v (n + (J - l + H - rank v) * p)) j :=
        add_le_add le_rfl hi
      _ = _ := by rw [ennResponseMassMajorant]; ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite families can be combined using superadditivity of the lower integral. -/

theorem finite_sum_lintegral_le {ι T : Type*} [MeasurableSpace T]
    (μ : Measure T) (s : Finset ι) (f : ι → T → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ t, f i t ∂μ) ≤ ∫⁻ t, ∑ i ∈ s, f i t ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add (μ := μ) (f i) (fun t => ∑ j ∈ s, f j t))

theorem family_weighted_lower_energy_budget {ι : Type*} [Fintype ι] {T : Type*}
    [MeasurableSpace T] (μ : Measure T) (mass : ι → ℝ≥0∞)
    (hmass : ∀ i, mass i ≠ ⊤)
    (energy initial : ι → ℝ≥0∞) (forcing : ι → T → ℝ≥0∞) (A : ℝ≥0∞)
    (h : ∀ i, energy i ≤ A * (initial i + 16 * ∫⁻ t, forcing i t ∂μ)) :
    (∑ i, mass i * energy i) ≤
      A * ((∑ i, mass i * initial i) + 16 * ∫⁻ t, ∑ i, mass i * forcing i t ∂μ) := by
  have hf : (∑ i, mass i * ∫⁻ t, forcing i t ∂μ) ≤
      ∫⁻ t, ∑ i, mass i * forcing i t ∂μ := by
    have hh := finite_sum_lintegral_le μ Finset.univ (fun i t => mass i * forcing i t)
    simp only [lintegral_const_mul' _ _ (hmass _)] at hh
    exact hh
  calc
    _ ≤ ∑ i, mass i * (A * (initial i + 16 * ∫⁻ t, forcing i t ∂μ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (h i))
    _ = A * ((∑ i, mass i * initial i) + 16 * ∑ i, mass i * ∫⁻ t, forcing i t ∂μ) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl hf))

end AVRegularity.CycleWords
end
end

section
public section
namespace AVRegularity.CycleWords

/-! The literal metric quadratic symbol is real at real frequencies. -/

theorem fibreQuad_real_star (G : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (hξ : ∀ j, (ξ j).im = 0) : star (fibreQuad G ξ) = fibreQuad G ξ := by
  have hs (j : Fin 2) : star (ξ j) = ξ j := by
    apply Complex.ext
    · rfl
    · simp only [Complex.star_def, Complex.conj_im, hξ j, neg_zero]
  simp only [fibreQuad, star_sum, star_mul, hs, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Finite factorial sums retain the true absolutely continuous energy production. -/

theorem strongTimeRegularity_const_mul {a b : ℝ} {E P : ℝ → ℝ}
    (h : StrongTimeRegularity a b E P) (c : ℝ) :
    StrongTimeRegularity a b (fun t => c * E t) (fun t => c * P t) := by
  refine ⟨h.ac.const_mul c, ?_⟩
  filter_upwards [h.derivative] with t ht
  exact ht.const_mul c

theorem strongTimeRegularity_finset_sum {ι : Type*} {a b : ℝ}
    (S : Finset ι) (E P : ι → ℝ → ℝ)
    (h : ∀ i ∈ S, StrongTimeRegularity a b (E i) (P i)) :
    StrongTimeRegularity a b (fun t => ∑ i ∈ S, E i t) (fun t => ∑ i ∈ S, P i t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, Filter.Eventually.of_forall (fun t => hasDerivAt_const t 0)⟩
    simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hi' := h i (Finset.mem_insert_self i S)
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨hi'.ac.fun_add hs.ac, ?_⟩
    filter_upwards [hi'.derivative, hs.derivative] with t hit hst
    exact hit.fun_add hst

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Literal normal-form terms for ordered frequency differential operators. -/

variable {I V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure FrequencyNormalTerm (I V E F : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] where
  word : List I
  coefficient : V → E →L[ℝ] F

def FrequencyNormalTerm.eval (t : FrequencyNormalTerm I V E F)
    (direction : I → V) (f : V → E) : V → F :=
  fun x => t.coefficient x (frequencyOrderedDerivative direction t.word f x)

def FrequencyNormalTerm.coefficientDerivative (t : FrequencyNormalTerm I V E F)
    (direction : I → V) (i : I) : FrequencyNormalTerm I V E F :=
  ⟨t.word, fun x => fderiv ℝ t.coefficient x (direction i)⟩

def FrequencyNormalTerm.inputDerivative (t : FrequencyNormalTerm I V E F)
    (i : I) : FrequencyNormalTerm I V E F :=
  ⟨t.word ++ [i], t.coefficient⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Combine the defect rate with diffusion coercivity and cutoff absorption. -/

open AVRegularity.Weighted

theorem halfCoercive_cutoff_pointwise_energy_absorption {χ η r M d u f q lam Q R : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hr : r ^ 2 = lam)
    (hQ : (1 / 2 : ℝ) * d ^ 2 ≤ Q)
    (hR : R ≤ q * (8 * χ * η * M * u ^ 2 + 32 * χ * η * r * u ^ 2 +
      40 * χ * η * d * u + 2 * χ ^ 2 * r * d * u +
      2 * χ ^ 2 * f * d + 2 * χ ^ 2 * r * f * u + 8 * χ * η * f * u)) :
    2 * lam * χ ^ 2 * q * u ^ 2 + R - 2 * χ ^ 2 * q * Q + (1 / 2) * χ ^ 2 * q * d ^ 2 ≤
      18 * lam * χ ^ 2 * q * u ^ 2 + 8 * q * f ^ 2 +
        (4096 * η ^ 2 + 16 * M * η) * q * u ^ 2 := by
  have hy := mul_le_mul_of_nonneg_left (compact_weight_cutoff_young hχ hχ1 hη hM
    (r := r) (d := d) (u := u) (f := f)) hq
  have hc := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * χ ^ 2 * q by positivity)
  rw [hr] at hy
  nlinarith only [hy, hc, hR]

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! A weak Hilbert limit retains a common norm bound. -/

theorem hilbertWeak_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (v : H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R)
    (hw : ∀ ell : H →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v))) :
    ‖v‖ ≤ R := by
  have hl := hw (innerSL ℝ v)
  have hb : ∀ n, inner ℝ v (u n) ≤ ‖v‖ * R := fun n =>
    (real_inner_le_norm v (u n)).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg v))
  have he : inner ℝ v v ≤ ‖v‖ * R := le_of_tendsto hl (Filter.Eventually.of_forall hb)
  rw [real_inner_self_eq_norm_sq] at he
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (hu 0)
  nlinarith [norm_nonneg v]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Complex Metric
namespace AVRegularity.CycleWords

/-! A bounded native lift with continuous injective readout is genuinely circle integrable. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem injectiveCircleLift_integrable (A : E →L[ℂ] F) (hA : Function.Injective A)
    (f : ℂ → E) (c : ℂ) (R M : ℝ)
    (hcont : Continuous (fun θ : ℝ => A (f (circleMap c R θ))))
    (hbound : ∀ θ : ℝ, ‖f (circleMap c R θ)‖ ≤ M) :
    CircleIntegrable f c R := by
  have he := A.continuous.measurableEmbedding hA
  have hm : Measurable (fun θ : ℝ => f (circleMap c R θ)) :=
    he.measurable_comp_iff.mp hcont.measurable
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr
  exact Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Complex Metric
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! A circle-integrable native lift inherits the genuine Cauchy series through an injective readout. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem injectiveComplex_cauchy_lift (A : E →L[ℂ] F) (hA : Function.Injective A)
    (f : ℂ → E) (c : ℂ) (R : ℝ≥0) (hR : 0 < R)
    (hf : CircleIntegrable f c R) (hlow : DiffContOnCl ℂ (A ∘ f) (ball c R)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R := by
  have he (z : ℂ) (hz : z ∈ ball c R) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ w in C(c, R), (w - z)⁻¹ • f w) = f z := by
    have hn : z ∉ sphere c |(R : ℝ)| := by
      change dist z c ≠ |(R : ℝ)|
      exact ((mem_ball.mp hz).trans_le (le_abs_self (R : ℝ))).ne
    have hi : CircleIntegrable (fun w => (w - z)⁻¹ • f w) c R := by
      simpa only [zpow_neg_one] using hf.sub_zpow_smul (-1) hn
    apply hA
    rw [A.map_smul, complexLinearMap_circleIntegral A _ c R hi]
    have hfun : (fun w => A ((w - z)⁻¹ • f w)) =
        (fun w => (w - z)⁻¹ • (A ∘ f) w) := by
      funext w
      exact A.map_smul _ _
    rw [hfun]
    exact hlow.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
  have hp := hasFPowerSeriesOn_cauchy_integral hf hR
  refine { r_le := hp.r_le, r_pos := hp.r_pos, hasSum := ?_ }
  intro w hw
  have hz : c + w ∈ ball c R := by
    simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
      NNReal.coe_lt_coe, enorm_lt_coe] using hw
  rw [← he (c + w) hz]
  exact hp.hasSum hw

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Clipped enlarged pulse intervals and their finite indexing geometry. -/

def interiorPulseRegionLo (τ a : ℝ) (n : ℤ) : ℝ :=
  max a ((2 * (n : ℝ) + 1) * τ - 3 / 4 * τ)

def interiorPulseRegionHi (τ b : ℝ) (n : ℤ) : ℝ :=
  min b ((2 * (n : ℝ) + 1) * τ + 3 / 4 * τ)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact squared L2 distances of actual representatives. -/

theorem L2_dist_sq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure X) (f g : Lp E 2 μ) :
    dist f g ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [dist_eq_norm, lpTwoHilbert_normSq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx, Pi.sub_apply]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Dominated convergence of literal fields implies convergence of their native L2 classes. -/

section
variable {X I E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {l : Filter I} [l.IsCountablyGenerated]

theorem tendsto_L2Field_of_dominated (f : I → X → E) (f₀ : X → E) (g : X → F)
    (hf : ∀ i, MemLp (f i) 2 μ) (hf₀ : MemLp f₀ 2 μ) (hg : MemLp g 2 μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖g x‖)
    (hb₀ : ∀ᵐ x ∂μ, ‖f₀ x‖ ≤ ‖g x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (f₀ x))) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hf₀.toLp f₀)) := by
  let r := fun i x => f i x - f₀ x
  have hr : ∀ i, MemLp (r i) 2 μ := fun i => (hf i).sub hf₀
  have hdom : ∀ i, ∀ᵐ x ∂μ, ‖r i x‖ ≤ ‖(2 : ℝ) • g x‖ := by
    intro i
    filter_upwards [hb i, hb₀] with x hx hx₀
    change ‖f i x - f₀ x‖ ≤ ‖(2 : ℝ) • g x‖
    rw [norm_smul, show ‖(2 : ℝ)‖ = 2 by norm_num]
    exact (norm_sub_le _ _).trans (by linarith)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => r i x) l (𝓝 0) := by
    filter_upwards [ht] with x hx
    simpa [r] using hx.sub_const (f₀ x)
  have hconv := tendsto_lpNorm_two_of_dominated r (fun x => (2 : ℝ) • g x)
    hr (hg.const_smul 2) hdom hlim
  rw [tendsto_iff_dist_tendsto_zero]
  have he (i : I) : dist ((hf i).toLp (f i)) (hf₀.toLp f₀) = lpNorm (r i) 2 μ := by
    rw [dist_eq_norm, Lp.norm_def, toReal_eLpNorm]
    unfold lpNorm
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf i).toLp (f i)) (hf₀.toLp f₀),
      (hf i).coeFn_toLp, hf₀.coeFn_toLp] with x hx hi h₀
    rw [hx, Pi.sub_apply, hi, h₀]
  simpa only [he] using hconv
end

/-! Uniformly bounded strong operator convergence lifts to L2 fields. -/

section
variable {X E F 𝕜 : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {μ : Measure X}

theorem tendsto_L2OperatorLift (A : ℕ → E →L[𝕜] F) (B : E →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C) (hB : ‖B‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => A n z) atTop (𝓝 (B z))) (f : Lp E 2 μ) :
    Tendsto (fun n => (A n).compLp f) atTop (𝓝 (B.compLp f)) := by
  let r (n : ℕ) (x : X) := A n (f x) - B (f x)
  have he (n : ℕ) : (A n).compLp f - B.compLp f =ᵐ[μ] r n := by
    filter_upwards [Lp.coeFn_sub ((A n).compLp f) (B.compLp f),
      (A n).coeFn_compLp f, B.coeFn_compLp f] with x hx hax hbx
    rw [hx, Pi.sub_apply, hax, hbx]
  have hr (n : ℕ) : MemLp (r n) 2 μ :=
    (Lp.memLp ((A n).compLp f - B.compLp f)).ae_eq (he n)
  let g (x : X) : E := (2 * C) • f x
  have hg : MemLp g 2 μ := (Lp.memLp f).const_smul (2 * C)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖r n x‖ ≤ ‖g x‖ := by
    apply Eventually.of_forall
    intro x
    have hax : ‖A n (f x)‖ ≤ C * ‖f x‖ :=
      ((A n).le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right (hA n) (norm_nonneg _))
    have hbx : ‖B (f x)‖ ≤ C * ‖f x‖ :=
      (B.le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    change ‖A n (f x) - B (f x)‖ ≤ ‖(2 * C) • f x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hC)]
    exact (norm_sub_le _ _).trans (by linarith)
  have ht' : ∀ᵐ x ∂μ, Tendsto (fun n => r n x) atTop (𝓝 0) :=
    Eventually.of_forall fun x => by simpa [r] using (ht (f x)).sub_const (B (f x))
  have hh := tendsto_lpNorm_two_of_dominated r g hr hg hb ht'
  rw [tendsto_iff_dist_tendsto_zero]
  have hn (n : ℕ) : dist ((A n).compLp f) (B.compLp f) = lpNorm (r n) 2 μ := by
    rw [dist_eq_norm, Lp.norm_def, toReal_eLpNorm]
    unfold lpNorm
    congr 1
    exact eLpNorm_congr_ae (he n)
  simpa only [hn] using hh
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Surjectivity survives the genuine pointwise lift to L2 fields. -/

variable {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem liftLinearIsometryL2_surjective (μ : Measure X) (L : E →ₗᵢ[ℝ] F)
    (hL : Function.Surjective L) : Function.Surjective (liftLinearIsometryL2 μ L) := by
  let R := LinearIsometryEquiv.ofSurjective L hL
  intro f
  refine ⟨liftLinearIsometryL2 μ R.symm.toLinearIsometry f, ?_⟩
  apply Lp.ext
  filter_upwards [liftLinearIsometryL2_ae μ L
    (liftLinearIsometryL2 μ R.symm.toLinearIsometry f),
    liftLinearIsometryL2_ae μ R.symm.toLinearIsometry f] with x hx hy
  rw [hx, hy]
  change R (R.symm (f x)) = f x
  exact R.apply_symm_apply (f x)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A measurable weak action inherits square integrability from a possibly nonmeasurable flux majorant. -/

theorem square_linear_majorant {a b c d x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : 0 ≤ x)
    (h : x ≤ c * a + d * b) : x ^ 2 ≤ 2 * c ^ 2 * a ^ 2 + 2 * d ^ 2 * b ^ 2 := by
  have hp : 0 ≤ c * a + d * b := add_nonneg (mul_nonneg hc ha) (mul_nonneg hd hb)
  have hsq : x ^ 2 ≤ (c * a + d * b) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (c * a - d * b)]

theorem memLp_two_of_measurable_linear_majorant
    {X E U V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup U] [NormedAddCommGroup V]
    (μ : Measure X) (F : X → E) (hF : AEStronglyMeasurable F μ)
    (u : X → U) (hu : MemLp u 2 μ) (v : X → V)
    (hv : (∫⁻ t, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ) < ⊤)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hb : ∀ t, ‖F t‖ ≤ c * ‖u t‖ + d * ‖v t‖) : MemLp F 2 μ := by
  have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have huint : (∫⁻ t, ENNReal.ofReal (‖u t‖ ^ 2) ∂μ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun t => sq_nonneg ‖u t‖))).mp hui.hasFiniteIntegral
  have hum : AEMeasurable (fun t => ENNReal.ofReal (‖u t‖ ^ 2)) μ :=
    (hu.aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  apply memLp_two_of_lower_integral_majorant μ F hF
    (fun t => ENNReal.ofReal (2 * c ^ 2) * ENNReal.ofReal (‖u t‖ ^ 2) +
      ENNReal.ofReal (2 * d ^ 2) * ENNReal.ofReal (‖v t‖ ^ 2))
  · exact lower_integral_two_majorants_finite μ _ _ hum huint hv _ _
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · intro t
    have hs := square_linear_majorant (norm_nonneg (u t)) (norm_nonneg (v t)) hc hd
      (norm_nonneg (F t)) (hb t)
    have he := ENNReal.ofReal_le_ofReal hs
    simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * c ^ 2 * ‖u t‖ ^ 2)
      (by positivity : 0 ≤ 2 * d ^ 2 * ‖v t‖ ^ 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * c ^ 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * d ^ 2)] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Time reflection preserves the literal Lp data on the corresponding closed interval. -/

theorem nativeTimeReflection_measurePreserving (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Icc a b))
      (volume.restrict (Icc (-b) (-a))) := by
  simpa only [neg_neg] using cellTimeReverse_measurePreserving_Icc (-b) (-a)

theorem nativeTimeReflection_memLp {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Icc (-b) (-a)))) :
    MemLp (fun t => f (-t)) p (volume.restrict (Icc a b)) := by
  simpa only [neg_neg] using cellTimeReverse_memLp hf

end AVRegularity.CycleWords
end
end

section
public section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! Retained negative-weight dissipation controls the genuine unweighted gradient integral. -/

theorem negativeWeighted_energy_bounds (a b mass initial F : ℝ) (hab : a ≤ b)
    (hm : 0 ≤ mass) (hF : 0 ≤ F) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc a b)) (hgn : ∀ t ∈ Icc a b, 0 ≤ g t)
    (h : Real.exp (-4 * (b - a)) * mass +
      (∫ t in a..b, Real.exp (-4 * (t - a)) * ((3 / 4) * g t)) ≤
      initial + ∫ t in a..b, Real.exp (-4 * (t - a)) * F) :
    mass ≤ Real.exp (4 * (b - a)) * (initial + F / 4) ∧
      (∫ t in a..b, g t) ≤ (4 / 3) * Real.exp (4 * (b - a)) * (initial + F / 4) := by
  let W := fun t => Real.exp (-4 * (t - a))
  have hW : Continuous W := Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
  have hwi : IntervalIntegrable (fun t => W t * ((3 / 4) * g t)) volume a b :=
    (hi.const_mul (3 / 4)).continuousOn_mul hW.continuousOn
  have hbound : initial + (∫ t in a..b, W t * F) ≤ initial + F / 4 := by
    rw [intervalIntegral.integral_mul_const]
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_right (negativeExponential_integral_le a b) hF).trans_eq (by ring))
  have hn : 0 ≤ ∫ t in a..b, W t * ((3 / 4) * g t) :=
    intervalIntegral.integral_nonneg hab (fun t ht => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (by norm_num) (hgn t ht)))
  have hs := h.trans hbound
  constructor
  · apply negativeExponential_cancel
    exact (le_add_of_nonneg_right hn).trans hs
  · have hweight : Real.exp (-4 * (b - a)) * ((3 / 4) * ∫ t in a..b, g t) ≤
        ∫ t in a..b, W t * ((3 / 4) * g t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab ((hi.const_mul _).const_mul _) hwi
      intro t ht
      exact mul_le_mul_of_nonneg_right (negativeExponential_weight_lower a b t ht.2)
        (mul_nonneg (by norm_num) (hgn t ht))
    have hh : Real.exp (-4 * (b - a)) * ((3 / 4) * ∫ t in a..b, g t) ≤ initial + F / 4 := by
      have hm' := mul_nonneg (Real.exp_pos (-4 * (b - a))).le hm
      exact hweight.trans ((le_add_of_nonneg_left hm').trans hs)
    have hc := negativeExponential_cancel (b - a) _ _ hh
    linarith only [hc]

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! The normalized cell gradient has a bound at the inverse duration scale. -/

theorem normalized_gradient_sq_le {e ν B T C d : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T)
    (hd : ν * d ^ 2 ≤ 2 * C * B) :
    ((e / Real.sqrt (B * T)) * d) ^ 2 ≤ 2 * C * ((e ^ 2 / ν) / T) := by
  rw [mul_pow, div_pow, Real.sq_sqrt (mul_pos hB hT).le]
  have hh := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ e ^ 2 / (ν * B * T) by positivity)
  convert hh using 1 <;> field_simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Leibniz recombination preserves a normalized radius in every factor. -/

theorem normalized_scalar_jet_product_le (J : ℕ) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (J : ℕ) f) (hg : ContDiff ℝ (J : ℕ) g)
    {ρ A B : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : Vec 2)
    (hfb : ∀ j ≤ J, ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j ≤ J, ρ ^ j * ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (j : ℕ) (hj : j ≤ J) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => f x * g x) x‖ ≤ 2 ^ J * A * B := by
  have hm := norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hj)
  calc
    _ ≤ ρ ^ j * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      mul_le_mul_of_nonneg_left hm (pow_nonneg hρ j)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : ρ ^ j * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (j - i) g x‖) = (j.choose i : ℝ) *
          (ρ ^ i * ‖iteratedFDeriv ℝ i f x‖) * (ρ ^ (j - i) * ‖iteratedFDeriv ℝ (j - i) g x‖) := by
        have hp : ρ ^ j = ρ ^ i * ρ ^ (j - i) := by
          rw [← pow_add, Nat.add_sub_of_le hij]
        rw [hp]
        ring
      rw [he]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i (hij.trans hj)) (Nat.cast_nonneg _))
        (hgb (j - i) ((Nat.sub_le _ _).trans hj)) (by positivity) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

end AVRegularity.CycleWords
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual plane Fourier unitary followed by exact lattice fibre rearrangement. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def planeFourierRealIsometry :
    Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ] Lp E 2 (volume : Measure (Vec 2)) where
  toLinearMap := (fourierL2 (F := E)).toLinearMap.restrictScalars ℝ
  norm_map' := fourierL2_norm

def planeBlochCoefficients (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ]
      Lp (lp (fun _ : Fin 2 → ℤ => E) 2) 2 (volume.restrict (planeFrequencyCell a P)) :=
  (planeFrequencyL2Isometry a P hP).comp planeFourierRealIsometry

theorem planeBlochCoefficients_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      planeBlochCoefficients a P hP f θ n = fourierL2 f (planeLatticeEmbedding P n + θ) := by
  have hreal : planeFourierRealIsometry f = fourierL2 f := rfl
  change ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
    planeFrequencyFibreL2 a P hP (planeFourierRealIsometry f) θ n =
      fourierL2 f (planeLatticeEmbedding P n + θ)
  rw [hreal]
  filter_upwards [planeFrequencyFibreL2_ae a P hP (fourierL2 f),
    planeFrequency_L2_fibre_memℓp a P hP (fourierL2 f) (Lp.memLp _)] with θ hθ hm n
  rw [hθ]
  exact planeFrequencyFibre_coeff P _ θ hm n

end AVRegularity.CycleWords
end
end
