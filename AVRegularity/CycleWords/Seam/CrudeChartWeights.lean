-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.Leibniz
public import AVRegularity.CycleWords.Seam.LowPassFibre
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.Interior.ChartWeightBudget
public import AVRegularity.CycleWords.Seam.Adjoint
import AVRegularity.CycleJoint.NativeRawOriginalFamilyTaylorSplitEdges
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Seam

/-! # Pairings of the negative jet norm with smooth tests, and the symmetry of the cutoff

* `pair_le_of_test`: the negative jet norm bounds the pairing with every smooth test of finite
  test norm, compactly supported or not, as long as the pairing is integrable: the cut-off tests
  `spatialCutoff R • φ` (`R ≥ r`) are compactly supported with test norm at most `CutConst L` times that
  of `φ`, and their pairings converge to that of `φ` (dominated convergence).
* `integral_inner_fourierCutoff_comm`: the cutoff `m(D)` is symmetric on square-integrable
  functions (its kernel is even, so the averaging operator is self-adjoint). -/

open AVRegularity.CycleWords.Assembly

section Pair

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- **The negative jet norm against a smooth test of finite test norm.** -/
theorem pair_le_of_test (π : ι → ℝ) (p : ℝ) (L : ℕ) (ϖ : ℝ) {r : ℝ} (hr : 0 < r)
    (g φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v))
    (hint : ∀ v, Integrable (fun z => inner ℝ (g v z) (φ v z)) volume)
    {T : ℝ} (hT : 0 < T)
    (hb : weightedJetNorm π (-p) L ϖ r (fun v _ w z => orderedDerivative w (φ v) z) ≤
      ENNReal.ofReal T) :
    ENNReal.ofReal |∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (φ v z)| ≤
      ENNReal.ofReal (CutConst L * T) * negJetNorm π p L ϖ r g := by
  have hcut : ∀ k : ℕ, ENNReal.ofReal |∑ v, (π v)⁻¹ *
      ∫ z, inner ℝ (g v z) (spatialCutoff (r + k) z • φ v z)| ≤
      ENNReal.ofReal (CutConst L * T) * negJetNorm π p L ϖ r g := by
    intro k
    have hrk : r ≤ r + k := le_add_of_nonneg_right (Nat.cast_nonneg k)
    have hψ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => spatialCutoff (r + k) y • φ v y) ∧
        HasCompactSupport (fun y => spatialCutoff (r + k) y • φ v y) := fun v =>
      ⟨(Cut_contDiff _).smul (hφ v), (Cut_hasCompactSupport (hr.trans_le hrk)).smul_right⟩
    have hb' := (weightedJetNorm_cut_le π (-p) L ϖ hr hrk φ hφ).trans
      (mul_le_mul' le_rfl hb)
    rw [← ENNReal.ofReal_mul (CutConst_pos L).le] at hb'
    exact cutoff_compact_test_pair_le π p L ϖ r g _ hψ _ (mul_pos (CutConst_pos L) hT) hb'
  have hlim : Tendsto (fun k : ℕ => ∑ v, (π v)⁻¹ *
      ∫ z, inner ℝ (g v z) (spatialCutoff (r + k) z • φ v z)) atTop
      (𝓝 (∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z) (φ v z))) := by
    refine tendsto_finsetSum _ fun v _ => Tendsto.const_mul _ ?_
    have he : ∀ k : ℕ, (fun z => inner ℝ (g v z) (spatialCutoff (r + k) z • φ v z)) =
        fun z => spatialCutoff (r + k) z * inner ℝ (g v z) (φ v z) := by
      intro k
      funext z
      rw [real_inner_smul_right]
    simp only [he]
    refine tendsto_integral_of_dominated_convergence (fun z => ‖inner ℝ (g v z) (φ v z)‖)
      (fun k => ((Cut_contDiff (r + k)).continuous.aestronglyMeasurable.mul
        (hint v).aestronglyMeasurable)) (hint v).norm (fun k => ?_) ?_
    · refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Cut_nonneg _ z)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Cut_le_one _ z)
    · refine Eventually.of_forall fun z => ?_
      obtain ⟨k₀, hk₀⟩ := exists_nat_ge ‖z‖
      refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
      have hzk : ‖z‖ ≤ r + k := by
        have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      rw [Cut_eq_one (hr.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg k))) hzk, one_mul]
  have hc := ((ENNReal.continuous_ofReal.comp continuous_abs).tendsto _).comp hlim
  exact le_of_tendsto' hc hcut

end Pair

section Symmetric

theorem integrable_inner_of_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : Vec 2 → E} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun z => inner ℝ (f z) (g z)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp _) (hg.toLp _)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The cutoff kernel is even. -/
theorem cutoffKernel_neg (m : Vec 2 → ℝ) (x : Vec 2) : cutoffKernel m (-x) = cutoffKernel m x := by
  unfold cutoffKernel
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  have hd : vecDot θ (-x) = -vecDot θ x := by
    simp only [vecDot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  simp only [hd, Real.cos_neg]

/-- The cutoff, as an operator on `L²`, is self-adjoint. -/
theorem seamCutoffL2_adjoint (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m) :
    (seamCutoffL2 (E := E) m R hm hs).adjoint = seamCutoffL2 m R hm hs := by
  unfold seamCutoffL2 Analysis.Convolution.planeAveragingOperator
  rw [Analysis.Convolution.averagingOperator_adjoint]
  congr 1
  funext z
  exact cutoffKernel_neg m z

/-- **The cutoff is symmetric** on square-integrable functions. -/
theorem integral_inner_fourierCutoff_comm (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g χ : Vec 2 → E} (hg : MemLp g 2 volume) (hχ : MemLp χ 2 volume) :
    ∫ z, inner ℝ (fourierCutoff m g z) (χ z) = ∫ z, inner ℝ (g z) (fourierCutoff m χ z) := by
  set S := seamCutoffL2 (E := E) m R hm hs
  have hSg : S (hg.toLp g) =ᵐ[volume] fourierCutoff m g := by
    have h1 := seamCutoffL2_ae m R hm hs (hg.toLp g)
    rwa [cutoff_fourierCutoff_congr_ae m hg.coeFn_toLp] at h1
  have hSχ : S (hχ.toLp χ) =ᵐ[volume] fourierCutoff m χ := by
    have h1 := seamCutoffL2_ae m R hm hs (hχ.toLp χ)
    rwa [cutoff_fourierCutoff_congr_ae m hχ.coeFn_toLp] at h1
  have hl : ∫ z, inner ℝ (fourierCutoff m g z) (χ z) = inner ℝ (S (hg.toLp g)) (hχ.toLp χ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hSg, hχ.coeFn_toLp] with z h1 h2
    rw [h1, h2]
  have hr : ∫ z, inner ℝ (g z) (fourierCutoff m χ z) = inner ℝ (hg.toLp g) (S (hχ.toLp χ)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hSχ, hg.coeFn_toLp] with z h1 h2
    rw [h1, h2]
  rw [hl, hr, ← ContinuousLinearMap.adjoint_inner_right, seamCutoffL2_adjoint]

end Symmetric

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The cutoff is bounded on the negative jet norm

`negJetNorm_fourierCutoff_le`: `negJet(m(D)g) ≤ (1 + ∫ |k_m(y)| (2⟨y⟩²)^p dy) negJet(g)` at
every scale `s ≤ 1` and every order and output scale. Against a compact test `φ`, the pairing of
`m(D)g` is `∫ k_m(y) P(y) dy` with `P(y)` the pairing of `g` with the translated test `φ(· + y)`
(`cutoffFamilyPair_complement_eq`); the translation costs `(2⟨s y⟩²)^p ≤ (2⟨y⟩²)^p`
(`cutoff_weightedJetNorm_translation_le`). -/

open AVRegularity.CycleWords.Assembly

section Translate

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

theorem cutoffBracket_mono {s : ℝ} (hs1 : s ^ 2 ≤ 1) (y : Vec 2) :
    cutoffBracket s y ≤ cutoffBracket 1 y := by
  unfold cutoffBracket
  have := mul_le_mul_of_nonneg_right hs1 (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
  linarith

/-- **The pairing with a translated unit test.** -/
theorem familyPair_le (π : ι → ℝ) (p L : ℕ) (s r : ℝ) (g φ : ∀ v, Vec 2 → h v)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v))
    (hb : weightedJetNorm π (-(p : ℝ)) L s r (fun v _ w z => orderedDerivative w (φ v) z) ≤ 1)
    (y : Vec 2) :
    ENNReal.ofReal |cutoffFamilyPair π g φ y| ≤
      ENNReal.ofReal ((2 * cutoffBracket s y) ^ p) * negJetNorm π p L s r g := by
  set χ : ∀ v, Vec 2 → h v := fun v z => φ v (z + y) with hχd
  have hχ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (χ v) ∧ HasCompactSupport (χ v) := fun v =>
    ⟨(hφ v).1.comp (contDiff_id.add contDiff_const),
      (hφ v).2.comp_homeomorph (Homeomorph.addRight y)⟩
  have hshift : weightedJetNorm π (-(p : ℝ)) L s r
      (fun v _ w z => orderedDerivative w (χ v) z) ≤
      ENNReal.ofReal ((2 * cutoffBracket s y) ^ p) := by
    have hd : ∀ (v : ι) (a : ℕ) (w : DerivativeWord2 a),
        orderedDerivative w (χ v) = fun z => orderedDerivative w (φ v) (z + y) :=
      fun v a w => cutoff_orderedDerivative_translate w (φ v) (hφ v).1 y
    simp_rw [hd]
    have hh := cutoff_weightedJetNorm_translation_le π p L s r y
      (fun v _ w z => orderedDerivative w (φ v) z)
      (fun v a w => orderedDerivative_continuous w ((hφ v).1.of_le (by simp)))
    exact hh.trans ((mul_le_mul' le_rfl hb).trans_eq (mul_one _))
  have hA : 0 < (2 * cutoffBracket s y) ^ p :=
    pow_pos (by linarith [cutoffBracket_one_le s y]) p
  have hh := cutoff_compact_test_pair_le π (p : ℝ) L s r g χ hχ _ hA hshift
  simpa only [cutoffFamilyPair, cutoffComponentPair_eq_integral] using hh

end Translate

section Bound

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- The constant of `negJetNorm_fourierCutoff_le`. -/
def NegCutoffConst (m : Vec 2 → ℝ) (p : ℕ) : ℝ := cutoffWeightedMoment (cutoffKernel m) 1 0 p + 1

theorem NegCutoffConst_pos (m : Vec 2 → ℝ) (p : ℕ) : 0 < NegCutoffConst m p := by
  have := cutoffWeightedMoment_nonneg (cutoffKernel m) 1 0 p
  unfold NegCutoffConst
  linarith

/-- **The cutoff is bounded on the negative jet norm.** -/
theorem negJetNorm_fourierCutoff_le (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (π : ι → ℝ) (p L : ℕ) {s : ℝ} (hs1 : s ^ 2 ≤ 1) (r : ℝ)
    (G : ∀ x, Vec 2 → h x) (hG : ∀ x, MemLp (G x) 2 volume) :
    negJetNorm π p L s r (fun x => fourierCutoff m (G x)) ≤
      ENNReal.ofReal (NegCutoffConst m p) * negJetNorm π p L s r G := by
  set N := negJetNorm π p L s r G with hNd
  by_cases hN : N = ⊤
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 (NegCutoffConst_pos m p)).ne']
    exact le_top
  set k := cutoffKernel m with hkd
  have hks : (seamRealCutoffSchwartz m R hm hs : Vec 2 → ℝ) = k := seamRealCutoffSchwartz_eq _ _ _ _
  have hmom : Integrable (fun y => ‖k y‖ * ‖y‖ ^ 0 * (2 * cutoffBracket 1 y) ^ p) := by
    rw [← hks]
    exact cutoff_schwartz_weightedMoment_integrable _ 1 0 p
  have hF2 : ∀ x, MemLp (fourierCutoff m (G x)) 2 volume := fun x =>
    fourierCutoff_memLp_of_memLp m R hm hs (hG x)
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hb => ?_
  have hφ2 : ∀ x, MemLp (φ x) 2 volume := fun x =>
    (hφ x).1.continuous.memLp_of_hasCompactSupport (hφ x).2
  set P := cutoffFamilyPair π G φ with hPd
  have hcomp := cutoffFamilyPair_complement_eq m R hm hs π G φ hG hφ
  have hP0 : P 0 = ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (G x z) (φ x z) := by
    simp only [hPd, cutoffFamilyPair, cutoffComponentPair_eq_integral, add_zero]
  have hsplit : (∑ x, (π x)⁻¹ * ∫ z, inner ℝ (G x z - fourierCutoff m (G x) z) (φ x z)) =
      (∑ x, (π x)⁻¹ * ∫ z, inner ℝ (G x z) (φ x z)) -
        ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (fourierCutoff m (G x) z) (φ x z) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_sub, ← integral_sub (integrable_inner_of_memLp (hG x) (hφ2 x))
      (integrable_inner_of_memLp (hF2 x) (hφ2 x))]
    congr 2
    funext z
    rw [inner_sub_left]
  have hpair : (∑ x, (π x)⁻¹ * ∫ z, inner ℝ (fourierCutoff m (G x) z) (φ x z)) =
      ∫ y, k y * P y := by
    rw [hsplit, ← hP0] at hcomp
    linarith
  rw [hpair]
  have hNr : N = ENNReal.ofReal N.toReal := (ENNReal.ofReal_toReal hN).symm
  have hPy : ∀ y, |P y| ≤ (2 * cutoffBracket s y) ^ p * N.toReal := by
    intro y
    have h1 := familyPair_le π p L s r G φ hφ hb y
    rw [← hNd, hNr, ← ENNReal.ofReal_mul (pow_nonneg (by linarith [cutoffBracket_one_le s y]) _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
      (pow_nonneg (by linarith [cutoffBracket_one_le s y]) _) ENNReal.toReal_nonneg)).1 h1
  have hbd : |∫ y, k y * P y| ≤ cutoffWeightedMoment k 1 0 p * N.toReal := by
    refine (abs_integral_le_integral_abs).trans ?_
    unfold cutoffWeightedMoment
    rw [← integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
      (hmom.mul_const _) (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [abs_mul, pow_zero, mul_one, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hPy y).trans ?_) (abs_nonneg _)
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [cutoffBracket_one_le s y])
      (by linarith [cutoffBracket_mono hs1 y]) p) ENNReal.toReal_nonneg
  calc ENNReal.ofReal |∫ y, k y * P y|
      ≤ ENNReal.ofReal (cutoffWeightedMoment k 1 0 p * N.toReal) := ENNReal.ofReal_le_ofReal hbd
    _ ≤ ENNReal.ofReal (NegCutoffConst m p * N.toReal) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
        unfold NegCutoffConst
        linarith
    _ = ENNReal.ofReal (NegCutoffConst m p) * N := by
        rw [ENNReal.ofReal_mul (NegCutoffConst_pos m p).le, ← hNr]

end Bound

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal SchwartzMap
namespace AVRegularity.CycleWords.Seam

/-! # Test norms of a smoothed field

`weightedJetNorm_conv_le`: for a Schwartz kernel `k` and integrable data `χ`, the test norm of
negative weight `-p` of `k ⋆ χ` is at most a constant times the weighted `L²` norm
`‖⟨s z⟩^{-p} χ‖₂`, with no derivative of `χ`: the derivatives fall on the kernel
(`schwartzConvolution_orderedDerivative`), the weight moves through the convolution at the price
`(2⟨s(z-y)⟩²)^p` of the kernel variable (`cutoff_negative_weight_shift`), and Young's inequality
`L¹ ⋆ L² ⊆ L²` closes (`lintegral_young`, in `lintegral` form). The constant is
`∑_{a ≤ L} r^a/a! ∑_{|w| = a} ∫ |∂^w k| (2⟨s y⟩²)^p dy` (`TestConst`). -/

open AVRegularity.CycleWords.Assembly

section Young

/-- Cauchy–Schwarz for one convolution integral. -/
theorem sq_lintegral_conv_le {K f : Vec 2 → ℝ≥0∞} (hK : Measurable K) (hf : AEMeasurable f)
    (z : Vec 2) :
    (∫⁻ y, K (z - y) * f y) ^ 2 ≤ (∫⁻ x, K x) * ∫⁻ y, K (z - y) * f y ^ 2 := by
  have hKz : Measurable fun y => K (z - y) := hK.comp (measurable_const.sub measurable_id)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.withDensity fun y => K (z - y))
    Real.HolderConjugate.two_two (f := fun _ => 1) (g := f) aemeasurable_const
    (hf.mono_ac (withDensity_absolutelyContinuous _ _))
  rw [lintegral_withDensity_eq_lintegral_mul₀ hKz.aemeasurable (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul₀ hKz.aemeasurable (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul₀ hKz.aemeasurable (hf.pow_const _)] at h
  simp only [Pi.mul_apply, one_pow, mul_one, one_mul, ENNReal.rpow_two] at h
  have hK' : ∫⁻ y, K (z - y) = ∫⁻ x, K x := lintegral_sub_left_eq_self K z
  rw [hK'] at h
  calc (∫⁻ y, K (z - y) * f y) ^ 2
      ≤ ((∫⁻ x, K x) ^ (1 / 2 : ℝ) * (∫⁻ y, K (z - y) * f y ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ x, K x) * ∫⁻ y, K (z - y) * f y ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Young's inequality** `‖K ⋆ f‖₂ ≤ ‖K‖₁ ‖f‖₂` for nonnegative functions, squared. -/
theorem lintegral_young {K f : Vec 2 → ℝ≥0∞} (hK : Measurable K) (hf : AEMeasurable f) :
    ∫⁻ z, (∫⁻ y, K (z - y) * f y) ^ 2 ≤ (∫⁻ x, K x) ^ 2 * ∫⁻ y, f y ^ 2 := by
  have hmeas : AEMeasurable (fun q : Vec 2 × Vec 2 => K (q.1 - q.2) * f q.2 ^ 2)
      (volume.prod volume) :=
    (hK.comp measurable_sub).aemeasurable.mul ((hf.pow_const 2).comp_snd)
  calc ∫⁻ z, (∫⁻ y, K (z - y) * f y) ^ 2
      ≤ ∫⁻ z, (∫⁻ x, K x) * ∫⁻ y, K (z - y) * f y ^ 2 :=
        lintegral_mono fun z => sq_lintegral_conv_le hK hf z
    _ = (∫⁻ x, K x) * ∫⁻ z, ∫⁻ y, K (z - y) * f y ^ 2 :=
        lintegral_const_mul'' _ hmeas.lintegral_prod_right'
    _ = (∫⁻ x, K x) * ∫⁻ y, ∫⁻ z, K (z - y) * f y ^ 2 := by
        rw [lintegral_lintegral_swap hmeas]
    _ = (∫⁻ x, K x) * ∫⁻ y, (∫⁻ x, K x) * f y ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const _ (show Measurable fun z : Vec 2 => K (z - y) from
          hK.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self K y]
    _ = (∫⁻ x, K x) ^ 2 * ∫⁻ y, f y ^ 2 := by
        rw [lintegral_const_mul'' _ (hf.pow_const 2), ← mul_assoc, sq]

/-- **Young's inequality in `L²`** for a function dominated by a nonnegative convolution. -/
theorem eLpNorm_le_of_conv {F : Vec 2 → ℝ} (hFm : AEStronglyMeasurable F volume)
    {K f : Vec 2 → ℝ≥0∞} (hK : Measurable K) (hf : AEMeasurable f)
    (hF : ∀ z, ‖F z‖ₑ ≤ ∫⁻ y, K (z - y) * f y) :
    eLpNorm F 2 volume ≤ (∫⁻ x, K x) * (∫⁻ y, f y ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hFm, eLpNorm'_eq_lintegral_enorm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ z, ‖F z‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ z, (∫⁻ y, K (z - y) * f y) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun z => pow_le_pow_left₀ zero_le (hF z) 2)
          (by norm_num)
    _ ≤ ((∫⁻ x, K x) ^ 2 * ∫⁻ y, f y ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_young hK hf) (by norm_num)
    _ = (∫⁻ x, K x) * (∫⁻ y, f y ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

end Young

section Component

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cutoffBracket_sub_comm (s : ℝ) (x y : Vec 2) :
    cutoffBracket s (x - y) = cutoffBracket s (y - x) := by
  unfold cutoffBracket
  simp only [Pi.sub_apply]
  ring

/-- The inverse weight passes through one value of the kernel. -/
theorem weight_conv_pointwise (s : ℝ) (p : ℕ) {a b : ℝ} (z y : Vec 2) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    cutoffBracket s z ^ (-(p : ℝ) / 2) * (a * b) ≤
      (a * (2 * cutoffBracket s (z - y)) ^ p) * (cutoffBracket s y ^ (-(p : ℝ) / 2) * b) := by
  have h := cutoff_negative_weight_shift s p z (y - z)
  rw [show z + (y - z) = y by abel, ← cutoffBracket_sub_comm] at h
  calc cutoffBracket s z ^ (-(p : ℝ) / 2) * (a * b)
      ≤ ((2 * cutoffBracket s (z - y)) ^ p * cutoffBracket s y ^ (-(p : ℝ) / 2)) * (a * b) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg ha hb)
    _ = _ := by ring

theorem weight_nonneg' (s : ℝ) (q : ℝ) (z : Vec 2) : 0 ≤ cutoffBracket s z ^ q :=
  Real.rpow_nonneg (zero_le_one.trans (cutoffBracket_one_le s z)) _

theorem weight_continuous' (s q : ℝ) : Continuous fun z : Vec 2 => cutoffBracket s z ^ (q / 2) :=
  weight_continuous s q

/-- **The weighted `L²` norm of a smoothed function.** -/
theorem eLpNorm_weighted_conv_le (k : 𝓢(Vec 2, ℝ)) (s : ℝ) (p : ℕ) {χ : Vec 2 → E}
    (hχ : Integrable χ) :
    eLpNorm (fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) * ‖schwartzConvolution k χ z‖) 2
        volume ≤
      ENNReal.ofReal (cutoffWeightedMoment k s 0 p) *
        eLpNorm (fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) * ‖χ z‖) 2 volume := by
  set w : Vec 2 → ℝ := fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) with hw
  have hwc : Continuous w := weight_continuous' s (-(p : ℝ))
  have hw0 : ∀ z, 0 ≤ w z := fun z => weight_nonneg' s _ z
  set K : Vec 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (‖k x‖ * (2 * cutoffBracket s x) ^ p) with hKd
  have hK : Measurable K := by
    refine Measurable.ennreal_ofReal ?_
    refine (k.continuous.norm.mul ((continuous_const.mul ?_).pow p)).measurable
    unfold cutoffBracket
    fun_prop
  set g : Vec 2 → ℝ := fun y => w y * ‖χ y‖ with hgd
  have hg : AEStronglyMeasurable g volume :=
    hwc.aestronglyMeasurable.mul hχ.aestronglyMeasurable.norm
  set f : Vec 2 → ℝ≥0∞ := fun y => ‖g y‖ₑ with hfd
  have hf : AEMeasurable f := hg.aemeasurable.enorm
  have hFm : AEStronglyMeasurable (fun z => w z * ‖schwartzConvolution k χ z‖) volume :=
    (hwc.mul (schwartzConvolution_contDiff k χ hχ).continuous.norm).aestronglyMeasurable
  have hpt : ∀ z, ‖w z * ‖schwartzConvolution k χ z‖‖ₑ ≤ ∫⁻ y, K (z - y) * f y := by
    intro z
    have h1 : ‖schwartzConvolution k χ z‖ₑ ≤ ∫⁻ y, ‖k (z - y)‖ₑ * ‖χ y‖ₑ := by
      unfold schwartzConvolution
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      rw [enorm_smul]
    rw [enorm_mul, Real.enorm_eq_ofReal (hw0 z), enorm_norm]
    calc ENNReal.ofReal (w z) * ‖schwartzConvolution k χ z‖ₑ
        ≤ ENNReal.ofReal (w z) * ∫⁻ y, ‖k (z - y)‖ₑ * ‖χ y‖ₑ := mul_le_mul_right h1 _
      _ = ∫⁻ y, ENNReal.ofReal (w z) * (‖k (z - y)‖ₑ * ‖χ y‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y, K (z - y) * f y := lintegral_mono fun y => ?_
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (hw0 z)]
    simp only [hfd, hgd, hKd]
    rw [Real.enorm_eq_ofReal (mul_nonneg (hw0 y) (norm_nonneg _)), ← ENNReal.ofReal_mul
      (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [cutoffBracket_one_le s (z - y)]) _))]
    exact ENNReal.ofReal_le_ofReal
      (weight_conv_pointwise s p z y (norm_nonneg _) (norm_nonneg _))
  have hY := eLpNorm_le_of_conv hFm hK hf hpt
  have hKint : ∫⁻ x, K x = ENNReal.ofReal (cutoffWeightedMoment k s 0 p) := by
    unfold cutoffWeightedMoment
    rw [ofReal_integral_eq_lintegral_ofReal (cutoff_schwartz_weightedMoment_integrable k s 0 p)
      (Eventually.of_forall fun y => mul_nonneg (mul_nonneg (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _))
        (pow_nonneg (by linarith [cutoffBracket_one_le s y]) _))]
    refine lintegral_congr fun y => ?_
    simp only [hKd, pow_zero, mul_one]
  have hfint : (∫⁻ y, f y ^ 2) ^ (1 / 2 : ℝ) = eLpNorm g 2 volume := by
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hg, eLpNorm'_eq_lintegral_enorm]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hfd]
  rw [hKint, hfint] at hY
  exact hY

end Component

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The kernel mass of the derivatives of order `a`. -/
def KernelMass (k : 𝓢(Vec 2, ℝ)) (s : ℝ) (p a : ℕ) : ℝ :=
  ∑ w : DerivativeWord2 a, cutoffWeightedMoment (schwartzWordKernel (List.ofFn w) k) s 0 p

theorem KernelMass_nonneg (k : 𝓢(Vec 2, ℝ)) (s : ℝ) (p a : ℕ) : 0 ≤ KernelMass k s p a :=
  Finset.sum_nonneg fun _ _ => cutoffWeightedMoment_nonneg _ _ _ _

/-- The constant of the test norm of a smoothed family. -/
def TestConst (k : 𝓢(Vec 2, ℝ)) (s r : ℝ) (p L : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (L + 1), r ^ a / (a.factorial : ℝ) * KernelMass k s p a

theorem TestConst_nonneg (k : 𝓢(Vec 2, ℝ)) (s : ℝ) {r : ℝ} (hr : 0 ≤ r) (p L : ℕ) :
    0 ≤ TestConst k s r p L :=
  Finset.sum_nonneg fun a _ => mul_nonneg (div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
    (KernelMass_nonneg k s p a)

/-- **The test norm of a smoothed family** by the weighted `L²` norm of the data. -/
theorem weightedJetNorm_conv_le (π : ι → ℝ) (k : 𝓢(Vec 2, ℝ)) (s : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (p L : ℕ) (χ : ∀ v, Vec 2 → h v) (hχ : ∀ v, Integrable (χ v)) :
    weightedJetNorm π (-(p : ℝ)) L s r
        (fun v _ w z => orderedDerivative w (schwartzConvolution k (χ v)) z) ≤
      ENNReal.ofReal (TestConst k s r p L) *
        familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹))
          (fun v => eLpNorm (fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) * ‖χ v z‖) 2 volume) := by
  set c : ι → ℝ≥0∞ := fun v => ENNReal.ofReal ((π v)⁻¹) with hc
  set N := familyNorm c
    (fun v => eLpNorm (fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) * ‖χ v z‖) 2 volume) with hN
  rw [cutoff_weightedJetNorm_eq_sum π (-(p : ℝ)) s r (fun v => schwartzConvolution k (χ v)) L]
  have hterm : ∀ a ∈ Finset.range (L + 1),
      ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        cutoffJetSize π (-(p : ℝ)) s (fun v => schwartzConvolution k (χ v)) a ≤
      ENNReal.ofReal (r ^ a / (a.factorial : ℝ) * KernelMass k s p a) * N := by
    intro a _
    rw [ENNReal.ofReal_mul (div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _)), mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [cutoffJetSize_eq_familyNorm]
    set F : DerivativeWord2 a → ∀ v, Vec 2 → ℝ := fun w v z =>
      cutoffBracket s z ^ (-(p : ℝ) / 2) *
        ‖orderedDerivative w (schwartzConvolution k (χ v)) z‖ with hF
    have hmaj := familyNorm_eLpNorm_majorant c Finset.univ (fun _ => (1 : ℝ))
      (fun _ _ => zero_le_one)
      (fun v z => cutoffBracket s z ^ (-(p : ℝ) / 2) *
        wordSize a (fun w : DerivativeWord2 a =>
          orderedDerivative w (schwartzConvolution k (χ v)) z))
      (fun v => ((weight_continuous' s (-(p : ℝ))).mul
        (Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ =>
          ((orderedDerivative_continuous w
            ((schwartzConvolution_contDiff k (χ v) (hχ v)).of_le (by simp))).norm.pow 2)))).aestronglyMeasurable)
      F (fun v z => by
        rw [abs_of_nonneg (mul_nonneg (weight_nonneg' s _ z) (wordSize_nonneg _))]
        simp only [hF, one_mul, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg' s _ z)
        unfold wordSize
        rw [Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    refine hmaj.trans ?_
    have hw : ∀ w : DerivativeWord2 a,
        familyNorm c (fun v => eLpNorm (F w v) 2 volume) ≤
          ENNReal.ofReal (cutoffWeightedMoment (schwartzWordKernel (List.ofFn w) k) s 0 p) * N := by
      intro w
      rw [hN, ← familyNorm_mul]
      refine familyNorm_mono c fun v => ?_
      simp only [hF]
      rw [schwartzConvolution_orderedDerivative w k (χ v) (hχ v)]
      exact eLpNorm_weighted_conv_le _ s p (hχ v)
    calc ∑ w : DerivativeWord2 a, ENNReal.ofReal 1 * familyNorm c (fun v => eLpNorm (F w v) 2 volume)
        ≤ ∑ w : DerivativeWord2 a,
            ENNReal.ofReal (cutoffWeightedMoment (schwartzWordKernel (List.ofFn w) k) s 0 p) * N :=
          Finset.sum_le_sum fun w _ => by rw [ENNReal.ofReal_one, one_mul]; exact hw w
      _ = ENNReal.ofReal (KernelMass k s p a) * N := by
          rw [← Finset.sum_mul, KernelMass, ENNReal.ofReal_sum_of_nonneg
            (fun _ _ => cutoffWeightedMoment_nonneg _ _ _ _)]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, TestConst, ENNReal.ofReal_sum_of_nonneg fun a _ =>
    mul_nonneg (div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _)) (KernelMass_nonneg k s p a)]

end Family

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The dual estimate on the transform of one moment family

`trans_dual`: for a family `F ∈ L²` and a moment family `H = ϖ^j y^w F` with `H ∈ L¹`
(`j ≤ n`), the Gaussian-weighted `L²` norm over the cube of the pair of transforms of `H` is at
most a constant times the negative jet norm of `F` with weight `n + 2`, at every order `L`; the
constant depends on `L`, `j`, `c` only.

Proof (duality with the band-limited test). Put `W(θ) = e^{-2c|θ|²/ϖ²} ρ(θ)` with a smooth bump
`ρ = 1` on the cube (`frequencyCubeBump`), the amplitudes `A = W Ĥ_cos`, `B = W Ĥ_sin` and `Ψ = ampFun A B`.
Then `J = ∫ W (|Ĥ_cos|² + |Ĥ_sin|²) = ∑_v π_v⁻¹ ⟨H_v, Ψ_v⟩ = ∑_v π_v⁻¹ ⟨F_v, ϖ^j y^w Ψ_v⟩`
(Fubini, `integral_inner_ampFun`). The test `ϖ^j y^w Ψ` has test norm of weight `-(n+2)` at
most `C ‖Ψ‖_{ϖ⁻¹, L; 0} ≤ C (∫ (1 + |θ|/ϖ)^{2L} W² pair²)^{1/2} ≤ C' J^{1/2}`
(`weightedJetNorm_monomial_le`, `weightedJetNorm_ampFun_le` at `m = 0`, and the Gaussian
absorbs `(1 + |θ|/ϖ)^{2L}`, `gauss_absorb`). The negative norm bounds the pairing
(`pair_le_of_test`): `J ≤ C'' J^{1/2} negJet(F)`. -/

section
open AVRegularity.CycleWords.Assembly

section Weight

/-- A smooth bump, `1` on the closed frequency cube. -/
def frequencyCubeBump : ContDiffBump (0 : Vec 2) where
  rIn := Real.pi
  rOut := 2 * Real.pi
  rIn_pos := Real.pi_pos
  rIn_lt_rOut := by linarith [Real.pi_pos]

theorem Rho_one {θ : Vec 2} (hθ : θ ∈ freqCube) : frequencyCubeBump θ = 1 := by
  refine frequencyCubeBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun i => by
    rw [Real.norm_eq_abs]
    exact hθ i

theorem vecDot_self (θ : Vec 2) : vecDot θ θ = θ 0 ^ 2 + θ 1 ^ 2 := by
  simp [vecDot, Fin.sum_univ_two, sq]

theorem Rho_zero {θ : Vec 2} (hθ : 81 < vecDot θ θ) : frequencyCubeBump θ = 0 := by
  refine frequencyCubeBump.zero_of_le_dist ?_
  rw [dist_zero_right]
  by_contra hlt
  push Not at hlt
  have hi : ∀ i, |θ i| < 2 * Real.pi := fun i =>
    lt_of_le_of_lt (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm θ i) hlt
  have hs : ∀ i, θ i ^ 2 < (2 * Real.pi) ^ 2 := fun i => by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ (hi i) (abs_nonneg _) two_ne_zero
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  rw [vecDot_self] at hθ
  nlinarith [hs 0, hs 1, Real.pi_pos]

/-- The weight `e^{-2c|θ|²/ϖ²} ρ(θ)`. -/
def gaussianBumpWeight (c ϖ : ℝ) (θ : Vec 2) : ℝ := Real.exp (-(2 * c) * (vecDot θ θ / ϖ ^ 2)) * frequencyCubeBump θ

theorem W_nonneg (c ϖ : ℝ) (θ : Vec 2) : 0 ≤ gaussianBumpWeight c ϖ θ :=
  mul_nonneg (Real.exp_pos _).le frequencyCubeBump.nonneg

theorem W_continuous (c ϖ : ℝ) : Continuous (gaussianBumpWeight c ϖ) := by
  unfold gaussianBumpWeight
  refine (Real.continuous_exp.comp (continuous_const.mul ?_)).mul frequencyCubeBump.continuous
  simp only [vecDot_self]
  fun_prop

theorem W_hasCompactSupport (c ϖ : ℝ) : HasCompactSupport (gaussianBumpWeight c ϖ) :=
  frequencyCubeBump.hasCompactSupport.mul_left

theorem W_zero (c ϖ : ℝ) {θ : Vec 2} (hθ : 81 < vecDot θ θ) : gaussianBumpWeight c ϖ θ = 0 := by
  rw [gaussianBumpWeight, Rho_zero hθ, mul_zero]

theorem W_cube (c ϖ : ℝ) {θ : Vec 2} (hθ : θ ∈ freqCube) :
    gaussianBumpWeight c ϖ θ = Real.exp (-c * (vecDot θ θ / ϖ ^ 2)) ^ 2 := by
  rw [gaussianBumpWeight, Rho_one hθ, mul_one, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The Gaussian absorbs the polynomial weight.** -/
theorem W_absorb {c ϖ : ℝ} (hc : 0 < c) (hϖ : 0 < ϖ) (L : ℕ) (θ : Vec 2) :
    (1 + ‖θ‖ / ϖ) ^ (2 * L) * gaussianBumpWeight c ϖ θ ^ 2 ≤ gaussConst (2 * L) (2 * c) * gaussianBumpWeight c ϖ θ := by
  set t := Real.sqrt (vecDot θ θ) / ϖ with htd
  have ht0 : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hϖ.le
  have ht2 : t ^ 2 = vecDot θ θ / ϖ ^ 2 := by
    rw [htd, div_pow, Real.sq_sqrt (by rw [vecDot_self]; positivity)]
  have hg := gauss_absorb (2 * L) (by linarith : 0 < 2 * c) ht0
  rw [ht2] at hg
  have hnorm : (1 + ‖θ‖ / ϖ) ^ (2 * L) ≤ (1 + t) ^ (2 * L) :=
    pow_le_pow_left₀ (by positivity) (by
      have := div_le_div_of_nonneg_right (norm_le_sqrt_vecDot θ) hϖ.le
      linarith) _
  have hρ0 := frequencyCubeBump.nonneg (x := θ)
  have hρ1 := frequencyCubeBump.le_one (x := θ)
  set e := Real.exp (-(2 * c) * (vecDot θ θ / ϖ ^ 2)) with hed
  have he0 : 0 < e := Real.exp_pos _
  have hW : gaussianBumpWeight c ϖ θ = e * frequencyCubeBump θ := rfl
  rw [hW]
  calc (1 + ‖θ‖ / ϖ) ^ (2 * L) * (e * frequencyCubeBump θ) ^ 2
      = ((1 + ‖θ‖ / ϖ) ^ (2 * L) * e) * (e * (frequencyCubeBump θ * frequencyCubeBump θ)) := by ring
    _ ≤ gaussConst (2 * L) (2 * c) * (e * frequencyCubeBump θ) := by
        refine mul_le_mul ((mul_le_mul_of_nonneg_right hnorm he0.le).trans hg)
          (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hρ0 hρ1) he0.le)
          (by positivity) (gaussConst_pos _ (by linarith)).le

end Weight

section Fubini

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The pairing of the transform with a fixed vector. -/
theorem integral_phase_inner {H : Vec 2 → E} (hH : Integrable H) {ψ : ℝ → ℝ}
    (hψ : IsUnitPhase ψ) (θ : Vec 2) (a : E) :
    ∫ y, ψ (vecDot θ y) * inner ℝ (H y) a = inner ℝ (phaseTransform ψ H θ) a := by
  unfold phaseTransform
  rw [real_inner_comm, ← integral_inner (Trans_integrand_integrable hψ hH θ) a]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ψ (vecDot θ y) * inner ℝ (H y) a = inner ℝ a (ψ (vecDot θ y) • H y)
  rw [real_inner_smul_right, real_inner_comm]

/-- **The pairing with the band-limited test** (Fubini). -/
theorem integral_inner_ampFun {H : Vec 2 → E} (hH : Integrable H) {V : Vec 2 → ℝ}
    (hV : Continuous V) (hVc : HasCompactSupport V) (hV0 : ∀ θ, 81 < vecDot θ θ → V θ = 0) :
    ∫ y, inner ℝ (H y) (ampFun 9 (fun θ => V θ • phaseTransform Real.cos H θ)
      (fun θ => V θ • phaseTransform Real.sin H θ) y) =
      ∫ θ, V θ * (‖phaseTransform Real.cos H θ‖ ^ 2 + ‖phaseTransform Real.sin H θ‖ ^ 2) := by
  set A : Vec 2 → E := fun θ => V θ • phaseTransform Real.cos H θ with hAd
  set B : Vec 2 → E := fun θ => V θ • phaseTransform Real.sin H θ with hBd
  have hAc : Continuous A := hV.smul (Trans_continuous isUnitPhase_cos hH)
  have hBc : Continuous B := hV.smul (Trans_continuous isUnitPhase_sin hH)
  have hAi : Integrable A := hAc.integrable_of_hasCompactSupport hVc.smul_right
  have hBi : Integrable B := hBc.integrable_of_hasCompactSupport hVc.smul_right
  have hzero : ∀ θ : Vec 2, (9 : ℝ) ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0 := by
    intro θ hθ
    have h0 := hV0 θ (by norm_num at hθ ⊢; linarith)
    simp only [hAd, hBd, h0, zero_smul, and_self]
  have hdot : Continuous fun q : Vec 2 × Vec 2 => vecDot q.2 q.1 := by
    unfold vecDot
    fun_prop
  set f : Vec 2 → Vec 2 → ℝ := fun y θ => Real.cos (vecDot θ y) * inner ℝ (H y) (A θ) +
    Real.sin (vecDot θ y) * inner ℝ (H y) (B θ) with hfd
  have hfm : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : Vec 2 × Vec 2 => inner ℝ (H q.1) (A q.2))
        (volume.prod volume) :=
      hH.aestronglyMeasurable.comp_fst.inner (hAc.comp continuous_snd).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : Vec 2 × Vec 2 => inner ℝ (H q.1) (B q.2))
        (volume.prod volume) :=
      hH.aestronglyMeasurable.comp_fst.inner (hBc.comp continuous_snd).aestronglyMeasurable
    exact ((Real.continuous_cos.comp hdot).aestronglyMeasurable.mul h1).add
      ((Real.continuous_sin.comp hdot).aestronglyMeasurable.mul h2)
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    refine (hH.norm.mul_prod (hAi.norm.add hBi.norm)).mono' hfm
      (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, hfd]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Real.norm_eq_abs, Pi.add_apply]
    have h1 := abs_real_inner_le_norm (H q.1) (A q.2)
    have h2 := abs_real_inner_le_norm (H q.1) (B q.2)
    have c1 := Real.abs_cos_le_one (vecDot q.2 q.1)
    have s1 := Real.abs_sin_le_one (vecDot q.2 q.1)
    calc |Real.cos (vecDot q.2 q.1)| * |inner ℝ (H q.1) (A q.2)| +
          |Real.sin (vecDot q.2 q.1)| * |inner ℝ (H q.1) (B q.2)|
        ≤ 1 * (‖H q.1‖ * ‖A q.2‖) + 1 * (‖H q.1‖ * ‖B q.2‖) := by
          gcongr
      _ = ‖H q.1‖ * (‖A q.2‖ + ‖B q.2‖) := by ring
  have hin : ∀ y, inner ℝ (H y) (ampFun 9 A B y) = ∫ θ, f y θ := fun y =>
    inner_ampFun hzero hAi hBi (H y) y
  have hinner : ∀ θ, ∫ y, f y θ = V θ * (‖phaseTransform Real.cos H θ‖ ^ 2 +
      ‖phaseTransform Real.sin H θ‖ ^ 2) := by
    intro θ
    have hc : ∫ y, Real.cos (vecDot θ y) * inner ℝ (H y) (A θ) =
        inner ℝ (phaseTransform Real.cos H θ) (A θ) :=
      integral_phase_inner hH isUnitPhase_cos θ (A θ)
    have hs : ∫ y, Real.sin (vecDot θ y) * inner ℝ (H y) (B θ) =
        inner ℝ (phaseTransform Real.sin H θ) (B θ) :=
      integral_phase_inner hH isUnitPhase_sin θ (B θ)
    have hic : Integrable fun y => Real.cos (vecDot θ y) * inner ℝ (H y) (A θ) := by
      refine ((Trans_integrand_integrable isUnitPhase_cos hH θ).inner_const (A θ)).congr
        (Eventually.of_forall fun y => ?_)
      simp only [real_inner_smul_left]
    have his : Integrable fun y => Real.sin (vecDot θ y) * inner ℝ (H y) (B θ) := by
      refine ((Trans_integrand_integrable isUnitPhase_sin hH θ).inner_const (B θ)).congr
        (Eventually.of_forall fun y => ?_)
      simp only [real_inner_smul_left]
    simp only [hfd]
    rw [integral_add hic his, hc, hs]
    simp only [hAd, hBd, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  simp only [hin]
  rw [integral_integral_swap hfi]
  exact integral_congr_ae (Eventually.of_forall hinner)

end Fubini
end

/-! # The dual estimate for one moment family

`trans_dual`: `∫_cube e^{-2c|θ|²/ϖ²} pair(Ĥ)(θ)² dθ ≤ (C negJet_{n+2}(F))²` for the moment family
`H = ϖ^j y^w F` of a square-integrable family `F` with `H ∈ L¹`, `j ≤ n`; `C = DualConst L j c`. -/

section
open AVRegularity.CycleWords.Assembly

/-- The constant of the dual estimate. -/
def DualConst (L j : ℕ) (c : ℝ) : ℝ :=
  CutConst L * (LeibConst L ^ j * gaussJetConst 0 L * Real.sqrt (gaussConst (2 * L) (2 * c)) + 1)

theorem DualConst_pos (L j : ℕ) (c : ℝ) : 0 < DualConst L j c := by
  unfold DualConst
  have h1 := CutConst_pos L
  have h2 := (LeibConst_pos L).le
  have h3 := (gaussJetConst_pos 0 L).le
  have h4 := Real.sqrt_nonneg (gaussConst (2 * L) (2 * c))
  positivity

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The amplitude jet norm of order `0` of the weighted transforms. -/
theorem ajn0_eq (π : ι → ℝ) (ϖ : ℝ) (V : Vec 2 → ℝ) (hV : ∀ θ, 0 ≤ V θ)
    (H : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    amplitudeJetNorm π 0 ϖ (fun x θ' => V θ' • phaseTransform Real.cos (H x) θ')
        (fun x θ' => V θ' • phaseTransform Real.sin (H x) θ') θ =
      ENNReal.ofReal (V θ) * Pair (fun x => ENNReal.ofReal ((π x)⁻¹)) H θ := by
  have hmi : momentIndices 0 = {(0, 0)} := by decide
  unfold amplitudeJetNorm Pair
  rw [hmi, Finset.sum_singleton]
  simp only [thetaPartial_zero_zero, add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    div_one, ENNReal.ofReal_one, one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hV θ),
    mul_pow, ENNReal.ofReal_mul (sq_nonneg (V θ))]
  have he : ∀ x, ENNReal.ofReal ((π x)⁻¹) * (ENNReal.ofReal (V θ ^ 2) *
      ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) + ENNReal.ofReal (V θ ^ 2) *
        ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2)) =
      ENNReal.ofReal (V θ) ^ 2 * (ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) +
          ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2))) := by
    intro x
    rw [ENNReal.ofReal_pow (hV θ)]
    ring
  simp only [he, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half']

/-- **The dual estimate for one moment family.** -/
theorem trans_dual (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {c : ℝ} (hc : 0 < c) (n L j : ℕ)
    (hj : j ≤ n) (w : DerivativeWord2 j) {ϖ : ℝ} (hϖ : 0 < ϖ) (F : ∀ x, Vec 2 → h x)
    (hH : ∀ x, Integrable (fun y => (ϖ ^ j * wordMonomial w y) • F x y)) :
    ∫⁻ θ in freqCube, (ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) *
        Pair (fun x => ENNReal.ofReal ((π x)⁻¹))
          (fun x y => (ϖ ^ j * wordMonomial w y) • F x y) θ) ^ 2 ≤
      (ENNReal.ofReal (DualConst L j c) * negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ F) ^ 2 := by
  set H : ∀ x, Vec 2 → h x := fun x y => (ϖ ^ j * wordMonomial w y) • F x y with hHd
  set cc : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hcc
  set W := gaussianBumpWeight c ϖ with hWd
  set pair := Pair cc H with hpair
  set J := ∫⁻ θ, ENNReal.ofReal (W θ) * pair θ ^ 2 with hJd
  set N := negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ F with hNd
  have hWc : Continuous W := W_continuous c ϖ
  have hW0 : ∀ θ, 0 ≤ W θ := W_nonneg c ϖ
  -- the cube integral is at most `J`
  have hb : ∫⁻ θ in freqCube, (ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) *
      pair θ) ^ 2 ≤ J := by
    refine (setLIntegral_congr_fun measurableSet_freqCube (fun θ hθ => ?_)).trans_le
      (setLIntegral_le_lintegral _ _)
    rw [hWd, W_cube c ϖ hθ, mul_pow, ENNReal.ofReal_pow (Real.exp_pos _).le]
  -- `J` is finite
  have hTc : ∀ x θ, ‖phaseTransform Real.cos (H x) θ‖ ≤ ∫ y, ‖H x y‖ := fun x θ =>
    Trans_norm_le isUnitPhase_cos (hH x) θ
  have hTs : ∀ x θ, ‖phaseTransform Real.sin (H x) θ‖ ≤ ∫ y, ‖H x y‖ := fun x θ =>
    Trans_norm_le isUnitPhase_sin (hH x) θ
  set Cp : ℝ≥0∞ := ∑ x, cc x * (ENNReal.ofReal ((∫ y, ‖H x y‖) ^ 2) +
    ENNReal.ofReal ((∫ y, ‖H x y‖) ^ 2)) with hCp
  have hpair_le : ∀ θ, pair θ ^ 2 ≤ Cp := by
    intro θ
    rw [hpair, Pair_sq]
    refine Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (add_le_add ?_ ?_)
    · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hTc x θ) 2)
    · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hTs x θ) 2)
  have hCpfin : Cp ≠ ⊤ := (ENNReal.sum_lt_top.2 fun x _ => ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)).ne
  have hWi : Integrable W := hWc.integrable_of_hasCompactSupport (W_hasCompactSupport c ϖ)
  have hJfin : J < ⊤ := by
    calc J ≤ ∫⁻ θ, ENNReal.ofReal (W θ) * Cp :=
          lintegral_mono fun θ => mul_le_mul' le_rfl (hpair_le θ)
      _ = (∫⁻ θ, ENNReal.ofReal (W θ)) * Cp := lintegral_mul_const' _ _ hCpfin
      _ < ⊤ := ENNReal.mul_lt_top hWi.lintegral_lt_top (lt_top_iff_ne_top.2 hCpfin)
  -- the amplitudes and the test
  set A : ∀ x, Vec 2 → h x := fun x θ => W θ • phaseTransform Real.cos (H x) θ with hAd
  set B : ∀ x, Vec 2 → h x := fun x θ => W θ • phaseTransform Real.sin (H x) θ with hBd
  have hAc : ∀ x, Continuous (A x) := fun x => hWc.smul (Trans_continuous isUnitPhase_cos (hH x))
  have hBc : ∀ x, Continuous (B x) := fun x => hWc.smul (Trans_continuous isUnitPhase_sin (hH x))
  have hAi : ∀ x, Integrable (A x) := fun x =>
    (hAc x).integrable_of_hasCompactSupport (W_hasCompactSupport c ϖ).smul_right
  have hBi : ∀ x, Integrable (B x) := fun x =>
    (hBc x).integrable_of_hasCompactSupport (W_hasCompactSupport c ϖ).smul_right
  have hA : ∀ x, IsBandAmp 9 0 (A x) := fun x => ⟨by
      rw [Nat.cast_zero]
      exact contDiff_zero.2 (hAc x), fun θ hθ => by
      have h81 : 81 < vecDot θ θ := by norm_num at hθ; linarith
      simp only [hAd, hWd, W_zero c ϖ h81, zero_smul]⟩
  have hB : ∀ x, IsBandAmp 9 0 (B x) := fun x => ⟨by
      rw [Nat.cast_zero]
      exact contDiff_zero.2 (hBc x), fun θ hθ => by
      have h81 : 81 < vecDot θ θ := by norm_num at hθ; linarith
      simp only [hBd, hWd, W_zero c ϖ h81, zero_smul]⟩
  set Ψ : ∀ x, Vec 2 → h x := fun x => ampFun 9 (A x) (B x) with hΨd
  have hΨs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (Ψ x) := fun x => contDiff_infty.2 fun M =>
    ampFun_contDiff (by norm_num) M (hAi x).integrableOn (hBi x).integrableOn
  set Cψ : ι → ℝ := fun x =>
    ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ 9 ^ 2}, (‖A x θ‖ + ‖B x θ‖) with hCψ
  have hΨb : ∀ x y, ‖Ψ x y‖ ≤ Cψ x := fun x y =>
    norm_ampFun_le (hAi x).integrableOn (hBi x).integrableOn y
  set φ : ∀ x, Vec 2 → h x := fun x y => (ϖ ^ j * wordMonomial w y) • Ψ x y with hφd
  have hφs : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) := fun x =>
    (contDiff_const.mul (wordMonomial_contDiff w)).smul (hΨs x)
  have hpt : ∀ x y, inner ℝ (F x y) (φ x y) = inner ℝ (H x y) (Ψ x y) := by
    intro x y
    simp only [hφd, hHd, real_inner_smul_left, real_inner_smul_right]
  have hint : ∀ x, Integrable (fun y => inner ℝ (F x y) (φ x y)) := by
    intro x
    refine (((hH x).norm.mul_const (Cψ x)).mono'
      ((hH x).aestronglyMeasurable.inner (hΨs x).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)).congr (Eventually.of_forall fun y => (hpt x y).symm)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hΨb x y) (norm_nonneg _))
  set g : ι → Vec 2 → ℝ := fun x θ => W θ * (‖phaseTransform Real.cos (H x) θ‖ ^ 2 +
    ‖phaseTransform Real.sin (H x) θ‖ ^ 2) with hgd
  have hIx : ∀ x, ∫ y, inner ℝ (F x y) (φ x y) = ∫ θ, g x θ := by
    intro x
    rw [integral_congr_ae (Eventually.of_forall (hpt x))]
    exact integral_inner_ampFun (hH x) hWc (W_hasCompactSupport c ϖ)
      (fun θ hθ => W_zero c ϖ hθ)
  have hg0 : ∀ x θ, 0 ≤ g x θ := fun x θ => mul_nonneg (hW0 θ) (by positivity)
  have hgc : ∀ x, Continuous (g x) := fun x => hWc.mul
    (((Trans_continuous isUnitPhase_cos (hH x)).norm.pow 2).add
      ((Trans_continuous isUnitPhase_sin (hH x)).norm.pow 2))
  have hgi : ∀ x, Integrable (g x) := fun x =>
    (hgc x).integrable_of_hasCompactSupport (W_hasCompactSupport c ϖ).mul_right
  set P : ℝ := ∑ x, (π x)⁻¹ * ∫ y, inner ℝ (F x y) (φ x y) with hPd
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ => by
    rw [hIx x]
    exact mul_nonneg (inv_nonneg.2 (hπ x).le) (integral_nonneg (hg0 x))
  have hPJ : ENNReal.ofReal P = J := by
    rw [hPd, ENNReal.ofReal_sum_of_nonneg fun x _ => by
      rw [hIx x]
      exact mul_nonneg (inv_nonneg.2 (hπ x).le) (integral_nonneg (hg0 x))]
    have he : ∀ x, ENNReal.ofReal ((π x)⁻¹ * ∫ y, inner ℝ (F x y) (φ x y)) =
        ∫⁻ θ, cc x * (ENNReal.ofReal (W θ) * (ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) +
          ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2))) := by
      intro x
      rw [hIx x, ENNReal.ofReal_mul (inv_nonneg.2 (hπ x).le),
        ofReal_integral_eq_lintegral_ofReal (hgi x) (Eventually.of_forall (hg0 x)),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun θ => ?_
      simp only [hgd, hcc]
      rw [ENNReal.ofReal_mul (hW0 θ), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    simp only [he]
    rw [← lintegral_finsetSum' _ fun x _ => ?_]
    · refine lintegral_congr fun θ => ?_
      rw [hpair, Pair_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    · refine (Measurable.const_mul ?_ _).aemeasurable
      exact hWc.measurable.ennreal_ofReal.mul
        (((Trans_continuous isUnitPhase_cos (hH x)).norm.pow 2).measurable.ennreal_ofReal.add
          ((Trans_continuous isUnitPhase_sin (hH x)).norm.pow 2).measurable.ennreal_ofReal)
  -- the test norm
  obtain ⟨GC, hGC⟩ : ∃ GC : ℝ, GC = gaussConst (2 * L) (2 * c) := ⟨_, rfl⟩
  have hGC0 : 0 < GC := hGC ▸ gaussConst_pos _ (by linarith)
  obtain ⟨TC, hTCd⟩ : ∃ TC : ℝ, TC = LeibConst L ^ j * gaussJetConst 0 L * Real.sqrt GC :=
    ⟨_, rfl⟩
  have hL0 := (LeibConst_pos L).le
  have hg0 := (gaussJetConst_pos 0 L).le
  have hTC0 : 0 ≤ TC := by
    rw [hTCd]
    positivity
  have hr : (0 : ℝ) < ϖ⁻¹ := inv_pos.2 hϖ
  have hϖr : ϖ ≤ (ϖ⁻¹)⁻¹ := by rw [inv_inv]
  have hAJ : ampJetIntegral π 0 L ϖ A B ≤ ENNReal.ofReal GC * J := by
    unfold ampJetIntegral
    rw [hJd, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [hAd, hBd, ajn0_eq π ϖ W hW0 H θ]
    set a : ℝ := 1 + ‖θ‖ / ϖ with had
    have ha0 : 0 ≤ a := by positivity
    have e1 : (ENNReal.ofReal (a ^ L) * (ENNReal.ofReal (W θ) * pair θ)) ^ 2 =
        ENNReal.ofReal (a ^ (2 * L) * W θ ^ 2) * pair θ ^ 2 := by
      have h1 : ENNReal.ofReal (a ^ (2 * L) * W θ ^ 2) =
          ENNReal.ofReal (a ^ L) ^ 2 * ENNReal.ofReal (W θ) ^ 2 := by
        rw [ENNReal.ofReal_mul (pow_nonneg ha0 _), ENNReal.ofReal_pow (hW0 θ),
          show a ^ (2 * L) = (a ^ L) ^ 2 by ring, ENNReal.ofReal_pow (pow_nonneg ha0 L)]
      rw [h1]
      ring
    rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul hGC0.le]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [hGC]
    exact W_absorb hc hϖ L θ
  have htest : weightedJetNorm π (-(((n + 2 : ℕ) : ℝ))) L ϖ ϖ⁻¹
      (fun x _ u z => orderedDerivative u (φ x) z) ≤ ENNReal.ofReal TC * J ^ (1 / 2 : ℝ) := by
    have hmono := weightedJetNorm_monomial_le π L hϖ.le hr hϖr j w
      (-(((n + 2 : ℕ) : ℝ))) Ψ hΨs
    have hwm := weightedJetNorm_weight_mono π (q := -(((n + 2 : ℕ) : ℝ)) + j)
      (q' := ((0 : ℕ) : ℝ)) (by
        have : (j : ℝ) ≤ n := by exact_mod_cast hj
        push_cast
        linarith) L ϖ ϖ⁻¹ (fun v _ u z => orderedDerivative u (Ψ v) z)
      (fun v a u => orderedDerivative_continuous u ((hΨs v).of_le (by simp)))
    have hamp := weightedJetNorm_ampFun_le π (r := 9) (by norm_num) (m := 0) (M := L) hϖ hA hB
    have hroot : ampJetIntegral π 0 L ϖ A B ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt GC) * J ^ (1 / 2 : ℝ) := by
      refine (ENNReal.rpow_le_rpow hAJ (by norm_num)).trans (le_of_eq ?_)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hGC0.le (by norm_num), Real.sqrt_eq_rpow]
    have hc3 : ENNReal.ofReal TC = ENNReal.ofReal (LeibConst L ^ j) *
        (ENNReal.ofReal (gaussJetConst 0 L) * ENNReal.ofReal (Real.sqrt GC)) := by
      rw [hTCd, ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hL0 _) hg0),
        ENNReal.ofReal_mul (pow_nonneg hL0 _), mul_assoc]
    calc weightedJetNorm π (-(((n + 2 : ℕ) : ℝ))) L ϖ ϖ⁻¹
          (fun x _ u z => orderedDerivative u (φ x) z)
        ≤ ENNReal.ofReal (LeibConst L ^ j) *
            (ENNReal.ofReal (gaussJetConst 0 L) *
              (ENNReal.ofReal (Real.sqrt GC) * J ^ (1 / 2 : ℝ))) :=
          hmono.trans (mul_le_mul' le_rfl (hwm.trans (hamp.trans (mul_le_mul' le_rfl hroot))))
      _ = ENNReal.ofReal TC * J ^ (1 / 2 : ℝ) := by
          rw [hc3]
          ring
  -- conclusion
  by_cases hJ0 : J = 0
  · exact hb.trans (by rw [hJ0]; exact zero_le)
  have hJh : J ^ (1 / 2 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hJ0) hJfin.ne).ne'
  have hJh' : J ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hJfin.ne
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = (TC + 1) * (J ^ (1 / 2 : ℝ)).toReal := ⟨_, rfl⟩
  have hTC1 : (0 : ℝ) ≤ TC + 1 := by linarith
  have hT : 0 < T := by
    rw [hTd]
    exact mul_pos (by linarith) (ENNReal.toReal_pos hJh hJh')
  have hofT : ENNReal.ofReal T = ENNReal.ofReal (TC + 1) * J ^ (1 / 2 : ℝ) := by
    rw [hTd, ENNReal.ofReal_mul hTC1, ENNReal.ofReal_toReal hJh']
  have htest' : weightedJetNorm π (-(((n + 2 : ℕ) : ℝ))) L ϖ ϖ⁻¹
      (fun x _ u z => orderedDerivative u (φ x) z) ≤ ENNReal.ofReal T := by
    refine htest.trans ?_
    rw [hofT]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  have hE := pair_le_of_test π ((n + 2 : ℕ) : ℝ) L ϖ hr F φ hφs hint hT htest'
  rw [← hPd, abs_of_nonneg hP0, hPJ, ← hNd] at hE
  have hD : ENNReal.ofReal (CutConst L * T) =
      ENNReal.ofReal (DualConst L j c) * J ^ (1 / 2 : ℝ) := by
    have hD' : DualConst L j c = CutConst L * (TC + 1) := by
      rw [DualConst, hTCd, hGC]
    rw [ENNReal.ofReal_mul (CutConst_pos L).le, hofT, hD',
      ENNReal.ofReal_mul (CutConst_pos L).le, mul_assoc]
  have hE' : J ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal (DualConst L j c) * N) * J ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hJ0 hJfin.ne, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      ENNReal.rpow_one]
    refine hE.trans (le_of_eq ?_)
    rw [hD]
    ring
  have hroot := (ENNReal.mul_le_mul_iff_left hJh hJh').1 hE'
  calc ∫⁻ θ in freqCube, (ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) * pair θ) ^ 2
      ≤ J := hb
    _ = (J ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (ENNReal.ofReal (DualConst L j c) * N) ^ 2 := pow_le_pow_left₀ zero_le hroot 2

end Family
end

end AVRegularity.CycleWords.Seam
end

section
open Homogenization AVenhance AVRegularity.Weighted AVRegularity.CycleJointProofs
namespace AVRegularity.CycleWords.Seam

/-! Polynomial chart weights for any bounded drift: `W_m = (1 + ϖ²|z|²)^m`, flux `0`, rate
`λ_m = 4mϖV + 64(m+1)²ϖ²` for `‖v‖ ≤ V`. The rate depends on the size of the drift, so these
weights only give finiteness of weighted energies (for the adjoint chains of the seam), not
uniform bounds. -/

/-- The crude rate. -/
def crudeChartRate (ϖ V : ℝ) (m : ℕ) : ℝ := 4 * (m : ℝ) * ϖ * V + 64 * ((m : ℝ) + 1) ^ 2 * ϖ ^ 2

theorem crudeChartRate_nonneg {ϖ V : ℝ} (hϖ : 0 ≤ ϖ) (hV : 0 ≤ V) (m : ℕ) :
    0 ≤ crudeChartRate ϖ V m := by
  unfold crudeChartRate
  positivity

/-- **Crude chart weights.** -/
theorem crudeChartWeights_exists (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (v : ℝ → Vec 2 → Vec 2) (V : ℝ) (hV : 0 ≤ V)
    (hbv : ∀ t z, ‖v t z‖ ≤ V) (t₀ S ϖ : ℝ) (hS : 0 < S) (hϖ : 0 ≤ ϖ) (N : ℕ) :
    ∃ C : ChartWeights (fun t _ => G t) v t₀ S ϖ 0 N
        (fun m => 1 + crudeChartRate ϖ V m * S),
      ∀ m t z, C.W m t z = planeMomentPolynomial m ϖ 0 z := by
  have hP (m : ℕ) (z : Vec 2) : 0 < planeMomentPolynomial m ϖ 0 z := by
    unfold planeMomentPolynomial
    positivity
  have hW (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (planeMomentPolynomial m ϖ 0) := by
    unfold planeMomentPolynomial
    fun_prop
  have hR (m : ℕ) := crudeChartRate_nonneg hϖ hV m
  refine ⟨{
    W := fun m _ => planeMomentPolynomial m ϖ 0
    Phi := fun _ _ _ => 0
    lam := fun m => crudeChartRate ϖ V m
    smooth := fun m _ => ⟨((hW m).of_le (by simp)).comp contDiff_snd, contDiff_const⟩
    pos := fun m _ _ z => hP m z
    comparable := ?_
    defect := ?_
    bound := ?_
    lam_bound := fun m _ => ⟨hR m, ?_⟩ }, fun _ _ _ => rfl⟩
  · intro m _ t _ z
    have h1 : 1 ≤ 1 + crudeChartRate ϖ V m * S := le_add_of_nonneg_right (mul_nonneg (hR m) hS.le)
    have hi : (1 + crudeChartRate ϖ V m * S)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    change (1 + crudeChartRate ϖ V m * S)⁻¹ * planeMomentPolynomial m ϖ 0 z ≤
        planeMomentPolynomial m ϖ 0 z ∧
      planeMomentPolynomial m ϖ 0 z ≤ (1 + crudeChartRate ϖ V m * S) * planeMomentPolynomial m ϖ 0 z
    exact ⟨(mul_le_mul_of_nonneg_right hi (hP m z).le).trans_eq (one_mul _),
      (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right h1 (hP m z).le)⟩
  · intro m _ t _ z
    simp only [deriv_const, zero_add]
    have h0 : ∀ k : Fin 2, fderiv ℝ (fun _ : Vec 2 => (0 : Vec 2) k) z (basisVec k) = 0 :=
      fun k => by simp
    simp only [h0, Finset.sum_const_zero, add_zero]
    have hd := Interior.moment_metric_diffusion_le G hG m ϖ t z
    have htr : ∑ k : Fin 2, v t z k * fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k) ≤
        4 * (m : ℝ) * ϖ * V * planeMomentPolynomial m ϖ 0 z := by
      have hk (k : Fin 2) : v t z k * fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k) ≤
          V * (2 * (m : ℝ) * ϖ * planeMomentPolynomial m ϖ 0 z) := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have hv : |v t z k| ≤ V := (norm_le_pi_norm (v t z) k).trans (hbv t z)
        have hg := planeMomentPolynomial_gradient_abs_le m ϖ 0 z k
        rw [abs_of_nonneg hϖ] at hg
        exact mul_le_mul hv hg (abs_nonneg _) hV
      calc ∑ k : Fin 2, v t z k * fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k)
          ≤ ∑ _k : Fin 2, V * (2 * (m : ℝ) * ϖ * planeMomentPolynomial m ϖ 0 z) :=
            Finset.sum_le_sum fun k _ => hk k
        _ = 4 * (m : ℝ) * ϖ * V * planeMomentPolynomial m ϖ 0 z := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    change ∑ k : Fin 2, v t z k * fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k) +
        ∑ k : Fin 2, fderiv ℝ (fun z' => ∑ j : Fin 2, G t k j *
          fderiv ℝ (planeMomentPolynomial m ϖ 0) z' (basisVec j)) z (basisVec k) ≤
      crudeChartRate ϖ V m * planeMomentPolynomial m ϖ 0 z
    unfold crudeChartRate
    nlinarith [hP m z]
  · intro m _ t _ z
    simp only [Pi.zero_apply, Finset.sum_const_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div, add_zero]
    have hW2 : 0 < planeMomentPolynomial m ϖ 0 z ^ 2 := pow_pos (hP m z) 2
    rw [div_le_iff₀ hW2]
    have hk (k : Fin 2) : fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k) ^ 2 ≤
        (2 * (m : ℝ) * ϖ) ^ 2 * planeMomentPolynomial m ϖ 0 z ^ 2 := by
      have hg := planeMomentPolynomial_gradient_abs_le m ϖ 0 z k
      rw [abs_of_nonneg hϖ] at hg
      rw [← sq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hg 2
    calc ∑ k : Fin 2, fderiv ℝ (planeMomentPolynomial m ϖ 0) z (basisVec k) ^ 2
        ≤ ∑ _k : Fin 2, (2 * (m : ℝ) * ϖ) ^ 2 * planeMomentPolynomial m ϖ 0 z ^ 2 :=
          Finset.sum_le_sum fun k _ => hk k
      _ = 8 * (m : ℝ) ^ 2 * ϖ ^ 2 * planeMomentPolynomial m ϖ 0 z ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ crudeChartRate ϖ V m * planeMomentPolynomial m ϖ 0 z ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hW2.le
          unfold crudeChartRate
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have h1 : 0 ≤ 4 * (m : ℝ) * ϖ * V := by positivity
          nlinarith [sq_nonneg ϖ]
  · rw [le_div_iff₀ hS]
    linarith

end AVRegularity.CycleWords.Seam
end
