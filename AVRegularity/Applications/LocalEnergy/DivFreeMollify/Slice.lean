-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import AVRegularity.Applications.Parabolic.SliceGrad
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

section
@[expose] public section
open Homogenization
open scoped Convolution Topology
namespace AVRegularity.Applications.LocalEnergy.Moll

/-!
# ContDiffBump mollification

Mathlib provides normalized `ContDiffBump` kernels, convolution regularity,
and approximate-identity convergence. The kernel and convolution API here is
independent of the geometry layer.
-/

/-- A smooth bump centered at zero with outer radius `ε`. -/
noncomputable def standardMollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump (0 : Vec d) :=
  { rIn := ε / 2
    rOut := ε
    rIn_pos := half_pos hε
    rIn_lt_rOut := half_lt_self hε }

/-- The normalized scalar kernel associated with `standardMollifier`. -/
noncomputable def mollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) : Vec d → ℝ :=
  (standardMollifier ε hε).normed MeasureTheory.volume

theorem mollifier_nonneg {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    0 ≤ mollifier (d := d) ε hε x := by
  exact (standardMollifier (d := d) ε hε).nonneg_normed x

theorem mollifier_integral_one {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Vec d, mollifier (d := d) ε hε x ∂MeasureTheory.volume = 1 := by
  exact (standardMollifier (d := d) ε hε).integral_normed

theorem mollifier_hasCompactSupport {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).hasCompactSupport_normed

theorem mollifier_contDiff {d : ℕ} {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).contDiff_normed

/-- Convolution of `u` with the normalized radius-`ε` kernel. -/
noncomputable def mollify {d : ℕ} (u : Vec d → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Vec d → ℝ :=
  MeasureTheory.convolution (mollifier (d := d) ε hε) u
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

theorem mollify_contDiff {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    ContDiff ℝ n (mollify u ε hε) := by
  exact (mollifier_hasCompactSupport (d := d) hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_contDiff (d := d) hε) hu

theorem mollify_continuous {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    Continuous (mollify u ε hε) := by
  exact (mollify_contDiff hε hu (n := 0)).continuous

/-- The topological support of the normalized mollifier kernel of radius `ε > 0` is the closed
ball of radius `ε`. -/
theorem mollifier_tsupp_eq_closedBall {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifier (d := d) ε hε) = Metric.closedBall 0 ε :=
  (standardMollifier (d := d) ε hε).tsupport_normed_eq

end AVRegularity.Applications.LocalEnergy.Moll
end
end

section
public section
noncomputable section
open MeasureTheory Filter Topology
namespace AVRegularity.Applications.LocalEnergy.Moll

/-! # Continuity of `(a, b) ↦ ∫ h a b` in `L² × L²` for a bounded weight `h` -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy–Schwarz for a bounded weight. -/
theorem abs_integral_mul_mul_le {a b h : α → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hh : AEStronglyMeasurable h μ) (hM : ∀ᵐ y ∂μ, |h y| ≤ M) :
    |∫ y, h y * (a y * b y) ∂μ| ≤
      M * (Real.sqrt (∫ y, a y ^ 2 ∂μ) * Real.sqrt (∫ y, b y ^ 2 ∂μ)) := by
  have hab : Integrable (fun y => a y * b y) μ := ha.integrable_mul hb
  have habn : Integrable (fun y => ‖a y‖ * ‖b y‖) μ := by
    simpa [norm_mul] using hab.norm
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := a) (g := b)
    Real.HolderConjugate.two_two (by simpa using ha) (by simpa using hb)
  have hi : Integrable (fun y => h y * (a y * b y)) μ := by
    refine hab.bdd_mul (c := M) hh ?_
    filter_upwards [hM] with y hy using by simpa using hy
  calc |∫ y, h y * (a y * b y) ∂μ| ≤ ∫ y, ‖h y * (a y * b y)‖ ∂μ := by
        simpa using norm_integral_le_integral_norm (μ := μ) (fun y => h y * (a y * b y))
    _ ≤ ∫ y, M * (‖a y‖ * ‖b y‖) ∂μ := by
        refine integral_mono_ae hi.norm (habn.const_mul M) ?_
        filter_upwards [hM] with y hy
        rw [norm_mul, ← mul_assoc, norm_mul, Real.norm_eq_abs]
        have := mul_le_mul_of_nonneg_right hy (mul_nonneg (norm_nonneg (a y)) (norm_nonneg (b y)))
        simpa [norm_mul, mul_assoc] using this
    _ = M * ∫ y, ‖a y‖ * ‖b y‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        refine hholder.trans (le_of_eq ?_)
        simp [Real.sqrt_eq_rpow]


theorem integrable_weight_mul_mul {a b h : α → ℝ} {M : ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hh : AEStronglyMeasurable h μ) (hM : ∀ᵐ y ∂μ, |h y| ≤ M) :
    Integrable (fun y => h y * (a y * b y)) μ := by
  have hab : Integrable (fun y => a y * b y) μ := ha.integrable_mul hb
  refine hab.bdd_mul (c := M) hh ?_
  filter_upwards [hM] with y hy using by simpa using hy

theorem sqrt_integral_sq_tendsto_zero {f : ℕ → α → ℝ}
    (h : Tendsto (fun n => ∫ y, f n y ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ y, f n y ^ 2 ∂μ)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Function.comp_def] using this

/-- The weighted bilinear pairing is continuous in `L² × L²`. -/
theorem tendsto_integral_mul_mul {a b h : α → ℝ} {an bn : ℕ → α → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hh : AEStronglyMeasurable h μ) (hM : ∀ᵐ y ∂μ, |h y| ≤ M)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (han : ∀ n, MemLp (an n) 2 μ)
    (hbn : ∀ n, MemLp (bn n) 2 μ)
    (hta : Tendsto (fun n => ∫ y, (an n y - a y) ^ 2 ∂μ) atTop (𝓝 0))
    (htb : Tendsto (fun n => ∫ y, (bn n y - b y) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, h y * (an n y * bn n y) ∂μ) atTop
      (𝓝 (∫ y, h y * (a y * b y) ∂μ)) := by
  have hsa := sqrt_integral_sq_tendsto_zero hta
  have hsb := sqrt_integral_sq_tendsto_zero htb
  have hbound : Tendsto (fun n => M * (Real.sqrt (∫ y, (an n y - a y) ^ 2 ∂μ) *
        Real.sqrt (∫ y, b y ^ 2 ∂μ) + Real.sqrt (∫ y, a y ^ 2 ∂μ) *
        Real.sqrt (∫ y, (bn n y - b y) ^ 2 ∂μ) + Real.sqrt (∫ y, (an n y - a y) ^ 2 ∂μ) *
        Real.sqrt (∫ y, (bn n y - b y) ^ 2 ∂μ))) atTop (𝓝 0) := by
    have := ((hsa.mul_const (Real.sqrt (∫ y, b y ^ 2 ∂μ))).add
      (hsb.const_mul (Real.sqrt (∫ y, a y ^ 2 ∂μ)))).add (hsa.mul hsb)
    simpa using this.const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound
  have hdec : ∫ y, h y * (an n y * bn n y) ∂μ - ∫ y, h y * (a y * b y) ∂μ =
      (∫ y, h y * ((an n y - a y) * b y) ∂μ + ∫ y, h y * (a y * (bn n y - b y)) ∂μ) +
        ∫ y, h y * ((an n y - a y) * (bn n y - b y)) ∂μ := by
    have i0 := integrable_weight_mul_mul (M := M) (han n) (hbn n) hh hM
    have i0' := integrable_weight_mul_mul (M := M) ha hb hh hM
    have i1 : Integrable (fun y => h y * ((an n y - a y) * b y)) μ :=
      integrable_weight_mul_mul (a := fun y => an n y - a y) ((han n).sub ha) hb hh hM
    have i2 : Integrable (fun y => h y * (a y * (bn n y - b y))) μ :=
      integrable_weight_mul_mul (b := fun y => bn n y - b y) ha ((hbn n).sub hb) hh hM
    have i3 : Integrable (fun y => h y * ((an n y - a y) * (bn n y - b y))) μ :=
      integrable_weight_mul_mul (a := fun y => an n y - a y) (b := fun y => bn n y - b y)
        ((han n).sub ha) ((hbn n).sub hb) hh hM
    rw [← integral_sub i0 i0']
    have e : (fun y => h y * (an n y * bn n y) - h y * (a y * b y)) =
        fun y => (h y * ((an n y - a y) * b y) + h y * (a y * (bn n y - b y))) +
          h y * ((an n y - a y) * (bn n y - b y)) := by
      ext y; ring
    have i12 : Integrable (fun y => h y * ((an n y - a y) * b y) +
        h y * (a y * (bn n y - b y))) μ := i1.add i2
    rw [e, integral_add i12 i3, integral_add i1 i2]
  rw [Real.norm_eq_abs, hdec]
  have h1 := abs_integral_mul_mul_le hM0 ((han n).sub ha) hb hh hM
  have h2 := abs_integral_mul_mul_le hM0 ha ((hbn n).sub hb) hh hM
  have h3 := abs_integral_mul_mul_le hM0 ((han n).sub ha) ((hbn n).sub hb) hh hM
  refine (abs_add_three _ _ _).trans ?_
  simp only [Pi.sub_apply] at h1 h2 h3
  linarith [h1, h2, h3]

end AVRegularity.Applications.LocalEnergy.Moll
end
end
end

section
@[expose] public section
open Function Set Filter MeasureTheory Topology
open Homogenization
open scoped ENNReal Convolution
namespace AVRegularity.Applications.LocalEnergy.Moll

/-!
# `L^p` bounds for normalized convolution

The proof uses Jensen for `|·|^p`, translation invariance, and Tonelli.  The
result is the contraction estimate needed in the density argument for
mollification.
-/

noncomputable section

private lemma convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := by
    convert (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun x : ℝ => ‖x‖)) using 1
  have h2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
  have h3 : MonotoneOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow ha hab (le_trans zero_le_one hp)
  have himg : (fun x : ℝ => |x|) '' Set.univ ⊆ Set.Ici 0 := by
    rintro _ ⟨x, -, rfl⟩
    exact abs_nonneg x
  have himg_convex : Convex ℝ ((fun x : ℝ => |x|) '' Set.univ) := by
    have heq : (fun x : ℝ => |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ici]
      constructor
      · rintro ⟨x, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, abs_of_nonneg hy⟩
    rw [heq]
    exact convex_Ici 0
  exact (h2.subset himg himg_convex).comp h1 (h3.mono himg)

private lemma jensen_abs_rpow_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Integrable f μ) (hfpow : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ ∫ x, |f x| ^ p ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := convexOn_abs_rpow hp
  have hcont : ContinuousOn (fun x : ℝ => |x| ^ p) Set.univ := by
    exact (continuous_abs.rpow_const fun _ => Or.inr (le_trans zero_le_one hp)).continuousOn
  exact hconv.map_integral_le hcont isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf hfpow

private lemma lintegral_comp_sub_right {d : ℕ} (f : Vec d → ℝ≥0∞) (hf : Measurable f)
    (t : Vec d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) = ∫⁻ x, f x ∂volume := by
  have heq : (fun x => f (x - t)) = f ∘ ((· + (-t)) : Vec d → Vec d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap : Measure.map (fun x : Vec d => x + (-t)) (volume : Measure (Vec d)) = volume := by
    simpa using (MeasureTheory.map_add_right_eq_self (μ := (volume : Measure (Vec d))) (-t))
  rw [hmap]

private lemma fubini_translation_key {d : ℕ} (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ) (p : ℝ)
    (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · have hpow : Measurable (fun z : Vec d × Vec d =>
          (ENNReal.ofReal |g (z.1 - z.2)|) ^ p) := by
        have hbase : Measurable (fun z : Vec d × Vec d =>
            ENNReal.ofReal |g (z.1 - z.2)|) := by
          exact ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp (hg.comp (measurable_fst.sub measurable_snd)))
        exact Measurable.pow_const hbase p
      exact hpow.aemeasurable
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ρ t * ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    congr 1
    ext t
    have hsub : Measurable (fun x : Vec d => x - t) := measurable_id.sub measurable_const
    exact lintegral_const_mul _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (hg.comp hsub))) p)
  rw [hfactor]
  have htrans : ∀ t, ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂(volume : Measure (Vec d)) =
      ∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume := by
    intro t
    exact lintegral_comp_sub_right _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private lemma integral_withDensity_ofReal_eq_integral_mul
    {d : ℕ} {f g : Vec d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_meas : AEMeasurable f volume) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq : (fun x => ENNReal.ofReal (f x)) =
      fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hf_nonneg x),
      Real.toNNReal_of_nonneg (hf_nonneg x)]
  rw [heq, integral_withDensity_eq_integral_smul₀ (hf_meas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hf_nonneg x)]

theorem young_convolution_nonneg_integral_one
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1) (hρ_meas : Measurable ρ) (hg_meas : Measurable g) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_ge_one : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  let μ : Measure (Vec d) := volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hρ_aestrong : AEStronglyMeasurable ρ volume := hρ_meas.aestronglyMeasurable
  have hg_aestrong : AEStronglyMeasurable g volume := hg_meas.aestronglyMeasurable
  have hconv_aestrong : AEStronglyMeasurable
      (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
    hρ_aestrong.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hg_aestrong
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hconv_aestrong]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hg_aestrong]
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini := fubini_translation_key (d := d) (fun t => ENNReal.ofReal (ρ t)) g
    p.toReal hρ_meas.ennreal_ofReal hg_meas
  have hρ_lint_one : ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hpointwise : ∀ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
      ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heq_int : ∫ t, ρ t * g (x - t) = ∫ t, g (x - t) ∂μ := by
      symm
      exact integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable
    rw [heq_int]
    by_cases hg_int_μ : Integrable (fun t => g (x - t)) μ
    · by_cases hgpow_int_μ : Integrable (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen := jensen_abs_rpow_integral μ hp_ge_one hg_int_μ hgpow_int_μ
        have heq_pow : ∫ t, |g (x - t)| ^ p.toReal ∂μ =
            (∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal
              ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρ_nonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          · exact ae_of_all _ (fun t => mul_nonneg (hρ_nonneg t)
              (Real.rpow_nonneg (abs_nonneg _) _))
          · have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
              have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
              exact hcont.measurable.comp (hg_meas.comp (measurable_const.sub measurable_id))
            exact (hρ_meas.mul habs_rpow_meas).aestronglyMeasurable
        calc
          ENNReal.ofReal |∫ t, g (x - t) ∂μ| ^ p.toReal =
              ENNReal.ofReal (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
                rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          _ ≤ ENNReal.ofReal (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ = ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal) := by
            rw [heq_pow]
          _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnot_finite : ∫⁻ t, ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume = ⊤ := by
          have h_eq : ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume =
              ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ := by
            have hsub : Measurable (fun t : Vec d => x - t) := measurable_const.sub measurable_id
            have h_abs_meas : Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp (hg_meas.comp hsub)
            have h_meas_pow : Measurable
                (fun t => (ENNReal.ofReal |g (x - t)|) ^ p.toReal) :=
              Measurable.pow_const h_abs_meas.ennreal_ofReal p.toReal
            symm
            convert lintegral_withDensity_eq_lintegral_mul volume
              hρ_meas.ennreal_ofReal h_meas_pow using 2
          rw [h_eq]
          have habs_rpow_nonneg : ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t => Real.rpow_nonneg (abs_nonneg _) _
          have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
            have hsub : Measurable (fun t : Vec d => x - t) := measurable_const.sub measurable_id
            exact hcont.measurable.comp (hg_meas.comp hsub)
          have htop : ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ = ⊤ := by
            rw [← lintegral_ofReal_ne_top_iff_integrable habs_rpow_meas.aestronglyMeasurable
                (ae_of_all _ habs_rpow_nonneg)] at hgpow_int_μ
            have htop' : ∫⁻ t, ENNReal.ofReal (|g (x - t)| ^ p.toReal) ∂μ = ⊤ := by
              exact not_ne_iff.mp hgpow_int_μ
            convert htop' using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          rw [htop]
        simp [hnot_finite]
    · rw [integral_undef hg_int_μ]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hp_pos]
      exact zero_le
  calc
    ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ∂volume ≤
        ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t) *
          (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ = (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := hfubini
    _ = 1 * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := by rw [hρ_lint_one]
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume := one_mul _
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

theorem young_convolution_nonneg_integral_one_of_aemeasurable
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1) (hρ_meas : Measurable ρ)
    (hg_meas : AEMeasurable g volume) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  let g' : Vec d → ℝ := hg_meas.mk g
  have hconv :
      convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    simpa [g'] using
      (convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure (Vec d))) (h1 := EventuallyEq.rfl)
        (h2 := hg_meas.ae_eq_mk))
  rw [hconv]
  calc
    eLpNorm (convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
        eLpNorm g' p volume :=
      young_convolution_nonneg_integral_one hp hp_top hρ_nonneg hρ_int hρ_one hρ_meas
        hg_meas.measurable_mk
    _ = eLpNorm g p volume := eLpNorm_congr_ae hg_meas.ae_eq_mk.symm

end

end AVRegularity.Applications.LocalEnergy.Moll
end
end

section
@[expose] public section
open scoped Convolution Topology
open MeasureTheory Homogenization
namespace AVRegularity.Applications.LocalEnergy.Moll

/-!
# Interior transport of weak derivatives through mollification

The translated `ContDiffBump` is used as the test function in the
defining weak-derivative identity, while Mathlib supplies the convolution
derivative and measure-preserving change of variables.

The transport theorem below is pointwise on a closed-ball interior condition,
with a compact-set wrapper. The general local `L^p` approximation theorem is
not asserted here because the available Mathlib API does not provide the
needed local convolution bound and translation-continuity package.
-/

theorem fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
    {d : ℕ} {U : Set (Vec d)} (_ : IsOpen U)
    {u gi : Vec d → ℝ} {i : Fin d} (hu : MeasureTheory.LocallyIntegrable u volume)
    (_ : MeasureTheory.LocallyIntegrable gi volume)
    (hweak : HasWeakPartialDerivOn U i u gi) {ε : ℝ} (hε : 0 < ε)
    {x : Vec d} (hx : Metric.closedBall x ε ⊆ U) :
    (fderiv ℝ (mollify u ε hε) x) (basisVec i) = mollify gi ε hε x := by
  let k : Vec d → ℝ := mollifier (d := d) ε hε
  let φ : Vec d → ℝ := fun y => k (x - y)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := mollifier_contDiff hε
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact hk.comp (contDiff_const.sub contDiff_id)
  have hφSupport : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using
      (mollifier_hasCompactSupport (d := d) hε).comp_homeomorph (Homeomorph.subLeft x)
  have hφSubset : tsupport φ ⊆ U := by
    have hts : tsupport φ = (Homeomorph.subLeft x) ⁻¹' tsupport k := by
      simpa [φ, Function.comp_def] using
        (tsupport_comp_eq_preimage k (Homeomorph.subLeft x))
    rw [hts, show tsupport k = Metric.closedBall (0 : Vec d) ε by
      exact (standardMollifier (d := d) ε hε).tsupport_normed_eq]
    intro y hy
    apply hx
    change x - y ∈ Metric.closedBall (0 : Vec d) ε at hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖y - x‖ = ‖-(y - x)‖ := (norm_neg _).symm
      _ = ‖x - y‖ := by
        congr 1
        abel
      _ ≤ ε := hy
  have hfd := (mollifier_hasCompactSupport (d := d) hε).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_contDiff hε (n := 1)) hu x
  rw [(by simpa [mollify] using hfd.fderiv :
    fderiv ℝ (mollify u ε hε) x =
      (MeasureTheory.convolution (fderiv ℝ (mollifier (d := d) ε hε)) u
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)) volume) x)]
  simp only [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, mollify]
  dsimp [k]
  have hconv : ConvolutionExists (fderiv ℝ (mollifier (d := d) ε hε)) u
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec d) (E := Vec d →L[ℝ] ℝ) (E' := ℝ)
      (F := Vec d →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d))
      ((mollifier_hasCompactSupport (d := d) hε).fderiv (𝕜 := ℝ))
      ((mollifier_contDiff (d := d) hε (n := 2)).continuous_fderiv (by simp)) hu
  rw [ContinuousLinearMap.integral_apply (hconv x) (basisVec i)]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  change (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
      ∂volume) =
    ∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume
  have hφDeriv (y : Vec d) :
      (fderiv ℝ φ y) (basisVec i) =
        - (fderiv ℝ k (x - y)) (basisVec i) := by
    have hinner : HasFDerivAt (fun z : Vec d => x - z)
        (-(1 : Vec d →L[ℝ] Vec d)) y :=
      (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) :=
      (hk.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  have hφOutside : ∀ y, y ∉ U → φ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hy' => hy (hφSubset hy'))
  have hφDerivOutside : ∀ y, y ∉ U → (fderiv ℝ φ y) (basisVec i) = 0 := by
    intro y hy
    have hy' : y ∉ tsupport φ := fun hy' => hy (hφSubset hy')
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy']
    simp
  have hweakGlobal :
      (∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume) =
        -∫ y, gi y * φ y ∂volume := by
    calc
      (∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume) =
          ∫ y in U, u y * (fderiv ℝ φ y) (basisVec i) ∂volume := by
        symm
        apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        simp [hφDerivOutside y hy]
      _ = -∫ y in U, gi y * φ y ∂volume :=
        hweak φ hφ hφSupport hφSubset
      _ = -∫ y, gi y * φ y ∂volume := by
        congr 1
        apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        simp [hφOutside y hy]
  have hchange :
      (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
          ∂volume) =
        ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := by
    calc
      (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
          ∂volume) =
          ∫ t, u (x - t) * (fderiv ℝ (mollifier (d := d) ε hε) t)
            (basisVec i) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        ring
      _ = ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := by
        let F : Vec d → ℝ := fun y =>
          u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i)
        simpa [F, sub_sub_cancel] using
          (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
            (Homeomorph.subLeft x).measurableEmbedding F
  have hright :
      (∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume) =
        ∫ y, gi y * φ y ∂volume := by
    let F : Vec d → ℝ := fun y => φ y * gi y
    calc
      (∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume) =
          ∫ t, F (x - t) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        simp [F, φ, k]
      _ = ∫ y, F y ∂volume :=
        (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
          (Homeomorph.subLeft x).measurableEmbedding F
      _ = ∫ y, gi y * φ y ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        simp [F, mul_comm]
  calc
    (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
        ∂volume) =
        ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := hchange
    _ = -∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume := by
      rw [show (fun y => u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i)) =
          (fun y => -(u y * (fderiv ℝ φ y) (basisVec i))) by
            funext y
            rw [hφDeriv]
            ring]
      rw [MeasureTheory.integral_neg]
    _ = ∫ y, gi y * φ y ∂volume := by rw [hweakGlobal]; simp
    _ = ∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume := hright.symm

end AVRegularity.Applications.LocalEnergy.Moll
end
end

section
@[expose] public section
open Function Set Filter MeasureTheory Topology
open Homogenization
open scoped ENNReal Convolution Pointwise
namespace AVRegularity.Applications.LocalEnergy.Moll

/-!
# Global and local `Lᵖ` approximation by mollification

Global `Lᵖ` convergence of mollifications (dimension 2).
-/

noncomputable section

private theorem tendsto_eLpNorm_sub_zero_mollify_of_continuous
    {d : ℕ} {f : Vec d → ℝ} {p : ENNReal}
    (hp_top : p ≠ ∞) (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume)
      atTop (nhds 0) := by
  let K : Set (Vec d) := Metric.closedBall 0 1 + tsupport f
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : Vec d) 1).add hf_supp.isCompact
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hK_ne_top : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
  have hpow_ne_top : volume K ^ (1 / p.toReal) ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK_ne_top).ne
  let cK : ℝ := (volume K ^ (1 / p.toReal)).toReal
  have hcK_nonneg : 0 ≤ cK := ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cK = volume K ^ (1 / p.toReal) := by
    dsimp [cK]
    exact ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  let δ : ℝ := η.toReal / (cK + 1)
  have hη_real : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont) δ hδ_pos
  have hε_small : ∀ᶠ n in atTop, ε n < γ / 2 :=
    (tendsto_order.1 hε).2 _ (by positivity)
  have hε_le_one : ∀ᶠ n in atTop, ε n ≤ 1 :=
    ((tendsto_order.1 hε).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [hε_small, hε_le_one] with n hn_small hn_one
  have hkernel_support :
      support (mollifier (d := d) (ε n) (hε_pos n)) ⊆ Metric.ball 0 (2 * ε n) := by
    apply (subset_tsupport _).trans
    rw [mollifier_tsupp_eq_closedBall (hε_pos n)]
    exact Metric.closedBall_subset_ball (by linarith only [hε_pos n])
  have hdist : ∀ x,
      dist (mollify f (ε n) (hε_pos n) x) (f x) ≤ δ := by
    intro x
    apply MeasureTheory.dist_convolution_le (le_of_lt hδ_pos)
    · exact hkernel_support
    · exact mollifier_nonneg (hε_pos n)
    · exact mollifier_integral_one (hε_pos n)
    · exact hf_cont.aestronglyMeasurable
    · intro y hy
      rw [Metric.mem_ball, dist_eq_norm_sub] at hy
      apply (hγ ?_).le
      rw [dist_eq_norm_sub]
      exact hy.trans (by linarith only [hn_small])
  have hconv_support :
      support (mollify f (ε n) (hε_pos n)) ⊆ K := by
    calc
      support (mollify f (ε n) (hε_pos n)) ⊆
          support (mollifier (d := d) (ε n) (hε_pos n)) + support f := by
        simpa [mollify] using
          (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
            (f := mollifier (d := d) (ε n) (hε_pos n)) (g := f))
      _ ⊆ Metric.closedBall 0 1 + tsupport f := by
        exact add_subset_add
          ((subset_tsupport _).trans (by
            rw [mollifier_tsupp_eq_closedBall (hε_pos n)]
            exact Metric.closedBall_subset_closedBall hn_one))
          (subset_tsupport _)
  have hf_support : support f ⊆ K := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hbound :
      eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := by
    have hmeas : AEStronglyMeasurable
        (fun x => mollify f (ε n) (hε_pos n) x - f x) volume :=
      ((mollify_continuous (hε_pos n)
        (hf_cont.integrable_of_hasCompactSupport hf_supp).locallyIntegrable).sub hf_cont)
        |>.aestronglyMeasurable
    exact eLpNorm_sub_le_of_dist_bdd volume hp_top hK_meas.nullMeasurableSet hδ_pos.le
      hmeas hdist
      hconv_support hf_support
  have hδmul : δ * cK ≤ η.toReal := by
    have hfrac_le : cK / (cK + 1) ≤ 1 := by
      exact div_le_one_of_le₀ (by linarith only [hcK_nonneg]) (by linarith only [hcK_nonneg])
    calc
      δ * cK = η.toReal * (cK / (cK + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη_real.le
      _ = η.toReal := mul_one _
  calc
    eLpNorm (fun x => mollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := hbound
    _ = ENNReal.ofReal (δ * cK) := by
      rw [← hpow_eq, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hη_top]
      exact ENNReal.ofReal_le_ofReal hδmul

theorem tendsto_eLpNorm_sub_zero_mollify
    {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {g : Vec 2 → ℝ} (hg : MemLp g p volume)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm (fun x => mollify g (ε n) (hε_pos n) x - g x) p volume)
      atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec 2))) (ε := ℝ) (p := p) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec 2))) (ε := ℝ) (p := p) hη₁_pos.ne'
  let δ : ℝ≥0∞ := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f', hf'_supp, happrox', hf'_cont, hf'_mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp_top hδ_pos.ne'
  have hthird_mem' : MemLp (fun x => f' x - g x) p volume := hf'_mem.sub hg
  have hthird_norm' : eLpNorm (fun x => f' x - g x) p volume ≤ η₁ := by
    have hneg : (fun x => f' x - g x) = -(fun x => g x - f' x) := by
      ext x
      change f' x - g x = -(g x - f' x)
      abel_nf
    rw [hneg, eLpNorm_neg]
    exact happrox'.trans (min_le_left _ _)
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm (fun x => mollify f' (ε n) (hε_pos n) x - f' x) p volume ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_sub_zero_mollify_of_continuous hp_top hf'_cont hf'_supp hε hε_pos)
      η₂ hη₂_pos
  filter_upwards [hmid_eventually] with n hmid
  let k : Vec 2 → ℝ := mollifier (d := 2) (ε n) (hε_pos n)
  have hk_compact : HasCompactSupport k := mollifier_hasCompactSupport (hε_pos n)
  have hk_cont : Continuous k := (mollifier_contDiff (hε_pos n) (n := 0)).continuous
  have hg_loc : LocallyIntegrable g volume := hg.locallyIntegrable hp
  have hf'_loc : LocallyIntegrable f' volume := hf'_mem.locallyIntegrable hp
  have hdiff_loc : LocallyIntegrable (fun x => g x - f' x) volume := hg_loc.sub hf'_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hconv_f : ConvolutionExists k f' (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hf'_loc
  have hconv_diff : ConvolutionExists k (fun x => g x - f' x)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hdiff_loc
  have hsplit : g = (fun x => g x - f' x) + f' := by
    ext x
    change g x = (g x - f' x) + f' x
    abel_nf
  have hconv_split :
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := by
    calc
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => g x - f' x) + f') := by
            exact congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' :=
            hconv_diff.distrib_add hconv_f
  have hfirst_norm :
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
        p volume ≤ η₂ := by
    calc
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
          p volume ≤ eLpNorm (fun x => g x - f' x) p volume :=
        young_convolution_nonneg_integral_one_of_aemeasurable hp hp_top
          (mollifier_nonneg (hε_pos n)) (integrable_of_integral_eq_one
            (mollifier_integral_one (hε_pos n))) (mollifier_integral_one (hε_pos n))
          hk_cont.measurable (hg.sub hf'_mem).aestronglyMeasurable.aemeasurable
      _ ≤ η₂ := happrox'.trans (min_le_right _ _)
  have hfirst_meas : AEStronglyMeasurable
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) volume := by
    exact (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hk_cont hdiff_loc).aestronglyMeasurable
  have hmiddle_meas : AEStronglyMeasurable
      (fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) volume := by
    exact (hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hk_cont hf'_loc).sub hf'_cont |>.aestronglyMeasurable
  have hfirst_middle :
      eLpNorm
        ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x)
        p volume < η₁ := by
    exact hη₂ _ _ hfirst_norm (by simpa only [k, mollify] using hmid)
  have hsum :
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p volume < η := by
    exact hη₁ _ _ hfirst_middle.le hthird_norm'
  have hdecomp :
      eLpNorm (fun x => mollify g (ε n) (hε_pos n) x - g x) p volume =
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        p volume := by
    rw [show mollify g (ε n) (hε_pos n) =
        k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g by rfl, hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    abel_nf
  exact hdecomp ▸ hsum.le

end

end AVRegularity.Applications.LocalEnergy.Moll
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.LocalEnergy.Moll

/-! # Time slices of the unit cylinder

`openCyl 0 1 = (-1,0) × B₁`, the product structure of the restricted volume, and the transfer of
measurability and a.e. bounds from the cylinder to a.e. time slices. -/

theorem isOpen_unitBall : IsOpen (euclidBall (0 : Vec 2) 1) := by
  unfold euclidBall
  simp only [sub_zero]
  have hc : Continuous (fun y : Vec 2 => vecNormSq y) := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    fun_prop
  exact isOpen_lt hc continuous_const

theorem unitBall_subset_box : euclidBall (0 : Vec 2) 1 ⊆ Metric.ball (0 : Vec 2) 1 := by
  intro y hy
  simp only [euclidBall, sub_zero, vecNormSq, vecDot, Fin.sum_univ_two, Set.mem_ofPred_eq,
    one_pow] at hy
  rw [mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one]
  intro i
  rw [Real.norm_eq_abs, abs_lt]
  fin_cases i <;> simp <;> constructor <;> nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1)]

theorem volume_unitBall_ne_top : volume (euclidBall (0 : Vec 2) 1) ≠ ⊤ :=
  ((measure_mono unitBall_subset_box).trans_lt measure_ball_lt_top).ne

theorem openCyl_zero_one : openCyl 0 1 = Set.Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1 := by
  simp [openCyl]

theorem restrict_openCyl :
    (volume : Measure (ℝ × Vec 2)).restrict (openCyl 0 1) =
      (volume.restrict (Set.Ioo (-1 : ℝ) 0)).prod (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
  rw [openCyl_zero_one, Measure.volume_eq_prod, Measure.prod_restrict]

theorem ae_slice_aestronglyMeasurable {f : ℝ × Vec 2 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (openCyl 0 1))) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      AEStronglyMeasurable (fun y => f (τ, y)) (volume.restrict (euclidBall (0 : Vec 2) 1)) := by
  rw [restrict_openCyl] at hf
  exact hf.prodMk_left

theorem ae_slice_of_ae {P : ℝ × Vec 2 → Prop}
    (hP : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), P p) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      ∀ᵐ y ∂(volume.restrict (euclidBall (0 : Vec 2) 1)), P (τ, y) := by
  rw [restrict_openCyl] at hP
  exact Measure.ae_ae_of_ae_prod hP

end AVRegularity.Applications.LocalEnergy.Moll
end
end
end
