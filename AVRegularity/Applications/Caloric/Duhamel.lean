-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Parabolic.SliceGrad
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

section
@[expose] public section
noncomputable section
section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.Caloric

/-! # Cutoff functions for the interior estimate

`cutω p = cutθ p.1 * cutχ p.2` equals `1` on `W = {s > -25/64, |x|² < 25/64}`, vanishes for
`s ≤ -1/2` and for `|x|² ≥ 1/2`. -/

/-- Spatial cutoff, `1` on `|y|² ≤ 25/64`, `0` on `|y|² ≥ 1/2`. -/
def cutχ (y : Vec 2) : ℝ := Real.smoothTransition ((1 / 2 - vecNormSq y) / (1 / 2 - 25 / 64))

/-- Temporal cutoff, `0` for `s ≤ -1/2`, `1` for `s ≥ -25/64`. -/
def cutθ (s : ℝ) : ℝ := Real.smoothTransition ((s + 1 / 2) / (1 / 2 - 25 / 64))

/-- The space-time cutoff. -/
def cutω (p : ℝ × Vec 2) : ℝ := cutθ p.1 * cutχ p.2

/-- The region where `cutω ≡ 1` locally. -/
def cutW : Set (ℝ × Vec 2) := {p | -(25 / 64 : ℝ) < p.1 ∧ vecNormSq p.2 < 25 / 64}

/-- `(∂ₛ + Δ) cutω`. -/
def cutA (p : ℝ × Vec 2) : ℝ := stTimeDeriv cutω p + stSpaceLap cutω p

/-- `∂_{x_i} cutω`. -/
def cutD (i : Fin 2) (p : ℝ × Vec 2) : ℝ := fderiv ℝ cutω p (0, basisVec i)

theorem contDiff_vecNormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => vecNormSq y) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum fun i _ =>
    ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i))

theorem cutχ_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutχ := by
  unfold cutχ
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_vecNormSq).div_const _)

theorem cutθ_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutθ := by
  unfold cutθ
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)

theorem cutω_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutω := by
  unfold cutω
  exact (cutθ_contDiff.comp contDiff_fst).mul (cutχ_contDiff.comp contDiff_snd)

theorem cutχ_eq_one {y : Vec 2} (h : vecNormSq y ≤ 25 / 64) : cutχ y = 1 := by
  unfold cutχ
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem cutχ_eq_zero {y : Vec 2} (h : 1 / 2 ≤ vecNormSq y) : cutχ y = 0 := by
  unfold cutχ
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

theorem cutθ_eq_one {s : ℝ} (h : -(25 / 64 : ℝ) ≤ s) : cutθ s = 1 := by
  unfold cutθ
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem cutθ_eq_zero {s : ℝ} (h : s ≤ -(1 / 2 : ℝ)) : cutθ s = 0 := by
  unfold cutθ
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

theorem isOpen_cutW : IsOpen cutW := by
  have h1 : Continuous (fun p : ℝ × Vec 2 => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × Vec 2 => vecNormSq p.2) :=
    contDiff_vecNormSq.continuous.comp continuous_snd
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt h2 continuous_const)

theorem cutω_eq_one_of_mem {p : ℝ × Vec 2} (hp : p ∈ cutW) : cutω p = 1 := by
  unfold cutω
  rw [cutθ_eq_one hp.1.le, cutχ_eq_one hp.2.le, one_mul]

theorem cutω_eventuallyEq_one {p : ℝ × Vec 2} (hp : p ∈ cutW) :
    cutω =ᶠ[nhds p] fun _ => 1 :=
  Filter.eventuallyEq_of_mem (isOpen_cutW.mem_nhds hp) fun _ hq => cutω_eq_one_of_mem hq

theorem fderiv_cutω_eq_zero {p : ℝ × Vec 2} (hp : p ∈ cutW) : fderiv ℝ cutω p = 0 := by
  rw [(cutω_eventuallyEq_one hp).fderiv_eq]
  simp

theorem cutD_eq_zero {p : ℝ × Vec 2} (hp : p ∈ cutW) (i : Fin 2) : cutD i p = 0 := by
  simp [cutD, fderiv_cutω_eq_zero hp]

theorem cutA_eq_zero {p : ℝ × Vec 2} (hp : p ∈ cutW) : cutA p = 0 := by
  have hev : ∀ᶠ q in nhds p, fderiv ℝ cutω q = 0 :=
    Filter.eventually_of_mem (isOpen_cutW.mem_nhds hp) fun q hq => fderiv_cutω_eq_zero hq
  have h1 : stTimeDeriv cutω p = 0 := by
    simp [stTimeDeriv, fderiv_cutω_eq_zero hp]
  have h2 : stSpaceLap cutω p = 0 := by
    unfold stSpaceLap
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (fun q => fderiv ℝ cutω q (0, basisVec i)) =ᶠ[nhds p] fun _ => (0 : ℝ) :=
      hev.mono fun q hq => by simp [hq]
    rw [this.fderiv_eq]
    simp
  simp [cutA, h1, h2]

theorem cutω_support {p : ℝ × Vec 2} (hp : cutω p ≠ 0) :
    -(1 / 2 : ℝ) < p.1 ∧ vecNormSq p.2 < 1 / 2 := by
  constructor
  · by_contra h
    exact hp (by simp [cutω, cutθ_eq_zero (not_lt.mp h)])
  · by_contra h
    exact hp (by simp [cutω, cutχ_eq_zero (not_lt.mp h)])

theorem vecNormSq_sub_ge {a b : Vec 2} (ha : vecNormSq a < (1 / 2 : ℝ) ^ 2)
    (hb : (5 / 8 : ℝ) ^ 2 ≤ vecNormSq b) : 1 / 64 ≤ vecNormSq (a - b) := by
  by_contra hlt
  push Not at hlt
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq a (a - b)
  have hn : 0 ≤ vecNormSq (a - b) := vecNormSq_nonneg _
  have hna : 0 ≤ vecNormSq a := vecNormSq_nonneg _
  have hb2 : vecNormSq b = vecNormSq a - 2 * vecDot a (a - b) + vecNormSq (a - b) := by
    unfold vecNormSq vecDot
    rw [show ∑ i, b i * b i = ∑ i, (a i * a i - 2 * (a i * (a - b) i) + (a - b) i * (a - b) i) from
      Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hprod : vecNormSq a * vecNormSq (a - b) ≤ 1 / 256 := by
    have : vecNormSq a * vecNormSq (a - b) ≤ (1 / 4) * (1 / 64) := by
      apply mul_le_mul (by norm_num at ha ⊢; linarith) hlt.le hn (by norm_num)
    linarith
  have habs : vecDot a (a - b) ≤ 1 / 16 := by
    by_contra hh
    push Not at hh
    nlinarith
  norm_num at ha hb
  nlinarith

/-- Separation: away from `W`, the kernel arguments avoid the singular region of `Γ`. -/
theorem cut_sep {z p : ℝ × Vec 2} (hz : z ∈ openCyl 0 (1 / 2)) (hp : p ∉ cutW) :
    1 / 64 ≤ vecNormSq (z - p).2 ∨ 9 / 64 ≤ (z - p).1 := by
  simp only [openCyl, euclidBall, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero,
    sub_zero, Set.mem_ofPred_eq] at hz
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  unfold cutW at hp
  simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hp
  rcases hp with h | h
  · right
    simp only [Prod.fst_sub]
    norm_num at hz1 ⊢
    linarith
  · left
    simp only [Prod.snd_sub]
    exact vecNormSq_sub_ge hz3 (by norm_num; linarith)

/-! # The heat kernel on ℝ² (skeleton) -/

/-- `Γ(r,ξ) = (4πr)⁻¹ e^{-|ξ|²/4r}` for `r > 0`, and `0` for `r ≤ 0`. -/
def heatK (r : ℝ) (ξ : Vec 2) : ℝ :=
  if 0 < r then (4 * Real.pi * r)⁻¹ * Real.exp (-(vecNormSq ξ) / (4 * r)) else 0

/-- The heat kernel as a function on space-time `(r,ξ)`. -/
def heatKP (q : ℝ × Vec 2) : ℝ := heatK q.1 q.2

theorem heatK_of_nonpos {r : ℝ} (h : r ≤ 0) (ξ : Vec 2) : heatK r ξ = 0 := by
  simp [heatK, not_lt.mpr h]

theorem heatK_of_pos {r : ℝ} (h : 0 < r) (ξ : Vec 2) :
    heatK r ξ = (4 * Real.pi * r)⁻¹ * Real.exp (-(vecNormSq ξ) / (4 * r)) := by
  simp [heatK, h]

theorem vecNormSq_eq_sum (ξ : Vec 2) : vecNormSq ξ = ∑ i, ξ i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem heatK_nonneg (r : ℝ) (ξ : Vec 2) : 0 ≤ heatK r ξ := by
  unfold heatK
  split_ifs with h
  · positivity
  · exact le_rfl

private lemma gaussian_exp_eq_prod (ξ : Vec 2) (r : ℝ) :
    Real.exp (-(vecNormSq ξ) / (4 * r)) =
      ∏ i, Real.exp (-(1 / (4 * r)) * (ξ i) ^ 2) := by
  rw [← Real.exp_sum, vecNormSq_eq_sum, ← Finset.mul_sum]
  congr 1
  ring

private lemma gaussian_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (fun ξ : Vec 2 => Real.exp (-(vecNormSq ξ) / (4 * r))) volume := by
  rw [show volume = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from volume_pi]
  have hprod : Integrable
      (fun ξ : Vec 2 => ∏ i, Real.exp (-(1 / (4 * r)) * (ξ i) ^ 2))
      (Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))) :=
    Integrable.fintype_prod (ι := Fin 2) (E := ℝ)
      (μ := fun _ : Fin 2 => (volume : Measure ℝ)) (fun _ => by
      convert integrable_exp_neg_mul_sq
        (by positivity : 0 < (1 / (4 * r) : ℝ)) using 1)
  exact hprod.congr (Filter.Eventually.of_forall fun x => (gaussian_exp_eq_prod x r).symm)

private lemma gaussian_integral (r : ℝ) (hr : 0 < r) :
    ∫ ξ : Vec 2, Real.exp (-(vecNormSq ξ) / (4 * r)) = 4 * Real.pi * r := by
  rw [show volume = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from volume_pi]
  have hfun : (fun ξ : Vec 2 => Real.exp (-(vecNormSq ξ) / (4 * r))) =
      (fun ξ : Vec 2 => ∏ i, Real.exp (-(1 / (4 * r)) * (ξ i) ^ 2)) := by
    funext x
    exact gaussian_exp_eq_prod x r
  have hprod := integral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (fun _ : Fin 2 => fun y : ℝ => Real.exp (-(1 / (4 * r)) * y ^ 2))
  rw [hfun, hprod]
  simp only [Finset.prod_const, Finset.card_fin]
  rw [integral_gaussian (1 / (4 * r))]
  have h1 : Real.pi / (1 / (4 * r)) = 4 * Real.pi * r := by field_simp
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem integrable_heatK {r : ℝ} (hr : 0 < r) : Integrable (heatK r) volume := by
  have : heatK r = fun ξ : Vec 2 =>
      (4 * Real.pi * r)⁻¹ * Real.exp (-(vecNormSq ξ) / (4 * r)) := by
    funext ξ; exact heatK_of_pos hr ξ
  rw [this]
  exact (gaussian_integrable r hr).const_mul _

theorem integral_heatK {r : ℝ} (hr : 0 < r) : ∫ ξ, heatK r ξ = 1 := by
  have : heatK r = fun ξ : Vec 2 =>
      (4 * Real.pi * r)⁻¹ * Real.exp (-(vecNormSq ξ) / (4 * r)) := by
    funext ξ; exact heatK_of_pos hr ξ
  rw [this, integral_const_mul, gaussian_integral r hr]
  have : 4 * Real.pi * r ≠ 0 := by positivity
  field_simp

theorem measurable_heatKP : Measurable heatKP := by
  unfold heatKP heatK
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  have hn : Measurable (fun q : ℝ × Vec 2 => vecNormSq q.2) := by
    simp only [vecNormSq_eq_sum]
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_snd).pow_const 2)
  fun_prop

theorem heatKP_integrableOn_Iio (T : ℝ) :
    IntegrableOn heatKP (Set.Iio T ×ˢ (Set.univ : Set (Vec 2))) volume := by
  rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
    integrable_prod_iff measurable_heatKP.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : 0 < x
    · exact integrable_heatK hx
    · have : (fun y : Vec 2 => heatKP (x, y)) = fun _ => 0 := by
        funext y; exact heatK_of_nonpos (not_lt.mp hx) y
      rw [this]; exact integrable_zero _ _ _
  · have hfun : (fun x : ℝ => ∫ y : Vec 2, ‖heatKP (x, y)‖) =
        (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : 0 < x
      · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
        have : (fun y : Vec 2 => ‖heatKP (x, y)‖) = heatK x := by
          funext y; exact Real.norm_of_nonneg (heatK_nonneg _ _)
        rw [this]; exact integral_heatK hx
      · simp [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hx),
          heatKP, heatK_of_nonpos (not_lt.mp hx)]
    rw [hfun, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi]
    have hsub : Set.Ioi (0:ℝ) ∩ Set.Iio T ⊆ Set.Ioo 0 T := fun x hx => hx
    exact (integrableOn_const (s := Set.Ioo (0:ℝ) T) (by simp)).mono_set hsub

theorem heatKP_locallyIntegrable : LocallyIntegrable heatKP (volume : Measure (ℝ × Vec 2)) := by
  intro p
  refine ⟨Set.Iio (p.1 + 1) ×ˢ Set.univ, ?_, heatKP_integrableOn_Iio _⟩
  exact (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨by simp, Set.mem_univ _⟩

/-! # Product rules for the space-time operators (skeleton) -/

private theorem fderiv_mul_apply' {f g : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p e : ℝ × Vec 2) :
    fderiv ℝ (fun z => f z * g z) p e = f p * fderiv ℝ g p e + g p * fderiv ℝ f p e := by
  have hfd : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have hgd : DifferentiableAt ℝ g p := (hg.differentiable (by simp)) p
  have hd : HasFDerivAt (fun z => f z * g z) _ p := hfd.hasFDerivAt.mul hgd.hasFDerivAt
  rw [hd.fderiv]
  simp

private theorem contDiff_fderiv_apply' {f : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (e : ℝ × Vec 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z e) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem stTimeDeriv_mul {f g : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : ℝ × Vec 2) :
    stTimeDeriv (fun z => f z * g z) p = f p * stTimeDeriv g p + g p * stTimeDeriv f p := by
  unfold stTimeDeriv
  exact fderiv_mul_apply' hf hg p _

theorem stSpaceLap_mul {f g : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : ℝ × Vec 2) :
    stSpaceLap (fun z => f z * g z) p = f p * stSpaceLap g p + g p * stSpaceLap f p
      + 2 * ∑ i : Fin 2, fderiv ℝ f p (0, basisVec i) * fderiv ℝ g p (0, basisVec i) := by
  unfold stSpaceLap
  have key : ∀ i : Fin 2,
      fderiv ℝ (fun q => fderiv ℝ (fun z => f z * g z) q (0, basisVec i)) p (0, basisVec i) =
        f p * fderiv ℝ (fun q => fderiv ℝ g q (0, basisVec i)) p (0, basisVec i)
        + g p * fderiv ℝ (fun q => fderiv ℝ f q (0, basisVec i)) p (0, basisVec i)
        + 2 * (fderiv ℝ f p (0, basisVec i) * fderiv ℝ g p (0, basisVec i)) := by
    intro i
    have hfun : (fun q => fderiv ℝ (fun z => f z * g z) q (0, basisVec i)) =
        fun q => f q * fderiv ℝ g q (0, basisVec i) + g q * fderiv ℝ f q (0, basisVec i) := by
      funext q; exact fderiv_mul_apply' hf hg q _
    rw [hfun]
    have h1 : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
    have h2 : DifferentiableAt ℝ g p := (hg.differentiable (by simp)) p
    have h3 := ((contDiff_fderiv_apply' hf (0, basisVec i)).differentiable (by simp)) p
    have h4 := ((contDiff_fderiv_apply' hg (0, basisVec i)).differentiable (by simp)) p
    have hd : HasFDerivAt (fun q => f q * fderiv ℝ g q (0, basisVec i)
        + g q * fderiv ℝ f q (0, basisVec i)) _ p :=
      (h1.hasFDerivAt.mul h4.hasFDerivAt).add (h2.hasFDerivAt.mul h3.hasFDerivAt)
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! # Explicit derivatives of the heat kernel for `r > 0` -/

/-- Spatial derivative of the quadratic form. -/
theorem hasFDerivAt_vecNormSq (ξ : Vec 2) :
    HasFDerivAt (fun y : Vec 2 => vecNormSq y)
      (∑ i, (2 * ξ i) • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) ξ := by
  have h : HasFDerivAt (fun y : Vec 2 => ∑ i, y i ^ 2)
      (∑ i, (2 * ξ i) • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) ξ := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hp : HasFDerivAt (fun y : Vec 2 => y i) (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ) ξ :=
      (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).hasFDerivAt
    simpa using hp.pow 2
  simpa [vecNormSq_eq_sum] using h

theorem hasFDerivAt_vecNormSq_apply_basis (ξ : Vec 2) (j : Fin 2) :
    (∑ i, (2 * ξ i) • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) (basisVec j) = 2 * ξ j := by
  fin_cases j <;> simp [basisVec, Fin.sum_univ_two]

/-- The spatial Fréchet derivative of `heatK r` for `r > 0`. -/
theorem hasFDerivAt_heatK {r : ℝ} (hr : 0 < r) (ξ : Vec 2) :
    HasFDerivAt (heatK r)
      ((-(heatK r ξ) / (4 * r)) •
        ∑ i, (2 * ξ i) • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) ξ := by
  have h1 := (((hasFDerivAt_vecNormSq ξ).const_mul (-(1 / (4 * r)))).exp).const_mul
    ((4 * Real.pi * r)⁻¹)
  have hfun : heatK r = fun y : Vec 2 =>
      (4 * Real.pi * r)⁻¹ * Real.exp (-(1 / (4 * r)) * vecNormSq y) := by
    funext y; rw [heatK_of_pos hr y]; congr 2; ring
  rw [hfun]
  convert h1 using 1
  ext y
  simp only [smul_apply, smul_eq_mul]
  have : -(1 / (4 * r)) * vecNormSq ξ = -vecNormSq ξ / (4 * r) := by ring
  rw [this]
  ring

theorem fderiv_heatK_basis {r : ℝ} (hr : 0 < r) (ξ : Vec 2) (j : Fin 2) :
    fderiv ℝ (heatK r) ξ (basisVec j) = -(ξ j / (2 * r)) * heatK r ξ := by
  rw [(hasFDerivAt_heatK hr ξ).fderiv]
  simp only [smul_apply, smul_eq_mul,
    hasFDerivAt_vecNormSq_apply_basis]
  field_simp
  ring

/-- Second derivative: `∂_j² Γ = (ξ_j²/(4r²) - 1/(2r)) Γ`. -/
theorem fderiv_fderiv_heatK_basis {r : ℝ} (hr : 0 < r) (ξ : Vec 2) (j : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ (heatK r) y (basisVec j)) ξ (basisVec j) =
      (ξ j ^ 2 / (4 * r ^ 2) - 1 / (2 * r)) * heatK r ξ := by
  have hfun : (fun y => fderiv ℝ (heatK r) y (basisVec j)) =
      fun y : Vec 2 => (-(1 / (2 * r)) * y j) * heatK r y := by
    funext y
    rw [fderiv_heatK_basis hr]
    ring
  rw [hfun]
  have h1 : HasFDerivAt (fun y : Vec 2 => (-(1 / (2 * r)) * y j))
      ((-(1 / (2 * r))) • (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ)) ξ := by
    have hp : HasFDerivAt (fun y : Vec 2 => y j) (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ) ξ :=
      (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).hasFDerivAt
    convert hp.const_mul (-(1 / (2 * r))) using 1
  rw [(h1.fun_mul (hasFDerivAt_heatK hr ξ)).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    hasFDerivAt_vecNormSq_apply_basis]
  simp [basisVec]
  field_simp
  ring

/-- The sum of second spatial derivatives of `Γ(r, ·)`. -/
theorem sum_second_deriv_heatK {r : ℝ} (hr : 0 < r) (ξ : Vec 2) :
    ∑ j : Fin 2, fderiv ℝ (fun y => fderiv ℝ (heatK r) y (basisVec j)) ξ (basisVec j) =
      (vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ := by
  simp only [fderiv_fderiv_heatK_basis hr, vecNormSq_eq_sum, Fin.sum_univ_two]
  field_simp
  ring

/-- Time derivative of the kernel for `r > 0`. -/
theorem hasDerivAt_heatK_time {r : ℝ} (hr : 0 < r) (ξ : Vec 2) :
    HasDerivAt (fun s => heatK s ξ) ((vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ) r := by
  have h1 : HasDerivAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ * Real.exp (-(vecNormSq ξ) / (4 * s)))
      ((vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ) r := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hA : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) r := by
      simpa using (hasDerivAt_id r).const_mul (4 * Real.pi)
    have hA' := hA.inv (by positivity)
    have hB : HasDerivAt (fun s : ℝ => 4 * s) 4 r := by
      simpa using (hasDerivAt_id r).const_mul (4 : ℝ)
    have hC := ((hasDerivAt_const r (-(vecNormSq ξ))).fun_div hB (by positivity))
    have hD := hC.exp
    have := hA'.mul hD
    convert this using 1
    rw [heatK_of_pos hr]
    simp only [Pi.inv_apply]
    field_simp
    ring
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact heatK_of_pos hs ξ

theorem continuousOn_heatK_pos : ContinuousOn (fun q : ℝ × Vec 2 => heatK q.1 q.2) {q | 0 < q.1} := by
  intro q hq
  have hq' : 0 < q.1 := hq
  refine ContinuousAt.continuousWithinAt ?_
  have : (fun q : ℝ × Vec 2 => heatK q.1 q.2) =ᶠ[nhds q]
      fun q => (4 * Real.pi * q.1)⁻¹ * Real.exp (-(vecNormSq q.2) / (4 * q.1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hq'] with p hp
    exact heatK_of_pos hp p.2
  refine ContinuousAt.congr ?_ this.symm
  have hv : Continuous fun p : ℝ × Vec 2 => vecNormSq p.2 := by
    simp only [vecNormSq_eq_sum]; fun_prop
  have h4 : (4 * Real.pi * q.1) ≠ 0 := by positivity
  have h5 : (4 * q.1) ≠ 0 := by positivity
  apply ContinuousAt.mul
  · exact (continuousAt_const.mul continuous_fst.continuousAt).inv₀ h4
  · exact (((hv.neg).continuousAt).div (continuous_const.mul continuous_fst).continuousAt h5).rexp

/-! # The representation kernel

`kern G z p = G(z - p) (∂ₛ + Δ)ω(p) - 2 ∇G(z - p) · ∇ω(p)` where `G` is a smooth modification of
the heat kernel. It is jointly smooth, and its `z`-derivative is bounded on compact sets. -/

/-- The spatial partial derivative `∂_{ξ_i} G`. -/
def kernD (G : ℝ × Vec 2 → ℝ) (i : Fin 2) (q : ℝ × Vec 2) : ℝ := fderiv ℝ G q (0, basisVec i)

/-- The representation kernel. -/
def kern (G : ℝ × Vec 2 → ℝ) (z p : ℝ × Vec 2) : ℝ :=
  G (z - p) * cutA p - 2 * ∑ i : Fin 2, kernD G i (z - p) * cutD i p

theorem contDiff_fderiv_dir_apply {f : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (e : ℝ × Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z e) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem contDiff_kernD {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (kernD G i) :=
  contDiff_fderiv_dir_apply hG _

theorem contDiff_cutD (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (cutD i) :=
  contDiff_fderiv_dir_apply cutω_contDiff _

theorem contDiff_cutA : ContDiff ℝ (⊤ : ℕ∞) cutA := by
  unfold cutA stTimeDeriv stSpaceLap
  refine (contDiff_fderiv_dir_apply cutω_contDiff _).add ?_
  exact ContDiff.sum fun i _ => contDiff_fderiv_dir_apply (contDiff_fderiv_dir_apply cutω_contDiff _) _

theorem contDiff_kern {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ × Vec 2) × (ℝ × Vec 2) => kern G x.1 x.2) := by
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ × Vec 2) × (ℝ × Vec 2) => x.1 - x.2) :=
    contDiff_fst.sub contDiff_snd
  unfold kern
  refine ((hG.comp hsub).mul (contDiff_cutA.comp contDiff_snd)).sub ?_
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact ((contDiff_kernD hG i).comp hsub).mul ((contDiff_cutD i).comp contDiff_snd)

theorem exists_kern_bound {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {Z K : Set (ℝ × Vec 2)} (hZ : IsCompact Z) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ z ∈ Z, ∀ p ∈ K, |kern G z p| ≤ M := by
  obtain ⟨M, hM⟩ := (hZ.prod hK).exists_bound_of_continuousOn
    (contDiff_kern hG).continuous.continuousOn
  exact ⟨M, fun z hz p hp => by simpa using hM (z, p) ⟨hz, hp⟩⟩

/-- The `z`-derivative of the kernel. -/
def kernZ (G : ℝ × Vec 2 → ℝ) (z p : ℝ × Vec 2) : (ℝ × Vec 2) →L[ℝ] ℝ :=
  cutA p • fderiv ℝ G (z - p) -
    (2 : ℝ) • ∑ i : Fin 2, cutD i p • fderiv ℝ (kernD G i) (z - p)

theorem hasFDerivAt_comp_sub {f : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z p : ℝ × Vec 2) :
    HasFDerivAt (fun z => f (z - p)) (fderiv ℝ f (z - p)) z := by
  have h1 : HasFDerivAt (fun z : ℝ × Vec 2 => z - p) (ContinuousLinearMap.id ℝ _) z :=
    (hasFDerivAt_id z).sub_const p
  have h2 : HasFDerivAt (fun z : ℝ × Vec 2 => f (z - p))
      ((fderiv ℝ f (z - p)).comp (ContinuousLinearMap.id ℝ _)) z :=
    ((hf.differentiable (by simp)) (z - p)).hasFDerivAt.comp z h1
  rwa [ContinuousLinearMap.comp_id] at h2

theorem hasFDerivAt_kern {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (z p : ℝ × Vec 2) :
    HasFDerivAt (fun z => kern G z p) (kernZ G z p) z := by
  unfold kern kernZ
  have h1 := (hasFDerivAt_comp_sub hG z p).mul_const (cutA p)
  have h2 : HasFDerivAt (fun z => ∑ i : Fin 2, kernD G i (z - p) * cutD i p)
      (∑ i : Fin 2, cutD i p • fderiv ℝ (kernD G i) (z - p)) z := by
    refine HasFDerivAt.fun_sum fun i _ => ?_
    simpa [mul_comm] using (hasFDerivAt_comp_sub (contDiff_kernD hG i) z p).const_mul (cutD i p)
  have h3 := (h1.sub (h2.const_mul (2 : ℝ)))
  convert h3 using 1

theorem continuous_kernZ {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (fun x : (ℝ × Vec 2) × (ℝ × Vec 2) => kernZ G x.1 x.2) := by
  have hsub : Continuous (fun x : (ℝ × Vec 2) × (ℝ × Vec 2) => x.1 - x.2) :=
    continuous_fst.sub continuous_snd
  unfold kernZ
  refine Continuous.sub ?_ (Continuous.fun_const_smul (continuous_finsetSum _ fun i _ => ?_) _)
  · exact ((contDiff_cutA.continuous.comp continuous_snd)).smul
      ((hG.continuous_fderiv (by simp)).comp hsub)
  · exact ((contDiff_cutD i).continuous.comp continuous_snd).smul
      (((contDiff_kernD hG i).continuous_fderiv (by simp)).comp hsub)

/-- Lipschitz bound for the kernel in the `z` variable, uniformly for `p` in a compact set. -/
theorem exists_kern_lipschitz {G : ℝ × Vec 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {Z K : Set (ℝ × Vec 2)} (hZ : IsCompact Z) (hZc : Convex ℝ Z) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Z, ∀ w ∈ Z, ∀ p ∈ K, |kern G w p - kern G z p| ≤ C * ‖w - z‖ := by
  obtain ⟨M, hM⟩ := (hZ.prod hK).exists_bound_of_continuousOn
    (continuous_kernZ hG).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun z hz w hw p hp => ?_⟩
  have hb : ∀ x ∈ Z, ‖fderiv ℝ (fun z => kern G z p) x‖ ≤ max M 0 := fun x hx => by
    rw [(hasFDerivAt_kern hG x p).fderiv]
    exact (hM (x, p) ⟨hx, hp⟩).trans (le_max_left _ _)
  have := hZc.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hasFDerivAt_kern hG x p).differentiableAt) hb hz hw
  simpa [Real.norm_eq_abs] using this

end AVRegularity.Applications.Caloric
end
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.Caloric

/-! # The approximate identity `∫ Γ(ε,ξ) v(ε,ξ) dξ → v(0,0)` -/

theorem vecNormSq_smul (c : ℝ) (η : Vec 2) : vecNormSq (c • η) = c ^ 2 * vecNormSq η := by
  simp [vecNormSq_eq_sum, mul_pow]
  ring

theorem heatK_sqrt_smul {ε : ℝ} (hε : 0 < ε) (η : Vec 2) :
    heatK ε (Real.sqrt ε • η) = ε⁻¹ * heatK 1 η := by
  rw [heatK_of_pos hε, heatK_of_pos one_pos, vecNormSq_smul, Real.sq_sqrt hε.le]
  have h1 : -(ε * vecNormSq η) / (4 * ε) = -(vecNormSq η) / (4 * 1) := by
    field_simp
  rw [h1]
  field_simp

theorem integral_heatK_mul_eq_scaled {g : Vec 2 → ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∫ ξ, heatK ε ξ * g ξ = ∫ η, heatK 1 η * g (Real.sqrt ε • η) := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec 2))
    (fun ξ => heatK ε ξ * g ξ) (Real.sqrt ε)
  have hs : (Real.sqrt ε ^ Module.finrank ℝ (Vec 2))⁻¹ = ε⁻¹ := by
    simp [Real.sq_sqrt hε.le]
  rw [hs, abs_of_pos (inv_pos.mpr hε), smul_eq_mul] at h
  have h2 : (fun η : Vec 2 => heatK ε (Real.sqrt ε • η) * g (Real.sqrt ε • η)) =
      fun η => ε⁻¹ * (heatK 1 η * g (Real.sqrt ε • η)) := by
    funext η
    rw [heatK_sqrt_smul hε]; ring
  simp only [h2, integral_const_mul] at h
  field_simp at h
  linarith

theorem tendsto_integral_heatK_mul {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hc : HasCompactSupport v) :
    Tendsto (fun ε => ∫ ξ, heatK ε ξ * v (ε, ξ)) (𝓝[>] 0) (𝓝 (v 0)) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖v x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hv.continuous.bounded_above_of_compact_support hc
    exact ⟨B, hB⟩
  have hint : Integrable (heatK 1) volume := integrable_heatK one_pos
  have hlim : Tendsto (fun ε : ℝ => ∫ η, heatK 1 η * v (ε, Real.sqrt ε • η)) (𝓝[>] 0)
      (𝓝 (∫ η, heatK 1 η * v 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun η => B * heatK 1 η) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun ε => ?_
      have hm : Continuous fun η : Vec 2 => v (ε, Real.sqrt ε • η) :=
        hv.continuous.comp (continuous_const.prodMk (continuous_const_smul _))
      exact hint.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun η => ?_
      rw [norm_mul, Real.norm_of_nonneg (heatK_nonneg 1 η)]
      nlinarith [hB (ε, Real.sqrt ε • η), heatK_nonneg 1 η, norm_nonneg (v (ε, Real.sqrt ε • η))]
    · exact (hint.const_mul B)
    · refine Eventually.of_forall fun η => ?_
      refine Tendsto.const_mul _ ?_
      have hcont : Continuous fun ε : ℝ => v (ε, Real.sqrt ε • η) :=
        hv.continuous.comp (continuous_id.prodMk (Real.continuous_sqrt.smul continuous_const))
      have := hcont.continuousAt (x := 0)
      have h0 : v ((0 : ℝ), Real.sqrt 0 • η) = v 0 := by simp [Prod.mk_zero_zero]
      have ht := this.tendsto
      rw [h0] at ht
      exact ht.mono_left nhdsWithin_le_nhds
  have hone : ∫ η, heatK 1 η * v 0 = v 0 := by
    rw [integral_mul_const, integral_heatK one_pos, one_mul]
  rw [hone] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_heatK_mul_eq_scaled (g := fun ξ => v (ε, ξ)) hε).symm

end AVRegularity.Applications.Caloric
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.Caloric

/-! # Slices, integration by parts and compact supports for the Duhamel identity -/

/-- Spatial slices differentiate as expected. -/
theorem fderiv_slice {f : ℝ × Vec 2 → ℝ} {r : ℝ} {ξ : Vec 2}
    (hf : DifferentiableAt ℝ f (r, ξ)) (e : Vec 2) :
    fderiv ℝ (fun y => f (r, y)) ξ e = fderiv ℝ f (r, ξ) (0, e) := by
  have hin : HasFDerivAt (fun y : Vec 2 => (r, y)) (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) ξ :=
    (hasFDerivAt_const r ξ).prodMk (hasFDerivAt_id ξ)
  have := hf.hasFDerivAt.comp ξ hin
  have h2 : fderiv ℝ (fun y => f (r, y)) ξ = fderiv ℝ f (r, ξ) ∘SL ContinuousLinearMap.inr ℝ ℝ (Vec 2) :=
    this.fderiv
  rw [h2]
  rfl

/-- Time slices differentiate as expected. -/
theorem hasDerivAt_time_slice {f : ℝ × Vec 2 → ℝ} {r : ℝ} {ξ : Vec 2}
    (hf : DifferentiableAt ℝ f (r, ξ)) :
    HasDerivAt (fun s => f (s, ξ)) (fderiv ℝ f (r, ξ) (1, 0)) r := by
  have hin : HasDerivAt (fun s : ℝ => (s, ξ)) ((1 : ℝ), (0 : Vec 2)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r ξ)
  exact hf.hasFDerivAt.comp_hasDerivAt r hin

/-- The spatial Laplacian of a space-time function is the Laplacian of its slice. -/
theorem stSpaceLap_eq_slice {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (r : ℝ)
    (ξ : Vec 2) :
    stSpaceLap v (r, ξ) = ∑ i : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ (fun z => v (r, z)) y (basisVec i)) ξ (basisVec i) := by
  unfold stSpaceLap
  refine Finset.sum_congr rfl fun i _ => ?_
  have hH : ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ v q (0, basisVec i)) :=
    (hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  rw [← AVRegularity.Applications.Caloric.fderiv_slice (hH.differentiable (by simp) _)]
  congr 2
  funext y
  exact (AVRegularity.Applications.Caloric.fderiv_slice (hv.differentiable (by simp) _) _).symm

/-- Directional derivatives of smooth functions are smooth. -/
theorem contDiff_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (e : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x e) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem contDiff_heatK {r : ℝ} (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (heatK r) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => vecNormSq y) := by
    simp only [vecNormSq_eq_sum]
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2
  have hfun : heatK r = fun y : Vec 2 =>
      (4 * Real.pi * r)⁻¹ * Real.exp (-(vecNormSq y) / (4 * r)) := by
    funext y; exact heatK_of_pos hr y
  rw [hfun]
  exact contDiff_const.mul (Real.contDiff_exp.comp (hv.neg.div_const _))

/-- Integration by parts in a coordinate direction for a smooth function and a smooth compactly
supported one. -/
theorem integral_mul_fderiv_eq {f g : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (e : Vec 2) :
    ∫ x, f x * fderiv ℝ g x e = - ∫ x, fderiv ℝ f x e * g x := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hdf : Continuous fun x => fderiv ℝ f x e := (contDiff_dirDeriv hf e).continuous
  have hdg : Continuous fun x => fderiv ℝ g x e := (contDiff_dirDeriv hg e).continuous
  have hcd : HasCompactSupport fun x => fderiv ℝ g x e := hc.fderiv_apply ℝ e
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hdf.mul hgc).integrable_of_hasCompactSupport (hc.mul_left)
  · exact (hfc.mul hdg).integrable_of_hasCompactSupport (hcd.mul_left)
  · exact (hfc.mul hgc).integrable_of_hasCompactSupport (hc.mul_left)
  · exact fun x _ => (hf.differentiable (by simp) x)
  · exact fun x _ => (hg.differentiable (by simp) x)

/-! # Smoothness of the heat kernel away from the origin

`heatKP` is smooth on `{q ≠ 0}` (the flat gluing function `expNegInvGlue` handles `r = 0`,
`ξ ≠ 0`), and has a globally smooth modification agreeing with it away from the origin. -/

/-- `G(t) = e^{-1/t}/t` for `t > 0` and `0` otherwise, written as `t * (expNegInvGlue)'`. -/
private def glueG (t : ℝ) : ℝ := t * deriv expNegInvGlue t

private theorem contDiff_glueG : ContDiff ℝ (⊤ : ℕ∞) glueG := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (deriv expNegInvGlue) := by
    have h1 := expNegInvGlue.contDiff (n := (⊤ : ℕ∞))
    exact (contDiff_succ_iff_deriv.mp (by simpa using h1)).2.2
  exact contDiff_id.mul h

private theorem glueG_of_pos {t : ℝ} (ht : 0 < t) : glueG t = Real.exp (-t⁻¹) / t := by
  have : deriv expNegInvGlue t = Real.exp (-t⁻¹) * (t ^ 2)⁻¹ := by
    have hev : expNegInvGlue =ᶠ[nhds t] fun s => Real.exp (-s⁻¹) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact by simp [expNegInvGlue, not_le.mpr hs]
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun s : ℝ => Real.exp (-s⁻¹)) (Real.exp (-t⁻¹) * (t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht.ne').neg.exp
      convert this using 1
      simp
    exact hd.deriv
  rw [glueG, this]
  field_simp

private theorem glueG_of_nonpos {t : ℝ} (ht : t ≤ 0) : glueG t = 0 := by
  rcases ht.lt_or_eq with h | h
  · have hev : expNegInvGlue =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact expNegInvGlue.zero_of_nonpos (le_of_lt hs)
    rw [glueG, hev.deriv_eq]; simp
  · simp [glueG, h]

private theorem heatKP_eq_glue {q : ℝ × Vec 2} (hq : vecNormSq q.2 ≠ 0) :
    heatKP q = (Real.pi * vecNormSq q.2)⁻¹ * glueG (4 * q.1 / vecNormSq q.2) := by
  have hn : 0 < vecNormSq q.2 := lt_of_le_of_ne (vecNormSq_nonneg _) (Ne.symm hq)
  by_cases hr : 0 < q.1
  · have ht : 0 < 4 * q.1 / vecNormSq q.2 := by positivity
    rw [glueG_of_pos ht, heatKP, heatK_of_pos hr]
    have h1 : (4 * q.1 / vecNormSq q.2)⁻¹ = vecNormSq q.2 / (4 * q.1) := by
      rw [inv_div]
    rw [h1]
    have h2 : -(vecNormSq q.2 / (4 * q.1)) = -vecNormSq q.2 / (4 * q.1) := by ring
    rw [h2]
    field_simp
  · rw [glueG_of_nonpos (by
      have : 4 * q.1 ≤ 0 := by linarith [not_lt.mp hr]
      exact div_nonpos_of_nonpos_of_nonneg this hn.le), heatKP,
      heatK_of_nonpos (not_lt.mp hr)]
    simp

theorem heatKP_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) heatKP {q : ℝ × Vec 2 | q ≠ 0} := by
  apply contDiffOn_of_locally_contDiffOn
  intro q hq
  have hq' : q ≠ 0 := hq
  have hn : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => vecNormSq p.2) :=
    contDiff_vecNormSq.comp contDiff_snd
  by_cases h2 : vecNormSq q.2 ≠ 0
  · refine ⟨{p | vecNormSq p.2 ≠ 0}, ?_, h2, ?_⟩
    · exact isOpen_ne_fun hn.continuous continuous_const
    · have : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : ℝ × Vec 2 => (Real.pi * vecNormSq p.2)⁻¹ *
            glueG (4 * p.1 / vecNormSq p.2)) {p | vecNormSq p.2 ≠ 0} := by
        have hne : ∀ p ∈ {p : ℝ × Vec 2 | vecNormSq p.2 ≠ 0}, vecNormSq p.2 ≠ 0 := fun p hp => hp
        refine ContDiffOn.mul ?_ ?_
        · exact ContDiffOn.inv (contDiff_const.mul hn).contDiffOn
            (fun p hp => mul_ne_zero Real.pi_ne_zero (hne p hp))
        · exact contDiff_glueG.comp_contDiffOn
            ((contDiff_const.mul contDiff_fst).contDiffOn.div hn.contDiffOn hne)
      exact (this.congr (fun p hp => heatKP_eq_glue hp)).mono Set.inter_subset_right
  · have h2' : vecNormSq q.2 = 0 := not_not.mp h2
    have hξ : q.2 = 0 := by
      by_contra hne
      apply hne
      funext i
      have := sq_apply_le_vecNormSq q.2 i
      rw [h2'] at this
      simpa using pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
    have hr : q.1 ≠ 0 := by
      intro h; apply hq'; exact Prod.ext h hξ
    rcases hr.lt_or_gt with hlt | hgt
    · refine ⟨{p | p.1 < 0}, isOpen_lt continuous_fst continuous_const, hlt, ?_⟩
      have : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℝ × Vec 2 => (0 : ℝ)) {p : ℝ × Vec 2 | p.1 < 0} := contDiffOn_const
      exact (this.congr (fun p hp => by
        have h : p.1 < 0 := hp
        exact heatK_of_nonpos h.le p.2)).mono Set.inter_subset_right
    · refine ⟨{p | 0 < p.1}, isOpen_lt continuous_const continuous_fst, hgt, ?_⟩
      have hn' : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => vecNormSq p.2) := hn
      have : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (4 * Real.pi * p.1)⁻¹ *
          Real.exp (-(vecNormSq p.2) / (4 * p.1))) {p | 0 < p.1} := by
        refine ContDiffOn.mul ?_ ?_
        · exact ContDiffOn.inv ((contDiff_const.mul contDiff_fst).contDiffOn)
            (fun p hp => by have : 0 < p.1 := hp; positivity)
        · exact Real.contDiff_exp.comp_contDiffOn
            ((hn'.neg).contDiffOn.div ((contDiff_const.mul contDiff_fst).contDiffOn)
              (fun p hp => by have : 0 < p.1 := hp; positivity))
      exact (this.congr (fun p hp => by
        have : 0 < p.1 := hp
        simp [heatKP, heatK_of_pos this])).mono Set.inter_subset_right

/-- A globally smooth modification of the heat kernel agreeing with it away from the origin
(on `|ξ|² ≥ 1/64` or `r ≥ 9/64`). -/
theorem exists_smooth_heatKernel :
    ∃ G : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      ∀ q : ℝ × Vec 2, (1 / 64 ≤ vecNormSq q.2 ∨ 9 / 64 ≤ q.1) → G q = heatKP q := by
  let b : ContDiffBump (0 : ℝ × Vec 2) :=
    ⟨1 / 24, 1 / 12, by norm_num, by norm_num⟩
  refine ⟨fun q => heatKP q * (1 - b q), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q = 0
    · subst hq
      have hev : (fun q : ℝ × Vec 2 => heatKP q * (1 - b q)) =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
        filter_upwards [b.eventuallyEq_one] with p hp
        simp [hp]
      exact (contDiffAt_const).congr_of_eventuallyEq hev
    · have hopen : IsOpen {q : ℝ × Vec 2 | q ≠ 0} := isOpen_ne
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) heatKP q :=
        heatKP_contDiffOn.contDiffAt (hopen.mem_nhds hq)
      exact h1.mul (contDiffAt_const.sub b.contDiff.contDiffAt)
  · intro q hq
    have hout : b q = 0 := by
      apply b.zero_of_le_dist
      show (1 / 12 : ℝ) ≤ dist q 0
      rw [dist_zero_right]
      rcases hq with h | h
      · by_contra hlt
        push Not at hlt
        have hc : ∀ i : Fin 2, q.2 i ^ 2 ≤ (1 / 12) ^ 2 := by
          intro i
          have h1 : |q.2 i| ≤ ‖q‖ := (norm_le_pi_norm q.2 i).trans (norm_snd_le q)
          have h2 : |q.2 i| ≤ 1 / 12 := by
            have := Real.norm_eq_abs (q.2 i) ▸ h1
            linarith
          have := abs_le.mp h2
          nlinarith [this.1, this.2]
        have : vecNormSq q.2 ≤ 2 * (1 / 12) ^ 2 := by
          unfold vecNormSq vecDot
          simp only [Fin.sum_univ_two]
          nlinarith [hc 0, hc 1]
        norm_num at this
        linarith
      · exact le_trans (by norm_num) (le_trans h (le_trans (le_abs_self _) (norm_fst_le q)))
    simp [hout]

/-! # The slice identity `∫ Γ Δv = ∫ ΔΓ v` and regularity of the space-time operators -/

theorem integrable_mul_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) μ :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_left

theorem hasCompactSupport_slice {v : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport v) (r : ℝ) :
    HasCompactSupport (fun y : Vec 2 => v (r, y)) := by
  refine HasCompactSupport.intro (hc.isCompact.image continuous_snd) ?_
  intro y hy
  by_contra hne
  exact hy ⟨(r, y), subset_tsupport _ hne, rfl⟩

theorem contDiff_slice {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => v (r, y)) :=
  hv.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_stTimeDeriv {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (stTimeDeriv v) := contDiff_dirDeriv hv (1, 0)

theorem contDiff_stSpaceLap {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (stSpaceLap v) := by
  have : stSpaceLap v = fun p => ∑ i : Fin 2,
      fderiv ℝ (fun q => fderiv ℝ v q (0, basisVec i)) p (0, basisVec i) := rfl
  rw [this]
  exact ContDiff.sum fun i _ => contDiff_dirDeriv (contDiff_dirDeriv hv _) _

theorem hasCompactSupport_stTimeDeriv {v : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (stTimeDeriv v) := hc.fderiv_apply ℝ (1, 0)

theorem hasCompactSupport_stSpaceLap {v : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (stSpaceLap v) := by
  have : stSpaceLap v = fun p => ∑ i : Fin 2,
      fderiv ℝ (fun q => fderiv ℝ v q (0, basisVec i)) p (0, basisVec i) := rfl
  rw [this]
  simp only [Fin.sum_univ_two]
  exact ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).add ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _)

theorem exists_bound_zero {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} (hf : HasCompactSupport f) :
    ∃ C : ℝ, ∀ p, C < ‖p‖ → f p = 0 := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  refine ⟨C, fun p hp => ?_⟩
  by_contra hne
  exact absurd (hC p (subset_tsupport _ hne)) (not_le.mpr hp)

/-- Slice identity: `∫ Γ(r,·) Δv(r,·) = ∫ ΔΓ(r,·) v(r,·)`. -/
theorem integral_heatK_stSpaceLap {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hc : HasCompactSupport v) {r : ℝ} (hr : 0 < r) :
    ∫ ξ, heatK r ξ * stSpaceLap v (r, ξ) =
      ∫ ξ, ((vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ) * v (r, ξ) := by
  set w : Vec 2 → ℝ := fun y => v (r, y) with hw
  have hwd : ContDiff ℝ (⊤ : ℕ∞) w := contDiff_slice hv r
  have hwc : HasCompactSupport w := hasCompactSupport_slice hc r
  have hΓ : ContDiff ℝ (⊤ : ℕ∞) (heatK r) := contDiff_heatK hr
  have key : ∀ i : Fin 2, ∫ ξ, heatK r ξ *
      fderiv ℝ (fun y => fderiv ℝ w y (basisVec i)) ξ (basisVec i) =
      ∫ ξ, fderiv ℝ (fun y => fderiv ℝ (heatK r) y (basisVec i)) ξ (basisVec i) * w ξ := by
    intro i
    have hE : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ (heatK r) y (basisVec i)) :=
      contDiff_dirDeriv hΓ _
    have hdw : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ w y (basisVec i)) :=
      contDiff_dirDeriv hwd _
    have hdwc : HasCompactSupport (fun y => fderiv ℝ w y (basisVec i)) := hwc.fderiv_apply ℝ _
    rw [integral_mul_fderiv_eq hΓ hdw hdwc, integral_mul_fderiv_eq hE hwd hwc,
      neg_neg]
  have hI1 : ∀ i : Fin 2, Integrable (fun ξ => heatK r ξ *
      fderiv ℝ (fun y => fderiv ℝ w y (basisVec i)) ξ (basisVec i)) := fun i =>
    integrable_mul_of_compact hΓ.continuous
      (contDiff_dirDeriv (contDiff_dirDeriv hwd _) _).continuous
      ((hwc.fderiv_apply ℝ _).fderiv_apply ℝ _)
  have hI2 : ∀ i : Fin 2, Integrable (fun ξ =>
      fderiv ℝ (fun y => fderiv ℝ (heatK r) y (basisVec i)) ξ (basisVec i) * w ξ) := fun i =>
    integrable_mul_of_compact
      (contDiff_dirDeriv (contDiff_dirDeriv hΓ _) _).continuous hwd.continuous hwc
  have h1 : ∀ ξ, heatK r ξ * stSpaceLap v (r, ξ) = ∑ i : Fin 2, heatK r ξ *
      fderiv ℝ (fun y => fderiv ℝ w y (basisVec i)) ξ (basisVec i) := fun ξ => by
    rw [stSpaceLap_eq_slice hv, Finset.mul_sum]
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => hI1 i)]
  simp_rw [key]
  rw [← integral_finsetSum _ (fun i _ => hI2 i)]
  congr 1
  funext ξ
  rw [← Finset.sum_mul, sum_second_deriv_heatK hr]

end AVRegularity.Applications.Caloric
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Set
namespace AVRegularity.Applications.Caloric

/-! # Duhamel identity at the origin

For `v ∈ C_c^∞(ℝ × ℝ²)`: `∬ Γ(r,ξ) (∂_r v + Δ v)(r,ξ) = -v(0,0)`. The proof integrates by parts
in `ξ` at each fixed `r > 0`, recognises `∂_r(Γ v)`, applies Fubini and the fundamental theorem of
calculus on `(ε, R)`, and lets `ε → 0`. -/

/-- The `r`-derivative of `Γ(r,ξ) v(r,ξ)`. -/
def Fdu (v : ℝ × Vec 2 → ℝ) (r : ℝ) (ξ : Vec 2) : ℝ :=
  (vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ * v (r, ξ) + heatK r ξ * stTimeDeriv v (r, ξ)

theorem hasDerivAt_heatK_mul {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) {r : ℝ}
    (hr : 0 < r) (ξ : Vec 2) :
    HasDerivAt (fun s => heatK s ξ * v (s, ξ)) (Fdu v r ξ) r :=
  (hasDerivAt_heatK_time hr ξ).fun_mul (hasDerivAt_time_slice (hv.differentiable (by simp) _))

private theorem cont_slice {f : ℝ × Vec 2 → ℝ} (hf : Continuous f) (r : ℝ) :
    Continuous fun ξ : Vec 2 => f (r, ξ) := hf.comp (continuous_const.prodMk continuous_id)

theorem integral_heatK_psi {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hc : HasCompactSupport v) {r : ℝ} (hr : 0 < r) :
    ∫ ξ, heatK r ξ * (stTimeDeriv v (r, ξ) + stSpaceLap v (r, ξ)) = ∫ ξ, Fdu v r ξ := by
  have hΓ := (contDiff_heatK hr).continuous
  have I1 : Integrable (fun ξ => heatK r ξ * stTimeDeriv v (r, ξ)) volume :=
    integrable_mul_of_compact hΓ (cont_slice (contDiff_stTimeDeriv hv).continuous r)
      (hasCompactSupport_slice (hasCompactSupport_stTimeDeriv hc) r)
  have I2 : Integrable (fun ξ => heatK r ξ * stSpaceLap v (r, ξ)) volume :=
    integrable_mul_of_compact hΓ (cont_slice (contDiff_stSpaceLap hv).continuous r)
      (hasCompactSupport_slice (hasCompactSupport_stSpaceLap hc) r)
  have hX : Continuous fun ξ : Vec 2 => (vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ := by
    have : Continuous fun ξ : Vec 2 => vecNormSq ξ := by
      simp only [vecNormSq_eq_sum]; fun_prop
    exact ((this.div_const _).sub continuous_const).mul hΓ
  have I3 : Integrable (fun ξ => ((vecNormSq ξ / (4 * r ^ 2) - 1 / r) * heatK r ξ) * v (r, ξ))
      volume :=
    integrable_mul_of_compact hX (cont_slice hv.continuous r) (hasCompactSupport_slice hc r)
  simp_rw [mul_add]
  rw [integral_add I1 I2, integral_heatK_stSpaceLap hv hc hr, add_comm]
  unfold Fdu
  rw [integral_add I3 I1]

theorem continuousOn_Fdu {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContinuousOn (fun q : ℝ × Vec 2 => Fdu v q.1 q.2) {q | 0 < q.1} := by
  have hH := continuousOn_heatK_pos
  have hn : Continuous fun q : ℝ × Vec 2 => vecNormSq q.2 := by
    simp only [vecNormSq_eq_sum]; fun_prop
  have hne : ∀ q ∈ {q : ℝ × Vec 2 | 0 < q.1}, q.1 ≠ 0 := fun q hq => (ne_of_gt hq)
  have hX : ContinuousOn (fun q : ℝ × Vec 2 => vecNormSq q.2 / (4 * q.1 ^ 2) - 1 / q.1)
      {q | 0 < q.1} := by
    refine ContinuousOn.sub (ContinuousOn.div hn.continuousOn (by fun_prop) ?_)
      (ContinuousOn.div continuousOn_const continuous_fst.continuousOn hne)
    intro q hq
    have := hne q hq
    positivity
  have hvc : Continuous fun q : ℝ × Vec 2 => v (q.1, q.2) := hv.continuous
  have hTc : Continuous fun q : ℝ × Vec 2 => stTimeDeriv v (q.1, q.2) :=
    (contDiff_stTimeDeriv hv).continuous
  unfold Fdu
  exact ((hX.mul hH).mul hvc.continuousOn).add (hH.mul hTc.continuousOn)

theorem continuousOn_Fdu_slice {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) {ε R : ℝ}
    (hε : 0 < ε) (ξ : Vec 2) : ContinuousOn (fun r : ℝ => Fdu v r ξ) (Icc ε R) := by
  have hf : Continuous (fun r : ℝ => (r, ξ)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun r : ℝ => (r, ξ)) (Icc ε R) {q : ℝ × Vec 2 | 0 < q.1} :=
    fun r hr => lt_of_lt_of_le hε hr.1
  have := (continuousOn_Fdu hv).comp hf.continuousOn hmaps
  exact this

theorem fubini_step {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) {C ε R : ℝ}
    (hC : ∀ p : ℝ × Vec 2, C < ‖p‖ → v p = 0 ∧ stTimeDeriv v p = 0) (hε : 0 < ε)
    (hεR : ε ≤ R) (hCR : C < R) :
    ∫ r in Ioc ε R, ∫ ξ, Fdu v r ξ = - ∫ ξ, heatK ε ξ * v (ε, ξ) := by
  have hzero : ∀ r ξ, C < ‖ξ‖ → Fdu v r ξ = 0 := by
    intro r ξ h
    have hn : C < ‖(r, ξ)‖ := lt_of_lt_of_le h (by simp [Prod.norm_def])
    obtain ⟨h1, h2⟩ := hC _ hn
    simp [Fdu, h1, h2]
  have hK : IsCompact (Icc ε R ×ˢ Metric.closedBall (0 : Vec 2) C) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hFK : IntegrableOn (fun q : ℝ × Vec 2 => Fdu v q.1 q.2)
      (Icc ε R ×ˢ Metric.closedBall (0 : Vec 2) C) volume :=
    ((continuousOn_Fdu hv).mono (fun q hq => lt_of_lt_of_le hε hq.1.1)).integrableOn_compact hK
  have hbig : IntegrableOn (fun q : ℝ × Vec 2 => Fdu v q.1 q.2) (Icc ε R ×ˢ univ) volume := by
    refine hFK.of_forall_sdiff_eq_zero (measurableSet_Icc.prod MeasurableSet.univ) ?_
    intro q hq
    have : q.2 ∉ Metric.closedBall (0 : Vec 2) C := fun h => hq.2 ⟨hq.1.1, h⟩
    exact hzero _ _ (by simpa [mem_closedBall_zero_iff] using this)
  have hint : Integrable (Function.uncurry (Fdu v)) ((volume.restrict (Ioc ε R)).prod volume) := by
    have h1 : IntegrableOn (fun q : ℝ × Vec 2 => Fdu v q.1 q.2) (Ioc ε R ×ˢ univ) volume :=
      hbig.mono_set (prod_mono Ioc_subset_Icc_self subset_rfl)
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
      at h1
    exact h1
  rw [integral_integral_swap hint]
  have hinner : ∀ ξ : Vec 2, ∫ r in Ioc ε R, Fdu v r ξ =
      heatK R ξ * v (R, ξ) - heatK ε ξ * v (ε, ξ) := by
    intro ξ
    rw [← intervalIntegral.integral_of_le hεR]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => heatK r ξ * v (r, ξ))
      (f' := fun r => Fdu v r ξ) (fun r hr => ?_) ?_
    · rw [uIcc_of_le hεR] at hr
      exact hasDerivAt_heatK_mul hv (lt_of_lt_of_le hε hr.1) ξ
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hεR]
      exact continuousOn_Fdu_slice hv hε ξ
  simp_rw [hinner]
  have hR : ∀ ξ : Vec 2, v (R, ξ) = 0 := fun ξ =>
    (hC (R, ξ) (lt_of_lt_of_le hCR ((le_abs_self R).trans
      (by rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _)))).1
  simp only [hR, mul_zero, zero_sub, integral_neg]

/-- For `v ∈ C_c^∞(ℝ × ℝ²)`: `∬ Γ(r,ξ) (∂_r v + Δ v)(r,ξ) = -v(0,0)`. -/
theorem heatKP_duhamel {v : ℝ × Vec 2 → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hc : HasCompactSupport v) :
    ∫ q, heatKP q * (stTimeDeriv v q + stSpaceLap v q) = - v 0 := by
  obtain ⟨C₁, h₁⟩ := exists_bound_zero hc
  obtain ⟨C₂, h₂⟩ := exists_bound_zero (hasCompactSupport_stTimeDeriv hc)
  obtain ⟨C₃, h₃⟩ := exists_bound_zero (hasCompactSupport_stSpaceLap hc)
  have hC : ∀ p : ℝ × Vec 2, max C₁ (max C₂ C₃) < ‖p‖ →
      v p = 0 ∧ stTimeDeriv v p = 0 ∧ stSpaceLap v p = 0 := fun p hp =>
    ⟨h₁ p (lt_of_le_of_lt (le_max_left _ _) hp),
      h₂ p (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp),
      h₃ p (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp)⟩
  generalize max C₁ (max C₂ C₃) = C at hC
  set R : ℝ := |C| + 1 with hRdef
  have hCR : C < R := by have := le_abs_self C; linarith
  have hR0 : 0 < R := by positivity
  have hψc : Continuous fun q => stTimeDeriv v q + stSpaceLap v q :=
    (contDiff_stTimeDeriv hv).continuous.add (contDiff_stSpaceLap hv).continuous
  have hψs : HasCompactSupport fun q => stTimeDeriv v q + stSpaceLap v q :=
    (hasCompactSupport_stTimeDeriv hc).add (hasCompactSupport_stSpaceLap hc)
  have hΦ : Integrable (fun q : ℝ × Vec 2 => heatKP q * (stTimeDeriv v q + stSpaceLap v q))
      volume :=
    heatKP_locallyIntegrable.integrable_smul_right_of_hasCompactSupport hψc hψs
  set A : ℝ → ℝ := fun r => ∫ ξ, heatKP (r, ξ) * (stTimeDeriv v (r, ξ) + stSpaceLap v (r, ξ))
    with hA
  have hΦ' : Integrable (fun q : ℝ × Vec 2 => heatKP q * (stTimeDeriv v q + stSpaceLap v q))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hΦ
  have hsplit : ∫ q, heatKP q * (stTimeDeriv v q + stSpaceLap v q) = ∫ r, A r := by
    rw [Measure.volume_eq_prod, integral_prod _ hΦ']
  have hAint : Integrable A volume := hΦ'.integral_prod_left
  have hAneg : ∀ r, r ≤ 0 → A r = 0 := fun r hr => by
    simp [hA, heatKP, heatK_of_nonpos hr]
  have hApos : ∀ r, R < r → A r = 0 := fun r hr => by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun ξ => ?_)
    have hn : C < ‖(r, ξ)‖ := lt_of_lt_of_le (by linarith)
      ((le_abs_self r).trans (by rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _))
    obtain ⟨-, h2, h3⟩ := hC _ hn
    simp [h2, h3]
  have h1 : Tendsto (fun ε => ∫ r in Ioc ε R, A r) (𝓝[>] 0) (𝓝 (∫ r, A r)) := by
    have e1 : ∀ ε : ℝ, ∫ r in Ioc ε R, A r = ∫ r, (Ioc ε R).indicator A r := fun ε =>
      (integral_indicator measurableSet_Ioc).symm
    simp_rw [e1]
    refine tendsto_integral_filter_of_dominated_convergence (fun r => ‖A r‖) ?_ ?_ hAint.norm ?_
    · exact Eventually.of_forall fun ε => hAint.aestronglyMeasurable.indicator measurableSet_Ioc
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun r =>
        norm_indicator_le_norm_self _ _
    · refine Eventually.of_forall fun r => ?_
      by_cases hr0 : r ≤ 0
      · rw [hAneg r hr0]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [indicator_of_notMem (fun h => by have := h.1; have : 0 < ε := hε; linarith)]
      · by_cases hrR : R < r
        · rw [hApos r hrR]
          refine tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_)
          show 0 = (Ioc ε R).indicator A r
          rw [indicator_of_notMem (fun h : r ∈ Ioc ε R => by have := h.2; linarith)]
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT (lt_of_not_ge hr0)] with ε hε
          show A r = (Ioc ε R).indicator A r
          rw [indicator_of_mem (show r ∈ Ioc ε R from ⟨hε.2, not_lt.mp hrR⟩)]
  have h2 : ∀ᶠ ε in 𝓝[>] 0, ∫ r in Ioc ε R, A r = - ∫ ξ, heatK ε ξ * v (ε, ξ) := by
    filter_upwards [Ioo_mem_nhdsGT hR0] with ε hε
    rw [← fubini_step hv (fun p hp => (hC p hp).imp_right And.left) hε.1 hε.2.le hCR]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    exact integral_heatK_psi hv hc (lt_of_lt_of_le hε.1 hr.1.le)
  have h3 := (tendsto_integral_heatK_mul hv hc).neg
  rw [hsplit]
  exact tendsto_nhds_unique (h1.congr' h2) h3

end AVRegularity.Applications.Caloric
end
end
end
