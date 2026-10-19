-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Parabolic.SliceGrad
public import AVRegularity.Applications.LocalEnergy.Mollifier
import Mathlib.MeasureTheory.Function.L2Space
import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Limit

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.LocalEnergy

/-! # Classical energy identity for smooth space-time functions

If `w` and `Pw` are `C¹`, `∂ₜw = div Pw + gw` and `∇w = Dw` on `I × tsupport ζ`, then
`E(τ) = ∫ ζ² w(τ,·)²` is differentiable on `I` and satisfies the integrated energy identity
with flux integrand `fluxIntegrand`. This is the calculus core of the time-mollification
argument for `local_energy_identity`. -/

/-- The flux integrand of the energy identity. -/
def fluxIntegrand (ζ : Vec 2 → ℝ) (w : ℝ × Vec 2 → ℝ) (Pw Dw : ℝ × Vec 2 → Vec 2)
    (gw : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  vecDot (Pw p) (ζ p.2 ^ 2 • Dw p + (2 * ζ p.2 * w p) • spGrad ζ p.2) - gw p * ζ p.2 ^ 2 * w p

theorem fderiv_slice {f : ℝ × Vec 2 → ℝ} (hf : Differentiable ℝ f) (τ : ℝ) (y v : Vec 2) :
    fderiv ℝ (fun z : Vec 2 => f (τ, z)) y v = fderiv ℝ f (τ, y) (0, v) := by
  have h1 : HasFDerivAt f (fderiv ℝ f (τ, y)) (τ, y) := (hf (τ, y)).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Vec 2 => (τ, z))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have := (h1.comp y h2).fderiv
  change fderiv ℝ (f ∘ Prod.mk τ) y v = _
  rw [this]
  simp

theorem differentiable_slice {f : ℝ × Vec 2 → ℝ} (hf : Differentiable ℝ f) (τ : ℝ) :
    Differentiable ℝ (fun z : Vec 2 => f (τ, z)) :=
  hf.comp (differentiable_const τ |>.prodMk differentiable_id)

theorem continuous_slice {f : ℝ × Vec 2 → ℝ} (hf : Continuous f) (τ : ℝ) :
    Continuous (fun z : Vec 2 => f (τ, z)) :=
  hf.comp (continuous_const.prodMk continuous_id)

/-- Integration by parts in one space direction for compactly supported `C¹` factors. -/
theorem ibp_dir (f g : Vec 2 → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (v : Vec 2) :
    ∫ y, f y * fderiv ℝ g y v = -∫ y, fderiv ℝ f y v * g y := by
  have hfd : Continuous fun y => fderiv ℝ f y := hf.continuous_fderiv one_ne_zero
  have hgd : Continuous fun y => fderiv ℝ g y := hg.continuous_fderiv one_ne_zero
  have hfv : Continuous fun y => fderiv ℝ f y v :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hfd
  have hgv : Continuous fun y => fderiv ℝ g y v :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hgd
  have hfcd : HasCompactSupport fun y => fderiv ℝ f y v :=
    (hfc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L v) (by simp)
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hfv.mul hg.continuous).integrable_of_hasCompactSupport hfcd.mul_right
  · exact (hf.continuous.mul hgv).integrable_of_hasCompactSupport hfc.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · exact fun x _ => hf.differentiable one_ne_zero x
  · exact fun x _ => hg.differentiable one_ne_zero x

theorem hasDerivAt_integral_sq (ζ : Vec 2 → ℝ) (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 1 w) (τ₀ : ℝ) :
    HasDerivAt (fun τ => ∫ y, ζ y ^ 2 * w (τ, y) ^ 2)
      (∫ y, 2 * ζ y ^ 2 * w (τ₀, y) * fderiv ℝ w (τ₀, y) (1, 0)) τ₀ := by
  have hwc : Continuous w := hw.continuous
  have hdc : Continuous fun p => fderiv ℝ w p := hw.continuous_fderiv one_ne_zero
  have h1 : Continuous fun p : ℝ × Vec 2 => fderiv ℝ w p (1, 0) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Vec 2))).continuous.comp hdc
  set F' : ℝ → Vec 2 → ℝ := fun τ y => 2 * ζ y ^ 2 * w (τ, y) * fderiv ℝ w (τ, y) (1, 0) with hF'
  have hF'c : Continuous (Function.uncurry F') := by
    unfold Function.uncurry
    simp only [hF']
    have : Continuous fun q : ℝ × Vec 2 => ζ q.2 := hζ.comp continuous_snd
    fun_prop
  have hK : IsCompact (Set.Icc (τ₀ - 1) (τ₀ + 1) ×ˢ tsupport ζ) :=
    isCompact_Icc.prod hζc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'c.continuousOn (s := Set.Icc (τ₀ - 1) (τ₀ + 1) ×ˢ tsupport ζ))
  have hzero : ∀ y, y ∉ tsupport ζ → ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hcont_F : Continuous fun p : ℝ × Vec 2 => ζ p.2 ^ 2 * w p ^ 2 := by
    have : Continuous fun q : ℝ × Vec 2 => ζ q.2 := hζ.comp continuous_snd
    fun_prop
  have hint : ∀ τ, Integrable (fun y => ζ y ^ 2 * w (τ, y) ^ 2) := by
    intro τ
    have hc : Continuous fun y => ζ y ^ 2 * w (τ, y) ^ 2 := by
      have : Continuous fun y : Vec 2 => w (τ, y) := hwc.comp (by fun_prop)
      fun_prop
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hζc ?_
    intro y hy
    simp [hzero y hy]
  have hF'meas : AEStronglyMeasurable (F' τ₀) volume := by
    have hc : Continuous (F' τ₀) := by
      have : Continuous fun y : Vec 2 => (τ₀, y) := by fun_prop
      exact hF'c.comp (Continuous.prodMk continuous_const continuous_id)
    exact hc.aestronglyMeasurable
  have hbd_int : Integrable (fun y => M * (tsupport ζ).indicator (fun _ => (1 : ℝ)) y) := by
    refine Integrable.const_mul ?_ M
    exact (integrable_indicator_iff hζc.isCompact.measurableSet).2
      (integrableOn_const (hζc.isCompact.measure_lt_top.ne) |>.mono_set subset_rfl)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ y => ζ y ^ 2 * w (τ, y) ^ 2) (F' := F') (x₀ := τ₀)
    (s := Set.Ioo (τ₀ - 1) (τ₀ + 1)) (bound := fun y => M * (tsupport ζ).indicator (fun _ => (1 : ℝ)) y)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun τ => (hint τ).aestronglyMeasurable) (hint τ₀) hF'meas
    (Eventually.of_forall fun y τ hτ => by
      by_cases hy : y ∈ tsupport ζ
      · have := hM (τ, y) ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hy⟩
        simpa [hy, hF', Function.uncurry] using this
      · simp [hF', hzero y hy, hy])
    hbd_int
    (Eventually.of_forall fun y τ _ => by
      have hwd : HasDerivAt (fun τ => w (τ, y)) (fderiv ℝ w (τ, y) (1, 0)) τ := by
        have h1 : HasFDerivAt w (fderiv ℝ w (τ, y)) (τ, y) :=
          (hw.differentiable one_ne_zero (τ, y)).hasFDerivAt
        have h2 : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : Vec 2)) τ :=
          (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
        exact h1.comp_hasDerivAt τ h2
      have := ((hwd.pow 2).const_mul (ζ y ^ 2))
      convert this using 1
      simp [hF']; ring)
  exact key.2


theorem fderiv_sq_mul (ζ : Vec 2 → ℝ) (hζ : Differentiable ℝ ζ) (u : Vec 2 → ℝ)
    (hu : Differentiable ℝ u) (y v : Vec 2) :
    fderiv ℝ (fun z => ζ z ^ 2 * u z) y v =
      2 * ζ y * fderiv ℝ ζ y v * u y + ζ y ^ 2 * fderiv ℝ u y v := by
  have h1 : HasFDerivAt (fun z => ζ z ^ 2 * u z) _ y :=
    ((hζ y).hasFDerivAt.pow 2).mul (hu y).hasFDerivAt
  rw [h1.fderiv]
  simp
  ring


theorem integrable_of_zero_off {ζ : Vec 2 → ℝ} (hζc : HasCompactSupport ζ) {h : Vec 2 → ℝ}
    (hh : Continuous h) (h0 : ∀ y, y ∉ tsupport ζ → h y = 0) : Integrable h :=
  hh.integrable_of_hasCompactSupport (HasCompactSupport.intro hζc h0)

theorem hasDerivAt_energy {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {w gw : ℝ × Vec 2 → ℝ} {Pw Dw : ℝ × Vec 2 → Vec 2}
    (hw : ContDiff ℝ 1 w) (hP : ∀ i, ContDiff ℝ 1 (fun p => Pw p i))
    (hD : ∀ i, Continuous fun p => Dw p i) (hg : Continuous gw) (τ₀ : ℝ)
    (htime : ∀ y ∈ tsupport ζ, fderiv ℝ w (τ₀, y) (1, 0) =
      ∑ i, fderiv ℝ (fun p => Pw p i) (τ₀, y) (0, basisVec i) + gw (τ₀, y))
    (hgrad : ∀ y ∈ tsupport ζ, ∀ i, fderiv ℝ w (τ₀, y) (0, basisVec i) = Dw (τ₀, y) i) :
    HasDerivAt (fun τ => ∫ y, ζ y ^ 2 * w (τ, y) ^ 2)
      (-2 * ∫ y, fluxIntegrand ζ w Pw Dw gw (τ₀, y)) τ₀ := by
  have h0 := hasDerivAt_integral_sq ζ hζ.continuous hζc w hw τ₀
  convert h0 using 1
  have hzero : ∀ y, y ∉ tsupport ζ → ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdzero : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
  set wτ : Vec 2 → ℝ := fun y => w (τ₀, y) with hwτ
  have hwτc : ContDiff ℝ 1 wτ := hw.comp (contDiff_const.prodMk contDiff_id)
  have hPτ : ∀ i, ContDiff ℝ 1 (fun y => Pw (τ₀, y) i) := fun i =>
    (hP i).comp (contDiff_const.prodMk contDiff_id)
  set f : Vec 2 → ℝ := fun y => ζ y ^ 2 * wτ y with hf
  have hfc : ContDiff ℝ 1 f := (hζ.pow 2).mul hwτc
  have hfcs : HasCompactSupport f := by
    refine HasCompactSupport.intro hζc ?_
    intro y hy
    simp [hf, hzero y hy]
  have hwτd : Differentiable ℝ wτ := hwτc.differentiable one_ne_zero
  have hζd : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  have hwd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hPd : ∀ i, Differentiable ℝ (fun p => Pw p i) := fun i => (hP i).differentiable one_ne_zero
  -- the derivative of f in direction e_i
  have hfder : ∀ i y, fderiv ℝ f y (basisVec i) =
      ζ y ^ 2 * Dw (τ₀, y) i + 2 * ζ y * wτ y * fderiv ℝ ζ y (basisVec i) := by
    intro i y
    simp only [hf]
    rw [fderiv_sq_mul ζ hζd wτ hwτd]
    by_cases hy : y ∈ tsupport ζ
    · have : fderiv ℝ wτ y (basisVec i) = Dw (τ₀, y) i := by
        rw [hwτ, AVRegularity.Applications.LocalEnergy.fderiv_slice hwd, hgrad y hy i]
      rw [this]; ring
    · simp [hzero y hy]
  -- pointwise rewriting of the integrand
  have hkey : ∀ y, 2 * ζ y ^ 2 * w (τ₀, y) * fderiv ℝ w (τ₀, y) (1, 0) =
      2 * (gw (τ₀, y) * ζ y ^ 2 * w (τ₀, y)) +
        ∑ i : Fin 2, 2 * (f y * fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i)) := by
    intro y
    by_cases hy : y ∈ tsupport ζ
    · rw [htime y hy]
      have hs : ∀ i, fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i) =
          fderiv ℝ (fun p => Pw p i) (τ₀, y) (0, basisVec i) := fun i =>
        AVRegularity.Applications.LocalEnergy.fderiv_slice (hPd i) τ₀ y _
      simp only [hs, hf, hwτ, Fin.sum_univ_two]
      ring
    · simp [hzero y hy, hf]
  -- integrability facts
  have hwτcont : Continuous wτ := hwτc.continuous
  have hζcont : Continuous ζ := hζ.continuous
  have hdζcont : ∀ i, Continuous fun y => fderiv ℝ ζ y (basisVec i) := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp (hζ.continuous_fderiv one_ne_zero)
  have hPcont : ∀ i, Continuous fun y => Pw (τ₀, y) i := fun i => (hPτ i).continuous
  have hDcont : ∀ i, Continuous fun y => Dw (τ₀, y) i := fun i =>
    (hD i).comp (continuous_const.prodMk continuous_id)
  have hdPcont : ∀ i, Continuous fun y => fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i) := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
      ((hPτ i).continuous_fderiv one_ne_zero)
  have hfz : ∀ y, y ∉ tsupport ζ → f y = 0 := fun y hy => by simp [hf, hzero y hy]
  set A : Fin 2 → Vec 2 → ℝ := fun i y => Pw (τ₀, y) i *
    (ζ y ^ 2 * Dw (τ₀, y) i + 2 * ζ y * wτ y * fderiv ℝ ζ y (basisVec i)) with hA
  set G : Vec 2 → ℝ := fun y => gw (τ₀, y) * ζ y ^ 2 * wτ y with hG
  have hAcont : ∀ i, Continuous (A i) := fun i => by
    have := hPcont i; have := hDcont i; have := hdζcont i
    simp only [hA]; fun_prop
  have hAz : ∀ i y, y ∉ tsupport ζ → A i y = 0 := fun i y hy => by simp [hA, hzero y hy]
  have hGcont : Continuous G := by
    have : Continuous fun y => gw (τ₀, y) := hg.comp (continuous_const.prodMk continuous_id)
    simp only [hG]; fun_prop
  have hGz : ∀ y, y ∉ tsupport ζ → G y = 0 := fun y hy => by simp [hG, hzero y hy]
  have hFPcont : ∀ i, Continuous fun y => f y * fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i) :=
    fun i => hfc.continuous.mul (hdPcont i)
  have hFPz : ∀ i y, y ∉ tsupport ζ →
      f y * fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i) = 0 := fun i y hy => by
    simp [hfz y hy]
  have hAint := fun i => integrable_of_zero_off hζc (hAcont i) (hAz i)
  have hGint := integrable_of_zero_off hζc hGcont hGz
  have hFPint := fun i => integrable_of_zero_off hζc (hFPcont i) (hFPz i)
  have hibp : ∀ i, ∫ y, f y * fderiv ℝ (fun z => Pw (τ₀, z) i) y (basisVec i) = -∫ y, A i y := by
    intro i
    rw [ibp_dir f (fun y => Pw (τ₀, y) i) hfc (hPτ i) hfcs (basisVec i)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hfder, hA]
    ring
  -- flux integral
  have hflux : ∀ y, fluxIntegrand ζ w Pw Dw gw (τ₀, y) = A 0 y + A 1 y - G y := by
    intro y
    simp [fluxIntegrand, vecDot, Fin.sum_univ_two, hA, hG, spGrad, hwτ]
  have hL : ∫ y, fluxIntegrand ζ w Pw Dw gw (τ₀, y) = (∫ y, A 0 y) + (∫ y, A 1 y) - ∫ y, G y := by
    simp_rw [hflux]
    have h1 := integral_sub ((hAint 0).add (hAint 1)) hGint
    have h2 := integral_add (hAint 0) (hAint 1)
    simp only [Pi.add_apply] at h1
    rw [h1, h2]
  have hR : ∫ y, 2 * ζ y ^ 2 * w (τ₀, y) * fderiv ℝ w (τ₀, y) (1, 0) =
      2 * (∫ y, G y) + 2 * (∫ y, f y * fderiv ℝ (fun z => Pw (τ₀, z) 0) y (basisVec 0)) +
        2 * (∫ y, f y * fderiv ℝ (fun z => Pw (τ₀, z) 1) y (basisVec 1)) := by
    have hpt : ∀ y, 2 * ζ y ^ 2 * w (τ₀, y) * fderiv ℝ w (τ₀, y) (1, 0) =
        (2 * G y + 2 * (f y * fderiv ℝ (fun z => Pw (τ₀, z) 0) y (basisVec 0))) +
          2 * (f y * fderiv ℝ (fun z => Pw (τ₀, z) 1) y (basisVec 1)) := by
      intro y
      rw [hkey y, Fin.sum_univ_two]
      simp only [hG, hwτ]
      ring
    simp_rw [hpt]
    have h1 := integral_add ((hGint.const_mul 2).add ((hFPint 0).const_mul 2)) ((hFPint 1).const_mul 2)
    have h2 := integral_add (hGint.const_mul 2) ((hFPint 0).const_mul 2)
    simp only [Pi.add_apply] at h1
    rw [h1, h2]
    simp only [integral_const_mul]
  rw [hL, hR, hibp 0, hibp 1]
  ring


theorem continuous_flux {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ 1 ζ)
    {w gw : ℝ × Vec 2 → ℝ} {Pw Dw : ℝ × Vec 2 → Vec 2}
    (hw : Continuous w) (hP : ∀ i, Continuous fun p => Pw p i)
    (hD : ∀ i, Continuous fun p => Dw p i) (hg : Continuous gw) :
    Continuous (fluxIntegrand ζ w Pw Dw gw) := by
  have hζc : Continuous fun p : ℝ × Vec 2 => ζ p.2 := hζ.continuous.comp continuous_snd
  have hdζ : ∀ i, Continuous fun p : ℝ × Vec 2 => spGrad ζ p.2 i := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp
      ((hζ.continuous_fderiv one_ne_zero).comp continuous_snd)
  have := fun i => hP i
  have := fun i => hD i
  have := fun i => hdζ i
  unfold fluxIntegrand vecDot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem flux_zero_off {ζ : Vec 2 → ℝ} {w gw : ℝ × Vec 2 → ℝ} {Pw Dw : ℝ × Vec 2 → Vec 2}
    (p : ℝ × Vec 2) (hp : p.2 ∉ tsupport ζ) : fluxIntegrand ζ w Pw Dw gw p = 0 := by
  have h0 : ζ p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
  have h1 : spGrad ζ p.2 = 0 := by
    funext i
    simp [spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp]
  simp [fluxIntegrand, h0, h1, vecDot]

theorem classical_energy_identity {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {B : Set (Vec 2)} (hB : MeasurableSet B) (hζB : tsupport ζ ⊆ B)
    {w gw : ℝ × Vec 2 → ℝ} {Pw Dw : ℝ × Vec 2 → Vec 2}
    (hw : ContDiff ℝ 1 w) (hP : ∀ i, ContDiff ℝ 1 (fun p => Pw p i))
    (hD : ∀ i, Continuous fun p => Dw p i) (hg : Continuous gw)
    {I : Set ℝ} (hI : I.OrdConnected)
    (htime : ∀ τ ∈ I, ∀ y ∈ tsupport ζ, fderiv ℝ w (τ, y) (1, 0) =
      ∑ i, fderiv ℝ (fun p => Pw p i) (τ, y) (0, basisVec i) + gw (τ, y))
    (hgrad : ∀ τ ∈ I, ∀ y ∈ tsupport ζ, ∀ i,
      fderiv ℝ w (τ, y) (0, basisVec i) = Dw (τ, y) i)
    {τ₁ τ₂ : ℝ} (h1 : τ₁ ∈ I) (h2 : τ₂ ∈ I) (h12 : τ₁ ≤ τ₂) :
    (∫ y in B, ζ y ^ 2 * w (τ₂, y) ^ 2) - ∫ y in B, ζ y ^ 2 * w (τ₁, y) ^ 2 =
      -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ w Pw Dw gw p := by
  have hzero : ∀ y, y ∉ tsupport ζ → ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hfull : ∀ τ, (∫ y in B, ζ y ^ 2 * w (τ, y) ^ 2) = ∫ y, ζ y ^ 2 * w (τ, y) ^ 2 := by
    intro τ
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    have : y ∉ tsupport ζ := fun h => hy (hζB h)
    simp [hzero y this]
  rw [hfull, hfull]
  set Φ : ℝ → ℝ := fun τ => -2 * ∫ y, fluxIntegrand ζ w Pw Dw gw (τ, y) with hΦ
  have hfc : Continuous (fluxIntegrand ζ w Pw Dw gw) :=
    continuous_flux hζ hw.continuous (fun i => (hP i).continuous) hD hg
  have hΦc : Continuous Φ := by
    have hint : ∀ τ, (∫ y, fluxIntegrand ζ w Pw Dw gw (τ, y)) =
        ∫ y in tsupport ζ, fluxIntegrand ζ w Pw Dw gw (τ, y) := by
      intro τ
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
      exact flux_zero_off (ζ := ζ) (w := w) (Pw := Pw) (Dw := Dw) (gw := gw) (τ, y) hy
    simp only [hΦ, hint]
    refine continuous_const.mul ?_
    exact continuous_parametric_integral_of_continuous
      (f := fun τ y => fluxIntegrand ζ w Pw Dw gw (τ, y)) (hfc.comp continuous_id) hζc.isCompact
  have hderiv : ∀ τ ∈ Set.uIcc τ₁ τ₂, HasDerivAt (fun τ => ∫ y, ζ y ^ 2 * w (τ, y) ^ 2) (Φ τ) τ := by
    intro τ hτ
    have hτI : τ ∈ I := by
      rw [Set.uIcc_of_le h12] at hτ
      exact hI.out h1 h2 hτ
    exact hasDerivAt_energy hζ hζc hw hP hD hg τ (htime τ hτI) (hgrad τ hτI)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hΦc.intervalIntegrable _ _)
  rw [← hftc, intervalIntegral.integral_of_le h12]
  have hint : ∀ τ, (∫ y, fluxIntegrand ζ w Pw Dw gw (τ, y)) =
      ∫ y in B, fluxIntegrand ζ w Pw Dw gw (τ, y) := by
    intro τ
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    exact flux_zero_off (ζ := ζ) (w := w) (Pw := Pw) (Dw := Dw) (gw := gw) (τ, y)
      (fun h => hy (hζB h))
  have hKc : IsCompact (Set.Icc τ₁ τ₂ ×ˢ tsupport ζ) := isCompact_Icc.prod hζc
  have hIntOn : IntegrableOn (fluxIntegrand ζ w Pw Dw gw) (Set.Ioc τ₁ τ₂ ×ˢ B)
      (volume.prod volume) := by
    have h0 : IntegrableOn (fluxIntegrand ζ w Pw Dw gw) (Set.Icc τ₁ τ₂ ×ˢ tsupport ζ)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hfc.continuousOn.integrableOn_compact hKc
    have h1 : IntegrableOn (fluxIntegrand ζ w Pw Dw gw) (Set.Ioc τ₁ τ₂ ×ˢ tsupport ζ)
        (volume.prod volume) := h0.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self subset_rfl)
    refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioc.prod hB) ?_
    intro p hp
    refine flux_zero_off p fun h => hp.2 ?_
    exact ⟨hp.1.1, h⟩
  rw [Measure.volume_eq_prod, setIntegral_prod _ hIntOn]
  simp_rw [hΦ, hint]
  rw [integral_const_mul]

end AVRegularity.Applications.LocalEnergy
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # The spatial cutoff for the Caccioppoli inequality

`caccCut y = smoothTransition ((3/4 - |y|²)/(3/4 - 9/16))` equals `1` on `|y|² ≤ 9/16`
(in particular on the closed disc of radius `3/4`), vanishes for `|y|² ≥ 3/4`, and has compact
support inside the open unit disc. -/

/-- The cutoff used in the Caccioppoli inequality. -/
def caccCut (y : Vec 2) : ℝ :=
  Real.smoothTransition ((3 / 4 - vecNormSq y) / (3 / 4 - 9 / 16))

theorem contDiff_vecNormSq' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => vecNormSq y) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i))

theorem caccCut_contDiff : ContDiff ℝ (⊤ : ℕ∞) caccCut := by
  unfold caccCut
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_vecNormSq').div_const _)

theorem caccCut_nonneg (y : Vec 2) : 0 ≤ caccCut y := Real.smoothTransition.nonneg _

theorem caccCut_le_one (y : Vec 2) : caccCut y ≤ 1 := Real.smoothTransition.le_one _

theorem caccCut_eq_one {y : Vec 2} (h : vecNormSq y ≤ 9 / 16) : caccCut y = 1 := by
  unfold caccCut
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem caccCut_eq_zero {y : Vec 2} (h : 3 / 4 ≤ vecNormSq y) : caccCut y = 0 := by
  unfold caccCut
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

theorem isCompact_cutSet : IsCompact {y : Vec 2 | vecNormSq y ≤ 3 / 4} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le contDiff_vecNormSq'.continuous continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Vec 2)) (r := 1)).subset ?_
    intro y hy
    simp only [Set.mem_ofPred_eq, vecNormSq, vecDot, Fin.sum_univ_two] at hy
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    fin_cases i <;> simp <;> constructor <;> nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1)]

theorem isOpen_euclidBall_zero (r : ℝ) : IsOpen (euclidBall (0 : Vec 2) r) := by
  unfold euclidBall
  simp only [sub_zero]
  exact isOpen_lt contDiff_vecNormSq'.continuous continuous_const

theorem caccCut_support_subset : Function.support caccCut ⊆ {y : Vec 2 | vecNormSq y ≤ 3 / 4} := by
  intro y hy
  by_contra h
  exact hy (caccCut_eq_zero (not_le.1 h).le)

theorem caccCut_isSpTest : IsSpTest (euclidBall 0 1) caccCut := by
  refine ⟨caccCut_contDiff, ?_, ?_⟩
  · exact HasCompactSupport.intro isCompact_cutSet fun y hy =>
      caccCut_eq_zero (not_le.1 hy).le
  · refine (closure_minimal caccCut_support_subset
      (isClosed_le contDiff_vecNormSq'.continuous continuous_const)).trans ?_
    intro y hy
    have hy' : vecNormSq y ≤ 3 / 4 := hy
    simp only [euclidBall, sub_zero]
    exact lt_of_le_of_lt hy' (by norm_num)

theorem spGrad_caccCut_eq_zero {y : Vec 2} (hy : y ∈ euclidBall 0 (3 / 4)) (i : Fin 2) :
    spGrad caccCut y i = 0 := by
  have hopen := isOpen_euclidBall_zero (3 / 4)
  have hev : caccCut =ᶠ[nhds y] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    apply caccCut_eq_one
    have hz' : vecNormSq z < (3 / 4) ^ 2 := by simpa [euclidBall] using hz
    norm_num at hz'
    linarith
  simp [spGrad, hev.fderiv_eq]

theorem spGrad_caccCut_continuous (i : Fin 2) : Continuous fun y => spGrad caccCut y i := by
  unfold spGrad
  exact (caccCut_contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A uniform bound on the gradient of the cutoff. -/
theorem exists_caccCut_grad_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, vecNormSq (spGrad caccCut y) ≤ L ^ 2 := by
  have hb : ∀ i : Fin 2, ∃ C : ℝ, ∀ y, ‖spGrad caccCut y i‖ ≤ C := by
    intro i
    have hc : HasCompactSupport fun y => spGrad caccCut y i := by
      exact (caccCut_isSpTest.2.1.fderiv ℝ).comp_left
        (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
    exact (spGrad_caccCut_continuous i).bounded_above_of_compact_support hc
  obtain ⟨C0, hC0⟩ := hb 0
  obtain ⟨C1, hC1⟩ := hb 1
  refine ⟨2 * (|C0| + |C1|), by positivity, fun y => ?_⟩
  have h0 := (hC0 y).trans (le_abs_self C0)
  have h1 := (hC1 y).trans (le_abs_self C1)
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  rw [Real.norm_eq_abs] at h0 h1
  have := sq_abs (spGrad caccCut y 0)
  have := sq_abs (spGrad caccCut y 1)
  nlinarith [abs_nonneg C0, abs_nonneg C1, abs_nonneg (spGrad caccCut y 0),
    abs_nonneg (spGrad caccCut y 1)]

end AVRegularity.Applications
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Set Filter Topology
namespace AVRegularity.Applications

/-! # Measure-theoretic plumbing for the Caccioppoli inequality -/

/-- Square-bounded functions are `L²`. -/
theorem memLp_two_of_sq_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : AEStronglyMeasurable f μ) (hg : MemLp g 2 μ)
    (h : ∀ᵐ x ∂μ, f x ^ 2 ≤ c * g x ^ 2) : MemLp f 2 μ := by
  refine hg.of_le_mul (c := Real.sqrt c) hf ?_
  filter_upwards [h] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ (by positivity)
  calc f x ^ 2 ≤ c * g x ^ 2 := hx
    _ = (Real.sqrt c * |g x|) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc, sq_abs]

theorem volume_euclidBall_zero_lt_top (r : ℝ) : volume (euclidBall (0 : Vec 2) r) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall (0 : Vec 2) |r|) ?_)
    (isCompact_closedBall _ _).measure_lt_top
  intro y hy
  simp only [euclidBall, sub_zero, mem_ofPred_eq, vecNormSq, vecDot, Fin.sum_univ_two] at hy
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ (abs_nonneg r)
  rw [sq_abs]
  fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1)]

theorem openCyl_one : openCyl 0 1 = Ioo (-1 : ℝ) 0 ×ˢ euclidBall (0 : Vec 2) 1 := by
  simp [openCyl]

/-- `L²` functions on a space-time product have `L²` slices. -/
theorem memLp_slice {S : Set ℝ} {B : Set (Vec 2)} {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (S ×ˢ B))) :
    ∀ᵐ τ ∂(volume.restrict S), MemLp (fun y => f (τ, y)) 2 (volume.restrict B) := by
  have hμ : volume.restrict (S ×ˢ B) = (volume.restrict S).prod (volume.restrict B) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [hμ] at hf
  have h1 := hf.integrable_sq.prod_right_ae
  have h2 := hf.aestronglyMeasurable.prodMk_left
  filter_upwards [h1, h2] with τ h1τ h2τ
  exact (memLp_two_iff_integrable_sq h2τ).2 h1τ

theorem integral_stTimeDeriv_eq_zero_Q1 {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (openCyl 0 1) φ) :
    ∫ p in openCyl 0 1, stTimeDeriv φ p = 0 := by
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hT : IsCompact (tsupport φ) := hφ.2.1
  have hfd : ∀ p, p ∉ tsupport φ → fderiv ℝ φ p = 0 := fun p hp => by
    have h := notMem_tsupport_iff_eventuallyEq.1 hp
    have := h.fderiv_eq (𝕜 := ℝ)
    simpa using this
  have hcont : Continuous (stTimeDeriv φ) := by
    unfold stTimeDeriv
    exact (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport (stTimeDeriv φ) := by
    refine HasCompactSupport.intro hT fun p hp => ?_
    simp [stTimeDeriv, hfd p hp]
  have hint : Integrable (stTimeDeriv φ) volume := hcont.integrable_of_hasCompactSupport hsupp
  have hzero' : ∀ p ∉ tsupport φ, stTimeDeriv φ p = 0 := fun p hp => by
    simp [stTimeDeriv, hfd p hp]
  have hzero : ∀ p ∉ openCyl 0 1, stTimeDeriv φ p = 0 := fun p hp =>
    hzero' p fun h => hp (hφ.2.2 h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, Measure.volume_eq_prod,
    integral_prod_symm _ (by rwa [← Measure.volume_eq_prod])]
  have : ∀ y : Vec 2, ∫ τ : ℝ, stTimeDeriv φ (τ, y) = 0 := fun y => by
    refine integral_eq_zero_of_hasDerivAt_of_integrable (f := fun τ => φ (τ, y)) ?_ ?_ ?_
    · intro τ
      have h1 : HasDerivAt (fun τ : ℝ => ((τ, y) : ℝ × Vec 2)) ((1 : ℝ), (0 : Vec 2)) τ :=
        (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
      exact (hdiff (τ, y)).hasFDerivAt.comp_hasDerivAt τ h1
    · have hc : Continuous fun τ : ℝ => stTimeDeriv φ (τ, y) :=
        hcont.comp (continuous_id.prodMk continuous_const)
      refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hT.image continuous_fst)
        fun τ hτ => hzero' (τ, y) fun h => hτ ⟨(τ, y), h, rfl⟩)
    · have hc : Continuous fun τ : ℝ => φ (τ, y) :=
        hdiff.continuous.comp (continuous_id.prodMk continuous_const)
      refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hT.image continuous_fst)
        fun τ hτ => image_eq_zero_of_notMem_tsupport fun h => hτ ⟨(τ, y), h, rfl⟩)
  simp [this]

/-- Dropping the (null) top face of a space-time cylinder. -/
theorem Ioc_prod_ae_eq_Ioo_prod (a b : ℝ) (B : Set (Vec 2)) :
    (Ioc a b ×ˢ B : Set (ℝ × Vec 2)) =ᵐ[volume] (Ioo a b ×ˢ B : Set (ℝ × Vec 2)) := by
  have h0 : (volume : Measure (ℝ × Vec 2)) (({b} : Set ℝ) ×ˢ B) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ h0
    rintro ⟨t, y⟩ ⟨⟨⟨h1, h2⟩, hy⟩, hn⟩
    refine ⟨?_, hy⟩
    by_contra hb
    exact hn ⟨⟨h1, lt_of_le_of_ne h2 hb⟩, hy⟩
  · refine measure_mono_null ?_ (measure_empty (μ := (volume : Measure (ℝ × Vec 2))))
    rintro ⟨t, y⟩ ⟨⟨⟨h1, h2⟩, hy⟩, hn⟩
    exact absurd ⟨⟨h1, h2.le⟩, hy⟩ hn

theorem setIntegral_Ioc_prod_eq {f : ℝ × Vec 2 → ℝ} (a b : ℝ) (B : Set (Vec 2)) :
    ∫ p in Ioc a b ×ˢ B, f p = ∫ p in Ioo a b ×ˢ B, f p :=
  setIntegral_congr_set (Ioc_prod_ae_eq_Ioo_prod a b B)

/-- A continuous function dominated a.e. by a nonnegative integrable one has an average
point `τ₁ ∈ [-1,-9/16]` with `E τ₁ ≤ (16/7) M`. -/
theorem exists_tau_le_of_avg {E m : ℝ → ℝ} {M : ℝ}
    (hE : ContinuousOn E (Icc (-1) 0))
    (hae : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), E τ = m τ)
    (hmi : IntegrableOn m (Ioo (-1) 0)) (hm0 : ∀ τ, 0 ≤ m τ)
    (hM : ∫ τ in Ioo (-1 : ℝ) 0, m τ ≤ M) :
    ∃ τ₁ ∈ Icc (-1 : ℝ) (-9 / 16), E τ₁ ≤ 16 / 7 * M := by
  have hsub : Icc (-1 : ℝ) (-9 / 16) ⊆ Icc (-1) 0 := Icc_subset_Icc le_rfl (by norm_num)
  have hEint : IntegrableOn E (Icc (-1 : ℝ) (-9 / 16)) :=
    (hE.mono hsub).integrableOn_Icc
  have hvol : volume (Icc (-1 : ℝ) (-9 / 16)) = ENNReal.ofReal (7 / 16) := by
    rw [Real.volume_Icc]; norm_num
  obtain ⟨x, hx, hle⟩ := exists_le_setAverage (μ := volume) (s := Icc (-1 : ℝ) (-9 / 16))
    (by rw [hvol]; simp) (by rw [hvol]; simp) hEint
  refine ⟨x, hx, hle.trans ?_⟩
  rw [setAverage_eq, smul_eq_mul]
  have hreal : volume.real (Icc (-1 : ℝ) (-9 / 16)) = 7 / 16 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (by norm_num)]
  rw [hreal]
  have hI : ∫ a in Icc (-1 : ℝ) (-9 / 16), E a ≤ M := by
    rw [← setIntegral_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (-1 : ℝ)) (b := -9 / 16))]
    have hsub2 : Ioo (-1 : ℝ) (-9 / 16) ⊆ Ioo (-1) 0 := Ioo_subset_Ioo le_rfl (by norm_num)
    have hae2 : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) (-9 / 16))), E τ = m τ :=
      ae_restrict_of_ae_restrict_of_subset hsub2 hae
    rw [setIntegral_congr_ae measurableSet_Ioo (ae_restrict_iff' measurableSet_Ioo |>.1 hae2)]
    refine le_trans ?_ hM
    exact setIntegral_mono_set hmi (Eventually.of_forall hm0) hsub2.eventuallyLE
  have h7 : (7 / 16 : ℝ)⁻¹ = 16 / 7 := by norm_num
  rw [h7]
  exact mul_le_mul_of_nonneg_left hI (by norm_num)

/-- A function continuous on `[-1,0]` and a.e. nonnegative on `(-1,0)` is nonnegative at `0`. -/
theorem nonneg_zero_of_ae {E : ℝ → ℝ} (hE : ContinuousOn E (Icc (-1) 0))
    (hae : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), 0 ≤ E τ) : 0 ≤ E 0 := by
  have hae' : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ioo (-1 : ℝ) 0 → 0 ≤ E τ :=
    (ae_restrict_iff' measurableSet_Ioo).1 hae
  have hd := Measure.dense_of_ae (μ := (volume : Measure ℝ)) hae'
  have hcl : IsClosed (Icc (-1 : ℝ) 0 ∩ E ⁻¹' Ici 0) :=
    hE.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h1 : Ioo (-1 : ℝ) 0 ⊆ closure (Ioo (-1 : ℝ) 0 ∩ {τ | τ ∈ Ioo (-1 : ℝ) 0 → 0 ≤ E τ}) :=
    hd.open_subset_closure_inter isOpen_Ioo
  have h2 : Ioo (-1 : ℝ) 0 ∩ {τ | τ ∈ Ioo (-1 : ℝ) 0 → 0 ≤ E τ} ⊆
      Icc (-1 : ℝ) 0 ∩ E ⁻¹' Ici 0 := fun τ ⟨h, h'⟩ => ⟨Ioo_subset_Icc_self h, h' h⟩
  have h4 : closure (Ioo (-1 : ℝ) 0) ⊆
      closure (Ioo (-1 : ℝ) 0 ∩ {τ | τ ∈ Ioo (-1 : ℝ) 0 → 0 ≤ E τ}) :=
    closure_minimal h1 isClosed_closure
  have h0 : (0 : ℝ) ∈ closure (Ioo (-1 : ℝ) 0) := by
    rw [closure_Ioo (by norm_num)]; simp
  exact (closure_minimal h2 hcl (h4 h0)).2

end AVRegularity.Applications
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open AVRegularity.Applications.LocalEnergy.Moll
namespace AVRegularity.Applications

/-! # Weak gradients: shifts, products with cutoffs, and divergence-free drifts

* `hasWeakGradientOn_sub_const`, `hasWeakGradientOn_smul_smooth`: elementary calculus of weak
  gradients (product rule against a `C^∞_c` cutoff).
* `divFree_integral_grad`, `divFree_integral_mul_grad`: for a.e. time slice, a bounded
  divergence-free drift annihilates `∇ψ` and `ψ ∇ψ` for compactly supported `H¹` functions `ψ`
  (smooth approximation by mollification, see `DivFreeMollify`). -/

/-- The integral of a coordinate derivative of a `C^∞_c` function vanishes. -/
theorem integral_fderiv_basis_eq_zero {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin 2) :
    ∫ x, fderiv ℝ φ x (basisVec i) = 0 := by
  have hcont : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Vec 2))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := φ) (f' := fun x => fderiv ℝ φ x (basisVec i)) (g := fun _ => (1 : ℝ))
    (g' := fun _ => 0)
    (v := basisVec i) (by simpa using hcont.integrable_of_hasCompactSupport hcs)
    (by simp) (by simpa using hφ.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => ((hφ.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt _)
    (fun x _ => by simpa using ((hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt (basisVec i)))
  simpa using h.symm

/-- weak gradient of a constant-shifted function -/
theorem hasWeakGradientOn_sub_const {B : Set (Vec 2)} (_hB : IsOpen B) {u : Vec 2 → ℝ}
    {Du : Vec 2 → Vec 2} (h : HasWeakGradientOn B u Du) (c : ℝ) :
    HasWeakGradientOn B (fun y => u y - c) Du := by
  intro i φ hφ hφc hφB
  rw [← h i φ hφ hφc hφB]
  have hcont : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have hc0 : ∫ x in B, fderiv ℝ φ x (basisVec i) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_fderiv_basis_eq_zero hφ hφc i]
    intro y hy
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hy (hφB h))]
    simp
  have hci : IntegrableOn (fun x => c * fderiv ℝ φ x (basisVec i)) B volume :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn.const_mul c
  by_cases hi : IntegrableOn (fun x => u x * fderiv ℝ φ x (basisVec i)) B volume
  · have e : (fun x => (u x - c) * fderiv ℝ φ x (basisVec i)) =
        fun x => u x * fderiv ℝ φ x (basisVec i) - c * fderiv ℝ φ x (basisVec i) := by
      ext x; ring
    rw [e, integral_sub hi hci, integral_const_mul, hc0]
    ring
  · have hni : ¬ IntegrableOn (fun x => (u x - c) * fderiv ℝ φ x (basisVec i)) B volume := by
      intro h2
      apply hi
      have := h2.add hci
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]; ring
    rw [integral_undef hni, integral_undef hi]

/-- `g * f` is integrable on `B` for `g ∈ L²(B)` and `f` continuous with compact support. -/
theorem integrableOn_mul_cpt {B : Set (Vec 2)} {g f : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict B)) (hf : Continuous f) (hc : HasCompactSupport f) :
    IntegrableOn (fun x => g x * f x) B volume :=
  hg.integrable_mul (hf.memLp_of_hasCompactSupport (p := 2) hc)

/-- product rule for the weak gradient against a smooth compactly supported cutoff -/
theorem hasWeakGradientOn_smul_smooth {B : Set (Vec 2)} (_hB : IsOpen B) {u : Vec 2 → ℝ}
    {Du : Vec 2 → Vec 2} (h : HasWeakGradientOn B u Du)
    (hu : MemLp u 2 (volume.restrict B))
    (hLoc : ∀ i : Fin 2, MemLp (fun y => Du y i) 2 (volume.restrict B))
    {χ : Vec 2 → ℝ} (hχ : IsSpTest B χ) :
    HasWeakGradientOn B (fun y => χ y * u y)
      (fun y => χ y • Du y + u y • spGrad χ y) := by
  intro i φ hφ hφc hφB
  obtain ⟨hχs, hχc, hχB⟩ := hχ
  have hχcont := hχs.continuous
  have hφcont := hφ.continuous
  have hdχ : Continuous (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχc : HasCompactSupport (fun x => fderiv ℝ χ x (basisVec i)) :=
    (hχc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  -- the test function `χ φ`
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * φ x) := hχs.mul hφ
  have hprodc : HasCompactSupport (fun x => χ x * φ x) := hχc.mul_right
  have hprodB : tsupport (fun x => χ x * φ x) ⊆ B :=
    (tsupport_mul_subset_right).trans hφB
  have hw := h i _ hprod hprodc hprodB
  have hder : ∀ x, fderiv ℝ (fun x => χ x * φ x) x (basisVec i) =
      χ x * fderiv ℝ φ x (basisVec i) + φ x * fderiv ℝ χ x (basisVec i) := by
    intro x
    have h1 : DifferentiableAt ℝ χ x := hχs.differentiable (by simp) x
    have h2 : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
    have h3 : fderiv ℝ (fun x => χ x * φ x) x = χ x • fderiv ℝ φ x + φ x • fderiv ℝ χ x :=
      fderiv_mul h1 h2
    rw [h3]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [hder] at hw
  -- integrabilities
  have i1 : IntegrableOn (fun x => u x * (χ x * fderiv ℝ φ x (basisVec i))) B volume :=
    integrableOn_mul_cpt hu (hχcont.mul hdφ) hχc.mul_right
  have i2 : IntegrableOn (fun x => u x * (φ x * fderiv ℝ χ x (basisVec i))) B volume :=
    integrableOn_mul_cpt hu (hφcont.mul hdχ) hφc.mul_right
  have i3 : IntegrableOn (fun x => Du x i * (χ x * φ x)) B volume :=
    integrableOn_mul_cpt (hLoc i) (hχcont.mul hφcont) hχc.mul_right
  have i4 : IntegrableOn (fun x => u x * (φ x * fderiv ℝ χ x (basisVec i))) B volume := i2
  have e1 : (fun x => u x * (χ x * fderiv ℝ φ x (basisVec i) +
      φ x * fderiv ℝ χ x (basisVec i))) =
      fun x => u x * (χ x * fderiv ℝ φ x (basisVec i)) +
        u x * (φ x * fderiv ℝ χ x (basisVec i)) := by ext x; ring
  rw [e1, integral_add i1 i2] at hw
  have e2 : (fun x => (χ x • Du x + u x • spGrad χ x) i * φ x) =
      fun x => Du x i * (χ x * φ x) + u x * (φ x * fderiv ℝ χ x (basisVec i)) := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, spGrad]
    ring
  have e3 : (fun x => χ x * u x * fderiv ℝ φ x (basisVec i)) =
      fun x => u x * (χ x * fderiv ℝ φ x (basisVec i)) := by ext x; ring
  have e4 : (fun x => Du x i * (χ x * φ x)) = fun x => Du x i * (χ x * φ x) := rfl
  rw [e2, e3, integral_add i3 i4]
  have e5 : (fun x => (fun y => Du y i) x * (χ x * φ x)) = fun x => Du x i * (χ x * φ x) := rfl
  rw [e5] at hw
  linarith

/-- Common a.e.-time-slice package for a bounded measurable drift. -/
theorem ae_slice_drift {d : ℝ × Vec 2 → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), vecNormSq (d p) ≤ kd ^ 2) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      (∀ i : Fin 2, AEStronglyMeasurable (fun y => d (τ, y) i)
        (volume.restrict (euclidBall (0 : Vec 2) 1))) ∧
      ∀ᵐ y ∂(volume.restrict (euclidBall (0 : Vec 2) 1)), vecNormSq (d (τ, y)) ≤ kd ^ 2 := by
  have h0 := ae_slice_aestronglyMeasurable (hdm 0)
  have h1 := ae_slice_aestronglyMeasurable (hdm 1)
  have hb := ae_slice_of_ae hbound
  filter_upwards [h0, h1, hb] with τ m0 m1 mb
  exact ⟨fun i => by fin_cases i <;> assumption, mb⟩

/-- For a.e. time slice, the bounded divergence-free drift annihilates the gradient of every
`H¹` function compactly supported in the unit disc. -/
theorem divFree_integral_grad {d : ℝ × Vec 2 → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), vecNormSq (d p) ≤ kd ^ 2)
    (hdiv : IsDivFreeQ1 d) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      ∀ (ψ : Vec 2 → ℝ) (Dψ : Vec 2 → Vec 2),
        MemLp ψ 2 (volume.restrict (euclidBall 0 1)) →
        (∀ i : Fin 2, MemLp (fun y => Dψ y i) 2 (volume.restrict (euclidBall 0 1))) →
        HasWeakGradientOn (euclidBall 0 1) ψ Dψ →
        (∃ Kc : Set (Vec 2), IsCompact Kc ∧ Kc ⊆ euclidBall 0 1 ∧ ∀ y, y ∉ Kc → ψ y = 0) →
        ∫ y in euclidBall 0 1, vecDot (d (τ, y)) (Dψ y) = 0 := by
  filter_upwards [hdiv, ae_slice_drift hdm hbound] with τ hτ ⟨hm, hb⟩ ψ Dψ hψ hD hw ⟨Kc, hKc, hKB, hz⟩
  exact divFree_slice_grad isOpen_unitBall volume_unitBall_ne_top hm hb hτ hψ hD hw hKc hKB hz

/-- The quadratic version: `∫ ψ d·∇ψ = 0` for the same class. -/
theorem divFree_integral_mul_grad {d : ℝ × Vec 2 → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1)))
    (hbound : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), vecNormSq (d p) ≤ kd ^ 2)
    (hdiv : IsDivFreeQ1 d) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      ∀ (ψ : Vec 2 → ℝ) (Dψ : Vec 2 → Vec 2),
        MemLp ψ 2 (volume.restrict (euclidBall 0 1)) →
        (∀ i : Fin 2, MemLp (fun y => Dψ y i) 2 (volume.restrict (euclidBall 0 1))) →
        HasWeakGradientOn (euclidBall 0 1) ψ Dψ →
        (∃ Kc : Set (Vec 2), IsCompact Kc ∧ Kc ⊆ euclidBall 0 1 ∧ ∀ y, y ∉ Kc → ψ y = 0) →
        ∫ y in euclidBall 0 1, ψ y * vecDot (d (τ, y)) (Dψ y) = 0 := by
  filter_upwards [hdiv, ae_slice_drift hdm hbound] with τ hτ ⟨hm, hb⟩ ψ Dψ hψ hD hw ⟨Kc, hKc, hKB, hz⟩
  exact divFree_slice_mul_grad isOpen_unitBall volume_unitBall_ne_top hm hb hτ hψ hD hw hKc hKB hz

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # Mollified weak equation

For a kernel `K` whose translated support stays inside `(ta,tb) × B`, the mollified functions
`w = mollify (1_S U) K` etc. satisfy pointwise `∂ₜw = div Pw + gw` and `∂ᵢw = Dwᵢ`
(`mollify_time_eq`, `mollify_grad_eq`), `S = (ta,tb) × B`. -/

open AVRegularity.Applications

/-- Window condition for a kernel. -/
def Window (S : Set (ℝ × Vec 2)) (K : ℝ × Vec 2 → ℝ) (I : Set ℝ) (T : Set (Vec 2)) : Prop :=
  ∀ τ ∈ I, ∀ y ∈ T, ∀ q ∈ tsupport K, ((τ, y) - q) ∈ S

theorem hasCompactSupport_kernel_shift {K : ℝ × Vec 2 → ℝ} (hKc : HasCompactSupport K)
    (p : ℝ × Vec 2) : HasCompactSupport (fun q => K (p - q)) :=
  hKc.comp_isClosedEmbedding (Homeomorph.subLeft p).isClosedEmbedding

theorem tsupport_kernel_shift (K : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    tsupport (fun q => K (p - q)) = (fun q => p - q) ⁻¹' tsupport K :=
  tsupport_comp_eq_preimage K (Homeomorph.subLeft p)

theorem isSTTest_kernel {S : Set (ℝ × Vec 2)} {K : ℝ × Vec 2 → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) {p : ℝ × Vec 2}
    (hp : ∀ q ∈ tsupport K, p - q ∈ S) : IsSTTest S (fun q => K (p - q)) := by
  refine ⟨hK.comp (contDiff_const.sub contDiff_id), hasCompactSupport_kernel_shift hKc p, ?_⟩
  rw [tsupport_kernel_shift]
  intro q hq
  simpa using hp (p - q) hq

theorem fderiv_kernel_shift {K : ℝ × Vec 2 → ℝ} (hK : Differentiable ℝ K) (p q v : ℝ × Vec 2) :
    fderiv ℝ (fun x => K (p - x)) q v = - fderiv ℝ K (p - q) v := by
  have h1 : HasFDerivAt K (fderiv ℝ K (p - q)) (p - q) := (hK _).hasFDerivAt
  have h2 : HasFDerivAt (fun x : ℝ × Vec 2 => p - x) (-(ContinuousLinearMap.id ℝ (ℝ × Vec 2))) q :=
    (hasFDerivAt_id q).const_sub p
  have := (h1.comp q h2).fderiv
  change fderiv ℝ (K ∘ fun x : ℝ × Vec 2 => p - x) q v = _
  rw [this]
  simp

theorem stTimeDeriv_kernel {K : ℝ × Vec 2 → ℝ} (hK : Differentiable ℝ K) (p q : ℝ × Vec 2) :
    stTimeDeriv (fun x => K (p - x)) q = - fderiv ℝ K (p - q) (1, 0) :=
  fderiv_kernel_shift hK p q _

theorem stSpaceGrad_kernel {K : ℝ × Vec 2 → ℝ} (hK : Differentiable ℝ K) (p q : ℝ × Vec 2)
    (i : Fin 2) :
    stSpaceGrad (fun x => K (p - x)) q i = - fderiv ℝ K (p - q) (0, basisVec i) :=
  fderiv_kernel_shift hK p q _


/-- The weak formulation `∂ₜU = div P + g` in `(ta,tb) × B`, with slice weak gradient `DU`. -/
structure WeakEq (ta tb : ℝ) (B : Set (Vec 2)) (U g : ℝ × Vec 2 → ℝ)
    (DU P : ℝ × Vec 2 → Vec 2) : Prop where
  hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))
  hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))
  hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
    HasWeakGradientOn B (fun y => U (τ, y)) (fun y => DU (τ, y))
  hP : ∀ i : Fin 2, MemLp (fun p => P p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))
  hg : MemLp g 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))
  hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ B) φ →
    ∫ p in Set.Ioo ta tb ×ˢ B,
      (-(U p * stTimeDeriv φ p) + vecDot (P p) (stSpaceGrad φ p) - g p * φ p) = 0

theorem integrable_mul_shift {S : Set (ℝ × Vec 2)} {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict S)) {k : ℝ × Vec 2 → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (p : ℝ × Vec 2) :
    Integrable (fun q => f q * k (p - q)) (volume.restrict S) := by
  have h1 : MemLp (fun q => k (p - q)) 2 (volume.restrict S) :=
    ((hk.comp (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
      (hasCompactSupport_kernel_shift hkc p)).restrict S
  exact hf.integrable_mul h1

theorem mollify_indicator {S : Set (ℝ × Vec 2)} (hS : MeasurableSet S) (f k : ℝ × Vec 2 → ℝ)
    (p : ℝ × Vec 2) : mollify (S.indicator f) k p = ∫ q in S, f q * k (p - q) := by
  rw [mollify_eq_integral, ← integral_indicator hS]
  congr 1
  funext q
  by_cases hq : q ∈ S <;> simp [hq]


theorem kernel_deriv_props {K : ℝ × Vec 2 → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKc : HasCompactSupport K) (v : ℝ × Vec 2) :
    Continuous (fun z => fderiv ℝ K z v) ∧ HasCompactSupport (fun z => fderiv ℝ K z v) := by
  refine ⟨?_, ?_⟩
  · exact (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
      ((hK.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero)
  · exact (hKc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (ℝ × Vec 2) →L[ℝ] ℝ => L v) (by simp)

theorem mollify_time_eq {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P) {K : ℝ × Vec 2 → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) {p : ℝ × Vec 2}
    (hp : ∀ q ∈ tsupport K, p - q ∈ Set.Ioo ta tb ×ˢ B) :
    mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (fun z => fderiv ℝ K z (1, 0)) p =
      ∑ i : Fin 2, mollify ((Set.Ioo ta tb ×ˢ B).indicator (fun q => P q i))
        (fun z => fderiv ℝ K z (0, basisVec i)) p +
      mollify ((Set.Ioo ta tb ×ˢ B).indicator g) K p := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have hKd : Differentiable ℝ K := hK.differentiable (by simp)
  have hweak := h.hweak _ (isSTTest_kernel hK hKc hp)
  simp only [mollify_indicator hS, Fin.sum_univ_two]
  obtain ⟨c1, s1⟩ := kernel_deriv_props hK hKc ((1 : ℝ), (0 : Vec 2))
  obtain ⟨c20, s20⟩ := kernel_deriv_props hK hKc ((0 : ℝ), basisVec (0 : Fin 2))
  obtain ⟨c21, s21⟩ := kernel_deriv_props hK hKc ((0 : ℝ), basisVec (1 : Fin 2))
  have i1 := integrable_mul_shift h.hU c1 s1 p
  have i20 := integrable_mul_shift (h.hP 0) c20 s20 p
  have i21 := integrable_mul_shift (h.hP 1) c21 s21 p
  have i3 := integrable_mul_shift h.hg hK.continuous hKc p
  have hpt : ∀ q, (-(U q * stTimeDeriv (fun x => K (p - x)) q) +
      vecDot (P q) (stSpaceGrad (fun x => K (p - x)) q) - g q * K (p - q)) =
      U q * fderiv ℝ K (p - q) (1, 0) -
        (P q 0 * fderiv ℝ K (p - q) (0, basisVec 0) + P q 1 * fderiv ℝ K (p - q) (0, basisVec 1)) -
        g q * K (p - q) := by
    intro q
    simp only [stTimeDeriv_kernel hKd, vecDot, Fin.sum_univ_two, stSpaceGrad_kernel hKd]
    ring
  simp only [hpt] at hweak
  have e1 := integral_sub (i1.sub (i20.add i21)) i3
  have e2 := integral_sub i1 (i20.add i21)
  have e3 := integral_add i20 i21
  simp only [Pi.sub_apply, Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3] at hweak
  linarith


theorem isClosedEmbedding_mk_left (σ : ℝ) :
    Topology.IsClosedEmbedding (fun z : Vec 2 => (σ, z)) :=
  Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (g := fun z : Vec 2 => (σ, z))
    (fun _ => rfl) continuous_snd (by fun_prop)

theorem mollify_grad_eq {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B) {U g : ℝ × Vec 2 → ℝ}
    {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P) {K : ℝ × Vec 2 → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) {p : ℝ × Vec 2}
    (hp : ∀ q ∈ tsupport K, p - q ∈ Set.Ioo ta tb ×ˢ B) (i : Fin 2) :
    mollify ((Set.Ioo ta tb ×ˢ B).indicator U) (fun z => fderiv ℝ K z (0, basisVec i)) p =
      mollify ((Set.Ioo ta tb ×ˢ B).indicator (fun q => DU q i)) K p := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have hKd : Differentiable ℝ K := hK.differentiable (by simp)
  simp only [mollify_indicator hS]
  obtain ⟨c2, s2⟩ := kernel_deriv_props hK hKc ((0 : ℝ), basisVec i)
  have i1 := integrable_mul_shift h.hU c2 s2 p
  have i2 := integrable_mul_shift (h.hDU i) hK.continuous hKc p
  rw [Measure.volume_eq_prod] at i1 i2
  rw [Measure.volume_eq_prod, setIntegral_prod _ i1, setIntegral_prod _ i2]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 h.hgrad] with σ hσ hσI
  have hσ := hσ hσI
  set φ : ℝ × Vec 2 → ℝ := fun q => K (p - q) with hφ
  have hφT := isSTTest_kernel hK hKc hp
  have hψ : IsSpTest B (fun z : Vec 2 => φ (σ, z)) := by
    refine ⟨hφT.1.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
    · exact hφT.2.1.comp_isClosedEmbedding (isClosedEmbedding_mk_left σ)
    · intro z hz
      have := tsupport_comp_subset_preimage φ (f := fun z : Vec 2 => (σ, z)) (by fun_prop) hz
      exact (hφT.2.2 this).2
  have hw := hσ i (fun z => φ (σ, z)) hψ.1 hψ.2.1 hψ.2.2
  have hφd : Differentiable ℝ φ := hφT.1.differentiable (by simp)
  have hder : ∀ x, fderiv ℝ (fun z : Vec 2 => φ (σ, z)) x (basisVec i) =
      - fderiv ℝ K (p - (σ, x)) (0, basisVec i) := by
    intro x
    rw [AVRegularity.Applications.LocalEnergy.fderiv_slice hφd σ x (basisVec i), hφ]
    exact fderiv_kernel_shift hKd p (σ, x) _
  simp only [hder, mul_neg, integral_neg] at hw
  simpa [hφ] using neg_inj.1 hw

end AVRegularity.Applications.LocalEnergy
end
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Set Filter Topology
namespace AVRegularity.Applications

/-! # `L²` bookkeeping for the Caccioppoli inequality

Generic lemmas: `L²` of vector fields with bounded multipliers, and integrability of dot
products. -/

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

theorem integrable_vecDot_of_memLp {F G : α → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 μ) (hG : ∀ i : Fin 2, MemLp (fun x => G x i) 2 μ) :
    Integrable (fun x => vecDot (F x) (G x)) μ := by
  simp only [vecDot, Fin.sum_univ_two]
  exact ((hF 0).integrable_mul (hG 0)).add ((hF 1).integrable_mul (hG 1))

theorem memLp_cut_mul {pos : α → Vec 2} (hpos : Measurable pos) {f : α → ℝ}
    (hf : MemLp f 2 μ) : MemLp (fun x => caccCut (pos x) * f x) 2 μ := by
  refine memLp_two_of_sq_le (c := 1) zero_le_one ?_ hf (Eventually.of_forall fun x => ?_)
  · exact ((caccCut_contDiff.continuous.measurable.comp hpos).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · have h0 := caccCut_nonneg (pos x)
    have h1 := caccCut_le_one (pos x)
    rw [mul_pow, one_mul]
    have : caccCut (pos x) ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (sq_nonneg _) this

theorem memLp_cut_sq_mul {pos : α → Vec 2} (hpos : Measurable pos) {f : α → ℝ}
    (hf : MemLp f 2 μ) : MemLp (fun x => caccCut (pos x) ^ 2 * f x) 2 μ := by
  have := memLp_cut_mul hpos (memLp_cut_mul hpos hf)
  refine this.ae_eq (Eventually.of_forall fun x => ?_)
  simp only [pow_two, mul_assoc]

theorem memLp_grad_mul {pos : α → Vec 2} (hpos : Measurable pos) {f : α → ℝ}
    (hf : MemLp f 2 μ) (i : Fin 2) : MemLp (fun x => spGrad caccCut (pos x) i * f x) 2 μ := by
  obtain ⟨L, hL0, hL⟩ := exists_caccCut_grad_bound
  refine memLp_two_of_sq_le (c := L ^ 2) (sq_nonneg L) ?_ hf (Eventually.of_forall fun x => ?_)
  · exact (((spGrad_caccCut_continuous i).measurable.comp hpos).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · have h1 : spGrad caccCut (pos x) i ^ 2 ≤ L ^ 2 := by
      refine le_trans ?_ (hL (pos x))
      simp only [vecNormSq, vecDot, Fin.sum_univ_two]
      fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (spGrad caccCut (pos x) 0),
        mul_self_nonneg (spGrad caccCut (pos x) 1)]
    rw [mul_pow]
    nlinarith [sq_nonneg (f x)]

theorem vec_apply_sq_le (v : Vec 2) (i : Fin 2) : v i ^ 2 ≤ vecNormSq v := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

theorem vecNormSq_le_abs_sq (v : Vec 2) : vecNormSq v ≤ (|v 0| + |v 1|) ^ 2 := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_mul_abs_self (v 0), abs_mul_abs_self (v 1)]

/-- Components of a bounded matrix applied to an `L²` field are `L²`. -/
theorem memLp_mulVec {K : α → Matrix (Fin 2) (Fin 2) ℝ} {F : α → Vec 2} {kK : ℝ}
    (hKm : ∀ i j : Fin 2, AEStronglyMeasurable (fun x => K x i j) μ)
    (hbd : ∀ᵐ x ∂μ, ∀ e : Vec 2, vecNormSq ((K x).mulVec e) ≤ kK ^ 2 * vecNormSq e)
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 μ) (i : Fin 2) :
    MemLp (fun x => ((K x).mulVec (F x)) i) 2 μ := by
  have hg : MemLp (fun x => |F x 0| + |F x 1|) 2 μ := (hF 0).abs.add (hF 1).abs
  refine memLp_two_of_sq_le (c := kK ^ 2) (sq_nonneg kK) ?_ hg ?_
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hKm i 0).mul (hF 0).aestronglyMeasurable).add
      ((hKm i 1).mul (hF 1).aestronglyMeasurable)
  · filter_upwards [hbd] with x hx
    exact (vec_apply_sq_le _ i).trans ((hx (F x)).trans
      (mul_le_mul_of_nonneg_left (vecNormSq_le_abs_sq (F x)) (sq_nonneg kK)))

/-- A bounded vector field times an `L²` function. -/
theorem memLp_bdd_mul {d : α → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun x => d x i) μ)
    (hbd : ∀ᵐ x ∂μ, vecNormSq (d x) ≤ kd ^ 2) {f : α → ℝ} (hf : MemLp f 2 μ) (i : Fin 2) :
    MemLp (fun x => f x * d x i) 2 μ := by
  refine memLp_two_of_sq_le (c := kd ^ 2) (sq_nonneg kd) (hf.aestronglyMeasurable.mul (hdm i)) hf
    ?_
  filter_upwards [hbd] with x hx
  have := (vec_apply_sq_le (d x) i).trans hx
  rw [mul_pow]
  nlinarith [sq_nonneg (f x)]

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology Convolution
namespace AVRegularity.Applications.LocalEnergy

/-! # Energy identity for the mollified functions

`mollified_energy_identity`: for a smooth compactly supported kernel `K` whose translated support
stays inside `(ta,tb) × B` (a `Window`), the mollified zero-extension `w = mollify (1_S U) K`
satisfies the energy identity with the mollified data `Pw, Dw, gw`. -/

open AVRegularity.Applications

/-- Vector-valued mollification of the zero-extension. -/
def molVec (S : Set (ℝ × Vec 2)) (P : ℝ × Vec 2 → Vec 2) (K : ℝ × Vec 2 → ℝ) :
    ℝ × Vec 2 → Vec 2 := fun p i => mollify (S.indicator (fun q => P q i)) K p

theorem locallyIntegrable_indicator {S : Set (ℝ × Vec 2)} (hS : MeasurableSet S)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict S)) :
    LocallyIntegrable (S.indicator f) volume := by
  have : MemLp (S.indicator f) 2 volume := (memLp_indicator_iff_restrict hS).2 hf
  exact this.locallyIntegrable (by norm_num)

theorem mollified_energy_identity {ta tb : ℝ} {B : Set (Vec 2)} (hB : IsOpen B)
    {U g : ℝ × Vec 2 → ℝ} {DU P : ℝ × Vec 2 → Vec 2} (h : WeakEq ta tb B U g DU P)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest B ζ) {K : ℝ × Vec 2 → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) {I : Set ℝ} (hI : I.OrdConnected)
    (hwin : Window (Set.Ioo ta tb ×ˢ B) K I (tsupport ζ)) {τ₁ τ₂ : ℝ} (h1 : τ₁ ∈ I)
    (h2 : τ₂ ∈ I) (h12 : τ₁ ≤ τ₂) :
    (∫ y in B, ζ y ^ 2 * (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K (τ₂, y)) ^ 2) -
      (∫ y in B, ζ y ^ 2 * (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K (τ₁, y)) ^ 2) =
    -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, fluxIntegrand ζ
      (mollify ((Set.Ioo ta tb ×ˢ B).indicator U) K)
      (molVec (Set.Ioo ta tb ×ˢ B) P K) (molVec (Set.Ioo ta tb ×ˢ B) DU K)
      (mollify ((Set.Ioo ta tb ×ˢ B).indicator g) K) p := by
  have hS : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB.measurableSet
  have hc1 : ∀ {f : ℝ × Vec 2 → ℝ}, MemLp f 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)) →
      ContDiff ℝ 1 (mollify ((Set.Ioo ta tb ×ˢ B).indicator f) K) := fun hf =>
    (mollify_contDiff hK hKc (locallyIntegrable_indicator hS hf)).of_le (by exact_mod_cast le_top)
  refine classical_energy_identity (hζ.1.of_le (by exact_mod_cast le_top)) hζ.2.1 hB.measurableSet
    hζ.2.2 (hc1 h.hU) (fun i => hc1 (h.hP i)) ?_ ?_ hI ?_ ?_ h1 h2 h12
  · intro i
    exact (mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS (h.hDU i)))
  · exact (mollify_continuous hK.continuous hKc (locallyIntegrable_indicator hS h.hg))
  · intro τ hτ y hy
    have hp := hwin τ hτ y hy
    have hK1 : ContDiff ℝ 1 K := hK.of_le (by exact_mod_cast le_top)
    rw [fderiv_mollify_apply hK1 hKc (locallyIntegrable_indicator hS h.hU)]
    rw [mollify_time_eq hB h hK hKc hp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_mollify_apply hK1 hKc (locallyIntegrable_indicator hS (h.hP i))]
  · intro τ hτ y hy i
    have hp := hwin τ hτ y hy
    have hK1 : ContDiff ℝ 1 K := hK.of_le (by exact_mod_cast le_top)
    rw [fderiv_mollify_apply hK1 hKc (locallyIntegrable_indicator hS h.hU)]
    exact mollify_grad_eq hB h hK hKc hp i

end AVRegularity.Applications.LocalEnergy
end
end
end
