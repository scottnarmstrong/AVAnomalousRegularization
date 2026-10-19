-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Tubes.Weak
public import AVenhance.Statements.Roots.SpaceGrad
import Homogenization.Ambient.BlockMatrix
import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # The rescaled solution lies in the energy class

For a local weak solution `w` in `O ⊇ closedTube`, the rescaled `U = w ∘ Θ`, `∇U = r (∇w) ∘ Θ`
belongs to `L^∞(-1,0;L²(B₁)) ∩ L²(-1,0;H¹(B₁))` with the bound
`∫_{B₁} U(τ)² ≤ r⁻² A²` coming from the `L^∞L²` bound of `w`.
-/

section Energy

variable {b : ℝ → Vec 2 → Vec 2} {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
  {Y : ℝ → Vec 2} {t r κ : ℝ} {O : Set (ℝ × Vec 2)}

theorem memLp_comp_tubeMap {c : ℝ} (hY : Measurable Y) (hc : 0 < c) (hr : r ≠ 0)
    {S : Set (ℝ × Vec 2)} {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (tubeMap Y t c r '' S))) :
    MemLp (fun p => f (tubeMap Y t c r p)) 2 (volume.restrict S) := by
  have hemb := measurableEmbedding_tubeMap (t := t) hY hc.ne' hr
  have h2 : MemLp f 2 (Measure.map (tubeMap Y t c r) (volume.restrict S)) := by
    rw [map_tubeMap_restrict hY hc hr]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (hemb.memLp_map_measure_iff).1 h2

theorem memLp_tube_of_local (hY : Continuous Y) (hκ : 0 < κ) (hr : 0 < r)
    (hsub : closedTube Y t r κ ⊆ O) {f : ℝ × Vec 2 → ℝ}
    (hf : ∀ Kc : Set (ℝ × Vec 2), Kc ⊆ O → IsCompact Kc → MemLp f 2 (volume.restrict Kc)) :
    MemLp (fun p => f (tubeMap Y t (r ^ 2 / κ) r p)) 2 (volume.restrict (openCyl 0 1)) := by
  have hc : 0 < r ^ 2 / κ := by positivity
  refine memLp_comp_tubeMap hY.measurable hc hr.ne' ?_
  exact (hf _ hsub (isCompact_closedTube hY t r κ)).mono_measure
    (Measure.restrict_mono (tubeMap_image_subset_closedTube hr hκ) le_rfl)

theorem timeSection_measurable (hO : IsOpen O) (s : ℝ) : MeasurableSet (timeSection O s) :=
  (hO.preimage (continuous_const.prodMk continuous_id)).measurableSet

theorem euclidBall_subset_timeSection (hsub : closedTube Y t r κ ⊆ O)
    {s : ℝ} (hs : s ∈ Icc (t - r ^ 2 / κ) t) : euclidBall (Y s) r ⊆ timeSection O s := by
  intro x hx
  apply hsub
  exact ⟨hs, le_of_lt hx⟩

/-- Weak gradients of the slices of the rescaled solution. -/
theorem tube_slice_weakGradient (hκ : 0 < κ) (hr : 0 < r) (hO : IsOpen O)
    (hsub : closedTube Y t r κ ⊆ O)
    (hgrad : ∀ᵐ s ∂(volume : Measure ℝ),
      HasWeakGradientOn (timeSection O s) (fun x => w (s, x)) (fun x => Dw (s, x))) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      HasWeakGradientOn (euclidBall 0 1) (fun y => tubeU w Y t (r ^ 2 / κ) r (τ, y))
        (fun y => tubeDU Dw Y t (r ^ 2 / κ) r (τ, y)) := by
  have hc : 0 < r ^ 2 / κ := by positivity
  have h1 : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      HasWeakGradientOn (timeSection O (t + r ^ 2 / κ * τ)) (fun x => w (t + r ^ 2 / κ * τ, x))
        (fun x => Dw (t + r ^ 2 / κ * τ, x)) := by
    exact ae_restrict_timeDil t hc (S := Ioo (-1 : ℝ) 0)
      (P := fun s => HasWeakGradientOn (timeSection O s) (fun x => w (s, x))
        (fun x => Dw (s, x))) (ae_restrict_of_ae hgrad)
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with τ hτ hτmem
  have hs : t + r ^ 2 / κ * τ ∈ Icc (t - r ^ 2 / κ) t := by
    obtain ⟨h1, h2⟩ := hτmem
    constructor <;> nlinarith
  have hball : HasWeakGradientOn (euclidBall (Y (t + r ^ 2 / κ * τ)) (r * 1))
      (fun x => w (t + r ^ 2 / κ * τ, x)) (fun x => Dw (t + r ^ 2 / κ * τ, x)) := by
    rw [mul_one]
    exact HasWeakGradientOn.mono_set (euclidBall_subset_timeSection hsub hs)
      (timeSection_measurable hO _) hτ
  exact HasWeakGradientOn.comp_spDil hr hball

/-- The `L^∞L²` bound for the rescaled solution, from a mass bound on all discs of radius `r`
contained in the time sections. -/
theorem tube_slice_bound (hκ : 0 < κ) (hr : 0 < r) (hsub : closedTube Y t r κ ⊆ O) {A : ℝ}
    (hA : ∀ᵐ s ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O s →
      ∫ x in euclidBall y r, w (s, x) ^ 2 ≤ A ^ 2) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∫ y in euclidBall 0 1, tubeU w Y t (r ^ 2 / κ) r (τ, y) ^ 2 ≤ (r ^ 2)⁻¹ * A ^ 2 := by
  have hc : 0 < r ^ 2 / κ := by positivity
  have hA' : ∀ᵐ s ∂(volume.restrict ((fun τ : ℝ => t + r ^ 2 / κ * τ) '' Ioo (-1 : ℝ) 0)),
      ∀ y : Vec 2, euclidBall y r ⊆ timeSection O s →
        ∫ x in euclidBall y r, w (s, x) ^ 2 ≤ A ^ 2 := ae_restrict_of_ae hA
  have h1 := ae_restrict_timeDil t hc (S := Ioo (-1 : ℝ) 0) hA'
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with τ hτ hτmem
  have hs : t + r ^ 2 / κ * τ ∈ Icc (t - r ^ 2 / κ) t := by
    obtain ⟨h1, h2⟩ := hτmem
    constructor <;> nlinarith
  have hsubO := euclidBall_subset_timeSection hsub hs
  have hle := hτ (Y (t + r ^ 2 / κ * τ)) hsubO
  have hcv : ∫ y in euclidBall 0 1, tubeU w Y t (r ^ 2 / κ) r (τ, y) ^ 2 =
      (r ^ 2)⁻¹ * ∫ x in euclidBall (Y (t + r ^ 2 / κ * τ)) r,
        w (t + r ^ 2 / κ * τ, x) ^ 2 := by
    have h := integral_spDil (Y (t + r ^ 2 / κ * τ)) hr.ne'
      (fun x => w (t + r ^ 2 / κ * τ, x) ^ 2) (euclidBall 0 1)
    rw [image_spDil_euclidBall _ hr, mul_one] at h
    exact h
  rw [hcv]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (sq_nonneg r))

/-- The rescaled solution lies in the energy class on `Q₁`. -/
theorem tube_energyClass (hY : Continuous Y) (hκ : 0 < κ) (hr : 0 < r) (hO : IsOpen O)
    (hsub : closedTube Y t r κ ⊆ O) (hw : IsLocalWeakSolution b κ O w Dw) {A : ℝ}
    (hA : ∀ᵐ s ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O s →
      ∫ x in euclidBall y r, w (s, x) ^ 2 ≤ A ^ 2) :
    IsEnergyClassQ1 (tubeU w Y t (r ^ 2 / κ) r) (tubeDU Dw Y t (r ^ 2 / κ) r) := by
  refine ⟨memLp_tube_of_local hY hκ hr hsub hw.1, fun i => ?_,
    tube_slice_weakGradient hκ hr hO hsub hw.2.2.1, (r ^ 2)⁻¹ * A ^ 2,
    tube_slice_bound hκ hr hsub hA⟩
  have := (memLp_tube_of_local hY hκ hr hsub (hw.2.1 · · · i)).const_mul r
  simpa [tubeDU, Pi.smul_apply, smul_eq_mul] using this

end Energy

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set Filter Topology
namespace AVRegularity.Applications

/-! # Filters and change of variables for the trace statement -/

/-- Reverse transfer of a.e. statements along the time dilation `τ ↦ t + c τ`. -/
theorem ae_restrict_timeDil_inv (t : ℝ) {c : ℝ} (hc : 0 < c) {S : Set ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ τ ∂(volume.restrict S), P τ) :
    ∀ᵐ σ ∂(volume.restrict ((fun τ : ℝ => t + c * τ) '' S)), P ((σ - t) / c) := by
  have hemb : MeasurableEmbedding (fun τ : ℝ => t + c * τ) :=
    (timeDilEquiv t hc.ne').measurableEmbedding
  have h1 : ∀ᵐ σ ∂(ENNReal.ofReal c⁻¹ •
      volume.restrict ((fun τ : ℝ => t + c * τ) '' S)), P ((σ - t) / c) := by
    rw [← map_timeDil_restrict t hc S, hemb.ae_map_iff]
    filter_upwards [h] with τ hτ
    have : (t + c * τ - t) / c = τ := by field_simp; ring
    rw [this]; exact hτ
  rw [ae_iff] at h1 ⊢
  rw [Measure.smul_apply, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (by simp [hc])

theorem tendsto_timeNormalize (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ => (σ - t) / c) (𝓝[<] t ⊓ ae (volume : Measure ℝ))
      (𝓝[<] 0 ⊓ ae (volume : Measure ℝ)) := by
  refine Tendsto.inf ?_ ?_
  · refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun σ : ℝ => (σ - t) / c) (𝓝 t) (𝓝 ((t - t) / c)) :=
        ((continuous_id.sub continuous_const).div_const c).tendsto t
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_neg_of_neg_of_pos (sub_neg.2 hσ) hc
  · have hqmp : Measure.QuasiMeasurePreserving (fun σ : ℝ => (σ - t) / c) volume volume := by
      have hform : (fun σ : ℝ => (σ - t) / c) = fun σ => (-t / c) + c⁻¹ * σ := by
        funext σ; field_simp; ring
      refine ⟨by fun_prop, ?_⟩
      rw [hform, map_time_affine_volume _ _ (inv_ne_zero hc.ne')]
      exact Measure.smul_absolutelyContinuous
    exact hqmp.tendsto_ae

theorem neBot_nhdsLT_inf_ae (t : ℝ) : (𝓝[<] t ⊓ ae (volume : Measure ℝ)).NeBot := by
  rw [inf_neBot_iff]
  intro s hs u hu
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hs
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have h1 : Ioo ε t ⊆ uᶜ := by
    intro x hx hxu
    have : x ∈ s ∩ u := ⟨hsub hx, hxu⟩
    rw [hne] at this; exact this
  have h2 : volume (Ioo ε t) = 0 := measure_mono_null h1 (mem_ae_iff.1 hu)
  rw [Real.volume_Ioo] at h2
  have := hε
  simp at h2
  linarith [h2, hε.out]

theorem norm_sub_le_of_hasDerivAt {Y Yd : ℝ → Vec 2} (hYd : ∀ s, HasDerivAt Y (Yd s) s) {B : ℝ}
    (hB : ∀ s, ‖Yd s‖ ≤ B) (s u : ℝ) : ‖Y s - Y u‖ ≤ B * |s - u| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Y) (f' := Yd) (s := univ)
    (fun x _ => (hYd x).hasDerivWithinAt) (fun x _ => hB x) convex_univ (mem_univ u) (mem_univ s)
  simpa [Real.norm_eq_abs] using this

theorem integrableOn_spDil_image {c : Vec 2} {r : ℝ} (hr : r ≠ 0) {S : Set (Vec 2)}
    {g : Vec 2 → ℝ} :
    IntegrableOn g (spDil c r '' S) ↔ IntegrableOn (fun y => g (spDil c r y)) S := by
  have hemb : MeasurableEmbedding (spDil c r) := (spDilEquiv c hr).measurableEmbedding
  unfold IntegrableOn
  rw [show (fun y => g (spDil c r y)) = g ∘ spDil c r from rfl,
    ← hemb.integrable_map_iff, map_spDil_restrict c hr S]
  exact (integrable_smul_measure (by simp [hr]) ENNReal.ofReal_ne_top).symm

/-- Fubini: slices of an `L²(Q₁)` function are measurable and square integrable for a.e. time. -/
theorem ae_slice_memLp {U : ℝ × Vec 2 → ℝ} (hU : MemLp U 2 (volume.restrict (openCyl 0 1))) :
    ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      AEStronglyMeasurable (fun y => U (τ, y)) (volume.restrict (euclidBall 0 1)) ∧
        IntegrableOn (fun y => U (τ, y) ^ 2) (euclidBall 0 1) := by
  have h1 := ae_slice_integrable_sq hU
  have h2 := hU.aestronglyMeasurable
  rw [volume_restrict_openCyl_eq_prod] at h2
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, one_pow] at h2
  filter_upwards [h1, h2.prodMk_left] with τ hτ1 hτ2
  exact ⟨hτ2, hτ1⟩

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # Cylinder averages of the rescaled solution

`∫_{Q₁} U² ≤ M` from the slice bound, and the comparison of the averages over the closed-top
cylinder `cylinder 0 1` and the open cylinder `openCyl 0 1` (they differ by a null set), together
with the Cauchy--Schwarz bound for the mean. -/

theorem integral_openCyl_sq_le {U : ℝ × Vec 2 → ℝ} (hU : MemLp U 2 (volume.restrict (openCyl 0 1)))
    {M : ℝ}
    (hslice : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∫ y in euclidBall 0 1, U (τ, y) ^ 2 ≤ M) :
    ∫ p in openCyl 0 1, U p ^ 2 ≤ M := by
  have hint : Integrable (fun p => U p ^ 2) (volume.restrict (openCyl 0 1)) := hU.integrable_sq
  rw [volume_restrict_openCyl_eq_prod] at hint ⊢
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, one_pow] at hint ⊢
  rw [integral_prod _ hint]
  have hfin : IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 0)) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  calc ∫ τ, ∫ y, U (τ, y) ^ 2 ∂(volume.restrict (euclidBall 0 1)) ∂(volume.restrict (Ioo (-1 : ℝ) 0))
      ≤ ∫ _τ, M ∂(volume.restrict (Ioo (-1 : ℝ) 0)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ =>
          integral_nonneg fun y => sq_nonneg _) (integrable_const M) hslice
    _ = M := by simp

theorem restrict_cylinder_eq_openCyl :
    (volume : Measure (ℝ × Vec 2)).restrict (AVRegularity.External.Campanato.cylinder 0 1) =
      volume.restrict (openCyl 0 1) := by
  unfold AVRegularity.External.Campanato.cylinder openCyl
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]

theorem cylinderMean_abs_le {U : ℝ × Vec 2 → ℝ} (hU : MemLp U 2 (volume.restrict (openCyl 0 1))) :
    |cylinderMean U 0 1| ≤ Real.sqrt (⨍ p in openCyl 0 1, U p ^ 2) := by
  have h := setAverage_abs_le_sqrt_setAverage_sq (μ := (volume : Measure (ℝ × Vec 2)))
    (s := AVRegularity.External.Campanato.cylinder 0 1) (cylinder_measure_ne_zero 0 one_pos) (cylinder_measure_ne_top 0 one_pos)
    U (by rw [restrict_cylinder_eq_openCyl]; exact hU)
  unfold cylinderMean
  convert h using 3
  rw [restrict_cylinder_eq_openCyl]

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # The relative drift is divergence free and small

In the proof of Lemma 8.1 of the paper, the drift
`d = (r/κ)(b(t', Y(t') + r y) - Ẏ(t'))` is divergence free on `B₁` and satisfies
`‖d‖ ≤ [b] r^{1+α}/κ` (sup norm; `vecNormSq d ≤ 2‖d‖²`). -/

theorem integrable_vecDot_spGrad {g : Vec 2 → Vec 2} (hg : Continuous g) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun y => vecDot (g y) (spGrad ψ y)) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hterm : ∀ i : Fin 2, Integrable (fun y => g y i * fderiv ℝ ψ y (basisVec i)) := by
    intro i
    have hc : Continuous fun y => fderiv ℝ ψ y (basisVec i) :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs' : HasCompactSupport fun y => fderiv ℝ ψ y (basisVec i) :=
      hasCompactSupport_fderiv_apply hcs _
    exact ((continuous_apply i).comp hg |>.mul hc).integrable_of_hasCompactSupport
      (hcs'.mul_left)
  simp only [vecDot, spGrad, Fin.sum_univ_two]
  exact (hterm 0).add (hterm 1)

theorem integral_const_vecDot_spGrad (v : Vec 2) {ψ : Vec 2 → ℝ} (hψ : IsSpTest (euclidBall 0 1) ψ) :
    ∫ y in euclidBall 0 1, vecDot v (spGrad ψ y) = 0 := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  rw [setIntegral_eq_integral_of_tsupport (g := ψ) hψ.2.2 fun y hy => by
    simp [vecDot, spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]]
  have hterm : ∀ i : Fin 2, Integrable (fun y => v i * fderiv ℝ ψ y (basisVec i)) := by
    intro i
    have hc : Continuous fun y => fderiv ℝ ψ y (basisVec i) :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (continuous_const.mul hc).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hψ.2.1 _).mul_left)
  simp only [vecDot, spGrad, Fin.sum_univ_two]
  rw [integral_add (hterm 0) (hterm 1), integral_const_mul, integral_const_mul,
    integral_fderiv_eq_zero_of_hasCompactSupport hψ.1 hψ.2.1,
    integral_fderiv_eq_zero_of_hasCompactSupport hψ.1 hψ.2.1]
  ring

/-- Divergence-free transfer along an affine change of variables on a single time slice. -/
theorem integral_drift_slice {b : ℝ → Vec 2 → Vec 2}
    (hb : ∀ s : ℝ, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b s x) (AVenhance.spaceGrad φ x) = 0) (s : ℝ) (c : Vec 2) {r : ℝ} (hr : 0 < r)
    {ψ : Vec 2 → ℝ} (hψ : IsSpTest (euclidBall 0 1) ψ) :
    ∫ y in euclidBall 0 1, vecDot (b s (c + r • y)) (spGrad ψ y) = 0 := by
  have htest : IsSpTest (euclidBall c (r * 1)) (pushSp c r ψ) := isSpTest_pushSp c hr hψ
  have h0 := hb s (pushSp c r ψ) htest.1 htest.2.1
  have hvan : ∀ x, x ∉ tsupport (pushSp c r ψ) →
      vecDot (b s x) (spGrad (pushSp c r ψ) x) = 0 := by
    intro x hx
    simp [vecDot, spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
  have h1 : ∫ x in euclidBall c (r * 1), vecDot (b s x) (spGrad (pushSp c r ψ) x) = 0 := by
    rw [setIntegral_eq_integral_of_tsupport (g := pushSp c r ψ) htest.2.2 hvan]
    exact h0
  rw [mul_one] at h1
  have h2 := integral_spDil c hr.ne' (fun x => vecDot (b s x) (spGrad (pushSp c r ψ) x))
    (euclidBall 0 1)
  rw [image_spDil_euclidBall c hr, mul_one, h1, mul_zero] at h2
  have h3 : ∫ y in euclidBall 0 1, vecDot (b s (spDil c r y)) (spGrad (pushSp c r ψ) (spDil c r y))
      = r⁻¹ * ∫ y in euclidBall 0 1, vecDot (b s (c + r • y)) (spGrad ψ y) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable 0 1) fun y _ => ?_
    rw [spGrad_pushSp c hr.ne' hψ.1, vecDot_smul_right]
    rfl
  rw [h3] at h2
  exact (mul_eq_zero.1 h2).resolve_left (inv_ne_zero hr.ne')

theorem vecDot_sub_left' (x y z : Vec 2) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

/-- The relative drift is divergence free. -/
theorem tube_divFree {b : ℝ → Vec 2 → Vec 2}
    (hb : ∀ s : ℝ, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b s x) (AVenhance.spaceGrad φ x) = 0)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2) {Y Yd : ℝ → Vec 2}
    {t r κ : ℝ} (hr : 0 < r) :
    IsDivFreeQ1 (tubeDrift b Y Yd t (r ^ 2 / κ) r κ) := by
  refine Filter.Eventually.of_forall fun τ ψ hψ => ?_
  set s := t + r ^ 2 / κ * τ with hs
  have hbs : Continuous (b s) := hbc.comp (continuous_const.prodMk continuous_id)
  have hA : Integrable (fun y => vecDot (b s (Y s + r • y)) (spGrad ψ y)) :=
    integrable_vecDot_spGrad (g := fun y => b s (Y s + r • y))
      (hbs.comp (continuous_const.add (continuous_id.const_smul r))) hψ.1 hψ.2.1
  have hB : Integrable (fun y => vecDot (Yd s) (spGrad ψ y)) :=
    integrable_vecDot_spGrad (g := fun _ => Yd s) continuous_const hψ.1 hψ.2.1
  have : ∀ y, vecDot (tubeDrift b Y Yd t (r ^ 2 / κ) r κ (τ, y)) (spGrad ψ y) =
      (r / κ) * (vecDot (b s (Y s + r • y)) (spGrad ψ y) - vecDot (Yd s) (spGrad ψ y)) := by
    intro y
    simp only [tubeDrift]
    rw [vecDot_smul_left, vecDot_sub_left']
  simp only [this]
  rw [integral_const_mul, integral_sub hA.integrableOn hB.integrableOn,
    integral_drift_slice hb s (Y s) hr hψ, integral_const_vecDot_spGrad _ hψ]
  ring

theorem vecNormSq_le_two_norm_sq (v : Vec 2) : vecNormSq v ≤ 2 * ‖v‖ ^ 2 := by
  have h0 := sq_apply_le_vecNormSq v 0
  have h1 := sq_apply_le_vecNormSq v 1
  have e : vecNormSq v = v 0 ^ 2 + v 1 ^ 2 := by simp [vecNormSq, vecDot, pow_two, Fin.sum_univ_two]
  have a0 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v 0) 2
  have a1 : v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs (v 1)]
    exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v 1) 2
  rw [e]
  linarith

/-- The relative drift on `Q₁` has size at most `√2 |C| r^{1+α} / κ` (the drift bound in the
proof of Lemma 8.1 of the paper).
-/
theorem tube_drift_bound {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2} {C : ℝ}
    (hC : ∀ t u : ℝ, ∀ x y : Vec 2,
      ‖b t x - b u y‖ ≤ C * (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α)
    {Y Yd : ℝ → Vec 2} {t r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hYd : ∀ s, s ≤ t → Yd s = b s (Y s)) {p : ℝ × Vec 2} (hp : p ∈ openCyl 0 1) :
    vecNormSq (tubeDrift b Y Yd t (r ^ 2 / κ) r κ p) ≤
      (Real.sqrt 2 * |C| * r ^ (1 + α) / κ) ^ 2 := by
  rw [mem_openCyl_zero_one_iff] at hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  have hc : 0 < r ^ 2 / κ := by positivity
  have hsle : t + r ^ 2 / κ * p.1 ≤ t := by nlinarith
  have hnorm : ‖tubeDrift b Y Yd t (r ^ 2 / κ) r κ p‖ ≤ |C| * r ^ (1 + α) / κ := by
    unfold tubeDrift
    rw [norm_smul, hYd _ hsle, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / κ)]
    have h1 := hC (t + r ^ 2 / κ * p.1) (t + r ^ 2 / κ * p.1) (Y (t + r ^ 2 / κ * p.1) + r • p.2)
      (Y (t + r ^ 2 / κ * p.1))
    simp only [sub_self, abs_zero, zero_add, add_sub_cancel_left, vecNormSq_smul] at h1
    have hsq : Real.sqrt (r ^ 2 * vecNormSq p.2) ≤ r := by
      rw [Real.sqrt_le_left hr.le]
      have := vecNormSq_nonneg p.2
      nlinarith
    have h2 : (Real.sqrt (r ^ 2 * vecNormSq p.2)) ^ α ≤ r ^ α :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) hsq hα.le
    have h3 : ‖b (t + r ^ 2 / κ * p.1) (Y (t + r ^ 2 / κ * p.1) + r • p.2) -
        b (t + r ^ 2 / κ * p.1) (Y (t + r ^ 2 / κ * p.1))‖ ≤ |C| * r ^ α :=
      h1.trans (mul_le_mul (le_abs_self C) h2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        (abs_nonneg _))
    calc r / κ * ‖_‖ ≤ r / κ * (|C| * r ^ α) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = |C| * r ^ (1 + α) / κ := by
        rw [Real.rpow_add hr, Real.rpow_one]; ring
  calc vecNormSq _ ≤ 2 * ‖tubeDrift b Y Yd t (r ^ 2 / κ) r κ p‖ ^ 2 :=
        vecNormSq_le_two_norm_sq _
    _ ≤ 2 * (|C| * r ^ (1 + α) / κ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by norm_num)
    _ = (Real.sqrt 2 * |C| * r ^ (1 + α) / κ) ^ 2 := by
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        field_simp
        rw [h2]; ring

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set Filter Topology AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # Reading the trace back from the rescaled tube

Geometry in rescaled coordinates for the proof that the continuous representative `Ut` of the
rescaled solution represents the moving-frame top trace of `w` on the fixed disc `B_{r/4}(x)`.
-/

/-- The spatial profile `y ↦ Ut(0, (y - x)/r)` read from the top of the tube. -/
def tubeProfile (Ut : ℝ × Vec 2 → ℝ) (x : Vec 2) (r : ℝ) (y : Vec 2) : ℝ :=
  Ut (0, spDilInv x r y)

theorem volume_euclidBall_lt_top (c : Vec 2) (ρ : ℝ) : volume (euclidBall c ρ) < ⊤ := by
  have hsub : euclidBall c ρ ⊆ Metric.closedBall c |ρ| := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine norm_le_of_vecNormSq_le (abs_nonneg ρ) ?_
    rw [sq_abs]
    exact le_of_lt hy
  exact lt_of_le_of_lt (measure_mono hsub) measure_closedBall_lt_top

theorem zero_mem_cylinder_of {u : Vec 2} (hu : u ∈ euclidBall 0 (1 / 2)) :
    ((0 : ℝ), u) ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2) := by
  refine ⟨?_, hu⟩
  simp only [Prod.fst_zero, mem_Ioc, le_refl, and_true]
  norm_num

theorem mem_euclidBall_spDilInv {x y : Vec 2} {r ρ : ℝ} (hr : 0 < r) :
    spDilInv x r y ∈ euclidBall 0 ρ ↔ y ∈ euclidBall x (r * ρ) := by
  have := mem_euclidBall_dil (c := x) (y := spDilInv x r y) (ρ := ρ) hr
  rw [show x + r • spDilInv x r y = y from spDil_spDilInv x hr.ne' y] at this
  exact this.symm

/-- Geometry of the rescaled disc `B'`. -/
theorem rescaled_ball_geometry {x z : Vec 2} {r : ℝ} (hr : 0 < r)
    (hz : vecNormSq (z - x) < r ^ 2 / 72) {y : Vec 2}
    (hy : z + r • y ∈ euclidBall x (r / 4)) :
    y ∈ euclidBall 0 (1 / 2) ∧ y + spDilInv x r z ∈ euclidBall 0 (1 / 4) := by
  simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
  have hr2 : 0 < r ^ 2 := by positivity
  have hdiff : r • y = (z + r • y - x) - (z - x) := by abel
  have h1 : vecNormSq (r • y) ≤ 2 * (vecNormSq (z + r • y - x) + vecNormSq (z - x)) := by
    have := vecNormSq_sub_le (z + r • y - x) (z - x)
    rwa [← hdiff] at this
  have h2 : y + spDilInv x r z = r⁻¹ • (z + r • y - x) := by
    simp only [spDilInv, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    abel
  constructor
  · rw [sub_zero]
    have h3 : r ^ 2 * vecNormSq y < r ^ 2 * (1 / 2) ^ 2 := by
      rw [← vecNormSq_smul]
      nlinarith
    exact lt_of_mul_lt_mul_left h3 hr2.le
  · rw [sub_zero, h2, vecNormSq_smul]
    have h3 : vecNormSq (z + r • y - x) < (r / 4) ^ 2 := by simpa using hy
    have : (r⁻¹) ^ 2 * vecNormSq (z + r • y - x) < (r⁻¹) ^ 2 * (r / 4) ^ 2 :=
      mul_lt_mul_of_pos_left h3 (by positivity)
    have h4 : (r⁻¹) ^ 2 * (r / 4) ^ 2 = (1 / 4) ^ 2 := by field_simp
    linarith

theorem vecNormSq_neg' (e : Vec 2) : vecNormSq (-e) = vecNormSq e := by
  simp [vecNormSq, vecDot]

theorem holder_at_top {Ut : ℝ × Vec 2 → ℝ} {M₁ a' : ℝ}
    (hhol : ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z' ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
      |Ut z - Ut z'| ≤ M₁ * parabolicHolderDistance z z' ^ a')
    {u u' : Vec 2} (hu : u ∈ euclidBall 0 (1 / 2)) (hu' : u' ∈ euclidBall 0 (1 / 2)) :
    |Ut (0, u) - Ut (0, u')| ≤ M₁ * (Real.sqrt (vecNormSq (u - u'))) ^ a' := by
  have := hhol _ (zero_mem_cylinder_of hu) _ (zero_mem_cylinder_of hu')
  simpa [parabolicHolderDistance] using this

/-- The core trace estimate in rescaled coordinates. -/
theorem trace_estimate {Ut : ℝ × Vec 2 → ℝ} {M₁ a' r : ℝ} {x z : Vec 2} (hr : 0 < r)
    (hcont : ContinuousOn Ut (AVRegularity.External.Campanato.cylinder 0 (1 / 2)))
    (hhol : ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z' ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
      |Ut z - Ut z'| ≤ M₁ * parabolicHolderDistance z z' ^ a')
    (hz : vecNormSq (z - x) < r ^ 2 / 72) {f : Vec 2 → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => f (z + r • y)) (volume.restrict (euclidBall 0 (1 / 2))))
    (hint : IntegrableOn (fun y => (f (z + r • y) - Ut (0, y)) ^ 2) (euclidBall 0 (1 / 2))) :
    IntegrableOn (fun y => (f y - tubeProfile Ut x r y) ^ 2) (euclidBall x (r / 4)) ∧
    ∫ y in euclidBall x (r / 4), (f y - tubeProfile Ut x r y) ^ 2 ≤
      r ^ 2 * (2 * (∫ y in euclidBall 0 (1 / 2), (f (z + r • y) - Ut (0, y)) ^ 2) +
        2 * (M₁ * Real.sqrt (vecNormSq (spDilInv x r z)) ^ a') ^ 2 *
          volume.real (euclidBall 0 (1 / 2))) := by
  set e : Vec 2 := spDilInv x r z with he
  set ε : ℝ := M₁ * Real.sqrt (vecNormSq e) ^ a' with hε
  set B' : Set (Vec 2) := spDil z r ⁻¹' euclidBall x (r / 4) with hB'
  have hBimg : spDil z r '' B' = euclidBall x (r / 4) :=
    Set.image_preimage_eq _ (fun y => ⟨spDilInv z r y, spDil_spDilInv z hr.ne' y⟩)
  have hBmeas : MeasurableSet B' := measurable_spDil z r (euclidBall_measurable x _)
  have hgeom : ∀ y ∈ B', y ∈ euclidBall 0 (1 / 2) ∧ y + e ∈ euclidBall 0 (1 / 4) :=
    fun y hy => rescaled_ball_geometry hr hz hy
  have hB'sub : B' ⊆ euclidBall 0 (1 / 2) := fun y hy => (hgeom y hy).1
  have hid : ∀ y, (f (spDil z r y) - tubeProfile Ut x r (spDil z r y)) ^ 2 =
      (f (z + r • y) - Ut (0, y + e)) ^ 2 := by
    intro y
    have : spDilInv x r (spDil z r y) = y + e := by
      simp only [spDilInv, spDil, he, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne',
        one_smul]
      abel
    simp only [tubeProfile, this]
    rfl
  -- measurability of the shifted profile
  have hUt0 : ContinuousOn (fun y : Vec 2 => Ut (0, y)) (euclidBall 0 (1 / 2)) :=
    hcont.comp (by fun_prop) (fun y hy => zero_mem_cylinder_of hy)
  have hUte : ContinuousOn (fun y : Vec 2 => Ut (0, y + e)) B' := by
    refine hcont.comp (by fun_prop) (fun y hy => zero_mem_cylinder_of ?_)
    have := (hgeom y hy).2
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at this ⊢
    nlinarith [vecNormSq_nonneg (y + e)]
  have hmeas' : AEStronglyMeasurable (fun y => f (z + r • y)) (volume.restrict B') :=
    hmeas.mono_measure (Measure.restrict_mono hB'sub le_rfl)
  have hUt0m : AEStronglyMeasurable (fun y : Vec 2 => Ut (0, y)) (volume.restrict B') :=
    (hUt0.mono hB'sub).aestronglyMeasurable hBmeas
  have hUtem : AEStronglyMeasurable (fun y : Vec 2 => Ut (0, y + e)) (volume.restrict B') :=
    hUte.aestronglyMeasurable hBmeas
  -- pointwise bound
  have hpt : ∀ y ∈ B', (f (z + r • y) - Ut (0, y + e)) ^ 2 ≤
      2 * (f (z + r • y) - Ut (0, y)) ^ 2 + 2 * ε ^ 2 := by
    intro y hy
    have hh := holder_at_top hhol (hgeom y hy).1
      (u' := y + e) (by
        have := (hgeom y hy).2
        simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at this ⊢
        nlinarith [vecNormSq_nonneg (y + e)])
    rw [show y - (y + e) = -e by abel, vecNormSq_neg'] at hh
    have h2 : (Ut (0, y) - Ut (0, y + e)) ^ 2 ≤ ε ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hh 2
    nlinarith [h2, sq_nonneg (f (z + r • y) - Ut (0, y) - (Ut (0, y) - Ut (0, y + e)))]
  have hg : IntegrableOn (fun y => 2 * (f (z + r • y) - Ut (0, y)) ^ 2 + 2 * ε ^ 2) B' := by
    have h1 : IntegrableOn (fun y => (f (z + r • y) - Ut (0, y)) ^ 2) B' := hint.mono_set hB'sub
    have h2 : IntegrableOn (fun _ : Vec 2 => 2 * ε ^ 2) B' :=
      integrableOn_const (lt_top_iff_ne_top.1 (lt_of_le_of_lt (measure_mono hB'sub)
        (volume_euclidBall_lt_top 0 (1 / 2))))
    exact (h1.const_mul 2).add h2
  have hFint : IntegrableOn (fun y => (f (z + r • y) - Ut (0, y + e)) ^ 2) B' := by
    refine hg.mono' ((hmeas'.sub hUtem).pow 2) ?_
    refine (ae_restrict_iff' hBmeas).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt y hy
  constructor
  · rw [← hBimg, integrableOn_spDil_image hr.ne']
    simpa only [hid] using hFint
  · have h1 : ∫ y in B', (f (spDil z r y) - tubeProfile Ut x r (spDil z r y)) ^ 2 =
        (r ^ 2)⁻¹ * ∫ y in euclidBall x (r / 4), (f y - tubeProfile Ut x r y) ^ 2 := by
      rw [← hBimg]
      exact integral_spDil z hr.ne' (fun y => (f y - tubeProfile Ut x r y) ^ 2) B'
    have h2 : ∫ y in B', (f (spDil z r y) - tubeProfile Ut x r (spDil z r y)) ^ 2 ≤
        ∫ y in B', (2 * (f (z + r • y) - Ut (0, y)) ^ 2 + 2 * ε ^ 2) := by
      simp only [hid]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) hg ?_
      exact (ae_restrict_iff' hBmeas).2 (Filter.Eventually.of_forall hpt)
    have h3 : ∫ y in B', (2 * (f (z + r • y) - Ut (0, y)) ^ 2 + 2 * ε ^ 2) =
        2 * (∫ y in B', (f (z + r • y) - Ut (0, y)) ^ 2) + 2 * ε ^ 2 * volume.real B' := by
      have hc1 : ∫ y in B', 2 * (f (z + r • y) - Ut (0, y)) ^ 2 =
          2 * ∫ y in B', (f (z + r • y) - Ut (0, y)) ^ 2 := integral_const_mul _ _
      have hc2 : ∫ _y in B', 2 * ε ^ 2 = volume.real B' * (2 * ε ^ 2) := by
        rw [setIntegral_const, smul_eq_mul]
      rw [integral_add ((hint.mono_set hB'sub).const_mul 2) (integrableOn_const
        (lt_top_iff_ne_top.1 (lt_of_le_of_lt (measure_mono hB'sub)
          (volume_euclidBall_lt_top 0 (1 / 2))))), hc1, hc2]
      ring
    have h4 : ∫ y in B', (f (z + r • y) - Ut (0, y)) ^ 2 ≤
        ∫ y in euclidBall 0 (1 / 2), (f (z + r • y) - Ut (0, y)) ^ 2 :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hB'sub)
    have h5 : volume.real B' ≤ volume.real (euclidBall 0 (1 / 2)) :=
      measureReal_mono hB'sub (lt_top_iff_ne_top.1 (volume_euclidBall_lt_top 0 (1 / 2)))
    have hr2 : 0 < r ^ 2 := by positivity
    have h6 : ∫ y in euclidBall x (r / 4), (f y - tubeProfile Ut x r y) ^ 2 =
        r ^ 2 * ∫ y in B', (f (spDil z r y) - tubeProfile Ut x r (spDil z r y)) ^ 2 := by
      rw [h1]; field_simp
    rw [h6]
    refine mul_le_mul_of_nonneg_left (h2.trans ?_) hr2.le
    rw [h3]
    have : 2 * ε ^ 2 * volume.real B' ≤ 2 * ε ^ 2 * volume.real (euclidBall 0 (1 / 2)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith [h4, this]

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization Set
namespace AVRegularity.Applications

/-! # Uniqueness of continuous representatives of the trace

Two continuous, bounded functions which are both `L²`-limits of `w(σ, ·)` on an open set `V`
as `σ → t⁻` (a.e.) coincide on `V`: in the proof of Lemma 8.1 of the paper, the limits from
different cylinders agree on overlaps. -/

theorem traces_unique {w : ℝ × Vec 2 → ℝ} {t : ℝ} {W₁ W₂ : Vec 2 → ℝ} {V B₁ B₂ : Set (Vec 2)}
    {M : ℝ} (hV : IsOpen V) (hVfin : volume V < ⊤) (hV1 : V ⊆ B₁) (hV2 : V ⊆ B₂)
    (hc1 : ContinuousOn W₁ V) (hc2 : ContinuousOn W₂ V)
    (hb1 : ∀ y ∈ V, |W₁ y| ≤ M) (hb2 : ∀ y ∈ V, |W₂ y| ≤ M)
    (hi1 : ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      IntegrableOn (fun y => (w (σ, y) - W₁ y) ^ 2) B₁)
    (ht1 : Tendsto (fun σ : ℝ => ∫ y in B₁, (w (σ, y) - W₁ y) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0))
    (hi2 : ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      IntegrableOn (fun y => (w (σ, y) - W₂ y) ^ 2) B₂)
    (ht2 : Tendsto (fun σ : ℝ => ∫ y in B₂, (w (σ, y) - W₂ y) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) :
    EqOn W₁ W₂ V := by
  have := neBot_nhdsLT_inf_ae t
  set F : Filter ℝ := 𝓝[<] t ⊓ ae (volume : Measure ℝ) with hF
  -- traces on `V`
  have tV : ∀ {W : Vec 2 → ℝ} {B : Set (Vec 2)}, V ⊆ B →
      (∀ᶠ σ in F, IntegrableOn (fun y => (w (σ, y) - W y) ^ 2) B) →
      Tendsto (fun σ : ℝ => ∫ y in B, (w (σ, y) - W y) ^ 2) F (𝓝 0) →
      Tendsto (fun σ : ℝ => ∫ y in V, (w (σ, y) - W y) ^ 2) F (𝓝 0) := by
    intro W B hVB hi ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Filter.Eventually.of_forall fun σ => integral_nonneg fun y => sq_nonneg _) ?_
    filter_upwards [hi] with σ hσ
    exact setIntegral_mono_set hσ (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hVB)
  have h1 := tV hV1 hi1 ht1
  have h2 := tV hV2 hi2 ht2
  have hVm : MeasurableSet V := hV.measurableSet
  -- integrability of the squares on `V`
  have hI1 : ∀ᶠ σ in F, IntegrableOn (fun y => (w (σ, y) - W₁ y) ^ 2) V :=
    hi1.mono fun σ h => h.mono_set hV1
  have hI2 : ∀ᶠ σ in F, IntegrableOn (fun y => (w (σ, y) - W₂ y) ^ 2) V :=
    hi2.mono fun σ h => h.mono_set hV2
  -- the integral of `(W₁ - W₂)²` over `V` vanishes
  have hbound : ∀ᶠ σ in F, ∫ y in V, (W₁ y - W₂ y) ^ 2 ≤
      2 * (∫ y in V, (w (σ, y) - W₁ y) ^ 2) + 2 * (∫ y in V, (w (σ, y) - W₂ y) ^ 2) := by
    filter_upwards [hI1, hI2] with σ a b
    have hs : ∫ y in V, (W₁ y - W₂ y) ^ 2 ≤
        ∫ y in V, (2 * (w (σ, y) - W₁ y) ^ 2 + 2 * (w (σ, y) - W₂ y) ^ 2) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        ((a.const_mul 2).add (b.const_mul 2))
        (ae_restrict_of_forall_mem hVm fun y _ => by
          nlinarith [sq_nonneg (w (σ, y) - W₁ y + (w (σ, y) - W₂ y))])
    rwa [integral_add (a.const_mul 2) (b.const_mul 2), integral_const_mul,
      integral_const_mul] at hs
  have hlim : Tendsto (fun σ : ℝ => 2 * (∫ y in V, (w (σ, y) - W₁ y) ^ 2) +
      2 * (∫ y in V, (w (σ, y) - W₂ y) ^ 2)) F (𝓝 0) := by
    simpa using ((h1.const_mul 2).add (h2.const_mul 2))
  have hL : ∫ y in V, (W₁ y - W₂ y) ^ 2 ≤ 0 := ge_of_tendsto hlim hbound
  have hL0 : ∫ y in V, (W₁ y - W₂ y) ^ 2 = 0 :=
    le_antisymm hL (integral_nonneg fun y => sq_nonneg _)
  have hcont : ContinuousOn (fun y => (W₁ y - W₂ y) ^ 2) V := (hc1.sub hc2).pow 2
  have hint : Integrable (fun y => (W₁ y - W₂ y) ^ 2) (volume.restrict V) := by
    have hfin : IsFiniteMeasure (volume.restrict V) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hVfin⟩
    refine (integrable_const ((2 * M) ^ 2)).mono' (hcont.aestronglyMeasurable hVm) ?_
    refine ae_restrict_of_forall_mem hVm fun y hy => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 : |W₁ y - W₂ y| ≤ 2 * M := by
      have := abs_sub (W₁ y) (W₂ y)
      linarith [hb1 y hy, hb2 y hy]
    calc (W₁ y - W₂ y) ^ 2 = |W₁ y - W₂ y| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hint).1 hL0
  have heq := Measure.eqOn_open_of_ae_eq hae hV hcont continuousOn_const
  intro y hy
  have := heq hy
  have h2 : (W₁ y - W₂ y) ^ 2 = 0 := this
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization Set AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # Applying the microscopic oscillation lemma to the rescaled tube

`OcAt a' η C` is the body of `OcMicroscopicStatement` for fixed `a', η, C`. For `K = 0` and a
divergence-free drift of size at most `η`, it gives a continuous representative `Ut` of the
rescaled solution with the trace convergence and the bounds
`|Ut z - Ut z'| ≤ C R ρ(z,z')^{a'}`, `|Ut z| ≤ (C+1) R`, `R = (⨍_{Q₁} U²)^{1/2}`. -/

/-- The statement of `OcMicroscopicStatement` for fixed exponent and constants. -/
def OcAt (a' η C : ℝ) : Prop :=
  ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2),
    (∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) →
    (∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) →
    (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
    (∃ kK kd : ℝ, 0 ≤ kK ∧ 0 ≤ kd ∧ kK + kd ≤ η ∧
      ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
        (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
        vecNormSq (d p) ≤ kd ^ 2) →
    IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
    ∃ Ut : ℝ × Vec 2 → ℝ,
      ContinuousOn Ut (AVRegularity.External.Campanato.cylinder 0 (1 / 2)) ∧
      Ut =ᵐ[volume.restrict (AVRegularity.External.Campanato.cylinder 0 (1 / 2))] U ∧
      Tendsto (fun τ => ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2)
        (𝓝[<] 0 ⊓ ae volume) (𝓝 0) ∧
      ∀ c : ℝ, ∀ x ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
        ∀ w ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), z ≠ w →
          |Ut z - Ut w| / parabolicHolderDistance z w ^ a' + |Ut x - cylinderMean U 0 1|
            ≤ C * Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2)

theorem ocAt_of_statement (hcamp : OcMicroscopicStatement) {a' : ℝ} (ha0 : 0 < a')
    (ha1 : a' < 1) : ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ OcAt a' η C :=
  hcamp a' ha0 ha1

theorem parabolicHolderDistance_pos {z w : ℝ × Vec 2} (h : z ≠ w) :
    0 < parabolicHolderDistance z w := by
  unfold parabolicHolderDistance
  by_contra hle
  rw [not_lt] at hle
  have h1 := Real.sqrt_nonneg (vecNormSq (z.2 - w.2))
  have h2 := Real.sqrt_nonneg |z.1 - w.1|
  have e1 : Real.sqrt (vecNormSq (z.2 - w.2)) = 0 := by linarith
  have e2 : Real.sqrt |z.1 - w.1| = 0 := by linarith
  rw [Real.sqrt_eq_zero (vecNormSq_nonneg _)] at e1
  rw [Real.sqrt_eq_zero (abs_nonneg _), abs_eq_zero] at e2
  apply h
  refine Prod.ext (sub_eq_zero.1 e2) ?_
  exact sub_eq_zero.1 (vecNormSq_eq_zero e1)

theorem parabolicHolderDistance_nonneg' (z w : ℝ × Vec 2) : 0 ≤ parabolicHolderDistance z w :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem parabolicHolderDistance_self (z : ℝ × Vec 2) : parabolicHolderDistance z z = 0 := by
  simp [parabolicHolderDistance, vecNormSq, vecDot]

/-- Consequences of `OcAt` for the rescaled tube. -/
theorem camp_apply {a' η Ch : ℝ} (ha : 0 < a') (H : OcAt a' η Ch)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} {d : ℝ × Vec 2 → Vec 2}
    (hd : Continuous d) {kd : ℝ} (hkd0 : 0 ≤ kd) (hkd : kd ≤ η)
    (hdb : ∀ p ∈ openCyl 0 1, vecNormSq (d p) ≤ kd ^ 2) (hdiv : IsDivFreeQ1 d)
    (hE : IsEnergyClassQ1 U DU) (hW : IsSkewDriftWeak 0 d U DU) :
    ∃ Ut : ℝ × Vec 2 → ℝ, ContinuousOn Ut (AVRegularity.External.Campanato.cylinder 0 (1 / 2)) ∧
      Tendsto (fun τ => ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2)
        (𝓝[<] 0 ⊓ ae volume) (𝓝 0) ∧
      (∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z' ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
        |Ut z - Ut z'| ≤ Ch * Real.sqrt (⨍ p in openCyl 0 1, U p ^ 2) *
          parabolicHolderDistance z z' ^ a') ∧
      ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
        |Ut z| ≤ (Ch + 1) * Real.sqrt (⨍ p in openCyl 0 1, U p ^ 2) := by
  obtain ⟨Ut, hcont, -, htr, hbound⟩ := H 0 d U DU
    (fun i j => by simpa using aestronglyMeasurable_const)
    (fun i => (continuous_apply i |>.comp hd).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => by simp)
    ⟨0, kd, le_rfl, hkd0, by simpa using hkd, (ae_restrict_iff' (openCyl_measurable 0 1)).2
      (Filter.Eventually.of_forall fun p hp => ⟨fun e => by simp [vecNormSq, vecDot], hdb p hp⟩)⟩ hdiv hE hW
  set R : ℝ := Real.sqrt (⨍ p in openCyl 0 1, U p ^ 2) with hR
  have hb0 : ∀ x ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
      ∀ w ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), z ≠ w →
        |Ut z - Ut w| / parabolicHolderDistance z w ^ a' + |Ut x - cylinderMean U 0 1|
          ≤ Ch * R := by
    intro x hx z hz w hw hzw
    simpa [hR] using hbound 0 x hx z hz w hw hzw
  have hz0 : ((0 : ℝ), (0 : Vec 2)) ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2) :=
    zero_mem_cylinder_of (by simp [euclidBall, vecNormSq, vecDot])
  refine ⟨Ut, hcont, htr, ?_, ?_⟩
  · intro z hz z' hz'
    by_cases h : z = z'
    · subst h
      simp [parabolicHolderDistance_self, Real.zero_rpow ha.ne']
    · have hpos := parabolicHolderDistance_pos h
      have := hb0 _ hz z hz z' hz' h
      have h1 : |Ut z - Ut z'| / parabolicHolderDistance z z' ^ a' ≤ Ch * R :=
        le_trans (le_add_of_nonneg_right (abs_nonneg _)) this
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)] at h1
      exact h1
  · intro z hz
    have hmean : |cylinderMean U 0 1| ≤ R := cylinderMean_abs_le hE.1
    have hw1 : ((-1 / 8 : ℝ), (0 : Vec 2)) ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2) := by
      refine ⟨?_, by simp [euclidBall, vecNormSq, vecDot]⟩
      simp only [Prod.fst_zero, mem_Ioc]
      constructor <;> norm_num
    have hne : (((0 : ℝ), (0 : Vec 2)) : ℝ × Vec 2) ≠ ((-1 / 8 : ℝ), (0 : Vec 2)) := by
      intro h
      have := congrArg Prod.fst h
      norm_num at this
    have h1 := hb0 z hz _ hz0 _ hw1 hne
    have h2 : |Ut z - cylinderMean U 0 1| ≤ Ch * R :=
      le_trans (le_add_of_nonneg_left (div_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (parabolicHolderDistance_nonneg' _ _) _))) h1
    calc |Ut z| = |(Ut z - cylinderMean U 0 1) + cylinderMean U 0 1| := by rw [sub_add_cancel]
      _ ≤ |Ut z - cylinderMean U 0 1| + |cylinderMean U 0 1| := abs_add_le _ _
      _ ≤ Ch * R + R := add_le_add h2 hmean
      _ = (Ch + 1) * R := by ring

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Set Filter Topology AVRegularity.External.Campanato
namespace AVRegularity.Applications

/-! # The moving-frame trace gives the fixed-frame trace

If the continuous representative `Ut` of the rescaled solution `U(τ, y) = w(t + cτ, Y(t+cτ) + r y)`
converges to the rescaled solution in `L²(B_{1/2})` as `τ → 0⁻` (a.e.), then the profile
`y ↦ Ut(0, (y - Y t)/r)` is the `L²(B_{r/4}(Y t))`-limit of `w(σ, ·)` as `σ → t⁻` (a.e.): the discs
`B_{r/4}(Y t)` and `B_{r/2}(Y σ)` are comparable and `Ut` is uniformly continuous.
-/

theorem euclidBall_half_subset_one : euclidBall (0 : Vec 2) (1 / 2) ⊆ euclidBall 0 1 := by
  intro y hy
  simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at hy ⊢
  nlinarith [vecNormSq_nonneg y]

theorem trace_package {w : ℝ × Vec 2 → ℝ} {Ut : ℝ × Vec 2 → ℝ} {Y : ℝ → Vec 2}
    {t r c M₁ M₀ a' B : ℝ} (hc : 0 < c) (hr : 0 < r) (ha : 0 < a') (hY : Continuous Y)
    (hB : 0 ≤ B) (hlip : ∀ s, ‖Y s - Y t‖ ≤ B * |s - t|)
    (hcont : ContinuousOn Ut (AVRegularity.External.Campanato.cylinder 0 (1 / 2)))
    (hhol : ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), ∀ z' ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2),
      |Ut z - Ut z'| ≤ M₁ * parabolicHolderDistance z z' ^ a')
    (hbd : ∀ z ∈ AVRegularity.External.Campanato.cylinder 0 (1 / 2), |Ut z| ≤ M₀)
    (htr : Tendsto (fun τ : ℝ => ∫ y in euclidBall 0 (1 / 2),
      (w (t + c * τ, Y (t + c * τ) + r • y) - Ut (0, y)) ^ 2)
      (𝓝[<] 0 ⊓ ae (volume : Measure ℝ)) (𝓝 0))
    (hslice : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      AEStronglyMeasurable (fun y => w (t + c * τ, Y (t + c * τ) + r • y))
        (volume.restrict (euclidBall 0 1)) ∧
      IntegrableOn (fun y => w (t + c * τ, Y (t + c * τ) + r • y) ^ 2) (euclidBall 0 1)) :
    (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      IntegrableOn (fun y => (w (σ, y) - tubeProfile Ut (Y t) r y) ^ 2)
        (euclidBall (Y t) (r / 4))) ∧
    Tendsto (fun σ : ℝ => ∫ y in euclidBall (Y t) (r / 4),
      (w (σ, y) - tubeProfile Ut (Y t) r y) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
  set F : Filter ℝ := 𝓝[<] t ⊓ ae (volume : Measure ℝ) with hF
  set x : Vec 2 := Y t with hx
  -- Step 1: a.e. slice facts in rescaled time
  have hQ : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      AEStronglyMeasurable (fun y => w (t + c * τ, Y (t + c * τ) + r • y))
        (volume.restrict (euclidBall 0 (1 / 2))) ∧
      IntegrableOn (fun y => (w (t + c * τ, Y (t + c * τ) + r • y) - Ut (0, y)) ^ 2)
        (euclidBall 0 (1 / 2)) := by
    filter_upwards [hslice] with τ ⟨hm, hi⟩
    have hm' := hm.mono_measure (Measure.restrict_mono euclidBall_half_subset_one le_rfl)
    refine ⟨hm', ?_⟩
    have hUt0 : ContinuousOn (fun y : Vec 2 => Ut (0, y)) (euclidBall 0 (1 / 2)) :=
      hcont.comp (by fun_prop) (fun y hy => zero_mem_cylinder_of hy)
    have hfin : volume (euclidBall (0 : Vec 2) (1 / 2)) ≠ ⊤ :=
      (volume_euclidBall_lt_top 0 (1 / 2)).ne
    have hg : IntegrableOn (fun y => 2 * w (t + c * τ, Y (t + c * τ) + r • y) ^ 2 + 2 * M₀ ^ 2)
        (euclidBall 0 (1 / 2)) :=
      ((hi.mono_set euclidBall_half_subset_one).const_mul 2).add (integrableOn_const hfin)
    refine hg.mono' ((hm'.sub (hUt0.aestronglyMeasurable (euclidBall_measurable 0 _))).pow 2) ?_
    refine (ae_restrict_iff' (euclidBall_measurable 0 _)).2 (Filter.Eventually.of_forall
      fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := hbd _ (zero_mem_cylinder_of hy)
    have : (Ut (0, y)) ^ 2 ≤ M₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_nonneg (w (t + c * τ, Y (t + c * τ) + r • y) + Ut (0, y))]
  -- Step 2: transfer to physical time
  have hQσ : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t - c) t →
      AEStronglyMeasurable (fun y => w (σ, Y σ + r • y)) (volume.restrict (euclidBall 0 (1 / 2))) ∧
      IntegrableOn (fun y => (w (σ, Y σ + r • y) - Ut (0, y)) ^ 2) (euclidBall 0 (1 / 2)) := by
    have h1 := ae_restrict_timeDil_inv t hc hQ
    rw [image_timeDil_Ioo t hc] at h1
    rw [ae_restrict_iff' measurableSet_Ioo] at h1
    filter_upwards [h1] with σ hσ hσmem
    have hmem : σ ∈ Ioo (t + c * (-1)) (t + c * 0) := by
      constructor <;> simp only [mul_neg, mul_one, mul_zero, add_zero] at hσmem ⊢ <;>
        linarith [hσmem.1, hσmem.2]
    have := hσ hmem
    have e : t + c * ((σ - t) / c) = σ := by field_simp; ring
    simpa only [e] using this
  -- Step 3: eventually good
  set ε₁ : ℝ := min c (r / (12 * (B + 1))) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hc (by positivity)
  have hgood : ∀ᶠ σ in F, σ ∈ Ioo (t - ε₁) t ∧
      (σ ∈ Ioo (t - c) t →
        AEStronglyMeasurable (fun y => w (σ, Y σ + r • y)) (volume.restrict (euclidBall 0 (1 / 2))) ∧
        IntegrableOn (fun y => (w (σ, Y σ + r • y) - Ut (0, y)) ^ 2) (euclidBall 0 (1 / 2))) := by
    have h1 : ∀ᶠ σ in 𝓝[<] t, σ ∈ Ioo (t - ε₁) t := Ioo_mem_nhdsLT (by linarith)
    exact (h1.filter_mono inf_le_left).and (hQσ.filter_mono inf_le_right)
  -- Step 4: the key estimate for good times
  have hkey : ∀ᶠ σ in F,
      IntegrableOn (fun y => (w (σ, y) - tubeProfile Ut x r y) ^ 2) (euclidBall x (r / 4)) ∧
      ∫ y in euclidBall x (r / 4), (w (σ, y) - tubeProfile Ut x r y) ^ 2 ≤
        r ^ 2 * (2 * (∫ y in euclidBall 0 (1 / 2), (w (σ, Y σ + r • y) - Ut (0, y)) ^ 2) +
          2 * (M₁ * Real.sqrt (vecNormSq (spDilInv x r (Y σ))) ^ a') ^ 2 *
            volume.real (euclidBall 0 (1 / 2))) := by
    filter_upwards [hgood] with σ ⟨hσ, hQ'⟩
    have hσc : σ ∈ Ioo (t - c) t :=
      ⟨by linarith [hσ.1, min_le_left c (r / (12 * (B + 1)))], hσ.2⟩
    obtain ⟨hm, hi⟩ := hQ' hσc
    have hdist : ‖Y σ - x‖ < r / 12 := by
      have h1 := hlip σ
      have h2 : |σ - t| < r / (12 * (B + 1)) := by
        rw [abs_of_neg (by linarith [hσ.2])]
        linarith [hσ.1, min_le_right c (r / (12 * (B + 1)))]
      calc ‖Y σ - x‖ ≤ B * |σ - t| := h1
        _ ≤ (B + 1) * |σ - t| := by nlinarith [abs_nonneg (σ - t)]
        _ < (B + 1) * (r / (12 * (B + 1))) :=
          mul_lt_mul_of_pos_left h2 (by positivity)
        _ = r / 12 := by field_simp
    have hz : vecNormSq (Y σ - x) < r ^ 2 / 72 := by
      have h1 := vecNormSq_le_two_norm_sq (Y σ - x)
      have h2 : ‖Y σ - x‖ ^ 2 < (r / 12) ^ 2 :=
        pow_lt_pow_left₀ hdist (norm_nonneg _) two_ne_zero
      nlinarith
    exact trace_estimate hr hcont hhol hz hm hi
  refine ⟨hkey.mono fun σ h => h.1, ?_⟩
  -- Step 5: squeeze
  have hJ : Tendsto (fun σ : ℝ => ∫ y in euclidBall 0 (1 / 2),
      (w (σ, Y σ + r • y) - Ut (0, y)) ^ 2) F (𝓝 0) := by
    have := htr.comp (tendsto_timeNormalize t hc)
    refine this.congr fun σ => ?_
    have e : t + c * ((σ - t) / c) = σ := by field_simp; ring
    simp only [Function.comp, e]
  have hE : Tendsto (fun σ : ℝ => M₁ * Real.sqrt (vecNormSq (spDilInv x r (Y σ))) ^ a') F
      (𝓝 0) := by
    have hcts : Continuous fun σ : ℝ => M₁ * Real.sqrt (vecNormSq (spDilInv x r (Y σ))) ^ a' := by
      refine continuous_const.mul (Continuous.rpow_const ?_ fun _ => Or.inr ha.le)
      refine Real.continuous_sqrt.comp ?_
      have : Continuous fun σ : ℝ => spDilInv x r (Y σ) := by
        unfold spDilInv; fun_prop
      unfold vecNormSq vecDot
      fun_prop
    have h0 : M₁ * Real.sqrt (vecNormSq (spDilInv x r (Y t))) ^ a' = 0 := by
      have : spDilInv x r (Y t) = 0 := by simp [spDilInv, hx]
      rw [this]
      simp [vecNormSq, vecDot, Real.zero_rpow ha.ne']
    have := hcts.tendsto t
    rw [h0] at this
    exact this.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have hbound : Tendsto (fun σ : ℝ => r ^ 2 * (2 * (∫ y in euclidBall 0 (1 / 2),
      (w (σ, Y σ + r • y) - Ut (0, y)) ^ 2) +
      2 * (M₁ * Real.sqrt (vecNormSq (spDilInv x r (Y σ))) ^ a') ^ 2 *
        volume.real (euclidBall 0 (1 / 2)))) F (𝓝 0) := by
    have h := (((hJ.const_mul 2).add (((hE.pow 2).const_mul 2).mul_const
      (volume.real (euclidBall (0 : Vec 2) (1 / 2))))).const_mul (r ^ 2))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Filter.Eventually.of_forall fun σ => integral_nonneg fun y => sq_nonneg _) ?_
  filter_upwards [hkey] with σ h using h.2

end AVRegularity.Applications
end
