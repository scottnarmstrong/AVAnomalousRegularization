-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Microscopic.DilationTests
import Mathlib.MeasureTheory.Function.L2Space
import Homogenization.Ambient.BlockMatrix

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Rescaling the small skew/drift problem

For `Q_r(z) ⊆ Q₁` and `0 < r ≤ 1`, the functions `U_{z,r} = U ∘ T`, `∇U_{z,r} = r (∇U) ∘ T`,
`K_{z,r} = K ∘ T`, `d_{z,r} = r d ∘ T`, `T = parDil z r`, satisfy every hypothesis of the lemma
whenever `U, K, d` do. -/

section
/-- `U_{z,r} = U ∘ parDil z r`. -/
def rsU (U : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (r : ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => U (parDil z r p)

/-- `∇U_{z,r} = r (∇U) ∘ parDil z r`. -/
def rsDU (DU : ℝ × Vec 2 → Vec 2) (z : ℝ × Vec 2) (r : ℝ) : ℝ × Vec 2 → Vec 2 :=
  fun p => r • DU (parDil z r p)

/-- `K_{z,r} = K ∘ parDil z r`. -/
def rsK (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ × Vec 2) (r : ℝ) :
    ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun p => K (parDil z r p)

/-- `d_{z,r} = r d ∘ parDil z r`. -/
def rsd (d : ℝ × Vec 2 → Vec 2) (z : ℝ × Vec 2) (r : ℝ) : ℝ × Vec 2 → Vec 2 :=
  fun p => r • d (parDil z r p)

section Inclusions

variable {z : ℝ × Vec 2} {r : ℝ}

theorem openCyl_subset_split (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1) :
    Set.Ioo (z.1 - r ^ 2) z.1 ⊆ Set.Ioo (-1 : ℝ) 0 ∧ euclidBall z.2 r ⊆ euclidBall 0 1 := by
  have hne : (openCyl z r).Nonempty := by
    refine ⟨(z.1 - r ^ 2 / 2, z.2), ?_, ?_⟩
    · constructor
      · have : 0 < r ^ 2 := by positivity
        simp only; linarith
      · have : 0 < r ^ 2 := by positivity
        simp only; linarith
    · simp only [euclidBall, Set.mem_ofPred_eq, sub_self]
      simp [vecNormSq, vecDot]
      positivity
  have h := (Set.prod_subset_prod_iff' hne).1 hsub
  simpa [openCyl] using h

end Inclusions

/-- The time dilation `τ ↦ a + c τ` as a measurable equivalence. -/
def timeDilEquiv (a : ℝ) {c : ℝ} (hc : c ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun := fun τ => a + c * τ
  invFun := fun t => (t - a) / c
  left_inv := fun τ => by field_simp; ring
  right_inv := fun t => by field_simp; ring
  measurable_toFun := by
    change Measurable (fun τ : ℝ => a + c * τ)
    fun_prop
  measurable_invFun := by
    change Measurable (fun t : ℝ => (t - a) / c)
    fun_prop

theorem map_timeDil_restrict (a : ℝ) {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    Measure.map (fun τ : ℝ => a + c * τ) (volume.restrict S) =
      ENNReal.ofReal c⁻¹ • volume.restrict ((fun τ : ℝ => a + c * τ) '' S) := by
  have hemb : MeasurableEmbedding (fun τ : ℝ => a + c * τ) :=
    (timeDilEquiv a hc.ne').measurableEmbedding
  have hmap := map_time_affine_volume a c hc.ne'
  rw [abs_of_pos (inv_pos.mpr hc)] at hmap
  rw [← Measure.restrict_smul, ← hmap, hemb.restrict_map,
    Set.preimage_image_eq _ hemb.injective]

theorem ae_restrict_timeDil (a : ℝ) {c : ℝ} (hc : 0 < c) {S : Set ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict ((fun τ : ℝ => a + c * τ) '' S)), P t) :
    ∀ᵐ τ ∂(volume.restrict S), P (a + c * τ) := by
  have hemb : MeasurableEmbedding (fun τ : ℝ => a + c * τ) :=
    (timeDilEquiv a hc.ne').measurableEmbedding
  rw [← hemb.ae_map_iff (p := P), map_timeDil_restrict a hc S]
  exact Measure.ae_smul_measure h _

theorem image_timeDil_Ioo (a : ℝ) {c : ℝ} (hc : 0 < c) (lo hi : ℝ) :
    (fun τ : ℝ => a + c * τ) '' Set.Ioo lo hi = Set.Ioo (a + c * lo) (a + c * hi) := by
  ext t
  constructor
  · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨(t - a) / c, ⟨?_, ?_⟩, by field_simp; ring⟩
    · rw [lt_div_iff₀ hc]; linarith
    · rw [div_lt_iff₀ hc]; linarith

section Transfer

variable {z : ℝ × Vec 2} {r : ℝ}

theorem memLp_rescale (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1) {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCyl 0 1))) :
    MemLp (fun p => f (parDil z r p)) 2 (volume.restrict (openCyl 0 1)) := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr.ne').measurableEmbedding
  have h1 : MemLp f 2 (volume.restrict (parDil z r '' openCyl 0 1)) := by
    rw [image_parDil_openCyl z hr, mul_one]
    exact hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h2 : MemLp f 2 (Measure.map (parDil z r) (volume.restrict (openCyl 0 1))) := by
    rw [map_parDil_restrict z hr.ne']
    exact h1.smul_measure ENNReal.ofReal_ne_top
  exact (hemb.memLp_map_measure_iff).1 h2

theorem aestronglyMeasurable_rescale (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {f : ℝ × Vec 2 → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (openCyl 0 1))) :
    AEStronglyMeasurable (fun p => f (parDil z r p)) (volume.restrict (openCyl 0 1)) := by
  have hemb : MeasurableEmbedding (parDil z r) := (parDilEquiv z hr.ne').measurableEmbedding
  have h1 : AEStronglyMeasurable f (volume.restrict (parDil z r '' openCyl 0 1)) := by
    rw [image_parDil_openCyl z hr, mul_one]
    exact hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h2 : AEStronglyMeasurable f (Measure.map (parDil z r) (volume.restrict (openCyl 0 1))) := by
    rw [map_parDil_restrict z hr.ne']
    exact h1.smul_measure _
  exact (hemb.aestronglyMeasurable_map_iff).1 h2

theorem ae_rescale (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1) {P : ℝ × Vec 2 → Prop}
    (h : ∀ᵐ q ∂(volume.restrict (openCyl 0 1)), P q) :
    ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), P (parDil z r p) := by
  apply ae_restrict_parDil hr.ne'
  rw [image_parDil_openCyl z hr, mul_one]
  exact ae_restrict_of_ae_restrict_of_subset hsub h

end Transfer
end

/-! # The rescaled solution stays in the energy class; coefficient bounds rescale -/

section
variable {z : ℝ × Vec 2} {r : ℝ}

theorem volume_restrict_openCyl_eq_prod (z : ℝ × Vec 2) (r : ℝ) :
    volume.restrict (openCyl z r) =
      (volume.restrict (Set.Ioo (z.1 - r ^ 2) z.1)).prod (volume.restrict (euclidBall z.2 r)) := by
  rw [openCyl, Measure.volume_eq_prod, Measure.prod_restrict]

/-- Fubini: an `L²(Q₁)` function has `L²(B₁)` slices for a.e. time. -/
theorem ae_slice_integrable_sq {U : ℝ × Vec 2 → ℝ}
    (hU : MemLp U 2 (volume.restrict (openCyl 0 1))) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
      IntegrableOn (fun y => U (τ, y) ^ 2) (euclidBall 0 1) := by
  have hint : Integrable (fun p => U p ^ 2) (volume.restrict (openCyl 0 1)) := by
    have := hU.integrable_sq
    exact this
  rw [volume_restrict_openCyl_eq_prod] at hint
  have h := hint.prod_right_ae
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, one_pow] at h
  exact h

theorem rescale_energyClass (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} (hU : IsEnergyClassQ1 U DU) :
    IsEnergyClassQ1 (rsU U z r) (rsDU DU z r) := by
  obtain ⟨hU2, hDU2, hgrad, M, hM⟩ := hU
  have hr0 : r ≠ 0 := hr.ne'
  obtain ⟨htime, hspace⟩ := openCyl_subset_split hr hsub
  have himg : (fun τ : ℝ => z.1 + r ^ 2 * τ) '' Set.Ioo (-1) 0 = Set.Ioo (z.1 - r ^ 2) z.1 := by
    rw [image_timeDil_Ioo z.1 (by positivity : (0 : ℝ) < r ^ 2)]
    congr 1 <;> ring
  have htransfer : ∀ {P : ℝ → Prop}, (∀ᵐ t ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)), P t) →
      ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)), P (z.1 + r ^ 2 * τ) := by
    intro P h
    apply ae_restrict_timeDil z.1 (by positivity : (0 : ℝ) < r ^ 2)
    rw [himg]
    exact ae_restrict_of_ae_restrict_of_subset htime h
  refine ⟨memLp_rescale hr hsub hU2, ?_, ?_, ?_⟩
  · intro i
    have := (memLp_rescale hr hsub (hDU2 i)).const_mul r
    simpa [rsDU, Pi.smul_apply, smul_eq_mul] using this
  · filter_upwards [htransfer hgrad] with τ hτ
    have hball : HasWeakGradientOn (euclidBall z.2 (r * 1)) (fun y => U (z.1 + r ^ 2 * τ, y))
        (fun y => DU (z.1 + r ^ 2 * τ, y)) := by
      rw [mul_one]
      exact HasWeakGradientOn.mono_set hspace (External.Campanato.euclidBall_measurable 0 1) hτ
    exact HasWeakGradientOn.comp_spDil hr hball
  · refine ⟨(r ^ 2)⁻¹ * M, ?_⟩
    filter_upwards [htransfer hM, htransfer (ae_slice_integrable_sq hU2)] with τ hτ hint
    have hcv : ∫ y in euclidBall 0 1, rsU U z r (τ, y) ^ 2 =
        (r ^ 2)⁻¹ * ∫ x in euclidBall z.2 r, U (z.1 + r ^ 2 * τ, x) ^ 2 := by
      rw [show euclidBall z.2 r = spDil z.2 r '' euclidBall 0 1 by
        rw [image_spDil_euclidBall z.2 hr, mul_one], ← integral_spDil z.2 hr0]
      rfl
    rw [hcv]
    have hmono : ∫ x in euclidBall z.2 r, U (z.1 + r ^ 2 * τ, x) ^ 2 ≤
        ∫ x in euclidBall 0 1, U (z.1 + r ^ 2 * τ, x) ^ 2 :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hspace)
    have hpos : 0 ≤ (r ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg r)
    exact mul_le_mul_of_nonneg_left (hmono.trans hτ) hpos

theorem rescale_measurableK (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) :
    ∀ i j : Fin 2, AEStronglyMeasurable (fun p => rsK K z r p i j)
      (volume.restrict (openCyl 0 1)) :=
  fun i j => aestronglyMeasurable_rescale hr hsub (hK i j)

theorem rescale_measurabled (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {d : ℝ × Vec 2 → Vec 2}
    (hd : ∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) :
    ∀ i : Fin 2, AEStronglyMeasurable (fun p => rsd d z r p i) (volume.restrict (openCyl 0 1)) := by
  intro i
  have := (aestronglyMeasurable_rescale hr hsub (hd i)).const_mul r
  simpa [rsd, Pi.smul_apply, smul_eq_mul] using this

theorem rescale_skew (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) :
    ∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (rsK K z r p).transpose = -rsK K z r p :=
  ae_rescale hr hsub hK

theorem rescale_bound (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2} {kK kd : ℝ}
    (hb : ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
      (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
      vecNormSq (d p) ≤ kd ^ 2) :
    ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
      (∀ e : Vec 2, vecNormSq ((rsK K z r p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
      vecNormSq (rsd d z r p) ≤ (r * kd) ^ 2 := by
  filter_upwards [ae_rescale hr hsub hb] with p hp
  refine ⟨hp.1, ?_⟩
  simp only [rsd, vecNormSq_smul]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hp.2 (sq_nonneg r)
end

/-! # The rescaled problem satisfies the hypotheses of the small skew/drift lemma -/

section
variable {z : ℝ × Vec 2} {r : ℝ}

theorem openCyl_measurable (z : ℝ × Vec 2) (r : ℝ) : MeasurableSet (openCyl z r) :=
  measurableSet_Ioo.prod (External.Campanato.euclidBall_measurable z.2 r)

/-- The integrand of `IsSkewDriftWeak`. -/
def skewDriftIntegrand (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -(U p * stTimeDeriv φ p) + vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p)
    + vecDot (d p) (DU p) * φ p

theorem skewDriftIntegrand_rescale (hr : 0 < r) (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (d : ℝ × Vec 2 → Vec 2) (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2)
    {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p : ℝ × Vec 2) :
    skewDriftIntegrand (rsK K z r) (rsd d z r) (rsU U z r) (rsDU DU z r) φ p =
      r ^ 2 * skewDriftIntegrand K d U DU (pushTest z r φ) (parDil z r p) := by
  have hr0 : r ≠ 0 := hr.ne'
  unfold skewDriftIntegrand
  rw [stTimeDeriv_pushTest z hφ p hr0, stSpaceGrad_pushTest z hφ p hr0]
  simp only [rsK, rsd, rsU, rsDU, pushTest, parDilInv_parDil z hr0, Matrix.mulVec_smul,
    vecDot_smul_left, vecDot_smul_right]
  field_simp

theorem rescale_weak (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ × Vec 2 → Vec 2}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2} (hw : IsSkewDriftWeak K d U DU) :
    IsSkewDriftWeak (rsK K z r) (rsd d z r) (rsU U z r) (rsDU DU z r) := by
  intro φ hφ
  have hr0 : r ≠ 0 := hr.ne'
  have htest : IsSTTest (openCyl z (r * 1)) (pushTest z r φ) := isSTTest_pushTest z hr hφ
  rw [mul_one] at htest
  have h0 := hw (pushTest z r φ) ⟨htest.1, htest.2.1, htest.2.2.trans hsub⟩
  change ∫ p in openCyl 0 1, skewDriftIntegrand K d U DU (pushTest z r φ) p = 0 at h0
  change ∫ p in openCyl 0 1, skewDriftIntegrand (rsK K z r) (rsd d z r) (rsU U z r)
    (rsDU DU z r) φ p = 0
  -- the original integrand vanishes off `Q_r(z)`
  have hvan : ∀ q ∈ openCyl 0 1 \ openCyl z r,
      skewDriftIntegrand K d U DU (pushTest z r φ) q = 0 := by
    intro q hq
    have hq' : q ∉ tsupport (pushTest z r φ) := fun h => hq.2 (htest.2.2 h)
    have hfd : fderiv ℝ (pushTest z r φ) q = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hq'
    have hval : pushTest z r φ q = 0 := image_eq_zero_of_notMem_tsupport hq'
    have hgrad : stSpaceGrad (pushTest z r φ) q = 0 := by
      funext i; simp [stSpaceGrad, hfd]
    simp [skewDriftIntegrand, stTimeDeriv, hfd, hval, hgrad, vecDot]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (openCyl_measurable 0 1) hsub hvan] at h0
  rw [show (∫ p in openCyl 0 1, skewDriftIntegrand (rsK K z r) (rsd d z r) (rsU U z r)
      (rsDU DU z r) φ p) = ∫ p in openCyl 0 1,
        r ^ 2 * skewDriftIntegrand K d U DU (pushTest z r φ) (parDil z r p) from
      setIntegral_congr_fun (openCyl_measurable 0 1)
        fun p _ => skewDriftIntegrand_rescale hr K d U DU hφ.1 p]
  rw [integral_const_mul, integral_parDil z hr0, image_parDil_openCyl z hr, mul_one, h0]
  ring

theorem rescale_divFree (hr : 0 < r) (hsub : openCyl z r ⊆ openCyl 0 1)
    {d : ℝ × Vec 2 → Vec 2} (hdiv : IsDivFreeQ1 d) : IsDivFreeQ1 (rsd d z r) := by
  have hr0 : r ≠ 0 := hr.ne'
  obtain ⟨htime, hspace⟩ := openCyl_subset_split hr hsub
  have himg : (fun τ : ℝ => z.1 + r ^ 2 * τ) '' Set.Ioo (-1) 0 = Set.Ioo (z.1 - r ^ 2) z.1 := by
    rw [image_timeDil_Ioo z.1 (by positivity : (0 : ℝ) < r ^ 2)]
    congr 1 <;> ring
  have h1 : ∀ᵐ t ∂(volume.restrict ((fun τ : ℝ => z.1 + r ^ 2 * τ) '' Set.Ioo (-1) 0)),
      ∀ ψ : Vec 2 → ℝ, IsSpTest (euclidBall 0 1) ψ →
        ∫ y in euclidBall 0 1, vecDot (d (t, y)) (spGrad ψ y) = 0 := by
    rw [himg]
    exact ae_restrict_of_ae_restrict_of_subset htime hdiv
  filter_upwards [ae_restrict_timeDil z.1 (by positivity : (0 : ℝ) < r ^ 2) h1] with τ hτ
  intro ψ hψ
  have htest : IsSpTest (euclidBall z.2 (r * 1)) (pushSp z.2 r ψ) := isSpTest_pushSp z.2 hr hψ
  rw [mul_one] at htest
  have h0 := hτ (pushSp z.2 r ψ) ⟨htest.1, htest.2.1, htest.2.2.trans hspace⟩
  have hvan : ∀ x ∈ euclidBall 0 1 \ euclidBall z.2 r,
      vecDot (d (z.1 + r ^ 2 * τ, x)) (spGrad (pushSp z.2 r ψ) x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport (pushSp z.2 r ψ) := fun h => hx.2 (htest.2.2 h)
    have hfd : fderiv ℝ (pushSp z.2 r ψ) x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx'
    have hgrad : spGrad (pushSp z.2 r ψ) x = 0 := by
      funext i; simp [spGrad, hfd]
    simp [hgrad, vecDot]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (External.Campanato.euclidBall_measurable 0 1) hspace hvan] at h0
  have hcv : ∫ y in euclidBall 0 1, vecDot (rsd d z r (τ, y)) (spGrad ψ y) =
      r ^ 2 * ((r ^ 2)⁻¹ * ∫ x in spDil z.2 r '' euclidBall 0 1,
        vecDot (d (z.1 + r ^ 2 * τ, x)) (spGrad (pushSp z.2 r ψ) x)) := by
    rw [← integral_spDil z.2 hr0, ← integral_const_mul]
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable 0 1) fun y _ => ?_
    simp only [rsd, parDil, spGrad_pushSp z.2 hr0 hψ.1, vecDot_smul_left, vecDot_smul_right]
    change r * vecDot (d (z.1 + r ^ 2 * τ, spDil z.2 r y)) (spGrad ψ y) = _
    field_simp
  rw [hcv, image_spDil_euclidBall z.2 hr, mul_one, h0]
  ring
end

end AVRegularity.Applications
end
