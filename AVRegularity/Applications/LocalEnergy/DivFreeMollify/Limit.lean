-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Slice
import Mathlib.MeasureTheory.Function.L2Space

public section
noncomputable section

section
open MeasureTheory Homogenization Filter Topology
open scoped Convolution ENNReal Pointwise
namespace AVRegularity.Applications.LocalEnergy.Moll

/-! # Smooth approximation of compactly supported `H¹` functions

If `ψ ∈ L²(B)` has weak gradient `Dψ ∈ L²(B)` and vanishes outside a compact `Kc ⊆ B`, then the
mollifications `ρ_ε ⋆ ψ` are in `C^∞_c(B)` for small `ε`, converge to `ψ` in `L²`, and their
gradients `ρ_ε ⋆ (1_{Kc} Dψ)` converge to `Dψ` in `L²`. -/

variable {B : Set (Vec 2)}

/-- The weak gradient of a function vanishing outside `Kc` vanishes a.e. on `B \ Kc`. -/
theorem weakGrad_ae_zero_off (hB : IsOpen B) {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hw : HasWeakGradientOn B ψ Dψ)
    (hloc : ∀ i, LocallyIntegrableOn (fun y => Dψ y i) B volume) {Kc : Set (Vec 2)}
    (hKc : IsCompact Kc) (hz : ∀ y, y ∉ Kc → ψ y = 0) (i : Fin 2) :
    ∀ᵐ y ∂volume, y ∈ B → y ∉ Kc → Dψ y i = 0 := by
  have hO : IsOpen (B \ Kc) := hB.sdiff hKc.isClosed
  have h := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun y => Dψ y i) ((hloc i).mono_set Set.sdiff_subset) ?_
  · filter_upwards [h] with y hy hyB hyK using hy ⟨hyB, hyK⟩
  · intro φ hφ hφc hφs
    have hφB : tsupport φ ⊆ B := hφs.trans Set.sdiff_subset
    have h1 := hw i φ hφ hφc hφB
    have h2 : ∫ x in B, ψ x * (fderiv ℝ φ x) (basisVec i) = 0 := by
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
      by_cases hy : y ∈ tsupport φ
      · rw [hz y (hφs hy).2, zero_mul]
      · rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]; simp
    rw [h2] at h1
    have h3 : ∫ x in B, Dψ x i * φ x = 0 := by linarith
    have h4 : ∫ x, φ x • Dψ x i = ∫ x in B, Dψ x i * φ x := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp [smul_eq_mul, mul_comm]
      · intro y hy
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφB h)), mul_zero]
    rw [h4, h3]

/-- A mollification vanishes away from the thickened support. -/
theorem mollify_eq_zero_of_notMem {b : Vec 2 → ℝ} {A : Set (Vec 2)} (hbA : ∀ y, y ∉ A → b y = 0)
    {ε : ℝ} (hε : 0 < ε) {x : Vec 2} (hx : x ∉ Metric.closedBall (0 : Vec 2) ε + A) :
    mollify b ε hε x = 0 := by
  have hsub : Function.support (mollify b ε hε) ⊆ Metric.closedBall (0 : Vec 2) ε + A := by
    calc Function.support (mollify b ε hε)
        ⊆ Function.support (mollifier (d := 2) ε hε) + Function.support b := by
          simpa [mollify] using
            (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
              (f := mollifier (d := 2) ε hε) (g := b))
      _ ⊆ Metric.closedBall (0 : Vec 2) ε + A := by
          refine Set.add_subset_add ((subset_tsupport _).trans ?_) ?_
          · rw [mollifier_tsupp_eq_closedBall hε]
          · intro y hy
            by_contra hyA
            exact hy (hbA y hyA)
  by_contra h
  exact hx (hsub h)


/-- Extension by zero outside `Kc` of the gradient component. -/
def gradExt (Kc : Set (Vec 2)) (Dψ : Vec 2 → Vec 2) (i : Fin 2) : Vec 2 → ℝ :=
  Kc.indicator (fun y => Dψ y i)

theorem memLp_ext_of_memLp {Kc : Set (Vec 2)} (hKc : IsCompact Kc) (hKB : Kc ⊆ B)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict B)) :
    MemLp (Kc.indicator f) 2 volume := by
  refine (memLp_indicator_iff_restrict hKc.measurableSet).2 ?_
  exact hf.mono_measure (Measure.restrict_mono hKB le_rfl)

theorem hasWeakPartialDerivOn_gradExt (hB : IsOpen B) {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hw : HasWeakGradientOn B ψ Dψ)
    (hloc : ∀ i, LocallyIntegrableOn (fun y => Dψ y i) B volume) {Kc : Set (Vec 2)}
    (hKc : IsCompact Kc) (hz : ∀ y, y ∉ Kc → ψ y = 0) (i : Fin 2) :
    HasWeakPartialDerivOn B i ψ (gradExt Kc Dψ i) := by
  intro φ hφ hφc hφB
  rw [hw i φ hφ hφc hφB]
  congr 1
  have hae := weakGrad_ae_zero_off hB hw hloc hKc hz i
  refine setIntegral_congr_ae hB.measurableSet ?_
  filter_upwards [hae] with y hy hyB
  by_cases hyK : y ∈ Kc
  · simp [gradExt, hyK]
  · simp [gradExt, hyK, hy hyB hyK]

theorem fderiv_mollify_gradExt {Kc : Set (Vec 2)} (hB : IsOpen B) {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hw : HasWeakGradientOn B ψ Dψ)
    (hloc : ∀ i, LocallyIntegrableOn (fun y => Dψ y i) B volume)
    (hψ : LocallyIntegrable ψ volume)
    (hG : ∀ i, LocallyIntegrable (gradExt Kc Dψ i) volume)
    (hKc : IsCompact Kc) (hz : ∀ y, y ∉ Kc → ψ y = 0)
    {δ ε : ℝ} (hδ : Metric.cthickening δ Kc ⊆ B) (hε : 0 < ε) (hεδ : 2 * ε ≤ δ)
    (i : Fin 2) (x : Vec 2) :
    (fderiv ℝ (mollify ψ ε hε) x) (basisVec i) = mollify (gradExt Kc Dψ i) ε hε x := by
  by_cases hx : x ∈ Metric.closedBall (0 : Vec 2) ε + Kc
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    refine fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn hB hψ (hG i)
      (hasWeakPartialDerivOn_gradExt hB hw hloc hKc hz i) hε ?_
    intro y hy
    apply hδ
    refine Metric.mem_cthickening_of_dist_le y k δ Kc hk ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    rw [dist_eq_norm]
    calc ‖y - k‖ = ‖(y - (t + k)) + t‖ := by congr 1; abel
      _ ≤ ‖y - (t + k)‖ + ‖t‖ := norm_add_le _ _
      _ ≤ ε + ε := add_le_add hy ht
      _ ≤ δ := by linarith
  · have hzero : ∀ x', x' ∉ Metric.closedBall (0 : Vec 2) ε + Kc → mollify ψ ε hε x' = 0 :=
      fun x' hx' => mollify_eq_zero_of_notMem hz hε hx'
    have hclosed : IsClosed (Metric.closedBall (0 : Vec 2) ε + Kc) :=
      (isCompact_closedBall (0 : Vec 2) ε |>.add hKc).isClosed
    have hts : tsupport (mollify ψ ε hε) ⊆ Metric.closedBall (0 : Vec 2) ε + Kc := by
      refine closure_minimal (fun y hy => ?_) hclosed
      by_contra hy'
      exact hy (hzero y hy')
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hts h)), mollify_eq_zero_of_notMem
      (fun y hy => by simp [gradExt, hy]) hε hx]
    simp


theorem setIntegral_sq_le_eLpNorm {F : Vec 2 → ℝ} (hF : MemLp F 2 volume) (S : Set (Vec 2)) :
    ∫ y in S, F y ^ 2 ≤ (eLpNorm F 2 volume).toReal ^ 2 := by
  have h := hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ a, ‖F a‖ ^ (2 : ENNReal).toReal := integral_nonneg fun a => by positivity
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h hnn
  have hI : (eLpNorm F 2 volume).toReal ^ 2 = ∫ a, F a ^ 2 := by
    rw [h, ENNReal.toReal_ofReal (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  rw [hI]
  have hint : Integrable (fun y => F y ^ 2) volume := hF.integrable_sq
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun y => sq_nonneg _)

theorem tendsto_setIntegral_sq {f : ℕ → Vec 2 → ℝ} {g : Vec 2 → ℝ} (S : Set (Vec 2))
    (hf : ∀ n, MemLp (fun x => f n x - g x) 2 volume)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y in S, (f n y - g y) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (eLpNorm (fun x => f n x - g x) 2 volume).toReal ^ 2) atTop
      (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).pow 2
    simpa using this
  refine squeeze_zero (fun n => setIntegral_nonneg_of_ae_restrict ?_) (fun n => ?_) h1
  · exact Filter.Eventually.of_forall fun y => sq_nonneg _
  · exact setIntegral_sq_le_eLpNorm (hf n) S


theorem locallyIntegrableOn_of_memLp (hB : IsOpen B) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict B)) : LocallyIntegrableOn f B volume := by
  intro x hx
  obtain ⟨K, hK, hxK, hKB⟩ := exists_compact_subset hB hx
  rw [hB.nhdsWithin_eq hx]
  refine ⟨K, mem_interior_iff_mem_nhds.mp hxK, ?_⟩
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (hf.mono_measure (Measure.restrict_mono hKB le_rfl)).integrable (by norm_num)

theorem memLp_mollify {g : Vec 2 → ℝ} (hg : MemLp g 2 volume) {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollify g ε hε) 2 volume := by
  have hle : eLpNorm (mollify g ε hε) 2 volume ≤ eLpNorm g 2 volume :=
    young_convolution_nonneg_integral_one_of_aemeasurable (p := 2) (by norm_num) (by norm_num)
      (mollifier_nonneg hε) (integrable_of_integral_eq_one (mollifier_integral_one hε))
      (mollifier_integral_one hε)
      (mollifier_contDiff (d := 2) hε (n := 0)).continuous.measurable
      hg.aestronglyMeasurable.aemeasurable
  exact lt_of_le_of_lt hle hg.eLpNorm_lt_top

/-- Smooth `L²`-approximation of a compactly supported `H¹` function. -/
theorem exists_smooth_approx (hB : IsOpen B) {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hψ : MemLp ψ 2 (volume.restrict B))
    (hD : ∀ i, MemLp (fun y => Dψ y i) 2 (volume.restrict B))
    (hw : HasWeakGradientOn B ψ Dψ) {Kc : Set (Vec 2)} (hKc : IsCompact Kc) (hKB : Kc ⊆ B)
    (hz : ∀ y, y ∉ Kc → ψ y = 0) :
    ∃ ψn : ℕ → Vec 2 → ℝ, (∀ n, IsSpTest B (ψn n)) ∧
      Tendsto (fun n => ∫ y in B, (ψn n y - ψ y) ^ 2) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => ∫ y in B, (spGrad (ψn n) y i - Dψ y i) ^ 2) atTop (𝓝 0) := by
  obtain ⟨δ, hδ0, hδB⟩ := hKc.exists_cthickening_subset_open hB hKB
  let ε : ℕ → ℝ := fun n => δ / 2 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hε2 : ∀ n, 2 * ε n ≤ δ := fun n => by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have : ε n ≤ δ / 2 := div_le_self (by positivity) h1
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 2)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [ε]
    ring
  have hψ_eq : Kc.indicator ψ = ψ := by
    funext y
    by_cases hy : y ∈ Kc
    · simp [hy]
    · simp [hy, hz y hy]
  have hψg : MemLp ψ 2 volume := hψ_eq ▸ memLp_ext_of_memLp hKc hKB hψ
  have hGg : ∀ i, MemLp (gradExt Kc Dψ i) 2 volume := fun i =>
    memLp_ext_of_memLp hKc hKB (hD i)
  have hloc : ∀ i, LocallyIntegrableOn (fun y => Dψ y i) B volume := fun i =>
    locallyIntegrableOn_of_memLp hB (hD i)
  have hψloc : LocallyIntegrable ψ volume := hψg.locallyIntegrable (by norm_num)
  have hGloc : ∀ i, LocallyIntegrable (gradExt Kc Dψ i) volume := fun i =>
    (hGg i).locallyIntegrable (by norm_num)
  have hS : ∀ n, Metric.closedBall (0 : Vec 2) (ε n) + Kc ⊆ B := by
    intro n y hy
    obtain ⟨t, ht, k, hk, rfl⟩ := hy
    apply hδB
    refine Metric.mem_cthickening_of_dist_le _ k δ Kc hk ?_
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    rw [dist_eq_norm]
    have : t + k - k = t := by abel
    rw [this]
    linarith [hε2 n]
  have hScpt : ∀ n, IsCompact (Metric.closedBall (0 : Vec 2) (ε n) + Kc) := fun n =>
    (isCompact_closedBall (0 : Vec 2) (ε n)).add hKc
  have hzero : ∀ n x, x ∉ Metric.closedBall (0 : Vec 2) (ε n) + Kc →
      mollify ψ (ε n) (hεpos n) x = 0 := fun n x hx =>
    mollify_eq_zero_of_notMem hz (hεpos n) hx
  have hts : ∀ n, tsupport (mollify ψ (ε n) (hεpos n)) ⊆
      Metric.closedBall (0 : Vec 2) (ε n) + Kc := by
    intro n
    refine closure_minimal (fun y hy => ?_) (hScpt n).isClosed
    by_contra hy'
    exact hy (hzero n y hy')
  refine ⟨fun n => mollify ψ (ε n) (hεpos n), fun n => ⟨?_, ?_, (hts n).trans (hS n)⟩, ?_, ?_⟩
  · exact mollify_contDiff (hεpos n) hψloc
  · exact HasCompactSupport.intro (hScpt n) (fun x hx => hzero n x hx)
  · have hlim := tendsto_eLpNorm_sub_zero_mollify (p := 2) (by norm_num) (by norm_num) hψg
      hεlim hεpos
    exact tendsto_setIntegral_sq B (fun n => (memLp_mollify hψg (hεpos n)).sub hψg) hlim
  · intro i
    have hlim := tendsto_eLpNorm_sub_zero_mollify (p := 2) (by norm_num) (by norm_num) (hGg i)
      hεlim hεpos
    have h1 := tendsto_setIntegral_sq (f := fun n => mollify (gradExt Kc Dψ i) (ε n) (hεpos n))
      (g := gradExt Kc Dψ i) B (fun n => (memLp_mollify (hGg i) (hεpos n)).sub (hGg i)) hlim
    have hae := weakGrad_ae_zero_off hB hw hloc hKc hz i
    refine h1.congr fun n => ?_
    refine setIntegral_congr_ae hB.measurableSet ?_
    filter_upwards [hae] with y hy hyB
    have hgrad : spGrad (mollify ψ (ε n) (hεpos n)) y i =
        mollify (gradExt Kc Dψ i) (ε n) (hεpos n) y :=
      fderiv_mollify_gradExt hB hw hloc hψloc hGloc hKc hz hδB (hεpos n) (hε2 n) i y
    have hD' : gradExt Kc Dψ i y = Dψ y i := by
      by_cases hyK : y ∈ Kc
      · simp [gradExt, hyK]
      · simp [gradExt, hyK, hy hyB hyK]
    simp only [hgrad, hD']

end AVRegularity.Applications.LocalEnergy.Moll
end

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.LocalEnergy.Moll

/-! # A bounded divergence-free field annihilates `∇ψ` and `ψ ∇ψ` for compactly supported `H¹`

Slice-level statement: if a bounded field `d` satisfies `∫_B d·∇ψ₀ = 0` for all smooth compactly
supported `ψ₀`, then the same holds for every `ψ ∈ H¹(B)` vanishing outside a compact subset of `B`
(and `∫ ψ d·∇ψ = 0`). -/

variable {B : Set (Vec 2)}

theorem memLp_fderiv_basis {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (i : Fin 2) : MemLp (fun y => fderiv ℝ f y (basisVec i)) 2 (volume.restrict B) := by
  have hcont : Continuous (fun y => fderiv ℝ f y (basisVec i)) :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcs : HasCompactSupport (fun y => fderiv ℝ f y (basisVec i)) :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  exact hcont.memLp_of_hasCompactSupport hcs

theorem memLp_smooth_cpt {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    MemLp f 2 (volume.restrict B) :=
  hf.continuous.memLp_of_hasCompactSupport hc

theorem abs_coord_le {x : Vec 2} {kd : ℝ} (h : vecNormSq x ≤ kd ^ 2) (i : Fin 2) :
    |x i| ≤ |kd| := by
  have h1 : x i ^ 2 ≤ kd ^ 2 := by
    refine le_trans ?_ h
    fin_cases i <;> simp [vecNormSq, vecDot, Fin.sum_univ_two] <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  exact sq_le_sq.mp h1


theorem integral_mul_vecDot_eq {μ : Measure (Vec 2)} {d g : Vec 2 → Vec 2} {a : Vec 2 → ℝ}
    (h0 : Integrable (fun y => d y 0 * (a y * g y 0)) μ)
    (h1 : Integrable (fun y => d y 1 * (a y * g y 1)) μ) :
    ∫ y, a y * vecDot (d y) (g y) ∂μ =
      ∫ y, d y 0 * (a y * g y 0) ∂μ + ∫ y, d y 1 * (a y * g y 1) ∂μ := by
  rw [← integral_add h0 h1]
  congr 1; ext y
  simp only [vecDot, Fin.sum_univ_two]; ring

/-- Core limit argument, for a general weight sequence `an → a` in `L²`. -/
theorem divFree_slice_core (hBfin : volume B ≠ ⊤) {d : Vec 2 → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => d y i) (volume.restrict B))
    (hbd : ∀ᵐ y ∂(volume.restrict B), vecNormSq (d y) ≤ kd ^ 2)
    {Dψ : Vec 2 → Vec 2} (hD : ∀ i, MemLp (fun y => Dψ y i) 2 (volume.restrict B))
    {ψn : ℕ → Vec 2 → ℝ} (hsp : ∀ n, IsSpTest B (ψn n))
    (hgt : ∀ i, Tendsto (fun n => ∫ y in B, (spGrad (ψn n) y i - Dψ y i) ^ 2) atTop (𝓝 0))
    {an : ℕ → Vec 2 → ℝ} {a : Vec 2 → ℝ} (ha : MemLp a 2 (volume.restrict B))
    (han : ∀ n, MemLp (an n) 2 (volume.restrict B))
    (hta : Tendsto (fun n => ∫ y in B, (an n y - a y) ^ 2) atTop (𝓝 0))
    (hzero : ∀ n, ∫ y in B, an n y * vecDot (d y) (spGrad (ψn n) y) = 0) :
    ∫ y in B, a y * vecDot (d y) (Dψ y) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBfin⟩
  have hM : ∀ i, ∀ᵐ y ∂(volume.restrict B), |d y i| ≤ |kd| := fun i => by
    filter_upwards [hbd] with y hy using abs_coord_le hy i
  have hg : ∀ n i, MemLp (fun y => spGrad (ψn n) y i) 2 (volume.restrict B) := fun n i =>
    memLp_fderiv_basis (hsp n).1 (hsp n).2.1 i
  have hlim : ∀ i : Fin 2, Tendsto (fun n => ∫ y in B, d y i * (an n y * spGrad (ψn n) y i))
      atTop (𝓝 (∫ y in B, d y i * (a y * Dψ y i))) := fun i =>
    tendsto_integral_mul_mul (abs_nonneg kd) (hdm i) (hM i) ha (hD i) han (fun n => hg n i) hta
      (hgt i)
  have hint : ∀ n i, Integrable (fun y => d y i * (an n y * spGrad (ψn n) y i))
      (volume.restrict B) := fun n i =>
    integrable_weight_mul_mul (han n) (hg n i) (hdm i) (hM i)
  have hint' : ∀ i, Integrable (fun y => d y i * (a y * Dψ y i)) (volume.restrict B) := fun i =>
    integrable_weight_mul_mul ha (hD i) (hdm i) (hM i)
  have hsum : Tendsto (fun n => ∫ y in B, an n y * vecDot (d y) (spGrad (ψn n) y)) atTop
      (𝓝 ((∫ y in B, d y 0 * (a y * Dψ y 0)) + ∫ y in B, d y 1 * (a y * Dψ y 1))) := by
    refine ((hlim 0).add (hlim 1)).congr fun n => ?_
    rw [integral_mul_vecDot_eq (hint n 0) (hint n 1)]
  have h0 : Tendsto (fun n => ∫ y in B, an n y * vecDot (d y) (spGrad (ψn n) y)) atTop
      (𝓝 0) := by
    simp [hzero]
  rw [integral_mul_vecDot_eq (hint' 0) (hint' 1)]
  exact tendsto_nhds_unique hsum h0


theorem spGrad_mul_self {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) (i : Fin 2) :
    spGrad (fun z => f z * f z) y i = 2 * f y * spGrad f y i := by
  have hd : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have : fderiv ℝ (fun z => f z * f z) y = f y • fderiv ℝ f y + f y • fderiv ℝ f y :=
    fderiv_mul hd hd
  simp only [spGrad]
  rw [this]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Slice statement: `∫_B d·Dψ = 0`. -/
theorem divFree_slice_grad (hB : IsOpen B) (hBfin : volume B ≠ ⊤) {d : Vec 2 → Vec 2} {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => d y i) (volume.restrict B))
    (hbd : ∀ᵐ y ∂(volume.restrict B), vecNormSq (d y) ≤ kd ^ 2)
    (hdiv : ∀ ψ0, IsSpTest B ψ0 → ∫ y in B, vecDot (d y) (spGrad ψ0 y) = 0)
    {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hψ : MemLp ψ 2 (volume.restrict B))
    (hD : ∀ i, MemLp (fun y => Dψ y i) 2 (volume.restrict B))
    (hw : HasWeakGradientOn B ψ Dψ) {Kc : Set (Vec 2)} (hKc : IsCompact Kc) (hKB : Kc ⊆ B)
    (hz : ∀ y, y ∉ Kc → ψ y = 0) :
    ∫ y in B, vecDot (d y) (Dψ y) = 0 := by
  obtain ⟨ψn, hsp, -, hgt⟩ := exists_smooth_approx hB hψ hD hw hKc hKB hz
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBfin⟩
  have hone : MemLp (fun _ : Vec 2 => (1 : ℝ)) 2 (volume.restrict B) := memLp_const 1
  have := divFree_slice_core hBfin hdm hbd hD hsp hgt (an := fun _ _ => 1) (a := fun _ => 1)
    hone (fun _ => hone) (by simp) (fun n => by simpa using hdiv _ (hsp n))
  simpa using this

/-- Slice statement: `∫_B ψ d·Dψ = 0`. -/
theorem divFree_slice_mul_grad (hB : IsOpen B) (hBfin : volume B ≠ ⊤) {d : Vec 2 → Vec 2}
    {kd : ℝ}
    (hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => d y i) (volume.restrict B))
    (hbd : ∀ᵐ y ∂(volume.restrict B), vecNormSq (d y) ≤ kd ^ 2)
    (hdiv : ∀ ψ0, IsSpTest B ψ0 → ∫ y in B, vecDot (d y) (spGrad ψ0 y) = 0)
    {ψ : Vec 2 → ℝ} {Dψ : Vec 2 → Vec 2}
    (hψ : MemLp ψ 2 (volume.restrict B))
    (hD : ∀ i, MemLp (fun y => Dψ y i) 2 (volume.restrict B))
    (hw : HasWeakGradientOn B ψ Dψ) {Kc : Set (Vec 2)} (hKc : IsCompact Kc) (hKB : Kc ⊆ B)
    (hz : ∀ y, y ∉ Kc → ψ y = 0) :
    ∫ y in B, ψ y * vecDot (d y) (Dψ y) = 0 := by
  obtain ⟨ψn, hsp, hψt, hgt⟩ := exists_smooth_approx hB hψ hD hw hKc hKB hz
  refine divFree_slice_core hBfin hdm hbd hD hsp hgt hψ
    (fun n => memLp_smooth_cpt (hsp n).1 (hsp n).2.1) hψt (fun n => ?_)
  have hsq : IsSpTest B (fun z => ψn n z * ψn n z) :=
    ⟨(hsp n).1.mul (hsp n).1, (hsp n).2.1.mul_right,
      (tsupport_mul_subset_left).trans (hsp n).2.2⟩
  have h := hdiv _ hsq
  have e : ∀ y, vecDot (d y) (spGrad (fun z => ψn n z * ψn n z) y) =
      2 * (ψn n y * vecDot (d y) (spGrad (ψn n) y)) := by
    intro y
    simp only [vecDot, Fin.sum_univ_two, spGrad_mul_self (hsp n).1]
    ring
  simp only [e] at h
  rw [integral_const_mul] at h
  linarith

end AVRegularity.Applications.LocalEnergy.Moll
end
