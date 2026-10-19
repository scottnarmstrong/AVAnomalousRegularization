-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.CompactDiscardOfParts
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Model jets from the leaves

`RetainedModelJetsStatement` from the leaves `CompactChainExistenceStatement` (compact chains),
`CompactDensityStatement` (compact data), `AmplitudePlancherelStatement` (band-limited calculus),
`CompactChainGaussianStatement` (Gaussian amplitude of compact chain data) and
`GaussianPlancherelStatement` (Plancherel with a Gaussian amplitude). On a smooth compactly
supported datum the retained map is the retained cutoff of the endpoint of a base-slot chain
(`CompactChainExistenceStatement`, `IsRetainedMap.chain`), whose amplitudes satisfy the Gaussian
bound (`CompactChainGaussianStatement`); `GaussianPlancherelStatement` turns it into the weighted
jet bound; the transfer of weighted jet bounds from compact data extends the bound to every
measurable datum of finite moment norm. -/

section
universe u v

/-- **Model jets from the leaves.** -/
theorem retainedModelJets_of_leaves (hA3 : CompactChainExistenceStatement.{u, v})
    (hA4 : CompactDensityStatement.{u, v}) (hB0 : AmplitudePlancherelStatement.{v})
    (hB1 : CompactChainGaussianStatement.{u, v}) (hB2 : GaussianPlancherelStatement.{u, v}) :
    RetainedModelJetsStatement.{u, v} := by
  intro K
  have hA3K := (hA3 K).choose_spec
  have hB1K := (hB1 K).choose_spec
  refine ⟨min (hA3 K).choose (hB1 K).choose, lt_min hA3K.1 hB1K.1, ?_⟩
  intro χlo hχ Nw D H m d Ks pos
  have hB1c := hB1K.2 χlo hχ Nw D H m d Ks pos (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) χlo
    hχ.dilate_smooth hχ.dilate_hasCompactSupport hχ.smooth
    (exists_bound_iteratedFDeriv_of_hasCompactSupport hχ.smooth hχ.hasCompactSupport)
    (hχ.eq_dilate_pow_mul _)
  have hB1s := hB1c.choose_spec.choose_spec.choose_spec.choose_spec
  have hB2c := fun M => hB2 m (wordReserveN m Ks) (wordReserveP m Ks) M
    hB1c.choose_spec.choose hB1s.2.1 (fun ξ => χlo ((2 : ℝ)⁻¹ • ξ)) hχ.dilate_smooth
    hχ.dilate_hasCompactSupport
  refine ⟨fun M => (hB2c M).choose * hB1c.choose, hB1c.choose_spec.choose_spec.choose,
    hB1c.choose_spec.choose_spec.choose_spec.choose,
    fun M => mul_pos (hB2c M).choose_spec.1 hB1s.1, hB1s.2.2.1, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ ϖ G v g reg pkg hB hJ hwb X₀ R hR M F
    hFm hFfin
  have hξ : 0 < K.ξlo := pkg.consts_pos.2.1
  have hr : 0 < 2 * K.ξlo * Real.sqrt η := by
    have := Real.sqrt_pos.2 hB.hη
    positivity
  have hKs : (fun i => (letters i).slow) = Ks := funext fun i => (hletters i).2.1
  have hd : (fun i => (letters i).order) = d := funext fun i => (hletters i).1
  have hn : wordReserveN 0 (fun i => (letters i).slow) ≤ wordReserveN m Ks := by
    rw [hKs]
    unfold wordReserveN
    omega
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN 0 fun i => (letters i).slow)
      fun i => (letters i).order) (fun i => (letters i).order) ≤ J := by
    rw [hKs, hd]
    exact (wordReserveJstar_le 0 0 0 m Ks d le_rfl (Nat.zero_le _)).trans hJ
  have hΘ := hB.wordTheta_nonneg
  have hslots := wordBaseSlots_isWordSlots letters hB.hlet
  have hconst : (hB2c M).choose * hB1c.choose * wordTheta ηg letters =
      (hB2c M).choose * (hB1c.choose * wordTheta ηg letters) := by ring
  show _ ≤ ENNReal.ofReal ((hB2c M).choose * hB1c.choose * wordTheta ηg letters) * _
  rw [hconst]
  refine retainedMap_jets_le_of_compact hB0 hA4 hR hr hB.hπ (m : ℝ) M (wordReserveN m Ks) ϖ ϖ⁻¹
    _ hn ?_ F hFm hFfin
  intro φ hφ
  have hlift := fun x => hA4.1 (wordBaseSlots letters 0 x) (φ x) (hφ x).1 (hφ x).2
  choose f hf using hlift
  have hcd : IsCompactDatum f := fun x => ⟨φ x, (hφ x).1, (hφ x).2, hf x⟩
  obtain ⟨u, w, hch⟩ := hA3K.2 H J π letters η S ηg t₀ ϖ G v g reg pkg
    (hB.mono (min_le_left _ _)) hJ0 X₀ f hcd
  have hRφ : R φ = fun x =>
      fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))) := by
    rw [hR.congr φ (fun x => planeValue (f x)) fun x => (hf x).symm]
    exact hR.chain _ hslots f u w hch hcd
  have hb1 := hB1s.2.2.2 J π letters hletters η S ηg t₀ ϖ G v g reg pkg
    (hB.mono (min_le_right _ _)) hJ hwb X₀ (wordBaseSlots letters) hslots φ hφ f u w hf hch
  refine (hB2c M).choose_spec.2 π hB.hπ η ϖ (2 * K.ξlo * Real.sqrt η)
    (hB1c.choose * wordTheta ηg letters) hB.hη hB.ϖ_pos hB.ϖ_le
    (mul_nonneg hB1s.1.le hΘ) (R φ)
    (fun x => retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
    (fun x => retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) φ hφ
    (fun x => by rw [hRφ]; exact hb1.2.1 x) (fun x => hb1.2.2.1 x) (fun x θ hθ => ?_) hb1.2.2.2
  simp only [retainedCosAmplitude, retainedSinAmplitude, retainedCutoff_eq_zero hχ η hθ,
    mul_zero, zero_smul, and_self]
end

/-! # Compactly supported data

Smooth compactly supported functions lift to every carrier (`smoothCompactPlaneHk`) and are dense in
`L²` (a continuous compactly supported approximant, mollified). Approximating `⟨z⟩^{m_k} F` with
the largest available moment order `m_k ≤ k` and dividing by the weight gives one sequence that
converges in every moment norm in which `F` is finite (`compactDensity`). -/

section
universe u v

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Smooth compactly supported functions are dense in `L²`.** -/
theorem exists_smooth_compact_eLpNorm_sub_le {f : Vec 2 → E} (hf : MemLp f 2 volume)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 2 volume ≤ ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨g₀, hg₀c, hg₀, hg₀cont, -⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε2
  set T := Metric.cthickening 1 (tsupport g₀) with hTdef
  have hTc : IsCompact T := hg₀c.isCompact.cthickening
  set V : ℝ≥0∞ := volume T ^ (2 : ℝ≥0∞).toReal⁻¹ with hVdef
  have hVfin : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hTc.measure_lt_top.ne
  -- the uniform tolerance of the mollification
  obtain ⟨η, hη, hηV⟩ : ∃ η : ℝ, 0 < η ∧ V * ENNReal.ofReal η ≤ ε / 2 := by
    by_cases htop : ε / 2 = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top⟩
    · have he : 0 < (ε / 2).toReal := ENNReal.toReal_pos hε2 htop
      have hV0 : 0 ≤ V.toReal := ENNReal.toReal_nonneg
      refine ⟨(ε / 2).toReal / (V.toReal + 1), div_pos he (by positivity), ?_⟩
      calc V * ENNReal.ofReal ((ε / 2).toReal / (V.toReal + 1))
          = ENNReal.ofReal (V.toReal * ((ε / 2).toReal / (V.toReal + 1))) := by
            rw [ENNReal.ofReal_mul hV0, ENNReal.ofReal_toReal hVfin]
        _ ≤ ENNReal.ofReal (ε / 2).toReal := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith
        _ = ε / 2 := ENNReal.ofReal_toReal htop
  obtain ⟨δ, hδ, hδη⟩ := Metric.uniformContinuous_iff.1
    (hg₀c.uniformContinuous_of_continuous hg₀cont) η hη
  let φ : ContDiffBump (0 : Vec 2) :=
    ⟨min (δ / 2) (1 / 2), min δ 1, lt_min (half_pos hδ) (by norm_num),
      min_lt_min (half_lt_self hδ) (by norm_num)⟩
  set g := convolution (φ.normed volume) g₀ (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgdef
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.contDiff_normed hg₀cont.locallyIntegrable
  have hgc : HasCompactSupport g :=
    φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg₀c
  have hrOut : φ.rOut ≤ 1 := min_le_right _ _
  have hclose : ∀ x, dist (g x) (g₀ x) ≤ η := fun x =>
    φ.dist_normed_convolution_le hg₀cont.aestronglyMeasurable fun y hy =>
      (hδη (lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _))).le
  -- outside `T` both functions vanish
  have hout : ∀ x ∉ T, g₀ x - g x = 0 := by
    intro x hx
    have h0 : ∀ y ∈ Metric.ball x φ.rOut, g₀ y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hyT => hx ?_
      refine Metric.mem_cthickening_of_dist_le x y 1 _ hyT ?_
      rw [dist_comm]
      exact (Metric.mem_ball.1 hy).le.trans hrOut
    have hx0 : g₀ x = 0 := h0 x (Metric.mem_ball_self (lt_of_lt_of_le
      (lt_min (half_pos hδ) (by norm_num)) (le_of_lt φ.rIn_lt_rOut)))
    have hgx : dist (g x) (g₀ x) ≤ 0 :=
      φ.dist_normed_convolution_le hg₀cont.aestronglyMeasurable fun y hy => by
        rw [h0 y hy, hx0, dist_self]
    rw [dist_le_zero.1 hgx, sub_self]
  have hsupp : Function.support (g₀ - g) ⊆ T := fun x hx => by
    by_contra hxT
    exact hx (hout x hxT)
  have hmeas : AEStronglyMeasurable (g₀ - g) volume :=
    (hg₀cont.sub hgs.continuous).aestronglyMeasurable
  have hdiff : eLpNorm (g₀ - g) 2 volume ≤ V * ENNReal.ofReal η := by
    rw [← eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
    refine (eLpNorm_le_of_ae_bound (C := η) hmeas.restrict
      (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Pi.sub_apply, ← dist_eq_norm, dist_comm]
      exact hclose x
    · rw [Measure.restrict_apply_univ]
  refine ⟨g, hgs, hgc, ?_⟩
  calc eLpNorm (f - g) 2 volume = eLpNorm ((f - g₀) + (g₀ - g)) 2 volume := by
        rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (f - g₀) 2 volume + eLpNorm (g₀ - g) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ ε / 2 + ε / 2 := add_le_add hg₀ (hdiff.trans hηV)
    _ = ε := ENNReal.add_halves ε

end Smooth

section Weights

/-- The bracket `⟨z⟩ = (1 + |z|²)^{1/2}`. -/
noncomputable def jbracket (z : Vec 2) : ℝ := Real.sqrt (1 + (z 0 ^ 2 + z 1 ^ 2))

theorem one_le_jbracket (z : Vec 2) : 1 ≤ jbracket z := by
  unfold jbracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)])

theorem jbracket_pos (z : Vec 2) : 0 < jbracket z := lt_of_lt_of_le one_pos (one_le_jbracket z)

theorem abs_coord_le_jbracket (z : Vec 2) (i : Fin 2) : |z i| ≤ jbracket z := by
  unfold jbracket
  refine Real.abs_le_sqrt ?_
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]

theorem jbracket_le (z : Vec 2) : jbracket z ≤ 1 + |z 0| + |z 1| := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (z 0), abs_nonneg (z 1), sq_abs (z 0), sq_abs (z 1),
    mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

theorem jbracket_contDiff : ContDiff ℝ (⊤ : ℕ∞) jbracket := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) fun z : Vec 2 => 1 + (z 0 ^ 2 + z 1 ^ 2) := by fun_prop
  exact hb.sqrt fun z => (by positivity : (0 : ℝ) < 1 + (z 0 ^ 2 + z 1 ^ 2)).ne'

theorem jbracket_inv_pow_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (jbracket z ^ n)⁻¹ :=
  (jbracket_contDiff.pow n).inv fun z => pow_ne_zero n (jbracket_pos z).ne'

/-- A moment monomial is bounded by the bracket power (`⟨z⟩^0 = 1` when `s = 0`). -/
theorem abs_moment_le (s : ℝ) {n : ℕ} {β : ℕ × ℕ} (hβ : β ∈ momentIndices n) (z : Vec 2) :
    |(s * z 0) ^ β.1 * (s * z 1) ^ β.2| ≤
      max 1 |s| ^ n * jbracket z ^ (if s = 0 then 0 else n) := by
  have hβn : β.1 + β.2 ≤ n := by
    simp only [momentIndices, Finset.mem_filter] at hβ
    exact hβ.2
  have hM : 0 ≤ max 1 |s| ^ n := by positivity
  by_cases hs : s = 0
  · subst hs
    rcases Nat.eq_zero_or_pos β.1 with h1 | h1 <;> rcases Nat.eq_zero_or_pos β.2 with h2 | h2
    · simp [h1, h2]
    · simp [zero_pow h2.ne']
    · simp [zero_pow h1.ne']
    · simp [zero_pow h1.ne']
  · simp only [hs, ↓reduceIte]
    rw [abs_mul, abs_pow, abs_pow, abs_mul, abs_mul, mul_pow, mul_pow]
    have h0 := abs_coord_le_jbracket z 0
    have h1 := abs_coord_le_jbracket z 1
    have hj := one_le_jbracket z
    calc |s| ^ β.1 * |z 0| ^ β.1 * (|s| ^ β.2 * |z 1| ^ β.2)
        = |s| ^ (β.1 + β.2) * (|z 0| ^ β.1 * |z 1| ^ β.2) := by ring
      _ ≤ max 1 |s| ^ (β.1 + β.2) * (jbracket z ^ β.1 * jbracket z ^ β.2) := by
          gcongr
          exact le_max_right _ _
      _ = max 1 |s| ^ (β.1 + β.2) * jbracket z ^ (β.1 + β.2) := by ring
      _ ≤ max 1 |s| ^ n * jbracket z ^ n := by
          gcongr
          exact le_max_left _ _

end Weights

section Moments

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- A finite moment norm makes every moment term of a component of positive mass finite. -/
theorem momentNorm_term_lt_top {π : ι → ℝ} {n : ℕ} {s : ℝ} {F : ∀ v, Vec 2 → h v}
    (hF : momentNorm π n s F < ⊤) {β : ℕ × ℕ} (hβ : β ∈ momentIndices n) {v : ι}
    (hv : 0 < π v) :
    eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume < ⊤ := by
  unfold momentNorm at hF
  set T : ℝ≥0∞ := ∑ v, ENNReal.ofReal ((π v)⁻¹) *
    eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume ^ 2 with hT
  have h1 : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) * T ^ (1 / 2 : ℝ) < ⊤ :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun β : ℕ × ℕ =>
      ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume ^ 2) ^
            (1 / 2 : ℝ)) (fun _ _ => zero_le) hβ) hF
  have hc : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have h2 : T ^ (1 / 2 : ℝ) < ⊤ := (ENNReal.mul_lt_top_iff.1 h1).elim (fun h => h.2)
    (fun h => h.elim (fun h => absurd h hc) fun h => h ▸ ENNReal.zero_lt_top)
  have h3 : T < ⊤ := by
    by_contra hT'
    rw [not_lt, top_le_iff] at hT'
    rw [hT', ENNReal.top_rpow_of_pos (by norm_num)] at h2
    exact lt_irrefl _ h2
  have h4 : ENNReal.ofReal ((π v)⁻¹) *
      eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume ^ 2 < ⊤ :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun v => ENNReal.ofReal ((π v)⁻¹) *
      eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F v z) 2 volume ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ v)) h3
  have hpv : ENNReal.ofReal ((π v)⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hv
  have h5 := (ENNReal.mul_lt_top_iff.1 h4).elim (fun h => h.2)
    (fun h => h.elim (fun h => absurd h hpv) fun h => h ▸ ENNReal.zero_lt_top)
  exact ENNReal.pow_lt_top_iff.1 h5 |>.elim (fun h => h) fun h => absurd h two_ne_zero

theorem one_add_add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (1 + a + b) ^ n ≤ 3 ^ n * (1 + a ^ n + b ^ n) := by
  set M := max 1 (max a b) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMa : a ≤ M := (le_max_left a b).trans (le_max_right _ _)
  have hMb : b ≤ M := (le_max_right a b).trans (le_max_right _ _)
  have hsum : 1 + a + b ≤ 3 * M := by linarith
  have hMn : M ^ n ≤ 1 + a ^ n + b ^ n := by
    have han : 0 ≤ a ^ n := pow_nonneg ha n
    have hbn : 0 ≤ b ^ n := pow_nonneg hb n
    rcases le_total a b with hab | hab
    · rcases le_total 1 b with h1 | h1
      · have : M = b := by rw [hM, max_eq_right hab, max_eq_right h1]
        rw [this]; linarith
      · have : M = 1 := by rw [hM, max_eq_right hab, max_eq_left h1]
        rw [this, one_pow]; linarith
    · rcases le_total 1 a with h1 | h1
      · have : M = a := by rw [hM, max_eq_left hab, max_eq_right h1]
        rw [this]; linarith
      · have : M = 1 := by rw [hM, max_eq_left hab, max_eq_left h1]
        rw [this, one_pow]; linarith
  calc (1 + a + b) ^ n ≤ (3 * M) ^ n := pow_le_pow_left₀ (by positivity) hsum n
    _ = 3 ^ n * M ^ n := mul_pow _ _ _
    _ ≤ 3 ^ n * (1 + a ^ n + b ^ n) := by gcongr

/-- With `s ≠ 0`, a finite moment norm puts `⟨z⟩^n F_v` in `L²` (`n` replaced by `0` when
`s = 0`). -/
theorem memLp_bracket_of_momentNorm {π : ι → ℝ} {n : ℕ} {s : ℝ} {F : ∀ v, Vec 2 → h v}
    (hF : momentNorm π n s F < ⊤) {v : ι} (hv : 0 < π v)
    (hFm : AEStronglyMeasurable (F v) volume) :
    MemLp (fun z => jbracket z ^ (if s = 0 then 0 else n) • F v z) 2 volume := by
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ momentIndices n := by
    simp [momentIndices]
  have hF0 : MemLp (F v) 2 volume := by
    have := momentNorm_term_lt_top hF h00 hv
    rw [memLp_iff]
    simpa using this
  by_cases hs : s = 0
  · simp only [hs, ↓reduceIte, pow_zero, one_smul]
    exact hF0
  · simp only [hs, ↓reduceIte]
    have hn0 : (n, (0 : ℕ)) ∈ momentIndices n := by simp [momentIndices]
    have h0n : ((0 : ℕ), n) ∈ momentIndices n := by simp [momentIndices]
    have hX : MemLp (fun z => (s * z 0) ^ n • F v z) 2 volume := by
      have := momentNorm_term_lt_top hF hn0 hv
      rw [memLp_iff]
      simpa using this
    have hY : MemLp (fun z => (s * z 1) ^ n • F v z) 2 volume := by
      have := momentNorm_term_lt_top hF h0n hv
      rw [memLp_iff]
      simpa using this
    set c := |s|⁻¹ ^ n with hc
    have hmaj : MemLp (fun z => 3 ^ n * (‖F v z‖ + c * ‖(s * z 0) ^ n • F v z‖ +
        c * ‖(s * z 1) ^ n • F v z‖)) 2 volume :=
      ((hF0.norm.add (hX.norm.const_mul c)).add (hY.norm.const_mul c)).const_mul _
    refine hmaj.of_le ((jbracket_contDiff.pow n).continuous.aestronglyMeasurable.smul hFm)
      (Eventually.of_forall fun z => ?_)
    have hsa : 0 < |s| := abs_pos.2 hs
    have hz0 : |z 0| ^ n * ‖F v z‖ = c * ‖(s * z 0) ^ n • F v z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul, mul_pow, hc, inv_pow, ← mul_assoc,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hsa.ne'), one_mul]
    have hz1 : |z 1| ^ n * ‖F v z‖ = c * ‖(s * z 1) ^ n • F v z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul, mul_pow, hc, inv_pow, ← mul_assoc,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hsa.ne'), one_mul]
    have hj := (pow_le_pow_left₀ (jbracket_pos z).le (jbracket_le z) n).trans
      (one_add_add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) n)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (jbracket_pos z).le n),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc jbracket z ^ n * ‖F v z‖ ≤ 3 ^ n * (1 + |z 0| ^ n + |z 1| ^ n) * ‖F v z‖ :=
          mul_le_mul_of_nonneg_right hj (norm_nonneg _)
      _ = 3 ^ n * (‖F v z‖ + |z 0| ^ n * ‖F v z‖ + |z 1| ^ n * ‖F v z‖) := by ring
      _ = _ := by rw [hz0, hz1]

/-- The moment norm is bounded by the bracket-weighted `L²` norm. -/
theorem momentNorm_le_bracket (π : ι → ℝ) (n : ℕ) (s : ℝ) (G : ∀ v, Vec 2 → h v)
    (hG : ∀ v, AEStronglyMeasurable (G v) volume) :
    momentNorm π n s G ≤ ENNReal.ofReal ((momentIndices n).card * max 1 |s| ^ n) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => jbracket z ^ (if s = 0 then 0 else n) • G v z) 2 volume ^ 2) ^
          (1 / 2 : ℝ) := by
  set M := max 1 |s| ^ n with hM
  have hM0 : 0 ≤ M := by positivity
  set T := ∑ v, ENNReal.ofReal ((π v)⁻¹) *
    eLpNorm (fun z => jbracket z ^ (if s = 0 then 0 else n) • G v z) 2 volume ^ 2 with hT
  have hterm : ∀ β ∈ momentIndices n,
      ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ^
            (1 / 2 : ℝ) ≤ ENNReal.ofReal M * T ^ (1 / 2 : ℝ) := by
    intro β hβ
    have hc1 : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      have h1 : 1 ≤ β.1.factorial * β.2.factorial :=
        Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      exact inv_le_one_of_one_le₀ (by exact_mod_cast h1)
    have he : ∀ v, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ≤
        ENNReal.ofReal M *
          eLpNorm (fun z => jbracket z ^ (if s = 0 then 0 else n) • G v z) 2 volume := by
      intro v
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((by fun_prop : Continuous fun z : Vec 2 => (s * z 0) ^ β.1 * (s * z 1) ^ β.2)
          |>.aestronglyMeasurable.smul (hG v)) (Eventually.of_forall fun z => ?_) 2
      show ‖((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z‖ ≤ _
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (jbracket_pos z).le _), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (abs_moment_le s hβ z) (norm_nonneg _)
    have hsum : (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ≤
        ENNReal.ofReal M ^ 2 * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [mul_left_comm, ← mul_pow]
      gcongr
      exact he v
    calc ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((π v)⁻¹) *
            eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ^
              (1 / 2 : ℝ)
        ≤ 1 * (ENNReal.ofReal M ^ 2 * T) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal M * T ^ (1 / 2 : ℝ) := by
          rw [one_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_mul]
          norm_num
  unfold momentNorm
  calc ∑ β ∈ momentIndices n, ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ^
            (1 / 2 : ℝ)
      ≤ ∑ _β ∈ momentIndices n, ENNReal.ofReal M * T ^ (1 / 2 : ℝ) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((momentIndices n).card * M) * T ^ (1 / 2 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]

end Moments

section Approx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One smooth compactly supported sequence approximating `f` in every weighted space
`⟨z⟩^{-N} L²` containing it, with error `1/(k+1)` from `k = N` on. -/
theorem exists_bracket_approx {f : Vec 2 → E} (hf : AEStronglyMeasurable f volume) :
    ∃ ψ : ℕ → Vec 2 → E, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) ∧ HasCompactSupport (ψ k)) ∧
      ∀ N, MemLp (fun z => jbracket z ^ N • f z) 2 volume → ∀ k, N ≤ k →
        eLpNorm (fun z => jbracket z ^ N • (f z - ψ k z)) 2 volume ≤
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  classical
  have hk : ∀ k : ℕ, ∃ ψk : Vec 2 → E, (ContDiff ℝ (⊤ : ℕ∞) ψk ∧ HasCompactSupport ψk) ∧
      ∀ N, MemLp (fun z => jbracket z ^ N • f z) 2 volume → N ≤ k →
        eLpNorm (fun z => jbracket z ^ N • (f z - ψk z)) 2 volume ≤
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    by_cases hex : ∃ N ≤ k, MemLp (fun z => jbracket z ^ N • f z) 2 volume
    · obtain ⟨N₀, hN₀k, hN₀⟩ := hex
      set m := Nat.findGreatest (fun N => MemLp (fun z => jbracket z ^ N • f z) 2 volume) k
        with hm
      have hPm : MemLp (fun z => jbracket z ^ m • f z) 2 volume :=
        Nat.findGreatest_spec (P := fun N => MemLp (fun z => jbracket z ^ N • f z) 2 volume)
          hN₀k hN₀
      have hε : ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (by positivity)).ne'
      obtain ⟨g, hgs, hgc, hg⟩ := exists_smooth_compact_eLpNorm_sub_le hPm hε
      refine ⟨fun z => (jbracket z ^ m)⁻¹ • g z, ⟨(jbracket_inv_pow_contDiff m).smul hgs,
        hgc.smul_left (f := fun z => (jbracket z ^ m)⁻¹)⟩, fun N hN hNk => ?_⟩
      have hNm : N ≤ m := Nat.le_findGreatest hNk hN
      have hmeas : AEStronglyMeasurable
          (fun z => jbracket z ^ N • (f z - (jbracket z ^ m)⁻¹ • g z)) volume :=
        (jbracket_contDiff.pow N).continuous.aestronglyMeasurable.smul
          (hf.sub ((jbracket_inv_pow_contDiff m).smul hgs).continuous.aestronglyMeasurable)
      refine le_trans (eLpNorm_mono hmeas fun z => ?_) hg
      show _ ≤ ‖jbracket z ^ m • f z - g z‖
      have hjm : 0 < jbracket z ^ m := pow_pos (jbracket_pos z) m
      have heq : jbracket z ^ N • (f z - (jbracket z ^ m)⁻¹ • g z) =
          (jbracket z ^ N / jbracket z ^ m) • (jbracket z ^ m • f z - g z) := by
        rw [smul_sub, smul_sub, smul_smul, smul_smul, div_mul_cancel₀ _ hjm.ne', div_eq_mul_inv]
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_pos (pow_pos (jbracket_pos z) N) hjm).le]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one hjm).2 (pow_le_pow_right₀ (one_le_jbracket z) hNm))
    · refine ⟨0, ⟨contDiff_const, HasCompactSupport.zero⟩, fun N hN hNk => absurd ⟨N, hNk, hN⟩ hex⟩
  choose ψ hψs hψ using hk
  exact ⟨ψ, hψs, fun N hN k hNk => hψ k N hN hNk⟩

end Approx

theorem tendsto_bound_zero {C A : ℝ≥0∞} (hC : C ≠ ⊤) (hA : A ≠ ⊤) :
    Tendsto (fun k : ℕ => C * (A * ENNReal.ofReal (1 / ((k : ℝ) + 1)) ^ 2) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
  have he : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp he
  rw [zero_pow two_ne_zero] at h2
  have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hA)
  rw [mul_zero] at h3
  have h4 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h3
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h4
  have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr hC)
  rw [mul_zero] at h5
  exact h5

/-- **Compactly supported data** (`CompactDensityStatement`). -/
theorem compactDensity : CompactDensityStatement.{u, v} := by
  refine ⟨fun k φ hφ hc => ⟨smoothCompactPlaneHk k φ hφ hc, ?_⟩, ?_⟩
  · have h := smoothCompactPlaneHk_jet_ae k φ hφ hc 0 (Nat.zero_le _) (fun i => i.elim0)
    simp only [orderedDerivative_zero] at h
    exact h
  intro ι _ h _ _ _ _ _ F hF
  have hap := fun x => exists_bracket_approx (hF x)
  choose ψ hψs hψ using hap
  refine ⟨fun k x => ψ x k, fun k x => hψs x k, fun π n s hfin => ?_⟩
  set N := if s = 0 then 0 else n with hN
  set C := ENNReal.ofReal ((momentIndices n).card * max 1 |s| ^ n) with hC
  set A := ∑ x, ENNReal.ofReal ((π x)⁻¹) with hA
  have hAt : A ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_bound_zero (C := C) (A := A) ENNReal.ofReal_ne_top hAt)
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
  refine (momentNorm_le_bracket π n s _ fun x =>
    (hF x).sub (hψs x k).1.continuous.aestronglyMeasurable).trans ?_
  rw [← hN, ← hC]
  gcongr
  rw [hA, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : 0 < π x
  · gcongr
    exact hψ x N (memLp_bracket_of_momentNorm hfin hx (hF x)) k hk
  · rw [ENNReal.ofReal_eq_zero.2 (inv_nonpos.2 (not_lt.1 hx)), zero_mul, zero_mul]
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Compact chain data determine the retained amplitudes linearly

The explicit amplitudes `retainedCosAmplitude`, `retainedSinAmplitude` are a.e. invariant and, on
integrable endpoints, linear (`retainedCosAmplitude_add_smul`). If chains whose datum vanishes a.e.
have vanishing amplitudes (from `CompactChainGaussianStatement` at the datum `0`) and the endpoints
of compact chain data are integrable (`CompactChainGaussianStatement`), then the chain combination
(`ChainCombinationStatement`) makes the amplitudes linear in the datum, across any descending slot
assignments (`retainedAmplitudes_linear`). -/

universe u v

section Amplitudes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem retainedCosAmplitude_congr_ae (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ)
    {e e' : Vec 2 → E} (he : e =ᵐ[volume] e') :
    retainedCosAmplitude K η χlo e = retainedCosAmplitude K η χlo e' := by
  funext θ
  unfold retainedCosAmplitude
  have hc : (fun y => Real.cos (vecDot θ y) • e y) =ᵐ[volume]
      fun y => Real.cos (vecDot θ y) • e' y := he.mono fun y hy => by simp only [hy]
  rw [integral_congr_ae hc]

theorem retainedSinAmplitude_congr_ae (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ)
    {e e' : Vec 2 → E} (he : e =ᵐ[volume] e') :
    retainedSinAmplitude K η χlo e = retainedSinAmplitude K η χlo e' := by
  funext θ
  unfold retainedSinAmplitude
  have hc : (fun y => Real.sin (vecDot θ y) • e y) =ᵐ[volume]
      fun y => Real.sin (vecDot θ y) • e' y := he.mono fun y hy => by simp only [hy]
  rw [integral_congr_ae hc]

theorem integrable_phase_smul {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ1 : ∀ t, |ψ t| ≤ 1)
    (θ : Vec 2) {e : Vec 2 → E} (he : Integrable e volume) :
    Integrable (fun y => ψ (vecDot θ y) • e y) volume := by
  refine Integrable.mono' he.norm ((hψ.comp (by unfold vecDot; fun_prop :
    Continuous fun y : Vec 2 => vecDot θ y)).aestronglyMeasurable.smul he.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hψ1 _)

theorem integral_phase_add_smul {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ1 : ∀ t, |ψ t| ≤ 1)
    (θ : Vec 2) {e₁ e₂ : Vec 2 → E} (h₁ : Integrable e₁ volume) (h₂ : Integrable e₂ volume)
    (a b : ℝ) :
    ∫ y, ψ (vecDot θ y) • (a • e₁ y + b • e₂ y) =
      a • (∫ y, ψ (vecDot θ y) • e₁ y) + b • ∫ y, ψ (vecDot θ y) • e₂ y := by
  have hs : ∀ y, ψ (vecDot θ y) • (a • e₁ y + b • e₂ y) =
      a • (ψ (vecDot θ y) • e₁ y) + b • (ψ (vecDot θ y) • e₂ y) := fun y => by
    rw [smul_add, smul_comm _ a, smul_comm _ b]
  simp_rw [hs]
  rw [integral_add (f := fun y => a • (ψ (vecDot θ y) • e₁ y))
    (g := fun y => b • (ψ (vecDot θ y) • e₂ y)) ((integrable_phase_smul hψ hψ1 θ h₁).smul a)
    ((integrable_phase_smul hψ hψ1 θ h₂).smul b), integral_smul, integral_smul]

/-- The amplitudes are linear on integrable endpoints. -/
theorem retainedCosAmplitude_add_smul (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ)
    {e₁ e₂ : Vec 2 → E} (h₁ : Integrable e₁ volume) (h₂ : Integrable e₂ volume) (a b : ℝ) :
    retainedCosAmplitude K η χlo (fun y => a • e₁ y + b • e₂ y) =
      a • retainedCosAmplitude K η χlo e₁ + b • retainedCosAmplitude K η χlo e₂ := by
  funext θ
  simp only [retainedCosAmplitude, Pi.add_apply, Pi.smul_apply]
  rw [integral_phase_add_smul Real.continuous_cos Real.abs_cos_le_one θ h₁ h₂, smul_add,
    smul_comm _ a, smul_comm _ b]

theorem retainedSinAmplitude_add_smul (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ)
    {e₁ e₂ : Vec 2 → E} (h₁ : Integrable e₁ volume) (h₂ : Integrable e₂ volume) (a b : ℝ) :
    retainedSinAmplitude K η χlo (fun y => a • e₁ y + b • e₂ y) =
      a • retainedSinAmplitude K η χlo e₁ + b • retainedSinAmplitude K η χlo e₂ := by
  funext θ
  simp only [retainedSinAmplitude, Pi.add_apply, Pi.smul_apply]
  rw [integral_phase_add_smul Real.continuous_sin Real.abs_sin_le_one θ h₁ h₂, smul_add,
    smul_comm _ a, smul_comm _ b]

end Amplitudes

section Chains

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem IsWordSlots.min {letters : Fin Nw → CycleLetter ι h D} {κ κ' : Fin (Nw + 1) → ι → ℕ}
    (h₁ : IsWordSlots letters κ) (h₂ : IsWordSlots letters κ') :
    IsWordSlots letters fun j x => Min.min (κ j x) (κ' j x) := by
  intro j x y o he
  have e₁ := h₁ j x y o he
  have e₂ := h₂ j x y o he
  show Min.min (κ j.succ x) (κ' j.succ x) + o.1 ≤ Min.min (κ j.castSucc y) (κ' j.castSucc y) + 2
  omega

/-- **Linearity on compact chain data.** If the endpoints of compact chain data are integrable and
chains with a.e. vanishing datum have vanishing amplitudes, the amplitudes of chains at any
descending slots are linear in the datum. -/
theorem retainedAmplitudes_linear (hA1 : ChainCombinationStatement.{u, v}) (hD : 2 ≤ D)
    (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (δ t₀ t₁ : ℝ)
    (hint : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ δ) κ t₀ t₁ v f (fun _ _ _ => 0) u w →
        IsCompactDatum f → ∀ x, Integrable (planeValue (u (Fin.last Nw) x t₁)) volume)
    (hzero : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ δ) κ t₀ t₁ v f (fun _ _ _ => 0) u w →
        (∀ x, planeValue (f x) =ᵐ[volume] 0) →
        ∀ x, retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x t₁)) = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x t₁)) = 0)
    {κ₁ κ₂ κ₃ : Fin (Nw + 1) → ι → ℕ} (hs₁ : IsWordSlots letters κ₁)
    (hs₂ : IsWordSlots letters κ₂) (hs₃ : IsWordSlots letters κ₃)
    {f₁ : ∀ x, PlaneHk Set.univ (κ₁ 0 x) (h x)}
    {u₁ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₁ j x) (h x)}
    {w₁ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₁ j x + 1) (h x)}
    (hc₁ : IsPlaneChain (wordChainData G letters X₀ δ) κ₁ t₀ t₁ v f₁ (fun _ _ _ => 0) u₁ w₁)
    (hd₁ : IsCompactDatum f₁)
    {f₂ : ∀ x, PlaneHk Set.univ (κ₂ 0 x) (h x)}
    {u₂ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₂ j x) (h x)}
    {w₂ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₂ j x + 1) (h x)}
    (hc₂ : IsPlaneChain (wordChainData G letters X₀ δ) κ₂ t₀ t₁ v f₂ (fun _ _ _ => 0) u₂ w₂)
    (hd₂ : IsCompactDatum f₂)
    {f₃ : ∀ x, PlaneHk Set.univ (κ₃ 0 x) (h x)}
    {u₃ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₃ j x) (h x)}
    {w₃ : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ₃ j x + 1) (h x)}
    (hc₃ : IsPlaneChain (wordChainData G letters X₀ δ) κ₃ t₀ t₁ v f₃ (fun _ _ _ => 0) u₃ w₃)
    (hd₃ : IsCompactDatum f₃) (a b : ℝ)
    (h₃ : ∀ x, planeValue (f₃ x) =ᵐ[volume]
      fun z => a • planeValue (f₁ x) z + b • planeValue (f₂ x) z) (x : ι) :
    retainedCosAmplitude K η χlo (planeValue (u₃ (Fin.last Nw) x t₁)) =
        a • retainedCosAmplitude K η χlo (planeValue (u₁ (Fin.last Nw) x t₁)) +
          b • retainedCosAmplitude K η χlo (planeValue (u₂ (Fin.last Nw) x t₁)) ∧
      retainedSinAmplitude K η χlo (planeValue (u₃ (Fin.last Nw) x t₁)) =
        a • retainedSinAmplitude K η χlo (planeValue (u₁ (Fin.last Nw) x t₁)) +
          b • retainedSinAmplitude K η χlo (planeValue (u₂ (Fin.last Nw) x t₁)) := by
  -- the combination `a c₁ + b c₂`
  obtain ⟨f₁₂, u₁₂, w₁₂, hc₁₂, hf₁₂, he₁₂⟩ :=
    hA1 letters G v X₀ δ t₀ t₁ κ₁ κ₂ hD hs₁ hs₂ f₁ u₁ w₁ f₂ u₂ w₂ hc₁ hc₂ a b
  -- the difference `c₃ - (a c₁ + b c₂)`
  obtain ⟨f₀, u₀, w₀, hc₀, hf₀, he₀⟩ :=
    hA1 letters G v X₀ δ t₀ t₁ κ₃ _ hD hs₃ (hs₁.min hs₂) f₃ u₃ w₃ f₁₂ u₁₂ w₁₂ hc₃ hc₁₂ 1 (-1)
  have hz : ∀ y, planeValue (f₀ y) =ᵐ[volume] 0 := fun y => by
    filter_upwards [hf₀ y, hf₁₂ y, h₃ y] with z h0 h12 h3
    rw [h0, h12, h3]
    simp only [one_smul, neg_one_smul, add_neg_cancel, Pi.zero_apply]
  obtain ⟨hcos0, hsin0⟩ := hzero _ (hs₃.min (hs₁.min hs₂)) f₀ u₀ w₀ hc₀ hz x
  have hi₁ := hint κ₁ hs₁ f₁ u₁ w₁ hc₁ hd₁ x
  have hi₂ := hint κ₂ hs₂ f₂ u₂ w₂ hc₂ hd₂ x
  have hi₃ := hint κ₃ hs₃ f₃ u₃ w₃ hc₃ hd₃ x
  have hi₁₂ : Integrable (planeValue (u₁₂ (Fin.last Nw) x t₁)) volume :=
    ((hi₁.smul a).add (hi₂.smul b)).congr (he₁₂ x).symm
  constructor
  · have h12 := (retainedCosAmplitude_congr_ae K η χlo (he₁₂ x)).trans
      (retainedCosAmplitude_add_smul K η χlo hi₁ hi₂ a b)
    have h0 := (retainedCosAmplitude_congr_ae K η χlo (he₀ x)).trans
      (retainedCosAmplitude_add_smul K η χlo hi₃ hi₁₂ 1 (-1))
    rw [hcos0, h12, one_smul, neg_one_smul] at h0
    have h' := eq_neg_of_add_eq_zero_left h0.symm
    rwa [neg_neg] at h'
  · have h12 := (retainedSinAmplitude_congr_ae K η χlo (he₁₂ x)).trans
      (retainedSinAmplitude_add_smul K η χlo hi₁ hi₂ a b)
    have h0 := (retainedSinAmplitude_congr_ae K η χlo (he₀ x)).trans
      (retainedSinAmplitude_add_smul K η χlo hi₃ hi₁₂ 1 (-1))
    rw [hsin0, h12, one_smul, neg_one_smul] at h0
    have h' := eq_neg_of_add_eq_zero_left h0.symm
    rwa [neg_neg] at h'

end Chains

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Smoothness of the cut-off Bloch sums in the frequency

`χ(θ) ∑_k ψ(θ·(z+k)) g(z+k)` with `ψ ∈ {cos, sin}`: each term is smooth in `θ` with
`‖∂_θ^j‖ ≤ B 2^n (2⟨z+k⟩)^n ‖g(z+k)‖` for `j ≤ n` (Leibniz with the cutoff, the phase is a
continuous linear map of norm `≤ 2⟨y⟩`). Under `∑_k ⟨z+k⟩^n ‖g(z+k)‖ < ∞` the sum is `C^n` in `θ`,
its derivatives are bounded by `B 4^n ∑_k ⟨z+k⟩^n ‖g(z+k)‖`, and it is linear in `g`
(`cutoffBloch_contDiff_bound`, `blochPhase_sub`). -/

/-- The phase `θ ↦ θ·y` as a continuous linear map. -/
noncomputable def phaseCLM (y : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, y i • ContinuousLinearMap.proj i

theorem phaseCLM_apply (y θ : Vec 2) : phaseCLM y θ = vecDot θ y := by
  simp [phaseCLM, vecDot, Fin.sum_univ_two, mul_comm]

theorem norm_phaseCLM_le (y : Vec 2) : ‖phaseCLM y‖ ≤ 2 * jbracket y := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_pos two_pos (jbracket_pos y)).le
    fun θ => ?_
  rw [phaseCLM_apply, Real.norm_eq_abs]
  unfold vecDot
  rw [Fin.sum_univ_two]
  have h0 : |θ 0| ≤ ‖θ‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm θ 0
  have h1 : |θ 1| ≤ ‖θ‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm θ 1
  have hy0 := abs_coord_le_jbracket y 0
  have hy1 := abs_coord_le_jbracket y 1
  calc |θ 0 * y 0 + θ 1 * y 1| ≤ |θ 0| * |y 0| + |θ 1| * |y 1| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ ‖θ‖ * jbracket y + ‖θ‖ * jbracket y :=
        add_le_add (mul_le_mul h0 hy0 (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 hy1 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * jbracket y * ‖θ‖ := by ring

/-- A smooth phase with all derivatives bounded by one (`cos`, `sin`). -/
def IsUnitPhase (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ ∀ (j : ℕ) (t : ℝ), |iteratedDeriv j ψ t| ≤ 1

theorem isUnitPhase_cos : IsUnitPhase Real.cos :=
  ⟨Real.contDiff_cos, Real.abs_iteratedDeriv_cos_le_one⟩

theorem isUnitPhase_sin : IsUnitPhase Real.sin :=
  ⟨Real.contDiff_sin, Real.abs_iteratedDeriv_sin_le_one⟩

theorem IsUnitPhase.abs_le {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (t : ℝ) : |ψ t| ≤ 1 := by
  simpa using hψ.2 0 t

theorem IsUnitPhase.contDiff_comp {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (y : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun θ : Vec 2 => ψ (vecDot θ y) := by
  have h : (fun θ : Vec 2 => ψ (vecDot θ y)) = ψ ∘ phaseCLM y :=
    funext fun θ => by simp [phaseCLM_apply]
  rw [h]
  exact hψ.1.comp (phaseCLM y).contDiff

theorem norm_iteratedFDeriv_phase_le {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (y : Vec 2) (j : ℕ)
    (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun θ => ψ (vecDot θ y)) θ‖ ≤ (2 * jbracket y) ^ j := by
  have h : (fun θ : Vec 2 => ψ (vecDot θ y)) = ψ ∘ phaseCLM y :=
    funext fun θ => by simp [phaseCLM_apply]
  rw [h, (phaseCLM y).iteratedFDeriv_comp_right hψ.1 θ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  calc |iteratedDeriv j ψ (phaseCLM y θ)| * ‖phaseCLM y‖ ^ j ≤ 1 * (2 * jbracket y) ^ j :=
        mul_le_mul (hψ.2 _ _) (pow_le_pow_left₀ (norm_nonneg _) (norm_phaseCLM_le y) j)
          (by positivity) zero_le_one
    _ = (2 * jbracket y) ^ j := one_mul _

/-- Uniform bounds of the derivatives of a smooth compactly supported cutoff. -/
theorem exists_iteratedFDeriv_bound {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B := by
  have h : ∀ i : ℕ, ∃ C, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ C := fun i =>
    (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  choose C hC using h
  refine ⟨∑ i ∈ Finset.range (n + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _,
    fun i hi θ => (hC i θ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- **Leibniz** for the cutoff times a phase. -/
theorem norm_iteratedFDeriv_cutoffPhase_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {n : ℕ} {B : ℝ}
    (hB : ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B) (y : Vec 2) {j : ℕ} (hj : j ≤ n)
    (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun θ => χ θ * ψ (vecDot θ y)) θ‖ ≤
      B * 2 ^ n * (2 * jbracket y) ^ n := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) θ)
  have hy1 : 1 ≤ 2 * jbracket y := by linarith [one_le_jbracket y]
  refine (norm_iteratedFDeriv_mul_le hχ (hψ.contDiff_comp y) θ
    (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ θ‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun θ => ψ (vecDot θ y)) θ‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * (2 * jbracket y) ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hij : i ≤ n := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hB i hij θ) (Nat.cast_nonneg _))
          ((norm_iteratedFDeriv_phase_le hψ y (j - i) θ).trans
            (pow_le_pow_right₀ hy1 ((Nat.sub_le j i).trans hj)))
          (norm_nonneg _) (by positivity)
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * B * (2 * jbracket y) ^ n := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = 2 ^ j * B * (2 * jbracket y) ^ n := by
        congr 2
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ n * B * (2 * jbracket y) ^ n := by
        gcongr
        · norm_num
    _ = B * 2 ^ n * (2 * jbracket y) ^ n := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_smul_const_le {φ : Vec 2 → ℝ} {N : ℕ∞}
    (hφ : ContDiff ℝ N φ) (v : E) {j : ℕ} (hj : (j : ℕ∞) ≤ N) (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun θ => φ θ • v) θ‖ ≤ ‖iteratedFDeriv ℝ j φ θ‖ * ‖v‖ := by
  have h : (fun θ => φ θ • v) = (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ φ :=
    funext fun θ => by simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [h, (ContinuousLinearMap.toSpanSingleton ℝ v).iteratedFDeriv_comp_left hφ.contDiffAt
    (by exact_mod_cast hj)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton, mul_comm]

/-- The Bloch sum with phase `ψ`: `∑_k ψ(θ·(z+k)) g(z+k)`. -/
noncomputable def blochPhase (ψ : ℝ → ℝ) (θ : Vec 2) (g : Vec 2 → E) (z : Vec 2) : E :=
  ∑' k : Fin 2 → ℤ, ψ (vecDot θ (z + fun i => (k i : ℝ))) • g (z + fun i => (k i : ℝ))

theorem blochCos_eq_blochPhase (θ : Vec 2) (g : Vec 2 → E) (z : Vec 2) :
    blochCos θ g z = blochPhase Real.cos θ g z := rfl

theorem blochSin_eq_blochPhase (θ : Vec 2) (g : Vec 2 → E) (z : Vec 2) :
    blochSin θ g z = blochPhase Real.sin θ g z := rfl

omit [NormedSpace ℝ E] in
theorem summable_norm_of_weighted {g : Vec 2 → E} {z : Vec 2} {n : ℕ}
    (hs : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) :
    Summable fun k : Fin 2 → ℤ => ‖g (z + fun i => (k i : ℝ))‖ :=
  hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun _ =>
    le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_jbracket _))

variable [CompleteSpace E]

theorem summable_blochPhase_terms {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {g : Vec 2 → E}
    {z : Vec 2} (hs : Summable fun k : Fin 2 → ℤ => ‖g (z + fun i => (k i : ℝ))‖) (θ : Vec 2) :
    Summable fun k : Fin 2 → ℤ =>
      ψ (vecDot θ (z + fun i => (k i : ℝ))) • g (z + fun i => (k i : ℝ)) :=
  hs.of_norm_bounded fun k => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψ.abs_le _)

/-- Linearity of the Bloch sums on summable data. -/
theorem blochPhase_sub {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {g₁ g₂ : Vec 2 → E} {z : Vec 2}
    (h₁ : Summable fun k : Fin 2 → ℤ => ‖g₁ (z + fun i => (k i : ℝ))‖)
    (h₂ : Summable fun k : Fin 2 → ℤ => ‖g₂ (z + fun i => (k i : ℝ))‖) (θ : Vec 2) :
    blochPhase ψ θ (fun y => g₁ y - g₂ y) z = blochPhase ψ θ g₁ z - blochPhase ψ θ g₂ z := by
  unfold blochPhase
  rw [← (summable_blochPhase_terms hψ h₁ θ).tsum_sub (summable_blochPhase_terms hψ h₂ θ)]
  simp only [smul_sub]

theorem cutoffBloch_eq {χ : Vec 2 → ℝ} {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {g : Vec 2 → E}
    {z : Vec 2} (hs : Summable fun k : Fin 2 → ℤ => ‖g (z + fun i => (k i : ℝ))‖) :
    (fun θ => χ θ • blochPhase ψ θ g z) = fun θ => ∑' k : Fin 2 → ℤ,
      (χ θ * ψ (vecDot θ (z + fun i => (k i : ℝ)))) • g (z + fun i => (k i : ℝ)) := by
  funext θ
  rw [blochPhase, ← (summable_blochPhase_terms hψ hs θ).tsum_const_smul]
  simp only [smul_smul]

/-- **Termwise smoothness**: under `∑_k ⟨z+k⟩^n ‖g(z+k)‖ < ∞` the cut-off Bloch sum is `C^n`
in `θ` with derivatives bounded by `B 4^n ∑_k ⟨z+k⟩^n ‖g(z+k)‖`. -/
theorem cutoffBloch_contDiff_bound {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {ψ : ℝ → ℝ}
    (hψ : IsUnitPhase ψ) {n : ℕ} {B : ℝ} (hB : ∀ i ≤ n, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B)
    {g : Vec 2 → E} {z : Vec 2}
    (hs : Summable fun k : Fin 2 → ℤ =>
      jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) :
    ContDiff ℝ n (fun θ => χ θ • blochPhase ψ θ g z) ∧
      ∀ j ≤ n, ∀ θ, ‖iteratedFDeriv ℝ j (fun θ => χ θ • blochPhase ψ θ g z) θ‖ ≤
        B * 2 ^ n * 2 ^ n * ∑' k : Fin 2 → ℤ,
          jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖ := by
  rw [cutoffBloch_eq hψ (summable_norm_of_weighted hs)]
  set f : (Fin 2 → ℤ) → Vec 2 → E := fun k θ =>
    (χ θ * ψ (vecDot θ (z + fun i => (k i : ℝ)))) • g (z + fun i => (k i : ℝ)) with hf
  set v : ℕ → (Fin 2 → ℤ) → ℝ := fun _ k => B * 2 ^ n * 2 ^ n *
    (jbracket (z + fun i => (k i : ℝ)) ^ n * ‖g (z + fun i => (k i : ℝ))‖) with hv
  have hfs : ∀ k, ContDiff ℝ (n : ℕ∞) (f k) := fun k =>
    ((hχ.mul (hψ.contDiff_comp _)).smul contDiff_const).of_le (by exact_mod_cast le_top)
  have hvs : ∀ j : ℕ, (j : ℕ∞) ≤ n → Summable (v j) := fun _ _ => hs.mul_left _
  have hbd : ∀ (j : ℕ) (k : Fin 2 → ℤ) (θ : Vec 2), (j : ℕ∞) ≤ n →
      ‖iteratedFDeriv ℝ j (f k) θ‖ ≤ v j k := by
    intro j k θ hj
    have hjn : j ≤ n := by exact_mod_cast hj
    refine (norm_iteratedFDeriv_smul_const_le ((hχ.mul (hψ.contDiff_comp _)).of_le
      (by exact_mod_cast le_top : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))
      _ hj θ).trans ?_
    have h := norm_iteratedFDeriv_cutoffPhase_le hχ hψ hB (z + fun i => (k i : ℝ)) hjn θ
    calc ‖iteratedFDeriv ℝ j (fun θ => χ θ * ψ (vecDot θ (z + fun i => (k i : ℝ)))) θ‖ *
          ‖g (z + fun i => (k i : ℝ))‖
        ≤ B * 2 ^ n * (2 * jbracket (z + fun i => (k i : ℝ))) ^ n *
          ‖g (z + fun i => (k i : ℝ))‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = v j k := by rw [hv, mul_pow]; ring
  refine ⟨contDiff_tsum hfs hvs fun j k θ hj => hbd j k θ hj, fun j hj θ => ?_⟩
  rw [iteratedFDeriv_tsum_apply hfs hvs hbd (by exact_mod_cast hj)]
  refine (tsum_of_norm_bounded (hvs j (by exact_mod_cast hj)).hasSum
    fun k => hbd j k θ (by exact_mod_cast hj)).trans (le_of_eq ?_)
  rw [hv, tsum_mul_left]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The amplitudes of compact chain data in `L²`

The weighted jet norm of order `0` without weight is the moment norm of order `0`
(`weightedJetNorm_zero_zero`). The explicit amplitudes are even and odd
(`retainedCosAmplitude_neg`, `retainedSinAmplitude_neg`), so Plancherel
(`AmplitudePlancherelStatement`) bounds them in `L²` by the function they represent
(`eLpNorm_amplitude_le`). With `GaussianPlancherelStatement` at output order `0` this bounds the
amplitudes of compact chain data by the moment norm of the datum. -/

universe u v

section Norms

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The unweighted jet norm of order `0` is the moment norm of order `0`. -/
theorem weightedJetNorm_zero_zero (π : ι → ℝ) (s r : ℝ) {g : ∀ x, Vec 2 → h x}
    (hg : ∀ x, AEStronglyMeasurable (g x) volume) :
    weightedJetNorm π 0 0 s r (fun x _ wd z => orderedDerivative wd (g x) z) =
      momentNorm π 0 1 g := by
  have hidx : momentIndices 0 = {(0, 0)} := by decide
  have hw : ∀ x, (fun z : Vec 2 => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((0 : ℝ) / 2) *
      Real.sqrt (∑ w : DerivativeWord2 0, ‖orderedDerivative w (g x) z‖ ^ 2)) =
      fun z => ‖g x z‖ := fun x => by
    funext z
    rw [zero_div, Real.rpow_zero, one_mul, Fintype.sum_unique, orderedDerivative_zero,
      Real.sqrt_sq (norm_nonneg _)]
  simp only [weightedJetNorm, momentNorm, hidx, Finset.sum_singleton, zero_add,
    Finset.range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
    ENNReal.ofReal_one, one_mul, inv_one, hw, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [eLpNorm_norm (g x) (hg x)]

end Norms

section Amplitudes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem retainedCutoff_neg {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) (θ : Vec 2) : retainedCutoff K η χlo (-θ) = retainedCutoff K η χlo θ := by
  unfold retainedCutoff
  rw [smul_neg, smul_neg, hχ.even, hχ.even]

private theorem vecDot_neg_left (θ y : Vec 2) : vecDot (-θ) y = -vecDot θ y := by
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem retainedCosAmplitude_neg {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) (e : Vec 2 → E) (θ : Vec 2) :
    retainedCosAmplitude K η χlo e (-θ) = retainedCosAmplitude K η χlo e θ := by
  simp only [retainedCosAmplitude, retainedCutoff_neg hχ, vecDot_neg_left, Real.cos_neg]

theorem retainedSinAmplitude_neg {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) (e : Vec 2 → E) (θ : Vec 2) :
    retainedSinAmplitude K η χlo e (-θ) = -retainedSinAmplitude K η χlo e θ := by
  simp only [retainedSinAmplitude, retainedCutoff_neg hχ, vecDot_neg_left, Real.sin_neg,
    neg_smul, MeasureTheory.integral_neg, smul_neg]

end Amplitudes

/-- **Plancherel bounds an even/odd amplitude pair** by the function it represents. -/
theorem eLpNorm_amplitude_le (hB0 : AmplitudePlancherelStatement.{v}) {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {r : ℝ} (hr : 0 < r) {g A B : Vec 2 → E}
    (hret : IsRetainedAmplitude g r A B)
    (hsym : ∀ θ, A (-θ) = A θ ∧ B (-θ) = -B θ) :
    eLpNorm A 2 volume ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * eLpNorm g 2 volume ∧
      eLpNorm B 2 volume ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * eLpNorm g 2 volume := by
  obtain ⟨-, -, hpl⟩ := hB0 r g A B hr hret
  obtain ⟨hiff, heq⟩ := hpl hsym
  by_cases hfin : eLpNorm g 2 volume = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact ⟨le_top, le_top⟩
  have hmem : MemLp g 2 volume := Ne.lt_top hfin
  have hAB := hiff.1 hmem
  have hg2 := heq hmem
  have h2π : ENNReal.ofReal (2 * Real.pi)⁻¹ * ENNReal.ofReal (2 * Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  have hA : eLpNorm A 2 volume ≤ (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) ^
      (1 / 2 : ℝ) := by
    calc eLpNorm A 2 volume = (eLpNorm A 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow le_self_add (by norm_num)
  have hB : eLpNorm B 2 volume ≤ (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) ^
      (1 / 2 : ℝ) := by
    calc eLpNorm B 2 volume = (eLpNorm B 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow le_add_self (by norm_num)
  have hT : (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * eLpNorm g 2 volume := by
    rw [hg2, ← mul_assoc, h2π, one_mul]
  exact ⟨hA.trans hT.le, hB.trans hT.le⟩

end AVRegularity.CycleWords.Assembly
end
