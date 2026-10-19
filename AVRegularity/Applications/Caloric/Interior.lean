-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Caloric.Duhamel
public import AVRegularity.External.Campanato.Representative

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.Caloric

/-! # The backward heat potential of a test function (skeleton) -/

/-- `(Pρ)(p) = ∫ Γ(q) ρ(p + q) dq`. -/
def potential (ρ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ := ∫ q, heatKP q * ρ (p + q)

instance instIsNegInvariantVolumeProd :
    (volume : Measure (ℝ × Vec 2)).IsNegInvariant := by
  refine ⟨?_⟩
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure (Vec 2)))
  rw [← Measure.volume_eq_prod] at h
  exact h.map_eq

instance instIsAddLeftInvariantVolumeProd :
    (volume : Measure (ℝ × Vec 2)).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The reflected kernel `q ↦ Γ(-q)`. -/
def refKernel (q : ℝ × Vec 2) : ℝ := heatKP (-q)

theorem refKernel_locallyIntegrable :
    LocallyIntegrable refKernel (volume : Measure (ℝ × Vec 2)) := by
  intro p
  rcases heatKP_locallyIntegrable (-p) with ⟨s, hs, hi⟩
  let e : (ℝ × Vec 2) ≃ₜ (ℝ × Vec 2) := Homeomorph.neg _
  have hs' : e '' s ∈ nhds p := by
    have h := e.isOpenMap.image_mem_nhds hs
    rw [show e (-p) = p by simp [e]] at h
    exact h
  refine ⟨e '' s, hs', ?_⟩
  have hneg : MeasurePreserving (fun x : ℝ × Vec 2 => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hc := hneg.integrableOn_comp_preimage e.measurableEmbedding
    (f := heatKP) (s := s)
  have hc' := hc.mpr hi
  have hset : (fun x : ℝ × Vec 2 => -x) ⁻¹' s = e '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨-x, hx, by simp [e]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [e] using hy
  rw [hset] at hc'
  exact hc'

theorem potential_eq_convolution (ρ : ℝ × Vec 2 → ℝ) :
    potential ρ = fun p => MeasureTheory.convolution refKernel ρ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume p := by
  funext p
  unfold potential MeasureTheory.convolution
  rw [← integral_neg_eq_self (fun q : ℝ × Vec 2 => heatKP q * ρ (p + q)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [refKernel, sub_eq_add_neg]

theorem potential_contDiff {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) : ContDiff ℝ (⊤ : ℕ∞) (potential ρ) := by
  rw [potential_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    refKernel_locallyIntegrable hρ

theorem potential_eq_zero {ρ : ℝ × Vec 2 → ℝ} {T : ℝ} (hT : ∀ z : ℝ × Vec 2, T ≤ z.1 → ρ z = 0)
    (p : ℝ × Vec 2) (hp : T ≤ p.1) : potential ρ p = 0 := by
  unfold potential
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : 0 < q.1
  · have : ρ (p + q) = 0 := hT _ (by simp; linarith)
    simp [this]
  · have : heatKP q = 0 := heatK_of_nonpos (not_lt.mp hq) _
    simp [this]

theorem potential_fderiv {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (p e : ℝ × Vec 2) :
    fderiv ℝ (potential ρ) p e = potential (fun z => fderiv ℝ ρ z e) p := by
  have hfd := hc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
    refKernel_locallyIntegrable (hρ.of_le (by norm_num)) p
  rw [potential_eq_convolution, hfd.fderiv,
    MeasureTheory.convolution_precompR_apply
      (L := ContinuousLinearMap.lsmul ℝ ℝ) refKernel_locallyIntegrable
      (hc.fderiv (𝕜 := ℝ)) (hρ.continuous_fderiv (by simp))]
  exact (congrFun (potential_eq_convolution fun z => fderiv ℝ ρ z e) p).symm

theorem integrable_heatKP_mul_translate {f : ℝ × Vec 2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (p : ℝ × Vec 2) :
    Integrable (fun q => heatKP q * f (p + q)) volume := by
  have hc' : HasCompactSupport (fun q => f (p + q)) :=
    hc.comp_homeomorph (Homeomorph.addLeft p)
  simpa [smul_eq_mul] using heatKP_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    (hf.comp (continuous_const.add continuous_id)) hc'

theorem potential_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × Vec 2 → ℝ)
    (hf : ∀ i, Continuous (f i)) (hc : ∀ i, HasCompactSupport (f i)) (p : ℝ × Vec 2) :
    potential (fun z => ∑ i ∈ s, f i z) p = ∑ i ∈ s, potential (f i) p := by
  unfold potential
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s fun i _ => integrable_heatKP_mul_translate (hf i) (hc i) p

theorem contDiff_fderiv_dir {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (e : ℝ × Vec 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ ρ z e) := by
  have := hρ.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)
  exact this.comp (contDiff_id.prodMk contDiff_const)

theorem stTimeDeriv_translate (ρ : ℝ × Vec 2 → ℝ) (p q : ℝ × Vec 2) :
    stTimeDeriv (fun z => ρ (p + z)) q = stTimeDeriv ρ (p + q) := by
  unfold stTimeDeriv
  rw [fderiv_comp_add_left]

theorem stSpaceLap_translate (ρ : ℝ × Vec 2 → ℝ) (p q : ℝ × Vec 2) :
    stSpaceLap (fun z => ρ (p + z)) q = stSpaceLap ρ (p + q) := by
  unfold stSpaceLap
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun q' => fderiv ℝ (fun z => ρ (p + z)) q' (0, basisVec i)) =
      fun q' => (fun w => fderiv ℝ ρ w (0, basisVec i)) (p + q') := by
    funext q'; rw [fderiv_comp_add_left]
  rw [h1]
  exact congrArg (fun L => L (0, basisVec i))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun w => fderiv ℝ ρ w (0, basisVec i)) p)

theorem potential_equation {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (p : ℝ × Vec 2) :
    stTimeDeriv (potential ρ) p + stSpaceLap (potential ρ) p = - ρ p := by
  have hD : ∀ e, ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ ρ z e) := contDiff_fderiv_dir hρ
  have hDc : ∀ e, HasCompactSupport (fun z => fderiv ℝ ρ z e) := fun e => hc.fderiv_apply ℝ e
  have hT : stTimeDeriv (potential ρ) p = potential (stTimeDeriv ρ) p :=
    potential_fderiv hρ hc p _
  have hL : stSpaceLap (potential ρ) p = potential (stSpaceLap ρ) p := by
    have h1 : ∀ i : Fin 2, fderiv ℝ (fun q => fderiv ℝ (potential ρ) q (0, basisVec i)) p
        (0, basisVec i) = potential (fun z => fderiv ℝ (fun w => fderiv ℝ ρ w (0, basisVec i)) z
          (0, basisVec i)) p := by
      intro i
      have : (fun q => fderiv ℝ (potential ρ) q (0, basisVec i)) =
          potential (fun w => fderiv ℝ ρ w (0, basisVec i)) := by
        funext q; exact potential_fderiv hρ hc q _
      rw [this]
      exact potential_fderiv (hD _) (hDc _) p _
    unfold stSpaceLap
    simp_rw [h1]
    rw [← potential_sum]
    · intro i
      exact (contDiff_fderiv_dir (hD _) _).continuous
    · intro i
      exact (hDc _).fderiv_apply ℝ _
  have hcont : Continuous (stTimeDeriv ρ) := (hD _).continuous
  have hsupp : HasCompactSupport (stTimeDeriv ρ) := hDc _
  have hLc : Continuous (stSpaceLap ρ) := by
    unfold stSpaceLap
    exact continuous_finsetSum _ fun i _ => (contDiff_fderiv_dir (hD _) _).continuous
  have hLs : HasCompactSupport (stSpaceLap ρ) := by
    unfold stSpaceLap
    rw [show (fun z => ∑ i : Fin 2, _) = _ from rfl]
    simp_rw [Fin.sum_univ_two]
    exact ((hDc _).fderiv_apply ℝ _).add ((hDc _).fderiv_apply ℝ _)
  rw [hT, hL]
  unfold potential
  rw [← integral_add (integrable_heatKP_mul_translate hcont hsupp p)
    (integrable_heatKP_mul_translate hLc hLs p)]
  have hv := heatKP_duhamel (v := fun z => ρ (p + z)) (hρ.comp (contDiff_const.add contDiff_id))
    (hc.comp_homeomorph (Homeomorph.addLeft p))
  simp_rw [stTimeDeriv_translate, stSpaceLap_translate] at hv
  simpa [mul_add] using hv

/-! # Pointwise form of the cutoff potential identity

For a test function `ρ` supported in `Q_{1/2}` and `u = Pρ`, the function `ω u` satisfies
`(∂ₛ+Δ)(ω u) = -ρ + ∫ ρ(z) kern(z,p) dz`. -/

section
section

variable {G : ℝ × Vec 2 → ℝ} {ρ : ℝ × Vec 2 → ℝ}

/-- Standing hypotheses on the smooth modification of the heat kernel. -/
def IsKernelMod (G : ℝ × Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) G ∧
    ∀ q : ℝ × Vec 2, (1 / 64 ≤ vecNormSq q.2 ∨ 9 / 64 ≤ q.1) → G q = heatKP q

/-- Standing hypotheses on the test function `ρ`. -/
def IsRepTest (ρ : ℝ × Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ openCyl 0 (1 / 2)

theorem translate_heat (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    ∫ q, heatKP q * φ (p + q) = ∫ z, heatKP (z - p) * φ z := by
  have := integral_add_left_eq_self (μ := (volume : Measure (ℝ × Vec 2)))
    (fun z => heatKP (z - p) * φ z) p
  simpa using this

theorem integral_heat_eq_kernelMod (hG : IsKernelMod G) {φ : ℝ × Vec 2 → ℝ} {p : ℝ × Vec 2}
    (hp : p ∉ cutW) (hφ : ∀ z, φ z ≠ 0 → z ∈ openCyl 0 (1 / 2)) :
    ∫ q, heatKP q * φ (p + q) = ∫ z, G (z - p) * φ z := by
  rw [translate_heat]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases h0 : φ z = 0
  · simp [h0]
  · simp only
    rw [hG.2 _ (cut_sep (hφ z h0) hp)]

theorem integrable_mul_cont (hρ : IsRepTest ρ) {g : ℝ × Vec 2 → ℝ} (hg : Continuous g) :
    Integrable (fun z => ρ z * g z) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hρ.1.continuous.mul hg
  · exact hρ.2.1.mul_right

theorem mem_openCyl_of_ne_zero (hρ : IsRepTest ρ) {z : ℝ × Vec 2} (hz : ρ z ≠ 0) :
    z ∈ openCyl 0 (1 / 2) := hρ.2.2 (subset_tsupport _ hz)

theorem mem_openCyl_of_fderiv_ne_zero (hρ : IsRepTest ρ) {z : ℝ × Vec 2} {e : ℝ × Vec 2}
    (hz : fderiv ℝ ρ z e ≠ 0) : z ∈ openCyl 0 (1 / 2) := by
  have : z ∈ Function.support (fderiv ℝ ρ) := by
    intro h; apply hz; simp [h]
  exact hρ.2.2 (support_fderiv_subset ℝ this)

theorem cutω_mul_self (hρ : IsRepTest ρ) (p : ℝ × Vec 2) : cutω p * ρ p = ρ p := by
  by_cases h0 : ρ p = 0
  · simp [h0]
  · have hp := mem_openCyl_of_ne_zero hρ h0
    simp only [openCyl, euclidBall, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero,
      sub_zero, Set.mem_ofPred_eq] at hp
    have : p ∈ cutW := by
      refine ⟨?_, ?_⟩ <;> norm_num at hp ⊢ <;> linarith [hp.1.1, hp.2]
    rw [cutω_eq_one_of_mem this, one_mul]

theorem potential_mul_cutA (hG : IsKernelMod G) (hρ : IsRepTest ρ) (p : ℝ × Vec 2) :
    potential ρ p * cutA p = ∫ z, ρ z * (G (z - p) * cutA p) := by
  by_cases hA : cutA p = 0
  · simp [hA]
  · have hp : p ∉ cutW := fun h => hA (cutA_eq_zero h)
    unfold potential
    rw [integral_heat_eq_kernelMod hG hp (fun z hz => mem_openCyl_of_ne_zero hρ hz),
      ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring

instance instIsAddHaarVolumeProd : (volume : Measure (ℝ × Vec 2)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

theorem integral_fderiv_mul_shift (hG : IsKernelMod G) (hρ : IsRepTest ρ) (p e : ℝ × Vec 2) :
    ∫ z, G (z - p) * fderiv ℝ ρ z e = -∫ z, ρ z * fderiv ℝ G (z - p) e := by
  have hd : ∀ z, fderiv ℝ (fun z => G (z - p)) z = fderiv ℝ G (z - p) := fun z =>
    (hasFDerivAt_comp_sub hG.1 z p).fderiv
  have hGc : Continuous (fun z => G (z - p)) :=
    hG.1.continuous.comp (continuous_id.sub continuous_const)
  have hGd : Continuous (fun z => fderiv ℝ G (z - p) e) :=
    ((hG.1.continuous_fderiv (by simp)).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const
  have hρd : Continuous (fun z => fderiv ℝ ρ z e) :=
    (hρ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun x => fderiv ℝ (fun z => G (z - p)) x e * ρ x) := by
    simp only [hd]
    exact (integrable_mul_cont hρ hGd).congr
      (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have i2 : Integrable (fun x => G (x - p) * fderiv ℝ ρ x e) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hGc.mul hρd
    · exact (hρ.2.1.fderiv_apply (𝕜 := ℝ) e).mul_left
  have i3 : Integrable (fun x => G (x - p) * ρ x) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hGc.mul hρ.1.continuous
    · exact hρ.2.1.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (ℝ × Vec 2))) (f := fun z => G (z - p)) (g := ρ) (v := e)
    i1 i2 i3 (fun x _ => (hasFDerivAt_comp_sub hG.1 x p).differentiableAt)
    (fun x _ => (hρ.1.differentiable (by simp)) x)
  simp only [hd] at key
  rw [key]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

theorem cutD_mul_fderiv_potential (hG : IsKernelMod G) (hρ : IsRepTest ρ) (i : Fin 2)
    (p : ℝ × Vec 2) :
    cutD i p * fderiv ℝ (potential ρ) p (0, basisVec i) =
      ∫ z, ρ z * (-(kernD G i (z - p)) * cutD i p) := by
  by_cases hD : cutD i p = 0
  · simp [hD]
  · have hp : p ∉ cutW := fun h => hD (cutD_eq_zero h i)
    rw [potential_fderiv hρ.1 hρ.2.1]
    unfold potential
    rw [integral_heat_eq_kernelMod hG hp (φ := fun z => fderiv ℝ ρ z (0, basisVec i))
      (fun z hz => mem_openCyl_of_fderiv_ne_zero hρ hz),
      integral_fderiv_mul_shift hG hρ, mul_neg, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [kernD]
    ring

end
end

/-! # The cutoff test function `ω · Pρ`

For `ρ` a test function supported in `Q_{1/2}`, `ψ = ω · Pρ` is a legitimate test function in
`Q_{3/4}` and `(∂ₛ + Δ) ψ = -ρ + ∫ ρ(z) kern(z, ·) dz`. -/

section
section

variable {G : ℝ × Vec 2 → ℝ} {ρ : ℝ × Vec 2 → ℝ}

theorem potential_terms (hG : IsKernelMod G) (hρ : IsRepTest ρ) (p : ℝ × Vec 2) :
    potential ρ p * cutA p +
        2 * ∑ i : Fin 2, cutD i p * fderiv ℝ (potential ρ) p (0, basisVec i) =
      ∫ z, ρ z * kern G z p := by
  have hsub : Continuous (fun z : ℝ × Vec 2 => z - p) := continuous_id.sub continuous_const
  have hint1 : Integrable (fun z => ρ z * (G (z - p) * cutA p)) :=
    integrable_mul_cont hρ ((hG.1.continuous.comp hsub).mul continuous_const)
  have hint2 : ∀ i : Fin 2,
      Integrable (fun z => ρ z * (-(kernD G i (z - p)) * cutD i p)) := fun i =>
    integrable_mul_cont hρ
      (((contDiff_kernD hG.1 i).continuous.comp hsub).neg.mul continuous_const)
  have hpt : ∀ z, ρ z * kern G z p = ρ z * (G (z - p) * cutA p) +
      2 * ∑ i : Fin 2, ρ z * (-(kernD G i (z - p)) * cutD i p) := by
    intro z
    have : ∑ i : Fin 2, ρ z * (-(kernD G i (z - p)) * cutD i p) =
        -(ρ z * ∑ i : Fin 2, kernD G i (z - p) * cutD i p) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    unfold kern
    ring
  simp_rw [hpt]
  rw [integral_add hint1 ((integrable_finsetSum _ fun i _ => hint2 i).const_mul 2),
    integral_const_mul, integral_finsetSum _ fun i _ => hint2 i,
    ← potential_mul_cutA hG hρ]
  simp_rw [← cutD_mul_fderiv_potential hG hρ]

theorem cutoff_equation (hG : IsKernelMod G) (hρ : IsRepTest ρ) (p : ℝ × Vec 2) :
    stTimeDeriv (fun z => cutω z * potential ρ z) p +
        stSpaceLap (fun z => cutω z * potential ρ z) p =
      -ρ p + ∫ z, ρ z * kern G z p := by
  have hu := potential_contDiff hρ.1 hρ.2.1
  rw [stTimeDeriv_mul cutω_contDiff hu, stSpaceLap_mul cutω_contDiff hu, ← potential_terms hG hρ]
  have h1 := potential_equation hρ.1 hρ.2.1 p
  have h2 := cutω_mul_self hρ p
  have hA : cutA p = stTimeDeriv cutω p + stSpaceLap cutω p := rfl
  have hD : ∀ i : Fin 2, fderiv ℝ cutω p (0, basisVec i) = cutD i p := fun i => rfl
  simp only [hD]
  rw [hA]
  have : cutω p * (stTimeDeriv (potential ρ) p + stSpaceLap (potential ρ) p) = -ρ p := by
    rw [h1, mul_neg, h2]
  linarith

end
end

end AVRegularity.Applications.Caloric
end
end
end

section
@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.Caloric

/-! # Representation of a weakly caloric function against test functions

If `h ∈ L¹(Q_{3/4})` is weakly caloric then for every test function `ρ` supported in `Q_{1/2}`,
`∫ ρ(z) (∫_Q h(p) kern(z,p) dp) dz = ∫_Q h ρ`. -/

section
/-- A compact box containing `Q_{3/4}`. -/
def boxK : Set (ℝ × Vec 2) := Set.Icc (-(9 / 16 : ℝ)) 0 ×ˢ Metric.closedBall (0 : Vec 2) (3 / 4)

theorem isCompact_boxK : IsCompact boxK := isCompact_Icc.prod (isCompact_closedBall _ _)

theorem norm_le_of_vecNormSq_le {y : Vec 2} {c : ℝ} (h : vecNormSq y ≤ c) :
    ‖y‖ ≤ Real.sqrt c := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt ((sq_apply_le_vecNormSq y i).trans h)

theorem isCompact_vecNormSq_le (c : ℝ) : IsCompact {y : Vec 2 | vecNormSq y ≤ c} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_le (contDiff_vecNormSq.continuous) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Vec 2)) (r := Real.sqrt c)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_vecNormSq_le hy

theorem openCyl_subset_boxK : openCyl 0 (3 / 4) ⊆ boxK := by
  intro p hp
  simp only [openCyl, euclidBall, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero,
    sub_zero, Set.mem_ofPred_eq] at hp
  refine ⟨⟨by norm_num at hp ⊢; linarith [hp.1.1], hp.1.2.le⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  have := norm_le_of_vecNormSq_le (c := (3 / 4) ^ 2) hp.2.le
  rwa [Real.sqrt_sq (by norm_num)] at this

section

variable {G : ℝ × Vec 2 → ℝ} {ρ : ℝ × Vec 2 → ℝ}

theorem exists_time_bound (hρ : IsRepTest ρ) : ∃ T : ℝ, T < 0 ∧ ∀ z ∈ tsupport ρ, z.1 < T := by
  by_cases hne : (tsupport ρ).Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := hρ.2.1.isCompact.exists_isMaxOn hne continuous_fst.continuousOn
    have hz₀' := hρ.2.2 hz₀
    simp only [openCyl, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero] at hz₀'
    refine ⟨z₀.1 / 2, by linarith [hz₀'.1.2], fun z hz => ?_⟩
    have := hmax hz
    simp only [Set.mem_ofPred_eq] at this
    linarith [hz₀'.1.2]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨-1, by norm_num, fun z hz => by simp [hne] at hz⟩

theorem isSTTest_cutoff (hρ : IsRepTest ρ) :
    IsSTTest (openCyl 0 (3 / 4)) (fun z => cutω z * potential ρ z) := by
  obtain ⟨T, hT, hTz⟩ := exists_time_bound hρ
  have hρz : ∀ z : ℝ × Vec 2, T ≤ z.1 → ρ z = 0 := fun z hz => by
    by_contra h
    exact absurd (hTz z (subset_tsupport _ h)) (not_lt.mpr hz)
  let C : Set (ℝ × Vec 2) := Set.Icc (-(1 / 2 : ℝ)) T ×ˢ {y : Vec 2 | vecNormSq y ≤ 1 / 2}
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_vecNormSq_le _)
  have hsupp : tsupport (fun z => cutω z * potential ρ z) ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro p hp
    have hp' : cutω p ≠ 0 ∧ potential ρ p ≠ 0 := by
      simpa [Function.mem_support, mul_ne_zero_iff] using hp
    have h1 := cutω_support hp'.1
    have h2 : p.1 < T := by
      by_contra h
      exact hp'.2 (potential_eq_zero hρz p (not_lt.mp h))
    exact ⟨⟨h1.1.le, h2.le⟩, h1.2.le⟩
  have hCsub : C ⊆ openCyl 0 (3 / 4) := by
    intro p hp
    simp only [C, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq] at hp
    simp only [openCyl, euclidBall, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero,
      sub_zero, Set.mem_ofPred_eq]
    refine ⟨⟨by norm_num; linarith [hp.1.1], by linarith [hp.1.2]⟩, by norm_num; linarith [hp.2]⟩
  exact ⟨cutω_contDiff.mul (potential_contDiff hρ.1 hρ.2.1),
    HasCompactSupport.of_support_subset_isCompact hC
      ((subset_tsupport _).trans hsupp), hsupp.trans hCsub⟩

end

theorem isOpen_openCyl (z : ℝ × Vec 2) (r : ℝ) : IsOpen (openCyl z r) := by
  have h2 : Continuous (fun y : Vec 2 => vecNormSq (y - z.2)) :=
    contDiff_vecNormSq.continuous.comp (continuous_id.sub continuous_const)
  exact isOpen_Ioo.prod (isOpen_lt h2 continuous_const)

theorem continuous_stOps {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (fun p => stTimeDeriv φ p + stSpaceLap φ p) := by
  have h1 : Continuous (stTimeDeriv φ) := (contDiff_fderiv_dir_apply hφ (1, 0)).continuous
  have h2 : Continuous (stSpaceLap φ) := by
    unfold stSpaceLap
    exact continuous_finsetSum _ fun i _ => (contDiff_fderiv_dir_apply (contDiff_fderiv_dir_apply hφ _) _).continuous
  exact h1.add h2

section

variable {G : ℝ × Vec 2 → ℝ} {ρ : ℝ × Vec 2 → ℝ}

theorem representation_identity (hG : IsKernelMod G) {h : ℝ × Vec 2 → ℝ}
    (hh : IntegrableOn h (openCyl 0 (3 / 4)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 (3 / 4)) φ →
      ∫ p in openCyl 0 (3 / 4), h p * (stTimeDeriv φ p + stSpaceLap φ p) = 0)
    (hρ : IsRepTest ρ) :
    ∫ z, ρ z * (∫ p in openCyl 0 (3 / 4), h p * kern G z p) =
      ∫ p in openCyl 0 (3 / 4), h p * ρ p := by
  set Q := openCyl 0 (3 / 4) with hQ
  have hQm : MeasurableSet Q := (isOpen_openCyl _ _).measurableSet
  have hQK : Q ⊆ boxK := openCyl_subset_boxK
  set E : ℝ × Vec 2 → ℝ := fun p => ∫ z, ρ z * kern G z p with hE
  set ψ : ℝ × Vec 2 → ℝ := fun z => cutω z * potential ρ z with hψ
  have hψt := isSTTest_cutoff hρ
  have hLc := continuous_stOps hψt.1
  have hL : ∀ p, stTimeDeriv ψ p + stSpaceLap ψ p = -ρ p + E p := fun p => cutoff_equation hG hρ p
  have hI1 : IntegrableOn (fun p => h p * (stTimeDeriv ψ p + stSpaceLap ψ p)) Q :=
    hh.mul_continuousOn_of_subset hLc.continuousOn hQm isCompact_boxK hQK
  have hI2 : IntegrableOn (fun p => h p * ρ p) Q :=
    hh.mul_continuousOn_of_subset hρ.1.continuous.continuousOn hQm isCompact_boxK hQK
  have hsplit : ∫ p in Q, h p * E p =
      (∫ p in Q, h p * (stTimeDeriv ψ p + stSpaceLap ψ p)) + ∫ p in Q, h p * ρ p := by
    rw [show (∫ p in Q, h p * E p) = ∫ p in Q, (h p * (stTimeDeriv ψ p + stSpaceLap ψ p) + h p * ρ p)
      from setIntegral_congr_fun hQm fun p _ => by simp only [hL]; ring]
    exact integral_add hI1 hI2
  rw [hweak ψ hψt, zero_add] at hsplit
  rw [← hsplit]
  -- Fubini
  set h₀ : ℝ × Vec 2 → ℝ := Q.indicator h with hh₀def
  have hh₀ : Integrable h₀ := (integrable_indicator_iff hQm).mpr hh
  have hρint : Integrable ρ := by
    simpa using integrable_mul_cont hρ (continuous_const (y := (1 : ℝ)))
  obtain ⟨M, hM⟩ := exists_kern_bound hG.1 hρ.2.1.isCompact isCompact_boxK
  have hint : Integrable (fun x : (ℝ × Vec 2) × (ℝ × Vec 2) =>
      h₀ x.1 * (ρ x.2 * kern G x.2 x.1)) (volume.prod volume) := by
    refine Integrable.mono' (g := fun x => max M 0 * (‖h₀ x.1‖ * ‖ρ x.2‖)) ?_ ?_ ?_
    · exact (hh₀.norm.mul_prod hρint.norm).const_mul _
    · exact (hh₀.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
        ((hρ.1.continuous.comp continuous_snd).mul
          ((contDiff_kern hG.1).continuous.comp continuous_swap)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases h0 : h₀ x.1 = 0
      · simp [h0]
      by_cases r0 : ρ x.2 = 0
      · simp [r0]
      have hp : x.1 ∈ Q := by
        by_contra hn
        exact h0 (by simp [hh₀def, hn])
      have hk := hM x.2 (subset_tsupport _ r0) x.1 (hQK hp)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (kern G _ _)]
      calc ‖h₀ x.1‖ * (‖ρ x.2‖ * |kern G x.2 x.1|)
          ≤ ‖h₀ x.1‖ * (‖ρ x.2‖ * max M 0) := by
            gcongr; exact hk.trans (le_max_left _ _)
        _ = max M 0 * (‖h₀ x.1‖ * ‖ρ x.2‖) := by ring
  have hswap := integral_integral_swap (f := fun p z => h₀ p * (ρ z * kern G z p)) hint
  refine Eq.symm ?_
  calc ∫ p in Q, h p * E p = ∫ p, h₀ p * E p := by
        rw [← integral_indicator hQm]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        by_cases hp : p ∈ Q <;> simp [hh₀def, hp]
    _ = ∫ p, ∫ z, h₀ p * (ρ z * kern G z p) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [hE]
        rw [integral_const_mul]
    _ = ∫ z, ∫ p, h₀ p * (ρ z * kern G z p) := hswap
    _ = ∫ z, ρ z * (∫ p in Q, h p * kern G z p) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_indicator hQm, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        by_cases hp : p ∈ Q <;> simp [hh₀def, hp, mul_left_comm]

end
end

/-! # Interior Lipschitz estimate for weakly caloric functions

Used for the one-step decay (8.6) in the proof of Lemma 3.3 of the paper. -/

section
/-- A compact convex box containing the cylinder `Q_{1/2}`. -/
def boxZ : Set (ℝ × Vec 2) := Set.Icc (-(1 / 4 : ℝ)) 0 ×ˢ Metric.closedBall (0 : Vec 2) (1 / 2)

theorem isCompact_boxZ : IsCompact boxZ := isCompact_Icc.prod (isCompact_closedBall _ _)

theorem convex_boxZ : Convex ℝ boxZ := (convex_Icc _ _).prod (convex_closedBall _ _)

theorem cylinder_subset_boxZ : External.Campanato.cylinder 0 (1 / 2) ⊆ boxZ := by
  intro p hp
  simp only [External.Campanato.cylinder, euclidBall, Set.mem_prod, Set.mem_Ioc, Prod.fst_zero,
    Prod.snd_zero, sub_zero, Set.mem_ofPred_eq] at hp
  refine ⟨⟨by norm_num at hp ⊢; linarith [hp.1.1], hp.1.2⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  have := norm_le_of_vecNormSq_le (c := (1 / 2) ^ 2) hp.2.le
  rwa [Real.sqrt_sq (by norm_num)] at this

theorem openCyl_half_subset_boxZ : openCyl 0 (1 / 2) ⊆ boxZ := by
  refine Set.Subset.trans ?_ cylinder_subset_boxZ
  intro p hp
  simp only [openCyl, External.Campanato.cylinder, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.le⟩, hp.2⟩

theorem openCyl_half_subset_three_quarters : openCyl 0 (1 / 2) ⊆ openCyl 0 (3 / 4) := by
  intro p hp
  simp only [openCyl, euclidBall, Set.mem_prod, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero,
    sub_zero, Set.mem_ofPred_eq] at hp ⊢
  refine ⟨⟨by norm_num at hp ⊢; linarith [hp.1.1], hp.1.2⟩, by norm_num at hp ⊢; linarith [hp.2]⟩

section

variable {G : ℝ × Vec 2 → ℝ}

/-- The representing function `F(z) = ∫_Q h(p) kern(z,p) dp`. -/
def repFun (G : ℝ × Vec 2 → ℝ) (h : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) : ℝ :=
  ∫ p in openCyl 0 (3 / 4), h p * kern G z p

theorem integrableOn_mul_kern (hG : IsKernelMod G) {h : ℝ × Vec 2 → ℝ}
    (hh : IntegrableOn h (openCyl 0 (3 / 4))) (z : ℝ × Vec 2) :
    IntegrableOn (fun p => h p * kern G z p) (openCyl 0 (3 / 4)) :=
  hh.mul_continuousOn_of_subset
    ((contDiff_kern hG.1).continuous.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
    (isOpen_openCyl _ _).measurableSet isCompact_boxK openCyl_subset_boxK

theorem exists_repFun_lipschitz (hG : IsKernelMod G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ × Vec 2 → ℝ, IntegrableOn h (openCyl 0 (3 / 4)) →
      ∀ z ∈ boxZ, ∀ w ∈ boxZ,
        |repFun G h z - repFun G h w| ≤ C * ‖z - w‖ * ∫ p in openCyl 0 (3 / 4), |h p| := by
  obtain ⟨C, hC0, hC⟩ := exists_kern_lipschitz hG.1 isCompact_boxZ convex_boxZ isCompact_boxK
  refine ⟨C, hC0, fun h hh z hz w hw => ?_⟩
  have hQm : MeasurableSet (openCyl 0 (3 / 4)) := (isOpen_openCyl _ _).measurableSet
  unfold repFun
  rw [← integral_sub (integrableOn_mul_kern hG hh z) (integrableOn_mul_kern hG hh w)]
  rw [← Real.norm_eq_abs]
  have hg : Integrable (fun p => C * ‖z - w‖ * |h p|) (volume.restrict (openCyl 0 (3 / 4))) :=
    hh.norm.const_mul _
  refine (norm_integral_le_of_norm_le hg ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' hQm).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hk := hC w hw z hz p (openCyl_subset_boxK hp)
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm (C * ‖z - w‖)]
    rw [norm_sub_rev] at hk
    gcongr
    simpa [norm_sub_rev] using hk
  · rw [integral_const_mul]

theorem repFun_continuousOn (hG : IsKernelMod G) {h : ℝ × Vec 2 → ℝ}
    (hh : IntegrableOn h (openCyl 0 (3 / 4))) : ContinuousOn (repFun G h) boxZ := by
  obtain ⟨C, _, hC⟩ := exists_repFun_lipschitz hG
  have hL : ∃ K : NNReal, LipschitzOnWith K (repFun G h) boxZ := by
    refine ⟨⟨C * ∫ p in openCyl 0 (3 / 4), |h p|, ?_⟩, ?_⟩
    · exact mul_nonneg ‹_› (integral_nonneg fun p => abs_nonneg _)
    · refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
      rw [Real.dist_eq, dist_eq_norm]
      show |_| ≤ (C * ∫ p in openCyl 0 (3 / 4), |h p|) * ‖z - w‖
      calc _ ≤ C * ‖z - w‖ * ∫ p in openCyl 0 (3 / 4), |h p| := hC h hh z hz w hw
        _ = _ := by ring
  obtain ⟨K, hK⟩ := hL
  exact hK.continuousOn

end
end

end AVRegularity.Applications.Caloric
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Interior Lipschitz estimate for weakly caloric functions (final assembly)

A weakly caloric `h ∈ L¹(Q_{3/4})` agrees a.e. on `Q_{1/2}` with a function that is Lipschitz
with constant `C₁ ‖h‖_{L¹(Q_{3/4})}`. The representing function is `∫_Q h(p) kern(z,p) dp`, for
which the identity with `h` is proved by duality against test functions through the backward heat
potential. -/

open Caloric

theorem caloric_ae_eq_repFun {G : ℝ × Vec 2 → ℝ} (hG : IsKernelMod G) {h : ℝ × Vec 2 → ℝ}
    (hh : IntegrableOn h (openCyl 0 (3 / 4)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 (3 / 4)) φ →
      ∫ p in openCyl 0 (3 / 4), h p * (stTimeDeriv φ p + stSpaceLap φ p) = 0) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Vec 2)), z ∈ openCyl 0 (1 / 2) → repFun G h z = h z := by
  set U := openCyl 0 (1 / 2) with hU
  set Q := openCyl 0 (3 / 4) with hQ
  have hUo : IsOpen U := isOpen_openCyl _ _
  have hUQ : U ⊆ Q := openCyl_half_subset_three_quarters
  have hUZ : U ⊆ boxZ := openCyl_half_subset_boxZ
  have hFc : ContinuousOn (repFun G h) boxZ := repFun_continuousOn hG hh
  have hloc : LocallyIntegrableOn (fun z => repFun G h z - h z) U := by
    refine LocallyIntegrableOn.sub ?_ ((hh.mono_set hUQ).locallyIntegrableOn)
    exact (hFc.mono hUZ).locallyIntegrableOn hUo.measurableSet
  have key := hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [key] with z hz hzU
    exact sub_eq_zero.mp (hz hzU)
  · intro g hg hgc hgU
    have hρ : IsRepTest g := ⟨hg, hgc, hgU⟩
    have hrep := representation_identity hG hh hweak hρ
    have hgF : Integrable (fun z => g z * repFun G h z) := by
      rw [← integrableOn_iff_integrable_of_support_subset (s := boxZ)]
      · exact (hg.continuous.continuousOn.mul hFc).integrableOn_compact isCompact_boxZ
      · intro z hz
        exact hUZ (hgU (subset_tsupport _ (left_ne_zero_of_mul hz)))
    have hgh : Integrable (fun z => g z * h z) := by
      rw [← integrableOn_iff_integrable_of_support_subset (s := Q)]
      · exact hh.continuousOn_mul_of_subset hg.continuous.continuousOn isCompact_boxK
          (isOpen_openCyl _ _).measurableSet openCyl_subset_boxK |> fun h' =>
            (by simpa [mul_comm] using h')
      · intro z hz
        exact hUQ (hgU (subset_tsupport _ (left_ne_zero_of_mul hz)))
    have hgh' : ∫ z, g z * h z = ∫ p in Q, h p * g p := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Q)]
      · exact setIntegral_congr_fun (isOpen_openCyl _ _).measurableSet fun p _ => mul_comm _ _
      · intro z hz
        by_contra hne
        exact hz (hUQ (hgU (subset_tsupport _ (left_ne_zero_of_mul hne))))
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub hgF hgh, hgh']
    exact sub_eq_zero.mpr hrep

theorem caloric_interior_lipschitz :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ h : ℝ × Vec 2 → ℝ,
      IntegrableOn h (openCyl 0 (3 / 4)) →
      (∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 (3 / 4)) φ →
        ∫ p in openCyl 0 (3 / 4), h p * (stTimeDeriv φ p + stSpaceLap φ p) = 0) →
      ∃ hh : ℝ × Vec 2 → ℝ,
        hh =ᵐ[volume.restrict (External.Campanato.cylinder 0 (1 / 2))] h ∧
        ∀ z ∈ External.Campanato.cylinder 0 (1 / 2), ∀ w ∈ External.Campanato.cylinder 0 (1 / 2),
          |hh z - hh w| ≤ C₁ * (|z.1 - w.1| + Real.sqrt (vecNormSq (z.2 - w.2))) *
            ∫ p in openCyl 0 (3 / 4), |h p| := by
  obtain ⟨G, hGs, hGe⟩ := exists_smooth_heatKernel
  have hG : IsKernelMod G := ⟨hGs, hGe⟩
  obtain ⟨C, hC0, hC⟩ := exists_repFun_lipschitz hG
  refine ⟨C, hC0, fun h hh hweak => ⟨repFun G h, ?_, ?_⟩⟩
  · have hball : IsOpen (euclidBall (0 : Vec 2) (1 / 2)) :=
      isOpen_lt (contDiff_vecNormSq.continuous.comp (continuous_id.sub continuous_const))
        continuous_const
    have hmeas : MeasurableSet (External.Campanato.cylinder 0 (1 / 2)) :=
      measurableSet_Ioc.prod hball.measurableSet
    have h0 : ∀ᵐ t : ℝ ∂volume, t ∉ ({0} : Set ℝ) := (Set.countable_singleton 0).ae_notMem _
    have h1 : ∀ᵐ z : ℝ × Vec 2 ∂volume, z.1 ∉ ({0} : Set ℝ) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae h0
    refine (ae_restrict_iff' hmeas).mpr ?_
    filter_upwards [caloric_ae_eq_repFun hG hh hweak, h1] with z hz1 hz2 hzc
    apply hz1
    simp only [External.Campanato.cylinder, openCyl, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo,
      Prod.fst_zero, euclidBall, Prod.snd_zero, sub_zero, Set.mem_ofPred_eq] at hzc ⊢
    exact ⟨⟨hzc.1.1, lt_of_le_of_ne hzc.1.2 (by simpa using hz2)⟩, hzc.2⟩
  · intro z hz w hw
    have hI : 0 ≤ ∫ p in openCyl 0 (3 / 4), |h p| := integral_nonneg fun p => abs_nonneg _
    refine (hC h hh z (cylinder_subset_boxZ hz) w (cylinder_subset_boxZ hw)).trans ?_
    have hnorm : ‖z - w‖ ≤ |z.1 - w.1| + Real.sqrt (vecNormSq (z.2 - w.2)) := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · simp only [Prod.fst_sub, Real.norm_eq_abs]
        linarith [Real.sqrt_nonneg (vecNormSq (z.2 - w.2))]
      · simp only [Prod.snd_sub]
        have := norm_le_of_vecNormSq_le (le_refl (vecNormSq (z.2 - w.2)))
        linarith [abs_nonneg (z.1 - w.1)]
    gcongr

end AVRegularity.Applications
end
end
end
end
