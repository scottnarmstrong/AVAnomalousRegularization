-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Pipe.LocalEnergy
public import AVRegularity.Applications.Local.LabelTrace
import AVRegularity.Applications.LocalEnergy.MolEnergy
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.TorusEnergy.StreamFacts
import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Limit
import AVRegularity.Velocity.IncrementProvider
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Generic facts on local weak solutions

Restriction to a subset, subtraction, integrability of the weak form against a test, and slice
integration by parts over the time sections of an arbitrary space-time set `O`. -/

theorem fderiv_apply_eq_zero_of_notMem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {x : E} (hx : x ∉ tsupport φ) (v : E) : fderiv ℝ φ x v = 0 := by
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

theorem stIntegrand_eq_zero {v : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u : ℝ × Vec 2 → ℝ}
    {Du : ℝ × Vec 2 → Vec 2} {φ : ℝ × Vec 2 → ℝ} {p : ℝ × Vec 2} (hp : p ∉ tsupport φ) :
    (-(u p * stTimeDeriv φ p) + vecDot (v p.1 p.2) (Du p) * φ p
      + κ * vecDot (Du p) (stSpaceGrad φ p)) = 0 := by
  obtain ⟨h1, h2, -⟩ := st_derivs_zero hp
  have h3 : φ p = 0 := image_eq_zero_of_notMem_tsupport hp
  simp [h1, h2, h3, vecDot]

theorem integrableOn_of_memLp_compact {K : Set (ℝ × Vec 2)} (hK : IsCompact K)
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict K)) : IntegrableOn f K := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact hf.integrable (by norm_num)

/-- The time slice of a space-time test is a spatial test in the time section. -/
theorem sliceTest_section {O : Set (ℝ × Vec 2)} {ψ : ℝ × Vec 2 → ℝ} (hψ : IsSTTest O ψ)
    (t : ℝ) : IsSpTest (timeSection O t) (fun y => ψ (t, y)) := by
  obtain ⟨hsm, hcs, hts⟩ := hψ
  have hcont : Continuous (fun y : Vec 2 => (t, y)) := continuous_const.prodMk continuous_id
  have hsub : tsupport (fun y => ψ (t, y)) ⊆ (fun y : Vec 2 => (t, y)) ⁻¹' tsupport ψ := by
    refine closure_minimal ?_ (isClosed_tsupport ψ |>.preimage hcont)
    intro y hy
    exact subset_closure hy
  refine ⟨hsm.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
  · refine IsCompact.of_isClosed_subset (hcs.image continuous_snd) (isClosed_tsupport _) ?_
    intro y hy
    exact ⟨(t, y), hsub hy, rfl⟩
  · intro y hy
    exact hts (hsub hy)

/-- Weak gradients restrict to subsets. -/
theorem hasWeakGradientOn_mono {B B' : Set (Vec 2)} (hBB : B' ⊆ B) {u : Vec 2 → ℝ}
    {Du : Vec 2 → Vec 2} (h : HasWeakGradientOn B u Du) : HasWeakGradientOn B' u Du := by
  intro i φ hφ hc hts
  have := h i φ hφ hc (hts.trans hBB)
  have e1 : ∫ x in B, u x * fderiv ℝ φ x (basisVec i) = ∫ x in B', u x * fderiv ℝ φ x (basisVec i) := by
    rw [setIntegral_eq_integral_of_tsupport (g := φ) (hts.trans hBB) fun x hx => by
        simp [fderiv_apply_eq_zero_of_notMem hx],
      setIntegral_eq_integral_of_tsupport (g := φ) hts fun x hx => by
        simp [fderiv_apply_eq_zero_of_notMem hx]]
  have e2 : ∫ x in B, Du x i * φ x = ∫ x in B', Du x i * φ x := by
    rw [setIntegral_eq_integral_of_tsupport (g := φ) (hts.trans hBB) fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx],
      setIntegral_eq_integral_of_tsupport (g := φ) hts fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]]
  rw [← e1, ← e2]
  exact this

theorem IsLocalWeakSolution.mono {v : ℝ → Vec 2 → Vec 2} {κ : ℝ} {O O' : Set (ℝ × Vec 2)}
    {u : ℝ × Vec 2 → ℝ} {Du : ℝ × Vec 2 → Vec 2} (h : IsLocalWeakSolution v κ O u Du)
    (hO : O' ⊆ O) : IsLocalWeakSolution v κ O' u Du := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun K hK hc => h1 K (hK.trans hO) hc, fun K hK hc i => h2 K (hK.trans hO) hc i,
    ?_, ?_⟩
  · filter_upwards [h3] with t ht
    exact hasWeakGradientOn_mono (fun x hx => hO hx) ht
  · intro φ hφ
    have hφ' : IsSTTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hO⟩
    have := h4 φ hφ'
    rw [setIntegral_eq_integral_of_tsupport (g := φ) hφ'.2.2 fun p hp => stIntegrand_eq_zero hp]
      at this
    rwa [setIntegral_eq_integral_of_tsupport (g := φ) hφ.2.2 fun p hp => stIntegrand_eq_zero hp]

/-- The weak form of a local weak solution is integrable on `O` against every test. -/
theorem localWeak_integrand_integrable {v : ℝ → Vec 2 → Vec 2} {κ B : ℝ}
    {O : Set (ℝ × Vec 2)} {u : ℝ × Vec 2 → ℝ} {Du : ℝ × Vec 2 → Vec 2}
    (hvm : Measurable fun p : ℝ × Vec 2 => v p.1 p.2) (hvB : ∀ t x, ‖v t x‖ ≤ B)
    (h : IsLocalWeakSolution v κ O u Du) {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest O φ) :
    Integrable (fun p => -(u p * stTimeDeriv φ p) + vecDot (v p.1 p.2) (Du p) * φ p
      + κ * vecDot (Du p) (stSpaceGrad φ p)) (volume.restrict O) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hu : ∀ K ⊆ O, IsCompact K → IntegrableOn u K := fun K hK hc =>
    integrableOn_of_memLp_compact hc (h1 K hK hc)
  have hD : ∀ i : Fin 2, ∀ K ⊆ O, IsCompact K → IntegrableOn (fun p => Du p i) K :=
    fun i K hK hc => integrableOn_of_memLp_compact hc (h2 K hK hc i)
  have hcont : Continuous (stTimeDeriv φ) :=
    (contDiff_fderiv_apply_of_smooth hφ.1 ((1 : ℝ), (0 : Vec 2))).continuous
  have hcs : HasCompactSupport (stTimeDeriv φ) := hasCompactSupport_fderiv_apply hφ.2.1 _
  have hts : tsupport (stTimeDeriv φ) ⊆ O := (tsupport_fderiv_apply_subset φ _).trans hφ.2.2
  have i1 : IntegrableOn (fun p => u p * stTimeDeriv φ p) O :=
    integrableOn_mul_of_support hu hcont hcs hts
  have hvD : ∀ K ⊆ O, IsCompact K →
      IntegrableOn (fun p => vecDot (v p.1 p.2) (Du p)) K := by
    intro K hK hc
    simp only [vecDot]
    refine integrable_finsetSum _ fun i _ => ?_
    exact (hD i K hK hc).bdd_mul (c := B) ((measurable_pi_apply i).comp hvm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (norm_le_pi_norm (v p.1 p.2) i).trans (hvB _ _))
  have i2 : IntegrableOn (fun p => vecDot (v p.1 p.2) (Du p) * φ p) O :=
    integrableOn_mul_of_support hvD hφ.1.continuous hφ.2.1 hφ.2.2
  have i3 : ∀ i : Fin 2, IntegrableOn (fun p => Du p i * stSpaceGrad φ p i) O := fun i =>
    integrableOn_mul_of_support (hD i)
      (contDiff_fderiv_apply_of_smooth hφ.1 (0, basisVec i)).continuous
      (hasCompactSupport_fderiv_apply hφ.2.1 _)
      ((tsupport_fderiv_apply_subset φ _).trans hφ.2.2)
  have i3' : IntegrableOn (fun p => vecDot (Du p) (stSpaceGrad φ p)) O := by
    simp only [vecDot]
    exact integrable_finsetSum _ fun i _ => i3 i
  exact (i1.neg.add i2).add (i3'.const_mul κ)

/-- Subtraction of local weak solutions, given slice integrability. -/
theorem IsLocalWeakSolution.sub {v : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {O : Set (ℝ × Vec 2)}
    {u₁ u₂ : ℝ × Vec 2 → ℝ} {D₁ D₂ : ℝ × Vec 2 → Vec 2}
    (hvm : Measurable fun p : ℝ × Vec 2 => v p.1 p.2) (hvB : ∀ t x, ‖v t x‖ ≤ B)
    (h₁ : IsLocalWeakSolution v κ O u₁ D₁) (h₂ : IsLocalWeakSolution v κ O u₂ D₂)
    (hs₁ : ∀ᵐ t ∂(volume : Measure ℝ), IntegrableOn (fun x => u₁ (t, x)) (timeSection O t) ∧
      ∀ i : Fin 2, IntegrableOn (fun x => D₁ (t, x) i) (timeSection O t))
    (hs₂ : ∀ᵐ t ∂(volume : Measure ℝ), IntegrableOn (fun x => u₂ (t, x)) (timeSection O t) ∧
      ∀ i : Fin 2, IntegrableOn (fun x => D₂ (t, x) i) (timeSection O t)) :
    IsLocalWeakSolution v κ O (fun p => u₁ p - u₂ p) (fun p => D₁ p - D₂ p) := by
  have e₁ := h₁
  have e₂ := h₂
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨fun K hK hc => (a1 K hK hc).sub (a2 K hK hc),
    fun K hK hc i => (b1 K hK hc i).sub (b2 K hK hc i), ?_, ?_⟩
  · filter_upwards [c1, c2, hs₁, hs₂] with t g1 g2 i1 i2
    intro i φ hφ hc hts
    have hb : ∀ {w : Vec 2 → ℝ}, IntegrableOn w (timeSection O t) →
        Integrable (fun x => w x * fderiv ℝ φ x (basisVec i)) (volume.restrict (timeSection O t)) := by
      intro w hw
      obtain ⟨C, hC⟩ := (contDiff_fderiv_apply_of_smooth hφ (basisVec i)).continuous
        |>.bounded_above_of_compact_support (hasCompactSupport_fderiv_apply hc _)
      exact hw.mul_bdd (c := C)
        (contDiff_fderiv_apply_of_smooth hφ (basisVec i)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)
    have hb' : ∀ {w : Vec 2 → ℝ}, IntegrableOn w (timeSection O t) →
        Integrable (fun x => w x * φ x) (volume.restrict (timeSection O t)) := by
      intro w hw
      obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
      exact hw.mul_bdd (c := C) hφ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hC)
    have x1 := g1 i φ hφ hc hts
    have x2 := g2 i φ hφ hc hts
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub (hb i1.1) (hb i2.1), integral_sub (hb' (i1.2 i)) (hb' (i2.2 i)), x1, x2]
    ring
  · intro φ hφ
    have k1 := localWeak_integrand_integrable hvm hvB e₁ hφ
    have k2 := localWeak_integrand_integrable hvm hvB e₂ hφ
    have := (d1 φ hφ)
    have := (d2 φ hφ)
    have hfun : ∀ p, (-((u₁ p - u₂ p) * stTimeDeriv φ p) +
        vecDot (v p.1 p.2) (D₁ p - D₂ p) * φ p + κ * vecDot (D₁ p - D₂ p) (stSpaceGrad φ p)) =
        (-(u₁ p * stTimeDeriv φ p) + vecDot (v p.1 p.2) (D₁ p) * φ p
          + κ * vecDot (D₁ p) (stSpaceGrad φ p)) -
        (-(u₂ p * stTimeDeriv φ p) + vecDot (v p.1 p.2) (D₂ p) * φ p
          + κ * vecDot (D₂ p) (stSpaceGrad φ p)) := by
      intro p
      simp only [vecDot, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub, sub_mul]
      ring
    simp_rw [hfun]
    rw [integral_sub k1 k2, d1 φ hφ, d2 φ hφ, sub_zero]

/-- Slice integration by parts over the time sections of `O` for locally integrable `H`, `g`. -/
theorem integral_mul_partial_section {O : Set (ℝ × Vec 2)} {H g : ℝ × Vec 2 → ℝ} (i : Fin 2)
    (hH : ∀ K ⊆ O, IsCompact K → IntegrableOn H K)
    (hg : ∀ K ⊆ O, IsCompact K → IntegrableOn g K)
    (hgrad : ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakPartialDerivOn (timeSection O t) i (fun x => H (t, x)) (fun x => g (t, x)))
    {ψ : ℝ × Vec 2 → ℝ} (hψ : IsSTTest O ψ) :
    ∫ p in O, H p * fderiv ℝ ψ p (0, basisVec i) = -∫ p in O, g p * ψ p := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hdc : Continuous fun p => fderiv ℝ ψ p (0, basisVec i) :=
    (contDiff_fderiv_apply_of_smooth hψ.1 _).continuous
  have hdcs := hasCompactSupport_fderiv_apply hψ.2.1 (((0 : ℝ), basisVec i) : ℝ × Vec 2)
  have hdts := tsupport_fderiv_apply_subset ψ (((0 : ℝ), basisVec i) : ℝ × Vec 2)
  have hz1 : ∀ p, p ∉ tsupport ψ → H p * fderiv ℝ ψ p (0, basisVec i) = 0 := fun p hp => by
    simp [fderiv_apply_eq_zero_of_notMem hp]
  have hz2 : ∀ p, p ∉ tsupport ψ → g p * ψ p = 0 := fun p hp => by
    simp [image_eq_zero_of_notMem_tsupport hp]
  have hK : IsCompact (tsupport ψ) := hψ.2.1
  have hI1 : Integrable (fun p => H p * fderiv ℝ ψ p (0, basisVec i)) volume := by
    have h0 : IntegrableOn (fun p => H p * fderiv ℝ ψ p (0, basisVec i)) (tsupport ψ) :=
      integrableOn_mul_of_support (S := tsupport ψ)
        (fun K hKs hKc => (hH K (hKs.trans hψ.2.2) hKc)) hdc hdcs hdts
    exact h0.integrable_of_forall_notMem_eq_zero hz1
  have hI2 : Integrable (fun p => g p * ψ p) volume := by
    have h0 : IntegrableOn (fun p => g p * ψ p) (tsupport ψ) :=
      integrableOn_mul_of_support (S := tsupport ψ)
        (fun K hKs hKc => (hg K (hKs.trans hψ.2.2) hKc)) hψc hψ.2.1 subset_rfl
    exact h0.integrable_of_forall_notMem_eq_zero hz2
  rw [setIntegral_eq_integral_of_tsupport (g := ψ) hψ.2.2 hz1,
    setIntegral_eq_integral_of_tsupport (g := ψ) hψ.2.2 hz2]
  rw [Measure.volume_eq_prod] at hI1 hI2 ⊢
  rw [integral_prod _ hI1, integral_prod _ hI2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hgrad] with t ht
  have hs := sliceTest_section hψ t
  have h := ht (fun y => ψ (t, y)) hs.1 hs.2.1 hs.2.2
  simp only [fderiv_slice hψ.1] at h
  rw [setIntegral_eq_integral_of_tsupport (g := fun y => ψ (t, y)) hs.2.2 (fun x hx => by
      have : fderiv ℝ ψ (t, x) (0, basisVec i) = 0 := by
        rw [← fderiv_slice hψ.1 t x]; exact fderiv_apply_eq_zero_of_notMem hx _
      simp [this]),
    setIntegral_eq_integral_of_tsupport (g := fun y => ψ (t, y)) hs.2.2 (fun x hx => by
      have : ψ (t, x) = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => ψ (t, y)) hx
      simp [this])] at h
  exact h

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix
namespace AVRegularity.Applications

/-! # Weak gradients through the material chart

If `U_t = θ_t ∘ F_t` has weak gradient `DU_t` on `B`, then `θ_t` has weak gradient
`physGrad X t₁ DU (t,·) = (adj D F_t ∘ H_t)ᵀ DU_t ∘ H_t` on `F_t(B)`. The proof is the change of
variables `x = F_t y`, with the 2D Piola identity `Σⱼ ∂ⱼ (adj DF)ⱼᵢ = 0` absorbing the derivative
of the Jacobian. -/

section
/-- The physical gradient `Dθ(t,x) = (adj D_yF_t(H_t x))ᵀ DU(t, H_t x)` of a pulled-back
function with label gradient `DU`. -/
def physGrad (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (DU : ℝ → Vec 2 → Vec 2)
    (p : ℝ × Vec 2) : Vec 2 :=
  (pipeAdj X t₁ (p.1, X t₁ p.2 p.1))ᵀ.mulVec (DU p.1 (X t₁ p.2 p.1))

section Chart

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

theorem physGrad_chart {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (DU : ℝ → Vec 2 → Vec 2)
    (y : Vec 2) :
    physGrad X t₁ DU (t, X t y t₁) = (pipeAdj X t₁ (t, y))ᵀ.mulVec (DU t y) := by
  simp [physGrad, ch.left t ht y]

theorem chart_image_integral {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (g : Vec 2 → ℝ)
    (B : Set (Vec 2)) :
    ∫ x in (fun y => X t y t₁) '' B, g x = ∫ y in B, g (X t y t₁) :=
  (ch.mp t ht).setIntegral_image_emb (chartHomeo ch ht).measurableEmbedding g B

theorem chart_injective {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) :
    Function.Injective (fun y => X t y t₁) := (chartHomeo ch ht).injective

omit ch in
theorem integrableOn_mul_cts' {B : Set (Vec 2)} {w f : Vec 2 → ℝ} (hw : IntegrableOn w B)
    (hf : Continuous f) (hc : HasCompactSupport f) : IntegrableOn (fun y => w y * f y) B := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  exact hw.mul_bdd (c := C) hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The pullback gradient identity: `∇ψ(F y) = (adj DF(y))ᵀ ∇(ψ∘F)(y)`. -/
theorem spGrad_chart {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec 2) (i : Fin 2) :
    spGrad ψ (X t y t₁) i =
      ∑ j : Fin 2, (jacMat (fun z => X t z t₁) y).adjugate j i *
        spGrad (ψ ∘ fun z => X t z t₁) y j := by
  have hF := ((contDiff_Ft ch t).differentiable (by simp)) y
  have hψd := (hψ.differentiable (by simp)) (X t y t₁)
  have hcomp := spGrad_comp hψd hF
  set J := jacMat (fun z => X t z t₁) y with hJ
  have hdet : J.det = 1 := by
    have := jacMat_det_one ch ht y
    simpa [pipeJac] using this
  have hAJ : J * J.adjugate = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  have hg : spGrad ψ (X t y t₁) = (J.adjugate)ᵀ.mulVec (spGrad (ψ ∘ fun z => X t z t₁) y) := by
    rw [hcomp, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hAJ, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [hg]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem hasWeakGradientOn_chart_image {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)
    {B : Set (Vec 2)} {θt : Vec 2 → ℝ} {DU : ℝ → Vec 2 → Vec 2}
    (hU : IntegrableOn (fun y => θt (X t y t₁)) B)
    (hD : ∀ j : Fin 2, IntegrableOn (fun y => DU t y j) B)
    (hw : HasWeakGradientOn B (fun y => θt (X t y t₁)) (DU t)) :
    HasWeakGradientOn ((fun y => X t y t₁) '' B) θt
      (fun x => physGrad X t₁ DU (t, x)) := by
  intro i ψ hψ hψc hψts
  set F : Vec 2 → Vec 2 := fun y => X t y t₁ with hFdef
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_Ft ch t
  set η : Vec 2 → ℝ := ψ ∘ F with hη
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η := hψ.comp hFs
  have hηc : HasCompactSupport η := hψc.comp_homeomorph (chartHomeo ch ht)
  have hηB : tsupport η ⊆ B := by
    have h1 : tsupport η ⊆ F ⁻¹' tsupport ψ := by
      refine closure_minimal ?_ ((isClosed_tsupport ψ).preimage hFs.continuous)
      intro y hy
      exact subset_closure hy
    intro y hy
    obtain ⟨y', hy', hyy⟩ := hψts (h1 hy)
    rwa [← chart_injective ch ht hyy]
  -- the vector-valued test functions `a_j η`
  set a : Fin 2 → Vec 2 → ℝ := fun j y => (jacMat F y).adjugate j i with ha
  have has : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (a j) := fun j => contDiff_adjugate_entry hFs j i
  set τ : Fin 2 → Vec 2 → ℝ := fun j y => a j y * η y with hτ
  have hτs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (τ j) := fun j => (has j).mul hηs
  have hτc : ∀ j, HasCompactSupport (τ j) := fun j => hηc.mul_left
  have hτB : ∀ j, tsupport (τ j) ⊆ B := fun j => (tsupport_mul_subset_right).trans hηB
  have hτd : ∀ j y, fderiv ℝ (τ j) y (basisVec j) =
      a j y * fderiv ℝ η y (basisVec j) + η y * fderiv ℝ (a j) y (basisVec j) := by
    intro j y
    have h1 : DifferentiableAt ℝ (a j) y := (has j).differentiable (by simp) y
    have h2 : DifferentiableAt ℝ η y := hηs.differentiable (by simp) y
    have h3 : fderiv ℝ (τ j) y = a j y • fderiv ℝ η y + η y • fderiv ℝ (a j) y := fderiv_mul h1 h2
    rw [h3]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hpiola : ∀ y, ∑ j : Fin 2, fderiv ℝ (a j) y (basisVec j) = 0 :=
    fun y => piola_column hFs y i
  have hLpt : ∀ y, θt (F y) * fderiv ℝ ψ (F y) (basisVec i) =
      ∑ j : Fin 2, θt (F y) * fderiv ℝ (τ j) y (basisVec j) := by
    intro y
    have h1 : fderiv ℝ ψ (F y) (basisVec i) =
        ∑ j : Fin 2, a j y * fderiv ℝ η y (basisVec j) := spGrad_chart ch ht hψ y i
    have h2 := hpiola y
    rw [Fin.sum_univ_two] at h1 h2 ⊢
    rw [h1, hτd, hτd]
    linear_combination (-(θt (F y) * η y)) * h2
  have hRpt : ∀ y, physGrad X t₁ DU (t, F y) i * ψ (F y) = ∑ j : Fin 2, DU t y j * τ j y := by
    intro y
    rw [physGrad_chart ch ht]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, hτ, ha,
      hη, Function.comp]
    simp only [pipeAdj, pipeJac]
    ring
  have hint1 : ∀ j, IntegrableOn (fun y => θt (F y) * fderiv ℝ (τ j) y (basisVec j)) B :=
    fun j => integrableOn_mul_cts' hU (contDiff_fderiv_apply_of_smooth (hτs j) _).continuous
      (hasCompactSupport_fderiv_apply (hτc j) _)
  have hint2 : ∀ j, IntegrableOn (fun y => DU t y j * τ j y) B := fun j =>
    integrableOn_mul_cts' (hD j) (hτs j).continuous (hτc j)
  have e1 := chart_image_integral ch ht (fun x => θt x * fderiv ℝ ψ x (basisVec i)) B
  have e2 := chart_image_integral ch ht (fun x => physGrad X t₁ DU (t, x) i * ψ x) B
  rw [e1, e2]
  calc ∫ y in B, θt (F y) * fderiv ℝ ψ (F y) (basisVec i)
      = ∫ y in B, ∑ j : Fin 2, θt (F y) * fderiv ℝ (τ j) y (basisVec j) :=
        integral_congr_ae (Filter.Eventually.of_forall hLpt)
    _ = ∑ j : Fin 2, ∫ y in B, θt (F y) * fderiv ℝ (τ j) y (basisVec j) :=
        integral_finsetSum _ fun j _ => hint1 j
    _ = ∑ j : Fin 2, -∫ y in B, DU t y j * τ j y :=
        Finset.sum_congr rfl fun j _ => hw j (τ j) (hτs j) (hτc j) (hτB j)
    _ = -∫ y in B, ∑ j : Fin 2, DU t y j * τ j y := by
        rw [Finset.sum_neg_distrib, integral_finsetSum _ fun j _ => hint2 j]
    _ = -∫ y in B, physGrad X t₁ DU (t, F y) i * ψ (F y) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hRpt y).symm)

/-- Compact subsets of the comparison pipe pull back to compact subsets of the label cylinder. -/
theorem preimage_compact_subset_cylinder {s₀ ρ : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀)
    {K : Set (ℝ × Vec 2)} (hKO : K ⊆ innerPipeO X t₁ s₀ ρ) :
    pipeMap X t₁ T ⁻¹' K ⊆ Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 ρ := by
  rintro ⟨t, y⟩ hp
  have hp' : pipeMap X t₁ T (t, y) ∈ innerPipeO X t₁ s₀ ρ := hKO hp
  have h0 := (mem_innerPipeO_iff ch hs₀ _).1 hp'
  have h1' : s₀ < t ∧ t < t₁ := ⟨h0.1, h0.2.1⟩
  have h2 : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨by linarith [h1'.1], h1'.2.le⟩
  have h3 : X t₁ (X t y t₁) t ∈ euclidBall 0 ρ := by
    have := h0.2.2
    rwa [pipeMap_apply_of_mem h2] at this
  rw [ch.left t h2 y] at h3
  exact ⟨⟨by linarith [h1'.1], h1'.2⟩, h3⟩

/-- `L²` bound of the physical gradient on compact subsets of the comparison pipe. -/
theorem memLp_physGrad_of_compact (hT : 0 < T) {s₀ ρ R : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀)
    (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) {DU : ℝ → Vec 2 → Vec 2}
    (hDU : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    {K : Set (ℝ × Vec 2)} (hKO : K ⊆ innerPipeO X t₁ s₀ ρ) (hK : IsCompact K) (i : Fin 2) :
    MemLp (fun p => physGrad X t₁ DU p i) 2 (volume.restrict K) := by
  set Ψ := pipeMap X t₁ T with hΨ
  set K' := Ψ ⁻¹' K with hK'
  have hK'c : IsCompact K' := (pipeHomeo ch hT).isCompact_preimage.2 hK
  have hsub : K' ⊆ Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R := by
    refine (preimage_compact_subset_cylinder ch hs₀ hKO).trans ?_
    exact Set.prod_mono subset_rfl (fun y hy => by
      simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
      exact lt_of_lt_of_le hy (pow_le_pow_left₀ hρ0 hρR 2))
  have hmp := (pipeMap_mp ch hT).restrict_preimage_emb (pipeMap_measurableEmbedding ch hT) K
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  -- the pulled-back gradient is `Σⱼ adj_{ji} DUⱼ`
  have hterm : ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 => pipeAdj X t₁ p j i * DU p.1 p.2 j) 2
      (volume.restrict K') := by
    intro j
    have hg := (hDU j).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hcont : Continuous fun p : ℝ × Vec 2 => pipeAdj X t₁ p j i :=
      (contDiff_pipeAdj_entry ch j i).continuous
    obtain ⟨C, hC⟩ := hK'c.exists_bound_of_continuousOn hcont.continuousOn
    refine hg.of_le_mul (c := C) ((hcont.aestronglyMeasurable).mul hg.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' hK'm).2 (Filter.Eventually.of_forall fun p hp => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC p hp) (norm_nonneg _)
  have hcomp : MemLp ((fun p => physGrad X t₁ DU p i) ∘ Ψ) 2 (volume.restrict K') := by
    have hsum := (hterm 0).add (hterm 1)
    refine hsum.ae_eq ?_
    refine (ae_restrict_iff' hK'm).2 (Filter.Eventually.of_forall fun p hp => ?_)
    obtain ⟨t, y⟩ := p
    have hw := hsub hp
    have ht : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨hw.1.1.le, hw.1.2.le⟩
    simp only [Function.comp, hΨ, pipeMap_apply_of_mem ht, physGrad_chart ch ht]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hmap : MemLp (fun p => physGrad X t₁ DU p i) 2 (Measure.map Ψ (volume.restrict K')) :=
    ((pipeMap_measurableEmbedding ch hT).memLp_map_measure_iff).2 hcomp
  rwa [hmp.map_eq] at hmap

end Chart
end

/-! # Slice `L²` bounds on the sections of the comparison pipe

`L²` slices of space-time functions on cylinders, the section `F_t(B_ρ)` is bounded, has finite
measure, and `L²` on `F_t(B_ρ)` is `L²` of the pull-back on `B_ρ`. -/

section
theorem ae_slice_memLp_two {a b : ℝ} {B : Set (Vec 2)} {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioo a b ×ˢ B))) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      MemLp (fun y => f (τ, y)) 2 (volume.restrict B) := by
  have hint : Integrable (fun p => f p ^ 2) (volume.restrict (Set.Ioo a b ×ˢ B)) :=
    hf.integrable_sq
  rw [volume_restrict_prod_eq] at hint
  have h1 := hint.prod_right_ae
  have h2 : AEStronglyMeasurable f ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := by
    have := hf.aestronglyMeasurable
    rwa [volume_restrict_prod_eq] at this
  filter_upwards [h1, h2.prodMk_left] with τ i1 m1
  exact (memLp_two_iff_integrable_sq m1).2 i1

theorem euclidBall_subset_closedBall_abs (ρ : ℝ) :
    euclidBall (0 : Vec 2) ρ ⊆ Metric.closedBall (0 : Vec 2) |ρ| := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := norm_le_sqrt_vecNormSq y
  have h2 : vecNormSq y < ρ ^ 2 := by simpa [euclidBall] using hy
  have h3 : Real.sqrt (vecNormSq y) ≤ |ρ| :=
    Real.sqrt_le_iff.2 ⟨abs_nonneg _, by rw [sq_abs]; exact h2.le⟩
  exact h1.trans h3

section Chart

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

theorem volume_chart_image {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (B : Set (Vec 2)) :
    volume ((fun y => X t y t₁) '' B) = volume B := by
  have h := (ch.mp t ht).measure_preimage_emb (chartHomeo ch ht).measurableEmbedding
    ((fun y => X t y t₁) '' B)
  rw [(chart_injective ch ht).preimage_image] at h
  exact h.symm

theorem memLp_chart_image {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (g : Vec 2 → ℝ)
    (B : Set (Vec 2)) :
    MemLp g 2 (volume.restrict ((fun y => X t y t₁) '' B)) ↔
      MemLp (fun y => g (X t y t₁)) 2 (volume.restrict B) := by
  have hmp := (ch.mp t ht).restrict_preimage_emb (chartHomeo ch ht).measurableEmbedding
    ((fun y => X t y t₁) '' B)
  rw [(chart_injective ch ht).preimage_image] at hmp
  have := (chartHomeo ch ht).measurableEmbedding.memLp_map_measure_iff (p := 2) (g := g)
    (μ := volume.restrict B)
  have hmap : Measure.map (⇑(chartHomeo ch ht)) (volume.restrict B) =
      volume.restrict ((fun y => X t y t₁) '' B) := hmp.map_eq
  rw [hmap] at this
  exact this

theorem chart_image_bounded {t : ℝ} (ρ : ℝ) :
    ∃ r : ℝ, ∀ x ∈ (fun y => X t y t₁) '' euclidBall (0 : Vec 2) ρ, ‖x‖ ≤ r := by
  have hc : IsCompact ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) |ρ|) :=
    (isCompact_closedBall _ _).image (contDiff_Ft ch t).continuous
  obtain ⟨r, hr⟩ := hc.isBounded.exists_norm_le
  exact ⟨r, fun x hx => hr x (Set.image_mono (euclidBall_subset_closedBall_abs ρ) hx)⟩

/-- `L²` of the physical gradient on the section `F_t(B_ρ)`. -/
theorem memLp_physGrad_section {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (ρ : ℝ)
    {DU : ℝ → Vec 2 → Vec 2}
    (hDU : ∀ j : Fin 2, MemLp (fun y => DU t y j) 2 (volume.restrict (euclidBall 0 ρ)))
    (i : Fin 2) :
    MemLp (fun x => physGrad X t₁ DU (t, x) i) 2
      (volume.restrict ((fun y => X t y t₁) '' euclidBall 0 ρ)) := by
  rw [memLp_chart_image ch ht (fun x => physGrad X t₁ DU (t, x) i)]
  have hterm : ∀ j : Fin 2, MemLp (fun y => pipeAdj X t₁ (t, y) j i * DU t y j) 2
      (volume.restrict (euclidBall 0 ρ)) := by
    intro j
    have hcont : Continuous fun y : Vec 2 => pipeAdj X t₁ (t, y) j i :=
      (contDiff_pipeAdj_entry ch j i).continuous.comp (continuous_const.prodMk continuous_id)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec 2) |ρ|).exists_bound_of_continuousOn
      hcont.continuousOn
    refine (hDU j).of_le_mul (c := C) (hcont.aestronglyMeasurable.mul (hDU j).aestronglyMeasurable)
      ?_
    refine (ae_restrict_iff' (pipe_isOpen_euclidBall 0 ρ).measurableSet).2
      (Filter.Eventually.of_forall fun y hy => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC y (euclidBall_subset_closedBall_abs ρ hy))
      (norm_nonneg _)
  refine ((hterm 0).add (hterm 1)).ae_eq (Filter.Eventually.of_forall fun y => ?_)
  simp only [physGrad_chart ch ht]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Chart
end

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # A divergence-free drift against `H¹` functions on a time section

For a bounded measurable field `b` annihilating `∇ψ`, `ψ ∈ C^∞_c(ℝ²)`, and `u ∈ H¹(S)` with
`S` open of finite measure, `χ ∈ C^∞_c(S)`:
`∫_S u b·∇χ + ∫_S (b·Du) χ = 0` (apply the divergence-free property to `χ u ∈ H¹_0(S)`). -/

theorem memLp_mul_bdd {S : Set (Vec 2)} {u f : Vec 2 → ℝ} (hu : MemLp u 2 (volume.restrict S))
    (hf : Continuous f) (hc : HasCompactSupport f) : MemLp (fun x => f x * u x) 2
      (volume.restrict S) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  refine hu.of_le_mul (c := C) (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using hC x) (norm_nonneg _)

theorem vecNormSq_le_of_norm_le {v : Vec 2} {B : ℝ} (h : ‖v‖ ≤ B) :
    vecNormSq v ≤ (2 * |B|) ^ 2 := by
  have h1 := vecNormSq_le_two_mul_norm_sq v
  have h2 : ‖v‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h3 : (2 * |B|) ^ 2 = 4 * B ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [h3]
  linarith [sq_nonneg B]

/-- **Divergence-free drift against `H¹_0`.** -/
theorem slice_drift_ibp {S : Set (Vec 2)} (hS : IsOpen S) (hSfin : volume S ≠ ⊤)
    {b : Vec 2 → Vec 2} {B : ℝ} (hbm : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B)
    (hdb : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spGrad φ x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : MemLp u 2 (volume.restrict S))
    (hD : ∀ i : Fin 2, MemLp (fun x => Du x i) 2 (volume.restrict S))
    (hw : HasWeakGradientOn S u Du) {χ : Vec 2 → ℝ} (hχ : IsSpTest S χ) :
    ∫ x in S, (u x * vecDot (b x) (spGrad χ x) + vecDot (b x) (Du x) * χ x) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hSfin⟩
  obtain ⟨hχs, hχc, hχS⟩ := hχ
  have hgc : ∀ i : Fin 2, Continuous fun x => spGrad χ x i := fun i =>
    (contDiff_fderiv_apply_of_smooth hχs (basisVec i)).continuous
  have hgk : ∀ i : Fin 2, HasCompactSupport fun x => spGrad χ x i := fun i =>
    hasCompactSupport_fderiv_apply hχc _
  -- the product `χ u` and its gradient
  have hw' := hasWeakGradientOn_smul_smooth hS hw hu hD (χ := χ) ⟨hχs, hχc, hχS⟩
  have hψ : MemLp (fun y => χ y * u y) 2 (volume.restrict S) :=
    memLp_mul_bdd hu hχs.continuous hχc
  have hDψ : ∀ i : Fin 2, MemLp (fun y => (χ y • Du y + u y • spGrad χ y) i) 2
      (volume.restrict S) := by
    intro i
    have h1 := memLp_mul_bdd (hD i) hχs.continuous hχc
    have h2 := memLp_mul_bdd hu (hgc i) (hgk i)
    refine (h1.add h2).ae_eq (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hKc : IsCompact (tsupport χ) := hχc
  have hz : ∀ y, y ∉ tsupport χ → χ y * u y = 0 := fun y hy => by
    simp [image_eq_zero_of_notMem_tsupport hy]
  have hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => b y i) (volume.restrict S) :=
    fun i => ((measurable_pi_apply i).comp hbm).aestronglyMeasurable
  have hbd : ∀ᵐ y ∂(volume.restrict S), vecNormSq (b y) ≤ (2 * |B|) ^ 2 :=
    Filter.Eventually.of_forall fun y => vecNormSq_le_of_norm_le (hbB y)
  have hdiv : ∀ ψ0, IsSpTest S ψ0 → ∫ y in S, vecDot (b y) (spGrad ψ0 y) = 0 := by
    intro ψ0 hψ0
    have hz0 : ∀ y, y ∉ tsupport ψ0 → vecDot (b y) (spGrad ψ0 y) = 0 := by
      intro y hy
      simp [vecDot, spGrad, fderiv_apply_eq_zero_of_notMem hy]
    rw [setIntegral_eq_integral_of_tsupport (g := ψ0) hψ0.2.2 hz0]
    exact hdb ψ0 hψ0.1 hψ0.2.1
  have key := LocalEnergy.Moll.divFree_slice_grad hS hSfin hdm hbd hdiv hψ hDψ hw' hKc hχS hz
  -- expand `b·(χ Du + u ∇χ)`
  have hexp : ∀ y, vecDot (b y) (χ y • Du y + u y • spGrad χ y) =
      vecDot (b y) (Du y) * χ y + u y * vecDot (b y) (spGrad χ y) := by
    intro y
    simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  simp_rw [hexp] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-! # From the distributional equation to the weak form with gradients

`theta_isLocalWeakSolution`: a function `θ` on an open set `O ⊆ ℝ × ℝ²` which is `L²` on compacts
of `O` with a slice gradient `Dθ` (also `L²` on compacts, and `L²` on the time sections), and which
satisfies the distributional equation `∫ θ (∂ₜφ + b·∇φ + κΔφ) = 0` for a bounded measurable
divergence-free drift `b`, is a local weak solution:
`∫_O -(θ ∂ₜφ) + (b·Dθ) φ + κ Dθ·∇φ = 0`. -/

theorem isOpen_timeSection {O : Set (ℝ × Vec 2)} (hO : IsOpen O) (t : ℝ) :
    IsOpen (timeSection O t) :=
  hO.preimage (continuous_const.prodMk continuous_id)

/-- Integrability of `b_i * g` on a measure space for bounded measurable `b_i`. -/
theorem integrableOn_coord_mul {O : Set (ℝ × Vec 2)} {b : ℝ → Vec 2 → Vec 2} {B : ℝ}
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) (hbB : ∀ t x, ‖b t x‖ ≤ B)
    {g : ℝ × Vec 2 → ℝ} (hg : IntegrableOn g O) (i : Fin 2) :
    IntegrableOn (fun p => b p.1 p.2 i * g p) O :=
  hg.bdd_mul (c := B) ((measurable_pi_apply i).comp hbm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => (norm_le_pi_norm (b p.1 p.2) i).trans (hbB _ _))

theorem theta_isLocalWeakSolution {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {O : Set (ℝ × Vec 2)}
    (hO : IsOpen O) (hfin : ∀ t, volume (timeSection O t) ≠ ⊤)
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) (hbB : ∀ t x, ‖b t x‖ ≤ B)
    (hdb : ∀ t, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b t x) (spGrad φ x) = 0)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ × Vec 2 → Vec 2}
    (hL2 : ∀ K ⊆ O, IsCompact K → MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict K))
    (hDL2 : ∀ K ⊆ O, IsCompact K → ∀ i : Fin 2,
      MemLp (fun p => Dθ p i) 2 (volume.restrict K))
    (hsec : ∀ᵐ t ∂(volume : Measure ℝ), MemLp (fun x => θ t x) 2
        (volume.restrict (timeSection O t)) ∧
      ∀ i : Fin 2, MemLp (fun x => Dθ (t, x) i) 2 (volume.restrict (timeSection O t)))
    (hgrad : ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakGradientOn (timeSection O t) (fun x => θ t x) (fun x => Dθ (t, x)))
    (heq : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest O φ →
      ∫ p in O, θ p.1 p.2 * (stTimeDeriv φ p + vecDot (b p.1 p.2) (stSpaceGrad φ p)
        + κ * stSpaceLap φ p) = 0) :
    IsLocalWeakSolution b κ O (fun p => θ p.1 p.2) Dθ := by
  refine ⟨hL2, hDL2, hgrad, ?_⟩
  intro φ hφ
  have hu : ∀ K ⊆ O, IsCompact K → IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) K :=
    fun K hK hc => integrableOn_of_memLp_compact hc (hL2 K hK hc)
  have hD : ∀ i : Fin 2, ∀ K ⊆ O, IsCompact K → IntegrableOn (fun p => Dθ p i) K :=
    fun i K hK hc => integrableOn_of_memLp_compact hc (hDL2 K hK hc i)
  have hg1 : ∀ i : Fin 2, Continuous fun p => stSpaceGrad φ p i := fun i =>
    (contDiff_fderiv_apply_of_smooth hφ.1 (0, basisVec i)).continuous
  have hg2 : ∀ i : Fin 2, HasCompactSupport fun p => stSpaceGrad φ p i := fun i =>
    hasCompactSupport_fderiv_apply hφ.2.1 _
  have hg3 : ∀ i : Fin 2, tsupport (fun p => stSpaceGrad φ p i) ⊆ O := fun i =>
    (tsupport_fderiv_apply_subset φ _).trans hφ.2.2
  have hψ : ∀ i : Fin 2, IsSTTest O fun q => fderiv ℝ φ q (0, basisVec i) := fun i =>
    ⟨contDiff_fderiv_apply_of_smooth hφ.1 _, hasCompactSupport_fderiv_apply hφ.2.1 _,
      (tsupport_fderiv_apply_subset _ _).trans hφ.2.2⟩
  -- the five integrable pieces
  have P1 : IntegrableOn (fun p => θ p.1 p.2 * stTimeDeriv φ p) O :=
    integrableOn_mul_of_support hu (contDiff_fderiv_apply_of_smooth hφ.1 _).continuous
      (hasCompactSupport_fderiv_apply hφ.2.1 _) ((tsupport_fderiv_apply_subset φ _).trans hφ.2.2)
  have Pg : ∀ i : Fin 2, IntegrableOn (fun p => θ p.1 p.2 * stSpaceGrad φ p i) O := fun i =>
    integrableOn_mul_of_support hu (hg1 i) (hg2 i) (hg3 i)
  have P2 : IntegrableOn (fun p => θ p.1 p.2 * vecDot (b p.1 p.2) (stSpaceGrad φ p)) O := by
    have : (fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (b p.1 p.2) (stSpaceGrad φ p)) = fun p =>
        ∑ i : Fin 2, b p.1 p.2 i * (θ p.1 p.2 * stSpaceGrad φ p i) := by
      funext p; simp only [vecDot, Fin.sum_univ_two]; ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => integrableOn_coord_mul hbm hbB (Pg i) i
  have hbD : ∀ K ⊆ O, IsCompact K →
      IntegrableOn (fun p => vecDot (b p.1 p.2) (Dθ p)) K := by
    intro K hK hc
    simp only [vecDot]
    exact integrable_finsetSum _ fun i _ => integrableOn_coord_mul hbm hbB (hD i K hK hc) i
  have P3 : IntegrableOn (fun p => vecDot (b p.1 p.2) (Dθ p) * φ p) O :=
    integrableOn_mul_of_support hbD hφ.1.continuous hφ.2.1 hφ.2.2
  have PD : ∀ i : Fin 2, IntegrableOn (fun p => Dθ p i * stSpaceGrad φ p i) O := fun i =>
    integrableOn_mul_of_support (hD i) (hg1 i) (hg2 i) (hg3 i)
  have P5 : IntegrableOn (fun p => vecDot (Dθ p) (stSpaceGrad φ p)) O := by
    simp only [vecDot]
    exact integrable_finsetSum _ fun i _ => PD i
  have PA : ∀ i : Fin 2, IntegrableOn (fun p => θ p.1 p.2 *
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i)) O := fun i =>
    integrableOn_mul_of_support hu
      (contDiff_fderiv_apply_of_smooth (hψ i).1 _).continuous
      (hasCompactSupport_fderiv_apply (hψ i).2.1 _)
      ((tsupport_fderiv_apply_subset _ _).trans (hψ i).2.2)
  have P4 : IntegrableOn (fun p => θ p.1 p.2 * stSpaceLap φ p) O := by
    have : (fun p : ℝ × Vec 2 => θ p.1 p.2 * stSpaceLap φ p) = fun p =>
        ∑ i : Fin 2, θ p.1 p.2 *
          fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) := by
      funext p; simp only [stSpaceLap, Finset.mul_sum]
    rw [this]
    exact integrable_finsetSum _ fun i _ => PA i
  -- (ii) the Laplacian term
  have hlap : ∫ p in O, θ p.1 p.2 * stSpaceLap φ p = -∫ p in O, vecDot (Dθ p) (stSpaceGrad φ p) := by
    have h1 : ∀ i : Fin 2, ∫ p in O, θ p.1 p.2 *
        fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) =
        -∫ p in O, Dθ p i * stSpaceGrad φ p i := fun i =>
      integral_mul_partial_section (H := fun p => θ p.1 p.2) (g := fun p => Dθ p i) i hu
        (hD i) (by filter_upwards [hgrad] with t ht using ht i) (hψ i)
    have e1 : (fun p : ℝ × Vec 2 => θ p.1 p.2 * stSpaceLap φ p) = fun p =>
        ∑ i : Fin 2, θ p.1 p.2 *
          fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) := by
      funext p; simp only [stSpaceLap, Finset.mul_sum]
    rw [e1, integral_finsetSum _ fun i _ => PA i]
    simp only [vecDot]
    rw [integral_finsetSum _ fun i _ => PD i, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => h1 i
  -- (i) the drift term
  have hdrift : ∫ p in O, (θ p.1 p.2 * vecDot (b p.1 p.2) (stSpaceGrad φ p)
      + vecDot (b p.1 p.2) (Dθ p) * φ p) = 0 := by
    set Q : ℝ × Vec 2 → ℝ := fun p => θ p.1 p.2 * vecDot (b p.1 p.2) (stSpaceGrad φ p)
      + vecDot (b p.1 p.2) (Dθ p) * φ p with hQ
    have hQz : ∀ p, p ∉ tsupport φ → Q p = 0 := by
      intro p hp
      obtain ⟨-, h2, -⟩ := st_derivs_zero hp
      have h3 : φ p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp [hQ, h2, h3, vecDot]
    rw [setIntegral_eq_integral_of_tsupport (g := φ) hφ.2.2 hQz]
    have hQi : Integrable Q volume :=
      ((P2.add P3).mono_set hφ.2.2).integrable_of_forall_notMem_eq_zero hQz
    rw [Measure.volume_eq_prod] at hQi ⊢
    rw [integral_prod _ hQi]
    have : ∀ᵐ t ∂(volume : Measure ℝ), ∫ x, Q (t, x) = 0 := by
      filter_upwards [hsec, hgrad] with t ⟨hs1, hs2⟩ hg
      have hS := isOpen_timeSection hO t
      have hχ := sliceTest_section hφ t
      have key := slice_drift_ibp hS (hfin t) (b := b t) (B := B) (hbm.comp
        (measurable_const.prodMk measurable_id)) (fun x => hbB t x) (hdb t) hs1 hs2 hg hχ
      have hz : ∀ x, x ∉ tsupport (fun y => φ (t, y)) → Q (t, x) = 0 := by
        intro x hx
        have h1 : stSpaceGrad φ (t, x) = 0 := by
          ext i
          simp only [stSpaceGrad, Pi.zero_apply]
          rw [← fderiv_slice hφ.1 t x]
          exact fderiv_apply_eq_zero_of_notMem hx _
        have h2 : φ (t, x) = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => φ (t, y)) hx
        simp [hQ, h1, h2, vecDot]
      rw [← setIntegral_eq_integral_of_tsupport (g := fun y => φ (t, y)) hχ.2.2 hz]
      rw [← key]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hQ]
      have : spGrad (fun y => φ (t, y)) x = stSpaceGrad φ (t, x) := by
        ext i
        simp only [spGrad, stSpaceGrad]
        rw [fderiv_slice hφ.1 t x]
      rw [this]
    rw [integral_congr_ae this]
    simp
  -- assemble
  have hE := heq φ hφ
  have hfun : ∀ p : ℝ × Vec 2, θ p.1 p.2 * (stTimeDeriv φ p + vecDot (b p.1 p.2) (stSpaceGrad φ p)
      + κ * stSpaceLap φ p) = θ p.1 p.2 * stTimeDeriv φ p + (θ p.1 p.2 *
        vecDot (b p.1 p.2) (stSpaceGrad φ p)) + κ * (θ p.1 p.2 * stSpaceLap φ p) := by
    intro p; ring
  simp_rw [hfun] at hE
  have I12 : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2 * stTimeDeriv φ p +
      θ p.1 p.2 * vecDot (b p.1 p.2) (stSpaceGrad φ p)) O := P1.add P2
  rw [integral_add I12 (P4.const_mul κ), integral_add P1 P2, integral_const_mul] at hE
  rw [integral_add P2 P3] at hdrift
  have hgoal : ∫ p in O, (-(θ p.1 p.2 * stTimeDeriv φ p) + vecDot (b p.1 p.2) (Dθ p) * φ p
      + κ * vecDot (Dθ p) (stSpaceGrad φ p)) =
      -(∫ p in O, θ p.1 p.2 * stTimeDeriv φ p) + (∫ p in O, vecDot (b p.1 p.2) (Dθ p) * φ p)
        + κ * ∫ p in O, vecDot (Dθ p) (stSpaceGrad φ p) := by
    have N1 : IntegrableOn (fun p : ℝ × Vec 2 => -(θ p.1 p.2 * stTimeDeriv φ p)) O := P1.neg
    have I13 : IntegrableOn (fun p : ℝ × Vec 2 => -(θ p.1 p.2 * stTimeDeriv φ p) +
        vecDot (b p.1 p.2) (Dθ p) * φ p) O := N1.add P3
    rw [integral_add I13 (P5.const_mul κ), integral_add N1 P3, integral_neg,
      integral_const_mul]
  rw [hgoal]
  rw [hlap] at hE
  linarith

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix
namespace AVRegularity.Applications

/-! # A local energy solution is a local weak solution in the comparison pipe

`theta_localWeak_chart`: for a chart `F_t` on the window `[t₁ - 8T, t₁]` and a local energy solution
`θ` (`IsLocalEnergySolution`) of `∂ₜθ + b·∇θ - κΔθ = 0` in the outer pipe (with `b` bounded
measurable and divergence free), `θ` is a local weak solution in `𝒪 = innerPipeO X t₁ s₀ (R/8)`,
with the physical gradient `Dθ = physGrad X t₁ DU`. -/

theorem innerPipeO_subset_outerPipe {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s₀ ρ : ℝ}
    (hs₀ : t₁ - 8 * T ≤ s₀) (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) :
    innerPipeO X t₁ s₀ ρ ⊆ outerPipe (fun t y => X t y t₁) t₁ T R := by
  rintro p ⟨h1, h2, y, hy, hp⟩
  refine ⟨by linarith, h2, y, ?_, hp⟩
  simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
  exact lt_of_lt_of_le hy (pow_le_pow_left₀ hρ0 hρR 2)

theorem euclidBall_mono' {ρ R : ℝ} (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) :
    euclidBall (0 : Vec 2) ρ ⊆ euclidBall 0 R := by
  intro y hy
  simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
  exact lt_of_lt_of_le hy (pow_le_pow_left₀ hρ0 hρR 2)


section Chart

variable {b0 b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R κ B : ℝ}

theorem theta_localWeak_chart (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) {s₀ : ℝ}
    (hs₀ : t₁ - 8 * T ≤ s₀) (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2)
    (hbB : ∀ t x, ‖b t x‖ ≤ B)
    (hdb : ∀ t, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b t x) (spGrad φ x) = 0)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ) :
    ∃ Dθ : ℝ × Vec 2 → Vec 2,
      IsLocalWeakSolution b κ (innerPipeO X t₁ s₀ (R / 8)) (fun p => θ p.1 p.2) Dθ ∧
      ∀ᵐ t ∂(volume : Measure ℝ),
        IntegrableOn (fun x => θ t x) (timeSection (innerPipeO X t₁ s₀ (R / 8)) t) ∧
        ∀ i : Fin 2, IntegrableOn (fun x => Dθ (t, x) i)
          (timeSection (innerPipeO X t₁ s₀ (R / 8)) t) := by
  obtain ⟨hL2, heq, DU, ⟨C, hCae⟩, hDU2, hgrad⟩ := hθ
  set ρ := R / 8 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρR : ρ ≤ R := by linarith
  set O := innerPipeO X t₁ s₀ ρ with hOdef
  have hO : IsOpen O := isOpen_innerPipeO ch hs₀
  have hOouter := innerPipeO_subset_outerPipe (X := X) (T := T) hs₀ hρ0 hρR
  have hballρ : euclidBall (0 : Vec 2) ρ ⊆ euclidBall 0 R := euclidBall_mono' hρ0 hρR
  have hmeas : MeasurableSet (Set.Ioo (t₁ - 8 * T) t₁) := measurableSet_Ioo
  -- a.e. slice package on the label ball `B_R`
  have hDUs : ∀ j : Fin 2, ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      MemLp (fun y => DU t y j) 2 (volume.restrict (euclidBall 0 R)) := fun j =>
    ae_slice_memLp_two (f := fun p : ℝ × Vec 2 => DU p.1 p.2 j) (hDU2 j)
  have hslice : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (t₁ - 8 * T) t₁ →
      MemL2On (euclidBall 0 R) (fun y => θ t (X t y t₁)) ∧
      (∀ j : Fin 2, MemLp (fun y => DU t y j) 2 (volume.restrict (euclidBall 0 R))) ∧
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (X t y t₁)) (DU t) := by
    refine (ae_restrict_iff' hmeas).1 ?_
    filter_upwards [hCae, hDUs 0, hDUs 1, hgrad] with t h1 h2 h3 h4
    exact ⟨h1.1, fun j => by fin_cases j <;> assumption, h4⟩
  have hfin : ∀ t, volume (timeSection O t) ≠ ⊤ := by
    intro t
    by_cases htm : t ∈ Set.Ioo s₀ t₁
    · have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨by linarith [htm.1], htm.2.le⟩
      rw [timeSection_innerPipeO_of_mem htm, volume_chart_image ch htI]
      exact (pipe_volume_euclidBall_lt_top ρ).ne
    · rw [timeSection_innerPipeO_of_notMem htm]
      simp
  have hsec : ∀ᵐ t ∂(volume : Measure ℝ), MemLp (fun x => θ t x) 2
        (volume.restrict (timeSection O t)) ∧
      ∀ i : Fin 2, MemLp (fun x => physGrad X t₁ DU (t, x) i) 2
        (volume.restrict (timeSection O t)) := by
    filter_upwards [hslice] with t ht
    by_cases htm : t ∈ Set.Ioo s₀ t₁
    · have htw : t ∈ Set.Ioo (t₁ - 8 * T) t₁ := ⟨by linarith [htm.1], htm.2⟩
      have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨htw.1.le, htw.2.le⟩
      obtain ⟨h1, h2, -⟩ := ht htw
      rw [timeSection_innerPipeO_of_mem htm]
      refine ⟨(memLp_chart_image ch htI (θ t) _).2 (h1.mono_measure
        (Measure.restrict_mono hballρ le_rfl)), fun i => ?_⟩
      exact memLp_physGrad_section ch htI ρ
        (fun j => (h2 j).mono_measure (Measure.restrict_mono hballρ le_rfl)) i
    · rw [timeSection_innerPipeO_of_notMem htm]
      simp
  have hgradP : ∀ᵐ t ∂(volume : Measure ℝ), HasWeakGradientOn (timeSection O t)
      (fun x => θ t x) (fun x => physGrad X t₁ DU (t, x)) := by
    filter_upwards [hslice] with t ht
    by_cases htm : t ∈ Set.Ioo s₀ t₁
    · have htw : t ∈ Set.Ioo (t₁ - 8 * T) t₁ := ⟨by linarith [htm.1], htm.2⟩
      have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨htw.1.le, htw.2.le⟩
      obtain ⟨h1, h2, h3⟩ := ht htw
      rw [timeSection_innerPipeO_of_mem htm]
      have hfinB : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) ρ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact pipe_volume_euclidBall_lt_top ρ⟩
      refine hasWeakGradientOn_chart_image ch htI ?_ ?_ (hasWeakGradientOn_mono hballρ h3)
      · exact (h1.mono_measure (Measure.restrict_mono hballρ le_rfl)).integrable (by norm_num)
      · exact fun j => ((h2 j).mono_measure
          (Measure.restrict_mono hballρ le_rfl)).integrable (by norm_num)
    · rw [timeSection_innerPipeO_of_notMem htm]
      intro i φ _ _ _
      simp
  have hL2' : ∀ K ⊆ O, IsCompact K → MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict K) := fun K hK _ =>
    hL2.mono_measure (Measure.restrict_mono (hK.trans hOouter) le_rfl)
  have hDL2' : ∀ K ⊆ O, IsCompact K → ∀ i : Fin 2,
      MemLp (fun p => physGrad X t₁ DU p i) 2 (volume.restrict K) :=
    fun K hK hc i => memLp_physGrad_of_compact ch hT hs₀ hρ0 hρR hDU2 hK hc i
  have heq' : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest O φ →
      ∫ p in O, θ p.1 p.2 * (stTimeDeriv φ p + vecDot (b p.1 p.2) (stSpaceGrad φ p)
        + κ * stSpaceLap φ p) = 0 := by
    intro φ hφ
    have h : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 *
        (stTimeDeriv φ p + vecDot (b p.1 p.2) (stSpaceGrad φ p) + κ * stSpaceLap φ p) = 0 :=
      heq φ hφ.1 hφ.2.1 (hφ.2.2.trans hOouter)
    have hz : ∀ p, p ∉ tsupport φ → θ p.1 p.2 * (stTimeDeriv φ p +
        vecDot (b p.1 p.2) (stSpaceGrad φ p) + κ * stSpaceLap φ p) = 0 := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := st_derivs_zero hp
      simp [h1, h2, h3, vecDot]
    rw [setIntegral_eq_integral_of_tsupport (g := φ) (hφ.2.2.trans hOouter) hz] at h
    rw [setIntegral_eq_integral_of_tsupport (g := φ) hφ.2.2 hz]
    exact h
  refine ⟨physGrad X t₁ DU, theta_isLocalWeakSolution hO hfin hbm hbB hdb hL2' hDL2' hsec hgradP
    heq', ?_⟩
  filter_upwards [hsec] with t ht
  have : IsFiniteMeasure (volume.restrict (timeSection O t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (hfin t)⟩
  exact ⟨ht.1.integrable (by norm_num), fun i => (ht.2 i).integrable (by norm_num)⟩


/-- Slice integrability of a periodic `H¹` family on the sections of the comparison pipe. -/
theorem section_integrable_of_periodicH1 (ch : IsPipeChart b0 X t₁ T) {s₀ ρ : ℝ}
    (hs₀ : t₁ - 8 * T ≤ s₀) {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hper : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo s₀ t₁ → IsPeriodicH1With (u t) (Du t)) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      IntegrableOn (fun x => u t x) (timeSection (innerPipeO X t₁ s₀ ρ) t) ∧
      ∀ i : Fin 2, IntegrableOn (fun x => Du t x i) (timeSection (innerPipeO X t₁ s₀ ρ) t) := by
  filter_upwards [hper] with t ht
  by_cases htm : t ∈ Set.Ioo s₀ t₁
  · have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨by linarith [htm.1], htm.2.le⟩
    obtain ⟨hup, hDp, hu2, hD2, -⟩ := ht htm
    rw [timeSection_innerPipeO_of_mem htm]
    obtain ⟨r, hr⟩ := chart_image_bounded ch (t := t) ρ
    have hsub : (fun y => X t y t₁) '' euclidBall (0 : Vec 2) ρ ⊆ supBall r := fun x hx => hr x hx
    have hfinS : IsFiniteMeasure (volume.restrict ((fun y => X t y t₁) '' euclidBall (0 : Vec 2) ρ)) :=
      ⟨by
        rw [Measure.restrict_apply_univ, volume_chart_image ch htI]
        exact pipe_volume_euclidBall_lt_top ρ⟩
    refine ⟨((memLp_two_supBall_space hup hu2 r).mono_measure
      (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num), fun i => ?_⟩
    have hpi : IsZ2Periodic (fun x => Du t x i) := fun k x => by simp [hDp k x]
    exact ((memLp_two_supBall_space hpi (hD2 i) r).mono_measure
      (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num)
  · rw [timeSection_innerPipeO_of_notMem htm]
    simp

end Chart

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Filter Topology
namespace AVRegularity.Applications

/-! # The physical lift (`PhysLiftStmt`)

For a local energy solution `θ` in the outer pipe and a torus energy solution `u` from
`s₀ = t₁ - 9T/2`, the difference `θ - u` is a local weak solution in the comparison pipe
`{(ℓ, F_ℓ y) : s₀ < ℓ < t₁, |y| < R/8}`: `θ` is a local weak solution there
(`theta_localWeak_chart`, change of variables and the divergence-free structure of `b`), the
periodic lift of `u` is a local weak solution on `(s₀, s₀ + 5T) × ℝ²`, and local weak solutions
subtract. -/

section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

omit hα₀ hα₁ hs₀ hs₁ hq in
theorem limit_velocity_periodic' (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) (t : ℝ) :
    IsZ2Periodic (b t) := by
  intro k x
  have hper : ∀ M, streamVel (Φ M) t (x + latticeShift k) = streamVel (Φ M) t x := fun M => by
    have := (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)).periodic 0 k t x
    simpa using this
  refine tendsto_nhds_unique (hb t (x + latticeShift k)) ?_
  simp only [hper]
  exact hb t x

/-- **The physical lift** (`PhysLiftStmt`). -/
theorem physLift_holds (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    PhysLiftStmt α q Λ Φ b := by
  intro n _hn X hX t₁ T R κ hT hR _hR8 _hκ hh θ hθ f _hf u hu
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT hh
  obtain ⟨hbm, ⟨B, hBb⟩, hdb⟩ :=
    limit_velocity_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  have hs0 : t₁ - 8 * T ≤ t₁ - 9 * T / 2 := by linarith
  obtain ⟨Dθ, hθlw, hθsec⟩ := theta_localWeak_chart ch hT hR hs0 hbm hBb hdb hθ
  obtain ⟨Du, hDuW, hlu⟩ := isLocalWeakSolution_of_isWeakSolutionOn
    (fun t _ => limit_velocity_periodic' α q ζ hζ Λ hΛ Φ hΦ b hb t) hu
  have hsub : innerPipeO X t₁ (t₁ - 9 * T / 2) (R / 8) ⊆
      Set.Ioo (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T) ×ˢ (Set.univ : Set (Vec 2)) := by
    rintro p ⟨h1, h2, -⟩
    exact ⟨⟨h1, by linarith⟩, Set.mem_univ _⟩
  have hlu' := hlu.mono hsub
  have hper : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (t₁ - 9 * T / 2) t₁ →
      IsPeriodicH1With (u t) (Du t) := by
    have h := (ae_restrict_iff' (measurableSet_Ioo (a := t₁ - 9 * T / 2)
      (b := t₁ - 9 * T / 2 + 5 * T))).1 hDuW.2.2.2.2.1
    filter_upwards [h] with t ht htm
    exact ht ⟨htm.1, by linarith [htm.2]⟩
  have hus := section_integrable_of_periodicH1 ch (ρ := R / 8) hs0 hper
  exact ⟨fun p => Dθ p - Du p.1 p.2,
    IsLocalWeakSolution.sub hbm hBb hθlw hlu' hθsec hus⟩

end Construction

end AVRegularity.Applications
end
