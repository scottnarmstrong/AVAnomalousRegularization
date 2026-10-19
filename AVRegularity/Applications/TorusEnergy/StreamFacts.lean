-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.TorusEnergy.LocalInt
public import AVRegularity.Applications.TorusEnergy.With
public import AVenhance.Statements.Construction.StreamVel
public import AVRegularity.Applications.Parabolic.SliceGrad
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # Forced energy identity on the torus: setting

`IsTorusForced w Dw P g t₁ t₂` collects the hypotheses of the forced torus energy identity:
`w` is a weak solution on the window of `∂ₜw = div P + g` with `w, Dw, P, g ∈ L²`, periodic `H¹`
slices, and weakly continuous in time. The identity is derived from the local energy identity
`local_energy_identity` with a spatial cutoff `ζ` satisfying `Σ_n ζ(x + n)² = 1`. -/

/-- Hypotheses of the forced torus energy identity: `w` solves
`∂ₜw - div P - g = 0` weakly on `(t₁,t₂) × ℝ²` (periodic data). -/
structure IsTorusForced (w : ℝ → Vec 2 → ℝ) (Dw P : ℝ → Vec 2 → Vec 2) (g : ℝ → Vec 2 → ℝ)
    (t₁ t₂ : ℝ) : Prop where
  slice : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (w t) ∧ MemL2On unitCube (w t)
  memw : MemLp (fun p : ℝ × Vec 2 => w p.1 p.2) 2 (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))
  memDw : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dw p.1 p.2 i) 2
    (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))
  memP : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => P p.1 p.2 i) 2
    (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))
  memg : MemLp (fun p : ℝ × Vec 2 => g p.1 p.2) 2 (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))
  h1 : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsPeriodicH1With (w t) (Dw t)
  Pper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (P t)
  gper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (g t)
  weak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) φ →
    ∫ p in Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2)),
      (-(w p.1 p.2 * stTimeDeriv φ p) + vecDot (P p.1 p.2) (stSpaceGrad φ p) - g p.1 p.2 * φ p)
      = 0
  cont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, w t x * ψ x) (Set.Icc t₁ t₂)

theorem hasWeakGradientOn_univ_mono {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : HasWeakGradientOn (Set.univ : Set (Vec 2)) u Du) (V : Set (Vec 2)) :
    HasWeakGradientOn V u Du := by
  intro i φ hφs hφc hφV
  have h' := h i φ hφs hφc (Set.subset_univ _)
  have hz1 : ∀ x ∈ (Set.univ : Set (Vec 2)) \ V, u x * fderiv ℝ φ x (basisVec i) = 0 := by
    intro x hx
    have : x ∉ tsupport φ := fun hx' => hx.2 (hφV hx')
    simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
  have hz2 : ∀ x ∈ (Set.univ : Set (Vec 2)) \ V, Du x i * φ x = 0 := by
    intro x hx
    have : x ∉ tsupport φ := fun hx' => hx.2 (hφV hx')
    simp [image_eq_zero_of_notMem_tsupport this]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (Set.subset_univ V) hz1,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (Set.subset_univ V) hz2]
    at h'
  exact h'

theorem nhdsIoo_ae_neBot {a b : ℝ} (hab : a < b) {τ : ℝ} (hτ : τ ∈ Set.Icc a b) :
    (𝓝[Set.Ioo a b] τ ⊓ ae (volume : Measure ℝ)).NeBot := by
  rw [inf_neBot_iff]
  intro s hs s' hs'
  rw [mem_nhdsWithin] at hs
  obtain ⟨U, hUo, hτU, hUs⟩ := hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo τ hτU
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hJ : Set.Ioo (max (τ - ε) a) (min (τ + ε) b) ⊆ s'ᶜ := by
    intro y hy hy'
    have hy1 : y ∈ Set.Ioo a b := ⟨lt_of_le_of_lt (le_max_right _ _) hy.1,
      lt_of_lt_of_le hy.2 (min_le_right _ _)⟩
    have hy2 : y ∈ Metric.ball τ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := lt_of_le_of_lt (le_max_left _ _) hy.1; linarith
      · have := lt_of_lt_of_le hy.2 (min_le_left _ _); linarith
    have : y ∈ s ∩ s' := ⟨hUs ⟨hball hy2, hy1⟩, hy'⟩
    rw [hne] at this
    exact this
  have hnull : volume s'ᶜ = 0 := hs'
  have := measure_mono_null hJ hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  have hlt : max (τ - ε) a < min (τ + ε) b := by
    exact max_lt (lt_min (by linarith) (by linarith [hτ.2])) (lt_min (by linarith [hτ.1]) hab)
  linarith

/-- The open sup-ball of radius `4`, containing the support of the cutoff. -/
def cutBall : Set (Vec 2) := Metric.ball (0 : Vec 2) 4

theorem isOpen_cutBall : IsOpen cutBall := Metric.isOpen_ball

theorem cutBall_subset_supBall : cutBall ⊆ supBall 4 := fun x hx => by
  simpa [cutBall, supBall, dist_zero_right] using le_of_lt (by simpa [cutBall] using hx)

theorem isSpTest_cutoffZ : IsSpTest cutBall cutoffZ := by
  refine ⟨cutoffZ_contDiff, cutoffZ_hasCompactSupport, ?_⟩
  have hcl : IsClosed {x : Vec 2 | ‖x‖ ≤ 3} := isClosed_le continuous_norm continuous_const
  have hsub : tsupport cutoffZ ⊆ {x : Vec 2 | ‖x‖ ≤ 3} := by
    refine closure_minimal ?_ hcl
    intro x hx
    exact cutoffZ_supBdd 0 x hx
  intro x hx
  have := hsub hx
  simp only [Set.mem_ofPred_eq] at this
  simp only [cutBall, Metric.mem_ball, dist_zero_right]
  linarith

/-! # Identification of the cutoff `L²` trace with the pointwise-in-time slices

For `w` weakly continuous in time with periodic `L²(cube)` slices, an `L²(B)`-valued `W`
continuous on `[t₁,t₂]` with `W(τ) = ζ w(τ)` for a.e. `τ` satisfies, for **every** `τ`,
`W(τ) = ζ w(τ)` a.e. in `B`, `‖W(τ)‖² = ‖w(τ)‖²_{L²(𝕋²)}`, and
`∫_B W(τ) ρ = ∫_{𝕋²} w(τ) (ζρ)^per`. -/

section
theorem integrable_of_integrable_prod_snd {h : Vec 2 → ℝ} {A : Set (Vec 2)}
    (hint : Integrable (fun p : ℝ × Vec 2 => h p.2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ A))) : Integrable h (volume.restrict A) := by
  rw [volume_restrict_prod_eq] at hint
  have h1 := hint.prod_right_ae
  have hne : (ae (volume.restrict (Set.Ioo (0 : ℝ) 1))).NeBot := by
    rw [ae_neBot]
    intro h0
    have := congrArg (fun μ : Measure ℝ => μ Set.univ) h0
    simp at this
  obtain ⟨x, hx⟩ := h1.exists
  exact hx

theorem integrableOn_supBall_space {G : Vec 2 → ℝ} (hper : IsZ2Periodic G)
    (hG : Integrable G (volume.restrict unitCube)) (R : ℝ) :
    Integrable G (volume.restrict (supBall R)) := by
  have hG' : Integrable (fun p : ℝ × Vec 2 => (fun (_ : ℝ) x => G x) p.1 p.2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
    rw [volume_restrict_prod_eq]
    exact hG.comp_snd (volume.restrict (Set.Ioo (0 : ℝ) 1))
  exact integrable_of_integrable_prod_snd
    (integrableOn_supBall_of_cell measurableSet_Ioo (G := fun _ x => G x)
      (Eventually.of_forall fun t => hper) hG' R)

theorem memLp_two_supBall_space {G : Vec 2 → ℝ} (hper : IsZ2Periodic G)
    (hG : MemLp G 2 (volume.restrict unitCube)) (R : ℝ) :
    MemLp G 2 (volume.restrict (supBall R)) := by
  have hm : AEStronglyMeasurable G (volume.restrict (supBall R)) := by
    have hG' : AEStronglyMeasurable (fun p : ℝ × Vec 2 => (fun (_ : ℝ) x => G x) p.1 p.2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
      rw [volume_restrict_prod_eq]
      exact hG.aestronglyMeasurable.comp_snd
    have := aestronglyMeasurable_of_cell measurableSet_Ioo (G := fun _ x => G x)
      (Eventually.of_forall fun t => hper) hG'
    rw [volume_restrict_prod_eq] at this
    have hne : (ae (volume.restrict (Set.Ioo (0 : ℝ) 1))).NeBot := by
      rw [ae_neBot]
      intro h0
      have := congrArg (fun μ : Measure ℝ => μ Set.univ) h0
      simp at this
    obtain ⟨x, hx⟩ := this.prodMk_left.exists
    exact hx.mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)
  rw [memLp_two_iff_integrable_sq hm]
  exact integrableOn_supBall_space (G := fun x => G x ^ 2) (fun k x => by simp [hper k x])
    hG.integrable_sq R

instance isFiniteMeasure_unitCube : IsFiniteMeasure (volume.restrict unitCube : Measure (Vec 2)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact unitCube_measure_ne_top.lt_top⟩

/-- The cutoff pairing: `∫_B ρ (ζ G) = ∫_{𝕋²} G (ζρ)^per`. -/
theorem cutoff_pairing {G ρ : Vec 2 → ℝ} (hper : IsZ2Periodic G)
    (hG : Integrable G (volume.restrict unitCube)) (hρ : IsSpTest cutBall ρ) :
    ∫ x in cutBall, ρ x * (cutoffZ x * G x) =
      ∫ x in unitCube, G x * perX (fun y => cutoffZ y * ρ y) x := by
  have h1 : ∫ x in cutBall, ρ x * (cutoffZ x * G x) = ∫ x, G x * (cutoffZ x * ρ x) := by
    have h0 : ∫ x in cutBall, G x * (cutoffZ x * ρ x) = ∫ x, G x * (cutoffZ x * ρ x) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have : x ∉ tsupport ρ := fun h => hx (hρ.2.2 h)
        simp [image_eq_zero_of_notMem_tsupport this]
    rw [← h0]
    exact setIntegral_congr_fun isOpen_cutBall.measurableSet fun x _ => by ring
  rw [h1]
  exact integral_unfold_space (G := G) (ρ := fun y => cutoffZ y * ρ y)
    (cutoffZ_contDiff.mul hρ.1) (hρ.2.1.mul_left) hper hG

theorem integral_mul_lp_eq_inner {μ : Measure (Vec 2)} (u : Lp ℝ 2 μ) {ρ : Vec 2 → ℝ}
    (hρ : MemLp ρ 2 μ) :
    ∫ x, (u : Vec 2 → ℝ) x * ρ x ∂μ = inner ℝ (hρ.toLp ρ) u := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hρ.coeFn_toLp] with x hx
  rw [hx]
  simp [mul_comm]

theorem memLp_two_cutBall_of_isSpTest {ρ : Vec 2 → ℝ} (hρ : IsSpTest cutBall ρ) :
    MemLp ρ 2 (volume.restrict cutBall) := by
  have hc : Continuous ρ := hρ.1.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hρ.2.1
  have hfin : IsFiniteMeasure (volume.restrict cutBall : Measure (Vec 2)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (Metric.isBounded_ball.measure_lt_top)
  exact MemLp.of_bound hc.aestronglyMeasurable C (Eventually.of_forall hC)

/-- **Pairing identification.** -/
theorem trace_pair {w : ℝ → Vec 2 → ℝ} {t₁ t₂ : ℝ} (h12 : t₁ < t₂)
    (hslice : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (w t) ∧ MemL2On unitCube (w t))
    (hcont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, w t x * ψ x) (Set.Icc t₁ t₂))
    {W : ℝ → Lp ℝ 2 (volume.restrict cutBall)} (hWc : ContinuousOn W (Set.Icc t₁ t₂))
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y)
    {ρ : Vec 2 → ℝ} (hρ : IsSpTest cutBall ρ) {τ : ℝ} (hτ : τ ∈ Set.Icc t₁ t₂) :
    ∫ x in cutBall, (W τ : Vec 2 → ℝ) x * ρ x =
      ∫ x in unitCube, w τ x * perX (fun y => cutoffZ y * ρ y) x := by
  set a : ℝ → ℝ := fun σ => ∫ x in cutBall, (W σ : Vec 2 → ℝ) x * ρ x with ha
  set c : ℝ → ℝ := fun σ => ∫ x in unitCube, w σ x * perX (fun y => cutoffZ y * ρ y) x with hc
  have hρL := memLp_two_cutBall_of_isSpTest hρ
  have ha' : ∀ σ, a σ = inner ℝ (hρL.toLp ρ) (W σ) := fun σ => by
    simpa [ha] using integral_mul_lp_eq_inner (μ := volume.restrict cutBall) (W σ) hρL
  have haC : ContinuousOn a (Set.Icc t₁ t₂) := by
    have : a = fun σ => inner ℝ (hρL.toLp ρ) (W σ) := funext ha'
    rw [this]
    exact continuousOn_const.inner hWc
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (perX fun y => cutoffZ y * ρ y) :=
    perX_contDiff (cutoffZ_contDiff.mul hρ.1) hρ.2.1.mul_left
  have hcC : ContinuousOn c (Set.Icc t₁ t₂) :=
    hcont _ hψs (perX_periodic _)
  have hF := nhdsIoo_ae_neBot h12 hτ
  have hle : (𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ)) ≤ 𝓝[Set.Icc t₁ t₂] τ :=
    inf_le_left.trans (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
  have hta : Tendsto a (𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ)) (𝓝 (a τ)) :=
    (haC τ hτ).tendsto.mono_left hle
  have htc : Tendsto c (𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ)) (𝓝 (c τ)) :=
    (hcC τ hτ).tendsto.mono_left hle
  have hev : a =ᶠ[𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ)] c := by
    have e1 : ∀ᶠ σ in 𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ), σ ∈ Set.Ioo t₁ t₂ :=
      (eventually_mem_nhdsWithin).filter_mono inf_le_left
    have e2 : ∀ᶠ σ in 𝓝[Set.Ioo t₁ t₂] τ ⊓ ae (volume : Measure ℝ),
        (σ ∈ Set.Ioo t₁ t₂ → (W σ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall]
          fun y => cutoffZ y * w σ y) :=
      ((ae_restrict_iff' measurableSet_Ioo).1 hWae).filter_mono inf_le_right
    filter_upwards [e1, e2] with σ h1 h2
    have hσ := hslice σ (Set.Ioo_subset_Icc_self h1)
    have := h2 h1
    calc a σ = ∫ x in cutBall, (fun y => cutoffZ y * w σ y) x * ρ x :=
          integral_congr_ae (this.mono fun x hx => by simp [hx])
      _ = ∫ x in cutBall, ρ x * (cutoffZ x * w σ x) :=
          integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = c σ := cutoff_pairing hσ.1 (hσ.2.integrable (by norm_num)) hρ
  exact tendsto_nhds_unique_of_eventuallyEq hta htc hev

section Rep

variable {w : ℝ → Vec 2 → ℝ} {t₁ t₂ : ℝ}

theorem trace_rep (h12 : t₁ < t₂)
    (hslice : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (w t) ∧ MemL2On unitCube (w t))
    (hcont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, w t x * ψ x) (Set.Icc t₁ t₂))
    {W : ℝ → Lp ℝ 2 (volume.restrict cutBall)} (hWc : ContinuousOn W (Set.Icc t₁ t₂))
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y)
    {τ : ℝ} (hτ : τ ∈ Set.Icc t₁ t₂) :
    (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y := by
  have hfin : IsFiniteMeasure (volume.restrict cutBall : Measure (Vec 2)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (Metric.isBounded_ball.measure_lt_top)
  have hwτ := hslice τ hτ
  have hwint : Integrable (w τ) (volume.restrict (supBall 4)) :=
    integrableOn_supBall_space hwτ.1 (hwτ.2.integrable (by norm_num)) 4
  have hZw : Integrable (fun y => cutoffZ y * w τ y) (volume.restrict cutBall) := by
    have h1 : Integrable (w τ) (volume.restrict cutBall) :=
      hwint.mono_measure (Measure.restrict_mono cutBall_subset_supBall le_rfl)
    obtain ⟨C, hC⟩ := cutoffZ_contDiff.continuous.bounded_above_of_compact_support
      cutoffZ_hasCompactSupport
    exact h1.bdd_mul cutoffZ_contDiff.continuous.aestronglyMeasurable (c := C)
      (Eventually.of_forall hC)
  have hWint : Integrable (fun y => (W τ : Vec 2 → ℝ) y) (volume.restrict cutBall) :=
    (Lp.memLp (W τ)).integrable (by norm_num)
  have hf : IntegrableOn (fun y => (W τ : Vec 2 → ℝ) y - cutoffZ y * w τ y) cutBall volume :=
    hWint.sub hZw
  have key := isOpen_cutBall.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hf.locallyIntegrableOn (fun g hgs hgc hgsub => by
      have hg : IsSpTest cutBall g := ⟨hgs, hgc, hgsub⟩
      have hgL := memLp_two_cutBall_of_isSpTest hg
      have hgb : ∃ C, ∀ x, ‖g x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
        exact ⟨C, hC⟩
      have e0 : ∫ x in cutBall, g x • ((W τ : Vec 2 → ℝ) x - cutoffZ x * w τ x) =
          ∫ x, g x • ((W τ : Vec 2 → ℝ) x - cutoffZ x * w τ x) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have : x ∉ tsupport g := fun h => hx (hgsub h)
          simp [image_eq_zero_of_notMem_tsupport this]
      rw [← e0]
      obtain ⟨C, hC⟩ := hgb
      have i1 : Integrable (fun x => g x * (W τ : Vec 2 → ℝ) x) (volume.restrict cutBall) :=
        hWint.bdd_mul hgs.continuous.aestronglyMeasurable (c := C) (Eventually.of_forall hC)
      have i2 : Integrable (fun x => g x * (cutoffZ x * w τ x)) (volume.restrict cutBall) :=
        hZw.bdd_mul hgs.continuous.aestronglyMeasurable (c := C) (Eventually.of_forall hC)
      have e1 := trace_pair h12 hslice hcont hWc hWae hg hτ
      have e2 := cutoff_pairing hwτ.1 (hwτ.2.integrable (by norm_num)) hg
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub i1 i2]
      have : ∫ x in cutBall, g x * (W τ : Vec 2 → ℝ) x =
          ∫ x in cutBall, (W τ : Vec 2 → ℝ) x * g x :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      rw [this, e1, ← e2]
      ring)
  rw [Filter.EventuallyEq, ae_restrict_iff' isOpen_cutBall.measurableSet]
  filter_upwards [key] with x hx hxB
  exact sub_eq_zero.1 (hx hxB)

theorem trace_norm_sq (h12 : t₁ < t₂)
    (hslice : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (w t) ∧ MemL2On unitCube (w t))
    (hcont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, w t x * ψ x) (Set.Icc t₁ t₂))
    {W : ℝ → Lp ℝ 2 (volume.restrict cutBall)} (hWc : ContinuousOn W (Set.Icc t₁ t₂))
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y)
    {τ : ℝ} (hτ : τ ∈ Set.Icc t₁ t₂) : ‖W τ‖ ^ 2 = l2NormSq (w τ) := by
  have hwτ := hslice τ hτ
  have hrep := trace_rep h12 hslice hcont hWc hWae hτ
  rw [← LocalEnergy.integral_sq_lp]
  have h1 : ∫ x in cutBall, (W τ : Vec 2 → ℝ) x ^ 2 =
      ∫ x in cutBall, cutoffZ x * (cutoffZ x * w τ x ^ 2) :=
    integral_congr_ae (hrep.mono fun x hx => by simp [hx]; ring)
  rw [h1]
  have h2 := cutoff_pairing (G := fun x => w τ x ^ 2) (ρ := cutoffZ)
    (fun k x => by simp [hwτ.1 k x]) hwτ.2.integrable_sq isSpTest_cutoffZ
  have h3 : ∫ x in unitCube, w τ x ^ 2 * perX (fun y => cutoffZ y * cutoffZ y) x =
      l2NormSq (w τ) := by
    unfold l2NormSq
    refine setIntegral_congr_fun measurableSet_unitCube' fun x _ => ?_
    have : perX (fun y => cutoffZ y * cutoffZ y) x = 1 := by
      simpa [sq] using perX_cutoffZ_sq x
    simp [this]
  rw [← h3, ← h2]

theorem trace_initial (h12 : t₁ < t₂)
    (hslice : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (w t) ∧ MemL2On unitCube (w t))
    (hcont : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, w t x * ψ x) (Set.Icc t₁ t₂))
    (hinit : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ∫ x in unitCube, w t₁ x * ψ x = 0)
    {W : ℝ → Lp ℝ 2 (volume.restrict cutBall)} (hWc : ContinuousOn W (Set.Icc t₁ t₂))
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y) :
    ‖W t₁‖ ^ 2 = 0 := by
  have hτ : t₁ ∈ Set.Icc t₁ t₂ := ⟨le_rfl, h12.le⟩
  have hfin : IsFiniteMeasure (volume.restrict cutBall : Measure (Vec 2)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (Metric.isBounded_ball.measure_lt_top)
  have hWint : Integrable (fun y => (W t₁ : Vec 2 → ℝ) y) (volume.restrict cutBall) :=
    (Lp.memLp (W t₁)).integrable (by norm_num)
  have key := isOpen_cutBall.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun y => (W t₁ : Vec 2 → ℝ) y)
    (show IntegrableOn (fun y => (W t₁ : Vec 2 → ℝ) y) cutBall volume from hWint).locallyIntegrableOn (fun g hgs hgc hgsub => by
      have hg : IsSpTest cutBall g := ⟨hgs, hgc, hgsub⟩
      have e0 : ∫ x in cutBall, g x • (W t₁ : Vec 2 → ℝ) x =
          ∫ x, g x • (W t₁ : Vec 2 → ℝ) x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have : x ∉ tsupport g := fun h => hx (hgsub h)
          simp [image_eq_zero_of_notMem_tsupport this]
      rw [← e0]
      have e1 := trace_pair h12 hslice hcont hWc hWae hg hτ
      have hψs : ContDiff ℝ (⊤ : ℕ∞) (perX fun y => cutoffZ y * g y) :=
        perX_contDiff (cutoffZ_contDiff.mul hgs) hgc.mul_left
      have := hinit _ hψs (perX_periodic _)
      simp only [smul_eq_mul]
      rw [show (∫ x in cutBall, g x * (W t₁ : Vec 2 → ℝ) x) =
        ∫ x in cutBall, (W t₁ : Vec 2 → ℝ) x * g x from
          integral_congr_ae (Eventually.of_forall fun x => by ring), e1, this])
  have hzero : (W t₁ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' isOpen_cutBall.measurableSet]
    filter_upwards [key] with x hx hxB
    exact hx hxB
  rw [← LocalEnergy.integral_sq_lp]
  have : ∫ x in cutBall, (W t₁ : Vec 2 → ℝ) x ^ 2 = ∫ x in cutBall, (0 : ℝ) :=
    integral_congr_ae (hzero.mono fun x hx => by simp [hx])
  rw [this]
  simp

end Rep
end

/-! # The forced energy identity on the torus -/

section
theorem perX_cutoffZ_sq_grad (x : Vec 2) (i : Fin 2) :
    perX (fun y => spaceGrad (fun z => cutoffZ z ^ 2) y i) x = 0 := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (fun (_ : ℝ) y => cutoffZ y ^ 2) p.1 p.2) :=
    (cutoffZ_contDiff.comp contDiff_snd).pow 2
  have h := spaceGrad_perST cutoffZ_sq_supBdd hs 0 x i
  have h1 : perST (fun (_ : ℝ) y => cutoffZ y ^ 2) 0 = fun _ => 1 := by
    funext y; exact perX_cutoffZ_sq y
  rw [h1] at h
  have h2 : spaceGrad (fun _ : Vec 2 => (1 : ℝ)) x i = 0 := by simp [spaceGrad]
  rw [h2] at h
  exact h.symm

theorem spaceGrad_cutoffZ_sq (y : Vec 2) (i : Fin 2) :
    spaceGrad (fun z => cutoffZ z ^ 2) y i = 2 * cutoffZ y * spGrad cutoffZ y i := by
  have hd : DifferentiableAt ℝ cutoffZ y := (cutoffZ_contDiff.differentiable (by simp)) y
  simp only [spaceGrad, spGrad]
  rw [fderiv_fun_pow 2 hd]
  simp

section Main

variable {w : ℝ → Vec 2 → ℝ} {Dw P : ℝ → Vec 2 → Vec 2} {g : ℝ → Vec 2 → ℝ} {t₁ t₂ : ℝ}

theorem integrable_mul_window {a b : ℝ} {f₁ f₂ : ℝ × Vec 2 → ℝ}
    (h1 : MemLp f₁ 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube)))
    (h2 : MemLp f₂ 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    Integrable (fun p => f₁ p * f₂ p) (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
  have : MemLp (fun p => f₁ p * f₂ p) 1 (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := h1.mul h2
  exact this.integrable le_rfl

theorem forced_rhs_unfold (h : IsTorusForced w Dw P g t₁ t₂) {τ₁ τ₂ : ℝ} (h1 : t₁ ≤ τ₁)
    (h2 : τ₂ ≤ t₂) :
    ∫ p in Set.Ioo τ₁ τ₂ ×ˢ cutBall,
      (vecDot (P p.1 p.2) (cutoffZ p.2 ^ 2 • Dw p.1 p.2
          + (2 * cutoffZ p.2 * w p.1 p.2) • spGrad cutoffZ p.2)
        - g p.1 p.2 * cutoffZ p.2 ^ 2 * w p.1 p.2) =
    ∫ p in Set.Ioo τ₁ τ₂ ×ˢ unitCube,
      (vecDot (P p.1 p.2) (Dw p.1 p.2) - g p.1 p.2 * w p.1 p.2) := by
  have hS : MeasurableSet (Set.Ioo τ₁ τ₂) := measurableSet_Ioo
  have hsub : Set.Ioo τ₁ τ₂ ⊆ Set.Ioo t₁ t₂ := Set.Ioo_subset_Ioo h1 h2
  have hmono : (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ unitCube) : Measure (ℝ × Vec 2)) ≤
      volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube) :=
    Measure.restrict_mono (Set.prod_mono hsub le_rfl) le_rfl
  have hae : ∀ {Q : ℝ → Prop}, (∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), Q t) →
      ∀ᵐ t ∂(volume.restrict (Set.Ioo τ₁ τ₂)), Q t := fun hQ =>
    ae_restrict_of_ae_restrict_of_subset hsub hQ
  have hwper : ∀ᵐ t ∂(volume.restrict (Set.Ioo τ₁ τ₂)), IsZ2Periodic (w t) := by
    refine hae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (h.slice t (Set.Ioo_subset_Icc_self ht)).1
  have hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo τ₁ τ₂)), IsZ2Periodic (Dw t) :=
    hae (h.h1.mono fun t ht => ht.2.1)
  have hPper := hae h.Pper
  have hgper := hae h.gper
  -- the four unfolded integrands
  set ρ₀ : Vec 2 → ℝ := fun y => cutoffZ y ^ 2 with hρ₀
  set ρ : Fin 2 → Vec 2 → ℝ := fun i y => spaceGrad (fun z => cutoffZ z ^ 2) y i with hρ
  have hρ₀s : ContDiff ℝ (⊤ : ℕ∞) ρ₀ := cutoffZ_contDiff.pow 2
  have hρ₀c : HasCompactSupport ρ₀ := by
    have : ρ₀ = fun y => cutoffZ y * cutoffZ y := by funext y; simp [hρ₀, sq]
    rw [this]
    exact cutoffZ_hasCompactSupport.mul_left
  have hρs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ρ i) := fun i =>
    contDiff_fderiv_apply_of_smooth hρ₀s (basisVec i)
  have hρc : ∀ i, HasCompactSupport (ρ i) := fun i =>
    hasCompactSupport_fderiv_apply hρ₀c (basisVec i)
  have iA : Integrable (fun p : ℝ × Vec 2 => vecDot (P p.1 p.2) (Dw p.1 p.2))
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ unitCube)) := by
    have : (fun p : ℝ × Vec 2 => vecDot (P p.1 p.2) (Dw p.1 p.2)) =
        fun p => P p.1 p.2 0 * Dw p.1 p.2 0 + P p.1 p.2 1 * Dw p.1 p.2 1 := by
      funext p; simp [vecDot, Fin.sum_univ_two]
    rw [this]
    exact ((integrable_mul_window (h.memP 0) (h.memDw 0)).add
      (integrable_mul_window (h.memP 1) (h.memDw 1))).mono_measure hmono
  have iI : ∀ i, Integrable (fun p : ℝ × Vec 2 => P p.1 p.2 i * w p.1 p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ unitCube)) := fun i =>
    (integrable_mul_window (h.memP i) h.memw).mono_measure hmono
  have iG : Integrable (fun p : ℝ × Vec 2 => g p.1 p.2 * w p.1 p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ unitCube)) :=
    (integrable_mul_window h.memg h.memw).mono_measure hmono
  obtain ⟨a1, a2, a3⟩ := integral_unfold_x hS hρ₀s hρ₀c
    (G := fun t x => vecDot (P t x) (Dw t x))
    (by filter_upwards [hPper, hDper] with t h1 h2 using vecDot_periodic h1 h2) iA
  obtain ⟨g1, g2, g3⟩ := integral_unfold_x hS hρ₀s hρ₀c
    (G := fun t x => g t x * w t x)
    (by
      filter_upwards [hgper, hwper] with t h1 h2
      intro k x
      simp only [h1 k x, h2 k x]) iG
  obtain ⟨c01, c02, c03⟩ := integral_unfold_x hS (hρs 0) (hρc 0)
    (G := fun t x => P t x 0 * w t x)
    (by
      filter_upwards [hPper, hwper] with t h1 h2
      intro k x
      simp only [h1 k x, h2 k x]) (iI 0)
  obtain ⟨c11, c12, c13⟩ := integral_unfold_x hS (hρs 1) (hρc 1)
    (G := fun t x => P t x 1 * w t x)
    (by
      filter_upwards [hPper, hwper] with t h1 h2
      intro k x
      simp only [h1 k x, h2 k x]) (iI 1)
  have hF : ∀ p : ℝ × Vec 2,
      (vecDot (P p.1 p.2) (cutoffZ p.2 ^ 2 • Dw p.1 p.2
          + (2 * cutoffZ p.2 * w p.1 p.2) • spGrad cutoffZ p.2)
        - g p.1 p.2 * cutoffZ p.2 ^ 2 * w p.1 p.2) =
      vecDot (P p.1 p.2) (Dw p.1 p.2) * ρ₀ p.2 + P p.1 p.2 0 * w p.1 p.2 * ρ 0 p.2
        + P p.1 p.2 1 * w p.1 p.2 * ρ 1 p.2 - g p.1 p.2 * w p.1 p.2 * ρ₀ p.2 := by
    intro p
    simp only [hρ₀, hρ, spaceGrad_cutoffZ_sq, vecDot, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hB : ∫ p in Set.Ioo τ₁ τ₂ ×ˢ cutBall,
      (vecDot (P p.1 p.2) (cutoffZ p.2 ^ 2 • Dw p.1 p.2
          + (2 * cutoffZ p.2 * w p.1 p.2) • spGrad cutoffZ p.2)
        - g p.1 p.2 * cutoffZ p.2 ^ 2 * w p.1 p.2) =
      ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (Vec 2)),
      (vecDot (P p.1 p.2) (cutoffZ p.2 ^ 2 • Dw p.1 p.2
          + (2 * cutoffZ p.2 * w p.1 p.2) • spGrad cutoffZ p.2)
        - g p.1 p.2 * cutoffZ p.2 ^ 2 * w p.1 p.2) := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hS.prod MeasurableSet.univ) (Set.prod_mono le_rfl (Set.subset_univ _)) ?_).symm
    rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hn⟩
    have hx : x ∉ cutBall := fun hx => hn ⟨ht, hx⟩
    have hz : cutoffZ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h' => hx (isSpTest_cutoffZ.2.2 h'))
    simp [hz, vecDot]
  rw [hB]
  simp_rw [hF]
  have s2 : Integrable (fun p : ℝ × Vec 2 => vecDot (P p.1 p.2) (Dw p.1 p.2) * ρ₀ p.2
      + P p.1 p.2 0 * w p.1 p.2 * ρ 0 p.2) (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ Set.univ)) :=
    a1.add c01
  have s3 : Integrable (fun p : ℝ × Vec 2 => vecDot (P p.1 p.2) (Dw p.1 p.2) * ρ₀ p.2
      + P p.1 p.2 0 * w p.1 p.2 * ρ 0 p.2 + P p.1 p.2 1 * w p.1 p.2 * ρ 1 p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ Set.univ)) := s2.add c11
  rw [integral_sub s3 g1, integral_add s2 c11, integral_add a1 c01, a3, c03, c13, g3]
  have hper0 : ∀ x, perX ρ₀ x = 1 := fun x => perX_cutoffZ_sq x
  have hper1 : ∀ i x, perX (ρ i) x = 0 := fun i x => perX_cutoffZ_sq_grad x i
  simp only [hper0, hper1, mul_one, mul_zero, integral_zero, add_zero]
  rw [← integral_sub iA iG]

theorem memLp_window_cutBall {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (G t))
    (hG : MemLp (fun p : ℝ × Vec 2 => G p.1 p.2) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => G p.1 p.2) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ cutBall)) :=
  (memLp_two_supBall_of_cell measurableSet_Ioo hper hG 4).mono_measure
    (Measure.restrict_mono (Set.prod_mono le_rfl cutBall_subset_supBall) le_rfl)

/-- The cutoff `L²` trace of a forced torus solution. -/
theorem forced_W (h12 : t₁ < t₂) (h : IsTorusForced w Dw P g t₁ t₂) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict cutBall), ContinuousOn W (Set.Icc t₁ t₂) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall] fun y => cutoffZ y * w τ y) ∧
      ∀ τ₁ ∈ Set.Icc t₁ t₂, ∀ τ₂ ∈ Set.Icc t₁ t₂, τ₁ ≤ τ₂ →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ cutBall,
          (vecDot (P p.1 p.2) (cutoffZ p.2 ^ 2 • Dw p.1 p.2
            + (2 * cutoffZ p.2 * w p.1 p.2) • spGrad cutoffZ p.2)
          - g p.1 p.2 * cutoffZ p.2 ^ 2 * w p.1 p.2) := by
  have hwper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (w t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (h.slice t (Set.Ioo_subset_Icc_self ht)).1
  have hDcper : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => Dw t x i) := fun i =>
    h.h1.mono fun t ht k x => by simp [ht.2.1 k x]
  have hPcper : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => P t x i) := fun i =>
    h.Pper.mono fun t ht k x => by simp [ht k x]
  have hU := memLp_window_cutBall (G := w) hwper h.memw
  have hDU := fun i => memLp_window_cutBall (G := fun t x => Dw t x i) (hDcper i) (h.memDw i)
  have hP := fun i => memLp_window_cutBall (G := fun t x => P t x i) (hPcper i) (h.memP i)
  have hg := memLp_window_cutBall (G := g) h.gper h.memg
  have hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo t₁ t₂)),
      HasWeakGradientOn cutBall (fun y => w τ y) (fun y => Dw τ y) :=
    h.h1.mono fun t ht => hasWeakGradientOn_univ_mono ht.2.2.2.2 cutBall
  have hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo t₁ t₂ ×ˢ cutBall) φ →
      ∫ p in Set.Ioo t₁ t₂ ×ˢ cutBall,
        (-(w p.1 p.2 * stTimeDeriv φ p) + vecDot (P p.1 p.2) (stSpaceGrad φ p)
          - g p.1 p.2 * φ p) = 0 := by
    intro φ hφ
    have hφ' : IsSTTest (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) φ :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans (Set.prod_mono le_rfl (Set.subset_univ _))⟩
    rw [← h.weak φ hφ']
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioo.prod MeasurableSet.univ) (Set.prod_mono le_rfl (Set.subset_univ _))
      ?_).symm
    intro p hp
    have : p ∉ tsupport φ := fun h' => hp.2 (hφ.2.2 h')
    have hsg : stSpaceGrad φ p = 0 := by
      funext i
      simp [stSpaceGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
    simp [stTimeDeriv, hsg, fderiv_of_notMem_tsupport (𝕜 := ℝ) this,
      image_eq_zero_of_notMem_tsupport this, vecDot]
  exact local_trace_aux h12 isOpen_cutBall
    (U := fun p => w p.1 p.2) (g := fun p => g p.1 p.2) (DU := fun p => Dw p.1 p.2)
    (P := fun p => P p.1 p.2) hU hDU hgrad hP hg hweak cutoffZ isSpTest_cutoffZ

/-- **Forced energy identity on the torus.** -/
theorem torus_forced_energy_identity (h12 : t₁ < t₂) (h : IsTorusForced w Dw P g t₁ t₂) :
    ∀ τ₁ ∈ Set.Icc t₁ t₂, ∀ τ₂ ∈ Set.Icc t₁ t₂, τ₁ ≤ τ₂ →
      l2NormSq (w τ₂) - l2NormSq (w τ₁) = -2 * ∫ p in Set.Ioo τ₁ τ₂ ×ˢ unitCube,
        (vecDot (P p.1 p.2) (Dw p.1 p.2) - g p.1 p.2 * w p.1 p.2) := by
  obtain ⟨W, hWc, hWae, hWid⟩ := forced_W h12 h
  intro τ₁ hτ₁ τ₂ hτ₂ hle
  have hid := hWid τ₁ hτ₁ τ₂ hτ₂ hle
  rw [trace_norm_sq h12 h.slice h.cont hWc hWae hτ₂, trace_norm_sq h12 h.slice h.cont hWc hWae hτ₁]
    at hid
  rw [hid]
  congr 1
  rw [← forced_rhs_unfold h hτ₁.1 hτ₂.2]
  have hae : (Set.Ioc τ₁ τ₂ ×ˢ cutBall : Set (ℝ × Vec 2)) =ᵐ[volume]
      (Set.Ioo τ₁ τ₂ ×ˢ cutBall : Set (ℝ × Vec 2)) := by
    have := Measure.set_prod_ae_eq (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
      (Ioo_ae_eq_Ioc (a := τ₁) (b := τ₂)).symm (Filter.EventuallyEq.refl _ cutBall)
    rwa [← Measure.volume_eq_prod] at this
  rw [Measure.restrict_congr_set hae]

/-- If `w(t₁) = 0` weakly, then `‖w(t₁)‖_{L²(𝕋²)} = 0`. -/
theorem torus_forced_initial_zero (h12 : t₁ < t₂) (h : IsTorusForced w Dw P g t₁ t₂)
    (hinit : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ∫ x in unitCube, w t₁ x * ψ x = 0) : l2NormSq (w t₁) = 0 := by
  obtain ⟨W, hWc, hWae, -⟩ := forced_W h12 h
  rw [← trace_norm_sq h12 h.slice h.cont hWc hWae ⟨le_rfl, h12.le⟩]
  exact trace_initial h12 h.slice h.cont hinit hWc hWae

end Main
end

/-! # Integration by parts on `ℝ²` and `𝕋²`; divergence-free streams; the skew identity

The skew form of the stream identities. -/

section
theorem continuous_fderiv_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (v : Vec 2) :
    Continuous fun x => fderiv ℝ f x v :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem ibp_c1_left {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (v : Vec 2) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ (fun x _ =>
    (hf.differentiable (by simp)) x) (fun x _ => (hg.differentiable (by simp)) x)
  · exact ((continuous_fderiv_apply hf v).mul hg.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hfc v).mul_right)
  · exact (hf.continuous.mul (continuous_fderiv_apply hg v)).integrable_of_hasCompactSupport
      hfc.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right

theorem ibp_c1_right {f g : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : Vec 2) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ (fun x _ =>
    (hf.differentiable (by simp)) x) (fun x _ => (hg.differentiable (by simp)) x)
  · exact ((continuous_fderiv_apply hf v).mul hg.continuous).integrable_of_hasCompactSupport
      hgc.mul_left
  · exact (hf.continuous.mul (continuous_fderiv_apply hg v)).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hgc v).mul_left)
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left

/-- `∫ ∂ᵥ g = 0` for `g ∈ C¹_c`. -/
theorem integral_fderiv_eq_zero_c1 {g : Vec 2 → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : Vec 2) : ∫ x, fderiv ℝ g x v = 0 := by
  have := ibp_c1_right (f := fun _ => (1 : ℝ)) contDiff_const hg hgc v
  simpa using this

theorem cutoffZ_sq_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun y => cutoffZ y ^ 2) :=
  cutoffZ_contDiff.pow 2

theorem cutoffZ_sq_hasCompactSupport : HasCompactSupport (fun y => cutoffZ y ^ 2) := by
  have : (fun y => cutoffZ y ^ 2) = fun y => cutoffZ y * cutoffZ y := by funext y; simp [sq]
  rw [this]
  exact cutoffZ_hasCompactSupport.mul_left

theorem fderiv_periodic {F : Vec 2 → ℝ} (hp : IsZ2Periodic F) (n : Fin 2 → ℤ) (x : Vec 2) :
    fderiv ℝ F (x + latticeShift n) = fderiv ℝ F x := by
  have h : (fun y => F (y + latticeShift n)) = F := funext fun y => hp n y
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (latticeShift n) (x := x)
  rw [h] at this
  exact this.symm

theorem integrableOn_cube_of_continuous {g : Vec 2 → ℝ} (hg : Continuous g) :
    Integrable g (volume.restrict unitCube) := by
  obtain ⟨C, hC⟩ := exists_bound_cube hg
  refine Measure.integrableOn_of_bounded (M := C) unitCube_measure_ne_top
    hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
  simpa using hC x hx

/-- `∫_{𝕋²} (∂₁F₁ + ∂₂F₂) = 0` for `C¹` periodic fields. -/
theorem integral_div_periodic {F₁ F₂ : Vec 2 → ℝ} (h1 : ContDiff ℝ 1 F₁) (h2 : ContDiff ℝ 1 F₂)
    (p1 : IsZ2Periodic F₁) (p2 : IsZ2Periodic F₂) :
    ∫ x in unitCube, (fderiv ℝ F₁ x (basisVec 0) + fderiv ℝ F₂ x (basisVec 1)) = 0 := by
  set D : Vec 2 → ℝ := fun x => fderiv ℝ F₁ x (basisVec 0) + fderiv ℝ F₂ x (basisVec 1) with hD
  have hDc : Continuous D :=
    (continuous_fderiv_apply h1 _).add (continuous_fderiv_apply h2 _)
  have hDp : IsZ2Periodic D := fun n x => by simp [hD, fderiv_periodic p1 n x, fderiv_periodic p2 n x]
  set ρ₀ : Vec 2 → ℝ := fun y => cutoffZ y ^ 2 with hρ₀
  have e1 : ∫ x in unitCube, D x = ∫ x, D x * ρ₀ x := by
    rw [integral_unfold_space cutoffZ_sq_contDiff cutoffZ_sq_hasCompactSupport hDp
      (integrableOn_cube_of_continuous hDc)]
    refine setIntegral_congr_fun measurableSet_unitCube' fun x _ => ?_
    simp [perX_cutoffZ_sq x]
  have hcs : ∀ {F : Vec 2 → ℝ}, ContDiff ℝ 1 F → ∀ v : Vec 2,
      Integrable (fun x => fderiv ℝ F x v * ρ₀ x) := fun hF v =>
    ((continuous_fderiv_apply hF v).mul
      (cutoffZ_sq_contDiff.continuous)).integrable_of_hasCompactSupport
      cutoffZ_sq_hasCompactSupport.mul_left
  have e2 : ∫ x, D x * ρ₀ x = -(∫ x, F₁ x * fderiv ℝ ρ₀ x (basisVec 0))
      - (∫ x, F₂ x * fderiv ℝ ρ₀ x (basisVec 1)) := by
    have a1 := ibp_c1_left (f := ρ₀) (g := F₁) (cutoffZ_sq_contDiff.of_le (by simp)) h1
      cutoffZ_sq_hasCompactSupport (basisVec 0)
    have a2 := ibp_c1_left (f := ρ₀) (g := F₂) (cutoffZ_sq_contDiff.of_le (by simp)) h2
      cutoffZ_sq_hasCompactSupport (basisVec 1)
    have i1 : Integrable (fun x => ρ₀ x * fderiv ℝ F₁ x (basisVec 0)) := by
      have := hcs h1 (basisVec 0)
      exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
    have i2 : Integrable (fun x => ρ₀ x * fderiv ℝ F₂ x (basisVec 1)) := by
      have := hcs h2 (basisVec 1)
      exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
    have : ∫ x, D x * ρ₀ x = (∫ x, ρ₀ x * fderiv ℝ F₁ x (basisVec 0)) +
        ∫ x, ρ₀ x * fderiv ℝ F₂ x (basisVec 1) := by
      rw [← integral_add i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hD]; ring)
    have c1 : ∫ x, fderiv ℝ ρ₀ x (basisVec 0) * F₁ x = ∫ x, F₁ x * fderiv ℝ ρ₀ x (basisVec 0) :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have c2 : ∫ x, fderiv ℝ ρ₀ x (basisVec 1) * F₂ x = ∫ x, F₂ x * fderiv ℝ ρ₀ x (basisVec 1) :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [this, a1, a2, c1, c2]
    ring
  have e3 : ∀ (F : Vec 2 → ℝ), ContDiff ℝ 1 F → IsZ2Periodic F → ∀ i : Fin 2,
      ∫ x, F x * fderiv ℝ ρ₀ x (basisVec i) = 0 := by
    intro F hF hp i
    have hρs : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ρ₀ x (basisVec i)) :=
      contDiff_fderiv_apply_of_smooth cutoffZ_sq_contDiff _
    have hρc : HasCompactSupport (fun x => fderiv ℝ ρ₀ x (basisVec i)) :=
      hasCompactSupport_fderiv_apply cutoffZ_sq_hasCompactSupport _
    rw [integral_unfold_space hρs hρc hp (integrableOn_cube_of_continuous hF.continuous)]
    have : ∀ x, perX (fun x => fderiv ℝ ρ₀ x (basisVec i)) x = 0 := fun x =>
      perX_cutoffZ_sq_grad x i
    simp [this]
  rw [e1, e2, e3 F₁ h1 p1 0, e3 F₂ h2 p2 1]
  simp

/-- The planar cross product `a × b = a₀ b₁ - a₁ b₀ = (σ a)·b`. -/
def crossDot (a b : Vec 2) : ℝ := a 0 * b 1 - a 1 * b 0

theorem vecDot_sigma (a b : Vec 2) : vecDot (sigmaMat.mulVec a) b = crossDot a b := by
  simp [vecDot, crossDot, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem mixed_symm {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) =
      fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)) x
  have key : ∀ k : Fin 2, fderiv ℝ (fun y => fderiv ℝ f y (basisVec k)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec k) := fun k => by
    have := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ f) (u := fun _ => basisVec k) (x := x) hd
      (differentiableAt_const _)
    simpa using this
  rw [key, key]
  have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  simpa using (hsym (basisVec j) (basisVec i)).symm

theorem contDiff_one_of_top {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 1 f :=
  hf.of_le (by exact_mod_cast le_top)

theorem contDiff_fderiv_apply_one {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec 2) :
    ContDiff ℝ 1 fun x => fderiv ℝ f x v :=
  contDiff_one_of_top (contDiff_fderiv_apply_of_smooth hf v)

/-- Pointwise: the divergence of `(φ ∂₂f, -φ ∂₁f)` is `∇φ × ∇f`. -/
theorem div_stream_field {φ f : Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Vec 2) :
    fderiv ℝ (fun y => φ y * fderiv ℝ f y (basisVec 1)) x (basisVec 0) +
      fderiv ℝ (fun y => -(φ y * fderiv ℝ f y (basisVec 0))) x (basisVec 1) =
      crossDot (spaceGrad φ x) (spaceGrad f x) := by
  have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
  have hd : ∀ k : Fin 2, DifferentiableAt ℝ (fun y => fderiv ℝ f y (basisVec k)) x := fun k =>
    ((contDiff_fderiv_apply_of_smooth hf (basisVec k)).differentiable (by simp)) x
  rw [fderiv_fun_neg, fderiv_fun_mul hφd (hd 0), fderiv_fun_mul hφd (hd 1)]
  have h01 := mixed_symm hf x 0 1
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, crossDot, spaceGrad]
  rw [h01]
  ring

theorem integral_cross_compact {φ χ : Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∫ x, crossDot (spaceGrad φ x) (spaceGrad χ x) = 0 := by
  have hc : ∀ k : Fin 2, HasCompactSupport (fun y => fderiv ℝ χ y (basisVec k)) := fun k =>
    hasCompactSupport_fderiv_apply hχc _
  have h1 : ContDiff ℝ 1 (fun y => φ y * fderiv ℝ χ y (basisVec 1)) :=
    hφ.mul (contDiff_fderiv_apply_one hχ _)
  have h2 : ContDiff ℝ 1 (fun y => -(φ y * fderiv ℝ χ y (basisVec 0))) :=
    (hφ.mul (contDiff_fderiv_apply_one hχ _)).neg
  have c1 : HasCompactSupport (fun y => φ y * fderiv ℝ χ y (basisVec 1)) := (hc 1).mul_left
  have c2 : HasCompactSupport (fun y => -(φ y * fderiv ℝ χ y (basisVec 0))) :=
    ((hc 0).mul_left).neg
  have i1 := (continuous_fderiv_apply h1 (basisVec 0)).integrable_of_hasCompactSupport
    (μ := (volume : Measure (Vec 2)))
    (hasCompactSupport_fderiv_apply c1 (basisVec 0))
  have i2 := (continuous_fderiv_apply h2 (basisVec 1)).integrable_of_hasCompactSupport
    (μ := (volume : Measure (Vec 2)))
    (hasCompactSupport_fderiv_apply c2 (basisVec 1))
  have := integral_add i1 i2
  rw [integral_fderiv_eq_zero_c1 h1 c1, integral_fderiv_eq_zero_c1 h2 c2, add_zero] at this
  calc ∫ x, crossDot (spaceGrad φ x) (spaceGrad χ x)
      = ∫ x, (fderiv ℝ (fun y => φ y * fderiv ℝ χ y (basisVec 1)) x (basisVec 0) +
        fderiv ℝ (fun y => -(φ y * fderiv ℝ χ y (basisVec 0))) x (basisVec 1)) :=
        integral_congr_ae (Eventually.of_forall fun x => (div_stream_field hφ hχ x).symm)
    _ = 0 := this

/-- Streams are divergence free against compactly supported tests. -/
theorem streamVel_integral_zero {φ : ℝ → Vec 2 → ℝ} (hφ : ∀ t, ContDiff ℝ 1 (φ t)) (t : ℝ)
    {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∫ x, vecDot (streamVel φ t x) (spaceGrad χ x) = 0 := by
  have := integral_cross_compact (hφ t) hχ hχc
  have e : ∀ x, vecDot (streamVel φ t x) (spaceGrad χ x) =
      crossDot (spaceGrad (φ t) x) (spaceGrad χ x) := fun x => vecDot_sigma _ _
  simp_rw [e]
  exact this

theorem continuous_spaceGrad_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous fun x => spaceGrad f x i := continuous_fderiv_apply hf (basisVec i)

theorem continuous_crossDot_grad {a b : Vec 2 → ℝ} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    Continuous fun x => crossDot (spaceGrad a x) (spaceGrad b x) := by
  unfold crossDot
  exact ((continuous_spaceGrad_apply ha 0).mul (continuous_spaceGrad_apply hb 1)).sub
    ((continuous_spaceGrad_apply ha 1).mul (continuous_spaceGrad_apply hb 0))

/-- Pointwise: divergence of `(ψ ∂₂v w, -ψ ∂₁v w)`. -/
theorem div_skew_field {ψ v w : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : Vec 2) :
    fderiv ℝ (fun y => ψ y * fderiv ℝ v y (basisVec 1) * w y) x (basisVec 0) +
      fderiv ℝ (fun y => -(ψ y * fderiv ℝ v y (basisVec 0) * w y)) x (basisVec 1) =
      crossDot (spaceGrad ψ x) (spaceGrad v x) * w x
        - ψ x * crossDot (spaceGrad v x) (spaceGrad w x) := by
  have hψd : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
  have hwd : DifferentiableAt ℝ w x := (hw.differentiable (by simp)) x
  have hd : ∀ k : Fin 2, DifferentiableAt ℝ (fun y => fderiv ℝ v y (basisVec k)) x := fun k =>
    ((contDiff_fderiv_apply_of_smooth hv (basisVec k)).differentiable (by simp)) x
  have hm : ∀ k : Fin 2, DifferentiableAt ℝ (fun y => ψ y * fderiv ℝ v y (basisVec k)) x :=
    fun k => hψd.mul (hd k)
  rw [fderiv_fun_neg, fderiv_fun_mul (hm 1) hwd, fderiv_fun_mul (hm 0) hwd,
    fderiv_fun_mul hψd (hd 1), fderiv_fun_mul hψd (hd 0)]
  have h01 := mixed_symm hv x 0 1
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, crossDot, spaceGrad]
  rw [h01]
  ring

theorem skew_smooth {ψ v w : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (pψ : IsZ2Periodic ψ) (pv : IsZ2Periodic v)
    (pw : IsZ2Periodic w) :
    ∫ x in unitCube, crossDot (spaceGrad ψ x) (spaceGrad v x) * w x =
      ∫ x in unitCube, ψ x * crossDot (spaceGrad v x) (spaceGrad w x) := by
  have hv1 := contDiff_one_of_top hv
  have hw1 := contDiff_one_of_top hw
  have h := integral_div_periodic
    (F₁ := fun y => ψ y * fderiv ℝ v y (basisVec 1) * w y)
    (F₂ := fun y => -(ψ y * fderiv ℝ v y (basisVec 0) * w y))
    ((hψ.mul (contDiff_fderiv_apply_one hv _)).mul hw1)
    (((hψ.mul (contDiff_fderiv_apply_one hv _)).mul hw1).neg)
    (fun n x => by simp [pψ n x, fderiv_periodic pv n x, pw n x])
    (fun n x => by simp [pψ n x, fderiv_periodic pv n x, pw n x])
  have hA : Integrable (fun x => crossDot (spaceGrad ψ x) (spaceGrad v x) * w x)
      (volume.restrict unitCube) :=
    integrableOn_cube_of_continuous ((continuous_crossDot_grad hψ hv1).mul hw.continuous)
  have hB : Integrable (fun x => ψ x * crossDot (spaceGrad v x) (spaceGrad w x))
      (volume.restrict unitCube) :=
    integrableOn_cube_of_continuous (hψ.continuous.mul (continuous_crossDot_grad hv1 hw1))
  have h2 : ∫ x in unitCube, (crossDot (spaceGrad ψ x) (spaceGrad v x) * w x
      - ψ x * crossDot (spaceGrad v x) (spaceGrad w x)) = 0 := by
    rw [← h]
    exact setIntegral_congr_fun measurableSet_unitCube' fun x _ =>
      (div_skew_field hψ hv hw x).symm
  rw [integral_sub hA hB] at h2
  linarith

theorem memL2_mul_continuous {c g : Vec 2 → ℝ} (hc : Continuous c)
    (hg : MemL2On unitCube g) : MemL2On unitCube (fun x => c x * g x) := by
  obtain ⟨C, hC⟩ := exists_bound_cube hc
  have hcm : MemLp c ⊤ (volume.restrict unitCube) :=
    MemLp.of_bound hc.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx using by
        simpa using hC x hx)
  exact hcm.mul hg

theorem memL2_continuous {c : Vec 2 → ℝ} (hc : Continuous c) : MemL2On unitCube c :=
  AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On hc

theorem integrable_mul_memL2 {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    (hg : MemL2On unitCube g) : Integrable (fun x => f x * g x) (volume.restrict unitCube) := by
  have : MemLp (fun x => f x * g x) 1 (volume.restrict unitCube) := hf.mul hg
  exact this.integrable le_rfl

section Slots

variable {R : ℕ → Vec 2 → ℝ} {DR : Vec 2 → Vec 2} {ω : Vec 2 → ℝ} {B : Vec 2 → Vec 2}

/-- Weak convergence of `∫ ω (B × ∇R_N)` (varying second slot). -/
theorem tendsto_cross_second (hRc : ∀ N i, Continuous fun x => spaceGrad (R N) x i)
    (hDR : ∀ i, MemL2On unitCube fun x => DR x i)
    (hR : ∀ g : Vec 2 → ℝ, MemL2On unitCube g → ∀ i : Fin 2,
      Tendsto (fun N => ∫ x in unitCube, spaceGrad (R N) x i * g x) atTop
        (𝓝 (∫ x in unitCube, DR x i * g x)))
    (hB0 : MemL2On unitCube fun x => ω x * B x 0) (hB1 : MemL2On unitCube fun x => ω x * B x 1) :
    Tendsto (fun N => ∫ x in unitCube, ω x * crossDot (B x) (spaceGrad (R N) x)) atTop
      (𝓝 (∫ x in unitCube, ω x * crossDot (B x) (DR x))) := by
  have key : ∀ (F : Vec 2 → Vec 2) (hF : ∀ i, MemL2On unitCube fun x => F x i),
      ∫ x in unitCube, ω x * crossDot (B x) (F x) =
        (∫ x in unitCube, F x 1 * (ω x * B x 0)) - ∫ x in unitCube, F x 0 * (ω x * B x 1) := by
    intro F hF
    rw [← integral_sub (integrable_mul_memL2 (hF 1) hB0) (integrable_mul_memL2 (hF 0) hB1)]
    exact setIntegral_congr_fun measurableSet_unitCube' fun x _ => by simp only [crossDot]; ring
  have hRL : ∀ N i, MemL2On unitCube fun x => spaceGrad (R N) x i := fun N i =>
    memL2_continuous (hRc N i)
  have hfun : (fun N => ∫ x in unitCube, ω x * crossDot (B x) (spaceGrad (R N) x)) =
      fun N => (∫ x in unitCube, spaceGrad (R N) x 1 * (ω x * B x 0))
        - ∫ x in unitCube, spaceGrad (R N) x 0 * (ω x * B x 1) :=
    funext fun N => key (fun x => spaceGrad (R N) x) (hRL N)
  rw [hfun, key DR hDR]
  exact (hR _ hB0 1).sub (hR _ hB1 0)

/-- Weak convergence of `∫ ω (∇R_N × B)` (varying first slot). -/
theorem tendsto_cross_first (hRc : ∀ N i, Continuous fun x => spaceGrad (R N) x i)
    (hDR : ∀ i, MemL2On unitCube fun x => DR x i)
    (hR : ∀ g : Vec 2 → ℝ, MemL2On unitCube g → ∀ i : Fin 2,
      Tendsto (fun N => ∫ x in unitCube, spaceGrad (R N) x i * g x) atTop
        (𝓝 (∫ x in unitCube, DR x i * g x)))
    (hB0 : MemL2On unitCube fun x => ω x * B x 0) (hB1 : MemL2On unitCube fun x => ω x * B x 1) :
    Tendsto (fun N => ∫ x in unitCube, ω x * crossDot (spaceGrad (R N) x) (B x)) atTop
      (𝓝 (∫ x in unitCube, ω x * crossDot (DR x) (B x))) := by
  have key : ∀ (F : Vec 2 → Vec 2) (hF : ∀ i, MemL2On unitCube fun x => F x i),
      ∫ x in unitCube, ω x * crossDot (F x) (B x) =
        (∫ x in unitCube, F x 0 * (ω x * B x 1)) - ∫ x in unitCube, F x 1 * (ω x * B x 0) := by
    intro F hF
    rw [← integral_sub (integrable_mul_memL2 (hF 0) hB1) (integrable_mul_memL2 (hF 1) hB0)]
    exact setIntegral_congr_fun measurableSet_unitCube' fun x _ => by simp only [crossDot]; ring
  have hRL : ∀ N i, MemL2On unitCube fun x => spaceGrad (R N) x i := fun N i =>
    memL2_continuous (hRc N i)
  have hfun : (fun N => ∫ x in unitCube, ω x * crossDot (spaceGrad (R N) x) (B x)) =
      fun N => (∫ x in unitCube, spaceGrad (R N) x 0 * (ω x * B x 1))
        - ∫ x in unitCube, spaceGrad (R N) x 1 * (ω x * B x 0) :=
    funext fun N => key (fun x => spaceGrad (R N) x) (hRL N)
  rw [hfun, key DR hDR]
  exact (hR _ hB1 0).sub (hR _ hB0 1)

end Slots

/-- **Skew identity** for `H¹(𝕋²)` functions: for `ψ ∈ C¹` periodic,
`∫ (∇ψ × Dv) w = ∫ ψ (Dv × Dw)`. -/
theorem skew_h1 {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (pψ : IsZ2Periodic ψ)
    {v w : Vec 2 → ℝ} {Dv Dw : Vec 2 → Vec 2} (hv : IsPeriodicH1With v Dv)
    (hw : IsPeriodicH1With w Dw) :
    ∫ x in unitCube, crossDot (spaceGrad ψ x) (Dv x) * w x =
      ∫ x in unitCube, ψ x * crossDot (Dv x) (Dw x) := by
  obtain ⟨P, hPs, hPp, hP⟩ := torus_exists_smooth_approx hv
  obtain ⟨Q, hQs, hQp, hQ⟩ := torus_exists_smooth_approx hw
  have hP1 : ∀ N, ContDiff ℝ 1 (P N) := fun N => contDiff_one_of_top (hPs N)
  have hQ1 : ∀ N, ContDiff ℝ 1 (Q N) := fun N => contDiff_one_of_top (hQs N)
  have hψg : ∀ i, Continuous fun x => spaceGrad ψ x i := continuous_spaceGrad_apply hψ
  have hwL : MemL2On unitCube w := hw.2.2.1
  have hDvL : ∀ i, MemL2On unitCube (fun x => Dv x i) := hv.2.2.2.1
  have hDwL : ∀ i, MemL2On unitCube (fun x => Dw x i) := hw.2.2.2.1
  have hPc : ∀ N i, Continuous fun x => spaceGrad (P N) x i := fun N i =>
    continuous_spaceGrad_apply (hP1 N) i
  have hQc : ∀ N i, Continuous fun x => spaceGrad (Q N) x i := fun N i =>
    continuous_spaceGrad_apply (hQ1 N) i
  -- step 1: `M → ∞`
  have step1 : ∀ N, ∫ x in unitCube, crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * w x =
      ∫ x in unitCube, ψ x * crossDot (spaceGrad (P N) x) (Dw x) := by
    intro N
    have hgc : Continuous fun x => crossDot (spaceGrad ψ x) (spaceGrad (P N) x) :=
      continuous_crossDot_grad hψ (hP1 N)
    have hl := (hQ _ (memL2_continuous hgc)).1
    have hl' : Tendsto (fun M => ∫ x in unitCube,
        crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * Q M x) atTop
        (𝓝 (∫ x in unitCube, crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * w x)) := by
      have : (fun M => ∫ x in unitCube,
          crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * Q M x) = fun M => ∫ x in unitCube,
          Q M x * crossDot (spaceGrad ψ x) (spaceGrad (P N) x) :=
        funext fun M => integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      rw [this]
      have h2 : (∫ x in unitCube, crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * w x) =
          ∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (spaceGrad (P N) x) :=
        integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
      rw [h2]
      exact hl
    have hr := tendsto_cross_second (R := Q) (DR := Dw) (ω := ψ)
      (B := fun x => spaceGrad (P N) x) hQc hDwL (fun g hg i => (hQ g hg).2 i)
      (memL2_continuous (hψ.continuous.mul (hPc N 0)))
      (memL2_continuous (hψ.continuous.mul (hPc N 1)))
    have hr' : Tendsto (fun M => ∫ x in unitCube,
        crossDot (spaceGrad ψ x) (spaceGrad (P N) x) * Q M x) atTop
        (𝓝 (∫ x in unitCube, ψ x * crossDot (spaceGrad (P N) x) (Dw x))) := by
      refine hr.congr fun M => ?_
      rw [← skew_smooth hψ (hPs N) (hQs M) pψ (hPp N) (hQp M)]
    exact tendsto_nhds_unique hl' hr'
  -- step 2: `N → ∞`
  have hl2 := tendsto_cross_second (R := P) (DR := Dv) (ω := w) (B := fun x => spaceGrad ψ x)
    hPc hDvL (fun g hg i => (hP g hg).2 i)
    (by simpa [mul_comm] using memL2_mul_continuous (hψg 0) hwL)
    (by simpa [mul_comm] using memL2_mul_continuous (hψg 1) hwL)
  have hr2 := tendsto_cross_first (R := P) (DR := Dv) (ω := ψ) (B := fun x => Dw x)
    hPc hDvL (fun g hg i => (hP g hg).2 i)
    (by simpa using memL2_mul_continuous hψ.continuous (hDwL 0))
    (by simpa using memL2_mul_continuous hψ.continuous (hDwL 1))
  have hl2' : Tendsto (fun N => ∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (spaceGrad (P N) x))
      atTop (𝓝 (∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (Dv x))) := hl2
  have e1 : ∀ N, ∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (spaceGrad (P N) x) =
      ∫ x in unitCube, ψ x * crossDot (spaceGrad (P N) x) (Dw x) := fun N => by
    rw [← step1 N]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hl3 : Tendsto (fun N => ∫ x in unitCube, ψ x * crossDot (spaceGrad (P N) x) (Dw x))
      atTop (𝓝 (∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (Dv x))) :=
    hl2'.congr e1
  have := tendsto_nhds_unique hl3 hr2
  calc ∫ x in unitCube, crossDot (spaceGrad ψ x) (Dv x) * w x
      = ∫ x in unitCube, w x * crossDot (spaceGrad ψ x) (Dv x) :=
        integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = _ := this
end

/-! # Elementary facts on streams and on `H¹(𝕋²)` differences -/

theorem spaceGrad_periodic {F : Vec 2 → ℝ} (hp : IsZ2Periodic F) : IsZ2Periodic (spaceGrad F) := by
  intro n x
  funext i
  simp [spaceGrad, fderiv_periodic hp n x]

theorem streamVel_periodic {φ : ℝ → Vec 2 → ℝ} (hφp : ∀ t, IsZ2Periodic (φ t)) (t : ℝ) :
    IsZ2Periodic (streamVel φ t) := by
  intro n x
  simp only [streamVel, spaceGrad_periodic (hφp t) n x]

theorem streamVel_apply (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x = ![-(spaceGrad (φ t) x 1), spaceGrad (φ t) x 0] := by
  funext i
  fin_cases i <;> simp [streamVel, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem continuous_streamVel_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) := by
  have hg : ∀ i : Fin 2, Continuous (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 i) := by
    intro i
    have := (contDiff_fderiv_apply_of_smooth hφ ((0 : ℝ), basisVec i)).continuous
    refine this.congr fun p => ?_
    exact (spaceGrad_slc_eq (ρ := fun q : ℝ × Vec 2 => φ q.1 q.2) hφ p.1 p.2 i).symm
  simp only [streamVel_apply]
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hg 1).neg
  · exact hg 0

theorem bounded_periodic_window {F : ℝ × Vec 2 → ℝ} (hF : Continuous F)
    (hp : ∀ t, IsZ2Periodic (fun x => F (t, x))) (a b : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, |F (t, x)| ≤ C := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun t ht x => ?_⟩
  have hx : (x - latticeShift (fun i => ⌊x i⌋)) ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    intro i _
    simp only [Pi.sub_apply, latticeShift]
    exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩
  have h1 := hC (t, x - latticeShift (fun i => ⌊x i⌋)) ⟨ht, hx⟩
  have h2 : F (t, x - latticeShift (fun i => ⌊x i⌋)) = F (t, x) := by
    have := hp t (fun i => ⌊x i⌋) (x - latticeShift (fun i => ⌊x i⌋))
    simpa using this.symm
  rw [h2] at h1
  simpa using h1

theorem bounded_streamVel_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hφp : ∀ t, IsZ2Periodic (φ t)) (a b : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ C := by
  have hc := continuous_streamVel_smooth hφ
  have hcomp : ∀ i : Fin 2, ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, |streamVel φ t x i| ≤ C := by
    intro i
    refine bounded_periodic_window (F := fun p => streamVel φ p.1 p.2 i)
      ((continuous_apply i).comp hc) (fun t n x => ?_) a b
    simp only [streamVel_periodic hφp t n x]
  obtain ⟨C0, h0⟩ := hcomp 0
  obtain ⟨C1, h1⟩ := hcomp 1
  refine ⟨max (max C0 C1) 0, fun t ht x => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => ?_
  fin_cases i
  · rw [Real.norm_eq_abs]
    exact (h0 t ht x).trans ((le_max_left C0 C1).trans (le_max_left _ _))
  · rw [Real.norm_eq_abs]
    exact (h1 t ht x).trans ((le_max_right C0 C1).trans (le_max_left _ _))

theorem integrable_periodic_mul_compact {G χ : Vec 2 → ℝ} (hper : IsZ2Periodic G)
    (hG : Integrable G (volume.restrict unitCube)) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) : Integrable (fun x => G x * χ x) := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have h1 : IntegrableOn (fun x => G x * χ x) (supBall R) :=
    (integrableOn_supBall_space hper hG R).mul_bdd hχ.aestronglyMeasurable (c := C)
      (Eventually.of_forall hC)
  refine h1.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have : χ x = 0 := by
    by_contra hne
    exact hx (by simpa [supBall] using hR x (subset_tsupport _ hne))
  simp [this]

theorem isPeriodicH1With_sub {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (hv : IsPeriodicH1With v Dv) :
    IsPeriodicH1With (fun x => u x - v x) (fun x => Du x - Dv x) := by
  obtain ⟨pu, pDu, mu, gu, wu⟩ := hu
  obtain ⟨pv, pDv, mv, gv, wv⟩ := hv
  refine ⟨fun n x => by simp [pu n x, pv n x], fun n x => by simp [pDu n x, pDv n x],
    mu.sub mv, fun i => (gu i).sub (gv i), ?_⟩
  intro i φ hφs hφc _
  have hφ1 : ContDiff ℝ 1 φ := contDiff_one_of_top hφs
  have dc : Continuous fun x => fderiv ℝ φ x (basisVec i) := continuous_fderiv_apply hφ1 _
  have dcc : HasCompactSupport fun x => fderiv ℝ φ x (basisVec i) :=
    hasCompactSupport_fderiv_apply hφc _
  have a1 := integrable_periodic_mul_compact pu (mu.integrable (by norm_num)) dc dcc
  have a2 := integrable_periodic_mul_compact pv (mv.integrable (by norm_num)) dc dcc
  have b1 := integrable_periodic_mul_compact (G := fun x => Du x i)
    (fun n x => by simp [pDu n x]) ((gu i).integrable (by norm_num)) hφs.continuous hφc
  have b2 := integrable_periodic_mul_compact (G := fun x => Dv x i)
    (fun n x => by simp [pDv n x]) ((gv i).integrable (by norm_num)) hφs.continuous hφc
  have e1 := wu i φ hφs hφc (Set.subset_univ _)
  have e2 := wv i φ hφs hφc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at e1 e2 ⊢
  simp only [sub_mul, Pi.sub_apply]
  rw [integral_sub a1 a2, integral_sub b1 b2, e1, e2]
  ring

end AVRegularity.Applications
end
