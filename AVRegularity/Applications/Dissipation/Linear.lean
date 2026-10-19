-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
import AVenhance.Infra.Parabolic.WeakUniqueness.ModePath
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy

/-! # Linearity, constants, data classes and mass of weak solutions on a window

The explicit-gradient weak class `IsWeakSolutionOnWith` is closed under sums and scalar
multiples; every constant is a solution with zero gradient, for every drift; the datum enters
only through its class on the cell; and for a divergence-free window drift the cell mean of
every slice is the mean of the datum. These are the facts on linearity, constants and mass used
in the proof of Theorem B of the paper. -/

public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications.Dissipation

/-- The unit cell has finite measure. -/
local instance dissipationLinearFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 unitCube_measure_ne_top

/-! ### Integrability on the window and on the cell -/

/-- A continuous function is bounded on a bounded window times the cell. -/
theorem exists_bound_window_cell (t₁ t₂ : ℝ) {F : ℝ × Vec 2 → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ p ∈ Set.Ioo t₁ t₂ ×ˢ unitCube, ‖F p‖ ≤ C := by
  have hK : IsCompact (Set.Icc t₁ t₂ ×ˢ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun p hp => hC p ⟨Set.Ioo_subset_Icc_self hp.1,
    fun i hi => ⟨(hp.2 i hi).1.le, (hp.2 i hi).2.le⟩⟩⟩

/-- An integrable function on the window times the cell, times a continuous function, is
integrable. -/
theorem integrable_mul_continuous_window {t₁ t₂ : ℝ} {F G : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))) (hG : Continuous G) :
    Integrable (fun p => F p * G p) (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
  obtain ⟨C, hC⟩ := exists_bound_window_cell t₁ t₂ hG
  refine hF.mul_bdd hG.aestronglyMeasurable (c := C) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_unitCube')] with p hp
  exact hC p hp

/-- A cell-`L²` function times a continuous function is integrable on the cell. -/
theorem integrable_mul_continuous_cell {F G : Vec 2 → ℝ} (hF : MemL2On unitCube F)
    (hG : Continuous G) : Integrable (fun x => F x * G x) (volume.restrict unitCube) := by
  obtain ⟨C, hC⟩ := exists_bound_cube hG
  refine (hF.integrable one_le_two).mul_bdd hG.aestronglyMeasurable (c := C) ?_
  filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

/-- The integrand of the window weak form is integrable for every window test. -/
theorem integrable_weakIntegrand_window {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsWindowTestFunction t₂ φ) :
    Integrable (fun p : ℝ × Vec 2 =>
        -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
  obtain ⟨-, -, hL2, hDL2, -, hint, -, -⟩ := h
  obtain ⟨hsm, -, -⟩ := hφ
  have hT : Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) := by
    have e : (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) =
        fun p => fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p (1, 0) := by
      funext p
      exact deriv_slc_eq hsm p.1 p.2
    rw [e]
    exact (contDiff_fderiv_apply_of_smooth hsm _).continuous
  have hG : ∀ i : Fin 2, Continuous (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 i) := by
    intro i
    have e : (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 i) =
        fun p => fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p (0, basisVec i) := by
      funext p
      exact spaceGrad_slc_eq hsm p.1 p.2 i
    rw [e]
    exact (contDiff_fderiv_apply_of_smooth hsm _).continuous
  have i0 := integrable_mul_continuous_window (memLp_two_integrable_window hL2) hT
  have i1 := integrable_mul_continuous_window hint hsm.continuous
  have i2 := integrable_mul_continuous_window (memLp_two_integrable_window (hDL2 0)) (hG 0)
  have i3 := integrable_mul_continuous_window (memLp_two_integrable_window (hDL2 1)) (hG 1)
  refine ((i0.neg.add i1).add ((i2.add i3).const_mul κ)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, Pi.neg_apply, vecDot, Fin.sum_univ_two]
  ring

/-- `‖u + v‖² ≤ 2‖u‖² + 2‖v‖²` on the cell. -/
theorem l2NormSq_add_le_two_mul {u v : Vec 2 → ℝ} (hu : MemL2On unitCube u)
    (hv : MemL2On unitCube v) : l2NormSq (u + v) ≤ 2 * l2NormSq u + 2 * l2NormSq v := by
  have hu2 := hu.integrable_sq
  have hv2 := hv.integrable_sq
  have huv2 := (hu.add hv).integrable_sq
  unfold l2NormSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hu2.const_mul 2) (hv2.const_mul 2)]
  refine integral_mono huv2 ((hu2.const_mul 2).add (hv2.const_mul 2)) fun x => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u x - v x)]

/-! ### Periodic `H¹` witnesses: constants, sums, scalar multiples -/

/-- A constant is periodic `H¹` with zero gradient. -/
theorem isPeriodicH1With_const_dissipation (c : ℝ) :
    IsPeriodicH1With (fun _ => c) (fun _ => (0 : Vec 2)) := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, memLp_const c, fun i => ?_, fun i φ hφ hφc _ => ?_⟩
  · exact memLp_const (0 : ℝ)
  · rw [setIntegral_univ, setIntegral_univ, integral_const_mul,
      integral_fderiv_eq_zero_of_hasCompactSupport hφ hφc]
    simp

/-- Scalar multiples of periodic `H¹` witnesses. -/
theorem isPeriodicH1With_smul_dissipation {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (c : ℝ)
    (h : IsPeriodicH1With u Du) : IsPeriodicH1With (c • u) (c • Du) := by
  obtain ⟨hpu, hpD, hu, hDu, hw⟩ := h
  refine ⟨fun k x => by simp [hpu k x], fun k x => by simp [hpD k x], hu.const_smul c,
    fun i => (hDu i).const_smul c, fun i φ hφ hφc hφs => ?_⟩
  have e1 : ∫ x in Set.univ, (c • u) x * fderiv ℝ φ x (basisVec i) =
      c * ∫ x in Set.univ, u x * fderiv ℝ φ x (basisVec i) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : ∫ x in Set.univ, (c • Du) x i * φ x = c * ∫ x in Set.univ, Du x i * φ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e2, hw i φ hφ hφc hφs]
  ring

/-- Sums of periodic `H¹` witnesses. -/
theorem isPeriodicH1With_add_dissipation {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (hv : IsPeriodicH1With v Dv) :
    IsPeriodicH1With (u + v) (Du + Dv) := by
  have h0 := isPeriodicH1With_const_dissipation 0
  have h := Infra.Parabolic.WeakUniqueness.isPeriodicH1With_sub hu
    (Infra.Parabolic.WeakUniqueness.isPeriodicH1With_sub h0 hv)
  convert h using 1
  · funext x
    simp
  · funext x
    simp

/-! ### The weak class -/

/-- Weak solutions add: `θ + η` solves with datum `f + g` and gradient `Dθ + Dη`. -/
theorem isWeakSolutionOnWith_add {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f g : Vec 2 → ℝ}
    {θ η : ℝ → Vec 2 → ℝ} {Dθ Dη : ℝ → Vec 2 → Vec 2}
    (hf : MemL2On unitCube f) (hg : MemL2On unitCube g)
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) (hη : IsWeakSolutionOnWith b κ t₁ t₂ g η Dη) :
    IsWeakSolutionOnWith b κ t₁ t₂ (f + g) (θ + η) (Dθ + Dη) := by
  have hθ' := hθ
  have hη' := hη
  obtain ⟨hsθ, ⟨Cθ, hCθ⟩, hLθ, hDLθ, hHθ, hintθ, hcθ, hwθ⟩ := hθ
  obtain ⟨hsη, ⟨Cη, hCη⟩, hLη, hDLη, hHη, hintη, hcη, hwη⟩ := hη
  refine ⟨fun t ht => ⟨fun k x => ?_, (hsθ t ht).2.add (hsη t ht).2⟩,
    ⟨2 * Cθ + 2 * Cη, fun t ht => ?_⟩, hLθ.add hLη, fun i => (hDLθ i).add (hDLη i), ?_, ?_,
    fun ψ hψ hψp => ?_, fun φ hφ => ?_⟩
  · simp [(hsθ t ht).1 k x, (hsη t ht).1 k x]
  · have h2 := l2NormSq_add_le_two_mul (hsθ t ht).2 (hsη t ht).2
    have := hCθ t ht
    have := hCη t ht
    change l2NormSq (θ t + η t) ≤ _
    linarith
  · filter_upwards [hHθ, hHη] with t h1 h2
    exact isPeriodicH1With_add_dissipation h1 h2
  · refine (hintθ.add hintη).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, vecDot, Fin.sum_univ_two]
    ring
  · refine ((hcθ ψ hψ hψp).add (hcη ψ hψ hψp)).congr fun t ht => ?_
    have i1 := integrable_mul_continuous_cell (hsθ t ht).2 hψ.continuous
    have i2 := integrable_mul_continuous_cell (hsη t ht).2 hψ.continuous
    simp only [Pi.add_apply, add_mul]
    exact integral_add i1 i2
  · have i1 := integrable_weakIntegrand_window hθ' hφ
    have i2 := integrable_weakIntegrand_window hη' hφ
    have hφ0 : Continuous (φ t₁) := hφ.1.continuous.comp (Continuous.prodMk_right t₁)
    have j1 := integrable_mul_continuous_cell hf hφ0
    have j2 := integrable_mul_continuous_cell hg hφ0
    have e : ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-((θ + η) p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) ((Dθ + Dη) p.1 p.2) * φ p.1 p.2
          + κ * vecDot ((Dθ + Dη) p.1 p.2) (spaceGrad (φ p.1) p.2)) =
        ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
          ((-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
          + (-(η p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dη p.1 p.2) * φ p.1 p.2
            + κ * vecDot (Dη p.1 p.2) (spaceGrad (φ p.1) p.2))) := by
      congr 1
      funext p
      simp only [Pi.add_apply, vecDot, Fin.sum_univ_two]
      ring
    rw [e, integral_add i1 i2, hwθ φ hφ, hwη φ hφ, ← integral_add j1 j2]
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring

/-- Weak solutions scale: `c • θ` solves with datum `c • f` and gradient `c • Dθ`. -/
theorem isWeakSolutionOnWith_smul {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (c : ℝ)
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsWeakSolutionOnWith b κ t₁ t₂ (c • f) (c • θ) (c • Dθ) := by
  obtain ⟨hs, ⟨C, hC⟩, hL, hDL, hH, hint, hc, hw⟩ := hθ
  refine ⟨fun t ht => ⟨fun k x => ?_, (hs t ht).2.const_smul c⟩,
    ⟨c ^ 2 * C, fun t ht => ?_⟩, hL.const_smul c, fun i => (hDL i).const_smul c, ?_, ?_,
    fun ψ hψ hψp => ?_, fun φ hφ => ?_⟩
  · simp [(hs t ht).1 k x]
  · have e : l2NormSq ((c • θ) t) = c ^ 2 * l2NormSq (θ t) := by
      unfold l2NormSq
      rw [← integral_const_mul]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hC t ht) (sq_nonneg c)
  · filter_upwards [hH] with t h1
    exact isPeriodicH1With_smul_dissipation c h1
  · refine (hint.const_mul c).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, vecDot, Fin.sum_univ_two]
    ring
  · refine ((hc ψ hψ hψp).const_smul c).congr fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · have e : ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-((c • θ) p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) ((c • Dθ) p.1 p.2) * φ p.1 p.2
          + κ * vecDot ((c • Dθ) p.1 p.2) (spaceGrad (φ p.1) p.2)) =
        c * ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
          (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) := by
      rw [← integral_const_mul]
      congr 1
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, vecDot, Fin.sum_univ_two]
      ring
    rw [e, hw φ hφ, ← integral_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- `∫_{t₁}^{t₂} ∫_{𝕋²} -∂ₜφ = ∫_{𝕋²} φ(t₁)` for a window test. -/
private theorem integral_neg_timeDeriv_window {t₁ t₂ : ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsWindowTestFunction t₂ φ) (c : ℝ) :
    ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, -(c * deriv (fun s => φ s p.2) p.1) =
      ∫ x in unitCube, c * φ t₁ x := by
  obtain ⟨hsm, -, hvan⟩ := hφ
  rcases lt_or_ge t₁ t₂ with h12 | h21
  · have hT : Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) := by
      have e : (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) =
          fun p => fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p (1, 0) := by
        funext p
        exact deriv_slc_eq hsm p.1 p.2
      rw [e]
      exact (contDiff_fderiv_apply_of_smooth hsm _).continuous
    have hF : Continuous (fun p : ℝ × Vec 2 => -(c * deriv (fun s => φ s p.2) p.1)) :=
      (continuous_const.mul hT).neg
    obtain ⟨C, hC⟩ := exists_bound_window_cell t₁ t₂ hF
    have hint : Integrable (fun p : ℝ × Vec 2 => -(c * deriv (fun s => φ s p.2) p.1))
        ((volume.restrict (Set.Ioo t₁ t₂)).prod (volume.restrict unitCube)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      refine Integrable.of_bound hF.aestronglyMeasurable C ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_unitCube')] with p hp
      exact hC p hp
    have hdiff : ∀ x, Differentiable ℝ (fun s => φ s x) := fun x =>
      (hsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    have hderivc : ∀ x, Continuous (fun s => deriv (fun r => φ r x) s) := fun x =>
      hT.comp (Continuous.prodMk_left x)
    have hinner : ∀ x, ∫ s in Set.Ioo t₁ t₂, -(c * deriv (fun r => φ r x) s) = c * φ t₁ x := by
      intro x
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h12.le,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_deriv_eq_sub (fun s _ => hdiff x s)
          ((hderivc x).intervalIntegrable _ _), hvan t₂ le_rfl x]
      ring
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  · have hempty : Set.Ioo t₁ t₂ ×ˢ unitCube = (∅ : Set (ℝ × Vec 2)) := by
      rw [Set.Ioo_eq_empty (not_lt.2 h21), Set.empty_prod]
    rw [hempty, Measure.restrict_empty, integral_zero_measure]
    have hz : (fun x => c * φ t₁ x) = fun _ => (0 : ℝ) := by
      funext x
      rw [hvan t₁ h21 x, mul_zero]
    rw [hz, integral_zero]

/-- Every constant is a weak solution with zero gradient, for every drift and diffusivity. -/
theorem isWeakSolutionOnWith_const (b : ℝ → Vec 2 → Vec 2) (κ t₁ t₂ c : ℝ) :
    IsWeakSolutionOnWith b κ t₁ t₂ (fun _ => c) (fun _ _ => c) (fun _ _ => 0) := by
  refine ⟨fun t _ => ⟨fun _ _ => rfl, memLp_const c⟩, ⟨l2NormSq (fun _ => c), fun t _ => le_rfl⟩,
    memLp_const c, fun i => memLp_const 0,
    Filter.Eventually.of_forall fun t => isPeriodicH1With_const_dissipation c, ?_,
    fun ψ _ _ => continuousOn_const, fun φ hφ => ?_⟩
  · refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun p => ?_)
    simp [vecDot]
  · rw [← integral_neg_timeDeriv_window hφ c]
    congr 1
    funext p
    simp [vecDot]

/-- The datum enters only through its class on the cell. -/
theorem isWeakSolutionOnWith_congr_datum {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f g : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hfg : f =ᵐ[volume.restrict unitCube] g) (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsWeakSolutionOnWith b κ t₁ t₂ g θ Dθ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hw⟩ := hθ
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun φ hφ => ?_⟩
  rw [hw φ hφ]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [hx]

/-! ### Conservation of mass -/

/-- For a bounded measurable periodic divergence-free field `B`, `∫_{𝕋²} B · Du = 0` for every
periodic `H¹` function `u` (polarization of `divFree_static_h1_cancellation` with `u + 1`). -/
theorem integral_vecDot_grad_eq_zero_of_divFree {B : Vec 2 → Vec 2}
    (hBm : AEStronglyMeasurable B volume) (hBb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖B x‖ ≤ C)
    (hBp : IsZ2Periodic B)
    (hBd : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (B x) (spaceGrad φ x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du) :
    ∫ x in unitCube, vecDot (B x) (Du x) = 0 := by
  have hsmooth : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ∫ x in Infra.Torus.unitCell 2, vecDot (B x) (spaceGrad ψ x) = 0 := fun ψ hψ hψp =>
    Infra.Parabolic.WeakUniqueness.isDivFree_integral_periodic_smooth_test hBm hBb hBp hBd hψ hψp
  have hu1 : IsPeriodicH1With (u + fun _ => 1) (Du + fun _ => 0) :=
    isPeriodicH1With_add_dissipation hu (isPeriodicH1With_const_dissipation 1)
  have z1 := Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy.divFree_static_h1_cancellation
    hBm hBb hsmooth hu
  have z2 := Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy.divFree_static_h1_cancellation
    hBm hBb hsmooth hu1
  rw [Infra.Torus.integral_unitCell_eq_unitCube] at z1 z2
  obtain ⟨C, -, hC⟩ := hBb
  have hBi : ∀ i : Fin 2, AEStronglyMeasurable (fun x => B x i) (volume.restrict unitCube) :=
    fun i => ((continuous_apply i).comp_aestronglyMeasurable hBm).restrict
  have hBib : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict unitCube), ‖B x i‖ ≤ C := fun i =>
    Filter.Eventually.of_forall fun x => (norm_le_pi_norm (B x) i).trans (hC x)
  have hDu : ∀ i : Fin 2, MemL2On unitCube (fun x => Du x i) := hu.2.2.2.1
  have Ia : Integrable (fun x => vecDot (B x) (Du x) * u x) (volume.restrict unitCube) := by
    have h0 := (Infra.Parabolic.WeakUniqueness.weak_product_integrable_cell (hDu 0)
      hu.2.2.1).bdd_mul (hBi 0) (hBib 0)
    have h1 := (Infra.Parabolic.WeakUniqueness.weak_product_integrable_cell (hDu 1)
      hu.2.2.1).bdd_mul (hBi 1) (hBib 1)
    refine (h0.add h1).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, vecDot, Fin.sum_univ_two]
    ring
  have Ib : Integrable (fun x => vecDot (B x) (Du x)) (volume.restrict unitCube) := by
    have h0 := ((hDu 0).integrable one_le_two).bdd_mul (hBi 0) (hBib 0)
    have h1 := ((hDu 1).integrable one_le_two).bdd_mul (hBi 1) (hBib 1)
    refine (h0.add h1).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, vecDot, Fin.sum_univ_two]
  have e : ∫ x in unitCube,
      vecDot (B x) ((Du + (fun _ => 0 : Vec 2 → Vec 2)) x) * (u + (fun _ => 1 : Vec 2 → ℝ)) x =
      (∫ x in unitCube, vecDot (B x) (Du x) * u x) + ∫ x in unitCube, vecDot (B x) (Du x) := by
    rw [← integral_add Ia Ib]
    congr 1
    funext x
    simp only [Pi.add_apply, add_zero]
    ring
  rw [e, z1, zero_add] at z2
  exact z2

/-- **Conservation of mass.** For a divergence-free window drift, every slice of a weak solution
has the cell mean of its datum. -/
theorem integral_eq_of_isWeakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    (h12 : t₁ < t₂) (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    ∀ t ∈ Set.Icc t₁ t₂, ∫ x in unitCube, θ t x = ∫ x in unitCube, f x := by
  intro t ht
  obtain ⟨T, hT, rfl⟩ : ∃ T, 0 < T ∧ t₂ = t₁ + T := ⟨t₂ - t₁, by linarith, by ring⟩
  obtain ⟨hbm, ⟨C, hC⟩, hbp, hdiv⟩ := hb
  have hu := isWeakSolutionOnWith_to_isWeakSolutionGrad hT hθ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t₁ ⟨le_rfl, by linarith⟩ 0)
  have hforce : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      IsPeriodicH1With (Wellposed.stateToUnit t₁ T θ r) (Wellposed.gradientToUnit t₁ T Dθ r) →
      Infra.Parabolic.WeakUniqueness.weakModeForcing (Wellposed.rescaledDrift b t₁ T) (T * κ)
        (Wellposed.gradientToUnit t₁ T Dθ) (fun _ => (1 : ℝ)) r = 0 := by
    intro r hr hH
    have hr' : Wellposed.timeForward t₁ T r ∈ Set.Icc t₁ (t₁ + T) :=
      Wellposed.timeForward_mem_Icc hT (Set.Ioo_subset_Icc_self hr)
    have hm : Measurable (fun x => b (Wellposed.timeForward t₁ T r) x) :=
      hbm.comp measurable_prodMk_left
    have hz := integral_vecDot_grad_eq_zero_of_divFree
      (B := Wellposed.rescaledDrift b t₁ T r) (hm.const_smul T).aestronglyMeasurable
      ⟨T * C, mul_nonneg hT.le hC0, fun x => by
        change ‖T • b (Wellposed.timeForward t₁ T r) x‖ ≤ T * C
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
        exact mul_le_mul_of_nonneg_left (hC _ hr' x) hT.le⟩
      (fun k x => by
        change T • b (Wellposed.timeForward t₁ T r) (x + latticeShift k) =
          T • b (Wellposed.timeForward t₁ T r) x
        rw [hbp _ hr' k x])
      (fun φ hφ hφc => by
        change ∫ x, vecDot (T • b (Wellposed.timeForward t₁ T r) x) (spaceGrad φ x) = 0
        simp_rw [Homogenization.vecDot_smul_left]
        rw [integral_const_mul, hdiv _ hr' φ hφ hφc, mul_zero]) hH
    have hgrad1 : ∀ x, spaceGrad (fun _ : Vec 2 => (1 : ℝ)) x = 0 := by
      intro x
      funext i
      simp [spaceGrad]
    unfold Infra.Parabolic.WeakUniqueness.weakModeForcing
    simp only [hgrad1, mul_one]
    simpa [vecDot] using hz
  have hH1 := (ae_restrict_iff' measurableSet_Ioo).1 hu.2.2.2.2.1
  have hs : (t - t₁) / T ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [ht.1]) hT.le, (div_le_one hT).2 (by linarith [ht.2])⟩
  have hzero : ∫ r in (0 : ℝ)..((t - t₁) / T),
      Infra.Parabolic.WeakUniqueness.weakModeForcing (Wellposed.rescaledDrift b t₁ T) (T * κ)
        (Wellposed.gradientToUnit t₁ T Dθ) (fun _ => (1 : ℝ)) r = 0 := by
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 1 := by
      simp [ae_iff, measure_singleton]
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    filter_upwards [hH1, hne] with r hr hr1 hrI
    rw [Set.uIoc_of_le hs.1] at hrI
    exact hforce r ⟨hrI.1, lt_of_le_of_ne (hrI.2.trans hs.2) hr1⟩
      (hr ⟨hrI.1, lt_of_le_of_ne (hrI.2.trans hs.2) hr1⟩)
  have hpath := Infra.Parabolic.WeakUniqueness.weak_solution_mode_integral_path hu hf
    (ψ := fun _ => (1 : ℝ)) contDiff_const (fun _ _ => rfl) _ hs
  rw [hzero, sub_zero] at hpath
  have htime : Wellposed.timeForward t₁ T ((t - t₁) / T) = t := by
    unfold Wellposed.timeForward
    field_simp
    ring
  simpa [Infra.Parabolic.WeakUniqueness.weakModePairing, Wellposed.stateToUnit, htime]
    using hpath


end AVRegularity.Applications.Dissipation

end
