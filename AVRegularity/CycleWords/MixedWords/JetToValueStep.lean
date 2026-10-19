-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer

section
section
/-! The three regularity ingredients, with one common window and weak equation. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-- A window of the reduced scalar multiplier equation with the exact premises. -/
structure TransverseRegWindow (ρ Cw : ℝ) (J : ℕ → ℝ) where
  a : ℝ
  b : ℝ
  η : ℝ
  hCw : 0 ≤ Cw
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  hG : IsCellMetric (fun t _ => G t)
  v : ℝ → Vec 2 → Vec 2
  hv : IsCellDrift v
  hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw
  ξ : Fin 2 → ℂ
  hab : a ≤ b
  hη0 : 0 ≤ η
  hη1 : η ≤ 1
  hreal : ∀ i, (ξ i).im = 0
  hfreq : fibreNorm ξ ≤ ρ
  hsmooth : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)
  hjets : ∀ (l : ℕ) t, t ∈ Icc a b → ∀ x,
    ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l
  u : ℝ → ComplexCellL2
  slice : ℝ → TorusHk 1 ℂ
  curve : CellWeakHilbertCurve a b u slice
    (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (slice t))

/-- Unit-window propagation with constants fixed before the metric, drift, frequency and solution. -/
def TransverseRegGrowthStatement : Prop :=
  ∀ (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ), 0 ≤ ρ → 0 ≤ Cw → (∀ l, 0 ≤ J l) →
  ∃ C : ℝ, 0 < C ∧ ∀ W : TransverseRegWindow ρ Cw J,
    ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = W.u W.a →
    ∀ t ∈ Icc W.a W.b, t ≤ W.a + 1 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = W.u t ∧ ‖w‖ ≤ C * ‖w₀‖

/-- Smoothing on the second unit interval from the L2 entrance alone. -/
def TransverseRegSmoothingStatement : Prop :=
  ∀ (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ), 0 ≤ ρ → 0 ≤ Cw → (∀ l, 0 ≤ J l) →
  ∃ C : ℝ, 0 < C ∧ ∀ W : TransverseRegWindow ρ Cw J,
    ∀ t ∈ Icc W.a W.b, W.a + 1 ≤ t → t ≤ W.a + 2 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = W.u t ∧ ‖w‖ ≤ C * ‖W.u W.a‖

/-- The solution from one differs from one by a quantity linear in the frequency. -/
def TransverseRegConstantStatement : Prop :=
  ∀ (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ), 0 ≤ ρ → 0 ≤ Cw → (∀ l, 0 ≤ J l) →
  ∃ C : ℝ, 0 < C ∧ ∀ W : TransverseRegWindow ρ Cw J,
    W.u W.a = cellConstantCLM 1 → ∀ t ∈ Icc W.a W.b, t ≤ W.a + 2 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = W.u t - cellConstantCLM 1 ∧ ‖w‖ ≤ C * fibreNorm W.ξ

/-- The exact fixed statement assembles from the three regularity clauses. -/
theorem transverseRegularity_of_ingredients
    (hGrowth : TransverseRegGrowthStatement) (hSmooth : TransverseRegSmoothingStatement)
    (hConstant : TransverseRegConstantStatement) : TransverseRegularityStatement := by
  intro j ρ Cw J hρ hCw hJ
  obtain ⟨CG, hCG, hG⟩ := hGrowth j ρ Cw J hρ hCw hJ
  obtain ⟨CS, hCS, hS⟩ := hSmooth j ρ Cw J hρ hCw hJ
  obtain ⟨CC, hCC, hC⟩ := hConstant j ρ Cw J hρ hCw hJ
  refine ⟨CG + CS + CC, by positivity, ?_⟩
  intro a b η hCw' G hmetric v hv hw ξ hab hη0 hη1 hreal hfreq hsmooth hjets u slice hu
  let W : TransverseRegWindow ρ Cw J :=
    ⟨a, b, η, hCw', G, hmetric, v, hv, hw, ξ, hab, hη0, hη1, hreal, hfreq, hsmooth, hjets, u, slice, hu⟩
  refine ⟨?_, ?_, ?_⟩
  · intro w₀ hi t ht ht1
    obtain ⟨w, hwv, hwb⟩ := hG W w₀ hi t ht ht1
    exact ⟨w, hwv, hwb.trans (mul_le_mul_of_nonneg_right (by linarith only [hCS, hCC]) (norm_nonneg _))⟩
  · intro t ht ht1 ht2
    obtain ⟨w, hwv, hwb⟩ := hS W t ht ht1 ht2
    exact ⟨w, hwv, hwb.trans (mul_le_mul_of_nonneg_right (by linarith only [hCG, hCC]) (norm_nonneg _))⟩
  · intro hi t ht ht2
    obtain ⟨w, hwv, hwb⟩ := hC W hi t ht ht2
    exact ⟨w, hwv, hwb.trans (mul_le_mul_of_nonneg_right (by linarith only [hCG, hCS]) (fibreNorm_nonneg _))⟩

end AVRegularity.CycleWords.Assembly
end
end

section
/-! The constituent bounds split into periodic pairing and strong-source calculus. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-- One constituent and its row/column perturbations, with literal classical budgets. -/
structure TransverseBlockFrame (d j : ℕ) (R : ℝ) where
  hd : 2 ≤ d
  θ : Vec 2
  ε : ℝ
  M : ℝ
  b : ℝ
  hε : 0 ≤ ε
  hR : ε ≤ R
  hθ : Real.sqrt (vecDot θ θ) ≤ ε
  hM : 0 ≤ M
  a : DerivativeWord2 (d - 1) → Vec 2 → Vec 2
  ha : ∀ α, ContDiff ℝ (j + d) (a α) ∧ AVenhance.IsZ2Periodic (a α)
  hb : ∀ α (i : ℕ), i ≤ j + d → ∀ z, ‖iteratedFDeriv ℝ i (a α) z‖ ≤ b
  ℓ : Vec 2 → ℂ
  r : Vec 2 → ℂ
  hℓ : ContDiff ℝ (j + d) ℓ
  hpℓ : AVenhance.IsZ2Periodic ℓ
  hr : ContDiff ℝ (j + d) r
  hpr : AVenhance.IsZ2Periodic r
  hℓnorm : cellSobolevNorm (j + d) (fun z => ℓ z - 1) ≤ ENNReal.ofReal (M * ε)
  hrnorm : cellSobolevNorm (j + d) r ≤ ENNReal.ofReal (M * ε)

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # Periodization against quasi-periodic tests

For an integrable plane function `g` and a bounded measurable periodic `φ`,
`∫ e^{-iθ·y} g(y) φ(y) dy = ∫_cell (planeBlochC θ g)(z) φ(z) dz`
(`integral_phase_mul_eq_cell_planeBlochC`): tile the plane by the integer translates of the cell
(`integral_tiling_translate`), interchange the lattice sum with the cell integral
(`integral_tsum`), use the periodicity of `φ`. With `φ = 1` the Fourier transform of `g` at `θ` is
the cell integral of its Bloch periodic part (`integral_phase_eq_cell_planeBlochC`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

/-- The phase `e^{-iθ·y}` has modulus one. -/
theorem norm_planePhase (θ y : Vec 2) : ‖Complex.exp (-(Complex.I * (vecDot θ y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem planePhase_continuous (θ : Vec 2) :
    Continuous fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) := by
  have : Continuous fun y : Vec 2 => vecDot θ y := by unfold vecDot; fun_prop
  fun_prop

/-- **Periodization.** -/
theorem integral_phase_mul_eq_cell_planeBlochC (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g)
    {φ : Vec 2 → ℂ} (hφm : AEStronglyMeasurable φ volume) {B : ℝ} (hφb : ∀ z, ‖φ z‖ ≤ B)
    (hφp : AVenhance.IsZ2Periodic φ) :
    (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * φ y) =
      ∫ z in AVenhance.unitCube, planeBlochC θ g z * φ z := by
  set F : Vec 2 → ℂ := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * φ y
    with hFdef
  have hgC : Integrable (fun y => (g y : ℂ)) := hg.ofReal
  have hFm : AEStronglyMeasurable F volume :=
    ((planePhase_continuous θ).aestronglyMeasurable.mul hgC.aestronglyMeasurable).mul hφm
  have hFi : Integrable F := by
    refine Integrable.mono' (hg.norm.mul_const B) hFm (Filter.Eventually.of_forall fun y => ?_)
    rw [hFdef]
    simp only [norm_mul, norm_planePhase, one_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hφb y) (norm_nonneg _)
  rw [CycleJointProofs.integral_tiling_translate F hFi,
    setIntegral_congr_set Applications.cellI_ae_eq_unitCube.symm]
  have hpt : ∀ z, planeBlochC θ g z * φ z =
      ∑' k : Fin 2 → ℤ, F (z + AVenhance.latticeShift k) := by
    intro z
    unfold planeBlochC
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [hFdef]
    simp only [hφp k z]
    rfl
  simp only [hpt]
  have hmk : ∀ k : Fin 2 → ℤ, AEStronglyMeasurable (fun z => F (z + AVenhance.latticeShift k))
      (volume.restrict Applications.cellI) :=
    fun k => (hFm.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (AVenhance.latticeShift k)).quasiMeasurePreserving).restrict
  have hsum : ∑' k : Fin 2 → ℤ, ∫⁻ z in Applications.cellI,
      ‖F (z + AVenhance.latticeShift k)‖ₑ ≠ ⊤ := by
    have hmeas : Measurable fun y => ‖hFm.mk F y‖ₑ := hFm.stronglyMeasurable_mk.measurable.enorm
    have hae : ∀ k : Fin 2 → ℤ, ∫⁻ z in Applications.cellI, ‖F (z + AVenhance.latticeShift k)‖ₑ =
        ∫⁻ z in Applications.cellI, ‖hFm.mk F (z + AVenhance.latticeShift k)‖ₑ := by
      intro k
      refine lintegral_congr_ae ?_
      have := (measurePreserving_add_right volume (AVenhance.latticeShift k)).quasiMeasurePreserving
        |>.ae_eq_comp hFm.ae_eq_mk
      filter_upwards [ae_restrict_of_ae this] with z hz
      simp only [Function.comp_apply] at hz
      rw [hz]
    rw [tsum_congr hae, ← CycleJointProofs.lintegral_tiling_translate _ hmeas]
    have hmk' : ∫⁻ y, ‖hFm.mk F y‖ₑ = ∫⁻ y, ‖F y‖ₑ :=
      lintegral_congr_ae (hFm.ae_eq_mk.mono fun y hy => by simp [hy])
    rw [hmk']
    exact hFi.2.ne
  exact (integral_tsum hmk hsum).symm

/-- The Fourier transform at `θ` is the cell integral of the Bloch periodic part. -/
theorem integral_phase_eq_cell_planeBlochC (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ)) =
      ∫ z in AVenhance.unitCube, planeBlochC θ g z := by
  have h := integral_phase_mul_eq_cell_planeBlochC θ hg (φ := fun _ => (1 : ℂ))
    aestronglyMeasurable_const (B := 1) (fun _ => by simp) (fun _ _ => rfl)
  simpa using h

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Jet-to-value transfer: one letter

For the phase `e(y) = e^{-iθ·y}`, the moment weight `m = y^β` and a smooth periodic test `φ`,
integration by parts on the plane moves one derivative of a field `g` onto the test and the weight:

`∫ e m (∂_k g) φ = -∫ e m g (∂_k φ - iθ_k φ) - β_k ∫ e y^{β - e_k} g φ`

because `∂_k(e φ) = e (∂_k φ - iθ_k φ)` (`fderiv_phase_mul`) and `∂_k y^β = β_k y^{β - e_k}`
(`fderiv_momentWeight`). Periodization (`integral_phase_mul_eq_cell_planeBlochC`) gives the cell
form. The weak forms are `integral_phase_moment_weakDeriv` and `cell_moment_weakDeriv`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.Assembly

/-- A continuous `ℤ²`-periodic complex function is bounded. -/
theorem exists_norm_bound_of_periodic {φ : Vec 2 → ℂ} (hc : Continuous φ)
    (hp : AVenhance.IsZ2Periodic φ) : ∃ M, ∀ y, ‖φ y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))
    ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun y => ?_⟩
  have hy : y = (fun i => Int.fract (y i)) + AVenhance.latticeShift (fun i => ⌊y i⌋) := by
    funext i
    simp [AVenhance.latticeShift]
  rw [hy, hp]
  exact hM (fun i => Int.fract (y i)) (fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)

/-- The derivative of a `ℤ²`-periodic complex function in a fixed direction is periodic. -/
theorem isZ2Periodic_fderiv_apply {φ : Vec 2 → ℂ} (hp : AVenhance.IsZ2Periodic φ) (v : Vec 2) :
    AVenhance.IsZ2Periodic (fun z => fderiv ℝ φ z v) := by
  intro n z
  show fderiv ℝ φ (z + AVenhance.latticeShift n) v = fderiv ℝ φ z v
  rw [← fderiv_comp_add_right]
  have e : (fun y => φ (y + AVenhance.latticeShift n)) = φ := funext fun y => hp n y
  rw [e]

/-- The twisted derivative of a periodic function is periodic. -/
theorem isZ2Periodic_fibreCovDeriv {φ : Vec 2 → ℂ} (hp : AVenhance.IsZ2Periodic φ) (θ : Vec 2)
    (k : Fin 2) : AVenhance.IsZ2Periodic (fibreCovDeriv θ k φ) := by
  intro n z
  have h1 : fderiv ℝ φ (z + AVenhance.latticeShift n) (basisVec k) = fderiv ℝ φ z (basisVec k) :=
    isZ2Periodic_fderiv_apply hp (basisVec k) n z
  simp only [fibreCovDeriv]
  rw [h1, hp n z]

/-- The twisted derivative of a `C^{j+1}` function is `C^j`. -/
theorem contDiff_fibreCovDeriv {φ : Vec 2 → ℂ} {j : ℕ} (hφ : ContDiff ℝ (j + 1 : ℕ) φ)
    (θ : Vec 2) (k : Fin 2) : ContDiff ℝ j (fibreCovDeriv θ k φ) := by
  have h1 : ContDiff ℝ j (fun z => fderiv ℝ φ z (basisVec k)) :=
    (hφ.fderiv_right (m := j) (by norm_cast)).clm_apply contDiff_const
  have h2 : ContDiff ℝ j φ := hφ.of_le (by norm_cast; omega)
  exact h1.add (contDiff_const.mul h2)

/-- The linear form `y ↦ θ·y`. -/
def vecDotCLM (θ : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  ∑ k : Fin 2, θ k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k

theorem vecDotCLM_apply (θ y : Vec 2) : vecDotCLM θ y = vecDot θ y := by
  simp [vecDotCLM, vecDot]

/-- The derivative of the phase `e^{-iθ·y}`. -/
theorem hasFDerivAt_planePhase (θ y : Vec 2) :
    HasFDerivAt (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))))
      (Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) •
        -(Complex.I • (Complex.ofRealCLM.comp (vecDotCLM θ)))) y := by
  have h1 : HasFDerivAt (fun y : Vec 2 => ((vecDot θ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (vecDotCLM θ)) y := by
    have := (Complex.ofRealCLM.comp (vecDotCLM θ)).hasFDerivAt (x := y)
    convert this using 1
    funext y'
    simp [vecDotCLM_apply]
  exact ((h1.const_mul Complex.I).neg).cexp

/-- `∂_k(e^{-iθ·y} φ) = e^{-iθ·y} (∂_k φ - iθ_k φ)`. -/
theorem fderiv_phase_mul {φ : Vec 2 → ℂ} (θ y : Vec 2) (hφ : DifferentiableAt ℝ φ y)
    (k : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * φ y) y
        (basisVec k) =
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * fibreCovDeriv (-θ) k φ y := by
  have h := (hasFDerivAt_planePhase θ y).mul hφ.hasFDerivAt
  rw [show (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * φ y) =
    (fun y : Vec 2 => Complex.exp (-(Complex.I * (vecDot θ y : ℂ)))) * φ from rfl, h.fderiv]
  have hv : vecDot θ (basisVec k) = θ k := by
    fin_cases k <;> simp [vecDot, basisVec_apply]
  simp [fibreCovDeriv, vecDotCLM_apply, hv]
  ring

/-- The index `β_k` of the moment weight `y^β`. -/
def momentIndex (β : ℕ × ℕ) (k : Fin 2) : ℕ := if k = 0 then β.1 else β.2

/-- The lowered moment `β - e_k` (truncated). -/
def momentShift (β : ℕ × ℕ) (k : Fin 2) : ℕ × ℕ :=
  if k = 0 then (β.1 - 1, β.2) else (β.1, β.2 - 1)

theorem momentWeight_contDiff (β : ℕ × ℕ) : ContDiff ℝ (⊤ : ℕ∞) (momentWeight β) := by
  unfold momentWeight
  fun_prop

/-- `∂_k y^β = β_k y^{β - e_k}`. -/
theorem fderiv_momentWeight (β : ℕ × ℕ) (y : Vec 2) (k : Fin 2) :
    fderiv ℝ (momentWeight β) y (basisVec k) =
      (momentIndex β k : ℝ) * momentWeight (momentShift β k) y := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y).pow β.1
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y).pow β.2
  have h := h0.mul h1
  have hfun : momentWeight β = (fun y : Vec 2 => y 0 ^ β.1) * fun y : Vec 2 => y 1 ^ β.2 :=
    funext fun y => rfl
  rw [hfun, h.fderiv]
  fin_cases k <;>
    simp [momentIndex, momentShift, momentWeight, basisVec_apply, nsmul_eq_mul] <;> ring

/-- A bounded continuous complex multiplier keeps a real integrable function integrable. -/
theorem integrable_ofReal_mul_bdd {f : Vec 2 → ℝ} (hf : Integrable f) {ψ : Vec 2 → ℂ}
    (hψ : Continuous ψ) {M : ℝ} (hM : ∀ y, ‖ψ y‖ ≤ M) :
    Integrable (fun y => (f y : ℂ) * ψ y) :=
  hf.ofReal.mul_bdd hψ.aestronglyMeasurable (Filter.Eventually.of_forall hM)

end AVRegularity.CycleWords.Assembly
end
end
end
