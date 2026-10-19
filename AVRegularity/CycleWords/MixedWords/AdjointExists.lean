-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleWords.MixedWords.AfwCrude
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleWords.MixedWords.GaussianAbsorb
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # B1 from the factorization and the gauge jets

On a complete block, B1.F (`RetainedAmplitudeFactorStatement`) writes the retained amplitude on the
low disc as `e^{Ξ}` times an amplitude pair with polynomial normalized derivatives, and B1.G
(`GaugeJetsStatement`) gives the normalized derivatives of `e^{Ξ}` with the Gaussian factor. The
Leibniz rule for the rotation (`ampDerivNorm_rot_le`), the comparison with the `θ`-partials, the
well-buffered hypothesis (the quiet-switching factor is at most one) and Gaussian absorption give
the bound of B1; off the support of the cutoff the amplitudes vanish near `θ`
(`compactChainGaussian_of_factor`). -/

section
universe u v

theorem fibreNorm_planeFibreFrequency (η : ℝ) (θ : Vec 2) :
    fibreNorm (planeFibreFrequency η θ) =
      Real.sqrt (vecDot ((Real.sqrt η)⁻¹ • θ) ((Real.sqrt η)⁻¹ • θ)) := by
  unfold fibreNorm planeFibreFrequency vecDot
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem continuous_fibreNorm_planeFibreFrequency (η : ℝ) :
    Continuous fun θ : Vec 2 => fibreNorm (planeFibreFrequency η θ) := by
  simp_rw [fibreNorm_planeFibreFrequency]
  exact Real.continuous_sqrt.comp (by unfold vecDot; fun_prop)

section Vanish

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Amplitudes vanishing near `θ` have vanishing jet norm at `θ`. -/
theorem amplitudeJetNorm_eq_zero_of_eventually (π : ι → ℝ) (m : ℕ) (ϖ : ℝ)
    {A B : ∀ x, Vec 2 → h x} {θ : Vec 2}
    (hev : ∀ x, (A x =ᶠ[𝓝 θ] fun _ => 0) ∧ (B x =ᶠ[𝓝 θ] fun _ => 0)) :
    amplitudeJetNorm π m ϖ A B θ = 0 := by
  have hz : ∀ x (a b : ℕ), thetaPartial a b (A x) θ = 0 ∧ thetaPartial a b (B x) θ = 0 := by
    intro x a b
    unfold thetaPartial
    rw [((hev x).1.iteratedFDeriv ℝ (a + b)).eq_of_nhds,
      ((hev x).2.iteratedFDeriv ℝ (a + b)).eq_of_nhds]
    simp
  unfold amplitudeJetNorm
  refine Finset.sum_eq_zero fun β _ => ?_
  simp [hz, ENNReal.zero_rpow_of_pos]

end Vanish

/-- The real inequality of the reduction. -/
theorem factor_constant_le {m P p : ℕ} {M1 CG CF Θ q cG x X : ℝ} (hM1 : 0 ≤ M1) (hCG : 0 ≤ CG)
    (hCF : 0 ≤ CF) (hΘ : 0 ≤ Θ) (hq0 : 0 ≤ q) (hq : q ≤ 2) (hcG : 0 < cG) (hx : 0 ≤ x)
    (hX : X = x ^ 2) :
    M1 * (2 * ((m + 1 : ℕ) : ℝ) * (CG * (1 + x) ^ m * Real.exp (-cG * X))) *
        (CF * Θ * (1 + x) ^ P * (1 + q)) ≤
      M1 * 2 * ((m + 1 : ℕ) : ℝ) * CG * CF * 3 * gaussConst (m + P) (cG / 2) * Θ *
        (1 + x) ^ p * Real.exp (-(cG / 2) * X) := by
  have he : Real.exp (-cG * X) = Real.exp (-(cG / 2) * x ^ 2) * Real.exp (-(cG / 2) * X) := by
    rw [← Real.exp_add, hX]
    ring_nf
  have habs := gauss_absorb (m + P) (half_pos hcG) hx
  have hp1 : 1 ≤ (1 + x) ^ p := one_le_pow₀ (by linarith)
  have hE0 : 0 ≤ Real.exp (-(cG / 2) * X) := (Real.exp_pos _).le
  have hcore : (1 + x) ^ m * (1 + x) ^ P * Real.exp (-cG * X) ≤
      gaussConst (m + P) (cG / 2) * (1 + x) ^ p * Real.exp (-(cG / 2) * X) := by
    rw [he, ← pow_add, ← mul_assoc]
    calc (1 + x) ^ (m + P) * Real.exp (-(cG / 2) * x ^ 2) * Real.exp (-(cG / 2) * X)
        ≤ gaussConst (m + P) (cG / 2) * Real.exp (-(cG / 2) * X) :=
          mul_le_mul_of_nonneg_right habs hE0
      _ ≤ gaussConst (m + P) (cG / 2) * (1 + x) ^ p * Real.exp (-(cG / 2) * X) := by
          rw [mul_assoc (gaussConst _ _)]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE0 hp1)
            (gaussConst_pos _ (half_pos hcG)).le
  have hK : 0 ≤ M1 * 2 * ((m + 1 : ℕ) : ℝ) * CG * CF * Θ := by positivity
  have hg := gaussConst_pos (m + P) (half_pos hcG)
  calc M1 * (2 * ((m + 1 : ℕ) : ℝ) * (CG * (1 + x) ^ m * Real.exp (-cG * X))) *
        (CF * Θ * (1 + x) ^ P * (1 + q))
      = (M1 * 2 * ((m + 1 : ℕ) : ℝ) * CG * CF * Θ) *
          ((1 + x) ^ m * (1 + x) ^ P * Real.exp (-cG * X)) * (1 + q) := by ring
    _ ≤ (M1 * 2 * ((m + 1 : ℕ) : ℝ) * CG * CF * Θ) *
          (gaussConst (m + P) (cG / 2) * (1 + x) ^ p * Real.exp (-(cG / 2) * X)) * 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcore hK) (by linarith) (by linarith)
          (mul_nonneg hK (mul_nonneg (mul_nonneg hg.le (pow_nonneg (by linarith) _)) hE0))
    _ = _ := by ring

/-- The end of a complete window is quiet after the last region. -/
theorem terminal_quiet {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) :
    Set.Ioc (t₀ + S - reg.buffer) (t₀ + S) ⊆ reg.quiet := by
  intro t ht
  have hle := pkg.buffer_le
  have hwin : t ∈ Set.Icc t₀ (t₀ + S) := ⟨by linarith [ht.1], ht.2⟩
  rcases pkg.cover t hwin with hq | ⟨p, hp⟩
  · exact hq
  · have hin := pkg.buffer_inside p
      ⟨by linarith [hp.1, hp.2, pkg.buffer_nonneg], le_refl _⟩
    linarith [hin.2, hp.2, ht.1]

/-- **B1 from the factorization and the gauge jets.** -/
theorem compactChainGaussian_of_factor (hF : RetainedAmplitudeFactorStatement.{u, v})
    (hG : GaugeJetsStatement) : CompactChainGaussianStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hFK⟩ := hF K
  refine ⟨g₁, hg₁, ?_⟩
  intro χlo hχ Nw D H m d Ks pos χr χ₃ hχr hχrc hχ₃ hχ₃b hrel
  obtain ⟨P, Q, hPQ⟩ := hFK Nw D H m d Ks pos
  obtain ⟨CG, cG, hCG, hcG, hGc⟩ := hG K m
  by_cases hK : 2 * K.ξlo < K.ξ0
  swap
  · refine ⟨1, 1, 1, 0, one_pos, one_pos, one_pos, ?_⟩
    intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ ϖ G v g reg pkg
    exact absurd pkg.consts_pos.2.2.1 hK
  set ψ : Vec 2 → ℝ := fun θ => χlo ((4 * K.ξlo / Real.pi) • θ) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.smooth.comp (contDiff_const_smul _)
  obtain ⟨CF, cF, hCF, hcF, hFc⟩ := hPQ 1 (2 * K.ξlo) χlo ψ hK le_rfl hχ.smooth hχ.supp hψs
    (exists_bound_iteratedFDeriv_comp_smul hχ.smooth hχ.hasCompactSupport _) χr χ₃ hχr
    (exists_bound_iteratedFDeriv_of_hasCompactSupport hχr hχrc) hχ₃ hχ₃b hrel
  set M1 : ℝ := ((m + 1 : ℕ) : ℝ) * 2 ^ m with hM1
  have hM10 : 0 ≤ M1 := by positivity
  refine ⟨M1 * 2 * ((m + 1 : ℕ) : ℝ) * CG * CF * 3 * gaussConst (m + P) (cG / 2),
    cG / 2, cF, Q, by have := gaussConst_pos (m + P) (half_pos hcG); positivity, half_pos hcG,
    hcF, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ ϖ G v g reg pkg hB hJ hwb X₀ κ hκ φ hφ
    f u w hf hch
  have hS1 := hB.hS
  have hterm : Set.Ioc (t₀ + S - reg.buffer) (t₀ + S) ⊆ reg.quiet :=
    terminal_quiet pkg.toCoreScalarPackage
  obtain ⟨hint, hret, hsmooth, Ac, As, hAcs, hrot, hbound⟩ :=
    hFc J π letters hletters η S ηg t₀ S ϖ t₀ (t₀ + S) reg.buffer G v g reg pkg.toCoreScalarPackage
      hB.toPiece le_rfl (by linarith) le_rfl (by linarith) pkg.buffer_nonneg hterm hJ X₀ κ hκ f u w
      (planeDatum_support_of_compact φ (fun x => (hφ x).2) _ hf) hch
  have hϖ := hB.ϖ_pos
  have hcp := pkg.consts_pos
  have hsη := Real.sqrt_pos.2 hB.hη
  have hret' : ∀ x, IsRetainedAmplitude
      (fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (2 * K.ξlo * Real.sqrt η)
      (retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
      (retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) := by
    refine hret (2 * K.ξlo * Real.sqrt η) (by have := hcp.2.1; positivity) fun θ hθ => ?_
    unfold pieceCutoff
    refine mul_eq_zero_of_left (hχ.supp _ ?_) _
    rw [sqrt_vecDot_smul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),
      inv_mul_eq_div, le_div_iff₀ hsη]
    have hθ' : 2 * K.ξlo * Real.sqrt η < Real.sqrt (vecDot θ θ) := by
      have hr0 : 0 ≤ 2 * K.ξlo * Real.sqrt η := by have := hcp.2.1; positivity
      rw [← Real.sqrt_sq hr0]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hθ
    exact hθ'.le
  refine ⟨hint, hret', hsmooth, fun θ _ => ?_⟩
  set A : ∀ x, Vec 2 → h x := fun x =>
    retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) with hA
  set Bs : ∀ x, Vec 2 → h x := fun x =>
    retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) with hBs
  by_cases hlow : fibreNorm (planeFibreFrequency η θ) ≤ 2 * K.ξlo
  · -- the low disc: rotation by the gauge
    set U : Set (Vec 2) := {θ' | fibreNorm (planeFibreFrequency η θ') < K.ξ0} with hU
    have hUo : IsOpen U := isOpen_lt (continuous_fibreNorm_planeFibreFrequency η) continuous_const
    have hθU : θ ∈ U := lt_of_le_of_lt hlow hcp.2.2.1
    obtain ⟨hEsm, hEj⟩ := hGc η S t₀ ϖ G v reg pkg hB.hη hB.hη1 hS1 hB.hϖ hB.hGm hB.hv hB.hvw
    set x : ℝ := Real.sqrt (vecDot θ θ) / ϖ with hx
    have hx0 : 0 ≤ x := div_nonneg (Real.sqrt_nonneg _) hϖ.le
    have hX : vecDot θ θ / ϖ ^ 2 = x ^ 2 := by
      have hv : 0 ≤ vecDot θ θ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      rw [hx, div_pow, Real.sq_sqrt hv]
    set Gv : ℝ := CG * (1 + x) ^ m * Real.exp (-cG * (vecDot θ θ / ϖ ^ 2)) with hGv
    have hGl : ∀ l ≤ m, ϖ ^ l * ‖iteratedFDeriv ℝ l
        (fun θ' => Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')) θ‖ ≤ Gv := by
      intro l hl
      refine (hEj θ hlow l hl).trans ?_
      have h1 : (1 + x) ^ l ≤ (1 + x) ^ m := pow_le_pow_right₀ (by linarith) hl
      have := Real.exp_pos (-cG * (vecDot θ θ / ϖ ^ 2))
      rw [hGv]
      gcongr
    have hrot' : ∀ θ' ∈ U, ∀ x', A x' θ' =
        (Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')).re • Ac x' θ' +
          (Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')).im • As x' θ' ∧
        Bs x' θ' = (Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')).re • As x' θ' -
          (Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ')).im • Ac x' θ' :=
      fun θ' hθ' x' => hrot θ' hθ' x'
    have h1 := amplitudeJetNorm_le_ampDerivNorm π m hϖ.le A Bs θ
    have h2 := ampDerivNorm_rot_le hUo hEsm π hB.hπ (fun x' => (hAcs x').1)
      (fun x' => (hAcs x').2) hrot' hθU hϖ.le hGl
    have h3 := hbound θ hθU
    simp only [blochFibreDerivNorm_congr_ae hf] at h3
    set q : ℝ := peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
      Real.exp (-cF * reg.buffer) + Real.exp (-cF * reg.buffer)) with hq
    have hq0 : 0 ≤ q := by
      rw [hq]
      unfold peFactor
      positivity
    have hq2 : q ≤ 2 := by
      have hw : (1 + (reg.joins : ℝ)) * peFactor η ^ Q * (1 + S) ^ Q *
          Real.exp (-cF * reg.buffer) ≤ 1 := hwb
      have hj : (1 : ℝ) ≤ 1 + (reg.joins : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) reg.joins
        linarith
      have hp : 0 ≤ peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-cF * reg.buffer) := by
        unfold peFactor
        positivity
      have : q = (1 + (reg.joins : ℝ)) * peFactor η ^ Q * (1 + S) ^ Q *
          Real.exp (-cF * reg.buffer) +
          peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-cF * reg.buffer) := by rw [hq]; ring
      rw [this]
      nlinarith
    have hreal := factor_constant_le (m := m) (P := P) (p := wordReserveP m Ks)
      hM10 hCG.le hCF.le hB.wordTheta_nonneg hq0 hq2 hcG hx0 hX
    calc amplitudeJetNorm π m ϖ A Bs θ
        ≤ ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * 2 ^ m) *
            (ENNReal.ofReal (2 * ((m + 1 : ℕ) : ℝ) * Gv) *
              (ENNReal.ofReal (CF * wordTheta ηg letters * (1 + x) ^ P * (1 + q)) *
                ∑ α ∈ momentIndices (wordReserveN m Ks),
                  ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                    blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α φ θ)) :=
          h1.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3)))
      _ = ENNReal.ofReal (M1 * (2 * ((m + 1 : ℕ) : ℝ) * Gv) *
            (CF * wordTheta ηg letters * (1 + x) ^ P * (1 + q))) *
            ∑ α ∈ momentIndices (wordReserveN m Ks),
              ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α φ θ := by
          have hΘ := hB.wordTheta_nonneg
          have hGv0 : 0 ≤ Gv := by
            rw [hGv]
            have := Real.exp_pos (-cG * (vecDot θ θ / ϖ ^ 2))
            have : 0 ≤ (1 + x) ^ m := pow_nonneg (by linarith) _
            positivity
          rw [ENNReal.ofReal_mul (p := M1 * (2 * ((m + 1 : ℕ) : ℝ) * Gv))
            (q := CF * wordTheta ηg letters * (1 + x) ^ P * (1 + q))
            (by positivity), ENNReal.ofReal_mul (p := M1) (q := 2 * ((m + 1 : ℕ) : ℝ) * Gv) hM10]
          ring
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
  · -- off the cutoff: the amplitudes vanish near `θ`
    have hV : IsOpen {θ' : Vec 2 | 2 * K.ξlo < fibreNorm (planeFibreFrequency η θ')} :=
      isOpen_lt continuous_const (continuous_fibreNorm_planeFibreFrequency η)
    have hθV : θ ∈ {θ' : Vec 2 | 2 * K.ξlo < fibreNorm (planeFibreFrequency η θ')} :=
      lt_of_not_ge hlow
    have hcut : ∀ θ' ∈ {θ' : Vec 2 | 2 * K.ξlo < fibreNorm (planeFibreFrequency η θ')},
        retainedCutoff K η χlo θ' = 0 := by
      intro θ' hθ'
      unfold retainedCutoff
      refine mul_eq_zero_of_left (hχ.supp _ ?_) _
      rw [← fibreNorm_planeFibreFrequency]
      exact le_of_lt hθ'
    have hev : ∀ x', (A x' =ᶠ[𝓝 θ] fun _ => 0) ∧ (Bs x' =ᶠ[𝓝 θ] fun _ => 0) := fun x' =>
      ⟨eventually_of_mem (hV.mem_nhds hθV) fun θ' hθ' => by
          simp only [hA, retainedCosAmplitude, hcut θ' hθ', mul_zero, zero_smul],
        eventually_of_mem (hV.mem_nhds hθV) fun θ' hθ' => by
          simp only [hBs, retainedSinAmplitude, hcut θ' hθ', mul_zero, zero_smul]⟩
    rw [amplitudeJetNorm_eq_zero_of_eventually π m ϖ hev]
    exact zero_le
end

/-! # Auxiliary facts for the Gaussian amplitude of the retained map

The Gaussian factor is bounded (`gaussFactor_le`); band-limited functions converge pointwise when
their amplitudes converge pointwise under a uniform bound (`tendsto_ampFun_of_bounded`, dominated
convergence on the ball); an amplitude pair of vanishing jet norm vanishes
(`amplitude_eq_zero_of_jetNorm`); the derivative of order `0` is the value
(`tendsto_value_of_iteratedFDeriv`). -/

section
/-- **The Gaussian factor is bounded.** -/
theorem gaussFactor_le {CGa Θ cGa ϖ : ℝ} (hC : 0 ≤ CGa * Θ) (hc : 0 < cGa) (hϖ : 0 < ϖ) (p : ℕ)
    (θ : Vec 2) :
    CGa * Θ * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p * Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2)) ≤
      CGa * Θ * gaussConst p cGa := by
  have hx0 : 0 ≤ Real.sqrt (vecDot θ θ) / ϖ := div_nonneg (Real.sqrt_nonneg _) hϖ.le
  have hX : vecDot θ θ / ϖ ^ 2 = (Real.sqrt (vecDot θ θ) / ϖ) ^ 2 := by
    have hv : 0 ≤ vecDot θ θ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [div_pow, Real.sq_sqrt hv]
  rw [hX, mul_assoc]
  exact mul_le_mul_of_nonneg_left (gauss_absorb p hc hx0) hC

section Values

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of order `0` is the value. -/
theorem tendsto_value_of_iteratedFDeriv {A : ℕ → Vec 2 → E} {A₀ : Vec 2 → E} {θ : Vec 2}
    (h : Tendsto (fun k => iteratedFDeriv ℝ 0 (A k) θ) atTop (𝓝 (iteratedFDeriv ℝ 0 A₀ θ))) :
    Tendsto (fun k => A k θ) atTop (𝓝 (A₀ θ)) := by
  have := ((continuous_eval_const (Fin.elim0 : Fin 0 → Vec 2)).tendsto _).comp h
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using this

/-- **Pointwise convergence of band-limited functions** under a uniform bound of the amplitudes. -/
theorem tendsto_ampFun_of_bounded {r : ℝ} {A B : ℕ → Vec 2 → E} {A₀ B₀ : Vec 2 → E}
    (hA : ∀ k, Continuous (A k)) (hB : ∀ k, Continuous (B k))
    (hlimA : ∀ θ, Tendsto (fun k => A k θ) atTop (𝓝 (A₀ θ)))
    (hlimB : ∀ θ, Tendsto (fun k => B k θ) atTop (𝓝 (B₀ θ))) {M : ℝ}
    (hbd : ∀ᶠ k in atTop, ∀ θ, ‖A k θ‖ ≤ M ∧ ‖B k θ‖ ≤ M) (z : Vec 2) :
    Tendsto (fun k => ampFun r (A k) (B k) z) atTop (𝓝 (ampFun r A₀ B₀ z)) := by
  have : IsFiniteMeasure (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact amplitudeBall_volume_lt_top r⟩
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  unfold ampFun
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M + M)
    (Eventually.of_forall fun k => ((((Real.continuous_cos.comp hc).smul (hA k)).add
      ((Real.continuous_sin.comp hc).smul (hB k))).aestronglyMeasurable))
    (hbd.mono fun k hk => Eventually.of_forall fun θ => ?_) (integrable_const _)
    (Eventually.of_forall fun θ => ?_)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)).trans (hk θ).1
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)).trans (hk θ).2
  · exact ((hlimA θ).const_smul _).add ((hlimB θ).const_smul _)

end Values

section Zero

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem thetaPartial_zero_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec 2 → E) (θ : Vec 2) : thetaPartial 0 0 f θ = f θ := by
  simp only [thetaPartial]
  rfl

/-- **An amplitude pair of vanishing jet norm vanishes.** -/
theorem amplitude_eq_zero_of_jetNorm (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (m : ℕ) {ϖ : ℝ}
    (hϖ : 0 < ϖ) {A B : ∀ x, Vec 2 → h x} {θ : Vec 2} (h0 : amplitudeJetNorm π m ϖ A B θ = 0)
    (x : ι) : A x θ = 0 ∧ B x θ = 0 := by
  have hβ : ((0, 0) : ℕ × ℕ) ∈ momentIndices m := by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  obtain ⟨hA, hB⟩ := ofReal_norm_thetaPartial_le π hπ hϖ A B θ hβ x
  rw [h0, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, thetaPartial_zero_zero] at hA hB
  exact ⟨norm_le_zero_iff.1 hA, norm_le_zero_iff.1 hB⟩

end Zero
end

/-! # The Gaussian amplitude of the retained map from the leaves

`retainedGaussian_of_leaves`: approximants `φ_k` of the datum (A4) start chains (A3) whose explicit
amplitudes are linear in the datum (A1, B1 at the datum `0`); by B1 for the differences and D1 they
are uniformly Cauchy in the amplitude jet norm, so they converge in `C^m` (`exists_amplitude_limit`)
to an even/odd pair representing `R F` (pointwise convergence of `R φ_k`, dominated convergence on
the ball), and B1's Gaussian bound passes to the limit with D1 for the Bloch fibre norms. -/

section
universe u v

/-- Passing a Gaussian-type bound to the limit. -/
theorem le_of_tendsto_weighted {L : ℝ≥0∞} {a : ℕ → ℝ≥0∞} {G : ℝ≥0∞} (hG : G ≠ ⊤)
    (s : Finset (ℕ × ℕ)) (w b : ℕ × ℕ → ℝ≥0∞) (hw : ∀ α, w α ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {mk : ℕ → ℝ≥0∞} (hm : Tendsto mk atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 L))
    (hle : ∀ k, a k ≤ G * ∑ α ∈ s, w α * (b α + C * mk k)) :
    L ≤ G * ∑ α ∈ s, w α * b α := by
  have hR : Tendsto (fun k => G * ∑ α ∈ s, w α * (b α + C * mk k)) atTop
      (𝓝 (G * ∑ α ∈ s, w α * (b α + C * 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun α _ => ENNReal.Tendsto.const_mul
      (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hm (Or.inr hC))) (Or.inr (hw α)))
      (Or.inr hG)
  simp only [mul_zero, add_zero] at hR
  exact le_of_tendsto_of_tendsto' ha hR hle

/-- A Gaussian bound with uniformly bounded fibre norms. -/
theorem jetNorm_le_of_gauss {X M : ℝ≥0∞} {g Ginf CD : ℝ} (hg : g ≤ Ginf) (hCD : 0 ≤ CD)
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (hw : ∀ α, 0 ≤ w α) (bf : ℕ × ℕ → ℝ≥0∞)
    (hbf : ∀ α ∈ s, bf α ≤ ENNReal.ofReal CD * M)
    (hX : X ≤ ENNReal.ofReal g * ∑ α ∈ s, ENNReal.ofReal (w α) * bf α) :
    X ≤ ENNReal.ofReal (Ginf * (∑ α ∈ s, w α) * CD) * M := by
  have hW : 0 ≤ ∑ α ∈ s, w α := Finset.sum_nonneg fun α _ => hw α
  refine hX.trans ?_
  calc ENNReal.ofReal g * ∑ α ∈ s, ENNReal.ofReal (w α) * bf α
      ≤ ENNReal.ofReal Ginf * ∑ α ∈ s, ENNReal.ofReal (w α) * (ENNReal.ofReal CD * M) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hg)
          (Finset.sum_le_sum fun α hα => mul_le_mul' le_rfl (hbf α hα))
    _ = ENNReal.ofReal (Ginf * (∑ α ∈ s, w α) * CD) * M := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun α _ => hw α]
        by_cases hG : 0 ≤ Ginf
        · rw [ENNReal.ofReal_mul (mul_nonneg hG hW), ENNReal.ofReal_mul hG]
          ring
        · rw [ENNReal.ofReal_of_nonpos (not_le.1 hG).le,
            ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hG).le hW) hCD)]
          simp

/-- **The Gaussian amplitude of the retained map from the leaves.** -/
theorem retainedGaussian_of_leaves (hA1 : ChainCombinationStatement.{u, v})
    (hA3 : CompactChainExistenceStatement.{u, v}) (hA4 : CompactDensityStatement.{u, v})
    (hB0 : AmplitudePlancherelStatement.{v}) (hB1 : CompactChainGaussianStatement.{u, v})
    (hD1 : BlochFibreContinuityStatement.{u, v}) : RetainedGaussianStatement.{u, v} := by
  intro K
  have hA3K := (hA3 K).choose_spec
  have hB1K := (hB1 K).choose_spec
  refine ⟨min (hA3 K).choose (hB1 K).choose, lt_min hA3K.1 hB1K.1, ?_⟩
  intro χr hχr Nw D H m d Ks pos
  -- the retained map is cut off by `χ_r^{n+1}`; the datum norms keep `χ_r`
  set χlo : Vec 2 → ℝ := fun ξ => χr ξ ^ (wordReserveN m Ks + 1) with hχlo
  have hχ : IsLowCutoff K χlo := hχr.pow _
  obtain ⟨CGa, cGa, c₁, Q₁, hCGa, hcGa, hc₁, hB1s⟩ := hB1K.2 χlo hχ Nw D H m d Ks pos χr
    (fun _ => 1) hχr.smooth hχr.hasCompactSupport contDiff_const
    exists_bound_iteratedFDeriv_const_one fun ξ => (mul_one _).symm
  refine ⟨CGa, cGa, c₁, Q₁, hCGa, hcGa, hc₁, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ ϖ G v g reg pkg hB hJ hwb X₀ R hR F
    hFm hFfin
  have hKs : (fun i => (letters i).slow) = Ks := funext fun i => (hletters i).2.1
  have hd : (fun i => (letters i).order) = d := funext fun i => (hletters i).1
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN 0 fun i => (letters i).slow)
      fun i => (letters i).order) (fun i => (letters i).order) ≤ J := by
    rw [hKs, hd]
    exact (wordReserveJstar_le 0 0 0 m Ks d le_rfl (Nat.zero_le _)).trans hJ
  have hξ : 0 < K.ξlo := pkg.consts_pos.2.1
  have hsη := Real.sqrt_pos.2 hB.hη
  have hr : 0 < 2 * K.ξlo * Real.sqrt η := by positivity
  have hϖ := hB.ϖ_pos
  have hπ := hB.hπ
  have hΘ := hB.wordTheta_nonneg
  have hslots := wordBaseSlots_isWordSlots letters hB.hlet
  -- B1 on the chains of the block
  have hB1b := fun (κ : Fin (Nw + 1) → ι → ℕ) (hκ : IsWordSlots letters κ)
      (φ : ∀ x, Vec 2 → h x) (hφ : IsCompactFamily φ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
      (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
      (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
      (hf : ∀ x, planeValue (f x) =ᵐ[volume] φ x)
      (hc : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
        (fun _ _ _ => 0) u w) =>
    hB1s J π letters hletters η S ηg t₀ ϖ G v g reg pkg (hB.mono (min_le_right _ _)) hJ hwb X₀ κ
      hκ φ hφ f u w hf hc
  have hint : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        IsCompactDatum f → ∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume := by
    intro κ hκ f u w hc hf
    obtain ⟨φ, hφ, hfφ⟩ := hf.exists_family
    exact (hB1b κ hκ φ hφ f u w hfφ hc).1
  -- off the zone the explicit amplitudes vanish
  have hoff : ∀ (y : ι) (e : Vec 2 → h y) (θ : Vec 2), Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) →
      retainedCosAmplitude K η χlo e θ = 0 ∧ retainedSinAmplitude K η χlo e θ = 0 := by
    intro y e θ hθ
    simp only [retainedCosAmplitude, retainedSinAmplitude, retainedCutoff_eq_zero hχ η hθ,
      mul_zero, zero_smul, and_self]
  have hcube : ∀ θ : Vec 2, ¬ (∀ i, |θ i| ≤ Real.pi) → Real.pi / 2 < Real.sqrt (vecDot θ θ) := by
    intro θ hθ
    push Not at hθ
    obtain ⟨i, hi⟩ := hθ
    have h1 : |θ i| ≤ Real.sqrt (vecDot θ θ) := Real.abs_le_sqrt (by
      rw [sq]
      exact Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i))
    linarith [Real.pi_pos]
  have hB1z : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, planeValue (f x) =ᵐ[volume] 0) →
        ∀ x, retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 := by
    intro κ hκ f u w hc hf0 x
    have hb1 := hB1b κ hκ 0 isCompactFamily_zero f u w hf0 hc
    have hpt : ∀ θ : Vec 2,
        retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ = 0 := by
      intro θ
      by_cases hθ : ∀ i, |θ i| ≤ Real.pi
      · have hle := hb1.2.2.2 θ hθ
        simp only [blochFibreDerivNorm_zero_family, mul_zero, Finset.sum_const_zero] at hle
        exact amplitude_eq_zero_of_jetNorm π hπ m hϖ (le_antisymm hle zero_le) x
      · exact hoff _ _ θ (hcube θ hθ).le
    exact ⟨funext fun θ => (hpt θ).1, funext fun θ => (hpt θ).2⟩
  have hexist := fun (f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x))
      (hf : IsCompactDatum f) =>
    hA3K.2 H J π letters η S ηg t₀ ϖ G v g reg pkg (hB.mono (min_le_left _ _)) hJ0 X₀ f hf
  obtain ⟨ampC, ampS, hlin, hid⟩ := exists_linearAmplitudes hA1 hA4 K η χlo hB.hD letters S ηg
    t₀ ϖ G v X₀ hslots hexist hint hB1z
  -- a chain for every compact datum
  have hchain : ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∃ (f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (wordBaseSlots letters j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (wordBaseSlots letters j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) ∧
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (wordBaseSlots letters) t₀ (t₀ + S) v
          f (fun _ _ _ => 0) u w := by
    intro φ hφ
    have hl := fun x => hA4.1 (wordBaseSlots letters 0 x) (φ x) (hφ x).1 (hφ x).2
    choose f hf using hl
    obtain ⟨u, w, hc⟩ := hexist f fun x => ⟨φ x, (hφ x).1, (hφ x).2, hf x⟩
    exact ⟨f, u, w, hf, hc⟩
  -- B1 for the amplitudes of compact data
  have hamp : ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      (∀ x, IsRetainedAmplitude (R φ x) (2 * K.ξlo * Real.sqrt η) (ampC φ x) (ampS φ x)) ∧
      (∀ x, ContDiff ℝ m (ampC φ x) ∧ ContDiff ℝ m (ampS φ x)) ∧
      (∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → ampC φ x θ = 0 ∧ ampS φ x θ = 0) ∧
      (∀ x θ, ampC φ x (-θ) = ampC φ x θ ∧ ampS φ x (-θ) = -ampS φ x θ) ∧
      ∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
        amplitudeJetNorm π m ϖ (ampC φ) (ampS φ) θ ≤
          ENNReal.ofReal (CGa * wordTheta ηg letters *
              (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ wordReserveP m Ks *
              Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
            ∑ α ∈ momentIndices (wordReserveN m Ks),
              ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α φ θ := by
    intro φ hφ
    obtain ⟨f, u, w, hf, hc⟩ := hchain φ hφ
    obtain ⟨hC, hS⟩ := hid _ hslots φ hφ f u w hf hc
    have hb := hB1b _ hslots φ hφ f u w hf hc
    have hcd : IsCompactDatum f := fun x => ⟨φ x, (hφ x).1, (hφ x).2, hf x⟩
    have hRφ : R φ = fun x =>
        fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))) := by
      rw [hR.congr φ (fun x => planeValue (f x)) fun x => (hf x).symm]
      exact hR.chain _ hslots f u w hc hcd
    rw [hC, hS, hRφ]
    exact ⟨hb.2.1, hb.2.2.1, fun x θ hθ => hoff _ _ θ hθ,
      fun x θ => ⟨retainedCosAmplitude_neg hχ η _ θ, retainedSinAmplitude_neg hχ η _ θ⟩,
      hb.2.2.2⟩
  -- D1 at the scale `ϖ`
  have hχs : ContDiff ℝ (⊤ : ℕ∞) (fun θ' : Vec 2 => χr ((Real.sqrt η)⁻¹ • θ')) :=
    hχr.smooth.comp (contDiff_const_smul _)
  have hχc : HasCompactSupport (fun θ' : Vec 2 => χr ((Real.sqrt η)⁻¹ • θ')) :=
    hχr.hasCompactSupport.comp_smul (inv_ne_zero hsη.ne')
  obtain ⟨CD, hCD, hD1b⟩ := hD1 (wordReserveN m Ks) _ hχs hχc ϖ hϖ
  have hbfd0 : ∀ ψ : ∀ x, Vec 2 → h x, IsCompactFamily ψ →
      ∀ α ∈ momentIndices (wordReserveN m Ks), ∀ θ,
        blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α ψ θ ≤
          ENNReal.ofReal CD * momentNorm π (wordReserveN m Ks + 2) ϖ ψ := by
    intro ψ hψ α hα θ
    have hαn : α.1 + α.2 ≤ wordReserveN m Ks := (Finset.mem_filter.1 hα).2
    have h0 : momentNorm π (wordReserveN m Ks + 2) ϖ (0 : ∀ x, Vec 2 → h x) < ⊤ := by
      rw [momentNorm_zero_family]
      exact ENNReal.zero_lt_top
    have := hD1b π hπ ψ 0 hψ.aestronglyMeasurable (fun _ => aestronglyMeasurable_const)
      (momentNorm_lt_top_of_compact _ _ _ hψ) h0 α hαn θ
    rw [blochFibreDerivNorm_zero_family, zero_add] at this
    simpa using this
  -- the approximants
  obtain ⟨φs, hφs0, hconv⟩ := hA4.2 F hFm
  have hφs : ∀ k, IsCompactFamily (φs k) := fun k x => hφs0 k x
  have hconvN := hconv π (wordReserveN m Ks + 2) ϖ hFfin
  -- the constants
  have hCΘ : 0 ≤ CGa * wordTheta ηg letters := mul_nonneg hCGa.le hΘ
  have hGinf : 0 ≤ CGa * wordTheta ηg letters * gaussConst (wordReserveP m Ks) cGa :=
    mul_nonneg hCΘ (gaussConst_pos _ hcGa).le
  have hW0 : 0 ≤ ∑ α ∈ momentIndices (wordReserveN m Ks),
      ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ) :=
    Finset.sum_nonneg fun α _ => by positivity
  set K1 : ℝ := CGa * wordTheta ηg letters * gaussConst (wordReserveP m Ks) cGa *
    (∑ α ∈ momentIndices (wordReserveN m Ks),
      ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) * CD with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg (mul_nonneg hGinf hW0) hCD.le
  have hsqrt : Continuous fun θ : Vec 2 => Real.sqrt (vecDot θ θ) :=
    Real.continuous_sqrt.comp (by unfold vecDot; fun_prop)
  -- the uniform Cauchy bound
  have hcau : ∀ k l θ, amplitudeJetNorm π m ϖ (fun x => ampC (φs k) x - ampC (φs l) x)
      (fun x => ampS (φs k) x - ampS (φs l) x) θ ≤
        ENNReal.ofReal (K1 * (momentNorm π (wordReserveN m Ks + 2) ϖ
          (fun x z => φs k x z - φs l x z)).toReal) := by
    intro k l θ
    set ψ : ∀ x, Vec 2 → h x := fun x z => (1 : ℝ) • φs k x z + (-1 : ℝ) • φs l x z with hψ
    have hψc : IsCompactFamily ψ := (hφs k).add_smul (hφs l) 1 (-1)
    have hAψ : (fun x => ampC (φs k) x - ampC (φs l) x) = ampC ψ := by
      rw [(hlin _ _ (hφs k) (hφs l) 1 (-1)).1]
      funext x θ
      simp [sub_eq_add_neg]
    have hBψ : (fun x => ampS (φs k) x - ampS (φs l) x) = ampS ψ := by
      rw [(hlin _ _ (hφs k) (hφs l) 1 (-1)).2]
      funext x θ
      simp [sub_eq_add_neg]
    have hmψ : momentNorm π (wordReserveN m Ks + 2) ϖ ψ =
        momentNorm π (wordReserveN m Ks + 2) ϖ (fun x z => φs k x z - φs l x z) := by
      congr 1
      funext x z
      simp [hψ, sub_eq_add_neg]
    have hfin : momentNorm π (wordReserveN m Ks + 2) ϖ (fun x z => φs k x z - φs l x z) ≠ ⊤ :=
      hmψ ▸ (momentNorm_lt_top_of_compact _ _ _ hψc).ne
    rw [hAψ, hBψ, ENNReal.ofReal_mul hK10, ENNReal.ofReal_toReal hfin, ← hmψ]
    by_cases hθ : ∀ i, |θ i| ≤ Real.pi
    · exact jetNorm_le_of_gauss (gaussFactor_le hCΘ hcGa hϖ _ θ) hCD.le _ _
        (fun α => by positivity) _ (fun α hα => hbfd0 ψ hψc α hα θ) ((hamp ψ hψc).2.2.2.2 θ hθ)
    · have hU : IsOpen {θ' : Vec 2 | Real.pi / 2 < Real.sqrt (vecDot θ' θ')} :=
        isOpen_lt continuous_const hsqrt
      rw [amplitudeJetNorm_eq_zero_of_eventually π m ϖ fun x =>
        ⟨eventually_of_mem (hU.mem_nhds (hcube θ hθ)) fun θ' hθ' =>
          ((hamp ψ hψc).2.2.1 x θ' hθ'.le).1,
        eventually_of_mem (hU.mem_nhds (hcube θ hθ)) fun θ' hθ' =>
          ((hamp ψ hψc).2.2.1 x θ' hθ'.le).2⟩]
      exact zero_le
  have hcN : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, K1 * (momentNorm π (wordReserveN m Ks + 2) ϖ
      (fun x z => φs k x z - φs l x z)).toReal < ε := by
    intro ε hε
    have hK11 : 0 < K1 + 1 := by linarith
    have hδ : 0 < ε / (2 * (K1 + 1)) := div_pos hε (mul_pos two_pos hK11)
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 (hconvN.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ)))
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := (momentNorm_sub_le_approx π (wordReserveN m Ks + 2) ϖ F (φs k) (φs l)).trans_lt
      (ENNReal.add_lt_add (hN k hk) (hN l hl))
    rw [← ENNReal.ofReal_add hδ.le hδ.le] at h1
    have h2 := ENNReal.toReal_lt_of_lt_ofReal h1
    have h3 : K1 * (ε / (2 * (K1 + 1)) + ε / (2 * (K1 + 1))) = ε * (K1 / (K1 + 1)) := by
      rw [← add_div, ← two_mul, mul_div_mul_left _ _ two_ne_zero]
      ring
    calc K1 * (momentNorm π (wordReserveN m Ks + 2) ϖ (fun x z => φs k x z - φs l x z)).toReal
        ≤ K1 * (ε / (2 * (K1 + 1)) + ε / (2 * (K1 + 1))) := mul_le_mul_of_nonneg_left h2.le hK10
      _ = ε * (K1 / (K1 + 1)) := h3
      _ < ε := mul_lt_of_lt_one_right hε (by rw [div_lt_one hK11]; linarith)
  obtain ⟨A₀, B₀, hAB₀, hconvAB⟩ := exists_amplitude_limit π hπ m hϖ
    (fun k x => ((hamp _ (hφs k)).2.1 x).1) (fun k x => ((hamp _ (hφs k)).2.1 x).2) _ hcau hcN
  -- pointwise limits of the values
  have hvalA : ∀ x θ, Tendsto (fun k => ampC (φs k) x θ) atTop (𝓝 (A₀ x θ)) := fun x θ =>
    tendsto_value_of_iteratedFDeriv (hconvAB x 0 (Nat.zero_le _) θ).1
  have hvalB : ∀ x θ, Tendsto (fun k => ampS (φs k) x θ) atTop (𝓝 (B₀ x θ)) := fun x θ =>
    tendsto_value_of_iteratedFDeriv (hconvAB x 0 (Nat.zero_le _) θ).2
  -- a uniform bound of the amplitudes, eventually
  have hβ0 : ((0, 0) : ℕ × ℕ) ∈ momentIndices m := by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hmomt := momentNorm_tendsto π (wordReserveN m Ks + 2) ϖ F φs hFfin hconvN
  set MF : ℝ := (momentNorm π (wordReserveN m Ks + 2) ϖ F).toReal with hMF
  have hev : ∀ᶠ k in atTop, momentNorm π (wordReserveN m Ks + 2) ϖ (φs k) ≤
      ENNReal.ofReal (MF + 1) := by
    refine hmomt.eventually (ge_mem_nhds ?_)
    rw [hMF, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hFfin.ne]
    exact ENNReal.lt_add_right hFfin.ne (ENNReal.ofReal_pos.2 one_pos).ne'
  have hbound : ∀ x, ∀ᶠ k in atTop, ∀ θ,
      ‖ampC (φs k) x θ‖ ≤ partialConst ϖ (0, 0) (π x) * K1 * (MF + 1) ∧
        ‖ampS (φs k) x θ‖ ≤ partialConst ϖ (0, 0) (π x) * K1 * (MF + 1) := by
    intro x
    refine hev.mono fun k hk θ => ?_
    have hM0 : 0 ≤ partialConst ϖ (0, 0) (π x) * K1 * (MF + 1) :=
      mul_nonneg (mul_nonneg (partialConst_nonneg hϖ _ _) hK10) (by positivity)
    by_cases hθ : ∀ i, |θ i| ≤ Real.pi
    · have hJ1 : amplitudeJetNorm π m ϖ (ampC (φs k)) (ampS (φs k)) θ ≤
          ENNReal.ofReal K1 * ENNReal.ofReal (MF + 1) :=
        (jetNorm_le_of_gauss (gaussFactor_le hCΘ hcGa hϖ _ θ) hCD.le _ _ (fun α => by positivity)
          _ (fun α hα => hbfd0 (φs k) (hφs k) α hα θ) ((hamp _ (hφs k)).2.2.2.2 θ hθ)).trans
          (mul_le_mul' le_rfl hk)
      obtain ⟨hA1', hB1'⟩ := ofReal_norm_thetaPartial_le π hπ hϖ (ampC (φs k)) (ampS (φs k)) θ
        hβ0 x
      rw [thetaPartial_zero_zero] at hA1' hB1'
      have hconst : ENNReal.ofReal (partialConst ϖ (0, 0) (π x)) *
          (ENNReal.ofReal K1 * ENNReal.ofReal (MF + 1)) =
          ENNReal.ofReal (partialConst ϖ (0, 0) (π x) * K1 * (MF + 1)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (partialConst_nonneg hϖ _ _) hK10),
          ENNReal.ofReal_mul (partialConst_nonneg hϖ _ _), mul_assoc]
      refine ⟨(ENNReal.ofReal_le_ofReal_iff hM0).1 ?_, (ENNReal.ofReal_le_ofReal_iff hM0).1 ?_⟩
      · exact hA1'.trans ((mul_le_mul' le_rfl hJ1).trans (le_of_eq hconst))
      · exact hB1'.trans ((mul_le_mul' le_rfl hJ1).trans (le_of_eq hconst))
    · obtain ⟨h1, h2⟩ := (hamp _ (hφs k)).2.2.1 x θ (hcube θ hθ).le
      rw [h1, h2, norm_zero]
      exact ⟨hM0, hM0⟩
  -- the representation of `R F`
  have hn₀ : wordReserveN 0 (fun i => (letters i).slow) ≤ wordReserveN m Ks + 2 := by
    rw [hKs]
    unfold wordReserveN
    omega
  have hconv0 := hconv π (wordReserveN 0 fun i => (letters i).slow) ϖ
    ((momentNorm_mono hn₀ π ϖ F).trans_lt hFfin)
  have hrep : ∀ x z, R F x z = ampFun (2 * K.ξlo * Real.sqrt η) (A₀ x) (B₀ x) z := by
    intro x z
    have ht1 : Tendsto (fun k => R (φs k) x z) atTop (𝓝 (R F x z)) := by
      have := retainedMap_orderedDerivative_tendsto hB0 hR hr hπ F φs hFm
        (fun k y => (hφs k).aestronglyMeasurable y) hconv0 x 0 Fin.elim0 z
      simpa only [orderedDerivative_zero] using this
    have hRk : ∀ k, R (φs k) x z =
        ampFun (2 * K.ξlo * Real.sqrt η) (ampC (φs k) x) (ampS (φs k) x) z := fun k =>
      ((hamp _ (hφs k)).1 x).2.2.2 z
    simp_rw [hRk] at ht1
    exact tendsto_nhds_unique ht1 (tendsto_ampFun_of_bounded
      (fun k => ((hamp _ (hφs k)).2.1 x).1.continuous)
      (fun k => ((hamp _ (hφs k)).2.1 x).2.continuous) (hvalA x) (hvalB x) (hbound x) z)
  refine ⟨A₀, B₀, fun x => ⟨fun θ hθ => ⟨?_, ?_⟩,
      ContinuousOn.integrableOn_compact (isCompact_ampBall _) (hAB₀ x).1.continuous.continuousOn,
      ContinuousOn.integrableOn_compact (isCompact_ampBall _) (hAB₀ x).2.continuous.continuousOn,
      hrep x⟩, hAB₀, fun x θ => ⟨?_, ?_⟩, fun θ hθ => ?_⟩
  · exact tendsto_nhds_unique (hvalA x θ) (tendsto_const_nhds.congr fun k =>
      ((((hamp _ (hφs k)).1 x).1 θ hθ).1).symm)
  · exact tendsto_nhds_unique (hvalB x θ) (tendsto_const_nhds.congr fun k =>
      ((((hamp _ (hφs k)).1 x).1 θ hθ).2).symm)
  · exact tendsto_nhds_unique (hvalA x (-θ)) ((hvalA x θ).congr fun k =>
      (((hamp _ (hφs k)).2.2.2.1 x θ).1).symm)
  · exact tendsto_nhds_unique (hvalB x (-θ)) ((hvalB x θ).neg.congr fun k =>
      (((hamp _ (hφs k)).2.2.2.1 x θ).2).symm)
  · -- the Gaussian bound passes to the limit
    have hL := tendsto_amplitudeJetNorm π m ϖ θ (fun x j hj => (hconvAB x j hj θ).1)
      (fun x j hj => (hconvAB x j hj θ).2)
    have hmk : Tendsto (fun k => momentNorm π (wordReserveN m Ks + 2) ϖ
        (fun x z => φs k x z - F x z)) atTop (𝓝 0) := by
      simp_rw [momentNorm_sub_comm π (wordReserveN m Ks + 2) ϖ (φs _) F]
      exact hconvN
    refine le_of_tendsto_weighted (C := ENNReal.ofReal CD) ENNReal.ofReal_ne_top _ _ _
      (fun α => ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top hmk hL fun k =>
        ((hamp _ (hφs k)).2.2.2.2 θ hθ).trans ?_
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun α hα => mul_le_mul' le_rfl ?_)
    have hαn : α.1 + α.2 ≤ wordReserveN m Ks := (Finset.mem_filter.1 hα).2
    exact hD1b π hπ (φs k) F (hφs k).aestronglyMeasurable hFm
      (momentNorm_lt_top_of_compact _ _ _ (hφs k)) hFfin α hαn θ
end

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Genuine adjoint fibre curves from any terminal test

For the fibre coefficients `⟨G, v, θ, 0⟩` and any `ψ ∈ L²` of the cell, there is a genuine
backward adjoint curve on `[a, t]` ending at `ψ` (`adjointCurve_exists`). It is the conjugate
time reflection (`CellWeakHilbertCurve.reflected_adjoint`) of the forward solution of the reversed
problem on `[-t, -a]` started at `conj ψ` (`cellActual_exists_Hilbert`). This supplies the terminal
test `q` and the test families of H4 of the abstract fibre word. -/

/-- **Adjoint fibre curves exist from every terminal test.** -/
theorem adjointCurve_exists {a t : ℝ} (hat : a ≤ t)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ) (ψ : ComplexCellL2) :
    ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a t Ψv Ψs (fun r =>
        -cellDualDerivative (cellAdjointCoefficients ⟨G, v, θ, 0⟩) hG V (cellDrift_neg hv).1
          (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧ Ψv t = ψ := by
  have hr : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := fun s x => by
    simpa only [Pi.neg_apply, neg_sq] using hb (-s) x
  obtain ⟨u, slice, hu, hu0⟩ := cellActual_exists_Hilbert (neg_le_neg hat)
    ⟨fun s x => G (-s) x, fun s x => -v (-s) x, fun j => -θ j, 0⟩ (cellMetric_timeReverse hG)
    V 0 (cellDrift_timeReverse hv).1 hr measurable_const (fun _ => by simp)
    (fun _ _ => 0) (fun _ _ => 0) measurable_const measurable_const (by simp [cellL2Norm])
    (by simp [cellL2Norm])
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ψ)
  have hu' : CellWeakHilbertCurve (-t) (-a) u slice (fun r =>
      cellDualDerivative ⟨fun s x => G (-s) x, fun s x => -v (-s) x, fun j => -θ j, 0⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1 hr r (slice r) 0 0) := by
    simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
      show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hu
  refine ⟨fun r => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)),
    fun r => cellH1Conj (slice (-r)), hu'.reflected_adjoint G hG hv V hb θ, ?_⟩
  simp only [hu0, cellFiberConj_involutive]

end AVRegularity.CycleWords.Assembly
end
end
