-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.CoarseLetters
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleWords.CellTransitionGeometry
import AVRegularity.CycleComparison.Reconstruction.ClassicalBridge
public import AVRegularity.CycleComparison.Reconstruction.ApproxDefect
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Applications.Transfer.TubeK
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Velocity.ExistsLimitVelocity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Assembly

/-! **The coarse drift is small at the scale of the window**. `coarse_drift_fields` with the
quantitative smallness `a B₀ R² ≤ C₁ B E^{2δ}` of the actual drift scale `a = 2¹³‖ι‖ a_{m-1}`
exposed (`coarse_drift_small`): the coarse defect bound needs `q₀ ≲ E^{2δ}`, which the drift
condition `a B₀ R² ≤ B/8` of `IsCoarseSetting` alone does not give. -/

/-- **The coarse drift fields with the smallness of the drift scale.** -/
theorem coarse_drift_small (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (B₀ C₁ : ℝ), 128 ≤ Λ₀ ∧ 1 ≤ B₀ ∧ 0 ≤ C₁ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M' → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∃ a lam : ℝ, 0 ≤ a ∧ 0 < lam ∧
        B₀ * Real.sqrt (B * ocTauPP α q Λ m) / lam ≤ 1 / 2 ∧
        a * B₀ * Real.sqrt (B * ocTauPP α q Λ m) ^ 2 ≤ B / 8 ∧
        a * B₀ * Real.sqrt (B * ocTauPP α q Λ m) ^ 2 ≤
          C₁ * B * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
        (∀ l : ℕ, 1 ≤ l → ∀ (t : ℝ) (x : Vec 2),
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ (m - 1)) t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) ∧
        (∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) t)) ∧
        (∀ (t : ℝ) (x : Vec 2),
          ∑ k : Fin 2, fderiv ℝ (streamVel (Φ (m - 1)) t) x (basisVec k) k = 0) ∧
        (∀ t : ℝ, AVenhance.IsZ2Periodic (streamVel (Φ (m - 1)) t)) ∧
        (∀ t₀ t₁ : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖streamVel (Φ (m - 1)) t x‖ ≤ C) ∧
        (∀ t₀ t₁ : ℝ,
          Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => streamVel (Φ (m - 1)) p.1 p.2) := by
  obtain ⟨C₀, hC₀, Λ₁, hΛ₁, hled⟩ :=
    AVRegularity.CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ : 0 < ocGamma α q := hexp.1
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hc : 0 < ocGamma α q / 2 + ocDelta α q := by linarith
  have h2δ : 0 < 2 * ocDelta α q := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hM : 0 ≤ 2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ := by positivity
  refine ⟨max Λ₁ (max ⌈(2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊
      ⌈(2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^ (1 / (2 * ocDelta α q))⌉₊),
    2 ^ 11, 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * C₀, hΛ₁.trans (le_max_left _ _),
    by norm_num, by positivity, ?_⟩
  intro Λ hΛ Φ hΦ M' κ hband m hm2 hmM ν B hν hB
  have hΛ₁' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ₂ : ⌈(2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊ ≤ Λ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛ₃ : ⌈(2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^
      (1 / (2 * ocDelta α q))⌉₊ ≤ Λ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ₁'
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast (show 0 < Λ by omega)
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
    AVRegularity.CycleReference.epsilon_le_inv_separation (m := m - 1) hq.1 h128 (by omega)
  have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
  have hBpos : 0 < B := by
    rw [← hB]
    exact AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband (show m - 1 ≤ M' by omega)
  obtain ⟨_, _, _, _, hRh, _, _, _, _, _, _, _, hAτ, _⟩ :=
    (hled Λ hΛ₁' M' (by omega) κ hband).2 m hm2 hmM ν B hν hB
  unfold ocRh at hRh
  unfold ocC at hRh
  have hrad : 2 ^ 12 * Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1) := by
    refine le_of_powerLaw_of_small hE (by positivity : (0 : ℝ) < 2 ^ 12 * C₀) hc hΛpos hEΛ
      ((Nat.le_ceil ((2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q)))).trans
        (Nat.cast_le.2 hΛ₂)) ?_
    calc 2 ^ 12 * Real.sqrt (B * ocTauPP α q Λ m)
        ≤ 2 ^ 12 * (C₀ * ocEpsilon q Λ (m - 1) ^ (1 + (ocGamma α q / 2 + ocDelta α q))) :=
          mul_le_mul_of_nonneg_left hRh.2 (by norm_num)
      _ = 2 ^ 12 * C₀ * ocEpsilon q Λ (m - 1) ^ (1 + (ocGamma α q / 2 + ocDelta α q)) :=
          (mul_assoc _ _ _).symm
  have hsmall : 2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ *
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ≤ 1 :=
    mul_rpow_le_one_of_small hE h2δ hΛpos hEΛ hM
      ((Nat.le_ceil ((2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^
        (1 / (2 * ocDelta α q)))).trans (Nat.cast_le.2 hΛ₃))
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact (Real.rpow_pos_of_pos hE _).le
  have hadm : IsAdmissibleStream (Φ (m - 1)) :=
    AVRegularity.Velocity.streamSeq_admissible hζ h128 hΦ (m - 1)
  have hsl : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) r) := fun r =>
    hadm.1.comp (contDiff_const.prodMk contDiff_id)
  have hvs : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) r) := fun r =>
    AVRegularity.Applications.streamVel_slice_smooth α q ζ hζ Λ h128 Φ hΦ (m - 1) r
  obtain ⟨_, _, hreg⟩ :=
    AVRegularity.Velocity.stream_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
  refine ⟨2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * ocA α q Λ (m - 1),
    ocEpsilon q Λ (m - 1), by positivity, hE, ?_, ?_, ?_, ?_, hvs, ?_, ?_, ?_, ?_⟩
  · -- `B₀ R / λ ≤ 1/2`
    rw [div_le_iff₀ hE]
    linarith
  · -- `a B₀ R² ≤ B/8`
    calc 2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * ocA α q Λ (m - 1) * 2 ^ 11 *
          Real.sqrt (B * ocTauPP α q Λ m) ^ 2
        = 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by
          rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le)]
          ring
      _ ≤ 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (C₀ * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) :=
          mul_le_mul_of_nonneg_left hAτ (by positivity)
      _ = B / 8 * (2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ *
            ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) := by ring
      _ ≤ B / 8 * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = B / 8 := mul_one _
  · -- `a B₀ R² ≤ C₁ B E^{2δ}`
    calc 2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * ocA α q Λ (m - 1) * 2 ^ 11 *
          Real.sqrt (B * ocTauPP α q Λ m) ^ 2
        = 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by
          rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le)]
          ring
      _ ≤ 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (C₀ * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) :=
          mul_le_mul_of_nonneg_left hAτ (by positivity)
      _ = 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ * B *
            ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := by ring
  · -- the analytic jets
    intro l hl t x
    exact streamVel_driftJet_le (φ := Φ (m - 1)) (t := t) (hsl t) (hvs t) hE hA0 hl
      ((hreg (m - 1) (by omega) t).2.1 (l + 1) (by omega)) x
  · -- incompressibility
    intro t x
    have h := AVRegularity.Applications.streamVel_classical_div hsl t x
    unfold AVRegularity.Applications.pd at h
    rw [AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 0 0,
      AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 1 1] at h
    rw [Fin.sum_univ_two]
    exact h
  · -- periodicity
    intro t
    exact AVRegularity.Velocity.streamSeq_velocity_spatial_periodic hζ h128 hΦ (m - 1) t
  · -- boundedness
    intro _ _
    exact ⟨AVRegularity.Applications.velBound α q Λ, fun t _ x =>
      AVRegularity.Applications.streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
        (m - 1) t x⟩
  · -- joint measurability
    intro _ _
    exact hadm.vel_continuous.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Pointwise-in-time limits of carrier families**. The mass-weighted factorial norm of the
limit of carrier families is bounded by every uniform bound of those of the approximating
families (`massNormSq_le_of_tendsto`). It is used to obtain the residual `(R, q)` of the
reconstruction from the residuals of the Galerkin approximants. -/

section Single

end Single

section Family

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)]

/-- **The mass-weighted factorial norm passes to the limit.** -/
theorem massNormSq_le_of_tendsto (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (G : ℕ → ∀ i, TorusHk (K i) (E i)) (L : ∀ i, TorusHk (K i) (E i))
    (hL : ∀ i, Tendsto (fun n => G n i) atTop (𝓝 (L i))) {b : ℝ}
    (hb : ∀ n, massNormSq ρ π (fun i => (G n i).val) ≤ b) :
    massNormSq ρ π (fun i => (L i).val) ≤ b := by
  have hT : Tendsto G atTop (𝓝 L) := tendsto_pi_nhds.2 hL
  have hc := ((massWeightedCarrierCLM (E := E) K ρ π).continuous.tendsto L).comp hT
  have hn := hc.norm.pow 2
  simp only [Function.comp_def, massWeightedCarrierCLM_normSq K ρ π hπ] at hn
  exact le_of_tendsto' hn hb

end Family

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Limits of the residual families of the Galerkin approximants**. A family
`G n s` of torus Sobolev carrier families, a.e. strongly measurable in time on a window `I` of
finite measure, Cauchy at every time of `I`, with mass-weighted factorial norms bounded by an
integrable `b` uniformly in `n`, converges at every time of `I` to a family `L` that is a.e.
strongly measurable, square integrable in time, with mass-weighted norms bounded by `b`; and the
distances `‖G n s - L s‖` are bounded by functions `c n` integrable on `I` with `∫_I c n → 0`
(dominated convergence) (`exists_residual_limit`). This is how the residual `(R, q)` of the
physical reconstruction is obtained from the residuals of the Galerkin approximants, in the form
consumed by `isCoupledWeakSolutionTorus_of_approximants`. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)]

/-- The carrier norm of one component is controlled by the mass-weighted factorial norm. -/
theorem norm_sq_le_massNormSq (K : ι → ℕ) {ρ : ℝ} (hρ : 0 < ρ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (D : ∀ i, TorusHk (K i) (E i)) (i : ι) :
    ‖D i‖ ^ 2 ≤ π i / factorialWeightMin ρ (K i) * massNormSq ρ π (fun i => (D i).val) := by
  have hw := factorialWeightMin_pos (K := K i) ρ hρ
  have hlow := factorialNormSq_lower ρ (D i).val
  have hle : (π i)⁻¹ * factorialNormSq ρ (D i).val ≤ massNormSq ρ π (fun i => (D i).val) := by
    unfold massNormSq
    exact Finset.single_le_sum (f := fun j => (π j)⁻¹ * factorialNormSq ρ (D j).val)
      (fun j _ => mul_nonneg (inv_nonneg.2 (hπ j).le) (factorialNormSq_nonneg ρ _))
      (Finset.mem_univ i)
  have hn : ‖D i‖ = ‖(D i).val‖ := rfl
  rw [hn]
  calc ‖(D i).val‖ ^ 2 = π i / factorialWeightMin ρ (K i) *
        ((π i)⁻¹ * (factorialWeightMin ρ (K i) * ‖(D i).val‖ ^ 2)) := by
        field_simp [(hπ i).ne', hw.ne']
    _ ≤ π i / factorialWeightMin ρ (K i) * ((π i)⁻¹ * factorialNormSq ρ (D i).val) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow (inv_nonneg.2 (hπ i).le))
          (div_nonneg (hπ i).le hw.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (div_nonneg (hπ i).le hw.le)

/-- The carrier norm of one component, by the square root of the mass-weighted norm. -/
theorem norm_le_sqrt_massNormSq (K : ι → ℕ) {ρ : ℝ} (hρ : 0 < ρ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (D : ∀ i, TorusHk (K i) (E i)) (i : ι) :
    ‖D i‖ ≤ Real.sqrt (π i / factorialWeightMin ρ (K i)) *
      Real.sqrt (massNormSq ρ π (fun i => (D i).val)) := by
  rw [← Real.sqrt_mul (div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le)]
  exact Real.le_sqrt_of_sq_le (norm_sq_le_massNormSq K hρ π hπ D i)

/-- **Limits of Cauchy residual families with a uniform integrable bound.** -/
theorem exists_residual_limit {I : Set ℝ} (hI : MeasurableSet I) (hIfin : volume I < ∞)
    (K : ι → ℕ) {ρ : ℝ} (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (G : ℕ → ℝ → ∀ i, TorusHk (K i) (E i))
    (hGm : ∀ n i, AEStronglyMeasurable (fun s => G n s i) (volume.restrict I))
    (hcauchy : ∀ s ∈ I, ∀ i, CauchySeq (fun n => G n s i))
    (b : ℝ → ℝ) (hb : IntegrableOn b I)
    (hGb : ∀ n, ∀ s ∈ I, massNormSq ρ π (fun i => (G n s i).val) ≤ b s) :
    ∃ L : ℝ → ∀ i, TorusHk (K i) (E i),
      (∀ s ∈ I, ∀ i, Tendsto (fun n => G n s i) atTop (𝓝 (L s i))) ∧
      (∀ i, AEStronglyMeasurable (fun s => L s i) (volume.restrict I)) ∧
      (∀ s ∈ I, massNormSq ρ π (fun i => (L s i).val) ≤ b s) ∧
      (∀ i, MemLp (fun s => L s i) 2 (volume.restrict I)) ∧
      ∃ c : ℕ → ℝ → ℝ, (∀ n, IntegrableOn (c n) I) ∧
        Tendsto (fun n => ∫ s in I, c n s) atTop (𝓝 0) ∧ (∀ n s, 0 ≤ c n s) ∧
        ∀ n, ∀ s ∈ I, ∀ i, ‖G n s i - L s i‖ ≤ c n s := by
  classical
  have hfin : IsFiniteMeasure (volume.restrict I) := ⟨by simpa using hIfin⟩
  set L : ℝ → ∀ i, TorusHk (K i) (E i) := fun s i => limUnder atTop (fun n => G n s i) with hL
  have hlim : ∀ s ∈ I, ∀ i, Tendsto (fun n => G n s i) atTop (𝓝 (L s i)) := fun s hs i =>
    (hcauchy s hs i).tendsto_limUnder
  have hLm : ∀ i, AEStronglyMeasurable (fun s => L s i) (volume.restrict I) := fun i =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hGm n i)
      ((ae_restrict_iff' hI).2 (Eventually.of_forall fun s hs => hlim s hs i))
  have hLb : ∀ s ∈ I, massNormSq ρ π (fun i => (L s i).val) ≤ b s := fun s hs =>
    massNormSq_le_of_tendsto K ρ π hπ (fun n => G n s) (L s) (hlim s hs) (fun n => hGb n s hs)
  -- the bound of the norms of the components
  set M : ι → ℝ := fun i => Real.sqrt (π i / factorialWeightMin ρ (K i)) with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => Real.sqrt_nonneg _
  have hb0 : ∀ s ∈ I, 0 ≤ b s := fun s hs =>
    (Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le)
      (factorialNormSq_nonneg ρ _)).trans (hGb 0 s hs)
  have hnG : ∀ n, ∀ s ∈ I, ∀ i, ‖G n s i‖ ≤ M i * Real.sqrt (b s) := fun n s hs i =>
    (norm_le_sqrt_massNormSq K hρ π hπ (G n s) i).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hGb n s hs)) (hM0 i))
  have hnL : ∀ s ∈ I, ∀ i, ‖L s i‖ ≤ M i * Real.sqrt (b s) := fun s hs i =>
    (norm_le_sqrt_massNormSq K hρ π hπ (L s) i).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hLb s hs)) (hM0 i))
  -- the square root of `b` is integrable on the window
  have hsb : IntegrableOn (fun s => Real.sqrt (b s)) I := by
    refine Integrable.mono' (hb.add (integrableOn_const (C := (1 : ℝ)) hIfin.ne)) ?_ ?_
    · exact (hb.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
    · refine (ae_restrict_iff' hI).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      show Real.sqrt (b s) ≤ b s + 1
      have h1 := hb0 s hs
      exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  refine ⟨L, hlim, hLm, hLb, fun i => ?_, ?_⟩
  · -- square integrability of the limit
    refine memLp_two_iff_integrable_sq_norm (hLm i) |>.2 ?_
    refine Integrable.mono' ((hb.const_mul (M i ^ 2))) ?_ ?_
    · exact ((hLm i).norm.aemeasurable.pow_const 2).aestronglyMeasurable
    · refine (ae_restrict_iff' hI).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖L s i‖ ^ 2 ≤ (M i * Real.sqrt (b s)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hnL s hs i) 2
        _ = M i ^ 2 * b s := by rw [mul_pow, Real.sq_sqrt (hb0 s hs)]
  · -- the distances
    set c : ℕ → ℝ → ℝ := fun n s => ∑ i, ‖G n s i - L s i‖ with hc
    have hcm : ∀ n, AEStronglyMeasurable (c n) (volume.restrict I) := fun n =>
      Finset.aestronglyMeasurable_fun_sum _ fun i _ => ((hGm n i).sub (hLm i)).norm
    have hcb : ∀ n, ∀ s ∈ I, ‖c n s‖ ≤ ∑ i, 2 * M i * Real.sqrt (b s) := fun n s hs => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ‖G n s i - L s i‖ ≤ ‖G n s i‖ + ‖L s i‖ := norm_sub_le _ _
        _ ≤ M i * Real.sqrt (b s) + M i * Real.sqrt (b s) := add_le_add (hnG n s hs i)
            (hnL s hs i)
        _ = 2 * M i * Real.sqrt (b s) := by ring
    have hdom : IntegrableOn (fun s => ∑ i, 2 * M i * Real.sqrt (b s)) I :=
      integrable_finsetSum _ fun i _ => hsb.const_mul (2 * M i)
    have hcint : ∀ n, IntegrableOn (c n) I := fun n =>
      Integrable.mono' hdom (hcm n) ((ae_restrict_iff' hI).2 (Eventually.of_forall (hcb n)))
    refine ⟨c, hcint, ?_, fun n s => Finset.sum_nonneg fun i _ => norm_nonneg _,
      fun n s hs i => ?_⟩
    · have h0 := tendsto_integral_of_dominated_convergence (μ := volume.restrict I)
        (fun s => ∑ i, 2 * M i * Real.sqrt (b s)) hcm hdom
        (fun n => (ae_restrict_iff' hI).2 (Eventually.of_forall (hcb n)))
        ((ae_restrict_iff' hI).2 (Eventually.of_forall fun s hs => by
          have : Tendsto (fun n => c n s) atTop (𝓝 (∑ i : ι, (0 : ℝ))) :=
            tendsto_finsetSum _ fun i _ => by
              simpa [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.1 (hlim s hs i))
          simpa using this))
      simpa using h0
    · exact Finset.single_le_sum (f := fun i => ‖G n s i - L s i‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Facts about the lift data of one pulse**.

The generic per-pulse lemmas (`labels_chart_prim`, `setting_pulse_tested`,
`labelDensity_physical`) take abstract hypotheses on the lift data `Q`. Here they are discharged
for `Q = pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge`, in the chart
`χ t = ocChart α q Λ m φ hφ l t`, `l = ocPulseChartIndex α q Λ m k`, with the time scale
`c = ℓ²` (`ℓ = ocEll q Λ m ν`), the slow scale `ρ`, the fast scale `e = ocEpsilon q Λ m`, the
diffusivity `ν` and the expansion parameter `ε_c = d_*/ρ` (`d_* = ocDStar q Λ m ν B`):

* `pulse_G_chart`: `G(c⁻¹t, ρ⁻¹y) = Dχ_t(y)⁻¹ Dχ_t(y)⁻ᵀ` (for `ℓ ≠ 0`, `ρ ≠ 0`);
* `pulse_G_differentiable`: the metric is differentiable in the slow variable;
* `pulse_v_factor`: `v = (ℓ²/e) w` with the unit drift `w = pulseCellDriftUnit`
  (`w(s,z) = p_k(ℓ²s) 𝐮_{m,k}(ez)`); `pulse_scale_h1`, `pulse_scale_h2`, `pulse_scale_h3`: the
  scale identities `ℓ²ν e⁻² = 1`, `ε_c √η = ℓ²ν e⁻¹ρ⁻¹`, `ε_c² η = ℓ²ν ρ⁻²` (`ν, B > 0`, `e ≠ 0`);
* `pulse_drift_physical`: at a time at which no other pulse is active, the pushed-forward unit
  drift is the velocity increment `b_m - b_{m-1}`;
* `pulse_G_slow_invariant`, `pulse_edge_slow_invariant`: slow `ρ⁻¹ℤ²`-periodicity of the metric and
  of the lifted source coefficients (the latter for `lam = ρ/E` and a torus-compatible family);
* `pulse_e_inv_nat`: `e⁻¹` is a natural number. -/

/-! ### Scales -/

/-- `ℓ = e/√ν ≠ 0` for `e ≠ 0` and `ν > 0`. -/
theorem ocEll_ne_zero_of {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hν : 0 < ν) (he : ocEpsilon q Λ m ≠ 0) :
    ocEll q Λ m ν ≠ 0 :=
  div_ne_zero he (Real.sqrt_ne_zero'.mpr hν)

/-- `e = ε_m ≠ 0` for `Λ ≥ 1`. -/
theorem ocEpsilon_ne_zero_of {q : ℝ} {Λ : ℕ} (m : ℕ) (hΛ : 1 ≤ Λ) : ocEpsilon q Λ m ≠ 0 :=
  (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ).ne'

/-- `ℓ²ν = e²` for `ν > 0`. -/
theorem ocEll_sq_mul {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hν : 0 < ν) :
    ocEll q Λ m ν ^ 2 * ν = ocEpsilon q Λ m ^ 2 := by
  rw [ocEll, div_pow, Real.sq_sqrt hν.le, div_mul_cancel₀ _ hν.ne']

/-- **Scale identity `h1`**: `ℓ²ν e⁻¹e⁻¹ = 1`. -/
theorem pulse_scale_h1 {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hν : 0 < ν) (he : ocEpsilon q Λ m ≠ 0) :
    ocEll q Λ m ν ^ 2 * ν * (ocEpsilon q Λ m)⁻¹ * (ocEpsilon q Λ m)⁻¹ = 1 := by
  have hb : ocEpsilon q Λ m * (ocEpsilon q Λ m)⁻¹ = 1 := mul_inv_cancel₀ he
  rw [ocEll_sq_mul hν]
  linear_combination (ocEpsilon q Λ m * (ocEpsilon q Λ m)⁻¹ + 1) * hb

/-- `√(B/ν) √(ν/B) = 1`. -/
theorem pulse_sqrt_div_mul_sqrt_div {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) :
    Real.sqrt (B / ν) * Real.sqrt (ν / B) = 1 := by
  rw [← Real.sqrt_mul (div_nonneg hB.le hν.le), div_mul_div_comm, mul_comm B ν,
    div_self (mul_ne_zero hν.ne' hB.ne'), Real.sqrt_one]

/-- `(B/ν)(ν/B) = 1`. -/
theorem pulse_div_mul_div_self {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) : B / ν * (ν / B) = 1 := by
  rw [div_mul_div_comm, mul_comm B ν, div_self (mul_ne_zero hν.ne' hB.ne')]

section Data

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

/-- **Scale identity `h2`**: `ε_c √η = ℓ²ν e⁻¹ρ⁻¹` for `ε_c = d_*/ρ`, `η = ν/B`. -/
theorem pulse_scale_h2 (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (he : ocEpsilon q Λ m ≠ 0) (ρ lam : ℝ) (k : ℤ) (edge : ConstituentEdges D h) :
    ocDStar q Λ m ν B / ρ * Real.sqrt (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).η =
      ocEll q Λ m ν ^ 2 * ν * (ocEpsilon q Λ m)⁻¹ * ρ⁻¹ := by
  have hb : ocEpsilon q Λ m * (ocEpsilon q Λ m)⁻¹ = 1 := mul_inv_cancel₀ he
  have hs := pulse_sqrt_div_mul_sqrt_div hν hB
  show ocDStar q Λ m ν B / ρ * Real.sqrt (ν / B) = _
  rw [ocEll_sq_mul hν, ocDStar]
  linear_combination (ocEpsilon q Λ m * ρ⁻¹) * hs - (ocEpsilon q Λ m * ρ⁻¹) * hb

/-- **Scale identity `h3`**: `ε_c² η = ℓ²ν ρ⁻¹ρ⁻¹` for `ε_c = d_*/ρ`, `η = ν/B`. -/
theorem pulse_scale_h3 (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (ρ lam : ℝ) (k : ℤ)
    (edge : ConstituentEdges D h) :
    (ocDStar q Λ m ν B / ρ) ^ 2 * (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).η =
      ocEll q Λ m ν ^ 2 * ν * ρ⁻¹ * ρ⁻¹ := by
  have hd := pulse_div_mul_div_self hν hB
  show (ocDStar q Λ m ν B / ρ) ^ 2 * (ν / B) = _
  rw [ocEll_sq_mul hν, ocDStar, div_pow, mul_pow, Real.sq_sqrt (div_nonneg hB.le hν.le)]
  linear_combination (ocEpsilon q Λ m ^ 2 * ρ⁻¹ * ρ⁻¹) * hd

/-! ### The metric -/

/-- **The metric of the lift in the chart** (`hGχ` of `labelDensity_physical`): with `c = ℓ²`,
`G(c⁻¹t, ρ⁻¹y) = Dχ_t(y)⁻¹ Dχ_t(y)⁻ᵀ` for the chart `χ_t` of the pulse. -/
theorem pulse_G_chart (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (lam : ℝ) (k : ℤ)
    (edge : ConstituentEdges D h) (hℓ : ocEll q Λ m ν ≠ 0) (t : ℝ) (y : Vec 2) :
    (fun i j => (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G
        ((ocEll q Λ m ν ^ 2)⁻¹ * t) (ρ⁻¹ • y) i j) =
      (jacMatrix (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t) y)⁻¹ *
        ((jacMatrix (ocChart α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) t) y)⁻¹)ᵀ := by
  have ht : ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t) = t :=
    mul_inv_cancel_left₀ (pow_ne_zero 2 hℓ) t
  have hy : ρ • ρ⁻¹ • y = y := by rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
  ext i j
  show ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)
      (ocEll q Λ m ν ^ 2 * ((ocEll q Λ m ν ^ 2)⁻¹ * t)) (ρ • ρ⁻¹ • y) i j = _
  rw [ht, hy]
  rfl

/-- **The metric of the lift is differentiable in the slow variable** (`hG`). -/
theorem pulse_G_differentiable (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B ρ lam : ℝ) (k : ℤ) (edge : ConstituentEdges D h) :
    ∀ s i j, Differentiable ℝ
      (fun X => (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G s X i j) := by
  intro s i j
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k) p.1 p.2 i j) :=
    AVRegularity.CycleWords.ocMaterialMetric_joint_contDiff α q Λ m hφ
      (ocPulseChartIndex α q Λ m k) i j
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 => ((ocEll q Λ m ν ^ 2 * s, ρ • X) : ℝ × Vec 2)) := by fun_prop
  show Differentiable ℝ (fun X => ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)
    (ocEll q Λ m ν ^ 2 * s) (ρ • X) i j)
  exact (h1.comp h2).differentiable (by simp)

/-- **Slow periodicity of the metric** (`hGs`), for `ρ ≠ 0`. -/
theorem pulse_G_slow_invariant (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (lam : ℝ) (k : ℤ)
    (edge : ConstituentEdges D h) :
    ∀ (n : Fin 2 → ℤ) t X i j,
      (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G t (X + ρ⁻¹ • latticeShift n) i j =
        (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).G t X i j :=
  fun n t X i j =>
    AVRegularity.CycleComparison.Assembly.pulseLiftData_G_shift α q Λ m ζ hφ ν B hρ lam k edge
      n t X i j

/-! ### The drift -/

/-- The unit cell drift of the pulse `k`: `w(s, z) = p_k(ℓ²s) 𝐮_{m,k}(e z)`, so that
`ocPulseCellDrift = (ℓ²/e) w`. -/
def pulseCellDriftUnit (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (k : ℤ) :
    ℝ → Vec 2 → Vec 2 :=
  fun s z => ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) •
    ocShearVel α q Λ m k (ocEpsilon q Λ m • z)

/-- **The drift of the lift is `c₁ = ℓ² e⁻¹` times the unit drift** (`hv`, `hc₁ : c₁ = c e⁻¹`). -/
theorem pulse_v_factor (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B ρ lam : ℝ) (k : ℤ) (edge : ConstituentEdges D h) :
    ∀ s z, (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam k edge).v s z =
      (ocEll q Λ m ν ^ 2 * (ocEpsilon q Λ m)⁻¹) • pulseCellDriftUnit α q Λ ζ m ν k s z := by
  intro s z
  show (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) •
        ocShearVel α q Λ m k (ocEpsilon q Λ m • z)) = _
  rw [div_eq_mul_inv]
  rfl

end Data

/-- The pulse stream at a time at which no pulse other than the odd pulse `k` is active. -/
theorem pulseStreamVel_eq_of_isolated {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {k : ℤ} (hk : Odd k)
    {t : ℝ} (hiso : ∀ k' : ℤ, Odd k' → k' ≠ k → ocPulse α q Λ ζ m k' t = 0) (y : Vec 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y =
      ocPulse α q Λ ζ m k t • ocShearVel α q Λ m k y := by
  have hstream : ocPulseStream α q Λ ζ m t = fun y =>
      ocPulse α q Λ ζ m k t * ocShear α q Λ m k y := by
    funext y'
    unfold ocPulseStream
    refine tsum_eq_single (⟨k, hk⟩ : {k : ℤ // Odd k}) fun b hb => ?_
    have hbk : b.1 ≠ k := fun hb' => hb (Subtype.ext hb')
    rw [hiso b.1 b.2 hbk, zero_mul]
  simp only [ocShearVel, streamVel]
  rw [hstream]
  have hgrad : spaceGrad (fun y => ocPulse α q Λ ζ m k t * ocShear α q Λ m k y) y =
      ocPulse α q Λ ζ m k t • spaceGrad (ocShear α q Λ m k) y := by
    ext i
    unfold spaceGrad
    rw [fderiv_const_mul
      ((AVRegularity.CycleReference.ocShear_contDiff α q Λ m k).differentiable (by simp) y)]
    simp
  rw [hgrad, Matrix.mulVec_smul]

/-- **The physical drift of an isolated pulse** (`hwb` of `labelDensity_physical`). If at time
`t` no pulse other than the odd pulse `k` is active and `l` is the label of `k`, the unit drift
at the labels, pushed forward by the chart `χ_t = ocChart … l t`, is the velocity increment:
`Dχ_t(ψ_t x) w(c⁻¹t, e⁻¹ψ_t x) = b_m(t,x) - b_{m-1}(t,x)`, `c = ℓ²`. -/
theorem pulse_drift_physical {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (ν : ℝ) {k l : ℤ} (hk : Odd k) (hkl : ocLabel α q Λ m k = l)
    (he : ocEpsilon q Λ m ≠ 0) (hℓ : ocEll q Λ m ν ≠ 0) {t : ℝ}
    (hiso : ∀ k' : ℤ, Odd k' → k' ≠ k → ocPulse α q Λ ζ m k' t = 0) (x : Vec 2) :
    (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t)
        (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)).mulVec
      (pulseCellDriftUnit α q Λ ζ m ν k ((ocEll q Λ m ν ^ 2)⁻¹ * t)
        ((ocEpsilon q Λ m)⁻¹ • ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)) =
      streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x := by
  obtain ⟨hΨ', -⟩ := hseq.2 (m + 1) (by omega)
  have hΨ : IsAdmissibleStream (Φ m) := hΨ'
  have hw : pulseCellDriftUnit α q Λ ζ m ν k ((ocEll q Λ m ν ^ 2)⁻¹ * t)
      ((ocEpsilon q Λ m)⁻¹ • ocChartInv α q Λ m (Φ (m - 1)) hφ l t x) =
      ocPulse α q Λ ζ m k t •
        ocShearVel α q Λ m k (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x) := by
    simp only [pulseCellDriftUnit]
    rw [mul_inv_cancel_left₀ (pow_ne_zero 2 hℓ), smul_smul, mul_inv_cancel₀ he, one_smul]
  have hfun : AVRegularity.CycleReference.chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m)
      (Φ m) t = ocPulseStream α q Λ ζ m t :=
    funext fun y => chartStreamIncrement_eq_ocPulseStream_of_isolated hseq hm hφ k l hkl t hiso y
  have hinc : streamVel (AVRegularity.CycleReference.chartStreamIncrement hφ
      ((l : ℝ) * ocTauPP α q Λ m) (Φ m)) t (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x) =
      ocPulse α q Λ ζ m k t •
        ocShearVel α q Λ m k (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x) := by
    rw [← pulseStreamVel_eq_of_isolated hk hiso (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)]
    unfold streamVel
    rw [hfun]
  have hvel := AVRegularity.CycleReference.chartStreamIncrement_velocity hφ hΨ
    ((l : ℝ) * ocTauPP α q Λ m) t (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)
  have hX : AVRegularity.streamFlow (Φ (m - 1)) hφ t (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)
      ((l : ℝ) * ocTauPP α q Λ m) = x :=
    AVRegularity.CycleComparison.Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ l t x
  have hdet : IsUnit (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t)
      (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)).det := by
    rw [AVRegularity.CycleComparison.Charts.ocChart_det hφ α q Λ m l t
      (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)]
    exact isUnit_one
  rw [hw, ← hinc, hvel, hX, Matrix.mulVec_mulVec]
  show ((jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t)
      (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x)) *
      (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t)
        (ocChartInv α q Λ m (Φ (m - 1)) hφ l t x))⁻¹).mulVec _ = _
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-! ### The sources and the fast scale -/

section Family

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **Slow periodicity of the lifted source coefficients** (`hcs`), for `lam = ρ/E`, `ρ ≠ 0` and
a family torus compatible at the slow scale `E` (only the periodicity of the fluxes,
`htorus.2`, is used). -/
theorem pulse_edge_slow_invariant (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (ν B : ℝ) {ρ E : ℝ} (hρ : ρ ≠ 0) (k : ℤ)
    {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p}
    (htorus : IsTorusCompatible F actual E) (p : P) :
    ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ φ hφ ν B ρ (ρ / E) k (F.fiber p (actual p))).edge v u d,
        ∀ w t X z, γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z :=
  fun n _ _ _ _ hγ w t X z =>
    AVRegularity.CycleComparison.Assembly.liftEdges_fiber_coeff_shift hρ htorus
      (ocEll q Λ m ν ^ 2) p n hγ w t X z

end Family

/-- **`e⁻¹` is a natural number** (`hM`). -/
theorem pulse_e_inv_nat (q : ℝ) (Λ m : ℕ) : ∃ M : ℕ, (ocEpsilon q Λ m)⁻¹ = M := by
  by_cases hm : m = 0
  · exact ⟨1, by simp [ocEpsilon, hm]⟩
  · exact ⟨⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊, by simp [ocEpsilon, hm]⟩

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Convergence of the finite-rank approximants.** Contracting projections converging strongly
converge uniformly on compact sets; hence the Galerkin cutoffs of a continuous trajectory
`t ↦ W(t) ∈ H^K(𝕋²)` converge uniformly on a compact time set, and (by the quantitative embedding
`H^{r+2}(𝕋²) ⊂ C^r`, `classicalRep_orderedDerivative_sub_le`) the ordered derivatives of order
`≤ r` of the finite-rank approximants `a_n(t, ·)` converge to those of the classical representative
of `W(t)`, uniformly in `t` and in space. This is the passage `n → ∞` of the finite-rank coarse
fields. -/

/-- **Contracting projections converging strongly converge uniformly on compact sets.** -/
theorem contracting_eventually_uniform {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ℕ → X →L[ℝ] X) (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) {S : Set X} (hS : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ x ∈ S, ‖P n x - x‖ < ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T, hT, hST⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded (ε / 3) hε3
  have hev : ∀ᶠ n in atTop, ∀ y ∈ T, ‖P n y - y‖ < ε / 3 := by
    refine (Filter.eventually_all_finite hT).2 fun y _ => ?_
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hlim y) (ε / 3) hε3
    refine Filter.eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
    have hd := hN₀ n hn
    rwa [dist_eq_norm] at hd
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hST hx)
  have hxy' : ‖x - y‖ < ε / 3 := by
    rw [Metric.mem_ball, dist_eq_norm] at hxy
    exact hxy
  have h1 : ‖P n (x - y)‖ ≤ ‖x - y‖ := hP n (x - y)
  have h2 : ‖P n y - y‖ < ε / 3 := hn y hyT
  have key : P n x - x = P n (x - y) + (P n y - y) - (x - y) := by
    rw [map_sub]
    abel
  calc ‖P n x - x‖ = ‖P n (x - y) + (P n y - y) - (x - y)‖ := by rw [key]
    _ ≤ ‖P n (x - y) + (P n y - y)‖ + ‖x - y‖ := norm_sub_le _ _
    _ ≤ ‖P n (x - y)‖ + ‖P n y - y‖ + ‖x - y‖ := by linarith [norm_add_le (P n (x - y)) (P n y - y)]
    _ < ε := by linarith

/-- **Galerkin cutoffs of a continuous trajectory converge uniformly on a compact time set.** -/
theorem galerkinProj_eventually_uniform {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] {K : ℕ} {I : Set ℝ} (hI : IsCompact I) {V : ℝ → TorusHk K E}
    (hV : ContinuousOn V I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ I, ‖galerkinProj n (V t) - V t‖ < ε := by
  filter_upwards [contracting_eventually_uniform (fun n => galerkinProj (E := E) (K := K) n)
    (fun n u => galerkinProj_norm_le n u) galerkinProj_tendsto (hI.image_of_continuousOn hV)
    hε] with n hn t ht
  exact hn (V t) (Set.mem_image_of_mem V ht)

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The strong energies of the Galerkin approximants**. The classical strong
energy of the approximants `a_n = S_n W` at the order `m` is at most the strong energy of `W` at
the same order (`classicalStrongEnergy_coarseTraj_le`): the approximants are classical
representatives of the Galerkin cutoffs, whose factorial norms are contracted. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The classical strong energy of the approximants is at most the strong energy of `W`.** -/
theorem classicalStrongEnergy_coarseTraj_le {K m : ℕ} (hmK : m + 1 ≤ K) (ρ B : ℝ) (π : ι → ℝ)
    (t₀ t₁ : ℝ) (n : ℕ) (W : ∀ v, ℝ → TorusHk K (h v)) :
    classicalStrongEnergy ρ B π (Set.Icc t₀ t₁) m (coarseTraj n W) ≤
      strongEnergyUpTo ρ B π t₀ t₁ m W := by
  have hrep : ∀ t v, IsClassicalRep (galerkinProj n (W v t))
      (fun x => coarseTraj n W t x v) (m + 1) := fun t v => by
    rw [coarseTraj_eq]
    exact coarseApprox_isClassicalRep n (fun u => W u t) v hmK
  unfold classicalStrongEnergy strongEnergyUpTo
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => ?_) (by norm_num)
  refine mul_le_mul_right (add_le_add (iSup₂_mono fun t _ => ?_) (mul_le_mul_right
    (lintegral_mono fun t => ?_) _)) _
  · rw [classicalFactorialSq_eq_of_rep (hrep t v) ρ (Nat.le_succ m)]
    exact ENNReal.ofReal_le_ofReal (factorialNormSqUpTo_galerkinProj_le n ρ m (W v t))
  · rw [classicalGradFactorialSq_eq_of_rep (hrep t v) ρ le_rfl]
    exact ENNReal.ofReal_le_ofReal (gradFactorialNormSqUpTo_galerkinProj_le n ρ m (W v t))

section Order

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure (Vec 2)} {K : ℕ}

/-- The truncated factorial norm is monotone in the order. -/
theorem factorialNormSqUpTo_mono_order (ρ : ℝ) {m m' : ℕ} (hmm : m ≤ m') (X : JetL2 μ K E) :
    factorialNormSqUpTo ρ m X ≤ factorialNormSqUpTo ρ m' X := by
  unfold factorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 : 0 ≤ factorialWeight ρ j.val * derivativeNormSq X j :=
    mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hmm) h2
  · exact h0
  · exact le_rfl

/-- The truncated gradient factorial norm is monotone in the order. -/
theorem gradFactorialNormSqUpTo_mono_order (ρ : ℝ) {m m' : ℕ} (hmm : m ≤ m') (X : JetL2 μ K E) :
    gradFactorialNormSqUpTo ρ m X ≤ gradFactorialNormSqUpTo ρ m' X := by
  unfold gradFactorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  have h0 : 0 ≤ factorialWeight ρ (j.val - 1) * derivativeNormSq X j :=
    mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.trans (by omega)⟩ h2
  · exact h0
  · exact le_rfl

end Order

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The strong energy is monotone in the order.** -/
theorem strongEnergyUpTo_mono_order {K m m' : ℕ} (hmm : m ≤ m') (ρ B : ℝ)
    (π : ι → ℝ) (t₀ t₁ : ℝ) (W : ∀ v, ℝ → TorusHk K (h v)) :
    strongEnergyUpTo ρ B π t₀ t₁ m W ≤ strongEnergyUpTo ρ B π t₀ t₁ m' W := by
  unfold strongEnergyUpTo
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => ?_) (by norm_num)
  refine mul_le_mul_right (add_le_add (iSup₂_mono fun t _ => ?_) (mul_le_mul_right
    (lintegral_mono fun t => ?_) _)) _
  · exact ENNReal.ofReal_le_ofReal (factorialNormSqUpTo_mono_order ρ hmm _)
  · exact ENNReal.ofReal_le_ofReal (gradFactorialNormSqUpTo_mono_order ρ hmm _)

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The source data of a lift sequence** (the cell inverse of the centered source). The ambient
recurrence data of a lift sequence (`setting_ambient_scalar_power_ recurrence_data`: coefficient and
uncentered data of every grade and degree), the `z`-periodicity of its coefficients and their cell
means zero give the source data of every positive degree, as for the constructed sequence
(`setting_constructed_source_data_of_predecessors`). With them the coefficient sources, hence the
time densities of the coefficients, are bounded and measurable in time on the window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The source data of every positive degree of a lift sequence.** -/
theorem setting_liftSequence_source_data (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    AmbientLiftSourceData par a b P.window lam hh n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q Cc
      (ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hnR : n ≤ N + D := by omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  let Budget := fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m
    CG Cw Cj
  let KM := fun h m => ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) h m CG Cw Cj Budget
  have hrec (h' : ℕ) (hh' : h' ≤ H) (m : ℕ) (hm : m ≤ N + D) :=
    setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve h' hh' m hm
  have uncentered := (hrec hh hhh n hnR).uncentered hn
  have hcoef j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftCoefficientData par a b P.window lam j p q (Cc ab.1 j)
        (fun v u => Budget ab.1 j * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.1 v u) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    exact ((hrec ab.1 (by omega) j (by omega)).coefficient).mono
      (ambientDegreeSlowReserve_mono P₀ (N + D) n j (by omega))
      (ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.1 n j (by omega) (by omega))
  have hmean j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftUncenteredData par a b P.window lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.2) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (hrec ab.2 (by omega) (n - j) (by omega)).uncentered (by omega)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n j hnR (by omega)
      change p + j ≤ _
      rw [← he]
    · exact ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.2 n (n - j)
        (by omega) (Nat.sub_le _ _)
  have source := ambient_ordered_centered_source_data_of_coefficients par a b P.window lam hlam
    hh n p q Q Cc
    (fun j hj ab hab' m _ α v u t ht X => by
      have hj' := Finset.mem_Icc.mp hj
      have hab'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
      exact (hseq.2.2.2.2.2.1 ab.1 (by omega) j m α v u t ht).2 X)
    (fun j hj ab hab' m hm α v u t ht X ξ => by
      have hj' := Finset.mem_Icc.mp hj
      have hab'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
      exact liftSequence_coefficient_applied_mean_zero Q sX sZ a b N H Cc hseq ab.1 j m
        (by omega) hj'.1 (by omega) hm α t ht X v u ξ)
    (physicalEdgeEnvelopeMatrix π edge)
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) Budget
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _) (KM hh n) KM
    uncentered hcoef hmean
  dsimp only [p, q, Budget, KM] at source
  rw [orderedCenteredScalarConstant_eq_ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D)
    hh n hnR CG Cw Cj] at source
  exact source

end AVRegularity.CycleComparison.Reconstruction
end
