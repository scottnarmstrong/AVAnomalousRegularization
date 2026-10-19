-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.OcData
public import AVRegularity.CycleComparison.Assembly.CoarseLetters
public import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleReference.SingleModeFlux
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.CycleReference.TransitionTaylorBounds
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleComparison.Diagonal.Main
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.CycleReference.CorrectorMeanGeometry
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! The construction facts of clause 4 of `cycle_comparison`:
* the pulses vanish at the quiet times and before their slots, so the zero-start memory of a
  pulse at the start of its lift window differs from the reference memory by the switching price
  `μ H_* M_k(T₀) ≤ C H_* ℓ²/τ`;
* the reference flux is bounded by `ν + H_*`;
* the metric of the lift data of a pulse deviates from the identity by `g_m λ_s^r` in the slow
  variable (`g_m = a_{m-1} τ_m''`);
* the scalar letters inherit the jet bounds of the diagonal chart-frame letters. -/

open AVRegularity.CycleComparison.ActualMeans

/-! ### Pulses at the quiet times and before their slots -/

/-- A pulse vanishes at a quiet time. -/
theorem ocPulse_eq_zero_of_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) {t : ℝ} (ht : t ∈ ocQuietTimes α q Λ ζ m) :
    ocPulse α q Λ ζ m k t = 0 := by
  by_contra hp
  have hq : ∀ y : Vec 2, streamVel (ocPulseStream α q Λ ζ m) t y = 0 := ht
  have h := hq 0
  rw [CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp 0] at h
  have hε : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hA : 0 < 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ := by positivity
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have h' := congrFun h 1
    rw [CycleReference.ocShearVel_horizontal h1, Pi.smul_apply, smul_eq_mul] at h'
    simp only [Matrix.cons_val_one, Pi.zero_apply, mul_zero, Real.cos_zero, mul_one] at h'
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact hp h0
    · exact hA.ne' h0
  · have h' := congrFun h 0
    rw [CycleReference.ocShearVel_vertical h3, Pi.smul_apply, smul_eq_mul] at h'
    simp only [Matrix.cons_val_zero, Pi.zero_apply, mul_zero, Real.cos_zero, mul_one] at h'
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact hp h0
    · exact hA.ne' (neg_eq_zero.1 h0)

/-- A pulse vanishes before `(k - 2/3) τ`. -/
theorem ocPulse_eq_zero_of_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {k : ℤ} {t : ℝ}
    (ht : t ≤ (k : ℝ) * ocTau α q Λ m - (2 / 3) * ocTau α q Λ m) :
    ocPulse α q Λ ζ m k t = 0 := by
  by_contra hp
  have h := (CycleReference.pulse_nonzero_center_distance hΛ hζ hp).1
  linarith

/-- The pulse vanishes at the start `max((k - 61/48)τ, t_p)` of its lift window when `t_p` is
quiet. -/
theorem ocPulse_obsStart_eq_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) {tp : ℝ} (htp : tp ∈ ocQuietTimes α q Λ ζ m) :
    ocPulse α q Λ ζ m k (max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp) = 0 := by
  rcases le_total (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp with h | h
  · rw [max_eq_right h]
    exact ocPulse_eq_zero_of_quiet hΛ hζ hk htp
  · rw [max_eq_left h]
    have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
    exact ocPulse_eq_zero_of_le hΛ hζ (by nlinarith)

/-! ### The switching price and the size of the reference flux -/

/-- `μ ℓ² = 4π²`. -/
theorem ocMu_mul_ocEll_sq {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocMu q Λ m ν * ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 := by
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  rw [CycleReference.ocEll_sq_eq hν, ocMu]
  field_simp

/-- **The switching price.** If the pulse vanishes at `T₀`, its memory there costs
`μ H_* M_k(T₀) ≤ K H_* ℓ²/τ`. -/
theorem switching_le {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Kζ : ℝ, 0 ≤ Kζ ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν → ∀ (k : ℤ) (T₀ : ℝ),
      ocPulse α q Λ ζ m k T₀ = 0 →
      ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulseMemory α q Λ ζ m ν k T₀ ≤
        Kζ * (ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m) := by
  obtain ⟨K, hK, herr⟩ := CycleReference.pulse_memory_instantaneous_error hζ
  refine ⟨K / (4 * Real.pi ^ 2), by positivity, ?_⟩
  intro α q Λ m hΛ ν hν k T₀ hp
  have hμ : 0 < ocMu q Λ m ν := CycleReference.ocMu_pos hΛ hν
  have hH : 0 < ocHStar α q Λ m ν := CycleReference.ocHStar_pos hΛ hν
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have h1 := herr α q Λ m hΛ ν hν k T₀
  rw [hp, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hμ.le
    (CycleReference.ocPulseMemory_range hΛ hζ ν hν k T₀).1)] at h1
  have hμℓ := ocMu_mul_ocEll_sq (q := q) (m := m) hΛ hν
  have hℓ0 : ocEll q Λ m ν ≠ 0 :=
    (div_pos (Construction.Stream.ocEpsilon_pos hΛ) (Real.sqrt_pos.2 hν)).ne'
  have e : ocHStar α q Λ m ν * (K / (ocMu q Λ m ν * ocTau α q Λ m)) =
      K / (4 * Real.pi ^ 2) * (ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m) := by
    rw [← hμℓ]
    field_simp
  calc ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulseMemory α q Λ ζ m ν k T₀
      = ocHStar α q Λ m ν * (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k T₀) := by ring
    _ ≤ ocHStar α q Λ m ν * (K / (ocMu q Λ m ν * ocTau α q Λ m)) :=
        mul_le_mul_of_nonneg_left h1 hH.le
    _ = _ := e

/-- The entries of the reference flux are at most `ν + H_*`. -/
theorem refFlux_entry_abs_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (t : ℝ) (a b : Fin 2) :
    |ocRefFlux α q Λ ζ m ν t a b| ≤ ν + ocHStar α q Λ m ν := by
  have hH : 0 < ocHStar α q Λ m ν := CycleReference.ocHStar_pos hΛ hν
  have hone : |(1 : Matrix (Fin 2) (Fin 2) ℝ) a b| ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rcases CycleReference.refFlux_shape (α := α) (m := m) (ζ := ζ) (t := t) hΛ hζ hν with
    ⟨k, c, hflux, hc0, hc1⟩ | hquiet
  · rw [hflux, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    have hpi : |ocPi k a b| ≤ 1 := by
      unfold ocPi
      split_ifs <;> fin_cases a <;> fin_cases b <;> simp
    calc |ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) a b + c * ocPi k a b|
        ≤ |ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) a b| + |c * ocPi k a b| := abs_add_le _ _
      _ = ν * |(1 : Matrix (Fin 2) (Fin 2) ℝ) a b| + c * |ocPi k a b| := by
          rw [abs_mul, abs_mul, abs_of_pos hν, abs_of_nonneg hc0]
      _ ≤ ν * 1 + ocHStar α q Λ m ν * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hone hν.le)
            (mul_le_mul hc1 hpi (abs_nonneg _) hH.le)
      _ = ν + ocHStar α q Λ m ν := by ring
  · rw [hquiet, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hν]
    calc ν * |(1 : Matrix (Fin 2) (Fin 2) ℝ) a b| ≤ ν * 1 := mul_le_mul_of_nonneg_left hone hν.le
      _ ≤ ν + ocHStar α q Λ m ν := by linarith

/-! ### The metric of a pulse in the slow variable -/

/-- **The metric deviation of the lift data of a pulse**: on cell times whose physical time is in
the anchor window of the chart, the slow jets of `G - I` are at most `C_r g_m λ_s^r`. -/
theorem pulseLiftData_metric_deviation {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B ρ lam : ℝ) (k : ℤ) (edge : ConstituentEdges D h)
    (hρ : 0 ≤ ρ) {t₀ t₁ : ℝ}
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, |ocEll q Λ m ν ^ 2 * t -
      (ocPulseChartIndex α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m) (r : ℕ) :
    (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2, ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
        (pulseLiftData (ι := ι) α q Λ m ζ (Φ (m - 1)) hφ ν B ρ lam k edge).G t X' i j -
          (if i = j then 1 else 0)) X‖ₑ) ≤
      ENNReal.ofReal (Charts.metricDevConst r * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) *
        (ρ / ocEpsilon q Λ (m - 1)) ^ r) := by
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos (by omega)
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos (by omega)
  have hg0 : 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := by
    have : 0 ≤ ocA α q Λ (m - 1) := by
      unfold ocA
      exact Real.rpow_nonneg hE.le _
    positivity
  have hC0 := Charts.metricDevConst_nonneg r
  refine iSup₂_le fun t ht => iSup_le fun X => ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  set l := ocPulseChartIndex α q Λ m k
  set T := ocEll q Λ m ν ^ 2 * t
  have hdev := Charts.ocMaterialMetric_deviation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ
    l T (hwin t ht) r
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun X' : Vec 2 => fun i j : Fin 2 =>
      ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l T (ρ • X') i j - (if i = j then 1 else 0)) := by
    refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    exact ((LiftSetting.materialMetric_entry_contDiff α q Λ m hφ l T i j).comp
      (contDiff_const_smul ρ)).sub contDiff_const
  refine LiftSetting.norm_iteratedFDeriv_pi2_le_of_entries _ hA r X _
    (mul_nonneg (mul_nonneg hC0 hg0) (pow_nonneg (div_nonneg hρ hE.le) r)) fun i j => ?_
  have hg : ContDiff ℝ (r : ℕ∞) (fun y : Vec 2 =>
      ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l T y i j - (if i = j then 1 else 0)) :=
    (hdev i j).contDiff
  have hb := (hdev i j).bound (ρ • X) r le_rfl
  have e2 : ρ ^ r = (ρ / ocEpsilon q Λ (m - 1)) ^ r * ocEpsilon q Λ (m - 1) ^ r := by
    rw [← mul_pow, div_mul_cancel₀ _ hE.ne']
  calc ‖iteratedFDeriv ℝ r (fun y : Vec 2 =>
          ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l T (ρ • y) i j - (if i = j then 1 else 0)) X‖
      = |ρ| ^ r * ‖iteratedFDeriv ℝ r (fun y : Vec 2 =>
          ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l T y i j - (if i = j then 1 else 0))
            (ρ • X)‖ := iteratedFDeriv_comp_smul_norm r _ hg ρ X
    _ = (ρ / ocEpsilon q Λ (m - 1)) ^ r * (ocEpsilon q Λ (m - 1) ^ r *
          ‖iteratedFDeriv ℝ r (fun y : Vec 2 =>
            ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l T y i j - (if i = j then 1 else 0))
              (ρ • X)‖) := by
        rw [abs_of_nonneg hρ, e2, mul_assoc]
    _ ≤ (ρ / ocEpsilon q Λ (m - 1)) ^ r *
          (Charts.metricDevConst r * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (div_nonneg hρ hE.le) r)
    _ = _ := by ring

/-! ### Scalar letters from the chart-frame letters -/

section Reading

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The scalar letters inherit the jet bounds of the diagonal chart-frame letters. -/
theorem scalarReading_jet_le {Lb0 : ℤ → ℕ → MeanCoeff ι h}
    {Lsc Lfb : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ}
    (hR : IsScalarReading Lb0 Lsc Lfb) (k : ℤ) (n d : ℕ) (α : DerivativeWord2 (d - 1))
    (l : Fin 2) (s : ℝ) (i : ℕ) (X : Vec 2) {M : ℝ}
    (hf : ∀ v, ContDiff ℝ (i : ℕ∞) (fun X' => Lb0 k n d α s X' l v v))
    (hb : ∀ v, ‖iteratedFDeriv ℝ i (fun X' => Lb0 k n d α s X' l v v) X‖ ≤ M)
    (hfb : ‖iteratedFDeriv ℝ i (Lfb k n d α l s) X‖ ≤ M) :
    ‖iteratedFDeriv ℝ i (Lsc k n d α l s) X‖ ≤ M := by
  rcases hR with ⟨v₀, φ, hφ, -, hread⟩ | hfall
  · have e : Lsc k n d α l s = fun X' => φ (Lb0 k n d α s X' l v₀ v₀) :=
      funext fun X' => hread k n d α l s X'
    rw [e]
    have hle := φ.norm_iteratedFDeriv_comp_left (f := fun X' => Lb0 k n d α s X' l v₀ v₀)
      (x := X) (hf v₀).contDiffAt (n := i) (by exact_mod_cast le_rfl)
    refine hle.trans ?_
    calc ‖φ‖ * ‖iteratedFDeriv ℝ i (fun X' => Lb0 k n d α s X' l v₀ v₀) X‖
        ≤ 1 * M := mul_le_mul hφ (hb v₀) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  · rw [hfall]
    exact hfb

/-- The order-two scalar letters, paired with the reference flux, inherit the jet bounds of the
diagonal chart-frame letters paired with the identity. -/
theorem scalarReading_pair_jet_le {Lb0 : ℤ → ℕ → MeanCoeff ι h}
    {Lsc Lfb : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ}
    (hR : IsScalarReading Lb0 Lsc Lfb) (k : ℤ) (n d : ℕ) (α : DerivativeWord2 (d - 1))
    (l : Fin 2) (s : ℝ) (i : ℕ) (X : Vec 2) (B J : ℝ) {M : ℝ}
    (hf : ∀ v, ContDiff ℝ (i : ℕ∞) (fun X' => Lb0 k n d α s X' l v v))
    (hb : ∀ v, ‖iteratedFDeriv ℝ i
      (fun X' => B • Lb0 k n d α s X' l v v + J • ContinuousLinearMap.id ℝ (h v)) X‖ ≤ M)
    (hfb : ‖iteratedFDeriv ℝ i (fun X' => B * Lfb k n d α l s X' + J) X‖ ≤ M) :
    ‖iteratedFDeriv ℝ i (fun X' => B * Lsc k n d α l s X' + J) X‖ ≤ M := by
  rcases hR with ⟨v₀, φ, hφ, hφid, hread⟩ | hfall
  · have e : (fun X' => B * Lsc k n d α l s X' + J) =
        fun X' => φ (B • Lb0 k n d α s X' l v₀ v₀ + J • ContinuousLinearMap.id ℝ (h v₀)) := by
      funext X'
      have h1 : φ (ContinuousLinearMap.id ℝ (h v₀)) = 1 := by
        have h1' := hφid 1
        rwa [one_smul] at h1'
      rw [map_add, map_smul, map_smul, h1, hread k n d α l s X', smul_eq_mul, smul_eq_mul,
        mul_one]
    rw [e]
    have hg : ContDiff ℝ (i : ℕ∞)
        (fun X' => B • Lb0 k n d α s X' l v₀ v₀ + J • ContinuousLinearMap.id ℝ (h v₀)) :=
      ((hf v₀).const_smul B).add contDiff_const
    have hle := φ.norm_iteratedFDeriv_comp_left
      (f := fun X' => B • Lb0 k n d α s X' l v₀ v₀ + J • ContinuousLinearMap.id ℝ (h v₀))
      (x := X) hg.contDiffAt (n := i) (by exact_mod_cast le_rfl)
    refine hle.trans ?_
    calc ‖φ‖ * ‖iteratedFDeriv ℝ i
          (fun X' => B • Lb0 k n d α s X' l v₀ v₀ + J • ContinuousLinearMap.id ℝ (h v₀)) X‖
        ≤ 1 * M := mul_le_mul hφ (hb v₀) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  · rw [hfall]
    exact hfb

end Reading

/-! ### The fallback letters -/

/-- The fallback letters of orders `n ≠ 2` have zero jets. -/
theorem refFallback_jet_of_ne (B c : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) {n : ℕ}
    (hn : n ≠ 2) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) (s : ℝ) (i : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ i (refFallback B c Jm k n d α l s) X‖ = 0 := by
  have e : refFallback B c Jm k n d α l s = fun _ => 0 :=
    funext fun X' => refFallback_of_ne B c Jm k hn d α l s X'
  rw [e, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]

/-- The fallback letter of order two, paired with the reference flux, vanishes. -/
theorem refFallback_pair_jet (B c : ℝ) (hB : B ≠ 0) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ)
    (α : DerivativeWord2 1) (l : Fin 2) (s : ℝ) (i : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ i
      (fun X' => B * refFallback B c Jm k 2 2 α l s X' + Jm (c * s) l (α 0)) X‖ = 0 := by
  have e : (fun X' => B * refFallback B c Jm k 2 2 α l s X' + Jm (c * s) l (α 0)) =
      fun _ => (0 : ℝ) := by
    funext X'
    rw [refFallback_two]
    show B * -(B⁻¹ * jmEntry Jm (c * s) 1 α l) + Jm (c * s) l (α 0) = 0
    rw [jmEntry_one, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, neg_add_cancel]
  rw [e, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! The reference-flux fields of `IsCoarseSetting` for `𝖩 = J = 𝐉_m^ν` (`ν = κ_m`,
`B = κ_{m-1} = K̄_m^ν`) on any window `[t₀, t₁]` (the coarse window of clause 6 of
`cycle_comparison`): `J` is symmetric (diagonal), entrywise measurable,
bounded, and its covariance anchored at `t₀` is at most `R² = Bτ_m''`.

The covariance: the anchored primitive bound `CycleReference.refFlux_covariance_primitive`
(`|C_s(t)_{ij}| ≤ 16H_*τ + 4H_*(4τ'' K/(μτ) + 16τ')` for all `s, t`) with `H_* ≤ CB`,
`τ ≤ τ' = τ''/L ≤ τ'' E^δ` (`L ≥ 4E^{-δ}`) and `μτ = 4π² τ/ℓ² ≥ C⁻¹E^{-δ}` gives
`≤ C(80 + 16KC) E^δ · Bτ''`, and `C(80 + 16KC)E^δ ≤ 1` for `Λ ≥ Λ₀`. -/

/-- **The reference-flux fields of the coarse setting** for `𝖩 = ocRefFlux α q Λ ζ m ν` at the
radius `R = √(Bτ_m'')`. -/
theorem coarse_flux_fields (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m : ℕ, 2 ≤ m → m ≤ M' →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ t₀ t₁ : ℝ,
        (∀ (t : ℝ) (i j : Fin 2), ocRefFlux α q Λ ζ m ν t i j = ocRefFlux α q Λ ζ m ν t j i) ∧
        (∀ i j : Fin 2, Measurable fun t => ocRefFlux α q Λ ζ m ν t i j) ∧
        matrixSupNorm (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          t₀ t₁ ≠ ⊤ ∧
        matrixSupNorm (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B t₀) t₀ t₁ ≤
          ENNReal.ofReal (Real.sqrt (B * ocTauPP α q Λ m) ^ 2) := by
  obtain ⟨C, hC, Λ₁, hΛ₁, hlaws⟩ := scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨K, hK0, hprim⟩ := AVRegularity.CycleReference.refFlux_covariance_primitive hζ
  have hδ : 0 < ocDelta α q :=
    (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hM : 0 ≤ C * (80 + 16 * K * C) := by positivity
  refine ⟨max Λ₁ ⌈(C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q)⌉₊,
    hΛ₁.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M' κ hband m hm2 hmM ν B hν hB t₀ t₁
  have hΛ₁' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ₂ : ⌈(C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q)⌉₊ ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ₁'
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast (show 0 < Λ by omega)
  have hL := hlaws Λ hΛ₁' M' κ hband m hm2 hmM ν B hν hB
  have hνpos : 0 < ν := hL.ν_pos
  have hBpos : 0 < B := lt_of_lt_of_le hνpos hL.ν_le
  refine ⟨?_, fun i j => AVRegularity.CycleReference.refFlux_entry_measurable hΛ1 hζ hνpos i j,
    ?_, ?_⟩
  · -- symmetry: the reference flux is diagonal
    intro t
    have hd := AVRegularity.CycleReference.refFlux_diagonal (α := α) (q := q) (m := m)
      (ζ := ζ) (t := t) hΛ1 hζ hνpos
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨rfl, ?_⟩, Fin.forall_fin_two.2 ⟨?_, rfl⟩⟩
    · rw [hd.1, hd.2]
    · rw [hd.1, hd.2]
  · -- boundedness of `J - B I`
    have hbound : ∀ (t : ℝ) (i j : Fin 2),
        |(ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
          ν + ocHStar α q Λ m ν + B := by
      intro t i j
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have h1 := refFlux_entry_abs_le (α := α) (q := q) (m := m) (ζ := ζ) hΛ1 hζ hνpos t i j
      have hone : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]
        split_ifs <;> simp
      have h2 : |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
        rw [abs_mul, abs_of_pos hBpos]
        calc B * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B * 1 :=
              mul_le_mul_of_nonneg_left hone hBpos.le
          _ = B := mul_one B
      calc |ocRefFlux α q Λ ζ m ν t i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
          = |ocRefFlux α q Λ ζ m ν t i j + -(B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| := by
            rw [sub_eq_add_neg]
        _ ≤ |ocRefFlux α q Λ ζ m ν t i j| + |-(B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| :=
            abs_add_le _ _
        _ = |ocRefFlux α q Λ ζ m ν t i j| + |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
            rw [abs_neg]
        _ ≤ ν + ocHStar α q Λ m ν + B := add_le_add h1 h2
    have hle : matrixSupNorm
        (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≤
          ENNReal.ofReal (ν + ocHStar α q Λ m ν + B) := by
      unfold matrixSupNorm
      exact iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j =>
        ENNReal.ofReal_le_ofReal (hbound t i j)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  · -- the covariance anchored at `t₀`
    have hE : 0 < ocEpsilon q Λ (m - 1) :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
    have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
    have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
    have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
      AVRegularity.CycleReference.epsilon_le_inv_separation (m := m - 1) hq.1 h128 (by omega)
    have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
    have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
    have hts := AVRegularity.Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq h128
      (m := m) (by omega)
    have hL5 : (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by exact_mod_cast hts.1
    have hLpos : (0 : ℝ) < (ocL α q Λ m : ℝ) := by linarith
    have hL1 : (1 : ℝ) ≤ (ocL α q Λ m : ℝ) := by linarith
    -- the block times against `τ'' E^δ`
    have hEδ : 0 < ocEpsilon q Λ (m - 1) ^ ocDelta α q := Real.rpow_pos_of_pos hE _
    have hcancel : ocEpsilon q Λ (m - 1) ^ ocDelta α q *
        ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) = 1 := by
      rw [← Real.rpow_add hE, add_neg_cancel, Real.rpow_zero]
    have hEL : 1 ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) := by
      have h0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := (Real.rpow_pos_of_pos hE _).le
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) := by
        linarith [hts.2.1]
      calc (1 : ℝ) = ocEpsilon q Λ (m - 1) ^ ocDelta α q *
            ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := hcancel.symm
        _ ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hEδ.le
    have hτP : ocTauP α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      unfold ocTauP
      rw [div_le_iff₀ hLpos]
      calc ocTauPP α q Λ m = ocTauPP α q Λ m * 1 := (mul_one _).symm
        _ ≤ ocTauPP α q Λ m * (ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ)) :=
            mul_le_mul_of_nonneg_left hEL hτ''.le
        _ = ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            (mul_assoc _ _ _).symm
    have hτP0 : 0 ≤ ocTauP α q Λ m := by
      unfold ocTauP
      exact div_nonneg hτ''.le hLpos.le
    have hτle : ocTau α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      have heq : ocTau α q Λ m = ocTauP α q Λ m / (ocL α q Λ m : ℝ) := by
        unfold ocTau ocTauP
        rw [div_div, sq]
      rw [heq]
      exact (div_le_self hτP0 hL1).trans hτP
    -- the memory rate against `C⁻¹ E^{-δ}`
    have hℓ : 0 < ocEll q Λ m ν := by
      unfold ocEll
      exact div_pos he (Real.sqrt_pos.2 hνpos)
    have hμτ : ocMu q Λ m ν * ocTau α q Λ m =
        4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
      have hℓ2 : ocEll q Λ m ν ^ 2 ≠ 0 := (pow_pos hℓ 2).ne'
      calc ocMu q Λ m ν * ocTau α q Λ m
          = ocMu q Λ m ν * (ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)) := by
            rw [mul_div_cancel₀ _ hℓ2]
        _ = ocMu q Λ m ν * ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            (mul_assoc _ _ _).symm
        _ = 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
            rw [ocMu_mul_ocEll_sq hΛ1 hνpos]
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
    have hlow : C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
        ocMu q Λ m ν * ocTau α q Λ m := by
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
          ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
        Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
      have h2 : 0 ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := div_nonneg hτ.le (sq_nonneg _)
      rw [hμτ]
      calc C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)
          ≤ C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hCpos.le)
        _ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := hL.quiet_ge
        _ ≤ 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            le_mul_of_one_le_left h2 hπ
    have hlowpos : 0 < C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) :=
      mul_pos (inv_pos.2 hCpos) (Real.rpow_pos_of_pos hE _)
    have hr : K / (ocMu q Λ m ν * ocTau α q Λ m) ≤
        K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      calc K / (ocMu q Λ m ν * ocTau α q Λ m)
          ≤ K / (C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) :=
            div_le_div_of_nonneg_left hK0 hlowpos hlow
        _ = K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
            rw [div_eq_mul_inv, mul_inv, inv_inv, Real.rpow_neg hE.le, inv_inv]
            ring
    have hr0 : 0 ≤ K / (ocMu q Λ m ν * ocTau α q Λ m) :=
      div_nonneg hK0 (hlowpos.trans_le hlow).le
    have hsmall : C * (80 + 16 * K * C) * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 :=
      mul_rpow_le_one_of_small hE hδ hΛpos hEΛ hM
        ((Nat.le_ceil ((C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q))).trans
          (Nat.cast_le.2 hΛ₂))
    have hbudget := covariance_budget_le hL.hstar_le hBpos hCpos.le hτ.le hτP0 hτ'' hr0 hτle
      hτP hr hsmall
    -- the mean flux is the coarse diffusivity
    have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
      rw [← hB, ← hν]
      exact hband.2 m (by omega) hmM
    rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le)]
    unfold matrixSupNorm
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
    have hprim' := hprim α q Λ m hΛ1 ν hνpos t₀ t i j
    rw [← hBmean] at hprim'
    exact hprim'.trans hbudget

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! Clauses 1 to 3 of `cycle_comparison` for the observed pulses of the construction: the
means stage with the pulse lift data, the renewal charts and the family partition substituted,
and the lift settings supplied by `cycle_comparison_lift_setting`. The letters are the
explicit Eulerian letters `adLetter`, `ceLetter` on the chart-frame letters of the pulses.
-/

section
open AVRegularity.CycleComparison.ActualMeans

section Data

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}

/-- The lift data of the observed pulse `k`. -/
abbrev obsLiftData (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B : ℝ) (F : ChartedFamily ι h D P' Ctx)
    (actual : ∀ p, Ctx p) (pp : ℤ → P') (k : ℤ) : LiftOperatorData ι h D :=
  pulseLiftData α q Λ m ζ (Φ (m - 1)) hφ ν B (Real.sqrt (B * ocTauPP α q Λ m))
    (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
    (F.fiber (pp k) (actual (pp k)))

end Data

/-- The start of the lift window of the pulse `k`, clipped to the observation window. -/
abbrev obsStart (α q : ℝ) (Λ m : ℕ) (ν tp : ℝ) (k : ℤ) : ℝ :=
  max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp / ocEll q Λ m ν ^ 2

/-- The end of the lift window of the pulse `k`, clipped to the observation window. -/
abbrev obsEnd (α q : ℝ) (Λ m : ℕ) (ν tz : ℝ) (k : ℤ) : ℝ :=
  min (((k : ℝ) + 61 / 48) * ocTau α q Λ m) tz / ocEll q Λ m ν ^ 2

/-- A cell time of the lift window of a pulse is within one renewal time of the anchor of its
chart. -/
theorem abs_sub_anchor_le (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {ν : ℝ} (hℓ : 0 < ocEll q Λ m ν)
    (tp tz : ℝ) (k : ℤ) {t : ℝ}
    (ht : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν tz k)) :
    |t - (ocPulseChartIndex α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m := by
  have h1 := LiftSetting.liftWindow_subset_chartWindow α q hΛ m ν tp tz k ht
  have h2 := mem_window_of_cellTime (pow_pos hℓ 2) h1
  rw [abs_le]
  constructor
  · linarith [h2.2.1]
  · linarith [h2.2.2]

/-- **Clauses 1 to 3 of `cycle_comparison`, with explicit letters.** -/
theorem oc_means (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (g₀ Ca : ℝ) (CG : ℕ → ℝ), g₀ ≤ 1 / 4 →
      ∀ (H D Nc Klift Llift Ks Ls qJ Kmax : ℕ), 2 ≤ D → 1 ≤ Nc →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ Ks →
        Llift + 2 + H * D + 2 * Nc + 2 * D ≤ Ls →
        Klift + 4 * (H + 1) * (Nc + D) ^ 2 ≤ qJ →
      ∃ (CGl Cw : ℕ → ℝ) (C₂ C₁ Ct : ℝ), 0 ≤ C₂ ∧ 0 ≤ C₁ ∧ 0 ≤ Ct ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tp Tobs ρs g a B₀ lam₀ Cb : ℝ)
        (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) ρs g g₀ a B₀ lam₀ Cb
          qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hmeas : F.IsTimeMeasurable) (A : Matrix ι ι ℝ) (S : ℝ)
        (_hb : ∀ v u, 0 ≤ Real.sqrt (π u / π v) * A v u)
        (_hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ S)
        (_hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ S)
        (_hpointwiseAn : IsPointwiseAnalyticEnvelope F π
          (ChartedFamily.Domain.onWindow F (Set.Icc tp (tp + Tobs))) (ocEpsilon q Λ (m - 1))
          Ca Ks Ls (fun v u => Real.sqrt (π u / π v) * A v u))
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tp (tp + Tobs))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)))
        (pp : ℤ → P')
        (_hout : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          ocPulseWindow α q Λ m k ∩ Set.Icc tp (tp + Tobs) ⊆ (F.piece (pp k)).output)
        (Cpart : ℝ)
        (_hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs))
          (fun k => F.weight (pp k)) (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m)
          (Set.Icc tp (tp + Tobs)) (ocTau α q Λ m) Cpart),
      ∃ (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ),
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∃ (par : Fin 2) (V : ℝ → ℝ → ℝ),
          IsLiftSetting (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) π
            (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k) (ocEpsilon q Λ m) ν B
            (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1)) (ocEll q Λ m ν)
            (ocDStar q Λ m ν B) (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) par V H Nc Klift 0 Llift
            (Klift + 4 * (H + 1) * (Nc + D) ^ 2) (max 0 (Llift + 2) + H * D + 2 * Nc + 2 * D)
            CGl Cw (fun _ _ => Ca) (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) S) ∧
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsLiftSequence (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) (Klift + D + 2)
            (Llift + 2) (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k) Nc H
            (Cc k)) ∧
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsPulseLetters (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) (Cc k) π
            (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) (obsStart α q Λ m ν tp k)
            (obsEnd α q Λ m ν (tp + Tobs) k)
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) C₂ Nc H Klift (Lb k)) ∧
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ n, 2 ≤ n → n ≤ Nc + D →
          ∀ d, 2 ≤ d → d ≤ n → ∀ (α' : DerivativeWord2 (d - 1)) (l : Fin 2),
            ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k), ∀ X,
              (∀ (v : ι) (ξ : h v), Lb k 0 n d α' s' X l v v ξ = Lsc k n d α' l s' X • ξ) ∧
              (∀ v u : ι, v ≠ u → Lb k 0 n d α' s' X l v u = 0)) ∧
        (∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ n, 2 ≤ n → n ≤ Nc + D →
          ∀ d, 2 ≤ d → d ≤ n → ∀ (α' : DerivativeWord2 (d - 1)) (l : Fin 2),
            ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k),
              ContDiff ℝ ((Klift + 1 : ℕ) : ℕ∞) (Lsc k n d α' l s')) ∧
        IsScalarReading (fun k n => Lb k 0 n) Lsc
          (refFallback B (ocEll q Λ m ν ^ 2) (ocRefFlux α q Λ ζ m ν)) ∧
        IsActualMeans Nc D H (Klift + 1) C₁ (ocObsPulses α q Λ m tp (tp + Tobs))
          (fun k => F.weight (pp k)) tp (tp + Tobs) (ocEll q Λ m ν ^ 2)
          (Real.sqrt (B * ocTauPP α q Λ m))
          (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
          (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) (ocEpsilon q Λ (m - 1))
          (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp) Cc
          (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
          (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lb (ocRefFlux α q Λ ζ m ν)
          (adLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lsc (ocRefFlux α q Λ ζ m ν))
          (ceLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
            (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
            (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
            (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
            (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lb) ∧
        (∀ r, 1 ≤ r → r ≤ H → ∀ K' : ℕ, K' ≤ Klift + 1 → ∀ v u,
          ENNReal.ofReal (Real.sqrt (π u / π v)) *
            ((∑ d : Finset.Icc 2 (Nc + D),
                coefficientSeminorm (ocEpsilon q Λ (m - 1)) K' tp (tp + Tobs)
                  (ceLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
                    (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
                    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
                    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lb r v u d) *
                  (ENNReal.ofReal (B * ocEpsilon q Λ (m - 1) ^ (d.1 - 2)))⁻¹) +
              ∑ d : Finset.Icc 2 (Nc + D),
                coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m)) K' tp (tp + Tobs)
                  (ceLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
                    (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
                    (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
                    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lb r v u d) *
                  (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹) ≤
            ENNReal.ofReal (2 * ((Nc + D : ℕ) : ℝ) ^ 2 * ((K' : ℝ) + 1) * (Ct * C₂) *
              (Real.sqrt (π u / π v) * (Coarse.maskedEdgeMatrix (familyAdj F) A ^ r) v u))) := by
  obtain ⟨Λ₀, Cw, hΛ₀, h6⟩ := LiftSetting.lift_setting α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ g₀ Ca CG hg₀
  obtain ⟨CGl, h6'⟩ := h6 Λ hΛ g₀ Ca CG hg₀
  intro H D Nc Klift Llift Ks Ls qJ Kmax hD hN hKs hLs hqJ
  obtain ⟨C₂, C₁, Ct, hC₂, hC₁, hCt, hstage⟩ := means_stage Nc Klift 0 Llift D H hD CGl Cw
    (fun _ _ => Ca) (Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨CGl, Cw, C₂, C₁, Ct, hC₂, hC₁, hCt, ?_⟩
  intro ι _ _ h _ _ _ _ π hπ Φ hΦ M' κ hband m hm2 hmM ν B hν hB hφ tp Tobs ρs g a B₀ lam₀ Cb
    l₀ P y₀ cov P' Ctx F actual hdepth htorus hmeas A S hb hrow hcol hpointwiseAn htrans hquiet
    pp hout Cpart hpart
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hνpos : 0 < ν := LiftSetting.ν_pos cov
  have hBpos : 0 < B := LiftSetting.B_pos cov
  have hρ : 0 < Real.sqrt (B * ocTauPP α q Λ m) := LiftSetting.ρ_pos α q hΛ1 m hBpos
  have hE : 0 < ocEpsilon q Λ (m - 1) := LiftSetting.E_pos q hΛ1 m
  have hℓ : 0 < ocEll q Λ m ν := by
    unfold ocEll
    exact div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.2 hνpos)
  have hdρ : ocDStar q Λ m ν B ≤ Real.sqrt (B * ocTauPP α q Λ m) :=
    (div_le_one hρ).1 (LiftSetting.εc_le α q hΛ1 m hνpos.le hBpos cov.ellT)
  have hqf : Llift + 2 + H * D + 2 * Nc + 2 * D =
      max 0 (Llift + 2) + H * D + 2 * Nc + 2 * D := by
    rw [Nat.zero_max]
  -- the lift settings of the observed pulses
  choose! par V hset using fun k₁ (hk₁ : k₁ ∈ ocObsPulses α q Λ m tp (tp + Tobs)) =>
    h6' H D Nc Klift 0 Llift (Klift + 4 * (H + 1) * (Nc + D) ^ 2)
      (max 0 (Llift + 2) + H * D + 2 * Nc + 2 * D) Ks Ls qJ Kmax hD hN rfl rfl hKs
      (hqf ▸ hLs) hqJ π hπ Φ M' κ hband m hm2 hmM ν B hν hB hφ tp Tobs ρs g a B₀ lam₀ Cb l₀ P
      y₀ cov F actual hdepth hmeas (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) S
      (familyMask_nonneg F hb) (familyMask_row_le F hb hrow) (familyMask_col_le F hb hcol)
      (pointwiseAnalyticEnvelope_familyMask F π _ _ _ _ _ hpointwiseAn) htrans hquiet pp k₁ hk₁
      (hout k₁ hk₁)
  obtain ⟨hϖ0, hϖm, hϖ1, hϖsupp⟩ := partition_stage_facts hpart
  obtain ⟨Cc, Lb, Lsc, hCc, hLb, hsc, hscC, hdeg, hAM, hC3⟩ := hstage
    (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k)) tp (tp + Tobs)
    (ocEpsilon q Λ m) ν B (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1))
    (ocEll q Λ m ν) (ocDStar q Λ m ν B) π
    (familyMask F (fun v u => Real.sqrt (π u / π v) * A v u)) S
    (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp)
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) par V
    (Klift + 4 * (H + 1) * (Nc + D) ^ 2) (max 0 (Llift + 2) + H * D + 2 * Nc + 2 * D)
    (ocRefFlux α q Λ ζ m ν) hπ (familyMask_nonneg F hb) hℓ hBpos hρ hE
    (LiftSetting.dstar_eq q Λ m hνpos.le B) hdρ
    cov.RE hset (fun i j => CycleReference.refFlux_entry_measurable hΛ1 hζ hνpos i j)
    hϖ0 hϖm hϖ1
    (fun k hk t ht hne => cellTime_mem_liftWindow (pow_pos hℓ 2) (hϖsupp k hk t hne) ht)
    (fun k _ t y => Charts.ocChartInv_ocChart α q Λ m (Φ (m - 1)) hφ _ t y)
    (fun k _ t x => Charts.ocChart_ocChartInv α q Λ m (Φ (m - 1)) hφ _ t x)
    (fun k _ t p y => Charts.ocChart_latticeShift hφ α q Λ m _ t p y)
    (fun k _ t y => Charts.ocChart_det hφ α q Λ m _ t y)
    (fun k _ => Charts.contDiff_ocChart_joint hφ α q Λ m _)
    (fun k _ => Charts.contDiff_ocChartInv_joint hφ α q Λ m _)
    (fun k _ t _ hwin p hp1 _ y => Charts.ocChart_window_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ
      hΛ128 Φ hΦ m hm2 hφ (ocPulseChartIndex α q Λ m k) t
      (abs_sub_anchor_le α q hΛ1 m hℓ tp (tp + Tobs) k hwin) p hp1 y)
    (fun k _ p t X i j => pulseLiftData_G_shift α q Λ m ζ hφ ν B hρ.ne' _ k _ p t X i j)
    (fun k _ p v u d γ hγ α' t X z =>
      liftEdges_fiber_coeff_shift hρ.ne' htorus (ocEll q Λ m ν ^ 2) (pp k) p hγ α' t X z)
  refine ⟨Cc, Lb, Lsc, fun k hk => ⟨par k, V k, hset k hk⟩, ?_, hLb, hsc, hscC, hdeg, hAM, ?_⟩
  · intro k hk
    have h := hCc k hk
    have hmax : max (0 + 1) (Llift + 2) = Llift + 2 := by omega
    rw [hmax] at h
    exact h
  · intro r hr1 hrH K' hK' v u
    have h := hC3 r hr1 hrH K' hK' v u
    rw [familyMask_conj F hπ A] at h
    exact h
end

/-! Clause 4 of `cycle_comparison` for the observed pulses of the construction: the
diagonal letter `adLetter` of the explicit letters has normalized size
`α_R ≤ C E^{2δ}`. The per-pulse order-two comparison with the
reference flux is `pulse_diagonal_two` (the flat pulse solution, metric stability and the
switching price); the chart deviation, the higher orders and the partition are
`adLetter_means_bound`; the scale laws give `ε_c ≤ C E^{3δ}`, `H_* ℓ²/τ ≤ C B E^{2δ}`,
`ν ≤ B`, `H_* ≤ C B`, and `a_{m-1}τ_m'' ≤ 2^{-25} E^{2δ}`. -/

section
open AVRegularity.CycleComparison.ActualMeans

/-- The arithmetic of the final constant of clause 4. -/
theorem diag_size_le {Cad M Kp Kl C₂ εc Cs e B g Cpd Kζ X Cdev CJ : ℝ} (hCad : 0 ≤ Cad)
    (hM : 0 ≤ M) (hKp : 0 ≤ Kp) (hKl : Kp ≤ Kl) (hC₂ : 0 ≤ C₂) (hε : εc ≤ Cs * e)
    (hB : 0 < B) (hg0 : 0 ≤ g) (hg : g ≤ 2 ^ (-25 : ℤ) * e) (hCpd : 0 ≤ Cpd) (hKζ : 0 ≤ Kζ)
    (hX : X ≤ Cs * B * e) (hCdev : 0 ≤ Cdev) (hCJ : CJ ≤ (1 + Cs) * B) (hCs : 0 ≤ Cs)
    (he : 0 ≤ e) :
    Cad * M * Kp * (C₂ * M * εc + (Cpd * B * g + Kζ * X + CJ * (Cdev * g)) / B) ≤
      Cad * M * Kl * (C₂ * M * Cs + Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
        (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e := by
  have h1 : C₂ * M * εc ≤ C₂ * M * Cs * e := by
    calc C₂ * M * εc ≤ C₂ * M * (Cs * e) := mul_le_mul_of_nonneg_left hε (mul_nonneg hC₂ hM)
      _ = C₂ * M * Cs * e := by ring
  have h2 : (Cpd * B * g + Kζ * X + CJ * (Cdev * g)) / B ≤
      (Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs + (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e := by
    rw [div_le_iff₀ hB]
    have a1 : Cpd * B * g ≤ Cpd * B * (2 ^ (-25 : ℤ) * e) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg hCpd hB.le)
    have a2 : Kζ * X ≤ Kζ * (Cs * B * e) := mul_le_mul_of_nonneg_left hX hKζ
    have a3 : CJ * (Cdev * g) ≤ ((1 + Cs) * B) * (Cdev * (2 ^ (-25 : ℤ) * e)) :=
      mul_le_mul hCJ (mul_le_mul_of_nonneg_left hg hCdev) (mul_nonneg hCdev hg0)
        (mul_nonneg (by linarith) hB.le)
    calc Cpd * B * g + Kζ * X + CJ * (Cdev * g)
        ≤ Cpd * B * (2 ^ (-25 : ℤ) * e) + Kζ * (Cs * B * e) +
            ((1 + Cs) * B) * (Cdev * (2 ^ (-25 : ℤ) * e)) := by linarith
      _ = (Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs + (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e * B := by
          ring
  have h25 : (0 : ℝ) ≤ 2 ^ (-25 : ℤ) := by positivity
  have hbr : 0 ≤ C₂ * M * Cs + Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
      (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ)) := by
    have b1 := mul_nonneg (mul_nonneg hC₂ hM) hCs
    have b2 := mul_nonneg hCpd h25
    have b3 := mul_nonneg hKζ hCs
    have b4 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Cs) (mul_nonneg hCdev h25)
    linarith
  have h3 : 0 ≤ (C₂ * M * Cs + Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
      (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e := mul_nonneg hbr he
  calc Cad * M * Kp * (C₂ * M * εc + (Cpd * B * g + Kζ * X + CJ * (Cdev * g)) / B)
      ≤ Cad * M * Kp * ((C₂ * M * Cs + Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
          (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hCad hM) hKp)
        calc C₂ * M * εc + (Cpd * B * g + Kζ * X + CJ * (Cdev * g)) / B
            ≤ C₂ * M * Cs * e + (Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
                (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e := add_le_add h1 h2
          _ = _ := by ring
    _ ≤ Cad * M * Kl * ((C₂ * M * Cs + Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs +
          (1 + Cs) * (Cdev * 2 ^ (-25 : ℤ))) * e) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKl (mul_nonneg hCad hM)) h3
    _ = _ := by ring

/-- `E^{3δ} ≤ E^{2δ}` for `0 < E ≤ 1`, `δ ≥ 0`. -/
theorem rpow_three_le_two {E δ : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ) :
    E ^ (3 * δ) ≤ E ^ (2 * δ) :=
  Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)

/-- The cell time `ℓ²` times the start of the lift window is the clipped physical start. -/
theorem ell_sq_mul_obsStart {α q : ℝ} {Λ m : ℕ} {ν : ℝ} (hℓ : 0 < ocEll q Λ m ν) (tp : ℝ)
    (k : ℤ) :
    ocEll q Λ m ν ^ 2 * obsStart α q Λ m ν tp k =
      max (((k : ℝ) - 61 / 48) * ocTau α q Λ m) tp := by
  unfold obsStart
  rw [mul_div_cancel₀ _ (pow_pos hℓ 2).ne']

/-- **Clause 4 of `cycle_comparison` for the observed pulses.** -/
theorem oc_diagonal (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (CGl Cw : ℕ → ℝ) (Ca C₂ : ℝ) (H D Nc Klift Llift : ℕ), 2 ≤ D → 0 ≤ C₂ →
      ∃ C4 : ℝ, 0 ≤ C4 ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1))) (tp Tobs ρs g a B₀ lam₀ Cb g₀ : ℝ)
        (qJ Kmax : ℕ) (CG : ℕ → ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζ Φ hφ ν B tp (tp + Tobs) ρs g g₀ a B₀ lam₀ Cb
          qJ Kmax CG l₀ P y₀)
        (_htpq : tp ∈ ocQuietTimes α q Λ ζ m)
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (actual : ∀ p, Ctx p) (pp : ℤ → P') (bm : ι → ι → ℝ) (Θ : ℝ) (qs qf : ℕ)
        (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
        (_hset : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsLiftSetting (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) π
            (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k) (ocEpsilon q Λ m) ν B
            (Real.sqrt (B * ocTauPP α q Λ m)) (ocEpsilon q Λ (m - 1)) (ocEll q Λ m ν)
            (ocDStar q Λ m ν B) (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) (par k) (V k) H Nc
            Klift 0 Llift qs qf CGl Cw (fun _ _ => Ca) bm Θ)
        (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
        (_hCc : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsLiftSequence (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) (Klift + D + 2)
            (Llift + 2) (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k) Nc H
            (Cc k))
        (_hLb : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs),
          IsPulseLetters (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) (Cc k) π bm
            (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k)
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) C₂ Nc H Klift (Lb k))
        (_hsc : IsScalarReading (fun k n => Lb k 0 n) Lsc
          (refFallback B (ocEll q Λ m ν ^ 2) (ocRefFlux α q Λ ζ m ν)))
        (_hscC : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ n, 2 ≤ n → n ≤ Nc + D →
          ∀ d, 2 ≤ d → d ≤ n → ∀ (α' : DerivativeWord2 (d - 1)) (l : Fin 2),
            ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k),
              ContDiff ℝ ((Klift + 1 : ℕ) : ℕ∞) (Lsc k n d α' l s'))
        (Cpart : ℝ)
        (_hpart : IsLiftPartition (ocObsPulses α q Λ m tp (tp + Tobs))
          (fun k => F.weight (pp k)) (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m)
          (Set.Icc tp (tp + Tobs)) (ocTau α q Λ m) Cpart),
      ∀ K' : ℕ, K' ≤ Klift →
        ∑ d : Finset.Icc 2 (Nc + D),
            coefficientSeminorm (Real.sqrt (B * ocTauPP α q Λ m)) K' tp (tp + Tobs)
              (adLetter (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
                (ocEll q Λ m ν ^ 2) (Real.sqrt (B * ocTauPP α q Λ m))
                (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Nc + D)
                (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
                (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lsc
                (ocRefFlux α q Λ ζ m ν) d) *
            (ENNReal.ofReal (B * Real.sqrt (B * ocTauPP α q Λ m) ^ (d.1 - 2)))⁻¹ ≤
          ENNReal.ofReal (C4 * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) := by
  obtain ⟨Cs, hCs1, Λs, hΛs, hlaws⟩ := scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Kζ, hKζ, hsw⟩ := switching_le hζ
  refine ⟨Λs, hΛs, ?_⟩
  intro Λ hΛ CGl Cw Ca C₂ H D Nc Klift Llift hD hC₂
  obtain ⟨Cpd, hCpd, hpd⟩ := Diagonal.pulse_diagonal_two Nc Klift 0 Llift D H CGl Cw
    (fun _ _ => Ca) Charts.metricDevConst
  obtain ⟨Cad, hCad, had⟩ := adLetter_means_bound Nc D Klift
    (Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨Cad * ((Nc + D : ℕ) : ℝ) * ((Klift : ℝ) + 1) * (C₂ * ((Nc + D : ℕ) : ℝ) * Cs +
    Cpd * 2 ^ (-25 : ℤ) + Kζ * Cs + (1 + Cs) * (Charts.chartDevConst Klift * 2 ^ (-25 : ℤ))),
    ?_, ?_⟩
  · have h25 : (0 : ℝ) ≤ 2 ^ (-25 : ℤ) := by positivity
    have b1 := mul_nonneg (mul_nonneg hC₂ (Nat.cast_nonneg (Nc + D))) (by linarith : (0 : ℝ) ≤ Cs)
    have b2 := mul_nonneg hCpd h25
    have b3 := mul_nonneg hKζ (by linarith : (0 : ℝ) ≤ Cs)
    have b4 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Cs)
      (mul_nonneg (Charts.chartDevConst_nonneg Klift) h25)
    exact mul_nonneg (mul_nonneg (mul_nonneg hCad (Nat.cast_nonneg _)) (by positivity))
      (by linarith)
  intro ι _ _ h _ _ _ _ π Φ hΦ M' κ hband m hm2 hmM ν B hν hB hφ tp Tobs ρs g a B₀ lam₀ Cb g₀
    qJ Kmax CG l₀ P y₀ cov htpq P' Ctx F actual pp bm Θ qs qf par V hset Cc Lb Lsc hCc hLb hsc
    hscC Cpart hpart K' hK'
  have hΛ128 : 128 ≤ Λ := hΛs.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hL := hlaws Λ hΛ M' κ hband m hm2 hmM ν B hν hB
  have hνpos : 0 < ν := hL.ν_pos
  have hBpos : 0 < B := lt_of_lt_of_le hνpos hL.ν_le
  have hρ : 0 < Real.sqrt (B * ocTauPP α q Λ m) := LiftSetting.ρ_pos α q hΛ1 m hBpos
  have hE : 0 < ocEpsilon q Λ (m - 1) := LiftSetting.E_pos q hΛ1 m
  have hEb := Scales.epsilon_basic (q := q) (Λ := Λ) (m := m - 1) hq.1 hΛ128
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hℓ : 0 < ocEll q Λ m ν := by
    unfold ocEll
    exact div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.2 hνpos)
  have hdρ : ocDStar q Λ m ν B ≤ Real.sqrt (B * ocTauPP α q Λ m) :=
    (div_le_one hρ).1 (LiftSetting.εc_le α q hΛ1 m hνpos.le hBpos cov.ellT)
  have hdstar := LiftSetting.dstar_eq q Λ m hνpos.le B
  set gm : ℝ := ocA α q Λ (m - 1) * ocTauPP α q Λ m
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_nonneg hE.le _
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ1
  have hgm0 : 0 ≤ gm := mul_nonneg hA0 hτ.le
  have hgmle : gm ≤ 2 ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
    (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ128 (by omega : 1 ≤ m)).2.2.2.2.1
  have hH0 : 0 < ocHStar α q Λ m ν := CycleReference.ocHStar_pos hΛ1 hνpos
  have hτ0 : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ1
  set X : ℝ := ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m
  have hX0 : 0 ≤ X := div_nonneg (mul_nonneg hH0.le (pow_nonneg hℓ.le 2)) hτ0.le
  set θ : ℝ := Cpd * B * gm + Kζ * X with hθ
  have hθ0 : 0 ≤ θ :=
    add_nonneg (mul_nonneg (mul_nonneg hCpd hBpos.le) hgm0) (mul_nonneg hKζ hX0)
  obtain ⟨hϖ0, hϖm, hϖ1, hϖsupp⟩ := partition_stage_facts hpart
  have hchart_t : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t, ContDiff ℝ (⊤ : ℕ∞)
      (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) := fun k _ t =>
    (Charts.contDiff_ocChart_joint hφ α q Λ m _).comp ((contDiff_const (c := t)).prodMk contDiff_id)
  have hlabel_t : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ t, ContDiff ℝ (⊤ : ℕ∞)
      (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) := fun k _ t =>
    (Charts.contDiff_ocChartInv_joint hφ α q Λ m _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id)
  -- the anchor window of the chart of a pulse, at the physical times of its lift window
  have hanchor : ∀ k : ℤ, ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k)
      (obsEnd α q Λ m ν (tp + Tobs) k),
      |ocEll q Λ m ν ^ 2 * s' - (ocPulseChartIndex α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤
        ocTauPP α q Λ m := by
    intro k s' hs'
    refine abs_sub_anchor_le α q hΛ1 m hℓ tp (tp + Tobs) k ?_
    rw [inv_mul_cancel_left₀ (pow_pos hℓ 2).ne']
    exact hs'
  -- the order-two premise
  have hpair : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ (α' : DerivativeWord2 1)
      (l : Fin 2), ∀ i, i ≤ Klift →
      ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k), ∀ X',
        ‖iteratedFDeriv ℝ i (fun X'' => B * Lsc k 2 2 α' l s' X'' +
          ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * s') l (α' 0)) X'‖ ≤
          θ * (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ^ i := by
    intro k hk α' l i hi s' hs' X'
    have hkodd : Odd k := LiftSetting.obsPulse_odd hk
    have hseq' : IsLiftSequence (obsLiftData α q Λ m ζ Φ hφ ν B F actual pp k) (Klift + D + 2)
        (max (0 + 1) (Llift + 2)) (obsStart α q Λ m ν tp k)
        (obsEnd α q Λ m ν (tp + Tobs) k) Nc H (Cc k) := by
      have hmax : max (0 + 1) (Llift + 2) = Llift + 2 := by omega
      rw [hmax]
      exact hCc k hk
    have hmetric := fun r (_ : r ≤ qs) => pulseLiftData_metric_deviation (ι := ι) α s hα₀ hα₁
      hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ m hm2 hφ ν B (Real.sqrt (B * ocTauPP α q Λ m))
      (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) k
      (F.fiber (pp k) (actual (pp k))) hρ.le (hanchor k) r
    have hwin : ∀ t ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k),
        ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m k := by
      intro t ht
      have h1 := mem_window_of_cellTime (pow_pos hℓ 2)
        (show (ocEll q Λ m ν ^ 2)⁻¹ * (ocEll q Λ m ν ^ 2 * t) ∈ _ by
          rw [inv_mul_cancel_left₀ (pow_pos hℓ 2).ne']
          exact ht)
      exact h1.1
    have hsw' : ocMu q Λ m ν * ocHStar α q Λ m ν *
        ocPulseMemory α q Λ ζ m ν k (ocEll q Λ m ν ^ 2 * obsStart α q Λ m ν tp k) ≤ Kζ * X := by
      rw [ell_sq_mul_obsStart hℓ tp k]
      exact hsw α q Λ m hΛ1 ν hνpos k _ (ocPulse_obsStart_eq_zero hΛ1 hζ hkodd htpq)
    refine scalarReading_pair_jet_le hsc k 2 2 α' l s' i X' B
      (ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * s') l (α' 0))
      (fun v => ((hLb k hk).smooth 0 (Nat.zero_le H) 2 le_rfl (by omega) 2 α' l v v s'
        hs').of_le (by exact_mod_cast (by omega : i ≤ Klift + 1)))
      (fun v => ?_) ?_
    · have hpd' := hpd (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) (φ := Φ (m - 1)) (hφ := hφ)
        (ν := ν) (B := B) (ρ := Real.sqrt (B * ocTauPP α q Λ m))
        (lam := Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) (kp := k)
        (edge := F.fiber (pp k) (actual (pp k))) (π := π) (t₀ := obsStart α q Λ m ν tp k)
        (t₁ := obsEnd α q Λ m ν (tp + Tobs) k) (E := ocEpsilon q Λ (m - 1))
        (dstar := ocDStar q Λ m ν B)
        (εc := ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (par := par k) (V := V k)
        (qs := qs) (qf := qf) (b := bm) (Θ := Θ) (g := gm) hζ hΛ1 hkodd (hset k hk) hgm0
        hmetric hwin (Cc k) hseq' α' l v i hi s' hs' X'
      rw [(hLb k hk).explicit 0 2, LiftMeanEntrywise.meanLetter_zero]
      refine hpd'.trans ?_
      by_cases hi0 : i = 0
      · subst hi0
        rw [ite_eq_left rfl]
        simp only [pow_zero, mul_one]
        rw [hθ]
        linarith
      · rw [ite_eq_right hi0, add_zero, hθ, add_mul]
        have hlam0 : 0 ≤ (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ^ i :=
          pow_nonneg (div_nonneg hρ.le hE.le) i
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hKζ hX0) hlam0)
    · rw [refFallback_pair_jet B (ocEll q Λ m ν ^ 2) hBpos.ne' (ocRefFlux α q Λ ζ m ν) k α' l
        s' i X']
      exact mul_nonneg hθ0 (pow_nonneg (div_nonneg hρ.le hE.le) i)
  -- the higher orders
  have hhi : ∀ k ∈ ocObsPulses α q Λ m tp (tp + Tobs), ∀ n, 3 ≤ n → n ≤ Nc + D →
      ∀ d, 2 ≤ d → d ≤ n → ∀ (α' : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ Klift →
        ∀ s' ∈ Set.Icc (obsStart α q Λ m ν tp k) (obsEnd α q Λ m ν (tp + Tobs) k), ∀ X',
          ‖iteratedFDeriv ℝ i (Lsc k n d α' l s') X'‖ ≤
            C₂ * (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ^ (n - d + i) := by
    intro k hk n hn3 hnN d hd hdn α' l i hi s' hs' X'
    refine scalarReading_jet_le hsc k n d α' l s' i X'
      (fun v => ((hLb k hk).smooth 0 (Nat.zero_le H) n (by omega) hnN d α' l v v s'
        hs').of_le (by exact_mod_cast (by omega : i ≤ Klift + 1)))
      (fun v => ?_) ?_
    · have hb := (hLb k hk).bound 0 (Nat.zero_le H) n (by omega) hnN d hd hdn α' l v v i
        (by omega) s' hs' X'
      rw [pow_zero, Matrix.one_apply_eq, mul_one] at hb
      exact hb
    · rw [refFallback_jet_of_ne B (ocEll q Λ m ν ^ 2) (ocRefFlux α q Λ ζ m ν) k (by omega) d α'
        l s' i X']
      exact mul_nonneg hC₂ (pow_nonneg (div_nonneg hρ.le hE.le) _)
  have hmain := had (ocObsPulses α q Λ m tp (tp + Tobs)) (fun k => F.weight (pp k))
    (ocEll q Λ m ν) B (ocDStar q Λ m ν B) (Real.sqrt (B * ocTauPP α q Λ m))
    (ocEpsilon q Λ (m - 1)) tp (tp + Tobs)
    (fun k => ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (fun k => ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k))
    (obsStart α q Λ m ν tp) (obsEnd α q Λ m ν (tp + Tobs)) Lsc (ocRefFlux α q Λ ζ m ν) C₂ θ
    (Charts.chartDevConst Klift * gm) (ν + ocHStar α q Λ m ν) (by omega) hℓ hBpos hρ hdstar hdρ
    cov.RE hC₂ hθ0 (mul_nonneg (Charts.chartDevConst_nonneg Klift) hgm0)
    (add_nonneg hνpos.le hH0.le)
    hϖ0 hϖ1
    (fun k hk t ht hne => cellTime_mem_liftWindow (pow_pos hℓ 2) (hϖsupp k hk t hne) ht)
    hchart_t hlabel_t
    (fun k _ t _ hwin p hp1 _ y => Charts.ocChart_window_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ
      hΛ128 Φ hΦ m hm2 hφ (ocPulseChartIndex α q Λ m k) t
      (abs_sub_anchor_le α q hΛ1 m hℓ tp (tp + Tobs) k hwin) p hp1 y)
    (fun k _ t _ hwin a' b' => Charts.ocChart_jac_deviation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ
      hΛ128 Φ hΦ m hm2 hφ (ocPulseChartIndex α q Λ m k) t
      (abs_sub_anchor_le α q hΛ1 m hℓ tp (tp + Tobs) k hwin) Klift a' b')
    (fun t _ a' b' => refFlux_entry_abs_le hΛ1 hζ hνpos t a' b')
    (fun k hk n hn hnN d hd hdn α' l s' hs' =>
      (hscC k hk n hn hnN d hd hdn α' l s' hs').of_le
        (by exact_mod_cast (by omega : Klift ≤ Klift + 1)))
    hhi hpair K' hK'
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hεc : ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) ≤
      Cs * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
    hL.εc_le.trans (mul_le_mul_of_nonneg_left (rpow_three_le_two hE hEb.2.1 hδ.le)
      (by linarith))
  have hXle : X ≤ Cs * B * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := hL.switching_le
  have hCJ : ν + ocHStar α q Λ m ν ≤ (1 + Cs) * B := by
    have := hL.hstar_le
    have := hL.ν_le
    linarith
  have hK'r : ((K' : ℝ) + 1) ≤ (Klift : ℝ) + 1 := by
    have : (K' : ℝ) ≤ Klift := by exact_mod_cast hK'
    linarith
  have h := diag_size_le (Cad := Cad) (M := ((Nc + D : ℕ) : ℝ)) (Kp := (K' : ℝ) + 1)
    (Kl := (Klift : ℝ) + 1) (C₂ := C₂)
    (εc := ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) (Cs := Cs)
    (e := ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) (B := B) (g := gm) (Cpd := Cpd) (Kζ := Kζ)
    (X := X) (Cdev := Charts.chartDevConst Klift) (CJ := ν + ocHStar α q Λ m ν) hCad
    (Nat.cast_nonneg _) (by positivity) hK'r hC₂ hεc hBpos hgm0 hgmle hCpd hKζ hXle
    (Charts.chartDevConst_nonneg Klift) hCJ (by linarith) (Real.rpow_nonneg hE.le _)
  refine Eq.trans_le ?_ h
  rw [hθ]
end

end AVRegularity.CycleComparison.Assembly
end
