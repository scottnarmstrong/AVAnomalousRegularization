-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Davies.UfPackage
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVRegularity.Velocity.IncrementProvider
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance Matrix Filter Topology
namespace AVRegularity.Applications.Davies

/-! # The Davies localization in label coordinates

`davies_chart`: for a local energy solution in the chart `F_t = X(t,·,t₁)`, with cutoffs and
buffers, the datum `f = (per χU(s₀)) ∘ F_{s₀}⁻¹` has `L²` norm `≲ R A` and every torus solution
`u` from `f` is exponentially close to `θ` in the inner pipe. -/

open AVRegularity.Applications


/-- The datum built from the initial trace `W` of `χ U`. -/
theorem davies_datum {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow (streamVel φ) X) (t₁ s₀ : ℝ) {R : ℝ} (hR : 0 < R) (hR8 : R ≤ 1 / 8)
    (W : Lp ℝ 2 (volume.restrict (euclidBall (0 : Vec 2) R))) {Kb : ℝ} (hW : ‖W‖ ^ 2 ≤ Kb) :
    ∃ v₀ : Vec 2 → ℝ, v₀ =ᵐ[volume.restrict (euclidBall (0 : Vec 2) R)] (W : Vec 2 → ℝ) ∧
      MemL2On unitCube (datumFun X t₁ s₀ v₀) ∧ l2NormSq (datumFun X t₁ s₀ v₀) ≤ 625 * Kb ∧
      IsZ2Periodic (datumFun X t₁ s₀ v₀) ∧
      ∀ y ∈ euclidBall (0 : Vec 2) R, perX v₀ y = v₀ y := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hBn : ∀ y ∈ euclidBall (0 : Vec 2) R, ‖y‖ ≤ 1 / 8 := by
    intro y hy
    have h2 : vecNormSq y < R ^ 2 := by simpa [euclidBall] using hy
    have h1 := norm_le_sqrt_vecNormSq y
    have h3 : Real.sqrt (vecNormSq y) ≤ R :=
      Real.sqrt_le_iff.2 ⟨hR.le, h2.le⟩
    linarith
  set v₀ : Vec 2 → ℝ := (euclidBall (0 : Vec 2) R).indicator (fun y => (W : Vec 2 → ℝ) y) with hv₀
  have hsupp : ∀ y, v₀ y ≠ 0 → ‖y‖ ≤ 1 / 4 := by
    intro y hy
    by_cases hyB : y ∈ euclidBall (0 : Vec 2) R
    · linarith [hBn y hyB]
    · exact absurd (Set.indicator_of_notMem hyB _) hy
  have hv₀L : MemLp v₀ 2 volume := by
    rw [hv₀, memLp_indicator_iff_restrict hBm]
    exact Lp.memLp W
  have hv₀sq : ∫ y, v₀ y ^ 2 = ‖W‖ ^ 2 := by
    rw [← LocalEnergy.integral_sq_lp]
    have : (fun y => v₀ y ^ 2) = (euclidBall (0 : Vec 2) R).indicator
        (fun y => (W : Vec 2 → ℝ) y ^ 2) := by
      funext y
      by_cases hy : y ∈ euclidBall (0 : Vec 2) R <;> simp [hv₀, hy]
    rw [this, integral_indicator hBm]
  refine ⟨v₀, ?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' hBm]
    exact Filter.Eventually.of_forall fun y hy => by simp [hv₀, hy]
  obtain ⟨h1, h2⟩ := datum_l2 hφ hX t₁ s₀ hsupp hv₀L
  refine ⟨h1, ?_, datum_periodic hφ hX t₁ s₀, fun y hy => ?_⟩
  · rw [hv₀sq] at h2; linarith
  · exact perX_eq_self hsupp (hBn y hy)


variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2}

/-- The source integral is bounded by the energies. -/
theorem srcBound_final {V₀ T t₁ s₀ R κ N Kb Ef : ℝ} (hc : LabelCoeffs G V V₀ (t₁ - 8 * T) t₁)
    (hT : 0 < T) (hκ : 0 < κ) (hs : t₁ - s₀ = 9 * T / 2) (hs0 : t₁ - 8 * T ≤ s₀)
    (hs1 : s₀ < t₁) (hKb : 0 ≤ Kb) (hκT : κ * T ≤ R ^ 2) (hVT : (V₀ * T) ^ 2 ≤ R ^ 2)
    {U Uf : ℝ × Vec 2 → ℝ} {DU DUf : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hUf : MemLp Uf 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    {η : Vec 2 → ℝ} (hη : IsSpTest (euclidBall 0 R) η) (hη1 : ∀ y, 0 ≤ η y ∧ η y ≤ 1)
    {Wη : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R))}
    (hWηae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      (Wη τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => η y * U (τ, y))
    (hWηb : ∀ τ ∈ Set.Icc (t₁ - 8 * T + 2 * T) t₁, ‖Wη τ‖ ^ 2 ≤ Kb)
    (hWηg : κ * ∫ p in Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall 0 R,
      η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤ Kb)
    (hEf : Ef ≤ 625 * Kb) (hIUf : ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, Uf p ^ 2 ≤
      81 * (t₁ - s₀) * Ef) (hIGf : κ * ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R,
        vecNormSq (DUf p) ≤ 162 * Ef) :
    0 ≤ srcBound G V₀ κ (1 / T) N s₀ t₁ R η U Uf DU DUf ∧
      srcBound G V₀ κ (1 / T) N s₀ t₁ R η U Uf DU DUf ≤ 50000000 * (N * R) ^ 2 * Kb := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hsub : Set.Ioo s₀ t₁ ×ˢ euclidBall (0 : Vec 2) R ⊆
      Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R :=
    Set.prod_mono (Set.Ioo_subset_Ioo hs0 le_rfl) le_rfl
  have hsub2 : Set.Ioo s₀ t₁ ×ˢ euclidBall (0 : Vec 2) R ⊆
      Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R := by
    refine Set.prod_mono (Set.Ioo_subset_Ioo ?_ le_rfl) le_rfl
    linarith
  have hU' := hU.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDU' : ∀ i : Fin 2, MemLp (fun p => DU p i) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := fun i =>
    (hDU i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hηc : Continuous fun p : ℝ × Vec 2 => η p.2 := hη.1.continuous.comp continuous_snd
  have hηb : ∀ᵐ p ∂(volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall (0 : Vec 2) R)), ‖η p.2‖ ≤ 1 :=
    Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hη1 _).1]; exact (hη1 _).2
  have hηU : MemLp (fun p => η p.2 * U p) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    memLp_two_mul_bdd hηc.aestronglyMeasurable hηb hU'
  have hηUf : MemLp (fun p => η p.2 * Uf p) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    memLp_two_mul_bdd hηc.aestronglyMeasurable hηb hUf
  have iU : Integrable (fun p => η p.2 ^ 2 * U p ^ 2)
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    hηU.integrable_sq.congr (Filter.Eventually.of_forall fun p => by simp only [mul_pow])
  have iUf : Integrable (fun p => Uf p ^ 2)
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := hUf.integrable_sq
  -- the energy of the cutoff solution
  have hI1 : ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, η p.2 ^ 2 * U p ^ 2 ≤
      9 * T / 2 * Kb := by
    refine (prod_integral_le iU (c := fun _ => Kb) (integrableOn_const (by simp [Real.volume_Ioo]))
      ?_).trans ?_
    · have hae := ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo hs0 le_rfl) hWηae
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with τ h1 hτ
      have hτI : τ ∈ Set.Icc (t₁ - 8 * T + 2 * T) t₁ := ⟨by linarith [hτ.1], hτ.2.le⟩
      have : ∫ y in euclidBall (0 : Vec 2) R, η y ^ 2 * U (τ, y) ^ 2 = ‖Wη τ‖ ^ 2 := by
        rw [← LocalEnergy.integral_sq_lp]
        exact integral_congr_ae (h1.mono fun y hy => by simp only [hy, mul_pow])
      rw [this]
      exact hWηb τ hτI
    · rw [setIntegral_const, Real.volume_real_Ioo_of_le hs1.le]
      simp only [smul_eq_mul]
      nlinarith
  have iQ := integrable_quad hc hDU hη (fun y => by rw [abs_of_nonneg (hη1 y).1]; exact (hη1 y).2)
  have iQ' : Integrable (fun p => η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    iQ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have iQ2 : IntegrableOn (fun p : ℝ × Vec 2 => η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)))
      (Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall 0 R) :=
    integrableOn_Ioo_of_Ioo iQ (by linarith) le_rfl
  have hQ0 : ∀ p ∈ Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R,
      0 ≤ η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) := fun p hp =>
    mul_nonneg (sq_nonneg _) (hc.psd ⟨by linarith [hp.1.1], hp.1.2.le⟩ _)
  have hI2 : κ * ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R,
      η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤ Kb := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hκ.le) hWηg
    exact setIntegral_mono_set iQ2 ((ae_restrict_iff' (measurableSet_Ioo.prod hBm)).2
      (Filter.Eventually.of_forall hQ0)) (Filter.Eventually.of_forall hsub2)
  -- the difference
  have hSD : ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, η p.2 ^ 2 * (U p - Uf p) ^ 2 ≤
      9 * T * Kb + 729 * T * Ef := by
    have hmono : ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, η p.2 ^ 2 * (U p - Uf p) ^ 2 ≤
        ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R,
          (2 * (η p.2 ^ 2 * U p ^ 2) + 2 * Uf p ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity)
        ((iU.const_mul 2).add (iUf.const_mul 2)) (Filter.Eventually.of_forall fun p => ?_)
      have h1 : η p.2 ^ 2 ≤ 1 := by nlinarith [(hη1 p.2).1, (hη1 p.2).2]
      have h2 : 0 ≤ η p.2 ^ 2 := sq_nonneg _
      have h3 : η p.2 ^ 2 * (U p - Uf p) ^ 2 ≤ η p.2 ^ 2 * (2 * U p ^ 2 + 2 * Uf p ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (U p + Uf p)]) h2
      have h4 : η p.2 ^ 2 * (2 * Uf p ^ 2) ≤ 1 * (2 * Uf p ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    refine hmono.trans ?_
    rw [integral_add (iU.const_mul 2) (iUf.const_mul 2), integral_const_mul, integral_const_mul]
    have hIUf' := hIUf
    rw [hs] at hIUf'
    nlinarith [hI1, hIUf']
  have hIQ0 : 0 ≤ ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R,
      η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) :=
    setIntegral_nonneg (measurableSet_Ioo.prod hBm) fun p hp =>
      mul_nonneg (sq_nonneg _) (hc.psd ⟨by linarith [hp.1.1], hp.1.2.le⟩ _)
  have hIGf0 : 0 ≤ ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, vecNormSq (DUf p) :=
    setIntegral_nonneg (measurableSet_Ioo.prod hBm) fun p _ => vecNormSq_nonneg _
  have key := srcBound_alg (N := N) hT hκ hKb hIQ0 hIGf0 hκT hVT hEf hSD hI2 hIGf
  unfold srcBound
  have e : 1 / (1 / T) = T := by field_simp
  rw [e]
  refine ⟨?_, key⟩
  have hSD0 : 0 ≤ ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, η p.2 ^ 2 * (U p - Uf p) ^ 2 :=
    setIntegral_nonneg (measurableSet_Ioo.prod hBm) fun p _ => by positivity
  have hc1 : 0 ≤ 729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2) := by positivity
  have hc2 : 0 ≤ T * (9 * κ ^ 2 * N ^ 2) := by positivity
  exact add_nonneg (mul_nonneg hc1 hSD0)
    (mul_nonneg hc2 (add_nonneg hIQ0 (mul_nonneg (by norm_num) hIGf0)))

/-- The comparison for a given torus solution. -/
theorem davies_uPart {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow (streamVel φ) X) {t₁ T : ℝ} (ch : IsPipeChart (streamVel φ) X t₁ T) (hT : 0 < T)
    {b : ℝ → Vec 2 → Vec 2} (hbW : ∀ s e, IsWindowDrift b s e)
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) {Bb : ℝ} (hbB : ∀ t x, ‖b t x‖ ≤ Bb)
    (hb0s : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
    (hb0d : ∀ t x, divSp (streamVel φ t) x = 0) {V₀ : ℝ}
    (hc : LabelCoeffs (pipeMetric X t₁) (pipeDrift b (streamVel φ) X t₁) V₀ (t₁ - 8 * T) t₁)
    {R κ L₁ L₂ ca εV Kb : ℝ} (hR0 : 0 < R) (hR8 : R ≤ 1 / 8) (hκ : 0 < κ) (hL1 : 0 ≤ L₁)
    (hεV1 : εV ≤ 1) (hεV : εV ^ 2 ≤ ca ^ 2 / 12960)
    (hκT : κ * T ≤ R ^ 2) (hVT : V₀ * T ≤ εV * R) (hKb : 0 ≤ Kb)
    {χ η ψ : Vec 2 → ℝ} (hpack : CutoffPack R L₁ L₂ ca χ η ψ)
    {θ : ℝ → Vec 2 → ℝ} {DU : ℝ → Vec 2 → Vec 2}
    (hUw : MemLp (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hDUm : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (X t y t₁)) (DU t))
    (hweakc : ∀ ξ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R,
        (-(θ p.1 (X p.1 p.2 t₁) * stTimeDeriv ξ p) +
          vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) -
            θ p.1 (X p.1 p.2 t₁) • pipeDrift b (streamVel φ) X t₁ p) (stSpaceGrad ξ p)) = 0)
    {Wχ Wη : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R))}
    (hWχc : ContinuousOn Wχ (Set.Icc (t₁ - 8 * T) t₁))
    (hWχae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      (Wχ τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => χ y * θ τ (X τ y t₁))
    (hWχb : ∀ τ ∈ Set.Icc (t₁ - 8 * T + 2 * T) t₁, ‖Wχ τ‖ ^ 2 ≤ Kb)
    (hWηae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      (Wη τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => η y * θ τ (X τ y t₁))
    (hWηb : ∀ τ ∈ Set.Icc (t₁ - 8 * T + 2 * T) t₁, ‖Wη τ‖ ^ 2 ≤ Kb)
    (hWηg : κ * ∫ p in Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall 0 R,
      η p.2 ^ 2 * vecDot (DU p.1 p.2) ((pipeMetric X t₁ p).mulVec (DU p.1 p.2)) ≤ Kb)
    {v₀ : Vec 2 → ℝ}
    (hv₀ : v₀ =ᵐ[volume.restrict (euclidBall 0 R)] (Wχ (t₁ - 9 * T / 2) : Vec 2 → ℝ))
    (hf2 : MemL2On unitCube (datumFun X t₁ (t₁ - 9 * T / 2) v₀))
    (hEf : l2NormSq (datumFun X t₁ (t₁ - 9 * T / 2) v₀) ≤ 625 * Kb)
    (hperB : ∀ y ∈ euclidBall (0 : Vec 2) R, perX v₀ y = v₀ y)
    {u : ℝ → Vec 2 → ℝ}
    (hu : IsWeakSolutionOn b κ (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T)
      (datumFun X t₁ (t₁ - 9 * T / 2) v₀) u) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 9 * T / 2) t₁)),
      ∫ y in euclidBall 0 (R / 8), (θ τ (X τ y t₁) - u τ (X τ y t₁)) ^ 2 ≤
        Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * Kb) *
          Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T)))) := by
  have hR1 : R ≤ 1 := by linarith
  have hta : t₁ - 8 * T ≤ t₁ - 9 * T / 2 := by linarith
  have hs1 : t₁ - 9 * T / 2 < t₁ := by linarith
  have ht1 : t₁ ≤ t₁ - 9 * T / 2 + 5 * T := by linarith
  have hBo : IsOpen (euclidBall (0 : Vec 2) R) := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := hBo.measurableSet
  have hbp : ∀ t ∈ Set.Ioo (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T), IsZ2Periodic (b t) :=
    fun t ht => (hbW _ _).2.2.1 t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨Du, hD, -⟩ := isLocalWeakSolution_of_isWeakSolutionOn hbp hu
  obtain ⟨hUf, hDUf, hgUf, hqUf, hIUf, hIGf⟩ := uf_package hφ hX ch hT hta hs1 ht1 hD (hbW _ _)
    hf2 hκ hR0.le hR1 hbm hbB hb0s hb0d
  have hfper := datum_periodic hφ hX t₁ (t₁ - 9 * T / 2) (v := v₀)
  -- the initial datum
  have hinit : ∀ ρ : Vec 2 → ℝ, IsSpTest (euclidBall 0 R) ρ →
      ContinuousWithinAt (fun τ => ∫ y in euclidBall 0 R, Ufun u X t₁ (τ, y) * ρ y)
        (Set.Icc (t₁ - 9 * T / 2) t₁) (t₁ - 9 * T / 2) ∧
      ∫ y in euclidBall 0 R, Ufun u X t₁ (t₁ - 9 * T / 2, y) * ρ y =
        ∫ y in euclidBall 0 R, v₀ y * ρ y := by
    intro ρ hρ
    obtain ⟨hcont, hval⟩ := uf_initial hφ hX hD (by linarith) hs1.le ht1 hfper hf2 hρ.1 hρ.2.1
    have hB2 : ∀ g : Vec 2 → ℝ, ∫ y in euclidBall (0 : Vec 2) R, g y * ρ y = ∫ y, g y * ρ y :=
      fun g => setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        have : y ∉ tsupport ρ := fun h => hy (hρ.2.2 h)
        simp [image_eq_zero_of_notMem_tsupport this]
    refine ⟨hcont.congr (fun τ _ => hB2 _) (hB2 _), ?_⟩
    rw [hB2]
    refine (show ∫ y, Ufun u X t₁ (t₁ - 9 * T / 2, y) * ρ y =
      ∫ y, u (t₁ - 9 * T / 2) (X (t₁ - 9 * T / 2) y t₁) * ρ y from rfl).trans (hval.trans ?_)
    have e1 : ∫ y, datumFun X t₁ (t₁ - 9 * T / 2) v₀ (X (t₁ - 9 * T / 2) y t₁) * ρ y =
        ∫ y, perX v₀ y * ρ y :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [datum_apply hφ hX t₁ (t₁ - 9 * T / 2) y])
    rw [e1, ← hB2]
    exact setIntegral_congr_fun hBm fun y hy => by simp only [hperB y hy]
  -- restriction to the later window
  have hsub : Set.Ioo (t₁ - 9 * T / 2) t₁ ×ˢ euclidBall (0 : Vec 2) R ⊆
      Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R :=
    Set.prod_mono (Set.Ioo_subset_Ioo hta le_rfl) le_rfl
  have hmono := Measure.restrict_mono hsub (le_refl (volume : Measure (ℝ × Vec 2)))
  have hU' := hUw.mono_measure hmono
  have hDU' : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 9 * T / 2) t₁ ×ˢ euclidBall 0 R)) := fun i =>
    (hDUm i).mono_measure hmono
  have hgU' := ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo hta le_rfl) hgrad
  have hqU := nc_eq_restrict (a' := t₁ - 9 * T / 2) hta hBm
    (nonconservative_of_flux hc (U := fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁))
      (DU := fun p : ℝ × Vec 2 => DU p.1 p.2) hUw hDUm hgrad hweakc)
  have hlam : 0 < 1 / T := by positivity
  have hWχc' := hWχc.mono (Set.Icc_subset_Icc hta le_rfl)
  have hWχae' := ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo hta le_rfl) hWχae
  have hcomp := davies_compare (hc.mono hta le_rfl) hs1 (R := R) (κ := κ) (lam := 1 / T)
    (ℓ := ca / 90 * R / (κ * T)) (ca := ca) (N := L₁ / R) hκ hlam hU' hDU' hgU' hqU hUf hDUf
    hgUf hqUf hpack.hχ hpack.hχ1 (by positivity) hpack.hχN
    hpack.hη hpack.hη1 hpack.hηχ hpack.hψ hpack.hψ1 hpack.hP10 hpack.hP11 hpack.hP12 hWχc' hWχae'
    hv₀ hinit
  have hV₀ := hc.V0
  have hVT0 : 0 ≤ V₀ * T := by positivity
  have hVT1 : V₀ * T ≤ R := hVT.trans (by nlinarith)
  have hVT2 : (V₀ * T) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hVT0 hVT1 2
  have hVTε : (V₀ * T) ^ 2 ≤ ca ^ 2 / 12960 * R ^ 2 := by
    calc (V₀ * T) ^ 2 ≤ (εV * R) ^ 2 := pow_le_pow_left₀ hVT0 hVT 2
      _ = εV ^ 2 * R ^ 2 := by ring
      _ ≤ ca ^ 2 / 12960 * R ^ 2 := mul_le_mul_of_nonneg_right hεV (sq_nonneg R)
  obtain ⟨hsrc0, hsrc⟩ := srcBound_final (s₀ := t₁ - 9 * T / 2) hc hT hκ (by ring) hta hs1 hKb hκT hVT2
    (U := fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) (DU := fun p : ℝ × Vec 2 => DU p.1 p.2)
    (Uf := Ufun u X t₁) (DUf := DUfun Du X t₁) hUw hDUm hUf hpack.hη hpack.hη1 hWηae hWηb hWηg
    (Ef := l2NormSq (datumFun X t₁ (t₁ - 9 * T / 2) v₀)) (N := L₁ / R) hEf hIUf hIGf
  have hNR : (L₁ / R * R) ^ 2 = L₁ ^ 2 := by field_simp
  rw [hNR] at hsrc
  have hexp := exponent_alg (ca := ca) (R := R) hκ hT hVTε
  filter_upwards [hcomp] with τ hτ
  refine hτ.trans ?_
  have hWs : ‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 ≤ Kb := hWχb _ ⟨by linarith, hs1.le⟩
  have hZ : ‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 + srcBound (pipeMetric X t₁) V₀ κ (1 / T) (L₁ / R)
      (t₁ - 9 * T / 2) t₁ R η (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) (Ufun u X t₁)
      (fun p : ℝ × Vec 2 => DU p.1 p.2) (DUfun Du X t₁) ≤ (1 + 50000000 * L₁ ^ 2) * Kb := by
    nlinarith [hWs, hsrc]
  have hdec : 2 * decayRate κ (ca / 90 * R / (κ * T)) V₀ (1 / T) * (t₁ - (t₁ - 9 * T / 2)) =
      2 * (10 * κ * ((ca / 90 * R / (κ * T)) ^ 2) + 8 * V₀ ^ 2 / κ + (1 / T) / 2) * (9 * T / 2) := by
    unfold decayRate; ring
  rw [hdec]
  have hZ0 : 0 ≤ ‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 + srcBound (pipeMetric X t₁) V₀ κ (1 / T) (L₁ / R)
      (t₁ - 9 * T / 2) t₁ R η (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) (Ufun u X t₁)
      (fun p : ℝ × Vec 2 => DU p.1 p.2) (DUfun Du X t₁) := by
    exact add_nonneg (sq_nonneg _) hsrc0
  calc Real.exp (2 * (10 * κ * ((ca / 90 * R / (κ * T)) ^ 2) + 8 * V₀ ^ 2 / κ + (1 / T) / 2) *
        (9 * T / 2)) * (Real.exp (-(2 * (ca / 90 * R / (κ * T)) * (ca * R))) *
        (‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 + srcBound (pipeMetric X t₁) V₀ κ (1 / T) (L₁ / R)
          (t₁ - 9 * T / 2) t₁ R η (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) (Ufun u X t₁)
          (fun p : ℝ × Vec 2 => DU p.1 p.2) (DUfun Du X t₁)))
      = Real.exp (2 * (10 * κ * ((ca / 90 * R / (κ * T)) ^ 2) + 8 * V₀ ^ 2 / κ + (1 / T) / 2) *
        (9 * T / 2) - 2 * (ca / 90 * R / (κ * T)) * (ca * R)) *
        (‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 + srcBound (pipeMetric X t₁) V₀ κ (1 / T) (L₁ / R)
          (t₁ - 9 * T / 2) t₁ R η (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) (Ufun u X t₁)
          (fun p : ℝ × Vec 2 => DU p.1 p.2) (DUfun Du X t₁)) := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2
    _ ≤ Real.exp (9 / 2 - ca ^ 2 / 180 * (R ^ 2 / (κ * T))) * ((1 + 50000000 * L₁ ^ 2) * Kb) := by
        apply mul_le_mul (Real.exp_le_exp.2 hexp) hZ hZ0 (Real.exp_pos _).le
    _ = Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * Kb) *
          Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T)))) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-- **Localization in the chart**: the estimate of Lemma 8.3 of the paper in the label coordinates
of a pipe chart. -/
theorem davies_chart {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow (streamVel φ) X) {t₁ T : ℝ} (ch : IsPipeChart (streamVel φ) X t₁ T) (hT : 0 < T)
    {b : ℝ → Vec 2 → Vec 2} (hbW : ∀ s e, IsWindowDrift b s e)
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) {Bb : ℝ} (hbB : ∀ t x, ‖b t x‖ ≤ Bb)
    (hb0s : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
    (hb0d : ∀ t x, divSp (streamVel φ t) x = 0) {V₀ : ℝ}
    (hc : LabelCoeffs (pipeMetric X t₁) (pipeDrift b (streamVel φ) X t₁) V₀ (t₁ - 8 * T) t₁)
    {R κ L₁ L₂ ca εV C : ℝ} (hR0 : 0 < R) (hR8 : R ≤ 1 / 8) (hκ : 0 < κ) (hL1 : 0 ≤ L₁)
    (hL2 : 0 ≤ L₂) (hεV1 : εV ≤ 1) (hεV : εV ^ 2 ≤ ca ^ 2 / 12960)
    (hκT : κ * T ≤ R ^ 2) (hVT : V₀ * T ≤ εV * R)
    (hC1 : 25 * Real.sqrt (16 + 288 * (L₁ + L₂) ^ 2 + 64 * (L₁ + L₂)) ≤ C)
    (hC2 : Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) *
      (16 + 288 * (L₁ + L₂) ^ 2 + 64 * (L₁ + L₂))) ≤ C ^ 2)
    {χ η ψ : Vec 2 → ℝ} (hpack : CutoffPack R L₁ L₂ ca χ η ψ)
    {θ : ℝ → Vec 2 → ℝ}
    (hθ2 : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R)))
    {DU : ℝ → Vec 2 → Vec 2}
    (hDUm : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (X t y t₁)) (DU t))
    (hweakc : ∀ ξ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R,
        (-(θ p.1 (X p.1 p.2 t₁) * stTimeDeriv ξ p) +
          vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) -
            θ p.1 (X p.1 p.2 t₁) • pipeDrift b (streamVel φ) X t₁ p) (stSpaceGrad ξ p)) = 0) :
    ∃ f : Vec 2 → ℝ, MemL2On unitCube f ∧
      Real.sqrt (l2NormSq f) ≤ C * R * pipeAmp X t₁ T R θ ∧
      ∀ u : ℝ → Vec 2 → ℝ,
        IsWeakSolutionOn b κ (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T) f u →
        ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 9 * T / 2) t₁)),
          ∫ y in euclidBall 0 (R / 8), (θ t (X t y t₁) - u t (X t y t₁)) ^ 2 ≤
            (C * R * pipeAmp X t₁ T R θ * Real.exp (-(ca ^ 2 / 360) * R ^ 2 / (κ * T))) ^ 2 := by
  set A := pipeAmp X t₁ T R θ with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hUw := pipe_U_memLp ch hT hθ2
  have hM := amp_bound ch hT hR0 θ
  have hV₀ := hc.V0
  have hVT1 : V₀ * T ≤ R := hVT.trans (by nlinarith)
  set K₀ : ℝ := 16 + 288 * (L₁ + L₂) ^ 2 + 64 * (L₁ + L₂) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 25 * Real.sqrt K₀).trans hC1
  set Kb : ℝ := K₀ * (R ^ 2 * A ^ 2) with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  obtain ⟨Wχ, hWχc, hWχae, hWχb, -⟩ := davies_traces hc hT hκ hR0 hUw hDUm hgrad hweakc
    hpack.hχ (fun y => (hpack.hχ1 y).1) (fun y => (hpack.hχ1 y).2) hL1 (Lm := L₁ + L₂)
    (by linarith) hpack.hχN hM hκT hVT1
  obtain ⟨Wη, hWηc, hWηae, hWηb, hWηg⟩ := davies_traces hc hT hκ hR0 hUw hDUm hgrad hweakc
    hpack.hη (fun y => (hpack.hη1 y).1) (fun y => (hpack.hη1 y).2) hL2 (Lm := L₁ + L₂)
    (by linarith) hpack.hηN hM hκT hVT1
  have hWs : ‖Wχ (t₁ - 9 * T / 2)‖ ^ 2 ≤ Kb := hWχb _ ⟨by linarith, by linarith⟩
  obtain ⟨v₀, hv₀ae, hf2, hfl, hfper, hperB⟩ := davies_datum hφ hX t₁ (t₁ - 9 * T / 2) hR0 hR8
    (Wχ (t₁ - 9 * T / 2)) hWs
  refine ⟨datumFun X t₁ (t₁ - 9 * T / 2) v₀, hf2, ?_, fun u hu => ?_⟩
  · refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h1 : 25 * Real.sqrt K₀ * R * A ≤ C * R * A := by
      have := mul_nonneg hR0.le hA0
      nlinarith
    have h2 : (25 * Real.sqrt K₀ * R * A) ^ 2 = 625 * Kb := by
      rw [hKb]; rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK₀0]; ring
    calc l2NormSq (datumFun X t₁ (t₁ - 9 * T / 2) v₀) ≤ 625 * Kb := hfl
      _ = (25 * Real.sqrt K₀ * R * A) ^ 2 := h2.symm
      _ ≤ (C * R * A) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h1
  · have hεVu := davies_uPart hφ hX ch hT hbW hbm hbB hb0s hb0d hc hR0 hR8 hκ hL1 hεV1 hεV hκT hVT
      hKb0 hpack hUw hDUm hgrad hweakc hWχc hWχae hWχb hWηae hWηb hWηg hv₀ae hf2 hfl hperB hu
    filter_upwards [hεVu] with τ hτ
    refine hτ.trans ?_
    have hE : Real.exp (-(ca ^ 2 / 360) * R ^ 2 / (κ * T)) ^ 2 =
        Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T)))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hKbe : Kb = K₀ * (R ^ 2 * A ^ 2) := rfl
    calc Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * Kb) *
          Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T))))
        = (Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀)) * (R ^ 2 * A ^ 2) *
          Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T)))) := by rw [hKbe]; ring
      _ ≤ C ^ 2 * (R ^ 2 * A ^ 2) * Real.exp (-(ca ^ 2 / 180 * (R ^ 2 / (κ * T)))) := by
        gcongr
      _ = (C * R * A * Real.exp (-(ca ^ 2 / 360) * R ^ 2 / (κ * T))) ^ 2 := by
        rw [mul_pow, hE]; ring

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Filter Topology
namespace AVRegularity.Applications

/-! # Localization for the construction (Lemma 8.3 of the paper)

`davies_holds` proves `DaviesStmt α q Λ Φ b`. -/

section
section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- **Localization for the construction.** Lemma 8.3 of the paper follows from it. -/
theorem davies_holds (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    DaviesStmt α q Λ Φ b := by
  obtain ⟨C₂, hC₂0, hcoef⟩ := pipe_coeff_bounds_uniform α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  obtain ⟨L₁, L₂, ca, hL1, hL2, hca, hca1, hcut⟩ := Davies.exists_cutoffPack
  set K₀ : ℝ := 16 + 288 * (L₁ + L₂) ^ 2 + 64 * (L₁ + L₂) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  set C : ℝ := max (25 * Real.sqrt K₀)
    (Real.sqrt (Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀))) with hC
  have hC1 : 25 * Real.sqrt K₀ ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 25 * Real.sqrt K₀).trans hC1
  have hC2 : Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀) ≤ C ^ 2 := by
    have h1 : Real.sqrt (Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀)) ≤ C := le_max_right _ _
    have h2 : 0 ≤ Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀) := by positivity
    calc _ = Real.sqrt (Real.exp (9 / 2) * ((1 + 50000000 * L₁ ^ 2) * K₀)) ^ 2 :=
          (Real.sq_sqrt h2).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hCb0 : 0 < 1 + 114 * C₂ / ca := by positivity
  refine ⟨1 + 114 * C₂ / ca, C, ca ^ 2 / 360, hCb0, hC0, by positivity, ?_⟩
  intro n hn X hX t₁ T R κ hT hR hR8 hκ hh hb1 hb2 θ hθ
  have hφ := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ (n - 2)
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT hh
  obtain ⟨hell, hdrift, hsymm, -, hGm, hVm, hdiv⟩ := hcoef n hn X hX t₁ T hT hh
  have hεpos : 0 < ocEpsilon q Λ (n - 1) := AVRegularity.Construction.Stream.ocEpsilon_pos (by omega)
  have hεα : 0 ≤ ocEpsilon q Λ (n - 1) ^ α := Real.rpow_nonneg hεpos.le _
  have hV₀ : 0 ≤ C₂ * ocEpsilon q Λ (n - 1) ^ α := mul_nonneg hC₂0 hεα
  have hc : Davies.LabelCoeffs (pipeMetric X t₁)
      (pipeDrift b (streamVel (Φ (n - 2))) X t₁) (C₂ * ocEpsilon q Λ (n - 1) ^ α)
      (t₁ - 8 * T) t₁ :=
    ⟨hsymm, fun p hp e => (hell p.1 hp p.2 e).1, fun p hp e => (hell p.1 hp p.2 e).2, hGm, hVm,
      hV₀, fun p hp => hdrift p.1 hp p.2, fun t ht ψ hψ hψc => hdiv t ht ψ hψ hψc⟩
  obtain ⟨hbm, ⟨Bb, hbB⟩, -⟩ := limit_velocity_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  have hbW := fun t₁' t₂' => Davies.limit_window_drift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b
    hb t₁' t₂'
  obtain ⟨hb0s, hb0d⟩ := Davies.approx_velocity_facts α q ζ hζ Λ hΛ Φ hΦ (n - 2)
  obtain ⟨χ, η, ψ, hpack⟩ := hcut R hR
  obtain ⟨DU, hDUm, hgrad, hweakc⟩ := pipe_pullback_weak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b
    hb n hn X hX t₁ T hT hh hκ hR hθ
  -- the buffers
  have hκT : κ * T ≤ R ^ 2 := by
    have h1 : Real.sqrt (κ * T) ≤ R := by
      have hCb1 : 1 ≤ 1 + 114 * C₂ / ca := by
        have : 0 ≤ 114 * C₂ / ca := by positivity
        linarith
      have := Real.sqrt_nonneg (κ * T)
      nlinarith
    have h2 := Real.sq_sqrt (show 0 ≤ κ * T by positivity)
    nlinarith [Real.sqrt_nonneg (κ * T)]
  have hVT : C₂ * ocEpsilon q Λ (n - 1) ^ α * T ≤ ca / 114 * R := by
    set Cb : ℝ := 1 + 114 * C₂ / ca with hCbd
    have h1 : C₂ ≤ ca / 114 * Cb := by
      have : ca / 114 * Cb = ca / 114 + C₂ := by rw [hCbd]; field_simp
      rw [this]; linarith
    have h2 : Cb * (C₂ * ocEpsilon q Λ (n - 1) ^ α * T) ≤ C₂ * R := by
      calc Cb * (C₂ * ocEpsilon q Λ (n - 1) ^ α * T) =
          C₂ * (Cb * (ocEpsilon q Λ (n - 1) ^ α * T)) := by ring
        _ ≤ C₂ * R := mul_le_mul_of_nonneg_left hb1 hC₂0
    have h3 : Cb * (C₂ * ocEpsilon q Λ (n - 1) ^ α * T) ≤ Cb * (ca / 114 * R) := by
      calc _ ≤ C₂ * R := h2
        _ ≤ ca / 114 * Cb * R := mul_le_mul_of_nonneg_right h1 hR.le
        _ = Cb * (ca / 114 * R) := by ring
    exact le_of_mul_le_mul_left h3 hCb0
  have hεV : (ca / 114) ^ 2 ≤ ca ^ 2 / 12960 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg ca) (by norm_num) (by norm_num)
  exact Davies.davies_chart hφ hX ch hT hbW hbm hbB hb0s hb0d hc hR hR8 hκ hL1 hL2
    (by linarith) hεV hκT hVT hC1 hC2 hpack hθ.1 hDUm hgrad hweakc

end Construction
end

/-! # Local `L²` traces from below of the pulled-back slices

`localTrace_holds` proves `LocalTraceStmt α q Λ Φ b`: for `ρ < R` and `t ∈ (t₁ - 6T, t₁]` the
slices `θ(r, F_r ·)` converge in `L²(B_ρ)` as `r ↑ t` (outside a null set of times), via the
continuous trace of the cutoff energy identity. -/

section
section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

theorem localTrace_holds (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    LocalTraceStmt α q Λ Φ b := by
  intro n hn X hX t₁ T R κ hT hR hR8 hκ hh θ hθ ρ hρ0 hρR t ht
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT hh
  obtain ⟨C₂, hC₂0, hcoef⟩ := pipe_coeff_bounds_uniform α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  obtain ⟨hell, hdrift, hsymm, -, hGm, hVm, hdiv⟩ := hcoef n hn X hX t₁ T hT hh
  have hεpos : 0 < ocEpsilon q Λ (n - 1) := AVRegularity.Construction.Stream.ocEpsilon_pos (by omega)
  have hV₀ : 0 ≤ C₂ * ocEpsilon q Λ (n - 1) ^ α :=
    mul_nonneg hC₂0 (Real.rpow_nonneg hεpos.le _)
  have hc : Davies.LabelCoeffs (pipeMetric X t₁)
      (pipeDrift b (streamVel (Φ (n - 2))) X t₁) (C₂ * ocEpsilon q Λ (n - 1) ^ α)
      (t₁ - 8 * T) t₁ :=
    ⟨hsymm, fun p hp e => (hell p.1 hp p.2 e).1, fun p hp e => (hell p.1 hp p.2 e).2, hGm, hVm,
      hV₀, fun p hp => hdrift p.1 hp p.2, fun t ht ψ hψ hψc => hdiv t ht ψ hψ hψc⟩
  obtain ⟨DU, hDUm, hgrad, hweakc⟩ := pipe_pullback_weak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b
    hb n hn X hX t₁ T hT hh hκ hR hθ
  have hUw := pipe_U_memLp ch hT hθ.1
  have hab : t₁ - 8 * T < t₁ := by linarith
  -- the cutoff
  set a : ℝ := ρ / R with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one hR]; exact hρR
  set bb : ℝ := (a + 1) / 2 with hbb
  have hab' : a < bb := by rw [hbb]; linarith
  have hbb1 : bb < 1 := by rw [hbb]; linarith
  set η : Vec 2 → ℝ := Davies.prof a bb R with hη
  have hηtest : IsSpTest (euclidBall 0 R) η := by
    refine ⟨Davies.prof_contDiff _ _ _, Davies.prof_hasCompactSupport hR hab' ha0.le, ?_⟩
    intro y hy
    have := Davies.prof_tsupport hR hab' ha0.le hy
    simp only [Set.mem_ofPred_eq] at this
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero]
    have h0 : bb * R < R := by nlinarith
    have h1 : (bb * R) ^ 2 < R ^ 2 :=
      pow_lt_pow_left₀ h0 (by positivity) (by norm_num)
    linarith
  have hη1 : ∀ y, |η y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (Davies.prof_nonneg _ _ _ _)]; exact Davies.prof_le_one _ _ _ _
  obtain ⟨N, hN0, hN⟩ := exists_grad_bound hηtest.1 hηtest.2.1
  obtain ⟨W, hWc, hWae, -⟩ := Davies.cutoff_energy_identity hc hab hUw hDUm hgrad hweakc hηtest
    hη1 hN0 hN
  refine ⟨fun y => (W t : Vec 2 → ℝ) y, ?_, ?_⟩
  · have hB : euclidBall (0 : Vec 2) ρ ⊆ euclidBall (0 : Vec 2) R := by
      intro y hy
      simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at hy ⊢
      nlinarith [sq_nonneg ρ]
    exact (Lp.memLp (W t)).mono_measure (Measure.restrict_mono hB le_rfl)
  · have ht' : t₁ - 8 * T < t := by linarith [ht.1]
    have hIcc : Set.Icc (t₁ - 8 * T) t₁ ∈ 𝓝[<] t :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT ht') (fun r hr => ⟨hr.1.le, hr.2.le.trans ht.2⟩)
    have hle : 𝓝[<] t ≤ 𝓝[Set.Icc (t₁ - 8 * T) t₁] t := nhdsWithin_le_iff.2 hIcc
    have hdist : Tendsto (fun r => dist (W r) (W t)) (𝓝[<] t) (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 (((hWc t ⟨ht'.le, ht.2⟩).tendsto).mono_left hle)
    have hsq : Tendsto (fun r => dist (W r) (W t) ^ 2) (𝓝[<] t ⊓ ae (volume : Measure ℝ))
        (𝓝 0) := by
      have := (hdist.pow 2).mono_left (inf_le_left : 𝓝[<] t ⊓ ae (volume : Measure ℝ) ≤ 𝓝[<] t)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
      (Filter.Eventually.of_forall fun r => integral_nonneg fun y => sq_nonneg _) ?_
    have hmemIoo : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Set.Ioo (t₁ - 8 * T) t₁ := by
      have : Set.Ioo (t₁ - 8 * T) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht'
      have h2 : ∀ᶠ r in 𝓝[<] t, r ∈ Set.Ioo (t₁ - 8 * T) t₁ :=
        Filter.mem_of_superset this fun r hr => ⟨hr.1, hr.2.trans_le ht.2⟩
      exact h2.filter_mono inf_le_left
    have hae : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), (W r : Vec 2 → ℝ) =ᵐ[volume.restrict
        (euclidBall (0 : Vec 2) R)] fun y => η y * θ r (X r y t₁) := by
      have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hWae
      have h3 : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Set.Ioo (t₁ - 8 * T) t₁ →
          (W r : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall (0 : Vec 2) R)]
            fun y => η y * θ r (X r y t₁) := Filter.Eventually.filter_mono inf_le_right h1
      filter_upwards [h3, hmemIoo] with r h4 h5 using h4 h5
    filter_upwards [hae] with r hr
    have hB : euclidBall (0 : Vec 2) ρ ⊆ euclidBall (0 : Vec 2) R := by
      intro y hy
      simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at hy ⊢
      nlinarith [sq_nonneg ρ]
    have hBm : MeasurableSet (euclidBall (0 : Vec 2) ρ) := (pipe_isOpen_euclidBall 0 ρ).measurableSet
    have hBRm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
    have hrB : (W r : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall (0 : Vec 2) ρ)]
        fun y => θ r (X r y t₁) := by
      have h6 : (W r : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall (0 : Vec 2) ρ)]
          fun y => η y * θ r (X r y t₁) := ae_mono (Measure.restrict_mono hB le_rfl) hr
      refine h6.trans ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' hBm]
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy2 : vecNormSq y ≤ (a * R) ^ 2 := by
        have : vecNormSq (y - 0) < ρ ^ 2 := by simpa [euclidBall] using hy
        have e : a * R = ρ := by rw [ha]; field_simp
        rw [e]; simpa using this.le
      have : η y = 1 := Davies.prof_eq_one hR hab' ha0.le hy2
      simp [this]
    have hsq2 : ∫ y in euclidBall (0 : Vec 2) ρ, (θ r (X r y t₁) - (W t : Vec 2 → ℝ) y) ^ 2 =
        ∫ y in euclidBall (0 : Vec 2) ρ, ((W r : Vec 2 → ℝ) y - (W t : Vec 2 → ℝ) y) ^ 2 :=
      integral_congr_ae (hrB.mono fun y hy => by simp only [hy])
    rw [hsq2]
    have hint : Integrable (fun y => ((W r : Vec 2 → ℝ) y - (W t : Vec 2 → ℝ) y) ^ 2)
        (volume.restrict (euclidBall (0 : Vec 2) R)) :=
      ((Lp.memLp (W r)).sub (Lp.memLp (W t))).integrable_sq
    calc ∫ y in euclidBall (0 : Vec 2) ρ, ((W r : Vec 2 → ℝ) y - (W t : Vec 2 → ℝ) y) ^ 2
        ≤ ∫ y in euclidBall (0 : Vec 2) R, ((W r : Vec 2 → ℝ) y - (W t : Vec 2 → ℝ) y) ^ 2 :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => sq_nonneg _)
            (Filter.Eventually.of_forall hB)
      _ = dist (W r) (W t) ^ 2 := LocalEnergy.integral_sq_sub_lp (W r) (W t)

end Construction
end

end AVRegularity.Applications
end
