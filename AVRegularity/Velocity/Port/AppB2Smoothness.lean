-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.AppB2FieldBounds
public import AVenhance.Infra.Section4.Amnr.FlowSpatialSourceRates
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.FaaDiBruno.Composition
import AVenhance.Infra.FaaDiBruno.TransportSharpEstimate
import AVenhance.Infra.FaaDiBruno.TransportTimeAnalyticity
import AVenhance.Infra.Section4.Amnr.Cutoff
import AVenhance.Infra.Section4.Amnr.FlowSpatialJetRates
import AVenhance.Infra.Section4.Amnr.SpatialCommutator
import AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds
import AVenhance.Infra.Section4.Amnr.SpatialPrimitive
import AVenhance.Infra.Section4.Amnr.VelocityHigherRates
import AVenhance.Infra.Section4.Amnr.VelocitySecondRates
import AVenhance.Infra.Section4.Amnr.VelocitySpatial
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
open AVenhance AVenhance.Infra.Flow
open AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity.Port.MaterialAuxiliaryFlow

/-! Auxiliary spatial flow orders for the finite material word budget. -/

/-- The flow-window bound follows from the time-scale facts and
the block-smallness field. -/
theorem cutoff_window_fits_flow
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m) :
    D.tauPP m / 2 + D.tauP m ≤
      (2 : ℝ) ^ (-25 : ℤ) * (D.velocityAmplitude (m - 1))⁻¹ := by
  let facts := AVRegularity.Scales.admissible_time_scale_facts
    D.hαpos D.hαlt D.hspos D.hslt D.hq D.hΛ hm
  have hratio : D.tauPP m / D.tauP m = (ocL α q Λ m : ℝ) := by
    simpa [D.tauPP_eq_oc, D.tauP_eq_oc] using facts.2.2.2.2.2.2.2.1
  have hL : 5 ≤ ocL α q Λ m := facts.1
  have htp : 0 < D.tauP m := D.tauP_pos m hm
  have hpp : 0 < D.tauPP m := D.tauPP_pos m hm
  have hratio' : 0 < D.tauPP m / D.tauP m := div_pos hpp htp
  have htpLe : D.tauP m ≤ D.tauPP m / 5 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    have hLr : (5 : ℝ) ≤ D.tauPP m / D.tauP m := by
      rw [hratio]
      exact_mod_cast hL
    have hmul := mul_le_mul_of_nonneg_right hLr htp.le
    have hmul' : 5 * D.tauP m ≤ D.tauPP m := by
      calc
        5 * D.tauP m ≤ (D.tauPP m / D.tauP m) * D.tauP m := hmul
        _ = D.tauPP m := by field_simp
    linarith
  have hwindow : D.tauPP m / 2 + D.tauP m ≤ D.tauPP m := by
    linarith
  have hblock := D.block_small m hm
  have heprev : 0 < D.epsilon (m - 1) := D.epsilon_pos _
  have heleprev : D.epsilon (m - 1) ≤ 1 := D.epsilon_le_one _
  have hexp : 0 < 2 * AVRegularity.ocDelta α q := by
    have hfacts := AVRegularity.Scales.admissible_exponent_facts
      D.hαpos D.hαlt D.hspos D.hslt D.hq
    linarith [hfacts.2.1]
  have hpow : D.epsilon (m - 1) ^ (2 * AVRegularity.ocDelta α q) ≤ 1 :=
    Real.rpow_le_one heprev.le heleprev hexp.le
  have hA : 0 < D.velocityAmplitude (m - 1) := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos heprev _
  have hblock' : D.velocityAmplitude (m - 1) * D.tauPP m ≤
      (2 : ℝ) ^ (-25 : ℤ) := by
    calc
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 :=
        hblock.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = _ := by ring
  have hwindow' : D.velocityAmplitude (m - 1) *
      (D.tauPP m / 2 + D.tauP m) ≤ (2 : ℝ) ^ (-25 : ℤ) :=
    (mul_le_mul_of_nonneg_left hwindow hA.le).trans hblock'
  apply (le_div_iff₀ hA).2
  simpa [mul_comm] using hwindow'

/-- The pointwise source stream seminorm supplies the coordinate spatial
word bound at every finite auxiliary order. -/
theorem stream_spatial_word_raw_of_regularity
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ)
    (word : List (Fin 2)) (hword : 2 ≤ word.length) (x : Vec 2) :
    ‖amnrSpaceWord word (Φ m t) x‖ ≤
      amnrStreamSpatialEnvelope (D.velocityAmplitude m) (D.epsilon m) word.length := by
  have hE : 0 < D.epsilon m := D.epsilon_pos m
  have hA : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos hE _
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1.comp
      (contDiff_const.prodMk contDiff_id)
  exact amnrSpaceWord_norm_le_of_barNorm hf word (by positivity) (by positivity)
    ((hreg m hm t).2.1 word.length hword) x

/-- The exact source envelope for spatial derivatives of the velocity
gradient, with the stream seminorm translated to `D.epsilon`. -/
theorem velocityGradient_spatial_word_raw_of_regularity
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (word : List (Fin 2))
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ m) y.1 y.2) (word.map some)
      (amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2) i p) z| ≤
      amnrStreamSpatialEnvelope (D.velocityAmplitude m) (D.epsilon m)
        (word.length + 2) := by
  have hb := (AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)).smooth
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2) i p) :=
    contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ
      hb.contDiffOn i p)
  rw [amnrWord_spatial_slice hB]
  fin_cases i
  · change ‖amnrSpaceWord word
      (fun y => amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2)
        (0 : Fin 2) p (z.1, y)) z.2‖ ≤ _
    rw [amnrVelocityGradient_stream_zero, amnrSpaceWord_const_smul]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul]
    rw [← amnrSpaceWord_append]
    have hspace := stream_spatial_word_raw_of_regularity hseq hreg hm
      z.1 (word ++ [p, 1]) (by simp) z.2
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Real.norm_eq_abs] using hspace
  · change ‖amnrSpaceWord word
      (fun y => amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2)
        (1 : Fin 2) p (z.1, y)) z.2‖ ≤ _
    rw [amnrVelocityGradient_stream_one, ← amnrSpaceWord_append]
    have hspace := stream_spatial_word_raw_of_regularity hseq hreg hm
      z.1 (word ++ [p, 0]) (by simp) z.2
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Real.norm_eq_abs] using hspace

/-- Uniform source constant for all coordinate derivatives of the preceding
scale velocity Jacobian. -/
theorem velocityGradient_spatial_bound_of_regularity
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ) {m N : ℕ} (hm : 1 ≤ m)
    (word : List (Fin 2)) (hbudget : word.length ≤ N)
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ m) y.1 y.2) (word.map some)
      (amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant N * D.velocityAmplitude m *
        (D.epsilon m)⁻¹ ^ word.length := by
  have hA : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
  have hraw := velocityGradient_spatial_word_raw_of_regularity
    hseq hreg hm word i p z
  have hh := hraw.trans (amnrStreamSpatialEnvelope_le_uniform hA.le
    (D.epsilon_pos m) (show word.length ≤ N by omega))
  simpa only [Real.norm_eq_abs] using hh

/-- Coordinate primitive gradients obey the source spatial estimate at every
finite auxiliary order. This is the exact input consumed by the material word
induction. -/
theorem velocityGradient_spatial_le_of_A3_auxiliary_budget
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (word : List (Fin 2)) (N : ℕ) (hbudget : word.length ≤ N)
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ m) y.1 y.2) (word.map some)
      (amnrVelocityGradient (fun y => streamVel (Φ m) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant N * D.velocityAmplitude m *
        (D.epsilon m)⁻¹ ^ word.length :=
  velocityGradient_spatial_bound_of_regularity hseq hreg hm word hbudget i p z

/-- The preceding-scale spatial primitive estimate retains the current
source amplitude and every finite auxiliary spatial budget. -/
theorem previous_velocityGradient_spatial_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ) {m N : ℕ} (hm : 1 ≤ m)
    (word : List (Fin 2)) (hbudget : word.length ≤ N)
    (i p : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) (word.map some)
      (amnrVelocityGradient (fun y => streamVel (Φ (m - 1)) y.1 y.2) i p) z| ≤
      amnrSpatialVelocityConstant N * D.velocityAmplitude (m - 1) *
        (D.epsilon (m - 1))⁻¹ ^ word.length := by
  have hE : 0 < D.epsilon (m - 1) := D.epsilon_pos _
  have hA : 0 < D.velocityAmplitude (m - 1) := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos hE _
  by_cases hbase : m = 1
  · subst m
    have hB : amnrVelocityGradient
        (fun y => streamVel (Φ (1 - 1)) y.1 y.2) i p = (0 : AmnrSpace → ℝ) := by
      funext y
      rw [show 1 - 1 = (0 : ℕ) by omega, hseq.1]
      simp [amnrVelocityGradient, streamVel, AVenhance.spaceGrad]
    rw [hB, amnrWord_zero]
    simp only [Pi.zero_apply, abs_zero]
    have hK : 0 < amnrSpatialVelocityConstant N := amnrSpatialVelocityConstant_pos N
    have hE : 0 < D.epsilon (1 - 1) := D.epsilon_pos _
    have hA : 0 < D.velocityAmplitude (1 - 1) := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos hE _
    positivity
  · have hprev : 1 ≤ m - 1 := by omega
    exact velocityGradient_spatial_bound_of_regularity hseq hreg hprev word
      (by omega) i p z

/-- Coordinate spatial words give the operator norm of every preceding-scale
velocity-gradient jet. -/
theorem previous_velocityGradient_iteratedFDeriv_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (n N : ℕ) (hbudget : n ≤ N) (i p : Fin 2) (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
      (fun y => amnrVelocityGradient
        (fun z => streamVel (Φ (m - 1)) z.1 z.2) i p (t, y)) x‖ ≤
      (2 : ℝ) ^ n * (amnrSpatialVelocityConstant N *
        D.velocityAmplitude (m - 1) * (D.epsilon (m - 1))⁻¹ ^ n) := by
  let b := fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1))).smooth
  have hB : ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient b i p) :=
    contDiffOn_univ.mp (amnrVelocityGradient_contDiffOn_infty isOpen_univ
      hb.contDiffOn i p)
  apply amnr_iteratedFDeriv_norm_le_of_spatial_words
    (hB.comp (contDiff_const.prodMk contDiff_id)) n x
  · have hA : 0 < D.velocityAmplitude (m - 1) := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
    have hK : 0 < amnrSpatialVelocityConstant N := amnrSpatialVelocityConstant_pos N
    have hE : 0 < D.epsilon (m - 1) := D.epsilon_pos _
    positivity
  intro word hlen
  have hwordBudget : word.length ≤ N := by omega
  have hh := previous_velocityGradient_spatial_bound (D := D) (C := C)
    (m := m) (N := N) hseq hreg hm word hwordBudget i p (t, x)
  rw [amnrWord_spatial_slice hB, hlen] at hh
  simpa [Function.comp_def] using hh

/-- Uniform source constant for all coordinate derivatives of the preceding
scale velocity Jacobian. -/
theorem previous_velocityJacobian_iteratedFDeriv_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (n N : ℕ) (hnN : n ≤ N)
    (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
      (fun y => jointSpatialFDeriv (streamVel (Φ (m - 1))) t y) x‖ ≤
      (2 : ℝ) ^ (n + 1) * (amnrSpatialVelocityConstant N *
        D.velocityAmplitude (m - 1) * (D.epsilon (m - 1))⁻¹ ^ n) := by
  let Q := amnrSpatialVelocityConstant N * D.velocityAmplitude (m - 1) *
    (D.epsilon (m - 1))⁻¹ ^ n
  have hQ : 0 ≤ Q := by
    have hA : 0 < D.velocityAmplitude (m - 1) := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
    dsimp [Q]
    exact mul_nonneg
      (mul_nonneg (amnrSpatialVelocityConstant_pos N).le hA.le)
      (pow_nonneg (inv_nonneg.mpr (D.epsilon_pos _).le) _)
  have htarget : 0 ≤ 2 * ((2 : ℝ) ^ n * Q) :=
    mul_nonneg (by norm_num) (mul_nonneg (by positivity) hQ)
  have hcoeff : (2 : ℝ) ^ (n + 1) *
      (amnrSpatialVelocityConstant N * D.velocityAmplitude (m - 1) *
        (D.epsilon (m - 1))⁻¹ ^ n) = 2 * ((2 : ℝ) ^ n * Q) := by
    dsimp [Q]
    rw [pow_succ]
    ring
  rw [hcoeff]
  apply ContinuousMultilinearMap.opNorm_le_bound htarget
  intro v
  have hP : 0 ≤ ∏ j : Fin n, ‖v j‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hh : ‖iteratedFDeriv ℝ n
      (fun y => jointSpatialFDeriv (streamVel (Φ (m - 1))) t y) x v‖ ≤
      2 * ((2 : ℝ) ^ n * Q * ∏ j : Fin n, ‖v j‖) := by
    apply amnr_clm_norm_le_two_basis_general (by positivity)
    intro p
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs, amnr_velocityJacobian_iteratedFDeriv_coordinate
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)))]
    have hc := previous_velocityGradient_iteratedFDeriv_bound
      hseq hreg hm n N hnN i p t x
    have he := (iteratedFDeriv ℝ n
      (fun y => amnrVelocityGradient
        (fun z => streamVel (Φ (m - 1)) z.1 z.2) i p (t, y)) x).le_opNorm v
    rw [Real.norm_eq_abs] at he
    exact he.trans (mul_le_mul_of_nonneg_right hc hP)
  exact hh.trans_eq (by ring)

/-- The stream seminorm controls the Lipschitz constant of its velocity. -/
theorem previous_velocityJacobian_norm_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {D : JetRecursionData α s q Λ ζ}
    {C : ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖jointSpatialFDeriv (streamVel (Φ (m - 1))) t x‖ ≤
      (2 : ℝ) ^ 20 * D.velocityAmplitude (m - 1) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1))
  rw [jointSpatialFDeriv_eq_slice hb]
  have hA : 0 < D.velocityAmplitude (m - 1) := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
  by_cases hbase : m = 1
  · subst m
    have hzero : streamVel (Φ (1 - 1)) t = (fun _ => (0 : Vec 2)) := by
      rw [show 1 - 1 = (0 : ℕ) by omega, hseq.1]
      funext x
      simp [streamVel, AVenhance.spaceGrad]
    rw [hzero]
    change ‖fderiv ℝ (fun _ : Vec 2 => (0 : Vec 2)) x‖ ≤ _
    rw [(hasFDerivAt_const (0 : Vec 2) x).fderiv, norm_zero]
    positivity
  · have hprev : 1 ≤ m - 1 := by omega
    have hE : 0 < D.epsilon (m - 1) := D.epsilon_pos _
    have hAprev : 0 < D.velocityAmplitude (m - 1) := hA
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (Φ (m - 1) t) :=
      (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).1.comp
        (contDiff_const.prodMk contDiff_id)
    have hH : ∀ y (J : Fin 2 → Fin 2),
        ‖iteratedFDeriv ℝ 2 (Φ (m - 1) t) y
          (fun j => basisVec (J j))‖ ≤ 2 ^ 19 * D.velocityAmplitude (m - 1) := by
      intro y J
      have hbar := (hreg (m - 1) hprev t).2.1 2 (by norm_num)
      have hpoint := amnr_partial_norm_le_of_barNorm (Φ (m - 1) t) 2
        (hsmooth.of_le (by simp))
        (R := 2 ^ 8 * (D.epsilon (m - 1))⁻¹)
        (B := 2 ^ 5 * D.velocityAmplitude (m - 1) *
          D.epsilon (m - 1) ^ 2 * (4 ^ 2 / 3 ^ 3))
        (by positivity) (by positivity) (by norm_num at hbar ⊢; exact hbar) y J
      have heq : (2 : ℝ) ^ 5 * D.velocityAmplitude (m - 1) *
          D.epsilon (m - 1) ^ 2 * (4 ^ 2 / 3 ^ 3) *
          (Nat.factorial 2 : ℝ) *
          (2 ^ 8 * (D.epsilon (m - 1))⁻¹) ^ 2 / (2 + 1 : ℝ) ^ 2 =
          (2 : ℝ) ^ 26 / 243 * D.velocityAmplitude (m - 1) := by
        norm_num [Nat.factorial]
        field_simp
        ring
      simp only [Nat.cast_ofNat] at hpoint
      rw [heq] at hpoint
      exact hpoint.trans (mul_le_mul_of_nonneg_right (by norm_num)
        hAprev.le)
    have hLip : ∀ y : Vec 2,
        ‖streamVel (Φ (m - 1)) t y - streamVel (Φ (m - 1)) t x‖ ≤
          2 * ((2 : ℝ) ^ 19 * D.velocityAmplitude (m - 1)) * ‖y - x‖ := by
      intro y
      exact amnr_streamVel_lipschitz_of_hessian t hsmooth
        (show 0 ≤ (2 : ℝ) ^ 19 * D.velocityAmplitude (m - 1) by positivity)
        hH y x
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    apply Filter.Eventually.of_forall
    intro y
    have hLip' := hLip y
    have hLip'' : ‖streamVel (Φ (m - 1)) t y -
        streamVel (Φ (m - 1)) t x‖ ≤
        (2 : ℝ) ^ 20 * D.velocityAmplitude (m - 1) * ‖y - x‖ := by
      calc
        _ ≤ 2 * ((2 : ℝ) ^ 19 * D.velocityAmplitude (m - 1)) * ‖y - x‖ := hLip'
        _ = _ := by rw [pow_succ]; ring
    simpa [dist_eq_norm, sub_eq_add_neg, mul_assoc] using hLip''

/-- The stream-regularity estimates and the actual source cutoff length
control all actual spatial flow operators at auxiliary orders. -/
theorem amnr_aux_previous_flow_iteratedFDeriv_norm_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData α s q Λ ζ) {C : ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t - s| ≤ D.tauPP m / 2 + D.tauP m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1)
      (fun y => Section2FlowIdentities.constructionFlow D hseq (m - 1) t y s) x‖ ≤
      amnrFlowSpatialSourceConstant N * (D.epsilon (m - 1))⁻¹ ^ n := by
  let A := D.velocityAmplitude (m - 1)
  let ε := D.epsilon (m - 1)
  let M := (2 : ℝ) ^ 20 * A
  let P := (2 : ℝ) ^ (N + 1) * amnrSpatialVelocityConstant N
  let B := P * A
  let C := (2 : ℝ) ^ (-25 : ℤ) * P
  have hA : 0 < A := by
    dsimp [A]
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
  have hε : 0 < ε := D.epsilon_pos _
  have hCN : 0 < amnrSpatialVelocityConstant N := amnrSpatialVelocityConstant_pos N
  have hP : 0 ≤ P := by dsimp [P]; exact mul_nonneg (by positivity) hCN.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := mul_nonneg hP hA.le
  have htime : |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) * A⁻¹ :=
    ht.trans (cutoff_window_fits_flow D m hm)
  have hAd : A * |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) := by
    have hh := mul_le_mul_of_nonneg_left htime hA.le
    have heq : A * ((2 : ℝ) ^ (-25 : ℤ) * A⁻¹) = (2 : ℝ) ^ (-25 : ℤ) := by
      field_simp
    rwa [heq] at hh
  have hsmall : (max s t - min s t) * M ≤ 1 / 2 := by
    rw [max_sub_min_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hAd (show (0 : ℝ) ≤ 2 ^ 20 by positivity)
    have heq : (2 : ℝ) ^ 20 * (2 : ℝ) ^ (-25 : ℤ) = 1 / 32 := by norm_num
    rw [heq] at hh
    have hmid : |t - s| * M ≤ 1 / 32 := by convert hh using 1; dsimp [M]; ring
    exact hmid.trans (by norm_num)
  have hscale : (max s t - min s t) * B ≤ C := by
    rw [max_sub_min_eq_abs]
    have hh := mul_le_mul_of_nonneg_left hAd hP
    convert hh using 1 <;> dsimp [B, C] <;> ring
  have hp : ∀ i, i ≤ N → ∀ u y,
      ‖iteratedFDeriv ℝ i
        (fun z => jointSpatialFDeriv (streamVel (Φ (m - 1))) u z) y‖ ≤
        B * ε⁻¹ ^ i := by
    intro i hi u y
    have hh := previous_velocityJacobian_iteratedFDeriv_bound
      (D := D) hseq hreg hm i N hi u y
    refine hh.trans ?_
    change (2 : ℝ) ^ (i + 1) *
        (amnrSpatialVelocityConstant N * A * ε⁻¹ ^ i) ≤
      ((2 : ℝ) ^ (N + 1) * amnrSpatialVelocityConstant N * A) * ε⁻¹ ^ i
    calc
      _ ≤ (2 : ℝ) ^ (N + 1) *
          (amnrSpatialVelocityConstant N * A * ε⁻¹ ^ i) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      _ = _ := by ring
  have hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ (m - 1))) :=
    AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel (Φ (m - 1)))
      (Section2FlowIdentities.constructionFlow D hseq (m - 1)) := by
    change IsFlow (streamVel (Φ (m - 1)))
      (AVenhance.flow (streamVel (Φ (m - 1)))
        (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).vel_continuous
        (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).vel_lipschitz)
    exact AVenhance.flow_isFlow (streamVel (Φ (m - 1)))
      (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).vel_continuous
      (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).vel_lipschitz
  have hh := amnr_flow_iteratedFDeriv_norm_le_of_primitive_jets hb hX
    hM hB hε (previous_velocityJacobian_norm_bound (D := D) hseq hreg hm)
    (min_le_max) ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _⟩ hsmall hscale hp n hbudget x
  have hc : amnrJacobianJetConstant C N = amnrFlowSpatialSourceConstant N := by
    unfold amnrFlowSpatialSourceConstant
    congr 1
    dsimp [C, P]
    ring
  refine hh.trans ?_
  change amnrJacobianJetConstant C n * ε⁻¹ ^ n ≤
    amnrFlowSpatialSourceConstant N * ε⁻¹ ^ n
  rw [← hc]
  exact mul_le_mul_of_nonneg_right
    (amnrJacobianJetConstant_mono C hbudget) (by positivity)

/-- The inverse flow has the same auxiliary spatial rate after exchanging
its actual initial and target times. -/
theorem amnr_aux_xFlowInv_iteratedFDeriv_norm_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData α s q Λ ζ) {C : ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * D.tauPP m| ≤ D.tauPP m / 2 + D.tauP m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1)
      (fun y => Section2FlowIdentities.constructionFlowInv D hseq (m - 1)
        t y (l * D.tauPP m)) x‖ ≤
      amnrFlowSpatialSourceConstant N * (D.epsilon (m - 1))⁻¹ ^ n := by
  have h := amnr_aux_previous_flow_iteratedFDeriv_norm_le_of_A3
    D hseq hreg hm t (l * D.tauPP m)
    (by simpa only [abs_sub_comm] using ht) (N := N) n hbudget x
  simpa [Section2FlowIdentities.constructionFlowInv,
    Section2FlowIdentities.streamFlowInv, Section2FlowIdentities.constructionFlow,
    Section2FlowIdentities.streamFlow, AVenhance.flowInv] using h

end AVRegularity.Velocity.Port.MaterialAuxiliaryFlow
end
end
end

section
@[expose] public section
namespace AVRegularity.Velocity.Port.RecursionIncrement

/-! The inverse-flow input consumed by the Section 2 increment estimate. -/

open Homogenization AVenhance
open AVRegularity.Velocity.Port.Section2Induction

/-- The App. B.2 inverse-flow package in the OC Section 2 seminorm. -/
structure AppB2InverseFlowData {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) : Prop where
  inverse_spatial_smooth : ∀ m : ℕ, 1 ≤ m → ∀ s u : ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
      Section2FlowIdentities.constructionFlowInv D hseq (m - 1) (s + u) x s)
  inverse_transport_estimate : ∀ m : ℕ, 1 ≤ m →
    Section2StreamInductionHypothesis D Φ (m - 1) →
    ∀ s u : ℝ, |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹ →
    ∀ n : ℕ, 1 ≤ n →
      FaaDiBruno.snorm
        (fun x : Vec 2 =>
          Section2FlowIdentities.constructionFlowInv D hseq (m - 1) (s + u) x s)
        n ((9 / 8) * D.radius (m - 1)) ≤
          ENNReal.ofReal (5 * (8 / 9 : ℝ) * (D.radius (m - 1))⁻¹)

end AVRegularity.Velocity.Port.RecursionIncrement
end
end

section
@[expose] public section

open MeasureTheory Homogenization AVenhance

/-! Repackage all finite joint flow orders into the spatial smoothness witness
required by the consumed App. B.2 inverse-flow data. -/

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVRegularity.Velocity.Port.AppB2Smoothness

open AVRegularity.Velocity.Port.Section2FlowIdentities
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.Section2Scales
open AVRegularity.Velocity.Port.AppB2FieldBounds
open AVRegularity.Velocity.Port.RecursionIncrement

theorem constructionFlowInv_spatial_smooth_of_joint_orders
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (s u : ℝ) :
    ContDiff ℝ ∞ (fun x : Vec 2 =>
      constructionFlowInv D hseq m (s + u) x s) := by
  have hforward : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow D hseq m p.1 p.2.1 p.2.2) := by
    rw [contDiff_infty]
    intro n
    exact hjoint m n
  let spaceTimeMap : Vec 2 → ℝ × Vec 2 × ℝ := fun x => (s, x, s + u)
  have hmapSmooth : ContDiff ℝ ∞ spaceTimeMap := by
    fun_prop
  have hinv :
      (fun x : Vec 2 => constructionFlowInv D hseq m (s + u) x s) =
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2) ∘ spaceTimeMap := by
    funext x
    simp [spaceTimeMap,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlowInv,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlow,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlowInv,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlow, flowInv]
  rw [hinv]
  exact hforward.comp hmapSmooth

theorem identity_orderedPartial_one (x : Vec 2) (I : Fin 1 → Fin 2) :
    AVenhance.FaaDiBruno.orderedPartial 1 (fun y : Vec 2 => y) x I =
      AVenhance.FaaDiBruno.coordinateVector 2 (I 0) := by
  open AVenhance.FaaDiBruno in
  have hderiv : fderiv ℝ
      (fun z : AVenhance.FaaDiBruno.VecOne 2 =>
        AVenhance.FaaDiBruno.vecOneEquiv 2 z)
      (WithLp.toLp 1 x) =
        (AVenhance.FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap := by
    exact (AVenhance.FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.fderiv
  rw [AVenhance.FaaDiBruno.orderedPartial,
    show AVenhance.FaaDiBruno.liftVecOne (fun y : Vec 2 => y) =
      fun z => AVenhance.FaaDiBruno.vecOneEquiv 2 z by rfl,
    iteratedFDeriv_one_apply, hderiv]
  ext j
  by_cases hji : j = I 0 <;>
    simp [AVenhance.FaaDiBruno.vecOneEquiv,
      AVenhance.FaaDiBruno.coordinateVectorOne,
      AVenhance.FaaDiBruno.coordinateVector, hji]

theorem identity_orderedPartial_ge_two (x : Vec 2) {n : ℕ}
    (hn : 2 ≤ n) (I : Fin n → Fin 2) :
    AVenhance.FaaDiBruno.orderedPartial n (fun y : Vec 2 => y) x I = 0 := by
  open AVenhance.FaaDiBruno in
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      have hconst :
          (fun y : VecOne 2 => fderiv ℝ (fun z : VecOne 2 => vecOneEquiv 2 z) y) =
            fun _ => (vecOneEquiv 2).toContinuousLinearMap := by
        funext y
        exact (vecOneEquiv 2).toContinuousLinearMap.fderiv
      rw [orderedPartial,
        show liftVecOne (fun y : Vec 2 => y) = fun z => vecOneEquiv 2 z by rfl,
        iteratedFDeriv_succ_apply_right, hconst]
      have hz := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := VecOne 2)
        (F := VecOne 2 →L[ℝ] Vec 2) (n := k + 1) (by omega)
        ((vecOneEquiv 2).toContinuousLinearMap)
      rw [hz]
      simp

theorem identity_derivativeSup_le_one {n : ℕ} (hn : 1 ≤ n) :
    AVenhance.FaaDiBruno.derivativeSup n (fun x : Vec 2 => x) ≤ ENNReal.ofReal 1 := by
  open AVenhance.FaaDiBruno in
  by_cases hOne : n = 1
  · subst n
    unfold derivativeSup
    apply iSup_le
    intro I
    unfold partialSup
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    rw [identity_orderedPartial_one x I]
    have hnorm : ‖AVenhance.FaaDiBruno.coordinateVector 2 (I 0)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonempty]
      intro j
      by_cases hj : j = I 0 <;>
        simp [AVenhance.FaaDiBruno.coordinateVector, hj]
    exact hnorm
  · have hnTwo : 2 ≤ n := by omega
    have hpartialZero (I : Fin n → Fin 2) :
        partialSup n (fun x : Vec 2 => x) I = 0 := by
      unfold partialSup
      rw [eLpNormEssSup_eq_zero_iff]
      filter_upwards with x
      exact identity_orderedPartial_ge_two x hnTwo I
    have hzero : derivativeSup n (fun x : Vec 2 => x) = 0 := by
      unfold derivativeSup
      apply le_antisymm
      · exact iSup_le fun I => (hpartialZero I).le
      · exact bot_le
    rw [hzero]
    simp

theorem identity_snorm_le_four_div {n : ℕ} (hn : 1 ≤ n) {S : ℝ}
    (hS : 0 < S) :
    AVenhance.FaaDiBruno.snorm (fun x : Vec 2 => x) n S ≤
      ENNReal.ofReal (4 / S) := by
  open AVenhance.FaaDiBruno in
  by_cases hOne : n = 1
  · subst n
    have hD := identity_derivativeSup_le_one (n := 1) (by norm_num)
    have hfactor :
        ((4 / S) * S ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
          ((↑(1 : ℕ) + 1 : ℝ) ^ 2)) = 1 := by
      norm_num [Nat.factorial]
      field_simp [ne_of_gt hS]
    have htarget : ENNReal.ofReal 1 ≤ ENNReal.ofReal
        ((4 / S) * S ^ (1 : ℕ) * (Nat.factorial 1 : ℝ) /
          ((↑(1 : ℕ) + 1 : ℝ) ^ 2)) := by
      rw [hfactor]
    apply snorm_le_of_derivativeSup_le (fun x : Vec 2 => x) hS
    exact hD.trans htarget
  · have hnTwo : 2 ≤ n := by omega
    have hpartialZero (I : Fin n → Fin 2) :
        partialSup n (fun x : Vec 2 => x) I = 0 := by
      unfold partialSup
      rw [eLpNormEssSup_eq_zero_iff]
      filter_upwards with x
      exact identity_orderedPartial_ge_two x hnTwo I
    have hzero : derivativeSup n (fun x : Vec 2 => x) = 0 := by
      unfold derivativeSup
      apply le_antisymm
      · exact iSup_le fun I => (hpartialZero I).le
      · exact bot_le
    unfold snorm
    rw [hzero]
    simp

theorem derivativeSup_add_le_vec {n : ℕ} (f g : Vec 2 → Vec 2)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.FaaDiBruno.derivativeSup n (fun x => f x + g x) ≤
      AVenhance.FaaDiBruno.derivativeSup n f +
        AVenhance.FaaDiBruno.derivativeSup n g := by
  classical
  open AVenhance.FaaDiBruno in
  unfold derivativeSup
  refine iSup_le fun I => ?_
  calc
    partialSup n (fun x => f x + g x) I ≤ partialSup n f I + partialSup n g I := by
      unfold partialSup
      have hadd : liftVecOne (fun x => f x + g x) = liftVecOne f + liftVecOne g := by
        funext z
        rfl
      have hpart (x : Vec 2) :
          orderedPartial n (fun x => f x + g x) x I =
            orderedPartial n f x I + orderedPartial n g x I := by
        simp only [orderedPartial, hadd]
        rw [iteratedFDeriv_add_apply
          (contDiff_liftVecOne hf).contDiffAt
          (contDiff_liftVecOne hg).contDiffAt]
        rfl
      have hfun :
          (fun x => orderedPartial n (fun x => f x + g x) x I) =
            (fun x => orderedPartial n f x I) +
              (fun x => orderedPartial n g x I) := by
        funext x
        exact hpart x
      rw [hfun]
      exact eLpNormEssSup_add_le
    _ ≤ derivativeSup n f + derivativeSup n g :=
      add_le_add (le_iSup_of_le I le_rfl) (le_iSup_of_le I le_rfl)

theorem snorm_add_le_vec {n : ℕ} {S : ℝ} (f g : Vec 2 → Vec 2)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    AVenhance.FaaDiBruno.snorm (fun x => f x + g x) n S ≤
      AVenhance.FaaDiBruno.snorm f n S + AVenhance.FaaDiBruno.snorm g n S := by
  open AVenhance.FaaDiBruno in
  unfold snorm
  have hD := derivativeSup_add_le_vec f g hf hg
  let c := ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal S)⁻¹ ^ n
  calc
    _ ≤ c * (derivativeSup n f + derivativeSup n g) := by
      dsimp [c]
      gcongr
    _ = _ := by
      dsimp [c]
      rw [mul_add]

theorem snorm_neg_eq_vec {n : ℕ} {S : ℝ} (f : Vec 2 → Vec 2) :
    AVenhance.FaaDiBruno.snorm (fun x => -f x) n S =
      AVenhance.FaaDiBruno.snorm f n S := by
  open AVenhance.FaaDiBruno in
  have hpartial (I : Fin n → Fin 2) :
      partialSup n (fun x => -f x) I = partialSup n f I := by
    unfold partialSup
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    apply essSup_congr_ae
    filter_upwards with x
    have h : orderedPartial n (fun x => -f x) x I = -orderedPartial n f x I := by
      change iteratedFDeriv ℝ n
        (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
          (fun j => coordinateVectorOne 2 (I j)) =
        -iteratedFDeriv ℝ n
          (fun z : VecOne 2 => f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
            (fun j => coordinateVectorOne 2 (I j))
      rw [show (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) =
        -(fun z : VecOne 2 => f ((vecOneEquiv 2) z)) by rfl, iteratedFDeriv_neg]
      rfl
    rw [h]
    simp
  have hderiv :
      derivativeSup n (fun x => -f x) = derivativeSup n f := by
    unfold derivativeSup
    apply le_antisymm
    · apply iSup_le
      intro I
      rw [hpartial I]
      exact le_iSup_of_le I le_rfl
    · apply iSup_le
      intro I
      rw [← hpartial I]
      exact le_iSup_of_le I le_rfl
  unfold snorm
  rw [hderiv]

theorem constructionFlow_jointSmooth_of_joint_orders
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ =>
        constructionFlow D hseq m p.1.1 p.1.2 p.2) := by
  have hjointAll : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow D hseq m p.1 p.2.1 p.2.2) := by
    rw [contDiff_infty]
    intro n
    exact hjoint m n
  have hperm : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => (p.1.1, p.1.2, p.2)) := by
    fun_prop
  change ContDiff ℝ ∞
    ((fun p : ℝ × Vec 2 × ℝ =>
      constructionFlow D hseq m p.1 p.2.1 p.2.2) ∘
      fun p : (ℝ × Vec 2) × ℝ => (p.1.1, p.1.2, p.2))
  exact hjointAll.comp hperm

theorem constructionFlow_shift_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) (s : ℝ) :
    IsFlow (fun t x => b (s + t) x)
      (fun t x r => X (s + t) x (s + r)) := by
  refine ⟨?_, ?_⟩
  · intro x r
    exact hX.1 x (s + r)
  · intro x r t
    have hbase : HasDerivAt (fun z => X z x (s + r))
        (b (t + s) (X (t + s) x (s + r))) (t + s) := by
      simpa [add_comm] using hX.2 x (s + r) (s + t)
    have hshifted := hbase.comp_add_const t s
    convert hshifted using 1 <;> simp [add_comm]

theorem constructionFlowInv_displacement_data_of_joint_orders
    {α s q₀ : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q₀ Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q₀ Λ ζ Φ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹)
    (n : ℕ) (hn : 1 ≤ n) :
    ContDiff ℝ n
      (fun x : Vec 2 => constructionFlow D hseq (m - 1) s x (s + u) - x) ∧
    AVenhance.FaaDiBruno.snorm
      (fun x : Vec 2 => constructionFlow D hseq (m - 1) s x (s + u) - x)
      n ((9 / 8) * D.radius (m - 1)) ≤
      ENNReal.ofReal (1 / (4 * D.radius (m - 1))) := by
  let q : ℕ := m - 1
  let Rq : ℝ := D.radius q
  let Mq : ℝ := D.jetSize q
  let Cf : ℝ := Mq / Rq
  let Cg : ℝ := Mq / Rq
  have hRq : 0 < Rq := by dsimp [Rq, q]; exact section2_radius_pos D (m - 1)
  have hMq : 0 < Mq := by dsimp [Mq, q]; exact section2_amplitude_pos D (m - 1)
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCfR : Cf * Rq = Mq := by
    dsimp [Cf]
    field_simp [ne_of_gt hRq]
  have hu' : |u| ≤ (1 / 64 : ℝ) * Mq⁻¹ := by
    have hz : (2 : ℝ) ^ (-6 : ℤ) = (1 / 64 : ℝ) := by norm_num
    simpa [hz, Mq, q, mul_comm] using hu
  have htime : |u| ≤ 1 / (8 * Cf * Rq) := by
    calc
      |u| ≤ (1 / 64 : ℝ) * Mq⁻¹ := hu'
      _ ≤ (1 / 8 : ℝ) * Mq⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hMq.le)
      _ = 1 / (8 * Cf * Rq) := by
        have hmul : 8 * Cf * Rq = 8 * Mq := by
          calc
            8 * Cf * Rq = 8 * (Cf * Rq) := by ring
            _ = 8 * Mq := by rw [hCfR]
        rw [hmul]
        field_simp [ne_of_gt hMq]
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ q)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow D hseq q
  have hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq q
  have hb : AVenhance.Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlow,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ q)) hφ.vel_continuous hφ.vel_lipschitz
  have hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2) := by
    simpa [X] using constructionFlow_jointSmooth_of_joint_orders D hseq q hjoint
  let bShift : ℝ → Vec 2 → Vec 2 := fun t x => b (s + t) x
  let gShift : ℝ → Vec 2 → Vec 2 := fun t x => -bShift t x
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun t x r => X (s + t) x (s + r)
  have hbShift : ContDiff ℝ ∞ (Function.uncurry bShift) := by
    have hmap : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ ∞ (Function.uncurry b ∘
      fun p : ℝ × Vec 2 => (s + p.1, p.2))
    exact hb.smooth.comp hmap
  have hgShift : ContDiff ℝ ∞ (Function.uncurry gShift) := by
    change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      -(Function.uncurry bShift p))
    exact contDiff_neg.comp hbShift
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using constructionFlow_shift_isFlow hX s
  let Y : ℝ → Vec 2 → Vec 2 := fun t x => X s x (s + t) - x
  have hYjoint : ContDiff ℝ ∞ (Function.uncurry Y) := by
    let map : ℝ × Vec 2 → (ℝ × Vec 2) × ℝ :=
      fun p => ((s, p.2), s + p.1)
    have hmap : ContDiff ℝ ∞ map := by fun_prop
    have hF : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => X s p.2 (s + p.1)) := by
      change ContDiff ℝ ∞
        ((fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2) ∘ map)
      exact hXsmooth.comp hmap
    have hId : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => p.2) := by fun_prop
    change ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => X s p.2 (s + p.1) - p.2)
    exact hF.sub hId
  have hYslice : ContDiff ℝ n (Y u) := by
    have hmap : ContDiff ℝ n (fun x : Vec 2 => (u, x)) := by fun_prop
    exact (hYjoint.of_le (by simp)).comp hmap
  have htransport :
      AVenhance.FaaDiBruno.IsClassicalTransportSolution bShift gShift Y := by
    simpa [bShift, gShift, Y, b, X] using
      AVenhance.FaaDiBruno.flow_inverse_displacement_at_start_isTransportSolution_of_jointSmooth
        hb hX hXsmooth s
  have hB : ∀ t k, 1 ≤ k → k ≤ n →
      AVenhance.FaaDiBruno.snorm (bShift t) k Rq ≤ ENNReal.ofReal Cf := by
    intro t k hk hkn
    have hfield := section2_streamVel_snorm_bound D hseq hprev hk (s + t)
    simpa [bShift, b, Cf, Cg, Rq, Mq, q] using hfield
  have hG : ∀ t k, 1 ≤ k → k ≤ n →
      AVenhance.FaaDiBruno.snorm (gShift t) k Rq ≤ ENNReal.ofReal Cg := by
    intro t k hk hkn
    rw [snorm_neg_eq_vec]
    have hfield := section2_streamVel_snorm_bound D hseq hprev hk (s + t)
    simpa [bShift, b, Cf, Cg, Rq, Mq, q] using hfield
  have hYest : ∀ k, 1 ≤ k → k ≤ n → ∀ t,
      |t| ≤ 1 / (8 * Cf * Rq) →
      AVenhance.FaaDiBruno.snorm (Y t) k
        (AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |t|) ≤
        ENNReal.ofReal (16 * Cg * |t|) := by
    exact AVenhance.FaaDiBruno.transportSolution_snorm_equalRadius_all
      htransport hbShift hgShift hXShift hCf hCg hRq hB hG
  have hYat := hYest n hn (by omega) u htime
  let Sout : ℝ := (9 / 8) * Rq
  have hSout : 0 < Sout := by dsimp [Sout]; positivity
  have hshift :
      AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |u| ≤ Sout := by
    have huM : 8 * Mq * |u| ≤ 1 / 8 := by
      calc
        8 * Mq * |u| ≤ 8 * Mq * ((1 / 64 : ℝ) * Mq⁻¹) := by gcongr
        _ = 1 / 8 := by field_simp [ne_of_gt hMq]; ring
    change AVenhance.FaaDiBruno.transportShiftRadius Cf Rq |u| ≤ (9 / 8) * Rq
    rw [AVenhance.FaaDiBruno.transportShiftRadius]
    have hterm : 8 * |u| * Cf * Rq ^ 2 = (8 * Mq * |u|) * Rq := by
      rw [← hCfR]
      ring
    rw [hterm]
    nlinarith [hRq, huM]
  have hYout : AVenhance.FaaDiBruno.snorm (Y u) n Sout ≤
      ENNReal.ofReal (16 * Cg * |u|) := by
    apply AVenhance.FaaDiBruno.snorm_le_of_radius_le (Y u)
      (by
        rw [AVenhance.FaaDiBruno.transportShiftRadius]
        positivity)
      hSout hshift (by positivity) hYat
  have hdispReal : 16 * Cg * |u| ≤ 1 / (4 * Rq) := by
    rw [show 1 / (4 * Rq) = (1 / 4 : ℝ) / Rq by ring]
    apply (le_div_iff₀ hRq).2
    have hleft : (16 * Cg * |u|) * Rq = 16 * Mq * |u| := by
      dsimp [Cg]
      field_simp [ne_of_gt hRq]
    rw [hleft]
    calc
      16 * Mq * |u| ≤ 16 * Mq * ((1 / 64 : ℝ) * Mq⁻¹) := by gcongr
      _ = 1 / 4 := by field_simp [ne_of_gt hMq]; ring
  have hYout' : AVenhance.FaaDiBruno.snorm (Y u) n Sout ≤
      ENNReal.ofReal (1 / (4 * Rq)) :=
    hYout.trans (ENNReal.ofReal_le_ofReal hdispReal)
  exact ⟨hYslice, by simpa [Y, Sout, q] using hYout'⟩

theorem constructionFlowInv_snorm_bound_of_joint_orders
    {α s q₀ : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q₀ Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q₀ Λ ζ Φ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2))
    (m : ℕ) (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (s u : ℝ) (hu : |u| ≤ (2 : ℝ) ^ (-6 : ℤ) * (D.jetSize (m - 1))⁻¹)
    (n : ℕ) (hn : 1 ≤ n) :
    AVenhance.FaaDiBruno.snorm
      (fun x : Vec 2 => constructionFlowInv D hseq (m - 1) (s + u) x s)
      n ((9 / 8) * D.radius (m - 1)) ≤
      ENNReal.ofReal (5 * (8 / 9 : ℝ) * (D.radius (m - 1))⁻¹) := by
  let q : ℕ := m - 1
  let Rq : ℝ := D.radius q
  let Sout : ℝ := (9 / 8) * Rq
  have hRq : 0 < Rq := by dsimp [Rq, q]; exact section2_radius_pos D (m - 1)
  have hSout : 0 < Sout := by dsimp [Sout]; positivity
  obtain ⟨hYslice, hYbound⟩ :=
    constructionFlowInv_displacement_data_of_joint_orders
      D hseq hjoint m hprev s u hu n hn
  let Y : Vec 2 → Vec 2 := fun x => constructionFlow D hseq q s x (s + u) - x
  have htargetfun :
      (fun x : Vec 2 => constructionFlowInv D hseq q (s + u) x s) =
        (fun x => x + Y x) := by
    funext x
    simp [Y, q,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlowInv,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlow,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlowInv,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlow, flowInv]
  have hid := identity_snorm_le_four_div hn hSout
  have hadd := snorm_add_le_vec (n := n) (S := Sout)
    (fun x : Vec 2 => x) Y contDiff_id hYslice
  rw [htargetfun]
  have hsum := hadd.trans (add_le_add hid hYbound)
  have hcoef : 4 / Sout + 1 / (4 * Rq) ≤ 40 / 9 * Rq⁻¹ := by
    dsimp [Sout]
    field_simp [ne_of_gt hRq]
    nlinarith
  calc
    AVenhance.FaaDiBruno.snorm (fun x : Vec 2 => x + Y x) n Sout ≤
        ENNReal.ofReal (4 / Sout) + ENNReal.ofReal (1 / (4 * Rq)) := hsum
    _ = ENNReal.ofReal (4 / Sout + 1 / (4 * Rq)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (40 / 9 * Rq⁻¹) := ENNReal.ofReal_le_ofReal hcoef
    _ = ENNReal.ofReal (5 * (8 / 9 : ℝ) * (D.radius (m - 1))⁻¹) := by
      congr 1
      change 40 / 9 * (D.radius (m - 1))⁻¹ =
        5 * (8 / 9 : ℝ) * (D.radius (m - 1))⁻¹
      ring

/-- Construct the consumed App. B.2 package from the previous-scale induction
bound, provided every finite joint order of the construction flow is available.
The finite-order premise assembles the smooth inverse witness; the quantitative
field input is exactly `e.indyhyp` at scale `m - 1`. -/
theorem appB2InverseFlowData_of_joint_orders
    {α s q₀ : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q₀ Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q₀ Λ ζ Φ)
    (hjoint : ∀ m n : ℕ,
      ContDiff ℝ n
        (fun p : ℝ × Vec 2 × ℝ =>
          constructionFlow D hseq m p.1 p.2.1 p.2.2)) :
    AppB2InverseFlowData D Φ hseq := by
  refine ⟨?_, ?_⟩
  · intro m hm s u
    exact constructionFlowInv_spatial_smooth_of_joint_orders D hseq hjoint (m - 1) s u
  · intro m hm hprev s u hu n hn
    exact constructionFlowInv_snorm_bound_of_joint_orders
      D hseq hjoint m hprev s u hu n hn

/-- Construct all finite joint orders of the construction flow from the
merged all-orders ODE theorem. Each scale's stream velocity is a smooth
periodic field, and its characterized construction flow is therefore jointly
C∞ in target time, initial point, and start time. -/
theorem appB2InverseFlowData_of_smoothPeriodicFlow
    {α s q₀ : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData α s q₀ Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq α q₀ Λ ζ Φ) :
    AppB2InverseFlowData D Φ hseq := by
  apply appB2InverseFlowData_of_joint_orders D hseq
  intro m n
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow D hseq m
  have hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hb : AVenhance.Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b,
      AVRegularity.Velocity.Port.Section2FlowIdentities.constructionFlow,
      AVRegularity.Velocity.Port.Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hJointSmooth : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) :=
    AVenhance.Infra.Flow.flow_joint_contDiff_infty hb hX
  simpa [X] using hJointSmooth.of_le (by simp : (n : ℕ∞ω) ≤ ∞)

end AVRegularity.Velocity.Port.AppB2Smoothness

end
end
end
