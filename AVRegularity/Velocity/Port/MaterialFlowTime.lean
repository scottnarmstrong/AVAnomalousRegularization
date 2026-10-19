-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.Section2FlowRegularity
import AVenhance.Infra.Section4.Amnr.GradientScaleChange
public import AVenhance.Infra.Section4.Amnr.CorrectionCardinality
public import AVenhance.Infra.Section4.Amnr.NormalOrderConstants
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Section4.Amnr.BoundedGradientInduction
import AVenhance.Infra.Section4.Amnr.Cutoff
import AVenhance.Infra.Section4.Amnr.FastVelocityMaterial
import AVenhance.Infra.Section4.Amnr.HigherGradientStep
import AVenhance.Infra.Section4.Amnr.HigherMaterialScaling
import AVenhance.Infra.Section4.Amnr.MaterialCalculus
import AVenhance.Infra.Section4.Amnr.Seed
import AVenhance.Infra.Section4.Amnr.SpatialCommutator
import AVenhance.Infra.Section4.Amnr.StreamFirstMaterialSpatial
import AVenhance.Infra.Section4.Amnr.VelocityFirstSpatialSum
import AVenhance.Infra.Section4.Amnr.VelocityHigherStep
import AVenhance.Infra.Section4.Amnr.VelocityMaterialSum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section
noncomputable section

section
open Homogenization MeasureTheory
namespace AVRegularity.Velocity.Port.MaterialAuxiliaryInduction

/-! All-order material jets with a separate auxiliary spatial/word budget. -/

open AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.MaterialAuxiliaryWords

private theorem hβlt_of_data {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ) : β < 4 / 3 := by linarith [D.hαlt]

private theorem material_aux_epsilon_current_le_prev
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {m : ℕ} (hm : 1 ≤ m) :
    D.epsilon m ≤ D.epsilon (m - 1) := by
  have hratio := D.epsilon_ratio m hm
  have he := D.epsilon_pos m
  have hΛ : (1 : ℝ) ≤ Λ := by
    have h := D.hΛ
    exact_mod_cast (show 1 ≤ Λ by omega)
  have hmul : (Λ : ℝ) * D.epsilon m ≤ D.epsilon (m - 1) :=
    (le_div_iff₀ he).mp hratio
  exact (le_mul_of_one_le_left he.le hΛ).trans hmul

private theorem material_aux_negative_power_sum
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    {p : ℝ} (hp : p ≤ -(1 / 7 : ℝ)) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), D.epsilon j ^ p) ≤
      2 * D.epsilon m ^ p := by
  let r : ℝ := -p
  have hr : (1 / 7 : ℝ) ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hΛpos : (0 : ℝ) < Λ := by
    have h := D.hΛ
    exact_mod_cast (show 0 < Λ by omega)
  have hΛpow : (Λ : ℝ) ^ (-r) ≤ 1 / 2 := by
    have h128 : (2 : ℝ) ^ 7 ≤ (Λ : ℝ) := by
      have hnat : 128 ≤ Λ := D.hΛ
      have hpow : 2 ^ 7 ≤ Λ := by norm_num at hnat ⊢; exact hnat
      exact_mod_cast hpow
    calc
      (Λ : ℝ) ^ (-r) ≤ ((2 : ℝ) ^ 7) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h128 (by linarith)
      _ = (2 : ℝ) ^ (-(7 * r)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring_nf
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hden : 0 < 1 - (Λ : ℝ) ^ (-r) := by linarith
  have hratio : (Λ : ℝ) ^ (-r) ≤ 1 / 2 := hΛpow
  have hsum := AVRegularity.Scales.admissible_epsilon_backward_sum
    (α := β - 1) (s := s) (q := q) D.hq D.hΛ (m := m) hrpos
  have hsum' : (∑ j ∈ Finset.range (m + 1), D.epsilon j ^ p) ≤
      D.epsilon m ^ p / (1 - (Λ : ℝ) ^ (-r)) := by
    simpa [D.epsilon_eq_oc, r, Real.rpow_neg] using hsum
  calc
    _ ≤ D.epsilon m ^ p / (1 - (Λ : ℝ) ^ (-r)) := hsum'
    _ ≤ 2 * D.epsilon m ^ p := by
      apply (div_le_iff₀ hden).2
      have hpnonneg : 0 ≤ D.epsilon m ^ p := Real.rpow_nonneg (D.epsilon_pos m).le p
      nlinarith [hratio]

private theorem material_aux_streamIncrement_contDiff
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => Φ m z.1 z.2 - Φ (m - 1) z.1 z.2) := by
  exact (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1.sub
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).1

private theorem material_aux_fastVelocity_component
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (m : ℕ) (i : Fin 2) :
    (fun z : AmnrSpace => AVenhance.streamVel (Φ m) z.1 z.2 i -
      AVenhance.streamVel (Φ (m - 1)) z.1 z.2 i) =
      (if i = 0 then (-1 : ℝ) else 1) •
        amnrOp (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2)
          (some (if i = 0 then 1 else 0))
          (fun z => Φ m z.1 z.2 - Φ (m - 1) z.1 z.2) := by
  have hf := material_aux_streamIncrement_contDiff D hseq m
  funext z
  have hφ : DifferentiableAt ℝ (Φ m z.1) z.2 :=
    (((AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1.comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
  have hψ : DifferentiableAt ℝ (Φ (m - 1) z.1) z.2 :=
    (((AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).1.comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
  have hgrad := congrArg (fun v : Vec 2 => v i)
    (amnr_streamVel_sub z.1 z.2 hφ hψ)
  simp only [Pi.sub_apply] at hgrad
  rw [← hgrad]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [amnrOp_space (hf.differentiable (by simp) z)]
  fin_cases i <;> simp [AVenhance.streamVel, AVenhance.sigmaMat,
    dotProduct, Fin.sum_univ_two]

private theorem material_aux_streamVelocity_zero_word
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (_D : JetRecursionData (β - 1) s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (w : List (Option (Fin 2))) (i : Fin 2) :
    amnrWord (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) w
      (fun y => AVenhance.streamVel (Φ 0) y.1 y.2 i) = 0 := by
  have hv : (fun y : AmnrSpace => AVenhance.streamVel (Φ 0) y.1 y.2) = 0 := by
    funext y p
    rw [hseq.1]
    fin_cases p <;> simp [AVenhance.streamVel, AVenhance.spaceGrad]
  have hi : (fun y : AmnrSpace => AVenhance.streamVel (Φ 0) y.1 y.2 i) = 0 := by
    funext y
    exact congrFun (congrFun hv y) i
  rw [hv, hi, amnrWord_zero]

private theorem material_aux_streamGradient_zero_word
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (_D : JetRecursionData (β - 1) s q Λ ζ)
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (w : List (Option (Fin 2))) (i p : Fin 2) :
    amnrWord (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) w
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) i p) = 0 := by
  have hv : (fun y : AmnrSpace => AVenhance.streamVel (Φ 0) y.1 y.2) = 0 := by
    funext y j
    rw [hseq.1]
    fin_cases j <;> simp [AVenhance.streamVel, AVenhance.spaceGrad]
  rw [hv]
  have hg : amnrVelocityGradient (0 : AmnrSpace → Vec 2) i p = 0 := by
    funext y
    simp [amnrVelocityGradient, AVenhance.spaceGrad]
  rw [hg, amnrWord_zero]

/-- Source material/spatial jets through `cut`, using auxiliary budget `N`.
The material range remains finite because time-cutoff data are only used
through `Nstar`; spatial orders can exceed that cutoff. -/
structure MaterialAuxJetLevels {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (N : ℕ) (K : ℝ) (cut : ℕ) : Prop where
  velocity : ∀ m α r, r ≤ cut → amnrMixedWord α r ≠ [] →
    α.length + 2 * r + 1 ≤ N → ∀ i z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
        K * D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r
  gradient : ∀ m α r, r ≤ cut →
    α.length + 2 * r + 2 ≤ N → ∀ i p z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z| ≤
        K * D.velocityAmplitude m *
          (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r

/-- Spatial velocity jets at arbitrary finite auxiliary order follow from
the all-order spatial displays of the stream-regularity estimates, with no bound on the velocity value. -/
theorem material_aux_velocity_nonempty_spatial_abs_le_of_A3
    {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (hne : α ≠ []) {N : ℕ}
    (hbudget : α.length + 1 ≤ N) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      amnrSpatialVelocityConstant N * D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length := by
  rcases List.eq_nil_or_concat α with hnil | ⟨η, p, hα⟩
  · exact (hne hnil).elim
  · have hα' : α = η ++ [p] := by simpa only [List.concat_eq_append] using hα
    rw [hα'] at hbudget ⊢
    simp only [List.length_append, List.length_singleton] at hbudget
    let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
    have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)).smooth
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y i) := (contDiff_apply ℝ ℝ i).comp hb
    have heq : amnrWord b [some p] (fun y => b y i) = amnrVelocityGradient b i p := by
      funext y
      exact amnrOp_space (hf.differentiable (by simp) y) p
    simp only [List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [amnrWord_append, heq]
    have hh := MaterialAuxiliaryFlow.velocityGradient_spatial_le_of_A3_auxiliary_budget
      hseq hreg hm η N (by omega) i p z
    have hE := D.epsilon_pos (m)
    have hscale : D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ = D.velocityAmplitude m := by
      calc
        _ = D.epsilon m ^ (β - 2) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
          exact congrArg (fun e : ℝ => D.epsilon m ^ e) (by ring)
        _ = D.velocityAmplitude m := by
          rw [D.velocityAmplitude_eq]
          exact congrArg (fun e : ℝ => D.epsilon m ^ e) (by ring)
    rw [pow_succ]
    calc
      _ ≤ amnrSpatialVelocityConstant N * D.velocityAmplitude m *
            (D.epsilon m)⁻¹ ^ η.length := hh
      _ = amnrSpatialVelocityConstant N *
            (D.epsilon m ^ (β - 1) *
              (D.epsilon m)⁻¹) *
            (D.epsilon m)⁻¹ ^ η.length := by rw [hscale]
      _ = amnrSpatialVelocityConstant N * D.epsilon m ^ (β - 1) *
            ((D.epsilon m)⁻¹ ^ η.length *
              (D.epsilon m)⁻¹) := by ring

/-- The zero material level is precisely the source spatial stream-regularity estimate. -/
theorem material_aux_jet_levels_spatial {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ) {N : ℕ} :
    ∃ K : ℝ, 1 ≤ K ∧ MaterialAuxJetLevels D Φ N K 0 := by
  let K := max 1 (amnrSpatialVelocityConstant N)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  constructor
  · intro m α r hr hne hbudget i z
    have hr0 : r = 0 := by omega
    subst r
    have hα : α ≠ [] := by
      intro hnil
      apply hne
      simp [hnil, amnrMixedWord]
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil,
      pow_zero, mul_one, Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [material_aux_streamVelocity_zero_word D hseq]
      simp only [Pi.zero_apply, abs_zero]
      have hE := D.epsilon_pos (0)
      positivity
    · have hh := material_aux_velocity_nonempty_spatial_abs_le_of_A3
        D hseq hreg (by omega : 1 ≤ m) α hα hbudget i z
      have hle : amnrSpatialVelocityConstant N ≤ K := le_max_right _ _
      have hE := D.epsilon_pos (m)
      have hInv : 0 ≤ (D.epsilon m)⁻¹ := inv_nonneg.mpr hE.le
      have hV : 0 ≤ D.epsilon m ^ (β - 1) :=
        Real.rpow_nonneg hE.le _
      calc
        _ ≤ amnrSpatialVelocityConstant N *
            (D.epsilon m ^ (β - 1) *
              (D.epsilon m)⁻¹ ^ α.length) := by
          simpa [mul_assoc] using hh
        _ ≤ K * (D.epsilon m ^ (β - 1) *
            (D.epsilon m)⁻¹ ^ α.length) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hV (pow_nonneg hInv _))
        _ = _ := by ring
  · intro m α r hr hbudget i p z
    have hr0 : r = 0 := by omega
    subst r
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil,
      pow_zero, mul_one, Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [material_aux_streamGradient_zero_word D hseq]
      simp only [Pi.zero_apply, abs_zero]
      have hE := D.epsilon_pos (0)
      have hA : 0 < D.velocityAmplitude 0 := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos 0) _
      positivity
    · have hh := MaterialAuxiliaryFlow.velocityGradient_spatial_le_of_A3_auxiliary_budget
        hseq hreg (by omega : 1 ≤ m) α N (by omega : α.length ≤ N) i p z
      have hle : amnrSpatialVelocityConstant N ≤ K := le_max_right _ _
      have hE := D.epsilon_pos (m)
      have hA : 0 < D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
      have hInv : 0 ≤ (D.epsilon m)⁻¹ := inv_nonneg.mpr hE.le
      calc
        _ ≤ amnrSpatialVelocityConstant N * D.velocityAmplitude m *
            (D.epsilon m)⁻¹ ^ α.length := hh
        _ ≤ K * D.velocityAmplitude m *
            (D.epsilon m)⁻¹ ^ α.length := by
          have h1 := mul_le_mul_of_nonneg_right hle hA.le
          exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hInv α.length)
        _ = _ := by ring

/-- Fast velocity mixed jets use the differentiated recursion and lower
material-gradient jets, with the source material order kept at `Nstar`. -/
private theorem material_aux_streamIncrement_mixed_current_abs_le_independent_budget
    {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (word : List (Fin 2)) (ell : ℕ)
    {Nspace : ℕ} (hword : word.length ≤ Nspace)
    (hell : ell ≤ AVenhance.Nstar β) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord word ell)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      (materialAuxStreamMixedCurrentConstant D Nspace * D.velocityAmplitude m *
        D.epsilon m ^ 2) * (D.epsilon m)⁻¹ ^ word.length *
        D.velocityAmplitude m ^ ell := by
  have hh := material_aux_streamIncrement_mixed_abs_le_of_A3
    D hseq hreg hm word ell hword (by
      have hβeq : 1 + (β - 1) = β := by ring
      simpa [hβeq] using hell) z
  have hp := fine_time_power_le_current_amplitude D hm
    (N := AVenhance.Nstar β) hell
  have hbase : 0 ≤ 3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace *
      D.velocityAmplitude m * D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length := by
    have hChat : 0 ≤ D.Chat := le_trans (by norm_num) D.one_le_Chat
    have hCzeta : 0 ≤ D.Czeta := le_trans (by norm_num) D.one_le_Czeta
    have hK := amnrTransportSpatialConstant_pos Nspace
    have hA : 0 < D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
    have hE : 0 < D.epsilon m := D.epsilon_pos m
    positivity
  have hmul := mul_le_mul_of_nonneg_left hp hbase
  calc
    _ ≤ 3 * (((2 : ℝ) ^ ell * D.Chat * D.Czeta) *
        (amnrTransportSpatialConstant Nspace * D.velocityAmplitude m *
          D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length) *
        (D.tau m)⁻¹ ^ ell) := hh
    _ = (3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace *
          D.velocityAmplitude m * D.epsilon m ^ 2 *
          (D.epsilon m)⁻¹ ^ word.length) *
        ((2 : ℝ) ^ ell * (D.tau m)⁻¹ ^ ell) := by ring
    _ ≤ (3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace *
          D.velocityAmplitude m * D.epsilon m ^ 2 *
          (D.epsilon m)⁻¹ ^ word.length) *
        ((2 * (2 : ℝ) ^ 34) ^ AVenhance.Nstar β *
          D.velocityAmplitude m ^ ell) := hmul
    _ = _ := by
      unfold materialAuxStreamMixedCurrentConstant
      ring_nf

theorem material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
    {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {K : ℝ} {Nspace cut : ℕ}
    (hlevels : MaterialAuxJetLevels D Φ Nspace K cut)
    (hK : 0 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (n : ℕ)
    (hn : n ≤ cut + 1) (hcutN : cut + 1 ≤ AVenhance.Nstar β)
    (hbudget : α.length + 1 + 2 * n ≤ Nspace)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α n)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i -
        AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i) z| ≤
      ((1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
        materialAuxStreamMixedCurrentConstant D Nspace) *
        D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let f := fun y : AmnrSpace => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2
  let q : Fin 2 := if i = 0 then 1 else 0
  let S := (D.epsilon m)⁻¹
  let H := D.velocityAmplitude m
  let F := materialAuxStreamMixedCurrentConstant D Nspace * H * D.epsilon m ^ 2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1))).smooth
  have hf := material_aux_streamIncrement_contDiff D hseq m
  have hE := D.epsilon_pos m
  have hH : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
  have hS : 0 ≤ S := inv_nonneg.mpr hE.le
  have hH0 : 0 ≤ H := hH.le
  have hF : 0 ≤ F := by
    dsimp [F]
    have hCurrent := materialAuxStreamMixedCurrentConstant_nonneg D Nspace
    positivity
  have hfb : ∀ η r, r ≤ n → η.length + 2 * r ≤ Nspace →
      |amnrWord b (amnrMixedWord η r) f z| ≤ F * S ^ η.length * H ^ r := by
    intro η r hr hη
    have hη' : η.length ≤ Nspace := by omega
    have hr' : r ≤ AVenhance.Nstar β := (hr.trans hn).trans hcutN
    have hs := material_aux_streamIncrement_mixed_current_abs_le_independent_budget
      D hseq hreg hm η r hη' hr' z
    simpa [b, f, S, H, F, mul_assoc, mul_left_comm, mul_comm] using hs
  have hBb : ∀ p q' η r, r < n → η.length + 2 * r + 2 ≤ Nspace →
      |amnrWord b (amnrMixedWord η r) (amnrVelocityGradient b p q') z| ≤
        K * H * S ^ η.length * H ^ r := by
    intro p q' η r hr hη
    have hr' : r ≤ cut := by omega
    have hs := hlevels.gradient (m - 1) η r hr' hη p q' z
    have hEF := material_aux_epsilon_current_le_prev D hm
    have hPrev := D.epsilon_pos (m - 1)
    have hscale := amnr_gradient_material_scale_antitone hE hPrev hEF (hβlt_of_data D) η.length r
    have hscaled := mul_le_mul_of_nonneg_left hscale hK
    calc
      _ ≤ K * (D.velocityAmplitude (m - 1) *
          (D.epsilon (m - 1))⁻¹ ^ η.length *
          D.velocityAmplitude (m - 1) ^ r) := by
        convert hs using 1; ring
      _ ≤ K * (H * S ^ η.length * H ^ r) := by
        have hβexp : (β - 1) - 1 = β - 2 := by ring
        simpa [H, S, D.velocityAmplitude_eq, hβexp, mul_assoc, mul_left_comm,
          mul_comm] using hscaled
      _ = _ := by ring
  have hh := amnr_material_gradient_mixed_abs_le_of_bounded_lower_gradient_bounds hb hf
    (N := Nspace) (cut := n) hS hH0 hF hK z hfb hBb
    n le_rfl α 0 (by omega) (by omega) q
  simp only [List.replicate_zero, amnrWord, Nat.add_zero] at hh
  rw [material_aux_fastVelocity_component D hseq m i, amnrWord_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [show |if i = 0 then (-1 : ℝ) else 1| = 1 by split_ifs <;> norm_num, one_mul]
  change |amnrWord b (amnrMixedWord α n) (amnrOp b (some q) f) z| ≤ _
  have hAmp : H * D.epsilon m = D.epsilon m ^ (β - 1) := by
    change D.velocityAmplitude m * D.epsilon m = _
    rw [D.velocityAmplitude_eq]
    have hβexp : (β - 1) - 1 = β - 2 := by ring
    rw [hβexp]
    exact amnr_amplitude_gradient_scale hE
  have hcancel := amnr_stream_amplitude_spatial_cancel (A := H) (β := β) hE
    hAmp α.length
  refine hh.trans_eq ?_
  dsimp [F, H, S]
  calc
    _ = ((1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
        materialAuxStreamMixedCurrentConstant D Nspace) *
        (D.velocityAmplitude m * D.epsilon m ^ 2 *
          (D.epsilon m)⁻¹ ^ (α.length + 1)) *
          D.velocityAmplitude m ^ n := by ring
    _ = _ := by rw [hcancel]; ring

/-- Uniform fast-velocity constant for the auxiliary material word budget. -/
def materialAuxHigherFastConstant {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    (K : ℝ) (N : ℕ) : ℝ :=
  max 1 ((1 + (2 : ℝ) ^ (N + 1) * K) ^ N *
    materialAuxStreamMixedCurrentConstant D N)

theorem materialAuxHigherFastConstant_one_le {β s q K : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) (N : ℕ) :
    1 ≤ materialAuxHigherFastConstant D K N := le_max_left _ _

/-- Scale-step constant for changing the velocity in a material word. -/
def materialAuxHigherVelocityStepConstant {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    (K : ℝ) (N n k : ℕ) : ℝ :=
  let D := materialAuxHigherFastConstant D K N
  let R := amnrNormalOrderConstant (N - 1) K (N - 1)
  D + ((amnrMaterialErrorCardinality n * (n + 1) ^ k : ℕ) : ℝ) *
    (R * D) ^ n * (R * (K + D))

theorem materialAuxHigherVelocityStepConstant_nonneg {β s q K : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) (hK : 0 ≤ K) (N n k : ℕ) :
    0 ≤ materialAuxHigherVelocityStepConstant D K N n k := by
  have hD : 0 ≤ materialAuxHigherFastConstant D K N :=
    le_trans (by norm_num) (materialAuxHigherFastConstant_one_le (K := K) D N)
  have hR : 0 ≤ amnrNormalOrderConstant (N - 1) K (N - 1) :=
    le_trans (by norm_num) (amnrNormalOrderConstant_one_le hK (N - 1))
  unfold materialAuxHigherVelocityStepConstant
  dsimp
  positivity

/-- One higher source material order follows from strictly lower velocity
and gradient levels plus the all-order transported fast increment. -/
theorem material_aux_velocity_higher_source_step {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (Data : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds Data C Φ)
    {Nspace n m : ℕ} {K : ℝ} (hn : 1 ≤ n)
    (hnN : n ≤ AVenhance.Nstar β)
    (hlevels : MaterialAuxJetLevels Data Φ Nspace K (n - 1))
    (hK : 1 ≤ K) (α : List (Fin 2))
    (hbudget : α.length + 2 * n + 1 ≤ Nspace)
    (hm : 1 ≤ m) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
          (List.replicate n none) (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) -
        amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          (List.replicate n none) (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i)) z|
      ≤ materialAuxHigherVelocityStepConstant Data K Nspace n α.length *
        Data.epsilon m ^ (β - 1) *
        (Data.epsilon m)⁻¹ ^ α.length * Data.velocityAmplitude m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
  let c := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let S := (Data.epsilon m)⁻¹
  let H := Data.velocityAmplitude m
  let V := Data.epsilon m ^ (β - 1)
  let fast := materialAuxHigherFastConstant Data K Nspace
  let R := amnrNormalOrderConstant (Nspace - 1) K (Nspace - 1)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible Data.hζ Data.hΛ hseq m)).smooth
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (AVRegularity.Velocity.streamSeq_admissible Data.hζ Data.hΛ hseq (m - 1))).smooth
  have hE := Data.epsilon_pos (m)
  have hH : 0 ≤ H := by
    dsimp [H]
    rw [Data.velocityAmplitude_eq]
    exact (Real.rpow_pos_of_pos (Data.epsilon_pos m) _).le
  have hVS : V * S = H := by
    dsimp [V, S, H]
    rw [Data.velocityAmplitude_eq]
    rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
    congr 1
  have hFastBase : 1 ≤ 1 + (2 : ℝ) ^ (Nspace + 1) * K := by
    have hpow : 0 ≤ (2 : ℝ) ^ (Nspace + 1) := by positivity
    have hK0 : 0 ≤ K := by linarith
    have hmul : 0 ≤ (2 : ℝ) ^ (Nspace + 1) * K := mul_nonneg hpow hK0
    linarith
  have hFastCoeff (r : ℕ) (hrN : r ≤ Nspace) :
      (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ r *
        materialAuxStreamMixedCurrentConstant Data Nspace ≤ fast := by
    have hAux := materialAuxStreamMixedCurrentConstant_nonneg Data Nspace
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hFastBase hrN) hAux
    dsimp [fast, materialAuxHigherFastConstant]
    exact hp.trans (le_max_right _ _)
  have hfast (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hη : η.length + 2 * r + 1 ≤ Nspace) (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (amnrAdvectionVelocity b c p) z| ≤
        (fast * V) * amnrWeight S H (amnrMixedWord η r) := by
    change |amnrWord c (amnrMixedWord η r) (fun y => b y p - c y p) z| ≤ _
    have hh := material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
      Data hseq hreg hlevels (by linarith) hm η r
      (by omega) (by omega) (by omega) p z
    have hrate : 0 ≤ V * S ^ η.length * H ^ r := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hFastCoeff r (by omega)) hrate
    calc
      _ ≤ (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ r *
          materialAuxStreamMixedCurrentConstant Data Nspace * V * S ^ η.length * H ^ r := by
        simpa [b, c, V, S, H, amnrAdvectionVelocity, mul_assoc, mul_left_comm,
          mul_comm] using hh
      _ ≤ fast * V * S ^ η.length * H ^ r := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (fast * V) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have hcoarse (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hne : amnrMixedWord η r ≠ [])
      (hη : η.length + 2 * r + 1 ≤ Nspace) (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (fun y => c y p) z| ≤
        (K * V) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := hlevels.velocity (m - 1) η r (by omega) hne hη p z
    have hkr : 1 ≤ η.length + r := by
      by_contra hh0
      have hη0 : η = [] := List.length_eq_zero_iff.mp (by omega)
      have hr0 : r = 0 := by omega
      apply hne
      simp [hη0, hr0, amnrMixedWord]
    have hscale := amnr_higher_velocity_scale_antitone hE
      (Data.epsilon_pos (m - 1))
      (material_aux_epsilon_current_le_prev Data hm) (hβlt_of_data Data) η.length r hkr
    have hh' := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ K)
    calc
      _ ≤ K * (Data.epsilon (m - 1) ^ (β - 1) *
          (Data.epsilon (m - 1))⁻¹ ^ η.length *
          Data.velocityAmplitude (m - 1) ^ r) := by
        convert hh using 1; ring
      _ ≤ K * (V * S ^ η.length * H ^ r) := by
        have hβexp : (β - 1) - 1 = β - 2 := by ring
        simpa [V, S, H, Data.velocityAmplitude_eq, hβexp, mul_assoc,
          mul_left_comm, mul_comm] using hh'
      _ = (K * V) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have hB (p q : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hr : r < n) (hη : η.length + 2 * r + 2 ≤ Nspace) :
      |amnrWord c (amnrMixedWord η r) (amnrVelocityGradient c p q) z| ≤
        (K * H) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := hlevels.gradient (m - 1) η r (by omega) hη p q z
    have hscale := amnr_gradient_material_scale_antitone
      (Data.epsilon_pos m)
      (Data.epsilon_pos (m - 1))
      (material_aux_epsilon_current_le_prev Data hm) (hβlt_of_data Data) η.length r
    have hh' := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ K)
    calc
      _ ≤ K * (Data.velocityAmplitude (m - 1) *
          (Data.epsilon (m - 1))⁻¹ ^ η.length *
          Data.velocityAmplitude (m - 1) ^ r) := by
        convert hh using 1; ring
      _ ≤ K * (H * S ^ η.length * H ^ r) := by
        have hβexp : (β - 1) - 1 = β - 2 := by ring
        simpa [H, S, Data.velocityAmplitude_eq, hβexp, mul_assoc, mul_left_comm,
          mul_comm] using hh'
      _ = (K * H) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have htop := material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
    Data hseq hreg hlevels (by linarith) hm α n (by omega) (by omega) (by omega) i z
  have htopRate : 0 ≤ V * S ^ α.length * H ^ n := by positivity
  have htopMul := mul_le_mul_of_nonneg_right (hFastCoeff n (by omega)) htopRate
  have htop' : |amnrWord c (amnrMixedWord α n) (amnrAdvectionVelocity b c i) z| ≤
      fast * V * S ^ α.length * H ^ n := by
    change |amnrWord c (amnrMixedWord α n) (fun y => b y i - c y i) z| ≤ _
    calc
      _ ≤ (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
          materialAuxStreamMixedCurrentConstant Data Nspace * V * S ^ α.length * H ^ n := by
        simpa [b, c, V, S, H, amnrAdvectionVelocity, mul_assoc, mul_left_comm,
          mul_comm] using htop
      _ ≤ fast * V * S ^ α.length * H ^ n := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htopMul
  have hstep := amnr_velocity_higher_step_abs_le_of_lower_bounds hb hc
    (inv_nonneg.mpr hE.le) hH (Real.rpow_nonneg hE.le _)
    (materialAuxHigherFastConstant_one_le (K := K) Data Nspace)
    (by linarith) (by linarith) hVS α n hn (by omega) i z hfast hcoarse hB htop'
  simpa [amnrMixedWord, amnrWord_append, fast, R, V, S, H,
    materialAuxHigherVelocityStepConstant, materialAuxHigherFastConstant] using hstep

/-- The higher material velocity jets telescope over scales. Their exponent
is uniformly negative, so the new constant is independent of the scale. -/
theorem material_aux_velocity_higher_material_abs_le_of_source_lower_levels
    {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {Nspace n : ℕ} {K : ℝ} (hn : 1 ≤ n)
    (hnN : n ≤ AVenhance.Nstar β)
    (hlevels : MaterialAuxJetLevels D Φ Nspace K (n - 1))
    (hK : 1 ≤ K) (m : ℕ) (α : List (Fin 2))
    (hbudget : α.length + 2 * n + 1 ≤ Nspace) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
      (amnrMixedWord α n) (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      (2 * materialAuxHigherVelocityStepConstant D K Nspace n α.length) *
        D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ n := by
  let b (j : ℕ) := fun y : AmnrSpace => AVenhance.streamVel (Φ j) y.1 y.2
  let F (j : ℕ) := amnrWord (b j) (List.replicate n none) (fun y => b j y i)
  let q := β - 1 + (β - 2) * (n : ℝ) - (α.length : ℝ)
  let v (j : ℕ) := amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F j) z
  let u (j : ℕ) := D.epsilon j ^ q
  let S := materialAuxHigherVelocityStepConstant D K Nspace n α.length
  have hS : 0 ≤ S := materialAuxHigherVelocityStepConstant_nonneg D (by linarith) Nspace n α.length
  have hF (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F j) := by
    have hb :=
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq j)).smooth
    exact contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
      ((contDiff_apply ℝ ℝ i).comp hb).contDiffOn (List.replicate n none))
  have hzero : v 0 = 0 := by
    have hFb : F 0 = 0 := material_aux_streamVelocity_zero_word D hseq _ i
    simp [v, hFb, amnrWord_zero]
  have hstep (j : ℕ) : |v (j + 1) - v j| ≤ S * u (j + 1) := by
    have hh := material_aux_velocity_higher_source_step (m := j + 1) D hseq hreg
      hn hnN hlevels hK α hbudget (by omega) i z
    have hs := amnrWord_sub_global
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : AmnrSpace => (0 : Vec 2)))
      (hF (j + 1)) (hF j) (α.map some)
    have hscale := amnr_higher_material_spatial_scale (β := β)
      (D.epsilon_pos (j + 1)) α.length n
    rw [amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))] at hh
    change |amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F (j + 1) - F j) z| ≤ _ at hh
    rw [hs] at hh
    refine hh.trans_eq ?_
    change materialAuxHigherVelocityStepConstant D K Nspace n α.length *
        D.epsilon (j + 1) ^ (β - 1) *
        (D.epsilon (j + 1))⁻¹ ^ α.length *
        D.velocityAmplitude (j + 1) ^ n =
      S * D.epsilon (j + 1) ^ q
    rw [show q = β - 1 + (β - 2) * (n : ℝ) - (α.length : ℝ) by rfl]
    dsimp [S]
    rw [← hscale]
    rw [D.velocityAmplitude_eq]
    ring_nf
  have hh := amnr_abs_recursion_sum v u hS
    (fun j => Real.rpow_nonneg (D.epsilon_pos (j)).le _)
    hzero hstep m
  have hq := amnr_higher_material_exponent_le (hβlt_of_data D) α.length n hn
  have hsum := material_aux_negative_power_sum D hq m
  have hb := hh.trans (mul_le_mul_of_nonneg_left hsum hS)
  rw [amnrMixedWord, amnrWord_append,
    amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))]
  refine hb.trans_eq ?_
  have hscale := amnr_higher_material_spatial_scale (β := β)
    (D.epsilon_pos m) α.length n
  change S * (2 * D.epsilon m ^ q) = _
  rw [← hscale]
  dsimp [S]
  rw [D.velocityAmplitude_eq]
  ring_nf


/-- The source constant after one auxiliary material induction level. -/
def materialAuxVelocityAdvanceConstant {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    (K : ℝ) (N cut : ℕ) : ℝ :=
  K + 2 * materialAuxHigherVelocityStepConstant D K N (cut + 1) N

theorem materialAuxVelocityAdvanceConstant_nonneg {β s q K : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) (hK : 0 ≤ K) (N cut : ℕ) :
    0 ≤ materialAuxVelocityAdvanceConstant D K N cut := by
  have hstep := materialAuxHigherVelocityStepConstant_nonneg D hK N (cut + 1) N
  unfold materialAuxVelocityAdvanceConstant
  exact add_nonneg hK (mul_nonneg (by norm_num) hstep)

theorem materialAuxHigherVelocityStepConstant_mono_spatial {β s q K : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) (hK : 0 ≤ K) (N n : ℕ)
    {k l : ℕ} (hkl : k ≤ l) :
    materialAuxHigherVelocityStepConstant D K N n k ≤
      materialAuxHigherVelocityStepConstant D K N n l := by
  have hD : 1 ≤ materialAuxHigherFastConstant D K N :=
    materialAuxHigherFastConstant_one_le (K := K) D N
  have hR := amnrNormalOrderConstant_one_le (N := N - 1) hK (N - 1)
  dsimp [materialAuxHigherVelocityStepConstant]
  simp only [Nat.cast_mul, Nat.cast_pow]
  gcongr
  exact_mod_cast (show 1 ≤ n + 1 by omega)

/-- Extend the velocity part of the source invariant through its next
material order, summing the actual scale increments. -/
theorem material_aux_velocity_advance {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {N cut : ℕ} {K : ℝ}
    (hlevels : MaterialAuxJetLevels D Φ N K cut) (hK : 1 ≤ K)
    (hcutN : cut + 1 ≤ AVenhance.Nstar β)
    (m : ℕ) (α : List (Fin 2)) (r : ℕ)
    (hr : r ≤ cut + 1) (hne : amnrMixedWord α r ≠ [])
    (hbudget : α.length + 2 * r + 1 ≤ N)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
      (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      materialAuxVelocityAdvanceConstant D K N cut *
        D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r := by
  let Knew := materialAuxVelocityAdvanceConstant D K N cut
  have hK0 : 0 ≤ K := by linarith
  have hKle : K ≤ Knew := by
    have hstep := materialAuxHigherVelocityStepConstant_nonneg D hK0 N (cut + 1) N
    dsimp [Knew, materialAuxVelocityAdvanceConstant]
    linarith
  by_cases hrc : r ≤ cut
  · have hh := hlevels.velocity m α r hrc hne hbudget i z
    have hE := D.epsilon_pos (m)
    have hA : 0 < D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
    have hscale : 0 ≤ D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r := by
      positivity
    calc
      _ ≤ K * (D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ Knew * (D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) :=
        mul_le_mul_of_nonneg_right hKle hscale
      _ = _ := by ring
  · have hrEq : r = cut + 1 := by omega
    subst r
    have hlevels' : MaterialAuxJetLevels D Φ N K (cut + 1 - 1) := by
      simpa using hlevels
    have hh := material_aux_velocity_higher_material_abs_le_of_source_lower_levels
      D hseq hreg (by omega) hcutN hlevels' hK m α hbudget i z
    have hlen : α.length ≤ N := by omega
    have hmono := materialAuxHigherVelocityStepConstant_mono_spatial
      D hK0 N (cut + 1) hlen
    have hcoef : 2 * materialAuxHigherVelocityStepConstant D K N (cut + 1) α.length ≤ Knew := by
      dsimp [Knew, materialAuxVelocityAdvanceConstant]
      nlinarith
    have hE := D.epsilon_pos (m)
    have hA : 0 < D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
    have hscale : 0 ≤ D.epsilon m ^ (β - 1) *
        (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ (cut + 1) := by
      positivity
    calc
      _ ≤ (2 * materialAuxHigherVelocityStepConstant D K N (cut + 1) α.length) *
          (D.epsilon m ^ (β - 1) *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ (cut + 1)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ Knew * (D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ (cut + 1)) :=
        mul_le_mul_of_nonneg_right hcoef hscale
      _ = _ := by ring

/-- Advancing one material level closes the gradient estimates from the
velocity estimates at that same level and the previous gradient level. -/
def materialAuxJetAdvanceConstant {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData (β - 1) s q Λ ζ)
    (K : ℝ) (N cut : ℕ) : ℝ :=
  let Kv := materialAuxVelocityAdvanceConstant D K N cut
  max Kv ((1 + (2 : ℝ) ^ N * K) ^ (cut + 1) * Kv)

theorem material_aux_jet_levels_advance {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {N cut : ℕ} {K : ℝ}
    (hlevels : MaterialAuxJetLevels D Φ N K cut) (hK : 1 ≤ K)
    (hcutN : cut + 1 ≤ AVenhance.Nstar β) :
    ∃ Knew : ℝ, 1 ≤ Knew ∧ MaterialAuxJetLevels D Φ N Knew (cut + 1) := by
  let Kv := materialAuxVelocityAdvanceConstant D K N cut
  let Kg := (1 + (2 : ℝ) ^ N * K) ^ (cut + 1) * Kv
  let Knew := materialAuxJetAdvanceConstant D K N cut
  have hK0 : 0 ≤ K := by linarith
  have hKvge : K ≤ Kv := by
    have hstep := materialAuxHigherVelocityStepConstant_nonneg D hK0 N (cut + 1) N
    dsimp [Kv, materialAuxVelocityAdvanceConstant]
    linarith
  have hKv : 1 ≤ Kv := hK.trans hKvge
  have hKgv : 0 ≤ Kg := by
    have hbase : 0 ≤ 1 + (2 : ℝ) ^ N * K := by positivity
    have hKv0 := materialAuxVelocityAdvanceConstant_nonneg D hK0 N cut
    dsimp [Kg]
    exact mul_nonneg (pow_nonneg hbase _) hKv0
  have hKnewgeKv : Kv ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kv]
    exact le_max_left _ _
  have hKnewgeKg : Kg ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kg, Kv]
    exact le_max_right _ _
  have hKnew : 1 ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kv]
    have hleft : 1 ≤ materialAuxVelocityAdvanceConstant D K N cut := hKv
    exact le_trans hleft (le_max_left _ _)
  refine ⟨Knew, hKnew, ?_⟩
  constructor
  · intro m α r hr hne hbudget i z
    by_cases hro : r ≤ cut
    · have hh := hlevels.velocity m α r hro hne hbudget i z
      have hcoeff : K ≤ Knew := le_trans hKvge hKnewgeKv
      have hE := D.epsilon_pos (m)
      have hA : 0 < D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
      have hscale : 0 ≤ D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length *
          D.velocityAmplitude m ^ r := by positivity
      calc
        _ ≤ K * (D.epsilon m ^ (β - 1) *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (D.epsilon m ^ (β - 1) *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = _ := by ring
    · have hr' : r = cut + 1 := by omega
      subst r
      have hh := material_aux_velocity_advance D hseq hreg hlevels hK hcutN
        m α (cut + 1) (by omega) hne hbudget i z
      have hE := D.epsilon_pos (m)
      have hA : 0 < D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
      have hscale : 0 ≤ D.epsilon m ^ (β - 1) *
          (D.epsilon m)⁻¹ ^ α.length *
          D.velocityAmplitude m ^ (cut + 1) := by positivity
      calc
        _ ≤ materialAuxVelocityAdvanceConstant D K N cut *
            (D.epsilon m ^ (β - 1) *
              (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ (cut + 1)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (D.epsilon m ^ (β - 1) *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ (cut + 1)) :=
          mul_le_mul_of_nonneg_right hKnewgeKv hscale
        _ = _ := by ring
  · intro m α r hr hbudget i p z
    by_cases hro : r ≤ cut
    · have hh := hlevels.gradient m α r hro hbudget i p z
      have hcoeff : K ≤ Knew := le_trans hKvge hKnewgeKv
      have hE := D.epsilon_pos (m)
      have hA : 0 < D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
      have hscale : 0 ≤ D.velocityAmplitude m *
          (D.epsilon m)⁻¹ ^ α.length *
          D.velocityAmplitude m ^ r := by positivity
      calc
        _ ≤ K * (D.velocityAmplitude m *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (D.velocityAmplitude m *
            (D.epsilon m)⁻¹ ^ α.length * D.velocityAmplitude m ^ r) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = _ := by ring
    · have hr' : r = cut + 1 := by omega
      subst r
      let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
      let S := (D.epsilon m)⁻¹
      let H := D.velocityAmplitude m
      let V := D.epsilon m ^ (β - 1)
      have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
        (AVenhance.Infra.Construction.smoothPeriodic_streamVel
          (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)).smooth
      have hE := D.epsilon_pos (m)
      have hH : 0 < D.velocityAmplitude m := by
        rw [D.velocityAmplitude_eq]
        exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
      have hVS : V * S = H := by
        dsimp [V, S, H]
        rw [D.velocityAmplitude_eq]
        rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
        congr 1
      have hgrad := amnr_velocityGradient_mixed_abs_le_of_bounded_velocity_jets hb
        (inv_nonneg.mpr hE.le) hH.le (Real.rpow_nonneg hE.le _)
        (materialAuxVelocityAdvanceConstant_nonneg (K := K) D hK0 N cut)
        hK0 hVS α (cut + 1) hbudget i p z
        (fun η r' hr' hne' hbudget' => by
          exact material_aux_velocity_advance D hseq hreg hlevels hK hcutN
            m η r' hr' hne' hbudget' i z)
        (fun j q η r' hlt hbudget' => by
          exact hlevels.gradient m η r' (by omega) hbudget' j q z)
      have hgrad' : |amnrWord b (amnrMixedWord α (cut + 1))
          (amnrVelocityGradient b i p) z| ≤ Kg * H * S ^ α.length * H ^ (cut + 1) := by
        simpa [Kg, H, S, Kv, materialAuxVelocityAdvanceConstant] using hgrad
      have hcoef : Kg ≤ Knew := hKnewgeKg
      have hscale : 0 ≤ H * S ^ α.length * H ^ (cut + 1) := by positivity
      calc
        _ ≤ Kg * (H * S ^ α.length * H ^ (cut + 1)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgrad'
        _ ≤ Knew * (H * S ^ α.length * H ^ (cut + 1)) :=
          mul_le_mul_of_nonneg_right hcoef hscale
        _ = _ := by ring

/-- The differentiated recursion and the actual stream-regularity spatial estimates give
all source word bounds through the paper's material cutoff. The auxiliary
word budget is `2*Nstar+1`; time derivatives of recursion cutoffs never
exceed the literal `Nstar`. -/
theorem material_aux_jet_levels_all_orders_of_A3 {β s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ) :
    ∃ K : ℝ, 1 ≤ K ∧
      MaterialAuxJetLevels D Φ (2 * AVenhance.Nstar β + 1) K
        (AVenhance.Nstar β) := by
  have hlevels : ∀ n : ℕ, n ≤ AVenhance.Nstar β →
      ∃ K : ℝ, 1 ≤ K ∧
        MaterialAuxJetLevels D Φ (2 * AVenhance.Nstar β + 1) K n := by
    intro n
    induction n with
    | zero =>
        intro _
        exact material_aux_jet_levels_spatial D hseq hreg
    | succ n ih =>
        intro hn
        obtain ⟨K, hK, hbase⟩ := ih (by omega)
        exact material_aux_jet_levels_advance D hseq hreg hbase hK (by omega)
  exact hlevels (AVenhance.Nstar β) le_rfl

end AVRegularity.Velocity.Port.MaterialAuxiliaryInduction
end

section
open Homogenization
namespace AVRegularity.Velocity.Port.MaterialFlowTime

/-! Temporal material-Jacobian consequences of the source flow package. -/

theorem iteratedTimeDerivative_neg_local
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : ℕ) (f : ℝ → E) :
    AVRegularity.Velocity.Port.MaterialGoalSource.iteratedTimeDerivative ell
        (fun t => -f t) =
      fun t => -AVRegularity.Velocity.Port.MaterialGoalSource.iteratedTimeDerivative ell f t := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      funext t
      simp [AVRegularity.Velocity.Port.MaterialGoalSource.iteratedTimeDerivative, ih]

end AVRegularity.Velocity.Port.MaterialFlowTime
end
