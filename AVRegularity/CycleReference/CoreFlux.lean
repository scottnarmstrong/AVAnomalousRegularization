-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.TestDriftIntegrability
import AVenhance.Infra.Classical.PeriodicCalculus
public import AVRegularity.CycleReference.PlaneCoefficientCongruence
public import AVRegularity.CycleReference.SpacetimeGradientPairing
import AVRegularity.Velocity.Port.StreamRegularity
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseStream
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux
public import AVenhance.Statements.Construction.BarNorm
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Integrability consequences of the full periodic tested equation. -/

 theorem spaceGrad_periodic {η : Vec 2 → ℝ} (hp : IsZ2Periodic η) :
    IsZ2Periodic (spaceGrad η) := by
  intro k x
  funext i
  exact Infra.Classical.periodic_spaceGrad_component hp i k x

 theorem timeDeriv_periodic {η : ℝ → Vec 2 → ℝ}
    (hp : ∀ t, IsZ2Periodic (η t)) (t : ℝ) :
    IsZ2Periodic (fun x => deriv (fun r => η r x) t) := by
  intro k x
  have he : (fun r => η r (x + latticeShift k)) = (fun r => η r x) :=
    funext (fun r => hp r k x)
  exact congrArg (fun f : ℝ → ℝ => deriv f t) he

 theorem torus_tested_integrability_implies_mul_test_integrability
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (a c : ℝ)
    (hI : ∀ η : ℝ → Vec 2 → ℝ, IsWindowTestFunction c η →
      Integrable (planeWeakIntegrand b A q f θ Dθ η)
        (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (η : ℝ → Vec 2 → ℝ) (hη : IsWindowTestFunction c η) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * η p.1 p.2)
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  have hIη := hI η hη
  have hItη := hI (fun t x => t * η t x)
    ⟨contDiff_fst.mul hη.1, fun t k x => by dsimp only; rw [hη.2.1 t k x],
      fun t ht x => by dsimp only; rw [hη.2.2 t ht x, mul_zero]⟩
  have hbound : ∀ᵐ p : ℝ × Vec 2 ∂(volume.restrict (Set.Ioo a c ×ˢ unitCube)),
      ‖p.1‖ ≤ |a| + |c| := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
      (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have ha := neg_abs_le a
      have hc := abs_nonneg c
      linarith [hp.1.1]
    · have ha := abs_nonneg a
      have hc := le_abs_self c
      linarith [hp.1.2]
  have hweighted := hIη.bdd_mul continuous_fst.aestronglyMeasurable hbound
  convert hweighted.sub hItη using 1
  funext p
  simp only [Pi.sub_apply]
  rw [planeWeakIntegrand_time_mul b A q f θ Dθ η hη.1 p]
  ring

 theorem torus_tested_integrability_implies_drift_correction_integrability
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (a c : ℝ)
    (hI : ∀ η : ℝ → Vec 2 → ℝ, IsWindowTestFunction c η →
      Integrable (planeWeakIntegrand b A q f θ Dθ η)
        (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (B : ℝ → Vec 2 → Vec 2)
    (hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => B p.1 p.2))
    (hpB : ∀ t, IsZ2Periodic (B t))
    (η : ℝ → Vec 2 → ℝ) (hη : IsWindowTestFunction c η) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 *
      Homogenization.vecDot (B p.1 p.2) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  let ξ := fun t x => Homogenization.vecDot (B t x) (spaceGrad (η t) x)
  have he : (fun p : ℝ × Vec 2 => ξ p.1 p.2) =
      (fun p => B p.1 p.2 0 * spaceGrad (η p.1) p.2 0 +
        B p.1 p.2 1 * spaceGrad (η p.1) p.2 1) := by
    funext p
    simp [ξ, Homogenization.vecDot, Fin.sum_univ_two]
  have hξ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ξ p.1 p.2) := by
    rw [he]
    exact (((contDiff_apply ℝ ℝ 0).comp hB).mul (joint_spaceGrad_smooth hη.1 0)).add
      (((contDiff_apply ℝ ℝ 1).comp hB).mul (joint_spaceGrad_smooth hη.1 1))
  have hpξ : ∀ t, IsZ2Periodic (ξ t) := by
    intro t k x
    dsimp [ξ]
    rw [hpB t k x, spaceGrad_periodic (hη.2.1 t) k x]
  have hzξ : ∀ t, c ≤ t → ∀ x, ξ t x = 0 := by
    intro t ht x
    dsimp [ξ]
    rw [spaceGrad_eq_zero_of_eq_zero (hη.2.2 t ht)]
    simp [Homogenization.vecDot]
  exact torus_tested_integrability_implies_mul_test_integrability b A q f θ Dθ a c hI ξ
    ⟨hξ, hpξ, hzξ⟩

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
open AVRegularity.Velocity AVRegularity.Velocity.Port
namespace AVRegularity.CycleReference

/-! The inverse-flow regularity package applies to adjacent renewal charts. -/

theorem adjacent_time_difference {h : ℝ} (hh : 0 ≤ h) {l₁ l₂ : ℤ}
    (hl : l₂ = l₁ + 1 ∨ l₁ = l₂ + 1) :
    |(l₂ : ℝ) * h - (l₁ : ℝ) * h| = h := by
  rcases hl with hl | hl
  · subst l₂
    rw [Int.cast_add, Int.cast_one]
    rw [show ((l₁ : ℝ) + 1) * h - (l₁ : ℝ) * h = h by ring, abs_of_nonneg hh]
  · subst l₁
    rw [Int.cast_add, Int.cast_one]
    rw [show (l₂ : ℝ) * h - ((l₂ : ℝ) + 1) * h = -h by ring, abs_neg, abs_of_nonneg hh]

theorem transition_jacobian_bar_bounds
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 2 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l₁ l₂ : ℤ) (hl : l₂ = l₁ + 1 ∨ l₁ = l₂ + 1) :
    ∀ n i a, barNorm n (2 ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹)
      (fun x => jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) x i a -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤
      ENNReal.ofReal (2 ^ 23 * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) := by
  let D := ocJetRecursionData α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ ζ hζ
  have hα : (α + 1) - 1 = α := by ring
  have hout := StreamRegularity.section2_induction_outputs_from_source_data (β := α + 1) (s := s) (q := q) (Λ := Λ) (ζ := ζ) (Φ := Φ)
  rw [hα] at hout
  obtain ⟨C, _, hflow⟩ := (hout D hseq).2
  let h := ocTauPP α q Λ m
  have hh : 0 < h := D.tauPP_pos m (by omega)
  have ha : 0 < D.velocityAmplitude (m - 1) := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
  have hδ := (Scales.admissible_delta_mu_positive hα₀ hα₁ hs₀ hs₁ hq).1
  have ht : h ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude (m - 1))⁻¹ := by
    have hb := D.block_small m (by omega)
    have he := Real.rpow_le_one (D.epsilon_pos (m - 1)).le
      (D.epsilon_le_one (m - 1)) (by positivity : 0 ≤ 2 * ocDelta α q)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left he (by positivity))
    rw [le_mul_inv_iff₀ ha]
    change D.tauPP m * D.velocityAmplitude (m - 1) ≤ _
    simpa only [one_mul, mul_one, mul_comm] using hb'
  have hadj := adjacent_time_difference hh.le hl
  intro n i a
  have hb := hflow.inverse_regbounds (m - 1) (by omega)
    ((l₁ : ℝ) * h) ((l₂ : ℝ) * h - (l₁ : ℝ) * h)
    (by rw [hadj]; exact ht) n
  have he : (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hseq
      (m - 1) ((l₂ : ℝ) * h - (l₁ : ℝ) * h) ((l₁ : ℝ) * h) x) =
      fderiv ℝ (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) := by
    funext x
    simp only [Section2FlowIdentities.constructionFlowInvJacobian,
      Section2FlowIdentities.streamFlowInvJacobian, Section2FlowIdentities.streamFlowInv,
      flowInv]
    congr 2
    funext y
    congr 1
    ring
  rw [hadj] at hb
  simp_rw [show ∀ x, Section2FlowIdentities.constructionFlowInvJacobian D hseq
      (m - 1) ((l₂ : ℝ) * h - (l₁ : ℝ) * h) ((l₁ : ℝ) * h) x =
      fderiv ℝ (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) x from congrFun he] at hb
  unfold Section2FlowRegularityCore.flowJacobianBarNorm at hb
  have hb' := (le_iSup_of_le i (le_iSup_of_le a le_rfl)).trans hb
  convert hb' using 1
  · congr 1
    funext x
    simp only [jacMatrix, sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply]
    simp [basisVec, Matrix.one_apply, Pi.single_apply]
  · dsimp [D, h]
    congr 1
    dsimp only [ocJetRecursionData]
    ring

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! The stream increment becomes the reference pulse stream on its own block. -/

theorem ocShear_zero_of_not_odd (α q : ℝ) (Λ m : ℕ) {k : ℤ} (hk : ¬ Odd k) (y : Vec 2) :
    ocShear α q Λ m k y = 0 := by
  have hodd : k % 2 ≠ 1 := by simpa only [Int.odd_iff] using hk
  have h1 : k % 4 ≠ 1 := by omega
  have h3 : k % 4 ≠ 3 := by omega
  simp [ocShear, psi0, h1, h3]

theorem ocNextStream_in_chart {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ)
    (ht : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) (y : Vec 2) :
    ocNextStream α q Λ ζ m φ hφ t (ocChart α q Λ m φ hφ l t y) =
      φ t (ocChart α q Λ m φ hφ l t y) + ocPulseStream α q Λ ζ m t y := by
  classical
  let f : ℤ → ℝ := fun k => ocPulse α q Λ ζ m k t * ocShear α q Λ m k
    (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t
      (ocChart α q Λ m φ hφ l t y) ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))
  have hs : Function.support f ⊆ {k : ℤ | Odd k} := by
    intro k hk
    by_contra h
    apply hk
    dsimp [f]
    rw [ocShear_zero_of_not_odd α q Λ m h, mul_zero]
  change φ t (ocChart α q Λ m φ hφ l t y) + (∑' k : ℤ, f k) = _
  congr 1
  rw [← tsum_subtype_eq_of_support_subset hs]
  unfold ocPulseStream
  apply tsum_congr
  intro k
  by_cases hp : ocPulse α q Λ ζ m k.1 t = 0
  · simp [f, hp]
  · have hl := pulse_label_on_block hΛ ht hp
    have hgroup := (streamFlowHomeomorph hφ t ((l : ℝ) * ocTauPP α q Λ m)).left_inv y
    change AVRegularity.streamFlow φ hφ ((l : ℝ) * ocTauPP α q Λ m)
      (ocChart α q Λ m φ hφ l t y) t = y at hgroup
    dsimp [f]
    rw [hl]
    change ocPulse α q Λ ζ m k.1 t * ocShear α q Λ m k.1
      (AVRegularity.streamFlow φ hφ ((l : ℝ) * ocTauPP α q Λ m)
        (ocChart α q Λ m φ hφ l t y) t) = _
    rw [hgroup]

end AVRegularity.CycleReference
end
end

section
@[expose] public section

section
namespace AVRegularity.CycleReference

/-! Pointwise reductions of the glued stream and corrector on an active pulse. -/

open Homogenization

theorem ocPulseStream_eq_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} {t : ℝ} {y : Vec 2}
    (hk : Odd k) (hp : ocPulse α q Λ ζ m k t ≠ 0) :
    ocPulseStream α q Λ ζ m t y = ocPulse α q Λ ζ m k t * ocShear α q Λ m k y := by
  classical
  let slot : {k : ℤ // Odd k} := ⟨k, hk⟩
  change (∑' j : {j : ℤ // Odd j},
    ocPulse α q Λ ζ m j.1 t * ocShear α q Λ m j.1 y) = _
  apply tsum_eq_single slot
  intro j hj
  have hpj : ocPulse α q Λ ζ m j.1 t = 0 := by
    by_contra hne
    have heq := odd_pulse_support_unique hΛ hζ (k := k) (j := j.1)
      (t := t) hk j.2 hp hne
    exact hj (Subtype.ext heq.symm)
  simp [hpj]

theorem ocRefCorrector_eq_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} {k : ℤ}
    (hk : Odd k) (hp : ocPulse α q Λ ζ m k t ≠ 0) :
    ocRefCorrector α q Λ ζ m ν t = ocPulseCorrector α q Λ ζ m ν k t := by
  classical
  let slot : {k : ℤ // Odd k} := ⟨k, hk⟩
  funext y
  change (∑' j : {j : ℤ // Odd j},
    ocCutoff α q Λ m j.1 t • ocPulseCorrector α q Λ ζ m ν j.1 t y) = _
  calc
    _ = ocCutoff α q Λ m k t • ocPulseCorrector α q Λ ζ m ν k t y := by
      apply tsum_eq_single slot
      intro j hj
      have hneval : j.1 ≠ k := by
        intro heq
        exact hj (Subtype.ext heq)
      have hcut := ocCutoff_eq_zero_of_other_slot hΛ hζ hk j.2 hneval hp
      simp [hcut]
    _ = _ := by rw [ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hp]; simp

theorem ocRefCorrector_eq_finset_cutoff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) :
    ocRefCorrector α q Λ ζ m ν t = fun y =>
      ∑ k ∈ (ocCutoff_support_finite (α := α) (q := q) (Λ := Λ) (m := m)
        hΛ (t := t)).toFinset,
        ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y := by
  classical
  let S := ocCutoff_support_finite (α := α) (q := q) (Λ := Λ) (m := m) hΛ (t := t)
  have hzero (k : {k : ℤ // Odd k}) (hk : k ∉ S.toFinset) :
      (fun y => ocCutoff α q Λ m k.1 t •
        ocPulseCorrector α q Λ ζ m ν k.1 t y) = fun _ => 0 := by
    have hcut : ocCutoff α q Λ m k.1 t = 0 := by
      by_contra hne
      exact hk (S.mem_toFinset.mpr hne)
    funext y
    simp [hcut]
  funext y
  change (∑' k : {k : ℤ // Odd k},
      ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y) = _
  rw [tsum_eq_sum (s := S.toFinset)]
  intro k hk
  exact congrFun (hzero k hk) y

end AVRegularity.CycleReference
end

section
open MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Period and half-period integral identities for the reference flux. -/

theorem refFlux_diagonal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (hν : 0 < ν) :
    ocRefFlux α q Λ ζ m ν t 0 1 = 0 ∧ ocRefFlux α q Λ ζ m ν t 1 0 = 0 := by
  rcases refFlux_shape hΛ hζ hν with hactive | hquiet
  · rcases hactive with ⟨k, c, hflux, _, _⟩
    rw [hflux]
    constructor
    · by_cases hk : k.1 % 4 = 1 <;>
        simp [Matrix.add_apply, Matrix.smul_apply, ocPi, Matrix.of_apply, hk]
    · by_cases hk : k.1 % 4 = 1 <;>
        simp [Matrix.add_apply, Matrix.smul_apply, ocPi, Matrix.of_apply, hk]
  · rw [hquiet]
    simp [Matrix.smul_apply]

theorem refFlux_entry_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (_hζ : IsFastProfile ζ) {ν : ℝ} (_hν : 0 < ν)
    (i j : Fin 2) : Function.Periodic (fun t => ocRefFlux α q Λ ζ m ν t i j)
      (4 * ocTauPP α q Λ m) := by
  intro t
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j)
    (refFlux_time_shift_four (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
      hΛ ν t (ocTauPP α q Λ m) rfl)

theorem refFlux_half_shift_00_11 {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (_hν : 0 < ν) :
    ocRefFlux α q Λ ζ m ν (t + 2 * ocTauPP α q Λ m) 0 0 =
      ocRefFlux α q Λ ζ m ν t 1 1 := by
  have h := refFlux_time_shift_two (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
    hΛ hζ ν t (ocTauPP α q Λ m) rfl
  rw [h]
  have hs00 : AVenhance.sigmaMat 0 0 = 0 := by norm_num [AVenhance.sigmaMat, Matrix.of_apply]
  have hs01 : AVenhance.sigmaMat 0 1 = -1 := by norm_num [AVenhance.sigmaMat, Matrix.of_apply]
  have hs10 : AVenhance.sigmaMat 1 0 = 1 := by norm_num [AVenhance.sigmaMat, Matrix.of_apply]
  have hs11 : AVenhance.sigmaMat 1 1 = 0 := by norm_num [AVenhance.sigmaMat, Matrix.of_apply]
  have hconj (M : Matrix (Fin 2) (Fin 2) ℝ) :
      (AVenhance.sigmaMat * M * AVenhance.sigmaMatᵀ) 0 0 = M 1 1 := by
    have hr (j : Fin 2) : (AVenhance.sigmaMat * M) 0 j = -M 1 j := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [hs00, hs01]
    calc
      _ = ∑ a : Fin 2, (AVenhance.sigmaMat * M) 0 a * AVenhance.sigmaMatᵀ a 0 :=
        Matrix.mul_apply
      _ = (AVenhance.sigmaMat * M) 0 0 * AVenhance.sigmaMatᵀ 0 0 +
          (AVenhance.sigmaMat * M) 0 1 * AVenhance.sigmaMatᵀ 1 0 := by
        rw [Fin.sum_univ_two]
      _ = M 1 1 := by
        rw [hr 0, hr 1]
        simp [Matrix.transpose_apply, hs00, hs01]
  exact hconj _

theorem refFlux_diagonal_integrals_equal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) :
    (∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 0 0) =
      ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 1 1 := by
  let T := 4 * ocTauPP α q Λ m
  let d := 2 * ocTauPP α q Λ m
  have hper := refFlux_entry_periodic (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
    hΛ hζ hν (0 : Fin 2) (0 : Fin 2)
  calc
    (∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 0 0) =
        ∫ t in d..(d + T), ocRefFlux α q Λ ζ m ν t 0 0 := by
      simpa [T, d, add_comm, add_left_comm, add_assoc] using
        (Function.Periodic.intervalIntegral_add_eq hper d 0).symm
    _ = ∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν (t + d) 0 0 := by
      convert (intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := T)
        (fun t => ocRefFlux α q Λ ζ m ν t 0 0) d).symm using 1
      ring_nf
    _ = ∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 1 1 := by
      apply intervalIntegral.integral_congr
      intro t _
      exact refFlux_half_shift_00_11
        (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
        hΛ hζ (ν := ν) (t := t) hν

theorem refFlux_full_period_mean_entry {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (i j : Fin 2) :
    (4 * ocTauPP α q Λ m)⁻¹ *
      ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t i j =
      ocMeanFlux α q Λ ζ m ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  let T := 4 * ocTauPP α q Λ m
  have hi00 : IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν t 0 0)
      volume 0 T := by
    exact refFlux_entry_intervalIntegrable hΛ hζ hν 0 0 0 T
  have hi11 : IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν t 1 1)
      volume 0 T := by
    exact refFlux_entry_intervalIntegrable hΛ hζ hν 1 1 0 T
  have htrace : ∀ t : ℝ, Matrix.trace (ocRefFlux α q Λ ζ m ν t) =
      ocRefFlux α q Λ ζ m ν t 0 0 + ocRefFlux α q Λ ζ m ν t 1 1 := by
    intro t
    simp [Matrix.trace, Fin.sum_univ_two]
  have htraceInt :
      (∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), Matrix.trace (ocRefFlux α q Λ ζ m ν t)) =
        (∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 0 0) +
          ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 1 1 := by
    calc
      _ = ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m),
          (ocRefFlux α q Λ ζ m ν t 0 0 + ocRefFlux α q Λ ζ m ν t 1 1) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact htrace t
      _ = _ := intervalIntegral.integral_add hi00 hi11
  have hdiag := refFlux_diagonal_integrals_equal
    (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) hΛ hζ hν
  have hmean00 : (4 * ocTauPP α q Λ m)⁻¹ *
      ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 0 0 =
        ocMeanFlux α q Λ ζ m ν := by
    rw [ocMeanFlux, htraceInt, hdiag]
    ring
  have hmean11 : (4 * ocTauPP α q Λ m)⁻¹ *
    ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t 1 1 =
        ocMeanFlux α q Λ ζ m ν := by
    rw [ocMeanFlux, htraceInt, hdiag]
    ring
  fin_cases i <;> fin_cases j
  · simpa [Matrix.one_apply] using hmean00
  · have hzero : (∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m),
        ocRefFlux α q Λ ζ m ν t 0 1) = 0 := by
      calc
        _ = ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact (refFlux_diagonal (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
            hΛ hζ hν).1
        _ = 0 := by simp
    have hscaled := congrArg (fun x : ℝ => (4 * ocTauPP α q Λ m)⁻¹ * x) hzero
    simpa [Matrix.one_apply] using hscaled
  · have hzero : (∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m),
        ocRefFlux α q Λ ζ m ν t 1 0) = 0 := by
      calc
        _ = ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact (refFlux_diagonal (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
            hΛ hζ hν).2
        _ = 0 := by simp
    have hscaled := congrArg (fun x : ℝ => (4 * ocTauPP α q Λ m)⁻¹ * x) hzero
    simpa [Matrix.one_apply] using hscaled
  · simpa [Matrix.one_apply] using hmean11

theorem refFlux_window_mean_entry {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (s : ℝ) (i j : Fin 2) :
    (4 * ocTauPP α q Λ m)⁻¹ *
      ∫ t in s..(s + 4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t i j =
      ocMeanFlux α q Λ ζ m ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  let T := 4 * ocTauPP α q Λ m
  have hper := refFlux_entry_periodic
    (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) hΛ hζ hν i j
  rw [show (4 * ocTauPP α q Λ m)⁻¹ = T⁻¹ by rfl,
    show s + 4 * ocTauPP α q Λ m = s + T by rfl]
  rw [Function.Periodic.intervalIntegral_add_eq hper s 0]
  simpa [T] using refFlux_full_period_mean_entry hΛ hζ hν i j

/-! Integral trace formula for the scalar reference mean. -/

theorem refFlux_trace_intervalIntegrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (a b : ℝ) :
    IntervalIntegrable (fun t => Matrix.trace (ocRefFlux α q Λ ζ m ν t)) volume a b := by
  have he : (fun t => Matrix.trace (ocRefFlux α q Λ ζ m ν t)) = fun t =>
      ocRefFlux α q Λ ζ m ν t 0 0 + ocRefFlux α q Λ ζ m ν t 1 1 := by
    funext t
    simp [Matrix.trace, Fin.sum_univ_two]
  rw [he]
  exact (refFlux_entry_intervalIntegrable hΛ hζ hν 0 0 a b).add
    (refFlux_entry_intervalIntegrable hΛ hζ hν 1 1 a b)

theorem refFlux_window_trace_integral {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (s : ℝ) :
    (∫ t in s..(s + 4 * ocTauPP α q Λ m), Matrix.trace (ocRefFlux α q Λ ζ m ν t)) =
      2 * ocMeanFlux α q Λ ζ m ν * (4 * ocTauPP α q Λ m) := by
  let T := 4 * ocTauPP α q Λ m
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos (by norm_num) (AVRegularity.Construction.Stream.ocTauPP_pos hΛ)
  have he (i : Fin 2) : (∫ t in s..(s + T), ocRefFlux α q Λ ζ m ν t i i) =
      ocMeanFlux α q Λ ζ m ν * T := by
    have hm := refFlux_window_mean_entry (α := α) (q := q) (m := m) hΛ hζ hν s i i
    simp only [Matrix.one_apply, ite_true, mul_one] at hm
    change T⁻¹ * (∫ t in s..(s + T), ocRefFlux α q Λ ζ m ν t i i) =
      ocMeanFlux α q Λ ζ m ν at hm
    apply (div_eq_iff hT.ne').mp
    rw [div_eq_mul_inv, mul_comm]
    exact hm
  calc
    _ = ∫ t in s..(s + T), (ocRefFlux α q Λ ζ m ν t 0 0 + ocRefFlux α q Λ ζ m ν t 1 1) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp [Matrix.trace, Fin.sum_univ_two]
    _ = _ := by
      rw [intervalIntegral.integral_add (refFlux_entry_intervalIntegrable hΛ hζ hν 0 0 _ _)
        (refFlux_entry_intervalIntegrable hΛ hζ hν 1 1 _ _), he 0, he 1]
      dsimp [T]
      ring

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Normalized memory lower bound on the terminal half of a complete core. -/

theorem pulseMemory_integrableOn {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (k : ℤ) (t : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (-(ocMu q Λ m ν) * r) *
      ocPulse α q Λ ζ m k (t - r)) (Set.Ioi 0) := by
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  have hkernel : IntegrableOn (fun r : ℝ => Real.exp (-(ocMu q Λ m ν) * r)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hcont : Continuous (fun r : ℝ => Real.exp (-(ocMu q Λ m ν) * r) *
      ocPulse α q Λ ζ m k (t - r)) :=
    (Real.continuous_exp.comp (by fun_prop)).mul ((ocPulse_continuous hζ k).comp (by fun_prop))
  apply hkernel.mono' hcont.aestronglyMeasurable
  filter_upwards [] with r
  have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k (t - r)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.1, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left hp.2 (Real.exp_pos _).le).trans_eq (mul_one _)

theorem pulseMemory_core_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (l k : ℤ) (hcore : IsOCCompleteCore α q Λ m l k)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) * ocTau α q Λ m)
      (((k : ℝ) + 1 / 3) * ocTau α q Λ m)) :
    1 - Real.exp (-2) ≤ ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t := by
  let μ := ocMu q Λ m ν
  let d := ocTau α q Λ m / 3
  have hμ : 0 < μ := ocMu_pos hΛ hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hd : 0 < d := div_pos hτ (by norm_num)
  let f : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun r =>
    Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r))
  let g : ℝ → ℝ := (Set.Ioc (0 : ℝ) d).indicator (fun r => Real.exp (-μ * r))
  have hf : Integrable f := by
    rw [show f = (Set.Ioi (0 : ℝ)).indicator (fun r => Real.exp (-μ * r) *
      ocPulse α q Λ ζ m k (t - r)) by rfl, integrable_indicator_iff measurableSet_Ioi]
    exact pulseMemory_integrableOn hΛ hζ hν k t
  have hle : ∫ r, g r ≤ ∫ r, f r := by
    apply integral_mono_of_nonneg
    · filter_upwards [] with r
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) r
    · exact hf
    · filter_upwards [] with r
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) d
      · have hp : ocPulse α q Λ ζ m k (t - r) = 1 := by
          apply pulse_eq_one_on_completeCore hΛ hζ l k hcore
          constructor
          · dsimp [d] at hr
            linarith [ht.1, hr.2]
          · linarith [ht.2, hr.1]
        simp only [g, f, Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ Set.Ioi (0 : ℝ) from hr.1), hp, mul_one]
        exact le_rfl
      · rw [show g r = 0 from Set.indicator_of_notMem hr _]
        exact Set.indicator_nonneg (fun s _ =>
          mul_nonneg (Real.exp_pos _).le (ocPulse_range hζ k (t - s)).1) r
  have hmem : (∫ r, f r) = ocPulseMemory α q Λ ζ m ν k t := by
    dsimp [f]
    rw [integral_indicator measurableSet_Ioi]
    rfl
  have hint : (∫ r, g r) = (1 - Real.exp (-μ * d)) / μ := by
    dsimp [g]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hd.le,
      intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr (ne_of_gt hμ)),
      integral_exp]
    simp
    field_simp
    ring
  have hnorm : 1 - Real.exp (-μ * d) ≤ μ * ocPulseMemory α q Λ ζ m ν k t := by
    rw [hmem, hint] at hle
    have hh := mul_le_mul_of_nonneg_left hle hμ.le
    calc
      _ = μ * ((1 - Real.exp (-μ * d)) / μ) := by field_simp
      _ ≤ _ := hh
  have hexp : Real.exp (-μ * d) ≤ Real.exp (-2) := by
    apply Real.exp_le_exp.mpr
    change 6 ≤ μ * ocTau α q Λ m at hrelax
    dsimp [d]
    linarith
  exact (sub_le_sub_left hexp 1).trans hnorm

end AVRegularity.CycleReference
end

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleReference

/-! A fixed finite sum represents the glued corrector on a neighborhood in time. -/

theorem cutoff_nonzero_distance {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (k : ℤ) (t : ℝ) (hk : ocCutoff α q Λ m k t ≠ 0) :
    |t - (k : ℝ) * ocTau α q Λ m| < 5 / 4 * ocTau α q Λ m := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have ha : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    by_contra h
    exact hk (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  have hr : 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 5 / 2 := by linarith
  have hh := (div_lt_iff₀ hτ).mp hr
  linarith

theorem cutoff_locally_finite {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (t : ℝ) :
    ∃ S : Finset {k : ℤ // Odd k}, ∀ᶠ s in 𝓝 t,
      ∀ k : {k : ℤ // Odd k}, k ∉ S → ocCutoff α q Λ m k.1 s = 0 := by
  classical
  let τ := ocTau α q Λ m
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  let I : Set ℤ := Set.Icc ⌊t / τ - 2⌋ ⌈t / τ + 2⌉
  have hI : I.Finite := Set.finite_Icc _ _
  have hS : ((fun k : {k : ℤ // Odd k} => k.1) ⁻¹' I).Finite :=
    hI.preimage (by intro a ha b hb h; exact Subtype.ext h)
  refine ⟨hS.toFinset, ?_⟩
  filter_upwards [Metric.ball_mem_nhds t (show 0 < τ / 4 by positivity)] with s hs
  intro k hk
  by_contra hne
  have hd := cutoff_nonzero_distance hΛ k.1 s hne
  have hs' : |s - t| < τ / 4 := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
  have htri := abs_sub_le t s ((k.1 : ℝ) * τ)
  rw [abs_sub_comm t s] at htri
  have hdist : |t - (k.1 : ℝ) * τ| < 3 / 2 * τ := by
    change |s - (k.1 : ℝ) * τ| < 5 / 4 * τ at hd
    linarith
  have hlo : t / τ - 2 ≤ (k.1 : ℝ) := by
    have hh := (abs_lt.mp hdist).2
    rw [sub_le_iff_le_add, div_le_iff₀ hτ]
    nlinarith
  have hhi : (k.1 : ℝ) ≤ t / τ + 2 := by
    have hh := (abs_lt.mp hdist).1
    rw [← sub_le_iff_le_add, le_div_iff₀ hτ]
    nlinarith
  have hmem : k.1 ∈ I := by
    exact ⟨Int.cast_le.mp ((Int.floor_le _).trans hlo),
      Int.cast_le.mp (hhi.trans (Int.le_ceil _))⟩
  exact hk (hS.mem_toFinset.mpr hmem)

theorem refCorrector_locally_finite {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) :
    ∃ S : Finset {k : ℤ // Odd k}, ∀ᶠ s in 𝓝 t,
      ocRefCorrector α q Λ ζ m ν s = fun y =>
        ∑ k ∈ S, ocCutoff α q Λ m k.1 s • ocPulseCorrector α q Λ ζ m ν k.1 s y := by
  classical
  obtain ⟨S, hS⟩ := cutoff_locally_finite hΛ t
  refine ⟨S, ?_⟩
  filter_upwards [hS] with s hs
  funext y
  unfold ocRefCorrector
  apply tsum_eq_sum
  intro k hk
  rw [hs k hk, zero_smul]

end AVRegularity.CycleReference
end

section
open MeasureTheory
open scoped NNReal
namespace AVRegularity.CycleReference

/-! Integration by parts for causal memory, adapted from upstream FluxEnergyCutoff. -/

theorem expKernel_integral_Iic {ρ t : ℝ} (hρ : 0 < ρ) :
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) = ρ⁻¹ := by
  have hcancel : Real.exp (-ρ * t) * Real.exp (ρ * t) = 1 := by
    rw [← Real.exp_add]
    have hsum : -ρ * t + ρ * t = 0 := by ring
    rw [hsum, Real.exp_zero]
  calc
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) =
        Real.exp (-ρ * t) * (∫ s in Set.Iic t, Real.exp (ρ * s)) := by
          rw [show (fun s : ℝ => Real.exp (ρ * (s - t))) =
            fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) by
              funext s
              rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring,
                Real.exp_add]
              ring]
          rw [integral_const_mul]
    _ = Real.exp (-ρ * t) * (Real.exp (ρ * t) / ρ) := by
          rw [integral_exp_mul_Iic hρ t]
    _ = ρ⁻¹ := by
          rw [div_eq_mul_inv, ← mul_assoc, hcancel]
          simp

theorem compact_forcing_error_integral (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfcompact : HasCompactSupport f) (ρ t : ℝ) :
    f t - ρ * (∫ s in Set.Iic t, f s * Real.exp (ρ * (s - t))) =
      ∫ s in Set.Iic t, deriv f s * Real.exp (ρ * (s - t)) := by
  let e : ℝ → ℝ := fun s => Real.exp (ρ * (s - t))
  let g : ℝ → ℝ := f * e
  have he : ContDiff ℝ (⊤ : ℕ∞) e := by
    dsimp [e]
    fun_prop
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.mul he
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.mul_right (f := f) (f' := e) hfcompact
  have hfone : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfoneDeriv : Continuous (deriv f) := hfone.continuous_deriv (by norm_num)
  have hfderivCompact : HasCompactSupport (deriv f) := hfcompact.deriv
  have hpcont : Continuous (fun s => deriv f s * e s) := hfoneDeriv.mul he.continuous
  have hpcompact : HasCompactSupport (fun s => deriv f s * e s) :=
    HasCompactSupport.mul_right (f := deriv f) (f' := e) hfderivCompact
  have hqcont : Continuous (fun s => ρ * (f s * e s)) :=
    continuous_const.mul (hf.continuous.mul he.continuous)
  have hqcompact : HasCompactSupport (fun s => ρ * (f s * e s)) := by
    have hqfun : (fun s => ρ * (f s * e s)) = (fun _ : ℝ => ρ) * (f * e) := by
      funext s
      rfl
    rw [hqfun]
    exact HasCompactSupport.mul_left hgcompact
  have hpint : IntegrableOn (fun s => deriv f s * e s) (Set.Iic t) :=
    (hpcont.integrable_of_hasCompactSupport hpcompact).integrableOn
  have hqint : IntegrableOn (fun s => ρ * (f s * e s)) (Set.Iic t) :=
    (hqcont.integrable_of_hasCompactSupport hqcompact).integrableOn
  have hderivEq : deriv g = fun s => deriv f s * e s + ρ * (f s * e s) := by
    funext s
    have hfdiff : DifferentiableAt ℝ f s :=
      (ContDiff.contDiffAt (x := s) hf).differentiableAt (by norm_num)
    have hediff : DifferentiableAt ℝ e s :=
      (ContDiff.contDiffAt (x := s) he).differentiableAt (by norm_num)
    have hmul := deriv_mul hfdiff hediff
    have hederiv : deriv e s = ρ * e s := by
      have harg : HasDerivAt (fun x : ℝ => ρ * (x - t)) ρ s := by
        simpa using (hasDerivAt_id s).sub_const t |>.const_mul ρ
      have h := harg.exp.deriv
      change deriv (fun x : ℝ => Real.exp (ρ * (x - t))) s = _
      rw [h]
      ring
    change deriv (f * e) s = _
    rw [hmul, hederiv]
    ring
  have hfund := hgcompact.integral_Iic_deriv_eq (hg.of_le (by norm_num)) t
  rw [hderivEq, integral_add hpint hqint, integral_const_mul] at hfund
  have hgval : g t = f t := by simp [g, e]
  rw [hgval] at hfund
  dsimp [g, e] at hfund
  linarith only [hfund]

theorem compact_forcing_error_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfcompact : HasCompactSupport f)
    (ρ D t : ℝ) (hρ : 0 < ρ) (hd : ∀ s, |deriv f s| ≤ D) :
    |f t - ρ * (∫ s in Set.Iic t, f s * Real.exp (ρ * (s - t)))| ≤ D / ρ := by
  rw [compact_forcing_error_integral f hf hfcompact]
  have hk : IntegrableOn (fun s : ℝ => Real.exp (ρ * (s - t))) (Set.Iic t) := by
    have heq : (fun s : ℝ => Real.exp (ρ * (s - t))) =
        fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
      funext s
      rw [show ρ * (s - t) = -ρ * t + ρ * s by ring, Real.exp_add]
    rw [heq]
    exact (integrableOn_exp_mul_Iic hρ t).const_mul _
  have hmajor := norm_integral_le_of_norm_le (hk.const_mul D)
    (Filter.Eventually.of_forall (fun s : ℝ => show
      ‖deriv f s * Real.exp (ρ * (s - t))‖ ≤ D * Real.exp (ρ * (s - t)) from by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hd s) (Real.exp_pos _).le))
  rw [Real.norm_eq_abs, integral_const_mul, expKernel_integral_Iic hρ] at hmajor
  simpa only [div_eq_mul_inv] using hmajor

theorem ocPulse_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (ocPulse α q Λ ζ m k) := by
  unfold ocPulse slowEnvelope
  exact ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
      (hζ.1.comp (by fun_prop))

theorem ocPulseMemory_eq_weighted_Iic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (k : ℤ) (t : ℝ) :
    ocPulseMemory α q Λ ζ m ν k t =
      ∫ s in Set.Iic t, ocPulse α q Λ ζ m k s * Real.exp (ocMu q Λ m ν * (s - t)) := by
  rw [ocPulseMemory_eq_exp_mul_Iic]
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [show ocMu q Λ m ν * (s - t) = -(ocMu q Λ m ν) * t + ocMu q Λ m ν * s by ring,
    Real.exp_add]
  ring

theorem pulse_memory_instantaneous_error {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν → ∀ k : ℤ, ∀ t : ℝ,
      |ocPulse α q Λ ζ m k t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t| ≤
        K / (ocMu q Λ m ν * ocTau α q Λ m) := by
  obtain ⟨K, hK, hLip⟩ := ocPulse_uniform_lipschitz hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν k t
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hd : ∀ s, |deriv (ocPulse α q Λ ζ m k) s| ≤ K / ocTau α q Λ m := by
    have hl := LipschitzWith.of_dist_le' (fun x y : ℝ => show
      dist (ocPulse α q Λ ζ m k x) (ocPulse α q Λ ζ m k y) ≤
        (K / ocTau α q Λ m) * dist x y from by
          simpa only [Real.dist_eq] using hLip α q Λ m hΛ k x y)
    intro s
    simpa only [Real.norm_eq_abs, Real.coe_toNNReal _ (div_nonneg hK hτ.le)] using
      norm_deriv_le_of_lipschitz (x₀ := s) hl
  rw [ocPulseMemory_eq_weighted_Iic]
  have hb := compact_forcing_error_bound _ (ocPulse_contDiff hζ k)
    (ocPulse_hasCompactSupport hΛ hζ k) (ocMu q Λ m ν) (K / ocTau α q Λ m) t
    (ocMu_pos hΛ hν) hd
  convert hb using 1
  ring

end AVRegularity.CycleReference
end

section
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The material metric exactly cancels the pulled gradient Jacobian. -/

theorem metric_pullback_energy (F : Matrix (Fin 2) (Fin 2) ℝ) (hF : IsUnit F.det)
    (v : Vec 2) :
    vecDot (Fᵀ.mulVec v) ((F⁻¹ * (F⁻¹)ᵀ).mulVec (Fᵀ.mulVec v)) = vecDot v v := by
  change dotProduct (Fᵀ.mulVec v) _ = dotProduct v v
  have hT : (F⁻¹)ᵀ * Fᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hF, Matrix.transpose_one]
  have hi : (F⁻¹)ᵀ.mulVec (Fᵀ.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hi]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hF, Matrix.one_mulVec, dotProduct_comm]

theorem chart_gradient_energy (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) (l : ℤ) (t : ℝ) (Du : Vec 2 → Vec 2) :
    ∫ y, vecDot
      ((jacMatrix (ocChart α q Λ m φ hφ l t) y)ᵀ.mulVec
        (Du (ocChart α q Λ m φ hφ l t y)))
      ((ocMaterialMetric α q Λ m φ hφ l t y).mulVec
        ((jacMatrix (ocChart α q Λ m φ hφ l t) y)ᵀ.mulVec
          (Du (ocChart α q Λ m φ hφ l t y)))) =
      ∫ x, vecDot (Du x) (Du x) := by
  have he (y : Vec 2) := metric_pullback_energy
    (jacMatrix (ocChart α q Λ m φ hφ l t) y)
    (by change IsUnit (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x _) y).det
        rw [streamFlow_jacMatrix_det_one hφ]; exact isUnit_one)
    (Du (ocChart α q Λ m φ hφ l t y))
  simp_rw [ocMaterialMetric, he]
  exact chart_integral α q Λ m hφ l t (fun x => vecDot (Du x) (Du x))

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Space-time measure preservation for a fixed-start chart. -/

theorem streamFlow_joint_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 × ℝ => AVRegularity.streamFlow φ hφ p.1 p.2.1 p.2.2) := by
  exact Infra.Flow.flow_joint_contDiff_infty
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ)
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz)

noncomputable def streamFlowTimeHomeomorph {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) : (ℝ × Vec 2) ≃ₜ (ℝ × Vec 2) where
  toFun := fun p => (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)
  invFun := fun p => (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)
  left_inv := by
    intro p
    exact Prod.ext rfl ((streamFlowHomeomorph hφ p.1 s).left_inv p.2)
  right_inv := by
    intro p
    exact Prod.ext rfl ((streamFlowHomeomorph hφ p.1 s).right_inv p.2)
  continuous_toFun := continuous_fst.prodMk
    ((streamFlow_joint_smooth hφ).continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))
  continuous_invFun := continuous_fst.prodMk
    ((streamFlow_joint_smooth hφ).continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk continuous_fst)))

theorem streamFlowTime_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    MeasurePreserving (streamFlowTimeHomeomorph hφ s) volume volume := by
  have hg : Measurable (Function.uncurry (fun t x => AVRegularity.streamFlow φ hφ t x s)) := by
    exact ((streamFlow_joint_smooth hφ).continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk (continuous_const (y := s))))).measurable
  have ht := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t x => AVRegularity.streamFlow φ hφ t x s) hg
    (Filter.Eventually.of_forall (fun t => (streamFlow_measurePreserving hφ t s).map_eq))
  exact ht

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Quadratic-form gain on a terminal half-core and the molecular lower bound everywhere. -/

theorem shearFlux_qform (ν c : ℝ) (k : {k : ℤ // Odd k}) (v : Vec 2) :
    vecDot v ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + c • ocPi k).mulVec v) =
      ν * vecDot v v + c * (if k.1 % 4 = 1 then v 1 ^ 2 else v 0 ^ 2) := by
  by_cases hk : k.1 % 4 = 1
  · simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ocPi, hk,
      Matrix.one_apply]
    ring
  · simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ocPi, hk,
      Matrix.one_apply]
    ring

theorem refFlux_qform_molecular_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (t : ℝ) (v : Vec 2) :
    ν * vecDot v v ≤ vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v) := by
  rcases refFlux_shape hΛ hζ (t := t) hν with ⟨k, c, hflux, hc, _⟩ | hflux
  · rw [hflux, shearFlux_qform]
    have hsq : 0 ≤ (if k.1 % 4 = 1 then v 1 ^ 2 else v 0 ^ 2) := by
      split_ifs <;> exact sq_nonneg _
    exact le_add_of_nonneg_right (mul_nonneg hc hsq)
  · rw [hflux]
    simp [vecDot]
    ring_nf
    exact le_rfl

theorem refFlux_core_qform_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (l k : ℤ) (hcore : IsOCCompleteCore α q Λ m l k)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) * ocTau α q Λ m)
      (((k : ℝ) + 1 / 3) * ocTau α q Λ m)) (v : Vec 2) :
    ν * vecDot v v + ocHStar α q Λ m ν * (1 - Real.exp (-2)) *
      (if k % 4 = 1 then v 1 ^ 2 else v 0 ^ 2) ≤
        vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v) := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hp : ocPulse α q Λ ζ m k t = 1 := by
    apply pulse_eq_one_on_completeCore hΛ hζ l k hcore
    exact ⟨by linarith [ht.1], ht.2⟩
  have hpne : ocPulse α q Λ ζ m k t ≠ 0 := by rw [hp]; norm_num
  have hflux : ocRefFlux α q Λ ζ m ν t =
      ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulseMemory α q Λ ζ m ν k t) •
          ocPi ⟨k, hcore.1⟩ := by
    unfold ocRefFlux
    rw [pulseMatrixSum_eq_at_active hΛ hζ ν t ⟨k, hcore.1⟩ hpne, hp, one_mul, smul_smul]
  rw [hflux, shearFlux_qform]
  have hM := pulseMemory_core_lower hΛ hζ hν l k hcore hrelax t ht
  have hH := ocHStar_pos (α := α) (q := q) (m := m) hΛ hν
  have hsq : 0 ≤ (if k % 4 = 1 then v 1 ^ 2 else v 0 ^ 2) := by
    split_ifs <;> exact sq_nonneg _
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hsq
  calc
    _ ≤ ocHStar α q Λ m ν * (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t) :=
      mul_le_mul_of_nonneg_left hM hH.le
    _ = _ := by ring

end AVRegularity.CycleReference
end
end
