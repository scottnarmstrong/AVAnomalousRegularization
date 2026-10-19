-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Velocity.Port.Section2FlowInverseBounds
public import AVRegularity.Velocity.Port.Section2FlowRegularityCore
public import AVRegularity.Velocity.Port.Section2JointInduction
public import AVenhance.Infra.Section4.Amnr.TransportProfileJets
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Cutoff.DerivativeBounds
import AVenhance.Infra.Flow.InverseC1
import AVenhance.Infra.Section4.Amnr.Cutoff
import AVenhance.Infra.Section4.Amnr.SpatialCommutator
import AVenhance.Infra.Section4.Amnr.StreamMaterial
import AVenhance.Infra.Section4.Amnr.StreamMaterialRates
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
open AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.RecursionIncrement
open AVRegularity.Velocity.Port.Section2FlowIdentities
namespace AVRegularity.Velocity.Port.MaterialAuxiliaryWords

/-! Source increment bounds with independent spatial and material cutoffs.
Spatial stream regularity and inverse-flow bounds hold at every order; only
cutoff-time orders use the literal `Nstar`. -/

theorem material_aux_amnrSpaceWord_abs_le_iteratedFDeriv
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 2)) (x : Vec 2) :
    |amnrSpaceWord α f x| ≤ ‖iteratedFDeriv ℝ α.length f x‖ := by
  rw [amnrSpaceWord_eq_iteratedFDeriv hf α]
  have hp : ∏ j : Fin α.length, ‖amnrSpatialDirections α j‖ = 1 := by
    rw [amnrSpatialDirections_eq]
    have hb (p : Fin 2) : ‖basisVec p‖ = 1 := by
      fin_cases p <;> simp [basisVec, Pi.norm_single]
    simp only [hb, Finset.prod_const_one]
  have hd := (iteratedFDeriv ℝ α.length f x).le_opNorm (amnrSpatialDirections α)
  rw [hp, mul_one, Real.norm_eq_abs] at hd
  exact hd

/-- The slow and fast cutoff factors satisfy the uniform
derivative rate with the fixed input constants recorded in `JetRecursionData`. -/
theorem streamRecursionCutoff_derivative_abs_le
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (hm : 1 ≤ m) (k : ℤ)
    {j : ℕ} (hj : j ≤ AVenhance.Nstar (1 + α)) (t : ℝ) :
    |iteratedDeriv j (streamRecursionCutoff D m k) t| ≤
      (2 : ℝ) ^ j * D.Chat * D.Czeta * (D.tau m)⁻¹ ^ j := by
  let l := ocLabel α q Λ m k
  have hτ : 0 < D.tau m := D.tau_pos m hm
  have hτP : 0 < D.tauP m := D.tauP_pos m hm
  have hChat : 0 ≤ D.Chat := le_trans (by norm_num) D.one_le_Chat
  have hCzeta : 0 ≤ D.Czeta := le_trans (by norm_num) D.one_le_Czeta
  have hscale : D.tau m ≤ D.tauP m := by
    have facts := AVRegularity.Scales.admissible_time_scale_facts
      D.hαpos D.hαlt D.hspos D.hslt D.hq D.hΛ hm
    have hratio : D.tauP m / D.tau m = (ocL α q Λ m : ℝ) := by
      simpa [D.tauP_eq_oc, D.tau_eq_oc] using facts.2.2.2.2.2.2.2.2
    have hL : 1 ≤ (ocL α q Λ m : ℝ) := by
      exact_mod_cast (show 1 ≤ ocL α q Λ m by omega)
    have hratio' : 1 ≤ D.tauP m / D.tau m := by rw [hratio]; exact hL
    simpa using (le_div_iff₀ hτ).mp hratio'
  have hslow : ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.slowEnvelope α q Λ m l) := by
    unfold AVRegularity.slowEnvelope
    fun_prop
  have hslowBound : ∀ i : ℕ, i ≤ AVenhance.Nstar (1 + α) → ∀ r : ℝ,
      |iteratedDeriv i (AVRegularity.slowEnvelope α q Λ m l) r| ≤
        D.Chat * (D.tau m)⁻¹ ^ i := by
    intro i hi r
    have hraw := D.slowEnvelope_derivative_bound m hm l i hi r
    have hdiv : |iteratedDeriv i (AVRegularity.slowEnvelope α q Λ m l) r| ≤
        D.Chat / D.tauP m ^ i :=
      (le_div_iff₀ (pow_pos hτP i)).2 (by simpa [mul_comm] using hraw)
    calc
      _ ≤ D.Chat * (D.tauP m)⁻¹ ^ i := by
        simpa [div_eq_mul_inv, inv_pow] using hdiv
      _ ≤ D.Chat * (D.tau m)⁻¹ ^ i :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.mpr hτP.le)
            (inv_anti₀ hτ hscale) i) hChat
  have hfast : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m)) :=
    D.hζ.1.comp (by fun_prop)
  have hfastBound : ∀ i : ℕ, i ≤ AVenhance.Nstar (1 + α) → ∀ r : ℝ,
      |iteratedDeriv i
        (fun t : ℝ => ζ ((t - (k : ℝ) * D.tau m) / D.tau m)) r| ≤
        D.Czeta * (D.tau m)⁻¹ ^ i := by
    intro i hi r
    have hscaled := AVenhance.Infra.Cutoff.scaled_translate_iteratedDeriv_bound
      (shift := (k : ℝ)) (x := r) (j := i)
      D.hζ.1 D.fast_profile_derivative_bound hτ hi
    have hfun : (fun t : ℝ => ζ ((t - (k : ℝ) * D.tau m) / D.tau m)) =
        fun t => ζ (t / D.tau m - (k : ℝ)) := by
      funext r'
      congr 1
      field_simp [hτ.ne']
    rw [← hfun] at hscaled
    have hdiv : |iteratedDeriv i
        (fun t : ℝ => ζ ((t - (k : ℝ) * D.tau m) / D.tau m)) r| ≤
        D.Czeta / D.tau m ^ i :=
      (le_div_iff₀ (pow_pos hτ i)).2 (by simpa [mul_comm] using hscaled)
    simpa [div_eq_mul_inv, inv_pow] using hdiv
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (streamRecursionCutoff D m k) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (AVRegularity.slowEnvelope α q Λ m l *
        (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m)))
    exact hslow.mul hfast
  have hslowN : ContDiff ℝ (AVenhance.Nstar (1 + α))
      (AVRegularity.slowEnvelope α q Λ m l) := hslow.of_le (by simp)
  have hfastN : ContDiff ℝ (AVenhance.Nstar (1 + α))
      (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m)) := hfast.of_le (by simp)
  have hrate := amnr_iteratedDeriv_product_abs_le hslowN hfastN
    (by exact_mod_cast hj) hChat hCzeta (inv_nonneg.mpr hτ.le)
    hslowBound hfastBound t
  change |iteratedDeriv j
      (AVRegularity.slowEnvelope α q Λ m l *
        (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m))) t| ≤
    (2 : ℝ) ^ j * D.Chat * D.Czeta * (D.tau m)⁻¹ ^ j
  exact hrate

/-- Material derivatives hit the two-cutoff factor, while spatial
derivatives hit only the transported shear profile. This is the OC form of
the mixed-word identity of the `AVenhance` library. -/
theorem material_aux_nextStreamTerm_mixed_word
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) {m : ℕ} (hm : 1 ≤ m)
    (k : ℤ) (word : List (Fin 2)) (ell : ℕ) (z : AmnrSpace) :
    amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
      (word.map some ++ List.replicate ell none)
      (fun y => streamRecursionCutoff D m k y.1 *
        ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) y.1 y.2
            ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) z =
      iteratedDeriv ell (streamRecursionCutoff D m k) z.1 *
        amnrSpaceWord word
          (fun x => ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) z.1 x
              ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) z.2 := by
  obtain ⟨hφ, _⟩ := hseq.2 m hm
  have hφeq : hφ = AVRegularity.Velocity.streamSeq_admissible
      D.hζ D.hΛ hseq (m - 1) := Subsingleton.elim _ _
  have hτ : 0 < D.tau m := D.tau_pos m hm
  have hc : ContDiff ℝ (⊤ : ℕ∞) (streamRecursionCutoff D m k) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (slowEnvelope α q Λ m (ocLabel α q Λ m k) *
        (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m)))
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (slowEnvelope α q Λ m (ocLabel α q Λ m k)) := by
      unfold slowEnvelope
      fun_prop
    exact hs.mul (D.hζ.1.comp (by fun_prop))
  have hflow :=
    AVRegularity.Velocity.Port.Section2FlowRegularityCore.constructionFlowInv_joint_smooth
      D hseq (m - 1)
  let sk := (ocLabel α q Λ m k : ℝ) * D.tauPP m
  let T : AmnrSpace → ℝ := fun y => streamRecursionCutoff D m k y.1 *
    ocShear α q Λ m k (constructionFlowInv D hseq (m - 1) y.1 y.2 sk)
  have hX : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : AmnrSpace => constructionFlowInv D hseq (m - 1) y.1 y.2 sk) := by
    exact hflow.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : AmnrSpace => (y.1, y.2, sk)))
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by
    dsimp [T]
    exact (hc.comp contDiff_fst).mul
      ((AVRegularity.Velocity.Port.RecursionIncrement.ocShear_contDiff D m k).comp hX)
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1))
  have hinner : ContDiff ℝ (⊤ : ℕ∞)
      (amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
        (List.replicate ell none) T) :=
    contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.smooth.contDiffOn
      hT.contDiffOn (List.replicate ell none))
  have hTflow : T = fun y => streamRecursionCutoff D m k y.1 *
      ocShear α q Λ m k
        (flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous hφ.vel_lipschitz
          y.1 y.2 sk) := by
    funext y
    dsimp [T, Section2FlowIdentities.constructionFlowInv,
      Section2FlowIdentities.streamFlowInv, Section2FlowIdentities.streamFlow]
  rw [amnrWord_append, amnrWord_spatial_slice hinner]
  rw [hTflow, amnr_inverse_flow_material_word hφ
    ((AVRegularity.Velocity.Port.RecursionIncrement.ocShear_contDiff D m k).of_le (by simp))
    (hc.of_le (show (ell : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)) sk ell le_rfl]
  change amnrSpaceWord word
      ((iteratedDeriv ell (streamRecursionCutoff D m k) z.1) •
        (fun x => ocShear α q Λ m k
          (flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous hφ.vel_lipschitz
            z.1 x sk))) z.2 = _
  rw [amnrSpaceWord_const_smul]
  have hprofileEq : (fun x : Vec 2 => ocShear α q Λ m k
      (flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous hφ.vel_lipschitz
        z.1 x sk)) =
      (fun x => ocShear α q Λ m k
        (constructionFlowInv D hseq (m - 1) z.1 x sk)) := by
    funext x
    dsimp [Section2FlowIdentities.constructionFlowInv,
      Section2FlowIdentities.streamFlowInv, Section2FlowIdentities.streamFlow]
  rw [hprofileEq]
  rfl

/-- A transported recursion summand has arbitrary auxiliary spatial order,
while its time-cutoff derivative stays within the source `Nstar` budget. -/
theorem material_aux_nextStreamTerm_mixed_abs_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {C : ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (word : List (Fin 2)) (ell : ℕ)
    {Nspace : ℕ} (hword : word.length ≤ Nspace)
    (hell : ell ≤ AVenhance.Nstar (1 + α)) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
      (word.map some ++ List.replicate ell none)
      (fun y => streamRecursionCutoff D m k y.1 *
        ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) y.1 y.2
            ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) z| ≤
      ((2 : ℝ) ^ ell * D.Chat * D.Czeta) *
        (amnrTransportSpatialConstant Nspace * D.velocityAmplitude m *
          D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length) *
        (D.tau m)⁻¹ ^ ell := by
  by_cases ht : |z.1 - (ocLabel α q Λ m k : ℝ) * D.tauPP m| ≤
      D.tauPP m / 2 + D.tauP m
  · rw [material_aux_nextStreamTerm_mixed_word D hseq hm k word ell z, abs_mul]
    have hb :=
      AVRegularity.Velocity.Port.MaterialAuxiliaryProfile.material_aux_transportProfile_iteratedFDeriv_norm_le_of_A3
        D hseq hreg hm k (ocLabel α q Λ m k) z.1 z.2 ht
        (N := Nspace) word.length hword
    have hXsp : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => constructionFlowInv D hseq (m - 1) z.1 x
          ((ocLabel α q Λ m k : ℝ) * D.tauPP m)) := by
      exact (AVRegularity.Velocity.Port.Section2FlowRegularityCore.constructionFlowInv_joint_smooth
        D hseq (m - 1)).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec 2 => (z.1, y, (ocLabel α q Λ m k : ℝ) * D.tauPP m)))
    have hprofile : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) z.1 x
            ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) :=
      (AVRegularity.Velocity.Port.RecursionIncrement.ocShear_contDiff D m k).comp hXsp
    have hsp := material_aux_amnrSpaceWord_abs_le_iteratedFDeriv hprofile word z.2
    have hbword := hsp.trans hb
    have hc := streamRecursionCutoff_derivative_abs_le D m hm k hell z.1
    have hnonneg := (abs_nonneg _).trans hc
    have hh := mul_le_mul hc hbword (abs_nonneg _) hnonneg
    convert hh using 1
    ring
  · have hV : IsOpen {y : AmnrSpace |
        D.tauPP m / 2 + D.tauP m <
          |y.1 - (ocLabel α q Λ m k : ℝ) * D.tauPP m|} :=
      isOpen_lt continuous_const (by fun_prop)
    have hz : z ∈ {y : AmnrSpace |
        D.tauPP m / 2 + D.tauP m <
          |y.1 - (ocLabel α q Λ m k : ℝ) * D.tauPP m|} := by
      exact lt_of_not_ge ht
    have hzero : Set.EqOn (fun y : AmnrSpace => streamRecursionCutoff D m k y.1 *
        ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) y.1 y.2
            ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) 0
        {y : AmnrSpace | D.tauPP m / 2 + D.tauP m <
          |y.1 - (ocLabel α q Λ m k : ℝ) * D.tauPP m|} := by
      intro y hy
      have hcut : streamRecursionCutoff D m k y.1 = 0 := by
        by_contra hne
        have hslow : slowEnvelope α q Λ m (ocLabel α q Λ m k) y.1 ≠ 0 := by
          intro hzero
          apply hne
          simp [streamRecursionCutoff, hzero]
        have hd := AVRegularity.Velocity.Port.RecursionIncrement.slowEnvelope_nonzero_distance
          D m hm (ocLabel α q Λ m k) y.1 hslow
        have hfar := hy
        change D.tauPP m / 2 + D.tauP m <
          |y.1 - (ocLabel α q Λ m k : ℝ) * D.tauPP m| at hfar
        rw [← D.tauPP_eq_oc m] at hd
        have hp := D.tauP_pos m hm
        linarith
      simp [hcut]
    have hzeroWord := amnrWord_congr hV
      (b := fun y => streamVel (Φ (m - 1)) y.1 y.2) hzero
      (word.map some ++ List.replicate ell none) hz
    rw [hzeroWord]
    simp only [amnrWord_zero, Pi.zero_apply, abs_zero]
    have hK := amnrTransportSpatialConstant_pos Nspace
    have hA : 0 < D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
    have hE := D.epsilon_pos m
    have hτ := D.tau_pos m hm
    have hChat : 0 < D.Chat := lt_of_lt_of_le zero_lt_one D.one_le_Chat
    have hCzeta : 0 < D.Czeta := lt_of_lt_of_le zero_lt_one D.one_le_Czeta
    positivity

/-- The admissible OC time scale has the source fine-time rate in the
current velocity amplitude. -/
theorem inverse_tau_le_current_velocityAmplitude
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {m : ℕ} (hm : 1 ≤ m) :
    (D.tau m)⁻¹ ≤ (2 : ℝ) ^ 34 * D.velocityAmplitude m := by
  let E := D.epsilon (m - 1)
  let e := D.epsilon m
  let p := 1 - α
  let δ := ocDelta α q
  let κ := 2 - (1 + α) + 2 * δ
  have hEpos : 0 < E := D.epsilon_pos (m - 1)
  have hEle : E ≤ 1 := D.epsilon_le_one (m - 1)
  have hepos : 0 < e := D.epsilon_pos m
  have hp : 0 < p := by dsimp [p]; linarith [D.hαlt]
  have hpone : p ≤ 1 := by dsimp [p]; linarith [D.hαpos]
  have htime := AVRegularity.Scales.admissible_time_scale_facts
    D.hαpos D.hαlt D.hspos D.hslt D.hq D.hΛ hm
  rcases htime with ⟨hLmin, hLlower, hLupper, hPPlo, _, _, _, _, _⟩
  have hspace := AVRegularity.Scales.admissible_space_scale_facts D.hq D.hΛ hm
  have heupper : e ≤ 2 * E ^ q := by
    simpa [e, E, D.epsilon_eq_oc] using hspace.2.2.2
  have hLpos : 0 < (ocL α q Λ m : ℝ) := by
    exact_mod_cast (show 0 < ocL α q Λ m by omega)
  have hLupper' : (ocL α q Λ m : ℝ) ≤ 9 * E ^ (-δ) := by
    simpa [E, δ, D.epsilon_eq_oc] using hLupper
  have hLsq : (ocL α q Λ m : ℝ) ^ 2 ≤ (9 * E ^ (-δ)) ^ 2 := by
    have hLnonneg : 0 ≤ (ocL α q Λ m : ℝ) := hLpos.le
    have hUnonneg : 0 ≤ 9 * E ^ (-δ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hLupper')
      (add_nonneg hLnonneg hUnonneg)]
  have hPPlo' : (2 : ℝ) ^ (-26 : ℤ) * E ^ κ ≤ D.tauPP m := by
    simpa [E, δ, κ, D.tauPP_eq_oc, D.epsilon_eq_oc] using hPPlo
  have hPPpos : 0 < D.tauPP m := D.tauPP_pos m hm
  have hUpos : 0 < 9 * E ^ (-δ) := by positivity
  have hcross : ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) *
        (ocL α q Λ m : ℝ) ^ 2 ≤
      D.tauPP m * (9 * E ^ (-δ)) ^ 2 := by
    calc
      _ ≤ D.tauPP m * (ocL α q Λ m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hPPlo' (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hLsq hPPpos.le
  have hquot : ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) /
        (9 * E ^ (-δ)) ^ 2 ≤
      D.tauPP m / (ocL α q Λ m : ℝ) ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos hUpos) (sq_pos_of_pos hLpos)).2 hcross
  have hκ : κ = p + 2 * δ := by dsimp [κ, p]; ring
  have hpowδ : (E ^ (-δ)) ^ (2 : ℕ) = E ^ (-2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hEpos.le]
    congr 1
    ring
  have hquotEq : ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) /
      (9 * E ^ (-δ)) ^ 2 =
      ((2 : ℝ) ^ (-26 : ℤ) / 81) * E ^ (p + 4 * δ) := by
    rw [hκ, mul_pow, hpowδ, show (9 : ℝ) ^ 2 = 81 by norm_num]
    have hfactor : ((2 : ℝ) ^ (-26 : ℤ) * E ^ (p + 2 * δ)) /
        (81 * E ^ (-2 * δ)) =
      ((2 : ℝ) ^ (-26 : ℤ) / 81) *
        (E ^ (p + 2 * δ) / E ^ (-2 * δ)) := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hEpos _)]
    rw [hfactor, ← Real.rpow_sub hEpos]
    congr 2
    ring
  have hTauLower : ((2 : ℝ) ^ (-26 : ℤ) / 81) *
      E ^ (p + 4 * δ) ≤ D.tau m := by
    rw [D.tau_eq_oc m, AVRegularity.ocTau, ← D.tauPP_eq_oc m]
    calc
      _ = ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) /
          (9 * E ^ (-δ)) ^ 2 := hquotEq.symm
      _ ≤ _ := hquot
  have hqpos : 1 < q := D.hq.1
  have hden : 0 < 2 * q + 2 := by linarith
  have hratio : α ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [D.hαlt, hqpos]
  have hfactor : 1 - (2 * q + 1) * (1 + α) / (2 * q + 2) ≤ 1 - α := by
    linarith
  have hδbound : 4 * δ ≤ (q - 1) * (1 - α) := by
    have hqnonneg : 0 ≤ q - 1 := by linarith
    calc
      4 * δ = (q - 1) *
          (1 - (2 * q + 1) * (1 + α) / (2 * q + 2)) := by
        dsimp [δ, ocDelta]
        ring
      _ ≤ (q - 1) * (1 - α) := mul_le_mul_of_nonneg_left hfactor hqnonneg
  have hgap : p + 4 * δ ≤ q * p := by
    dsimp [p]
    nlinarith [hδbound]
  have hEpow : E ^ (q * p) ≤ E ^ (p + 4 * δ) :=
    (Real.antitone_rpow_of_base_le_one hEpos hEle) hgap
  have h2pow : (2 : ℝ) ^ p ≤ 2 := by
    calc
      (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hpone
      _ = 2 := by rw [Real.rpow_one]
  have hsplit : (2 * E ^ q) ^ p = 2 ^ p * E ^ (q * p) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hEpos.le q),
      ← Real.rpow_mul hEpos.le]
  have hepow : e ^ p ≤ 2 * E ^ (p + 4 * δ) := by
    calc
      e ^ p ≤ (2 * E ^ q) ^ p := Real.rpow_le_rpow hepos.le heupper hp.le
      _ = 2 ^ p * E ^ (q * p) := hsplit
      _ ≤ 2 * E ^ (p + 4 * δ) := by
        calc
          _ ≤ 2 * E ^ (q * p) :=
            mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hEpos.le _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hEpow (by norm_num)
  have hcpos : 0 < (2 : ℝ) ^ (-26 : ℤ) / 81 := by positivity
  have hcoef : 2 / ((2 : ℝ) ^ (-26 : ℤ) / 81) ≤ (2 : ℝ) ^ 34 := by
    norm_num [zpow_neg]
  have hbig : e ^ p ≤ (2 : ℝ) ^ 34 * D.tau m := by
    calc
      e ^ p ≤ 2 * E ^ (p + 4 * δ) := hepow
      _ ≤ (2 / ((2 : ℝ) ^ (-26 : ℤ) / 81)) * D.tau m := by
        have hh := mul_le_mul_of_nonneg_left hTauLower
          (by positivity : 0 ≤ 2 / ((2 : ℝ) ^ (-26 : ℤ) / 81))
        calc
          _ = (2 / ((2 : ℝ) ^ (-26 : ℤ) / 81)) *
              (((2 : ℝ) ^ (-26 : ℤ) / 81) * E ^ (p + 4 * δ)) := by
                field_simp [ne_of_gt hcpos]
          _ ≤ _ := hh
      _ ≤ (2 : ℝ) ^ 34 * D.tau m :=
        mul_le_mul_of_nonneg_right hcoef (D.tau_pos m hm).le
  have hmul : (D.tau m)⁻¹ * e ^ p ≤ (2 : ℝ) ^ 34 := by
    calc
      _ ≤ (D.tau m)⁻¹ * ((2 : ℝ) ^ 34 * D.tau m) :=
        mul_le_mul_of_nonneg_left hbig (inv_nonneg.mpr (D.tau_pos m hm).le)
      _ = (2 : ℝ) ^ 34 := by field_simp [ne_of_gt (D.tau_pos m hm)]
  have hrpow : 0 < e ^ p := Real.rpow_pos_of_pos hepos p
  have hfinal : (D.tau m)⁻¹ ≤ (2 : ℝ) ^ 34 / e ^ p :=
    (le_div_iff₀ hrpow).2 hmul
  have hpowneg : e ^ (α - 1) = (e ^ p)⁻¹ := by
    have hexp : α - 1 = -p := by dsimp [p]; ring
    rw [hexp, Real.rpow_neg hepos.le]
  have hvel : D.velocityAmplitude m = e ^ (α - 1) := by
    rw [D.velocityAmplitude_eq]
  rw [hvel]
  simpa [div_eq_mul_inv, hpowneg] using hfinal

/-- Every fine cutoff time power is controlled by the current velocity
amplitude, uniformly through `Nstar`. -/
theorem fine_time_power_le_current_amplitude
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {m : ℕ} (hm : 1 ≤ m)
    {ell N : ℕ} (hell : ell ≤ N) :
    (2 : ℝ) ^ ell * (D.tau m)⁻¹ ^ ell ≤
      (2 * (2 : ℝ) ^ 34) ^ N * D.velocityAmplitude m ^ ell := by
  have hA : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
  have hbase : 2 * (D.tau m)⁻¹ ≤
      (2 * (2 : ℝ) ^ 34) * D.velocityAmplitude m := by
    calc
      2 * (D.tau m)⁻¹ ≤ 2 * ((2 : ℝ) ^ 34 * D.velocityAmplitude m) :=
        mul_le_mul_of_nonneg_left (inverse_tau_le_current_velocityAmplitude D hm)
          (by norm_num)
      _ = _ := by ring
  have hτ : 0 < D.tau m := D.tau_pos m hm
  have hpow := pow_le_pow_left₀
    (mul_nonneg (by norm_num) (inv_nonneg.mpr hτ.le)) hbase ell
  rw [mul_pow, mul_pow] at hpow
  calc
    (2 : ℝ) ^ ell * (D.tau m)⁻¹ ^ ell ≤
        (2 * (2 : ℝ) ^ 34) ^ ell * D.velocityAmplitude m ^ ell := hpow
    _ ≤ (2 * (2 : ℝ) ^ 34) ^ N * D.velocityAmplitude m ^ ell :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ 34) hell)
        (pow_nonneg hA.le ell)

/-- The stream increment is locally a finite sum of transported
recursion terms, exactly as in the proof for `IsStreamSeq` in the `AVenhance` library. -/
theorem stream_increment_word_sum
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) {m : ℕ} (hm : 1 ≤ m)
    (w : List (Option (Fin 2))) (z : AmnrSpace) :
    ∃ S : Finset ℤ, S.card ≤ 3 ∧
      amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) w
        (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z =
        ∑ k ∈ S, amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) w
          (fun y => streamRecursionCutoff D m k y.1 *
            ocShear α q Λ m k
              (constructionFlowInv D hseq (m - 1) y.1 y.2
                ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) z := by
  classical
  obtain ⟨hφ, hrec⟩ := hseq.2 m hm
  have hφeq : hφ = AVRegularity.Velocity.streamSeq_admissible
      D.hζ D.hΛ hseq (m - 1) := Subsingleton.elim _ _
  let S : Finset ℤ :=
    {(⌊z.1 / D.tau m⌋ : ℤ), (⌊z.1 / D.tau m⌋ : ℤ) + 1}
  let d : ℤ → AmnrSpace → ℝ := fun k y =>
    streamRecursionCutoff D m k y.1 *
      ocShear α q Λ m k
        (constructionFlowInv D hseq (m - 1) y.1 y.2
          ((ocLabel α q Λ m k : ℝ) * D.tauPP m))
  have hτ : 0 < D.tau m := D.tau_pos m hm
  let V : Set AmnrSpace := {y | |y.1 - z.1| < D.tau m / 8}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hz : z ∈ V := by
    change |z.1 - z.1| < D.tau m / 8
    simp [hτ]
  have hzero (k : ℤ) (hk : k ∉ S) (y : AmnrSpace) (hy : y ∈ V) : d k y = 0 := by
    have hcut : streamRecursionCutoff D m k y.1 = 0 := by
      by_contra hne
      have hclose : |y.1 - z.1| < D.tau m / 6 := by
        have habs : |y.1 - z.1| < D.tau m / 8 := by simpa [V] using hy
        nlinarith [hτ]
      have hpair := active_recursion_index D m k y.1 z.1 hclose hne
      have hpair' : ⌊z.1 / D.tau m⌋ ≤ k ∧ k ≤ ⌊z.1 / D.tau m⌋ + 1 := by
        simpa using hpair
      have heq : k = ⌊z.1 / D.tau m⌋ ∨ k = ⌊z.1 / D.tau m⌋ + 1 := by omega
      have hmem : k ∈ S := by rcases heq with h | h <;> simp [S, h]
      exact hk hmem
    dsimp [d]
    rw [hcut]
    simp
  have hincrement : Set.EqOn
      (fun y : AmnrSpace => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2)
      (∑ k ∈ S, d k) V := by
    intro y hy
    have htsum : (∑' k : ℤ, d k y) = ∑ k ∈ S, d k y :=
      tsum_eq_sum (s := S) (fun k hk => hzero k hk y hy)
    have hrecPoint : Φ m y.1 y.2 = Φ (m - 1) y.1 y.2 + ∑' k : ℤ, d k y := by
      have hpoint := congrArg (fun f : ℝ → Vec 2 → ℝ => f y.1 y.2) hrec
      have hflow (k : ℤ) (y : AmnrSpace) :
          Section2FlowIdentities.constructionFlowInv D hseq (m - 1) y.1 y.2
              ((ocLabel α q Λ m k : ℝ) * D.tauPP m) =
            flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous hφ.vel_lipschitz
              y.1 y.2 ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) := by
        rw [hφeq]
        dsimp [Section2FlowIdentities.constructionFlowInv,
          Section2FlowIdentities.streamFlowInv, Section2FlowIdentities.streamFlow]
        rw [D.tauPP_eq_oc m]
      rw [AVRegularity.ocNextStream] at hpoint
      have hterm (k : ℤ) :
          slowEnvelope α q Λ m (ocLabel α q Λ m k) y.1 *
            ζ ((y.1 - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
            ocShear α q Λ m k
              (flowInv (streamVel (Φ (m - 1))) hφ.vel_continuous hφ.vel_lipschitz
                y.1 y.2 ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m)) = d k y := by
        dsimp [d, streamRecursionCutoff]
        rw [D.tau_eq_oc m, ← hflow k y]
      rw [tsum_congr hterm] at hpoint
      simpa [Finset.sum_apply] using hpoint
    change Φ m y.1 y.2 - Φ (m - 1) y.1 y.2 = (∑ k ∈ S, d k) y
    rw [Finset.sum_apply, hrecPoint, htsum]
    ring
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq (m - 1))
  have htermSmooth (k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (d k) := by
    let sk := (ocLabel α q Λ m k : ℝ) * D.tauPP m
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => streamRecursionCutoff D m k r) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (slowEnvelope α q Λ m (ocLabel α q Λ m k) *
          (fun r : ℝ => ζ ((r - (k : ℝ) * D.tau m) / D.tau m)))
      have hslowTerm : ContDiff ℝ (⊤ : ℕ∞)
          (slowEnvelope α q Λ m (ocLabel α q Λ m k)) := by
        unfold slowEnvelope
        fun_prop
      exact hslowTerm.mul (D.hζ.1.comp (by fun_prop))
    have hflow :=
      AVRegularity.Velocity.Port.Section2FlowRegularityCore.constructionFlowInv_joint_smooth
        D hseq (m - 1)
    have hX : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : AmnrSpace => constructionFlowInv D hseq (m - 1) y.1 y.2 sk) := by
      exact hflow.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : AmnrSpace => (y.1, y.2, sk)))
    have hprofile :=
      AVRegularity.Velocity.Port.RecursionIncrement.ocShear_contDiff D m k
    have hprofileFlow : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : AmnrSpace => ocShear α q Λ m k
          (constructionFlowInv D hseq (m - 1) y.1 y.2 sk)) := hprofile.comp hX
    exact (hc.comp contDiff_fst).mul hprofileFlow
  have hsum := amnrWord_congr hV (b := fun y => streamVel (Φ (m - 1)) y.1 y.2)
    hincrement w hz
  rw [hsum]
  have hword := amnrWord_sum hV
    ((hb.smooth.of_le (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn)
    S (fun y => d y) (fun k _ => ((htermSmooth k).of_le
      (show (w.length : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffOn)
    w le_rfl hz
  refine ⟨S, ?_, ?_⟩
  · dsimp [S]
    exact (Finset.card_le_two (a := (⌊z.1 / D.tau m⌋ : ℤ))
      (b := (⌊z.1 / D.tau m⌋ : ℤ) + 1)).trans (by norm_num)
  · simpa [d, Finset.sum_apply, Function.uncurry_def] using hword

/-- The three locally active recursion summands give the mixed stream
increment estimate with an arbitrary finite auxiliary spatial budget. -/
theorem material_aux_streamIncrement_mixed_abs_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {C : ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (word : List (Fin 2)) (ell : ℕ)
    {Nspace : ℕ} (hword : word.length ≤ Nspace)
    (hell : ell ≤ AVenhance.Nstar (1 + α))
    (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord word ell)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      3 * (((2 : ℝ) ^ ell * D.Chat * D.Czeta) *
        (amnrTransportSpatialConstant Nspace * D.velocityAmplitude m *
          D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length) *
        (D.tau m)⁻¹ ^ ell) := by
  obtain ⟨S, hcard, heq⟩ := stream_increment_word_sum D hseq hm
    (amnrMixedWord word ell) z
  rw [heq]
  let B := ((2 : ℝ) ^ ell * D.Chat * D.Czeta) *
    (amnrTransportSpatialConstant Nspace * D.velocityAmplitude m *
      D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length) *
    (D.tau m)⁻¹ ^ ell
  have hChat : 0 ≤ D.Chat := le_trans (by norm_num) D.one_le_Chat
  have hCzeta : 0 ≤ D.Czeta := le_trans (by norm_num) D.one_le_Czeta
  have hA : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
  have hE := D.epsilon_pos m
  have hτ := D.tau_pos m hm
  have hK := amnrTransportSpatialConstant_pos Nspace
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  calc
    _ ≤ ∑ k ∈ S, |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord word ell)
        (fun y => streamRecursionCutoff D m k y.1 *
          ocShear α q Λ m k
            (constructionFlowInv D hseq (m - 1) y.1 y.2
              ((ocLabel α q Λ m k : ℝ) * D.tauPP m))) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, B := Finset.sum_le_sum (fun k _ =>
      material_aux_nextStreamTerm_mixed_abs_le_of_A3 D hseq hreg hm k word ell
        hword hell z)
    _ = (S.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- The mixed stream increment has its current material amplitude, with an
auxiliary spatial order and literal cutoff-time order. -/
def materialAuxStreamMixedCurrentConstant
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Nspace : ℕ) : ℝ :=
  3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace *
    (2 * (2 : ℝ) ^ 34) ^ AVenhance.Nstar (1 + α)

theorem materialAuxStreamMixedCurrentConstant_nonneg
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Nspace : ℕ) :
    0 ≤ materialAuxStreamMixedCurrentConstant D Nspace := by
  unfold materialAuxStreamMixedCurrentConstant
  have hChat : 0 ≤ D.Chat := le_trans (by norm_num) D.one_le_Chat
  have hCzeta : 0 ≤ D.Czeta := le_trans (by norm_num) D.one_le_Czeta
  have hK := amnrTransportSpatialConstant_pos Nspace
  positivity

theorem material_aux_streamIncrement_mixed_current_abs_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {C : ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (word : List (Fin 2)) (ell : ℕ)
    {Nspace : ℕ} (hword : word.length ≤ Nspace)
    (hbudget : word.length + 2 * ell ≤ AVenhance.Nstar (1 + α))
    (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord word ell)
      (fun y => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2) z| ≤
      (materialAuxStreamMixedCurrentConstant D Nspace * D.velocityAmplitude m *
        D.epsilon m ^ 2) * (D.epsilon m)⁻¹ ^ word.length *
        D.velocityAmplitude m ^ ell := by
  have hh := material_aux_streamIncrement_mixed_abs_le_of_A3
    D hseq hreg hm word ell hword (by omega) z
  have hp := fine_time_power_le_current_amplitude D hm
    (N := AVenhance.Nstar (1 + α)) (by omega : ell ≤ AVenhance.Nstar (1 + α))
  have hbase : 0 ≤ (3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace) *
      D.velocityAmplitude m * D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length := by
    have hChat : 0 ≤ D.Chat := le_trans (by norm_num) D.one_le_Chat
    have hCzeta : 0 ≤ D.Czeta := le_trans (by norm_num) D.one_le_Czeta
    have hK := amnrTransportSpatialConstant_pos Nspace
    have hA : 0 < D.velocityAmplitude m := by
      rw [D.velocityAmplitude_eq]
      exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
    have hE := D.epsilon_pos m
    positivity
  have hd := mul_le_mul_of_nonneg_left hp hbase
  refine hh.trans ?_
  calc
    _ = (3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace) *
        ((2 : ℝ) ^ ell * (D.tau m)⁻¹ ^ ell) * D.velocityAmplitude m *
        D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length := by ring
    _ ≤ (3 * D.Chat * D.Czeta * amnrTransportSpatialConstant Nspace) *
        ((2 * (2 : ℝ) ^ 34) ^ AVenhance.Nstar (1 + α) *
          D.velocityAmplitude m ^ ell) * D.velocityAmplitude m *
        D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ word.length := by
      convert hd using 1 <;> ring
    _ = _ := by
      unfold materialAuxStreamMixedCurrentConstant
      ring

end AVRegularity.Velocity.Port.MaterialAuxiliaryWords
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance
open scoped ContDiff
namespace AVRegularity.Velocity.Port.MaterialFlowBounds

/-- The source-form §2 displays sufficient for the spatial slices of the
material Jacobian consequences. This package deliberately excludes the
material conclusion being derived below. -/
structure Section2SpatialFlowData {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) : Prop where
  flow_close : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ x : Vec 2,
      ‖Section2FlowIdentities.constructionFlowJacobian D hseq m r s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |r| * D.velocityAmplitude m ∧
      2 ^ 23 * |r| * D.velocityAmplitude m ≤ 1 / 4
  flow_jacobian_composed : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
      Section2FlowRegularityCore.flowJacobianBarNorm n (2 ^ 10 * (D.epsilon m)⁻¹)
        (fun x => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ →
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r x)
  flow_higher_derivative : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
          Section2FlowIdentities.constructionFlow D hseq m (s + r) y s) x
          (fun k => basisVec (J k))‖ ≤
            2 * n.factorial *
              (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1)

/-- Source-form flow bounds used by the temporal material consequences. This
package is assembled by the Section 2 bridge from the spatial induction and
material-word induction; it is not a field of `JetRecursionData`. -/
structure FlowBoundsData {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) (Cmat : ℝ) : Prop where
  material_constant_ge_one : 1 ≤ Cmat
  inverse_regbounds : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
      Section2FlowRegularityCore.flowJacobianBarNorm n
        (2 ^ 11 * (D.epsilon m)⁻¹)
        (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤
        ENNReal.ofReal (2 ^ 23 * |t| * D.velocityAmplitude m)
  flow_close : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ x : Vec 2,
      ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
        2 ^ 23 * |t| * D.velocityAmplitude m ∧
      2 ^ 23 * |t| * D.velocityAmplitude m ≤ 1 / 4
  flow_jacobian_composed : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
      Section2FlowRegularityCore.flowJacobianBarNorm n
        (2 ^ 10 * (D.epsilon m)⁻¹)
        (fun x => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s t x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ →
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s t x)
  flow_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      Section2FlowRegularityCore.flowJacobianBarNorm n
        (2 ^ 14 * (D.epsilon m)⁻¹)
        (Section2FlowIdentities.constructionFlowJacobian D hseq m t s) ≤
        ENNReal.ofReal 12
  flow_higher_derivative : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
          Section2FlowIdentities.constructionFlow D hseq m (s + t) y s)
          x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1)
  material_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ AVenhance.Nstar (1 + α) → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => constructionMaterialIterate
              (fun r z => streamVel (Φ m) (s + r) z) ell
              (fun r z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r z
                (basisVec j) i) t y)
            x (fun k => basisVec (J k))‖ ≤
          Cmat * (D.epsilon m)⁻¹ ^ n *
            (D.epsilon m ^ ((1 + α) - 2)) ^ ell
  material_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r x
          (basisVec j) i) t
  inverse_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => Section2FlowIdentities.constructionFlowInvJacobian D hseq m r s x) t
  inverse_transport : ∀ m : ℕ, 1 ≤ m → ∀ t s : ℝ, ∀ x : Vec 2,
    HasDerivAt (fun r : ℝ => Section2FlowIdentities.constructionFlowInv D hseq m r x s)
      (-(Section2FlowIdentities.constructionFlowInvJacobian D hseq m (t - s) s x)
        (streamVel (Φ m) t x)) t

theorem iteratedFDeriv_component {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : Vec 2)
    (J : Fin n → Vec 2) (i : Fin 2) :
    iteratedFDeriv ℝ n (fun y : Vec 2 => f y i) x
      J = iteratedFDeriv ℝ n f x J i := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hcomp := P.iteratedFDeriv_comp_left
    (f := f) (x := x) hfN.contDiffAt (i := n) le_rfl
  change iteratedFDeriv ℝ n (P ∘ f) x J = _
  rw [hcomp]
  rfl

theorem fderiv_component_apply {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => f y i) x (basisVec j) =
      fderiv ℝ f x (basisVec j) i := by
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa using h'

theorem basisVec_norm_eq_one (j : Fin 2) : ‖basisVec j‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro k
    by_cases hk : k = j <;> simp [basisVec, hk]
  · have hk := norm_le_pi_norm (basisVec j) j
    simpa [basisVec] using hk

theorem inverseJacobianPulledBack_cofactor_entries
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s r : ℝ) (x : Vec 2) :
    MaterialGoalSource.inverseJacobianPulledBack D hseq m s r x (basisVec 0) 0 =
        Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 1) 1 ∧
    MaterialGoalSource.inverseJacobianPulledBack D hseq m s r x (basisVec 1) 0 =
        -Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 1) 0 ∧
    MaterialGoalSource.inverseJacobianPulledBack D hseq m s r x (basisVec 0) 1 =
        -Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 0) 1 ∧
    MaterialGoalSource.inverseJacobianPulledBack D hseq m s r x (basisVec 1) 1 =
        Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 0) 0 := by
  let hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  let b := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b (Section2FlowIdentities.constructionFlow D hseq m) := by
    dsimp [b, Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  obtain ⟨_, _, hinv, _⟩ := Infra.Flow.flow_fixed_time_maps_are_C1_inverses
    hb hX s (s + r)
  have hmap : Section2FlowIdentities.constructionFlowInv D hseq m (s + r)
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) s = x := by
    simpa [Section2FlowIdentities.constructionFlowInv,
      Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlowInv,
      Section2FlowIdentities.streamFlow, flowInv] using hinv x
  have hcofBase := Section2FlowIdentities.streamComposedJacobian_cofactor_entries
    hφ r s (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s)
  have hcof := by
    simpa [Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowInvJacobian,
      MaterialGoalSource.inverseJacobianPulledBack] using hcofBase
  have hmap' : Section2FlowIdentities.streamFlowInv (Φ m) hφ (s + r)
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) s = x := by
    simpa [Section2FlowIdentities.constructionFlowInv] using hmap
  have hcomp00 : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 0) 0 =
      Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 0) 0 := by
    simp [Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowJacobian, hmap']
  have hcomp10 : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 1) 0 =
      Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 1) 0 := by
    simp [Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowJacobian, hmap']
  have hcomp01 : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 0) 1 =
      Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 0) 1 := by
    simp [Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowJacobian, hmap']
  have hcomp11 : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
      (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 1) 1 =
      Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec 1) 1 := by
    simp [Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowJacobian, hmap']
  rcases hcof with ⟨h00, h10, h01, h11⟩
  dsimp [MaterialGoalSource.inverseJacobianPulledBack]
  constructor
  · rw [← hcomp11]
    exact h11.symm
  constructor
  · rw [← hcomp10]
    have h10' : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 1) 0 =
        -Section2FlowIdentities.constructionFlowInvJacobian D hseq m r s
          (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 1) 0 := by
      simpa [Section2FlowIdentities.constructionComposedFlowJacobian,
        Section2FlowIdentities.constructionFlowInvJacobian] using h10
    linarith
  constructor
  · rw [← hcomp01]
    have h01' : Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 0) 1 =
        -Section2FlowIdentities.constructionFlowInvJacobian D hseq m r s
          (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (basisVec 0) 1 := by
      simpa [Section2FlowIdentities.constructionComposedFlowJacobian,
        Section2FlowIdentities.constructionFlowInvJacobian] using h01
    linarith
  · rw [← hcomp00]
    exact h00.symm

theorem iteratedFDeriv_add_const_eq_of_pos
    {n : ℕ} {f : Vec 2 → ℝ} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) (c : ℝ) (x : Vec 2) (J : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (fun y => f y + c) x J =
      iteratedFDeriv ℝ n f x J := by
  have hfun : (fun y : Vec 2 => f y + c) = f + fun _ => c := by
    funext y
    rfl
  rw [hfun]
  rw [iteratedFDeriv_add_apply hf.contDiffAt contDiff_const.contDiffAt]
  have hconst := iteratedFDeriv_const_of_ne
    (𝕜 := ℝ) (E := Vec 2) (F := ℝ) (n := n) (by omega) c
  rw [hconst]
  simp

/-- The `ell = 0` slice of `c.material.DX.Xinv`, derived from the explicit
`flow_jacobian_composed` seminorm display in `Section2FlowBoundsAtScale`. -/
def section2MaterialSpatialConstant (N : ℕ) : ℝ :=
  42 + 40 * ∑ q ∈ Finset.range (N + 1),
    ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))

theorem section2_material_jacobian_spatial_slice_of_flow_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} {m N : ℕ}
    (hflow : Section2SpatialFlowData D Φ hseq m) :
    1 ≤ section2MaterialSpatialConstant N ∧ ∀ s r : ℝ,
      |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ →
      ∀ n : ℕ, n ≤ N → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r y
              (basisVec j) i)
            x (fun k => basisVec (J k))‖ ≤
              section2MaterialSpatialConstant N * (D.epsilon m)⁻¹ ^ n := by
  let S : ℝ := ∑ q ∈ Finset.range (N + 1),
      ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))
  let Cmat : ℝ := 42 + 40 * S
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 1 ≤ Cmat := by dsimp [Cmat]; linarith
  refine ⟨?_, ?_⟩
  · simpa [section2MaterialSpatialConstant, Cmat, S] using hC
  intro s r hr n hn i j x J
  let R : ℝ := 2 ^ 10 * (D.epsilon m)⁻¹
  let F : Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r
  let g : Vec 2 → ℝ := fun y => F y (basisVec j) i
  let h : Vec 2 → ℝ := fun y =>
    (F y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  let c : ℝ := (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  have he : 0 < D.epsilon m :=
    D.epsilon_pos m
  have hR : 0 < R := by dsimp [R]; positivity
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    exact hflow.composed_jacobian_smooth s r hr
  have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    fun_prop
  have hhsmooth : ContDiff ℝ (⊤ : ℕ∞) h := by
    dsimp [h]
    fun_prop
  have hbarAll : Section2FlowRegularityCore.flowJacobianBarNorm n R
      (fun y => F y - ContinuousLinearMap.id ℝ (Vec 2)) ≤
        ENNReal.ofReal 40 := by
    simpa [R, F] using hflow.flow_jacobian_composed s r hr n
  have hbar : barNorm n R h ≤ ENNReal.ofReal 40 := by
    unfold Section2FlowRegularityCore.flowJacobianBarNorm at hbarAll
    change (⨆ i : Fin 2, ⨆ j : Fin 2,
      barNorm n R (fun y =>
        (F y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i)) ≤ _ at hbarAll
    change barNorm n R
      (fun y => (F y - ContinuousLinearMap.id ℝ (Vec 2))
        (basisVec j) i) ≤ ENNReal.ofReal 40
    apply le_trans _ hbarAll
    apply le_iSup_of_le i
    apply le_iSup_of_le j
    rfl
  have hhn : ContDiff ℝ n h := hhsmooth.of_le (by simp)
  have hcontinuous : Continuous (fun y : Vec 2 =>
      iteratedFDeriv ℝ n h y (fun k => basisVec (J k))) := by
    have h := hhn.continuous_iteratedFDeriv'
    fun_prop
  have hpt := barNorm_iterated_pointwise (n := n) (R := R) (B := 40)
    J hcontinuous hR (by norm_num) hbar x
  have hdecomp : g = fun y : Vec 2 => h y + c := by
    funext y
    simp [g, h, c, F]
  have hpow : 0 ≤ (D.epsilon m)⁻¹ ^ n := by positivity
  by_cases hn0 : n = 0
  · subst n
    have hHval : ‖h x‖ ≤ 40 := by
      simpa [iteratedFDeriv_zero_apply] using hpt
    have hc : ‖c‖ ≤ 1 := by
      dsimp [c]
      calc
        _ = ‖(basisVec j) i‖ := by simp
        _ ≤ ‖basisVec j‖ := norm_le_pi_norm (basisVec j) i
        _ = 1 := basisVec_norm_eq_one j
    have hGval : ‖g x‖ ≤ 41 := by
      rw [hdecomp]
      calc
        _ ≤ ‖h x‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 40 + 1 := add_le_add hHval hc
        _ = 41 := by norm_num
    have hC41 : (41 : ℝ) ≤ Cmat := by dsimp [Cmat]; linarith
    have hGmat : ‖g x‖ ≤ Cmat := hGval.trans hC41
    simpa [iteratedFDeriv_zero_apply, g, F, section2MaterialSpatialConstant,
      Cmat, S] using hGmat
  · have hnpos : 1 ≤ n := by omega
    have hderivEq : iteratedFDeriv ℝ n g x
        (fun k => basisVec (J k)) =
      iteratedFDeriv ℝ n h x (fun k => basisVec (J k)) := by
      rw [hdecomp]
      exact iteratedFDeriv_add_const_eq_of_pos
        hhn hnpos c x (fun k => basisVec (J k))
    have hfact : 0 < (n.factorial : ℝ) := by positivity
    let dNorm : ℝ := ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) * R⁻¹ ^ n
    have hD : 0 < dNorm := by dsimp [dNorm]; positivity
    have hnormalize :
        40 / dNorm ≤ 40 * (n.factorial : ℝ) * R ^ n := by
      apply (div_le_iff₀ hD).2
      have hprod : (40 * (n.factorial : ℝ) * R ^ n) * dNorm =
          40 * ((n : ℝ) + 1) ^ 2 := by
        dsimp [dNorm]
        rw [mul_assoc, ← mul_assoc, ← mul_assoc]
        rw [inv_pow]
        field_simp [ne_of_gt hR, ne_of_gt hfact]
      rw [hprod]
      have hsquare : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
        have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
        nlinarith
      nlinarith
    have hpoint : ‖iteratedFDeriv ℝ n h x
        (fun k => basisVec (J k))‖ ≤
          40 * (n.factorial : ℝ) * R ^ n := by
      calc
        _ ≤ 40 / dNorm := by simpa [dNorm] using hpt
        _ ≤ 40 * (n.factorial : ℝ) * R ^ n := hnormalize
    let fsum : ℕ → ℝ := fun q =>
      ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q))
    have hsum : fsum n ≤ S := by
      dsimp [fsum, S]
      exact Finset.single_le_sum
        (f := fun q : ℕ => ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)))
        (s := Finset.range (N + 1))
        (fun q hq => by positivity)
        (Finset.mem_range.mpr (by omega))
    have hcoef : 40 * (n.factorial : ℝ) * (2 : ℝ) ^ (10 * n) ≤ Cmat := by
      dsimp [Cmat]
      nlinarith [hsum]
    have hRpow : R ^ n = (2 : ℝ) ^ (10 * n) *
        (D.epsilon m)⁻¹ ^ n := by
      dsimp [R]
      rw [mul_pow, ← pow_mul]
    have hbound : ‖iteratedFDeriv ℝ n g x
        (fun k => basisVec (J k))‖ ≤
          Cmat * (D.epsilon m)⁻¹ ^ n := by
      rw [hderivEq]
      calc
        _ ≤ 40 * (n.factorial : ℝ) * R ^ n := hpoint
        _ = (40 * (n.factorial : ℝ) * (2 : ℝ) ^ (10 * n)) *
            (D.epsilon m)⁻¹ ^ n := by rw [hRpow]; ring
        _ ≤ Cmat * (D.epsilon m)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right hcoef hpow
    simpa [section2MaterialSpatialConstant, Cmat, S] using hbound

end AVRegularity.Velocity.Port.MaterialFlowBounds
end
end
end

section
/-! Import facade for the OC Section 2 flow regularity modules. -/

@[expose] public section
end
end
