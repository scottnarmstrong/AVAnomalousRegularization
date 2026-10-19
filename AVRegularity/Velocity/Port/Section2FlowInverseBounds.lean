-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.Section2FlowRegularityCore
import AVRegularity.Velocity.Port.Section2JointInduction
public import AVenhance.Infra.Section4.Amnr.TransportProfileJets
import AVenhance.Infra.FaaDiBruno.FlowDnInduction.SmallTime
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.FaaDiBruno.Composition
import AVenhance.Infra.FaaDiBruno.TransportSharpEstimate
import AVenhance.Infra.Section4.Amnr.SpatialCompositionRates
import AVenhance.Infra.Section4.Amnr.StreamProfileJets
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular

section
@[expose] public section
open Homogenization MeasureTheory AVenhance
open scoped ContDiff
namespace AVRegularity.Velocity.Port.Section2FlowHigherDerivative

/-! Pointwise all-order spatial derivative extraction for the OC flow. -/

open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.AppB2FieldBounds

theorem continuous_orderedPartial {n : ℕ} {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (J : Fin n → Fin 2) :
    Continuous (fun x => FaaDiBruno.orderedPartial n f x J) := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  have hlift := FaaDiBruno.contDiff_liftVecOne hfN
  have hderiv : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hlift.contDiffAt).continuousAt_iteratedFDeriv (by simp)
  have heval : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
          (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) := by
    fun_prop
  have hmap : Continuous (fun x : Vec 2 => WithLp.toLp 1 x) := by fun_prop
  change Continuous
    ((fun z : FaaDiBruno.VecOne 2 =>
      iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
        (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) ∘
      (fun x : Vec 2 => WithLp.toLp 1 x))
  exact heval.comp hmap

theorem continuous_norm_le_of_ae_le_vecVolume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hopenPos : (FaaDiBruno.vecVolume 2).IsOpenPosMeasure := by
    unfold FaaDiBruno.vecVolume
    infer_instance
  intro x
  by_contra hx
  have hx' : B < ‖f x‖ := lt_of_not_ge hx
  let U : Set (Vec 2) := {y | B < ‖f y‖}
  have hUopen : IsOpen U := isOpen_lt continuous_const (Continuous.norm hf)
  have hUnonempty : U.Nonempty := ⟨x, hx'⟩
  have hUpos : 0 < (FaaDiBruno.vecVolume 2) U :=
    (hopenPos.open_pos U hUopen hUnonempty).bot_lt
  have hnotU : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2), y ∉ U := by
    filter_upwards [h] with y hy
    intro hyU
    have hle : ENNReal.ofReal ‖f y‖ ≤ ENNReal.ofReal B := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hy
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal_iff hB).mp hle)) hyU
  have hUzero : (FaaDiBruno.vecVolume 2) U = 0 := by
    simpa [ae_iff] using hnotU
  exact (ne_of_gt hUpos) hUzero

theorem continuousVector_norm_le_of_ae_le {f : Vec 2 → Vec 2} {B : ℝ}
    (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hcoord : ∀ i : Fin 2, ∀ x, ‖f x i‖ ≤ B := by
    intro i
    apply continuous_norm_le_of_ae_le_vecVolume
      (continuous_apply i |>.comp hf) hB
    filter_upwards [h] with x hx
    have hnorm : ‖f x i‖ ≤ ‖f x‖ := norm_le_pi_norm (f x) i
    have hcomponent : ‖f x i‖ₑ ≤ ‖f x‖ₑ := by
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    exact hcomponent.trans hx
  intro x
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  exact hcoord i x

theorem orderedPartial_pointwise_of_snorm {n : ℕ} {f : Vec 2 → Vec 2}
    {R C : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hC : 0 ≤ C)
    (hs : FaaDiBruno.snorm f n R ≤ ENNReal.ofReal C)
    (J : Fin n → Fin 2) (x : Vec 2) :
    ‖FaaDiBruno.orderedPartial n f x J‖ ≤
      C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
  have hderiv := FaaDiBruno.derivativeSup_le_of_snorm_le f hR hs
  have hpartial : FaaDiBruno.partialSup n f J ≤ ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (le_iSup_of_le J le_rfl).trans hderiv
  have hess : eLpNormEssSup (fun y => FaaDiBruno.orderedPartial n f y J)
      (FaaDiBruno.vecVolume 2) ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
    simpa [FaaDiBruno.partialSup] using hpartial
  have hae : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2),
      ‖FaaDiBruno.orderedPartial n f y J‖ₑ ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (ae_le_eLpNormEssSup
      (f := fun y => FaaDiBruno.orderedPartial n f y J)
      (μ := FaaDiBruno.vecVolume 2)).mono fun y hy => hy.trans hess
  have hboundNonneg : 0 ≤ C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (by positivity)
  have hpoint := continuousVector_norm_le_of_ae_le
    (B := C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2)
    (continuous_orderedPartial hf J) hboundNonneg hae
  exact hpoint x

theorem orderedPartial_eq_iteratedFDeriv {n : ℕ} {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (J : Fin n → Fin 2) :
    FaaDiBruno.orderedPartial n f x J =
      iteratedFDeriv ℝ n f x (fun j => basisVec (J j)) := by
  unfold FaaDiBruno.orderedPartial FaaDiBruno.liftVecOne
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  change iteratedFDeriv ℝ n
      (f ∘ (FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap)
      (WithLp.toLp 1 x)
      (fun j => FaaDiBruno.coordinateVectorOne 2 (J j)) = _
  rw [(FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    hfN (WithLp.toLp 1 x) le_rfl]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    FaaDiBruno.vecOneEquiv, FaaDiBruno.coordinateVectorOne,
    basisVec, PiLp.coe_continuousLinearEquiv]

theorem section2_flow_higher_derivative_from_current_induction
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcurrent : Section2StreamInductionHypothesis D Φ m)
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (x : Vec 2) (J : Fin n → Fin 2)
    (hclose : ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * D.velocityAmplitude m ∧
      2 ^ 23 * |t| * D.velocityAmplitude m ≤ 1 / 4) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        Section2FlowIdentities.constructionFlow D hseq m (s + t) y s) x
        (fun k => basisVec (J k))‖ ≤
      2 * n.factorial *
        (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := Section2FlowIdentities.constructionFlow D hseq m
  let Rm : ℝ := D.radius m
  let Mm : ℝ := D.jetSize m
  let Cf : ℝ := Mm / Rm
  have hRm : 0 < Rm := by dsimp [Rm]; exact Section2Scales.section2_radius_pos D m
  have hMm : 0 < Mm := by dsimp [Mm]; exact Section2Scales.section2_amplitude_pos D m
  have he : 0 < D.epsilon m := D.epsilon_pos m
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hMbound : Mm ≤ 2 ^ 19 * D.velocityAmplitude m := by
    dsimp [Mm]
    exact AVRegularity.Velocity.Port.Scalars.full_amplitude_recurrence_bound D m
  have ha : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos he _
  have hma : Mm * (D.velocityAmplitude m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ ha).2
    dsimp [Mm] at hMbound
    linarith only [hMbound]
  have hMtime : Mm * |t| ≤ 1 / 64 := by
    calc
      Mm * |t| ≤ Mm * (2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹) :=
        mul_le_mul_of_nonneg_left ht hMm.le
      _ = 2 ^ (-25 : ℤ) * (Mm * (D.velocityAmplitude m)⁻¹) := by ring
      _ ≤ 2 ^ (-25 : ℤ) * 2 ^ 19 :=
        mul_le_mul_of_nonneg_left hma (by positivity)
      _ = 1 / 64 := by norm_num
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) := mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, Section2FlowIdentities.constructionFlow]
    exact AVenhance.flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  let bShift : ℝ → Vec 2 → Vec 2 := fun u y => b (s + u) y
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u y r => X (s + u) y (s + r)
  have hbShift : Infra.Flow.SmoothPeriodicField bShift := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
      change ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro k ell r y
      dsimp [bShift]
      simpa [add_assoc] using hb.periodic k ell (s + r) y
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using Section2FlowIdentities.constructionFlow_shift_isFlow hX s
  have hXjoint := Section2FlowRegularityCore.constructionFlow_joint_smooth D hseq m
  have hXShiftSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Vec 2) × ℝ => XShift p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × Vec 2) × ℝ =>
          (s + p.1.1, p.1.2, s + p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        Section2FlowIdentities.constructionFlow D hseq m p.1 p.2.1 p.2.2) ∘
        (fun p : (ℝ × Vec 2) × ℝ => (s + p.1.1, p.1.2, s + p.2)))
    exact hXjoint.comp hmap
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := AppB2FieldBounds.section2_streamVel_snorm_bound D hseq hcurrent
      (n := k) hk (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  let f : Vec 2 → Vec 2 := fun y => Section2FlowIdentities.constructionFlow D hseq m (s + t) y s
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + t, y, s)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        Section2FlowIdentities.constructionFlow D hseq m p.1 p.2.1 p.2.2) ∘
        (fun y : Vec 2 => (s + t, y, s)))
    exact hXjoint.comp hmap
  have hDn := FaaDiBruno.flow_spatialDn_snorm_smallTime
    (N := n) (by omega) hbShift hXShift hXShiftSmooth hCf hRm hBfield
    (t := t) hpaperTime n hn (by rfl)
  let Rflow : ℝ := 16 * Rm * (1 + 16 * Cf * Rm * |t|)
  let Rtarget : ℝ := 2 ^ 14 * (D.epsilon m)⁻¹
  let Cflow : ℝ := FaaDiBruno.flowHalfBinomialCoeff (n - 1) / (2 * Rm)
  have hRflowDef : (8 : ℝ) * 2 * Rm *
      (1 + (8 * 2 * Cf * Rm) * |t|) = Rflow := by
    dsimp [Rflow]
    ring
  have hflowSnorm : FaaDiBruno.snorm f n Rflow ≤ ENNReal.ofReal Cflow := by
    have hDnR := hDn
    rw [hRflowDef] at hDnR
    simpa [f, XShift, X, Section2FlowIdentities.constructionFlow, Cflow] using hDnR
  have hRflowPositive : 0 < Rflow := by dsimp [Rflow]; positivity
  have hfactor : 1 + 16 * Cf * Rm * |t| ≤ 5 / 4 := by
    rw [show 16 * Cf * Rm * |t| = 16 * (Mm * |t|) by rw [← hCfRm]; ring]
    linarith only [hMtime]
  have hRflow20 : Rflow ≤ 20 * Rm := by
    dsimp [Rflow]
    calc
      16 * Rm * (1 + 16 * Cf * Rm * |t|) ≤ 16 * Rm * (5 / 4) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 20 * Rm := by ring
  have hR131 : Rm ≤ 131 * (D.epsilon m)⁻¹ := by
    dsimp [Rm]
    exact AVRegularity.Velocity.Port.Scalars.radius_recurrence_bound D hm
  have hRtargetPositive : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hRflowTarget : Rflow ≤ Rtarget := by
    dsimp [Rtarget]
    calc
      Rflow ≤ 20 * Rm := hRflow20
      _ ≤ 20 * (131 * (D.epsilon m)⁻¹) :=
        mul_le_mul_of_nonneg_left hR131 (by norm_num)
      _ = 2620 * (D.epsilon m)⁻¹ := by ring
      _ ≤ 2 ^ 14 * (D.epsilon m)⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (inv_nonneg.mpr he.le)
  by_cases hn1 : n = 1
  · subst n
    have hdev : ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 / 4 := hclose.1.trans hclose.2
    have hidnorm : ‖ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 := by simp
    have hJnorm : ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x‖ ≤ 2 := by
      have hdecomp : Section2FlowIdentities.constructionFlowJacobian D hseq m t s x =
          (Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
            ContinuousLinearMap.id ℝ (Vec 2)) +
              ContinuousLinearMap.id ℝ (Vec 2) := by abel
      rw [hdecomp]
      calc
        ‖(Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
            ContinuousLinearMap.id ℝ (Vec 2)) +
              ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
            ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
              ContinuousLinearMap.id ℝ (Vec 2)‖ +
                ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := add_le_add hdev hidnorm
        _ ≤ 2 := by norm_num
    have hbasis : ‖basisVec (J 0)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonempty]
      intro i
      by_cases hi : i = J 0
      · simp [Homogenization.basisVec, hi]
      · simp [Homogenization.basisVec, hi]
    rw [iteratedFDeriv_one_apply]
    have hderiv : fderiv ℝ
        (fun y : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + t) y s) x =
        Section2FlowIdentities.constructionFlowJacobian D hseq m t s x := rfl
    rw [hderiv]
    calc
      ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x (basisVec (J 0))‖ ≤
          ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x‖ * ‖basisVec (J 0)‖ :=
        (Section2FlowIdentities.constructionFlowJacobian D hseq m t s x).le_opNorm _
      _ ≤ 2 * 1 := mul_le_mul hJnorm hbasis (norm_nonneg _) (by norm_num)
      _ = 2 * Nat.factorial 1 * Rtarget ^ (1 - 1) := by norm_num
  · have hn2 : 2 ≤ n := by omega
    have hpoint := Section2FlowHigherDerivative.orderedPartial_pointwise_of_snorm hf hRflowPositive
      (div_nonneg (FaaDiBruno.flowHalfBinomialCoeff_nonneg
        (by omega : 1 ≤ n - 1)) (by positivity)) hflowSnorm J x
    have hcoeff : FaaDiBruno.flowHalfBinomialCoeff (n - 1) ≤ 1 := by
      have hsmall := FaaDiBruno.flowHalfBinomialCoeff_le_inverse
        (n := n - 1) (by omega : 1 ≤ n - 1)
      have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hnSub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (show n - 1 + 1 = n by omega)
      have hsmall' : FaaDiBruno.flowHalfBinomialCoeff (n - 1) ≤
          1 / (4 * (n : ℝ)) := by
        simpa [hnSub] using hsmall
      have hfrac : (1 : ℝ) / (4 * (n : ℝ)) ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).2
        linarith only [hnReal]
      exact hsmall'.trans hfrac
    have hCflowRflow : Cflow * Rflow ≤ 10 := by
      dsimp [Cflow]
      calc
        (FaaDiBruno.flowHalfBinomialCoeff (n - 1) / (2 * Rm)) * Rflow ≤
            (1 / (2 * Rm)) * Rflow := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hRflowPositive)
              exact (div_le_div_of_nonneg_right hcoeff (by positivity))
        _ = Rflow / (2 * Rm) := by ring
        _ ≤ 10 := (div_le_iff₀ (by positivity)).2 (by linarith only [hRflow20])
    have hcoefRadius : Cflow * Rflow / (n + 1 : ℝ) ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).2
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hden : 9 ≤ (n + 1 : ℝ) ^ 2 :=
        le_trans (by norm_num)
          (pow_le_pow_left₀ (by norm_num) (by linarith only [hnR] : (3 : ℝ) ≤ n + 1) 2)
      linarith only [hCflowRflow, hden]
    have hpow : Rflow ^ (n - 1) ≤ Rtarget ^ (n - 1) :=
      pow_le_pow_left₀ hRflowPositive.le hRflowTarget (n - 1)
    have htargetBound : Cflow * n.factorial * Rflow ^ n / (n + 1 : ℝ) ^ 2 ≤
        2 * n.factorial * Rtarget ^ (n - 1) := by
      have hpowN : Rflow ^ n = Rflow ^ (n - 1) * Rflow := by
        calc
          Rflow ^ n = Rflow ^ ((n - 1) + 1) := by congr 1; omega
          _ = Rflow ^ (n - 1) * Rflow := by rw [pow_succ]
      calc
        Cflow * n.factorial * Rflow ^ n /
            (n + 1 : ℝ) ^ 2 =
          Cflow * n.factorial * (Rflow ^ (n - 1) * Rflow) /
            (n + 1 : ℝ) ^ 2 := by rw [hpowN]
        _ = (Cflow * Rflow / (n + 1 : ℝ) ^ 2) *
            (n.factorial * Rflow ^ (n - 1)) := by ring
        _ ≤ 2 * (n.factorial * Rtarget ^ (n - 1)) := by
          apply mul_le_mul hcoefRadius
          · exact mul_le_mul_of_nonneg_left hpow (by positivity)
          · positivity
          · norm_num
        _ = 2 * n.factorial * Rtarget ^ (n - 1) := by ring
    rw [← Section2FlowHigherDerivative.orderedPartial_eq_iteratedFDeriv hf x J]
    exact hpoint.trans htargetBound

/-- The source all-order flow derivative estimate at level `m`, derived from
the previous stream-induction level and its flow-closeness consequence. -/
theorem section2_flow_higher_derivative_from_previous
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1))
    (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        Section2FlowIdentities.constructionFlow D hseq m (s + t) y s)
        x (fun k => basisVec (J k))‖ ≤
      2 * n.factorial * (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1) := by
  exact section2_flow_higher_derivative_from_current_induction D hseq m n hm hn
    (section2_stream_induction_step (D := D) (hseq := hseq) happB2 m hm hprev)
    s t ht x J
    (Section2FlowRegularityCore.section2_flow_close_from_previous D hseq happB2
      m hm hprev s t ht x)

end AVRegularity.Velocity.Port.Section2FlowHigherDerivative
end
end

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
open AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity.Port.MaterialAuxiliaryProfile

/-! Transported profiles at auxiliary spatial orders, with material cutoff
orders checked against the literal source cutoff. -/

/-- The pointwise derivative estimate of the shear, in amplitude and
radius form. -/
theorem ocShear_iteratedFDeriv_norm_le
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) (k : ℤ) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (AVRegularity.ocShear α q Λ m k) x‖ ≤
      (D.velocityAmplitude m * D.epsilon m ^ 2) *
        (2 * Real.pi) ^ n * (D.epsilon m)⁻¹ ^ n := by
  let E := D.epsilon m
  have hE : 0 < E := D.epsilon_pos m
  have hA : 0 ≤ E ^ (1 + α) := Real.rpow_nonneg hE.le _
  have hω : 0 ≤ 2 * Real.pi / E := by positivity
  have heq : AVRegularity.ocShear α q Λ m k = fun x => E ^ (1 + α) *
      (if k % 4 = 1 then Real.sin ((2 * Real.pi / E) * x 0)
       else if k % 4 = 3 then Real.sin ((2 * Real.pi / E) * x 1) else 0) := by
    funext y
    dsimp [E, AVRegularity.ocShear]
    rw [D.epsilon_eq_oc m]
    unfold AVenhance.psi0
    have hcoord (i : Fin 2) :
        2 * Real.pi * ((ocEpsilon q Λ m)⁻¹ * y i) =
          (2 * Real.pi / ocEpsilon q Λ m) * y i := by
      rw [div_eq_mul_inv]
      ring
    by_cases h1 : k % 4 = 1
    · simp only [ite_eq_left h1]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hcoord 0]
    · by_cases h3 : k % 4 = 3
      · simp only [ite_eq_right h1, ite_eq_left h3]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hcoord 1]
      · simp only [ite_eq_right h1, ite_eq_right h3]
  have hamp : D.velocityAmplitude m * E ^ 2 = E ^ (1 + α) := by
    rw [D.velocityAmplitude_eq]
    rw [← Real.rpow_natCast E 2, ← Real.rpow_add hE]
    congr 1
    ring
  have hbound : 0 ≤ (D.velocityAmplitude m * E ^ 2) *
      (2 * Real.pi) ^ n * E⁻¹ ^ n := by
    rw [D.velocityAmplitude_eq]
    positivity
  rw [heq]
  by_cases h1 : k % 4 = 1
  · simp only [h1, ite_true]
    have hh := amnr_shear_iteratedFDeriv_norm_le hA hω 0 n x
    rw [hamp]
    simpa [E, mul_pow, mul_assoc, div_eq_mul_inv] using hh
  · by_cases h3 : k % 4 = 3
    · simp only [ite_eq_right h1, ite_eq_left h3]
      have hh := amnr_shear_iteratedFDeriv_norm_le hA hω 1 n x
      rw [hamp]
      simpa [E, mul_pow, mul_assoc, div_eq_mul_inv] using hh
    · simp only [ite_eq_right h1, ite_eq_right h3]
      have hzero : (fun x : Vec 2 => E ^ (1 + α) * 0) = fun _ => 0 := by
        funext y
        simp
      rw [hzero]
      by_cases hn : n = 0
      · subst n
        simp only [norm_iteratedFDeriv_zero, norm_zero]
        simpa [E] using hbound
      · rw [iteratedFDeriv_const_of_ne hn]
        simpa [E] using hbound

/-- Every actual transported profile derivative retains the fine spatial
radius. Coarse flow derivatives are absorbed by the actual scale separation. -/
theorem material_aux_transportProfile_iteratedFDeriv_norm_le_of_A3
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (D : JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    {C : ℝ} (hreg : Section2Induction.OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (k l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * D.tauPP m| ≤ D.tauPP m / 2 + D.tauP m)
    {N : ℕ} (n : ℕ) (hbudget : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => AVRegularity.ocShear α q Λ m k
        (Section2FlowIdentities.constructionFlowInv D hseq (m - 1)
          t y ((l : ℝ) * D.tauPP m))) x‖ ≤
      amnrTransportSpatialConstant N * D.velocityAmplitude m *
        D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ n := by
  let E := D.epsilon m
  let P := D.epsilon (m - 1)
  let A := D.velocityAmplitude m
  let K := amnrFlowSpatialSourceConstant N
  let Y : Vec 2 → Vec 2 := fun y =>
    Section2FlowIdentities.constructionFlowInv D hseq (m - 1)
      t y ((l : ℝ) * D.tauPP m)
  change ‖iteratedFDeriv ℝ n
      (fun y => AVRegularity.ocShear α q Λ m k (Y y)) x‖ ≤
    amnrTransportSpatialConstant N * D.velocityAmplitude m *
      D.epsilon m ^ 2 * (D.epsilon m)⁻¹ ^ n
  have hE : 0 < E := D.epsilon_pos m
  have hP : 0 < P := D.epsilon_pos _
  have hA : 0 < A := by
    dsimp [A]
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos hE _
  have hK : 1 ≤ K :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (amnrJacobianJetConstant_two_le _ _)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hEP : E ≤ P := by
    have hratio := D.epsilon_ratio m hm
    have hΛ : 128 ≤ Λ := D.hΛ
    have hL : 1 ≤ (Λ : ℝ) := by exact_mod_cast (show 1 ≤ Λ by omega)
    have hmul : (Λ : ℝ) * E ≤ P := (le_div_iff₀ hE).mp hratio
    exact (le_mul_of_one_le_left hE.le hL).trans hmul
  have hout : ∀ j, j ≤ n →
      ‖iteratedFDeriv ℝ j (AVRegularity.ocShear α q Λ m k) (Y x)‖ ≤
        (A * E ^ 2 * (2 * Real.pi) ^ N) * E⁻¹ ^ j := by
    intro j hj
    have hh := ocShear_iteratedFDeriv_norm_le D m k j (Y x)
    refine hh.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hπ (hj.trans hbudget))
        (by positivity)) (by positivity)
  have hin : ∀ j, j < n → ‖iteratedFDeriv ℝ (j + 1) Y x‖ ≤ K * E⁻¹ ^ j := by
    intro j hj
    have hh :=
      AVRegularity.Velocity.Port.MaterialAuxiliaryFlow.amnr_aux_xFlowInv_iteratedFDeriv_norm_le_of_A3
        D hseq hreg hm l t ht (N := N) j (by omega) x
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hP.le) (inv_anti₀ hE hEP) j) (by linarith))
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := by
    have hjoint :=
      AVRegularity.Velocity.Port.Section2FlowRegularityCore.constructionFlowInv_joint_smooth
        D hseq (m - 1)
    simpa [Y, Function.comp_def] using hjoint.comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (t, y, (l : ℝ) * D.tauPP m)))
  have hh := amnr_iteratedFDeriv_comp_radius_bound
    (AVRegularity.Velocity.Port.RecursionIncrement.ocShear_contDiff D m k)
    hY hE hK n x hout hin
  have htransport : ‖iteratedFDeriv ℝ n
      (fun y => AVRegularity.ocShear α q Λ m k (Y y)) x‖ ≤
      amnrTransportSpatialConstant N * A * E ^ 2 * E⁻¹ ^ n := by
    refine hh.trans ?_
    have hc : (n.factorial : ℝ) * (2 * Real.pi) ^ N * K ^ n ≤
        amnrTransportSpatialConstant N := by
      unfold amnrTransportSpatialConstant
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hbudget)
          (by positivity))
        (pow_le_pow_right₀ hK hbudget) (by positivity) (by positivity)
    calc
      _ = ((n.factorial : ℝ) * (2 * Real.pi) ^ N * K ^ n) * A * E ^ 2 * E⁻¹ ^ n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hA.le) (sq_nonneg E))
        (by positivity)
  simpa [Y, E, A] using htransport

end AVRegularity.Velocity.Port.MaterialAuxiliaryProfile
end
end
end

section
@[expose] public section
open Homogenization MeasureTheory AVenhance
open scoped ContDiff
namespace AVRegularity.Velocity.Port.Section2FlowInverseBounds

/-! Quantitative regularity of the OC inverse flow in the Section 2 time
window. The transport estimate is copied from the source with the OC radius
and amplitude recurrences substituted. -/

open AVRegularity.Velocity.Port.Section2FlowIdentities
open AVRegularity.Velocity.Port.Section2FlowRegularityCore
open AVRegularity.Velocity.Port.Section2FlowHigherDerivative
open AVRegularity.Velocity.Port.Section2Induction

/-- A bound on one additional derivative controls the seminorm of the
spatial gradient matrix, with the radius conversion made explicit. -/
theorem spatialGradient_snorm_le_time_scaled
    (f : Vec 2 → Vec 2) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    {Rsrc Rt Rbase C τ : ℝ}
    (hRsrc : 0 < Rsrc) (hRt : 0 < Rt) (hRbase : 0 < Rbase)
    (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hRsrcBase : Rsrc ≤ (9 / 8) * Rbase)
    (hRratio : Rsrc / Rt ≤ 1 / 8)
    (hnext : FaaDiBruno.snorm f (n + 1) Rsrc ≤
      ENNReal.ofReal (16 * C * τ)) :
    FaaDiBruno.snorm (FaaDiBruno.spatialGradientMatrix f) n Rt ≤
      ENNReal.ofReal (8 * C * Rbase * τ) := by
  have hDnext := FaaDiBruno.derivativeSup_le_of_snorm_le f hRsrc hnext
  have hDgrad := FaaDiBruno.spatialGradientMatrix_derivativeSup_le f hf n
  have hDgrad' : FaaDiBruno.derivativeSup n
      (FaaDiBruno.spatialGradientMatrix f) ≤ ENNReal.ofReal
        (16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2) := by
    have hDnext' : FaaDiBruno.derivativeSup (n + 1) f ≤ ENNReal.ofReal
        (16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2) := by
      convert hDnext using 1
      congr 1
      push_cast
      ring
    exact hDgrad.trans hDnext'
  let q : ℝ := Rsrc / Rt
  let qbase : ℝ := Rsrc / Rbase
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqle : q ≤ 1 / 8 := by simpa [q] using hRratio
  have hqbase : 0 ≤ qbase := by dsimp [qbase]; positivity
  have hqbasele : qbase ≤ 9 / 8 := by
    dsimp [qbase]
    exact (div_le_iff₀ hRbase).2 (by simpa [mul_comm] using hRsrcBase)
  have hpoly : (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 ≤ (n + 1 : ℝ) := by
    have hsq : (n + 1 : ℝ) ^ 2 ≤ (n + 2 : ℝ) ^ 2 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      exact pow_le_pow_left₀ (by linarith only [hn0]) (by linarith only) 2
    have hfrac : (n + 1 : ℝ) ^ 2 / (n + 2 : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      simpa using hsq
    calc
      (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 =
          (n + 1 : ℝ) * ((n + 1 : ℝ) ^ 2 / (n + 2 : ℝ) ^ 2) := by ring
      _ ≤ (n + 1 : ℝ) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = n + 1 := by ring
  have hfactor : 2 *
      ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 * q ^ n * qbase) ≤ 1 := by
    by_cases hn0 : n = 0
    · subst n
      norm_num [q, qbase]
      nlinarith [hqbasele]
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ 2 ^ k := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
            rw [pow_succ]
            push_cast
            have hk0 : 0 ≤ (k : ℝ) := by positivity
            nlinarith [ih, hk0]
      have hqpow : q ^ n ≤ (1 / 8 : ℝ) ^ n :=
        pow_le_pow_left₀ hq hqle n
      have hnatPow : (n + 1 : ℝ) * q ^ n ≤ 1 / 4 := by
        have hprod : (n + 1 : ℝ) * q ^ n ≤
            (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n :=
          mul_le_mul (hnat n) hqpow (by positivity) (by norm_num)
        have hpowEq : (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n = (1 / 4 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num
        have hsmallPow : (1 / 4 : ℝ) ^ n ≤ 1 / 4 := by
          have hnEq : n = (n - 1) + 1 := by omega
          rw [hnEq, pow_succ]
          have hbasePow : (1 / 4 : ℝ) ^ (n - 1) ≤ 1 :=
            pow_le_one₀ (by norm_num) (by norm_num)
          linarith only [mul_le_mul_of_nonneg_left hbasePow
            (by norm_num : 0 ≤ (1 / 4 : ℝ))]
        exact hprod.trans (hpowEq ▸ hsmallPow)
      have hpolyPow := mul_le_mul_of_nonneg_right hpoly (pow_nonneg hq n)
      have hpolyQnonneg : 0 ≤ (n + 1 : ℝ) * q ^ n := by positivity
      have hprodBound :
          (n + 1 : ℝ) * q ^ n * qbase ≤ (n + 1 : ℝ) * q ^ n * (9 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hqbasele hpolyQnonneg
      have htotal :
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2) * q ^ n * qbase ≤
            (n + 1 : ℝ) * q ^ n * (9 / 8 : ℝ) := by
        calc
          _ ≤ (n + 1 : ℝ) * q ^ n * qbase :=
            mul_le_mul_of_nonneg_right hpolyPow hqbase
          _ ≤ _ := hprodBound
      have hlast := mul_le_mul_of_nonneg_right hnatPow
        (by norm_num : 0 ≤ (9 / 8 : ℝ))
      linarith [htotal, hlast]
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
    rw [Nat.factorial_succ]
    norm_cast
  let targetCoeff : ℝ := 8 * C * Rbase * τ * Rt ^ n * n.factorial /
    (n + 1 : ℝ) ^ 2
  have htargetCoeff : 0 ≤ targetCoeff := by
    dsimp [targetCoeff]
    positivity
  have hcoeffEq :
      16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2 =
        targetCoeff * (2 *
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 * q ^ n * qbase)) := by
    dsimp [targetCoeff, q, qbase]
    rw [hfac, div_pow]
    field_simp [ne_of_gt hRbase, ne_of_gt hRt,
      (by positivity : (n + 1 : ℝ) ≠ 0), (by positivity : (n + 2 : ℝ) ≠ 0)]
    ring
  have hcoeff :
      16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2 ≤ targetCoeff := by
    rw [hcoeffEq]
    exact mul_le_of_le_one_right htargetCoeff hfactor
  have hDtarget : FaaDiBruno.derivativeSup n
      (FaaDiBruno.spatialGradientMatrix f) ≤ ENNReal.ofReal targetCoeff :=
    hDgrad'.trans (ENNReal.ofReal_le_ofReal hcoeff)
  have hsnorm := FaaDiBruno.snorm_le_of_derivativeSup_le
    (FaaDiBruno.spatialGradientMatrix f) hRt hDtarget
  simpa [targetCoeff, mul_assoc, mul_left_comm, mul_comm] using hsnorm

theorem inverseFlowJacobian_snorm_from_transport
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (m n : ℕ) (hm : 1 ≤ m)
    (hcurrent : Section2StreamInductionHypothesis D Φ m)
    (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹) :
    Section2FlowRegularityCore.flowJacobianBarNorm n (2 ^ 11 * (D.epsilon m)⁻¹)
      (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤
      ENNReal.ofReal (2 ^ 23 * |t| * D.velocityAmplitude m) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow D hseq m
  let Rm : ℝ := D.radius m
  let Mm : ℝ := D.jetSize m
  let Cf : ℝ := Mm / Rm
  let Rtarget : ℝ := 2 ^ 11 * (D.epsilon m)⁻¹
  let Rsource : ℝ := FaaDiBruno.transportShiftRadius Cf Rm |t|
  have hRm : 0 < Rm := by
    dsimp [Rm]
    exact AVRegularity.Velocity.Port.Section2Scales.section2_radius_pos D m
  have hMm : 0 < Mm := by
    dsimp [Mm]
    exact AVRegularity.Velocity.Port.Section2Scales.section2_amplitude_pos D m
  have he : 0 < D.epsilon m := D.epsilon_pos m
  have ha : 0 < D.velocityAmplitude m := by
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos he _
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hMbound : Mm ≤ 2 ^ 19 * D.velocityAmplitude m := by
    dsimp [Mm]
    exact AVRegularity.Velocity.Port.Scalars.full_amplitude_recurrence_bound D m
  have hma : Mm * (D.velocityAmplitude m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ ha).2
    dsimp [Mm] at hMbound
    linarith only [hMbound]
  have hMtime : Mm * |t| ≤ 1 / 64 := by
    calc
      Mm * |t| ≤ Mm * (2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹) :=
        mul_le_mul_of_nonneg_left ht hMm.le
      _ = 2 ^ (-25 : ℤ) * (Mm * (D.velocityAmplitude m)⁻¹) := by ring
      _ ≤ 2 ^ (-25 : ℤ) * 2 ^ 19 :=
        mul_le_mul_of_nonneg_left hma (by positivity)
      _ = 1 / 64 := by norm_num
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) := mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hRsource : 0 < Rsource := by
    dsimp [Rsource]
    unfold FaaDiBruno.transportShiftRadius
    positivity
  have hRsourceBase : Rsource ≤ (9 / 8) * Rm := by
    dsimp [Rsource]
    rw [FaaDiBruno.transportShiftRadius]
    rw [show 8 * |t| * Cf * Rm ^ 2 = 8 * (Mm * |t|) * Rm by
      rw [← hCfRm]
      ring]
    have hfactor : 1 + 8 * (Mm * |t|) ≤ 9 / 8 := by linarith only [hMtime]
    calc
      Rm + 8 * (Mm * |t|) * Rm = Rm * (1 + 8 * (Mm * |t|)) := by ring
      _ ≤ Rm * (9 / 8) := mul_le_mul_of_nonneg_left hfactor hRm.le
      _ = (9 / 8) * Rm := by ring
  have hR131 : Rm ≤ 131 * (D.epsilon m)⁻¹ := by
    dsimp [Rm]
    exact AVRegularity.Velocity.Port.Scalars.radius_recurrence_bound D hm
  have hRtarget : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hRratio : Rsource / Rtarget ≤ 1 / 8 := by
    apply (div_le_iff₀ hRtarget).2
    calc
      Rsource ≤ (9 / 8) * Rm := hRsourceBase
      _ ≤ (9 / 8) * (131 * (D.epsilon m)⁻¹) :=
        mul_le_mul_of_nonneg_left hR131 (by norm_num)
      _ ≤ (1 / 8) * Rtarget := by
        dsimp [Rtarget]
        have hinv : 0 ≤ (D.epsilon m)⁻¹ := inv_nonneg.mpr he.le
        linarith only [hinv]
  let bShift : ℝ → Vec 2 → Vec 2 := fun u y => b (s + u) y
  let gShift : ℝ → Vec 2 → Vec 2 := fun u y => -bShift u y
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u y r => X (s + u) y (s + r)
  have hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, Section2FlowIdentities.constructionFlow]
    exact AVenhance.flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hbShift : Infra.Flow.SmoothPeriodicField bShift := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
      change ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro k ell r y
      dsimp [bShift]
      simpa [add_assoc] using hb.periodic k ell (s + r) y
  have hgShift : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry gShift) := by
    convert contDiff_neg.comp hbShift.smooth using 1
    rfl
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using constructionFlow_shift_isFlow hX s
  have hXjoint := constructionFlow_joint_smooth D hseq m
  have hXShiftSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Vec 2) × ℝ => XShift p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × Vec 2) × ℝ =>
          (s + p.1.1, p.1.2, s + p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow D hseq m p.1 p.2.1 p.2.2) ∘
        (fun p : (ℝ × Vec 2) × ℝ => (s + p.1.1, p.1.2, s + p.2)))
    exact hXjoint.comp hmap
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := AppB2FieldBounds.section2_streamVel_snorm_bound D hseq hcurrent
      (n := k) hk (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  have hGfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (gShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hneg := snorm_neg_eq_vec (n := k) (R := Rm) (bShift u)
    calc
      FaaDiBruno.snorm (gShift u) k Rm =
          FaaDiBruno.snorm (bShift u) k Rm := by simpa [gShift] using hneg
      _ ≤ ENNReal.ofReal Cf := hBfield u k hk hkn
  have hY := FaaDiBruno.flow_inverse_displacement_isTransportSolution_of_jointSmooth
    hbShift hXShift hXShiftSmooth
  have hnext := FaaDiBruno.transportSolution_snorm_equalRadius_all
    (N := n + 1) hY hbShift.smooth hgShift hXShift hCf hCf.le hRm
    (fun u k hk hkn => hBfield u k hk hkn)
    (fun u k hk hkn => hGfield u k hk hkn)
    (n + 1) (by omega) (by omega) t hpaperTime
  let disp : Vec 2 → Vec 2 := fun y =>
    Section2FlowIdentities.constructionFlowInv D hseq m (s + t) y s - y
  have hInvSmooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun y : Vec 2 => Section2FlowIdentities.constructionFlowInv D hseq m (s + t) y s) := by
    have hInvJoint := constructionFlowInv_joint_smooth D hseq m
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + t, (y, s))) := by fun_prop
    have h := hInvJoint.comp hmap
    simpa only [Function.comp_def] using h
  have hdispSmooth : ContDiff ℝ (⊤ : ℕ∞) disp := by
    dsimp [disp]
    exact hInvSmooth.sub contDiff_id
  have hdispNext : FaaDiBruno.snorm disp (n + 1) Rsource ≤
      ENNReal.ofReal (16 * Cf * |t|) := by
    have hinv (y : Vec 2) :
        Section2FlowIdentities.constructionFlowInv D hseq m (s + t) y s =
          Section2FlowIdentities.constructionFlow D hseq m s y (s + t) := by
      rfl
    simpa [disp, Rsource, XShift, X, hinv] using hnext
  have hgrad := spatialGradient_snorm_le_time_scaled disp hdispSmooth n
    hRsource hRtarget hRm hCf.le (abs_nonneg t) hRsourceBase hRratio hdispNext
  have hGradSmooth : ContDiff ℝ n
      (FaaDiBruno.spatialGradientMatrix disp) := by
    unfold FaaDiBruno.spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => fderiv ℝ disp y (FaaDiBruno.coordinateVector 2 j)) :=
      hdispSmooth.fderiv_right (by simp) |>.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp (hcolumn.of_le (by simp))
  have hJfun : (fun y => Section2FlowIdentities.constructionFlowInvJacobian D hseq m t s y -
      ContinuousLinearMap.id ℝ (Vec 2)) = (fun y => fderiv ℝ disp y) := by
    funext y
    have hsub := fderiv_sub
      (hInvSmooth.differentiable (by simp) y) (differentiable_id y)
    change fderiv ℝ (fun z : Vec 2 =>
        Section2FlowIdentities.constructionFlowInv D hseq m (s + t) z s) y -
      ContinuousLinearMap.id ℝ (Vec 2) = fderiv ℝ disp y
    rw [show disp = (fun z : Vec 2 =>
        Section2FlowIdentities.constructionFlowInv D hseq m (s + t) z s) - id by
      funext z
      rfl]
    simpa [fderiv_id] using hsub.symm
  rw [hJfun]
  have hbound := Section2FlowRegularityCore.flowJacobianBarNorm_le_spatialGradient_snorm disp n Rtarget
    (8 * Cf * Rm * |t|) hGradSmooth hgrad
  have htarget : 8 * Cf * Rm * |t| ≤
      2 ^ 23 * |t| * D.velocityAmplitude m := by
    have hleft : 8 * Cf * Rm * |t| = 8 * (Cf * Rm) * |t| := by ring
    rw [hleft, hCfRm]
    calc
      8 * Mm * |t| ≤ 8 * (2 ^ 19 * D.velocityAmplitude m) * |t| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMbound (by norm_num)) (abs_nonneg t)
      _ = 2 ^ 22 * |t| * D.velocityAmplitude m := by ring
      _ = 2 ^ 22 * (|t| * D.velocityAmplitude m) := by ring
      _ ≤ 2 ^ 23 * (|t| * D.velocityAmplitude m) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (abs_nonneg t) ha.le)
      _ = 2 ^ 23 * |t| * D.velocityAmplitude m := by ring
  exact hbound.trans (ENNReal.ofReal_le_ofReal htarget)

/-- The source `inverse_regbounds` field, derived from the previous scale's
stream induction hypothesis and the equal-radius transport estimate. -/
theorem section2_flow_inverse_regbounds_from_previous
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis D Φ (m - 1)) :
    ∀ s t : ℝ,
      |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
      Section2FlowRegularityCore.flowJacobianBarNorm n
        (2 ^ 11 * (D.epsilon m)⁻¹)
        (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤
        ENNReal.ofReal (2 ^ 23 * |t| * D.velocityAmplitude m) := by
  intro s t ht n
  exact inverseFlowJacobian_snorm_from_transport D hseq m n hm
    (section2_stream_induction_step (D := D) (hseq := hseq) happB2 m hm hprev)
    s t ht

end AVRegularity.Velocity.Port.Section2FlowInverseBounds
end
end
