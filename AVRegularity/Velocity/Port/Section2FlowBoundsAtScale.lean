-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.FaaDiBruno.BarNormBridge
import AVRegularity.Velocity.Port.Section2FlowInverseBounds
public import AVRegularity.Velocity.Port.Section2FlowRegularity
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.FaaDiBruno.Composition
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance
open AVenhance.FaaDiBruno
open AVRegularity.Velocity.Port.MaterialGoalSource
open AVRegularity.Velocity.Port.MaterialPullback
open AVRegularity.Velocity.Port.MaterialFlowBounds
namespace AVRegularity.Velocity.Port.MaterialFlowComposition

/-! Faà di Bruno transfer of material-Jacobian bounds through the flow map. -/

theorem orderedPartial_eq_iteratedFDeriv_local
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ n f)
    (x : Vec 2) (J : Fin n → Fin 2) :
    orderedPartial n f x J =
      iteratedFDeriv ℝ n f x (fun k => basisVec (J k)) := by
  change iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
      (fun k => coordinateVectorOne 2 (J k)) = _
  have h := (vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    (f := f) hf (WithLp.toLp 1 x) (i := n) le_rfl
  have h' := congrArg
    (fun T => T (fun k => coordinateVectorOne 2 (J k))) h
  simpa [liftVecOne, coordinateVectorOne, basisVec, vecOneEquiv,
    PiLp.coe_continuousLinearEquiv] using h'

/-- Uniform coordinate derivative bounds imply the corresponding Appendix B
derivative seminorm bound. -/
theorem derivativeSup_le_of_uniform_coordinate_bound
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ n f) {B : ℝ}
    (hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun k => basisVec (J k))‖ ≤ B) :
    FaaDiBruno.derivativeSup n f ≤ ENNReal.ofReal B := by
  unfold FaaDiBruno.derivativeSup
  apply iSup_le
  intro J
  unfold FaaDiBruno.partialSup
  have hae : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖orderedPartial n f x J‖ₑ ≤ ENNReal.ofReal B := by
    filter_upwards with x
    rw [orderedPartial_eq_iteratedFDeriv_local hf x J]
    simpa using ENNReal.ofReal_le_ofReal (hcoord x J)
  rw [eLpNormEssSup_eq_essSup_enorm]
  exact essSup_le_of_ae_le _ hae

/-- Coordinate derivatives bounded at the natural inverse-regularity radius
give a uniform source seminorm, with the finite order loss exposed. -/
theorem snorm_le_of_uniform_coordinate_bound
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    {R : ℝ} (hR : 0 < R) {B : ℝ}
    (hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n f x (fun k => basisVec (J k))‖ ≤ B) :
    FaaDiBruno.snorm f n R ≤ ENNReal.ofReal
      ((((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        (R⁻¹) ^ n * B) := by
  have hderiv := derivativeSup_le_of_uniform_coordinate_bound f hf hcoord
  rw [FaaDiBruno.snorm]
  rw [← ENNReal.ofReal_inv_of_pos hR,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ R⁻¹)]
  have hcoeff : 0 ≤ ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) := by positivity
  calc
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
        ENNReal.ofReal ((R⁻¹) ^ n) * ENNReal.ofReal B :=
      mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ = ENNReal.ofReal
        ((((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * (R⁻¹) ^ n * B) := by
      rw [← ENNReal.ofReal_mul hcoeff,
        ← ENNReal.ofReal_mul (by positivity :
          0 ≤ ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) * (R⁻¹) ^ n)]

theorem materialJacobianField_joint_smooth
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s : ℝ)
    (ell : ℕ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar
        (constructionMaterialIterate
          (fun q y => streamVel (Φ m) (s + q) y) ell
          (fun q y => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q y
            (basisVec j) i))) := by
  let b : ℝ → Vec 2 → Vec 2 := fun q y => streamVel (Φ m) (s + q) y
  let F : ℝ → Vec 2 → ℝ := fun q y =>
    Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q y (basisVec j) i
  let v : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  have hv : Infra.Flow.SmoothPeriodicField v :=
    AVenhance.Infra.Construction.smoothPeriodic_streamVel (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := by
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => v p.1 p.2) := hv.smooth
    have hshift : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => streamVel (Φ m) (s + p.1) p.2)
    exact hbase.comp hshift
  have hmatrix := constructionComposedFlowJacobian_joint_contDiff
    (D := D) (hseq := hseq) m s
  have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2 (basisVec j)) :=
    hmatrix.clm_apply contDiff_const
  have hentry : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2 (basisVec j) i)
    exact (contDiff_pi.1 hcolumn) i
  have hiterate := constructionMaterialIterate_joint_contDiff hb hentry ell
  simpa [F, b] using hiterate

/-- A material Jacobian field has a uniform Appendix B seminorm after
normalizing its source derivative scale. -/
theorem materialJacobianField_snorm
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData D Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (ell n : ℕ) (hnell : n + ell ≤ AVenhance.Nstar (1 + α))
    (i j : Fin 2) :
    FaaDiBruno.snorm
      (fun y => constructionMaterialIterate
        (fun q z => streamVel (Φ m) (s + q) z) ell
        (fun q z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q z
          (basisVec j) i) r y)
      n (D.epsilon m)⁻¹ ≤
      ENNReal.ofReal (Cmat * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) *
        (D.epsilon m ^ ((1 + α) - 2)) ^ ell) := by
  let e : ℝ := D.epsilon m
  let H : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q z
      (basisVec j) i) r y
  have he : 0 < e := by
    dsimp [e]
    exact D.epsilon_pos m
  have hR : 0 < e⁻¹ := inv_pos.mpr he
  have hH : ContDiff ℝ n H := by
    have hspace :=
      (materialJacobianField_joint_smooth (D := D) (hseq := hseq) m s ell i j).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (r, y)))
    have hspace' : ContDiff ℝ (⊤ : ℕ∞) H := by
      simpa [H, constructionJointScalar, Function.comp_def] using hspace
    exact hspace'.of_le (by simp)
  have hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n H x (fun k => basisVec (J k))‖ ≤
        Cmat * e⁻¹ ^ n * (e ^ ((1 + α) - 2)) ^ ell := by
    intro x J
    exact hflow.material_jacobian m hm s r hr n ell hnell i j x J
  have hseminorm := snorm_le_of_uniform_coordinate_bound H hH hR hcoord
  have hcancel : e ^ n * e⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt he), one_pow]
  have hfactor : ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) ≤
      ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) := by
    have hindex : (n : ℝ) + 1 ≤ (AVenhance.Nstar (1 + α) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (by omega : n ≤ AVenhance.Nstar (1 + α)) 1
    have hfact : 1 ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((AVenhance.Nstar (1 + α) : ℝ) + 1) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hindex
    exact (div_le_self (by positivity) (by linarith)).trans hsq
  have hreal : (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
      ((e⁻¹)⁻¹) ^ n * (Cmat * e⁻¹ ^ n * (e ^ ((1 + α) - 2)) ^ ell) ≤
      Cmat * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) * (e ^ ((1 + α) - 2)) ^ ell := by
    rw [show ((e⁻¹)⁻¹) ^ n = e ^ n by rw [inv_inv]]
    have hCmat : 0 ≤ Cmat := le_trans (by norm_num) hflow.material_constant_ge_one
    have hEell : 0 ≤ (e ^ ((1 + α) - 2)) ^ ell := by positivity
    calc
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * Cmat *
          (e ^ n * e⁻¹ ^ n) * (e ^ ((1 + α) - 2)) ^ ell := by ring
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) * Cmat *
          (e ^ ((1 + α) - 2)) ^ ell := by rw [hcancel]; ring
      _ = (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
          (Cmat * (e ^ ((1 + α) - 2)) ^ ell) := by ring
      _ ≤ ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) *
          (Cmat * (e ^ ((1 + α) - 2)) ^ ell) :=
            mul_le_mul_of_nonneg_right hfactor (mul_nonneg hCmat hEell)
      _ = Cmat * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) *
          (e ^ ((1 + α) - 2)) ^ ell := by ring
  have hfinal := hseminorm.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa [H, e] using hfinal

theorem constructionFlowSlice_smooth_local
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) := by
  let hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  let b := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b (Section2FlowIdentities.constructionFlow D hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hjoint := Infra.Flow.flow_joint_contDiff_infty hb hX
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => (s + r, x, s)) := by fun_prop
  simpa only [Function.comp_def] using hjoint.comp hmap

/-- The forward flow map has the scale-normalized composition seminorm
required by App. B.3, using the corrected `c.flowreg` derivative display. -/
theorem constructionFlowSlice_snorm
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData D Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ AVenhance.Nstar (1 + α)) :
    FaaDiBruno.snorm
      (fun x : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) n
      (2 ^ 14 * (D.epsilon m)⁻¹) ≤
      ENNReal.ofReal (2 * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) *
        (2 ^ 14 * (D.epsilon m)⁻¹)⁻¹) := by
  let e : ℝ := D.epsilon m
  let Rg : ℝ := 2 ^ 14 * e⁻¹
  let Cg : ℝ := 2 * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) * Rg⁻¹
  have he : 0 < e := by
    dsimp [e]
    exact D.epsilon_pos m
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hflowSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) :=
    constructionFlowSlice_smooth_local (hseq := hseq) m s r
  have hcoord : ∀ x (J : Fin n → Fin 2),
      ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + r) y s)
        x (fun k => basisVec (J k))‖ ≤
        2 * n.factorial * Rg ^ (n - 1) := by
    intro x J
    have hderiv := hflow.flow_higher_derivative m hm s r hr n hn x J
    simpa [Rg, e] using hderiv
  have hseminorm := snorm_le_of_uniform_coordinate_bound
    (fun x : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + r) x s)
    (hflowSmooth.of_le (by exact_mod_cast le_top)) hRg hcoord
  have hpow : (Rg⁻¹) ^ n * Rg ^ (n - 1) = Rg⁻¹ := by
    rw [inv_pow]
    have hstep : Rg ^ n = Rg ^ (n - 1) * Rg := by
      calc
        Rg ^ n = Rg ^ (n - 1 + 1) :=
          congrArg (fun q : ℕ => Rg ^ q) (Nat.sub_add_cancel hn).symm
        _ = Rg ^ (n - 1) * Rg := pow_succ Rg (n - 1)
    rw [hstep]
    field_simp [ne_of_gt hRg]
  have hfactor : ((n : ℝ) + 1) ^ 2 ≤ ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) := by
    have hindex : (n : ℝ) + 1 ≤ (AVenhance.Nstar (1 + α) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (by omega : n ≤ AVenhance.Nstar (1 + α)) 1
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hindex
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hreal : (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ)) *
      (Rg⁻¹) ^ n * (2 * n.factorial * Rg ^ (n - 1)) ≤ Cg := by
    calc
      _ = 2 * ((n : ℝ) + 1) ^ 2 * ((Rg⁻¹) ^ n * Rg ^ (n - 1)) := by
        field_simp [ne_of_gt hfact]
      _ = 2 * ((n : ℝ) + 1) ^ 2 * Rg⁻¹ := by rw [hpow]
      _ ≤ 2 * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) * Rg⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor (by norm_num)) (inv_nonneg.mpr hRg.le)
      _ = Cg := by rfl
  have hfinal := hseminorm.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa [Rg, Cg, e, FaaDiBruno.snorm] using hfinal

def materialFlowCompositionConstant (α Cmat : ℝ) : ℝ :=
  Cmat * ((AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2) * ((AVenhance.Nstar (1 + α)).factorial : ℝ) *
    (2 ^ 14 * (1 + (AVenhance.Nstar (1 + α) + 1 : ℝ) ^ 2)) ^ AVenhance.Nstar (1 + α)

/-- Spatial differentiation of the pulled back material Jacobian is controlled
by App. B.3, the pointwise source material display, and the flow derivative
display. -/
theorem materialJacobianPullback_spatial_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData D Φ hseq Cmat) (hm : 1 ≤ m)
    (s r : ℝ)
    (hr : |r| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (ell n : ℕ) (hnell : n + ell ≤ AVenhance.Nstar (1 + α))
    (i j : Fin 2) (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n
      (fun y => constructionMaterialIterate
        (fun q z => streamVel (Φ m) (s + q) z) ell
        (fun q z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q z
          (basisVec j) i) r
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) y s))
      x (fun k => basisVec (J k))‖ ≤
      materialFlowCompositionConstant α Cmat *
        (D.epsilon m)⁻¹ ^ n *
        (D.epsilon m ^ ((1 + α) - 2)) ^ ell := by
  let e : ℝ := D.epsilon m
  let Eell : ℝ := (e ^ ((1 + α) - 2)) ^ ell
  let N : ℝ := (AVenhance.Nstar (1 + α) : ℝ) + 1
  let Rg : ℝ := 2 ^ 14 * e⁻¹
  let Rh : ℝ := e⁻¹
  let Cg : ℝ := 2 * N ^ 2 * Rg⁻¹
  let Ch : ℝ := Cmat * N ^ 2 * Eell
  let Rcomp : ℝ := Rg * (1 + 2 * Cg * Rh)
  let K : ℝ := 2 ^ 14 * (1 + N ^ 2)
  let X : Vec 2 → Vec 2 := fun y => Section2FlowIdentities.constructionFlow D hseq m (s + r) y s
  let H : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q z
      (basisVec j) i) r y
  have he : 0 < e := by
    dsimp [e]
    exact D.epsilon_pos m
  have hCmat : 0 < Cmat := lt_of_lt_of_le (by norm_num)
    hflow.material_constant_ge_one
  have hEbase : 0 < e ^ ((1 + α) - 2) := Real.rpow_pos_of_pos he _
  have hEell : 0 < Eell := by
    dsimp [Eell]
    exact pow_pos hEbase _
  have hRg : 0 < Rg := by dsimp [Rg]; positivity
  have hRh : 0 < Rh := by dsimp [Rh]; positivity
  have hCg : 0 < Cg := by
    have hRginv : 0 < Rg⁻¹ := inv_pos.mpr hRg
    dsimp [Cg]
    positivity
  have hCh : 0 < Ch := by dsimp [Ch]; positivity
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (AVenhance.Nstar (1 + α) : ℝ) + 1
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hRcomp : 0 < Rcomp := by dsimp [Rcomp]; positivity
  have hHtop : ContDiff ℝ (⊤ : ℕ∞) H := by
    have h := (materialJacobianField_joint_smooth
      (D := D) (hseq := hseq) m s ell i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (r, y)))
    simpa [H, constructionJointScalar, Function.comp_def] using h
  have hXtop : ContDiff ℝ (⊤ : ℕ∞) X := by
    simpa [X] using constructionFlowSlice_smooth_local (hseq := hseq) m s r
  have hH : ContDiff ℝ n H := hHtop.of_le (by simp)
  have hXn : ContDiff ℝ n X := hXtop.of_le (by simp)
  have hHsnorm (q : ℕ) (hq : q ≤ n) :
      FaaDiBruno.snorm H q Rh ≤ ENNReal.ofReal Ch := by
    have hqell : q + ell ≤ AVenhance.Nstar (1 + α) := by omega
    simpa [H, Rh, Ch, Eell, e, N] using
      materialJacobianField_snorm hflow hm s r hr ell q hqell i j
  have hXsnorm (q : ℕ) (hq0 : 1 ≤ q) (hq : q ≤ n) :
      FaaDiBruno.snorm X q Rg ≤ ENNReal.ofReal Cg := by
    have hqN : q ≤ AVenhance.Nstar (1 + α) := by omega
    simpa [X, Rg, Cg, N, e] using
      constructionFlowSlice_snorm hflow hm s r hr q hq0 hqN
  have hcomposition := FaaDiBruno.compositionEstimate10528
    H X hH hXn hCh hCg hRh hRg hHsnorm hXsnorm n (by omega)
  have hcompositionSmooth : ContDiff ℝ n (H ∘ X) := hH.comp hXn
  have hbar : barNorm n Rcomp (H ∘ X) ≤ ENNReal.ofReal Ch := by
    rw [FaaDiBruno.barNorm_eq_snorm hcompositionSmooth]
    simpa [H, X, Rcomp, Rg, Cg, Rh, Ch, Eell, e, N] using hcomposition
  have hcontinuous : Continuous (fun y : Vec 2 =>
      iteratedFDeriv ℝ n (H ∘ X) y (fun k => basisVec (J k))) := by
    have h := hcompositionSmooth.continuous_iteratedFDeriv'
    fun_prop
  have hRcomp' : 0 < Rcomp := hRcomp
  have hCh : 0 ≤ Ch := hCh.le
  have hpoint := barNorm_iterated_pointwise
    (n := n) (R := Rcomp) (B := Ch) J hcontinuous hRcomp' hCh hbar x
  have hRcompEq : Rcomp =
      2 ^ 14 * (1 + N ^ 2 / 2 ^ 12) * e⁻¹ := by
    dsimp [Rcomp, Rg, Cg, Rh]
    field_simp [ne_of_gt he]
  have hRratio : 1 + N ^ 2 / 2 ^ 12 ≤ 1 + N ^ 2 := by
    have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
    linarith only [hN2]
  have hRcompLe : Rcomp ≤ K * e⁻¹ := by
    rw [hRcompEq]
    dsimp [K]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRratio (by norm_num)) (inv_nonneg.mpr he.le)
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith only [sq_nonneg N]
  have hRpow : Rcomp ^ n ≤ K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n := by
    calc
      Rcomp ^ n ≤ (K * e⁻¹) ^ n := pow_le_pow_left₀ hRcomp.le hRcompLe n
      _ = K ^ n * e⁻¹ ^ n := by rw [mul_pow]
      _ ≤ K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hK (by omega)) (by positivity)
  have hfac : (n.factorial : ℝ) ≤ (AVenhance.Nstar (1 + α)).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ AVenhance.Nstar (1 + α))
  have hden : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hn0r : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact one_le_pow₀ (by linarith only [hn0r])
  have hpointSimple : ‖iteratedFDeriv ℝ n (H ∘ X) x
      (fun k => basisVec (J k))‖ ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := by
    have hdiv : Ch / (((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) *
        Rcomp⁻¹ ^ n) ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := by
      have hcancel : Rcomp ^ n * Rcomp⁻¹ ^ n = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hRcomp), one_pow]
      apply (div_le_iff₀ (by positivity)).2
      field_simp [ne_of_gt hRcomp]
      calc
        1 = (Rcomp ^ n * Rcomp⁻¹ ^ n) * 1 := by rw [hcancel]; ring
        _ ≤ (Rcomp ^ n * Rcomp⁻¹ ^ n) * ((n : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hden (by positivity)
        _ = Rcomp ^ n * ((n : ℝ) + 1) ^ 2 * (1 / Rcomp) ^ n := by
          rw [one_div]
          ring
    exact hpoint.trans hdiv
  calc
    _ ≤ Ch * (n.factorial : ℝ) * Rcomp ^ n := hpointSimple
    _ = Cmat * N ^ 2 * Eell * (n.factorial : ℝ) * Rcomp ^ n := by
      simp [Ch]
    _ ≤ Cmat * N ^ 2 * Eell * ((AVenhance.Nstar (1 + α)).factorial : ℝ) *
        (K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n) := by
      rw [show Cmat * N ^ 2 * Eell * (n.factorial : ℝ) * Rcomp ^ n =
        (Cmat * N ^ 2 * Eell) * ((n.factorial : ℝ) * Rcomp ^ n) by ring]
      rw [show Cmat * N ^ 2 * Eell * ((AVenhance.Nstar (1 + α)).factorial : ℝ) *
        (K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n) =
        (Cmat * N ^ 2 * Eell) *
          (((AVenhance.Nstar (1 + α)).factorial : ℝ) * (K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n)) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (n.factorial : ℝ) * Rcomp ^ n ≤
            ((AVenhance.Nstar (1 + α)).factorial : ℝ) * Rcomp ^ n :=
              mul_le_mul_of_nonneg_right hfac (by positivity)
        _ ≤ ((AVenhance.Nstar (1 + α)).factorial : ℝ) *
            (K ^ (AVenhance.Nstar (1 + α)) * e⁻¹ ^ n) :=
              mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ = materialFlowCompositionConstant α Cmat * e⁻¹ ^ n * Eell := by
      dsimp [materialFlowCompositionConstant, N, K]
      ring

theorem iteratedTimeDerivative_neg_local
    (ell : ℕ) (f : ℝ → ℝ) :
    iteratedTimeDerivative ell (fun t => -f t) =
      fun t => -iteratedTimeDerivative ell f t := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      funext t
      simp [iteratedTimeDerivative, ih]

theorem norm_iteratedFDeriv_neg_local {g : Vec 2 → ℝ}
    (n : ℕ) (x : Vec 2) (J : Fin n → Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => -g y) x J‖ =
      ‖iteratedFDeriv ℝ n g x J‖ := by
  change ‖iteratedFDeriv ℝ n (-g) x J‖ = _
  rw [iteratedFDeriv_neg]
  change ‖-(iteratedFDeriv ℝ n g x J)‖ = _
  rw [norm_neg]

/-- `c.material.goal`, with the source `c.material.DX.Xinv` field read from
`FlowBoundsData`. The two dimensional cofactor converts the inverse Jacobian
to entries of the composed forward Jacobian, the material pullback identity
turns those entries into time derivatives, and App. B.3 transfers their
spatial estimates through the flow. -/
theorem c_material_goal_source_of_flow_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} {Cmat : ℝ} {m : ℕ}
    (hflow : FlowBoundsData D Φ hseq Cmat) (hm : 1 ≤ m) :
    MaterialGoalSource.CMaterialGoalSourceData D Φ hseq
      (materialFlowCompositionConstant α Cmat) m := by
  refine ⟨?_⟩
  intro s r hr n ell hnell i j x J
  let Q : Vec 2 → ℝ := fun y => constructionMaterialIterate
    (fun q z => streamVel (Φ m) (s + q) z) ell
    (fun q z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s q z
      (basisVec (1 - i)) (1 - j)) r
    (Section2FlowIdentities.constructionFlow D hseq m (s + r) y s)
  have hentry (y : Vec 2) :
      (fun q : ℝ => MaterialGoalSource.inverseJacobianPulledBack D hseq m s q y
        (basisVec j) i) =
      fun q => if i = j then
        Section2FlowIdentities.constructionFlowJacobian D hseq m q s y
          (basisVec (1 - i)) (1 - j)
      else -Section2FlowIdentities.constructionFlowJacobian D hseq m q s y
          (basisVec (1 - i)) (1 - j) := by
    funext q
    obtain ⟨h00, h10, h01, h11⟩ :=
      inverseJacobianPulledBack_cofactor_entries (D := D) (hseq := hseq) m s q y
    fin_cases i <;> fin_cases j <;>
      simp_all [Homogenization.basisVec]
  have htarget :
      (fun y : Vec 2 => iteratedTimeDerivative ell
        (fun q => MaterialGoalSource.inverseJacobianPulledBack D hseq m s q y
          (basisVec j) i) r) =
      fun y => if i = j then Q y else -Q y := by
    funext y
    have hc := congrArg
      (fun f : ℝ → ℝ => iteratedTimeDerivative ell f r) (hentry y)
    by_cases hij : i = j
    · have hpull := constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
        (D := D) (hseq := hseq) m s y (1 - j) (1 - i) ell r
      have hc' : iteratedTimeDerivative ell
          (fun q => MaterialGoalSource.inverseJacobianPulledBack D hseq m s q y
            (basisVec j) i) r =
          iteratedTimeDerivative ell
            (fun q => Section2FlowIdentities.constructionFlowJacobian D hseq m q s y
              (basisVec (1 - i)) (1 - j)) r := by
        simpa [hij] using hc
      simpa [hij, Q] using hc'.trans hpull.symm
    · have hpull := constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
        (D := D) (hseq := hseq) m s y (1 - j) (1 - i) ell r
      have hc' : iteratedTimeDerivative ell
          (fun q => MaterialGoalSource.inverseJacobianPulledBack D hseq m s q y
            (basisVec j) i) r =
          iteratedTimeDerivative ell
            (fun q => -Section2FlowIdentities.constructionFlowJacobian D hseq m q s y
              (basisVec (1 - i)) (1 - j)) r := by
        simpa [hij] using hc
      have hneg : iteratedTimeDerivative ell
          (fun q => -Section2FlowIdentities.constructionFlowJacobian D hseq m q s y
            (basisVec (1 - i)) (1 - j)) r = -Q y := by
        rw [iteratedTimeDerivative_neg_local]
        simpa [Q] using congrArg (fun z : ℝ => -z) hpull.symm
      simpa [hij, Q] using hc'.trans hneg
  have hbound := materialJacobianPullback_spatial_bound
    hflow hm s r hr ell n hnell (1 - j) (1 - i) x J
  rw [htarget]
  by_cases hij : i = j
  · simpa [hij, Q] using hbound
  · simp only [ite_eq_right hij]
    rw [norm_iteratedFDeriv_neg_local]
    simpa [Q, inv_pow] using hbound

end AVRegularity.Velocity.Port.MaterialFlowComposition
end

section
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Construction
open scoped ContDiff
namespace AVRegularity.Velocity.Port

/-! Per-scale assembly for the source-form Section 2 flow bounds. -/

/-- One scale of the source-form flow data used by Section 2 and Appendix B.
The fields retain the displayed bounds; only the scale index is fixed. -/
structure Section2FlowBoundsAtScale {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ) (Cmat : ℝ)
    (m : ℕ) : Prop where
  inverse_regbounds : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
    Section2FlowRegularityCore.flowJacobianBarNorm n (2 ^ 11 * (D.epsilon m)⁻¹)
      (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤
      ENNReal.ofReal (2 ^ 23 * |t| * D.velocityAmplitude m)
  flow_close : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ x : Vec 2,
      ‖Section2FlowIdentities.constructionFlowJacobian D hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * D.velocityAmplitude m ∧
      2 ^ 23 * |t| * D.velocityAmplitude m ≤ 1 / 4
  flow_jacobian_composed : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ,
    Section2FlowRegularityCore.flowJacobianBarNorm n (2 ^ 10 * (D.epsilon m)⁻¹)
      (fun x => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ →
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s t x)
  flow_jacobian : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    Section2FlowRegularityCore.flowJacobianBarNorm n (2 ^ 14 * (D.epsilon m)⁻¹)
      (Section2FlowIdentities.constructionFlowJacobian D hseq m t s) ≤ ENNReal.ofReal 12
  flow_higher_derivative : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        Section2FlowIdentities.constructionFlow D hseq m (s + t) y s)
        x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (D.epsilon m)⁻¹) ^ (n - 1)
  material_jacobian : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n ell : ℕ,
    n + ell ≤ AVenhance.Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
      ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * (D.epsilon m)⁻¹ ^ n *
              (D.epsilon m ^ (β - 2)) ^ ell
  material_jacobian_time_diff : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r x
          (basisVec j) i) t
  inverse_jacobian_time_diff : ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => Section2FlowIdentities.constructionFlowInvJacobian D hseq m r s x) t

/-- The spatial flow inputs for the material-Jacobian estimate follow from the
preceding Section 2 induction level. -/
theorem section2_spatial_flow_data_from_previous
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2Induction.Section2StreamInductionHypothesis D Φ (m - 1)) :
    MaterialFlowBounds.Section2SpatialFlowData D Φ hseq m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t ht x
    exact Section2FlowRegularityCore.section2_flow_close_from_previous
      D hseq happB2 m hm hprev s t ht x
  · intro s t ht n
    exact Section2FlowRegularityCore.section2_flow_jacobian_composed_from_previous
      D hseq happB2 m hm n hprev s t ht
  · intro s t ht
    exact Section2FlowRegularityCore.section2_composed_jacobian_smooth D hseq m s t
  · intro s t ht n hn x J
    exact Section2FlowHigherDerivative.section2_flow_higher_derivative_from_previous
      D hseq happB2 m hm n hn hprev s t ht x J

/-- Assemble the per-scale source flow fields from the preceding scale and
the material-Jacobian estimate. -/
theorem section2_flow_bounds_at_scale_from_previous
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
    (happB2 : RecursionIncrement.AppB2InverseFlowData D Φ hseq)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2Induction.Section2StreamInductionHypothesis D Φ (m - 1))
    (Cmat : ℝ)
    (hmaterial : ∀ s t : ℝ,
      |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ AVenhance.Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * (D.epsilon m)⁻¹ ^ n *
              (D.epsilon m ^ (β - 2)) ^ ell) :
    Section2FlowBoundsAtScale D Φ hseq Cmat m := by
  refine {
    inverse_regbounds := ?_
    flow_close := ?_
    flow_jacobian_composed := ?_
    composed_jacobian_smooth := ?_
    flow_jacobian := ?_
    flow_higher_derivative := ?_
    material_jacobian := hmaterial
    material_jacobian_time_diff := ?_
    inverse_jacobian_time_diff := ?_ }
  · intro s t ht n
    exact Section2FlowInverseBounds.section2_flow_inverse_regbounds_from_previous
      D hseq happB2 m hm hprev s t ht n
  · intro s t ht x
    exact Section2FlowRegularityCore.section2_flow_close_from_previous
      D hseq happB2 m hm hprev s t ht x
  · intro s t ht n
    exact Section2FlowRegularityCore.section2_flow_jacobian_composed_from_previous
      D hseq happB2 m hm n hprev s t ht
  · intro s t ht
    exact Section2FlowRegularityCore.section2_composed_jacobian_smooth D hseq m s t
  · intro s t ht n hn
    exact Section2FlowRegularityCore.section2_flow_jacobian_from_previous
      D hseq happB2 m hm n hn hprev s t ht
  · intro s t ht n hn x J
    exact Section2FlowHigherDerivative.section2_flow_higher_derivative_from_previous
      D hseq happB2 m hm n hn hprev s t ht x J
  · intro s t ht i j x
    exact Section2FlowRegularityCore.section2_material_jacobian_time_diff D hseq m s t i j x
  · intro s t x
    exact Section2FlowRegularityCore.section2_inverse_jacobian_time_diff D hseq m t s x

end AVRegularity.Velocity.Port
end
