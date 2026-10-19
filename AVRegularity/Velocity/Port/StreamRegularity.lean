-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.MaterialFlowTime
import AVenhance.Infra.Section4.Amnr.FlowMixedEstimate
public import AVRegularity.Velocity.Port.Section2FlowBoundsAtScale
public import AVenhance.Infra.Construction.MaterialPullback
public import AVenhance.Infra.Section4.Amnr.FlowJacobianC1
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.Laws
import AVenhance.Infra.Flow.StartTimeDerivative
import AVenhance.Infra.Section4.Amnr.MaterialCalculus
import AVenhance.Infra.Section4.Amnr.Seed
import AVenhance.Infra.Section4.Amnr.SpatialCommutator
import AVenhance.Infra.Section4.Amnr.SpatialOperatorBounds
import AVenhance.Infra.Section5.MatrixTransport
import AVenhance.Statements.FlowDefs.FlowInvRightInverse
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.Velocity.Port

/-! The material Jacobian field follows from the all-order velocity-gradient
jets and the spatial flow displays. -/

open AVenhance AVenhance.Infra.Construction AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.MaterialFlowBounds

open AVenhance.Infra.Section4

def MaterialJacobianFromP.materialTimeShift (s : ℝ) (z : AmnrSpace) : AmnrSpace :=
  ((s, (0 : Vec 2)) : AmnrSpace) + z

theorem MaterialJacobianFromP.amnrOp_timeShift {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (s : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Option (Fin 2)) (z : AmnrSpace) :
    amnrOp (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) d
      (fun y => f (MaterialJacobianFromP.materialTimeShift s y)) z =
        amnrOp b d f (MaterialJacobianFromP.materialTimeShift s z) := by
  let T := MaterialJacobianFromP.materialTimeShift s
  have hT : HasFDerivAt T (ContinuousLinearMap.id ℝ AmnrSpace) z := by
    have hid : HasFDerivAt (fun y : AmnrSpace => y)
        (ContinuousLinearMap.id ℝ AmnrSpace) z := hasFDerivAt_id z
    have h := hid.const_add ((s, (0 : Vec 2)) : AmnrSpace)
    have hfun : T = fun y : AmnrSpace => ((s, (0 : Vec 2)) : AmnrSpace) + y := by
      funext y
      simp [T, MaterialJacobianFromP.materialTimeShift]
    rw [hfun]
    exact h
  have hcomp := (hf.differentiable (by simp) (T z)).hasFDerivAt.comp z hT
  have hderiv : fderiv ℝ (f ∘ T) z = fderiv ℝ f (T z) := by
    simpa [Function.comp_def] using hcomp.fderiv
  have hdir : amnrDirection (fun y => b (T y)) d z =
      amnrDirection b d (T z) := by
    cases d <;> simp [amnrDirection, T]
  unfold amnrOp
  rw [show (fun y => f (T y)) = f ∘ T by rfl, hderiv, hdir]

theorem MaterialJacobianFromP.amnrWord_timeShift {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (s : ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Option (Fin 2))) :
    amnrWord (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) w
      (fun y => f (MaterialJacobianFromP.materialTimeShift s y)) =
        fun z => amnrWord b w f (MaterialJacobianFromP.materialTimeShift s z) := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      have htail : ContDiff ℝ (⊤ : ℕ∞) (amnrWord b w f) :=
        contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ
          hb.contDiffOn hf.contDiffOn w)
      funext z
      change amnrOp (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) d
        (amnrWord (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) w
          (fun y => f (MaterialJacobianFromP.materialTimeShift s y))) z = _
      rw [ih]
      exact MaterialJacobianFromP.amnrOp_timeShift s htail d z

theorem MaterialJacobianFromP.materialJacobianEntry_transport
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {D : JetRecursionData (β - 1) s q Λ ζ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (m : ℕ) (s : ℝ) (i j : Fin 2) :
    ∀ z : AmnrSpace,
      amnrOp (fun y => streamVel (Φ m) (s + y.1) y.2) none
        (fun y => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s y.1 y.2
          (basisVec j) i) z =
        ∑ q : Fin 2,
          Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s z.1 z.2
            (basisVec j) q *
          amnrVelocityGradient
            (fun y => streamVel (Φ m) (s + y.1) y.2) i q z := by
  let constructionFlow := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlow D hs k
  let constructionFlowInv := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlowInv D hs k
  let constructionFlowJacobian := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlowJacobian D hs k
  let constructionComposedFlowJacobian :=
    fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ) (k : ℕ) =>
      Section2FlowIdentities.constructionComposedFlowJacobian D hs k
  intro z
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let bshift : ℝ → Vec 2 → Vec 2 := fun r x => b (s + r) x
  let x₀ : Vec 2 := constructionFlowInv hseq m (s + z.1) z.2 s
  let X : ℝ → Vec 2 := fun r => constructionFlow hseq m (s + r) x₀ s
  let G : ℝ → Vec 2 → ℝ := fun r y =>
    constructionComposedFlowJacobian hseq m s r y (basisVec j) i
  let g : AmnrSpace → ℝ := fun y => G y.1 y.2
  have hφ : IsAdmissibleStream (Φ m) :=
    AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hfield : Infra.Flow.SmoothPeriodicField b := smoothPeriodic_streamVel hφ
  have hXflow : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hXderiv (r : ℝ) : HasDerivAt X (bshift r (X r)) r := by
    have hode := hXflow.2 x₀ s (r + s)
    have htime := hode.comp_add_const r s
    simpa [X, bshift, b, add_comm, add_left_comm, add_assoc] using htime
  have hXz : X z.1 = z.2 := by
    change constructionFlow hseq m (s + z.1)
      (constructionFlowInv hseq m (s + z.1) z.2 s) s = z.2
    exact flowInv_rightInverse b hφ.vel_continuous hφ.vel_lipschitz
      (s + z.1) s z.2
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar G) := by
    have h := MaterialPullback.constructionComposedFlowJacobian_joint_contDiff
      (D := D) (hseq := hseq) m s
    have hcol := h.clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : AmnrSpace => basisVec j))
    exact (contDiff_pi.1 hcol) i
  have hbshift : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector bshift) := by
    have hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b) := hfield.smooth
    have hb' : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => b y.1 y.2) := by
      convert hb using 1
      funext y
      rfl
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ × Vec 2 => b (s + y.1) y.2)
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => (s + y.1, y.2)) := by fun_prop
    exact hb'.comp hmap
  have hGslice : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar G) := hGsmooth
  have hmat := constructionMaterialDerivative_eq_deriv_pullback
    (b := bshift) (F := G) hGslice z.1 (hXderiv z.1)
  have hmaterial : constructionMaterialDerivative bshift G z.1 z.2 =
      amnrOp (constructionJointVector bshift) none (constructionJointScalar G) z := by
    rw [constructionMaterialDerivative_eq_joint_fderiv hGslice]
    rfl
  have hpullEq (r : ℝ) : G r (X r) =
      constructionFlowJacobian hseq m r s x₀ (basisVec j) i := by
    have hflowId : constructionFlowInv hseq m (s + r)
        (constructionFlow hseq m (s + r) x₀ s) s = x₀ := by
      calc
        _ = constructionFlow hseq m s
            (constructionFlow hseq m (s + r) x₀ s) (s + r) := rfl
        _ = constructionFlow hseq m s x₀ s := by
          exact Infra.Flow.flow_group_law b hφ.vel_lipschitz hXflow x₀ s (s + r) s
        _ = x₀ := hXflow.1 x₀ s
    have hflowId' : Section2FlowIdentities.constructionFlowInv D hseq m (s + r)
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) x₀ s) s = x₀ := by
      exact hflowId
    dsimp only [G, X, constructionComposedFlowJacobian,
      constructionFlow, constructionFlowInv, constructionFlowJacobian,
      Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowInv,
      Section2FlowIdentities.streamFlowInv,
      Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow,
      Section2FlowIdentities.constructionFlowJacobian,
      Section2FlowIdentities.streamFlowJacobian] at hflowId' ⊢
    rw [hflowId']
  have htimepull := MaterialPullback.constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
    (D := D) (hseq := hseq) m s x₀ i j 1 z.1
  have htimeDerivative : MaterialGoalSource.iteratedTimeDerivative 1
      (fun r => constructionFlowJacobian hseq m r s x₀ (basisVec j) i) z.1 =
      Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
        (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := by
    have hvar := amnrFlowJacobianEntry_hasDerivAt_time hfield hXflow s
      (s + z.1) x₀ j i
    have hvar' : HasDerivAt
        (fun r => amnrFlowJacobianEntry (constructionFlow hseq m) s j i (r, x₀))
        ((Infra.Flow.jointSpatialFDeriv b (s + z.1)
          (constructionFlow hseq m (s + z.1) x₀ s)
          (fderiv ℝ (fun y => constructionFlow hseq m (s + z.1) y s)
            x₀ (basisVec j))) i) (z.1 + s) := by
      convert hvar using 1; ring
    have hshifted := hvar'.comp_add_const z.1 s
    have hentry : (fun q : ℝ =>
        amnrFlowJacobianEntry (constructionFlow hseq m) s j i (q + s, x₀)) =
        fun q => constructionFlowJacobian hseq m q s x₀ (basisVec j) i := by
      funext q
      simp [amnrFlowJacobianEntry, constructionFlowJacobian, constructionFlow,
        Section2FlowIdentities.constructionFlowJacobian,
        Section2FlowIdentities.constructionFlow,
        Section2FlowIdentities.streamFlowJacobian,
        Section2FlowIdentities.streamFlow, add_comm]
    have hshifted' := hshifted.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => (congrFun hentry q).symm)
    have hpoint := hshifted'.deriv
    have hflowpt : constructionFlow hseq m (s + z.1) x₀ s = z.2 := by
      simpa [X] using hXz
    rw [hflowpt] at hpoint
    simpa [MaterialGoalSource.iteratedTimeDerivative, b, constructionFlowJacobian,
      constructionFlow,
      Section2FlowIdentities.constructionFlowJacobian,
      Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlowJacobian,
      Section2FlowIdentities.streamFlow,
      Infra.Flow.jointSpatialFDeriv, add_comm, add_left_comm] using hpoint
  have hderivpoint :
      constructionMaterialDerivative bshift G z.1 z.2 =
      Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
          (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := by
    calc
      constructionMaterialDerivative bshift G z.1 z.2 =
          constructionMaterialIterate bshift 1 G z.1 z.2 := rfl
      _ = MaterialGoalSource.iteratedTimeDerivative 1
          (fun r => constructionFlowJacobian hseq m r s x₀ (basisVec j) i) z.1 := by
        simpa [bshift, X, G, constructionFlow, constructionComposedFlowJacobian,
          MaterialGoalSource.iteratedTimeDerivative, hXz] using htimepull
      _ = Infra.Flow.jointSpatialFDeriv b (s + z.1) z.2
          (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i := htimeDerivative
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (b (s + z.1)) := by
    have hb : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry b) := hfield.smooth
    have hb' : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ × Vec 2 => b y.1 y.2) := by
      convert hb using 1
      funext y
      rfl
    have hm : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + z.1, y)) := by fun_prop
    exact hb'.comp hm
  have hcomponent := AVenhance.Infra.Section5.fderiv_vector_component_eq_sum_gradMatrix
    (F := fun y => b (s + z.1) y) (x := z.2)
    (v := constructionFlowJacobian hseq m z.1 s x₀ (basisVec j))
    (hslice.differentiable (by simp) z.2) i
  have hspatial := Infra.Flow.jointSpatialFDeriv_eq_slice hfield (s + z.1) z.2
  have hcolumn (q : Fin 2) :
      constructionFlowJacobian hseq m z.1 s x₀ (basisVec j) q =
        constructionComposedFlowJacobian hseq m s z.1 z.2 (basisVec j) q := by
    rfl
  change amnrOp (constructionJointVector bshift) none
    (constructionJointScalar G) z = _
  rw [← hmaterial, hderivpoint, hspatial]
  change fderiv ℝ (fun y => b (s + z.1) y) z.2
      (constructionFlowJacobian hseq m z.1 s x₀ (basisVec j)) i = _
  rw [hcomponent]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hcolumn q]
  rfl

theorem MaterialJacobianFromP.materialPureWord_eq_iterate
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (ell : ℕ) :
    amnrWord (constructionJointVector b) (List.replicate ell none)
      (constructionJointScalar F) =
        constructionJointScalar (constructionMaterialIterate b ell F) := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
      change amnrOp (constructionJointVector b) none
          (amnrWord (constructionJointVector b) (List.replicate ell none)
            (constructionJointScalar F)) =
        constructionJointScalar (constructionMaterialIterate b (ell + 1) F)
      rw [ih]
      funext p
      have hiterate := constructionMaterialIterate_joint_contDiff hb hF ell
      have hstep := constructionMaterialDerivative_eq_joint_fderiv
        (b := b) (F := constructionMaterialIterate b ell F) hiterate p.1 p.2
      change fderiv ℝ (constructionJointScalar
        (constructionMaterialIterate b ell F)) p
          (1, b p.1 p.2) = _
      simpa [constructionJointScalar, constructionJointVector,
        constructionMaterialIterate] using hstep.symm

theorem MaterialJacobianFromP.amnrVelocityGradient_timeShift
    {b : AmnrSpace → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (s : ℝ) (i p : Fin 2) (z : AmnrSpace) :
    amnrVelocityGradient (fun y => b (MaterialJacobianFromP.materialTimeShift s y)) i p z =
      amnrVelocityGradient b i p (MaterialJacobianFromP.materialTimeShift s z) := by
  let f : AmnrSpace → ℝ := fun y => b y i
  let bs : AmnrSpace → Vec 2 := fun y => b (MaterialJacobianFromP.materialTimeShift s y)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ i).comp hb
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (MaterialJacobianFromP.materialTimeShift s) := by
    fun_prop [MaterialJacobianFromP.materialTimeShift]
  have hbs : ContDiff ℝ (⊤ : ℕ∞) bs := hb.comp hmap
  have hshift := MaterialJacobianFromP.amnrOp_timeShift (b := b) s hf (some p) z
  have hdleft : DifferentiableAt ℝ (fun y => bs y i) z := by
    have hdvec : DifferentiableAt ℝ bs z := hbs.differentiable (by simp) z
    simpa only [Function.comp_def] using
      (differentiable_apply i).differentiableAt.comp z hdvec
  have hdright : DifferentiableAt ℝ f (MaterialJacobianFromP.materialTimeShift s z) := by
    have hdvec : DifferentiableAt ℝ b (MaterialJacobianFromP.materialTimeShift s z) :=
      hb.differentiable (by simp) (MaterialJacobianFromP.materialTimeShift s z)
    simpa only [Function.comp_def] using
      (differentiable_apply i).differentiableAt.comp (MaterialJacobianFromP.materialTimeShift s z) hdvec
  calc
    amnrVelocityGradient bs i p z = amnrOp bs (some p) (fun y => bs y i) z := by
      symm
      simpa [bs, amnrVelocityGradient] using amnrOp_space hdleft p
    _ = amnrOp b (some p) f (MaterialJacobianFromP.materialTimeShift s z) := hshift
    _ = amnrVelocityGradient b i p (MaterialJacobianFromP.materialTimeShift s z) := by
      simpa [f, amnrVelocityGradient] using amnrOp_space hdright p

def section2MaterialJacobianConstant (β K : ℝ) : ℝ :=
  (2 : ℝ) ^ (Nstar β + 1) *
    MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
      (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β

theorem section2MaterialJacobianConstant_ge_one {β K : ℝ} (hK : 1 ≤ K) :
    1 ≤ section2MaterialJacobianConstant β K := by
  have hpow2 : 1 ≤ (2 : ℝ) ^ (Nstar β + 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hspatial : 1 ≤ MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) := by
    unfold MaterialFlowBounds.section2MaterialSpatialConstant
    have hs : 0 ≤ ∑ q ∈ Finset.range (2 * Nstar β + 2),
        ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)) := by positivity
    linarith
  have hcoef : 1 ≤ 1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K := by
    have hp : 0 ≤ (2 : ℝ) ^ (2 * Nstar β + 2) * K := by positivity
    linarith
  have hpow : 1 ≤
      (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := one_le_pow₀ hcoef
  calc
    1 = (1 : ℝ) * 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
        MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
          (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by gcongr
    _ = section2MaterialJacobianConstant β K := rfl

/-- The material-Jacobian display follows from the all-order weighted
material gradient jets and the source spatial flow displays. -/
theorem section2_material_jacobian_of_material_levels
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {D : JetRecursionData (β - 1) s q Λ ζ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ} {K : ℝ}
    (hK : 1 ≤ K)
    (hlevels : MaterialAuxiliaryInduction.MaterialAuxJetLevels
      D Φ (2 * Nstar β + 1) K (Nstar β))
    {m : ℕ} (hflow : Section2SpatialFlowData D Φ hseq m) :
    ∀ s t : ℝ,
      |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
              (fun r z => streamVel (Φ m) (s + r) z) ell
              (fun r z => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r z
                (basisVec j) i) t y)
            x (fun k => basisVec (J k))‖ ≤
              section2MaterialJacobianConstant β K *
                (D.epsilon m)⁻¹ ^ n *
                (D.epsilon m ^ (β - 2)) ^ ell := by
  let constructionFlow := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlow D hs k
  let constructionFlowInv := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlowInv D hs k
  let constructionFlowJacobian := fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ)
      (k : ℕ) => Section2FlowIdentities.constructionFlowJacobian D hs k
  let constructionComposedFlowJacobian :=
    fun (hs : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ) (k : ℕ) =>
      Section2FlowIdentities.constructionComposedFlowJacobian D hs k
  intro s t ht n ell hnell i j x J
  let N := Nstar β
  let W := 2 * N + 1
  let S := (D.epsilon m)⁻¹
  let H := D.velocityAmplitude m
  let Cflow := MaterialFlowBounds.section2MaterialSpatialConstant W
  let R := 1 + (2 : ℝ) ^ (W + 1) * K
  let Cmat := section2MaterialJacobianConstant β K
  have hE : 0 < D.epsilon m := D.epsilon_pos m
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    exact (by rw [D.velocityAmplitude_eq]; positivity)
  have hN : 1 ≤ N := by
    dsimp [N]
    have hNstar : AVenhance.Nstar (1 + (β - 1)) = AVenhance.Nstar β := by
      congr 1
      ring
    rw [← hNstar]
    exact Nat.le_trans (by norm_num) D.nstar_ge_256
  have hnN : n ≤ N := by dsimp [N]; omega
  have hellN : ell ≤ N := by dsimp [N]; omega
  have hWbudget : n + 2 * ell ≤ W := by dsimp [W, N]; omega
  have ⟨hCflow, hspatial⟩ :=
    section2_material_jacobian_spatial_slice_of_flow_bounds
      (N := W) hflow
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hR : 1 ≤ R := by
    dsimp [R]
    have hprod : 0 ≤ (2 : ℝ) ^ (W + 1) * K := by positivity
    linarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRpow : ∀ r : ℕ, r ≤ N → R ^ r ≤ R ^ N := by
    intro r hr
    exact pow_le_pow_right₀ hR hr
  have hCmatGeOne : 1 ≤ Cmat := by
    have hpow2 : 1 ≤ (2 : ℝ) ^ (Nstar β + 1) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hpowR : 1 ≤
        (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
      apply one_le_pow₀
      have hcoef : 0 ≤ (2 : ℝ) ^ (2 * Nstar β + 2) * K := by positivity
      linarith
    have hcf : 1 ≤ MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) := by
      unfold MaterialFlowBounds.section2MaterialSpatialConstant
      have hs : 0 ≤ ∑ q ∈ Finset.range (2 * Nstar β + 2),
          ((↑q.factorial : ℝ) * (2 : ℝ) ^ (10 * q)) := by positivity
      linarith
    have hprod : (1 : ℝ) * 1 * 1 ≤
        (2 : ℝ) ^ (Nstar β + 1) *
          MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
            (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
      calc
        _ ≤ (2 : ℝ) ^ (Nstar β + 1) * 1 * 1 := by gcongr
        _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
              MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) * 1 := by gcongr
        _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
              MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
                (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by gcongr
    simpa [Cmat, section2MaterialJacobianConstant] using hprod
  have hb0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ m) z.1 z.2) :=
    (smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m)).smooth
  let b0 : AmnrSpace → Vec 2 := fun z => streamVel (Φ m) z.1 z.2
  let bshift : ℝ → Vec 2 → Vec 2 := fun r y => streamVel (Φ m) (s + r) y
  let bAmnr : AmnrSpace → Vec 2 := fun z => b0 (MaterialJacobianFromP.materialTimeShift s z)
  have hbAmnr : ContDiff ℝ (⊤ : ℕ∞) bAmnr := by
    dsimp [bAmnr, b0]
    exact hb0.comp (by fun_prop [MaterialJacobianFromP.materialTimeShift])
  have hbshiftEq : bAmnr = constructionJointVector bshift := by
    funext z
    simp [bAmnr, b0, constructionJointVector, bshift,
      MaterialJacobianFromP.materialTimeShift, add_comm]
  have hbAmnrEq : bAmnr = fun y => streamVel (Φ m) (s + y.1) y.2 := by
    funext z
    simp [bAmnr, b0, MaterialJacobianFromP.materialTimeShift]
  let G : Fin 2 → AmnrSpace → ℝ := fun p z =>
    constructionComposedFlowJacobian hseq m s z.1 z.2 (basisVec j) p
  have hG : ∀ p : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (G p) := by
    intro p
    have hmatrix := MaterialPullback.constructionComposedFlowJacobian_joint_contDiff
      (D := D) (hseq := hseq) m s
    have hcolumn := hmatrix.clm_apply
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : AmnrSpace => basisVec j))
    have hentry := (contDiff_pi.1 hcolumn) p
    simpa [G] using hentry
  have htransport : ∀ p z, amnrOp bAmnr none (G p) z =
      ∑ q : Fin 2, G q z * amnrVelocityGradient bAmnr p q z := by
    intro p z
    have hh := MaterialJacobianFromP.materialJacobianEntry_transport
      (D := D) (hseq := hseq) m s p j z
    rw [hbAmnrEq]
    simpa [G, constructionJointVector, bshift, add_comm] using hh
  have hgradSmooth : ∀ p q : Fin 2,
      ContDiff ℝ (⊤ : ℕ∞) (amnrVelocityGradient b0 p q) := by
    intro p q
    exact contDiffOn_univ.mp
      (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb0.contDiffOn p q)
  have hgradShift (p q : Fin 2) :
      amnrVelocityGradient bAmnr p q =
        fun z => amnrVelocityGradient b0 p q (MaterialJacobianFromP.materialTimeShift s z) := by
    funext z
    exact MaterialJacobianFromP.amnrVelocityGradient_timeShift hb0 s p q z
  have hBb : ∀ p q w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ W →
      |amnrWord bAmnr w (amnrVelocityGradient bAmnr p q) (t, x)| ≤
        K * H * amnrWeight S H w := by
    intro p q w hw hbudget
    obtain ⟨α, r, rfl⟩ := hw.normalForm
    have hbudget' : α.length + 2 * r + 2 ≤ W := by
      rw [amnrMixedWord_budget] at hbudget
      omega
    have hr : r ≤ N := by omega
    have hWordShift := MaterialJacobianFromP.amnrWord_timeShift (b := b0) s hb0 (hgradSmooth p q)
      (amnrMixedWord α r)
    have hlevel := hlevels.gradient m α r hr hbudget' p q
      (MaterialJacobianFromP.materialTimeShift s (t, x))
    have hwordEq : amnrWord bAmnr (amnrMixedWord α r)
        (amnrVelocityGradient bAmnr p q) (t, x) =
        amnrWord b0 (amnrMixedWord α r)
          (amnrVelocityGradient b0 p q) (MaterialJacobianFromP.materialTimeShift s (t, x)) := by
      rw [hgradShift]
      simpa [bAmnr, b0, MaterialJacobianFromP.materialTimeShift] using congrFun hWordShift (t, x)
    rw [hwordEq]
    have hweight : amnrWeight S H (amnrMixedWord α r) = S ^ α.length * H ^ r := by
      simp [amnrWeight, amnrMixedWord, S, H, Function.comp_def,
        List.map_append, List.map_replicate, List.prod_append,
        List.prod_replicate, inv_pow]
    rw [hweight]
    simpa [S, H, inv_pow, mul_assoc, mul_left_comm, mul_comm] using hlevel
  have hGb : ∀ p (η : List (Fin 2)), η.length ≤ W →
      |amnrWord bAmnr (η.map some) (G p) (t, x)| ≤ Cflow * S ^ η.length := by
    intro p η hη
    let f : Vec 2 → ℝ := fun y => G p (t, y)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := (hG p).comp (by fun_prop)
    rw [amnrWord_spatial_slice (hG p) bAmnr η]
    change |amnrSpaceWord η f x| ≤ Cflow * S ^ η.length
    rw [amnrSpaceWord_eq_iteratedFDeriv hf η, amnrSpatialDirections_eq]
    have hpoint := hspatial s t ht η.length hη p j x
      (fun k => amnrSpatialIndices η k)
    simpa [f, S, G, constructionComposedFlowJacobian, Real.norm_eq_abs] using hpoint
  have hGjoint : ∀ p : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (fun r y => G p (r, y))) := by
    intro p
    change ContDiff ℝ (⊤ : ℕ∞) (G p)
    exact hG p
  have hbshift : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector bshift) := by
    rw [← hbshiftEq]
    exact hbAmnr
  have hIterSmooth (p : Fin 2) (r : ℕ) :
      ContDiff ℝ (⊤ : ℕ∞)
        (constructionJointScalar
          (constructionMaterialIterate bshift r (fun q y => G p (q, y)))) :=
    constructionMaterialIterate_joint_contDiff hbshift (hGjoint p) r
  have htargetWord (p : Fin 2) (α : List (Fin 2)) :
      amnrWord bAmnr (amnrMixedWord α ell) (G p) (t, x) =
        amnrSpaceWord α
          (fun y => constructionMaterialIterate bshift ell
            (fun q z => G p (q, z)) t y) x := by
    rw [hbshiftEq]
    simp only [amnrMixedWord]
    have hpure := MaterialJacobianFromP.materialPureWord_eq_iterate hbshift (hGjoint p) ell
    have hGpeq : G p = constructionJointScalar (fun q y => G p (q, y)) := by
      funext z
      rfl
    have hpure' : amnrWord (constructionJointVector bshift)
        (List.replicate ell none) (G p) =
        constructionJointScalar
          (constructionMaterialIterate bshift ell (fun q y => G p (q, y))) := by
      rw [← hGpeq] at hpure
      exact hpure
    rw [amnrWord_append, hpure']
    have hslice := amnrWord_spatial_slice (hIterSmooth p ell)
      (constructionJointVector bshift) α
    simpa [constructionJointScalar] using congrFun hslice (t, x)
  have hWbound := amnr_flow_mixed_abs_le_of_primitive_jets
    hbAmnr G hG htransport hS hH (le_trans (by norm_num) hCflow) hK0
    (t, x) hGb hBb
    (List.ofFn J) ell (by simpa [N, W] using hWbudget) i
  have hconst :
      (2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell ≤ Cmat := by
    have hpow2 : (2 : ℝ) ^ ((List.ofFn J).length + 1) ≤ (2 : ℝ) ^ (N + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      simp only [List.length_ofFn]
      exact Nat.add_le_add_right hnN 1
    have hpowR' := hRpow ell hellN
    calc
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
          MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
            (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ ell := by
        calc
          _ ≤ (2 : ℝ) ^ (N + 1) * Cflow * R ^ ell := by
            gcongr
          _ = (2 : ℝ) ^ (Nstar β + 1) *
              MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
                (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ ell := by
            simp [N, Cflow, W, R]
      _ ≤ (2 : ℝ) ^ (Nstar β + 1) *
          MaterialFlowBounds.section2MaterialSpatialConstant (2 * Nstar β + 1) *
            (1 + (2 : ℝ) ^ (2 * Nstar β + 2) * K) ^ Nstar β := by
        exact mul_le_mul_of_nonneg_left hpowR' (by positivity)
      _ = Cmat := by simp [Cmat, section2MaterialJacobianConstant]
  have htargetBound :
      |amnrWord bAmnr (amnrMixedWord (List.ofFn J) ell) (G i) (t, x)| ≤
        Cmat * S ^ n * H ^ ell := by
    calc
      _ ≤ (2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell *
          S ^ (List.ofFn J).length * H ^ ell := by
        simpa [R, S, H, W] using hWbound
      _ = ((2 : ℝ) ^ ((List.ofFn J).length + 1) * Cflow * R ^ ell) *
          (S ^ (List.ofFn J).length * H ^ ell) := by ring
      _ ≤ Cmat * (S ^ (List.ofFn J).length * H ^ ell) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = Cmat * S ^ n * H ^ ell := by simp [List.length_ofFn]; ring
  have htarget := htargetWord i (List.ofFn J)
  have hslice : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => constructionMaterialIterate bshift ell
        (fun q z => G i (q, z)) t y) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact (hIterSmooth i ell).comp hmap
  have hderivWord := amnrSpaceWord_ofFn_eq_iteratedFDeriv hslice n J
  rw [htarget, hderivWord] at htargetBound
  have hHdef : H = D.epsilon m ^ (β - 2) := by
    dsimp [H]
    rw [D.velocityAmplitude_eq]
    congr 1
    ring
  simpa [Real.norm_eq_abs, S, H, hHdef, Cmat,
    section2MaterialJacobianConstant] using htargetBound

end AVRegularity.Velocity.Port
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Construction
open AVRegularity.Velocity.Port
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.MaterialAuxiliaryInduction
open AVRegularity.Velocity.Port.MaterialFlowBounds
open AVRegularity.Velocity.Port.MaterialFlowComposition
open AVRegularity.Velocity.Port.MaterialGoalSource
open AVRegularity.Velocity.Port.RecursionIncrement
namespace AVRegularity.Velocity.Port.Section2FlowBridge

/-! Bridges from the global source-form flow package to the per-scale
hypotheses consumed by the Section 2 induction. -/

private theorem high_order_radius_transfer {E a α : ℝ} {n : ℕ}
    {f : Vec 2 → ℝ} (he : 0 < E) (hn : 2 ≤ n)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hscale : a * E ^ 2 = E ^ (1 + α))
    (hsource : AVenhance.barNorm n ((2 : ℝ) ^ 7 * E⁻¹) f ≤
      ENNReal.ofReal (20 * E ^ (1 + α))) :
    AVenhance.barNorm n ((2 : ℝ) ^ 8 * E⁻¹) f ≤
      ENNReal.ofReal (32 * a * E ^ 2 * Section2JointInduction.section2Weight n) := by
  have hE : 0 < E := he
  have hRsource : 0 < (2 : ℝ) ^ 7 * E⁻¹ := by positivity
  have hRtarget : 0 < (2 : ℝ) ^ 8 * E⁻¹ := by positivity
  have hratio : ((2 : ℝ) ^ 7 * E⁻¹) / ((2 : ℝ) ^ 8 * E⁻¹) = 1 / 2 := by
    field_simp [ne_of_gt hE]
  have hΦsmoothN : ContDiff ℝ n f := hf.of_le (by simp)
  have hchange := ExplicitBarNorm.barNorm_radius_change
    hΦsmoothN hRsource hRtarget
  have hweight := Section2JointInduction.section2_weight_half_power n hn
  have hweight_nonneg : 0 ≤ Section2JointInduction.section2Weight n := by
    dsimp [Section2JointInduction.section2Weight]
    positivity
  have hcoef : 20 * (1 / 2 : ℝ) ^ n ≤
      32 * Section2JointInduction.section2Weight n := by
    have hnidx : n = (n - 2) + 2 := by omega
    have hpow : (1 / 2 : ℝ) ^ n =
        (1 / 2 : ℝ) ^ (n - 2) * (1 / 2 : ℝ) ^ 2 := by
      calc
        (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ ((n - 2) + 2) := by
          congr 1
        _ = (1 / 2 : ℝ) ^ (n - 2) * (1 / 2 : ℝ) ^ 2 := by rw [pow_add]
    calc
      20 * (1 / 2 : ℝ) ^ n = 5 * (1 / 2 : ℝ) ^ (n - 2) := by
        rw [hpow]
        ring
      _ ≤ 15 * Section2JointInduction.section2Weight n := by
        simpa only [← mul_assoc, show (5 : ℝ) * 3 = 15 by norm_num] using
          mul_le_mul_of_nonneg_left hweight (by norm_num : (0 : ℝ) ≤ 5)
      _ ≤ 32 * Section2JointInduction.section2Weight n :=
        mul_le_mul_of_nonneg_right (by norm_num) hweight_nonneg
  have hpower_nonneg : 0 ≤ E ^ (1 + α) := Real.rpow_nonneg hE.le _
  change AVenhance.barNorm n ((2 : ℝ) ^ 8 * E⁻¹) f ≤
    ENNReal.ofReal (32 * a * E ^ 2 *
      Section2JointInduction.section2Weight n)
  rw [hchange, hratio]
  calc
    AVenhance.barNorm n ((2 : ℝ) ^ 7 * E⁻¹) f *
        ENNReal.ofReal (1 / 2 : ℝ) ^ n ≤
      ENNReal.ofReal (20 * E ^ (1 + α)) * ENNReal.ofReal (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hsource (by positivity)
    _ = ENNReal.ofReal (20 * E ^ (1 + α) * (1 / 2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal
        (32 * E ^ (1 + α) * Section2JointInduction.section2Weight n) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        20 * E ^ (1 + α) * (1 / 2 : ℝ) ^ n =
            E ^ (1 + α) * (20 * (1 / 2 : ℝ) ^ n) := by ring
        _ ≤ E ^ (1 + α) * (32 * Section2JointInduction.section2Weight n) :=
          mul_le_mul_of_nonneg_left hcoef hpower_nonneg
        _ = 32 * E ^ (1 + α) * Section2JointInduction.section2Weight n := by ring
    _ = ENNReal.ofReal
        (32 * a * E ^ 2 *
          Section2JointInduction.section2Weight n) := by
      rw [← hscale]
      congr 1
      ring

/-- The full source spatial stream package follows from its first increment
display by summing the source scale recurrence. -/
theorem stream_regularity_bounds_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hinc : StreamIncrementBounds D Φ) :
    OCStreamRegularityBounds D (11 + 768 / α) Φ := by
  have hΦzero : ∀ t x, Φ 0 t x = 0 := by
    intro t x
    have hzero := hseq.1
    change Φ 0 = (fun _ _ => 0) at hzero
    exact congrFun (congrFun hzero t) x
  have hΦsmooth : ∀ m t, ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
    intro m t
    exact (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1.comp
      (contDiff_const.prodMk contDiff_id)
  intro m hm t
  refine ⟨?_, ?_, ?_⟩
  · exact hinc m hm t
  · intro n hn
    have hscale : D.velocityAmplitude m * D.epsilon m ^ 2 =
        D.epsilon m ^ (1 + α) := by
      rw [D.velocityAmplitude_eq, ← Real.rpow_natCast,
        ← Real.rpow_add (D.epsilon_pos m)]
      congr 1
      ring
    have h := high_order_radius_transfer (D.epsilon_pos m) hn (hΦsmooth m t)
      hscale (Section2Induction.high_order_stream_bound_of_increment_bounds
        D hΦzero hΦsmooth hinc m t n hn)
    simpa only [Section2JointInduction.section2Weight,
      show (2 : ℝ) ^ 5 = 32 by norm_num] using h
  · intro n hn
    exact Section2Induction.low_order_stream_bounds_of_increment_bounds
      D hseq hinc m t n hn

/-- The time-transport identity for the inverse flow, copied from the
generic source proof with the local flow aliases substituted. -/
theorem constructionFlowInv_hasDerivAt
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (t s : ℝ) (x : Vec 2) :
    HasDerivAt
      (fun r : ℝ => Section2FlowIdentities.constructionFlowInv D hseq m r x s)
      (-(Section2FlowIdentities.constructionFlowInvJacobian D hseq m (t - s) s x)
        (streamVel (Φ m) t x)) t := by
  let hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b :=
    AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow b (Section2FlowIdentities.constructionFlow D hseq m) := by
    dsimp [b, Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hstart := Infra.Flow.flow_initialTime_hasDerivAt hb hX x t s
  simpa [Section2FlowIdentities.constructionFlowInv,
    Section2FlowIdentities.streamFlowInv,
    Section2FlowIdentities.constructionFlowInvJacobian,
    Section2FlowIdentities.streamFlowInvJacobian,
    Section2FlowIdentities.constructionFlow,
    Section2FlowIdentities.streamFlow, flowInv, sub_add_cancel] using hstart

/-- The material-Jacobian display at one scale follows from the actual
all-order velocity material jets and the spatial displays at that scale. -/
theorem section2_flow_bounds_at_scale_from_induction
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : AppB2InverseFlowData D Φ hseq)
    (hind : ∀ m : ℕ, Section2StreamInductionHypothesis D Φ m)
    {K : ℝ} (hK : 1 ≤ K)
    (hlevels : MaterialAuxJetLevels D Φ
      (2 * Nstar β + 1) K (Nstar β))
    (m : ℕ) (hm : 1 ≤ m) :
    Section2FlowBoundsAtScale (β := β) D Φ hseq (section2MaterialJacobianConstant β K) m := by
  have hspatial := section2_spatial_flow_data_from_previous
    D hseq happB2 m hm (hind (m - 1))
  have hmaterial := section2_material_jacobian_of_material_levels
    (β := β) (D := D) (hseq := hseq) hK hlevels hspatial
  exact section2_flow_bounds_at_scale_from_previous (β := β)
    D hseq happB2 m hm (hind (m - 1))
    (section2MaterialJacobianConstant β K) hmaterial

/-- Assemble `FlowBoundsData` from the same induction that proves the first
stream-regularity increment display. In particular, each positive-scale
material field is derived from the previous scale's stream induction
hypothesis. -/
theorem section2_flow_bounds_of_stream_induction
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : AppB2InverseFlowData D Φ hseq)
    (hind : ∀ m : ℕ, Section2StreamInductionHypothesis D Φ m)
    (hincrement : StreamIncrementBounds D Φ) :
    ∃ Cmat : ℝ, 1 ≤ Cmat ∧ FlowBoundsData D Φ hseq Cmat := by
  let Creg := 11 + 768 / (β - 1)
  have hreg : OCStreamRegularityBounds D Creg Φ := by
    simpa [Creg] using stream_regularity_bounds_of_increment_bounds D hseq hincrement
  obtain ⟨K, hK, hlevels⟩ :=
    MaterialAuxiliaryInduction.material_aux_jet_levels_all_orders_of_A3 D hseq hreg
  let Cmat := section2MaterialJacobianConstant β K
  have hCmat : 1 ≤ Cmat := by
    dsimp [Cmat]
    exact section2MaterialJacobianConstant_ge_one hK
  have hflow : FlowBoundsData D Φ hseq Cmat := by
    refine ⟨hCmat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm s t ht n
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).inverse_regbounds s t ht n
    · intro m hm s t ht x
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).flow_close s t ht x
    · intro m hm s t ht n
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).flow_jacobian_composed s t ht n
    · intro m hm s t ht
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).composed_jacobian_smooth s t ht
    · intro m hm s t ht n hn
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).flow_jacobian s t ht n hn
    · intro m hm s t ht n hn x J
      exact (section2_flow_bounds_at_scale_from_induction D happB2 hind
        hK hlevels m hm).flow_higher_derivative s t ht n hn x J
    · intro m hm s t ht n ell hnell i j x J
      simpa only [Cmat, add_sub_cancel] using
        (section2_flow_bounds_at_scale_from_induction D happB2 hind
          hK hlevels m hm).material_jacobian s t ht n ell
            (by simpa only [add_sub_cancel] using hnell) i j x J
    · intro m hm s t ht i j x
      exact Section2FlowRegularityCore.section2_material_jacobian_time_diff
        D hseq m s t i j x
    · intro m hm s t x
      exact Section2FlowRegularityCore.section2_inverse_jacobian_time_diff
        D hseq m t s x
    · intro m hm t s x
      exact constructionFlowInv_hasDerivAt D hseq m t s x
  exact ⟨Cmat, hCmat, hflow⟩

/-- The joint induction now proves both `e.indyhyp` and the global source-form
flow/material package, with no full per-scale hypothesis assumed. -/
theorem section2_joint_induction_with_derived_flow
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ}
    (happB2 : AppB2InverseFlowData D Φ hseq) :
    (∀ m : ℕ, Section2StreamInductionHypothesis D Φ m) ∧
      StreamIncrementBounds D Φ ∧
      (∃ Cmat : ℝ, 1 ≤ Cmat ∧ FlowBoundsData D Φ hseq Cmat ∧
        (∀ m : ℕ, 1 ≤ m →
          CMaterialGoalSourceData D Φ hseq
            (MaterialFlowComposition.materialFlowCompositionConstant (β - 1) Cmat) m)) := by
  obtain ⟨hind, hincrement⟩ := section2_joint_induction D happB2
  obtain ⟨Cmat, hCmat, hflow⟩ :=
    section2_flow_bounds_of_stream_induction D happB2 hind hincrement
  exact ⟨hind, hincrement, Cmat, hCmat, hflow,
    fun m hm => MaterialFlowComposition.c_material_goal_source_of_flow_bounds hflow hm⟩

end AVRegularity.Velocity.Port.Section2FlowBridge
end
end
end

section
@[expose] public section
open Homogenization
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.RecursionIncrement
open AVRegularity.Velocity.Port.Section2JointInduction
open AVRegularity.Velocity.Port.Section2FlowBridge
open AVRegularity.Velocity.Port.AppB2Smoothness
namespace AVRegularity.Velocity.Port.StreamRegularity

/-! Section 2 stream regularity for the OC recursion data. -/

/-- Conditional stream regularity from the derived increment display. -/
theorem stream_regularity_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hinc : StreamIncrementBounds D Φ) :
    OCStreamRegularityBounds D (11 + 768 / α) Φ :=
  stream_regularity_bounds_of_increment_bounds D hseq hinc

/-- App. B.2 and the source recurrence prove the stream increments. -/
theorem stream_increment_bounds_of_appB2
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ}
    (happB2 : AppB2InverseFlowData D Φ hseq) :
    StreamIncrementBounds D Φ := by
  generalize hβ : α + 1 = β
  have hα : α = β - 1 := by linarith
  subst α
  exact (section2_joint_induction D happB2).2

/-- The smooth periodic flow theorem discharges the App. B.2 input. -/
theorem stream_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) :
    StreamIncrementBounds D Φ :=
  stream_increment_bounds_of_appB2 D
    (appB2InverseFlowData_of_smoothPeriodicFlow D hseq)

/-- All three spatial stream displays, with the inverse-flow input proved. -/
theorem stream_regularity
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ) :
    OCStreamRegularityBounds D (11 + 768 / α) Φ :=
  stream_regularity_of_increment_bounds D hseq (stream_increment_bounds D hseq)

/-- The same induction produces the global flow/material package. -/
theorem section2_induction_outputs_from_source_data
    {β s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData (β - 1) s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq (β - 1) q Λ ζ Φ) :
    OCStreamRegularityBounds D (11 + 768 / (β - 1)) Φ ∧
      ∃ Cmat : ℝ, 1 ≤ Cmat ∧
        MaterialFlowBounds.FlowBoundsData D Φ hseq Cmat := by
  have happB2 := appB2InverseFlowData_of_smoothPeriodicFlow D hseq
  obtain ⟨_, hincrement, Cmat, hCmat, hflow, _⟩ :=
    section2_joint_induction_with_derived_flow D happB2
  exact ⟨stream_regularity_of_increment_bounds D hseq hincrement,
    Cmat, hCmat, hflow⟩

end AVRegularity.Velocity.Port.StreamRegularity
end
end
