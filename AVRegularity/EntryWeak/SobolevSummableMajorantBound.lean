-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.SobolevCellFourier
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
public import AVRegularity.Velocity.Port.MaterialGoalSource
import AVRegularity.Velocity.Port.StreamRegularity
import Mathlib.Analysis.Normed.Group.Tannery

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Transverse shear maps preserve the determinant exactly. -/

theorem transverse_shear_jacobian_det_one (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (i : Fin 2) (x : Vec 2) :
    (jacMatrix (fun y => y + f (y i) • basisVec i.rev) x).det = 1 := by
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hpf := (hf (x i)).hasFDerivAt.comp x P.hasFDerivAt
  have hfull := (hasFDerivAt_id x).add (hpf.smul_const (basisVec i.rev))
  have hder : fderiv ℝ (fun y : Vec 2 => y + f (y i) • basisVec i.rev) x =
      ContinuousLinearMap.id ℝ (Vec 2) +
        ((fderiv ℝ f (x i)).comp P).smulRight (basisVec i.rev) := by
    simpa only [Function.comp_def, Pi.add_def, id_eq, P, ContinuousLinearMap.proj_apply] using hfull.fderiv
  simp only [Matrix.det_fin_two, jacMatrix, Matrix.of_apply, hder]
  fin_cases i <;> simp [P, basisVec, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped Classical
namespace AVRegularity.EntryWeakProofs

/-! Restrict a genuine window source to a measurable time window without spending spatial reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def timeWindowSource (I : Set ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (t : ℝ) (z Y : Vec 2) : E := if t ∈ I then f t z Y else 0

def windowJointSourceReserve (H : ℕ) (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hr : ∀ t ∈ I, ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2))
    (hp : ∀ t ∈ I, ∀ Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (hm : ∀ Y, Measurable (fun X : ℝ × Vec 2 => f X.1 X.2 Y))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ H → ∀ t ∈ I, ∀ X : Vec 2 × Vec 2,
      ‖iteratedFDeriv ℝ n (fun U : Vec 2 × Vec 2 => f t U.1 U.2) X‖ ≤ B n) :
    JointSourceReserve H (timeWindowSource I f) where
  regular t := by
    by_cases ht : t ∈ I
    · simpa only [timeWindowSource, ite_eq_left ht] using hr t ht
    · simpa only [timeWindowSource, ite_eq_right ht] using
        (contDiff_const : ContDiff ℝ (H : ℕ∞) (fun _ : Vec 2 × Vec 2 => (0 : E)))
  periodic t Y := by
    by_cases ht : t ∈ I
    · simpa only [timeWindowSource, ite_eq_left ht] using hp t ht Y
    · intro v z
      simp only [timeWindowSource, ite_eq_right ht]
  measurable Y := by
    exact (hm Y).ite (hI.preimage measurable_fst) measurable_const
  budget := B
  budget_nonneg := hB
  derivative_bound n hn t X := by
    by_cases ht : t ∈ I
    · simpa only [timeWindowSource, ite_eq_left ht] using hb n hn t ht X
    · simpa only [timeWindowSource, ite_eq_right ht, iteratedFDeriv_fun_zero,
        Pi.zero_apply, norm_zero] using hB n

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat AVenhance.Infra.Torus
namespace AVRegularity.EntryWeakProofs

/-! A fixed measurable classical readout of a cell L² trace. -/

def cellClassicalLift (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) : Vec 2 → ℝ :=
  fun x => (∑' k : Frequency, cellFourierCoeffCLM k u • torusCharacter (-k) x).re

theorem cellClassicalLift_eq (K : ℕ) (f : TorusHk K ℝ) :
    cellClassicalLift (complexifyCellClass (f.val (valueIndex2 K))) = realClassicalLift K f := by
  funext x
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  rw [← realJetFourier_eq_cellCoeff K f (valueIndex2 K) k]
  rfl

theorem cellClassicalLift_contDiff (K r : ℕ) (hr : r + 2 ≤ K) (f : TorusHk K ℝ) :
    ContDiff ℝ (r : ℕ∞) (cellClassicalLift (complexifyCellClass (f.val (valueIndex2 K)))) := by
  rw [cellClassicalLift_eq]
  exact realClassicalLift_contDiff K r hr f

theorem cellClassicalLift_periodic (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    AVenhance.IsZ2Periodic (cellClassicalLift u) := by
  intro n x
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  exact congrArg (fun z : ℂ => cellFourierCoeffCLM k u • z) (torusCharacter_periodic (-k) n x)

theorem cellClassicalLift_joint_measurable (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hu : Continuous u) : Measurable (fun p : ℝ × Vec 2 => cellClassicalLift (u p.1) p.2) := by
  apply Complex.reCLM.continuous.measurable.comp
  apply Measurable.tsum
  intro k
  exact (((cellFourierCoeffCLM k).continuous.comp hu).measurable.comp measurable_fst).smul
    ((torusCharacter_contDiff (-k)).continuous.measurable.comp measurable_snd)

theorem cellClassicalLift_value_ae (K : ℕ) (hK : 2 ≤ K) (f : TorusHk K ℝ) :
    (fun x => (cellClassicalLift (complexifyCellClass (f.val (valueIndex2 K))) x : ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] complexifyCellClass (f.val (valueIndex2 K)) := by
  rw [cellClassicalLift_eq]
  exact ((realClassicalLift_value_ae K hK f).fun_comp Complex.ofReal).trans
    (ContinuousLinearMap.coeFn_compLpL (L := Complex.ofRealCLM) (f.val (valueIndex2 K))).symm

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! A smooth slow cutoff converts genuine carrier-local bounds into a global forcing reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def cutoffSourceReserve (H : ℕ) (U : Set (Vec 2)) (hU : IsOpen U)
    (χ : Vec 2 → ℝ) (hs : tsupport χ ⊆ U)
    (Qχ : JointSourceReserve H (fun _ _ Y => χ Y))
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t, ContDiffOn ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2) {X | X.2 ∈ U})
    (hp : ∀ t Y, Y ∈ U → AVenhance.IsZ2Periodic (fun z => f t z Y))
    (hm : ∀ Y ∈ U, Measurable (fun Z : ℝ × Vec 2 => f Z.1 Z.2 Y))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n ≤ H, ∀ (t : ℝ) (X : Vec 2 × Vec 2), X.2 ∈ U →
      ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖ ≤ B n) :
    JointSourceReserve H (cutoffSource χ f) where
  regular t := cutoffSource_joint_contDiff H U hU χ
    ((Qχ.regular 0).comp₂ (contDiff_const (c := (0 : Vec 2))) contDiff_id) hs f hf t
  periodic t Y k z := by
    by_cases hY : Y ∈ U
    · exact congrArg (fun e : E => χ Y • e) (hp t Y hY k z)
    · have hz : χ Y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hY (hs hh))
      simp only [cutoffSource, hz, zero_smul]
  measurable Y := by
    by_cases hY : Y ∈ U
    · exact (hm Y hY).const_smul (χ Y)
    · have hz : χ Y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hY (hs hh))
      simp only [cutoffSource, hz, zero_smul]
      exact measurable_const
  budget n := ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ *
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Qχ.budget i * B (n - i)
  budget_nonneg n := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Qχ.budget_nonneg i)) (hB _))
  derivative_bound n hn t X := by
    by_cases hX : X.2 ∈ U
    · let V : Set (Vec 2 × Vec 2) := {Z | Z.2 ∈ U}
      have ho : IsOpen V := hU.preimage continuous_snd
      let T : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
      have hh := T.norm_iteratedFDerivWithin_le_of_bilinear
        (Qχ.regular t).contDiffOn (hf t) ho.uniqueDiffOn hX (by exact_mod_cast hn)
      rw [← iteratedFDerivWithin_of_isOpen n ho hX]
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      apply Finset.sum_le_sum
      intro i hi
      have hiH : i ≤ H := by have := Finset.mem_range.mp hi; omega
      have hni : n - i ≤ H := by omega
      have hc := Qχ.derivative_bound i hiH t X
      have hf' := hb (n - i) hni t X hX
      rw [← iteratedFDerivWithin_of_isOpen i ho hX] at hc
      rw [← iteratedFDerivWithin_of_isOpen (n - i) ho hX] at hf'
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
        hf' (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Qχ.budget_nonneg i))
    · have hz := cutoffSource_eventually_zero χ f t X (fun hh => hX (hs hh))
      rw [(hz.iteratedFDeriv ℝ n).self_of_nhds]
      change ‖iteratedFDeriv ℝ n (fun _ : Vec 2 × Vec 2 => (0 : E)) X‖ ≤ _
      rw [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Qχ.budget_nonneg i)) (hB _))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Genuine fast directional words spend only their actual finite joint derivative reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceFastWord (f : ℝ → Vec 2 → Vec 2 → E) (n : ℕ) (w : Fin n → Vec 2)
    (t : ℝ) (z Y : Vec 2) : E := realWordJet (fun x => f t x Y) n w z

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem sourceFastWord_eq_jointWord (f : ℝ → Vec 2 → Vec 2 → E) (n : ℕ)
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2))
    (w : Fin n → Vec 2) (t : ℝ) (X : Vec 2 × Vec 2) :
    sourceFastWord f n w t X.1 X.2 =
      realWordJet (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n (fun i => (w i, 0)) X := by
  have he := finite_realWordJet_affine_eq (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n
    (hf t) (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) (0, X.2) w X.1
  simpa only [sourceFastWord, ContinuousLinearMap.inl_apply, Prod.mk_add_mk,
    zero_add, add_zero, Prod.mk.eta] using he

def JointSourceReserve.fastWord {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n r : ℕ) (hnr : n + r ≤ H)
    (w : Fin n → Vec 2) (hw : ∀ i, ‖w i‖ ≤ 1) :
    JointSourceReserve r (sourceFastWord f n w) := by
  have he (t : ℝ) : (fun X : Vec 2 × Vec 2 => sourceFastWord f n w t X.1 X.2) =
      realWordJet (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n (fun i => (w i, 0)) :=
    funext (sourceFastWord_eq_jointWord f n
      (fun t => (Q.regular t).of_le (by exact_mod_cast (show n ≤ H by omega))) w t)
  have hword : ∀ i, ‖(w i, (0 : Vec 2))‖ ≤ 1 := by
    intro i
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using hw i
  refine ⟨?_, ?_, ?_, (fun j => Q.budget (n + j)), (fun j => Q.budget_nonneg _), ?_⟩
  · intro t
    rw [he]
    exact finite_realWordJet_contDiff _ n r ((Q.regular t).of_le (by exact_mod_cast hnr)) _
  · intro t Y k z
    have ht : (fun x => f t (x + AVenhance.latticeShift k) Y) = fun x => f t x Y :=
      funext (Q.periodic t Y k)
    have hd := congrArg (fun g => iteratedFDeriv ℝ n g z) ht
    have hshift : iteratedFDeriv ℝ n (fun x => f t (x + AVenhance.latticeShift k) Y) z =
        iteratedFDeriv ℝ n (fun x => f t x Y) (z + AVenhance.latticeShift k) :=
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => f t y Y) n
        (AVenhance.latticeShift k) z
    rw [hshift] at hd
    exact congrArg (fun A => A w) hd
  · intro Y
    exact finite_realParameterWordJet_measurable_joint (fun t z => f t z Y) n
      (fun t => (Q.fast_contDiff t Y).of_le (by exact_mod_cast (show n ≤ H by omega)))
      (Q.measurable Y) w
  · intro j hj t X
    rw [he]
    exact (finite_realWordJet_derivative_bound _ n j
      ((Q.regular t).of_le (by exact_mod_cast (show n + j ≤ H by omega))) _ hword X).trans
      (Q.derivative_bound (n + j) (by omega) t X)
end

/-! Literal bilinear path-forcing products retain genuine finite source reserves. -/

section
variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def JointSourceReserve.bilinear {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    {g : ℝ → Vec 2 → Vec 2 → F} (Q : JointSourceReserve H f) (R : JointSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) : JointSourceReserve H (fun t z Y => T (f t z Y) (g t z Y)) where
  regular t := (T.contDiff.comp (Q.regular t)).clm_apply (R.regular t)
  periodic t Y n z := congrArg₂ (fun x y => T x y) (Q.periodic t Y n z) (R.periodic t Y n z)
  measurable Y := T.isBoundedBilinearMap.continuous.measurable.comp
    ((Q.measurable Y).prodMk (R.measurable Y))
  budget n := ‖T‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Q.budget i * R.budget (n - i)
  budget_nonneg n := mul_nonneg (norm_nonneg T) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Q.budget_nonneg i)) (R.budget_nonneg _))
  derivative_bound n hn t X := by
    apply (T.norm_iteratedFDeriv_le_of_bilinear (Q.regular t) (R.regular t) X
      (by exact_mod_cast hn)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ H := by have := Finset.mem_range.mp hi; omega
    have hni : n - i ≤ H := by omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Q.derivative_bound i hi' t X) (Nat.cast_nonneg _))
      (R.derivative_bound (n - i) hni t X) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Q.budget_nonneg i))
end

/-! Finite literal path sums preserve the finite source reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.zero (H : ℕ) : JointSourceReserve H (fun _ _ _ => (0 : E)) where
  regular _ := contDiff_const
  periodic _ _ _ _ := rfl
  measurable _ := measurable_const
  budget _ := 0
  budget_nonneg _ := le_rfl
  derivative_bound _ _ _ _ := by
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, le_refl]
end

/-! Genuine slow directional words spend only their actual finite joint derivative reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceSlowWord (f : ℝ → Vec 2 → Vec 2 → E) (n : ℕ) (w : Fin n → Vec 2)
    (t : ℝ) (z Y : Vec 2) : E := realWordJet (fun x => f t z x) n w Y

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem sourceSlowWord_eq_jointWord (f : ℝ → Vec 2 → Vec 2 → E) (n : ℕ)
    (hf : ∀ t, ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2))
    (w : Fin n → Vec 2) (t : ℝ) (X : Vec 2 × Vec 2) :
    sourceSlowWord f n w t X.1 X.2 =
      realWordJet (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n (fun i => (0, w i)) X := by
  have he := finite_realWordJet_affine_eq (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n
    (hf t) (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)) (X.1, 0) w X.2
  simpa only [sourceSlowWord, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    zero_add, add_zero, Prod.mk.eta] using he

def JointSourceReserve.slowWord {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n r : ℕ) (hnr : n + r ≤ H)
    (w : Fin n → Vec 2) (hw : ∀ i, ‖w i‖ ≤ 1) :
    JointSourceReserve r (sourceSlowWord f n w) := by
  have he (t : ℝ) : (fun X : Vec 2 × Vec 2 => sourceSlowWord f n w t X.1 X.2) =
      realWordJet (fun U : Vec 2 × Vec 2 => f t U.1 U.2) n (fun i => (0, w i)) :=
    funext (sourceSlowWord_eq_jointWord f n
      (fun t => (Q.regular t).of_le (by exact_mod_cast (show n ≤ H by omega))) w t)
  have hword : ∀ i, ‖((0 : Vec 2), w i)‖ ≤ 1 := by
    intro i
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hw i
  refine ⟨?_, ?_, ?_, (fun j => Q.budget (n + j)), (fun j => Q.budget_nonneg _), ?_⟩
  · intro t
    rw [he]
    exact finite_realWordJet_contDiff _ n r ((Q.regular t).of_le (by exact_mod_cast hnr)) _
  · intro t Y k z
    have ht : (fun x => f t (z + AVenhance.latticeShift k) x) = fun x => f t z x :=
      funext (fun x => Q.periodic t x k z)
    exact congrArg (fun g => iteratedFDeriv ℝ n g Y w) ht
  · intro Y
    exact finite_realParameterWordJet_measurable
      (fun U : ℝ × Vec 2 => f U.1 U.2) n
      (fun U => ((Q.regular U.1).comp₂ contDiff_const contDiff_id).of_le
        (by exact_mod_cast (show n ≤ H by omega))) Q.measurable w Y
  · intro j hj t X
    rw [he]
    exact (finite_realWordJet_derivative_bound _ n j
      ((Q.regular t).of_le (by exact_mod_cast (show n + j ≤ H by omega))) _ hword X).trans
      (Q.derivative_bound (n + j) (by omega) t X)
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs

/-! Restricting a genuine forcing in time preserves its literal spatial derivative budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.window {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (I : Set ℝ) (hI : MeasurableSet I) :
    JointSourceReserve H (timeWindowSource I f) :=
  windowJointSourceReserve H I hI f (fun t _ => Q.regular t)
    (fun t _ Y => Q.periodic t Y) Q.measurable Q.budget Q.budget_nonneg
    (fun n hn t _ X => Q.derivative_bound n hn t X)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Quantitative Hilbert bounds for every ordered Fourier coordinate. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.Analysis.Convolution

local instance sobolevFourierNormBoundMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sobolevFourierNormBoundAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevFourierNormBoundProbTorus : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.EntryWeakProofs

theorem realJetFourier_norm_le (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) :
    ‖realJetFourier K f a‖ ≤ ‖Complex.ofRealCLM‖ * ‖f‖ := by
  change ‖UnitAddTorus.mFourierBasis.repr
    (frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 a))‖ ≤ _
  have hn : ‖frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 a)‖ =
      ‖complexifyCellClass (f.val a)‖ := by
    have he := congrArg (fun z => ‖z‖) (realJet_torusClass K f a)
    exact he.trans ((cellToTorus (E := ℂ)).norm_map _)
  rw [LinearIsometryEquiv.norm_map, hn]
  have hc := (ContinuousLinearMap.le_opNorm (complexifyCellClass) (f.val a)).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le Complex.ofRealCLM)
      (norm_nonneg _))
  exact hc.trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le f.val a) (norm_nonneg _))

def fourierNormSequence (f : lp (fun _ : Frequency => ℂ) 2) : lp (fun _ : Frequency => ℝ) 2 :=
  ⟨fun k => ‖f k‖, f.property.norm⟩

theorem fourierNormSequence_norm (f : lp (fun _ : Frequency => ℂ) 2) :
    ‖fourierNormSequence f‖ = ‖f‖ := by
  have he (k : Frequency) : ‖fourierNormSequence f k‖ = ‖f k‖ := by
    exact Real.norm_of_nonneg (norm_nonneg _)
  exact le_antisymm (lp.norm_mono (by norm_num) (fun k => (he k).le))
    (lp.norm_mono (by norm_num) (fun k => (he k).ge))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A full independent parameter jet controls one intrinsic slow derivative without a norm loss. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_slow_directional_derivative_jet_norm_le (f : P × Vec 2 → ℝ)
    (n : ℕ) (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (X : P × Vec 2) (i : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Z => fderiv ℝ (fun y => f (Z.1, y)) Z.2 (basisVec i)) X‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f X‖ := by
  have he : (fun Z : P × Vec 2 => fderiv ℝ (fun y => f (Z.1, y)) Z.2 (basisVec i)) =
      realWordJet f 1 (fun _ => ((0 : P), basisVec i)) := by
    funext Z
    have hh := finite_realWordJet_affine_eq f 1
      (hf.of_le (by exact_mod_cast (show 1 ≤ n + 1 by omega)))
      (ContinuousLinearMap.inr ℝ P (Vec 2)) (Z.1, 0) (fun _ => basisVec i) Z.2
    simpa only [realWordJet, iteratedFDeriv_one_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta] using hh
  rw [he]
  have hnorm : ∀ a : Fin 1, ‖((0 : P), basisVec i)‖ ≤ 1 := by
    intro a
    simp only [Prod.norm_def, norm_zero,
      show ‖(basisVec i : Vec 2)‖ = 1 by simp [basisVec, Pi.norm_single],
      max_eq_right zero_le_one, le_refl]
  have hh := finite_realWordJet_derivative_bound f 1 n
    (by simpa only [Nat.add_comm] using hf) (fun _ => ((0 : P), basisVec i)) hnorm X
  rw [Nat.add_comm 1 n] at hh
  exact hh
end

/-! Literal bilinear source budgets multiply the stored amplitudes exactly. -/

section
variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology E] [SecondCountableTopology V] in
theorem JointSourceReserve.bilinear_budget_le {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} {g : ℝ → Vec 2 → Vec 2 → F}
    (Q : JointSourceReserve H f) (R : JointSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) (θ φ B C : ℝ)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ i ≤ H, Q.budget i ≤ θ * B) (hR : ∀ i ≤ H, R.budget i ≤ φ * C)
    (n : ℕ) (hn : n ≤ H) :
    (Q.bilinear R T).budget n ≤ (θ * φ) * (‖T‖ * 2 ^ n * B * C) := by
  change ‖T‖ * (∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * Q.budget i * R.budget (n - i)) ≤ _
  have hb : (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * Q.budget i * R.budget (n - i)) ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (θ * B) * (φ * C) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ H := by have := Finset.mem_range.mp hi; omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hQ i hi') (Nat.cast_nonneg _))
      (hR (n - i) (by omega)) (R.budget_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hθ hB))
  have hchoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have he : ‖T‖ * (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (θ * B) * (φ * C)) =
      (θ * φ) * (‖T‖ * 2 ^ n * B * C) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    ring
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg T)).trans_eq he
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Quantitative two-dimensional Wiener bounds with two reserved derivatives. -/

def latticeReciprocalSequence : lp (fun _ : Frequency => ℂ) 2 :=
  ⟨fun k => (1 / latticeWeight k : ℂ), latticeReciprocal_memLp⟩

def weightedRealJetFourier (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) : lp (fun _ : Frequency => ℂ) 2 :=
  ⟨fun k => latticeWeight k • realJetFourier K f a k, realJetFourier_weight_memLp K f a ha⟩

theorem weightedRealJetFourier_norm_le (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) :
    ‖weightedRealJetFourier K f a ha‖ ≤ 4 * ‖Complex.ofRealCLM‖ * ‖f‖ := by
  let a0 := appendJetIndex K a 0 (by omega)
  let a1 := appendJetIndex K a 1 (by omega)
  let a01 := appendJetIndex K a0 1 (by dsimp only [a0, appendJetIndex]; omega)
  let A := fourierNormSequence (realJetFourier K f a)
  let B := fourierNormSequence (realJetFourier K f a0)
  let C := fourierNormSequence (realJetFourier K f a1)
  let D := fourierNormSequence (realJetFourier K f a01)
  have hm : ‖weightedRealJetFourier K f a ha‖ ≤ ‖((A + B) + C) + D‖ := by
    apply lp.norm_mono (by norm_num)
    intro k
    change ‖latticeWeight k • realJetFourier K f a k‖ ≤
      ‖‖realJetFourier K f a k‖ + ‖realJetFourier K f a0 k‖ +
        ‖realJetFourier K f a1 k‖ + ‖realJetFourier K f a01 k‖‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k),
      Real.norm_of_nonneg (by positivity)]
    exact realJetFourier_weight_bound K f a ha k
  have hAB := norm_add_le A B
  have hABC := norm_add_le (A + B) C
  have hABCD := norm_add_le ((A + B) + C) D
  have hA := realJetFourier_norm_le K f a
  have hB := realJetFourier_norm_le K f a0
  have hC := realJetFourier_norm_le K f a1
  have hD := realJetFourier_norm_le K f a01
  have hnA : ‖A‖ = ‖realJetFourier K f a‖ := fourierNormSequence_norm _
  have hnB : ‖B‖ = ‖realJetFourier K f a0‖ := fourierNormSequence_norm _
  have hnC : ‖C‖ = ‖realJetFourier K f a1‖ := fourierNormSequence_norm _
  have hnD : ‖D‖ = ‖realJetFourier K f a01‖ := fourierNormSequence_norm _
  rw [hnA, hnB] at hAB
  rw [hnC] at hABC
  rw [hnD] at hABCD
  linarith

theorem realJetFourier_wiener_bound (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) :
    (∑' k : Frequency, ‖realJetFourier K f a k‖) ≤
      (4 * ‖Complex.ofRealCLM‖ * ‖latticeReciprocalSequence‖) * ‖f‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
    ENNReal.HolderConjugate.toReal (by norm_num)
  have h := lp.tsum_mul_le_mul_norm' hpq (weightedRealJetFourier K f a ha) latticeReciprocalSequence
  have he (k : Frequency) : ‖weightedRealJetFourier K f a ha k‖ *
      ‖latticeReciprocalSequence k‖ = ‖realJetFourier K f a k‖ := by
    change ‖latticeWeight k • realJetFourier K f a k‖ * ‖(1 / latticeWeight k : ℂ)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k), norm_div,
      norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k)]
    field_simp [ne_of_gt (latticeWeight_pos k)]
  simp only [he] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (weightedRealJetFourier_norm_le K f a ha)
    (norm_nonneg _)).trans_eq (by ring))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Filter Topology
open AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Summable Fourier majorants upgrade coefficient convergence to uniform series convergence. -/

variable {A : Type*} {l : Filter A}

theorem fourier_norm_sum_tendsto_zero (c : A → Frequency → ℂ) (b : Frequency → ℝ)
    (hb : Summable b) (hc : ∀ k, Tendsto (fun a => c a k) l (𝓝 0))
    (hm : ∀ᶠ a in l, ∀ k, ‖c a k‖ ≤ b k) :
    Tendsto (fun a => ∑' k, ‖c a k‖) l (𝓝 0) := by
  have hh := tendsto_tsum_of_dominated_convergence hb
    (fun k => (hc k).norm) (hm.mono (fun a ha k => by simpa using ha k))
  simpa only [norm_zero, tsum_zero] using hh

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Finite forcing sums retain the sum of their actual derivative budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem jointSourceReserve_sum_with_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i, JointSourceReserve H (f i)) :
    ∃ R : JointSourceReserve H (fun t z Y => ∑ i ∈ s, f i t z Y),
      ∀ n, R.budget n = ∑ i ∈ s, (Q i).budget n := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨JointSourceReserve.zero H, ?_⟩
      intro n
      simp only [JointSourceReserve.zero, Finset.sum_empty]
  | @insert i s hi ih =>
      obtain ⟨R, hR⟩ := ih
      have he : (fun t z Y => ∑ j ∈ insert i s, f j t z Y) =
          fun t z Y => f i t z Y + ∑ j ∈ s, f j t z Y := by
        funext t z Y
        exact Finset.sum_insert hi
      rw [he]
      refine ⟨(Q i).add R, ?_⟩
      intro n
      change (Q i).budget n + R.budget n = _
      rw [hR, Finset.sum_insert hi]

def JointSourceReserve.fintypeSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i, JointSourceReserve H (f i)) :
    JointSourceReserve H (fun t z Y => ∑ i, f i t z Y) :=
  Classical.choose (jointSourceReserve_sum_with_budget Finset.univ H f Q)

theorem JointSourceReserve.fintypeSum_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i, JointSourceReserve H (f i)) (n : ℕ) :
    (JointSourceReserve.fintypeSum H f Q).budget n = ∑ i, (Q i).budget n :=
  Classical.choose_spec (jointSourceReserve_sum_with_budget Finset.univ H f Q) n

def JointSourceReserve.finsetSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i ∈ s, JointSourceReserve H (f i)) :
    JointSourceReserve H (fun t z Y => ∑ i ∈ s, f i t z Y) := by
  have he : (fun t z Y => ∑ i : s, f i.val t z Y) =
      fun t z Y => ∑ i ∈ s, f i t z Y := by
    funext t z Y
    exact Finset.sum_attach s (fun i => f i t z Y)
  exact (JointSourceReserve.fintypeSum H (fun i : s => f i.val)
    (fun i => Q i.val i.property)).congrSource he

theorem JointSourceReserve.finsetSum_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i ∈ s, JointSourceReserve H (f i)) (n : ℕ) :
    (JointSourceReserve.finsetSum s H f Q).budget n = ∑ i : s, (Q i.val i.property).budget n := by
  unfold JointSourceReserve.finsetSum
  rw [JointSourceReserve.congrSource_budget, JointSourceReserve.fintypeSum_budget]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! One finite product constant bounds every retained source derivative without enlarging stored amplitudes. -/

section
variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology E] [SecondCountableTopology V] in
theorem JointSourceReserve.bilinear_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → Vec 2 → E} {g : ℝ → Vec 2 → Vec 2 → F}
    (Q : JointSourceReserve H f) (R : JointSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) (θ φ B C : ℝ)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hQ : ∀ i ≤ H, Q.budget i ≤ θ * B) (hR : ∀ i ≤ H, R.budget i ≤ φ * C)
    (r : ℕ) (hr : r ≤ H) :
    (Q.bilinear R T).budget r ≤ (θ * φ) * (‖T‖ * 2 ^ H * B * C) := by
  apply (Q.bilinear_budget_le R T θ φ B C hθ hB hQ hR r hr).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ hφ)
  have hp : (2 : ℝ) ^ r ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (norm_nonneg T)) hB) hC
end

/-! Spatial normalization leaves the chart Jacobian unchanged at the scaled point. -/

theorem rescaledChart_fderiv (ρ : ℝ) (hρ : 0 < ρ) (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Vec 2) :
    fderiv ℝ (rescaledChart ρ F) x = fderiv ℝ F (ρ • x) := by
  have h := ((hF.differentiable (by simp) (ρ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul ρ)).const_smul ρ⁻¹
  have hd : fderiv ℝ (rescaledChart ρ F) x =
      ρ⁻¹ • ((fderiv ℝ F (ρ • x)).comp (ρ • ContinuousLinearMap.id ℝ (Vec 2))) := by
    change fderiv ℝ (fun z => ρ⁻¹ • F (ρ • z)) x = _
    simpa only [Function.comp_def, Pi.smul_def, id_eq] using h.fderiv
  rw [hd]
  ext v i
  change ρ⁻¹ * ((fderiv ℝ F (ρ • x)) (ρ • v)) i = ((fderiv ℝ F (ρ • x)) v) i
  rw [map_smul]
  change ρ⁻¹ * (ρ * ((fderiv ℝ F (ρ • x)) v) i) = _
  rw [← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]

theorem rescaledChart_jacMatrix (ρ : ℝ) (hρ : 0 < ρ) (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Vec 2) :
    jacMatrix (rescaledChart ρ F) x = jacMatrix F (ρ • x) := by
  ext i j
  simp only [jacMatrix, Matrix.of_apply, rescaledChart_fderiv ρ hρ F hF x]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Uniform classical derivative bounds from two reserved Sobolev orders. -/

theorem realFourierMajorant_eq_word_sum (K : ℕ) (f : TorusHk K ℝ)
    (n : ℕ) (hn : n ≤ K) (k : Frequency) :
    realFourierMajorant K f n k =
      ∑ w : DerivativeWord2 n, ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖ := by
  simp_rw [realJetFourier_word_norm K f n hn]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← frequencyPower_eq_word_sum]
  dsimp only [realFourierMajorant]
  ring

theorem realFourierMajorant_tsum_bound (K : ℕ) (f : TorusHk K ℝ)
    (n : ℕ) (hn : n + 2 ≤ K) :
    (∑' k : Frequency, realFourierMajorant K f n k) ≤
      (Fintype.card (DerivativeWord2 n) : ℝ) *
        (4 * ‖Complex.ofRealCLM‖ * ‖latticeReciprocalSequence‖) * ‖f‖ := by
  have hs : HasSum (fun k : Frequency =>
      ∑ w : DerivativeWord2 n, ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖)
      (∑ w : DerivativeWord2 n, ∑' k : Frequency,
        ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖) := by
    apply hasSum_sum
    intro w _
    exact (realJetFourier_norm_summable K f ⟨⟨n, by omega⟩, w⟩ hn).hasSum
  simp_rw [realFourierMajorant_eq_word_sum K f n (by omega)]
  rw [hs.tsum_eq]
  calc
    (∑ w : DerivativeWord2 n, ∑' k : Frequency,
      ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖) ≤
        ∑ _w : DerivativeWord2 n,
          (4 * ‖Complex.ofRealCLM‖ * ‖latticeReciprocalSequence‖) * ‖f‖ := by
      apply Finset.sum_le_sum
      intro w _
      exact realJetFourier_wiener_bound K f ⟨⟨n, by omega⟩, w⟩ hn
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem realFourierLift_derivative_norm_le (K : ℕ) (f : TorusHk K ℝ)
    (n : ℕ) (hn : n + 2 ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (realFourierLift K f) x‖ ≤
      (Fintype.card (DerivativeWord2 n) : ℝ) *
        (4 * ‖Complex.ofRealCLM‖ * ‖latticeReciprocalSequence‖) * ‖f‖ := by
  have hs (j : ℕ) (hj : (j : ℕ∞) ≤ (n : ℕ∞)) :
      Summable (realFourierMajorant K f j) := by
    have hjn : j ≤ n := by exact_mod_cast hj
    exact realFourierMajorant_summable K f j (by omega)
  have hd := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (n : ℕ∞))
    (f := realFourierMode K f) (v := realFourierMajorant K f)
    (fun k => (realFourierMode_contDiff K f k).of_le (by simp)) hs
    (fun j k y _ => realFourierMode_derivative_bound K f j k y) (le_refl _) x
  change ‖iteratedFDeriv ℝ n (fun y => ∑' k : Frequency, realFourierMode K f k y) x‖ ≤ _
  rw [hd]
  exact (tsum_of_norm_bounded (realFourierMajorant_summable K f n hn).hasSum
    (fun k => realFourierMode_derivative_bound K f n k x)).trans
      (realFourierMajorant_tsum_bound K f n hn)

def classicalSobolevConstant (n : ℕ) : ℝ :=
  ‖Complex.reCLM‖ * (Fintype.card (DerivativeWord2 n) : ℝ) *
    (4 * ‖Complex.ofRealCLM‖ * ‖latticeReciprocalSequence‖)

theorem realClassicalLift_derivative_norm_le (K : ℕ) (f : TorusHk K ℝ)
    (n : ℕ) (hn : n + 2 ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (realClassicalLift K f) x‖ ≤ classicalSobolevConstant n * ‖f‖ := by
  change ‖iteratedFDeriv ℝ n (Complex.reCLM ∘ realFourierLift K f) x‖ ≤ _
  rw [Complex.reCLM.iteratedFDeriv_comp_left
    (realFourierLift_contDiff K n hn f).contDiffAt (le_refl _)]
  exact (Complex.reCLM.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul_of_nonneg_left (realFourierLift_derivative_norm_le K f n hn x)
      (norm_nonneg _)).trans_eq (by dsimp only [classicalSobolevConstant]; ring))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open AVRegularity.Velocity AVRegularity.Velocity.Port
open AVRegularity.Velocity.Port.Section2FlowIdentities
namespace AVRegularity.EntryWeakProofs

/-! Source-derived short-time Jacobian bounds for the actual coarse flow. -/

theorem source_flow_close {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (r t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude m)⁻¹)
    (x : Vec 2) :
    ‖constructionFlowJacobian D hseq m t r x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      2 ^ 23 * |t| * D.velocityAmplitude m := by
  generalize hβ : α + 1 = β
  have hα : α = β - 1 := by linarith
  subst α
  obtain ⟨_, C, _, hf⟩ :=
    StreamRegularity.section2_induction_outputs_from_source_data D hseq
  exact (hf.flow_close m hm r t ht x).1

theorem actual_coarse_flow_close (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (m : ℕ) (hm : 1 ≤ m) (r t : ℝ)
    (ht : |t - r| ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ m)⁻¹) (x : Vec 2) :
    ‖fderiv ℝ (fun y => D.flowOf m t y r) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      2 ^ 23 * |t - r| * ocA D.α D.q D.Λ m := by
  let J := ocJetRecursionData D.α s hα₀ hα₁ hs₀ hs₁ D.q hq D.Λ hΛ D.ζ hζ
  have hc := source_flow_close J hseq m hm r (t - r) ht x
  simpa only [Section2FlowIdentities.constructionFlowJacobian,
    Section2FlowIdentities.streamFlowJacobian, OCData.flowOf,
    Section2FlowIdentities.streamFlow, AVRegularity.streamFlow, J, ocJetRecursionData,
    add_sub_cancel] using hc

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Fast derivative budgets control the genuine classical periodic Sobolev carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

local instance finiteSmoothPeriodicCarrierBoundFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp only [Measure.restrict_apply_univ, weak_unitCube_volume]; exact ENNReal.one_lt_top⟩

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem finite_smooth_periodic_jet_memLp (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (C : ℕ → ℝ)
    (hb : ∀ n, n ≤ K → ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C n) (a : JetIndex2 K) :
    MemLp (orderedDerivative a.2 f) 2 (volume.restrict AVenhance.unitCube) := by
  have hs : ContDiff ℝ (a.1.val : ℕ∞) f := hf.of_le (by exact_mod_cast (show a.1.val ≤ K by omega))
  exact MemLp.of_bound (ChartTransport.continuous_orderedDerivative a.2 hs).aestronglyMeasurable
    (C a.1.val) (Filter.Eventually.of_forall fun z =>
      (ChartTransport.norm_orderedDerivative_le hs a.2 z).trans (hb _ (by omega) z))

def finiteBoundedSmoothPeriodicHk (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (C : ℕ → ℝ)
    (hb : ∀ n, n ≤ K → ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C n) : TorusHk K E :=
  finiteSmoothPeriodicHk K f hf hp (finite_smooth_periodic_jet_memLp K f hf C hb)

theorem finiteBoundedSmoothPeriodicHk_norm_le (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) (C : ℕ → ℝ)
    (hC : ∀ n, 0 ≤ C n)
    (hb : ∀ n, n ≤ K → ∀ z, ‖iteratedFDeriv ℝ n f z‖ ≤ C n) :
    ‖finiteBoundedSmoothPeriodicHk K f hf hp C hb‖ ≤ ∑ a : JetIndex2 K, C a.1.val := by
  apply (AVRegularity.Weighted.finitePiLp_norm_le_sum
    (finiteBoundedSmoothPeriodicHk K f hf hp C hb).val).trans
  apply Finset.sum_le_sum
  intro a _
  have hs : ContDiff ℝ (a.1.val : ℕ∞) f := hf.of_le (by exact_mod_cast (show a.1.val ≤ K by omega))
  have hnorm (z : Vec 2) : ‖orderedDerivative a.2 f z‖ ≤ C a.1.val :=
    (ChartTransport.norm_orderedDerivative_le hs a.2 z).trans (hb _ (by omega) z)
  have he := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict AVenhance.unitCube)
    (ChartTransport.continuous_orderedDerivative a.2 hs).aestronglyMeasurable
    (Filter.Eventually.of_forall hnorm)
  have he' : eLpNorm (orderedDerivative a.2 f) 2 (volume.restrict AVenhance.unitCube) ≤
      ENNReal.ofReal (C a.1.val) := by
    simpa only [Measure.restrict_apply_univ, weak_unitCube_volume,
      ENNReal.one_rpow, one_mul] using he
  change ‖(finite_smooth_periodic_jet_memLp K f hf C hb a).toLp (orderedDerivative a.2 f)‖ ≤ _
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_ofReal (hC _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he'

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The independent child-geometry recursion is the geometry of the literal extended real chain. -/

section
variable {P : Type*}

def independentChainAppend (A : P → RealChain) (e : ℤ × (P → ChainChild)) (Y : P) : RealChain :=
  { A Y with
    slots := (A Y).slots ++ [e.1]
    children := (A Y).children ++ [e.2 Y] }

def independentChainExtension : (P → RealChain) → List (ℤ × (P → ChainChild)) → P → RealChain
  | A, [] => A
  | A, e :: rest => independentChainExtension (independentChainAppend A e) rest

theorem independentChainAppend_wellSlotted (A : P → RealChain) (e : ℤ × (P → ChainChild))
    (hA : ∀ Y, (A Y).WellSlotted) (Y : P) : (independentChainAppend A e Y).WellSlotted := by
  have hh := hA Y
  change (A Y).slots.length = (A Y).children.length + 1 at hh
  change ((A Y).slots ++ [e.1]).length = ((A Y).children ++ [e.2 Y]).length + 1
  simp only [List.length_append, List.length_singleton]
  omega

theorem independentChainAppend_ctxLevel (A : P → RealChain) (e : ℤ × (P → ChainChild)) (Y : P) :
    (independentChainAppend A e Y).ctxLevel = (A Y).ctxLevel + 1 := by
  simp only [independentChainAppend, RealChain.ctxLevel, RealChain.lastLevel,
    List.length_append, List.length_singleton]
  omega

theorem independentChainAppend_slot (A : P → RealChain) (e : ℤ × (P → ChainChild)) (Y : P) :
    (independentChainAppend A e Y).slot = e.1 := by
  simp only [independentChainAppend, RealChain.slot, List.getLastD_concat]

theorem independentChainAppend_geom (D : OCData) (A : P → RealChain)
    (e : ℤ × (P → ChainChild)) (hA : ∀ Y, (A Y).WellSlotted) (Y : P) :
    (independentChainAppend A e Y).geom D = D.childGeom (A Y).ctxLevel (A Y).slot
      (D.slotAnchor ((A Y).ctxLevel + 1) e.1) (e.2 Y) ((A Y).geom D) := by
  simpa only [independentChainAppend, RealChain.ctxLevel, RealChain.lastLevel, RealChain.slot,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (geom_append_child D (A Y).baseLevel (A Y).slots (A Y).base (A Y).children (hA Y) e.1 (e.2 Y))
end

/-! Constituent lists retain multiplicity and the sum of their individual forcing reserves. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.listSum {ι : Type*} (l : List ι) (H : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i ∈ l, JointSourceReserve H (f i)) :
    JointSourceReserve H (fun t z Y => (l.map (fun i => f i t z Y)).sum) := by
  induction l with
  | nil => exact JointSourceReserve.zero H
  | cons i l ih =>
      have he : (fun t z Y => ((i :: l).map (fun i => f i t z Y)).sum) =
          fun t z Y => f i t z Y + (l.map (fun i => f i t z Y)).sum := by
        funext t z Y
        simp only [List.map_cons, List.sum_cons]
      exact ((Q i (List.mem_cons_self ..)).add
        (ih (fun j hj => Q j (List.mem_cons_of_mem i hj)))).congrSource he.symm

theorem JointSourceReserve.listSum_uniform_budget {ι : Type*} (l : List ι) (H : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → E)
    (Q : ∀ i ∈ l, JointSourceReserve H (f i)) (θ B : ℝ)
    (hQ : ∀ i hi r, r ≤ H → (Q i hi).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (JointSourceReserve.listSum l H f Q).budget r ≤ (l.length : ℝ) * (θ * B) := by
  induction l with
  | nil =>
      simp only [JointSourceReserve.listSum, JointSourceReserve.zero, List.length_nil,
        Nat.cast_zero, zero_mul, le_refl]
  | cons i l ih =>
      unfold JointSourceReserve.listSum
      rw [JointSourceReserve.congrSource_budget]
      change (Q i (List.mem_cons_self ..)).budget r +
        (JointSourceReserve.listSum l H f (fun j hj => Q j (List.mem_cons_of_mem i hj))).budget r ≤ _
      have ht := ih (fun j hj => Q j (List.mem_cons_of_mem i hj))
        (fun j hj => hQ j (List.mem_cons_of_mem i hj))
      apply (add_le_add (hQ i (List.mem_cons_self ..) r hr) ht).trans_eq
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
end

/-! Finite scalar families retain genuine joint reserves through their actual coordinate inclusions. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarCoordinateInjection (i : ι) : ℝ →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℝ ℝ else 0)

def jointSourcePiReserve (H : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → ℝ)
    (Q : ∀ i, JointSourceReserve H (f i)) :
    JointSourceReserve H (fun t z Y i => f i t z Y) := by
  let F := fun i t z Y => scalarCoordinateInjection i (f i t z Y)
  have he : (fun t z Y => ∑ i : ι, F i t z Y) = fun t z Y i => f i t z Y := by
    funext t z Y j
    rw [Finset.sum_apply]
    change (∑ i : ι, (scalarCoordinateInjection i (f i t z Y)) j) = f j t z Y
    have hterm (i : ι) : (scalarCoordinateInjection i (f i t z Y)) j =
        if j = i then f i t z Y else 0 := by
      by_cases h : j = i
      · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, h, ite_true,
          ContinuousLinearMap.id_apply]
      · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, h, ite_false,
          zero_apply]
    simp_rw [hterm]
    simp
  exact (JointSourceReserve.fintypeSum H F
    (fun i => (Q i).map (scalarCoordinateInjection i))).congrSource he
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Linearity of the canonical classical Fourier readout at finite Sobolev order. -/

theorem realJetFourier_add (K : ℕ) (f g : TorusHk K ℝ) (a : JetIndex2 K) (k : Frequency) :
    realJetFourier K (f + g) a k = realJetFourier K f a k + realJetFourier K g a k := by
  simp only [realJetFourier_eq_cellCoeff]
  have he : (f + g).val a = f.val a + g.val a := rfl
  rw [he, map_add, map_add]

theorem realJetFourier_smul (K : ℕ) (c : ℝ) (f : TorusHk K ℝ) (a : JetIndex2 K) (k : Frequency) :
    realJetFourier K (c • f) a k = c • realJetFourier K f a k := by
  simp only [realJetFourier_eq_cellCoeff]
  have he : (c • f).val a = c • f.val a := rfl
  rw [he, map_smul, map_smul]

theorem realFourierMode_summable (K : ℕ) (hK : 2 ≤ K) (f : TorusHk K ℝ) (x : Vec 2) :
    Summable (fun k : Frequency => realFourierMode K f k x) := by
  apply (realFourierMajorant_summable K f 0 (by omega)).of_norm_bounded
  intro k
  simpa only [norm_iteratedFDeriv_zero] using realFourierMode_derivative_bound K f 0 k x

theorem realFourierLift_add (K : ℕ) (hK : 2 ≤ K) (f g : TorusHk K ℝ) :
    realFourierLift K (f + g) = realFourierLift K f + realFourierLift K g := by
  funext x
  change (∑' k, realFourierMode K (f + g) k x) = _
  have he (k : Frequency) : realFourierMode K (f + g) k x =
      realFourierMode K f k x + realFourierMode K g k x := by
    unfold realFourierMode
    rw [realJetFourier_add, add_smul]
  simp_rw [he]
  exact (realFourierMode_summable K hK f x).tsum_add (realFourierMode_summable K hK g x)

theorem realFourierLift_smul (K : ℕ) (hK : 2 ≤ K) (c : ℝ) (f : TorusHk K ℝ) :
    realFourierLift K (c • f) = c • realFourierLift K f := by
  funext x
  change (∑' k, realFourierMode K (c • f) k x) = _
  have he (k : Frequency) : realFourierMode K (c • f) k x = c • realFourierMode K f k x := by
    unfold realFourierMode
    rw [realJetFourier_smul, smul_assoc]
  simp_rw [he]
  exact (realFourierMode_summable K hK f x).tsum_const_smul c

theorem realClassicalLift_add (K : ℕ) (hK : 2 ≤ K) (f g : TorusHk K ℝ) :
    realClassicalLift K (f + g) = realClassicalLift K f + realClassicalLift K g := by
  funext x
  simp only [realClassicalLift, realFourierLift_add K hK, Pi.add_apply, Complex.add_re]

theorem realClassicalLift_smul (K : ℕ) (hK : 2 ≤ K) (c : ℝ) (f : TorusHk K ℝ) :
    realClassicalLift K (c • f) = c • realClassicalLift K f := by
  funext x
  simp only [realClassicalLift, realFourierLift_smul K hK, Pi.smul_apply, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Four derivative reserves give a fixed summable majorant for every Fourier jet. -/

theorem realJetFourier_weight_point_bound (K : ℕ) (f : TorusHk K ℝ)
    (a : JetIndex2 K) (ha : a.1.val + 2 ≤ K) (k : Frequency) :
    latticeWeight k * ‖realJetFourier K f a k‖ ≤ 4 * ‖Complex.ofRealCLM‖ * ‖f‖ := by
  have hh := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weightedRealJetFourier K f a ha) k).trans (weightedRealJetFourier_norm_le K f a ha)
  simpa only [weightedRealJetFourier, norm_smul, Real.norm_eq_abs,
    abs_of_pos (latticeWeight_pos k)] using hh

theorem realJetFourier_summable_majorant (K : ℕ) (f : TorusHk K ℝ)
    (a : JetIndex2 K) (ha : a.1.val + 4 ≤ K) (k : Frequency) :
    ‖realJetFourier K f a k‖ ≤
      (16 * ‖Complex.ofRealCLM‖ * ‖f‖) * (1 / latticeWeight k) ^ 2 := by
  let a0 := appendJetIndex K a 0 (by omega)
  let a1 := appendJetIndex K a 1 (by omega)
  let a01 := appendJetIndex K a0 1 (by dsimp only [a0, appendJetIndex]; omega)
  have hh := mul_le_mul_of_nonneg_left
    (realJetFourier_weight_bound K f a (by omega) k) (latticeWeight_pos k).le
  rw [mul_add, mul_add, mul_add] at hh
  have h0 := realJetFourier_weight_point_bound K f a (by omega) k
  have h1 := realJetFourier_weight_point_bound K f a0
    (by dsimp only [a0, appendJetIndex]; omega) k
  have h2 := realJetFourier_weight_point_bound K f a1
    (by dsimp only [a1, appendJetIndex]; omega) k
  have h3 := realJetFourier_weight_point_bound K f a01
    (by dsimp only [a01, a0, appendJetIndex]; omega) k
  have hsum : latticeWeight k ^ 2 * ‖realJetFourier K f a k‖ ≤
      16 * ‖Complex.ofRealCLM‖ * ‖f‖ := by
    dsimp only [a0, a1, a01] at h1 h2 h3
    nlinarith only [hh, h0, h1, h2, h3]
  rw [one_div_pow, mul_one_div]
  exact (le_div_iff₀ (sq_pos_of_pos (latticeWeight_pos k))).2 (by
    simpa only [mul_comm] using hsum)

end AVRegularity.EntryWeakProofs
end
end
