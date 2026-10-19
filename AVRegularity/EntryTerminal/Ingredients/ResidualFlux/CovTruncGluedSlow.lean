-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncPulsePeriodic
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.CycleComparison.Reconstruction.FrozenMeasure
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Jets
public import AVRegularity.EntryTerminal.Ingredients.Recon.Setting.Main
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
import AVRegularity.CycleComparison.Assembly.OcData
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetSteps
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import Mathlib.MeasureTheory.Function.Floor

section
section
/-! Positive scalar derivative arrays are fixed linear readings of derivative arrays of
its gradient. This removes one tested derivative before applying the factorial reserve.
The reading and its norm bound are independent of the component space and the datum.
Degenerate cases: r=0 reads the gradient coordinates; zero fields and zero components give
zero arrays. The first letter of an ordered word is its innermost derivative. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.Construction.Residual.Presentation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reading the inner derivative from a gradient and the remaining derivatives from its jet. -/
def covTruncGradientWordCLM (r : ℕ) :
    PiLp 2 (fun _ : DerivativeWord2 r => PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
      PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 (r + 1) => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun β =>
      (PiLp.proj 2 (fun _ : Fin 2 => E) (β 0)).comp
        (PiLp.proj 2 (fun _ : DerivativeWord2 r => PiLp 2 (fun _ : Fin 2 => E)) (Fin.tail β)))

/-- The literal word-reading formula. -/
theorem covTruncGradientWordCLM_apply (r : ℕ)
    (w : PiLp 2 (fun _ : DerivativeWord2 r => PiLp 2 (fun _ : Fin 2 => E)))
    (β : DerivativeWord2 (r + 1)) :
    covTruncGradientWordCLM r w β = w (Fin.tail β) (β 0) := by
  rfl

/-- A uniform, finite word-count bound for the reading operator. -/
theorem covTruncGradientWordCLM_norm (r : ℕ) :
    ‖covTruncGradientWordCLM (E := E) r‖ ≤ (2 : ℝ) ^ (r + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  refine (norm_piLp_le_sum _).trans ?_
  have hb : ∀ β : DerivativeWord2 (r + 1), ‖covTruncGradientWordCLM r w β‖ ≤ ‖w‖ := by
    intro β
    rw [covTruncGradientWordCLM_apply]
    exact (PiLp.norm_apply_le _ _).trans (PiLp.norm_apply_le _ _)
  refine (Finset.sum_le_sum fun β _ => hb β).trans_eq ?_
  rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul]
  push_cast
  rfl

/-- Reading the derivative array of a classical gradient gives the next scalar jet. -/
theorem covTruncGradientWordCLM_jet (r : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) f) (x : Vec 2) :
    covTruncGradientWordCLM r
        (WithLp.toLp 2 fun α : DerivativeWord2 r => orderedDerivative α (AVRegularity.CycleComparison.Coarse.gradField f) x) =
      WithLp.toLp 2 fun β : DerivativeWord2 (r + 1) => orderedDerivative β f x := by
  have hg : ContDiff ℝ (r : ℕ∞) (AVRegularity.CycleComparison.Coarse.gradField f) := contDiff_gradField_nat hf
  apply PiLp.ext
  intro β
  rw [covTruncGradientWordCLM_apply]
  change (orderedDerivative (Fin.tail β) (AVRegularity.CycleComparison.Coarse.gradField f) x) (β 0) = orderedDerivative β f x
  have he := congrFun (orderedDerivative_clm_comp
    (PiLp.proj 2 (fun _ : Fin 2 => E) (β 0)) (Fin.tail β) hg) x
  have hβ : (Fin.cons (β 0) (Fin.tail β) : DerivativeWord2 (r + 1)) = β := Fin.cons_self_tail β
  rw [← hβ, orderedDerivative_cons]
  exact he.symm

/-- Fixed readings preserve coefficient regularity and periodicity. -/
theorem covTruncGradientWord_coefficient_regular {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r K : ℕ)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E) →L[ℝ] F)
    (hA : ContDiff ℝ (K : ℕ) A) (hp : AVenhance.IsZ2Periodic A) :
    ContDiff ℝ (K : ℕ) (fun x => (A x).comp (covTruncGradientWordCLM r)) ∧
      AVenhance.IsZ2Periodic (fun x => (A x).comp (covTruncGradientWordCLM r)) := by
  refine ⟨?_, fun z x => ?_⟩
  · exact ((ContinuousLinearMap.compL ℝ
    (PiLp 2 (fun _ : DerivativeWord2 r => PiLp 2 (fun _ : Fin 2 => E)))
    (PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E)) F).flip (covTruncGradientWordCLM (E := E) r)).contDiff.comp hA
  · change (A (x + AVenhance.latticeShift z)).comp (covTruncGradientWordCLM r) = _
    rw [hp z x]

/-- Fixed readings cost only a word-count factor in each coefficient derivative array. -/
theorem covTruncGradientWord_coefficient_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r j : ℕ)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E) →L[ℝ] F)
    (hA : ContDiff ℝ (j : ℕ) A) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => (A y).comp (covTruncGradientWordCLM r)) j x‖ ≤
      (2 : ℝ) ^ j * (2 ^ (r + 1) * ‖coefficientDerivativeArray A j x‖) := by
  let Φ := (ContinuousLinearMap.compL ℝ
    (PiLp 2 (fun _ : DerivativeWord2 r => PiLp 2 (fun _ : Fin 2 => E)))
    (PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E)) F).flip (covTruncGradientWordCLM (E := E) r)
  have hΦ : ‖Φ‖ ≤ (2 : ℝ) ^ (r + 1) := by
    refine (ContinuousLinearMap.opNorm_le_bound Φ (by positivity) fun T => ?_)
    change ‖T.comp (covTruncGradientWordCLM r)‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (covTruncGradientWordCLM_norm (E := E) r) (norm_nonneg T))
  exact (norm_array_clm_comp_le Φ A j hA x).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦ (norm_nonneg _)) (by positivity))

/-- The fixed gradient reading costs a uniform word factor in the coefficient seminorm.
Suprema remain inside each entry, before any component row or column is summed. -/
theorem covTruncGradientWord_seminorm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r K : ℕ) (ρ a b : ℝ)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E) →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t)) :
    coefficientSeminorm ρ K a b (fun t x => (A t x).comp (covTruncGradientWordCLM r)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ K * 2 ^ (r + 1)) * coefficientSeminorm ρ K a b A := by
  unfold coefficientSeminorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hb : (⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2,
      (‖coefficientDerivativeArray (fun y => (A t y).comp (covTruncGradientWordCLM r)) j x‖₊ : ℝ≥0∞)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ K * 2 ^ (r + 1)) *
        ⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞) := by
    refine iSup₂_le fun t ht => iSup_le fun x => ?_
    have hjet := (covTruncGradientWord_coefficient_bound r j (A t)
      ((hA t ht).of_le (by exact_mod_cast hjK)) x).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjK)
          (mul_nonneg (by positivity) (norm_nonneg _)))
    have he : (‖coefficientDerivativeArray (fun y => (A t y).comp (covTruncGradientWordCLM r)) j x‖₊ : ℝ≥0∞) ≤
        ENNReal.ofReal ((2 : ℝ) ^ K * 2 ^ (r + 1)) *
          (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞) := by
      have he := ENNReal.ofReal_le_ofReal hjet
      rw [← mul_assoc] at he
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ K),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (r + 1)),
        ofReal_norm, enorm_eq_nnnorm, mul_assoc] using he
    exact he.trans (mul_le_mul_of_nonneg_left (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le x le_rfl))) zero_le)
  calc
    _ ≤ ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
        (ENNReal.ofReal ((2 : ℝ) ^ K * 2 ^ (r + 1)) *
          ⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)) :=
      mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by ring

/-- A uniform finite-order cost of reading scalar jets from gradient jets. -/
def covTruncGradientCoefficientConst (K R : ℕ) : ℝ :=
  ((2 : ℝ) ^ K * 2 ^ (R + 1)) * ((K + R).factorial : ℝ) / (K.factorial : ℝ)

/-- The gradient reading's coefficient seminorm and factorial reserve are paid by the
usual normalized scalar coefficient price. The constant precedes all field data. -/
theorem covTruncGradientWord_cost {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r K R : ℕ) (hr : r ≤ R) (ρ a b : ℝ) (hρ : 0 < ρ)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (r + 1) => E) →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hfin : coefficientSeminorm ρ K a b A ≠ ⊤) :
    (coefficientSeminorm ρ K a b (fun t x => (A t x).comp (covTruncGradientWordCLM r))).toReal *
        derivativeReserveFactor ρ K r ≤ covTruncGradientCoefficientConst K R *
      ((coefficientSeminorm ρ K a b A).toReal / ρ ^ r) := by
  have hg : 0 ≤ (2 : ℝ) ^ K * 2 ^ (r + 1) := by positivity
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (covTruncGradientWord_seminorm_le r K ρ a b A hA)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hg] at hb
  have hγ : (2 : ℝ) ^ K * 2 ^ (r + 1) ≤ 2 ^ K * 2 ^ (R + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.add_le_add_right hr 1)) (by positivity)
  have hfac : ((K + r).factorial : ℝ) ≤ (K + R).factorial :=
    Nat.cast_le.mpr (Nat.factorial_le (Nat.add_le_add_left hr K))
  have hconst : ((2 : ℝ) ^ K * 2 ^ (r + 1)) * ((K + r).factorial : ℝ) /
      (K.factorial : ℝ) ≤ covTruncGradientCoefficientConst K R := by
    unfold covTruncGradientCoefficientConst
    exact div_le_div_of_nonneg_right (mul_le_mul hγ hfac (Nat.cast_nonneg _) (by positivity))
      (Nat.cast_nonneg _)
  calc
    _ ≤ ((2 : ℝ) ^ K * 2 ^ (r + 1)) * (coefficientSeminorm ρ K a b A).toReal *
        derivativeReserveFactor ρ K r :=
      mul_le_mul_of_nonneg_right hb (by unfold derivativeReserveFactor; positivity)
    _ = (((2 : ℝ) ^ K * 2 ^ (r + 1)) * ((K + r).factorial : ℝ) / (K.factorial : ℝ)) *
        ((coefficientSeminorm ρ K a b A).toReal / ρ ^ r) := by
      unfold derivativeReserveFactor
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst
      (div_nonneg ENNReal.toReal_nonneg (pow_nonneg hρ.le _))

/-- Positive tested orders are indexed either by d=2..R or by the gradient reserve r=d-2.
The zero extension includes r=R-1 and r=R and also handles R=0 or R=1. -/
theorem covTruncPositiveOrder_sum {F : Type*} [AddCommMonoid F] (R : ℕ)
    (g : Finset.Icc 2 R → F) :
    (∑ r : Fin (R + 1), if hr : r.val + 2 ≤ R then
      g ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ else 0) = ∑ d, g d := by
  classical
  let S := Finset.univ.filter (fun r : Fin (R + 1) => r.val + 2 ≤ R)
  have he : (∑ r : Fin (R + 1), if hr : r.val + 2 ≤ R then
      g ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ else 0) =
      ∑ r ∈ S, if hr : r.val + 2 ≤ R then
        g ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> rfl
  rw [he]
  refine Finset.sum_bij (fun r hr => ⟨r.val + 2, Finset.mem_Icc.mpr
    ⟨by omega, (Finset.mem_filter.mp hr).2⟩⟩) ?_ ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_univ _
  · intro r hr r' hr' he
    apply Fin.ext
    have hv := congrArg Subtype.val he
    change r.val + 2 = r'.val + 2 at hv
    omega
  · intro d _
    have hd := Finset.mem_Icc.mp d.2
    let r : Fin (R + 1) := ⟨d.val - 2, by omega⟩
    have hr : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [r]; omega⟩
    exact ⟨r, hr, Subtype.ext (by dsimp [r]; omega)⟩
  · intro r hr
    rw [dite_eq_left (Finset.mem_filter.mp hr).2]

open AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- Matching scalar jets give matching jets of the gradient at one lower order. -/
theorem covTruncGradient_sameJet (R : ℕ) (x : Vec 2) (f g : Vec 2 → E)
    (hf : ContDiff ℝ ((R + 1 : ℕ) : ℕ∞) f)
    (hg : ContDiff ℝ ((R + 1 : ℕ) : ℕ∞) g) (hj : SameJetAt (R + 1) x f g) :
    SameJetAt R x (AVRegularity.CycleComparison.Coarse.gradField f)
      (AVRegularity.CycleComparison.Coarse.gradField g) := by
  intro r α hr
  have hgf : ContDiff ℝ (r : ℕ∞) (AVRegularity.CycleComparison.Coarse.gradField f) :=
    (contDiff_gradField_nat hf).of_le (by exact_mod_cast hr)
  have hgg : ContDiff ℝ (r : ℕ∞) (AVRegularity.CycleComparison.Coarse.gradField g) :=
    (contDiff_gradField_nat hg).of_le (by exact_mod_cast hr)
  apply PiLp.ext
  intro j
  have he := hj (r + 1) (Fin.cons j α) (by omega)
  rw [orderedDerivative_cons, orderedDerivative_cons] at he
  have ef := congrFun (orderedDerivative_clm_comp (PiLp.proj 2 (fun _ : Fin 2 => E) j) α hgf) x
  have eg := congrFun (orderedDerivative_clm_comp (PiLp.proj 2 (fun _ : Fin 2 => E) j) α hgg) x
  exact ef.symm.trans (he.trans eg)

/-- Constant covariance polynomials commute with the gradient at the finite order consumed
by the actual physical mean flux. -/
theorem covTruncGradient_covPolyP_finite {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ ((2 * p + 1 : ℕ) : ℕ∞) f) (x : Vec 2) :
    AVRegularity.CycleComparison.Coarse.gradField (covPolyP Hc p f) x =
      covPolyP Hc p (AVRegularity.CycleComparison.Coarse.gradField f) x := by
  obtain ⟨g, hg, hj⟩ := smoothJetRealization (2 * p + 1) f hf x
  have hf' : ContDiff ℝ ((1 + 2 * p : ℕ) : ℕ∞) f := by simpa only [Nat.add_comm] using hf
  have hg' : ContDiff ℝ ((1 + 2 * p : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  have hjf : SameJetAt (2 * p + 1) x f g := fun r α hr => (hj r α hr).symm
  have hj' : SameJetAt (1 + 2 * p) x f g := by simpa only [Nat.add_comm] using hjf
  have hp := (covPolyPJet Hc p 1 x f g hf' hg' hj').2.2
  have hgrad : AVRegularity.CycleComparison.Coarse.gradField (covPolyP Hc p f) x =
      AVRegularity.CycleComparison.Coarse.gradField (covPolyP Hc p g) x := by
    apply PiLp.ext
    intro j
    have he := hp 1 (Fin.cons j (Fin.elim0 : DerivativeWord2 0)) le_rfl
    rw [orderedDerivative_cons, orderedDerivative_cons, orderedDerivative_zero,
      orderedDerivative_zero] at he
    exact he
  have hjg := covTruncGradient_sameJet (2 * p) x f g hf
    (hg.of_le (by exact_mod_cast le_top)) hjf
  have hgf : ContDiff ℝ ((0 + 2 * p : ℕ) : ℕ∞)
      (AVRegularity.CycleComparison.Coarse.gradField f) := by
    simp only [zero_add]
    exact_mod_cast contDiff_gradField_nat hf
  have hgg : ContDiff ℝ ((0 + 2 * p : ℕ) : ℕ∞)
      (AVRegularity.CycleComparison.Coarse.gradField g) :=
    (contDiff_gradField_top hg).of_le (by exact_mod_cast le_top)
  have hp' := (covPolyPJet Hc p 0 x _ _ hgf hgg
    (by simpa only [zero_add] using hjg)).2.2 0 (Fin.elim0 : DerivativeWord2 0) le_rfl
  simp only [orderedDerivative_zero] at hp'
  rw [hgrad, gradField_covPolyP Hc p hg]
  exact hp'.symm

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! # The lifted field of a stage is `C^J` in space

`menuLiftedRep Mn G m N depth CcT a` at a time `t` of the window is `C^J` if the coefficients of
the lift sequences of the slots are box smooth of order `(J, J)` (`J ≤ s_X, s_Z`) and `a t` is
`C^{N+J}`. The proof is that of `covTruncReg_gluedMeanFlux_contDiff` (the glued mean flux) with
`pulsePhysicalLift_contDiff'` in place of the Eulerian flux.

Degenerate cases: `J = 0`; `N = 0`; `t` outside every pulse window (the cutoffs vanish). -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The lifted field of the menu is `C^J` in space.** -/
theorem menuLiftedRep_contDiff (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N depth : ℕ)
    (hm : G.level = m)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (sX sZ : ℕ)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth
        (CcT k))
    (J : ℕ) (hJX : J ≤ sX) (hJZ : J ≤ sZ)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) :
    ContDiff ℝ (J : ℕ∞) (fun x => menuLiftedRep Mn G m N depth CcT a t x) := by
  subst hm
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hbase hprof hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hbase
  classical
  unfold menuLiftedRep gluedLift
  refine ContDiff.sum fun k hk => ?_
  by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
  · simp only [hcut, zero_smul]
    exact contDiff_const
  · refine ContDiff.const_smul _ ?_
    have hodd : Odd k := by
      unfold ocObsPulses at hk
      exact (Finset.mem_filter.1 hk).2.1
    have ht' := clock_mem_window D G.level k t hτ hcc hcut
    obtain ⟨-, -, -, -, -, hbox, -⟩ := hlift k hodd
    exact pulsePhysicalLift_contDiff' _ _ _ _ N depth (CcT k) _ _ a t hcc.ne'
      (fun hh hH n m α v u => (hbox hh hH n m α v u _ ht').1.mono hJX hJZ)
      ((CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
        (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top))
      ((CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)) ha

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The lifted field of a stage is jointly measurable in `(t, x)` on a window

* `pulsePhysicalLift_measurable`: the physical lift of one pulse, as a function of a time
  parameter and the point, is measurable when the coefficients are jointly measurable on the
  window of the sequence (`coeff_measurable`), the label map and the chart-frame coarse field
  are jointly measurable, and the chart-frame coarse field is `C^N` at each time. The lift is the
  finite coefficient sum of `labelLift_coeff_sum`; the word derivatives of the chart-frame field
  are measurable by `measurable_orderedDerivative`.
* `obsPulse_measurableSet`: the set of times at which a pulse is observed is measurable.
* `menuLiftedRep_measurable`: `(t, x) ↦ menuLiftedRep … a t x v` is measurable on the window
  subtype, for a coarse field `a` that is jointly measurable on the window and `C^N` at each time
  of it. The sum over the observed pulses of the time `t` is a sum over a fixed finite set of the
  indicators of the sets of times at which the pulse is observed.

Degenerate cases: a window with `t_p > t_f` (the subtype is empty); a pulse never observed on the
window (its indicator is `0`); `N = 0` (no derivative of the coarse field). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- Composition of measurable functions in lambda form (matching a goal in lambda form needs no
unfolding of the outer function). -/
theorem measurable_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (fun x => g (f x)) :=
  hg.comp hf

section Pulse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [DecidableEq ι] in
/-- **The physical lift of a pulse is jointly measurable** in a time parameter and the point. -/
theorem pulsePhysicalLift_measurable {T : Type*} [MeasurableSpace T] (τ : T → ℝ)
    (hτ : Measurable τ) (c ρ e εc : ℝ) (hc : c ≠ 0) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) {t₀ t₁ : ℝ}
    (hwin : ∀ t : T, c⁻¹ * τ t ∈ Set.Icc t₀ t₁)
    (hcoef : ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m) (v u : ι),
      Measurable (fun p : Set.Icc t₀ t₁ × (Vec 2 × Vec 2) => Cc hh n m α p.1.1 p.2.1 p.2.2 v u))
    (hlab : Measurable (fun p : T × Vec 2 => label (τ p.1) p.2))
    (hG : Measurable (fun p : T × Vec 2 => a (τ p.1) (chart (τ p.1) (ρ • p.2))))
    (hGs : ∀ t : T, ContDiff ℝ ((N : ℕ) : ℕ∞) (fun X => a (τ t) (chart (τ t) (ρ • X))))
    (v : ι) :
    Measurable (fun p : T × Vec 2 =>
      pulsePhysicalLift c ρ e εc N H Cc chart label a (τ p.1) p.2 v) := by
  have hclk : ∀ t : ℝ, c * (c⁻¹ * t) = t := fun t => by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hfun : (fun p : T × Vec 2 =>
      pulsePhysicalLift c ρ e εc N H Cc chart label a (τ p.1) p.2 v) =
      fun p : T × Vec 2 => ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), εc ^ n •
        ∑ q : LiftActionIndex ι n,
          Cc hh n q.1.val q.2.1 (c⁻¹ * τ p.1) (ρ⁻¹ • label (τ p.1) p.2)
            (e⁻¹ • label (τ p.1) p.2) v q.2.2
            (orderedDerivative q.2.1 (fun X => a (τ p.1) (chart (τ p.1) (ρ • X)))
              (ρ⁻¹ • label (τ p.1) p.2) q.2.2) := by
    funext p
    rw [pulsePhysicalLift_eq_comp, Function.comp_apply, labelLift_coeff_sum]
    simp only [hclk]
  rw [hfun]
  refine Finset.measurable_sum _ fun hh hhm => Finset.measurable_sum _ fun n hnm => ?_
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_sum _ fun q _ => ?_
  have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhm)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnm)
  have hqn : q.1.val ≤ n := Nat.lt_succ_iff.mp q.1.2
  have hclock : Measurable (fun p : T × Vec 2 => (⟨c⁻¹ * τ p.1, hwin p.1⟩ : Set.Icc t₀ t₁)) :=
    Measurable.subtype_mk ((hτ.comp measurable_fst).const_mul c⁻¹)
  have hC : Measurable (fun p : T × Vec 2 =>
      Cc hh n q.1.val q.2.1 (c⁻¹ * τ p.1) (ρ⁻¹ • label (τ p.1) p.2)
        (e⁻¹ • label (τ p.1) p.2) v q.2.2) :=
    (hcoef hh hhH n q.1.val q.2.1 v q.2.2).comp
      (hclock.prodMk ((hlab.const_smul ρ⁻¹).prodMk (hlab.const_smul e⁻¹)))
  have hD : Measurable (fun p : T × Vec 2 =>
      orderedDerivative q.2.1 (fun X => a (τ p.1) (chart (τ p.1) (ρ • X)))
        (ρ⁻¹ • label (τ p.1) p.2) q.2.2) := by
    have h1 := measurable_orderedDerivative q.1.val q.2.1
      (fun (t : T) (X : Vec 2) => a (τ t) (chart (τ t) (ρ • X)))
      (fun t => (hGs t).of_le (by exact_mod_cast hqn.trans hnN)) hG
    exact (measurable_pi_apply q.2.2).comp
      (h1.comp (measurable_fst.prodMk (hlab.const_smul ρ⁻¹)))
  exact isBoundedBilinearMap_apply.continuous.measurable.comp (hC.prodMk hD)

end Pulse

/-- **The set of times at which a pulse is observed is measurable.** -/
theorem obsPulse_measurableSet (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    MeasurableSet {t : ℝ | k ∈ ocObsPulses α q Λ m t t} := by
  have he : {t : ℝ | k ∈ ocObsPulses α q Λ m t t} =
      ((fun t : ℝ => ⌊t / ocTau α q Λ m⌋) ⁻¹' {j : ℤ | j - 1 ≤ k}) ∩
        ((fun t : ℝ => ⌈t / ocTau α q Λ m⌉) ⁻¹' {j : ℤ | k ≤ j + 1}) ∩
        {_t : ℝ | Odd k} ∩ ocPulseWindow α q Λ m k := by
    ext t
    simp only [ocObsPulses, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_preimage, Set.Icc_self, Set.inter_singleton_nonempty, and_assoc]
  rw [he]
  exact ((((Int.measurable_floor.comp (measurable_id.div_const _)) (MeasurableSet.of_discrete)).inter
    ((Int.measurable_ceil.comp (measurable_id.div_const _)) (MeasurableSet.of_discrete))).inter
    (MeasurableSet.const _)).inter measurableSet_Icc

section Menu

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The times of the window at which the pulse `k` of the level `m` is observed. -/
def ObsTimes (D : OCData) (m : ℕ) (tp tf : ℝ) (k : ℤ) : Set ℝ :=
  Set.Icc tp tf ∩ {t | k ∈ ocObsPulses D.α D.q D.Λ m t t}

theorem ObsTimes_measurableSet (D : OCData) (m : ℕ) (tp tf : ℝ) (k : ℤ) :
    MeasurableSet (ObsTimes D m tp tf k) :=
  measurableSet_Icc.inter (obsPulse_measurableSet _ _ _ _ k)

theorem ObsTimes_odd {D : OCData} {m : ℕ} {tp tf : ℝ} {k : ℤ} {t : ℝ}
    (ht : t ∈ ObsTimes D m tp tf k) : Odd k := by
  classical
  have hk : k ∈ ocObsPulses D.α D.q D.Λ m t t := ht.2
  unfold ocObsPulses at hk
  exact (Finset.mem_filter.1 hk).2.1

theorem ObsTimes_subset_pulse (D : OCData) (m : ℕ) (tp tf : ℝ) (k : ℤ) :
    ObsTimes D m tp tf k ⊆ ocPulseWindow D.α D.q D.Λ m k := by
  classical
  intro t ht
  have hk : k ∈ ocObsPulses D.α D.q D.Λ m t t := ht.2
  unfold ocObsPulses at hk
  obtain ⟨s, hs1, hs2⟩ := (Finset.mem_filter.1 hk).2.2
  rw [Set.Icc_self, Set.mem_singleton_iff] at hs2
  rw [← hs2]
  exact hs1

/-- One pulse term of the lifted field: the cutoff times the physical lift of the pulse. -/
def PulseTerm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (k : ℤ) (t : ℝ)
    (y : Vec 2) : hr v.1.root :=
  ocCutoff D.α D.q D.Λ G.level k t •
    pulsePhysicalLift (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
      (D.eps G.level)
      (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
        (Mn.lenFactor * liftLength D G.level)) N depth (CcT k)
      (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
      (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') a t y v

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] in
/-- **The lifted field is the sum of its pulse terms over any finite set containing the observed
pulses.** -/
theorem menuLiftedRep_eq_sum (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (K₀ : Finset ℤ) (t : ℝ) (y : Vec 2)
    (hsub : ocObsPulses D.α D.q D.Λ G.level t t ⊆ K₀) :
    menuLiftedRep Mn G G.level N depth CcT a t y v =
      ∑ k ∈ K₀, if k ∈ ocObsPulses D.α D.q D.Λ G.level t t then
        PulseTerm Mn G N depth CcT a v k t y else 0 := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  unfold menuLiftedRep gluedLift PulseTerm
  rw [Finset.sum_apply]
  rfl

/-- **One pulse term of the lifted field on a set of times at which it is observed.** -/
theorem menuPulse_measurable (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (N depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hcc : 0 < D.cellScaleSq G.level) (sX sZ : ℕ) (k : ℤ) (hk : Odd k)
    (hlift : IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k)
          (Mn.lenFactor * liftLength D G.level)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N depth
        (CcT k))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (tp tf : ℝ)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((N : ℕ) : ℕ∞) (a t))
    (ham : Measurable (fun p : Set.Icc tp tf × Vec 2 => a p.1.1 p.2))
    (E : Set ℝ) (hE1 : E ⊆ Set.Icc tp tf) (hE2 : E ⊆ ocPulseWindow D.α D.q D.Λ G.level k)
    (v : CompIn G.comps) :
    Measurable (fun p : E × Vec 2 => PulseTerm Mn G N depth CcT a v k p.1.1 p.2) := by
  have hflow : Continuous (fun p : ℝ × Vec 2 × ℝ => D.flowOf (G.level - 1) p.1 p.2.1 p.2.2) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (G.level - 1))).continuous
  have hlab : Measurable (fun p : E × Vec 2 =>
      D.flowOf (G.level - 1) (D.slotAnchor G.level k) p.2 p.1.1) :=
    (hflow.comp (continuous_const.prodMk
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)))).measurable
  have hchart : Measurable (fun p : E × Vec 2 =>
      D.flowOf (G.level - 1) p.1.1 ((Mn.lenFactor * liftLength D G.level) • p.2)
        (D.slotAnchor G.level k)) :=
    (hflow.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_snd.const_smul (Mn.lenFactor * liftLength D G.level)).prodMk
        continuous_const))).measurable
  have hwindow : Measurable (fun p : E × Vec 2 => (⟨p.1.1, hE1 p.1.2⟩ : Set.Icc tp tf)) :=
    Measurable.subtype_mk (measurable_subtype_coe.comp measurable_fst)
  have hG : Measurable (fun p : E × Vec 2 =>
      a p.1.1 (D.flowOf (G.level - 1) p.1.1 ((Mn.lenFactor * liftLength D G.level) • p.2)
        (D.slotAnchor G.level k))) :=
    ham.comp (hwindow.prodMk hchart)
  have hGs : ∀ t : E, ContDiff ℝ ((N : ℕ) : ℕ∞) (fun X : Vec 2 =>
      a t.1 (D.flowOf (G.level - 1) t.1 ((Mn.lenFactor * liftLength D G.level) • X)
        (D.slotAnchor G.level k))) := by
    intro t
    have h1 : ContDiff ℝ ((N : ℕ) : ℕ∞)
        (fun y : Vec 2 => D.flowOf (G.level - 1) t.1 y (D.slotAnchor G.level k)) :=
      (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t.1
        (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
    have h2 : ContDiff ℝ ((N : ℕ) : ℕ∞)
        (fun X : Vec 2 => (Mn.lenFactor * liftLength D G.level) • X) :=
      contDiff_const_smul _
    exact (ha t.1 (hE1 t.2)).comp (h1.comp h2)
  have hpulse := pulsePhysicalLift_measurable (T := E) (fun t => t.1)
    measurable_subtype_coe (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
    (D.eps G.level)
    (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      (Mn.lenFactor * liftLength D G.level)) hcc.ne' N depth (CcT k)
    (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
    (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s') a
    (t₀ := D.slotStart G.level k / D.cellScaleSq G.level)
    (t₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
    (fun t => by
      obtain ⟨h1, h2⟩ := hE2 t.2
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right h1 hcc.le, div_le_div_of_nonneg_right h2 hcc.le⟩)
    (fun hh hhH n m' α v' u' => coeff_measurable hlift hhH n m' α v' u')
    hlab hG hGs v
  have hcut : Measurable (fun p : E × Vec 2 => ocCutoff D.α D.q D.Λ G.level k p.1.1) :=
    (CycleReference.ocCutoff_contDiff hbase k).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_fst)
  unfold PulseTerm
  exact hcut.smul hpulse

/-- **One pulse term, cut off outside the times at which the pulse is observed, is jointly
measurable.** -/
theorem pulseIndicator_measurable (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (N depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hcc : 0 < D.cellScaleSq G.level) (sX sZ : ℕ)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k)
          (Mn.lenFactor * liftLength D G.level)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N depth
        (CcT k))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (tp tf : ℝ)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((N : ℕ) : ℕ∞) (a t))
    (ham : Measurable (fun p : Set.Icc tp tf × Vec 2 => a p.1.1 p.2))
    (v : CompIn G.comps) (k : ℤ) :
    Measurable ((Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)).indicator
      (fun p => PulseTerm Mn G N depth CcT a v k p.1 p.2)) := by
  have hS : MeasurableSet (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)) :=
    measurable_fst (ObsTimes_measurableSet D G.level tp tf k)
  refine measurable_indicator hS _ ?_
  by_cases hne : Nonempty (ObsTimes D G.level tp tf k)
  · obtain ⟨t0⟩ := hne
    have hk : Odd k := ObsTimes_odd t0.2
    have hpulse := menuPulse_measurable Mn G N depth CcT hbase hcc sX sZ k hk
      (hlift k hk) a tp tf ha ham (ObsTimes D G.level tp tf k) Set.inter_subset_left
      (ObsTimes_subset_pulse D G.level tp tf k) v
    have hmap : Measurable
        (fun z : ↥(Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)) =>
          ((⟨z.1.1, z.2⟩ : ObsTimes D G.level tp tf k), z.1.2)) :=
      (Measurable.subtype_mk (measurable_fst.comp measurable_subtype_coe)).prodMk
        (measurable_snd.comp measurable_subtype_coe)
    have hcomp := measurable_comp
      (g := fun p : ObsTimes D G.level tp tf k × Vec 2 =>
        PulseTerm Mn G N depth CcT a v k p.1.1 p.2) hpulse hmap
    exact hcomp
  · have hem : IsEmpty ↥(Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)) :=
      ⟨fun z => hne ⟨⟨z.1.1, z.2⟩⟩⟩
    exact measurable_of_empty _

/-- **The lifted field of the menu is jointly measurable** on the window. -/
theorem menuLiftedRep_measurable (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (m N depth : ℕ) (hm : G.level = m)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (sX sZ : ℕ)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth
        (CcT k))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (tp tf : ℝ)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((N : ℕ) : ℕ∞) (a t))
    (ham : Measurable (fun p : Set.Icc tp tf × Vec 2 => a p.1.1 p.2))
    (v : CompIn G.comps) :
    Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} =>
      menuLiftedRep Mn G m N depth CcT a z.1.1 z.1.2 v) := by
  subst hm
  classical
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hbase hprof hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hbase
  have hsum : Measurable (fun p : ℝ × Vec 2 =>
      ∑ k ∈ Finset.Icc (⌊tp / ocTau D.α D.q D.Λ G.level⌋ - 1)
        (⌈tf / ocTau D.α D.q D.Λ G.level⌉ + 1),
        (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)).indicator
          (fun p => PulseTerm Mn G N depth CcT a v k p.1 p.2) p) :=
    Finset.measurable_sum _ fun k _ =>
      pulseIndicator_measurable Mn G N depth CcT hbase hcc sX sZ hlift a tp tf ha ham v k
  have hfun : (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} =>
      menuLiftedRep Mn G G.level N depth CcT a z.1.1 z.1.2 v) =
      fun z => ∑ k ∈ Finset.Icc (⌊tp / ocTau D.α D.q D.Λ G.level⌋ - 1)
        (⌈tf / ocTau D.α D.q D.Λ G.level⌉ + 1),
        (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)).indicator
          (fun p => PulseTerm Mn G N depth CcT a v k p.1 p.2) z.1 := by
    funext z
    obtain ⟨⟨t, y⟩, ht⟩ := z
    have ht' : t ∈ Set.Icc tp tf := ht
    have hsub : ocObsPulses D.α D.q D.Λ G.level t t ⊆
        Finset.Icc (⌊tp / ocTau D.α D.q D.Λ G.level⌋ - 1)
          (⌈tf / ocTau D.α D.q D.Λ G.level⌉ + 1) := by
      intro k hk
      unfold ocObsPulses at hk
      have hk' := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
      have h1 : ⌊tp / ocTau D.α D.q D.Λ G.level⌋ ≤ ⌊t / ocTau D.α D.q D.Λ G.level⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right ht'.1 hτ.le)
      have h2 : ⌈t / ocTau D.α D.q D.Λ G.level⌉ ≤ ⌈tf / ocTau D.α D.q D.Λ G.level⌉ :=
        Int.ceil_mono (div_le_div_of_nonneg_right ht'.2 hτ.le)
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    show menuLiftedRep Mn G G.level N depth CcT a t y v =
      ∑ k ∈ Finset.Icc (⌊tp / ocTau D.α D.q D.Λ G.level⌋ - 1)
        (⌈tf / ocTau D.α D.q D.Λ G.level⌉ + 1),
        (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)).indicator
          (fun p => PulseTerm Mn G N depth CcT a v k p.1 p.2) (t, y)
    rw [menuLiftedRep_eq_sum Mn G N depth CcT a v _ t y hsub]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ ocObsPulses D.α D.q D.Λ G.level t t
    · simp only [hk, ↓reduceIte]
      exact (Set.indicator_of_mem
        (show (t, y) ∈ (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)) from
          ⟨ht', hk⟩)
        (fun p : ℝ × Vec 2 => PulseTerm Mn G N depth CcT a v k p.1 p.2)).symm
    · simp only [hk, ↓reduceIte]
      exact (Set.indicator_of_notMem
        (show (t, y) ∉ (Prod.fst ⁻¹' ObsTimes D G.level tp tf k : Set (ℝ × Vec 2)) from
          fun hmem => hk hmem.2)
        (fun p : ℝ × Vec 2 => PulseTerm Mn G N depth CcT a v k p.1 p.2)).symm
  rw [hfun]
  have hcomp := measurable_comp hsum
    (measurable_subtype_coe (p := fun z : ℝ × Vec 2 => z.1 ∈ Set.Icc tp tf))
  exact hcomp

end Menu

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The lifted field of a stage is periodic

`menuLiftedRep` at a time `t` is `ℤ²`-periodic if the coarse field `a t` is, the coefficients of
the active pulses are slow-periodic (the slow lattice `ρ⁻¹ ℤ²`; at the terminal context this is
`CovTruncLiftSlowAt`) and fast-periodic (the lift sequence), and the flow charts are
lattice equivariant (`native_flow_latticeShift`). The proof is
`nativeStageLiftFamily_glued_periodic` with the coefficients supplied by hypotheses.

Degenerate cases: no active pulse (the field is `0`); `a t = 0`. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The lifted field of the menu is periodic.** -/
theorem menuLiftedRep_periodic (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (m N depth : ℕ) (hm : G.level = m)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hρ : Mn.lenFactor * liftLength D m ≠ 0) (hc : D.cellScaleSq m ≠ 0) (sX sZ : ℕ)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        sX sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N depth
        (CcT k))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hbase : 1 ≤ D.Λ) (hcc : 0 < D.cellScaleSq m)
    (hslow : ∀ k ∈ ocObsPulses D.α D.q D.Λ m t t, ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      ∀ (p : Fin 2 → ℤ) hh, hh ≤ depth → ∀ n m' (α : DerivativeWord2 m') X z v u,
        CcT k hh n m' α ((D.cellScaleSq m)⁻¹ * t)
          (X + (Mn.lenFactor * liftLength D m)⁻¹ • latticeShift p) z v u =
        CcT k hh n m' α ((D.cellScaleSq m)⁻¹ * t) X z v u)
    (ha : IsZ2Periodic (a t)) :
    IsZ2Periodic (fun x => menuLiftedRep Mn G m N depth CcT a t x) := by
  classical
  subst hm
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hbase
  obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ G.level
  have hclock : D.cellScaleSq G.level * ((D.cellScaleSq G.level)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  intro p x
  simp only [menuLiftedRep, gluedLift]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
  · simp only [hcut, zero_smul]
  · apply congrArg (fun y => ocCutoff D.α D.q D.Λ G.level k t • y)
    have hodd : Odd k := by
      unfold ocObsPulses at hk
      exact (Finset.mem_filter.1 hk).2.1
    have ht' := clock_mem_window D G.level k t hτ hcc hcut
    obtain ⟨-, -, -, -, -, hbox, -⟩ := hlift k hodd
    rw [pulsePhysicalLift_freeze_time, hclock]
    exact pulsePhysicalLift_static_periodic _ _ _ _ N depth (CcT k) _ _ (a t) t hρ
      (J := J) hJ (fun p Y => native_flow_latticeShift D _ _ _ p Y)
      (fun p Y => native_flow_latticeShift D _ _ _ p Y) ha
      (fun hh hhH n _ m' _ α p X z v u => hslow k hk hcut p hh hhH n m' α X z v u)
      (fun hh hhH n _ m' _ α X v u => (hbox hh hhH n m' α v u _ ht').2 X) p x

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
section
/-! # The defect of the derivative array: the jet bound (generic)

For a torus field `V ∈ H^{K+1}` with a classical representative `a`, a moving paired kernel `S`
with vanishing moments through `L`, the realization `Y = kdRealization … (trunc V)` of
`(I - S(t))a` of order `k + (m+1)` has the `(m+1)`-st derivative array bounded by the gradient
of `V`:

`|∇^{m+1} Y|²_{ρ,k} ≤ (C₀ ((k+m+L)!/k!) (r/ρ)^L ρ^{-m})² |∇V|²_{ρ,k+m+L}`

(`fd_derivFactorialNormSq_le_of_order_le`). This is the term bound of the defect version of
`kernel_flux_bound_torus`: the regularizer `S` lifting `H^k → H^{k+j}` is replaced by the defect
`I - S`, which maps `H^{k+L+j} → H^{k+j}` and gains `(r/ρ)^L`. Generic: no stage, no context
(shared with the filter tails). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The weight inequality with the derivative shift `s = m + L` split as `r^{2L} ρ^{-2m}`. -/
theorem fd_weight_shift {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) {i k : ℕ} (m L : ℕ) (hi : i ≤ k) :
    factorialWeight ρ i * r ^ (2 * L) ≤
      (((k + (L + m)).factorial : ℝ) / k.factorial) ^ 2 * (r / ρ) ^ (2 * L) *
        (ρ⁻¹) ^ (2 * m) * factorialWeight ρ (i + (L + m)) := by
  have h := kd_weight_shift (ρ := ρ) (r := r) hρ hr.le (L + m) hi
  have hr2 : (0 : ℝ) < r ^ (2 * m) := pow_pos hr _
  have e1 : (r / ρ) ^ (2 * (L + m)) = (r / ρ) ^ (2 * L) * (r ^ (2 * m) * (ρ⁻¹) ^ (2 * m)) := by
    rw [mul_add, pow_add, div_eq_mul_inv, mul_pow (r) (ρ⁻¹) (2 * m)]
  have e2 : r ^ (2 * (L + m)) = r ^ (2 * L) * r ^ (2 * m) := by rw [mul_add, pow_add]
  rw [e2, e1] at h
  have h2 : factorialWeight ρ i * r ^ (2 * L) * r ^ (2 * m) ≤
      ((((k + (L + m)).factorial : ℝ) / k.factorial) ^ 2 * (r / ρ) ^ (2 * L) *
        (ρ⁻¹) ^ (2 * m) * factorialWeight ρ (i + (L + m))) * r ^ (2 * m) := by
    calc _ = factorialWeight ρ i * (r ^ (2 * L) * r ^ (2 * m)) := by ring
      _ ≤ _ := h
      _ = _ := by ring
  exact le_of_mul_le_mul_right h2 hr2

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The coarse pair of the engine from the energy bound

From `ReconEnergyAt c x kc ℓ hW Cs` (the energy step: `W = P_pZ` continuous in time on the window with
`strongEnergyUpTo (ρ_rec) κ_{M-1} π t_p (a+T₀) (rpord) W ≤ C_s ‖f‖₂`) and an order `n` with
`n + 1 ≤ k_c + 1 + N_T + D_t` and `n ≤ rpord`: the truncations `Z` of order `n` and `Z_w` of order
`n + 1` of `W` are classical representatives of the prepared field `aRep` (a.e. in time for `Z_w`
trivially everywhere), `Z_w` is strongly measurable in time, and the strong energy of `(Z, Z_w)` at
`(ρ_rec, κ_{M-1})` is at most `C_s ‖f‖₂`.

Degenerate case: `C_s = 0` and `f = 0` gives energy `0`. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The coarse pair `(Z, Z_w)` of the engine from the energy bound.** -/
theorem coarse
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) {Cs : ℝ}
    (hR : ReconEnergyAt c x kc ℓ hW Cs) {n : ℕ} (hn : n + 1 ≤ kc + 1 + (A.NT + A.Dt))
    (hnm : n ≤ rpord A ℓ) :
    ∃ (Z : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk n (ScalarH v.1.root))
      (Zw : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (n + 1) (ScalarH v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), IsClassicalRep (Z v t) (fun y => c.aRep t y v) n) ∧
      (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
        IsClassicalRep (Zw v t) (fun y => c.aRep t y v) (n + 1)) ∧
      (∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
      strongEnergy (liftLength c.D M) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Z Zw ≤
        ENNReal.ofReal (Cs * c.normF) := by
  have hn0 : n ≤ kc + 1 + (A.NT + A.Dt) := Nat.le_of_succ_le hn
  refine ⟨fun v t => truncateTorusHk hn0 (reconW c kc hW v t),
    fun v t => truncateTorusHk hn (reconW c kc hW v t), ?_, ?_, ?_, ?_⟩
  · intro v t ht
    exact Construction.Preservation.FullLift.classicalRep_truncate hn0 le_rfl _ _
      (Construction.Preservation.FullLift.classicalRep_truncate hW (by omega) (c.PZ v t)
        (fun y => c.aRep t y v) (rdJets_classicalRep_mono (c.lift.2.1 v t ht).2 (by omega)))
  · intro v t ht
    exact Construction.Preservation.FullLift.classicalRep_truncate hn (by omega) _ _
      (Construction.Preservation.FullLift.classicalRep_truncate hW (by omega) (c.PZ v t)
        (fun y => c.aRep t y v) (rdJets_classicalRep_mono (c.lift.2.1 v t ht).2 (by omega)))
  · intro v
    have hI : c.tp + rTobs c = c.a + A.T₀ := by simp only [rTobs]; ring
    have hc := hR.1 v
    rw [hI] at hc
    exact ((truncateTorusHk hn).continuous.comp_continuousOn hc).aestronglyMeasurable
      measurableSet_Icc
  · have h2 := hR.2
    have hI : c.tp + rTobs c = c.a + A.T₀ := by simp only [rTobs]; ring
    rw [hI] at h2
    exact le_trans (strongEnergy_truncate_le_upTo (by omega) hnm _ _ _ _ _ _) h2

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # A native slot lift per odd slot from the terminal setting and the lift
sequences

`native_slot_lifts`: the native lift settings of `native_setting` (at `cr = 1`), a lift sequence of
the lift data at the stored orders `(K + Dt + 2, max (kk + 1) (L + 2))` for the coefficients `CcT`
(`LiftSeqClause`), and the window / effective-order restrictions of the sequence give a
`NativeSlotLift` for every odd slot with `coeff = CcT slot`, `S = Θmax`.

Degenerate case: the window is a point `a = b`: the restrictions are the identity on the stored
data. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients.Recon.Setting AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- A lift sequence of `Q` on `[a, b]` is one of the data with the clamped window edges. -/
theorem seq_window {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
    (Q : LiftOperatorData ι h D) (a b : ℝ) (sX sZ N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence {Q with edge := windowEdges a b Q.edge} sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X
  apply CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t ht
  funext z
  exact (EntryWeakProofs.liftCellSource_edge_slow_open_congr isOpen_univ Q
    (windowEdges a b Q.edge) Cc (fun _ => f) hh n t
    (windowEdges_agree a b Q.edge t ht) X (Set.mem_univ X) z)

/-- The lift sequence of the restricted, window-clamped data. -/
theorem seq_restricted {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {D : ℕ} (Q : LiftOperatorData ι h D) (a b : ℝ) (cap : ℕ) (hcap : cap ≤ D)
    (hz : ∀ v u d, cap < d.val → Q.edge v u d = []) (sX sZ N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hNK : N ≤ cap)
    (hc : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence (restrictLiftData cap hcap {Q with edge := windowEdges a b Q.edge}) sX sZ a b
      N H Cc := by
  have h1 := seq_window Q a b sX sZ N H Cc hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h1
  refine ⟨c1, c2, c3, c4, c5, c6, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hi := c7 hh hhh n hn hnN f hf X
  apply CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t _
  funext z
  exact congrFun (congrFun (EntryWeakProofs.liftCellSource_restrict_effective_order cap hcap
    {Q with edge := windowEdges a b Q.edge}
    (fun v u d hd => by
      show windowEdges a b Q.edge v u d = []
      exact (windowEdges_empty_iff a b Q.edge v u d).mpr (hz v u d hd)) Cc
    (fun _ => f) hh n (hnN.trans hNK) t) X) z

/-- **The native slot lifts of the terminal weak stage.** -/
theorem native_slot_lifts {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} (D : OCData) (m : ℕ)
    (Gw : GenStage D ScalarH Dt bw j₀) (hlev : Gw.level = m) (law : BirthLaw) (Θmax : ℝ)
    (N H K kk L sX sZ : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (hDt : 2 ≤ Dt)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (hseq : LiftSeqClause Gw m N H sX sZ CcT) (hsX : K + Dt + 2 ≤ sX)
    (hsZ : max (kk + 1) (L + 2) ≤ sZ) (hNK : N ≤ Dt)
    (hset : ∀ (k : ℤ) (hk : Odd k), NativeSlotSetting D m Gw law 1 Θmax N H K kk L CG Cw Cj k hk) :
    ∀ slot : OddSlot,
      Nonempty (NativeSlotLift Gw slot (Gw.mass law) H N K kk L CG Cw Cj Θmax) := by
  intro slot
  subst hlev
  obtain ⟨Θ, hΘ, hs⟩ := hset slot.1 slot.2
  have hs' : IsLiftSetting
      (restrictLiftData Dt le_rfl
        {familyLiftData D Gw.level slot.1 (nativeChain Gw.level slot.1) (liftLength D Gw.level)
            (Gw.fam.fiber slot (Gw.actual slot)) with
          edge := windowEdges (D.slotStart Gw.level slot.1 / D.cellScaleSq Gw.level)
            ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ Gw.level) / D.cellScaleSq Gw.level)
            (familyLiftData D Gw.level slot.1 (nativeChain Gw.level slot.1)
              (liftLength D Gw.level) (Gw.fam.fiber slot (Gw.actual slot))).edge})
      (Gw.mass law) (D.slotStart Gw.level slot.1 / D.cellScaleSq Gw.level)
      ((((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ Gw.level) / D.cellScaleSq Gw.level)
      (D.eps Gw.level) (D.kap Gw.level) (D.kap (Gw.level - 1)) (liftLength D Gw.level)
      (D.eps (Gw.level - 1)) (D.eps Gw.level / Real.sqrt (D.kap Gw.level))
      (ocDStar D.q D.Λ Gw.level (D.kap Gw.level) (D.kap (Gw.level - 1)))
      (ocDStar D.q D.Λ Gw.level (D.kap Gw.level) (D.kap (Gw.level - 1)) / liftLength D Gw.level)
      (liftLength D Gw.level / D.eps (Gw.level - 1)) (pulseParallel slot.1)
      (pulseShearProfile D.α D.q D.Λ Gw.level D.ζ (D.kap Gw.level) slot.1)
      H N K kk L (K + 4 * (H + 1) * (N + Dt) ^ 2)
      (max kk (L + 2) + H * Dt + 2 * N + 2 * Dt) CG Cw Cj
      (recordMajorant (Gw.mass law) Gw.fam) Θ := by
    simpa only [one_mul] using hs
  have hz : ∀ v u d, Dt < d.1 →
      (familyLiftData D Gw.level slot.1 (nativeChain Gw.level slot.1) (liftLength D Gw.level)
        (Gw.fam.fiber slot (Gw.actual slot))).edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hamb := CycleComparison.Reconstruction.isLiftSequence_mono (hseq slot.1 slot.2) (sX' := K + Dt + 2)
    (sZ' := max (kk + 1) (L + 2)) hsX hsZ
  exact ⟨
    { cap := Dt
      cap_le := le_rfl
      cap_ge := hDt
      empty := hz
      setting := isLiftSetting_mono_const hs' (fun _ _ _ _ => le_rfl) hΘ
      coeff := CcT slot.1
      restricted := seq_restricted _ _ _ Dt le_rfl hz _ _ N H _ hNK hamb
      ambient := hamb }⟩

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! Slow periodicity of the supplied lift coefficients. The lift-sequence and lift-setting steps are joined using
ReconPrefixU; the family step supplies the torus-compatible actual family. For periodicity the fixed order
offset zero suffices, since the coefficient uniqueness theorem covers every cell degree. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.CycleComparison.Assembly

namespace AVRegularity.Construction.Residual.Presentation

section Context
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The supplied coefficients at an active observation pulse are slow-periodic in the native
physical label radius. This includes all cell degrees, but only the constrained grades. -/
def CovTruncLiftSlowAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) : Prop :=
  ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M t t,
    ocCutoff c.D.α c.D.q c.D.Λ M k t ≠ 0 →
    ∀ (p : Fin 2 → ℤ) hh, hh ≤ A.dW → ∀ n m (α : DerivativeWord2 m) X z v u,
      c.CcT k hh n m α ((c.D.cellScaleSq M)⁻¹ * t)
        (X + (cr * liftLength c.D M)⁻¹ • latticeShift p) z v u =
      c.CcT k hh n m α ((c.D.cellScaleSq M)⁻¹ * t) X z v u

/-- At a context, the lift-sequence, lift-setting and family steps give the slow coefficient periodicity used by the mean flux. -/
theorem covTruncLiftSlow_of_setting
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hcP : 0 < cP)
    (hdl : c.tp < c.a + A.T₀) (hseq : ReconSeqAt c 0)
    (CG CwL : ℕ → ℝ) (Ca Sb Cg : ℝ) (hset : ReconSettingAt c x 0 CG CwL Ca Sb Cg) :
    CovTruncLiftSlowAt c := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos hΛ1
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hcs : ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 = c.D.cellScaleSq M := by
    rw [CycleReference.ocEll_sq_eq hν]
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
  have hcell : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 := by
    rw [hcs]
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hν
  obtain ⟨T, hf⟩ := Family.reconFamilyAt_of_ctx c hcP (by omega) 0 hdl
  have htorus := hf.2.1
  obtain ⟨qs, qf, par, V, bM, hsetting, -⟩ := hset
  intro t ht k hk hcut p hh hhH n m α Y z v u
  have ht' : t ∈ Set.Icc c.tp (c.tp + rTobs c) := by
    have hend : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
    rwa [hend]
  have hkobs := obsPulses_time_subset c.D.α c.D.q c.D.Λ M hτ ht' hk
  have hwin := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have htcell := cellTime_mem_liftWindow hcell hwin ht'
  have P := hsetting k hkobs
  have hperiod := setting_liftSequence_slowShift_invariant P
    (rKlift A 0 + A.Dt + 2) (max (rLlift A 0 + 1) (rLlift A 0 + 2))
    (c.CcT k) (hseq k hkobs) ((rRho c)⁻¹ • latticeShift p)
    (fun s Y i j => pulseLiftData_G_shift c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.hΦ (M - 1))
      (c.D.κ M) (c.D.κ (M - 1)) P.ρ_pos.ne' _ k _ p s Y i j)
    (fun v u d γ hγ α s Y z => liftEdges_fiber_coeff_shift P.ρ_pos.ne' htorus
      (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (oddSlotOf k) p hγ α s Y z)
    hh hhH n m α _ htcell Y z v u
  have hρ : cr * liftLength c.D M = rRho c :=
    (congrArg (· * liftLength c.D M) x.one).trans (one_mul _)
  rw [hcs, ← hρ] at hperiod
  exact hperiod
end Context

/-- Slow periodicity with the exact terminal residual prefix. -/
def CovTruncLiftSlowStatement : Prop :=
  TermResPrefix fun c _ _ _ _ _ _ => CovTruncLiftSlowAt c

/-- The uniform prefix of the lift-sequence and lift-setting steps supplies the slow periodicity. Offset zero is enough for this
qualitative assertion; every coefficient degree is covered by the shift uniqueness theorem. -/
theorem covTruncLiftSlow : CovTruncLiftSlowStatement := by
  have hU := (((termReconSeq.and termReconTimes).and termReconFloors).and termReconSetting)
  intro X
  obtain ⟨Λ₀, h128, hu⟩ := hU X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := h128.trans hΛ
  obtain ⟨kc₀, hu⟩ := hu A hΛ hV 0
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hu⟩ := hu kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hu⟩ := hu sXT sZT hX hZ Kout hK
  refine ⟨Kn, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hone hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨k, CH, Υ, hCH, hΥ, hu⟩ := hu Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hone
    hkS hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP
  refine ⟨0, 1, 1, one_pos, CH, Υ, hCH, hΥ, fun C _ j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hu⟩ := hu j₀ hj₀
  refine ⟨M₀, fun M hM c x => ?_⟩
  obtain ⟨⟨⟨hs, ht⟩, hf⟩, hset⟩ := hu M hM c x
  exact covTruncLiftSlow_of_setting c x hΛ128 hcP ht.2 (hs hf.1 hf.2 ht.1)
    k.2.1.1 k.2.1.2.1 k.2.1.2.2.1 k.2.1.2.2.2.1 k.2.1.2.2.2.2 hset

end AVRegularity.Construction.Residual.Presentation
end
end
end
