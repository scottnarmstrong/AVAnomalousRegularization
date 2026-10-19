-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
public import AVRegularity.CycleComparison.Lift.TruncatedMeanCoefficientRegularity
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

section
@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A fast directional derivative consumes exactly one fast jet in the mixed majorant. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jetApply_norm_le (q : ℕ) (v : Vec 2) : ‖jetApply (F := E) q v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  change ‖f (Fin.snoc w v)‖ ≤ (‖v‖ * ‖f‖) * ∏ i, ‖w i‖
  have h := f.le_opNorm (Fin.snoc w v)
  simp only [Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] at h
  convert h using 1
  ring

theorem norm_mixed_fast_direction_le {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r (q + 1) f) (v : Vec 2) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (fun y => fderiv ℝ (f Y) y v) z) X‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) X‖ := by
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => fderiv ℝ (f Y) y v) z) =
      (jetApply q v) ∘ (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) := by
    funext Y
    exact iteratedFDeriv_fderiv_apply (hf.1 Y).contDiffAt v
  rw [he]
  have hb := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
    (jetApply (F := E) q v) (f := fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z)
    (x := X) (n := r) (hf.2.1 (q + 1) le_rfl z).contDiffAt le_rfl
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (jetApply_norm_le (E := E) q v) (norm_nonneg _)
end

/-! Real smooth coordinate derivatives remain smooth and commute, without an analytic premise. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordinateDerivative (k : Fin 2) (f : Vec 2 → E) : Vec 2 → E :=
  fun X => fderiv ℝ f X (basisVec k)

theorem coordinateDerivative_contDiff (k : Fin 2) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative k f) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hd.clm_apply contDiff_const

theorem coordinateDerivative_second (i j : Fin 2) (f : Vec 2 → E)
    (hf : ContDiff ℝ 2 f) (X : Vec 2) :
    coordinateDerivative j (coordinateDerivative i f) X =
      fderiv ℝ (fderiv ℝ f) X (basisVec j) (basisVec i) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he := ((ContinuousLinearMap.apply ℝ E (basisVec i)).hasFDerivAt.comp X
    ((hd.differentiable one_ne_zero) X).hasFDerivAt).fderiv
  change fderiv ℝ (fun Y => fderiv ℝ f Y (basisVec i)) X (basisVec j) = _
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply] using congrArg (fun L : Vec 2 →L[ℝ] E => L (basisVec j)) he

theorem coordinateDerivative_commute (i j : Fin 2) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivative j (coordinateDerivative i f) = coordinateDerivative i (coordinateDerivative j f) := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  funext X
  rw [coordinateDerivative_second i j f h2 X, coordinateDerivative_second j i f h2 X]
  exact (h2.contDiffAt.isSymmSndFDerivAt (by simp)) (basisVec j) (basisVec i)
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Identification of the actual scalar ODE solution with the measurable-metric Duhamel response. -/

theorem transverseMode_eq_response (rate : ℝ) (g f u : ℝ → ℝ) (a b : ℝ)
    (hi : IntervalIntegrable g volume a b) (hu : AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt u (-rate * g t * u t + f t) t)
    (hzero : u a = 0) : u b = transverseModeResponse rate g f a b := by
  have he := transverseMode_weighted_identity rate g f u a b hi hu hd
  rw [hzero, sub_zero] at he
  have hfactor : (∫ s in a..b, transverseModeKernel rate g s b * f s) =
      transverseModeKernel rate g a b * ∫ s in a..b, transverseModeKernel (-rate) g a s * f s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [transverseModeKernel_factor rate g a b s hi hs, mul_assoc]
  unfold transverseModeResponse
  simp only [smul_eq_mul]
  rw [hfactor, ← he, ← mul_assoc, transverseModeKernel_opposite_rates, one_mul]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! A finite sum of normalized reserved jets supplies one uniform constituent majorant. -/

def constituentUniformMixedBudget (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    (jetSup I r s f).toReal * (lam ^ r)⁻¹

theorem constituentUniformMixedBudget_nonneg (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) (f : ℝ → Vec 2 → Vec 2 → Vec 2) :
    0 ≤ constituentUniformMixedBudget I p q lam f := by
  unfold constituentUniformMixedBudget
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
    mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr (pow_nonneg hlam r))

theorem coefficient_mixed_jet_norm_le_toReal (I : Set ℝ) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) (hf : jetSup I r q f < ⊤)
    (t : ℝ) (ht : t ∈ I) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f t Y) z) X‖ ≤
      (jetSup I r q f).toReal := by
  apply (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal hf.ne]
  simpa only [jetSup, ← ofReal_norm] using
    (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le X (le_iSup_of_le z le_rfl))) :
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f t Y) z) X‖ₑ ≤ jetSup I r q f)

theorem constituentUniformMixedBudget_bounds (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (hlam : 0 < lam) (f : ℝ → Vec 2 → Vec 2 → Vec 2)
    (hfin : ∀ r ≤ p, ∀ s ≤ q, jetSup I r s f < ⊤)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (t : ℝ) (ht : t ∈ I) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (f t Y) z) X‖ ≤
      constituentUniformMixedBudget I p q lam f * lam ^ r := by
  have hinner : (jetSup I r s f).toReal * (lam ^ r)⁻¹ ≤
      ∑ b ∈ Finset.range (q + 1), (jetSup I r b f).toReal * (lam ^ r)⁻¹ := by
    apply Finset.single_le_sum (f := fun b => (jetSup I r b f).toReal * (lam ^ r)⁻¹) (a := s)
    · intro b _
      positivity
    · exact Finset.mem_range.mpr (by omega)
  have houter : (∑ b ∈ Finset.range (q + 1),
      (jetSup I r b f).toReal * (lam ^ r)⁻¹) ≤ constituentUniformMixedBudget I p q lam f := by
    unfold constituentUniformMixedBudget
    apply Finset.single_le_sum
      (f := fun a => ∑ b ∈ Finset.range (q + 1), (jetSup I a b f).toReal * (lam ^ a)⁻¹) (a := r)
    · intro a _
      exact Finset.sum_nonneg fun b _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)
    · exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ (jetSup I r s f).toReal := coefficient_mixed_jet_norm_le_toReal I r s f (hfin r hr s hs) t ht X z
    _ = ((jetSup I r s f).toReal * (lam ^ r)⁻¹) * lam ^ r := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos hlam r)), mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hinner.trans houter) (pow_nonneg hlam.le r)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Scalar Fourier jet bounds recover operator-valued jet norms with constant one. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem weighted_integral_jet_norm_le_from_duals (p r : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ X, Continuous (f X))
    (w : Vec 2 → ℝ) (hw : Continuous w)
    (hc : ContDiff ℝ (p : ℕ∞) (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z))
    (X : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ l : E →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w z • l (f Y z)) X‖ ≤
        C * ‖l‖) :
    ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z) X‖ ≤ C := by
  apply multilinear_norm_le_from_real_duals _ C hC
  intro l
  rw [← weighted_integral_dual_iteratedFDeriv p r hr f hf w hw hc l X]
  exact hb l

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Tested lift operators preserve the transverse geometry of their left coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_transverse (par : Fin 2) (I : Set ℝ) (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsTransverseOn par I (fun t X z => c m α t X z v u)) :
    IsTransverseOn par I (liftApply n c f) := by
  intro t ht X z s
  funext v
  simp only [liftApply]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  exact congrArg (fun A => A (orderedDerivative α (f t) X u))
    (hc m hmn α v u t ht X z s)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Restricting a cell field to a fixed line preserves mixed bounds with the line norm factor only. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_linear_profile_le (p q r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (L : ℝ →L[ℝ] Vec 2) (X : Vec 2) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (fun y => f Y (L y)) x) X‖ ≤
      ‖L‖ ^ j * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f Y) (L x)) X‖ := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E →L[ℝ] E :=
    multilinearEvaluationMap (fun _ : Fin j => L 1)
  have hA : ‖A‖ ≤ ‖L‖ ^ j := by
    apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (norm_nonneg L) j)
    intro F
    apply (F.le_opNorm (fun _ => L 1)).trans
    have hL : ‖L 1‖ ≤ ‖L‖ := by simpa only [norm_one, mul_one] using L.le_opNorm 1
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg F)
  have he : (fun Y => iteratedDeriv j (fun y => f Y (L y)) x) =
      A ∘ (fun Y => iteratedFDeriv ℝ j (f Y) (L x)) := by
    funext Y
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have hh := L.iteratedFDeriv_comp_right (hf.1 Y) x (by exact_mod_cast hj)
    change (iteratedFDeriv ℝ j (f Y ∘ L) x) (fun _ => 1) = _
    rw [hh]
    rfl
  rw [he]
  exact (A.norm_iteratedFDeriv_comp_left (hf.2.1 j hj (L x)).contDiffAt
    (by exact_mod_cast hr)).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Smooth real ordered derivatives are invariant under word permutations. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def orderedListDerivative (w : List (Fin 2)) (f : Vec 2 → E) : Vec 2 → E :=
  w.foldl (fun g k => coordinateDerivative k g) f

theorem orderedListDerivative_contDiff (w : List (Fin 2)) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (orderedListDerivative w f) := by
  induction w generalizing f with
  | nil => exact hf
  | cons k w ih => exact ih _ (coordinateDerivative_contDiff k f hf)

theorem orderedListDerivative_perm {w w' : List (Fin 2)} (hw : w.Perm w')
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedListDerivative w f = orderedListDerivative w' f := by
  induction hw generalizing f with
  | nil => rfl
  | cons k _ ih => exact ih _ (coordinateDerivative_contDiff k f hf)
  | swap i j l =>
    change orderedListDerivative l (coordinateDerivative i (coordinateDerivative j f)) =
      orderedListDerivative l (coordinateDerivative j (coordinateDerivative i f))
    rw [coordinateDerivative_commute j i f hf]
  | trans _ _ ih ih' => exact (ih f hf).trans (ih' f hf)

theorem orderedDerivative_comp_perm {m : ℕ} (α : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedDerivative (α ∘ σ) f = orderedDerivative α f := by
  change orderedListDerivative (List.ofFn (α ∘ σ)) f = orderedListDerivative (List.ofFn α) f
  exact orderedListDerivative_perm (σ.ofFn_comp_perm α) f hf

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Finite transverse source jets propagate to two additional uniformly bounded Fourier jets. -/

def profileModeResponse (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a t : ℝ) (n : ℤ) : ℂ :=
  transverseModeResponse (‖profileFourierFrequency n‖ ^ 2) g
    (fun s => unitProfileFourierCoeff (f s) n) a t

theorem profileModeResponse_frequency_weight_bound (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ : ℝ) (hat : a ≤ t) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a t))
    (hg : ∀ s ∈ Icc a t, κ ≤ g s) (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ s ∈ Icc a t, ContDiff ℝ j (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hj : ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j (f s) x‖ ≤ C)
    (n : ℤ) (hn : n ≠ 0) :
    ‖profileFourierFrequency n‖ ^ (j + 2) * ‖profileModeResponse g f a t n‖ ≤ C / κ := by
  have hr : 0 < ‖profileFourierFrequency n‖ := norm_pos_iff.mpr (profileFourierFrequency_ne_zero n hn)
  exact transverseModeResponse_two_jet_gain ‖profileFourierFrequency n‖ κ hr hκ g
    (fun s => unitProfileFourierCoeff (f s) n) a t hat hi hg j C hC
    (fun s hs => unitProfileFourierCoeff_frequency_weight_bound j (f s) (hf s hs) (hp s hs)
      n hn C (hj s hs))

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The literal real-coordinate profile series retains its Fourier coefficients. -/

theorem profileFourierSeries_periodic (c : ℤ → ℂ) :
    Function.Periodic (profileFourierSeries c) 1 := by
  intro x
  simp only [profileFourierSeries, AddCircle.coe_add_period]

theorem unitProfileFourierCoeff_profileFourierSeries (c : ℤ → ℂ)
    (hc : Summable c) (n : ℤ) : unitProfileFourierCoeff (profileFourierSeries c) n = c n := by
  let hp := profileFourierSeries_periodic c
  rw [unitProfileFourierCoeff_eq_lift_coeff _ hp]
  have he : hp.lift = fun x : AddCircle (1 : ℝ) => ∑' m : ℤ, fourier m x * c m := by
    funext x
    induction x using Quotient.inductionOn with
    | h y => simp only [Function.Periodic.lift_coe, profileFourierSeries]
  rw [he]
  exact fourierCoeff_profile_torus_series c hc n

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Scalar cosine/sine bounds control their operator-valued pair uniformly. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem real_fourier_dual_pair_bound (p r : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ X, Continuous (f X))
    (w₁ w₂ : Vec 2 → ℝ) (hw₁ : Continuous w₁) (hw₂ : Continuous w₂)
    (hc₁ : ContDiff ℝ (p : ℕ∞) (fun Y => ∫ z in AVenhance.unitCube, w₁ z • f Y z))
    (hc₂ : ContDiff ℝ (p : ℕ∞) (fun Y => ∫ z in AVenhance.unitCube, w₂ z • f Y z))
    (X : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ l : E →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w₁ z • l (f Y z)) X‖ +
        ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w₂ z • l (f Y z)) X‖ ≤
          C * ‖l‖) :
    ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w₁ z • f Y z) X‖ +
      ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w₂ z • f Y z) X‖ ≤ 2 * C := by
  have h₁ := weighted_integral_jet_norm_le_from_duals p r hr f hf w₁ hw₁ hc₁ X C hC
    (fun l => (le_add_of_nonneg_right (norm_nonneg _)).trans (hb l))
  have h₂ := weighted_integral_jet_norm_le_from_duals p r hr f hf w₂ hw₂ hc₂ X C hC
    (fun l => (le_add_of_nonneg_left (norm_nonneg _)).trans (hb l))
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Finite cell-norm word budgets control the literal weighted Schur norm. -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem schurCellL2Jet_le_of_word_matrix_budget
    (π : ι → ℝ) (I : Set ℝ) (r : ℕ)
    (f : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (A : κ → ℝ) (hA : ∀ p, 0 ≤ A p) (M : ι → ι → ℝ) (hM0 : ∀ v u, 0 ≤ M v u)
    (C : ℝ) (hM : HasRealSchurBudget (massConjugatedMatrix π M) C)
    (hb : ∀ p v u, cellL2Jet I r (fun t X z => f p t X z v u) ≤
      ENNReal.ofReal (A p * M v u)) :
    schurCellL2Jet π I r f ≤ ENNReal.ofReal ((∑ p, A p) * C) := by
  let B := ∑ p, A p
  have hB : 0 ≤ B := Finset.sum_nonneg fun p _ => hA p
  have hbudget : HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => B * M v u)) (B * C) := by
    convert hM.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  apply schurSums_le_of_real_matrix_budget π _ (B * C) hbudget
  intro v u
  calc
    _ ≤ ∑ p, ENNReal.ofReal (A p * M v u) := Finset.sum_le_sum fun p _ => hb p v u
    _ = ENNReal.ofReal (B * M v u) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hA p) (hM0 v u))]
      congr 1
      simp only [B, Finset.sum_mul]
end

/-! Finite word budgets turn entrywise slow-jet estimates into the literal Schur norm. -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem schurSlowJet_le_of_word_matrix_budget
    (π : ι → ℝ) (I : Set ℝ) (r : ℕ)
    (f : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (A : κ → ℝ) (hA : ∀ p, 0 ≤ A p) (M : ι → ι → ℝ) (hM0 : ∀ v u, 0 ≤ M v u)
    (S C : ℝ) (hS : 0 ≤ S) (hM : HasRealSchurBudget (massConjugatedMatrix π M) C)
    (hb : ∀ p, ∀ t ∈ I, ∀ X z v u,
      ‖iteratedFDeriv ℝ r (fun Y => f p t Y z v u) X‖ ≤ A p * M v u * S) :
    schurSlowJet π I r f ≤ ENNReal.ofReal (((∑ p, A p) * S) * C) := by
  let B := (∑ p, A p) * S
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun p _ => hA p) hS
  have hbudget : HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => B * M v u)) (B * C) := by
    convert hM.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  apply schurSums_le_of_real_matrix_budget π _ (B * C) hbudget
  intro v u
  have hj p : slowJet I r (fun t X z => f p t X z v u) ≤
      ENNReal.ofReal (A p * M v u * S) := by
    unfold slowJet
    refine iSup_le fun t => iSup_le fun ht => iSup_le fun X => iSup_le fun z => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb p t ht X z v u)
  calc
    _ ≤ ∑ p, ENNReal.ofReal (A p * M v u * S) := Finset.sum_le_sum fun p _ => hj p
    _ = ENNReal.ofReal (B * M v u) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (mul_nonneg (hA p) (hM0 v u)) hS)]
      congr 1
      simp only [B, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by ring
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Finite Taylor composition preserves parameter jets jointly with the passive fast variable. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slowSmooth_continuous {p : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsSlowSmooth p f) : Continuous (Function.uncurry f) := by
  have h := hf.2 0 (Nat.zero_le p)
  have he : Function.uncurry f =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E) ∘
        (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ 0 (fun X => f X x.2) x.1) := rfl
  rw [he]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).continuous.comp h

theorem isSlowSmooth_comp {p : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsSlowSmooth p f)
    (g : E → F) (hg : ContDiff ℝ (p : ℕ∞) g) :
    IsSlowSmooth p (fun X z => g (f X z)) := by
  refine ⟨fun z => hg.comp (hf.1 z), fun a ha => ?_⟩
  have he : (fun x : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X => g (f X x.2)) x.1) =
      fun x => (ftaylorSeries ℝ g (f x.1 x.2)).taylorComp
        (ftaylorSeries ℝ (fun X => f X x.2) x.1) a := by
    funext x
    exact iteratedFDeriv_comp hg.contDiffAt (hf.1 x.2).contDiffAt (by exact_mod_cast ha)
  rw [he]
  change Continuous (fun x : Vec 2 × Vec 2 => ∑ c : OrderedFinpartition a,
    c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f x.1 x.2))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (fun X => f X x.2) x.1))
  apply continuous_finsetSum
  intro c _
  let L := c.compAlongOrderedFinpartitionL ℝ (Vec 2) E F
  have ho : Continuous (fun x : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ c.length g (f x.1 x.2)) :=
    (hg.continuous_iteratedFDeriv (by exact_mod_cast c.length_le.trans ha)).comp
      (slowSmooth_continuous hf)
  have hi : Continuous (fun x : Vec 2 × Vec 2 =>
      fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i) (fun X => f X x.2) x.1) :=
    continuous_pi fun i => hf.2 _ ((c.partSize_le i).trans ha)
  have hL := L.continuous.comp ho
  change Continuous (fun x : Vec 2 × Vec 2 =>
    L (iteratedFDeriv ℝ c.length g (f x.1 x.2))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (fun X => f X x.2) x.1))
  exact continuous_eval.comp (hL.prodMk hi)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The centered primitive of a transverse coefficient gives a centered fast-divergence flux. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def transverseCenteredFlux (par : Fin 2) (f : ℝ → E) (k : Fin 2) (z : Vec 2) : E :=
  if k = par.rev then centeredIntervalPrimitive f (z par.rev) else 0

theorem transverseCenteredFlux_mean_zero (par k : Fin 2) (f : ℝ → E) (hf : Continuous f) :
    fieldCellMean (transverseCenteredFlux par f k) = 0 := by
  by_cases hk : k = par.rev
  · have hc : Continuous (centeredIntervalPrimitive f) :=
      (fun r => (centeredIntervalPrimitive_hasDerivAt f hf r).continuousAt) |> continuous_iff_continuousAt.mpr
    simp only [transverseCenteredFlux, ite_eq_left hk, fieldCellMean]
    rw [integral_coordinate_eq_intervalIntegral par.rev _ hc]
    exact centeredIntervalPrimitive_mean_zero f hf
  · simp [transverseCenteredFlux, hk, fieldCellMean]

theorem transverseCenteredFlux_div (par : Fin 2) (f : ℝ → E) (hf : Continuous f)
    (X z : Vec 2) :
    (∑ k : Fin 2, fastPartial k (fun _ y => transverseCenteredFlux par f k y) X z) =
      f (z par.rev) := by
  have hd : Differentiable ℝ (centeredIntervalPrimitive f) :=
    fun r => (centeredIntervalPrimitive_hasDerivAt f hf r).differentiableAt
  have he (k : Fin 2) : fastPartial k (fun _ y => transverseCenteredFlux par f k y) X z =
      if k = par.rev then f (z par.rev) else 0 := by
    by_cases hk : k = par.rev
    · simp only [transverseCenteredFlux, ite_eq_left hk, fastPartial]
      rw [fderiv_profile_basis _ hd par.rev k z, centeredIntervalPrimitive_deriv f hf, ite_eq_left hk]
    · simp only [transverseCenteredFlux, ite_eq_right hk, fastPartial]
      simp only [fderiv_fun_const, Pi.zero_apply, zero_apply]
  simp only [he]
  simp

omit [CompleteSpace E] in
theorem transverseCenteredFlux_periodic (par k : Fin 2) (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hz : (∫ r in (0 : ℝ)..1, f r) = 0) :
    AVenhance.IsZ2Periodic (transverseCenteredFlux par f k) := by
  by_cases hk : k = par.rev
  · intro n z
    simp only [transverseCenteredFlux, ite_eq_left hk]
    have h := (centeredIntervalPrimitive_periodic f hf hp hz).zsmul (n par.rev) (z par.rev)
    simpa only [Pi.add_apply, AVenhance.latticeShift, zsmul_eq_mul, mul_one] using h
  · intro n z
    simp only [transverseCenteredFlux, ite_eq_right hk]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Scalar mode identification transports through the separating real dual of the coefficient carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem transverseMode_vector_eq_response (rate : ℝ) (g : ℝ → ℝ) (f u : ℝ → E) (a b : ℝ)
    (hi : IntegrableOn g (uIcc a b)) (hf : IntervalIntegrable f volume a b)
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt u ((-rate * g t) • u t + f t) t)
    (hzero : u a = 0) : u b = transverseModeResponse rate g f a b := by
  have hkf : IntervalIntegrable (fun s => transverseModeKernel rate g s b • f s) volume a b :=
    hf.continuousOn_smul (transverseModeKernel_continuousOn_left rate g a b hi)
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ℓ
  have hdℓ : ∀ᵐ t ∂volume.restrict (uIcc a b),
      HasDerivAt (fun s => ℓ (u s)) (-rate * g t * ℓ (u t) + ℓ (f t)) t := by
    filter_upwards [hd] with t ht
    simpa only [Function.comp_def, map_add, map_smul, smul_eq_mul] using!
      ℓ.hasFDerivAt.comp_hasDerivAt t ht
  have he := transverseMode_eq_response rate g (fun t => ℓ (f t)) (fun t => ℓ (u t)) a b
    hi.intervalIntegrable (ℓ.lipschitzWith.comp_absolutelyContinuousOnInterval hu) hdℓ
    (by simp [hzero])
  have hcomm : ℓ (transverseModeResponse rate g f a b) =
      transverseModeResponse rate g (fun t => ℓ (f t)) a b := by
    unfold transverseModeResponse
    rw [← ℓ.intervalIntegral_comp_comm hkf]
    simp only [map_smul]
  rw [map_sub, hcomm, he, sub_self]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A valid divergence order has exactly the Schur jet of its fast-independent lift coefficient. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem truncatedMeanCoefficient_schurSlowJet (n d r : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (c : Fin 2 → LiftCoeff ι h) (π : ι → ℝ) (I : Set ℝ)
    (hc : ∀ k m α t X z v u, c k m α t X z v u = c k m α t X 0 v u) :
    schurSlowJet π I r (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
      truncatedMeanCoefficient n c d p.1 t X p.2) =
    schurSlowJet π I r (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X z =>
      c p.2 (d - 1) p.1 t X z) := by
  congr 1
  funext p t X z v u
  rw [truncatedMeanCoefficient_eq n d hd hdn]
  exact (hc p.2 (d - 1) p.1 t X z v u).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The real majorant is dominated by the positive normalized envelope before any constituent sums. -/

def constituentPositiveMixedBudget (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    ENNReal.ofReal ((lam ^ r)⁻¹) * jetSup I r s f

theorem constituentUniformMixedBudget_ofReal_le (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (hlam : 0 ≤ lam) (f : ℝ → Vec 2 → Vec 2 → Vec 2) :
    ENNReal.ofReal (constituentUniformMixedBudget I p q lam f) ≤
      constituentPositiveMixedBudget I p q lam f := by
  have hnonneg (r s : ℕ) : 0 ≤ (jetSup I r s f).toReal * (lam ^ r)⁻¹ := by positivity
  unfold constituentUniformMixedBudget constituentPositiveMixedBudget
  rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => Finset.sum_nonneg fun s _ => hnonneg r s)]
  apply Finset.sum_le_sum
  intro r _
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => hnonneg r s)]
  apply Finset.sum_le_sum
  intro s _
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simpa only [mul_comm] using
    (mul_le_mul_right (ENNReal.ofReal_toReal_le (a := jetSup I r s f))
      (ENNReal.ofReal ((lam ^ r)⁻¹)))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fixed continuous linear output maps commute with the classical cell operator. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coordinateDerivative_postcomposition (L : E →L[ℝ] F) (f : Vec 2 → E)
    (hf : Differentiable ℝ f) (k : Fin 2) :
    coordinateDerivative k (fun z => L (f z)) = fun z => L (coordinateDerivative k f z) := by
  funext z
  have he := (L.hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  change fderiv ℝ (L ∘ f) z (basisVec k) = _
  rw [he]
  rfl

theorem cellOperator_postcomposition (L : E →L[ℝ] F)
    (G : Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2) (f : Vec 2 → E)
    (hf : ContDiff ℝ 2 f) (z : Vec 2) :
    cellOperator G v (fun y => L (f y)) z = L (cellOperator G v f z) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfirst (k : Fin 2) := coordinateDerivative_postcomposition L f hd k
  have hsecond (i j : Fin 2) :
      coordinateDerivative i (coordinateDerivative j (fun y => L (f y))) =
        fun y => L (coordinateDerivative i (coordinateDerivative j f) y) := by
    rw [hfirst j]
    exact coordinateDerivative_postcomposition L (coordinateDerivative j f)
      ((hfd.clm_apply contDiff_const).differentiable one_ne_zero) i
  change (∑ k, v z k • coordinateDerivative k (fun y => L (f y)) z) -
      ∑ i, ∑ j, G i j • coordinateDerivative i (coordinateDerivative j (fun y => L (f y))) z =
    L ((∑ k, v z k • coordinateDerivative k f z) -
      ∑ i, ∑ j, G i j • coordinateDerivative i (coordinateDerivative j f) z)
  simp_rw [hsecond, hfirst]
  simp only [map_sub, map_sum, map_smul]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Real spatial dilation scales each smooth coordinate derivative by one power. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinateDerivative_dilation (k : Fin 2) (a : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivative k (fun X => f (a • X)) =
      fun X => a • coordinateDerivative k f (a • X) := by
  funext X
  have hcomp := ((hf.differentiable (by simp) (a • X)).hasFDerivAt.comp X
    ((a • (ContinuousLinearMap.id ℝ (Vec 2))).hasFDerivAt)).fderiv
  change fderiv ℝ (fun X => f (a • X)) X (basisVec k) = _
  change fderiv ℝ (f ∘ (fun X : Vec 2 => a • X)) X (basisVec k) = _
  rw [hcomp]
  simp [coordinateDerivative]

theorem coordinateDerivative_const_smul (k : Fin 2) (a : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivative k (fun X => a • f X) = fun X => a • coordinateDerivative k f X := by
  funext X
  change fderiv ℝ (fun X => a • f X) X (basisVec k) = _
  rw [fderiv_fun_const_smul (hf.differentiable (by simp) X)]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Recover rectangular regularity from genuine real dual coordinates. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isBoxSmooth_of_all_real_duals (p q : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : ∀ l : E →L[ℝ] ℝ, IsBoxSmooth p q (fun X z => l (f X z))) :
    IsBoxSmooth p q f := by
  classical
  let b := Module.finBasis ℝ E
  let e := b.equivFunL
  let l := fun i => (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have he : f = fun X z => ∑ i, (l i (f X z)) • b i := by
    funext X z
    exact (b.sum_repr (f X z)).symm
  rw [he]
  exact IsBoxSmooth.sum Finset.univ fun i _ =>
    (hf (l i)).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
end

/-! A linear profile restriction retains all slow derivatives of every reserved fast jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_profile_iteratedDeriv_slow_contDiff (p q j : ℕ) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (L : ℝ →L[ℝ] Vec 2) (x : ℝ) :
    ContDiff ℝ (p : ℕ∞) (fun Y => iteratedDeriv j (fun y => f Y (L y)) x) := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E →L[ℝ] E :=
    multilinearEvaluationMap (fun _ : Fin j => L 1)
  have he : (fun Y => iteratedDeriv j (fun y => f Y (L y)) x) =
      A ∘ (fun Y => iteratedFDeriv ℝ j (f Y) (L x)) := by
    funext Y
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have hh := L.iteratedFDeriv_comp_right (hf.1 Y) x (by exact_mod_cast hj)
    change (iteratedFDeriv ℝ j (f Y ∘ L) x) (fun _ => 1) = _
    rw [hh]
    rfl
  rw [he]
  exact A.contDiff.comp (hf.2.1 j hj (L x))
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A finite coordinate synthesis recovers strong measurability of the full slow derivative. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fderiv_parameter_stronglyMeasurable (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t))
    (x : Vec 2) : StronglyMeasurable (fun t => fderiv ℝ (f t) x) := by
  let S := fun v : Fin 2 → E => ∑ q : Fin 2,
    (ContinuousLinearMap.proj q : Vec 2 →L[ℝ] ℝ).smulRight (v q)
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro q _
    exact (ContinuousLinearMap.smulRightL ℝ (Vec 2) E
      (ContinuousLinearMap.proj q)).continuous.comp (continuous_apply q)
  have hv : StronglyMeasurable (fun t (q : Fin 2) => fderiv ℝ (f t) x (basisVec q)) :=
    (measurable_pi_iff.mpr (fun q => fderiv_apply_parameter_measurable f hm hd x (basisVec q))).stronglyMeasurable
  have he : (fun t => fderiv ℝ (f t) x) =
      fun t => S (fun q => fderiv ℝ (f t) x (basisVec q)) := by
    funext t
    apply ContinuousLinearMap.ext
    intro ξ
    conv_lhs => rw [vec_eq_sum_basis ξ]
    simp [S, map_smul, ContinuousLinearMap.smulRight_apply]
  rw [he]
  simpa only [Function.comp_def] using! hS.comp_stronglyMeasurable hv

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The actual scalar Fourier ODE derivative inherits two inverse-frequency powers from the source's second jet. -/

theorem scalarModeRhs_weight_bound (r g M U F : ℝ) (c f : ℂ)
    (hg : |g| ≤ M) (hu : r ^ 4 * ‖c‖ ≤ U) (hf : r ^ 2 * ‖f‖ ≤ F) :
    r ^ 2 * ‖(-r ^ 2 * g) • c + f‖ ≤ M * U + F := by
  have hM : 0 ≤ M := (abs_nonneg g).trans hg
  calc
    r ^ 2 * ‖(-r ^ 2 * g) • c + f‖ ≤ r ^ 2 * (‖(-r ^ 2 * g) • c‖ + ‖f‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg r)
    _ = |g| * (r ^ 4 * ‖c‖) + r ^ 2 * ‖f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg r)]
      ring
    _ ≤ M * U + F := add_le_add
      ((mul_le_mul_of_nonneg_right hg (mul_nonneg (by positivity) (norm_nonneg c))).trans
        (mul_le_mul_of_nonneg_left hu hM)) hf

theorem profileModeResponse_rhs_frequency_bound (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ M C : ℝ) (hat : a ≤ t) (hκ : 0 < κ)
    (hi : IntegrableOn g (Icc a t)) (hg : ∀ s ∈ Icc a t, κ ≤ g s)
    (hgm : |g t| ≤ M) (hC : 0 ≤ C)
    (hf : ∀ s ∈ Icc a t, ContDiff ℝ 2 (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hj : ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 2 (f s) x‖ ≤ C)
    (n : ℤ) (hn : n ≠ 0) :
    ‖profileFourierFrequency n‖ ^ 2 *
      ‖(-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n‖ ≤ M * (C / κ) + C := by
  apply scalarModeRhs_weight_bound _ (g t) M (C / κ) C _ _ hgm
  · exact profileModeResponse_frequency_weight_bound g f a t κ hat hκ hi hg 2 C hC hf hp hj n hn
  · exact unitProfileFourierCoeff_frequency_weight_bound 2 (f t) (hf t ⟨hat, le_rfl⟩)
      (hp t ⟨hat, le_rfl⟩) n hn C (hj t ⟨hat, le_rfl⟩)

/-! The zero Fourier mode is the literal source primitive and has the compact-window forcing bound. -/

theorem profileModeResponse_zero (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a t : ℝ) :
    profileModeResponse g f a t 0 = ∫ s in a..t, unitProfileFourierCoeff (f s) 0 := by
  simp only [profileModeResponse, profileFourierFrequency, Int.cast_zero, mul_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0), transverseModeResponse, transverseModeKernel,
    neg_zero, zero_mul, Real.exp_zero, one_smul]

theorem profileModeResponse_zero_norm_le (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b t C : ℝ) (ht : t ∈ Icc a b) (hC : 0 ≤ C)
    (hf : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C) :
    ‖profileModeResponse g f a t 0‖ ≤ C * (b - a) := by
  rw [profileModeResponse_zero]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := t) (f := fun s => unitProfileFourierCoeff (f s) 0)
    (C := C) (fun s hs => by
      have hs' : s ∈ Ioc a t := by simpa only [uIoc_of_le ht.1] using hs
      exact unitProfileFourierCoeff_norm_le (f s) 0 C (hf s ⟨hs'.1.le, hs'.2.trans ht.2⟩))
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  rw [abs_of_nonneg hta] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hC)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The physical coefficient Schur jet has the exact spatial dilation multiplier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem scaledMeanCoefficient_schurSlowJet_le (π : ι → ℝ) (I J : Set ℝ)
    (τ : ℝ → ℝ) (hτ : ∀ t ∈ J, τ t ∈ I) (c ρ : ℝ) (b : MeanCoeff ι h) (d r : ℕ)
    (hb : ∀ α k v u, ∀ t ∈ I, ContDiff ℝ (r : ℕ∞) (fun X => b d α t X k v u)) :
    schurSlowJet π J r (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
      scaledMeanCoefficient c ρ τ b d p.1 t X p.2) ≤
    ENNReal.ofReal (|c * ρ ^ d| * |ρ⁻¹| ^ r) *
      schurSlowJet π I r (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => b d p.1 t X p.2) :=
  schurSlowJet_dilation_smul_le π I J τ hτ r ρ⁻¹ (c * ρ ^ d)
    (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => b d p.1 t X p.2)
    (fun p t ht _ v u => hb p.1 p.2 v u t ht)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Variable multilinear evaluation preserves jointly continuous slow jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSlowSmooth_pair {p : ℕ} {f : Vec 2 → Vec 2 → E} {g : Vec 2 → Vec 2 → F}
    (hf : IsSlowSmooth p f) (hg : IsSlowSmooth p g) :
    IsSlowSmooth p (fun X z => (f X z, g X z)) := by
  have h := isSlowSmooth_add
    (isSlowSmooth_clm_comp (ContinuousLinearMap.inl ℝ E F) hf)
    (isSlowSmooth_clm_comp (ContinuousLinearMap.inr ℝ E F) hg)
  simpa only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using! h

theorem isSlowSmooth_multilinear_evaluation (n p : ℕ) (E : Fin n → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (f : Vec 2 → Vec 2 → ContinuousMultilinearMap ℝ E F)
    (φ : Vec 2 → Vec 2 → ∀ i, E i) (hf : IsSlowSmooth p f) (hφ : IsSlowSmooth p φ) :
    IsSlowSmooth p (fun X z => f X z (φ X z)) := by
  have he : ContDiff ℝ (p : ℕ∞)
      (fun x : ContinuousMultilinearMap ℝ E F × (∀ i, E i) => x.1 x.2) :=
    contDiff_multilinear_evaluation n E p Prod.fst Prod.snd contDiff_fst contDiff_snd
  exact isSlowSmooth_comp (isSlowSmooth_pair hf hφ) _ he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Summing normalized reserved source jets removes their scale factors before the mass sums. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceEnvelopeJetConstant (p q : ℕ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1), |Cj r s|

def normalizedSourceEnvelopeSum (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (p q : ℕ) (v u : ι) : ℝ≥0∞ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    ENNReal.ofReal ((lam ^ r)⁻¹) *
      (ENNReal.ofReal (Real.sqrt (π u / π v)) *
        ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
          ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r s (γ.coeff α)).sum)

theorem normalizedSourceEnvelopeSum_le (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q : ℕ) (hp : p ≤ qs) (hq : q ≤ qf) (v u : ι) :
    normalizedSourceEnvelopeSum π edge I lam p q v u ≤
      ENNReal.ofReal (sourceEnvelopeJetConstant p q Cj * b v u) := by
  have hsum : (∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
      ENNReal.ofReal (|Cj r s| * b v u)) =
      ENNReal.ofReal (sourceEnvelopeJetConstant p q Cj * b v u) := by
    unfold sourceEnvelopeJetConstant
    rw [Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun r _ =>
      Finset.sum_nonneg fun s _ => mul_nonneg (abs_nonneg _) (he.nonneg v u))]
    apply Finset.sum_congr rfl
    intro r _
    exact (ENNReal.ofReal_sum_of_nonneg (fun s _ =>
      mul_nonneg (abs_nonneg _) (he.nonneg v u))).symm
  rw [← hsum]
  unfold normalizedSourceEnvelopeSum
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  have hrp : r ≤ p := by have hh := Finset.mem_range.mp hr; omega
  have hsq : s ≤ q := by have hh := Finset.mem_range.mp hs; omega
  apply (mul_le_mul_right (he.jets v u r (hrp.trans hp) s (hsq.trans hq)) _).trans
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hlam.le r))]
  have hcancel : (lam ^ r)⁻¹ * (Cj r s * lam ^ r * b v u) = Cj r s * b v u := by
    calc
      _ = ((lam ^ r)⁻¹ * lam ^ r) * (Cj r s * b v u) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt (pow_pos hlam r)), one_mul]
  rw [hcancel]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (he.nonneg v u))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A centered transverse primitive recovers its source by literal fast divergence. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem transverseCenteredFlux_field_div (par : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : ∀ X, Continuous (f X))
    (hfactor : ∀ X z, f X z = f X ((z par.rev) • basisVec par.rev)) (X z : Vec 2) :
    (∑ k : Fin 2, fastPartial k (fun Y y => transverseCenteredFlux par
      (fun r => f Y (r • basisVec par.rev)) k y) X z) = f X z := by
  have hc : Continuous (fun r : ℝ => f X (r • basisVec par.rev)) :=
    (hf X).comp (continuous_id.smul continuous_const)
  exact (transverseCenteredFlux_div par _ hc X z).trans (hfactor X z).symm
end

/-! The classical cell operator commutes with one explicit finite coefficient synthesis map. -/

section
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellOperator_finite_synthesis (G : Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2)
    (w : J → ℝ) (f : J → Vec 2 → E) (hf : ∀ j, ContDiff ℝ 2 (f j)) (z : Vec 2) :
    cellOperator G v (fun y => ∑ j, w j • f j y) z = ∑ j, w j • cellOperator G v (f j) z := by
  let F : Vec 2 → J → E := fun y j => f j y
  let L : (J → E) →L[ℝ] E := ∑ j, w j • ContinuousLinearMap.proj j
  have hF : ContDiff ℝ 2 F := contDiff_pi.mpr hf
  have hL (u : J → E) : L u = ∑ j, w j • u j := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  have hcomp : (fun y => L (F y)) = fun y => ∑ j, w j • f j y := funext (fun y => hL (F y))
  rw [← hcomp, cellOperator_postcomposition L G v F hF z, hL]
  apply Finset.sum_congr rfl
  intro j _
  have he := cellOperator_postcomposition (ContinuousLinearMap.proj j : (J → E) →L[ℝ] E)
    G v F hF z
  exact congrArg (fun u => w j • u) he.symm
end

/-! Finite input coordinates recover rectangular regularity of operator fields. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isBoxSmooth_clm_of_apply (p q : ℕ) (f : Vec 2 → Vec 2 → E →L[ℝ] F)
    (hf : ∀ ξ, IsBoxSmooth p q (fun X z => f X z ξ)) : IsBoxSmooth p q f := by
  classical
  let b := Module.finBasis ℝ E
  let e := b.equivFunL
  let l := fun i => (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have he : f = fun X z => ∑ i, (l i).smulRight (f X z (b i)) := by
    funext X z
    apply ContinuousLinearMap.ext
    intro ξ
    have hh := congrArg (f X z) (b.sum_repr ξ)
    simpa only [map_sum, map_smul, sum_apply,
      ContinuousLinearMap.smulRight_apply, l, e, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using! hh.symm
  rw [he]
  exact IsBoxSmooth.sum Finset.univ fun i _ =>
    (hf (b i)).clm_comp (ContinuousLinearMap.smulRightL ℝ E F (l i))
end

/-! Linear fast restrictions preserve the rectangular slow reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_profile_iteratedDeriv_parameter_contDiff (p q j : ℕ) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (L : ℝ →L[ℝ] Vec 2) (x : ℝ) :
    ContDiff ℝ (p : ℕ∞) (fun Y => iteratedDeriv j (fun y => f Y (L y)) x) :=
  linear_profile_iteratedDeriv_slow_contDiff p q j hj f hf L x
end

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Smooth ordered derivatives obey the exact real dilation law. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedListDerivative_const_smul (w : List (Fin 2)) (a : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedListDerivative w (fun X => a • f X) = fun X => a • orderedListDerivative w f X := by
  induction w generalizing f with
  | nil => rfl
  | cons k w ih =>
    change orderedListDerivative w (coordinateDerivative k (fun X => a • f X)) = _
    rw [coordinateDerivative_const_smul k a f hf]
    exact ih _ (coordinateDerivative_contDiff k f hf)

theorem orderedListDerivative_dilation (w : List (Fin 2)) (a : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedListDerivative w (fun X => f (a • X)) =
      fun X => a ^ w.length • orderedListDerivative w f (a • X) := by
  induction w generalizing f with
  | nil => simp [orderedListDerivative]
  | cons k w ih =>
    change orderedListDerivative w (coordinateDerivative k (fun X => f (a • X))) = _
    rw [coordinateDerivative_dilation k a f hf]
    rw [orderedListDerivative_const_smul]
    · rw [ih _ (coordinateDerivative_contDiff k f hf)]
      funext X
      simp [orderedListDerivative, smul_smul, pow_succ, mul_comm]
    · exact (coordinateDerivative_contDiff k f hf).comp
        (contDiff_const_smul a)

theorem orderedDerivative_dilation {m : ℕ} (α : DerivativeWord2 m) (a : ℝ)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedDerivative α (fun X => f (a • X)) = fun X => a ^ m • orderedDerivative α f (a • X) := by
  change orderedListDerivative (List.ofFn α) (fun X => f (a • X)) =
    fun X => a ^ m • orderedListDerivative (List.ofFn α) f (a • X)
  simpa only [List.length_ofFn] using orderedListDerivative_dilation (List.ofFn α) a f hf

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter Set
namespace AVRegularity.CycleComparison.Lift

/-! Dominated slow-parameter integration with merely measurable time slices.
The differentiation argument is that of compact parameter integrals. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem parameter_integral_continuous (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec 2 → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hc : ∀ t, Continuous (f t)) (C : ℝ) (hb : ∀ t x, ‖f t x‖ ≤ C) :
    Continuous (fun x => ∫ t, f t x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact Eventually.of_forall (fun y => ae_of_all μ (fun t => hb t y))
  · exact integrable_const C
  · exact ae_of_all μ (fun t => (hc t).continuousAt)

omit [CompleteSpace E] in
theorem parameter_integral_hasFDerivAt (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec 2 → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hd : ∀ t, Differentiable ℝ (f t)) (C₀ C₁ : ℝ)
    (hb₀ : ∀ t x, ‖f t x‖ ≤ C₀)
    (hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C₁) (x : Vec 2) :
    HasFDerivAt (fun y => ∫ t, f t y ∂μ)
      (∫ t, fderiv ℝ (f t) x ∂μ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (μ := μ) (F := fun y t => f t y)
    (F' := fun y t => fderiv ℝ (f t) y)
    (bound := fun _ => C₁) (Filter.univ_mem)
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact (integrable_const C₀).mono' (hm x).aestronglyMeasurable
      (ae_of_all μ (fun t => hb₀ t x))
  · exact (fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
  · exact ae_of_all μ (fun t y _ => hb₁ t y)
  · exact integrable_const C₁
  · exact ae_of_all μ (fun t y _ => (hd t y).hasFDerivAt)

end AVRegularity.CycleComparison.Lift
end
end
