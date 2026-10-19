-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.Lift.WordPolynomialFiniteExtraction
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite tested lift operators preserve exact fast periodicity of their coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_periodic_of_coefficients
    (n : ℕ) (c : LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X : Vec 2)
    (hper : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) :
    AVenhance.IsZ2Periodic (liftApply n c f t X) := by
  intro k z
  funext v
  simp only [liftApply]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  exact congrArg (fun A => A (orderedDerivative α (f t) X u))
    (hper m (by have := Finset.mem_range.mp hm; omega) α v u k z)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Undo mass conjugation once to obtain a physical matrix independent of exponential test directions. -/

variable {ι : Type*}

def physicalEdgeEnvelopeMatrix (π : ι → ℝ) (b : ι → ι → ℝ) : ι → ι → ℝ :=
  fun v u => b v u / Real.sqrt (π u / π v)

theorem physicalEdgeEnvelopeMatrix_nonneg (π : ι → ℝ) (b : ι → ι → ℝ)
    (hb : ∀ v u, 0 ≤ b v u) (v u : ι) : 0 ≤ physicalEdgeEnvelopeMatrix π b v u :=
  div_nonneg (hb v u) (Real.sqrt_nonneg _)

theorem massConjugated_physicalEdgeEnvelopeMatrix [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (b : ι → ι → ℝ) :
    massConjugatedMatrix π (physicalEdgeEnvelopeMatrix π b) = b := by
  funext v u
  exact mul_div_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v))))

theorem physical_matrix_entry_le_of_weighted (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (b A : ι → ι → ℝ) (C : ℝ) (v u : ι)
    (hb : Real.sqrt (π u / π v) * A v u ≤ C * b v u) :
    A v u ≤ C * physicalEdgeEnvelopeMatrix π b v u := by
  have hs : 0 < Real.sqrt (π u / π v) := Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v))
  change A v u ≤ C * (b v u / Real.sqrt (π u / π v))
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hb)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The exact transverse Fourier eigenmodes of the cell spatial operator. -/

def transverseFourierMode (par : Fin 2) (n : ℤ) (z : Vec 2) : ℂ :=
  fourier n (z par.rev : AddCircle (1 : ℝ))

theorem profileFourier_character_contDiff (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => fourier n (x : AddCircle (1 : ℝ))) := by
  simp_rw [fourier_coe_apply]
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  simpa only [Complex.ofReal_one] using ((contDiff_const.mul hx).div_const (1 : ℂ)).cexp

theorem transverseFourierMode_contDiff (par : Fin 2) (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (transverseFourierMode par n) := by
  exact (profileFourier_character_contDiff n).comp
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ).contDiff

theorem transverseFourierMode_periodic (par : Fin 2) (n : ℤ) :
    AVenhance.IsZ2Periodic (transverseFourierMode par n) := by
  have hp : Function.Periodic (fun x : ℝ => fourier n (x : AddCircle (1 : ℝ))) 1 := by
    intro x
    dsimp only
    rw [AddCircle.coe_add_period]
  intro m z
  simpa only [transverseFourierMode, Pi.add_apply, AVenhance.latticeShift, zsmul_eq_mul, mul_one] using
    hp.zsmul (m par.rev) (z par.rev)

theorem profileFourierFrequency_sq (n : ℤ) :
    profileFourierFrequency n ^ 2 = -((‖profileFourierFrequency n‖ ^ 2 : ℝ) : ℂ) := by
  rw [profileFourierFrequency_norm_sq]
  simp only [profileFourierFrequency, mul_pow, Complex.I_sq]
  push_cast
  ring

theorem profileFourier_character_deriv (n : ℤ) :
    deriv (fun x : ℝ => fourier n (x : AddCircle (1 : ℝ))) =
      fun (x : ℝ) => profileFourierFrequency n * fourier n (x : AddCircle (1 : ℝ)) := by
  funext x
  simpa only [profileFourierFrequency, Complex.ofReal_one, div_one] using
    (hasDerivAt_fourier (1 : ℝ) n x).deriv

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Classical derivatives of the synthesized profile are the literal Fourier jet series. -/

theorem profileFourierSeries_iteratedDeriv (j : ℕ) (c : ℤ → ℂ)
    (hc : ∀ k : ℕ, k ≤ j → Summable (fun n => profileFourierFrequency n ^ k * c n)) :
    iteratedDeriv j (profileFourierSeries c) =
      profileFourierSeries (fun n => profileFourierFrequency n ^ j * c n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (fun k hk => hc k (hk.trans (Nat.le_succ j)))]
    have h0 := hc j (Nat.le_succ j)
    have h1 : Summable (fun n => profileFourierFrequency n * (profileFourierFrequency n ^ j * c n)) := by
      apply (hc (j + 1) le_rfl).congr
      intro n
      rw [pow_succ]
      ring
    funext x
    rw [(profileFourierSeries_hasDerivAt _ h0 h1 x).deriv]
    congr 1
    funext n
    rw [pow_succ]
    ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Absolute profile Fourier synthesis has exactly its supplied coefficients. -/

theorem fourierCoeff_profile_torus_series (c : ℤ → ℂ) (hc : Summable c) (n : ℤ) :
    fourierCoeff (fun x : AddCircle (1 : ℝ) => ∑' m : ℤ, fourier m x * c m) n = c n := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  have ht (x : AddCircle (1 : ℝ)) :
      fourier (-n) x * ∑' m : ℤ, fourier m x * c m =
        ∑' m : ℤ, fourier (-n) x * (fourier m x * c m) := by
    exact tsum_mul_left.symm
  simp_rw [ht]
  rw [boundedSeries_integral_tsum
    (fun m (x : AddCircle (1 : ℝ)) => fourier (-n) x * (fourier m x * c m))
    (fun m => ‖c m‖) hc.norm]
  · have hi (m : ℤ) : (∫ x : AddCircle (1 : ℝ),
        fourier (-n) x * (fourier m x * c m) ∂AddCircle.haarAddCircle) =
        if m = n then c m else 0 := by
      have hh := fourierCoeff.const_mul (fourier m : AddCircle (1 : ℝ) → ℂ) (c m) n
      rw [fourierCoeff_fourier] at hh
      unfold fourierCoeff at hh
      simp only [smul_eq_mul] at hh
      convert hh using 1
      · apply integral_congr_ae
        filter_upwards with x
        ring
      · simp [Pi.single_apply, mul_ite, eq_comm]
    simp_rw [hi]
    simp
  · intro m
    exact (((fourier (-n)).continuous.mul
      ((fourier m).continuous.mul continuous_const)).aestronglyMeasurable)
  · intro m
    filter_upwards with x
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, le_refl]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Polynomial Wiener weights of parameter jets are controlled by weighted Fourier modes. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem profile_wiener_parameter_jet_weight_le (p r L : ℕ) (hr : r ≤ p)
    (F : E → ℂ) (hF : ContDiff ℝ (p : ℕ∞) F) (n : ℤ) (hn : n ≠ 0) (X : E) :
    (1 + |(n : ℝ)|) ^ L * ‖iteratedFDeriv ℝ r F X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => profileFourierFrequency n ^ L * F Y) X‖ := by
  have he : iteratedFDeriv ℝ r (fun Y => profileFourierFrequency n ^ L * F Y) X =
      profileFourierFrequency n ^ L • iteratedFDeriv ℝ r F X := by
    simpa only [smul_eq_mul] using!
      iteratedFDeriv_const_smul_apply' (a := (profileFourierFrequency n ^ L : ℂ))
        (hF.contDiffAt.of_le (by exact_mod_cast hr))
  rw [he, norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_right (profile_wiener_weight_le_frequency L n hn) (norm_nonneg _)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Transport a scalar fast jet along a fixed coordinate projection. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarFastJetTransport (j : ℕ) (l : Vec 2 →L[ℝ] ℝ) :
    E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => l)).comp
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) E).toContinuousLinearEquiv.toContinuousLinearMap

theorem scalar_fast_jet_transport_eq (q j : ℕ) (hjq : j ≤ q)
    (f : ℝ → E) (hf : ContDiff ℝ (q : ℕ∞) f) (l : Vec 2 →L[ℝ] ℝ) (z : Vec 2) :
    iteratedFDeriv ℝ j (fun y => f (l y)) z =
      scalarFastJetTransport j l (iteratedDeriv j f (l z)) := by
  change iteratedFDeriv ℝ j (f ∘ l) z = _
  rw [l.iteratedFDeriv_comp_right hf z (by exact_mod_cast hjq),
    iteratedFDeriv_eq_equiv_comp]
  rfl

theorem scalar_fast_jet_parameter_contDiff (p q j : ℕ) (hjq : j ≤ q)
    (f : Vec 2 → ℝ → E) (hf : ∀ X, ContDiff ℝ (q : ℕ∞) (f X))
    (l : Vec 2 →L[ℝ] ℝ) (z : Vec 2)
    (hs : ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f X) (l z))) :
    ContDiff ℝ (p : ℕ∞)
      (fun X => iteratedFDeriv ℝ j (fun y => f X (l y)) z) := by
  let A := scalarFastJetTransport (E := E) j l
  have he : (fun X => iteratedFDeriv ℝ j (fun y => f X (l y)) z) =
      fun X => A (iteratedDeriv j (f X) (l z)) := by
    funext X
    exact scalar_fast_jet_transport_eq q j hjq (f X) (hf X) l z
  rw [he]
  exact A.contDiff.comp hs
end

/-! Parallel fast invariance survives the actual finite coefficient algebra. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem transverse_comp (par : Fin 2) (I : Set ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : IsTransverseOn par I f) (M : E → F) : IsTransverseOn par I (fun t X z => M (f t X z)) := by
  intro t ht X z s
  dsimp only
  rw [hf t ht X z s]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem transverse_bilinear (par : Fin 2) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (g : ℝ → Vec 2 → Vec 2 → F)
    (hf : IsTransverseOn par I f) (hg : IsTransverseOn par I g) (T : E → F → G) :
    IsTransverseOn par I (fun t X z => T (f t X z) (g t X z)) := by
  intro t ht X z s
  dsimp only
  rw [hf t ht X z s, hg t ht X z s]

omit [NormedSpace ℝ E] in
theorem transverse_finset_sum {α : Type*} (l : Finset α) (par : Fin 2) (I : Set ℝ)
    (f : α → ℝ → Vec 2 → Vec 2 → E) (hf : ∀ a ∈ l, IsTransverseOn par I (f a)) :
    IsTransverseOn par I (fun t X z => ∑ a ∈ l, f a t X z) := by
  intro t ht X z s
  exact Finset.sum_congr rfl (fun a ha => hf a ha t ht X z s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem transverse_slow_field (par : Fin 2) (I : Set ℝ) (f : ℝ → Vec 2 → E) :
    IsTransverseOn par I (fun t X (_ : Vec 2) => f t X) := by
  intro t ht X z s
  rfl
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The scalar damping's reciprocal rate supplies two Fourier derivatives without time differentiation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverseModeResponse_const_smul (rate c : ℝ) (g : ℝ → ℝ) (f : ℝ → E) (a t : ℝ) :
    transverseModeResponse rate g (fun s => c • f s) a t = c • transverseModeResponse rate g f a t := by
  unfold transverseModeResponse
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [smul_smul, smul_smul, mul_comm]

theorem transverseModeResponse_two_jet_gain (r κ : ℝ) (hr : 0 < r) (hκ : 0 < κ)
    (g : ℝ → ℝ) (f : ℝ → E) (a t : ℝ) (hat : a ≤ t)
    (hi : IntegrableOn g (Icc a t)) (hg : ∀ s ∈ Icc a t, κ ≤ g s)
    (j : ℕ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ s ∈ Icc a t, r ^ j * ‖f s‖ ≤ C) :
    r ^ (j + 2) * ‖transverseModeResponse (r ^ 2) g f a t‖ ≤ C / κ := by
  have hsf : ∀ s ∈ Icc a t, ‖r ^ j • f s‖ ≤ C := by
    intro s hs
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr j)] using hf s hs
  have he := transverseModeResponse_norm_le (r ^ 2) κ (pow_pos hr 2) hκ g
    (fun s => r ^ j • f s) a t hat hi hg C hC hsf
  rw [transverseModeResponse_const_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos hr j)] at he
  calc
    r ^ (j + 2) * ‖transverseModeResponse (r ^ 2) g f a t‖ =
        r ^ 2 * (r ^ j * ‖transverseModeResponse (r ^ 2) g f a t‖) := by rw [pow_add]; ring
    _ ≤ r ^ 2 * (C / (r ^ 2 * κ)) := mul_le_mul_of_nonneg_left he (sq_nonneg r)
    _ = C / κ := by field_simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! Integer cell periodicity restricts to period one on a coordinate line. -/

variable {E : Type*}

theorem cell_periodic_linear_profile (k : Fin 2) (f : Vec 2 → E)
    (hf : ∀ n : Fin 2 → ℤ, ∀ z, f (z + intVector n) = f z) :
    Function.Periodic (fun x : ℝ => f (x • basisVec k)) 1 := by
  intro x
  let n : Fin 2 → ℤ := fun i => if i = k then 1 else 0
  have he : (x + 1) • basisVec k = x • basisVec k + intVector n := by
    ext i
    by_cases hi : i = k
    · simp [n, intVector, basisVec_apply, hi]
    · simp [n, intVector, basisVec_apply, hi]
  change f ((x + 1) • basisVec k) = f (x • basisVec k)
  rw [he]
  exact hf n _

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace AVRegularity.CycleComparison.Lift

/-! Conjugation commutes with the real-kernel finite-past response. -/

theorem transverseModeResponse_conj (rate : ℝ) (g : ℝ → ℝ)
    (f : ℝ → ℂ) (a b : ℝ) :
    transverseModeResponse rate g (fun t => conj (f t)) a b =
      conj (transverseModeResponse rate g f a b) := by
  unfold transverseModeResponse intervalIntegral
  rw [map_sub, ← integral_conj, ← integral_conj]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Unit coordinate projection has exact norm one in the plain cell vector space. -/

theorem cell_coordinate_projection_norm (k : Fin 2) :
    ‖(ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)‖ = 1 := by
  apply le_antisymm (cell_coordinate_projection_norm_le k)
  have hh := (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).le_opNorm (basisVec k)
  rw [norm_basisVec, mul_one] at hh
  simpa [ContinuousLinearMap.proj_apply, basisVec] using hh

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The first cross operator has zero mean on a fast-independent input. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem cellB1_independent (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (f : Vec 2 → E) (X : Vec 2) :
    (fun z => cellB1 η G v t (fun X _ => f X) X z) =
      fun z => ∑ q : Fin 2, (Real.sqrt η * v t z q) • fderiv ℝ f X (basisVec q) := by
  funext z
  simp [cellB1, slowPartial, fastPartial]

theorem fieldCellMean_cellB1_independent (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (hv : Continuous (v t))
    (hm : ∀ q : Fin 2, ∫ z in AVenhance.unitCube, v t z q = 0)
    (f : Vec 2 → E) (X : Vec 2) :
    fieldCellMean (fun z => cellB1 η G v t (fun X _ => f X) X z) = 0 := by
  rw [cellB1_independent]
  unfold fieldCellMean
  rw [← integral_unitCell_eq_unitCube]
  have hi (q : Fin 2) : IntegrableOn
      (fun z => (Real.sqrt η * v t z q) • fderiv ℝ f X (basisVec q)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell
      ((continuous_const.mul ((continuous_apply q).comp hv)).smul continuous_const)
  rw [integral_finsetSum _ (fun q _ => hi q)]
  apply Finset.sum_eq_zero
  intro q hq
  rw [integral_smul_const, integral_const_mul, integral_unitCell_eq_unitCube, hm q, mul_zero, zero_smul]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A weighted Fourier jet estimate gives explicit reciprocal-frequency decay. -/

theorem profile_frequency_jet_decay (p r j : ℕ) (hr : r ≤ p)
    (F : Vec 2 → ℂ) (hF : ContDiff ℝ (p : ℕ∞) F)
    (m : ℤ) (hm : m ≠ 0) (X : Vec 2) (C : ℝ)
    (hb : ‖iteratedFDeriv ℝ r (fun Y => profileFourierFrequency m ^ j * F Y) X‖ ≤ C) :
    ‖iteratedFDeriv ℝ r F X‖ ≤ C / ‖profileFourierFrequency m‖ ^ j := by
  have hnorm : 0 < ‖profileFourierFrequency m‖ ^ j :=
    pow_pos (norm_pos_iff.mpr (profileFourierFrequency_ne_zero m hm)) j
  have he : iteratedFDeriv ℝ r (fun Y => profileFourierFrequency m ^ j * F Y) X =
      profileFourierFrequency m ^ j • iteratedFDeriv ℝ r F X := by
    simpa only [smul_eq_mul] using!
      iteratedFDeriv_const_smul_apply' (a := (profileFourierFrequency m ^ j : ℂ))
        (hF.contDiffAt.of_le (by exact_mod_cast hr))
  rw [he, norm_smul, norm_pow] at hb
  exact (le_div_iff₀ hnorm).mpr (by simpa only [mul_comm] using hb)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! Cosine and sine coefficient jets are controlled by the actual complex coefficient jet. -/

theorem real_fourier_coefficient_jet_sum_le (p r : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → ℝ) (hf : ∀ X, Continuous (f X)) (k : Fin 2 → ℤ)
    (hF : ContDiff ℝ (p : ℕ∞)
      (fun Y => smoothFourierCoeff (fun z => (f Y z : ℂ)) k)) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube,
        Real.cos (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f Y z) X‖ +
      ‖iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube,
        Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f Y z) X‖ ≤
      2 * ‖iteratedFDeriv ℝ r
        (fun Y => smoothFourierCoeff (fun z => (f Y z : ℂ)) k) X‖ := by
  let F := fun Y => smoothFourierCoeff (fun z => (f Y z : ℂ)) k
  have hec : (fun Y => ∫ z in AVenhance.unitCube,
      Real.cos (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f Y z) =
      fun Y => (F Y).re := by
    funext Y
    exact cosine_cell_coefficient_eq_re (f Y) (hf Y) k
  have hes : (fun Y => ∫ z in AVenhance.unitCube,
      Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f Y z) =
      fun Y => -(F Y).im := by
    funext Y
    exact sine_cell_coefficient_eq_neg_im (f Y) (hf Y) k
  rw [hec, hes]
  rw [show (fun Y => -(F Y).im) = -(fun Y => (F Y).im) from rfl,
    iteratedFDeriv_neg_apply, norm_neg]
  have hc := norm_iteratedFDeriv_re_le p r hr F hF X
  have hs := norm_iteratedFDeriv_im_le p r hr F hF X
  linarith

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Real mass-conjugated budgets control the public extended-real Schur sums. -/

variable {ι : Type*} [Fintype ι]

theorem schurSums_le_of_real_matrix_budget (π : ι → ℝ)
    (A : ι → ι → ℝ) (C : ℝ)
    (hA : HasRealSchurBudget (massConjugatedMatrix π A) C)
    (N : ι → ι → ℝ≥0∞) (hN : ∀ v u, N v u ≤ ENNReal.ofReal (A v u)) :
    schurSums π N ≤ ENNReal.ofReal C := by
  have hentry (v u : ι) :
      ENNReal.ofReal (Real.sqrt (π u / π v)) * N v u ≤
        ENNReal.ofReal (massConjugatedMatrix π A v u) := by
    exact (mul_le_mul' (le_refl _) (hN v u)).trans_eq
      (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  unfold schurSums
  apply max_le
  · apply iSup_le
    intro v
    calc
      _ ≤ ∑ u, ENNReal.ofReal (massConjugatedMatrix π A v u) :=
        Finset.sum_le_sum fun u _ => hentry v u
      _ = ENNReal.ofReal (∑ u, massConjugatedMatrix π A v u) :=
        (ENNReal.ofReal_sum_of_nonneg (fun u _ => hA.nonneg v u)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hA.row_sum v)
  · apply iSup_le
    intro u
    calc
      _ ≤ ∑ v, ENNReal.ofReal (massConjugatedMatrix π A v u) :=
        Finset.sum_le_sum fun v _ => hentry v u
      _ = ENNReal.ofReal (∑ v, massConjugatedMatrix π A v u) :=
        (ENNReal.ofReal_sum_of_nonneg (fun v _ => hA.nonneg v u)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hA.col_sum u)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fast coordinate transport controls full multilinear jets without a dimension factor. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarFastJetTransport_norm_le (j : ℕ) (l : Vec 2 →L[ℝ] ℝ) :
    ‖scalarFastJetTransport (E := E) j l‖ ≤ ‖l‖ ^ j := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (norm_nonneg l) j)
  intro ξ
  have hh := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) E ξ).norm_compContinuousLinearMap_le
    (fun _ : Fin j => l)
  simpa only [scalarFastJetTransport, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    LinearIsometryEquiv.norm_map, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_comm] using! hh

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Scalar coefficient budgets factor out of matrix products without a component-count loss. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteMatrixProduct_scalar_powers (A : ι → ι → ℝ) (h₁ h₂ : ℕ) (B C : ℝ) :
    finiteMatrixProduct (fun v u => B * finiteMatrixPower A h₁ v u)
      (fun v u => C * finiteMatrixPower A h₂ v u) =
        fun v u => (B * C) * finiteMatrixPower A (h₁ + h₂) v u := by
  funext v u
  have hp := congrFun (congrFun (finiteMatrixPower_add A h₁ h₂) v) u
  rw [← hp]
  unfold finiteMatrixProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem finiteMatrixProduct_edge_scalar_power (A : ι → ι → ℝ) (hh : ℕ) (B : ℝ) :
    finiteMatrixProduct A (fun v u => B * finiteMatrixPower A hh v u) =
      fun v u => B * finiteMatrixPower A (hh + 1) v u := by
  funext v u
  rw [finiteMatrixPower_succ]
  unfold finiteMatrixProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite divergence cutoff extends actual tested-order coefficients by zero. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def truncatedMeanCoefficient (n : ℕ) (c : Fin 2 → LiftCoeff ι h) : MeanCoeff ι h :=
  fun d α t X k v u => if 2 ≤ d ∧ d ≤ n then c k (d - 1) α t X 0 v u else 0

omit [Fintype ι] in
theorem truncatedMeanCoefficient_eq (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (c : Fin 2 → LiftCoeff ι h) (α : DerivativeWord2 (d - 1)) (t : ℝ)
    (X : Vec 2) (k : Fin 2) (v u : ι) :
    truncatedMeanCoefficient n c d α t X k v u = c k (d - 1) α t X 0 v u := by
  simp only [truncatedMeanCoefficient, ite_eq_left (show 2 ≤ d ∧ d ≤ n from ⟨hd, hdn⟩)]

omit [Fintype ι] in
theorem truncatedMeanCoefficient_perm (n : ℕ) (c : Fin 2 → LiftCoeff ι h)
    (hc : ∀ k m α (σ : Equiv.Perm (Fin m)), c k m (α ∘ σ) = c k m α)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))) :
    truncatedMeanCoefficient n c d (α ∘ σ) = truncatedMeanCoefficient n c d α := by
  funext t X k v u
  unfold truncatedMeanCoefficient
  rw [hc]

theorem truncatedMeanCoefficient_meanApply (n : ℕ) (c : Fin 2 → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) :
    meanApply n (truncatedMeanCoefficient n c) f =
      meanApply n (fun d α t X k => c k (d - 1) α t X 0) f := by
  funext t X
  ext v
  unfold meanApply
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Finset.mem_Icc.mp hd
  simp only [truncatedMeanCoefficient, ite_eq_left hd']

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Enlarging a nonnegative constant preserves an ofReal bound even when its scalar factor is negative. -/

theorem ofReal_constant_mul_mono (c C a : ℝ) (hc : 0 ≤ c) (hC : c ≤ C) :
    ENNReal.ofReal (c * a) ≤ ENNReal.ofReal (C * a) := by
  by_cases ha : 0 ≤ a
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC ha)
  · rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge ha))]
    exact zero_le

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The positive constituent envelope bounds each actual weighted coefficient jet separately. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem scaledEnvelope_constituent_jet_le (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ)
    (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (v u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
    (hγ : γ ∈ edge v u d) (α : DerivativeWord2 (d.val - 1))
    (r q : ℕ) (hr : r ≤ qs) (hq : q ≤ qf) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      (ENNReal.ofReal ‖γ.map‖ * jetSup I r q (γ.coeff α)) ≤
      ENNReal.ofReal (Cj r q * lam ^ r * b v u) := by
  apply le_trans _ (he.jets v u r hr q hq)
  apply mul_le_mul_right
  have hα : jetSup I r q (γ.coeff α) ≤ ∑ β, jetSup I r q (γ.coeff β) :=
    Finset.single_le_sum (f := fun β => jetSup I r q (γ.coeff β))
      (fun _ _ => zero_le) (Finset.mem_univ α)
  have hterm : ENNReal.ofReal ‖γ.map‖ * (∑ β, jetSup I r q (γ.coeff β)) ≤
      ((edge v u d).map fun δ => ENNReal.ofReal ‖δ.map‖ *
        ∑ β, jetSup I r q (δ.coeff β)).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨γ, hγ, rfl⟩)
  exact (mul_le_mul_right hα _).trans
    (hterm.trans (Finset.single_le_sum (f := fun d => ((edge v u d).map fun δ =>
      ENNReal.ofReal ‖δ.map‖ * ∑ β, jetSup I r q (δ.coeff β)).sum)
      (fun _ _ => zero_le) (Finset.mem_univ d)))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Fixed coordinate synthesis transports jointly continuous slow jets to full multilinear jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem multilinear_slow_jet_continuous_of_basis_coordinates
    (q p r : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
    (hs : ∀ (w : DerivativeWord2 q) z,
      ContDiff ℝ (p : ℕ∞) (fun X => f X z (fun i => basisVec (w i))))
    (hj : ∀ w : DerivativeWord2 q, Continuous (fun x : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ r (fun X => f X x.2 (fun i => basisVec (w i))) x.1)) :
    Continuous (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ r (fun X => f X x.2) x.1) := by
  have hfull (z : Vec 2) : ContDiff ℝ (p : ℕ∞) (fun X => f X z) :=
    contDiff_multilinear_of_basis_coordinates q p (fun X => f X z) (fun w => hs w z)
  apply continuous_multilinear_of_basis_coordinates r
  intro a
  apply continuous_multilinear_of_basis_coordinates q
  intro w
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
    (fun i => basisVec (w i))
  let S := ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
    (fun i => basisVec (a i))
  have hc := S.continuous.comp (hj w)
  apply hc.congr
  intro x
  exact congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) E =>
    T (fun i => basisVec (a i)))
      (L.iteratedFDeriv_comp_left (hfull x.2).contDiffAt (by exact_mod_cast hr))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Summable mode bounds control full parameter jets independently of the Fourier phase. -/

theorem fourier_parameter_jet_norm_le (p q : ℕ) (hq : q ≤ p)
    (F : ℤ → Vec 2 → ℂ) (hF : ∀ m, ContDiff ℝ (p : ℕ∞) (F m))
    (V : ℕ → ℤ → ℝ) (hV : ∀ r ≤ p, Summable (V r))
    (hb : ∀ r ≤ p, ∀ m X, ‖iteratedFDeriv ℝ r (F m) X‖ ≤ V r m)
    (X : Vec 2) (z : ℝ) :
    ‖iteratedFDeriv ℝ q
      (fun Y => ∑' m : ℤ, fourier m (z : AddCircle (1 : ℝ)) * F m Y) X‖ ≤ ∑' m, V q m := by
  have hmode := fun m => unit_complex_mul_contDiff p _ (hF m)
    (fourier m (z : AddCircle (1 : ℝ)))
  have hbound : ∀ (r : ℕ) (m : ℤ) (Y : Vec 2), (r : ℕ∞) ≤ (p : ℕ∞) →
      ‖iteratedFDeriv ℝ r (fun Y => fourier m (z : AddCircle (1 : ℝ)) * F m Y) Y‖ ≤ V r m := by
    intro r m Y hr
    exact (norm_iteratedFDeriv_unit_complex_mul_le p r (by exact_mod_cast hr)
      _ (hF m) _ (by simp only [fourier_apply, Circle.norm_coe]) Y).trans
      (hb r (by exact_mod_cast hr) m Y)
  rw [iteratedFDeriv_tsum_apply hmode (fun r hr => hV r (by exact_mod_cast hr))
    hbound (by exact_mod_cast hq)]
  exact boundedSeries_norm_le _ (V q) (hV q hq)
    (fun m => hbound q m X (by exact_mod_cast hq))

/-! The actual identity's component maps have the diagonal matrix budget independently of component dimensions. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem identity_component_map_norm_le (v u : ι) :
    ‖(ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u)‖ ≤
      if v = u then 1 else 0 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by split_ifs <;> norm_num)
  intro ξ
  by_cases hvu : v = u
  · subst v
    simp
  · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hvu]

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] in
theorem mass_identity_matrix_schur_budget (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    HasRealSchurBudget (massConjugatedMatrix π (fun v u => if v = u then 1 else 0)) 1 := by
  have he : massConjugatedMatrix π (fun v u => if v = u then 1 else 0) =
      fun v u => if v = u then (1 : ℝ) else 0 := by
    funext v u
    by_cases hvu : v = u
    · subst v
      simp [massConjugatedMatrix, ne_of_gt (hπ u)]
    · simp [massConjugatedMatrix, hvu]
  rw [he]
  exact hasRealSchurBudget_diagonal
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual lift is linear in a finite synthesized coarse input at its tested derivative order. -/

section
variable {J ι : Type*} [Fintype J] [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_input_finite_synthesis (n : ℕ) (c : LiftCoeff ι h)
    (w : J → ℝ) (f : J → Vec 2 → ∀ i, h i)
    (hf : ∀ j, ContDiff ℝ (n : ℕ∞) (f j)) (t : ℝ) (X z : Vec 2) :
    liftApply n c (fun _ Y => ∑ j, w j • f j Y) t X z =
      ∑ j, w j • liftApply n c (fun _ => f j) t X z := by
  classical
  ext v
  simp only [liftApply, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [orderedDerivative_finite_synthesis α w f
    (fun j => (hf j).of_le (by exact_mod_cast hmn)) X]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  rw [Finset.sum_comm]
end

/-! The literal lift action is linear in smooth coarse inputs, with only its tested-order reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_input_sub_at_time (n : ℕ) (c : LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) (hb : ContDiff ℝ (n : ℕ∞) (b t)) :
    liftApply n c (fun s Y => a s Y - b s Y) t =
      fun X z => liftApply n c a t X z - liftApply n c b t X z := by
  funext X z v
  simp only [liftApply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [orderedDerivative_sub α (ha.of_le (by exact_mod_cast hmn)) (hb.of_le (by exact_mod_cast hmn))]
  simp only [Pi.sub_apply, map_sub]
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fixed output maps preserve full mixed jet bounds up to their operator norm. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_mixed_jet_postcomposition_le (p q r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ X, ContDiff ℝ (q : ℕ∞) (f X))
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedFDeriv ℝ j (f X) z))
    (L : E →L[ℝ] F) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => L (f Y y)) z) X‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f Y) z) X‖ := by
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Vec 2) E F L
  have he : (fun Y => iteratedFDeriv ℝ j (fun y => L (f Y y)) z) =
      A ∘ (fun Y => iteratedFDeriv ℝ j (f Y) z) := by
    funext Y
    exact L.iteratedFDeriv_comp_left (hf Y).contDiffAt (by exact_mod_cast hj)
  rw [he]
  have hA : ‖A‖ ≤ ‖L‖ := multilinear_postcomposition_norm_le (D := fun _ : Fin j => Vec 2) L
  exact (A.norm_iteratedFDeriv_comp_left (hs z).contDiffAt (by exact_mod_cast hr)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A period-one profile defines a genuinely periodic cell field. -/

variable {E : Type*}

theorem periodic_scalar_profile (p : Fin 2) (f : ℝ → E) (hf : Function.Periodic f 1) :
    AVenhance.IsZ2Periodic (fun z : Vec 2 => f (z p)) := by
  intro n z
  simpa only [Pi.add_apply, AVenhance.latticeShift, mul_one] using
    (hf.int_mul (n p)) (z p)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Physical edge powers have exactly the source-height Schur budget after mass conjugation. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem massConjugatedMatrix_power (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hh : ℕ) :
    massConjugatedMatrix π (finiteMatrixPower A hh) =
      finiteMatrixPower (massConjugatedMatrix π A) hh := by
  induction hh with
  | zero =>
    rw [finiteMatrixPower_zero, finiteMatrixPower_zero]
    funext v u
    by_cases hvu : v = u
    · subst u
      simp [massConjugatedMatrix, div_self (ne_of_gt (hπ v))]
    · simp [massConjugatedMatrix, hvu]
  | succ hh ih =>
    rw [finiteMatrixPower_succ, finiteMatrixPower_succ, massConjugatedMatrix_product π hπ, ih]

theorem massConjugated_physicalEdgeEnvelopeMatrix_power
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (b : ι → ι → ℝ) (hh : ℕ) :
    massConjugatedMatrix π (finiteMatrixPower (physicalEdgeEnvelopeMatrix π b) hh) =
      finiteMatrixPower b hh := by
  rw [massConjugatedMatrix_power π hπ, massConjugated_physicalEdgeEnvelopeMatrix π hπ]

theorem physicalEdgeEnvelopeMatrix_power_schur_budget
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (b : ι → ι → ℝ) (Θ : ℝ) (hΘ : 0 ≤ Θ)
    (hb : HasRealSchurBudget b Θ) (hh : ℕ) :
    HasRealSchurBudget
      (massConjugatedMatrix π (finiteMatrixPower (physicalEdgeEnvelopeMatrix π b) hh)) (Θ ^ hh) := by
  rw [massConjugated_physicalEdgeEnvelopeMatrix_power π hπ]
  exact hb.power hΘ hh

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The classical transverse source is recovered by its absolutely convergent profile Fourier series. -/

theorem periodic_profileLift_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) : Continuous hp.lift := by
  exact continuous_quot_lift _ hf

theorem unitProfileFourierCoeff_eq_lift_coeff (f : ℝ → ℂ) (hp : Function.Periodic f 1) (n : ℤ) :
    unitProfileFourierCoeff f n = fourierCoeff hp.lift n := by
  unfold unitProfileFourierCoeff
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [sub_zero, div_one, one_smul, zero_add, Function.Periodic.lift_coe]
  apply intervalIntegral.integral_congr
  intro x _
  simp

theorem profileFourierSeries_reconstruct (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hc : Summable (unitProfileFourierCoeff f)) :
    profileFourierSeries (unitProfileFourierCoeff f) = f := by
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, periodic_profileLift_continuous f hf hp⟩
  have hcoeff : fourierCoeff F = unitProfileFourierCoeff f := by
    funext n
    exact (unitProfileFourierCoeff_eq_lift_coeff f hp n).symm
  have hF : Summable (fourierCoeff F) := by rw [hcoeff]; exact hc
  funext x
  have hs := (has_pointwise_sum_fourier_series_of_summable hF (x : AddCircle (1 : ℝ))).tsum_eq
  rw [hcoeff] at hs
  simpa only [profileFourierSeries, smul_eq_mul, mul_comm, F, Function.Periodic.lift_coe] using! hs

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular scalar jets transport to rectangular jets on the cell. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_fast_box_transport (p q : ℕ) (f : Vec 2 → ℝ → E)
    (hf : ∀ X, ContDiff ℝ (q : ℕ∞) (f X))
    (hs : ∀ j ≤ q, ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f X) z))
    (hc : ∀ r j, r ≤ p → j ≤ q → Continuous (fun x : Vec 2 × ℝ =>
      iteratedFDeriv ℝ r (fun X => iteratedDeriv j (f X) x.2) x.1))
    (l : Vec 2 →L[ℝ] ℝ) : IsBoxSmooth p q (fun X z => f X (l z)) := by
  refine ⟨fun X => (hf X).comp l.contDiff, ?_, ?_⟩
  · intro j hj z
    exact scalar_fast_jet_parameter_contDiff p q j hj f hf l z (hs j hj (l z))
  · intro r j hr hj
    let A := scalarFastJetTransport (E := E) j l
    let B := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin r => Vec 2) E
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E) A
    have he (z : Vec 2) :
        (fun X => iteratedFDeriv ℝ j (fun y => f X (l y)) z) =
          fun X => A (iteratedDeriv j (f X) (l z)) := by
      funext X
      exact scalar_fast_jet_transport_eq q j hj (f X) (hf X) l z
    have hh : (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ r
        (fun X => iteratedFDeriv ℝ j (fun y => f X (l y)) x.2) x.1) =
        fun x => B (iteratedFDeriv ℝ r
          (fun X => iteratedDeriv j (f X) (l x.2)) x.1) := by
      funext x
      rw [he]
      change iteratedFDeriv ℝ r (A ∘ (fun X => iteratedDeriv j (f X) (l x.2))) x.1 = _
      rw [A.iteratedFDeriv_comp_left (hs j hj (l x.2)).contDiffAt
        (by exact_mod_cast hr)]
      rfl
    rw [hh]
    exact B.continuous.comp ((hc r j hr hj).comp
      (continuous_fst.prodMk (l.continuous.comp continuous_snd)))
end

/-! Mixed slow-fast operator norms survive coordinate transport with the exact projection factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_fast_mixed_jet_norm_le (p q r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → ℝ → E) (hf : ∀ X, ContDiff ℝ (q : ℕ∞) (f X))
    (l : Vec 2 →L[ℝ] ℝ) (z : Vec 2) (X : Vec 2)
    (hs : ContDiff ℝ (p : ℕ∞) (fun Y => iteratedDeriv j (f Y) (l z))) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => f Y (l y)) z) X‖ ≤
      ‖l‖ ^ j * ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f Y) (l z)) X‖ := by
  let A := scalarFastJetTransport (E := E) j l
  have he : (fun Y => iteratedFDeriv ℝ j (fun y => f Y (l y)) z) =
      A ∘ (fun Y => iteratedDeriv j (f Y) (l z)) := by
    funext Y
    exact scalar_fast_jet_transport_eq q j hj (f Y) (hf Y) l z
  rw [he]
  exact (A.norm_iteratedFDeriv_comp_left hs.contDiffAt (by exact_mod_cast hr)).trans
    (mul_le_mul_of_nonneg_right (scalarFastJetTransport_norm_le (E := E) j l) (norm_nonneg _))
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The factorial Schur norm is bounded by the finite sum of weighted uniform slow Schur jets. -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem schurFactorialJet_le_sum (π : ι → ℝ) (I : Set ℝ) (E : ℝ) (K : ℕ)
    (f : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) :
    schurFactorialJet π I E K f ≤ ∑ j ∈ Finset.range (K + 1),
      ENNReal.ofReal (E ^ j / (j.factorial : ℝ)) * schurSlowJet π I j f := by
  have he : (fun v u => ∑ a, ∑ j ∈ Finset.range (K + 1),
      ENNReal.ofReal (E ^ j / (j.factorial : ℝ)) * slowJet I j (fun t X z => f a t X z v u)) =
      fun v u => ∑ j ∈ Finset.range (K + 1),
        ENNReal.ofReal (E ^ j / (j.factorial : ℝ)) * ∑ a, slowJet I j (fun t X z => f a t X z v u) := by
    funext v u
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  unfold schurFactorialJet
  rw [he]
  apply (schurSums_finset_sum_le π _ _).trans
  exact Finset.sum_le_sum fun j _ => schurSums_scalar_mul_le π _ _
end

/-! Spatial scaling acts uniformly on all positive Schur entry sums. -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem schurSlowJet_dilation_smul_le (π : ι → ℝ) (I J : Set ℝ)
    (τ : ℝ → ℝ) (hτ : ∀ t ∈ J, τ t ∈ I) (j : ℕ) (a c : ℝ)
    (f : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hf : ∀ p, ∀ t ∈ I, ∀ z v u, ContDiff ℝ (j : ℕ∞) (fun X => f p t X z v u)) :
    schurSlowJet π J j (fun p t X z v u => c • f p (τ t) (a • X) z v u) ≤
      ENNReal.ofReal (|c| * |a| ^ j) * schurSlowJet π I j f := by
  have hj (p : κ) (v u : ι) :
      slowJet J j (fun t X z => c • f p (τ t) (a • X) z v u) ≤
        ENNReal.ofReal (|c| * |a| ^ j) * slowJet I j (fun t X z => f p t X z v u) :=
    slowJet_dilation_smul_le I J τ hτ j a c (fun t X z => f p t X z v u)
      (fun t ht z => hf p t ht z v u)
  unfold schurSlowJet
  apply (schurSums_entry_mono π (fun v u => ?_)).trans
  · exact schurSums_scalar_mul_le π _ _
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hj p v u
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Zero extension supplies regularity at every order while retaining the tested-order reserve. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem truncatedMeanCoefficient_contDiff (n p : ℕ) (c : Fin 2 → LiftCoeff ι h)
    (t : ℝ) (hc : ∀ k m, m ≤ n - 1 → ∀ α v u,
      ContDiff ℝ (p : ℕ∞) (fun X => c k m α t X 0 v u))
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (k : Fin 2) (v u : ι) :
    ContDiff ℝ (p : ℕ∞) (fun X => truncatedMeanCoefficient n c d α t X k v u) := by
  by_cases hd : 2 ≤ d ∧ d ≤ n
  · simp only [truncatedMeanCoefficient, ite_eq_left hd]
    exact hc k (d - 1) (by omega) α v u
  · simp only [truncatedMeanCoefficient, ite_eq_right hd]
    exact contDiff_const

end AVRegularity.CycleComparison.Lift
end
end
