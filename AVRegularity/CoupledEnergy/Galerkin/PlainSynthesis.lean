-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.CarrierFamilyProjection
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import AVenhance.Infra.Classical.GalerkinSmoothWordEquation
public import Mathlib.Tactic.Monotonicity.Lemmas
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public section
noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Finite Fourier coefficient products for heterogeneous torus components. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} {K : ι → ℕ}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Coordinates in the finite componentwise Fourier ranges. -/
abbrev CoupledFourierCoordinates (N : ℕ) := ∀ i : ι,
  (galerkinProj (E := h i) (K := K i) N).toLinearMap.range

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The L² mass form is nondegenerate on the finite coupled Fourier range. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} {K : ι → ℕ}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coupledRangeAddCommGroup (N : ℕ) (i : ι) :
    AddCommGroup ((galerkinProj (E := h i) (K := K i) N).toLinearMap.range) :=
  inferInstance

local instance coupledRangeModule (N : ℕ) (i : ι) :
    Module ℝ ((galerkinProj (E := h i) (K := K i) N).toLinearMap.range) :=
  inferInstance

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Each ordered Fourier band jet is controlled by the genuine carrier
norm and by the sum of its two spectral tails. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem torusHk_jet_norm_le {K : ℕ} (u : TorusHk K E) (j : JetIndex2 K) :
    ‖u.val j‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val j

theorem galerkinBand_jet_norm_le_tails {K : ℕ} (N M : ℕ) (u : TorusHk K E) (j : JetIndex2 K) :
    ‖(galerkinProj N u).val j - (galerkinProj M u).val j‖ ≤
      ‖galerkinProj N u - u‖ + ‖galerkinProj M u - u‖ := by
  have he : galerkinProj N u - galerkinProj M u =
      (galerkinProj N u - u) - (galerkinProj M u - u) := by abel
  calc
    _ ≤ ‖galerkinProj N u - galerkinProj M u‖ :=
      torusHk_jet_norm_le (galerkinProj N u - galerkinProj M u) j
    _ ≤ _ := by rw [he]; exact norm_sub_le _ _

theorem galerkinBand_jet_norm_le {K : ℕ} (N M : ℕ) (u : TorusHk K E) (j : JetIndex2 K) :
    ‖(galerkinProj N u).val j - (galerkinProj M u).val j‖ ≤ 2 * ‖u‖ := by
  calc
    _ ≤ ‖galerkinProj N u - galerkinProj M u‖ :=
      torusHk_jet_norm_le (galerkinProj N u - galerkinProj M u) j
    _ ≤ ‖galerkinProj N u‖ + ‖galerkinProj M u‖ := norm_sub_le _ _
    _ ≤ 2 * ‖u‖ := by linarith [galerkinProj_norm_le N u, galerkinProj_norm_le M u]
end

/-! The literal finite-range drift and coupling weak forms.
Coupling tensors are assembled one ordered derivative at a time. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inject one entry into a finite Euclidean tensor. -/
def tensorEntryLinearMap {J : Type*} [Fintype J] [DecidableEq J] (j : J) :
    E →ₗ[ℝ] PiLp 2 (fun _ : J => E) where
  toFun := fun x => PiLp.single (β := fun _ : J => E) 2 j x
  map_add' := by intro x y; exact PiLp.single_add (β := fun _ : J => E) 2 j
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]

/-- Coordinate injection with its Euclidean norm. -/
def tensorEntryCLM {J : Type*} [Fintype J] [DecidableEq J] (j : J) :
    E →L[ℝ] PiLp 2 (fun _ : J => E) :=
  (tensorEntryLinearMap (E := E) j).mkContinuous 1 (by
    intro x
    change ‖PiLp.single (β := fun _ : J => E) 2 j x‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single, one_mul])

variable {ι : Type*} [Fintype ι] {h : ι → Type*} {K : ι → ℕ}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

attribute [local instance] coupledRangeAddCommGroup coupledRangeModule

/-- One output direction of one coupling tensor entry. -/
def couplingEntryCoefficient {m : ℕ} (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (w : DerivativeWord2 m) (k : Fin 2) :
    Vec 2 → h i' →L[ℝ] h i :=
  fun x => (PiLp.proj 2 (fun _ : Fin 2 => h i) k).comp
    ((A x).comp (tensorEntryCLM (E := h i') w))
end

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The finite scalar coordinate space and its smooth vector-valued Fourier modes. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Component × real Fourier mode × fiber coordinate, with ordinary Pi instances. -/
abbrev CoupledPlainCoefficients (N : ℕ) :=
  PlainCoefficients (CoupledFourierModeIndex (ι := ι) (h := h) N)

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem coupledModeJet_contDiff (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ)
    (w : DerivativeWord2 m) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coupledModeJet N a i m w) := by
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    exact (coupledModeScalarDerivative_contDiff N a m w).smul contDiff_const
  · simp only [coupledModeJet, dite_eq_right hi]
    exact contDiff_const

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem coupledModeJet_periodic (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ)
    (w : DerivativeWord2 m) : AVenhance.IsZ2Periodic (coupledModeJet N a i m w) := by
  intro n x
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    rw [coupledModeScalarDerivative_periodic N a m w n x]
  · simp only [coupledModeJet, dite_eq_right hi]

/-- Synthesis as an explicit finite sum of smooth modes, before bundling in the carrier. -/
def coupledPlainRawJet (N : ℕ) (c : CoupledPlainCoefficients (ι := ι) (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) : Vec 2 → h i :=
  fun x => ∑ a : CoupledFourierModeIndex (h := h) N, c a • coupledModeJet N a i m w x

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The synthesized finite raw Fourier field is smooth at every retained derivative. -/
theorem coupledPlainRawJet_contDiff (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coupledPlainRawJet N c i m w) := by
  apply ContDiff.sum
  intro a _
  exact (coupledModeJet_contDiff N a i m w).const_smul (c a)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem coupledPlainRawJet_fderiv (N : ℕ)
    (c : CoupledPlainCoefficients (ι := ι) (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) (k : Fin 2) (x : Vec 2) :
    fderiv ℝ (coupledPlainRawJet N c i m w) x (basisVec k) =
      coupledPlainRawJet N c i (m + 1) (Fin.snoc w k) x := by
  unfold coupledPlainRawJet
  rw [fderiv_fun_sum (A := fun a y => c a • coupledModeJet N a i m w y) (fun a _ =>
    ((coupledModeJet_contDiff N a i m w).differentiable (by simp) x).const_smul (c a))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_const_smul ((coupledModeJet_contDiff N a i m w).differentiable (by simp) x)]
  simp only [smul_apply]
  rw [coupledModeJet_fderiv]


omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Every finite synthesized spatial jet is periodic. -/
theorem coupledPlainRawJet_periodic (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) : AVenhance.IsZ2Periodic (coupledPlainRawJet N c i m w) := by
  intro n x
  unfold coupledPlainRawJet
  apply Finset.sum_congr rfl
  intro a _
  rw [coupledModeJet_periodic N a i m w n x]

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The all-order smooth lift represents the graph Fourier cutoff at low order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothFourierLift_truncate_eq {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (f : TorusHk K E) :
    truncateTorusHk hKL (smoothFourierLift (K := K) (L := L) N f) =
      galerkinProj (E := E) (K := K) N f := by
  apply TorusHk.ext_value
  apply Lp.ext
  have hindex : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hprojection :
      (galerkinProj (E := E) (K := K) N f).val (valueIndex2 K) =
        (torusJetFourierPolynomialToHk N f).val (valueIndex2 K) := by
    rw [galerkinProj_val]
    exact congrArg (fun D : JetL2 (volume.restrict AVenhance.unitCube) K E =>
      D (valueIndex2 K)) (cellJetFourierProjection_eq_polynomialToHk N f)
  have hliftAE :
      (smoothFourierLift (K := K) (L := L) N f).val (valueIndex2 L) =ᵐ[
        volume.restrict AVenhance.unitCube]
        torusJetFourierPolynomial N f (valueIndex2 K) := by
    change torusJetToL2 (smoothFourierJet N f)
        (smoothFourierJet_memLp N f) (valueIndex2 L) =ᵐ[
          volume.restrict AVenhance.unitCube]
        torusJetFourierPolynomial N f (valueIndex2 K)
    exact (torusJetToL2_ae (smoothFourierJet N f) (smoothFourierJet_memLp N f)
      (valueIndex2 L)).trans
        (Filter.EventuallyEq.of_eq (smoothFourierJet_value_eq_polynomial N f))
  have hpolyAE :
      (torusJetFourierPolynomialToHk N f).val (valueIndex2 K) =ᵐ[
        volume.restrict AVenhance.unitCube]
        torusJetFourierPolynomial N f (valueIndex2 K) := by
    change torusJetToL2 (torusJetFourierPolynomial N f)
        (torusJetFourierPolynomial_memLp N f) (valueIndex2 K) =ᵐ[
          volume.restrict AVenhance.unitCube]
        torusJetFourierPolynomial N f (valueIndex2 K)
    exact torusJetToL2_ae (torusJetFourierPolynomial N f)
      (torusJetFourierPolynomial_memLp N f) (valueIndex2 K)
  rw [truncateTorusHk_apply, hindex, hprojection]
  exact hliftAE.trans hpolyAE.symm

theorem smoothFourierLift_of_fixed {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (f : TorusHk K E)
    (hfixed : galerkinProj (E := E) (K := K) N f = f) :
    truncateTorusHk hKL (smoothFourierLift (K := K) (L := L) N f) = f := by
  rw [smoothFourierLift_truncate_eq hKL N f, hfixed]

theorem galerkinProj_fixed_of_range {K : ℕ} (N : ℕ)
    (f : (galerkinProj (E := E) (K := K) N).toLinearMap.range) :
    galerkinProj (E := E) (K := K) N f.val = f.val := by
  rcases f.property with ⟨g, hg⟩
  rw [← hg]
  exact galerkinProj_idempotent N g

noncomputable def rangeSmoothFourierLift {K L : ℕ} (_hKL : K ≤ L) (N : ℕ)
    (f : (galerkinProj (E := E) (K := K) N).toLinearMap.range) : TorusHk L E :=
  smoothFourierLift (K := K) (L := L) N f.val

theorem rangeSmoothFourierLift_truncate {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (f : (galerkinProj (E := E) (K := K) N).toLinearMap.range) :
    truncateTorusHk hKL (rangeSmoothFourierLift hKL N f) = f.val := by
  exact smoothFourierLift_of_fixed hKL N f.val (galerkinProj_fixed_of_range N f)

theorem smoothFourierLift_value_eq_projection {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (f : TorusHk K E) :
    (smoothFourierLift (K := K) (L := L) N f).val (valueIndex2 L) =
      (galerkinProj (E := E) (K := K) N f).val (valueIndex2 K) := by
  have h := congrArg (fun z : TorusHk K E => z.val (valueIndex2 K))
    (smoothFourierLift_truncate_eq hKL N f)
  simpa [truncateTorusHk_apply, truncateJetIndex, valueIndex2, valueIndex] using h

theorem smoothFourierLift_add {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (f g : TorusHk K E) :
    smoothFourierLift (K := K) (L := L) N (f + g) =
      smoothFourierLift (K := K) (L := L) N f +
        smoothFourierLift (K := K) (L := L) N g := by
  apply TorusHk.ext_value
  calc
    (smoothFourierLift (K := K) (L := L) N (f + g)).val (valueIndex2 L) =
        (galerkinProj (E := E) (K := K) N (f + g)).val (valueIndex2 K) :=
      smoothFourierLift_value_eq_projection hKL N (f + g)
    _ = ((galerkinProj (E := E) (K := K) N f) +
        (galerkinProj (E := E) (K := K) N g)).val (valueIndex2 K) := by
      rw [map_add]
    _ = (smoothFourierLift (K := K) (L := L) N f +
        smoothFourierLift (K := K) (L := L) N g).val (valueIndex2 L) := by
      change (galerkinProj (E := E) (K := K) N f).val (valueIndex2 K) +
          (galerkinProj (E := E) (K := K) N g).val (valueIndex2 K) = _
      rw [← smoothFourierLift_value_eq_projection hKL N f,
        ← smoothFourierLift_value_eq_projection hKL N g]
      rfl

theorem smoothFourierLift_smul {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (c : ℝ) (f : TorusHk K E) :
    smoothFourierLift (K := K) (L := L) N (c • f) =
      c • smoothFourierLift (K := K) (L := L) N f := by
  apply TorusHk.ext_value
  calc
    (smoothFourierLift (K := K) (L := L) N (c • f)).val (valueIndex2 L) =
        (galerkinProj (E := E) (K := K) N (c • f)).val (valueIndex2 K) :=
      smoothFourierLift_value_eq_projection hKL N (c • f)
    _ = (c • galerkinProj (E := E) (K := K) N f).val (valueIndex2 K) := by
      rw [map_smul]
    _ = (c • smoothFourierLift (K := K) (L := L) N f).val (valueIndex2 L) := by
      change c • (galerkinProj (E := E) (K := K) N f).val (valueIndex2 K) = _
      rw [← smoothFourierLift_value_eq_projection hKL N f]
      rfl

noncomputable def rangeSmoothFourierLiftLinearMap {K L : ℕ}
    (hKL : K ≤ L) (N : ℕ) :
    (galerkinProj (E := E) (K := K) N).toLinearMap.range →ₗ[ℝ] TorusHk L E where
  toFun := fun f => smoothFourierLift (K := K) (L := L) N f.val
  map_add' := by
    intro f g
    exact smoothFourierLift_add hKL N f.val g.val
  map_smul' := by
    intro c f
    exact smoothFourierLift_smul hKL N c f.val

noncomputable def rangeSmoothFourierLiftCLM {K L : ℕ}
    (hKL : K ≤ L) (N : ℕ) :
    (galerkinProj (E := E) (K := K) N).toLinearMap.range →L[ℝ] TorusHk L E :=
  letI : FiniteDimensional ℝ
      ((galerkinProj (E := E) (K := K) N).toLinearMap.range) :=
    galerkinProj_range_finite (E := E) (K := K) N
  LinearMap.toContinuousLinearMap (rangeSmoothFourierLiftLinearMap hKL N)

noncomputable def torusHkValueCLM {K : ℕ} :
    TorusHk K E →L[ℝ] ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
      ComponentL2 (volume.restrict AVenhance.unitCube) E) (valueIndex2 K)).comp
    (torusHkGraph (E := E) K).toSubmodule.subtypeL

noncomputable def rangeSmoothDerivativeCLM {K r : ℕ} (N : ℕ)
    (a : DerivativeWord2 r) :
    (galerkinProj (E := E) (K := K) N).toLinearMap.range →L[ℝ]
      TorusHk K E :=
  (derivativeTorusHk (K := K) a).comp
    (rangeSmoothFourierLiftCLM (E := E) (K := K) (L := K + r)
      (by omega) N)

noncomputable def rangeSmoothDerivativeValueCLM {K r : ℕ} (N : ℕ)
    (a : DerivativeWord2 r) :
    (galerkinProj (E := E) (K := K) N).toLinearMap.range →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  (torusHkValueCLM (E := E) (K := K)).comp
    (rangeSmoothDerivativeCLM (E := E) (K := K) N a)

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Pointwise source pairing bounds for the spectral-tail representative.
The scalar value source is paired with the bounded lower-order trace. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem galerkinBand_pairing_bound {K L : ℕ} (N M : ℕ)
    (H : TorusHk K E) (u : TorusHk L E) (a : JetIndex2 K) (b : JetIndex2 L) :
    |inner ℝ ((galerkinProj N H).val a - (galerkinProj M H).val a)
      ((galerkinProj N u).val b - (galerkinProj M u).val b)| ≤
      (‖galerkinProj N H - H‖ + ‖galerkinProj M H - H‖) * (2 * ‖u‖) := by
  apply (abs_real_inner_le_norm _ _).trans
  exact mul_le_mul (galerkinBand_jet_norm_le_tails N M H a) (galerkinBand_jet_norm_le N M u b)
    (norm_nonneg _) (by positivity)

theorem galerkinBand_source_pairing_bound {K : ℕ} (N M : ℕ)
    (H u : TorusHk K E) (S : Fin 2 → TorusHk K E) (w : TorusHk (K + 1) E)
    (R : ℝ) (hu : ‖u‖ ≤ R) {j : ℕ} (hj : j ≤ K) (word : DerivativeWord2 j) :
    2 * |inner ℝ
      ((galerkinProj N H).val ⟨⟨j, by omega⟩, word⟩ - (galerkinProj M H).val ⟨⟨j, by omega⟩, word⟩)
      ((galerkinProj N u).val ⟨⟨j, by omega⟩, word⟩ - (galerkinProj M u).val ⟨⟨j, by omega⟩, word⟩) -
      ∑ k : Fin 2, inner ℝ
        ((galerkinProj N (S k)).val ⟨⟨j, by omega⟩, word⟩ -
          (galerkinProj M (S k)).val ⟨⟨j, by omega⟩, word⟩)
        ((galerkinProj N w).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩ -
          (galerkinProj M w).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩)| ≤
      4 * R * (‖galerkinProj N H - H‖ + ‖galerkinProj M H - H‖) +
      4 * ∑ k : Fin 2, (‖galerkinProj N (S k) - S k‖ + ‖galerkinProj M (S k) - S k‖) * ‖w‖ := by
  have hH := galerkinBand_pairing_bound N M H u ⟨⟨j, by omega⟩, word⟩ ⟨⟨j, by omega⟩, word⟩
  have hS (k : Fin 2) := galerkinBand_pairing_bound N M (S k) w
    ⟨⟨j, by omega⟩, word⟩ ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩
  have hH' := hH.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu (by norm_num))
    (by positivity : 0 ≤ ‖galerkinProj N H - H‖ + ‖galerkinProj M H - H‖))
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hS k)
  have ha := abs_sub_le
    (inner ℝ ((galerkinProj N H).val ⟨⟨j, by omega⟩, word⟩ - (galerkinProj M H).val ⟨⟨j, by omega⟩, word⟩)
      ((galerkinProj N u).val ⟨⟨j, by omega⟩, word⟩ - (galerkinProj M u).val ⟨⟨j, by omega⟩, word⟩))
    0 (∑ k : Fin 2, inner ℝ ((galerkinProj N (S k)).val ⟨⟨j, by omega⟩, word⟩ -
      (galerkinProj M (S k)).val ⟨⟨j, by omega⟩, word⟩)
      ((galerkinProj N w).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩ -
        (galerkinProj M w).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩))
  simp only [sub_zero, zero_sub, abs_neg] at ha
  have hh := ha.trans (add_le_add hH' ((Finset.abs_sum_le_sum_abs _ _).trans hs))
  have he : (∑ k : Fin 2, (‖galerkinProj N (S k) - S k‖ + ‖galerkinProj M (S k) - S k‖) * (2 * ‖w‖)) =
      2 * ∑ k : Fin 2, (‖galerkinProj N (S k) - S k‖ + ‖galerkinProj M (S k) - S k‖) * ‖w‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hh
  nlinarith

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Actual temporal Fourier-tail convergence in periodic Sobolev carriers,
including the paper's L¹ value source. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Fourier tails of an actual L¹ Sobolev source vanish in temporal L¹ norm. -/
theorem galerkinProj_time_L1_tendsto (K : ℕ) (a b : ℝ) (g : ℝ → TorusHk K E)
    (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => ∫ r in Set.Icc a b, ‖galerkinProj N (g r) - g r‖) atTop (𝓝 0) :=
  Variational.contractingProjection_integral_norm_sub_tendsto (volume.restrict (Set.Icc a b))
    (fun N => galerkinProj N) (fun N u => galerkinProj_norm_le N u)
    galerkinProj_tendsto g hg
end

/-! The actual periodic Sobolev flux tails vanish when paired with a
higher-order time L² field. -/

section
variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup Z]

theorem galerkinProj_time_tail_product_integrable (K : ℕ) (a b : ℝ) (N : ℕ)
    (u : ℝ → TorusHk K E) (hu : MemLp u 2 (volume.restrict (Set.Icc a b)))
    (z : ℝ → Z) (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    Integrable (fun t => ‖galerkinProj N (u t) - u t‖ * ‖z t‖) (volume.restrict (Set.Icc a b)) :=
  Variational.contractingProjection_tail_product_integrable _ (galerkinProj N) u hu z hz

theorem galerkinProj_time_tail_product_tendsto (K : ℕ) (a b : ℝ)
    (u : ℝ → TorusHk K E) (hu : MemLp u 2 (volume.restrict (Set.Icc a b)))
    (z : ℝ → Z) (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => ∫ t in Set.Icc a b, ‖galerkinProj N (u t) - u t‖ * ‖z t‖) atTop (𝓝 0) :=
  Variational.contractingProjection_integral_tail_product_tendsto _
    (fun N => galerkinProj N) galerkinProj_norm_le galerkinProj_tendsto u hu z hz
end

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Coupling entry operators inherit the exact coefficient hypotheses. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- Each tensor entry has operator norm at most the norm of the full coupling tensor. -/
theorem couplingEntryCoefficient_norm_le {m : ℕ} (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (w : DerivativeWord2 m) (k : Fin 2)
    (x : Vec 2) : ‖couplingEntryCoefficient i i' A w k x‖ ≤ ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A x))
  intro z
  calc
    ‖couplingEntryCoefficient i i' A w k x z‖ ≤
        ‖A x (tensorEntryCLM (E := h i') w z)‖ := PiLp.norm_apply_le _ k
    _ ≤ ‖A x‖ * ‖tensorEntryCLM (E := h i') w z‖ := (A x).le_opNorm _
    _ = ‖A x‖ * ‖z‖ := by
      change ‖A x‖ * ‖PiLp.single (β := fun _ : DerivativeWord2 m => h i') 2 w z‖ = _
      rw [PiLp.norm_single]

/-- Continuity in space is preserved by extraction of a tensor entry. -/
theorem couplingEntryCoefficient_continuous {m : ℕ} (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hA : Continuous A)
    (w : DerivativeWord2 m) (k : Fin 2) :
    Continuous (couplingEntryCoefficient i i' A w k) := by
  unfold couplingEntryCoefficient
  fun_prop

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! H¹ tests separate periodic Sobolev fields. The smooth Fourier lifts
provide the concrete dense tests at every input Sobolev order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The smooth finite Fourier lift has the same value class at every bundled order. -/
theorem smoothFourierLift_value_projection (K L N : ℕ) (f : TorusHk K E) :
    torusHkValueCLM (smoothFourierLift (K := K) (L := L) N f) =
      torusHkValueCLM (galerkinProj N f) := by
  apply Lp.ext
  have hlift : (smoothFourierLift (K := K) (L := L) N f).val (valueIndex2 L) =ᵐ[
      volume.restrict AVenhance.unitCube] torusJetFourierPolynomial N f (valueIndex2 K) := by
    change torusJetToL2 (smoothFourierJet N f) (smoothFourierJet_memLp N f) (valueIndex2 L) =ᵐ[_] _
    exact (torusJetToL2_ae (smoothFourierJet N f) (smoothFourierJet_memLp N f) (valueIndex2 L)).trans
      (Filter.EventuallyEq.of_eq (smoothFourierJet_value_eq_polynomial N f))
  have hp : (galerkinProj N f).val (valueIndex2 K) =
      (torusJetFourierPolynomialToHk N f).val (valueIndex2 K) := by
    rw [galerkinProj_val]
    exact congrArg (fun D : JetL2 (volume.restrict AVenhance.unitCube) K E => D (valueIndex2 K))
      (cellJetFourierProjection_eq_polynomialToHk N f)
  have hpoly : (torusJetFourierPolynomialToHk N f).val (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] torusJetFourierPolynomial N f (valueIndex2 K) := by
    exact torusJetToL2_ae (torusJetFourierPolynomial N f) (torusJetFourierPolynomial_memLp N f) _
  change (smoothFourierLift (K := K) (L := L) N f).val (valueIndex2 L) =ᵐ[_]
    (galerkinProj N f).val (valueIndex2 K)
  rw [hp]
  exact hlift.trans hpoly.symm

/-- Periodic Sobolev fields agreeing against all genuine H¹ tests are equal. -/
theorem torusHk_eq_of_H1_value_pairings (K : ℕ) (u v : TorusHk K E)
    (hpair : ∀ φ : TorusHk 1 E,
      inner ℝ (torusHkValueCLM u) (torusHkValueCLM φ) =
        inner ℝ (torusHkValueCLM v) (torusHkValueCLM φ)) : u = v := by
  let z := torusHkValueCLM (u - v)
  have hz (φ : TorusHk 1 E) : inner ℝ z (torusHkValueCLM φ) = 0 := by
    simp only [z, map_sub, inner_sub_left, hpair φ, sub_self]
  have hproj := (torusHkValueCLM (E := E) (K := K)).continuous.continuousAt.tendsto.comp
    (galerkinProj_tendsto (u - v))
  have hlim : Tendsto (fun N => inner ℝ z (torusHkValueCLM
      (smoothFourierLift (K := K) (L := 1) N (u - v)))) atTop (𝓝 (inner ℝ z z)) := by
    simp_rw [smoothFourierLift_value_projection]
    exact (innerSL ℝ z).continuous.continuousAt.tendsto.comp hproj
  have hself : inner ℝ z z = 0 := by
    apply tendsto_nhds_unique hlim
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hznorm : ‖z‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq, hself]
  have hz0 : z = 0 := norm_eq_zero.mp ((sq_eq_zero_iff).mp hznorm)
  apply TorusHk.ext_value
  exact sub_eq_zero.mp (by simpa only [z, map_sub] using! hz0)

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Moving a gradient direction through an ordered smooth finite Fourier jet. -/

/-- Prefixing a weak-word direction appends it to the reversed classical derivative list. -/
theorem smoothLiftWord_cons (j : ℕ) (w : DerivativeWord2 j) (k : Fin 2) :
    smoothLiftWord (j + 1) (Fin.cons k w) = smoothLiftWord j w ++ [k] := by
  induction j with
  | zero => simp [smoothLiftWord]
  | succ j ih =>
    have heq : Fin.cons k w =
        (Fin.snoc (Fin.cons k (Fin.init w) : DerivativeWord2 (j + 1)) (w (Fin.last j)) :
          DerivativeWord2 (j + 2)) := by
      rw [← Fin.cons_snoc_eq_snoc_cons, Fin.snoc_init_self]
    rw [heq, smoothLiftWord_snoc, ih]
    conv_rhs => rw [← Fin.snoc_init_self w, smoothLiftWord_snoc]
    rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Scalar smooth Fourier mixed partials commute across the whole derivative word. -/
theorem coupledModeScalarDerivative_cons_eq_snoc (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (j : ℕ) (w : DerivativeWord2 j)
    (k : Fin 2) (x : Vec 2) :
    coupledModeScalarDerivative N a (j + 1) (Fin.cons k w) x =
      coupledModeScalarDerivative N a (j + 1) (Fin.snoc w k) x := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (coupledModeScalar N a) :=
    (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm a.2.1)).of_le le_top
  unfold coupledModeScalarDerivative
  rw [smoothLiftWord_cons, smoothLiftWord_snoc,
    ← GalerkinSmoothWordEquation.classicalWordDerivative_append]
  exact congrFun (classicalWordDerivative_commute_gradient (smoothLiftWord j w)
    (coupledModeScalar N a) hf k) x

omit [Fintype ι] in
/-- Each vector Fourier mode inherits commutation of the scalar mixed derivatives. -/
theorem coupledModeJet_cons_eq_snoc (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (j : ℕ) (w : DerivativeWord2 j)
    (k : Fin 2) (x : Vec 2) :
    coupledModeJet N a i (j + 1) (Fin.cons k w) x =
      coupledModeJet N a i (j + 1) (Fin.snoc w k) x := by
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    rw [coupledModeScalarDerivative_cons_eq_snoc]
  · simp only [coupledModeJet, dite_eq_right hi]

/-- All reconstructed finite fields commute gradient directions through ordered derivatives. -/
theorem coupledPlainRawJet_cons_eq_snoc (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) (k : Fin 2) (x : Vec 2) :
    coupledPlainRawJet N c i (j + 1) (Fin.cons k w) x =
      coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) x := by
  unfold coupledPlainRawJet
  apply Finset.sum_congr rfl
  intro a _
  rw [coupledModeJet_cons_eq_snoc]


omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Adjacent final scalar mixed partials commute by the symmetry of the second derivative. -/
theorem coupledModeScalarDerivative_snoc_swap (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (j : ℕ) (w : DerivativeWord2 j)
    (k l : Fin 2) (x : Vec 2) :
    coupledModeScalarDerivative N a (j + 2) (Fin.snoc (Fin.snoc w k) l) x =
      coupledModeScalarDerivative N a (j + 2) (Fin.snoc (Fin.snoc w l) k) x := by
  have h := classicalSpaceGrad_commute (coupledModeScalarDerivative N a j w)
    (coupledModeScalarDerivative_contDiff N a j w) k l x
  simp_rw [coupledModeScalarDerivative_spaceGrad] at h
  exact h.symm

omit [Fintype ι] in
/-- Adjacent final derivative directions commute in every vector Fourier mode. -/
theorem coupledModeJet_snoc_swap (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (j : ℕ) (w : DerivativeWord2 j)
    (k l : Fin 2) (x : Vec 2) :
    coupledModeJet N a i (j + 2) (Fin.snoc (Fin.snoc w k) l) x =
      coupledModeJet N a i (j + 2) (Fin.snoc (Fin.snoc w l) k) x := by
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    rw [coupledModeScalarDerivative_snoc_swap]
  · simp only [coupledModeJet, dite_eq_right hi]

/-- Adjacent final mixed partials commute for the entire synthesized finite field. -/
theorem coupledPlainRawJet_snoc_swap (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) (k l : Fin 2) (x : Vec 2) :
    coupledPlainRawJet N c i (j + 2) (Fin.snoc (Fin.snoc w k) l) x =
      coupledPlainRawJet N c i (j + 2) (Fin.snoc (Fin.snoc w l) k) x := by
  unfold coupledPlainRawJet
  apply Finset.sum_congr rfl
  intro a _
  rw [coupledModeJet_snoc_swap]

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Explicit synthesis of plain finite coefficients into any requested torus Sobolev order.
The ODE state has no dependency on these carrier instances. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- All finite derivatives of a mode as an ordered jet. -/
def coupledModeRawJet (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K : ℕ) : RawJet2 K (h i) :=
  fun j => coupledModeJet N a i j.1.val j.2

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem coupledModeJet_memLp (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    MemLp (coupledModeJet N a i m w) 2 (volume.restrict AVenhance.unitCube) := by
  by_cases hi : i = a.1
  · subst i
    simp only [coupledModeJet, dite_true]
    exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ (h a.1)) a.2.2)).comp_memLp'
        (weak_continuous_memL2On (coupledModeScalarDerivative_contDiff N a m w).continuous)
  · simp only [coupledModeJet, dite_eq_right hi]
    exact MemLp.zero

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem coupledModeRawJet_hasWeakJet (N : ℕ)
    (a : CoupledFourierModeIndex (h := h) N) (i : ι) (K : ℕ) :
    HasOrderedWeakJetOn (K := K) Set.univ (coupledModeRawJet N a i K) := by
  intro j w k e
  let L := InnerProductSpace.toDual ℝ (h i) e
  have hc : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun x => inner ℝ e (coupledModeJet N a i j.val w x)) :=
    (L.contDiff.comp (coupledModeJet_contDiff N a i j.val w)).of_le (by simp)
  have hd : (fun x => fderiv ℝ
      (fun y => inner ℝ e (coupledModeJet N a i j.val w y)) x (basisVec k)) =
      fun x => inner ℝ e (coupledModeJet N a i (j.val + 1) (Fin.snoc w k) x) := by
    funext x
    have hf := ((coupledModeJet_contDiff N a i j.val w).differentiable (by simp) x).hasFDerivAt
    have hl := L.hasFDerivAt.comp x hf
    change (fderiv ℝ (L ∘ coupledModeJet N a i j.val w) x) (basisVec k) = _
    rw [hl.fderiv]
    change inner ℝ e (fderiv ℝ (coupledModeJet N a i j.val w) x (basisVec k)) = _
    rw [coupledModeJet_fderiv]
  have hw := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := k) hc
  have hw' : HasWeakPartialDerivOn Set.univ k
      (fun x => inner ℝ e (coupledModeJet N a i j.val w x))
      (fun x => inner ℝ e (coupledModeJet N a i (j.val + 1) (Fin.snoc w k) x)) := by
    rw [← hd]
    exact hw
  exact hw'

/-- A single vector-valued mode bundled at a requested Sobolev order. -/
def coupledModeHk (N : ℕ) (a : CoupledFourierModeIndex (h := h) N) (i : ι) (K : ℕ) :
    TorusHk K (h i) :=
  (TorusHkFunction.toHk
    { jet := coupledModeRawJet N a i K
      hasPeriodicWeakJet := ⟨fun j => coupledModeJet_periodic N a i j.1.val j.2,
        fun j => coupledModeJet_memLp N a i j.1.val j.2,
        coupledModeRawJet_hasWeakJet N a i K⟩ })

/-- One explicit linear synthesis map, applied only after solving the plain coefficient ODE. -/
def coupledPlainSynthesis (N : ℕ) (i : ι) (K : ℕ) :
    CoupledPlainCoefficients (ι := ι) (h := h) N →L[ℝ] TorusHk K (h i) :=
  ∑ a : CoupledFourierModeIndex (h := h) N,
    (ContinuousLinearMap.proj a : CoupledPlainCoefficients (h := h) N →L[ℝ] ℝ).smulRight
      (coupledModeHk N a i K)

@[simp] theorem coupledPlainSynthesis_apply (N : ℕ) (i : ι) (K : ℕ)
    (c : CoupledPlainCoefficients (ι := ι) (h := h) N) :
    coupledPlainSynthesis N i K c =
      ∑ a : CoupledFourierModeIndex (h := h) N, c a • coupledModeHk N a i K := by
  simp [coupledPlainSynthesis]

omit [Fintype ι] in
/-- The bundled mode has exactly its explicit raw jet almost everywhere on the cell. -/
theorem coupledModeHk_jet_ae (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K : ℕ) (j : JetIndex2 K) :
    (coupledModeHk N a i K).val j =ᵐ[volume.restrict AVenhance.unitCube]
      coupledModeJet N a i j.1.val j.2 :=
  torusJetToL2_ae _ _ j

/-- Synthesis reads the finite raw Fourier sum at every jet coordinate. -/
theorem coupledPlainSynthesis_jet_ae (N : ℕ) (i : ι) (K : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (j : JetIndex2 K) :
    (coupledPlainSynthesis N i K c).val j =ᵐ[volume.restrict AVenhance.unitCube]
      coupledPlainRawJet N c i j.1.val j.2 := by
  have heq : (coupledPlainSynthesis N i K c).val j =
      ∑ a : CoupledFourierModeIndex (h := h) N, c a • (coupledModeHk N a i K).val j := by
    simp [coupledPlainSynthesis]
  rw [heq]
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun a : CoupledFourierModeIndex (h := h) N => c a • (coupledModeHk N a i K).val j)
  have hterms : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ∀ a : CoupledFourierModeIndex (h := h) N,
        (c a • (coupledModeHk N a i K).val j) x =
          c a • coupledModeJet N a i j.1.val j.2 x := by
    rw [ae_all_iff]
    intro a
    filter_upwards [Lp.coeFn_smul (c a) ((coupledModeHk N a i K).val j),
      coupledModeHk_jet_ae N a i K j] with x hx hm
    rw [hx]
    change c a • ((coupledModeHk N a i K).val j) x = _
    rw [hm]
  filter_upwards [hsum, hterms] with x hx ht
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => ht a)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Every finite synthesized derivative is a cell L² function. -/
theorem coupledPlainRawJet_memLp (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    MemLp (coupledPlainRawJet N c i m w) 2 (volume.restrict AVenhance.unitCube) := by
  exact memLp_finsetSum Finset.univ (fun a _ => (coupledModeJet_memLp N a i m w).const_smul (c a))

end AVRegularity.CoupledEnergy.Galerkin
end
end
