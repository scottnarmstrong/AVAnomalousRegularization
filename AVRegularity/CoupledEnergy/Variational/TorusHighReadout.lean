-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble finite Sobolev families into a tensor carrier without losing a dimension factor. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Assemble the fiber entries by their mutually orthogonal singleton injections. -/
def torusFamilyTensor {K : ℕ} (w : J → TorusHk K E) :
    TorusHk K (PiLp 2 (fun _ : J => E)) :=
  ∑ a, mapTorusHk (tensorEntryCLM a) (w a)

/-- Each assembled jet is the corresponding finite sum of L² singleton injections. -/
theorem torusFamilyTensor_jet {K : ℕ} (w : J → TorusHk K E) (j : JetIndex2 K) :
    (torusFamilyTensor w).val j =
      ∑ a, (tensorEntryCLM (E := E) a).compLpL 2 (volume.restrict AVenhance.unitCube) ((w a).val j) := by
  simp [torusFamilyTensor, mapTorusHk_jet_eq_compLp]

omit [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Distinct tensor injections are orthogonal in the cell Hilbert space. -/
theorem tensorEntryLp_inner (a b : J)
    (u v : ComponentL2 (volume.restrict AVenhance.unitCube) E) :
    inner ℝ ((tensorEntryCLM a).compLpL 2 (volume.restrict AVenhance.unitCube) u)
      ((tensorEntryCLM b).compLpL 2 (volume.restrict AVenhance.unitCube) v) =
        if a = b then inner ℝ u v else 0 := by
  rw [L2.inner_def]
  have hpoint : (fun x => inner ℝ
      (((tensorEntryCLM a).compLpL 2 (volume.restrict AVenhance.unitCube) u) x)
      (((tensorEntryCLM b).compLpL 2 (volume.restrict AVenhance.unitCube) v) x)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => if a = b then inner ℝ (u x) (v x) else 0 := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM a) u,
      ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM b) v] with x hu hv
    rw [hu, hv]
    change inner ℝ (PiLp.single (β := fun _ : J => E) 2 a (u x))
      (PiLp.single (β := fun _ : J => E) 2 b (v x)) = _
    rw [PiLp.inner_apply]
    simp only [PiLp.ofLp_single, Pi.single_apply]
    change (∑ k : J, inner ℝ (if k = a then u x else 0) (if k = b then v x else 0)) = _
    have hs (k : J) : inner ℝ (if k = a then u x else 0) (if k = b then v x else 0) =
        if k = a then (if a = b then inner ℝ (u x) (v x) else 0) else 0 := by
      by_cases hka : k = a <;> by_cases hkb : k = b <;> simp_all
    simp_rw [hs]
    simp
  rw [integral_congr_ae hpoint]
  by_cases hab : a = b <;> simp [hab, L2.inner_def]

/-- The tensor norm has exactly the sum of entry norm squares. -/
theorem torusFamilyTensor_jet_normSq {K : ℕ} (w : J → TorusHk K E) (j : JetIndex2 K) :
    ‖(torusFamilyTensor w).val j‖ ^ 2 = ∑ a, ‖(w a).val j‖ ^ 2 := by
  rw [torusFamilyTensor_jet, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, tensorEntryLp_inner]
  simp

/-- The tensor factorial norm is exactly the sum of the entry factorial norm squares. -/
theorem torusFamilyTensor_factorialNormSq {K : ℕ} (ρ : ℝ) (w : J → TorusHk K E) :
    factorialNormSq ρ (torusFamilyTensor w).val = ∑ a, factorialNormSq ρ (w a).val := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [torusFamilyTensor_jet_normSq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Fixed bounded readouts from ambient coupled higher jets. These maps do not
search for finite-dimensional instances on a Sobolev graph. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- Read a single derivative jet of one component. -/
def coupledHighJetCLM (K : ι → ℕ) (i : ι) (j : JetIndex2 (K i + 1)) :
    CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 (K i + 1) =>
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) j).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun i =>
        JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) i)

omit [Fintype ι] [∀ i, BorelSpace (h i)] in
@[simp] theorem coupledHighJetCLM_apply (K : ι → ℕ) (i : ι)
    (j : JetIndex2 (K i + 1)) (U : CoupledHighHilbert (h := h) K) :
    coupledHighJetCLM K i j U = U i j := rfl

/-- Assemble one derivative order as a single vector-valued spatial L² tensor. -/
def coupledHighTensorCLM (K : ι → ℕ) (i : ι) (m : ℕ) (hm : m ≤ K i + 1) :
    CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube)
        (PiLp 2 (fun _ : DerivativeWord2 m => h i)) :=
  ∑ w : DerivativeWord2 m,
    ((Galerkin.tensorEntryCLM (E := h i) w).compLpL 2
      (volume.restrict AVenhance.unitCube)).comp
        (coupledHighJetCLM K i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩)

omit [Fintype ι] [∀ i, BorelSpace (h i)] in
@[simp] theorem coupledHighTensorCLM_apply (K : ι → ℕ) (i : ι)
    (m : ℕ) (hm : m ≤ K i + 1) (U : CoupledHighHilbert (h := h) K) :
    coupledHighTensorCLM (h := h) K i m hm U = ∑ w : DerivativeWord2 m,
      (Galerkin.tensorEntryCLM (E := h i) w).compLpL 2
        (volume.restrict AVenhance.unitCube) (U i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩) := by
  simp only [coupledHighTensorCLM, sum_apply,
    ContinuousLinearMap.comp_apply, coupledHighJetCLM_apply]

omit [Fintype ι] [∀ i, BorelSpace (h i)] in
/-- The assembled spatial L² tensor has exactly the component jet representatives. -/
theorem coupledHighTensorCLM_ae (K : ι → ℕ) (i : ι)
    (m : ℕ) (hm : m ≤ K i + 1) (U : CoupledHighHilbert (h := h) K) :
    coupledHighTensorCLM (h := h) K i m hm U =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun w : DerivativeWord2 m =>
        U i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ x) := by
  rw [coupledHighTensorCLM_apply]
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun w : DerivativeWord2 m =>
    (Galerkin.tensorEntryCLM (E := h i) w).compLpL 2
      (volume.restrict AVenhance.unitCube) (U i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩))
  have hterms : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ w : DerivativeWord2 m,
      ((Galerkin.tensorEntryCLM (E := h i) w).compLpL 2
        (volume.restrict AVenhance.unitCube) (U i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩)) x =
      Galerkin.tensorEntryCLM w (U i ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ x) := by
    rw [ae_all_iff]
    intro w
    exact ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hsum, hterms] with x hx hxt
  rw [hx]
  simp only [Finset.sum_apply]
  simp_rw [hxt]
  apply PiLp.ext
  intro w
  simp [Galerkin.tensorEntryCLM, Galerkin.tensorEntryLinearMap, PiLp.ofLp_single]

end AVRegularity.CoupledEnergy.Variational
end
