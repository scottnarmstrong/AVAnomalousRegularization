-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The raw periodic representatives agree with the fixed Hilbert
value, gradient and derivative-tensor readouts used in the native equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusRawJet_ae {K : ℕ} (w : TorusHk K E) (j : JetIndex2 K) :
    w.toFunction.jet j =ᵐ[volume.restrict AVenhance.unitCube] w.val j :=
  periodicJetRepresentative_ae w.val j

theorem torusRawValue_ae {K : ℕ} (w : TorusHk K E) :
    w.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      Galerkin.torusHkValueCLM w := torusRawJet_ae w _

theorem torusRawTestGradient_ae (φ : TorusHk 1 E) :
    (fun x => WithLp.toLp 2 (fun k : Fin 2 => φ.toFunction.jet
      ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
        torusH1GradientL2CLM (E := E) φ := by
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x =
        φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun k => torusRawJet_ae φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
  filter_upwards [hj, torusH1GradientL2CLM_ae φ] with x hx hg
  rw [hg]
  exact congrArg (WithLp.toLp 2) (funext hx)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def coupledCarrierHighJets (K : ι → ℕ) (w : ∀ i, TorusHk (K i + 1) (h i)) :
    CoupledHighHilbert (h := h) K := WithLp.toLp 2 (fun i => (w i).val)

omit [Fintype ι] in
theorem torusRawCarrierGradient_ae (K : ι → ℕ) (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) :
    (fun x => WithLp.toLp 2 (fun k : Fin 2 => (w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)) =ᵐ[
        volume.restrict AVenhance.unitCube] coupledHighGradientCLM (h := h) K i (coupledCarrierHighJets K w) := by
  have hj := ae_all_iff.mpr (fun k : Fin 2 => torusRawJet_ae (w i)
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
  filter_upwards [hj, coupledHighGradientCLM_ae K i (coupledCarrierHighJets K w)] with x hx hg
  rw [hg]
  exact congrArg (WithLp.toLp 2) (funext hx)

omit [Fintype ι] in
theorem torusRawCarrierTensor_ae (K : ι → ℕ) (w : ∀ i, TorusHk (K i + 1) (h i))
    (i : ι) (m : ℕ) (hm : m ≤ K i + 1) :
    (fun x => WithLp.toLp 2 (fun word : DerivativeWord2 m => (w i).toFunction.jet
      ⟨⟨m, Nat.lt_succ_of_le hm⟩, word⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
        coupledHighTensorCLM (h := h) K i m hm (coupledCarrierHighJets K w) := by
  have hj := ae_all_iff.mpr (fun word : DerivativeWord2 m => torusRawJet_ae (w i)
    ⟨⟨m, Nat.lt_succ_of_le hm⟩, word⟩)
  filter_upwards [hj, coupledHighTensorCLM_ae K i m hm (coupledCarrierHighJets K w)] with x hx hg
  rw [hg]
  exact congrArg (WithLp.toLp 2) (funext hx)

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Literal value representatives of the assembled derivative tensors. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The assembled carrier has exactly the finite vector of the component value representatives. -/
theorem torusFamilyTensor_value_ae {K : ℕ} (w : J → TorusHk K E) :
    (torusFamilyTensor w).val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (WithLp.toLp 2 (fun j => (w j).val (valueIndex2 K) x) : PiLp 2 (fun _ : J => E)) := by
  rw [torusFamilyTensor_jet]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun j : J =>
    (tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict AVenhance.unitCube)
      ((w j).val (valueIndex2 K)))
  have ht : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j : J,
      ((tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict AVenhance.unitCube)
        ((w j).val (valueIndex2 K))) x = tensorEntryCLM (J := J) (E := E) j ((w j).val (valueIndex2 K) x) :=
    ae_all_iff.mpr (fun j => ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := J) (E := E) j) _)
  filter_upwards [hs, ht] with x hx hterms
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterms]
  change (∑ k : J, PiLp.single 2 k ((w k).val (valueIndex2 K) x) j) = _
  simp

variable {K r : ℕ}

/-- The value of an ordered derivative tensor is the complete original order-r jet array. -/
theorem torusDerivativeTensor_value_ae (w : TorusHk (K + r) E) :
    (torusDerivativeTensor w).val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun a : DerivativeWord2 r => w.val ⟨⟨r, by omega⟩, a⟩ x) := by
  have ht := torusFamilyTensor_value_ae (fun a : DerivativeWord2 r => derivativeTorusHk a w)
  have hval (a : DerivativeWord2 r) :
      (derivativeTorusHk a w).val (valueIndex2 K) = w.val ⟨⟨r, by omega⟩, a⟩ := by
    rw [derivativeTorusHk_apply]
    have hi : prefixJetIndex a (valueIndex2 K) = (⟨⟨r, by omega⟩, a⟩ : JetIndex2 (K + r)) := by
      simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
    rw [hi]
  simpa only [torusDerivativeTensor, hval] using ht

/-- Reserve-compatible positive tensors retain the literal original derivative array at value order. -/
theorem torusPositiveDerivativeTensor_value_ae {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) (w : TorusHk (L + 1) E) :
    (torusPositiveDerivativeTensor m hm hKL w).val (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
      (WithLp.toLp 2 (fun a : DerivativeWord2 m => w.val ⟨⟨m, by omega⟩, a⟩ x) :
        PiLp 2 (fun _ : DerivativeWord2 m => E)) := by
  cases m with
  | zero => omega
  | succ s =>
    have ht := torusDerivativeTensor_value_ae
      (truncateTorusHk (by omega : K + (s + 1) ≤ L + 1) w)
    simpa only [torusPositiveDerivativeTensor, torusGradientReserveTensor,
      truncateTorusHk_apply, truncateJetIndex] using ht

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact integrable value tests for the raw periodic representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusRawValue_pairing_integrable_and_integral {K L : ℕ}
    (u : TorusHk K E) (φ : TorusHk L E) :
    Integrable (fun x => inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) =
      inner ℝ (Galerkin.torusHkValueCLM u) (Galerkin.torusHkValueCLM φ) := by
  have he : (fun x => inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => inner ℝ (Galerkin.torusHkValueCLM u x) (Galerkin.torusHkValueCLM φ x)) := by
    filter_upwards [torusRawValue_ae u, torusRawValue_ae φ] with x hu hp
    rw [hu, hp]
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) _ _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, L2.inner_def]

end AVRegularity.CoupledEnergy.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Cell L² drift bounds, through the multiplication tensor estimate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Hilbert array of one positional drift contribution. -/
def driftMaskL2Array {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a)) (m : PositionMask j) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict AVenhance.unitCube) E) :=
  WithLp.toLp 2 fun w => (driftMaskTerm_memLp hj v hv D hc m w).toLp
    (driftMaskTerm hj v D m w)

omit [BorelSpace E] in
/-- No dimension factor is lost when integrating the pointwise drift-array estimate. -/
theorem driftMaskL2Array_normSq_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a))
    (hD : JetMemL2On AVenhance.unitCube D) (m : PositionMask j)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ AVenhance.unitCube,
      ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    ‖driftMaskL2Array hj v hv D hc m‖ ^ 2 ≤ M ^ 2 *
      derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ := by
  classical
  let r : Fin (K + 2) := ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩
  let T := fun w : DerivativeWord2 j => driftMaskTerm hj v D m w
  have hT : ∀ w, MemLp (T w) 2 (volume.restrict AVenhance.unitCube) :=
    driftMaskTerm_memLp hj v hv D hc m
  have hleft := integrable_finsetSum Finset.univ (fun w _ => integrable_normSq_of_memLp (hT w))
  have hright := integrable_finsetSum Finset.univ
    (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))
  calc
    ‖driftMaskL2Array hj v hv D hc m‖ ^ 2 =
        ∫ x in AVenhance.unitCube, ∑ w : DerivativeWord2 j, ‖T w x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ w : DerivativeWord2 j, ‖(hT w).toLp (T w)‖ ^ 2) = _
      simp_rw [normSq_toLp_eq_integral]
      exact (integral_finsetSum Finset.univ
        (fun w _ => integrable_normSq_of_memLp (hT w))).symm
    _ ≤ ∫ x in AVenhance.unitCube, M ^ 2 *
        ∑ w : DerivativeWord2 r.val, ‖D ⟨r, w⟩ x‖ ^ 2 := by
      apply integral_mono_ae hleft (hright.const_mul (M ^ 2))
      filter_upwards [ae_restrict_mem
        AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable]
        with x hx
      exact driftMaskTerm_pointwise_sumSq_le hj v D m x hM (hb x hx)
    _ = M ^ 2 * derivativeNormSq (jetToL2 D hD) r := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))]
      change M ^ 2 * (∑ w : DerivativeWord2 r.val,
        ∫ x in AVenhance.unitCube, ‖D ⟨r, w⟩ x‖ ^ 2) =
        M ^ 2 * ∑ w : DerivativeWord2 r.val, ‖(hD ⟨r, w⟩).toLp (D ⟨r, w⟩)‖ ^ 2
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      exact (normSq_toLp_eq_integral (hD ⟨r, w⟩)).symm

omit [BorelSpace E] in
/-- Unsquared version of the cell drift-array estimate. -/
theorem driftMaskL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a))
    (hD : JetMemL2On AVenhance.unitCube D) (m : PositionMask j)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ AVenhance.unitCube,
      ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    ‖driftMaskL2Array hj v hv D hc m‖ ≤ M * Real.sqrt
      (derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩) := by
  have hnonneg : 0 ≤ derivativeNormSq (jetToL2 D hD)
      ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hnonneg]
  exact driftMaskL2Array_normSq_le hj v hv D hc hD m hM hb

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Closed-time lower weak limits can be tested against the moving Fourier
projections used in the finite integrated equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A fixed component value readout of the lower ambient jets. -/
def coupledLowValueCLM (K : ι → ℕ) (i : ι) : CoupledLowHilbert (h := h) K →L[ℝ]
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 (K i) =>
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) (valueIndex2 (K i))).comp
      (PiLp.proj (𝕜 := ℝ) 2
        (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j) (h j)) i)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
@[simp] theorem coupledLowValueCLM_apply (K : ι → ℕ) (i : ι)
    (U : CoupledLowHilbert (h := h) K) :
    coupledLowValueCLM (h := h) K i U = U i (valueIndex2 (K i)) := rfl

/-- The spatial value pairing converges at a closed time despite its moving projected test. -/
theorem coupledLow_projected_test_weak_limit (K : ι → ℕ) (i : ι)
    (U : ℕ → CoupledLowHilbert (h := h) K) (V : CoupledLowHilbert (h := h) K)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => ∫ x in AVenhance.unitCube,
      inner ℝ (U n i (valueIndex2 (K i)) x)
        (Galerkin.torusHkValueCLM (Galerkin.galerkinProj (N n) φ) x)) atTop
      (𝓝 (∫ x in AVenhance.unitCube,
        inner ℝ (V i (valueIndex2 (K i)) x) (Galerkin.torusHkValueCLM φ x))) := by
  let B := pullbackInnerCLM (ContinuousLinearMap.id ℝ
    (ComponentL2 (volume.restrict AVenhance.unitCube) (h i))) (coupledLowValueCLM (h := h) K i)
  have hz := (Galerkin.torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
    ((Galerkin.galerkinProj_tendsto φ).comp hN.tendsto_atTop)
  have ht := bilinear_weak_limit_moving_test B U V Q hu hw
    (fun n => Galerkin.torusHkValueCLM (Galerkin.galerkinProj (N n) φ))
    (Galerkin.torusHkValueCLM φ) hz
  simpa only [B, pullbackInnerCLM_apply, ContinuousLinearMap.id_apply,
    coupledLowValueCLM_apply, real_inner_comm, L2.inner_def] using ht

end AVRegularity.CoupledEnergy.Variational
end
