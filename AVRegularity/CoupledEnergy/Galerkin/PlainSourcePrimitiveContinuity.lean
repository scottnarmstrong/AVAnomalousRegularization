-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
public import AVRegularity.CoupledEnergy.Galerkin.PlainSmoothFluxIBP
public import AVRegularity.CoupledEnergy.Galerkin.PlainHigherSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
public import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
import AVRegularity.CoupledEnergy.Variational.TorusCoefficientCarrierMeasurable
import AVRegularity.CoupledEnergy.Galerkin.PlainSourceEnergy
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Ordered jets of the reconstructed finite source, with no time-regularity
assumptions and no change to the weak forcing carriers. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourceCoefficients_jet_eq (N : ℕ) (K : ι → ℕ) (i : ι)
    {r : ℕ} (hr : r ≤ K i) (w : DerivativeWord2 r)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) :
    (coupledPlainSynthesis N i (K i) (plainSourceCoefficients N K F g)).val
      ⟨⟨r, by omega⟩, w⟩ = (galerkinProj N (g i)).val ⟨⟨r, by omega⟩, w⟩ +
      ∑ k : Fin 2, (smoothFourierLift (K := K i) (L := K i + 1) N
        (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
          ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩ := by
  change plainJetSynthesisCLM N i (K i) ⟨⟨r, by omega⟩, w⟩
    (plainSourceCoefficients N K F g) = _
  rw [plainSourceCoefficients_eq_value_add_divergence]
  change plainJetSynthesisCLM N i (K i) ⟨⟨r, by omega⟩, w⟩
    (plainInitialCoefficients N K g + ∑ k : Fin 2,
      plainDerivativeCoefficients N 0 (fun _ : Fin 1 => k) (plainInitialCoefficients N K
        (fun j => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h j) k) (F j)))) = _
  rw [map_add, map_sum]
  simp only [plainJetSynthesisCLM_apply, plainInitialCoefficients_synthesis]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [plainDerivativeCoefficients_direction_jet hr,
    plainInitialCoefficients_synthesis_smoothLift]
end

/-! Identify the common ambient readouts with the actual plain Galerkin jets
and tensors. This identification is made after solving the coefficient ODE. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A fixed tensor readout is the literal tensor of the finite Fourier sum. -/
theorem plainHigherTensor_readout_ae (N : ℕ) (K : ι → ℕ) (i : ι)
    (m : ℕ) (hm : m ≤ K i + 1) (c : CoupledPlainCoefficients (h := h) N) :
    coupledHighTensorCLM (h := h) K i m hm (plainHigherSynthesisCLM N K c) =ᵐ[
      volume.restrict AVenhance.unitCube] coupledPlainRawTensor N c i m := by
  have hjet : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ w : DerivativeWord2 m,
      (coupledPlainSynthesis N i (K i + 1) c).val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ x =
        coupledPlainRawJet N c i m w x := by
    rw [ae_all_iff]
    intro w
    exact coupledPlainSynthesis_jet_ae N i (K i + 1) c ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩
  filter_upwards [coupledHighTensorCLM_ae K i m hm (plainHigherSynthesisCLM N K c), hjet] with x hx hj
  rw [hx]
  apply PiLp.ext
  intro w
  exact hj w

/-- The finite Bochner class represents the original synthesized coefficient path. -/
theorem plainHigherBochner_readout_ae (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) :
    plainHigherBochner N K a b hab y =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => plainHigherSynthesisCLM N K (AVenhance.Infra.ODE.extendCurve hab y t) :=
  (plainHigherSynthesis_memLp N K a b (AVenhance.Infra.ODE.continuous_extendCurve hab y)).coeFn_toLp
end

/-! Testing the actual finite Bochner class gives the synthesized ODE path
on every closed-time subinterval. No additional measurability is needed for
this representative identity. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Any scalar test of the actual Bochner class equals the test of its synthesized path. -/
theorem plainHigherBochner_test_integral (N : ℕ) (K : ι → ℕ)
    {a b s t : ℝ} (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hst : s ≤ t) (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N))
    (B : ℝ → CoupledHighHilbert (h := h) K → ℝ) :
    (∫ r in s..t, B r (plainHigherBochner N K a b hab y r)) =
      ∫ r in s..t, B r (plainHigherSynthesisCLM N K (AVenhance.Infra.ODE.extendCurve hab y r)) := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hst]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
    (plainHigherBochner_readout_ae N K a b hab y)] with r hr
  rw [hr]
end

/-! Test the reconstructed source against a different finite Fourier cutoff.
Exact periodic integration by parts leaves one derivative on the test and
retains the original weak flux at its declared Sobolev order. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourceCoefficients_external_jet_pairing (N M : ℕ) (K : ι → ℕ) (i : ι)
    {r : ℕ} (hr : r ≤ K i) (w : DerivativeWord2 r)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) (c : CoupledPlainCoefficients (h := h) M) :
    inner ℝ ((coupledPlainSynthesis N i (K i) (plainSourceCoefficients N K F g)).val
      ⟨⟨r, by omega⟩, w⟩) ((coupledPlainSynthesis M i (K i) c).val ⟨⟨r, by omega⟩, w⟩) =
      inner ℝ ((galerkinProj N (g i)).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis M i (K i) c).val ⟨⟨r, by omega⟩, w⟩) -
      ∑ k : Fin 2, inner ℝ ((galerkinProj N
        (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
          ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis M i (K i + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  rw [plainSourceCoefficients_jet_eq N K i hr w F g, inner_add_left, sum_inner]
  simp_rw [plainSmoothFlux_jet_partial_ibp hr N M i w]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
end

/-! The forcing contribution to the difference of two cutoff energies.
Self-adjoint spectral testing and periodic integration by parts are already
proved in the external-cutoff pairing, so no cutoff nesting is needed. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourceCoefficients_band_jet_pairing (N M : ℕ) (K : ι → ℕ) (i : ι)
    {r : ℕ} (hr : r ≤ K i) (w : DerivativeWord2 r)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i))
    (c : CoupledPlainCoefficients (h := h) N) (d : CoupledPlainCoefficients (h := h) M) :
    inner ℝ
      ((coupledPlainSynthesis N i (K i) (plainSourceCoefficients N K F g)).val ⟨⟨r, by omega⟩, w⟩ -
        (coupledPlainSynthesis M i (K i) (plainSourceCoefficients M K F g)).val ⟨⟨r, by omega⟩, w⟩)
      ((coupledPlainSynthesis N i (K i) c).val ⟨⟨r, by omega⟩, w⟩ -
        (coupledPlainSynthesis M i (K i) d).val ⟨⟨r, by omega⟩, w⟩) =
      inner ℝ ((galerkinProj N (g i)).val ⟨⟨r, by omega⟩, w⟩ -
        (galerkinProj M (g i)).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i (K i) c).val ⟨⟨r, by omega⟩, w⟩ -
          (coupledPlainSynthesis M i (K i) d).val ⟨⟨r, by omega⟩, w⟩) -
      ∑ k : Fin 2, inner ℝ
        ((galerkinProj N (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
            ⟨⟨r, by omega⟩, w⟩ -
          (galerkinProj M (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
            ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i (K i + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩ -
          (coupledPlainSynthesis M i (K i + 1) d).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  simp only [inner_sub_left, inner_sub_right]
  simp_rw [plainSourceCoefficients_external_jet_pairing _ _ K i hr w F g]
  simp only [Finset.sum_sub_distrib]
  ring
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Strong convergence and weak-limit identification of the actual initial
Fourier jets in the fixed lower-order ambient Hilbert space. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- All actual initial Fourier jets converge strongly to the original initial data. -/
theorem plainInitialLower_tendsto (K : ι → ℕ) (f : ∀ i, TorusHk (K i) (h i)) :
    Tendsto (fun N => plainLowerSynthesisCLM N K (plainInitialCoefficients N K f)) atTop
      (𝓝 (WithLp.toLp 2 (fun i => (f i).val) : CoupledLowHilbert (h := h) K)) := by
  have hp : Tendsto (fun N i => (galerkinProj N (f i)).val) atTop
      (𝓝 (fun i => (f i).val)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact continuous_subtype_val.continuousAt.tendsto.comp (galerkinProj_tendsto (f i))
  have ht := (PiLp.continuous_toLp 2
    (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))).continuousAt.tendsto.comp hp
  convert ht using 1
  funext N
  apply PiLp.ext
  intro i
  exact congrArg Subtype.val (plainInitialCoefficients_synthesis N K f i)

/-- A scalar-observable weak limit of initial Fourier jets equals the prescribed initial data. -/
theorem plainInitialLower_weak_limit_eq (K : ι → ℕ) (f : ∀ i, TorusHk (K i) (h i))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (V : CoupledLowHilbert (h := h) K)
    (hw : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (φ n) K
        (plainInitialCoefficients (φ n) K f))) atTop (𝓝 (ell V))) :
    V = WithLp.toLp 2 (fun i => (f i).val) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ell
  exact tendsto_nhds_unique (hw ell)
    (ell.continuous.continuousAt.tendsto.comp ((plainInitialLower_tendsto K f).comp hφ.tendsto_atTop))

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The explicit finite gradient is the gradient carrier used by the coupling estimate. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The smooth finite gradient bundle agrees with the derivative-based Sobolev gradient. -/
theorem coupledPlainGradientHk_eq_gradientTensor (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (K : ℕ) :
    coupledPlainGradientHk N c i K = torusGradientTensor (coupledPlainSynthesis N i (K + 1) c) := by
  apply TorusHk.ext_value
  apply Lp.ext
  rw [torusGradientTensor, torusFamilyTensor_jet]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun k : Fin 2 =>
    (tensorEntryCLM (E := h i) k).compLpL 2 (volume.restrict AVenhance.unitCube)
      ((derivativeTorusHk (fun _ : Fin 1 => k) (coupledPlainSynthesis N i (K + 1) c)).val
        (valueIndex2 K)))
  have ht : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      ((tensorEntryCLM (E := h i) k).compLpL 2 (volume.restrict AVenhance.unitCube)
        ((derivativeTorusHk (fun _ : Fin 1 => k) (coupledPlainSynthesis N i (K + 1) c)).val
          (valueIndex2 K))) x =
        tensorEntryCLM k (coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x) := by
    rw [ae_all_iff]
    intro k
    rw [derivativeTorusHk_value_slot]
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (E := h i) k)
      ((coupledPlainSynthesis N i (K + 1) c).val ⟨⟨1, by omega⟩, fun _ => k⟩),
      coupledPlainSynthesis_jet_ae N i (K + 1) c ⟨⟨1, by omega⟩, fun _ => k⟩] with x hx hd
    rw [hx, hd]
  filter_upwards [coupledPlainGradientHk_jet_ae N c i K (valueIndex2 K), hs, ht] with x hx hsum hterms
  rw [hx, hsum, Finset.sum_apply]
  exact (Finset.sum_congr rfl (fun k _ => hterms k)).symm

/-- The actual finite gradient has exactly the factorial gradient square. -/
theorem coupledPlainGradientHk_factorialNormSq (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (K : ℕ) (ρ : ℝ) :
    factorialNormSq ρ (coupledPlainGradientHk N c i K).val =
      gradFactorialNormSq ρ (coupledPlainSynthesis N i (K + 1) c).val := by
  rw [coupledPlainGradientHk_eq_gradientTensor, torusGradientTensor_factorialNormSq]

/-- Each gradient-carrier jet coordinate is the original field's final directional partial. -/
theorem coupledPlainGradientHk_jet_coordinate (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (K : ℕ) (a : JetIndex2 K) (k : Fin 2) :
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL 2 (volume.restrict AVenhance.unitCube))
      ((coupledPlainGradientHk N c i K).val a) =
      (coupledPlainSynthesis N i (K + 1) c).val ⟨⟨a.1.val + 1, by omega⟩, Fin.snoc a.2 k⟩ := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) ((coupledPlainGradientHk N c i K).val a),
    coupledPlainGradientHk_jet_ae N c i K a,
    coupledPlainSynthesis_jet_ae N i (K + 1) c ⟨⟨a.1.val + 1, by omega⟩, Fin.snoc a.2 k⟩] with x hx hg hs
  rw [hx]
  change (coupledPlainGradientHk N c i K).val a x k = _
  rw [hg, coupledPlainGradientJet_apply, hs]
end

/-! The forcing contribution to the difference of two cutoff energies.
Self-adjoint spectral testing and periodic integration by parts are already
proved in the external-cutoff pairing, so no cutoff nesting is needed. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourceCoefficients_trace_band_jet_pairing (N M : ℕ) (K : ι → ℕ) (i : ι)
    {r : ℕ} (hr : r ≤ K i) (word : DerivativeWord2 r)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, TorusHk (K i) (h i)) (w : ∀ i, TorusHk (K i + 1) (h i))
    (hu : ∀ i, u i = truncateTorusHk (Nat.le_succ (K i)) (w i)) :
    inner ℝ
      ((coupledPlainSynthesis N i (K i) (plainSourceCoefficients N K F g)).val ⟨⟨r, by omega⟩, word⟩ -
        (coupledPlainSynthesis M i (K i) (plainSourceCoefficients M K F g)).val ⟨⟨r, by omega⟩, word⟩)
      ((galerkinProj N (u i)).val ⟨⟨r, by omega⟩, word⟩ -
        (galerkinProj M (u i)).val ⟨⟨r, by omega⟩, word⟩) =
      inner ℝ ((galerkinProj N (g i)).val ⟨⟨r, by omega⟩, word⟩ -
        (galerkinProj M (g i)).val ⟨⟨r, by omega⟩, word⟩)
        ((galerkinProj N (u i)).val ⟨⟨r, by omega⟩, word⟩ -
          (galerkinProj M (u i)).val ⟨⟨r, by omega⟩, word⟩) -
      ∑ k : Fin 2, inner ℝ
        ((galerkinProj N (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
            ⟨⟨r, by omega⟩, word⟩ -
          (galerkinProj M (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (F i))).val
            ⟨⟨r, by omega⟩, word⟩)
        ((galerkinProj N (w i)).val ⟨⟨r + 1, by omega⟩, Fin.snoc word k⟩ -
          (galerkinProj M (w i)).val ⟨⟨r + 1, by omega⟩, Fin.snoc word k⟩) := by
  have he := plainSourceCoefficients_band_jet_pairing N M K i hr word F g
    (plainInitialCoefficients N K u) (plainInitialCoefficients M K u)
  have hs (L : ℕ) : coupledPlainSynthesis L i (K i + 1) (plainInitialCoefficients L K u) =
      galerkinProj L (w i) := by
    have hu' : u = fun i => truncateTorusHk (Nat.le_succ (K i)) (w i) := funext hu
    rw [hu']
    exact plainInitialCoefficients_higher_synthesis L K w i
  rw [hs N, hs M] at he
  simpa only [plainInitialCoefficients_synthesis] using he
end

/-! The fixed ambient gradient and projected test readouts represent the
literal finite Fourier gradients appearing in the projected equation. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The common high-order readout is the actual finite two-coordinate gradient. -/
theorem plainHigherGradient_readout_ae (N : ℕ) (K : ι → ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) :
    coupledHighGradientCLM (h := h) K i (plainHigherSynthesisCLM N K c) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => WithLp.toLp 2
        (fun k : Fin 2 => coupledPlainRawJet N c i 1 (fun _ => k) x) := by
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (coupledPlainSynthesis N i (K i + 1) c).val
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x =
      coupledPlainRawJet N c i 1 (fun _ => k) x := by
    rw [ae_all_iff]
    intro k
    exact coupledPlainSynthesis_jet_ae N i (K i + 1) c _
  filter_upwards [coupledHighGradientCLM_ae K i (plainHigherSynthesisCLM N K c), hj]
    with x hx hjx
  rw [hx]
  apply PiLp.ext
  exact hjx

/-- The H¹ synthesis gradient agrees with its literal finite Fourier sum. -/
theorem plainSynthesis_gradient_readout_ae (N : ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) :
    torusH1GradientL2CLM (E := h i) (coupledPlainSynthesis N i 1 c) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => WithLp.toLp 2
        (fun k : Fin 2 => coupledPlainRawJet N c i 1 (fun _ => k) x) := by
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (coupledPlainSynthesis N i 1 c).val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x =
      coupledPlainRawJet N c i 1 (fun _ => k) x := by
    rw [ae_all_iff]
    intro k
    exact coupledPlainSynthesis_jet_ae N i 1 c _
  filter_upwards [torusH1GradientL2CLM_ae (coupledPlainSynthesis N i 1 c), hj] with x hx hjx
  rw [hx]
  apply PiLp.ext
  exact hjx

/-- Projected H¹ tests have the literal gradient used by the coefficient equation. -/
theorem plainProjectedTest_gradient_ae (N : ℕ) (φ : ∀ i, TorusHk 1 (h i)) (i : ι) :
    torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => WithLp.toLp 2
        (fun k : Fin 2 => coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ)
          i 1 (fun _ => k) x) := by
  rw [← plainInitialCoefficients_synthesis N (fun _ => 1) φ i]
  exact plainSynthesis_gradient_readout_ae N i _
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Lower-order weak compactness along any already chosen Fourier cutoffs.
This permits closed-time extraction from the common spacetime subsequence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A bounded actual finite mass sequence has a graph-valued lower weak limit,
including when the finite cutoffs were selected by an earlier limit. -/
theorem plainLower_mass_subsequence (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (N : ℕ → ℕ)
    (c : (n : ℕ) → CoupledPlainCoefficients (h := h) (N n))
    (C : ℝ) (hc : ∀ n, massNormSq ρ π
      (fun i => (coupledPlainSynthesis (N n) i (K i) (c n)).val) ≤ C) :
    ∃ (V : CoupledLowHilbert (h := h) K) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
        Tendsto (fun n => ell (plainLowerSynthesisCLM (N (ψ n)) K (c (ψ n))))
          atTop (𝓝 (ell V))) ∧
      (∀ i, V i ∈ torusHkGraph (E := h i) (K i)) ∧
      ‖V‖ ≤ Real.sqrt ((∑ i, π i / factorialWeightMin ρ (K i)) * C) := by
  let Q : ℝ := ∑ i, π i / factorialWeightMin ρ (K i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ (K := K i)).le)
  have hn (n : ℕ) : ‖plainLowerSynthesisCLM (N n) K (c n)‖ ≤ Real.sqrt (Q * C) := by
    have hsq := (plainLowerSynthesis_normSq_le_mass (N n) K ρ hρ π hπ (c n)).trans
      (mul_le_mul_of_nonneg_left (hc n) hQ)
    simpa only [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq
  obtain ⟨V, ψ, hψ, hw⟩ := exists_strictMono_tendsto_lowHilbert_clm K
    (Real.sqrt (Q * C)) (fun n => plainLowerSynthesisCLM (N n) K (c n)) hn
  refine ⟨V, ψ, hψ, hw, ?_, ?_⟩
  · apply lowHilbert_graph_of_weak_limit K hw
    intro n i
    exact (coupledPlainSynthesis (N (ψ n)) i (K i) (c (ψ n))).property
  · exact coupledLowHilbert_norm_le_of_weak_limit K _ V _ (fun n => hn (ψ n)) hw

/-- Initial identification remains valid after two successive subsequence selections. -/
theorem plainInitialLower_subsubsequence_eq (K : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (N ψ : ℕ → ℕ)
    (hN : StrictMono N) (hψ : StrictMono ψ) (V : CoupledLowHilbert (h := h) K)
    (hw : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (N (ψ n)) K
        (plainInitialCoefficients (N (ψ n)) K f))) atTop (𝓝 (ell V))) :
    V = WithLp.toLp 2 (fun i => (f i).val) :=
  plainInitialLower_weak_limit_eq K f (N ∘ ψ) (hN.comp hψ) V hw

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Exact conversion of differentiated flux testing to the Hilbert gradient pairing. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The directional flux test is exactly the assembled gradient Hilbert pairing. -/
theorem plainFlux_jet_pairing (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) (a : JetIndex2 K) :
    (∑ k : Fin 2, inner ℝ
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
        2 (volume.restrict AVenhance.unitCube)) (F.val a))
      ((coupledPlainSynthesis N i (K + 1) c).val ⟨⟨a.1.val + 1, by omega⟩, Fin.snoc a.2 k⟩)) =
      inner ℝ (F.val a) ((coupledPlainGradientHk N c i K).val a) := by
  rw [tensorL2_inner_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coupledPlainGradientHk_jet_coordinate]

/-- Summing the differentiated flux tests gives the exact factorial gradient pairing. -/
theorem plainFlux_factorial_pairing (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (ρ : ℝ) (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
      ∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) (F.val ⟨j, w⟩))
        ((coupledPlainSynthesis N i (K + 1) c).val ⟨⟨j.val + 1, by omega⟩, Fin.snoc w k⟩)) =
      inner ℝ (factorialWeightedJet ρ F.val)
        (factorialWeightedJet ρ (coupledPlainGradientHk N c i K).val) := by
  simp_rw [plainFlux_jet_pairing]
  rw [factorialWeightedJet_inner]
end

/-! The physical forcing form of the finite Fourier band energy identity.
Only integrable finite coefficient primitives are used in the chain rule. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourcePrimitive_bandJet_identity (N M : ℕ) (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (H : ∀ i, ℝ → TorusHk (K i) (h i))
    (hS : ∀ i, MemLp (S i) 2 (volume.restrict (Set.Icc a b)))
    (hH : ∀ i, Integrable (H i) (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hprim : ∀ L, ∀ t ∈ Set.Icc a b,
      plainInitialCoefficients L K (fun i => u i t) = plainInitialCoefficients L K f +
        ∫ r in a..t, plainSourceCoefficients L K (fun i => S i r) (fun i => H i r))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) {j : ℕ} (hj : j ≤ K i) (word : DerivativeWord2 j) :
    ‖(galerkinProj N (u i t)).val ⟨⟨j, by omega⟩, word⟩ -
      (galerkinProj M (u i t)).val ⟨⟨j, by omega⟩, word⟩‖ ^ 2 -
      ‖(galerkinProj N (f i)).val ⟨⟨j, by omega⟩, word⟩ -
        (galerkinProj M (f i)).val ⟨⟨j, by omega⟩, word⟩‖ ^ 2 =
    ∫ r in a..t, 2 * inner ℝ
      ((galerkinProj N (u i r)).val ⟨⟨j, by omega⟩, word⟩ -
        (galerkinProj M (u i r)).val ⟨⟨j, by omega⟩, word⟩)
      ((coupledPlainSynthesis N i (K i)
          (plainSourceCoefficients N K (fun i => S i r) (fun i => H i r))).val ⟨⟨j, by omega⟩, word⟩ -
        (coupledPlainSynthesis M i (K i)
          (plainSourceCoefficients M K (fun i => S i r) (fun i => H i r))).val ⟨⟨j, by omega⟩, word⟩) := by
  let q : (L : ℕ) → ℝ → CoupledPlainCoefficients (h := h) L := fun L r =>
    plainSourceCoefficients L K (fun i => S i r) (fun i => H i r)
  let c : (L : ℕ) → ℝ → CoupledPlainCoefficients (h := h) L := fun L r =>
    plainInitialCoefficients L K (fun i => u i r)
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hi (L : ℕ) : IntervalIntegrable (q L) volume a t :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (plainSourceCoefficients_integrable L K a b S H hS hH)).mono_set hsub
  have hp (L : ℕ) : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) (q L)
      (plainInitialCoefficients L K f) a t (c L) := by
    intro r hr
    have hh : AVenhance.Infra.ODE.linearRhs
        (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) (q L) (c L) = q L := by
      funext s
      simp only [AVenhance.Infra.ODE.linearRhs, plainMatrixCLM_zero_apply, zero_add]
    rw [hh]
    exact hprim L r ⟨hr.1, hr.2.trans ht.2⟩
  have he := plainPrimitive_band_energy_identity ht.1 (q N) (c N) (q M) (c M)
    (plainInitialCoefficients N K f) (plainInitialCoefficients M K f) (hi N) (hi M) (hp N) (hp M)
    (plainJetSynthesisCLM N i (K i) ⟨⟨j, by omega⟩, word⟩)
    (plainJetSynthesisCLM M i (K i) ⟨⟨j, by omega⟩, word⟩)
  have hc (L : ℕ) : c L a = plainInitialCoefficients L K f := by
    simpa only [intervalIntegral.integral_same, add_zero] using hprim L a ⟨le_rfl, hab⟩
  rw [hc N, hc M] at he
  simp only [plainJetSynthesisCLM_apply, c, plainInitialCoefficients_synthesis] at he
  exact he.symm

theorem plainSourcePrimitive_band_energy (N M : ℕ) (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (H : ∀ i, ℝ → TorusHk (K i) (h i))
    (hS : ∀ i, MemLp (S i) 2 (volume.restrict (Set.Icc a b)))
    (hH : ∀ i, Integrable (H i) (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (huw : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i,
      u i r = truncateTorusHk (Nat.le_succ (K i)) (w i r))
    (hprim : ∀ L, ∀ t ∈ Set.Icc a b,
      plainInitialCoefficients L K (fun i => u i t) = plainInitialCoefficients L K f +
        ∫ r in a..t, plainSourceCoefficients L K (fun i => S i r) (fun i => H i r))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) {j : ℕ} (hj : j ≤ K i) (word : DerivativeWord2 j) :
    ‖(galerkinProj N (u i t)).val ⟨⟨j, by omega⟩, word⟩ -
      (galerkinProj M (u i t)).val ⟨⟨j, by omega⟩, word⟩‖ ^ 2 -
      ‖(galerkinProj N (f i)).val ⟨⟨j, by omega⟩, word⟩ -
        (galerkinProj M (f i)).val ⟨⟨j, by omega⟩, word⟩‖ ^ 2 =
    ∫ r in a..t, 2 * (inner ℝ
      ((galerkinProj N (H i r)).val ⟨⟨j, by omega⟩, word⟩ -
        (galerkinProj M (H i r)).val ⟨⟨j, by omega⟩, word⟩)
      ((galerkinProj N (u i r)).val ⟨⟨j, by omega⟩, word⟩ -
        (galerkinProj M (u i r)).val ⟨⟨j, by omega⟩, word⟩) -
      ∑ k : Fin 2, inner ℝ
        ((galerkinProj N (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (S i r))).val
            ⟨⟨j, by omega⟩, word⟩ -
          (galerkinProj M (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k) (S i r))).val
            ⟨⟨j, by omega⟩, word⟩)
        ((galerkinProj N (w i r)).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩ -
          (galerkinProj M (w i r)).val ⟨⟨j + 1, by omega⟩, Fin.snoc word k⟩)) := by
  have he := plainSourcePrimitive_bandJet_identity N M K hab S H hS hH u f hprim t ht i hj word
  rw [he]
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub' : Set.uIoc a t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le ht.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' huw] with r hr
  rw [real_inner_comm]
  exact congrArg (fun x : ℝ => 2 * x)
    (plainSourceCoefficients_trace_band_jet_pairing N M K i hj word
      (fun i => S i r) (fun i => H i r) (fun i => u i r) (fun i => w i r) hr)
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify scalar closed-time traces of actual plain finite coefficient
curves with the common ambient spacetime weak limit. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Bounded pointwise limits of an actual finite value observable identify its spacetime readout. -/
theorem plainBochner_trace_pairing_eq_ae (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (N : ℕ → ℕ) (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (U : CoupledHighTime (h := h) K a b)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) K a b hab (y n))) atTop (𝓝 (ell U)))
    (i : ι) (φ : TorusHk 1 (h i)) (u : ℝ → ℝ) (hu : AEStronglyMeasurable u
      (volume.restrict (Set.Icc a b))) (R : ℝ)
    (hb : ∀ n, ∀ t ∈ Set.Icc a b,
      ‖torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))‖ ≤ R)
    (ht : ∀ t ∈ Set.Icc a b, Tendsto (fun n => inner ℝ
      (torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))) (torusHkValueCLM φ)) atTop (𝓝 (u t))) :
    u =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      inner ℝ (U t i (valueIndex2 (K i + 1))) (torusHkValueCLM φ) := by
  let ell : CoupledHighHilbert (h := h) K →L[ℝ] ℝ :=
    (innerSL ℝ (torusHkValueCLM φ)).comp (coupledHighJetCLM K i (valueIndex2 (K i + 1)))
  have hz (n : ℕ) : (fun t => inner ℝ
      (torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))) (torusHkValueCLM φ)) =ᵐ[
      volume.restrict (Set.Icc a b)] fun t => ell (plainHigherBochner (N n) K a b hab (y n) t) := by
    filter_upwards [plainHigherBochner_readout_ae (N n) K a b hab (y n)] with t ht
    rw [ht]
    change inner ℝ ((coupledPlainSynthesis (N n) i (K i) (AVenhance.Infra.ODE.extendCurve hab (y n) t)).val (valueIndex2 (K i))) (torusHkValueCLM φ) =
      inner ℝ (torusHkValueCLM φ) ((coupledPlainSynthesis (N n) i (K i + 1) (AVenhance.Infra.ODE.extendCurve hab (y n) t)).val (valueIndex2 (K i + 1)))
    rw [coupledPlainSynthesis_value_order_independent (N n) i (K i) (K i + 1), real_inner_comm]
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖inner ℝ
      (torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))) (torusHkValueCLM φ)‖ ≤ R * ‖torusHkValueCLM φ‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb n t ht) (norm_nonneg _))
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Icc a b), Tendsto (fun n => inner ℝ
      (torusHkValueCLM (coupledPlainSynthesis (N n) i (K i)
        (AVenhance.Infra.ODE.extendCurve hab (y n) t))) (torusHkValueCLM φ)) atTop (𝓝 (u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t hr
    exact ht t hr
  have he := weakLp_scalar_trace_eq_ae (volume.restrict (Set.Icc a b))
    (fun n => plainHigherBochner (N n) K a b hab (y n)) U hw ell _ u _ hz hu hbound hlim
  simpa only [ell, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    coupledHighJetCLM_apply, real_inner_comm] using he

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The Fourier scalar rows of the genuine transport trajectory are time
integrable directly from the original velocity measurability and common
higher-order Bochner readout. No derivative measurability is assumed. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTransport_rows_integrable (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (U : CoupledHighTime (h := h) K a b)
    (T : ∀ i, ℝ → TorusHk (K i) (h i))
    (hT : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (T i t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        ∑ k : Fin 2, v t x k • (U t i
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)) :
    ∀ N, ∀ r : CoupledFourierModeIndex (h := h) N,
      Integrable (fun t => plainInitialCoefficients N K (fun i => T i t) r)
        (volume.restrict (Set.Icc a b)) := by
  intro N r
  let φ := coupledModeHk N r r.1 1
  have hi := integrable_finsetSum Finset.univ (fun k _ =>
    torusDrift_test_integrable K hab v hv hc V hb U r.1 k φ)
  apply hi.congr
  filter_upwards [hT, ae_restrict_mem measurableSet_Icc] with t ht htI
  rw [plainInitialCoefficients_mode_pairing]
  rw [L2.inner_def]
  have hsp (k : Fin 2) : Integrable (fun x => v t x k * inner ℝ
      (coupledHighJetCLM K r.1 ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K r.1))⟩, fun _ => k⟩ (U t) x)
      (torusHkValueCLM φ x)) (volume.restrict AVenhance.unitCube) := by
    exact boundedScalar_inner_integrable (fun x => v t x k)
      ((continuous_apply k).comp (hc t htI)) V hV
      (fun x => (norm_le_pi_norm (v t x) k).trans (hb t htI x)) _ _
  symm
  calc
    _ = ∫ x in AVenhance.unitCube, ∑ k : Fin 2, v t x k * inner ℝ
        (coupledHighJetCLM K r.1 ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K r.1))⟩, fun _ => k⟩ (U t) x)
        (torusHkValueCLM φ x) := by
      apply integral_congr_ae
      filter_upwards [ht r.1] with x hx
      change inner ℝ ((T r.1 t).val (valueIndex2 (K r.1)) x) (torusHkValueCLM φ x) = _
      rw [hx, sum_inner]
      simp only [real_inner_smul_left, coupledHighJetCLM_apply]
    _ = _ := integral_finsetSum Finset.univ (fun k _ => hsp k)
end

/-! The weak transport of a synthesized finite field is exactly the
smooth Fourier transport carrier. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTransport_synthesis (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l) :
    torusTransportCarrier v hv hp C hb (coupledPlainSynthesis N i (K + 1) c) =
      coupledPlainDriftHk N c i K v hv hp := by
  apply TorusHk.ext_value
  apply Lp.ext
  have hs : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (coupledPlainSynthesis N i (K + 1) c).val
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x =
          coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x :=
    ae_all_iff.mpr (fun k => coupledPlainSynthesis_jet_ae N i (K + 1) c
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩)
  filter_upwards [torusTransportCarrier_value_ae v hv hp C hb
    (coupledPlainSynthesis N i (K + 1) c), coupledPlainDriftHk_value_ae N c i K v hv hp,
    hs] with x hx hy hz
  rw [hx, hy]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => v x k • z) (hz k))
end

/-! The sum of admissible coupling carriers retains the literal finite coupling flux. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)

/-- The complete actual admissible coupling flux at a fixed Galerkin time. -/
def plainCouplingFlux (i : ι) : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ i', ∑ d : admissibleOrders K D i i',
    torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht (hC i i' d) (hp i i' d)
      (coupledPlainSynthesis N i' (K i' + 1) c)

/-- The bundled sum reads precisely the sum of the actual Fourier-coefficient coupling actions. -/
theorem plainCouplingFlux_value_ae (i : ι) :
    (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
      ∑ i', ∑ d : admissibleOrders K D i i', A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) := by
  let Q := fun (i' : ι) (d : admissibleOrders K D i i') =>
    torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht (hC i i' d) (hp i i' d)
      (coupledPlainSynthesis N i' (K i' + 1) c)
  have heq : (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) =
      ∑ i', ∑ d : admissibleOrders K D i i', (Q i' d).val (valueIndex2 (K i)) := by
    simp [plainCouplingFlux, Q]
  rw [heq]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i' : ι =>
    ∑ d : admissibleOrders K D i i', (Q i' d).val (valueIndex2 (K i)))
  have hi : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ i' : ι,
      (∑ d : admissibleOrders K D i i', (Q i' d).val (valueIndex2 (K i))) x =
        ∑ d : admissibleOrders K D i i', A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) := by
    rw [ae_all_iff]
    intro i'
    have hd := Lp.coeFn_finsetSum Finset.univ
      (fun d : admissibleOrders K D i i' => (Q i' d).val (valueIndex2 (K i)))
    have hv : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ d : admissibleOrders K D i i',
        (Q i' d).val (valueIndex2 (K i)) x =
          A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) :=
      ae_all_iff.mpr (fun d => plainCoupledFluxTerm_value_ae N c ρ hρ K D a b i i' d
        (A i i' d) (hA i i' d) t ht (hC i i' d) (hp i i' d))
    filter_upwards [hd, hv] with x hx hterms
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun d _ => hterms d)
  filter_upwards [hs, hi] with x hx hterms
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i' _ => hterms i')

/-- The entire literal coupling flux has the exact ν/8 mass energy absorption. -/
theorem plainCouplingFlux_massPairing_abs_le (ν : ℝ) (hν : 0 < ν)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) :
    |∑ i, (π i)⁻¹ * inner ℝ
      (factorialWeightedJet ρ (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val)
      (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val)| ≤
      (ν / 8) * massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) c).val) := by
  let T := fun (i i' : ι) (d : admissibleOrders K D i i') => inner ℝ
    (factorialWeightedJet ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d)
      (hA i i' d) t ht (hC i i' d) (hp i i' d)
      (coupledPlainSynthesis N i' (K i' + 1) c)).val)
    (factorialWeightedJet ρ (torusGradientTensor (coupledPlainSynthesis N i (K i + 1) c)).val)
  have heq (i : ι) : inner ℝ
      (factorialWeightedJet ρ (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val)
      (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) =
      ∑ i', ∑ d : admissibleOrders K D i i', T i i' d := by
    rw [coupledPlainGradientHk_eq_gradientTensor]
    simp [plainCouplingFlux, factorialWeightedJet_sum, sum_inner, T]
  simp_rw [heq, Finset.mul_sum]
  refine le_trans ?_ (torusCoupledFlux_schurEnergy_abs_sum_le ν ρ hν hρ π hπ K D a b A hA
    t ht hC hp hschur (fun i => coupledPlainSynthesis N i (K i + 1) c))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i' _
  have hb := Finset.abs_sum_le_sum_abs
    (fun d : admissibleOrders K D i i' => (π i)⁻¹ * T i i' d) Finset.univ
  simpa only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (hπ i).le), T] using hb
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Discharge the spectral-tail estimate from actual finite source
primitives of a bounded weak trace. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourcePrimitive_bandJet_tail_bound (N M : ℕ) (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (H : ∀ i, ℝ → TorusHk (K i) (h i))
    (hS : ∀ i, MemLp (S i) 2 (volume.restrict (Set.Icc a b)))
    (hH : ∀ i, Integrable (H i) (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (huw : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i,
      u i r = truncateTorusHk (Nat.le_succ (K i)) (w i r))
    (hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b))
    (R : ℝ) (hub : ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R)
    (hprim : ∀ L, ∀ t ∈ Set.Icc a b,
      plainInitialCoefficients L K (fun i => u i t) = plainInitialCoefficients L K f +
        ∫ r in a..t, plainSourceCoefficients L K (fun i => S i r) (fun i => H i r))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) (j : JetIndex2 (K i)) :
    ‖torusBandJetCLM (K i) N M j (u i t)‖ ^ 2 ≤
      torusSourceTailBudget N a b R (f i) (H i) (S i) (w i) +
        torusSourceTailBudget M a b R (f i) (H i) (S i) (w i) := by
  have he := plainSourcePrimitive_band_energy N M K hab S H hS hH u f w huw hprim
    t ht i (Nat.le_of_lt_succ j.1.isLt) j.2
  apply torusBandJet_sqNorm_le_tailBudget N M ht (Nat.le_of_lt_succ j.1.isLt) j.2 R
    (f i) (H i) (u i) (S i) (w i) (hH i) (hS i) (hw i)
    (plainTrace_aestronglyMeasurable K a b u hcont i) (hub i)
  simpa only [torusBandJetCLM_apply, torusBandSourceIntegrand] using he

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Literal finite Fourier pairings equal the fixed ambient and projected
carrier pairings used to pass through the common weak limit. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The projected value test represents its literal finite Fourier sum. -/
theorem plainProjectedTest_value_ae (N : ℕ) (φ : ∀ i, TorusHk 1 (h i)) (i : ι) :
    torusHkValueCLM (galerkinProj N (φ i)) =ᵐ[volume.restrict AVenhance.unitCube]
      coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 0 Fin.elim0 := by
  rw [← plainInitialCoefficients_synthesis N (fun _ => 1) φ i]
  exact coupledPlainSynthesis_jet_ae N i 1 _ (valueIndex2 1)

/-- The literal finite diffusion pairing equals the ambient gradient pairing. -/
theorem plainDiffusion_test_integral (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (φ : ∀ i, TorusHk 1 (h i)) (i : ι) :
    (∫ x in AVenhance.unitCube,
      inner ℝ (coupledHighGradientCLM (h := h) K i (plainHigherSynthesisCLM N K c) x)
        (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) x)) =
    ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
        (coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 1 (fun _ => k) x) := by
  apply integral_congr_ae
  filter_upwards [plainHigherGradient_readout_ae N K i c, plainProjectedTest_gradient_ae N φ i]
    with x hc hφ
  rw [hc, hφ, PiLp.inner_apply]

/-- The literal finite coupling pairing equals its fixed admissible tensor readout. -/
theorem plainCoupling_test_integral (N D : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (φ : ∀ i, TorusHk 1 (h i))
    (i i' : ι) (d : admissibleOrders K D i i')
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) :
    (∫ x in AVenhance.unitCube,
      inner ℝ (A x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (plainHigherSynthesisCLM N K c) x))
        (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) x)) =
    ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      inner ℝ (A x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
        (coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 1 (fun _ => k) x) := by
  apply integral_congr_ae
  filter_upwards [plainHigherTensor_readout_ae N K i' (d.1 - 1)
    (admissibleOrders_high_readout_bound K D i i' d) c, plainProjectedTest_gradient_ae N φ i]
    with x hc hφ
  rw [hc, hφ, PiLp.inner_apply]

/-- The literal finite drift row equals the fixed first-jet and value-test pairing. -/
theorem plainDrift_test_integral (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (φ : ∀ i, TorusHk 1 (h i))
    (i : ι) (k : Fin 2) (v : Vec 2 → Vec 2) :
    (∫ x in AVenhance.unitCube, v x k *
      inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
        fun _ => k⟩ (plainHigherSynthesisCLM N K c) x) (torusHkValueCLM (galerkinProj N (φ i)) x)) =
    ∫ x in AVenhance.unitCube, v x k *
      inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
        (coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 0 Fin.elim0 x) := by
  apply integral_congr_ae
  filter_upwards [coupledPlainSynthesis_jet_ae N i (K i + 1) c
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩,
    plainProjectedTest_value_ae N φ i] with x hc hφ
  change v x k * inner ℝ ((coupledPlainSynthesis N i (K i + 1) c).val _ x) _ = _
  rw [hc, hφ]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual combined diffusion and coupling flux of a finite field. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)

/-- Diffusion and all admissible couplings in the actual weak Sobolev flux carrier. -/
def plainSpatialFlux (i : ι) : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ν • coupledPlainGradientHk N c i (K i) + plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i

/-- The combined carrier reads the literal diffusion and coupling actions almost everywhere. -/
theorem plainSpatialFlux_value_ae (i : ι) :
    (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
      ν • coupledPlainGradientJet N c i 0 Fin.elim0 x +
        ∑ i', ∑ d : admissibleOrders K D i i', A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) := by
  have heq : (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) =
      ν • (coupledPlainGradientHk N c i (K i)).val (valueIndex2 (K i)) +
        (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) := by
    simp [plainSpatialFlux]
  rw [heq]
  filter_upwards [Lp.coeFn_add
    (ν • (coupledPlainGradientHk N c i (K i)).val (valueIndex2 (K i)))
    ((plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i))),
    Lp.coeFn_smul ν ((coupledPlainGradientHk N c i (K i)).val (valueIndex2 (K i))),
    coupledPlainGradientHk_jet_ae N c i (K i) (valueIndex2 (K i)),
    plainCouplingFlux_value_ae N D ρ hρ K a b A hA t ht hC hp c i] with x hx hs hg hc
  rw [hx, Pi.add_apply, hs, Pi.smul_apply, hg, hc]
  rfl

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Discharge the spectral-tail estimate from actual finite source
primitives of a bounded weak trace. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainSourcePrimitive_continuousOn (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (H : ∀ i, ℝ → TorusHk (K i) (h i))
    (hS : ∀ i, MemLp (S i) 2 (volume.restrict (Set.Icc a b)))
    (hH : ∀ i, Integrable (H i) (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (huw : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i,
      u i r = truncateTorusHk (Nat.le_succ (K i)) (w i r))
    (hcont : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b))
    (R : ℝ) (hub : ∀ i, ∀ r ∈ Set.Icc a b, ‖u i r‖ ≤ R)
    (hprim : ∀ L, ∀ t ∈ Set.Icc a b,
      plainInitialCoefficients L K (fun i => u i t) = plainInitialCoefficients L K f +
        ∫ r in a..t, plainSourceCoefficients L K (fun i => S i r) (fun i => H i r))
 :
    ∀ i, ContinuousOn (u i) (Set.Icc a b) := by
  intro i
  let e : ℕ → ℝ := fun N => (Fintype.card (JetIndex2 (K i)) : ℝ) *
    torusSourceTailBudget N a b R (f i) (H i) (S i) (w i)
  have he : Filter.Tendsto e Filter.atTop (𝓝 0) := by
    have hh := (torusSourceTailBudget_tendsto a b R (f i) (H i) (S i) (w i)
      (hH i) (hS i) (hw i)).const_mul (Fintype.card (JetIndex2 (K i)) : ℝ)
    simpa only [mul_zero] using hh
  let q : ℕ → C(Set.Icc a b, TorusHk (K i) (h i)) := fun N =>
    ⟨fun t => galerkinProj N (u i t), continuousOn_iff_continuous_domRestrict.mp
      (plainTrace_galerkinProj_continuousOn N K a b u hcont i)⟩
  have hq : ∀ N M t, ‖q N t - q M t‖ ^ 2 ≤ e N + e M := by
    intro N M t
    have hh := torusBand_sqNorm_le_of_jetBounds N M (u i t)
      (torusSourceTailBudget N a b R (f i) (H i) (S i) (w i) +
        torusSourceTailBudget M a b R (f i) (H i) (S i) (w i))
      (fun j => plainSourcePrimitive_bandJet_tail_bound N M K hab S H hS hH u f w hw huw
        hcont R hub hprim t t.property i j)
    simpa only [q, e, ContinuousMap.coe_mk, mul_add] using! hh
  exact AVRegularity.CoupledEnergy.Variational.continuousOn_of_spectral_tails a b (u i) q e he hq
    (fun t => galerkinProj_tendsto (u i t))

end AVRegularity.CoupledEnergy.Galerkin
end
