-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeTimeReadout
public import AVRegularity.Proofs.Transverse.ClassicalCell.Spatial
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
public import AVRegularity.EntryWeak.IndependentLiftFluxCrossAffine
import AVRegularity.EntryWeak.IndependentCovariantOperations
import AVRegularity.CoupledEnergy.Galerkin.PlainFamilyMeasurableFromRows
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

/-! The periodic divergence in the reserved Sobolev carrier. Its weak pairing gives
an actual Hilbert derivative from a source and a flux, before choosing a spatial test. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Divergence loses one Sobolev order and sums the two physical flux directions. -/
def nativeTorusDivergenceCLM (K : ℕ) :
    TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] TorusHk K E :=
  ∑ k : Fin 2, (derivativeTorusHk (fun _ : Fin 1 => k)).comp
    (mapTorusHkCLM (K + 1) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k))

omit [FiniteDimensional ℝ E] in
/-- The projected weak-test gradient is its first-order weak jet. -/
theorem native_test_gradient_component (φ : TorusHk 1 E) (k : Fin 2) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k).compLpL 2
      (volume.restrict AVenhance.unitCube) (torusH1GradientL2CLM (E := E) φ) =
      φ.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (torusH1GradientL2CLM (E := E) φ),
    torusH1GradientL2CLM_ae φ] with x hx hφ
  rw [hx, hφ]
  rfl

/-- Divergence and the weak-test gradient are exact negatives of one another. -/
theorem native_torus_divergence_pairing {K : ℕ}
    (F : TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => E))) (φ : TorusHk 1 E) :
    inner ℝ (torusHkValueCLM (nativeTorusDivergenceCLM K F)) (torusHkValueCLM φ) =
      -inner ℝ (torusHkValueCLM F) (torusH1GradientL2CLM (E := E) φ) := by
  simp only [nativeTorusDivergenceCLM, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, sum_inner, mapTorusHkCLM_apply]
  rw [tensorL2_inner_eq_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change inner ℝ ((derivativeTorusHk (fun _ : Fin 1 => k)
    (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) F)).val (valueIndex2 K)) _ = _
  rw [derivativeTorusHk_value_slot, native_torus_partial_pairing,
    native_test_gradient_component]
  congr 2
  exact mapTorusHk_jet_eq_compLp _ F (valueIndex2 (K + 1))

/-- An integrable source and one reserved flux give a derivative independent of all tests. -/
theorem native_torus_strong_time_of_source_flux {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (U S : ℝ → TorusHk K E)
    (F : ℝ → TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : IntervalIntegrable S volume a b) (hF : IntervalIntegrable F volume a b)
    (hweak : ∀ t ∈ Icc a b, ∀ φ : TorusHk 1 E,
      inner ℝ (torusHkValueCLM (U t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (U a)) (torusHkValueCLM φ) =
        ∫ s in a..t, inner ℝ (torusHkValueCLM (S s)) (torusHkValueCLM φ) -
          inner ℝ (torusHkValueCLM (F s)) (torusH1GradientL2CLM (E := E) φ)) :
    CycleEvolution.StrongTimeRegularity a b U
      (fun t => S t + nativeTorusDivergenceCLM K (F t)) := by
  have hdiv : IntervalIntegrable (fun t => nativeTorusDivergenceCLM K (F t)) volume a b :=
    ⟨(nativeTorusDivergenceCLM (E := E) K).integrable_comp hF.1,
      (nativeTorusDivergenceCLM (E := E) K).integrable_comp hF.2⟩
  apply native_torus_strong_time_of_value_pairings hab U _ (hS.add hdiv)
  intro t ht φ
  rw [hweak t ht φ]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [map_add, inner_add_left, native_torus_divergence_pairing, sub_eq_add_neg]

/-- The native gradient of a restricted carrier has exactly the original
classical weak gradient representatives at value order. -/
theorem native_torus_gradient_value_ae {K L : ℕ} (hKL : K + 1 ≤ L) (w : TorusHk L E) :
    torusHkValueCLM (torusGradientTensorCLM K (truncateTorusHk hKL w)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => WithLp.toLp 2
        (fun k : Fin 2 => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) := by
  have hg := torusFamilyTensor_value_ae
    (fun k : Fin 2 => derivativeTorusHk (K := K) (fun _ : Fin 1 => k)
      (truncateTorusHk hKL w))
  simp only [derivativeTorusHk_value_slot] at hg
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      (truncateTorusHk hKL w).val ⟨⟨1, by omega⟩, fun _ => k⟩ x =
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun _ => (torusRawJet_ae w _).symm)
  simp only [torusGradientTensorCLM_apply, torusGradientTensor]
  filter_upwards [hg, hj] with x hx hjx
  exact hx.trans (PiLp.ext hjx)

omit [FiniteDimensional ℝ E] in
/-- Adding a restricted carrier and a scaled carrier preserves their literal
value representatives. The coefficient space is kept abstract. -/
theorem native_torus_value_smul_add_ae {K L : ℕ} (hKL : K ≤ L) (c : ℝ)
    (R : TorusHk K E) (Q : TorusHk L E) (f g : Vec 2 → E)
    (hR : torusHkValueCLM R =ᵐ[volume.restrict AVenhance.unitCube] f)
    (hQ : torusHkValueCLM Q =ᵐ[volume.restrict AVenhance.unitCube] g) :
    torusHkValueCLM (c • R + truncateTorusHk hKL Q) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => c • f x + g x := by
  have ht : torusHkValueCLM (truncateTorusHk hKL Q) = torusHkValueCLM Q := rfl
  rw [map_add, map_smul, ht]
  filter_upwards [Lp.coeFn_add (c • torusHkValueCLM R) (torusHkValueCLM Q),
    Lp.coeFn_smul c (torusHkValueCLM R), hR, hQ] with x ha hs hr hq
  rw [ha]
  change (c • torusHkValueCLM R) x + torusHkValueCLM Q x = _
  rw [hs]
  change c • torusHkValueCLM R x + torusHkValueCLM Q x = _
  rw [hr, hq]

/-- Convert the literal homogeneous PDE integrand to its actual source and total
flux pairing. Only spatial almost-everywhere identities are used. -/
theorem native_raw_rhs_pairing {K : ℕ} (ν : ℝ) (v : Vec 2 → Vec 2)
    (du : Fin 2 → Vec 2 → E) (q : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (S : TorusHk K E) (B : TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : torusHkValueCLM S =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -(∑ k : Fin 2, v x k • du k x))
    (hB : torusHkValueCLM B =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ν • WithLp.toLp 2 (fun k => du k x) + q x) (φ : TorusHk 1 E) :
    (∫ x in AVenhance.unitCube,
      -(∑ k : Fin 2, v x k * inner ℝ (du k x) (φ.toFunction.jet (valueIndex2 1) x)) -
        ν * ∑ k : Fin 2, inner ℝ (du k x)
          (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) -
        ∑ k : Fin 2, inner ℝ (q x k)
          (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
      inner ℝ (torusHkValueCLM S) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM B) (torusH1GradientL2CLM (E := E) φ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_sub
    (L2.integrable_inner (𝕜 := ℝ) (torusHkValueCLM S) (torusHkValueCLM φ))
    (L2.integrable_inner (𝕜 := ℝ) (torusHkValueCLM B) (torusH1GradientL2CLM (E := E) φ))]
  apply integral_congr_ae
  filter_upwards [hS, hB, torusRawValue_ae φ, torusRawTestGradient_ae φ] with x hs hb hφ hg
  rw [hs, hb, ← hg]
  rw [← hφ]
  simp only [inner_neg_left, sum_inner, real_inner_smul_left, inner_add_left,
    PiLp.inner_apply, PiLp.smul_apply, ← Finset.mul_sum]
  ring

/-- The raw weak identity `CoupledWeakIdentity` determines a common reserved Sobolev derivative,
provided its actual source and total flux have been placed in the native carriers. -/
theorem native_torus_strong_time_of_raw_weak {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (U S : ℝ → TorusHk K E)
    (B : ℝ → TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => E)))
    (du : ℝ → Fin 2 → Vec 2 → E)
    (q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hS : IntervalIntegrable S volume a b) (hB : IntervalIntegrable B volume a b)
    (hSv : ∀ t ∈ Icc a b, torusHkValueCLM (S t) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -(∑ k : Fin 2, v t x k • du t k x))
    (hBv : ∀ t ∈ Icc a b, torusHkValueCLM (B t) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ν • WithLp.toLp 2 (fun k => du t k x) + q t x)
    (hweak : ∀ t ∈ Icc a b, ∀ φ : TorusHk 1 E,
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
        ((U t).toFunction.jet (valueIndex2 K)) ((U a).toFunction.jet (valueIndex2 K))
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
        du q (fun _ _ => 0) (fun _ _ => 0)) :
    CycleEvolution.StrongTimeRegularity a b U
      (fun t => S t + nativeTorusDivergenceCLM K (B t)) := by
  apply native_torus_strong_time_of_source_flux hab U S B hS hB
  intro t ht φ
  have hw := (hweak t ht φ).2.2.2.2
  have hleft := (torusRawValue_pairing_integrable_and_integral (U t) φ).2
  have hinit := (torusRawValue_pairing_integrable_and_integral (U a) φ).2
  rw [hleft, hinit] at hw
  rw [hw, intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hri : r ∈ Icc a b := ⟨hr.1.le, hr.2.trans ht.2⟩
  have he := native_raw_rhs_pairing ν (v r) (du r) (q r) (S r) (B r)
    (hSv r hri) (hBv r hri) φ
  simpa only [PiLp.zero_apply, add_zero, inner_zero_left, add_zero] using he

/-- A classical scalar inverse satisfies its strong spatial right-hand side
paired against every native H¹ test. This uses the public cell equation directly,
with no fixed normalized metric bound. -/
theorem native_scalar_cell_inverse_test_increment
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    {sZ : ℕ} (hsZ : 2 ≤ sZ) {a b : ℝ} (hab : a ≤ b)
    (g c : ℝ → Vec 2 → ℝ) (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hv : ∀ t ∈ Icc a b, Continuous (v t))
    (hg : ∀ t ∈ Icc a b, Continuous (g t))
    (t : ℝ) (ht : t ∈ Icc a b) (ψ : TorusHkFunction 1 ℂ) :
    let R := fun r => ∫ x in AVenhance.unitCube,
      (Providers.Transverse.strongRhs (G r) (v r) (g r) (c r) x : ℂ) *
        ψ.jet (valueIndex2 1) x
    IntegrableOn R (Ioc a t) ∧
      (∫ x in AVenhance.unitCube, (c t x : ℂ) * ψ.jet (valueIndex2 1) x) -
        (∫ x in AVenhance.unitCube, (c a x : ℂ) * ψ.jet (valueIndex2 1) x) =
          ∫ r in Ioc a t, R r := by
  have hs := (hc.2 (ContinuousLinearMap.id ℝ ℝ)).1
  have hw := hs.2.2.2.2.2.2 a ⟨le_rfl, hab⟩ t ht ht.1 ψ
  unfold CellWeakIdentity at hw
  simp only [cellValue, cellJetOfField, valueIndex2, valueIndex, cellGradComp,
    ContinuousLinearMap.id_apply, WithLp.ofLp_zero, Pi.zero_apply,
    mul_zero, zero_mul, add_zero, sub_zero, Finset.sum_const_zero] at hw
  have hk (r : ℝ) (hr : r ∈ Ioc a t) :
      (∫ x in AVenhance.unitCube,
        Providers.Transverse.weakRhsSimple (G r) (v r) (g r) (c r) ψ x) =
      ∫ x in AVenhance.unitCube,
        (Providers.Transverse.strongRhs (G r) (v r) (g r) (c r) x : ℂ) *
          ψ.jet (valueIndex2 1) x := by
    have hrb : r ∈ Icc a b := ⟨hr.1.le, hr.2.trans ht.2⟩
    have hcr : ContDiff ℝ 2 (c r) := (hc.1 r hrb).of_le
      (WithTop.coe_le_coe.mpr (by exact_mod_cast hsZ))
    have hpc : AVenhance.IsZ2Periodic (c r) := by
      intro n x
      have hh := (hs.2.2.1 r hrb).2 n x
      exact Complex.ofReal_injective hh
    exact (Providers.Transverse.weakRhsSimple_integrable_and_integral
      (hv r hrb) (hg r hrb) hcr hpc ψ).2
  have hint := hw.2.2.2.1
  change IntegrableOn (fun r => ∫ x in AVenhance.unitCube,
      Providers.Transverse.weakRhsSimple (G r) (v r) (g r) (c r) ψ x) (Ioc a t) at hint
  dsimp only
  have he := setIntegral_congr_fun (μ := volume) measurableSet_Ioc hk
  refine ⟨hint.congr_fun hk measurableSet_Ioc, ?_⟩
  rw [← he]
  exact hw.2.2.2.2

/-- Smooth-test separation upgrades the literal scalar cell equation to a
pointwise time primitive. The budgets concern its actual classical right-hand
side, so arbitrary native ellipticity bounds are allowed. -/
theorem native_scalar_cell_inverse_pointwise_primitive
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    {sZ : ℕ} (hsZ : 2 ≤ sZ) {a b : ℝ} (hab : a ≤ b)
    (g c : ℝ → Vec 2 → ℝ) (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hv : ∀ t ∈ Icc a b, Continuous (v t))
    (hg : ∀ t ∈ Icc a b, Continuous (g t))
    (hR : ∀ t ∈ Icc a b,
      Continuous (Providers.Transverse.strongRhs (G t) (v t) (g t) (c t)))
    (hpR : ∀ t ∈ Icc a b,
      AVenhance.IsZ2Periodic (Providers.Transverse.strongRhs (G t) (v t) (g t) (c t)))
    (hmR : Measurable (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} =>
      Providers.Transverse.strongRhs (G Z.1.1) (v Z.1.1) (g Z.1.1) (c Z.1.1) Z.1.2))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x,
      ‖Providers.Transverse.strongRhs (G t) (v t) (g t) (c t) x‖ ≤ B t) :
    ∀ t ∈ Icc a b, ∀ x, c t x - c a x =
      ∫ r in Ioc a t, Providers.Transverse.strongRhs (G r) (v r) (g r) (c r) x := by
  let R := fun t => Providers.Transverse.strongRhs (G t) (v t) (g t) (c t)
  have hpc (t : ℝ) (ht : t ∈ Icc a b) : AVenhance.IsZ2Periodic (c t) := by
    intro n x
    have hh := ((hc.2 (ContinuousLinearMap.id ℝ ℝ)).1.2.2.1 t ht).2 n x
    exact Complex.ofReal_injective hh
  apply native_pointwise_primitive_of_cell_tests hab c R
    (fun t ht => (hc.1 t ht).continuous) hpc hR hpR hmR B hB hb
  intro t ht φ hφ hpφ
  have hφC : ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hpφC : AVenhance.IsZ2Periodic (fun x => (φ x : ℂ)) :=
    fun n x => congrArg Complex.ofReal (hpφ n x)
  obtain ⟨ψ, hψ, _⟩ := Construction.Preservation.Residual.kernel_readout_smooth_test
    (fun x => (φ x : ℂ)) hφC hpφC
  have hpair (f : Vec 2 → ℝ) (hf : Continuous f) :
      (∫ x in AVenhance.unitCube, (f x : ℂ) * ψ.toFunction.jet (valueIndex2 1) x) =
        (cellInner f φ : ℂ) := by
    calc
      _ = ∫ x in AVenhance.unitCube, ((inner ℝ (f x) (φ x) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hψ] with x hx
        rw [hx]
        simp only [Real.inner_apply, Complex.ofReal_mul, mul_comm]
      _ = (cellInner f φ : ℂ) := Complex.ofRealCLM.integral_comp_comm
        (continuous_cell_integrable _ (hf.inner hφ.continuous))
  obtain ⟨hInt, heq⟩ := native_scalar_cell_inverse_test_increment G v hsZ hab g c hc
    hv hg t ht ψ.toFunction
  have hsub : Ioc a t ⊆ Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have he : (fun r => ∫ x in AVenhance.unitCube,
      (R r x : ℂ) * ψ.toFunction.jet (valueIndex2 1) x) =ᵐ[volume.restrict (Ioc a t)]
      fun r => (cellInner (R r) φ : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hpair (R r) (hR r (hsub hr))
  have hRealInt : IntegrableOn (fun r => cellInner (R r) φ) (Ioc a t) := by
    have hh := Complex.reCLM.integrable_comp hInt
    apply hh.congr
    filter_upwards [he] with r hr
    change (∫ x in AVenhance.unitCube,
      (R r x : ℂ) * ψ.toFunction.jet (valueIndex2 1) x).re = cellInner (R r) φ
    rw [hr, Complex.ofReal_re]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub, ← hpair (c t) (hc.1 t ht).continuous,
    ← hpair (c a) (hc.1 a ⟨le_rfl, hab⟩).continuous, heq, integral_congr_ae he]
  exact Complex.ofRealCLM.integral_comp_comm hRealInt

private theorem native_scalar_strong_rhs_eq (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, G i j = G j i) (v : Vec 2 → Vec 2) (g c : Vec 2 → ℝ) (x : Vec 2) :
    Providers.Transverse.strongRhs G v g c x = -cellOperator G v c x + g x := by
  have hd : (∑ j : Fin 2, ∑ k : Fin 2, G j k *
      fderiv ℝ (fun y => fderiv ℝ c y (basisVec j)) x (basisVec k)) =
      ∑ k : Fin 2, ∑ j : Fin 2, G k j *
        fderiv ℝ (fun y => fderiv ℝ c y (basisVec j)) x (basisVec k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [hG j k]
  simp only [Providers.Transverse.strongRhs, cellOperator, smul_eq_mul, hd]
  ring

section NormedCellCarrier
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

/-- Two fast reserves suffice for the literal cell time derivative. The metric
and drift retain their actual entries; no normalized ellipticity is required. -/
def native_cell_rhs_source_reserve (R : ℕ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g c : ℝ → Vec 2 → Vec 2 → V)
    (QG : ∀ i j, EntryWeakProofs.IndependentParameterSourceReserve R
      (fun t (_ : Vec 2) Y => G t Y i j))
    (Qv : ∀ k, EntryWeakProofs.IndependentParameterSourceReserve R
      (fun t z (_ : Vec 2) => v t z k))
    (Qg : EntryWeakProofs.IndependentParameterSourceReserve R g)
    (Qc : EntryWeakProofs.IndependentParameterSourceReserve (R + 2) c) :
    EntryWeakProofs.IndependentParameterSourceReserve R
      (fun t z Y => -cellOperator (G t Y) (v t) (fun y => c t y Y) z + g t z Y) := by
  let Qdiff := EntryWeakProofs.IndependentParameterSourceReserve.fintypeSum R
    (fun i : Fin 2 => fun t z Y => ∑ j : Fin 2,
      G t Y i j • fderiv ℝ (fun y => fderiv ℝ (fun w => c t w Y) y (basisVec j))
        z (basisVec i))
    (fun i => EntryWeakProofs.IndependentParameterSourceReserve.fintypeSum R _
      (fun j : Fin 2 => (QG i j).scalarProduct
        ((Qc.fastPartial (R + 1) (by omega) j).fastPartial R (by omega) i)))
  let Qadv := EntryWeakProofs.IndependentParameterSourceReserve.fintypeSum R
    (fun k : Fin 2 => fun t z Y => v t z k • fderiv ℝ (fun y => c t y Y) z (basisVec k))
    (fun k => (Qv k).scalarProduct (Qc.fastPartial R (by omega) k))
  have Q := (Qdiff.add (Qadv.map (-ContinuousLinearMap.id ℝ V))).add Qg
  refine Q.congrSource ?_
  funext t z Y
  change (∑ i : Fin 2, ∑ j : Fin 2, G t Y i j •
      fderiv ℝ (fun y => fderiv ℝ (fun w => c t w Y) y (basisVec j)) z (basisVec i)) +
      -(∑ k : Fin 2, v t z k • fderiv ℝ (fun y => c t y Y) z (basisVec k)) + g t z Y = _
  simp only [cellOperator]
  abel

/-- Dual coordinates give the native pointwise cell primitive in the finite
operator carrier as well as in scalar fibres. All measurability is windowed. -/
theorem native_cell_inverse_pointwise_primitive
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    {sZ : ℕ} (hsZ : 2 ≤ sZ) {a b : ℝ} (hab : a ≤ b)
    (g c : ℝ → Vec 2 → V) (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hG : ∀ t ∈ Icc a b, ∀ i j, G t i j = G t j i)
    (hv : ∀ t ∈ Icc a b, Continuous (v t))
    (hg : ∀ t ∈ Icc a b, Continuous (g t))
    (hR : ∀ t ∈ Icc a b, Continuous (fun x => -cellOperator (G t) (v t) (c t) x + g t x))
    (hpR : ∀ t ∈ Icc a b,
      AVenhance.IsZ2Periodic (fun x => -cellOperator (G t) (v t) (c t) x + g t x))
    (hmR : Measurable (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} =>
      -cellOperator (G Z.1.1) (v Z.1.1) (c Z.1.1) Z.1.2 + g Z.1.1 Z.1.2))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x, ‖-cellOperator (G t) (v t) (c t) x + g t x‖ ≤ B t) :
    ∀ t ∈ Icc a b, ∀ x, c t x - c a x =
      ∫ r in Ioc a t, -cellOperator (G r) (v r) (c r) x + g r x := by
  let R := fun t x => -cellOperator (G t) (v t) (c t) x + g t x
  obtain ⟨dq, hdq, heq⟩ := macroWeakTime_extension a b R hmR
  intro t ht x
  have hsub : Ioc a t ⊆ Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hi : IntegrableOn (fun r => R r x) (Ioc a t) := by
    have hm : AEStronglyMeasurable (fun r => R r x) (volume.restrict (Ioc a t)) := by
      apply ((hdq.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact heq (r, x) (hsub hr)
    apply (hB.mono_set hsub).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hb r (hsub hr) x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro l
  have hcl := CycleComparison.Lift.cellFieldInverse_postcomposition l G v sZ (by omega)
    a b 0 g c hc
  simp only [Pi.zero_apply, map_zero] at hcl
  have hRs (r : ℝ) (hr : r ∈ Icc a b) (z : Vec 2) :
      Providers.Transverse.strongRhs (G r) (v r) (fun y => l (g r y))
        (fun y => l (c r y)) z = l (R r z) := by
    rw [native_scalar_strong_rhs_eq (G r) (hG r hr),
      CycleComparison.Lift.cellOperator_postcomposition l (G r) (v r) (c r)
        ((hc.1 r hr).of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast hsZ))) z]
    simp only [R, map_add, map_neg]
  have hrc (r : ℝ) (hr : r ∈ Icc a b) : Continuous
      (Providers.Transverse.strongRhs (G r) (v r) (fun y => l (g r y))
        (fun y => l (c r y))) :=
    (l.continuous.comp (hR r hr)).congr (fun z => (hRs r hr z).symm)
  have hrp (r : ℝ) (hr : r ∈ Icc a b) : AVenhance.IsZ2Periodic
      (Providers.Transverse.strongRhs (G r) (v r) (fun y => l (g r y))
        (fun y => l (c r y))) := by
    intro n z
    rw [hRs r hr, hRs r hr]
    exact congrArg l (hpR r hr n z)
  have hrm : Measurable (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} =>
      Providers.Transverse.strongRhs (G Z.1.1) (v Z.1.1) (fun y => l (g Z.1.1 y))
        (fun y => l (c Z.1.1 y)) Z.1.2) := by
    have he : (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} =>
        Providers.Transverse.strongRhs (G Z.1.1) (v Z.1.1) (fun y => l (g Z.1.1 y))
          (fun y => l (c Z.1.1 y)) Z.1.2) =
        (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} => l (R Z.1.1 Z.1.2)) :=
      funext fun Z => hRs Z.1.1 Z.2 Z.1.2
    rw [he]
    exact l.continuous.measurable.comp hmR
  have hbound (r : ℝ) (hr : r ∈ Icc a b) (z : Vec 2) :
      ‖Providers.Transverse.strongRhs (G r) (v r) (fun y => l (g r y))
        (fun y => l (c r y)) z‖ ≤ ‖l‖ * B r := by
    rw [hRs r hr z]
    exact (l.le_opNorm (R r z)).trans (mul_le_mul_of_nonneg_left (hb r hr z) (norm_nonneg l))
  have hp := native_scalar_cell_inverse_pointwise_primitive G v hsZ hab _ _ hcl hv
    (fun r hr => l.continuous.comp (hg r hr)) hrc hrp hrm (fun r => ‖l‖ * B r)
    (hB.const_mul ‖l‖) hbound t ht x
  rw [map_sub, ← l.integral_comp_comm hi]
  exact hp.trans (setIntegral_congr_fun (μ := volume) measurableSet_Ioc
    (fun r hr => hRs r (hsub hr) x))

/-- A reserved local model of the literal right-hand side gives its actual cell
time primitive. The model is used only at the chosen slow label on the window. -/
theorem native_cell_inverse_primitive_of_reserved_rhs
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    {sZ : ℕ} (hsZ : 2 ≤ sZ) {a b : ℝ} (hab : a ≤ b)
    (g c : ℝ → Vec 2 → V) (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hG : ∀ t ∈ Icc a b, ∀ i j, G t i j = G t j i)
    (hv : ∀ t ∈ Icc a b, Continuous (v t))
    (hg : ∀ t ∈ Icc a b, Continuous (g t))
    {H : ℕ} (df : ℝ → Vec 2 → Vec 2 → V)
    (Qdf : EntryWeakProofs.IndependentParameterSourceReserve H df) (Y : Vec 2)
    (heq : ∀ t ∈ Icc a b, ∀ z,
      df t z Y = -cellOperator (G t) (v t) (c t) z + g t z) :
    ∀ t ∈ Icc a b, ∀ z, c t z - c a z = ∫ r in Ioc a t, df r z Y := by
  have hcont (t : ℝ) (ht : t ∈ Icc a b) :
      Continuous (fun z => -cellOperator (G t) (v t) (c t) z + g t z) :=
    ((Qdf.regular t).comp (contDiff_id.prodMk (contDiff_const (c := Y)))).continuous.congr
      (fun z => heq t ht z)
  have hper (t : ℝ) (ht : t ∈ Icc a b) :
      AVenhance.IsZ2Periodic (fun z => -cellOperator (G t) (v t) (c t) z + g t z) := by
    intro n z
    exact (heq t ht (z + AVenhance.latticeShift n)).symm.trans
      ((Qdf.periodic t Y n z).trans (heq t ht z))
  have hm : Measurable (fun Z : {Z : ℝ × Vec 2 // Z.1 ∈ Icc a b} =>
      -cellOperator (G Z.1.1) (v Z.1.1) (c Z.1.1) Z.1.2 + g Z.1.1 Z.1.2) := by
    convert (Qdf.measurable Y).comp measurable_subtype_coe using 1
    funext Z
    exact (heq Z.1.1 Z.2 Z.1.2).symm
  have hb (t : ℝ) (ht : t ∈ Icc a b) (z : Vec 2) :
      ‖-cellOperator (G t) (v t) (c t) z + g t z‖ ≤ Qdf.budget 0 := by
    rw [← heq t ht z]
    simpa only [norm_iteratedFDeriv_zero] using
      Qdf.derivative_bound 0 (Nat.zero_le H) t (z, Y)
  have hp := native_cell_inverse_pointwise_primitive G v hsZ hab g c hc hG hv hg
    hcont hper hm (fun _ => Qdf.budget 0)
    (integrableOn_const isCompact_Icc.measure_ne_top) hb
  intro t ht z
  exact (hp t ht z).trans (setIntegral_congr_fun (μ := volume) measurableSet_Ioc
    (fun r hr => (heq r ⟨hr.1.le, hr.2.trans ht.2⟩ z).symm))

end NormedCellCarrier

/-- Local all-order reserves and the literal pointwise time equation of a native
coefficient in any finite carrier. This data are proved once before choosing derivative words. -/
structure NativeLocalTimeData {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] (a b : ℝ) (Ω : Set (Vec 2))
    (f df : ℝ → Vec 2 → Vec 2 → V) : Prop where
  coefficient : ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
    IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
    ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z
  rhs : ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
    IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
    ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = df t z Z
  primitive : ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
    f t z Y - f a z Y = ∫ s in Ioc a t, df s z Y

/-- Local independent reserve models give continuity, window measurability and
uniform bounds on compact sets of admissible slow labels. -/
theorem native_local_reserve_window_data
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {Ω : Set (Vec 2)} (f : ℝ → Vec 2 → Vec 2 → V)
    (hmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve 0 g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z) :
    (∀ t ∈ Icc a b, Continuous (fun X : Ω × Vec 2 => f t X.2 X.1.1)) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : ℝ × Vec 2 =>
      if Z.1 ∈ Icc a b then f Z.1 Z.2 Y else 0)) ∧
    (∀ K : Set (Vec 2), IsCompact K → K ⊆ Ω → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ K, ∀ z, ‖f t z Y‖ ≤ B) := by
  classical
  choose U g hU hYU hQ heq using fun Y : Ω => hmodel Y Y.2
  let Q (Y : Ω) := Classical.choice (hQ Y)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    apply continuous_iff_continuousAt.mpr
    intro X
    have hc : Continuous (fun Z : Ω × Vec 2 => g X.1 t Z.2 Z.1.1) :=
      ((Q X.1).regular t).continuous.comp
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
    apply hc.continuousAt.congr_of_eventuallyEq
    have hn : ∀ᶠ Z : Ω × Vec 2 in 𝓝 X, Z.1.1 ∈ U X.1 :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.preimage_mem_nhds
        ((hU X.1).mem_nhds (hYU X.1))
    filter_upwards [hn] with Z hZ
    exact (heq X.1 t ht Z.1.1 hZ Z.2).symm
  · intro Y hY
    let Y' : Ω := ⟨Y, hY⟩
    have hm : Measurable (fun Z : ℝ × Vec 2 =>
        if Z.1 ∈ Icc a b then g Y' Z.1 Z.2 Y else (0 : V)) :=
      ((Q Y').measurable Y).ite
        (measurableSet_Icc.preimage measurable_fst) measurable_const
    convert hm using 1
    funext Z
    by_cases ht : Z.1 ∈ Icc a b
    · simp only [ite_eq_left ht]
      exact (heq Y' Z.1 ht Y (hYU Y') Z.2).symm
    · simp only [ite_eq_right ht]
  · intro K hK hKΩ
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (fun Y hY =>
      mem_iUnion.mpr ⟨⟨Y, hKΩ hY⟩, hYU ⟨Y, hKΩ hY⟩⟩)
    refine ⟨∑ Y ∈ s, (Q Y).budget 0,
      Finset.sum_nonneg (fun Y _ => (Q Y).budget_nonneg 0), ?_⟩
    intro t ht Y hY z
    obtain ⟨Z, hZs, hZU⟩ := mem_iUnion₂.mp (hs hY)
    have hb : ‖g Z t z Y‖ ≤ (Q Z).budget 0 := by
      simpa only [norm_iteratedFDeriv_zero] using (Q Z).derivative_bound 0 le_rfl t (z, Y)
    rw [heq Z t ht Y hZU z] at hb
    exact hb.trans (Finset.single_le_sum (fun W _ => (Q W).budget_nonneg 0) hZs)

/-- Local reserve models give the literal joint spatial jets and uniform bounds
on compact slow-label sets. The fast variable remains unrestricted. -/
theorem native_local_reserve_joint_data
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {Ω : Set (Vec 2)} (R : ℕ) (f : ℝ → Vec 2 → Vec 2 → V)
    (hmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z) :
    (∀ t ∈ Icc a b, ContDiffOn ℝ (R : ℕ∞)
      (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (univ ×ˢ Ω)) ∧
    ∀ q ≤ R, ∀ K : Set (Vec 2), IsCompact K → K ⊆ Ω → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ K, ∀ z,
        ‖iteratedFDeriv ℝ q (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (z, Y)‖ ≤ B := by
  classical
  choose U g hU hYU hQ heq using fun Y : Ω => hmodel Y Y.2
  let Q (Y : Ω) := Classical.choice (hQ Y)
  have hlocal (Y : Ω) (t : ℝ) (ht : t ∈ Icc a b) (Z : Vec 2) (hZ : Z ∈ U Y)
      (z : Vec 2) :
      (fun W : Vec 2 × Vec 2 => g Y t W.1 W.2) =ᶠ[𝓝 (z, Z)]
        (fun W => f t W.1 W.2) := by
    have hn : ∀ᶠ W : Vec 2 × Vec 2 in 𝓝 (z, Z), W.2 ∈ U Y :=
      continuous_snd.continuousAt.preimage_mem_nhds ((hU Y).mem_nhds hZ)
    filter_upwards [hn] with W hW
    exact heq Y t ht W.2 hW W.1
  refine ⟨?_, ?_⟩
  · intro t ht Z hZ
    let Y : Ω := ⟨Z.2, hZ.2⟩
    exact (((Q Y).regular t).contDiffAt.congr_of_eventuallyEq
      (hlocal Y t ht Z.2 (hYU Y) Z.1).symm).contDiffWithinAt
  · intro q hq K hK hKΩ
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (fun Y hY =>
      mem_iUnion.mpr ⟨⟨Y, hKΩ hY⟩, hYU ⟨Y, hKΩ hY⟩⟩)
    refine ⟨∑ Y ∈ s, (Q Y).budget q,
      Finset.sum_nonneg (fun Y _ => (Q Y).budget_nonneg q), ?_⟩
    intro t ht Y hY z
    obtain ⟨Z, hZs, hZU⟩ := mem_iUnion₂.mp (hs hY)
    rw [← ((hlocal Z t ht Y hZU z).iteratedFDeriv ℝ q).eq_of_nhds]
    exact ((Q Z).derivative_bound q hq t (z, Y)).trans
      (Finset.single_le_sum (fun W _ => (Q W).budget_nonneg q) hZs)

/-- A scalar coefficient with local native reserves and a finite-past primitive
remains absolutely continuous along every absolutely continuous compact chart
path. The compact chart can be any convex subset of the admissible labels. -/
theorem native_local_reserves_moving_ac
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    (f df : ℝ → Vec 2 → Vec 2 → V)
    (hfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve 1 g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (hdfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve 0 g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = df t z Z)
    (hp : ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
      f t z Y - f a z Y = ∫ s in Ioc a t, df s z Y)
    (K : Set (Vec 2 × Vec 2)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKΩ : Prod.snd '' K ⊆ Ω) (γ : ℝ → K)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (fun t => f t (γ t).1.1 (γ t).1.2) a b := by
  classical
  let nativeCompactChart : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨hfc, hfb⟩ := native_local_reserve_joint_data 1 f hfmodel
  obtain ⟨hdfc, _⟩ := native_local_reserve_joint_data 0 df hdfmodel
  obtain ⟨_, hdm, hdb⟩ := native_local_reserve_window_data df hdfmodel
  have hproj : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  obtain ⟨B, _hB, hb⟩ := hdb _ hproj hKΩ
  obtain ⟨L, hL, hl⟩ := hfb 1 le_rfl _ hproj hKΩ
  have hmem (X : K) : X.1 ∈ univ ×ˢ Ω := ⟨mem_univ _, hKΩ ⟨X.1, X.2, rfl⟩⟩
  have hfs (t : ℝ) (ht : t ∈ Icc a b) : Continuous (fun X : K => f t X.1.1 X.1.2) :=
    (hfc t ht).continuousOn.comp_continuous continuous_subtype_val hmem
  have hds (t : ℝ) (ht : t ∈ Icc a b) : Continuous (fun X : K => df t X.1.1 X.1.2) :=
    (hdfc t ht).continuousOn.comp_continuous continuous_subtype_val hmem
  have hLip (t : ℝ) (ht : t ∈ Icc a b) :
      LipschitzWith (⟨L, hL⟩ : NNReal) (fun X : K => f t X.1.1 X.1.2) := by
    have hdiff : ∀ X ∈ K, DifferentiableAt ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X := by
      intro X hX
      exact ((hfc t ht).contDiffAt ((isOpen_univ.prod hΩ).mem_nhds
        (hmem ⟨X, hX⟩))).differentiableAt (by simp)
    have hbound : ∀ X ∈ K,
        ‖fderiv ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖₊ ≤ (⟨L, hL⟩ : NNReal) := by
      intro X hX
      apply NNReal.coe_le_coe.mp
      change ‖fderiv ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖ ≤ L
      simpa only [norm_iteratedFDeriv_one] using hl t ht X.2 ⟨X, hX, rfl⟩ X.1
    exact (Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hbound hconv).to_restrict
  exact native_window_moving_primitive_ac hab
    (fun t (X : K) => f t X.1.1 X.1.2) (fun t (X : K) => df t X.1.1 X.1.2)
    hfs hds
    (fun X => (hdm X.1.2 (hmem X).2).comp (measurable_id.prodMk measurable_const))
    (fun _ => B) (integrableOn_const isCompact_Icc.measure_ne_top)
    (fun t ht X => hb t ht X.1.2 ⟨X.1, X.2, rfl⟩ X.1.1)
    (fun t ht X => (hp t ht X.1.2 (hmem X).2 X.1.1).trans
      (intervalIntegral.integral_of_le (f := fun s => df s X.1.1 X.1.2)
        (μ := volume) ht.1).symm)
    γ hγ ⟨L, hL⟩ hLip

/-- Fast words commute with the finite-past primitive under local independent
reserves. The models are used only on the closed time window. -/
theorem native_fast_word_time_primitive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (Vec 2)}
    (f df : ℝ → Vec 2 → Vec 2 → V) (q : ℕ) (β : DerivativeWord2 q)
    (hfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve q g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (hdfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve q g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = df t z Z)
    (hp : ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
      f t z Y - f a z Y = ∫ s in Ioc a t, df s z Y) :
    ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
      orderedDerivative β (fun w => f t w Y) z -
        orderedDerivative β (fun w => f a w Y) z =
      ∫ s in Ioc a t, orderedDerivative β (fun w => df s w Y) z := by
  intro t ht Y hY z
  obtain ⟨Uf, c, _hUf, hYf, ⟨Qc⟩, hec⟩ := hfmodel Y hY
  obtain ⟨Ug, g, _hUg, hYg, ⟨Qg⟩, heg⟩ := hdfmodel Y hY
  have hc (r : ℝ) (hr : r ∈ Icc a b) : ContDiff ℝ (q : ℕ∞) (fun w => f r w Y) := by
    rw [← show (fun w => c r w Y) = (fun w => f r w Y) from funext (hec r hr Y hYf)]
    exact Qc.fast_contDiff r Y
  have he : (fun w => f t w Y - f a w Y) = fun w => ∫ r in a..t, g r w Y := by
    funext w
    rw [hp t ht Y hY w, intervalIntegral.integral_of_le ht.1]
    exact setIntegral_congr_fun (μ := volume) measurableSet_Ioc
      (fun r hr => (heg r ⟨hr.1.le, hr.2.trans ht.2⟩ Y hYg w).symm)
  have hd := congrArg (orderedDerivative β) he
  rw [AVRegularity.orderedDerivative_sub β (hc t ht) (hc a ⟨le_rfl, hab⟩),
    CycleComparison.Lift.orderedDerivative_parameter_intervalIntegral q (fun r w => g r w Y)
      (fun w => (Qg.measurable Y).comp (measurable_id.prodMk measurable_const))
      (fun r => Qg.fast_contDiff r Y) Qg.budget
      (fun j hj r w => Qg.fast_derivative_bound j hj r Y w) a t q le_rfl β] at hd
  exact (congrFun hd z).trans ((intervalIntegral.integral_of_le ht.1).trans
    (setIntegral_congr_fun (μ := volume) measurableSet_Ioc (fun r hr => by
      have he' : (fun w => g r w Y) = fun w => df r w Y :=
        funext (heg r ⟨hr.1.le, hr.2.trans ht.2⟩ Y hYg)
      rw [he'])))

private theorem native_orderedDerivative_germ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ}
    (β : DerivativeWord2 q) {f g : Vec 2 → V} {x : Vec 2}
    (he : f =ᶠ[𝓝 x] g) : orderedDerivative β f =ᶠ[𝓝 x] orderedDerivative β g := by
  induction q generalizing f g with
  | zero => simpa only [AVRegularity.orderedDerivative_zero] using he
  | succ q ih =>
    simp only [AVRegularity.orderedDerivative_succ]
    filter_upwards [(ih (fun i => β i.castSucc) he).fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun T : Vec 2 →L[ℝ] V => T (basisVec (β (Fin.last q)))) hy

/-- Slow words also commute with the finite-past primitive. Their proof is local
in the slow labels; no globally reserved extension of the actual field is assumed. -/
theorem native_slow_word_time_primitive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    (f df : ℝ → Vec 2 → Vec 2 → V) (q : ℕ) (β : DerivativeWord2 q)
    (hfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve q g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f t z Z)
    (hdfmodel : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve q g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = df t z Z)
    (hp : ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
      f t z Y - f a z Y = ∫ s in Ioc a t, df s z Y) :
    ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ z,
      orderedDerivative β (f t z) Y - orderedDerivative β (f a z) Y =
      ∫ s in Ioc a t, orderedDerivative β (df s z) Y := by
  intro t ht Y hY z
  obtain ⟨Uf, c, hUf, hYf, ⟨Qc⟩, hec⟩ := hfmodel Y hY
  obtain ⟨Ug, g, hUg, hYg, ⟨Qg⟩, heg⟩ := hdfmodel Y hY
  have hc (r : ℝ) : ContDiff ℝ (q : ℕ∞) (c r z) :=
    (Qc.regular r).comp (contDiff_const.prodMk contDiff_id)
  have hecf (r : ℝ) (hr : r ∈ Icc a b) : c r z =ᶠ[𝓝 Y] f r z := by
    filter_upwards [hUf.mem_nhds hYf] with Z hZ
    exact hec r hr Z hZ z
  have hegdf (r : ℝ) (hr : r ∈ Icc a b) : g r z =ᶠ[𝓝 Y] df r z := by
    filter_upwards [hUg.mem_nhds hYg] with Z hZ
    exact heg r hr Z hZ z
  have he : (fun Z => c t z Z - c a z Z) =ᶠ[𝓝 Y]
      (fun Z => ∫ r in a..t, g r z Z) := by
    filter_upwards [hΩ.mem_nhds hY, hUf.mem_nhds hYf, hUg.mem_nhds hYg] with Z hZO hZf hZg
    rw [hec t ht Z hZf z, hec a ⟨le_rfl, hab⟩ Z hZf z,
      hp t ht Z hZO z, intervalIntegral.integral_of_le ht.1]
    exact setIntegral_congr_fun (μ := volume) measurableSet_Ioc
      (fun r hr => (heg r ⟨hr.1.le, hr.2.trans ht.2⟩ Z hZg z).symm)
  have hd := (native_orderedDerivative_germ β he).eq_of_nhds
  rw [AVRegularity.orderedDerivative_sub β (hc t) (hc a),
    CycleComparison.Lift.orderedDerivative_parameter_intervalIntegral q (fun r Z => g r z Z)
      (fun Z => (Qg.measurable Z).comp (measurable_id.prodMk measurable_const))
      (fun r => (Qg.regular r).comp (contDiff_const.prodMk contDiff_id)) Qg.budget
      (fun j hj r Z => Qg.parameter_derivative_bound j hj r z Z) a t q le_rfl β] at hd
  dsimp only at hd
  rw [(native_orderedDerivative_germ β (hecf t ht)).eq_of_nhds,
    (native_orderedDerivative_germ β (hecf a ⟨le_rfl, hab⟩)).eq_of_nhds] at hd
  exact hd.trans ((intervalIntegral.integral_of_le ht.1).trans
    (setIntegral_congr_fun (μ := volume) measurableSet_Ioc (fun r hr =>
      (native_orderedDerivative_germ β (hegdf r ⟨hr.1.le, hr.2.trans ht.2⟩)).eq_of_nhds)))

/-- A slow word consumes its order from the same local joint reserve. -/
theorem native_slow_word_local_reserve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {Ω : Set (Vec 2)} (q R : ℕ) (β : DerivativeWord2 q)
    (F : ℝ → Vec 2 → Vec 2 → V)
    (hF : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve (q + R) g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = F t z Z) :
    ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z,
        g t z Z = orderedDerivative β (F t z) Z := by
  intro Y hY
  obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := hF Y hY
  let w : Fin q → Vec 2 := fun i => basisVec (β (Fin.rev i))
  have he : (fun t z Z => EntryWeakProofs.realWordJet (g t z) q w Z) =
      (fun t z Z => orderedDerivative β (g t z) Z) := by
    funext t z Z
    exact (congrFun (AVRegularity.orderedDerivative_eq_iteratedFDeriv β
      (((Qg.regular t).comp (contDiff_const.prodMk contDiff_id)).of_le
        (by exact_mod_cast (Nat.le_add_right q R)))) Z).symm
  let Qw := (Qg.wordJet q R le_rfl w
    (fun i => by simp only [w, basisVec, Pi.norm_single, norm_one]; exact le_rfl)).congrSource he
  refine ⟨U, _, hU, hYU, ⟨Qw⟩, ?_⟩
  intro t ht Z hZ z
  apply (native_orderedDerivative_germ β ?_).eq_of_nhds
  filter_upwards [hU.mem_nhds hZ] with X hX
  exact heq t ht X hX z

/-- A fast word consumes only its own order from a local joint reserve. -/
theorem native_fast_word_local_reserve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {Ω : Set (Vec 2)} (q R : ℕ) (β : DerivativeWord2 q)
    (F : ℝ → Vec 2 → Vec 2 → V)
    (hF : ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve (q + R) g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = F t z Z) :
    ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z,
        g t z Z = orderedDerivative β (fun w => F t w Z) z := by
  intro Y hY
  obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := hF Y hY
  let w : Fin q → Vec 2 := fun i => basisVec (β (Fin.rev i))
  have he : EntryWeakProofs.independentSourceFastWord g q w =
      fun t z Z => orderedDerivative β (fun y => g t y Z) z := by
    funext t z Z
    exact (congrFun (AVRegularity.orderedDerivative_eq_iteratedFDeriv β
      ((Qg.fast_contDiff t Z).of_le (by exact_mod_cast (Nat.le_add_right q R)))) z).symm
  let Qw := (Qg.fastWordReserve q R le_rfl w
    (fun i => by simp only [w, basisVec, Pi.norm_single, norm_one]; exact le_rfl)).congrSource he
  refine ⟨U, _, hU, hYU, ⟨Qw⟩, ?_⟩
  intro t ht Z hZ z
  exact congrFun (congrArg (orderedDerivative β) (funext (heq t ht Z hZ))) z

/-- All mixed words retain the same local time equation and unlimited finite
reserves; the array and its derivative are never reselected by a test. -/
theorem NativeLocalTimeData.mixed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    {f df : ℝ → Vec 2 → Vec 2 → V} (Q : NativeLocalTimeData a b Ω f df)
    (q : ℕ) (β : DerivativeWord2 q) (r : ℕ) (σ : DerivativeWord2 r) :
    NativeLocalTimeData a b Ω
      (fun t z Y => orderedDerivative σ (fun Z => orderedDerivative β (fun w => f t w Z) z) Y)
      (fun t z Y => orderedDerivative σ (fun Z => orderedDerivative β (fun w => df t w Z) z) Y) := by
  let fc := fun t z Y => orderedDerivative β (fun w => f t w Y) z
  let dfc := fun t z Y => orderedDerivative β (fun w => df t w Y) z
  have hfR (R : ℕ) := native_fast_word_local_reserve q R β f (Q.coefficient (q + R))
  have hdR (R : ℕ) := native_fast_word_local_reserve q R β df (Q.rhs (q + R))
  refine ⟨fun R => native_slow_word_local_reserve r R σ fc (hfR (r + R)),
    fun R => native_slow_word_local_reserve r R σ dfc (hdR (r + R)), ?_⟩
  exact native_slow_word_time_primitive hab hΩ fc dfc r σ (hfR r) (hdR r)
    (native_fast_word_time_primitive hab f df q β (Q.coefficient q) (Q.rhs q) Q.primitive)

/-- The native local time data give a derivative in the compact-chart norm,
with one exceptional set before any moving-label or spatial-point evaluation. -/
theorem NativeLocalTimeData.compact
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {Ω : Set (Vec 2)}
    {f df : ℝ → Vec 2 → Vec 2 → V} (Q : NativeLocalTimeData a b Ω f df)
    (K : Set (Vec 2 × Vec 2)) (hK : IsCompact K) (hKΩ : Prod.snd '' K ⊆ Ω) :
    let _nativeCompactTimeChart : CompactSpace K := isCompact_iff_compactSpace.mp hK
    ∃ U dU : ℝ → C(K, V),
      (∀ t ∈ Icc a b, ∀ X : K, U t X = f t X.1.1 X.1.2) ∧
      (∀ t ∈ Icc a b, ∀ X : K, dU t X = df t X.1.1 X.1.2) ∧
      AbsolutelyContinuousOnInterval U a b ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt U (dU t) t := by
  classical
  let nativeCompactTimeChart : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨hfc, _⟩ := native_local_reserve_joint_data 0 f (Q.coefficient 0)
  obtain ⟨hdfc, _⟩ := native_local_reserve_joint_data 0 df (Q.rhs 0)
  obtain ⟨_, hdm, hdb⟩ := native_local_reserve_window_data df (Q.rhs 0)
  have hproj : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  obtain ⟨B, _hB, hb⟩ := hdb _ hproj hKΩ
  have hmem (X : K) : X.1 ∈ univ ×ˢ Ω := ⟨mem_univ _, hKΩ ⟨X.1, X.2, rfl⟩⟩
  exact native_window_compact_primitive_data hab
    (fun t (X : K) => f t X.1.1 X.1.2) (fun t (X : K) => df t X.1.1 X.1.2)
    (fun t ht => (hfc t ht).continuousOn.comp_continuous continuous_subtype_val hmem)
    (fun t ht => (hdfc t ht).continuousOn.comp_continuous continuous_subtype_val hmem)
    (fun X => (hdm X.1.2 (hmem X).2).comp (measurable_id.prodMk measurable_const))
    (fun _ => B) (integrableOn_const isCompact_Icc.measure_ne_top)
    (fun t ht X => hb t ht X.1.2 ⟨X.1, X.2, rfl⟩ X.1.1)
    (fun t ht X => (Q.primitive t ht X.1.2 (hmem X).2 X.1.1).trans
      (intervalIntegral.integral_of_le (f := fun s => df s X.1.1 X.1.2) (μ := volume) ht.1).symm)

/-- The literal RHS of local time data is integrable at every admissible label,
including all endpoints of the original window. -/
theorem NativeLocalTimeData.rhs_integrableOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {Ω : Set (Vec 2)} {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b Ω f df) (Y : Vec 2) (hY : Y ∈ Ω) (z : Vec 2) :
    IntegrableOn (fun t => df t z Y) (Icc a b) := by
  obtain ⟨U, g, _hU, hYU, ⟨Qg⟩, heq⟩ := Q.rhs 0 Y hY
  have hm : StronglyMeasurable (fun t => g t z Y) :=
    ((Qg.measurable Y).comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  have hi : IntegrableOn (fun t => g t z Y) (Icc a b) := by
    apply (integrableOn_const (C := Qg.budget 0) isCompact_Icc.measure_ne_top).mono'
      hm.aestronglyMeasurable
    exact ae_of_all _ fun t => by
      simpa only [norm_iteratedFDeriv_zero] using Qg.derivative_bound 0 le_rfl t (z, Y)
  exact hi.congr_fun (fun t ht => heq t ht Y hYU z) measurableSet_Icc

/-- Fixed linear maps preserve the literal local time equation and its reserves. -/
theorem NativeLocalTimeData.map
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] [CompleteSpace W]
    {a b : ℝ} {Ω : Set (Vec 2)} {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b Ω f df) (L : V →L[ℝ] W) :
    NativeLocalTimeData a b Ω (fun t z Y => L (f t z Y)) (fun t z Y => L (df t z Y)) := by
  have hmodels (F : ℝ → Vec 2 → Vec 2 → V)
      (hF : ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
        IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
        ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = F t z Z) :
      ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → W),
        IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
        ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = L (F t z Z) := by
    intro R Y hY
    obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := hF R Y hY
    exact ⟨U, _, hU, hYU, ⟨Qg.map L⟩, fun t ht Z hZ z => congrArg L (heq t ht Z hZ z)⟩
  refine ⟨hmodels f Q.coefficient, hmodels df Q.rhs, ?_⟩
  intro t ht Y hY z
  rw [← map_sub, Q.primitive t ht Y hY z]
  have hsub : Ioc a t ⊆ Icc a b := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  exact (L.integral_comp_comm ((Q.rhs_integrableOn Y hY z).mono_set hsub)).symm

/-- Genuine local coefficient reserves share one neighborhood under a finite sum. -/
theorem native_local_reserve_fintype_sum
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [Fintype ι]
    {a b : ℝ} {Ω : Set (Vec 2)} (R : ℕ) (f : ι → ℝ → Vec 2 → Vec 2 → V)
    (hF : ∀ i, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = f i t z Z) :
    ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (g : ℝ → Vec 2 → Vec 2 → V),
      IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R g) ∧
      ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, g t z Z = ∑ i, f i t z Z := by
  classical
  intro Y hY
  choose U g hU hYU hQg heq using fun i => hF i Y hY
  let Qg (i : ι) := Classical.choice (hQg i)
  refine ⟨⋂ i, U i, _, isOpen_iInter_of_finite hU, mem_iInter.mpr hYU,
    ⟨EntryWeakProofs.IndependentParameterSourceReserve.fintypeSum R g Qg⟩, ?_⟩
  intro t ht Z hZ z
  exact Finset.sum_congr rfl (fun i _ => heq i t ht Z (mem_iInter.mp hZ i) z)

/-- Finite native path sums preserve the same time data before any spatial jet
or test is chosen. No exceptional sets are selected at individual labels. -/
theorem NativeLocalTimeData.sum
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [Fintype ι]
    {a b : ℝ} {Ω : Set (Vec 2)} {f df : ι → ℝ → Vec 2 → Vec 2 → V}
    (Q : ∀ i, NativeLocalTimeData a b Ω (f i) (df i)) :
    NativeLocalTimeData a b Ω (fun t z Y => ∑ i, f i t z Y)
      (fun t z Y => ∑ i, df i t z Y) := by
  classical
  refine ⟨fun R => native_local_reserve_fintype_sum R f (fun i => (Q i).coefficient R),
    fun R => native_local_reserve_fintype_sum R df (fun i => (Q i).rhs R), ?_⟩
  intro t ht Y hY z
  rw [← Finset.sum_sub_distrib]
  simp_rw [(Q _).primitive t ht Y hY z]
  exact (integral_finsetSum _ (fun i _ => ((Q i).rhs_integrableOn Y hY z).mono_set
    (fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩))).symm

/-- Window equality of literal fields transports local time data without
assuming anything about the two extensions outside that window. -/
theorem NativeLocalTimeData.congr_window
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {a b : ℝ} {Ω : Set (Vec 2)} {f df g dg : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b Ω f df)
    (he : ∀ t ∈ Icc a b, ∀ z Y, f t z Y = g t z Y)
    (hde : ∀ t ∈ Icc a b, ∀ z Y, df t z Y = dg t z Y) :
    NativeLocalTimeData a b Ω g dg := by
  have hmodels (F G : ℝ → Vec 2 → Vec 2 → V)
      (hFG : ∀ t ∈ Icc a b, ∀ z Y, F t z Y = G t z Y)
      (hF : ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (c : ℝ → Vec 2 → Vec 2 → V),
        IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R c) ∧
        ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, c t z Z = F t z Z) :
      ∀ R, ∀ Y ∈ Ω, ∃ (U : Set (Vec 2)) (c : ℝ → Vec 2 → Vec 2 → V),
        IsOpen U ∧ Y ∈ U ∧ Nonempty (EntryWeakProofs.IndependentParameterSourceReserve R c) ∧
        ∀ t ∈ Icc a b, ∀ Z ∈ U, ∀ z, c t z Z = G t z Z := by
    intro R Y hY
    obtain ⟨U, c, hU, hYU, Qc, hc⟩ := hF R Y hY
    exact ⟨U, c, hU, hYU, Qc, fun t ht Z hZ z => (hc t ht Z hZ z).trans (hFG t ht z Z)⟩
  refine ⟨hmodels f g he Q.coefficient, hmodels df dg hde Q.rhs, ?_⟩
  intro t ht Y hY z
  rw [← he t ht z Y, ← he a ⟨le_rfl, ht.1.trans ht.2⟩ z Y,
    Q.primitive t ht Y hY z]
  exact setIntegral_congr_fun measurableSet_Ioc
    (fun s hs => hde s ⟨hs.1.le, hs.2.trans ht.2⟩ z Y)

/-- A countable compact exhaustion makes the moving-label derivative independent
of the label and of its range. No bounded global chart is required. -/
theorem NativeLocalTimeData.global_moving_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ γ : ℝ → Vec 2 × Vec 2, ∀ w : V,
      ContinuousAt γ t → HasDerivAt (fun s => f t (γ s).1 (γ s).2) w t →
      HasDerivAt (fun s => f s (γ s).1 (γ s).2)
        (df t (γ t).1 (γ t).2 + w) t := by
  obtain ⟨hfc, _⟩ := native_local_reserve_joint_data 0 f (Q.coefficient 0)
  obtain ⟨hdfc, _⟩ := native_local_reserve_joint_data 0 df (Q.rhs 0)
  obtain ⟨_, hm, hb⟩ := native_local_reserve_window_data df (Q.rhs 0)
  have hcont (F : ℝ → Vec 2 → Vec 2 → V)
      (hF : ∀ t ∈ Icc a b, ContDiffOn ℝ (0 : ℕ∞)
        (fun Z : Vec 2 × Vec 2 => F t Z.1 Z.2) (univ ×ˢ univ)) :
      ∀ t ∈ Icc a b, Continuous (fun Z : Vec 2 × Vec 2 => F t Z.1 Z.2) := by
    intro t ht
    simpa only [univ_prod_univ, continuousOn_univ] using (hF t ht).continuousOn
  apply native_window_global_moving_derivative hab
    (fun t (Z : Vec 2 × Vec 2) => f t Z.1 Z.2)
    (fun t (Z : Vec 2 × Vec 2) => df t Z.1 Z.2) (hcont f hfc) (hcont df hdfc)
    (fun Z => (hm Z.2 (mem_univ _)).comp (measurable_id.prodMk measurable_const))
  · intro K hK
    obtain ⟨B, _hB, hbound⟩ := hb (Prod.snd '' K) (hK.image continuous_snd) (subset_univ _)
    exact ⟨fun _ => B, integrableOn_const isCompact_Icc.measure_ne_top,
      fun t ht Z hZ => hbound t ht Z.2 ⟨Z, hZ, rfl⟩ Z.1⟩
  · exact fun t ht Z => Q.primitive t ht Z.2 (mem_univ _) Z.1

/-- The common moving-label rule gives the literal spatial chain term for every
curve, with one exceptional set preceding the curve and its velocity. -/
theorem NativeLocalTimeData.moving_chain_rule
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ γ : ℝ → Vec 2 × Vec 2, ∀ v : Vec 2 × Vec 2,
      HasDerivAt γ v t → HasDerivAt (fun s => f s (γ s).1 (γ s).2)
        (df t (γ t).1 (γ t).2 + fderiv ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (γ t) v) t := by
  have hspace := (native_local_reserve_joint_data 1 f (Q.coefficient 1)).1
  filter_upwards [Q.global_moving_derivative hab, ae_restrict_mem measurableSet_Icc] with t ht hmem
  intro γ v hγ
  have hd : DifferentiableAt ℝ (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (γ t) :=
    ((hspace t hmem).contDiffAt (by simp)).differentiableAt (by simp)
  exact ht γ _ hγ.continuousAt (hd.hasFDerivAt.comp_hasDerivAt t hγ)

/-- The local primitive gives joint continuity in time and space on its closed
window. Only a compact neighborhood of each spatial point is used. -/
theorem NativeLocalTimeData.continuous_window
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} (hab : a ≤ b) {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) :
    Continuous (fun p : Icc a b × (Vec 2 × Vec 2) => f p.1 p.2.1 p.2.2) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  let K := Metric.closedBall (0 : Vec 2 × Vec 2) (‖p.2‖ + 1)
  have hK : IsCompact K := isCompact_closedBall _ _
  let nativeContinuousTimeChart : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hp : p.2 ∈ K := mem_closedBall_zero_iff.mpr (le_add_of_nonneg_right zero_le_one)
  let δ : (Vec 2 × Vec 2) → K := fun X =>
    ⟨if hX : X ∈ K then X else p.2, by split_ifs with hX; exact hX; exact hp⟩
  have he : (fun X => (δ X).1) =ᶠ[𝓝 p.2] id := by
    have hn : K ∈ 𝓝 p.2 := Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (lt_add_one ‖p.2‖)))
      Metric.ball_subset_closedBall
    filter_upwards [hn] with X hX
    exact dite_eq_left hX
  have hδ : ContinuousAt δ p.2 := (continuousAt_id.congr_of_eventuallyEq he).codRestrict _
  obtain ⟨U, _dU, hUeq, _hdUeq, hAC, _hd⟩ := Q.compact hab K hK (subset_univ _)
  have hU : Continuous (fun t : Icc a b => U t) :=
    continuousOn_iff_continuous_domRestrict.mp (by
      simpa only [uIcc_of_le hab] using hAC.continuousOn)
  have hj : ContinuousAt (fun q : Icc a b × (Vec 2 × Vec 2) => U q.1 (δ q.2)) p :=
    (hU.comp continuous_fst).continuousAt.eval (hδ.comp continuousAt_snd)
  apply hj.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds he] with q hq
  rw [hUeq q.1 q.1.2 (δ q.2)]
  exact congrArg (fun X : Vec 2 × Vec 2 => f q.1 X.1 X.2) hq.symm

/-- A positive physical clock transports the same local time data and includes
its chain factor in the derivative. Spatial reserves are unchanged. -/
theorem NativeLocalTimeData.time_scale
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b c : ℝ} (hc : 0 < c) {Ω : Set (Vec 2)}
    {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData (c * a) (c * b) Ω f df) :
    NativeLocalTimeData a b Ω (fun t z Y => f (c * t) z Y)
      (fun t z Y => c • df (c * t) z Y) := by
  have hclock : Measurable (fun t : ℝ => c * t) := measurable_const.mul measurable_id
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : c * t ∈ Icc (c * a) (c * b) :=
    ⟨mul_le_mul_of_nonneg_left ht.1 hc.le, mul_le_mul_of_nonneg_left ht.2 hc.le⟩
  refine ⟨?_, ?_, ?_⟩
  · intro R Y hY
    obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := Q.coefficient R Y hY
    exact ⟨U, _, hU, hYU, ⟨Qg.timeReparam _ hclock⟩,
      fun t ht Z hZ z => heq (c * t) (hmem t ht) Z hZ z⟩
  · intro R Y hY
    obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := Q.rhs R Y hY
    let L := c • ContinuousLinearMap.id ℝ V
    exact ⟨U, _, hU, hYU, ⟨(Qg.timeReparam _ hclock).map L⟩,
      fun t ht Z hZ z => congrArg (fun v : V => c • v) (heq (c * t) (hmem t ht) Z hZ z)⟩
  · intro t ht Y hY z
    rw [Q.primitive (c * t) (hmem t ht) Y hY z, integral_smul,
      ← intervalIntegral.integral_of_le ht.1,
      intervalIntegral.smul_integral_comp_mul_left (fun s => df s z Y) c,
      intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left ht.1 hc.le)]

/-- Actual local coefficient data give absolute continuity along any spatial
label curve on the window. Compactness is obtained from the curve itself. -/
theorem NativeLocalTimeData.global_moving_ac
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    {a b : ℝ} {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b univ f df) (hab : a ≤ b)
    (γ : ℝ → Vec 2 × Vec 2) (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (fun t => f t (γ t).1 (γ t).2) a b := by
  classical
  have hgc : ContinuousOn γ (Icc a b) := by
    simpa only [uIcc_of_le hab] using hγ.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let K := Metric.closedBall (0 : Vec 2 × Vec 2) R
  let Γ : ℝ → K := fun s => ⟨γ (projIcc a b hab s),
    mem_closedBall_zero_iff.mpr (hR _ (projIcc a b hab s).2)⟩
  have he (s : ℝ) (hs : s ∈ Icc a b) : (Γ s).1 = γ s := by
    dsimp only [Γ]
    rw [projIcc_of_mem hab hs]
  have hΓ : AbsolutelyContinuousOnInterval Γ a b := by
    have hg' : AbsolutelyContinuousOnInterval (fun s => (Γ s).1) a b :=
      hγ.congr (fun s hs => (he s (by simpa only [uIcc_of_le hab] using hs)).symm)
    simpa only [AbsolutelyContinuousOnInterval, Subtype.dist_eq] using hg'
  have hmove := native_local_reserves_moving_ac hab isOpen_univ f df
    (Q.coefficient 1) (Q.rhs 0) Q.primitive K (isCompact_closedBall _ _)
    (convex_closedBall (0 : Vec 2 × Vec 2) R) (subset_univ _) Γ hΓ
  exact hmove.congr (fun t ht => by
    dsimp only
    rw [he t (by simpa only [uIcc_of_le hab] using ht)])

private def native_reserve_time_indicator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {R : ℕ} {g : ℝ → Vec 2 → Vec 2 → V}
    (Q : EntryWeakProofs.IndependentParameterSourceReserve R g)
    (I : Set ℝ) (hI : MeasurableSet I) :
    EntryWeakProofs.IndependentParameterSourceReserve R
      (fun t z Y => I.indicator (fun s => g s z Y) t) where
  regular t := by
    by_cases ht : t ∈ I
    · simpa only [indicator_of_mem ht] using Q.regular t
    · simpa only [indicator_of_notMem ht] using
        (contDiff_const (c := (0 : V)) : ContDiff ℝ (R : ℕ∞) (fun _ : Vec 2 × Vec 2 => (0 : V)))
  periodic t Y := by
    by_cases ht : t ∈ I
    · simpa only [indicator_of_mem ht] using Q.periodic t Y
    · intro l z
      simp only [indicator_of_notMem ht]
  measurable Y := by
    exact (Q.measurable Y).piecewise (hI.preimage measurable_fst) measurable_const
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn t X := by
    by_cases ht : t ∈ I
    · simpa only [indicator_of_mem ht] using Q.derivative_bound n hn t X
    · simpa only [indicator_of_notMem ht, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        using Q.budget_nonneg n

/-- A coefficient time window extends by constant values at its two endpoints.
The same local spatial models and the windowed RHS give its time data on any
new observation window, without assumptions about the original outside values. -/
theorem NativeLocalTimeData.time_clamp
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
    {a b : ℝ} {Ω : Set (Vec 2)} {f df : ℝ → Vec 2 → Vec 2 → V}
    (Q : NativeLocalTimeData a b Ω f df) (hab : a ≤ b) (a' b' : ℝ) :
    NativeLocalTimeData a' b' Ω
      (fun t z Y => f (projIcc a b hab t) z Y)
      (fun t z Y => (Ioc a b).indicator (fun s => df s z Y) t) := by
  classical
  have hclock : Measurable (fun t : ℝ => (projIcc a b hab t : ℝ)) :=
    continuous_projIcc.subtype_val.measurable
  refine ⟨?_, ?_, ?_⟩
  · intro R Y hY
    obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := Q.coefficient R Y hY
    exact ⟨U, _, hU, hYU, ⟨Qg.timeReparam _ hclock⟩,
      fun t _ Z hZ z => heq _ (projIcc a b hab t).2 Z hZ z⟩
  · intro R Y hY
    obtain ⟨U, g, hU, hYU, ⟨Qg⟩, heq⟩ := Q.rhs R Y hY
    refine ⟨U, _, hU, hYU, ⟨native_reserve_time_indicator Qg (Ioc a b) measurableSet_Ioc⟩,
      fun t _ Z hZ z => ?_⟩
    by_cases ht : t ∈ Ioc a b
    · simp only [indicator_of_mem ht]
      exact heq t (Ioc_subset_Icc_self ht) Z hZ z
    · simp only [indicator_of_notMem ht]
  · intro t ht Y hY z
    have he := native_window_clamp_increment hab (fun r => f r z Y) (fun r => df r z Y)
      (Q.rhs_integrableOn Y hY z) (fun r hr => Q.primitive r hr Y hY z) a' t
    rw [intervalIntegral.integral_of_le ht.1] at he
    exact he

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
