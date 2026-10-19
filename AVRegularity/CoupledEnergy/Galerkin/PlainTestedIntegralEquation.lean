-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
import AVRegularity.CoupledEnergy.Variational.ConstantTimeTest
import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.CoupledEnergy.Galerkin.TorusBandSourceIntegrand
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Native integrable coefficient primitives retain their exact identity
when the RHS is identified almost everywhere with the physical source. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTrace_sourcePrimitive (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (q : (N : ℕ) → ℝ → CoupledPlainCoefficients (h := h) N)
    (S : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (H : ∀ i, ℝ → TorusHk (K i) (h i))
    (hprim : ∀ N, ∀ t ∈ Set.Icc a b, plainInitialCoefficients N K (fun i => u i t) =
      plainInitialCoefficients N K f + ∫ r in a..t, q N r)
    (hq : ∀ N, ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ z,
      q N r z = plainSourceCoefficients N K (fun i => S i r) (fun i => H i r) z) :
    ∀ N, ∀ t ∈ Set.Icc a b, plainInitialCoefficients N K (fun i => u i t) =
      plainInitialCoefficients N K f +
        ∫ r in a..t, plainSourceCoefficients N K (fun i => S i r) (fun i => H i r) := by
  intro N t ht
  rw [hprim N t ht]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : Set.uIoc a t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le ht.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (hq N)] with r hr
  exact funext hr

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Pass native coefficient integrals through weak trial convergence and
strong convergence of projected spatial tests. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Uniformly bounded weak trials and strongly converging spatial tests pass through literal coefficient rows. -/
theorem coefficient_integral_weak_limit_moving_test {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ r, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r x, ‖C r x‖ ≤ M)
    (U : ℕ → Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (V : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (R : ℝ) (hu : ∀ n, ‖U n‖ ≤ R)
    (hw : ∀ ell : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
        (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (z : ℕ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (w : Lp F 2 (volume.restrict AVenhance.unitCube)) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (C r x (U n r x)) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (V r x)) (w x))) := by
  let μ := volume.restrict (Set.Icc a b)
  let B := pullbackInnerCLM
    (constantTimeTestCLM (G := Lp F 2 (volume.restrict AVenhance.unitCube))
      μ (Set.Ioc s t) measurableSet_Ioc (measure_ne_top μ _))
    (coefficientTimeCLM μ C hC hc M hM hb)
  have happly (u : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 μ)
      (q : Lp F 2 (volume.restrict AVenhance.unitCube)) :
      B q u = ∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (u r x)) (q x) := by
    change timeTestIntegralCLM a b s t (fun _ => q) (memLp_const q)
      (coefficientTimeCLM μ C hC hc M hM hb u) = _
    exact coefficientTimeCLM_test_integral hs ht hst C hC hc M hM hb u (fun _ => q) (memLp_const q)
  simpa only [happly] using bilinear_weak_limit_moving_test B U V R hu hw z w hz

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify the literal drift Leibniz terms with the dimension-free mask estimates. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Each coordinate of the actual gradient array is the corresponding final partial. -/
theorem coupledPlainGradientJet_apply (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (j : ℕ) (w : DerivativeWord2 j) (x : Vec 2) (k : Fin 2) :
    coupledPlainGradientJet N c i j w x k =
      coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) x := by
  unfold coupledPlainGradientJet
  change (WithLp.ofLp (∑ l : Fin 2, PiLp.single 2 l
    (coupledPlainRawJet N c i (j + 1) (Fin.snoc w l) x))) k = _
  rw [WithLp.ofLp_sum]
  simp

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The drift product-rule contribution is exactly the term whose mask norm was bounded. -/
theorem plainDrift_multiplicationTerm_eq {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) :
    multiplicationTerm hj (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K) m w x =
      driftMaskTerm hj v (fun a => coupledPlainRawJet N c i a.1.val a.2) m w x := by
  unfold multiplicationTerm driftFiberCoefficient
  rw [orderedCoefficientDerivative_linearMap (scalarRowFiberMap (E := h i))
    (driftCoefficient v) (driftCoefficient_contDiff v hv), scalarRowFiberMap_apply]
  change (∑ k : Fin 2, orderedCoefficientDerivative (driftCoefficient v)
    (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x (PiLp.single 2 k 1) •
    coupledPlainGradientJet N c i (maskRightLength j m) (maskWordEquiv 2 j m w).2 x k) = _
  simp only [coupledPlainGradientJet_apply]
  rfl

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The mask expansion of the actual transport term has genuine ordered weak derivatives. -/
theorem plainDrift_product_hasWeakJet (N : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) (K : ℕ)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) :
    HasOrderedWeakJetOn (K := K) Set.univ
      (multiplicationRawJet (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K)) := by
  apply multiplicationRawJet_hasOrderedWeakJetOn
    ((driftFiberCoefficient_contDiff v hv).of_le (by simp))
    (coupledPlainGradientRawJet_hasWeakJet N c i K)
  intro a e
  exact (continuous_const.inner
    (coupledPlainGradientJet_contDiff N c i a.1.val a.2).continuous).locallyIntegrable

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- At order zero the product-rule jet is literally the transport term in the PDE. -/
theorem plainDrift_product_value (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (v : Vec 2 → Vec 2) (x : Vec 2) :
    multiplicationRawJet (driftFiberCoefficient v) (coupledPlainGradientRawJet N c i K)
      (valueIndex2 K) x =
      ∑ k : Fin 2, v x k • coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x := by
  rw [multiplicationRawJet_value, driftFiberCoefficient_apply]
  apply Finset.sum_congr rfl
  intro k _
  change v x k • coupledPlainGradientJet N c i 0 Fin.elim0 x k = _
  rw [coupledPlainGradientJet_apply]
  rfl

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A drift mask without a velocity derivative is the actual principal transport term. -/
theorem plainDrift_principalMask {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι)
    (v : Vec 2 → Vec 2) (m : PositionMask j) (hm : maskLeftLength j m = 0)
    (w : DerivativeWord2 j) (x : Vec 2) :
    driftMaskTerm hj v (fun a => coupledPlainRawJet N c i a.1.val a.2) m w x =
      ∑ k : Fin 2, v x k • coupledPlainRawJet N c i (j + 1) (Fin.snoc w k) x := by
  change (∑ k : Fin 2, orderedCoefficientDerivative (driftCoefficient v)
    (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x (PiLp.single 2 k 1) •
    coupledPlainRawJet N c i (maskRightLength j m + 1)
      (Fin.snoc (maskWordEquiv 2 j m w).2 k) x) = _
  have hc (r : ℕ) (hr : r = 0) (a : DerivativeWord2 r) :
      orderedCoefficientDerivative (driftCoefficient v) r a = driftCoefficient v := by
    subst r
    rfl
  rw [hc _ hm]
  apply Finset.sum_congr rfl
  intro k _
  have hword := zero_left_mask_word
    (fun r a => coupledPlainRawJet N c i (r + 1) (Fin.snoc a k) x) j m hm w
  rw [hword]
  congr 1
  fin_cases k <;> simp [driftCoefficient]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Pass native coefficient integrals through weak trial convergence and
strong convergence of projected spatial tests. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Uniformly bounded weak trials and strongly converging spatial tests pass through literal coefficient rows. -/
theorem intervalCoefficient_integral_weak_limit_moving_test {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (U : ℕ → Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (V : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (R : ℝ) (hu : ∀ n, ‖U n‖ ≤ R)
    (hw : ∀ ell : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
        (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (z : ℕ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (w : Lp F 2 (volume.restrict AVenhance.unitCube)) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (C r x (U n r x)) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (V r x)) (w x))) := by
  have hab : a ≤ b := hs.1.trans hs.2
  let Cp := fun r x => C (Set.projIcc a b hab r) x
  have hmeas : Measurable (Function.uncurry Cp) := by
    exact hC.comp (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hcont (r : ℝ) : Continuous (Cp r) := hc _ (Set.projIcc a b hab r).property
  have hbound (r : ℝ) (x : Vec 2) : ‖Cp r x‖ ≤ M := hb _ (Set.projIcc a b hab r).property x
  have heq (u : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b))) (q : Lp F 2 (volume.restrict AVenhance.unitCube)) :
      (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (Cp r x (u r x)) (q x)) =
      ∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (u r x)) (q x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with r hr
    have hr' : r ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hst] at hr
      exact ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
    simp only [Cp, Set.projIcc_of_mem hab hr']
  simpa only [heq] using coefficient_integral_weak_limit_moving_test hs ht hst Cp hmeas hcont
    M hM hbound U V R hu hw z w hz

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The initial coefficient vector reconstructs the M1 Sobolev Fourier projection. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A mode has no value in any other component. -/
theorem plainModeCellLp_off_component (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (hi : i ≠ r.1) : plainModeCellLp N r i 0 Fin.elim0 = 0 := by
  apply Lp.ext
  filter_upwards [plainModeCellLp_ae N r i 0 Fin.elim0,
    Lp.coeFn_zero (E := h i) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx hz
  rw [hx, hz]
  simp [coupledModeJet, hi]

omit [Fintype ι] in
/-- A Fourier test observes only its own component of the input. -/
theorem plainValueForcingCLM_off_component (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (hi : i ≠ r.1)
    (K₀ : ℕ) (f : TorusHk K₀ (h i)) : plainValueForcingCLM N r i K₀ f = 0 := by
  change inner ℝ (plainModeCellLp N r i 0 Fin.elim0) (torusHkValueCLM f) = 0
  rw [plainModeCellLp_off_component N r i hi, inner_zero_left]

/-- The initial scalar row is exactly its own component's value pairing. -/
theorem plainInitialCoefficients_component (N : ℕ) (K : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (r : CoupledFourierModeIndex (h := h) N) :
    plainInitialCoefficients N K f r = plainValueForcingCLM N r r.1 (K r.1) (f r.1) := by
  unfold plainInitialCoefficients
  apply Finset.sum_eq_single r.1
  · intro i _ hi
    exact plainValueForcingCLM_off_component N r i hi (K i) (f i)
  · simp

/-- The reconstructed initial field equals the graph Fourier cutoff, at every Sobolev order. -/
theorem plainInitialCoefficients_synthesis (N : ℕ) (K : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    coupledPlainSynthesis N i (K i) (plainInitialCoefficients N K f) = galerkinProj N (f i) := by
  apply TorusHk.ext_value
  have hsyn : (coupledPlainSynthesis N i (K i) (plainInitialCoefficients N K f)).val
      (valueIndex2 (K i)) = ∑ r : CoupledFourierModeIndex (h := h) N,
        plainInitialCoefficients N K f r • plainModeCellLp N r i 0 Fin.elim0 := by
    simp [coupledPlainSynthesis, coupledModeHk_value_eq_cellLp]
  rw [hsyn]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp_rw [plainInitialCoefficients_component]
    change (∑ p : VectorFourierIndex N (h i),
      inner ℝ (plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0)
        ((f i).val (valueIndex2 (K i))) • plainModeCellLp N ⟨i, p⟩ i 0 Fin.elim0) = _
    rw [← cellVectorFourierProjection_eq_plain_sum]
    rfl
  · intro i' _ hi
    apply Finset.sum_eq_zero
    intro p _
    rw [plainModeCellLp_off_component N ⟨i', p⟩ i (Ne.symm hi), smul_zero]
  · simp


/-- Every explicitly synthesized field is fixed by the M1 Fourier cutoff. -/
theorem plainSynthesis_galerkin_fixed (N : ℕ) (K : ι → ℕ)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    galerkinProj N (coupledPlainSynthesis N i (K i) c) = coupledPlainSynthesis N i (K i) c := by
  have hc : plainInitialCoefficients N K (fun i => coupledPlainSynthesis N i (K i) c) = c := by
    funext r
    exact plainSynthesis_mass_coordinate N K c r
  have hproj := plainInitialCoefficients_synthesis N K
    (fun i => coupledPlainSynthesis N i (K i) c) i
  rw [hc] at hproj
  exact hproj.symm

/-- Projecting the initial data does not increase the exact factorial mass square. -/
theorem plainInitialCoefficients_mass_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (f : ∀ i, TorusHk (K i) (h i)) :
    massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (plainInitialCoefficients N K f)).val) ≤
      massNormSq ρ π (fun i => (f i).val) := by
  unfold massNormSq
  apply Finset.sum_le_sum
  intro i _
  change (π i)⁻¹ * factorialNormSq ρ (coupledPlainSynthesis N i (K i) (plainInitialCoefficients N K f)).val ≤
    (π i)⁻¹ * factorialNormSq ρ (f i).val
  rw [plainInitialCoefficients_synthesis]
  exact mul_le_mul_of_nonneg_left (galerkinProj_factorialNormSq_le N ρ (f i))
    (inv_nonneg.mpr (hπ i).le)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Arbitrary finite test vectors in the integrated coefficient equation,
with reconstructed spatial value pairings and the actual initial data. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The finite coefficient observable associated with an arbitrary retained test. -/
def plainCoefficientTestCLM (N : ℕ) (z : CoupledPlainCoefficients (h := h) N) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] ℝ :=
  ∑ r, z r • ContinuousLinearMap.proj r

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
@[simp] theorem plainCoefficientTestCLM_apply (N : ℕ)
    (z c : CoupledPlainCoefficients (h := h) N) :
    plainCoefficientTestCLM N z c = ∑ r, z r * c r := by
  simp [plainCoefficientTestCLM, smul_eq_mul]

/-- Testing the actual initial coefficient vector recovers its spatial pairing with the test. -/
theorem plainInitialCoefficients_test_pairing (N : ℕ) (K L : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (z : CoupledPlainCoefficients (h := h) N) :
    plainCoefficientTestCLM N z (plainInitialCoefficients N K f) =
      ∑ i, inner ℝ (torusHkValueCLM (f i))
        (torusHkValueCLM (coupledPlainSynthesis N i (L i) z)) := by
  have htest (i : ι) : torusHkValueCLM (coupledPlainSynthesis N i (L i) z) =
      ∑ r, z r • plainModeCellLp N r i 0 Fin.elim0 := by
    simp only [coupledPlainSynthesis_apply, map_sum, map_smul]
    rfl
  simp only [plainCoefficientTestCLM_apply, plainInitialCoefficients, htest,
    inner_sum, real_inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  change z r * inner ℝ (plainModeCellLp N r i 0 Fin.elim0) (torusHkValueCLM (f i)) =
    z r * inner ℝ (torusHkValueCLM (f i)) (plainModeCellLp N r i 0 Fin.elim0)
  rw [real_inner_comm]

/-- Every retained finite test satisfies the integrated equation with literal spatial mass pairings. -/
theorem plainODE_tested_integral_equation (N : ℕ) (K L : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → CoupledFourierModeIndex (h := h) N → CoupledFourierModeIndex (h := h) N → ℝ)
    (source y : ℝ → CoupledPlainCoefficients (h := h) N)
    (f : ∀ i, TorusHk (K i) (h i))
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (A s)) source
      (plainInitialCoefficients N K f) a b y)
    (hint : IntervalIntegrable (linearRhs (fun s => plainMatrixCLM (A s)) source y) volume a b)
    (z : CoupledPlainCoefficients (h := h) N) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (y t)))
      (torusHkValueCLM (coupledPlainSynthesis N i (L i) z))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i))
      (torusHkValueCLM (coupledPlainSynthesis N i (L i) z))) =
    ∫ s in a..t, ∑ r, z r * ((∑ c, A s r c * y s c) + source s r) := by
  have hid := plainODE_observable_identity hab A source y (plainInitialCoefficients N K f)
    hy hint (plainCoefficientTestCLM N z) t ht
  rw [plainInitialCoefficients_test_pairing N K L f z] at hid
  have hmass : plainCoefficientTestCLM N z (y t) =
      ∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (y t)))
        (torusHkValueCLM (coupledPlainSynthesis N i (L i) z)) := by
    rw [plainSynthesis_mixed_mass_pairing, plainCoefficientTestCLM_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _
  rw [hmass] at hid
  simpa only [plainCoefficientTestCLM_apply, Pi.add_apply, plainMatrixCLM_apply] using hid

end AVRegularity.CoupledEnergy.Galerkin
end
