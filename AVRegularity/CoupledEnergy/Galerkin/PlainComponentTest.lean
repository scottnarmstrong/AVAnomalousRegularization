-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CoupledEnergy.Galerkin.PlainLowerSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainFamilyMeasurableFromRows
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar H¹-observable continuity makes every actual finite Fourier
coefficient curve continuous, then synthesis gives continuous Sobolev
cutoffs. This uses the plain Pi coefficient space throughout. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Every finite coefficient coordinate is an actual continuous H¹ observable of the trace. -/
theorem plainTrace_coefficients_continuousOn (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hu : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) :
    ContinuousOn (fun t => plainInitialCoefficients N K (fun i => u i t)) (Set.Icc a b) := by
  apply continuousOn_pi.mpr
  intro r
  apply (hu r.1 (coupledModeHk N r r.1 1)).congr
  intro t _
  dsimp only
  rw [plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N r r.1 0 Fin.elim0) (torusHkValueCLM (u r.1 t)) =
    inner ℝ (torusHkValueCLM (u r.1 t)) ((coupledModeHk N r r.1 1).val (valueIndex2 1))
  rw [coupledModeHk_value_eq_cellLp, real_inner_comm]

/-- Every Fourier cutoff of the weak trace is a continuous genuine Sobolev curve. -/
theorem plainTrace_galerkinProj_continuousOn (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (hu : ∀ i, ∀ φ : TorusHk 1 (h i), ContinuousOn
      (fun t => inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ)) (Set.Icc a b)) (i : ι) :
    ContinuousOn (fun t => galerkinProj N (u i t)) (Set.Icc a b) := by
  have hc := (coupledPlainSynthesis N i (K i)).continuous.comp_continuousOn
    (plainTrace_coefficients_continuousOn N K a b u hu)
  simpa only [Function.comp_def, plainInitialCoefficients_synthesis] using hc

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Countably many finite Fourier coordinates identify genuine periodic
Sobolev trajectories almost everywhere. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Equality of all finite coefficient vectors identifies the whole Sobolev graph. -/
theorem plainTrace_eq_ae_of_coefficients {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (u w : ∀ i, T → TorusHk (K i) (h i))
    (hc : ∀ N, ∀ᵐ t ∂μ, plainInitialCoefficients N K (fun i => u i t) =
      plainInitialCoefficients N K (fun i => w i t)) :
    ∀ᵐ t ∂μ, ∀ i, u i t = w i t := by
  filter_upwards [ae_all_iff.mpr hc] with t ht
  intro i
  have hp (N : ℕ) : galerkinProj N (u i t) = galerkinProj N (w i t) := by
    rw [← plainInitialCoefficients_synthesis N K (fun j => u j t) i,
      ← plainInitialCoefficients_synthesis N K (fun j => w j t) i, ht N]
  exact tendsto_nhds_unique (galerkinProj_tendsto (u i t))
    ((galerkinProj_tendsto (w i t)).congr' (Eventually.of_forall (fun N => (hp N).symm)))

/-- A coefficient is its concrete H¹ Fourier mode pairing. -/
theorem plainInitialCoefficients_mode_pairing (N : ℕ) (K : ι → ℕ)
    (f : ∀ i, TorusHk (K i) (h i)) (r : CoupledFourierModeIndex (h := h) N) :
    plainInitialCoefficients N K f r = inner ℝ (torusHkValueCLM (f r.1))
      (torusHkValueCLM (coupledModeHk N r r.1 1)) := by
  rw [plainInitialCoefficients_component]
  change inner ℝ (plainModeCellLp N r r.1 0 Fin.elim0) (torusHkValueCLM (f r.1)) =
    inner ℝ (torusHkValueCLM (f r.1)) ((coupledModeHk N r r.1 1).val (valueIndex2 1))
  rw [coupledModeHk_value_eq_cellLp, real_inner_comm]

/-- The countable concrete Fourier H¹ tests suffice for almost-everywhere identification. -/
theorem plainTrace_eq_ae_of_mode_pairings {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (u w : ∀ i, T → TorusHk (K i) (h i))
    (hc : ∀ N, ∀ᵐ t ∂μ, ∀ r : CoupledFourierModeIndex (h := h) N,
      inner ℝ (torusHkValueCLM (u r.1 t)) (torusHkValueCLM (coupledModeHk N r r.1 1)) =
      inner ℝ (torusHkValueCLM (w r.1 t)) (torusHkValueCLM (coupledModeHk N r r.1 1))) :
    ∀ᵐ t ∂μ, ∀ i, u i t = w i t := by
  apply plainTrace_eq_ae_of_coefficients μ K u w
  intro N
  filter_upwards [hc N] with t ht
  funext r
  rw [plainInitialCoefficients_mode_pairing, plainInitialCoefficients_mode_pairing]
  exact ht r

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Component-supported tests in the ordinary finite coefficient space. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Retain the finite Fourier coordinates of one component. -/
def plainComponentCoefficients (N : ℕ) (i : ι) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] CoupledPlainCoefficients (h := h) N :=
  ContinuousLinearMap.pi fun a => if a.1 = i then ContinuousLinearMap.proj a else 0

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
@[simp] theorem plainComponentCoefficients_apply (N : ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) (a : CoupledFourierModeIndex (h := h) N) :
    plainComponentCoefficients N i c a = if a.1 = i then c a else 0 := by
  by_cases ha : a.1 = i <;> simp [plainComponentCoefficients, ha]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Component-supported tests preserve every raw derivative in their own component. -/
theorem plainComponentCoefficients_raw_self (N : ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) (r : ℕ) (w : DerivativeWord2 r) (x : Vec 2) :
    coupledPlainRawJet N (plainComponentCoefficients N i c) i r w x =
      coupledPlainRawJet N c i r w x := by
  unfold coupledPlainRawJet
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.1 = i
  · simp [ha]
  · have hi : i ≠ a.1 := Ne.symm ha
    simp [plainComponentCoefficients_apply, ha, coupledModeJet, hi]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Component-supported tests vanish in every other component. -/
theorem plainComponentCoefficients_raw_other (N : ℕ) (i j : ι) (hji : j ≠ i)
    (c : CoupledPlainCoefficients (h := h) N) (r : ℕ) (w : DerivativeWord2 r) (x : Vec 2) :
    coupledPlainRawJet N (plainComponentCoefficients N i c) j r w x = 0 := by
  unfold coupledPlainRawJet
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a.1 = i
  · simp [plainComponentCoefficients_apply, ha, coupledModeJet, hji]
  · simp [plainComponentCoefficients_apply, ha]

/-- The reconstructed supported test agrees with the chosen component at every Sobolev order. -/
theorem plainComponentCoefficients_synthesis_self (N : ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) (K : ℕ) :
    coupledPlainSynthesis N i K (plainComponentCoefficients N i c) = coupledPlainSynthesis N i K c := by
  apply TorusHk.ext_value
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N i K _ (valueIndex2 K)).trans
    ((Filter.EventuallyEq.of_eq (funext (plainComponentCoefficients_raw_self N i c 0 Fin.elim0))).trans
      (coupledPlainSynthesis_jet_ae N i K c (valueIndex2 K)).symm)

/-- The reconstructed supported test is zero in every other Sobolev component. -/
theorem plainComponentCoefficients_synthesis_other (N : ℕ) (i j : ι) (hji : j ≠ i)
    (c : CoupledPlainCoefficients (h := h) N) (K : ℕ) :
    coupledPlainSynthesis N j K (plainComponentCoefficients N i c) = 0 := by
  apply TorusHk.ext_value
  change (coupledPlainSynthesis N j K (plainComponentCoefficients N i c)).val (valueIndex2 K) =
    (0 : ComponentL2 (volume.restrict AVenhance.unitCube) (h j))
  apply Lp.ext
  filter_upwards [coupledPlainSynthesis_jet_ae N j K (plainComponentCoefficients N i c) (valueIndex2 K),
    Lp.coeFn_zero (E := h j) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx hz
  rw [hx, hz, plainComponentCoefficients_raw_other N i j hji c]
  rfl

/-- Differentiating a component-supported test still vanishes in every other component. -/
theorem plainComponentDerivative_synthesis_other (N : ℕ) (i j : ι) (hji : j ≠ i)
    (c : CoupledPlainCoefficients (h := h) N) {r : ℕ} (w : DerivativeWord2 r) (L : ℕ) :
    coupledPlainSynthesis N j L (plainDerivativeCoefficients N L w (plainComponentCoefficients N i c)) = 0 := by
  rw [plainDerivativeCoefficients_synthesis, plainComponentCoefficients_synthesis_other N i j hji,
    map_zero]

/-- Differentiating a component-supported test preserves the chosen component's derivative. -/
theorem plainComponentDerivative_synthesis_self (N : ℕ) (i : ι)
    (c : CoupledPlainCoefficients (h := h) N) {r : ℕ} (w : DerivativeWord2 r) (L : ℕ) :
    coupledPlainSynthesis N i L (plainDerivativeCoefficients N L w (plainComponentCoefficients N i c)) =
      coupledPlainSynthesis N i L (plainDerivativeCoefficients N L w c) := by
  rw [plainDerivativeCoefficients_synthesis, plainDerivativeCoefficients_synthesis,
    plainComponentCoefficients_synthesis_self]

end AVRegularity.CoupledEnergy.Galerkin
end
