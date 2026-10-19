-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify the actual coupling carrier with the Fourier matrix's literal coefficient action. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The reserve tensor of a finite field is exactly its finite order-m raw Fourier tensor. -/
theorem plainPositiveDerivativeTensor_value_ae (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) {K L : ℕ} (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L) :
    (torusPositiveDerivativeTensor m hm hKL (coupledPlainSynthesis N i (L + 1) c)).val
      (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] coupledPlainRawTensor N c i m := by
  have ht := torusPositiveDerivativeTensor_value_ae m hm hKL (coupledPlainSynthesis N i (L + 1) c)
  have hs : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ w : DerivativeWord2 m,
      (coupledPlainSynthesis N i (L + 1) c).val ⟨⟨m, by omega⟩, w⟩ x =
        coupledPlainRawJet N c i m w x :=
    ae_all_iff.mpr (fun w => coupledPlainSynthesis_jet_ae N i (L + 1) c ⟨⟨m, by omega⟩, w⟩)
  filter_upwards [ht, hs] with x hx hwords
  rw [hx]
  apply PiLp.ext
  intro w
  exact hwords w

/-- Each actual coupling flux's value is precisely the coefficient applied to the synthesized tensor. -/
theorem plainCoupledFluxTerm_value_ae (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) :
    (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp
      (coupledPlainSynthesis N i' (K i' + 1) c)).val (valueIndex2 (K i)) =ᵐ[
        volume.restrict AVenhance.unitCube]
      fun x => A t x (coupledPlainRawTensor N c i' (d.1 - 1) x) := by
  have hm := torusMulCoefficient_value_ae
    (torusPositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 (coupledPlainSynthesis N i' (K i' + 1) c))
    (A t) hC hp (fun l x => coefficientOrderSup_derivative_bound ρ hρ (K i) a b A hA
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)
  have hs := plainPositiveDerivativeTensor_value_ae N c i' (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2
  filter_upwards [hm, hs] with x hx htensor
  exact hx.trans (congrArg (A t x) htensor)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Ordered derivatives of the finite synthesis stay in the same plain coefficient space. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The derivative coefficient map is a finite family of scalar Fourier pairings. -/
def plainDerivativeCoefficients (N L : ℕ) {r : ℕ} (w : DerivativeWord2 r) :
    CoupledPlainCoefficients (h := h) N →L[ℝ] CoupledPlainCoefficients (h := h) N :=
  ContinuousLinearMap.pi fun a => ∑ i,
    (plainValueForcingCLM N a i L).comp
      ((derivativeTorusHk w).comp (coupledPlainSynthesis N i (L + r)))

/-- The finite derivative coefficient map consists exactly of the initial-pairing map of the derivatives. -/
theorem plainDerivativeCoefficients_apply (N L : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (c : CoupledPlainCoefficients (h := h) N) :
    plainDerivativeCoefficients N L w c = plainInitialCoefficients N (fun _ => L)
      (fun i => derivativeTorusHk w (coupledPlainSynthesis N i (L + r) c)) := by
  funext a
  simp [plainDerivativeCoefficients, plainInitialCoefficients]

/-- Reconstructing derivative coefficients gives exactly the differentiated field in the Sobolev carrier. -/
theorem plainDerivativeCoefficients_synthesis (N L : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    coupledPlainSynthesis N i L (plainDerivativeCoefficients N L w c) =
      derivativeTorusHk w (coupledPlainSynthesis N i (L + r) c) := by
  rw [plainDerivativeCoefficients_apply,
    plainInitialCoefficients_synthesis N (fun _ => L)]
  rw [galerkinProj_derivative_commute,
    plainSynthesis_galerkin_fixed N (fun _ => L + r)]


/-- The value slot of an ordered derivative is the corresponding original weak-jet slot. -/
theorem derivativeTorusHk_value_slot {L r : ℕ} (w : DerivativeWord2 r)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (f : TorusHk (L + r) E) :
    (derivativeTorusHk w f).val (valueIndex2 L) = f.val ⟨⟨r, by omega⟩, w⟩ := by
  rw [derivativeTorusHk_apply]
  have hi : prefixJetIndex w (valueIndex2 L) = (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (L + r)) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi]

/-- Every reconstructed derivative coefficient has the exact original raw Fourier derivative as its value. -/
theorem plainDerivativeCoefficients_value_ae (N L : ℕ) {r : ℕ} (w : DerivativeWord2 r)
    (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    (coupledPlainSynthesis N i L (plainDerivativeCoefficients N L w c)).val (valueIndex2 L) =ᵐ[
      volume.restrict AVenhance.unitCube] coupledPlainRawJet N c i r w := by
  rw [plainDerivativeCoefficients_synthesis, derivativeTorusHk_value_slot]
  exact coupledPlainSynthesis_jet_ae N i (L + r) c ⟨⟨r, by omega⟩, w⟩

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Genuine Sobolev-valued measurability from integrable Fourier scalar
rows. This avoids any measurability assumption on the spatial coefficient
derivatives when constructing the transport and coupling trajectories. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
variable {T : Type*} [MeasurableSpace T]

theorem plainFamily_aestronglyMeasurable_of_integrable_rows (μ : Measure T) (K : ι → ℕ)
    (u : ∀ i, T → TorusHk (K i) (h i))
    (hrow : ∀ N, ∀ r : CoupledFourierModeIndex (h := h) N,
      Integrable (fun t => plainInitialCoefficients N K (fun i => u i t) r) μ) (i : ι) :
    AEStronglyMeasurable (u i) μ := by
  have hm (N : ℕ) : AEStronglyMeasurable (fun t => galerkinProj N (u i t)) μ := by
    have hc : Integrable (fun t => plainInitialCoefficients N K (fun i => u i t)) μ :=
      integrable_pi_iff.mpr (hrow N)
    have hs := (coupledPlainSynthesis N i (K i)).continuous.comp_aestronglyMeasurable hc.aestronglyMeasurable
    simpa only [Function.comp_def, plainInitialCoefficients_synthesis] using hs
  exact aestronglyMeasurable_of_tendsto_ae atTop hm
    (Eventually.of_forall (fun t => galerkinProj_tendsto (u i t)))

end AVRegularity.CoupledEnergy.Galerkin
end
