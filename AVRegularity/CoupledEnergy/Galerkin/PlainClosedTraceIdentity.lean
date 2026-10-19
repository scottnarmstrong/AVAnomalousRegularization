-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
public import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
import AVRegularity.CoupledEnergy.Galerkin.PlainSourceEnergy
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergy.CouplingBounds
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The Fourier cutoffs of an actual weak trace are finite vector primitives
with integrable native PDE forcing. This supplies the energy chain rule
needed for the Lions-Magenes spectral-tail argument. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTrace_coefficients_integralSolution (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b)
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hid : ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
        coupledIntegratedRhs K D ν a t v A F g U i φ) :
    let q := fun t r => coupledTimeRhs K D ν t v A F g (U t) r.1
      (coupledModeHk N r r.1 1)
    IntervalIntegrable q volume a b ∧
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) q
        (plainInitialCoefficients N K f) a b
        (fun t => plainInitialCoefficients N K (fun i => u i t)) := by
  dsimp only
  let q : ℝ → CoupledPlainCoefficients (h := h) N := fun t r =>
    coupledTimeRhs K D ν t v A F g (U t) r.1 (coupledModeHk N r r.1 1)
  have hq : IntervalIntegrable q volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply integrable_pi_iff.mpr
    intro r
    exact coupledTimeRhs_integrable K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc F g hF hg U
      r.1 (coupledModeHk N r r.1 1)
  refine ⟨hq, plainRows_isIntegralSolution hab q _ _ hq ?_⟩
  intro t ht r
  rw [plainInitialCoefficients_mode_pairing, plainInitialCoefficients_mode_pairing]
  rw [hid r.1 t ht]
  exact (coupledTimeRhs_integral K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc F g hF hg U
    r.1 (coupledModeHk N r r.1 1)).symm

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Rewrite the native weak equation in terms of genuine Sobolev transport
and flux carriers. The scalar value source keeps its original L¹ role. -/

open AVRegularity.CoupledEnergy.Variational
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTimeRhs_eq_sourceCoefficient (N : ℕ) (K : ι → ℕ) (D : ℕ) (ν r : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hc : Continuous (v r))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ x, ‖v r x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighHilbert (h := h) K)
    (T : ∀ i, TorusHk (K i) (h i))
    (G : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (B : ∀ i i', admissibleOrders K D i i' → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hT : ∀ i, (T i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ k : Fin 2, v r x k • (U i
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x))
    (hG : ∀ i, (G i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      coupledHighGradientCLM (h := h) K i U)
    (hB : ∀ i i' d, (B i i' d).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) U x)) (z : CoupledFourierModeIndex (h := h) N) :
    coupledTimeRhs K D ν r v A F g U z.1 (coupledModeHk N z z.1 1) =
      plainSourceCoefficients N K
        (fun i => ν • G i + (∑ i', ∑ d, B i i' d) + F i r)
        (fun i => g i r - T i) z := by
  rw [coupledTimeRhs_carrier_split K D ν r v hc V hV hb A F g U T G B hT hG hB,
    plainSourceCoefficients_mode_pairing]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Original source terms in the literal finite equation are precisely the
projected H¹ carrier pairings used in the L²/L¹ limit arguments. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The actual finite forcing integral splits into projected flux and value test pairings. -/
theorem plainForcingTest_projected_integral (N : ℕ) (φ : ∀ i, TorusHk 1 (h i))
    (F : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    (∫ x in AVenhance.unitCube,
      plainForcingTestIntegrand N (plainInitialCoefficients N (fun _ => 1) φ) F g x) =
    ∑ i, ((∫ x in AVenhance.unitCube, inner ℝ (g i x) (torusHkValueCLM (galerkinProj N (φ i)) x)) -
      (∫ x in AVenhance.unitCube, inner ℝ (F i x)
        (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) x))) := by
  have hg (i : ι) : Integrable (fun x => inner ℝ (g i x)
      (coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 0 Fin.elim0 x))
      (volume.restrict AVenhance.unitCube) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (g i) (torusHkValueCLM (galerkinProj N (φ i)))).congr
    filter_upwards [plainProjectedTest_value_ae N φ i] with x hx
    rw [hx]
  have hF (i : ι) : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F i x k)
      (coupledPlainRawJet N (plainInitialCoefficients N (fun _ => 1) φ) i 1 (fun _ => k) x))
      (volume.restrict AVenhance.unitCube) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (F i)
      (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)))).congr
    filter_upwards [plainProjectedTest_gradient_ae N φ i] with x hx
    rw [hx, PiLp.inner_apply]
  unfold plainForcingTestIntegrand
  have hsum := integral_finsetSum Finset.univ (fun i _ => (hg i).sub (hF i))
  simp only [Pi.sub_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  have hsub := integral_sub (hg i) (hF i)
  rw [hsub]
  congr 1
  · apply integral_congr_ae
    filter_upwards [plainProjectedTest_value_ae N φ i] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [plainProjectedTest_gradient_ae N φ i] with x hx
    rw [hx, PiLp.inner_apply]
end

/-! The finite spatial equation expressed on fixed ambient trial readouts
and the actual projected H¹ tests. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- All spatial terms in the finite equation equal the fixed-readout native weak form. -/
theorem plainSpatialTest_projected_integral (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2) (hv : Continuous v)
    (A : ∀ i i', (d : admissibleOrders K D i i') → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Continuous (A i i' d))
    (c : CoupledPlainCoefficients (h := h) N) (φ : ∀ i, TorusHk 1 (h i)) :
    (∫ x in AVenhance.unitCube, plainSpatialTestIntegrand N D ν K v A c
      (plainInitialCoefficients N (fun _ => 1) φ) x) =
    -ν * (∑ i, ∫ x in AVenhance.unitCube,
      inner ℝ (coupledHighGradientCLM (h := h) K i (plainHigherSynthesisCLM N K c) x)
        (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) x)) -
    (∑ i, ∑ k : Fin 2, ∫ x in AVenhance.unitCube, v x k *
      inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
        fun _ => k⟩ (plainHigherSynthesisCLM N K c) x) (torusHkValueCLM (galerkinProj N (φ i)) x)) -
    (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∫ x in AVenhance.unitCube,
      inner ℝ (A i i' d x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (plainHigherSynthesisCLM N K c) x))
        (torusH1GradientL2CLM (E := h i) (galerkinProj N (φ i)) x)) := by
  rw [plainSpatialTest_integral_split N D ν K v hv A hA]
  simp_rw [plainDiffusion_test_integral N K c φ, plainDrift_test_integral N K c φ,
    plainCoupling_test_integral N D K c φ]
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The explicit Fourier matrix is exactly the native weak diffusion, drift and coupling source. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)

/-- No spatial terms are assumed: the literal scalar-integral matrix is the actual Sobolev source vector. -/
theorem plainFourierMatrix_action_eq_spatial_source (r : CoupledFourierModeIndex (h := h) N) :
    plainMatrixCLM (plainFourierMatrix N D ν K v A t) c r =
      plainSourceCoefficients N K
        (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c)
        (fun i => -coupledPlainDriftHk N c i (K i) (v t) hv hvp) r := by
  rw [plainMatrixCLM_apply,
    plainFourierMatrix_action_eq_spatial_integral N D ν K v A t hv.continuous
      (fun i i' d => (hC i i' d).continuous), plainSourceCoefficients_eq_fourierForcing]
  unfold plainFourierForcing
  apply integral_congr_ae
  have hf : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ i : ι,
      (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i).val (valueIndex2 (K i)) x =
        ν • coupledPlainGradientJet N c i 0 Fin.elim0 x +
          ∑ i', ∑ d : admissibleOrders K D i i', A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) :=
    ae_all_iff.mpr (plainSpatialFlux_value_ae N D ν ρ hρ K a b A hA t ht hC hp c)
  have hg : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ i : ι,
      (-coupledPlainDriftHk N c i (K i) (v t) hv hvp).val (valueIndex2 (K i)) x =
        -(∑ k : Fin 2, v t x k • coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x) := by
    rw [ae_all_iff]
    intro i
    have hn : (-coupledPlainDriftHk N c i (K i) (v t) hv hvp).val (valueIndex2 (K i)) =
        -(coupledPlainDriftHk N c i (K i) (v t) hv hvp).val (valueIndex2 (K i)) := by
      change WithLp.ofLp (-(coupledPlainDriftHk N c i (K i) (v t) hv hvp).val)
        (valueIndex2 (K i)) = _
      rw [WithLp.ofLp_neg]
      rfl
    rw [hn]
    filter_upwards [Lp.coeFn_neg ((coupledPlainDriftHk N c i (K i) (v t) hv hvp).val (valueIndex2 (K i))),
      coupledPlainDriftHk_value_ae N c i (K i) (v t) hv hvp] with x hx hy
    rw [hx, Pi.neg_apply, hy]
  filter_upwards [hf, hg] with x hx hy
  have hflux (i : ι) (k : Fin 2) :
      (ν • coupledPlainGradientJet N c i 0 Fin.elim0 x +
        ∑ i', ∑ d : admissibleOrders K D i i', A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x)) k =
      ν • coupledPlainRawJet N c i 1 (fun _ : Fin 1 => k) x +
        ∑ i', ∑ d : admissibleOrders K D i i', (A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x)) k := by
    have hw : (Fin.snoc Fin.elim0 k : DerivativeWord2 1) = fun _ : Fin 1 => k := by
      funext z
      fin_cases z
      rfl
    simp [WithLp.ofLp_sum, coupledPlainGradientJet_apply, hw]
  have hcoup (i : ι) : (∑ k : Fin 2, ∑ i', ∑ d : admissibleOrders K D i i',
      inner ℝ (A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
        (coupledModeJet N r i 1 (fun _ => k) x)) =
      ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
        inner ℝ (A i i' d t x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
          (coupledModeJet N r i 1 (fun _ => k) x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' _
    rw [Finset.sum_comm]
  change plainSpatialRowIntegrand N D ν K (v t) (fun i i' d => A i i' d t) r c x =
    ∑ i, (inner ℝ ((-coupledPlainDriftHk N c i (K i) (v t) hv hvp).val (valueIndex2 (K i)) x)
      (coupledModeJet N r i 0 Fin.elim0 x) -
      ∑ k : Fin 2, inner ℝ ((plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i).val
        (valueIndex2 (K i)) x k) (coupledModeJet N r i 1 (fun _ => k) x))
  simp only [hy, hx, hflux, inner_neg_left, sum_inner, real_inner_smul_left,
    inner_add_left, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, hcoup, ← Finset.mul_sum, plainSpatialRowIntegrand]
  ring

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Genuine time L² transport from value-level measurability and a finite
spatial derivative budget. Fourier rows supply carrier measurability. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem plainTransport_memLp (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (coupledHighGraphReadout K i (U t)).val = U t i)
    (T : ∀ i, ℝ → TorusHk (K i) (h i))
    (hT : ∀ t, ∀ ht : t ∈ Set.Icc a b, ∀ i,
      T i t = torusTransportCarrier (v t) (hc t ht) (hp t ht) (C i)
        (hC t ht i) (coupledHighGraphReadout K i (U t))) :
    ∀ i, MemLp (T i) 2 (volume.restrict (Set.Icc a b)) := by
  have hval : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (T i t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        ∑ k : Fin 2, v t x k • (U t i
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) := by
    filter_upwards [hU, ae_restrict_mem measurableSet_Icc] with t hu ht
    intro i
    rw [hT t ht i]
    have hh := torusTransportCarrier_value_ae (v t) (hc t ht) (hp t ht) (C i)
      (hC t ht i) (coupledHighGraphReadout K i (U t))
    simpa only [hu i] using hh
  have hrows := plainTransport_rows_integrable K hab v hv (fun t ht => (hc t ht).continuous)
    V hV hb U T hval
  intro i
  apply (highTimeGraphReadout_memLp K a b U i).of_le_mul
    (plainFamily_aestronglyMeasurable_of_integrable_rows _ K T hrows i)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [hT t ht i]
  exact torusTransportCarrier_norm_le ρ hρ (v t) (hc t ht) (hp t ht) (C i)
    (hC t ht i) (coupledHighGraphReadout K i (U t))

/-- Construct the actual transport trajectory using precisely the original velocity envelope. -/
theorem plainTransport_exists_memLp (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (α B lam : ℝ)
    (hj : ∀ t ∈ Set.Icc a b, ∀ i l, 1 ≤ l → l ≤ K i → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (coupledHighGraphReadout K i (U t)).val = U t i) :
    ∃ T : ∀ i, ℝ → TorusHk (K i) (h i),
      (∀ i, MemLp (T i) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        (T i t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
          ∑ k : Fin 2, v t x k • (U t i
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)) := by
  let C := fun i => driftCarrierBudget (K i) V α B lam
  have hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l := by
    intro t ht i
    exact driftCarrierBudget_bounds (K i) (v t) V α B lam hV (hb t ht) (hj t ht i)
  let T : ∀ i, ℝ → TorusHk (K i) (h i) := fun i t =>
    if ht : t ∈ Set.Icc a b then
      torusTransportCarrier (v t) (hc t ht) (hp t ht) (C i) (hC t ht i)
        (coupledHighGraphReadout K i (U t))
    else 0
  have he : ∀ t, ∀ ht : t ∈ Set.Icc a b, ∀ i,
      T i t = torusTransportCarrier (v t) (hc t ht) (hp t ht) (C i) (hC t ht i)
        (coupledHighGraphReadout K i (U t)) := by
    intro t ht i
    simp only [T, dite_eq_left ht]
  refine ⟨T, plainTransport_memLp K hab ρ hρ v hv hc hp V hV hb C hC U hU T he, ?_⟩
  filter_upwards [hU, ae_restrict_mem measurableSet_Icc] with t hu ht
  intro i
  rw [he t ht i]
  have hh := torusTransportCarrier_value_ae (v t) (hc t ht) (hp t ht) (C i)
    (hC t ht i) (coupledHighGraphReadout K i (U t))
  simpa only [hu i] using hh

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Exact differentiated energy rows for the actual scalar-integral Fourier system. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)
  (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, TorusHk (K i) (h i))

/-- The actual projected RHS is the genuine combined weak source, including the given forcing. -/
theorem plainFourierRhs_eq_totalSource :
    plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g =
      plainSourceCoefficients N K
        (fun i => plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i + F i)
        (fun i => -coupledPlainDriftHk N c i (K i) (v t) hv hvp + g i) := by
  funext r
  rw [Pi.add_apply, plainFourierMatrix_action_eq_spatial_source N D ν ρ hρ K a b v A hA t ht hv hvp hC hp c r]
  simp only [plainSourceCoefficients, ContinuousLinearMap.map_add, ContinuousLinearMap.map_neg,
    Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- Every differentiated RHS row is exactly its weak value pairing minus its weak flux pairing. -/
theorem plainFourierRhs_energy_row (i : ι) {r : ℕ} (hr : r ≤ K i) (w : DerivativeWord2 r) :
    inner ℝ
      ((coupledPlainSynthesis N i (K i)
        (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g)).val
          ⟨⟨r, by omega⟩, w⟩)
      ((coupledPlainSynthesis N i (K i) c).val ⟨⟨r, by omega⟩, w⟩) =
      inner ℝ ((-coupledPlainDriftHk N c i (K i) (v t) hv hvp + g i).val ⟨⟨r, by omega⟩, w⟩)
        ((coupledPlainSynthesis N i (K i) c).val ⟨⟨r, by omega⟩, w⟩) -
      ∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube))
          ((plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i + F i).val ⟨⟨r, by omega⟩, w⟩))
        ((coupledPlainSynthesis N i (K i + 1) c).val ⟨⟨r + 1, by omega⟩, Fin.snoc w k⟩) := by
  rw [← plainEnergyTest_pairing hr N i w c,
    plainFourierRhs_eq_totalSource N D ν ρ hρ K a b v A hA t ht hv hvp hC hp c F g]
  exact plainSourceCoefficients_energy_pairing N K i hr w _ _ c

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Literal transport paths of arbitrary higher Sobolev trajectories.
Their Fourier tail errors vanish in time L² and time L¹. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)

def plainTransportCarrierPath (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)) :
    ∀ i, ℝ → TorusHk (K i) (h i) := fun i t =>
  if ht : t ∈ Set.Icc a b then
    torusTransportCarrier (v t) (hc t ht) (hp t ht) (C i) (hC t ht i) (w i t)
  else 0

theorem plainTransportCarrierPath_memLp (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (plainTransportCarrierPath K a b v hc hp C hC w i)
      2 (volume.restrict (Set.Icc a b)) := by
  let U := coupledCarrierHighTime K a b w hw
  let W : ∀ j, ℝ → TorusHk (K j + 1) (h j) := fun j t => coupledHighGraphReadout K j (U t)
  have he := coupledCarrierHighTime_graphReadout_ae K a b w hw
  have hu : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j := by
    filter_upwards [he, coupledCarrierHighTime_ae K a b w hw] with t ht hval
    intro j
    rw [ht j]
    exact hval j
  have hLp := plainTransport_memLp K hab ρ hρ v hv hc hp V hV hb C hC U hu
    (plainTransportCarrierPath K a b v hc hp C hC W)
    (by intro t ht j; simp only [plainTransportCarrierPath, dite_eq_left ht, W]) i
  have heq : plainTransportCarrierPath K a b v hc hp C hC W i =ᵐ[
      volume.restrict (Set.Icc a b)] plainTransportCarrierPath K a b v hc hp C hC w i := by
    filter_upwards [he] with t ht
    unfold plainTransportCarrierPath
    split_ifs with hti
    · rw [show W i t = w i t from ht i]
    · rfl
  exact (memLp_congr_ae heq).mp hLp

theorem plainTransportCarrierPath_tail_norm_tendsto (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (w : ∀ j, ℝ → TorusHk (K j + 1) (h j))
    (hw : ∀ j, MemLp (w j) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b,
      ‖plainTransportCarrierPath K a b v hc hp C hC
        (fun j s => w j s - galerkinProj N (w j s)) i t‖)
      Filter.atTop (nhds 0) := by
  have htLp (N : ℕ) (j : ι) : MemLp (fun s => w j s - galerkinProj N (w j s))
      2 (volume.restrict (Set.Icc a b)) := by
    simpa only [Pi.sub_apply, Function.comp_def] using!
      (hw j).sub ((galerkinProj (E := h j) (K := K j + 1) N).comp_memLp' (hw j))
  let L := ((∑ l : Fin (K i + 1), factorialRootWeight ρ l.val * C i l) *
      Real.sqrt (factorialWeightMax ρ (K i)) / Real.sqrt (factorialWeightMin ρ (K i)))
  have hL : 0 ≤ L := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    apply mul_nonneg _ (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro l _
    have hCl : 0 ≤ C i l := (norm_nonneg _).trans (hC a ⟨le_rfl, hab⟩ i l 0)
    exact mul_nonneg (by unfold factorialRootWeight; positivity) hCl
  apply boundedResidual_integral_norm_tendsto (volume.restrict (Set.Icc a b))
    (fun N => galerkinProj (E := h i) (K := K i + 1) N) (galerkinProj_norm_le (E := h i) (K := K i + 1))
    (galerkinProj_tendsto (E := h i) (K := K i + 1)) (w i) (hw i)
    (fun N => plainTransportCarrierPath K a b v hc hp C hC
      (fun j s => w j s - galerkinProj N (w j s)) i)
    (fun N => plainTransportCarrierPath_memLp K a b v hc hp C hC hab ρ hρ hv V hV hb _ (htLp N) i) L hL
  intro N
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [plainTransportCarrierPath, dite_eq_left ht]
  have hn := torusTransportCarrier_norm_le ρ hρ (v t) (hc t ht) (hp t ht) (C i) (hC t ht i)
    (w i t - galerkinProj N (w i t))
  simpa only [norm_sub_rev] using hn
end

/-! The full spatial energy identity of the actual projected coupled system. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)
  (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, TorusHk (K i) (h i))


/-- The literal projected RHS splits into diffusion, transport, coupling and the two forcing terms. -/
theorem plainFourierRhs_factorial_energy_identity (i : ι) :
    inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N i (K i)
        (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g)).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val) =
    inner ℝ (factorialWeightedJet ρ (g i).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val) -
    inner ℝ (factorialWeightedJet ρ (coupledPlainDriftHk N c i (K i) (v t) hv hvp).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val) -
    ν * gradFactorialNormSq ρ (coupledPlainSynthesis N i (K i + 1) c).val -
    inner ℝ (factorialWeightedJet ρ (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val)
      (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) -
    inner ℝ (factorialWeightedJet ρ (F i).val)
      (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) := by
  have hid : inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N i (K i)
        (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g)).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val) =
      inner ℝ (factorialWeightedJet ρ (-coupledPlainDriftHk N c i (K i) (v t) hv hvp + g i).val)
        (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val) -
      inner ℝ (factorialWeightedJet ρ
        (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i + F i).val)
        (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) := by
    rw [factorialWeightedJet_inner]
    have hrow (j : Fin (K i + 1)) (w : DerivativeWord2 j.val) :=
      plainFourierRhs_energy_row N D ν ρ hρ K a b v A hA t ht hv hvp hC hp c F g i
        (Nat.le_of_lt_succ j.isLt) w
    simp_rw [hrow, Finset.sum_sub_distrib, mul_sub]
    rw [Finset.sum_sub_distrib, ← factorialWeightedJet_inner, plainFlux_factorial_pairing]
  rw [hid]
  have hvval : (-coupledPlainDriftHk N c i (K i) (v t) hv hvp + g i).val =
      -(coupledPlainDriftHk N c i (K i) (v t) hv hvp).val + (g i).val := rfl
  have hfval : (plainSpatialFlux N D ν ρ hρ K a b A hA t ht hC hp c i + F i).val =
      ν • (coupledPlainGradientHk N c i (K i)).val +
        (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val + (F i).val := rfl
  rw [hvval, hfval]
  simp only [factorialWeightedJet_add, factorialWeightedJet_neg, factorialWeightedJet_smul,
    inner_add_left, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    factorialWeightedJet_normSq, coupledPlainGradientHk_factorialNormSq]
  ring
end

/-! The exact pointwise a priori energy inequality for the actual plain Fourier RHS. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
  (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (c : CoupledPlainCoefficients (h := h) N)
  (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, TorusHk (K i) (h i))



include hρ hA ht hv hvp hC hp in
/-- Diffusion absorbs the actual drift, coupling and flux terms with the source constants required by M3. -/
theorem plainFourierRhs_mass_energy_le (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) :
    (∑ i, (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N i (K i)
        (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g)).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N i (K i) c).val)) +
      (ν / 2) * massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) c).val) ≤
    Real.sqrt (massNormSq ρ π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) c).val)) +
      (2 / ν) * massNormSq ρ π (fun i => (F i).val) := by
  let U := fun i => (coupledPlainSynthesis N i (K i) c).val
  let W := fun i => (coupledPlainSynthesis N i (K i + 1) c).val
  let R := massGradNormSq ρ π W
  let Gp := ∑ i, (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (g i).val) (factorialWeightedJet ρ (U i))
  let Vp := ∑ i, (π i)⁻¹ * inner ℝ
    (factorialWeightedJet ρ (coupledPlainDriftHk N c i (K i) (v t) hv hvp).val)
    (factorialWeightedJet ρ (U i))
  let Cp := ∑ i, (π i)⁻¹ * inner ℝ
    (factorialWeightedJet ρ (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val)
    (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val)
  let Fp := ∑ i, (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (F i).val)
    (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val)
  have hG : |Gp| ≤ Real.sqrt (massNormSq ρ π (fun i => (g i).val)) * Real.sqrt (massNormSq ρ π U) :=
    massFactorialPairing_abs_le ρ π hπ _ _
  have hV : |Vp| ≤ (ν / 4) * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    change (∑ i, |(π i)⁻¹ * inner ℝ
      (factorialWeightedJet ρ (coupledPlainDriftHk N c i (K i) (v t) hv hvp).val)
      (factorialWeightedJet ρ (U i))|) ≤ _
    simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (hπ _).le)]
    change _ ≤ (ν / 4) * ∑ i, (π i)⁻¹ * gradFactorialNormSq ρ (W i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := coupledPlainDriftHk_energy_abs_le (hK i) N c i ρ αv B lam ν hρ hα hB hlam hν
      hsmall hstrain (v t) hv hvp hd hjets
    rw [← factorialWeightedJet_inner] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hπ i).le)).trans_eq (by ring)
  have hCoup : |Cp| ≤ (ν / 8) * R :=
    plainCouplingFlux_massPairing_abs_le N D ρ hρ K a b A hA t ht hC hp c ν hν π hπ hschur
  have hgrad : massNormSq ρ π (fun i => (coupledPlainGradientHk N c i (K i)).val) = R := by
    unfold massNormSq R massGradNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [coupledPlainGradientHk_factorialNormSq]
  have hF := massFactorialPairing_abs_le ρ π hπ (fun i => (F i).val)
    (fun i => (coupledPlainGradientHk N c i (K i)).val)
  rw [hgrad] at hF
  have hy := coupledFluxYoung hν (Real.sqrt (massNormSq ρ π (fun i => (F i).val))) (Real.sqrt R)
  rw [Real.sq_sqrt (massNormSq_nonneg ρ π hπ _), Real.sq_sqrt (massGradNormSq_nonneg ρ π hπ W)] at hy
  have hid := fun i => plainFourierRhs_factorial_energy_identity N D ν ρ hρ K a b v A hA t ht hv hvp hC hp c F g i
  have he (i : ι) : (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N i (K i)
        (plainMatrixCLM (plainFourierMatrix N D ν K v A t) c + plainSourceCoefficients N K F g)).val)
      (factorialWeightedJet ρ (U i)) =
      (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (g i).val) (factorialWeightedJet ρ (U i)) -
      (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (coupledPlainDriftHk N c i (K i) (v t) hv hvp).val)
        (factorialWeightedJet ρ (U i)) - ν * ((π i)⁻¹ * gradFactorialNormSq ρ (W i)) -
      (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (plainCouplingFlux N D ρ hρ K a b A hA t ht hC hp c i).val)
        (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) -
      (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (F i).val)
        (factorialWeightedJet ρ (coupledPlainGradientHk N c i (K i)).val) := by
    dsimp only [U, W]
    rw [hid i]
    ring
  have hs := congrArg (fun z : ι → ℝ => ∑ i, z i) (funext he)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  change _ = Gp - Vp - ν * R - Cp - Fp at hs
  change _ + (ν / 2) * R ≤ _
  rw [hs]
  have hnegV := neg_le_abs Vp
  have hnegC := neg_le_abs Cp
  have hnegF := neg_le_abs Fp
  have hposG := le_abs_self Gp
  change |Fp| ≤ _ at hF
  change _ ≤ (ν / 8) * R + (2 / ν) * massNormSq ρ π (fun i => (F i).val) at hy
  dsimp only [U] at hG
  linarith
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Original coefficient and forcing assumptions discharge the finite RHS integrability. -/
theorem plainFourier_projected_ambient_weak_equation (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, Continuous (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b)))
    (y : C(Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b (extendCurve hab y))
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (extendCurve hab y t)))
      (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∫ r in a..t, ∑ i, coupledTimeRhs K D ν r v A F g
      (plainHigherBochner N K a b hab y r) i (galerkinProj N (φ i)) := by
  rw [plainHigherBochner_test_integral N K hab ⟨le_rfl, hab⟩ ht ht.1 y
    (fun r U => ∑ i, coupledTimeRhs K D ν r v A F g U i (galerkinProj N (φ i)))]
  rw [plainFourier_projected_weak_equation_of_data N D ν ρ hρ K hab v A hv_bdd hv_meas
    hA_meas hA_bdd hv hA F g f hF hg y hy φ t ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with r hr
  have hr' : r ∈ Icc a b := by
    rw [uIoc_of_le ht.1] at hr
    exact ⟨hr.1.le, hr.2.trans ht.2⟩
  rw [plainSpatialTest_projected_integral N D ν K (v r) (hv r hr')
    (fun i i' d => A i i' d r) (hA r hr'), plainForcingTest_projected_integral]
  simp only [coupledTimeRhs, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]
  ring
end

/-! The actual integrated finite spatial equation against the Fourier cutoff
of an arbitrary periodic H¹ test. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Original coefficient and forcing assumptions discharge the finite RHS integrability. -/
theorem plainFourier_projected_integrated_equation (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hv_bdd : ∃ V : ℝ, ∀ s ∈ Icc a b, ∀ x, ‖v s x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hA_meas : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hv : ∀ s ∈ Icc a b, Continuous (v s))
    (hA : ∀ s ∈ Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (f : ∀ i, TorusHk (K i) (h i)) (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b)))
    (y : C(Icc a b, CoupledPlainCoefficients (h := h) N))
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (plainFourierMatrix N D ν K v A s))
      (fun s => plainSourceCoefficients N K (fun i => F i s) (fun i => g i s))
      (plainInitialCoefficients N K f) a b (extendCurve hab y))
    (φ : ∀ i, TorusHk 1 (h i)) (t : ℝ) (ht : t ∈ Icc a b) :
    (∑ i, inner ℝ (torusHkValueCLM (coupledPlainSynthesis N i (K i) (extendCurve hab y t)))
      (torusHkValueCLM (galerkinProj N (φ i)))) -
    (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (galerkinProj N (φ i)))) =
    ∑ i, coupledIntegratedRhs K D ν a t v A F g (plainHigherBochner N K a b hab y) i
      (galerkinProj N (φ i)) := by
  have hid := plainFourier_projected_ambient_weak_equation N D ν ρ hρ K hab v A hv_bdd hv_meas
    hA_meas hA_bdd hv (fun r hr i i' d => (hA r hr i i' d).continuous) F g f hF hg y hy φ t ht
  obtain ⟨B, hB⟩ := hv_bdd
  rw [coupledTimeRhs_array_integral K D ν ρ hρ hab ht v hv_meas hv B hB A hA_bdd
    hA_meas hA F g hF hg (plainHigherBochner N K a b hab y) (fun i => galerkinProj N (φ i))] at hid
  exact hid
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The actual Galerkin differential energy inequality in time. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- The finite measurable Fourier ODE obeys the exact differential energy bound almost everywhere. -/
theorem plainODE_mass_deriv_energy_le (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) initial a b y)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y s)).val)) t +
        ν * massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (y t)).val) ≤
      2 * Real.sqrt (massNormSq ρ π (fun i => (g i t).val)) *
        Real.sqrt (massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y t)).val)) +
        (4 / ν) * massNormSq ρ π (fun i => (F i t).val) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [plainODE_mass_ae_deriv N K ρ π hab
    (plainFourierMatrix N D ν K v A)
    (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) y initial hy hint] with t ht
  intro hmem
  rw [(ht hmem).deriv]
  have hpoint := plainFourierRhs_mass_energy_le N D ν ρ hρ K a b v A hA t hmem
    (hv t hmem) (hvp t hmem) (hC t hmem) (hp t hmem) (y t)
    (fun i => F i t) (fun i => g i t) hν π hπ Kmax hK αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem) hschur
  convert mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
end

/-! Uniform energy bounds for the actual finite Fourier ODE. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (a b : ℝ)
  (v : ℝ → Vec 2 → Vec 2)
  (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (hC : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
  (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk (K i) (h i))

include hρ hA hv hvp hC hp in
/-- The synthesized finite Fourier ODE obeys the exact constants uniformly in the truncation. -/
theorem plainODE_uniform_mass_energy (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (hab : a ≤ b) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (plainFourierMatrix N D ν K v A t))
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y t)).val) +
        (ν / 2) * (∫ s in Set.Icc a b,
          massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i + 1) (y s)).val)) ≤
      2 * massNormSq ρ π (fun i => (coupledPlainSynthesis N i (K i) (y a)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  have hac := plainSynthesis_mass_absolutelyContinuous N K ρ π
    (hy.absolutelyContinuousOnInterval hab hint)
  have hr := (plainSynthesis_massGrad_continuous N K ρ π hycont).intervalIntegrable (μ := volume) a b
  have hf := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (massNormSq_integrable ρ π hπ (fun i => torusJet_memLp (K i) (hF i)))
  have hg' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (massNorm_integrable ρ π hπ (fun i => torusJet_memLp (K i) (memLp_one_iff_integrable.mpr (hg i))))
  have hd := plainODE_mass_deriv_energy_le N D ν ρ hρ K a b v A hA hv hvp hC hp F g
    hν π hπ Kmax hK αv B lam hα hB hlam hsmall hstrain hd hjets hschur hab y initial hy hint
  obtain ⟨S, _, hbound, hclose⟩ := coupledTimeEnergy_uniform_of_deriv_le hab hν hac
    (fun t _ => massNormSq_nonneg ρ π hπ _)
    (fun t _ => massGradNormSq_nonneg ρ π hπ _)
    (fun t _ => Real.sqrt_nonneg _)
    (fun t _ => massNormSq_nonneg ρ π hπ _) hr hg' hf hd
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hclose
  intro t ht
  linarith [hbound t ht]
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Identify the genuine lower-order weak trace of the same finite sequence
by the integrated equation of its common spacetime weak limit. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The actual finite solutions identify every closed-time weak trace against all H¹ tests. -/
theorem plainClosedTrace_integrated_identity (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA_bdd : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hA_meas : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk (K i) (h i))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (y : (n : ℕ) → C(Set.Icc a b, CoupledPlainCoefficients (h := h) (N n)))
    (hy : ∀ n, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun r => plainMatrixCLM (plainFourierMatrix (N n) D ν K v A r))
      (fun r => plainSourceCoefficients (N n) K (fun i => F i r) (fun i => g i r))
      (plainInitialCoefficients (N n) K f) a b (AVenhance.Infra.ODE.extendCurve hab (y n)))
    (U : CoupledHighTime (h := h) K a b) (Q : ℝ)
    (hu : ∀ n, ‖plainHigherBochner (N n) K a b hab (y n)‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainHigherBochner (N n) K a b hab (y n))) atTop (𝓝 (ell U)))
    (V : CoupledLowHilbert (h := h) K) (R : ℝ)
    (hlow : ∀ n, ‖plainLowerSynthesisCLM (N n) K (AVenhance.Infra.ODE.extendCurve hab (y n) t)‖ ≤ R)
    (htrace : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (plainLowerSynthesisCLM (N n) K (AVenhance.Infra.ODE.extendCurve hab (y n) t)))
        atTop (𝓝 (ell V))) (φ : ∀ i, TorusHk 1 (h i)) :
    (∑ i, inner ℝ (coupledLowValueCLM (h := h) K i V) (torusHkValueCLM (φ i))) -
      (∑ i, inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (φ i))) =
      ∑ i, coupledIntegratedRhs K D ν a t v A F g U i (φ i) := by
  let L := fun n => plainLowerSynthesisCLM (N n) K (AVenhance.Infra.ODE.extendCurve hab (y n) t)
  have hleft (i : ι) : Tendsto (fun n => inner ℝ (coupledLowValueCLM (h := h) K i (L n))
      (torusHkValueCLM (galerkinProj (N n) (φ i)))) atTop
      (𝓝 (inner ℝ (coupledLowValueCLM (h := h) K i V) (torusHkValueCLM (φ i)))) := by
    simpa only [L2.inner_def, coupledLowValueCLM_apply] using
      coupledLow_projected_test_weak_limit K i L V R hlow htrace N hN (φ i)
  have hinitial (i : ι) : Tendsto (fun n => inner ℝ (torusHkValueCLM (f i))
      (torusHkValueCLM (galerkinProj (N n) (φ i)))) atTop
      (𝓝 (inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM (φ i)))) := by
    exact ((innerSL ℝ (torusHkValueCLM (f i))).continuous.continuousAt.tendsto).comp
      ((torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
        ((galerkinProj_tendsto (φ i)).comp hN.tendsto_atTop))
  have hlhs := (tendsto_finsetSum Finset.univ (fun i _ => hleft i)).sub
    (tendsto_finsetSum Finset.univ (fun i _ => hinitial i))
  obtain ⟨B, hB⟩ := hv_bdd
  have hrhs := tendsto_finsetSum Finset.univ (fun i _ =>
    coupledIntegratedRhs_projected_weak_limit K D ν ρ hρ hab ht v hv_meas hv B hB A hA_bdd
      hA_meas hA F g hF hg (fun n => plainHigherBochner (N n) K a b hab (y n)) U Q hu hw N hN i (φ i))
  apply tendsto_nhds_unique hlhs
  apply hrhs.congr'
  filter_upwards [] with n
  exact (plainFourier_projected_integrated_equation (N n) D ν ρ hρ K hab v A ⟨B, hB⟩ hv_meas
    hA_meas hA_bdd hv hA F g f hF hg (y n) (hy n) φ t ht).symm

end AVRegularity.CoupledEnergy.Galerkin
end
