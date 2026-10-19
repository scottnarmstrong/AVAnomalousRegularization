-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.TorusCoefficientCarrierMeasurable
public import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Actual coupling flux trajectories are time L² under the original
value-level measurability and finite coefficient seminorm assumptions. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusCoupledFlux_trajectory_memLp (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j)
    (T : ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hT : ∀ t, ∀ ht : t ∈ Set.Icc a b,
      T t = torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht
        (hc t ht) (hp t ht) (coupledHighGraphReadout K i' (U t))) :
    MemLp T 2 (volume.restrict (Set.Icc a b)) := by
  have hval : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (T t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        A t x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) (U t) x) := by
    filter_upwards [hU, ae_restrict_mem measurableSet_Icc] with t hu ht
    rw [hT t ht]
    have hv := torusCoupledFluxTerm_value_ae ρ hρ K D a b i i' d A hA t ht (hc t ht)
      (hp t ht) (coupledHighGraphReadout K i' (U t))
    have hx := coupledHighTensorCLM_ae K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d) (U t)
    filter_upwards [hv, hx] with x hvx hxx
    rw [hvx, hu i', hxx]
  have hmeas := torusCoefficientCarrier_aestronglyMeasurable K hab U
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d))
    A hm (fun t ht => (hc t ht).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg
    (fun t ht x => plainCoefficient_norm_le_seminorm ρ hρ (K i) a b A hA t ht x) (K i) T hval
  apply (highTimeGraphReadout_memLp K a b U i').of_le_mul hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [hT t ht]
  exact torusCoupledFluxTerm_norm_le ρ hρ K D a b i i' d A hA t ht (hc t ht) (hp t ht)
    (coupledHighGraphReadout K i' (U t))


theorem torusCoupledFlux_exists_memLp (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j) :
    ∃ T : ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)),
      MemLp T 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b),
        (T t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
          A t x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
            (admissibleOrders_high_readout_bound K D i i' d) (U t) x)) := by
  let T : ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun t =>
    if ht : t ∈ Set.Icc a b then torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht
      (hc t ht) (hp t ht) (coupledHighGraphReadout K i' (U t)) else 0
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) : T t = torusCoupledFluxTerm ρ hρ K D a b i i' d A hA
      t ht (hc t ht) (hp t ht) (coupledHighGraphReadout K i' (U t)) := by
    simp only [T, dite_eq_left ht]
  have hval : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (T t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube] fun x =>
        A t x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) (U t) x) := by
    filter_upwards [hU, ae_restrict_mem measurableSet_Icc] with t hu ht
    rw [he t ht]
    have hv := torusCoupledFluxTerm_value_ae ρ hρ K D a b i i' d A hA t ht (hc t ht)
      (hp t ht) (coupledHighGraphReadout K i' (U t))
    have hx := coupledHighTensorCLM_ae K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d) (U t)
    filter_upwards [hv, hx] with x hvx hxx
    rw [hvx, hu i', hxx]
  have hmeas := torusCoefficientCarrier_aestronglyMeasurable K hab U
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d))
    A hm (fun t ht => (hc t ht).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg
    (fun t ht x => plainCoefficient_norm_le_seminorm ρ hρ (K i) a b A hA t ht x) (K i) T hval
  refine ⟨T, ?_, hval⟩
  apply (highTimeGraphReadout_memLp K a b U i').of_le_mul hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [he t ht]
  exact torusCoupledFluxTerm_norm_le ρ hρ K D a b i i' d A hA t ht (hc t ht) (hp t ht)
    (coupledHighGraphReadout K i' (U t))

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The native component equation is the integral of a genuinely
integrable spatial scalar form at every time in the closed interval. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusRawSpatialRhs_integrable_and_integral (K : ι → ℕ) (D : ℕ)
    (ν ρ : ℝ) (hρ : 0 < ρ) (a b r : ℝ) (hr : r ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (v r))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ x, ‖v r x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d, Continuous (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) :
    Integrable (torusRawSpatialRhs K D ν r v A F g w i φ) (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, torusRawSpatialRhs K D ν r v A F g w i φ x) =
      coupledTimeRhs K D ν r v A F g (coupledCarrierHighJets K w) i φ := by
  have hn := torusNativeSpatialRhs_integrable_and_integral K D ν ρ hρ a b r hr v hv V hV hb
    A hA hc F g (coupledCarrierHighJets K w) i φ
  have he := torusRawSpatialRhs_ae_native K D ν r v A F g w i φ
  exact ⟨hn.1.congr he.symm, (integral_congr_ae he).trans hn.2⟩

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Actual coupling flux trajectories are time L² under the original
value-level measurability and finite coefficient seminorm assumptions. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusCoupledFlux_family_exists_memLp (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hAp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j) :
    ∃ C : ∀ i i', admissibleOrders K D i i' → ℝ →
        TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)),
      (∀ i i' d, MemLp (C i i' d) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i i' d,
        (C i i' d t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => A i i' d t x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
            (admissibleOrders_high_readout_bound K D i i' d) (U t) x)) := by
  have hex (i i' : ι) (d : admissibleOrders K D i i') := torusCoupledFlux_exists_memLp K D hab
    ρ hρ i i' d (A i i' d) (hA i i' d) (hAm i i' d)
    (fun t ht => hAc t ht i i' d) (fun t ht => hAp t ht i i' d) U hU
  choose C hCLp hCval using hex
  exact ⟨C, hCLp, ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun i' => ae_all_iff.mpr (hCval i i')))⟩

theorem torusCoupledTotalFlux_memLp (K : ι → ℕ) (D : ℕ) (a b ν : ℝ)
    (G F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i i', admissibleOrders K D i i' → ℝ →
      TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict (Set.Icc a b)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hC : ∀ i i' d, MemLp (C i i' d) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (fun t => ν • G i t + (∑ i', ∑ d, C i i' d t) + F i t)
      2 (volume.restrict (Set.Icc a b)) := by
  have hs : MemLp (fun t => ∑ i', ∑ d, C i i' d t) 2 (volume.restrict (Set.Icc a b)) := by
    exact memLp_finsetSum Finset.univ (f := fun i' t => ∑ d, C i i' d t)
      (fun i' _ => memLp_finsetSum Finset.univ (f := fun d t => C i i' d t)
        (fun d _ => hC i i' d))
  simpa only [Pi.add_apply, Pi.smul_apply] using! ((hG i).const_smul ν |>.add hs).add (hF i)

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusRawSpatialRhs_time_ae_native (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighTime (h := h) K a b)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hW : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (w i r).val = U r i)
    (i : ι) (φ : TorusHk 1 (h i)) :
    (fun r => ∫ x in AVenhance.unitCube, torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x) =ᵐ[
      volume.restrict (Set.Icc a b)] fun r => coupledTimeRhs K D ν r v A F g (U r) i φ := by
  have hB : 0 ≤ B := (norm_nonneg (v a 0)).trans (hvb a ⟨le_rfl, hab⟩ 0)
  filter_upwards [hW, ae_restrict_mem measurableSet_Icc] with r hr hri
  have hn := (torusRawSpatialRhs_integrable_and_integral K D ν ρ hρ a b r hri v (hvc r hri)
    B hB (hvb r hri) A hA (fun i i' d => (hAc r hri i i' d).continuous) F g (fun i => w i r) i φ).2
  have he : coupledCarrierHighJets K (fun i => w i r) = U r := PiLp.ext hr
  rw [he] at hn
  exact hn
end

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusRawSpatialRhs_time_integrable_and_integral (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hW : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (w i r).val = U r i)
    (i : ι) (φ : TorusHk 1 (h i)) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x) (volume.restrict (Set.Icc a b)) ∧
    (∀ t ∈ Set.Icc a b, (∫ r in Set.Ioc a t, ∫ x in AVenhance.unitCube,
      torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x) =
        coupledIntegratedRhs K D ν a t v A F g U i φ) := by
  have he := torusRawSpatialRhs_time_ae_native K D ν ρ hρ hab v hvc B hvb A hA hAc F g U w hW i φ
  have hn := coupledTimeRhs_integrable K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc F g hF hg U i φ
  refine ⟨hn.congr he.symm, ?_⟩
  intro t ht
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hs he)]
  rw [← intervalIntegral.integral_of_le ht.1]
  exact coupledTimeRhs_integral K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc F g hF hg U i φ
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! The literal diffusion and coupling flux on arbitrary weak carriers.
Its finite synthesis and subtraction identities are exact. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (a b : ℝ)
  (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hc : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))

def torusSpatialFluxCarrier (w : ∀ i, TorusHk (K i + 1) (h i))
    (i : ι) : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ν • torusGradientTensor (w i) + ∑ i', ∑ d : admissibleOrders K D i i',
    torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht
      (hc i i' d) (hp i i' d) (w i')

omit [DecidableEq ι] in
theorem torusSpatialFluxCarrier_sub (w z : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) :
    torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp (fun j => w j - z j) i =
      torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp w i -
        torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp z i := by
  unfold torusSpatialFluxCarrier
  simp only [torusGradientTensor_sub, torusCoupledFluxTerm_sub, smul_sub,
    Finset.sum_sub_distrib]
  abel

theorem torusSpatialFluxCarrier_synthesis (N : ℕ) (c : CoupledPlainCoefficients (h := h) N) (i : ι) :
    torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp
      (fun j => coupledPlainSynthesis N j (K j + 1) c) i =
        plainSpatialFlux N D ν ρ hρ K a b A hA t ht hc hp c i := by
  simp only [torusSpatialFluxCarrier, plainSpatialFlux, plainCouplingFlux,
    coupledPlainGradientHk_eq_gradientTensor]

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusNativeEquation_implies_rawWeakIdentity (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hW : ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i, (w i r).val = U r i)
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hid : ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (Galerkin.torusHkValueCLM (u i t)) (Galerkin.torusHkValueCLM φ) -
        inner ℝ (Galerkin.torusHkValueCLM (f i)) (Galerkin.torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g U i φ) :
    ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
        ((u i t).toFunction.jet (valueIndex2 (K i)))
        ((f i).toFunction.jet (valueIndex2 (K i))) (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
        (fun r k => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
        (fun r => torusRawCouplingFlux K D r A (fun i => w i r) i)
        (fun r => (F i r).toFunction.jet (valueIndex2 (K i)))
        (fun r => (g i r).toFunction.jet (valueIndex2 (K i))) := by
  intro i t ht φ
  have hleft := torusRawValue_pairing_integrable_and_integral (u i t) φ
  have hinit := torusRawValue_pairing_integrable_and_integral (f i) φ
  have htime := torusRawSpatialRhs_time_integrable_and_integral K D ν ρ hρ hab v hv hvc B hvb
    A hA hAm hAc F g hF hg U w hW i φ
  have hB : 0 ≤ B := (norm_nonneg (v a 0)).trans (hvb a ⟨le_rfl, hab⟩ 0)
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  change Integrable (fun x => inner ℝ ((u i t).toFunction.jet (valueIndex2 (K i)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) (volume.restrict AVenhance.unitCube) ∧
    Integrable (fun x => inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) (volume.restrict AVenhance.unitCube) ∧
    (∀ r ∈ Set.Ioc a t, Integrable (torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ)
      (volume.restrict AVenhance.unitCube)) ∧
    IntegrableOn (fun r => ∫ x in AVenhance.unitCube,
      torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x) (Set.Ioc a t) ∧
    (∫ x in AVenhance.unitCube, inner ℝ ((u i t).toFunction.jet (valueIndex2 (K i)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) -
      (∫ x in AVenhance.unitCube, inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
        (φ.toFunction.jet (valueIndex2 1) x)) =
      ∫ r in Set.Ioc a t, ∫ x in AVenhance.unitCube,
        torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x
  refine ⟨hleft.1, hinit.1, ?_, IntegrableOn.mono_set htime.1 hs, ?_⟩
  · intro r hr
    exact (torusRawSpatialRhs_integrable_and_integral K D ν ρ hρ a b r (hs hr) v (hvc r (hs hr))
      B hB (hvb r (hs hr)) A hA (fun i i' d => (hAc r (hs hr) i i' d).continuous)
      F g (fun i => w i r) i φ).1
  · rw [hleft.2, hinit.2, htime.2 t ht]
    exact hid i t ht φ

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Time L² membership of the literal coupling carrier of an arbitrary
higher Sobolev trajectory; no weak-limit origin is required. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (a b ρ : ℝ) (hρ : 0 < ρ)
    (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))

def torusCoupledFluxPath (w : ∀ j, ℝ → TorusHk (K j + 1) (h j)) :
    ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun t =>
  if ht : t ∈ Set.Icc a b then
    torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht (hc t ht) (hp t ht) (w i' t)
  else 0

theorem torusCoupledFluxPath_memLp (hab : a ≤ b)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (w : ∀ j, ℝ → TorusHk (K j + 1) (h j))
    (hw : ∀ j, MemLp (w j) 2 (volume.restrict (Set.Icc a b))) :
    MemLp (torusCoupledFluxPath K D a b ρ hρ i i' d A hA hc hp w)
      2 (volume.restrict (Set.Icc a b)) := by
  let U := coupledCarrierHighTime K a b w hw
  let W : ∀ j, ℝ → TorusHk (K j + 1) (h j) := fun j t => coupledHighGraphReadout K j (U t)
  have he := coupledCarrierHighTime_graphReadout_ae K a b w hw
  have hu : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j := by
    filter_upwards [he, coupledCarrierHighTime_ae K a b w hw] with t ht hv
    intro j
    rw [ht j]
    exact hv j
  have hLp := torusCoupledFlux_trajectory_memLp K D hab ρ hρ i i' d A hA hm hc hp U hu
    (torusCoupledFluxPath K D a b ρ hρ i i' d A hA hc hp W)
    (by intro t ht; simp only [torusCoupledFluxPath, dite_eq_left ht, W])
  have heq : torusCoupledFluxPath K D a b ρ hρ i i' d A hA hc hp W =ᵐ[
      volume.restrict (Set.Icc a b)] torusCoupledFluxPath K D a b ρ hρ i i' d A hA hc hp w := by
    filter_upwards [he] with t ht
    unfold torusCoupledFluxPath
    split_ifs with hti
    · rw [show W i' t = w i' t from ht i']
    · rfl
  exact (memLp_congr_ae heq).mp hLp

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusRawWeakSolution_nativeEquation (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w) :
    let U := coupledCarrierHighTime K a b w hsol.2.1
    ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (Galerkin.torusHkValueCLM (u i t)) (Galerkin.torusHkValueCLM φ) -
        inner ℝ (Galerkin.torusHkValueCLM (f i)) (Galerkin.torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g U i φ := by
  dsimp only
  intro i t ht φ
  let U := coupledCarrierHighTime K a b w hsol.2.1
  have htRaw := torusRawSpatialRhs_time_integrable_and_integral K D ν ρ hρ hab v hv hvc B hvb
    A hA hAm hAc F g hF hg U w (coupledCarrierHighTime_ae K a b w hsol.2.1) i φ
  have hleft := torusRawValue_pairing_integrable_and_integral (u i t) φ
  have hinit := torusRawValue_pairing_integrable_and_integral (f i) φ
  have he := (hsol.2.2.2.2 i t ht φ).2.2.2.2
  change (∫ x in AVenhance.unitCube, inner ℝ ((u i t).toFunction.jet (valueIndex2 (K i)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) -
    (∫ x in AVenhance.unitCube, inner ℝ ((f i).toFunction.jet (valueIndex2 (K i)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) =
    (∫ r in Set.Ioc a t, ∫ x in AVenhance.unitCube,
      torusRawSpatialRhs K D ν r v A F g (fun i => w i r) i φ x) at he
  rw [hleft.2, hinit.2, htRaw.2 t ht] at he
  exact he

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Uniform Sobolev graph bounds for the actual combined spatial flux. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (a b : ℝ)
  (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (t : ℝ) (ht : t ∈ Set.Icc a b)
  (hc : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))

omit [DecidableEq ι] in
theorem torusSpatialFluxCarrier_norm_le (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) :
    ‖torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht hc hp w i‖ ≤
      (|ν| * ‖torusGradientTensorCLM (E := h i) (K i)‖ +
        ∑ i', ∑ d : admissibleOrders K D i i',
          (((coefficientSeminorm ρ (K i) a b (A i i' d)).toReal *
            derivativeReserveFactor ρ (K i) (d.1 - 2)) *
            Real.sqrt (factorialWeightMax ρ (K i')) / Real.sqrt (factorialWeightMin ρ (K i)))) * ‖w‖ := by
  let L := fun i' (d : admissibleOrders K D i i') =>
    (((coefficientSeminorm ρ (K i) a b (A i i' d)).toReal *
      derivativeReserveFactor ρ (K i) (d.1 - 2)) *
      Real.sqrt (factorialWeightMax ρ (K i')) / Real.sqrt (factorialWeightMin ρ (K i)))
  have hL (i' : ι) (d : admissibleOrders K D i i') : 0 ≤ L i' d := by
    unfold L derivativeReserveFactor
    positivity
  have hg : ‖ν • torusGradientTensor (w i)‖ ≤
      (|ν| * ‖torusGradientTensorCLM (E := h i) (K i)‖) * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hn := (torusGradientTensorCLM (E := h i) (K i)).le_opNorm (w i)
    rw [torusGradientTensorCLM_apply] at hn
    calc
      _ ≤ |ν| * (‖torusGradientTensorCLM (E := h i) (K i)‖ * ‖w i‖) :=
        mul_le_mul_of_nonneg_left hn (abs_nonneg _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w i) (by positivity)
  have hb : ‖∑ i', ∑ d : admissibleOrders K D i i',
      torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht
        (hc i i' d) (hp i i' d) (w i')‖ ≤ (∑ i', ∑ d, L i' d) * ‖w‖ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i' _
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    exact (torusCoupledFluxTerm_norm_le ρ hρ K D a b i i' d (A i i' d) (hA i i' d)
      t ht (hc i i' d) (hp i i' d) (w i')).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm w i') (hL i' d))
  exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add hg hb)

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The native homogeneous equation of the difference of two weak
solutions with the same original forcing and initial data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusWeakSolution_difference_nativeEquation (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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

    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F g u' w')
    (hd : ∀ i, MemLp (fun t => w i t - w' i t) 2 (volume.restrict (Set.Icc a b))) :
    let U := coupledCarrierHighTime K a b (fun i t => w i t - w' i t) hd
    ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (Galerkin.torusHkValueCLM (u i t - u' i t)) (Galerkin.torusHkValueCLM φ) -
        inner ℝ (Galerkin.torusHkValueCLM (0 : TorusHk (K i) (h i))) (Galerkin.torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A (fun _ _ => 0) (fun _ _ => 0) U i φ := by
  dsimp only
  have hnative := torusRawWeakSolution_nativeEquation K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    F g hF hg w u f hsol
  have hnative' := torusRawWeakSolution_nativeEquation K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    F g hF hg w' u' f hsol'
  intro i t ht φ
  rw [coupledCarrierHighTime_sub K a b w w' hsol.2.1 hsol'.2.1 hd]
  rw [coupledIntegratedRhs_sub_same_forcing K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc
    F g (coupledCarrierHighTime K a b w hsol.2.1) (coupledCarrierHighTime K a b w' hsol'.2.1) i φ]
  simp only [map_sub, map_zero, inner_sub_left, inner_zero_left, sub_zero]
  linarith [hnative i t ht φ, hnative' i t ht φ]
end

/-! The native homogeneous equation of the difference of two weak
solutions with the same original forcing and initial data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusNativeEquation_pack_weakSolution (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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


    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hcont : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (halign : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.le_succ (K i)) (w i t) = u i t)
    (hinit : ∀ i, u i a = f i)
    (hid : ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (Galerkin.torusHkValueCLM (u i t)) (Galerkin.torusHkValueCLM φ) -
        inner ℝ (Galerkin.torusHkValueCLM (f i)) (Galerkin.torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A F g (coupledCarrierHighTime K a b w hw) i φ) :
    IsCoupledWeakSolutionTorus ν a b v D K A f F g u w := by
  have hraw := torusNativeEquation_implies_rawWeakIdentity K D ν ρ hρ hab v hv hvc B hvb
    A hA hAm hAc F g hF hg (coupledCarrierHighTime K a b w hw) w
    (coupledCarrierHighTime_ae K a b w hw) u f hid
  refine ⟨hcont, hw, halign, hinit, ?_⟩
  intro i t ht φ
  simpa only [torusRawCouplingFlux] using! hraw i t ht φ
end

/-! The native homogeneous equation of the difference of two weak
solutions with the same original forcing and initial data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusWeakSolution_difference (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
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

    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F g u' w')
 :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun i t => u i t - u' i t) (fun i t => w i t - w' i t) := by
  have hd : ∀ i, MemLp (fun t => w i t - w' i t) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_pointwise_sub (volume.restrict (Set.Icc a b)) 2 (w i) (w' i)
      (hsol.2.1 i) (hsol'.2.1 i)
  have hid := torusWeakSolution_difference_nativeEquation K D ν ρ hρ hab v hv hvc B hvb
    A hA hAm hAc F g hF hg w w' u u' f hsol hsol' hd
  have hF0 : ∀ i, MemLp (fun _ : ℝ => (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))))
      2 (volume.restrict (Set.Icc a b)) := fun i => timeMemLp_zero (E := TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
        (volume.restrict (Set.Icc a b)) 2
  have hg0 : ∀ i, Integrable (fun _ : ℝ => (0 : TorusHk (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := fun i => timeIntegrable_zero (E := TorusHk (K i) (h i)) (volume.restrict (Set.Icc a b))
  have hcont : ∀ i, ContinuousOn (fun t => u i t - u' i t) (Set.Icc a b) :=
    fun i => timeContinuousOn_pointwise_sub (u i) (u' i) (Set.Icc a b) (hsol.1 i) (hsol'.1 i)
  apply torusNativeEquation_pack_weakSolution (h := h) K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    (fun _ _ => 0) (fun _ _ => 0) hF0 hg0
    (fun i t => w i t - w' i t) (fun i t => u i t - u' i t) (fun _ => 0)
    hcont hd
  · intro i
    filter_upwards [hsol.2.2.1 i, hsol'.2.2.1 i] with t ht ht'
    rw [(truncateTorusHk (E := h i) (Nat.le_succ (K i))).map_sub, ht, ht']
  · intro i
    rw [hsol.2.2.2.1 i, hsol'.2.2.2.1 i, sub_self]
  · exact hid
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Literal combined spatial-flux trajectories and their vanishing Fourier
residuals, on arbitrary time L² Sobolev fields. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (a b ν ρ : ℝ) (hρ : 0 < ρ)
  (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
  (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
  (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
  (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))

def torusSpatialFluxPath (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)) :
    ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun i t =>
  ν • torusGradientTensor (w i t) + ∑ i', ∑ d : admissibleOrders K D i i',
    torusCoupledFluxPath K D a b ρ hρ i i' d (A i i' d) (hA i i' d)
      (fun s hs => hc s hs i i' d) (fun s hs => hp s hs i i' d) w t

theorem torusSpatialFluxPath_of_mem (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
    torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp w i t =
      torusSpatialFluxCarrier K D ν ρ hρ a b A hA t ht (hc t ht) (hp t ht) (fun j => w j t) i := by
  simp only [torusSpatialFluxPath, torusSpatialFluxCarrier, torusCoupledFluxPath, dite_eq_left ht]

theorem torusSpatialFluxPath_memLp (hab : a ≤ b)
    (hm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp w i)
      2 (volume.restrict (Set.Icc a b)) := by
  have hg := (torusGradientTensor_carrier_memLp (K i) a b (w i) (hw i)).const_smul ν
  have hb : MemLp (fun t => ∑ i', ∑ d : admissibleOrders K D i i',
      torusCoupledFluxPath K D a b ρ hρ i i' d (A i i' d) (hA i i' d)
        (fun s hs => hc s hs i i' d) (fun s hs => hp s hs i i' d) w t)
      2 (volume.restrict (Set.Icc a b)) := by
    apply memLp_finsetSum Finset.univ (f := fun i' t => ∑ d : admissibleOrders K D i i',
      torusCoupledFluxPath K D a b ρ hρ i i' d (A i i' d) (hA i i' d)
        (fun s hs => hc s hs i i' d) (fun s hs => hp s hs i i' d) w t)
    intro i' _
    apply memLp_finsetSum Finset.univ (f := fun d t =>
      torusCoupledFluxPath K D a b ρ hρ i i' d (A i i' d) (hA i i' d)
        (fun s hs => hc s hs i i' d) (fun s hs => hp s hs i i' d) w t)
    intro d _
    exact torusCoupledFluxPath_memLp K D a b ρ hρ i i' d (A i i' d) (hA i i' d)
      (fun s hs => hc s hs i i' d) (fun s hs => hp s hs i i' d) hab (hm i i' d) w hw
  simpa only [torusSpatialFluxPath, Pi.add_apply, Pi.smul_apply] using! hg.add hb


theorem torusForcedSpatialFluxPath_memLp (hab : a ≤ b)
    (hm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (fun t => F i t + torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp w i t)
      2 (volume.restrict (Set.Icc a b)) := by
  have hs := torusSpatialFluxPath_memLp K D a b ν ρ hρ A hA hc hp hab hm w hw i
  exact timeMemLp_pointwise_add (E := TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (volume.restrict (Set.Icc a b)) 2 (F i)
    (torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp w i) (hF i) hs

theorem torusSpatialFluxPath_tail_square_tendsto (hab : a ≤ b)
    (hm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (w : ∀ j, ℝ → TorusHk (K j + 1) (h j))
    (hw : ∀ j, MemLp (w j) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    Filter.Tendsto (fun N => ∫ t in Set.Icc a b,
      ‖torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp
        (fun j s => w j s - galerkinProj N (w j s)) i t‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have htLp (N : ℕ) (j : ι) : MemLp (fun s => w j s - galerkinProj N (w j s))
      2 (volume.restrict (Set.Icc a b)) := by
    simpa only [Pi.sub_apply, Function.comp_def] using!
      (hw j).sub ((galerkinProj N).comp_memLp' (hw j))
  let L := |ν| * ‖torusGradientTensorCLM (E := h i) (K i)‖ +
    ∑ i', ∑ d : admissibleOrders K D i i',
      (((coefficientSeminorm ρ (K i) a b (A i i' d)).toReal *
        derivativeReserveFactor ρ (K i) (d.1 - 2)) *
        Real.sqrt (factorialWeightMax ρ (K i')) / Real.sqrt (factorialWeightMin ρ (K i)))
  let P : ℕ → (∀ j, TorusHk (K j + 1) (h j)) →L[ℝ] (∀ j, TorusHk (K j + 1) (h j)) :=
    carrierFamilyProjection (h := h) (fun j => K j + 1)
  let u0 : ℝ → (∀ j, TorusHk (K j + 1) (h j)) := fun t j => w j t
  let R : ℕ → ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) := fun N =>
    torusSpatialFluxPath K D a b ν ρ hρ A hA hc hp (fun j s => w j s - galerkinProj N (w j s)) i
  have hu0 : MemLp u0 2 (volume.restrict (Set.Icc a b)) := memLp_pi_iff.mpr hw
  have hR (N : ℕ) : MemLp (R N) 2 (volume.restrict (Set.Icc a b)) :=
    torusSpatialFluxPath_memLp K D a b ν ρ hρ A hA hc hp hab hm _ (htLp N) i
  have hb : ∀ N, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖R N t‖ ≤ L * ‖P N (u0 t) - u0 t‖ := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [R]
    rw [torusSpatialFluxPath_of_mem K D a b ν ρ hρ A hA hc hp _ t ht i]
    have hn := torusSpatialFluxCarrier_norm_le K D ν ρ hρ a b A hA t ht (hc t ht) (hp t ht)
      (fun j => w j t - galerkinProj N (w j t)) i
    have he : ‖(fun j => w j t - galerkinProj N (w j t))‖ = ‖P N (u0 t) - u0 t‖ := by
      change ‖u0 t - P N (u0 t)‖ = _
      exact norm_sub_rev _ _
    calc
      _ ≤ L * ‖(fun j => w j t - galerkinProj N (w j t))‖ := by
        simpa only [L] using! hn
      _ = _ := congrArg (fun x => L * x) he
  exact boundedResidual_integral_square_tendsto (volume.restrict (Set.Icc a b)) P
    (carrierFamilyProjection_norm_le (h := h) (fun j => K j + 1))
    (carrierFamilyProjection_tendsto (h := h) (fun j => K j + 1)) u0 hu0 R hR L hb

end AVRegularity.CoupledEnergy.Variational
end
