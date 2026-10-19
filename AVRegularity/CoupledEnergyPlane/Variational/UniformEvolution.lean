-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.MassDriftEnergy
import AVRegularity.CoupledEnergy.CouplingBounds

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual weak transport products have all lower Sobolev jets in time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakTransportRawValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakTransportRawValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem weakTransportTime_raw_value_ae {a b : ℝ} (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ((planeHkValueOperator (E := h i) (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
        (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
          hV hstrain hB hlam hbv hjets W)) t =ᵐ[volume] fun x => ∑ k : Fin 2,
            v (clampPoint a b hab t) x k • (weakHighCarrier K a b W i t).toFunction.jet
              ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x := by
  have hp := timeReadout_compLp_ae (volume.restrict (Set.Icc a b))
    (planeHkValueOperator (E := h i) (K i))
    (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets)
    W _ (weakTransportTimeCLM_ae hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W)
  filter_upwards [hp] with t ht
  change ((planeHkValueOperator (E := h i) (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
    (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets W)) t = _ at ht
  rw [ht]
  exact planeTransportCarrier_raw_value_ae (hK i) (weakHighCarrier K a b W i t)
    (v (clampPoint a b hab t)) (hv _ (clampPoint a b hab t).property) V hV
    (hbv _ (clampPoint a b hab t).property) strain B lam (hjets _ (clampPoint a b hab t).property)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Actual admissible coupling fluxes of the weak high carrier belong to Sobolev time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakFluxTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakFluxAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakFluxTensorAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

local instance weakFluxTensorTopAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

def weakCoupledFluxTimeCLM {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2)) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
        (volume.restrict (Set.Icc a b)) :=
  (planeCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm).comp
    (weakHighCarrierTimeCLM K a b i')

theorem weakCoupledFluxTimeCLM_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (W : PlaneHighTime (h := h) K a b) :
    weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm W
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
          (clampPoint a b hab t) (clampPoint a b hab t).property
          (hc _ (clampPoint a b hab t).property) (weakHighCarrier K a b W i' t) := by
  have hp := planeCoupledFluxTimeCLM_ae hab ρ hρ K D i i' d A hA hc hAm
    (weakHighCarrierTimeCLM K a b i' W)
  refine hp.trans ?_
  filter_upwards [weakHighCarrierTimeCLM_ae K a b i' W] with t hW
  rw [hW]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Actual admissible coupling fluxes of the weak high carrier belong to Sobolev time L². -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakFluxValueTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakFluxValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakFluxValueTensorAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

local instance weakFluxValueTensorTopAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

theorem weakCoupledFluxTime_value_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) :
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b))
      (weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm W)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeCoefficientOperator (A (clampPoint a b hab t))
          (hc _ (clampPoint a b hab t).property).continuous ENNReal.toReal_nonneg
          (sourceCoefficient_norm_le ρ hρ (K i) a b A hA _ (clampPoint a b hab t).property)
          (highTensorReadout (h := h) K i' (d.1 - 1)
            (by have hh := admissibleOrders_reserve K D i i' d; omega) (W t)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i))
      (weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm W),
    weakCoupledFluxTimeCLM_ae hab ρ hρ K D i i' d A hA hc hAm W,
    weakHighCarrier_jet_ae K a b W hW i'] with t hv hflux hj
  rw [hv, hflux, ← planeCoupledFluxTerm_value]
  simp only [highTensorReadout, sum_apply, ContinuousLinearMap.comp_apply, highJetReadout]
  rw [hj]
  rfl
end

/-! Actual admissible coupling fluxes of the weak high carrier belong to Sobolev time L². -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakRawFluxValueTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakRawFluxValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakRawFluxValueTensorAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

local instance weakRawFluxValueTensorTopAdd (i : ι) (k : ℕ) (J : Type*) [Fintype J] :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : J => h i))) := inferInstance

theorem weakCoupledFluxTime_raw_value_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (W : PlaneHighTime (h := h) K a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b))
        (weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm W)) t =ᵐ[volume]
          fun x => A (clampPoint a b hab t) x (WithLp.toLp 2
            (fun word : DerivativeWord2 (d.1 - 1) =>
              (weakHighCarrier K a b W i' t).toFunction.jet ⟨⟨d.1 - 1, by
                have hh := admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x)) := by
  have hp := timeReadout_compLp_ae (volume.restrict (Set.Icc a b))
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i))
    (weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm) W _
    (weakCoupledFluxTimeCLM_ae hab ρ hρ K D i i' d A hA hc hAm W)
  filter_upwards [hp] with t ht
  change ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b))
    (weakCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm W)) t = _ at ht
  rw [ht]
  exact planeCoupledFluxTerm_raw_value_ae ρ hρ K D a b i i' d A hA
    (clampPoint a b hab t) (clampPoint a b hab t).property
    (hc _ (clampPoint a b hab t).property) (weakHighCarrier K a b W i' t)
end

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedOperator_massEnergy_le (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) :
    (∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i)
        (projectedOperator
          (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u i)).val
      (hilbertBandHk N (K i) (u i)).val) ≤
    -(5 * ν / 8) * massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (u i)).val) := by
  let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA
  let R := massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val)
  let transport (i : ι) := factorialPairing ρ
    (hilbertBandHk N (K i) (hilbertProjection N
      (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t)
        (bandGradientOperator (E := h i) N (u i))))).val
    (hilbertBandHk N (K i) (u i)).val
  let edge (i j : ι) (d : admissibleOrders K D i j) := factorialPairing ρ
    (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
      (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
        (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
        (bandTensorOperator (E := h j) N (d.1 - 1) (u j))))).val
    (hilbertBandHk N (K i) (u i)).val
  have hd : (∑ i, (π i)⁻¹ * |transport i|) ≤ (ν / 4) * R :=
    projectedDrift_massPairing_abs_sum_le K Kmax hK N (fun i => u i) ρ strain B lam ν
      hρ hstrain0 hB hlam hν hsmall hstrain π hπ (v t) (hv t t.property)
      V hV (hbv t t.property) hdiv hjets
  have he : (∑ i, ∑ j, ∑ d : admissibleOrders K D i j,
      (π i)⁻¹ * |edge i j d|) ≤ (ν / 8) * R :=
    projectedCoupling_schurEnergy_abs_sum_le ν ρ hν hρ π hπ K D a b A hA t t.property
      (fun i j d => hC i j d t t.property) hschur
      (fun i j d => (coefficientSeminorm ρ (K i) a b (A i j d)).toReal)
      (fun _ _ _ => ENNReal.toReal_nonneg)
      (fun i j d x => sourceCoefficient_norm_le ρ hρ (K i) a b (A i j d)
        (hA i j d) t t.property x) N (fun i => u i)
  have hr : (∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i) (projectedOperator C N ν t u i)).val
      (hilbertBandHk N (K i) (u i)).val) =
      (∑ i, (π i)⁻¹ * (-transport i)) - ν * R +
        ∑ i, ∑ j, ∑ d : admissibleOrders K D i j, (π i)⁻¹ * edge i j d := by
    simp_rw [projectedOperator_row_energy]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    congr 1
    dsimp [R, massGradNormSq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hds : (∑ i, (π i)⁻¹ * (-transport i)) ≤ ∑ i, (π i)⁻¹ * |transport i| := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) (inv_nonneg.mpr (hπ i).le)
  have hes : (∑ i, ∑ j, ∑ d : admissibleOrders K D i j, (π i)⁻¹ * edge i j d) ≤
      ∑ i, ∑ j, ∑ d : admissibleOrders K D i j, (π i)⁻¹ * |edge i j d| := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro d _
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr (hπ i).le)
  change _ ≤ -(5 * ν / 8) * R
  rw [hr]
  linarith [hds.trans hd, hes.trans he]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
section
/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier

namespace AVRegularity.CoupledEnergyPlane.Variational

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedRhs_massEnergy_le (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    (∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i)
        ((projectedOperator
          (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u +
          projectedSource N (fun i _ => F i) (fun i _ => g i) t) i)).val
      (hilbertBandHk N (K i) (u i)).val) ≤
    -(ν / 2) * massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (u i)).val) +
      Real.sqrt (massNormSq ρ π (fun i => (g i).val)) *
        Real.sqrt (massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val)) +
      (2 / ν) * massNormSq ρ π (fun i => (F i).val) := by
  have ho := sourceProjectedOperator_massEnergy_le K Kmax hK N u ρ strain B lam ν
    hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b v hv V hV hbv t hdiv hjets D A hA hC hschur
  have hf := projectedFlux_massPairing_young_le N K ρ ν hν π hπ F (fun i => u i)
  have hg := projectedSource_massPairing_abs_le N K ρ π hπ g (fun i => u i)
  simp only [WithLp.ofLp_add, Pi.add_apply, projectedSource,
    bandPairing_add, mul_add, Finset.sum_add_distrib]
  linarith [le_abs_self (∑ i, (π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
      (planeHkValueOperator (K i) (F i)))).val (hilbertBandHk N (K i) (u i)).val),
    le_abs_self (∑ i, (π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N (K i) (hilbertProjection N (planeHkValueOperator (K i) (g i)))).val
      (hilbertBandHk N (K i) (u i)).val)]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier

namespace AVRegularity.CoupledEnergyPlane.Variational

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedEnergy_deriv_le_of_hasDerivAt (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ℝ → ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hu : HasDerivAt u
      (projectedOperator
        (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t (u t) +
        projectedSource N (fun i _ => F i) (fun i _ => g i) t) t) :
    deriv (fun s => massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u s i)).val)) t +
      ν * massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u t i)).val) ≤
    2 * Real.sqrt (massNormSq ρ π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u t i)).val)) +
      (4 / ν) * massNormSq ρ π (fun i => (F i).val) := by
  rw [(hasDerivAt_massBandEnergy N K ρ π hπ hu).deriv]
  have he := sourceProjectedRhs_massEnergy_le K Kmax hK N (u t) ρ strain B lam ν
    hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b v hv V hV hbv t hdiv hjets
    D A hA hC hschur F g
  linear_combination 2 * he

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier

namespace AVRegularity.CoupledEnergyPlane.Variational

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedEnergy_uniform_of_timeRegularity (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b) (u : C(Set.Icc a b, ProjectedFamily h))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hac : AbsolutelyContinuousOnInterval (extendCurve hab u) a b)
    (hd : ∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt (extendCurve hab u)
      (projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
          (clampPoint a b hab)) N ν t (extendCurve hab u t) + projectedSource N F g t) t) :
    ∃ S : ℝ, 0 ≤ S ∧
      (∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (K i) (u t i)).val) ≤ S ^ 2) ∧
      S ^ 2 + (ν / 2) * (∫ s in a..b, massGradNormSq ρ π
        (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)) ≤
      2 * massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u ⟨a, le_rfl, hab⟩ i)).val) +
        (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  let E := fun s => massNormSq ρ π
    (fun i => (hilbertBandHk N (K i) (extendCurve hab u s i)).val)
  let R := fun s => massGradNormSq ρ π
    (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)
  let G := fun s => Real.sqrt (massNormSq ρ π (fun i => (g i s).val))
  let Fsq := fun s => massNormSq ρ π (fun i => (F i s).val)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    massBandEnergy_absolutelyContinuous N K ρ π hπ hac
  have hR : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (((continuous_massBandGradient N K ρ π).comp (continuous_extendCurve hab u)).integrableOn_Icc)
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (planeMassNorm_integrable ρ π hπ K g hg)
  have hFsq : IntervalIntegrable Fsq volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (planeMassNormSq_integrable ρ π hπ K F hF)
  have hi : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + ν * R t ≤ 2 * G t * Real.sqrt (E t) + (4 / ν) * Fsq t := by
    have hd' := hd.filter_mono (ae_mono (Measure.restrict_le_self (s := Set.Icc a b)))
    filter_upwards [hd', ae_restrict_mem measurableSet_Icc] with t ht htm
    have hcl : clampPoint a b hab t = ⟨t, htm⟩ := by
      apply Subtype.ext
      simp only [clampPoint, max_eq_right htm.1, min_eq_right htm.2]
    have hp : projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
          (clampPoint a b hab)) N ν t =
      projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA)
        N ν ⟨t, htm⟩ := by
      apply ContinuousLinearMap.ext
      intro z
      apply PiLp.ext
      intro i
      simp only [projectedOperator_component, ProjectedCoefficients.reindex, hcl]
    have hdt := ht htm
    rw [hp] at hdt
    exact sourceProjectedEnergy_deriv_le_of_hasDerivAt K Kmax hK N (extendCurve hab u)
      ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b v hv V hV hbv
      ⟨t, htm⟩ (hdiv t htm) (hjets t htm) D A hA hC hschur
      (fun i => F i t) (fun i => g i t) hdt
  obtain ⟨S, hS, hbnd, he⟩ := coupledTimeEnergy_uniform_of_deriv_le hab hν hE
    (fun _ _ => massNormSq_nonneg ρ π hπ _)
    (fun _ _ => massGradNormSq_nonneg ρ π hπ _)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun _ _ => massNormSq_nonneg ρ π hπ _) hR hG hFsq hi
  refine ⟨S, hS, ?_, ?_⟩
  · intro t
    simpa only [E, extendCurve_eq_of_mem hab u t.property] using hbnd t t.property
  · simpa only [E, R, G, Fsq, extendCurve_eq_of_mem hab u
      (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)] using he

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier

namespace AVRegularity.CoupledEnergyPlane.Variational

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_sourceProjectedEvolution_with_uniformEnergy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) :
    ∃ u : C(Set.Icc a b, ProjectedFamily h),
      (∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator
          ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
            (clampPoint a b hab)) N ν s (extendCurve hab u s) + projectedSource N F g s) ∧
      (∀ t : Set.Icc a b, familyProjection N (u t) = u t) ∧
      ∃ S : ℝ, 0 ≤ S ∧
        (∀ t : Set.Icc a b, massNormSq ρ π
          (fun i => (hilbertBandHk N (K i) (u t i)).val) ≤ S ^ 2) ∧
        S ^ 2 + (ν / 2) * (∫ s in a..b, massGradNormSq ρ π
          (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA
  have hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hC hA hAm
  obtain ⟨u, heq, hrange, hac, hd⟩ :=
    exists_projectedPlaneEvolution_with_timeRegularity hab C hc N ν f F hF g hg
  obtain ⟨S, hS, hbound, henergy⟩ := sourceProjectedEnergy_uniform_of_timeRegularity
    K Kmax hK N ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab u
    v hv V hV hbv hdiv hjets D A hA hC hschur F g hF hg hac hd
  refine ⟨u, heq, hrange, S, hS, hbound, ?_⟩
  have hi : u ⟨a, le_rfl, hab⟩ = projectedInitial N f := by
    simpa only [intervalIntegral.integral_same, add_zero] using heq ⟨a, le_rfl, hab⟩
  rw [hi] at henergy
  have hb := projectedInitial_massNormSq_le N K ρ π hπ f
  linarith

end AVRegularity.CoupledEnergyPlane.Variational
end
end
end
