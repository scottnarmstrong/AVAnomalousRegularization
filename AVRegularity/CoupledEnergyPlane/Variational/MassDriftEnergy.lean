-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.ResidualValueSource
import AVRegularity.CoupledEnergyPlane.Fourier.SobolevBandSourcePairing
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
import AVRegularity.CoupledEnergy.Variational.PullbackForm

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The velocity bounds of `coupled_energy_plane` supply the complete interval Sobolev transport
operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance residualValueReadoutAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance residualValueReadoutTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem planeResidualValueSource_readout_ae {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ K E) (N : ℕ)
    (q : ℝ → PlaneHk Set.univ (K + 1) E)
    (hU : (U : ℝ → PlaneHk Set.univ (K + 1) E) =ᵐ[volume.restrict (Set.Icc a b)] q) :
    planeResidualValueSource hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U g N
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => g t -
        planeTransportCarrier hK (v (clampPoint a b hab t))
          (hv _ (clampPoint a b hab t).property) V (hbv _ (clampPoint a b hab t).property)
          strain B lam (hjets _ (clampPoint a b hab t).property)
          (q t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K + 1) (q t)) := by
  have he := planeResidualValueSource_ae hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U g N
  filter_upwards [he, hU] with t ht hu
  simpa only [hu] using ht

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal admissible coupling is a bounded operator on genuine Sobolev time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coupledFluxNormed (i : ι) (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance coupledFluxAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance coupledFluxTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

def planeCoupledFluxTimeCLM {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2)) :
    Lp (PlaneHk Set.univ (K i' + 1) (h i')) 2 (volume.restrict (Set.Icc a b)) →L[ℝ]
      Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
        (volume.restrict (Set.Icc a b)) :=
  (intervalProductTimeCLM hab ρ hρ (K i) A hA hc hAm).comp
    ((planePositiveDerivativeTensorOperator (E := h i') (d.1 - 1)
      (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2).compLpL 2
        (volume.restrict (Set.Icc a b)))

omit [Fintype ι] in
theorem planeCoupledFluxTimeCLM_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (U : Lp (PlaneHk Set.univ (K i' + 1) (h i')) 2 (volume.restrict (Set.Icc a b))) :
    planeCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm U
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
          (clampPoint a b hab t) (clampPoint a b hab t).property
          (hc _ (clampPoint a b hab t).property) (U t) := by
  let L := planePositiveDerivativeTensorOperator (E := h i') (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2
  have hp := intervalProductTimeCLM_ae hab ρ hρ (K i) A hA hc hAm
    (L.compLpL 2 (volume.restrict (Set.Icc a b)) U)
  filter_upwards [hp, ContinuousLinearMap.coeFn_compLpL L U] with t ht hL
  change (intervalProductTimeCLM hab ρ hρ (K i) A hA hc hAm
    (L.compLpL 2 (volume.restrict (Set.Icc a b)) U)) t = _
  rw [ht, hL]
  dsimp only [L]
  rw [planePositiveDerivativeTensorOperator_apply]
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The constructed plane transport carrier is the exact mask expansion at every Galerkin jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_jet_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (p : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    (planeTransportCarrier hK v hv V hbv a B lam hjets p).val α =ᵐ[volume]
      multiplicationRawJet (driftFiberCoefficient v) (planeGradientTensor p).toFunction.jet α := by
  have he : (planeTransportCarrier hK v hv V hbv a B lam hjets p).val α =ᵐ[
      volume.restrict Set.univ]
      multiplicationRawJet (driftFiberCoefficient v) (planeGradientTensor p).toFunction.jet α := by
    unfold planeTransportCarrier PlaneHk.mulCoefficient
    exact jetToL2_ae _ _ α
  simpa only [Measure.restrict_univ] using he

theorem planeTransportCarrier_band_jet_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) (α : JetIndex2 K) :
    (planeTransportCarrier hK v hv V hbv a B lam hjets
      (hilbertBandHk N (K + 1) u)).val α =ᵐ[volume]
      fun x => ∑ m : PositionMask α.1.val,
        driftMaskTerm (Nat.le_of_lt_succ α.1.isLt) v
          (hilbertBandHk N (K + 1) u).toFunction.jet m α.2 x :=
  (planeTransportCarrier_jet_ae hK v hv V hbv a B lam hjets _ α).trans
    (bandDrift_multiplicationRawJet_ae N K u v hv α)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal admissible coupling is a bounded operator on genuine Sobolev time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance residualCoupledFluxNormed (i : ι) (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance residualCoupledFluxAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance residualCoupledFluxTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

omit [Fintype ι] in
theorem planeCoupledFluxTimeCLM_residual_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (U : Lp (PlaneHk Set.univ (K i' + 1) (h i')) 2 (volume.restrict (Set.Icc a b))) (N : ℕ) :
    planeCoupledFluxTimeCLM hab ρ hρ K D i i' d A hA hc hAm
      (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K i' + 1) U)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeCoupledFluxTerm ρ hρ K D a b i i' d A hA
          (clampPoint a b hab t) (clampPoint a b hab t).property
          (hc _ (clampPoint a b hab t).property)
          (U t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K i' + 1) (U t)) := by
  have hp := planeCoupledFluxTimeCLM_ae hab ρ hρ K D i i' d A hA hc hAm
    (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K i' + 1) U)
  filter_upwards [hp, planeSobolevTimeResidual_ae (volume.restrict (Set.Icc a b)) N (K i' + 1) U]
    with t ht hr
  rw [ht, hr]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Schur absorption for the actual differentiated coupling fluxes. -/

open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedCoupling_schurEnergy_abs_sum_le (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (M : ∀ i i' (_d : admissibleOrders K D i i'), ℝ)
    (hM : ∀ i i' d, 0 ≤ M i i' d)
    (hb : ∀ i i' d x, ‖A i i' d t x‖ ≤ M i i' d)
    (N : ℕ) (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2))) :
    (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', (π i)⁻¹ * |factorialPairing ρ
      (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
        (planeCoefficientOperator (A i i' d t) (hC i i' d).continuous
          (hM i i' d) (hb i i' d)
          (bandTensorOperator (E := h i') N (d.1 - 1) (u i'))))).val
      (hilbertBandHk N (K i) (u i)).val|) ≤
      (ν / 8) * massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val) := by
  have he (i i' : ι) (d : admissibleOrders K D i i') :=
    projectedCoupling_factorialPairing ρ hρ K D a b i i' d (A i i' d)
      (hA i i' d) t ht (hC i i' d) (M i i' d) (hM i i' d) (hb i i' d) N (u i') (u i)
  simp_rw [he, abs_neg, factorialPairing_eq_weighted_inner]
  exact planeCoupledFlux_schurEnergy_abs_sum_le ν ρ hν hρ π hπ K D a b A hA t ht hC
    hschur (fun i => hilbertBandHk N (K i + 1) (u i))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Read the genuine Sobolev source primitive in the ambient spatial value space. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeBandSobolevRhs_value (N K : ℕ)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : ℝ → PlaneHk Set.univ K E) (t : ℝ) :
    planeHkValueOperator (E := E) K (planeBandSobolevRhs N K S H t) =
      bandDivergenceOperator (E := E) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (S t)) +
      hilbertProjection (E := E) N (planeHkValueOperator (E := E) K (H t)) := by
  rw [planeBandSobolevRhs, map_add]
  change planeHkValueOperator (E := E) K
      (hilbertBandHk N K (bandDivergenceOperator (E := E) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (S t)))) +
    planeHkValueOperator (E := E) K (hilbertBandHk N K (planeHkValueOperator (E := E) K (H t))) = _
  simp only [planeHkValueOperator_apply, hilbertBandHk_value,
    AVRegularity.Analysis.Convolution.univToPlane_planeToUniv, hilbertProjection_divergence]

theorem planeBandSobolevRhs_value_of_carrier_fields (N K : ℕ) (ν : ℝ)
    (w : PlaneHk Set.univ (K + 1) E) (T g : PlaneHk Set.univ K E)
    (C F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    planeHkValueOperator (E := E) K
      (planeBandSobolevRhs N K (fun _ => ν • planeGradientTensor w + C + F) (fun _ => g - T) 0) =
      -hilbertProjection (E := E) N (planeHkValueOperator (E := E) K T) +
      ν • bandLaplacianOperator (E := E) N (planeHkValueOperator (E := E) (K + 1) w) +
      bandDivergenceOperator (E := E) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (C + F)) +
      hilbertProjection (E := E) N (planeHkValueOperator (E := E) K g) := by
  rw [planeBandSobolevRhs_value, bandLaplacian_planeHk_eq_divergence]
  simp only [map_add, map_sub, map_smul]
  abel
end

/-! Conditional conversion of actual Sobolev source fields to their projected value row. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandCarrierFields_rhs_ae (μ : Measure ℝ) (N K : ℕ) (ν : ℝ)
    (R : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hrange : ∀ t, hilbertProjection (E := E) N (R t) = R t)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : ℝ → PlaneHk Set.univ K E)
    (w : ℝ → PlaneHk Set.univ (K + 1) E) (T g : ℝ → PlaneHk Set.univ K E)
    (C F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hrhs : (fun t => hilbertBandHkOperator N K (R t)) =ᵐ[μ] planeBandSobolevRhs N K S H)
    (hs : S =ᵐ[μ] fun t => ν • planeGradientTensor (w t) + C t + F t)
    (hh : H =ᵐ[μ] fun t => g t - T t) :
    R =ᵐ[μ] fun t => -hilbertProjection (E := E) N (planeHkValueOperator (E := E) K (T t)) +
      ν • bandLaplacianOperator (E := E) N (planeHkValueOperator (E := E) (K + 1) (w t)) +
      bandDivergenceOperator (E := E) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (C t + F t)) +
      hilbertProjection (E := E) N (planeHkValueOperator (E := E) K (g t)) := by
  filter_upwards [hrhs, hs, hh] with t hr hs' hh'
  have he := congrArg (planeHkValueOperator (E := E) K) hr
  rw [planeHkValueOperator_hilbertBand, hrange, planeBandSobolevRhs_value, hs', hh'] at he
  have hf := planeBandSobolevRhs_value_of_carrier_fields N K ν (w t) (T t) (g t) (C t) (F t)
  rw [planeBandSobolevRhs_value] at hf
  exact he.trans hf
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual weak transport products have all lower Sobolev jets in time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakTransportTimeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakTransportTimeTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def weakTransportTimeCLM {a b : ℝ} (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ (K i) (h i)) 2 (volume.restrict (Set.Icc a b)) :=
  (intervalTransportTimeCLM (E := h i) hab (hK i) v hvm hv V strain B lam hV hstrain hB hlam
    hbv hjets).comp (weakHighCarrierTimeCLM K a b i)

theorem weakTransportTimeCLM_ae {a b : ℝ} (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b) :
    weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeTransportCarrier (hK i) (v (clampPoint a b hab t))
          (hv _ (clampPoint a b hab t).property) V (hbv _ (clampPoint a b hab t).property)
          strain B lam (hjets _ (clampPoint a b hab t).property) (weakHighCarrier K a b W i t) := by
  have hp := intervalTransportTimeCLM_ae (E := h i) hab (hK i) v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets (weakHighCarrierTimeCLM K a b i W)
  refine hp.trans ?_
  filter_upwards [weakHighCarrierTimeCLM_ae K a b i W] with t ht
  rw [ht]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal Sobolev primitive energy integrand is controlled by the single-cutoff budgets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance bandTailIntegrandAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance bandTailIntegrandTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandTailIntegrandTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandTailIntegrandTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

theorem planeBandSobolevSource_pairing_abs_le (N M K : ℕ) (R : ℝ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : PlaneHk Set.univ K E) (w : PlaneHk Set.univ (K + 1) E)
    (hw : ‖truncatePlaneHk (Nat.le_succ K) w‖ ≤ R) :
    |2 * inner ℝ
      ((planeBandDivergenceCLM N K S + planeHkCutoff N K H) -
        (planeBandDivergenceCLM M K S + planeHkCutoff M K H))
      (planeHkCutoff N K (truncatePlaneHk (Nat.le_succ K) w) -
        planeHkCutoff M K (truncatePlaneHk (Nat.le_succ K) w))| ≤
      4 * R * (‖planeHkCutoff N K H - H‖ + ‖planeHkCutoff M K H - H‖) +
        4 * (‖planeHkCutoff N K S - S‖ + ‖planeHkCutoff M K S - S‖) *
          ‖planeGradientTensor w‖ := by
  rw [planeBandSobolevSource_pairing, mul_sub]
  exact bandSourcePairing_abs_le
    (planeHkCutoff (E := E) N K) (planeHkCutoff (E := E) M K)
    (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K)
    (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K)
    H (truncatePlaneHk (Nat.le_succ K) w) S (planeGradientTensor w) R hw
    (planeHkCutoff_norm_le N K _) (planeHkCutoff_norm_le M K _)
    (planeHkCutoff_norm_le N K _) (planeHkCutoff_norm_le M K _)
end

/-! The projected operator is the cutoff of the genuine transport and coupling carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedRhs_carrierResidual (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i j : ι) (d : admissibleOrders K D i j), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d s))
    (i : ι) (w : ∀ j, PlaneHk Set.univ (K j + 1) (h j))
    (hu : ∀ j, u j = hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (w j)))
    (F : ∀ j, PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (g : ∀ j, PlaneHk Set.univ (K j) (h j)) :
    let T := fun j =>
      planeTransportCarrierOperator (E := h j) (hK j) (v t) (hv t t.property) V hV (hbv t t.property)
        strain B lam hjets
    let C := fun j j' (d : admissibleOrders K D j j') =>
      planeCoupledFluxCarrierOperator ρ hρ K D a b j j' d (A j j' d) (hA j j' d) t t.property
        (hC j j' d t t.property)
    let z := fun j => w j - hilbertBandHk N (K j + 1) (u j)
    let RF := fun j => F j + ∑ j', ∑ d : admissibleOrders K D j j', C j j' d (z j')
    let Rg := fun j => g j - T j (z j)
    projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u i +
      projectedSource N (fun j _ => RF j) (fun j _ => Rg j) t i =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (T i (w i))) +
        ν • bandLaplacianOperator (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (w i)) +
        bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          ((∑ j, ∑ d : admissibleOrders K D i j, C i j d (w j)) + F i)) +
        hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i)) := by
  let T := fun j => planeTransportCarrierOperator (E := h j) (hK j) (v t) (hv t t.property)
    V hV (hbv t t.property) strain B lam hjets
  let C := fun j j' (d : admissibleOrders K D j j') =>
    planeCoupledFluxCarrierOperator ρ hρ K D a b j j' d (A j j' d) (hA j j' d) t t.property
      (hC j j' d t t.property)
  dsimp only
  have hrow : projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u i =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
        (T i (hilbertBandHk N (K i + 1) (u i)))) +
      ν • bandLaplacianOperator (E := h i) N (u i) +
      ∑ j : ι, ∑ d : admissibleOrders K D i j,
        bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          (C i j d (hilbertBandHk N (K j + 1) (u j)))) := by
    simpa only [T, C, planeTransportCarrierOperator_apply, planeCoupledFluxCarrierOperator_apply] using
      sourceProjectedOperator_carrier_row K Kmax hK N u ρ strain B lam ν hρ a b v hv V hV hbv t hjets D A hA hC i
  rw [hrow]
  have hl : bandLaplacianOperator (E := h i) N (u i) =
      bandLaplacianOperator (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (w i)) := by
    rw [hu i, bandLaplacian_projection]
  change -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
      (T i (hilbertBandHk N (K i + 1) (u i)))) +
    ν • bandLaplacianOperator (E := h i) N (u i) +
    (∑ j, ∑ d : admissibleOrders K D i j,
      bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
        (C i j d (hilbertBandHk N (K j + 1) (u j))))) +
    (bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
      (F i + ∑ j, ∑ d : admissibleOrders K D i j, C i j d (w j - hilbertBandHk N (K j + 1) (u j)))) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
        (g i - T i (w i - hilbertBandHk N (K i + 1) (u i))))) =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (T i (w i))) +
      ν • bandLaplacianOperator (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (w i)) +
      bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
        ((∑ j, ∑ d : admissibleOrders K D i j, C i j d (w j)) + F i)) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i))
  simp only [map_add, map_sub, map_sum, Finset.sum_sub_distrib, hl]
  abel
end

/-! The projected operator is the cutoff of the genuine transport and coupling carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedRhs_literalCarrierResidual (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i j : ι) (d : admissibleOrders K D i j), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d s))
    (i : ι) (w : ∀ j, PlaneHk Set.univ (K j + 1) (h j))
    (hu : ∀ j, u j = hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (w j)))
    (F : ∀ j, PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (g : ∀ j, PlaneHk Set.univ (K j) (h j)) :
    let T := fun j (p : PlaneHk Set.univ (K j + 1) (h j)) =>
      planeTransportCarrier (hK j) (v t) (hv t t.property) V (hbv t t.property)
        strain B lam hjets p
    let C := fun j j' (d : admissibleOrders K D j j') (p : PlaneHk Set.univ (K j' + 1) (h j')) =>
      planeCoupledFluxTerm ρ hρ K D a b j j' d (A j j' d) (hA j j' d) t t.property
        (hC j j' d t t.property) p
    let z := fun j => w j - hilbertBandHk N (K j + 1) (u j)
    let RF := fun j => F j + ∑ j', ∑ d : admissibleOrders K D j j', C j j' d (z j')
    let Rg := fun j => g j - T j (z j)
    projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u i +
      projectedSource N (fun j _ => RF j) (fun j _ => Rg j) t i =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (T i (w i))) +
        ν • bandLaplacianOperator (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (w i)) +
        bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          ((∑ j, ∑ d : admissibleOrders K D i j, C i j d (w j)) + F i)) +
        hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i)) := by
  simpa only [planeTransportCarrierOperator_apply, planeCoupledFluxCarrierOperator_apply] using
    sourceProjectedRhs_carrierResidual K Kmax hK N u ρ strain B lam ν hρ a b v hv V hV hbv
      t hjets D A hA hC i w hu F g
end

/-! A true higher Sobolev time carrier controls the uniform tails of the source primitives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance bandTailBoundAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance bandTailBoundTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandTailBoundTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandTailBoundTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

private theorem tailBudget_of_difference {x y p q c d : ℝ}
    (h : x - y ≤ c + d) (hi : y ≤ 2 * p ^ 2 + 2 * q ^ 2) :
    x ≤ (2 * p ^ 2 + c) + (2 * q ^ 2 + d) := by
  linarith

theorem planeGradientTensor_memLp {K : ℕ} {a b : ℝ}
    (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeGradientTensor (E := E) (w t)) 2 (volume.restrict (Set.Icc a b)) := by
  simpa only [Function.comp_def, planeGradientTensorOperator_apply] using
    (planeGradientTensorOperator (E := E) K).lipschitzWith.comp_memLp
      (map_zero _) hw

theorem planeBandSobolevPrimitive_sqNorm_le_tailBudget {a b : ℝ} (hab : a ≤ b)
    (N M K : ℕ) (R : ℝ) (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E) (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ L, extendCurve hab (planeBandSobolevPrimitive hab L K f S hS H hH)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeHkCutoff (E := E) L K (truncatePlaneHk (E := E) (Nat.le_succ K) (w t)))
    (hbound : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ‖truncatePlaneHk (E := E) (Nat.le_succ K) (w t)‖ ≤ R) (t : Set.Icc a b) :
    ‖planeBandSobolevPrimitive hab N K f S hS H hH t -
      planeBandSobolevPrimitive hab M K f S hS H hH t‖ ^ 2 ≤
      bandSourceTailBudget (volume.restrict (Set.Icc a b))
        (planeHkCutoff (E := E) N K) (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K) R f H S (fun s => planeGradientTensor (E := E) (w s)) +
      bandSourceTailBudget (volume.restrict (Set.Icc a b))
        (planeHkCutoff (E := E) M K) (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K) R f H S (fun s => planeGradientTensor (E := E) (w s)) := by
  let σ : ℝ → ℝ := fun s => 2 * inner ℝ
    (extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH) s -
      extendCurve hab (planeBandSobolevPrimitive hab M K f S hS H hH) s)
    (planeBandSobolevRhs N K S H s - planeBandSobolevRhs M K S H s)
  let m : ℕ → ℝ → ℝ := fun L => bandSourceTailMajorant
    (planeHkCutoff (E := E) L K)
    (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) L K)
    R H S (fun s => planeGradientTensor (E := E) (w s))
  have hg := planeGradientTensor_memLp w hw
  have hm (L : ℕ) : Integrable (m L) (volume.restrict (Set.Icc a b)) :=
    bandSourceTailMajorant_integrable _ _ _ R H hH S hS _ hg
  have hσ : AEStronglyMeasurable σ (volume.restrict (Set.Icc a b)) := by
    let : SecondCountableTopologyEither ℝ (PlaneHk Set.univ K E) :=
      secondCountableTopologyEither_of_left ℝ _
    have hc := ((continuous_extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH)).sub
      (continuous_extendCurve hab (planeBandSobolevPrimitive hab M K f S hS H hH))).aestronglyMeasurable (μ := volume.restrict (Set.Icc a b))
    have hr := ((planeBandSobolevRhs_integrable N K a b S hS H hH).sub
      (planeBandSobolevRhs_integrable M K a b S hS H hH)).aestronglyMeasurable
    exact (hc.inner hr).const_mul 2
  have hb : ∀ᵐ s ∂volume.restrict (Set.Icc a b), |σ s| ≤ m N s + m M s := by
    filter_upwards [hq N, hq M, hbound] with s hn hm hb
    have he : σ s = 2 * inner ℝ
        (planeBandSobolevRhs N K S H s - planeBandSobolevRhs M K S H s)
        (planeHkCutoff (E := E) N K (truncatePlaneHk (E := E) (Nat.le_succ K) (w s)) -
          planeHkCutoff (E := E) M K (truncatePlaneHk (E := E) (Nat.le_succ K) (w s))) := by
      dsimp only [σ]
      rw [hn, hm, real_inner_comm]
    rw [he]
    have hh := planeBandSobolevSource_pairing_abs_le N M K R (S s) (H s) (w s) hb
    have hright := bandSourceTailMajorant_add
      (planeHkCutoff (E := E) N K) (planeHkCutoff (E := E) M K)
      (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K)
      (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) M K)
      R H S (fun r => planeGradientTensor (E := E) (w r)) s
    exact hh.trans_eq hright.symm
  have hint := AVRegularity.CoupledEnergy.Variational.intervalIntegral_le_full_majorant
    t.property σ (fun s => m N s + m M s) hσ ((hm N).add (hm M)) hb
  rw [integral_add (hm N) (hm M)] at hint
  have he := planeBandSobolevPrimitive_energy hab N M K f S hS H hH t
  change _ = ∫ s in a..t.1, σ s at he
  rw [← he] at hint
  have hi : ‖planeHkCutoff (E := E) N K f - planeHkCutoff (E := E) M K f‖ ^ 2 ≤
      2 * ‖planeHkCutoff (E := E) N K f - f‖ ^ 2 + 2 * ‖planeHkCutoff (E := E) M K f - f‖ ^ 2 := by
    exact norm_band_sq_le_tails (planeHkCutoff (E := E) N K) (planeHkCutoff (E := E) M K) f
  change _ ≤ (2 * ‖planeHkCutoff (E := E) N K f - f‖ ^ 2 + ∫ s in Set.Icc a b, m N s) +
    (2 * ‖planeHkCutoff (E := E) M K f - f‖ ^ 2 + ∫ s in Set.Icc a b, m M s)
  exact tailBudget_of_difference hint hi
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine source primitives with a higher Sobolev time carrier have a continuous lower representative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance sourceRepresentativeAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance sourceRepresentativeTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance
local instance sourceRepresentativeTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance sourceRepresentativeTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

theorem exists_continuous_sobolevRepresentative_of_source_primitives {a b : ℝ} (hab : a ≤ b)
    (K : ℕ) (R : ℝ) (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E) (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ N, extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeHkCutoff (E := E) N K (truncatePlaneHk (E := E) (Nat.le_succ K) (w t)))
    (hbound : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ‖truncatePlaneHk (E := E) (Nat.le_succ K) (w t)‖ ≤ R) :
    ∃ U : C(Set.Icc a b, PlaneHk Set.univ K E),
      Tendsto (fun N => planeBandSobolevPrimitive hab N K f S hS H hH) atTop (𝓝 U) ∧
        extendCurve hab U =ᵐ[volume.restrict (Set.Icc a b)]
          fun t => truncatePlaneHk (E := E) (Nat.le_succ K) (w t) := by
  let e : ℕ → ℝ := fun N => bandSourceTailBudget (volume.restrict (Set.Icc a b))
    (planeHkCutoff (E := E) N K)
    (planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K)
    R f H S (fun t => planeGradientTensor (E := E) (w t))
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_bandSourceTailBudget_of_integrable (volume.restrict (Set.Icc a b))
      (fun N => planeHkCutoff (E := E) N K)
      (fun N => planeHkCutoff (E := PiLp 2 (fun _ : Fin 2 => E)) N K)
      (fun N x => planeHkCutoff_norm_le N K x)
      (fun N x => planeHkCutoff_norm_le N K x)
      (tendsto_planeHkCutoff K) (tendsto_planeHkCutoff K)
      R f H hH S hS _ (planeGradientTensor_memLp w hw)
  exact exists_continuous_timeRepresentative_of_spectral_tails hab
    (fun t => truncatePlaneHk (E := E) (Nat.le_succ K) (w t))
    (fun N => planeHkCutoff (E := E) N K) (tendsto_planeHkCutoff K)
    (fun N => planeBandSobolevPrimitive hab N K f S hS H hH) e he
    (fun N M t => planeBandSobolevPrimitive_sqNorm_le_tailBudget hab N M K R f S hS H hH
      w hw hq hbound t) hq

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The true plane Galerkin transport product consumes ν/4 of the exact gradient energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_band_energy_abs_sum_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * |inner ℝ
      (orderL2Array (planeTransportCarrier hK v hv V hbv a B lam hjets
        (hilbertBandHk N (K + 1) u)).val j)
      (orderL2Array (hilbertBandHk N (K + 1) u).val ⟨j.val, by omega⟩)|) ≤
      (ν / 4) * gradFactorialNormSq ρ (hilbertBandHk N (K + 1) u).val := by
  let p := hilbertBandHk N (K + 1) u
  have he (j : Fin (K + 1)) := transportOrder_inner_eq_commutator_of_ae_masks
    p j v (hv.of_le (by simp)) ⟨V, hbv⟩ hdiv
    (fun m w => driftMaskTerm_memLp_of_velocityJets (Nat.le_of_lt_succ j.isLt) hK
      v hv V hbv a B lam hjets p.toFunction.jet p.toFunction.memL2 m w)
    (planeTransportCarrier hK v hv V hbv a B lam hjets p).val
    (fun w => planeTransportCarrier_band_jet_ae hK N u v hv V hbv a B lam hjets ⟨j, w⟩)
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * |inner ℝ
    (orderL2Array (planeTransportCarrier hK v hv V hbv a B lam hjets p).val j)
    (orderL2Array p.val ⟨j.val, by omega⟩)|) ≤ (ν / 4) * gradFactorialNormSq ρ p.val
  simp_rw [he]
  have hround := congrArg Subtype.val (PlaneHk.toFunction_toHk p)
  change jetToL2 p.toFunction.jet p.toFunction.memL2 = p.val at hround
  have hs := sourceDriftCommutator_energy_abs_sum_le hK ρ a B lam ν hρ ha hB hlam hν
    hsmall hstrain v hv V hbv hjets p.toFunction.jet p.toFunction.memL2
  simpa only [hround, sourceDriftCommutator] using hs


theorem planeTransportCarrier_band_factorialPairing_abs_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    |factorialPairing ρ
      (planeTransportCarrier hK v hv V hbv a B lam hjets (hilbertBandHk N (K + 1) u)).val
      (hilbertBandHk N K u).val| ≤
      (ν / 4) * gradFactorialNormSq ρ (hilbertBandHk N (K + 1) u).val := by
  rw [← hilbertBandHk_truncate N K (K + 1) (Nat.le_succ K) u]
  change |factorialPairing ρ
    (planeTransportCarrier hK v hv V hbv a B lam hjets (hilbertBandHk N (K + 1) u)).val
    (truncateJet (Nat.le_succ K) (hilbertBandHk N (K + 1) u).val)| ≤ _
  rw [factorialPairing_truncate_eq_order_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg (factorialWeight_nonneg ρ _)]
  exact planeTransportCarrier_band_energy_abs_sum_le hK N u ρ a B lam ν hρ ha hB hlam hν
    hsmall hstrain v hv V hbv hdiv hjets

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual weak transport products have all lower Sobolev jets in time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakTransportValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakTransportValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem weakTransportTime_value_ae {a b : ℝ} (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) :
    (planeHkValueOperator (E := h i) (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
      (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeCoefficientOperator (driftFiberCoefficient (E := h i) (v (clampPoint a b hab t)))
          (driftFiberCoefficient_contDiff (E := h i) _
            (hv _ (clampPoint a b hab t).property)).continuous
          (mul_nonneg (by norm_num) hV)
          (fun x => (driftFiberCoefficient_norm_le (E := h i) _ x).trans
            (mul_le_mul_of_nonneg_left (hbv _ (clampPoint a b hab t).property x) (by norm_num)))
          (highGradientReadout (h := h) K i (W t)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (planeHkValueOperator (E := h i) (K i))
      (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W),
    weakTransportTimeCLM_ae hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W,
    weakHighCarrier_jet_ae K a b W hW i] with t hvv ht hj
  rw [hvv, ht, ← planeTransportCarrier_value (hK i) _ _ _ V hV,
    planeGradientTensor_value_formula, hj]
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The projected operator is the cutoff of the genuine transport and coupling carriers. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedRhs_cutoffCarrierResidual (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ) (u : ProjectedFamily h)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (t : Set.Icc a b)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i j : ι) (d : admissibleOrders K D i j), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d s))
    (i : ι) (w : ∀ j, PlaneHk Set.univ (K j + 1) (h j))
    (hu : ∀ j, u j = hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (w j)))
    (F : ∀ j, PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (g : ∀ j, PlaneHk Set.univ (K j) (h j)) :
    let T := fun j (p : PlaneHk Set.univ (K j + 1) (h j)) =>
      planeTransportCarrier (hK j) (v t) (hv t t.property) V (hbv t t.property)
        strain B lam hjets p
    let C := fun j j' (d : admissibleOrders K D j j') (p : PlaneHk Set.univ (K j' + 1) (h j')) =>
      planeCoupledFluxTerm ρ hρ K D a b j j' d (A j j' d) (hA j j' d) t t.property
        (hC j j' d t t.property) p
    let z := fun j => w j - planeHkCutoff N (K j + 1) (w j)
    let RF := fun j => F j + ∑ j', ∑ d : admissibleOrders K D j j', C j j' d (z j')
    let Rg := fun j => g j - T j (z j)
    projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA) N ν t u i +
      projectedSource N (fun j _ => RF j) (fun j _ => Rg j) t i =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (T i (w i))) +
        ν • bandLaplacianOperator (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (w i)) +
        bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          ((∑ j, ∑ d : admissibleOrders K D i j, C i j d (w j)) + F i)) +
        hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i)) := by
  have he := sourceProjectedRhs_literalCarrierResidual K Kmax hK N u ρ strain B lam ν hρ a b
    v hv V hV hbv t hjets D A hA hC i w hu F g
  have hz (j : ι) : hilbertBandHk N (K j + 1) (u j) = planeHkCutoff N (K j + 1) (w j) := by
    calc
      _ = hilbertBandHk N (K j + 1) (hilbertProjection (E := h j) N
        (planeHkValueOperator (E := h j) (K j + 1) (w j))) :=
          congrArg (hilbertBandHk (E := h j) N (K j + 1)) (hu j)
      _ = hilbertBandHk N (K j + 1) (planeHkValueOperator (E := h j) (K j + 1) (w j)) :=
        hilbertBandHk_projection (E := h j) N (K j + 1) _
      _ = _ := rfl
  dsimp only at he ⊢
  simpa only [hz] using he

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem projectedDrift_factorialPairing_abs_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    |factorialPairing ρ
      (hilbertBandHk N K (hilbertProjection N
        (planeCoefficientOperator (E := PiLp 2 (fun _ : Fin 2 => E)) (F := E)
          (driftFiberCoefficient (E := E) v)
          (driftFiberCoefficient_contDiff (E := E) v hv).continuous
          (mul_nonneg (by norm_num) hV)
          (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
            (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
          (bandGradientOperator (E := E) N u)))).val
      (hilbertBandHk N K u).val| ≤
      (ν / 4) * gradFactorialNormSq ρ (hilbertBandHk N (K + 1) u).val := by
  rw [hilbertBandHk_projection,
    planeTransportCarrier_band_value hK N u v hv V hV hbv a B lam hjets,
    hilbertBandHk_carrier_factorialPairing]
  exact planeTransportCarrier_band_factorialPairing_abs_le hK N u ρ a B lam ν
    hρ ha hB hlam hν hsmall hstrain v hv V hbv hdiv hjets
end

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedDrift_massPairing_abs_sum_le (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2)))
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    (∑ i, (π i)⁻¹ * |factorialPairing ρ
      (hilbertBandHk N (K i) (hilbertProjection N
        (planeCoefficientOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (F := h i)
          (driftFiberCoefficient (E := h i) v)
          (driftFiberCoefficient_contDiff (E := h i) v hv).continuous
          (mul_nonneg (by norm_num) hV)
          (fun x => (driftFiberCoefficient_norm_le (E := h i) v x).trans
            (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
          (bandGradientOperator (E := h i) N (u i))))).val
      (hilbertBandHk N (K i) (u i)).val|) ≤
      (ν / 4) * massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val) := by
  unfold massGradNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb := mul_le_mul_of_nonneg_left
    (projectedDrift_factorialPairing_abs_le (hK i) N (u i) ρ a B lam ν
      hρ ha hB hlam hν hsmall hstrain v hv V hV hbv hdiv hjets)
    (inv_nonneg.mpr (hπ i).le)
  exact hb.trans_eq (by ring)
end

end AVRegularity.CoupledEnergyPlane.Variational
end
