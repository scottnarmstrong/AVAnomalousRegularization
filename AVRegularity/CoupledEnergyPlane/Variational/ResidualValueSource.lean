-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.PlaneWeakDifferenceCurve
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The velocity premises of `coupled_energy_plane` absorb the actual plane drift commutator with
constant ν/4. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual nonprincipal drift array; all L² facts are derived from the velocity data. -/
def sourceDriftCommutator {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D) (j : Fin (K + 1)) :
    PiLp 2 (fun _ : DerivativeWord2 j.val => ComponentL2 (volume.restrict Set.univ) E) :=
  driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v D
    (fun m w => driftMaskTerm_memLp_of_velocityJets (Nat.le_of_lt_succ j.isLt) hK
      v hv V hbv a B lam hjets D hD m w)

omit [BorelSpace E] in
theorem sourceDriftCommutator_energy_abs_sum_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * |inner ℝ
      (sourceDriftCommutator hK v hv V hbv a B lam hjets D hD j)
      (orderL2Array (jetToL2 D hD) ⟨j.val, by omega⟩)|) ≤
      (ν / 4) * gradFactorialNormSq ρ (jetToL2 D hD) := by
  exact driftCommutatorL2Array_energy_abs_sum_le hK ρ a B lam ν hρ ha hB hlam hν
    hsmall hstrain v hjets D
    (fun j m w => driftMaskTerm_memLp_of_velocityJets (Nat.le_of_lt_succ j.isLt) hK
      v hv V hbv a B lam hjets D hD m w) hD MeasurableSet.univ

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Actual spectral cutoffs converge in the factorial weighted mass energy `massNormSq`. -/

open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeMassNormSq_cutoff_tendsto (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (w : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    Tendsto (fun N => massNormSq ρ π (fun i => (planeHkCutoff N (K i) (w i)).val))
      atTop (𝓝 (massNormSq ρ π (fun i => (w i).val))) := by
  have hs : Tendsto (fun N i => planeHkCutoff N (K i) (w i)) atTop (𝓝 w) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_planeHkCutoff (K i) (w i))
  have hl := ((planeMassWeightedCarrierCLM (E := E) K ρ π).continuous.tendsto w).comp hs
  simpa only [Function.comp_def, planeMassWeightedCarrierCLM_normSq K ρ π hπ] using hl.norm.pow 2

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual multiplier in the plane Galerkin ODE is the value of the true transport carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_band_value {K Kmax : ℕ} (hK : K ≤ Kmax)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    planeCoefficientOperator (E := PiLp 2 (fun _ : Fin 2 => E)) (F := E)
      (driftFiberCoefficient (E := E) v) (driftFiberCoefficient_contDiff (E := E) v hv).continuous
      (mul_nonneg (by norm_num) hV)
      (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
        (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
      (bandGradientOperator (E := E) N u) =
      planeHkValueOperator K (planeTransportCarrier hK v hv V hbv a B lam hjets
        (hilbertBandHk N (K + 1) u)) := by
  have he := planeCoefficientOperator_eq_productValue
    (planeGradientTensor (hilbertBandHk N (K + 1) u)) (driftFiberCoefficient (E := E) v)
    ((driftFiberCoefficient_contDiff (E := E) v hv).of_le (by simp))
    (A := fun l => driftEnvelope V a B lam l.val)
    (fun l x => (driftFiberCoefficient_array_norm_le (E := E) v hv l.val x).trans
      (driftCoefficient_array_envelope v V hbv a B lam hjets l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))
    (mul_nonneg (by norm_num) hV)
    (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
      (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
  rw [planeGradientTensor_band_value] at he
  exact he

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem planeCoupledFluxTerm_value (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i')) :
    planeCoefficientOperator (A t) hC.continuous ENNReal.toReal_nonneg
      (sourceCoefficient_norm_le ρ hρ (K i) a b A hA t ht)
      (∑ word : DerivativeWord2 (d.1 - 1), (tensorEntryCLM (E := h i') word).compLpL 2 volume
        (univToPlane (w.val ⟨⟨d.1 - 1, by
          have hh := admissibleOrders_reserve K D i i' d; omega⟩, word⟩))) =
      planeHkValueOperator (K i) (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC w) := by
  have hp := planeMultiplyIntervalCoefficient_value ρ hρ (K i) a b A hA t ht hC
    (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w)
  rw [planePositiveDerivativeTensor_value_formula] at hp
  exact hp

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Vanishing strong time L² transport residuals preserve the literal value-source budget. -/

open AVRegularity.CoupledEnergy.Variational
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeMassNorm_timeLp_residual_tendsto (μ : Measure T) [IsFiniteMeasure μ]
    (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (g : ∀ i, T → PlaneHk Set.univ (K i) (E i)) (hg : ∀ i, Integrable (g i) μ)
    (R : ℕ → ∀ i, Lp (PlaneHk Set.univ (K i) (E i)) 2 μ)
    (hR : ∀ i, Tendsto (fun N => R N i) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ t, Real.sqrt (massNormSq ρ π (fun i => (g i t - R N i t).val)) ∂μ)
      atTop (𝓝 (∫ t, Real.sqrt (massNormSq ρ π (fun i => (g i t).val)) ∂μ)) := by
  let L := planeMassWeightedCarrierCLM (E := E) K ρ π
  let f : T → ∀ i, PlaneHk Set.univ (K i) (E i) := fun t i => g i t
  let r : ℕ → T → ∀ i, PlaneHk Set.univ (K i) (E i) := fun N t i => -(R N i t)
  have hf : Integrable f μ := timeL1_family_integrable μ g hg
  have hr (N : ℕ) (i : ι) : Integrable (fun t => -(R N i t)) μ := by
    exact ((Lp.memLp (R N i)).integrable (by norm_num)).neg
  have hri (N : ℕ) : Integrable (r N) μ :=
    timeL1_family_integrable μ (fun i t => -(R N i t)) (hr N)
  have hi (i : ι) : Tendsto (fun N => ∫ t, ‖-(R N i t)‖ ∂μ) atTop (𝓝 0) := by
    simpa only [norm_neg] using timeLp_integral_norm_tendsto_zero μ (fun N => R N i) (hR i)
  have hrl := timeL1_family_integral_norm_tendsto μ (fun N i t => -(R N i t)) hr hi
  have hLl := timeL1_integral_clm_norm_tendsto μ L r hri hrl
  have hh := timeL1_perturbed_integral_norm_tendsto μ (fun t => L (f t))
    (L.integrable_comp hf) (fun N t => L (r N t)) (fun N => L.integrable_comp (hri N)) hLl
  have he (N : ℕ) (t : T) : L (f t) + L (r N t) = L (fun i => g i t - R N i t) := by
    rw [← map_add]
    congr 1
    funext i
    simp only [f, r, Pi.add_apply, sub_eq_add_neg]
  simpa only [he, L, f, planeMassWeightedCarrierCLM_norm K ρ π hπ] using hh

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Zero mass and strict component coercivity for genuine plane carriers. -/

open AVRegularity.CoupledEnergy.Variational
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeMassNormSq_zero (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    massNormSq ρ π (fun i => (0 : PlaneHk Set.univ (K i) (h i)).val) = 0 := by
  have hh := planeMassWeightedCarrierCLM_normSq K ρ π hπ (0 : ∀ i, PlaneHk Set.univ (K i) (h i))
  rw [(planeMassWeightedCarrierCLM (E := h) K ρ π).map_zero] at hh
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply] using! hh.symm

theorem planeCarrier_eq_zero_of_mass_le_zero (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (w : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hm : massNormSq ρ π (fun i => (w i).val) ≤ 0) (i : ι) : w i = 0 := by
  have hf := (componentFactorial_le_mass ρ π hπ (fun i => (w i).val) i).trans
    (mul_nonpos_of_nonneg_of_nonpos (hπ i).le hm)
  have he : factorialNormSq ρ (w i).val = 0 := le_antisymm hf (factorialNormSq_nonneg ρ _)
  have hl := factorialNormSq_lower ρ (w i).val
  rw [he] at hl
  have hz : ‖(w i).val‖ ^ 2 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_right hl (factorialWeightMin_pos (K := K i) ρ hρ)) (sq_nonneg _)
  apply Subtype.ext
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal raw spatial form used in the weak-solution class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawSpatialRhs_ae_native_of_fields (K : ι → ℕ) (D : ℕ) (ν t : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (ψ : PlaneHk Set.univ 1 (h i))
    (T : Lp (h i) 2 (volume : Measure (Vec 2)))
    (G H : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
    (hT : T =ᵐ[volume] fun x => ∑ k : Fin 2, v t x k •
      (w i).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
    (hG : G =ᵐ[volume] fun x => WithLp.toLp 2 (fun k : Fin 2 =>
      (w i).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x))
    (hH : H =ᵐ[volume] fun x => planeRawCouplingFlux K D t A w i x +
      (F i t).toFunction.jet (valueIndex2 (K i)) x) :
    planeRawSpatialRhs K D ν t v A F g w i ψ =ᵐ[volume]
      nativeRawSpatialRhs ν T G H (planeHkValueOperator (E := h i) (K i) (g i t)) ψ := by
  filter_upwards [hT, hG, hH, planeRawValue_ae ψ,
    planeGradientTensor_raw_value_ae ψ, planeRawValue_ae (g i t)] with x ht hg hh hp hgp hv
  symm
  unfold nativeRawSpatialRhs planeRawSpatialRhs
  rw [ht, hg, hh, ← hp, hgp, ← hv]
  simp only [sum_inner, real_inner_smul_left, PiLp.inner_apply,
    WithLp.ofLp_add, Pi.add_apply]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The genuine weak gradient at the full lower Sobolev order belongs to time L². -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakGradientTimeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakGradientTimeTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def weakGradientTimeCLM (K : ι → ℕ) (a b : ℝ) (i : ι) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
        (volume.restrict (Set.Icc a b)) :=
  ((planeGradientTensorOperator (E := h i) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b))).comp (weakHighCarrierTimeCLM K a b i)

theorem weakGradientTimeCLM_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    weakGradientTimeCLM K a b i W =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => planeGradientTensor (weakHighCarrier K a b W i t) := by
  have hp := timeReadout_compLp_ae (volume.restrict (Set.Icc a b))
    (planeGradientTensorOperator (E := h i) (K i)) (weakHighCarrierTimeCLM K a b i) W
    (weakHighCarrier K a b W i) (weakHighCarrierTimeCLM_ae K a b i W)
  exact hp.mono (fun _ ht => ht.trans (planeGradientTensorOperator_apply _ _))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal raw drift multiplier is the value of the true Sobolev transport product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_raw_value_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (q : PlaneHk Set.univ (K + 1) E)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    planeHkValueOperator (E := E) K (planeTransportCarrier hK v hv V hbv a B lam hjets q)
      =ᵐ[volume] fun x => ∑ k : Fin 2, v x k •
        (q.toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) := by
  have hp := planeTransportCarrier_value hK q v hv V hV hbv a B lam hjets
  have ho := planeCoefficientOperator_ae (driftFiberCoefficient (E := E) v)
    (driftFiberCoefficient_contDiff (E := E) v hv).continuous (mul_nonneg (by norm_num) hV)
    (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
      (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (planeGradientTensor (E := E) q))
  filter_upwards [ho, planeGradientTensor_raw_value_ae q] with x hx hg
  rw [← hp, hx, hg, driftFiberCoefficient_apply]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem planeCoupledFluxTerm_raw_value_ae (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i')) :
    planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
      (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC w) =ᵐ[volume] fun x =>
      A t x (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
        w.toFunction.jet ⟨⟨d.1 - 1, by
          have hh := admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x)) := by
  let Q := planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2 w
  have hp := planeMultiplyIntervalCoefficient_value ρ hρ (K i) a b A hA t ht hC Q
  have hq := planePositiveDerivativeTensor_value_ae (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2 w
  simp only [Measure.restrict_univ] at hq
  have hval := univToPlane_ae (Q.val (valueIndex2 (K i)))
  have ho := planeCoefficientOperator_ae (A t) hC.continuous ENNReal.toReal_nonneg
    (sourceCoefficient_norm_le ρ hρ (K i) a b A hA t ht)
    (planeHkValueOperator (E := PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) (K i) Q)
  filter_upwards [hq, hval, ho] with x hx hv ho
  change planeHkValueOperator (K i) (planeMultiplyIntervalCoefficient ρ hρ (K i) a b A hA t ht hC Q) x = _
  rw [← hp, ho]
  change A t x (univToPlane (Q.val (valueIndex2 (K i))) x) = _
  rw [hv]
  exact congrArg (A t x) hx

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Exact energy pairing of the actual projected coupling operator. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupledFluxTerm_band_value (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖A t x‖ ≤ M)
    (N : ℕ) (u : Lp (h i') 2 (volume : Measure (Vec 2)))
 :
    planeCoefficientOperator (A t) hC.continuous hM hb
      (bandTensorOperator (E := h i') N (d.1 - 1) u) =
      planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
        (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC (hilbertBandHk N (K i' + 1) u)) := by
  have hp := planeCoefficientOperator_eq_productValue
    (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 (hilbertBandHk N (K i' + 1) u))
    (A t) hC
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ (K i) a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x) hM hb
  rw [planePositiveDerivativeTensor_band_value] at hp
  exact hp

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The weak high spacetime class has a genuine H¹ time carrier with its literal value readout. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakH1Add (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance weakH1TopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

def weakH1CarrierTimeCLM (K : ι → ℕ) (a b : ℝ) (i : ι) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ 1 (h i)) 2 (volume.restrict (Set.Icc a b)) :=
  ((truncatePlaneHk (E := h i) (show 1 ≤ K i + 1 by omega)).compLpL 2
    (volume.restrict (Set.Icc a b))).comp (weakHighCarrierTimeCLM K a b i)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem weakH1CarrierTimeCLM_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    weakH1CarrierTimeCLM K a b i W =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      truncatePlaneHk (show 1 ≤ K i + 1 by omega) (weakHighCarrier K a b W i t) := by
  exact timeReadout_compLp_ae (volume.restrict (Set.Icc a b))
    (truncatePlaneHk (E := h i) (show 1 ≤ K i + 1 by omega))
    (weakHighCarrierTimeCLM K a b i) W (weakHighCarrier K a b W i)
    (weakHighCarrierTimeCLM_ae K a b i W)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem weakH1CarrierTimeCLM_value_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1)) :
    (fun t => planeHkValueOperator 1 (weakH1CarrierTimeCLM K a b i W t))
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        highJetReadout (h := h) K i (valueIndex2 (K i + 1)) (W t) := by
  filter_upwards [weakH1CarrierTimeCLM_ae K a b i W, weakHighCarrier_jet_ae K a b W hW i]
    with t ht hj
  rw [ht, planeHkValueOperator_apply, truncatePlaneHk_apply]
  change univToPlane ((weakHighCarrier K a b W i t).val (valueIndex2 (K i + 1))) = _
  rw [hj]
  rfl

theorem weakH1CarrierTimeCLM_gradient_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1)) :
    (fun t => planeHkValueOperator 0
      (planeGradientTensor (weakH1CarrierTimeCLM K a b i W t)))
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => highGradientReadout (h := h) K i (W t) := by
  filter_upwards [weakH1CarrierTimeCLM_ae K a b i W, weakHighCarrier_jet_ae K a b W hW i]
    with t ht hj
  rw [ht]
  simp only [planeHkValueOperator_apply, planeGradientTensor, planeFamilyTensor_jet,
    derivativePlaneHk_apply, map_sum, univToPlane_fiberMap, highGradientReadout,
    sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hi : prefixJetIndex (fun _ : Fin 1 => k) (valueIndex2 0) =
      (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi, truncatePlaneHk_apply]
  change univToPlane ((weakHighCarrier K a b W i t).val
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩) = _
  rw [hj]
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_memLp (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d, ContDiff ℝ (K i : ℕ) (A i j d t))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    MemLp (planeRawCouplingFlux K D t A w i) 2 volume := by
  classical
  have hp (j : ι) (d : admissibleOrders K D i j) :
      MemLp (fun x => A i j d t x (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
        (w j).toFunction.jet ⟨⟨d.1 - 1, by
          have hd := admissibleOrders_reserve K D i j d; omega⟩, word⟩ x))) 2 volume := by
    exact MemLp.ae_eq
      (planeCoupledFluxTerm_raw_value_ae ρ hρ K D a b i j d (A i j d) (hA i j d) t ht (hC i j d) (w j))
      (Lp.memLp _)
  unfold planeRawCouplingFlux
  exact memLp_finsetSum Finset.univ (fun j _ =>
    memLp_finsetSum Finset.univ (fun d _ => hp j d))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The genuine lower-order weak carrier is a bounded readout of the common high time class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakLowerAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance weakLowerTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

def weakLowerCarrierTimeCLM (K : ι → ℕ) (a b : ℝ) (i : ι) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ (K i) (h i)) 2 (volume.restrict (Set.Icc a b)) :=
  ((truncatePlaneHk (E := h i) (Nat.le_succ (K i))).compLpL 2
    (volume.restrict (Set.Icc a b))).comp (weakHighCarrierTimeCLM K a b i)

theorem weakLowerCarrierTimeCLM_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    weakLowerCarrierTimeCLM K a b i W =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      truncatePlaneHk (Nat.le_succ (K i)) (weakHighCarrier K a b W i t) := by
  exact timeReadout_compLp_ae (volume.restrict (Set.Icc a b))
    (truncatePlaneHk (E := h i) (Nat.le_succ (K i))) (weakHighCarrierTimeCLM K a b i) W
    (weakHighCarrier K a b W i) (weakHighCarrierTimeCLM_ae K a b i W)

theorem weakLowerCarrierTimeCLM_value_eq_H1_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    (fun t => AVRegularity.CoupledEnergyPlane.Fourier.planeHkValueOperator (K i)
      (weakLowerCarrierTimeCLM K a b i W t)) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => AVRegularity.CoupledEnergyPlane.Fourier.planeHkValueOperator 1
        (weakH1CarrierTimeCLM K a b i W t) := by
  filter_upwards [weakLowerCarrierTimeCLM_ae K a b i W,
    weakH1CarrierTimeCLM_ae K a b i W] with t hlow h1
  rw [hlow, h1]
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawSpatialRhs_integrable (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b t ν : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (v t))
    (V : ℝ) (hbv : ∀ x, ‖v t x‖ ≤ V)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d, ContDiff ℝ (K i : ℕ) (A i j d t))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (φ : PlaneHk Set.univ 1 (h i)) :
    Integrable (planeRawSpatialRhs K D ν t v A F g w i φ) volume := by
  have hval := planeRawJet_memLp φ (valueIndex2 1)
  have hdu (k : Fin 2) := planeRawJet_memLp (w i)
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  have hp (k : Fin 2) := planeRawJet_memLp φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  have hd (k : Fin 2) : Integrable (fun x => v t x k * inner ℝ
      ((w i).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
      (φ.toFunction.jet (valueIndex2 1) x)) volume :=
    (rawInner_integrable_of_memLp_two volume _ _ (hdu k) hval).bdd_mul
      (((continuous_apply k).comp hv).aestronglyMeasurable)
      (ae_of_all _ (fun x => (norm_le_pi_norm (v t x) k).trans (hbv x)))
  have hdiff (k : Fin 2) := rawInner_integrable_of_memLp_two volume _ _ (hdu k) (hp k)
  have hflux := (planeRawCouplingFlux_memLp ρ hρ K D a b t ht A hA hC w i).add
    (planeRawJet_memLp (F i t) (valueIndex2 (K i)))
  have hfluxk (k : Fin 2) : MemLp (fun x => planeRawCouplingFlux K D t A w i x k +
      (F i t).toFunction.jet (valueIndex2 (K i)) x k) 2 volume := by
    simpa only [Function.comp_def, PiLp.proj_apply, WithLp.ofLp_add, Pi.add_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp' hflux
  have hf (k : Fin 2) := rawInner_integrable_of_memLp_two volume _ _ (hfluxk k) (hp k)
  have hg := rawInner_integrable_of_memLp_two volume _ _
    (planeRawJet_memLp (g i t) (valueIndex2 (K i))) hval
  exact ((((integrable_finsetSum Finset.univ (fun k _ => hd k)).neg.sub
    ((integrable_finsetSum Finset.univ (fun k _ => hdiff k)).const_mul ν)).sub
    (integrable_finsetSum Finset.univ (fun k _ => hf k))).add hg)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual multiplier in the plane Galerkin ODE is the value of the true transport carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeTransportCarrierOperator {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (_hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    PlaneHk Set.univ (K + 1) E →L[ℝ] PlaneHk Set.univ K E :=
  (productPlaneHkOperator (AVRegularity.CoupledEnergy.Variational.driftFiberCoefficient (E := E) v)
    ((AVRegularity.CoupledEnergy.Variational.driftFiberCoefficient_contDiff (E := E) v hv).of_le (by simp))
    (B := fun l => driftEnvelope V a B lam l.val)
    (fun l x => (AVRegularity.CoupledEnergy.Variational.driftFiberCoefficient_array_norm_le (E := E) v hv l.val x).trans
      (driftCoefficient_array_envelope v V hbv a B lam hjets l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))).comp
    (planeGradientTensorOperator (E := E) K)

theorem planeTransportCarrierOperator_apply {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (_hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) (u : PlaneHk Set.univ (K + 1) E) :
    planeTransportCarrierOperator hK v hv V _hV hbv a B lam hjets u =
      planeTransportCarrier hK v hv V hbv a B lam hjets u := by
  simp only [planeTransportCarrierOperator, ContinuousLinearMap.comp_apply,
    planeGradientTensorOperator_apply, productPlaneHkOperator_apply, planeTransportCarrier]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine time L² transport products at the complete lower Sobolev order. -/

section
variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance transportAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance

local instance transportTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) := inferInstance

def planeTransportTimeCLM (μ : Measure T) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : T → Vec 2 → Vec 2) (hvm : Measurable (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V a B lam : ℝ) (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hB : ∀ l : Fin (K + 1), 0 ≤ driftEnvelope V a B lam l.val)
    (hjets : ∀ t l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    Lp (PlaneHk Set.univ (K + 1) E) 2 μ →L[ℝ] Lp (PlaneHk Set.univ K E) 2 μ :=
  (productPlaneHkTimeCLM μ (fun t => driftFiberCoefficient (E := E) (v t))
    (driftFiberCoefficient_measurable v hvm)
    (fun t => (driftFiberCoefficient_contDiff (v t) (hv t)).of_le (by simp))
    (fun l => driftEnvelope V a B lam l.val) hB
    (fun t l x => (driftFiberCoefficient_array_norm_le (v t) (hv t) l.val x).trans
      (driftCoefficient_array_envelope (v t) V (hbv t) a B lam (hjets t) l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))).comp
    ((planeGradientTensorOperator (E := E) K).compLpL 2 μ)

theorem planeTransportTimeCLM_ae (μ : Measure T) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : T → Vec 2 → Vec 2) (hvm : Measurable (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V a B lam : ℝ) (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hB : ∀ l : Fin (K + 1), 0 ≤ driftEnvelope V a B lam l.val)
    (hjets : ∀ t l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 μ) :
    planeTransportTimeCLM μ hK v hvm hv V a B lam hbv hB hjets U =ᵐ[μ]
      fun t => planeTransportCarrier hK (v t) (hv t) V (hbv t) a B lam (hjets t) (U t) := by
  have hp := productPlaneHkTimeCLM_ae μ (fun t => driftFiberCoefficient (E := E) (v t))
    (driftFiberCoefficient_measurable v hvm)
    (fun t => (driftFiberCoefficient_contDiff (v t) (hv t)).of_le (by simp))
    (fun l => driftEnvelope V a B lam l.val) hB
    (fun t l x => (driftFiberCoefficient_array_norm_le (v t) (hv t) l.val x).trans
      (driftCoefficient_array_envelope (v t) V (hbv t) a B lam (hjets t) l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))
    ((planeGradientTensorOperator (E := E) K).compLpL 2 μ U)
  filter_upwards [hp, ContinuousLinearMap.coeFn_compLpL (planeGradientTensorOperator (E := E) K) U]
    with t ht hgrad
  have he : (planeTransportTimeCLM μ hK v hvm hv V a B lam hbv hB hjets U) t =
      (productPlaneHkTimeCLM μ (fun t => driftFiberCoefficient (E := E) (v t))
        (driftFiberCoefficient_measurable v hvm)
        (fun t => (driftFiberCoefficient_contDiff (v t) (hv t)).of_le (by simp))
        (fun l => driftEnvelope V a B lam l.val) hB
        (fun t l x => (driftFiberCoefficient_array_norm_le (v t) (hv t) l.val x).trans
          (driftCoefficient_array_envelope (v t) V (hbv t) a B lam (hjets t) l.val
            ((Nat.le_of_lt_succ l.isLt).trans hK) x))
        ((planeGradientTensorOperator (E := E) K).compLpL 2 μ U)) t := rfl
  rw [he, ht, hgrad, planeGradientTensorOperator_apply]
  rfl
end

/-! The velocity bounds of `coupled_energy_plane` supply the complete interval Sobolev transport
operator. -/

section
theorem driftEnvelope_nonneg {V a B lam : ℝ} (hV : 0 ≤ V) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hlam : 0 < lam) (l : ℕ) : 0 ≤ driftEnvelope V a B lam l := by
  unfold driftEnvelope
  split_ifs <;> positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance intervalTransportAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance intervalTransportTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

def intervalTransportTimeCLM {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b)) →L[ℝ]
      Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b)) :=
  planeTransportTimeCLM (volume.restrict (Set.Icc a b)) hK
    (fun t => v (clampPoint a b hab t))
    (hvm.comp (((continuous_clampPoint a b hab).measurable.comp measurable_fst).prodMk measurable_snd))
    (fun t => hv _ (clampPoint a b hab t).property)
    V strain B lam (fun t => hbv _ (clampPoint a b hab t).property)
    (fun l => driftEnvelope_nonneg hV hstrain hB hlam l.val)
    (fun t => hjets _ (clampPoint a b hab t).property)

theorem intervalTransportTimeCLM_ae {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b))) :
    intervalTransportTimeCLM hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeTransportCarrier hK (v (clampPoint a b hab t))
          (hv _ (clampPoint a b hab t).property) V (hbv _ (clampPoint a b hab t).property)
          strain B lam (hjets _ (clampPoint a b hab t).property) (U t) := by
  exact planeTransportTimeCLM_ae _ _ _ _ _ _ _ _ _ _ _ _ U
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The weak high spacetime class has a genuine H¹ time carrier with its literal value readout. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem weakH1CarrierTime_raw_gradient_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0
        (planeGradientTensor (E := h i) (weakH1CarrierTimeCLM K a b i W t)) =ᵐ[volume]
          fun x => WithLp.toLp 2 (fun k : Fin 2 => (weakHighCarrier K a b W i t).toFunction.jet
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) := by
  filter_upwards [weakH1CarrierTimeCLM_ae K a b i W] with t ht
  rw [ht]
  exact planeGradientTensor_raw_value_ae
    (truncatePlaneHk (E := h i) (show 1 ≤ K i + 1 by omega) (weakHighCarrier K a b W i t))

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

theorem sourceProjectedOperator_carrier_row (K : ι → ℕ) (Kmax : ℕ)
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
    (i : ι) :
    projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA)
      N ν t u i =
      -hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i)
        (planeTransportCarrier (hK i) (v t) (hv t t.property) V (hbv t t.property)
          strain B lam hjets (hilbertBandHk N (K i + 1) (u i)))) +
      ν • bandLaplacianOperator (E := h i) N (u i) +
      ∑ j : ι, ∑ d : admissibleOrders K D i j,
        bandDivergenceOperator (E := h i) N (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
          (planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hA i j d) t t.property
            (hC i j d t t.property) (hilbertBandHk N (K j + 1) (u j)))) := by
  let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA
  have hd : planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
      (C.drift_bound_nonneg i) (C.drift_le i t) (bandGradientOperator (E := h i) N (u i)) =
      planeHkValueOperator (E := h i) (K i)
        (planeTransportCarrier (hK i) (v t) (hv t t.property) V (hbv t t.property)
          strain B lam hjets (hilbertBandHk N (K i + 1) (u i))) :=
    planeTransportCarrier_band_value (hK i) N (u i) (v t) (hv t t.property)
      V hV (hbv t t.property) strain B lam hjets
  rw [projectedOperator_component, hd]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact planeCoupledFluxTerm_band_value ρ hρ K D a b i j d (A i j d) (hA i j d)
    t t.property (hC i j d t t.property) (coefficientSeminorm ρ (K i) a b (A i j d)).toReal
    ENNReal.toReal_nonneg (sourceCoefficient_norm_le ρ hρ (K i) a b (A i j d)
      (hA i j d) t t.property) N (u j)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The velocity bounds of `coupled_energy_plane` supply the complete interval Sobolev transport
operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance residualTransportAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance residualTransportTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem intervalTransportTimeCLM_residual_ae {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b))) (N : ℕ) :
    intervalTransportTimeCLM hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets
      (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K + 1) U)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeTransportCarrier hK (v (clampPoint a b hab t))
          (hv _ (clampPoint a b hab t).property) V (hbv _ (clampPoint a b hab t).property)
          strain B lam (hjets _ (clampPoint a b hab t).property)
          (U t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K + 1) (U t)) := by
  have hp := intervalTransportTimeCLM_ae (E := E) hab hK v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets
    (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K + 1) U)
  filter_upwards [hp, planeSobolevTimeResidual_ae (volume.restrict (Set.Icc a b)) N (K + 1) U]
    with t ht hr
  rw [ht, hr]

theorem tendsto_intervalTransportTimeCLM_residual {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => intervalTransportTimeCLM hab hK v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets
        (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K + 1) U)) atTop (𝓝 0) := by
  exact tendsto_planeSobolevTimeResidual_image (E := E)
    (J := Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b)))
    (volume.restrict (Set.Icc a b)) (K + 1) U
    (intervalTransportTimeCLM hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Exact energy pairing of the actual projected coupling operator. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedCoupling_factorialPairing (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖A t x‖ ≤ M)
    (N : ℕ) (u : Lp (h i') 2 (volume : Measure (Vec 2)))
    (ui : Lp (h i) 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ
      (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
        (planeCoefficientOperator (A t) hC.continuous hM hb
          (bandTensorOperator (E := h i') N (d.1 - 1) u)))).val
      (hilbertBandHk N (K i) ui).val =
    -factorialPairing ρ
      (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC
        (hilbertBandHk N (K i' + 1) u)).val
      (planeGradientTensor (hilbertBandHk N (K i + 1) ui)).val := by
  rw [planeCoupledFluxTerm_band_value ρ hρ K D a b i i' d A hA t ht hC M hM hb N u]
  exact bandDivergence_factorialPairing N (K i) ρ ui _

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The velocity bounds of `coupled_energy_plane` supply the complete interval Sobolev transport
operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance residualValueSourceAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance residualValueSourceTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

def planeResidualValueSource {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ K E) (N : ℕ) : ℝ → PlaneHk Set.univ K E :=
  timeValueSource (intervalTransportTimeCLM hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets
    (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K + 1) U)) g

theorem planeResidualValueSource_integrable {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ K E) (N : ℕ) (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    Integrable (planeResidualValueSource hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U g N)
      (volume.restrict (Set.Icc a b)) :=
  timeValueSource_integrable _ g hg

theorem planeResidualValueSource_ae {a b : ℝ} (hab : a ≤ b) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : Lp (PlaneHk Set.univ (K + 1) E) 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ K E) (N : ℕ) :
    planeResidualValueSource hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U g N
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => g t -
        planeTransportCarrier hK (v (clampPoint a b hab t))
          (hv _ (clampPoint a b hab t).property) V (hbv _ (clampPoint a b hab t).property)
          strain B lam (hjets _ (clampPoint a b hab t).property)
          (U t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K + 1) (U t)) := by
  exact timeValueSource_ae_sub_of_field _ g _
    (intervalTransportTimeCLM_residual_ae hab hK v hvm hv V strain B lam hV hstrain hB hlam hbv hjets U N)

end AVRegularity.CoupledEnergyPlane.Variational
end
end
end
