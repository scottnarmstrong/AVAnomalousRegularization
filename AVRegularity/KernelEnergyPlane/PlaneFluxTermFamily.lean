-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.CarrierPairing
public import AVRegularity.KernelEnergyPlane.PlaneDerivativeTensorCLM
import AVRegularity.KernelEnergy.TorusFactorialReadout
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
public import AVRegularity.KernelEnergy.PlaneFluxTerm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizer
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.KernelEnergyPlane

/-! Reconstruct plane Sobolev-valued measurability from the value through bounded-frequency cutoffs. -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
variable {T : Type*} [MeasurableSpace T]

def planeCarrierValueCLM (k : ℕ) : PlaneHk Set.univ k G →L[ℝ]
    Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 k => ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) G)
    (valueIndex2 k)).comp (planeHkGraph (E := G) Set.univ k).toSubmodule.subtypeL

omit [FiniteDimensional ℝ G] in
@[simp] theorem planeCarrierValueCLM_apply (k : ℕ) (u : PlaneHk Set.univ k G) :
    planeCarrierValueCLM k u = u.val (valueIndex2 k) := rfl

theorem planeCarrier_stronglyMeasurable_of_value (k : ℕ)
    (u : T → PlaneHk Set.univ k G)
    (hv : StronglyMeasurable (fun t => (u t).val (valueIndex2 k))) :
    StronglyMeasurable u := by
  have hm (N : ℕ) : StronglyMeasurable (fun t => planeHkCutoff N k (u t)) := by
    have hv' := (univToPlane (E := G)).continuous.comp_stronglyMeasurable hv
    exact (hilbertBandHkOperator (E := G) N k).continuous.comp_stronglyMeasurable hv'
  exact stronglyMeasurable_of_tendsto atTop hm
    (tendsto_pi_nhds.mpr (fun t => tendsto_planeHkCutoff k (u t)))

end AVRegularity.KernelEnergyPlane
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Simultaneous Sobolev cutoffs on a finite family, in its plain pi norm. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

def planeFamilyCutoff (N : ℕ) (K : ι → ℕ) :
    (∀ i, PlaneHk Set.univ (K i) (E i)) →L[ℝ] (∀ i, PlaneHk Set.univ (K i) (E i)) :=
  ContinuousLinearMap.pi (fun i => (planeHkCutoff (E := E i) N (K i)).comp
    (ContinuousLinearMap.proj i))

local instance familyTimeCarrierNormed (K : ι → ℕ) (i : ι) :
    NormedAddCommGroup (PlaneHk Set.univ (K i) (E i)) := inferInstance
local instance familyTimeCarrierSpace (K : ι → ℕ) (i : ι) :
    NormedSpace ℝ (PlaneHk Set.univ (K i) (E i)) := inferInstance
local instance familyTimeFamilyNormed (K : ι → ℕ) :
    NormedAddCommGroup (∀ i, PlaneHk Set.univ (K i) (E i)) := inferInstance
local instance familyTimeFamilySpace (K : ι → ℕ) :
    NormedSpace ℝ (∀ i, PlaneHk Set.univ (K i) (E i)) := inferInstance

theorem tendsto_planeFamilyCutoff_time {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ι → ℕ) (U : Lp (∀ i, PlaneHk Set.univ (K i) (E i)) 2 μ) :
    Tendsto (fun N => (planeFamilyCutoff (E := E) N K).compLpL 2 μ U) atTop (𝓝 U) := by
  classical
  exact timeFamily_cutoff_tendsto (E := fun i => PlaneHk Set.univ (K i) (E i)) μ
    (fun i N => planeHkCutoff (E := E i) N (K i)) U
    (fun i => tendsto_planeHkCutoff_time (E := E i) μ (K i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun j => PlaneHk Set.univ (K j) (E j)) i).compLpL 2 μ U))

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergyPlane

/-! Convert the existing factorial multiplication and reserve estimates to
ordinary Sobolev graph norm bounds for Bochner measurability arguments. -/

variable {μ : Measure (Vec 2)} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem jetNorm_le_factorialRoot {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (D : JetL2 μ K E) :
    ‖D‖ ≤ Real.sqrt (factorialNormSq ρ D) / Real.sqrt (factorialWeightMin ρ K) := by
  have hm := factorialWeightMin_pos ρ hρ (K := K)
  have hs := Real.sqrt_le_sqrt (factorialNormSq_lower ρ D)
  rw [Real.sqrt_mul hm.le, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hm), mul_comm]
  exact hs

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem gradFactorialNormSq_le_jetNormSq {K : ℕ} (ρ : ℝ)
    (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSq ρ D ≤ factorialWeightMax ρ K * ‖D‖ ^ 2 := by
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq D j.succ) ≤ _
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  calc
    _ ≤ ∑ j : Fin (K + 1), factorialWeightMax ρ K * derivativeNormSq D j.succ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ j) (derivativeNormSq_nonneg D _)
    _ = factorialWeightMax ρ K * ∑ j : Fin (K + 1), derivativeNormSq D j.succ := by
      rw [Finset.mul_sum]
    _ ≤ factorialWeightMax ρ K * ∑ j : Fin (K + 2), derivativeNormSq D j :=
      mul_le_mul_of_nonneg_left
        (sum_comp_le_sum_nonneg Fin.succ (Fin.succ_injective (K + 1)) (derivativeNormSq D)
          (derivativeNormSq_nonneg D)) hm
    _ = _ := by rw [jet_norm_sq_eq_sum]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem gradFactorialRoot_le_jetNorm {K : ℕ} (ρ : ℝ)
    (D : JetL2 μ (K + 1) E) :
    Real.sqrt (gradFactorialNormSq ρ D) ≤ Real.sqrt (factorialWeightMax ρ K) * ‖D‖ := by
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  have hs := Real.sqrt_le_sqrt (gradFactorialNormSq_le_jetNormSq ρ D)
  simpa only [Real.sqrt_mul hm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.KernelEnergyPlane

/-! A spatial regularizer (`IsSpatialRegularizer`) supplies a canonical bounded linear map on the
same-order Sobolev carrier. Linearity follows from uniqueness of weak jets. -/

section
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

theorem planeRegularizer_exists_sameOrder (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : PlaneHk Set.univ k G) :
    ∃ y : PlaneHk Set.univ k G,
      y.val (valueIndex2 k) = S t (z.val (valueIndex2 k)) ∧
      factorialNormSq ρ y.val ≤ (c 0) ^ 2 * factorialNormSq ρ z.val := by
  simpa only [Nat.add_zero, pow_zero, div_one, derivFactorialNormSq,
    factorialNormSq, derivativeNormSq] using hS.2.2.2 t ht 0 (by omega) z

def planeRegularizerCarrier (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : PlaneHk Set.univ k G) : PlaneHk Set.univ k G :=
  Classical.choose (planeRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)

theorem planeRegularizerCarrier_value (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : PlaneHk Set.univ k G) :
    (planeRegularizerCarrier ρ k D hD a b c r S hS t ht z).val (valueIndex2 k) =
      S t (z.val (valueIndex2 k)) :=
  (Classical.choose_spec (planeRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)).1

theorem planeRegularizerCarrier_factorial_bound (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : PlaneHk Set.univ k G) :
    factorialNormSq ρ (planeRegularizerCarrier ρ k D hD a b c r S hS t ht z).val ≤
      (c 0) ^ 2 * factorialNormSq ρ z.val :=
  (Classical.choose_spec (planeRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)).2
end

/-! Retain every regularizer gain to control the complete higher lifted carrier. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

theorem planeRegularizer_exists_shifted_bounds (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))) →L[ℝ]
      Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
    (hS : IsSpatialRegularizer ρ k D a b c r S) (V : PlaneHk Set.univ (k + 1) H) :
    ∃ Y : PlaneHk Set.univ (k + (D - 2) + 1) G,
      Y.val (valueIndex2 (k + (D - 2) + 1)) =
        S t (C.compLp (V.val (valueIndex2 (k + 1)))) ∧
      ∀ m : ℕ, ∀ hm : m ≤ D - 2 + 1,
        derivFactorialNormSq m ρ (truncatePlaneHk (by omega : k + m ≤ k + (D - 2) + 1) Y).val ≤
          (if m = 0 then (c 0) ^ 2 else 2 * (c (m - 1) / r ^ (m - 1)) ^ 2) *
            (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) := by
  classical
  obtain ⟨Y, hY, hgrad⟩ := planeRegularizerLift ρ k D hD a b t ht c r C S hS V
  refine ⟨Y, hY, ?_⟩
  intro m hm
  cases m with
  | zero =>
    let Z := mapPlaneHk C (truncatePlaneHk (Nat.le_succ k) V)
    have he : truncatePlaneHk (by omega : k + 0 ≤ k + (D - 2) + 1) Y =
        planeRegularizerCarrier ρ k D hD a b c r S hS t ht Z := by
      apply PlaneHk.ext_value isOpen_univ
      change Y.val (valueIndex2 (k + (D - 2) + 1)) =
        (planeRegularizerCarrier ρ k D hD a b c r S hS t ht Z).val (valueIndex2 k)
      rw [planeRegularizerCarrier_value]
      dsimp only [Z]
      rw [mapPlaneHk_jet_eq_compLp]
      exact hY
    rw [he]
    have hb := (planeRegularizerCarrier_factorial_bound ρ k D hD a b c r S hS t ht Z).trans
      (mul_le_mul_of_nonneg_left (mappedLowerInput_factorial_bound ρ k C V) (sq_nonneg (c 0)))
    simpa [derivFactorialNormSq, factorialNormSq, derivativeNormSq] using hb
  | succ m =>
    have hmD : m + 2 ≤ D := by omega
    choose Z hZv hZb hZeq using (fun q : Fin 2 => hgrad q m hmD)
    let T : PlaneHk Set.univ (k + m + 1) G := truncatePlaneHk (by omega) Y
    have hg (q : Fin 2) : derivativePlaneHk (K := k + m) (r := 1) (fun _ : Fin 1 => q) T = Z q := by
      rw [truncatePlane_derivative_commute (by omega : k + m ≤ k + (D - 2)) Y q]
      exact hZeq q
    have hb (q : Fin 2) : derivFactorialNormSq m ρ (Z q).val ≤
        (c m / r ^ m) ^ 2 * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) :=
      (hZb q).trans (mul_le_mul_of_nonneg_left (mappedGradientInput_factorial_bound ρ k C V q)
        (sq_nonneg (c m / r ^ m)))
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin 2))) => hb q)
    rw [← planeDerivFactorialNormSq_succ ρ T Z hg] at hs
    simpa only [Nat.succ_sub_one, Nat.add_succ, ite_eq_right (Nat.succ_ne_zero m),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
      mul_assoc, T] using hs
end

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
    Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
  (hS : IsSpatialRegularizer ρ k D a b c r S)

include hD hS in
theorem planeRegularizedInput_exists (t : ℝ) (ht : t ∈ Set.Icc a b) (V : PlaneHk Set.univ (k + 1) H) :
    ∃ Y : PlaneHk Set.univ (k + D - 1) G,
      Y.val (valueIndex2 (k + D - 1)) =
        S t (C.compLp (V.val (valueIndex2 (k + 1)))) := by
  obtain ⟨Y, hY, _⟩ := planeRegularizerLift ρ k D hD a b t ht c r C S hS V
  have he : k + (D - 2) + 1 = k + D - 1 := by omega
  refine ⟨castPlaneHk he Y, ?_⟩
  rw [castPlaneHk_valueIndex]
  exact hY

def planeRegularizedInput (t : ℝ) (ht : t ∈ Set.Icc a b) (V : PlaneHk Set.univ (k + 1) H) :
    PlaneHk Set.univ (k + D - 1) G :=
  Classical.choose (planeRegularizedInput_exists ρ k D hD a b c r C S hS t ht V)

theorem planeRegularizedInput_value (t : ℝ) (ht : t ∈ Set.Icc a b) (V : PlaneHk Set.univ (k + 1) H) :
    (planeRegularizedInput ρ k D hD a b c r C S hS t ht V).val (valueIndex2 (k + D - 1)) =
      S t (C.compLp (V.val (valueIndex2 (k + 1)))) :=
  Classical.choose_spec (planeRegularizedInput_exists ρ k D hD a b c r C S hS t ht V)

def planeRegularizedInputLinearMap (t : ℝ) (ht : t ∈ Set.Icc a b) :
    PlaneHk Set.univ (k + 1) H →ₗ[ℝ] PlaneHk Set.univ (k + D - 1) G where
  toFun := planeRegularizedInput ρ k D hD a b c r C S hS t ht
  map_add' U V := by
    apply PlaneHk.ext_value isOpen_univ
    rw [planeRegularizedInput_value]
    change S t ((C.compLpL 2 (volume.restrict (Set.univ : Set (Vec 2))))
      (U.val (valueIndex2 (k + 1)) + V.val (valueIndex2 (k + 1)))) = _
    rw [(C.compLpL 2 (volume.restrict (Set.univ : Set (Vec 2)))).map_add, (S t).map_add]
    change _ = (planeRegularizedInput ρ k D hD a b c r C S hS t ht U).val
        (valueIndex2 (k + D - 1)) +
      (planeRegularizedInput ρ k D hD a b c r C S hS t ht V).val (valueIndex2 (k + D - 1))
    rw [planeRegularizedInput_value, planeRegularizedInput_value]
    rfl
  map_smul' q U := by
    apply PlaneHk.ext_value isOpen_univ
    rw [planeRegularizedInput_value]
    change S t ((C.compLpL 2 (volume.restrict (Set.univ : Set (Vec 2))))
      (q • U.val (valueIndex2 (k + 1)))) = _
    rw [(C.compLpL 2 (volume.restrict (Set.univ : Set (Vec 2)))).map_smul, (S t).map_smul]
    change _ = q • (planeRegularizedInput ρ k D hD a b c r C S hS t ht U).val
      (valueIndex2 (k + D - 1))
    rw [planeRegularizedInput_value]
    rfl
end

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
    Lp G 2 (volume.restrict (Set.univ : Set (Vec 2))))
  (hS : IsSpatialRegularizer ρ k D a b c r S)

theorem planeRegularizedInput_time_stronglyMeasurable
    (V : Set.Icc a b → PlaneHk Set.univ (k + 1) H) (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      planeRegularizedInput ρ k D hD a b c r C S hS t t.property (V t)) := by
  have hv := ((C.compLpL 2 (volume.restrict (Set.univ : Set (Vec 2)))).comp
    (planeCarrierValueCLM (G := H) (k + 1))).continuous.comp_stronglyMeasurable hV
  have hs := timeOperator_stronglyMeasurable (fun t : Set.Icc a b => S t)
    (fun z => hS.1 z) _ hv
  apply planeCarrier_stronglyMeasurable_of_value (k + D - 1)
  have he : (fun t : Set.Icc a b => S t (C.compLp (planeCarrierValueCLM (G := H) (k + 1) (V t)))) =
      (fun t : Set.Icc a b => planeCarrierValueCLM (G := G) (k + D - 1)
        (planeRegularizedInput ρ k D hD a b c r C S hS t t.property (V t))) := by
    funext t
    exact (planeRegularizedInput_value ρ k D hD a b c r C S hS t t.property (V t)).symm
  change StronglyMeasurable (fun t : Set.Icc a b => S t
    (C.compLp (planeCarrierValueCLM (G := H) (k + 1) (V t)))) at hs
  rwa [he] at hs
end

/-! Original kernel hypotheses bundled for reuse in coefficient ODE and
Bochner-limit constructions. All bounds here are premises of `kernel_energy_plane`. -/

structure PlaneKernelOperator (t₀ t₁ ρ ν : ℝ) (k D : ℕ)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    where
  htime : t₀ ≤ t₁
  radius_pos : 0 < ρ
  diffusivity_pos : 0 < ν
  order_ge_two : 2 ≤ D
  π : ι → ℝ
  hπ : ∀ i, 0 < π i
  B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))
  hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => B i j α d p.1 p.2
  hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t)
  hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤
  C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α
  S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2))))
  c : ℕ → ℝ
  r : ∀ i j, Γ i j → ℝ
  hr : ∀ i j α, 0 < r i j α
  hS : ∀ i j α, IsSpatialRegularizer ρ k D t₀ t₁ c (r i j α) (S i j α)
  θ : ℝ
  hθ : θ ≤ 1 / 8
  hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B)

/-! The canonical lift and raw flux of a kernel on the plane. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def lift (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) : PlaneHk Set.univ (k + D - 1) (G i j α) :=
  planeRegularizedInput ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht (V j)

theorem lift_value (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) :
    (P.lift t ht V i j α).val (valueIndex2 (k + D - 1)) =
      P.S i j α t ((P.C i j α).compLp ((V j).val (valueIndex2 (k + 1)))) :=
  planeRegularizedInput_value ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht (V j)

def rawFlux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i : ι) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (P.lift t ht V i j α).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

theorem exists_flux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    ∃ Q : ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)),
      (∀ i, (Q i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
        P.rawFlux t ht V i) ∧
      massNormSq ρ P.π (fun i => (Q i).val) ≤
        (ν * P.θ) ^ 2 * massGradNormSq ρ P.π (fun i => (V i).val) := by
  obtain ⟨Y, Q, hY, hQ, hb⟩ := AVRegularity.Providers.kernel_flux_bound_plane
    a b P.htime ρ P.radius_pos ν P.diffusivity_pos k D P.order_ge_two P.π P.hπ
    P.B P.hB_meas P.hB_smooth P.hB_fin P.C P.S P.c P.r P.hr P.hS P.θ P.hθ P.hschur t ht V
  have he : Y = P.lift t ht V := by
    funext i j α
    apply PlaneHk.ext_value isOpen_univ
    exact (hY i j α).trans (P.lift_value t ht V i j α).symm
  rw [he] at hQ
  exact ⟨Q, hQ, hb⟩

def flux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    ∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  Classical.choose (P.exists_flux t ht V)

theorem flux_raw (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    (P.flux t ht V i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      P.rawFlux t ht V i := (Classical.choose_spec (P.exists_flux t ht V)).1 i

theorem flux_mass_bound (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) :
    massNormSq ρ P.π (fun i => (P.flux t ht V i).val) ≤
      (ν * P.θ) ^ 2 * massGradNormSq ρ P.π (fun i => (V i).val) :=
  (Classical.choose_spec (P.exists_flux t ht V)).2

end PlaneKernelOperator
end

/-! Linearity of the canonical lift and of the raw flux in the input. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem lift_add (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i j : ι) (α : Γ i j) :
    P.lift t ht (U + V) i j α = P.lift t ht U i j α + P.lift t ht V i j α :=
  (planeRegularizedInputLinearMap ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht).map_add (U j) (V j)

theorem lift_smul (t : ℝ) (ht : t ∈ Set.Icc a b) (q : ℝ)
    (U : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i j : ι) (α : Γ i j) :
    P.lift t ht (fun i => q • U i) i j α = q • P.lift t ht U i j α :=
  (planeRegularizedInputLinearMap ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht).map_smul q (U j)

theorem rawFlux_add_ae (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    P.rawFlux t ht (U + V) i =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => P.rawFlux t ht U i x + P.rawFlux t ht V i x := by
  have hj : ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      ∀ j (α : Γ i j) (a : JetIndex2 (k + D - 1)),
      (P.lift t ht (U + V) i j α).toFunction.jet a x =
        (P.lift t ht U i j α).toFunction.jet a x + (P.lift t ht V i j α).toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro a
    rw [P.lift_add]
    exact planeJet_add_ae _ _ a
  filter_upwards [hj] with x hx
  unfold rawFlux
  have he (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht (U + V) i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) =
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht U i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) +
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht V i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    rw [← (P.B i j α d t x).map_add]
    congr 1
    apply PiLp.ext
    intro word
    exact hx j α _
  simp_rw [he, Finset.sum_add_distrib]

theorem rawFlux_smul_ae (t : ℝ) (ht : t ∈ Set.Icc a b) (q : ℝ)
    (U : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    P.rawFlux t ht (fun i => q • U i) i =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => q • P.rawFlux t ht U i x := by
  have hj : ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      ∀ j (α : Γ i j) (a : JetIndex2 (k + D - 1)),
      (P.lift t ht (fun i => q • U i) i j α).toFunction.jet a x =
        q • (P.lift t ht U i j α).toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro a
    rw [P.lift_smul]
    exact planeJet_smul_ae q _ a
  filter_upwards [hj] with x hx
  unfold rawFlux
  have he (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht (fun i => q • U i) i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) =
      q • P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht U i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    rw [← (P.B i j α d t x).map_smul]
    congr 1
    apply PiLp.ext
    intro word
    exact hx j α _
  simp_rw [he, Finset.smul_sum]

def fluxLinearMap (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∀ i, PlaneHk Set.univ (k + 1) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) where
  toFun := P.flux t ht
  map_add' U V := by
    funext i
    apply planeCarrier_eq_of_value_ae
    filter_upwards [P.flux_raw t ht (U + V) i, P.flux_raw t ht U i, P.flux_raw t ht V i,
      P.rawFlux_add_ae t ht U V i,
      planeJet_add_ae (P.flux t ht U i) (P.flux t ht V i) (valueIndex2 k)] with x hsum hU hV ha hr
    exact hsum.trans (ha.trans ((congrArg₂ (· + ·) hU hV).symm.trans hr.symm))
  map_smul' q U := by
    funext i
    apply planeCarrier_eq_of_value_ae
    filter_upwards [P.flux_raw t ht (fun i => q • U i) i, P.flux_raw t ht U i,
      P.rawFlux_smul_ae t ht q U i,
      planeJet_smul_ae q (P.flux t ht U i) (valueIndex2 k)] with x hsum hU ha hr
    exact hsum.trans (ha.trans ((congrArg (q • ·) hU).symm.trans hr.symm))

end PlaneKernelOperator
end

/-! The family of flux terms of the canonical kernel flux and their assembled flux. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelOperator
variable (P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def fluxTerm (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  planeKernelFluxTerm (m := d.1 - 2) (r := d.1 - 1)
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
    (truncatePlaneHk (by have := Finset.mem_Icc.1 d.2; omega) (P.lift t ht V i j α))

theorem fluxTerm_raw (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    (P.fluxTerm t ht V i j α d).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      fun x => P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht V i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  have hd := Finset.mem_Icc.1 d.2
  have hr : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by omega
  have hb := planeKernelFluxTerm_base_ae hr ρ P.radius_pos a b (P.B i j α d)
    (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
    (truncatePlaneHk hlow (P.lift t ht V i j α))
  have hj : ∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)), ∀ word : DerivativeWord2 (d.1 - 1),
      (truncatePlaneHk hlow (P.lift t ht V i j α)).toFunction.jet
        ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
      (P.lift t ht V i j α).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x := by
    apply ae_all_iff.mpr
    intro word
    exact truncatePlaneHk_toFunction_jet_ae hlow (P.lift t ht V i j α) _
  filter_upwards [hb, hj] with x hx hjx
  exact hx.trans (congrArg (P.B i j α d t x) (PiLp.ext (fun word => hjx word)))

def assembledFlux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, PlaneHk Set.univ (k + 1) (h i))
    (i : ι) : PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), P.fluxTerm t ht V i j α d

theorem assembledFlux_raw (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    (P.assembledFlux t ht V i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict (Set.univ : Set (Vec 2))]
      P.rawFlux t ht V i := by
  classical
  apply planeJet_sum_ae_of_eq
  intro j
  apply planeJet_sum_ae_of_eq
  intro α
  apply planeJet_sum_ae_of_eq
  intro d
  exact P.fluxTerm_raw t ht V i j α d

theorem assembledFlux_eq_flux (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, PlaneHk Set.univ (k + 1) (h i)) (i : ι) :
    P.assembledFlux t ht V i = P.flux t ht V i := by
  apply planeCarrier_eq_of_value_ae
  exact (P.assembledFlux_raw t ht V i).trans (P.flux_raw t ht V i).symm

end PlaneKernelOperator
end

end AVRegularity.KernelEnergyPlane
end
end
end
