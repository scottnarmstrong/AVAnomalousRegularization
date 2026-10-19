-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.CycleJoint.PeriodizedFamilyGlobalReadout
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSolutionExistence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The entire actual physical coupling flux reads the finite weighted native Sobolev operators of the original constituents. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeRawCouplingFlux_family_native_rows
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (t : ℝ)
    (v : ι) (k : Fin 2)
    (hc : ∀ u (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) j,
      Continuous (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t
        (K u + 1) k j))
    (M : ∀ u, F.Γ v u → (F.locally_finite t t).toFinset → JetIndex2 (K u + 1) → ℝ)
    (hM : ∀ u γ p j, 0 ≤ M u γ p j)
    (hb : ∀ u (γ : F.Γ v u) (p : (F.locally_finite t t).toFinset) j x,
      |pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t
        (K u + 1) k j x| ≤ M u γ p j)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    (fun x => planeRawCouplingFlux K D t (edgeCoefficient F ν e E actual K) U v x k) =ᵐ[volume]
      fun x => ∑ u, ∑ γ : F.Γ v u, ∑ p : (F.locally_finite t t).toFinset,
        F.weight p t • planeScalarJetRow
          (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t
            (K u + 1) k)
          (hc u γ p) (M u γ p) (hM u γ p) (hb u γ p)
          (mapPlaneHk (F.identity v u γ).map (U u)) x := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ u, ∀ γ : F.Γ v u,
      (∑ d : admissibleOrders K D v u,
        constituentPhysical F ν e E actual v u γ d t x
          (WithLp.toLp 2 (planeNativeJetExtension (U u) x (d.1 - 1)))) k =
        ∑ p : (F.locally_finite t t).toFinset, F.weight p t • planeScalarJetRow
          (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t
            (K u + 1) k)
          (hc u γ p) (M u γ p) (hM u γ p) (hb u γ p)
          (mapPlaneHk (F.identity v u γ).map (U u)) x := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro γ
    exact constituentPhysical_flux_jet_row_ae F K hdesc ν e E actual t v u γ k
      (K u + 1) (by have hh := hdesc v u γ; omega)
      (hc u γ) (M u γ) (hM u γ) (hb u γ) (U u)
  filter_upwards [hall] with x hx
  rw [planeRawCouplingFlux_family_constituents F K ν e E actual U v t x]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro γ hγ
  simpa only [WithLp.ofLp_sum, Finset.sum_apply] using hx u γ

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The inherited cell source retains its spatial reserve from the original independent family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceCoefficient_contDiff
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : 0 < ν) (he : e ≠ 0) (hE : E ≠ 0) (K : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E K)
    (actual : ∀ p, Ctx p) (s : ℝ) (yc : Vec 2) (v u : ι)
    (d : admissibleOrders K D v u) (t : ℝ)
    (ht : t ∈ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    ContDiff ℝ (K v : ℕ)
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d t) := by
  have hscale : 0 < (e⁻¹) ^ 2 * ν := mul_pos (sq_pos_of_ne_zero (inv_ne_zero he)) hν
  have ht' : t ∈ Set.Icc (((e⁻¹) ^ 2 * ν) * a) (((e⁻¹) ^ 2 * ν) * b) := by
    simpa only [mul_assoc] using ht
  have htime : ((e⁻¹) ^ 2 * ν)⁻¹ * t = ν⁻¹ * (e ^ 2 * t) := by
    rw [mul_inv_rev, inv_pow, inv_inv, mul_assoc]
  have hh := affineTimeScaledCoefficient_contDiff (K v) a b ((e⁻¹) ^ 2 * ν) hscale
    ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) e yc
    (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d)
    (fun r hr => reference_edgeCoefficient_spatial_smooth F hc ν e E hE K hs actual K v u d s r hr)
    t ht'
  change ContDiff ℝ (K v : ℕ) (fun z => ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
    edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d
      (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
  simpa only [htime] using hh

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Finite sums of retained raw forcing maps have exactly the summed native readout. -/

variable {E X J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X] [Fintype J]

local instance rawSumNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance rawSumNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance rawSumLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance rawSumLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

theorem planeTimeAllMomentCarrier_sum_ae
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : J → PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :
    (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (∑ j, f j) t) =ᵐ[μ]
      fun t => ∑ j, planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (f j) t := by
  classical
  rw [map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (f j))] with t ht
  simpa only [Finset.sum_apply] using ht

theorem planeRaw_allMoment_linearMap_sum
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H : J → X → ℝ → Vec 2 → E)
    (T : J → X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (hT : ∀ j, IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ (H j) (T j)) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ zc μ
      (fun x t z => ∑ j, H j x t z) (∑ j, T j) := by
  classical
  intro x
  have hsum := planeTimeAllMomentCarrier_sum_ae K ϖ ρ zc μ (fun j => T j x)
  have hall := ae_all_iff.mpr (fun j => hT j x)
  filter_upwards [hsum, hall] with t ht hread
  simp only [LinearMap.sum_apply]
  rw [ht]
  have hh := planeJetOrder_finite_sum_ae (Nat.zero_le K)
    (fun j => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T j x) t) (fun i => Fin.elim0 i)
  have hr := ae_all_iff.mpr hread
  filter_upwards [hh, hr] with z hz hzread
  change planeJetOrder _ 0 _ z = _
  exact hz.trans (Finset.sum_congr rfl (fun j _ => hzread j))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Weighted AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Explicit gradients of the static polynomial moments used for qualitative preparation energy. -/

/-- A normalized affine coordinate has its literal coordinate derivative. -/
theorem momentCoordinate_gradient (ϖ : ℝ) (zc z : Vec 2) (i k : Fin 2) :
    fderiv ℝ (fun x : Vec 2 => ϖ * (x i - zc i)) z (basisVec k) =
      ϖ * (if k = i then 1 else 0) := by
  rw [fderiv_const_mul ((differentiableAt_apply i z).sub_const (zc i)),
    fderiv_sub_const, (hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv]
  fin_cases i <;> fin_cases k <;> simp [basisVec]

/-- The quadratic moment base has the exact gradient in each coordinate. -/
theorem planeMomentBase_gradient (ϖ : ℝ) (zc z : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun x : Vec 2 =>
      1 + ϖ ^ 2 * ((x 0 - zc 0) ^ 2 + (x 1 - zc 1) ^ 2)) z (basisVec k) =
      2 * ϖ ^ 2 * (z k - zc k) := by
  have he : (fun x : Vec 2 =>
      1 + ϖ ^ 2 * ((x 0 - zc 0) ^ 2 + (x 1 - zc 1) ^ 2)) =
      fun x => 1 + (ϖ * (x 0 - zc 0)) ^ 2 + (ϖ * (x 1 - zc 1)) ^ 2 := by
    funext x
    ring
  rw [he, quadratic_weight_gradient _ _ (by fun_prop) (by fun_prop)]
  simp_rw [momentCoordinate_gradient]
  fin_cases k <;> norm_num <;> ring

/-- Every polynomial moment has a finite explicit gradient, including degree zero. -/
theorem planeMomentPolynomial_gradient (m : ℕ) (ϖ : ℝ) (zc z : Vec 2) (k : Fin 2) :
    fderiv ℝ (planeMomentPolynomial m ϖ zc) z (basisVec k) =
      (m : ℝ) *
        (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ (m - 1) *
        (2 * ϖ ^ 2 * (z k - zc k)) := by
  unfold planeMomentPolynomial
  rw [polynomial_weight_gradient _ (by fun_prop), planeMomentBase_gradient]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact finite weighted geometry energy periodizes every actual component and its lift. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_finiteGeometry_family_periodization (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (a b ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hlift : ∀ i, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤) :
    ∃ (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsPeriodizedFamilyPair K a b u w U W := by
  have hex (i : ι) : ∃ (U : ℝ → TorusHk (K i) (h i)) (W : ℝ → TorusHk (K i + 1) (h i)),
      ContinuousOn U (Set.Icc a b) ∧ MemLp W 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ (K i)) (W t) = U t) ∧
      (∀ t ∈ Set.Icc a b, ∀ α, (U t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (u i t).toFunction.jet α) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ α, (W t).val α =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (w i t).toFunction.jet α) := by
    obtain ⟨C, hC, hb, hg⟩ := finite_geometry_energy_component π hπ K 4 ϖ z ρ a b u w he i
    exact exists_polynomialProduction_trace_lift a b (u i) (w i) (hu i) (hw i) (hlift i)
      ϖ hϖ z ρ hρ C hC hb hg
  choose U W hc hW hl hr hWr using hex
  exact ⟨U, W, hc, hW, hl, hr, hWr⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Positive native map prices sum before squaring, preserving original
identity budgets through arbitrary finite assembly. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

theorem planeAllMoment_map_sum_positive_price_density
    {ι : Type*} [Fintype ι] (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (T : ι → X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (price : ι → ℝ) (hp : ∀ i, 0 ≤ price i) (B : X → ℝ → Vec 2 → ℝ)
    (hB : ∀ x, ∀ᵐ t ∂μ, ∀ z, 0 ≤ B x t z)
    (hb : ∀ i x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T i x) t) z ≤
        price i ^ 2 * B x t z) :
    ∀ x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ ((∑ i, T i) x) t) z ≤
        (∑ i, price i) ^ 2 * B x t z := by
  classical
  intro x
  have hall : ∀ᵐ t ∂μ, ∀ i, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T i x) t) z ≤
        price i ^ 2 * B x t z := ae_all_iff.mpr (fun i => hb i x)
  have he := planeTimeAllMomentCarrier_sum_ae K ϖ ρ zc μ (fun i => T i x)
  simp only [LinearMap.sum_apply]
  filter_upwards [hall, he, hB x] with t ht heq hBt
  rw [heq]
  exact nativeFactorialDensity_sum_price_le ρ
    (fun i => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (T i x) t) price hp (B x t) hBt ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Weighted AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomial moments have a uniform relative gradient budget. -/

/-- Each normalized displacement is bounded by the quadratic moment base. -/
theorem momentCoordinate_abs_le_base (ϖ : ℝ) (zc z : Vec 2) (k : Fin 2) :
    |ϖ * (z k - zc k)| ≤
      1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2) := by
  have hh := abs_le_one_add_sq (ϖ * (z k - zc k))
  have h0 := sq_nonneg (ϖ * (z 0 - zc 0))
  have h1 := sq_nonneg (ϖ * (z 1 - zc 1))
  fin_cases k <;> norm_num at hh ⊢ <;> nlinarith only [hh, h0, h1]

/-- The relative gradient grows only linearly with degree and spatial normalization. -/
theorem planeMomentPolynomial_gradient_abs_le (m : ℕ) (ϖ : ℝ) (zc z : Vec 2)
    (k : Fin 2) :
    |fderiv ℝ (planeMomentPolynomial m ϖ zc) z (basisVec k)| ≤
      (2 * (m : ℝ) * |ϖ|) * planeMomentPolynomial m ϖ zc z := by
  rw [planeMomentPolynomial_gradient]
  cases m with
  | zero => simp [planeMomentPolynomial]
  | succ m =>
    let B := 1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hc : |ϖ * (z k - zc k)| ≤ B := momentCoordinate_abs_le_base ϖ zc z k
    have hs : |2 * ϖ ^ 2 * (z k - zc k)| =
        2 * |ϖ| * |ϖ * (z k - zc k)| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    change |(m + 1 : ℕ) * B ^ (m + 1 - 1) * (2 * ϖ ^ 2 * (z k - zc k))| ≤
      (2 * (m + 1 : ℕ) * |ϖ|) * B ^ (m + 1)
    have hnat : 0 ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Nat.add_sub_cancel, abs_mul, hs, abs_mul, abs_of_nonneg hnat,
      abs_of_nonneg (pow_nonneg hB m), pow_succ]
    have hh := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (m + 1)) (pow_nonneg hB m))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg ϖ)))
    nlinarith only [hh]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Uniqueness for strictly triangular systems with arbitrary finite coefficient amplitude. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem triangularWeakSolution_unique (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hmv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (C : ∀ i, Fin (K i + 1) → ℝ)
    (hC : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ C i l)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hmA : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ t ∈ Set.Icc a b, ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))

    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hν : 0 < ν)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (α B lam : ℝ)
    (hα : 0 ≤ α) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (r : ι → ℕ) (hr : ∀ i i', ¬ r i' < r i → ∀ d, A i i' d = 0)
    (u' : ∀ i, ℝ → TorusHk (K i) (h i)) (w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  obtain ⟨π, hπ, hschur⟩ := exists_triangularCoefficientSchur ν ρ K D a b A hν hρ hA r hr
  exact plainWeakSolution_unique K D ν ρ hρ a b hab v hmv hv hvp V hV hvb C hC
    A hA hmA hc hp F g w u f hF hg hsol hν π hπ Kmax hK α B lam hα hB hlam
    hsmall hstrain hd hjets hschur u' w' hsol'

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Compact smooth spacetime tests define strong H1 time curves. -/

theorem compactSpacetimeH1_strong_time (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (a b : ℝ) :
    CycleEvolution.StrongTimeRegularity a b (compactSpacetimeH1 f hf hs)
      (compactSpacetimeH1 (spacetimeDirectionalField f (1, 0))
        (spacetimeDirectionalField_smooth f hf (1, 0))
        (spacetimeDirectionalField_compact f hs (1, 0))) := by
  let D := spacetimeDirectionalField f (1, 0)
  have hD := spacetimeDirectionalField_smooth f hf (1, 0)
  have hsD := spacetimeDirectionalField_compact f hs (1, 0)
  apply planeHk_strong_time_of_jets
  rintro ⟨⟨n, hn⟩, w⟩
  have hn1 : n ≤ 1 := Nat.le_of_lt_succ hn
  interval_cases n
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact compactScalar_native_strong_time f (hf.of_le (by simp)) hs a b _ _
      (compactSpacetimeH1_value_ae f hf hs)
      (compactSpacetimeH1_value_ae D hD hsD)
  · let v : ℝ × Vec 2 := (0, basisVec (w 0))
    let G := spacetimeDirectionalField f v
    have hG := spacetimeDirectionalField_smooth f hf v
    have hsG := spacetimeDirectionalField_compact f hs v
    apply compactScalar_native_strong_time G (hG.of_le (by simp)) hsG a b _ _
    · exact fun t => compactSpacetimeH1_gradient_ae f hf hs t w
    · intro t
      apply (compactSpacetimeH1_gradient_ae D hD hsD t w).trans
      apply Filter.Eventually.of_forall
      intro x
      exact smoothField_directional_derivative_commute f (hf.of_le (by simp))
        (t, x) (1, 0) v

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Every bounded drift admits a static polynomial chart certificate for identity diffusion. -/

def staticPolynomialChartRate (ϖ M : ℝ) (m : ℕ) : ℝ :=
  4 * (2 * (m : ℝ) * |ϖ|) ^ 2 + 4 * M ^ 2 + 1

def staticPolynomialChartConstant (S ϖ M : ℝ) (m : ℕ) : ℝ :=
  1 + S * staticPolynomialChartRate ϖ M m

/-- The polynomial moment itself, with its gradient as flux, gives a genuine chart certificate. -/
def staticPolynomialChartWeights (v : ℝ → Vec 2 → Vec 2) (t₀ S ϖ M : ℝ)
    (zc : Vec 2) (N : ℕ) (hS : 0 < S) (hM : 0 ≤ M)
    (hv : ∀ t ∈ Set.Icc t₀ (t₀ + S), ∀ z, ‖v t z‖ ≤ M) :
    ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v
      t₀ S ϖ zc N (staticPolynomialChartConstant S ϖ M) where
  W m _ := planeMomentPolynomial m ϖ zc
  Phi m _ z k := fderiv ℝ (planeMomentPolynomial m ϖ zc) z (basisVec k)
  lam := staticPolynomialChartRate ϖ M
  smooth := by
    intro m _
    have hW : ContDiff ℝ 2 (planeMomentPolynomial m ϖ zc) := by
      unfold planeMomentPolynomial
      fun_prop
    refine ⟨hW.comp contDiff_snd, ?_⟩
    apply contDiff_pi.mpr
    intro k
    exact ((hW.fderiv_right (m := 1) (by norm_num)).comp contDiff_snd).clm_apply
      contDiff_const
  pos := by
    intro m _ t z
    unfold planeMomentPolynomial
    positivity
  comparable := by
    intro m _ t _ z
    have hr : 0 ≤ staticPolynomialChartRate ϖ M m := by
      unfold staticPolynomialChartRate
      positivity
    have hc : 1 ≤ staticPolynomialChartConstant S ϖ M m := by
      unfold staticPolynomialChartConstant
      exact le_add_of_nonneg_right (mul_nonneg hS.le hr)
    have hp : 0 ≤ planeMomentPolynomial m ϖ zc z := by
      unfold planeMomentPolynomial
      positivity
    constructor
    · exact (mul_le_mul_of_nonneg_right
        ((inv_le_one₀ (zero_lt_one.trans_le hc)).mpr hc) hp).trans_eq (one_mul _)
    · exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hc hp)
  defect := by
    intro m _ t ht z
    have he (k : Fin 2) :
        (fun z' : Vec 2 => ∑ j : Fin 2,
          (1 : Matrix (Fin 2) (Fin 2) ℝ) k j *
            fderiv ℝ (planeMomentPolynomial m ϖ zc) z' (basisVec j)) =
          fun z' => fderiv ℝ (planeMomentPolynomial m ϖ zc) z' (basisVec k) := by
      funext z'
      simp [Matrix.one_apply, Finset.sum_ite_eq]
    simp only [he, deriv_const, zero_add]
    refine add_le_add ?_ le_rfl
    apply staticWeight_drift_budget hM
    · unfold planeMomentPolynomial
      positivity
    · intro k
      have hh := norm_le_pi_norm (v t z) k
      have hk : |v t z k| ≤ ‖v t z‖ := by
        simpa only [Real.norm_eq_abs] using hh
      exact hk.trans (hv t ht z)
    · intro k
      exact planeMomentPolynomial_gradient_abs_le m ϖ zc z k
  bound := by
    intro m _ t _ z
    apply staticWeight_gradient_flux_budget (by positivity)
    · unfold planeMomentPolynomial
      positivity
    · intro k
      exact planeMomentPolynomial_gradient_abs_le m ϖ zc z k
  lam_bound := by
    intro m _
    have hr : 0 ≤ staticPolynomialChartRate ϖ M m := by
      unfold staticPolynomialChartRate
      positivity
    refine ⟨hr, ?_⟩
    apply (le_div_iff₀ hS).mpr
    unfold staticPolynomialChartConstant
    rw [mul_comm]
    exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! A constructed metric-source forcing map is unchanged by a time-window clamp. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  {K : ι → ℕ} {D : ℕ}
  {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)}

theorem planeMetricSource_raw_map_window_congr
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (i : ι) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier
      (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b)))
    (hT : IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b))
      (fun x t => planeRawCouplingFlux K D t
        (planeMetricSourceCoefficient K D G A) (fun j => w x j t) i) T)
    (heq : ∀ t ∈ Set.Icc a b, G' t = G t) :
    IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b))
      (fun x t => planeRawCouplingFlux K D t
        (planeMetricSourceCoefficient K D G' A) (fun j => w x j t) i) T := by
  exact planeRaw_allMoment_linearMap_window_congr (K i) ϖ ρ zc a b
    (fun x t => planeRawCouplingFlux K D t
      (planeMetricSourceCoefficient K D G A) (fun j => w x j t) i)
    (fun x t => planeRawCouplingFlux K D t
      (planeMetricSourceCoefficient K D G' A) (fun j => w x j t) i)
    T hT (fun x t ht =>
      planeMetricSource_raw_flux_congr_time (heq t ht) (fun j => w x j t) i)
end

/-! Raw coupled forcing maps depend only on their coefficient slices on the native window. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {X : Type*} [AddCommGroup X] [Module ℝ X]
  {K : ι → ℕ} {D : ℕ}
  {A A' : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem planeRawCouplingFlux_congr_time {t : ℝ}
    (heq : ∀ i j d, A' i j d t = A i j d t)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D t A' w i = planeRawCouplingFlux K D t A w i := by
  funext z
  simp only [planeRawCouplingFlux, heq]

theorem planeRaw_coupling_map_window_congr
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (i : ι) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ)
    (T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier
      (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b)))
    (hT : IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b))
      (fun x t => planeRawCouplingFlux K D t
        A (fun j => w x j t) i) T)
    (heq : ∀ i j d t, t ∈ Set.Icc a b → A' i j d t = A i j d t) :
    IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ zc
      (volume.restrict (Set.Icc a b))
      (fun x t => planeRawCouplingFlux K D t
        A' (fun j => w x j t) i) T := by
  exact planeRaw_allMoment_linearMap_window_congr (K i) ϖ ρ zc a b
    (fun x t => planeRawCouplingFlux K D t
      A (fun j => w x j t) i)
    (fun x t => planeRawCouplingFlux K D t
      A' (fun j => w x j t) i)
    T hT (fun x t ht =>
      planeRawCouplingFlux_congr_time (fun i j d => heq i j d t ht) (fun j => w x j t) i)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Smooth scalar spacetime tests in fixed Hilbert directions have strong H1 time data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def compactSpacetimeVectorH1 (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (e : E) (t : ℝ) : PlaneHk univ 1 E :=
  mapPlaneHkOperator 1 ((ContinuousLinearMap.id ℝ ℝ).smulRight e)
    (compactSpacetimeH1 f hf hs t)

theorem compactSpacetimeVectorH1_strong_time (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (e : E) (a b : ℝ) :
    CycleEvolution.StrongTimeRegularity a b (compactSpacetimeVectorH1 f hf hs e)
      (compactSpacetimeVectorH1 (spacetimeDirectionalField f (1, 0))
        (spacetimeDirectionalField_smooth f hf (1, 0))
        (spacetimeDirectionalField_compact f hs (1, 0)) e) :=
  (compactSpacetimeH1_strong_time f hf hs a b).map
    (mapPlaneHkOperator 1 ((ContinuousLinearMap.id ℝ ℝ).smulRight e))

theorem compactSpacetimeVectorH1_time_memLp {a b : ℝ} (hab : a ≤ b)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (e : E) :
    MemLp (compactSpacetimeVectorH1 f hf hs e) 2 (volume.restrict (Icc a b)) :=
  strongTime_memLp hab (compactSpacetimeVectorH1_strong_time f hf hs e a b) 2

theorem compactSpacetimeVectorH1_value_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (e : E) (t : ℝ) :
    (compactSpacetimeVectorH1 f hf hs e t).val (valueIndex2 1)
      =ᵐ[volume.restrict univ] fun x => f (t, x) • e := by
  rw [compactSpacetimeVectorH1, mapPlaneHkOperator_apply, mapPlaneHk_component]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    ((ContinuousLinearMap.id ℝ ℝ).smulRight e)
      ((compactSpacetimeH1 f hf hs t).val (valueIndex2 1)),
    compactSpacetimeH1_value_ae f hf hs t] with x hx hfvalue
  rw [hx, hfvalue]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Literal value, gradient and L2 pairings of compact spacetime Hilbert tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem compactSpacetimeVectorH1_valueOperator_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (e : E) (t : ℝ) :
    planeHkValueOperator 1 (compactSpacetimeVectorH1 f hf hs e t)
      =ᵐ[volume] fun x => f (t, x) • e := by
  rw [planeHkValueOperator_apply]
  apply (univToPlane_ae _).trans
  simpa only [Measure.restrict_univ] using compactSpacetimeVectorH1_value_ae f hf hs e t

theorem compactSpacetimeVectorH1_L2_pair (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (e : E) (t : ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ u (planeHkValueOperator 1 (compactSpacetimeVectorH1 f hf hs e t)) =
      ∫ x, f (t, x) * inner ℝ (u x) e := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactSpacetimeVectorH1_valueOperator_ae f hf hs e t] with x hx
  rw [hx, real_inner_smul_right]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual admissible source rows spend their two original-mass Schur sums and gradient dissipation, with a fixed maximal-order price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCouplingSourceRow_weighted_gradient_schur_budget
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ i u, (d : admissibleOrders K D i u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i u d, coefficientSeminorm ρ (K i) a b (A i u d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i u d, ContDiff ℝ (K i : ℕ) (A i u d t))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
    (he : ∀ u, weightedGradFactorialNormSq n ϖ zc ρ (K u) (U u) ≠ ⊤) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i)
      (∑ u, ∑ d : admissibleOrders K D i u,
        planeCoupledFluxTerm ρ hρ K D a b i u d (A i u d) (hA i u d) t ht (hC i u d) (U u))) ≤
      ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
        ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq n ϖ zc ρ (K u) (U u) := by
  classical
  let T := fun i u (d : admissibleOrders K D i u) =>
    planeCoupledFluxTerm ρ hρ K D a b i u d (A i u d) (hA i u d) t ht (hC i u d) (U u)
  have hD (i u : ι) (d : admissibleOrders K D i u) :
      JetMemL2On Set.univ (fun β x => planeMomentSquareRoot n ϖ zc x • (T i u d).toFunction.jet β x) :=
    planeCoupledFluxTerm_polynomial_weighted_memL2
      ρ hρ K D a b i u d (A i u d) (hA i u d) t ht (hC i u d) n ϖ zc (U u) (he u)
  let edge := fun i u => ∑ d : admissibleOrders K D i u, T i u d
  have hDe (i u : ι) : JetMemL2On Set.univ
      (fun β x => planeMomentSquareRoot n ϖ zc x • (edge i u).toFunction.jet β x) :=
    scalarWeightedJet_memL2_sum _ (T i u) (hD i u)
  let price := couplingReserveBudget ρ K D a b A
  have hp (i u : ι) : 0 ≤ price i u := by
    unfold price couplingReserveBudget
    apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg ENNReal.toReal_nonneg
    unfold derivativeReserveFactor
    positivity
  have hM : massConjugatedMatrix π price = schurMatrix 1 ρ π K D a b A := by
    funext i u
    simpa only [massConjugatedMatrix, div_one] using
      couplingReserveBudget_schurMatrix 1 ρ π K D a b A i u
  let x := fun u => ‖polynomialWeightedGradientJet n ϖ zc ρ hρ (U u) (he u)‖
  have hn (i u : ι) :
      ‖scalarWeightedFactorialJet ρ (planeMomentSquareRoot n ϖ zc) (edge i u) (hDe i u)‖ ≤
      Real.sqrt ((2 : ℝ) ^ D) * price i u * x u := by
    rw [scalarWeightedFactorialJet_sum ρ _ (T i u) (hD i u) (hDe i u)]
    calc
      _ ≤ ∑ d : admissibleOrders K D i u,
          ‖scalarWeightedFactorialJet ρ (planeMomentSquareRoot n ϖ zc) (T i u d) (hD i u d)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d : admissibleOrders K D i u,
          Real.sqrt ((2 : ℝ) ^ D) *
            ((coefficientSeminorm ρ (K i) a b (A i u d)).toReal *
              derivativeReserveFactor ρ (K i) (d.1 - 2)) * x u := by
        apply Finset.sum_le_sum
        intro d _
        have hh := planeCoupledFluxTerm_weighted_gradient_norm
          ρ hρ K D a b i u d (A i u d) (hA i u d) t ht (hC i u d) n ϖ zc (U u) (he u) (hD i u d)
        have hcost : 0 ≤ (coefficientSeminorm ρ (K i) a b (A i u d)).toReal *
            derivativeReserveFactor ρ (K i) (d.1 - 2) * x u := by
          unfold derivativeReserveFactor x
          positivity
        exact hh.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (admissibleDerivativeWord_sqrt_card_le K D i u d) hcost)
      _ = _ := by
        simp only [price, couplingReserveBudget, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hs := scalarWeightedFactorialRow_schur_budget K ρ (planeMomentSquareRoot n ϖ zc)
    π hπ price hp (Real.sqrt ((2 : ℝ) ^ D)) θ (Real.sqrt_nonneg _)
    (by simpa only [hM] using hrow) (by simpa only [hM] using hcol)
    edge x (fun u => norm_nonneg _) hDe (fun i => scalarWeightedJet_memL2_sum _ (edge i) (hDe i))
    (fun i u => by
      rw [← scalarWeightedFactorialJet_normSq ρ _ (edge i u) (hDe i u)]
      exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hp i u)) (norm_nonneg _))).mpr (hn i u)))
  have hq : (fun z => planeMomentSquareRoot n ϖ zc z ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  simp only [hq, ← weightedFactorialNormSq_stored_readout,
    x, polynomialWeightedGradientJet_normSq] at hs
  exact hs

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! All literal homogeneous integral atoms retain their image price and genuine torus time readout. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem homogeneousIntegralAtoms_actual_time_transfer (K : ι → ℕ) (D : ℕ) (i : ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (S : Set ℝ) (hS : MeasurableSet S)
    (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ S, Continuous (v t))
    (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ S, ∀ x, ‖v t x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hc : ∀ i' d t, t ∈ S → Continuous (A i i' d t))
    (hj : ∀ i' d, Measurable (Function.uncurry (A i i' d)))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ)
    (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d t, t ∈ S → ∀ x, ‖A i i' d t x‖ ≤ MC i' d)
    (hpA : ∀ i' d t, t ∈ S → AVenhance.IsZ2Periodic (A i i' d t))
    (f : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hf : ∀ i, MemLp (f i) 2 μ) (z : Vec 2)
    (M : ι → ℝ → ℝ) (hM : ∀ i, MemLp (M i) 2 μ)
    (hw : ∀ i α, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) volume)
    (hb : ∀ i α, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M i t‖)
    (T : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hr : ∀ i α, ∀ᵐ t ∂μ, (T i t).toFunction.jet α =ᵐ[volume]
      periodizeRawJet (f i t).toFunction.jet α)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let G := fun j (n : Fin 2 → ℤ) => planeHomogeneousIntegralAtom K D ν v A
      (fun i t => planeCarrierTranslation (K i + 1) (AVenhance.latticeShift n) (f i t)) i ψ j
    let P := torusHomogeneousIntegralAtom K D ν v A T i ψ
    ∀ j : Fin 3, (∀ n, Integrable (G j n) μ) ∧
      Summable (fun n => ∫ t, ‖G j n t‖ ∂μ) ∧ Integrable (P j) μ ∧
      (∑' n, ∫ t, G j n t ∂μ) = ∫ t, P j t ∂μ := by
  dsimp only
  intro j
  unfold planeHomogeneousIntegralAtom torusHomogeneousIntegralAtom homogeneousWeakRhsIntegralAtom
  split_ifs
  · exact drift_actual_time_transfer μ S hS hSae v hv hvm V hV hbv
      (Metric.ball (0 : Vec 2) 2) 2 (by norm_num) Set.Subset.rfl
      (f i) (hf i) z
      (fun k => ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ) (fun _ => valueIndex2 1)
      (fun _ => unitPatchLocalization_jet_ball_support_ae hζ 1 φ (valueIndex2 1))
      (M i) (hM i) (fun k => hw i _) (fun k => hb i _) (T i) (fun k => hr i _)
  · exact diffusion_actual_time_transfer μ (Metric.ball (0 : Vec 2) 2)
      2 (by norm_num) Set.Subset.rfl ν (f i) (hf i) z
      (fun k => ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ)
      (fun k => ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun k => unitPatchLocalization_jet_ball_support_ae hζ 1 φ _)
      (M i) (hM i) (fun k => hw i _) (fun k => hb i _) (T i) (fun k => hr i _)
  · exact coupling_actual_time_transfer K D i μ S hS hSae A hc hj MC hMC hbA hpA
      f hf z M hM hw hb T hr hζ φ

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal forcing on the original constituent graph has source degree one. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h V E : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem nativeRawOriginalFamilyMap_edge_zero
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H : ∀ v u, F.Γ v u → V u → ℝ → Vec 2 → E v)
    (hH : ∀ v u γ, ∀ᵐ t ∂μ, H v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (T : ∀ v, (∀ u, V u) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ)
    (hT : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ
      (fun x t z => ∑ u, ∑ γ, H v u γ (x u) t z) (T v))
    (v u : ι) (hΓ : ¬ Nonempty (F.Γ v u)) : nativeFamilyMapEdge T v u = 0 := by
  classical
  have : IsEmpty (F.Γ v u) := ⟨fun γ => hΓ ⟨γ⟩⟩
  apply planeRaw_allMoment_map_eq_zero_of_ae (K v) ϖ ρ zc μ
    (fun x t z => ∑ j, ∑ γ, H v j γ (Pi.single u x j) t z) _
    (planeRaw_allMoment_linearMap_comp (K v) ϖ ρ zc μ _ (T v) (hT v)
      (LinearMap.single ℝ V u))
  intro x
  have ht : ∀ᵐ t ∂μ, ∀ j γ, H v j γ 0 t =ᵐ[volume] (fun _ => 0) :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (hH v j))
  filter_upwards [ht] with t ht
  have hz : ∀ᵐ z ∂volume, ∀ j γ, H v j γ 0 t z = 0 :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (ht j))
  filter_upwards [hz] with z hz
  apply Finset.sum_eq_zero
  intro j _
  by_cases hju : j = u
  · subst j
    exact Finset.sum_eq_zero (fun γ _ => isEmptyElim γ)
  · apply Finset.sum_eq_zero
    intro γ _
    rw [Pi.single_eq_of_ne hju]
    exact hz j γ

theorem nativeRawOriginalFamilyMap_response_sourceDegree
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H : ∀ v u, F.Γ v u → V u → ℝ → Vec 2 → E v)
    (hH : ∀ v u γ, ∀ᵐ t ∂μ, H v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (T : ∀ v, (∀ u, V u) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ)
    (hT : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ
      (fun x t z => ∑ u, ∑ γ, H v u γ (x u) t z) (T v))
    (R : ∀ v, PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ →ₗ[ℝ] V v) :
    HasSourceDegreeOn F 1 (nativeComponentResponseOperator R T) := by
  have he : nativeFamilyEdgeForcingMap (nativeFamilyMapEdge T) = T :=
    funext (nativeFamilyMapEdge_assembly T)
  have hd := nativeFamilyEdgeResponse_sourceDegree F (nativeFamilyMapEdge T)
    (nativeRawOriginalFamilyMap_edge_zero F K ϖ ρ zc μ H hH T hT) R
  rw [he] at hd
  exact hd

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual normalized reference coefficient is the finite original-identity
sum of the natural Taylor arrays and constructed native remainder arrays. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceCoefficient_constructed_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (v u : ι) (d : admissibleOrders K D v u) (Ks : ℕ) (s : ℝ)
    (yc z : Vec 2) (a b τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (htime : ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) :
    preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d τ z =
      ∑ γ : F.Γ v u, ∑ p ∈ (F.locally_finite tS tZ).toFinset,
        (naturalFamilyTaylorNativeArray Ks F p (actual p) v u γ
          (ν⁻¹ * e ^ 2) hφ (F.piece p).anchor s e E yc (d.val - 1) τ z +
        naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ
          (ν⁻¹ * e ^ 2) a b hφ (F.piece p).anchor s e E yc (d.val - 1) τ z) := by
  classical
  unfold preparationReferenceCellSourceCoefficient edgeCoefficient physicalCoefficient
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  have hd : 2 ≤ d.val := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).1
  have hh := normalized_reference_constituent_constructed_remainder_split F hc ν e E hν he
    actual v u γ d.val hd Ks s ⟨ν⁻¹ * (e ^ 2 * τ), htime⟩ yc z
    (ν⁻¹ * e ^ 2) a b τ hτ (mul_assoc _ _ _)
  simpa only [naturalFamilyTaylorNativeArray, mul_assoc] using hh

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Summed initial polynomial factorial energy with constants chosen before the fibers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_weighted_factorial_sum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E)
    (ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hmesh : ρ * (N : ℝ) ≤ L)
    (n : ℕ) (ϖ R : ℝ) (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R) (hscale : ϖ / (N : ℝ) ≤ R) :
    (∑ p : Fin 2 → Fin N, weightedFactorialNormSq n ϖ
      (spatialPatchCenter N (fun i => (p i : ℤ))) ρ K
      (spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f)) ≤
      ENNReal.ofReal ((1 + 2 * R ^ 2) ^ n * patchFactorialEnergyBudget hζ K L) *
        ENNReal.ofReal (factorialNormSq ρ f.val) := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin 2 → Fin N) _ =>
    spatialPatchLocalization_weightedFactorialNormSq_bound hζ N hN (fun i => (p i : ℤ))
      f ρ n ϖ R hϖ hR hscale)
  apply ht.trans
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => factorialNormSq_nonneg _ _)]
  have hs := ENNReal.ofReal_le_ofReal
    (spatialPatchLocalization_uniform_factorial_energy hζ N hN f ρ L hρ hL hmesh)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ENNReal.ofReal ((1 + 2 * R ^ 2) ^ n) from zero_le)
  rw [ENNReal.ofReal_mul (patchFactorialEnergyBudget_nonneg hζ K L)] at hm
  simpa only [ENNReal.ofReal_mul (show 0 ≤ (1 + 2 * R ^ 2) ^ n by positivity),
    mul_assoc] using hm

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal forcing on the original constituent graph has source degree one. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h V E : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem nativeRawOriginalFamilyMap_taylor_split_edges
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (H : ∀ v u, F.Γ v u → V u → ℝ → Vec 2 → E v)
    (hH : ∀ v u γ, ∀ᵐ t ∂μ, H v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (Tfull Rs : ∀ v, (∀ u, V u) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ)
    (hTaylor : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ
      (fun x t z => ∑ u, ∑ γ, H v u γ (x u) t z) (Tfull v - Rs v))
    (Hfull : ∀ v, (∀ u, V u) → ℝ → Vec 2 → E v)
    (hfull : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ (Hfull v) (Tfull v)) :
    ∃ Ledge : ∀ v u, V u →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ,
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ
        (Hfull v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ zc μ
        (fun x t z => ∑ u, ∑ γ, H v u γ (x u) t z) (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      ∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := E v) (K v) ϖ ρ zc μ →ₗ[ℝ] V v,
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) := by
  let Ledge := nativeFamilyMapEdge (fun v => Tfull v - Rs v)
  have he v : nativeFamilyEdgeForcingMap Ledge v = Tfull v - Rs v :=
    nativeFamilyMapEdge_assembly _ v
  refine ⟨Ledge, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [he, sub_add_cancel]
    exact hfull v
  · intro v
    rw [he]
    exact hTaylor v
  · exact nativeRawOriginalFamilyMap_edge_zero F K ϖ ρ zc μ H hH _ hTaylor
  · intro R
    have hmaps : nativeFamilyEdgeForcingMap Ledge = (fun v => Tfull v - Rs v) := funext he
    rw [hmaps]
    exact nativeRawOriginalFamilyMap_response_sourceDegree F K ϖ ρ zc μ H hH _ hTaylor R

end AVRegularity.CycleJointProofs
end
