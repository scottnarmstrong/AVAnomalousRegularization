-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneAllMomentFamilyInitialGradientBudget
public import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Unit-patch localization supplies finite polynomial moments for arbitrary torus data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The compact unit patch has finite genuine polynomial factorial energy. -/
theorem unitPatchLocalization_weightedFactorialNormSq_ne_top {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) {K : ℕ} (f : TorusHk K E) (ρ : ℝ) (n : ℕ)
    (ϖ : ℝ) (hϖ : 0 ≤ ϖ) :
    weightedFactorialNormSq n ϖ 0 ρ K
      (spatialPatchLocalization hζ 1 (by decide) 0 K f) ≠ ⊤ := by
  have hh := spatialPatchLocalization_weightedFactorialNormSq_bound hζ 1 (by decide)
    0 f ρ n ϖ ϖ hϖ hϖ (by simp)
  have hcenter : spatialPatchCenter 1 (0 : Fin 2 → ℤ) = 0 := by
    funext i
    simp [spatialPatchCenter]
  rw [hcenter] at hh
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  exact hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual continuous traces of a linear native response give endpoint operators before the datum is selected. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X]

local instance allMomentTraceMapNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k
local instance allMomentTraceMapNativeModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := allMomentTimeNativeModule k

theorem planeAllMoment_continuous_trace_linearMap (K : ℕ) (ϖ ρ a b : ℝ)
    (hab : a < b) (zc : Vec 2)
    (L : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ zc
      (volume.restrict (Set.Icc a b)))
    (u : X → ℝ → PlaneHk Set.univ K E) (w : X → ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ∀ x, ContinuousOn (u x) (Set.Icc a b))
    (htr : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (w x t) = u x t)
    (hw : ∀ x, PlaneTimeAllMomentRepresents (K + 1) ϖ ρ zc
      (volume.restrict (Set.Icc a b)) (L x) (w x))
    (τ : ℝ) (hτ : τ ∈ Set.Icc a b) :
    ∃ T : X →ₗ[ℝ] PlaneHk Set.univ K E, ∀ x, T x = u x τ := by
  let μ := volume.restrict (Set.Icc a b)
  have hadd (x y : X) : u (x + y) τ = u x τ + u y τ := by
    have hr := planeTimeAllMomentRepresents_add (E := E) (K + 1) ϖ ρ zc μ
      (L x) (L y) (w x) (w y) (hw x) (hw y)
    rw [← map_add] at hr
    have ht : ∀ᵐ t ∂μ, truncatePlaneHk (Nat.le_succ K) (w x t + w y t) =
        u x t + u y t := by
      filter_upwards [htr x, htr y] with t hx hy
      rw [map_add, hx, hy]
    exact planeAllMoment_same_carrier_continuous_traces K ϖ ρ a b hab zc (L (x + y))
      (u (x + y)) (fun t => u x t + u y t) (w (x + y)) (fun t => w x t + w y t)
      (hu (x + y)) (planeCarrierCurve_continuousOn_add _ _ _ (hu x) (hu y))
      (htr (x + y)) ht (hw (x + y)) hr hτ
  have hsmul (c : ℝ) (x : X) : u (c • x) τ = c • u x τ := by
    have hr : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ zc μ
        (L (c • x)) (fun t => c • w x t) := by
      rw [map_smul]
      filter_upwards [planeTimeAllMomentCarrier_smul (E := E) (K + 1) ϖ ρ zc μ c (L x),
        hw x] with t ht hx
      rw [ht, hx]
    have ht : ∀ᵐ t ∂μ, truncatePlaneHk (Nat.le_succ K) (c • w x t) = c • u x t := by
      filter_upwards [htr x] with t hx
      rw [map_smul, hx]
    exact planeAllMoment_same_carrier_continuous_traces K ϖ ρ a b hab zc (L (c • x))
      (u (c • x)) (fun t => c • u x t) (w (c • x)) (fun t => c • w x t)
      (hu (c • x)) (normedCurve_continuousOn_smul c _ _ (hu x))
      (htr (c • x)) ht (hw (c • x)) hr hτ
  refine ⟨{ toFun := fun x => u x τ
            map_add' := hadd
            map_smul' := fun c x => hsmul c x }, ?_⟩
  intro x
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Smooth pullback preserves support of every weak jet. Polynomial moments can
therefore be bounded on the pulled-back support, without adding input derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_pullback_jet_support_ae {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (S : Set (Vec 2))
    (hs : ∀ a : JetIndex2 K, ∀ᵐ x ∂volume, x ∉ S → U.toFunction.jet a x = 0)
    (a : JetIndex2 K) :
    ∀ᵐ x ∂volume, X x ∉ S → V.toFunction.jet a x = 0 := by
  have hinput := hμ.quasiMeasurePreserving.ae (ae_all_iff.mpr hs)
  have hd := planeSobolev_pullback_word_density_bound U V X hX hμ B hb hv
    1 zero_le_one (le_refl 1) a.1.val (Nat.le_of_lt_succ a.1.isLt) a.2
  filter_upwards [hinput, hd] with x hx hdx
  intro hxs
  have hzero : planeFactorialDensity 1 U (X x) = 0 := by
    unfold planeFactorialDensity
    apply Finset.sum_eq_zero
    intro β _
    rw [planeJetOrder_eq_stored (Nat.le_of_lt_succ β.1.isLt), hx β hxs,
      norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [hzero, mul_zero] at hdx
  have hweight := factorialWeight_pos_of_radius_pos 1 zero_lt_one a.1.val
  have hn : ‖planeJetOrder V a.1.val a.2 x‖ ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hdx hweight
  have heq : planeJetOrder V a.1.val a.2 x = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hn (sq_nonneg _)))
  simpa only [planeJetOrder_eq_stored (Nat.le_of_lt_succ a.1.isLt)] using heq

theorem planeHk_pullback_polynomial_energy_le_of_support {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (S : Set (Vec 2))
    (hs : ∀ a : JetIndex2 K, ∀ᵐ x ∂volume, x ∉ S → U.toFunction.jet a x = 0)
    (n : ℕ) (ϖ ρ : ℝ) (yc : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hpoly : ∀ x, X x ∈ S → planeMomentPolynomial n ϖ yc x ≤ C) :
    weightedFactorialNormSq n ϖ yc ρ K V ≤
      ENNReal.ofReal C * ENNReal.ofReal (factorialNormSq ρ V.val) := by
  rw [weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_supported_bound ρ _ V C hC
  intro a
  filter_upwards [planeHk_pullback_jet_support_ae U V X hX hμ B hb hv S hs a] with x hx
  intro hn
  apply hpoly
  by_contra hnot
  exact hn (hx hnot)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The inherited source in reference cell coordinates has a finite coefficient seminorm at every radius. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
  (s ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2)

def preparationReferenceCellSourceCoefficient (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
    edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d
      (ν⁻¹ * (e ^ 2 * t)) (yc + e • z)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem preparationReferenceCellSourceCoefficient_seminorm_ne_top
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (a b ρ r C : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (he : e ≠ 0) (B : ι → ι → ℝ)
    (hs : IsSampledEnvelope (referenceChartedFamily F hφ s) π K actual a b ν e E ρ C B)
    (v u : ι) (d : admissibleOrders K D v u) :
    coefficientSeminorm r (K v) ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d) ≠ ⊤ := by
  have hscale : 0 < (e⁻¹) ^ 2 * ν := mul_pos (sq_pos_of_ne_zero (inv_ne_zero he)) hν
  have htime (t : ℝ) : ((e⁻¹) ^ 2 * ν)⁻¹ * t = ν⁻¹ * (e ^ 2 * t) := by
    rw [mul_inv_rev, inv_pow, inv_inv, mul_assoc]
  have hA : coefficientSeminorm ρ (K v) a b
      (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d) ≠ ⊤ :=
    sampledEnvelope_edge_seminorm_ne_top (referenceChartedFamily F hφ s)
    π hπ K actual a b ν e E ρ C hν hρ B hs v u d
  have hh := coefficientSeminorm_affine_time_scaling_ne_top ρ r hρ (K v) a b
    ((e⁻¹) ^ 2 * ν) hscale ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) e yc
    (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d) hA
  have hcoeff : (fun t z => ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
      edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d
        (((e⁻¹) ^ 2 * ν)⁻¹ * t) (yc + e • z)) =
      preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d := by
    funext t z
    rw [htime]
    rfl
  rw [hcoeff] at hh
  simpa only [mul_assoc] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual admissible coefficient fluxes spend their original d-minus-two gradient reserve under polynomial weights. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupledFluxTerm_weighted_gradient_budget
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i u : ι) (d : admissibleOrders K D i u)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ (K u + 1) (h u))
    (he : weightedGradFactorialNormSq n ϖ zc ρ (K u) U ≠ ⊤) :
    weightedFactorialNormSq n ϖ zc ρ (K i)
      (planeCoupledFluxTerm ρ hρ K D a b i u d A hA t ht hC U) ≤
      ENNReal.ofReal ((coefficientSeminorm ρ (K i) a b A).toReal ^ 2) *
        ((Fintype.card (DerivativeWord2 (d.1 - 1)) : ℝ≥0∞) *
          (ENNReal.ofReal ((derivativeReserveFactor ρ (K i) (d.1 - 2)) ^ 2) *
            weightedGradFactorialNormSq n ϖ zc ρ (K u) U)) := by
  let T := planePositiveDerivativeTensor (d.1 - 1)
    (admissibleOrders_reserve K D i u d).1 (admissibleOrders_reserve K D i u d).2 U
  have hT := planePositiveDerivativeTensor_weighted_gradient_budget ρ hρ (d.1 - 1)
    (admissibleOrders_reserve K D i u d).1 (admissibleOrders_reserve K D i u d).2 n ϖ zc U
  change weightedFactorialNormSq n ϖ zc ρ (K i) T ≤ _ at hT
  simp only [Nat.sub_sub] at hT
  have hTe : weightedFactorialNormSq n ϖ zc ρ (K i) T ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he)) hT
  have hq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  have hstored : storedChartFactorialEnergy ρ (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) T ≠ ⊤ := by
    rw [hq, ← weightedFactorialNormSq_stored_readout]
    exact hTe
  have hD := weighted_raw_jets_memL2On_of_stored_energy ρ hρ _
    (planeMomentSquareRoot_continuous n ϖ zc) T hstored
  have hm := planeMultiplyIntervalCoefficient_weighted_factorialEnergy_le
    ρ hρ (K i) a b A hA t ht hC T _ hD
  rw [hq, ← weightedFactorialNormSq_stored_readout,
    ← weightedFactorialNormSq_stored_readout] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hT zero_le)

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual and frozen metrics have simultaneous uniform adjoint weights
 and an internally chosen finite reserve at every requested moment order. -/

theorem windowCover_uniform_subwindow_weights_with_fixed_reserve {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cw : ℕ → ℝ, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ N : ℕ, ∃ L : ℕ, 1 ≤ L ∧
      (∀ k ≤ N, Real.exp (18 * Cw k) / (L : ℝ) ^ 2 ≤ 1 / 16) ∧
    ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (M : ℕ) (κ : ℕ → ℝ),
      IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (ν B : ℝ), κ m = ν → κ (m - 1) = B →
    ∀ (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tA tZ ρs g g0 a B₀ lam Cb : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
      (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2),
      IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ →
      g0 ≤ 1 / 4 →
    ∀ (i : Fin (P + 2)) (u0 u1 : ℝ), u0 < u1 →
      Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i →
      u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let G := ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i)
    let v := ocCellDrift α q Λ ζ m ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i)
    let ϖ := ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)
    Nonempty (ChartWeights G v u0 (u1 - u0) ϖ 0 N Cw) ∧
      Nonempty (ChartWeights (fun t _ => G t 0) v u0 (u1 - u0) ϖ 0 N Cw) := by
  obtain ⟨Cw, Λ₀, hΛ₀, he⟩ :=
    windowCover_uniform_subwindow_adjoint_weights hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Cw, Λ₀, hΛ₀, ?_⟩
  intro N
  obtain ⟨L, hL, hreserve⟩ := exists_uniform_natural_scalar_square_reserve Cw N
  refine ⟨L, hL, hreserve, ?_⟩
  intro Λ hΛ Φ M κ hκ m hm hmM ν B hν hB hφ tA tZ ρs g g0 a B₀ lam Cb
    qJ Kmax CG l₀ P y₀ cov hg0 i u0 u1 hu hwindow hlength G v ϖ
  have hweights := he Λ hΛ Φ M κ hκ m hm hmM ν B hν hB hφ
    tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ cov hg0 i
  exact ⟨hweights G (Or.inl rfl) u0 u1 hu hwindow hlength N,
    hweights (fun t _ => G t 0) (Or.inr rfl) u0 u1 hu hwindow hlength N⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual native family forcing energies satisfy a quadratic addition bound without a component-count factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyEnergyAdditionNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyEnergyAdditionNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMomentFamilyEnergy_add_le
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W V : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ) :
    planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π (W + V) ≤
      2 * (planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π W +
        planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π V) := by
  let U := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ (W i)
  let U' := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ (V i)
  let Uadd := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ (W i + V i)
  let J := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i) (Uadd i t)
  let G := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i) (U i t)
  let H := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i) (U' i t)
  have hJ (i : ι) : AEMeasurable (J i) μ :=
    weightedFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i) ϖ ρ 0 μ (W i + V i))
  have hG (i : ι) : AEMeasurable (G i) μ :=
    weightedFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i) ϖ ρ 0 μ (W i))
  have hH (i : ι) : AEMeasurable (H i) μ :=
    weightedFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i) ϖ ρ 0 μ (V i))
  have hb (i : ι) : (∫⁻ t, J i t ∂μ) ≤ 2 *
      ((∫⁻ t, G i t ∂μ) + ∫⁻ t, H i t ∂μ) := by
    have he : (∫⁻ t, J i t ∂μ) =
        ∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ (K i) (U i t + U' i t) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [planeTimeAllMomentCarrier_add (E := E i) (K i) ϖ ρ 0 μ (W i) (V i)] with t ht
      dsimp only [J]
      rw [show Uadd i t = U i t + U' i t from ht]
    rw [he]
    exact integrated_weightedFactorialNormSq_add_le n ϖ 0 ρ μ _ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i) ϖ ρ 0 μ (W i))
  exact finite_mass_time_quadratic_addition μ (fun i => ENNReal.ofReal ((π i)⁻¹))
    J G H hJ hG hH hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Native all-moment lift carriers have finite original-mass gradient energy at every retained moment. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyGradientFiniteNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k

theorem planeAllMomentFamilyGradientEnergy_ne_top
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ) (π : ι → ℝ)
    (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) :
    planeAllMomentFamilyGradientEnergy K n ϖ ρ μ π X ≠ ⊤ := by
  unfold planeAllMomentFamilyGradientEnergy
  have hm (i : ι) := weightedGradFactorialNormSq_time_aemeasurable n ϖ 0 ρ μ _
    (planeTimeAllMomentCarrier_memLp (K i + 1) ϖ ρ 0 μ (X i))
  rw [lintegral_finsetSum' _ (fun i _ => (hm i).const_mul _)]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [lintegral_const_mul'' _ (hm i)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (integrated_weightedGradFactorialNormSq_ne_top_of_lift n ϖ 0 ρ hρ μ _
      (planeTimeAllMomentCarrier_moment (K i + 1) ϖ ρ 0 μ (X i) n))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual rough native chart pullback preserves the factorial norm at every certified radius. -/

def compositionFactorialNormBound (C : ℕ → ℝ) (K : ℕ) : ℝ :=
  Real.sqrt (∑ j : Fin (K + 1), (2 : ℝ) ^ j.val *
    (compositionFactorialOrderBound C j.val / (j.val.factorial : ℝ)) ^ 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkScaledPullback_factorial_norm_le {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk univ K E) :
    Real.sqrt (factorialNormSq ρ (planeHkSmoothPullback X hX hμ B hB hb U).val) ≤
      compositionFactorialNormBound C K * Real.sqrt (factorialNormSq ρ U.val) := by
  have hC j (hj : 1 ≤ j) (hjK : j ≤ K) : 0 ≤ C j :=
    (mul_nonneg (pow_nonneg hρ _) (hB j hj hjK)).trans (hscale j hj hjK)
  have hs := factorialNormSq_le_of_scaled_jets hρ (Real.sqrt_nonneg (factorialNormSq ρ U.val))
    (planeHkSmoothPullback X hX hμ B hB hb U).val (compositionFactorialOrderBound C)
    (fun n hn => compositionFactorialOrderBound_nonneg C n (fun j hj hjn => hC j hj (hjn.trans hn)))
    (fun n hn w => planeHkScaledPullback_component_le_factorial X hX hμ B hB hb hρ C hscale U n hn w)
  rw [Real.sq_sqrt (factorialNormSq_nonneg ρ U.val)] at hs
  have hsum : 0 ≤ ∑ j : Fin (K + 1), (2 : ℝ) ^ j.val *
      (compositionFactorialOrderBound C j.val / (j.val.factorial : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _))
  have hr := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul hsum] at hr
  exact hr

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite polynomial dissipation supplies all weighted raw jets of each actual admissible coupling term. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeCoupledFluxTerm_polynomial_weighted_memL2
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i u : ι) (d : admissibleOrders K D i u)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ (K u + 1) (h u))
    (he : weightedGradFactorialNormSq n ϖ zc ρ (K u) U ≠ ⊤) :
    JetMemL2On Set.univ (fun β x => planeMomentSquareRoot n ϖ zc x •
      (planeCoupledFluxTerm ρ hρ K D a b i u d A hA t ht hC U).toFunction.jet β x) := by
  have hb := planeCoupledFluxTerm_weighted_gradient_budget
    ρ hρ K D a b i u d A hA t ht hC n ϖ zc U he
  have hfinite : weightedFactorialNormSq n ϖ zc ρ (K i)
      (planeCoupledFluxTerm ρ hρ K D a b i u d A hA t ht hC U) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he))) hb
  have hq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  apply weighted_raw_jets_memL2On_of_stored_energy ρ hρ _
    (planeMomentSquareRoot_continuous n ϖ zc)
  rw [hq, ← weightedFactorialNormSq_stored_readout]
  exact hfinite

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! A single chart reserve bounds the factorial pullback price at every lower
physical slot, independently of the number of components. -/

theorem compositionFactorialNormBound_nonneg (C : ℕ → ℝ) (K : ℕ) :
    0 ≤ compositionFactorialNormBound C K := Real.sqrt_nonneg _

theorem compositionFactorialNormBound_mono (C : ℕ → ℝ) {J K : ℕ} (hJK : J ≤ K) :
    compositionFactorialNormBound C J ≤ compositionFactorialNormBound C K := by
  unfold compositionFactorialNormBound
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (2 : ℝ) ^ j *
    (compositionFactorialOrderBound C j / (j.factorial : ℝ)) ^ 2) (J + 1),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => (2 : ℝ) ^ j *
    (compositionFactorialOrderBound C j / (j.factorial : ℝ)) ^ 2) (K + 1)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hJK 1))
  intro j _ _
  exact mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A single selected moment reserve bounds every native family forcing and gradient energy below it. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyMomentMonoFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := inferInstance
local instance familyMomentMonoFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := inferInstance
local instance familyMomentMonoNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyMomentMonoFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k

theorem planeAllMomentFamilyGradientEnergy_moment_mono
    (K : ι → ℕ) {n N : ℕ} (hn : n ≤ N) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) :
    planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π W ≤
      planeAllMomentFamilyGradientEnergy (E := E) K N ϖ ρ μ π W := by
  apply lintegral_mono
  intro t
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (weightedGradFactorialNormSq_moment_mono hn ϖ 0 ρ (K i) _) zero_le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive partition prices assemble native forcings without a quantitative cardinality loss. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {L : Type*} [Fintype L]

omit [FiniteDimensional ℝ E] in
theorem positiveSubpartition_native_density_sum_le {K : ℕ}
    (ρ : ℝ) (μ : Measure ℝ) (V : L → ℝ → PlaneHk Set.univ K E)
    (w : L → ℝ → ℝ) (B : ℝ → Vec 2 → ℝ)
    (hw : ∀ᵐ t ∂μ, (∀ p, 0 ≤ w p t) ∧ ∑ p, w p t ≤ 1)
    (hB : ∀ᵐ t ∂μ, ∀ z, 0 ≤ B t z)
    (hb : ∀ p, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (V p t) z ≤ (w p t) ^ 2 * B t z) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (∑ p, V p t) z ≤ B t z := by
  classical
  have hall : ∀ᵐ t ∂μ, ∀ p, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (V p t) z ≤ (w p t) ^ 2 * B t z :=
    ae_all_iff.mpr hb
  filter_upwards [hw, hB, hall] with t ht hbt hterms
  have hs0 : 0 ≤ ∑ p, w p t := Finset.sum_nonneg (fun p _ => ht.1 p)
  have hs1 : (∑ p, w p t) ^ 2 ≤ 1 := by
    have hh := mul_le_mul ht.2 ht.2 hs0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [pow_two, one_mul] using hh
  filter_upwards [nativeFactorialDensity_sum_price_le ρ (fun p => V p t)
    (fun p => w p t) ht.1 (B t) hbt hterms] with z hz
  exact hz.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 (hbt z))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Negation and subtraction preserve the original native family energy budget. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyEnergyNegationNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyEnergyNegationNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMomentFamilyEnergy_neg
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ) :
    planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π (-W) =
      planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π W := by
  classical
  unfold planeAllMomentFamilyEnergy
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => planeTimeAllMomentCarrier_smul
    (E := E i) (K i) ϖ ρ 0 μ (-1) (W i))] with t ht
  apply Finset.sum_congr rfl
  intro i _
  have he : planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ ((-W) i) t =
      -planeTimeAllMomentCarrierToLp (E := E i) (K i) ϖ ρ 0 μ (W i) t := by
    simpa only [neg_one_smul, Pi.neg_apply] using ht i
  rw [he, weightedFactorialNormSq_neg]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual native family gradient energies satisfy a quadratic addition bound without a component-count factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyGradientAdditionNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyGradientAdditionNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMomentFamilyGradientEnergy_add_le
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W V : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 μ) :
    planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π (W + V) ≤
      2 * (planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π W +
        planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π V) := by
  let U := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i)
  let U' := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (V i)
  let Uadd := fun i => planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i + V i)
  let J := fun i t => weightedGradFactorialNormSq n ϖ 0 ρ (K i) (Uadd i t)
  let G := fun i t => weightedGradFactorialNormSq n ϖ 0 ρ (K i) (U i t)
  let H := fun i t => weightedGradFactorialNormSq n ϖ 0 ρ (K i) (U' i t)
  have hJ (i : ι) : AEMeasurable (J i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i + V i))
  have hG (i : ι) : AEMeasurable (G i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  have hH (i : ι) : AEMeasurable (H i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (V i))
  have hb (i : ι) : (∫⁻ t, J i t ∂μ) ≤ 2 *
      ((∫⁻ t, G i t ∂μ) + ∫⁻ t, H i t ∂μ) := by
    have he : (∫⁻ t, J i t ∂μ) =
        ∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ (K i) (U i t + U' i t) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [planeTimeAllMomentCarrier_add (E := E i) (K i + 1) ϖ ρ 0 μ (W i) (V i)] with t ht
      dsimp only [J]
      rw [show Uadd i t = U i t + U' i t from ht]
    rw [he]
    exact integrated_weightedGradFactorialNormSq_add_le n ϖ 0 ρ μ _ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  exact finite_mass_time_quadratic_addition μ (fun i => ENNReal.ofReal ((π i)⁻¹))
    J G H hJ hG hH hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The metric remainder, original-source remainder and terminal metric forcing retain separate original-mass budgets. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance threeFluxResidualBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance threeFluxResidualBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMoment_three_residual_flux_energy_budget
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (Rm Rs T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ)
    (Bm Bs Bt : ℝ≥0∞)
    (hm : planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π Rm ≤ Bm)
    (hs : planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π Rs ≤ Bs)
    (ht : planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π T ≤ Bt) :
    planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π (Rm + Rs + T) ≤ 4 * (Bm + Bs + Bt) := by
  have he := quadratic_energy_three_sum_le (planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π)
    (planeAllMomentFamilyEnergy_add_le K n ϖ ρ μ π) Rm Rs T
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hm hs) ht) zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem inactiveTimeZeroFamily_natural_remainder_uniform_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ τ, τ ∈ W →
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      (inactiveTimeZeroFamily F).flux p c v u γ d I τ (E⁻¹ • Y x) (e⁻¹ • Y x) k -
        taylorSlow 0 Ks (fun X => (inactiveTimeZeroFamily F).flux p c v u γ d I τ X (e⁻¹ • Y x) k)
          (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      ((K v).factorial : ℝ) * Dchart ^ K v * ((K v + 1 : ℕ) * (CR * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  have henv0 := inactiveTimeZeroFamily_pointwiseMolecularEnvelope F W π K ν e E ρ C J b₀ henv
  obtain ⟨CR, hCR, hb⟩ := familyPointwiseMolecular_natural_remainder_uniform_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks (inactiveTimeZeroFamily F)
    π hπ K Kmax hK (fun _ _ => W ×ˢ Set.univ) ν e E ρ hν he hE hρ
    C J b₀ henv0 v u γ hγ d hd I hKs p c
  refine ⟨CR, hCR, ?_⟩
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ hτ yc z k j hj
  have hh := hb hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ
    (fun _ => ⟨hτ, Set.mem_univ _⟩) yc z k j hj
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans
    (polynomialMomentRoot_one_le ϖ z)) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hζ _)
  apply mul_le_mul_of_nonneg_left _ hCR
  apply div_le_div_of_nonneg_right _ (by unfold derivativeReserveFactor; positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold molecularRealPrice
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply ENNReal.toReal_mono
  · exact pointwiseMolecularEnvelope_constituent_jet_ne_top F π hπ K
      (ChartedFamily.Domain.onWindow F W) ν e E ρ hν he hρ C J b₀ henv
      v u γ hγ d hd I (Ks + 1) hKs
  · exact inactiveTimeZeroFamily_pointwiseMolecularJet_le F W ν e E ρ v u γ d I (K v) (Ks + 1)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A component response certificate records the actual frozen-metric weak solution and its native lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance componentCertificateFluxNormed :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentCertificateFluxInner :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentCertificateNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k
local instance componentCertificateNativeModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := allMomentTimeNativeModule k
local instance componentCertificateNativeFluxNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) :=
  allMomentTimeNativeNormed k
local instance componentCertificateNativeFluxModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) :=
  allMomentTimeNativeModule k
local instance componentCertificateFluxLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) 2 μ) :=
  allMomentTimeLpAdd k μ
local instance componentCertificateFluxLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) 2 μ) :=
  allMomentTimeLpModule k μ

def IsPlaneComponentAllMomentResponse (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (K : ℕ) (a b ϖ ρ : ℝ)
    (T : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))) : Prop :=
  ∀ f, ∃ (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (u : Unit → ℝ → PlaneHk Set.univ K E)
    (w : Unit → ℝ → PlaneHk Set.univ (K + 1) E),
    IsPlaneChainFrom (h := fun _ : Unit => E)
      (geometryScalarData (h := fun _ : Unit => E) 2 (fun t _ => M t))
      (fun _ (_ : Unit) => K) a b v
      (fun _ _ => 0)
      (fun _ _ => F)
      (fun _ x => u x) (fun _ x => w x) ∧
    PlaneTimeAllMomentRepresents K ϖ ρ 0 (volume.restrict (Set.Icc a b)) f F ∧
    PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (T f) (w Unit.unit)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual transformed array is exactly the metric-plus-original-source
array used by the coupled feedback estimate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

theorem preparationReferenceCellCoefficient_eq_metricSource
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (s ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2) (he : e ≠ 0) :
    preparationReferenceCellCoefficient F hφ s ν e E actual K yc =
      planeMetricSourceCoefficient K D
        (fun t z => chartMetric hφ s (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
        (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc) := by
  funext v u d t z
  exact preparationReferenceCellCoefficient_eq_metric_add_source F hφ s ν e E actual K yc he v u d t z

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual active family pieces define original and transported bounded native Sobolev source operators from the independent envelope and torus compatibility. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable (F : ChartedFamily ι h D P Ctx) (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (p : (F.locally_finite t t).toFinset)
    (v u : ι) (γ : F.Γ v u) (J : ℕ) (k : Fin 2)

def activePieceNativeScalarRowOperator :
    PlaneHk Set.univ J (h v) →L[ℝ] Lp (h v) 2 (volume : Measure (Vec 2)) :=
  periodicScalarRowOperator
    (nativeSourceScalarJetCoefficient (F.identity v u γ).maxOrder
      (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k)
    ((active_piece_native_scalar_rows_continuous F ν e E a b n hs t ht p (actual p) v u γ J).1 k)
    (pieceNativeSourceScalarJetCoefficient_periodic F ν e E actual hT he p v u γ t k)

def activePieceTransportedScalarRowOperator :
    PlaneHk Set.univ J (h v) →L[ℝ] Lp (h v) 2 (volume : Measure (Vec 2)) :=
  periodicScalarRowOperator
    (pieceTransportedNativeScalarJetCoefficient F ν e E p (actual p) v u γ t J k)
    ((active_piece_native_scalar_rows_continuous F ν e E a b n hs t ht p (actual p) v u γ J).2 k)
    (pieceTransportedNativeScalarJetCoefficient_periodic F ν e E actual hT he p v u γ t J k)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Zero native families have zero original mass-gradient energy. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeAllMomentFamilyGradientEnergy_zero
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ) :
    planeAllMomentFamilyGradientEnergy (E := E) K n ϖ ρ μ π 0 = 0 := by
  classical
  unfold planeAllMomentFamilyGradientEnergy
  calc
    _ = ∫⁻ (_t : ℝ), (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun i => planeTimeAllMomentCarrier_zero_representative
        (E := E i) (K i + 1) ϖ ρ 0 μ 0 rfl)] with t ht
      simp only [Pi.zero_apply, ht, weightedGradFactorialNormSq_zero_native,
        mul_zero, Finset.sum_const_zero]
    _ = 0 := lintegral_zero

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The literal remainder minus terminal-metric flux has the sum of the two original-mass budgets. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance familyResidualBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance familyResidualBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMomentFamilyEnergy_sub_le
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (W V : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ) :
    planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π (W - V) ≤
      2 * (planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π W +
        planeAllMomentFamilyEnergy (E := E) K n ϖ ρ μ π V) := by
  simpa only [sub_eq_add_neg, planeAllMomentFamilyEnergy_neg] using
    planeAllMomentFamilyEnergy_add_le K n ϖ ρ μ π W (-V)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The inherited source seminorm has its exact derivative-order price in cell coordinates. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

theorem preparationReferenceCellSourceCoefficient_seminorm_price
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (s ν e E a b ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 ≤ ρ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2)
    (v u : ι) (d : admissibleOrders K D v u) :
    coefficientSeminorm (ρ / e) (K v) ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d) =
      ENNReal.ofReal ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) *
        coefficientSeminorm ρ (K v) a b
          (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d) := by
  have hscale : 0 < (e⁻¹) ^ 2 * ν := mul_pos (sq_pos_of_ne_zero (inv_ne_zero he.ne')) hν
  have htime (t : ℝ) : ((e⁻¹) ^ 2 * ν)⁻¹ * t = ν⁻¹ * (e ^ 2 * t) := by
    rw [mul_inv_rev, inv_pow, inv_inv, mul_assoc]
  have hnorm : ‖(e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹‖ =
      (e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hh := coefficientSeminorm_affine_time_price ρ hρ (K v) a b ((e⁻¹) ^ 2 * ν) hscale
    ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) e he yc
    (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d)
  have hcoeff : (fun t z => ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
      edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d
        (((e⁻¹) ^ 2 * ν)⁻¹ * t) (yc + e • z)) =
      preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d := by
    funext t z
    rw [htime]
    rfl
  rw [hcoeff, hnorm] at hh
  simpa only [mul_assoc] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The literal retained residual consumes the separate metric, original source and terminal forcing budgets. -/

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance nativeResidualBudgetNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance nativeResidualBudgetModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k

theorem planeAllMoment_native_residual_energy_budget
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) (π : ι → ℝ)
    (full diag metric source Rm Rs : ∀ i, V →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i) ϖ ρ 0 μ)
    (hfull : ∀ i, full i = diag i + metric i + source i + Rm i + Rs i)
    (W T : V) (Bm Bs Bt : ℝ≥0∞)
    (hm : planeAllMomentFamilyEnergy K n ϖ ρ μ π (fun i => Rm i W) ≤ Bm)
    (hs : planeAllMomentFamilyEnergy K n ϖ ρ μ π (fun i => Rs i W) ≤ Bs)
    (ht : planeAllMomentFamilyEnergy K n ϖ ρ μ π (fun i => metric i T) ≤ Bt) :
    planeAllMomentFamilyEnergy K n ϖ ρ μ π
      (fun i => -((metric i W + source i W - metric i T) - full i W + diag i W)) ≤
      4 * (Bm + Bs + Bt) := by
  have he : (fun i => -((metric i W + source i W - metric i T) - full i W + diag i W)) =
      (fun i => Rm i W) + (fun i => Rs i W) + (fun i => metric i T) := by
    funext i
    exact nativeResidual_of_two_remainder_decomposition
      (full i) (diag i) (metric i) (source i) (Rm i) (Rs i) (hfull i) W T
  rw [he]
  exact planeAllMoment_three_residual_flux_energy_budget K n ϖ ρ μ π _ _ _ Bm Bs Bt hm hs ht

end AVRegularity.CycleJointProofs
end
end
