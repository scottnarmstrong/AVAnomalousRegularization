-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlanePolynomialJetMultiplierDensity
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CoupledEnergyPlane.Variational.SourceWeakSolutionExistence
import AVRegularity.Weighted.WeightedEnergyPlaneExistence
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CoupledEnergyPlane.PlaneWeakSolutionUniqueness
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The central, positive Taylor and remainder component maps transfer together
under metric equality on the native time window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance metricThreeMapsNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k
local instance metricThreeMapsNativeModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := allMomentTimeNativeModule k

theorem planeMetric_three_raw_maps_window_congr
    (K Ks : ℕ) (ϖ ρ a b : ℝ)
    (G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (M M' : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (heqG : ∀ t ∈ Set.Icc a b, G' t = G t)
    (heqM : ∀ t ∈ Set.Icc a b, M' t = M t)
    (diag positive remainder : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hd : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) diag)
    (hp : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) positive)
    (hr : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) remainder) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux (fun _ => M' t - 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) diag ∧
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G' t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) positive ∧
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeMatrixGradientFlux
        (fun z k l => G' t z k l - taylorSlow 0 Ks (fun y => G' t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) remainder := by
  refine ⟨?_, ?_, ?_⟩
  · exact planeMetric_raw_map_window_congr K ϖ ρ 0 a b (fun t _ => M t) (fun t _ => M' t)
      (fun Mat X t => planeMatrixGradientFlux (fun _ => Mat 0 - 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) diag hd
      (fun t ht => funext (fun _ => heqM t ht))
  · exact planeMetric_raw_map_window_congr K ϖ ρ 0 a b G G'
      (fun Mat X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => Mat y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) positive hp heqG
  · exact planeMetric_raw_map_window_congr K ϖ ρ 0 a b G G'
      (fun Mat X t => planeMatrixGradientFlux
        (fun z k l => Mat z k l - taylorSlow 0 Ks (fun y => Mat y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) X t)) remainder hr heqG

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomially growing native arrays construct actual all-moment source maps at their literal jet order. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

theorem planeWeightedNativeArrayPolynomial_allMoment_density
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : Fin 2 → DerivativeWord2 r → ℝ → Vec 2 → ℝ)
    (hm : ∀ a I z, Measurable (fun t => c a I t z))
    (hc : ∀ a I t, ContDiff ℝ (K : ℕ) (c a I t)) (C : U →L[ℝ] V)
    (B : Fin 2 → DerivativeWord2 r → ℝ) (hB : ∀ a I, 0 ≤ B a I)
    (hb : ∀ a I, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c a I t) z‖ ≤ B a I * polynomialMomentRoot ϖ z ^ p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw : ∀ t, |w t| ≤ 1)
    (T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t z => nativeArrayAssembly r C (fun a I => w t * c a I t z)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) T)
    (x : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (T x) t) z ≤
        w t ^ 2 * ((∑ β : Fin 2 × DerivativeWord2 r,
          Real.sqrt (multiplicationDensityBudget K) *
            (B β.1 β.2 * derivativeReserveFactor ρ K (r - 1) * ‖C‖)) ^ 2 *
          ((polynomialMomentRoot ϖ z ^ p) ^ 2 *
            planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) z)) := by
  obtain ⟨S, hS⟩ := exists_planeNativeArrayPolynomial_allMoment_map hKL hr p ϖ ρ hϖ hρ μ
    c hm hc C B hB hb
  have hden := planeNativeArrayPolynomial_allMoment_density hKL hr p ϖ ρ hϖ hρ μ
    c hm hc C B hB hb S hS x
  let U := fun t => planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (S x) t
  obtain ⟨W, _, _, hwval, hwden⟩ := planeUnitWeighted_forcing_exists μ w hwm hw K 0 ϖ ρ U
    (planeTimeAllMomentCarrier_memLp K ϖ ρ 0 μ (S x))
    (planeTimeAllMomentCarrier_moment K ϖ ρ 0 μ (S x) 0)
  have hval : ∀ᵐ t ∂μ, planeValue (W t) =ᵐ[volume]
      fun z => nativeArrayAssembly r C (fun a I => w t * c a I t z)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z)) := by
    filter_upwards [hS x] with t ht
    filter_upwards [hwval t, ht] with z hz hsz
    rw [hz, hsz]
    change _ = nativeArrayAssembly r C (w t • (fun a I => c a I t z)) _
    rw [map_smul]
    rfl
  have hrep := planeRaw_allMoment_map_represents (E := PiLp 2 (fun _ : Fin 2 => V))
    K ϖ ρ 0 μ _ T hT x W hval
  filter_upwards [hrep, hden] with t ht hdt
  rw [ht]
  filter_upwards [hwden t, hdt] with z hz hdz
  rw [hz]
  exact mul_le_mul_of_nonneg_left hdz (sq_nonneg _)
end

/-! Polynomially growing native arrays construct actual all-moment source maps at their literal jet order. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

theorem exists_planeWeightedNativeArrayPolynomial_allMoment_map
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : Fin 2 → DerivativeWord2 r → ℝ → Vec 2 → ℝ)
    (hm : ∀ a I z, Measurable (fun t => c a I t z))
    (hc : ∀ a I t, ContDiff ℝ (K : ℕ) (c a I t)) (C : U →L[ℝ] V)
    (B : Fin 2 → DerivativeWord2 r → ℝ) (hB : ∀ a I, 0 ≤ B a I)
    (hb : ∀ a I, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c a I t) z‖ ≤ B a I * polynomialMomentRoot ϖ z ^ p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw : ∀ t, |w t| ≤ 1) :
    ∃ T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
        (fun x t z => nativeArrayAssembly r C (fun a I => w t * c a I t z)
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) T := by
  let cw := fun a I t z => w t * c a I t z
  have hwmc a I z : Measurable (fun t => cw a I t z) := hwm.mul (hm a I z)
  have hwsc a I t : ContDiff ℝ (K : ℕ) (cw a I t) := contDiff_const.mul (hc a I t)
  have hwbc a I : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (cw a I t) z‖ ≤ B a I * polynomialMomentRoot ϖ z ^ p := by
    filter_upwards [hb a I] with t ht
    intro j hj z
    change ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => w t • c a I t x) z‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      ((hc a I t).of_le (by exact_mod_cast hj)).contDiffAt, norm_smul, Real.norm_eq_abs]
    calc
      ρ ^ j * (|w t| * ‖iteratedFDeriv ℝ j (c a I t) z‖) =
          |w t| * (ρ ^ j * ‖iteratedFDeriv ℝ j (c a I t) z‖) := by ring
      _ ≤ |w t| * (B a I * polynomialMomentRoot ϖ z ^ p) :=
        mul_le_mul_of_nonneg_left (ht j hj z) (abs_nonneg _)
      _ ≤ B a I * polynomialMomentRoot ϖ z ^ p :=
        mul_le_of_le_one_left (mul_nonneg (hB a I)
          (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _)) (hw t)
  exact exists_planeNativeArrayPolynomial_allMoment_map hKL hr p ϖ ρ hϖ hρ μ
    cw hwmc hwsc C B hB hwbc
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Genuine whole-plane response solutions for spatially frozen near-identity metrics. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_frozenMetricPlaneWeakSolution (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
 :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane 1 a b v 2 K
        (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) f F g u w := by
  exact exists_sourcePlaneWeakSolution K Kmax hK ρ strain B lam 1 hρ hstrain0 hB
    hlam zero_lt_one hsmall hstrain (fun _ => 1) (fun _ => zero_lt_one) a b hab v hv V hV hbv
    hdiv hjets 2 (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))
    (frozenMetric_diagonal_coefficients_finite K M ρ a b εg hεg hsym hquad)
    (fun i j d t _ => frozenMetric_diagonal_coefficient_contDiff K M i j d t)
    (frozenMetric_diagonal_schurCondition K (fun _ => 1) (fun _ => zero_lt_one) M ρ a b εg
      hεg hεgsmall hsym hquad)
    F g hF hg f hvm (frozenMetric_diagonal_coefficient_measurable K M hM a b)

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Spatially frozen diffusion has no positive-order metric radius price. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A spatially frozen scalar chain retains polynomial moments and dissipation. -/
theorem frozenMetricScalar_polynomial_factorial_supremum
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => M t)) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) := by
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (k j : Fin 2) : |M t k j| ≤ 1 + g := by
    have hd := symmetricMetric_difference_entry_abs_le (M t) g (hsym t ht)
      (hnear t 0) k j
    have hsplit : M t k j = (M t - 1) k j + (1 : Matrix (Fin 2) (Fin 2) ℝ) k j := by simp
    rw [hsplit]
    have hone : |(1 : Matrix (Fin 2) (Fin 2) ℝ) k j| ≤ 1 := by
      simp only [Matrix.one_apply]; split_ifs <;> norm_num
    exact (abs_add_le _ _).trans (by linarith)
  have hM (t : ℝ) (ht : t ∈ Icc a b) (l : ℕ) (x : Vec 2) (k j : Fin 2) :
      ‖iteratedFDeriv ℝ l (fun _ : Vec 2 => M t k j) x‖ ≤ 1 + g := by
    cases l with
    | zero => simpa [iteratedFDeriv_zero_eq_comp, Real.norm_eq_abs] using hentry t ht k j
    | succ l => rw [iteratedFDeriv_const_of_ne (by omega)]; simpa using (by linarith : 0 ≤ 1 + g)
  exact scalarChain_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets
    (fun t _ => M t) (hMm.comp (measurable_subtype_coe.comp measurable_fst))
    (fun _ _ _ _ _ => contDiff_const) (fun _ _ => 1 + g)
    (fun _ t ht l x k j => hM t ht l.val x k j)
    g hg4 hnear (fun t ht _ => hsym t ht)
    f F hF u w hsln i (fun _ _ _ _ => contDiff_const)
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall
    0 (by norm_num) hg (by simp) (fun _ => 0)
    (by simpa [metricRadiusConstant] using hreserve)
    (fun _ _ _ l hl _ _ _ => by rw [iteratedFDeriv_const_of_ne (by omega)]; simp)
    hdiv hwa hwb
end

/-! Identity diffusion removes every metric radius price from the actual scalar energy estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The identity scalar chain has the genuine polynomial value and dissipation bound. -/
theorem identityScalar_polynomial_factorial_supremum
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) := by
  have hM (l : ℕ) (x : Vec 2) (k j : Fin 2) :
      ‖iteratedFDeriv ℝ l (fun _ : Vec 2 => (1 : Matrix (Fin 2) (Fin 2) ℝ) k j) x‖ ≤ 1 := by
    cases l with
    | zero => simp [iteratedFDeriv_zero_eq_comp, Matrix.one_apply]; split_ifs <;> norm_num
    | succ l => rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  exact scalarChain_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets
    (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) measurable_const
    (fun _ _ _ _ _ => contDiff_const) (fun _ _ => 1)
    (fun _ _ _ l x k j => hM l.val x k j)
    0 (by norm_num) identityMetric_nearIdentity (fun _ _ _ => by simp [Matrix.IsSymm])
    f F hF u w hsln i (fun _ _ _ _ => contDiff_const)
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall
    0 (by norm_num) (by norm_num) (by simp) (fun _ => 0)
    (by simpa [metricRadiusConstant] using hreserve)
    (fun _ _ _ l hl _ _ _ => by rw [iteratedFDeriv_const_of_ne (by omega)]; simp)
    hdiv hwa hwb
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Whole-plane uniqueness for strictly triangular systems with arbitrary finite coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem triangularPlaneWeakSolution_unique (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
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
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (r : ι → ℕ) (hr : ∀ i i', ¬ r i' < r i → ∀ d, A i i' d = 0)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  obtain ⟨π, hπ, hschur⟩ := exists_triangularCoefficientSchur ν ρ K D a b A hν hρ hA r hr
  exact planeWeakSolution_unique K Kmax hK ρ strain B lam ν hρ hstrain0 hB hlam hν
    hsmall hstrain π hπ a b hab v hv hvm V hV hbv hdiv hjets D A hA hC hAm hschur
    F g hF hg f u w hsol u' w' hsol'

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine whole-plane response solutions for spatially frozen near-identity metrics. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_frozenMetricScalarChain (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (εg : ℝ) (hεg : 0 ≤ εg) (hεgsmall : 4 * εg ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        εg * ∑ i, ξ i ^ 2)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
 :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
        (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) := by
  obtain ⟨u, w, hs⟩ := exists_frozenMetricPlaneWeakSolution K Kmax hK ρ strain B lam hρ hstrain0
    hB hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets M hM εg hεg hεgsmall hsym hquad
    F (fun _ _ => 0) hF (fun i => ⟨aestronglyMeasurable_const, by
      simp only [HasFiniteIntegral, lintegral_const]
      change (‖(0 : PlaneHk Set.univ (K i) (h i))‖₊ : ℝ≥0∞) *
        (volume.restrict (Set.Icc a b)) Set.univ < ⊤
      simp only [nnnorm_zero, ENNReal.coe_zero, zero_mul, ENNReal.zero_lt_top]⟩) f hvm
  exact ⟨u, w, planeDiagonalMetric_scalar_solution K a b v (fun t _ => M t) f F u w hs⟩

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Spatially frozen diffusion preserves finite polynomial value and gradient energy. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Finite initial and flux moments give finite uniform value energy and gradient dissipation. -/
theorem frozenMetricScalar_weighted_value_gradient_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => M t)) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (hf : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) ≠ ⊤)
    (hFe : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤) :
    ((⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≠ ⊤ := by
  have he := frozenMetricScalar_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym f F hF u w hsln i
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb
  have hR : ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
      (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
      (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
        16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
      (ENNReal.add_ne_top.mpr ⟨hf, ENNReal.mul_ne_top (by norm_num) hFe⟩)
  exact ne_top_of_le_ne_top hR he
end

/-! Spatially frozen diffusion preserves finite polynomial energy of the native lift. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Finite initial and flux moments give finite time energy for the genuine higher-order lift. -/
theorem frozenMetricScalar_weighted_lift_time_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => M t)) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) (hr1 : r ≤ 1)
    (hf : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) ≠ ⊤)
    (hFe : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤) :
    (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2 + 1) (w i s)) ≠ ⊤ := by
  have he := frozenMetricScalar_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym f F hF u w hsln i
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb
  have hR : ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
      (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
      (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
        16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
      (ENNReal.add_ne_top.mpr ⟨hf, ENNReal.mul_ne_top (by norm_num) hFe⟩)
  have hfinite := ne_top_of_le_ne_top hR he
  have hsplit := ENNReal.add_ne_top.mp hfinite
  let Vsup := ⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)
  apply weightedFactorialNormSq_lift_time_ne_top m ϖ zc r a b hr hr1 (u i) (w i)
    (hsln.2.2.1 i) Vsup.toReal _ hsplit.2
  intro t ht
  rw [ENNReal.ofReal_toReal hsplit.1]
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
end

/-! Identity diffusion removes every metric radius price from the actual scalar energy estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Finite initial and flux moments give finite uniform value energy and gradient dissipation. -/
theorem identityScalar_weighted_value_gradient_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (hf : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) ≠ ⊤)
    (hFe : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤) :
    ((⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≠ ⊤ := by
  have he := identityScalar_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets f F hF u w hsln i
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb
  have hR : ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
      (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
      (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
        16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
      (ENNReal.add_ne_top.mpr ⟨hf, ENNReal.mul_ne_top (by norm_num) hFe⟩)
  exact ne_top_of_le_ne_top hR he
end

/-! Identity diffusion removes every metric radius price from the actual scalar energy estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Finite initial and flux moments give finite time energy for the genuine higher-order lift. -/
theorem identityScalar_weighted_lift_time_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) (hr1 : r ≤ 1)
    (hf : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) ≠ ⊤)
    (hFe : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤) :
    (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2 + 1) (w i s)) ≠ ⊤ := by
  have he := identityScalar_polynomial_factorial_supremum a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets f F hF u w hsln i
    t₀ S ϖ zc N m Cw C hm r L hr hL hsmall hstrainSmall hreserve hdiv hwa hwb
  have hR : ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
      (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
      (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
        16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
      (ENNReal.add_ne_top.mpr ⟨hf, ENNReal.mul_ne_top (by norm_num) hFe⟩)
  have hfinite := ne_top_of_le_ne_top hR he
  have hsplit := ENNReal.add_ne_top.mp hfinite
  let Vsup := ⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)
  apply weightedFactorialNormSq_lift_time_ne_top m ϖ zc r a b hr hr1 (u i) (w i)
    (hsln.2.2.1 i) Vsup.toReal _ hsplit.2
  intro t ht
  rw [ENNReal.ofReal_toReal hsplit.1]
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual continuous trajectory endpoint is controlled by the family time supremum. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeFamily_endpoint_le_energy
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (a b : ℝ) (π : ι → ℝ)
    (V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (V i t)) ≤
      ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        ((⨆ s ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc ρ (K i) (V i s)) +
          ∫⁻ s in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc ρ (K i) (w i s)) := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact (le_iSup_of_le t (le_iSup_of_le (f := fun _ : t ∈ Set.Icc a b =>
    weightedFactorialNormSq n ϖ zc ρ (K i) (V i t)) ht le_rfl)).trans (le_add_right le_rfl)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Returning a retained native endpoint preserves linearity before the datum is selected. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)

/-- The exact inverse chart and dilation act on each retained endpoint slot. -/
def preparationReferenceRetainedEndpointLinearMap
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) :
    X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (preparationReferenceCellReturnOperator hc hcover hTau ha
      (K i) (hK i) e he yc t ht).toLinearMap.comp ((LinearMap.proj i).comp T))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A uniform squared scalar metric estimate retains the actual time supremum and dissipation before family mass summation. -/

theorem scalarPlane_uniform_squared_energy (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          ∀ i,
            (⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
              (∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≤
            ENNReal.ofReal C * (weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) +
              16 * ∫⁻ t in Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) := by
  obtain ⟨L, hL, hreserve⟩ := exists_radius_absorption_reserve
    (Real.exp (18 * Cw n)) (metricRadiusConstant Kmax CG) (Real.exp_pos _).le
  let A := L ^ (2 * Kmax) * 9 * (Cw n) ^ 2 * Real.exp (18 * Cw n)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro ι _ h _ _ _ _ _ _ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln
  obtain ⟨Vbound, hvbound⟩ := hv_bdd
  intro x
  let κ : Fin 1 → ι → ℕ := fun _ i => Kslot i
  let M := fun i : Fin 1 × ι => fun l : Fin (κ i.1 i.2 + 1) => metricEntryEnvelope CG g δ l.val
  have hGsm : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc ta tb, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun z => G t z k j) := by
    intro i t ht' k j
    exact (hG_smooth t ht' k j).of_le (by exact_mod_cast (hKslot i.2).trans (le_max_left Kmax 1))
  have hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun z => G t z k j) := by
    intro t ht' k j
    exact (hG_smooth t ht' k j).of_le (by exact_mod_cast le_max_right Kmax 1)
  have hm : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc ta tb,
      ∀ (l : Fin (κ i.1 i.2 + 1)) z k j,
        ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) z‖ ≤ M i l := by
    intro i
    exact metricEntryEnvelope_bound (hKslot i.2) G CG g δ hg hδ hg4 hG_near hG_symm hG_jets
  have hh := scalarChain_polynomial_factorial_supremum ta tb ht κ Kmax
    (fun i => hKslot i.2) v hv_meas hv_smooth (max Vbound 0) strain B₀ lam
    (le_max_right _ _) ha hB₀ hlam (fun t ht' z => (hvbound t ht' z).trans (le_max_left _ _))
    (fun t ht' l hl hK z => hjets l hl hK t ht' z) G hG_meas hGsm M hm
    g hg4 hG_near hG_symm (fun i => V₀ i.2) (fun i => F i.2) (fun i => hF i.2)
    (fun i => V i.2) (fun i => Vw i.2) hsln (0, x) hG1 tw S ϖ zc n n Cw W le_rfl
    rstar L hrstar hL hB hab δ hδ hg hrδ CG hreserve hG_jets hv_div htw htb
  have hcoef : ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
      (ENNReal.ofReal (Cw n) * ENNReal.ofReal (Cw n) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw n))) = ENNReal.ofReal A := by
    have hC : 0 ≤ Cw n := (by norm_num : (0 : ℝ) ≤ 1).trans
      (chartWeights_constant_ge_one W n le_rfl ta ⟨htw, ht.trans htb⟩)
    dsimp [A]
    rw [show L ^ (2 * Kmax) * 9 * (Cw n) ^ 2 * Real.exp (18 * Cw n) =
      L ^ (2 * Kmax) * 3 * (Cw n * Cw n * (3 * Real.exp (18 * Cw n))) by ring]
    simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ (2 * Kmax)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_mul hC,
      ENNReal.ofReal_ofNat, mul_assoc]
  simpa only [κ, hcoef] using hh

/-! The actual scalar metric estimate preserves finite polynomial value and gradient energy. -/

theorem scalarPlane_weighted_value_gradient_energy_ne_top (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          ∀ i,
          weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤ →
          (∫⁻ t in Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤ →
          ((⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
            ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤ := by
  intro ι _ h _ _ _ _ _ _ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln i hinit hforcing
  obtain ⟨C, _, hb⟩ := scalarPlane_uniform_squared_energy n Kmax CG Cw
  have he := hb Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln i
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hinit, ENNReal.mul_ne_top (by norm_num) hforcing⟩)) he

/-! The actual scalar squared energy estimate preserves the original family masses before absorption. -/

theorem scalarPlane_uniform_mass_squared_energy (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            ((⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
              ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))) ≤
            ENNReal.ofReal C * ((∑ i, ENNReal.ofReal ((π i)⁻¹) *
              weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) +
                16 * ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) := by
  obtain ⟨C, hC, hscalar⟩ := scalarPlane_uniform_squared_energy n Kmax CG Cw
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln
  have hb := hscalar Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln
  exact family_weighted_energy_budget (volume.restrict (Set.Icc ta tb))
    (fun i => ENNReal.ofReal ((π i)⁻¹)) (fun _ => ENNReal.ofReal_ne_top)
    (fun i => (⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
      ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))
    (fun i => weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i))
    (fun i t => weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) (ENNReal.ofReal C)
    (fun i => weightedFactorialNormSq_time_aemeasurable n ϖ zc rstar _ (F i) (hF i)) hb

end AVRegularity.CycleJointProofs
end
