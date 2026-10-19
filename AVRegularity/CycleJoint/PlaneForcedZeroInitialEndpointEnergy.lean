-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
public import AVRegularity.CycleJoint.ScalarPlaneUniformMassSquaredEnergy
public import AVRegularity.CycleJoint.PlaneComponentAllMomentGradientBudget
import Mathlib.Algebra.Order.Star.Real

section
/-! Subtracting the constructed original remainder from the actual native
source map gives precisely the natural Taylor source, with an exact map split. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CoupledEnergyPlane.Variational

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationReferenceCellSourceMap_natural_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (hdesc : F.IsDescending K) (Ks : ℕ) (s : ℝ)
    (yc : Vec 2) (a b ϖ ρ : ℝ)
    (htime : ∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ)
    (Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hfull : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Lfull v))
    (T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hT : ∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (actual p.val) v u γ
        (ν⁻¹ * e ^ 2) a b hφ (F.piece p.val).anchor s e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x τ) (j.val + 1) I z))) (T v u γ j p)) :
    let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
    ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : (F.locally_finite tS tZ).toFinset,
        naturalFamilyTaylorNativeArray Ks F p.val (actual p.val) v u γ (ν⁻¹ * e ^ 2) hφ
          (F.piece p.val).anchor s e E yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
              (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z)))
      (Lfull v - Rs v) ∧ Lfull v = (Lfull v - Rs v) + Rs v := by
  classical
  dsimp only
  intro v
  refine ⟨?_, (sub_add_cancel _ _).symm⟩
  have hr := naturalFamilyRemainder_family_raw_map Ks F K (F.locally_finite tS tZ).toFinset
    (fun p => actual p.val) (fun p => (F.piece p.val).anchor) (ν⁻¹ * e ^ 2) a b s e E ϖ ρ
    hφ yc (volume.restrict (Set.Icc a b)) T hT v
  have hs := planeRaw_allMoment_linearMap_sub (K v) ϖ ρ 0 (volume.restrict (Set.Icc a b))
    _ _ _ _ (hfull v) hr
  intro x
  filter_upwards [hs x, ae_restrict_mem measurableSet_Icc] with τ hτ hm
  filter_upwards [hτ] with z hz
  have hflux := preparationReferenceCellSourceFlux_constructed_split F hc ν e E hν he actual K hdesc
    v Ks s yc z a b τ hm (htime τ hm)
    (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (x u) τ)
  have hcancel := sub_eq_iff_eq_add.mpr hflux
  apply hz.trans
  let Hrem := fun u (γ : F.Γ v u) (j : Fin D) (p : P') =>
    naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) a b hφ
      (F.piece p).anchor s e E yc (j.val + 1) τ z
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z))
  let Htay := fun u (γ : F.Γ v u) (j : Fin D) (p : P') =>
    naturalFamilyTaylorNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) hφ
      (F.piece p).anchor s e E yc (j.val + 1) τ z
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z))
  have hrSum (u : ι) (γ : F.Γ v u) (j : Fin D) :=
    Finset.sum_coe_sort (F.locally_finite tS tZ).toFinset (Hrem u γ j)
  have htSum (u : ι) (γ : F.Γ v u) (j : Fin D) :=
    Finset.sum_coe_sort (F.locally_finite tS tZ).toFinset (Htay u γ j)
  change _ - (∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D,
    ∑ p : (F.locally_finite tS tZ).toFinset, Hrem u γ j p.val) =
    ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D,
      ∑ p : (F.locally_finite tS tZ).toFinset, Htay u γ j p.val
  simp_rw [hrSum, htSum]
  exact hcancel

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Piecewise native remainder estimates assemble into the original mass moment budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwiseOriginalRemainder_piece_order_mass_moment_budget
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (K : ι → ℕ) (Ks Kmax M : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CR ζ : ℝ) (hCR : 0 ≤ CR) (hζ : 0 ≤ ζ)
    (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks + 1 ≤ J)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (θ : ℝ) (hθ : 0 ≤ θ) (hrow : ∀ v, ∑ u, b v u ≤ θ)
    (hcol : ∀ u, ∑ v, b v u ≤ θ) (ϖ : ℝ) (μ : Measure ℝ)
    (S : Finset P) (s : ℝ)
    (T : ∀ v u, F.Γ v u → Fin M → S →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ)
    (W : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ)
    (hpiece : ∀ v u γ r p x, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T v u γ r p x) t) z ≤
        F.weight p.val (s * t) ^ 2 *
          (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ CR ζ v u γ ^ 2 *
            ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
              planeGradFactorialDensity (ρ / e)
                (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x t) z)))
    (n : ℕ) :
    (∫⁻ t, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ r, ∑ p, T v u γ r p) v W) t) ∂μ) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) * (pointwiseOriginalRemainderGraphConstant Ks Kmax ((M : ℝ) * CR) C * θ)) ^ 2) *
        ∫⁻ t, ∑ u, ENNReal.ofReal ((π u)⁻¹) *
          weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u)
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (W u) t) ∂μ := by
  classical
  apply pointwiseOriginalRemainder_family_map_mass_moment_budget F π hπ K Ks Kmax hK
    dom ν e E ρ ((M : ℝ) * CR) ζ (mul_nonneg (Nat.cast_nonneg _) hCR) hζ
    hν hE hρ C J b hKs henv hb θ hθ hrow hcol ϖ μ
    (fun v u => ∑ γ, ∑ r, ∑ p, T v u γ r p) W
  intro v u
  have hh := pointwiseOriginalIdentity_piece_order_sum_density F K Ks Kmax M dom ν e E ρ CR ζ
    hν.le hE.le hρ.le hCR hζ v u s ϖ (ρ / e) μ S (T v u)
    (fun x t z => (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
      planeGradFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x t) z)
    (fun x => Filter.Eventually.of_forall (fun t z =>
      mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)))
    (hpiece v u)
  exact hh (W u)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Fixed compact scalar-direction increments for the actual native material dual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMaterial_compact_increment {a b : ℝ} (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ r, IsZ2Periodic (v r))
    (hvc : ∀ r ∈ Icc a b, Continuous (v r)) {M : ℝ} (hM : 0 ≤ M)
    (hvb : ∀ r ∈ Icc a b, ∀ x, ‖v r x‖ ≤ M)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (h : PlaneWeakHilbertCurve a b u slice (fun r => planeWeakDualRepresentative
      (planeIntervalTransport a b hab v hvc M hvb r)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) (slice r) (F r)))
    (c : ℝ) (hc : c ∈ Icc a b) (d : ℝ) (hd : d ∈ Icc a b) (hcd : c ≤ d)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hsq : HasCompactSupport q) (e : E) :
    let z := compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hsq.smul_right)
    inner ℝ (planeL2FlowPull hφ d s (u d)) (planeHkValueOperator 1 z) -
      inner ℝ (planeL2FlowPull hφ c s (u c)) (planeHkValueOperator 1 z) =
      ∫ r in c..d, inner ℝ (planeWeakDualRepresentative
        (planeMaterialTransport a b hab hφ s v hv hp r)
        (planeMaterialDiffusion a b hab hφ s ν r)
        (planeH1ChartPull hφ r s (slice r)) (planeFluxChartPull hφ r s (F r))) z := by
  obtain ⟨η, hη, hsη, hfixed⟩ := exists_compact_spacetime_fixed_test c d q hq hsq
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
  have hi := planeWeakCurve_material_test_increment hcd (planeWeakCurve_subwindow h hsub)
    hφ s η hη hsη e (fun r hr => (hfixed r hr).2)
  dsimp only at hi ⊢
  rw [compactSpacetimeVectorH1_eq_fixed_test η hη hsη q hq hsq e d
      (hfixed d ⟨hcd, le_rfl⟩).1,
    compactSpacetimeVectorH1_eq_fixed_test η hη hsη q hq hsq e c
      (hfixed c ⟨le_rfl, hcd⟩).1] at hi
  apply hi.trans
  apply intervalIntegral.integral_congr
  intro r hr
  have hrw : r ∈ Icc c d := by simpa only [uIcc_of_le hcd] using hr
  have hrab := hsub hrw
  have hrc k : Continuous (fun x => v r x k) := (continuous_apply k).comp (hvc r hrab)
  have hrb k x : |v r x k| ≤ M := by
    have hn : |v r x k| ≤ ‖v r x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v r x) k
    exact hn.trans (hvb r hrab x)
  dsimp only
  rw [planeIntervalTransport_eq_of_mem a b hab v hvc M hM hvb r hrab hrc hrb]
  have he := planeMaterialDual_compact_correction a b hab hφ s ν v hv hp r hrab
    hrc hM hrb (slice r) (F r) (materialChartTestField hφ s η)
    (materialChartTestField_smooth hφ s η hη)
    (materialChartTestField_compact hφ s η hsη) e
  rw [materialChart_native_test_cancellation hφ s r η hη hsη e,
    compactSpacetimeVectorH1_eq_fixed_test η hη hsη q hq hsq e r (hfixed r hrw).1] at he
  exact he.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Adapter: actual family coefficients give a plane solution whenever their seminorms are finite. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_physicalPlaneWeakSolution_of_finite_seminorms (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hs : family.IsSmoothOn (ChartedFamily.Domain.onWindow family (Set.Icc a b)) E K)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (edgeCoefficient family ν e E actual K i j d) ≠ ⊤)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2)) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b v D K
        (edgeCoefficient family ν e E actual K) f F g u w := by
  have hr : ∀ i j, ¬ sourceDepthRank family H j < sourceDepthRank family H i →
      ∀ d, edgeCoefficient family ν e E actual K i j d = 0 := by
    intro i j hij d
    exact physicalCoefficient_zero_of_rank family H hdepth ν e E actual i j d.val hij
  exact exists_triangularPlaneWeakSolution K Kmax hK ρ strain B lam ν hρ hstrain0 hB
    hlam hν hsmall hstrain a b hab v hv V hV hbv hdiv hjets D
    (edgeCoefficient family ν e E actual K) hA
    (fun i j d t ht => edgeCoefficient_spatial_smooth family hprep ν e E K hs actual K i j d t ht)
    (sourceDepthRank family H) hr F g hF hg f hvm
    (fun i j d => edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d)
end

/-! Actual responses are linear when native forcing superposes only almost everywhere in time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance frozenAeLiftResponseNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance frozenAeLiftResponseNativeLpAdd (i : ι) (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance frozenAeLiftResponseNativeLpModule (i : ι) (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance frozenAeLiftResponseNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance frozenAeLiftResponseNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance frozenAeLiftResponseFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance frozenAeLiftResponseFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem exists_frozenMetricPlaneResponse_ae_liftLinearMap (K : ι → ℕ) (Kmax : ℕ)
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
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lf : E →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (lF : E → ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hadd : ∀ x y i, lF (x + y) i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => lF x i t + lF y i t)
    (hsmul : ∀ (c : ℝ) x i, lF (c • x) i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => c • lF x i t)
    (lg : E →ₗ[ℝ] (∀ i, ℝ → PlaneHk Set.univ (K i) (h i)))
    (hF : ∀ x i, MemLp (lF x i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ x i, Integrable (lg x i) (volume.restrict (Set.Icc a b)))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    :
    ∃ T : ∀ i, E →ₗ[ℝ] Lp (PlaneHk Set.univ (K i + 1) (h i)) 2
      (volume.restrict (Set.Icc a b)),
      ∀ x, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        IsCoupledWeakSolutionPlane 1 a b v 2 K
          (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))
          (lf x) (lF x) (lg x) u w ∧
          ∃ hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)),
            (fun i => (hw i).toLp (w i)) = (fun i => T i x) := by
  classical
  have hex x := exists_frozenMetricPlaneWeakSolution K Kmax hK ρ strain B lam hρ hstrain0 hB
    hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets M hM εg hεg hεgsmall hsym hquad
    (lF x) (lg x) (hF x) (hg x) (lf x) hvm
  let u := fun x => Classical.choose (hex x)
  let w := fun x => Classical.choose (Classical.choose_spec (hex x))
  have hsol x : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))
      (lf x) (lF x) (lg x) (u x) (w x) :=
    Classical.choose_spec (Classical.choose_spec (hex x))
  have huniq x u₁ w₁ u₂ w₂ h₁ h₂ := frozenMetricPlaneWeakSolution_unique_lift K Kmax hK
    ρ strain B lam hρ hstrain0 hB hlam hsmall hstrain a b hab v hv V hV hbv hdiv hjets
    M hM εg hεg hεgsmall hsym hquad (lF x) (lg x) (hF x) (hg x) (lf x) hvm
    u₁ w₁ h₁ u₂ w₂ h₂
  let T : ∀ i, E →ₗ[ℝ] Lp (PlaneHk Set.univ (K i + 1) (h i)) 2
      (volume.restrict (Set.Icc a b)) := fun i =>
    { toFun := fun x => ((hsol x).2.1 i).toLp (w x i)
      map_add' := by
        intro x y
        have hadd' := planeWeakSolution_add_ae_linear_data K 2 1 a b v _ lf lF lg x y
          (hadd x y) (u x) (u y) (w x) (w y) (hsol x) (hsol y)
        have he := (huniq (x + y) _ _ _ _ (hsol (x + y)) hadd').2 i
        have hLp := MemLp.toLp_congr ((hsol (x + y)).2.1 i) (hadd'.2.1 i) he
        exact hLp.trans (MemLp.toLp_add ((hsol x).2.1 i) ((hsol y).2.1 i))
      map_smul' := by
        intro c x
        have hsmul' := planeWeakSolution_smul_ae_linear_data K 2 1 a b v _ lf lF lg c x
          (hsmul c x) (u x) (w x) (hsol x)
        have he := (huniq (c • x) _ _ _ _ (hsol (c • x)) hsmul').2 i
        have hLp := MemLp.toLp_congr ((hsol (c • x)).2.1 i) (hsmul'.2.1 i) he
        exact hLp.trans (MemLp.toLp_const_smul c ((hsol x).2.1 i)) }
  exact ⟨T, fun x => ⟨u x, w x, hsol x, (hsol x).2.1, rfl⟩⟩
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Material charts preserve the genuine native weak Hilbert curve with the actual transformed flux. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMaterial_weak_curve {a b : ℝ} (hab : a ≤ b)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ r, IsZ2Periodic (v r))
    (hvc : ∀ r ∈ Icc a b, Continuous (v r)) {M : ℝ} (hM : 0 ≤ M)
    (hvb : ∀ r ∈ Icc a b, ∀ x, ‖v r x‖ ≤ M)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (h : PlaneWeakHilbertCurve a b u slice (fun r => planeWeakDualRepresentative
      (planeIntervalTransport a b hab v hvc M hvb r)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) (slice r) (F r))) :
    PlaneWeakHilbertCurve a b (fun r => planeL2FlowPull hφ r s (u r))
      (fun r => planeH1ChartPull hφ r s (slice r))
      (fun r => planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp r)
        (planeMaterialDiffusion a b hab hφ s ν r)
        (planeH1ChartPull hφ r s (slice r)) (planeFluxChartPull hφ r s (F r))) := by
  apply planeWeakCurve_of_compact_tests
  · exact planeWeakCurve_chart_trace_continuous h hφ s
  · exact planeWeakCurve_chart_state_memLp h hφ s
  · exact planeMaterialDual_memLp hab h hφ s ν v hv hp F hF
  · exact planeWeakCurve_chart_state_agrees h hφ s
  · intro c hc d hd hcd q hq hsq e
    exact planeMaterial_compact_increment hab hφ s ν v hv hp hvc hM hvb u slice F h
      c hc d hd hcd q hq hsq e

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every covered reference time retains the certified positive constituent lowering budget. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparation_window_reference_constituent_lowering_budget (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc tS tZ)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ)
    (hE : 0 < ocEpsilon q Λ (m - 1)) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K
      (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (dout : ℕ) (hdout : dout ∈ Finset.Icc 2 D) :
    coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical (referenceChartedFamily F hφ σ) ν e (ocEpsilon q Λ (m - 1)) actual v u γ dout) ≤
    ENNReal.ofReal (‖(F.identity v u γ).map‖ *
      preparationSamplingSeminormConstant D Kmax Jchart Cchart *
      (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (ocEpsilon q Λ (m - 1))⁻¹ ^ (din - dout) *
          (pointwiseMolecularJet ρ e (K v) 0
            (fun z : F.Index => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ) z.1 z.2)
            (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ din I)).toReal)) := by
  classical
  let E := ocEpsilon q Λ (m - 1)
  let dom := ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)
  let M := fun din (I : DerivativeWord2 (din - 1)) =>
    pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e E z.1 z.2 v u γ din I)
  let S := ∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal
  by_cases hγ : (F.identity v u γ).map = 0
  · have hz : constituentPhysical (referenceChartedFamily F hφ σ) ν e E actual v u γ dout = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_map (referenceChartedFamily F hφ σ) ν e E actual v u γ hγ dout t x
    change coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical (referenceChartedFamily F hφ σ) ν e E actual v u γ dout) ≤ _
    rw [hz, coefficientSeminorm_zero_function]
    exact zero_le
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro din _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _) ENNReal.toReal_nonneg
  let B := ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart * S
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (preparationSamplingJetConstant_nonnegative _ _ _ _)) hS
  have hs : ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ) (constituentPhysical (referenceChartedFamily F hφ σ) ν e E actual v u γ dout t) := by
    intro t ht
    exact (reference_constituentPhysical_spatial_smooth F hc ν e E hE.ne' (fun v => K v + Jm)
      henv.1 actual v u γ dout σ t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hjets : ∀ t ∈ Set.Icc tS tZ, ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (constituentPhysical (referenceChartedFamily F hφ σ) ν e E actual v u γ dout t) x‖ ≤ B := by
    intro t ht j hj x
    let ts : Set.Icc tS tZ := ⟨t, ht⟩
    let g := fun p y => nativeArrayAssembly (dout - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor σ)
        (F.identity v u γ).maxOrder
        (fun din I => F.dimFlux ν e E p (actual p) v u γ din I t
          (streamFlow φ hφ (F.piece p).anchor y σ)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y σ)) (dout - 1) A y a)
    have hg p (hout : t ∈ (F.piece p).output) : ContDiff ℝ (K v : ℕ) (g p) := by
      exact (natural_flow_constituent_operator_smooth F ν e E hE.ne' (fun v => K v + Jm)
        dom henv.1 p (actual p) v u γ (dout - 1) φ hφ (F.piece p).anchor σ t
        (fun Y => by
          change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
          exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩)).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    apply positive_reference_constituentPhysical_jet_assembly F hc ν e E actual v u γ dout j
      σ ρ B hρ.le hB ts g (fun _ _ => rfl)
      (fun p hout => (hg p hout).of_le (by exact_mod_cast hj)) _ x
    intro p hout y
    have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, hout, ht⟩
    have hanchor := preparation_piece_anchor_mem_geometry hc p hp
    have has := hc.schedule.geometry_padded p hp hanchor
    have hat := preparation_reference_time_padded hc hcover σ hσ
    have hage := preparation_piece_to_window_reference_age hc hcover p hp
      (F.piece p).anchor hanchor σ hσ
    have hnchart : K v ≤ Jchart + 1 := by have hk := hK v; omega
    have hnN : j + (F.identity v u γ).maxOrder ≤ Kmax + D + 2 := by
      have hk := hK v
      have hd := (F.identity v u γ).le_D
      omega
    have hh := pointwise_molecular_native_flow_transport_uniform_budget F π hπ K Kmax hK dom ν e ρ
      hν he hE hρE (preparation_amplitude_nonnegative α q Λ (m - 1) hE.le) hρ
      Cm Jm b henv v u γ hγ p (actual p) hc.flow hnchart (Kmax + D + 2) hchart
      (F.piece p).anchor σ t has hat hage
      (fun Y => by
        change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
        exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩) j (dout - 1) hj (by have hh := (Finset.mem_Icc.mp hdout).1; omega)
      hnN (by have hh := Finset.mem_Icc.mp hdout; omega) y
    have hr : dout - 1 + 1 = dout := by have hh := (Finset.mem_Icc.mp hdout).1; omega
    have hediff din : din - 1 - (dout - 1) = din - dout := by
      have hh := (Finset.mem_Icc.mp hdout).1
      omega
    dsimp only at hh
    simp only [hr, hediff] at hh
    change ρ ^ j * ‖iteratedFDeriv ℝ j (g p) y‖ ≤
      ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart *
        (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) at hh
    have heq : (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) = S := by
      dsimp only [S]
      apply Finset.sum_congr rfl
      intro din _
      apply Finset.sum_congr rfl
      intro I _
      exact mul_comm _ _
    rw [heq] at hh
    exact hh
  have hh := uniform_pointwise_coefficient_seminorm ρ hρ (K v) Kmax (hK v) tS tZ
    (constituentPhysical (referenceChartedFamily F hφ σ) ν e E actual v u γ dout) hs B hB hjets
  apply hh.trans_eq
  congr 1
  dsimp only [preparationSamplingSeminormConstant, B]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The genuine forced coupled metric equation satisfies the uniform squared original-mass estimate with its actual source feedback. -/

/-- The scalar energy constant depends only on the fixed orders and chart budgets. -/
noncomputable def planeScalarSquaredConstant.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) : ℝ :=
  Classical.choose (scalarPlane_uniform_mass_squared_energy.{u, v} n Kmax CG Cw)

theorem planeScalarSquaredConstant_nonneg.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    0 ≤ planeScalarSquaredConstant.{u, v} n Kmax CG Cw :=
  (Classical.choose_spec (scalarPlane_uniform_mass_squared_energy.{u, v} n Kmax CG Cw)).1


theorem planeForced_uniform_mass_squared_energy.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
        (D : ℕ) (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (θ : ℝ)
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ θ)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ θ)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          (∀ i, (∫⁻ t in Set.Icc ta tb,
            weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤) →
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            V₀ F (fun _ _ => 0) V Vw →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            ((⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
              ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))) ≤
            ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) * ((∑ i, ENNReal.ofReal ((π i)⁻¹) *
              weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) +
                32 * ((∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) +
                  ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
                    ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                      weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W D hD A hA hc hAm θ hrow hcol V₀ F hF V Vw he hsln
  have hchain := planeForced_metric_source_order_two_chain (ι := ι) (h := h) ht rstar hrstar Kslot D hD
    v A G hA hc V₀ F V Vw hsln
  have hw := hsln.2.1
  have hrowmem := planeCouplingFluxRow_memLp (ι := ι) (h := h) ht rstar hrstar Kslot D A hA hc Vw hAm hw
  have hb := (Classical.choose_spec
    (scalarPlane_uniform_mass_squared_energy.{u, v} n Kmax CG Cw)).2 (ι := ι) (h := h) π Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀
    (fun i t => F i t + planeCouplingFluxRow ht rstar hrstar Kslot D A hA hc Vw i t)
    (fun i => timeMemLp_add (F i)
      (planeCouplingFluxRow ht rstar hrstar Kslot D A hA hc Vw i) (hF i) (hrowmem i)) V Vw hchain
  have hf := planeForced_total_flux_weighted_time_budget (ι := ι) (h := h) ta tb ht rstar hrstar Kslot D
    A hA hc π hπ θ hrow hcol n ϖ zc Vw hw he F hF
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply add_le_add le_rfl
  have hm := mul_le_mul_of_nonneg_left hf (show (0 : ℝ≥0∞) ≤ 16 from zero_le)
  simpa only [← mul_assoc, show (16 : ℝ≥0∞) * 2 = 32 by norm_num] using hm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The pointwise sampling bridge is uniform over all covered reference times. -/

/-- Independent-to-sampled envelope bridge at every covered reference time. -/
theorem preparation_window_reference_sampled_envelope_of_pointwise_certificate (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (b : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ b v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b →
        IsSampledEnvelope (referenceChartedFamily F hφ σ) π K actual tS tZ ν e (ocEpsilon q Λ (m - 1)) ρ Cprep b := by
  let C := preparationSamplingSeminormConstant D Kmax Jchart Cchart
  let Cbase := C * D * |Cm 0|
  refine ⟨max 1 Cbase, le_max_left _ _, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι h _ _ P' Ctx F π hπ K hK actual b hb hc hcover σ hσ henv
  have he : 0 < e := hρ.trans_le hρe
  have hρE : ρ ≤ ocEpsilon q Λ (m - 1) := hρe.trans heE
  have hE : 0 < ocEpsilon q Λ (m - 1) := hρ.trans_le hρE
  have hC : 0 ≤ C := preparationSamplingSeminormConstant_nonnegative _ _ _ _
  have hs : ∀ v u (γ : F.Γ v u) d, ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ)
        (constituentPhysical (referenceChartedFamily F hφ σ) ν e (ocEpsilon q Λ (m - 1)) actual v u γ d t) := by
    intro v u γ d t ht
    exact (reference_constituentPhysical_spatial_smooth F hc ν e (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + Jm) henv.1 actual v u γ d σ t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hh := sampled_envelope_of_lowering_budget (referenceChartedFamily F hφ σ) π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) actual tS tZ ν e
    (ocEpsilon q Λ (m - 1)) ρ C hν hρ hE hρE hC Cm Jm b hb henv hs
    (fun v u γ dout hdout => preparation_window_reference_constituent_lowering_budget F hc hcover σ hσ π hπ K Kmax hK
      hchart ν e ρ hν he hρ hE hρE Cm Jm b henv actual v u γ dout hdout)
  refine ⟨hh.1, ?_⟩
  intro v u
  exact (hh.2 v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right 1 Cbase) (hb v u)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual coupled error energy absorbs a small original-mass source Schur budget. -/

theorem planeForced_small_source_mass_energy.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
        (D : ℕ) (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (θ : ℝ)
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ θ)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ θ)
        (_hsmall : ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
          (32 * ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2)) ≤ (1 / 2 : ℝ≥0∞))
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        (∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤) →
        ((∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤) →
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          (∀ i, (∫⁻ t in Set.Icc ta tb,
            weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤) →
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            V₀ F (fun _ _ => 0) V Vw →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            ((⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
              ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))) ≤
            2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
              ((∑ i, ENNReal.ofReal ((π i)⁻¹) *
                weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) +
                32 * ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W D hD A hA hc hAm θ hrow hcol hsmall V₀ F hF hinit hforcing
    V Vw he hsln
  have hb := planeForced_uniform_mass_squared_energy n Kmax CG Cw
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W D hD A hA hc hAm θ hrow hcol V₀ F hF V Vw he hsln
  have hgrad := planeFamily_dissipation_le_energy Kslot n ϖ rstar zc ta tb π V Vw hsln.2.1
  have hgm i := weightedGradFactorialNormSq_time_aemeasurable
    n ϖ zc rstar _ (Vw i) (hsln.2.1 i)
  have hgfinite : (∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤ := by
    rw [lintegral_finsetSum' _ (fun i _ => (hgm i).const_mul _)]
    apply ENNReal.sum_ne_top.mpr
    intro i _
    rw [lintegral_const_mul'' _ (hgm i)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he i)
  have hifinite : (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinit i))
  exact finite_gradient_source_feedback_absorb _ _ _ _ _ _ hgfinite hifinite hforcing
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hb hgrad hsmall

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The preparation certificate constructs the actual reference-cell source map on each selected subwindow. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

local instance referenceSourceAllMomentNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance referenceSourceAllMomentModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem preparationReferenceCellSource_allMoment_map
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : 0 < ν) (he : e ≠ 0) (hE : E ≠ 0) (K : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E K)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (s : ℝ) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ r C : ℝ) (hρ : 0 < ρ) (hr : 0 < r)
    (B : ι → ι → ℝ)
    (hsamp : IsSampledEnvelope (referenceChartedFamily F hφ s) π K actual a b ν e E ρ C B)
    (u0 u1 ϖ : ℝ) (hu : u0 ≤ u1)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    ∃ T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ r 0
      (volume.restrict (Set.Icc u0 u1))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ r 0
        (volume.restrict (Set.Icc u0 u1)),
      ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ r 0 (volume.restrict (Set.Icc u0 u1))
        (fun W t => planeRawCouplingFlux K D t
          (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc)
          (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ r 0
            (volume.restrict (Set.Icc u0 u1)) (W j) t) i) (T i) := by
  obtain ⟨hA, hC, hAm, _⟩ := preparationReferenceCellSourceCoefficient_subwindow_data
    F hc ν e E hν he hE K hs hmeas hwmeas actual s yc π hπ ρ r C hρ B hsamp u0 u1 hsub
  exact exists_planeCouplingRow_allMoment_map hu ϖ r hr K D
    (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc) hA hC hAm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Original family masses are restored after absorbing the genuine source feedback by depth. -/

def planeSourceRankScale.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D : ℕ) (B : ℝ) : ℝ :=
  sourceFeedbackRankScale (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) B D

/-- The rank scale is monotone in the source strength. -/
theorem planeSourceRankScale_mono.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D : ℕ) {B B' : ℝ}
    (hB : 0 ≤ B) (hBB' : B ≤ B') :
    planeSourceRankScale.{u, v} n Kmax CG Cw D B ≤ planeSourceRankScale.{u, v} n Kmax CG Cw D B' :=
  sourceFeedbackRankScale_mono _ (planeScalarSquaredConstant_nonneg.{u, v} n Kmax CG Cw) D hB hBB'

theorem one_le_planeSourceRankScale.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D : ℕ) (B : ℝ) :
    1 ≤ planeSourceRankScale.{u, v} n Kmax CG Cw D B :=
  (sourceFeedbackRankScale_spec _ B (planeScalarSquaredConstant_nonneg.{u, v} n Kmax CG Cw) D).1

theorem planeForced_rank_discounted_mass_energy.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        (∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤) →
        ((∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤) →
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          (∀ i, (∫⁻ t in Set.Icc ta tb,
            weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤) →
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            V₀ F (fun _ _ => 0) V Vw →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            ((⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
              ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))) ≤
            ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
              (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
              ((∑ i, ENNReal.ofReal ((π i)⁻¹) *
                weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) +
                32 * ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t))) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hD A hA hc hAm hrow hcol rank hrank hzero V₀ F hF
    hinit hforcing V Vw he hsln
  let L := planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc
  have hchoice := sourceFeedbackRankScale_spec
    (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) Bsrc
    (planeScalarSquaredConstant_nonneg.{u, v} n Kmax CG Cw) D
  have hL : 1 ≤ L := hchoice.1
  let πr := fun i => π i * rankMass rank L i
  have hπr i : 0 < πr i := mul_pos (hπ i) (rankMass_pos rank L (zero_lt_one.trans_le hL) i)
  have hschur := triangularCoefficient_original_mass_schur_budget 1 rstar
    zero_lt_one hrstar Kslot D ta tb A hA rank hzero π hπ L Bsrc hL hrow hcol
  have hinitle := (originalMass_rank_energy_bounds π hπ rank H hrank L hL
    (fun i => weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i))).1
  have hforcele : (∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((πr i)⁻¹) *
      weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≤
      ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t) := by
    apply lintegral_mono
    intro t
    exact (originalMass_rank_energy_bounds π hπ rank H hrank L hL
      (fun i => weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t))).1
  have hb := planeForced_small_source_mass_energy n Kmax CG Cw
    πr hπr Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W D hD A hA hc hAm (Bsrc / L) hschur.1 hschur.2 hchoice.2
    V₀ F hF hinit (ne_top_of_le_ne_top hforcing hforcele) V Vw he hsln
  have hrestore := (originalMass_rank_energy_bounds π hπ rank H hrank L hL
    (fun i => (⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)) +
      ∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t))).2
  apply hrestore.trans
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact add_le_add hinitle (mul_le_mul_of_nonneg_left hforcele zero_le)

/-! Zero-initial actual coupled errors have an endpoint bound in the original family masses. -/

theorem planeForced_zero_initial_endpoint_energy.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ((∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤) →
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          (∀ i, (∫⁻ t in Set.Icc ta tb,
            weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤) →
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            (fun _ => 0) F (fun _ _ => 0) V Vw →
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i tp)) ≤
            ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
              (64 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
                ∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hD A hA hc hAm hrow hcol rank hrank hzero F hF
    hforcing V Vw he hsln tp htp
  have hinit (i : ι) : weightedFactorialNormSq n ϖ zc rstar (Kslot i)
      (0 : PlaneHk Set.univ (Kslot i) (h i)) ≠ ⊤ := by
    rw [weightedFactorialNormSq_zero_carrier]
    exact ENNReal.zero_ne_top
  have hb := planeForced_rank_discounted_mass_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hD A hA hc hAm hrow hcol rank hrank hzero
    (fun _ => 0) F hF hinit hforcing V Vw he hsln
  have hend := planeFamily_endpoint_le_energy Kslot n ϖ rstar zc ta tb π V Vw tp htp
  apply hend.trans
  apply hb.trans_eq
  simp only [weightedFactorialNormSq_zero_carrier, mul_zero, Finset.sum_const_zero, zero_add]
  ring

end AVRegularity.CycleJointProofs
end
end
