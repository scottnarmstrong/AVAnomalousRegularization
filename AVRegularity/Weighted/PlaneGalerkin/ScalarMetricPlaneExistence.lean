-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.PlaneGalerkin.ScalarProjectedMetricUniformEvolution
public import AVRegularity.CoupledEnergyPlane.HigherReadout
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import AVRegularity.CoupledEnergyPlane.Variational.PlaneWeakDifferenceCurve
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_scalarSourceProjectedEvolution_with_highTimeBound (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ)
    (hG : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ i, Integrable (q i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 =>
      planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i j d p.1 p.2)) :
    ∃ u : C(Set.Icc a b, ProjectedFamily (fun p : Fin 1 × ι => h p.2)),
      (∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator
          ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv (fun p : Fin 1 × ι => κ p.1 p.2) 2
            (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA).reindex
            (clampPoint a b hab)) N 1 s (extendCurve hab u s) + projectedSource N F q s) ∧
      (∀ t : Set.Icc a b, familyProjection N (u t) = u t) ∧
      (∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2) (u t i)).val) ≤
          2 * massNormSq ρ π (fun i => (f i).val) +
            32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2) ∧
      ‖higherBandBochner N (fun p : Fin 1 × ι => κ p.1 p.2) a b hab u‖ ^ 2 ≤
        ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (κ i.1 i.2)) * 8) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2) := by
  let K := fun p : Fin 1 × ι => κ p.1 p.2
  obtain ⟨u, heq, hrange, S, hS, hbound, henergy⟩ :=
    exists_scalarSourceProjectedEvolution_with_uniformEnergy ρ hρ κ a b hab G hA hC v hv V hV hbv
      N hG CG g δ hg hδ hg4 hnear hscale hbfull hb hprice Kmax hK
      strain B lam hstrain0 hB hlam hsmall hstrain π hπ hdiv hjets F q hF hq f hvm hAm
  let P := ∑ i, π i
  let Q := ∑ i, π i / factorialWeightMin ρ (K i)
  let C := 2 * massNormSq ρ π (fun i => (f i).val) +
    32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
      10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2
  let R := fun s => massGradNormSq ρ π
    (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => (hπ i).le)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le)
  have hR : IntervalIntegrable R volume a b :=
    ((continuous_massBandGradient N K ρ π).comp (continuous_extendCurve hab u)).intervalIntegrable a b
  have hRn : 0 ≤ ∫ s in a..b, R s :=
    intervalIntegral.integral_nonneg hab (fun _ _ => massGradNormSq_nonneg ρ π hπ _)
  change S ^ 2 + (1 / 8) * (∫ s in a..b, R s) ≤ C at henergy
  have hSc : S ^ 2 ≤ C := by
    linarith [mul_nonneg (div_nonneg (show (0 : ℝ) < 1 / 4 by norm_num).le (by norm_num : (0 : ℝ) ≤ 2)) hRn]
  refine ⟨u, heq, hrange, fun t => (hbound t).trans hSc, ?_⟩
  have hrle : (∫ s in a..b, R s) ≤ 2 * C / (1 / 4) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 1 / 4 by norm_num)).mpr
    nlinarith [sq_nonneg S]
  have hh : IntervalIntegrable (fun s => ‖higherBandJetOperator N K (extendCurve hab u s)‖ ^ 2)
      volume a b := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (higherBandJet_memLp N K a b (continuous_extendCurve hab u)).norm.integrable_sq
  have hconst : IntervalIntegrable (fun _ : ℝ => P * C) volume a b := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hab hh (hconst.add (hR.const_mul Q))
    (fun s hs => by
      have hc := higherBandJet_normSq_le N K ρ hρ π hπ (extendCurve hab u s)
      have hb : massNormSq ρ π (fun i => (hilbertBandHk N (K i) (extendCurve hab u s i)).val) ≤ C := by
        simpa only [extendCurve_eq_of_mem hab u hs] using (hbound ⟨s, hs⟩).trans hSc
      exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left hb hP) le_rfl))
  rw [intervalIntegral.integral_add hconst (hR.const_mul Q), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul] at hm
  simp only [smul_eq_mul] at hm
  rw [higherBandBochner_normSq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  change _ ≤ (P * (b - a) + Q * 8) * C
  have hq := mul_le_mul_of_nonneg_left hrle hQ
  have halg : (P * (b - a) + Q * 8) * C = (b - a) * (P * C) + Q * (2 * C / (1 / 4)) := by ring
  rw [halg]
  linarith
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_scalarSourcePlaneGalerkin_weakSubsequence (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hG : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ i, Integrable (q i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 =>
      planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i j d p.1 p.2)) :
    let K := fun p : Fin 1 × ι => κ p.1 p.2
    let D := 2
    let A := planeChainCoefficient (geometryScalarData (h := h) 2 G) κ
    ∃ (u : ℕ → C(Set.Icc a b, ProjectedFamily (fun p : Fin 1 × ι => h p.2)))
      (W : PlaneHighTime (h := fun p : Fin 1 × ι => h p.2) K a b) (φ : ℕ → ℕ), StrictMono φ ∧
      (∃ R : ℝ, ∀ N, ‖higherBandBochner N K a b hab (u N)‖ ≤ R) ∧
      (∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator
          ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
            (clampPoint a b hab)) N 1 s (extendCurve hab (u N) s) + projectedSource N F q s) ∧
      (∀ N, ∀ t : Set.Icc a b, familyProjection N (u N t) = u N t) ∧
      (∀ N, ∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤
          2 * massNormSq ρ π (fun i => (f i).val) +
            32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2) ∧
      (∀ ell : PlaneHighTime (h := fun p : Fin 1 × ι => h p.2) K a b →L[ℝ] ℝ,
        Filter.Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
          Filter.atTop (nhds (ell W))) := by
  dsimp only
  classical
  let K := fun p : Fin 1 × ι => κ p.1 p.2
  let D := 2
  let A := planeChainCoefficient (geometryScalarData (h := h) 2 G) κ
  let P (N : ℕ) (u : C(Set.Icc a b, ProjectedFamily (fun p : Fin 1 × ι => h p.2))) :=
    (∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
          (clampPoint a b hab)) N 1 s (extendCurve hab u s) + projectedSource N F q s) ∧
    (∀ t : Set.Icc a b, familyProjection N (u t) = u t) ∧
    (∀ t : Set.Icc a b, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u t i)).val) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2) ∧
    ‖higherBandBochner N K a b hab u‖ ^ 2 ≤
      ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * 8) *
        (2 * massNormSq ρ π (fun i => (f i).val) +
          32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2)
  have hex (N : ℕ) : ∃ u, P N u :=
    exists_scalarSourceProjectedEvolution_with_highTimeBound ρ hρ κ a b hab G hA hC v hv V hV hbv
      N hG CG g δ hg hδ hg4 hnear hscale hbfull hb hprice Kmax hK
      strain B lam hstrain0 hB hlam hsmall hstrain π hπ hdiv hjets F q hF hq f hvm hAm
  choose u hu using hex
  let C := ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * 8) *
    (2 * massNormSq ρ π (fun i => (f i).val) +
      32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
        10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2)
  have hn (N : ℕ) : ‖higherBandBochner N K a b hab (u N)‖ ≤ Real.sqrt C :=
    Real.le_sqrt_of_sq_le (hu N).2.2.2
  obtain ⟨W, φ, hφ, hw⟩ := AVRegularity.CoupledEnergyPlane.Variational.exists_strictMono_tendsto_highTime_clm K a b (Real.sqrt C)
    (fun N => higherBandBochner N K a b hab (u N)) hn
  exact ⟨u, W, φ, hφ, ⟨Real.sqrt C, hn⟩, fun N => (hu N).1, fun N => (hu N).2.1, fun N => (hu N).2.2.1, hw⟩
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_scalarSourcePlaneWeakSolution (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hG : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ i, Integrable (q i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 =>
      planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i j d p.1 p.2)) :
    ∃ (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
      (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2)),
      IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
        (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F q u w := by
  classical
  let K := fun p : Fin 1 × ι => κ p.1 p.2
  let A := planeChainCoefficient (geometryScalarData (h := h) 2 G) κ
  obtain ⟨u, W, φ, hφ, ⟨R, hu⟩, heq, hrange, hmass, hw⟩ :=
    exists_scalarSourcePlaneGalerkin_weakSubsequence ρ hρ κ a b hab G hA hC v hv V hV hbv
      hG CG g δ hg hδ hg4 hnear hscale hbfull hb hprice Kmax hK
      strain B lam hstrain0 hB hlam hsmall hstrain π hπ hdiv hjets F q hF hq f hvm hAm
  have hW := weakHighTime_graph_ae K a b hab u φ W hw
  let C := 2 * massNormSq ρ π (fun i => (f i).val) +
    32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
      10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2
  exact exists_planeWeakSolution_of_nativeGalerkinLimit hab ρ hρ v hv V hV hbv
    K 2 A hC hA hvm hAm 1 f F hF q hq u heq φ hφ W R (fun n => hu (φ n)) hw
    hrange π hπ C hmass hW Kmax hK strain B lam hstrain0
    (le_trans (by norm_num) hB) hlam hjets
end

end AVRegularity.Weighted.PlaneGalerkin
end
