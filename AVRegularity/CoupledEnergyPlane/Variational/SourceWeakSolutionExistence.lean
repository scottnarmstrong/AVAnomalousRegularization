-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.PlaneWeakSolutionUniqueness
import AVRegularity.CoupledEnergyPlane.SourceCarrierResidualRhs
public import AVRegularity.CoupledEnergyPlane.SourceSobolevFlux
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_sourceProjectedEvolution_with_highTimeBound (K : ι → ℕ) (Kmax : ℕ)
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
      (∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (K i) (u t i)).val) ≤
          2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) ∧
      ‖higherBandBochner N K a b hab u‖ ^ 2 ≤
        ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
          (2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) := by
  obtain ⟨u, heq, hrange, S, hS, hbound, henergy⟩ :=
    exists_sourceProjectedEvolution_with_uniformEnergy K Kmax hK N ρ strain B lam ν
      hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab v hv V hV hbv hdiv hjets
      D A hA hC hschur F g hF hg f hvm hAm
  let P := ∑ i, π i
  let Q := ∑ i, π i / factorialWeightMin ρ (K i)
  let C := 2 * massNormSq ρ π (fun i => (f i).val) +
    (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
      10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2
  let R := fun s => massGradNormSq ρ π
    (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => (hπ i).le)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le)
  have hR : IntervalIntegrable R volume a b :=
    ((continuous_massBandGradient N K ρ π).comp (continuous_extendCurve hab u)).intervalIntegrable a b
  have hRn : 0 ≤ ∫ s in a..b, R s :=
    intervalIntegral.integral_nonneg hab (fun _ _ => massGradNormSq_nonneg ρ π hπ _)
  change S ^ 2 + (ν / 2) * (∫ s in a..b, R s) ≤ C at henergy
  have hSc : S ^ 2 ≤ C := by
    linarith [mul_nonneg (div_nonneg hν.le (by norm_num : (0 : ℝ) ≤ 2)) hRn]
  refine ⟨u, heq, hrange, fun t => (hbound t).trans hSc, ?_⟩
  have hrle : (∫ s in a..b, R s) ≤ 2 * C / ν := by
    apply (le_div_iff₀ hν).mpr
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
  change _ ≤ (P * (b - a) + Q * (2 / ν)) * C
  have hq := mul_le_mul_of_nonneg_left hrle hQ
  have halg : (P * (b - a) + Q * (2 / ν)) * C = (b - a) * (P * C) + Q * (2 * C / ν) := by ring
  rw [halg]
  linarith
end

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_sourcePlaneGalerkin_weakSubsequence (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
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
    ∃ (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
      (W : PlaneHighTime (h := h) K a b) (φ : ℕ → ℕ), StrictMono φ ∧
      (∃ R : ℝ, ∀ N, ‖higherBandBochner N K a b hab (u N)‖ ≤ R) ∧
      (∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator
          ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
            (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s) ∧
      (∀ N, ∀ t : Set.Icc a b, familyProjection N (u N t) = u N t) ∧
      (∀ N, ∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤
          2 * massNormSq ρ π (fun i => (f i).val) +
            (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
              10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) ∧
      (∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
        Filter.Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
          Filter.atTop (nhds (ell W))) := by
  classical
  let P (N : ℕ) (u : C(Set.Icc a b, ProjectedFamily h)) :=
    (∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab u s) + projectedSource N F g s) ∧
    (∀ t : Set.Icc a b, familyProjection N (u t) = u t) ∧
    (∀ t : Set.Icc a b, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u t i)).val) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2) ∧
    ‖higherBandBochner N K a b hab u‖ ^ 2 ≤
      ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
        (2 * massNormSq ρ π (fun i => (f i).val) +
          (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2)
  have hex (N : ℕ) : ∃ u, P N u :=
    exists_sourceProjectedEvolution_with_highTimeBound K Kmax hK N ρ strain B lam ν
      hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab v hv V hV hbv hdiv hjets
      D A hA hC hschur F g hF hg f hvm hAm
  choose u hu using hex
  let C := ((∑ i, π i) * (b - a) + (∑ i, π i / factorialWeightMin ρ (K i)) * (2 / ν)) *
    (2 * massNormSq ρ π (fun i => (f i).val) +
      (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
        10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2)
  have hn (N : ℕ) : ‖higherBandBochner N K a b hab (u N)‖ ≤ Real.sqrt C :=
    Real.le_sqrt_of_sq_le (hu N).2.2.2
  obtain ⟨W, φ, hφ, hw⟩ := exists_strictMono_tendsto_highTime_clm K a b (Real.sqrt C)
    (fun N => higherBandBochner N K a b hab (u N)) hn
  exact ⟨u, W, φ, hφ, ⟨Real.sqrt C, hn⟩, fun N => (hu N).1, fun N => (hu N).2.1, fun N => (hu N).2.2.1, hw⟩
end

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_sourcePlaneContinuousCarriers (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
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
    ∃ (W : PlaneHighTime (h := h) K a b)
      (U : ∀ i, C(Set.Icc a b, PlaneHk Set.univ (K i) (h i))),
      (∀ i, U i ⟨a, le_rfl, hab⟩ = f i) ∧
      (∀ i, extendCurve hab (U i) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (weakHighCarrier K a b W i t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
        W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1)) ∧
      (let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA
       let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hC hA hAm
       ∀ i, ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 (h i),
         inner ℝ (planeHkValueOperator (E := h i) (K i) (U i t))
           (planeHkValueOperator (E := h i) 1 ψ) =
         nativeRawTestValue ν (planeHkValueOperator (E := h i) (K i) (f i))
           (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab Cc hc i W)
           (limitFluxField hab Cc hc W i
             ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
               (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
           (fun s => planeHkValueOperator (E := h i) (K i) (g i s)) t ψ) := by
  classical
  obtain ⟨u, W, φ, hφ, ⟨R, hu⟩, heq, hrange, hmass, hw⟩ :=
    exists_sourcePlaneGalerkin_weakSubsequence K Kmax hK ρ strain B lam ν hρ hstrain0 hB
      hlam hν hsmall hstrain π hπ a b hab v hv V hV hbv hdiv hjets D A hA hC hschur
      F g hF hg f hvm hAm
  have hW := weakHighTime_graph_ae K a b hab u φ W hw
  let C := 2 * massNormSq ρ π (fun i => (f i).val) +
    (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
      10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2
  have hrep (i : ι) := exists_sourceContinuousSobolevRepresentative hab ρ hρ v hv V hV hbv
    K D A hC hA hvm hAm ν f F hF g hg u heq φ hφ W R (fun n => hu (φ n)) hw
    hrange π hπ C hmass hW Kmax hK strain B lam hstrain0 (le_trans (by norm_num) hB) hlam hjets i
  choose U _hconv hinit hUa using hrep
  refine ⟨W, U, hinit, hUa, hW, ?_⟩
  dsimp only
  intro i t ψ
  exact AVRegularity.CoupledEnergyPlane.sourceContinuousCarrier_native_equation hab ρ hρ v hv V hV hbv
    K D A hC hA hvm hAm ν f F hF g hg u heq φ hφ W R (fun n => hu (φ n)) hw
    hrange π hπ C hmass hW i (U i) (hinit i) (hUa i) t ψ
end

/-! The actual projected drift multiplier satisfies the cutoff-independent energy bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_sourcePlaneWeakSolution (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
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
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b v D K A f F g u w := by
  obtain ⟨W, U, hinit, hUa, hW, hid⟩ :=
    exists_sourcePlaneContinuousCarriers K Kmax hK ρ strain B lam ν hρ hstrain0 hB
      hlam hν hsmall hstrain π hπ a b hab v hv V hV hbv hdiv hjets D A hA hC hschur
      F g hF hg f hvm hAm
  refine ⟨fun i => extendCurve hab (U i), weakHighCarrier K a b W, ?_⟩
  exact AVRegularity.CoupledEnergyPlane.sourceNativeEquation_pack_weakSolution hab ρ hρ
    v hv V hV hbv K D A hC hA hvm hAm Kmax hK strain B lam hstrain0
    (le_trans (by norm_num) hB) hlam hjets W hW ν F hF g hg f U hinit hUa hid
end

end AVRegularity.CoupledEnergyPlane.Variational
end
