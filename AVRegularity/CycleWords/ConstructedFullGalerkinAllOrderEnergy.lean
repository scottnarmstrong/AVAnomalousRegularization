-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstantMetricClippedFactorialENNReal
public import AVRegularity.CycleWords.InteriorPulseReflectedEnergyPolynomialPrice
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalRemainderPair_native_flux_exists_uniform (Ks Kmax : ℕ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks + 1 ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ α : OriginalSourceIndex F v u,
            (F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 -
              taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
                X0 ((e / E) • z)) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤
            (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α) ^ 2 *
              (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CR, hCR, hflux⟩ := originalRemainderConstituent_native_flux_exists_all_uniform Ks Kmax
  refine ⟨CR, hCR, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ hwindow n U hU henergy
  have hex (α : OriginalSourceIndex F v u) := hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    C J b₀ hKs henv hmeas v u α.1 α.2.1.1 α.2.1.2 α.2.2.1 p c s a b ϖ ζ hs hϖ hscale
    hζ hδ X0 φ α.2.2.2 hwindow n U hU henergy
  choose V hV hVe hvalue hdensity using hex
  have hp (α : OriginalSourceIndex F v u) : 0 ≤ originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α :=
    originalRemainderPrice_nonneg F K (Ks + 1) Kmax dom ν e E ρ CR hν.le hE.le hρ.le hCR v u α
  have hdens : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e) (∑ α, V α t) z ≤
        (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α) ^ 2 *
          (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z := by
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    have hh := nativeFactorialDensity_sum_price_le (ρ / e) (fun α => V α t)
      (fun α => originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α) hp
      (fun z => (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z)
      (fun z => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (planeGradFactorialDensity_nonneg (ρ / e) (U t) z))
      (fun α => by
        filter_upwards [ht α] with z hz
        simpa only [originalRemainderPrice, mul_pow,
          Real.sq_sqrt (multiplicationDensityBudget_nonneg (K v)), mul_assoc, mul_comm, mul_left_comm] using hz)
    simpa only [mul_assoc] using hh
  refine ⟨fun t => ∑ α, V α t, ?_, ?_, ?_, hdens⟩
  · exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun α _ => hV α)
  · have hh := nativeFlux_time_moment_shift_budget n (Ks + 1) ϖ (ρ / e)
      ((∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α) * ζ ^ (Ks + 1))
      (volume.restrict (Set.Icc a b)) (fun t => ∑ α, V α t) U
        (by simpa only [mul_pow, mul_assoc] using hdens)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top henergy) hh
  · filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun α => V α t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun α _ => hzs α))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Exact continuous trace readout of the real reconstructed Bloch plane evolution. -/

theorem planeBlochEnergyRealTrace_value {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) (t : CellCompactTime a b) :
    planeHkValueOperator 0
      (cellEnergyPlaneRealTrace hab
        (planeBlochEnergyField hab G hG v V hv hb
          (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)) t) =
      planeComplexRealPartL2 (planeBlochEnergyReconstructedTrace hab G hG v V hv hb f t) := by
  unfold cellEnergyPlaneRealTrace
  rw [planeL2ZeroCarrier_value, projIcc_of_mem hab t.property]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy of the original full finite cell system, uniformly in its Fourier cutoff. -/

theorem constructedFullGalerkinOperator_higher_energy {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t) u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  have hl := constructedFullGalerkinOperator_higher_lift hK N hΛ hζ ν y₀ hv V hb G hG θ κ t u
  have hi := torusHigherProjection_retained_inner K N
    (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
    (rangeSmoothFourierLiftCLM hK N u) (rangeSmoothFourierLift_fixed hK N u)
  have hpair := (congrArg (fun z : TorusHk K ℂ =>
    inner ℝ z (rangeSmoothFourierLiftCLM hK N u)) hl).trans hi
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t)
    (constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2)
    (constructedHigherFullGenerator_smooth_adjacent_energy K hΛ hζ hν hr y₀ hv G hG θ R hθ κ t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u) (cellGalerkinSmoothValue_periodic N u))
  exact (congrArg (fun x : ℝ => 2 * x + (1 / 2) *
    (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
      ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The rough generator's native readouts give the frozen scalar weak spatial RHS. -/

theorem planeRealBlochScalarRawRhs_ae (K : ℕ) (v : Vec 2 → Vec 2)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (w : PlaneHk Set.univ (K + 1) ℝ) (φ : PlaneHk Set.univ 1 ℝ) :
    planeRealBlochSpatialRhs G v (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) φ =ᵐ[volume]
      planeScalarRawRhs K v (fun _ => G) w 0 φ := by
  have hw : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeRealH1TestGradient (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) i x =
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun i => univToPlane_ae _)
  have hp : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeRealH1TestGradient φ i x = φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun i => univToPlane_ae _)
  filter_upwards [hw, hp, univToPlane_ae (φ.val (valueIndex2 1)),
    planeZeroJetRepresentative_ae (E := ℝ) K (valueIndex2 K),
    planeZeroJetRepresentative_ae (E := PiLp 2 (fun _ : Fin 2 => ℝ)) K (valueIndex2 K)]
    with x hwx hpx hvx hzx hfx
  simp only [planeRealBlochSpatialRhs, planeScalarRawRhs,
    planeHkValueOperator_apply, hvx, hzx, hfx, PiLp.zero_apply,
    add_zero, inner_zero_left]
  simp_rw [hwx, hpx]
  have ha := metricDeviation_weak_pairing G
    (fun i => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)
    (fun j => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ x)
    (fun _ => (0 : ℝ))
  have htranspose :
      (∑ i : Fin 2, ∑ j : Fin 2, G i j * inner ℝ
        (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)
        (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ x)) =
      ∑ j : Fin 2, inner ℝ
        (∑ i : Fin 2, G j i • w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x)
        (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ x) := by
    simp only [sum_inner, real_inner_smul_left]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hG.apply j i]
  simp only [add_zero] at ha
  rw [htranspose]
  simp only [PlaneHk.toFunction, planeJetRepresentative] at ha ⊢
  linarith [ha]

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The signed reflected higher operator has the original reflected variational readout. -/

 theorem interiorPulseReflectedFullGeneratorCLM_pairing (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t U))
      (torusHkValueCLM z) =
    cellGeneratorForm ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t
      (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) z := by
  let C : CellCoefficients := ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
  let u := truncateTorusHk (by omega : 2 ≤ K + 2) U
  have hd : cellDiffusionForm C (cellMetric_timeReverse hG) t (cellH2BaseCLM u) z =
      inner ℝ (cellConstantMetricStrongDiffusionCLM (fun s => G (-s)) θ t u) (torusHkValueCLM z) := by
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair (fun s => G (-s)) (cellMetric_timeReverse hG) θ t u z)
    rw [cellComplexDiffusionForm_real_part C (cellMetric_timeReverse hG), cellComplexPair_re] at he
    exact he
  simp only [interiorPulseReflectedFullGeneratorCLM, add_apply, ContinuousLinearMap.comp_apply,
    map_add, torusHigherStrongDiffusionCLM_value,
    interiorPulseHigherAdvectionCLM_value K hΛ hζ ν y₀ hslot hv V hb,
    torusHigherScalarCLM_value, inner_add_left, Fin.sum_univ_two]
  change _ = cellGeneratorForm C (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t (cellH2BaseCLM u) z
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hd]
  have h0 := cellDriftEntryCLM_reflected_pair _ hv V hb t 0
    (cellShiftedDerivativeCLM θ 0 (cellH2BaseCLM u)) (torusHkValueCLM z)
  have h1 := cellDriftEntryCLM_reflected_pair _ hv V hb t 1
    (cellShiftedDerivativeCLM θ 1 (cellH2BaseCLM u)) (torusHkValueCLM z)
  let d := inner ℝ (cellConstantMetricStrongDiffusionCLM (fun s => G (-s)) θ t u)
    (torusHkValueCLM z)
  let c := inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM z)
  let a (i : Fin 2) := inner ℝ
    (cellDriftEntryCLM ⟨0, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, 0, 0⟩ V hv.1 hb (-t) i
      (cellShiftedDerivativeCLM θ i (cellH2BaseCLM u))) (torusHkValueCLM z)
  let b (i : Fin 2) := inner ℝ
    (cellDriftEntryCLM C V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t i
      (cellShiftedDerivativeCLM θ i (cellH2BaseCLM u))) (torusHkValueCLM z)
  change d + (a 0 + a 1) + c = d - (b 0 + b 1) + c
  change a 0 = -b 0 at h0
  change a 1 = -b 1 at h1
  linarith only [h0, h1]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Literal divergence forcing of the frozen scalar equation is the actual native H1 source dual. -/

theorem planeRealBlochForcedRawRhs_ae (K : ℕ) (v : Vec 2 → Vec 2)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (w : PlaneHk Set.univ (K + 1) ℝ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (φ : PlaneHk Set.univ 1 ℝ) :
    planeScalarRawRhs K v (fun _ => G) w F φ =ᵐ[volume]
      fun x => planeRealBlochSpatialRhs G v (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) φ x -
        ∑ i : Fin 2, inner ℝ (planeFluxValueOperator K F i x) (planeRealH1TestGradient φ i x) := by
  have hF : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeFluxValueOperator K F i x = F.toFunction.jet (valueIndex2 K) x i :=
    ae_all_iff.mpr (fun i => planeFluxValueOperator_ae K F i)
  have hφ : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeRealH1TestGradient φ i x = φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun i => univToPlane_ae _)
  have hz := (planeRealBlochScalarRawRhs_ae K v G hG w φ).trans
    (planeScalarRawRhs_zeroFlux_ae K v (fun _ => G) w φ)
  filter_upwards [hF, hφ, hz,
    planeZeroJetRepresentative_ae (E := ℝ) K (valueIndex2 K)] with x hFx hφx hzx hgx
  rw [hzx]
  simp_rw [hFx, hφx]
  simp only [planeScalarRawRhs, planeScalarRawRhsZeroFlux, hgx, inner_zero_left,
    inner_add_left, Finset.sum_add_distrib, add_zero]
  ring

theorem planeRealBlochForcedDual_pair (K : ℕ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (w : PlaneHk Set.univ (K + 1) ℝ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (φ : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual G v hv t C hC
        (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) +
      planeSourceDual 0 (planeFluxValueOperator K F)) φ =
        ∫ x, planeScalarRawRhs K (v t) (fun _ => G) w F φ x := by
  rw [inner_add_left, planeRealBlochGeneratorDual_spatialPair,
    planeSourceDual_pair, inner_zero_left, zero_sub, planeFlux_inner_eq_integral]
  have hi := planeRealBlochSpatialRhs_integrable G v hv t C hC
    (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) φ
  have hf : Integrable (fun x => ∑ i : Fin 2,
      inner ℝ (planeFluxValueOperator K F i x) (planeRealH1TestGradient φ i x)) volume :=
    integrable_finsetSum Finset.univ (fun i _ => L2.integrable_inner _ _)
  rw [← sub_eq_add_neg]
  change (∫ x, planeRealBlochSpatialRhs G (v t)
      (truncatePlaneHk (show 1 ≤ K + 1 by omega) w) φ x) -
    (∫ x, ∑ i : Fin 2, inner ℝ (planeFluxValueOperator K F i x)
      (planeRealH1TestGradient φ i x)) = _
  rw [← integral_sub hi hf]
  exact (integral_congr_ae (planeRealBlochForcedRawRhs_ae K (v t) G hG w F φ)).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The weighted plane estimate for one native scalar component, with the
constant selected before the component Hilbert space. -/

theorem scalarNative_component_apriori_uniform (q Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E],
      ∀ (K : ℕ), K ≤ Kmax → ∀ (a b ρ δ ϖ g strain B lam : ℝ)
      (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ),
      ScalarCoefficientInputs Kmax CG a b ρ δ v strain B lam G g →
      ∀ (tw S : ℝ), tw ≤ a → b ≤ tw + S → ChartWeights G v tw S ϖ 0 q Cw →
      ∀ (f : PlaneHk Set.univ K E) (V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
      (U : ℝ → PlaneHk Set.univ K E) (Uw : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp V 2 (volume.restrict (Set.Icc a b)) →
      IsPlaneChainFrom (ι := Unit) (h := fun _ => E) (geometryScalarData 2 G)
        (fun _ _ => K) a b v (fun _ _ => f) (fun _ _ => V) (fun _ _ => U) (fun _ _ => Uw) →
      nativeComponentEnergy q ϖ ρ a b U Uw ≤
        ENNReal.ofReal A * (weightedFactorialNormSq q ϖ 0 ρ K f +
          16 * ∫⁻ t in Set.Icc a b, weightedFactorialNormSq q ϖ 0 ρ K (V t)) := by
  obtain ⟨A, hA, henergy⟩ := weighted_energy_plane_component_lower_apriori q Kmax CG Cw
  refine ⟨A, hA, ?_⟩
  intro E _ _ _ _ _ _ K hK a b ρ δ ϖ g strain B lam v G HC tw S htw htb W f V U Uw hV hs
  exact henergy (h := fun _ : Unit => E) (fun _ => K) (fun _ => hK)
    a b HC.time ρ δ HC.radius HC.delta HC.scale
    v HC.drift_bounded HC.drift_measurable HC.drift_smooth HC.drift_divergence
    strain B lam HC.strain HC.drift_constant HC.drift_length HC.drift_jets HC.drift_scale HC.drift_small
    G g HC.metric_size HC.metric_small HC.metric_measurable HC.metric_symmetric HC.metric_near
    HC.metric_smooth HC.metric_jets tw S ϖ 0 htw htb W
    (fun _ => f) (fun _ => V) (fun _ => nativeTimeNorm_lower_integral_lt_top hV)
    (fun _ => U) (fun _ => Uw) hs ()

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The original full finite cell curve obeys a cutoff-independent higher integrating-factor estimate. -/

theorem energyGradientDifference_absorb {P E B V C : ℝ}
    (hv : V ≤ E) (he : P + (1 / 2) * (B - V) ≤ C * E) :
    P + (1 / 2) * B ≤ (C + 1 / 2) * E := by
  nlinarith

theorem cellGalerkinRangeHigher_value_norm_le {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    ‖cellGalerkinValue N u‖ ≤ ‖rangeSmoothFourierLiftCLM hK N u‖ := by
  rw [← cellGalerkinRangeHigher_value hK N u]
  exact PiLp.norm_apply_le (rangeSmoothFourierLiftCLM hK N u).val (valueIndex2 K)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A native realization of the literal source turns the actual coupled chain into a scalar forced metric equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryError_weak_equation (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (a b s δ : ℝ) (X0 phase : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (Mv MG : ℝ) (hMv : 0 ≤ Mv) (hMG : 0 ≤ MG)
    (hvc : ∀ t ∈ Set.Icc a b, ∀ k, Continuous (fun x => v t x k))
    (hvb : ∀ t ∈ Set.Icc a b, ∀ k x, |v t x k| ≤ Mv)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun x => G t x k j))
    (hGb : ∀ t ∈ Set.Icc a b, ∀ k j x, |G t x k j| ≤ MG)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (fZ : ∀ (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (Z : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (V : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hsol : IsPlaneChainFrom (geometryActualData G (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v (fun _ x => f x) (fun _ _ _ => 0)
      (fun _ x => U x) (fun _ x => Uw x))
    (hZ : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v fZ (fun _ _ _ => 0) Z Zw)
    (hV : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      geometryErrorSourceFlux F J Ks K p c G s δ X0 phase (fun u => Uw u t - ∑ j, Zw j u t)
        (fun j u => Zw j u t) x t) :
    ∀ (x : ι) (t : ℝ), t ∈ Set.Icc a b → ∀ ψ : PlaneHk Set.univ 1 (h x),
      CoupledWeakIdentity volume 1 a t v
        ((U x t - ∑ j, Z j x t).toFunction.jet (valueIndex2 (K x)))
        ((f x - ∑ j, fZ j x).toFunction.jet (valueIndex2 (K x)))
        (ψ.toFunction.jet (valueIndex2 1))
        (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r k => (Uw x r - ∑ j, Zw j x r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r => geometryScalarFlux D G (fun _ u => K u)
          (fun q => Uw q.2 r - ∑ j, Zw j q.2 r) (0, x) r)
        (fun r => (V x r).toFunction.jet (valueIndex2 (K x)))
        (fun _ => (0 : PlaneHk Set.univ (K x) (h x)).toFunction.jet (valueIndex2 (K x))) := by
  classical
  intro x t ht ψ
  let A := fun r => geometryActualFlux D G (F.cellFiber s phase p c) X0 δ
    (fun _ u => K u) (fun q => Uw q.2 r) (0, x) r
  let B := fun j r => geometryResponseRawFlux J Ks K G (F.cellFiber s phase p c) X0 δ
    (fun j u => Zw j u r) j x r
  let A' := fun r => geometryScalarFlux D G (fun _ u => K u)
    (fun q => Uw q.2 r - ∑ j, Zw j q.2 r) (0, x) r
  let du := fun r k => (Uw x r - ∑ j, Zw j x r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩
  let fzero := fun _ : ℝ => (0 : PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x))).toFunction.jet (valueIndex2 (K x))
  let gzero := fun _ : ℝ => (0 : PlaneHk Set.univ (K x) (h x)).toFunction.jet (valueIndex2 (K x))
  let fnew := fun r => (V x r).toFunction.jet (valueIndex2 (K x))
  have hFzero (r : ℝ) : fzero r =ᵐ[volume] 0 := by
    have hz := planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x)
    rw [planeValue_eq_stored] at hz
    filter_upwards [hz] with z hzero
    change (0 : PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x))).toFunction.jet (valueIndex2 (K x)) z = 0 at hzero
    exact hzero
  have hgzero (r : ℝ) : gzero r =ᵐ[volume] 0 := by
    have hz := planeValue_zero_ae (E := h x) (K x)
    rw [planeValue_eq_stored] at hz
    filter_upwards [hz] with z hzero
    change (0 : PlaneHk Set.univ (K x) (h x)).toFunction.jet (valueIndex2 (K x)) z = 0 at hzero
    exact hzero
  have hu := hsol.2.2.2.2 (0, x) t ht ψ
  simp only [Measure.restrict_univ] at hu
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ _ A fzero gzero at hu
  have hu0 := coupledWeakIdentity_zero_forcings volume 1 a t v _ _ _ _ _ A fzero gzero hu hFzero hgzero
  have hz0 (j : Fin (J + 1)) := hZ.2.2.2.2 (j, x) t ht ψ
  simp only [Measure.restrict_univ] at hz0
  have hz (j : Fin (J + 1)) : CoupledWeakIdentity volume 1 a t v
      ((Z j x t).toFunction.jet (valueIndex2 (K x))) ((fZ j x).toFunction.jet (valueIndex2 (K x)))
      (ψ.toFunction.jet (valueIndex2 1)) (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (Zw j x r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩) (B j) 0 0 := by
    exact coupledWeakIdentity_zero_forcings volume 1 a t v _ _ _ _ _ (B j) fzero gzero (hz0 j) hFzero hgzero
  have hh := nativeWeakIdentity_sub_sum (K x) 1 a t v (U x t) (f x) (fun j => Z j x t) (fun j => fZ j x)
    (Uw x) (fun j => Zw j x) A B ψ hu0 hz
  have hh' := coupledWeakIdentity_forcings_congr volume 1 a t v _ _ _ _ du (A - ∑ j, B j) 0 0 0 gzero hh
    (fun _ => Filter.Eventually.of_forall (fun _ => rfl)) (fun r => (hgzero r).symm)
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ du A' fnew gzero
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  apply coupledWeakIdentity_flux_ae_time_congr volume 1 a t v _ _ _ _ du (A - ∑ j, B j) 0 A' fnew gzero hh'
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hV x)] with r hr
    have hraw := geometryError_raw_flux_split_ae F hD J Ks K hdesc p c G s δ X0 phase
      (fun u => Uw u r) (fun j u => Zw j u r) x r
    rw [planeValue_eq_stored] at hr
    filter_upwards [hraw, hr] with z hz hvz
    change (A - ∑ j, B j) r z + (0 : PiLp 2 (fun _ : Fin 2 => h x)) = A' r z + fnew r z
    simp only [Pi.sub_apply, Finset.sum_apply, add_zero, A, B, A', fnew]
    change (V x r).toFunction.jet (valueIndex2 (K x)) z = _ at hvz
    rw [hz, hvz]
  · intro r hr
    have hrI := hsub hr
    have hi := planeScalarRawRhs_integrable (K x) (v r) (hvc r hrI) hMv (hvb r hrI)
      (G r) (hGc r hrI) hMG (hGb r hrI) (Uw x r - ∑ j, Zw j x r) (V x r) ψ
    unfold Weighted.planeScalarRawRhs at hi
    simpa only [du, A', fnew, gzero, geometryScalarFlux_eq D hD, one_mul] using hi

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full original Taylor family admits a native forcing and a mass Schur bound at shifted moments. -/

theorem originalRemainderFamily_native_flux_exists_uniform (Ks Kmax : ℕ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks + 1 ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      (∀ v u, 0 ≤ b₀ v u) → (∀ v, ∑ u, b₀ v u ≤ 1) → (∀ u, ∑ v, b₀ v u ≤ 1) →
      ∀ (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      (∀ u, MemLp (U u) 2 (volume.restrict (Set.Icc a b))) →
      (∀ u, (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u) (U u t)) ≠ ⊤) →
      ∃ V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        (∀ v, MemLp (V v) 2 (volume.restrict (Set.Icc a b))) ∧
        (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V v t) =ᵐ[volume]
          (fun z => ∑ u, ∑ α : OriginalSourceIndex F v u,
            (F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 -
              taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
                X0 ((e / E) • z)) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U u t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ m, (∫⁻ t in Set.Icc a b,
          ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (V v t)) ≤
          ENNReal.ofReal ((originalRemainderGraphConstant (Ks + 1) Kmax CR C * ζ ^ (Ks + 1)) ^ 2) *
            ∫⁻ t in Set.Icc a b,
              ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (m + (Ks + 1)) ϖ 0 (ρ / e) (K u) (U u t)) := by
  classical
  obtain ⟨CR, hCR, hpairs⟩ := originalRemainderPair_native_flux_exists_uniform Ks Kmax
  refine ⟨CR, hCR, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas hb₀ hrow hcol
    p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ hwindow n U hU henergy
  have hex (v u : ι) := hpairs F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ hwindow n (U u) (hU u) (henergy u)
  choose V hV hVe hvalue hdensity using hex
  refine ⟨fun v t => ∑ u, V v u t, ?_, ?_, ?_⟩
  · intro v
    exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V v) Finset.univ (fun u _ => hV v u)
  · intro v
    filter_upwards [ae_all_iff.mpr (hvalue v)] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun u => V v u t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun u _ => hzs u))
  · obtain ⟨hr, hc⟩ := originalRemainderPrice_graph_budget F π K (Ks + 1) Kmax hK dom ν e E ρ CR hCR
      hν hE hρ C J b₀ hKs henv hb₀ hrow hcol
    have hdens : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
        (∑ v, (π v)⁻¹ * planeFactorialDensity (ρ / e) (∑ u, V v u t) z) ≤
          originalRemainderGraphConstant (Ks + 1) Kmax CR C ^ 2 * (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            ∑ u, (π u)⁻¹ * planeGradFactorialDensity (ρ / e) (U u t) z := by
      filter_upwards [ae_all_iff.mpr (fun v => ae_all_iff.mpr (hdensity v))] with t ht
      have hh := nativeFluxGraph_density_budget K (ρ / e) (fun v u => V v u t) π hπ
        (fun v u => ∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K (Ks + 1) Kmax dom ν e E ρ CR v u α)
        (fun v u => Finset.sum_nonneg (fun α _ =>
          originalRemainderPrice_nonneg F K (Ks + 1) Kmax dom ν e E ρ CR hν.le hE.le hρ.le hCR v u α))
        (originalRemainderGraphConstant (Ks + 1) Kmax CR C) (originalRemainderGraphConstant_nonneg (Ks + 1) Kmax CR C) hr hc
        (fun u z => (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U u t) z)
        (fun u z => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (planeGradFactorialDensity_nonneg (ρ / e) (U u t) z))
        (fun v u => by simpa only [mul_assoc] using ht v u)
      filter_upwards [hh] with z hz
      have he : (∑ u, (π u)⁻¹ * ((ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
          planeGradFactorialDensity (ρ / e) (U u t) z)) =
          (ζ ^ (Ks + 1)) ^ 2 * (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * ∑ u, (π u)⁻¹ * planeGradFactorialDensity (ρ / e) (U u t) z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      rw [he] at hz
      simpa only [mul_assoc] using hz
    intro m
    exact nativeFlux_time_moment_shift_mass_budget π (fun v => (hπ v).le) K m (Ks + 1) ϖ (ρ / e)
      (originalRemainderGraphConstant (Ks + 1) Kmax CR C * ζ ^ (Ks + 1)) (volume.restrict (Set.Icc a b))
      (fun v t => ∑ u, V v u t) U
        (by simpa only [mul_pow, mul_assoc] using hdens)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The committed reflected finite cell system reads out its full higher generator. -/

theorem constructedReflectedGalerkinOperator_higher_readout (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinOperator N (cellGeneratorB
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u =
    cellGalerkinL2Initial N (torusHkValueCLM
      (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinOperator N _ u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N _)) (cellGalerkinValue N z)
  rw [cellGalerkinOperator_pairing, cellGalerkinL2Initial_pairing]
  change cellGeneratorForm
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t u.val z.val =
    inner ℝ (torusHkValueCLM
      (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) (torusHkValueCLM z.val)
  rw [constructedReflectedFullGeneratorCLM_pairing K hΛ hζ ν y₀ hv V hb G hG θ κ t _ z.val]
  have he := rangeSmoothFourierLift_truncate (by omega : 1 ≤ K + 2) N u
  have hbase : cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) = u.val := by
    exact he
  rw [hbase]

theorem constructedReflectedGalerkinOperator_higher_lift {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u) =
    galerkinProj N (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) := by
  rw [constructedReflectedGalerkinOperator_higher_readout K N hΛ hζ ν y₀ hv V hb G hG θ κ t u,
    cellGalerkinL2Initial_higher_lift]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact real plane generator pairing through genuine cell Bloch H1 test fields. -/

theorem planeRealBlochGeneratorForm_cellIntegral
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (t : ℝ) (u z : PlaneHk Set.univ 1 ℝ) :
    planeRealBlochGeneratorForm (G t) v hv t C (hC t) u z =
      ∫ θ, cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩
        hG V hv.1 hb t
        (cellComplexH1RealEquiv (planeRealH1BlochTest u θ))
        (cellComplexH1RealEquiv (planeRealH1BlochTest z θ))
        ∂centeredPlaneFrequencyMeasure := by
  rw [cellFrequencyGenerator_plane_form G hG v hv V hb C hCpos hC]
  simp only [planeRealH1BlochTest_value, planeRealH1BlochTest_gradient,
    planeComplexRealPairing, map_smul, planeComplexRealPartL2_ofRealL2,
    planeRealBlochGeneratorForm]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A forward trajectory of reversed coefficients is an actual backward plane adjoint curve. -/

theorem planeWeakCurve_reflectedAdjoint {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (Cr C' : ℝ)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v r x) t i z‖ ≤ C')
    {u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2))}
    {slice : ℝ → PlaneHk Set.univ 1 ℝ}
    (h : PlaneWeakHilbertCurve (-b) (-a) u slice
      (fun r => planeRealBlochGeneratorDual (G (-r)) (fun r x => -v (-r) x)
        (cellDrift_timeReverse hv) r Cr (hCr r) (slice r))) :
    PlaneWeakHilbertCurve a b (fun r => u (-r)) (fun r => slice (-r))
      (fun r => -planeRealBlochGeneratorDual (G r) (fun r x => -v r x)
        (cellDrift_neg hv) r C' (hC' r) (slice (-r))) := by
  have hr := planeWeakCurve_timeReflection h
  have he : (fun r => -planeRealBlochGeneratorDual (G (-(-r)))
      (fun r x => -v (-r) x) (cellDrift_timeReverse hv) (-r) Cr (hCr (-r)) (slice (-r))) =
        fun r => -planeRealBlochGeneratorDual (G r) (fun r x => -v r x)
          (cellDrift_neg hv) r C' (hC' r) (slice (-r)) := by
    funext r
    rw [neg_neg]
    apply congrArg Neg.neg
    exact planeRealBlochGeneratorDual_congr_time (G r)
      (fun r x => -v (-r) x) (fun r x => -v r x)
      (cellDrift_timeReverse hv) (cellDrift_neg hv) (-r) r
      (by simp only [neg_neg]) Cr C' (hCr (-r)) (hC' r) (slice (-r))
  rw [he] at hr
  exact hr

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual canonical fast projection is uniformly bounded on rough L2 entrances. -/

theorem canonicalAdjointFast_initial_norm_le (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (u : ComplexCellL2) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    ‖u - cellScalarCLM (cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1)))
        (cellSourceSlice ell t)‖ ≤ 13 * ‖u‖ := by
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hξ, hrad]
  have hmode := (fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hξR t).2
  have hrow := fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hξ t
  have hell : ‖cellSourceSlice (fibreSeriesFun
      (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t‖ ≤ 4 := by
    have hn := norm_add_le
      (cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t -
        cellConstantCLM 1) (cellConstantCLM 1)
    simp only [sub_add_cancel, cellConstantCLM_norm, norm_one] at hn
    linarith only [hn, hrow]
  dsimp only
  let R := cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t + cellConstantCLM 1
  let L := cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t
  have hc := cellComplexPair_norm_le u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)
  rw [cellFiberConj_norm] at hc
  have hcn : ‖cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)‖ ≤ 3 * ‖u‖ := by
    calc
      _ ≤ ‖u‖ * ‖R‖ := hc
      _ ≤ ‖u‖ * 3 := mul_le_mul_of_nonneg_left hmode (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ‖u‖ + ‖cellScalarCLM (cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)) L‖ := norm_sub_le _ _
    _ = ‖u‖ + ‖cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)‖ * ‖L‖ := by
        rw [cellScalarCLM_smul, norm_smul]
    _ ≤ ‖u‖ + (3 * ‖u‖) * 4 := add_le_add_right
      (mul_le_mul hcn hell (norm_nonneg _) (by positivity)) _
    _ = _ := by ring

/-! The actual canonical fast projection is uniformly bounded on rough L2 entrances. -/

theorem canonicalFast_initial_norm_le (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (u : ComplexCellL2) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    ‖u - cellScalarCLM (cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t)))
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1)‖ ≤ 13 * ‖u‖ := by
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hξ, hrad]
  have hmode := (fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hξR t).2
  have hrow := fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hξ t
  have hell : ‖cellSourceSlice (fibreSeriesFun
      (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t‖ ≤ 4 := by
    have hn := norm_add_le
      (cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t -
        cellConstantCLM 1) (cellConstantCLM 1)
    simp only [sub_add_cancel, cellConstantCLM_norm, norm_one] at hn
    linarith only [hn, hrow]
  exact cellNormalized_remainder_norm _ _ _ hmode hell

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The native L2 divergence source pairs to the literal Hilbert-valued scalar RHS in each coordinate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeScalarCoordinateNativeFlux_pair (K : ℕ) (e : E)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (w : PlaneHk Set.univ (K + 1) E) (S : PlaneFluxL2 E)
    (R : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hS : ∀ i, S i =ᵐ[volume] fun x => R x i)
    (φ : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual G v hv t C hC
        (mapPlaneHk (InnerProductSpace.toDual ℝ E e)
          (truncatePlaneHk (show 1 ≤ K + 1 by omega) w)) +
      planeSourceDual 0 (planeFluxFiberCoordinateCLM e S)) φ =
      ∫ x, planeScalarRawRhsZeroFlux K (v t) (fun _ => G) w
        (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ) x -
        ∑ i : Fin 2, inner ℝ (R x i)
          ((mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ).toFunction.jet
            ⟨⟨1, by omega⟩, fun _ => i⟩ x) := by
  rw [planeRealBlochNativeFlux_pair]
  apply integral_congr_ae
  have hr := ((planeRealBlochScalarRawRhs_ae K (v t) G hG
    (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w) φ).trans
      (planeScalarRawRhs_zeroFlux_ae K (v t) (fun _ => G)
        (mapPlaneHk (InnerProductSpace.toDual ℝ E e) w) φ)).trans
          (planeScalarCoordinateRawRhs K e (v t) (fun _ => G) w φ)
  rw [← planeHkFiberTruncate] at hr
  have hs : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeFluxFiberCoordinateCLM e S i x = inner ℝ e (R x i) :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [planeFluxFiberCoordinateCLM_ae e S i, hS i] with x hc hR
      rw [hc, hR])
  have hφ : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeRealH1TestGradient φ i x = φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hi : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ).toFunction.jet
        ⟨⟨1, by omega⟩, fun _ => i⟩ x =
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => i⟩ x • e :=
    ae_all_iff.mpr (fun _ => planeHkMapRawReadout _ φ _)
  filter_upwards [hr, hs, hφ, hi] with x hrx hsx hφx hix
  rw [hrx]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hsx, hφx, hix, realFiberScalarTestPair]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy of the original full reflected finite cell system, uniformly in its Fourier cutoff. -/

theorem constructedReflectedGalerkinOperator_higher_energy {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  have hl := constructedReflectedGalerkinOperator_higher_lift hK N hΛ hζ ν y₀ hv V hb G hG θ κ t u
  have hi := torusHigherProjection_retained_inner K N
    (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
    (rangeSmoothFourierLiftCLM hK N u) (rangeSmoothFourierLift_fixed hK N u)
  have hpair := (congrArg (fun z : TorusHk K ℂ =>
    inner ℝ z (rangeSmoothFourierLiftCLM hK N u)) hl).trans hi
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t)
    (constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2)
    (constructedReflectedFullGenerator_smooth_adjacent_energy K hΛ hζ hν hr y₀ hv G hG θ R hθ κ t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u) (cellGalerkinSmoothValue_periodic N u))
  exact (congrArg (fun x : ℝ => 2 * x + (1 / 2) *
    (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
      ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A native realization of the literal source turns the actual coupled chain into a scalar forced metric equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryError_scalar_component_redistribution (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (a b s δ : ℝ) (X0 phase : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (Mv MG : ℝ) (hMv : 0 ≤ Mv) (hMG : 0 ≤ MG)
    (hvc : ∀ t ∈ Set.Icc a b, ∀ k, Continuous (fun x => v t x k))
    (hvb : ∀ t ∈ Set.Icc a b, ∀ k x, |v t x k| ≤ Mv)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun x => G t x k j))
    (hGb : ∀ t ∈ Set.Icc a b, ∀ k j x, |G t x k j| ≤ MG)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (fZ : ∀ (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (Z : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (V : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hsol : IsPlaneChainFrom (geometryActualData G (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v (fun _ x => f x) (fun _ _ _ => 0)
      (fun _ x => U x) (fun _ x => Uw x))
    (hZ : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v fZ (fun _ _ _ => 0) Z Zw)
    (hV : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      geometryErrorSourceFlux F J Ks K p c G s δ X0 phase (fun u => Uw u t - ∑ j, Zw j u t)
        (fun j u => Zw j u t) x t) :
    ∀ x : ι, IsPlaneChainFrom (ι := Unit) (h := fun _ => h x) (geometryScalarData D G)
      (fun _ _ => K x) a b v
      (fun _ _ => nativeErrorDatum (f x) (fun j => fZ j x)) (fun _ _ => V x)
      (fun _ _ => nativeErrorCurve (U x) (fun j => Z j x))
      (fun _ _ => nativeErrorCurve (Uw x) (fun j => Zw j x)) := by
  classical
  intro x
  have hk := nativeError_kinematics a b (f x) (fun j => fZ j x)
    (U x) (fun j => Z j x) (Uw x) (fun j => Zw j x)
    (hsol.1 (0, x)) (fun j => hZ.1 (j, x))
    (hsol.2.1 (0, x)) (fun j => hZ.2.1 (j, x))
    (hsol.2.2.1 (0, x)) (fun j => hZ.2.2.1 (j, x))
    (hsol.2.2.2.1 (0, x)) (fun j => hZ.2.2.2.1 (j, x))
  apply nativeScalarError_chain D (K x) a b v G (f x) (fun j => fZ j x)
    (U x) (fun j => Z j x) (Uw x) (fun j => Zw j x) (V x) hk
  intro t ht ψ
  have hh := geometryError_weak_equation F hD J Ks K hdesc p c
    a b s δ X0 phase v G Mv MG hMv hMG hvc hvb hGc hGb f U Uw fZ Z Zw V hsol hZ hV x t ht ψ
  rw [geometryScalar_component_flux D hD G K (fun u r => Uw u r - ∑ j, Zw j u r) x] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A single native energy hierarchy for the actual full finite cell generator. -/

def constructedAllOrderGrowth (K : ℕ) (R k η Cw : ℝ) (ξ : Fin 2 → ℂ) : ℝ :=
  match K with
  | 0 => cellFullZerothGrowth η Cw ξ k
  | j + 1 => constructedHigherEnergyOrderPrice (j + 1) R k * peFactor η ^ 2 + 1 / 2

theorem constructedFullGalerkin_all_order_energy (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k) (u : CellGalerkinSpace (E := ℂ) N) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let θ := fun i => (Real.sqrt η : ℂ) * ξ i
    let A := cellGalerkinOperator N (cellGeneratorB
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t)
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (A u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      constructedAllOrderGrowth K R k η Cw ξ * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  dsimp only
  cases K with
  | zero =>
    change _ + (1 / 2) * ‖cellGalerkinNativeLiftCLM N 1 u‖ ^ 2 ≤ _
    have he := cellFullGalerkin_zeroth_adjacent_energy N (ν / ocMeanFlux α q Λ ζ m ν)
      Cw hCw G hG hv hw V hb ξ κ t k hk u
    simpa only [constructedAllOrderGrowth, torusH0_inner_value,
      cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_one,
      cellGalerkinNativeLiftCLM_zero_norm_sq] using he
  | succ j =>
    have he := constructedFullGalerkinOperator_higher_energy (by omega : 1 ≤ j + 1) N
      hΛ hζ hν hr y₀ hv V hb G hG
      (fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i) R hθ κ t k hk u
    have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
      (cellGalerkinRangeHigher_value_norm_le (by omega : 1 ≤ j + 1) N u) 2
    have hp := energyGradientDifference_absorb hv' he
    simpa only [constructedAllOrderGrowth,
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ j + 1),
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ (j + 1) + 1)] using hp

end AVRegularity.CycleWords
end
