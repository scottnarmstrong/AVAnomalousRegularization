-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.OriginalTaylorPairNativeFluxSupported
public import AVRegularity.CycleEvolution.FibreCoefficientGraphRawDual
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalTaylorPair_native_flux_exists_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤
            (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorConstituent_native_flux_exists_all_uniform Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  have hex (α : OriginalSourceIndex F v u) := hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    C J b₀ hKs henv hmeas v u α.1 α.2.1.1 α.2.1.2 α.2.2.1 p c s a b ϖ ζ hs hϖ hscale
    hζ hζ1 hδ X0 φ α.2.2.2 hwindow n U hU henergy
  choose V hV hVe hvalue hdensity using hex
  have hp (α : OriginalSourceIndex F v u) : 0 ≤ originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α := by
    unfold originalTaylorPrice
    apply mul_nonneg _ (norm_nonneg _)
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCT)
    apply Finset.sum_nonneg
    intro r _
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hdens : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e) (∑ α, V α t) z ≤
        (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
          (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z := by
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    have hh := nativeFactorialDensity_sum_price_le (ρ / e) (fun α => V α t)
      (fun α => originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) hp
      (fun z => (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z)
      (fun z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg (ρ / e) (U t) z))
      (fun α => by
        filter_upwards [ht α] with z hz
        simpa only [originalTaylorPrice, mul_pow,
          Real.sq_sqrt (multiplicationDensityBudget_nonneg (K v)), mul_assoc] using hz)
    simpa only [mul_assoc] using hh
  refine ⟨fun t => ∑ α, V α t, ?_, ?_, ?_, hdens⟩
  · exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun α _ => hV α)
  · have hh := nativeFlux_time_moment_shift_budget n Ks ϖ (ρ / e)
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
      (volume.restrict (Set.Icc a b)) (fun t => ∑ α, V α t) U hdens
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top henergy) hh
  · filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun α => V α t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun α _ => hzs α))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual joint generator has the plane form of the native transposed state. -/

theorem cellEnergyJointGenerator_planeForm_ae {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure)
    (test : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (∫ θ, cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv.1 hb t
        (cellComplexH1RealEquiv (cellEnergyJointH1 hab F (θ, t))) (cellComplexH1RealEquiv (test θ))
        ∂centeredPlaneFrequencyMeasure) =
          -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ
            (G t i j • cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i)
            (cellFrequencyPlaneGradient test j)) -
          ∑ i : Fin 2, inner ℝ
            (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
              (cellDriftTorusSymbol_measurable v hv t i) C (hC t i)
                (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i))
            (cellFrequencyPlaneValue test) := by
  filter_upwards [cellEnergyTimeFrequencyState_slices hab F] with t ht
  calc
    _ = ∫ θ, cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv.1 hb t
        (cellComplexH1RealEquiv (cellEnergyTimeFrequencyState hab F t θ))
        (cellComplexH1RealEquiv (test θ)) ∂centeredPlaneFrequencyMeasure := by
      apply integral_congr_ae
      filter_upwards [ht] with θ hθ
      rw [hθ]
      rfl
    _ = _ := cellFrequencyGenerator_plane_form G hG v hv V hb C hCpos hC t _ test

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The literal difference of the actual and response weak-equation fluxes is
the scalar metric flux of the native error plus its exact error forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryError_raw_flux_split_ae (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (p : P) (c : Ctx p) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ : ℝ) (X0 phase : Vec 2)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
    (Z : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (v : ι) (t : ℝ) :
    (fun z => geometryActualFlux D G (F.cellFiber s phase p c) X0 δ (fun _ u => K u)
      (fun q => U q.2) (0, v) t z -
      ∑ j, geometryResponseRawFlux J Ks K G (F.cellFiber s phase p c) X0 δ Z j v t z) =ᵐ[volume]
    (fun z => geometryScalarFlux D G (fun _ u => K u) (fun q => U q.2 - ∑ j, Z j q.2) (0, v) t z +
      geometryErrorSourceFlux F J Ks K p c G s δ X0 phase (fun u => U u - ∑ j, Z j u) Z v t z) := by
  have hh := geometryActualFlux_sub_sum_ae D G (F.cellFiber s phase p c) X0 δ (fun _ u => K u)
    (fun q => U q.2) (fun j q => Z j q.2) (0, v) t
  filter_upwards [hh] with z hz
  have ht := geometryResponse_flux_telescope F hD J Ks K hdesc p c G s δ X0 phase Z v t z
  have he := geometryActualFamilyFlux_split F K hdesc p c G s δ t X0 phase z v (fun u => U u - ∑ j, Z j u)
  rw [he] at hz
  simp only [geometryResponseRawFlux_eq_ordered, geometryErrorSourceFlux, geometryErrorRemainderFlux]
  rw [← add_assoc, hz]
  have hm := congrArg (fun x => -x) ht
  simp only [neg_neg] at hm
  rw [← hm]
  abel

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Only actual original source edges require higher weighted moments to construct a pair forcing. -/

theorem originalTaylorPair_native_flux_exists_supported_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (Nonempty (F.Γ v u) →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤
            (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorPair_native_flux_exists_uniform Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  by_cases hed : Nonempty (F.Γ v u)
  · exact hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
      v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU (henergy hed)
  · have hempty : (Finset.univ : Finset (OriginalSourceIndex F v u)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro α _
      exact hed ⟨α.1⟩
    have hzero : MemLp
        (fun _ : ℝ => (0 : PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v))))
        2 (volume.restrict (Set.Icc a b)) :=
      Weighted.planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc a b))
    refine ⟨fun _ => 0, hzero, ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only [hempty, Finset.sum_empty] using (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v)))
    · exact Filter.Eventually.of_forall (fun _ => by
        filter_upwards [planeFactorialDensity_zero_ae
          (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
        simp only [hz, hempty, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact time integration of the genuine joint-to-plane generator identity. -/

theorem cellEnergyJointGenerator_planeIntegral {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure)
    (test : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val) :
    (∫ r in s.val..t.val, ∫ θ,
      cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv.1 hb r
        (cellComplexH1RealEquiv (cellEnergyJointH1 hab F (θ, r)))
        (cellComplexH1RealEquiv (test θ)) ∂centeredPlaneFrequencyMeasure) =
      ∫ r in s.val..t.val,
        -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ
          (G r i j • cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i)
          (cellFrequencyPlaneGradient test j)) -
        ∑ i : Fin 2, inner ℝ
          (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v r i)
            (cellDriftTorusSymbol_measurable v hv r i) C (hC r i)
              (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i))
          (cellFrequencyPlaneValue test) := by
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  apply integral_congr_ae
  exact (cellEnergyJointGenerator_planeForm_ae hab G hG v hv V hb C hCpos hC F test).filter_mono
    (ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.property.1 t.property.2)) le_rfl))

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The original molecular envelope supplies a graph budget uniform in the family and its masses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylor_normalized_graph_budget (F : ChartedFamily ι h D P Ctx)
    (Hdepth : ℕ) (hdepth : F.HasDepthAtMost Hdepth) (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CT : ℝ) (hCT : 0 ≤ CT) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks ≤ J)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (hrow : ∀ v, ∑ u, b v u ≤ 1)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) :
    let price := fun v u => Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
    let θ := originalTaylorGraphConstant Ks Kmax CT C
    (∀ v u, 0 ≤ normalizedFiniteGraph θ price v u) ∧
    (∀ v, ∑ u, normalizedFiniteGraph θ price v u ≤ 1) ∧
    (∀ u, ∑ v, normalizedFiniteGraph θ price v u ≤ 1) ∧
    (∀ v u, normalizedFiniteGraph θ price v u ≠ 0 →
      familyDepthRank F Hdepth u < familyDepthRank F Hdepth v) := by
  classical
  let price := fun v u => Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
  have hp (v u : ι) : 0 ≤ price v u := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun α _ =>
      originalTaylorPrice_nonneg F K Ks Kmax dom ν e E ρ CT hν.le hE.le hρ.le hCT v u α))
  obtain ⟨hr, hc⟩ := originalTaylorPrice_graph_budget F π K Ks Kmax hK dom ν e E ρ CT hCT
    hν hE hρ C J b hKs henv hb hrow hcol
  obtain ⟨hn, hnr, hnc⟩ := normalizedFiniteGraph_budget
    (originalTaylorGraphConstant Ks Kmax CT C) (originalTaylorGraphConstant_nonneg Ks Kmax CT C)
    price hp hr hc
  refine ⟨hn, hnr, hnc, ?_⟩
  apply normalizedFiniteGraph_support
  intro v u hne
  by_contra hlt
  have hz := originalSource_sum_zero_of_rank F Hdepth hdepth v u (Nat.le_of_not_gt hlt)
    (fun α => originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
  exact hne (by simp only [hz, mul_zero])

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The weighted a priori estimate uses exactly the coefficient and chart assumptions of
`weighted_energy_plane`. -/

theorem weighted_energy_plane_component_lower_apriori (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
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
        (_hF : ∀ x, (∫⁻ t in Set.Icc ta tb, ENNReal.ofReal (‖F x t‖ ^ 2)) < ⊤),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          ∀ x,
            (⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot x) (V x t)) +
              (∫⁻ t in Set.Icc ta tb, weightedGradFactorialNormSq n ϖ zc rstar (Kslot x) (Vw x t)) ≤
              ENNReal.ofReal C * (weightedFactorialNormSq n ϖ zc rstar (Kslot x) (V₀ x) +
                16 * ∫⁻ t in Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot x) (F x t)) := by
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
  have hh := scalarChain_polynomial_factorial_lower_supremum ta tb ht κ Kmax
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

/-! The weighted a priori estimate uses exactly the coefficient and chart assumptions of
`weighted_energy_plane`. -/

theorem weighted_energy_plane_lower_apriori (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
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
        (_hF : ∀ x, (∫⁻ t in Set.Icc ta tb, ENNReal.ofReal (‖F x t‖ ^ 2)) < ⊤),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) →
          geometryEnergyNorm π Kslot n ϖ zc rstar ta tb V Vw ≤
            ENNReal.ofReal C *
              (geometryDataNorm π Kslot n ϖ zc rstar V₀ +
                geometryFluxNorm π Kslot n ϖ zc rstar ta tb F) := by
  obtain ⟨L, hL, hreserve⟩ := exists_radius_absorption_reserve
    (Real.exp (18 * Cw n)) (metricRadiusConstant Kmax CG) (Real.exp_pos _).le
  let A := L ^ (2 * Kmax) * 9 * (Cw n) ^ 2 * Real.exp (18 * Cw n)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(16 * A) ^ (1 / 2 : ℝ), Real.rpow_nonneg (by positivity) _, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hsln
  obtain ⟨Vbound, hvbound⟩ := hv_bdd
  apply geometryEnergyNorm_of_component_lower_bounds π Kslot n ϖ zc rstar ta tb
    V₀ F V Vw A hA
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
  have hh := scalarChain_polynomial_factorial_lower_supremum ta tb ht κ Kmax
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

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Each actual metric and drift adjoint term belongs to the Bochner L2 time class. -/

theorem planeRealBlochMetricDualTerm_memLp
    (μ : Measure ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t))
    (u : ℝ → PlaneHk Set.univ 1 ℝ) (hu : MemLp u 2 μ) (i j : Fin 2) :
    MemLp (fun t => G t i j •
      (planeRealH1GradientCLM j).adjoint (planeRealH1GradientCLM i (u t))) 2 μ :=
  (planeCellMetricTimeEntry_memLp μ G hG i j).smul
    ((planeRealH1GradientCLM j).adjoint.comp_memLp'
      ((planeRealH1GradientCLM i).comp_memLp' hu))

theorem planeRealBlochDriftDualTerm_memLp
    (μ : Measure ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u : ℝ → PlaneHk Set.univ 1 ℝ) (hu : MemLp u 2 μ) (i : Fin 2) :
    MemLp (fun t => (planeHkValueOperator (E := ℝ) 1).adjoint
      (planeRealDriftMultiplier v hv t i C (hC t i) (planeRealH1GradientCLM i (u t)))) 2 μ :=
  (planeHkValueOperator (E := ℝ) 1).adjoint.comp_memLp'
    (planeRealDriftMultiplier_timeMemLp μ v hv i C hC0 (fun t => hC t i)
      (fun t => planeRealH1GradientCLM i (u t))
      ((planeRealH1GradientCLM i).comp_memLp' hu))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy for the genuine single-pulse generator at the original quadratic price. -/

theorem interiorPulseHigherFullGenerator_smooth_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) :
    2 * inner ℝ
        (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      constructedHigherEnergyGrowth K R (ν / ocMeanFlux α q Λ ζ m ν) k *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let U := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let W := finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let B := ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖
  let A := constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)
  have ha := interiorPulseHigherAdvectionCLM_adjacent_polynomial_bound K hΛ hζ hν hr y₀ hslot hv θ R hθ t W
  rw [finiteSmoothPeriodicHk_truncate (K := K + 1) (L := K + 2) (by omega) f hf hp] at ha
  have hy := real_inner_transport_young
    (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ t W) U A B ha
  have hb := finiteSmoothHigher_adjacent_energy_le K f hf hp
  have hd := finiteSmoothHigherDiffusion_energy K f hf hp G hG θ t
  have ht : (∑ i : Fin 2, ‖θ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hc : |inner ℝ (torusHigherScalarCLM K (κ t) U) U| ≤
      (k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2 := by
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (((torusHigherScalarCLM K (κ t)).le_opNorm U).trans
          (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K (κ t) k hk) (norm_nonneg U)))
        (norm_nonneg U))).trans_eq (by ring)
  have hdt := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖U‖)
  have hat := neg_le_abs (inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ t W) U)
  have hct := le_abs_self (inner ℝ (torusHigherScalarCLM K (κ t) U) U)
  simp only [interiorPulseHigherFullGeneratorCLM, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left]
  rw [finiteSmoothPeriodicHk_truncate (K := K) (L := K + 2) (by omega) f hf hp]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤ _
  change 2 * inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U + _ ≤ _ at hd
  change B ^ 2 ≤ ‖U‖ ^ 2 + _ at hb
  unfold constructedHigherEnergyGrowth
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤
    (528 * R ^ 2 + 1 / 4 + 4 * A ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2
  nlinarith

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual measurable-time metric and rough drift give an L2-in-time H1 dual. -/

local instance planeRealBlochGeneratorDualTimeLpSeminormedAddCommGroup : SeminormedAddCommGroup (PlaneHk Set.univ 1 ℝ) :=
  (inferInstance : NormedAddCommGroup (PlaneHk Set.univ 1 ℝ)).toSeminormedAddCommGroup

local instance planeRealBlochGeneratorDualTimeLpAddCommMonoid : AddCommMonoid (PlaneHk Set.univ 1 ℝ) :=
  (inferInstance : NormedAddCommGroup (PlaneHk Set.univ 1 ℝ)).toAddCommMonoid

local instance planeRealBlochGeneratorDualTimeLpModule : Module ℝ (PlaneHk Set.univ 1 ℝ) :=
  (inferInstance : NormedSpace ℝ (PlaneHk Set.univ 1 ℝ)).toModule

theorem planeRealBlochGeneratorDual_timeMemLp
    (μ : Measure ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u : ℝ → PlaneHk Set.univ 1 ℝ) (hu : MemLp u 2 μ) :
    MemLp (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t) (u t)) 2 μ := by
  simp only [planeRealBlochGeneratorDual, sub_apply, neg_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply]
  exact (memLp_finsetSum (ε' := PlaneHk Set.univ 1 ℝ) Finset.univ (fun i _ =>
    memLp_finsetSum (ε' := PlaneHk Set.univ 1 ℝ) Finset.univ
      (fun j _ => planeRealBlochMetricDualTerm_memLp μ G hG u hu i j))).neg.sub
    (memLp_finsetSum (ε' := PlaneHk Set.univ 1 ℝ) Finset.univ
      (fun i _ => planeRealBlochDriftDualTerm_memLp μ v hv C hC0 hC u hu i))

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A uniform graph constant covers the normalized row's low-frequency and Taylor prices. -/

def constructedScalarGraphPrice (Cw : ℝ) : ℝ :=
  max (fibreCoefficientGraphBound Cw) (max 4 (64 / fibreCoefficientMajorantRadius Cw))

theorem constructedScalarGraphPrice_graph (Cw : ℝ) :
    fibreCoefficientGraphBound Cw ≤ constructedScalarGraphPrice Cw := le_max_left _ _

theorem constructedScalarGraphPrice_four (Cw : ℝ) :
    4 ≤ constructedScalarGraphPrice Cw := (le_max_left _ _).trans (le_max_right _ _)

theorem constructedScalarGraphPrice_linear (Cw : ℝ) :
    64 / fibreCoefficientMajorantRadius Cw ≤ constructedScalarGraphPrice Cw :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem constructedScalarGraphPrice_pos (Cw : ℝ) :
    0 < constructedScalarGraphPrice Cw :=
  lt_of_lt_of_le (by norm_num) (constructedScalarGraphPrice_four Cw)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The universal higher energy price bounds the genuine pulse extension. -/

 theorem interiorPulseHigherFullGenerator_smooth_adjacent_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ
        (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have he := interiorPulseHigherFullGenerator_smooth_energy K hΛ hζ hν hr y₀ hslot hv G hG θ R hθ κ t k hk f hf hp
  have hg := finiteSmoothHigherGradientEnergy_native_identity K f hf hp
  have hprice := mul_le_mul_of_nonneg_right
    (constructedHigherEnergyGrowth_polynomial_bound K R (ν / ocMeanFlux α q Λ ζ m ν) k
      ((norm_nonneg _).trans hk))
    (sq_nonneg ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖)
  apply le_trans ?_ hprice
  nlinarith only [he, hg]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The real plane trace starts at the prescribed genuine real L2 datum. -/

theorem planeBlochEnergyRealTrace_initial {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    cellEnergyPlaneRealTrace hab
      (planeBlochEnergyField hab G hG v V hv hb
        (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f))) a =
      planeL2ZeroCarrier f := by
  unfold cellEnergyPlaneRealTrace
  rw [projIcc_of_mem hab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
  rw [planeBlochEnergyField_initial]
  change planeL2ZeroCarrier (planeComplexRealPartL2
    ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
      ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)) (ofRealL2 volume f)))) = _
  rw [(planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm_apply_apply]
  change planeL2ZeroCarrier (reL2 volume (ofRealL2 volume f)) = planeL2ZeroCarrier f
  rw [reL2_ofRealL2]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! A genuine L2 flux is sufficient for the exact rough generator pairing. -/

theorem planeRealBlochNativeFlux_pair
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (w φ : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual G v hv t C hC w + planeSourceDual 0 S) φ =
      ∫ x, planeRealBlochSpatialRhs G (v t) w φ x -
        ∑ i : Fin 2, inner ℝ (S i x) (planeRealH1TestGradient φ i x) := by
  rw [inner_add_left, planeRealBlochGeneratorDual_spatialPair,
    planeSourceDual_pair, inner_zero_left, zero_sub, planeFlux_inner_eq_integral]
  have hi := planeRealBlochSpatialRhs_integrable G v hv t C hC w φ
  have hf : Integrable (fun x => ∑ i : Fin 2,
      inner ℝ (S i x) (planeRealH1TestGradient φ i x)) volume :=
    integrable_finsetSum Finset.univ (fun i _ => L2.integrable_inner _ _)
  rw [← sub_eq_add_neg]
  change (∫ x, planeRealBlochSpatialRhs G (v t) w φ x) -
    (∫ x, ∑ i : Fin 2, inner ℝ (S i x) (planeRealH1TestGradient φ i x)) = _
  exact (integral_sub hi hf).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full higher energy for the signed time-reflected constructed drift. -/

def interiorPulseReflectedFullGeneratorCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t +
    interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ (-t) +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

theorem interiorPulseReflectedFullGenerator_smooth_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) :
    2 * inner ℝ
        (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      constructedHigherEnergyGrowth K R (ν / ocMeanFlux α q Λ ζ m ν) k *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let U := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let W := finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let B := ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖
  let A := constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)
  have ha := interiorPulseHigherAdvectionCLM_adjacent_polynomial_bound K hΛ hζ hν hr y₀ hslot hv θ R hθ (-t) W
  rw [finiteSmoothPeriodicHk_truncate (K := K + 1) (L := K + 2) (by omega) f hf hp] at ha
  have hy := real_inner_transport_young
    (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ (-t) W) U A B ha
  have hb := finiteSmoothHigher_adjacent_energy_le K f hf hp
  have hd := finiteSmoothHigherDiffusion_energy K f hf hp (fun s => G (-s)) (cellMetric_timeReverse hG) θ t
  have ht : (∑ i : Fin 2, ‖θ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hc : |inner ℝ (torusHigherScalarCLM K (κ t) U) U| ≤
      (k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2 := by
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (((torusHigherScalarCLM K (κ t)).le_opNorm U).trans
          (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K (κ t) k hk) (norm_nonneg U)))
        (norm_nonneg U))).trans_eq (by ring)
  have hdt := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖U‖)
  have hat := le_abs_self (inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ (-t) W) U)
  have hct := le_abs_self (inner ℝ (torusHigherScalarCLM K (κ t) U) U)
  simp only [interiorPulseReflectedFullGeneratorCLM, add_apply,
    ContinuousLinearMap.comp_apply, inner_add_left]
  rw [finiteSmoothPeriodicHk_truncate (K := K) (L := K + 2) (by omega) f hf hp]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U +
    inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ (-t) W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤ _
  change 2 * inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U + _ ≤ _ at hd
  change B ^ 2 ≤ ‖U‖ ^ 2 + _ at hb
  unfold constructedHigherEnergyGrowth
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U +
    inner ℝ (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hslot hv θ (-t) W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤
    (528 * R ^ 2 + 1 / 4 + 4 * A ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2
  nlinarith

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full original Taylor family admits a native forcing and a normalized row bound at shifted moments. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorRow_native_flux_exists_supported (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      (∀ v u, 0 ≤ b₀ v u) → (∀ v, ∑ u, b₀ v u ≤ 1) → (∀ u, ∑ v, b₀ v u ≤ 1) →
      ∀ (v : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      (∀ u, MemLp (U u) 2 (volume.restrict (Set.Icc a b))) →
      (∀ u, Nonempty (F.Γ v u) →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U u t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        (MemLp V 2 (volume.restrict (Set.Icc a b))) ∧
        ((∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ u, ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U u t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          (π v)⁻¹ * planeFactorialDensity (ρ / e) (V t) z ≤
            originalTaylorGraphConstant Ks Kmax CT C * (polynomialMomentRoot ϖ z ^ Ks) ^ 2 *
              ∑ u, (Real.sqrt (π u / π v) *
                (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)) *
                  ((π u)⁻¹ * planeGradFactorialDensity (ρ / e) (U u t) z)) := by
  classical
  obtain ⟨CT, hCT, hpairs⟩ := originalTaylorPair_native_flux_exists_supported (ι := ι) (h := h)
    (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas hb₀ hrow hcol
    v p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  have hex (u : ι) := hpairs F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n (U u) (hU u) (henergy u)
  choose V hV hVe hvalue hdensity using hex
  refine ⟨fun t => ∑ u, V u t, ?_, ?_, ?_, ?_⟩
  ·
    exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun u _ => hV u)
  ·
    exact (Weighted.finite_weighted_sobolev_time_sum n ϖ 0 (ρ / e) (div_pos hρ he)
      (volume.restrict (Set.Icc a b)) V hV hVe).2
  ·
    filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun u => V u t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun u _ => hzs u))
  · obtain ⟨hr, _⟩ := originalTaylorPrice_graph_budget F π K Ks Kmax hK dom ν e E ρ CT hCT
      hν hE hρ C J b₀ hKs henv hb₀ hrow hcol
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    exact nativeFlux_normalized_row_density_budget (ρ / e) (fun u => V u t) π hπ v
      (fun u => ∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
      (fun u => Finset.sum_nonneg (fun α _ =>
        originalTaylorPrice_nonneg F K Ks Kmax dom ν e E ρ CT hν.le hE.le hρ.le hCT v u α))
      (originalTaylorGraphConstant Ks Kmax CT C) (hr v)
      (fun z => (polynomialMomentRoot ϖ z ^ Ks) ^ 2) (fun _ => sq_nonneg _)
      (fun u z => planeGradFactorialDensity (ρ / e) (U u t) z)
      (fun u z => planeGradFactorialDensity_nonneg (ρ / e) (U u t) z)
      (fun u => by simpa only [mul_assoc] using ht u)
end

/-! The full original Taylor family admits a native forcing and a normalized row bound at shifted moments. -/

theorem originalTaylorRow_native_flux_exists_supported_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      (∀ v u, 0 ≤ b₀ v u) → (∀ v, ∑ u, b₀ v u ≤ 1) → (∀ u, ∑ v, b₀ v u ≤ 1) →
      ∀ (v : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      (∀ u, MemLp (U u) 2 (volume.restrict (Set.Icc a b))) →
      (∀ u, Nonempty (F.Γ v u) →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U u t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        (MemLp V 2 (volume.restrict (Set.Icc a b))) ∧
        ((∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ u, ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U u t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          (π v)⁻¹ * planeFactorialDensity (ρ / e) (V t) z ≤
            originalTaylorGraphConstant Ks Kmax CT C * (polynomialMomentRoot ϖ z ^ Ks) ^ 2 *
              ∑ u, (Real.sqrt (π u / π v) *
                (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)) *
                  ((π u)⁻¹ * planeGradFactorialDensity (ρ / e) (U u t) z)) := by
  classical
  obtain ⟨CT, hCT, hpairs⟩ := originalTaylorPair_native_flux_exists_supported_uniform Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas hb₀ hrow hcol
    v p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  have hex (u : ι) := hpairs F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n (U u) (hU u) (henergy u)
  choose V hV hVe hvalue hdensity using hex
  refine ⟨fun t => ∑ u, V u t, ?_, ?_, ?_, ?_⟩
  ·
    exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun u _ => hV u)
  ·
    exact (Weighted.finite_weighted_sobolev_time_sum n ϖ 0 (ρ / e) (div_pos hρ he)
      (volume.restrict (Set.Icc a b)) V hV hVe).2
  ·
    filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun u => V u t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun u _ => hzs u))
  · obtain ⟨hr, _⟩ := originalTaylorPrice_graph_budget F π K Ks Kmax hK dom ν e E ρ CT hCT
      hν hE hρ C J b₀ hKs henv hb₀ hrow hcol
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    exact nativeFlux_normalized_row_density_budget (ρ / e) (fun u => V u t) π hπ v
      (fun u => ∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
      (fun u => Finset.sum_nonneg (fun α _ =>
        originalTaylorPrice_nonneg F K Ks Kmax dom ν e E ρ CT hν.le hE.le hρ.le hCT v u α))
      (originalTaylorGraphConstant Ks Kmax CT C) (hr v)
      (fun z => (polynomialMomentRoot ϖ z ^ Ks) ^ 2) (fun _ => sq_nonneg _)
      (fun u z => planeGradFactorialDensity (ρ / e) (U u t) z)
      (fun u z => planeGradFactorialDensity_nonneg (ρ / e) (U u t) z)
      (fun u => by simpa only [mul_assoc] using ht u)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full reflected drift has the same quadratic polynomial adjacent-energy price. -/

 theorem interiorPulseReflectedFullGenerator_smooth_adjacent_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ
        (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have he := interiorPulseReflectedFullGenerator_smooth_energy K hΛ hζ hν hr y₀ hslot hv G hG θ R hθ κ t k hk f hf hp
  have hg := finiteSmoothHigherGradientEnergy_native_identity K f hf hp
  have hprice := mul_le_mul_of_nonneg_right
    (constructedHigherEnergyGrowth_polynomial_bound K R (ν / ocMeanFlux α q Λ ζ m ν) k
      ((norm_nonneg _).trans hk))
    (sq_nonneg ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖)
  apply le_trans ?_ hprice
  nlinarith only [he, hg]

end AVRegularity.CycleWords
end
