-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.OriginalConstituentPriceReindex
import AVRegularity.CycleWords.ConstantMetricClippedFactorialENNReal
public import AVRegularity.CycleWords.CellTransverseGalerkinCorrectionLocalGrowthEnergy
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorConstituent_native_flux_exists_all (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => taylorSlow 0 Ks (fun X => F.flux p c v u γ d I (s * t) X (z + φ) k)
            X0 ((e / E) • z) • Weighted.fluxCoordinateInjection k (F.identity v u γ).map
              (planeJetOrder (U t) (d - 1) I z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
            (CT * (∑ r ∈ Finset.range (Ks + 1),
              molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r) *
                ‖(F.identity v u γ).map‖) ^ 2 *
                  (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorConstituent_native_flux_exists (ι := ι) (h := h)
    (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy
  by_cases hγ : (F.identity v u γ).map = 0
  · have hzero : MemLp
        (fun _ : ℝ => (0 : PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v))))
        2 (volume.restrict (Set.Icc a b)) :=
      Weighted.planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc a b))
    refine ⟨fun _ => 0, hzero, ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only [hγ, Weighted.fluxCoordinateInjection_zero, zero_apply, smul_zero] using
          (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v)))
    · exact Filter.Eventually.of_forall (fun t => by
        filter_upwards [planeFactorialDensity_zero_ae
          (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
        simp only [hz, hγ, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])
  · exact hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
      v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The original analytic envelope supplies finite positive constituent prices and controls each reserved jet without cancelling identities. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSourcePriceENN_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      (∑ α : OriginalSourceIndex F v u, analyticOriginalSourcePriceENN F dom Ks J v u α) ≤
      2 * ENNReal.ofReal (b v u) := by
  have hh := henv.2 v u
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hh
  rw [analyticOriginalSourcePriceENN_sum_eq]
  convert mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ≥0∞) ≤ 2) using 1; ring

theorem analyticOriginalSourcePriceENN_ne_top (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) (α : OriginalSourceIndex F v u) :
    analyticOriginalSourcePriceENN F dom Ks J v u α ≠ ⊤ := by
  have hh := analyticOriginalSourcePriceENN_envelope_le F π dom Ks J b henv v u
  have hm : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hs := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hh) hm).ne
  exact ne_top_of_le_ne_top hs (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ α))

theorem analyticOriginalSourcePrice_reserved_jet_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) (α : OriginalSourceIndex F v u)
    (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ J) :
    ‖(F.identity v u α.1).map‖ *
      (jetSupFam (fun x : F.Index => dom x.1 x.2) r q
        (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1)).toReal ≤
      analyticOriginalSourcePrice F dom Ks J v u α := by
  classical
  have hj : jetSupFam (fun x : F.Index => dom x.1 x.2) r q
      (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1) ≤
      ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1),
        jetSupFam (fun x : F.Index => dom x.1 x.2) r q
          (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1) := by
    let jet := fun r q => jetSupFam (fun x : F.Index => dom x.1 x.2) r q
      (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1)
    have hi : jet r q ≤ ∑ q ∈ Finset.range (J + 1), jet r q :=
      Finset.single_le_sum (f := jet r) (fun _ _ => bot_le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
    have ho : (∑ q ∈ Finset.range (J + 1), jet r q) ≤
        ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1), jet r q :=
      Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (J + 1), jet r q)
        (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    exact hi.trans ho
  have hh := ENNReal.toReal_mono (analyticOriginalSourcePriceENN_ne_top F π hπ dom Ks J b henv v u α)
    (mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ‖(F.identity v u α.1).map‖))
  simpa only [analyticOriginalSourcePrice, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] using hh

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Summing native source prices counts each original identity with its molecular order sum. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalSourcePrice_sum_eq (F : ChartedFamily ι h D P Ctx)
    (K : ι → ℕ) (Kmax : ℕ) (dom : F.Domain) (ν e E ρ : ℝ) (v u : ι) :
    (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α) =
      (2 * Real.sqrt (multiplicationDensityBudget (K v)) * (4 : ℝ) ^ Kmax *
        (Kmax.factorial : ℝ) ^ 2) *
      ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          molecularRealPrice ν ρ (K v) (d - 2)
            (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type,
    originalSourcePrice, Fin.sum_univ_two]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  conv_rhs =>
    arg 2
    arg 2
    rw [← Finset.sum_coe_sort]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem originalSourcePrice_sum_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) :
    Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α) ≤
        (2 * Real.sqrt (multiplicationDensityBudget (K v)) * (4 : ℝ) ^ Kmax *
          (Kmax.factorial : ℝ) ^ 2 * |C 0|) * b v u := by
  have hh := molecularRealEnvelope_sum_le F π K dom ν e E ρ hν hE hρ C J b
    henv v u hb 0 (Nat.zero_le J)
  simp only [pow_zero, inv_one, mul_one] at hh
  have hs := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 2 * Real.sqrt (multiplicationDensityBudget (K v)) *
      (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2)
  rw [originalSourcePrice_sum_eq]
  convert hs using 1
  · ring
  · ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalTaylorConstituent_native_flux_exists_all_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => taylorSlow 0 Ks (fun X => F.flux p c v u γ d I (s * t) X (z + φ) k)
            X0 ((e / E) • z) • Weighted.fluxCoordinateInjection k (F.identity v u γ).map
              (planeJetOrder (U t) (d - 1) I z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
            (CT * (∑ r ∈ Finset.range (Ks + 1),
              molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r) *
                ‖(F.identity v u γ).map‖) ^ 2 *
                  (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorConstituent_native_flux_exists_uniform Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy
  by_cases hγ : (F.identity v u γ).map = 0
  · have hzero : MemLp
        (fun _ : ℝ => (0 : PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v))))
        2 (volume.restrict (Set.Icc a b)) :=
      Weighted.planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc a b))
    refine ⟨fun _ => 0, hzero, ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only [hγ, Weighted.fluxCoordinateInjection_zero, zero_apply, smul_zero] using
          (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v)))
    · exact Filter.Eventually.of_forall (fun t => by
        filter_upwards [planeFactorialDensity_zero_ae
          (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
        simp only [hz, hγ, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])
  · exact hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
      v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Fibre weak increments integrated over frequency with genuine joint integrability. -/

theorem planeBlochEnergyIntegratedIncrement {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure)
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val)
    (test : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    let F := planeBlochEnergyField hab G hG v V hv hb f
    inner ℝ ((cellEnergyTraceAtCLM a b t).compLp F) (centeredCellBlochValueField test) -
      inner ℝ ((cellEnergyTraceAtCLM a b s).compLp F) (centeredCellBlochValueField test) =
        ∫ r in s.val..t.val, ∫ θ, cellGeneratorForm
          ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb r
            (cellComplexH1RealEquiv (cellEnergyJointH1 hab F (θ, r)))
            (cellComplexH1RealEquiv (test θ)) ∂centeredPlaneFrequencyMeasure := by
  let F := planeBlochEnergyField hab G hG v V hv hb f
  let q := fun θ r => cellGeneratorForm
    ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb r
      (cellComplexH1RealEquiv (cellEnergyJointH1 hab F (θ, r)))
      (cellComplexH1RealEquiv (test θ))
  have hsub : Ioc s.val t.val ⊆ Icc a b :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc s.property.1 t.property.2)
  have hq : Integrable (Function.uncurry q)
      (centeredPlaneFrequencyMeasure.prod (volume.restrict (Ioc s.val t.val))) := by
    exact (cellPhysicalGenerator_joint_integrable a b G hG v V hv hb
      (cellEnergyJointH1 hab F) test).mono_measure
        (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  have hi := planeBlochEnergyJointIncrement hab G hG v V hv hb f
  have ht := (cellEnergyTraceAtCLM a b t).coeFn_compLp F
  have hs := (cellEnergyTraceAtCLM a b s).coeFn_compLp F
  have hvf := cellComplexH1ValueCLM.coeFn_compLp test
  change (∫ θ, inner ℝ (((cellEnergyTraceAtCLM a b t).compLp F) θ)
      (centeredCellBlochValueField test θ) ∂centeredPlaneFrequencyMeasure) -
    (∫ θ, inner ℝ (((cellEnergyTraceAtCLM a b s).compLp F) θ)
      (centeredCellBlochValueField test θ) ∂centeredPlaneFrequencyMeasure) =
        ∫ r in s.val..t.val, ∫ θ, q θ r ∂centeredPlaneFrequencyMeasure
  rw [← integral_sub (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  calc
    _ = ∫ θ, (∫ r in s.val..t.val, q θ r) ∂centeredPlaneFrequencyMeasure := by
      apply integral_congr_ae
      filter_upwards [hi, ht, hs, hvf] with θ hiθ htθ hsθ hvθ
      change inner ℝ (((cellEnergyTraceAtCLM a b t).compLp F) θ)
          (cellComplexH1ValueCLM.compLp test θ) -
        inner ℝ (((cellEnergyTraceAtCLM a b s).compLp F) θ)
          (cellComplexH1ValueCLM.compLp test θ) = _
      rw [htθ, hsθ, hvθ, cellEnergyTraceAtCLM_apply, cellEnergyTraceAtCLM_apply]
      exact hiθ s t hst (test θ)
    _ = _ := by
      simp only [intervalIntegral.integral_of_le hst]
      exact integral_integral_swap hq

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The literal source flux of a response level: original Taylor constituents
at that level and the positive metric polynomial at the preceding level. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def geometryResponseSourceFlux (F : ChartedFamily ι h D P Ctx)
    (J Ks : ℕ) (K : ι → ℕ) (p : P) (c : Ctx p)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (s δ : ℝ) (X0 phase : Vec 2)
    (Uw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (j : Fin (J + 1)) (x : ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h x) :=
  (∑ u, ∑ α : OriginalSourceIndex F x u,
    taylorSlow 0 Ks (fun X => F.flux p c x u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + phase) α.2.2.2)
      X0 (δ • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity x u α.1).map
        (planeJetOrder (Uw j u t) (α.2.1.1 - 1) α.2.2.1 z)) +
  ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
    WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l •
      (Uw j' x t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) else 0

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Each original nonzero sampled constituent produces a genuine native forcing with its molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalPair_native_flux_exists (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (v u : ι) (p : P) (c : Ctx p)
    (s a b ϖ : ℝ) (hs : s ≠ 0) (hϖ : 0 < ϖ) (X0 φ : Vec 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (U : ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hU : MemLp U 2 (volume.restrict (Set.Icc a b))) :
    ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        (fun z => ∑ α : OriginalSourceIndex F v u,
          F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 •
            Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
              (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
        planeFactorialDensity (ρ / e) (V t) z ≤
          (∑ α : OriginalSourceIndex F v u,
            originalSourcePrice F K Kmax dom ν e E ρ v u α) ^ 2 *
              planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  have hex (α : OriginalSourceIndex F v u) := originalConstituent_native_flux_exists_all
    F π hπ K Kmax hK hdesc dom ν e E ρ hν he hE hρ C J b₀ henv hmeas
      v u α.1 α.2.1.1 α.2.1.2 α.2.2.1 p c s a b ϖ hs hϖ X0 φ α.2.2.2 hwindow U hU
  choose V hV hvalue hdensity using hex
  refine ⟨fun t => ∑ α, V α t, ?_, ?_, ?_⟩
  · exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun α _ => hV α)
  · filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun α => V α t)
      (fun i : Fin 0 => Fin.elim0 i)
    have hh : ∀ᵐ z ∂volume, ∀ α, planeValue (V α t) z =
        F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 •
          Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
            (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z) := ae_all_iff.mpr ht
    filter_upwards [hv, hh] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun α _ => hzs α))
  · filter_upwards [ae_all_iff.mpr hdensity] with t ht
    apply nativeFactorialDensity_sum_price_le
    · exact fun α => originalSourcePrice_nonneg F K Kmax dom ν e E ρ hν.le hρ.le v u α
    · exact fun z => planeGradFactorialDensity_nonneg (ρ / e) (U t) z
    · intro α
      filter_upwards [ht α] with z hz
      simpa only [originalSourcePrice, mul_pow,
        Real.sq_sqrt (multiplicationDensityBudget_nonneg (K v))] using hz

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_real_lower_budget
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
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, (∫⁻ t in Icc a b, ENNReal.ofReal (‖F i t‖ ^ 2)) < ⊤)
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (hG1 : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (clip ρ : ℝ) (hclip : 0 < clip)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1) (CG : ℕ → ℝ)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
:
    let q := fun t x => clipWeight clip (C.W m t x)
    let d := fun t => rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
    let fenergy := fun t => rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy ρ (q t) (u i t).toFunction.jet + (∫ s in a..t, d s) ≤
      (rawWeightedFactorialEnergy ρ (q a) (f i).toFunction.jet +
        16 * (∫⁻ s in Icc a b, ENNReal.ofReal (fenergy s)).toReal +
        (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) *
          (∫ s in a..b, d s)) * Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  let q := fun t x => clipWeight clip (C.W m t x)
  let d := fun t => rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
  let fe := fun t => rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet
  let c := 16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  have hd0 t : 0 ≤ d t := rawWeightedGradientEnergy_nonneg _ _ (hq0 t) _
  have hf0 t : 0 ≤ fe t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hdi := rawWeightedGradient_time_integrable C m hm clip hclip ρ
    (volume.restrict (Icc a b)) (w i) (hsln.2.1 i)
  have hfi := bounded_raw_factorial_lower_integral_finite ρ q
    (fun t => (chartWeights_clipped_spatial_regularity C m hm t clip hclip).1.continuous)
    clip hclip.le hq0 (fun t x => clipWeight_le_bound hclip (C.pos m hm t x))
    (volume.restrict (Icc a b)) (F i) (hF i)
  have hh := scalarChain_clipped_factorial_lower_integral a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip ρ hclip hρ ν hν
    hsmall hstrainSmall δ hδ hg hscale CG hmetricJets hdiv hwa hwb
  intro t ht
  have hr := lower_integral_real_energy_budget fe d hf0 hd0 hdi hfi 16 c
    (rawWeightedFactorialEnergy ρ (q a) (f i).toFunction.jet)
    (Real.exp (18 * C.lam m * (t - a))) _ (by norm_num) hc
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) _) (Real.exp_pos _).le (hh t ht)
  have heq : (∫ s in a..b, d s) = ∫ s, d s ∂volume.restrict (Icc a b) := by
    rw [intervalIntegral.integral_of_le hab, restrict_Ioc_eq_restrict_Icc]
  simpa only [← heq] using hr

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Original source prices and forcing sums vanish outside the strictly descending graph rank. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalSource_sum_zero_of_rank (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H) (v u : ι)
    (hr : familyDepthRank F H v ≤ familyDepthRank F H u)
    {M : Type*} [AddCommMonoid M] (f : OriginalSourceIndex F v u → M) :
    ∑ α, f α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro α _
  have hh := familyDepthRank_strict F H hdepth (u := u) (v := v) ⟨α.1⟩
  exact False.elim (Nat.not_lt_of_ge hr hh)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual reserved mixed jets are controlled almost everywhere by their original positive constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSource_reserved_jet_ae_bound (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) (α : OriginalSourceIndex F v u)
    (p : P) (c : Ctx p) (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ J) :
    ∀ᵐ t ∂volume, ∀ X, (t, X) ∈ dom p c → ∀ z,
      ‖(F.identity v u α.1).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
          (F.slowFlux 1 p c v u α.1 α.2.1.1 α.2.2.1 t Y) z) X‖ ≤
        analyticOriginalSourcePrice F dom Ks J v u α := by
  by_cases hz : (F.identity v u α.1).map = 0
  · exact Filter.Eventually.of_forall (fun _ _ _ _ => by
      rw [hz, norm_zero, zero_mul]
      exact ENNReal.toReal_nonneg)
  have hf := Weighted.analyticEnvelope_reserved_jet_ne_top F π hπ dom Ks J b henv v u α.1 hz
    α.2.1.1 α.2.1.2 α.2.2.1 r q hr hq
  have hp : jetSupOn (dom p c) r q (F.slowFlux 1 p c v u α.1 α.2.1.1 α.2.2.1) ≤
      jetSupFam (fun x : F.Index => dom x.1 x.2) r q
        (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1) :=
    le_iSup (fun x : F.Index => jetSupOn (dom x.1 x.2) r q
      (F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1)) ⟨p, c⟩
  have hj := Weighted.jetSupOn_ae_norm_bound (dom p c) r q
    (F.slowFlux 1 p c v u α.1 α.2.1.1 α.2.2.1) (ne_top_of_le_ne_top hf hp)
  have hm := ENNReal.toReal_mono hf hp
  have hprice := analyticOriginalSourcePrice_reserved_jet_le F π hπ dom Ks J b henv v u α r q hr hq
  filter_upwards [hj] with t ht
  intro X hX z
  exact (mul_le_mul_of_nonneg_left ((ht X hX z).trans hm) (norm_nonneg _)).trans hprice

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The admissible-order source flux is exactly the forcing indexed by original identities. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem originalCellSource_eval_order_flux (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (p : P) (c : Ctx p) (v u : ι)
    (ev : (Vec 2 → ℝ) → Vec 2 → ℝ) (s t : ℝ) (φ z : Vec 2) (U : PlaneHk Set.univ (K u + 1) (h u)) :
    (∑ d : admissibleOrders K D v u,
      slowEvalCoefficient ev
        (F.cellFiber s φ p c v u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
        (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
          planeJetOrder U (d.1 - 1) word z))) =
      ∑ α : OriginalSourceIndex F v u,
        ev (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2) z •
          Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
            (planeJetOrder U (α.2.1.1 - 1) α.2.2.1 z) := by
  classical
  let f := fun (γ : F.Γ v u) (d : ℕ) => ∑ w : DerivativeWord2 (d - 1), ∑ k : Fin 2,
    ev (fun X => F.flux p c v u γ d w (s * t) X (z + φ) k) z •
      Weighted.fluxCoordinateInjection k (F.identity v u γ).map (planeJetOrder U (d - 1) w z)
  have hh := original_order_reindex F K hdesc v u f
  unfold admissibleOrders at hh ⊢
  simp_rw [originalCellFiber_slowFlux_expansion]
  change (∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u,
    if d.1 ≤ (F.identity v u γ).maxOrder then f γ d.1 else 0) = _
  refine hh.trans ?_
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro γ _
  exact (Finset.sum_coe_sort (Finset.Icc 2 (F.identity v u γ).maxOrder) (f γ)).symm
end

/-! The admissible-order source flux is exactly the forcing indexed by original identities. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem originalCellSource_order_flux (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (p : P) (c : Ctx p) (v u : ι)
    (s δ t : ℝ) (X0 φ z : Vec 2) (U : PlaneHk Set.univ (K u + 1) (h u)) :
    (∑ d : admissibleOrders K D v u,
      slowEvalCoefficient (fun f z => f (X0 + δ • z))
        (F.cellFiber s φ p c v u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
        (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
          planeJetOrder U (d.1 - 1) word z))) =
      ∑ α : OriginalSourceIndex F v u,
        F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + δ • z) (z + φ) α.2.2.2 •
          Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
            (planeJetOrder U (α.2.1.1 - 1) α.2.2.1 z) := by
  classical
  let f := fun (γ : F.Γ v u) (d : ℕ) => ∑ w : DerivativeWord2 (d - 1), ∑ k : Fin 2,
    F.flux p c v u γ d w (s * t) (X0 + δ • z) (z + φ) k •
      Weighted.fluxCoordinateInjection k (F.identity v u γ).map (planeJetOrder U (d - 1) w z)
  have hh := original_order_reindex F K hdesc v u f
  unfold admissibleOrders at hh ⊢
  simp_rw [originalCellFiber_slowFlux_expansion]
  change (∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u,
    if d.1 ≤ (F.identity v u γ).maxOrder then f γ d.1 else 0) = _
  refine hh.trans ?_
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro γ _
  exact (Finset.sum_coe_sort (Finset.Icc 2 (F.identity v u γ).maxOrder) (f γ)).symm
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Original independent prices control scalar mixed jets with arbitrary fast phase. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSource_scalar_mixed_ae_price (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) (α : OriginalSourceIndex F v u)
    (p : P) (c : Ctx p) (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ J) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ φ k X z,
      ‖(F.identity v u α.1).map‖ *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
          (fun y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k) z) X‖ ≤
      analyticOriginalSourcePrice F dom Ks J v u α := by
  filter_upwards [analyticOriginalSource_reserved_jet_ae_bound F π hπ dom Ks J b henv
    v u α p c r q hr hq] with t ht
  intro hdom φ k X z
  have hf := molecular_joint_contDiff F dom 1 one_ne_zero (fun _ => Ks + J)
    henv.1 p c t hdom v u α.1 α.2.1.1 α.2.2.1
  have hbox : IsBoxSmooth r q (F.flux p c v u α.1 α.2.1.1 α.2.2.1 t) :=
    Weighted.isBoxSmooth_of_joint_contDiff r q _ (hf.of_le (by exact_mod_cast (by omega : r + q ≤ Ks + J)))
  have hh := mul_le_mul_of_nonneg_left
    (mixedJet_fast_shift_coordinate_norm_le _ hbox φ k X z) (norm_nonneg (F.identity v u α.1).map)
  have he : F.slowFlux 1 p c v u α.1 α.2.1.1 α.2.2.1 =
      F.flux p c v u α.1 α.2.1.1 α.2.2.1 := by
    funext τ Y y
    simp only [ChartedFamily.slowFlux, inv_one, one_smul]
  have hb := ht X (hdom X) (z + φ)
  rw [he] at hb
  exact hh.trans hb

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The original molecular envelope supplies a graph budget uniform in the family and its masses. -/

def originalSourceGraphConstant (Kmax : ℕ) (C0 : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 * |C0| *
    ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N)

theorem originalSourceGraphConstant_nonneg (Kmax : ℕ) (C0 : ℝ) :
    0 ≤ originalSourceGraphConstant Kmax C0 := by
  unfold originalSourceGraphConstant
  positivity

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalSourcePrice_graph_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (hrow : ∀ v, ∑ u, b v u ≤ 1)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) :
    (∀ v, ∑ u, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α) ≤
        originalSourceGraphConstant Kmax (C 0)) ∧
    (∀ u, ∑ v, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α) ≤
        originalSourceGraphConstant Kmax (C 0)) := by
  classical
  have hv (v : ι) : Real.sqrt (multiplicationDensityBudget (K v)) ≤
      ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N) :=
    Finset.single_le_sum (fun N _ => Real.sqrt_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK v)))
  have hpoint (v u : ι) : Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α) ≤
        originalSourceGraphConstant Kmax (C 0) * b v u := by
    have hh := originalSourcePrice_sum_envelope_le F π K Kmax dom ν e E ρ hν hE hρ
      C J b henv v u (hb v u)
    have hc := mul_le_mul_of_nonneg_left (hv v)
      (by positivity : 0 ≤ 2 * (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 * |C 0|)
    have hc' : 2 * Real.sqrt (multiplicationDensityBudget (K v)) * (4 : ℝ) ^ Kmax *
        (Kmax.factorial : ℝ) ^ 2 * |C 0| ≤ originalSourceGraphConstant Kmax (C 0) := by
      simpa only [originalSourceGraphConstant, mul_assoc, mul_comm, mul_left_comm] using hc
    exact hh.trans (mul_le_mul_of_nonneg_right hc' (hb v u))
  constructor
  · intro v
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hrow v) (originalSourceGraphConstant_nonneg Kmax (C 0)))
  · intro u
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hcol u) (originalSourceGraphConstant_nonneg Kmax (C 0)))

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_polynomial_factorial_energy
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
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (hCell : IsCellMetric G)
    (hconstant : ∀ t x, G t x = G t 0)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (hG1 : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    ∀ t ∈ Icc a b,
      weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t) +
      ENNReal.ofReal (1 / 4 : ℝ) *
        (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (F i s)) := by
  have hh := constantMetric_scalarChain_chart_factorial_energy a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall hreserve hdiv hwa hwb
  have haW : a ∈ Icc t₀ (t₀ + S) := ⟨hwa, hab.trans hwb⟩
  have hC : 0 ≤ Cw m := (by norm_num : (0 : ℝ) ≤ 1).trans
    (chartWeights_constant_ge_one C m hm a haW)
  intro t ht
  have htW : t ∈ Icc t₀ (t₀ + S) := ⟨hwa.trans ht.1, ht.2.trans hwb⟩
  have he := storedChartFactorialEnergy_le_scaled (r / L) (planeMomentPolynomial m ϖ zc)
    (C.W m t) hC (chartWeights_polynomial_le_comparisonWeight C m hm t htW) (u i t)
  have hd := storedChartGradientEnergy_time_le_scaled (r / L)
    (fun _ => planeMomentPolynomial m ϖ zc) (C.W m) (volume.restrict (Icc a b)) hC
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact chartWeights_polynomial_le_comparisonWeight C m hm s ⟨hwa.trans hs.1, hs.2.trans hwb⟩) (w i)
  have hi := storedChartFactorialEnergy_le_scaled (r / L) (C.W m a)
    (planeMomentPolynomial m ϖ zc) hC (fun x => (C.comparable m hm a haW x).2) (f i)
  have hf := storedChartFluxEnergy_time_le_scaled (r / L) (C.W m)
    (fun _ => planeMomentPolynomial m ϖ zc) (volume.restrict (Icc a b)) hC
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact fun x => (C.comparable m hm s ⟨hwa.trans hs.1, hs.2.trans hwb⟩ x).2) (F i)
  have hfinal := quarter_scaled_retained_energy_transfer he hd (hh t ht) hi hf
  simp only [weightedFactorialNormSq_stored_readout, weightedGradFactorialNormSq_stored_readout]
  simpa only [storedChartFluxEnergy_eq_factorial] using hfinal

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Original constituent jet prices give a positive Schur matrix before chronological integration. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def letterRetainedJetMatrix (π : ι → ℝ) (L : CycleLetter ι h D)
    (dom : Set (ℝ × Vec 2)) (J : ℕ) : ι → ι → ℝ := fun v u =>
  Real.sqrt (π u / π v) *
    ∑ α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u,
      analyticOriginalSourcePrice (ChartedFamily.ofFiber L.edge) (fun _ _ => dom) L.slow J v u α

omit [Fintype ι] in
theorem letterRetainedJetMatrix_nonneg (π : ι → ℝ) (L : CycleLetter ι h D)
    (dom : Set (ℝ × Vec 2)) (J : ℕ) (v u : ι) :
    0 ≤ letterRetainedJetMatrix π L dom J v u :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem letterRetainedJetMatrix_entry_le (π : ι → ℝ) (L : CycleLetter ι h D)
    (dom : Set (ℝ × Vec 2)) (J H : ℕ) (hL : IsCycleLetter π L dom J H) (v u : ι) :
    letterRetainedJetMatrix π L dom J v u ≤ 2 * L.majorant v u :=
  analyticOriginalSourcePrice_sum_envelope_le (ChartedFamily.ofFiber L.edge) π (fun _ _ => dom)
    L.slow J L.majorant hL.analytic v u (hL.nonneg v u)

theorem letterRetainedJetMatrix_schur_budget (π : ι → ℝ) (L : CycleLetter ι h D)
    (dom : Set (ℝ × Vec 2)) (J H : ℕ) (hL : IsCycleLetter π L dom J H) :
    (∀ v u, 0 ≤ letterRetainedJetMatrix π L dom J v u) ∧
      (∀ v, ∑ u, letterRetainedJetMatrix π L dom J v u ≤ 2 * L.theta) ∧
      (∀ u, ∑ v, letterRetainedJetMatrix π L dom J v u ≤ 2 * L.theta) := by
  refine ⟨letterRetainedJetMatrix_nonneg π L dom J, ?_, ?_⟩
  · intro v
    have hs : (∑ u, letterRetainedJetMatrix π L dom J v u) ≤ ∑ u, 2 * L.majorant v u :=
      Finset.sum_le_sum (fun u _ => letterRetainedJetMatrix_entry_le π L dom J H hL v u)
    rw [← Finset.mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (hL.row_sum v) (by norm_num))
  · intro u
    have hs : (∑ v, letterRetainedJetMatrix π L dom J v u) ≤ ∑ v, 2 * L.majorant v u :=
      Finset.sum_le_sum (fun v _ => letterRetainedJetMatrix_entry_le π L dom J H hL v u)
    rw [← Finset.mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (hL.col_sum u) (by norm_num))

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Genuine plane H1 time states with the exact reconstructed continuous trace. -/

local instance {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) : AddCommMonoid (Lp E 2 μ) :=
  (inferInstance : NormedAddCommGroup (Lp E 2 μ)).toAddCommMonoid

local instance cellEnergyPlaneH1Add : AddCommMonoid (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : NormedAddCommGroup (PlaneHk Set.univ 1 ℂ)).toAddCommMonoid

local instance cellEnergyPlaneH1Topology : TopologicalSpace (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : PseudoMetricSpace (PlaneHk Set.univ 1 ℂ)).toUniformSpace.toTopologicalSpace

local instance cellEnergyPlaneH1Module : Module ℝ (PlaneHk Set.univ 1 ℂ) :=
  (inferInstance : NormedSpace ℝ (PlaneHk Set.univ 1 ℂ)).toModule

local instance cellEnergyPlaneH1FrequencyModule :
    Module ℝ (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :=
  (inferInstance : NormedSpace ℝ (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)).toModule

def cellEnergyPlaneH1State {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    Lp (PlaneHk Set.univ 1 ℂ) 2 (volume.restrict (Icc a b)) :=
  centeredCellBlochH1Operator.compLp (cellEnergyTimeFrequencyState hab F)

theorem cellEnergyPlaneH1State_value {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      planeHkValueOperator 1 (cellEnergyPlaneH1State hab F t) =
        (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
          ((cellEnergyTraceAtCLM a b (projIcc a b hab t)).compLp F) := by
  have hs := centeredCellBlochH1Operator.coeFn_compLp (cellEnergyTimeFrequencyState hab F)
  filter_upwards [hs, cellEnergyTimeFrequencyState_value hab F] with t hs' ht
  change cellEnergyPlaneH1State hab F t =
    centeredCellBlochH1Reconstruct (cellEnergyTimeFrequencyState hab F t) at hs'
  rw [hs', centeredCellBlochH1Reconstruct_value, centeredCellBlochTorusValue, ht,
    planeCellBlochUnitary_symm_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Actual physical gradient readouts of the reconstructed plane H1 time state. -/

theorem cellEnergyPlaneH1State_gradient {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i : Fin 2,
      univToPlane ((cellEnergyPlaneH1State hab F t).val ⟨⟨1, by decide⟩, fun _ => i⟩) =
        cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i := by
  filter_upwards [centeredCellBlochH1Operator.coeFn_compLp (cellEnergyTimeFrequencyState hab F)]
    with t ht i
  change cellEnergyPlaneH1State hab F t =
    centeredCellBlochH1Operator (cellEnergyTimeFrequencyState hab F t) at ht
  rw [ht, centeredCellBlochH1Operator_apply, centeredCellBlochH1Reconstruct_native_gradient]

end AVRegularity.CycleWords
end
