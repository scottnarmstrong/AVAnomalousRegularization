-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstantMetricScalarComponentFinite
import AVRegularity.CycleWords.ConstantMetricClippedFactorialENNReal
import AVRegularity.CycleDamping.ReferenceTimeEquation
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.FibreCoefficientGraphRawDual
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalRemainderConstituent_native_flux_exists_uniform (Ks Kmax : ℕ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks + 1 ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => (F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ) k -
            taylorSlow 0 Ks (fun X => F.flux p c v u γ d I (s * t) X (z + φ) k) X0 ((e / E) • z)) • Weighted.fluxCoordinateInjection k (F.identity v u γ).map
              (planeJetOrder (U t) (d - 1) I z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
            (CR * molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1) * ζ ^ (Ks + 1) *
                ‖(F.identity v u γ).map‖) ^ 2 *
                  (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CR, hCR, hcoeff⟩ := familyMolecular_remainder_coefficient_uniform Ks Kmax
  refine ⟨CR, hCR, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ k hwindow n U hU henergy
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdmax := (Finset.mem_Icc.mp hd).2
  have hdu := hdesc v u γ
  have hKL : K v + (d - 1) ≤ K u + 1 := by omega
  have hr : 1 ≤ d - 1 := by omega
  let cc := slowRemainderTimeCoefficient Ks
    (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
  let B := CR * molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1) * ζ ^ (Ks + 1)
  let T := Weighted.fluxCoordinateInjection k (F.identity v u γ).map
  have hB : 0 ≤ B := by
    apply mul_nonneg _ (pow_nonneg hζ _)
    apply mul_nonneg hCR
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  obtain ⟨hcm, hc, hb⟩ := hcoeff F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ k hwindow
  have hb' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
        B / derivativeReserveFactor (ρ / e) (K v) ((d - 1) - 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
    filter_upwards [hb] with t ht
    intro j hj z
    have heq : B / derivativeReserveFactor (ρ / e) (K v) ((d - 1) - 1) =
        CR * molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1) /
          derivativeReserveFactor (ρ / e) (K v) (d - 2) * ζ ^ (Ks + 1) := by
      rw [show (d - 1) - 1 = d - 2 by omega]
      dsimp [B]
      ring
    rw [heq]
    exact ht j hj z
  obtain ⟨V, hV, hVe, hv, hdensity⟩ := reserved_scalar_native_flux_exists hKL hr I n (Ks + 1) ϖ (ρ / e)
    hϖ (div_pos hρ he) cc hcm hc T B hB (volume.restrict (Set.Icc a b)) hb' U hU henergy
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
    simpa only [cc, slowRemainderTimeCoefficient, ite_eq_left htI, T] using ht
  · filter_upwards [hdensity] with t ht
    filter_upwards [ht] with z hz
    have hcost := mul_le_mul_of_nonneg_left (fluxCoordinateInjection_norm_le k (F.identity v u γ).map) hB
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hB (norm_nonneg T)) hcost 2)
          (multiplicationDensityBudget_nonneg (K v))) (sq_nonneg (polynomialMomentRoot ϖ z ^ (Ks + 1))))
      (planeGradFactorialDensity_nonneg (ρ / e) (U t) z)
    exact hz.trans hn

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_chart_factorial_lower_energy
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
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    ∀ t ∈ Icc a b,
      storedChartFactorialEnergy (r / L) (C.W m t) (u i t) +
      ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (C.W m s) (w i s)) ≤
      ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (storedChartFactorialEnergy (r / L) (C.W m a) (f i) +
          16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (C.W m s) (F i s)) := by
  intro t ht
  have he := storedChartFactorialEnergy_clipping_tendsto (r / L)
    (C.W m t) (C.pos m hm t)
    (fun n => (chartWeights_clipped_continuous C m hm t ((n : ℝ) + 1) (by positivity)).measurable) (u i t)
  have hd := storedChartGradientEnergy_time_clipping_tendsto (r / L) C m hm
    (volume.restrict (Icc a b)) (w i) (hsln.2.1 i)
  have hdh := ENNReal.Tendsto.const_mul hd
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤))
  apply le_of_tendsto (he.add hdh)
  apply Eventually.of_forall
  intro n
  have hh := scalarChain_clipped_factorial_lower_ennreal a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm ((n : ℝ) + 1) r L (by positivity) hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
  dsimp only at hh
  apply (hh t ht).trans
  apply mul_le_mul' le_rfl
  apply add_le_add
  · exact storedChartFactorialEnergy_mono (r / L) _ _
      (fun x => clipWeight_le_value (by positivity) (C.pos m hm a x)) (f i)
  · apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro s
    exact storedChartFluxEnergy_mono (r / L) _ _
      (fun x => clipWeight_le_value (by positivity) (C.pos m hm s x)) (F i s)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Continuity of the actual real order-zero plane trace. -/

theorem cellEnergyPlaneRealTrace_continuous {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    Continuous (cellEnergyPlaneRealTrace hab F) := by
  exact planeL2ZeroCarrier.continuous.comp
    (planeComplexRealPartL2.continuous.comp
      ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm.continuous.comp
        ((cellEnergyTraceLp_continuous centeredPlaneFrequencyMeasure a b F).comp
          continuous_projIcc)))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy for the full constructed cell generator, with a quadratic contrast price. -/

theorem real_inner_transport_young {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v u : H) (A B : ℝ)
    (hv : ‖v‖ ≤ A * B) :
    2 * |inner ℝ v u| ≤ (1 / 4) * B ^ 2 + 4 * A ^ 2 * ‖u‖ ^ 2 := by
  have hi := (abs_real_inner_le_norm v u).trans
    (mul_le_mul_of_nonneg_right hv (norm_nonneg u))
  have hs := sq_nonneg (B / 2 - 2 * A * ‖u‖)
  nlinarith

def constructedHigherEnergyGrowth (K : ℕ) (R η k : ℝ) : ℝ :=
  528 * R ^ 2 + 1 / 4 +
    4 * (constructedAdvectionAdjacentPrice K R * peFactor η) ^ 2 +
    2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)

theorem constructedHigherFullGenerator_smooth_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) :
    2 * inner ℝ
        (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      constructedHigherEnergyGrowth K R (ν / ocMeanFlux α q Λ ζ m ν) k *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let U := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let W := finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let B := ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖
  let A := constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)
  have ha := constructedHigherAdvectionCLM_adjacent_polynomial_bound K hΛ hζ hν hr y₀ hv θ R hθ t W
  rw [finiteSmoothPeriodicHk_truncate (K := K + 1) (L := K + 2) (by omega) f hf hp] at ha
  have hy := real_inner_transport_young
    (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t W) U A B ha
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
  have hat := neg_le_abs (inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t W) U)
  have hct := le_abs_self (inner ℝ (torusHigherScalarCLM K (κ t) U) U)
  simp only [constructedHigherFullGeneratorCLM, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left]
  rw [finiteSmoothPeriodicHk_truncate (K := K) (L := K + 2) (by omega) f hf hp]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤ _
  change 2 * inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U + _ ≤ _ at hd
  change B ^ 2 ≤ ‖U‖ ^ 2 + _ at hb
  unfold constructedHigherEnergyGrowth
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K G θ t W) U -
    inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤
    (528 * R ^ 2 + 1 / 4 + 4 * A ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2
  nlinarith

/-! The full higher energy growth is bounded by a universal order price times the squared contrast. -/

def constructedHigherEnergyOrderPrice (K : ℕ) (R k : ℝ) : ℝ :=
  528 * R ^ 2 + 1 / 4 + 4 * (constructedAdvectionAdjacentPrice K R) ^ 2 +
    2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)

theorem constructedHigherEnergyOrderPrice_nonneg (K : ℕ) (R k : ℝ) (hk : 0 ≤ k) :
    0 ≤ constructedHigherEnergyOrderPrice K R k := by
  unfold constructedHigherEnergyOrderPrice
  positivity

theorem constructedHigherEnergyGrowth_polynomial_bound (K : ℕ) (R η k : ℝ) (hk : 0 ≤ k) :
    constructedHigherEnergyGrowth K R η k ≤
      constructedHigherEnergyOrderPrice K R k * peFactor η ^ 2 := by
  have hp : 1 ≤ peFactor η := by
    unfold peFactor
    have h := inv_nonneg.mpr (Real.sqrt_nonneg η)
    linarith
  have hp2 : 1 ≤ peFactor η ^ 2 := by nlinarith
  have hc : 0 ≤ 528 * R ^ 2 + 1 / 4 +
      2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖) := by positivity
  have he := mul_le_mul_of_nonneg_left hp2 hc
  unfold constructedHigherEnergyGrowth constructedHigherEnergyOrderPrice
  nlinarith only [he]

 theorem constructedHigherFullGenerator_smooth_adjacent_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ
        (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have he := constructedHigherFullGenerator_smooth_energy K hΛ hζ hν hr y₀ hv G hG θ R hθ κ t k hk f hf hp
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
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A positive original Taylor letter retains its geometric gain in every reserved fast jet. -/

section
def originalPositiveTaylorFastJetPriceConstant (Ks J : ℕ) : ℝ :=
  Classical.choose (positiveSlowTaylor_sample_jet_budget Ks J (fun _ => 1))

theorem originalPositiveTaylorFastJetPriceConstant_spec (Ks J : ℕ) :
    0 ≤ originalPositiveTaylorFastJetPriceConstant Ks J ∧
      ∀ (f : Vec 2 → Vec 2 → ℝ), IsBoxSmooth Ks J f →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ B → δ = ζ * ϖ →
      (∀ r ≤ Ks, ∀ j ≤ J, ∀ X z, ρ ^ j *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ ≤ B) →
      ∀ X j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => taylorSlow 1 Ks (fun X' => f X' z) X (δ • z)) z‖ ≤
          originalPositiveTaylorFastJetPriceConstant Ks J * B * ζ * polynomialMomentRoot ϖ z ^ Ks := by
  simpa only [originalPositiveTaylorFastJetPriceConstant, one_mul] using Classical.choose_spec (positiveSlowTaylor_sample_jet_budget Ks J (fun _ => 1))

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSource_positive_taylor_fast_price (Ks J : ℕ) :
    let C := originalPositiveTaylorFastJetPriceConstant Ks J
    0 ≤ C ∧ ∀ (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ),
      (∀ i, 0 < π i) → ∀ (dom : F.Domain) (b : ι → ι → ℝ),
      IsAnalyticEnvelope F π dom 1 1 Ks J b → ∀ (v u : ι)
      (α : OriginalSourceIndex F v u) (p : P) (c : Ctx p)
      (ϖ ζ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 →
      ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ φ k X j, j ≤ J → ∀ z,
        ‖(F.identity v u α.1).map‖ *
          ‖iteratedFDeriv ℝ j (fun y => taylorSlow 1 Ks
            (fun Y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k) X
              ((ζ * ϖ) • y)) z‖ ≤
        C * analyticOriginalSourcePrice F dom Ks J v u α * ζ * polynomialMomentRoot ϖ z ^ Ks := by
  let C := originalPositiveTaylorFastJetPriceConstant Ks J
  have hC : 0 ≤ C := (originalPositiveTaylorFastJetPriceConstant_spec Ks J).1
  have hbound := (originalPositiveTaylorFastJetPriceConstant_spec Ks J).2
  refine ⟨hC, ?_⟩
  intro F π hπ dom b henv v u α p c ϖ ζ hϖ hϖ1 hζ hζ1
  have hj (rq : Fin (Ks + 1) × Fin (J + 1)) :=
    analyticOriginalSource_scalar_mixed_ae_price F π hπ dom Ks J b henv v u α p c
      rq.1.val rq.2.val (Nat.le_of_lt_succ rq.1.isLt) (Nat.le_of_lt_succ rq.2.isLt)
  filter_upwards [ae_all_iff.mpr hj] with t ht
  intro hdom φ k X j hjJ z
  let A := ‖(F.identity v u α.1).map‖
  let B := analyticOriginalSourcePrice F dom Ks J v u α
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  by_cases hA : A = 0
  · change A * _ ≤ C * B * ζ * _
    rw [hA, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hB) hζ)
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) Ks)
  have hAp : 0 < A := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
  let f := fun Y y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k
  have hf : IsBoxSmooth Ks J f :=
    Weighted.isBoxSmooth_of_joint_contDiff Ks J _
      (molecular_cell_coefficient_contDiff F dom 1 one_ne_zero (fun _ => Ks + J)
        henv.1 p c t hdom v u α.1 α.2.1.1 α.2.2.1 φ k)
  have hjet : ∀ r ≤ Ks, ∀ q ≤ J, ∀ Y y,
      (1 : ℝ) ^ q * ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f Y') y) Y‖ ≤
        (B / A) := by
    intro r hr q hq Y y
    simp only [one_pow, one_mul]
    apply (le_div_iff₀ hAp).mpr
    simpa only [mul_comm] using ht (⟨r, Nat.lt_succ_of_le hr⟩, ⟨q, Nat.lt_succ_of_le hq⟩)
      hdom φ k Y y
  have hh := hbound f hf ϖ 1 (ζ * ϖ) ζ (B / A) hϖ zero_le_one
    (by simpa only [one_mul] using hϖ1) hζ hζ1 (div_nonneg hB hAp.le) rfl hjet X j hjJ z
  simp only [one_pow, one_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh hAp.le
  change A * _ ≤ C * B * ζ * _
  convert hm using 1
  dsimp only [C]
  field_simp
end

/-! A original Taylor letter has a moment budget in every reserved fast jet. -/

section
def originalTaylorFastJetPriceConstant (lo Ks J : ℕ) : ℝ :=
  Classical.choose (slowTaylor_sample_jet_budget lo Ks J (fun _ => 1))

theorem originalTaylorFastJetPriceConstant_spec (lo Ks J : ℕ) :
    0 ≤ originalTaylorFastJetPriceConstant lo Ks J ∧
      ∀ (f : Vec 2 → Vec 2 → ℝ), IsBoxSmooth Ks J f →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → ζ ≤ 1 → 0 ≤ B → δ = ζ * ϖ →
      (∀ r ≤ Ks, ∀ j ≤ J, ∀ X z, ρ ^ j *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ ≤ B) →
      ∀ X j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => taylorSlow lo Ks (fun X' => f X' z) X (δ • z)) z‖ ≤
          originalTaylorFastJetPriceConstant lo Ks J * B * polynomialMomentRoot ϖ z ^ Ks := by
  simpa only [originalTaylorFastJetPriceConstant, one_mul] using Classical.choose_spec (slowTaylor_sample_jet_budget lo Ks J (fun _ => 1))

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSource_taylor_fast_price (lo Ks J : ℕ) :
    let C := originalTaylorFastJetPriceConstant lo Ks J
    0 ≤ C ∧ ∀ (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ),
      (∀ i, 0 < π i) → ∀ (dom : F.Domain) (b : ι → ι → ℝ),
      IsAnalyticEnvelope F π dom 1 1 Ks J b → ∀ (v u : ι)
      (α : OriginalSourceIndex F v u) (p : P) (c : Ctx p)
      (ϖ ζ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 →
      ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ φ k X j, j ≤ J → ∀ z,
        ‖(F.identity v u α.1).map‖ *
          ‖iteratedFDeriv ℝ j (fun y => taylorSlow lo Ks
            (fun Y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k) X
              ((ζ * ϖ) • y)) z‖ ≤
        C * analyticOriginalSourcePrice F dom Ks J v u α * polynomialMomentRoot ϖ z ^ Ks := by
  let C := originalTaylorFastJetPriceConstant lo Ks J
  have hC : 0 ≤ C := (originalTaylorFastJetPriceConstant_spec lo Ks J).1
  have hbound := (originalTaylorFastJetPriceConstant_spec lo Ks J).2
  refine ⟨hC, ?_⟩
  intro F π hπ dom b henv v u α p c ϖ ζ hϖ hϖ1 hζ hζ1
  have hj (rq : Fin (Ks + 1) × Fin (J + 1)) :=
    analyticOriginalSource_scalar_mixed_ae_price F π hπ dom Ks J b henv v u α p c
      rq.1.val rq.2.val (Nat.le_of_lt_succ rq.1.isLt) (Nat.le_of_lt_succ rq.2.isLt)
  filter_upwards [ae_all_iff.mpr hj] with t ht
  intro hdom φ k X j hjJ z
  let A := ‖(F.identity v u α.1).map‖
  let B := analyticOriginalSourcePrice F dom Ks J v u α
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  by_cases hA : A = 0
  · change A * _ ≤ C * B * _
    rw [hA, zero_mul]
    exact mul_nonneg (mul_nonneg hC hB)
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) Ks)
  have hAp : 0 < A := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
  let f := fun Y y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k
  have hf : IsBoxSmooth Ks J f :=
    Weighted.isBoxSmooth_of_joint_contDiff Ks J _
      (molecular_cell_coefficient_contDiff F dom 1 one_ne_zero (fun _ => Ks + J)
        henv.1 p c t hdom v u α.1 α.2.1.1 α.2.2.1 φ k)
  have hjet : ∀ r ≤ Ks, ∀ q ≤ J, ∀ Y y,
      (1 : ℝ) ^ q * ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f Y') y) Y‖ ≤
        (B / A) := by
    intro r hr q hq Y y
    simp only [one_pow, one_mul]
    apply (le_div_iff₀ hAp).mpr
    simpa only [mul_comm] using ht (⟨r, Nat.lt_succ_of_le hr⟩, ⟨q, Nat.lt_succ_of_le hq⟩)
      hdom φ k Y y
  have hh := hbound f hf ϖ 1 (ζ * ϖ) ζ (B / A) hϖ zero_le_one
    (by simpa only [one_mul] using hϖ1) hζ hζ1 (div_nonneg hB hAp.le) rfl hjet X j hjJ z
  simp only [one_pow, one_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh hAp.le
  change A * _ ≤ C * B * _
  convert hm using 1
  dsimp only [C]
  field_simp
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalRemainderConstituent_native_flux_exists_all_uniform (Ks Kmax : ℕ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks + 1 ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), ∀ d,
      d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder →
      ∀ (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2) (k : Fin 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => (F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ) k -
            taylorSlow 0 Ks (fun X => F.flux p c v u γ d I (s * t) X (z + φ) k) X0 ((e / E) • z)) • Weighted.fluxCoordinateInjection k (F.identity v u γ).map
              (planeJetOrder (U t) (d - 1) I z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
            (CR * molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I (Ks + 1) * ζ ^ (Ks + 1) *
                ‖(F.identity v u γ).map‖) ^ 2 *
                  (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CR, hCR, hflux⟩ := originalRemainderConstituent_native_flux_exists_uniform Ks Kmax
  refine ⟨CR, hCR, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ k hwindow n U hU henergy
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
      v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hδ X0 φ k hwindow n U hU henergy

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The literal integral phase times the supplied graph is a genuine homogeneous cell evolution. -/

theorem fibreScalarData_symbol_memLp_top
    (K : ScalarConstants) (η t₀ S : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) (a b : ℝ) :
    MemLp (fibreSeriesC data.lam ξ) ⊤ (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound
    ((CycleDamping.graph_symbol_aestronglyMeasurable hG hv data.graph ξ hξ).mono_measure
      Measure.restrict_le_self) ((8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2)
  exact Filter.Eventually.of_forall (fun t =>
    scalarPackageSymbol_quadratic_bound data hη0 hη hCg hCw hG hv hw ξ hξ t)

theorem fibreScalarData_graph_homogeneous_evolution
    (K : ScalarConstants) (η t₀ S : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) {a b : ℝ} (hab : a ≤ b) :
    let phase := fun t => Complex.exp (∫ r in a..t, fibreSeriesC data.lam ξ r)
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (phase t) (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1))
      (fun t => cellH1Scalar (phase t) (cellH1Slice (fibreSeriesJet data.r ξ) t + cellH1One))
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
        hG V hv.1 hb t
        (cellH1Scalar (phase t) (cellH1Slice (fibreSeriesJet data.r ξ) t + cellH1One)) 0 0) := by
  have hh := fibreScalarData_graph_weak_evolution K η t₀ S hη0 hη hCw G hG v hv hm hw data
    V hb ξ hξ hab
  have hl := fibreScalarData_symbol_memLp_top K η t₀ S hη0 hη hCg hCw G hG v hv hw data ξ hξ a b
  exact hh.remove_potential hab (fun t _ => G t) hG v V hv.1 hb _ _ hl

end AVRegularity.CycleWords
end

section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The original metric part of the scalar symbol is integrable on every finite time interval. -/

theorem fibreMetricSymbol_intervalIntegrable (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (ξ : Fin 2 → ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t => -(η : ℂ) * fibreQuad (G t) ξ) volume a b := by
  have hm : Measurable (fun t => -(η : ℂ) * fibreQuad (G t) ξ) :=
    measurable_const.mul (fibreQuad_time_measurable hG ξ)
  have hb (t : ℝ) : ‖-(η : ℂ) * fibreQuad (G t) ξ‖ ≤ |η| * (8 * fibreNorm ξ ^ 2) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (fibreQuad_norm_le_eight (G t) (fun i j => cellMetric_entry_bound hG t 0 i j) ξ)
      (abs_nonneg η)
  apply intervalIntegrable_iff.mpr
  have hp : MemLp (fun t => -(η : ℂ) * fibreQuad (G t) ξ) ⊤
      (volume.restrict (uIoc a b)) :=
    memLp_top_of_bound hm.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  let finiteQuietMetricTimeMeasure : IsFiniteMeasure (volume.restrict (uIoc a b)) := ⟨by
    simp only [Measure.restrict_apply_univ, uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  exact hp.integrable (by simp)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A native realization of one response source gives a scalar equation for that component alone. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryResponse_scalar_component_redistribution (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (a b s δ : ℝ) (X0 phase : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (Mv MG : ℝ) (hMv : 0 ≤ Mv) (hMG : 0 ≤ MG)
    (hvc : ∀ t ∈ Set.Icc a b, ∀ k, Continuous (fun x => v t x k))
    (hvb : ∀ t ∈ Set.Icc a b, ∀ k x, |v t x k| ≤ Mv)
    (hGb : ∀ t ∈ Set.Icc a b, ∀ k j, |G t 0 k j| ≤ MG)
    (f : ∀ (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v f (fun _ _ _ => 0) U Uw)
    (j : Fin (J + 1)) (x : ι)
    (V : ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hV : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
      (fun z => (∑ u, ∑ α : OriginalSourceIndex F x u,
        taylorSlow 0 Ks (fun X => F.flux p c x u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + phase) α.2.2.2)
          X0 (δ • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity x u α.1).map
            (planeJetOrder (Uw j u t) (α.2.1.1 - 1) α.2.2.1 z)) +
        ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
          WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l •
            (Uw j' x t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) else 0)) :
    IsPlaneChainFrom (h := fun _ : Unit => h x) (geometryScalarData D (fun t _ => G t 0))
      (fun _ _ => K x) a b v (fun _ _ => f j x) (fun _ _ => V)
      (fun _ _ => U j x) (fun _ _ => Uw j x) := by
  refine ⟨(fun _ => hsol.1 (j, x)), (fun _ => hsol.2.1 (j, x)),
    (fun _ => hsol.2.2.1 (j, x)), (fun _ => hsol.2.2.2.1 (j, x)), ?_⟩
  intro i t ht ψ
  rcases i with ⟨j0, u⟩
  cases u
  have hj := Fin.eq_zero j0
  subst j0
  have hs := hsol.2.2.2.2 (j, x) t ht ψ
  simp only [Measure.restrict_univ] at hs ⊢
  let du := fun r k => (Uw j x r).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩
  let fzero := fun _ : ℝ => (0 : PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x))).toFunction.jet (valueIndex2 (K x))
  let fnew := fun r => (V r).toFunction.jet (valueIndex2 (K x))
  let gzero := fun _ : ℝ => (0 : PlaneHk Set.univ (K x) (h x)).toFunction.jet (valueIndex2 (K x))
  let A := fun r => geometryResponseRawFlux J Ks K G (F.cellFiber s phase p c) X0 δ
    (fun j u => Uw j u r) j x r
  let A' := fun r => geometryScalarFlux D (h := fun _ : Unit => h x) (fun t _ => G t 0) (fun _ _ => K x)
    (fun _ => Uw j x r) (0, ()) r
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ du A fzero gzero at hs
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ du A' fnew gzero
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  apply coupledWeakIdentity_flux_ae_time_congr volume 1 a t v _ _ _ _ du A fzero A' fnew gzero hs
  · have hv := ae_restrict_of_ae_restrict_of_subset hsub hV
    filter_upwards [hv] with r hr
    have hz := planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x)
    rw [planeValue_eq_stored] at hr hz
    filter_upwards [hr, hz] with z hrz hzz
    change A r z + fzero r z = A' r z + fnew r z
    dsimp only [A, A', fzero, fnew]
    rw [geometryResponseRawFlux_eq_ordered]
    have he := geometryResponseOrderedFlux_split F hD J Ks K hdesc p c G s δ X0 phase
      (fun j u => Uw j u r) j x r z
    have hscalar : geometryScalarFlux D (fun t _ => G t 0) (fun _ u => K u)
        (fun q => Uw j q.2 r) (0, x) r z = A' r z := by
      dsimp only [A']
      apply PiLp.ext
      intro k
      rw [geometryScalarFlux_eq D hD, geometryScalarFlux_eq D hD]
    rw [he, hscalar, add_assoc]
    change (0 : PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x))).toFunction.jet
      (valueIndex2 (K x)) z = 0 at hzz
    change (V r).toFunction.jet (valueIndex2 (K x)) z = _ at hrz
    rw [hzz, add_zero, hrz]
    exact add_assoc _ _ _
  · intro r hr
    have hrI := hsub hr
    have hi := planeScalarRawRhs_integrable (K x) (v r) (hvc r hrI) hMv (hvb r hrI)
      (fun _ => G r 0) (fun _ _ => continuous_const) hMG (fun k l _ => hGb r hrI k l) (Uw j x r) (V r) ψ
    unfold Weighted.planeScalarRawRhs at hi
    simpa only [du, A', fnew, gzero, geometryScalarFlux_eq D hD, one_mul] using hi

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_polynomial_factorial_lower_energy
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
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    ∀ t ∈ Icc a b,
      weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t) +
      ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (F i s)) := by
  have hh := scalarChain_chart_factorial_lower_energy a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
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
  have hfinal := scaled_retained_energy_transfer he hd (hh t ht) hi hf
  simp only [weightedFactorialNormSq_stored_readout, weightedGradFactorialNormSq_stored_readout]
  simpa only [storedChartFluxEnergy_eq_factorial] using hfinal

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact scalar-symbol differences when canonical graphs consume a common drift slice. -/

theorem cellBlochDriftMeanCLM_congr_at_time (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (hvw : v t = w t) :
    cellBlochDriftMeanCLM η Cw hCw hv hsv ξ t =
      cellBlochDriftMeanCLM η Cw hCw hw hsw ξ t := by
  ext u
  rw [cellBlochDriftMeanCLM_apply, cellBlochDriftMeanCLM_apply]
  unfold fibreDriftCoupling
  rw [hvw]

theorem canonicalGraph_symbol_difference_at_common_drift (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (t : ℝ) (hvw : v t = w t) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hsv
    let s := fibreCoefficientFamily η Cw hη G hG hw hsw
    fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t -
      fibreSeriesC (fibreCoefficientSymbol η G w s) ξ t =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hsv ξ t
        (cellRawTrace (fibreSeriesJet r ξ) t - cellRawTrace (fibreSeriesJet s ξ) t) := by
  dsimp only
  rw [fibreCoefficientFamily_symbol_class η Cw hη hCw G hG hv hsv ξ hξ t,
    fibreCoefficientFamily_symbol_class η Cw hη hCw G hG hw hsw ξ hξ t,
    ← cellBlochDriftMeanCLM_congr_at_time η Cw hCw v w hv hw hsv hsw ξ t hvw, map_sub]
  ring

theorem canonicalGraph_symbol_difference_norm_at_common_drift (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (t : ℝ) (hvw : v t = w t) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hsv
    let s := fibreCoefficientFamily η Cw hη G hG hw hsw
    ‖fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t -
      fibreSeriesC (fibreCoefficientSymbol η G w s) ξ t‖ ≤
      Cw * fibreNorm ξ *
        ‖cellRawTrace (fibreSeriesJet r ξ) t - cellRawTrace (fibreSeriesJet s ξ) t‖ := by
  dsimp only
  rw [canonicalGraph_symbol_difference_at_common_drift η Cw hη hCw G hG
    v w hv hw hsv hsw ξ hξ t hvw]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact cellBlochDriftMeanCLM_norm_le η Cw hCw hv hsv ξ t _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual positive flag supplies the correct Taylor lower degree and geometric price. -/

def originalFlaggedTaylorFastJetPriceConstant (pos : Bool) (Ks J : ℕ) : ℝ :=
  if pos then originalPositiveTaylorFastJetPriceConstant Ks J
  else originalTaylorFastJetPriceConstant 0 Ks J

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticOriginalSource_flagged_taylor_fast_price (pos : Bool) (Ks J : ℕ) :
    let C := originalFlaggedTaylorFastJetPriceConstant pos Ks J
    0 ≤ C ∧ ∀ (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ),
      (∀ i, 0 < π i) → ∀ (dom : F.Domain) (b : ι → ι → ℝ),
      IsAnalyticEnvelope F π dom 1 1 Ks J b → ∀ (v u : ι)
      (α : OriginalSourceIndex F v u) (p : P) (c : Ctx p)
      (ϖ ζ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 →
      ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ φ k X j, j ≤ J → ∀ z,
        ‖(F.identity v u α.1).map‖ *
          ‖iteratedFDeriv ℝ j (fun y => taylorSlow (if pos then 1 else 0) Ks
            (fun Y => F.flux p c v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) k) X
              ((ζ * ϖ) • y)) z‖ ≤
        C * analyticOriginalSourcePrice F dom Ks J v u α * (if pos then ζ else 1) *
          polynomialMomentRoot ϖ z ^ Ks := by
  cases pos
  · simpa only [originalFlaggedTaylorFastJetPriceConstant, Bool.false_eq_true, ↓reduceIte, mul_one] using
      (analyticOriginalSource_taylor_fast_price (ι := ι) (h := h) (D := D) (P := P) (Ctx := Ctx) 0 Ks J)
  · simpa only [originalFlaggedTaylorFastJetPriceConstant, ↓reduceIte] using
      (analyticOriginalSource_positive_taylor_fast_price (ι := ι) (h := h) (D := D) (P := P) (Ctx := Ctx) Ks J)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The remainder insertion uses its original molecular price at slow order K+1. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def originalRemainderPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (j Kmax : ℕ)
    (dom : F.Domain) (ν e E ρ CR : ℝ) (v u : ι) (α : OriginalSourceIndex F v u) : ℝ :=
  Real.sqrt (multiplicationDensityBudget (K v)) * CR *
    molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u α.1 α.2.1.1 α.2.2.1 j *
      ‖(F.identity v u α.1).map‖

theorem originalRemainderPrice_nonneg (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (j Kmax : ℕ) (dom : F.Domain) (ν e E ρ CR : ℝ)
    (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCR : 0 ≤ CR)
    (v u : ι) (α : OriginalSourceIndex F v u) :
    0 ≤ originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α := by
  unfold originalRemainderPrice molecularTaylorPrefixPrice
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCR)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE _))
      (molecularRealPrice_nonneg ν ρ hν hρ _ _ _))) (norm_nonneg _)

theorem originalRemainderPrice_sum_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (j Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ CR : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ) (hCR : 0 ≤ CR)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hj : j ≤ J)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b) (v u : ι) (hb : 0 ≤ b v u) :
    Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α) ≤
        (2 * Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2 * |C j|) * b v u := by
  classical
  let q := fun (γ : F.Γ v u) d (I : DerivativeWord2 (d - 1)) =>
    E ^ j * molecularRealPrice ν ρ (K v) (d - 2)
      (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  have hp (α : OriginalSourceIndex F v u) :
      originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α =
        (Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2) *
          q α.1 α.2.1.1 α.2.2.1 * ‖(F.identity v u α.1).map‖ := by
    unfold originalRemainderPrice molecularTaylorPrefixPrice
    dsimp only [q]
    ring
  simp_rw [hp]
  rw [originalConstituent_price_sum_eq]
  have hh := molecularRealEnvelope_scaled_sum_le F π K dom ν e E ρ hν hE hρ C J b henv v u hb j hj
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 2 * Real.sqrt (multiplicationDensityBudget (K v)) * CR * (Kmax.factorial : ℝ) ^ 2)
  convert hm using 1 <;> ring

end AVRegularity.CycleWords
end
