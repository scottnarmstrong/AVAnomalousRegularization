-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal
public import AVRegularity.Weighted.WeightedZeroCarrier
import AVRegularity.Weighted.PlaneGalerkin.ScalarMetricPlaneExistence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_chart_factorial_energy
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
  have hh := scalarChain_clipped_factorial_ennreal a b hab κ Kmax hκ v hvm hv
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
end

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_polynomial_factorial_energy
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
  have hh := scalarChain_chart_factorial_energy a b hab κ Kmax hκ v hvm hv
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
end

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_polynomial_factorial_supremum
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
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) := by
  have hh := scalarChain_polynomial_factorial_energy a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
  have hs := half_production_supremum_le (Icc a b) b ⟨hab, le_rfl⟩ _ _ _ hh
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρ0 : 0 ≤ r / L := (div_pos hr hLp).le
  have hρr : r / L ≤ r := div_le_self hr.le hL
  have hpower : ENNReal.ofReal (L ^ (2 * κ i.1 i.2)) ≤ ENNReal.ofReal (L ^ (2 * Kmax)) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 (hκ i)))
  let A := ENNReal.ofReal (L ^ (2 * Kmax))
  have he t : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t) ≤
      A * weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t) :=
    (weightedFactorialNormSq_radius_reserve m ϖ zc r L hL _ _).trans
      (mul_le_mul' hpower le_rfl)
  have hd : (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      A * ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro s
    exact (weightedGradFactorialNormSq_radius_reserve m ϖ zc r L hL _ _).trans
      (mul_le_mul' hpower le_rfl)
  have heSup : (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) ≤
      A * (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t)) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (he t).trans (mul_le_mul' le_rfl (le_iSup_of_le t (le_iSup_of_le ht le_rfl)))
  have hi := weightedFactorialNormSq_radius_mono m ϖ zc hρ0 hρr (κ i.1 i.2) (f i)
  have hf : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (F i s)) ≤
      ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s) :=
    lintegral_mono (fun s => weightedFactorialNormSq_radius_mono m ϖ zc hρ0 hρr _ (F i s))
  calc
    _ ≤ A * ((⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t)) +
        ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s)) := by
      simpa only [mul_add] using add_le_add heSup hd
    _ ≤ A * (3 * ((ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
          (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
            16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)))) := by
      apply mul_le_mul' le_rfl
      apply hs.trans
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      exact add_le_add hi (mul_le_mul' le_rfl hf)
    _ = _ := by dsimp [A]; ring
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The weighted a priori estimate uses exactly the coefficient and chart assumptions of
`weighted_energy_plane`. -/

theorem weighted_energy_plane_apriori (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
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
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
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
  apply geometryEnergyNorm_of_component_bounds π Kslot n ϖ zc rstar ta tb
    V₀ F hF V Vw A hA
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

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Existence follows from the committed plane Fourier construction and true metric coercivity. -/

theorem weighted_energy_plane_exists (Kmax : ℕ) (CG : ℕ → ℝ) :
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
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (_hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc ta tb))),
        ∃ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
          (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsPlaneChainFrom (geometryScalarData 2 G) (fun _ x => Kslot x) ta tb v
            (fun _ x => V₀ x) (fun _ x => F x) (fun _ x => V x) (fun _ x => Vw x) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets V₀ F hF
  obtain ⟨L, hL, hreserve⟩ := exists_radius_absorption_reserve 1 (metricRadiusConstant Kmax CG) (by norm_num)
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 1)]
  let ρ := rstar / L
  have hρ : 0 < ρ := div_pos hrstar hLp
  let κ : Fin 1 → ι → ℕ := fun _ i => Kslot i
  have hsm : ∀ t ∈ Set.Icc ta tb, ∀ p : Fin 1 × ι, ∀ k j,
      ContDiff ℝ (κ p.1 p.2 : ℕ) (fun z => G t z k j) := by
    intro t ht' p k j
    exact (hG_smooth t ht' k j).of_le (by exact_mod_cast (hKslot p.2).trans (le_max_left Kmax 1))
  have hm : ∀ t ∈ Set.Icc ta tb, ∀ p : Fin 1 × ι,
      ∀ (l : Fin (κ p.1 p.2 + 1)) z k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) z‖ ≤ metricEntryEnvelope CG g δ l.val := by
    intro t ht' p
    exact metricEntryEnvelope_bound (hKslot p.2) G CG g δ hg hδ hg4 hG_near hG_symm hG_jets t ht'
  have hAf : ∀ p p' d, coefficientSeminorm ρ (κ p.1 p.2) ta tb
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ p p' d) ≠ ⊤ := by
    intro p p' d
    exact scalarChainCoefficient_coefficientSeminorm_ne_top G κ ρ ta tb p p' d
      (fun t ht' => hsm t ht' p) (fun l => metricEntryEnvelope CG g δ l.val)
      (fun l t ht' => hm t ht' p l)
  have hAc : ∀ p p' d, ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (κ p.1 p.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ p p' d t) := by
    intro p p' d t ht'
    exact scalarChainCoefficient_contDiff G κ p p' d t (hsm t ht' p)
  have hAm := scalarChainCoefficient_measurable (h := h) G κ ta tb hG_meas
  have hp : ∀ p : Fin 1 × ι, (metricRadiusConstant (κ p.1 p.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16 := by
    intro p
    have hh := maximalSlot_radius_source_reserve (hKslot p.2) CG (A := 1) (by norm_num)
      hL hreserve hrstar.le hδ hg hg4 hrδ
    have hn : 0 ≤ (1 / L ^ 2) / 2 := by positivity
    dsimp only [ρ, κ]
    simp only [one_mul] at hh
    nlinarith only [hh, hn]
  have hscale : ρ * δ ≤ 1 :=
    (reducedRadius_metric_scale hLp hrδ).trans (div_le_self (by norm_num) hL)
  have hsmall : B₀ * ρ / lam ≤ 1 / 2 :=
    (reducedRadius_drift_scale hlam hLp hB).trans (div_le_self (by norm_num) hL)
  have hstrain : strain * B₀ * ρ ^ 2 ≤ 1 / 8 :=
    (reducedRadius_strain_scale hab).trans (div_le_self (by norm_num) hLsq)
  obtain ⟨Vbound, hvbound⟩ := hv_bdd
  have hbv : ∀ t ∈ Set.Icc ta tb, ∀ z, ‖v t z‖ ≤ max Vbound 0 :=
    fun t ht' z => (hvbound t ht' z).trans (le_max_left _ _)
  obtain ⟨u, w, hs⟩ := PlaneGalerkin.exists_scalarSourcePlaneWeakSolution
    ρ hρ κ ta tb ht G hAf hAc v hv_smooth (max Vbound 0) (le_max_right _ _) hbv
    hsm CG g δ hg hδ hg4 hG_near hscale hm
    (fun t ht' p l hl hle z k j => hG_jets t ht' z l hl (hle.trans (hKslot p.2)) k j)
    hp Kmax (fun p => hKslot p.2) strain B₀ lam ha hB₀ hlam hsmall hstrain
    (fun p => π p.2) (fun p => hπ p.2) hv_div
    (fun t ht' l hl hle z => hjets l hl hle t ht' z)
    (fun p => F p.2) (fun _ _ => 0) (fun p => hF p.2) (fun p => integrable_zero ℝ (PlaneHk Set.univ (κ p.1 p.2) (h p.2))
      (volume.restrict (Set.Icc ta tb)))
    (fun p => V₀ p.2) hv_meas hAm
  refine ⟨fun x => u (0, x), fun x => w (0, x), ?_⟩
  have hu : (fun p : Fin 1 × ι => u (0, p.2)) = u := by
    funext p
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hw : (fun p : Fin 1 × ι => w (0, p.2)) = w := by
    funext p
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  simpa only [IsPlaneChainFrom, hu, hw] using hs

end AVRegularity.Weighted
end
