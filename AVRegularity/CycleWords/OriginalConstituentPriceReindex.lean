-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstantMetricClippedFactorialENNReal
public import AVRegularity.CycleWords.DerivativeSourceDensity
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Concrete coefficient inputs for applying the weighted plane estimate. -/

structure ScalarCoefficientInputs (K : ℕ) (CG : ℕ → ℝ) (ta tb r δ : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (a B lam : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) : Prop where
  time : ta ≤ tb
  radius : 0 < r
  delta : 0 ≤ δ
  scale : r * δ ≤ 1
  drift_bounded : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C
  drift_measurable : Measurable (fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
  drift_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t)
  drift_divergence : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0
  strain : 0 ≤ a
  drift_constant : 1 ≤ B
  drift_length : 0 < lam
  drift_jets : ∀ l, 1 ≤ l → l ≤ K → ∀ t ∈ Set.Icc ta tb, ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B * r / lam ≤ 1 / 2
  drift_small : a * B * r ^ 2 ≤ 1 / 8
  metric_size : 0 ≤ g
  metric_small : g ≤ 1 / 4
  metric_measurable : Measurable (fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
  metric_symmetric : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm
  metric_near : IsMetricNearIdentity G g
  metric_smooth : ∀ t ∈ Set.Icc ta tb, ∀ i j,
    ContDiff ℝ (max K 1 : ℕ) (fun z => G t z i j)
  metric_jets : ∀ t ∈ Set.Icc ta tb, ∀ z l, 1 ≤ l → l ≤ K → ∀ i j,
    ‖iteratedFDeriv ℝ l (fun y => G t y i j) z‖ ≤ CG l * g * δ ^ l

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

theorem constantMetric_scalarChain_chart_factorial_energy
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
      storedChartFactorialEnergy (r / L) (C.W m t) (u i t) +
      ENNReal.ofReal (1 / 4 : ℝ) *
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
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (1 / 4 : ℝ) ≠ ⊤))
  apply le_of_tendsto (he.add hdh)
  apply Eventually.of_forall
  intro n
  have hh := constantMetric_scalarChain_clipped_factorial_ennreal a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm ((n : ℝ) + 1) r L (by positivity) hr hL
    hsmall hstrainSmall hreserve hdiv hwa hwb
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
open Homogenization
namespace AVRegularity.CycleWords

/-! Enlarging metric jet constants preserves the scalar coefficient inputs. -/

theorem ScalarCoefficientInputs.metric_mono {K : ℕ} {CG CH : ℕ → ℝ}
    {a b ρ δ strain B lam g : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (HC : ScalarCoefficientInputs K CG a b ρ δ v strain B lam G g)
    (hC : ∀ r, CG r ≤ CH r) : ScalarCoefficientInputs K CH a b ρ δ v strain B lam G g := by
  refine { HC with metric_jets := ?_ }
  intro t ht z r hr hK k l
  exact (HC.metric_jets t ht z r hr hK k l).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC r) HC.metric_size) (pow_nonneg HC.delta r))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Spatial continuity and bounded entries supplied by the scalar coefficient inputs. -/

theorem scalarCoefficientInputs_spatial_bounds {K : ℕ} {CG : ℕ → ℝ}
    {a b r δ A B lam g : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (H : ScalarCoefficientInputs K CG a b r δ v A B lam G g) :
    ∃ Mv : ℝ, 0 ≤ Mv ∧
      (∀ t ∈ Set.Icc a b, ∀ k, Continuous (fun x => v t x k)) ∧
      (∀ t ∈ Set.Icc a b, ∀ k x, |v t x k| ≤ Mv) ∧
      (∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun x => G t x k j)) ∧
      (∀ t ∈ Set.Icc a b, ∀ k j x, |G t x k j| ≤ 5 / 4) := by
  obtain ⟨M, hM⟩ := H.drift_bounded
  refine ⟨max M 0, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro t ht k
    exact (continuous_apply k).comp (H.drift_smooth t ht).continuous
  · intro t ht k x
    have hk : |v t x k| ≤ ‖v t x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v t x) k
    exact hk.trans ((hM t ht x).trans (le_max_left _ _))
  · intro t ht k j
    exact (H.metric_smooth t ht k j).continuous
  · intro t ht k j x
    exact Weighted.nearIdentity_entry_abs_le G g H.metric_small H.metric_near t x
      (H.metric_symmetric t ht x) k j

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

theorem originalConstituent_native_flux_exists (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (s a b ϖ : ℝ) (hs : s ≠ 0) (hϖ : 0 < ϖ) (X0 φ : Vec 2) (k : Fin 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (U : ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hU : MemLp U 2 (volume.restrict (Set.Icc a b))) :
    ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        (fun z => F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ) k •
          Weighted.fluxCoordinateInjection k (F.identity v u γ).map
            (planeJetOrder (U t) (d - 1) I z))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
        planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            molecularRealPrice ν ρ (K v) (d - 2)
              (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) * ‖(F.identity v u γ).map‖) ^ 2 *
                  planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdmax := (Finset.mem_Icc.mp hd).2
  have hdu := hdesc v u γ
  have hKL : K v + (d - 1) ≤ K u + 1 := by omega
  have hr : 1 ≤ d - 1 := by omega
  have hρstar := div_pos hρ he
  let μ := volume.restrict (Set.Icc a b)
  let cc := cellSampleScalar F p c v u γ d I s (e / E) a b X0 φ k
  let R := derivativeReserveFactor (ρ / e) (K v) (d - 2)
  let B := (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
    molecularRealPrice ν ρ (K v) (d - 2)
      (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let A := B / R
  let T := Weighted.fluxCoordinateInjection k (F.identity v u γ).map
  have hR : 0 < R := by dsimp [R, derivativeReserveFactor]; positivity
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hA : 0 ≤ A := div_nonneg hB hR.le
  obtain ⟨hcm, hc, hcb⟩ := familyMolecular_cell_sample_coefficient F π hπ K Kmax hK dom
    ν e E ρ hν he hE hρ C J b₀ henv hmeas v u γ hγ d hd I p c s a b hs X0 φ k hwindow
  have hb : ∀ᵐ t ∂μ, ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤ A * polynomialMomentRoot ϖ z ^ 0 := by
    simpa only [pow_zero, mul_one, μ, A, B, R, cc] using (ae_restrict_of_ae hcb)
  have hu0 := integrated_zero_moment_gradient_ne_top (ρ / e) ϖ μ U hU
  obtain ⟨V, hV, _, hVr, _⟩ := scalarDerivativeProduct_ae_time_exists hKL hr I
    0 0 ϖ hϖ (ρ / e) hρstar cc hcm hc T A hA μ hb U hU hu0
  refine ⟨V, hV, ?_, ?_⟩
  · filter_upwards [hVr, ae_restrict_mem measurableSet_Icc] with t ht htI
    have hh := productReadout_planeValue_ae (Weighted.derivativeSourceOperator hKL I (U t)) (V t)
      (fun z => cc t z • T) ht
    rw [derivativeSourceOperator_planeValue] at hh
    simpa only [cc, cellSampleScalar, ite_eq_left htI, T, smul_apply] using hh
  · filter_upwards [hVr, ae_restrict_of_ae hcb] with t ht hct
    have hbd (j : ℕ) (hj : j ≤ K v) (z : Vec 2) :
        (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤ A * (1 : ℝ) := by
      simpa only [mul_one, cc, A, B, R] using hct j hj z
    have hh := scalarDerivativeProduct_readout_density_le hKL hr I (U t) (V t)
      (cc t) (hc t) T (ρ / e) A hρstar (fun _ => 1) hbd ht
    have hcost : A * ‖T‖ * derivativeReserveFactor (ρ / e) (K v) ((d - 1) - 1) ≤
        B * ‖(F.identity v u γ).map‖ := by
      have hdr : (d - 1) - 1 = d - 2 := by omega
      rw [hdr]
      change A * ‖T‖ * R ≤ _
      have hn := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fluxCoordinateInjection_norm_le k (F.identity v u γ).map) hA) hR.le
      have heq : A * ‖(F.identity v u γ).map‖ * R = B * ‖(F.identity v u γ).map‖ := by
        dsimp only [A]
        field_simp
      exact hn.trans_eq heq
    filter_upwards [hh] with z hz
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hcost 2) (multiplicationDensityBudget_nonneg (K v)))
      (planeGradFactorialDensity_nonneg (ρ / e) (U t) z)
    simp only [one_pow, mul_one] at hz
    exact hz.trans hn

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorConstituent_native_flux_exists (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
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
  obtain ⟨CT, hCT, hcoeff⟩ := familyMolecular_taylor_coefficient (ι := ι) (h := h)
    (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdmax := (Finset.mem_Icc.mp hd).2
  have hdu := hdesc v u γ
  have hKL : K v + (d - 1) ≤ K u + 1 := by omega
  have hr : 1 ≤ d - 1 := by omega
  let cc := slowTaylorTimeCoefficient Ks
    (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
  let B := CT * ∑ r ∈ Finset.range (Ks + 1), molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r
  let T := Weighted.fluxCoordinateInjection k (F.identity v u γ).map
  have hB : 0 ≤ B := by
    apply mul_nonneg hCT
    apply Finset.sum_nonneg
    intro r _
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  obtain ⟨hcm, hc, hb⟩ := hcoeff F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow
  have hb' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
        B / derivativeReserveFactor (ρ / e) (K v) ((d - 1) - 1) * polynomialMomentRoot ϖ z ^ Ks := by
    simpa only [cc, B, show (d - 1) - 1 = d - 2 by omega] using hb
  obtain ⟨V, hV, hVe, hv, hdensity⟩ := reserved_scalar_native_flux_exists hKL hr I n Ks ϖ (ρ / e)
    hϖ (div_pos hρ he) cc hcm hc T B hB (volume.restrict (Set.Icc a b)) hb' U hU henergy
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
    simpa only [cc, slowTaylorTimeCoefficient, ite_eq_left htI, T] using ht
  · filter_upwards [hdensity] with t ht
    filter_upwards [ht] with z hz
    have hcost := mul_le_mul_of_nonneg_left (fluxCoordinateInjection_norm_le k (F.identity v u γ).map) hB
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hB (norm_nonneg T)) hcost 2)
          (multiplicationDensityBudget_nonneg (K v))) (sq_nonneg (polynomialMomentRoot ϖ z ^ Ks)))
      (planeGradFactorialDensity_nonneg (ρ / e) (U t) z)
    exact hz.trans hn

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

theorem originalConstituent_native_flux_exists_all (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (s a b ϖ : ℝ) (hs : s ≠ 0) (hϖ : 0 < ϖ) (X0 φ : Vec 2) (k : Fin 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (U : ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hU : MemLp U 2 (volume.restrict (Set.Icc a b))) :
    ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        (fun z => F.flux p c v u γ d I (s * t) (X0 + (e / E) • z) (z + φ) k •
          Weighted.fluxCoordinateInjection k (F.identity v u γ).map
            (planeJetOrder (U t) (d - 1) I z))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
        planeFactorialDensity (ρ / e) (V t) z ≤ multiplicationDensityBudget (K v) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            molecularRealPrice ν ρ (K v) (d - 2)
              (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) * ‖(F.identity v u γ).map‖) ^ 2 *
                  planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  by_cases hγ : (F.identity v u γ).map = 0
  · have hzero : MemLp
        (fun _ : ℝ => (0 : PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v))))
        2 (volume.restrict (Set.Icc a b)) := Weighted.planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc a b))
    refine ⟨fun _ => 0, hzero, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only [hγ, Weighted.fluxCoordinateInjection_zero, zero_apply, smul_zero] using
          (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v)))
    · exact Filter.Eventually.of_forall (fun t => by
        filter_upwards [planeFactorialDensity_zero_ae
          (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
        simp only [hz, hγ, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])
  · exact originalConstituent_native_flux_exists F π hπ K Kmax hK hdesc dom ν e E ρ
      hν he hE hρ C J b₀ henv hmeas v u γ hγ d hd I p c s a b ϖ hs hϖ X0 φ k hwindow U hU

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

theorem originalTaylorConstituent_native_flux_exists_uniform (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (γ : F.Γ v u), (F.identity v u γ).map ≠ 0 → ∀ d,
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
  obtain ⟨CT, hCT, hcoeff⟩ := familyMolecular_taylor_coefficient_uniform Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow n U hU henergy
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdmax := (Finset.mem_Icc.mp hd).2
  have hdu := hdesc v u γ
  have hKL : K v + (d - 1) ≤ K u + 1 := by omega
  have hr : 1 ≤ d - 1 := by omega
  let cc := slowTaylorTimeCoefficient Ks
    (fun t X z => F.flux p c v u γ d I (s * t) X (z + φ) k) a b X0 (e / E)
  let B := CT * ∑ r ∈ Finset.range (Ks + 1), molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u γ d I r
  let T := Weighted.fluxCoordinateInjection k (F.identity v u γ).map
  have hB : 0 ≤ B := by
    apply mul_nonneg hCT
    apply Finset.sum_nonneg
    intro r _
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  obtain ⟨hcm, hc, hb⟩ := hcoeff F π hπ K hK dom ν e E ρ hν he hE hρ C J b₀ hKs henv
    hmeas v u γ hγ d hd I p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ k hwindow
  have hb' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (cc t) z‖ ≤
        B / derivativeReserveFactor (ρ / e) (K v) ((d - 1) - 1) * polynomialMomentRoot ϖ z ^ Ks := by
    simpa only [cc, B, show (d - 1) - 1 = d - 2 by omega] using hb
  obtain ⟨V, hV, hVe, hv, hdensity⟩ := reserved_scalar_native_flux_exists hKL hr I n Ks ϖ (ρ / e)
    hϖ (div_pos hρ he) cc hcm hc T B hB (volume.restrict (Set.Icc a b)) hb' U hU henergy
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
    simpa only [cc, slowTaylorTimeCoefficient, ite_eq_left htI, T] using ht
  · filter_upwards [hdensity] with t ht
    filter_upwards [ht] with z hz
    have hcost := mul_le_mul_of_nonneg_left (fluxCoordinateInjection_norm_le k (F.identity v u γ).map) hB
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hB (norm_nonneg T)) hcost 2)
          (multiplicationDensityBudget_nonneg (K v))) (sq_nonneg (polynomialMomentRoot ϖ z ^ Ks)))
      (planeGradFactorialDensity_nonneg (ρ / e) (U t) z)
    exact hz.trans hn

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Indices retain the original identity, current order, derivative word, and output coordinate. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

abbrev OriginalSourceIndex (F : ChartedFamily ι h D P Ctx) (v u : ι) :=
  Σ γ : F.Γ v u, Σ d : Finset.Icc 2 (F.identity v u γ).maxOrder,
    DerivativeWord2 (d.1 - 1) × Fin 2

instance originalSourceIndexFintype (F : ChartedFamily ι h D P Ctx) (v u : ι) : Fintype (OriginalSourceIndex F v u) :=
  inferInstanceAs (Fintype (Σ γ : F.Γ v u, Σ d : Finset.Icc 2 (F.identity v u γ).maxOrder,
    DerivativeWord2 (d.1 - 1) × Fin 2))

def originalSourcePrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Kmax : ℕ) (dom : F.Domain) (ν e E ρ : ℝ) (v u : ι)
    (α : OriginalSourceIndex F v u) : ℝ :=
  Real.sqrt (multiplicationDensityBudget (K v)) *
    ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
      molecularRealPrice ν ρ (K v) (α.2.1.1 - 2)
        (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u α.1 α.2.1.1 α.2.2.1)) *
            ‖(F.identity v u α.1).map‖)

theorem originalSourcePrice_nonneg (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Kmax : ℕ) (dom : F.Domain) (ν e E ρ : ℝ) (hν : 0 ≤ ν) (hρ : 0 ≤ ρ)
    (v u : ι) (α : OriginalSourceIndex F v u) :
    0 ≤ originalSourcePrice F K Kmax dom ν e E ρ v u α := by
  unfold originalSourcePrice
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (molecularRealPrice_nonneg ν ρ hν hρ _ _ _)) (norm_nonneg _))

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original retained constituent prices obey the literal independent-jet envelope before cancellation. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def analyticOriginalSourcePriceENN (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (Ks J : ℕ) (v u : ι) (α : OriginalSourceIndex F v u) : ℝ≥0∞ :=
  ENNReal.ofReal ‖(F.identity v u α.1).map‖ *
    ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1),
      jetSupFam (fun x : F.Index => dom x.1 x.2) r q
        (fun x => F.slowFlux 1 x.1 x.2 v u α.1 α.2.1.1 α.2.2.1)

def analyticOriginalSourcePrice (F : ChartedFamily ι h D P Ctx) (dom : F.Domain)
    (Ks J : ℕ) (v u : ι) (α : OriginalSourceIndex F v u) : ℝ :=
  (analyticOriginalSourcePriceENN F dom Ks J v u α).toReal

theorem analyticOriginalSourcePriceENN_sum_eq (F : ChartedFamily ι h D P Ctx)
    (dom : F.Domain) (Ks J : ℕ) (v u : ι) :
    (∑ α : OriginalSourceIndex F v u, analyticOriginalSourcePriceENN F dom Ks J v u α) =
      2 * ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1),
            jetSupFam (fun x : F.Index => dom x.1 x.2) r q
              (fun x => F.slowFlux 1 x.1 x.2 v u γ d I) := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, analyticOriginalSourcePriceENN, Fin.sum_univ_two]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  conv_rhs => arg 2; arg 2; rw [← Finset.sum_coe_sort]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem analyticOriginalSourcePrice_sum_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (henv : IsAnalyticEnvelope F π dom 1 1 Ks J b) (v u : ι) (hb : 0 ≤ b v u) :
    Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, analyticOriginalSourcePrice F dom Ks J v u α) ≤ 2 * b v u := by
  classical
  have hh := henv.2 v u
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hh
  have hs := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ≥0∞) ≤ 2)
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hb)).mp
  have hn : ∀ α : OriginalSourceIndex F v u, 0 ≤ analyticOriginalSourcePrice F dom Ks J v u α :=
    fun _ => ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun α _ => hn α)]
  have hp : (∑ α : OriginalSourceIndex F v u, ENNReal.ofReal (analyticOriginalSourcePrice F dom Ks J v u α)) ≤
      ∑ α : OriginalSourceIndex F v u, analyticOriginalSourcePriceENN F dom Ks J v u α :=
    Finset.sum_le_sum (fun α _ => ENNReal.ofReal_toReal_le)
  apply (mul_le_mul_of_nonneg_left hp bot_le).trans
  rw [analyticOriginalSourcePriceENN_sum_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  convert hs using 1; ring

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Price sums count each original identity and order, with only the two flux coordinates repeated. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalConstituent_price_sum_eq (F : ChartedFamily ι h D P Ctx) (v u : ι)
    (q : ∀ _γ : F.Γ v u, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (A : ℝ) :
    (∑ α : OriginalSourceIndex F v u,
      A * q α.1 α.2.1.1 α.2.2.1 * ‖(F.identity v u α.1).map‖) =
      (2 * A) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1), q γ d I := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Fin.sum_univ_two]
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

end AVRegularity.CycleWords
end
