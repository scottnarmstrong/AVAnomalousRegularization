-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.WordPredecessorFluxIdentity

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.Weighted

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWords_clipped_raw_energy_bound {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hW : MemLp W 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) 
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) :
    let T := planeIntervalTransport (E := E) a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion (E := E) a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let L := fun (α : JetIndex2 K) t => planeJetFluxOperator K α (Q t) - D t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let R := fun (α : JetIndex2 K) t => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m t x)) (U t).toFunction.jet +
      (∫ s in a..t, rawWeightedGradientEnergy ρ
        (fun x => clipWeight B (C.W m s x)) (W s).toFunction.jet) ≤
      (rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m a x)) (U a).toFunction.jet +
        8 * (∫ s in a..b, ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, clipWeight B (C.W m s x) * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α s k x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) +
        2 * (∫ s in a..b, ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, clipWeight B (C.W m s x) * (‖R α s x‖ * ‖planeJetReadoutOperator K α (U s) x‖)))) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  let T := planeIntervalTransport (E := E) a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
  let D := planeIntervalDiffusion (E := E) a b hab G
    (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
  let e := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖planeJetReadoutOperator K α (U t) x‖ ^ 2
  let d := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖(WithLp.toLp 2 (fun k : Fin 2 =>
      planeH1GradientOperator (planeWordH1SliceOperator K α (W t)) k x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let p := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖(WithLp.toLp 2 (fun k : Fin 2 =>
      (planeJetFluxOperator K α (Q t) - D t
        (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) k x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let z := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) *
      (‖(planeJetReadoutOperator K α (H t) + T t
        (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) x‖ *
        ‖planeJetReadoutOperator K α (U t) x‖)
  have hint α := storedWord_residual_time_integrable a b hab v hv hvm Mv hvb G hG hGm
    g hg4 hGnear hGs t₀ S ϖ zc N m Cw C hm U H W Q hH hQ hcurve B hB α
  have hp α : IntervalIntegrable (p α) volume a b :=
    intervalIntegrable_of_integrable_Icc hab (hint α).1
  have hz α : IntervalIntegrable (z α) volume a b :=
    intervalIntegrable_of_integrable_Icc hab (hint α).2
  have he t : (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * e α t) =
      rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m t x)) (U t).toFunction.jet :=
    planeStoredWord_factorial_energy ρ _ (U t)
  intro t ht
  have hh := storedWords_clipped_value_energy_sum a b hab v hv hvm hdiv Mv hMv hvb
    G hG hGm g hg4 hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb U H W Q hH hQ hcurve B hB ρ t ht
  change (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * (e α t + ∫ s in a..t, d α s)) ≤
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (e α a + 8 * (∫ s in a..b, p α s) + 2 * (∫ s in a..b, z α s))) *
      Real.exp (18 * C.lam m * (t - a)) at hh
  rw [finite_weighted_sum_add, finite_three_energy_budget_sum, he t, he a,
    intervalIntegral_weighted_sum a b _ p hp, intervalIntegral_weighted_sum a b _ z hz] at hh
  have hWt := hW.mono_measure
    (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl)
  have hd := planeStoredWord_gradient_interval_energy C m hm B hB ρ a t ht.1 W hWt
  change (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * (∫ s in a..t, d α s)) = _ at hd
  rw [hd] at hh
  exact hh

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_ordered_planeWeakHilbertCurve
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
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
      (fun _ _ => 0) u w) (i : Fin 1 × ι) (α : JetIndex2 (κ i.1 i.2)) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    PlaneWeakHilbertCurve a b (fun t => planeJetReadoutOperator (κ i.1 i.2) α (u i t))
      (fun t => planeWordH1SliceOperator (κ i.1 i.2) α (w i t))
      (fun t => planeSourceDual (planeJetReadoutOperator (κ i.1 i.2) α (H t))
        (planeJetFluxOperator (κ i.1 i.2) α (S t))) := by
  dsimp only
  apply plane_ordered_source_curve
  · exact hsln.1 i
  · exact hsln.2.1 i
  · exact scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
      hV ha hB hlam hbv hjets (w i) (hsln.2.1 i)
  · exact scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
      (w i) (F i) (hsln.2.1 i) (hF i)
  · filter_upwards [hsln.2.2.1 i] with t ht
    exact ht.symm
  · intro s hs t ht hst Z
    have hi := scalarChainTrace_increment a b hab κ v G f F u w hsln i hs ht Z
    refine hi.trans ?_
    apply intervalIntegral.integral_congr
    intro r hr
    exact (scalarSobolevSource_pair_eq_raw (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) g hg4 hGnear hGs (w i) (F i) r
      (Set.Icc_subset_Icc hs.1 ht.2 (by simpa only [Set.uIcc_of_le hst] using hr)) Z).symm

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! An actual scalar polynomial coefficient consumes its degree in the time-integrated Sobolev moments. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem exists_scalar_polynomial_product_time {K : ℕ}
    (n r : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ)
    (c : ℝ → Vec 2 → ℝ) (hcm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (T : E →L[ℝ] F)
    (A : ℝ) (hA : 0 ≤ A)
    (hcb : ∀ t j, j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (c t) x‖ ≤ A * (1 + ‖x‖) ^ r)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy
      (fun x => (planeMomentSquareRoot (n + r) ϖ 0 x) ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      ∀ᵐ t ∂μ, ∀ α, planeJetReadoutOperator K α (V t) =ᵐ[volume]
        multiplicationRawJet (fun x => c t x • T) (U t).toFunction.jet α := by
  classical
  borelize (E →L[ℝ] F)
  let C := fun t x => c t x • T
  have hC (t : ℝ) : ContDiff ℝ (K : ℕ) (C t) := (hc t).smul_const T
  have hCm (l : Fin (K + 1)) (β : DerivativeWord2 l.val) :
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)) :=
    parameter_orderedCoefficientDerivative_joint_measurable K l.val
      (Nat.le_of_lt_succ l.isLt) C (fun x => (hcm x).smul_const T) hC β
  let B := fun l : Fin (K + 1) => (Fintype.card (DerivativeWord2 l.val) : ℝ) *
    (A * ‖T‖) * (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ r
  have hB (l : Fin (K + 1)) : 0 ≤ B l := by dsimp [B]; positivity
  let p := planeMomentSquareRoot n ϖ 0
  let q := planeMomentSquareRoot (n + r) ϖ 0
  have hpb (l : Fin (K + 1)) (t : ℝ) (x : Vec 2) :
      p x * ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l * q x :=
    scalar_operator_moment_array_bound n r l.val ϖ hϖ (c t)
      ((hc t).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)) T A hA
      (hcb t l.val (Nat.le_of_lt_succ l.isLt)) x
  have hb (l : Fin (K + 1)) (t : ℝ) (x : Vec 2) :
      ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l * q x :=
    by
      calc
        _ ≤ p x * ‖coefficientDerivativeArray (C t) l.val x‖ := by
          simpa only [one_mul] using! mul_le_mul_of_nonneg_right
            (planeMomentSquareRoot_one_le n ϖ 0 x)
            (norm_nonneg (coefficientDerivativeArray (C t) l.val x))
        _ ≤ _ := hpb l t x
  let V := growingPlaneHkCurve q (planeMomentSquareRoot_continuous _ _ _)
    (fun x => (planeMomentSquareRoot_pos _ _ _ x).le) C hC B hB hb U
  have hV : MemLp V 2 μ := growingPlaneHkCurve_time_memLp q
    (planeMomentSquareRoot_continuous _ _ _) (planeMomentSquareRoot_pos _ _ _)
    C hC hCm B hB hb μ U hU he
  refine ⟨V, hV, ?_, ?_⟩
  · apply integrated_weightedFactorialNormSq_ne_top n ϖ 0 ρ μ V hV
    intro α
    exact growingPlaneHkCurve_weighted_energy_ne_top q
      (planeMomentSquareRoot_continuous _ _ _) (planeMomentSquareRoot_pos _ _ _)
      p (planeMomentSquareRoot_continuous _ _ _) (fun x => (planeMomentSquareRoot_pos _ _ _ x).le)
      C hC hCm B hB hb B hB hpb μ U hU he α
  · filter_upwards [planeJet_energy_ae_ne_top q (planeMomentSquareRoot_continuous _ _ _)
      (planeMomentSquareRoot_pos _ _ _) μ U hU he] with t ht
    intro α
    exact growingPlaneHkCurve_readout_ae q (planeMomentSquareRoot_continuous _ _ _)
      (fun x => (planeMomentSquareRoot_pos _ _ _ x).le) C hC B hB hb U t ht α

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevSource_word_spatial_budget {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc ta tb, ∀ x, (G t x).IsSymm)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb)
    (hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (U : PlaneHk Set.univ K E) (hU : U = truncatePlaneHk (Nat.le_succ K) (W t))
    (ρ : ℝ) (q : Vec 2 → ℝ)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hstrain : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1) (CG : ℕ → ℝ)
    (hmetricEnvelope : ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hmetricJets : ∀ l, 1 ≤ l → l ≤ K → ∀ x k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x) (Cq : ℝ) (hqb : ∀ x, q x ≤ Cq) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := planeIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      g hg4 hGnear hGs
    let R := fun α : JetIndex2 K => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let L := fun α : JetIndex2 K => planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * (‖R α x‖ * ‖planeJetReadoutOperator K α U x‖))) ≤
      (ν / 4) * rawWeightedGradientEnergy ρ q (W t).toFunction.jet) ∧
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) ≤
      2 * ((metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 *
        rawWeightedGradientEnergy ρ q (W t).toFunction.jet) +
        2 * rawWeightedFactorialEnergy ρ q (F t).toFunction.jet) := by
  dsimp only
  have hr := scalarSobolevSource_word_energy_readout hK hab v hv V strain B lam hbv hjets
    G hG M hb g hg4 hGnear hGs W F t ht hG1 U hU ρ q
  dsimp only at hr
  constructor
  · rw [hr.1]
    exact planeDriftValueSource_budget hK ρ strain B lam ν V hρ hstrain hB hlam hν hV
      hsmall hstrainSmall (v t) (hv t ht) (hbv t ht) (hjets t ht) q hq hq0 Cq hqb
      (W t).toFunction.jet (W t).toFunction.memL2
  · rw [hr.2]
    exact planeMetricForcedFlux_budget ρ δ g hρ.le hδ hg hscale (G t) (hG t ht)
      CG hmetricEnvelope hmetricJets q hq hq0 Cq hqb
      (W t).toFunction.jet (W t).toFunction.memL2 (F t).toFunction.jet (F t).toFunction.memL2

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A literal nonzero letter term acts on its positive derivative source with the required moment budget. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {D : ℕ}

theorem exists_letter_derivative_product_time (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (i : Fin 2) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ X z, Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (K Q n : ℕ) (hKJ : K ≤ J) (hKQ : K + (o.1 - 1) ≤ Q + 1)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ) (T : h u →L[ℝ] F)
    (W : ℝ → PlaneHk Set.univ (Q + 1) (h u))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (he : (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq (n + L.slow) ϖ 0 ρ Q (W t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ α,
        planeJetReadoutOperator K α (V t) =ᵐ[volume]
          multiplicationRawJet (fun z => (taylorSlow lo L.slow
            (fun X => ((L.edge v u o).get k).coeff w t X z i) X₀ (δ • z)) • T)
            (derivativeSourceOperator hKQ w (W t)).toFunction.jet α := by
  obtain ⟨c, hcm, hc, ⟨A, hA, hcb⟩, hce⟩ :=
    exists_letter_taylor_measurable_extension π hπ L a b J H hL v u o k hk w i lo X₀ δ hm
  let U := fun t => derivativeSourceOperator hKQ w (W t)
  have hU : MemLp U 2 (volume.restrict (Set.Icc a b)) :=
    (derivativeSourceOperator (E := h u) hKQ w).comp_memLp' hW
  have hr : 0 < o.1 - 1 := by have := (Finset.mem_Icc.mp o.2).1; omega
  have hUe (α : JetIndex2 K) := derivativeSourceOperator_weighted_jet_integral_ne_top
    hKQ hr w (n + L.slow) ϖ 0 ρ hρ (volume.restrict (Set.Icc a b)) W he α
  obtain ⟨V, hV, hVe, hVr⟩ := exists_scalar_polynomial_product_time n L.slow ϖ hϖ ρ c hcm
    (fun t => (hc t).of_le (by exact_mod_cast hKJ)) T A hA
    (fun t j hj => hcb t j (hj.trans hKJ)) (volume.restrict (Set.Icc a b)) U hU hUe
  refine ⟨V, hV, hVe, ?_⟩
  filter_upwards [hVr, ae_restrict_of_ae hce, ae_restrict_mem measurableSet_Icc] with t ht hc' htI
  have heq : c t = fun z => taylorSlow lo L.slow
      (fun X => ((L.edge v u o).get k).coeff w t X z i) X₀ (δ • z) := funext (hc' htI)
  intro α
  simpa only [heq] using ht α
end

/-! Each literal Taylor letter term is an actual weighted Sobolev flux curve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_nonzero_letter_term_flux_time (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (i : Fin 2) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ X z, Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (K Q n : ℕ) (hKJ : K ≤ J) (hKQ : K + (o.1 - 1) ≤ Q + 1)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (W : ℝ → PlaneHk Set.univ (Q + 1) (h u))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (he : (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq (n + L.slow) ϖ 0 ρ Q (W t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
        planeJetReadoutOperator K (valueIndex2 K) (V t) =ᵐ[volume] fun z =>
          (taylorSlow lo L.slow (fun X => ((L.edge v u o).get k).coeff w t X z i)
            X₀ (δ • z)) • fluxCoordinateInjection i ((L.edge v u o).get k).map
              ((W t).toFunction.jet (sourceWordIndex hKQ w) z) := by
  obtain ⟨V, hV, hVe, hVr⟩ := exists_letter_derivative_product_time π hπ L a b J H hL
    v u o k hk w i lo X₀ δ hm K Q n hKJ hKQ ϖ hϖ ρ hρ
    (fluxCoordinateInjection i ((L.edge v u o).get k).map) W hW he
  refine ⟨V, hV, hVe, ?_⟩
  filter_upwards [hVr] with t ht
  have hh := scalar_product_value_readout_ae (derivativeSourceOperator hKQ w (W t))
    (V t) (fun z => taylorSlow lo L.slow
      (fun X => ((L.edge v u o).get k).coeff w t X z i) X₀ (δ • z))
    (fluxCoordinateInjection i ((L.edge v u o).get k).map) (ht (valueIndex2 K))
  rw [derivativeSourceOperator_value_readout, derivative_source_value_index] at hh
  filter_upwards [hh, planeJetReadout_ae_raw (W t) (sourceWordIndex hKQ w)] with z hz hw
  rw [hz, hw]
end

/-! Each literal Taylor letter term is an actual weighted Sobolev flux curve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_letter_term_flux_time (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (w : DerivativeWord2 (o.1 - 1)) (i : Fin 2) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ X z, Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (K Q n : ℕ) (hKJ : K ≤ J) (hKQ : K + (o.1 - 1) ≤ Q + 1)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (W : ℝ → PlaneHk Set.univ (Q + 1) (h u))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (he : (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq (n + L.slow) ϖ 0 ρ Q (W t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
        planeJetReadoutOperator K (valueIndex2 K) (V t) =ᵐ[volume] fun z =>
          (taylorSlow lo L.slow (fun X => ((L.edge v u o).get k).coeff w t X z i)
            X₀ (δ • z)) • fluxCoordinateInjection i ((L.edge v u o).get k).map
              ((W t).toFunction.jet (sourceWordIndex hKQ w) z) := by
  classical
  by_cases hk : ((L.edge v u o).get k).map = 0
  · refine ⟨fun _ => 0, planeHk_zero_time_memLp (E := PiLp 2 (fun _ : Fin 2 => h v)) K
      (volume.restrict (Set.Icc a b)), ?_, ?_⟩
    · simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero, ne_eq,
        ENNReal.zero_ne_top, not_false_eq_true]
    · filter_upwards with t
      simp only [map_zero]
      filter_upwards [Lp.coeFn_zero (PiLp 2 (fun _ : Fin 2 => h v)) 2
        (volume : Measure (Vec 2))] with z hz
      rw [hz, hk]
      simp only [Pi.zero_apply, fluxCoordinateInjection_zero, zero_apply, smul_zero]
  · exact exists_nonzero_letter_term_flux_time π hπ L a b J H hL v u o k hk
      w i lo X₀ δ hm K Q n hKJ hKQ ϖ hϖ ρ hρ W hW he
end

/-! A complete finite edge list gives the literal weighted Taylor-letter forcing. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_letter_edge_flux_time (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ k : Fin (L.edge v u o).length, ∀ w X z,
      Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (K Q n : ℕ) (hKJ : K ≤ J) (hKQ : K + (o.1 - 1) ≤ Q + 1)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (W : ℝ → PlaneHk Set.univ (Q + 1) (h u))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (he : (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq (n + L.slow) ϖ 0 ρ Q (W t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
        planeJetReadoutOperator K (valueIndex2 K) (V t) =ᵐ[volume] fun z =>
          slowEvalCoefficient
            (fun f z => taylorSlow lo L.slow f X₀ (δ • z)) (L.edge v u o) t z
            (WithLp.toLp 2 (fun w => (W t).toFunction.jet (sourceWordIndex hKQ w) z)) := by
  classical
  let Idx := Fin (L.edge v u o).length × (DerivativeWord2 (o.1 - 1) × Fin 2)
  have hex (p : Idx) := exists_letter_term_flux_time π hπ L a b J H hL v u o p.1
    p.2.1 p.2.2 lo X₀ δ (hm p.1 p.2.1) K Q n hKJ hKQ ϖ hϖ ρ hρ W hW he
  choose U hU hUe hUr using hex
  obtain ⟨V, hV, hVe, hVr⟩ := finite_weighted_sobolev_flux_sum n ϖ 0 ρ hρ
    (volume.restrict (Set.Icc a b)) U hU hUe _ hUr
  refine ⟨V, hV, hVe, ?_⟩
  filter_upwards [hVr] with t ht
  filter_upwards [ht] with z hz
  rw [hz, slowEvalCoefficient_value_expansion]
  simp only [Idx, Fintype.sum_prod_type]
  exact Fin.sum_univ_fun_getElem (L.edge v u o)
    (fun γ => ∑ w : DerivativeWord2 (o.1 - 1), ∑ i : Fin 2,
      (taylorSlow lo L.slow (fun X => γ.coeff w t X z i) X₀ (δ • z)) •
        fluxCoordinateInjection i γ.map ((W t).toFunction.jet (sourceWordIndex hKQ w) z))
end

/-! The full admissible Taylor letter is an actual flux curve with a finite moment budget. -/

section
variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_admissible_letter_flux_time (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (ta tb : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc ta tb ×ˢ Set.univ) J H)
    (κ : σ → ℕ) (a : σ) (b : ι → σ) (v : ι) (hKJ : κ a ≤ J)
    (lo n : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ u o (k : Fin (L.edge v u o).length), ∀ w X z,
      Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (W : ∀ u, ℝ → PlaneHk Set.univ (κ (b u) + 1) (h u))
    (hW : ∀ u, MemLp (W u) 2 (volume.restrict (Set.Icc ta tb)))
    (he : ∀ u, (∫⁻ t in Set.Icc ta tb,
      weightedGradFactorialNormSq (n + L.slow) ϖ 0 ρ (κ (b u)) (W u t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ (κ a) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc ta tb)) ∧
      (∫⁻ t in Set.Icc ta tb, weightedFactorialNormSq n ϖ 0 ρ (κ a) (V t)) ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc ta tb)),
        planeJetReadoutOperator (κ a) (valueIndex2 (κ a)) (V t) =ᵐ[volume] fun z =>
          ∑ u : ι, ∑ o : admissibleOrders κ D a (b u),
            slowEvalCoefficient (fun f z => taylorSlow lo L.slow f X₀ (δ • z))
              (L.edge v u (admissibleLetterOrder κ D a (b u) o)) t z
              (WithLp.toLp 2 (fun w => (W u t).toFunction.jet
                (admissibleLetterSourceIndex κ D a (b u) o w) z)) := by
  classical
  let Idx := Σ u : ι, admissibleOrders κ D a (b u)
  have hex (p : Idx) := exists_letter_edge_flux_time π hπ L ta tb J H hL v p.1
    (admissibleLetterOrder κ D a (b p.1) p.2) lo X₀ δ
    (hm p.1 _) (κ a) (κ (b p.1)) n hKJ
    (admissible_letter_source_reserve κ D a (b p.1) p.2)
    ϖ hϖ ρ hρ (W p.1) (hW p.1) (he p.1)
  choose U hU hUe hUr using hex
  obtain ⟨V, hV, hVe, hVr⟩ := finite_weighted_sobolev_flux_sum n ϖ 0 ρ hρ
    (volume.restrict (Set.Icc ta tb)) U hU hUe _ hUr
  refine ⟨V, hV, hVe, ?_⟩
  filter_upwards [hVr] with t ht
  filter_upwards [ht] with z hz
  simpa only [Idx, Fintype.sum_sigma, admissibleLetterSourceIndex, admissibleLetterOrder, sourceWordIndex] using! hz
end

end AVRegularity.Weighted
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_words_clipped_source_integral_budgets
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
    (clip ρ : ℝ) (hclip : 0 < clip)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1) (CG : ℕ → ℝ)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let Q := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    let T := planeIntervalTransport (E := h i.2) a b hab v (fun t ht => (hv t ht).continuous) V hbv
    let D := planeIntervalDiffusion (E := h i.2) a b hab G
      (fun t ht k j => (hG1 t ht k j).continuous) g hg4 hGnear hGs
    let R := fun (α : JetIndex2 (κ i.1 i.2)) t => planeJetReadoutOperator (κ i.1 i.2) α (H t) +
      T t (planeH1GradientOperator (planeWordH1SliceOperator (κ i.1 i.2) α (w i t)))
    let L := fun (α : JetIndex2 (κ i.1 i.2)) t => planeJetFluxOperator (κ i.1 i.2) α (Q t) -
      D t (planeH1GradientOperator (planeWordH1SliceOperator (κ i.1 i.2) α (w i t)))
    let q := fun t x => clipWeight clip (C.W m t x)
    let d := fun t => rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
    let fenergy := fun t => rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet
    ((∫ t in a..b, ∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
      (∫ x, q t x * (‖R α t x‖ * ‖planeJetReadoutOperator (κ i.1 i.2) α (u i t) x‖))) ≤
      (ν / 4) * (∫ t in a..b, d t)) ∧
    ((∫ t in a..b, ∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
      (∫ x, q t x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α t k x) :
        PiLp 2 (fun _ : Fin 2 => h i.2))‖ ^ 2)) ≤
      2 * ((metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 * (∫ t in a..b, d t)) +
        2 * (∫ t in a..b, fenergy t)) := by
  dsimp only
  have hH := scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
    hV ha (le_trans (by norm_num) hB) hlam hbv hjets (w i) (hsln.2.1 i)
  have hQ := scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
    (w i) (F i) (hsln.2.1 i) (hF i)
  have hcv α := scalarChain_ordered_planeWeakHilbertCurve a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha (le_trans (by norm_num) hB) hlam hbv hjets G hGm hG M hb g hg4
    hGnear hGs f F hF u w hsln i α
  have hint α := storedWord_residual_time_integrable a b hab v
    (fun t ht => (hv t ht).of_le (by simp)) hvm V hbv G hG1 hGm g hg4 hGnear hGs
    t₀ S ϖ zc N m Cw C hm (u i) _ (w i) _ hH hQ hcv clip hclip α
  have hRint := intervalIntegrable_of_integrable_Icc hab
    (integrable_finsetSum (Finset.univ : Finset (JetIndex2 (κ i.1 i.2)))
      (fun α _ => (hint α).2.const_mul (factorialWeight ρ α.1.val)))
  have hLint := intervalIntegrable_of_integrable_Icc hab
    (integrable_finsetSum (Finset.univ : Finset (JetIndex2 (κ i.1 i.2)))
      (fun α _ => (hint α).1.const_mul (factorialWeight ρ α.1.val)))
  have hDint := intervalIntegrable_of_integrable_Icc hab
    (rawWeightedGradient_time_integrable C m hm clip hclip ρ _ (w i) (hsln.2.1 i))
  have hFint := intervalIntegrable_of_integrable_Icc hab
    (rawWeightedFlux_time_integrable C m hm clip hclip ρ _ (F i) (hF i))
  have hpoint := hsln.2.2.1 i
  have hbud := hpoint.and (ae_restrict_mem measurableSet_Icc)
  have hbds := hbud.mono (fun t ht =>
    scalarSobolevSource_word_spatial_budget (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) g hg4 hGnear hGs (w i) (F i) t ht.2 hG1 (u i t) ht.1.symm
      ρ (fun x => clipWeight clip (C.W m t x)) hρ ν hν ha hB hlam hV hsmall hstrainSmall
      δ hδ hg hscale CG
      (metricEntryEnvelope_bound (hκ i) G CG g δ hg hδ hg4 hGnear hGs hmetricJets t ht.2)
      (fun l hl hlK x k j => hmetricJets t ht.2 x l hl (hlK.trans (hκ i)) k j)
      ((chartWeights_clipped_time_coefficient C m hm clip hclip).1 t)
      (fun x => (clipWeight_pos hclip (C.pos m hm t x)).le) clip
      (fun x => clipWeight_le_bound hclip (C.pos m hm t x)))
  exact interval_residual_source_budgets hab hRint hLint hDint hFint hbds
end

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_gronwall
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
    (clip ρ : ℝ) (hclip : 0 < clip)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1) (CG : ℕ → ℝ)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy ρ (q t) (u i t).toFunction.jet +
      (∫ s in a..t, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet) ≤
      (rawWeightedFactorialEnergy ρ (q a) (f i).toFunction.jet +
        16 * (∫ s in a..b, rawWeightedFactorialEnergy ρ (q s) (F i s).toFunction.jet) +
        (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) *
          (∫ s in a..b, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet)) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  have hH := scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
    hV ha (le_trans (by norm_num) hB) hlam hbv hjets (w i) (hsln.2.1 i)
  have hQ := scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
    (w i) (F i) (hsln.2.1 i) (hF i)
  have hcv α := scalarChain_ordered_planeWeakHilbertCurve a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha (le_trans (by norm_num) hB) hlam hbv hjets G hGm hG M hb g hg4
    hGnear hGs f F hF u w hsln i α
  have hraw := storedWords_clipped_raw_energy_bound a b hab v
    (fun t ht => (hv t ht).of_le (by simp)) hvm hdiv V hV hbv G hG1 hGm g hg4 hGnear hGs
    t₀ S ϖ zc N m Cw C hm hwa hwb (u i) _ (w i) _ (hsln.2.1 i) hH hQ hcv clip hclip ρ
  have hbud := scalarChain_words_clipped_source_integral_budgets a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip ρ hclip
    hρ ν hν hsmall hstrainSmall δ hδ hg hscale CG hmetricJets
  dsimp only at hraw hbud
  intro t ht
  have hh := hraw t ht
  rw [hsln.2.2.2.1 i] at hh
  have hmerge := three_source_budget_merge
    (I := rawWeightedFactorialEnergy ρ (fun x => clipWeight clip (C.W m a x)) (f i).toFunction.jet)
    hbud.2 hbud.1
  exact hh.trans (mul_le_mul_of_nonneg_right hmerge (Real.exp_pos _).le)
end

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_absorption
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet +
      (∫ s in a..b, rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) / 2 ≤
      3 * Real.exp (18 * Cw m) *
        (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
          16 * (∫ s in a..b, rawWeightedFactorialEnergy (r / L) (q s) (F i s).toFunction.jet)) := by
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hν : 0 < 1 / L ^ 2 := one_div_pos.mpr (sq_pos_of_pos hLp)
  have hρ : 0 < r / L := div_pos hr hLp
  have hs : B * (r / L) / lam ≤ 1 / 2 :=
    (reducedRadius_drift_scale hlam hLp hsmall).trans
      (div_le_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hL)
  have hst : strain * B * (r / L) ^ 2 ≤ (1 / L ^ 2) / 8 := by
    convert reducedRadius_strain_scale (L := L) hstrainSmall using 1
    ring
  have hsc : (r / L) * δ ≤ 1 :=
    (reducedRadius_metric_scale hLp hscale).trans (by simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hL)
  have hh := scalarChain_clipped_factorial_gronwall a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip (r / L) hclip
    hρ (1 / L ^ 2) hν hs hst δ hδ hg hsc CG hmetricJets hdiv hwa hwb
  dsimp only at hh
  let q := fun t x => clipWeight clip (C.W m t x)
  let e := fun t => rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet
  let d := fun t => rawWeightedGradientEnergy (r / L) (q t) (w i t).toFunction.jet
  let ff := fun t => rawWeightedFactorialEnergy (r / L) (q t) (F i t).toFunction.jet
  let A := Real.exp (18 * Cw m)
  let c := 16 * (metricRadiusConstant (κ i.1 i.2) CG * g * ((r / L) * δ)) ^ 2 +
    (1 / L ^ 2) / 2
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  have he0 t : 0 ≤ e t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hd0 t : 0 ≤ d t := rawWeightedGradientEnergy_nonneg _ _ (hq0 t) _
  have hf0 t : 0 ≤ ff t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hD0 : 0 ≤ ∫ s in a..b, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0)
  have hF0 : 0 ≤ ∫ s in a..b, ff s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hf0)
  have hI0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet :=
    rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) _
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : A * c ≤ 1 / 2 := maximalSlot_radius_source_reserve (hκ i) CG
    (Real.exp_pos _).le hL hreserve hr.le hδ hg hg4 hscale
  have hCw : 0 ≤ Cw m := (by norm_num : (0 : ℝ) ≤ 1).trans
    (chartWeights_constant_ge_one C m hm a ⟨hwa, hab.trans hwb⟩)
  have hbudget0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
      16 * (∫ s in a..b, ff s) + c * (∫ s in a..b, d s) := by positivity
  have hbound t (ht : t ∈ Icc a b) : e t + (∫ s in a..t, d s) ≤
      A * (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
        16 * (∫ s in a..b, ff s) + c * (∫ s in a..b, d s)) := by
    have hexp := chart_interval_rate_exp_bound hwa hab hwb ht
      (C.lam_bound m hm).1 hCw (C.lam_bound m hm).2
    exact (hh t ht).trans (by
      rw [mul_comm A]
      exact mul_le_mul_of_nonneg_left hexp hbudget0)
  intro t ht
  have hpart0 : 0 ≤ ∫ s in a..t, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict ht.1 (Filter.Eventually.of_forall hd0)
  have het := (le_add_of_nonneg_right hpart0).trans (hbound t ht)
  exact retained_full_interval_energy (he0 b) hD0 hc het (hbound b ⟨hab, le_rfl⟩)
end

end AVRegularity.Weighted
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_ennreal
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      storedChartFactorialEnergy (r / L) (q t) (u i t) +
      ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
      ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (storedChartFactorialEnergy (r / L) (q a) (f i) +
          16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s)) := by
  dsimp only
  have hh := scalarChain_clipped_factorial_absorption a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip r L hclip hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
  dsimp only at hh
  let q := fun t x => clipWeight clip (C.W m t x)
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  obtain ⟨hqc, _, hqb⟩ := chartWeights_clipped_time_coefficient C m hm clip hclip
  have hd0 s : 0 ≤ rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet :=
    rawWeightedGradientEnergy_nonneg _ _ (hq0 s) _
  have hf0 s : 0 ≤ rawWeightedFactorialEnergy (r / L) (q s) (F i s).toFunction.jet :=
    rawWeightedFactorialEnergy_nonneg _ _ (hq0 s) _
  have hdi := rawWeightedGradient_time_integrable C m hm clip hclip (r / L) _
    (w i) (hsln.2.1 i)
  have hfi := rawWeightedFlux_time_integrable C m hm clip hclip (r / L) _ (F i) (hF i)
  have hdlim := ofReal_intervalIntegral_nonneg hab _ hdi hd0
  have hflim := ofReal_intervalIntegral_nonneg hab _ hfi hf0
  have heq s := storedChartFactorialEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  have hdeq s := storedChartGradientEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  have hfeq s := storedChartFluxEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  intro t ht
  have hh' := retained_factorial_energy_to_ennreal
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) (u i t).toFunction.jet)
    (intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0))
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) (f i).toFunction.jet)
    (intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hf0)) (hh t ht)
  rw [hdlim, hflim] at hh'
  have hdEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hdeq s (w i s))
  have hfEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hfeq s (F i s))
  change storedChartFactorialEnergy (r / L) (q t) (u i t) +
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
    ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
      (storedChartFactorialEnergy (r / L) (q a) (f i) +
        16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s))
  rw [heq t (u i t), heq a (f i), hdEq, hfEq]
  exact hh' 

end AVRegularity.Weighted
end
