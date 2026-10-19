-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellComplexH1Separability
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
import AVRegularity.CycleDamping.ReferenceTimeEquation
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainFrom_finite_polynomial_energy (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (Kmax : ℕ) (hκ : ∀ j x, κ j x ≤ Kmax)
    (hKJ : ∀ (j : Fin N) x, κ j.succ x ≤ J) (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S) (m : ℕ)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hf : ∀ j x, weightedFactorialNormSq (wordMomentSlot m (fun j => (letters j).slow) j)
      ϖ 0 r (κ j x) (f (j, x)) ≠ ⊤) :
    ∀ j x,
      ((⨆ t ∈ Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (κ j x) (U (j, x) t)) +
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (κ j x) (Uw (j, x) t))) ≠ ⊤ := by
  classical
  obtain ⟨Mv, hMv⟩ := hv.2.1
  have hvm : ∀ t k, Measurable (fun x => v t x k) := fun t k =>
    (measurable_pi_apply k).comp (hv.1.comp (measurable_const.prodMk measurable_id))
  have hvb : ∀ t k x, ‖v t x k‖ ≤ |Mv| := by
    intro t k x
    simpa only [Real.norm_eq_abs] using CycleEvolution.cellDrift_entry_bound hMv t x k
  have hcomponent (j : Fin (N + 1)) (x : ι)
      (V : ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
      (hVt : MemLp V 2 (volume.restrict (Icc a b)))
      (hVe : (∫⁻ t in Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (κ j x) (V t)) ≠ ⊤)
      (hV : ∀ᵐ t ∂volume.restrict (Icc a b), planeValue (V t) =ᵐ[volume]
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) (j, x) t) := by
    have hs := wordChain_scalar_component_redistribution hD G letters X0 δ κ a b v hvm
      |Mv| hvb f U Uw hsol (j, x) V hV
    have hs2 := geometryScalarSolution_order_two (h := fun _ : Unit => h x) D hD
      (fun t _ => G t) (fun _ _ => κ j x) a b v
      (fun _ _ => f (j, x)) (fun _ _ => V) (fun _ _ => U (j, x))
      (fun _ _ => Uw (j, x)) hs
    exact constantMetric_scalar_component_energy_ne_top a b hab (κ j x) Kmax
      (wordMomentSlot m (fun j => (letters j).slow) j) (hκ j x) v hv hvs
      strain r ha hr hrh hsmall hjets G hG tw S ϖ 0 Cw (W _) hwa hwb
      (f (j, x)) V hVt (U (j, x)) (Uw (j, x)) hs2 (hf j x) hVe
  intro j
  induction j using Fin.induction with
  | zero =>
    intro x
    refine hcomponent 0 x (fun _ => 0) ?_ ?_ ?_
    · exact planeHk_zero_time_memLp (E := PiLp 2 (fun _ : Fin 2 => h x))
        (κ 0 x) (volume.restrict (Icc a b))
    · change (∫⁻ t in Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) 0) ϖ 0 r (κ 0 x)
        (0 : PlaneHk Set.univ (κ 0 x) (PiLp 2 (fun _ : Fin 2 => h x)))) ≠ ⊤
      simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · apply Filter.Eventually.of_forall
      intro t
      rw [wordChainPreviousFlux_zero]
      exact planeValue_zero_ae _
  | succ j ih =>
    intro x
    have he u : (∫⁻ t in Icc a b, weightedGradFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j.succ + (letters j).slow)
        ϖ 0 r (κ j.castSucc u) (Uw (j.castSucc, u) t)) ≠ ⊤ := by
      rw [← wordMomentSlot_castSucc]
      exact (ENNReal.add_ne_top.mp (ih u)).2
    obtain ⟨V, hVt, hVe, hVr⟩ := exists_admissible_letter_flux_time π hπ (letters j)
      a b J H (hL j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
      (j.succ, x) (fun u => (j.castSucc, u)) x (hKJ j x)
      (if (letters j).positive then 1 else 0)
      (wordMomentSlot m (fun j => (letters j).slow) j.succ) X0 δ (hm j x)
      ϖ hϖ r hr (fun u => Uw (j.castSucc, u)) (fun u => hsol.2.1 (j.castSucc, u)) he
    apply hcomponent j.succ x V hVt hVe
    filter_upwards [hVr] with t ht
    rw [planeValue_eq_stored]
    refine (planeJetReadout_ae_raw (V t) (valueIndex2 (κ j.succ x))).symm.trans ?_
    have heq : wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) (j.succ, x) t =
        letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
          (j.succ, x) (fun u => (j.castSucc, u)) x
          (if (letters j).positive then 1 else 0) X0 δ (fun u => Uw (j.castSucc, u) t) t :=
      funext (fun z => wordChainPreviousFlux_succ letters X0 δ κ _ j x t z)
    rw [heq]
    exact ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual normalization converts the reversed graph phase to the forward scalar symbol. -/

theorem canonicalRow_normalization_phase (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
    Complex.exp (∫ t in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t) *
      fibreSeriesC k ξ a = fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b a *
        fibreSeriesC k ξ b := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let Dr := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let d := fun t => cellComplexPair (cellRawTrace D t + cellConstantCLM 1)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellRawTrace Dr (-t) + cellConstantCLM 1))
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hξ, hrad]
  have hg := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξR hab
  have hq := fibreAdjointGraph_backward_homogeneous η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξR hab
  have hc := cellWeakAdjointPairing hab
    ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv hb hg hq
  dsimp only at hc
  simp only [cellComplexPair_scalar_left, cellFiberConj_scalar,
    cellComplexPair_scalar_right, star_star, fibreAdjointGraphPhase,
    intervalIntegral.integral_same, Complex.exp_zero, one_mul] at hc
  have hn (t : ℝ) : fibreSeriesC k ξ t * d t = 1 := by
    have hh := fibreAdjointRow_pairing_normalization η Cw hη hCw G hG hv hw ξ hξ t
    have hs := fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hξ t
    dsimp only at hh
    rw [hs] at hh
    simpa only [cellFiberConj_scalar, cellComplexPair_scalar_right, star_star] using hh
  exact complex_normalization_transport (fibreSeriesC k ξ a) (fibreSeriesC k ξ b)
    (d a) (d b) _ _ (hn a) (hn b) hc

/-! The actual normalization converts the reversed graph phase to the forward scalar symbol. -/

theorem canonicalAdjoint_row_phase_class (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    cellScalarCLM (Complex.exp (∫ t in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t))
      (cellSourceSlice ell a) =
      cellScalarCLM (fibreSeriesC k ξ b)
        (cellScalarCLM (fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b a)
          (cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-a) + cellConstantCLM 1)) := by
  dsimp only
  rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hξ a]
  simp only [cellScalarCLM_smul, smul_smul]
  rw [canonicalRow_normalization_phase η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξ hab]
  congr 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Any positive short full-equation window produces one smooth periodic endpoint representative. -/

theorem interiorPulseReflectedActualWeak_positive_short_window_smooth
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1)
    : ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  apply torusHigher_all_order_smooth_representative (U b)
  intro J
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let δ₀ := constructedNativeSmoothingTime J R k Cw η
  have hδ₀ := constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw
  have hA : 0 ≤ constructedNativeWindowPrice J R k Cw * peFactor η ^ 2 :=
    mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR
      ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  obtain ⟨hδ, hbudget, hfit⟩ := shortSmoothingStep_budget J δ₀ (b - a)
    (constructedNativeWindowPrice J R k Cw * peFactor η ^ 2) hδ₀ (sub_pos.mpr hab) hA
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
  obtain ⟨W, hw, _⟩ := interiorPulseReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU
    hinitial hwindow (min δ₀ ((b - a) / ((J : ℝ) + 1))) hδ hbudget hfit
  exact ⟨W, hw⟩

/-! Every positive full-equation interval has a smooth periodic endpoint representative. -/

theorem interiorPulseReflectedActualWeak_positive_window_smooth
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  by_cases hshort : b - a ≤ 1
  · exact interiorPulseReflectedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU hinitial hshort
  · have ha : a ≤ b - 1 := by linarith only [hshort]
    have hsub : Icc (b - 1) b ⊆ Icc a b := Icc_subset_Icc ha le_rfl
    exact interiorPulseReflectedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ (by linarith : b - 1 < b)
      (U (b - 1)) U slice (hU.mono hsub) rfl (by ring_nf; exact le_rfl)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The exact quiet constant mode is a genuine homogeneous fibre trajectory. -/

theorem cellQuiet_constant_mode_dual (η Cw : ℝ) (hη : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hreal : ∀ j, (ξ j).im = 0)
    (t : ℝ) (hquiet : ∀ x, v t x = 0) :
    cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
      hG V hv.1 hb t cellH1One 0 0 =
      cellPivotDualCLM (cellConstantCLM (-(η : ℂ) * fibreQuad (G t) ξ)) := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair
      (cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
        hG V hv.1 hb t cellH1One 0 0) z =
      cellDualComplexPair (cellPivotDualCLM
        (cellConstantCLM (-(η : ℂ) * fibreQuad (G t) ξ))) z := by
    rw [show (0 : Fin 2 → ComplexCellL2) = (fun _ => 0) from rfl,
      cellDualComplexPair_actual, cellComplexSource_zero, add_zero,
      cellComplexGenerator_quiet_symmetry hG hv V hb _ (fibreBloch_real_star η ξ hreal)
        t hquiet, cellBlochLinear_generator_one G hG hv V hb,
      cellBlochLinearSourceClass_mean η Cw hη hCw G hv hw V hb ξ t z,
      cellBlochDriftMean_at_quiet_time η Cw hCw hv hw ξ t hquiet]
    rw [cellPivotDual_complex_pair, ← cellScalarCLM_constant_one,
      cellComplexPair_scalar_left, cellComplexPair_symm (cellConstantCLM 1), cellComplexPair_one]
    simp only [mul_zero, zero_sub, star_neg, star_mul]
    rw [fibreQuad_real_star (G t) ξ hreal]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The actual word component has the backward Bloch formula with only an L2 preceding-letter flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainCoordinateNative_duhamel (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (S : ℝ → PlaneFluxL2 (h i.2)) (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
      fun x => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
    (e : h i.2) (g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    let B := planeBlochBackwardRealField hab G hG v hv M hb g
    inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b))) g =
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i)))
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) B (-a))) -
      ∫ r in a..b, inner ℝ (planeFluxFiberCoordinateCLM e (S r))
        (planeH1GradientOperator (cellEnergyPlaneRealH1State (neg_le_neg hab) B (-r))) := by
  obtain ⟨C, hCpos, hC⟩ := cellDriftTorusSymbol_bound v hv
  obtain ⟨C', hC'pos, hC'⟩ := cellDriftTorusSymbol_bound _ (cellDrift_neg hv)
  obtain ⟨Cr, hCrpos, hCr⟩ := cellDriftTorusSymbol_bound _ (cellDrift_timeReverse hv)
  have hc := wordChainCoordinateNative_weakCurve hD G hG letters X0 δ κ a b hab v hv
    C hCpos hC f U Uw hsol i S hSl hS e
  have he := planeBlochDuhamel_pair hab G hG v hv M hb C hCpos hC C' hC'pos hC'
    Cr hCrpos hCr (fun r => planeFiberCoordinateCLM e (coupledPlaneL2Trace U i r))
    (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r))
    (fun r => planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r))) hc g
  have hi : planeFiberCoordinateCLM e (coupledPlaneL2Trace U i a) =
      planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i)) := by
    change planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i a)) = _
    have hi0 : U i a = f i := hsol.2.2.2.1 i
    exact congrArg (fun q => planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) q)) hi0
  change planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i a)) = _ at hi
  simp only [planeSourceDual_pair, inner_zero_left, zero_sub,
    intervalIntegral.integral_neg, coupledPlaneL2Trace] at he
  rw [hi] at he
  linarith only [he]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

section
open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainFrom_compact_polynomial_energy (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (Kmax : ℕ) (hκ : ∀ j x, κ j x ≤ Kmax)
    (hKJ : ∀ (j : Fin N) x, κ j.succ x ≤ J) (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S) (m : ℕ)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (A : (Fin (N + 1) × ι) → Set (Vec 2))
    (hA : ∀ p, IsCompact (A p))
    (hfs : ∀ p, ∀ᵐ z ∂volume, z ∉ A p → planeValue (f p) z = 0) :
    ∀ j x,
      ((⨆ t ∈ Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (κ j x) (U (j, x) t)) +
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (κ j x) (Uw (j, x) t))) ≠ ⊤ := by
  apply wordChainFrom_finite_polynomial_energy hD π hπ letters J H a b hab hL κ Kmax hκ
    hKJ X0 δ hm v hv hvs strain r ϖ ha hr hϖ hrh hsmall hjets G hG tw S Cw W hwa hwb
    m f U Uw hsol
  intro j x
  apply weightedFactorialNormSq_compact_value_ne_top _ _ _ _ (f (j, x)) (hA (j, x))
  have he : (f (j, x)).toFunction.jet (valueIndex2 (κ j x)) = planeValue (f (j, x)) :=
    (planeValue_eq_stored (f (j, x))).symm
  rw [he]
  exact hfs (j, x)
end

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

section
open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainFrom_capped_finite_polynomial_energy (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (hd : ∀ j, (letters j).order = d j) (hreserve : (K + ∑ j, d j) ≤ J)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ (K + ∑ j, d j) → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S) (m : ℕ)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hf : ∀ j x, weightedFactorialNormSq
      (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r
      (cappedWordSlots κ K d j x)
      (truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (f (j, x))) ≠ ⊤) :
    ∀ j x,
      ((⨆ t ∈ Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (cappedWordSlots κ K d j x)
        (truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (U (j, x) t))) +
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (cappedWordSlots κ K d j x)
        (truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ K d j x))
          (Uw (j, x) t)))) ≠ ⊤ := by
  have hcap := wordChainFrom_capped hD G letters κ K d hL hd hc X0 δ a b v
    (fun j x => f (j, x)) (fun _ _ _ => 0)
    (fun j x => U (j, x)) (fun j x => Uw (j, x)) hsol
  have hs : IsPlaneChainFrom (wordChainData G letters X0 δ) (cappedWordSlots κ K d) a b v
      (fun j x => truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (f (j, x)))
      (fun _ _ _ => 0)
      (fun j x t => truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (U (j, x) t))
      (fun j x t => truncatePlaneHk (Nat.succ_le_succ
        (cappedWordSlots_le_original κ K d j x)) (Uw (j, x) t)) := by
    simpa only [map_zero] using hcap
  apply wordChainFrom_finite_polynomial_energy hD π hπ letters J H a b hab hL
    (cappedWordSlots κ K d) (K + ∑ j, d j) (cappedWordSlots_le_fixed κ K d)
    (fun j x => (cappedWordSlots_le_fixed κ K d j.succ x).trans hreserve)
    X0 δ hm v hv hvs strain r ϖ ha hr hϖ hrh hsmall hjets G hG tw S Cw W hwa hwb m
    (fun p => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2) (f p))
    (fun p t => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2) (U p t))
    (fun p t => truncatePlaneHk (Nat.succ_le_succ
      (cappedWordSlots_le_original κ K d p.1 p.2)) (Uw p t)) hs hf
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual full adjoint fast subtraction has the sharp molecular gap. -/

theorem canonicalAdjoint_fast_remainder_decay (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
 :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
    let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ b
    let c := k * cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
    let phase := fun τ => Complex.exp (∫ s in -b..τ,
      fibreAdjointGraphSymbol η Cw hη G hG hv hw ξ s)
    let w := fun τ => U τ - cellScalarCLM c (cellScalarCLM (phase τ)
      (cellRawTrace D τ + cellConstantCLM 1))
    ∀ τ ∈ Icc (-b) (-a), ‖w τ‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (τ + b)) * ‖w (-b)‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ b
  let c := k * cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
    (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
  let phase := fun τ => Complex.exp (∫ s in -b..τ,
    fibreAdjointGraphSymbol η Cw hη G hG hv hw ξ s)
  let w := fun τ => U τ - cellScalarCLM c (cellScalarCLM (phase τ)
    (cellRawTrace D τ + cellConstantCLM 1))
  let ws := fun τ => slice τ - cellH1Scalar c (cellH1Scalar (phase τ)
    (cellH1Slice D τ + cellH1One))
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hξ, hrad]
  have h16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by
    linarith only [hξ, hrad]
  have he := canonicalAdjoint_mode_subtraction_weak η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hR hab U slice hU c
  have hk := canonicalAdjoint_initial_kernel η Cw hη hCw G hG hv hw ξ h16 (U (-b)) b
  have hker : cellComplexPair (w (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) = 0 := by
    simpa only [w, phase, intervalIntegral.integral_same, Complex.exp_zero,
      cellScalarCLM_smul, one_smul] using hk
  exact canonicalAdjoint_graph_kernel_decay η Cw hη0 hη hCw G hG hv hm hw V hb hg hgsmall
    ξ hξ hfreq hab w ws he hker

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual graph evolution is available before the scalar package is assembled. -/

variable {η ξ₀ Cg Cw : ℝ}
  {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
  (hgraph : IsFibreGraph η G v ξ₀ Cg r lam)
  (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
  (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
  (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
  (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
  (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
  (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀)

include hgraph hη0 hη hCw hm hw hξ in
theorem fibreGraph_actual_weak_evolution {a b : ℝ} (hab : a ≤ b) :
    CellWeakHilbertCurve a b
      (fun t => cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1)
      (fun t => cellH1Slice (fibreSeriesJet r ξ) t + cellH1One)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j,
          fun s => -fibreSeriesC lam ξ s⟩ hG V hv.1 hb t
        (cellH1Slice (fibreSeriesJet r ξ) t + cellH1One) 0 0) := by
  let D := fibreSeriesJet r ξ
  have hd := hgraph.2.1 ξ hξ
  obtain ⟨_, _, _, htr, _, he⟩ := cellFibreGraph_native_equation
    η Cw hη hCw G hG hv hw V hb ξ D hd.2.2.1
  have hh := he a b hab
  apply hh.add_one.dual_congr
  filter_upwards [hh.agrees] with t ht
  have hsrc : cellFibreGraphSourceClass η Cw hCw hv hw ξ t (cellRawTrace D t) =
      cellNormalizedGraphSourceClass G v V hv hb
        (fun j => (Real.sqrt η : ℂ) * ξ j) (fun s => -fibreSeriesC lam ξ s) t
        (cellH1Slice D t) := by
    apply Lp.ext
    have hraw := cellFibreGraphSourceClass_ae η Cw hCw hv hw ξ t
      (cellRawTrace D t) (cellValue D) (htr t)
    have hnorm := cellNormalizedGraphSourceClass_bloch_ae η hη0 G hv V hb ξ
      (fibreSeriesC lam ξ) t (cellH1Slice D t)
    have hval : (torusHkValueCLM (cellH1Slice D t) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] cellValue D t := by
      rw [← ht]
      exact htr t
    filter_upwards [hraw, hnorm, hval] with x hr hn hx
    rw [hr, hn, hx]
    exact fibreGraph_normalized_source_identity η Cw ξ₀ Cg G hv hm hw
      r lam hgraph ξ hξ t x
  have hflux : cellFibreGraphFluxClass η G ξ t (cellRawTrace D t) =
      cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t (cellH1Slice D t) := by
    funext j
    unfold cellFibreGraphFluxClass cellNormalizedGraphFluxClass
    rw [← ht]
    have hs : (∑ k : Fin 2, (G t j k : ℂ) * ((Real.sqrt η : ℂ) * ξ k)) =
        (Real.sqrt η : ℂ) * ∑ k : Fin 2, (G t j k : ℂ) * ξ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs]
    congr 2
    ring
  change cellDualDerivative _ hG V hv.1 hb t (cellH1Slice D t) _ _ = _
  rw [hsrc, hflux]
  exact (cellNormalizedGraph_dual G hG hv V hb _ _ t (cellH1Slice D t)).symm

include hgraph hη0 hη hCw hG hv hw hξ in
theorem fibreGraph_symbol_memLp_top (hCg : 0 ≤ Cg) (a b : ℝ) :
    MemLp (fibreSeriesC lam ξ) ⊤ (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound
    ((CycleDamping.graph_symbol_aestronglyMeasurable hG hv hgraph ξ hξ).mono_measure
      Measure.restrict_le_self) ((8 + Cw * Cg) * fibreNorm ξ ^ 2)
  exact Filter.Eventually.of_forall (fun t =>
    fibreGraph_symbol_quadratic_bound hgraph hη0 hη hCg hCw hG hv hw ξ hξ t)

include hgraph hη0 hη hCw hm hw hξ in
theorem fibreGraph_actual_homogeneous_evolution (hCg : 0 ≤ Cg)
    {a b : ℝ} (hab : a ≤ b) :
    let phase := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC lam ξ τ)
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (phase t) (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1))
      (fun t => cellH1Scalar (phase t) (cellH1Slice (fibreSeriesJet r ξ) t + cellH1One))
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
        hG V hv.1 hb t
        (cellH1Scalar (phase t) (cellH1Slice (fibreSeriesJet r ξ) t + cellH1One)) 0 0) := by
  have hh := fibreGraph_actual_weak_evolution hgraph hη0 hη hCw hG hv hm hw V hb ξ hξ hab
  have hl := fibreGraph_symbol_memLp_top hgraph hη0 hη hCw hG hv hw ξ hξ hCg a b
  exact hh.remove_potential hab (fun t _ => G t) hG v V hv.1 hb _ _ hl

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Future-buffer comparison for the actual reversed canonical graphs. -/

theorem canonicalAdjointGraph_buffered_norm_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t) :
    let D := fibreAdjointGraphRaw η Cw hη G hG hv hsv ξ
    let E := fibreAdjointGraphRaw η Cw hη G hG hw hsw ξ
    ∀ t ∈ Icc (lo - buffer) hi, ‖cellRawTrace D (-t) - cellRawTrace E (-t)‖ ≤
      Real.exp (-(Real.pi ^ 2 / 4) * buffer) * (2 * fibreWordCorrectionBound Cw * fibreNorm ξ) := by
  have hgrev : IsMetricNearIdentity (fun t _ => G (-t)) g := fun t x z => hg (-t) x z
  have hbvr (t : ℝ) (x : Vec 2) : ∑ i, (-v (-t) x) i ^ 2 ≤ V ^ 2 := by
    simpa only [Pi.neg_apply, neg_sq] using hbv (-t) x
  have hbwr (t : ℝ) (x : Vec 2) : ∑ i, (-w (-t) x) i ^ 2 ≤ V ^ 2 := by
    simpa only [Pi.neg_apply, neg_sq] using hbw (-t) x
  have hagree : ∀ t ∈ Icc (-hi - buffer) (-lo + buffer),
      (fun x => -w (-t) x) = (fun x => -v (-t) x) := by
    intro t ht
    have hti : -t ∈ Icc (lo - buffer) (hi + buffer) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hvw (-t) hti]
  have hnξ : fibreNorm (fun j => -ξ j) ≤ fibreWordRadius Cw := by
    rwa [fibreNorm_neg]
  have he := canonicalGraph_buffered_norm_difference_bound η Cw hη0 hη hCw
    (fun t => G (-t)) (cellMetric_timeReverse hG) hgrev hgsmall
    (fun t x => -v (-t) x) (fun t x => -w (-t) x)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse hw)
    (cellDrift_timeReverse_mean_zero hmv) (cellDrift_timeReverse_mean_zero hmw)
    (cellDrift_timeReverse_scaled_bound hsv) (cellDrift_timeReverse_scaled_bound hsw)
    V hbvr hbwr (fun j => -ξ j) hnξ (-hi) (-lo) buffer
    (by linarith) hbuffer hagree
  dsimp only
  intro t ht
  have hti : -t ∈ Icc (-hi) (-lo + buffer) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [fibreAdjointGraphRaw, fibreNorm_neg] using he (-t) hti

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Subtracting the actual slow graph trajectory leaves a solution of the full homogeneous equation. -/

theorem fibreGraph_actual_fast_weak_evolution
    {η ξ₀ Cg Cw : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ Cg) (hCw : 0 ≤ Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀)
    {a b : ℝ} (hab : a ≤ b) (c : ℂ)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    let phase := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC lam ξ τ)
    let R := fun t => cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
    let Rs := fun t => cellH1Slice (fibreSeriesJet r ξ) t + cellH1One
    CellWeakHilbertCurve a b
      (fun t => U t - cellScalarCLM c (cellScalarCLM (phase t) (R t)))
      (fun t => slice t - cellH1Scalar c (cellH1Scalar (phase t) (Rs t)))
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
        hG V hv.1 hb t (slice t - cellH1Scalar c (cellH1Scalar (phase t) (Rs t))) 0 0) := by
  have hR := fibreGraph_actual_homogeneous_evolution hgraph hη0 hη hCw hG hv hm hw V hb ξ hξ hCg hab
  have hc := hR.homogeneous_complex_scalar (fun t _ => G t) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) c
  exact cellWeakActual_sub_same_source
    ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb
    0 0 _ _ _ _ hU hc

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual normalized graph has a uniform cell L2 budget from its original energy bound. -/

theorem fibreGraph_normalized_mode_norm_le {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (hCg : 0 ≤ Cg)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀) (t : ℝ) :
    ‖cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1‖ ≤ 1 + Cg * fibreNorm ξ := by
  have hg := hgraph.2.1 ξ hξ
  have he : (cellEnergyNorm univ (fibreSeriesJet r ξ)).toReal ≤ Cg * fibreNorm ξ := by
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (Cg * fibreNorm ξ) ≠ ⊤) hg.2.2.2.2
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hCg (fibreNorm_nonneg ξ))] using hh
  exact (cellInverse_normalized_mode_upper hg.2.2.1 t).trans (add_le_add le_rfl he)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal BigOperators
namespace AVRegularity.CycleWords

/-! Native graph coefficients with the package's genuine energy majorant. -/

variable {η ξ₀ Cg : ℝ}
  {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}

theorem fibreGraphCoefficient_memLp
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀)
    (p : ℕ × ℕ) (s : ℝ) :
    MemLp (cellValue (r p) s) 2 (volume.restrict AVenhance.unitCube) := by
  let ξ : Fin 2 → ℂ := fun _ => ((R : ℝ) : ℂ)
  have hm : fibreMonomial ξ p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (show (R : ℝ) ≠ 0 from (show (0 : ℝ) < R from hR).ne')))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (show (R : ℝ) ≠ 0 from (show (0 : ℝ) < R from hR).ne')))
  have hp : ENNReal.ofReal ‖fibreMonomial ξ p‖ *
      cellEnergyNorm Set.univ (r p) < ⊤ :=
    (ENNReal.le_tsum (f := fun q => ENNReal.ofReal ‖fibreMonomial ξ q‖ *
      cellEnergyNorm Set.univ (r q)) p).trans_lt (hgraph.2.1 ξ hband).1
  have hn : ENNReal.ofReal ‖fibreMonomial ξ p‖ ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hm)).ne'
  have he := ENNReal.lt_top_of_mul_ne_top_right hp.ne hn
  exact (cellValue_cellL2Norm_le_energy (r p) s).trans_lt he

def fibreGraphCoefficientClass
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀)
    (p : ℕ × ℕ) (s : ℝ) : ComplexCellL2 :=
  (fibreGraphCoefficient_memLp hgraph R hR hband p s).toLp
    (cellValue (r p) s)

theorem fibreGraphCoefficientClass_ae
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀)
    (p : ℕ × ℕ) (s : ℝ) :
    fibreGraphCoefficientClass hgraph R hR hband p s
      =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) s :=
  (fibreGraphCoefficient_memLp hgraph R hR hband p s).coeFn_toLp

theorem fibreGraphCoefficientClass_majorant
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀) :
    (∑' p, fibreCoefficientWeight (R : ENNReal) p *
      ⨆ s, ‖fibreGraphCoefficientClass hgraph R hR hband p s‖ₑ) < ⊤ := by
  have hm (p : ℕ × ℕ) :
      ENNReal.ofReal ‖fibreMonomial (fun _ : Fin 2 => ((R : ℝ) : ℂ)) p‖ =
        fibreCoefficientWeight (R : ENNReal) p := by
    simp only [fibreMonomial, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg, ← pow_add,
      fibreCoefficientWeight, ENNReal.ofReal_pow R.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
  have hs := (hgraph.2.1 (fun _ : Fin 2 => ((R : ℝ) : ℂ)) hband).1
  simp only [hm] at hs
  apply lt_of_le_of_lt _ hs
  apply ENNReal.tsum_le_tsum
  intro p
  apply mul_le_mul' le_rfl
  apply iSup_le
  intro s
  rw [fibreGraphCoefficientClass, Lp.enorm_toLp]
  exact cellValue_cellL2Norm_le_energy (r p) s

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Stability of the actual normalized canonical rows in their forward and reversed graphs. -/

theorem canonicalRow_difference_bound (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw) (t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    let A := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hsv ξ) (-t)
    let B := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hw hsw ξ) (-t)
    ‖cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hsv) ξ) t -
      cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hw hsw) ξ) t‖ ≤
      10 * ‖A - B‖ + 8 * ‖B‖ * ‖cellRawTrace D t - cellRawTrace E t‖ := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hr := hξ.trans (fibreWordRadius_le_graph Cw)
  have hrsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024 :=
    hr.trans (min_le_left _ _)
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by
    linarith only [hrsmall, hR]
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    linarith only [hrsmall, hR]
  have hsmall := (fibreWord_frequency_small hCw ξ hξ).2.1
  have hρ : ‖cellRawTrace
      (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ) t‖ ≤ 1 :=
    (fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hsv ξ hξR t).trans
      hsmall
  have hnξ : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rwa [fibreNorm_neg]
  have hB : ‖cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hw hsw ξ) (-t)‖ ≤ 1 := by
    have he := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw
      (fun s => G (-s)) (cellMetric_timeReverse hG) (cellDrift_timeReverse hw)
      (cellDrift_timeReverse_scaled_bound hsw) (fun j => -ξ j) hnξ (-t)
    rw [fibreNorm_neg] at he
    exact he.trans hsmall
  dsimp only
  rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hsv ξ hξ16 t,
    fibreAdjointRow_source_slice η Cw hη hCw G hG hw hsw ξ hξ16 t]
  exact cellNormalizedRow_difference_bound _ _ _ _ _ _
    (canonicalRow_overlap_normalization η Cw hη hCw G hG hv hsv ξ hξ16 t)
    (canonicalRow_overlap_normalization η Cw hη hCw G hG hw hsw ξ hξ16 t)
    (fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hv hsv ξ hξ16 t)
    (fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hw hsw ξ hξ16 t) hρ hB

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal BigOperators
namespace AVRegularity.CycleWords

/-! The scalar package graph equals its convergent native L2 power series. -/

variable {η ξ₀ Cg : ℝ}
  {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}

theorem fibreGraphTrace_eq_nativeSeries
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀) (hξR : ‖ξ‖ ≤ R) (s : ℝ) :
    cellRawTrace (fibreSeriesJet r ξ) s =
      ∑' p, fibreMonomial ξ p • fibreGraphCoefficientClass hgraph R hR hband p s := by
  let c := fun p => fibreGraphCoefficientClass hgraph R hR hband p s
  have hw := fibreUniformMajorant_weighted_summable
    (fibreGraphCoefficientClass hgraph R hR hband) R
    (fibreGraphCoefficientClass_majorant hgraph R hR hband) s
  have hn : Summable (fun p => ‖fibreMonomial ξ p • c p‖) := by
    apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ hw
    intro p
    rw [norm_smul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (fibreMonomial_norm_le_pi ξ p).trans
      (pow_le_pow_left₀ (norm_nonneg _) hξR _)
  have he : (∑' p, ‖fibreMonomial ξ p • c p‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hn
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ p,
      (fibreMonomial ξ p • c p) x = fibreMonomial ξ p * cellValue (r p) s x := by
    apply ae_all_iff.mpr
    intro p
    filter_upwards [Lp.coeFn_smul (fibreMonomial ξ p) (c p),
      fibreGraphCoefficientClass_ae hgraph R hR hband p s] with x hx hc
    change c p x = cellValue (r p) s x at hc
    simpa only [Pi.smul_apply, smul_eq_mul, hc] using hx
  apply Lp.ext
  filter_upwards [cellRawTrace_ae (fibreSeriesJet r ξ) s
      (((hgraph.2.1 ξ hξ).2.2.1).1.2.2.1 s (Set.mem_univ s)).1,
    Lp.coeFn_tsum he, hall] with x hr ht hc
  exact hr.trans (ht.trans (tsum_congr (fun p => hc p))).symm

theorem fibreGraphNativeSeries_analyticOnNhd
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀) (s : ℝ) :
    AnalyticOnNhd ℂ
      (fun ξ => ∑' p, fibreMonomial ξ p •
        fibreGraphCoefficientClass hgraph R hR hband p s)
      (Metric.ball 0 (R : ℝ)) :=
  fibreUniformMajorant_analyticOnNhd
    (fibreGraphCoefficientClass hgraph R hR hband) R hR
    (fibreGraphCoefficientClass_majorant hgraph R hR hband) s

end AVRegularity.CycleWords
end
