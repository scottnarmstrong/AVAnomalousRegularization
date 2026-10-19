-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellTransverseGalerkinCorrectionLocalGrowthEnergy
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual reconstructed plane trace is continuous, initially exact, and contractive. -/

def planeBlochEnergyReconstructedTrace {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) (t : CellCompactTime a b) :
    Lp ℂ 2 (volume : Measure (Vec 2)) :=
  (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
    ((cellEnergyTraceAtCLM a b t).compLp
      (planeBlochEnergyField hab G hG v V hv hb
        (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)))

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_words_clipped_source_spatial_budgets
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
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
    ∀ᵐ t ∂volume.restrict (Icc a b),
      ((∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
        (∫ x, q t x * (‖R α t x‖ * ‖planeJetReadoutOperator (κ i.1 i.2) α (u i t) x‖))) ≤
        (ν / 4) * d t) ∧
      ((∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
        (∫ x, q t x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α t k x) :
          PiLp 2 (fun _ : Fin 2 => h i.2))‖ ^ 2)) ≤
        2 * ((metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 * d t) +
          2 * fenergy t) := by
  dsimp only
  have hpoint := hsln.2.2.1 i
  have hbud := hpoint.and (ae_restrict_mem measurableSet_Icc)
  exact hbud.mono (fun t ht =>
    scalarSobolevSource_word_spatial_budget (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) g hg4 hGnear hGs (w i) (F i) t ht.2 hG1 (u i t) ht.1.symm
      ρ (fun x => clipWeight clip (C.W m t x)) hρ ν hν ha hB hlam hV hsmall hstrainSmall
      δ hδ hg hscale CG
      (metricEntryEnvelope_bound (hκ i) G CG g δ hg hδ hg4 hGnear hGs hmetricJets t ht.2)
      (fun l hl hlK x k j => hmetricJets t ht.2 x l hl (hlK.trans (hκ i)) k j)
      ((chartWeights_clipped_time_coefficient C m hm clip hclip).1 t)
      (fun x => (clipWeight_pos hclip (C.pos m hm t x)).le) clip
      (fun x => clipWeight_le_bound hclip (C.pos m hm t x)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Finite correction mass and first gradient bounds depend only on its initial L2 correction. -/

theorem cellTransverseGalerkin_correction_local_bounds
    (N : ℕ) (a b η : ℝ) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (hsmall : ∀ t ∈ Icc a b,
      264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * ‖κ t‖ + 1 ≤ 2)
    (L : ℝ) (hL : 0 ≤ L)
    (hκq : ∀ t ∈ Icc a b, ‖κ t‖ ≤ L * fibreNorm ξ ^ 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hwsmall : Cw * fibreNorm ξ ≤ 1)
    (initial : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
      0 initial a b (AVenhance.Infra.ODE.extendCurve hab y))
    (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) :
    let Y := AVenhance.Infra.ODE.extendCurve hab y
    let z := fun t => Y t - cellGalerkinConstant N 1
    let B := ‖cellGalerkinValue N (z c)‖ ^ 2 + (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 / 2
    (‖cellGalerkinValue N (z d)‖ ^ 2 ≤ Real.exp (4 * (d - c)) * B) ∧
      (∫ t in c..d, ∑ j, ‖cellDerivativeCLM j (z t).val‖ ^ 2) ≤
        (4 / 3) * Real.exp (4 * (d - c)) * B := by
  let Y := AVenhance.Infra.ODE.extendCurve hab y
  let z := fun t => Y t - cellGalerkinConstant N 1
  have hz : Continuous (fun t => (z t).val) :=
    ((cellGalerkinState (E := ℂ) N).continuous.comp
      (AVenhance.Infra.ODE.continuous_extendCurve hab y)).sub continuous_const
  have hg : Continuous (fun t => ∑ j : Fin 2, ‖cellDerivativeCLM j (z t).val‖ ^ 2) := by
    apply continuous_finsetSum
    intro j _
    exact ((cellDerivativeCLM j).continuous.comp hz).norm.pow 2
  have he := cellTransverseGalerkin_correction_local_growth_energy N a b η hab hη0 hη G hG hv ξ
    hc A hA hb κ Cw hCw hw hκm k hκ hsmall L hL hκq hξ1 hwsmall initial y hy c d hcd hsub
  have hh := negativeWeighted_energy_bounds c d (‖cellGalerkinValue N (z d)‖ ^ 2)
    (‖cellGalerkinValue N (z c)‖ ^ 2) (2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2) hcd
    (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
    _ hg.continuousOn (fun t _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) he
  have hB : ‖cellGalerkinValue N (z c)‖ ^ 2 +
      2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 / 4 =
      ‖cellGalerkinValue N (z c)‖ ^ 2 + (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 / 2 := by ring
  exact ⟨hh.1.trans_eq (congrArg (fun B : ℝ => Real.exp (4 * (d - c)) * B) hB),
    hh.2.trans_eq (congrArg (fun B : ℝ => (4 / 3) * Real.exp (4 * (d - c)) * B) hB)⟩

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Genuine fibre increments with the actual jointly measurable H1 state. -/

theorem planeBlochEnergyJointIncrement {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    let F := planeBlochEnergyField hab G hG v V hv hb f
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, ∀ s t : CellCompactTime a b, s.val ≤ t.val →
      ∀ test : CellComplexH1,
        inner ℝ ((F θ).val.1 t) (cellComplexH1ValueCLM test) -
          inner ℝ ((F θ).val.1 s) (cellComplexH1ValueCLM test) =
            ∫ r in s.val..t.val, cellGeneratorForm
              ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb r
                (cellComplexH1RealEquiv (cellEnergyJointH1 hab F (θ, r)))
                (cellComplexH1RealEquiv test) := by
  let F := planeBlochEnergyField hab G hG v V hv hb f
  filter_upwards [planeBlochEnergyField_solves_ae hab G hG v V hv hb f,
    cellEnergyJointH1_state_slices hab F] with θ hsol hstate s t hst test
  have hi := cellFiniteEnergyHomogeneous_nativeIncrement hab
    ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb (f θ) (F θ)
    hsol s t hst (cellComplexH1RealEquiv test)
  apply hi.trans
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  apply integral_congr_ae
  have hs := hstate.filter_mono (ae_mono (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.property.1 t.property.2)) le_rfl))
  filter_upwards [hs] with r hr
  rw [cellDualDerivative_pairing]
  have hz : cellSourceFunctional (planePhysicalBlochShift θ) 0
      (0 : Fin 2 → ComplexCellL2) (cellComplexH1RealEquiv test) = 0 := by
    change cellSourceFunctional (planePhysicalBlochShift θ) 0
      (fun _ => 0) (cellComplexH1RealEquiv test) = 0
    exact cellSourceFunctional_zero _ _
  rw [hz, add_zero]
  change cellGeneratorForm _ hG V hv hb r
    (cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab (F θ) r)) _ = _
  rw [← hr]

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_clipped_factorial_gronwall
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
    (clip ρ : ℝ) (hclip : 0 < clip)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy ρ (q t) (u i t).toFunction.jet +
      (1 / 2) * (∫ s in a..t, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet) ≤
      (rawWeightedFactorialEnergy ρ (q a) (f i).toFunction.jet +
        16 * (∫ s in a..b, rawWeightedFactorialEnergy ρ (q s) (F i s).toFunction.jet) +
        (ν / 2) *
          (∫ s in a..b, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet)) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  have hH := scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
    hV ha (le_trans (by norm_num) hB) hlam hbv hjets (w i) (hsln.2.1 i)
  have hQ := scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
    (w i) (F i) (hsln.2.1 i) (hF i)
  have hcv α := cellMetric_scalarChain_ordered_planeWeakHilbertCurve a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha (le_trans (by norm_num) hB) hlam hbv hjets G hGm hG M hb hCell f F hF u w hsln i α
  have hraw := cellMetric_storedWords_clipped_raw_energy_bound a b hab v
    (fun t ht => (hv t ht).of_le (by simp)) hvm hdiv V hV hbv G hG1 hGm hCell hGs
    t₀ S ϖ zc N m Cw C hm hwa hwb (u i) _ (w i) _ (hsln.2.1 i) hH hQ hcv clip hclip ρ
  have hbud := constantMetric_scalarChain_words_clipped_source_integral_budgets a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip ρ hclip
    hρ ν hν hsmall hstrainSmall
  dsimp only at hraw hbud
  intro t ht
  have hh := hraw t ht
  rw [hsln.2.2.2.1 i] at hh
  have hmerge := add_le_add
    (add_le_add (le_refl (rawWeightedFactorialEnergy ρ
      (fun x => clipWeight clip (C.W m a x)) (f i).toFunction.jet))
      (mul_le_mul_of_nonneg_left hbud.2 (by norm_num : (0 : ℝ) ≤ 8)))
    (mul_le_mul_of_nonneg_left hbud.1 (by norm_num : (0 : ℝ) ≤ 2))
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hf0 : 0 ≤ ∫ s in a..b, rawWeightedFactorialEnergy ρ
        (fun x => clipWeight clip (C.W m s x)) (F i s).toFunction.jet := by
      apply intervalIntegral.integral_nonneg hab
      intro s _
      apply rawWeightedFactorialEnergy_nonneg
      intro x
      exact (clipWeight_pos hclip (C.pos m hm s x)).le
  linarith only [hmerge, hf0]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Literal native metric insertions with their integrated moment bounds. -/

theorem metricRemainder_native_insertion_exists_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 ρ K (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (U t) z)) ∧
        (∀ m, (∫⁻ t in Set.Icc a b, weightedFactorialNormSq m ϖ 0 ρ K (V t)) ≤
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ ^ (Ks + 1))) ^ 2) *
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (m + (Ks + 1)) ϖ 0 ρ K (U t))) := by
  obtain ⟨C, hC, hmatrix⟩ := metricRemainderMatrix_native_flux_exists_uniform Ks Kmax M
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet n U hU he
  obtain ⟨V, hV, hVe, hv, hdens⟩ := hmatrix K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet n U hU he
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hv] with t ht
    filter_upwards [ht] with z hz
    have hh := metricCoordinateFlux_eq_stored
      (fun k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z) (U t) z
    exact hz.trans (by simpa only [nativeMetricInsertionFlux, Matrix.sub_apply, metricTaylor, sub_zero] using hh)
  · intro m
    exact nativeFlux_time_moment_shift_budget m (Ks + 1) ϖ ρ
      (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ ^ (Ks + 1)))
      (volume.restrict (Set.Icc a b)) V U hdens

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The supplied package graph is a genuine normalized weak Bloch evolution. -/

theorem fibreScalarData_graph_weak_evolution
    (K : ScalarConstants) (η t₀ S : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ K.Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) {a b : ℝ} (hab : a ≤ b) :
    CellWeakHilbertCurve a b
      (fun t => cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (fun t => cellH1Slice (fibreSeriesJet data.r ξ) t + cellH1One)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j,
          fun s => -fibreSeriesC data.lam ξ s⟩ hG V hv.1 hb t
        (cellH1Slice (fibreSeriesJet data.r ξ) t + cellH1One) 0 0) := by
  let D := fibreSeriesJet data.r ξ
  have hd := data.graph.2.1 ξ hξ
  obtain ⟨_, _, _, htr, _, he⟩ := cellFibreGraph_native_equation
    η K.Cw hη hCw G hG hv hw V hb ξ D hd.2.2.1
  have hh := he a b hab
  apply hh.add_one.dual_congr
  filter_upwards [hh.agrees] with t ht
  have hsrc : cellFibreGraphSourceClass η K.Cw hCw hv hw ξ t (cellRawTrace D t) =
      cellNormalizedGraphSourceClass G v V hv hb
        (fun j => (Real.sqrt η : ℂ) * ξ j) (fun s => -fibreSeriesC data.lam ξ s) t
        (cellH1Slice D t) := by
    apply Lp.ext
    have hraw := cellFibreGraphSourceClass_ae η K.Cw hCw hv hw ξ t
      (cellRawTrace D t) (cellValue D) (htr t)
    have hnorm := cellNormalizedGraphSourceClass_bloch_ae η hη0 G hv V hb ξ
      (fibreSeriesC data.lam ξ) t (cellH1Slice D t)
    have hval : (torusHkValueCLM (cellH1Slice D t) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] cellValue D t := by
      rw [← ht]
      exact htr t
    filter_upwards [hraw, hnorm, hval] with x hr hn hx
    rw [hr, hn, hx]
    exact fibreGraph_normalized_source_identity η K.Cw K.ξ0 K.Cg G hv hm hw
      data.r data.lam data.graph ξ hξ t x
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

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_compact_factorial_lower_integral
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
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η) :
    let q := fun t x => clipWeight clip (C.W m t x)
    let d := fun t => rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
    let fenergy := fun t => rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet
    ∀ t ∈ Icc a b,
      ENNReal.ofReal (rawWeightedFactorialEnergy ρ (fun x => χ x ^ 2 * q t x)
        (u i t).toFunction.jet + ∫ s in a..t,
          rawWeightedGradientEnergy ρ (fun x => χ x ^ 2 * q s x) (w i s).toFunction.jet) ≤
      (ENNReal.ofReal (rawWeightedFactorialEnergy ρ (fun x => χ x ^ 2 * q a x)
        (f i).toFunction.jet) + ∫⁻ s in Icc a b, ENNReal.ofReal
          (16 * fenergy s +
            (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) * d s +
            (4096 * η ^ 2 + 16 * V * η) * rawWeightedFactorialEnergy ρ (q s) (u i s).toFunction.jet)) *
        ENNReal.ofReal (Real.exp (18 * C.lam m * (t - a))) := by
  dsimp only
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
  have hcv α := scalarChain_ordered_curve_of_flux_lower_integral
    a b hab κ Kmax hκ v hvm hv V strain B lam hV ha (le_trans (by norm_num) hB) hlam
    hbv hjets G hGm hG M hb g hg4 hGnear hGs f F hF u w hsln i α
  have hgr := storedWords_clipped_compact_lower_integral_bound a b hab v
    (fun t ht => (hv t ht).of_le (by simp)) hdiv V hV hbv G hG1 g hg4 hGnear hGs
    t₀ S ϖ zc N m Cw C hm hwa hwb (u i) H (w i) Q hcv χ hχ hsχ hχ0 hχ1 η hη hdχ clip hclip ρ
  have hbud := scalarChain_words_clipped_source_spatial_budgets a b hab κ Kmax hκ
    v hv V strain B lam hV ha hB hlam hbv hjets G hG M hb g hg4 hGnear hGs
    f F u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip ρ hclip
    hρ ν hν hsmall hstrainSmall δ hδ hg hscale CG hmetricJets
  dsimp only at hgr hbud
  have hforce : ∀ᵐ s ∂volume.restrict (Icc a b),
      8 * (∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
        (∫ x, q s x * ‖(WithLp.toLp 2 (fun k => L α s k x) : PiLp 2 (fun _ : Fin 2 => h i.2))‖ ^ 2)) +
      (4096 * η ^ 2 + 16 * V * η) * (∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
        (∫ x, q s x * ‖planeJetReadoutOperator (κ i.1 i.2) α (u i s) x‖ ^ 2)) +
      2 * (∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
        (∫ x, χ x ^ 2 * q s x * (‖R α s x‖ * ‖planeJetReadoutOperator (κ i.1 i.2) α (u i s) x‖))) ≤
      16 * rawWeightedFactorialEnergy ρ (q s) (F i s).toFunction.jet +
      (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) *
        rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet +
      (4096 * η ^ 2 + 16 * V * η) * rawWeightedFactorialEnergy ρ (q s) (u i s).toFunction.jet := by
    filter_upwards [hbud] with s hs
    have hRc := cutoff_weighted_value_word_sum_le
      (fun α : JetIndex2 (κ i.1 i.2) => factorialWeight ρ α.1.val)
      (fun α => factorialWeight_nonneg ρ _) (q s) χ
      (chartWeights_clipped_spatial_regularity C m hm s clip hclip).1.continuous hχ.continuous
      (fun x => (clipWeight_pos hclip (C.pos m hm s x)).le) clip
      (fun x => by rw [abs_of_nonneg (clipWeight_pos hclip (C.pos m hm s x)).le];
                   exact clipWeight_le_bound hclip (C.pos m hm s x))
      hχ0 hχ1 (fun α => R α s) (fun α => planeJetReadoutOperator (κ i.1 i.2) α (u i s))
    rw [planeStoredWord_factorial_energy]
    exact compact_source_budget_combine hs.2 hs.1 hRc
  intro t ht
  have hh := hgr t ht
  simp only [planeStoredWord_factorial_energy, planeStoredWord_gradient_energy] at hh
  rw [hsln.2.2.2.1 i] at hh
  apply hh.trans
  apply mul_le_mul _ le_rfl zero_le zero_le
  apply add_le_add le_rfl
  apply lintegral_mono_ae
  filter_upwards [hforce] with s hs
  apply ENNReal.ofReal_le_ofReal
  simpa only [planeStoredWord_factorial_energy] using hs

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Absorption of the clipped factorial energy for a weight whose rate is at most `Λ/S` on a
window of length `S`; the energy then grows by at most `3e^{18Λ}`. -/
theorem constantMetric_scalarChain_clipped_factorial_absorption_of_rate
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (hrate : C.lam m ≤ Λ / S)
    (hreserve : Real.exp (18 * Λ) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet +
      (∫ s in a..b, rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) / 4 ≤
      3 * Real.exp (18 * Λ) *
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
  have hh := constantMetric_scalarChain_clipped_factorial_gronwall a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip (r / L) hclip
    hρ (1 / L ^ 2) hν hs hst hdiv hwa hwb
  dsimp only at hh
  let q := fun t x => clipWeight clip (C.W m t x)
  let e := fun t => rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet
  let d := fun t => (1 / 2) * rawWeightedGradientEnergy (r / L) (q t) (w i t).toFunction.jet
  let ff := fun t => rawWeightedFactorialEnergy (r / L) (q t) (F i t).toFunction.jet
  let A := Real.exp (18 * Λ)
  let c := 1 / L ^ 2
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  have he0 t : 0 ≤ e t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hd0 t : 0 ≤ d t := mul_nonneg (by norm_num)
    (rawWeightedGradientEnergy_nonneg _ _ (hq0 t) _)
  have hf0 t : 0 ≤ ff t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hD0 : 0 ≤ ∫ s in a..b, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0)
  have hF0 : 0 ≤ ∫ s in a..b, ff s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hf0)
  have hI0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet :=
    rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) _
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : A * c ≤ 1 / 2 := by
    simpa only [A, c, div_eq_mul_inv, inv_pow, one_mul] using hreserve
  have hbudget0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
      16 * (∫ s in a..b, ff s) + c * (∫ s in a..b, d s) := by positivity
  have hbound t (ht : t ∈ Icc a b) : e t + (∫ s in a..t, d s) ≤
      A * (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
        16 * (∫ s in a..b, ff s) + c * (∫ s in a..b, d s)) := by
    have hexp := chart_interval_rate_exp_bound hwa hab hwb ht
      (C.lam_bound m hm).1 hΛ hrate
    have hhh := hh t ht
    have heqd : (1 / 2) * (∫ s in a..t,
        rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) =
        ∫ s in a..t, d s := by rw [intervalIntegral.integral_const_mul]
    have heqbd : ((1 / L ^ 2) / 2) * (∫ s in a..b,
        rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) =
        c * (∫ s in a..b, d s) := by
      rw [intervalIntegral.integral_const_mul]
      dsimp only [c]
      ring
    rw [heqd, heqbd] at hhh
    exact hhh.trans (by
      rw [mul_comm A]
      exact mul_le_mul_of_nonneg_left hexp hbudget0)
  intro t ht
  have hpart0 : 0 ≤ ∫ s in a..t, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict ht.1 (Filter.Eventually.of_forall hd0)
  have het := (le_add_of_nonneg_right hpart0).trans (hbound t ht)
  have hfinal := retained_full_interval_energy (he0 b) hD0 hc het (hbound b ⟨hab, le_rfl⟩)
  convert hfinal using 1
  · dsimp only [e, d, q]
    rw [intervalIntegral.integral_const_mul]
    ring

/-- The case of the chart constant: rate times window length at most `Cw m`. -/
theorem constantMetric_scalarChain_clipped_factorial_absorption
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet +
      (∫ s in a..b, rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) / 4 ≤
      3 * Real.exp (18 * Cw m) *
        (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
          16 * (∫ s in a..b, rawWeightedFactorialEnergy (r / L) (q s) (F i s).toFunction.jet)) := by
  have hCw : 0 ≤ Cw m := (by norm_num : (0 : ℝ) ≤ 1).trans
    (chartWeights_constant_ge_one C m hm a ⟨hwa, hab.trans hwb⟩)
  exact constantMetric_scalarChain_clipped_factorial_absorption_of_rate a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs f F hF u w hsln i
    hG1 t₀ S ϖ zc N m Cw C hm clip r L hclip hr hL hsmall hstrainSmall (Cw m) hCw
    (C.lam_bound m hm).2 hreserve hdiv hwa hwb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The finite single-pulse cell equation reads out its genuine higher generator. -/

theorem interiorPulseGalerkinOperator_higher_readout (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinOperator N (cellGeneratorB
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, θ, κ⟩ hG V hv.1 hb t) u =
    cellGalerkinL2Initial N (torusHkValueCLM
      (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinOperator N _ u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N _)) (cellGalerkinValue N z)
  rw [cellGalerkinOperator_pairing, cellGalerkinL2Initial_pairing]
  change cellGeneratorForm
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, θ, κ⟩ hG V hv.1 hb t u.val z.val =
    inner ℝ (torusHkValueCLM
      (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) (torusHkValueCLM z.val)
  rw [interiorPulseHigherFullGeneratorCLM_pairing K hΛ hζ ν y₀ hslot hv V hb G hG θ κ t _ z.val]
  have he := rangeSmoothFourierLift_truncate (by omega : 1 ≤ K + 2) N u
  have hbase : cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) = u.val := by
    exact he
  rw [hbase]

theorem interiorPulseGalerkinOperator_higher_lift {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, θ, κ⟩ hG V hv.1 hb t) u) =
    galerkinProj N (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) := by
  rw [interiorPulseGalerkinOperator_higher_readout K N hΛ hζ ν y₀ hslot hv V hb G hG θ κ t u,
    cellGalerkinL2Initial_higher_lift]

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

theorem scalarChain_clipped_factorial_lower_integral
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
      ENNReal.ofReal (rawWeightedFactorialEnergy ρ (q t) (u i t).toFunction.jet +
        ∫ s in a..t, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet) ≤
      (ENNReal.ofReal (rawWeightedFactorialEnergy ρ (q a) (f i).toFunction.jet) +
        ∫⁻ s in Icc a b, ENNReal.ofReal (16 * fenergy s +
          (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) * d s)) *
        ENNReal.ofReal (Real.exp (18 * C.lam m * (t - a))) := by
  dsimp only
  obtain ⟨χ, Cχ, hCχ, hχ, hχrange, hχlim, hdχ⟩ :=
    AVRegularity.CoupledEnergyPlane.Transport.exists_expanding_smooth_cutoffs
  let q := fun t x => clipWeight clip (C.W m t x)
  let mass := fun t => rawWeightedFactorialEnergy ρ (q t) (u i t).toFunction.jet
  let force := fun t => 16 * rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet +
    (16 * (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 + ν / 2) *
      rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
  let η := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * Cχ
  let c := fun n => 4096 * η n ^ 2 + 16 * V * η n
  have hu := planeHk_lower_memLp_of_lift (volume.restrict (Icc a b))
    (u i) (w i) (hsln.2.1 i) (hsln.2.2.1 i)
  have hmint := rawWeightedFactorial_time_integrable C m hm clip hclip ρ
    (volume.restrict (Icc a b)) (u i) hu
  have hη n : 0 ≤ η n := by dsimp only [η]; positivity
  have hχ2 n : ContDiff ℝ 2 (χ n) := (hχ n).1.of_le (by simp)
  have hgr n := scalarChain_compact_factorial_lower_integral a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip ρ hclip hρ ν hν
    hsmall hstrainSmall δ hδ hg hscale CG hmetricJets hdiv hwa hwb
    (χ n) (hχ2 n) (hχ n).2 (fun x => (hχrange n x).1) (fun x => (hχrange n x).2)
    (η n) (hη n) (hdχ n)
  have hqcont t := (chartWeights_clipped_spatial_regularity C m hm t clip hclip).1.continuous
  have hqb t x : |q t x| ≤ clip := by
    rw [abs_of_nonneg (clipWeight_pos hclip (C.pos m hm t x)).le]
    exact clipWeight_le_bound hclip (C.pos m hm t x)
  have henergy t := stored_factorial_spatial_cutoff_tendsto χ
    (fun n => (hχ n).1.continuous) hχrange hχlim (q t) (hqcont t) clip (hqb t) ρ (u i t)
  have hinitial := stored_factorial_spatial_cutoff_tendsto χ
    (fun n => (hχ n).1.continuous) hχrange hχlim (q a) (hqcont a) clip (hqb a) ρ (f i)
  have hclim : Tendsto c atTop (𝓝 0) := cutoff_error_rate_tendsto_zero
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  have hmass0 t : 0 ≤ mass t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hforce0 t : 0 ≤ force t := by
    dsimp only [force]
    have hf := rawWeightedFactorialEnergy_nonneg ρ (q t) (hq0 t) (F i t).toFunction.jet
    have hd := rawWeightedGradientEnergy_nonneg ρ (q t) (hq0 t) (w i t).toFunction.jet
    positivity
  have hc0 n : 0 ≤ c n := by dsimp only [c]; positivity
  intro t ht
  have hsub : Ioc a t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hWt := (hsln.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdlim := stored_gradient_spatial_cutoff_time_tendsto C m hm clip hclip ρ
    (volume.restrict (Ioc a t)) (w i) hWt χ (fun n => (hχ n).1.continuous) hχrange hχlim
  have hdlim' : Tendsto (fun n => ∫ s in a..t, rawWeightedGradientEnergy ρ
      (fun x => χ n x ^ 2 * q s x) (w i s).toFunction.jet) atTop
      (𝓝 (∫ s in a..t, rawWeightedGradientEnergy ρ (q s) (w i s).toFunction.jet)) := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hdlim
  apply lower_integral_cutoff_removal force mass hforce0 hmass0 hmint c _ _ _ hc0 hclim
    (henergy t) hdlim' hinitial
  intro n
  exact hgr n t ht

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_clipped_factorial_ennreal
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      storedChartFactorialEnergy (r / L) (q t) (u i t) +
      ENNReal.ofReal (1 / 4 : ℝ) *
        (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
      ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (storedChartFactorialEnergy (r / L) (q a) (f i) +
          16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s)) := by
  dsimp only
  have hh := constantMetric_scalarChain_clipped_factorial_absorption a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip r L hclip hr hL
    hsmall hstrainSmall hreserve hdiv hwa hwb
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
  have hh' := quarter_retained_factorial_energy_to_ennreal
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) (u i t).toFunction.jet)
    (intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0))
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) (f i).toFunction.jet)
    (intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hf0)) (hh t ht)
  rw [hdlim, hflim] at hh'
  have hdEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hdeq s (w i s))
  have hfEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hfeq s (F i s))
  change storedChartFactorialEnergy (r / L) (q t) (u i t) +
    ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
    ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
      (storedChartFactorialEnergy (r / L) (q a) (f i) +
        16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s))
  rw [heq t (u i t), heq a (f i), hdEq, hfEq]
  exact hh' 

end AVRegularity.CycleWords
end
