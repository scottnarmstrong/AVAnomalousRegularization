-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.CycleWords.CellTransitionGeometry
import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleWords.CellTransitionLipschitz
public import AVRegularity.CycleEvolution.CellMetricJetFluxDerivative
public import AVRegularity.CycleWords.IntegralMultilinearPolynomialJets
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! The clipped pulse buffers are quiet for the actual drift under endpoint quiet margins. -/

theorem interiorBufferedPulse_left_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) (a D : ℝ)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hq : ∀ t ∈ Set.Ico a (a + D), ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) (n : ℤ) :
    Set.Ico (interiorBufferedPulseLo (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a D n - D)
      (interiorBufferedPulseLo (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a D n) ⊆
      interiorPulseQuiet α q Λ ζ m ν y₀ := by
  intro t ht z
  rcases interiorBufferedPulse_left_buffer
    (div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL) hD n ht with he | he
  · exact hq t he z
  · exact interior_cell_quiet_annulus hΛ hζ ν y₀ hL n he.1 he.2 z

theorem interiorBufferedPulse_right_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) (b D : ℝ)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hq : ∀ t ∈ Set.Ioc (b - D) b, ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) (n : ℤ) :
    Set.Ioc (interiorBufferedPulseHi (ocTau α q Λ m / ocEll q Λ m ν ^ 2) b D n)
      (interiorBufferedPulseHi (ocTau α q Λ m / ocEll q Λ m ν ^ 2) b D n + D) ⊆
      interiorPulseQuiet α q Λ ζ m ν y₀ := by
  intro t ht z
  rcases interiorBufferedPulse_right_buffer
    (div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL) hD n ht with he | he
  · exact hq t he z
  · exact interior_cell_quiet_annulus hΛ hζ ν y₀ hL n he.1 he.2 z

end AVRegularity.CycleWords
end
end

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Native higher values are a genuine injective complex linear readout. -/

theorem torusHigher_complex_value_smul (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    torusHkValueCLM (c • U) = c • torusHkValueCLM U := by
  rw [torusHigher_complex_smul, torusHigherScalarCLM_value]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae c (torusHkValueCLM U), Lp.coeFn_smul c (torusHkValueCLM U)]
    with x hl hr
  rw [hl, hr]
  rfl

def torusHigherComplexValueCLM (K : ℕ) : TorusHk K ℂ →L[ℂ] ComplexCellL2 where
  toFun := torusHkValueCLM
  map_add' U V := (torusHkValueCLM).map_add U V
  map_smul' c U := torusHigher_complex_value_smul K c U
  cont := (torusHkValueCLM).continuous

theorem torusHigherComplexValueCLM_injective (K : ℕ) :
    Function.Injective (torusHigherComplexValueCLM K) := by
  intro U V h
  exact TorusHk.ext_value h

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Sharp diffusion Gårding bound costs only the Bloch frequency, with no constant or drift loss. -/

theorem cellDiffusionForm_sharp_garding
    (C : CellCoefficients) (hG : IsCellMetric C.G) (t : ℝ) (u : TorusHk 1 ℂ) :
    2 * cellDiffusionForm C hG t u u + (3 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      264 * (∑ j, ‖C.θ j‖ ^ 2) * ‖torusHkValueCLM u‖ ^ 2 := by
  let m := fun j k x => ((C.G t x j k : ℂ) * cellShiftedDerivativeCLM C.θ j u x *
    star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k u x)).re
  let D := fun x : Vec 2 => -(∑ j : Fin 2, ∑ k : Fin 2, m j k x)
  have hm (j k : Fin 2) : Integrable (m j k) (volume.restrict AVenhance.unitCube) :=
    cellMetric_pairing_integrable hG t j k _ _
  have hms (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hm j k)
  have hD : Integrable D (volume.restrict AVenhance.unitCube) := by
    apply Integrable.neg
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hms j)
  have he : (∫ x in AVenhance.unitCube, D x) = cellDiffusionForm C hG t u u := by
    rw [show D = fun x => -(∑ j : Fin 2, ∑ k : Fin 2, m j k x) from rfl, integral_neg,
      integral_finsetSum Finset.univ (fun j _ => hms j)]
    simp_rw [integral_finsetSum Finset.univ (fun k _ => hm _ k)]
    simp only [cellDiffusionForm, neg_apply, sum_apply, pullbackInnerCLM_apply,
      ContinuousLinearMap.comp_apply]
    simp_rw [cellMetric_pairing_eq_integral]
    rfl
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (cellDerivativeCLM j u))
  have hds := integrable_finsetSum Finset.univ (fun j _ => hd j)
  have hval := integrable_normSq_of_memLp (Lp.memLp (torusHkValueCLM u))
  have hθ := ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae C.θ j u)
  have hθ' := ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae (fun i => star (C.θ i)) j u)
  have hi := integral_mono_ae ((hD.const_mul 2).add (hds.const_mul (3 / 4)))
    (hval.const_mul (264 * ∑ j, ‖C.θ j‖ ^ 2)) (by
      filter_upwards [hθ, hθ'] with x hx hx'
      have hp : D x = -cellMetricPairing (C.G t x)
          ((fun j => cellDerivativeCLM j u x) + cellBlochShift C.θ (torusHkValueCLM u x))
          ((fun j => cellDerivativeCLM j u x) +
            cellBlochShift (fun i => star (C.θ i)) (torusHkValueCLM u x)) := by
        simp only [D, m, cellMetricPairing, Fin.sum_univ_two, Complex.add_re,
          Pi.add_apply, cellBlochShift, hx, hx']
      change 2 * D x + (3 / 4) * ∑ j, ‖cellDerivativeCLM j u x‖ ^ 2 ≤
        (264 * ∑ j, ‖C.θ j‖ ^ 2) * ‖torusHkValueCLM u x‖ ^ 2
      rw [hp]
      exact cellDiffusion_pointwise_garding hG t x C.θ _ _)
  simp only [Pi.add_apply] at hi
  rw [integral_add (hD.const_mul 2) (hds.const_mul (3 / 4)),
    integral_const_mul, integral_const_mul, integral_const_mul, he,
    integral_finsetSum Finset.univ (fun j _ => hd j)] at hi
  simp only [cellL2_norm_sq_integral] at hi
  exact hi

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The genuine injective native value map recovers measurability of native states. -/

local instance cellNativeValueMeasurableSpace : MeasurableSpace ComplexCellL2 := borel _
local instance cellNativeValueMeasurableBorelSpace : BorelSpace ComplexCellL2 := ⟨rfl⟩

theorem cellNative_stronglyMeasurable_of_value {α : Type*} [MeasurableSpace α]
    (q : ℕ) (U : α → TorusHk q ℂ)
    (hm : Measurable (fun t => torusHkValueCLM (U t))) : StronglyMeasurable U := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (TorusHk q ℂ) := inferInstance
  let : MeasurableSpace (TorusHk q ℂ) := borel _
  let : BorelSpace (TorusHk q ℂ) := ⟨rfl⟩
  have he := (torusHkValueCLM (E := ℂ) (K := q)).continuous.measurableEmbedding
    (fun x y h => TorusHk.ext_value h)
  have hc : Measurable ((torusHkValueCLM (E := ℂ) (K := q)) ∘ U) := hm
  exact (he.measurable_comp_iff.mp hc).stronglyMeasurable

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Raw cell energy and literal coefficient summation depend only on each spatial jet class. -/

theorem cellEnergyNorm_congr_all_sections (I : Set ℝ) (D E : ℝ → RawJet2 1 ℂ)
    (he : ∀ t a, D t a =ᵐ[volume.restrict AVenhance.unitCube] E t a) :
    cellEnergyNorm I D = cellEnergyNorm I E := by
  have hv : (⨆ t ∈ I, cellL2Norm (cellValue D t)) =
      ⨆ t ∈ I, cellL2Norm (cellValue E t) := by
    apply iSup_congr
    intro t
    apply iSup_congr
    intro _
    exact eLpNorm_congr_ae (he t (valueIndex2 1))
  have hg : ∀ t, cellGradient (D t) =ᵐ[volume.restrict AVenhance.unitCube]
      cellGradient (E t) := by
    intro t
    filter_upwards [ae_all_iff.mpr (he t)] with x hx
    apply PiLp.ext
    intro k
    exact hx ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  unfold cellEnergyNorm
  rw [hv, cellUlNorm_congr_sections I _ _ (Filter.Eventually.of_forall hg)]

theorem fibreSeriesJet_congr_ae_sections
    (r s : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (he : ∀ p t a, r p t a =ᵐ[volume.restrict AVenhance.unitCube] s p t a)
    (ξ : Fin 2 → ℂ) (t : ℝ) (a : JetIndex2 1) :
    fibreSeriesJet r ξ t a =ᵐ[volume.restrict AVenhance.unitCube] fibreSeriesJet s ξ t a := by
  filter_upwards [ae_all_iff.mpr (fun p => he p t a)] with x hx
  unfold fibreSeriesJet
  apply tsum_congr
  intro p
  rw [hx p]

theorem fibreHomogeneousJet_congr_ae_sections
    (r s : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (he : ∀ p t a, r p t a =ᵐ[volume.restrict AVenhance.unitCube] s p t a)
    (ξ : Fin 2 → ℂ) (n : ℕ) (t : ℝ) (a : JetIndex2 1) :
    fibreHomogeneous r ξ n t a =ᵐ[volume.restrict AVenhance.unitCube]
      fibreHomogeneous s ξ n t a := by
  filter_upwards [ae_all_iff.mpr (fun p => he p t a)] with x hx
  simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [hx p]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual normalized renewal has uniform higher jets at the coarse-to-fine ratio. -/

theorem cellTransition_higher_jet_bound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l : ℤ) (y y' : Vec 2) (n : ℕ) (hn : 1 ≤ n) (z : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) (ocCellTransition α q Λ m (Φ (m - 1)) hφ l y y') z‖ ≤
      2 ^ (n + 1) * ((2 : ℝ) ^ 23 * (n.factorial : ℝ) *
        (ocEpsilon q Λ m * ((2 : ℝ) ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹)) ^ n) := by
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have he := (Scales.epsilon_basic (m := m) hq.1 hΛ).1
  have hb := transition_uniform_jacobian_bar α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hseq m hm hφ l (l + 1) (Or.inl rfl)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1)) :=
    CycleReference.streamFlow_spatial_smooth hφ _ _
  exact cell_rescaled_iteratedFDeriv_norm_from_bar hF
    (by positivity : 0 < (2 : ℝ) ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹)
    (by positivity : 0 ≤ (2 : ℝ) ^ 23) hb (ocEpsilon q Λ m) he y y' n hn z

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Replace only the value of an order-one raw jet, retaining its original weak gradient. -/

def cellValueRepresentativeJet (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ) : RawJet2 1 ℂ :=
  fun a x => if a = valueIndex2 1 then f x else D a x

theorem cellValueRepresentativeJet_value (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ) :
    cellValueRepresentativeJet D f (valueIndex2 1) = f := by
  funext x
  simp [cellValueRepresentativeJet]

theorem cellValueRepresentativeJet_ae (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] D (valueIndex2 1)) (a : JetIndex2 1) :
    cellValueRepresentativeJet D f a =ᵐ[volume.restrict AVenhance.unitCube] D a := by
  by_cases h : a = valueIndex2 1
  · subst a
    simpa only [cellValueRepresentativeJet_value] using he
  · exact Filter.Eventually.of_forall (fun x => by simp only [cellValueRepresentativeJet, ite_eq_right h])

theorem cellValueRepresentativeJet_periodicWeak (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ)
    (hD : HasPeriodicOrderedWeakJet D) (hp : AVenhance.IsZ2Periodic f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] D (valueIndex2 1)) :
    HasPeriodicOrderedWeakJet (cellValueRepresentativeJet D f) := by
  let U : TorusHkFunction 1 ℂ := ⟨D, hD⟩
  apply cellPeriodicJet_of_class _ U.toHk
  · intro a
    by_cases h : a = valueIndex2 1
    · subst a
      simpa only [cellValueRepresentativeJet_value] using hp
    · have heq : cellValueRepresentativeJet D f a = D a := by
        funext x
        simp only [cellValueRepresentativeJet, ite_eq_right h]
      rw [heq]
      exact hD.1 a
  · intro a
    exact (torusJetToL2_ae D hD.2.1 a).trans (cellValueRepresentativeJet_ae D f he a).symm

theorem cellValueRepresentativeJet_gradComp (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ)
    (k : Fin 2) : cellGradComp (cellValueRepresentativeJet D f) k = cellGradComp D k := by
  have hne : (⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ : JetIndex2 1) ≠ valueIndex2 1 := by
    intro h
    have hh := congrArg (fun a : JetIndex2 1 => a.1.val) h
    norm_num [valueIndex2, valueIndex] at hh
  funext x
  simp only [cellGradComp, cellValueRepresentativeJet, ite_eq_right hne]

theorem cellValueRepresentativeJet_gradient (D : RawJet2 1 ℂ) (f : Vec 2 → ℂ) :
    cellGradient (cellValueRepresentativeJet D f) = cellGradient D := by
  funext x
  apply PiLp.ext
  intro k
  exact congrFun (cellValueRepresentativeJet_gradComp D f k) x

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The weak generator consumes drift values only at times in its evolution window. -/

theorem cellDriftEntryCLM_congr_at_time
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v w : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hw : Measurable (fun p : ℝ × Vec 2 => w p.1 p.2))
    (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (hvw : v t = w t) (j : Fin 2) :
    cellDriftEntryCLM ⟨G, v, θ, κ⟩ V hv hbv t j =
      cellDriftEntryCLM ⟨G, w, θ, κ⟩ V hw hbw t j := by
  unfold cellDriftEntryCLM
  congr 1
  funext x
  exact congrArg (fun f => (f x j : ℂ)) hvw

theorem cellDualDerivative_drift_congr_at_time
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v w : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hw : Measurable (fun p : ℝ × Vec 2 => w p.1 p.2))
    (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (hvw : v t = w t) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative ⟨G, v, θ, κ⟩ hG V hv hbv t u S F =
      cellDualDerivative ⟨G, w, θ, κ⟩ hG V hw hbw t u S F := by
  have he : cellGeneratorForm ⟨G, v, θ, κ⟩ hG V hv hbv t =
      cellGeneratorForm ⟨G, w, θ, κ⟩ hG V hw hbw t := by
    unfold cellGeneratorForm
    simp only [cellDriftEntryCLM_congr_at_time G v w θ κ V hv hw hbv hbw t hvw]
    rfl
  unfold cellDualDerivative
  rw [he]

theorem cellWeak_drift_window_congr {a b : ℝ}
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v w : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hw : Measurable (fun p : ℝ × Vec 2 => w p.1 p.2))
    (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (hvw : ∀ t ∈ Icc a b, v t = w t)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ, κ⟩ hG V hv hbv t (slice t) (S t) (F t))) :
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, w, θ, κ⟩ hG V hw hbw t (slice t) (S t) (F t)) := by
  apply h.dual_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact cellDualDerivative_drift_congr_at_time G hG v w θ κ V hv hw hbv hbw
    t (hvw t ht) (slice t) (S t) (F t)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual complex Fourier modes belong to the committed periodic weak H1 graph. -/

def cellComplexFourierJet (n : Fin 2 → ℤ) : RawJet2 1 ℂ := fun a x =>
  if h : a.1.val = 0 then cellComplexFourierMode n x else
    ((2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 ⟨0, by omega⟩) : ℂ)) *
      cellComplexFourierMode n x

theorem cellComplexFourierJet_value (n : Fin 2 → ℤ) (j : Fin 1)
    (w : DerivativeWord2 j.val) :
    cellComplexFourierJet n (lowerIndex2 j w) = cellComplexFourierMode n := by
  funext x
  simp only [lowerIndex2, lowerIndex]
  simp [cellComplexFourierJet]

theorem cellComplexFourierJet_next (n : Fin 2 → ℤ) (j : Fin 1)
    (w : DerivativeWord2 j.val) (i : Fin 2) :
    cellComplexFourierJet n (nextIndex2 j w i) = fun x =>
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * cellComplexFourierMode n x := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  funext x
  simp [cellComplexFourierJet, nextIndex2, nextIndex, Fin.snoc]

theorem cellComplexFourierJet_hasPeriodicWeakJet (n : Fin 2 → ℤ) :
    HasPeriodicOrderedWeakJet (cellComplexFourierJet n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a k x
    simp only [cellComplexFourierJet]
    split
    · exact cellComplexFourierMode_periodic n k x
    · rw [cellComplexFourierMode_periodic n k x]
  · intro a
    unfold cellComplexFourierJet
    split
    · exact cellComplexFourierMode_memLp n
    · exact (cellComplexFourierMode_memLp n).const_mul
        ((2 * (Real.pi : ℂ) * Complex.I) * (n (a.2 ⟨0, by omega⟩) : ℂ))
  · intro j w i e
    rw [cellComplexFourierJet_value, cellComplexFourierJet_next]
    have h := smoothVector_weak_coordinate
      ((cellComplexFourierMode_contDiff n).of_le (show (1 : WithTop ℕ∞) ≤ ⊤ from le_top)) i e
    simpa only [cellComplexFourierMode_directional_derivative] using h

def cellComplexFourierModeH1 (n : Fin 2 → ℤ) : TorusHk 1 ℂ :=
  TorusHkFunction.toHk
    { jet := cellComplexFourierJet n
      hasPeriodicWeakJet := cellComplexFourierJet_hasPeriodicWeakJet n }

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The native value readout intertwines an almost-everywhere renewal with spatial L2 transport. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeValueLp_ae {K : ℕ} (U : PlaneHk Set.univ K E) :
    planeHkValueOperator K U =ᵐ[volume] planeValue U := by
  rw [planeHkValueOperator_apply, planeValue_eq_stored]
  exact univToPlane_ae _

omit [FiniteDimensional ℝ E] in
theorem planeValueLp_transport_eq {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hμ : MeasurePreserving X volume volume)
    (h : planeValue V =ᵐ[volume] planeValue U ∘ X) :
    planeHkValueOperator K V = Lp.compMeasurePreserving X hμ (planeHkValueOperator K U) := by
  apply Lp.ext
  have hu := hμ.quasiMeasurePreserving.ae_eq_comp (planeValueLp_ae U)
  filter_upwards [planeValueLp_ae V, h, hu,
    Lp.coeFn_compMeasurePreserving (planeHkValueOperator K U) hμ] with x hv h hu hc
  simpa only [hv, h, hc, Function.comp_apply] using hu.symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Complex Metric AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
open scoped NNReal ENNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Genuine bounded higher-state witnesses realize an analytic cell state in the native torus carrier. -/

theorem torusHigher_native_cauchy_realization (K : ℕ) (g : ℂ → ComplexCellL2)
    (c : ℂ) (R : ℝ≥0) (hR : 0 < R) (M : ℝ)
    (hc : ContinuousOn g (closedBall c R)) (hd : DifferentiableOn ℂ g (ball c R))
    (hex : ∀ z ∈ closedBall c R, ∃ U : TorusHk K ℂ, torusHkValueCLM U = g z ∧ ‖U‖ ≤ M) :
    ∃ f : ℂ → TorusHk K ℂ,
      (∀ z ∈ closedBall c R, torusHkValueCLM (f z) = g z ∧ ‖f z‖ ≤ M) ∧
        HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R := by
  let : MeasurableSpace (TorusHk K ℂ) := borel (TorusHk K ℂ)
  let : BorelSpace (TorusHk K ℂ) := ⟨rfl⟩
  let : MeasurableSpace ComplexCellL2 := borel ComplexCellL2
  let : BorelSpace ComplexCellL2 := ⟨rfl⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (ComponentL2 (volume.restrict AVenhance.unitCube) ℂ) := inferInstance
  have : SecondCountableTopology (JetL2 (volume.restrict AVenhance.unitCube) K ℂ) := inferInstance
  have : SecondCountableTopology (TorusHk K ℂ) := inferInstance
  exact injectiveNative_cauchy_realization (torusHigherComplexValueCLM K)
    (torusHigherComplexValueCLM_injective K) g c R hR M hc hd hex

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! A finite-order derivative budget independent of level and diffusivity contrast. -/

def cellTransitionJetBudget (j : ℕ) : ℝ :=
  if j = 1 then 2 * ((2 : ℝ) ^ 23 + 1)
  else (2 : ℝ) ^ j * ((2 : ℝ) ^ 23 * ((j - 1).factorial : ℝ) * ((2 : ℝ) ^ 11) ^ (j - 1))

theorem cellTransition_uniform_jet_bound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l : ℤ) (y y' : Vec 2) (j : ℕ) (hj : 1 ≤ j) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (ocCellTransition α q Λ m (Φ (m - 1)) hφ l y y') z‖ ≤
      cellTransitionJetBudget j := by
  by_cases hj1 : j = 1
  · subst j
    rw [norm_iteratedFDeriv_one]
    exact norm_fderiv_le_of_lipschitz ℝ
      (cellTransition_forward_lipschitz α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hseq m hm hφ l y y')
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hn : 1 ≤ n := by omega
    have hE := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
    have heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) :=
      (Scales.admissible_space_scale_facts hq hΛ hm).2.2.1.trans
        (div_le_self hE.le (by norm_num))
    have hratio : ocEpsilon q Λ m * ((2 : ℝ) ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹) ≤ 2 ^ 11 := by
      calc
        _ ≤ ocEpsilon q Λ (m - 1) * ((2 : ℝ) ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹) :=
          mul_le_mul_of_nonneg_right heE (by positivity)
        _ = _ := by field_simp
    have hbound := cellTransition_higher_jet_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
      Φ hseq m hm hφ l y y' n hn z
    unfold cellTransitionJetBudget
    simp only [ite_eq_right hj1, Nat.succ_sub_one]
    apply hbound.trans
    gcongr
    exact mul_nonneg (Scales.epsilon_basic (m := m) hq.1 hΛ).1.le (by positivity)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization MeasureTheory Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! One native choice agrees with every local analytic line realization. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The native value is unique. Consequently bounded witnesses on a domain
supply one choice, analytic on every complex line contained in that domain. -/
theorem torusHigher_native_line_choice (q : ℕ) (g : V → ComplexCellL2) (s : Set V)
    (hg : AnalyticOnNhd ℂ g s) (M : ℝ)
    (hex : ∀ y ∈ s, ∃ U : TorusHk q ℂ, torusHkValueCLM U = g y ∧ ‖U‖ ≤ M) :
    ∃ F : V → TorusHk q ℂ,
      (∀ y ∈ s, torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M) ∧
      ∀ (x ν : V) (ρ : ℝ≥0), 0 < ρ →
        (∀ z ∈ closedBall (0 : ℂ) ρ, x + z • ν ∈ s) →
        AnalyticOnNhd ℂ (fun z : ℂ => F (x + z • ν)) (ball 0 (ρ : ℝ)) := by
  classical
  let F := fun y => if hy : y ∈ s then Classical.choose (hex y hy) else 0
  have hF (y) (hy : y ∈ s) : torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M := by
    simpa only [F, dite_eq_left hy] using Classical.choose_spec (hex y hy)
  refine ⟨F, hF, ?_⟩
  intro x ν ρ hρ hline
  let h := fun z : ℂ => g (x + z • ν)
  have ha (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : AnalyticAt ℂ h z :=
    (hg _ (hline z hz)).comp (f := fun z : ℂ => x + z • ν)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  obtain ⟨f, hf, hseries⟩ := torusHigher_native_cauchy_realization q h 0 ρ hρ M
    (fun z hz => (ha z hz).continuousAt.continuousWithinAt)
    (fun z hz => (ha z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hex _ (hline z hz))
  intro z hz
  have he : (fun z : ℂ => F (x + z • ν)) =ᶠ[𝓝 z] f := by
    have hb : ball (0 : ℂ) (ρ : ℝ) ∈ 𝓝 z := isOpen_ball.mem_nhds hz
    filter_upwards [hb] with z hz
    apply torusHigherComplexValueCLM_injective q
    exact (hF _ (hline z (ball_subset_closedBall hz))).1.trans
      (hf z (ball_subset_closedBall hz)).1.symm
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) (ρ : ℝ)) := by
    simpa only [Metric.eball_coe] using hseries.analyticOnNhd
  exact (han z hz).congr he.symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Finite normalized row coefficients preserve smooth periodic replacements. -/

theorem fibreRowCoefficients_contDiff (k : ℕ × ℕ → ℝ → ℂ)
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, ContDiff ℝ (⊤ : ℕ∞) (a p t)) (p : ℕ × ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreRowCoefficients k a p t) := by
  unfold fibreRowCoefficients
  exact contDiff_const.add (ContDiff.sum (fun q _ => contDiff_const.mul (ha _ t)))

theorem fibreRowCoefficients_periodic (k : ℕ × ℕ → ℝ → ℂ)
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, AVenhance.IsZ2Periodic (a p t)) (p : ℕ × ℕ) (t : ℝ) :
    AVenhance.IsZ2Periodic (fibreRowCoefficients k a p t) := by
  intro n x
  unfold fibreRowCoefficients
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [ha _ t n x]

theorem fibreRowCoefficients_congr_ae (k : ℕ × ℕ → ℝ → ℂ)
    (a b : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube] b p t)
    (p : ℕ × ℕ) (t : ℝ) :
    fibreRowCoefficients k a p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreRowCoefficients k b p t := by
  filter_upwards [ae_all_iff.mpr (fun q => ha q t)] with x hx
  unfold fibreRowCoefficients
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [hx (fibreCoefficientComplement p q)]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The continuous spatial L2 word readout agrees with the target's literal weak-jet accessor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetLpReadout_ae {K j : ℕ} (hj : j ≤ K) (U : PlaneHk Set.univ K E)
    (w : DerivativeWord2 j) :
    Weighted.planeJetReadoutOperator K ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ U =ᵐ[volume]
      planeJetOrder U j w := by
  rw [Weighted.planeJetReadoutOperator_apply, planeJetOrder_eq_stored hj]
  exact univToPlane_ae _

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Replacing coefficient values preserves all original gradients and literal Taylor summation. -/

def fibreGraphValueReplacement (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (f : ℕ × ℕ → ℝ → Vec 2 → ℂ) : ℕ × ℕ → ℝ → RawJet2 1 ℂ :=
  fun p t => cellValueRepresentativeJet (r p t) (f p t)

theorem fibreGraphValueReplacement_series (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (f : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreSeriesJet (fibreGraphValueReplacement r f) ξ t =
      cellValueRepresentativeJet (fibreSeriesJet r ξ t) (fibreSeriesFun f ξ t) := by
  funext a x
  by_cases ha : a = valueIndex2 1
  · subst a
    simp [fibreSeriesJet, fibreGraphValueReplacement, fibreSeriesFun, cellValueRepresentativeJet]
  · simp only [fibreSeriesJet, fibreGraphValueReplacement, cellValueRepresentativeJet,
      ite_eq_right ha]

theorem cellValue_replacement_energyNorm (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (f : ℝ → Vec 2 → ℂ)
    (he : ∀ t, f t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    cellEnergyNorm I (fun t => cellValueRepresentativeJet (D t) (f t)) = cellEnergyNorm I D := by
  have hv : (⨆ t ∈ I, cellL2Norm (f t)) = ⨆ t ∈ I, cellL2Norm (cellValue D t) := by
    apply iSup_congr
    intro t
    apply iSup_congr
    intro _
    exact eLpNorm_congr_ae (he t)
  unfold cellEnergyNorm
  have hvalue : cellValue (fun t => cellValueRepresentativeJet (D t) (f t)) = f := by
    funext t
    exact cellValueRepresentativeJet_value (D t) (f t)
  rw [hvalue, hv]
  congr 1

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Native linear combinations have the expected literal spatial readouts almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_add_ae {K j : ℕ} (hj : j ≤ K)
    (U V : PlaneHk Set.univ K E) (w : DerivativeWord2 j) :
    planeJetOrder (U + V) j w =ᵐ[volume] fun z => planeJetOrder U j w z + planeJetOrder V j w z := by
  let R := Weighted.planeJetReadoutOperator (E := E) K ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩
  have hsum := Lp.coeFn_add (R U) (R V)
  rw [← map_add] at hsum
  filter_upwards [(planeJetLpReadout_ae hj (U + V) w).symm, hsum,
    planeJetLpReadout_ae hj U w, planeJetLpReadout_ae hj V w] with z hz hs hu hv
  exact hz.trans (hs.trans (congrArg₂ (· + ·) hu hv))

theorem planeValue_add_ae {K : ℕ} (U V : PlaneHk Set.univ K E) :
    planeValue (U + V) =ᵐ[volume] fun z => planeValue U z + planeValue V z :=
  planeJetOrder_add_ae (Nat.zero_le K) U V (fun i => Fin.elim0 i)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The genuine higher Sobolev entrance of a normalized graph remainder. -/

theorem torusHigher_normalized_projection_value (J : ℕ) (U R : TorusHk J ℂ)
    (ell : ComplexCellL2) :
    torusHkValueCLM (U - torusHigherScalarCLM J
      (cellComplexPair (torusHkValueCLM U)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)) R) =
      torusHkValueCLM U - cellScalarCLM
        (cellComplexPair (torusHkValueCLM U)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)) (torusHkValueCLM R) := by
  rw [map_sub, torusHigherScalarCLM_value]

theorem torusHigher_normalized_projection_norm (J : ℕ) (U R : TorusHk J ℂ)
    (ell : ComplexCellL2) (L B : ℝ) (hL : ‖ell‖ ≤ L) (hB : ‖R‖ ≤ B) :
    ‖U - torusHigherScalarCLM J
      (cellComplexPair (torusHkValueCLM U)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)) R‖ ≤
      (1 + L * B) * ‖U‖ := by
  have hL0 := (norm_nonneg ell).trans hL
  have hv : ‖torusHkValueCLM U‖ ≤ ‖U‖ := PiLp.norm_apply_le U.val (valueIndex2 J)
  have hc := cellComplexPair_norm_le (torusHkValueCLM U)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)
  rw [cellFiberConj_norm] at hc
  have hc' := hc.trans (mul_le_mul hv hL (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ ‖U‖ + ‖torusHigherScalarCLM J _ R‖ := norm_sub_le _ _
    _ = ‖U‖ + ‖cellComplexPair (torusHkValueCLM U)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)‖ * ‖R‖ := by
        rw [torusHigherScalarCLM_norm]
    _ ≤ ‖U‖ + (‖U‖ * L) * B := add_le_add le_rfl
      (mul_le_mul hc' hB (norm_nonneg _) (mul_nonneg (norm_nonneg _) hL0))
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The bilinear cell pairing is symmetric in its two unconjugated fields. -/

theorem cellComplexPair_bilinear_symm (u z : ComplexCellL2) :
    cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap z) =
      cellComplexPair z (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) := by
  unfold cellComplexPair
  apply integral_congr_ae
  filter_upwards [cellFiberConj_ae u, cellFiberConj_ae z] with x hu hz
  rw [hu, hz, star_star, star_star, mul_comm]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Equal graph coefficient value classes preserve both literal full fast remainders. -/

theorem fibreFastPart_graph_congr_ae
    (r r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (he : ∀ p t, cellValue (r p) t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r' p) t)
    (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreFastPart r' lam ell ξ D s t := by
  have hs := fibreSeriesFun_congr_ae (fun p => cellValue (r p))
    (fun p => cellValue (r' p)) he ξ t
  filter_upwards [hs] with x hx
  change cellValue (fibreSeriesJet r ξ) t x = cellValue (fibreSeriesJet r' ξ) t x at hx
  unfold fibreFastPart
  rw [hx]

theorem fibreAdjointFastPart_graph_congr_ae
    (r r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (he : ∀ p t, cellValue (r p) t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r' p) t)
    (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    fibreAdjointFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointFastPart r' lam ell ξ D s t := by
  have hs := fibreSeriesFun_congr_ae (fun p => cellValue (r p))
    (fun p => cellValue (r' p)) he ξ t
  have hi : (∫ y in AVenhance.unitCube,
      (1 + cellValue (fibreSeriesJet r ξ) t y) * cellValue D (-t) y) =
      ∫ y in AVenhance.unitCube,
      (1 + cellValue (fibreSeriesJet r' ξ) t y) * cellValue D (-t) y := by
    apply integral_congr_ae
    filter_upwards [hs] with y hy
    change cellValue (fibreSeriesJet r ξ) t y = cellValue (fibreSeriesJet r' ξ) t y at hy
    rw [hy]
  exact Filter.Eventually.of_forall (fun x => by unfold fibreAdjointFastPart; rw [hi])

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Genuine plane H1 test carriers reconstructed from native Bloch fibre derivative data. -/

local instance planeBlochReconstructH1Measure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def planeBlochReconstructH1 (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (G : Fin 2 → Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (hfg : ∀ i, ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (G i θ) n = (2 * (Real.pi : ℂ) * Complex.I) *
        ((planeLatticeEmbedding P n + θ) i : ℂ) * mFourierCoeff (F θ) n) :
    PlaneHk Set.univ 1 ℂ :=
  planeComplexH1OfDistribution (planeScalarBlochReconstruct a P hP F)
    (fun i => planeScalarBlochReconstruct a P hP (G i))
    (fun i => planeBlochReconstruct_distribution_derivative a P hP F (G i) i (hfg i))

theorem planeBlochReconstructH1_value (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (G : Fin 2 → Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (hfg : ∀ i, ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (G i θ) n = (2 * (Real.pi : ℂ) * Complex.I) *
        ((planeLatticeEmbedding P n + θ) i : ℂ) * mFourierCoeff (F θ) n) :
    planeHkValueOperator 1 (planeBlochReconstructH1 a P hP F G hfg) =
      planeScalarBlochReconstruct a P hP F :=
  planeComplexH1OfDistribution_value _ _ _

theorem planeBlochReconstructH1_norm_sq (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (G : Fin 2 → Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (hfg : ∀ i, ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (G i θ) n = (2 * (Real.pi : ℂ) * Complex.I) *
        ((planeLatticeEmbedding P n + θ) i : ℂ) * mFourierCoeff (F θ) n) :
    ‖planeBlochReconstructH1 a P hP F G hfg‖ ^ 2 = ‖F‖ ^ 2 + ∑ i : Fin 2, ‖G i‖ ^ 2 := by
  rw [planeBlochReconstructH1, planeComplexH1OfDistribution_norm_sq]
  simp only [planeScalarBlochReconstruct_norm]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual complex torus Fourier basis transferred to the committed cell L2 carrier. -/

local instance scalarTorusCellBridgeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem scalarTorusQuotient_measurePreserving :
    MeasurePreserving torusQuotient (volume.restrict AVenhance.unitCube)
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [← coupledEnergy_torusMeasure_eq_volume]
  exact measurePreserving_torusQuotient_cell

def scalarTorusToCell : ScalarTorusL2 →ₗᵢ[ℝ] ComplexCellL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ torusQuotient scalarTorusQuotient_measurePreserving

theorem scalarTorusToCell_ae (f : ScalarTorusL2) :
    scalarTorusToCell f =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => f (torusQuotient x) :=
  Lp.coeFn_compMeasurePreserving f scalarTorusQuotient_measurePreserving

theorem scalarTorusToCell_mode (n : Fin 2 → ℤ) :
    scalarTorusToCell (mFourierLp 2 n) =
      (cellComplexFourierMode_memLp n).toLp (cellComplexFourierMode n) := by
  apply Lp.ext
  filter_upwards [scalarTorusToCell_ae (mFourierLp 2 n),
    scalarTorusQuotient_measurePreserving.quasiMeasurePreserving.ae (coeFn_mFourierLp 2 n),
    (cellComplexFourierMode_memLp n).coeFn_toLp] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, cellComplexFourierMode_eq]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Exact native plane gradient components of the actual Bloch H1 reconstruction. -/

local instance planeBlochReconstructH1GradientMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem planeBlochReconstructH1_gradient (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (F : Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (G : Fin 2 → Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)))
    (hfg : ∀ i, ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (G i θ) n = (2 * (Real.pi : ℂ) * Complex.I) *
        ((planeLatticeEmbedding P n + θ) i : ℂ) * mFourierCoeff (F θ) n) (i : Fin 2) :
    univToPlane ((planeBlochReconstructH1 a P hP F G hfg).val
      ⟨⟨1, by decide⟩, fun _ => i⟩) = planeScalarBlochReconstruct a P hP (G i) := by
  rw [planeBlochReconstructH1, planeComplexH1OfDistribution_component]
  simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The same actual torus-to-cell pullback is a complex linear isometry. -/

local instance scalarTorusCellComplexBridgeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

def scalarTorusToCellComplex : ScalarTorusL2 →ₗᵢ[ℂ] ComplexCellL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ AVRegularity.Analysis.Convolution.torusQuotient
    scalarTorusQuotient_measurePreserving

theorem scalarTorusToCellComplex_eq (f : ScalarTorusL2) :
    scalarTorusToCellComplex f = scalarTorusToCell f := rfl

theorem scalarTorusToCell_complex_smul (c : ℂ) (f : ScalarTorusL2) :
    scalarTorusToCell (c • f) = c • scalarTorusToCell f :=
  scalarTorusToCellComplex.map_smul c f

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Normalized torus almost-everywhere facts pull back to the whole plane. -/

local instance scalarTorusPlaneAEMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorus_ae_plane_pullback {p : UnitAddTorus (Fin 2) → Prop}
    (hp : ∀ᵐ z ∂(volume : Measure (UnitAddTorus (Fin 2))), p z) :
    ∀ᵐ x ∂(volume : Measure (Vec 2)), p (torusQuotient x) := by
  apply ae_torusQuotient
  rwa [coupledEnergy_torusMeasure_eq_volume]

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution Metric Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Native Cauchy realizations give genuine higher frequency derivative classes on a fixed disc. -/

theorem torusHigher_cauchy_derivative_readout (q : ℕ) (f : ℂ → TorusHk q ℂ)
    (g : ℂ → ComplexCellL2) (R : ℝ≥0) (hR : 0 < R) (M : ℝ)
    (hf : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R)
    (hg : ∀ z ∈ closedBall (0 : ℂ) R, torusHkValueCLM (f z) = g z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ M) (n : ℕ) :
    ∃ U : TorusHk q ℂ, torusHkValueCLM U = iteratedDeriv n g 0 ∧
      ‖U‖ ≤ analyticBallDerivativeConstant n * M / ((R : ℝ) / 2) ^ n := by
  have ha : AnalyticOnNhd ℂ f (ball 0 (R : ℝ)) := by
    simpa only [Metric.eball_coe] using hf.analyticOnNhd
  have hr : 0 < (R : ℝ) := hR
  have hnorm := analyticLine_interior_derivative_bound f R 0 ((R : ℝ) / 2) M
    (half_pos hr) (by linarith only [hr]) ha
    (fun z hz => hb z (ball_subset_closedBall hz)) 0 (by simp) n
  refine ⟨iteratedDeriv n f 0, ?_, hnorm⟩
  have he : g =ᶠ[𝓝 (0 : ℂ)] (fun z => torusHkValueCLM (f z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact (hg z (ball_subset_closedBall hz)).symm
  rw [he.iteratedDeriv_eq n]
  change torusHigherComplexValueCLM q (iteratedDeriv n f 0) =
    iteratedDeriv n ((torusHigherComplexValueCLM q) ∘ f) 0
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    (torusHigherComplexValueCLM q).iteratedFDeriv_comp_left
      (show ContDiffAt ℂ (n : WithTop ℕ∞) f 0 from hf.analyticAt.contDiffAt) le_rfl]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact Fourier series convergence in the committed complex cell L2 carrier. -/

local instance scalarFourierCellSeriesMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusToCell_fourier_series (u : ScalarTorusL2) :
    HasSum (fun n : Fin 2 → ℤ => mFourierCoeff u n • scalarTorusToCell (mFourierLp 2 n))
      (scalarTorusToCell u) := by
  have h := (hasSum_mFourier_series_L2 u).mapL
    scalarTorusToCellComplex.toContinuousLinearMap
  change HasSum (fun n : Fin 2 → ℤ => scalarTorusToCellComplex
    (mFourierCoeff u n • mFourierLp 2 n)) (scalarTorusToCellComplex u) at h
  simpa only [map_smul, scalarTorusToCellComplex_eq] using h

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual torus-to-cell pullback is onto, with the committed cell selector as inverse. -/

local instance scalarTorusCellUnitaryMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

def scalarCellToTorus (f : ComplexCellL2) : ScalarTorusL2 :=
  torusLpToVolume (cellToTorus f)

theorem scalarTorusToCell_scalarCellToTorus (f : ComplexCellL2) :
    scalarTorusToCell (scalarCellToTorus f) = f := by
  apply Lp.ext
  have hcell := torusToCell_ae (cellToTorus f)
  have ht := torusLpToVolume_coeFn (cellToTorus f)
  have ht' : torusLpToVolume (cellToTorus f) =ᵐ[torusMeasure] cellToTorus f := by
    simpa only [coupledEnergy_torusMeasure_eq_volume] using ht
  have hp := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae ht'
  have hi := torusToCell_cellToTorus f
  have hf : torusToCell (cellToTorus f) =ᵐ[volume.restrict AVenhance.unitCube] f :=
    Filter.Eventually.of_forall (fun x => congrArg (fun z : ComplexCellL2 => z x) hi)
  filter_upwards [scalarTorusToCell_ae (scalarCellToTorus f), hp, hcell, hf]
    with x hx hp' hc hf'
  exact hx.trans (hp'.trans (hc.symm.trans hf'))

theorem scalarTorusToCell_surjective : Function.Surjective scalarTorusToCell :=
  fun f => ⟨scalarCellToTorus f, scalarTorusToCell_scalarCellToTorus f⟩

def scalarTorusCellUnitary : ScalarTorusL2 ≃ₗᵢ[ℝ] ComplexCellL2 :=
  LinearIsometryEquiv.ofSurjective scalarTorusToCell scalarTorusToCell_surjective

end AVRegularity.CycleWords
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Subtraction of actual weighted jet arrays agrees almost everywhere with native subtraction. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedJetArray_sub_ae {K : ℕ} (U V : PlaneHk Set.univ K E) (q : Vec 2 → ℝ)
    (R S : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x))
    (hS : ∀ a, S a =ᵐ[volume] (fun x => q x • V.toFunction.jet a x)) (a : JetIndex2 K) :
    (R - S) a =ᵐ[volume] (fun x => q x • (U - V).toFunction.jet a x) := by
  have hn := planeJetOrder_sub_ae (Nat.le_of_lt_succ a.1.isLt) U V a.2
  simp only [planeJetOrder_eq_stored (Nat.le_of_lt_succ a.1.isLt)] at hn
  filter_upwards [Lp.coeFn_sub (R a) (S a), hR a, hS a, hn] with x hx hr hs hu
  change (R a - S a) x = _
  rw [hx, Pi.sub_apply, hr, hs, hu, smul_sub]
end

/-! The smooth pullback norm bound also controls differences, through native value uniqueness. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothPlanePullback_sub_norm_le {K : ℕ} (U V : PlaneHk Set.univ K E)
    (f g : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : planeValue U =ᵐ[volume] f) (hv : planeValue V =ᵐ[volume] g)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    ‖smoothPlanePullback U f hf hu X hX hμ B hb -
      smoothPlanePullback V g hg hv X hX hμ B hb‖ ≤ smoothPullbackNormBound B K * ‖U - V‖ := by
  have hsub : planeValue (U - V) =ᵐ[volume] f - g := by
    filter_upwards [planeValue_sub_ae U V, hu, hv] with x hs hu hv
    simp only [hs, hu, hv, Pi.sub_apply]
  let W := smoothPlanePullback (U - V) (f - g) (hf.sub hg) hsub X hX hμ B hb
  have hW : W = smoothPlanePullback U f hf hu X hX hμ B hb -
      smoothPlanePullback V g hg hv X hX hμ B hb := by
    apply planeHk_eq_of_planeValue_ae
    filter_upwards [smoothPlanePullback_value_ae (U - V) (f - g) (hf.sub hg) hsub X hX hμ B hb,
      planeValue_sub_ae (smoothPlanePullback U f hf hu X hX hμ B hb)
        (smoothPlanePullback V g hg hv X hX hμ B hb),
      smoothPlanePullback_value_ae U f hf hu X hX hμ B hb,
      smoothPlanePullback_value_ae V g hg hv X hX hμ B hb] with x hW hs hf hg
    simp only [W, hW, hs, hf, hg, Function.comp_apply, Pi.sub_apply]
  rw [← hW]
  exact smoothPlanePullback_norm_le (U - V) (f - g) (hf.sub hg) hsub X hX hμ B hb
end

end AVRegularity.CycleWords
end
end
