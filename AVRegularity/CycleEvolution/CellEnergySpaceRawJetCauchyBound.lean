-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.CycleEvolution.CellEnergySeriesRegularity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Arbitrary common forcing cancels before constructing the Hilbert time derivative of a difference. -/

/-- The difference of two public solutions has the actual homogeneous Hilbert test equation. -/
theorem cellSolutionPair_Hilbert_increment {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D)
    (h' : IsCellSolution (Icc a b) C src F D')
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    inner ℝ (cellRawTrace D t - cellRawTrace D' t) (torusHkValueCLM z) -
      inner ℝ (cellRawTrace D s - cellRawTrace D' s) (torusHkValueCLM z) =
        ∫ r in s..t, inner ℝ
          (cellDualDerivative C hG V hv hb r (cellH1Slice D r - cellH1Slice D' r) 0 (fun _ => 0)) z := by
  let ψ := cellHilbertTest z
  let E := fun r j x => D r j x - D' r j x
  let R := fun r => cellLiteralRHS C r (cellValue E r) (cellGradComp (E r))
    (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) 0 0
  let g := fun r => cellDualDerivative C hG V hv hb r (cellH1Slice D r - cellH1Slice D' r) 0 (fun _ => 0)
  have hid := cellWeakIdentity_sub_same_source C s t _ _ _ _ _ _ _ _ _ _ src F
    (h.2.2.2.2.2.2 s hs t ht hst ψ) (h'.2.2.2.2.2.2 s hs t ht hst ψ)
  change Integrable (fun x => cellValue E t x * ψ.jet (valueIndex2 1) x) _ ∧
    Integrable (fun x => cellValue E s x * ψ.jet (valueIndex2 1) x) _ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) _) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, R r x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, cellValue E t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue E s x * ψ.jet (valueIndex2 1) x) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x at hid
  have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  have hj := (cellSolution_slice_ae h).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hj' := (cellSolution_slice_ae h').filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (g r) z := by
    filter_upwards [hj, hj'] with r hr hr'
    have hE (j) : (((cellH1Slice D r - cellH1Slice D' r).val j) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] E r j :=
      (Lp.coeFn_sub _ _).trans ((hr j).sub (hr' j))
    have heq := (cellRawSpatial_equation C hG V hv hb r (cellH1Slice D r - cellH1Slice D' r)
      (E r) hE ψ 0 (fun _ => 0) 0 0 (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube))
      (fun _ => by
        filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2)
          (μ := volume.restrict AVenhance.unitCube)] with x hx
        simpa only [Pi.zero_apply, PiLp.zero_apply] using hx)).2
    change (∫ x in AVenhance.unitCube, R r x) = cellDualComplexPair (g r) (cellRawTest ψ) at heq
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at heq
    exact heq
  have htrace (r : ℝ) (hr : r ∈ Icc a b) :
      ((cellRawTrace D r - cellRawTrace D' r : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue E r :=
    (Lp.coeFn_sub _ _).trans ((cellRawTrace_ae D r (h.2.2.1 r hr).1).sub
      (cellRawTrace_ae D' r (h'.2.2.1 r hr).1))
  have hp (r : ℝ) (hr : r ∈ Icc a b) := cellRawTest_pairing_integral ψ
    (cellRawTrace D r - cellRawTrace D' r) (cellValue E r) (htrace r hr)
  have hinc : cellComplexPair (cellRawTrace D t - cellRawTrace D' t) (torusHkValueCLM z) -
      cellComplexPair (cellRawTrace D s - cellRawTrace D' s) (torusHkValueCLM z) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x := by
    have hpt := hp t ht
    have hps := hp s hs
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at hpt hps
    rw [hpt, hps]
    exact hid.2.2.2.2
  have hre := congrArg Complex.re hinc
  simp only [Complex.sub_re, cellComplexPair_re] at hre
  have hmap := Complex.reCLM.integral_comp_comm hid.2.2.2.1
  change (∫ r in Ioc s t, (∫ x in AVenhance.unitCube, R r x).re) =
    (∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x).re at hmap
  rw [← hmap] at hre
  rw [intervalIntegral.integral_of_le hst]
  have hreal : (fun r => (∫ x in AVenhance.unitCube, R r x).re) =ᵐ[
      volume.restrict (Ioc s t)] fun r => inner ℝ (g r) z :=
    he.mono (fun r hr => (congrArg Complex.re hr).trans (cellDualComplexPair_re _ _))
  exact hre.trans (integral_congr_ae hreal)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every raw homogeneous energy solution gives the actual homogeneous weak Hilbert curve. -/

theorem cellSourceSlice_zero (t : ℝ) :
    cellSourceSlice (fun (_ : ℝ) (_ : Vec 2) => (0 : ℂ)) t = 0 := by
  exact cellSourceSlice_eq_of_ae _ t 0 (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube))

theorem cellRawHomogeneous_to_Hilbert {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) ⟨G, v, θ, 0⟩ (fun _ _ => 0) (fun _ _ => 0) D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Slice D t) 0 0) := by
  have hh := cellSolution_to_Hilbert hab ⟨G, v, θ, 0⟩ hG V 0 hv hb
    measurable_const (fun _ => by simp) (fun _ _ => 0) (fun _ _ => 0)
    MemLp.zero MemLp.zero D h
  change CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
    (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Slice D t)
      (cellSourceSlice (fun _ _ => 0) t)
      (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hh
  simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hh

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Actual continuous Banach jets with genuine coordinate Frechet derivatives give the public raw norm-jet interface. -/

theorem cellEnergySpaceRaw_isNormJetFamily_of_derivatives {a b : ℝ} (hab : a ≤ b)
    (K : ℕ) (U : Set (Fin 2 → ℂ))
    (J : ℕ × ℕ → (Fin 2 → ℂ) → CellEnergySpace a b)
    (D : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ)
    (hD : ∀ p y, IsCellEnergySpaceRawRepresentative hab (J p y) (D p y))
    (hc : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ K → ∀ y ∈ U, ContinuousAt (J p) y)
    (hd : ∀ p : ℕ × ℕ, p.1 + p.2 < K → ∀ y ∈ U,
      ∃ L : (Fin 2 → ℂ) →L[ℂ] CellEnergySpace a b,
        HasFDerivAt (J p) L y ∧
        L (Pi.single 0 1) = J (p.1 + 1, p.2) y ∧
        L (Pi.single 1 1) = J (p.1, p.2 + 1) y) :
    IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Icc a b)) K U D := by
  constructor
  · intro p hp y hy
    have hn : Tendsto (fun y' => J p y' - J p y) (𝓝 y) (𝓝 0) := by
      simpa only [sub_self] using (hc p hp y hy).tendsto.sub (tendsto_const_nhds (x := J p y))
    apply cellEnergySpaceRaw_energyNorm_tendsto hab (𝓝 y) (fun y' => J p y' - J p y)
    · intro y'
      exact cellEnergySpaceRawRepresentative_sub hab _ _ _ _ (hD p y') (hD p y)
    · exact hn
  · intro p hp y hy
    obtain ⟨L, hL, h0, h1⟩ := hd p hp y hy
    constructor
    · have he := hD (p.1 + 1, p.2) y
      rw [← h0] at he
      exact cellEnergySpaceRaw_directional_tendsto hab (J p) (D p) L y (Pi.single 0 1)
        (D (p.1 + 1, p.2) y) (hD p) he hL
    · have he := hD (p.1, p.2 + 1) y
      rw [← h1] at he
      exact cellEnergySpaceRaw_directional_tendsto hab (J p) (D p) L y (Pi.single 1 1)
        (D (p.1, p.2 + 1) y) (hD p) he hL

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleEvolution

/-! Complex linearity of the actual bounded mean-zero inverse relation. -/

/-- Bounded mean-zero inverse solutions scale with their forcing. -/
theorem cellInverse_complex_smul {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (r : ℂ) :
    IsCellInverseValue C (r • src) (r • F) (r • D) := by
  refine ⟨cellSolution_complex_smul hD.1 r, ?_, ?_⟩
  · intro t
    change (∫ x in AVenhance.unitCube, r • cellValue D t x) = 0
    rw [integral_smul]
    change r • cellMean (cellValue D t) = 0
    rw [hD.2.1 t, smul_zero]
  · exact (cellEnergyNorm_complex_smul univ r D
      (cellSolution_gradient_aestronglyMeasurable hD.1)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top hD.2.2)

/-! Linearity of the bounded all-time mean-zero inverse relation. -/

section
local instance cellInverseLinearProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Bounded mean-zero inverse solutions add with their forcing. -/
theorem cellInverse_add {C : CellCoefficients}
    {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C src' F' E) :
    IsCellInverseValue C (src + src') (F + F') (D + E) := by
  refine ⟨cellSolution_add hD.1 hE.1, ?_, ?_⟩
  · intro t
    change (∫ x in AVenhance.unitCube, cellValue D t x + cellValue E t x) = 0
    rw [integral_add ((hD.1.2.2.1 t (mem_univ _)).1.integrable (by norm_num))
      ((hE.1.2.2.1 t (mem_univ _)).1.integrable (by norm_num))]
    change cellMean (cellValue D t) + cellMean (cellValue E t) = 0
    rw [hD.2.1 t, hE.2.1 t, zero_add]
  · exact (cellEnergyNorm_add univ D E
      (cellSolution_gradient_aestronglyMeasurable hD.1)
      (cellSolution_gradient_aestronglyMeasurable hE.1)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hD.2.2, hE.2.2⟩)

/-- Bounded mean-zero inverse solutions scale with their forcing. -/
theorem cellInverse_smul {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (r : ℝ) :
    IsCellInverseValue C (r • src) (r • F) (r • D) := by
  refine ⟨cellSolution_smul hD.1 r, ?_, ?_⟩
  · intro t
    change (∫ x in AVenhance.unitCube, r • cellValue D t x) = 0
    rw [integral_smul]
    change r • cellMean (cellValue D t) = 0
    rw [hD.2.1 t, smul_zero]
  · exact (cellEnergyNorm_smul univ r D
      (cellSolution_gradient_aestronglyMeasurable hD.1)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top hD.2.2)
end

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual homogeneous Hilbert curves from pairs of public raw solutions with arbitrary common forcing. -/

/-- The public solution predicate itself makes a common-forcing difference a homogeneous energy curve. -/
theorem cellSolutionPair_to_homogeneous_Hilbert {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D)
    (h' : IsCellSolution (Icc a b) C src F D') :
    CellWeakHilbertCurve a b (fun t => cellRawTrace D t - cellRawTrace D' t)
      (fun t => cellH1Slice D t - cellH1Slice D' t)
      (fun t => cellDualDerivative C hG V hv hb t (cellH1Slice D t - cellH1Slice D' t) 0 (fun _ => 0)) := by
  have hs := (cellSolution_slice_memLp hab h).sub (cellSolution_slice_memLp hab h')
  refine ⟨(IsCellSolution.trace_continuous h).sub (IsCellSolution.trace_continuous h'), hs,
    cellDualDerivative_memLp C hG V k hv hb hκ hκb _ hs _ MemLp.zero _ (fun _ => MemLp.zero),
    ?_, ?_⟩
  · filter_upwards [cellSolution_trace_agrees h, cellSolution_trace_agrees h'] with t ht ht'
    rw [ht, ht', ← map_sub]
  · exact cellSolutionPair_Hilbert_increment C hG V hv hb src F D D' h h'

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every public raw cell solution satisfies the actual Hilbert variational equation. -/

/-- The public raw solution predicate discharges every premise of the weak Hilbert energy calculus. -/
theorem cellSolution_to_Hilbert_aePotential {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b))) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (cellRawSolutionDual C hG V hv hb src F D) :=
  ⟨IsCellSolution.trace_continuous h, cellSolution_slice_memLp hab h,
    cellSolution_dual_memLp_aePotential hab C hG V k hv hb hκ hκb src F hsrc hF D h,
    cellSolution_trace_agrees h,
    cellSolution_Hilbert_increment C hG V hv hb src F hsrc hF D h⟩

/-! Genuine conjugation preserves the bounded mean-zero all-time cell inverse relation. -/

theorem cellEnergyNorm_conjugate (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ) :
    cellEnergyNorm I (fun t => cellRawJetConj (D t)) = cellEnergyNorm I D := by
  unfold cellEnergyNorm cellUlNorm
  simp only [show ∀ t, cellValue (fun t => cellRawJetConj (D t)) t =
      (fun x => star (cellValue D t x)) from fun _ => rfl,
    cellL2Norm_conjugate, cellL2Norm_gradient_conjugate]

theorem cellInverse_conjugate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t x => star (src t x))
      (fun t => cellFluxConj (F t)) (fun t => cellRawJetConj (D t)) := by
  have hC : cellConjugateCoefficients ⟨G, v, 0, 0⟩ = ⟨G, v, 0, 0⟩ := by
    simp only [cellConjugateCoefficients, Pi.zero_apply, star_zero, neg_zero]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hC] using cellSolution_conjugate hD.1
  · intro t
    change (∫ x in AVenhance.unitCube, star (cellValue D t x)) = 0
    rw [cellIntegral_star]
    change star (cellMean (cellValue D t)) = 0
    rw [hD.2.1 t, star_zero]
  · rw [cellEnergyNorm_conjugate]
    exact hD.2.2

/-! Uniqueness of all public raw cell solution traces. -/

/-- All public solutions with the same initial raw value have the same L² trace at every time. -/
theorem cellActual_unique_raw {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D D' : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) C src F D)
    (hD' : IsCellSolution (Icc a b) C src F D')
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' a) :
    ∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  have h := cellSolution_to_Hilbert hab C hG V k hv hb hκ hκb src F hsrc hF D hD
  have h' := cellSolution_to_Hilbert hab C hG V k hv hb hκ hκb src F hsrc hF D' hD'
  have hi' : cellRawTrace D a = cellRawTrace D' a := Lp.ext
    ((cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab⟩).1).trans
      (hi.trans (cellRawTrace_ae D' a (hD'.2.2.1 a ⟨le_rfl, hab⟩).1).symm))
  have he := cellActualWeak_unique hab C hG V k hv hb hκb
    (cellSourceSlice src) (fun r j => cellSourceSlice (fun t x => F t x j) r)
    (cellRawTrace D) (cellRawTrace D') (cellH1Slice D) (cellH1Slice D') h h' hi'
  intro t ht
  exact (cellRawTrace_ae D t (hD.2.2.1 t ht).1).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) (he t ht))).trans
      (cellRawTrace_ae D' t (hD'.2.2.1 t ht).1))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual normalized graph identity as equality of H¹ Riesz dual derivatives. -/

theorem cellNormalizedGraph_dual (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
      (u + cellH1One) 0 0 =
    cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t u
      (cellNormalizedGraphSourceClass G v V hv hb θ κ t u)
      (cellNormalizedGraphFluxClass G θ t u) := by
  apply ext_inner_right ℝ
  intro z
  have hz := cellNormalizedGraph_generator G hG hv V hb θ κ t u z
  have hleft := cellDualComplexPair_actual ⟨fun t _ => G t, v, θ, κ⟩
    hG V hv.1 hb t (u + cellH1One) z 0 0
  have hright := cellDualComplexPair_actual ⟨fun t _ => G t, v, 0, 0⟩
    hG V hv.1 hb t u z
    (cellNormalizedGraphSourceClass G v V hv hb θ κ t u)
    (cellNormalizedGraphFluxClass G θ t u)
  have hp : cellDualComplexPair
      (cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
        (u + cellH1One) 0 0) z =
      cellDualComplexPair
        (cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t u
          (cellNormalizedGraphSourceClass G v V hv hb θ κ t u)
          (cellNormalizedGraphFluxClass G θ t u)) z := by
    rw [hleft, hright, hz]
    simp only [cellComplexSource, Pi.zero_apply, star_zero, cellComplexPair_zero_left,
      Finset.sum_const_zero, sub_zero, add_zero]
  simpa only [cellDualComplexPair_re] using congrArg Complex.re hp

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual analytic complete-energy families admit raw mixed complex norm jets of every finite order. -/

def cellEnergySpaceAnalyticRawJet {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b) (p : ℕ × ℕ) (ξ : Fin 2 → ℂ) :
    ℝ → RawJet2 1 ℂ :=
  cellEnergySpaceRawRepresentative hab (complexFrequencyCanonicalJet f p ξ)

theorem cellEnergySpaceAnalyticRawJet_represents {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b) (p : ℕ × ℕ) (ξ : Fin 2 → ℂ) :
    IsCellEnergySpaceRawRepresentative hab (complexFrequencyCanonicalJet f p ξ)
      (cellEnergySpaceAnalyticRawJet hab f p ξ) :=
  cellEnergySpaceRawRepresentative_spec hab _

theorem cellEnergySpaceAnalyticRawJet_zero_represents {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b) (ξ : Fin 2 → ℂ) :
    IsCellEnergySpaceRawRepresentative hab (f ξ) (cellEnergySpaceAnalyticRawJet hab f (0, 0) ξ) := by
  have h := cellEnergySpaceAnalyticRawJet_represents hab f (0, 0) ξ
  rw [complexFrequencyCanonicalJet_zero] at h
  exact h

theorem cellEnergySpaceAnalyticRawJet_isNormJetFamily {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b) (U : Set (Fin 2 → ℂ))
    (hf : AnalyticOnNhd ℂ f U) (K : ℕ) :
    IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Icc a b)) K U (cellEnergySpaceAnalyticRawJet hab f) := by
  apply cellEnergySpaceRaw_isNormJetFamily_of_derivatives hab K U (complexFrequencyCanonicalJet f)
  · exact cellEnergySpaceAnalyticRawJet_represents hab f
  · intro p _ ξ hξ
    exact (complexFrequencyCanonicalJet_analyticAt f U hf p ξ hξ).continuousAt
  · intro p _ ξ hξ
    exact complexFrequencyCanonicalJet_derivatives f U hf p ξ hξ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every homogeneous raw solution with an almost measurable scalar gauge satisfies the genuine weak Hilbert equation. -/

theorem cellRawHomogeneous_to_Hilbert_aePotential {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) C (fun _ _ => 0) (fun _ _ => 0) D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative C hG V hv hb t (cellH1Slice D t) 0 0) := by
  have hh := cellSolution_to_Hilbert_aePotential hab C hG V k hv hb hκ hκb
    (fun _ _ => 0) (fun _ _ => 0) MemLp.zero MemLp.zero D h
  change CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
    (fun t => cellDualDerivative C hG V hv hb t (cellH1Slice D t)
      (cellSourceSlice (fun _ _ => 0) t)
      (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hh
  simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hh

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Localized real energy estimate for every public raw cell solution. -/

/-- The actual raw solution satisfies the real energy inequality using source energy only up to t. -/
theorem cellActual_raw_real_energy {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) C src F D)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖cellRawTrace D t‖ ^ 2 + (1 / 2) *
      (∫ r in a..t, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D r)‖ ^ 2) ≤
    Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (t - a)) *
      (‖cellRawTrace D a‖ ^ 2 + (∫ r in a..t, ‖cellSourceSlice src r‖ ^ 2) +
        9 * ∫ r in a..t, ∑ j, ‖cellSourceSlice (fun s x => F s x j) r‖ ^ 2) := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hS := (cellSourceSlice_memLp (Icc a b) src hsrc).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have hQ (j : Fin 2) := (cellSourceSlice_memLp (Icc a b) (fun s x => F s x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have h := (cellSolution_to_Hilbert hab C hG V k hv hb hκ hκb src F hsrc hF D hD).mono hsub
  have he := cellActualWeak_energy_bound ht.1 C hG V k hv hb hκb
    (cellSourceSlice src) (fun r j => cellSourceSlice (fun s x => F s x j) r) hS hQ
    (cellRawTrace D) (cellH1Slice D) h t ⟨ht.1, le_rfl⟩
  have hiS := cellTime_normSq_intervalIntegrable ht.1 hS
  have hiQ := (cellTime_normSq_intervalIntegrable ht.1 (hQ 0)).add
    (cellTime_normSq_intervalIntegrable ht.1 (hQ 1))
  have hiF : IntervalIntegrable (fun r => ∑ j, ‖cellSourceSlice (fun s x => F s x j) r‖ ^ 2)
      volume a t := by simpa only [Fin.sum_univ_two, Pi.add_apply] using hiQ
  have hsplit := intervalIntegral.integral_add hiS (hiF.const_mul 9)
  rw [hsplit, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  calc
    _ ≤ _ := he
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The constant test identifies the exact scalar mean equations for Bloch forcing and evolution. -/

theorem cellBlochLinear_generator_one (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun t _ => G t, v, θ, 0⟩ hG V hv.1 hb t u cellH1One =
      cellMean (cellBlochLinearSourceClass G v V hv hb θ t u) := by
  rw [cellBlochLinear_generator G hG hv V hb, cellComplexGenerator_one hG hv,
    cellComplexSource_one, zero_add]

theorem cellComplexSource_bloch_one (θ : Fin 2 → ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellComplexSource θ S F cellH1One =
      cellMean S + ∑ j : Fin 2, Complex.I * θ j * cellMean (F j) := by
  have hshift (j : Fin 2) : cellShiftedDerivativeCLM (fun i => star (θ i)) j cellH1One =
      cellScalarCLM (Complex.I * star (θ j)) (cellConstantCLM 1) := by
    simp [cellShiftedDerivativeCLM, cellH1One_derivative, cellH1One_value]
  simp only [cellComplexSource, cellH1One_value, hshift, cellComplexPair_scalar_right,
    cellComplexPair_one, star_mul, star_star, show star Complex.I = -Complex.I from Complex.conj_I,
    Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The exact mean of the Bloch scalar source separates drift coupling from the quadratic metric symbol. -/

theorem cellMeanCLM_complex_scalar (c : ℂ) (u : ComplexCellL2) :
    cellMeanCLM (cellScalarCLM c u) = c * cellMeanCLM u := by
  rw [cellMeanCLM_apply, ← cellComplexPair_one, cellComplexPair_scalar_left,
    cellComplexPair_one, cellMeanCLM_apply]

theorem cellBlochLinearSourceClass_mean (η Cw : ℝ) (hη0 : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellMean (cellBlochLinearSourceClass G v V hv hb (fun j => (Real.sqrt η : ℂ) * ξ j) t u) =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM u) -
      (η : ℂ) * fibreQuad (G t) ξ * cellMean (torusHkValueCLM u) := by
  let M := cellCoefficientCLM (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
    (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
    (fibreDriftCoupling_norm_le η Cw v hw ξ t)
  let U := torusHkValueCLM u
  have he : cellBlochLinearSourceClass G v V hv hb (fun j => (Real.sqrt η : ℂ) * ξ j) t u =
      cellScalarCLM (-Complex.I) (M U) - cellScalarCLM ((η : ℂ) * fibreQuad (G t) ξ) U := by
    apply Lp.ext
    filter_upwards [cellBlochLinearSourceClass_ae G hv V hb
      (fun j => (Real.sqrt η : ℂ) * ξ j) t u,
      cellCoefficientCLM_ae (fibreDriftCoupling η v ξ t)
        (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
        (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
        (fibreDriftCoupling_norm_le η Cw v hw ξ t) U,
      cellScalarCLM_ae (-Complex.I) (M U),
      cellScalarCLM_ae ((η : ℂ) * fibreQuad (G t) ξ) U,
      Lp.coeFn_sub (cellScalarCLM (-Complex.I) (M U))
        (cellScalarCLM ((η : ℂ) * fibreQuad (G t) ξ) U)] with x hs hm hc hq hsub
    rw [hs, hsub]
    change _ = cellScalarCLM (-Complex.I) (M U) x -
      cellScalarCLM ((η : ℂ) * fibreQuad (G t) ξ) U x
    rw [hc, hq, hm, fibreBloch_drift_coupling, fibreBloch_metric_quadratic η hη0]
    dsimp only [U]
    ring
  rw [← cellMeanCLM_apply, he, map_sub, cellMeanCLM_complex_scalar, cellMeanCLM_complex_scalar]
  change -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t U -
    ((η : ℂ) * fibreQuad (G t) ξ) * cellMeanCLM U = _
  rw [cellMeanCLM_apply]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The normalized Bloch equation has an exact mean identity including its actual scalar gauge. -/

theorem cellDualComplexPair_bloch_potential_one (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩
      hG V hv.1 hb t u S F) cellH1One =
      cellMean (cellBlochLinearSourceClass G v V hv hb θ t u) +
      κ t * cellMean (torusHkValueCLM u) + cellMean S +
      ∑ j : Fin 2, Complex.I * θ j * cellMean (F j) := by
  rw [cellDualComplexPair_actual, cellComplexGenerator_potential,
    cellComplexSource_bloch_one, cellH1One_value, cellComplexPair_one]
  change cellComplexGenerator ⟨fun t _ => G t, v, θ, 0⟩ hG V hv.1 hb t u cellH1One +
    κ t * cellMean (torusHkValueCLM u) +
    (cellMean S + ∑ j : Fin 2, Complex.I * θ j * cellMean (F j)) = _
  rw [cellBlochLinear_generator_one G hG hv V hb]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Every actual quiet mean-zero graph trajectory decays at a rate stronger than the required buffer. -/

theorem cellWeakGraphFlux_meanZero_decay {a b : ℝ} (hab : a ≤ b)
    (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : 1024 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t (slice t) 0
      (cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t (slice t))))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖u a‖ ^ 2 := by
  apply (h.energy_strongTime hab).scalar_decay hab (6 * Real.pi ^ 2)
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  have hd := cellGraphFlux_meanZero_dissipation η hη G hG hg hgsmall hv V hb ξ hξ
    t (slice t) hmean
  rw [ht]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The extended-real energy estimate for every public raw cell solution. -/

/-- Every public cell solution satisfies the energy bound with universal constants 300, 1/2, 9. -/
theorem cellActual_raw_energy {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) C src F D)
    (u₀ : Vec 2 → ℂ) (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] u₀)
    (t : ℝ) (ht : t ∈ Icc a b) :
    cellL2Norm (cellValue D t) ^ 2 + ENNReal.ofReal (1 / 2 : ℝ) *
      (∫⁻ r in Icc a t, cellL2Norm (cellGradient (D r)) ^ 2) ≤
    ENNReal.ofReal (Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (t - a))) *
      (cellL2Norm u₀ ^ 2 + (∫⁻ r in Icc a t, cellL2Norm (src r) ^ 2) +
        ENNReal.ofReal 9 * ∫⁻ r in Icc a t, cellL2Norm (F r) ^ 2) := by
  have htrace := cellRawTrace_ae D t (hD.2.2.1 t ht).1
  have hinit := (cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab⟩).1).trans hi
  rw [cellL2Norm_eq_of_class _ _ htrace, ← ENNReal.ofReal_pow (norm_nonneg _),
    cellL2Norm_eq_of_class _ _ hinit, ← ENNReal.ofReal_pow (norm_nonneg _),
    cellSolution_gradient_energy_integral hab ⟨le_rfl, hab⟩ ht ht.1 hD,
    cellSource_energy_integral ⟨le_rfl, hab⟩ ht ht.1 src hsrc,
    cellFlux_energy_integral ⟨le_rfl, hab⟩ ht ht.1 F hF]
  have hGint : 0 ≤ ∫ r in a..t, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D r)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hSint : 0 ≤ ∫ r in a..t, ‖cellSourceSlice src r‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
  have hFint : 0 ≤ ∫ r in a..t, ∑ j, ‖cellSourceSlice (fun s x => F s x j) r‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact cellEnergy_ofReal (sq_nonneg _) (sq_nonneg _) hGint hSint hFint
    (by norm_num) (by norm_num) (Real.exp_nonneg _)
    (cellActual_raw_real_energy hab C hG V k hv hb hκ hκb src F hsrc hF D hD t ht)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Complex linearity and constant annihilation for the actual Bloch drift-to-mean coupling. -/

theorem cellBlochDriftMeanCLM_complex_scalar (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (c : ℂ) (u : ComplexCellL2) :
    cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (cellScalarCLM c u) =
      c * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t u := by
  simp only [cellBlochDriftMeanCLM, ContinuousLinearMap.comp_apply,
    cellCoefficientCLM_complex_scalar, cellMeanCLM_complex_scalar]

theorem cellBlochDriftMeanCLM_one (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (cellConstantCLM 1) = 0 := by
  rw [cellBlochDriftMeanCLM_apply]
  calc
    _ = cellMean (fibreDriftCoupling η v ξ t) := by
      unfold cellMean
      apply integral_congr_ae
      filter_upwards [cellConstantCLM_ae 1] with x hx
      rw [hx, mul_one]
    _ = 0 := fibreDriftCoupling_mean_zero η hv hm ξ t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniform drift-independent trace bounds for finite-past mean-zero weak solutions. -/

/-- Finite-past mean-zero traces obey a uniform bound independent of the time horizon and drift size. -/
theorem cellWeakActual_ul_trace_bound {a b : ℝ} (hab : a ≤ b) (I : Set ℝ)
    (hI : Icc a b ⊆ I)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm I f < ⊤) (hF : cellUlNorm I F < ⊤)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t)
        (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ ‖u a‖ ^ 2 +
      (4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2) /
        (1 - Real.exp (-(Real.pi ^ 2))) +
      (4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2) := by
  have hef := cellUl_interval_integral_lt_top I f hf a b
  have heF := cellUl_interval_integral_lt_top I F hF a b
  rw [inter_eq_left.mpr hI] at hef heF
  have hi := cellMeanFreeForcingBudget_integrable (Icc a b) f F hfm
    (cellSource_memLp_product (Icc a b) f hfm hef)
    (cellSource_memLp_product (Icc a b) F hFm heF)
  have hfi : IntervalIntegrable (cellMeanFreeForcingBudget f F) volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    exact hi.mono_set Ioc_subset_Icc_self
  apply (h.energy_strongTime hab).scalar_ul_bound hab
    (sq_pos_of_pos Real.pi_pos) (by positivity) (sq_nonneg _) _ hfi
    (Filter.Eventually.of_forall (cellMeanFreeForcingBudget_nonneg f F))
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    have hmean := hm t hti
    rw [ht] at hmean
    rw [cellDualDerivative_pairing, ht]
    unfold cellMeanFreeForcingBudget
    have he := cellUnshifted_source_energy_bound hG hv V hb t (slice t) hmean
      (cellSourceSlice (fun r => cellQ0 (f r)) t) (fun j => cellSourceSlice (fun r x => F r x j) t)
    have hn : 0 ≤ ∑ j : Fin 2, ‖cellDerivativeCLM j (slice t)‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  · intro s hs t ht hst hl
    exact cellMeanFreeForcingBudget_short_bound I f F hfm hFm hf hF hst hl
      ((Icc_subset_Icc hs.1 ht.2).trans hI)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual graph symbol cancels the scalar mean term in the normalized triangular equation. -/

theorem cellBloch_normalized_mean_triangular (η Cw : ℝ) (hη0 : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (ρ z : ComplexCellL2)
    (hdecomp : torusHkValueCLM u =
      cellScalarCLM (cellMean (torusHkValueCLM u)) (ρ + cellConstantCLM 1) + z) :
    cellMean (cellBlochLinearSourceClass G v V hv hb (fun j => (Real.sqrt η : ℂ) * ξ j) t u) -
      (-(η : ℂ) * fibreQuad (G t) ξ -
        Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t ρ) *
      cellMean (torusHkValueCLM u) =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t z := by
  have hd : cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM u) =
      cellMean (torusHkValueCLM u) * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t ρ +
      cellBlochDriftMeanCLM η Cw hCw hv hw ξ t z := by
    calc
      _ = cellBlochDriftMeanCLM η Cw hCw hv hw ξ t
          (cellScalarCLM (cellMean (torusHkValueCLM u)) (ρ + cellConstantCLM 1) + z) :=
        congrArg (cellBlochDriftMeanCLM η Cw hCw hv hw ξ t) hdecomp
      _ = _ := by
        rw [map_add, cellBlochDriftMeanCLM_complex_scalar, map_add,
          cellBlochDriftMeanCLM_one η Cw hCw hv hw hm ξ t, add_zero]
  rw [cellBlochLinearSourceClass_mean η Cw hη0 hCw G hv hw V hb, hd]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual Bloch trajectories satisfy the scalar mean equation at the weak time regularity used by the word operators. -/

theorem cellWeakBloch_mean_strongTime {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t (slice t) (S t) (F t))) :
    StrongTimeRegularity a b (fun t => cellMean (u t)) (fun t =>
      cellMean (cellBlochLinearSourceClass G v V hv hb θ t (slice t)) +
      κ t * cellMean (torusHkValueCLM (slice t)) + cellMean (S t) +
      ∑ j : Fin 2, Complex.I * θ j * cellMean (F t j)) := by
  have he := h.mean_strongTime hab
  simp_rw [cellDualComplexPair_bloch_potential_one G hG hv V hb] at he
  exact he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Public mean-zero cell difference decay with arbitrary common forcing. -/

/-- Common forcing cancels before the actual energy identity; no separate source regularity is required. -/
theorem cellRaw_meanZero_difference_decay_arbitrary_source {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) ⟨G, v, 0, 0⟩ src F D)
    (h' : IsCellSolution (Icc a b) ⟨G, v, 0, 0⟩ src F D')
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0)
    (hm' : ∀ t ∈ Icc a b, cellMean (cellValue D' t) = 0) :
    ∀ t ∈ Icc a b, ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (t - a)) * ‖cellRawTrace D a - cellRawTrace D' a‖ ^ 2 := by
  apply cellWeakHomogeneous_meanZero_decay hab hG hv V hb _ _
    (cellSolutionPair_to_homogeneous_Hilbert hab ⟨G, v, 0, 0⟩ hG V 0 hv.1 hb
      measurable_const (fun _ => by simp) src F D D' h h')
  intro t ht
  have hd : cellMean (cellRawTrace D t) = 0 :=
    (integral_congr_ae (cellRawTrace_ae D t (h.2.2.1 t ht).1)).trans (hm t ht)
  have hw : cellMean (cellRawTrace D' t) = 0 :=
    (integral_congr_ae (cellRawTrace_ae D' t (h'.2.2.1 t ht).1)).trans (hm' t ht)
  rw [← cellMeanCLM_apply, map_sub, cellMeanCLM_apply, cellMeanCLM_apply, hd, hw, sub_self]

/-- Two public finite-past mean-zero solutions forget arbitrary common forcing at the stated norm rate. -/
theorem cellFinitePast_decay (s : ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Ici s) ⟨G, v, 0, 0⟩ src F D)
    (h' : IsCellSolution (Ici s) ⟨G, v, 0, 0⟩ src F D')
    (hm : ∀ t, s ≤ t → cellMean (cellValue D t) = 0)
    (hm' : ∀ t, s ≤ t → cellMean (cellValue D' t) = 0) :
    ∀ t, s ≤ t → cellL2Norm (fun x => cellValue D t x - cellValue D' t x) ≤
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (t - s) / 2)) *
        cellL2Norm (fun x => cellValue D s x - cellValue D' s x) := by
  obtain ⟨V, hV⟩ := hv.2.1
  intro t hst
  have hsub : Icc s t ⊆ Ici s := fun _ ht => ht.1
  have hd := cellRaw_meanZero_difference_decay_arbitrary_source hst hG hv V hV src F D D'
    (cellSolution_restrict hsub ordConnected_Icc h) (cellSolution_restrict hsub ordConnected_Icc h')
    (fun r hr => hm r hr.1) (fun r hr => hm' r hr.1) t ⟨hst, le_rfl⟩
  have hnorm := scalar_norm_decay_of_sq (norm_nonneg _) (norm_nonneg _) (sq_nonneg Real.pi)
    (sub_nonneg.mpr hst) hd
  have hrep (r : ℝ) (hr : s ≤ r) :
      ((cellRawTrace D r - cellRawTrace D' r : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x => cellValue D r x - cellValue D' r x :=
    (Lp.coeFn_sub _ _).trans ((cellRawTrace_ae D r (h.2.2.1 r hr).1).sub
      (cellRawTrace_ae D' r (h'.2.2.1 r hr).1))
  rw [cellL2Norm_eq_of_class _ _ (hrep t hst), cellL2Norm_eq_of_class _ _ (hrep s le_rfl),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hnorm

/-! Actual squared-trace decay of mean-zero public cell solutions with common L² forcing. -/

/-- Public mean-zero solution traces satisfy the homogeneous difference decay on finite intervals. -/
theorem cellRaw_meanZero_difference_decay {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D D' : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) ⟨G, v, 0, 0⟩ src F D)
    (h' : IsCellSolution (Icc a b) ⟨G, v, 0, 0⟩ src F D')
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0)
    (hm' : ∀ t ∈ Icc a b, cellMean (cellValue D' t) = 0) :
    ∀ t ∈ Icc a b, ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (t - a)) * ‖cellRawTrace D a - cellRawTrace D' a‖ ^ 2 := by
  have hu := cellSolution_to_Hilbert hab ⟨G, v, 0, 0⟩ hG V 0 hv.1 hb
    measurable_const (fun _ => by simp) src F hsrc hF D h
  have hw := cellSolution_to_Hilbert hab ⟨G, v, 0, 0⟩ hG V 0 hv.1 hb
    measurable_const (fun _ => by simp) src F hsrc hF D' h'
  apply cellWeakActual_difference_decay hab hG hv V hb
    (cellSourceSlice src) (fun t j => cellSourceSlice (fun r x => F r x j) t)
    (cellRawTrace D) (cellRawTrace D') (cellH1Slice D) (cellH1Slice D') hu hw
  · intro t ht
    exact (integral_congr_ae (cellRawTrace_ae D t (h.2.2.1 t ht).1)).trans (hm t ht)
  · intro t ht
    exact (integral_congr_ae (cellRawTrace_ae D' t (h'.2.2.1 t ht).1)).trans (hm' t ht)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Metric
namespace AVRegularity.CycleEvolution

/-! Quantitative raw jet estimates from uniformly bounded analytic readouts. -/

theorem cellEnergySpaceRawJet_cauchy_bound {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b) (ξ : Fin 2 → ℂ)
    (θ : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball ξ R))
    (htrace : ∀ ζ ∈ ball ξ R, ‖cellEnergySpaceTraceCLM a b (f ζ)‖ ≤ M)
    (hgrad : ∀ ζ ∈ ball ξ R, ∀ j : Fin 2,
      ‖cellEnergySpaceShiftedDerivativeCLM hab θ j (f ζ)‖ ≤ M)
    (p : ℕ × ℕ) :
    fibreXNorm θ (Icc a b) (cellEnergySpaceAnalyticRawJet hab f p ξ) ≤
      ENNReal.ofReal (3 * analyticBallDerivativeConstant (p.1 + p.2) * M / R ^ (p.1 + p.2)) := by
  have hw (i : Fin (p.1 + p.2)) : ‖complexFrequencyCanonicalWord p i‖ ≤ 1 :=
    (complexFrequencyCanonicalWord_norm p i).le
  have ht := complexFrequencyWordJet_readout_bound f (cellEnergySpaceTraceCLM a b)
    ξ R M hR hf htrace (p.1 + p.2) (complexFrequencyCanonicalWord p) hw
  have hg (j : Fin 2) := complexFrequencyWordJet_readout_bound f
    (cellEnergySpaceShiftedDerivativeCLM hab θ j) ξ R M hR hf
    (fun ζ hζ => hgrad ζ hζ j) (p.1 + p.2) (complexFrequencyCanonicalWord p) hw
  have hr := cellEnergySpaceRaw_fibreXNorm_le_readouts hab
    (complexFrequencyCanonicalJet f p ξ) (cellEnergySpaceAnalyticRawJet hab f p ξ)
    (cellEnergySpaceAnalyticRawJet_represents hab f p ξ) θ
  apply hr.trans
  apply ENNReal.ofReal_le_ofReal
  change ‖cellEnergySpaceTraceCLM a b (complexFrequencyWordJet f (p.1 + p.2)
      (complexFrequencyCanonicalWord p) ξ)‖ +
    ‖cellEnergySpaceShiftedDerivativeCLM hab θ 0 (complexFrequencyWordJet f (p.1 + p.2)
      (complexFrequencyCanonicalWord p) ξ)‖ +
    ‖cellEnergySpaceShiftedDerivativeCLM hab θ 1 (complexFrequencyWordJet f (p.1 + p.2)
      (complexFrequencyCanonicalWord p) ξ)‖ ≤ _
  calc
    _ ≤ _ := add_le_add (add_le_add ht (hg 0)) (hg 1)
    _ = _ := by ring

end AVRegularity.CycleEvolution
end
