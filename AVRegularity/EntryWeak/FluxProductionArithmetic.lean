-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
public import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! Every natural output piece has uniformly bounded normalized forward and inverse spatial jets. -/

theorem weak_natural_piece_inverse_eq (D : OCData) (M i : ℕ) (p : ℤ) (P : ChartPiece)
    (hP : IsNaturalPiece D M i p P) (t : ℝ) :
    ⇑(P.material t).symm = fun x => D.flowOf (i - 1) (D.slotAnchor i p) x t := by
  have he : P.material t = streamFlowHomeomorph (D.hΦ (i - 1)) t (D.slotAnchor i p) := by
    apply Homeomorph.ext
    intro x
    exact congrFun (hP.2.2.2.2 t) x
  rw [he]
  rfl

theorem weak_natural_piece_chart_jets (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (M i : ℕ) (hi : 2 ≤ i) (p : ℤ) (P : ChartPiece) (hP : IsNaturalPiece D M i p P)
    (hsmall : ocTauPP D.α D.q D.Λ i ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ (i - 1))⁻¹)
    (heps : D.eps i ≤ D.eps (i - 1)) (t : ℝ) (ht : t ∈ P.output)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (inverse : Bool) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
      (rescaledChart (D.eps i) (if inverse then ⇑(P.material t).symm else ⇑(P.material t))) x‖ ≤
      weakBaseChartJetBudget K := by
  have htime : |t - D.slotAnchor i p| ≤ 2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ (i - 1))⁻¹ := by
    apply (weak_lift_anchor_distance D.α D.q (by omega) i p t ?_).trans hsmall
    rwa [hP.2.1] at ht
  have he : 0 < D.eps i := Construction.Stream.ocEpsilon_pos (by omega)
  cases inverse with
  | false =>
    rw [hP.2.2.2.2 t]
    have hb := scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      (i - 1) (by omega) (D.slotAnchor i p) t htime (D.eps i) he heps 0 0 n hn x
    simp only [zero_add, sub_zero] at hb
    exact hb.trans (weakBaseChartJetBudget_bounds_order K n hnK)
  | true =>
    rw [weak_natural_piece_inverse_eq D M i p P hP t]
    have hb := scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      (i - 1) (by omega) t (D.slotAnchor i p) (by simpa only [abs_sub_comm] using htime)
      (D.eps i) he heps 0 0 n hn x
    simp only [zero_add, sub_zero] at hb
    exact hb.trans (weakBaseChartJetBudget_bounds_order K n hnK)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Uniqueness of all public raw cell solution traces. -/

/-- All public solutions with the same initial raw value have the same L² trace at every time. -/
theorem dataActual_unique_raw {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D D' : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) (dataCoefficients P) src F D)
    (hD' : IsCellSolution (Icc a b) (dataCoefficients P) src F D')
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' a) :
    ∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  have h := dataSolution_to_Hilbert hab P src F hsrc hF D hD
  have h' := dataSolution_to_Hilbert hab P src F hsrc hF D' hD'
  have hi' : cellRawTrace D a = cellRawTrace D' a := Lp.ext
    ((cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab⟩).1).trans
      (hi.trans (cellRawTrace_ae D' a (hD'.2.2.1 a ⟨le_rfl, hab⟩).1).symm))
  have he := dataActualWeak_unique hab P
    (cellSourceSlice src) (fun r j => cellSourceSlice (fun t x => F t x j) r)
    (cellRawTrace D) (cellRawTrace D') (cellH1Slice D) (cellH1Slice D') h h' hi'
  intro t ht
  exact (cellRawTrace_ae D t (hD.2.2.1 t ht).1).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) (he t ht))).trans
      (cellRawTrace_ae D' t (hD'.2.2.1 t ht).1))

/-! Real data produce a real molecular trace by uniqueness and conjugation. -/

theorem dataRaw_real_trace {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (g : ℝ → Vec 2 → ℝ) (c₀ : Vec 2 → ℝ)
    (hg : MemLp (fun p : ℝ × Vec 2 => (g p.1 p.2 : ℂ)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P)
      (fun t x => (g t x : ℂ)) (fun _ _ => 0) D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] fun x => (c₀ x : ℂ)) :
    ∀ t ∈ Icc a b, (fun x => ((cellValue D t x).re : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue D t := by
  have hf : (fun t : ℝ => cellFluxConj (fun _ : Vec 2 => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)))) =
      (fun _ _ => 0) := by
    funext t x
    apply PiLp.ext
    intro j
    simp [cellFluxConj]
  have hC : cellConjugateCoefficients (dataCoefficients P) = dataCoefficients P := by
    unfold cellConjugateCoefficients dataCoefficients molecularCoefficients
    congr 1
    · funext j
      simp
    · funext t
      simp
  have hc : IsCellSolution (Icc a b) (dataCoefficients P)
      (fun t x => (g t x : ℂ)) (fun _ _ => 0) (fun t => cellRawJetConj (D t)) := by
    simpa [hC, hf] using
      cellSolution_conjugate hD
  have hi' : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fun t => cellRawJetConj (D t)) a := by
    filter_upwards [hi] with x hx
    change cellValue D a x = star (cellValue D a x)
    rw [hx]
    simp
  have hu := dataActual_unique_raw hab P (fun t x => (g t x : ℂ)) (fun _ _ => 0)
    hg MemLp.zero D (fun t => cellRawJetConj (D t)) hD hc hi'
  intro t ht
  filter_upwards [hu t ht] with x hx
  change cellValue D t x = star (cellValue D t x) at hx
  have him := congrArg Complex.im hx
  change (cellValue D t x).im = -(cellValue D t x).im at him
  apply Complex.ext
  · rfl
  · change 0 = (cellValue D t x).im
    linarith

/-! Uniqueness of scalar classical inverse fields follows from uniqueness of their energy classes. -/

theorem dataScalarInverse_unique {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (r : ℕ) (c₀ : Vec 2 → ℝ) (g : ℝ → Vec 2 → ℝ)
    (hg : MemLp (fun p : ℝ × Vec 2 => (g p.1 p.2 : ℂ)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (c c' : ℝ → Vec 2 → ℝ)
    (hc : IsCellFieldInverse P.G P.v r a b c₀ g c)
    (hc' : IsCellFieldInverse P.G P.v r a b c₀ g c') :
    ∀ t ∈ Icc a b, c t =ᵐ[volume.restrict AVenhance.unitCube] c' t := by
  have h := hc.2 (ContinuousLinearMap.id ℝ ℝ)
  have h' := hc'.2 (ContinuousLinearMap.id ℝ ℝ)
  have hi := h.2.2.1.trans h'.2.2.1.symm
  have hu := dataActual_unique_raw hab P (fun t x => (g t x : ℂ)) (fun _ _ => 0)
    hg MemLp.zero _ _ h.1 h'.1 hi
  intro t ht
  filter_upwards [hu t ht] with x hx
  exact Complex.ofReal_injective hx

/-! Uniqueness fixes the periodic classical representative, even at regularity order zero. -/

theorem periodicCell_ae_eq_pointwise (f g : Vec 2 → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] g) : f = g := by
  have hopen : IsOpen AVenhance.unitCube :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hcell : EqOn f g AVenhance.unitCube :=
    Measure.eqOn_open_of_ae_eq he hopen hf.continuousOn hg.continuousOn
  have hcl := hcell.closure hf hg
  funext x
  let y : Vec 2 := fun i => Int.fract (x i)
  let n : Fin 2 → ℤ := fun i => Int.floor (x i)
  have hy : y ∈ closure AVenhance.unitCube := by
    rw [AVenhance.unitCube, closure_pi_set]
    intro i _
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have heq : y + AVenhance.latticeShift n = x := by
    funext i
    simp only [Pi.add_apply, y, n, AVenhance.latticeShift, Int.fract]
    ring
  have hp := hfp n y
  have hq := hgp n y
  rw [heq] at hp hq
  exact hp.trans ((hcl hy).trans hq.symm)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The sharp homogeneous molecular bound for public raw solution traces. -/

theorem dataRawHomogeneous_to_Hilbert {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) (dataCoefficients P)
      (fun _ _ => 0) (fun _ _ => 0) D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => dataDualDerivative P t (cellH1Slice D t) 0 (fun _ => 0)) := by
  have hh := dataSolution_to_Hilbert hab P (fun _ _ => 0) (fun _ _ => 0)
    MemLp.zero MemLp.zero D h
  change CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
    (fun t => dataDualDerivative P t (cellH1Slice D t)
      (cellSourceSlice (fun _ _ => 0) t)
      (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hh
  simpa only [cellSourceSlice_zero, PiLp.zero_apply] using hh

theorem dataRaw_homogeneous_decay {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) (dataCoefficients P)
      (fun _ _ => 0) (fun _ _ => 0) D)
    (hm : ∀ t ∈ Icc a b, cellMean (cellValue D t) = 0) :
    ∀ t ∈ Icc a b, ‖cellRawTrace D t‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖cellRawTrace D a‖ ^ 2 := by
  apply dataWeak_homogeneous_decay hab P hv _ _
    (dataRawHomogeneous_to_Hilbert hab P D h)
  filter_upwards [h.2.1, ae_restrict_mem measurableSet_Icc] with t ht hti
  exact (integral_congr_ae (cellH1Slice_value_ae D t ht)).trans (hm t hti)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The sharp molecular spectral gap implies the requested real scalar decay. -/

theorem dataScalarInverse_decay {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v) (r : ℕ) (ω : ℝ)
    (hω : ω < 3 * Real.pi ^ 2 / 2) (c₀ : Vec 2 → ℝ) (c : ℝ → Vec 2 → ℝ)
    (hc : IsCellFieldInverse P.G P.v r a b c₀ (fun _ _ => 0) c) :
    ∀ t ∈ Icc a b, ∫ x in AVenhance.unitCube, c t x ^ 2 ≤
      Real.exp (-(2 * ω * (t - a))) * ∫ x in AVenhance.unitCube, c₀ x ^ 2 := by
  have h := hc.2 (ContinuousLinearMap.id ℝ ℝ)
  let D := cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c
  have hd := dataRaw_homogeneous_decay hab P hv D h.1 h.2.1
  have hi : (cellRawTrace D a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c₀ x : ℂ) :=
    (cellRawTrace_ae D a (h.1.2.2.1 a ⟨le_rfl, hab⟩).1).trans h.2.2.1
  intro t ht
  have he : (cellRawTrace D t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c t x : ℂ) := cellRawTrace_ae D t (h.1.2.2.1 t ht).1
  rw [← realTrace_square _ _ he, ← realTrace_square _ _ hi]
  apply (hd t ht).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hcoef : 2 * ω ≤ 6 * Real.pi ^ 2 := by
    have hp := sq_nonneg Real.pi
    linarith
  have he := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr ht.1)
  linarith only [he]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Genuine joint reserves for the actual pulse and each molecular metric entry. -/

def pulseJointSourceReserve (H : ℕ) {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) :
    JointSourceReserve H (fun t z _ => ocPulseCellDrift α q Λ ζ m ν k t z) :=
  fastIndependentJointSourceReserve H _
    (fun t => (normalizedPulseDrift_contDiff hΛ hν hk t).of_le (by simp))
    (fun t => normalizedPulseDrift_periodic hΛ hν hk t)
    (normalizedPulseDrift_joint_continuous hΛ hν hζ hk).measurable
    (fun _ => (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H)
    (fun _ => mul_nonneg (div_nonneg (Real.rpow_nonneg
      (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le)
      (pulseFastDerivativeConstant_nonneg H))
    (fun n hn t z => normalizedPulseDrift_vector_fast_bound hΛ hν hζ hk H n hn t z)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Higher Sobolev control of the original finite molecular curves. -/

def dataWeightedFourierCLM (N K : ℕ) (ρ : ℝ) :
    ComplexCellL2 →L[ℝ] JetL2 (volume.restrict AVenhance.unitCube) K ℂ :=
  (plainWeightedSynthesisCLM N Unit.unit K ρ).comp (dataFourierCoordinatesCLM N)

@[simp] theorem dataWeightedFourierCLM_apply (N K : ℕ) (ρ : ℝ) (u : ComplexCellL2) :
    dataWeightedFourierCLM N K ρ u = factorialWeightedJet ρ (dataFourierHighCLM N K u).val := by
  simp only [dataWeightedFourierCLM, ContinuousLinearMap.comp_apply,
    plainWeightedSynthesisCLM_apply, dataFourierHighCLM, dataPlainSynthesisCLM_apply]

theorem dataFinite_high_energy_production (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (u du : CellGalerkinSpace (E := ℂ) N) (S : TorusHk K ℂ)
    (heq : ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N du) (cellGalerkinValue N z) =
        dataGeneratorForm P t u.val z.val + inner ℝ (S.val (valueIndex2 K)) (cellGalerkinValue N z)) :
    2 * inner ℝ (dataWeightedFourierCLM N K ρ (cellGalerkinValue N u))
        (dataWeightedFourierCLM N K ρ (cellGalerkinValue N du)) ≤
      (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
        finiteTransportBudget (E := ℂ) K Cv j) ^ 2) *
        ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N u)‖ ^ 2 + factorialNormSq ρ S.val := by
  have hd := dataFinite_dual_coordinates N K P t Cv hCv hv hp hb u du S heq
  simp only [dataWeightedFourierCLM, ContinuousLinearMap.comp_apply,
    plainWeightedSynthesisCLM_apply, hd]
  rw [real_inner_comm, factorialWeightedJet_normSq]
  have hh := molecularFiniteSource_energy_bound N K ρ hρ P t Cv hCv hv hp hb
    (dataFourierCoordinatesCLM N (cellGalerkinValue N u)) S
  have hn : 0 ≤ gradFactorialNormSq ρ
      (coupledPlainSynthesis N Unit.unit (K + 1)
        (dataFourierCoordinatesCLM N (cellGalerkinValue N u))).val := by
    rw [← coupledPlainGradientHk_factorialNormSq]
    exact factorialNormSq_nonneg _ _
  exact (le_add_of_nonneg_right hn).trans hh

theorem dataFinite_high_energy_bound {a b : ℝ} (hab : a ≤ b) (N K : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (P : MolecularData) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (y dy : ℝ → CellGalerkinSpace (E := ℂ) N) (S : ℝ → TorusHk K ℂ)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (htime : StrongTimeRegularity a b (fun t => cellGalerkinValue N (y t))
      (fun t => cellGalerkinValue N (dy t)))
    (heq : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy t)) (cellGalerkinValue N z) =
        dataGeneratorForm P t (y t).val z.val +
          inner ℝ ((S t).val (valueIndex2 K)) (cellGalerkinValue N z)) :
    ∀ t ∈ Icc a b, factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y t))).val ≤
      (factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val +
        ∫ s in a..b, factorialNormSq ρ (S s).val) *
      Real.exp ((1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
        finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (t - a)) := by
  have ht := htime.map (dataWeightedFourierCLM N K ρ)
  have hf : IntervalIntegrable (fun s => factorialNormSq ρ (S s).val) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (factorialNormSq_integrable ρ K (torusJet_memLp K hS))
  have hg := ht.norm_sq_le_gronwall hab
    (1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ^ 2) (by positivity)
    (fun s => factorialNormSq ρ (S s).val) hf
    (Filter.Eventually.of_forall (fun _ => factorialNormSq_nonneg _ _))
    (heq.mono (fun t ht => dataFinite_high_energy_production N K ρ hρ P t Cv hCv
      (hv t) (hp t) (hb t) (y t) (dy t) (S t) ht))
  simpa only [dataWeightedFourierCLM_apply, factorialWeightedJet_normSq] using hg

end AVRegularity.EntryWeakProofs
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Dissipative finite molecular energy includes arbitrary regular divergence sources. -/

theorem molecularFiniteSource_small_flux_energy (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c : FiniteMolecularCoefficients N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hm : cellMean (torusHkValueCLM (coupledPlainSynthesis N Unit.unit (K + 1) c)) = 0)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8) :
    2 * inner ℝ (factorialWeightedJet ρ
      (coupledPlainSynthesis N Unit.unit K (plainSourceCoefficients N (fun _ : Unit => K)
        (fun _ => F + dataFiniteFlux N K P t c)
        (fun _ => S - dataFiniteTransport N K P t Cv hCv hv hp hb c))).val)
      (factorialWeightedJet ρ (coupledPlainSynthesis N Unit.unit K c).val) +
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1) c).val / 2 ≤
        4 * (factorialNormSq ρ S.val + factorialNormSq ρ F.val) := by
  have hP : factorialNormSq ρ (coupledPlainSynthesis N Unit.unit K c).val ≤
      factorialNormSq ρ (coupledPlainGradientHk N c Unit.unit K).val := by
    rw [coupledPlainGradientHk_factorialNormSq]
    have h := factorialCellPoincare_coarse ρ
      (coupledPlainSynthesis N Unit.unit (K + 1) c) hm
    rw [coupledPlainSynthesis_truncate (h := fun _ : Unit => ℂ)
      N Unit.unit (Nat.le_succ K) c] at h
    exact h
  rw [molecularFiniteSource_energy_identity]
  have hsub : (S - dataFiniteTransport N K P t Cv hCv hv hp hb c).val =
    S.val - (dataFiniteTransport N K P t Cv hCv hv hp hb c).val := rfl
  have hadd : (F + dataFiniteFlux N K P t c).val =
      F.val + (dataFiniteFlux N K P t c).val := rfl
  rw [hsub, hadd]
  simp only [sub_eq_add_neg, factorialWeightedJet_add, factorialWeightedJet_neg,
    inner_add_left, inner_neg_left]
  rw [dataFiniteFlux, molecularMetric_factorial_pairing,
    ← coupledPlainGradientHk_factorialNormSq N c Unit.unit K ρ]
  have hh := dataHigher_spatial_flux_energy_small_transport K ρ hρ P.G P.metric_coercive t
    (P.v t) Cv hCv hv hp hb (coupledPlainSynthesis N Unit.unit K c) S F
    (coupledPlainGradientHk N c Unit.unit K) hP hsmall
  dsimp only [dataFiniteTransport]
  convert hh using 1
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Genuine earlier coefficient reserves produce the complete literal forcing for each exponential test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftAFromEarlierCoefficients (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve (H + 1) (fun t z Y => γ.coeff α t Y z)) :
    JointSourceReserve H (fun t z Y => normalizedLiftASource Q Cc
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n A t z Y v) := by
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single u (1 : ℝ) : ι → ℝ)
  let F := fun p q t z Y => (Real.exp (A Y))⁻¹ • liftApply q (Cc p q) f t Y z
  have Qtest (p q K : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) (hK : K ≤ H + D + 2) (w : ι) :
      JointSourceReserve K (fun t z Y => F p q t z Y w) :=
    normalizedScalarLiftTestReserve K q (Cc p q) A w u
      (fun m α x => (Qc p q hpq m α w x).mono K hK)
  have Q1 (w : ι) : JointSourceReserve (H + 2) (fun t z Y => F hh (n - 1) t z Y w) :=
    Qtest hh (n - 1) (H + 2) (Or.inr ⟨rfl, by omega⟩) (by omega) w
  have Q2 (hn2 : 2 ≤ n) (w : ι) :
      JointSourceReserve (H + 2) (fun t z Y => F hh (n - 2) t z Y w) :=
    Qtest hh (n - 2) (H + 2) (Or.inr ⟨rfl, by omega⟩) (by omega) w
  have QS (hhh : hh ≠ 0) (j : ℕ) (hj : j ∈ Finset.range (min D n + 1)) :
      JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y z v) := by
    let Qi := fun w => Qtest (hh - 1) (n - j) (H + 1 + D) (Or.inl (by omega)) (by omega) w
    have hjD : j ≤ D := by have := Finset.mem_range.mp hj; omega
    let R := normalizedSourceComponentCoefficientReserve H hH Q.edge hD Q.η A
      (F (hh - 1) (n - j)) Qi Qedge j hjD v
    have he (t : ℝ) : (fun X y => Real.exp (A X) • F (hh - 1) (n - j) t y X) =
        liftApply (n - j) (Cc (hh - 1) (n - j)) f t := by
      funext X y
      simp only [F, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
    exact R.congrSource (by funext t z Y; rw [he t])
  exact normalizedLiftAComponentReserve H Q Cc f hh n A v QG Qv Q1 Q2 QS

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The actual odd weak pulse has zero cell mean in each component. -/

theorem unitCosine_interval_mean :
    (∫ s in (0 : ℝ)..1, Real.cos (2 * Real.pi * s)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (by positivity : 2 * Real.pi ≠ 0)]
  simp [Real.sin_two_pi]

theorem unitCosine_cell_mean (i : Fin 2) :
    (∫ z in AVenhance.unitCube, Real.cos (2 * Real.pi * z i)) = 0 :=
  CycleComparison.Lift.integral_coordinate_mean_zero i _ (by fun_prop) unitCosine_interval_mean

theorem normalizedPulseDrift_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : Odd k)
    (t : ℝ) (i : Fin 2) :
    (∫ z in AVenhance.unitCube, ocPulseCellDrift α q Λ ζ m ν k t z i) = 0 := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · simp_rw [normalizedPulseDrift_horizontal hΛ hν h1]
    fin_cases i
    · simp
    · change (∫ z in AVenhance.unitCube,
        ((ocEpsilon q Λ m ^ (1 + α) / ν) *
          (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t))) *
            Real.cos (2 * Real.pi * z 0)) = 0
      rw [integral_const_mul, unitCosine_cell_mean, mul_zero]
  · simp_rw [normalizedPulseDrift_vertical hΛ hν h3]
    fin_cases i
    · change (∫ z in AVenhance.unitCube,
        -(((ocEpsilon q Λ m ^ (1 + α) / ν) *
          (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t))) *
            Real.cos (2 * Real.pi * z 1))) = 0
      rw [integral_neg, integral_const_mul, unitCosine_cell_mean]
      simp
    · simp

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Original scalar eddy lift clauses reindex the unused ambient source degree exactly. -/

theorem scalar_family_lift_zero_grade_degree_congr (D : OCData) (level : ℕ) (slot : ℤ)
    (A : RealChain) (ρ : ℝ) (Dm Dm' sX sZ N : ℕ) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hc : IsLiftSequence (familyLiftData (Dm := Dm) D level slot A ρ (fun _ _ _ => [])) sX sZ a b N 0 Cc) :
    IsLiftSequence (familyLiftData (Dm := Dm') D level slot A ρ (fun _ _ _ => [])) sX sZ a b N 0 Cc := by
  exact isLiftSequence_zero_grade_degree_congr
    (familyLiftData (Dm := Dm) D level slot A ρ (fun _ _ _ => []))
    (familyLiftData (Dm := Dm') D level slot A ρ (fun _ _ _ => []))
    rfl rfl rfl sX sZ N a b Cc hc

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The actual inverse transition used by native Piola lowering is smooth in its slow label. -/

theorem weak_appendChild_anchor (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (z : Vec 2) :
    ((A.appendChild D slot t z).geom D).2.2 = D.slotAnchor (A.ctxLevel + 1) slot := by
  rw [weak_appendChild_geom D A hl]
  rfl

theorem weak_transfer_matrix_eq (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (z h : Vec 2) (he : D.eps A.ctxLevel ≠ 0) :
    (childTransition D slot t (A.recenter D h) (z + (D.eps A.ctxLevel)⁻¹ • h))⁻¹ =
      (jacMatrix (fun y => (A.geom D).1 t y (A.geom D).2.2) ((A.geom D).2.1 + h))⁻¹ *
      jacMatrix (fun y => ((A.appendChild D slot t z).geom D).1 t y
        ((A.appendChild D slot t z).geom D).2.2)
        (((A.recenter D h).appendChild D slot t (z + (D.eps A.ctxLevel)⁻¹ • h)).geom D).2.1 := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  have hl' : (A.recenter D h).WellSlotted := by
    change (A.recenter D h).slots.length = (A.recenter D h).children.length + 1
    rw [hs, hc]
    exact hl
  have hctx : (A.recenter D h).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have ha : (((A.recenter D h).appendChild D slot t
      (z + (D.eps A.ctxLevel)⁻¹ • h)).geom D).2.2 =
      ((A.appendChild D slot t z).geom D).2.2 := by
    rw [weak_appendChild_anchor D (A.recenter D h) hl', hctx, weak_appendChild_anchor D A hl]
  rw [weak_childTransition_inverse_eq]
  unfold RealChain.famJac
  rw [geom_recenter D A hl h]
  rw [weak_appendChild_recenter_flow D A hl slot t z h he, ha]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The literal odd pulse supplies the shear profile required by the lift setting. -/

def pulseShearAmplitude (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ)
    (k : ℤ) (t : ℝ) : ℝ :=
  (if k % 4 = 1 then 1 else -1) * (ocEpsilon q Λ m ^ (1 + α) / ν) *
    (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t))

def pulseShearProfile (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ)
    (k : ℤ) (t x : ℝ) : ℝ :=
  pulseShearAmplitude α q Λ m ζ ν k t * Real.cos (2 * Real.pi * x)

theorem pulseShearProfile_contDiff (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (ν : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (pulseShearProfile α q Λ m ζ ν k t) := by
  unfold pulseShearProfile
  fun_prop

theorem pulseShearProfile_periodic (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (ν : ℝ) (k : ℤ) (t : ℝ) :
    Function.Periodic (pulseShearProfile α q Λ m ζ ν k t) 1 := by
  intro x
  unfold pulseShearProfile
  have he : 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi := by ring
  rw [he, Real.cos_add_two_pi]

theorem pulseShearProfile_mean_zero (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (ν : ℝ) (k : ℤ) (t : ℝ) :
    (∫ x in (0 : ℝ)..1, pulseShearProfile α q Λ m ζ ν k t x) = 0 := by
  unfold pulseShearProfile
  rw [intervalIntegral.integral_const_mul, unitCosine_interval_mean, mul_zero]

theorem normalizedPulseDrift_shear {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) {k : ℤ} (hk : Odd k)
    (t : ℝ) (z : Vec 2) :
    ocPulseCellDrift α q Λ ζ m ν k t z =
      pulseShearProfile α q Λ m ζ ν k t (z (pulseParallel k).rev) •
        basisVec (pulseParallel k) := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · rw [normalizedPulseDrift_horizontal hΛ hν h1]
    ext i
    fin_cases i <;> simp [pulseShearProfile, pulseShearAmplitude, pulseParallel, h1, basisVec]
  · rw [normalizedPulseDrift_vertical hΛ hν h3]
    have hn : k % 4 ≠ 1 := by omega
    ext i
    fin_cases i <;> simp [pulseShearProfile, pulseShearAmplitude, pulseParallel, hn, basisVec]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The actual retained Galerkin value has the factorial Poincaré control used by its energy gap. -/

theorem dataGalerkin_factorial_poincare (N K : ℕ) (ρ : ℝ)
    (u : CellGalerkinSpace (E := ℂ) N) (hm : cellMean (cellGalerkinValue N u) = 0) :
    ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N u)‖ ^ 2 ≤
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1)
        (dataFourierCoordinatesCLM N (cellGalerkinValue N u))).val := by
  let c := dataFourierCoordinatesCLM N (cellGalerkinValue N u)
  have he : torusHkValueCLM (coupledPlainSynthesis N Unit.unit (K + 1) c) =
      cellGalerkinValue N u := by
    change (coupledPlainSynthesis N Unit.unit (K + 1) c).val (valueIndex2 (K + 1)) = _
    rw [coupledPlainSynthesis_value_order_independent N Unit.unit (K + 1) 1]
    dsimp only [c]
    rw [dataFourierCoordinates_reconstruct]
    rfl
  have hp := factorialCellPoincare_coarse ρ (coupledPlainSynthesis N Unit.unit (K + 1) c)
    (by simpa only [he] using hm)
  rw [coupledPlainSynthesis_truncate (h := fun _ : Unit => ℂ)
    N Unit.unit (Nat.le_succ K) c] at hp
  simpa only [dataWeightedFourierCLM, ContinuousLinearMap.comp_apply,
    plainWeightedSynthesisCLM_apply, factorialWeightedJet_normSq] using hp

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The native transfer center intertwines the fixed child chart with its parent chart. -/

def weakTransferCenterMap (D : OCData) (A : RealChain) (slot : ℤ) (t : ℝ) (z : Vec 2) :
    Vec 2 → Vec 2 := fun h =>
  (((A.recenter D h).appendChild D slot t (z + (D.eps A.ctxLevel)⁻¹ • h)).geom D).2.1

theorem weak_transfer_center_chart_identity (D : OCData) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (z h : Vec 2)
    (he : D.eps A.ctxLevel ≠ 0) :
    ((A.appendChild D slot t z).geom D).1 t (weakTransferCenterMap D A slot t z h)
      ((A.appendChild D slot t z).geom D).2.2 =
      (A.geom D).1 t ((A.geom D).2.1 + h) (A.geom D).2.2 := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  have hl' : (A.recenter D h).WellSlotted := by
    change (A.recenter D h).slots.length = (A.recenter D h).children.length + 1
    rw [hs, hc]
    exact hl
  have hctx : (A.recenter D h).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have hh := weak_appendChild_output_origin D hζ (A.recenter D h) hl' slot t
    (z + (D.eps A.ctxLevel)⁻¹ • h)
  rw [weak_appendChild_recenter_flow D A hl slot t z h he,
    weak_appendChild_anchor D (A.recenter D h) hl', hctx,
    ← weak_appendChild_anchor D A hl slot t z, geom_recenter D A hl h] at hh
  exact hh

theorem weak_transfer_center_jacobian_identity (D : OCData) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (z h : Vec 2)
    (he : D.eps A.ctxLevel ≠ 0) :
    jacMatrix (fun y => ((A.appendChild D slot t z).geom D).1 t y
        ((A.appendChild D slot t z).geom D).2.2) (weakTransferCenterMap D A slot t z h) *
      jacMatrix (weakTransferCenterMap D A slot t z) h =
      jacMatrix (fun y => (A.geom D).1 t y (A.geom D).2.2) ((A.geom D).2.1 + h) := by
  let F := fun y => ((A.appendChild D slot t z).geom D).1 t y
    ((A.appendChild D slot t z).geom D).2.2
  let G := fun y => (A.geom D).1 t y (A.geom D).2.2
  let C := weakTransferCenterMap D A slot t z
  have hC : ContDiff ℝ (⊤ : ℕ∞) C :=
    (weak_transfer_child_center_joint_smooth D A hl slot t).comp
      (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := geomSpatialSmooth_geom D _ _ _
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := geomSpatialSmooth_geom D _ _ _
  have heq : F ∘ C = G ∘ (fun y => (A.geom D).2.1 + y) :=
    funext (fun y => weak_transfer_center_chart_identity D hζ A hl slot t z y he)
  have hT : Differentiable ℝ (fun y : Vec 2 => (A.geom D).2.1 + y) := by
    fun_prop
  have hh := congrArg (fun f => jacMatrix f h) heq
  rw [CycleReference.jacMatrix_comp h ((hF.differentiable (by simp)) _)
    ((hC.differentiable (by simp)) _),
    CycleReference.jacMatrix_comp (f := G) (g := fun y => (A.geom D).2.1 + y)
      h ((hG.differentiable (by simp)) _) (hT _)] at hh
  have ht : jacMatrix (fun y : Vec 2 => (A.geom D).2.1 + y) h = 1 := by
    have hd : fderiv ℝ (fun y : Vec 2 => (A.geom D).2.1 + y) h =
        ContinuousLinearMap.id ℝ (Vec 2) :=
      ((hasFDerivAt_id h).const_add (A.geom D).2.1).fderiv
    ext i a
    simp only [jacMatrix, Matrix.of_apply, hd,
      ContinuousLinearMap.id_apply, basisVec, Pi.single_apply, Matrix.one_apply]
  rw [ht, Matrix.mul_one] at hh
  exact hh

theorem weak_transfer_matrix_inverse_eq_center_jacobian_inverse
    (D : OCData) (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (z h : Vec 2) (he : D.eps A.ctxLevel ≠ 0) :
    (childTransition D slot t (A.recenter D h)
      (z + (D.eps A.ctxLevel)⁻¹ • h))⁻¹ =
      (jacMatrix (weakTransferCenterMap D A slot t z) h)⁻¹ := by
  let B := A.appendChild D slot t z
  let C := weakTransferCenterMap D A slot t z
  let Q := jacMatrix (fun y => (B.geom D).1 t y (B.geom D).2.2) (C h)
  let P := jacMatrix (fun y => (A.geom D).1 t y (A.geom D).2.2) ((A.geom D).2.1 + h)
  have hunit : IsUnit Q.det := weak_offsetJacobian_det_isUnit
    (geomSpatialSmooth_geom D B) (actualOffset_inverse_law D B) t (B.geom D).2.2 (C h)
  have hh : Q * jacMatrix C h = P :=
    weak_transfer_center_jacobian_identity D hζ A hl slot t z h he
  have hc : jacMatrix C h = Q⁻¹ * P := by
    have heq := congrArg (fun M => Q⁻¹ * M) hh
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul] at heq
    exact heq
  rw [hc, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hunit]
  exact weak_transfer_matrix_eq D A hl slot t z h he

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! The original finite equation retains the full high-gradient dissipation with divergence forcing. -/

theorem dataFinite_small_flux_gradient_production (N K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (P : MolecularData) (t Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ContDiff ℝ (K : ℕ∞) (P.v t)) (hp : AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (u du : CellGalerkinSpace (E := ℂ) N) (S : TorusHk K ℂ)
    (F : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (heq : ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N du) (cellGalerkinValue N z) =
        dataGeneratorForm P t u.val z.val + inner ℝ (S.val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ k : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
              2 (volume.restrict AVenhance.unitCube)) (F.val (valueIndex2 K)))
            (cellDerivativeCLM k z.val))
    (hm : cellMean (cellGalerkinValue N u) = 0)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8) :
    2 * inner ℝ (dataWeightedFourierCLM N K ρ (cellGalerkinValue N u))
      (dataWeightedFourierCLM N K ρ (cellGalerkinValue N du)) +
      gradFactorialNormSq ρ (coupledPlainSynthesis N Unit.unit (K + 1)
        (dataFourierCoordinatesCLM N (cellGalerkinValue N u))).val / 2 ≤
        4 * (factorialNormSq ρ S.val + factorialNormSq ρ F.val) := by
  let c := dataFourierCoordinatesCLM N (cellGalerkinValue N u)
  have hmean : cellMean (torusHkValueCLM (coupledPlainSynthesis N Unit.unit (K + 1) c)) = 0 := by
    have he : torusHkValueCLM (coupledPlainSynthesis N Unit.unit (K + 1) c) =
        cellGalerkinValue N u := by
      change (coupledPlainSynthesis N Unit.unit (K + 1) c).val (valueIndex2 (K + 1)) = _
      rw [coupledPlainSynthesis_value_order_independent N Unit.unit (K + 1) 1]
      dsimp only [c]
      rw [dataFourierCoordinates_reconstruct]
      rfl
    simpa only [he] using hm
  have hh := molecularFiniteSource_small_flux_energy N K ρ hρ P t Cv hCv hv hp hb c S F hmean hsmall
  have hd := dataFinite_flux_dual_coordinates N K P t Cv hCv hv hp hb u du S F heq
  simp only [dataWeightedFourierCLM, ContinuousLinearMap.comp_apply,
    plainWeightedSynthesisCLM_apply, hd]
  rw [real_inner_comm]
  exact hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The native child-center map preserves area, so its inverse entries are cofactors. -/

theorem weak_transfer_center_jacobian_det_one (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot)
    (ha : GeomAreaPreserving (A.geom D)) (slot : ℤ) (t : ℝ) (z h : Vec 2) :
    (jacMatrix (weakTransferCenterMap D A slot t z) h).det = 1 := by
  have hchild : GeomAreaPreserving ((A.appendChild D slot t z).geom D) := by
    rw [weak_appendChild_geom D A hl]
    exact childGeom_area_preserving D A.ctxLevel (Construction.Stream.ocEpsilon_pos hΛ)
      A.slot hp _ _ (geomSpatialSmooth_geom D A) ha
  have hh := congrArg Matrix.det (weak_transfer_center_jacobian_identity D hζ A hl
    slot t z h (Construction.Stream.ocEpsilon_pos hΛ).ne')
  rw [Matrix.det_mul, hchild, ha, one_mul] at hh
  exact hh

/-! Joint fast/slow center sampling at the actual parent scale uses one normalized shear. -/

def weakTransferCenterJoint (D : OCData) (A : RealChain) (slot : ℤ) (t : ℝ) :
    Vec 2 × Vec 2 → Vec 2 := fun Z =>
  (D.eps A.ctxLevel)⁻¹ • weakTransferCenterMap D A slot t Z.1 (D.eps A.ctxLevel • Z.2)

theorem weak_transfer_center_joint_formula (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (he : D.eps A.ctxLevel ≠ 0) :
    weakTransferCenterJoint D A slot t =
      fun Z => rescaledChart (D.eps A.ctxLevel)
        (fun y => (A.geom D).1 (D.slotAnchor (A.ctxLevel + 1) slot) y (A.geom D).2.2)
        ((D.eps A.ctxLevel)⁻¹ • (A.geom D).2.1 + Z.2 +
          D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t (Z.1 + Z.2)) := by
  funext Z
  dsimp only [weakTransferCenterJoint, weakTransferCenterMap]
  rw [weak_transfer_child_center_eq D A hl, inv_smul_smul₀ he]
  dsimp only [rescaledChart]
  rw [smul_add, smul_add, smul_inv_smul₀ he]

/-! Centering removes the family-dependent origin before taking the slow Jacobian. -/

def weakTransferCenteredJoint (D : OCData) (A : RealChain) (slot : ℤ) (t : ℝ) :
    Vec 2 × Vec 2 → Vec 2 := fun Z =>
  centeredGeometryChart (A.geom D) (D.eps A.ctxLevel)
    (D.slotAnchor (A.ctxLevel + 1) slot)
    (Z.2 + D.relDisp A.ctxLevel A.slot
      (D.slotAnchor (A.ctxLevel + 1) slot) t (Z.1 + Z.2))

theorem weak_transfer_center_joint_eq_centered (D : OCData) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (he : D.eps A.ctxLevel ≠ 0) :
    weakTransferCenterJoint D A slot t = fun Z =>
      (D.eps A.ctxLevel)⁻¹ • (A.geom D).1
        (D.slotAnchor (A.ctxLevel + 1) slot) (A.geom D).2.1 (A.geom D).2.2 +
      weakTransferCenteredJoint D A slot t Z := by
  rw [weak_transfer_center_joint_formula D A hl slot t he]
  funext Z
  dsimp only [rescaledChart, weakTransferCenteredJoint, centeredGeometryChart]
  rw [smul_add, smul_add, smul_inv_smul₀ he, smul_add]
  rw [← smul_add]
  congr 1
  rw [add_sub_cancel, add_assoc]

theorem jacMatrix_const_add (c : Vec 2) (f : Vec 2 → Vec 2) (X : Vec 2) :
    jacMatrix (fun y => c + f y) X = jacMatrix f X := by
  unfold jacMatrix
  rw [fderiv_const_add]

theorem weak_transfer_centered_slow_jacobian (D : OCData) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (he : D.eps A.ctxLevel ≠ 0)
    (Z : Vec 2 × Vec 2) :
    jacMatrix (fun y => weakTransferCenterJoint D A slot t (Z.1, y)) Z.2 =
      jacMatrix (fun y => weakTransferCenteredJoint D A slot t (Z.1, y)) Z.2 := by
  rw [weak_transfer_center_joint_eq_centered D A hl slot t he]
  exact jacMatrix_const_add _ _ _

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Uniform finite higher energy from scalar and flux budgets on unit windows. -/

theorem dataFinite_uniform_ul_flux_energy {a b : ℝ} (hab : a ≤ b) (N K : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (P : MolecularData) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (y dy : ℝ → CellGalerkinSpace (E := ℂ) N) (S : ℝ → TorusHk K ℂ)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (htime : StrongTimeRegularity a b (fun t => cellGalerkinValue N (y t))
      (fun t => cellGalerkinValue N (dy t)))
    (heq : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy t)) (cellGalerkinValue N z) =
        dataGeneratorForm P t (y t).val z.val +
          inner ℝ ((S t).val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ k : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
              2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)))
            (cellDerivativeCLM k z.val))
    (hm : ∀ t ∈ Icc a b, cellMean (cellGalerkinValue N (y t)) = 0)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (B : ℝ) (hB : 0 ≤ B)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq ρ (S r).val + factorialNormSq ρ (F r).val)) ≤ B) :
    ∀ t ∈ Icc a b,
      ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N (y t))‖ ^ 2 ≤
        ‖dataWeightedFourierCLM N K ρ (cellGalerkinValue N (y a))‖ ^ 2 +
          B / (1 - Real.exp (-(1 / 2))) + B := by
  let f := fun t => 4 * (factorialNormSq ρ (S t).val + factorialNormSq ρ (F t).val)
  have hf : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (((factorialNormSq_integrable ρ K (torusJet_memLp K hS)).add
        (factorialNormSq_integrable ρ K (torusJet_memLp K hF))).const_mul 4)
  have ht := strongTime_normSq (htime.map (dataWeightedFourierCLM N K ρ))
  apply ht.scalar_ul_bound hab (by norm_num : (0 : ℝ) < 1 / 2) hB (sq_nonneg _) f hf
    (Filter.Eventually.of_forall (fun t => mul_nonneg (by norm_num)
      (add_nonneg (factorialNormSq_nonneg _ _) (factorialNormSq_nonneg _ _)))) _ hshort
  filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with t he htmem
  have hh := dataFinite_small_flux_gradient_production N K ρ hρ P t Cv hCv
    (hv t) (hp t) (hb t) (y t) (dy t) (S t) (F t) he (hm t htmem) hsmall
  have hP := dataGalerkin_factorial_poincare N K ρ (y t) (hm t htmem)
  dsimp only [f]
  linarith

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Pointwise forcing budgets give uniform unit-window budgets at every finite reserve. -/

theorem scalar_unit_window_integral_bound {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b) (Q : ℝ) (hQ : 0 ≤ Q)
    (hb : ∀ t ∈ Icc a b, f t ≤ Q) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, f r) ≤ Q := by
  intro s hs t ht hst hlen
  have hsub : uIcc s t ⊆ uIcc a b := by
    simpa only [uIcc_of_le hst, uIcc_of_le hab] using Icc_subset_Icc hs.1 ht.2
  have hh := intervalIntegral.integral_mono_on hst (hf.mono_set hsub)
    (continuous_const.intervalIntegrable s t)
    (fun r hr => hb r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩)
  have hp : (t - s) * Q ≤ Q := mul_le_of_le_one_left hQ hlen
  rw [intervalIntegral.integral_const, smul_eq_mul] at hh
  exact hh.trans hp

theorem higher_forcing_unit_window_budget {a b : ℝ} (hab : a ≤ b) (K : ℕ) (ρ : ℝ)
    (S : ℝ → TorusHk K ℂ) (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hb : ∀ t ∈ Icc a b, factorialNormSq ρ (S t).val + factorialNormSq ρ (F t).val ≤ Q) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq ρ (S r).val + factorialNormSq ρ (F r).val)) ≤ 4 * Q := by
  apply scalar_unit_window_integral_bound hab _
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (((factorialNormSq_integrable ρ K (torusJet_memLp K hS)).add
        (factorialNormSq_integrable ρ K (torusJet_memLp K hF))).const_mul 4)) (4 * Q) (by positivity)
  intro t ht
  exact mul_le_mul_of_nonneg_left (hb t ht) (by norm_num)

end AVRegularity.EntryWeakProofs
end

section
open AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The uniform scalar-and-flux energy budget is linear in the common source size. -/

def fluxProductionConstant (K : ℕ) : ℝ :=
  Real.sqrt ((8 * factorialWeightMax 1 K / (1 - Real.exp (-(1 / 2))) +
    8 * factorialWeightMax 1 K) / factorialWeightMin 1 K)

theorem fluxProductionConstant_nonneg (K : ℕ) : 0 ≤ fluxProductionConstant K :=
  Real.sqrt_nonneg _

theorem factorialWeightMax_nonneg_local (K : ℕ) : 0 ≤ factorialWeightMax 1 K :=
  (factorialWeight_nonneg 1 0).trans (factorialWeight_le_max 1 (0 : Fin (K + 1)))

theorem fluxProduction_sqrt_scale (K : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt (((8 * factorialWeightMax 1 K * N ^ 2) / (1 - Real.exp (-(1 / 2))) +
      8 * factorialWeightMax 1 K * N ^ 2) / factorialWeightMin 1 K) =
        fluxProductionConstant K * N := by
  have hm : 0 < factorialWeightMin 1 K := factorialWeightMin_pos 1 (by norm_num)
  have hd : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hW := factorialWeightMax_nonneg_local K
  have he : ((8 * factorialWeightMax 1 K * N ^ 2) / (1 - Real.exp (-(1 / 2))) +
      8 * factorialWeightMax 1 K * N ^ 2) / factorialWeightMin 1 K =
      ((8 * factorialWeightMax 1 K / (1 - Real.exp (-(1 / 2))) +
        8 * factorialWeightMax 1 K) / factorialWeightMin 1 K) * N ^ 2 := by ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hN]
  rfl

end AVRegularity.EntryWeakProofs
end
end
end
