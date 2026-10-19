-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.SmoothPullbackDifference
import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
public import AVRegularity.CycleWords.FiniteSmoothPeriodicCarrier
public import AVRegularity.CycleEvolution.CellPeriodicSliceGraphFluxSlice
import AVRegularity.KernelEnergy.TorusMultiplierTime
import AVRegularity.Weighted.GradientCarrierJet
import Mathlib.Algebra.Order.Star.Real

section
public noncomputable section
open Homogenization MeasureTheory Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! A mixed frequency derivative step preserves the native reserve using a complex line inside the original ball. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem torusHigher_native_frequency_derivative_step (q : ℕ) (g : V → ComplexCellL2)
    (c : V) (R M : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (hex : ∀ y ∈ ball c R, ∃ U : TorusHk q ℂ, torusHkValueCLM U = g y ∧ ‖U‖ ≤ M)
    (x : V) (hx : x ∈ ball c (R / 2)) (ν : V) (hν : ‖ν‖ ≤ 1) :
    ∃ U : TorusHk q ℂ, torusHkValueCLM U = fderiv ℂ g x ν ∧ ‖U‖ ≤ 32 * M / R := by
  let ρ : ℝ≥0 := ⟨R / 4, by positivity⟩
  have hρ : 0 < ρ := by change 0 < R / 4; positivity
  let h := fun z : ℂ => g (x + z • ν)
  have hinside (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : x + z • ν ∈ ball c R := by
    have hz' : ‖z‖ ≤ R / 4 := by
      rw [mem_closedBall, dist_zero_right] at hz
      exact hz
    have ht := norm_add_le (x - c) (z • ν)
    have hs : ‖z • ν‖ ≤ R / 4 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left hν (norm_nonneg z)).trans_eq (mul_one _) |>.trans hz'
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have he : x + z • ν - c = (x - c) + z • ν := by abel
    rw [he]
    linarith only [ht, hs, hx, hR]
  have ha (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : AnalyticAt ℂ h z :=
    (hg _ (hinside z hz)).comp (f := fun z : ℂ => x + z • ν)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  obtain ⟨f, hf, hseries⟩ := torusHigher_native_cauchy_realization q h 0 ρ hρ M
    (fun z hz => (ha z hz).continuousAt.continuousWithinAt)
    (fun z hz => (ha z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hex _ (hinside z hz))
  obtain ⟨U, hU, hn⟩ := torusHigher_cauchy_derivative_readout q f h ρ hρ M hseries
    (fun z hz => (hf z hz).1) (fun z hz => (hf z hz).2) 1
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith only [hR]) hx
  have hl : HasDerivAt (fun z : ℂ => x + z • ν) ν 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℂ)).smul_const ν).const_add x
  have hd : HasDerivAt h (fderiv ℂ g x ν) 0 := by
    exact (hg x hxR).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl
      (by rw [zero_smul, add_zero])
  refine ⟨U, ?_, ?_⟩
  · rw [iteratedDeriv_one, hd.deriv] at hU
    exact hU
  · exact hn.trans_eq (by
      change analyticBallDerivativeConstant 1 * M / ((R / 4) / 2) ^ 1 = 32 * M / R
      simp only [analyticBallDerivativeConstant, pow_zero, pow_one]
      field_simp
      ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native H2 states read their genuine first derivatives as H1 states. -/

def cellH2BaseCLM : TorusHk 2 ℂ →L[ℝ] TorusHk 1 ℂ := truncateTorusHk (by decide)

def cellH2DerivativeH1CLM (j : Fin 2) : TorusHk 2 ℂ →L[ℝ] TorusHk 1 ℂ :=
  derivativeTorusHk (fun _ : Fin 1 => j)

theorem cellH2DerivativeH1CLM_value (j : Fin 2) (u : TorusHk 2 ℂ) :
    torusHkValueCLM (cellH2DerivativeH1CLM j u) = cellDerivativeCLM j (cellH2BaseCLM u) := by
  change u.val (prefixJetIndex (fun _ : Fin 1 => j) (valueIndex2 1)) =
    u.val (truncateJetIndex (by decide : 1 ≤ 2) ⟨⟨1, by decide⟩, fun _ => j⟩)
  simp only [prefixJetIndex, valueIndex2, valueIndex, truncateJetIndex, Fin.append_elim0]
  rfl

theorem cellH2_second_derivative_pair (j k : Fin 2) (u : TorusHk 2 ℂ) (z : TorusHk 1 ℂ) :
    cellComplexPair (cellDerivativeCLM k (cellH2DerivativeH1CLM j u)) (torusHkValueCLM z) =
      -cellComplexPair (cellDerivativeCLM j (cellH2BaseCLM u)) (cellDerivativeCLM k z) := by
  rw [cellComplexDerivative_skew, cellH2DerivativeH1CLM_value]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual inverse cell-to-torus transfer, lifted isometrically to L2 fields. -/

theorem scalarTorusCellUnitary_symm_apply (f : ComplexCellL2) :
    scalarTorusCellUnitary.symm f = scalarCellToTorus f := by
  apply scalarTorusToCell.injective
  rw [scalarTorusToCell_scalarCellToTorus]
  exact scalarTorusCellUnitary.apply_symm_apply f

def scalarCellToTorusField {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Lp ComplexCellL2 2 μ →ₗᵢ[ℝ] Lp ScalarTorusL2 2 μ :=
  liftLinearIsometryL2 μ scalarTorusCellUnitary.symm.toLinearIsometry

theorem scalarCellToTorusField_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : Lp ComplexCellL2 2 μ) :
    scalarCellToTorusField μ F =ᵐ[μ] fun x => scalarCellToTorus (F x) := by
  have h := liftLinearIsometryL2_ae μ scalarTorusCellUnitary.symm.toLinearIsometry F
  filter_upwards [h] with x hx
  exact hx.trans (scalarTorusCellUnitary_symm_apply (F x))

theorem scalarCellToTorusField_inverse {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : Lp ComplexCellL2 2 μ) :
    liftLinearIsometryL2 μ scalarTorusToCell (scalarCellToTorusField μ F) = F := by
  apply Lp.ext
  filter_upwards [liftLinearIsometryL2_ae μ scalarTorusToCell (scalarCellToTorusField μ F),
    scalarCellToTorusField_ae μ F] with x hx hy
  rw [hx, hy, scalarTorusToCell_scalarCellToTorus]

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization MeasureTheory Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The first frequency derivative has a genuine native complex linear lift. -/

/-- Two coordinate witnesses assemble into a native derivative map; no native
operator-valued separability assertion is needed. -/
theorem torusHigher_native_frequency_derivative_map (q : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (c : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (hex : ∀ y ∈ ball c R, ∃ U : TorusHk q ℂ, torusHkValueCLM U = g y ∧ ‖U‖ ≤ M)
    (x : Fin 2 → ℂ) (hx : x ∈ ball c (R / 2)) :
    ∃ D : (Fin 2 → ℂ) →L[ℂ] TorusHk q ℂ,
      (torusHigherComplexValueCLM q).comp D = fderiv ℂ g x ∧
      ∀ ν, ‖D ν‖ ≤ (64 * M / R) * ‖ν‖ := by
  let e₀ : Fin 2 → ℂ := Pi.single 0 1
  let e₁ : Fin 2 → ℂ := Pi.single 1 1
  have he₀ : ‖e₀‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num [e₀, Pi.single_apply]
  have he₁ : ‖e₁‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num [e₁, Pi.single_apply]
  obtain ⟨U₀, hU₀, hb₀⟩ := torusHigher_native_frequency_derivative_step q g c R M hR hg hex x hx e₀ he₀
  obtain ⟨U₁, hU₁, hb₁⟩ := torusHigher_native_frequency_derivative_step q g c R M hR hg hex x hx e₁ he₁
  let D := (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight U₀ +
    (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight U₁
  refine ⟨D, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro ν
    have he : ν = ν 0 • e₀ + ν 1 • e₁ := by
      funext i
      fin_cases i <;> simp [e₀, e₁]
    change torusHkValueCLM (ν 0 • U₀ + ν 1 • U₁) = _
    rw [map_add, torusHigher_complex_value_smul, torusHigher_complex_value_smul, hU₀, hU₁]
    conv_rhs => rw [he, map_add, map_smul, map_smul]
  · intro ν
    change ‖ν 0 • U₀ + ν 1 • U₁‖ ≤ _
    have h₀ : ‖ν 0 • U₀‖ ≤ (32 * M / R) * ‖ν‖ := by
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm ν 0) hb₀ (norm_nonneg _) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    have h₁ : ‖ν 1 • U₁‖ ≤ (32 * M / R) * ‖ν‖ := by
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm ν 1) hb₁ (norm_nonneg _) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    exact (norm_add_le _ _).trans ((add_le_add h₀ h₁).trans_eq (by ring))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Stability of normalized dual rows, keeping the forward-graph error multiplied by the reversed correction. -/

theorem cellBilinearOverlap_difference_bound (ρ σ A B : ComplexCellL2) :
    ‖cellComplexPair ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A) -
      cellComplexPair σ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B)‖ ≤
    ‖ρ‖ * ‖A - B‖ + ‖ρ - σ‖ * ‖B‖ := by
  have he : cellComplexPair ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A) -
      cellComplexPair σ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B) =
      cellComplexPair ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (A - B)) +
      cellComplexPair (ρ - σ) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B) := by
    rw [map_sub]
    simp only [sub_eq_add_neg, cellComplexPair_add_left,
      cellComplexPair_add_right, cellComplexPair_neg_left, cellComplexPair_neg_right]
    ring
  rw [he]
  calc
    _ ≤ ‖cellComplexPair ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (A - B))‖ +
        ‖cellComplexPair (ρ - σ) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B)‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      simpa only [cellFiberConj_norm] using add_le_add
        (cellComplexPair_norm_le ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (A - B)))
        (cellComplexPair_norm_le (ρ - σ) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B))

theorem cellNormalizedRow_difference_bound (ρ σ A B : ComplexCellL2) (k l : ℂ)
    (hk : (1 + cellComplexPair ρ
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A)) * k = 1)
    (hl : (1 + cellComplexPair σ
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap B)) * l = 1)
    (hkn : ‖k‖ ≤ 2) (hln : ‖l‖ ≤ 2) (hρ : ‖ρ‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖cellScalarCLM k (A + cellConstantCLM 1) -
      cellScalarCLM l (B + cellConstantCLM 1)‖ ≤
      10 * ‖A - B‖ + 8 * ‖B‖ * ‖ρ - σ‖ := by
  have hd := cellBilinearOverlap_difference_bound ρ σ A B
  have hrec := complexReciprocal_difference_norm _ _ k l hk hl hkn hln
  have hrec' : ‖k - l‖ ≤ 4 * (‖A - B‖ + ‖ρ - σ‖ * ‖B‖) := by
    apply hrec.trans
    apply (mul_le_mul_of_nonneg_left hd (by norm_num)).trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add_left (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hρ (norm_nonneg (A - B))) _) (by norm_num)
  have he : cellScalarCLM k (A + cellConstantCLM 1) -
      cellScalarCLM l (B + cellConstantCLM 1) =
      k • (A - B) + (k - l) • (B + cellConstantCLM 1) := by
    simp only [cellScalarCLM_smul, smul_sub, smul_add, sub_smul]
    abel
  have hb1 : ‖B + cellConstantCLM 1‖ ≤ 2 := by
    calc
      _ ≤ ‖B‖ + ‖cellConstantCLM 1‖ := norm_add_le _ _
      _ = ‖B‖ + 1 := by rw [cellConstantCLM_norm, norm_one]
      _ ≤ 2 := by linarith only [hB]
  rw [he]
  calc
    _ ≤ ‖k • (A - B)‖ + ‖(k - l) • (B + cellConstantCLM 1)‖ := norm_add_le _ _
    _ = ‖k‖ * ‖A - B‖ + ‖k - l‖ * ‖B + cellConstantCLM 1‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ 2 * ‖A - B‖ + (4 * (‖A - B‖ + ‖ρ - σ‖ * ‖B‖)) * 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hkn (norm_nonneg _))
        (mul_le_mul hrec' hb1 (norm_nonneg _) (by positivity))
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Every supplied genuine graph has the literal normalized Bloch source identity. -/

theorem fibreGraph_normalized_source_identity
    (η Cw ξ0 Cg : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hr : IsFibreGraph η G v ξ0 Cg r lam)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ0) (t : ℝ) (x : Vec 2) :
    fibreGraphSource η v ξ (cellValue (fibreSeriesJet r ξ)) t x =
      -Complex.I * fibreDriftCoupling η v ξ t x * (1 + cellValue (fibreSeriesJet r ξ) t x) -
        ((η : ℂ) * fibreQuad (G t) ξ + fibreSeriesC lam ξ t) *
          (1 + cellValue (fibreSeriesJet r ξ) t x) := by
  have hd := hr.2.1 ξ hξ
  have hl : fibreSeriesC lam ξ t = -(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
      cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue (fibreSeriesJet r ξ) t y) :=
    hd.2.2.2.1 t
  rw [fibreGraphSource_normalized η Cw hv hw hm ξ (cellValue (fibreSeriesJet r ξ)) t
    (hd.2.2.1.1.2.2.1 t (Set.mem_univ t)).1 x, hl]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual constant states at every native torus Sobolev order. -/

def torusHigherConstant (K : ℕ) (c : ℂ) : TorusHk K ℂ :=
  finiteSmoothPeriodicHk K (fun _ => c) contDiff_const (fun _ _ => rfl)

theorem torusHigherConstant_value (K : ℕ) (c : ℂ) :
    torusHkValueCLM (torusHigherConstant K c) = cellConstantCLM c := by
  apply Lp.ext
  have h := finiteSmoothPeriodicHk_jet_ae K (fun _ => c) contDiff_const
    (fun _ _ => rfl) (valueIndex2 K)
  exact h.trans (cellConstantCLM_ae c).symm

theorem torusHigherConstant_truncate {K L : ℕ} (h : L ≤ K) (c : ℂ) :
    truncateTorusHk h (torusHigherConstant K c) = torusHigherConstant L c := by
  apply TorusHk.ext_value
  change torusHkValueCLM (truncateTorusHk h (torusHigherConstant K c)) =
    torusHkValueCLM (torusHigherConstant L c)
  rw [torusHigherConstant_value]
  change torusHkValueCLM (torusHigherConstant K c) = _
  exact torusHigherConstant_value K c

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Higher constant-coefficient spatial operators have exactly the actual H2 L2 readout. -/

def torusHigherFirstCLM (K : ℕ) (j : Fin 2) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  (derivativeTorusHk (K := K) (fun _ : Fin 1 => j)).comp
    (truncateTorusHk (by omega : K + 1 ≤ K + 2))

def torusHigherSecondCLM (K : ℕ) (j k : Fin 2) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  (derivativeTorusHk (K := K) (fun _ : Fin 1 => k)).comp
    (derivativeTorusHk (K := K + 1) (fun _ : Fin 1 => j))

theorem torusHigherFirstCLM_value (K : ℕ) (j : Fin 2) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (torusHigherFirstCLM K j U) =
      cellDerivativeCLM j (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) := by
  change U.val (truncateJetIndex (by omega : K + 1 ≤ K + 2)
    (prefixJetIndex (fun _ : Fin 1 => j) (valueIndex2 K))) =
    U.val (truncateJetIndex (by omega : 2 ≤ K + 2)
      (truncateJetIndex (by decide : 1 ≤ 2) ⟨⟨1, by decide⟩, fun _ => j⟩))
  simp only [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, Fin.val_zero, Nat.add_zero, Fin.append_elim0]
  rfl

theorem torusHigherSecondCLM_value (K : ℕ) (j k : Fin 2) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (torusHigherSecondCLM K j k U) =
      cellDerivativeCLM k (cellH2DerivativeH1CLM j
        (truncateTorusHk (by omega : 2 ≤ K + 2) U)) := by
  change U.val (prefixJetIndex (K := K + 1) (r := 1) (fun _ : Fin 1 => j)
    (prefixJetIndex (K := K) (r := 1) (fun _ : Fin 1 => k) (valueIndex2 K))) =
    U.val (truncateJetIndex (by omega : 2 ≤ K + 2)
      (prefixJetIndex (K := 1) (r := 1) (fun _ : Fin 1 => j) ⟨⟨1, by decide⟩, fun _ => k⟩))
  simp only [prefixJetIndex, truncateJetIndex, valueIndex2, valueIndex, Fin.val_zero, Nat.add_zero, Fin.append_elim0]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Native endpoint energy transfers to classical Sobolev norms for a rough L2 entrance. -/

theorem torusHigher_rough_entrance_sobolev_transfer (J : ℕ)
    (g : Vec 2 → ℂ) (hg : ContDiff ℝ (J : ℕ∞) g)
    (W : TorusHk J ℂ) (initial : ComplexCellL2)
    (hv : (torusHkValueCLM W : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g)
    (C : ℝ) (hC : 0 ≤ C) (hb : ‖W‖ ^ 2 ≤ C ^ 2 * ‖initial‖ ^ 2) :
    cellSobolevNorm J g ≤
      ((∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
        ENNReal.ofReal C) * ENNReal.ofReal ‖initial‖ := by
  have hn : ‖W‖ ≤ C * ‖initial‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    simpa only [mul_pow] using hb
  have he : ‖W‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal ‖initial‖ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hn
  exact (torusHigher_smooth_cellSobolevNorm_le W g hg hv).trans
    ((mul_le_mul_right he _).trans_eq (mul_assoc _ _ _).symm)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.Analysis.Convolution
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CycleWords

/-! Every finite cell Fourier band contains the original constant state. -/

local instance cellFourierConstantMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance cellFourierConstantAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance cellFourierConstantCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance cellFourierConstantTorusProbability : IsProbabilityMeasure (volume : Measure Torus) := inferInstance

theorem finiteOrthonormalProjection_fixes_mode {α E ι : Type*}
    [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [Fintype ι] [DecidableEq ι] (v : ι → Lp E 2 μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0) (i : ι) :
    finiteOrthonormalProjection v (v i) = v i := by
  simp only [finiteOrthonormalProjection_apply, finiteProjectionSynthesis,
    finiteProjectionCoefficients, hv]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def cellFourierConstantIndex (N : ℕ) : Fin (RealFourierDimension N) :=
  realFourierIndexEquivFin N none

theorem cellFourierConstantMode (N : ℕ) (j : Fin (Module.finrank ℝ ℂ)) :
    torusToCell (vectorFourierMode (E := ℂ) N (cellFourierConstantIndex N) j) =
      cellConstantCLM ((stdOrthonormalBasis ℝ ℂ) j) := by
  apply Lp.ext
  have hv := ContinuousLinearMap.coeFn_compLpL
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ ℂ) j)) (realFourierModeL2 N (cellFourierConstantIndex N))
  have hr := (realFourierModeFin_memLp N (cellFourierConstantIndex N)).coeFn_toLp
  have hm : vectorFourierMode (E := ℂ) N (cellFourierConstantIndex N) j =ᵐ[torusMeasure]
      fun _ => (stdOrthonormalBasis ℝ ℂ) j := by
    filter_upwards [hv, hr] with x hx hxr
    rw [show vectorFourierMode N (cellFourierConstantIndex N) j x =
      realFourierModeL2 N (cellFourierConstantIndex N) x • (stdOrthonormalBasis ℝ ℂ) j from hx]
    change realFourierModeL2 N (cellFourierConstantIndex N) x = _ at hxr
    rw [hxr]
    simp only [realFourierModeFin, cellFourierConstantIndex, Equiv.symm_apply_apply,
      realFourierMode, one_smul]
  have hmcell := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae hm
  filter_upwards [torusToCell_ae (vectorFourierMode N (cellFourierConstantIndex N) j),
    hmcell, cellConstantCLM_ae ((stdOrthonormalBasis ℝ ℂ) j)] with x hx hm hc
  exact hx.trans (hm.trans hc.symm)

theorem cellVectorFourierProjection_constant (N : ℕ) (c : ℂ) :
    cellVectorFourierProjection N (cellConstantCLM c) = cellConstantCLM c := by
  have hmode (j : Fin (Module.finrank ℝ ℂ)) :
      cellVectorFourierProjection N (cellConstantCLM ((stdOrthonormalBasis ℝ ℂ) j)) =
        cellConstantCLM ((stdOrthonormalBasis ℝ ℂ) j) := by
    rw [← cellFourierConstantMode N j]
    change torusToCell (vectorFourierProjection N
      (cellToTorus (torusToCell (vectorFourierMode N (cellFourierConstantIndex N) j)))) = _
    let m := vectorFourierMode (E := ℂ) N (cellFourierConstantIndex N) j
    have hr : cellToTorus (torusToCell m) = m := cellToTorus_torusToCell m
    have hp : vectorFourierProjection N m = m :=
      finiteOrthonormalProjection_fixes_mode _
        (fun p q => vectorFourierMode_orthonormal N p.1 q.1 p.2 q.2) (cellFourierConstantIndex N, j)
    exact (congrArg (fun x => torusToCell (vectorFourierProjection N x)) hr).trans
      (congrArg torusToCell hp)
  have hc := (stdOrthonormalBasis ℝ ℂ).sum_repr' c
  have hsum := congrArg cellConstantCLM hc
  simp only [map_sum, map_smul] at hsum
  rw [← hsum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hmode]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual and centre frozen chart metric satisfy the same qualitative weight inputs. -/

theorem cellMetricChoice_joint_contDiff (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m φ hφ l ν yc ∨
      G = fun t _ => ocCellMetric α q Λ m φ hφ l ν yc t 0) (i j : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => G p.1 p.2 i j) := by
  rcases hG with rfl | rfl
  · exact (ocCellMetric_joint_contDiff α q Λ m hφ l ν yc i j).of_le (by simp)
  · exact (ocCellMetric_frozen_joint_contDiff α q Λ m hφ l ν yc i j).of_le (by simp)

theorem cellMetricChoice_symmetric (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m φ hφ l ν yc ∨
      G = fun t _ => ocCellMetric α q Λ m φ hφ l ν yc t 0) (t : ℝ) (z : Vec 2) :
    (G t z).IsSymm := by
  rcases hG with rfl | rfl
  · exact ocCellMetric_symmetric α q Λ m hφ l ν yc t z
  · exact ocCellMetric_symmetric α q Λ m hφ l ν yc t 0

/-- Windowed near-identity: a near-identity bound of the actual chart
metric on a time set passes to the chosen (actual or centre-frozen) metric on that set. -/
theorem cellMetricChoice_nearIdentityOn (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (ν : ℝ) (yc : Vec 2)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m φ hφ l ν yc ∨
      G = fun t _ => ocCellMetric α q Λ m φ hφ l ν yc t 0) (s : Set ℝ) (g : ℝ)
    (hnear : IsMetricNearIdentityOn s (ocCellMetric α q Λ m φ hφ l ν yc) g) :
    IsMetricNearIdentityOn s G g := by
  rcases hG with rfl | rfl
  · exact hnear
  · intro t ht _ ξ
    exact hnear t ht 0 ξ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual native H1 primitive identities give genuine weak Hilbert curves. -/

theorem cellH1Primitive_test_increment (U T : ℝ → TorusHk 1 ℂ) {s t : ℝ}
    (hint : IntervalIntegrable T volume s t)
    (hi : U t - U s = ∫ r in s..t, T r) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (U t)) (torusHkValueCLM z) -
      inner ℝ (torusHkValueCLM (U s)) (torusHkValueCLM z) =
    ∫ r in s..t, inner ℝ (cellPivotDualCLM (torusHkValueCLM (T r))) z := by
  let L : TorusHk 1 ℂ →L[ℝ] ℝ :=
    (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := 1))
  have he := congrArg L hi
  rw [map_sub, ← L.intervalIntegral_comp_comm hint] at he
  change inner ℝ (torusHkValueCLM z) (torusHkValueCLM (U t)) -
    inner ℝ (torusHkValueCLM z) (torusHkValueCLM (U s)) =
    ∫ r in s..t, inner ℝ (torusHkValueCLM z) (torusHkValueCLM (T r)) at he
  have hp (r : ℝ) : inner ℝ (cellPivotDualCLM (torusHkValueCLM (T r))) z =
      inner ℝ (torusHkValueCLM (T r)) (torusHkValueCLM z) :=
    ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)) z _
  simp only [hp]
  rw [real_inner_comm (torusHkValueCLM z) (torusHkValueCLM (U t)),
    real_inner_comm (torusHkValueCLM z) (torusHkValueCLM (U s))]
  apply he.trans
  apply intervalIntegral.integral_congr
  intro r _
  exact real_inner_comm (torusHkValueCLM (T r)) (torusHkValueCLM z)


theorem cellWeakHilbertCurve_of_H1_primitive {a b : ℝ}
    (U T : ℝ → TorusHk 1 ℂ) (hU : ContinuousOn U (Icc a b))
    (hmU : MemLp U 2 (volume.restrict (Icc a b)))
    (hmT : MemLp T 2 (volume.restrict (Icc a b)))
    (hi : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → U t - U s = ∫ r in s..t, T r) :
    CellWeakHilbertCurve a b (fun t => torusHkValueCLM (U t)) U
      (fun t => cellPivotDualCLM (torusHkValueCLM (T t))) := by
  let : NormedAddCommGroup (TorusHk 1 ℂ) := inferInstance
  let : NormedAddCommGroup ComplexCellL2 := inferInstance
  refine ⟨(torusHkValueCLM (E := ℂ) (K := 1)).continuous.comp_continuousOn hU, hmU,
    cellPivotDualCLM.comp_memLp' ((torusHkValueCLM (E := ℂ) (K := 1)).comp_memLp' hmT),
    Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  intro s hs t ht hst z
  have hint : IntervalIntegrable T volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hst]
    exact (hmT.integrable (by norm_num)).mono_measure (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)
  exact cellH1Primitive_test_increment U T hint (hi s hs t ht hst) z

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization MeasureTheory Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! A genuine native choice has a uniform quadratic frequency remainder. -/

theorem torusHigher_native_frequency_remainder (q : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (c : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (F : (Fin 2 → ℂ) → TorusHk q ℂ)
    (hF : ∀ y ∈ ball c R, torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M)
    (x : Fin 2 → ℂ) (hx : x ∈ ball c (R / 2))
    (D : (Fin 2 → ℂ) →L[ℂ] TorusHk q ℂ)
    (hD : (torusHigherComplexValueCLM q).comp D = fderiv ℂ g x)
    (h : Fin 2 → ℂ) (hh : ‖h‖ < R / 8) :
    ‖F (x + h) - F x - D h‖ ≤ 32 * M / R ^ 2 * ‖h‖ ^ 2 := by
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith only [hR]) hx
  have hM : 0 ≤ M := (norm_nonneg (F x)).trans (hF x hxR).2
  by_cases hzero : h = 0
  · simp only [hzero, add_zero, sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, le_refl]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hzero
  let ν : Fin 2 → ℂ := ((‖h‖ : ℂ)⁻¹) • h
  have hν : ‖ν‖ = 1 := by
    simp only [ν, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg h)]
    exact inv_mul_cancel₀ hn.ne'
  have he : (‖h‖ : ℂ) • ν = h := by
    dsimp only [ν]
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  let ρ : ℝ≥0 := ⟨R / 4, by positivity⟩
  have hρ : 0 < ρ := by change 0 < R / 4; positivity
  have hinside (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : x + z • ν ∈ ball c R := by
    have hz' : ‖z‖ ≤ R / 4 := by
      rw [mem_closedBall, dist_zero_right] at hz
      exact hz
    have ht := norm_add_le (x - c) (z • ν)
    rw [norm_smul, hν, mul_one] at ht
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have he' : x + z • ν - c = (x - c) + z • ν := by abel
    rw [he']
    linarith only [ht, hz', hx, hR]
  let u := fun z : ℂ => g (x + z • ν)
  have ha (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : AnalyticAt ℂ u z :=
    (hg _ (hinside z hz)).comp (f := fun z : ℂ => x + z • ν)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  obtain ⟨f, hf, hseries⟩ := torusHigher_native_cauchy_realization q u 0 ρ hρ M
    (fun z hz => (ha z hz).continuousAt.continuousWithinAt)
    (fun z hz => (ha z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => ⟨F _, (hF _ (hinside z hz)).1, (hF _ (hinside z hz)).2⟩)
  have hmatch (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : f z = F (x + z • ν) := by
    apply torusHigherComplexValueCLM_injective q
    exact (hf z hz).1.trans (hF _ (hinside z hz)).1.symm
  have hz0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self ρ.2
  have hz : (‖h‖ : ℂ) ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg h)]
    change ‖h‖ ≤ R / 4
    linarith only [hh, hR]
  have hdu : HasDerivAt u (fderiv ℂ g x ν) 0 := by
    have hl : HasDerivAt (fun z : ℂ => x + z • ν) ν 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℂ)).smul_const ν).const_add x
    exact (hg x hxR).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl
      (by rw [zero_smul, add_zero])
  have hdf := (torusHigherComplexValueCLM q).hasFDerivAt.comp_hasDerivAt 0
    hseries.hasFPowerSeriesAt.hasDerivAt
  have huf : u =ᶠ[𝓝 (0 : ℂ)] ((torusHigherComplexValueCLM q) ∘ f) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with z hz'
    exact (hf z (ball_subset_closedBall hz')).1.symm
  have hdval : torusHigherComplexValueCLM q (deriv f 0) = fderiv ℂ g x ν := by
    rw [hseries.hasFPowerSeriesAt.deriv]
    exact hdf.deriv.symm.trans (huf.deriv_eq.symm.trans hdu.deriv)
  have hd : deriv f 0 = D ν := by
    apply torusHigherComplexValueCLM_injective q
    exact hdval.trans (DFunLike.congr_fun hD ν).symm
  have hh' : ‖(‖h‖ : ℂ)‖ < (ρ : ℝ) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg h)]
    change ‖h‖ < (R / 4) / 2
    linarith only [hh]
  have hb := boundedCauchy_linear_remainder f ρ hρ M hM hseries
    (fun z hz' => (hf z (sphere_subset_closedBall hz')).2) (‖h‖ : ℂ) hh'
  rw [hmatch _ hz, hmatch _ hz0, zero_smul, add_zero, he, hd, ← map_smul, he] at hb
  exact hb.trans_eq (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg h)]
    change 2 * M * (‖h‖ / (R / 4)) ^ 2 = 32 * M / R ^ 2 * ‖h‖ ^ 2
    field_simp
    ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Freezing a metric at the centre preserves all stated spatial jet bounds. -/

theorem metricChoice_spatial_contDiff
    (A G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = A ∨ G = fun t _ => A t 0)
    (I : Set ℝ) (N : ℕ)
    (hA : ∀ t ∈ I, ∀ i j, ContDiff ℝ N (fun x => A t x i j)) :
    ∀ t ∈ I, ∀ i j, ContDiff ℝ N (fun x => G t x i j) := by
  rcases hG with rfl | rfl
  · exact hA
  · intro t _ i j
    exact contDiff_const

theorem metricChoice_spatial_jets
    (A G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = A ∨ G = fun t _ => A t 0)
    (I : Set ℝ) (N : ℕ) (M : ℕ → ℝ)
    (hA : ∀ t ∈ I, ∀ x l, 1 ≤ l → l ≤ N → ∀ i j,
      ‖iteratedFDeriv ℝ l (fun y => A t y i j) x‖ ≤ M l) :
    ∀ t ∈ I, ∀ x l, 1 ≤ l → l ≤ N → ∀ i j,
      ‖iteratedFDeriv ℝ l (fun y => G t y i j) x‖ ≤ M l := by
  rcases hG with rfl | rfl
  · exact hA
  · intro t ht x l hl hN i j
    have hM := (norm_nonneg (iteratedFDeriv ℝ l (fun y => A t y i j) 0)).trans
      (hA t ht 0 l hl hN i j)
    simpa only [iteratedFDeriv_const_of_ne (by omega : l ≠ 0), Pi.zero_apply, norm_zero] using hM

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleWords

/-! Restrict joint coefficient measurability without unfolding the time endpoints. -/

theorem restrict_time_coefficient_measurable {E : Type*} [MeasurableSpace E]
    (F : ℝ → Vec 2 → E) (hF : Measurable (Function.uncurry F)) (a b : ℝ) :
    Measurable (fun p : Set.Icc a b × Vec 2 => F p.1 p.2) :=
  hF.comp (measurable_subtype_coe.prodMap measurable_id)

theorem matrix_coefficient_joint_measurable
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, Continuous (fun p : ℝ × Vec 2 => G p.1 p.2 i j)) :
    Measurable (Function.uncurry G) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (hG i j).measurable

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization MeasureTheory Metric Filter AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin Asymptotics
open scoped Topology AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Bounded genuine native witnesses yield joint complex frequency differentiability. -/

/-- The native derivative is obtained from the actual lower derivative, with a
uniform quadratic remainder proving joint differentiability. -/
theorem torusHigher_native_frequency_hasFDerivAt (q : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (c : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (F : (Fin 2 → ℂ) → TorusHk q ℂ)
    (hF : ∀ y ∈ ball c R, torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M)
    (x : Fin 2 → ℂ) (hx : x ∈ ball c (R / 2)) :
    ∃ D : (Fin 2 → ℂ) →L[ℂ] TorusHk q ℂ,
      HasFDerivAt F D x ∧ (torusHigherComplexValueCLM q).comp D = fderiv ℂ g x ∧
      ∀ ν, ‖D ν‖ ≤ (64 * M / R) * ‖ν‖ := by
  obtain ⟨D, hD, hb⟩ := torusHigher_native_frequency_derivative_map q g c R M hR hg
    (fun y hy => ⟨F y, (hF y hy).1, (hF y hy).2⟩) x hx
  refine ⟨D, ?_, hD, hb⟩
  apply HasFDerivAt.of_isLittleO
  have hbig : (fun y => F y - F x - D (y - x)) =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    apply IsBigO.of_bound (32 * M / R ^ 2)
    filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 8)] with y hy
    have hh : ‖y - x‖ < R / 8 := by simpa only [mem_ball, dist_eq_norm] using hy
    have ht := torusHigher_native_frequency_remainder q g c R M hR hg F hF x hx D hD (y - x) hh
    have he : x + (y - x) = y := by abel
    simpa only [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖)] using ht
  have ht : Tendsto (fun y : Fin 2 → ℂ => y - x) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, id_eq] using (tendsto_id.sub tendsto_const_nhds :
      Tendsto (fun y : Fin 2 → ℂ => y - x) (𝓝 x) (𝓝 (x - x)))
  exact hbig.trans_isLittleO ((isLittleO_norm_pow_id (by decide : 1 < 2)).comp_tendsto ht)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.KernelEnergy
namespace AVRegularity.CycleWords

/-! The committed torus multiplier preserves genuine Bochner L2 curves. -/

variable {E F T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [MeasurableSpace T] [Nonempty T]

theorem torusCoefficient_time_memLp {K : ℕ} (μ : Measure T) [IsFiniteMeasure μ]
    (C : T → Vec 2 → E →L[ℝ] F) (hm : Measurable (Function.uncurry C))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t)) (hp : ∀ t, AVenhance.IsZ2Periodic (C t))
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l)
    (u : T → TorusHk K E) (hu : MemLp u 2 μ) :
    MemLp (fun t => (u t).mulCoefficient (C t) (hc t) (hp t) (hb t)) 2 μ := by
  let : NormedAddCommGroup (TorusHk K F) := inferInstance
  let M : ℝ := (∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)
  have hA (l) : 0 ≤ A l := (norm_nonneg (coefficientDerivativeArray (C (Classical.choice (inferInstance : Nonempty T))) l.val 0)).trans
      (hb (Classical.choice (inferInstance : Nonempty T)) l 0)
  have hM : 0 ≤ M := by
    apply div_nonneg
    · apply mul_nonneg
      · exact Finset.sum_nonneg (fun l _ => mul_nonneg
          (by unfold factorialRootWeight; positivity) (hA l))
      · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  have hmeas := torusMultiplier_time_aestronglyMeasurable μ 1 (by norm_num) C hm hc hp A hb
    u hu.aestronglyMeasurable
  apply (hu.const_smul M).of_le hmeas
  apply Filter.Eventually.of_forall
  intro t
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hM]
  exact torusMultiplier_norm_bound (C t) (hc t) (hp t) A (hb t) 1 (by norm_num) (u t)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution Metric
open AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The literal zero-frequency correction gains one frequency factor in every native reserve. -/

theorem torusHigher_native_frequency_zero_gain (K : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (F : (Fin 2 → ℂ) → TorusHk K ℂ)
    (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 R))
    (hF : ∀ ξ ∈ ball (0 : Fin 2 → ℂ) R, torusHkValueCLM (F ξ) = g ξ ∧ ‖F ξ‖ ≤ M)
    (hz : F 0 = 0) (ξ : Fin 2 → ℂ) (hξ : ξ ∈ ball 0 (R / 2)) :
    ‖F ξ‖ ≤ (64 * M / R) * ‖ξ‖ := by
  have hC : 0 ≤ 64 * M / R := by positivity
  have hd (x : Fin 2 → ℂ) (hx : x ∈ ball 0 (R / 2)) :
      DifferentiableAt ℂ F x ∧ ‖fderiv ℂ F x‖ ≤ 64 * M / R := by
    obtain ⟨D, hD, _, hb⟩ := torusHigher_native_frequency_hasFDerivAt K g 0 R M hR hg F hF x hx
    exact ⟨hD.differentiableAt, hD.fderiv ▸ D.opNorm_le_bound hC hb⟩
  have he := (convex_ball (0 : Fin 2 → ℂ) (R / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hd x hx).1) (fun x hx => (hd x hx).2)
    (mem_ball_self (half_pos hR)) hξ
  simpa only [hz, sub_zero] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Spatial coefficient regularity on a time window yields an explicit zero extension. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def windowCoefficient (a b : ℝ) (C : ℝ → Vec 2 → E →L[ℝ] F) (t : ℝ) :
    Vec 2 → E →L[ℝ] F := if t ∈ Icc a b then C t else 0

theorem windowCoefficient_eq {a b t : ℝ} (C : ℝ → Vec 2 → E →L[ℝ] F)
    (ht : t ∈ Icc a b) : windowCoefficient a b C t = C t := ite_eq_left ht

theorem windowCoefficient_contDiff (a b : ℝ) (K : ℕ)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (C t)) (t : ℝ) :
    ContDiff ℝ (K : ℕ) (windowCoefficient a b C t) := by
  by_cases ht : t ∈ Icc a b
  · rw [windowCoefficient, ite_eq_left ht]
    exact hC t ht
  · rw [windowCoefficient, ite_eq_right ht]
    exact contDiff_const

theorem windowCoefficient_periodic (a b : ℝ)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (C t)) (t : ℝ) :
    AVenhance.IsZ2Periodic (windowCoefficient a b C t) := by
  by_cases ht : t ∈ Icc a b
  · rw [windowCoefficient, ite_eq_left ht]
    exact hp t ht
  · rw [windowCoefficient, ite_eq_right ht]
    exact fun _ _ => rfl

theorem windowCoefficient_measurable (a b : ℝ)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hm : Measurable (Function.uncurry C)) :
    Measurable (Function.uncurry (windowCoefficient a b C)) := by
  have he : Function.uncurry (windowCoefficient a b C) =
      (fun p : ℝ × Vec 2 => if p.1 ∈ Icc a b then C p.1 p.2 else 0) := by
    funext p
    unfold Function.uncurry windowCoefficient
    by_cases ht : p.1 ∈ Icc a b
    · rw [ite_eq_left ht, ite_eq_left ht]
    · rw [ite_eq_right ht, ite_eq_right ht]
      rfl
  rw [he]
  exact hm.ite (measurableSet_Icc.preimage measurable_fst) measurable_const

theorem coefficientDerivativeArray_zero_function (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (0 : Vec 2 → E →L[ℝ] F) j x = 0 := by
  ext z w
  change (orderedCoefficientDerivative (fun _ : Vec 2 => (0 : E →L[ℝ] F)) j w x) z = 0
  rw [AVRegularity.Weighted.orderedCoefficientDerivative_zero_function]
  rfl

theorem windowCoefficient_derivative_bound (a b : ℝ) (K : ℕ)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l)
    (t : ℝ) (l : Fin (K + 1)) (x : Vec 2) :
    ‖coefficientDerivativeArray (windowCoefficient a b C t) l.val x‖ ≤ A l := by
  by_cases ht : t ∈ Icc a b
  · rw [windowCoefficient, ite_eq_left ht]
    exact hb t ht l x
  · rw [windowCoefficient, ite_eq_right ht, coefficientDerivativeArray_zero_function, norm_zero]
    exact hA l

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Interval diffusion duals from cell ellipticity and measurable time coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetricInterval_entry_bound (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (t : ℝ) (k j : Fin 2) (z : Vec 2) :
    |planeIntervalCoefficient a b hab G t z k j| ≤ 2 :=
  CycleEvolution.cellMetric_entry_bound hG _ z k j

def cellMetricIntervalDiffusion (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hG : IsCellMetric G) : ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  fun t => planeScalarDiffusion (planeIntervalCoefficient a b hab G t)
    (planeIntervalMetric_continuous a b hab G hGc t) (by norm_num : (0 : ℝ) ≤ 2)
    (cellMetricInterval_entry_bound a b hab G hG t)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem cellMetricIntervalDiffusion_eq_of_mem (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hG : IsCellMetric G) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hc : ∀ k j, Continuous (fun z => G t z k j))
    (hb : ∀ k j z, |G t z k j| ≤ 2) :
    cellMetricIntervalDiffusion (E := E) a b hab G hGc hG t =
      planeScalarDiffusion (G t) hc (by norm_num : (0 : ℝ) ≤ 2) hb := by
  exact planeScalarDiffusion_congr _ _ (planeIntervalCoefficient_of_mem a b hab G t ht)
    _ hc (by norm_num) (by norm_num) _ hb

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization MeasureTheory Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Bounded native vector lifts are smooth throughout the original complex frequency domain. -/

theorem torusHigher_native_frequency_native_step (q : ℕ)
    (g : (Fin 2 → ℂ) → ComplexCellL2) (F : (Fin 2 → ℂ) → TorusHk q ℂ)
    (c : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (hF : ∀ y ∈ ball c R, torusHkValueCLM (F y) = g y ∧ ‖F y‖ ≤ M)
    (x : Fin 2 → ℂ) (hx : x ∈ ball c (R / 2))
    (ν : Fin 2 → ℂ) (hν : ‖ν‖ ≤ 1) :
    torusHkValueCLM (fderiv ℂ F x ν) = fderiv ℂ g x ν ∧
      ‖fderiv ℂ F x ν‖ ≤ 32 * M / R := by
  obtain ⟨D, hd, hD, _⟩ := torusHigher_native_frequency_hasFDerivAt q g c R M hR hg F hF x hx
  obtain ⟨U, hU, hb⟩ := torusHigher_native_frequency_derivative_step q g c R M hR hg
    (fun y hy => ⟨F y, (hF y hy).1, (hF y hy).2⟩) x hx ν hν
  have hv : torusHkValueCLM (fderiv ℂ F x ν) = fderiv ℂ g x ν := by
    rw [hd.fderiv]
    exact DFunLike.congr_fun hD ν
  have he : fderiv ℂ F x ν = U := torusHigherComplexValueCLM_injective q (hv.trans hU.symm)
  exact ⟨hv, he.symm ▸ hb⟩

theorem torusHigher_native_frequency_contDiffOn_shrink (q : ℕ) (n : ℕ)
    (T : (Fin 2 → ℂ) → ComplexCellL2)
    (B : (Fin 2 → ℂ) → TorusHk q ℂ)
    (c : Fin 2 → ℂ) (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (hT : AnalyticOnNhd ℂ T (ball c R))
    (hB : ∀ y ∈ ball c R, torusHkValueCLM (B y) = T y ∧ ‖B y‖ ≤ C) :
    ContDiffOn ℂ n B (ball c (R / 2 ^ (n + 1))) := by
  induction n generalizing T B R C with
  | zero =>
    change ContDiffOn ℂ (0 : WithTop ℕ∞) B _
    apply (contDiffOn_zero (𝕜 := ℂ) (f := B)).mpr
    intro x hx
    have hx' : x ∈ ball c (R / 2) := by simpa only [zero_add, pow_one] using hx
    obtain ⟨D, hd, _, _⟩ := torusHigher_native_frequency_hasFDerivAt q T c R C hR hT B hB x hx'
    exact hd.continuousAt.continuousWithinAt
  | succ n ih =>
    have heq : R / 2 ^ (n + 1 + 1) = (R / 2) / 2 ^ (n + 1) := by
      rw [pow_succ]
      field_simp
    change ContDiffOn ℂ (n + 1 : ℕ) B (ball c (R / 2 ^ (n + 1 + 1)))
    rw [heq]
    have hsub : ball c ((R / 2) / 2 ^ (n + 1)) ⊆ ball c (R / 2) :=
      ball_subset_ball (div_le_self (half_pos hR).le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    have hd : DifferentiableOn ℂ B (ball c ((R / 2) / 2 ^ (n + 1))) := by
      intro x hx
      obtain ⟨D, hD, _, _⟩ := torusHigher_native_frequency_hasFDerivAt q T c R C hR hT B hB x (hsub hx)
      exact hD.differentiableAt.differentiableWithinAt
    have hcoords (j : Fin 2) : ContDiffOn ℂ n
        (fun y => fderiv ℂ B y (Pi.single j 1)) (ball c ((R / 2) / 2 ^ (n + 1))) := by
      have he : ‖(Pi.single j 1 : Fin 2 → ℂ)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
        intro i
        by_cases hi : i = j <;> simp [hi]
      have ht : AnalyticOnNhd ℂ (fun y => fderiv ℂ T y (Pi.single j 1)) (ball c (R / 2)) := by
        intro y hy
        have hy' : y ∈ ball c R := ball_subset_ball (by linarith only [hR]) hy
        exact ((ContinuousLinearMap.apply ℂ ComplexCellL2
          (Pi.single j 1)).analyticAt _).comp (hT.fderiv y hy')
      exact ih _ _ (R / 2) (32 * C / R) (half_pos hR) (by positivity) ht
        (fun y hy => torusHigher_native_frequency_native_step q T B c R C hR hT hB y hy _ he)
    exact contDiffOn_succ_of_two_coordinate_derivatives B _ isOpen_ball n hd (hcoords 0) (hcoords 1)

/-- Local shrinking is only used in the proof. The native family is smooth on
its original common frequency domain. -/
theorem torusHigher_native_frequency_contDiffOn (q : ℕ)
    (T : (Fin 2 → ℂ) → ComplexCellL2)
    (B : (Fin 2 → ℂ) → TorusHk q ℂ)
    (c : Fin 2 → ℂ) (R C : ℝ) (hC : 0 ≤ C)
    (hT : AnalyticOnNhd ℂ T (ball c R))
    (hB : ∀ y ∈ ball c R, torusHkValueCLM (B y) = T y ∧ ‖B y‖ ≤ C) :
    ContDiffOn ℂ (⊤ : ℕ∞) B (ball c R) := by
  apply contDiffOn_infty.mpr
  intro n x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
  have ht := torusHigher_native_frequency_contDiffOn_shrink q n T B x r C hr hC
    (hT.mono hsub) (fun y hy => hB y (hsub hy))
  have hr' : 0 < r / 2 ^ (n + 1) := by positivity
  have hx' : x ∈ ball x (r / 2 ^ (n + 1)) := mem_ball_self hr'
  exact ((ht x hx').contDiffAt (ball_mem_nhds x hr')).contDiffWithinAt

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Every-time null changes of solution values preserve the actual integrated weak identity. -/

theorem cellWeakIdentity_value_congr_sections (C : CellCoefficients) (s t : ℝ)
    (u0 u1 v0 v1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u v : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h0 : u0 =ᵐ[volume.restrict AVenhance.unitCube] v0)
    (h1 : u1 =ᵐ[volume.restrict AVenhance.unitCube] v1)
    (hu : ∀ᵐ r ∂volume.restrict (Ioc s t), u r =ᵐ[volume.restrict AVenhance.unitCube] v r)
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t v0 v1 ψ dψ v du src F := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS C r (v r) (du r) ψ dψ (src r) (F r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => v1 x * ψ x) μ ∧ Integrable (fun x => v0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, v1 x * ψ x ∂μ) - (∫ x, v0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he0 : (fun x => u0 x * ψ x) =ᵐ[μ] fun x => v0 x * ψ x :=
    h0.mono (fun x hx => congrArg (fun z : ℂ => z * ψ x) hx)
  have he1 : (fun x => u1 x * ψ x) =ᵐ[μ] fun x => v1 x * ψ x :=
    h1.mono (fun x hx => congrArg (fun z : ℂ => z * ψ x) hx)
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t), R r =ᵐ[μ] R' r := by
    filter_upwards [hu] with r hr
    filter_upwards [hr] with x hx
    simp only [R, R', cellLiteralRHS, hx]
  have hint : (fun r => ∫ x, R r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => ∫ x, R' r x ∂μ := he.mono (fun r hr => integral_congr_ae hr)
  refine ⟨h.1.congr he1, h.2.1.congr he0, ?_, h.2.2.2.1.congr hint, ?_⟩
  · filter_upwards [h.2.2.1, he] with r hr her
    exact hr.congr her
  · rw [← integral_congr_ae he1, ← integral_congr_ae he0]
    exact h.2.2.2.2.trans (integral_congr_ae hint)

end AVRegularity.CycleWords
end
end
