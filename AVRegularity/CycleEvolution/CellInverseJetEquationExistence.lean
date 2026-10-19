-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellPullbackRawSolution
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual cell solution map is bounded and complex linear on complete finite energy data. -/

def cellFiniteEnergyEvolutionCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b :=
  (cellFiniteEnergyEvolutionLinear hab C hG V k hv hb hκ hκb).mkContinuous
    (Real.sqrt (20 * (b - a + 2) *
      Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))))
    (fun d => cellFiniteEnergyEvolution_norm_bound hab C hG V k hv hb hκb d _
      (cellFiniteEnergyEvolutionLinear_solves hab C hG V k hv hb hκ hκb d))

theorem cellFiniteEnergyEvolutionCLM_solves {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (d : CellFiniteEnergyDatum a b) :
    IsCellFiniteEnergyEvolution C hG V hv hb d
      (cellFiniteEnergyEvolutionCLM hab C hG V k hv hb hκ hκb d) :=
  cellFiniteEnergyEvolutionLinear_solves hab C hG V k hv hb hκ hκb d

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual finite-past mean-zero solutions from arbitrary L² initial data with a universal energy bound. -/

/-- Arbitrary mean-zero L² initial data produce a bounded finite-past cell solution. -/
theorem cellFinitePast_exists_bound (s : ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm (Ici s) f < ⊤) (hF : cellUlNorm (Ici s) F < ⊤)
    (c0 : Vec 2 → ℂ) (_hmi : AEStronglyMeasurable c0 (volume.restrict AVenhance.unitCube))
    (h0 : cellL2Norm c0 < ⊤) (hm0 : cellMean c0 = 0) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Ici s) ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      (∀ t, s ≤ t → cellMean (cellValue raw t) = 0) ∧
      cellValue raw s =ᵐ[volume.restrict AVenhance.unitCube] c0 ∧
      cellEnergyNorm (Ici s) raw ≤ ENNReal.ofReal 14 *
        (cellUlNorm (Ici s) f + cellUlNorm (Ici s) F + cellL2Norm c0) := by
  obtain ⟨V, hV⟩ := hv.2.1
  have hic : MemLp c0 2 (volume.restrict AVenhance.unitCube) := by
    change eLpNorm c0 2 _ < ⊤
    exact h0
  let initial : ComplexCellL2 := hic.toLp c0
  have hi : cellMean initial = 0 := (integral_congr_ae hic.coeFn_toLp).trans hm0
  let x := (cellUlNorm (Ici s) f).toReal
  let y := (cellUlNorm (Ici s) F).toReal
  let B := 4 * x ^ 2 + 8 * y ^ 2
  let R := ‖initial‖ ^ 2 + B / (1 - Real.exp (-(Real.pi ^ 2))) + B
  let L := x + y + ‖initial‖
  have hL : 0 ≤ L := add_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (norm_nonneg _)
  have hbudget : R ≤ 25 * L ^ 2 ∧ 2 * R + 2 * B ≤ 81 * L ^ 2 :=
    cellFinitePast_numerical_budgets ENNReal.toReal_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
  obtain ⟨A⟩ := cellFinitePastApproximation_exists s hG hv V hV f F hfm hFm hf hF initial hi
  change CellFinitePastApproximationData s G hG v hv V hV f F initial R at A
  obtain ⟨raw, hraw, htrace, hjet⟩ := A.exists_past_raw_solution hfm hFm hf hF
  have hmean : ∀ t, s ≤ t → cellMean (cellValue raw t) = 0 := by
    intro t ht
    rw [show cellMean (cellValue raw t) = cellMean (A.pastTrace t) from integral_congr_ae (htrace t).symm]
    exact A.pastTrace_mean ht
  have hinit : cellValue raw s =ᵐ[volume.restrict AVenhance.unitCube] c0 := by
    have he := htrace s
    rw [A.pastTrace_initial] at he
    exact he.symm.trans hic.coeFn_toLp
  have hvalue : (⨆ t ∈ Ici s, cellL2Norm (cellValue raw t)) ≤ ENNReal.ofReal (5 * L) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [cellL2Norm_eq_of_class _ _ (htrace t)]
    apply ENNReal.ofReal_le_ofReal
    exact scalar_trace_le_five_of_sq (norm_nonneg _) hL ((A.pastTrace_bound ht).trans hbudget.1)
  have hgrad : cellUlNorm (Ici s) (fun t => cellGradient (raw t)) ≤ ENNReal.ofReal (9 * L) := by
    apply cellUlNorm_le_of_window_sq_bound
    intro a
    have hclip : Icc a (a + 1) ∩ Ici s = Icc (max a s) (a + 1) := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici, max_le_iff]
      tauto
    rw [hclip]
    rcases le_or_gt (max a s) (a + 1) with hab | hba
    · have hsub : Icc (max a s) (a + 1) ⊆ Ici s := fun _ ht => (le_max_right _ _).trans ht.1
      have hm : volume.restrict (Icc (max a s) (a + 1)) ≤ volume.restrict (Ici s) :=
        Measure.restrict_mono hsub le_rfl
      have hc := A.past_local_curve hab (le_max_right _ _)
      have hn := cellSolution_gradient_lintegral_of_state hab
        (cellSolution_restrict hsub ordConnected_Icc hraw) A.pastState hc.state
        (hjet.filter_mono (ae_mono hm))
      rw [hn, ← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hL)]
      apply ENNReal.ofReal_le_ofReal
      have hg := A.gradient_short_bound hfm hFm hf hF hab (le_max_right _ _)
        (by have := le_max_left a s; linarith)
      change (∫ t in max a s..a + 1, ∑ j, ‖cellDerivativeCLM j (A.pastState t)‖ ^ 2) ≤ 2 * R + 2 * B at hg
      have hs := hg.trans hbudget.2
      nlinarith
    · simp only [Icc_eq_empty_of_lt hba, Measure.restrict_empty, lintegral_zero_measure]
      exact bot_le
  have hnorm : ENNReal.ofReal ‖initial‖ = cellL2Norm c0 := (cellL2Norm_eq_toLp c0 hic).symm
  have heq : ENNReal.ofReal (5 * L) + ENNReal.ofReal (9 * L) = ENNReal.ofReal 14 *
      (cellUlNorm (Ici s) f + cellUlNorm (Ici s) F + cellL2Norm c0) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hL) (mul_nonneg (by norm_num) hL),
      show 5 * L + 9 * L = 14 * L by ring, ENNReal.ofReal_mul (by norm_num)]
    rw [show L = x + y + ‖initial‖ from rfl,
      ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (norm_nonneg _),
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hf.ne, ENNReal.ofReal_toReal hF.ne, hnorm]
  refine ⟨raw, hraw, hmean, hinit, ?_⟩
  change _ + _ ≤ _
  rw [← heq]
  exact add_le_add hvalue hgrad

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Uniqueness of the all-time inverse without auxiliary assumptions on common forcing. -/

/-- Bounded all-time mean-zero public solutions with arbitrary common forcing agree. -/
theorem cellAllTimeInverse_unique_arbitrary_source
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D)
    (hD' : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D') :
    ∀ t, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  obtain ⟨V, hV⟩ := hv.2.1
  let K := (cellEnergyNorm univ D).toReal + (cellEnergyNorm univ D').toReal
  intro t
  have hbound (n : ℕ) : ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2 := by
    have hst : t - n ≤ t := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have he := cellRaw_meanZero_difference_decay_arbitrary_source hst hG hv V hV src F D D'
      (cellSolution_restrict (subset_univ (Icc (t - n) t)) ordConnected_Icc hD.1)
      (cellSolution_restrict (subset_univ (Icc (t - n) t)) ordConnected_Icc hD'.1)
      (fun r _ => hD.2.1 r) (fun r _ => hD'.2.1 r) t ⟨hst, le_rfl⟩
    have hnorm : ‖cellRawTrace D (t - n) - cellRawTrace D' (t - n)‖ ≤ K :=
      (norm_sub_le _ _).trans (add_le_add
        (cellRawTrace_norm_le_energy D hD.1 hD.2.2 (t - n))
        (cellRawTrace_norm_le_energy D' hD'.1 hD'.2.2 (t - n)))
    have hs : ‖cellRawTrace D (t - n) - cellRawTrace D' (t - n)‖ ^ 2 ≤ K ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hnorm
    rw [show t - (t - (n : ℝ)) = n by ring] at he
    exact he.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_add] using cellPullback_exp_budget_tendsto_zero 0 (K ^ 2)
  have hz : ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  have hn : ‖cellRawTrace D t - cellRawTrace D' t‖ = 0 := by
    nlinarith [norm_nonneg (cellRawTrace D t - cellRawTrace D' t)]
  have heq := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have htrace := cellRawTrace_ae D t (hD.1.2.2.1 t (mem_univ _)).1
  rw [heq] at htrace
  exact htrace.symm.trans (cellRawTrace_ae D' t (hD'.1.2.2.1 t (mem_univ _)).1)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual scalar potential perturbations act by bounded complex-linear forcing operators. -/

def cellScalarSourceDatumCLM (a b : ℝ) :
    Lp ComplexCellL2 2 (volume.restrict (Icc a b)) →L[ℂ] CellFiniteEnergyDatum a b :=
  (0 : Lp ComplexCellL2 2 (volume.restrict (Icc a b)) →L[ℂ] ComplexCellL2).prod
    ((ContinuousLinearMap.id ℂ _).prod 0)

def cellScalarPotentialSourceCLM {a b : ℝ} (hab : a ≤ b) :
    Lp ℂ ∞ (volume.restrict (Icc a b)) →L[ℂ]
      CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b :=
  (ContinuousLinearMap.compL ℂ (CellFiniteEnergyCarrier a b)
      (Lp ComplexCellL2 2 (volume.restrict (Icc a b))) (CellFiniteEnergyDatum a b)
      (cellScalarSourceDatumCLM a b)).comp
    ((ContinuousLinearMap.compL ℂ (CellFiniteEnergyCarrier a b)
      (Lp ComplexCellL2 2 (volume.restrict (Icc a b)))
      (Lp ComplexCellL2 2 (volume.restrict (Icc a b)))).flip
      (cellFiniteEnergyTimeValueCLM hab) |>.comp
      (lpTopScalarMultiplier (volume.restrict (Icc a b))))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual all-time mean-zero inverse existence with a universal drift-independent energy bound. -/

/-- The actual finite-past pullback construction produces a bounded all-time cell inverse. -/
theorem cellAllTimeInverse_exists_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      cellEnergyNorm univ raw ≤ ENNReal.ofReal 13 * (cellUlNorm univ f + cellUlNorm univ F) := by
  obtain ⟨V, hV⟩ := hv.2.1
  let x := (cellUlNorm univ f).toReal
  let y := (cellUlNorm univ F).toReal
  let B := 4 * x ^ 2 + 8 * y ^ 2
  let R := B / (1 - Real.exp (-(Real.pi ^ 2))) + B
  let L := x + y
  have hL : 0 ≤ L := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hbudget : R ≤ 24 * L ^ 2 ∧ 2 * R + 2 * B ≤ 64 * L ^ 2 :=
    cellInverse_numerical_budgets ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  obtain ⟨A⟩ := cellPullbackApproximation_exists hG hv V hV f F hfm hFm hf hF
  change CellPullbackApproximationData G hG v hv V hV f F R at A
  obtain ⟨raw, hraw, htrace, hjet⟩ := A.exists_raw_solution hfm hFm hf hF
  have hmean : ∀ t, cellMean (cellValue raw t) = 0 := by
    intro t
    rw [show cellMean (cellValue raw t) = cellMean (A.limit t) from integral_congr_ae (htrace t).symm]
    exact A.limit_mean t
  have hvalue : (⨆ t ∈ (univ : Set ℝ), cellL2Norm (cellValue raw t)) ≤ ENNReal.ofReal (5 * L) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro _
    rw [cellL2Norm_eq_of_class _ _ (htrace t)]
    apply ENNReal.ofReal_le_ofReal
    exact scalar_trace_le_five (norm_nonneg _) hL ((A.limit_bound t).trans hbudget.1)
  have hgrad : cellUlNorm univ (fun t => cellGradient (raw t)) ≤ ENNReal.ofReal (8 * L) := by
    apply cellUlNorm_le_of_window_sq_bound
    intro a
    have hab : a ≤ a + 1 := by linarith
    have hc := A.state_local_curve hfm hFm hf hF hab
    have hj := hjet.filter_mono (ae_mono (Measure.restrict_le_self (μ := volume) (s := Icc a (a + 1))))
    have hn := cellSolution_gradient_lintegral_of_state hab
      (cellSolution_restrict (subset_univ (Icc a (a + 1))) ordConnected_Icc hraw) A.state hc.state hj
    rw [inter_univ, hn, ← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hL)]
    apply ENNReal.ofReal_le_ofReal
    have hg := A.gradient_window_bound hfm hFm hf hF a
    change (∫ t in a..a + 1, ∑ j, ‖cellDerivativeCLM j (A.state t)‖ ^ 2) ≤ 2 * R + 2 * B at hg
    have hs := hg.trans hbudget.2
    nlinarith
  have heq : ENNReal.ofReal (5 * L) + ENNReal.ofReal (8 * L) =
      ENNReal.ofReal 13 * (cellUlNorm univ f + cellUlNorm univ F) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hL) (mul_nonneg (by norm_num) hL),
      show 5 * L + 8 * L = 13 * L by ring, ENNReal.ofReal_mul (by norm_num)]
    rw [show L = (cellUlNorm univ f).toReal + (cellUlNorm univ F).toReal from rfl,
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hf.ne, ENNReal.ofReal_toReal hF.ne]
  have henergy : cellEnergyNorm univ raw ≤
      ENNReal.ofReal 13 * (cellUlNorm univ f + cellUlNorm univ F) := by
    change _ + _ ≤ _
    rw [← heq]
    exact add_le_add hvalue hgrad
  have hfinite : ENNReal.ofReal 13 * (cellUlNorm univ f + cellUlNorm univ F) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hf, hF⟩)
  exact ⟨raw, ⟨hraw, hmean, henergy.trans_lt hfinite⟩, henergy⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The complete all-time existence, bound, and uniqueness clause of the mean-zero cell inverse. -/

/-- All-time cell inversion exists, obeys a universal energy bound, and is unique among bounded mean-zero histories. -/
theorem cellAllTimeInverse_exists_unique
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      cellEnergyNorm univ raw ≤ ENNReal.ofReal 13 * (cellUlNorm univ f + cellUlNorm univ F) ∧
      ∀ raw' : ℝ → RawJet2 1 ℂ,
        IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw' →
        ∀ t, cellValue raw' t =ᵐ[volume.restrict AVenhance.unitCube] cellValue raw t := by
  obtain ⟨raw, hr, hb⟩ := cellAllTimeInverse_exists_bound hG hv f F hfm hFm hf hF
  exact ⟨raw, hr, hb, fun raw' hr' => cellAllTimeInverse_unique hG hv f F hfm hFm hf hF raw' raw hr' hr⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual bounded operator coefficients of the linear and quadratic Bloch perturbation. -/

def cellBlochLinearForcingCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (j : Fin 2) :
    CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b :=
  (0 : CellFiniteEnergyCarrier a b →L[ℂ] ComplexCellL2).prod
    (((Complex.I • (∑ k : Fin 2, (cellTimeMetricEntryCLM (Icc a b) hG k j).comp
        (cellFiniteEnergyTimeShiftedDerivativeCLM hab C.θ k))) -
      Complex.I • ((cellTimeDriftEntryCLM (Icc a b) C V hv hb j).comp
        (cellFiniteEnergyTimeValueCLM hab))).prod
      (ContinuousLinearMap.pi (fun k => Complex.I •
        ((cellTimeMetricEntryCLM (Icc a b) hG j k).comp (cellFiniteEnergyTimeValueCLM hab)))))

def cellBlochQuadraticForcingCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (j k : Fin 2) :
    CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b :=
  (0 : CellFiniteEnergyCarrier a b →L[ℂ] ComplexCellL2).prod
    ((-((cellTimeMetricEntryCLM (Icc a b) hG j k).comp
      (cellFiniteEnergyTimeValueCLM hab))).prod 0)

def cellBlochPolynomialForcing {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) : CellEnergyForcingOperator a b :=
  (∑ j : Fin 2, δ j • cellEnergyForcingOperatorOfCLM a b
    (cellBlochLinearForcingCLM hab C hG V hv hb j)) +
  (∑ j : Fin 2, ∑ k : Fin 2, (δ j * δ k) • cellEnergyForcingOperatorOfCLM a b
    (cellBlochQuadraticForcingCLM hab C hG j k)) +
  cellEnergyForcingOperatorOfCLM a b (cellScalarPotentialSourceCLM hab q)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Cell inversion for jointly almost strongly measurable forcing, as required for metric-jet fluxes. -/

/-- Mean-free projection preserves spatial almost-everywhere equality. -/
theorem cellQ0_congr_ae (f g : Vec 2 → ℂ)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] g) :
    cellQ0 f =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 g := by
  have hm : cellMean f = cellMean g := integral_congr_ae he
  filter_upwards [he] with x hx
  simp only [cellQ0, hx, hm]

/-- Measurable representatives extend the actual all-time inverse to almost measurable data. -/
theorem cellAllTimeInverse_exists_bound_ae
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      cellEnergyNorm univ raw ≤ ENNReal.ofReal 13 *
        (cellUlNorm univ f + cellUlNorm univ F) := by
  obtain ⟨g, hgm, heg, hgn⟩ := cellUl_measurable_representative univ f hfm
  obtain ⟨H, hHm, heH, hHn⟩ := cellUl_measurable_representative univ F hFm
  obtain ⟨raw, hr, hb⟩ := cellAllTimeInverse_exists_bound hG hv g H hgm hHm
    (hgn ▸ hf) (hHn ▸ hF)
  have hs : ∀ᵐ t ∂volume.restrict univ,
      cellQ0 (g t) =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 (f t) := by
    filter_upwards [Measure.ae_ae_of_ae_prod heg] with t ht
    change f t =ᵐ[volume.restrict AVenhance.unitCube] g t at ht
    exact cellQ0_congr_ae _ _ ht.symm
  refine ⟨raw, ⟨?_, hr.2⟩, ?_⟩
  · exact cellSolution_source_congr_sections univ ⟨G, v, 0, 0⟩ _ _ H F raw hs
      (Measure.ae_ae_of_ae_prod heH.symm) hr.1
  · simpa only [hgn, hHn] using hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual linear and quadratic forcing polynomial is analytic in complex frequency and in an analytic L-infinity potential. -/

theorem cellBlochPolynomialForcing_analyticAt {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : X → Fin 2 → ℂ) (q : X → Lp ℂ ∞ (volume.restrict (Icc a b))) (x : X)
    (hδ : AnalyticAt ℂ δ x) (hq : AnalyticAt ℂ q x) :
    AnalyticAt ℂ (fun y => cellBlochPolynomialForcing hab C hG V hv hb (δ y) (q y)) x := by
  have hd (j : Fin 2) : AnalyticAt ℂ (fun y => δ y j) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).analyticAt (δ x)).comp hδ
  have hl j : AnalyticAt ℂ (fun y => δ y j • cellEnergyForcingOperatorOfCLM a b
      (cellBlochLinearForcingCLM hab C hG V hv hb j)) x :=
    (hd j).smul analyticAt_const
  have ht j k : AnalyticAt ℂ (fun y => (δ y j * δ y k) • cellEnergyForcingOperatorOfCLM a b
      (cellBlochQuadraticForcingCLM hab C hG j k)) x :=
    ((hd j).mul (hd k)).smul analyticAt_const
  let L := (cellEnergyForcingOperatorOfCLM a b).comp (cellScalarPotentialSourceCLM hab)
  have hp : AnalyticAt ℂ (fun y => cellEnergyForcingOperatorOfCLM a b
      (cellScalarPotentialSourceCLM hab (q y))) x := (L.analyticAt (q x)).comp hq
  simpa only [cellBlochPolynomialForcing, Fin.sum_univ_two, Pi.add_def] using
    ((hl 0).add (hl 1)).add (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))) |>.add hp

/-! The analytic operator polynomial equals the literal Bloch perturbation forcing map. -/

theorem cellBlochPerturbationDatumCLM_eq_polynomial {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) :
    cellEnergyForcingOperatorOfCLM a b (cellBlochPerturbationDatumCLM hab C hG V hv hb δ q) =
      cellBlochPolynomialForcing hab C hG V hv hb δ q := by
  apply cellEnergyForcingOperator_ext
  intro z
  rw [cellEnergyForcingOperatorEval_ofCLM]
  simp only [cellBlochPolynomialForcing, map_add, map_sum, map_smul,
    cellEnergyForcingOperatorEval_ofCLM]
  apply Prod.ext
  · simp [cellBlochPerturbationDatumCLM, 
      cellBlochLinearForcingCLM, cellBlochQuadraticForcingCLM,
      cellScalarPotentialSourceCLM, cellScalarSourceDatumCLM, 
      Fin.sum_univ_two]
  · apply Prod.ext
    · simp only [cellBlochPerturbationDatumCLM, 
        cellBlochLinearForcingCLM, cellBlochQuadraticForcingCLM, cellBlochPerturbationScalarCLM,
        cellScalarPotentialSourceCLM, cellScalarSourceDatumCLM, 
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply,
        cellFiniteEnergyTimeShiftedDerivativeCLM, Fin.sum_univ_two,
        add_apply, sub_apply, smul_apply, neg_apply, map_add, map_smul, Pi.add_apply,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        zero_apply]
      match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
    · funext k
      simp only [cellBlochPerturbationDatumCLM, 
        cellBlochLinearForcingCLM, cellBlochQuadraticForcingCLM, cellBlochPerturbationFluxCLM,
        cellScalarPotentialSourceCLM, cellScalarSourceDatumCLM, 
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, Fin.sum_univ_two, add_apply, smul_apply,
        Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        smul_smul, zero_apply, Pi.zero_apply]
      module

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Literal L2 boundedness of the actual mean-free projection. -/

/-- The literal cell projection has the same universal L2 bound as its Hilbert realization. -/
theorem cellQ0_cellL2Norm_le (f : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (cellQ0 f) ≤ 2 * cellL2Norm f := by
  have he : (cellQ0CLM (hf.toLp f) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      cellQ0 f := (cellQ0CLM_ae (hf.toLp f)).trans (cellQ0_congr_ae _ _ hf.coeFn_toLp)
  rw [cellL2Norm_eq_of_class _ _ he, cellL2Norm_eq_toLp f hf]
  have hb := ENNReal.ofReal_le_ofReal (cellQ0CLM_norm_le (hf.toLp f))
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual Bloch forcing polynomial composed with bounded evolution is analytic in the complete operator algebra. -/

theorem cellBlochPolynomialEvolution_analyticAt {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (sol : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b)
    (δ : X → Fin 2 → ℂ) (q : X → Lp ℂ ∞ (volume.restrict (Icc a b))) (x : X)
    (hδ : AnalyticAt ℂ δ x) (hq : AnalyticAt ℂ q x) :
    AnalyticAt ℂ (fun y => cellEnergyEvolutionForcingLiftCLM a b sol
      (cellBlochPolynomialForcing hab C hG V hv hb (δ y) (q y))) x :=
  ((cellEnergyEvolutionForcingLiftCLM a b sol).analyticAt
    (cellBlochPolynomialForcing hab C hG V hv hb (δ x) (q x))).comp
      (f := fun y => cellBlochPolynomialForcing hab C hG V hv hb (δ y) (q y))
      (x := x) (cellBlochPolynomialForcing_analyticAt hab C hG V hv hb δ q x hδ hq)

theorem cellBlochPolynomialForcing_zero {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) :
    cellBlochPolynomialForcing hab C hG V hv hb 0 0 = 0 := by
  simp only [cellBlochPolynomialForcing, Pi.zero_apply, zero_smul, zero_mul,
    map_zero, Fin.sum_univ_two, zero_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniformly local boundedness of the literal mean-free source projection. -/

/-- Joint almost measurability and a finite uniformly local norm suffice for projection boundedness. -/
theorem cellQ0_cellUlNorm_le (f : ℝ → Vec 2 → ℂ)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm Set.univ f < ⊤) :
    cellUlNorm Set.univ (fun t => cellQ0 (f t)) ≤ 2 * cellUlNorm Set.univ f := by
  have hs := cellUl_memLp_slices_ae f hm hf
  apply cellUlNorm_le_of_window_sq_bound
  intro a
  have ha : ∀ᵐ t ∂volume.restrict (Set.Icc a (a + 1) ∩ Set.univ),
      cellL2Norm (cellQ0 (f t)) ^ 2 ≤ 4 * cellL2Norm (f t) ^ 2 := by
    filter_upwards [ae_mono (Measure.restrict_le_self) hs] with t ht
    have hb := pow_le_pow_left' (cellQ0_cellL2Norm_le (f t) ht) 2
    norm_num only [mul_pow, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num] at hb
    exact hb
  calc
    _ ≤ ∫⁻ t in Set.Icc a (a + 1) ∩ Set.univ, 4 * cellL2Norm (f t) ^ 2 := lintegral_mono_ae ha
    _ = 4 * ∫⁻ t in Set.Icc a (a + 1) ∩ Set.univ, cellL2Norm (f t) ^ 2 := by
      rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 4 * cellUlNorm Set.univ f ^ 2 := mul_le_mul' le_rfl (cellUl_window_integral_le Set.univ f a)
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual projection bounds for uniformly bounded L2 time slices. -/

/-- The literal mean-free projection of uniformly bounded L2 slices is an admissible source. -/
theorem cellQ0_uniform_ul_bound (f : ℝ → Vec 2 → ℂ) (A : ℝ≥0∞)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hA : A < ⊤) (hb : ∀ t, cellL2Norm (f t) ≤ A) :
    cellUlNorm univ (fun t => cellQ0 (f t)) ≤ 2 * A ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellQ0 (f p.1) p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  refine ⟨cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_),
    cellQ0_aestronglyMeasurable hm⟩
  exact (cellQ0_cellL2Norm_le (f t) ((hb t).trans_lt hA)).trans (by gcongr; exact hb t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual inversion of a parameter-jet forcing with its already constructed lower-order state. -/

/-- The first differentiated cell equation has a genuine bounded mean-zero solution. -/
theorem cellInverse_metricJetStep_exists
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : cellMetricSupNorm A < ⊤) (hAm : Measurable (Function.uncurry A))
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    (D : ℝ → RawJet2 1 ℂ)
    (hDm : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hD : cellEnergyNorm univ D < ⊤) :
    ∃ E : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t))
        (F + cellMetricFlux A D) E ∧
      cellEnergyNorm univ E ≤ ENNReal.ofReal 13 *
        (cellUlNorm univ f + cellUlNorm univ F +
          2 * cellMetricSupNorm A * cellEnergyNorm univ D) := by
  have hfluxm := cellMetricFlux_aestronglyMeasurable univ A D hAm hDm
  have hflux := cellMetricFlux_ul_bound univ A hA hAm D hDm
  have hfluxfinite : cellUlNorm univ (cellMetricFlux A D) < ⊤ :=
    hflux.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hA) hD)
  have hR := cellUlNorm_add univ F (cellMetricFlux A D) hFm hfluxm
  obtain ⟨E, hE, hb⟩ := cellAllTimeInverse_exists_bound_ae hG hv f
    (F + cellMetricFlux A D) hfm (hFm.add hfluxm) hf
    (hR.trans_lt (ENNReal.add_lt_top.mpr ⟨hF, hfluxfinite⟩))
  refine ⟨E, hE, hb.trans ?_⟩
  have hRf := hR.trans (add_le_add le_rfl hflux)
  rw [add_assoc]
  gcongr

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual admissibility and bounds for the affine scalar source in the fibre graph. -/

/-- The affine multiplier estimate holds on each literal spatial L2 slice. -/
theorem cellAffineMultiplier_cellL2Norm_le (b f : Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable b) (hB : ∀ x, ‖b x‖ ≤ B)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (fun x => b x * (1 + f x)) ≤
      ENNReal.ofReal B * (1 + cellL2Norm f) := by
  have hm : AEStronglyMeasurable (fun x => b x * (1 + f x))
      (volume.restrict AVenhance.unitCube) :=
    hb.aestronglyMeasurable.mul (aestronglyMeasurable_const.add hf.aestronglyMeasurable)
  apply (cellL2Norm_mul_le b (fun x => 1 + f x) B hm
    (Filter.Eventually.of_forall hB)).trans
  gcongr
  have he := eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (f := fun _ : Vec 2 => (1 : ℂ)) (g := f)
    (μ := volume.restrict AVenhance.unitCube)
  have hc : cellL2Norm (fun _ : Vec 2 => (1 : ℂ)) = 1 := by
    rw [cellL2Norm_const]
    simp
  change cellL2Norm (fun x => 1 + f x) ≤
    cellL2Norm (fun _ : Vec 2 => (1 : ℂ)) + cellL2Norm f at he
  rw [hc] at he
  exact he

/-- A bounded multiplier times one plus an actual cell value is a jointly almost measurable source. -/
theorem cellAffineMultiplier_ul_bound
    (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution univ C src F D) :
    cellUlNorm univ (fun t x => b t x * (1 + cellValue D t x)) ≤
      ENNReal.ofReal B * (1 + cellEnergyNorm univ D) ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2 * (1 + cellValue D p.1 p.2))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  refine ⟨cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_), ?_⟩
  · exact (cellAffineMultiplier_cellL2Norm_le (b t) (cellValue D t) B
      (hb.comp (measurable_const.prodMk measurable_id)) (hB t)
      (hD.2.2.1 t (mem_univ t)).1).trans (by
        gcongr
        exact cellValue_cellL2Norm_le_energy D t)
  · exact hb.aestronglyMeasurable.mul
      (aestronglyMeasurable_const.add (hD.2.2.2.1 (valueIndex2 1)))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual full Bloch forcing polynomial composed with the bounded baseline solution map. -/

def cellBlochPolynomialEvolutionOperator {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (sol : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) : CellEnergyOperator a b :=
  cellEnergyEvolutionForcingLiftCLM a b sol
    (cellBlochPolynomialForcing hab C hG V hv hb δ q)

theorem cellBlochPolynomialEvolutionOperator_apply {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (sol : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) (z : CellEnergySpace a b) :
    cellEnergyOperatorApplyCLM a b (cellBlochPolynomialEvolutionOperator hab C hG V hv hb sol δ q) z =
      sol (cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z) := by
  unfold cellBlochPolynomialEvolutionOperator
  rw [cellEnergyEvolutionForcingLift_apply]
  have he := congrArg (cellEnergyForcingOperatorEvalCLM a b z)
    (cellBlochPerturbationDatumCLM_eq_polynomial hab C hG V hv hb δ q)
  have hh := congrArg sol he
  change sol (cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z) =
    sol (cellEnergyForcingOperatorEvalCLM a b z (cellBlochPolynomialForcing hab C hG V hv hb δ q)) at hh
  exact hh.symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Linear projected multiplier estimates for the nonlinear graph contraction. -/

/-- Projected bounded multiplication of an actual cell inverse is an admissible linear forcing. -/
theorem cellProjectedMultiplier_ul_bound
    (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) :
    cellUlNorm univ (fun t => cellQ0 (fun x => b t x * cellValue D t x)) ≤
      2 * (ENNReal.ofReal B * cellEnergyNorm univ D) ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      cellQ0 (fun x => b p.1 x * cellValue D p.1 x) p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hm := (cellBoundedMultiplier_ul_bound b B hb hB hD.1).2
  apply cellQ0_uniform_ul_bound (fun t x => b t x * cellValue D t x) _ hm
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.2.2
  · intro t
    have hmt : AEStronglyMeasurable (fun x => b t x * cellValue D t x)
        (volume.restrict AVenhance.unitCube) :=
      ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
        (hD.1.2.2.1 t (mem_univ t)).1.aestronglyMeasurable
    exact (cellL2Norm_mul_le (b t) (cellValue D t) B hmt
      (Filter.Eventually.of_forall (hB t))).trans (by
        gcongr
        exact cellValue_cellL2Norm_le_energy D t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Genuine L2 membership of bounded multiplier forcing on every L2 trace. -/

/-- Bounded measurable multiplication preserves actual literal cell L2 membership. -/
theorem cellMultiplier_memLp (b f : Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable b) (hB : ∀ x, ‖b x‖ ≤ B)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    MemLp (fun x => b x * f x) 2 (volume.restrict AVenhance.unitCube) := by
  have hm : AEStronglyMeasurable (fun x => b x * f x)
      (volume.restrict AVenhance.unitCube) := hb.aestronglyMeasurable.mul hf.aestronglyMeasurable
  exact (cellL2Norm_mul_le b f B hm (Filter.Eventually.of_forall hB)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

/-- The affine bounded multiplier also preserves actual literal cell L2 membership. -/
theorem cellAffineMultiplier_memLp (b f : Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable b) (hB : ∀ x, ‖b x‖ ≤ B)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    MemLp (fun x => b x * (1 + f x)) 2 (volume.restrict AVenhance.unitCube) := by
  exact (cellAffineMultiplier_cellL2Norm_le b f B hb hB hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨by simp, hf⟩))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Uniform estimates for every representative of the all-time mean-zero inverse. -/

/-- Uniqueness transfers the actual existence estimate to any bounded inverse solution. -/
theorem cellAllTimeInverse_bound_ae
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D) :
    cellEnergyNorm univ D ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ f + cellUlNorm univ F) := by
  obtain ⟨E, hE, hb⟩ := cellAllTimeInverse_exists_bound_ae hG hv f F hfm hFm hf hF
  have he := cellAllTimeInverse_unique_arbitrary_source hG hv (fun t => cellQ0 (f t)) F D E hD hE
  rw [cellSolution_energyNorm_congr hD.1 hE.1 (fun t _ => he t)]
  exact hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every-time bounds for bounded multiplier means of actual cell solution traces. -/

/-- A bounded measurable mean multiplier is controlled by the actual trajectory energy at every time. -/
theorem cellBoundedMean_energy_bound (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution Set.univ C src F D) (t : ℝ) :
    ‖cellMean (fun x => b t x * cellValue D t x)‖ₑ ≤
      ENNReal.ofReal B * cellEnergyNorm Set.univ D := by
  have hm : Measurable (b t) := hb.comp ((measurable_const (a := t)).prodMk measurable_id)
  have hf := (hD.2.2.1 t (Set.mem_univ t)).1
  have hp := cellMultiplier_memLp (b t) (cellValue D t) B hm (hB t) hf
  exact (cellMean_enorm_le_cellL2Norm _ hp).trans
    ((cellL2Norm_mul_le (b t) (cellValue D t) B hp.aestronglyMeasurable
      (Filter.Eventually.of_forall (hB t))).trans
      (mul_le_mul' le_rfl (cellValue_cellL2Norm_le_energy D t)))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Projected affine forcing is admissible for every actual bounded cell inverse. -/

/-- Mean-free affine multiplier forcing obeys the literal energy bound and joint measurability. -/
theorem cellProjectedAffineMultiplier_ul_bound
    (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) :
    cellUlNorm univ (fun t => cellQ0 (fun x => b t x * (1 + cellValue D t x))) ≤
      2 * (ENNReal.ofReal B * (1 + cellEnergyNorm univ D)) ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      cellQ0 (fun x => b p.1 x * (1 + cellValue D p.1 x)) p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hm := (cellAffineMultiplier_ul_bound b B hb hB hD.1).2
  apply cellQ0_uniform_ul_bound (fun t x => b t x * (1 + cellValue D t x)) _ hm
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨by simp, hD.2.2⟩)
  · intro t
    exact (cellAffineMultiplier_cellL2Norm_le (b t) (cellValue D t) B
      (hb.comp (measurable_const.prodMk measurable_id)) (hB t)
      (hD.1.2.2.1 t (mem_univ t)).1).trans (by
        gcongr
        exact cellValue_cellL2Norm_le_energy D t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual perturbed solution satisfies the baseline evolution fixed-point equation by weak uniqueness. -/

theorem cellBlochEvolution_fixedPoint {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b)))
    (d : CellFiniteEnergyDatum a b) (z : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution
      { C with θ := C.θ + δ, κ := fun t => C.κ t + q t } hG V hv hb d z) :
    let sol := cellFiniteEnergyEvolutionCLM hab C hG V k hv hb hκ hκb
    z = sol (cellBlochExternalDatum δ d) +
      sol (cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z) := by
  dsimp only
  let sol := cellFiniteEnergyEvolutionCLM hab C hG V k hv hb hκ hκb
  let e := cellBlochExternalDatum δ d
  let p := cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z
  have ht := cellBlochEvolution_transfer hab C hG V hv hb δ q d z hz
  have he : z = sol (e + p) := cellFiniteEnergyEvolution_unique hab C hG V k hv hb hκb
    (e + p) z (sol (e + p)) ht
    (cellFiniteEnergyEvolutionCLM_solves hab C hG V k hv hb hκ hκb (e + p))
  exact he.trans (sol.map_add e p)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal zero trajectory is an actual bounded all-time mean-zero inverse. -/

/-- Zero scaling gives the literal zero inverse from any actual bounded inverse. -/
theorem cellInverse_zero_of_inverse {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (hD : IsCellInverseValue C src F D) :
    IsCellInverseValue C 0 0 0 := by
  simpa only [zero_smul] using cellInverse_complex_smul hD (0 : ℂ)

/-- The actual zero inverse exists for all admissible cell coefficients. -/
theorem cellInverse_zero {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ 0 0 0 := by
  have hf : cellUlNorm univ (0 : ℝ → Vec 2 → ℂ) < ⊤ := by
    simp [cellUlNorm, cellL2Norm]
  have hF : cellUlNorm univ (0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) < ⊤ := by
    simp [cellUlNorm, cellL2Norm]
  obtain ⟨D, hD, _⟩ := cellAllTimeInverse_exists_bound_ae hG hv
    (0 : ℝ → Vec 2 → ℂ) (0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    aestronglyMeasurable_const aestronglyMeasurable_const hf hF
  exact cellInverse_zero_of_inverse hD

/-! Actual certified bounded inverse trajectories for triangular fibre coefficient constructions. -/

/-- An actual bounded mean-zero cell trajectory, retaining its forcing and its full solution certificate. -/
structure CellInverseDatum (C : CellCoefficients) where
  raw : ℝ → RawJet2 1 ℂ
  source : ℝ → Vec 2 → ℂ
  flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)
  isInverse : IsCellInverseValue C source flux raw

/-- The zero datum is a genuine all-time inverse, rather than a merely formal initial coefficient. -/
def cellInverseZeroDatum {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) :
    CellInverseDatum ⟨G, v, 0, 0⟩ :=
  ⟨0, 0, 0, cellInverse_zero hG hv⟩

/-- A certified choice of the genuine mean-zero inverse for jointly almost measurable forcing. -/
def cellInverseDatum_of_forcing {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    CellInverseDatum ⟨G, v, 0, 0⟩ :=
  let he := cellAllTimeInverse_exists_bound_ae hG hv f F hm hFm hf hF
  ⟨he.choose, fun t => cellQ0 (f t), F, he.choose_spec.1⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual cell inversion for the finite triangular forcing in each parameter-jet equation. -/

/-- Once lower-order states are constructed, the literal next jet equation has a bounded mean-zero solution. -/
theorem cellInverse_jetEquation_exists
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hG0 : IsCellMetric (Gj 0))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    (hG : ∀ β ∈ cellJetFluxIndices α, cellMetricSupNorm (Gj β) < ⊤)
    (hGm : ∀ β ∈ cellJetFluxIndices α, Measurable (Function.uncurry (Gj β)))
    (hc : ∀ β ∈ cellJetFluxIndices α,
      cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2)) < ⊤)
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p.1 a p.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    ∃ E : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨Gj 0, v, 0, 0⟩ (fun t => cellQ0 (f t))
        (F + cellMetricJetFlux Gj cj α) E := by
  have hJm := cellMetricJetFlux_aestronglyMeasurable Gj cj α hGm hcm
  have hJ := cellMetricJetFlux_ul_lt_top Gj cj α hG hGm hc hcm
  have hsum := cellUlNorm_add univ F (cellMetricJetFlux Gj cj α) hFm hJm
  obtain ⟨E, hE, _⟩ := cellAllTimeInverse_exists_bound_ae hG0 hv f
    (F + cellMetricJetFlux Gj cj α) hfm (hFm.add hJm) hf
    (hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨hF, hJ⟩))
  exact ⟨E, hE⟩

end AVRegularity.CycleEvolution
end
