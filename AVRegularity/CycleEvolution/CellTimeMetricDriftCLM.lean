-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellWeakIdentityAbsoluteSeries
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.CycleEvolution

/-! The explicit smaller graph disk absorbs every uniform Bloch frequency error. -/

theorem fibreKernel_frequency_small {Cw : ℝ} (hCw : 0 ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024) :
    Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16 := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hR1 := fibreCoefficientMajorantRadius_le_one hCw
  have hfn := fibreNorm_nonneg ξ
  have hsmall : fibreNorm ξ ≤ 1 / 1024 := by linarith
  have hprod : Cw * fibreCoefficientMajorantRadius Cw ≤ 1 / 104 := by
    unfold fibreCoefficientMajorantRadius
    have hd : 0 < 104 * (Cw + 8) := by positivity
    rw [← mul_div_assoc, mul_one, div_le_iff₀ hd]
    nlinarith
  have hf := mul_le_mul_of_nonneg_left hξ hCw
  have hlin : Cw * fibreNorm ξ ≤ 1 / (104 * 1024) := by
    nlinarith
  have hsquare := mul_le_mul hsmall hsmall hfn (by norm_num : (0 : ℝ) ≤ 1 / 1024)
  have hπ : 2 ≤ Real.pi := Real.two_le_pi
  nlinarith [sq_nonneg Real.pi]

/-! Explicit positive phase derivative constants, depending only on the scaled drift bound. -/

def fibrePhaseJetConstant (Cw : ℝ) (n : ℕ) : ℝ :=
  if n = 1 then 8 * (6 * Cw + 24) / fibreCoefficientMajorantRadius Cw ^ 2
  else analyticBallDerivativeConstant n * (6 * Cw + 24) /
    (fibreCoefficientMajorantRadius Cw / 2) ^ n

theorem fibrePhaseJetConstant_pos {Cw : ℝ} (hCw : 0 ≤ Cw) (n : ℕ) :
    0 < fibrePhaseJetConstant Cw n := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hn := analyticBallDerivativeConstant_pos n
  unfold fibrePhaseJetConstant
  split_ifs <;> positivity

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact weak expansion of Bloch diffusion for the spatially constant frozen metric. -/

theorem cellConstantMetric_bloch_expansion {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDiffusionForm hG θ t u z =
      -(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) *
        cellComplexPair (cellDerivativeCLM j u) (cellDerivativeCLM k z)) -
      (∑ j : Fin 2, (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k) *
        cellComplexPair (torusHkValueCLM u) (cellDerivativeCLM j z)) -
      (∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) *
        cellComplexPair (torusHkValueCLM u) (torusHkValueCLM z) := by
  have hs : G t 1 0 = G t 0 1 := congrFun (congrFun (hG.2.2.1 t 0) 0) 1
  unfold cellComplexDiffusionForm
  simp_rw [cellConstantMetric_bloch_entry hG θ t]
  simp only [Fin.sum_univ_two]
  rw [hs]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! All-time fixed-test equation for the constructed Hilbert trace. -/

/-- The fixed-test primitive identity holds everywhere for the continuous trace. -/
theorem CellWeakTimeData.primitive_limit_moment {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial)
    (U : C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)))
    (hU : Tendsto (fun N => cellDualPrimitiveCurve hab.le N initial g h.dual) atTop (𝓝 U))
    (z : TorusHk 1 ℂ) :
    ∀ t ∈ Icc a b, inner ℝ (extendCurve hab.le U t) (torusHkValueCLM z) =
      inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t, inner ℝ (g r) z := by
  have hp := cellWeakPair_intervalIntegrable ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le g h.dual z
  have hprim : ContinuousOn (fun t => ∫ r in a..t, inner ℝ (g r) z) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hp left_mem_uIcc
  have hl : ContinuousOn (fun t => inner ℝ (extendCurve hab.le U t) (torusHkValueCLM z))
      (Icc a b) := ((continuous_extendCurve hab.le U).inner continuous_const).continuousOn
  have hr : ContinuousOn (fun t => inner ℝ initial (torusHkValueCLM z) +
      ∫ r in a..t, inner ℝ (g r) z) (Icc a b) := continuousOn_const.add hprim
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne _ hl hr
  filter_upwards [h.primitive_limit_agrees hab U hU, h.moment z,
    ae_restrict_mem measurableSet_Icc] with t ht hm hti
  rw [extendCurve_eq_of_mem hab.le U hti, ht hti]
  exact hm

/-- Integrated Bochner weak time data give a continuous Hilbert curve with the full time equation. -/
theorem CellWeakTimeData.exists_hilbert_curve {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) :
    ∃ U : C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)),
      CellWeakHilbertCurve a b (extendCurve hab.le U) slice g ∧
      extendCurve hab.le U a = initial := by
  obtain ⟨U, hU⟩ := h.exists_primitive_limit hab
  refine ⟨U, ⟨(continuous_extendCurve hab.le U).continuousOn, h.state, h.dual, ?_, ?_⟩, ?_⟩
  · filter_upwards [h.primitive_limit_agrees hab U hU, ae_restrict_mem measurableSet_Icc]
      with t ht hti
    rw [extendCurve_eq_of_mem hab.le U hti]
    exact ht hti
  · intro s hs t ht hst z
    have hms := h.primitive_limit_moment hab U hU z s hs
    have hmt := h.primitive_limit_moment hab U hU z t ht
    have has := cellWeakPair_intervalIntegrable ⟨le_rfl, hab.le⟩ hs hs.1 g h.dual z
    have hst' := cellWeakPair_intervalIntegrable hs ht hst g h.dual z
    have hi := intervalIntegral.integral_add_adjacent_intervals has hst'
    linarith
  · rw [extendCurve_eq_of_mem hab.le U ⟨le_rfl, hab.le⟩]
    exact h.primitive_limit_initial hab U hU

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Convergence of the actual triangular reciprocal coefficients from a small scalar majorant. -/

theorem fibreScalarInverseCoefficient_weighted_le_two (d : ℕ × ℕ → ℝ → ℂ)
    (ρ : ℝ≥0∞) (hρ : ρ < ⊤) (hd : ∀ p, (⨆ t, ‖d p t‖ₑ) < ⊤)
    (hsmall : (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖d p t‖ₑ) ≤ 1 / 2) :
    (∑' p, fibreCoefficientWeight ρ p *
      ⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ) ≤ 2 := by
  apply fibreCoefficient_weighted_total_le
  intro N
  exact fibreScalarInverse_prefix_le_two ρ (fun p => ⨆ t, ‖d p t‖ₑ)
    (fun p => ⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ)
    (fibreScalarInverseCoefficient_uniform_full_recurrence d) hsmall
    (fibreScalarInverseCoefficient_uniform_lt_top d hd) hρ N

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The plain actual cell generator is exactly diffusion minus divergence-free transport. -/

theorem cellComplexGenerator_plain
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨G, v, 0, 0⟩ hG V hv.1 hb t u z =
      cellComplexDiffusionForm hG (fun _ => 0) t u z - cellComplexDriftForm v V hv hb t u z := by
  rw [cellComplexGenerator_decomposition ⟨G, v, 0, 0⟩ hG V hv hb]
  change cellComplexDiffusionForm hG (fun _ => 0) t u z -
    cellComplexShiftedDriftForm v V hv hb (fun _ => 0) t u z +
      cellComplexPair (cellScalarCLM 0 (torusHkValueCLM u)) (torusHkValueCLM z) = _
  simp only [cellComplexShiftedDriftForm, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, cellScalarCLM_smul, zero_smul, cellComplexPair_zero_left]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Every actual scalar potential is a pivot-dual zeroth-order perturbation, including for forced solutions. -/

theorem cellDualDerivative_potential (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u S F =
      cellDualDerivative {C with κ := fun _ => 0} hG V hv hb t u S F +
      cellPivotDualCLM (cellScalarCLM (C.κ t) (torusHkValueCLM u)) := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair (cellDualDerivative C hG V hv hb t u S F) z =
      cellDualComplexPair (cellDualDerivative {C with κ := fun _ => 0} hG V hv hb t u S F +
        cellPivotDualCLM (cellScalarCLM (C.κ t) (torusHkValueCLM u))) z := by
    rw [cellDualComplexPair_add_left, cellDualComplexPair_actual, cellDualComplexPair_actual,
      cellPivotDual_complex_pair, cellComplexPair_scalar_left, cellComplexGenerator_potential]
    ring
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Raw periodic realization of an H¹-a.e. curve with arbitrary L² trace values. -/

/-- The exceptional-time jet preserves the L² value and assigns zero derivative representatives. -/
def cellTraceFallback (u : ComplexCellL2) (a : JetIndex2 1) : Vec 2 → ℂ :=
  if a = valueIndex2 1 then cellPeriodize u else 0

/-- A Bochner H¹ curve and its L² trace admit periodic, jointly L² raw jet representatives.
The trace is preserved at every time, including exceptional non-H¹ times. -/
theorem cellWeak_exists_raw_realization (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ) (hs : MemLp slice 2 (volume.restrict I))
    (ha : ∀ᵐ t ∂volume.restrict I, u t = torusHkValueCLM (slice t)) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      (∀ᵐ t ∂volume.restrict I, HasPeriodicOrderedWeakJet (D t)) ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ᵐ t ∂volume.restrict I, ∀ a,
        ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a) ∧
      (∀ t a, AVenhance.IsZ2Periodic (D t a)) := by
  classical
  obtain ⟨f, hf, he⟩ := cellBochner_exists_joint_jet I slice hs
  let Good := fun t => u t = torusHkValueCLM (slice t) ∧ ∀ a,
    ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f a t
  have hg : ∀ᵐ t ∂volume.restrict I, Good t := ha.and he
  let D := fun t a => if Good t then cellPeriodize (f a t) else cellTraceFallback (u t) a
  have hd (t) (ht : Good t) (a) :
      ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a := by
    dsimp only [D]
    rw [ite_eq_left ht]
    exact (ht.2 a).trans (cellPeriodize_ae _).symm
  have hp (t a) : AVenhance.IsZ2Periodic (D t a) := by
    dsimp only [D]
    split_ifs
    · exact cellPeriodize_periodic _
    · unfold cellTraceFallback
      split_ifs
      · exact cellPeriodize_periodic _
      · intro n x
        rfl
  refine ⟨D, ?_, ?_, ?_, ?_, hp⟩
  · filter_upwards [hg] with t ht
    exact cellPeriodicJet_of_class (D t) (slice t) (hp t) (hd t ht)
  · intro t
    by_cases ht : Good t
    · rw [ht.1]
      exact hd t ht (valueIndex2 1)
    · dsimp only [D, cellValue]
      rw [ite_eq_right ht]
      simp only [cellTraceFallback]
      exact (cellPeriodize_ae _).symm
  · intro a
    apply (hf a).ae_eq
    have htime := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict I)
      (ν := volume.restrict AVenhance.unitCube)).ae hg
    have hspace := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict I)
      (ν := volume.restrict AVenhance.unitCube)).ae (ae_restrict_mem cellCube_measurable)
    filter_upwards [htime, hspace] with p ht hx
    dsimp only [D]
    rw [ite_eq_left ht]
    exact (cellPeriodize_eq_of_mem _ _ hx).symm
  · filter_upwards [hg] with t ht
    exact hd t ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Jointly measurable bounded spatial coefficients act on actual Bochner L2 source classes. -/

theorem cellTimeCoefficient_memLp (I : Set ℝ) (b : ℝ → Vec 2 → ℂ)
    (hb : Measurable (Function.uncurry b)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t x, ‖b t x‖ ≤ B) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) :
    MemLp (fun t => cellCoefficientComplexCLM (b t)
      ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      B hB (hbound t) (u t)) 2 (volume.restrict I) := by
  obtain ⟨f, hm, hf, he⟩ := cellBochner_exists_measurable_realization I u hu
  let g := fun t x => b t x * f t x
  have hg : MemLp (Function.uncurry g) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    apply hf.of_le_mul ((hb.mul hm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun p =>
      (norm_mul_le (b p.1 p.2) (f p.1 p.2)).trans
        (mul_le_mul_of_nonneg_right (hbound p.1 p.2) (norm_nonneg _)))
  have hslice := cellSourceSlice_memLp I g hg
  apply hslice.ae_eq
  filter_upwards [he, cellSource_memLp_slices I f hf] with t ht hft
  apply cellSourceSlice_eq_of_ae g t
  have huf := cellSourceSlice_ae f t hft
  rw [ht] at huf
  have hcoef := cellCoefficientCLM_ae (b t)
    ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    B hB (hbound t) (u t)
  filter_upwards [huf, hcoef] with x hu' hc'
  rw [cellCoefficientComplexCLM_eq (b t)
    ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    B hB (hbound t) (u t)]
  dsimp only [g]
  rw [hc', hu']

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The normalized scalar gauge has the exact subtractive pivot-dual form. -/

theorem cellDualDerivative_negative_potential
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (lam : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative ⟨G, v, θ, fun t => -lam t⟩ hG V hv hb t u S F =
      cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t u S F -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM u)) := by
  rw [cellDualDerivative_potential]
  simp only [cellScalarCLM_smul, neg_smul, map_neg, sub_eq_add_neg]
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! ENNReal norm-square identities for raw continuous L² traces. -/

/-- The extended cell norm of an L² representative equals its Hilbert norm. -/
theorem cellL2Norm_eq_of_class (f : Vec 2 → ℂ) (u : ComplexCellL2)
    (he : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    cellL2Norm f = ENNReal.ofReal ‖u‖ := by
  change eLpNorm f 2 _ = _
  rw [← eLpNorm_congr_ae he]
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp u).eLpNorm_ne_top]

/-- The raw representative's square integral is the extended Hilbert norm square. -/
theorem cellTrace_square_lintegral (f : Vec 2 → ℂ) (u : ComplexCellL2)
    (he : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    (∫⁻ x in AVenhance.unitCube, ‖f x‖ₑ ^ 2) = (ENNReal.ofReal ‖u‖) ^ 2 := by
  rw [← cellL2Norm_sq_eq_lintegral ((Lp.memLp u).ae_eq he).aestronglyMeasurable,
    cellL2Norm_eq_of_class f u he]

/-- Raw representatives inherit continuous L² traces from their continuous Hilbert classes. -/
theorem cellRaw_trace_continuous (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : ContinuousOn u I) (f : ℝ → Vec 2 → ℂ)
    (he : ∀ t ∈ I, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f t) :
    ∀ t₀ ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube, ‖f t x - f t₀ x‖ₑ ^ 2)
      (𝓝[I] t₀) (𝓝 0) := by
  intro t₀ ht₀
  have hn := ((hu t₀ ht₀).sub (tendsto_const_nhds (x := u t₀))).norm
  have hE := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hn.pow 2)
  simp only [Function.comp_def, Pi.pow_apply, Pi.sub_apply, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero] at hE
  apply hE.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  exact (cellTrace_square_lintegral (fun x => f t x - f t₀ x) (u t - u t₀)
    ((Lp.coeFn_sub _ _).trans ((he t ht).sub (he t₀ ht₀)))).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Universal energy estimate for the actual weak cell equation. -/

/-- The actual weak cell equation has the same constants as its finite approximations. -/
theorem cellActualWeak_energy_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t))) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2 ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (t - a)) := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  let f := fun s => ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2
  let d := fun s => (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    have hθ : 0 ≤ ∑ j, ‖C.θ j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [R]
    positivity
  have hf : IntervalIntegrable f volume a b := by
    have hsum := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
      (cellTime_normSq_intervalIntegrable hab (hF 1))
    simpa only [f, Fin.sum_univ_two, Pi.add_def] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsum.const_mul 9)
  have hd : IntervalIntegrable d volume a b :=
    (cellTime_gradientSq_intervalIntegrable hab slice h.state).const_mul (1 / 2)
  apply h.energy_dissipation_le_gronwall hab R hR f d hf hd
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [f]; positivity)
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [d]; positivity)
  · filter_upwards [h.agrees] with s hs
    rw [cellDualDerivative_pairing, hs]
    simpa only [d, R, f, add_assoc] using
      cellGenerator_source_energy_bound C hG V k hv hb hκ s (slice s) (S s) (F s)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Jointly measurable spatial multipliers act as bounded complex-linear maps on temporal L2 classes. -/

def cellTimeCoefficientCLM (I : Set ℝ) (b : ℝ → Vec 2 → ℂ)
    (hb : Measurable (Function.uncurry b)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t x, ‖b t x‖ ≤ B) :
    Lp ComplexCellL2 2 (volume.restrict I) →L[ℂ] Lp ComplexCellL2 2 (volume.restrict I) := by
  let A := fun t => cellCoefficientComplexCLM (b t)
    ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B hB (hbound t)
  let hm := fun u : Lp ComplexCellL2 2 (volume.restrict I) =>
    cellTimeCoefficient_memLp I b hb B hB hbound u (Lp.memLp u)
  let R := fun u : Lp ComplexCellL2 2 (volume.restrict I) => (hm u).toLp (fun t => A t (u t))
  have hr u : R u =ᵐ[volume.restrict I] fun t => A t (u t) := (hm u).coeFn_toLp
  let L : Lp ComplexCellL2 2 (volume.restrict I) →ₗ[ℂ] Lp ComplexCellL2 2 (volume.restrict I) :=
    { toFun := R
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [hr (u + v), hr u, hr v, Lp.coeFn_add u v,
          Lp.coeFn_add (R u) (R v)] with t hsum hu hv hin hout
        change R (u + v) t = (R u + R v) t
        rw [hsum, hout]
        change A t ((u + v) t) = R u t + R v t
        rw [hin, hu, hv]
        exact (A t).map_add _ _
      map_smul' := fun c u => by
        change R (c • u) = c • R u
        apply Lp.ext
        filter_upwards [hr (c • u), hr u, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (R u)] with t hcu hu hin hout
        rw [hcu, hout]
        change A t ((c • u) t) = c • R u t
        change (c • u) t = c • u t at hin
        rw [hin, hu]
        exact (A t).map_smul c _ }
  apply L.mkContinuous B
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hr u] with t ht
  change ‖R u t‖ ≤ B * ‖u t‖
  rw [ht]
  exact cellCoefficientComplexCLM_apply_norm_le (b t) _ B hB (hbound t) (u t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! A uniform-in-time L2 bound for the actual weak Hilbert cell solution. -/

/-- The actual weak cell energy inequality controls every continuous L2 trace. -/
theorem cellActualWeak_energy_sup_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t))) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
        Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a)) := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  let budget := ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    dsimp only [R]
    positivity
  have hbudget : 0 ≤ budget := by
    have hi : 0 ≤ ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => by positivity)
    exact add_nonneg (sq_nonneg _) hi
  have he := cellActualWeak_energy_bound hab C hG V k hv hb hκ S F hS hF u slice h
  intro t ht
  have het := he t ht
  have hd : 0 ≤ ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => by positivity)
  have hex : Real.exp (R * (t - a)) ≤ Real.exp (R * (b - a)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hR
  have hm := mul_le_mul_of_nonneg_left hex hbudget
  dsimp only [R, budget] at hm
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniqueness for the actual weak cell equation with common forcing. -/

/-- Common scalar and divergence forcing cancels in the difference dual equation. -/
theorem cellDualDerivative_difference_pairing
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u v z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    inner ℝ (cellDualDerivative C hG V hv hb t u S F -
      cellDualDerivative C hG V hv hb t v S F) z = cellGeneratorForm C hG V hv hb t (u - v) z := by
  rw [inner_sub_left, cellDualDerivative_pairing, cellDualDerivative_pairing]
  have he := congrArg (fun L : TorusHk 1 ℂ →L[ℝ] ℝ => L z)
    ((cellGeneratorForm C hG V hv hb t).map_sub u v)
  simp only [sub_apply] at he
  rw [he]
  ring

/-- The actual cell equation has a cutoff-independent one-sided growth bound. -/
theorem cellGenerator_garding (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (t : ℝ) (z : TorusHk 1 ℂ) :
    2 * cellGeneratorForm C hG V hv hb t z z ≤
      300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * ‖torusHkValueCLM z‖ ^ 2 := by
  have hp := cellGenerator_source_energy_bound C hG V k hv hb hκ t z 0 (fun _ => 0)
  simp only [cellSourceFunctional, ContinuousLinearMap.comp_apply, sub_apply, sum_apply,
    innerSL_apply_apply, inner_zero_left, Finset.sum_const_zero, sub_self, add_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hp
  have hd : 0 ≤ (1 / 2 : ℝ) * ∑ j : Fin 2, ‖cellDerivativeCLM j z‖ ^ 2 := by positivity
  linarith

/-- All Hilbert traces of weak solutions of the actual cell equation agree for common initial data. -/
theorem cellActualWeak_unique {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u v : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other
      (fun t => cellDualDerivative C hG V hv hb t (other t) (S t) (F t)))
    (hi : u a = v a) : ∀ t ∈ Icc a b, u t = v t := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    have hθ : 0 ≤ ∑ j, ‖C.θ j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [R]
    positivity
  apply cellWeakHilbert_unique_of_difference_growth hab h h' hi R hR
  filter_upwards [h.agrees, h'.agrees] with t ht ht'
  rw [cellDualDerivative_difference_pairing, ht, ht', ← map_sub]
  exact cellGenerator_garding C hG V k hv hb hκ t (slice t - other t)

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual conjugation of the complex dual pairing on the H¹ Riesz carrier. -/

theorem cellDualComplexPair_conjugate (g z : TorusHk 1 ℂ) :
    cellDualComplexPair (cellH1Conj g) (cellH1Conj z) = star (cellDualComplexPair g z) := by
  apply Complex.ext
  · simp only [cellDualComplexPair_re, cellH1Conj_inner_both,
      Complex.star_def, Complex.conj_re]
  · rw [cellDualComplexPair_im, cellH1Conj_inner, cellH1Conj_scalar,
      show star Complex.I = -Complex.I from Complex.conj_I,
      cellH1Scalar_neg, cellH1Conj_involutive, inner_neg_right]
    simp only [Complex.star_def, Complex.conj_im, cellDualComplexPair_im]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Jointly measurable raw realization of locally L² H¹ curves on a time domain. -/

/-- Local Bochner H¹ lifts admit one jointly measurable periodic raw realization on their time domain. -/
theorem cellDomainLocalWeak_exists_raw_realization (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hs : ∀ n : ℕ, MemLp slice 2 (volume.restrict (Icc (-(n : ℝ)) n ∩ I)))
    (ha : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Icc (-(n : ℝ)) n ∩ I),
      u t = torusHkValueCLM (slice t)) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      (∀ᵐ t ∂volume.restrict I, HasPeriodicOrderedWeakJet (D t)) ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ᵐ t ∂volume.restrict I, ∀ a,
        ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a) ∧
      (∀ t a, AVenhance.IsZ2Periodic (D t a)) := by
  have hex (n : ℕ) := cellWeak_exists_raw_realization (Icc (-(n : ℝ)) n ∩ I) u slice (hs n) (ha n)
  choose raw hweak htrace hjoint hjet hper using hex
  let D := fun t a => raw (cellLocalTimeIndex t) t a
  have hgood (n : ℕ) : ∀ᵐ t ∂volume.restrict I,
      t ∈ Icc (-(n : ℝ)) n → HasPeriodicOrderedWeakJet (raw n t) ∧
        ∀ a, ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] raw n t a :=
    (ae_restrict_iff' measurableSet_Icc).mp (by
      rw [Measure.restrict_restrict measurableSet_Icc]
      exact (hweak n).and (hjet n))
  have hall := ae_all_iff.mpr hgood
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hall] with t ht
    exact (ht (cellLocalTimeIndex t) (cellLocalTimeIndex_mem t)).1
  · intro t
    exact htrace (cellLocalTimeIndex t) t
  · intro a
    exact cellJoint_selected_aestronglyMeasurable (volume.restrict I) cellLocalTimeIndex cellLocalTimeIndex_measurable
      (fun n => Icc (-(n : ℝ)) n) cellLocalTimeIndex_mem (fun n t x => raw n t a x)
      (fun n => by
        simpa only [Measure.restrict_restrict measurableSet_Icc, Function.uncurry_def] using
          (hjoint n a).aestronglyMeasurable)
  · filter_upwards [hall] with t ht
    exact (ht (cellLocalTimeIndex t) (cellLocalTimeIndex_mem t)).2
  · intro t a
    exact hper (cellLocalTimeIndex t) t a

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Package an actual Galerkin sequence and its weak temporal H¹ limit. -/

/-- Actual finite equations, initial moments, uniform class bounds, and a weak subsequence. -/
structure CellGalerkinLimitData (a b : ℝ) (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (initial : ComplexCellL2) where
  curve : ∀ N, C(Icc a b, CellGalerkinSpace (E := ℂ) N)
  stateLp : ∀ N, MemLp (fun t => (extendCurve hab (curve N) t).val)
    2 (volume.restrict (Icc a b))
  variational : ∀ N, StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
    (fun t => cellGalerkinForm N (cellGeneratorB C hG V hv hb t))
    (fun t => cellGalerkinSource N (cellRawSourceFunctional C.θ src F t))
    (fun t => cellGalerkinValue N (extendCurve hab (curve N) t))
    (fun t => cellGalerkinValue N (linearRhs
      (fun r => cellGalerkinOperator N (cellGeneratorB C hG V hv hb r))
      (fun r => cellGalerkinForcing N (cellRawSourceFunctional C.θ src F r))
      (extendCurve hab (curve N)) t)) (extendCurve hab (curve N))
  initial_value : ∀ N, cellGalerkinValue N (extendCurve hab (curve N) a) =
    cellGalerkinValue N (cellGalerkinL2Initial N initial)
  budget : ℝ
  norm_bound : ∀ N,
    ‖(stateLp N).toLp (fun t => (extendCurve hab (curve N) t).val)‖ ≤ budget
  limit : CellBochnerH1 a b
  subsequence : ℕ → ℕ
  monotone : StrictMono subsequence
  weak : ∀ ell : CellBochnerH1 a b →L[ℝ] ℝ,
    Tendsto (fun n => ell ((stateLp (subsequence n)).toLp
      (fun t => (extendCurve hab (curve (subsequence n)) t).val))) atTop (𝓝 (ell limit))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Jointly measurable raw realization of a locally L² H¹ curve on the whole time line. -/

/-- Local Bochner H¹ lifts with an all-time L² trace admit one jointly measurable periodic raw realization. -/
theorem cellLocalWeak_exists_raw_realization (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hs : ∀ n : ℕ, MemLp slice 2 (volume.restrict (Icc (-(n : ℝ)) n)))
    (ha : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Icc (-(n : ℝ)) n),
      u t = torusHkValueCLM (slice t)) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      (∀ᵐ t ∂volume, HasPeriodicOrderedWeakJet (D t)) ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
        (volume.prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ᵐ t ∂volume, ∀ a,
        ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a) ∧
      (∀ t a, AVenhance.IsZ2Periodic (D t a)) := by
  have hex (n : ℕ) := cellWeak_exists_raw_realization (Icc (-(n : ℝ)) n) u slice (hs n) (ha n)
  choose raw hweak htrace hjoint hjet hper using hex
  let D := fun t a => raw (cellLocalTimeIndex t) t a
  have hgood (n : ℕ) : ∀ᵐ t ∂volume,
      t ∈ Icc (-(n : ℝ)) n → HasPeriodicOrderedWeakJet (raw n t) ∧
        ∀ a, ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] raw n t a :=
    (ae_restrict_iff' measurableSet_Icc).mp ((hweak n).and (hjet n))
  have hall := ae_all_iff.mpr hgood
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hall] with t ht
    exact (ht (cellLocalTimeIndex t) (cellLocalTimeIndex_mem t)).1
  · intro t
    exact htrace (cellLocalTimeIndex t) t
  · intro a
    exact cellJoint_selected_aestronglyMeasurable volume cellLocalTimeIndex cellLocalTimeIndex_measurable
      (fun n => Icc (-(n : ℝ)) n) cellLocalTimeIndex_mem (fun n t x => raw n t a x)
      (fun n => (hjoint n a).aestronglyMeasurable)
  · filter_upwards [hall] with t ht
    exact (ht (cellLocalTimeIndex t) (cellLocalTimeIndex_mem t)).2
  · intro t a
    exact hper (cellLocalTimeIndex t) t a

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Componentwise summability budgets for the complete periodic cell Hilbert jet. -/

/-- The periodic Hilbert jet norm is bounded by the sum of its component L2 norms. -/
theorem cellTorusHk_enorm_le_components {K : ℕ} (u : TorusHk K ℂ) :
    ‖u‖ₑ ≤ ∑ a : JetIndex2 K, ‖u.val a‖ₑ := by
  exact cellFiniteArray_enorm_le_sum u.val

/-- A raw periodic witness supplies the same componentwise literal norm budget after promotion. -/
theorem cellPeriodicJet_enorm_le_cellL2Norm {K : ℕ} (u : TorusHkFunction K ℂ) :
    ‖u.toHk‖ₑ ≤ ∑ a : JetIndex2 K, cellL2Norm (u.jet a) := by
  have hb := cellTorusHk_enorm_le_components u.toHk
  have he (a : JetIndex2 K) : ‖u.toHk.val a‖ₑ = cellL2Norm (u.jet a) := by
    change ‖(u.hasPeriodicWeakJet.2.1 a).toLp (u.jet a)‖ₑ = _
    exact Lp.enorm_toLp _
  simpa only [he] using hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The bounded temporal coefficient map has the literal spatial multiplier representative. -/

theorem cellTimeCoefficientCLM_ae (I : Set ℝ) (b : ℝ → Vec 2 → ℂ)
    (hb : Measurable (Function.uncurry b)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t x, ‖b t x‖ ≤ B) (u : Lp ComplexCellL2 2 (volume.restrict I)) :
    cellTimeCoefficientCLM I b hb B hB hbound u =ᵐ[volume.restrict I]
      fun t => cellCoefficientComplexCLM (b t)
        ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        B hB (hbound t) (u t) :=
  (cellTimeCoefficient_memLp I b hb B hB hbound u (Lp.memLp u)).coeFn_toLp

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Mean-zero homogeneous cell solutions decay uniformly in the drift size. -/

/-- Zero scalar and flux sources define the zero forcing functional. -/
theorem cellSourceFunctional_zero (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) :
    cellSourceFunctional θ 0 (fun _ => 0) u = 0 := by
  simp only [cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, inner_zero_left, Finset.sum_const_zero, sub_zero]

/-- The actual homogeneous weak equation has squared-energy decay at rate 4π². -/
theorem cellWeakHomogeneous_meanZero_decay {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) 0 (fun _ => 0)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ Real.exp (-(4 * Real.pi ^ 2) * (t - a)) * ‖u a‖ ^ 2 := by
  apply (h.energy_strongTime hab).scalar_decay hab (4 * Real.pi ^ 2)
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  have hg := cellUnshiftedGenerator_meanZero_gap hG hv V hb t (slice t) hmean
  rw [cellDualDerivative_pairing, cellSourceFunctional_zero, add_zero, ht]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Exact raw cell norm squares of vector gradients and fluxes. -/

/-- The extended cell norm equals the Hilbert norm of any L² representative. -/
theorem cellL2Norm_eq_toLp {E : Type*} [NormedAddCommGroup E] (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm f = ENNReal.ofReal ‖hf.toLp f‖ := by
  change eLpNorm f 2 _ = _
  rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

/-- The real norm-square integral of a pointwise Hilbert array is the sum of its class norm squares. -/
theorem cellArray_normSq_integral (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (U : Fin 2 → ComplexCellL2)
    (he : ∀ j, (U j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => f x j) :
    (∫ x in AVenhance.unitCube, ‖f x‖ ^ 2) = ∑ j, ‖U j‖ ^ 2 := by
  have hi (j : Fin 2) := ((Lp.memLp (U j)).ae_eq (he j)).norm.integrable_sq
  have hn : (∫ x in AVenhance.unitCube, ‖f x‖ ^ 2) =
      ∫ x in AVenhance.unitCube, ∑ j : Fin 2, ‖f x j‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℂ) (f x)))
  rw [hn, integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_congr_ae ((he j).fun_comp (fun z => ‖z‖ ^ 2))).symm.trans (cellL2_norm_sq_integral _)

/-- The extended vector cell norm is precisely the sum of its coordinate class norm squares. -/
theorem cellArray_cellNormSq (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (U : Fin 2 → ComplexCellL2)
    (he : ∀ j, (U j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => f x j) :
    cellL2Norm f ^ 2 = ENNReal.ofReal (∑ j, ‖U j‖ ^ 2) := by
  rw [cellL2Norm_eq_toLp f hf, ← ENNReal.ofReal_pow (norm_nonneg _),
    AVRegularity.Sobolev.normSq_toLp_eq_integral hf, cellArray_normSq_integral f U he]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Construct the complete weak Galerkin data package from the actual premises. -/

/-- Actual measurable cell data produce a Galerkin sequence and weak subsequence package. -/
theorem cellGalerkin_actual_limit_data {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    Nonempty (CellGalerkinLimitData a b hab C hG V hv hvb src F u₀) := by
  classical
  have hc := fun N => cellGalerkin_actual_exists_bochner hab N C hG V k
    hv hvb hκ hκb src F hsrcm hFm hsrc hF u₀
  choose y hy he hi hb using hc
  let U : ℕ → CellBochnerH1 a b := fun N => (hy N).toLp (fun t => (extendCurve hab (y N) t).val)
  let W := (b - a + 2) *
    ((‖u₀‖ ^ 2 + ∫ s in a..b, ‖cellSourceSlice src s‖ ^ 2 +
      9 * ∑ j, ‖cellSourceSlice (fun t x => F t x j) s‖ ^ 2) *
      Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a)))
  have hnorm : ∀ N, ‖U N‖ ≤ W + 1 := by
    intro N
    exact cellNorm_le_budget_add_one (hb N)
  obtain ⟨limit, φ, hφ, hlim⟩ := cellHilbert_weak_subsequence_clm U (W + 1) hnorm
  exact ⟨{
    curve := y
    stateLp := hy
    variational := he
    initial_value := hi
    budget := W + 1
    norm_bound := hnorm
    limit := limit
    subsequence := φ
    monotone := hφ
    weak := hlim }⟩

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The exact algebraic metric-change identity underlying the cell resolvent. -/

/-- Changing a symmetric metric is exactly compensated by its gradient flux. -/
theorem cellLiteralRHS_metric_change
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (D : RawJet2 1 ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hG : ∀ x, (G t x).IsSymm) (hH : ∀ x, (H t x).IsSymm) :
    ∀ x, cellLiteralRHS ⟨H, v, 0, 0⟩ t (D (valueIndex2 1))
        (fun j => cellGradComp D j) ψ dψ src F x =
      cellLiteralRHS ⟨G, v, 0, 0⟩ t (D (valueIndex2 1))
        (fun j => cellGradComp D j) ψ dψ src
        (fun x => F x + cellMetricFlux (H - G) (fun _ => D) t x) x := by
  intro x
  have h01G := (hG x).apply 0 1
  have h01H := (hH x).apply 0 1
  simp only [cellLiteralRHS, cellMetricFlux, cellMetricFluxVector, cellGradient,
    cellGradComp, Fin.sum_univ_two, Pi.zero_apply, mul_zero, zero_mul, add_zero,
    sub_zero, Pi.sub_apply, Matrix.sub_apply, Complex.ofReal_sub,
    PiLp.add_apply]
  rw [h01G, h01H]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Recover the continuous Hilbert trace from the public raw trace predicate. -/

/-- Total L² trace classes of a raw cell trajectory. -/
def cellRawTrace (D : ℝ → AVRegularity.Sobolev.RawJet2 1 ℂ) : ℝ → ComplexCellL2 :=
  cellSourceSlice (cellValue D)

/-- At every prescribed L² trace, the total class represents the actual raw value. -/
theorem cellRawTrace_ae (D : ℝ → AVRegularity.Sobolev.RawJet2 1 ℂ) (t : ℝ)
    (ht : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube)) :
    (cellRawTrace D t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t :=
  cellSourceSlice_ae _ t ht

/-- The public extended-square continuity condition is exactly continuity of its Hilbert trace classes. -/
theorem cellRawTrace_continuous (I : Set ℝ) (D : ℝ → AVRegularity.Sobolev.RawJet2 1 ℂ)
    (hmem : ∀ t ∈ I, MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hcont : ∀ t₀ ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube,
      ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2) (𝓝[I] t₀) (𝓝 0)) :
    ContinuousOn (cellRawTrace D) I := by
  intro t₀ ht₀
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t₀ ht₀)
  have he : (fun t => (∫⁻ x in AVenhance.unitCube,
      ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2).toReal) =ᶠ[𝓝[I] t₀]
      fun t => ‖cellRawTrace D t - cellRawTrace D t₀‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [cellTrace_square_lintegral (fun x => cellValue D t x - cellValue D t₀ x)
      (cellRawTrace D t - cellRawTrace D t₀)
      ((Lp.coeFn_sub _ _).trans ((cellRawTrace_ae D t (hmem t ht)).sub
        (cellRawTrace_ae D t₀ (hmem t₀ ht₀)))), ← ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have hs : Tendsto (fun t => ‖cellRawTrace D t - cellRawTrace D t₀‖ ^ 2)
      (𝓝[I] t₀) (𝓝 0) := by simpa only [ENNReal.toReal_zero] using hr.congr' he
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual metric and drift entries as bounded complex-linear operators on temporal L2 cell classes. -/

def cellTimeMetricEntryCLM (I : Set ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G) (j k : Fin 2) :
    Lp ComplexCellL2 2 (volume.restrict I) →L[ℂ] Lp ComplexCellL2 2 (volume.restrict I) :=
  cellTimeCoefficientCLM I (fun t x => (G t x j k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (cellMetric_entry_measurable hG j k))
    2 (by norm_num) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k)

def cellTimeDriftEntryCLM (I : Set ℝ) (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (j : Fin 2) :
    Lp ComplexCellL2 2 (volume.restrict I) →L[ℂ] Lp ComplexCellL2 2 (volume.restrict I) :=
  cellTimeCoefficientCLM I (fun t x => (C.v t x j : ℂ))
    (Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply j).comp hv))
    |V| (abs_nonneg V) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j)

end AVRegularity.CycleEvolution
end
