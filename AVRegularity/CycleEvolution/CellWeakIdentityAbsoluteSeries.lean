-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientWeightedForcing
import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

@[expose] public noncomputable section

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Finite degree prefixes exhaust the weighted coefficient series. -/

/-- A uniform finite-prefix bound controls the full weighted coefficient energy series. -/
theorem fibreCoefficient_weighted_total_le (ρ C : ℝ≥0∞) (E : ℕ × ℕ → ℝ≥0∞)
    (h : ∀ K, fibreCoefficientWeightedPrefix ρ E K ≤ C) :
    (∑' p, fibreCoefficientWeight ρ p * E p) ≤ C := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let K := ∑ p ∈ s, (p.1 + p.2)
  have hs : s ⊆ jetIndices K := by
    intro p hp
    apply (mem_jetIndices_iff K p).mpr
    exact Finset.single_le_sum (fun q _ => Nat.zero_le (q.1 + q.2)) hp
  exact (Finset.sum_le_sum_of_subset hs).trans (h K)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A single Bloch metric entry expanded after genuine periodic integration by parts. -/

theorem cellConstantMetric_bloch_entry {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (θ : Fin 2 → ℂ) (t : ℝ) (j k : Fin 2)
    (u z : TorusHk 1 ℂ) :
    cellComplexPair (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM θ j u))
      (cellShiftedDerivativeCLM (fun i => star (θ i)) k z) =
      (G t j k : ℂ) * cellComplexPair (cellDerivativeCLM j u) (cellDerivativeCLM k z) +
      Complex.I * (G t j k : ℂ) * θ j *
        cellComplexPair (torusHkValueCLM u) (cellDerivativeCLM k z) +
      Complex.I * (G t j k : ℂ) * θ k *
        cellComplexPair (torusHkValueCLM u) (cellDerivativeCLM j z) +
      (G t j k : ℂ) * θ j * θ k *
        cellComplexPair (torusHkValueCLM u) (torusHkValueCLM z) := by
  rw [cellConstantMetricEntryCLM, cellComplexPair_scalar_left]
  simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply,
    cellComplexPair_add_left, cellComplexPair_add_right, cellComplexPair_scalar_left,
    cellComplexPair_scalar_right, star_mul, star_star]
  rw [show star Complex.I = -Complex.I from Complex.conj_I,
    cellComplexDerivative_skew j u z]
  ring_nf
  rw [Complex.I_sq]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Construction of a continuous Hilbert trace from integrated weak time data. -/

/-- The finite dual primitive as a continuous L²-valued closed-interval curve. -/
def cellDualPrimitiveCurve {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (g : ℝ → TorusHk 1 ℂ) (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)) := by
  refine ⟨fun t => cellGalerkinValue N (cellDualPrimitive N a initial g t), ?_⟩
  have hc : ContinuousOn (fun t => cellGalerkinValue N (cellDualPrimitive N a initial g t))
      (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      ((cellDualPrimitive_strongTime hab N initial g hg).map (cellGalerkinValue N)).ac.continuousOn
  exact continuousOn_iff_continuous_domRestrict.mp hc

/-- A real scaled square bound gives the required pointwise metric estimate. -/
theorem cellScaled_square_bound {T x ε : ℝ} (hT : 0 < T) (hx : 0 ≤ x) (hε : 0 < ε)
    (h : T * x ^ 2 < T * ε ^ 2 / 4) : x ≤ ε / 2 := by
  have hh : x ^ 2 < ε ^ 2 / 4 := by nlinarith
  nlinarith

/-- Finite Fourier primitives of weak time data are Cauchy uniformly on the closed interval. -/
theorem CellWeakTimeData.primitive_curves_cauchy {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) :
    CauchySeq (fun N => cellDualPrimitiveCurve hab.le N initial g h.dual) := by
  let T := b - a
  let A := fun N => ∫ s in Icc a b, ‖galerkinProj N (slice s) - slice s‖ ^ 2
  let B := fun N => ∫ s in Icc a b, ‖g s‖ * ‖galerkinProj N (slice s) - slice s‖
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let β := fun N => 2 * J ^ 2 * A N + 4 * T * B N
  have hT : 0 < T := sub_pos.mpr hab
  obtain ⟨hA, hB⟩ := cellTime_fourier_tail_integrals h.state h.dual
  have hβ : Tendsto β atTop (𝓝 0) := by
    simpa only [β, A, B, zero_add, mul_zero] using
      (hA.const_mul (2 * J ^ 2)).add (hB.const_mul (4 * T))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < T * ε ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hβ.eventually (gt_mem_nhds hδ))
  refine ⟨K, fun N hN M hM => ?_⟩
  apply lt_of_le_of_lt ((ContinuousMap.dist_le (le_of_lt (half_pos hε))).mpr ?_) (half_lt_self hε)
  intro t
  rw [dist_eq_norm]
  apply cellScaled_square_bound hT (norm_nonneg _) hε
  have ht := h.primitive_difference_tail_bound hab.le N M t t.2
  have ht' : T * ‖cellGalerkinValue N (cellDualPrimitive N a initial g t) -
      cellGalerkinValue M (cellDualPrimitive M a initial g t)‖ ^ 2 ≤ β N + β M := by
    dsimp only [T, β, J, A, B]
    convert ht using 1; ring
  change T * ‖cellGalerkinValue N (cellDualPrimitive N a initial g t) -
    cellGalerkinValue M (cellDualPrimitive M a initial g t)‖ ^ 2 < T * ε ^ 2 / 4
  have hn := hK N hN
  have hm := hK M hM
  linarith

/-- Weak time data admit a uniform limit of their finite continuous Hilbert primitives. -/
theorem CellWeakTimeData.exists_primitive_limit {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) :
    ∃ U : C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)),
      Tendsto (fun N => cellDualPrimitiveCurve hab.le N initial g h.dual) atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete (h.primitive_curves_cauchy hab)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Jointly measurable L² representatives of arbitrary Bochner cell L² curves. -/

/-- Every Bochner L² curve of spatial L² classes has a joint L² realization.
No regularity of a chosen representative is assumed. -/
theorem cellBochner_exists_joint_realization (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) :
    ∃ f : ℝ → Vec 2 → ℂ,
      MemLp (Function.uncurry f) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) ∧
      ∀ᵐ t ∂volume.restrict I,
        (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f t := by
  let A := fun N => (cellJointFourier_memLp I N u hu).toLp
    (Function.uncurry (cellJointFourier N u))
  let B := fun N => ((cellVectorFourierProjection N).comp_memLp' hu).toLp
    (fun t => cellVectorFourierProjection N (u t))
  have hB := cellBochnerFourier_tendsto I u hu
  have hA : CauchySeq A := cellCauchy_of_distance_eq A B
    (cellJointFourier_distance I u hu) hB.cauchySeq
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete hA
  let f := fun t x => P (t, x)
  have hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := Lp.memLp P
  let Q := (cellSourceSlice_memLp I f hf).toLp (cellSourceSlice f)
  have hQ : Tendsto B atTop (𝓝 Q) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hd := (hP.dist (tendsto_const_nhds (x := P)))
    simpa only [dist_self, cellJointFourier_slice_distance I u hu, A, B, Q, f] using hd
  have he : hu.toLp u = Q := tendsto_nhds_unique hB hQ
  refine ⟨f, hf, ?_⟩
  filter_upwards [hu.coeFn_toLp, (cellSourceSlice_memLp I f hf).coeFn_toLp,
    cellSource_memLp_slices I f hf] with t hut hqt hft
  have hclass : u t = cellSourceSlice f t := by
    rw [← hut, he]
    exact hqt
  rw [hclass]
  exact cellSourceSlice_ae f t hft

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Differentiating the literal finite proper metric-jet flux in its uniformly local norm. -/

/-- Coefficient and lower-state directional quotients differentiate the actual proper source sum. -/
theorem cellMetricJetFlux_derivative_tendsto {P : Type*} (l : Filter P) (r : P → ℝ)
    (Gj : ℕ × ℕ → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (G0 : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → P → ℝ → RawJet2 1 ℂ)
    (c0 : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α ε : ℕ × ℕ)
    (hGj : ∀ β ∈ cellJetFluxIndices α, ∀ p,
      cellMetricSupNorm (Gj β p) < ⊤ ∧ Measurable (Function.uncurry (Gj β p)))
    (hG0 : ∀ β ∈ cellJetFluxIndices α,
      cellMetricSupNorm (G0 β) < ⊤ ∧ Measurable (Function.uncurry (G0 β)))
    (hG1 : ∀ β ∈ cellJetFluxIndices α,
      cellMetricSupNorm (G0 (β + ε)) < ⊤ ∧ Measurable (Function.uncurry (G0 (β + ε))))
    (hc0 : ∀ β ∈ cellJetFluxIndices α,
      cellEnergyNorm univ (c0 (α.1 - β.1, α.2 - β.2)) < ⊤)
    (hcjm : ∀ β ∈ cellJetFluxIndices α, ∀ p a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc0m : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => c0 (α.1 - β.1, α.2 - β.2) z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc1m : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => c0 ((α.1 - β.1, α.2 - β.2) + ε) z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGd : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun p => cellMetricSupNorm (r p • (Gj β p - G0 β) - G0 (β + ε))) l (𝓝 0))
    (hcc : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun p => cellEnergyNorm univ
        (cj (α.1 - β.1, α.2 - β.2) p - c0 (α.1 - β.1, α.2 - β.2))) l (𝓝 0))
    (hcd : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun p => cellEnergyNorm univ
        (r p • (cj (α.1 - β.1, α.2 - β.2) p - c0 (α.1 - β.1, α.2 - β.2)) -
          c0 ((α.1 - β.1, α.2 - β.2) + ε))) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (r p • (cellMetricJetFlux (fun β => Gj β p) (fun β => cj β p) α -
        cellMetricJetFlux G0 c0 α) - cellMetricJetFluxDerivative G0 c0 α ε)) l (𝓝 0) := by
  simp_rw [cellMetricJetFlux_eq_sum]
  exact cellMetricFlux_finset_productRule_tendsto l r (cellJetFluxIndices α)
    (fun β => (cellJetChoose α β : ℝ)) Gj G0 (fun β => G0 (β + ε))
    (fun β => cj (α.1 - β.1, α.2 - β.2))
    (fun β => c0 (α.1 - β.1, α.2 - β.2))
    (fun β => c0 ((α.1 - β.1, α.2 - β.2) + ε))
    hGj hG0 hG1 hc0 hcjm hc0m hc1m hGd hcc hcd

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Uniformly local data have genuine spatial L² classes at almost every time. -/

/-- Finite uniformly local norms imply almost-everywhere spatial L² membership on all time. -/
theorem cellUl_memLp_slices_ae {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : ℝ → Vec 2 → E)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) :
    ∀ᵐ t ∂volume, MemLp (f t) 2 (volume.restrict AVenhance.unitCube) := by
  let A : ℕ → Set ℝ := fun n => Icc (-(n : ℝ)) n
  have hc : (⋃ n, A n) = univ := by
    apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr ⟨cellLocalTimeIndex t, cellLocalTimeIndex_mem t⟩
  have ha : ∀ n, ∀ᵐ t ∂volume.restrict (A n),
      MemLp (f t) 2 (volume.restrict AVenhance.unitCube) := by
    intro n
    exact cellSource_memLp_slices (A n) f
      (cellUl_memLp_product_interval_ae univ f hm hf (-(n : ℝ)) n (subset_univ _))
  have hh := (ae_restrict_iUnion_iff A
    (fun t => MemLp (f t) 2 (volume.restrict AVenhance.unitCube))).mpr ha
  rwa [hc, Measure.restrict_univ] at hh

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! An explicit positive radius for the quadratic coefficient energy majorant. -/

/-- A radius depending only on the scaled drift bound. -/
def fibreCoefficientMajorantRadius (Cw : ℝ) : ℝ := 1 / (104 * (Cw + 8))

/-- The coefficient majorant radius is positive for every nonnegative drift bound. -/
theorem fibreCoefficientMajorantRadius_pos {Cw : ℝ} (hCw : 0 ≤ Cw) :
    0 < fibreCoefficientMajorantRadius Cw := by
  unfold fibreCoefficientMajorantRadius
  positivity

/-- The explicit radius makes the quadratic recurrence preserve the unit bound. -/
theorem fibreCoefficientMajorantRadius_small {Cw : ℝ} (hCw : 0 ≤ Cw) :
    (26 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) *
      (3 * ENNReal.ofReal Cw + 8) ≤ 1 := by
  have hρ := (fibreCoefficientMajorantRadius_pos hCw).le
  have hr : (26 * fibreCoefficientMajorantRadius Cw) * (3 * Cw + 8) ≤ 1 := by
    unfold fibreCoefficientMajorantRadius
    have hd : 0 < 104 * (Cw + 8) := by positivity
    field_simp
    nlinarith
  have hc : (3 : ℝ) * Cw ≥ 0 := by positivity
  have he : (26 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) *
      (3 * ENNReal.ofReal Cw + 8) =
      ENNReal.ofReal ((26 * fibreCoefficientMajorantRadius Cw) * (3 * Cw + 8)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 26 * fibreCoefficientMajorantRadius Cw),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 26),
      ENNReal.ofReal_add hc (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [he]
  exact (ENNReal.ofReal_le_ofReal hr).trans_eq (by norm_num)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Identify the constructed continuous trace and its arbitrary L² initial value. -/

/-- The uniform primitive limit has the prescribed arbitrary L² initial trace. -/
theorem CellWeakTimeData.primitive_limit_initial {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial)
    (U : C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)))
    (hU : Tendsto (fun N => cellDualPrimitiveCurve hab.le N initial g h.dual) atTop (𝓝 U)) :
    U ⟨a, ⟨le_rfl, hab.le⟩⟩ = initial := by
  let ta : Icc a b := ⟨a, ⟨le_rfl, hab.le⟩⟩
  have he := ((ContinuousMap.evalCLM (R := ℝ) ta).continuous.tendsto U).comp hU
  have hh : (fun N => (cellDualPrimitiveCurve hab.le N initial g h.dual) ta) =
      fun N => cellGalerkinValue N (cellGalerkinL2Initial N initial) := by
    funext N
    change cellGalerkinValue N (cellDualPrimitive N a initial g a) = _
    simp only [cellDualPrimitive, intervalIntegral.integral_same, add_zero]
  change Tendsto (fun N => (cellDualPrimitiveCurve hab.le N initial g h.dual) ta)
    atTop (𝓝 (U ta)) at he
  rw [hh] at he
  exact tendsto_nhds_unique he (cellGalerkinL2Initial_tendsto initial)

/-- The continuous primitive limit represents the Bochner H¹ state almost everywhere. -/
theorem CellWeakTimeData.primitive_limit_agrees {a b : ℝ} (hab : a < b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial)
    (U : C(Icc a b, Lp ℂ 2 (volume.restrict AVenhance.unitCube)))
    (hU : Tendsto (fun N => cellDualPrimitiveCurve hab.le N initial g h.dual) atTop (𝓝 U)) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ ht : t ∈ Icc a b,
      U ⟨t, ht⟩ = torusHkValueCLM (slice t) := by
  have ha := ae_all_iff.mpr (fun N => h.primitive_ae hab.le N)
  filter_upwards [ha] with t ht
  intro hti
  have he := ((ContinuousMap.evalCLM (R := ℝ) (⟨t, hti⟩ : Icc a b)).continuous.tendsto U).comp hU
  change Tendsto (fun N => cellGalerkinValue N (cellDualPrimitive N a initial g t))
    atTop (𝓝 (U ⟨t, hti⟩)) at he
  have hl : Tendsto (fun N => cellGalerkinValue N (cellGalerkinInitial N (slice t)))
      atTop (𝓝 (torusHkValueCLM (slice t))) := by
    simp_rw [← cellGalerkinL2Initial_of_H1]
    exact cellGalerkinL2Initial_tendsto _
  have hh : (fun N => cellGalerkinValue N (cellDualPrimitive N a initial g t)) =
      fun N => cellGalerkinValue N (cellGalerkinInitial N (slice t)) := by
    funext N
    rw [ht N]
  rw [hh] at he
  exact tendsto_nhds_unique he hl

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Elementary real bounds for the explicit coefficient radius. -/

/-- The explicit coefficient radius is at most one for every nonnegative drift bound. -/
theorem fibreCoefficientMajorantRadius_le_one {Cw : ℝ} (hCw : 0 ≤ Cw) :
    fibreCoefficientMajorantRadius Cw ≤ 1 := by
  unfold fibreCoefficientMajorantRadius
  have hd : 0 < 104 * (Cw + 8) := by positivity
  apply (div_le_iff₀ hd).mpr
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Arbitrary Bochner L2 source classes have jointly measurable raw representatives with the exact Hilbert slices. -/

theorem cellBochner_exists_measurable_realization (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) :
    ∃ f : ℝ → Vec 2 → ℂ,
      Measurable (Function.uncurry f) ∧
      MemLp (Function.uncurry f) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) ∧
      ∀ᵐ t ∂volume.restrict I, cellSourceSlice f t = u t := by
  obtain ⟨g, hg, he⟩ := cellBochner_exists_joint_realization I u hu
  let a := hg.aestronglyMeasurable.mk (Function.uncurry g)
  let f := fun t x => a (t, x)
  have hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
    hg.ae_eq hg.aestronglyMeasurable.ae_eq_mk
  refine ⟨f, hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable, hf, ?_⟩
  filter_upwards [he, Measure.ae_ae_of_ae_prod hg.aestronglyMeasurable.ae_eq_mk] with t ht hx
  exact cellSourceSlice_eq_of_ae f t (u t) (ht.trans hx)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The adjoint Bloch generator is the genuine opposite-drift cell generator. -/

theorem cellComplexShiftedDriftForm_neg {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexShiftedDriftForm (fun t x => -v t x) V (cellDrift_neg hv)
      (cellDrift_neg_bound hb) θ t u z = -cellComplexShiftedDriftForm v V hv hb θ t u z := by
  rw [cellComplexShiftedDriftForm_eq_sum, cellComplexShiftedDriftForm_eq_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [cellDriftEntryCLM_neg hv V hb, cellComplexPair_neg_left]

def cellAdjointCoefficients (C : CellCoefficients) : CellCoefficients :=
  ⟨C.G, (fun t x => -C.v t x), (fun j => star (C.θ j)), (fun t => star (C.κ t))⟩

theorem cellComplexGenerator_opposite_drift (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator C hG V hv.1 hb t u z =
      star (cellComplexGenerator (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t z u) := by
  rw [cellComplexGenerator_adjoint C hG V hv hb t u z,
    cellComplexGenerator_decomposition (cellAdjointCoefficients C) hG V
      (cellDrift_neg hv) (cellDrift_neg_bound hb) t z u]
  dsimp only [cellAdjointCoefficients]
  rw [cellComplexShiftedDriftForm_neg hv V hb, sub_neg_eq_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Actual finite cell approximations with uniform temporal H¹ class bounds. -/

/-- The actual Galerkin constructor has a temporal H¹ class bound independent of cutoff. -/
theorem cellGalerkin_actual_exists_bochner {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    let B := cellGeneratorB C hG V hv hvb
    let q := cellRawSourceFunctional C.θ src F
    let A := fun t => cellGalerkinOperator N (B t)
    let f := fun t => cellGalerkinForcing N (q t)
    ∃ y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N),
      ∃ hy : MemLp (fun t => (extendCurve hab y t).val) 2 (volume.restrict (Icc a b)),
      StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
        (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
        (fun t => cellGalerkinValue N (extendCurve hab y t))
        (fun t => cellGalerkinValue N (linearRhs A f (extendCurve hab y) t))
        (extendCurve hab y) ∧
      cellGalerkinValue N (extendCurve hab y a) = cellGalerkinValue N (cellGalerkinL2Initial N u₀) ∧
      ‖hy.toLp (fun t => (extendCurve hab y t).val)‖ ^ 2 ≤
        (b - a + 2) *
          ((‖u₀‖ ^ 2 + ∫ s in a..b, ‖cellSourceSlice src s‖ ^ 2 +
            9 * ∑ j, ‖cellSourceSlice (fun t x => F t x j) s‖ ^ 2) *
            Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))) := by
  dsimp only
  obtain ⟨y, hy, hdy, hstate, hinit⟩ := cellGalerkin_actual_exists_timeH1 hab N C hG V k
    hv hvb hκ hκb src F hsrcm hFm hsrc hF u₀
  have hsp := cellSource_memLp_product (Icc a b) src hsrcm hsrc
  have hfp := cellSource_memLp_product (Icc a b) F hFm hF
  have hsj := cellSourceSlice_memLp (Icc a b) src hsp
  have hfj (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun t x => F t x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp)
  have henergy := cellFinite_bochner_norm_bound hab N C hG V k hv hvb hκb
    (cellSourceSlice src) (fun t j => cellSourceSlice (fun t x => F t x j) t)
    hsj hfj _ _ _ hstate hy
  refine ⟨y, hstate, hy, hinit, henergy.trans ?_⟩
  have hn := cellGalerkinL2Initial_norm_le N u₀
  have hn2 : ‖cellGalerkinValue N (extendCurve hab y a)‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    rw [hinit]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hn
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact mul_le_mul_of_nonneg_right (add_le_add hn2 le_rfl) (Real.exp_nonneg _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open AVenhance.Infra.Torus AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Periodization preserves cell representatives and their joint measurability. -/

/-- The physical unit cube is measurable. -/
theorem cellCube_measurable : MeasurableSet AVenhance.unitCube := by
  simpa [AVenhance.unitCube, Set.pi] using
    (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
      (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))

/-- Periodic extension of arbitrary raw cell data. -/
def cellPeriodize (f : Vec 2 → ℂ) : Vec 2 → ℂ := fromUnitTorus (periodicToTorus f)

/-- Periodization agrees pointwise with the original data in the open unit cube. -/
theorem cellPeriodize_eq_of_mem (f : Vec 2 → ℂ) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    cellPeriodize f x = f x := by
  change f (unitTorusRepresentative 2 (toUnitTorus 2 x)) = f x
  rw [unitTorusRepresentative_eq_of_mem_unitCell]
  intro i
  have hi : 0 < x i ∧ x i < 1 := hx i (Set.mem_univ i)
  simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)

/-- Periodization preserves the cell class. -/
theorem cellPeriodize_ae (f : Vec 2 → ℂ) :
    cellPeriodize f =ᵐ[volume.restrict AVenhance.unitCube] f := by
  filter_upwards [ae_restrict_mem cellCube_measurable] with x hx
  exact cellPeriodize_eq_of_mem f x hx

/-- The extension is literally periodic, without assumptions on the chosen raw data. -/
theorem cellPeriodize_periodic (f : Vec 2 → ℂ) : AVenhance.IsZ2Periodic (cellPeriodize f) :=
  (isZdPeriodic_iff_frozen _).mp (isZdPeriodic_fromUnitTorus _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniform operator bounds for temporal fixed-test integrals. -/

/-- Convert an integral square budget into a norm estimate without square roots. -/
theorem cellSquare_time_bound {T x y : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 ≤ T * y ^ 2) : x ≤ (T + 1) * y := by
  have hc : T ≤ (T + 1) ^ 2 := by nlinarith [sq_nonneg T]
  have hs := h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg y))
  rw [← mul_pow] at hs
  exact (sq_le_sq₀ hx (mul_nonneg (by linarith) hy)).mp hs

/-- A bounded time test defines a uniformly bounded integral functional. -/
theorem cellTimeTestIntegralCLM_norm_le {a b : ℝ} (hab : a ≤ b) (s t : ℝ)
    (w : ℝ → TorusHk 1 ℂ) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ r, ‖w r‖ ≤ K) :
    ‖cellTimeTestIntegralCLM a b s t w hw‖ ≤ (b - a + 1) * K := by
  let wi := (Ioc s t).indicator w
  have hwi := cellTime_memLp_indicator (Ioc s t) measurableSet_Ioc w hw
  have hbound (r : ℝ) : ‖wi r‖ ≤ K := by
    by_cases hr : r ∈ Ioc s t
    · simpa only [wi, indicator_of_mem hr] using hb r
    · simpa only [wi, indicator_of_notMem hr, norm_zero] using hK
  have hnorm := cellTimeL2_norm_sq_integral wi hwi
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hnorm
  have hi : (∫ r in a..b, ‖wi r‖ ^ 2) ≤ (b - a) * K ^ 2 := by
    have hm := intervalIntegral.integral_mono_on hab
      (cellTime_normSq_intervalIntegrable hab hwi) (continuous_const.intervalIntegrable a b)
      (fun r _ => (sq_le_sq₀ (norm_nonneg _) hK).mpr (hbound r))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  change ‖innerSL ℝ (hwi.toLp wi)‖ ≤ _
  rw [innerSL_apply_norm]
  exact cellSquare_time_bound (sub_nonneg.mpr hab) (norm_nonneg _) hK (hnorm.le.trans hi)

/-- Actual fixed-test generator integrals have an operator bound linear in the test norm. -/
theorem cellGeneratorIntegralCLM_uniform_norm_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ r x, ∑ i, C.v r x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t z,
      ‖cellGeneratorIntegralCLM a b s t C hG V k hv hb hκ hκb z‖ ≤ L * ‖z‖ := by
  obtain ⟨M, hM, hMb⟩ := cellGeneratorForm_uniform_norm_bound C hG V k hv hb hκb
  refine ⟨(b - a + 1) * M, mul_nonneg (by linarith) hM, fun s t z => ?_⟩
  have hi := cellTimeTestIntegralCLM_norm_le hab s t
    (fun r => cellGeneratorTest C hG V hv hb r z)
    (cellGeneratorTest_memLp a b C hG V k hv hb hκ hκb z) (M * ‖z‖)
    (mul_nonneg hM (norm_nonneg _))
    (fun r => cellGeneratorTest_norm_le_of_bound C hG V hv hb M hM hMb r z)
  simpa only [cellGeneratorIntegralCLM, mul_assoc] using hi

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The complex product rule for two genuine weak Hilbert cell trajectories. -/

theorem CellWeakHilbertCurve.complex_pairing_increment {a b : ℝ} (hab : a ≤ b)
    {u v : ℝ → ComplexCellL2} {slice g slice' g' : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (h' : CellWeakHilbertCurve a b v slice' g') :
    cellComplexPair (u b) (v b) - cellComplexPair (u a) (v a) =
      ∫ t in a..b, cellDualComplexPair (g t) (slice' t) +
        star (cellDualComplexPair (g' t) (slice t)) := by
  have hi₁ := cellDualComplexPair_cross_intervalIntegrable hab h.dual h'.state
  have hi₂ := cellDualComplexPair_cross_intervalIntegrable hab h'.dual h.state
  have hi₂star : IntervalIntegrable (fun t => star (cellDualComplexPair (g' t) (slice t)))
      volume a b := intervalIntegrable_iff.mpr
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp (intervalIntegrable_iff.mp hi₂))
  have hi := hi₁.add hi₂star
  have hre := h.pairing_increment hab h'
  have him := h.pairing_increment hab (h'.complex_smul Complex.I)
  have hskew (z w : TorusHk 1 ℂ) : inner ℝ (cellH1Scalar Complex.I z) w =
      -inner ℝ z (cellH1Scalar Complex.I w) := by
    rw [cellH1Scalar_inner, Complex.star_def, Complex.conj_I, cellH1Scalar_neg, inner_neg_right]
  simp only [hskew] at him
  apply Complex.ext
  · have he := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t in a..b,
      (cellDualComplexPair (g t) (slice' t) + star (cellDualComplexPair (g' t) (slice t))).re) =
      (∫ t in a..b, cellDualComplexPair (g t) (slice' t) +
        star (cellDualComplexPair (g' t) (slice t))).re at he
    rw [Complex.sub_re, cellComplexPair_re, cellComplexPair_re, ← he]
    simpa only [Complex.add_re, Complex.star_def, Complex.conj_re, cellDualComplexPair_re] using hre
  · have he := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t in a..b,
      (cellDualComplexPair (g t) (slice' t) + star (cellDualComplexPair (g' t) (slice t))).im) =
      (∫ t in a..b, cellDualComplexPair (g t) (slice' t) +
        star (cellDualComplexPair (g' t) (slice t))).im at he
    rw [Complex.sub_im, cellComplexPair_im, cellComplexPair_im, ← he]
    simpa only [Complex.add_im, Complex.star_def, Complex.conj_im, cellDualComplexPair_im,
      cellComplexPair_im, sub_eq_add_neg] using him

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Total weighted forcing bounds from the normalized state coefficient majorant. -/

/-- Normalized total state energy bounds the total linear and quadratic coefficient forcing. -/
theorem fibreCoefficient_weighted_forcing_total_le (ρ B : ℝ≥0∞)
    (E U : ℕ × ℕ → ℝ≥0∞) (hzero : U 0 = 0)
    (hE : (∑' p, fibreCoefficientWeight ρ p * E p) ≤ 1)
    (hU : ∀ p, U p ≤
      ((∑ j ∈ fibreCoefficientDirections p, B *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), B *
          E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j)))) :
    (∑' p, fibreCoefficientWeight ρ p * U p) ≤ (2 * ρ) * (3 * B + 8) := by
  have hp K : fibreCoefficientWeightedPrefix ρ E K ≤ 1 :=
    (ENNReal.sum_le_tsum (jetIndices K)).trans hE
  apply fibreCoefficient_weighted_total_le
  intro K
  cases K with
  | zero => rw [fibreCoefficientWeightedPrefix_zero ρ U hzero]; exact zero_le
  | succ K =>
    apply (fibreCoefficient_weighted_forcing_prefix_le ρ B E U hU K).trans
    calc
      _ ≤ (2 * ρ) * (B + (B + 8) * 1 + B * 1 ^ 2) :=
        mul_le_mul' le_rfl (add_le_add
          (add_le_add le_rfl (mul_le_mul' le_rfl (hp K)))
          (mul_le_mul' le_rfl (pow_le_pow_left' (hp K) 2)))
      _ = _ := by ring

/-! A finite-prefix absorption bound for triangular reciprocal coefficient majorants. -/

theorem fibreScalarInverse_prefix_recurrence (ρ : ℝ≥0∞) (D K : ℕ × ℕ → ℝ≥0∞)
    (hK : ∀ p, K p ≤ (if p = 0 then 1 else 0) +
      ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a)) (N : ℕ) :
    fibreCoefficientWeightedPrefix ρ K N ≤
      1 + fibreCoefficientWeightedPrefix ρ D N * fibreCoefficientWeightedPrefix ρ K N := by
  classical
  have hzero : (0 : ℕ × ℕ) ∈ jetIndices N := (mem_jetIndices_iff N 0).mpr (by simp)
  have hc : (∑ p ∈ jetIndices N,
      fibreCoefficientWeight ρ p * (if p = 0 then 1 else 0)) = 1 := by
    simp [hzero, fibreCoefficientWeight]
  have hconv : (∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p *
      ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a)) ≤
        fibreCoefficientWeightedPrefix ρ D N * fibreCoefficientWeightedPrefix ρ K N := by
    exact fibreCoefficient_weighted_convolution_prefix_le ρ D K N
  calc
    _ ≤ ∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p *
        ((if p = 0 then 1 else 0) +
          ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a)) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul' le_rfl (hK p))
    _ = 1 + ∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p *
        ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a) := by
      simp only [mul_add, Finset.sum_add_distrib, hc]
    _ ≤ _ := add_le_add le_rfl hconv

theorem fibreScalarInverse_prefix_le_two (ρ : ℝ≥0∞) (D K : ℕ × ℕ → ℝ≥0∞)
    (hK : ∀ p, K p ≤ (if p = 0 then 1 else 0) +
      ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a))
    (hD : (∑' p, fibreCoefficientWeight ρ p * D p) ≤ 1 / 2)
    (hfinite : ∀ p, K p < ⊤) (hρ : ρ < ⊤) (N : ℕ) :
    fibreCoefficientWeightedPrefix ρ K N ≤ 2 := by
  have hf : fibreCoefficientWeightedPrefix ρ K N < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro p _
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hρ) (hfinite p)
  have hd : fibreCoefficientWeightedPrefix ρ D N ≤ 1 / 2 :=
    (ENNReal.sum_le_tsum (jetIndices N)).trans hD
  have he := (fibreScalarInverse_prefix_recurrence ρ D K hK N).trans
    (add_le_add le_rfl (mul_le_mul' hd le_rfl))
  simpa only [mul_one] using ennreal_half_absorption _ 1 hf he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The complete actual weak derivative under a Bloch perturbation equals the baseline equation with explicit sources. -/

theorem cellDualDerivative_blochPerturbation (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative { C with θ := C.θ + δ, κ := fun s => C.κ s + q s }
      hG V hv hb t u S F = cellDualDerivative C hG V hv hb t u
      (cellBlochPerturbationScalar C hG V hv hb δ q t u +
        (S + ∑ j : Fin 2, cellScalarCLM (Complex.I * δ j) (F j)))
      (cellBlochPerturbationFlux C hG δ t u + F) := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair
      (cellDualDerivative { C with θ := C.θ + δ, κ := fun s => C.κ s + q s }
        hG V hv hb t u S F) z =
      cellDualComplexPair (cellDualDerivative C hG V hv hb t u
        (cellBlochPerturbationScalar C hG V hv hb δ q t u +
          (S + ∑ j : Fin 2, cellScalarCLM (Complex.I * δ j) (F j)))
        (cellBlochPerturbationFlux C hG δ t u + F)) z := by
    rw [cellDualComplexPair_actual, cellDualComplexPair_actual,
      cellComplexGenerator_blochPerturbation, cellComplexSource_add]
    change cellComplexGenerator C hG V hv hb t u z +
      cellComplexSource C.θ (cellBlochPerturbationScalar C hG V hv hb δ q t u)
        (cellBlochPerturbationFlux C hG δ t u) z + cellComplexSource (C.θ + δ) S F z = _
    rw [cellComplexSource_add_shift]
    ring
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Trace and H1 integral estimates control the complete energy carrier norm. -/

theorem cellFiniteEnergyCarrier_norm_sq_le {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val)
    (W H : ℝ) (hW : 0 ≤ W)
    (ht : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ W)
    (hs : (∫ t in a..b, ‖slice t‖ ^ 2) ≤ H) :
    ‖z‖ ^ 2 ≤ max W H := by
  let : InnerProductSpace ℝ CellComplexH1 := InnerProductSpace.complexToReal
  have htrace : ‖z.val.1‖ ≤ Real.sqrt W := by
    apply (ContinuousMap.norm_le z.val.1 (Real.sqrt_nonneg W)).mpr
    intro t
    rw [hz t]
    exact (Real.le_sqrt (norm_nonneg _) hW).mpr (ht t.val t.property)
  have hstate : ‖z.val.2‖ ^ 2 ≤ H := by
    rw [cellLpL2_norm_sq_integral]
    have he := cellFiniteEnergyCarrier_state_eq u slice g h z hz
    have he' : (fun t : CellCompactTime a b => ‖z.val.2 t‖ ^ 2) =ᵐ[volume]
        (fun t => ‖slice t.val‖ ^ 2) := by
      filter_upwards [he] with t ht'
      rw [← ht', cellComplexH1RealEquiv.norm_map]
    rw [integral_congr_ae he']
    change (∫ t : ↥(Icc a b), ‖slice t.val‖ ^ 2 ∂Measure.comap Subtype.val volume) ≤ H
    rw [integral_subtype_comap (μ := volume) measurableSet_Icc (fun t : ℝ => ‖slice t‖ ^ 2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact hs
  have htrace' : ‖z.val.1‖ ^ 2 ≤ W := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) htrace 2
    rwa [Real.sq_sqrt hW] at hh
  change (max ‖z.val.1‖ ‖z.val.2‖) ^ 2 ≤ max W H
  rcases le_total ‖z.val.1‖ ‖z.val.2‖ with he | he
  · rw [max_eq_right he]
    exact hstate.trans (le_max_right W H)
  · rw [max_eq_left he]
    exact htrace'.trans (le_max_left W H)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Continuous dependence of the integrated generator functional on its H¹ test. -/

/-- The integrated generator formula also applies to the canonical temporal class representative. -/
theorem cellGeneratorIntegralCLM_apply_class {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ r x, ∑ i, C.v r x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k) (z : TorusHk 1 ℂ)
    (U : CellBochnerH1 a b) :
    cellGeneratorIntegralCLM a b s t C hG V k hv hb hκ hκb z U =
      ∫ r in s..t, cellGeneratorForm C hG V hv hb r (U r) z := by
  simpa only [Lp.toLp_coeFn] using
    cellGeneratorIntegralCLM_apply hs ht hst C hG V k hv hb hκ hκb z U (Lp.memLp U)

/-- Actual generator entries against a Bochner H¹ state are integrable on subintervals. -/
theorem cellGenerator_pairing_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ r x, ∑ i, C.v r x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k) (z : TorusHk 1 ℂ)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun r => cellGeneratorForm C hG V hv hb r (u r) z) volume s t := by
  simpa only [cellGeneratorTest_pairing] using cellTime_inner_intervalIntegrable hs ht hst
    u (fun r => cellGeneratorTest C hG V hv hb r z) hu
    (cellGeneratorTest_memLp a b C hG V k hv hb hκ hκb z)

/-- The integrated generator is linear in its fixed H¹ test. -/
def cellGeneratorIntegralTestLinearMap {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ r x, ∑ i, C.v r x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k) :
    TorusHk 1 ℂ →ₗ[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) where
  toFun z := cellGeneratorIntegralCLM a b s t C hG V k hv hb hκ hκb z
  map_add' z w := by
    ext U
    simp only [add_apply, cellGeneratorIntegralCLM_apply_class hs ht hst]
    have he : (fun r => cellGeneratorForm C hG V hv hb r (U r) (z + w)) =
        fun r => cellGeneratorForm C hG V hv hb r (U r) z + cellGeneratorForm C hG V hv hb r (U r) w := by
      funext r
      exact (cellGeneratorForm C hG V hv hb r (U r)).map_add z w
    rw [he]
    exact intervalIntegral.integral_add
      (cellGenerator_pairing_intervalIntegrable hs ht hst C hG V k hv hb hκ hκb z U (Lp.memLp U))
      (cellGenerator_pairing_intervalIntegrable hs ht hst C hG V k hv hb hκ hκb w U (Lp.memLp U))
  map_smul' r z := by
    ext U
    simp only [smul_apply, cellGeneratorIntegralCLM_apply_class hs ht hst]
    simp_rw [map_smul, smul_eq_mul]
    exact intervalIntegral.integral_const_mul r _

/-- Continuous dependence on the fixed test in the temporal dual norm. -/
def cellGeneratorIntegralTestCLM {a b s t : ℝ} (hab : a ≤ b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ r x, ∑ i, C.v r x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k) :
    TorusHk 1 ℂ →L[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) :=
  by
    let h := cellGeneratorIntegralCLM_uniform_norm_bound hab C hG V k hv hb hκ hκb
    let L : TorusHk 1 ℂ →ₗ[ℝ] (CellBochnerH1 a b →L[ℝ] ℝ) :=
      cellGeneratorIntegralTestLinearMap hs ht hst C hG V k hv hb hκ hκb
    refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := TorusHk 1 ℂ)
      (F := CellBochnerH1 a b →L[ℝ] ℝ) (σ := RingHom.id ℝ) L h.choose ?_
    intro z
    change ‖cellGeneratorIntegralCLM a b s t C hG V k hv hb hκ hκb z‖ ≤ h.choose * ‖z‖
    exact h.choose_spec.2 s t z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Joint L² realizations of all coordinates of a Bochner H¹ jet. -/

/-- Continuous coordinate projection of the periodic H¹ graph. -/
def cellJetCoordinateCLM (a : JetIndex2 1) : TorusHk 1 ℂ →L[ℝ] ComplexCellL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 1 => ComplexCellL2) a).comp
    (torusHkGraph (E := ℂ) 1).toSubmodule.subtypeL

/-- Each jet component admits a joint L² representative, with simultaneous slice agreement. -/
theorem cellBochner_exists_joint_jet (I : Set ℝ) (slice : ℝ → TorusHk 1 ℂ)
    (hs : MemLp slice 2 (volume.restrict I)) :
    ∃ f : JetIndex2 1 → ℝ → Vec 2 → ℂ,
      (∀ a, MemLp (Function.uncurry (f a)) 2
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) ∧
      ∀ᵐ t ∂volume.restrict I, ∀ a,
        ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f a t := by
  have hex (a : JetIndex2 1) := cellBochner_exists_joint_realization I
    (fun t => cellJetCoordinateCLM a (slice t)) ((cellJetCoordinateCLM a).comp_memLp' hs)
  choose f hf he using hex
  exact ⟨f, hf, ae_all_iff.mpr he⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Absolute local L1 summability of the zero-frequency weak cell integrands. -/

/-- Actual bounded coefficients and product L2 summability justify absolute weak-integrand summation. -/
theorem cellLiteralZeroRHS_series_L1 {J : Type*} [Countable J]
    (a b : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hvb : ∀ t x, ∑ k, v t x k ^ 2 ≤ V ^ 2)
    (ψ : TorusHkFunction 1 ℂ) (u src : J → ℝ → Vec 2 → ℂ)
    (du : J → ℝ → Fin 2 → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hdu : ∀ k, (∑' n, eLpNorm (fun p : ℝ × Vec 2 => du n p.1 k p.2) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤)
    (hsrc : (∑' n, eLpNorm (Function.uncurry (src n)) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤)
    (hF : ∀ k, (∑' n, eLpNorm (fun p : ℝ × Vec 2 => F n p.1 p.2 k) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤) :
    (∑' n, eLpNorm (fun p : ℝ × Vec 2 => cellLiteralRHS ⟨G, v, 0, 0⟩ p.1
      (u n p.1) (du n p.1) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩) (src n p.1) (F n p.1) p.2) 1
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
  let μ := (volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)
  let dg := fun (j k : Fin 2) (n : J) (p : ℝ × Vec 2) =>
    du n p.1 j p.2 * ((G p.1 p.2 j k : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩ p.2)
  let adv := fun (k : Fin 2) (n : J) (p : ℝ × Vec 2) =>
    du n p.1 k p.2 * ((v p.1 p.2 k : ℂ) * ψ.jet (valueIndex2 1) p.2)
  let sf := fun (n : J) (p : ℝ × Vec 2) => src n p.1 p.2 * ψ.jet (valueIndex2 1) p.2
  let ff := fun (k : Fin 2) (n : J) (p : ℝ × Vec 2) =>
    F n p.1 p.2 k * ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩ p.2
  have hdm (k : Fin 2) (n : J) : MemLp (fun p : ℝ × Vec 2 => du n p.1 k p.2) 2 μ :=
    (ENNReal.le_tsum n).trans_lt (hdu k)
  have hsm (n : J) : MemLp (Function.uncurry (src n)) 2 μ :=
    (ENNReal.le_tsum n).trans_lt hsrc
  have hfm (k : Fin 2) (n : J) : MemLp (fun p : ℝ × Vec 2 => F n p.1 p.2 k) 2 μ :=
    (ENNReal.le_tsum n).trans_lt (hF k)
  have hdg j k : (∑' n, eLpNorm (dg j k n) 1 μ) < ⊤ :=
    cellL2_product_series_eLpNorm_one_lt_top μ _ _
      (fun n => (hdm j n).aestronglyMeasurable)
      (cellTest_metric_product_memLp (Set.Icc a b) G hG ψ _ j k) (hdu j)
  have hadv k : (∑' n, eLpNorm (adv k n) 1 μ) < ⊤ :=
    cellL2_product_series_eLpNorm_one_lt_top μ _ _
      (fun n => (hdm k n).aestronglyMeasurable)
      (cellTest_drift_product_memLp (Set.Icc a b) v hvm V hvb ψ _ k) (hdu k)
  have hsf : (∑' n, eLpNorm (sf n) 1 μ) < ⊤ :=
    cellL2_product_series_eLpNorm_one_lt_top μ _ _
      (fun n => (hsm n).aestronglyMeasurable)
      (cellTest_component_product_memLp (Set.Icc a b) ψ _) hsrc
  have hff k : (∑' n, eLpNorm (ff k n) 1 μ) < ⊤ :=
    cellL2_product_series_eLpNorm_one_lt_top μ _ _
      (fun n => (hfm k n).aestronglyMeasurable)
      (cellTest_component_product_memLp (Set.Icc a b) ψ _) (hF k)
  let diffusion := fun n => ∑ j : Fin 2, ∑ k : Fin 2, dg j k n
  let advection := fun n => ∑ k : Fin 2, adv k n
  let flux := fun n => ∑ k : Fin 2, ff k n
  have hd : (∑' n, eLpNorm (diffusion n) 1 μ) < ⊤ :=
    cellL1Series_finset_sum_lt_top μ Finset.univ _ (fun j _ =>
      cellL1Series_finset_sum_lt_top μ Finset.univ (dg j) (fun k _ => hdg j k))
  have ha : (∑' n, eLpNorm (advection n) 1 μ) < ⊤ :=
    cellL1Series_finset_sum_lt_top μ Finset.univ adv (fun k _ => hadv k)
  have hfl : (∑' n, eLpNorm (flux n) 1 μ) < ⊤ :=
    cellL1Series_finset_sum_lt_top μ Finset.univ ff (fun k _ => hff k)
  have hb := cellL1Series_add_lt_top μ
    (fun n => (-diffusion n + -advection n) + sf n) (fun n => -flux n)
    (cellL1Series_add_lt_top μ _ sf
      (cellL1Series_add_lt_top μ _ _ (cellL1Series_neg_lt_top μ diffusion hd)
        (cellL1Series_neg_lt_top μ advection ha)) hsf)
    (cellL1Series_neg_lt_top μ flux hfl)
  have he n : (fun p : ℝ × Vec 2 => cellLiteralRHS ⟨G, v, 0, 0⟩ p.1
      (u n p.1) (du n p.1) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩) (src n p.1) (F n p.1) p.2) =
      (-diffusion n + -advection n) + sf n + -flux n := by
    funext p
    simp [cellLiteralRHS, diffusion, advection, flux, dg, adv, sf, ff, Fin.sum_univ_two]
    ring
  simp_rw [he]
  exact hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute summation of actual cell weak identities through the product-space integrands. -/

/-- Conditional series calculus: absolute integrand summability passes the actual weak identity to its literal sum. -/
theorem cellWeakIdentity_series_of_absolute_rhs {J : Type*} [Countable J]
    (C : CellCoefficients) (s t : ℝ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u₀ u₁ : J → Vec 2 → ℂ) (u src : J → ℝ → Vec 2 → ℂ)
    (du : J → ℝ → Fin 2 → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (U Src : ℝ → Vec 2 → ℂ) (DU : ℝ → Fin 2 → Vec 2 → ℂ)
    (Flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube))
    (h₀ : (∑' j, cellL2Norm (u₀ j)) < ⊤) (h₁ : (∑' j, cellL2Norm (u₁ j)) < ⊤)
    (hweak : ∀ j, CellWeakIdentity C s t (u₀ j) (u₁ j) ψ dψ (u j) (du j) (src j) (F j))
    (hR : (∑' j, eLpNorm (fun p : ℝ × Vec 2 =>
      cellLiteralRHS C p.1 (u j p.1) (du j p.1) ψ dψ (src j p.1) (F j p.1) p.2) 1
      ((volume.restrict (Set.Ioc s t)).prod (volume.restrict AVenhance.unitCube))) < ⊤)
    (he : (fun p : ℝ × Vec 2 => cellLiteralRHS C p.1 (U p.1) (DU p.1) ψ dψ (Src p.1) (Flux p.1) p.2) =ᵐ[
      (volume.restrict (Set.Ioc s t)).prod (volume.restrict AVenhance.unitCube)]
      (fun p => ∑' j, cellLiteralRHS C p.1 (u j p.1) (du j p.1) ψ dψ (src j p.1) (F j p.1) p.2)) :
    CellWeakIdentity C s t (fun x => ∑' j, u₀ j x) (fun x => ∑' j, u₁ j x)
      ψ dψ U DU Src Flux := by
  let μ := volume.restrict AVenhance.unitCube
  let ν := volume.restrict (Set.Ioc s t)
  let R := fun (j : J) (p : ℝ × Vec 2) =>
    cellLiteralRHS C p.1 (u j p.1) (du j p.1) ψ dψ (src j p.1) (F j p.1) p.2
  let S := fun p : ℝ × Vec 2 => cellLiteralRHS C p.1 (U p.1) (DU p.1) ψ dψ (Src p.1) (Flux p.1) p.2
  have hm₀ j : MemLp (u₀ j) 2 μ := (ENNReal.le_tsum j).trans_lt h₀
  have hm₁ j : MemLp (u₁ j) 2 μ := (ENNReal.le_tsum j).trans_lt h₁
  have hpair₀ := cellL2_product_series_eLpNorm_one_lt_top μ u₀ ψ
    (fun j => (hm₀ j).aestronglyMeasurable) hψ h₀
  have hpair₁ := cellL2_product_series_eLpNorm_one_lt_top μ u₁ ψ
    (fun j => (hm₁ j).aestronglyMeasurable) hψ h₁
  have hA₀ := cellL1Series_integrals_summable μ (fun j x => u₀ j x * ψ x) hpair₀
  have hA₁ := cellL1Series_integrals_summable μ (fun j x => u₁ j x * ψ x) hpair₁
  have hRj j : Integrable (R j) (ν.prod μ) :=
    memLp_one_iff_integrable.mp (show MemLp (R j) 1 (ν.prod μ) from (ENNReal.le_tsum j).trans_lt hR)
  have hS : Integrable S (ν.prod μ) :=
    (cellL1Series_integrable (ν.prod μ) R hR).congr he.symm
  change Integrable (fun x => (∑' j, u₁ j x) * ψ x) μ ∧
    Integrable (fun x => (∑' j, u₀ j x) * ψ x) μ ∧
    (∀ᵐ r ∂ν, Integrable (fun x => S (r, x)) μ) ∧
    Integrable (fun r => ∫ x, S (r, x) ∂μ) ν ∧
    (∫ x, (∑' j, u₁ j x) * ψ x ∂μ) - (∫ x, (∑' j, u₀ j x) * ψ x ∂μ) =
      ∫ r, ∫ x, S (r, x) ∂μ ∂ν
  refine ⟨memLp_one_iff_integrable.mp ((cellL2Series_memLp_bound u₁ h₁).1.mul hψ),
    memLp_one_iff_integrable.mp ((cellL2Series_memLp_bound u₀ h₀).1.mul hψ),
    hS.prod_right_ae, hS.integral_prod_left, ?_⟩
  calc
    _ = (∑' j, ∫ x, u₁ j x * ψ x ∂μ) - ∑' j, ∫ x, u₀ j x * ψ x ∂μ := by
      rw [cellL2_product_series_integral μ u₁ ψ (fun j => (hm₁ j).aestronglyMeasurable) hψ h₁,
        cellL2_product_series_integral μ u₀ ψ (fun j => (hm₀ j).aestronglyMeasurable) hψ h₀]
    _ = ∑' j, ((∫ x, u₁ j x * ψ x ∂μ) - ∫ x, u₀ j x * ψ x ∂μ) := (hA₁.tsum_sub hA₀).symm
    _ = ∑' j, ∫ r, ∫ x, R j (r, x) ∂μ ∂ν :=
      tsum_congr (fun j => (hweak j).2.2.2.2)
    _ = ∑' j, ∫ p, R j p ∂ν.prod μ :=
      tsum_congr (fun j => (integral_prod _ (hRj j)).symm)
    _ = ∫ p, ∑' j, R j p ∂ν.prod μ := (cellL1Series_integral_tsum (ν.prod μ) R hR).symm
    _ = ∫ p, S p ∂ν.prod μ := (integral_congr_ae he).symm
    _ = _ := integral_prod _ hS

end AVRegularity.CycleEvolution
end
