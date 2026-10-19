-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellComplexH1Carrier
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleEvolution.CellSpatialEnergy
import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public noncomputable section

section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! The cell pairing has the expected complex scalar actions. -/

theorem cellComplexPair_scalar_left (c : ℂ) (u z : ComplexCellL2) :
    cellComplexPair (cellScalarCLM c u) z = c * cellComplexPair u z := by
  unfold cellComplexPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [cellScalarCLM_ae c u] with x hx
  rw [hx, mul_assoc]

theorem cellComplexPair_scalar_right (c : ℂ) (u z : ComplexCellL2) :
    cellComplexPair u (cellScalarCLM c z) = star c * cellComplexPair u z := by
  rw [cellComplexPair_symm u, cellComplexPair_scalar_left, star_mul,
    ← cellComplexPair_symm u z]
  exact mul_comm _ _

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Additivity of the actual scalar and divergence source pairing. -/

theorem cellComplexSource_add (θ : Fin 2 → ℂ) (S T : ComplexCellL2)
    (F H : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) :
    cellComplexSource θ (S + T) (F + H) z =
      cellComplexSource θ S F z + cellComplexSource θ T H z := by
  simp only [cellComplexSource, cellComplexPair_add_left, Fin.sum_univ_two, Pi.add_apply]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Real metric and drift multiplication commute with actual cell conjugation. -/

theorem cellMetricEntryCLM_conjugate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellMetricEntryCLM hG t j k u) := by
  apply Lp.ext
  filter_upwards [cellMetricEntryCLM_ae hG t j k
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u), cellFiberConj_ae u,
    cellFiberConj_ae (cellMetricEntryCLM hG t j k u), cellMetricEntryCLM_ae hG t j k u]
    with x hm hu hc hr
  rw [hm, hu, hc, hr, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem cellDriftEntryCLM_conjugate (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2) (u : ComplexCellL2) :
    cellDriftEntryCLM C V hv hb t j (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellDriftEntryCLM C V hv hb t j u) := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u), cellFiberConj_ae u,
    cellFiberConj_ae (cellDriftEntryCLM C V hv hb t j u), cellDriftEntryCLM_ae C V hv hb t j u]
    with x hm hu hc hr
  rw [hm, hu, hc, hr, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Bundled scalar multiplication and its adjoint on the periodic H1 Hilbert carrier. -/

def cellH1ScalarCLM (c : ℂ) : TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ :=
  mapTorusHkCLM 1 (ContinuousLinearMap.mul ℝ ℂ c)

theorem cellH1ScalarCLM_apply (c : ℂ) (z : TorusHk 1 ℂ) :
    cellH1ScalarCLM c z = cellH1Scalar c z := mapTorusHkCLM_apply 1 _ z

theorem cellH1ScalarCLM_adjoint (c : ℂ) :
    (cellH1ScalarCLM c).adjoint = cellH1ScalarCLM (star c) := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, cellH1ScalarCLM_apply, cellH1ScalarCLM_apply]
  calc
    _ = inner ℝ (cellH1Scalar c u) z := real_inner_comm _ _
    _ = inner ℝ u (cellH1Scalar (star c) z) := cellH1Scalar_inner c u z
    _ = _ := real_inner_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Public bilinear tests realize arbitrary real Hilbert H¹ tests. -/

/-- Applying conjugation twice returns the periodic H¹ graph element. -/
theorem cellH1Conj_involutive (z : TorusHk 1 ℂ) : cellH1Conj (cellH1Conj z) = z := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  filter_upwards [cellH1Conj_jet_ae (cellH1Conj z) a, cellH1Conj_jet_ae z a]
    with x hh hx
  rw [hh, hx, star_star]

/-- A conjugate raw test represents an arbitrary Hilbert test under the bilinear convention. -/
def cellHilbertTest (z : TorusHk 1 ℂ) : TorusHkFunction 1 ℂ := (cellH1Conj z).toFunction

/-- The test conversion is surjective onto the Hilbert H¹ test carrier. -/
theorem cellHilbertTest_inverse (z : TorusHk 1 ℂ) : cellRawTest (cellHilbertTest z) = z := by
  unfold cellRawTest cellHilbertTest
  rw [TorusHk.toFunction_toHk, cellH1Conj_involutive]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Energy control of differences of finite weak-time primitives. -/

/-- Differences of projected dual derivatives have a uniform H⁻¹ pairing bound. -/
theorem cellDualMoment_difference_energy_abs (N M : ℕ) (g : TorusHk 1 ℂ)
    (y : CellGalerkinSpace (E := ℂ) N) (z : CellGalerkinSpace (E := ℂ) M) :
    ‖2 * inner ℝ (cellGalerkinValue N y - cellGalerkinValue M z)
      (cellGalerkinValue N (cellGalerkinDualMomentCLM N g) -
        cellGalerkinValue M (cellGalerkinDualMomentCLM M g))‖ ≤
      4 * ‖g‖ * ‖y.val - z.val‖ := by
  have hJ : cellGalerkinValue N y - cellGalerkinValue M z = torusHkValueCLM (y.val - z.val) := by
    rw [map_sub]
    rfl
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    real_inner_comm, hJ, inner_sub_left, cellGalerkinDualMoment_pairing_all,
    cellGalerkinDualMoment_pairing_all]
  have h1 := abs_real_inner_le_norm g (galerkinProj N (y.val - z.val))
  have h2 := abs_real_inner_le_norm g (galerkinProj M (y.val - z.val))
  have hp1 := galerkinProj_norm_le N (y.val - z.val)
  have hp2 := galerkinProj_norm_le M (y.val - z.val)
  have hb := (abs_sub _ _).trans (add_le_add h1 h2)
  have hc := add_le_add
    (mul_le_mul_of_nonneg_left hp1 (norm_nonneg g))
    (mul_le_mul_of_nonneg_left hp2 (norm_nonneg g))
  nlinarith

/-- Finite primitive differences are controlled by the difference of Fourier state slices. -/
theorem CellWeakTimeData.primitive_difference_production {a b : ℝ} (hab : a ≤ b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) (N M : ℕ) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖2 * inner ℝ
        (cellGalerkinValue N (cellDualPrimitive N a initial g t) -
          cellGalerkinValue M (cellDualPrimitive M a initial g t))
        (cellGalerkinValue N (cellGalerkinDualMomentCLM N (g t)) -
          cellGalerkinValue M (cellGalerkinDualMomentCLM M (g t)))‖ ≤
        4 * ‖g t‖ * ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ := by
  filter_upwards [h.primitive_ae hab N, h.primitive_ae hab M] with t htN htM
  rw [htN, htM]
  exact cellDualMoment_difference_energy_abs N M (g t) _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The true product rule for real Hilbert pairings of two weak cell trajectories. -/

theorem CellWeakHilbertCurve.pairing_increment {a b : ℝ} (hab : a ≤ b)
    {u v : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (h' : CellWeakHilbertCurve a b v slice' g') :
    inner ℝ (u b) (v b) - inner ℝ (u a) (v a) =
      ∫ t in a..b, inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t) := by
  have h₁ := h.energy_increment hab
  have h₂ := h'.energy_increment hab
  have h₃ := (h.sub h').energy_increment hab
  have hi₁ := h.production_intervalIntegrable hab
  have hi₂ := h'.production_intervalIntegrable hab
  have hi₃ := cellH1Pair_intervalIntegrable hab h.dual h'.state
  have hi₄ := cellH1Pair_intervalIntegrable hab h'.dual h.state
  have hfun : (fun t => 2 * inner ℝ (g t - g' t) (slice t - slice' t)) =
      (fun t => (2 * inner ℝ (g t) (slice t) + 2 * inner ℝ (g' t) (slice' t)) -
        2 * (inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))) := by
    funext t
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hi : (∫ t in a..b,
      (2 * inner ℝ (g t) (slice t) + 2 * inner ℝ (g' t) (slice' t)) -
        2 * (inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))) =
      (∫ t in a..b, 2 * inner ℝ (g t) (slice t)) +
        (∫ t in a..b, 2 * inner ℝ (g' t) (slice' t)) -
          2 * ∫ t in a..b, inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t) := by
    rw [intervalIntegral.integral_sub (hi₁.add hi₂) ((hi₃.add hi₄).const_mul 2),
      intervalIntegral.integral_add hi₁ hi₂]
    rw [intervalIntegral.integral_const_mul
      (f := fun t => inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))]
  rw [norm_sub_sq_real, norm_sub_sq_real, hfun, hi] at h₃
  linarith

/-! Squared energy of a weak-time Hilbert cell solution is an absolutely continuous scalar. -/

/-- The weak H⁻¹ equation implies strong scalar time regularity of its squared L² energy. -/
theorem CellWeakHilbertCurve.energy_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    StrongTimeRegularity a b (fun t => ‖u t‖ ^ 2) (fun t => 2 * inner ℝ (g t) (slice t)) := by
  apply scalarStrongTime_of_primitive hab _ _ (h.production_intervalIntegrable hab)
  intro t ht
  have he := (h.mono (Icc_subset_Icc le_rfl ht.2)).energy_increment ht.1
  linarith

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Symmetry of the complex weak metric form, including arbitrary derivative vectors. -/

theorem cellMetricEntryCLM_transpose
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k u = cellMetricEntryCLM hG t k j u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [cellMetricEntryCLM_ae hG t j k u,
    cellMetricEntryCLM_ae hG t k j u] with x hj hk
  rw [hj, hk]
  have hs := congrFun (congrFun (hG.2.2.1 t x) j) k
  change G t x k j = G t x j k at hs
  rw [hs]

theorem cellComplexMetricForm_symm
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (u z : Fin 2 → ComplexCellL2) :
    (∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair (cellMetricEntryCLM hG t j k (u j)) (z k)) =
      star (∑ j : Fin 2, ∑ k : Fin 2,
        cellComplexPair (cellMetricEntryCLM hG t j k (z j)) (u k)) := by
  rw [star_sum]
  simp_rw [star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [cellMetricEntryCLM_complex_adjoint, cellComplexPair_symm (u k),
    cellMetricEntryCLM_transpose hG t k j]

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Adjoint of the complex zero-order potential in the cell equation. -/

theorem cellComplexPotential_adjoint (κ : ℂ) (u z : ComplexCellL2) :
    cellComplexPair (cellScalarCLM κ u) z =
      star (cellComplexPair (cellScalarCLM (star κ) z) u) := by
  rw [cellComplexPair_scalar_left, cellComplexPair_scalar_left, star_mul, star_star,
    ← cellComplexPair_symm u z]
  exact mul_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! A complete complex carrier for finite-time continuous L2 traces and L2 periodic H1 states. -/

abbrev CellCompactTime (a b : ℝ) := ↥(Icc a b)

instance cellCompactTime_measureSpace (a b : ℝ) : MeasureSpace (CellCompactTime a b) :=
  Measure.Subtype.measureSpace

instance cellCompactTime_finiteMeasure (a b : ℝ) :
    IsFiniteMeasure (volume : Measure (CellCompactTime a b)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

abbrev CellFiniteEnergyCarrier (a b : ℝ) :=
  CompatibleTraceLp (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM

instance cellFiniteEnergyCarrier_complete (a b : ℝ) :
    CompleteSpace (CellFiniteEnergyCarrier a b) := inferInstance

theorem cellFiniteEnergyCarrier_agrees (a b : ℝ) (u : CellFiniteEnergyCarrier a b) :
    ∀ᵐ t ∂(volume : Measure (CellCompactTime a b)),
      u.val.1 t = cellComplexH1ValueCLM (u.val.2 t) :=
  compatibleTraceLp_agrees _ _ u

/-! Measure preserving passage from a restricted time interval to its compact subtype. -/

theorem cellCompactTimeProjection_measurePreserving {a b : ℝ} (hab : a ≤ b) :
    MeasurePreserving (projIcc a b hab) (volume.restrict (Icc a b))
      (volume : Measure (CellCompactTime a b)) := by
  have hc : MeasurePreserving ((↑) : CellCompactTime a b → ℝ) volume
      (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  refine ⟨continuous_projIcc.measurable, ?_⟩
  rw [← hc.map_eq, Measure.map_map continuous_projIcc.measurable measurable_subtype_coe]
  have he : (projIcc a b hab ∘ ((↑) : CellCompactTime a b → ℝ)) = id := by
    funext t
    simp
  rw [he, Measure.map_id]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Explicit complex normed-space instance for the closed compatible energy graph. -/

instance cellFiniteEnergyCarrier_normedSpace (a b : ℝ) : NormedSpace ℂ (CellFiniteEnergyCarrier a b) :=
  Submodule.normedSpace
    (compatibleTraceLpSpace (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM)

instance cellFiniteEnergyCarrier_module (a b : ℝ) : Module ℂ (CellFiniteEnergyCarrier a b) :=
  (cellFiniteEnergyCarrier_normedSpace a b).toModule

instance cellFiniteEnergyCarrier_smulCommClass (a b : ℝ) :
    SMulCommClass ℂ ℂ (CellFiniteEnergyCarrier a b) where
  smul_comm c d u := by
    simp only [smul_smul, mul_comm]

instance cellFiniteEnergyCarrier_continuousConstSMul (a b : ℝ) :
    ContinuousConstSMul ℂ (CellFiniteEnergyCarrier a b) where
  continuous_const_smul c := (lipschitzWith_smul (β := CellFiniteEnergyCarrier a b) c).continuous

instance cellFiniteEnergyCarrier_isBoundedSMul (a b : ℝ) :
    IsBoundedSMul ℂ (CellFiniteEnergyCarrier a b) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℂ) (E := CellFiniteEnergyCarrier a b)

instance cellFiniteEnergyCarrier_continuousSMul (a b : ℝ) :
    ContinuousSMul ℂ (CellFiniteEnergyCarrier a b) :=
  IsBoundedSMul.continuousSMul (α := ℂ) (β := CellFiniteEnergyCarrier a b)

instance cellFiniteEnergyCarrier_isUniformAddGroup (a b : ℝ) :
    IsUniformAddGroup (CellFiniteEnergyCarrier a b) :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := CellFiniteEnergyCarrier a b)

instance cellFiniteEnergyCarrier_endNormedRing (a b : ℝ) :
    NormedRing (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℂ) (E := CellFiniteEnergyCarrier a b)

instance cellFiniteEnergyCarrier_endNormedAlgebra (a b : ℝ) :
    NormedAlgebra ℂ (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℂ) (E := CellFiniteEnergyCarrier a b)

instance cellFiniteEnergyCarrier_endNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b) :=
  (cellFiniteEnergyCarrier_endNormedAlgebra a b).toNormedSpace

instance cellFiniteEnergyCarrier_endCompleteSpace (a b : ℝ) :
    CompleteSpace (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (E := CellFiniteEnergyCarrier a b) (F := CellFiniteEnergyCarrier a b) (σ := RingHom.id ℂ)

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! A named complete complex operator algebra, avoiding repeated expansion of the compatible energy graph during inference. -/

def CellEnergyOperator (a b : ℝ) := CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b

instance cellEnergyOperator_normedRing (a b : ℝ) : NormedRing (CellEnergyOperator a b) :=
  cellFiniteEnergyCarrier_endNormedRing a b

instance cellEnergyOperator_normedAlgebra (a b : ℝ) : NormedAlgebra ℂ (CellEnergyOperator a b) :=
  cellFiniteEnergyCarrier_endNormedAlgebra a b

instance cellEnergyOperator_completeSpace (a b : ℝ) : CompleteSpace (CellEnergyOperator a b) :=
  cellFiniteEnergyCarrier_endCompleteSpace a b

end AVRegularity.CycleEvolution
end
