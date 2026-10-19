-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellMeanProjection
public import AVRegularity.CycleEvolution.CellDriftComplexMultiplier
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
import Mathlib.Algebra.Order.Star.Real

section
section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Constant fibre actions commute with Hilbert adjoints and the value map of periodic H1 states. -/

def cellFiberCLM (L : ℂ →L[ℝ] ℂ) : ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  L.compLpL 2 (volume.restrict AVenhance.unitCube)

theorem cellFiberCLM_inner (L : ℂ →L[ℝ] ℂ) (u z : ComplexCellL2) :
    inner ℝ (cellFiberCLM L u) z = inner ℝ u (cellFiberCLM L.adjoint z) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L u,
    ContinuousLinearMap.coeFn_compLpL L.adjoint z] with x hu hz
  dsimp only [cellFiberCLM]
  rw [hu, hz]
  exact (ContinuousLinearMap.adjoint_inner_right L (u x) (z x)).symm

theorem cellFiberCLM_adjoint (L : ℂ →L[ℝ] ℂ) :
    (cellFiberCLM L).adjoint = cellFiberCLM L.adjoint := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = inner ℝ (cellFiberCLM L u) z := real_inner_comm _ _
    _ = inner ℝ u (cellFiberCLM L.adjoint z) := cellFiberCLM_inner L u z
    _ = _ := real_inner_comm _ _

theorem cellFiberCLM_value (L : ℂ →L[ℝ] ℂ) (z : TorusHk 1 ℂ) :
    cellFiberCLM L (torusHkValueCLM z) = torusHkValueCLM (mapTorusHkCLM 1 L z) := by
  rw [mapTorusHkCLM_apply]
  exact (mapTorusHk_jet_eq_compLp L z (valueIndex2 1)).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Almost measurable source projection without assuming global time integrability. -/

/-- The cell mean of a jointly almost strongly measurable source is almost strongly measurable in time. -/
theorem cellMean_aestronglyMeasurable {I : Set ℝ} {f : ℝ → Vec 2 → ℂ}
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (fun t => cellMean (f t)) (volume.restrict I) :=
  hf.integral_prod_right'

/-- The literal mean-free projection preserves joint almost strong measurability. -/
theorem cellQ0_aestronglyMeasurable {I : Set ℝ} {f : ℝ → Vec 2 → ℂ}
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellQ0 (f p.1) p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  hf.sub ((cellMean_aestronglyMeasurable hf).comp_fst)

/-- The time-dependent mean multiplier of a jointly almost measurable source is jointly almost measurable. -/
theorem cellMean_product_aestronglyMeasurable {I : Set ℝ} {f g : ℝ → Vec 2 → ℂ}
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => g p.1 p.2 * cellMean (f p.1))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  hg.mul ((cellMean_aestronglyMeasurable hf).comp_fst)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Literal pairing normalization for two mean-zero cell L2 corrections. -/

local instance cellMeanGraphProductProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem cellMean_one_add_mul_one_add (f g : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hmf : cellMean f = 0) (hmg : cellMean g = 0) :
    cellMean (fun x => (1 + f x) * (1 + g x)) =
      1 + cellMean (fun x => f x * g x) := by
  have hfi := hf.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  have hfg : Integrable (fun x => f x * g x) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp (hf.mul hg)
  have hc : Integrable (fun _ : Vec 2 => (1 : ℂ)) (volume.restrict AVenhance.unitCube) :=
    integrable_const _
  have he : (fun x => (1 + f x) * (1 + g x)) =
      (fun x => ((1 + f x) + g x) + f x * g x) := by
    funext x
    ring
  have hi : (∫ x in AVenhance.unitCube, ((1 + f x) + g x) + f x * g x) =
      (∫ x in AVenhance.unitCube, (1 + f x) + g x) +
        ∫ x in AVenhance.unitCube, f x * g x := integral_add ((hc.add hfi).add hgi) hfg
  have hi' : (∫ x in AVenhance.unitCube, (1 + f x) + g x) =
      (∫ x in AVenhance.unitCube, 1 + f x) + ∫ x in AVenhance.unitCube, g x :=
    integral_add (hc.add hfi) hgi
  have hi'' : (∫ x in AVenhance.unitCube, 1 + f x) =
      (∫ x in AVenhance.unitCube, (1 : ℂ)) + ∫ x in AVenhance.unitCube, f x :=
    integral_add hc hfi
  unfold cellMean
  rw [he, hi, hi', hi'', integral_const, Measure.real_def,
    Measure.restrict_apply_univ, cellCube_volume_one]
  simp only [ENNReal.toReal_one, one_smul]
  change ((1 + cellMean f) + cellMean g) + cellMean (fun x => f x * g x) = _
  rw [hmf, hmg]
  simp only [add_zero]
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Continuous L² mean and mean-free operators on the actual cell Hilbert space. -/

local instance cellMeanOperatorProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Averaging is the complex L² pairing with the constant one. -/
def cellMeanCLM : ComplexCellL2 →L[ℝ] ℂ :=
  (innerSL ℂ (cellConstantCLM 1)).restrictScalars ℝ

/-- The mean operator equals the literal cell integral. -/
theorem cellMeanCLM_apply (u : ComplexCellL2) : cellMeanCLM u = cellMean u := by
  change inner ℂ (cellConstantCLM 1) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellConstantCLM_ae 1] with x hx
  simp only [hx, RCLike.inner_apply, map_one, mul_one]

/-- Constant embedding preserves the complex modulus on the unit cell. -/
theorem cellConstantCLM_norm (c : ℂ) : ‖cellConstantCLM c‖ = ‖c‖ := by
  change ‖Lp.const 2 (volume.restrict AVenhance.unitCube) c‖ = _
  rw [Lp.norm_const' 2 _ c (by norm_num) (by norm_num)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, Real.one_rpow, mul_one]

/-- Averaging has L² operator norm at most one. -/
theorem cellMeanCLM_norm_le (u : ComplexCellL2) : ‖cellMeanCLM u‖ ≤ ‖u‖ := by
  change ‖inner ℂ (cellConstantCLM 1) u‖ ≤ _
  simpa only [cellConstantCLM_norm, norm_one, one_mul] using
    norm_inner_le_norm (cellConstantCLM 1) u

/-- The mean-free projection as a bounded real-linear L² operator. -/
def cellQ0CLM : ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  ContinuousLinearMap.id ℝ ComplexCellL2 - cellConstantCLM.comp cellMeanCLM

/-- The projection has its literal mean-subtracted representative. -/
theorem cellQ0CLM_ae (u : ComplexCellL2) : cellQ0CLM u =ᵐ[volume.restrict AVenhance.unitCube]
    cellQ0 u := by
  filter_upwards [Lp.coeFn_sub u (cellConstantCLM (cellMeanCLM u)),
    cellConstantCLM_ae (cellMeanCLM u)] with x hs hc
  change (u - cellConstantCLM (cellMeanCLM u)) x = _
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hc, cellMeanCLM_apply]
  rfl

/-- A uniform operator bound suffices for the cell inverse source estimates. -/
theorem cellQ0CLM_norm_le (u : ComplexCellL2) : ‖cellQ0CLM u‖ ≤ 2 * ‖u‖ := by
  change ‖u - cellConstantCLM (cellMeanCLM u)‖ ≤ _
  calc
    _ ≤ ‖u‖ + ‖cellConstantCLM (cellMeanCLM u)‖ := norm_sub_le _ _
    _ = ‖u‖ + ‖cellMeanCLM u‖ := by rw [cellConstantCLM_norm]
    _ ≤ ‖u‖ + ‖u‖ := by have := cellMeanCLM_norm_le u; linarith
    _ = 2 * ‖u‖ := by ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Linearity of the literal mean-free projection on genuine spatial L² data. -/

local instance cellQ0LinearProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- On L² slices the literal mean-free projection commutes with subtraction. -/
theorem cellQ0_sub (f g : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) :
    cellQ0 (f - g) = cellQ0 f - cellQ0 g := by
  have hm : cellMean (f - g) = cellMean f - cellMean g :=
    integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
  funext x
  simp only [cellQ0, Pi.sub_apply, hm]
  ring

/-- Real scaling commutes with the mean-free projection, including exceptional slices. -/
theorem cellQ0_smul (r : ℝ) (f : Vec 2 → ℂ) :
    cellQ0 (r • f) = r • cellQ0 f := by
  have hm : cellMean (r • f) = r • cellMean f := by
    change (∫ x in AVenhance.unitCube, r • f x) = _
    rw [integral_smul]
    rfl
  funext x
  simp only [cellQ0, hm, Pi.smul_apply, smul_sub]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Bloch covariant gradients of actual jointly L² raw jets are jointly L². -/

theorem cellRawCovGradient_memLp (I : Set ℝ) (θ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => cellCovGradient θ (D p.1) p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply cellFiniteArray_memLp
  intro j
  have hd := hD ⟨⟨1, by decide⟩, fun _ => j⟩
  have hv := (hD (valueIndex2 1)).const_smul (Complex.I * θ j)
  exact (hd.add hv).ae_eq (Filter.Eventually.of_forall (fun p => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cellGradComp]))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Weak-time cell energy identity by finite Fourier projection.
The argument permits spatial H¹ only almost everywhere. -/

/-- The weak-time cell curve satisfies the exact energy identity. No strong L² time
 derivative or energy-identity premise is required for the full curve. -/
theorem CellWeakHilbertCurve.energy_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 = ∫ t in a..b, 2 * inner ℝ (g t) (slice t) := by
  let μ := volume.restrict (Icc a b)
  have hm : Integrable (fun t => ‖g t‖ * ‖slice t‖) μ :=
    memLp_one_iff_integrable.mp (h.dual.norm.mul h.state.norm : MemLp _ 1 μ)
  have hbound : IntegrableOn (fun t => 2 * (‖g t‖ * ‖slice t‖)) (Ioc a b) :=
    (hm.const_mul 2).mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have ha : ∀ᵐ t ∂volume.restrict (Ioc a b), u t = torusHkValueCLM (slice t) :=
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  apply energy_increment_of_dominated_approximation hab
    (fun N t => cellGalerkinValue N (cellGalerkinL2Initial N (u t)))
    (fun N t => cellGalerkinValue N (cellGalerkinDualMomentCLM N (g t)))
    (fun N => (h.projected_strongTime hab N).map (cellGalerkinValue N))
    (u a) (u b) (cellGalerkinL2Initial_tendsto (u a)) (cellGalerkinL2Initial_tendsto (u b))
    (fun t => 2 * inner ℝ (g t) (slice t)) (fun t => 2 * (‖g t‖ * ‖slice t‖)) hbound
  · intro N
    filter_upwards [ha] with t hat
    rw [real_inner_comm, cellGalerkinDualMomentCLM_pairing, hat, cellGalerkinL2Initial_of_H1]
    change ‖2 * inner ℝ (g t) (galerkinProj N (slice t))‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (galerkinProj_norm_le N (slice t)) (norm_nonneg _))
  · filter_upwards [ha] with t hat
    have hp : Tendsto (fun N => 2 * inner ℝ (g t) (galerkinProj N (slice t))) atTop
        (𝓝 (2 * inner ℝ (g t) (slice t))) :=
      (tendsto_const_nhds.inner (galerkinProj_tendsto (slice t))).const_mul 2
    apply hp.congr'
    filter_upwards with N
    have he : inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N (u t)))
        (cellGalerkinValue N (cellGalerkinDualMomentCLM N (g t))) =
        inner ℝ (g t) (galerkinProj N (slice t)) := by
      rw [real_inner_comm, cellGalerkinDualMomentCLM_pairing, hat, cellGalerkinL2Initial_of_H1]
      rfl
    rw [he]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Integrated weak time data before construction of a continuous L² representative. -/

/-- Bochner state and dual derivative with the integrated fixed-test equation.
No continuous Hilbert trace is part of this predicate. -/
structure CellWeakTimeData (a b : ℝ) (slice g : ℝ → TorusHk 1 ℂ)
    (initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) : Prop where
  state : MemLp slice 2 (volume.restrict (Icc a b))
  dual : MemLp g 2 (volume.restrict (Icc a b))
  moment : ∀ z : TorusHk 1 ℂ, ∀ᵐ t ∂volume.restrict (Icc a b),
    inner ℝ (torusHkValueCLM (slice t)) (torusHkValueCLM z) =
      inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t, inner ℝ (g r) z

/-- Finite coefficient primitives of weak time data. -/
def cellDualPrimitive (N : ℕ) (a : ℝ)
    (initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (g : ℝ → TorusHk 1 ℂ) (t : ℝ) : CellGalerkinSpace (E := ℂ) N :=
  cellGalerkinL2Initial N initial + ∫ r in a..t, cellGalerkinDualMomentCLM N (g r)

/-- Finite dual primitives have genuine strong time derivatives. -/
theorem cellDualPrimitive_strongTime {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (g : ℝ → TorusHk 1 ℂ) (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    StrongTimeRegularity a b (cellDualPrimitive N a initial g)
      (fun t => cellGalerkinDualMomentCLM N (g t)) := by
  have hy : IsLinearIntegralSolution
      (fun _ => (0 : CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N))
      (fun t => cellGalerkinDualMomentCLM N (g t))
      (cellGalerkinL2Initial N initial) a b (cellDualPrimitive N a initial g) := by
    intro t _
    change cellGalerkinL2Initial N initial + (∫ r in a..t, cellGalerkinDualMomentCLM N (g r)) =
      cellGalerkinL2Initial N initial + ∫ r in a..t, 0 + cellGalerkinDualMomentCLM N (g r)
    simp only [zero_add]
  have he : linearRhs (fun _ => (0 : CellGalerkinSpace (E := ℂ) N →L[ℝ]
      CellGalerkinSpace (E := ℂ) N)) (fun t => cellGalerkinDualMomentCLM N (g t))
      (cellDualPrimitive N a initial g) = (fun t => cellGalerkinDualMomentCLM N (g t)) := by
    funext t
    change 0 + cellGalerkinDualMomentCLM N (g t) = _
    exact zero_add _
  have hint : IntervalIntegrable
      (linearRhs (fun _ => 0) (fun t => cellGalerkinDualMomentCLM N (g t))
        (cellDualPrimitive N a initial g)) volume a b := by
    rw [he]
    exact cellWeakDualMoment_intervalIntegrable hab N g hg
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  have hd := hy.ae_hasDerivAt hab hint
  filter_upwards [hd] with t ht
  simpa only [uIcc_of_le hab, he] using ht

/-- Fixed-test moments identify every finite primitive with the projected Bochner state. -/
theorem CellWeakTimeData.primitive_ae {a b : ℝ} (hab : a ≤ b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) (N : ℕ) :
    cellDualPrimitive N a initial g =ᵐ[volume.restrict (Icc a b)]
      fun t => cellGalerkinInitial N (slice t) := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  have hm := ae_all_iff.mpr (fun i => h.moment (basis i).val)
  filter_upwards [hm, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hti.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hti.2
  have hint := (cellWeakDualMoment_intervalIntegrable hab N g h.dual).mono_set hsub
  apply cellGalerkinMass_injective N
  apply basis.ext
  intro i
  change inner ℝ (cellGalerkinValue N (cellDualPrimitive N a initial g t))
      (cellGalerkinValue N (basis i)) =
    inner ℝ (cellGalerkinValue N (cellGalerkinInitial N (slice t)))
      (cellGalerkinValue N (basis i))
  rw [← cellGalerkinL2Initial_of_H1, cellGalerkinL2Initial_pairing]
  unfold cellDualPrimitive
  rw [map_add, inner_add_left, cellGalerkinL2Initial_pairing]
  let L := (innerSL ℝ (cellGalerkinValue N (basis i))).comp (cellGalerkinValue N)
  have he : inner ℝ (cellGalerkinValue N (∫ r in a..t, cellGalerkinDualMomentCLM N (g r)))
      (cellGalerkinValue N (basis i)) = ∫ r in a..t, inner ℝ (g r) (basis i).val := by
    calc
      _ = L (∫ r in a..t, cellGalerkinDualMomentCLM N (g r)) := real_inner_comm _ _
      _ = ∫ r in a..t, L (cellGalerkinDualMomentCLM N (g r)) :=
        (L.intervalIntegral_comp_comm hint).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r _
        exact (real_inner_comm _ _).trans (cellGalerkinDualMomentCLM_pairing N (g r) (basis i))
  rw [he]
  exact (ht i).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Bounded measurable coefficient multiplication commutes with complex scalar multiplication on the actual L² carrier. -/

theorem cellCoefficientCLM_complex_scalar (b : Vec 2 → ℂ)
    (hb : AEStronglyMeasurable b (volume.restrict AVenhance.unitCube))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖b x‖ ≤ B)
    (c : ℂ) (u : ComplexCellL2) :
    cellCoefficientCLM b hb B hB hbound (cellScalarCLM c u) =
      cellScalarCLM c (cellCoefficientCLM b hb B hB hbound u) := by
  apply Lp.ext
  filter_upwards [cellCoefficientCLM_ae b hb B hB hbound (cellScalarCLM c u),
    cellScalarCLM_ae c u, cellScalarCLM_ae c (cellCoefficientCLM b hb B hB hbound u),
    cellCoefficientCLM_ae b hb B hB hbound u] with x hl hu hr hb'
  rw [hl, hu, hr, hb']
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Additivity of the complex cell pairing on its two real Hilbert arguments. -/

theorem cellComplexPair_add_left (u v z : ComplexCellL2) :
    cellComplexPair (u + v) z = cellComplexPair u z + cellComplexPair v z := by
  apply Complex.ext
  · simp only [Complex.add_re, cellComplexPair_re, inner_add_left]
  · simp only [Complex.add_im, cellComplexPair_im, inner_add_left]

theorem cellComplexPair_add_right (u v z : ComplexCellL2) :
    cellComplexPair u (v + z) = cellComplexPair u v + cellComplexPair u z := by
  apply Complex.ext
  · simp only [Complex.add_re, cellComplexPair_re, inner_add_right]
  · simp only [Complex.add_im, cellComplexPair_im, map_add, inner_add_right]

/-! Negation on either argument of the complex cell pairing. -/

theorem cellComplexPair_neg_left (u z : ComplexCellL2) :
    cellComplexPair (-u) z = -cellComplexPair u z := by
  apply Complex.ext
  · simp only [Complex.neg_re, cellComplexPair_re, inner_neg_left]
  · simp only [Complex.neg_im, cellComplexPair_im, inner_neg_left]

theorem cellComplexPair_neg_right (u z : ComplexCellL2) :
    cellComplexPair u (-z) = -cellComplexPair u z := by
  apply Complex.ext
  · simp only [Complex.neg_re, cellComplexPair_re, inner_neg_right]
  · simp only [Complex.neg_im, cellComplexPair_im, map_neg, inner_neg_right]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Negating an admissible drift negates its genuine cell multiplication operators. -/

theorem cellDrift_neg {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) :
    IsCellDrift (fun t x => -v t x) := by
  refine ⟨hv.1.neg, ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hv.2.1
    exact ⟨M, fun t x => by simpa using hM t x⟩
  · intro t n x
    exact congrArg Neg.neg (hv.2.2.1 t n x)
  · intro t φ
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, integral_neg,
      hv.2.2.2 t φ, neg_zero]

theorem cellDrift_neg_bound {v : ℝ → Vec 2 → Vec 2} {V : ℝ}
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    ∀ t x, ∑ i, (-v t x) i ^ 2 ≤ V ^ 2 := by
  intro t x
  simpa using hb t x

theorem cellDriftEntryCLM_neg {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2)
    (u : ComplexCellL2) :
    cellDriftEntryCLM ⟨0, (fun t x => -v t x), 0, 0⟩ V
      (cellDrift_neg hv).1 (cellDrift_neg_bound hb) t j u =
        -cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j u := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae ⟨0, (fun t x => -v t x), 0, 0⟩ V
    (cellDrift_neg hv).1 (cellDrift_neg_bound hb) t j u,
    cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb t j u,
    Lp.coeFn_neg (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j u)] with x hn hp he
  rw [hn, he]
  change ((-v t x j : ℝ) : ℂ) * u x = -(cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j u x)
  rw [hp, Complex.ofReal_neg, neg_mul]

/-! Exact averaging of actual constant L² classes on the unit cell. -/

theorem cellMeanCLM_constant (c : ℂ) : cellMeanCLM (cellConstantCLM c) = c := by
  rw [cellMeanCLM_apply]
  change (∫ x in AVenhance.unitCube, cellConstantCLM c x) = c
  rw [integral_congr_ae (cellConstantCLM_ae c), integral_const]
  simp only [Measure.real_def, Measure.restrict_apply_univ, cellCube_volume_one, ENNReal.toReal_one, one_smul]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! A small actual cell mean leaves a quantitative fraction of the L² mass in the mean-free component. -/

theorem cellMeanFree_norm_lower (u : ComplexCellL2) (δ : ℝ)
    (hm : ‖cellMeanCLM u‖ ≤ δ * ‖u‖) :
    (1 - δ) * ‖u‖ ≤ ‖cellQ0CLM u‖ := by
  have hn := norm_sub_norm_le u (cellConstantCLM (cellMeanCLM u))
  rw [cellConstantCLM_norm] at hn
  change (1 - δ) * ‖u‖ ≤ ‖u - cellConstantCLM (cellMeanCLM u)‖
  nlinarith

theorem cellMeanFree_norm_sq_lower (u : ComplexCellL2) (δ : ℝ) (hδ : δ ≤ 1)
    (hm : ‖cellMeanCLM u‖ ≤ δ * ‖u‖) :
    (1 - δ) ^ 2 * ‖u‖ ^ 2 ≤ ‖cellQ0CLM u‖ ^ 2 := by
  have hl := cellMeanFree_norm_lower u δ hm
  have hp : 0 ≤ (1 - δ) * ‖u‖ := mul_nonneg (sub_nonneg.mpr hδ) (norm_nonneg u)
  nlinarith [norm_nonneg (cellQ0CLM u)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Real metric multiplication commutes with actual complex scalar multiplication. -/

theorem cellMetricEntryCLM_scalar
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (c : ℂ) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k (cellScalarCLM c u) =
      cellScalarCLM c (cellMetricEntryCLM hG t j k u) := by
  apply Lp.ext
  filter_upwards [cellMetricEntryCLM_ae hG t j k (cellScalarCLM c u),
    cellScalarCLM_ae c u, cellScalarCLM_ae c (cellMetricEntryCLM hG t j k u),
    cellMetricEntryCLM_ae hG t j k u] with x hmu hu hcu hm
  rw [hmu, hu, hcu, hm]
  ring

theorem cellScalarCLM_mul (c d : ℂ) (u : ComplexCellL2) :
    cellScalarCLM c (cellScalarCLM d u) = cellScalarCLM (c * d) u := by
  simp only [cellScalarCLM_smul, mul_smul]

/-! Complex linearity and preservation of mean-free literal forcing. -/

section
local instance cellQ0ComplexAlgebraProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Complex scalar multiplication commutes with the actual cell mean, even on exceptional slices. -/
theorem cellMean_complex_smul (z : ℂ) (f : Vec 2 → ℂ) :
    cellMean (z • f) = z * cellMean f := by
  change (∫ x in AVenhance.unitCube, z • f x) = _
  rw [integral_smul]
  rfl

/-- Complex scalar multiplication commutes with the literal cell projection. -/
theorem cellQ0_complex_smul (z : ℂ) (f : Vec 2 → ℂ) :
    cellQ0 (z • f) = z • cellQ0 f := by
  funext x
  simp only [cellQ0, cellMean_complex_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The literal projection commutes with addition on genuine L2 slices. -/
theorem cellQ0_add (f g : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) :
    cellQ0 (f + g) = cellQ0 f + cellQ0 g := by
  have hm : cellMean (f + g) = cellMean f + cellMean g :=
    integral_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
  funext x
  simp only [cellQ0, Pi.add_apply, hm]
  ring

/-- The projection fixes any literal zero-mean representative, without a regularity premise. -/
theorem cellQ0_eq_self_of_mean_zero (f : Vec 2 → ℂ) (hf : cellMean f = 0) :
    cellQ0 f = f := by
  funext x
  simp only [cellQ0, hf, sub_zero]
end

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Complex multiplication has its usual conjugate adjoint on the realified cell L2 carrier. -/

theorem cellScalarCLM_inner (c : ℂ) (u z : ComplexCellL2) :
    inner ℝ (cellScalarCLM c u) z = inner ℝ u (cellScalarCLM (star c) z) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellScalarCLM_ae c u, cellScalarCLM_ae (star c) z] with x hu hz
  rw [hu, hz]
  calc
    _ = inner ℝ (z x) (c * u x) := real_inner_comm _ _
    _ = inner ℝ (star c * z x) (u x) := cellComplex_real_inner_smul (z x) c (u x)
    _ = _ := real_inner_comm _ _

theorem cellScalarCLM_adjoint (c : ℂ) : (cellScalarCLM c).adjoint = cellScalarCLM (star c) := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = inner ℝ (cellScalarCLM c u) z := real_inner_comm _ _
    _ = inner ℝ u (cellScalarCLM (star c) z) := cellScalarCLM_inner c u z
    _ = _ := real_inner_comm _ _

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual shifted Sobolev derivative represents the literal raw covariant gradient. -/

theorem cellShiftedDerivative_jet_ae (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) (D : RawJet2 1 ℂ)
    (hu : ∀ a, (u.val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D a) (j : Fin 2) :
    (cellShiftedDerivativeCLM θ j u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => cellCovGradient θ D x j := by
  change ((cellDerivativeCLM j u + cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u) :
    ComplexCellL2) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] _
  have hd := hu ⟨⟨1, by decide⟩, fun _ => j⟩
  have hv := hu (valueIndex2 1)
  filter_upwards [Lp.coeFn_add (cellDerivativeCLM j u)
    (cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)),
    cellScalarCLM_ae (Complex.I * θ j) (torusHkValueCLM u), hd, hv] with x hx hc hdx hvx
  change cellDerivativeCLM j u x = _ at hdx
  change torusHkValueCLM u x = _ at hvx
  rw [hx]
  simp only [Pi.add_apply]
  rw [hc, hdx, hvx]
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.CycleEvolution

/-! Finite sum and real scaling rules for norm-convergent uniformly local source families. -/

/-- Fixed real scaling preserves uniformly local norm convergence. -/
theorem cellUlNorm_smul_tendsto {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : Filter P) (r : ℝ) (f : P → ℝ → Vec 2 → E) (f0 : ℝ → Vec 2 → E)
    (hfm : ∀ p, AEStronglyMeasurable (Function.uncurry (f p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf0m : AEStronglyMeasurable (Function.uncurry f0)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : Tendsto (fun p => cellUlNorm Set.univ (f p - f0)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm Set.univ (r • f p - r • f0)) l (𝓝 0) := by
  have hb (p : P) : cellUlNorm Set.univ (r • f p - r • f0) ≤
      ‖r‖ₑ * cellUlNorm Set.univ (f p - f0) := by
    rw [← smul_sub]
    exact cellUlNorm_smul Set.univ r _ ((hfm p).sub hf0m)
  have hl := ENNReal.Tendsto.const_mul hf (a := ‖r‖ₑ) (Or.inr enorm_ne_top)
  have hlim : Tendsto (fun p => ‖r‖ₑ * cellUlNorm Set.univ (f p - f0)) l (𝓝 0) := by
    simpa only [mul_zero] using hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb

/-- Any finite sum of jointly almost measurable norm-convergent source families converges in norm. -/
theorem cellUlNorm_finset_sum_tendsto {P J E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : Filter P) (S : Finset J)
    (f : J → P → ℝ → Vec 2 → E) (f0 : J → ℝ → Vec 2 → E)
    (hfm : ∀ j ∈ S, ∀ p, AEStronglyMeasurable (Function.uncurry (f j p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf0m : ∀ j ∈ S, AEStronglyMeasurable (Function.uncurry (f0 j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : ∀ j ∈ S, Tendsto (fun p => cellUlNorm Set.univ (f j p - f0 j)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm Set.univ ((∑ j ∈ S, f j p) - ∑ j ∈ S, f0 j)) l (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cellUlNorm, cellL2Norm, tendsto_const_nhds]
  | @insert j S hj ih =>
    have hmS (p : P) : AEStronglyMeasurable (Function.uncurry (∑ k ∈ S, f k p))
        ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
      simpa only [Function.uncurry_def, Finset.sum_apply] using
        cellFinite_sum_aestronglyMeasurable S (fun k (z : ℝ × Vec 2) => f k p z.1 z.2)
          (fun k hk => hfm k (Finset.mem_insert_of_mem hk) p)
    have hm0S : AEStronglyMeasurable (Function.uncurry (∑ k ∈ S, f0 k))
        ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
      simpa only [Function.uncurry_def, Finset.sum_apply] using
        cellFinite_sum_aestronglyMeasurable S (fun k (z : ℝ × Vec 2) => f0 k z.1 z.2)
          (fun k hk => hf0m k (Finset.mem_insert_of_mem hk))
    have hih := ih (fun k hk => hfm k (Finset.mem_insert_of_mem hk))
      (fun k hk => hf0m k (Finset.mem_insert_of_mem hk))
      (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hj] using cellUlNorm_add_tendsto l (f j)
      (fun p => ∑ k ∈ S, f k p) (f0 j) (∑ k ∈ S, f0 k)
      (hfm j (Finset.mem_insert_self _ _)) hmS (hf0m j (Finset.mem_insert_self _ _)) hm0S
      (hf j (Finset.mem_insert_self _ _)) hih

end AVRegularity.CycleEvolution
end
end

section
/-! Restriction and integrability calculus for weak-time cell curves. -/

@[expose] public noncomputable section

open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleEvolution

/-- Weak Hilbert cell curves restrict to smaller closed intervals. -/
theorem CellWeakHilbertCurve.mono {a b c d : ℝ}
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (hsub : Icc c d ⊆ Icc a b) : CellWeakHilbertCurve c d u slice g := by
  refine ⟨h.trace.mono hsub,
    h.state.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.dual.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)), ?_⟩
  intro s hs t ht hst z
  exact h.increment s (hsub hs) t (hsub ht) hst z

/-- Weak energy production is integrable, as a product of two Bochner L² fields. -/
theorem CellWeakHilbertCurve.production_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    IntervalIntegrable (fun t => 2 * inner ℝ (g t) (slice t)) volume a b := by
  have hm : Integrable (fun t => 2 * (‖g t‖ * ‖slice t‖)) (volume.restrict (Icc a b)) :=
    (memLp_one_iff_integrable.mp (h.dual.norm.mul h.state.norm : MemLp _ 1 _)).const_mul 2
  have hp : Integrable (fun t => 2 * inner ℝ (g t) (slice t)) (volume.restrict (Icc a b)) := by
    apply hm.mono'
    · exact aestronglyMeasurable_const.mul (h.dual.aestronglyMeasurable.inner h.state.aestronglyMeasurable)
    · apply Filter.Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hp.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Every fixed H¹ test has an integrable pairing with the Hilbert dual derivative. -/
theorem cellWeakPair_intervalIntegrable {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) (g : ℝ → TorusHk 1 ℂ)
    (hg : MemLp g 2 (volume.restrict (Icc a b))) (z : TorusHk 1 ℂ) :
    IntervalIntegrable (fun r => inner ℝ (g r) z) volume s t := by
  have hm := (innerSL ℝ z).comp_memLp' hg
  have hi : Integrable (fun r => inner ℝ (g r) z) (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      hm.integrable (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact hi.mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

/-- Differences retain the weak Hilbert time equation and almost-everywhere H¹ lift. -/
theorem CellWeakHilbertCurve.sub {a b : ℝ}
    {u v : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (h' : CellWeakHilbertCurve a b v slice' g') :
    CellWeakHilbertCurve a b (fun t => u t - v t) (fun t => slice t - slice' t)
      (fun t => g t - g' t) := by
  refine ⟨h.trace.sub h'.trace, h.state.sub h'.state, h.dual.sub h'.dual, ?_, ?_⟩
  · filter_upwards [h.agrees, h'.agrees] with t ht ht'
    rw [ht, ht', map_sub]
  · intro s hs t ht hst z
    have hg := cellWeakPair_intervalIntegrable hs ht hst g h.dual z
    have hg' := cellWeakPair_intervalIntegrable hs ht hst g' h'.dual z
    simp only [inner_sub_left]
    rw [intervalIntegral.integral_sub hg hg']
    have hu := h.increment s hs t ht hst z
    have hv := h'.increment s hs t ht hst z
    linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual bounded measurable spatial multipliers as complex-linear operators. -/

def cellCoefficientComplexCLM (b : Vec 2 → ℂ)
    (hb : AEStronglyMeasurable b (volume.restrict AVenhance.unitCube))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖b x‖ ≤ B) :
    ComplexCellL2 →L[ℂ] ComplexCellL2 := by
  let R := cellCoefficientCLM b hb B hB hbound
  let L : ComplexCellL2 →ₗ[ℂ] ComplexCellL2 :=
    { toFun := R
      map_add' := R.map_add
      map_smul' := fun c u => by
        change cellCoefficientCLM b hb B hB hbound (cellScalarCLM c u) =
          cellScalarCLM c (cellCoefficientCLM b hb B hB hbound u)
        exact cellCoefficientCLM_complex_scalar b hb B hB hbound c u }
  exact L.mkContinuous ‖R‖ (fun u => R.le_opNorm u)

theorem cellCoefficientComplexCLM_eq (b : Vec 2 → ℂ)
    (hb : AEStronglyMeasurable b (volume.restrict AVenhance.unitCube))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖b x‖ ≤ B) (u : ComplexCellL2) :
    cellCoefficientComplexCLM b hb B hB hbound u = cellCoefficientCLM b hb B hB hbound u := rfl

end AVRegularity.CycleEvolution
end
end

section
/-! Scalar multiplication and conjugation of periodic H¹ cell tests. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational

namespace AVRegularity.CycleEvolution

/-- Complex scalar multiplication preserves the realified H¹ graph. -/
def cellH1Scalar (c : ℂ) (z : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  mapTorusHk (ContinuousLinearMap.mul ℝ ℂ c) z

/-- Conjugation preserves the periodic weak H¹ graph. -/
def cellH1Conj (z : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  mapTorusHk Complex.conjCLE.toContinuousLinearMap z

/-- Scalar multiplication has the literal representative at every jet coordinate. -/
theorem cellH1Scalar_jet_ae (c : ℂ) (z : TorusHk 1 ℂ) (a : JetIndex2 1) :
    (cellH1Scalar c z).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c * z.val a x := mapTorusHk_jet_ae _ z a

/-- Conjugation has the literal representative at every jet coordinate. -/
theorem cellH1Conj_jet_ae (z : TorusHk 1 ℂ) (a : JetIndex2 1) :
    (cellH1Conj z).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (z.val a x) := mapTorusHk_jet_ae _ z a

/-- The shifted test derivative commutes with complex scalar multiplication. -/
theorem cellH1Scalar_shift_ae (θ : Fin 2 → ℂ) (c : ℂ) (z : TorusHk 1 ℂ) (j : Fin 2) :
    cellShiftedDerivativeCLM θ j (cellH1Scalar c z) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c * cellShiftedDerivativeCLM θ j z x := by
  filter_upwards [cellShiftedDerivativeCLM_ae θ j (cellH1Scalar c z),
    cellShiftedDerivativeCLM_ae θ j z,
    cellH1Scalar_jet_ae c z (valueIndex2 1),
    cellH1Scalar_jet_ae c z ⟨⟨1, by decide⟩, fun _ => j⟩] with x hs hz hv hd
  change cellDerivativeCLM j (cellH1Scalar c z) x = c * cellDerivativeCLM j z x at hd
  change torusHkValueCLM (cellH1Scalar c z) x = c * torusHkValueCLM z x at hv
  rw [hs, hz, hd, hv]
  ring

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- The value class of a scalar-multiplied test is its scalar-multiplied value class. -/
theorem cellH1Scalar_value (c : ℂ) (z : TorusHk 1 ℂ) :
    torusHkValueCLM (cellH1Scalar c z) = cellScalarCLM c (torusHkValueCLM z) := by
  apply Lp.ext
  exact (cellH1Scalar_jet_ae c z (valueIndex2 1)).trans (cellScalarCLM_ae c _).symm

/-- The shifted derivative classes commute with multiplication of the test. -/
theorem cellH1Scalar_shift (θ : Fin 2 → ℂ) (c : ℂ) (z : TorusHk 1 ℂ) (j : Fin 2) :
    cellShiftedDerivativeCLM θ j (cellH1Scalar c z) = cellScalarCLM c (cellShiftedDerivativeCLM θ j z) := by
  apply Lp.ext
  exact (cellH1Scalar_shift_ae θ c z j).trans (cellScalarCLM_ae c _).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Literal coefficient pullback identifies the actual Riesz derivative under time reversal. -/

def cellReverseTimeCoefficients (C : CellCoefficients) : CellCoefficients :=
  ⟨fun t x => C.G (-t) x, fun t x => C.v (-t) x, C.θ, fun t => C.κ (-t)⟩

theorem cellDualDerivative_reverse_time (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative (cellReverseTimeCoefficients C) (cellMetric_timeReverse hG) V
      (hv.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
      (fun s x => hb (-s) x) t u S F =
        cellDualDerivative C hG V hv hb (-t) u S F := by
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Discharge coefficient measurability and boundedness for the actual finite cell systems. -/

/-- The actual mass-inverted cell generator is measurable in time. -/
theorem cellGalerkin_actualOperator_aestronglyMeasurable
    (N : ℕ) (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : Measurable C.κ) :
    AEStronglyMeasurable
      (fun t => cellGalerkinOperator N (cellGeneratorB C hG V hv hb t)) volume := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  apply weakMassGeneratorCLM_aestronglyMeasurable basis
    (cellGalerkinMass N) (cellGalerkinMass_injective N)
    (fun t => cellGalerkinForm N (cellGeneratorB C hG V hv hb t))
  intro i j
  exact (cellGeneratorForm_pairing_stronglyMeasurable C hG V hv hb hκ
    (basis j).val (basis i).val).aestronglyMeasurable

/-- Actual finite cell generators are uniformly bounded; no spatial continuity is used. -/
theorem cellGalerkin_actualOperator_bounded
    (N : ℕ) (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖cellGalerkinOperator N (cellGeneratorB C hG V hv hb t)‖ ≤ M := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  let entry := fun i j =>
    (∑ r : Fin 2, ∑ l : Fin 2,
      2 * ‖cellShiftedDerivativeCLM C.θ r (basis j).val‖ *
        ‖cellShiftedDerivativeCLM (fun a => star (C.θ a)) l (basis i).val‖)
    + (∑ r : Fin 2, |V| * ‖cellShiftedDerivativeCLM C.θ r (basis j).val‖ *
        ‖torusHkValueCLM (basis i).val‖)
    + k * ‖torusHkValueCLM (basis j).val‖ * ‖torusHkValueCLM (basis i).val‖
  let M := ∑ i, ∑ j, entry i j *
    ‖weakMassGeneratorCLM (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (weakRankOneForm basis i j)‖
  have hk : 0 ≤ k := (norm_nonneg (C.κ 0)).trans (hκ 0)
  have he : ∀ i j, 0 ≤ entry i j := by
    intro i j
    dsimp only [entry]
    positivity
  refine ⟨M, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (he i j) (norm_nonneg _)))
  · intro t
    apply weakMassGeneratorCLM_norm_le basis
      (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (cellGalerkinForm N (cellGeneratorB C hG V hv hb t)) entry
    intro i j
    exact cellGeneratorForm_abs_le C hG V k hv hb hκ t (basis j).val (basis i).val

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Exact linear and quadratic difference identities for the graph scalar forcing. -/

local instance cellGraphSourceDifferenceAlgebraProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Subtraction cancels the constant part of the projected affine graph multiplier. -/
theorem cellProjectedAffine_difference (b f g : Vec 2 → ℂ)
    (hf : MemLp (fun y => -Complex.I * b y * (1 + f y)) 2
      (volume.restrict AVenhance.unitCube))
    (hg : MemLp (fun y => -Complex.I * b y * (1 + g y)) 2
      (volume.restrict AVenhance.unitCube)) (x : Vec 2) :
    cellQ0 (fun y => -Complex.I * b y * (1 + f y)) x -
      cellQ0 (fun y => -Complex.I * b y * (1 + g y)) x =
      cellQ0 (fun y => -Complex.I * b y * (f y - g y)) x := by
  have he : (fun y => -Complex.I * b y * (1 + f y)) -
      (fun y => -Complex.I * b y * (1 + g y)) =
      (fun y => -Complex.I * b y * (f y - g y)) := by
    funext y
    simp only [Pi.sub_apply]
    ring
  have h := cellQ0_sub _ _ hf hg
  rw [he] at h
  exact (congrFun h x).symm

/-- The mean of the difference of two drift products is the difference of their literal means. -/
theorem cellMean_multiplier_difference (b f g : Vec 2 → ℂ)
    (hf : MemLp (fun y => b y * f y) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (fun y => b y * g y) 2 (volume.restrict AVenhance.unitCube)) :
    cellMean (fun y => b y * (f y - g y)) =
      cellMean (fun y => b y * f y) - cellMean (fun y => b y * g y) := by
  have he : (fun y => b y * (f y - g y)) =
      (fun y => b y * f y) - (fun y => b y * g y) := by
    funext y
    simp only [Pi.sub_apply, mul_sub]
  rw [he]
  exact integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

/-- The quadratic graph multiplier splits into two genuine difference factors. -/
theorem cellGraphQuadratic_difference (b f g : Vec 2 → ℂ)
    (hf : MemLp (fun y => b y * f y) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (fun y => b y * g y) 2 (volume.restrict AVenhance.unitCube)) (x : Vec 2) :
    Complex.I * f x * cellMean (fun y => b y * f y) -
      Complex.I * g x * cellMean (fun y => b y * g y) =
      Complex.I * (f x - g x) * cellMean (fun y => b y * f y) +
        Complex.I * g x * cellMean (fun y => b y * (f y - g y)) := by
  rw [cellMean_multiplier_difference b f g hf hg]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every total L² slice of a mean-free raw source has zero mean, including exceptional slices. -/

/-- Mean subtraction gives a mean-zero total source class at every time. -/
theorem cellSourceSlice_Q0_mean (f : ℝ → Vec 2 → ℂ) (t : ℝ) :
    cellMean (cellSourceSlice (fun s => cellQ0 (f s)) t) = 0 := by
  classical
  let : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩
  by_cases h : MemLp (cellQ0 (f t)) 2 (volume.restrict AVenhance.unitCube)
  · have hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube) := by
      apply (h.add (memLp_const (cellMean (f t)))).ae_eq
      filter_upwards with x
      simp only [Pi.add_apply, cellQ0, sub_add_cancel]
    exact (integral_congr_ae (cellSourceSlice_ae (fun s => cellQ0 (f s)) t h)).trans
      (cellQ0_mean hf)
  · rw [cellSourceSlice, dite_eq_right h, ← cellMeanCLM_apply, map_zero]

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The literal uniform coefficient bound controls its complex L2 operator norm. -/

theorem cellCoefficientComplexCLM_apply_norm_le (b : Vec 2 → ℂ)
    (hb : AEStronglyMeasurable b (volume.restrict AVenhance.unitCube))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, ‖b x‖ ≤ B) (u : ComplexCellL2) :
    ‖cellCoefficientComplexCLM b hb B hB hbound u‖ ≤ B * ‖u‖ := by
  rw [cellCoefficientComplexCLM_eq]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cellCoefficientCLM_ae b hb B hB hbound u] with x hx
  rw [hx]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Hermitian symmetry of the complex pairing on the realified cell carrier. -/

theorem cellComplexPair_symm (u z : ComplexCellL2) :
    cellComplexPair u z = star (cellComplexPair z u) := by
  apply Complex.ext
  · change (cellComplexPair u z).re = (cellComplexPair z u).re
    rw [cellComplexPair_re, cellComplexPair_re]
    exact real_inner_comm z u
  · change (cellComplexPair u z).im = -(cellComplexPair z u).im
    rw [cellComplexPair_im, cellComplexPair_im]
    have hs := cellScalarCLM_inner Complex.I z u
    rw [show star Complex.I = -Complex.I from Complex.conj_I] at hs
    have hn : cellScalarCLM (-Complex.I) u = -cellScalarCLM Complex.I u := by
      apply Lp.ext
      filter_upwards [cellScalarCLM_ae (-Complex.I) u, cellScalarCLM_ae Complex.I u,
        Lp.coeFn_neg (cellScalarCLM Complex.I u)] with x hl hr hx
      rw [hl, hx]
      change -Complex.I * u x = -(cellScalarCLM Complex.I u x)
      rw [hr, neg_mul]
    rw [hn, inner_neg_right] at hs
    exact (real_inner_comm (cellScalarCLM Complex.I z) u).trans hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual conjugation on the cell L² carrier and its literal algebra. -/

theorem cellFiberConj_ae (u : ComplexCellL2) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap u
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => star (u x) :=
  ContinuousLinearMap.coeFn_compLpL Complex.conjCLE.toContinuousLinearMap u

theorem cellFiberConj_involutive (u : ComplexCellL2) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) = u := by
  apply Lp.ext
  filter_upwards [cellFiberConj_ae (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u),
    cellFiberConj_ae u] with x hh hu
  rw [hh, hu, star_star]

theorem cellFiberConj_scalar (c : ℂ) (u : ComplexCellL2) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellScalarCLM c u) =
      cellScalarCLM (star c) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u) := by
  apply Lp.ext
  filter_upwards [cellFiberConj_ae (cellScalarCLM c u), cellScalarCLM_ae c u,
    cellScalarCLM_ae (star c) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u),
    cellFiberConj_ae u] with x hh hc hs hu
  rw [hh, hc, hs, hu, star_mul]
  exact mul_comm _ _

theorem cellFiberConj_constant (c : ℂ) :
    cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellConstantCLM c) =
      cellConstantCLM (star c) := by
  apply Lp.ext
  filter_upwards [cellFiberConj_ae (cellConstantCLM c), cellConstantCLM_ae c,
    cellConstantCLM_ae (star c)] with x hh hc hs
  rw [hh, hc, hs]

end AVRegularity.CycleEvolution
end
end
