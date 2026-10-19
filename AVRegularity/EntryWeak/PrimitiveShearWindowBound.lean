-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
public import AVRegularity.EntryWeak.MolecularDualNormBounds
import AVRegularity.CycleDamping.ReferenceTimeEquation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Whole-family regularity justifies the scalar component identity for the literal normalized flux. -/

variable {ι : Type*} [Fintype ι]

theorem normalizedLiftFluxCrossSource_component (H : ℕ) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (Q₁ : ∀ u, JointSourceReserve (H + 1) (fun t z Y => f₁ t z Y u))
    (Q₂ : ∀ u, JointSourceReserve (H + 1) (fun t z Y => f₂ t z Y u))
    (k : Fin 2) (t : ℝ) (z Y : Vec 2) (u : ι) :
    normalizedLiftFluxCrossSource A η G v (fun t z Y => f₁ t z Y u)
      (fun t z Y => f₂ t z Y u) k t z Y =
    ((Real.exp (A Y))⁻¹ •
      (((Real.sqrt η * v t z k) • (Real.exp (A Y) • f₁ t z Y) -
        Real.sqrt η • ∑ j : Fin 2, G t Y k j •
          fastPartial j (fun X y => Real.exp (A X) • f₁ t y X) Y z) -
        η • ∑ j : Fin 2, G t Y k j •
          slowPartial j (fun X y => Real.exp (A X) • f₂ t y X) Y z)) u := by
  classical
  let R₁ := jointSourcePiReserve (H + 1) (fun u t z Y => f₁ t z Y u) Q₁
  let R₂ := jointSourcePiReserve (H + 1) (fun u t z Y => f₂ t z Y u) Q₂
  have h₁ : IsBoxSmooth 0 1 (fun X y => Real.exp (A X) • f₁ t y X) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _ ((R₁.exponentialGoodField A t).mono (by omega)).1
  have h₂ : IsBoxSmooth 1 0 (fun X y => Real.exp (A X) • f₂ t y X) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _ ((R₂.exponentialGoodField A t).mono (by omega)).1
  have hf j := fastPartial_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u) _ h₁ j Y z
  have hs j := slowPartial_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u) _ h₂ j Y z
  simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply] at hf hs
  simp only [normalizedLiftFluxCrossSource, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, hf, hs]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! The public finite-window solution predicate already implies a finite energy norm. -/

theorem cellSolution_finite_energyNorm {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) : cellEnergyNorm (Icc a b) D < ⊤ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (AVRegularity.CycleEvolution.IsCellSolution.trace_continuous h)
  have hv : (⨆ t ∈ Icc a b, cellL2Norm (cellValue D t)) ≤ ENNReal.ofReal M := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [AVRegularity.CycleEvolution.cellL2Norm_eq_of_class _ _
      (AVRegularity.CycleEvolution.cellRawTrace_ae D t (h.2.2.1 t ht).1)]
    exact ENNReal.ofReal_le_ofReal (hM t ht)
  have hg := h.2.2.2.2.2.1 a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩
  have hu := AVRegularity.CycleEvolution.cellUlNorm_le_totalEnergy (Icc a b)
    (fun t => cellGradient (D t)) _ le_rfl
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact hv.trans_lt ENNReal.ofReal_lt_top
  · exact hu.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.ne)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Strong measurability of the actual H⁻¹ derivative of a Bochner H¹ state. -/

/-- The actual generator and sources produce a strongly measurable H¹ Riesz derivative. -/
theorem dataDualDerivative_aestronglyMeasurable {μ : Measure ℝ}
    (P : MolecularData)
    (f : ℝ → TorusHk 1 ℂ) (hf : AEStronglyMeasurable f μ)
    (S : ℝ → ComplexCellL2) (hS : AEStronglyMeasurable S μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, AEStronglyMeasurable (fun t => F t j) μ) :
    AEStronglyMeasurable (fun t => dataDualDerivative P t (f t) (S t) (F t)) μ := by
  apply cellH1_aestronglyMeasurable_of_pairings
  intro z
  simp only [dataDualDerivative_pairing]
  have hgen := cellVariableForm_pairing_aestronglyMeasurable (dataGeneratorForm P)
    (fun u z => (dataGeneratorForm_pairing_stronglyMeasurable P u z).aestronglyMeasurable)
    f hf z
  have hs : AEStronglyMeasurable (fun t => cellSourceFunctional 0 (S t) (F t) z) μ := by
    have h0 := hS.inner (𝕜 := ℝ) (aestronglyMeasurable_const (b := torusHkValueCLM z))
    have h1 (j : Fin 2) := (hF j).inner (𝕜 := ℝ)
      (aestronglyMeasurable_const (b := cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j z))
    simpa only [cellSourceFunctional, sub_apply, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Fin.sum_univ_two, Pi.add_def, Pi.sub_def] using h0.sub ((h1 0).add (h1 1))
  exact hgen.add hs

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The actual finite inherited flux polynomial has bounded normalized forcing reserves. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedSourceFluxReserve (H : ℕ) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (η : ℝ) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → Vec 2 → ι → ℝ)
    (Qf : JointSourceReserve (H + D) f)
    (Qedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z))
    (k : Fin 2) (j : ℕ) (v : ι) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceFluxCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) k j Y z v) := by
  let F := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (α : DerivativeWord2 (d.val - 1)) t z Y =>
    γ.coeff α t Y z k • γ.map
      ((Real.exp (A Y))⁻¹ • covariantListCoefficients η (List.ofFn α)
        (fun X y => Real.exp (A X) • f t y X) j Y z u)
  let Qword := fun (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.val - 1)) =>
    normalizedCovariantListReserve Qf H A η (List.ofFn α)
      (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.property).2; omega) j
  let Q := fun (u : ι) (d : Finset.Icc 2 D)
      (γ : Constituent d.val ℝ ℝ) (hγ : γ ∈ edge v u d)
      (α : DerivativeWord2 (d.val - 1)) =>
    ((Qedge v u d γ hγ α).map
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)).scalarProduct
        (((Qword d α).map
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u)).map γ.map)
  let S := JointSourceReserve.fintypeSum H
    (fun u t z Y => ∑ d : Finset.Icc 2 D,
      ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
    (fun u => JointSourceReserve.fintypeSum H
      (fun d t z Y => ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
      (fun d => JointSourceReserve.listSum (edge v u d) H
        (fun γ t z Y => ∑ α, F u d γ α t z Y)
        (fun γ hγ => JointSourceReserve.fintypeSum H (F u d γ) (Q u d γ hγ))))
  have he : (fun t z Y => (Real.exp (A Y))⁻¹ •
      sourceFluxCoefficientArray edge η t
        (fun X y => Real.exp (A X) • f t y X) k j Y z v) =
      fun t z Y => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum := by
    funext t z Y
    simp only [sourceFluxCoefficientArray, Finset.smul_sum, List.smul_sum, List.map_map,
      Function.comp_def]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro d _
    apply congrArg List.sum
    apply List.map_congr_left
    intro γ _
    apply Finset.sum_congr rfl
    intro α _
    change (Real.exp (A Y))⁻¹ • (γ.coeff α t Y z k • γ.map _) =
      γ.coeff α t Y z k • γ.map ((Real.exp (A Y))⁻¹ • _)
    rw [map_smul]
    exact smul_comm _ _ _
  rw [he]
  exact S

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The actual H⁻¹ cell derivative belongs to temporal L². -/

/-- The coefficient bounds and Bochner L² state/source data imply an L² dual derivative. -/
theorem dataDualDerivative_memLp {μ : Measure ℝ}
    (P : MolecularData)
    (f : ℝ → TorusHk 1 ℂ) (hf : MemLp f 2 μ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, MemLp (fun t => F t j) 2 μ) :
    MemLp (fun t => dataDualDerivative P t (f t) (S t) (F t)) 2 μ := by
  obtain ⟨M, hM, hMb⟩ := dataGeneratorForm_uniform_norm_bound P
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let D := fun j => ‖cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j‖
  let budget := fun t => M * ‖f t‖ + J * ‖S t‖ + D 0 * ‖F t 0‖ + D 1 * ‖F t 1‖
  have hm : MemLp budget 2 μ := by
    simpa only [budget, Pi.smul_def, smul_eq_mul, Pi.add_def] using
      (((hf.norm.const_smul M).add (hS.norm.const_smul J)).add
        ((hF 0).norm.const_smul (D 0))).add ((hF 1).norm.const_smul (D 1))
  have hmeas := dataDualDerivative_aestronglyMeasurable P f
    hf.aestronglyMeasurable S hS.aestronglyMeasurable F (fun j => (hF j).aestronglyMeasurable)
  apply hm.of_le hmeas
  apply Filter.Eventually.of_forall
  intro t
  have hbn : 0 ≤ budget t := by dsimp only [budget, J, D]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbn]
  have hn := dataDualDerivative_norm_le P t (f t) (S t) (F t)
  have hb' := hMb t (f t)
  dsimp only [budget, J, D]
  simp only [Fin.sum_univ_two] at hn
  linarith

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Smooth periodic sources produce finite higher carriers with their literal readouts. -/

local instance finiteHigherSourceDataFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp only [Measure.restrict_apply_univ, weak_unitCube_volume]; exact ENNReal.one_lt_top⟩

def finiteHigherSourceData (a b : ℝ) (K : ℕ)
    (src : ℝ → Vec 2 → ℂ) (flux : ℝ → Vec 2 → ComplexCellVector)
    (hs : ∀ t, ContDiff ℝ (K : ℕ∞) (src t))
    (hf : ∀ t, ContDiff ℝ (K : ℕ∞) (flux t))
    (hps : ∀ t, AVenhance.IsZ2Periodic (src t))
    (hpf : ∀ t, AVenhance.IsZ2Periodic (flux t))
    (hms : Measurable (Function.uncurry src))
    (hmf : Measurable (Function.uncurry flux))
    (Cs Cf : ℕ → ℝ) (hCs : ∀ n, 0 ≤ Cs n) (hCf : ∀ n, 0 ≤ Cf n)
    (hbs : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (src t) z‖ ≤ Cs n)
    (hbf : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (flux t) z‖ ≤ Cf n)
    (hz : ∀ t, cellMean (src t) = 0) : HigherSourceCarrierData (Set.Icc a b) K src flux where
  S t := finiteBoundedSmoothPeriodicHk K (src t) (hs t) (hps t) Cs (fun n hn z => hbs n hn t z)
  F t := finiteBoundedSmoothPeriodicHk K (flux t) (hf t) (hpf t) Cf (fun n hn z => hbf n hn t z)
  Ns := ∑ j : JetIndex2 K, Cs j.1.val
  Nf := ∑ j : JetIndex2 K, Cf j.1.val
  scalar_budget_nonneg := Finset.sum_nonneg (fun _ _ => hCs _)
  flux_budget_nonneg := Finset.sum_nonneg (fun _ _ => hCf _)
  scalar_memLp := MemLp.of_bound hms.aestronglyMeasurable (Cs 0)
    (Filter.Eventually.of_forall fun p => by
      simpa only [norm_iteratedFDeriv_zero, Function.uncurry] using hbs 0 (Nat.zero_le K) p.1 p.2)
  flux_memLp := MemLp.of_bound hmf.aestronglyMeasurable (Cf 0)
    (Filter.Eventually.of_forall fun p => by
      simpa only [norm_iteratedFDeriv_zero, Function.uncurry] using hbf 0 (Nat.zero_le K) p.1 p.2)
  scalar_carrier_memLp := finiteBoundedSmoothPeriodicHk_memLp a b K src hs hps hms Cs hCs hbs
  flux_carrier_memLp := finiteBoundedSmoothPeriodicHk_memLp a b K flux hf hpf hmf Cf hCf hbf
  scalar_value := Filter.Eventually.of_forall fun t => finiteBoundedSmoothPeriodicHk_value_ae K
    (src t) (hs t) (hps t) Cs (fun n hn z => hbs n hn t z)
  flux_value := Filter.Eventually.of_forall fun t => finiteBoundedSmoothPeriodicHk_value_ae K
    (flux t) (hf t) (hpf t) Cf (fun n hn z => hbf n hn t z)
  scalar_mean_zero := Filter.Eventually.of_forall fun t => by
    have he := finiteBoundedSmoothPeriodicHk_value_ae K (src t) (hs t) (hps t) Cs
      (fun n hn z => hbs n hn t z)
    exact (integral_congr_ae he).trans (hz t)
  scalar_bound := fun t _ => finiteBoundedSmoothPeriodicHk_norm_le K (src t) (hs t) (hps t) Cs
    hCs (fun n hn z => hbs n hn t z)
  flux_bound := fun t _ => finiteBoundedSmoothPeriodicHk_norm_le K (flux t) (hf t) (hpf t) Cf
    hCf (fun n hn z => hbf n hn t z)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! A real L² trace with a high Sobolev class has the canonical classical real readout. -/

theorem cellClassicalLift_real_high (K r : ℕ) (hr : r + 2 ≤ K)
    (w : TorusHk K ℂ) (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hw : torusHkValueCLM w = u)
    (hu : (fun x => ((u x).re : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] u) :
    ContDiff ℝ (r : ℕ∞) (cellClassicalLift u) ∧
      (fun x => (cellClassicalLift u x : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] u := by
  let f := mapTorusHk Complex.reCLM w
  have he : complexifyCellClass (f.val (valueIndex2 K)) = u := by
    apply Lp.ext
    have hf := mapTorusHk_jet_ae Complex.reCLM w (valueIndex2 K)
    have hc := ContinuousLinearMap.coeFn_compLpL (L := Complex.ofRealCLM) (f.val (valueIndex2 K))
    have hv : w.val (valueIndex2 K) = u := hw
    rw [hv] at hf
    filter_upwards [hf, hc, hu] with x hfx hcx hux
    exact hcx.trans ((congrArg Complex.ofReal hfx).trans hux)
  constructor
  · rw [← he]
    exact cellClassicalLift_contDiff K r hr f
  · rw [← he]
    exact cellClassicalLift_value_ae K (by omega) f

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Package an actual Galerkin sequence and its weak temporal H¹ limit. -/

/-- Actual finite equations, initial moments, uniform class bounds, and a weak subsequence. -/
structure MolecularGalerkinLimitData (a b : ℝ) (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (initial : ComplexCellL2) where
  curve : ∀ N, C(Icc a b, CellGalerkinSpace (E := ℂ) N)
  stateLp : ∀ N, MemLp (fun t => (extendCurve hab (curve N) t).val)
    2 (volume.restrict (Icc a b))
  variational : ∀ N, StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
    (fun t => cellGalerkinForm N (dataGeneratorB P t))
    (fun t => cellGalerkinSource N (cellRawSourceFunctional 0 src F t))
    (fun t => cellGalerkinValue N (extendCurve hab (curve N) t))
    (fun t => cellGalerkinValue N (linearRhs
      (fun r => cellGalerkinOperator N (dataGeneratorB P r))
      (fun r => cellGalerkinForcing N (cellRawSourceFunctional 0 src F r))
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

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Hilbert representatives of the fixed-test generator entries used in weak limits. -/

/-- Riesz representative in the trial variable of a fixed generator test. -/
def dataGeneratorTest (P : MolecularData)
    (t : ℝ) (z : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm
    ((dataGeneratorForm P t).flip z)

/-- The fixed-test Riesz representative gives the literal generator entry. -/
theorem dataGeneratorTest_pairing (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    inner ℝ u (dataGeneratorTest P t z) = dataGeneratorForm P t u z := by
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- Fixed-test generator representatives are strongly measurable in time. -/
theorem dataGeneratorTest_aestronglyMeasurable {μ : Measure ℝ}
    (P : MolecularData)
    (z : TorusHk 1 ℂ) :
    AEStronglyMeasurable (fun t => dataGeneratorTest P t z) μ := by
  apply cellH1_aestronglyMeasurable_of_pairings
  intro u
  simp only [real_inner_comm, dataGeneratorTest_pairing]
  exact (dataGeneratorForm_pairing_stronglyMeasurable P u z).aestronglyMeasurable

/-- A uniform form-functional bound also bounds its fixed-test Riesz representative. -/
theorem dataGeneratorTest_norm_le_of_bound
    (P : MolecularData)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t u, ‖dataGeneratorForm P t u‖ ≤ M * ‖u‖)
    (t : ℝ) (z : TorusHk 1 ℂ) : ‖dataGeneratorTest P t z‖ ≤ M * ‖z‖ := by
  unfold dataGeneratorTest
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg z))
  intro u
  calc
    _ ≤ ‖dataGeneratorForm P t u‖ * ‖z‖ :=
      (dataGeneratorForm P t u).le_opNorm z
    _ ≤ (M * ‖u‖) * ‖z‖ := mul_le_mul_of_nonneg_right (hbound t u) (norm_nonneg z)
    _ = _ := by ring

/-- Actual fixed-test generator representatives belong to temporal L² on finite intervals. -/
theorem dataGeneratorTest_memLp (a b : ℝ)
    (P : MolecularData)
    (z : TorusHk 1 ℂ) :
    MemLp (fun t => dataGeneratorTest P t z) 2 (volume.restrict (Icc a b)) := by
  obtain ⟨M, hM, hMb⟩ := dataGeneratorForm_uniform_norm_bound P
  apply (memLp_const (M * ‖z‖)).of_le
    (dataGeneratorTest_aestronglyMeasurable P z)
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (norm_nonneg z))]
    exact dataGeneratorTest_norm_le_of_bound P M hM hMb t z)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! A fixed classical real readout of a complex energy trace, independent of higher carrier choices. -/

def realCellClassicalReadout
    (u : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) : Vec 2 → ℝ :=
  cellClassicalLift (complexifyCellClass
    ((Complex.reCLM.compLpL 2 (volume.restrict AVenhance.unitCube)) u))

theorem realCellClassicalReadout_high_eq (K : ℕ) (w : TorusHk K ℂ) :
    realCellClassicalReadout (torusHkValueCLM w) =
      realClassicalLift K (mapTorusHk Complex.reCLM w) := by
  unfold realCellClassicalReadout
  change cellClassicalLift (complexifyCellClass
    ((Complex.reCLM.compLpL 2 (volume.restrict AVenhance.unitCube))
      (w.val (valueIndex2 K)))) = _
  rw [← mapTorusHk_jet_eq_compLp Complex.reCLM w (valueIndex2 K)]
  exact cellClassicalLift_eq K _

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped Classical
namespace AVRegularity.EntryWeakProofs

/-! A forcing can be cut off at the original start without changing its finite-window inverse. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem cellFieldInverse_source_ae_congr [FiniteDimensional ℝ E] {a b : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ} {c₀ : Vec 2 → E} {g g' c : ℝ → Vec 2 → E}
    (h : IsCellFieldInverse G v r a b c₀ g c)
    (he : ∀ᵐ t ∂volume.restrict (Icc a b), g t = g' t) :
    IsCellFieldInverse G v r a b c₀ g' c := by
  refine ⟨h.1, fun ℓ => ?_⟩
  have hh := h.2 ℓ
  refine ⟨cellSolution_source_congr_sections (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
    (fun t x => (ℓ (g t x) : ℂ)) (fun t x => (ℓ (g' t x) : ℂ)) 0 0
    (cellJetOfField ℓ c) ?_ (Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl)
      hh.1, hh.2⟩
  filter_upwards [he] with t ht
  rw [ht]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The canonical classical field on the requested time window, extended by zero outside. -/

def cellClassicalWindow (a b : ℝ) (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    ℝ → Vec 2 → ℝ := fun t x => if t ∈ Icc a b then cellClassicalLift (u t) x else 0

theorem cellClassicalWindow_measurable (a b : ℝ)
    (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)) (hu : Continuous u) :
    Measurable (Function.uncurry (cellClassicalWindow a b u)) := by
  apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    (cellClassicalLift_joint_measurable u hu) measurable_const

theorem cellClassicalWindow_periodic (a b : ℝ)
    (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)) (t : ℝ) :
    AVenhance.IsZ2Periodic (cellClassicalWindow a b u t) := by
  intro n x
  dsimp only [cellClassicalWindow]
  split_ifs
  · exact cellClassicalLift_periodic (u t) n x
  · rfl

theorem cellClassicalWindow_contDiff (a b : ℝ) (K r : ℕ) (hr : r + 2 ≤ K)
    (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hh : ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t)
    (hreal : ∀ t ∈ Icc a b, (fun x => ((u t x).re : ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] u t) :
    ∀ t, ContDiff ℝ (r : ℕ∞) (cellClassicalWindow a b u t) := by
  intro t
  change ContDiff ℝ (r : ℕ∞) (fun x => if t ∈ Icc a b then cellClassicalLift (u t) x else 0)
  by_cases ht : t ∈ Icc a b
  · obtain ⟨w, hw⟩ := hh t ht
    simpa only [cellClassicalWindow, ite_eq_left ht] using
      (cellClassicalLift_real_high K r hr w (u t) hw (hreal t ht)).1
  · simpa only [cellClassicalWindow, ite_eq_right ht] using
      (contDiff_const : ContDiff ℝ (r : ℕ∞) (fun _ : Vec 2 => (0 : ℝ)))

theorem cellClassicalWindow_value_ae (a b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hh : ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t)
    (hreal : ∀ t ∈ Icc a b, (fun x => ((u t x).re : ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] u t) :
    ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (cellClassicalWindow a b u t x : ℂ) := by
  intro t ht
  obtain ⟨w, hw⟩ := hh t ht
  simpa only [cellClassicalWindow, ite_eq_left ht] using
    (cellClassicalLift_real_high K 0 hK w (u t) hw (hreal t ht)).2.symm

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The fixed classical readout respects literal zero energy traces. -/

theorem realCellClassicalReadout_zero :
    realCellClassicalReadout (0 : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) = 0 := by
  simp only [realCellClassicalReadout, map_zero]
  funext z
  simp [cellClassicalLift]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Mean-free scalar projection of actual smooth full planar sources. -/

def finiteMeanFreeHigherSourceData (a b : ℝ) (K : ℕ)
    (src : ℝ → Vec 2 → ℂ) (flux : ℝ → Vec 2 → ComplexCellVector)
    (hs : ∀ t, ContDiff ℝ (K : ℕ∞) (src t))
    (hf : ∀ t, ContDiff ℝ (K : ℕ∞) (flux t))
    (hps : ∀ t, AVenhance.IsZ2Periodic (src t))
    (hpf : ∀ t, AVenhance.IsZ2Periodic (flux t))
    (hms : Measurable (Function.uncurry src))
    (hmf : Measurable (Function.uncurry flux))
    (Cs Cf : ℕ → ℝ) (hCs : ∀ n, 0 ≤ Cs n) (hCf : ∀ n, 0 ≤ Cf n)
    (hbs : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (src t) z‖ ≤ Cs n)
    (hbf : ∀ n, n ≤ K → ∀ t z, ‖iteratedFDeriv ℝ n (flux t) z‖ ≤ Cf n) :
    HigherSourceCarrierData (Set.Icc a b) K (fun t => cellQ0 (src t)) flux :=
  finiteHigherSourceData a b K (fun t => cellQ0 (src t)) flux
    (fun t => finite_cellQ0 (src t) K (hs t)) hf
    (fun t => smooth_cellQ0_periodic (src t) (hps t)) hpf
    (cellQ0_measurable hms) hmf (fun n => 2 * Cs n) Cf
    (fun n => mul_nonneg (by norm_num) (hCs n)) hCf
    (fun n hn t z => finite_cellQ0_derivative_bound (src t) K (hs t) Cs hCs
      (fun r hr x => hbs r hr t x) n hn z) hbf
    (fun t => cellQ0_mean (finite_smooth_periodic_jet_memLp K (src t) (hs t) Cs
      (fun n hn z => hbs n hn t z) (valueIndex2 K)))

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Construct the complete weak Galerkin data package from the actual premises. -/

/-- Actual measurable cell data produce a Galerkin sequence and weak subsequence package. -/
theorem dataGalerkin_limit_data {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    Nonempty (MolecularGalerkinLimitData a b hab P src F u₀) := by
  classical
  have hc := fun N => dataGalerkin_exists_bochner hab N P src F hsrcm hFm hsrc hF u₀
  choose y hy he hi hb using hc
  let U : ℕ → CellBochnerH1 a b := fun N => (hy N).toLp (fun t => (extendCurve hab (y N) t).val)
  let W := (b - a + 2) *
    ((‖u₀‖ ^ 2 + ∫ s in a..b, ‖cellSourceSlice src s‖ ^ 2 +
      4 * ∑ j, ‖cellSourceSlice (fun t x => F t x j) s‖ ^ 2) *
      Real.exp ((1 + 8 * P.V ^ 2) * (b - a)))
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

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Quantitative bounds for the fixed classical readout of a real cell trace. -/

def cellClassicalSobolevConstant (K n : ℕ) : ℝ :=
  classicalSobolevConstant n * ‖mapTorusHkCLM K Complex.reCLM‖

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Integrated fixed tests as continuous linear functionals on temporal H¹ classes. -/

/-- The integrated generator against a fixed H¹ test as a temporal continuous functional. -/
def dataGeneratorIntegralCLM (a b s t : ℝ)
    (P : MolecularData)
    (z : TorusHk 1 ℂ) :
    CellBochnerH1 a b →L[ℝ] ℝ :=
  cellTimeTestIntegralCLM a b s t (fun τ => dataGeneratorTest P τ z)
    (dataGeneratorTest_memLp a b P z)

/-- The generator functional evaluates to the literal fixed-test weak equation integral. -/
theorem dataGeneratorIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (P : MolecularData)
    (z : TorusHk 1 ℂ)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    dataGeneratorIntegralCLM a b s t P z (hu.toLp u) =
      ∫ r in s..t, dataGeneratorForm P r (u r) z := by
  rw [dataGeneratorIntegralCLM, cellTimeTestIntegralCLM_apply hs ht hst]
  exact intervalIntegral.integral_congr (fun r _ => dataGeneratorTest_pairing P r _ z)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Uniform classical spatial bounds retained by the canonical window readout. -/

theorem cellClassicalSobolevConstant_nonneg (K n : ℕ) :
    0 ≤ cellClassicalSobolevConstant K n := by
  unfold cellClassicalSobolevConstant classicalSobolevConstant
  positivity

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! First-derivative integration by parts against arbitrary periodic weak tests. -/

def complexClassicalScalarH1 (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic q) : TorusHk 1 ℂ :=
  TorusHkFunction.toHk ⟨mapRawJet Complex.ofRealCLM (cellSmoothScalarJet q),
    mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _ (classical_first_jet_periodicWeak q hq hp)⟩

theorem complexClassicalScalarH1_ae (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic q) (a : JetIndex2 1) :
    (complexClassicalScalarH1 q hq hp).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ((cellSmoothScalarJet q a x : ℝ) : ℂ) :=
  torusJetToL2_ae _ _ a

theorem classical_weak_first_ibp (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic q) (ψ : TorusHkFunction 1 ℂ) (i : Fin 2) :
    (∫ x in AVenhance.unitCube, (q x : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
      -∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
  let U := complexClassicalScalarH1 q hq hp
  let Z := cellH1Conj ψ.toHk
  have hZ (a : JetIndex2 1) : Z.val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (ψ.jet a x) :=
    (cellH1Conj_jet_ae ψ.toHk a).trans
      ((torusJetToL2_ae ψ.jet ψ.hasPeriodicWeakJet.2.1 a).fun_comp star)
  have hl : cellComplexPair (torusHkValueCLM U) (cellDerivativeCLM i Z) =
      ∫ x in AVenhance.unitCube, (q x : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x := by
    apply integral_congr_ae
    filter_upwards [complexClassicalScalarH1_ae q hq hp (valueIndex2 1),
      hZ ⟨⟨1, by decide⟩, fun _ => i⟩] with x hu hz
    change torusHkValueCLM U x = (q x : ℂ) at hu
    change cellDerivativeCLM i Z x = _ at hz
    rw [hu, hz, star_star]
  have hr : cellComplexPair (cellDerivativeCLM i U) (torusHkValueCLM Z) =
      ∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
    apply integral_congr_ae
    filter_upwards [complexClassicalScalarH1_ae q hq hp ⟨⟨1, by decide⟩, fun _ => i⟩,
      hZ (valueIndex2 1)] with x hu hz
    change cellDerivativeCLM i U x = ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) at hu
    change torusHkValueCLM Z x = _ at hz
    rw [hu, hz, star_star]
  rw [← hl, ← hr, AVRegularity.CycleDamping.weak_complex_derivative_pairing]
  exact (neg_neg _).symm

theorem classical_real_weak_first_ibp (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic q) (ψ : TorusHkFunction 1 ℝ) (i : Fin 2) :
    (∫ x in AVenhance.unitCube, q x * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
      -∫ x in AVenhance.unitCube, fderiv ℝ q x (basisVec i) * ψ.jet (valueIndex2 1) x := by
  let Ψ : TorusHkFunction 1 ℂ := ⟨mapRawJet Complex.ofRealCLM ψ.jet,
    mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _ ψ.hasPeriodicWeakJet⟩
  have h := classical_weak_first_ibp q hq hp Ψ i
  change (∫ x in AVenhance.unitCube, (q x : ℂ) * (ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x : ℂ)) =
      -∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * (ψ.jet (valueIndex2 1) x : ℂ) at h
  simp_rw [← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_neg] at h
  exact Complex.ofReal_injective h

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite-depth Jacobian production from primitive renewal-window estimates. -/

def WeakPrimitiveChartSmall (D : OCData) (base J : ℕ) (δ : ℝ) : Prop :=
  ∀ m ≥ base + 1,
    2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * (ocA D.α D.q D.Λ (m - 1))⁻¹ ∧
    2 ^ 23 * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
      ocA D.α D.q D.Λ (m - 1) ≤ δ ∧
    (4 * Real.pi ^ 2) * (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ m) *
      ocA D.α D.q D.Λ (m - 1) ≤ δ

theorem finite_weak_chart_bound_of_small_windows (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (base J : ℕ) (hbase : 1 ≤ base)
    (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild)
    (hp : ∀ n ≤ J, Odd (p n))
    (hs : ∀ n < J, IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n))
    (δ : ℝ) (hprimitive : WeakPrimitiveChartSmall D base J δ) :
    ∀ n ≤ J, ∀ u r,
      |u - D.slotAnchor (base + 1 + n) (p n)| ≤
        finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
      |r - D.slotAnchor (base + 1 + n) (p n)| ≤
        finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) →
      ∀ x, ‖fderiv ℝ (fun y => (finiteWeakChainGeom D base Y p c n).1 u y r) x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ finiteChartBudget n δ := by
  have hδp := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ := renewal_window_antitone (by linarith : D.α < 1) hδp.le hq.1 hΛ
  intro n
  induction n with
  | zero =>
    intro _ u r hu hr x
    have h0 := hprimitive (base + 1) le_rfl
    simp only [Nat.add_sub_cancel] at h0
    exact finite_weak_base_chart_close_of_small_window D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      base hbase Y p c (2 * (J : ℝ) + 1) δ h0.1 h0.2.1 u r hu hr x
  | succ n ih =>
    intro hn u r hu hr x
    let g := finiteWeakChainGeom D base Y p c n
    let h := ocTauPP D.α D.q D.Λ (base + 1 + n)
    let h' := ocTauPP D.α D.q D.Λ (base + 1 + (n + 1))
    let R := finiteChainWindowRadius J (n + 1)
    have hR : 0 ≤ R := finiteChainWindowRadius_nonneg _ _
    have hh : 0 ≤ h := (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ D.Λ)).le
    have hh' : h' ≤ h := hτ (by omega)
    have ha : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) - g.2.2| ≤ 2 * h := by
      have he := scheduled_anchor_distance D (by omega : 1 ≤ D.Λ) (base + 1 + n)
        (p (n + 1)) (p n) (hs n (by omega))
      rw [finiteWeakChainGeom_anchor] 
      have he' : |D.slotAnchor (base + 1 + (n + 1)) (p (n + 1)) -
          D.slotAnchor (base + 1 + n) (p n)| ≤ h' + h := by
        simpa only [h, h', Nat.add_assoc] using he
      exact he'.trans (by linarith)
    have hparent : ∀ u₀ r₀, |u₀ - g.2.2| ≤ (R + 2) * h →
        |r₀ - g.2.2| ≤ (R + 2) * h → ∀ x,
        ‖fderiv ℝ (fun y => g.1 u₀ y r₀) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
          finiteChartBudget n δ := by
      intro u₀ r₀ hu₀ hr₀ x₀
      rw [finiteWeakChainGeom_anchor] at hu₀ hr₀
      rw [← finiteChainWindowRadius_succ J n hn] at hu₀ hr₀
      exact ih (by omega) u₀ r₀ hu₀ hr₀ x₀
    have hb := child_window_operator_bound_of_parent_bound D (by omega : 1 ≤ D.Λ) hζ
      (base + 1 + n) (p n) (hp n (by omega))
      (D.slotAnchor (base + 1 + (n + 1)) (p (n + 1))) (c n) g
      (finiteWeakChainGeom_smooth D base Y p c n) h h' R (finiteChartBudget n δ)
      hh hh' hR ha hparent u r hu hr x
    have hsmall := (hprimitive (base + 1 + (n + 1)) (by omega)).2.2
    have hi : base + 1 + (n + 1) - 1 = base + 1 + n := by omega
    rw [hi] at hsmall
    have hA : 0 ≤ (4 * Real.pi ^ 2) * ocA D.α D.q D.Λ (base + 1 + n) := by
      unfold ocA
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Scales.epsilon_basic hq.1 hΛ).1.le _)
    have hhn : 0 ≤ h' := (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ D.Λ)).le
    have herror : (2 * R * h') * ((4 * Real.pi ^ 2) * ocA D.α D.q D.Λ (base + 1 + n)) ≤ δ := by
      calc
        _ ≤ (2 * (2 * (J : ℝ) + 1) * h') *
            ((4 * Real.pi ^ 2) * ocA D.α D.q D.Λ (base + 1 + n)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (finiteChainWindowRadius_le J (n + 1)) (by norm_num)) hhn) hA
        _ ≤ δ := by
          convert hsmall using 1
          dsimp [h']
          ring
    change ‖fderiv ℝ (fun y => (D.childGeom (base + 1 + n) (p n)
      (D.slotAnchor (base + 1 + (n + 1)) (p (n + 1))) (c n) g).1 u y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ _
    apply hb.trans
    simp only [finiteChartBudget]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (1 : ℝ)) herror) (sq_nonneg _)) 1

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Energy-small raw errors control the value of any genuine higher carrier. -/

theorem carrier_value_tendsto_zero_of_raw_energy {A : Type*} (l : Filter A)
    (K : ℕ) (w : A → TorusHk K ℂ) (D : A → ℝ → RawJet2 1 ℂ) (t : ℝ)
    (he : ∀ a, torusHkValueCLM (w a) =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (D a) t)
    (h : Tendsto (fun a => cellEnergyNorm univ (D a)) l (𝓝 0)) :
    Tendsto (fun a => (w a).val (valueIndex2 K)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs (a : A) : cellL2Norm (cellValue (D a) t) ≤ cellEnergyNorm univ (D a) := by
    change _ ≤ (⨆ s ∈ (univ : Set ℝ), cellL2Norm (cellValue (D a) s)) + _
    calc
      _ ≤ ⨆ s ∈ (univ : Set ℝ), cellL2Norm (cellValue (D a) s) :=
        le_iSup_of_le t (le_iSup_of_le (mem_univ t) le_rfl)
      _ ≤ _ := le_add_of_nonneg_right (bot_le : (0 : ENNReal) ≤ _)
  have hn : Tendsto (fun a => ENNReal.ofReal ‖(w a).val (valueIndex2 K)‖) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    intro a
    change ENNReal.ofReal ‖torusHkValueCLM (w a)‖ ≤ cellEnergyNorm univ (D a)
    rw [← cellL2Norm_eq_of_class _ _ (he a)]
    exact hs a
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hn
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_zero] using ht

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Smooth periodic divergence-free fields annihilate every weak periodic test. -/

theorem classical_divergence_free_weak (v : Vec 2 → Vec 2)
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i))
    (hp : ∀ i, AVenhance.IsZ2Periodic (fun x => v x i))
    (hd : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun z => v z i) x (basisVec i) = 0)
    (ψ : TorusHkFunction 1 ℝ) :
    (∫ x in AVenhance.unitCube, ∑ i : Fin 2,
      v x i * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) = 0 := by
  have hi (i : Fin 2) : Integrable (fun x => v x i *
      ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp
      ((AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On (hv i).continuous).mul
        (ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩) : MemLp _ 1 _)
  have hj (i : Fin 2) : Integrable (fun x => fderiv ℝ (fun z => v z i) x (basisVec i) *
      ψ.jet (valueIndex2 1) x) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp
      ((AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On
        (((hv i).continuous_fderiv (by simp)).clm_apply continuous_const)).mul
        (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1)) : MemLp _ 1 _)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [classical_real_weak_first_ibp _ (hv _) (hp _) ψ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hj i)]
  simp_rw [← Finset.sum_mul, hd, zero_mul]
  simp only [integral_zero, neg_zero]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Uniform higher carriers supply actual classical fast derivative and slice variation bounds. -/

theorem realHigherCarrier_derivative_norm_le (K n : ℕ) (hn : n + 2 ≤ K)
    (w : TorusHk K ℂ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM w)) z‖ ≤
      cellClassicalSobolevConstant K n * ‖w‖ := by
  have hb := realClassicalLift_derivative_norm_le K (mapTorusHk Complex.reCLM w) n hn z
  have hm : ‖mapTorusHk Complex.reCLM w‖ ≤ ‖mapTorusHkCLM K Complex.reCLM‖ * ‖w‖ := by
    simpa only [mapTorusHkCLM_apply] using (mapTorusHkCLM K Complex.reCLM).le_opNorm w
  have hc : 0 ≤ classicalSobolevConstant n := by unfold classicalSobolevConstant; positivity
  exact hb.trans ((mul_le_mul_of_nonneg_left hm hc).trans_eq (by
    dsimp only [cellClassicalSobolevConstant]
    ring))

theorem realHigherCarrier_fast_jet_lipschitz (K n : ℕ) (hn : n + 3 ≤ K)
    (w : TorusHk K ℂ) (z x : Vec 2) :
    ‖iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM w)) z -
      iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM w)) x‖ ≤
      (cellClassicalSobolevConstant K (n + 1) * ‖w‖) * ‖z - x‖ := by
  let f := realClassicalLift K (mapTorusHk Complex.reCLM w)
  have hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f :=
    realClassicalLift_contDiff K (n + 1) (by omega) _
  have hj : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  apply finite_parameter_lipschitz _ hj _ _ x z
  intro y
  rw [norm_fderiv_iteratedFDeriv]
  exact realHigherCarrier_derivative_norm_le K (n + 1) (by omega) w y

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Literal complex weak forms for an arbitrary bounded molecular matrix. -/

def dataCoefficients (P : MolecularData) : CellCoefficients :=
  molecularCoefficients P.G P.v

def dataMetricEntryCLM (P : MolecularData) (t : ℝ) (j k : Fin 2) :
    ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  P.G t j k • ContinuousLinearMap.id ℝ ComplexCellL2

theorem dataMetricEntryCLM_ae (P : MolecularData) (t : ℝ) (j k : Fin 2)
    (u : ComplexCellL2) :
    dataMetricEntryCLM P t j k u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (P.G t j k : ℂ) * u x := by
  change (P.G t j k • u : ComplexCellL2) =ᵐ[volume.restrict AVenhance.unitCube] _
  filter_upwards [Lp.coeFn_smul (P.G t j k) u] with x hx
  simpa only [Pi.smul_apply, Complex.real_smul] using hx

def dataComplexGenerator (P : MolecularData) (t : ℝ) (u z : TorusHk 1 ℂ) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair
    (dataMetricEntryCLM P t j k (cellDerivativeCLM j u)) (cellDerivativeCLM k z)) -
  ∑ j : Fin 2, cellComplexPair
    (cellDriftEntryCLM (molecularCoefficients P.G P.v) P.V P.drift_measurable
      P.drift_bounded t j (cellDerivativeCLM j u)) (torusHkValueCLM z)

theorem dataComplexGenerator_re (P : MolecularData) (t : ℝ) (u z : TorusHk 1 ℂ) :
    (dataComplexGenerator P t u z).re = dataGeneratorForm P t u z := by
  simp only [dataComplexGenerator, dataGeneratorForm, molecularGeneratorForm,
    molecularDiffusionForm, dataMetricEntryCLM, Fin.sum_univ_two, Complex.sub_re,
    Complex.neg_re, Complex.add_re, cellComplexPair_re, add_apply, sub_apply,
    neg_apply, smul_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_left, smul_eq_mul]

theorem dataComplexGenerator_im (P : MolecularData) (t : ℝ) (u z : TorusHk 1 ℂ) :
    (dataComplexGenerator P t u z).im =
      dataGeneratorForm P t u (cellH1Scalar Complex.I z) := by
  simp only [dataComplexGenerator, dataGeneratorForm, molecularGeneratorForm,
    molecularDiffusionForm, dataMetricEntryCLM, Fin.sum_univ_two, Complex.sub_im,
    Complex.neg_im, Complex.add_im, cellComplexPair_im, add_apply, sub_apply,
    neg_apply, smul_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_left, smul_eq_mul,
    cellH1Scalar_value, cellH1Scalar_derivative]

theorem dataDualComplexPair_actual (P : MolecularData) (t : ℝ) (u z : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (dataDualDerivative P t u S F) z =
      dataComplexGenerator P t u z + cellComplexSource 0 S F z := by
  apply Complex.ext
  · rw [cellDualComplexPair_re, Complex.add_re, dataComplexGenerator_re,
      cellComplexSource_re, dataDualDerivative_pairing]
  · rw [cellDualComplexPair_im, Complex.add_im, dataComplexGenerator_im,
      cellComplexSource_im, dataDualDerivative_pairing]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Uniform operator bounds for temporal fixed-test integrals. -/

/-- Actual fixed-test generator integrals have an operator bound linear in the test norm. -/
theorem dataGeneratorIntegralCLM_uniform_norm_bound {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t z,
      ‖dataGeneratorIntegralCLM a b s t P z‖ ≤ L * ‖z‖ := by
  obtain ⟨M, hM, hMb⟩ := dataGeneratorForm_uniform_norm_bound P
  refine ⟨(b - a + 1) * M, mul_nonneg (by linarith) hM, fun s t z => ?_⟩
  have hi := cellTimeTestIntegralCLM_norm_le hab s t
    (fun r => dataGeneratorTest P r z)
    (dataGeneratorTest_memLp a b P z) (M * ‖z‖)
    (mul_nonneg hM (norm_nonneg _))
    (fun r => dataGeneratorTest_norm_le_of_bound P M hM hMb r z)
  simpa only [dataGeneratorIntegralCLM, mul_assoc] using hi

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Primitive short-window estimates control the physical shear displacement. -/

theorem four_pi_sq_ge_one : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
  have hp : 1 ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
  calc
    1 ≤ Real.pi ^ 2 := one_le_pow₀ hp
    _ ≤ 4 * Real.pi ^ 2 := le_mul_of_one_le_left (by positivity) (by norm_num)

theorem primitive_shear_window_bound (D : OCData) (hΛ : 1 ≤ D.Λ) (base J : ℕ)
    (hprimitive : WeakPrimitiveChartSmall D base J 1) (n : ℕ) :
    (2 * finiteChainWindowRadius J (n + 1) *
      ocTauPP D.α D.q D.Λ (base + 1 + (n + 1))) *
      ocA D.α D.q D.Λ (base + 1 + n) ≤ 1 := by
  have h := (hprimitive (base + 1 + (n + 1)) (by omega)).2.2
  have hi : base + 1 + (n + 1) - 1 = base + 1 + n := by omega
  rw [hi] at h
  have hτ : 0 ≤ ocTauPP D.α D.q D.Λ (base + 1 + (n + 1)) :=
    (Construction.Stream.ocTauPP_pos hΛ).le
  have hA : 0 ≤ ocA D.α D.q D.Λ (base + 1 + n) := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  calc
    _ ≤ (2 * (2 * (J : ℝ) + 1) * ocTauPP D.α D.q D.Λ (base + 1 + (n + 1))) *
        ocA D.α D.q D.Λ (base + 1 + n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (finiteChainWindowRadius_le J (n + 1)) (by norm_num)) hτ) hA
    _ ≤ (4 * Real.pi ^ 2) * ((2 * (2 * (J : ℝ) + 1) *
        ocTauPP D.α D.q D.Λ (base + 1 + (n + 1))) * ocA D.α D.q D.Λ (base + 1 + n)) :=
      le_mul_of_one_le_left (by positivity) four_pi_sq_ge_one
    _ ≤ 1 := by
      convert h using 1
      ring

end AVRegularity.EntryWeakProofs
end
