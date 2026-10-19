-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentCarrierCoefficientCopyOn
import AVRegularity.CycleComparison.Lift.SettingInverseZero
public import AVRegularity.EntryWeak.ChildOperatorCloseness
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
public import AVRegularity.EntryWeak.WeakRelativeDisplacementAllJets
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleJoint.PlaneWeakCurveCongruenceOn
import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Smooth local edge extensions preserve the actual carrier-local cell inverse. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem local_lift_inverse_edge_replacement {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (edge : ConstituentEdges D h)
    (a b : ℝ) (sZ hh n : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (Y : Vec 2) (hY : Y ∈ U)
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq U t Q.edge edge)
    (hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => liftCellSource Q Cc f hh n t Y z)
      (fun t z => liftApply n (Cc hh n) f t Y z)) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => liftCellSource {Q with edge := edge} Cc f hh n t Y z)
      (fun t z => liftApply n (Cc hh n) f t Y z) := by
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hc
  intro t ht
  funext z
  exact liftCellSource_edge_slow_open_congr hU Q edge Cc f hh n t (he t ht) Y hY z

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs

/-! A genuine metric germ on an open slow carrier preserves the original native inverse. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem local_lift_inverse_metric_carrier_replacement {U : Set (Vec 2)} (hU : IsOpen U)
    (Q : LiftOperatorData ι h D) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (a b : ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ X ∈ U, Q.G t X = G t X)
    (sZ hh n : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (Y : Vec 2) (hY : Y ∈ U)
    (hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => liftCellSource Q Cc f hh n t Y z)
      (fun t z => liftApply n (Cc hh n) f t Y z)) :
    IsCellFieldInverse (fun t => Matrix.of (G t Y)) Q.v sZ a b 0
      (fun t z => liftCellSource {Q with G := G} Cc f hh n t Y z)
      (fun t z => liftApply n (Cc hh n) f t Y z) := by
  have hc' := cellFieldInverse_coefficients_congr_on
    (fun t => Matrix.of (Q.G t Y)) (fun t => Matrix.of (G t Y)) Q.v Q.v sZ a b 0 _ _
    (fun t ht => congrArg Matrix.of (hG t ht Y hY)) (fun _ _ => rfl) hc
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hc'
  intro t ht
  funext z
  exact liftCellSource_metric_slow_open_congr hU Q G Cc f hh n t (hG t ht) Y hY z

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Carrier coefficient extension preserves the native inverse, including the centered ordered corrections. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

theorem independentCarrierCoefficientExtension_inverse (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d) (hP : P ∈ V)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (hc : IsLiftSequence Q sX sZ a b N R (c P)) (hh n : ℕ) (hhh : hh ≤ R)
    (hn : 1 ≤ n) (hnN : n ≤ N) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => liftCellSource Q (independentCarrierCoefficientExtension V c P) (fun _ => f) hh n t X z)
      (fun t z => liftApply n (independentCarrierCoefficientExtension V c P hh n) (fun _ => f) t X z) := by
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X
  have hcn : independentCarrierCoefficientExtension V c P hh n = c P hh n := by
    simp only [independentCarrierCoefficientExtension, ite_eq_right (by omega : n ≠ 0), ite_eq_left hP]
  rw [hcn]
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t ht
  funext z
  exact liftCellSource_slow_open_congr_predecessors isOpen_univ Q (c P)
    (independentCarrierCoefficientExtension V c P) (fun _ => f) hh n hn t (by
      intro p q hpq m _hm α Y _hY z v u
      have hpR : p ≤ R := by rcases hpq with hpq | ⟨rfl, _⟩ <;> omega
      exact (independentCarrierCoefficientExtension_copy V c P hP Q hc p hpR q m α t ht Y z v u).symm)
    X (mem_univ X) z

end AVRegularity.EntryWeakProofs
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational AVRegularity.Weighted
namespace AVRegularity.EntryWeakProofs

/-! The molecular flux carrier has exactly the differentiated matrix energy pairing. -/

theorem molecularMetric_L2_pairing (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (w : Lp (PiLp 2 (fun _ : Fin 2 => ℂ)) 2 (volume.restrict AVenhance.unitCube)) :
    inner ℝ ((metricFiberCoefficient (Matrix.transpose (G t))).compLpL
      2 (volume.restrict AVenhance.unitCube) w) w =
    molecularVectorEnergy G t (fun k => (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : Fin 2 => ℂ) k).compLpL 2 (volume.restrict AVenhance.unitCube) w) := by
  let q := fun k : Fin 2 => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).compLpL
    2 (volume.restrict AVenhance.unitCube) w
  let f := fun j k x => G t j k * inner ℝ (q j x) (q k x)
  have hf j k : Integrable (f j k) (volume.restrict AVenhance.unitCube) :=
    (L2.integrable_inner (𝕜 := ℝ) (q j) (q k)).const_mul _
  have hs j : Integrable (fun x => ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hf j k)
  have hr : molecularVectorEnergy G t q =
      ∫ x in AVenhance.unitCube, ∑ j : Fin 2, ∑ k : Fin 2, f j k x := by
    rw [integral_finsetSum Finset.univ (fun j _ => hs j)]
    unfold molecularVectorEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => hf j k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [L2.inner_def, ← integral_const_mul]
  rw [L2.inner_def, hr]
  apply integral_congr_ae
  have hq := ae_all_iff.mpr (fun k : Fin 2 =>
    ContinuousLinearMap.coeFn_compLpL (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k) w)
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (metricFiberCoefficient (E := ℂ) (Matrix.transpose (G t))) w, hq] with x hx hqx
  rw [hx, metricFiberCoefficient_apply]
  simp only [PiLp.inner_apply, finiteMetricFlux, sum_inner, real_inner_smul_left,
    Matrix.transpose_apply, f, q, hqx]
  exact Finset.sum_comm

theorem molecularMetric_factorial_pairing (K : ℕ) (ρ : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (w : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ))) :
    inner ℝ (factorialWeightedJet ρ
      (mapTorusHkCLM K (metricFiberCoefficient (Matrix.transpose (G t))) w).val)
      (factorialWeightedJet ρ w.val) = dataHigherDiffusion K ρ G t w := by
  rw [factorialWeightedJet_inner]
  unfold dataHigherDiffusion
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp]
  exact molecularMetric_L2_pairing G t _

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Read the existing molecular Galerkin curve in the proved plain Fourier coordinates. -/

abbrev MolecularPlainCoefficients (N : ℕ) := CoupledPlainCoefficients (h := fun _ : Unit => ℂ) N

def dataFourierCoordinatesCLM (N : ℕ) : ComplexCellL2 →L[ℝ] MolecularPlainCoefficients N :=
  ContinuousLinearMap.pi (fun r => innerSL ℝ (plainModeCellLp N r Unit.unit 0 Fin.elim0))

theorem dataFourierCoordinates_eq_initial (N : ℕ) (u : TorusHk 1 ℂ) :
    dataFourierCoordinatesCLM N (torusHkValueCLM u) =
      plainInitialCoefficients N (fun _ : Unit => 1) (fun _ => u) := by
  funext r
  rw [plainInitialCoefficients_component]
  simp only [dataFourierCoordinatesCLM, ContinuousLinearMap.pi_apply, innerSL_apply_apply,
    plainValueForcingCLM, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]

def dataPlainSynthesisCLM (N K : ℕ) : MolecularPlainCoefficients N →L[ℝ] TorusHk K ℂ :=
  ∑ r, (ContinuousLinearMap.proj r).smulRight (coupledModeHk N r Unit.unit K)

theorem dataPlainSynthesisCLM_apply (N K : ℕ) (c : MolecularPlainCoefficients N) :
    dataPlainSynthesisCLM N K c = coupledPlainSynthesis N Unit.unit K c := by
  simp [dataPlainSynthesisCLM, coupledPlainSynthesis]

def dataFourierHighCLM (N K : ℕ) : ComplexCellL2 →L[ℝ] TorusHk K ℂ :=
  (dataPlainSynthesisCLM N K).comp (dataFourierCoordinatesCLM N)

theorem dataFourierHigh_one (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    dataFourierHighCLM N 1 (cellGalerkinValue N u) = u.val := by
  change dataPlainSynthesisCLM N 1 (dataFourierCoordinatesCLM N (torusHkValueCLM u.val)) = _
  rw [dataPlainSynthesisCLM_apply, dataFourierCoordinates_eq_initial]
  calc
    _ = galerkinProj N u.val := plainInitialCoefficients_synthesis N
      (fun _ : Unit => 1) (fun _ => u.val) Unit.unit
    _ = u.val := by
      rcases u.property with ⟨v, hv⟩
      rw [← hv]
      exact galerkinProj_idempotent N v

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The three maps in a child chart propagate a finite positive-jet budget. -/

theorem child_chart_positive_jet_bound_of_component_bounds
    (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ) (c : ChainChild) (g : ChainGeom)
    (hg : GeomSpatialSmooth g) (u r ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hleft : ∀ n, 1 ≤ n → n ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ n (rescaledChart ρ (fun y => g.1 u y g.2.2)) x‖ ≤ B)
    (hmiddle : ∀ n, 1 ≤ n → n ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ n (rescaledChart ρ (childShearMap D k pk u r c g)) x‖ ≤ B)
    (hright : ∀ n, 1 ≤ n → n ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ n (rescaledChart ρ (fun y => g.1 g.2.2 y r)) x‖ ≤ B)
    (n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n
      (rescaledChart ρ (fun y => (D.childGeom k pk s' c g).1 u y r)) x‖ ≤
      positiveJetCompositionBudget K (positiveJetCompositionBudget K B) := by
  let F := rescaledChart ρ (fun y => g.1 u y g.2.2)
  let S := rescaledChart ρ (childShearMap D k pk u r c g)
  let P := rescaledChart ρ (fun y => g.1 g.2.2 y r)
  have hF := rescaledChart_smooth ρ _ (hg u g.2.2)
  have hS := rescaledChart_smooth ρ _ (childShearMap_spatial_smooth D k pk u r c g)
  have hP := rescaledChart_smooth ρ _ (hg g.2.2 r)
  have hSP (j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K) (z : Vec 2) :
      ‖iteratedFDeriv ℝ j (S ∘ P) z‖ ≤ positiveJetCompositionBudget K B :=
    finite_positive_jet_composition_bound S P hS hP K j hj hjK z B hB
      (fun a ha haK => hmiddle a ha haK _) (fun a ha haK => hright a ha haK _)
  have hmap : (fun y => (D.childGeom k pk s' c g).1 u y r) =
      (fun y => g.1 u y g.2.2) ∘
        (childShearMap D k pk u r c g ∘ fun y => g.1 g.2.2 y r) := rfl
  rw [hmap, rescaledChart_comp ρ hρ, rescaledChart_comp ρ hρ]
  exact finite_positive_jet_composition_bound F (S ∘ P) hF (hS.comp hP) K n hn hnK x
    (positiveJetCompositionBudget K B) (positiveJetCompositionBudget_ge_one K B hB)
    (fun j hj hjK => (hleft j hj hjK _).trans (positiveJetCompositionBudget_ge_self K B hB))
    (fun j hj hjK => hSP j hj hjK _)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The high readout of the molecular initial cutoff is its high Sobolev projection. -/

theorem dataFourierCoordinates_eq_initial_high (N K : ℕ) (u : TorusHk K ℂ) :
    dataFourierCoordinatesCLM N (torusHkValueCLM u) =
      plainInitialCoefficients N (fun _ : Unit => K) (fun _ => u) := by
  funext r
  rw [plainInitialCoefficients_component]
  simp only [dataFourierCoordinatesCLM, ContinuousLinearMap.pi_apply, innerSL_apply_apply,
    plainValueForcingCLM, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]

theorem dataFourierHigh_eq_projection (N K : ℕ) (u : TorusHk K ℂ) :
    dataFourierHighCLM N K (torusHkValueCLM u) = galerkinProj N u := by
  simp only [dataFourierHighCLM, ContinuousLinearMap.comp_apply,
    dataPlainSynthesisCLM_apply, dataFourierCoordinates_eq_initial_high]
  exact plainInitialCoefficients_synthesis N (fun _ : Unit => K) (fun _ => u) Unit.unit

theorem dataFourierHigh_initial (N K : ℕ) (u : TorusHk K ℂ) :
    dataFourierHighCLM N K (cellGalerkinValue N (cellGalerkinL2Initial N (torusHkValueCLM u))) =
      galerkinProj N u := by
  rw [cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]
  change dataFourierHighCLM N K (torusHkValueCLM (galerkinProj N u)) = _
  rw [dataFourierHigh_eq_projection, galerkinProj_idempotent]

theorem dataFourierHigh_initial_factorial_le (N K : ℕ) (ρ : ℝ) (u : TorusHk K ℂ) :
    factorialNormSq ρ (dataFourierHighCLM N K
      (cellGalerkinValue N (cellGalerkinL2Initial N (torusHkValueCLM u)))).val ≤
      factorialNormSq ρ u.val := by
  rw [dataFourierHigh_initial]
  exact galerkinProj_factorialNormSq_le N ρ u

/-! Higher Fourier readouts retain the exact finite L² trace. -/

theorem dataFourierHigh_value_order (N K L : ℕ) (u : ComplexCellL2) :
    torusHkValueCLM (dataFourierHighCLM N K u) =
      torusHkValueCLM (dataFourierHighCLM N L u) := by
  simp only [dataFourierHighCLM, ContinuousLinearMap.comp_apply,
    dataPlainSynthesisCLM_apply, coupledPlainSynthesis_apply, map_sum, map_smul]
  rfl

theorem dataFourierHigh_value (N K : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    torusHkValueCLM (dataFourierHighCLM N K (cellGalerkinValue N u)) = cellGalerkinValue N u := by
  rw [dataFourierHigh_value_order N K 1, dataFourierHigh_one]
  rfl

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Higher Sobolev traces are measurable through their finite Fourier cutoffs. -/

theorem higherTrace_stronglyMeasurable {A : Type*} [MeasurableSpace A]
    (K : ℕ) (u : A → ComplexCellL2) (hu : StronglyMeasurable u)
    (w : A → TorusHk K ℂ) (hw : ∀ a, torusHkValueCLM (w a) = u a) :
    StronglyMeasurable w := by
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun N a => dataFourierHighCLM N K (u a))
  · intro N
    exact (dataFourierHighCLM N K).continuous.comp_stronglyMeasurable hu
  · apply tendsto_pi_nhds.2
    intro a
    simp_rw [← hw a, dataFourierHigh_eq_projection]
    exact galerkinProj_tendsto (w a)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The coupled fast/slow shear has uniformly bounded positive joint jets. -/

def weakTransferJointShearCost (K : ℕ) : ℝ :=
  1 + positiveJetCompositionBudget K (max ((2 * Real.pi) ^ (K + 1)) 2)

theorem weak_transfer_joint_shear_positive_jets (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (X : Vec 2 × Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 =>
      Z.2 + D.relDisp m slot u r (Z.1 + Z.2)) X‖ ≤ weakTransferJointShearCost K := by
  let L : (Vec 2 × Vec 2) →L[ℝ] Vec 2 :=
    ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2) + ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)
  let P : (Vec 2 × Vec 2) →L[ℝ] Vec 2 := ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)
  have hL : ‖L‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro Y
    change ‖Y.1 + Y.2‖ ≤ 2 * ‖Y‖
    exact (norm_add_le _ _).trans ((add_le_add (norm_fst_le Y) (norm_snd_le Y)).trans_eq (by ring))
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.2‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_snd_le Y
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  let B := max ((2 * Real.pi) ^ (K + 1)) 2
  have hB : 1 ≤ B := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right _ _)
  have hδ (a : ℕ) (ha : 1 ≤ a) (haK : a ≤ K) (y : Vec 2) :
      ‖iteratedFDeriv ℝ a (D.relDisp m slot u r) y‖ ≤ B := by
    have hh := weak_relative_displacement_positive_jet_bound D hΛ hζ m slot hp u r a ha y
    have hc : |u - r| * (2 * Real.pi) ^ (a + 1) * ocA D.α D.q D.Λ m ≤
        (2 * Real.pi) ^ (a + 1) := by
      calc
        _ = (2 * Real.pi) ^ (a + 1) * (|u - r| * ocA D.α D.q D.Λ m) := by ring
        _ ≤ (2 * Real.pi) ^ (a + 1) * 1 := mul_le_mul_of_nonneg_left hsmall
          (pow_nonneg (zero_le_one.trans hpi) (a + 1))
        _ = _ := mul_one _
    exact (hh.trans hc).trans ((pow_le_pow_right₀ hpi (by omega)).trans (le_max_left _ _))
  have hcomp : ‖iteratedFDeriv ℝ n ((D.relDisp m slot u r) ∘ L) X‖ ≤
      positiveJetCompositionBudget K B :=
    finite_positive_jet_composition_bound _ L (relDisp_spatial_smooth D m slot u r)
      L.contDiff K n hn hnK X B hB
      (fun a ha haK => hδ a ha haK _)
      (fun a ha _ => (linear_positive_derivative_norm_le L a ha X).trans
        (hL.trans (le_max_right _ _)))
  change ‖iteratedFDeriv ℝ n ((fun Z => P Z) + (D.relDisp m slot u r) ∘ L) X‖ ≤ _
  have hPn : ContDiff ℝ (n : ℕ∞) P := P.contDiff
  rw [iteratedFDeriv_add_apply hPn.contDiffAt
    (((relDisp_spatial_smooth D m slot u r).comp L.contDiff).contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add
    ((linear_positive_derivative_norm_le P n hn X).trans hP) hcomp)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! A bounded higher trace on a measurable window gives a genuine higher Bochner carrier. -/

theorem higherWindowCarrier_exists {A : Type*} [MeasurableSpace A]
    (K : ℕ) (I : Set A) (hI : MeasurableSet I) (u : A → ComplexCellL2)
    (hu : StronglyMeasurable u) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ a ∈ I, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u a ∧ ‖w‖ ≤ R) :
    ∃ w : A → TorusHk K ℂ, StronglyMeasurable w ∧
      (∀ a, torusHkValueCLM (w a) = I.indicator u a) ∧ (∀ a, ‖w a‖ ≤ R) := by
  classical
  let w := fun a => if h : a ∈ I then Classical.choose (hw a h) else 0
  have he (a : A) : torusHkValueCLM (w a) = I.indicator u a := by
    by_cases ha : a ∈ I
    · simp only [w, dite_eq_left ha, indicator_of_mem ha]
      exact (Classical.choose_spec (hw a ha)).1
    · simp only [w, dite_eq_right ha, map_zero, indicator_of_notMem ha]
  refine ⟨w, higherTrace_stronglyMeasurable K (I.indicator u) (hu.indicator hI) w he, he, ?_⟩
  intro a
  by_cases ha : a ∈ I
  · simpa only [w, dite_eq_left ha] using (Classical.choose_spec (hw a ha)).2
  · simpa only [w, dite_eq_right ha, norm_zero] using hR

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Bounded higher Sobolev approximants identify a higher trace from all H¹ moments. -/

theorem cellL2_eq_of_H1_moments (u v : ComplexCellL2)
    (h : ∀ z : TorusHk 1 ℂ, inner ℝ u (torusHkValueCLM z) = inner ℝ v (torusHkValueCLM z)) :
    u = v := by
  apply ext_inner_right ℝ
  intro z
  have ht := cellGalerkinL2Initial_tendsto z
  have hu := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := u)) ht
  have hv := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v)) ht
  have he : (fun N => inner ℝ u (cellGalerkinValue N (cellGalerkinL2Initial N z))) =
      (fun N => inner ℝ v (cellGalerkinValue N (cellGalerkinL2Initial N z))) := by
    funext N
    exact h (cellGalerkinL2Initial N z).val
  rw [he] at hu
  exact tendsto_nhds_unique hu hv

theorem higherTrace_exists_of_bounded_moments (K : ℕ) (v : ℕ → TorusHk K ℂ)
    (u : ComplexCellL2) (R : ℝ) (hv : ∀ n, ‖v n‖ ≤ R)
    (hm : ∀ z : TorusHk 1 ℂ, Tendsto
      (fun n => inner ℝ (torusHkValueCLM (v n)) (torusHkValueCLM z)) atTop
      (𝓝 (inner ℝ u (torusHkValueCLM z)))) :
    ∃ w : TorusHk K ℂ, torusHkValueCLM w = u := by
  let : TopologicalSpace.SeparableSpace (TorusHk K ℂ) :=
    AVRegularity.CoupledEnergy.Variational.torusHkSeparableSpace K
  obtain ⟨w, φ, hφ, hw⟩ := cellHilbert_weak_subsequence_clm v R hv
  refine ⟨w, cellL2_eq_of_H1_moments _ _ (fun z => ?_)⟩
  let L := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (K := K) (E := ℂ))
  have hl := hw L
  have hh := (hm z).comp hφ.tendsto_atTop
  have hll : Tendsto (fun n => inner ℝ (torusHkValueCLM (v (φ n))) (torusHkValueCLM z))
      atTop (𝓝 (inner ℝ (torusHkValueCLM w) (torusHkValueCLM z))) := by
    have he (q : TorusHk K ℂ) : L q = inner ℝ (torusHkValueCLM q) (torusHkValueCLM z) := by
      change inner ℝ (torusHkValueCLM z) (torusHkValueCLM q) = _
      exact real_inner_comm _ _
    simp only [he] at hl
    exact hl
  exact tendsto_nhds_unique hll hh

/-! Weak higher Sobolev trace extraction retains the uniform norm bound. -/

theorem weakHilbertLimit_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℕ → H) (w : H) (R : ℝ)
    (hv : ∀ n, ‖v n‖ ≤ R)
    (hw : ∀ L : H →L[ℝ] ℝ, Tendsto (fun n => L (v n)) atTop (𝓝 (L w))) :
    ‖w‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg (v 0)).trans (hv 0)
  have ht := hw (innerSL ℝ w)
  have hh : inner ℝ w w ≤ ‖w‖ * R := le_of_tendsto ht
    (Filter.Eventually.of_forall fun n =>
      (real_inner_le_norm w (v n)).trans (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg w)))
  rw [real_inner_self_eq_norm_sq] at hh
  rcases eq_or_lt_of_le (norm_nonneg w) with hz | hp
  · linarith
  · nlinarith

theorem higherTrace_exists_bounded (K : ℕ) (v : ℕ → TorusHk K ℂ)
    (u : ComplexCellL2) (R : ℝ) (hv : ∀ n, ‖v n‖ ≤ R)
    (hm : ∀ z : TorusHk 1 ℂ, Tendsto
      (fun n => inner ℝ (torusHkValueCLM (v n)) (torusHkValueCLM z)) atTop
      (𝓝 (inner ℝ u (torusHkValueCLM z)))) :
    ∃ w : TorusHk K ℂ, torusHkValueCLM w = u ∧ ‖w‖ ≤ R := by
  let : TopologicalSpace.SeparableSpace (TorusHk K ℂ) :=
    AVRegularity.CoupledEnergy.Variational.torusHkSeparableSpace K
  obtain ⟨w, φ, hφ, hw⟩ := cellHilbert_weak_subsequence_clm v R hv
  refine ⟨w, cellL2_eq_of_H1_moments _ _ (fun z => ?_),
    weakHilbertLimit_norm_le (fun n => v (φ n)) w R (fun n => hv (φ n)) hw⟩
  let L := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (K := K) (E := ℂ))
  have hl := hw L
  have hh := (hm z).comp hφ.tendsto_atTop
  have he (q : TorusHk K ℂ) : L q = inner ℝ (torusHkValueCLM q) (torusHkValueCLM z) := by
    change inner ℝ (torusHkValueCLM z) (torusHkValueCLM q) = _
    exact real_inner_comm _ _
  simp only [he] at hl
  exact tendsto_nhds_unique hl hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! Every finite fast derivative budget of the actual pulse is linear in its Péclet amplitude. -/

def pulseFastDerivativeConstant (K : ℕ) : ℝ := (2 * Real.pi) * (2 * Real.pi) ^ K

theorem pulseFastDerivativeConstant_nonneg (K : ℕ) : 0 ≤ pulseFastDerivativeConstant K := by
  unfold pulseFastDerivativeConstant
  positivity

private theorem pulseCosine_budget (K n : ℕ) (hn : n ≤ K) (Pe c : ℝ)
    (hPe : 0 ≤ Pe) (hc : |c| ≤ Pe * (2 * Real.pi)) (i : Fin 2) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => c * Real.cos (2 * Real.pi * y i)) z‖ ≤
      Pe * pulseFastDerivativeConstant K := by
  have hh := cosine_coordinate_derivative_norm_le c (2 * Real.pi) (by positivity) i n z
  have hp := pow_le_pow_right₀ (by linarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi) hn
  exact hh.trans ((mul_le_mul hc hp (by positivity) (mul_nonneg hPe (by positivity))).trans_eq
    (by unfold pulseFastDerivativeConstant; ring))

theorem normalizedPulseDrift_fast_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) (K n : ℕ) (hn : n ≤ K) (s : ℝ) (z : Vec 2) (i : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y => ocPulseCellDrift α q Λ ζ m ν k s y i) z‖ ≤
      (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant K := by
  let Pe := ocEpsilon q Λ m ^ (1 + α) / ν
  let c := Pe * (2 * Real.pi * ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s))
  have hPe : 0 ≤ Pe := div_nonneg (Real.rpow_nonneg
    (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le
  have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k
    (ocEll q Λ m ν ^ 2 * s)
  have hc : |c| ≤ Pe * (2 * Real.pi) := by
    dsimp only [c]
    rw [abs_mul, abs_of_nonneg hPe, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      abs_of_nonneg hp.1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * Real.pi) hp.2) hPe
  have hz : ‖iteratedFDeriv ℝ n (fun _ : Vec 2 => (0 : ℝ)) z‖ ≤
      Pe * pulseFastDerivativeConstant K := by
    simpa only [zero_mul] using pulseCosine_budget K n hn Pe 0 hPe
      (by simpa using mul_nonneg hPe (by positivity : 0 ≤ 2 * Real.pi)) 0 z
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · have hv : ocPulseCellDrift α q Λ ζ m ν k s =
        fun y => ![0, c * Real.cos (2 * Real.pi * y 0)] :=
      funext (fun y => normalizedPulseDrift_horizontal hΛ hν h1 s y)
    rw [hv]
    fin_cases i
    · exact hz
    · exact pulseCosine_budget K n hn Pe c hPe hc 0 z
  · have hv : ocPulseCellDrift α q Λ ζ m ν k s =
        fun y => ![-(c * Real.cos (2 * Real.pi * y 1)), 0] :=
      funext (fun y => normalizedPulseDrift_vertical hΛ hν h3 s y)
    rw [hv]
    fin_cases i
    · change ‖iteratedFDeriv ℝ n (fun y : Vec 2 => -(c * Real.cos (2 * Real.pi * y 1))) z‖ ≤
        Pe * pulseFastDerivativeConstant K
      have hh := pulseCosine_budget K n hn Pe (-c) hPe (by simpa only [abs_neg] using hc) 1 z
      simpa only [neg_mul] using hh
    · exact hz

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! A bundle of the actual coefficient premises for the molecular weak-limit adapter. -/

structure MolecularData where
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  v : ℝ → Vec 2 → Vec 2
  CG : ℝ
  V : ℝ
  metric_measurable : ∀ i j, Measurable (fun t => G t i j)
  metric_bounded : ∀ t i j, |G t i j| ≤ CG
  metric_coercive : ∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤
    ∑ i, ∑ j, G t i j * k i * k j
  drift_measurable : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)
  drift_bounded : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2

def dataGeneratorForm (P : MolecularData) :=
  molecularGeneratorForm P.G P.v P.V P.drift_measurable P.drift_bounded

def dataGeneratorB (P : MolecularData) :=
  molecularGeneratorB P.G P.v P.V P.drift_measurable P.drift_bounded

theorem dataGeneratorForm_pairing_stronglyMeasurable (P : MolecularData)
    (u z : TorusHk 1 ℂ) : StronglyMeasurable (fun t => dataGeneratorForm P t u z) :=
  molecularGeneratorForm_pairing_stronglyMeasurable P.G P.v P.V
    P.metric_measurable P.drift_measurable P.drift_bounded u z

theorem dataGeneratorForm_uniform_norm_bound (P : MolecularData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u, ‖dataGeneratorForm P t u‖ ≤ M * ‖u‖ :=
  molecularGeneratorForm_uniform_norm_bound P.G P.v P.CG P.V
    P.metric_bounded P.drift_measurable P.drift_bounded

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The H¹ Riesz representative of the actual H⁻¹ cell time derivative. -/

/-- Riesz representation of the generator plus scalar/divergence forcing. -/
def dataDualDerivative (P : MolecularData)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm
    (dataGeneratorForm P t u + cellSourceFunctional 0 S F)

/-- The Riesz derivative has exactly the actual weak form pairing. -/
theorem dataDualDerivative_pairing (P : MolecularData)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    inner ℝ (dataDualDerivative P t u S F) z =
      dataGeneratorForm P t u z + cellSourceFunctional 0 S F z := by
  exact InnerProductSpace.toDual_symm_apply

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! A uniform-in-time finite cell L² bound derived from the actual energy estimate. -/

/-- The finite cell energy inequality implies an L² bound uniform on the time interval. -/
theorem dataFinite_energy_sup_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (P : MolecularData)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (dataGeneratorB P t))
      (fun t => cellGalerkinSource N (cellSourceFunctional 0 (S t) (F t)).toLinearMap)
      u du y) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2) *
        Real.exp ((1 + 8 * P.V ^ 2) * (b - a)) := by
  let R := (1 + 8 * P.V ^ 2)
  let budget := ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hbudget : 0 ≤ budget := by
    have hi : 0 ≤ ∫ s in a..b, ‖S s‖ ^ 2 + 4 * ∑ j, ‖F s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => by positivity)
    exact add_nonneg (sq_nonneg _) hi
  have he := molecularFinite_energy_bound hab N P.G P.v P.V P.metric_coercive P.drift_measurable P.drift_bounded S F hS hF u du y hy h
  intro t ht
  have het := he t ht
  have hd : 0 ≤ ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => by positivity)
  have hex : Real.exp (R * (t - a)) ≤ Real.exp (R * (b - a)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hR
  have hm := mul_le_mul_of_nonneg_left hex hbudget
  dsimp only [R, budget] at hm
  linarith

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Actual finite cell approximations with uniform temporal H¹ class bounds. -/

/-- The actual Galerkin constructor has a temporal H¹ class bound independent of cutoff. -/
theorem dataGalerkin_exists_bochner {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    let B := dataGeneratorB P
    let q := cellRawSourceFunctional 0 src F
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
            4 * ∑ j, ‖cellSourceSlice (fun t x => F t x j) s‖ ^ 2) *
            Real.exp ((1 + 8 * P.V ^ 2) * (b - a))) := by
  dsimp only
  obtain ⟨y, hy, hdy, hstate, hinit⟩ := molecularGalerkin_exists_timeH1 hab N P.G P.v P.CG P.V
    P.metric_measurable P.metric_bounded P.drift_measurable P.drift_bounded src F hsrcm hFm hsrc hF u₀
  have hsp := cellSource_memLp_product (Icc a b) src hsrcm hsrc
  have hfp := cellSource_memLp_product (Icc a b) F hFm hF
  have hsj := cellSourceSlice_memLp (Icc a b) src hsp
  have hfj (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun t x => F t x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp)
  have henergy := molecularFinite_bochner_norm_bound hab N P.G P.v P.V P.metric_coercive P.drift_measurable P.drift_bounded
    (cellSourceSlice src) (fun t j => cellSourceSlice (fun t x => F t x j) t)
    hsj hfj _ _ _ hstate hy
  refine ⟨y, hstate, hy, hinit, henergy.trans ?_⟩
  have hn := cellGalerkinL2Initial_norm_le N u₀
  have hn2 : ‖cellGalerkinValue N (extendCurve hab y a)‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by
    rw [hinit]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hn
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact mul_le_mul_of_nonneg_right (add_le_add hn2 le_rfl) (Real.exp_nonneg _)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A data-independent terminal threshold supplies the reference cutoff displacement margin. -/

theorem uniform_weak_reference_displacement_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → ∀ i ≥ M,
      ∀ parentSlot slot, Odd parentSlot → ∀ t,
      ocCutoff D.α D.q D.Λ (i + 1) slot t ≠ 0 → ∀ z,
        ‖D.relDisp i parentSlot (D.slotAnchor (i + 1) slot) t z‖ ≤ 1 / 16 := by
  obtain ⟨M, hM, hb⟩ := weak_anchor_product_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ (2 * Real.pi) (1 / 16) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ i hi parentSlot slot hp t hcut z
  have hΛ' : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have ha := ChildInert.anchor_dist D.α D.q hΛ' (i + 1) slot t hcut
  change |t - D.slotAnchor (i + 1) slot| ≤ _ at ha
  have hA : 0 ≤ ocA D.α D.q D.Λ i := Real.rpow_nonneg
    (Construction.Stream.ocEpsilon_pos hΛ').le _
  have hprice : (2 * Real.pi) *
      (ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1)) ≤ 1 / 16 := by
    simpa only [Nat.add_sub_cancel, hDα, hDq, hDΛ] using hb (i + 1) (by omega)
  calc
    _ ≤ |D.slotAnchor (i + 1) slot - t| * (2 * Real.pi) * ocA D.α D.q D.Λ i :=
      weak_relative_displacement_value_bound D hΛ' hζ' i parentSlot hp _ t z
    _ ≤ ocTauPP D.α D.q D.Λ (i + 1) * (2 * Real.pi) * ocA D.α D.q D.Λ i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by simpa only [abs_sub_comm] using ha) (by positivity)) hA
    _ = (2 * Real.pi) *
        (ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1)) := by ring
    _ ≤ 1 / 16 := hprice

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Physical Piola transport lowers the dimensional power exactly, with a finite menu price. -/

def weakPhysicalPiolaPrice (Ks K N n d : ℕ) (C B : ℝ) : ℝ :=
  ∑ _a : Fin 2, ∑ _A : DerivativeWord2 (d - 1), ∑ e ∈ Finset.Icc d n,
    ∑ _I : DerivativeWord2 (e - 1), ∑ _i : Fin 2,
      (((Ks + 1 : ℕ) * (2 : ℝ) ^ Ks) ^ 2 * C *
        (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ K) * B

theorem weakPhysicalPiolaPrice_nonneg (Ks K N n d : ℕ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    0 ≤ weakPhysicalPiolaPrice Ks K N n d C B := by
  unfold weakPhysicalPiolaPrice
  positivity

theorem weak_physical_piola_jet_bound
    (matrix : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hmat : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun x => matrix x a b))
    (Ks K N n d k : ℕ) (hnK : n ≤ K) (hd : 2 ≤ d) (_hdn : d ≤ n)
    (hk : k ≤ Ks) (hN : Ks + K ≤ N)
    (C B θ κ ef e : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (hef : 0 ≤ ef) (he : 0 < e)
    (hmj : ∀ a b j, j ≤ N → ∀ x, e ^ j * ‖iteratedFDeriv ℝ j (fun y => matrix y a b) x‖ ≤ C)
    (array : ∀ a : ℕ, DerivativeWord2 (a - 1) → Vec 2 → Vec 2)
    (harray : ∀ a I i, ContDiff ℝ (k : ℕ) (fun x => array a I x i))
    (hb : ∀ a ∈ Finset.Icc d n, ∀ I i j, j ≤ k → ∀ x,
      e ^ j * ‖iteratedFDeriv ℝ j (fun y => array a I y i) x‖ ≤
        θ * (κ * ef ^ (n - 2) * e ^ ((a : ℝ) - (n : ℝ)) * B))
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (map : U →L[ℝ] V) (hmap : ‖map‖ ≤ 1) (x : Vec 2) :
    e ^ k * ‖iteratedFDeriv ℝ k (fun y => CycleJointProofs.nativeArrayAssembly (d - 1) map
      (fun a A => transportedCoeff matrix n (fun e I => array e I y) (d - 1) A y a)) x‖ ≤
      θ * (κ * ef ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ))) *
        weakPhysicalPiolaPrice Ks K N n d C B := by
  let MB (a : ℕ) (_I : DerivativeWord2 (a - 1)) :=
    θ * (κ * ef ^ (n - 2) * e ^ ((a : ℝ) - (n : ℝ)) * B)
  have hMB a I : 0 ≤ MB a I := mul_nonneg hθ
    (mul_nonneg (mul_nonneg (mul_nonneg hκ (pow_nonneg hef _))
      (Real.rpow_pos_of_pos he _).le) hB)
  have heq : d - 1 + 1 = d := by omega
  have ht := CycleJointProofs.uniform_native_transport_assembly_jet_bound matrix hmat
    N n K Ks k (d - 1) hnK hk C e e hC he he.le le_rfl (by omega) hmj
    array harray MB hMB (by simpa only [heq] using hb) map x
  apply ht.trans
  simp only [heq]
  unfold weakPhysicalPiolaPrice
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  apply le_trans (mul_le_of_le_one_left (Finset.sum_nonneg fun a ha =>
    Finset.sum_nonneg fun I hI => Finset.sum_nonneg fun i hi =>
      mul_nonneg (by positivity) (mul_nonneg (hMB a I) (pow_nonneg (inv_nonneg.mpr he.le) _))) hmap)
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  dsimp only [MB]
  have hp := weak_piola_lowering_dimensional_count e he n a (d - 1)
    (by rw [heq]; exact (Finset.mem_Icc.mp ha).1)
  rw [heq] at hp
  calc
    _ = (θ * (κ * ef ^ (n - 2))) *
        (e ^ ((a : ℝ) - (n : ℝ)) * e⁻¹ ^ (a - 1 - (d - 1))) *
        ((((Ks + 1 : ℕ) * (2 : ℝ) ^ Ks) ^ 2 * C *
          (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ K) * B) := by ring
    _ = _ := by rw [hp]; ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite positive jets propagate from an enlarged parent renewal window. -/

theorem child_window_positive_jet_bound_of_parent_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (k : ℕ) (pk : ℤ) (hpk : Odd pk) (s' : ℝ) (c : ChainChild)
    (g : ChainGeom) (hg : GeomSpatialSmooth g) (h h' R B ρ : ℝ)
    (hh : 0 ≤ h) (hh' : h' ≤ h) (hR : 0 ≤ R) (hB : 1 ≤ B)
    (hρ : 0 < ρ) (hρe : ρ ≤ D.eps k)
    (ha : |s' - g.2.2| ≤ 2 * h)
    (hsmall : (2 * R * h') * ocA D.α D.q D.Λ k ≤ 1) (K : ℕ)
    (hp : ∀ u r, |u - g.2.2| ≤ (R + 2) * h → |r - g.2.2| ≤ (R + 2) * h →
      ∀ n, 1 ≤ n → n ≤ K → ∀ x,
        ‖iteratedFDeriv ℝ n (rescaledChart ρ (fun y => g.1 u y r)) x‖ ≤ B)
    (u r : ℝ) (hu : |u - s'| ≤ R * h') (hr : |r - s'| ≤ R * h')
    (n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (rescaledChart ρ (fun y => (D.childGeom k pk s' c g).1 u y r)) x‖ ≤
      positiveJetCompositionBudget K
        (positiveJetCompositionBudget K (max B (1 + (2 * Real.pi) ^ (K + 1)))) := by
  have hu' := child_window_parent_distance hR hh' ha hu
  have hr' := child_window_parent_distance hR hh' ha hr
  have ha0 : |g.2.2 - g.2.2| ≤ (R + 2) * h := by
    rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hh
  have htime : |u - r| ≤ 2 * R * h' := by
    have ht := abs_sub_le u s' r
    have hr' : |s' - r| ≤ R * h' := by simpa only [abs_sub_comm] using hr
    linarith
  have hA : 0 ≤ ocA D.α D.q D.Λ k := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hsmall' := (mul_le_mul_of_nonneg_right htime hA).trans hsmall
  apply child_chart_positive_jet_bound_of_component_bounds D k pk s' c g hg u r ρ hρ K
    (max B (1 + (2 * Real.pi) ^ (K + 1))) (hB.trans (le_max_left _ _))
  · intro j hj hjK z
    exact (hp u g.2.2 hu' ha0 j hj hjK z).trans (le_max_left _ _)
  · intro j hj hjK z
    apply (rescaled_child_shear_derivative_bound D hΛ hζ k pk hpk u r ρ hρ hρe c g j hj z).trans
    apply le_trans ?_ (le_max_right _ _)
    apply add_le_add le_rfl
    calc
      _ = (|u - r| * ocA D.α D.q D.Λ k) * (2 * Real.pi) ^ (j + 1) := by ring
      _ ≤ 1 * (2 * Real.pi) ^ (j + 1) := mul_le_mul_of_nonneg_right hsmall' (by positivity)
      _ ≤ (2 * Real.pi) ^ (K + 1) := by
        rw [one_mul]
        exact pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) (by omega)
  · intro j hj hjK z
    exact (hp g.2.2 r ha0 hr' j hj hjK z).trans (le_max_left _ _)
  · exact hn
  · exact hnK

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Symmetrization and cell averaging preserve the local germs of finite left coefficients. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set (Vec 2)}

theorem LeftTermSlowEq.coeffAt {c d : LeftTerm E F} (he : LeftTermSlowEq U c d)
    (m : ℕ) (α : DerivativeWord2 m) : SlowOpenFieldEq U (c.coeffAt m α) (d.coeffAt m α) := by
  classical
  rcases c with ⟨n, w, f⟩
  rcases d with ⟨n', w', g⟩
  rcases he with ⟨ho, hw, hf⟩
  dsimp only at ho hw hf
  subst n'
  have hww : w = w' := eq_of_heq hw
  subst w'
  intro X hX z
  unfold LeftTerm.coeffAt
  split_ifs
  · exact hf X hX z
  · rfl
  · rfl

theorem leftTermsCoefficient_slow_local_congr (l r : List (LeftTerm E F))
    (he : List.Forall₂ (LeftTermSlowEq U) l r) (m : ℕ) (α : DerivativeWord2 m) :
    SlowOpenFieldEq U (leftTermsCoefficient l m α) (leftTermsCoefficient r m α) := by
  induction he with
  | nil => intro X _ z; rfl
  | cons hcd hl ih =>
    intro X hX z
    simp only [leftTermsCoefficient_cons]
    exact congrArg₂ (fun f g : E →L[ℝ] F => f + g) (hcd.coeffAt m α X hX z) (ih X hX z)

theorem leftTermsSymmetricCoefficient_slow_local_congr (l r : List (LeftTerm E F))
    (he : List.Forall₂ (LeftTermSlowEq U) l r) (m : ℕ) (α : DerivativeWord2 m) :
    SlowOpenFieldEq U (leftTermsSymmetricCoefficient l m α) (leftTermsSymmetricCoefficient r m α) := by
  intro X hX z
  exact congrArg (fun f : DerivativeWord2 m → E →L[ℝ] F => wordSymmetrize f α)
    (funext (fun β => leftTermsCoefficient_slow_local_congr l r he m β X hX z))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem leftTermsMeanBlockCoefficient_slow_local_congr
    (l r : ∀ v, List (LeftTerm (∀ i, hv i) (hv v)))
    (he : ∀ v, List.Forall₂ (LeftTermSlowEq U) (l v) (r v))
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (hX : X ∈ U)
    (z : Vec 2) (v u : ι) :
    leftTermsMeanBlockCoefficient l m α t X z v u =
      leftTermsMeanBlockCoefficient r m α t X z v u := by
  unfold leftTermsMeanBlockCoefficient liftCoefficientCellMean
  apply congrArg fieldCellMean
  funext y
  exact congrArg (fun f => f.comp (ContinuousLinearMap.single ℝ hv u))
    (leftTermsSymmetricCoefficient_slow_local_congr (l v) (r v) (he v) m α X hX y)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Poincaré control for the actual ordered derivative fields. -/

theorem cellDerivative_mean_zero (i : Fin 2) (u : TorusHk 1 ℂ) :
    cellMean (cellDerivativeCLM i u) = 0 := by
  have hh := cellComplexPair_one_derivative i u
  have he : cellComplexPair (cellConstantCLM 1) (cellDerivativeCLM i u) =
      star (cellMean (cellDerivativeCLM i u)) := by
    rw [cellComplexPair_symm, cellComplexPair_one]
  rw [he] at hh
  exact star_eq_zero.mp hh

/-- The `H¹` field of an ordered derivative, constructed from the existing
weak-jet graph maps. -/
def orderedCellH1 {K : ℕ} (u : TorusHk (K + 1) ℂ) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) : TorusHk 1 ℂ :=
  derivativeTorusHk w (truncateTorusHk (by omega : 1 + j.val ≤ K + 1) u)

theorem orderedCellH1_value {K : ℕ} (u : TorusHk (K + 1) ℂ) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) :
    torusHkValueCLM (orderedCellH1 u j w) = u.val (lowerIndex2 j w) := by
  change (orderedCellH1 u j w).val (valueIndex2 1) = _
  simp only [orderedCellH1, derivativeTorusHk_apply, truncateTorusHk_apply]
  apply congrArg (fun a => u.val a)
  apply Sigma.ext
  · apply Fin.ext
    simp [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, lowerIndex2, lowerIndex]
  · simp [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, lowerIndex2, lowerIndex]

theorem orderedCellH1_derivative {K : ℕ} (u : TorusHk (K + 1) ℂ)
    (j : Fin (K + 1)) (w : DerivativeWord2 j.val) (i : Fin 2) :
    cellDerivativeCLM i (orderedCellH1 u j w) = u.val (nextIndex2 j w i) := by
  change (orderedCellH1 u j w).val ⟨⟨1, by decide⟩, fun _ => i⟩ = _
  simp only [orderedCellH1, derivativeTorusHk_apply, truncateTorusHk_apply]
  apply congrArg (fun a => u.val a)
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · simp [truncateJetIndex, prefixJetIndex, nextIndex2, nextIndex,
      Fin.append_right_eq_snoc]

theorem orderedCellJet_mean_zero {K : ℕ} (u : TorusHk (K + 1) ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0)
    (r : ℕ) (hr : r ≤ K) (w : DerivativeWord2 r) :
    cellMean (u.val ⟨⟨r, by omega⟩, w⟩) = 0 := by
  cases r with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact hm
  | succ r =>
    have hh := cellDerivative_mean_zero (w (Fin.last r))
      (orderedCellH1 u ⟨r, by omega⟩ (Fin.init w))
    rw [orderedCellH1_derivative] at hh
    have he : (⟨⟨r + 1, by omega⟩, w⟩ : JetIndex2 (K + 1)) =
        nextIndex2 ⟨r, by omega⟩ (Fin.init w) (w (Fin.last r)) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · simp [nextIndex2, nextIndex, Fin.snoc_init_self]
    simpa only [he] using hh

theorem orderedCellJet_poincare {K : ℕ} (u : TorusHk (K + 1) ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) :
    ‖u.val (lowerIndex2 j w)‖ ^ 2 ≤
      (4 * Real.pi ^ 2)⁻¹ * ∑ i : Fin 2, ‖u.val (nextIndex2 j w i)‖ ^ 2 := by
  have hmean : cellMean (torusHkValueCLM (orderedCellH1 u j w)) = 0 := by
    rw [orderedCellH1_value]
    exact orderedCellJet_mean_zero u hm j.val (by omega) w
  simpa only [orderedCellH1_value, orderedCellH1_derivative] using
    cellH1_meanZero_poincare (orderedCellH1 u j w) hmean

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Literal real cell square integrals agree with the complex Hilbert trace norm. -/

theorem realTrace_square (u : AVRegularity.CycleEvolution.ComplexCellL2)
    (q : Vec 2 → ℝ) (he : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (q x : ℂ)) : ‖u‖ ^ 2 = ∫ x in AVenhance.unitCube, q x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The ordered mean-free cell estimate summed with factorial weights. -/

theorem sum_snoc_words (r : ℕ) (f : DerivativeWord2 (r + 1) → ℝ) :
    (∑ w : DerivativeWord2 r, ∑ i : Fin 2, f (Fin.snoc w i)) = ∑ w, f w := by
  let e : (DerivativeWord2 r × Fin 2) ≃ DerivativeWord2 (r + 1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin 2))
  have he := Equiv.sum_comp e f
  simpa only [Fintype.sum_prod_type, e, Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.swap, Fin.snocEquiv, Equiv.coe_fn_mk] using he

theorem factorialCellPoincare {K : ℕ} (ρ : ℝ) (u : TorusHk (K + 1) ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    factorialNormSq ρ (truncateTorusHk (Nat.le_succ K) u).val ≤
      (4 * Real.pi ^ 2)⁻¹ * gradFactorialNormSq ρ u.val := by
  unfold factorialNormSq derivativeNormSq gradFactorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg _ _)
  calc
    (∑ w : DerivativeWord2 j.val,
      ‖(truncateTorusHk (Nat.le_succ K) u).val ⟨j, w⟩‖ ^ 2) ≤
        ∑ w : DerivativeWord2 j.val,
          (4 * Real.pi ^ 2)⁻¹ * ∑ i : Fin 2, ‖u.val (nextIndex2 j w i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      simpa only [truncateTorusHk_apply, truncateJetIndex, lowerIndex2, lowerIndex] using
        orderedCellJet_poincare u hm j w
    _ = (4 * Real.pi ^ 2)⁻¹ *
        ∑ w : DerivativeWord2 (j.val + 1), ‖u.val ⟨⟨j.val + 1, by omega⟩, w⟩‖ ^ 2 := by
      rw [← Finset.mul_sum]
      apply congrArg (fun x : ℝ => (4 * Real.pi ^ 2)⁻¹ * x)
      simpa only [nextIndex2, nextIndex] using sum_snoc_words j.val
        (fun w => ‖u.val ⟨⟨j.val + 1, by omega⟩, w⟩‖ ^ 2)

theorem factorialCellPoincare_coarse {K : ℕ} (ρ : ℝ) (u : TorusHk (K + 1) ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    factorialNormSq ρ (truncateTorusHk (Nat.le_succ K) u).val ≤
      gradFactorialNormSq ρ u.val := by
  have hπ : 1 ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
  have hg : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith
  have hi : (4 * Real.pi ^ 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hg
  have hn : 0 ≤ gradFactorialNormSq ρ u.val := by
    unfold gradFactorialNormSq
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  exact (factorialCellPoincare ρ u hm).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hi hn)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Operator norm bounds for actual scalar/flux forcing and the H⁻¹ cell derivative. -/

/-- The actual dual derivative is bounded by the form functional and source budgets. -/
theorem dataDualDerivative_norm_le
    (P : MolecularData)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    ‖dataDualDerivative P t u S F‖ ≤
      ‖dataGeneratorForm P t u‖ +
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖S‖ +
        ∑ j, ‖cellShiftedDerivativeCLM (fun i => star ((0 : Fin 2 → ℂ) i)) j‖ * ‖F j‖ := by
  unfold dataDualDerivative
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_add_le _ _).trans ((add_le_add le_rfl (cellSourceFunctional_norm_le 0 S F)).trans_eq
    (add_assoc _ _ _).symm)

end AVRegularity.EntryWeakProofs
end
end
end
