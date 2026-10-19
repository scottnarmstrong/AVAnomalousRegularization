-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.FactorialShift
public import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Constant fiber operators preserve the periodic weak Sobolev carrier. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Applying a constant fiber operator to every raw derivative. -/
def mapRawJet {K : ℕ} (L : E →L[ℝ] F) (D : RawJet2 K E) : RawJet2 K F :=
  fun j x => L (D j x)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Weak derivative identities commute with a constant fiber operator by its adjoint. -/
theorem mapRawJet_hasWeakJet {K : ℕ} (L : E →L[ℝ] F) (D : RawJet2 K E)
    (hD : HasOrderedWeakJetOn Set.univ D) : HasOrderedWeakJetOn Set.univ (mapRawJet L D) := by
  intro j w k e
  have he := hD j w k (L.adjoint e)
  simpa only [mapRawJet, ← ContinuousLinearMap.adjoint_inner_left] using he

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Constant fiber maps preserve the full periodic weak jet witness. -/
theorem mapRawJet_hasPeriodicWeakJet {K : ℕ} (L : E →L[ℝ] F) (D : RawJet2 K E)
    (hD : HasPeriodicOrderedWeakJet D) : HasPeriodicOrderedWeakJet (mapRawJet L D) := by
  refine ⟨?_, ?_, mapRawJet_hasWeakJet L D hD.2.2⟩
  · intro j n x
    unfold mapRawJet
    rw [hD.1 j n x]
  · intro j
    exact L.comp_memLp' (hD.2.1 j)

/-- A constant fiber map on the periodic Sobolev carrier. -/
def mapTorusHk {K : ℕ} (L : E →L[ℝ] F) (w : TorusHk K E) : TorusHk K F :=
  TorusHkFunction.toHk
    { jet := mapRawJet L w.toFunction.jet
      hasPeriodicWeakJet := mapRawJet_hasPeriodicWeakJet L _ w.toFunction.hasPeriodicWeakJet }

/-- The mapped carrier has the expected cell representative at every derivative. -/
theorem mapTorusHk_jet_ae {K : ℕ} (L : E →L[ℝ] F) (w : TorusHk K E) (j : JetIndex2 K) :
    (mapTorusHk L w).val j =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => L ((w.val j) x) := by
  have hm := torusJetToL2_ae (mapRawJet L w.toFunction.jet)
    (mapRawJet_hasPeriodicWeakJet L _ w.toFunction.hasPeriodicWeakJet).2.1 j
  have hw := periodicJetRepresentative_ae w.val j
  filter_upwards [hm, hw] with x hx hwx
  exact hx.trans (congrArg L hwx)

/-- Mapping the graph jet is exactly the L² action of the constant fiber operator. -/
theorem mapTorusHk_jet_eq_compLp {K : ℕ} (L : E →L[ℝ] F) (w : TorusHk K E) (j : JetIndex2 K) :
    (mapTorusHk L w).val j = (L.compLpL 2 (volume.restrict AVenhance.unitCube)) (w.val j) := by
  apply Lp.ext
  exact (mapTorusHk_jet_ae L w j).trans
    (ContinuousLinearMap.coeFn_compLpL L (w.val j)).symm

end AVRegularity.CoupledEnergy.Variational
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The dimension-free drift tensor estimate for one positional subset:
reindex by `maskWordEquiv`, apply the coefficient-array norm, and reassemble
the gradient slots. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Gradient input array for a fixed complementary derivative word. -/
def driftMaskGradient {K j : ℕ} (hj : j ≤ K) (D : RawJet2 (K + 1) E)
    (m : PositionMask j) (v : DerivativeWord2 (maskRightLength j m)) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => E) :=
  WithLp.toLp 2 fun k =>
    D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, Fin.snoc v k⟩ x

/-- A selected drift derivative contracted with the complementary differentiated gradient. -/
def driftMaskTerm {K j : ℕ} (hj : j ≤ K) (v : Vec 2 → Vec 2) (D : RawJet2 (K + 1) E)
    (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) : E :=
  scalarArrayAct (coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x)
    (driftMaskGradient hj D m (maskWordEquiv 2 j m w).2 x) (maskWordEquiv 2 j m w).1

/-- The full word-array square of one drift mask is bounded with constant one. -/
theorem driftMaskTerm_pointwise_sumSq_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (D : RawJet2 (K + 1) E) (m : PositionMask j) (x : Vec 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    (∑ w : DerivativeWord2 j, ‖driftMaskTerm hj v D m w x‖ ^ 2) ≤
      M ^ 2 * ∑ w : DerivativeWord2 (maskRightLength j m + 1),
        ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, w⟩ x‖ ^ 2 := by
  let T := coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x
  let f := fun p : DerivativeWord2 (maskLeftLength j m) × DerivativeWord2 (maskRightLength j m) =>
    ‖scalarArrayAct T (driftMaskGradient hj D m p.2 x) p.1‖ ^ 2
  have heq : (∑ w : DerivativeWord2 j, ‖driftMaskTerm hj v D m w x‖ ^ 2) = ∑ p, f p :=
    Fintype.sum_equiv (maskWordEquiv 2 j m) _ _ (fun _ => rfl)
  rw [heq, Fintype.sum_prod_type, Finset.sum_comm]
  have hbound : (∑ b : DerivativeWord2 (maskRightLength j m), ∑ a : DerivativeWord2 (maskLeftLength j m),
      f (a, b)) ≤ M ^ 2 * ∑ b : DerivativeWord2 (maskRightLength j m),
        ‖driftMaskGradient hj D m b x‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    change (∑ a : DerivativeWord2 (maskLeftLength j m),
      ‖scalarArrayAct T (driftMaskGradient hj D m b x) a‖ ^ 2) ≤ _
    rw [← PiLp.norm_sq_eq_of_L2]
    exact (scalarArrayAct_normSq_le T _).trans
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg T) hM).mpr hb) (sq_nonneg _))
  refine hbound.trans_eq ?_
  congr 1
  simp_rw [PiLp.norm_sq_eq_of_L2]
  change (∑ b : DerivativeWord2 (maskRightLength j m), ∑ k : Fin 2,
    ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, Fin.snoc b k⟩ x‖ ^ 2) = _
  rw [← Fintype.sum_prod_type (fun p : DerivativeWord2 (maskRightLength j m) × Fin 2 =>
    ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, Fin.snoc p.1 p.2⟩ x‖ ^ 2)]
  exact (Fintype.sum_equiv (wordInitLastEquiv 2 (maskRightLength j m))
    (fun w => ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, w⟩ x‖ ^ 2)
    (fun p => ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
      Fin.snoc p.1 p.2⟩ x‖ ^ 2)
    (fun w => by
      dsimp only [wordInitLastEquiv, Equiv.coe_fn_mk]
      rw [Fin.snoc_init_self])).symm

end AVRegularity.CoupledEnergy.Variational
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Spacetime weak compactness with an explicit, short Hilbert instance chain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The fixed higher-order ambient product Hilbert space used after finite coefficient synthesis. -/
abbrev CoupledHighHilbert (K : ι → ℕ) := PiLp 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))

/-- The fixed time Hilbert space for extracting a common spacetime weak subsequence. -/
abbrev CoupledHighTime (K : ι → ℕ) (a b : ℝ) :=
  Lp (CoupledHighHilbert (h := h) K) 2 (volume.restrict (Set.Icc a b))

omit [∀ i, BorelSpace (h i)] in
/-- Uniform higher-order spacetime norms yield one subsequence for every linear observable. -/
theorem exists_strictMono_tendsto_highTime_clm (K : ι → ℕ) (a b R : ℝ)
    (u : ℕ → CoupledHighTime (h := h) K a b) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (U : CoupledHighTime (h := h) K a b) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell U)) := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) := fun i => inferInstance
  let : InnerProductSpace ℝ (CoupledHighHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))
  let : InnerProductSpace ℝ (CoupledHighTime (h := h) K a b) := L2.innerProductSpace
  let : ∀ i, TopologicalSpace.SeparableSpace (JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) :=
    fun i => torusJetSeparableSpace (K i + 1)
  let : SecondCountableTopology (CoupledHighHilbert (h := h) K) :=
    PiLp.secondCountableTopology 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))
  let : TopologicalSpace.SeparableSpace (CoupledHighHilbert (h := h) K) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  let : SFinite (volume.restrict (Set.Icc a b) : Measure ℝ) := inferInstance
  let : MeasurableSpace.CountablyGenerated ℝ := inferInstance
  let : IsSeparable (volume.restrict (Set.Icc a b) : Measure ℝ) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (CoupledHighTime (h := h) K a b) := Lp.SecondCountableTopology
  let : TopologicalSpace.SeparableSpace (CoupledHighTime (h := h) K a b) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le u R hu

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Bundle the already constructed constant fiber action as a continuous
linear map. This gives genuine time L² membership of each flux direction. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def jetFiberMapCLM (K : ℕ) (L : E →L[ℝ] F) :
    JetL2 (volume.restrict AVenhance.unitCube) K E →L[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) K F :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict AVenhance.unitCube) F)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun j : JetIndex2 K =>
        (L.compLpL 2 (volume.restrict AVenhance.unitCube)).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
            ComponentL2 (volume.restrict AVenhance.unitCube) E) j)))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
@[simp] theorem jetFiberMapCLM_apply (K : ℕ) (L : E →L[ℝ] F)
    (w : JetL2 (volume.restrict AVenhance.unitCube) K E) (j : JetIndex2 K) :
    jetFiberMapCLM K L w j = L.compLpL 2 (volume.restrict AVenhance.unitCube) (w j) := rfl

theorem jetFiberMapCLM_preserves_graph (K : ℕ) (L : E →L[ℝ] F) (w : TorusHk K E) :
    jetFiberMapCLM K L w.val ∈ torusHkGraph (E := F) K := by
  have he : jetFiberMapCLM K L w.val = (mapTorusHk L w).val := by
    apply PiLp.ext
    intro j
    exact (mapTorusHk_jet_eq_compLp L w j).symm
  rw [he]
  exact (mapTorusHk L w).property

def mapTorusHkCLM (K : ℕ) (L : E →L[ℝ] F) : TorusHk K E →L[ℝ] TorusHk K F :=
  ((jetFiberMapCLM K L).comp (torusHkGraph (E := E) K).toSubmodule.subtypeL).codRestrict
    (torusHkGraph (E := F) K).toSubmodule (jetFiberMapCLM_preserves_graph K L)

@[simp] theorem mapTorusHkCLM_apply (K : ℕ) (L : E →L[ℝ] F) (w : TorusHk K E) :
    mapTorusHkCLM K L w = mapTorusHk L w := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  exact (mapTorusHk_jet_eq_compLp L w j).symm

theorem mapTorusHk_memLp {T : Type*} [MeasurableSpace T] (μ : Measure T) (K : ℕ)
    (L : E →L[ℝ] F) (w : T → TorusHk K E) (hw : MemLp w 2 μ) :
    MemLp (fun t => mapTorusHk L (w t)) 2 μ := by
  simpa only [Function.comp_def, mapTorusHkCLM_apply] using (mapTorusHkCLM K L).comp_memLp' hw

end AVRegularity.CoupledEnergy.Variational
end
