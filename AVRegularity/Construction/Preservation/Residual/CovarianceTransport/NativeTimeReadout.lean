-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.CycleWords.CellGalerkinLinearPrimitive
import AVRegularity.CycleWords.PeriodicClassicalLiftReadout
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Weighted.ParameterCoefficientJetMeasurable
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-! A native Sobolev time derivative gives a single pointwise derivative field.
The exceptional time set is selected in the Hilbert space before evaluating at any point. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CoupledEnergy.Variational AVRegularity.EntryWeakProofs

local instance nativeTorusHkNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance nativeTorusHkInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance nativeTorusHkNormedSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Finite Hilbert coordinates upgrade the existing scalar classical evaluation map. -/
def nativeClassicalEvaluationCLM (K : ℕ) (hK : 2 ≤ K) (x : Vec 2) : TorusHk K E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E i)).comp
      ((CycleWords.realClassicalEvaluationCLM K hK x).comp
        (mapTorusHkCLM K (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i))))

/-- Evaluation agrees everywhere with any continuous periodic classical representative. -/
theorem nativeClassicalEvaluationCLM_rep {K r : ℕ} (hK : 2 ≤ K)
    (U : TorusHk K E) (f : Vec 2 → E) (hrep : IsClassicalRep U f r) (x : Vec 2) :
    nativeClassicalEvaluationCLM K hK x U = f x := by
  have hc (i : Fin (Module.finrank ℝ E)) :
      realClassicalLift K (KernelEnergy.mapTorusHk
        (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)) U) =
      fun y => inner ℝ (stdOrthonormalBasis ℝ E i) (f y) := by
    have hm := classicalRep_map U f hrep
      (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i))
    apply CycleWords.realClassicalLift_eq_periodic_rep K hK
    · exact hm.2.1.continuous
    · exact hm.2.2.1
    · exact (periodicJetRepresentative_ae _ _).symm.trans
        (classicalRep_value_ae _ _ hm)
  simp only [nativeClassicalEvaluationCLM, sum_apply,
    ContinuousLinearMap.comp_apply, KernelEnergy.kernelMapTorusHkCLM_apply,
    CycleWords.realClassicalEvaluationCLM, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk, hc, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]
  exact (stdOrthonormalBasis ℝ E).sum_repr' (f x)

/-- The derivative exceptional set is independent of the spatial evaluation point. -/
theorem native_classical_time_derivative {K r : ℕ} (hK : 2 ≤ K) {a b : ℝ}
    (hab : a ≤ b) (U dU : ℝ → TorusHk K E) (hU : CycleEvolution.StrongTimeRegularity a b U dU)
    (f : ℝ → Vec 2 → E) (hrep : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) r) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
      HasDerivAt (fun s => f s x) (nativeClassicalEvaluationCLM K hK x (dU t)) t := by
  have hd := hU.derivative
  rw [uIcc_of_le hab] at hd
  have hInside : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hd, hInside] with t ht hti
  intro x
  have heval := (nativeClassicalEvaluationCLM (E := E) K hK x).hasFDerivAt.comp_hasDerivAt t ht
  apply heval.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
  exact (nativeClassicalEvaluationCLM_rep hK (U s) (f s) (hrep s ⟨hs.1.le, hs.2.le⟩) x).symm

/-- Fixed Hilbert pairings recover the vector-valued time primitive. -/
theorem native_hilbert_time_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {a b : ℝ} (U dU : ℝ → H)
    (hU : CycleEvolution.StrongTimeRegularity a b U dU) (hdU : IntervalIntegrable dU volume a b) :
    U b - U a = ∫ s in a..b, dU s := by
  apply ext_inner_right ℝ
  intro z
  have hi := (innerSL ℝ z).intervalIntegral_comp_comm hdU
  have he := hU.pairing_increment z
  rw [inner_sub_left]
  calc
    inner ℝ (U b) z - inner ℝ (U a) z = ∫ s in a..b, inner ℝ (dU s) z := he
    _ = inner ℝ (∫ s in a..b, dU s) z := by
      simpa only [innerSL_apply_apply, real_inner_comm] using hi

/-- Pointwise primitives hold at every spatial point, including the time endpoints. -/
theorem native_classical_time_increment {K r : ℕ} (hK : 2 ≤ K) {a b : ℝ}
    (hab : a ≤ b) (U dU : ℝ → TorusHk K E) (hU : CycleEvolution.StrongTimeRegularity a b U dU)
    (hdU : IntervalIntegrable dU volume a b)
    (f : ℝ → Vec 2 → E) (hrep : ∀ t ∈ Icc a b, IsClassicalRep (U t) (f t) r)
    (t : ℝ) (ht : t ∈ Icc a b) (x : Vec 2) :
    f t x - f a x = ∫ s in Ioc a t, nativeClassicalEvaluationCLM K hK x (dU s) := by
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  let L := nativeClassicalEvaluationCLM (E := E) K hK x
  have hm := (hU.mono hsub).map L
  have hint : IntervalIntegrable (fun s => L (dU s)) volume a t := by
    have hdt := hdU.mono_set hsub
    exact ⟨L.integrable_comp hdt.1, L.integrable_comp hdt.2⟩
  have hi := native_hilbert_time_increment (fun s => L (U s)) (fun s => L (dU s)) hm hint
  rw [intervalIntegral.integral_of_le ht.1] at hi
  rw [nativeClassicalEvaluationCLM_rep hK (U t) (f t) (hrep t ht) x,
    nativeClassicalEvaluationCLM_rep hK (U a) (f a) (hrep a ⟨le_rfl, hab⟩) x] at hi
  exact hi

/-- The literal parent readout transports the strong time equation, including
all root casts, finite sums and fixed birth weights. -/
theorem native_succReadout_strong_time
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {S S' : Finset Comp} {K : ℕ} {a b : ℝ} (m : ℕ) (ε η : ℝ) (U dU : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (hU : ∀ c, CycleEvolution.StrongTimeRegularity a b (U c) (dU c)) (v : CompIn S) :
    CycleEvolution.StrongTimeRegularity a b
      (fun t => succReadout m ε η K (fun c => U c t) v)
      (fun t => succReadout m ε η K (fun c => dU c t) v) := by
  classical
  have hcast {r r' : ℕ} (h : r = r')
      (u du : ℝ → TorusHk K (hr r)) (hu : CycleEvolution.StrongTimeRegularity a b u du) :
      CycleEvolution.StrongTimeRegularity a b
        (fun t => cast (congrArg (fun r => TorusHk K (hr r)) h) (u t))
        (fun t => cast (congrArg (fun r => TorusHk K (hr r)) h) (du t)) := by
    subst r'
    exact hu
  let term (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root)) (c : CompIn S') (t : ℝ) :=
    if he : compParent m c.1 = v.1 then ε ^ (η * (compWord m c.1).length) •
      cast (congrArg (fun r => TorusHk K (hr r))
        ((compParent_root m c.1).symm.trans (congrArg Comp.root he))) (u c t) else 0
  have hz : CycleEvolution.StrongTimeRegularity a b
      (fun _ => (0 : TorusHk K (hr v.1.root))) (fun _ => 0) :=
    ⟨contDiffOn_const.absolutelyContinuousOnInterval,
      ae_of_all _ (fun t => hasDerivAt_const t _)⟩
  have hterm (c : CompIn S') :
      CycleEvolution.StrongTimeRegularity a b (term U c) (term dU c) := by
    by_cases he : compParent m c.1 = v.1
    · simp only [term, dite_eq_left he]
      exact (hcast ((compParent_root m c.1).symm.trans (congrArg Comp.root he))
        (U c) (dU c) (hU c)).map
          ((ε ^ (η * (compWord m c.1).length)) • ContinuousLinearMap.id ℝ _)
    · simp only [term, dite_eq_right he]
      exact hz
  have hsum (s : Finset (CompIn S')) : CycleEvolution.StrongTimeRegularity a b
      (fun t => ∑ c ∈ s, term U c t) (fun t => ∑ c ∈ s, term dU c t) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hz
    | @insert c s hc ih =>
      simpa only [Finset.sum_insert hc] using (hterm c).add ih
  exact hsum Finset.univ

/-- The same finite parent readout preserves continuity at the full native order. -/
theorem native_succReadout_continuousOn
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {S S' : Finset Comp} {K : ℕ} {A : Set ℝ} (m : ℕ) (ε η : ℝ) (U : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (hU : ∀ c, ContinuousOn (U c) A) (v : CompIn S) :
    ContinuousOn (fun t => succReadout m ε η K (fun c => U c t) v) A := by
  classical
  have hcast {r r' : ℕ} (h : r = r') (u : ℝ → TorusHk K (hr r))
      (hu : ContinuousOn u A) :
      ContinuousOn (fun t => cast (congrArg (fun r => TorusHk K (hr r)) h) (u t)) A := by
    subst r'
    exact hu
  unfold succReadout
  apply continuousOn_finsetSum
  intro c _
  by_cases he : compParent m c.1 = v.1
  · simp only [dite_eq_left he]
    exact (hcast ((compParent_root m c.1).symm.trans (congrArg Comp.root he))
      (U c) (hU c)).const_smul (ε ^ (η * (compWord m c.1).length) : ℝ)
  · simp only [dite_eq_right he]
    exact continuousOn_const

open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Reconstruction

private theorem native_smul_identity_contDiff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c) (A : ℝ → V →L[ℝ] V)
    (hA : ∀ t, A t = c t • ContinuousLinearMap.id ℝ V) : ContDiff ℝ 1 A := by
  rw [show A = fun t => c t • ContinuousLinearMap.id ℝ V from funext hA]
  exact hc.smul contDiff_const

section Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Mc : ℝ → ℝ) (hM : ∀ t, covBound (Hc t) ≤ Mc t)

/-- The finite second-order covariance operator is C¹ in the covariance entries. -/
theorem native_covOp_adj_contDiff (hH : ∀ i j, ContDiff ℝ 1 (fun t => Hc t i j))
    (R Kc K : ℕ) (hK : K + 2 ≤ Kc) :
    ContDiff ℝ 1 (fun t => (TorusAdj.covOp (E := E) (Hc t) (hM t) R Kc).adj K hK) := by
  have he := funext fun t => adj_covOp (E := E) (Hc t) (hM t) R Kc K hK
  rw [he]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  have hs : ContDiff ℝ 1 (fun t => (torusSmulCLM (Hc t i j) :
      TorusHk K E →L[ℝ] TorusHk K E)) :=
    native_smul_identity_contDiff (hH i j) _ (fun t => torusSmulCLM_eq_smul_id (Hc t i j))
  exact hs.clm_comp contDiff_const

/-- Each finite covariance power is C¹, with the existing native index casts. -/
theorem native_covIter_adj_contDiff (hH : ∀ i j, ContDiff ℝ 1 (fun t => Hc t i j)) :
    ∀ (l R Kc K : ℕ) (hK : K + 2 * l ≤ Kc),
      ContDiff ℝ 1 (fun t => (TorusAdj.covIter (E := E) (Hc t) (hM t) l R Kc).adj K hK) := by
  intro l
  induction l with
  | zero =>
    intro R Kc K hK
    have he := funext fun t => adj_covIter_zero (E := E) (Hc t) (hM t) R Kc K hK
    rw [he]
    exact contDiff_const
  | succ l ih =>
    intro R Kc K hK
    have he := funext fun t => adj_covIter_succ (E := E) (Hc t) (hM t) l R Kc K hK
    rw [he]
    exact ((ih (R + 2) Kc K (by omega)).clm_comp
      ((native_covOp_adj_contDiff (E := E) Hc Mc hM hH R Kc (K + 2 * l) (by omega)).clm_comp
        contDiff_const)).clm_comp contDiff_const

/-- The actual covariance polynomial adjoint is C¹ in time; no new operator is introduced. -/
theorem native_covPolyP_adj_contDiff (hH : ∀ i j, ContDiff ℝ 1 (fun t => Hc t i j))
    (p R Kc K : ℕ) (hK : K + 2 * p ≤ Kc) :
    ContDiff ℝ 1 (fun t => (TorusAdj.covPolyP (E := E) (Hc t) (hM t) p R Kc).adj K hK) := by
  have he := funext fun t => adj_covPolyP (E := E) (Hc t) (hM t) p R Kc K hK
  rw [he]
  apply ContDiff.sum
  intro l _
  exact contDiff_const.clm_comp ((native_covIter_adj_contDiff (E := E) Hc Mc hM hH l.1 R Kc K
    (by have := Finset.mem_range.mp l.2; omega)).clm_comp contDiff_const)

end Operators

section TimeAction
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ H] in
/-- A compact-window continuous curve is square integrable in its native space. -/
theorem native_continuous_curve_memLp {a b : ℝ} {U : ℝ → H}
    (hU : ContinuousOn U (Icc a b)) : MemLp U 2 (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  apply MemLp.of_bound (hU.aestronglyMeasurable_of_isCompact (μ := volume)
    isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

/-- Compact-window operator bounds suffice for time L²; no global operator bound is needed. -/
theorem native_continuous_operator_memLp {a b : ℝ} {A : ℝ → H →L[ℝ] V}
    (hA : ContinuousOn A (Icc a b)) {U : ℝ → H} (hU : MemLp U 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => A t (U t)) 2 (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    ((hA.aestronglyMeasurable_of_isCompact (μ := volume) isCompact_Icc measurableSet_Icc).prodMk
      hU.aestronglyMeasurable)
  apply (hU.const_smul (max C 0)).of_le hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  calc
    ‖A t (U t)‖ ≤ ‖A t‖ * ‖U t‖ := (A t).le_opNorm _
    _ ≤ max C 0 * ‖U t‖ := mul_le_mul_of_nonneg_right
      ((hC t ht).trans (le_max_left C 0)) (norm_nonneg _)
    _ = ‖max C 0 • U t‖ := by rw [norm_smul, Real.norm_of_nonneg (le_max_right C 0)]

/-- The operator product derivative remains square integrable on the original window. -/
theorem native_contDiff_operator_strong_time {a b : ℝ} {A : ℝ → H →L[ℝ] V}
    (hA : ContDiff ℝ 1 A) {U dU : ℝ → H} (hU : ContinuousOn U (Icc a b))
    (hdU : MemLp dU 2 (volume.restrict (Icc a b))) (hUt : CycleEvolution.StrongTimeRegularity a b U dU) :
    MemLp (fun t => A t (dU t) + deriv A t (U t)) 2 (volume.restrict (Icc a b)) ∧
    CycleEvolution.StrongTimeRegularity a b (fun t => A t (U t))
      (fun t => A t (dU t) + deriv A t (U t)) := by
  constructor
  · exact (native_continuous_operator_memLp hA.continuous.continuousOn hdU).add
      (native_continuous_operator_memLp (hA.continuous_deriv le_rfl).continuousOn
        (native_continuous_curve_memLp hU))
  · apply Weighted.strongTimeRegularity_clm_apply hA.contDiffOn.absolutelyContinuousOnInterval
      (Filter.Eventually.of_forall fun t => (hA.differentiable (by decide) t).hasDerivAt) hUt

end TimeAction

section Images
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Smooth duality identifies the given covariance image with the continuous adjoint. -/
theorem native_covImage_eq_adj {K L p : ℕ} (hKL : K + 2 * p ≤ L)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Z : TorusHk L E) (W : TorusHk K E) (hW : IsCovImage (covPolyP Hc p) Z W) :
    W = (TorusAdj.covPolyP (E := E) Hc le_rfl p 0 (K + 2 * p)).adj K le_rfl
      (truncateTorusHk hKL Z) := by
  apply Construction.Preservation.FullLift.covImage_unique (covPolyP Hc p) Z W _ hW
  intro ψ hψ hp
  have he := (TorusAdj.covPolyP (E := E) Hc le_rfl p 0 (K + 2 * p)).ident K le_rfl
    (truncateTorusHk hKL Z) ψ (hψ.of_le (by exact_mod_cast le_top)) hp
  change cellInner (tval ((TorusAdj.covPolyP (E := E) Hc le_rfl p 0
    (K + 2 * p)).adj K le_rfl (truncateTorusHk hKL Z))) ψ = cellInner (tval Z) _
  simpa only [tval_truncateTorusHk] using he

/-- Smooth duality transfers native time continuity to an arbitrary stored covariance image. -/
theorem native_covImage_continuousOn {K L p : ℕ} (hKL : K + 2 * p ≤ L) {a b : ℝ}
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) (Icc a b))
    (Z : ℝ → TorusHk L E) (W : ℝ → TorusHk K E) (hZ : ContinuousOn Z (Icc a b))
    (hW : ∀ t ∈ Icc a b, IsCovImage (covPolyP (Hc t) p) (Z t) (W t)) :
    ContinuousOn W (Icc a b) := by
  have hA := (covPolyP_adj_continuousOn (E := E) Hc (fun t => covBound (Hc t))
    (fun _ => le_rfl) hH p 0 (K + 2 * p) K le_rfl).clm_comp
      (continuousOn_const (c := truncateTorusHk (E := E) hKL))
  apply (hA.clm_apply hZ).congr
  intro t ht
  exact native_covImage_eq_adj hKL (Hc t) (Z t) (W t) (hW t ht)

/-- The supplied native covariance image inherits continuity and a common
square-integrable Sobolev derivative from the actual readout. -/
theorem native_covImage_strong_time {K L p : ℕ} (hK : 2 ≤ K)
    (hKL : K + 2 * p ≤ L) {a b : ℝ} (hab : a ≤ b) (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, ContDiff ℝ 1 (fun t => Hc t i j)) (Z : ℝ → TorusHk L E) (dZ : ℝ → TorusHk (L - 2) E)
    (W : ℝ → TorusHk K E) (hZ : ContinuousOn Z (Icc a b)) (hdZ : MemLp dZ 2 (volume.restrict (Icc a b)))
    (hZt : CycleEvolution.StrongTimeRegularity a b
      (fun t => truncateTorusHk (Nat.sub_le L 2) (Z t)) dZ)
    (hW : ∀ t ∈ Icc a b, IsCovImage (covPolyP (Hc t) p) (Z t) (W t)) :
    ContinuousOn W (Icc a b) ∧ ∃ dW : ℝ → TorusHk (K - 2) E,
      MemLp dW 2 (volume.restrict (Icc a b)) ∧
      CycleEvolution.StrongTimeRegularity a b
        (fun t => truncateTorusHk (Nat.sub_le K 2) (W t)) dW := by
  refine ⟨native_covImage_continuousOn hKL Hc
    (fun i j => (hH i j).continuous.continuousOn) Z W hZ hW, ?_⟩
  have hl : K - 2 + 2 * p ≤ L - 2 := by omega
  let B (t : ℝ) : TorusHk (L - 2) E →L[ℝ] TorusHk (K - 2) E :=
    ((TorusAdj.covPolyP (E := E) (Hc t) le_rfl p 0 (K - 2 + 2 * p)).adj
      (K - 2) le_rfl).comp (truncateTorusHk hl)
  have hB : ContDiff ℝ 1 B :=
    (native_covPolyP_adj_contDiff (E := E) Hc (fun t => covBound (Hc t)) (fun _ => le_rfl)
      hH p 0 (K - 2 + 2 * p) (K - 2) le_rfl).clm_comp contDiff_const
  let U (t : ℝ) := truncateTorusHk (Nat.sub_le L 2) (Z t)
  have hUc : ContinuousOn U (Icc a b) :=
    (truncateTorusHk (E := E) (Nat.sub_le L 2)).continuous.comp_continuousOn hZ
  obtain ⟨hLp, ht⟩ := native_contDiff_operator_strong_time hB hUc hdZ hZt
  refine ⟨fun t => B t (dZ t) + deriv B t (U t), hLp, ?_⟩
  apply Weighted.strongTime_congr_on_window hab ht ?_ (fun _ _ => rfl)
  intro t ht
  exact (native_covImage_eq_adj hl (Hc t) (U t) _
    (Construction.Preservation.FullLift.covImage_truncate_input (Nat.sub_le L 2) _ _ _
      (Construction.Preservation.FullLift.covImage_truncate (Nat.sub_le K 2) _ _ _
        (hW t ht)))).symm

end Images

open AVRegularity.CycleComparison.Lift

/-- Finite spatial word coordinates have a bounded linear reconstruction of the
full multilinear jet. This permits norm-valued time calculus without choosing
separate exceptional sets for arbitrary directions. -/
theorem native_multilinear_word_retraction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (n : ℕ) :
    ∃ R : (DerivativeWord2 n → V) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V,
      ∀ A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V,
        R (fun w => A (fun i => basisVec (w (Fin.rev i)))) = A := by
  classical
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V →L[ℝ]
      (DerivativeWord2 n → V) := ContinuousLinearMap.pi (fun w =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) V
          (fun i => basisVec (w (Fin.rev i))))
  have hL : Function.Injective L := by
    intro A B hAB
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    calc
      ‖A - B‖ ≤ ∑ w : DerivativeWord2 n, ‖(A - B) (fun i => basisVec (w i))‖ :=
        ChartTransport.norm_le_sum_basisVec _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro w _hw
        have he := congrFun hAB (fun i => w (Fin.rev i))
        simp only [L, ContinuousLinearMap.pi_apply, ContinuousMultilinearMap.apply_apply,
          Fin.rev_rev] at he
        simp only [sub_apply, he, sub_self, norm_zero]
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  refine ⟨R.toContinuousLinearMap, fun A => ?_⟩
  exact congrArg (fun T : _ →ₗ[ℝ] _ => T A) hR

/-- A spatial jet over `Vec 2` has finitely many word coordinates. -/
instance nativeSpatialJetFiniteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (n : ℕ) : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V) := by
  obtain ⟨R, hR⟩ := native_multilinear_word_retraction (V := V) n
  exact FiniteDimensional.of_surjective R.toLinearMap
    (fun A => ⟨fun w => A (fun i => basisVec (w (Fin.rev i))), hR A⟩)

/-- A continuous periodic field inherits its uniform cell bound on the whole plane. -/
theorem native_periodic_norm_le_of_cube
    {V : Type*} [NormedAddCommGroup V] (f : Vec 2 → V) (hf : Continuous f) (hp : AVenhance.IsZ2Periodic f) (B : ℝ)
    (hb : ∀ x ∈ AVenhance.unitCube, ‖f x‖ ≤ B) (x : Vec 2) : ‖f x‖ ≤ B := by
  have hcl : closure AVenhance.unitCube ⊆ {x | ‖f x‖ ≤ B} :=
    closure_minimal hb (isClosed_le hf.norm continuous_const)
  let y : Vec 2 := fun i => Int.fract (x i)
  let n : Fin 2 → ℤ := fun i => Int.floor (x i)
  have hy : y ∈ closure AVenhance.unitCube := by
    rw [AVenhance.unitCube, closure_pi_set]
    intro i _hi
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have heq : y + AVenhance.latticeShift n = x := by
    funext i
    simp only [Pi.add_apply, y, n, AVenhance.latticeShift, Int.fract]
    ring
  have he := hp n y
  rw [heq] at he
  rw [he]
  exact hcl hy

/-- A permitted word inherits the same literal window measurability, periodicity
and time budgets, with exactly its spatial reserve loss. -/
theorem ClassicalWindowBound.word
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K n L : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ClassicalWindowBound a b K f) (w : DerivativeWord2 n) (hn : n + L ≤ K) :
    ClassicalWindowBound a b L (fun t => orderedDerivative w (f t)) := by
  have hfn (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ (n : ℕ∞) (f t) :=
    (Q.smooth t ht).of_le (Nat.cast_le.mpr (by omega))
  refine ⟨fun t ht => CycleComparison.Lift.orderedDerivative_contDiff w L (f t)
    ((Q.smooth t ht).of_le (Nat.cast_le.mpr (by omega))),
    fun t ht => orderedDerivative_periodic w (f t) (hfn t ht) (Q.periodic t ht), ?_, ?_⟩
  · have hm (x : Vec 2) : Measurable (fun t : Icc a b => f t x) :=
      Q.measurable.comp ((measurable_subtype_coe.prodMk measurable_const).subtype_mk (h := fun t : Icc a b => t.2))
    have hj := Weighted.parameter_orderedDerivative_joint_measurable K n (by omega)
      (fun t : Icc a b => f t) hm (fun t => Q.smooth t t.2) w
    exact hj.comp (((measurable_fst.comp measurable_subtype_coe).subtype_mk (h := fun z => z.2)).prodMk
      (measurable_snd.comp measurable_subtype_coe))
  · intro j hj β
    obtain ⟨B, hB, hb⟩ := Q.bound (n + j) (by omega) (Fin.append w β)
    refine ⟨B, hB, ?_⟩
    intro t ht x hx
    simpa only [CycleWords.orderedDerivative_append] using hb t ht x hx

/-- Continuous periodic jets extend their cell budgets to all spatial points. -/
theorem ClassicalWindowBound.global_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ClassicalWindowBound a b K f) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ x, ‖orderedDerivative w (f t) x‖ ≤ B t := by
  obtain ⟨B, hB, hb⟩ := Q.bound n hn w
  refine ⟨B, hB, fun t ht x => ?_⟩
  have hfn : ContDiff ℝ (n : ℕ∞) (f t) :=
    (Q.smooth t ht).of_le (Nat.cast_le.mpr hn)
  exact native_periodic_norm_le_of_cube _
    (CycleComparison.Lift.orderedDerivative_contDiff w 0 (f t)
      (by simpa only [Nat.zero_add] using hfn)).continuous
    (orderedDerivative_periodic w (f t) hfn (Q.periodic t ht)) (B t) (hb t ht) x

/-- Restricted window measurability suffices for the zero extension used in
compact-label time differentiation. No value outside the window is consumed. -/
theorem ClassicalWindowBound.measurable_zero_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ClassicalWindowBound a b K f) (x : Vec 2) :
    Measurable (fun t => if t ∈ Icc a b then f t x else 0) := by
  classical
  have hm : Measurable (fun t : Icc a b => f t x) :=
    Q.measurable.comp ((measurable_subtype_coe.prodMk measurable_const).subtype_mk (h := fun t : Icc a b => t.2))
  exact hm.dite measurable_const measurableSet_Icc

/-- A fixed bounded linear map preserves the actual spatial window budgets. -/
theorem ClassicalWindowBound.map
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V}
    (Q : ClassicalWindowBound a b K f) (L : V →L[ℝ] W) :
    ClassicalWindowBound a b K (fun t x => L (f t x)) := by
  refine ⟨fun t ht => L.contDiff.comp (Q.smooth t ht),
    fun t ht n x => congrArg L (Q.periodic t ht n x), L.continuous.measurable.comp Q.measurable, ?_⟩
  intro n hn w
  obtain ⟨B, hB, hb⟩ := Q.bound n hn w
  refine ⟨fun t => ‖L‖ * B t, hB.const_mul ‖L‖, fun t ht x hx => ?_⟩
  have he := AVRegularity.orderedDerivative_clm_comp L w
    ((Q.smooth t ht).of_le (Nat.cast_le.mpr hn))
  rw [congrFun he x]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb t ht x hx) (norm_nonneg L))

/-- Finite coordinate arrays retain genuine joint measurability and integrable
jet budgets in the product norm. -/
theorem ClassicalWindowBound.pi
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    [∀ i, MeasurableSpace (V i)] [∀ i, BorelSpace (V i)]
    [∀ i, SecondCountableTopology (V i)]
    {a b : ℝ} {K : ℕ} {f : ∀ i, ℝ → Vec 2 → V i} (Q : ∀ i, ClassicalWindowBound a b K (f i)) :
    ClassicalWindowBound a b K (fun t x i => f i t x) := by
  classical
  refine ⟨fun t ht => contDiff_pi.mpr (fun i => (Q i).smooth t ht),
    fun t ht n x => funext (fun i => (Q i).periodic t ht n x),
    Measurable.of_eval (fun i => (Q i).measurable), ?_⟩
  intro n hn w
  choose B hB hb using fun i => (Q i).bound n hn w
  refine ⟨fun t => ∑ i, |B i t|, integrable_finsetSum _ (fun i _ => (hB i).norm), ?_⟩
  intro t ht x hx
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (B i t)))).mpr
  intro i
  rw [ChartTransport.orderedDerivative_apply w
    (contDiff_pi.mpr (fun i => ((Q i).smooth t ht).of_le (Nat.cast_le.mpr hn))) i x]
  exact ((hb i t ht x hx).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (B j t)) (Finset.mem_univ i))

/-- The full multilinear spatial jet inherits its reserve and budgets from its
finite ordered word coordinates. -/
theorem ClassicalWindowBound.spatial_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {a b : ℝ} {K n L : ℕ} {f : ℝ → Vec 2 → V}
    [MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V)]
    [BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) V)]
    (Q : ClassicalWindowBound a b K f) (hn : n + L ≤ K) :
    ClassicalWindowBound a b L (fun t x => iteratedFDeriv ℝ n (f t) x) := by
  obtain ⟨R, hR⟩ := native_multilinear_word_retraction (V := V) n
  have hQ := (ClassicalWindowBound.pi (fun w => Q.word w hn)).map R
  have he (t : ℝ) (ht : t ∈ Icc a b) (x : Vec 2) :
      R (fun w : DerivativeWord2 n => orderedDerivative w (f t) x) =
        iteratedFDeriv ℝ n (f t) x := by
    simp_rw [AVRegularity.orderedDerivative_eq_iteratedFDeriv _
      ((Q.smooth t ht).of_le (Nat.cast_le.mpr (show n ≤ K by omega)))]
    exact hR _
  refine ⟨fun t ht => (funext (he t ht)) ▸ (hQ.smooth t ht),
    fun t ht l x => by rw [← he t ht, ← he t ht]; exact hQ.periodic t ht l x, ?_, ?_⟩
  · exact (funext (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} => he z.1.1 z.2 z.1.2)) ▸ hQ.measurable
  · intro j hj w
    obtain ⟨B, hB, hb⟩ := hQ.bound j hj w
    refine ⟨B, hB, fun t ht x hx => ?_⟩
    rw [show (fun x => iteratedFDeriv ℝ n (f t) x) =
      (fun x => R (fun w => orderedDerivative w (f t) x)) from (funext (he t ht)).symm]
    exact hb t ht x hx

/-- Every literal time section is integrable from its genuine window
measurability and periodic spatial budget. -/
theorem ClassicalWindowBound.integrable_section
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V} (Q : ClassicalWindowBound a b K f) (x : Vec 2) :
    IntegrableOn (fun t => f t x) (Icc a b) := by
  classical
  obtain ⟨B, hB, hb⟩ := Q.global_bound 0 (Nat.zero_le _) (fun i => Fin.elim0 i)
  have hz : IntegrableOn (fun t => if t ∈ Icc a b then f t x else 0) (Icc a b) := by
    apply hB.norm.mono' (Q.measurable_zero_extension x).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [ite_eq_left ht]
    have hx : ‖f t x‖ ≤ B t := by simpa only [orderedDerivative_zero] using hb t ht x
    exact hx.trans (le_abs_self (B t))
  exact hz.congr_fun (fun t ht => ite_eq_left ht) measurableSet_Icc

/-- The spatial derivative commutes with time integration under the actual
integrable window budget; its bound need not be constant in time. -/
theorem ClassicalWindowBound.integral_fderiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {f : ℝ → Vec 2 → V} (Q : ClassicalWindowBound a b 1 f) {t : ℝ} (ht : t ∈ Icc a b) (x : Vec 2) :
    IntegrableOn (fun r => fderiv ℝ (f r) x) (Ioc a t) ∧
      HasFDerivAt (fun y => ∫ r in Ioc a t, f r y)
        (∫ r in Ioc a t, fderiv ℝ (f r) x) x := by
  classical
  let g := fun r y => if r ∈ Icc a b then f r y else 0
  have hsub : Ioc a t ⊆ Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hg (r : ℝ) : ContDiff ℝ (1 : ℕ∞) (g r) := by
    by_cases hr : r ∈ Icc a b
    · have hh : ContDiff ℝ (1 : ℕ∞) (f r) := (Q.smooth r hr).of_le (by simp)
      simpa only [g, ite_eq_left hr] using hh
    · simpa only [g, ite_eq_right hr] using
        (contDiff_const : ContDiff ℝ (1 : ℕ∞) (fun _ : Vec 2 => (0 : V)))
  have hm (y : Vec 2) : Measurable (fun r => g r y) := Q.measurable_zero_extension y
  have he (r : ℝ) (hr : r ∈ Icc a b) : g r = f r := by
    funext y
    exact ite_eq_left hr
  choose B hB hb using fun w : DerivativeWord2 1 => Q.global_bound 1 le_rfl w
  let C := fun r => ∑ w : DerivativeWord2 1, B w r
  have hCwindow : IntegrableOn C (Icc a b) := integrable_finsetSum _ (fun w _ => hB w)
  have hC : IntegrableOn C (Ioc a t) := hCwindow.mono_set hsub
  have hbd (r : ℝ) (hr : r ∈ Icc a b) (y : Vec 2) :
      ‖fderiv ℝ (f r) y‖ ≤ C r := by
    have hh := ChartTransport.norm_iteratedFDeriv_le_sum_words (Q.smooth r hr) y
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (Finset.sum_le_sum (fun w _ => hb w r hr y))
  have hdm := CycleComparison.Lift.fderiv_parameter_stronglyMeasurable g hm
    (fun r => (hg r).differentiable one_ne_zero) x
  have hdg : IntegrableOn (fun r => fderiv ℝ (g r) x) (Ioc a t) := by
    apply hC.mono' hdm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [he r (hsub hr)]
    exact hbd r (hsub hr) x
  have hde : (fun r => fderiv ℝ (g r) x) =ᵐ[volume.restrict (Ioc a t)]
      (fun r => fderiv ℝ (f r) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [he r (hsub hr)]
  have hInt (y : Vec 2) : IntegrableOn (fun r => g r y) (Ioc a t) :=
    ((Q.integrable_section y).mono_set hsub).congr
      (ae_restrict_mem measurableSet_Ioc |>.mono
        (fun r hr => (congrFun (he r (hsub hr)) y).symm))
  have hd : HasFDerivAt (fun y => ∫ r in Ioc a t, g r y)
      (∫ r in Ioc a t, fderiv ℝ (g r) x) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
      (μ := volume.restrict (Ioc a t)) (F := fun y r => g r y)
      (F' := fun y r => fderiv ℝ (g r) y) (bound := C) univ_mem
    · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable.restrict)
    · exact hInt x
    · exact hdm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      intro y _hy
      rw [he r (hsub hr)]
      exact hbd r (hsub hr) y
    · exact hC
    · exact ae_of_all _ (fun r y _ => ((hg r).differentiable one_ne_zero y).hasFDerivAt)
  have heInt : (fun y => ∫ r in Ioc a t, g r y) = fun y => ∫ r in Ioc a t, f r y := by
    funext y
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact congrFun (he r (hsub hr)) y
  rw [heInt, integral_congr_ae hde] at hd
  exact ⟨hdg.congr hde, hd⟩

/-- Every reserved ordered spatial word commutes with the time integral.
Only the window's integrable jet budgets enter this statement. -/
theorem ClassicalWindowBound.integral_word
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {a b : ℝ} {K : ℕ} {f : ℝ → Vec 2 → V} (Q : ClassicalWindowBound a b K f)
    {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) :
    orderedDerivative w (fun y => ∫ r in Ioc a t, f r y) =
      fun y => ∫ r in Ioc a t, orderedDerivative w (f r) y := by
  induction n with
  | zero => simp only [orderedDerivative_zero]
  | succ n ih =>
    let β : DerivativeWord2 n := fun i => w i.castSucc
    have Qβ : ClassicalWindowBound a b 1 (fun r => orderedDerivative β (f r)) :=
      Q.word β (by omega)
    rw [orderedDerivative_succ, ih (by omega) β]
    funext y
    obtain ⟨hi, hd⟩ := Qβ.integral_fderiv ht y
    rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => (congrFun (orderedDerivative_succ w (f r)) y).symm)

/-- Spatial time primitives follow from the value primitive and the genuine
integrable budgets of the selected derivative, with the stated reserve loss. -/
theorem native_classical_time_curve_of_value_primitive
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (F : Frame D hr Dm bw j₀) (K : ℕ) (f df : F.Field) (hab : F.tp ≤ F.tf)
    (hfield : ∀ v, ClassicalWindowBound F.tp F.tf (K - 2) (fun t x => f t x v))
    (huniform : ∀ v, ∀ n, n + 2 ≤ K → ∀ w : DerivativeWord2 n, ∃ B : ℝ,
      ∀ t ∈ Icc F.tp F.tf, ∀ x ∈ AVenhance.unitCube,
        ‖orderedDerivative w (fun y => f t y v) x‖ ≤ B)
    (hd : IsTimeDerivRep (Icc F.tp F.tf) f df)
    (hdf : ∀ v, ClassicalWindowBound F.tp F.tf (K - 4) (fun t x => df t x v)) (hp : ∀ v, ∀ t ∈ Icc F.tp F.tf, ∀ x,
      f t x v - f F.tp x v = ∫ s in Ioc F.tp t, df s x v) :
    ClassicalTimeCurve F K f df := by
  refine ⟨hfield, huniform, hd, hdf, ?_, hp⟩
  intro n hn w v t ht x
  have hfn (r : ℝ) (hr : r ∈ Icc F.tp F.tf) :
      ContDiff ℝ (n : ℕ∞) (fun y => f r y v) :=
    ((hfield v).smooth r hr).of_le (Nat.cast_le.mpr (by omega))
  have he : (fun y => f t y v - f F.tp y v) =
      fun y => ∫ s in Ioc F.tp t, df s y v := funext (hp v t ht)
  have hw := congrArg (orderedDerivative w) he
  rw [AVRegularity.orderedDerivative_sub w (hfn t ht) (hfn F.tp ⟨le_rfl, hab⟩),
    (hdf v).integral_word ht n (by omega) w] at hw
  exact congrFun hw x

section NativeEarlyWeakCalculus
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The weak periodic partial can be moved onto any H¹ test, by Fourier approximation. -/
theorem native_torus_partial_pairing {K : ℕ} (u : TorusHk (K + 1) E)
    (φ : TorusHk 1 E) (k : Fin 2) :
    inner ℝ (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) (torusHkValueCLM φ) =
      -inner ℝ (torusHkValueCLM u) (φ.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) := by
  let h : Unit → Type := fun _ => E
  have he (N : ℕ) :
      inner ℝ (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩)
        (torusHkValueCLM (galerkinProj N φ)) =
      -inner ℝ (torusHkValueCLM u)
        ((galerkinProj N φ).val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) := by
    have hi := plainWeakJet_test_partial_ibp (h := h) N
      (plainInitialCoefficients N (fun _ : Unit => 1) (fun _ => φ)) () u
      ⟨0, by omega⟩ Fin.elim0 k
    rw [plainInitialCoefficients_synthesis (h := h) N (fun _ : Unit => 1)
      (fun _ => φ) ()] at hi
    have hn : nextIndex2 (⟨0, by omega⟩ : Fin (K + 1)) Fin.elim0 k =
        (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 (K + 1)) := rfl
    have hz : lowerIndex2 (⟨0, by omega⟩ : Fin (K + 1)) Fin.elim0 =
        valueIndex2 (K + 1) := by
      simp [lowerIndex2, lowerIndex, valueIndex2, valueIndex]
    rw [hn, hz] at hi
    exact hi
  let J : TorusHk 1 E →L[ℝ] Lp E 2 (volume.restrict AVenhance.unitCube) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 1 =>
      Lp E 2 (volume.restrict AVenhance.unitCube)) ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩).comp
      (torusHkGraph (E := E) 1).toSubmodule.subtypeL
  have hv := torusHkValueCLM.continuous.continuousAt.tendsto.comp (galerkinProj_tendsto φ)
  have hg := J.continuous.continuousAt.tendsto.comp (galerkinProj_tendsto φ)
  have hl : Tendsto (fun N =>
      inner ℝ (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩)
        (torusHkValueCLM (galerkinProj N φ))) atTop
      (𝓝 (inner ℝ (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) (torusHkValueCLM φ))) :=
    tendsto_const_nhds.inner hv
  have hr : Tendsto (fun N => -inner ℝ (torusHkValueCLM u)
      ((galerkinProj N φ).val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩)) atTop
      (𝓝 (-inner ℝ (torusHkValueCLM u) (φ.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩))) :=
    (tendsto_const_nhds.inner hg).neg
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun N => (he N).symm))

/-- H¹ value tests recover the integral equation at every reserved Sobolev order. -/
theorem native_torus_strong_time_of_value_pairings {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (U dU : ℝ → TorusHk K E) (hdU : IntervalIntegrable dU volume a b) (hweak : ∀ t ∈ Icc a b, ∀ φ : TorusHk 1 E,
      inner ℝ (torusHkValueCLM (U t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (U a)) (torusHkValueCLM φ) =
        ∫ s in a..t, inner ℝ (torusHkValueCLM (dU s)) (torusHkValueCLM φ)) :
    CycleEvolution.StrongTimeRegularity a b U dU := by
  have hrep (t : ℝ) (ht : t ∈ Icc a b) : U t = U a + ∫ s in a..t, dU s := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    apply torusHk_eq_of_H1_value_pairings K
    intro φ
    let L : TorusHk K E →L[ℝ] ℝ :=
      (innerSL ℝ (torusHkValueCLM φ)).comp torusHkValueCLM
    have hint := L.intervalIntegral_comp_comm (hdU.mono_set hsub)
    have hL (V : TorusHk K E) :
        L V = inner ℝ (torusHkValueCLM V) (torusHkValueCLM φ) :=
      (real_inner_comm (torusHkValueCLM φ) (torusHkValueCLM V)).symm
    have he' : L (U t) = L (U a) + ∫ s in a..t, L (dU s) := by
      simp_rw [hL]
      exact (eq_add_of_sub_eq (hweak t ht φ)).trans (add_comm _ _)
    rw [← hL (U t), ← hL (U a + ∫ s in a..t, dU s)]
    rw [map_add, ← hint]
    exact he'
  have hy : IsLinearIntegralSolution (fun _ => (0 : TorusHk K E →L[ℝ] TorusHk K E))
      dU (U a) a b U := by
    intro t ht
    simpa only [linearRhs, zero_apply, zero_add] using hrep t ht
  have he : linearRhs (fun _ => (0 : TorusHk K E →L[ℝ] TorusHk K E)) dU U = dU := by
    funext t
    exact zero_add _
  have hint : IntervalIntegrable
      (linearRhs (fun _ => (0 : TorusHk K E →L[ℝ] TorusHk K E)) dU U) volume a b := by
    rw [he]
    exact hdU
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  filter_upwards [hy.ae_hasDerivAt hab hint] with t ht
  simpa only [uIcc_of_le hab, he] using ht

/-- Smooth cell tests determine the pointwise primitive when the literal right
hand side has an integrable uniform spatial budget. No pointwise time derivative
is assumed in this recovery step. -/
theorem native_pointwise_primitive_of_cell_tests {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → Vec 2 → E) (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hfp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (f t))
    (hdf : ∀ t ∈ Icc a b, Continuous (df t))
    (hdfp : ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic (df t))
    (hm : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Icc a b} =>
      df z.1.1 z.1.2)) (B : ℝ → ℝ)
    (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x, ‖df t x‖ ≤ B t)
    (hweak : ∀ t ∈ Icc a b, ∀ φ : Vec 2 → E,
      ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      cellInner (f t) φ - cellInner (f a) φ =
        ∫ s in Ioc a t, cellInner (df s) φ) :
    ∀ t ∈ Icc a b, ∀ x,
      f t x - f a x = ∫ s in Ioc a t, df s x := by
  obtain ⟨dq, hdq, heq⟩ := macroWeakTime_extension a b df hm
  let A := fun t x => f a x + ∫ s in Ioc a t, df s x
  have hAa : A a = f a := by ext x; simp [A]
  have hAc (t : ℝ) (ht : t ∈ Icc a b) : Continuous (A t) := by
    have hsub : uIcc a t ⊆ Icc a b := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hi : IntervalIntegrable B volume a t :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hB).mono_set
        (by rw [uIcc_of_le hab]; exact hsub)
    have hmsection (x : Vec 2) : AEStronglyMeasurable (fun s => df s x)
        (volume.restrict (uIoc a t)) := by
      apply ((hdq.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict).congr
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      exact heq (s, x) (hsub (uIoc_subset_uIcc hs))
    have hc : Continuous (fun x => ∫ s in a..t, df s x) :=
      intervalIntegral.continuous_of_dominated_interval hmsection
        (fun x => ae_of_all _ (fun s hs => hb s (hsub (uIoc_subset_uIcc hs)) x))
        hi (ae_of_all _ (fun s hs => hdf s (hsub (uIoc_subset_uIcc hs))))
    apply ((hf a ⟨le_rfl, hab⟩).add hc).congr
    intro x
    exact congrArg (fun y => f a x + y)
      (intervalIntegral.integral_of_le (f := fun s => df s x) (μ := volume) ht.1)
  have hAp (t : ℝ) (ht : t ∈ Icc a b) : AVenhance.IsZ2Periodic (A t) := by
    intro n x
    dsimp only [A]
    rw [hfp a ⟨le_rfl, hab⟩ n x]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs =>
      hdfp s ⟨hs.1.le, hs.2.trans ht.2⟩ n x)
  have hprim : ∀ x, ∀ t ∈ Icc a b, A t x - A a x = ∫ s in Ioc a t, df s x := by
    intro x t _
    rw [congrFun hAa x]
    exact add_sub_cancel_left _ _
  intro t ht
  have he : f t = A t := by
    apply CycleComparison.Lift.periodicContinuous_eq_of_cell_ae _ _
      (hf t ht) (hAc t ht) (hfp t ht) (hAp t ht)
    apply Construction.Preservation.FullLift.hilbert_ae_eq_of_cellInner_eq
      (E := E) (F := f t) (G := A t)
      (AVRegularity.integrableOn_unitCube (hf t ht))
      (AVRegularity.integrableOn_unitCube (hAc t ht))
    intro φ hφ hp
    have hA := (macroWeakTime a b t ht A df φ hφ.continuous hprim
      hm ⟨B, hB, fun s hs x _ => hb s hs x⟩
      (continuous_cell_integrable _ ((hAc t ht).inner hφ.continuous))
      (continuous_cell_integrable _ ((hAc a ⟨le_rfl, hab⟩).inner hφ.continuous))).2.1
    change cellInner (A t) φ - cellInner (A a) φ = ∫ s in Ioc a t, cellInner (df s) φ at hA
    rw [hAa] at hA
    exact sub_left_injective ((hweak t ht φ hφ hp).trans hA.symm)
  intro x
  rw [congrFun he x]
  simpa only [hAa] using hprim x t ht

section CompactLabels
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [T2Space X]

omit [CompleteSpace V] in
/-- Pointwise time measurability and a uniform integrable budget give a genuine
Bochner integrable curve on a compact chart. -/
theorem native_compact_curve_integrable {a b : ℝ} (V : ℝ → C(X, V))
    (hm : ∀ x, Measurable (fun t => V t x)) (B : ℝ → ℝ)
    (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x, ‖V t x‖ ≤ B t) :
    IntegrableOn V (Icc a b) := by
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.mpr hm
  apply hB.norm.mono' hVm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (ContinuousMap.norm_le _ (norm_nonneg (B t))).mpr
    (fun x => (hb t ht x).trans (le_abs_self (B t)))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology X] in
/-- The compact-chart primitive selects one exceptional time set before any
slow or fast evaluation. This step uses a Banach space of continuous functions,
so its exceptional set does not arise from an uncountable intersection. -/
theorem native_compact_time_of_pointwise_primitives {a b : ℝ} (hab : a ≤ b)
    (U dU : ℝ → C(X, V)) (hdU : IntervalIntegrable dU volume a b)
    (hprimitive : ∀ t ∈ Icc a b, ∀ x,
      U t x - U a x = ∫ s in a..t, dU s x) :
    AbsolutelyContinuousOnInterval U a b ∧
    (∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt U (dU t) t) ∧
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x,
      HasDerivAt (fun s => U s x) (dU t x) t := by
  have hrep (t : ℝ) (ht : t ∈ Icc a b) : U t = U a + ∫ s in a..t, dU s := by
    ext x
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hi := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm
      (hdU.mono_set hsub)
    change (∫ s in a..t, dU s x) = (∫ s in a..t, dU s) x at hi
    change U t x = U a x + (∫ s in a..t, dU s) x
    rw [← hi]
    exact (eq_add_of_sub_eq (hprimitive t ht x)).trans (add_comm _ _)
  have hsol : IsLinearIntegralSolution (fun _ => (0 : C(X, V) →L[ℝ] C(X, V)))
      dU (U a) a b U := by
    intro t ht
    simpa only [linearRhs, zero_apply, zero_add] using hrep t ht
  have hrhs : IntervalIntegrable
      (linearRhs (fun _ => (0 : C(X, V) →L[ℝ] C(X, V))) dU U) volume a b := by
    change IntervalIntegrable (fun t => (0 : C(X, V)) + dU t) volume a b
    simpa only [zero_add] using hdU
  have hd := (hsol.ae_hasDerivAt hab hrhs).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict (Icc a b) ≤ volume))
  have hstrong : ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt U (dU t) t := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hh := ht hmem
    change HasDerivAt U ((0 : C(X, V)) + dU t) t at hh
    simpa only [zero_add] using hh
  refine ⟨hsol.absolutelyContinuousOnInterval hab hrhs, hstrong, ?_⟩
  filter_upwards [hstrong] with t ht
  intro x
  exact (ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t ht

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace V] [SecondCountableTopology X] [T2Space X] in
/-- A derivative in the compact-chart norm can be evaluated along a moving
label. The spatial term is differentiated with the time coordinate frozen. -/
theorem native_compact_moving_evaluation
    (U : ℝ → C(X, V)) (dU : C(X, V)) (γ : ℝ → X) (v : V) (t : ℝ)
    (hU : HasDerivAt U dU t) (hγ : ContinuousAt γ t)
    (hspace : HasDerivAt (fun s => U t (γ s)) v t) :
    HasDerivAt (fun s => U s (γ s)) (dU (γ t) + v) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have htime := hU.tendsto_slope.eval
    (hγ.tendsto.mono_left nhdsWithin_le_nhds)
  have he (s : ℝ) : slope (fun r => U r (γ r)) t s =
      (slope U t s) (γ s) + slope (fun r => U t (γ r)) t s := by
    change (s - t)⁻¹ • (U s (γ s) - U t (γ t)) =
      (s - t)⁻¹ • (U s (γ s) - U t (γ s)) +
        (s - t)⁻¹ • (U t (γ s) - U t (γ t))
    rw [← smul_add]
    congr 1
    abel
  exact (htime.add hspace.tendsto_slope).congr'
    (Eventually.of_forall fun s => (he s).symm)

end CompactLabels

section MovingLabels
variable {V X : Type*} [PseudoMetricSpace V] [PseudoMetricSpace X] [CompactSpace X]

/-- Absolute continuity survives evaluation along an absolutely continuous
label curve when the spatial Lipschitz bounds are uniform on the time window. -/
theorem native_compact_moving_evaluation_ac {a b : ℝ} (U : ℝ → C(X, V)) (γ : ℝ → X)
    (hU : AbsolutelyContinuousOnInterval U a b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (L : NNReal)
    (hL : ∀ t ∈ uIcc a b, LipschitzWith L (U t)) :
    AbsolutelyContinuousOnInterval (fun t => U t (γ t)) a b := by
  unfold AbsolutelyContinuousOnInterval at hU hγ ⊢
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero, add_zero] using hU.add (hγ.const_mul (L : ℝ)))
  · exact Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have ht := (hE.left i hi).right
  exact (dist_triangle (U (E.2 i).1 (γ (E.2 i).1))
    (U (E.2 i).2 (γ (E.2 i).1)) (U (E.2 i).2 (γ (E.2 i).2))).trans
    (add_le_add (ContinuousMap.dist_apply_le_dist (γ (E.2 i).1))
      ((hL (E.2 i).2 ht).dist_le_mul _ _))

end MovingLabels

section CompactPrimitiveMotion
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]

/-- Retain the derivative in the compact-chart norm before evaluating a moving
label. Both curves agree with the literal fields throughout the closed window. -/
theorem native_window_compact_primitive_data {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → X → V)
    (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hdf : ∀ t ∈ Icc a b, Continuous (df t))
    (hm : ∀ x, Measurable (fun t => if t ∈ Icc a b then df t x else 0))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x, ‖df t x‖ ≤ B t)
    (hp : ∀ t ∈ Icc a b, ∀ x, f t x - f a x = ∫ s in a..t, df s x) :
    ∃ U dU : ℝ → C(X, V),
      (∀ t ∈ Icc a b, ∀ x, U t x = f t x) ∧
      (∀ t ∈ Icc a b, ∀ x, dU t x = df t x) ∧
      AbsolutelyContinuousOnInterval U a b ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt U (dU t) t := by
  classical
  let U : ℝ → C(X, V) := fun t => if ht : t ∈ Icc a b then ⟨f t, hf t ht⟩ else 0
  let dU : ℝ → C(X, V) := fun t => if ht : t ∈ Icc a b then ⟨df t, hdf t ht⟩ else 0
  have hUeq (t : ℝ) (ht : t ∈ Icc a b) (x : X) : U t x = f t x := by
    simp only [U, dite_eq_left ht, ContinuousMap.coe_mk]
  have hdUeq (t : ℝ) (ht : t ∈ Icc a b) (x : X) : dU t x = df t x := by
    simp only [dU, dite_eq_left ht, ContinuousMap.coe_mk]
  have hdUm (x : X) : Measurable (fun t => dU t x) := by
    convert hm x using 1
    funext t
    by_cases ht : t ∈ Icc a b <;> simp only [dU, ht, ↓reduceDIte, ↓reduceIte,
      ContinuousMap.coe_mk, ContinuousMap.zero_apply]
  have hdUi : IntervalIntegrable dU volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact native_compact_curve_integrable dU hdUm B hB
      (fun t ht x => (hdUeq t ht x).symm ▸ hb t ht x)
  have hUp : ∀ t ∈ Icc a b, ∀ x, U t x - U a x = ∫ s in a..t, dU s x := by
    intro t ht x
    rw [hUeq t ht x, hUeq a ⟨le_rfl, hab⟩ x, hp t ht x]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact (hdUeq s ⟨hs.1, hs.2.trans ht.2⟩ x).symm
  have ht := native_compact_time_of_pointwise_primitives hab U dU hdUi hUp
  exact ⟨U, dU, hUeq, hdUeq, ht.1, ht.2.1⟩

/-- Windowed pointwise primitives and uniform spatial Lipschitz bounds give
absolute continuity after a moving-label evaluation. Only the derivative's
measurable zero extension is used outside the original window. -/
theorem native_window_moving_primitive_ac {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → X → V)
    (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hdf : ∀ t ∈ Icc a b, Continuous (df t))
    (hm : ∀ x, Measurable (fun t => if t ∈ Icc a b then df t x else 0))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Icc a b))
    (hb : ∀ t ∈ Icc a b, ∀ x, ‖df t x‖ ≤ B t)
    (hp : ∀ t ∈ Icc a b, ∀ x, f t x - f a x = ∫ s in a..t, df s x)
    (γ : ℝ → X) (hγ : AbsolutelyContinuousOnInterval γ a b) (L : NNReal)
    (hL : ∀ t ∈ Icc a b, LipschitzWith L (f t)) :
    AbsolutelyContinuousOnInterval (fun t => f t (γ t)) a b := by
  obtain ⟨U, _dU, hUeq, _hdUeq, hAC, _hd⟩ :=
    native_window_compact_primitive_data hab f df hf hdf hm B hB hb hp
  have hLip (t : ℝ) (ht : t ∈ uIcc a b) : LipschitzWith L (U t) := by
    rw [uIcc_of_le hab] at ht
    have he : (U t : X → V) = f t := funext (hUeq t ht)
    rw [he]
    exact hL t ht
  have hmove := native_compact_moving_evaluation_ac U γ hAC hγ L hLip
  apply hmove.congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact hUeq t ht (γ t)

end CompactPrimitiveMotion

section GlobalWindowMotion
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
  [NormedAddCommGroup W] [ProperSpace W] [SecondCountableTopology W]

/-- Compact spatial budgets for a pointwise primitive give a common moving-label
rule. The time budget can be integrable rather than uniformly bounded. -/
theorem native_window_global_moving_derivative {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → W → V)
    (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hdf : ∀ t ∈ Icc a b, Continuous (df t))
    (hm : ∀ x, Measurable (fun t => if t ∈ Icc a b then df t x else 0))
    (hbudget : ∀ K : Set W, IsCompact K → ∃ B : ℝ → ℝ,
      IntegrableOn B (Icc a b) ∧ ∀ t ∈ Icc a b, ∀ x ∈ K, ‖df t x‖ ≤ B t)
    (hp : ∀ t ∈ Icc a b, ∀ x, f t x - f a x = ∫ s in Ioc a t, df s x) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ γ : ℝ → W, ∀ w : V,
      ContinuousAt γ t → HasDerivAt (fun s => f t (γ s)) w t →
      HasDerivAt (fun s => f s (γ s)) (df t (γ t) + w) t := by
  classical
  let K (n : ℕ) := Metric.closedBall (0 : W) (n : ℝ)
  have hlocal (n : ℕ) : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ γ : ℝ → K n, ∀ w : V,
      ContinuousAt γ t → HasDerivAt (fun s => f t (γ s)) w t →
      HasDerivAt (fun s => f s (γ s)) (df t (γ t) + w) t := by
    let nativeWindowMovingChart : CompactSpace (K n) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    obtain ⟨B, hB, hb⟩ := hbudget (K n) (isCompact_closedBall _ _)
    obtain ⟨U, dU, hUeq, hdUeq, _hAC, hd⟩ := native_window_compact_primitive_data hab
      (fun t (x : K n) => f t x) (fun t (x : K n) => df t x)
      (fun t ht => (hf t ht).comp continuous_subtype_val)
      (fun t ht => (hdf t ht).comp continuous_subtype_val)
      (fun x => hm x) B hB (fun t ht x => hb t ht x x.2)
      (fun t ht x => (hp t ht x).trans
        (intervalIntegral.integral_of_le (f := fun s => df s x) (μ := volume) ht.1).symm)
    have hinside : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo a b := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hd, hinside] with t ht hti
    intro γ w hγ hspace
    have htcc := Ioo_subset_Icc_self hti
    have hfixed : HasDerivAt (fun s => U t (γ s)) w t := by
      simpa only [hUeq t htcc] using hspace
    have hmove := native_compact_moving_evaluation U (dU t) γ w t ht hγ hfixed
    rw [hdUeq t htcc (γ t)] at hmove
    apply hmove.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
    exact (hUeq s (Ioo_subset_Icc_self hs) (γ s)).symm
  filter_upwards [ae_all_iff.mpr hlocal] with t ht
  intro γ w hγ hw
  obtain ⟨n, hn⟩ := exists_nat_gt ‖γ t‖
  have hγt : γ t ∈ K n := mem_closedBall_zero_iff.mpr hn.le
  have hnear : ∀ᶠ s in 𝓝 t, γ s ∈ K n := by
    have hb : Metric.ball (0 : W) (n : ℝ) ∈ 𝓝 (γ t) :=
      Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hn)
    exact Filter.Eventually.mono (hγ hb) (fun _ hs => Metric.ball_subset_closedBall hs)
  let γ' : ℝ → K n := fun s => ⟨if hs : γ s ∈ K n then γ s else γ t,
    by split_ifs with hs; exact hs; exact hγt⟩
  have he : (fun s => (γ' s).1) =ᶠ[𝓝 t] γ := by
    filter_upwards [hnear] with s hs
    exact dite_eq_left hs
  have hγ' : ContinuousAt γ' t := (hγ.congr_of_eventuallyEq he).codRestrict _
  have hw' : HasDerivAt (fun s => f t (γ' s)) w t :=
    hw.congr_of_eventuallyEq (he.mono (fun s hs => by change (γ' s).1 = γ s at hs; dsimp only; rw [hs]))
  have hd := ht n γ' w hγ' hw'
  have het : (γ' t).1 = γ t := dite_eq_left hγt
  rw [het] at hd
  exact hd.congr_of_eventuallyEq (he.mono (fun s hs => by
    change (γ' s).1 = γ s at hs; dsimp only; rw [hs]))

/-- Moving evaluation preserves absolute continuity on the original window.
Only compact spatial budgets are used for the time derivative. -/
theorem native_window_global_moving_ac {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → W → V)
    (hf : ∀ t ∈ Icc a b, Continuous (f t))
    (hdf : ∀ t ∈ Icc a b, Continuous (df t))
    (hm : ∀ x, Measurable (fun t => if t ∈ Icc a b then df t x else 0))
    (hbudget : ∀ K : Set W, IsCompact K → ∃ B : ℝ → ℝ,
      IntegrableOn B (Icc a b) ∧ ∀ t ∈ Icc a b, ∀ x ∈ K, ‖df t x‖ ≤ B t)
    (hp : ∀ t ∈ Icc a b, ∀ x, f t x - f a x = ∫ s in Ioc a t, df s x)
    (γ : ℝ → W) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (L : NNReal) (hL : ∀ t ∈ Icc a b, LipschitzWith L (f t)) :
    AbsolutelyContinuousOnInterval (fun t => f t (γ t)) a b := by
  classical
  have hgc : ContinuousOn γ (Icc a b) := by
    simpa only [uIcc_of_le hab] using hγ.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let K := Metric.closedBall (0 : W) R
  let nativeWindowACChart : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let Γ : ℝ → K := fun s => ⟨γ (projIcc a b hab s),
    mem_closedBall_zero_iff.mpr (hR _ (projIcc a b hab s).2)⟩
  have he (s : ℝ) (hs : s ∈ Icc a b) : (Γ s).1 = γ s := by
    dsimp only [Γ]
    rw [projIcc_of_mem hab hs]
  have hΓ : AbsolutelyContinuousOnInterval Γ a b := by
    have hg' : AbsolutelyContinuousOnInterval (fun s => (Γ s).1) a b :=
      hγ.congr (fun s hs => (he s (by simpa only [uIcc_of_le hab] using hs)).symm)
    simpa only [AbsolutelyContinuousOnInterval, Subtype.dist_eq] using hg'
  obtain ⟨B, hB, hb⟩ := hbudget K (isCompact_closedBall _ _)
  have hmove := native_window_moving_primitive_ac hab
    (fun t (x : K) => f t x) (fun t (x : K) => df t x)
    (fun t ht => (hf t ht).comp continuous_subtype_val)
    (fun t ht => (hdf t ht).comp continuous_subtype_val)
    (fun x => hm x) B hB (fun t ht x => hb t ht x x.2)
    (fun t ht x => (hp t ht x).trans
      (intervalIntegral.integral_of_le (f := fun s => df s x) (μ := volume) ht.1).symm)
    Γ hΓ L (fun t ht => by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Subtype.dist_eq] using (hL t ht).dist_le_mul x.1 y.1)
  exact hmove.congr (fun t ht => by
    dsimp only
    rw [he t (by simpa only [uIcc_of_le hab] using ht)])

end GlobalWindowMotion

section BanachTimeCalculus
variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A bounded bilinear operation preserves absolute continuity in the native
Banach norms, including the multilinear spatial jet spaces. -/
theorem native_bilinear_time_ac {a b : ℝ} (B : V →L[ℝ] W →L[ℝ] Z)
    {f : ℝ → V} {g : ℝ → W}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => B (f t) (g t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg ⊢
  apply squeeze_zero' ?_ ?_
    (by simpa only [mul_zero, add_zero] using
      (hg.const_mul (‖B‖ * C)).add (hf.const_mul (‖B‖ * D)))
  · exact Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hl := (hE.left i hi).left
  have hr := (hE.left i hi).right
  apply (dist_triangle (B (f (E.2 i).1) (g (E.2 i).1))
    (B (f (E.2 i).1) (g (E.2 i).2)) (B (f (E.2 i).2) (g (E.2 i).2))).trans
  apply add_le_add
  · rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((B (f (E.2 i).1)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hC _ hl) (norm_nonneg _))) (norm_nonneg _))
  · rw [dist_eq_norm, ← sub_apply, ← map_sub, dist_eq_norm]
    calc
      ‖B (f (E.2 i).1 - f (E.2 i).2) (g (E.2 i).2)‖ ≤
          ‖B (f (E.2 i).1 - f (E.2 i).2)‖ * ‖g (E.2 i).2‖ := (B _).le_opNorm _
      _ ≤ (‖B‖ * ‖f (E.2 i).1 - f (E.2 i).2‖) * ‖g (E.2 i).2‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖B‖ * ‖f (E.2 i).1 - f (E.2 i).2‖) * D :=
        mul_le_mul_of_nonneg_left (hD _ hr) (mul_nonneg (norm_nonneg B) (norm_nonneg _))
      _ = (‖B‖ * D) * ‖f (E.2 i).1 - f (E.2 i).2‖ := by ring

/-- The Banach-valued time increment follows by scalar duality from absolute
continuity and its chosen integrable strong derivative. -/
theorem native_banach_time_increment [CompleteSpace V] {a b : ℝ} (U dU : ℝ → V)
    (hU : AbsolutelyContinuousOnInterval U a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt U (dU t) t)
    (hi : IntervalIntegrable dU volume a b) :
    U b - U a = ∫ s in a..b, dU s := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hL : AbsolutelyContinuousOnInterval (fun t => L (U t)) a b :=
    L.lipschitzWith.comp_absolutelyContinuousOnInterval hU
  have he : (fun t => deriv (fun s => L (U s)) t) =ᵐ[volume.restrict (uIoc a b)]
      (fun t => L (dU t)) := by
    filter_upwards [hd.filter_mono (ae_mono
      (Measure.restrict_mono uIoc_subset_uIcc le_rfl))] with t ht
    exact (L.hasFDerivAt.comp_hasDerivAt t ht).deriv
  rw [map_sub, ← hL.integral_deriv_eq_sub, intervalIntegral.integral_congr_ae_restrict he]
  exact L.intervalIntegral_comp_comm hi

/-- In a finite-dimensional target, absolute continuity makes any chosen strong
 time derivative integrable. Scalar coordinate derivatives supply the estimate. -/
theorem native_finite_time_derivative_integrable [FiniteDimensional ℝ V]
    {a b : ℝ} (U dU : ℝ → V) (hU : AbsolutelyContinuousOnInterval U a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt U (dU t) t) :
    IntervalIntegrable dU volume a b := by
  classical
  let e := (Module.finBasis ℝ V).equivFunL
  have hcoord (i : Fin (Module.finrank ℝ V)) :
      IntervalIntegrable (fun t => e (dU t) i) volume a b := by
    let L : V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    have hL : AbsolutelyContinuousOnInterval (fun t => L (U t)) a b :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hU
    apply hL.intervalIntegrable_deriv.congr_ae
    filter_upwards [hd.filter_mono (ae_mono
      (Measure.restrict_mono uIoc_subset_uIcc le_rfl))] with t ht
    exact (L.hasFDerivAt.comp_hasDerivAt t ht).deriv
  have hi : IntervalIntegrable (fun t => e (dU t)) volume a b := by
    rw [intervalIntegrable_iff]
    exact Integrable.of_eval (fun i => (hcoord i).def')
  have hr := e.symm.toContinuousLinearMap.integrable_comp hi.def'
  apply intervalIntegrable_iff.mpr
  change Integrable dU (volume.restrict (uIoc a b))
  change Integrable (fun t => e.symm (e (dU t))) (volume.restrict (uIoc a b)) at hr
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr

/-- A finite-dimensional absolutely continuous curve has the primitive of its
chosen derivative, with no separate integrability hypothesis. -/
theorem native_finite_time_increment [FiniteDimensional ℝ V] [CompleteSpace V]
    {a b : ℝ} (U dU : ℝ → V) (hU : AbsolutelyContinuousOnInterval U a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt U (dU t) t) :
    U b - U a = ∫ s in a..b, dU s :=
  native_banach_time_increment U dU hU hd
    (native_finite_time_derivative_integrable U dU hU hd)

/-- A finite sum of native Banach time curves remains absolutely continuous. -/
theorem native_time_finset_sum {ι : Type*} (S : Finset ι) {a b : ℝ}
    (f : ι → ℝ → V) (hf : ∀ i ∈ S, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ S, f i t) a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (contDiff_const (c := (0 : V)) : ContDiff ℝ 1 (fun _ : ℝ => (0 : V))).contDiffOn.absolutelyContinuousOnInterval
  | @insert i S hi ih =>
    apply ((hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).congr
    intro t _
    exact (Finset.sum_insert (f := fun j => f j t) hi).symm

/-- Constant extension of a time primitive across its window has exactly the
windowed derivative; in particular it introduces no outside-window premise. -/
theorem native_window_clamp_increment [CompleteSpace V] {a b : ℝ} (hab : a ≤ b)
    (f df : ℝ → V) (hi : IntegrableOn df (Icc a b))
    (hp : ∀ t ∈ Icc a b, f t - f a = ∫ s in Ioc a t, df s)
    (s t : ℝ) :
    f (projIcc a b hab t) - f (projIcc a b hab s) =
      ∫ r in s..t, (Ioc a b).indicator df r := by
  classical
  let d := (Ioc a b).indicator df
  have hd : Integrable d := (integrable_indicator_iff measurableSet_Ioc).mpr
    (hi.mono_set Ioc_subset_Icc_self)
  have he (r : ℝ) : f (projIcc a b hab r) - f a = ∫ u in a..r, d u := by
    rcases le_or_gt r a with hra | har
    · rw [projIcc_of_le_left hab hra, sub_self]
      symm
      calc
        (∫ u in a..r, d u) = ∫ u in a..r, (0 : V) := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
          rw [uIoc_of_ge hra] at hu
          exact indicator_of_notMem (s := Ioc a b) (fun h => (not_lt.mpr hu.2) h.1) df
        _ = 0 := intervalIntegral.integral_zero
    · rcases le_or_gt r b with hrb | hbr
      · rw [projIcc_of_mem hab ⟨har.le, hrb⟩, hp r ⟨har.le, hrb⟩,
          ← intervalIntegral.integral_of_le har.le]
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
        rw [uIoc_of_le har.le] at hu
        exact (indicator_of_mem (s := Ioc a b) ⟨hu.1, hu.2.trans hrb⟩ df).symm
      · rw [projIcc_of_right_le hab hbr.le, hp b ⟨hab, le_rfl⟩,
          ← intervalIntegral.integral_of_le hab]
        have hz : (∫ u in b..r, d u) = 0 := by
          calc
            (∫ u in b..r, d u) = ∫ u in b..r, (0 : V) := by
              apply intervalIntegral.integral_congr_ae_restrict
              filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
              rw [uIoc_of_le hbr.le] at hu
              exact indicator_of_notMem (s := Ioc a b) (fun h => (not_le.mpr hu.1) h.2) df
            _ = 0 := intervalIntegral.integral_zero
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hd.intervalIntegrable hd.intervalIntegrable, hz, add_zero]
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
        rw [uIoc_of_le hab] at hu
        exact (indicator_of_mem (s := Ioc a b) hu df).symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hd.intervalIntegrable (a := a) (b := s)) (hd.intervalIntegrable (a := s) (b := t))
  rw [← he s, ← he t] at hadd
  exact sub_eq_iff_eq_add.mpr (by
    calc
      f (projIcc a b hab t) = (f (projIcc a b hab s) - f a + ∫ r in s..t, d r) + f a := by
        rw [hadd, sub_add_cancel]
      _ = (∫ r in s..t, d r) + f (projIcc a b hab s) := by abel)

end BanachTimeCalculus

end NativeEarlyWeakCalculus

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
