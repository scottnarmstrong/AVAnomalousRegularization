-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.NativePiolaJetRowEquality
public import AVRegularity.Weighted.ScaledDriftNormAbsorption
import AVRegularity.CycleJoint.CellDriftWindowMeasurable
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
public import AVRegularity.Statements.Intermediate.CycleJoint.IsWindowCover
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Spatial cell dilation transfers the full actual coupled weak solution class, including higher traces and forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_affine (K : ι → ℕ) (D : ℕ) (ν a b e : ℝ)
    (he : e ≠ 0) (y : Vec 2) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane (ν * (e⁻¹) ^ 2) a b
      (fun t z => e⁻¹ • v t (y + e • z)) D K
      (fun i i' d t z => (e⁻¹ * (e ^ (d.1 - 1))⁻¹) • A i i' d t (y + e • z))
      (fun i => planeCarrierAffine e he y (f i))
      (fun i t => e⁻¹ • planeCarrierAffine e he y (F i t))
      (fun i t => planeCarrierAffine e he y (g i t))
      (fun i t => planeCarrierAffine e he y (u i t))
      (fun i t => planeCarrierAffine e he y (w i t)) := by
  refine ⟨fun i => (planeCarrierAffineOperator (K i) e he y).continuous.comp_continuousOn (hs.1 i),
    fun i => (planeCarrierAffineOperator (K i + 1) e he y).comp_memLp' (hs.2.1 i), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i] with t ht
    rw [← planeCarrierAffine_truncate, ht]
  · intro i
    change planeCarrierAffine e he y (u i a) = planeCarrierAffine e he y (f i)
    rw [hs.2.2.2.1 i]
  · intro i t ht φ
    let p := φ.toFunction.jet (valueIndex2 1)
    let dp := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    let ψ := planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • y)) φ
    let du := fun r k => (w i r).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    let Q := fun r => planeRawCouplingFlux K D r A (fun j => w j r) i
    let ff := fun r => (F i r).toFunction.jet (valueIndex2 (K i))
    let gg := fun r => (g i r).toFunction.jet (valueIndex2 (K i))
    have hcoord (x : Vec 2) : -(e⁻¹ • y) + e⁻¹ • x = e⁻¹ • (x - y) := by
      rw [smul_sub]
      abel
    have hp : ψ.toFunction.jet (valueIndex2 1) =ᵐ[volume]
        fun x => p (e⁻¹ • (x - y)) := by
      simpa only [ψ, p, valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul, hcoord] using
        planeCarrierAffine_jet_ae e⁻¹ (inv_ne_zero he) (-(e⁻¹ • y)) φ (valueIndex2 1)
    have hdp (k : Fin 2) : ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ =ᵐ[volume]
        fun x => e⁻¹ • dp k (e⁻¹ • (x - y)) := by
      simpa only [pow_one, hcoord] using planeCarrierAffine_jet_ae e⁻¹ (inv_ne_zero he)
        (-(e⁻¹ • y)) φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    have hold := hs.2.2.2.2 i t ht ψ
    simp only [Measure.restrict_univ] at hold ⊢
    have hideal := coupledWeakIdentity_test_congr volume ν a t v
      ((u i t).toFunction.jet (valueIndex2 (K i))) ((f i).toFunction.jet (valueIndex2 (K i)))
      _ (fun x => p (e⁻¹ • (x - y))) _ (fun k x => e⁻¹ • dp k (e⁻¹ • (x - y)))
      du Q ff gg hp hdp hold
    have htr := coupledWeakIdentity_affine_inverse_test ν a t e he y v
      ((u i t).toFunction.jet (valueIndex2 (K i))) ((f i).toFunction.jet (valueIndex2 (K i)))
      p dp du Q ff gg hideal
    let du' := fun r k => (planeCarrierAffine e he y (w i r)).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    let Q' := fun r => planeRawCouplingFlux K D r
      (fun j j' d s z => (e⁻¹ * (e ^ (d.1 - 1))⁻¹) • A j j' d s (y + e • z))
      (fun j => planeCarrierAffine e he y (w j r)) i
    let ff' := fun r => (e⁻¹ • planeCarrierAffine e he y (F i r)).toFunction.jet (valueIndex2 (K i))
    let gg' := fun r => (planeCarrierAffine e he y (g i r)).toFunction.jet (valueIndex2 (K i))
    apply coupledWeakIdentity_integrands_congr volume (ν * (e⁻¹) ^ 2) a t
      (fun r z => e⁻¹ • v r (y + e • z)) (fun r z => e⁻¹ • v r (y + e • z))
      _ _ _ _ p p dp dp (fun r k z => e • du r k (y + e • z)) du'
      (fun r z => e⁻¹ • Q r (y + e • z)) Q' (fun r z => e⁻¹ • ff r (y + e • z)) ff'
      (fun r z => gg r (y + e • z)) gg' _ _ _ htr
    · filter_upwards [planeCarrierAffine_jet_ae e he y (u i t) (valueIndex2 (K i))] with z hz
      simpa only [valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul] using congrArg (fun v => inner ℝ v (p z)) hz.symm
    · filter_upwards [planeCarrierAffine_jet_ae e he y (f i) (valueIndex2 (K i))] with z hz
      simpa only [valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul] using congrArg (fun v => inner ℝ v (p z)) hz.symm
    · intro r _
      apply weakIdentityRhs_congr_ae volume (ν * (e⁻¹) ^ 2) r _ _ p p dp dp
        (fun r k z => e • du r k (y + e • z)) du' (fun r z => e⁻¹ • Q r (y + e • z)) Q'
        (fun r z => e⁻¹ • ff r (y + e • z)) ff' (fun r z => gg r (y + e • z)) gg'
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
      · intro k
        simpa only [pow_one] using (planeCarrierAffine_jet_ae e he y (w i r)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩).symm
      · exact (planeRawCouplingFlux_affine_inverse_ae K D r e he y A (fun j => w j r) i).symm
      · filter_upwards [planeCarrier_jet_smul_ae e⁻¹ (planeCarrierAffine e he y (F i r)) (valueIndex2 (K i)),
          planeCarrierAffine_jet_ae e he y (F i r) (valueIndex2 (K i))] with z hs hz
        have hz' : (planeCarrierAffine e he y (F i r)).toFunction.jet (valueIndex2 (K i)) z =
            (F i r).toFunction.jet (valueIndex2 (K i)) (y + e • z) := by
          simpa only [valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul] using hz
        change e⁻¹ • (F i r).toFunction.jet (valueIndex2 (K i)) (y + e • z) =
          (e⁻¹ • planeCarrierAffine e he y (F i r)).toFunction.jet (valueIndex2 (K i)) z
        rw [hs, hz']
      · simpa only [gg, gg', valueIndex2, valueIndex, Fin.val_zero, pow_zero, one_smul] using
          (planeCarrierAffine_jet_ae e he y (g i r) (valueIndex2 (K i))).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The metric produced by the genuine reference/time/cell transfer agrees
with the construction's cell metric, including its physical time scaling. -/

theorem preparationReferenceCellMetric_eq_ocCellMetric
    (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (ν : ℝ) (hν : 0 < ν) (yc : Vec 2) :
    (fun t z => chartMetric hφ ((l : ℝ) * ocTauPP α q Λ m)
      (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * t)) (yc + ocEpsilon q Λ m • z)) =
      ocCellMetric α q Λ m φ hφ l ν yc := by
  funext t z
  have ht : ocEll q Λ m ν ^ 2 * t = ν⁻¹ * (ocEpsilon q Λ m ^ 2 * t) := by
    rw [ocEll_sq_eq hν, div_eq_mul_inv]
    ac_rfl
  unfold ocCellMetric
  rw [ht]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Every source flux of positive derivative order annihilates a constant component family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem torusConstantCouplingFlux_zero_ae (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (c : ∀ i, h i) (i : ι) :
    torusRawCouplingFlux K D r A (fun j => torusConstantCarrier (K j + 1) (c j)) i
      =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have hwords : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j,
      ∀ d : admissibleOrders K D i j, ∀ word : DerivativeWord2 (d.1 - 1),
      (torusConstantCarrier (K j + 1) (c j)).toFunction.jet
        ⟨⟨d.1 - 1, Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D i j d)⟩,
          word⟩ x = 0 := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro d
    rw [ae_all_iff]
    intro word
    apply torusConstantCarrier_raw_positive_ae
    have hd := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).1
    change 0 < d.val - 1
    omega
  filter_upwards [hwords] with x hx
  have ht (j : ι) (d : admissibleOrders K D i j) :
      (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
        (torusConstantCarrier (K j + 1) (c j)).toFunction.jet
          ⟨⟨d.1 - 1, Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D i j d)⟩,
            word⟩ x)) = 0 := by
    apply PiLp.ext
    intro word
    exact hx j d word
  simp only [torusRawCouplingFlux, ht, map_zero, Finset.sum_const_zero, Pi.zero_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Fourth response moments give a genuine integrable time curve of periodized weak flux pairings. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem periodized_coefficient_pairing_time_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    Integrable (fun t => ∫ x, inner ℝ (C t x (periodizeRawJet (f t).toFunction.jet α x))
      (φ.toFunction.jet β x)) μ := by
  let g := restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  let p := fun n : Fin 2 → ℤ =>
    (MC * (1 + R + ‖z‖) ^ 4 * ‖g‖) * (1 / spatialLatticeWeight n) ^ 2
  let G := fun (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)
  have hm (n : Fin 2 → ℤ) : AEStronglyMeasurable (G n) μ :=
    (translated_coefficient_pairing_time_integrable μ C hc hj MC hMC hC
      f hf (AVenhance.latticeShift n) α φ β).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ n, ‖G n t‖ ≤ p n * ‖M t‖ := by
    filter_upwards [hw, hb] with t ht hbt
    intro n
    rw [show G n t = _ from translated_compact_coefficient_pairing U (AVenhance.latticeShift n)
      (C t) (hc t) hMC (hC t) (f t) α φ β hφ]
    have he := localImage_coefficient_pairing_radial_bound U R hR hU z α
      (C t) (hc t) MC hMC (hC t) (f t) g ‖M t‖ (norm_nonneg _) ht hbt n
    convert he using 1
    dsimp only [p]
    ring
  have hsum : MemLp (fun t => ∑' n, G n t) 2 μ :=
    memLp_tsum_of_summable_majorant μ G hm p
      (spatialLatticeReciprocal_square_summable.mul_left _) M hM hbound
  apply (hsum.integrable (by norm_num)).congr
  filter_upwards [hw, hb] with t ht hbt
  exact summed_compact_coefficient_pairing U (C t) (hc t) hMC (hC t) (f t) α φ β hφ
    (planeImageJetCLM_radial_enorm_tsum_lt_top U R hR hU z α (f t) ‖M t‖
      (norm_nonneg _) ht hbt)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The scalar native row coefficients of one actual dimensional family piece. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def pieceTransportedNativeScalarJetCoefficient
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (J : ℕ) (k : Fin 2) : JetIndex2 J → Vec 2 → ℝ :=
  transportedNativeScalarJetCoefficient ((F.piece p).material t)
    (F.identity v u γ).maxOrder
    (pieceDimensionalNativeJetArray F ν e E p c v u γ t) k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Exact homogeneous coupled plane trace increments on the physical time window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A homogeneous plane solution (zero source) gives exact raw increments between any two window
times. -/
theorem planeHomogeneous_trace_increment {a b ν : ℝ} (hab : a ≤ b)
    (K : ι → ℕ) (D : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsln : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (φ : PlaneHk Set.univ 1 (h i)) :
    inner ℝ (coupledPlaneL2Trace u i t) (planeHkValueOperator (E := h i) 1 φ) -
      inner ℝ (coupledPlaneL2Trace u i s) (planeHkValueOperator (E := h i) 1 φ) =
      ∫ r in s..t, ∫ x, planeWeakSpatialRhs ν v
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r k => (w i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r => planeRawCouplingFlux K D r A (fun i => w i r) i)
        (fun _ _ => 0) (fun _ _ => 0) r x := by
  rw [coupledPlaneL2Trace_inner, coupledPlaneL2Trace_inner]
  have he := coupledWeakIdentity_fixed_increment (volume.restrict Set.univ) hab v
    (fun r => (u i r).toFunction.jet (valueIndex2 (K i)))
    ((f i).toFunction.jet (valueIndex2 (K i)))
    (φ.toFunction.jet (valueIndex2 1))
    (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r k => (w i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r => planeRawCouplingFlux K D r A (fun i => w i r) i)
    (fun _ => (0 : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))).toFunction.jet
      (valueIndex2 (K i)))
    (fun _ => (0 : PlaneHk Set.univ (K i) (h i)).toFunction.jet (valueIndex2 (K i)))
    (fun r hr => hsln.2.2.2.2 i r hr φ) hs ht
  simp only [Measure.restrict_univ] at he
  refine he.trans ?_
  apply intervalIntegral.integral_congr
  intro r _
  apply integral_congr_ae
  filter_upwards [planeZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i))
    (K i) (valueIndex2 (K i)), planeZero_rawJet_ae (E := h i) (K i) (valueIndex2 (K i))]
    with x hF hg
  simp only [planeWeakSpatialRhs, hF, hg, Pi.zero_apply, PiLp.zero_apply,
    add_zero, inner_zero_left]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The complete native constituent flux transfers exactly between two charts, including every original positive source order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteFlux_matrix_product (M J : Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin 2 → E) (k : Fin 2) :
    (∑ i : Fin 2, (M * J) k i • R i) =
      ∑ j : Fin 2, M k j • ∑ i : Fin 2, J j i • R i := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem transportedNativeScalarJetCoefficient_reference_flux {K : ℕ}
    (P X : Vec 2 ≃ₜ Vec 2)
    (hP : ContDiff ℝ (⊤ : ℕ∞) ⇑P) (hYP : ContDiff ℝ (⊤ : ℕ∞) ⇑P.symm)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hYX : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) (k : Fin 2) :
    (∑ z : JetIndex2 K,
      transportedNativeScalarJetCoefficient (P.trans X.symm) D B k z y •
        orderedDerivative z.2 f y) =
      ∑ j : Fin 2, (chartJacobian ⇑X y)⁻¹ k j •
        ∑ z : JetIndex2 K, transportedNativeScalarJetCoefficient P D B j z (X y) •
          orderedDerivative z.2 (f ∘ ⇑X.symm) (X y) := by
  rw [transportedNativeScalarJetCoefficient_flux_rows (P.trans X.symm)
    (hYX.comp hP) (hYP.comp hX) D hD B f hf y k]
  simp_rw [transportedNativeScalarJetCoefficient_flux_rows P hP hYP D hD B
    (f ∘ ⇑X.symm) (hf.comp hYX) (X y)]
  rw [chartInvJacobian_reference_transition P X (hP.differentiable (by simp))
    (hYP.differentiable (by simp)) (hX.differentiable (by simp))
    (hYX.differentiable (by simp)) y]
  exact finiteFlux_matrix_product _ _ _ k
end

/-! Original and transported scalar native jet rows retain the actual spatial coefficient smoothness. -/

theorem nativeSourceScalarJetCoefficient_smooth {J : ℕ} (D n : ℕ)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (hB : ∀ r I, ContDiff ℝ (n : ℕ) (B r I)) (k : Fin 2) (j : JetIndex2 J) :
    ContDiff ℝ (n : ℕ) (nativeSourceScalarJetCoefficient D B k j) := by
  classical
  unfold nativeSourceScalarJetCoefficient
  by_cases hj : 1 ≤ j.1.val ∧ j.1.val < D
  · simp only [ite_eq_left hj]
    exact contDiff_pi.mp (hB j.1.val j.2) k
  · simp only [ite_eq_right hj]
    exact contDiff_const

theorem transportedNativeScalarJetCoefficient_smooth {J : ℕ}
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm) (D n : ℕ)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (hB : ∀ r I, ContDiff ℝ (n : ℕ) (B r I)) (k : Fin 2) (j : JetIndex2 J) :
    ContDiff ℝ (n : ℕ) (transportedNativeScalarJetCoefficient X D B k j) := by
  classical
  unfold transportedNativeScalarJetCoefficient
  by_cases hj : 1 ≤ j.1.val ∧ j.1.val < D
  · simp only [ite_eq_left hj]
    apply transportedCoeff_spatial_smooth (chartInvJacobian ⇑X.symm)
      (chartInvJacobian_homeomorph_smooth X hX hY) D n
      (fun d I x => B (d - 1) I (X.symm x))
    intro d I i
    exact contDiff_pi.mp ((hB (d - 1) I).comp (hY.of_le (by simp))) i
  · simp only [ite_eq_right hj]
    exact contDiff_const

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual weak flux pairings pass through all integer images and the time integral. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem translated_coefficient_pairing_spacetime_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    (∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) ∂μ) =
      ∫ t, (∫ x, inner ℝ (C t x (periodizeRawJet (f t).toFunction.jet α x))
        (φ.toFunction.jet β x)) ∂μ := by
  have hi (n : Fin 2 → ℤ) := translated_coefficient_pairing_time_integrable
    μ C hc hj MC hMC hC f hf (AVenhance.latticeShift n) α φ β
  have hs := translated_coefficient_pairing_time_summable μ U R hR hU C hc hj MC hMC hC
    f hf z α φ β hφ M hM hw hb
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  filter_upwards [hw, hb] with t ht hbt
  exact summed_compact_coefficient_pairing U (C t) (hc t) hMC (hC t) (f t) α φ β hφ
    (planeImageJetCLM_radial_enorm_tsum_lt_top U R hR hU z α (f t) ‖M t‖
      (norm_nonneg _) ht hbt)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal integrated homogeneous weak atoms for the plane and torus family lifts. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeHomogeneousIntegralAtom (K : ι → ℕ) (D : ℕ) (ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) (j : Fin 3) (s : ℝ) : ℝ :=
  homogeneousWeakRhsIntegralAtom volume ν v (ψ.toFunction.jet (valueIndex2 1))
    (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
    (fun t k => (w i t).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
    (fun t => AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux K D t A
      (fun i => w i t) i) j s

def torusHomogeneousIntegralAtom (K : ι → ℕ) (D : ℕ) (ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) (j : Fin 3) (s : ℝ) : ℝ :=
  homogeneousWeakRhsIntegralAtom volume ν v (ψ.toFunction.jet (valueIndex2 1))
    (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
    (fun t k => (w i t).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
    (fun t => AVRegularity.CoupledEnergy.Variational.torusRawCouplingFlux K D t A
      (fun i => w i t) i) j s
end

/-! The literal integrated atoms depend only on the row coefficient values at their time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ) (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (A A' : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))

theorem planeHomogeneousIntegralAtom_coefficients_congr
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) (j : Fin 3) (s : ℝ)
    (hA : ∀ i' d, A i i' d s = A' i i' d s) :
    planeHomogeneousIntegralAtom K D ν v A w i ψ j s =
      planeHomogeneousIntegralAtom K D ν v A' w i ψ j s := by
  have hflux : AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux K D s A
      (fun i => w i s) i =
      AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux K D s A' (fun i => w i s) i := by
    funext x
    unfold AVRegularity.CoupledEnergyPlane.Variational.planeRawCouplingFlux
    apply Finset.sum_congr rfl
    intro i' _
    apply Finset.sum_congr rfl
    intro d _
    rw [hA i' d]
  unfold planeHomogeneousIntegralAtom homogeneousWeakRhsIntegralAtom
  split_ifs
  · rfl
  · rfl
  · simp only [hflux]

theorem torusHomogeneousIntegralAtom_coefficients_congr
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) (j : Fin 3) (s : ℝ)
    (hA : ∀ i' d, A i i' d s = A' i i' d s) :
    torusHomogeneousIntegralAtom K D ν v A w i ψ j s =
      torusHomogeneousIntegralAtom K D ν v A' w i ψ j s := by
  have hflux : AVRegularity.CoupledEnergy.Variational.torusRawCouplingFlux K D s A
      (fun i => w i s) i =
      AVRegularity.CoupledEnergy.Variational.torusRawCouplingFlux K D s A' (fun i => w i s) i := by
    funext x
    unfold AVRegularity.CoupledEnergy.Variational.torusRawCouplingFlux
    apply Finset.sum_congr rfl
    intro i' _
    apply Finset.sum_congr rfl
    intro d _
    rw [hA i' d]
  unfold torusHomogeneousIntegralAtom homogeneousWeakRhsIntegralAtom
  split_ifs
  · rfl
  · rfl
  · simp only [hflux]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A fixed finite-order price controls every lower native coordinate array,
without depending on a family's identities or physical scales. -/

def nativeArrayCoordinatePrice (D : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (D + 1), (Fintype.card (Fin 2 × DerivativeWord2 r) : ℝ)

def boundedTransportedPolynomialReservePrice (N D Kmax : ℕ) (C : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Kmax + 1), transportedPolynomialUniformReservePrice N D k C

def nativeArrayUniformTransportPrice (N D Kmax : ℕ) (C : ℝ) : ℝ :=
  nativeArrayCoordinatePrice D * boundedTransportedPolynomialReservePrice N D Kmax C

theorem nativeArrayCoordinatePrice_nonneg (D : ℕ) : 0 ≤ nativeArrayCoordinatePrice D := by
  unfold nativeArrayCoordinatePrice
  positivity

theorem boundedTransportedPolynomialReservePrice_nonneg (N D Kmax : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ boundedTransportedPolynomialReservePrice N D Kmax C :=
  Finset.sum_nonneg (fun k _ => transportedPolynomialUniformReservePrice_nonneg N D k C hC)

theorem nativeArrayUniformTransportPrice_nonneg (N D Kmax : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ nativeArrayUniformTransportPrice N D Kmax C :=
  mul_nonneg (nativeArrayCoordinatePrice_nonneg D)
    (boundedTransportedPolynomialReservePrice_nonneg N D Kmax C hC)

theorem nativeArray_uniform_transport_sum_le (N D Kmax r K : ℕ) (hr : r ≤ D) (hK : K ≤ Kmax)
    (C S A : ℝ) (hC : 0 ≤ C) (hS : 0 ≤ S) (hA : 0 ≤ A) :
    (∑ _β : Fin 2 × DerivativeWord2 r,
      Real.sqrt (multiplicationDensityBudget K) *
        (transportedPolynomialUniformReservePrice N D K C * S * A)) ≤
    Real.sqrt (multiplicationDensityBudget K) * (nativeArrayUniformTransportPrice N D Kmax C * S * A) := by
  have hcard : (Fintype.card (Fin 2 × DerivativeWord2 r) : ℝ) ≤ nativeArrayCoordinatePrice D :=
    Finset.single_le_sum (fun j _ => (Nat.cast_nonneg (Fintype.card (Fin 2 × DerivativeWord2 j)) :
      (0 : ℝ) ≤ Fintype.card (Fin 2 × DerivativeWord2 j)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  have hprice : transportedPolynomialUniformReservePrice N D K C ≤
      boundedTransportedPolynomialReservePrice N D Kmax C :=
    Finset.single_le_sum (fun j _ => transportedPolynomialUniformReservePrice_nonneg N D j C hC)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul hcard hprice (transportedPolynomialUniformReservePrice_nonneg N D K C hC)
      (nativeArrayCoordinatePrice_nonneg D))
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (multiplicationDensityBudget K)) hS) hA)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold nativeArrayUniformTransportPrice
  convert hh using 1 <;> ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Integer-image weak pairings transfer to the genuine torus carrier readout in time. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem periodized_coefficient_actual_time_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K E)
    (hr : ∀ᵐ t ∂μ, (T t).toFunction.jet α =ᵐ[volume] periodizeRawJet (f t).toFunction.jet α) :
    Integrable (fun t => ∫ x, inner ℝ (C t x ((T t).toFunction.jet α x))
      (φ.toFunction.jet β x)) μ ∧
    (∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) ∂μ) =
      ∫ t, (∫ x, inner ℝ (C t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)) ∂μ := by
  have he : (fun t => ∫ x, inner ℝ (C t x (periodizeRawJet (f t).toFunction.jet α x))
      (φ.toFunction.jet β x)) =ᵐ[μ]
      (fun t => ∫ x, inner ℝ (C t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)) := by
    filter_upwards [hr] with t ht
    apply integral_congr_ae
    filter_upwards [ht] with x hx
    rw [hx]
  refine ⟨(periodized_coefficient_pairing_time_integrable μ U R hR hU C hc hj MC hMC hC
    f hf z α φ β hφ M hM hw hb).congr he, ?_⟩
  exact (translated_coefficient_pairing_spacetime_transfer μ U R hR hU C hc hj MC hMC hC
    f hf z α φ β hφ M hM hw hb).trans (integral_congr_ae he)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The transported finite array and its scalar native jet row have exactly the same component readout. -/

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem transportedArrayAssembly_jet_row {K : ℕ}
    (X : Vec 2 ≃ₜ Vec 2) (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (C : U →L[ℝ] V) (g : ∀ r : ℕ, DerivativeWord2 r → U)
    (y : Vec 2) (a : Fin 2) :
    (∑ d ∈ Finset.Icc 2 D,
      nativeArrayAssembly (d - 1) C
        (fun k A => transportedCoeff (chartInvJacobian ⇑X.symm) D
          (fun d' I => B (d' - 1) I (X.symm y)) (d - 1) A y k)
        (WithLp.toLp 2 (g (d - 1)))) a =
      ∑ j : JetIndex2 K, transportedNativeScalarJetCoefficient X D B a j y •
        C (g j.1.val j.2) := by
  classical
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [nativeArrayAssembly_apply]
  symm
  simp only [transportedNativeScalarJetCoefficient, ite_smul, zero_smul]
  rw [nativeJet_source_order_sum K D hD
    (fun r A => transportedCoeff (chartInvJacobian ⇑X.symm) D
      (fun d I => B (d - 1) I (X.symm y)) r A y a • C (g r A))]
  exact native_source_order_shift D _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! Native subwindows inherit the physical preparation window and the slow
Taylor scale directly from the actual cover. -/

theorem windowCover_native_subwindow_scales
    {α q : ℝ} {Λ m : ℕ} {ζfast : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζfast Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (ic : Fin (P + 2)) (a b : ℝ)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic) :
    let e := ocEpsilon q Λ m
    let E := ocEpsilon q Λ (m - 1)
    let R := Real.sqrt (B * ocTauPP α q Λ m)
    Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tA)) ((e⁻¹) ^ 2 * (ν * tZ)) ∧
    (∀ t ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * t) ∈ Set.Icc tA tZ) ∧
    0 < e / R ∧ (ρs / e) * (e / R) ≤ 1 ∧
    0 ≤ R / E ∧ R / E ≤ 1 ∧ e / E = (R / E) * (e / R) := by
  dsimp only
  let e := ocEpsilon q Λ m
  let E := ocEpsilon q Λ (m - 1)
  let R := Real.sqrt (B * ocTauPP α q Λ m)
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛ
  have hR : 0 < R := Real.sqrt_pos.mpr
    (mul_pos cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1]
    exact div_pos (sq_pos_of_pos he) cov.pos.1
  have htime (t : ℝ) : t / ocEll q Λ m ν ^ 2 = e⁻¹ ^ 2 * (ν * t) := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1, div_div_eq_mul_div, inv_pow, div_eq_mul_inv]
    ring
  have hsub := hwindow.trans (clipped_scaled_time_window_subset _ _ _ _ _ hell)
  refine ⟨?_, ?_, div_pos he hR, ?_, div_nonneg hR.le hE.le,
    (div_le_one hE).mpr cov.RE, ?_⟩
  · simpa only [htime] using hsub
  · intro t ht
    have hh := hsub ht
    have heq : ν⁻¹ * (e ^ 2 * t) = ocEll q Λ m ν ^ 2 * t := by
      rw [CycleReference.ocEll_sq_eq cov.pos.1, div_eq_mul_inv]
      ring
    rw [heq]
    simpa only [Set.mem_Icc, mul_comm] using
      And.intro ((div_le_iff₀ hell).mp hh.1) ((le_div_iff₀ hell).mp hh.2)
  · rw [div_mul_div_cancel₀ he.ne']
    exact (div_le_one hR).mpr cov.rho_R
  · rw [div_mul_div_cancel₀' hR.ne']

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A cover's globally spatial bounds apply at every patch centre, on exactly
the same certified time windows. -/

theorem windowCover_recenter
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (yd : Vec 2) :
    IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P yd := by
  have he : ocEpsilon q Λ m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  let old (i : Fin (P + 2)) := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  let new (i : Fin (P + 2)) := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P yd i
  refine {
    pos := cov.pos
    P_pos := cov.P_pos
    RE := cov.RE
    ellT := cov.ellT
    rho_e := cov.rho_e
    rho_R := cov.rho_R
    dur := cov.dur
    short1 := cov.short1
    short2 := cov.short2
    window := cov.window
    g_range := cov.g_range
    drift_pos := cov.drift_pos
    drift_scale := cov.drift_scale
    drift_small := cov.drift_small
    metric_near := ?_ 
    metric_smooth := ?_ 
    metric_jets := ?_ 
    drift_jets := ?_ 
  }
  · intro i t ht z ξ
    change |∑ r, ∑ c, ξ r *
      (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν (new i) t z -
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) r c * ξ c| ≤ g * ∑ r, ξ r ^ 2
    rw [ocCellMetric_recenter (α := α) hφ (l₀ - 1 + i) ν he (old i) (new i)]
    exact cov.metric_near i t ht _ ξ
  · intro i t ht r c
    have hh : (fun z => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν (new i) t z r c) =
        fun z => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν (old i) t
          (z + (ocEpsilon q Λ m)⁻¹ • (new i - old i)) r c := by
      funext z
      rw [ocCellMetric_recenter (α := α) hφ (l₀ - 1 + i) ν he (old i) (new i)]
    change ContDiff ℝ qJ (fun z => ocCellMetric α q Λ m (Φ (m - 1)) hφ
      (l₀ - 1 + i) ν (new i) t z r c)
    rw [hh]
    exact (cov.metric_smooth i t ht r c).comp (contDiff_id.add contDiff_const)
  · intro i t ht z j hj hjq r c
    change ‖iteratedFDeriv ℝ j (fun x =>
      ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν (new i) t x r c) z‖ ≤
      CG j * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ j
    rw [ocCellMetric_iteratedFDeriv_recenter (α := α) hφ (l₀ - 1 + i) ν he (old i) (new i)]
    exact cov.metric_jets i t ht _ j hj hjq r c
  · intro i j hj hjK t ht z
    change ‖coefficientDerivativeArray (driftCoefficient
      (ocCellDrift α q Λ ζ m ν (new i) t)) j z‖ ≤
      strain * B₀ ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j)
    rw [ocCellDrift_coefficientDerivativeArray_recenter (α := α) (ζ := ζ) ν he (old i) (new i)]
    exact cov.drift_jets i j hj hjK t ht _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite coefficient arrays commute with the complete image sum and spacetime integral. -/

variable {E F X J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem finite_coefficient_pairing_spacetime_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (S : Finset J) (U : Set (Vec 2)) (hUm : MeasurableSet U) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : J → X → Vec 2 → E →L[ℝ] F) (hc : ∀ j t, Continuous (C j t))
    (hj : ∀ j, Measurable (Function.uncurry (C j))) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ j t x, ‖C j t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : J → JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ j, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) volume)
    (hb : ∀ j, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    (∑' n : Fin 2 → ℤ, ∫ t, (∫ x, ∑ j ∈ S, inner ℝ
      (C j t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α j) x))
      (φ.toFunction.jet β x)) ∂μ) =
      ∫ t, (∫ x, ∑ j ∈ S, inner ℝ
        (C j t x (periodizeRawJet (f t).toFunction.jet (α j) x))
        (φ.toFunction.jet β x)) ∂μ := by
  let G := fun j (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    (C j t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α j) x))
    (φ.toFunction.jet β x)
  let P := fun j t => ∫ x, inner ℝ
    (C j t x (periodizeRawJet (f t).toFunction.jet (α j) x)) (φ.toFunction.jet β x)
  have hi : ∀ j n, Integrable (G j n) μ := fun j n =>
    translated_coefficient_pairing_time_integrable μ (C j) (hc j) (hj j) MC hMC (hC j)
      f hf (AVenhance.latticeShift n) (α j) φ β
  have hs : ∀ j, Summable (fun n => ∫ t, G j n t ∂μ) := by
    intro j
    exact (hasSum_integral_of_summable_integral_norm (hi j)
      (translated_coefficient_pairing_time_summable μ U R hR hU (C j) (hc j) (hj j)
        MC hMC (hC j) f hf z (α j) φ β hφ M hM (hw j) (hb j))).summable
  calc
    _ = ∑' n, ∫ t, ∑ j ∈ S, G j n t ∂μ := by
      apply tsum_congr
      intro n
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => integral_finsetSum S (fun j _ =>
        translated_coefficient_pairing_space_integrable (AVenhance.latticeShift n)
          (C j t) (hc j t) MC hMC (hC j t) (f t) (α j) φ β))
    _ = ∑' n, ∑ j ∈ S, ∫ t, G j n t ∂μ :=
      tsum_congr (fun n => integral_finsetSum S (fun j _ => hi j n))
    _ = ∑ j ∈ S, ∑' n, ∫ t, G j n t ∂μ :=
      Summable.tsum_finsetSum (fun j _ => hs j)
    _ = ∑ j ∈ S, ∫ t, P j t ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      exact translated_coefficient_pairing_spacetime_transfer μ U R hR hU
        (C j) (hc j) (hj j) MC hMC (hC j) f hf z (α j) φ β hφ M hM (hw j) (hb j)
    _ = ∫ t, ∑ j ∈ S, P j t ∂μ :=
      (integral_finsetSum S (fun j _ => periodized_coefficient_pairing_time_integrable
        μ U R hR hU (C j) (hc j) (hj j) MC hMC (hC j) f hf z (α j) φ β hφ
        M hM (hw j) (hb j))).symm
    _ = _ := by
      apply integral_congr_ae
      have hwS := (Filter.eventually_all_finset S).mpr (fun j _ => hw j)
      have hbS := (Filter.eventually_all_finset S).mpr (fun j _ => hb j)
      filter_upwards [hwS, hbS] with t hwt hbt
      exact (integral_finsetSum S (fun j hjS =>
        periodized_compact_coefficient_pairing_integrable U hUm (C j t) (hc j t)
          MC hMC (hC j t) (f t) (α j) φ β hφ
          (planeImageJetCLM_radial_enorm_tsum_lt_top U R hR hU z (α j) (f t) ‖M t‖
            (norm_nonneg _) (hwt j hjS) (hbt j hjS)))).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Constant component vectors are exact stationary solutions of every positive-order coupled system. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusConstantCoupledSolution (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (c : ∀ i, h i) :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun i => torusConstantCarrier (K i) (c i))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun i _ => torusConstantCarrier (K i) (c i))
      (fun i _ => torusConstantCarrier (K i + 1) (c i)) := by
  refine ⟨fun _ => continuousOn_const, fun i => memLp_const _, ?_, fun _ => rfl, ?_⟩
  · intro i
    exact Filter.Eventually.of_forall (fun _ => torusConstantCarrier_truncate
      (K i) (K i + 1) (Nat.le_succ _) (c i))
  · intro i t _ φ
    have hpair := (torusRawValue_pairing_integrable_and_integral
      (torusConstantCarrier (K i) (c i)) φ).1
    have hs := coupledWeakIdentity_stationary (volume.restrict AVenhance.unitCube) ν a t v
      ((torusConstantCarrier (K i) (c i)).toFunction.jet (valueIndex2 (K i)))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (fun _ k => (torusConstantCarrier (K i + 1) (c i)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun r => torusRawCouplingFlux K D r A
        (fun j => torusConstantCarrier (K j + 1) (c j)) i) hpair
      (fun _ _ k => torusConstantCarrier_raw_positive_ae (K i + 1) (c i) _ Nat.zero_lt_one)
      (fun r _ => torusConstantCouplingFlux_zero_ae K D r A c i)
    exact torusHomogeneous_forcing_readout (K i) ν a t v _ _ _ _ _ _ hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVenhance Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The independent field time and the two flow endpoints can differ in a sampled coefficient. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_flow_sample_raw_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hn : K v ≤ Jchart + 1) (s τ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)) :
    let Cflow := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ t : ℝ, (∀ Y : Vec 2, (τ, Y) ∈ dom p c) →
      t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
      |s - t| ≤ 2 * Cage * ocTauPP α q Λ m → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e (ocEpsilon q Λ (m - 1))
        p c v u γ d I τ (streamFlow φ hφ s y t)
          (e⁻¹ • streamFlow φ hφ s y t)) x‖ ≤
        ((K v).factorial : ℝ) * Cflow ^ (K v) * ((K v + 1 : ℕ) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal)) := by
  dsimp only
  intro t hdom htime hage j hj x
  have ht := pointwise_molecular_physical_sample_raw_budget F π hπ K Kmax hK dom ν e
    (ocEpsilon q Λ (m - 1)) ρ hν he hE hρ C J b henv v u γ hγ d hd I p c τ
  let f := fun y : Vec 2 => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I τ y (e⁻¹ • y)
  have hf : ContDiff ℝ (K v : ℕ) f := by
    have hh := molecular_joint_contDiff F dom (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + J) henv.1 p c τ hdom v u γ d I
    have hsample := hh.comp ((contDiff_id.const_smul ((ocEpsilon q Λ (m - 1))⁻¹)).prodMk
      (contDiff_id.const_smul e⁻¹))
    exact (hsample.const_smul (ν * e ^ (d - 2))).of_le
      (by exact_mod_cast Nat.le_add_right (K v) J)
  exact preparation_flow_uniform_sample_jets hc ha ρ hρ hρE s t hs htime hage
    (K v) hn f hf _ (by positivity) (ht hdom) j hj x
end

/-! The molecular envelope bounds the actual dimensional diagonal sample before chart transport. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_material_sample_raw_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hn : K v ≤ Jchart + 1) (s : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m)) :
    let Cflow := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
      |s - t| ≤ 2 * Cage * ocTauPP α q Λ m → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e (ocEpsilon q Λ (m - 1))
        p c v u γ d I t (streamFlow φ hφ s y t)
          (e⁻¹ • streamFlow φ hφ s y t)) x‖ ≤
        ((K v).factorial : ℝ) * Cflow ^ (K v) * ((K v + 1 : ℕ) *
          ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
            (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal)) := by
  dsimp only
  intro t hdom htime hage j hj x
  have ht := pointwise_molecular_physical_sample_raw_budget F π hπ K Kmax hK dom ν e
    (ocEpsilon q Λ (m - 1)) ρ hν he hE hρ C J b henv v u γ hγ d hd I p c t
  let f := fun y : Vec 2 => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I t y (e⁻¹ • y)
  have hf : ContDiff ℝ (K v : ℕ) f := by
    have hh := molecular_joint_contDiff F dom (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + J) henv.1 p c t hdom v u γ d I
    have hsample := hh.comp ((contDiff_id.const_smul ((ocEpsilon q Λ (m - 1))⁻¹)).prodMk
      (contDiff_id.const_smul e⁻¹))
    exact (hsample.const_smul (ν * e ^ (d - 2))).of_le
      (by exact_mod_cast Nat.le_add_right (K v) J)
  exact preparation_flow_uniform_sample_jets hc ha ρ hρ hρE s t hs htime hage
    (K v) hn f hf _ (by positivity) (ht hdom) j hj x
end

end AVRegularity.CycleJointProofs
end
end
