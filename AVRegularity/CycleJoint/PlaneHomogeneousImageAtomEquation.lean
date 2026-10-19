-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.CycleJoint.UnitPatchValuePeriodization
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import AVRegularity.CycleEvolution.CellConjugateH1
public import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget
public import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
public import AVRegularity.CycleJoint.PlaneH1Average
public import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleReference.MeanEnhancementScale

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual plane lifts discharge spatial integrability for each homogeneous weak atom. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_weak_atom_integrable (K : ι → ℕ) (D : ℕ) (ν s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (v s))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i : ι)
    (hc : ∀ i' d, Continuous (A i i' d s))
    (M : ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ i' d, 0 ≤ M i' d) (hb : ∀ i' d x, ‖A i i' d s x‖ ≤ M i' d)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (ψ : PlaneHk Set.univ 1 (h i)) (j : Fin 3) :
    Integrable (homogeneousWeakRhsAtom ν v (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun t k => (w i t).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun t => planeRawCouplingFlux K D t A (fun k => w k t) i) j s) volume := by
  rw [← Measure.restrict_univ (μ := volume)]
  apply homogeneousWeakRhsAtom_integrable ν s v _ _ _ _ hv V hV hbv
  · exact ψ.toFunction.memL2 _
  · intro k
    exact ψ.toFunction.memL2 _
  · intro k
    exact (w i s).toFunction.memL2 _
  · intro k
    exact planeRawCouplingFlux_component_memLp K D s A i hc M hM hb (fun k => w k s) k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual plane weak solutions superpose, including their time traces and Sobolev lifts. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_add_identities (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f f' : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g g' u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (hs' : IsCoupledWeakSolutionPlane ν a b v D K A f' F' g' u' w') :
    ∀ i t, t ∈ Set.Icc a b → ∀ φ : PlaneHk Set.univ 1 (h i),
      CoupledWeakIdentity volume ν a t v
        ((u i t + u' i t).toFunction.jet (valueIndex2 (K i)))
        ((f i + f' i).toFunction.jet (valueIndex2 (K i)))
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
        (fun s k => (w i s + w' i s).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
        (fun s => planeRawCouplingFlux K D s A (fun j => w j s + w' j s) i)
        (fun s => (F i s + F' i s).toFunction.jet (valueIndex2 (K i)))
        (fun s => (g i s + g' i s).toFunction.jet (valueIndex2 (K i))) := by
  intro i t ht φ
  let p := φ.toFunction.jet (valueIndex2 1)
  let dp := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  let du := fun s k => (w i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let du' := fun s k => (w' i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let Q := fun s => planeRawCouplingFlux K D s A (fun j => w j s) i
  let Q' := fun s => planeRawCouplingFlux K D s A (fun j => w' j s) i
  let ff := fun s => (F i s).toFunction.jet (valueIndex2 (K i))
  let ff' := fun s => (F' i s).toFunction.jet (valueIndex2 (K i))
  let gg := fun s => (g i s).toFunction.jet (valueIndex2 (K i))
  let gg' := fun s => (g' i s).toFunction.jet (valueIndex2 (K i))
  have hsum := coupledWeakIdentity_add (volume.restrict Set.univ) ν a t v
    _ _ _ _ p dp du du' Q Q' ff ff' gg gg'
    (hs.2.2.2.2 i t ht φ) (hs'.2.2.2.2 i t ht φ)
  simp only [Measure.restrict_univ] at hsum ⊢
  apply coupledWeakIdentity_integrands_congr volume ν a t v v
    _ _ _ _ p p dp dp (du + du') _ (Q + Q') _ (ff + ff') _ (gg + gg') _ _ _ _ hsum
  · filter_upwards [planeCarrier_jet_add_ae (u i t) (u' i t) (valueIndex2 (K i))] with x hx
    exact congrArg (fun z => inner ℝ z (p x)) hx.symm
  · filter_upwards [planeCarrier_jet_add_ae (f i) (f' i) (valueIndex2 (K i))] with x hx
    exact congrArg (fun z => inner ℝ z (p x)) hx.symm
  · intro s _
    apply weakIdentityRhs_congr_ae volume ν s v v p p dp dp (du + du') _
      (Q + Q') _ (ff + ff') _ (gg + gg') _
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    · intro k
      exact (planeCarrier_jet_add_ae (w i s) (w' i s)
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩).symm
    · exact (planeRawCouplingFlux_add_ae K D s A (fun j => w j s) (fun j => w' j s) i).symm
    · exact (planeCarrier_jet_add_ae (F i s) (F' i s) (valueIndex2 (K i))).symm
    · exact (planeCarrier_jet_add_ae (g i s) (g' i s) (valueIndex2 (K i))).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open AVRegularity.CycleReference
open scoped Matrix
namespace AVRegularity.CycleJointProofs

/-! Material charts transport Hilbert-valued L2 gradients and all scalar weak derivative identities. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hilbertChartGradient {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (G : Fin 2 → Vec 2 → E) : Fin 2 → Vec 2 → E :=
  fun j y => hilbertMatrixAction
    (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ
    (fun i => G i (AVRegularity.streamFlow φ hφ t y s)) j

theorem hilbertChartGradient_inner {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (G : Fin 2 → Vec 2 → E) (e : E) (j : Fin 2) (y : Vec 2) :
    inner ℝ e (hilbertChartGradient hφ t s G j y) =
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (fun i => inner ℝ e (G i (AVRegularity.streamFlow φ hφ t y s)))) j :=
  hilbertMatrixAction_inner _ _ e j

theorem hilbertChartGradient_memLp {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (G : Fin 2 → Vec 2 → E) (hG : ∀ i, MemLp (G i) 2 volume) (j : Fin 2) :
    MemLp (hilbertChartGradient hφ t s G j) 2 volume := by
  obtain ⟨C, _, hb⟩ := streamFlow_jacMatrix_bounded hφ t s
  apply hilbertMatrixAction_memLp
    (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ)
    (fun i y => G i (AVRegularity.streamFlow φ hφ t y s))
    (fun k i => (jacMatrix_entry_smooth (streamFlow_spatial_smooth hφ t s) i k).continuous.aestronglyMeasurable)
    C (fun y k i => hb y i k)
    (fun i => (hG i).comp_measurePreserving (streamFlow_measurePreserving hφ t s)) j

theorem hilbertChartGradient_weak {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (f : Vec 2 → E) (G : Fin 2 → Vec 2 → E)
    (hf : MemLp f 2 volume) (hG : ∀ i, MemLp (G i) 2 volume)
    (hw : ∀ i e, HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) (j : Fin 2) (e : E) :
    HasWeakPartialDerivOn Set.univ j
      (fun y => inner ℝ e (f (AVRegularity.streamFlow φ hφ t y s)))
      (fun y => inner ℝ e (hilbertChartGradient hφ t s G j y)) := by
  have hfs : MemL2On Set.univ (fun x => inner ℝ e (f x)) :=
    ((innerSL ℝ e).comp_memLp' hf).mono_measure Measure.restrict_le_self
  have hgs : GradMemL2On Set.univ (fun x i => inner ℝ e (G i x)) :=
    fun i => ((innerSL ℝ e).comp_memLp' (hG i)).mono_measure Measure.restrict_le_self
  have hs := streamFlow_weakGradient hφ t s hfs hgs (fun i => hw i e)
  simpa only [hilbertChartGradient_inner] using hs j

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The physical viscous dual reads the exact raw homogeneous spatial weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A flux readout equality suffices to identify the Riesz dual with the literal raw RHS. -/
theorem planeViscousDual_pair_eq_raw (ν : ℝ) (K : ℕ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {M : ℝ} (hM : 0 ≤ M) (hvb : ∀ k x, |v x k| ≤ M)
    (w : PlaneHk Set.univ (K + 1) E) (φ : PlaneHk Set.univ 1 E)
    (F : PlaneFluxL2 E) (Q : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hQ : ∀ k, F k =ᵐ[volume] fun x => Q x k) :
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport v hvc hM hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
      (truncatePlaneHk (E := E) (by omega) w) F) φ =
      ∫ x, planeWeakSpatialRhs ν (fun _ => v)
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun _ k => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun _ => Q) (fun _ _ => 0) (fun _ _ => 0) 0 x := by
  rw [planeViscousDual_pair_eq_integral]
  have hw : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) (truncatePlaneHk (by omega) w) k x =
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hφ : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) φ k x =
        φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hf : ∀ᵐ x ∂volume, ∀ k : Fin 2, F k x = Q x k := ae_all_iff.mpr hQ
  apply integral_congr_ae
  filter_upwards [hw, hφ, hf, univToPlane_ae (φ.val (valueIndex2 1))]
    with x hwx hφx hfx hvx
  simp only [planeHkValueOperator_apply, hvx, planeWeakSpatialRhs, PiLp.zero_apply,
    add_zero, inner_zero_left]
  simp_rw [hwx, hφx, hfx]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The complete actual plane solution class is invariant under simultaneous spatial translation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_translate (K : ι → ℕ) (D : ℕ) (ν a b : ℝ) (z : Vec 2)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b (fun s x => v s (x + z)) D K
      (fun i i' d s x => A i i' d s (x + z))
      (fun i => planeCarrierTranslation (K i) z (f i))
      (fun i s => planeCarrierTranslation (K i) z (F i s))
      (fun i s => planeCarrierTranslation (K i) z (g i s))
      (fun i s => planeCarrierTranslation (K i) z (u i s))
      (fun i s => planeCarrierTranslation (K i + 1) z (w i s)) := by
  refine ⟨fun i => (planeCarrierTranslation (K i) z).continuous.comp_continuousOn (hsol.1 i),
    fun i => (planeCarrierTranslation (K i + 1) z).comp_memLp' (hsol.2.1 i), ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hsol.2.2.1 i] with s hs
    rw [← planeCarrierTranslation_truncate, hs]
  · intro i
    change planeCarrierTranslation (K i) z (u i a) = planeCarrierTranslation (K i) z (f i)
    rw [hsol.2.2.2.1 i]
  · intro i t ht φ
    let p := φ.toFunction.jet (valueIndex2 1)
    let dp := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    let ψ := planeCarrierTranslation 1 (-z) φ
    let du := fun s k => (w i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    let Q := fun s => planeRawCouplingFlux K D s A (fun j => w j s) i
    let ff := fun s => (F i s).toFunction.jet (valueIndex2 (K i))
    let gg := fun s => (g i s).toFunction.jet (valueIndex2 (K i))
    have hold := hsol.2.2.2.2 i t ht ψ
    simp only [Measure.restrict_univ] at hold ⊢
    have hψ : ψ.toFunction.jet (valueIndex2 1) =ᵐ[volume] fun y => p (y - z) := by
      simpa only [sub_eq_add_neg] using planeCarrierTranslation_jet_ae (-z) φ (valueIndex2 1)
    have hdψ (k : Fin 2) : ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ =ᵐ[volume]
        fun y => dp k (y - z) := by
      simpa only [sub_eq_add_neg] using planeCarrierTranslation_jet_ae (-z) φ
        ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    have hideal := coupledWeakIdentity_test_congr volume ν a t v
      ((u i t).toFunction.jet (valueIndex2 (K i))) ((f i).toFunction.jet (valueIndex2 (K i)))
      _ (fun y => p (y - z)) _ (fun k y => dp k (y - z)) du Q ff gg hψ hdψ hold
    have htr := coupledWeakIdentity_translate ν a t z v
      ((u i t).toFunction.jet (valueIndex2 (K i))) ((f i).toFunction.jet (valueIndex2 (K i)))
      p dp du Q ff gg hideal
    let du' := fun s k => (planeCarrierTranslation (K i + 1) z (w i s)).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    let Q' := fun s => planeRawCouplingFlux K D s (fun j j' d s x => A j j' d s (x + z))
      (fun j => planeCarrierTranslation (K j + 1) z (w j s)) i
    let ff' := fun s => (planeCarrierTranslation (K i) z (F i s)).toFunction.jet (valueIndex2 (K i))
    let gg' := fun s => (planeCarrierTranslation (K i) z (g i s)).toFunction.jet (valueIndex2 (K i))
    apply coupledWeakIdentity_integrands_congr volume ν a t
      (fun s x => v s (x + z)) (fun s x => v s (x + z))
      _ _ _ _ p p dp dp (fun s k x => du s k (x + z)) du'
      (fun s x => Q s (x + z)) Q' (fun s x => ff s (x + z)) ff'
      (fun s x => gg s (x + z)) gg' _ _ _ htr
    · filter_upwards [planeCarrierTranslation_jet_ae z (u i t) (valueIndex2 (K i))] with x hx
      rw [hx]
    · filter_upwards [planeCarrierTranslation_jet_ae z (f i) (valueIndex2 (K i))] with x hx
      rw [hx]
    · intro s _
      exact weakIdentityRhs_congr_ae volume ν s _ _ p p dp dp
        (fun s k x => du s k (x + z)) du' (fun s x => Q s (x + z)) Q'
        (fun s x => ff s (x + z)) ff' (fun s x => gg s (x + z)) gg'
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
        (fun k => (planeCarrierTranslation_jet_ae z (w i s)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩).symm)
        (planeRawCouplingFlux_translate_ae K D s z A (fun j => w j s) i).symm
        (planeCarrierTranslation_jet_ae z (F i s) (valueIndex2 (K i))).symm
        (planeCarrierTranslation_jet_ae z (g i s) (valueIndex2 (K i))).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A positive, radius-normalized bound for one exact native Piola/order-lowering summand. -/

theorem native_piola_summand_polynomial_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length)
    (n : ℕ) (hn : n + I.length ≤ N)
    (B : Vec 2 → ℝ) (hB : ContDiff ℝ (n : ℕ) B) (MB : ℝ)
    (ϖ : ℝ) (p : ℕ)
    (hBj : ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j B y‖ ≤ MB * polynomialMomentRoot ϖ y ^ p)
    (a i : Fin 2) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => K y a i * B y * transitionT K I A y) x‖ ≤
      ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB *
        ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length * E⁻¹ ^ (I.length - A.length)) *
          polynomialMomentRoot ϖ x ^ p := by
  have hnn : n ≤ N := by omega
  have hh := triple_product_weighted_jet_bound _ _ _ x n
    ((hK a i).of_le (by simp)) hB
    ((transitionT_spatial_smooth K hK I A).of_le (by simp)) ρ C (MB * polynomialMomentRoot ϖ x ^ p) _ hρ
    (by
      intro j hj
      have hh := hKC a i j (hj.trans hnn) x
      have hb := radius_lowering_bound E ρ C _ j 0 hE hρ hρE hC
        (by simpa only [Nat.add_zero] using hh)
      simpa only [pow_zero, mul_one] using hb)
    (fun j hj => hBj j hj x)
    (by
      intro j hj
      exact transitionT_molecular_jet_bound K hK N C E ρ hC hE hρ hρE hKC I A hA
        j (by omega) x)
  apply hh.trans_eq
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleJointProofs

/-! Integer images of a plane solution solve the same periodic equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_integer_translate (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t, IsZ2Periodic (v t))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d t, IsZ2Periodic (A i i' d t))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (n : Fin 2 → ℤ) :
    IsCoupledWeakSolutionPlane ν a b v D K A
      (fun i => planeCarrierTranslation (K i) (latticeShift n) (f i))
      (fun i t => planeCarrierTranslation (K i) (latticeShift n) (F i t))
      (fun i t => planeCarrierTranslation (K i) (latticeShift n) (g i t))
      (fun i t => planeCarrierTranslation (K i) (latticeShift n) (u i t))
      (fun i t => planeCarrierTranslation (K i + 1) (latticeShift n) (w i t)) := by
  have hvEq : (fun t x => v t (x + latticeShift n)) = v := funext (fun t => funext (hv t n))
  have hAEq : (fun i i' d t x => A i i' d t (x + latticeShift n)) = A := by
    funext i i' d t x
    exact hA i i' d t n x
  simpa only [hvEq, hAEq] using planeWeakSolution_translate K D ν a b (latticeShift n)
    v A f F g u w hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Diffusion time normalization preserves the homogeneous coupled plane weak solutions
(`IsCoupledWeakSolutionPlane`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The full homogeneous system, including all stored orders, transfers to unit diffusion. -/
theorem planeHomogeneous_diffusion_time_solution (K : ι → ℕ) (D : ℕ)
    {ν a b : ℝ} (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionPlane 1 (ν * a) (ν * b) (timeNormalizedVelocity ν v) D K
      (fun i i' d r x => ν⁻¹ • A i i' d (ν⁻¹ * r) x)
      f (fun _ _ => 0) (fun _ _ => 0)
      (fun i r => u i (ν⁻¹ * r)) (fun i r => w i (ν⁻¹ * r)) := by
  have hmaps : Set.MapsTo (fun r : ℝ => ν⁻¹ * r)
      (Set.Icc (ν * a) (ν * b)) (Set.Icc a b) := by
    intro r hr
    change ν⁻¹ * r ∈ Set.Icc a b
    rw [show ν⁻¹ * r = r / ν by rw [div_eq_mul_inv, mul_comm]]
    exact ⟨(le_div_iff₀ hν).mpr (by simpa only [mul_comm] using hr.1),
      (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using hr.2)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hs.1 i).comp (continuous_const.mul continuous_id).continuousOn hmaps
  · intro i
    exact memLp_comp_inv_mul_restrict_Icc hν (hs.2.1 i)
  · intro i
    exact ae_comp_inv_mul_restrict_Icc hν (hs.2.2.1 i)
  · intro i
    simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using hs.2.2.2.1 i
  · intro i t ht φ
    simp only [Measure.restrict_univ]
    apply coupledWeakIdentity_zeroCarrier_forcing
    exact planeHomogeneous_normalized_weak_test K D hν v A f u w hs i t ht φ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Material flow acts isometrically on native plane L2 classes and preserves continuous time traces. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def planeL2FlowPull {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) : Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun y => AVRegularity.streamFlow φ hφ t y s)
    (streamFlow_measurePreserving hφ t s)

theorem planeL2FlowPull_continuousOn {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (S : Set ℝ) (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hu : ContinuousOn u S) : ContinuousOn (fun t => planeL2FlowPull hφ t s (u t)) S := by
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  exact hu.compMeasurePreservingLp (streamFlowContinuousMap_continuous hφ s).continuousOn
    (fun t => streamFlow_measurePreserving hφ t s) (by norm_num : (2 : ENNReal) ≠ ⊤)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The actual bounded drift and L2 flux give integrable literal spatial weak right-hand sides at every time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeViscous_rawSpatial_integrable (ν : ℝ) (K : ℕ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {M : ℝ} (hM : 0 ≤ M) (hvb : ∀ k x, |v x k| ≤ M)
    (w : PlaneHk Set.univ (K + 1) E) (φ : PlaneHk Set.univ 1 E)
    (F : PlaneFluxL2 E) (Q : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hQ : ∀ k, F k =ᵐ[volume] fun x => Q x k) :
    Integrable (fun x => planeWeakSpatialRhs ν (fun _ => v)
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun _ k => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun _ => Q) (fun _ _ => 0) (fun _ _ => 0) 0 x) volume := by
  let du := planeH1GradientOperator (E := E) (truncatePlaneHk (by omega) w)
  let dφ := planeH1GradientOperator (E := E) φ
  let z := planeHkValueOperator (E := E) 1 φ
  let T := planeScalarTransport v hvc hM hvb du
  have hT : Integrable (fun x => inner ℝ (T x) (z x)) volume := L2.integrable_inner T z
  have hD : Integrable (fun x => ∑ k : Fin 2, inner ℝ (du k x) (dφ k x)) volume :=
    integrable_finsetSum _ (fun k _ => L2.integrable_inner (du k) (dφ k))
  have hF : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F k x) (dφ k x)) volume :=
    integrable_finsetSum _ (fun k _ => L2.integrable_inner (F k) (dφ k))
  apply (hT.neg.sub (hD.const_mul ν) |>.sub hF).congr
  have hw : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      du k x = w.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hφ : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      dφ k x = φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  filter_upwards [hw, hφ, ae_all_iff.mpr hQ, univToPlane_ae (φ.val (valueIndex2 1)),
    planeScalarTransport_ae v hvc hM hvb du] with x hwx hφx hfx hvx htx
  change -inner ℝ (T x) (z x) - ν * (∑ k, inner ℝ (du k x) (dφ k x)) -
    (∑ k, inner ℝ (F k x) (dφ k x)) = _
  rw [htx]
  simp only [sum_inner, real_inner_smul_left, z, planeHkValueOperator_apply, hvx,
    planeWeakSpatialRhs, PiLp.zero_apply, add_zero, inner_zero_left]
  simp_rw [hwx, hφx, hfx]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual plane weak solutions superpose, including their time traces and Sobolev lifts. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_add (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f f' : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g g' u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (hs' : IsCoupledWeakSolutionPlane ν a b v D K A f' F' g' u' w') :
    IsCoupledWeakSolutionPlane ν a b v D K A (fun i => f i + f' i)
      (fun i t => F i t + F' i t) (fun i t => g i t + g' i t)
      (fun i t => u i t + u' i t) (fun i t => w i t + w' i t) := by
  have hc : ∀ i, ContinuousOn (fun t => u i t + u' i t) (Set.Icc a b) :=
    fun i => planeCarrierCurve_continuousOn_add (u i) (u' i) _ (hs.1 i) (hs'.1 i)
  have hw : ∀ i, MemLp (fun t => w i t + w' i t) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => normedCurve_memLp_add (w i) (w' i) _ (hs.2.1 i) (hs'.2.1 i)
  refine ⟨hc, hw, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i, hs'.2.2.1 i] with s hsu hsu'
    change truncatePlaneHk (Nat.le_succ (K i)) (w i s + w' i s) = u i s + u' i s
    rw [map_add, hsu, hsu']
  · intro i
    change u i a + u' i a = f i + f' i
    rw [hs.2.2.2.1 i, hs'.2.2.2.1 i]
  · intro i t ht φ
    simp only [Measure.restrict_univ]
    exact planeWeakSolution_add_identities K D ν a b v A f f' F F' g g' u u' w w' hs hs' i t ht φ
end

/-! Actual plane weak solutions superpose, including their time traces and Sobolev lifts. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_smul_identities (K : ι → ℕ) (D : ℕ) (c ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    ∀ i t, t ∈ Set.Icc a b → ∀ φ : PlaneHk Set.univ 1 (h i),
      CoupledWeakIdentity volume ν a t v
        ((c • u i t).toFunction.jet (valueIndex2 (K i)))
        ((c • f i).toFunction.jet (valueIndex2 (K i)))
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
        (fun s k => (c • w i s).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
        (fun s => planeRawCouplingFlux K D s A (fun j => c • w j s) i)
        (fun s => (c • F i s).toFunction.jet (valueIndex2 (K i)))
        (fun s => (c • g i s).toFunction.jet (valueIndex2 (K i))) := by
  intro i t ht φ
  let p := φ.toFunction.jet (valueIndex2 1)
  let dp := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  let du := fun s k => (w i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let Q := fun s => planeRawCouplingFlux K D s A (fun j => w j s) i
  let ff := fun s => (F i s).toFunction.jet (valueIndex2 (K i))
  let gg := fun s => (g i s).toFunction.jet (valueIndex2 (K i))
  have hscaled := coupledWeakIdentity_smul (volume.restrict Set.univ) c ν a t v
    _ _ p dp du Q ff gg (hs.2.2.2.2 i t ht φ)
  simp only [Measure.restrict_univ] at hscaled ⊢
  apply coupledWeakIdentity_integrands_congr volume ν a t v v
    _ _ _ _ p p dp dp (c • du) _ (c • Q) _ (c • ff) _ (c • gg) _ _ _ _ hscaled
  · filter_upwards [planeCarrier_jet_smul_ae c (u i t) (valueIndex2 (K i))] with x hx
    exact congrArg (fun z => inner ℝ z (p x)) hx.symm
  · filter_upwards [planeCarrier_jet_smul_ae c (f i) (valueIndex2 (K i))] with x hx
    exact congrArg (fun z => inner ℝ z (p x)) hx.symm
  · intro s _
    apply weakIdentityRhs_congr_ae volume ν s v v p p dp dp (c • du) _
      (c • Q) _ (c • ff) _ (c • gg) _
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    · intro k
      exact (planeCarrier_jet_smul_ae c (w i s)
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩).symm
    · exact (planeRawCouplingFlux_smul_ae K D c s A (fun j => w j s) i).symm
    · exact (planeCarrier_jet_smul_ae c (F i s) (valueIndex2 (K i))).symm
    · exact (planeCarrier_jet_smul_ae c (g i s) (valueIndex2 (K i))).symm
end

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Material spacetime flow preserves every measurable time window. -/

theorem streamFlowTime_window_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurePreserving (streamFlowTimeHomeomorph hφ s)
      (volume.restrict (B ×ˢ univ)) (volume.restrict (B ×ˢ univ)) := by
  have hm := (streamFlowTime_measurePreserving hφ s).restrict_preimage
    (s := B ×ˢ (univ : Set (Vec 2))) (hB.prod MeasurableSet.univ)
  have he : (streamFlowTimeHomeomorph hφ s) ⁻¹' (B ×ˢ univ) = B ×ˢ univ := by
    ext p
    rfl
  rw [he] at hm
  exact hm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! A fixed constituent Hilbert map commutes with volume-preserving composition of actual plane L2 classes. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem planeLp_compMeasurePreserving_fiberMap (X : Vec 2 → Vec 2)
    (hμ : MeasurePreserving X volume volume) (L : E →L[ℝ] F)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    L.compLpL 2 volume (Lp.compMeasurePreservingₗᵢ ℝ X hμ u) =
      Lp.compMeasurePreservingₗᵢ ℝ X hμ (L.compLpL 2 volume u) := by
  apply Lp.ext
  have hL := ContinuousLinearMap.coeFn_compLpL L (Lp.compMeasurePreservingₗᵢ ℝ X hμ u)
  have hX := Lp.coeFn_compMeasurePreserving u hμ
  have hR := Lp.coeFn_compMeasurePreserving (L.compLpL 2 volume u) hμ
  have hLX := hμ.quasiMeasurePreserving.ae_eq_comp (ContinuousLinearMap.coeFn_compLpL L u)
  filter_upwards [hL, hX, hR, hLX] with x hl hx hr hlx
  exact hl.trans ((congrArg L hx).trans (hr.trans hlx).symm)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Profile-only derivative constants can be chosen before the Hilbert fiber. -/

def patchProfileDerivativeBudget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (K : ℕ) : ℝ :=
  Classical.choose (spatialPatchCutoff_derivatives_uniform hζ K)

theorem patchProfileDerivativeBudget_nonneg {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (K : ℕ) :
    0 ≤ patchProfileDerivativeBudget hζ K :=
  (Classical.choose_spec (spatialPatchCutoff_derivatives_uniform hζ K)).1

theorem patchProfileDerivativeBudget_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K N j : ℕ) (hj : j ≤ K) (k : Fin 2 → ℤ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (spatialPatchCutoff ζ N k) x‖ ≤
      patchProfileDerivativeBudget hζ K * (N : ℝ) ^ j :=
  (Classical.choose_spec (spatialPatchCutoff_derivatives_uniform hζ K)).2 N j hj k x

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPatchCoefficient_profile_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (K N j : ℕ) (hj : j ≤ K) (k : Fin 2 → ℤ) (x : Vec 2) :
    ‖coefficientDerivativeArray (spatialPatchCoefficient (E := E) ζ N k) j x‖ ≤
      (patchProfileDerivativeBudget hζ K * (2 : ℝ) ^ K) * (N : ℝ) ^ j := by
  have hC := patchProfileDerivativeBudget_nonneg hζ K
  have hs := scalar_operator_array_norm_le (spatialPatchCutoff ζ N k) j
    ((spatialPatchCutoff_smooth hζ N k).of_le (by simp)) (ContinuousLinearMap.id ℝ E) x
  have hm : ‖iteratedFDeriv ℝ j (spatialPatchCutoff ζ N k) x‖ *
      ‖ContinuousLinearMap.id ℝ E‖ ≤ (patchProfileDerivativeBudget hζ K * (N : ℝ) ^ j) * 1 :=
    mul_le_mul (patchProfileDerivativeBudget_bound hζ K N j hj k x)
      ContinuousLinearMap.norm_id_le (norm_nonneg _) (by positivity)
  have hc : (Fintype.card (DerivativeWord2 j) : ℝ) ≤ (2 : ℝ) ^ K := by
    have he : Fintype.card (DerivativeWord2 j) = 2 ^ j := by
      simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
    rw [he, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hj
  have ht := hs.trans (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _))
  apply ht.trans
  have hp := mul_le_mul_of_nonneg_right hc
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg N) j))
  convert hp using 1 <;> ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Actual coefficient-weighted compact pairings localize to the image Hilbert space. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K L : ℕ}

theorem translated_compact_coefficient_pairing (U : Set (Vec 2)) (z : Vec 2)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0) :
    (∫ x, inner ℝ (C x ((planeCarrierTranslation K z f).toFunction.jet α x))
      (φ.toFunction.jet β x)) =
      inner ℝ (boundedCoefficientL2CLM (U := U) C hc M hM hb
        (planeImageJetCLM U z α f))
        (restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)) := by
  let u := planeJetReadoutOperator K α (planeCarrierTranslation K z f)
  let g := planeJetReadoutOperator L β φ
  have hu := univToPlane_ae ((planeCarrierTranslation K z f).val α)
  have hg := univToPlane_ae (φ.val β)
  have hz : ∀ᵐ x ∂volume, x ∉ U → g x = 0 := by
    filter_upwards [hg, hφ] with x hx hzero hxu
    exact hx.trans (hzero hxu)
  calc
    _ = ∫ x, inner ℝ (C x (u x)) (g x) := by
      apply integral_congr_ae
      filter_upwards [hu, hg] with x hx hy
      exact congrArg₂ (inner ℝ) (congrArg (C x) hx.symm) hy.symm
    _ = inner ℝ (planeCoefficientOperator C hc hM hb u) g :=
      (planeCoefficientOperator_inner_eq_integral C hc hM hb u g).symm
    _ = inner ℝ (restrictPlaneLpCLM U (planeCoefficientOperator C hc hM hb u))
        (restrictPlaneLpCLM U g) := plane_pairing_eq_local_inner U _ _ hz
    _ = _ := by
      rw [local_coefficient_restriction]
      change inner ℝ (boundedCoefficientL2CLM (U := U) C hc M hM hb
        (restrictPlaneLpCLM U (planeJetReadoutOperator K α (planeCarrierTranslation K z f))))
        (restrictPlaneLpCLM U g) = _
      rw [translated_local_jet_readout]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleJointProofs

/-! Compact smooth Hilbert spacetime fields give actual strong native L2 time curves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem compactHilbert_native_strong_time
    (f : ℝ × Vec 2 → E) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (a b : ℝ) (z dz : ℝ → Lp E 2 (volume.restrict (univ : Set (Vec 2))))
    (hz : ∀ t, z t =ᵐ[volume.restrict univ] fun x => f (t, x))
    (hdz : ∀ t, dz t =ᵐ[volume.restrict univ] fun x => fderiv ℝ f (t, x) (1, 0)) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  let bE := stdOrthonormalBasis ℝ E
  let μ : Measure (Vec 2) := volume.restrict univ
  let P := fun k => (innerSL ℝ (bE k)).compLpL 2 μ
  let L := fun k => ((ContinuousLinearMap.id ℝ ℝ).smulRight (bE k)).compLpL 2 μ
  let q := fun k (p : ℝ × Vec 2) => inner ℝ (bE k) (f p)
  have hq k : ContDiff ℝ 2 (q k) := (innerSL ℝ (bE k)).contDiff.comp hf
  have hsQ k : HasCompactSupport (q k) := hs.comp_left (inner_zero_right (bE k))
  have ht k : CycleEvolution.StrongTimeRegularity a b (fun t => P k (z t))
      (fun t => P k (dz t)) := by
    apply compactScalar_native_strong_time (q k) (hq k) (hsQ k) a b
    · intro t
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (innerSL ℝ (bE k)) (z t), hz t]
        with x hx hz
      rw [hx, hz]
      rfl
    · intro t
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (innerSL ℝ (bE k)) (dz t), hdz t]
        with x hx hd
      rw [hx, hd]
      have hh : HasFDerivAt (q k)
          ((innerSL ℝ (bE k)).comp (fderiv ℝ f (t, x))) (t, x) :=
        (innerSL ℝ (bE k)).hasFDerivAt.comp (t, x)
          ((hf.differentiable (by norm_num)) (t, x)).hasFDerivAt
      rw [hh.fderiv]
      rfl
  have he (U : Lp E 2 μ) : (∑ k, L k (P k U)) = U :=
    finiteHilbert_L2_basis_decomposition μ U
  have hsum := strongTime_finset_sum Finset.univ
    (fun k t => L k (P k (z t))) (fun k t => L k (P k (dz t)))
    (fun k _ => (ht k).map (L k))
  simpa only [he] using hsum

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A genuine diagonal metric equation with external native forcing is the exact scalar geometry chain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeDiagonalMetric_scalar_solution (K : ι → ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v 2 K
      (planeDiagonalGradientCoefficient K 2 (fun _ t z => G t z - 1)) f F (fun _ _ => 0) u w) :
    IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) := by
  have hone := planeWeakSolution_oneLevel K 2 1 a b v
    (planeDiagonalGradientCoefficient K 2 (fun _ t z => G t z - 1)) f F (fun _ _ => 0) u w hs
  have heq : planeOneLevelCoefficient K 2
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t z => G t z - 1)) =
      planeChainCoefficient (geometryScalarData 2 G) (fun _ => K) := by
    funext p p' d t z
    exact planeDiagonalGradientCoefficient_eq_scalar_chain K 2 G p p' d t z
  rw [heq] at hone
  exact hone

end AVRegularity.CycleJointProofs
end
end

section
public section
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The parent diffusion length over one renewal is small compared with the
parent cell scale, uniformly for all permitted band chains. -/

theorem bandChain_preparation_mixing_scale {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 1 ≤ M →
      ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
        Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) ≤
          C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + ocDelta α q) := by
  obtain ⟨Cb, hCb, Λ₀, hΛ₀, hb⟩ :=
    bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  let Ct : ℝ := 2 ^ (26 : ℕ)
  let C : ℝ := Real.sqrt (Cb * Ct) + 1
  have hC : 1 ≤ C := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  refine ⟨C, hC, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have h128 := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have he := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have hboundB := (hb Λ hΛ M hM κ hκ (m - 1) (by omega) (by omega)).2
  have hboundT := (ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)).2
  have hs := sqrt_product_power_div_le he hB.le (show 0 ≤ Ct by positivity)
    (le_trans zero_le_one hCb) hboundB hboundT
  have hexp : (((1 + α) + ocGamma α q) + (2 - (1 + α) + 2 * ocDelta α q)) / 2 - 1 =
      ocGamma α q / 2 + ocDelta α q := by ring
  rw [hexp] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (Real.rpow_nonneg he.le _))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleJointProofs

/-! A finite-valued L2 time curve has a literal jointly L2 spatial representative. -/

variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem simpleLp_joint_sum (ν : Measure X) (s : SimpleFunc T (Lp E 2 ν)) (t : T) (x : X) :
    (∑ z ∈ s.range, (s ⁻¹' {z}).indicator (fun _ => (1 : ℝ)) t • z x) = s t x := by
  classical
  rw [Finset.sum_eq_single (s t)]
  · rw [indicator_of_mem (show t ∈ s ⁻¹' {s t} from rfl), one_smul]
  · intro z _ hz
    rw [indicator_of_notMem (show t ∉ s ⁻¹' {z} from fun ht => hz ht.symm), zero_smul]
  · intro h
    exact (h (s.mem_range_self t)).elim

theorem simpleLp_joint_memLp (μ : Measure T) (ν : Measure X)
    [IsFiniteMeasure μ] [SFinite ν] (s : SimpleFunc T (Lp E 2 ν)) :
    MemLp (fun p : T × X => s p.1 p.2) 2 (μ.prod ν) := by
  classical
  have hm : MemLp (fun p : T × X =>
      ∑ z ∈ s.range, (s ⁻¹' {z}).indicator (fun _ => (1 : ℝ)) p.1 • z p.2) 2
      (μ.prod ν) := by
    apply memLp_finsetSum
    intro z _
    exact CycleEvolution.cellTensor_memLp
      (memLp_indicator_const 2 (s.measurableSet_fiber z) 1 (Or.inr (measure_ne_top μ _)))
      (Lp.memLp z)
  exact hm.ae_eq (Filter.Eventually.of_forall (fun p => simpleLp_joint_sum ν s p.1 p.2))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Transfer of polynomially weighted coefficient jets to the genuine natural cell chart. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparationCellFlow_weighted_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (e : ℝ) (he : 0 < e) (yc : Vec 2)
    (s : ℝ) (hs : 0 < s) (hsE : s ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ : ℝ) (hϖ : 0 ≤ ϖ) (n d : ℕ) (hn : n ≤ Jchart + 1)
    (g : Vec 2 → V) (hg : ContDiff ℝ (n : ℕ∞) g) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j, j ≤ n → ∀ y,
      s ^ j * ‖iteratedFDeriv ℝ j g y‖ ≤ B * polynomialMomentRoot ϖ y ^ d)
    (z : Vec 2) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    s ^ n * ‖iteratedFDeriv ℝ n (g ∘ naturalPreparationCellFlow hφ r σ e yc) z‖ ≤
      (n.factorial : ℝ) * C ^ n * ((n + 1 : ℕ) * B) *
        (3 + max (Cchart 0) 0) ^ d * polynomialMomentRoot ϖ z ^ d := by
  dsimp only
  have hE : 0 < ocEpsilon q Λ (m - 1) := by
    have hh := mul_pos (hs.trans_le hsE) he
    simpa only [div_mul_cancel₀ _ he.ne'] using hh
  have hJ := naturalPreparationCellFlow_jetBound hc ha hE r σ hr hσ hage e he yc
  have hh := polynomialMoment_scaled_comp_bound hg
    ((naturalPreparationCellFlow_smooth hφ r σ e yc).of_le (by simp))
    (one_le_jetConst _ _) hs hsE hϖ (by positivity : 0 ≤ 1 + max (Cchart 0) 0 / 2) hB
    (fun p hp hpn x => hJ p hp (hpn.trans hn) x) hb z
    (naturalPreparationCellFlow_norm_le hc ha r σ hr hσ hage e he yc z)
  convert hh using 1
  congr 2
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Periodic cell L2 weak fields discharge all spatial integrability in compact-test transfer. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_cellL2_weakIdentity_transfer {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hu : MemLp u 2 (volume.restrict AVenhance.unitCube))
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hφ : MemLp φ 2 (volume.restrict AVenhance.unitCube))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict AVenhance.unitCube))
    (hup : AVenhance.IsZ2Periodic u) (hfp : AVenhance.IsZ2Periodic f)
    (hφp : AVenhance.IsZ2Periodic φ) (hdφp : ∀ k, AVenhance.IsZ2Periodic (dφ k))
    (hv : ∀ s ∈ Set.Ioc a t, Continuous (v s))
    (hvb : ∀ s ∈ Set.Ioc a t, ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖v s x‖ ≤ V)
    (hvp : ∀ s ∈ Set.Ioc a t, AVenhance.IsZ2Periodic (v s))
    (hdu : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (du s k) 2 (volume.restrict AVenhance.unitCube))
    (hflux : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube))
    (hF : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube))
    (hg : ∀ s ∈ Set.Ioc a t, MemLp (g s) 2 (volume.restrict AVenhance.unitCube))
    (hdup : ∀ s ∈ Set.Ioc a t, ∀ k, AVenhance.IsZ2Periodic (du s k))
    (hflp : ∀ s ∈ Set.Ioc a t, AVenhance.IsZ2Periodic (flux s))
    (hFp : ∀ s ∈ Set.Ioc a t, AVenhance.IsZ2Periodic (F s))
    (hgp : ∀ s ∈ Set.Ioc a t, AVenhance.IsZ2Periodic (g s))
    (hlocal : CoupledWeakIdentity volume ν a t v u f
      (fun x => spatialPatchCutoff ζ 1 0 x • φ x)
      (fun k x => fderiv ℝ (spatialPatchCutoff ζ 1 0) x (basisVec k) • φ x +
        spatialPatchCutoff ζ 1 0 x • dφ k x) du flux F g) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u f φ dφ du flux F g := by
  have hχ := (spatialPatchCutoff_smooth hζ 1 0).continuous
  have hcχ := spatialPatchCutoff_compact hζ 1 (by norm_num) 0
  apply periodic_cutoff_weakIdentity_transfer hζ ν a t v u f φ dφ du flux F g
    _ _ (integrable_inner_of_memLp_two _ _ _ hu hφ)
    (integrable_inner_of_memLp_two _ _ _ hf hφ) _ _ _ _ _ hlocal
  · intro n x
    change inner ℝ (u (x + AVenhance.latticeShift n)) (φ (x + AVenhance.latticeShift n)) = _
    rw [hup n x, hφp n x]
  · intro n x
    change inner ℝ (f (x + AVenhance.latticeShift n)) (φ (x + AVenhance.latticeShift n)) = _
    rw [hfp n x, hφp n x]
  · intro s hs
    obtain ⟨V, hV, hbV⟩ := hvb s hs
    exact cell_weakIdentityRhs_integrable ν s v φ dφ du flux F g (hv s hs) V hV hbV
      hφ hdφ (hdu s hs) (hflux s hs) (hF s hs) (hg s hs)
  · intro s hs
    exact weakIdentityRhs_periodic ν s v φ dφ du flux F g (hvp s hs) hφp hdφp
      (hdup s hs) (hflp s hs) (hFp s hs) (hgp s hs)
  · intro s hs k
    exact weakCutoffCorrection_periodic ν φ (du s k) (flux s) (F s) k
      hφp (hdup s hs k) (hflp s hs) (hFp s hs)
  · intro s hs
    obtain ⟨V, hV, hbV⟩ := hvb s hs
    exact compact_weakIdentityRhs_integrable ν s v φ dφ du flux F g (hv s hs) V hV hbV
      hφ hdφ (hdu s hs) (hflux s hs) (hF s hs) (hg s hs)
      hφp hdφp (hdup s hs) (hflp s hs) (hFp s hs) (hgp s hs) _ hχ hcχ
  · intro s hs k
    exact compact_weakCorrection_integrable ν φ (du s k) (flux s) (F s) k
      hφ (hdu s hs k) (hflux s hs k) (hF s hs k)
      hφp (hdup s hs k) (hflp s hs) (hFp s hs) _
      (((spatialPatchCutoff_smooth hζ 1 0).fderiv_right (m := (0 : ℕ)) (by simp)).continuous.clm_apply
        continuous_const) (hcχ.fderiv_apply (𝕜 := ℝ) (basisVec k))

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Hilbert coupling fluxes transform contravariantly in a material chart and remain product L2. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hilbertChartFlux {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (Q : Fin 2 → ℝ × Vec 2 → E) : Fin 2 → ℝ × Vec 2 → E :=
  fun k p => hilbertMatrixAction (chartJac hφ s p.1 p.2)⁻¹
    (fun j => Q j (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) k

theorem hilbertChartFlux_joint_memLp {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) (Q : Fin 2 → ℝ × Vec 2 → E)
    (hQ : ∀ i, MemLp (Q i) 2 (volume.restrict (Icc a b ×ˢ univ))) (k : Fin 2) :
    MemLp (hilbertChartFlux hφ s Q k) 2 (volume.restrict (Icc a b ×ˢ univ)) := by
  let μ := volume.restrict (Icc a b ×ˢ (univ : Set (Vec 2)))
  obtain ⟨C, _, hb⟩ := streamFlow_jacMatrix_bounded_on_compact_time hφ s (Icc a b) isCompact_Icc
  have htop (j : Fin 2) : MemLp (fun p : ℝ × Vec 2 => (chartJac hφ s p.1 p.2)⁻¹ k j) ⊤ μ := by
    apply memLp_top_of_bound (chartJac_inverse_entry_smooth hφ s k j).continuous.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with p hp
    rw [Real.norm_eq_abs]
    exact unitDet_inverse_entry_bound (chartJac hφ s p.1 p.2)
      (streamFlow_jacMatrix_det_one hφ p.1 s p.2) C (hb p.1 hp.1 p.2) k j
  have hcomp (j : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Q j (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2 μ :=
    (hQ j).comp_measurePreserving (streamFlowTime_window_measurePreserving hφ s measurableSet_Icc)
  change MemLp (fun p : ℝ × Vec 2 => ∑ j : Fin 2, (chartJac hφ s p.1 p.2)⁻¹ k j •
    Q j (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2 μ
  exact memLp_finsetSum _ (fun j _ => (htop j).smul (hcomp j))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual translated solutions supply the image equations used by spacetime assembly. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_image_atom_equation (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i))
    (hv : ∀ s ∈ Set.Ioc a t, Continuous (v s))
    (hvb : ∀ s ∈ Set.Ioc a t, ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖v s x‖ ≤ V)
    (hc : ∀ s ∈ Set.Ioc a t, ∀ i' d, Continuous (A i i' d s))
    (M : ℝ → ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ s ∈ Set.Ioc a t, ∀ i' d, 0 ≤ M s i' d)
    (hb : ∀ s ∈ Set.Ioc a t, ∀ i' d x, ‖A i i' d s x‖ ≤ M s i' d)
    (n : Fin 2 → ℤ) :
    let wN := fun j s => planeCarrierTranslation (K j + 1) (AVenhance.latticeShift n) (w j s)
    let duN := fun s k => (wN i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    (∫ x, inner ℝ
      ((planeCarrierTranslation (K i) (AVenhance.latticeShift n) (u i t)).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) -
    (∫ x, inner ℝ
      ((planeCarrierTranslation (K i) (AVenhance.latticeShift n) (f i)).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) =
    ∫ s in Set.Ioc a t, ∑ j : Fin 3, ∫ x, homogeneousWeakRhsAtom ν v
      (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      duN (fun s => planeRawCouplingFlux K D s A (fun k => wN k s) i) j s x := by
  dsimp only
  have htrans := planeWeakSolution_integer_translate K D ν a b v hvp A hAp f
    (fun _ _ => 0) (fun _ _ => 0) u w hs n
  simp only [map_zero] at htrans
  have htest := planeHomogeneous_weak_test K D ν a b v A
    (fun j => planeCarrierTranslation (K j) (AVenhance.latticeShift n) (f j))
    (fun j s => planeCarrierTranslation (K j) (AVenhance.latticeShift n) (u j s))
    (fun j s => planeCarrierTranslation (K j + 1) (AVenhance.latticeShift n) (w j s))
    htrans i t ht ψ
  apply coupledWeakIdentity_homogeneous_atoms volume ν a t v _ _ _ _ _ _ htest
  intro s hs' j
  obtain ⟨V, hV, hbV⟩ := hvb s hs'
  exact planeHomogeneous_weak_atom_integrable K D ν s v (hv s hs') V hV hbV A i
    (hc s hs') (M s) (hM s hs') (hb s hs')
    (fun k s => planeCarrierTranslation (K k + 1) (AVenhance.latticeShift n) (w k s)) ψ j

end AVRegularity.CycleJointProofs
end
end
