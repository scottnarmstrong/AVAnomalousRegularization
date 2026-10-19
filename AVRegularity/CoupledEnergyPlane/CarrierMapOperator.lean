-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.ActionODE
public import AVRegularity.Sobolev.FactorialShift
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.SeparableMeasure

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set TopologicalSpace
namespace AVRegularity.CoupledEnergyPlane

/-! Strong time measurability of literal jointly measurable L² slice classes. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The L² distance is the square root of the integral of the literal representative difference. -/
theorem toLp_dist_eq_sqrt_integral {U : Set (Vec 2)} {f : Vec 2 → F}
    (hf : MemLp f 2 (volume.restrict U)) (g : Lp F 2 (volume.restrict U)) :
    dist (hf.toLp f) g = Real.sqrt (∫ x in U, ‖f x - g x‖ ^ 2) := by
  have hn : ‖hf.toLp f - g‖ ^ 2 = ∫ x in U, ‖f x - g x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hf.toLp f) g, hf.coeFn_toLp] with x hx hf_x
    rw [hx]
    change inner ℝ ((hf.toLp f) x - g x) ((hf.toLp f) x - g x) = _
    rw [hf_x, real_inner_self_eq_norm_sq]
  rw [dist_eq_norm, ← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

variable [SecondCountableTopology F]

/-- Jointly strongly measurable literal L² slices give a strongly measurable curve of classes.
This uses source joint measurability, not a time-operator measurability premise. -/
theorem stronglyMeasurable_toLp_slices {T : Type*} [MeasurableSpace T]
    {U : Set (Vec 2)} {f : T → Vec 2 → F}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hmem : ∀ t, MemLp (f t) 2 (volume.restrict U)) :
    StronglyMeasurable (fun t => (hmem t).toLp (f t)) := by
  let : MeasurableSpace (Lp F 2 (volume.restrict U)) := borel _
  let : BorelSpace (Lp F 2 (volume.restrict U)) := ⟨rfl⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply Measurable.stronglyMeasurable
  apply measurable_of_all_dist
  intro g
  have hdiff : StronglyMeasurable (fun p : T × Vec 2 => f p.1 p.2 - g p.2) :=
    hf.sub ((Lp.stronglyMeasurable g).comp_measurable measurable_snd)
  have hi : StronglyMeasurable (fun t => ∫ x in U, ‖f t x - g x‖ ^ 2) :=
    (hdiff.norm.pow 2).integral_prod_right
  have heq : (fun t => dist ((hmem t).toLp (f t)) g) =
      (fun t => Real.sqrt (∫ x in U, ‖f t x - g x‖ ^ 2)) :=
    funext (fun t => toLp_dist_eq_sqrt_integral (hmem t) g)
  rw [heq]
  exact hi.measurable.sqrt

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane

/-! A clamped coefficient time can be removed from an actual subinterval integral. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clampedTime_integral_eq {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (H : ℝ → ℝ → E) :
    (∫ s in a..t, H (clampPoint a b hab s) s) = ∫ s in a..t, H s s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  have he : (clampPoint a b hab s : ℝ) = s := by
    simp only [clampPoint, max_eq_right hs.1, min_eq_right (hs.2.trans ht.2)]
  change H (clampPoint a b hab s) s = H s s
  rw [he]

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! An actual bounded ODE whose drift and forcing land in a projection range stays in that range. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Range preservation follows from the actual Bochner integral equation. -/
theorem ActionODEData.IsSolution.invariantProjection {a b : ℝ} {hab : a ≤ b}
    (D : ActionODEData (E := E) a b hab) (u : C(Icc a b, E)) (hu : D.IsSolution u)
    (Q : E →L[ℝ] E) (hy : Q D.y₀ = D.y₀)
    (hA : ∀ s x, Q (D.A s x) = D.A s x) (hf : ∀ s, Q (D.f s) = D.f s)
    (t : Icc a b) : Q (u t) = u t := by
  have hi := D.rhs_intervalIntegrable u
  have hsub : uIcc a t.1 ⊆ uIcc a b := by
    rw [uIcc_of_le t.property.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl t.property.2
  have ht := hi.mono_set hsub
  have he : u t = D.y₀ + ∫ s in a..t.1, D.rhs u s := by
    have h := congrArg (fun v : C(Icc a b, E) => v t) hu
    rw [D.volterra_apply] at h
    exact h.symm
  have hr (s : ℝ) : Q (D.rhs u s) = D.rhs u s := by
    simp only [ActionODEData.rhs, map_add, hA, hf]
  calc
    Q (u t) = Q (D.y₀ + ∫ s in a..t.1, D.rhs u s) := congrArg Q he
    _ = D.y₀ + ∫ s in a..t.1, Q (D.rhs u s) := by
      rw [map_add, hy, Q.intervalIntegral_comp_comm ht]
    _ = D.y₀ + ∫ s in a..t.1, D.rhs u s := by simp only [hr]
    _ = u t := he.symm

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane

/-! Exact differentiation of the finite factorial-weighted Hilbert jet energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

/-- The bilinear pairing whose diagonal is the actual factorial energy. -/
def factorialPairing (ρ : ℝ) (D Q : JetL2 μ K E) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, inner ℝ (D ⟨j, w⟩) (Q ⟨j, w⟩)

omit [BorelSpace E] [CompleteSpace E] in
theorem factorialPairing_self (ρ : ℝ) (D : JetL2 μ K E) :
    factorialPairing ρ D D = factorialNormSq ρ D := by
  simp only [factorialPairing, factorialNormSq, derivativeNormSq,
    real_inner_self_eq_norm_sq]

omit [BorelSpace E] [CompleteSpace E] in
theorem hasDerivAt_factorialNormSq (ρ : ℝ) {c : ℝ → JetL2 μ K E}
    {q : JetL2 μ K E} {t : ℝ} (hc : HasDerivAt c q t) :
    HasDerivAt (fun s => factorialNormSq ρ (c s))
      (2 * factorialPairing ρ (c t) q) t := by
  have hd (α : JetIndex2 K) : HasDerivAt (fun s => c s α) (q α) t :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 μ E) α).hasFDerivAt.comp_hasDerivAt t hc
  have he := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (HasDerivAt.sum (u := Finset.univ) (fun w _ => (hd ⟨j, w⟩).norm_sq)).const_mul
      (factorialWeight ρ j.val))
  convert he using 1
  · funext s
    simp only [factorialNormSq, derivativeNormSq, Finset.sum_apply]
  · simp only [factorialPairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro w _
    ring
end

/-! Linear identities for the exact factorial jet pairing. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialPairing_neg_left (ρ : ℝ) (D Q : JetL2 μ K E) :
    factorialPairing ρ (-D) Q = -factorialPairing ρ D Q := by
  simp only [factorialPairing, WithLp.ofLp_neg, Pi.neg_apply, inner_neg_left,
    Finset.sum_neg_distrib, mul_neg]

theorem factorialPairing_add_left (ρ : ℝ) (D P Q : JetL2 μ K E) :
    factorialPairing ρ (D + P) Q = factorialPairing ρ D Q + factorialPairing ρ P Q := by
  simp only [factorialPairing, WithLp.ofLp_add, Pi.add_apply, inner_add_left,
    Finset.sum_add_distrib, mul_add]

theorem factorialPairing_smul_left (ρ c : ℝ) (D Q : JetL2 μ K E) :
    factorialPairing ρ (c • D) Q = c * factorialPairing ρ D Q := by
  simp only [factorialPairing, WithLp.ofLp_smul, Pi.smul_apply,
    real_inner_smul_left, ← Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem factorialPairing_comm (ρ : ℝ) (D Q : JetL2 μ K E) :
    factorialPairing ρ D Q = factorialPairing ρ Q D := by
  unfold factorialPairing
  simp_rw [real_inner_comm]
end

/-! Constant Hilbert fiber maps preserve every plane weak derivative. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
variable {U : Set (Vec 2)} {K : ℕ}

/-- Apply a constant fiber map to all raw ordered derivatives. -/
def mapPlaneHk (L : E →L[ℝ] F) (u : PlaneHk U K E) : PlaneHk U K F :=
  PlaneHkFunction.toHk
    { jet := fun a x => L (u.val a x)
      memL2 := fun a => L.comp_memLp' (Lp.memLp (u.val a))
      hasWeakJet := by
        intro j w i e
        have h := u.toFunction.hasWeakJet j w i (L.adjoint e)
        simpa only [PlaneHk.toFunction, planeJetRepresentative,
          ← ContinuousLinearMap.adjoint_inner_left] using h }

theorem mapPlaneHk_component (L : E →L[ℝ] F) (u : PlaneHk U K E) (a : JetIndex2 K) :
    (mapPlaneHk L u).val a = L.compLpL 2 (volume.restrict U) (u.val a) := by
  apply Lp.ext
  exact (jetToL2_ae _ _ a).trans (ContinuousLinearMap.coeFn_compLpL L (u.val a)).symm

/-- The component map commutes with finite sums in the closed graph. -/
theorem planeHk_sum_component {J : Type*} [Fintype J]
    (f : J → PlaneHk U K E) (a : JetIndex2 K) :
    (∑ j, f j).val a = ∑ j, (f j).val a :=
  map_sum (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict U) E) a).comp
      (planeHkGraph (E := E) U K).toSubmodule.subtypeL)) f Finset.univ

theorem planeHk_add_component (u v : PlaneHk U K E) (a : JetIndex2 K) :
    (u + v).val a = u.val a + v.val a :=
  map_add (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict U) E) a).comp
      (planeHkGraph (E := E) U K).toSubmodule.subtypeL)) u v

theorem planeHk_smul_component (c : ℝ) (u : PlaneHk U K E) (a : JetIndex2 K) :
    (c • u).val a = c • u.val a :=
  map_smul (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict U) E) a).comp
      (planeHkGraph (E := E) U K).toSubmodule.subtypeL)) c u
end

/-! Fixed fiber maps act as genuine bounded linear maps on plane Sobolev carriers. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def jetFiberMap {U : Set (Vec 2)} (K : ℕ) (L : E →L[ℝ] F) :
    JetL2 (volume.restrict U) K E →L[ℝ] JetL2 (volume.restrict U) K F :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict U) F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun α => (L.compLpL 2 (volume.restrict U)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict U) E) α)))

theorem jetFiberMap_eq_mapPlaneHk {U : Set (Vec 2)} {K : ℕ}
    (L : E →L[ℝ] F) (q : PlaneHk U K E) :
    jetFiberMap K L q.val = (mapPlaneHk L q).val := by
  apply PiLp.ext
  intro α
  change L.compLpL 2 (volume.restrict U) (q.val α) = _
  exact (mapPlaneHk_component L q α).symm

def mapPlaneHkOperator {U : Set (Vec 2)} (K : ℕ) (L : E →L[ℝ] F) :
    PlaneHk U K E →L[ℝ] PlaneHk U K F :=
  ((jetFiberMap K L).comp (planeHkGraph (E := E) U K).toSubmodule.subtypeL).codRestrict
    (planeHkGraph (E := F) U K).toSubmodule (fun (q : PlaneHk U K E) => by
      change jetFiberMap K L q.val ∈ planeHkGraph (E := F) U K
      rw [jetFiberMap_eq_mapPlaneHk]
      exact (mapPlaneHk L q).property)

@[simp] theorem mapPlaneHkOperator_apply {U : Set (Vec 2)} {K : ℕ}
    (L : E →L[ℝ] F) (q : PlaneHk U K E) : mapPlaneHkOperator K L q = mapPlaneHk L q := by
  apply Subtype.ext
  exact jetFiberMap_eq_mapPlaneHk L q
end

end AVRegularity.CoupledEnergyPlane
end
end
