-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Compact localization on the actual torus and plane Sobolev carriers. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}

def localizeTorusCarrier (w : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) : PlaneHk Set.univ K F :=
  (localizePeriodicCoefficient w.toFunction C hC hc).toHk

theorem localizeTorusCarrier_jet_ae (w : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) (a : JetIndex2 K) :
    (localizeTorusCarrier w C hC hc).toFunction.jet a =ᵐ[volume]
      multiplicationRawJet C w.toFunction.jet a := by
  simpa only [localizeTorusCarrier, localizePeriodicCoefficient, Measure.restrict_univ] using
    (localizePeriodicCoefficient w.toFunction C hC hc).toHk_toFunction_ae a

theorem localizeTorusCarrier_value_ae (w : TorusHk K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) :
    (localizeTorusCarrier w C hC hc).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      fun x => C x (w.toFunction.jet (valueIndex2 K) x) := by
  filter_upwards [localizeTorusCarrier_jet_ae w C hC hc (valueIndex2 K)] with x hx
  exact hx.trans (multiplicationRawJet_value C w.toFunction.jet x)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Weak solutions see the transformed drift only on their actual time window. -/

theorem coupledWeakIdentity_drift_window_congr {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure (Vec 2)} {ν a t : ℝ} {v v' : ℝ → Vec 2 → Vec 2}
    {u f φ : Vec 2 → E} {dφ : Fin 2 → Vec 2 → E} {du : ℝ → Fin 2 → Vec 2 → E}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {g : ℝ → Vec 2 → E}
    (hv : ∀ s ∈ Set.Ioc a t, v s = v' s)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v' u f φ dφ du flux F g := by
  apply coupledWeakIdentity_integrands_congr μ ν a t v v' u u f f φ φ dφ dφ
    du du flux flux F F g g Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ hs
  intro s hmem
  exact weakIdentityRhs_congr_ae μ ν s v v' φ φ dφ dφ du du flux flux F F g g
    (Filter.Eventually.of_forall (fun x => congrFun (hv s hmem) x))
    Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_drift_window_congr {ν a b : ℝ}
    {v v' : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ i j, (o : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (o.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hv : ∀ t ∈ Set.Icc a b, v t = v' t)
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v' D K A f F g u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  exact coupledWeakIdentity_drift_window_congr
    (fun s hmem => hv s ⟨hmem.1.le, hmem.2.trans ht.2⟩) (hs.2.2.2.2 i t ht φ)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal jet integrals read the actual torus and localized plane carrier energies. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem torusHk_component_norm_sq (f : TorusHk K E) (a : JetIndex2 K) :
    ‖f.val a‖ ^ 2 = ∫ x in AVenhance.unitCube, ‖f.toFunction.jet a x‖ ^ 2 ∂volume := by
  have he := periodicJetRepresentative_ae f.val a
  have hi : (∫ x in AVenhance.unitCube, ‖periodicJetRepresentative f.val a x‖ ^ 2 ∂volume) =
      ∫ x in AVenhance.unitCube, ‖(f.val a) x‖ ^ 2 ∂volume :=
    integral_congr_ae (he.mono (fun _ h => congrArg (fun z : E => ‖z‖ ^ 2) h))
  change ‖f.val a‖ ^ 2 = ∫ x in AVenhance.unitCube, ‖periodicJetRepresentative f.val a x‖ ^ 2 ∂volume
  rw [hi]
  simpa only [Lp.toLp_coeFn] using normSq_toLp_eq_integral (Lp.memLp (f.val a))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ E]

theorem localizeTorusCarrier_component_norm_sq (f : TorusHk K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hc : HasCompactSupport C) (a : JetIndex2 K) :
    ‖(localizeTorusCarrier f C hC hc).val a‖ ^ 2 =
      ∫ x, ‖multiplicationRawJet C f.toFunction.jet a x‖ ^ 2 ∂volume := by
  have hi := normSq_toLp_eq_integral
    (Lp.memLp ((localizeTorusCarrier f C hC hc).val a))
  simp only [Lp.toLp_coeFn, Measure.restrict_univ] at hi
  apply hi.trans
  apply integral_congr_ae
  exact (localizeTorusCarrier_jet_ae f C hC hc a).mono
    (fun _ h => congrArg (fun z : F => ‖z‖ ^ 2) h)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Finite pointwise coefficient seminorms survive positive diffusion time normalization. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normalized coefficient has a finite seminorm at every positive radius with a finite source budget. -/
theorem coefficientSeminorm_diffusion_normalized_ne_top
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤) :
    coefficientSeminorm ρ K (ν * a) (ν * b)
      (fun t x => ν⁻¹ • A (ν⁻¹ * t) x) ≠ ⊤ := by
  apply coefficientSeminorm_ne_top_of_array_bound ρ K (ν * a) (ν * b) _
    (fun j => ν⁻¹ * (coefficientOrderSup a b A j.val).toReal)
  intro j t ht x
  have ht' : ν⁻¹ * t ∈ Set.Icc a b := by
    rw [show ν⁻¹ * t = t / ν by rw [div_eq_mul_inv, mul_comm]]
    exact ⟨(le_div_iff₀ hν).mpr (by simpa only [mul_comm] using ht.1),
      (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using ht.2)⟩
  rw [coefficientDerivativeArray_const_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hν)]
  exact mul_le_mul_of_nonneg_left
    (coefficientOrderSup_derivative_bound ρ hρ K a b A hA j.val
      (Nat.le_of_lt_succ j.isLt) _ ht' x) (inv_nonneg.mpr hν.le)

end AVRegularity.CycleJointProofs
end
