-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.JointRegularityBoxSmooth
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity
public import AVRegularity.Definitions.CycleWords.IsGeometryCover
import AVRegularity.CycleEvolution.CellBochnerCarrier
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
public import AVRegularity.CoupledEnergyPlane.Fourier.BandSobolev
public import AVRegularity.Statements.Intermediate.Families.IsAnalyticEnvelope
public import AVRegularity.Definitions.Families.MarkedLedger
import AVenhance.Infra.ODE.Linear.Gronwall
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite coefficient regularity suffices to identify its ordered derivative tensor. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a `C^j` coefficient, the ordered coefficient derivative along the word `w` is the
iterated Fréchet derivative along the reversed word. -/
theorem orderedCoefficientDerivative_eq_iterated
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (w : DerivativeWord2 j) (x : Vec 2) :
    orderedCoefficientDerivative C j w x =
      iteratedFDeriv ℝ j C x (fun k => basisVec (w k.rev)) := by
  induction j generalizing C x with
  | zero => simp only [orderedCoefficientDerivative, iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hCj : ContDiff ℝ (j : ℕ) C := hC.of_le (by exact_mod_cast Nat.le_succ j)
    have he : orderedCoefficientDerivative C j (Fin.init w) = fun y =>
        iteratedFDeriv ℝ j C y (fun k => basisVec (Fin.init w k.rev)) :=
      funext (fun y => ih C hCj (Fin.init w) y)
    rw [orderedCoefficientDerivative, he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j C) x :=
      hC.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_succ_self j) x
    have hder := hd.iteratedFDeriv_succ_apply_left'
      (m := fun k : Fin (j + 1) => basisVec (w k.rev))
    have ht : Fin.tail (fun k : Fin (j + 1) => basisVec (w k.rev)) =
        (fun k : Fin j => basisVec (Fin.init w k.rev)) := by
      funext k
      change basisVec (w k.succ.rev) = basisVec (w k.rev.castSucc)
      rw [Fin.rev_succ]
    rw [ht] at hder
    simpa only [Fin.rev_zero] using hder.symm

theorem orderedCoefficientDerivative_norm_le
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedCoefficientDerivative C j w x‖ ≤ ‖iteratedFDeriv ℝ j C x‖ := by
  rw [orderedCoefficientDerivative_eq_iterated C j hC w x]
  have hh := (iteratedFDeriv ℝ j C x).le_opNorm (fun k => basisVec (w k.rev))
  simpa only [show ∀ k : Fin j, ‖basisVec (w k.rev)‖ = 1 by
    intro k; simp [basisVec, Pi.norm_single], Finset.prod_const_one, mul_one] using hh
end

/-! Finite classical coefficient derivatives commute with finite operator sums. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_finset_sum {J : Type*}
    (s : Finset J) (C : J → Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hC : ∀ k ∈ s, ContDiff ℝ (j : ℕ) (C k)) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (fun x => ∑ k ∈ s, C k x) j w =
      fun x => ∑ k ∈ s, orderedCoefficientDerivative (C k) j w x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hcj : ∀ k ∈ s, ContDiff ℝ (j : ℕ) (C k) :=
      fun k hk => (hC k hk).of_le (by exact_mod_cast Nat.le_succ j)
    rw [orderedCoefficientDerivative, ih hcj (Fin.init w)]
    funext x
    rw [fderiv_fun_sum (fun k hk =>
      ((orderedCoefficientDerivative_contDiff (C k) j 1 (hC k hk) (Fin.init w)).differentiable
        (by norm_num)).differentiableAt)]
    simp only [sum_apply, orderedCoefficientDerivative]
end

/-! Ordered scalar metric derivatives retain exactly the available finite regularity. -/

theorem orderedScalarDerivative_contDiff (C : Vec 2 → ℝ) (j m : ℕ)
    (hC : ContDiff ℝ (j + m : ℕ) C) (w : DerivativeWord2 j) :
    ContDiff ℝ (m : ℕ) (orderedScalarDerivative C j w) := by
  induction j generalizing m with
  | zero => simpa only [Nat.zero_add, orderedScalarDerivative] using hC
  | succ j ih =>
    have hCm : ContDiff ℝ (j + (m + 1) : ℕ) C := by
      simpa only [Nat.succ_add, Nat.add_succ] using hC
    have hj := ih (m + 1) hCm (Fin.init w)
    exact (hj.fderiv_right (m := (m : ℕ)) (by simp)).clm_apply contDiff_const

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
namespace AVRegularity.Weighted

/-! Time increments extracted directly from the integrated plane weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The spatial integrand of the coupled weak identity. -/
def planeWeakSpatialRhs (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E) (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
    - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
    - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
    + inner ℝ (g s x) (φ x)

/-- A fixed spatial test may be used between any two times of the solution window. -/
theorem coupledWeakIdentity_fixed_increment
    (μ : Measure (Vec 2)) {ν a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (u : ℝ → Vec 2 → E)
    (f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E)
    (h : ∀ t ∈ Icc a b,
      CoupledWeakIdentity μ ν a t v (u t) f φ dφ du flux F g)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ x, inner ℝ (u t x) (φ x) ∂μ) -
        (∫ x, inner ℝ (u s x) (φ x) ∂μ) =
      ∫ r in s..t, ∫ x, planeWeakSpatialRhs ν v φ dφ du flux F g r x ∂μ := by
  let q : ℝ → ℝ := fun r =>
    ∫ x, planeWeakSpatialRhs ν v φ dφ du flux F g r x ∂μ
  have hb := h b ⟨hab, le_rfl⟩
  have hq : IntervalIntegrable q volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hb.2.2.2.1
  have hqs : IntervalIntegrable q volume a s := hq.mono_set (by
    rw [uIcc_of_le hs.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2)
  have hqt : IntervalIntegrable q volume a t := hq.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2)
  have hes := (h s hs).2.2.2.2
  have het := (h t ht).2.2.2.2
  change (∫ x, inner ℝ (u s x) (φ x) ∂μ) -
    (∫ x, inner ℝ (f x) (φ x) ∂μ) = ∫ r in Ioc a s, q r at hes
  change (∫ x, inner ℝ (u t x) (φ x) ∂μ) -
    (∫ x, inner ℝ (f x) (φ x) ∂μ) = ∫ r in Ioc a t, q r at het
  rw [← intervalIntegral.integral_of_le hs.1] at hes
  rw [← intervalIntegral.integral_of_le ht.1] at het
  change _ = ∫ r in s..t, q r
  rw [← intervalIntegral.integral_interval_sub_left hqt hqs, ← het, ← hes]
  ring

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Weighted

/-! The literal slow Taylor evaluation preserves measurable dependence on time. -/

theorem taylorSlow_parameter_measurable (lo K : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → ℝ)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t z, ContDiff ℝ (K : ℕ) (fun X => f t X z))
    (X₀ : Vec 2) (δ : ℝ) (z : Vec 2) :
    Measurable (fun t => taylorSlow lo K (fun X => f t X z) X₀ (δ • z)) := by
  unfold taylorSlow
  apply Finset.measurable_fun_sum
  intro r hr
  apply Measurable.const_mul
  exact parameter_iteratedFDeriv_apply_measurable (fun t X => f t X z)
    (fun X => hm X z) K r (fun t => hf t z) (Finset.mem_Icc.mp hr).2 X₀ (fun _ => δ • z)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Transfer an integrated weak equation along actual almost everywhere equal right sides. -/

def weakIdentityRhs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E) :=
  fun s x => -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
    - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
    - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
    + inner ℝ (g s x) (φ x)

theorem coupledWeakIdentity_rhs_transfer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux F flux' F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g g' : ℝ → Vec 2 → E)
    (hold : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g)
    (hnew : ∀ s ∈ Set.Ioc a t, Integrable (weakIdentityRhs ν v φ dφ du' flux' F' g' s) μ)
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)),
      weakIdentityRhs ν v φ dφ du' flux' F' g' s =ᵐ[μ]
        weakIdentityRhs ν v φ dφ du flux F g s) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du' flux' F' g' := by
  have he : (fun s => ∫ x, weakIdentityRhs ν v φ dφ du' flux' F' g' s x ∂μ)
      =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F g s x ∂μ) :=
    hae.mono (fun _ hs => integral_congr_ae hs)
  rcases hold with ⟨hu, hf, _, hi, heq⟩
  refine ⟨hu, hf, hnew, hi.congr he.symm, ?_⟩
  exact heq.trans (integral_congr_ae he).symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Weighted

/-! Gronwall closure for the scalar energies produced by bounded-weight tests. -/

/-- An absolutely continuous weighted energy with nonnegative dissipation obeys
the usual retained-dissipation Gronwall bound. -/
theorem scalar_energy_dissipation_le_gronwall {a b : ℝ} (hab : a ≤ b)
    {E P : ℝ → ℝ} (hE : AVRegularity.CycleEvolution.StrongTimeRegularity a b E P)
    (C : ℝ) (hC : 0 ≤ C) (f d : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hd : IntervalIntegrable d volume a b)
    (hf_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), 0 ≤ f t)
    (hd_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), 0 ≤ d t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Set.Icc a b), P t + d t ≤ C * E t + f t) :
    ∀ t ∈ Set.Icc a b,
      E t + ∫ s in a..t, d s ≤
        (E a + ∫ s in a..b, f s) * Real.exp (C * (t - a)) := by
  let Y : ℝ → ℝ := fun t => E t + ∫ s in a..t, d s
  have hEcont : ContinuousOn E (Icc a b) := by
    simpa only [uIcc_of_le hab] using hE.ac.continuousOn
  have hdcont : ContinuousOn (fun t => ∫ s in a..t, d s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hd left_mem_uIcc
  have hYcont : ContinuousOn Y (Icc a b) := hEcont.add hdcont
  have hYint : IntervalIntegrable Y volume a b := hYcont.intervalIntegrable_of_Icc hab
  have hCEint : IntervalIntegrable (fun t => C * Y t) volume a b :=
    (continuousOn_const.mul hYcont).intervalIntegrable_of_Icc hab
  have hCEint' : IntervalIntegrable (fun t => C * E t) volume a b :=
    (continuousOn_const.mul hEcont).intervalIntegrable_of_Icc hab
  have hEle (t : ℝ) (ht : t ∈ Icc a b) : E t ≤ Y t := by
    have hdt : ∀ᵐ s ∂volume.restrict (Icc a t), 0 ≤ d s := by
      rw [← restrict_Ioc_eq_restrict_Icc]
      exact hd_nonneg.filter_mono (ae_mono
        (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
    have hn := intervalIntegral.integral_nonneg_of_ae_restrict ht.1 hdt
    exact le_add_of_nonneg_right hn
  have hineq : ∀ t ∈ Icc a b,
      Y t ≤ (E a + ∫ s in a..b, f s) + ∫ s in a..t, C * Y s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hg := hgrowth.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hEt := hE.mono hsub
    have hPInt : IntervalIntegrable P volume a t :=
      hEt.scalar_derivative_intervalIntegrable
    have hdInt : IntervalIntegrable d volume a t :=
      hd.mono_set (c := a) (d := t) hsub
    have hCEInt : IntervalIntegrable (fun s => C * E s) volume a t :=
      hCEint'.mono_set (c := a) (d := t) hsub
    have hfInt : IntervalIntegrable f volume a t :=
      hf.mono_set (c := a) (d := t) hsub
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      (hPInt.add hdInt) (hCEInt.add hfInt) hg
    rw [intervalIntegral.integral_add hPInt hdInt,
      intervalIntegral.integral_add hCEInt hfInt] at hbound
    have hPinc : (∫ s in a..t, P s) = E t - E a := by
      calc
        _ = ∫ s in a..t, deriv E s := by
          apply intervalIntegral.integral_congr_ae_restrict
          have hder := hEt.derivative.filter_mono
            (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
          filter_upwards [hder] with s hs
          exact hs.deriv.symm
        _ = E t - E a := hEt.ac.integral_deriv_eq_sub
    rw [hPinc] at hbound
    have hfbound := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf_nonneg hf
    have hCbound : (∫ s in a..t, C * E s) ≤ ∫ s in a..t, C * Y s := by
      apply intervalIntegral.integral_mono_on ht.1 hCEInt
        (hCEint.mono_set (c := a) (d := t) hsub)
      intro s hs
      exact mul_le_mul_of_nonneg_left (hEle s ⟨hs.1, hs.2.trans ht.2⟩) hC
    dsimp only [Y]
    linarith
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hCEint (fun _ _ => hC) hineq
  intro t ht
  simpa only [Y, intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a) C]
    using hgr t ht

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Uniform finite derivative array bounds imply finiteness of the literal coefficient seminorm. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_zero_function (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (fun _ : Vec 2 => (0 : E →L[ℝ] F)) j w = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [orderedCoefficientDerivative, ih]
    funext x
    simp

theorem coefficientSeminorm_ne_top_of_array_bound (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (M : Fin (K + 1) → ℝ)
    (hb : ∀ (j : Fin (K + 1)) t, t ∈ Set.Icc a b → ∀ x,
      ‖coefficientDerivativeArray (A t) j.val x‖ ≤ M j) :
    coefficientSeminorm ρ K a b A ≠ ⊤ := by
  unfold coefficientSeminorm
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top (show ENNReal.ofReal (M ⟨j, Finset.mem_range.mp hj⟩) ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply iSup_le
  intro x
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (hb ⟨j, Finset.mem_range.mp hj⟩ t ht x)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Time integrability in the closed weak Sobolev graph follows from its literal stored jets. -/

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace T]

theorem planeHk_time_memLp_of_jets {U : Set (Vec 2)} {K : ℕ}
    (μ : Measure T) (u : T → PlaneHk U K E)
    (hj : ∀ α, MemLp (fun t => (u t).val α) 2 μ) : MemLp u 2 μ := by
  have hp : MemLp (fun t α => (u t).val α) 2 μ := memLp_pi_iff.mpr hj
  have hv : MemLp (fun t => (u t).val) 2 μ := by
    simpa only [Function.comp_def] using!
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : JetIndex2 K => ComponentL2 (volume.restrict U) E)).symm.toContinuousLinearMap.comp_memLp' hp
  have hm : AEStronglyMeasurable u μ :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hv.aestronglyMeasurable
  exact (memLp_congr_norm hm hv.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => rfl))).mpr hv

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Weighted

/-! Time-window extensions preserve the measurable literal Taylor coefficient on the window. -/

attribute [local instance] Classical.propDecidable

theorem taylorSlow_time_window_measurable (I : Set ℝ) (hI : MeasurableSet I)
    (lo K : ℕ) (f : ℝ → Vec 2 → Vec 2 → ℝ)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t ∈ I, ∀ z, ContDiff ℝ (K : ℕ) (fun X => f t X z))
    (X₀ : Vec 2) (δ : ℝ) (z : Vec 2) :
    Measurable (fun t => if t ∈ I then
      taylorSlow lo K (fun X => f t X z) X₀ (δ • z) else 0) := by
  classical
  let g := fun t X z => if t ∈ I then f t X z else 0
  have hgm (X z : Vec 2) : Measurable (fun t => g t X z) :=
    (hm X z).piecewise hI measurable_const
  have hgf (t : ℝ) (z : Vec 2) : ContDiff ℝ (K : ℕ) (fun X => g t X z) := by
    by_cases ht : t ∈ I
    · simpa only [g, ite_eq_left ht] using hf t ht z
    · simpa only [g, ite_eq_right ht] using (contDiff_const : ContDiff ℝ (K : ℕ)
        (fun _ : Vec 2 => (0 : ℝ)))
  have hmt := taylorSlow_parameter_measurable lo K g hgm hgf X₀ δ z
  have hp : Measurable (fun t => if t ∈ I then
      taylorSlow lo K (fun X => g t X z) X₀ (δ • z) else 0) :=
    hmt.piecewise hI (measurable_const (a := (0 : ℝ)))
  convert hp using 1
  funext t
  by_cases ht : t ∈ I
  · simp only [ite_eq_left ht, g]
  · simp only [ite_eq_right ht]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.ChartTransport
namespace AVRegularity.Weighted

/-! Coordinate expansion of a variable multilinear coefficient on the diagonal. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem multilinear_diagonal_coordinate_expansion {r : ℕ}
    (a : ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) E) (z : Vec 2) (δ : ℝ) :
    a (fun _ => δ • z) = ∑ w : DerivativeWord2 r,
      (∏ i, δ * z (w i)) • a (fun i => basisVec (w i)) := by
  have hz : (fun _ : Fin r => δ • z) =
      fun i => ∑ k : Fin 2, (δ * z k) • basisVec k := by
    funext i
    rw [vec2_eq_sum_basisVec (δ • z)]
    rfl
  rw [hz]
  have hs := a.toMultilinearMap.map_sum (fun (_ : Fin r) k => (δ * z k) • basisVec k)
  change (a (fun i => ∑ k : Fin 2, (δ * z k) • basisVec k)) = _ at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro w _
  exact a.map_smul_univ (fun i => δ * z (w i)) (fun i => basisVec (w i))

theorem multilinear_diagonal_contDiff {r : ℕ} (J : ℕ)
    (a : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) E)
    (ha : ContDiff ℝ (J : ℕ) a) (δ : ℝ) :
    ContDiff ℝ (J : ℕ) (fun z => a z (fun _ => δ • z)) := by
  simp_rw [multilinear_diagonal_coordinate_expansion]
  apply ContDiff.sum
  intro w _
  apply ContDiff.smul
  · apply contDiff_prod
    intro i _
    exact contDiff_const.mul ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) (w i)).contDiff)
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))).contDiff.comp ha

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Scalar matrix entry derivatives act on their constant operator blocks literally. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_smul_const
    (c : Vec 2 → ℝ) (j : ℕ) (hc : ContDiff ℝ (j : ℕ) c)
    (T : E →L[ℝ] F) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (fun x => c x • T) j w =
      fun x => orderedScalarDerivative c j w x • T := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hcj : ContDiff ℝ (j : ℕ) c := hc.of_le (by exact_mod_cast Nat.le_succ j)
    have he := ih hcj (Fin.init w)
    funext x
    rw [orderedCoefficientDerivative, he]
    dsimp only
    rw [fderiv_smul_const
        (((orderedScalarDerivative_contDiff c j 1 hc (Fin.init w)).differentiable
          (by norm_num)).differentiableAt) T]
    rfl
end

/-! A coordinate monomial times a bounded classical jet has the monomial's growth degree. -/

theorem coordinate_monomial_times_bounded_jet_growth {T : Type*} {r : ℕ}
    (J : ℕ) (w : DerivativeWord2 r) (δ B : ℝ) (hB : 0 ≤ B)
    (b : T → Vec 2 → ℝ) (hb : ∀ t, ContDiff ℝ (J : ℕ) (b t))
    (hbb : ∀ t j, j ≤ J → ∀ x, ‖iteratedFDeriv ℝ j (b t) x‖ ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => (∏ i, δ * x (w i)) * b t x) x‖ ≤
        A * (1 + ‖x‖) ^ r := by
  obtain ⟨M, hM, hMb⟩ := coordinate_monomial_jet_growth J w δ
  let A : ℝ := (∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ)) * M * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro t
  have hp : ContDiff ℝ (J : ℕ) (fun x : Vec 2 => ∏ i, δ * x (w i)) := by
    apply contDiff_prod
    intro i _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ (w i))
  have hh := growing_scalar_jet_product_bound J r 0 _ _ hp (hb t) M B hM hB hMb
    (fun j hj x => by simpa only [pow_zero, mul_one] using hbb t j hj x)
  simpa only [A, Nat.add_zero] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Reducing a positive radius decreases the public factorial data budgets. -/

theorem factorial_weight_radius_mono {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ r) (j : ℕ) :
    factorialWeight ρ j ≤ factorialWeight r j := by
  unfold factorialWeight
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ hr (2 * j)) (sq_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedFactorialNormSq_radius_mono {K' : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ r)
    (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedFactorialNormSq n ϖ zc ρ K U ≤ weightedFactorialNormSq n ϖ zc r K U := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (factorial_weight_radius_mono hρ hr j)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.Weighted

/-! Genuine spatial projections can be removed from each integrable fixed-test time pairing. -/

theorem intervalIntegrable_inner_const {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {s t : ℝ} (f : ℝ → H)
    (hf : IntervalIntegrable f volume s t) (z : H) :
    IntervalIntegrable (fun r => inner ℝ (f r) z) volume s t := by
  let L : H →L[ℝ] ℝ := InnerProductSpace.toDualMap ℝ H z
  have h : IntervalIntegrable (fun r => L (f r)) volume s t :=
    ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩
  simpa only [L, InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem intervalIntegrable_projection_pair {s t : ℝ}
    (f : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hf : IntervalIntegrable f volume s t)
    (z : Lp E 2 (volume : Measure (Vec 2))) (N : ℕ) :
    IntervalIntegrable (fun r => inner ℝ (hilbertProjection N (f r)) z) volume s t := by
  have hp : IntervalIntegrable (fun r => hilbertProjection N (f r)) volume s t :=
    ⟨(hilbertProjection (E := E) N).integrable_comp hf.1,
      (hilbertProjection (E := E) N).integrable_comp hf.2⟩
  exact intervalIntegrable_inner_const _ hp z

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem tendsto_projection_time_pairing {s t : ℝ} (hst : s ≤ t)
    (f : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hf : IntervalIntegrable f volume s t)
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun N => ∫ r in s..t, inner ℝ (hilbertProjection N (f r)) z)
      atTop (𝓝 (∫ r in s..t, inner ℝ (f r) z)) := by
  simp only [intervalIntegral.integral_of_le hst]
  apply tendsto_integral_of_dominated_convergence (fun r => ‖f r‖ * ‖z‖)
  · intro N
    exact ((hilbertProjection N).continuous.comp_aestronglyMeasurable
      hf.1.aestronglyMeasurable).inner aestronglyMeasurable_const
  · exact hf.1.norm.mul_const ‖z‖
  · intro N
    exact Eventually.of_forall (fun r => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hilbertProjection_norm_le N (f r)) (norm_nonneg z)))
  · exact Eventually.of_forall (fun r =>
      (tendsto_hilbertProjection (f r)).inner (𝕜 := ℝ) tendsto_const_nhds)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A finite coordinate polynomial with bounded coefficient jets has growth of its degree. -/

theorem finite_monomial_jet_growth {T : Type*} {r : ℕ} (J : ℕ)
    (b : DerivativeWord2 r → T → Vec 2 → ℝ)
    (hb : ∀ w t, ContDiff ℝ (J : ℕ) (b w t)) (δ B : ℝ) (hB : 0 ≤ B)
    (hbb : ∀ w t j, j ≤ J → ∀ x, ‖iteratedFDeriv ℝ j (b w t) x‖ ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j
        (fun x => ∑ w : DerivativeWord2 r, (∏ i, δ * x (w i)) * b w t x) x‖ ≤
        A * (1 + ‖x‖) ^ r := by
  have hp (w : DerivativeWord2 r) : ContDiff ℝ (J : ℕ)
      (fun x : Vec 2 => ∏ i, δ * x (w i)) := by
    apply contDiff_prod
    intro i _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ (w i))
  exact finite_scalar_growth_sum_exists Finset.univ J r
    (fun w t x => (∏ i, δ * x (w i)) * b w t x) (fun _ => r)
    (fun _ _ => le_rfl) (fun w _ t => (hp w).mul (hb w t))
    (fun w _ => coordinate_monomial_times_bounded_jet_growth J w δ B hB
      (b w) (hb w) (hbb w))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Nonzero constituent maps have finite reserved independent coefficient jets. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem analyticEnvelope_reserved_jet_ne_top
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (dom : F.Domain) (Ks J : ℕ) (b : ι → ι → ℝ)
    (hf : IsAnalyticEnvelope F π dom 1 1 Ks J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (w : DerivativeWord2 (d - 1)) (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ J) :
    jetSupFam (fun x : F.Index => dom x.1 x.2) r q
      (fun x => F.slowFlux 1 x.1 x.2 v u γ d w) ≠ ⊤ := by
  have hh := hf.2 v u
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hh
  have hmass : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hs := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh) hmass).ne
  have hg := ENNReal.sum_ne_top.mp hs γ (Finset.mem_univ γ)
  have hn : ENNReal.ofReal ‖(F.identity v u γ).map‖ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hγ)).ne'
  have hs' := (ENNReal.lt_top_of_mul_ne_top_right hg hn).ne
  have hd' := ENNReal.sum_ne_top.mp hs' d hd
  have hw := ENNReal.sum_ne_top.mp hd' w (Finset.mem_univ w)
  have hr' := ENNReal.sum_ne_top.mp hw r (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  exact ENNReal.sum_ne_top.mp hr' q (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A bounded family of multilinear coefficient jets gives diagonal polynomial jet growth. -/

theorem multilinear_diagonal_jet_growth {T : Type*} {r : ℕ} (J : ℕ)
    (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ)
    (ha : ∀ t, ContDiff ℝ (J : ℕ) (a t)) (δ B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => a t x (fun i => basisVec (w i))) x‖ ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => a t x (fun _ => δ • x)) x‖ ≤
        A * (1 + ‖x‖) ^ r := by
  have hc (w : DerivativeWord2 r) (t : T) : ContDiff ℝ (J : ℕ)
      (fun x => a t x (fun i => basisVec (w i))) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
      (fun i => basisVec (w i))).contDiff.comp (ha t)
  obtain ⟨A, hA, hAb⟩ := finite_monomial_jet_growth J
    (fun w t x => a t x (fun i => basisVec (w i))) hc δ B hB
    (fun w t j hj x => hb t w j hj x)
  refine ⟨A, hA, ?_⟩
  intro t j hj x
  have he : (fun x => a t x (fun _ => δ • x)) =
      fun x => ∑ w : DerivativeWord2 r, (∏ i, δ * x (w i)) *
        a t x (fun i => basisVec (w i)) := by
    funext x
    simpa only [smul_eq_mul] using multilinear_diagonal_coordinate_expansion (a t x) x δ
  rw [he]
  exact hAb t j hj x

/-! Small definitional readouts for the one-chart independent coefficient family. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem ofFiber_slowFlux_one_eq (edge : ConstituentEdges D h) (v u : ι)
    (o : Finset.Icc 2 D) (k : Fin (edge v u o).length)
    (w : DerivativeWord2 (o.1 - 1)) :
    (ChartedFamily.ofFiber edge).slowFlux 1 () () v u ⟨o, k⟩ o.1 w =
      ((edge v u o).get k).coeff w := by
  funext t X z
  simp only [ChartedFamily.slowFlux, ChartedFamily.ofFiber, dite_true, inv_one, one_smul]

theorem ofFiber_jetSupOn_le_jetSupFam (edge : ConstituentEdges D h)
    (dom : Set (ℝ × Vec 2)) (v u : ι)
    (o : Finset.Icc 2 D) (k : Fin (edge v u o).length)
    (w : DerivativeWord2 (o.1 - 1)) (r q : ℕ) :
    jetSupOn dom r q (((edge v u o).get k).coeff w) ≤
      jetSupFam (fun _ : (ChartedFamily.ofFiber edge).Index => dom) r q
        (fun x => (ChartedFamily.ofFiber edge).slowFlux 1 x.1 x.2 v u ⟨o, k⟩ o.1 w) := by
  rw [← ofFiber_slowFlux_one_eq edge v u o k w]
  exact le_iSup (fun x : (ChartedFamily.ofFiber edge).Index =>
    jetSupOn dom r q ((ChartedFamily.ofFiber edge).slowFlux 1 x.1 x.2 v u ⟨o, k⟩ o.1 w))
    ⟨(), ()⟩
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Continuous value and gradient readouts for the plane `H¹` carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Read the two weak first derivatives of a plane `H¹` element as one `L²` vector field. -/
def planeH1GradientOperator :
    PlaneHk Set.univ 1 E →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin 2 =>
      univToPlane.toContinuousLinearMap.comp
        ((PiLp.proj (𝕜 := ℝ) 2
          (fun _ : JetIndex2 1 => ComponentL2 (volume.restrict Set.univ) E)
          ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩).comp
          (planeHkGraph (E := E) Set.univ 1).toSubmodule.subtypeL))

omit [FiniteDimensional ℝ E] in
@[simp] theorem planeH1GradientOperator_apply (u : PlaneHk Set.univ 1 E) (k : Fin 2) :
    planeH1GradientOperator (E := E) u k =
      univToPlane (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) := by
  rfl

end AVRegularity.Weighted
end
end
