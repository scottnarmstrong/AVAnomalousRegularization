-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.KernelSchurTimeRestriction
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
public import AVRegularity.KernelEnergy.TorusTimeFlux
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.Velocity.IncrementProvider
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm

section
@[expose] public noncomputable section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Uniform molecular estimates recover the actual higher carrier at a fixed positive time. -/

open CoupledEnergy.Variational CoupledEnergy.Galerkin
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_higher_carrier_of_uniform_mass_bound_and_H1_pairings (K : ι → ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (M : ℝ) (f : ℕ → ∀ i, TorusHk (K i) (h i)) (g : ∀ i, TorusHk 0 (h i))
    (hsqrt : ∀ n, Real.sqrt (massNormSq ρ π (fun i => (f n i).val)) ≤ M)
    (hpair : ∀ i, ∀ ψ : TorusHk 1 (h i),
      Tendsto (fun n => inner ℝ (torusHkValueCLM (f n i)) (torusHkValueCLM ψ))
        atTop (𝓝 (inner ℝ (torusHkValueCLM (g i)) (torusHkValueCLM ψ)))) :
    ∃ F : ∀ i, TorusHk (K i) (h i),
      (∀ i, truncateTorusHk (Nat.zero_le (K i)) (F i) = g i) ∧
      Real.sqrt (massNormSq ρ π (fun i => (F i).val)) ≤ M := by
  let u : ℕ → CoupledLowHilbert (h := h) K :=
    fun n => WithLp.toLp 2 (fun i => (f n i).val)
  let C : ℝ := ∑ i, π i / factorialWeightMin ρ (K i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    div_nonneg (hπ i).le (factorialWeightMin_pos ρ hρ).le)
  have hbound (n : ℕ) : massNormSq ρ π (fun i => (f n i).val) ≤ M ^ 2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg _) (hsqrt n)
    simpa only [← pow_two, Real.sq_sqrt (massNormSq_nonneg ρ π hπ _)] using hh
  have hu : ∀ n, ‖u n‖ ≤ Real.sqrt (C * M ^ 2) := by
    intro n
    apply Real.le_sqrt_of_sq_le
    exact (coupledLowHilbert_normSq_le_mass K ρ hρ π hπ (u n)).trans
      (mul_le_mul_of_nonneg_left (hbound n) hC)
  obtain ⟨V, φ, hφ, hw⟩ := exists_strictMono_tendsto_lowHilbert_clm K _ u hu
  refine ⟨familyGraphReadout (h := h) K V, ?_, ?_⟩
  · intro i
    apply torusHk_eq_of_H1_value_pairings 0
    intro ψ
    have hread := familyGraphReadout_val_of_weak_limit (h := h) K (fun n => f (φ n)) V hw i
    have hlim := hw ((innerSL ℝ (torusHkValueCLM ψ)).comp (familyValueReadout (h := h) K i))
    have hv : Tendsto (fun n => inner ℝ (torusHkValueCLM (f (φ n) i))
        (torusHkValueCLM ψ)) atTop
        (𝓝 (inner ℝ (familyValueReadout (h := h) K i V) (torusHkValueCLM ψ))) := by
      change Tendsto (fun n => inner ℝ (torusHkValueCLM ψ)
        (torusHkValueCLM (f (φ n) i))) atTop
        (𝓝 (inner ℝ (torusHkValueCLM ψ) (familyValueReadout (h := h) K i V))) at hlim
      have heq : inner ℝ (torusHkValueCLM ψ) (familyValueReadout (h := h) K i V) =
          inner ℝ (familyValueReadout (h := h) K i V) (torusHkValueCLM ψ) :=
        real_inner_comm _ _
      rw [heq] at hlim
      exact hlim.congr' (Eventually.of_forall (fun n => real_inner_comm _ _))
    have he := tendsto_nhds_unique hv ((hpair i ψ).comp hφ.tendsto_atTop)
    change inner ℝ ((familyGraphReadout (h := h) K V i).val (valueIndex2 (K i)))
      (torusHkValueCLM ψ) = _
    rw [hread]
    exact he
  · exact familyGraphReadout_mass_bound (h := h) K ρ π hπ M (fun n => f (φ n)) V hw
      (fun n => hsqrt (φ n))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Restrict a literal kernel operator without changing its spatial data. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]



def kernelOperator_time_restrict {a b c d ρ ν : ℝ} {k D : ℕ}
    (P : KernelEnergy.TorusKernelOperator a b ρ ν k D (h := h) (Γ := Γ) (G := G))
    (hsub : Set.Icc c d ⊆ Set.Icc a b) (hcd : c ≤ d) :
    KernelEnergy.TorusKernelOperator c d ρ ν k D (h := h) (Γ := Γ) (G := G) where
  htime := hcd
  radius_pos := P.radius_pos
  diffusivity_pos := P.diffusivity_pos
  order_ge_two := P.order_ge_two
  π := P.π
  hπ := P.hπ
  B := P.B
  hB_meas := by
    intro i j α q
    exact (P.hB_meas i j α q).comp
      (((measurable_subtype_coe.comp measurable_fst).subtype_mk
        (h := fun p : Set.Icc c d × Vec 2 => hsub p.1.property)).prodMk measurable_snd)
  hB_smooth := fun i j α q t ht => P.hB_smooth i j α q t (hsub ht)
  hB_per := fun i j α q t ht => P.hB_per i j α q t (hsub ht)
  hB_fin := by
    intro i j α q
    exact ne_top_of_le_ne_top (P.hB_fin i j α q)
      (CycleJointProofs.coefficientSeminorm_time_mono ρ k c d a b hsub _)
  C := P.C
  S := P.S
  c := P.c
  r := P.r
  hr := P.hr
  hS := fun i j α => spatialRegularizerTorus_time_restrict (P.hS i j α) hsub
  θ := P.θ
  hθ := P.hθ
  hschur := kernelSchurBound_time_restrict P hsub

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Explicit all-order drift arrays for the actual OC velocity. -/

def actualDriftJetConstant : ℝ := ‖Weighted.driftCoefficientEmbedding‖ * 8192

theorem actualDriftJetConstant_nonneg : 0 ≤ actualDriftJetConstant :=
  mul_nonneg (norm_nonneg Weighted.driftCoefficientEmbedding) (by norm_num)

theorem actual_stream_drift_arrays
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (j : ℕ) (hj : 1 ≤ j) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ m) t)) j x‖ ≤
      (actualDriftJetConstant * ocA α q Λ m) * 1024 ^ j * (j.factorial : ℝ) *
        (ocEpsilon q Λ m) ^ ((1 : ℤ) - j) := by
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hfield := AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (Velocity.streamSeq_admissible hζ hΛ hΦ m)
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ m) t) :=
    hfield.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hb := drift_array_norm_le_geometric j hsmooth
    (mul_pos (by norm_num) (inv_pos.mpr he))
    (mul_nonneg (mul_nonneg (by norm_num) ha.le) he.le)
    (actual_stream_drift_snorm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm t j hj) x
  exact hb.trans_eq (drift_scaled_geometric_identity _ _ _ he.ne' j)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Metric MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Bounded two-coordinate holomorphic data control all actual mixed real base jets. -/

theorem two_coordinate_cauchy_exists_real_jet_bounds (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (F : ℂ → ℂ → ℂ),
        (∀ z ∈ closedBall 0 R, DiffContOnCl ℂ (fun w => F w z) (ball 0 R)) →
        (∀ w ∈ closedBall 0 R, DiffContOnCl ℂ (F w) (ball 0 R)) →
        Continuous (fun p : ℝ × ℝ => F (circleMap 0 R p.1) (circleMap 0 R p.2)) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ θ φ : ℝ, ‖F (circleMap 0 R θ) (circleMap 0 R φ)‖ ≤ M) →
          ContDiffAt ℝ (n : ℕ∞) (fun x : Vec 2 => F (x 0 : ℂ) (x 1 : ℂ)) 0 ∧
            ∀ j ≤ n, ‖iteratedFDeriv ℝ j
              (fun x : Vec 2 => F (x 0 : ℂ) (x 1 : ℂ)) 0‖ ≤ B j * M := by
  obtain ⟨χ, hχ, heχ, hb, hout⟩ := exists_smooth_bounded_local_identity
    (E := Vec 2) (R / 2) (by positivity)
  have hz : χ 0 = 0 := heχ.eq_of_nhds
  let μ := cauchyAngleMeasure.prod cauchyAngleMeasure
  obtain ⟨C, hC, hInt⟩ := localized_cauchy_integral_regular_and_jet_bound
    R hR χ hχ hb hz hout μ n
  let A : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2
  let B : ℕ → ℝ := fun j => (2 : ℝ) ^ j * (C j * A * μ.real Set.univ)
  refine ⟨B, fun j => by
    have hCj := hC j
    dsimp [B, A]
    positivity, ?_⟩
  intro F h₀ h₁ hc M hM hbound
  have hg := cauchy_boundary_coefficient_measurable R F hc
  have hgb := cauchy_boundary_coefficient_norm_le R hR F M hbound
  obtain ⟨hs, hjets⟩ := hInt (cauchyBoundaryCoefficient R F) hg (A * M) (by dsimp [A]; positivity) hgb
  let H : Vec 2 → ℂ := fun x =>
    ∫ p, cauchyBoundaryCoefficient R F p • localizedCauchyKernel R χ (p, x) ∂μ
  have he : (fun x : Vec 2 => F (x 0 : ℂ) (x 1 : ℂ)) =ᶠ[𝓝 0] H := by
    filter_upwards [heχ] with x hx
    have hh := localized_double_cauchy_representation R hR χ hχ hb hz hout
      F h₀ h₁ hc M hM hbound x
    rw [hx] at hh
    exact hh
  refine ⟨hs.contDiffAt.congr_of_eventuallyEq he, ?_⟩
  intro j hj
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (hjets j hj 0).trans_eq
  dsimp [B]
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Metric Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Two coordinate discs centered at a real base stay inside the native label strip. -/

def complexBaseShift (Y : Vec 2) (w z : ℂ) : Fin 2 → ℂ :=
  fun a => (Y a : ℂ) + if a = 0 then w else z

theorem complex_base_shift_real (Y X : Vec 2) :
    complexBaseShift Y (X 0 : ℂ) (X 1 : ℂ) = fun a => ((Y + X) a : ℂ) := by
  funext a
  fin_cases a <;> norm_num [complexBaseShift, Pi.add_apply, Complex.ofReal_add]

theorem complex_base_shift_im_sum_le (Y : Vec 2) (R : ℝ) (w z : ℂ)
    (hw : w ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) :
    (∑ a, |(complexBaseShift Y w z a).im|) ≤ 2 * R := by
  have hw' : |w.im| ≤ R := (abs_im_le_norm w).trans (by
    simpa only [mem_closedBall, dist_zero_right] using hw)
  have hz' : |z.im| ≤ R := (abs_im_le_norm z).trans (by
    simpa only [mem_closedBall, dist_zero_right] using hz)
  simp only [Fin.sum_univ_two, complexBaseShift,
    show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false, Complex.add_im,
    Complex.ofReal_im, zero_add]
  linarith only [hw', hz']

theorem base_strip_coordinate_slices
    (F : (Fin 2 → ℂ) → ℂ) (S R : ℝ) (hR : 0 < R) (hRS : 2 * R < S)
    (hF : DifferentiableOn ℂ F {Z | (∑ a, |(Z a).im|) < S}) (Y : Vec 2) :
    (∀ z ∈ closedBall 0 R,
      DiffContOnCl ℂ (fun w => F (complexBaseShift Y w z)) (ball 0 R)) ∧
    (∀ w ∈ closedBall 0 R,
      DiffContOnCl ℂ (fun z => F (complexBaseShift Y w z)) (ball 0 R)) ∧
    Continuous (fun p : ℝ × ℝ => F (complexBaseShift Y (circleMap 0 R p.1)
      (circleMap 0 R p.2))) := by
  have hmaps (w z : ℂ) (hw : w ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) :
      complexBaseShift Y w z ∈ {Z | (∑ a, |(Z a).im|) < S} :=
    (complex_base_shift_im_sum_le Y R w z hw hz).trans_lt hRS
  have hwDiff (z : ℂ) : Differentiable ℂ (fun w => complexBaseShift Y w z) := by
    apply differentiable_pi.mpr
    intro a
    by_cases ha : a = 0
    · simp only [complexBaseShift, ite_eq_left ha]
      fun_prop
    · simp only [complexBaseShift, ite_eq_right ha]
      fun_prop
  have hzDiff (w : ℂ) : Differentiable ℂ (fun z => complexBaseShift Y w z) := by
    apply differentiable_pi.mpr
    intro a
    by_cases ha : a = 0
    · simp only [complexBaseShift, ite_eq_left ha]
      fun_prop
    · simp only [complexBaseShift, ite_eq_right ha]
      fun_prop
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact DiffContOnCl.mk_ball
      (hF.comp (hwDiff z).differentiableOn (fun w hw => hmaps w z (ball_subset_closedBall hw) hz))
      (hF.continuousOn.comp (hwDiff z).continuous.continuousOn (fun w hw => hmaps w z hw hz))
  · intro w hw
    exact DiffContOnCl.mk_ball
      (hF.comp (hzDiff w).differentiableOn (fun z hz => hmaps w z hw (ball_subset_closedBall hz)))
      (hF.continuousOn.comp (hzDiff w).continuous.continuousOn (fun z hz => hmaps w z hw hz))
  · have hc : Continuous (fun p : ℝ × ℝ =>
        complexBaseShift Y (circleMap 0 R p.1) (circleMap 0 R p.2)) := by
      apply continuous_pi
      intro a
      by_cases ha : a = 0
      · simp only [complexBaseShift, ite_eq_left ha]
        exact continuous_const.add ((continuous_circleMap 0 R).comp continuous_fst)
      · simp only [complexBaseShift, ite_eq_right ha]
        exact continuous_const.add ((continuous_circleMap 0 R).comp continuous_snd)
    apply continuousOn_univ.mp
    exact hF.continuousOn.comp hc.continuousOn (fun p _ => hmaps _ _
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl]))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.Buffer

/-! Hilbert representation of the order-zero drift, diffusion and forcing integrand. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem window_physical_rhs_integral {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (ν : ℝ) (w : ℝ → TorusHk 1 E) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (F : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => E))) (z : TorusHk 1 E) :
    (∫ x in unitCube,
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (z.toFunction.jet (valueIndex2 1) x)) -
      ν * (∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (z.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) -
      ∑ k : Fin 2, inner ℝ (F.toFunction.jet (valueIndex2 0) x k)
        (z.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =
    inner ℝ (windowDriftSource hab v hv V hV hb w t) (torusHkValueCLM z) -
      inner ℝ (torusHkValueCLM (ν • torusGradientTensor (w t) + F))
        (torusH1GradientL2CLM (E := E) z) := by
  let S := windowDriftSource hab v hv V hV hb w t
  let H := torusHkValueCLM (ν • torusGradientTensor (w t) + F)
  let J := torusHkValueCLM z
  let G := torusH1GradientL2CLM (E := E) z
  have he : (fun x =>
      -(∑ k : Fin 2, v t x k * inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (z.toFunction.jet (valueIndex2 1) x)) -
      ν * (∑ k : Fin 2, inner ℝ
        ((w t).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        (z.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) -
      ∑ k : Fin 2, inner ℝ (F.toFunction.jet (valueIndex2 0) x k)
        (z.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict unitCube]
      (fun x => inner ℝ (S x) (J x) - inner ℝ (H x) (G x)) := by
    have hh : H = ν • torusH1GradientL2CLM (E := E) (w t) + torusHkValueCLM F := by
      dsimp only [H]
      rw [map_add, map_smul, gradientTensor_value_eq_test_gradient]
    rw [hh]
    filter_upwards [windowDriftSource_raw_ae hab v hv V hV hb w t ht,
      torusRawValue_ae z, torusRawValue_ae F, torusRawTestGradient_ae (w t),
      torusRawTestGradient_ae z,
      Lp.coeFn_add (ν • torusH1GradientL2CLM (E := E) (w t)) (torusHkValueCLM F),
      Lp.coeFn_smul ν (torusH1GradientL2CLM (E := E) (w t))] with x hs hz hf hw hg ha hm
    change _ = inner ℝ (S x) (torusHkValueCLM z x) - inner ℝ _ (torusH1GradientL2CLM (E := E) z x)
    rw [ha]
    simp only [Pi.add_apply]
    rw [hm]
    simp only [Pi.smul_apply]
    rw [← hw, ← hg, ← hf, ← hz]
    change _ = inner ℝ (windowDriftSource hab v hv V hV hb w t x) _ - _
    rw [hs]
    simp only [inner_neg_left, sum_inner, real_inner_smul_left, inner_add_left]
    exact sub_sub _ _ _
  rw [integral_congr_ae he, integral_sub (L2.integrable_inner (𝕜 := ℝ) S J)
    (L2.integrable_inner (𝕜 := ℝ) H G)]
  rfl

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Metric MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! The bounded slow Cauchy formula and fast profiles control actual spatial diagonal jets. -/

theorem base_fast_diagonal_exists_jet_bounds
    (S T : ℝ) (hS : 0 < S) (hST : S ≤ T) (lam : ℝ)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (n : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ F : (Fin 2 → ℂ) → Vec 2 → ℂ,
        (∀ z, DifferentiableOn ℂ (fun Z => F Z z) {Z | (∑ a, |(Z a).im|) < T}) →
        (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
          ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => F Z (z + lam • X))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z, ‖F Z z‖ ≤ M) →
          (∀ Z : Fin 2 → ℂ, (∑ a, |(Z a).im|) < S → ∀ z : Vec 2,
            ∀ j ≤ n, ∀ X, ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F Z (z + lam • X)) X‖ ≤ A j * M) →
          ∀ Y z : Vec 2,
            ContDiffAt ℝ (n : ℕ∞) (fun X : Vec 2 =>
              F (fun a => ((Y + X) a : ℂ)) (z + lam • X)) 0 ∧
            ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
              F (fun a => ((Y + X) a : ℂ)) (z + lam • X)) 0‖ ≤ B j * M := by
  let R := S / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hRS : 2 * R < S := by dsimp [R]; linarith only [hS]
  obtain ⟨χ, hχ, heχ, hbχ, hout⟩ := exists_smooth_bounded_local_identity
    (E := Vec 2) (R / 2) (by positivity)
  have hzχ : χ 0 = 0 := heχ.eq_of_nhds
  let μ := cauchyAngleMeasure.prod cauchyAngleMeasure
  let a₀ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2
  have ha₀ : 0 ≤ a₀ := by dsimp [a₀]; positivity
  obtain ⟨Q, hQ, hInt⟩ := localized_variable_cauchy_regular_and_jet_bound R hR χ hχ hbχ hzχ hout
    μ n (fun j => a₀ * A j) (fun j => mul_nonneg ha₀ (hA j))
  let B : ℕ → ℝ := fun j => (2 : ℝ) ^ j * (Q j * μ.real Set.univ)
  refine ⟨B, fun j => by have hh := hQ j; dsimp [B]; positivity, ?_⟩
  intro F hhol hfast M hM hvalue hjet Y z
  let D : ℝ × ℝ → Fin 2 → ℂ := fun p => complexBaseShift Y (circleMap 0 R p.1) (circleMap 0 R p.2)
  have hD (p : ℝ × ℝ) : (∑ a, |(D p a).im|) < S :=
    (complex_base_shift_im_sum_le Y R _ _
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])
      (by simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hR, le_refl])).trans_lt hRS
  let pref : ℝ × ℝ → ℂ := cauchyBoundaryCoefficient R (fun _ _ => 1)
  have hpref : Measurable pref := cauchy_boundary_coefficient_measurable R _ continuous_const
  have hpb (p : ℝ × ℝ) : ‖pref p‖ ≤ a₀ := by
    simpa only [mul_one] using cauchy_boundary_coefficient_norm_le R hR (fun _ _ => 1) 1
      (fun _ _ => by simp only [norm_one, le_refl]) p
  let f : (ℝ × ℝ) → Vec 2 → ℂ := fun p X => pref p * F (D p) (z + lam • X)
  have hm (X : Vec 2) : Measurable (fun p => f p X) := by
    have hc := (base_strip_coordinate_slices (fun Z => F Z (z + lam • X)) T R hR
      (hRS.trans_le hST) (hhol _) Y).2.2
    exact hpref.mul hc.measurable
  have hs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (f p) :=
    (hfast (D p) (hD p) z).const_smul (pref p)
  have hf : ∀ l ≤ n, ∀ p X, ‖iteratedFDeriv ℝ l (f p) X‖ ≤ (a₀ * A l) * M := by
    intro l hl p X
    change ‖iteratedFDeriv ℝ l (fun X => pref p • F (D p) (z + lam • X)) X‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hfast (D p) (hD p) z).contDiffAt.of_le
      (by exact_mod_cast hl)), norm_smul]
    exact (mul_le_mul (hpb p) (hjet (D p) (hD p) z l hl X) (norm_nonneg _) ha₀).trans_eq
      (by ring)
  obtain ⟨hreg, hjets⟩ := hInt f hm hs M hM hf
  let H : Vec 2 → ℂ := fun X => ∫ p, f p X * localizedCauchyKernel R χ (p, X) ∂μ
  have he : (fun X : Vec 2 => F (fun a => ((Y + X) a : ℂ)) (z + lam • X)) =ᶠ[𝓝 0] H := by
    filter_upwards [heχ] with X hX
    obtain ⟨h₀, h₁, hc⟩ := base_strip_coordinate_slices (fun Z => F Z (z + lam • X)) T R hR
      (hRS.trans_le hST) (hhol _) Y
    have hh := localized_double_cauchy_representation R hR χ hχ hbχ hzχ hout
      (fun w v => F (complexBaseShift Y w v) (z + lam • X)) h₀ h₁ hc M hM
      (fun θ φ => hvalue (D (θ, φ)) (hD (θ, φ)) _) X
    rw [hX, complex_base_shift_real] at hh
    simpa only [H, D, pref, f, cauchyBoundaryCoefficient, mul_one, smul_eq_mul, id_eq] using hh
  refine ⟨hreg.contDiffAt.congr_of_eventuallyEq he, ?_⟩
  intro j hj
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (hjets j hj 0).trans_eq
  dsimp [B]
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Choose the radius cap before the stream, order, datum, and carrier parameters. -/

theorem exists_molecular_uniform_constants :
    ∃ cmax : ℝ, 0 < cmax ∧ ∀ c : ℝ, 0 < c → c ≤ cmax →
      c ≤ 1 ∧ 1048576 * c ^ 2 ≤ 1 ∧
      ∀ e ν a : ℝ, 0 < e → 0 < ν → 0 < a →
        let ρ := c * min e (Real.sqrt (ν / a))
        0 < ρ ∧ ρ ≤ c * e ∧
          1024 * ρ / e ≤ 1 / 2 ∧
          (actualDriftJetConstant * a) * 1024 * ρ ^ 2 ≤ ν / 8 ∧
          (1048576 * a) * (ρ ^ 2 / ν) ≤ 1 := by
  obtain ⟨cD, hcD, hD⟩ := exists_drift_radius_constant actualDriftJetConstant 1024
    actualDriftJetConstant_nonneg (by norm_num)
  refine ⟨min cD (1 / 2048), lt_min hcD (by norm_num), ?_⟩
  intro c hc hcap
  have hcD' := hcap.trans (min_le_left _ _)
  have hcS : c ≤ 1 / 2048 := hcap.trans (min_le_right _ _)
  have hc1 : c ≤ 1 := hcS.trans (by norm_num)
  have hcSq : 1048576 * c ^ 2 ≤ 1 := by
    have hs := pow_le_pow_left₀ hc.le hcS 2
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1048576)
    norm_num at hm
    exact hm.trans (by norm_num)
  refine ⟨hc1, hcSq, ?_⟩
  intro e ν a he hν ha
  have hr := molecular_radius_bounds hc he hν ha
  have hd := molecular_radius_drift_smallness hc he hν ha actualDriftJetConstant_nonneg
    (by norm_num) (hD c hc hcD').1 (hD c hc hcD').2
  refine ⟨hr.1, hr.2.1, hd.1, hd.2, ?_⟩
  have hdel : 0 ≤ (c * min e (Real.sqrt (ν / a))) ^ 2 / ν :=
    div_nonneg (sq_nonneg _) hν.le
  have hf := molecular_time_window_smallness (s := 0)
    (t := (c * min e (Real.sqrt (ν / a))) ^ 2 / ν) hc he hν ha
    (by norm_num : (0 : ℝ) ≤ 1048576) hcSq
    (by rw [sub_zero, abs_of_nonneg hdel])
  simpa only [sub_zero, abs_of_nonneg hdel] using hf

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! Uniform scalar budgets discharge the quantitative inputs of the actual preparation buffer. -/

structure PreparationScalarBudget (eParent e ν a ρ r CQ CI Q τ : ℝ) : Prop where
  parent_pos : 0 < eParent
  diffusivity_pos : 0 < ν
  radius_pos : 0 < ρ
  radius_le_parent : ρ ≤ eParent
  enhanced_pos : 0 < r
  error_small : CQ * eParent ^ Q ≤ 1 / 8
  kernel_small : CI * eParent ^ τ ≤ 1 / 8
  radius_small : ρ ≤ (1 / (32 * Real.sqrt 2)) /
    (2 * Real.pi * (8 * Real.sqrt 18 * (|CQ| + 1) + 1))
  radius_ratio_small : ρ / r ≤ (1 / (32 * Real.sqrt 2)) /
    (2 * Real.pi * (8 * Real.sqrt 18 * (|CQ| + 1) + 1))
  drift_small : 1024 * ρ / e ≤ 1 / 2
  strain_small : (actualDriftJetConstant * a) * 1024 * ρ ^ 2 ≤ ν / 8
  flow_small : (1048576 * a) * (ρ ^ 2 / ν) ≤ 1

theorem preparation_scalar_budgets {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ cmax : ℝ, 0 < cmax ∧
      ∀ c cr Q τ CI CQ : ℝ, 0 < c → c ≤ cmax → 0 < cr → 0 < Q → 0 < τ →
      ∀ j₀ : ℕ, ∃ mStar : ℕ, 2 ≤ mStar ∧ j₀ ≤ mStar ∧
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, mStar ≤ m → m ≤ M →
        PreparationScalarBudget (ocEpsilon q Λ (m - 1)) (ocEpsilon q Λ m)
          (κ m) (ocA α q Λ m)
          (c * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m)))
          (cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) CQ CI Q τ := by
  obtain ⟨Lr, hLr, hdecay⟩ := band_preparation_radius_decay hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lp, _hLp, hpositive⟩ := band_preparation_positivity hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Lr Lp, hLr.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hcap⟩ := exists_molecular_uniform_constants
  refine ⟨cmax, hcmax, ?_⟩
  intro c cr Q τ CI CQ hc hcc hcr hQ hτ j₀
  have hΛr : Lr ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛp : Lp ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLr.trans hΛr
  let η := (1 / (32 * Real.sqrt 2)) /
    (2 * Real.pi * (8 * Real.sqrt 18 * (|CQ| + 1) + 1))
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨nr, hnr, hsmallr⟩ := hdecay Λ hΛr c cr hc hcr η hη
  obtain ⟨ne, _hne, hsmalle⟩ := preparation_parameters_eventually_small hq.1 h128 hQ hτ CQ CI
  refine ⟨max j₀ (max nr ne), hnr.trans ((le_max_left _ _).trans (le_max_right _ _)),
    le_max_left _ _, ?_⟩
  intro M κ hκ m hm hmM
  have hmr : nr ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hme : ne ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hm2 : 2 ≤ m := hnr.trans hmr
  have hp := hpositive Λ hΛp M κ hκ m hm2 hmM cr hcr
  have he := (Scales.epsilon_basic (m := m) hq.1 h128).1
  have hparent := (Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hcdata := hcap c hc hcc
  have hd := hcdata.2.2 (ocEpsilon q Λ m) (κ m) (ocA α q Λ m) he hp.1 ha
  have hr := hsmallr M κ hκ m hmr hmM
  have heps : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := by
    have hs := CycleReference.epsilon_succ_le (n := m - 1) hq.1 h128
    simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega)] using hs
  have hρparent := (hd.2.1.trans
    ((mul_le_mul_of_nonneg_right hcdata.1 he.le).trans_eq (one_mul _))).trans heps
  exact ⟨hparent, hp.1, hd.1, hρparent,
    hp.2.2, (hsmalle m hme).1, (hsmalle m hme).2, hr.2, hr.1,
    hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! Extract an actual native complex bound from the incoming stage's certified witnesses. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem contextCertified_exists_native_complex_bound
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} (hG : G.IsContextCertified k)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) :
    ∃ (θ : ℝ) (f : GenSort.Sem .ctx)
      (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
      0 ≤ θ ∧ IsHolExtension D bw j₀ G.level p.1 f (F p) ∧
      ctxSize D bw j₀ G.level F (compReserve k v.1) k.Lstar ≤ ENNReal.ofReal θ ∧
      (∀ (ctx : StageCtx D bw j₀ G.level p) (t : ℝ),
        t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ (X z : Vec 2),
        G.fam.flux p ctx v u γ d I t X z c =
          if IsAdmissibleChain D bw j₀ G.level p.1
              (ctx.1.recenter D (D.eps (G.level - 1) • X))
          then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0) ∧
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1, ∀ (z : Vec 2) (Z : Fin 2 → ℂ),
        (∑ a, |(Z a).im|) < (1 + compReserve k v.1 / 4) * (1 / 100) * D.eps (G.level - 1) →
        ‖F p ⟨G.level - 1, [p.1]⟩ 0 t
          (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))‖ ≤ θ := by
  obtain ⟨θ, hθ, _, hforms⟩ := hG v u γ
  obtain ⟨f, F, hslots, hsize⟩ := hforms d I c
  obtain ⟨_, hF, he⟩ := hslots p
  refine ⟨θ d I c, f p, F, hθ d I c, hF, hsize, he, ?_⟩
  intro t ht z Z hZ
  have ha (Y : Vec 2) : IsAdmissibleChain D bw j₀ G.level p.1
      ⟨G.level - 1, [p.1], Y, []⟩ :=
    nativeChain_isCarrier D bw j₀ G.level p.1 2 hi hj p.2 Y
  apply native_complex_context_norm_le D bw hb j₀ G.level p hε (f p) F hF ha t ht
    (compReserve k v.1) hm hm2 k.Lstar (θ d I c) (hθ d I c) hsize
    (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _) _ Z hZ
  intro Y
  have hp := native_context_sem_periodic G hi hj p v u γ d I c t (f p)
    (fun ctx X w => he ctx t ht X w) Y
  have hpz : IsZ2Periodic (fun w => f p t ⟨G.level - 1, [p.1], Y, []⟩ (z + w)) := by
    intro n w
    change f p t ⟨G.level - 1, [p.1], Y, []⟩ (z + (w + latticeShift n)) = _
    rw [← add_assoc]
    exact hp n (z + w)
  have hper := CycleComparison.Lift.coordinate_line_periodic _ hpz (transverseIndex p.1)
  have heq (s : ℝ) : F p ⟨G.level - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a),
        (fun a => (z a : ℂ)) + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) =
      (f p t ⟨G.level - 1, [p.1], Y, []⟩ (z + s • basisVec (transverseIndex p.1)) : ℂ) := by
    have hh := hF.2.2 ⟨G.level - 1, [p.1], Y, []⟩ t ht
      (z + s • basisVec (transverseIndex p.1)) (ha Y)
    change F p ⟨G.level - 1, [p.1]⟩ 0 t
      ((⟨G.level - 1, [p.1], Y, []⟩ : RealChain).paramsC
        (z + s • basisVec (transverseIndex p.1))) = _ at hh
    rw [native_paramsC_phase_line] at hh
    exact hh
  intro s
  dsimp only
  rw [heq, heq]
  exact congrArg (fun x : ℝ => (x : ℂ)) (hper s)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! The certified native complex slice is the literal incoming scalar flux. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def nativeStageContext (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (Y : Vec 2) : StageCtx D bw j₀ G.level p :=
  ⟨⟨G.level - 1, [p.1], Y, []⟩,
    nativeChain_isCarrier D bw j₀ G.level p.1 2 hi hj p.2 Y⟩

theorem native_flux_holomorphic_realization
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (f : GenSort.Sem .ctx)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D bw j₀ G.level p.1 f F)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (Y z : Vec 2) :
    F ⟨G.level - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ))) =
        (G.fam.flux p (nativeStageContext G hi hj p Y) v u γ d I t 0 z c : ℂ) := by
  let ctx := nativeStageContext G hi hj p Y
  have hrec : ctx.1.recenter D (D.eps (G.level - 1) • (0 : Vec 2)) = ctx.1 := by
    simp only [ctx, nativeStageContext, RealChain.recenter, smul_zero, add_zero]
    rfl
  have heq := he ctx 0 z
  rw [hrec, ite_eq_left ctx.2] at heq
  have hh := hF.2.2 ctx.1 t ht z ctx.2
  have hparams : ctx.1.paramsC z =
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext a
        exact Fin.elim0 a
      · rfl
  change F ⟨G.level - 1, [p.1]⟩ 0 t (ctx.1.paramsC z) = _ at hh
  rw [hparams, ← heq] at hh
  exact hh
end

/-! Recenter the actual native slot into its dimensional base label. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem actual_native_flux_eq
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (ha : (G.actual p).1 = nativeChain G.level p.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (t : ℝ) (f : GenSort.Sem .ctx)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (X z : Vec 2) :
    G.fam.flux p (G.actual p) v u γ d I t X z c =
      G.fam.flux p (nativeStageContext G hi hj p (D.eps (G.level - 1) • X))
        v u γ d I t 0 z c := by
  rw [he, he, ha]
  simp only [nativeChain, nativeStageContext, RealChain.recenter, List.getLast?_nil,
    zero_add, smul_zero, add_zero]

theorem actual_native_dimFlux_eq
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (ha : (G.actual p).1 = nativeChain G.level p.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (t : ℝ) (f : GenSort.Sem .ctx)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (hε : D.eps (G.level - 1) ≠ 0) (ν e : ℝ) (Y z : Vec 2) :
    G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t Y z c =
      (ν * e ^ (d - 2)) *
        G.fam.flux p (nativeStageContext G hi hj p Y) v u γ d I t 0 z c := by
  change (ν * e ^ (d - 2)) *
    G.fam.flux p (G.actual p) v u γ d I t ((D.eps (G.level - 1))⁻¹ • Y) z c = _
  rw [actual_native_flux_eq G hi hj p ha v u γ d I c t f he,
    smul_smul, mul_inv_cancel₀ hε, one_smul]
end

/-! Structural transverse flux invariance continues to complex native base labels. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_complex_parallel_invariance
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (hpar : G.IsSlotTransverse)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (f : GenSort.Sem .ctx)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D bw j₀ G.level p.1 f F)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (Z : Fin 2 → ℂ)
    (hZ : (∑ a, |(Z a).im|) < (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1))
    (z : Vec 2) (s : ℝ) :
    F ⟨G.level - 1, [p.1]⟩ 0 t
      (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => ((z + s • basisVec (slotParallel p.1)) a : ℂ))) =
    F ⟨G.level - 1, [p.1]⟩ 0 t
      (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ))) := by
  let R := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1)
  have hR : 0 < R := by dsimp [R]; positivity
  apply holomorphic_two_label_eqOn_of_real_eq R hR
    (native_holomorphic_base_slice D bw hb j₀ G.level p.1 f F hF t ht _
      (fun _ => Complex.ofReal_im _))
    (native_holomorphic_base_slice D bw hb j₀ G.level p.1 f F hF t ht _
      (fun _ => Complex.ofReal_im _)) _ hZ
  intro Y
  rw [native_flux_holomorphic_realization G hi hj p v u γ d I c f F hF t ht he,
    native_flux_holomorphic_realization G hi hj p v u γ d I c f F hF t ht he]
  exact congrArg (fun w : Vec 2 => (w c : ℂ))
    (hpar p (nativeStageContext G hi hj p Y) v u γ d I t ht 0 z s)
end

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! Real native transverse profiles are periodic for the original certified flux. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_real_phase_periodic
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (f : GenSort.Sem .ctx)
    (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D bw j₀ G.level p.1 f F)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (Y z : Vec 2) :
    Function.Periodic (fun s : ℝ => F ⟨G.level - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a),
        (fun a => (z a : ℂ)) + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) 1 := by
  let ctx := nativeStageContext G hi hj p Y
  have hpz : IsZ2Periodic (fun w : Vec 2 =>
      (G.fam.flux p ctx v u γ d I t 0 (z + w) c : ℂ)) := by
    intro m w
    dsimp only
    rw [← add_assoc]
    exact congrArg (fun a : Vec 2 => (a c : ℂ))
      (G.fam.flux_periodic p ctx v u γ d I t 0 m (z + w))
  have hp := CycleComparison.Lift.coordinate_line_periodic _ hpz (transverseIndex p.1)
  have heq (s : ℝ) : F ⟨G.level - 1, [p.1]⟩ 0 t
      ((fun a => (Y a : ℂ)), (fun a : Fin 0 => Fin.elim0 a),
        (fun a => (z a : ℂ)) + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0) =
      (G.fam.flux p ctx v u γ d I t 0 (z + s • basisVec (transverseIndex p.1)) c : ℂ) := by
    rw [← complex_real_phase_shift]
    exact native_flux_holomorphic_realization G hi hj p v u γ d I c f F hF t ht he Y _
  intro s
  dsimp only
  rw [heq, heq]
  exact hp s

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVenhance.Infra.Flow
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual natural Piola Jacobians have uniform jets on every compact time window. -/

open CycleJointProofs CycleReference

theorem naturalPreparationJacobian_spatial_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
    naturalPreparationJacobian hφ s t (x + latticeShift k) =
      naturalPreparationJacobian hφ s t x := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hp : ∀ r, IsZ2Periodic (streamVel φ r) := by
    intro r l y
    simpa using hb.periodic 0 l r y
  have hflow := flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz
  have he : streamFlow φ hφ s (x + latticeShift k) t =
      streamFlow φ hφ s x t + latticeShift k :=
    flow_lattice_equivariant _ hφ.vel_lipschitz hp hflow x t s k
  change jacMatrix (fun y => streamFlow φ hφ t y s)
    (streamFlow φ hφ s (x + latticeShift k) t) = _
  rw [he]
  exact streamFlow_jacMatrix_spatial_periodic hφ t s _ k

theorem naturalPreparationJacobian_compact_time_jet_bound {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T)
    (a b : Fin 2) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => naturalPreparationJacobian hφ s t y a b) x‖ ≤ C := by
  exact periodic_compact_time_spatial_jet_bound
    (fun tx => naturalPreparationJacobian hφ s tx.1 tx.2 a b)
    (naturalPreparationJacobian_entry_smooth hφ s a b)
    (fun t x k => congrArg (fun A => A a b)
      (naturalPreparationJacobian_spatial_periodic hφ s t x k)) T hT j

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual complex-base boundary fluxes have uniform affine fast spatial jets. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_complex_fast_affine_regular_and_jets
    (G : GenStage D hr Dm bw j₀) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1)) (hpar : G.IsSlotTransverse)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (f : GenSort.Sem .ctx)
    (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ)
    (hF : IsHolExtension D bw j₀ G.level p.1 f (F p))
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (he : ∀ (ctx : StageCtx D bw j₀ G.level p) (X z : Vec 2),
      G.fam.flux p ctx v u γ d I t X z c =
        if IsAdmissibleChain D bw j₀ G.level p.1
          (ctx.1.recenter D (D.eps (G.level - 1) • X))
        then f t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (mres : ℝ) (hm : 0 ≤ mres) (hm2 : mres ≤ 2) (L : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hsize : ctxSize D bw j₀ G.level F mres L ≤ ENNReal.ofReal θ)
    (Z : Fin 2 → ℂ)
    (hZ : (∑ a, |(Z a).im|) < (1 + mres / 4) * (1 / 100) * D.eps (G.level - 1))
    (z : Vec 2) (lam : ℝ) (n : ℕ) :
    ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 => F p ⟨G.level - 1, [p.1]⟩ 0 t
      (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => ((z + lam • X) a : ℂ)))) ∧
      ∀ j ≤ n, ∀ X : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 => F p ⟨G.level - 1, [p.1]⟩ 0 t
          (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => ((z + lam • X) a : ℂ)))) X‖ ≤
            (((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) *
              ‖lam • (ContinuousLinearMap.proj (transverseIndex p.1) : Vec 2 →L[ℝ] ℝ)‖ ^ j) * θ := by
  have hZ' : (∑ a, |(Z a).im|) <
      (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1) := by
    apply hZ.trans_le
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  let g : Vec 2 → ℂ := fun w => F p ⟨G.level - 1, [p.1]⟩ 0 t
    (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (w a : ℂ)))
  have hp : ∀ w : Vec 2, ∀ s : ℝ, g (w + s • basisVec (slotParallel p.1)) = g w :=
    fun w s => native_complex_parallel_invariance G hi hj hb hε hpar p v u γ d I c f (F p)
      hF t ht he Z hZ' w s
  have hphase := native_complex_phase_regular_and_jet_bound D bw hb j₀ G.level p hε f F hF
    (fun Y => nativeChain_isCarrier D bw j₀ G.level p.1 2 hi hj p.2 Y) t ht mres hm hm2 L
    θ hθ hsize (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _)
    (fun Y => native_real_phase_periodic G hi hj p v u γ d I c f (F p) hF t ht he Y z) Z hZ n
  have heprof : (fun s : ℝ => g (z + s • basisVec (slotParallel p.1).rev)) =
      (fun s : ℝ => F p ⟨G.level - 1, [p.1]⟩ 0 t
        (Z, (fun a : Fin 0 => Fin.elim0 a),
          (fun a => (z a : ℂ)) + fun a => if a = transverseIndex p.1 then (s : ℂ) else 0)) := by
    funext s
    dsimp only [g]
    rw [complex_real_phase_shift, ← transverseIndex_eq_slotParallel_rev]
  rw [← heprof] at hphase
  have hh := fast_affine_profile_regular_and_jet_bound (slotParallel p.1) g hp z lam n
    hphase.1 (fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) * θ)
    hphase.2
  simpa only [← transverseIndex_eq_slotParallel_rev, mul_assoc, mul_comm θ] using hh

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! A single finite constant bounds all retained natural Jacobian entries and orders. -/

open CycleJointProofs

theorem naturalPreparationJacobian_compact_scaled_jets {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T)
    (E : ℝ) (hE : 0 ≤ E) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ T, ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => naturalPreparationJacobian hφ s t y a b) x‖ ≤ C := by
  have hex (a b : Fin 2) (j : Fin (N + 1)) :=
    naturalPreparationJacobian_compact_time_jet_bound hφ s T hT a b j.1
  choose B hB hb using hex
  let C := ∑ a : Fin 2, ∑ b : Fin 2, ∑ j : Fin (N + 1), E ^ j.1 * B a b j
  have hterm (a b : Fin 2) (j : Fin (N + 1)) : 0 ≤ E ^ j.1 * B a b j :=
    mul_nonneg (pow_nonneg hE _) (hB a b j)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
    (fun b _ => Finset.sum_nonneg (fun j _ => hterm a b j)))
  refine ⟨1 + C, le_add_of_nonneg_right hC, ?_⟩
  intro t ht a b j hj x
  let q : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hh : E ^ j * B a b q ≤ C :=
    (Finset.single_le_sum (fun q _ => hterm a b q) (Finset.mem_univ q)).trans
      ((Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun q _ => hterm a b q))
        (Finset.mem_univ b)).trans
        (Finset.single_le_sum (fun a _ => Finset.sum_nonneg
          (fun b _ => Finset.sum_nonneg (fun q _ => hterm a b q))) (Finset.mem_univ a)))
  exact (mul_le_mul_of_nonneg_left (hb a b q t ht x) (pow_nonneg hE _)).trans
    (hh.trans (le_add_of_nonneg_left zero_le_one))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Original context certificates bound the actual slow/fast diagonal spatial coefficient jets. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem contextCertified_native_flux_diagonal_bounds
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} (hG : G.IsContextCertified k)
    (hpar : G.IsSlotTransverse) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2) (lam : ℝ) (n : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1, ∀ j ≤ n, ∀ Y : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (lam • X) c) Y‖ ≤ C j := by
  obtain ⟨θ, f, F, hθ, hHol, hsize, hsem, hbound⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  let S := (1 + compReserve k v.1 / 4) * (1 / 100) * D.eps (G.level - 1)
  let T := (1 + (2 : ℝ) / 4) * (1 / 100) * D.eps (G.level - 1)
  have hS : 0 < S := by dsimp [S]; positivity
  have hST : S ≤ T := by
    dsimp [S, T]
    apply mul_le_mul_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith only [hm2]
  let A : ℕ → ℝ := fun j => ((j.factorial : ℝ) * (2 * Real.pi / (3 * Real.pi * bw)) ^ j) *
    ‖lam • (ContinuousLinearMap.proj (transverseIndex p.1) : Vec 2 →L[ℝ] ℝ)‖ ^ j
  have hA (j : ℕ) : 0 ≤ A j := by dsimp [A]; positivity
  obtain ⟨B, hB, hdiag⟩ := base_fast_diagonal_exists_jet_bounds S T hS hST lam A hA n
  refine ⟨fun j => B j * θ, fun j => mul_nonneg (hB j) hθ, ?_⟩
  intro t ht j hjn Y
  let Fb : (Fin 2 → ℂ) → Vec 2 → ℂ := fun Z z => F p ⟨G.level - 1, [p.1]⟩ 0 t
    (Z, (fun a : Fin 0 => Fin.elim0 a), (fun a => (z a : ℂ)))
  have hd (z : Vec 2) : DifferentiableOn ℂ (fun Z => Fb Z z)
      {Z | (∑ a, |(Z a).im|) < T} :=
    native_holomorphic_base_slice D bw hb j₀ G.level p.1 f (F p) hHol t ht
      (fun a => (z a : ℂ)) (fun _ => Complex.ofReal_im _)
  have hfast (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < S) (z : Vec 2) :=
    native_complex_fast_affine_regular_and_jets G hi hj hb hε hpar p v u γ d I c f F hHol
      t ht (fun ctx X z => hsem ctx t ht X z) (compReserve k v.1) hm hm2 k.Lstar θ hθ hsize
      Z hZ z lam n
  obtain ⟨hreg, hnorm⟩ := hdiag Fb hd (fun Z hZ z => (hfast Z hZ z).1) θ hθ
    (fun Z hZ z => hbound t ht z Z hZ)
    (fun Z hZ z => (hfast Z hZ z).2) Y (lam • Y)
  let sf : Vec 2 → ℝ := fun X =>
    G.fam.flux p (nativeStageContext G hi hj p X) v u γ d I t 0 (lam • X) c
  let H : Vec 2 → ℂ := fun X => Fb (fun a => ((Y + X) a : ℂ)) (lam • Y + lam • X)
  have he : (fun X : Vec 2 => sf (Y + X)) = Complex.reCLM ∘ H := by
    funext X
    have hh := native_flux_holomorphic_realization G hi hj p v u γ d I c f (F p) hHol t ht
      (fun ctx X z => hsem ctx t ht X z) (Y + X) (lam • Y + lam • X)
    have hh' : H X = (sf (Y + X) : ℂ) := by
      simpa only [sf, Fb, H, smul_add] using hh
    exact (congrArg Complex.re hh').symm
  have hn : ‖iteratedFDeriv ℝ j (Complex.reCLM ∘ H) 0‖ ≤
      ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ j H 0‖ :=
    Complex.reCLM.norm_iteratedFDeriv_comp_left hreg (by exact_mod_cast hjn)
  rw [← he, Complex.reCLM_norm, one_mul,
    iteratedFDeriv_comp_add_left (f := sf) j Y 0, add_zero] at hn
  exact hn.trans (hnorm j hjn)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.KernelEnergy.TorusKernelOperator
namespace AVRegularity.Construction.Preservation.Buffer

/-! Read the literal order-zero weak equation as a value source and complete physical flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem orderZero_physical_weak_identity {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (ν : ℝ) (f : ∀ i, TorusHk 0 (h i))
    (F : ∀ i, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    (w : ∀ i, ℝ → TorusHk 1 (h i)) (u : ∀ i, ℝ → TorusHk 0 (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => 0)
      noLocalCoefficient f F (fun _ _ => 0) u w) (i : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : TorusHk 1 (h i)) :
    inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM z) -
      inner ℝ (torusHkValueCLM (u i a)) (torusHkValueCLM z) =
      ∫ r in a..t, inner ℝ (windowDriftSource hab v hv V hV hb (w i) r)
        (torusHkValueCLM z) -
        inner ℝ (torusHkValueCLM (ν • torusGradientTensor (w i r) + F i r))
          (torusH1GradientL2CLM (E := h i) z) := by
  classical
  have hzflux (r : ℝ) (x : Vec 2) :
      torusRawCouplingFlux (fun _ : ι => 0) 0 r noLocalCoefficient
        (fun j => w j r) i x = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro d _
    exact (noLocalOrders (k := 0) i j d).elim
  have hrhs (r : ℝ) (hr : r ∈ Set.Ioc a t) :
      (∫ x in unitCube, torusRawSpatialRhs (fun _ : ι => 0) 0 ν r v
        noLocalCoefficient F (fun _ _ => 0) (fun j => w j r) i z x) =
      inner ℝ (windowDriftSource hab v hv V hV hb (w i) r) (torusHkValueCLM z) -
        inner ℝ (torusHkValueCLM (ν • torusGradientTensor (w i r) + F i r))
          (torusH1GradientL2CLM (E := h i) z) := by
    rw [← window_physical_rhs_integral hab v hv V hV hb ν (w i) r
      ⟨hr.1.le, hr.2.trans ht.2⟩ (F i r) z]
    apply integral_congr_ae
    have hg := torusRawValue_ae (0 : TorusHk 0 (h i))
    filter_upwards [hg, Lp.coeFn_zero (h i) 2 (volume.restrict unitCube)] with x hx hzero
    simp only [map_zero] at hx
    rw [hzero] at hx
    simp only [torusRawSpatialRhs, hzflux, PiLp.zero_apply, zero_add, hx, Pi.zero_apply, inner_zero_left, add_zero]
  have he := (hsol.2.2.2.2 i t ht z).2.2.2.2
  change (∫ x in unitCube, inner ℝ ((u i t).toFunction.jet (valueIndex2 0) x)
      (z.toFunction.jet (valueIndex2 1) x)) -
    (∫ x in unitCube, inner ℝ ((f i).toFunction.jet (valueIndex2 0) x)
      (z.toFunction.jet (valueIndex2 1) x)) =
    ∫ r in Set.Ioc a t, ∫ x in unitCube,
      torusRawSpatialRhs (fun _ : ι => 0) 0 ν r v noLocalCoefficient F
        (fun _ _ => 0) (fun j => w j r) i z x at he
  rw [(torusRawValue_pairing_integrable_and_integral (u i t) z).2,
    (torusRawValue_pairing_integrable_and_integral (f i) z).2] at he
  rw [hsol.2.2.2.1 i, intervalIntegral.integral_of_le ht.1]
  exact he.trans (setIntegral_congr_fun measurableSet_Ioc hrhs)

end AVRegularity.Construction.Preservation.Buffer
end
end
