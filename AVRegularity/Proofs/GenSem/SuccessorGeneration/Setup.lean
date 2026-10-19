-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.ChildInert.Center
public import AVRegularity.Proofs.GenSem.Strain.Main
public import AVRegularity.Proofs.GenSem.LiftGen.Main
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.Liouville

section
section
/-! Complex-differentiable functions on open subsets of a finite-dimensional complex normed space
are `C^∞` (Mathlib has this only for functions of one complex variable).

The directional derivative of a complex-differentiable `F` is again complex differentiable, by the
one-variable Cauchy formula along the line `ζ ↦ y + ζ v` and differentiation under the circle
integral (the derivative is dominated by the Cauchy estimate). Induction on the order, with
`contDiffOn_clm_apply` in finite dimension, gives `ContDiffOn ℂ ⊤`. -/

@[expose] public noncomputable section

open MeasureTheory Metric Set Complex Filter
open scoped Topology Interval

namespace AVRegularity.Providers.GenSem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A local ball inside the domain on which a continuous function is bounded. -/
theorem exists_ball_bound {F : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, ball y₀ (4 * ρ) ⊆ U ∧ ∀ y ∈ ball y₀ (4 * ρ), ‖F y‖ ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hc : ContinuousAt F y₀ := hF.continuousOn.continuousAt (hU.mem_nhds hy₀)
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  refine ⟨min ε δ / 4, by positivity, ‖F y₀‖ + 1, ?_, ?_⟩
  · intro y hy
    apply hεU
    refine lt_of_lt_of_le (mem_ball.mp hy) ?_
    have := min_le_left ε δ
    linarith
  · intro y hy
    have hyd : dist y y₀ < δ := by
      refine lt_of_lt_of_le (mem_ball.mp hy) ?_
      have := min_le_right ε δ
      linarith
    have h1 := hδF hyd
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (F y) (F y₀)
    linarith

/-- The Cauchy estimate for the derivative of a function complex differentiable on a closed ball. -/
theorem norm_fderiv_le_of_closedBall {F : E → ℂ} {y : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ F (closedBall y ρ)) (hM : ∀ z ∈ closedBall y ρ, ‖F z‖ ≤ M) :
    ‖fderiv ℂ F y‖ ≤ M / ρ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (mem_closedBall_self hρ.le))
  have hdy : DifferentiableAt ℂ F y := hd.differentiableAt (closedBall_mem_nhds y hρ)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun w hw => ?_
  have hmaps : ∀ ζ : ℂ, ζ ∈ closedBall (0 : ℂ) ρ → y + ζ • w ∈ closedBall y ρ := by
    intro ζ hζ
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hw, mul_one]
    simpa using hζ
  have hψ : DifferentiableOn ℂ (fun ζ : ℂ => F (y + ζ • w)) (closedBall (0 : ℂ) ρ) := by
    refine hd.comp ?_ hmaps
    exact (differentiable_const _ |>.add (differentiable_id.smul_const w)).differentiableOn
  have hder : deriv (fun ζ : ℂ => F (y + ζ • w)) 0 = fderiv ℂ F y w := by
    have h1 : HasDerivAt (fun ζ : ℂ => y + ζ • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add y
    have h2 : HasFDerivAt F (fderiv ℂ F y) (y + (0 : ℂ) • w) := by
      simpa using hdy.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := ρ) (C := M) hρ
    ((hψ.mono closure_ball_subset_closedBall).diffContOnCl)
    (fun z hz => hM _ (hmaps z (sphere_subset_closedBall hz)))
  rwa [hder] at this

end AVRegularity.Providers.GenSem
end
end

section
/-! The directional derivative of a complex-differentiable function is complex differentiable, and
complex-differentiable functions on open sets of a finite-dimensional complex normed space are
`C^∞` (`differentiableOn_fderiv_apply`, `contDiffOn_top_of_differentiableOn`). -/

@[expose] public noncomputable section

open MeasureTheory Metric Set Complex Filter
open scoped Topology Interval

namespace AVRegularity.Providers.GenSem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Cauchy kernel `θ ↦ (deriv (circleMap 0 r) θ) • (1 / (circleMap 0 r θ)²) = I / circleMap 0 r θ`. -/
def cauchyKernel (r : ℝ) (θ : ℝ) : ℂ := I * (circleMap 0 r θ)⁻¹

theorem cauchyKernel_eq {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    deriv (circleMap 0 r) θ • (1 / (circleMap 0 r θ - 0) ^ 2) = cauchyKernel r θ := by
  have h0 : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
  rw [deriv_circleMap, cauchyKernel, smul_eq_mul, sub_zero]
  field_simp

theorem cauchyKernel_norm {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖cauchyKernel r θ‖ = 1 / r := by
  simp [cauchyKernel, abs_of_pos hr]

theorem continuous_cauchyKernel {r : ℝ} (hr : 0 < r) : Continuous (cauchyKernel r) :=
  continuous_const.mul ((continuous_circleMap 0 r).inv₀ fun _ => circleMap_ne_center hr.ne')

/-- The directional derivative of a complex-differentiable function is complex differentiable. -/
theorem differentiableOn_fderiv_apply [FiniteDimensional ℂ E] {F : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (v : E) :
    DifferentiableOn ℂ (fun y => fderiv ℂ F y v) U := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  intro y₀ hy₀
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ρ, hρ, M, hball, hM⟩ := exists_ball_bound hU hF hy₀
  set r : ℝ := ρ / (‖v‖ + 1) with hr_def
  have hr : 0 < r := by positivity
  have hrv : r * ‖v‖ ≤ ρ := by
    rw [hr_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v, hρ]
  -- points of the discs stay in the domain
  have hmem : ∀ y ∈ ball y₀ ρ, ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • v ∈ ball y₀ (2 * ρ) := by
    intro y hy ζ hζ
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have h1 : ‖ζ • v‖ ≤ ρ := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hζ (norm_nonneg v)).trans hrv
    calc ‖y + ζ • v - y₀‖ = ‖(y - y₀) + ζ • v‖ := by congr 1; abel
      _ ≤ ‖y - y₀‖ + ‖ζ • v‖ := norm_add_le _ _
      _ < 2 * ρ := by linarith
  have hmemU : ∀ y ∈ ball y₀ ρ, ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • v ∈ U := fun y hy ζ hζ =>
    hball (ball_subset_ball (by linarith) (hmem y hy ζ hζ))
  have hnorm_e : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by
    simp [abs_of_pos hr]
  let H : E → ℝ → ℂ := fun y θ => cauchyKernel r θ • F (y + circleMap 0 r θ • v)
  let H' : E → ℝ → (E →L[ℂ] ℂ) :=
    fun y θ => cauchyKernel r θ • fderiv ℂ F (y + circleMap 0 r θ • v)
  have hcontθ : ∀ y ∈ ball y₀ ρ, Continuous fun θ : ℝ => F (y + circleMap 0 r θ • v) := by
    intro y hy
    refine hF.continuousOn.comp_continuous
      (continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)) fun θ => ?_
    exact hmemU y hy _ (hnorm_e θ)
  have hHcont : ∀ y ∈ ball y₀ ρ, Continuous (H y) := fun y hy =>
    (continuous_cauchyKernel hr).smul (hcontθ y hy)
  -- the Cauchy formula along the line
  have hA : ∀ y ∈ ball y₀ ρ, fderiv ℂ F y v =
      (2 * Real.pi * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, H y θ := by
    intro y hy
    have hyU : y ∈ U := hball (ball_subset_ball (by linarith) hy)
    have hdiffy : DifferentiableAt ℂ F y := (hF y hyU).differentiableAt (hU.mem_nhds hyU)
    have hψ : DifferentiableOn ℂ (fun ζ : ℂ => F (y + ζ • v)) (closedBall (0 : ℂ) r) := by
      refine DifferentiableOn.comp (f := fun ζ : ℂ => y + ζ • v) hF ?_
        (fun ζ hζ => hmemU y hy ζ (mem_closedBall_zero_iff.mp hζ))
      exact (differentiable_const _ |>.add (differentiable_id.smul_const v)).differentiableOn
    have hder : deriv (fun ζ : ℂ => F (y + ζ • v)) 0 = fderiv ℂ F y v := by
      have h1 : HasDerivAt (fun ζ : ℂ => y + ζ • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
      have h2 : HasFDerivAt F (fderiv ℂ F y) (y + (0 : ℂ) • v) := by
        simpa using hdiffy.hasFDerivAt
      exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
    have hc := hψ.deriv_eq_smul_circleIntegral hr
    have hint : (∮ z in C(0, r), (1 / (z - 0) ^ 2) • F (y + z • v)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, H y θ := by
      unfold circleIntegral
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [H]
      rw [← smul_assoc, cauchyKernel_eq hr]
    rw [hint, hder] at hc
    have h2pi : (2 * Real.pi * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [hc, smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y₀ (mem_ball_self (by positivity)))
  have hB : HasFDerivAt (fun y => ∫ θ in (0 : ℝ)..2 * Real.pi, H y θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi, H' y₀ θ) y₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (bound := fun _ => 1 / r * (M / ρ)) (s := ball y₀ ρ) (ball_mem_nhds y₀ hρ) ?_ ?_ ?_ ?_ ?_ ?_
    · exact eventually_of_mem (ball_mem_nhds y₀ hρ) fun y hy => (hHcont y hy).aestronglyMeasurable
    · exact (hHcont y₀ (mem_ball_self hρ)).intervalIntegrable _ _
    · refine ((continuous_cauchyKernel hr).aestronglyMeasurable).smul ?_
      exact ((measurable_fderiv ℂ F).comp
        (continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)).measurable
          ).aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ y hy => ?_
      have hz : y + circleMap 0 r θ • v ∈ ball y₀ (2 * ρ) := hmem y hy _ (hnorm_e θ)
      have hsub : closedBall (y + circleMap 0 r θ • v) ρ ⊆ ball y₀ (4 * ρ) := by
        intro w hw
        rw [mem_closedBall] at hw
        rw [mem_ball] at hz ⊢
        have := dist_triangle w (y + circleMap 0 r θ • v) y₀
        linarith
      have hle := norm_fderiv_le_of_closedBall hρ (hF.mono (hsub.trans hball)) (fun w hw => hM w (hsub hw))
      show ‖cauchyKernel r θ • fderiv ℂ F (y + circleMap 0 r θ • v)‖ ≤ 1 / r * (M / ρ)
      rw [norm_smul, cauchyKernel_norm hr]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ y hy => ?_
      have hyU := hmemU y hy _ (hnorm_e θ)
      have hdy : DifferentiableAt ℂ F (y + circleMap 0 r θ • v) :=
        (hF _ hyU).differentiableAt (hU.mem_nhds hyU)
      have h1 : HasFDerivAt (fun x : E => x + circleMap 0 r θ • v)
          (ContinuousLinearMap.id ℂ E) y := (hasFDerivAt_id y).add_const _
      have h2 := HasFDerivAt.comp y hdy.hasFDerivAt h1
      exact (h2.const_smul (cauchyKernel r θ)).congr_fderiv (by rw [ContinuousLinearMap.comp_id])
  have hD : DifferentiableAt ℂ
      (fun y => (2 * Real.pi * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, H y θ) y₀ :=
    (hB.const_smul (2 * Real.pi * I)⁻¹).differentiableAt
  exact hD.congr_of_eventuallyEq
    (eventually_of_mem (ball_mem_nhds y₀ hρ) hA)

/-- Complex-differentiable functions on open sets of a finite-dimensional complex normed space
are `C^k` for every finite `k`. -/
theorem contDiffOn_nat_of_differentiableOn [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) :
    ∀ (k : ℕ) (F : E → ℂ), DifferentiableOn ℂ F U → ContDiffOn ℂ (k : WithTop ℕ∞) F U := by
  intro k
  induction k with
  | zero => intro F hF; exact contDiffOn_zero.mpr hF.continuousOn
  | succ k ih =>
    intro F hF
    have : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hF, fun h => absurd h (by simp), ?_⟩
    exact contDiffOn_clm_apply.mpr fun v => ih _ (differentiableOn_fderiv_apply hU hF v)

/-- Complex-differentiable functions on open sets of a finite-dimensional complex normed space
are `C^∞`. -/
theorem contDiffOn_top_of_differentiableOn [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U)
    {F : E → ℂ} (hF : DifferentiableOn ℂ F U) :
    ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F U :=
  contDiffOn_infty.mpr fun k => contDiffOn_nat_of_differentiableOn hU k F hF

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation: the appended children read by the transfer are admissible.** The argument of the
proof of `appended_child_inert`, for any carrier constants with `1 ≤ CH`, `1 ≤ Υ`:
`IsCarrierStart` then gives the start bound `2 A_k τ''_{k+1} ≤ b / (64 · 8π²)`
(`startBound_of_carrierStart`), and an admissible context with a scheduled finer slot of nonzero
weight has an admissible appended child (`appendChild_admissible`). -/

@[expose] public section

open Homogenization

namespace AVRegularity.Providers.GenSem

/-- The start bound from the carrier start with `1 ≤ CH`, `1 ≤ Υ`. -/
theorem startBound_of_carrierStart {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {bw CH Υ : ℝ} {j₀ : ℕ}
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hs : IsCarrierStart α q Λ bw CH Υ j₀) :
    ∀ k : ℕ, j₀ ≤ k + 1 → 2 * ocA α q Λ k * ocTauPP α q Λ (k + 1) ≤ bw / (64 * (8 * Real.pi ^ 2)) := by
  intro k hk
  have h := hs.1 k hk
  have hA : 0 ≤ ocA α q Λ k := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hT : 0 ≤ ocTauPP α q Λ (k + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  have hp : 0 ≤ ocA α q Λ k * ocTauPP α q Λ (k + 1) := mul_nonneg hA hT
  have h1 : 1 ≤ Υ * CH := by nlinarith
  nlinarith

/-- **The appended child of an admissible context is admissible where its weight is nonzero.** -/
theorem appendChild_admissible (D : OCData) (hΛ1 : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {bw : ℝ}
    (hbw : 0 < bw) {j₀ : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ bw / (64 * (8 * Real.pi ^ 2)))
    (i : ℕ) (pc : ℤ) (ch : RealChain) (hch : IsAdmissibleChain D bw j₀ i pc ch) (k : ℤ)
    (hk : Odd k) (hsch : IsScheduledIn D i k pc) (t : ℝ)
    (hcut : ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0) (ζf : Vec 2) :
    IsAdmissibleChain D bw j₀ (i + 1) k (ch.appendChild D k t ζf) := by
  obtain ⟨hctx, hbase, hlen, hslot, hodd, hsched, hchild⟩ := hch
  have hL : ch.baseLevel + ch.children.length + 1 = i := hctx
  have hcen := ChildInert.center_bound D (i := i) hΛ1 hζ hbw (hstart i (by omega)) pc k t hcut ζf
  have hslots : ch.slots ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  unfold IsAdmissibleChain IsCarrierChain
  refine ⟨?_, hbase, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RealChain.ctxLevel, RealChain.lastLevel, RealChain.appendChild,
      List.length_append, List.length_singleton]
    omega
  · simp [RealChain.appendChild, hlen]
  · simp [RealChain.slot, RealChain.appendChild]
  · intro q' hq'
    simp only [RealChain.appendChild, List.mem_append, List.mem_singleton] at hq'
    rcases hq' with h | h
    · exact hodd q' h
    · rw [h]; exact hk
  · intro kk hkk
    simp only [RealChain.appendChild, List.length_append, List.length_singleton] at hkk
    by_cases hlt : kk + 1 < ch.slots.length
    · simp only [RealChain.appendChild]
      rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
      exact hsched kk hlt
    · have hkk' : kk = ch.children.length := by omega
      subst hkk'
      simp only [RealChain.appendChild]
      have key : ∀ (a b : ℤ) (n : ℕ), a = k → b = pc → n = i → IsScheduledIn D n a b := by
        intro a b n ha hb hn; subst ha hb hn; exact hsch
      refine key _ _ _ ?_ ?_ (by omega)
      · simp [hlen]
      · rw [List.getElem_append_left (by omega)]
        have : ch.slot = pc := hslot
        simp only [RealChain.slot] at this
        rw [← this, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        simp [hlen]
  · intro kk hkk
    simp only [RealChain.appendChild, List.length_append, List.length_singleton] at hkk
    by_cases hlt : kk < ch.children.length
    · simp only [RealChain.appendChild]
      rw [List.getElem_append_left hlt]
      exact hchild kk hlt
    · have hkk' : kk = ch.children.length := by omega
      subst hkk'
      simp only [RealChain.appendChild]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_singleton]
      have e1 : ch.ctxLevel = i := hctx
      have e2 : ch.slot = pc := hslot
      have e3 : ch.baseLevel + 1 + ch.children.length = i := by omega
      rw [e3, e1, e2]
      have hDe : D.eps i = D.eps i := rfl
      exact hcen

end AVRegularity.Providers.GenSem
end
end

section
/-! The complex carrier `carrierC` is open, and the real parameters of an admissible chain lie in
it. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity.Providers.GenSem

open AVRegularity

theorem isOpen_carrierC (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ) (mres : ℝ) :
    IsOpen (carrierC D b dd n mres) := by
  unfold carrierC
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsOpen.inter (isOpen_lt (by fun_prop) continuous_const) (IsOpen.inter ?_ ?_)
  · refine isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  · exact isOpen_lt (by fun_prop) continuous_const

/-- The real parameters of an admissible chain lie in the outer complex carrier. -/
theorem paramsC_mem_carrierC {D : OCData} (hΛ : 1 ≤ D.Λ) {b : ℝ} (hb : 0 < b) {j₀ i : ℕ}
    {p : ℤ} {ch : RealChain} (h : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2) :
    ch.paramsC ζ ∈ carrierC D b ch.data ch.children.length 2 := by
  have he : 0 < D.eps ch.baseLevel := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  have hc : ∀ k : ℕ, ∀ hk : k < ch.children.length,
      ∑ a : Fin 2, |(ch.children[k]).center a| < (1 + 2) * b / 4 * D.eps (ch.baseLevel + 1 + k) :=
    h.2.2.2.2.2.2
  have hb1 : 0 < (3 + 2 / 4) * b + b / 64 := by positivity
  have hb2 : 0 < (3 + 2 / 4) * b := by positivity
  refine ⟨?_, ⟨fun k => ⟨?_, ?_⟩, ?_⟩⟩
  · simp only [RealChain.paramsC, Complex.ofReal_im, abs_zero, Finset.sum_const_zero]
    exact mul_pos (by norm_num) he
  · have := hc k.1 k.2
    simpa [RealChain.paramsC, RealChain.data] using this
  · simpa [RealChain.paramsC] using hb1
  · simpa [RealChain.paramsC] using hb2

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation, restricted parallel invariance: basics.** `ParEq` is the
`RealChain.IsParShift`, and `ParEq` preserves admissibility. -/

@[expose] public noncomputable section

open Homogenization AVRegularity

namespace AVRegularity.Providers.GenSem

theorem parStep_iff (p : ℤ) (c c' : ChainChild) :
    ParStep p c c' ↔ ChainChild.IsParStep p c c' := Iff.rfl

theorem parRel_iff_isParRel : ∀ (cs cs' : List ChainChild) (f : ℕ → ℤ),
    ParRel f cs cs' ↔ ChainChild.IsParRel f cs cs'
  | [], [], _ => Iff.rfl
  | [], _ :: _, _ => Iff.rfl
  | _ :: _, [], _ => Iff.rfl
  | _ :: cs, _ :: cs', f => by
    simp only [ParRel, ChainChild.IsParRel, parRel_iff_isParRel cs cs', parStep_iff]

theorem parEq_iff_isParShift (ch ch' : RealChain) : ParEq ch ch' ↔ ch.IsParShift ch' := by
  unfold ParEq RealChain.IsParShift
  rw [parRel_iff_isParRel]

end AVRegularity.Providers.GenSem
end
end

section
/-! **Generation, restricted parallel invariance: the predicates.** Invariance over the pulse window
and the admissible chains of the slot `p` of level `i`, with the operations (sums, products) and
the restricted time-integral chain lemma of the transverse inverse. -/

@[expose] public noncomputable section

open Homogenization AVRegularity

namespace AVRegularity.Providers.GenSem

/-- Invariance of a context/cell function over the slot `p` of level `i`, restricted to the pulse
window and the admissible chains. -/
def ParInvOn (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (f : ℝ → RealChain → Vec 2 → ℝ) : Prop :=
  ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
    (∀ ch' ζ, ParEq ch ch' → f t ch' ζ = f t ch ζ) ∧
    ∀ ζ (s : ℝ), f t ch (ζ + s • basisVec (parIdx p)) = f t ch ζ

/-- Invariance of a family function under parallel child-phase shifts, restricted. -/
def FamInvOn (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (f : ℝ → RealChain → ℝ) : Prop :=
  ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
    ∀ ch', ParEq ch ch' → f t ch' = f t ch

/-- The restricted invariance predicate of a sort. -/
def _root_.AVRegularity.GenSort.ParInvOn' :
    (s : GenSort) → OCData → ℝ → ℕ → ℕ → ℤ → s.Sem → Prop
  | .ctx, D, b, j₀, i, p, f => ParInvOn D b j₀ i p f
  | .fam, D, b, j₀, i, p, f => FamInvOn D b j₀ i p f
  | .cell, D, b, j₀, i, p, f => ParInvOn D b j₀ i p f

theorem ParInvOn.zipWith {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    {fa fb : ℝ → RealChain → Vec 2 → ℝ} (op : ℝ → ℝ → ℝ)
    (ha : ParInvOn D b j₀ i p fa) (hb : ParInvOn D b j₀ i p fb) :
    ParInvOn D b j₀ i p (fun t c z => op (fa t c z) (fb t c z)) :=
  fun t ht ch hA =>
    ⟨fun ch' ζ h => by simp only [(ha t ht ch hA).1 ch' ζ h, (hb t ht ch hA).1 ch' ζ h],
      fun ζ s => by simp only [(ha t ht ch hA).2 ζ s, (hb t ht ch hA).2 ζ s]⟩

theorem FamInvOn.zipWith {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    {fa fb : ℝ → RealChain → ℝ} (op : ℝ → ℝ → ℝ)
    (ha : FamInvOn D b j₀ i p fa) (hb : FamInvOn D b j₀ i p fb) :
    FamInvOn D b j₀ i p (fun t c => op (fa t c) (fb t c)) :=
  fun t ht ch hA ch' h => by simp only [ha t ht ch hA ch' h, hb t ht ch hA ch' h]

/-- `transverseInverseSem` at two chains agrees when the fluxes agree on `[t₀, t]`, the initial
states agree at `t₀` and the family metrics agree: only the flux on `[t₀, t]` matters. -/
theorem transverseInverseSem_chain_on (D : OCData) (i : ℕ) (p : ℤ) (F : Fin 2 → GenSort.Sem .cell)
    (t₀ : ℝ) (ι : GenSort.Sem .cell) (t : ℝ) {ch ch' : RealChain} (η : Vec 2) (ht : t₀ ≤ t)
    (hF : ∀ k, ∀ s ∈ Set.Icc t₀ t, F k s ch' = F k s ch) (hι : ι t₀ ch' = ι t₀ ch)
    (hm : ∀ u, ch'.famMetric D u = ch.famMetric D u) :
    transverseInverseSem D i p F t₀ ι t ch' η = transverseInverseSem D i p F t₀ ι t ch η := by
  have hk : ∀ h t s, modeKernel D i (transverseIndex p) ch' h t s =
      modeKernel D i (transverseIndex p) ch h t s := by
    intro h t s; simp only [modeKernel, hm]
  have key : ∀ h : ℤ, (∫ s in t₀..t, modeKernel D i (transverseIndex p) ch h t s *
      phaseCoeff (transverseIndex p) (F (transverseIndex p) s ch') h) =
      ∫ s in t₀..t, modeKernel D i (transverseIndex p) ch h t s *
      phaseCoeff (transverseIndex p) (F (transverseIndex p) s ch) h := by
    intro h
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    simp only [hF _ s hs]
  simp only [transverseInverseSem, hk, key, hι]

/-- Every child slot of an `evalChild` node of `e` is odd (needed for admissibility of the appended
child: carrier chains have odd slots; this is not implied by `IsScheduledIn`). -/
def _root_.AVRegularity.Gen.EvalOdd :
    {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, .geo _ _ => True
  | _, _, _, .drift _ => True
  | _, _, _, .time _ => True
  | _, _, _, .add a b => Gen.EvalOdd a ∧ Gen.EvalOdd b
  | _, _, _, .mul a b => Gen.EvalOdd a ∧ Gen.EvalOdd b
  | _, _, _, .dOld _ a => Gen.EvalOdd a
  | _, _, _, .dPhase a => Gen.EvalOdd a
  | _, _, _, .dSlowFam _ a => Gen.EvalOdd a
  | _, _, _, .dSlowCell _ a => Gen.EvalOdd a
  | _, _, _, .dInternal a => Gen.EvalOdd a
  | _, _, _, .restrict a => Gen.EvalOdd a
  | _, _, _, .cellInv F _ ι => (∀ k, Gen.EvalOdd (F k)) ∧ Gen.EvalOdd ι
  | _, _, _, .transPrim a => Gen.EvalOdd a
  | _, _, _, .solved _ _ _ _ _ _ _ _ _ => True
  | _, _, _, .mean a => Gen.EvalOdd a
  | _, _, _, .famCell a => Gen.EvalOdd a
  | _, _, _, .evalChild p' a => Odd p' ∧ Gen.EvalOdd a

end AVRegularity.Providers.GenSem
end
end

section
/-! The time derivative of the spatial Jacobian of the offset flows of a real chain is `C^∞` in
the space variable: for every `t, r`, `x ↦ ∂_u D_x 𝔛(u, x, r)|_{u = t}` has smooth entries.
Induction over `geomAux` as in `geomJacC1_geomAux`: the base is a stream flow (jointly smooth); a
child composes the parent flow with `A + κ(u) V'(A)` and `jacComp_deriv_core` expresses the
derivative through spatially smooth terms with constant coefficients. -/

@[expose] public noncomputable section

open Homogenization AVenhance AVRegularity AVRegularity.CycleReference
  AVRegularity.EntryWeakProofs

namespace AVRegularity.Providers.GenSem

/-- A matrix-valued map on `Vec 2` with smooth entries. -/
def MatSmooth (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => M x i j)

theorem MatSmooth.add {M N : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hM : MatSmooth M)
    (hN : MatSmooth N) : MatSmooth (fun x => M x + N x) :=
  fun i j => (hM i j).add (hN i j)

theorem MatSmooth.mul {M N : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hM : MatSmooth M)
    (hN : MatSmooth N) : MatSmooth (fun x => M x * N x) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hM i 0).mul (hN 0 j)).add ((hM i 1).mul (hN 1 j))

theorem MatSmooth.const_smul {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hM : MatSmooth M) (c : ℝ) :
    MatSmooth (fun x => c • M x) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.mul (hM i j)

theorem MatSmooth.comp {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hM : MatSmooth M)
    {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : MatSmooth (fun x => M (f x)) :=
  fun i j => (hM i j).comp hf

theorem matSmooth_jac {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    MatSmooth (fun x => jacMatrix f x) :=
  fun i j => jacMatrix_entry_smooth hf i j

/-- The time derivative of the spatial Jacobian of the offset flow is smooth in space. -/
def GeomTimeSmooth (g : ChainGeom) : Prop :=
  ∀ t r : ℝ, MatSmooth (fun x => Matrix.of (fun a b =>
    deriv (fun u => jacMatrix (fun y => g.1 u y r) x a b) t))

theorem timeSmooth_of_jointSmooth {H : ℝ → Vec 2 → Vec 2}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => H p.1 p.2)) (t : ℝ) :
    MatSmooth (fun x => Matrix.of (fun a b =>
      deriv (fun u => jacMatrix (fun y => H u y) x a b) t)) := by
  intro a b
  set e : ℝ × Vec 2 → ℝ := fun p => jacMatrix (fun y => H p.1 y) p.2 a b with hedef
  have he1 : e = fun p => fderiv ℝ (fun q : ℝ × Vec 2 => H q.1 q.2) p (0, basisVec b) a := by
    funext p
    have h1 : HasFDerivAt (fun y : Vec 2 => ((p.1, y) : ℝ × Vec 2))
        ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    have h2 := ((hH.differentiable (by simp)) (p.1, p.2)).hasFDerivAt.comp p.2 h1
    have h3 : HasFDerivAt (fun y => H p.1 y) _ p.2 := h2
    simp only [hedef, jacMatrix, Matrix.of_apply, h3.fderiv]
    simp
  have he : ContDiff ℝ (⊤ : ℕ∞) e := by
    rw [he1]
    exact (contDiff_apply ℝ ℝ a).comp
      ((hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)
  have hed : ∀ x, deriv (fun u => jacMatrix (fun y => H u y) x a b) t =
      fderiv ℝ e (t, x) (1, 0) := by
    intro x
    have h := (((he.differentiable (by simp)) (t, x)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact h.deriv
  simp only [Matrix.of_apply, hed]
  exact (((he.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp
    (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const)

theorem geomTimeSmooth_base (D : OCData) (k : ℕ) (x : Vec 2) (s : ℝ) :
    GeomTimeSmooth (D.flowOf k, x, s) := by
  intro t r
  exact timeSmooth_of_jointSmooth (H := fun u y => D.flowOf k u y r)
    ((CycleReference.streamFlow_joint_smooth (D.hΦ k)).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))) t

theorem geomTimeSmooth_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hs : GeomSpatialSmooth g) (hj : GeomJacC1 g)
    (ht : GeomTimeSmooth g) : GeomTimeSmooth (D.childGeom k pk s' c g) := by
  intro t r
  set A : Vec 2 → Vec 2 := fun x => g.1 g.2.2 x r with hAdef
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := hs g.2.2 r
  set γ : Vec 2 := c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center) with hγ
  set V : Vec 2 → Vec 2 := fun z =>
    ocShearVel D.α D.q D.Λ k pk (D.eps k • ((D.eps k)⁻¹ • z + γ)) with hVdef
  have hV : ContDiff ℝ (⊤ : ℕ∞) V :=
    (ocShearVel_spatial_smooth _ _ _ _ _).comp
      (((contDiff_id.const_smul _).add contDiff_const).const_smul _)
  set κ : ℝ → ℝ := fun u => D.eps k * ((D.eps k)⁻¹ *
    ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) with hκ
  set X : ℝ → Vec 2 → Vec 2 := fun u y => g.1 u y g.2.2 with hX
  have hpc : Continuous (ocPulse D.α D.q D.Λ D.ζ k pk) :=
    AVRegularity.CycleReference.ocPulse_continuous hζ pk
  have hκd : HasDerivAt κ (D.eps k * ((D.eps k)⁻¹ * ocPulse D.α D.q D.Λ D.ζ k pk t)) t :=
    ((intervalIntegral.integral_hasDerivAt_right (hpc.intervalIntegrable _ _)
      (hpc.stronglyMeasurableAtFilter _ _) hpc.continuousAt).const_mul _).const_mul _
  set p : ℝ := D.eps k * ((D.eps k)⁻¹ * ocPulse D.α D.q D.Λ D.ζ k pk t) with hp
  have hXd : ∀ u, Differentiable ℝ (X u) := fun u => (hs u g.2.2).differentiable (by simp)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hflow : ∀ u y, (D.childGeom k pk s' c g).1 u y r = X u (A y + κ u • V (A y + 0)) := by
    intro u y
    simp only [OCData.childGeom, OCData.relDisp, hX, hAdef, hκ, hVdef, hγ, smul_smul, add_zero]
  have hfam : ∀ u x', jacMatrix (fun y => (D.childGeom k pk s' c g).1 u y r) x' =
      jacMatrix (fun x => X u (A x + κ u • V (A x + 0))) x' := by
    intro u x'
    congr 1
    funext y
    exact hflow u y
  have hxA : ContDiff ℝ (⊤ : ℕ∞) (fun x' => A x' + κ t • V (A x' + 0)) :=
    hA.add ((hV.comp (hA.add contDiff_const)).const_smul _)
  have hJX : MatSmooth (fun y => jacMatrix (X t) y) := matSmooth_jac (hs t g.2.2)
  have hJA : MatSmooth (fun x' => jacMatrix A x') := matSmooth_jac hA
  have hJV : MatSmooth (fun x' => jacMatrix V (A x' + 0)) :=
    (matSmooth_jac hV).comp (hA.add contDiff_const)
  have hT1 : MatSmooth (fun x' => Matrix.of (fun a b =>
      deriv (fun u => jacMatrix (X u) (A x' + κ t • V (A x' + 0)) a b) t)) :=
    (ht t g.2.2).comp hxA
  have hT2 : MatSmooth (fun x' => Matrix.of (fun a b =>
      fderiv ℝ (fun y => jacMatrix (X t) y a b) (A x' + κ t • V (A x' + 0))
        (p • V (A x' + 0)))) := by
    intro a b
    simp only [Matrix.of_apply]
    exact ((((jacMatrix_entry_smooth (hs t g.2.2) a b).fderiv_right (m := (⊤ : ℕ∞))
      (by simp)).comp hxA).clm_apply ((hV.comp (hA.add contDiff_const)).const_smul p))
  have hT3 : MatSmooth (fun x' => jacMatrix (X t) (A x' + κ t • V (A x' + 0))) := hJX.comp hxA
  have hcore : ∀ x', Matrix.of (fun a b => deriv (fun u => jacMatrix
        (fun y => (D.childGeom k pk s' c g).1 u y r) x' a b) t) =
      (Matrix.of (fun a b => deriv (fun u => jacMatrix (X u) (A x' + κ t • V (A x' + 0)) a b) t) +
        Matrix.of (fun a b => fderiv ℝ (fun y => jacMatrix (X t) y a b)
          (A x' + κ t • V (A x' + 0)) (p • V (A x' + 0)))) *
        (jacMatrix A x' + κ t • (jacMatrix V (A x' + 0) * jacMatrix A x')) +
      jacMatrix (X t) (A x' + κ t • V (A x' + 0)) * (p • (jacMatrix V (A x' + 0) * jacMatrix A x')) := by
    intro x'
    have hG : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => fderiv ℝ (X q.1) q.2)
        (t, A x' + κ t • V (A x' + 0)) :=
      ((hj g.2.2).differentiable (by simp)) (t, A x' + κ t • V (A x' + 0))
    have h := jacComp_deriv_core hXd hAd hVd hκd 0 x' (A x' + κ t • V (A x' + 0)) rfl hG
    simp only [hfam]
    exact h
  intro a b
  have hfun : (fun x => Matrix.of (fun a b => deriv (fun u => jacMatrix
        (fun y => (D.childGeom k pk s' c g).1 u y r) x a b) t)) =
      fun x' => (Matrix.of (fun a b => deriv (fun u => jacMatrix (X u)
          (A x' + κ t • V (A x' + 0)) a b) t) +
        Matrix.of (fun a b => fderiv ℝ (fun y => jacMatrix (X t) y a b)
          (A x' + κ t • V (A x' + 0)) (p • V (A x' + 0)))) *
        (jacMatrix A x' + κ t • (jacMatrix V (A x' + 0) * jacMatrix A x')) +
      jacMatrix (X t) (A x' + κ t • V (A x' + 0)) *
        (p • (jacMatrix V (A x' + 0) * jacMatrix A x')) := funext hcore
  rw [hfun]
  exact (((hT1.add hT2).mul (hJA.add ((hJV.mul hJA).const_smul _))).add
    (hT3.mul ((hJV.mul hJA).const_smul p))) a b

theorem geomTimeSmooth_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomSpatialSmooth g → GeomJacC1 g → GeomTimeSmooth g →
        GeomTimeSmooth (D.geomAux k sl cs g)
  | [], k, sl, g, _, _, ht => by
    match sl with
    | [] => exact ht
    | [_] => exact ht
    | _ :: _ :: _ => exact ht
  | c :: cs, k, sl, g, hs, hj, ht => by
    match sl with
    | [] => exact ht
    | [_] => exact ht
    | pk :: pk1 :: rest =>
      exact geomTimeSmooth_geomAux D hζ cs (k + 1) (pk1 :: rest)
        (geomSpatialSmooth_childGeom D k pk _ c hs) (geomJacC1_childGeom D hζ k pk _ c hs hj)
        (geomTimeSmooth_childGeom D hζ k pk _ c hs hj ht)

/-- **The time derivative of the spatial Jacobian of a chain geometry is smooth in space.** -/
theorem geomTimeSmooth_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    GeomTimeSmooth (ch.geom D) :=
  geomTimeSmooth_geomAux D hζ _ _ _
    (fun _ _ => (CycleReference.streamFlow_joint_smooth (D.hΦ ch.baseLevel)).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)))
    (geomJacC1_base D _ _ _) (geomTimeSmooth_base D _ _ _)

end AVRegularity.Providers.GenSem
end
end

section
/-! Explicit parameter maps of recentered chains, avoiding the dependent type `ChainParamsC n`:
`RealChain.paramsN` (parameters of a chain at a propositionally equal length), the transport
lemma, and the two recentering models (no child; last child shifted). -/

@[expose] public noncomputable section

open Homogenization AVRegularity

namespace AVRegularity.Providers.GenSem

/-- The parameters of a chain at a length `n` propositionally equal to its number of children. -/
def _root_.AVRegularity.RealChain.paramsN (ch : RealChain) (n : ℕ) (h : ch.children.length = n) (ζ : Vec 2) :
    ChainParamsC n :=
  (fun a => (ch.base a : ℂ),
    fun k => (fun a => ((ch.children.get (Fin.cast h.symm k)).center a : ℂ),
      fun a => ((ch.children.get (Fin.cast h.symm k)).phase a : ℂ)),
    fun a => (ζ a : ℂ))

/-- Transport along equalities of the discrete data, the length and the parameters. -/
theorem paramsC_transport (ch : RealChain) (dd : ChainData) (n : ℕ) (hd : ch.data = dd)
    (hn : ch.children.length = n) (P : ChainParamsC n) (ζ : Vec 2)
    (hP : ch.paramsN n hn ζ = P) (Q : ∀ (_ : ChainData) (n : ℕ), ChainParamsC n → Prop)
    (hQ : Q ch.data ch.children.length (ch.paramsC ζ)) : Q dd n P := by
  subst hd
  subst hn
  subst hP
  exact hQ

/-- The shift of the child `k` of `n` children (only the last one moves). -/
def shiftC (n : ℕ) (k : Fin n) (w : Vec 2) (a : Fin 2) : ℂ :=
  if (k : ℕ) + 1 = n then (w a : ℂ) else 0

/-- Parameters of the chain `A` with the last child's center moved by `w` and its phase by
`e • w` (final phase `z`). -/
def PmShift (A : RealChain) (w : Vec 2) (e : ℝ) (z : Vec 2) : ChainParamsC A.children.length :=
  (fun a => (A.base a : ℂ),
    fun k => (fun a => ((A.children.get k).center a : ℂ) + shiftC A.children.length k w a,
      fun a => ((A.children.get k).phase a : ℂ) + shiftC A.children.length k (e • w) a),
    fun a => (z a : ℂ))

/-- Parameters of the chain `A` with the base label moved by `w` (final phase `z`). -/
def PmBase (A : RealChain) (w : Vec 2) (z : Vec 2) : ChainParamsC A.children.length :=
  (fun a => ((A.base a + w a : ℝ) : ℂ),
    fun k => (fun a => ((A.children.get k).center a : ℂ),
      fun a => ((A.children.get k).phase a : ℂ)),
    fun a => (z a : ℂ))

theorem paramsN_base (A A' : RealChain) (w : Vec 2) (hA' : A' = { A with base := A.base + w })
    (hl : A'.children.length = A.children.length) (z : Vec 2) :
    A'.paramsN A.children.length hl z = PmBase A w z := by
  subst hA'
  ext <;> simp [RealChain.paramsN, PmBase]

theorem paramsN_snoc (A A' : RealChain) (cs : List ChainChild) (c : ChainChild)
    (hc : A.children = cs ++ [c]) (w : Vec 2) (e : ℝ)
    (hA' : A' = { A with children := cs ++ [⟨c.center + w, c.phase + e • w⟩] })
    (hl : A'.children.length = A.children.length) (z : Vec 2) :
    A'.paramsN A.children.length hl z = PmShift A w e z := by
  subst hA'
  have hn : A.children.length = cs.length + 1 := by simp [hc]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext k
  have hk : (k : ℕ) < cs.length + 1 := hn ▸ k.2
  have hA : A.children[(k : ℕ)]'k.2 = (cs ++ [c])[(k : ℕ)]'(by simpa using hk) :=
    List.getElem_of_eq hc _
  have hn' : cs.length + 1 = A.children.length := hn.symm
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
  · have h1 : ¬ ((k : ℕ) + 1 = A.children.length) := by omega
    refine Prod.ext ?_ ?_ <;> funext a <;>
      simp [PmShift, RealChain.paramsN, shiftC, h1, hA, List.getElem_append, hlt]
  · have hA2 : ∀ h : cs.length < A.children.length, A.children[cs.length]'h = c := fun h => by
      rw [List.getElem_of_eq hc]; simp
    refine Prod.ext ?_ ?_ <;> funext a <;>
      simp [PmShift, RealChain.paramsN, shiftC, hA2, List.getElem_append, heq, hn']

end AVRegularity.Providers.GenSem
end
end
end

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Generation: the lift setup of a path family from its localized lift sequences.** For the lift
sequences of the scalar family on every admissible base chain over the odd slot `k` of level `m`
(`IsLiftSequenceOn (ladderOmega …)`, as in `SuccSource.IsLiftFamily`), with the reserve
`R ≤ sX, sZ`, `N + Dm + 2 ≤ R`, source edges `C^R` on the admissible offsets and the edge
aggregate represented on every admissible choice of offsets, there are cut-off edges, cut-off
lifts and balls `U A ∋ 0` (`exists_liftGenSetup`):
* the lift setup `LiftGenSetup` of the cut-off data on the original interval of the pulse (in cell
  time) over the admissible base chains;
* the cut-off data agree with the true data on `U A` and the cut-off lifts with the true lifts;
* the cut-off lifts are `LiftRegular` of every order `R' ≤ R` (for the covariance letters). -/

namespace UEnv

variable {ι : Type} {Dm : ℕ}


/-- The represented edge aggregate transfers to edges agreeing on the offsets. -/
theorem EdgeURep.of_agree {V : UEnv (RealChain × ℝ)}
    {Q Q' : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm} (h : V.EdgeURep Q)
    (hag : ∀ l ∈ V.W, Uniqueness.EdgesAgreeOn (V.U l) (Q l.1).edge (Q' l.1).edge) :
    V.EdgeURep Q' := by
  intro v u d α c
  refine (h v u d α c).congr fun l hl X hX z => ?_
  exact (Uniqueness.list_sum_map_forall₂ (hag l hl v u d) fun γ γ' hγ => by
    rw [hγ.1, hγ.2 α l.2 X hX z]).symm

end UEnv

variable {h : ℕ} {Dm : ℕ}

/-- The outcome of the cut-off construction for the path family `edge`, `Cc` over the odd slot
`k` of level `m`: cut-off edges, cut-off lifts and offset sets `U A` with the lift setup of the
cut-off data, agreement with the true data and lifts on `U A`, and regularity of every order
`R' ≤ R`. -/
def CutoffLiftSetup (D : OCData) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (m : ℕ) (k : ℤ) (ρ : ℝ)
    (edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ))
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (sX sZ N R : ℕ) : Prop :=
  ∃ (edge' : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ))
      (Cc' : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
      (U : RealChain → Set (Vec 2)),
      LiftGenSetup D b j₀ 𝒮 m k {A | IsAdmissibleChain D b j₀ m k A} ρ edge' U sX sZ
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h Cc' ∧
      (∀ A, IsAdmissibleChain D b j₀ m k A →
        IsOpen (U A) ∧ (0 : Vec 2) ∈ U A ∧ U A ⊆ ladderOmega D b j₀ m k A ρ ∧
        Uniqueness.DataAgreeOn (U A) (familyLiftData D m k A ρ (edge A))
          (familyLiftData D m k A ρ (edge' A)) ∧
        (∀ hh n m' (α : DerivativeWord2 m') t, ∀ X ∈ U A,
          Cc' A hh n m' α t X = Cc A hh n m' α t X) ∧
        ∀ hh ≤ h, ∀ n R', R' ≤ R →
          ∀ τ ∈ Icc (D.slotStart m k / D.cellScaleSq m)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m), ∀ w,
          LiftRegular (familyLiftData D m k A ρ (edge' A)) (Cc' A) w τ hh n R')

/-- **The lift setup of a path family from its localized lift sequences.** -/
theorem exists_liftGenSetup (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports)
    (m : ℕ) (k : ℤ) (hk : Odd k) (ρ : ℝ) (hlam : ρ / D.eps (m - 1) ≠ 0)
    (edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ))
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hNR : N + Dm + 2 ≤ R)
    (hC : ∀ A, IsAdmissibleChain D b j₀ m k A →
      IsLiftSequenceOn (ladderOmega D b j₀ m k A ρ) (familyLiftData D m k A ρ (edge A)) sX sZ
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N h (Cc A))
    (hedge : ∀ A, IsAdmissibleChain D b j₀ m k A →
      ∀ τ ∈ Icc (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
      ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
        γ ∈ (familyLiftData D m k A ρ (edge A)).edge v u d → ∀ α c,
          ContDiffOn ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α τ p.1 p.2 c)
            (ladderOmega D b j₀ m k A ρ ×ˢ univ))
    (hedges : ∀ U : RealChain → Set (Vec 2),
      (∀ A, IsAdmissibleChain D b j₀ m k A → U A ⊆ ladderOmega D b j₀ m k A ρ) →
      (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).EdgeURep
          (fun A => familyLiftData D m k A ρ (edge A))) :
    CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R := by
  unfold CutoffLiftSetup
  set t₀ := D.slotStart m k / D.cellScaleSq m with ht₀
  set t₁ := (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m with ht₁
  have hc : 0 < D.cellScaleSq m := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ m
  have key : ∀ A, IsAdmissibleChain D b j₀ m k A → ∃ r > 0,
      Metric.ball (0 : Vec 2) r ⊆ ladderOmega D b j₀ m k A ρ ∧
      ∃ (e' : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ))
        (C' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)),
      Uniqueness.DataAgreeOn (Metric.ball (0 : Vec 2) r) (familyLiftData D m k A ρ (edge A))
        (familyLiftData D m k A ρ e') ∧
      (∀ hh n m' (α : DerivativeWord2 m') t, ∀ X ∈ Metric.ball (0 : Vec 2) r,
        C' hh n m' α t X = Cc A hh n m' α t X) ∧
      IsLiftLocal (familyLiftData D m k A ρ e') (Metric.ball (0 : Vec 2) r) sZ t₀ t₁ N h C' ∧
      ∀ hh ≤ h, ∀ n R', R' ≤ R → ∀ τ ∈ Icc t₀ t₁, ∀ w,
        LiftRegular (familyLiftData D m k A ρ e') C' w τ hh n R' := fun A hA =>
    exists_cutoff_lift_data D m k hA.2.2.1 ρ hlam (edge A) (isOpen_ladderOmega D b j₀ m k A ρ)
      (zero_mem_ladderOmega hζ hA ρ) (hC A hA) hRX hRZ (hedge A hA)
  choose! r hr hrΩ e' C' hagree hCeq hloc hreg using key
  have hkap : ∀ i, 0 < D.kap i := EntryWeakProofs.weakData_kap_pos D hΛ hζ hκ
  refine ⟨e', C', fun A => Metric.ball 0 (r A), ?_, fun A hA => ⟨Metric.isOpen_ball,
    Metric.mem_ball_self (hr A hA), hrΩ A hA, hagree A hA, hCeq A hA, hreg A hA⟩⟩
  exact
    { hζ := hζ
      hρ := fun h0 => hlam (by rw [h0, zero_div])
      hU := fun _ _ => Metric.isOpen_ball
      hk := hk
      hA := fun _ hA => ⟨hA.2.2.1, hA.2.2.2.1⟩
      hc := hc
      h01 := EntryWeakProofs.weakData_lift_window D hΛ hζ hκ m k
      hstart := mul_div_cancel₀ _ hc.ne'
      hη := (Real.sqrt_pos.mpr (div_pos (hkap m) (hkap (m - 1)))).ne'
      hsZ := by omega
      loc := fun A hA => hloc A hA
      edges := (hedges _ fun A hA => hrΩ A hA).of_agree fun l hl => (hagree l.1 hl.1).edge
      reg := fun A hA hh hhH n _ hnN τ hτ w =>
        hreg A hA hh hhH n (n + Dm + 2) (by omega) τ hτ w }

end AVRegularity.Providers.GenSem
end
end
