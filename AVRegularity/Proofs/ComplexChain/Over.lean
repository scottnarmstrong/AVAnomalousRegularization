-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexChain.Family
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **The base family**. For a holomorphic field `v` on the strip `S_ℓ` and a window `[a, b]` of
the flow, the complex flow `X(u, y, r)` with a holomorphic center point `x_P` (`|Im x_P|₁ ≤ B₀`) and
an anchor in the window is a complex family with the invariants `OK Ω W ϱ (10Γ) (b - a)`
(`baseFam_ok`), as soon as the balls of radius `ϱ` around the transported centers stay in the
initial set of the group law, `B₀/(1 - Γ(b-a)) + 2ϱ ≤ (1 - Γ(b-a))² ℓ'`, and `10Γ(b - a) ≤ 1/2`. -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **The base family**: the complex flow of `v` with the center `x_P` and the anchor `s`. -/
def baseFam (v : ℝ → CVec → CVec) (ℓ' : ℝ) (ctr : Par → CVec) (s : ℝ) : CFam Par where
  fl _ u y r := cflow v ℓ' u y r
  ctr := ctr
  anc := s

variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

theorem imL1_lt_of_mem_ball {c y : CVec} {ρ : ℝ} (hy : y ∈ ball c ρ) : imL1 y < imL1 c + 2 * ρ := by
  have h1 := imL1_le_add_l1 y c
  have h2 := l1_le_two_mul_norm (y - c)
  rw [mem_ball, dist_eq_norm] at hy
  linarith

/-- **The base family has the invariants.** -/
theorem baseFam_ok (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {W : Set ℝ}
    (hW : W ⊆ Icc a b) {ctr : Par → CVec} {Ω : Set Par} (hΩ : IsOpen Ω)
    (hctr : DifferentiableOn ℂ ctr Ω) {B₀ ϱ : ℝ} (hB₀ : ∀ P ∈ Ω, imL1 (ctr P) ≤ B₀) (hϱ : 0 < ϱ)
    (hdom : B₀ / (1 - Γ * (b - a)) + 2 * ϱ ≤ (1 - Γ * (b - a)) ^ 2 * ℓ')
    (hΓT : 10 * Γ * (b - a) ≤ 1 / 2) {s : ℝ} (hs : s ∈ W) :
    (baseFam v ℓ' ctr s : CFam Par).OK Ω W ϱ (10 * Γ) (b - a) := by
  have hr := ratio_lt_one hw
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have h1r : 0 < 1 - Γ * (b - a) := by linarith
  have hℓ' := hw.hℓ'
  have hsq : (1 - Γ * (b - a)) ^ 2 ≤ 1 - Γ * (b - a) := by nlinarith
  have hB0 : ∀ P ∈ Ω, 0 ≤ B₀ := fun P hP => (imL1_nonneg _).trans (hB₀ P hP)
  -- the transported centers and the balls around them
  have hctrZ : ∀ P ∈ Ω, ctr P ∈ Z0 ℓ' Γ a b := by
    intro P hP
    show imL1 (ctr P) ≤ (1 - Γ * (b - a)) * ℓ'
    have h1 : B₀ ≤ B₀ / (1 - Γ * (b - a)) := by
      rw [le_div_iff₀ h1r]; nlinarith [hB0 P hP]
    calc imL1 (ctr P) ≤ B₀ := hB₀ P hP
      _ ≤ (1 - Γ * (b - a)) ^ 2 * ℓ' := by linarith
      _ ≤ (1 - Γ * (b - a)) * ℓ' := mul_le_mul_of_nonneg_right hsq hℓ'.le
  have hcur : ∀ P ∈ Ω, ∀ r ∈ W, imL1 ((baseFam v ℓ' ctr s : CFam Par).cur P r) ≤
      B₀ / (1 - Γ * (b - a)) := by
    intro P hP r hr
    exact (imL1_cflow_le hv.toStripField hw (hctrZ P hP) (hW hs) (hW hr)).trans
      (div_le_div_of_nonneg_right (hB₀ P hP) h1r.le)
  have hball : ∀ P ∈ Ω, ∀ r ∈ W, ∀ y ∈ ball ((baseFam v ℓ' ctr s : CFam Par).cur P r) ϱ,
      imL1 y ≤ (1 - Γ * (b - a)) ^ 2 * ℓ' := by
    intro P hP r hr y hy
    have := imL1_lt_of_mem_ball hy
    linarith [hcur P hP r hr]
  have hU : ∀ P ∈ Ω, ∀ r ∈ W, ∀ y ∈ ball ((baseFam v ℓ' ctr s : CFam Par).cur P r) ϱ,
      y ∈ U0 ℓ' Γ a b := by
    intro P hP r hr y hy
    show imL1 y < (1 - Γ * (b - a)) * ℓ'
    have h1 := imL1_lt_of_mem_ball hy
    have h2 := hcur P hP r hr
    have h3 : (1 - Γ * (b - a)) ^ 2 * ℓ' ≤ (1 - Γ * (b - a)) * ℓ' :=
      mul_le_mul_of_nonneg_right hsq hℓ'.le
    linarith
  refine ⟨hϱ, by linarith [hv.hΓ], fun u hu r hr => abs_sub_le_window (hW hu) (hW hr),
    by linarith, hs, hΩ, hctr, fun P hP => cflow_start hv.toStripField hw (hctrZ P hP) (hW hs),
    fun u hu r hr => ?_, fun P hP r hr y hy => ?_, fun P hP u hu r hr y hy => ?_,
    fun P hP u hu w hw' r hr y hy => ?_⟩
  · -- holomorphy
    intro q hq
    have hd := (hasFDerivAt_cflow hv hw (hW hr) (hW hu) (hU q.1 hq.1 r hr q.2 hq.2)).differentiableAt
    exact (hd.comp q differentiableAt_snd).differentiableWithinAt
  · -- the identity at equal times
    exact cflow_start hv.toStripField hw (U0_subset_Z0 (hU P hP r hr y hy)) (hW hr)
  · -- the Jacobian
    have hd := hasFDerivAt_cflow hv hw (hW hr) (hW hu) (hU P hP r hr y hy)
    show ‖fderiv ℂ (fun y => cflow v ℓ' u y r) y - ContinuousLinearMap.id ℂ CVec‖ ≤ _
    rw [hd.fderiv]
    exact norm_cjac_sub_one_le hv hw (hU P hP r hr y hy) (hW hr) (hW hu)
  · -- the group law
    exact cflow_group hv.toStripField hw
      (hball P hP r hr y (ball_subset_ball (by linarith) hy)) (hW hr) (hW hw') (hW hu)

end CFam

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The child of a complex family**, in offset-flow form. With the time integral
`I(u, r) = ∫_r^u p_{k,p}` of the pulse (`pInt`), the child of level `k` with anchor `s'`, center
`c_P` and phase `ζ_P` of a family `(𝔛, x, s)` has the offset flow
`𝔛'(u, y, r) = 𝔛(u, w + I(u, r) 𝐮_{k,p}(w - (x + c) + ε_k ζ), s)`, `w = 𝔛(s, y, r)`,
and the center `x' = 𝔛(s', x + c, s)` (`CFam.child`). It is the complex child geometry
`childGeomC` (`child_eq_childGeomC`), since `ε_k d_k(u; r, θ) = I(u, r) 𝐮_{k,p}(ε_k θ)`.
`pInt_add`: the time integrals are additive. -/

section
/-- The time integral `I(u, r) = ∫_r^u p_{k,p}` of the pulse `p` of level `k`. -/
def pInt (D : OCData) (k : ℕ) (pk : ℤ) (u r : ℝ) : ℝ :=
  ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v

theorem pInt_add (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (u v r : ℝ) :
    pInt D k pk u v + pInt D k pk v r = pInt D k pk u r := by
  unfold pInt
  rw [add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuous_ocPulse D hζ k pk).intervalIntegrable _ _)
    ((continuous_ocPulse D hζ k pk).intervalIntegrable _ _)

theorem pInt_same (D : OCData) (k : ℕ) (pk : ℤ) (u : ℝ) : pInt D k pk u u = 0 := by
  simp [pInt]

theorem abs_pInt_le (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (u r : ℝ) :
    |pInt D k pk u r| ≤ |u - r| :=
  abs_integral_pulse_le D hζ k pk u r

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **The child of a complex family.** -/
def child (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ) (cc ph : Par → CVec) (F : CFam Par) :
    CFam Par where
  fl P u y r := F.fl P u (F.fl P F.anc y r + ((pInt D k pk u r : ℝ) : ℂ) •
    ocShearVelC D.α D.q D.Λ k pk (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P)) F.anc
  ctr P := F.fl P s' (F.ctr P + cc P) F.anc
  anc := s'

omit [NormedAddCommGroup Par] [NormedSpace ℂ Par] in
/-- **The child is the complex child geometry.** -/
theorem child_eq_childGeomC (D : OCData) {k : ℕ} (hε : D.eps k ≠ 0) (pk : ℤ) (s' : ℝ)
    (cc ph : Par → CVec) (F : CFam Par) (P : Par) :
    childGeomC D k pk s' (cc P, ph P) (F.fl P, F.ctr P, F.anc) =
      ((F.child D k pk s' cc ph).fl P, (F.child D k pk s' cc ph).ctr P,
        (F.child D k pk s' cc ph).anc) := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext u y r
  show F.fl P u (F.fl P F.anc y r + epsC D k • relDispC D k pk u r
      (epsInvC D k • F.fl P F.anc y r + (ph P - epsInvC D k • (F.ctr P + cc P)))) F.anc = _
  congr 2
  unfold relDispC epsC epsInvC
  rw [smul_smul, ← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  congr 2
  rw [smul_add, smul_sub, smul_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hε,
    Complex.ofReal_one, one_smul, one_smul]
  abel

end CFam
end

/-! **The invariants pass from a family to its child** (in the offset-flow form). For a family `F`
with the invariants `F.OK Ω W ϱ Λ T`, a child of level `k` with anchor `s'`, holomorphic center
`c_P` and phase `ζ_P` satisfies `OK Ω W' ϱ' Λ' T'` (`CFam.ChildHyp.ok`) with
`Λ' = Λ + L (4ΛT/ϱ) M + L² M'`, `L = 1 + ΛT`,
where `M, M'` bound the shear velocity and its derivative on the transverse strip of width `σ`
reached by the shear argument, under the smallness conditions `ChildHyp` of the radii. The
transported child center is `c'_P(r) = 𝔛(r, x + c + I(r,s') 𝐮(ε_k ζ), s)` (`cur_child`); the child
group law is the parent group law with the additivity of the time integrals and the transverse
invariance of the shear (`group_child`); the two-time Jacobian bound uses the parent group law,
the Cauchy bound on `D²𝔛` and the derivative of the shear (`jac_child`). -/

section
namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **The hypotheses of the child step.** -/
structure ChildHyp (D : OCData) (F : CFam Par) (Ω : Set Par) (W W' : Set ℝ) (ϱ Λ T : ℝ) (k : ℕ)
    (pk : ℤ) (s' : ℝ) (cc ph : Par → CVec) (ϱ' T' Bc Bph σ Ms Ms' : ℝ) : Prop where
  hF : F.OK Ω W ϱ Λ T
  hζ : IsFastProfile D.ζ
  hε : 0 < D.eps k
  hcc : DifferentiableOn ℂ cc Ω
  hph : DifferentiableOn ℂ ph Ω
  hW' : W' ⊆ W
  hs' : s' ∈ W'
  hT' : ∀ u ∈ W', ∀ r ∈ W', |u - r| ≤ T'
  hϱ' : 0 < ϱ'
  hBc0 : 0 ≤ Bc
  hBph0 : 0 ≤ Bph
  hMs0 : 0 ≤ Ms
  hMs'0 : 0 ≤ Ms'
  hBc : ∀ P ∈ Ω, ‖cc P‖ ≤ Bc
  hBph : ∀ P ∈ Ω, |((ph P) (transverseIndex pk)).im| ≤ Bph
  hMs : ∀ w : CVec, |(w (transverseIndex pk)).im| ≤ σ → ‖ocShearVelC D.α D.q D.Λ k pk w‖ ≤ Ms
  hMs' : ∀ w : CVec, |(w (transverseIndex pk)).im| ≤ σ →
    ‖fderiv ℂ (ocShearVelC D.α D.q D.Λ k pk) w‖ ≤ Ms'
  hσ : (1 + Λ * T) * ϱ' + T' * Ms + D.eps k * Bph ≤ σ
  hRa : ϱ' + (1 + Λ * T) * (Bc + T' * Ms) < ϱ / 4
  hRb : Bc + (1 + Λ * T) * ϱ' + 2 * (T' * Ms) < ϱ / 4
  hΛT' : (Λ + (1 + Λ * T) * (4 * (Λ * T) / ϱ) * Ms + (1 + Λ * T) ^ 2 * Ms') * T' ≤ 1 / 2

namespace ChildHyp

variable {D : OCData} {F : CFam Par} {Ω : Set Par} {W W' : Set ℝ} {ϱ Λ T : ℝ} {k : ℕ} {pk : ℤ}
  {s' : ℝ} {cc ph : Par → CVec} {ϱ' T' Bc Bph σ Ms Ms' : ℝ}

/-- The shear velocity of the child. -/
abbrev Sh (D : OCData) (k : ℕ) (pk : ℤ) : CVec → CVec := ocShearVelC D.α D.q D.Λ k pk

/-- The point `x + c + I(r, s') 𝐮(ε_k ζ)` whose transport is the child center at `r`. -/
def Zc (D : OCData) (F : CFam Par) (k : ℕ) (pk : ℤ) (s' : ℝ) (cc ph : Par → CVec) (P : Par)
    (r : ℝ) : CVec :=
  F.ctr P + cc P + ((pInt D k pk r s' : ℝ) : ℂ) • Sh D k pk (epsC D k • ph P)

section

variable (h : ChildHyp D F Ω W W' ϱ Λ T k pk s' cc ph ϱ' T' Bc Bph σ Ms Ms')
include h

theorem hL0 : 0 ≤ Λ * T := mul_nonneg h.hF.hΛ h.hF.hT0

theorem hLT : (1 + Λ * T) ≤ 3 / 2 := by linarith [h.hF.hΛT]

theorem mem_W {u : ℝ} (hu : u ∈ W') : u ∈ W := h.hW' hu

theorem hT'0 : 0 ≤ T' := (abs_nonneg _).trans (h.hT' s' h.hs' s' h.hs')

theorem abs_pInt_le_T {u r : ℝ} (hu : u ∈ W') (hr : r ∈ W') : |pInt D k pk u r| ≤ T' :=
  (abs_pInt_le D h.hζ k pk u r).trans (h.hT' u hu r hr)

theorem im_epsph_le {P : Par} (hP : P ∈ Ω) :
    |((epsC D k • ph P) (transverseIndex pk)).im| ≤ D.eps k * Bph := by
  rw [Pi.smul_apply, epsC, smul_eq_mul, Complex.im_ofReal_mul, abs_mul, abs_of_pos h.hε]
  exact mul_le_mul_of_nonneg_left (h.hBph P hP) h.hε.le

theorem Ms_epsph {P : Par} (hP : P ∈ Ω) : ‖Sh D k pk (epsC D k • ph P)‖ ≤ Ms := by
  refine h.hMs _ ((h.im_epsph_le hP).trans ?_)
  have := h.hσ
  have : 0 ≤ (1 + Λ * T) * ϱ' := mul_nonneg (by linarith [h.hL0]) h.hϱ'.le
  nlinarith [h.hMs0, h.hT'0]

theorem norm_smul_Sh_le {u r : ℝ} (hu : u ∈ W') (hr : r ∈ W') {w : CVec}
    (hw : |(w (transverseIndex pk)).im| ≤ σ) :
    ‖((pInt D k pk u r : ℝ) : ℂ) • Sh D k pk w‖ ≤ T' * Ms := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (h.abs_pInt_le_T hu hr) (h.hMs w hw) (norm_nonneg _) h.hT'0

theorem cc_lt {P : Par} (hP : P ∈ Ω) : ‖cc P‖ < ϱ / 4 := by
  have := h.hRa
  have : 0 ≤ (1 + Λ * T) * (Bc + T' * Ms) := mul_nonneg (by linarith [h.hL0])
    (add_nonneg h.hBc0 (mul_nonneg h.hT'0 h.hMs0))
  have : 0 < ϱ' := h.hϱ'
  have := h.hBc P hP
  have : Bc ≤ (1 + Λ * T) * (Bc + T' * Ms) := by
    have e : (1 + Λ * T) * (Bc + T' * Ms) = Bc + ((Λ * T) * Bc + (1 + Λ * T) * (T' * Ms)) := by ring
    rw [e]
    have := mul_nonneg h.hL0 h.hBc0
    have := mul_nonneg (by linarith [h.hL0] : (0 : ℝ) ≤ 1 + Λ * T) (mul_nonneg h.hT'0 h.hMs0)
    linarith
  linarith

theorem norm_Zc_sub_le {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') :
    ‖Zc D F k pk s' cc ph P r - F.ctr P‖ ≤ Bc + T' * Ms := by
  have e : Zc D F k pk s' cc ph P r - F.ctr P =
      cc P + ((pInt D k pk r s' : ℝ) : ℂ) • Sh D k pk (epsC D k • ph P) := by
    unfold Zc; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (h.hBc P hP) ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (h.abs_pInt_le_T hr h.hs') (h.Ms_epsph hP) (norm_nonneg _) h.hT'0

theorem Zc_mem {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') :
    Zc D F k pk s' cc ph P r ∈ ball (F.cur P F.anc) (ϱ / 4) := by
  rw [h.hF.cur_anc P hP, mem_ball, dist_eq_norm]
  refine (h.norm_Zc_sub_le hP hr).trans_lt ?_
  have := h.hRb
  have : 0 ≤ (1 + Λ * T) * ϱ' := mul_nonneg (by linarith [h.hL0]) h.hϱ'.le
  nlinarith [h.hT'0, h.hMs0]

theorem ctr_add_mem {P : Par} (hP : P ∈ Ω) : F.ctr P + cc P ∈ ball (F.cur P F.anc) (ϱ / 4) := by
  rw [h.hF.cur_anc P hP, mem_ball, dist_eq_norm, add_sub_cancel_left]
  exact h.cc_lt hP

/-- **The transported child center.** -/
theorem cur_child {P : Par} (hP : P ∈ Ω) (r : ℝ) :
    (F.child D k pk s' cc ph).cur P r = F.fl P r (Zc D F k pk s' cc ph P r) F.anc := by
  have hs := h.hF.anc_mem
  have hs'W := h.mem_W h.hs'
  -- `𝔛(s, x', s') = x + c`
  have h1 : F.fl P F.anc (F.fl P s' (F.ctr P + cc P) F.anc) s' = F.ctr P + cc P := by
    rw [h.hF.group P hP F.anc hs s' hs'W F.anc hs _ (h.ctr_add_mem hP)]
    exact h.hF.init P hP F.anc hs _ (ball_subset_ball (by linarith [h.hF.hϱ]) (h.ctr_add_mem hP))
  show F.fl P r (F.fl P F.anc (F.fl P s' (F.ctr P + cc P) F.anc) s' +
    ((pInt D k pk r s' : ℝ) : ℂ) • ocShearVelC D.α D.q D.Λ k pk
      (F.fl P F.anc (F.fl P s' (F.ctr P + cc P) F.anc) s' - (F.ctr P + cc P) +
        epsC D k • ph P)) F.anc = _
  rw [h1, sub_self, zero_add]
  rfl

/-- Points of the child ball lie in the parent quarter ball. -/
theorem mem_parent {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') : y ∈ ball (F.cur P r) (ϱ / 4) := by
  have hs := h.hF.anc_mem
  have hrW := h.mem_W hr
  rw [h.cur_child hP r] at hy
  have hZ : Zc D F k pk s' cc ph P r ∈ ball (F.cur P F.anc) ϱ :=
    ball_subset_ball (by linarith [h.hF.hϱ]) (h.Zc_mem hP hr)
  have hx : F.ctr P ∈ ball (F.cur P F.anc) ϱ := by
    rw [h.hF.cur_anc P hP]; exact mem_ball_self h.hF.hϱ
  have h1 := h.hF.norm_fl_sub_le hP hrW hs hZ hx
  rw [mem_ball, dist_eq_norm] at hy ⊢
  have h2 := h.norm_Zc_sub_le hP hr
  calc ‖y - F.cur P r‖ = ‖(y - F.fl P r (Zc D F k pk s' cc ph P r) F.anc) +
        (F.fl P r (Zc D F k pk s' cc ph P r) F.anc - F.fl P r (F.ctr P) F.anc)‖ := by
        unfold CFam.cur; congr 1; abel
    _ ≤ ‖y - F.fl P r (Zc D F k pk s' cc ph P r) F.anc‖ +
        ‖F.fl P r (Zc D F k pk s' cc ph P r) F.anc - F.fl P r (F.ctr P) F.anc‖ := norm_add_le _ _
    _ < ϱ' + (1 + Λ * T) * (Bc + T' * Ms) := by
        refine add_lt_add_of_lt_of_le hy (h1.trans ?_)
        exact mul_le_mul_of_nonneg_left h2 (by linarith [h.hL0])
    _ < ϱ / 4 := h.hRa

/-- The parent maps the child center at `r` back to `Zc`. -/
theorem fl_cur_child {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') :
    F.fl P F.anc ((F.child D k pk s' cc ph).cur P r) r = Zc D F k pk s' cc ph P r := by
  have hs := h.hF.anc_mem
  rw [h.cur_child hP r, h.hF.group P hP F.anc hs r (h.mem_W hr) F.anc hs _ (h.Zc_mem hP hr)]
  exact h.hF.init P hP F.anc hs _ (ball_subset_ball (by linarith [h.hF.hϱ]) (h.Zc_mem hP hr))

/-- `‖𝔛(s, y, r) - Zc‖ ≤ L ϱ'` on the child ball. -/
theorem norm_w_sub_le {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    ‖F.fl P F.anc y r - Zc D F k pk s' cc ph P r‖ ≤ (1 + Λ * T) * ϱ' := by
  have hs := h.hF.anc_mem
  have hrW := h.mem_W hr
  have hc : (F.child D k pk s' cc ph).cur P r ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ' :=
    mem_ball_self h.hϱ'
  have hy1 : y ∈ ball (F.cur P r) ϱ :=
    ball_subset_ball (by linarith [h.hF.hϱ]) (h.mem_parent hP hr hy)
  have hc1 : (F.child D k pk s' cc ph).cur P r ∈ ball (F.cur P r) ϱ :=
    ball_subset_ball (by linarith [h.hF.hϱ]) (h.mem_parent hP hr hc)
  rw [← h.fl_cur_child hP hr]
  refine (h.hF.norm_fl_sub_le hP hs hrW hy1 hc1).trans ?_
  rw [mem_ball, dist_eq_norm] at hy
  exact mul_le_mul_of_nonneg_left hy.le (by linarith [h.hL0])

/-- The shear argument stays in the transverse strip of width `σ`. -/
theorem im_arg_le {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    |((F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P) (transverseIndex pk)).im| ≤ σ := by
  have h1 := h.norm_w_sub_le hP hr hy
  have hS := h.norm_smul_Sh_le hr h.hs' (w := epsC D k • ph P)
    ((h.im_epsph_le hP).trans (by
      have := h.hσ
      have : 0 ≤ (1 + Λ * T) * ϱ' := mul_nonneg (by linarith [h.hL0]) h.hϱ'.le
      nlinarith [h.hMs0, h.hT'0]))
  have e : F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P =
      (F.fl P F.anc y r - Zc D F k pk s' cc ph P r) +
        ((pInt D k pk r s' : ℝ) : ℂ) • Sh D k pk (epsC D k • ph P) + epsC D k • ph P := by
    unfold Zc; abel
  rw [e]
  have hcoord : ∀ w : CVec, |(w (transverseIndex pk)).im| ≤ ‖w‖ := fun w =>
    (Complex.abs_im_le_norm _).trans (norm_le_pi_norm w _)
  calc |(((F.fl P F.anc y r - Zc D F k pk s' cc ph P r) +
        ((pInt D k pk r s' : ℝ) : ℂ) • Sh D k pk (epsC D k • ph P) + epsC D k • ph P)
          (transverseIndex pk)).im|
      ≤ ‖(F.fl P F.anc y r - Zc D F k pk s' cc ph P r) +
          ((pInt D k pk r s' : ℝ) : ℂ) • Sh D k pk (epsC D k • ph P)‖ +
        |((epsC D k • ph P) (transverseIndex pk)).im| := by
        rw [Pi.add_apply, Complex.add_im]
        exact (abs_add_le _ _).trans (add_le_add (hcoord _) le_rfl)
    _ ≤ ((1 + Λ * T) * ϱ' + T' * Ms) + D.eps k * Bph :=
        add_le_add ((norm_add_le _ _).trans (add_le_add h1 hS)) (h.im_epsph_le hP)
    _ ≤ σ := h.hσ

/-- The point fed to the parent flow at the time `u` stays in the parent quarter ball at `s`. -/
theorem Zu_mem {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W') (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    F.fl P F.anc y r + ((pInt D k pk u r : ℝ) : ℂ) •
        Sh D k pk (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P) ∈
      ball (F.cur P F.anc) (ϱ / 4) := by
  rw [h.hF.cur_anc P hP, mem_ball, dist_eq_norm]
  have h1 := h.norm_w_sub_le hP hr hy
  have h2 := h.norm_Zc_sub_le hP hr
  have h3 := h.norm_smul_Sh_le hu hr (h.im_arg_le hP hr hy)
  calc ‖F.fl P F.anc y r + ((pInt D k pk u r : ℝ) : ℂ) •
        Sh D k pk (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P) - F.ctr P‖
      = ‖(F.fl P F.anc y r - Zc D F k pk s' cc ph P r) + (Zc D F k pk s' cc ph P r - F.ctr P) +
          ((pInt D k pk u r : ℝ) : ℂ) •
            Sh D k pk (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P)‖ := by
        congr 1; abel
    _ ≤ (1 + Λ * T) * ϱ' + (Bc + T' * Ms) + T' * Ms :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
    _ < ϱ / 4 := by linarith [h.hRb]

/-- The parent maps the child ball into its quarter ball at `s`. -/
theorem w_mem {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    F.fl P F.anc y r ∈ ball (F.cur P F.anc) (ϱ / 4) := by
  rw [h.hF.cur_anc P hP, mem_ball, dist_eq_norm]
  have h1 := h.norm_w_sub_le hP hr hy
  have h2 := h.norm_Zc_sub_le hP hr
  calc ‖F.fl P F.anc y r - F.ctr P‖ = ‖(F.fl P F.anc y r - Zc D F k pk s' cc ph P r) +
        (Zc D F k pk s' cc ph P r - F.ctr P)‖ := by congr 1; abel
    _ ≤ (1 + Λ * T) * ϱ' + (Bc + T' * Ms) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ < ϱ / 4 := by nlinarith [h.hRb, h.hT'0, h.hMs0]

theorem ctr_hol_child : DifferentiableOn ℂ (F.child D k pk s' cc ph).ctr Ω := by
  have hmaps : MapsTo (fun P => (P, F.ctr P + cc P)) Ω (F.dom Ω ϱ F.anc) := fun P hP =>
    ⟨hP, ball_subset_ball (by linarith [h.hF.hϱ]) (h.ctr_add_mem hP)⟩
  exact (h.hF.hol s' (h.mem_W h.hs') F.anc h.hF.anc_mem).comp
    (differentiableOn_id.prodMk (h.hF.ctr_hol.add h.hcc)) hmaps

theorem cur_anc_child {P : Par} (hP : P ∈ Ω) :
    (F.child D k pk s' cc ph).cur P s' = (F.child D k pk s' cc ph).ctr P := by
  rw [h.cur_child hP s']
  show F.fl P s' (F.ctr P + cc P + ((pInt D k pk s' s' : ℝ) : ℂ) •
    Sh D k pk (epsC D k • ph P)) F.anc = F.fl P s' (F.ctr P + cc P) F.anc
  rw [pInt_same, Complex.ofReal_zero, zero_smul, add_zero]

theorem init_child {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    (F.child D k pk s' cc ph).fl P r y r = y := by
  have hs := h.hF.anc_mem
  have hrW := h.mem_W hr
  have hy4 := h.mem_parent hP hr hy
  show F.fl P r (F.fl P F.anc y r + ((pInt D k pk r r : ℝ) : ℂ) •
    Sh D k pk (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P)) F.anc = y
  rw [pInt_same, Complex.ofReal_zero, zero_smul, add_zero, h.hF.group P hP r hrW F.anc hs r hrW y hy4]
  exact h.hF.init P hP r hrW y (ball_subset_ball (by linarith [h.hF.hϱ]) hy4)

/-- **The group law of the child.** -/
theorem group_child {P : Par} (hP : P ∈ Ω) {u v r : ℝ} (hv : v ∈ W') (hr : r ∈ W')
    {y : CVec} (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    (F.child D k pk s' cc ph).fl P u ((F.child D k pk s' cc ph).fl P v y r) v =
      (F.child D k pk s' cc ph).fl P u y r := by
  have hs := h.hF.anc_mem
  set w := F.fl P F.anc y r with hw
  set a := w - (F.ctr P + cc P) + epsC D k • ph P with ha
  set Zv := w + ((pInt D k pk v r : ℝ) : ℂ) • Sh D k pk a with hZv
  have hZvm : Zv ∈ ball (F.cur P F.anc) (ϱ / 4) := h.Zu_mem hP hv hr hy
  -- the parent maps the point at `v` back to `Zv`
  have hw' : F.fl P F.anc (F.fl P v Zv F.anc) v = Zv := by
    rw [h.hF.group P hP F.anc hs v (h.mem_W hv) F.anc hs Zv hZvm]
    exact h.hF.init P hP F.anc hs Zv (ball_subset_ball (by linarith [h.hF.hϱ]) hZvm)
  -- the shear argument moves parallel to the pulse
  have ha' : Zv - (F.ctr P + cc P) + epsC D k • ph P = a + ((pInt D k pk v r : ℝ) : ℂ) • Sh D k pk a := by
    rw [hZv, ha]; abel
  have hSa : Sh D k pk (a + ((pInt D k pk v r : ℝ) : ℂ) • Sh D k pk a) = Sh D k pk a := by
    refine ocShearVelC_add_of_transverse _ _ _ _ _ _ _ ?_
    rw [Pi.smul_apply, show Sh D k pk a (transverseIndex pk) = 0 from
      ocShearVelC_transverse _ _ _ _ _ _, smul_zero]
  show F.fl P u (F.fl P F.anc (F.fl P v Zv F.anc) v + ((pInt D k pk u v : ℝ) : ℂ) •
      Sh D k pk (F.fl P F.anc (F.fl P v Zv F.anc) v - (F.ctr P + cc P) + epsC D k • ph P)) F.anc =
    F.fl P u (w + ((pInt D k pk u r : ℝ) : ℂ) • Sh D k pk a) F.anc
  rw [hw', ha', hSa, hZv, add_assoc, ← add_smul, ← Complex.ofReal_add, add_comm (pInt D k pk v r),
    pInt_add D h.hζ k pk u v r]

theorem dom_child_subset {r : ℝ} (hr : r ∈ W') :
    (F.child D k pk s' cc ph).dom Ω ϱ' r ⊆ F.dom Ω ϱ r := fun q hq =>
  ⟨hq.1, ball_subset_ball (by linarith [h.hF.hϱ]) (h.mem_parent hq.1 hr hq.2)⟩

/-- **The child is holomorphic in the parameters and the point.** -/
theorem hol_child {u r : ℝ} (hu : u ∈ W') (hr : r ∈ W') :
    DifferentiableOn ℂ (fun q : Par × CVec => (F.child D k pk s' cc ph).fl q.1 u q.2 r)
      ((F.child D k pk s' cc ph).dom Ω ϱ' r) := by
  have hs := h.hF.anc_mem
  have hrW := h.mem_W hr
  set Dm := (F.child D k pk s' cc ph).dom Ω ϱ' r
  have h1 : DifferentiableOn ℂ (fun q : Par × CVec => F.fl q.1 F.anc q.2 r) Dm :=
    (h.hF.hol F.anc hs r hrW).mono (h.dom_child_subset hr)
  have hfst : MapsTo (fun q : Par × CVec => q.1) Dm Ω := fun q hq => hq.1
  have hctr : DifferentiableOn ℂ (fun q : Par × CVec => F.ctr q.1) Dm :=
    h.hF.ctr_hol.comp differentiableOn_fst hfst
  have hccq : DifferentiableOn ℂ (fun q : Par × CVec => cc q.1) Dm :=
    h.hcc.comp differentiableOn_fst hfst
  have hphq : DifferentiableOn ℂ (fun q : Par × CVec => ph q.1) Dm :=
    h.hph.comp differentiableOn_fst hfst
  have hphs : DifferentiableOn ℂ (fun q : Par × CVec => epsC D k • ph q.1) Dm :=
    hphq.const_smul (epsC D k)
  have harg : DifferentiableOn ℂ (fun q : Par × CVec =>
      F.fl q.1 F.anc q.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1) Dm :=
    (h1.sub (hctr.add hccq)).add hphs
  have hSq : DifferentiableOn ℂ (fun q : Par × CVec => ((pInt D k pk u r : ℝ) : ℂ) • Sh D k pk
      (F.fl q.1 F.anc q.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1)) Dm := by
    have h3 := ((differentiable_ocShearVelC D.α D.q D.Λ k pk).comp_differentiableOn harg).const_smul
      (((pInt D k pk u r : ℝ) : ℂ))
    exact h3
  have hZ : DifferentiableOn ℂ (fun q : Par × CVec => F.fl q.1 F.anc q.2 r +
      ((pInt D k pk u r : ℝ) : ℂ) • Sh D k pk
        (F.fl q.1 F.anc q.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1)) Dm :=
    h1.add hSq
  have hmaps : MapsTo (fun q : Par × CVec => (q.1, F.fl q.1 F.anc q.2 r +
      ((pInt D k pk u r : ℝ) : ℂ) • Sh D k pk
        (F.fl q.1 F.anc q.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1))) Dm
      (F.dom Ω ϱ F.anc) := fun q hq =>
    ⟨hq.1, ball_subset_ball (by linarith [h.hF.hϱ]) (h.Zu_mem hq.1 hu hr hq.2)⟩
  exact (h.hF.hol u (h.mem_W hu) F.anc hs).comp (differentiableOn_fst.prodMk hZ) hmaps

/-- **The two-time Jacobian bound of the child.** -/
theorem jac_child {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W') (hr : r ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P r) ϱ') :
    ‖fderiv ℂ (fun y => (F.child D k pk s' cc ph).fl P u y r) y - ContinuousLinearMap.id ℂ CVec‖ ≤
      (Λ + (1 + Λ * T) * (4 * (Λ * T) / ϱ) * Ms + (1 + Λ * T) ^ 2 * Ms') * |u - r| := by
  have hs := h.hF.anc_mem
  have hrW := h.mem_W hr
  have huW := h.mem_W hu
  have hϱ := h.hF.hϱ
  have hL0 := h.hL0
  have hy4 := h.mem_parent hP hr hy
  have hy1 : y ∈ ball (F.cur P r) ϱ := ball_subset_ball (by linarith) hy4
  set c : ℂ := ((pInt D k pk u r : ℝ) : ℂ) with hc
  set w := F.fl P F.anc y r with hw
  set a := w - (F.ctr P + cc P) + epsC D k • ph P with ha
  set Z := w + c • Sh D k pk a with hZ
  have hwm : w ∈ ball (F.cur P F.anc) (ϱ / 4) := h.w_mem hP hr hy
  have hZm : Z ∈ ball (F.cur P F.anc) (ϱ / 4) := h.Zu_mem hP hu hr hy
  have hw1 : w ∈ ball (F.cur P F.anc) ϱ := ball_subset_ball (by linarith) hwm
  have hZ1 : Z ∈ ball (F.cur P F.anc) ϱ := ball_subset_ball (by linarith) hZm
  -- the derivatives
  set DXs := fderiv ℂ (fun y => F.fl P F.anc y r) y
  set DXu := fderiv ℂ (fun z => F.fl P u z F.anc) Z
  set DXw := fderiv ℂ (fun z => F.fl P u z F.anc) w
  set DS := fderiv ℂ (Sh D k pk) a
  have hXs : HasFDerivAt (fun y => F.fl P F.anc y r) DXs y :=
    (h.hF.differentiableAt_fl hP hs hrW hy1).hasFDerivAt
  have hXu : HasFDerivAt (fun z => F.fl P u z F.anc) DXu Z :=
    (h.hF.differentiableAt_fl hP huW hs hZ1).hasFDerivAt
  have hXw : HasFDerivAt (fun z => F.fl P u z F.anc) DXw w :=
    (h.hF.differentiableAt_fl hP huW hs hw1).hasFDerivAt
  have hSd : HasFDerivAt (Sh D k pk) DS a :=
    ((differentiable_ocShearVelC _ _ _ _ _) a).hasFDerivAt
  have hA : HasFDerivAt (fun y => F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P) DXs y :=
    (hXs.sub_const _).add_const _
  have hZd : HasFDerivAt (fun y => F.fl P F.anc y r + c • Sh D k pk
      (F.fl P F.anc y r - (F.ctr P + cc P) + epsC D k • ph P)) (DXs + c • DS.comp DXs) y :=
    hXs.add ((hSd.comp y hA).const_smul c)
  have hg : HasFDerivAt (fun y => (F.child D k pk s' cc ph).fl P u y r)
      (DXu.comp (DXs + c • DS.comp DXs)) y := by
    have h' := hXu.comp y hZd
    exact h'
  -- the group law identifies `DXw ∘ DXs` with the parent Jacobian from `r`
  have hgrp : fderiv ℂ (fun y => F.fl P u y r) y = DXw.comp DXs := by
    have h2 : HasFDerivAt (fun y => F.fl P u (F.fl P F.anc y r) F.anc) (DXw.comp DXs) y := by
      have h' := hXw.comp y hXs
      exact h'
    have he : (fun y => F.fl P u (F.fl P F.anc y r) F.anc) =ᶠ[𝓝 y] fun y => F.fl P u y r := by
      filter_upwards [isOpen_ball.mem_nhds hy4] with y' hy'
      exact h.hF.group P hP u huW F.anc hs r hrW y' hy'
    exact (h2.congr_of_eventuallyEq he.symm).fderiv
  have hJ := h.hF.jac P hP u huW r hrW y hy1
  rw [hgrp] at hJ
  rw [hg.fderiv]
  -- the decomposition
  have key : DXu.comp (DXs + c • DS.comp DXs) - ContinuousLinearMap.id ℂ CVec =
      (DXu - DXw).comp DXs + (DXw.comp DXs - ContinuousLinearMap.id ℂ CVec) +
        c • DXu.comp (DS.comp DXs) := by
    ext v : 1
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply, map_add,
      map_smul]
    abel
  rw [key]
  -- the bounds
  have hT := h.hF.hT
  have hur : |u - r| ≤ T := hT u huW r hrW
  have hsr : |F.anc - r| ≤ T := hT F.anc hs r hrW
  have hus : |u - F.anc| ≤ T := hT u huW F.anc hs
  have hnorm1 : ‖ContinuousLinearMap.id ℂ CVec‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hDXs : ‖DXs‖ ≤ 1 + Λ * T := by
    have := h.hF.jac P hP F.anc hs r hrW y hy1
    calc ‖DXs‖ = ‖(DXs - ContinuousLinearMap.id ℂ CVec) + ContinuousLinearMap.id ℂ CVec‖ := by
          rw [sub_add_cancel]
      _ ≤ Λ * |F.anc - r| + 1 := (norm_add_le _ _).trans (add_le_add this hnorm1)
      _ ≤ 1 + Λ * T := by nlinarith [h.hF.hΛ]
  have hDXu : ‖DXu‖ ≤ 1 + Λ * T := by
    have := h.hF.jac P hP u huW F.anc hs Z hZ1
    calc ‖DXu‖ = ‖(DXu - ContinuousLinearMap.id ℂ CVec) + ContinuousLinearMap.id ℂ CVec‖ := by
          rw [sub_add_cancel]
      _ ≤ Λ * |u - F.anc| + 1 := (norm_add_le _ _).trans (add_le_add this hnorm1)
      _ ≤ 1 + Λ * T := by nlinarith [h.hF.hΛ]
  have hDS : ‖DS‖ ≤ Ms' := h.hMs' a (h.im_arg_le hP hr hy)
  have hcn : ‖c‖ ≤ |u - r| := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
    exact abs_pInt_le D h.hζ k pk u r
  have hZw : ‖Z - w‖ ≤ |u - r| * Ms := by
    rw [hZ, add_sub_cancel_left, norm_smul]
    exact mul_le_mul hcn (h.hMs a (h.im_arg_le hP hr hy)) (norm_nonneg _) (abs_nonneg _)
  have hDXuw : ‖DXu - DXw‖ ≤ 4 * (Λ * T) / ϱ * (|u - r| * Ms) :=
    (h.hF.norm_fderiv_fl_sub_le hP huW hs (ball_subset_ball (by linarith) hZm)
      (ball_subset_ball (by linarith) hwm)).trans
      (mul_le_mul_of_nonneg_left hZw (by positivity))
  have hL1 : 0 ≤ 1 + Λ * T := by linarith
  calc ‖(DXu - DXw).comp DXs + (DXw.comp DXs - ContinuousLinearMap.id ℂ CVec) +
        c • DXu.comp (DS.comp DXs)‖
      ≤ ‖DXu - DXw‖ * ‖DXs‖ + Λ * |u - r| + ‖c‖ * (‖DXu‖ * (‖DS‖ * ‖DXs‖)) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hJ)) ?_)
        rw [norm_smul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 4 * (Λ * T) / ϱ * (|u - r| * Ms) * (1 + Λ * T) + Λ * |u - r| +
          |u - r| * ((1 + Λ * T) * (Ms' * (1 + Λ * T))) := by
        refine add_le_add (add_le_add (mul_le_mul hDXuw hDXs (norm_nonneg _)
          (mul_nonneg (div_nonneg (by linarith) hϱ.le) (mul_nonneg (abs_nonneg _) h.hMs0)))
          le_rfl) (mul_le_mul hcn (mul_le_mul hDXu (mul_le_mul hDS hDXs (norm_nonneg _)
            h.hMs'0) (by positivity) hL1) (by positivity) (abs_nonneg _))
    _ = (Λ + (1 + Λ * T) * (4 * (Λ * T) / ϱ) * Ms + (1 + Λ * T) ^ 2 * Ms') * |u - r| := by ring

/-- **The invariants pass to the child.** -/
theorem ok : (F.child D k pk s' cc ph).OK Ω W' ϱ'
    (Λ + (1 + Λ * T) * (4 * (Λ * T) / ϱ) * Ms + (1 + Λ * T) ^ 2 * Ms') T' where
  hϱ := h.hϱ'
  hΛ := by
    have h4 : 0 ≤ 4 * (Λ * T) / ϱ := div_nonneg (by linarith [h.hL0]) h.hF.hϱ.le
    have hL1 : 0 ≤ 1 + Λ * T := by linarith [h.hL0]
    exact add_nonneg (add_nonneg h.hF.hΛ (mul_nonneg (mul_nonneg hL1 h4) h.hMs0))
      (mul_nonneg (sq_nonneg _) h.hMs'0)
  hT := h.hT'
  hΛT := h.hΛT'
  anc_mem := h.hs'
  hΩ := h.hF.hΩ
  ctr_hol := h.ctr_hol_child
  cur_anc := fun P hP => h.cur_anc_child hP
  hol := fun u hu r hr => h.hol_child hu hr
  init := fun P hP r hr y hy => h.init_child hP hr hy
  jac := fun P hP u hu r hr y hy => h.jac_child hP hu hr hy
  group := fun P hP u hu v hv r hr y hy =>
    h.group_child (u := u) hP hv hr (ball_subset_ball (by linarith [h.hϱ']) hy)

end

end ChildHyp

end CFam
end

/-! **Continuity of the families in the final time** (the maps are continuous in `u`). A family is
*time continuous* (`CFam.TimeCont`) if `(u, y) ↦ 𝔛_P(u, y, r)` is continuous on the window times the
ball around the transported center. The base family is (`baseFam_timeCont`, from the continuity of
the complex flow), and the property passes to the child (`ChildHyp.timeCont`): the child flow is the
parent flow at the time `u` of a point that depends continuously on `(u, y)` and stays in the parent
quarter ball. -/

section
namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **Joint continuity in the parameters, the final time and the point**, on the parameters
times the window times the balls around the transported centers. -/
def TimeCont (F : CFam Par) (Ω : Set Par) (W : Set ℝ) (ϱ : ℝ) : Prop :=
  ∀ r ∈ W, ContinuousOn (fun q : Par × ℝ × CVec => F.fl q.1 q.2.1 q.2.2 r)
    {q | q.1 ∈ Ω ∧ q.2.1 ∈ W ∧ q.2.2 ∈ ball (F.cur q.1 r) ϱ}

omit [NormedSpace ℂ Par] in
/-- The slice at fixed parameters. -/
theorem TimeCont.slice {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ : ℝ} (hc : F.TimeCont Ω W ϱ)
    {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W) :
    ContinuousOn (fun q : ℝ × CVec => F.fl P q.1 q.2 r) (W ×ˢ ball (F.cur P r) ϱ) :=
  (hc r hr).comp (continuous_const.prodMk continuous_id).continuousOn fun _ hq => ⟨hP, hq.1, hq.2⟩

variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

omit [NormedAddCommGroup Par] [NormedSpace ℂ Par] in
/-- The balls around the transported centers of the base family lie in the initial set. -/
theorem baseFam_ball_subset (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {W : Set ℝ}
    (hW : W ⊆ Icc a b) {ctr : Par → CVec} {Ω : Set Par} {B₀ ϱ : ℝ}
    (hB₀ : ∀ P ∈ Ω, imL1 (ctr P) ≤ B₀) (hϱ : 0 ≤ ϱ)
    (hdom : B₀ / (1 - Γ * (b - a)) + 2 * ϱ ≤ (1 - Γ * (b - a)) ^ 2 * ℓ') {s : ℝ} (hs : s ∈ W)
    {P : Par} (hP : P ∈ Ω) {r : ℝ} (hr : r ∈ W) :
    ball ((baseFam v ℓ' ctr s : CFam Par).cur P r) ϱ ⊆ Z0 ℓ' Γ a b := by
  have hr1 := ratio_lt_one hw
  have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hv.hΓ (sub_nonneg.mpr hw.hab)
  have h1r : 0 < 1 - Γ * (b - a) := by linarith
  have hℓ' := hw.hℓ'
  have hsq : (1 - Γ * (b - a)) ^ 2 ≤ 1 - Γ * (b - a) := by nlinarith
  have hB0 : 0 ≤ B₀ := (imL1_nonneg _).trans (hB₀ P hP)
  have h2 : (1 - Γ * (b - a)) ^ 2 * ℓ' ≤ (1 - Γ * (b - a)) * ℓ' :=
    mul_le_mul_of_nonneg_right hsq hℓ'.le
  have hctrZ : ctr P ∈ Z0 ℓ' Γ a b := by
    show imL1 (ctr P) ≤ (1 - Γ * (b - a)) * ℓ'
    have h1 : B₀ ≤ B₀ / (1 - Γ * (b - a)) := by
      rw [le_div_iff₀ h1r]; nlinarith
    linarith [hB₀ P hP]
  have hcur : imL1 ((baseFam v ℓ' ctr s : CFam Par).cur P r) ≤ B₀ / (1 - Γ * (b - a)) :=
    (imL1_cflow_le hv.toStripField hw hctrZ (hW hs) (hW hr)).trans
      (div_le_div_of_nonneg_right (hB₀ P hP) h1r.le)
  intro y hy
  show imL1 y ≤ (1 - Γ * (b - a)) * ℓ'
  have h1 := imL1_lt_of_mem_ball hy
  linarith

omit [NormedSpace ℂ Par] in
/-- **The base family is time continuous.** -/
theorem baseFam_timeCont (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {W : Set ℝ}
    (hW : W ⊆ Icc a b) {ctr : Par → CVec} {Ω : Set Par} {s ϱ : ℝ}
    (hU : ∀ P ∈ Ω, ∀ r ∈ W, ball ((baseFam v ℓ' ctr s : CFam Par).cur P r) ϱ ⊆ Z0 ℓ' Γ a b) :
    (baseFam v ℓ' ctr s : CFam Par).TimeCont Ω W ϱ := by
  intro r hr
  show ContinuousOn (fun q : Par × ℝ × CVec => cflow v ℓ' q.2.1 q.2.2 r)
    {q | q.1 ∈ Ω ∧ q.2.1 ∈ W ∧ q.2.2 ∈ ball ((baseFam v ℓ' ctr s : CFam Par).cur q.1 r) ϱ}
  have hg : Continuous fun q : Par × ℝ × CVec => ((q.2.1, q.2.2, r) : ℝ × CVec × ℝ) :=
    (continuous_fst.comp continuous_snd).prodMk ((continuous_snd.comp continuous_snd).prodMk
      continuous_const)
  have hmaps : MapsTo (fun q : Par × ℝ × CVec => ((q.2.1, q.2.2, r) : ℝ × CVec × ℝ))
      {q | q.1 ∈ Ω ∧ q.2.1 ∈ W ∧ q.2.2 ∈ ball ((baseFam v ℓ' ctr s : CFam Par).cur q.1 r) ϱ}
      (flowDom ℓ' Γ a b) :=
    fun q hq => ⟨hW hq.2.1, hU q.1 hq.1 r hr hq.2.2, hW hr⟩
  have h := (continuousOn_cflow hv.toStripField hw).comp hg.continuousOn hmaps
  exact h

namespace ChildHyp

variable {D : OCData} {F : CFam Par} {Ω : Set Par} {W W' : Set ℝ} {ϱ Λ T : ℝ} {k : ℕ} {pk : ℤ}
  {s' : ℝ} {cc ph : Par → CVec} {ϱ' T' Bc Bph σ Ms Ms' : ℝ}

/-- The point fed to the parent flow by the child flow. -/
def Zarg (D : OCData) (F : CFam Par) (k : ℕ) (pk : ℤ) (cc ph : Par → CVec) (r : ℝ)
    (q : Par × ℝ × CVec) : CVec :=
  F.fl q.1 F.anc q.2.2 r + ((pInt D k pk q.2.1 r : ℝ) : ℂ) •
    Sh D k pk (F.fl q.1 F.anc q.2.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1)

theorem continuousOn_Zarg_of {ϱ Λ T : ℝ} (hF : F.OK Ω W ϱ Λ T) (hζ : IsFastProfile D.ζ)
    (hcc : ContinuousOn cc Ω) (hph : ContinuousOn ph Ω) {r : ℝ} (hrW : r ∈ W)
    {S : Set (Par × ℝ × CVec)} (hS1 : ∀ q ∈ S, q.1 ∈ Ω)
    (hS2 : ∀ q ∈ S, q.2.2 ∈ ball (F.cur q.1 r) ϱ) :
    ContinuousOn (Zarg D F k pk cc ph r) S := by
  have hs := hF.anc_mem
  have hw0 : ContinuousOn (fun q : Par × CVec => F.fl q.1 F.anc q.2 r) (F.dom Ω ϱ r) :=
    (hF.hol F.anc hs r hrW).continuousOn
  have hmap : MapsTo (fun q : Par × ℝ × CVec => (q.1, q.2.2)) S (F.dom Ω ϱ r) :=
    fun q hq => ⟨hS1 q hq, hS2 q hq⟩
  have hw' : ContinuousOn (fun q : Par × ℝ × CVec => F.fl q.1 F.anc q.2.2 r) S :=
    hw0.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn hmap
  have hI : Continuous fun u : ℝ => ((pInt D k pk u r : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_ocPulse D hζ k pk).intervalIntegrable _ _) r)
  have hSh : Continuous (Sh D k pk) := (differentiable_ocShearVelC _ _ _ _ _).continuous
  have hP1 : MapsTo (fun q : Par × ℝ × CVec => q.1) S Ω := fun q hq => hS1 q hq
  have hctr : ContinuousOn (fun q : Par × ℝ × CVec => F.ctr q.1 + cc q.1) S :=
    (hF.ctr_hol.continuousOn.add hcc).comp continuous_fst.continuousOn hP1
  have hph' : ContinuousOn (fun q : Par × ℝ × CVec => epsC D k • ph q.1) S :=
    (hph.comp continuous_fst.continuousOn hP1).const_smul (epsC D k)
  have hin : ContinuousOn (fun q : Par × ℝ × CVec =>
      F.fl q.1 F.anc q.2.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1) S :=
    (hw'.sub hctr).add hph'
  have hsh : ContinuousOn (fun q : Par × ℝ × CVec => ((pInt D k pk q.2.1 r : ℝ) : ℂ) •
      Sh D k pk (F.fl q.1 F.anc q.2.2 r - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1)) S :=
    (hI.comp (continuous_fst.comp continuous_snd)).continuousOn.smul (hSh.comp_continuousOn hin)
  exact hw'.add hsh

theorem continuousOn_fl_Zarg {ϱ Λ T : ℝ} (hF : F.OK Ω W ϱ Λ T) (hc : F.TimeCont Ω W ϱ)
    {r : ℝ} {S : Set (Par × ℝ × CVec)} (hS1 : ∀ q ∈ S, q.1 ∈ Ω) (hS2 : ∀ q ∈ S, q.2.1 ∈ W)
    (hZ : ∀ q ∈ S, Zarg D F k pk cc ph r q ∈ ball (F.cur q.1 F.anc) ϱ)
    (hZc : ContinuousOn (Zarg D F k pk cc ph r) S) :
    ContinuousOn (fun q : Par × ℝ × CVec => F.fl q.1 q.2.1 (Zarg D F k pk cc ph r q) F.anc) S := by
  have hg : ContinuousOn (fun q : Par × ℝ × CVec => (q.1, q.2.1, Zarg D F k pk cc ph r q)) S :=
    continuous_fst.continuousOn.prodMk ((continuous_fst.comp continuous_snd).continuousOn.prodMk
      hZc)
  have hmaps : MapsTo (fun q : Par × ℝ × CVec => (q.1, q.2.1, Zarg D F k pk cc ph r q)) S
      {q | q.1 ∈ Ω ∧ q.2.1 ∈ W ∧ q.2.2 ∈ ball (F.cur q.1 F.anc) ϱ} := fun q hq =>
    ⟨hS1 q hq, hS2 q hq, hZ q hq⟩
  exact (hc F.anc hF.anc_mem).comp hg hmaps

/-- **Time continuity passes to the child.** -/
theorem timeCont (h : ChildHyp D F Ω W W' ϱ Λ T k pk s' cc ph ϱ' T' Bc Bph σ Ms Ms')
    (hc : F.TimeCont Ω W ϱ) : (F.child D k pk s' cc ph).TimeCont Ω W' ϱ' := by
  intro r hr
  have hS1 : ∀ q ∈ {q : Par × ℝ × CVec | q.1 ∈ Ω ∧ q.2.1 ∈ W' ∧
      q.2.2 ∈ ball ((F.child D k pk s' cc ph).cur q.1 r) ϱ'}, q.1 ∈ Ω := fun q hq => hq.1
  have hS2 : ∀ q ∈ {q : Par × ℝ × CVec | q.1 ∈ Ω ∧ q.2.1 ∈ W' ∧
      q.2.2 ∈ ball ((F.child D k pk s' cc ph).cur q.1 r) ϱ'}, q.2.2 ∈ ball (F.cur q.1 r) ϱ := by
    rintro q ⟨h1, _, h3⟩
    exact ball_subset_ball (by linarith [h.hF.hϱ]) (h.mem_parent h1 hr h3)
  have hZ : ∀ q ∈ {q : Par × ℝ × CVec | q.1 ∈ Ω ∧ q.2.1 ∈ W' ∧
      q.2.2 ∈ ball ((F.child D k pk s' cc ph).cur q.1 r) ϱ'},
      Zarg D F k pk cc ph r q ∈ ball (F.cur q.1 F.anc) ϱ := by
    rintro q ⟨h1, h2, h3⟩
    exact ball_subset_ball (by linarith [h.hF.hϱ]) (h.Zu_mem h1 h2 hr h3)
  have hW : ∀ q ∈ {q : Par × ℝ × CVec | q.1 ∈ Ω ∧ q.2.1 ∈ W' ∧
      q.2.2 ∈ ball ((F.child D k pk s' cc ph).cur q.1 r) ϱ'}, q.2.1 ∈ W := by
    rintro q ⟨_, h2, _⟩
    exact h.mem_W h2
  have hZc := continuousOn_Zarg_of (D := D) (k := k) (pk := pk) h.hF h.hζ h.hcc.continuousOn
    h.hph.continuousOn (h.mem_W hr) hS1 hS2
  have hres := continuousOn_fl_Zarg h.hF hc hS1 hW hZ hZc
  show ContinuousOn (fun q : Par × ℝ × CVec => F.fl q.1 q.2.1 (Zarg D F k pk cc ph r q) F.anc) _
  exact hres

end ChildHyp

end CFam
end

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **The families of a scheduled chain have the invariants of their levels**, with the windows
`slotWin` of the scheduled slots. A family of
level `l` anchored at the slot `p` of level `l + 1` is *over* `p` (`CFam.Over`) if it has the
invariants with the window `slotWin D (l+1) p`, the radius `ϱ_l = 8bε_l`, the rate `K a_l` and the
window length `6h_{l+1}/5`. The base family of level `l` is over its slot (`baseOver`), and the
child of level `l + 1` of a family over `p`, anchored at a slot `p'` scheduled in `p`, with
holomorphic center `|c| ≤ 3bε_{l+1}/4` and phase `|Im ζ_q| ≤ (3+1/2)b + b/64`, is over `p'`
(`Over.child`). The scale facts used at each level (`LevelScales`) follow from the carrier start
with `Υ, C_H ≥ 1` and `b ≤ 10^{-4}` (`levelScales_of_carrierStart`). -/

/-! ### Scale facts -/

/-- `2 E^θ ≤ e^θ` for `128 e ≤ E` and `θ ≤ -1/7`. -/
theorem two_mul_rpow_le {E e θ : ℝ} (he : 0 < e) (hE : 128 * e ≤ E) (hθ : θ ≤ -1 / 7) :
    2 * E ^ θ ≤ e ^ θ := by
  have hE0 : 0 < E := by linarith
  have h1 : (E / 128) ^ θ ≤ e ^ θ :=
    Real.rpow_le_rpow_of_nonpos he (by rw [le_div_iff₀ (by norm_num)]; linarith) (by linarith)
  rw [Real.div_rpow hE0.le (by norm_num)] at h1
  have h128 : (128 : ℝ) ^ θ ≤ 1 / 2 := by
    have h2 : (128 : ℝ) ^ θ ≤ (128 : ℝ) ^ (-1 / 7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
    have h3 : (128 : ℝ) ^ (-1 / 7 : ℝ) = 1 / 2 := by
      have e1 : (-1 / 7 : ℝ) = -((7 : ℕ) : ℝ)⁻¹ := by norm_num
      have e2 : (128 : ℝ) = 2 ^ (7 : ℕ) := by norm_num
      rw [e1, Real.rpow_neg (by norm_num), e2, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
      norm_num
    linarith
  have h4 : 0 < (128 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have h6 : 0 ≤ e ^ θ := Real.rpow_nonneg he.le θ
  rw [div_le_iff₀ h4] at h1
  have : e ^ θ * (128 : ℝ) ^ θ ≤ e ^ θ * (1 / 2) := mul_le_mul_of_nonneg_left h128 h6
  linarith

/-- The shear amplitude is `2π a_m ε_m`. -/
theorem shearAmp_eq {α q : ℝ} {Λ m : ℕ} (hε : 0 < ocEpsilon q Λ m) :
    shearAmp α q Λ m = 2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m := by
  unfold shearAmp ocA
  set e := ocEpsilon q Λ m
  have h1 : e ^ (1 + α) * e⁻¹ = e ^ α := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hε]
    congr 1; ring
  have h2 : e ^ ((1 + α) - 2) * e = e ^ α := by
    have : e ^ ((1 + α) - 2) * e = e ^ ((1 + α) - 2) * e ^ (1 : ℝ) := by rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hε]
    congr 1; ring
  calc 2 * Real.pi * e ^ (1 + α) * e⁻¹ = 2 * Real.pi * (e ^ (1 + α) * e⁻¹) := by ring
    _ = 2 * Real.pi * (e ^ ((1 + α) - 2) * e) := by rw [h1, h2]
    _ = 2 * Real.pi * e ^ ((1 + α) - 2) * e := by ring

/-- **The scale facts of the child step** at the parent level `l`. -/
structure LevelScales (D : OCData) (b : ℝ) (l : ℕ) : Prop where
  hb0 : 0 < b
  hb1 : b ≤ 1 / 10000
  hΛ : 128 ≤ D.Λ
  heps : 128 * D.eps (l + 1) ≤ D.eps l
  hA : 2 * ocA D.α D.q D.Λ l ≤ ocA D.α D.q D.Λ (l + 1)
  hAH : ocA D.α D.q D.Λ l * ocTauPP D.α D.q D.Λ (l + 1) ≤ b / 10000
  hah : ocA D.α D.q D.Λ (l + 1) * ocTauPP D.α D.q D.Λ (l + 2) ≤ b / 10000
  hsep : ocTauPP D.α D.q D.Λ (l + 2) < ocTau D.α D.q D.Λ (l + 1) / 48

/-- The strain-rate smallness of the carrier start, with `Υ, C_H ≥ 1`. -/
theorem smallness_of_carrierStart {α q b CH Υ : ℝ} {Λ j₀ : ℕ} (hΛ : 1 ≤ Λ) (hCH : 1 ≤ CH)
    (hΥ : 1 ≤ Υ) (h : IsCarrierStart α q Λ b CH Υ j₀) {k : ℕ} (hk : j₀ ≤ k + 1) :
    ocA α q Λ k * ocTauPP α q Λ (k + 1) ≤ b / 10000 := by
  have h1 := h.1 k hk
  have hA0 : 0 ≤ ocA α q Λ k := Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hT0 : 0 ≤ ocTauPP α q Λ (k + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  set x := ocA α q Λ k * ocTauPP α q Λ (k + 1)
  have hx0 : 0 ≤ x := mul_nonneg hA0 hT0
  have e1 : 2 * Υ * CH * ocA α q Λ k * ocTauPP α q Λ (k + 1) = 2 * (Υ * CH) * x := by ring
  rw [e1] at h1
  have hΥC : 1 ≤ Υ * CH := by nlinarith
  have h2 : 2 * x ≤ 2 * (Υ * CH) * x := by nlinarith
  have hπ := Real.pi_gt_d2
  have hden : 10000 ≤ 2 * (64 * (8 * Real.pi ^ 2)) := by nlinarith
  have hb : 0 ≤ b := by
    have : 0 ≤ 2 * (Υ * CH) * x := by positivity
    have hd : 0 < 64 * (8 * Real.pi ^ 2) := by positivity
    have := this.trans h1
    rwa [le_div_iff₀ hd, zero_mul] at this
  have h3 : 2 * x ≤ b / (64 * (8 * Real.pi ^ 2)) := h2.trans h1
  have h4 : b / (64 * (8 * Real.pi ^ 2)) ≤ 2 * (b / 10000) := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (b / 10000) * (64 * (8 * Real.pi ^ 2)) = b / 10000 * (2 * (64 * (8 * Real.pi ^ 2))) :=
      by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ b / 10000)
    linarith
  linarith

/-- The history separation of the carrier start, with `C_H ≥ 1`. -/
theorem separation_of_carrierStart {α q b CH Υ : ℝ} {Λ j₀ : ℕ} (hΛ : 1 ≤ Λ) (hCH : 1 ≤ CH)
    (h : IsCarrierStart α q Λ b CH Υ j₀) {m : ℕ} (hm : j₀ ≤ m) :
    ocTauPP α q Λ (m + 1) < ocTau α q Λ m / 48 := by
  have h1 := h.2 m hm
  have hT0 : 0 ≤ ocTauPP α q Λ (m + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  have : ocTauPP α q Λ (m + 1) ≤ CH * ocTauPP α q Λ (m + 1) := by nlinarith
  linarith

/-- **The scale facts from the carrier start.** -/
theorem levelScales_of_carrierStart {D : OCData} {b CH Υ : ℝ} {j₀ l : ℕ} (hq : 1 < D.q)
    (hΛ : 128 ≤ D.Λ) (hα : D.α < 1 / 3) (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hCH : 1 ≤ CH)
    (hΥ : 1 ≤ Υ) (hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (hl : j₀ ≤ l + 1) :
    LevelScales D b l := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  have heps : 128 * D.eps (l + 1) ≤ D.eps l := by
    have h := Scales.epsilon_ratio_lower (q := D.q) (Λ := D.Λ) (m := l + 1) hq hΛ (by omega)
    have hpos : 0 < ocEpsilon D.q D.Λ (l + 1) := Construction.Stream.ocEpsilon_pos hΛ1
    rw [Nat.add_sub_cancel, ge_iff_le, le_div_iff₀ hpos] at h
    have hΛr : (128 : ℝ) ≤ D.Λ := by exact_mod_cast hΛ
    have := mul_le_mul_of_nonneg_right hΛr hpos.le
    show 128 * ocEpsilon D.q D.Λ (l + 1) ≤ ocEpsilon D.q D.Λ l
    linarith
  refine ⟨hb0, hb1, hΛ, heps, ?_, smallness_of_carrierStart hΛ1 hCH hΥ hcs hl,
    smallness_of_carrierStart hΛ1 hCH hΥ hcs (by omega),
    separation_of_carrierStart hΛ1 hCH hcs (by omega)⟩
  exact two_mul_rpow_le (Construction.Stream.ocEpsilon_pos hΛ1) heps (by linarith)

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

/-- **The invariants are monotone in the rate.** -/
theorem OK.mono_rate (h : F.OK Ω W ϱ Λ T) {Λ' : ℝ} (hΛ' : Λ ≤ Λ') (hΛT : Λ' * T ≤ 1 / 2) :
    F.OK Ω W ϱ Λ' T where
  hϱ := h.hϱ
  hΛ := h.hΛ.trans hΛ'
  hT := h.hT
  hΛT := hΛT
  anc_mem := h.anc_mem
  hΩ := h.hΩ
  ctr_hol := h.ctr_hol
  cur_anc := h.cur_anc
  hol := h.hol
  init := h.init
  jac := fun P hP u hu r hr y hy =>
    (h.jac P hP u hu r hr y hy).trans (mul_le_mul_of_nonneg_right hΛ' (abs_nonneg _))
  group := h.group

/-- **A family over the slot `p`**: level `l`, anchored at the slot `p` of level `l + 1`, with the
invariants of its level. -/
structure Over (F : CFam Par) (D : OCData) (b : ℝ) (Ω : Set Par) (l : ℕ) (p : ℤ) : Prop where
  anc : F.anc = D.slotAnchor (l + 1) p
  ok : F.OK Ω (slotWin D (l + 1) p) (8 * b * D.eps l) (chainK * ocA D.α D.q D.Λ l)
    (6 / 5 * ocTauPP D.α D.q D.Λ (l + 1))
  cont : F.TimeCont Ω (slotWin D (l + 1) p) (8 * b * D.eps l)

variable {D : OCData} {b : ℝ}

/-- **The child of a family over a slot is over the scheduled slot.** -/
theorem Over.child {l : ℕ} {p p' : ℤ} (hF : F.Over D b Ω l p) (hS : LevelScales D b l)
    (hζ : IsFastProfile D.ζ) (hp' : IsScheduledIn D (l + 1) p' p) {cc ph : Par → CVec}
    (hcc : DifferentiableOn ℂ cc Ω) (hph : DifferentiableOn ℂ ph Ω)
    (hBc : ∀ P ∈ Ω, ‖cc P‖ ≤ 3 / 4 * b * D.eps (l + 1))
    (hBph : ∀ P ∈ Ω, |((ph P) (transverseIndex p)).im| ≤ phB b) :
    (F.child D (l + 1) p (D.slotAnchor (l + 2) p') cc ph).Over D b Ω (l + 1) p' := by
  have hΛ1 : 1 ≤ D.Λ := by have := hS.hΛ; omega
  have he : 0 < D.eps (l + 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hE : 0 < D.eps l := Construction.Stream.ocEpsilon_pos hΛ1
  have hA0 : 0 ≤ ocA D.α D.q D.Λ l := Real.rpow_nonneg hE.le _
  have ha0 : 0 ≤ ocA D.α D.q D.Λ (l + 1) := Real.rpow_nonneg he.le _
  have hH0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 1) := (Construction.Stream.ocTauPP_pos hΛ1).le
  have hh0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 2) := (Construction.Stream.ocTauPP_pos hΛ1).le
  have hX0 : 0 ≤ Real.exp (30 * Real.pi * b) := (Real.exp_pos _).le
  have hY0 : 0 ≤ Real.exp (30 * Real.pi * b + 1) := (Real.exp_pos _).le
  have hX := exp_small_le hS.hb0.le hS.hb1
  have hY := exp_small_one_le hS.hb0.le hS.hb1
  have hshA : shearAmp D.α D.q D.Λ (l + 1) = 2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) :=
    shearAmp_eq he
  have hfreq : shearFreq D.q D.Λ (l + 1) * (15 * b * D.eps (l + 1)) = 30 * Real.pi * b := by
    unfold shearFreq
    show 2 * Real.pi * (D.eps (l + 1))⁻¹ * (15 * b * D.eps (l + 1)) = 30 * Real.pi * b
    field_simp
    ring
  have hfreq0 : 0 ≤ shearFreq D.q D.Λ (l + 1) := (shearFreq_pos he).le
  have hAF : shearAmp D.α D.q D.Λ (l + 1) * shearFreq D.q D.Λ (l + 1) =
      4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) := by
    rw [hshA]
    unfold shearFreq
    show 2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * (2 * Real.pi * (D.eps (l + 1))⁻¹) = _
    field_simp
    ring
  have hMs : ∀ w : CVec, |(w (transverseIndex p)).im| ≤ 15 * b * D.eps (l + 1) →
      ‖ocShearVelC D.α D.q D.Λ (l + 1) p w‖ ≤
        2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * Real.exp (30 * Real.pi * b) := by
    intro w hw
    refine (norm_ocShearVelC_le _ _ _ _ _ he w).trans ?_
    rw [hshA, ← hfreq]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hfreq0))
      (by have := Real.pi_pos; positivity)
  have hMs' : ∀ w : CVec, |(w (transverseIndex p)).im| ≤ 15 * b * D.eps (l + 1) →
      ‖fderiv ℂ (ocShearVelC D.α D.q D.Λ (l + 1) p) w‖ ≤
        4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) * Real.exp (30 * Real.pi * b + 1) := by
    intro w hw
    refine (norm_fderiv_ocShearVelC_le _ _ _ _ _ he w).trans ?_
    rw [hAF, ← hfreq]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hw hfreq0]))
      (by have := Real.pi_pos; positivity)
  have hu0 := step_u_nonneg hA0 hH0
  have hu := step_u_le hA0 hH0 hS.hAH
  have hw0 := step_w_nonneg (X := Real.exp (30 * Real.pi * b)) he ha0 hh0 hX0
  have hw := step_w_le he ha0 hh0 hS.hah hX0 hX
  have hrate := step_rate hS.hb0 hS.hb1 he hS.heps hA0 hS.hA hH0 hS.hAH hX0 hX hY0 hY
  have hwin := step_window hS.hb1 ha0 hh0 hS.hah
  have hT'0 : 0 ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (l + 2) := by positivity
  have hC : CFam.ChildHyp D F Ω (slotWin D (l + 1) p) (slotWin D (l + 2) p') (8 * b * D.eps l)
      (chainK * ocA D.α D.q D.Λ l) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 1)) (l + 1) p
      (D.slotAnchor (l + 2) p') cc ph (8 * b * D.eps (l + 1)) (6 / 5 * ocTauPP D.α D.q D.Λ (l + 2))
      (3 / 4 * b * D.eps (l + 1)) (phB b) (15 * b * D.eps (l + 1))
      (2 * Real.pi * ocA D.α D.q D.Λ (l + 1) * D.eps (l + 1) * Real.exp (30 * Real.pi * b))
      (4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (l + 1) * Real.exp (30 * Real.pi * b + 1)) :=
    { hF := hF.ok
      hζ := hζ
      hε := he
      hcc := hcc
      hph := hph
      hW' := slotWin_subset D hΛ1 hp' hS.hsep
      hs' := anchor_mem_slotWin D hΛ1 (l + 2) p'
      hT' := fun u hu r hr => abs_sub_le_of_mem_slotWin D hu hr
      hϱ' := by have := hS.hb0; positivity
      hBc0 := by have := hS.hb0; positivity
      hBph0 := by unfold phB; have := hS.hb0; positivity
      hMs0 := by have := Real.pi_pos; positivity
      hMs'0 := by positivity
      hBc := hBc
      hBph := hBph
      hMs := hMs
      hMs' := hMs'
      hσ := step_sigma hS.hb0 hS.hb1 he hu hw
      hRa := step_Ra hS.hb0 hS.hb1 he hS.heps hu hw0 hw
      hRb := step_Rb hS.hb0 hS.hb1 he hS.heps hu hw
      hΛT' := (mul_le_mul_of_nonneg_right hrate hT'0).trans hwin }
  exact ⟨rfl, hC.ok.mono_rate hrate hwin, hC.timeCont hF.cont⟩

/-- **The base family is over its slot.** -/
theorem baseOver {l : ℕ} {V : ℝ}
    (hv : HolField (velC D.α D.q D.Λ D.ζ l) (D.eps l / 50) (velA * ocA D.α D.q D.Λ l) V)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (hΛ : 1 ≤ D.Λ)
    (hAH : ocA D.α D.q D.Λ l * ocTauPP D.α D.q D.Λ (l + 1) ≤ b / 10000)
    {ctr : Par → CVec} (hΩ : IsOpen Ω) (hctr : DifferentiableOn ℂ ctr Ω)
    (hB : ∀ P ∈ Ω, imL1 (ctr P) ≤ 15 / 1000 * D.eps l) (p : ℤ) :
    (baseFam (velC D.α D.q D.Λ D.ζ l) (baseW D l) ctr (D.slotAnchor (l + 1) p)).Over D b Ω l p := by
  have hE : 0 < D.eps l := Construction.Stream.ocEpsilon_pos hΛ
  have hA0 : 0 ≤ ocA D.α D.q D.Λ l := Real.rpow_nonneg hE.le _
  have hH0 : 0 ≤ ocTauPP D.α D.q D.Λ (l + 1) := (Construction.Stream.ocTauPP_pos hΛ).le
  obtain ⟨c1, c2, c3, c4, c5⟩ := base_consts hb1 hE hA0 hH0 hAH
  set s := D.slotAnchor (l + 1) p
  set h := ocTauPP D.α D.q D.Λ (l + 1)
  have hba : (s + 3 / 5 * h) - (s - 3 / 5 * h) = 6 / 5 * h := by ring
  have hvA : velA * ocA D.α D.q D.Λ l = 2 ^ 21 * ocA D.α D.q D.Λ l := by unfold velA; ring
  have hw : FlowWin (D.eps l / 50) (baseW D l) (velA * ocA D.α D.q D.Λ l) (s - 3 / 5 * h)
      (s + 3 / 5 * h) :=
    { hℓ' := by unfold baseW; positivity
      hℓℓ := by unfold baseW; linarith
      hab := by linarith
      hΓT := by rw [hba, hvA]; exact c2 }
  have hok := baseFam_ok hv hw (W := slotWin D (l + 1) p) subset_rfl hΩ hctr
    (B₀ := 15 / 1000 * D.eps l) (ϱ := 8 * b * D.eps l) hB (by have := hb0; positivity) (by rw [hba, hvA]; unfold baseW; exact c3)
    (by rw [hba, hvA]; linarith) (anchor_mem_slotWin D hΛ (l + 1) p)
  have hcont := baseFam_timeCont hv hw (W := slotWin D (l + 1) p) (Ω := Ω) (s := s)
    (ϱ := 8 * b * D.eps l) subset_rfl fun P hP r hr =>
      baseFam_ball_subset hv hw subset_rfl (B₀ := 15 / 1000 * D.eps l) hB
        (by have := hb0; positivity) (by rw [hba, hvA]; unfold baseW; exact c3)
        (anchor_mem_slotWin D hΛ (l + 1) p) hP hr
  rw [hba] at hok
  refine ⟨rfl, hok.mono_rate ?_ c5, hcont⟩
  rw [hvA]; linarith

end CFam

end AVRegularity.Providers.ComplexFlow
end
