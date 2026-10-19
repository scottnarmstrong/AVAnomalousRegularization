-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.DSlowCell
public import AVRegularity.Proofs.ComplexContext.CellInvC
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexContext.Restrict
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PicardGroup

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology Metric Homogenization Complex
open scoped ENNReal Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the old-label derivative of context expressions** (`dOld`). The old-label
derivative recenters the chain and moves the final phase at the rate `ε_i⁻¹`: its extension is the
derivative at `h = 0` along `recOld`, the complex recentering followed by the final-phase
translation by `ε_i⁻¹h` (`dOldF`). At a real final phase it splits into the recentering derivative
at a fixed final phase and `ε_i⁻¹` times the final-phase derivative in the direction `e_j`. The
final-phase modes of the first part are at most `(12/b)/(ε_{i-1}Δ) B(𝗆 + Δ)`: the Cauchy circle
integral in the offset is exchanged with the final-phase coefficient
(`norm_finalPhaseCoeff_dSlowG_le`). The second part is the `dPhase` derivative for `j = q` (modes
`2π|h|B(𝗆)`) and vanishes for `j ≠ q`, by the final-phase invariance (`CtxInv.dOld`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

theorem continuous_cauchyKernel {r : ℝ} (hr : 0 < r) : Continuous (GenSem.cauchyKernel r) := by
  unfold GenSem.cauchyKernel
  exact continuous_const.mul ((continuous_circleMap 0 r).inv₀ fun θ => circleMap_ne_center hr.ne')

/-- **The final-phase modes of the recentering derivative at a fixed final phase.** -/
theorem norm_finalPhaseCoeff_dSlowG_le (env : ChainEnv D b CH Υ j₀) {fa : GenSort.Sem .ctx}
    {F : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p fa F B) {mres Δ : ℝ}
    (hm0 : 0 ≤ mres) (hΔ : 0 < Δ) (hmΔ : mres + Δ ≤ 2) (k : ℤ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) {dd : ChainData} {n : ℕ}
    (hdd : AdmData D b j₀ i p dd n) {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    (hre : RealFinal x) (htop : B (mres + Δ) k t ≠ ⊤) (j : Fin 2) :
    ‖finalPhaseCoeff (transverseIndex p) (dSlowG D j₀ i p j F dd n t) x k‖ ≤
      (B (mres + Δ) k t).toReal / (b * D.eps (dd.baseLevel + n) * Δ / 12) := by
  have hg := hdd.goodData
  obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
  have hsl := hdd.lastSlot
  have hb0 := env.hb0
  set q := transverseIndex p with hq
  set r := b * D.eps (dd.baseLevel + n) * Δ / 12 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < b * D.eps (dd.baseLevel + n) := by rw [hr]; nlinarith
  have hymem : ∀ s : ℝ, ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) ∈
      carrierC D b dd n mres := fun s => by
    have := mem_carrierC_line hx (hre _) (z := (s : ℂ)) (by
      simp only [Complex.ofReal_im, abs_zero]; positivity)
    rwa [hsl] at this
  have hcn : ∀ θ : ℝ, ‖circleMap 0 r θ • cbasis j‖ = r := fun θ => by
    rw [norm_smul, norm_cbasis, mul_one, norm_circleMap_zero, abs_of_pos hr0]
  have hrecmem : ∀ s θ : ℝ, recC D dd n ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n)
      (circleMap 0 r θ • cbasis j) ∈ carrierC D b dd n (mres + Δ) := fun s θ =>
    recC_mem env hg.1 hm0 hΔ hmΔ (hymem s) (le_of_eq (hcn θ))
  -- the circle representation along the final-phase line
  have hA : ∀ s : ℝ, dSlowG D j₀ i p j F dd n t ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) :
      ChainParamsC n) = (2 * Real.pi * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
        GenSem.cauchyKernel r θ • F dd n t (recC D dd n ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) :
          ChainParamsC n) (circleMap 0 r θ • cbasis j)) := by
    intro s
    rw [dSlowG_of hg]
    have hys2 : ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) ∈ carrierC D b dd n 2 :=
      carrierC_mono hb0.le (by linarith) (hymem s)
    have hU := isOpen_alongFib (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ hys2
    have hFd : DifferentiableOn ℂ (fun w => F dd n t (recC D dd n
        ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) w))
        (ball (0 : CVec) (b * D.eps (dd.baseLevel + n)) ∩ (fun w => recC D dd n
          ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) w) ⁻¹'
            carrierC D b dd n 2) :=
      (hF.hol dd n t ht).comp (hΦ.comp ((differentiableOn_const _).prodMk
        differentiableOn_id) fun w hw => ⟨hys2, hw.1⟩) fun w hw => hw.2
    have h1 := fderiv_apply_eq_circle hU hFd hr0 (y := (0 : CVec)) (w := cbasis j)
      fun ζ hζ => by
        rw [zero_add]
        have hζw : ‖ζ • cbasis j‖ ≤ r := by rw [norm_smul, norm_cbasis, mul_one]; exact hζ
        exact ⟨mem_ball_zero_iff.mpr (hζw.trans_lt hrρ), carrierC_mono hb0.le hmΔ
          (recC_mem env hg.1 hm0 hΔ hmΔ (hymem s) hζw)⟩
    unfold dAlong
    rw [h1]
    simp only [zero_add]
  -- continuity of the double integrand
  have hcont : Continuous fun q' : ℝ × ℝ => F dd n t (recC D dd n
      ((x.1, x.2.1, x.2.2 + evec q (q'.1 : ℂ)) : ChainParamsC n) (circleMap 0 r q'.2 • cbasis j)) := by
    have hrc : ContinuousOn (fun w : ChainParamsC n × CVec => F dd n t (recC D dd n w.1 w.2))
        ((carrierC D b dd n 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + n))) ∩
          (fun w : ChainParamsC n × CVec => recC D dd n w.1 w.2) ⁻¹' carrierC D b dd n 2) :=
      ((hF.hol dd n t ht).comp (hΦ.mono fun w hw => hw.1) fun w hw => hw.2).continuousOn
    have hpath : Continuous fun q' : ℝ × ℝ => ((((x.1, x.2.1, x.2.2 + evec q (q'.1 : ℂ)) :
        ChainParamsC n), circleMap 0 r q'.2 • cbasis j) : ChainParamsC n × CVec) := by
      refine Continuous.prodMk ?_ (((continuous_circleMap 0 r).comp continuous_snd).smul
        continuous_const)
      refine continuous_const.prodMk (continuous_const.prodMk (continuous_const.add ?_))
      exact continuous_pi fun a => by
        unfold evec; split_ifs
        · exact Complex.continuous_ofReal.comp continuous_fst
        · exact continuous_const
    exact hrc.comp_continuous hpath fun q' => ⟨⟨carrierC_mono hb0.le (by linarith) (hymem q'.1),
      mem_ball_zero_iff.mpr ((le_of_eq (hcn q'.2)).trans_lt hrρ)⟩,
      carrierC_mono hb0.le hmΔ (hrecmem q'.1 q'.2)⟩
  set E : ℝ → ℂ := fun s => Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))) with hE
  have hEc : Continuous E := by rw [hE]; fun_prop
  set Ψ : ℝ → ℝ → ℂ := fun s θ => (GenSem.cauchyKernel r θ • F dd n t (recC D dd n
    ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) (circleMap 0 r θ • cbasis j))) * E s
    with hΨ
  have hΨc : Continuous (Function.uncurry Ψ) := by
    rw [hΨ]
    exact (((continuous_cauchyKernel hr0).comp continuous_snd).smul hcont).mul
      (hEc.comp continuous_fst)
  have hΨint : IntegrableOn (Function.uncurry Ψ) (Ι (0 : ℝ) 1 ×ˢ Ι (0 : ℝ) (2 * Real.pi)) :=
    (hΨc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  -- the exchange
  have h1 : finalPhaseCoeff q (dSlowG D j₀ i p j F dd n t) x k =
      (2 * Real.pi * I)⁻¹ • ∫ s in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..2 * Real.pi, Ψ s θ := by
    unfold finalPhaseCoeff
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show dSlowG D j₀ i p j F dd n t ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) * E s = _
    rw [hA s, smul_mul_assoc, ← intervalIntegral.integral_mul_const]
  have h2 : ∫ s in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..2 * Real.pi, Ψ s θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, GenSem.cauchyKernel r θ •
        finalPhaseCoeff q (F dd n t) (recC D dd n x (circleMap 0 r θ • cbasis j)) k := by
    rw [intervalIntegral_intervalIntegral_swap hΨint]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hΨ]
    simp_rw [smul_mul_assoc]
    rw [intervalIntegral.integral_smul]
    congr 1
    have e : ∀ s : ℝ, F dd n t (recC D dd n ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n)
        (circleMap 0 r θ • cbasis j)) = F dd n t ((recC D dd n x (circleMap 0 r θ • cbasis j)).1,
          (recC D dd n x (circleMap 0 r θ • cbasis j)).2.1,
          (recC D dd n x (circleMap 0 r θ • cbasis j)).2.2 + evec q (s : ℂ)) := fun s => by
      rw [recC_final, recC_snd_snd]
    unfold finalPhaseCoeff
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact congrArg (fun z => z * E s) (e s)
  rw [h1, h2, norm_smul]
  have hbd : ‖∫ θ in (0 : ℝ)..2 * Real.pi, GenSem.cauchyKernel r θ •
      finalPhaseCoeff q (F dd n t) (recC D dd n x (circleMap 0 r θ • cbasis j)) k‖ ≤
      r⁻¹ * (B (mres + Δ) k t).toReal * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_cauchyKernel hr0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hz : recC D dd n x (circleMap 0 r θ • cbasis j) ∈ carrierC D b dd n (mres + Δ) :=
      recC_mem env hg.1 hm0 hΔ hmΔ hx (le_of_eq (hcn θ))
    have hzre : RealFinal (recC D dd n x (circleMap 0 r θ • cbasis j)) := by
      intro a; rw [recC_snd_snd]; exact hre a
    have h3 := hF.mode (mres + Δ) (by linarith) hmΔ k t ht dd n hdd _ hz hzre
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h3
  have h2pi : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [h2pi]
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_pos Real.two_pi_pos]
  field_simp


/-! ### The old-label derivative -/

/-- The recentering followed by the final-phase translation by `ε_i⁻¹h`. -/
def recOld (D : OCData) (i : ℕ) (dd : ChainData) (n : ℕ) (x : ChainParamsC n) (w : CVec) :
    ChainParamsC n :=
  ((recC D dd n x w).1, (recC D dd n x w).2.1, x.2.2 + epsInvC D i • w)

open scoped Classical in
/-- **The extension of the old-label derivative.** -/
def dOldF (D : OCData) (j₀ i : ℕ) (p : ℤ) (j : Fin 2) (F : Ext) : Ext :=
  fun dd n t x => if GoodData D j₀ i p dd n then dAlong (recOld D i dd n) (F dd n t) (cbasis j) x
    else 0

theorem dOldF_of {j : Fin 2} {F : Ext} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : GoodData D j₀ i p dd n) :
    dOldF D j₀ i p j F dd n t x = dAlong (recOld D i dd n) (F dd n t) (cbasis j) x := by
  simp only [dOldF, hg, ↓reduceIte]

theorem dOldF_of_not {j : Fin 2} {F : Ext} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : ¬GoodData D j₀ i p dd n) : dOldF D j₀ i p j F dd n t x = 0 := by
  simp only [dOldF, hg, ↓reduceIte]

theorem recOld_facts (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) :
    0 < b * D.eps (dd.baseLevel + n) ∧
      DifferentiableOn ℂ (fun q : ChainParamsC n × CVec => recOld D i dd n q.1 q.2)
        (carrierC D b dd n 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + n))) ∧
      ∀ x ∈ carrierC D b dd n 2, recOld D i dd n x 0 = x := by
  obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
  refine ⟨hρ, hΦ.fst.prodMk (hΦ.snd.fst.prodMk ?_), fun x hx => ?_⟩
  · exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC n × CVec =>
      q.1.2.2 + epsInvC D i • q.2).differentiableOn
  · unfold recOld
    rw [hΦ0 x hx, smul_zero, add_zero]

theorem recOld_shiftFinal (D : OCData) (i : ℕ) (dd : ChainData) (n : ℕ) (x : ChainParamsC n)
    (v : Vec 2) (w : CVec) :
    recOld D i dd n (x.shiftFinal v) w = (recOld D i dd n x w).shiftFinal v := by
  unfold recOld ChainParamsC.shiftFinal
  rw [recC_final]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  show x.2.2 + (fun a => (v a : ℂ)) + epsInvC D i • w = x.2.2 + epsInvC D i • w + fun a => (v a : ℂ)
  abel

theorem recOld_shiftChild (hΛ : 1 ≤ D.Λ) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2} (hv : TInt (dd.slots.getD k 0) v) (w : CVec) :
    recOld D i dd n (x.shiftChild k v) w = (recOld D i dd n x w).shiftChild k v := by
  unfold recOld
  rw [recC_shiftChild hΛ hdd x k hv w]
  rfl

/-- **The chain rule for the old-label derivative**: recentering part plus `ε_i⁻¹` times the
final-phase derivative. -/
theorem dAlong_recOld_eq (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) {G : ChainParamsC n → ℂ}
    (hG : DifferentiableOn ℂ G (carrierC D b dd n 2)) {y : ChainParamsC n}
    (hy : y ∈ carrierC D b dd n 2) (w : CVec) :
    dAlong (recOld D i dd n) G w y =
      dAlong (recC D dd n) G w y + epsInvC D i * fderiv ℂ G y ((0, 0, w) : ChainParamsC n) := by
  obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
  have hGy : DifferentiableAt ℂ G y :=
    (hG y hy).differentiableAt ((ComplexFlow.isOpen_carrierC D b dd n 2).mem_nhds hy)
  have hr : DifferentiableAt ℂ (fun v => recC D dd n y v) 0 := by
    have h1 : DifferentiableOn ℂ (fun v => recC D dd n y v) (ball (0 : CVec)
        (b * D.eps (dd.baseLevel + n))) :=
      hΦ.comp ((differentiableOn_const y).prodMk differentiableOn_id) fun v hv => ⟨hy, hv⟩
    exact (h1 0 (mem_ball_self hρ)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  set Lf : CVec →L[ℂ] ChainParamsC n := (0 : CVec →L[ℂ] (Fin 2 → ℂ)).prod
    ((0 : CVec →L[ℂ] (Fin n → (Fin 2 → ℂ) × (Fin 2 → ℂ))).prod (epsInvC D i • ContinuousLinearMap.id ℂ CVec))
    with hLf
  have hf : HasFDerivAt (fun v : CVec => ((0, 0, epsInvC D i • v) : ChainParamsC n)) Lf 0 :=
    Lf.hasFDerivAt
  have he : (fun v => recOld D i dd n y v) = fun v => recC D dd n y v + ((0, 0, epsInvC D i • v) :
      ChainParamsC n) := by
    funext v
    unfold recOld
    refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
    simp only [Prod.snd_add, recC_snd_snd]
  have hsum := hr.hasFDerivAt.add hf
  have hpt : ((fun v => recC D dd n y v) +
      fun v : CVec => ((0, 0, epsInvC D i • v) : ChainParamsC n)) 0 = y := by
    simp only [Pi.add_apply]
    rw [hΦ0 y hy, smul_zero]
    simp
  have hc1 : HasFDerivAt (fun v => G (recOld D i dd n y v))
      ((fderiv ℂ G y).comp (fderiv ℂ (fun v => recC D dd n y v) 0 + Lf)) 0 := by
    have h0 : HasFDerivAt G (fderiv ℂ G y) (((fun v => recC D dd n y v) +
        fun v : CVec => ((0, 0, epsInvC D i • v) : ChainParamsC n)) 0) := by
      rw [hpt]; exact hGy.hasFDerivAt
    have h1 := h0.comp 0 hsum
    have e2 : (fun v => G (recOld D i dd n y v)) = G ∘ ((fun v => recC D dd n y v) +
        fun v : CVec => ((0, 0, epsInvC D i • v) : ChainParamsC n)) := by
      funext v
      simp only [Function.comp_apply, Pi.add_apply]
      rw [← congrFun he v]
    rw [e2]
    exact h1
  have hc2 : HasFDerivAt (fun v => G (recC D dd n y v))
      ((fderiv ℂ G y).comp (fderiv ℂ (fun v => recC D dd n y v) 0)) 0 := by
    have h0 : HasFDerivAt G (fderiv ℂ G y) ((fun v => recC D dd n y v) 0) := by
      show HasFDerivAt G (fderiv ℂ G y) (recC D dd n y 0)
      rw [hΦ0 y hy]
      exact hGy.hasFDerivAt
    exact h0.comp 0 hr.hasFDerivAt
  unfold dAlong
  rw [hc1.fderiv, hc2.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, add_apply, map_add]
  congr 1
  have : Lf w = epsInvC D i • ((0, 0, w) : ChainParamsC n) := by
    rw [hLf]
    simp
  rw [this, map_smul, smul_eq_mul]

/-- **A final-phase derivative in a non-transverse direction vanishes.** -/
theorem fderiv_final_eq_zero {n : ℕ} {S : Set (ChainParamsC n)} (hS : IsOpen S)
    {G : ChainParamsC n → ℂ} (hG : DifferentiableOn ℂ G S) {pq : ℤ}
    (hsym : ∀ y ∈ S, ∀ v : Vec 2, TInt pq v → G (y.shiftFinal v) = G y) {y : ChainParamsC n}
    (hy : y ∈ S) {j : Fin 2} (hj : j ≠ transverseIndex pq) :
    fderiv ℂ G y ((0, 0, cbasis j) : ChainParamsC n) = 0 := by
  set v : ChainParamsC n := (0, 0, cbasis j) with hv
  have hGy : DifferentiableAt ℂ G y := (hG y hy).differentiableAt (hS.mem_nhds hy)
  have h1 : HasDerivAt (fun z : ℂ => G (y + z • v)) (fderiv ℂ G y v) 0 := by
    have hl : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have h2 : HasFDerivAt G (fderiv ℂ G y) (y + (0 : ℂ) • v) := by
      simpa using hGy.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℂ) hl
  have h3 : HasDerivAt (fun s : ℝ => G (y + (s : ℂ) • v)) (fderiv ℂ G y v) 0 := by
    have := h1.comp_ofReal (z := 0)
    simpa using this
  have hconst : (fun s : ℝ => G (y + (s : ℂ) • v)) = fun _ => G y := by
    funext s
    have e : y + (s : ℂ) • v = y.shiftFinal (s • basisVec j) := by
      refine Prod.ext (by simp [hv, ChainParamsC.shiftFinal])
        (Prod.ext (by simp [hv, ChainParamsC.shiftFinal]) ?_)
      funext a
      simp only [hv, ChainParamsC.shiftFinal, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      by_cases ha : a = j
      · subst ha; simp [cbasis, basisVec_apply]
      · simp [cbasis, basisVec_apply, ha]
    rw [e]
    refine hsym y hy _ ⟨0, ?_⟩
    simp [basisVec_apply, Ne.symm hj]
  rw [hconst] at h3
  exact h3.unique (hasDerivAt_const 0 (G y))


/-- **The old-label derivative of a context expression.** -/
theorem CtxInv.dOld (env : ChainEnv D b CH Υ j₀) {Δ : ℝ} (hΔ : 0 < Δ) {C : ℝ≥0∞}
    (hC : ENNReal.ofReal (12 / b) ≤ C) (j : Fin 2) {fa : GenSort.Sem .ctx} {F : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p fa F B) :
    CtxInv D b j₀ i p (fun t ch ζ => fderiv ℝ (fun h : Vec 2 =>
        fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) 0 (basisVec j)) (dOldF D j₀ i p j F)
      (fun mres h t => derivCost C (D.eps i) Δ mres (B (mres + Δ) h t) +
        (if j = transverseIndex p then ENNReal.ofReal (2 * Real.pi * |(h : ℝ)| / D.eps i)
          else 0) * B mres h t) where
  hol dd n t ht := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
      exact (differentiableOn_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (hF.hol dd n t ht) (cbasis j)).congr fun x _ => dOldF_of hg
    · have : dOldF D j₀ i p j F dd n t = fun _ => 0 := funext fun _ => dOldF_of_not hg
      rw [this]
      exact differentiableOn_const 0
  meas dd n x hx := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
      have h1 := measurable_dAlong (G := fun t : ocPulseWindow D.α D.q D.Λ i p => F dd n t)
        (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ hρ hΦ0 (fun t => hF.hol dd n t t.2)
        (fun y hy => hF.meas dd n y hy) hx (cbasis j)
      convert h1 using 1
      funext t
      exact dOldF_of hg
    · convert measurable_const (a := (0 : ℂ)) using 1
      funext t
      exact dOldF_of_not hg
  agree ch t ht ζ hch := by
    have hdd := chainOK_of_admissible hch
    have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
    obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
    set n := ch.children.length with hn
    set x0 := ch.paramsC ζ with hx0def
    have hx0 : x0 ∈ carrierC D b ch.data n 2 := GenSem.paramsC_mem_carrierC env.hΛ1 env.hb0 hch ζ
    rw [dOldF_of hg]
    have hev : ∀ᶠ h in 𝓝 (0 : Vec 2), ((fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h) : ℝ) : ℂ) =
        F ch.data n t (recOld D i ch.data n x0 (ofRealVec h)) := by
      filter_upwards [recenter_admissible env hch] with h hadm
      have hl := recenter_length (D := D) ch h
      have hP : (ch.recenter D h).paramsN n hl (ζ + (D.eps i)⁻¹ • h) =
          recOld D i ch.data n x0 (ofRealVec h) := by
        rw [← recC_real env hch rfl (ζ + (D.eps i)⁻¹ • h) h hl]
        show recC D ch.data n ((x0.1, x0.2.1, ofRealVec (ζ + (D.eps i)⁻¹ • h)) : ChainParamsC n)
          (ofRealVec h) = _
        rw [recC_final]
        unfold recOld
        refine Prod.ext rfl (Prod.ext rfl ?_)
        rw [ofRealVec_add, ofRealVec_smul]
        rfl
      exact (paramsC_transport (ch.recenter D h) ch.data n (recenter_data ch h) hl _ _ hP
        (fun dd m P => F dd m t P = ((fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h) : ℝ) : ℂ))
        (hF.agree _ t ht _ hadm)).symm
    set U := ball (0 : CVec) (b * D.eps (ch.data.baseLevel + n)) ∩
      (fun w => recOld D i ch.data n x0 w) ⁻¹' carrierC D b ch.data n 2 with hU
    have hUo : IsOpen U := isOpen_alongFib (ComplexFlow.isOpen_carrierC _ _ _ _ _) hΦ hx0
    have h0 : (0 : CVec) ∈ U := ⟨mem_ball_self hρ, by
      show recOld D i ch.data n x0 0 ∈ carrierC D b ch.data n 2
      rw [hΦ0 _ hx0]; exact hx0⟩
    have e0 : ofRealVec (0 : Vec 2) = 0 := by funext a; simp [ofRealVec]
    have hGd : DifferentiableAt ℂ (fun w => F ch.data n t (recOld D i ch.data n x0 w))
        (ofRealVec 0) := by
      rw [e0]
      exact (((hF.hol _ _ t ht).comp (hΦ.comp ((differentiableOn_const _).prodMk
        differentiableOn_id) fun w hw => ⟨hx0, hw.1⟩) fun w hw => hw.2) 0 h0).differentiableAt
          (hUo.mem_nhds h0)
    have h1 := ofReal_fderiv_eq_of_hol (ι := ofRealVec) ofRealVecCLM.hasFDerivAt hGd hev
      (basisVec j)
    rw [h1, e0]
    show _ = fderiv ℂ _ 0 (ofRealVec (basisVec j))
    rw [ofRealVec_basisVec]
    rfl
  fin dd n t ht x hx v hv := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
      rw [dOldF_of hg, dOldF_of hg]
      exact dAlong_congr (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (τ := fun y => y.shiftFinal v) (fun y hy => hF.fin dd n t ht y hy v hv)
        (fun x' w => recOld_shiftFinal D i dd n x' v w) hx (cbasis j)
    · rw [dOldF_of_not hg, dOldF_of_not hg]
  child dd n t ht x hx k v hv := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
      rw [dOldF_of hg, dOldF_of hg]
      exact dAlong_congr (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (τ := fun y => y.shiftChild k v) (fun y hy => hF.child dd n t ht y hy k v hv)
        (fun x' w => recOld_shiftChild env.hΛ1 hg.1 x' k hv w) hx (cbasis j)
    · rw [dOldF_of_not hg, dOldF_of_not hg]
  bdd dd n := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recOld_facts (i := i) env hg
      have h1 := locBdd_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0 (hF.bdd dd n)
        (hF.hol dd n) (w := cbasis j) (by rw [norm_cbasis])
      intro x hx
      obtain ⟨U, hU, M, hM⟩ := h1 x hx
      exact ⟨U, hU, M, fun t ht y hy => by rw [dOldF_of hg]; exact hM t ht y hy⟩
    · exact fun _ _ => ⟨univ, univ_mem, 0, fun t _ y _ => by rw [dOldF_of_not hg, norm_zero]⟩
  mode mres hm0 hm2 k t ht dd n hdd x hx hre := by
    have hg := hdd.goodData
    have hsl := hdd.lastSlot
    have hb0 := env.hb0
    have hΛ1 := env.hΛ1
    set q := transverseIndex p with hq
    by_cases hmΔ : mres + Δ ≤ 2
    swap
    · simp only [derivCost, hmΔ, ↓reduceIte, top_add]
      exact le_top
    have hCpos : C / ENNReal.ofReal (D.eps i * Δ) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨(lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hC).ne',
        ENNReal.ofReal_ne_top⟩
    by_cases htop : B (mres + Δ) k t = ⊤
    · simp only [derivCost, hmΔ, ↓reduceIte, htop, ENNReal.mul_top hCpos, top_add]
      exact le_top
    -- the line and its membership
    have hx2 : x ∈ carrierC D b dd n 2 := carrierC_mono hb0.le hm2 hx
    have hys : ∀ s : ℝ, ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) ∈
        carrierC D b dd n 2 := fun s => by
      have := mem_carrierC_line hx2 (hre _) (z := (s : ℂ)) (by
        simp only [Complex.ofReal_im, abs_zero]; positivity)
      rwa [hsl] at this
    obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
    have hline : Continuous fun s : ℝ => ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) :=
      continuous_const.prodMk (continuous_const.prodMk (continuous_const.add
        (continuous_pi fun a => by unfold evec; split_ifs <;> fun_prop)))
    have hEc : Continuous fun s : ℝ => Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))) := by
      fun_prop
    have hA : DifferentiableOn ℂ (dAlong (recC D dd n) (F dd n t) (cbasis j)) (carrierC D b dd n 2) :=
      differentiableOn_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0 (hF.hol dd n t ht)
        (cbasis j)
    have hP : DifferentiableOn ℂ (fun y => fderiv ℂ (F dd n t) y ((0, 0, cbasis j) : ChainParamsC n))
        (carrierC D b dd n 2) :=
      GenSem.differentiableOn_fderiv_apply (ComplexFlow.isOpen_carrierC D b dd n 2)
        (hF.hol dd n t ht) _
    have hc1 : Continuous fun s : ℝ => dAlong (recC D dd n) (F dd n t) (cbasis j)
        ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) :=
      hA.continuousOn.comp_continuous hline hys
    have hc2 : Continuous fun s : ℝ => fderiv ℂ (F dd n t)
        ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) ((0, 0, cbasis j) : ChainParamsC n) :=
      hP.continuousOn.comp_continuous hline hys
    -- the decomposition of the coefficient
    have hdec : finalPhaseCoeff q (dOldF D j₀ i p j F dd n t) x k =
        finalPhaseCoeff q (dSlowG D j₀ i p j F dd n t) x k + epsInvC D i *
          finalPhaseCoeff q (fun y => fderiv ℂ (F dd n t) y ((0, 0, cbasis j) : ChainParamsC n)) x k := by
      unfold finalPhaseCoeff
      have hc1' : Continuous fun s : ℝ => dSlowG D j₀ i p j F dd n t
          ((x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) : ChainParamsC n) := by
        have e : (fun s : ℝ => dSlowG D j₀ i p j F dd n t
            ((x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) : ChainParamsC n)) =
            fun s : ℝ => dAlong (recC D dd n) (F dd n t) (cbasis j)
              ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) :=
          funext fun s => dSlowG_of hg
        rw [e]
        exact hc1
      have hi1 : IntervalIntegrable (fun s : ℝ => dSlowG D j₀ i p j F dd n t
          ((x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) : ChainParamsC n) *
            Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ)))) MeasureTheory.volume 0 1 :=
        (hc1'.mul hEc).intervalIntegrable 0 1
      have hi2 : IntervalIntegrable (fun s : ℝ => epsInvC D i * (fderiv ℂ (F dd n t)
          ((x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) : ChainParamsC n)
            ((0, 0, cbasis j) : ChainParamsC n) *
              Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))))) MeasureTheory.volume 0 1 :=
        (continuous_const.mul (hc2.mul hEc)).intervalIntegrable 0 1
      rw [← intervalIntegral.integral_const_mul]
      beta_reduce
      rw [← intervalIntegral.integral_add hi1 hi2]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show dOldF D j₀ i p j F dd n t ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) *
          Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))) =
        dSlowG D j₀ i p j F dd n t ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n) *
          Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))) +
        epsInvC D i * (fderiv ℂ (F dd n t) ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n)
          ((0, 0, cbasis j) : ChainParamsC n) * Complex.exp (-(2 * Real.pi * I * (k : ℂ) * (s : ℂ))))
      rw [dOldF_of hg, dAlong_recOld_eq env hg (hF.hol dd n t ht) (hys s) (cbasis j),
        dSlowG_of hg]
      ring
    -- the recentering part
    have hb1 := norm_finalPhaseCoeff_dSlowG_le env hF hm0 hΔ hmΔ k ht hdd hx hre htop j
    have hi : dd.baseLevel + n = i - 1 := by have := hg.2.2; omega
    rw [hi] at hb1
    have hS : LevelScales D b (i - 1) :=
      levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
        (by have := hg.1.base; have := hg.2.2; omega)
    have hεi : D.eps i ≤ D.eps (i - 1) := by
      have h1 := hS.heps
      have e : i - 1 + 1 = i := by have := hg.2.2; omega
      rw [e] at h1
      have : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
      linarith
    have hpart1 : ENNReal.ofReal ‖finalPhaseCoeff q (dSlowG D j₀ i p j F dd n t) x k‖ ≤
        derivCost C (D.eps i) Δ mres (B (mres + Δ) k t) := by
      refine (enorm_le_derivCost hb0 (Construction.Stream.ocEpsilon_pos hΛ1) hΔ hC hmΔ hb1
        htop).trans ?_
      simp only [derivCost, hmΔ, ↓reduceIte]
      gcongr
      exact hεi
    -- the final-phase part
    have hpart2 : ‖epsInvC D i * finalPhaseCoeff q
        (fun y => fderiv ℂ (F dd n t) y ((0, 0, cbasis j) : ChainParamsC n)) x k‖ₑ ≤
        (if j = q then ENNReal.ofReal (2 * Real.pi * |(k : ℝ)| / D.eps i) else 0) * B mres k t := by
      by_cases hj : j = q
      · subst hj
        simp only [↓reduceIte]
        have hdir : ((0, 0, cbasis q) : ChainParamsC n) = phaseDir n q := by
          refine Prod.ext rfl (Prod.ext rfl ?_)
          funext a
          simp only [phaseDir, evec, cbasis, Pi.single_apply]
        have hfun : (fun y => fderiv ℂ (F dd n t) y ((0, 0, cbasis q) : ChainParamsC n)) =
            dPhaseF q F dd n t := by
          funext y; rw [hdir]; rfl
        rw [hfun, enorm_mul]
        have h2 := (CtxInv.dPhase hΛ1 hb0 hF).mode mres hm0 hm2 k t ht dd n hdd x hx hre
        have hεpos : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
        have hε : ‖epsInvC D i‖ₑ = ENNReal.ofReal (D.eps i)⁻¹ := by
          rw [epsInvC, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hεpos)]
        rw [hε]
        calc ENNReal.ofReal (D.eps i)⁻¹ * ‖finalPhaseCoeff q (dPhaseF q F dd n t) x k‖ₑ
            ≤ ENNReal.ofReal (D.eps i)⁻¹ * (modeMul k * B mres k t) := mul_le_mul' le_rfl h2
          _ = ENNReal.ofReal (2 * Real.pi * |(k : ℝ)| / D.eps i) * B mres k t := by
            rw [← mul_assoc, modeMul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hεpos.le)]
            congr 2
            field_simp
      · simp only [hj, ↓reduceIte, zero_mul]
        have hz : ∀ s : ℝ, fderiv ℂ (F dd n t) ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) :
            ChainParamsC n) ((0, 0, cbasis j) : ChainParamsC n) = 0 := fun s =>
          fderiv_final_eq_zero (ComplexFlow.isOpen_carrierC D b dd n 2) (hF.hol dd n t ht)
            (pq := dd.slots.getLastD 0) (fun y hy v hv => hF.fin dd n t ht y hy v hv) (hys s)
            (by rw [hsl]; exact hj)
        have : finalPhaseCoeff q (fun y => fderiv ℂ (F dd n t) y ((0, 0, cbasis j) : ChainParamsC n))
            x k = 0 := by
          unfold finalPhaseCoeff
          refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s _ => ?_).trans
            intervalIntegral.integral_zero
          show fderiv ℂ (F dd n t) ((x.1, x.2.1, x.2.2 + evec q (s : ℂ)) : ChainParamsC n)
            ((0, 0, cbasis j) : ChainParamsC n) * _ = 0
          rw [hz s, zero_mul]
        rw [this, mul_zero, enorm_zero]
    rw [hdec]
    refine (enorm_add_le _ _).trans (add_le_add ?_ hpart2)
    rw [← ofReal_norm]
    exact hpart1

end AVRegularity.Providers.ComplexContext
end
end

section
/-! **Carrier calculus: the child-frame letters** `F^♮_t(0)`, `(F^♮_t(0))⁻¹`, `𝒢^♮_t(0)`
(`geo (child 𝗉')`). Over the slot `𝗉` of level `i`, the letter of the child `𝒜^♮` appended for
the finer slot `𝗉'` is gated by the cutoff `ϖ_{i+1,𝗉'}(t)`: where the cutoff vanishes it takes the
identity value `δ_ac`. A function `Φ` of the Jacobian (`EntryFun`) gives the extension
`childLeafExt`: on scheduled data, the outer carrier and the support of the cutoff, `Φ` of the
complex Jacobian of the extended appended child `appFamX` at `(x, λ(t))`; zero elsewhere.
* holomorphy: `appFamX` is over the finer slot on `𝔇_i(2;𝗉) × B(0, λ_R)` (`appFamX_over`);
* measurability in time: the Jacobian at the moving parameter `(x, λ(t))`
  (`CFam.measurable_jacC_moving`, `continuous_lamT`);
* agreement: `jacC_appFam_real`;
* symmetries: `appFamX_toGeom_shiftFinal`, `appFamX_toGeom_shiftChild`;
* modes: the extension is at most `B(m)`, `m = K a_i (6/5) h_{i+1}`, on the outer carrier, and it
  is periodic and holomorphic along the final-phase strip `|Im z| < 7b/2`, so its modes are at most
  `B(m) e^{-6πb|h|}` (`ctxMode_le_of_uniform`).
With `δ_ac` and the smallness `m ≤ 1/100`, every child-frame letter other than the strain has the
profile `2 e^{-6πb|h|}` (`CtxInv.geoChild`). -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal

namespace AVRegularity.Providers.ComplexFlow

/-- **Measurability in time of the Jacobian at a moving parameter.** -/
theorem CFam.measurable_jacC_moving {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
    {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ} (h : F.OK Ω W ϱ Λ T)
    (hc : F.TimeCont Ω W ϱ) {P : ℝ → Par} {S : Set ℝ} (hS : S ⊆ W) (hP : ContinuousOn P S)
    (hPΩ : ∀ t ∈ S, P t ∈ Ω) (a c : Fin 2) :
    Measurable fun t : S => F.jacC (P t) t a c := by
  have hcc : ContinuousOn (fun t => F.ctr (P t)) S := h.ctr_hol.continuousOn.comp hP hPΩ
  have hcont : ContinuousOn (fun q : ℝ × CVec => F.fl (P q.1) q.1 q.2 F.anc)
      {q | q.1 ∈ S ∧ q.2 ∈ ball (F.ctr (P q.1)) ϱ} := by
    refine (hc F.anc h.anc_mem).comp
      ((hP.comp continuousOn_fst fun q hq => hq.1).prodMk
        (continuousOn_fst.prodMk continuousOn_snd)) fun q hq => ⟨hPΩ q.1 hq.1, hS hq.1, ?_⟩
    show q.2 ∈ ball (F.cur (P q.1) F.anc) ϱ
    rw [h.cur_anc _ (hPΩ q.1 hq.1)]
    exact hq.2
  have hm := measurable_fderiv_moving (g := fun t y => F.fl (P t) t y F.anc)
    (c := fun t => F.ctr (P t)) h.hϱ hcc hcont (fun t ht =>
      h.differentiableAt_fl (hPΩ t ht) (hS ht) h.anc_mem
        (by rw [h.cur_anc _ (hPΩ t ht)]; exact mem_ball_self h.hϱ)) subset_rfl (cbasis c)
  exact (measurable_pi_apply a).comp hm

variable {D : OCData}

/-- The displacement scalar is continuous in time. -/
theorem continuous_lamT (hζ : IsFastProfile D.ζ) (dd : ChainData) (n : ℕ) (p' : ℤ) :
    Continuous (lamT D dd n p') := by
  have hf := continuous_ocPulse D hζ (appLevel dd n) (appSlot dd)
  have e : (fun t => ∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
      ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v) = fun t =>
      -∫ v in D.slotAnchor (appLevel dd n + 1) p'..t,
        ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v :=
    funext fun t => intervalIntegral.integral_symm _ _
  have h1 : Continuous fun t => ∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
      ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v := by
    rw [e]
    exact (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) _).neg
  unfold lamT
  exact Complex.continuous_ofReal.comp (continuous_const.mul h1)

end AVRegularity.Providers.ComplexFlow

namespace AVRegularity.Providers.ComplexContext

open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p p' : ℤ}

/-! ### Modes from a uniform bound -/

/-- **The final-phase modes of a bounded symmetric extension**: an extension holomorphic on the
outer carrier, invariant under the final-phase translations and at most `c` there has final-phase
modes at most `c e^{-6πb|h|}`. -/
theorem ctxMode_le_of_uniform (hb : 0 < b) {F : Ext} {c : ℝ}
    (hhol : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
      DifferentiableOn ℂ (F dd n t) (carrierC D b dd n 2))
    (hfin : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
      FinalSymm dd (F dd n t) (carrierC D b dd n 2))
    (hbd : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x, x ∈ carrierC D b dd n 2 →
      ‖F dd n t x‖ ≤ c)
    {mres : ℝ} (hm2 : mres ≤ 2) (h : ℤ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    {dd : ChainData} {n : ℕ} (hdd : AdmData D b j₀ i p dd n) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n mres) (hre : RealFinal x) :
    ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ ≤
      ENNReal.ofReal (c * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) := by
  have hsl := hdd.lastSlot
  have hx2 := carrierC_mono hb.le hm2 hx
  set q := transverseIndex p with hq
  set g : ℂ → ℂ := fun z => F dd n t (x.1, x.2.1, x.2.2 + evec q z) with hgdef
  have hmem : ∀ z : ℂ, |z.im| < (3 + 2 / 4) * b →
      ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) ∈ carrierC D b dd n 2 := by
    intro z hz
    have := mem_carrierC_line hx2 (hre _) hz
    rwa [hsl] at this
  have hl : Differentiable ℂ fun z : ℂ => ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) := by
    refine (differentiable_const _).prodMk ((differentiable_const _).prodMk ?_)
    refine (differentiable_const _).add ?_
    rw [differentiable_pi]
    intro a
    unfold evec
    split_ifs
    · exact differentiable_id
    · exact differentiable_const _
  have hgd : DifferentiableOn ℂ g {z : ℂ | |z.im| < (3 + 2 / 4) * b} :=
    (hhol dd n t ht).comp hl.differentiableOn fun z hz => hmem z hz
  have hgp : ∀ z : ℂ, |z.im| < (3 + 2 / 4) * b → g (z + 1) = g z := by
    intro z hz
    simp only [hgdef]
    rw [← shiftFinal_line]
    exact hfin dd n t ht _ (hmem z hz) (rvec q) (tInt_rvec_any _ q)
  have hgb : ∀ z : ℂ, |z.im| < (3 + 2 / 4) * b → ‖g z‖ ≤ c := fun z hz => hbd dd n t ht _ (hmem z hz)
  have hdec := norm_pcoeff_le_of_strip hgd hgp hgb h (w' := 3 * b) (by positivity) (by linarith)
  rw [finalPhaseCoeff_eq_pcoeff, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (hdec.trans (le_of_eq ?_))
  congr 2
  ring

/-! ### The extension of a gated child-frame leaf -/

theorem ownSize_nonneg (env : ChainEnv D b CH Υ j₀) (k : ℕ) : 0 ≤ ownSize D k := by
  unfold ownSize
  exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
    (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le _))
    (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos env.hΛ1).le)

open scoped Classical in
/-- **The extension of a gated child-frame leaf** `Φ(F^♮_t(0))` over the slot `𝗉` of level `i`,
for the child appended for the finer slot `𝗉'`. -/
def childLeafExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p p' : ℤ)
    (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) : Ext :=
  fun dd n t x =>
    if GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 ∧ ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0
    then Φ ((appFamX D dd n p').jacC (x, lamT D dd n p' t) t) else 0

theorem childLeafExt_of {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {dd : ChainData} {n : ℕ} {t : ℝ}
    {x : ChainParamsC n} (hg : GoodData D j₀ i p dd n) (hx : x ∈ carrierC D b dd n 2)
    (hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0) :
    childLeafExt D b j₀ i p p' Φ dd n t x =
      Φ ((appFamX D dd n p').jacC (x, lamT D dd n p' t) t) := by
  unfold childLeafExt
  split_ifs with h
  · rfl
  · exact (h ⟨hg, hx, hcut⟩).elim

theorem childLeafExt_of_not {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {dd : ChainData} {n : ℕ} {t : ℝ}
    {x : ChainParamsC n}
    (h : ¬(GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 ∧
      ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0)) :
    childLeafExt D b j₀ i p p' Φ dd n t x = 0 := by
  unfold childLeafExt
  split_ifs with h'
  · exact (h h').elim
  · rfl

/-- The extended appended child of good data is over the finer slot. -/
theorem goodData_appFamX_over (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) (hsch : IsScheduledIn D i p' p) :
    (appFamX D dd n p').Over D b (appOmega D b dd n) i p' := by
  have hlev : appLevel dd n = i := hg.2.2
  have h := ComplexFlow.appFamX_over env hg.1 (p' := p')
    (by rw [hlev, show appSlot dd = p from hg.2.1]; exact hsch)
  rwa [hlev] at h

/-- **The size of a gated child-frame leaf**, uniformly. -/
theorem norm_childLeafExt_le (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (dd : ChainData) (n : ℕ) (t : ℝ) (x : ChainParamsC n) :
    ‖childLeafExt D b j₀ i p p' Φ dd n t x‖ ≤ B (ownSize D (i + 1)) := by
  have hΛ1 := env.hΛ1
  by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 ∧
      ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0
  · obtain ⟨hg, hx, hcut⟩ := hgx
    have hO := goodData_appFamX_over env hg hsch
    have ht := mem_slotWin_of_cutoff D hΛ1 hcut
    have hP : ((x, lamT D dd n p' t) : ChainParamsC n × ℂ) ∈ appOmega D b dd n :=
      ⟨hx, lamT_mem env.hζ hΛ1 (dd := dd) (n := n) (p' := p') (t := t)
        (by rw [show appLevel dd n = i from hg.2.2]; exact ht)⟩
    have hr := CFam.rowSmall_jacC hO.ok hP ht
    have hmle := mul_le_mul_of_nonneg_left (hO.ok.hT t ht _ hO.ok.anc_mem) hO.ok.hΛ
    have h1 := hΦ.bd _ _ (hr.mono hmle) hO.ok.hΛT
    rw [add_sub_cancel] at h1
    rw [childLeafExt_of hg hx hcut]
    convert h1 using 2
    unfold ownSize
    rw [Nat.add_sub_cancel]
  · rw [childLeafExt_of_not hgx, norm_zero]
    exact hΦ.B_nonneg _ (ownSize_nonneg env _)

/-- **A gated child-frame leaf is holomorphic** on the outer carrier. -/
theorem childLeafExt_hol (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (dd : ChainData) (n : ℕ) (t : ℝ) :
    DifferentiableOn ℂ (childLeafExt D b j₀ i p p' Φ dd n t) (carrierC D b dd n 2) := by
  have hΛ1 := env.hΛ1
  by_cases hgc : GoodData D j₀ i p dd n ∧ ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0
  · obtain ⟨hg, hcut⟩ := hgc
    have hO := goodData_appFamX_over env hg hsch
    have ht := mem_slotWin_of_cutoff D hΛ1 hcut
    have hlam := lamT_mem env.hζ hΛ1 (dd := dd) (n := n) (p' := p') (t := t)
      (by rw [show appLevel dd n = i from hg.2.2]; exact ht)
    have hmap : MapsTo (fun x : ChainParamsC n => ((x, lamT D dd n p' t) : ChainParamsC n × ℂ))
        (carrierC D b dd n 2) (appOmega D b dd n) := fun x hx => ⟨hx, hlam⟩
    have hd := hΦ.hol n (carrierC D b dd n 2)
      (fun x => (appFamX D dd n p').jacC (x, lamT D dd n p' t) t)
      (fun a c => (CFam.differentiableOn_jacC hO.ok ht a c).comp
        (differentiableOn_id.prodMk (differentiableOn_const _)) hmap)
      (fun x hx => CFam.det_jacC_ne_zero hO.ok (hmap hx) ht)
    exact hd.congr fun x hx => childLeafExt_of hg hx hcut
  · have : childLeafExt D b j₀ i p p' Φ dd n t = fun _ => 0 := by
      funext x
      exact childLeafExt_of_not fun h => hgc ⟨h.1, h.2.2⟩
    rw [this]
    exact differentiableOn_const 0

/-- **A gated child-frame leaf is measurable in time** on the outer carrier. -/
theorem childLeafExt_meas (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (dd : ChainData) (n : ℕ) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) :
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => childLeafExt D b j₀ i p p' Φ dd n t x := by
  have hΛ1 := env.hΛ1
  by_cases hg : GoodData D j₀ i p dd n
  · have hO := goodData_appFamX_over env hg hsch
    have hcutc : Continuous fun t : ℝ => ocCutoff D.α D.q D.Λ (i + 1) p' t := by
      unfold ocCutoff; exact Real.smoothTransition.continuous.comp (by fun_prop)
    set S' : Set ℝ := {t | ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0} with hS'
    have hS'W : S' ⊆ slotWin D (i + 1) p' := fun t ht => mem_slotWin_of_cutoff D hΛ1 ht
    have hlam : ∀ t ∈ S', ((x, lamT D dd n p' t) : ChainParamsC n × ℂ) ∈ appOmega D b dd n :=
      fun t ht => ⟨hx, lamT_mem env.hζ hΛ1 (dd := dd) (n := n) (p' := p') (t := t)
        (by rw [show appLevel dd n = i from hg.2.2]; exact hS'W ht)⟩
    have hPc : ContinuousOn (fun t : ℝ => ((x, lamT D dd n p' t) : ChainParamsC n × ℂ)) S' :=
      (continuous_const.prodMk (continuous_lamT env.hζ dd n p')).continuousOn
    have hM : Measurable fun t : S' => (appFamX D dd n p').jacC (x, lamT D dd n p' t) t :=
      measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c =>
        CFam.measurable_jacC_moving hO.ok hO.cont hS'W hPc hlam a c
    set S : Set (ocPulseWindow D.α D.q D.Λ i p) :=
      {t | ocCutoff D.α D.q D.Λ (i + 1) p' (t : ℝ) ≠ 0} with hS
    have hSm : MeasurableSet S :=
      (isOpen_ne_fun (hcutc.comp continuous_subtype_val) continuous_const).measurableSet
    refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
    · have hι : Continuous fun t : S => (⟨(t : ℝ), t.2⟩ : S') :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      convert (hΦ.meas.comp hM).comp hι.measurable using 1
      funext t
      exact childLeafExt_of hg hx t.2
    · convert measurable_const (a := (0 : ℂ)) using 1
      funext t
      exact childLeafExt_of_not fun h =>
        (show ¬(ocCutoff D.α D.q D.Λ (i + 1) p' (t : ℝ) ≠ 0) from t.2) h.2.2
  · convert measurable_const (a := (0 : ℂ)) using 1
    funext t
    exact childLeafExt_of_not fun h => hg h.1

/-- **A gated child-frame leaf agrees with the real letter** at the admissible chains. -/
theorem childLeafExt_agree (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) {ch : RealChain} (hch : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2)
    (t : ℝ) :
    childLeafExt D b j₀ i p p' Φ ch.data ch.children.length t (ch.paramsC ζ) =
      ((if ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0 then
        φ ((ch.appendChild D p' t ζ).famJac D t) else 0 : ℝ) : ℂ) := by
  have hΛ1 := env.hΛ1
  have hg : GoodData D j₀ i p ch.data ch.children.length :=
    ⟨chainOK_of_admissible hch, hch.2.2.2.1, hch.1⟩
  have hx := GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
  by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
  · rw [childLeafExt_of_not fun h => h.2.2 hcut]
    split_ifs with h
    · exact absurd hcut h
    · simp
  · rw [childLeafExt_of hg hx hcut]
    have hJ : (appFamX D ch.data ch.children.length p').jacC
        (ch.paramsC ζ, lamT D ch.data ch.children.length p' t) t =
        ((ch.appendChild D p' t ζ).famJac D t).map fun r : ℝ => (r : ℂ) := by
      ext a c
      rw [← appFam_jacC_eq]
      exact jacC_appFam_real env hch hsch ζ (mem_slotWin_of_cutoff D hΛ1 hcut) a c
    split_ifs with h
    · rw [hJ, hΦ.real]
    · exact absurd hcut h

/-- A gated child-frame leaf does not see the final-phase translations. -/
theorem childLeafExt_shiftFinal (hΛ : 1 ≤ D.Λ) (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {dd : ChainData} {n : ℕ} (t : ℝ) (x : ChainParamsC n) {v : Vec 2}
    (hv : TInt (dd.slots.getLastD 0) v) :
    childLeafExt D b j₀ i p p' Φ dd n t (x.shiftFinal v) =
      childLeafExt D b j₀ i p p' Φ dd n t x := by
  have e : (appFamX D dd n p').jacC (x.shiftFinal v, lamT D dd n p' t) t =
      (appFamX D dd n p').jacC (x, lamT D dd n p' t) t :=
    jacC_of_toGeom (appFamX_toGeom_shiftFinal hΛ dd n p' (x, lamT D dd n p' t) hv) t
  unfold childLeafExt
  rw [mem_carrierC_shiftFinal_iff, e]

/-- A gated child-frame leaf does not see the child-phase translations. -/
theorem childLeafExt_shiftChild (hΛ : 1 ≤ D.Λ) (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {dd : ChainData} {n : ℕ} (t : ℝ) (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : TInt (dd.slots.getD k 0) v) :
    childLeafExt D b j₀ i p p' Φ dd n t (x.shiftChild k v) =
      childLeafExt D b j₀ i p p' Φ dd n t x := by
  have e : (appFamX D dd n p').jacC (x.shiftChild k v, lamT D dd n p' t) t =
      (appFamX D dd n p').jacC (x, lamT D dd n p' t) t :=
    jacC_of_toGeom (appFamX_toGeom_shiftChild hΛ dd n p' (x, lamT D dd n p' t) k hv) t
  unfold childLeafExt
  rw [mem_carrierC_shiftChild_iff, e]

/-- **A gated child-frame leaf**: the invariant with the profile `B(m) e^{-6πb|h|}`. -/
theorem CtxInv.childLeaf (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) :
    CtxInv D b j₀ i p
      (fun t ch ζ => if ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0 then
        φ ((ch.appendChild D p' t ζ).famJac D t) else 0)
      (childLeafExt D b j₀ i p p' Φ)
      (fun _ h _ => ENNReal.ofReal (B (ownSize D (i + 1)) *
        Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))) where
  hol dd n t _ := childLeafExt_hol env hsch hΦ dd n t
  meas dd n _ hx := childLeafExt_meas env hsch hΦ dd n hx
  agree _ t _ ζ hch := childLeafExt_agree env hsch hΦ hch ζ t
  fin _ _ t _ x _ _ hv := childLeafExt_shiftFinal env.hΛ1 Φ t x hv
  child _ _ t _ x _ k _ hv := childLeafExt_shiftChild env.hΛ1 Φ t x k hv
  bdd dd n _ _ := ⟨univ, univ_mem, _, fun t _ y _ => norm_childLeafExt_le env hsch hΦ dd n t y⟩
  mode _ _ hm2 h _ ht _ _ hdd _ hx hre :=
    ctxMode_le_of_uniform env.hb0 (fun dd n t _ => childLeafExt_hol env hsch hΦ dd n t)
      (fun _ _ t _ x _ _ hv => childLeafExt_shiftFinal env.hΛ1 Φ t x hv)
      (fun dd n t _ x _ => norm_childLeafExt_le env hsch hΦ dd n t x) hm2 h ht hdd hx hre

/-! ### The child-frame letters -/

theorem abs_idVal_le (L : GeoLetter) : |L.idVal| ≤ 1 := by
  cases L <;> simp only [GeoLetter.idVal] <;> (try split_ifs) <;> simp

/-- **A child-frame letter given by an entry function** of the Jacobian, with the profile
`2 e^{-6πb|h|}`. -/
theorem CtxInv.geoChild_of (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (hB : B (ownSize D (i + 1)) ≤ 1) (L : GeoLetter)
    (hL : L.isStrain = false) (hφ : ∀ (ch : RealChain) (u : ℝ),
      L.evalAt D ch u = φ (ch.famJac D u) + L.idVal) :
    ∃ F, CtxInv D b j₀ i p (GeoLetter.eval D i (.child p') L) F
      (fun _ h _ => ENNReal.ofReal (2 * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))) := by
  have h1 := (CtxInv.childLeaf env hsch hΦ).add env.hb0
    (CtxInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p)
      (L := TimeLetter.const L.idVal) continuous_const)
  refine ⟨_, (h1.congr fun t _ ch _ ζ => ?_).mono fun mres h t _ _ _ => ?_⟩
  · by_cases hc : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
    · simp [GenSort.add, GenSort.ofTime, TimeLetter.eval, GeoLetter.eval, hL, hc]
    · simp [GenSort.add, GenSort.ofTime, TimeLetter.eval, GeoLetter.eval, hL, hc, hφ]
  · have hB0 : 0 ≤ B (ownSize D (i + 1)) := hΦ.B_nonneg _ (ownSize_nonneg env _)
    have he : 0 < Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)) := Real.exp_pos _
    split_ifs with h0
    · subst h0
      have hv : |(TimeLetter.const L.idVal).eval D t| ≤ 1 := abs_idVal_le L
      rw [← ENNReal.ofReal_add (mul_nonneg hB0 he.le) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [Int.cast_zero, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      linarith
    · rw [add_zero]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_right hB he.le
      linarith

/-- **The child-frame letters other than the strain**, with the profile `2 e^{-6πb|h|}` under the
smallness `K a_i (6/5) h_{i+1} ≤ 1/100`. -/
theorem CtxInv.geoChild (env : ChainEnv D b CH Υ j₀) (hsch : IsScheduledIn D i p' p)
    (hm : ownSize D (i + 1) ≤ 1 / 100) (L : GeoLetter) (hL : L.isStrain = false) :
    ∃ F, CtxInv D b j₀ i p (GeoLetter.eval D i (.child p') L) F
      (fun _ h _ => ENNReal.ofReal (2 * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))) := by
  have hm0 := ownSize_nonneg env (i + 1)
  cases L with
  | jac a c =>
    exact CtxInv.geoChild_of env hsch (jacSub_entryFun a c)
      (by show ownSize D (i + 1) ≤ 1; linarith) _ hL
      (fun ch u => by simp only [GeoLetter.evalAt, GeoLetter.idVal]; ring)
  | jacInv a c =>
    exact CtxInv.geoChild_of env hsch (invSub_entryFun a c)
      ((invB_le hm0 hm).trans (by norm_num)) _ hL
      (fun ch u => by simp only [GeoLetter.evalAt, GeoLetter.idVal]; ring)
  | metric a c =>
    exact CtxInv.geoChild_of env hsch (metricSub_entryFun a c)
      ((metricB_le hm0 hm).trans (by norm_num)) _ hL
      (fun ch u => by simp only [GeoLetter.evalAt, GeoLetter.idVal, RealChain.famMetric]; ring)
  | strain a c => simp [GeoLetter.isStrain] at hL

end AVRegularity.Providers.ComplexContext
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the strain of a complex family.** The strain entry
`(∂_uF_u F_u⁻¹)_{ac}` at `u = t` (`strainEnt`) of a family with a velocity equals the entry of the
strain matrix `DV_P(t, c_P(t))` when the window is a neighborhood of `t` (`strainEnt_eq`); it is
therefore holomorphic in the parameters and bounded by the two-time rate (`norm_strainEnt_le`).
Where the complex Jacobians are the real ones, it is the real strain entry (`strainEnt_real`).
The output windows and the supports of the cutoffs lie in the interior of the slot windows
(`slotWin_mem_nhds_of_window`, `slotWin_mem_nhds_of_cutoff`). -/

section
open AVRegularity.Providers.ComplexFlow

/-! ### Windows -/

theorem slotWin_mem_nhds_of_window {D : OCData} (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) : slotWin D i p ∈ 𝓝 t := by
  have h1 := abs_le.mp (abs_sub_anchor_le_of_mem_window D hΛ ht)
  have h2 := tau_le D hΛ i
  have hh : 0 < ocTauPP D.α D.q D.Λ i := Construction.Stream.ocTauPP_pos hΛ
  exact Icc_mem_nhds (by linarith [h1.1]) (by linarith [h1.2])

theorem slotWin_mem_nhds_of_cutoff {D : OCData} (hΛ : 1 ≤ D.Λ) {k : ℕ} {p : ℤ} {t : ℝ}
    (hc : ocCutoff D.α D.q D.Λ k p t ≠ 0) : slotWin D k p ∈ 𝓝 t := by
  have h1 := abs_lt.mp (abs_sub_anchor_lt_of_cutoff D hΛ hc)
  have h2 := tau_le D hΛ k
  have hh : 0 < ocTauPP D.α D.q D.Λ k := Construction.Stream.ocTauPP_pos hΛ
  exact Icc_mem_nhds (by linarith [h1.1]) (by linarith [h1.2])

theorem neBot_of_mem_nhds {W : Set ℝ} {t : ℝ} (hW : W ∈ 𝓝 t) : (𝓝[W \ {t}] t).NeBot := by
  rw [sdiff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hW)]
  infer_instance

/-! ### The strain entry -/

/-- **The strain entry** `(∂_uF_u F_u⁻¹)_{ac}` at `u = t` of a family at the parameters `P`. -/
def strainEnt {Par : Type*} (G : CFam Par) (P : Par) (t : ℝ) (a c : Fin 2) : ℂ :=
  ((Matrix.of fun a c => deriv (fun u => G.jacC P u a c) t) * (G.jacC P t)⁻¹) a c

section Strain

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par] {G : CFam Par} {Ω : Set Par}
  {W : Set ℝ} {ϱ Λ T : ℝ} {Vel : Par → ℝ → CVec → CVec}

/-- **The strain entry is the entry of the strain matrix.** -/
theorem strainEnt_eq (h : G.OK Ω W ϱ Λ T) (hV : G.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hW : W ∈ 𝓝 t) (a c : Fin 2) :
    strainEnt G P t a c = G.strainMat Vel P t a c := by
  have hdet : IsUnit (G.jacC P t).det := (CFam.det_jacC_ne_zero h hP ht).isUnit
  have e : (Matrix.of fun a c => deriv (fun u => G.jacC P u a c) t) =
      G.strainMat Vel P t * G.jacC P t := by
    ext a c
    exact ((hV.hasDerivWithinAt_jacC h hP ht a c).hasDerivAt hW).deriv
  unfold strainEnt
  rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

/-- **The strain entry is bounded by the two-time rate.** -/
theorem norm_strainEnt_le (h : G.OK Ω W ϱ Λ T) (hV : G.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hW : W ∈ 𝓝 t) (a c : Fin 2) : ‖strainEnt G P t a c‖ ≤ Λ := by
  rw [strainEnt_eq h hV hP ht hW]
  exact hV.norm_strainMat_le h hP ht (neBot_of_mem_nhds hW) a c

/-- **The strain entry is holomorphic in the parameters.** -/
theorem differentiableOn_strainEnt [FiniteDimensional ℂ Par] (h : G.OK Ω W ϱ Λ T)
    (hV : G.VelOK Ω W ϱ Vel) {t : ℝ} (ht : t ∈ W) (hW : W ∈ 𝓝 t) (a c : Fin 2) :
    DifferentiableOn ℂ (fun P => strainEnt G P t a c) Ω :=
  (hV.differentiableOn_strainMat h ht a c).congr fun _ hP => strainEnt_eq h hV hP ht hW a c

/-- **At real Jacobians the strain entry is the real one.** -/
theorem strainEnt_real (h : G.OK Ω W ϱ Λ T) (hV : G.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hW : W ∈ 𝓝 t) {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : ∀ u ∈ W, ∀ a c, G.jacC P u a c = ((M u a c : ℝ) : ℂ)) (a c : Fin 2) :
    strainEnt G P t a c =
      (((Matrix.of fun a c => deriv (fun u => M u a c) t) * (M t)⁻¹) a c : ℝ) := by
  have hderiv : ∀ a c, deriv (fun u => G.jacC P u a c) t = ((deriv (fun u => M u a c) t : ℝ) : ℂ) := by
    intro a c
    have hg := (hV.hasDerivWithinAt_jacC h hP ht a c).hasDerivAt hW
    set z := (G.strainMat Vel P t * G.jacC P t) a c with hz
    have hev : (fun u => G.jacC P u a c) =ᶠ[𝓝 t] fun u => ((M u a c : ℝ) : ℂ) := by
      filter_upwards [hW] with u hu
      exact hM u hu a c
    have hg' : HasDerivAt (fun u => ((M u a c : ℝ) : ℂ)) z t := hg.congr_of_eventuallyEq hev.symm
    have hre : HasDerivAt (fun u => M u a c) z.re t := by
      have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg'
      refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).congr_deriv ?_
      · simp
      · simp
    have hz' : z = ((z.re : ℝ) : ℂ) := hg'.unique hre.ofReal_comp
    rw [hg.deriv, hre.deriv, ← hz']
  have hJ : G.jacC P t = (M t).map fun r : ℝ => (r : ℂ) := by
    ext a c
    exact hM t ht a c
  unfold strainEnt
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.of_apply, Matrix.of_apply, hderiv a b, hJ, inv_map_ofReal]

end Strain
end

/-! **Carrier calculus: the metric entry of the transverse inverse.** The complex extension of
`𝒢_qq` used by `CellInv.cellInv` is the complex-chain leaf of `𝒢 − I` plus one, evaluated at the
final phase `0` (the family does not depend on the final phase, and this makes the extension
independent of it off the carrier as well): `metricExtOf`. Under the smallness `m ≤ 1/100` of the
carrier start, `|𝒢_qq − 1| ≤ 1/10`, so `Re 𝒢_qq ≥ 9/10` (`metricExtOf_spec`). -/

section
open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- The parameters with the final phase set to zero. -/
def finalZero {n : ℕ} (x : ChainParamsC n) : ChainParamsC n := (x.1, x.2.1, 0)

theorem differentiable_finalZero (n : ℕ) : Differentiable ℂ (finalZero (n := n)) := by
  unfold finalZero
  exact differentiable_fst.prodMk (differentiable_snd.fst.prodMk (differentiable_const _))

/-- The entry `(q,q)` of `𝒢 − I` as a function of the Jacobian. -/
def metricQQ (q : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ → ℂ :=
  fun A => (A⁻¹ * A⁻¹.transpose) q q - (if q = q then 1 else 0)

/-- **The extension of the metric entry `𝒢_qq`** over the slot `p` of level `i`. -/
def metricExtOf (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) : Ext :=
  fun dd n u x => ownLeafExt D b j₀ i p (metricQQ (transverseIndex p)) dd n u (finalZero x) + 1

theorem metricExtOf_spec (env : ChainEnv D b CH Υ j₀) (hm : ownSize D i ≤ 1 / 100) :
    MetricExt D b j₀ i p (metricExtOf D b j₀ i p) := by
  classical
  set q := transverseIndex p
  have hΦ := metricSub_entryFun q q
  have hext := ownLeaf_isHolExtension env i p hΦ
  have hm0 : 0 ≤ ownSize D i := by
    unfold ownSize
    exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos env.hΛ1).le)
  have hsmall : ∀ dd n, ∀ u ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ x : ChainParamsC n,
      ‖ownLeafExt D b j₀ i p (metricQQ q) dd n u x‖ ≤ 1 / 10 := fun dd n u hu x =>
    (norm_ownLeafExt_le env i p hΦ dd n hu x).trans (by unfold ownSize at hm hm0; exact metricB_le hm0 hm)
  have hfz : ∀ dd n x, x ∈ carrierC D b dd n 2 → finalZero x ∈ carrierC D b dd n 2 :=
    fun dd n x hx => carrierC_final_zero (by norm_num) hx env.hb0
  refine ⟨fun dd n u hu => ?_, fun dd n x _ => ?_, fun dd n u x z => rfl,
    fun dd n u hu x hx k v hv => ?_, fun dd n u hu x hx => ?_, fun dd n u hu x hx => ?_,
    fun ch u hu hch => ?_⟩
  · exact ((hext.1 dd n u hu).comp (differentiable_finalZero n).differentiableOn
      fun x hx => hfz dd n x hx).add_const 1
  · exact (hext.2.1.1 dd n (finalZero x)).add_const 1
  · show ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero (x.shiftChild k v)) + 1 =
      ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero x) + 1
    rw [show finalZero (x.shiftChild k v) = (finalZero x).shiftChild k v from rfl,
      ownLeafExt_shiftChild env.hΛ1 _ u _ k hv]
  · show 9 / 10 ≤ (ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero x) + 1).re
    have h1 := hsmall dd n u hu (finalZero x)
    have h2 := Complex.abs_re_le_norm (ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero x))
    rw [Complex.add_re, Complex.one_re]
    have := neg_abs_le (ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero x)).re
    linarith
  · show ‖ownLeafExt D b j₀ i p (metricQQ q) dd n u (finalZero x) + 1‖ ≤ 2
    refine (norm_add_le _ _).trans ?_
    have := hsmall dd n u hu (finalZero x)
    simp only [norm_one]
    linarith
  · show ownLeafExt D b j₀ i p (metricQQ q) ch.data ch.children.length u
      (finalZero (ch.paramsC 0)) + 1 = _
    have hz : finalZero (ch.paramsC 0) = ch.paramsC 0 := by
      refine Prod.ext rfl (Prod.ext rfl (funext fun a => ?_))
      simp [finalZero, RealChain.paramsC]
    rw [hz]
    unfold metricQQ
    rw [hext.2.2 ch u hu 0 hch]
    simp [RealChain.famMetric, q]
end

end AVRegularity.Providers.ComplexContext
end
end
