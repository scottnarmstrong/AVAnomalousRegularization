-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.Inv
import AVRegularity.Proofs.ComplexChain.Vel

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: sums and products of context expressions.** At a real final phase of the outer
carrier, the final-phase line of a context extension is a phase series (`isPS_line`: holomorphic on
the strip `|Im z| < 7b/2` and `1`-periodic by the final-phase symmetry). Hence the final-phase
coefficients of a sum add and those of a product convolve: `CtxInv.add`,
`CtxInv.mul`. -/

section
open AVRegularity.Providers.ComplexFlow

/-- The real unit vector `e_q`. -/
def rvec (q : Fin 2) : Vec 2 := fun a => if a = q then 1 else 0

theorem tInt_rvec (p : ℤ) : TInt p (rvec (transverseIndex p)) := ⟨1, by simp [rvec]⟩

/-- A unit final-phase translation moves the final-phase line by one. -/
theorem shiftFinal_line {n : ℕ} (q : Fin 2) (x : ChainParamsC n) (z : ℂ) :
    ChainParamsC.shiftFinal ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) (rvec q) =
      (x.1, x.2.1, x.2.2 + evec q (z + 1)) := by
  simp only [ChainParamsC.shiftFinal, Prod.mk.injEq, true_and]
  funext a
  simp only [Pi.add_apply, evec, rvec]
  split_ifs <;> push_cast <;> ring

/-- **The final-phase line is a phase series** at a real final phase of the outer carrier. -/
theorem isPS_line {D : OCData} {b : ℝ} (hb : 0 < b) {dd : ChainData} {n : ℕ}
    {G : ChainParamsC n → ℂ} (hG : DifferentiableOn ℂ G (carrierC D b dd n 2))
    (hsym : FinalSymm dd G (carrierC D b dd n 2)) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2)
    (hre : (x.2.2 (transverseIndex (dd.slots.getLastD 0))).im = 0) :
    IsPS (fun s : ℝ => lineF (transverseIndex (dd.slots.getLastD 0)) G x s)
      (pcoeff fun s : ℝ => lineF (transverseIndex (dd.slots.getLastD 0)) G x s) := by
  set q := transverseIndex (dd.slots.getLastD 0)
  have hmem : ∀ z : ℂ, |z.im| < (3 + 2 / 4) * b → (x.1, x.2.1, x.2.2 + evec q z) ∈
      carrierC D b dd n 2 := fun z hz => mem_carrierC_line hx hre hz
  refine isPS_of_strip (w := (3 + 2 / 4) * b) (by positivity) ?_ ?_
  · have hl : Differentiable ℂ fun z : ℂ => ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) := by
      refine (differentiable_const _).prodMk ((differentiable_const _).prodMk ?_)
      refine (differentiable_const _).add ?_
      rw [differentiable_pi]
      intro a
      unfold evec
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    exact hG.comp hl.differentiableOn fun z hz => hmem z hz
  · intro z hz
    unfold lineF
    rw [← shiftFinal_line]
    exact hsym _ (hmem z hz) _ (tInt_rvec _)

/-- The extended norm of a convolution. -/
theorem enorm_conv_le {a c : ℤ → ℂ} (ha : Summable fun j => ‖a j‖)
    (hc : Summable fun j => ‖c j‖) (h : ℤ) :
    ‖conv a c h‖ₑ ≤ ∑' j, ‖a j‖ₑ * ‖c (h - j)‖ₑ := by
  have hfib : Summable fun j => ‖a j‖ * ‖c (h - j)‖ :=
    (summable_conv_real (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ha hc).2 h
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (norm_conv_le ha hc h)).trans ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hfib]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-! ### Local bounds -/

theorem LocBdd.add {n : ℕ} {F G : ℝ → ChainParamsC n → ℂ} {T : Set ℝ} {S : Set (ChainParamsC n)}
    (hF : LocBdd F T S) (hG : LocBdd G T S) : LocBdd (fun t y => F t y + G t y) T S := by
  intro x hx
  obtain ⟨U, hU, M, hM⟩ := hF x hx
  obtain ⟨V, hV, N, hN⟩ := hG x hx
  exact ⟨U ∩ V, inter_mem hU hV, M + N, fun t ht y hy =>
    (norm_add_le _ _).trans (add_le_add (hM t ht y hy.1) (hN t ht y hy.2))⟩

theorem LocBdd.mul {n : ℕ} {F G : ℝ → ChainParamsC n → ℂ} {T : Set ℝ} {S : Set (ChainParamsC n)}
    (hF : LocBdd F T S) (hG : LocBdd G T S) : LocBdd (fun t y => F t y * G t y) T S := by
  intro x hx
  obtain ⟨U, hU, M, hM⟩ := hF x hx
  obtain ⟨V, hV, N, hN⟩ := hG x hx
  refine ⟨U ∩ V, inter_mem hU hV, max M 0 * max N 0, fun t ht y hy => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hM t ht y hy.1).trans (le_max_left _ _))
    ((hN t ht y hy.2).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

/-! ### Sums and products -/

section Alg

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- The line coefficients at an admissible point, as a phase series. -/
theorem CtxInv.isPS {f : GenSort.Sem .ctx} {F : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CtxInv D b j₀ i p f F B) (hb : 0 < b) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    {dd : ChainData} {n : ℕ} (hdd : AdmData D b j₀ i p dd n) {mres : ℝ} (hm : mres ≤ 2)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres) (hre : RealFinal x) :
    IsPS (fun s : ℝ => lineF (transverseIndex p) (F dd n t) x s)
      (pcoeff fun s : ℝ => lineF (transverseIndex p) (F dd n t) x s) := by
  have hx2 : x ∈ carrierC D b dd n 2 := carrierC_mono hb.le hm hx
  have := isPS_line hb (hF.hol dd n t ht) (hF.fin dd n t ht) hx2 (hre _)
  rwa [hdd.lastSlot] at this

/-- **Sums of context expressions.** -/
theorem CtxInv.add {fa fb : GenSort.Sem .ctx} {Fa Fb : Ext} {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hb : 0 < b) (ha : CtxInv D b j₀ i p fa Fa Ba) (hc : CtxInv D b j₀ i p fb Fb Bb) :
    CtxInv D b j₀ i p (GenSort.add .ctx fa fb) (fun dd n t x => Fa dd n t x + Fb dd n t x)
      (fun mres h t => Ba mres h t + Bb mres h t) where
  hol dd n t ht := (ha.hol dd n t ht).add (hc.hol dd n t ht)
  meas dd n x hx := (ha.meas dd n x hx).add (hc.meas dd n x hx)
  agree ch t ht ζ hch := by
    simp only [ha.agree ch t ht ζ hch, hc.agree ch t ht ζ hch, GenSort.add, Complex.ofReal_add]
  fin dd n t ht x hx v hv := by
    simp only [ha.fin dd n t ht x hx v hv, hc.fin dd n t ht x hx v hv]
  child dd n t ht x hx k v hv := by
    simp only [ha.child dd n t ht x hx k v hv, hc.child dd n t ht x hx k v hv]
  bdd dd n := (ha.bdd dd n).add (hc.bdd dd n)
  mode mres hm0 hm2 h t ht dd n hdd x hx hre := by
    have hA := ha.isPS hb ht hdd hm2 hx hre
    have hC := hc.isPS hb ht hdd hm2 hx hre
    have hS := hA.add hC
    rw [finalPhaseCoeff_eq_pcoeff]
    rw [show (fun s : ℝ => lineF (transverseIndex p) (fun x => Fa dd n t x + Fb dd n t x) x s) =
      fun s : ℝ => lineF (transverseIndex p) (Fa dd n t) x s +
        lineF (transverseIndex p) (Fb dd n t) x s from rfl, hS.pcoeff_eq]
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← finalPhaseCoeff_eq_pcoeff]; exact ha.mode mres hm0 hm2 h t ht dd n hdd x hx hre
    · rw [← finalPhaseCoeff_eq_pcoeff]; exact hc.mode mres hm0 hm2 h t ht dd n hdd x hx hre

/-- **Products of context expressions.** -/
theorem CtxInv.mul {fa fb : GenSort.Sem .ctx} {Fa Fb : Ext} {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hb : 0 < b) (ha : CtxInv D b j₀ i p fa Fa Ba) (hc : CtxInv D b j₀ i p fb Fb Bb) :
    CtxInv D b j₀ i p (GenSort.mul .ctx fa fb) (fun dd n t x => Fa dd n t x * Fb dd n t x)
      (fun mres h t => ∑' k, Ba mres k t * Bb mres (h - k) t) where
  hol dd n t ht := (ha.hol dd n t ht).mul (hc.hol dd n t ht)
  meas dd n x hx := (ha.meas dd n x hx).mul (hc.meas dd n x hx)
  agree ch t ht ζ hch := by
    simp only [ha.agree ch t ht ζ hch, hc.agree ch t ht ζ hch, GenSort.mul, Complex.ofReal_mul]
  fin dd n t ht x hx v hv := by
    simp only [ha.fin dd n t ht x hx v hv, hc.fin dd n t ht x hx v hv]
  child dd n t ht x hx k v hv := by
    simp only [ha.child dd n t ht x hx k v hv, hc.child dd n t ht x hx k v hv]
  bdd dd n := (ha.bdd dd n).mul (hc.bdd dd n)
  mode mres hm0 hm2 h t ht dd n hdd x hx hre := by
    have hA := ha.isPS hb ht hdd hm2 hx hre
    have hC := hc.isPS hb ht hdd hm2 hx hre
    have hP := hA.mul hC
    rw [finalPhaseCoeff_eq_pcoeff]
    rw [show (fun s : ℝ => lineF (transverseIndex p) (fun x => Fa dd n t x * Fb dd n t x) x s) =
      fun s : ℝ => lineF (transverseIndex p) (Fa dd n t) x s *
        lineF (transverseIndex p) (Fb dd n t) x s from rfl, hP.pcoeff_eq]
    refine (enorm_conv_le hA.rapid.summable hC.rapid.summable h).trans ?_
    refine ENNReal.tsum_le_tsum fun k => mul_le_mul' ?_ ?_
    · rw [← finalPhaseCoeff_eq_pcoeff]; exact ha.mode mres hm0 hm2 k t ht dd n hdd x hx hre
    · rw [← finalPhaseCoeff_eq_pcoeff]
      exact hc.mode mres hm0 hm2 (h - k) t ht dd n hdd x hx hre

end Alg
end

/-! **Carrier calculus: certified leaves and the conclusion.** A certified leaf (`LeavesCertified`: a
holomorphic extension in the sense of `IsHolExtension`, with mode suprema below the
profile `B`) satisfies the context invariant with the time-independent majorant `B`
(`CtxInv.of_leaf`). Conversely, a context invariant gives a holomorphic extension once the
extension is set to zero off the outer carrier (`trimExt`, `CtxInv.isHolExtension`), with the
same mode suprema (`CtxInv.ctxModeSupAt_trim_le`). -/

section
open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- The mode supremum at a time of the output window is at most the mode supremum. -/
theorem ctxModeSupAt_le_ctxModeSup {F : Ext} {mres : ℝ} {h : ℤ} {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ctxModeSupAt D b j₀ i p F mres h t ≤ ctxModeSup D b j₀ i p F mres h := by
  unfold ctxModeSupAt ctxModeSup
  refine iSup₂_le fun dd n => iSup_le fun hex => iSup₂_le fun x hx => iSup_le fun hre => ?_
  exact le_iSup₂_of_le dd n (le_iSup_of_le hex (le_iSup₂_of_le t ht (le_iSup₂_of_le x hx
    (le_iSup_of_le hre le_rfl))))

/-- **A certified leaf satisfies the context invariant.** -/
theorem CtxInv.of_leaf {f : GenSort.Sem .ctx} {F : Ext} {B : ℝ → ℤ → ℝ≥0∞}
    (hF : IsHolExtension D b j₀ i p f F) (hB : ∀ mres h, ctxModeSup D b j₀ i p F mres h ≤ B mres h) :
    CtxInv D b j₀ i p f F (fun mres h _ => B mres h) where
  hol := hF.1
  meas dd n x _ := hF.2.1.1 dd n x
  agree := hF.2.2
  fin dd n t ht x hx v hv := (hF.2.1.2.1 dd n t ht x hx).1 v hv
  child dd n t ht x hx k v hv := (hF.2.1.2.1 dd n t ht x hx).2 k v hv
  bdd dd n := hF.2.1.2.2 dd n
  mode mres _ _ h _ ht _ _ hdd _ hx hre :=
    (le_ctxModeSupAt hdd hx hre).trans ((ctxModeSupAt_le_ctxModeSup ht).trans (hB mres h))

open scoped Classical in
/-- The extension set to zero off the outer carrier. -/
def trimExt (D : OCData) (b : ℝ) (F : Ext) : Ext :=
  fun dd n t x => if x ∈ carrierC D b dd n 2 then F dd n t x else 0

theorem trimExt_of_mem {F : Ext} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) : trimExt D b F dd n t x = F dd n t x := by
  simp [trimExt, hx]

/-- The final-phase coefficients of the trimmed extension at a real final phase. -/
theorem finalPhaseCoeff_trimExt (hb : 0 < b) {F : Ext} {dd : ChainData} {n : ℕ} {t : ℝ}
    {mres : ℝ} (hm : mres ≤ 2) {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    (hre : RealFinal x) (q : Fin 2) (h : ℤ) :
    finalPhaseCoeff q (trimExt D b F dd n t) x h = finalPhaseCoeff q (F dd n t) x h := by
  have hx2 := carrierC_mono hb.le hm hx
  unfold finalPhaseCoeff
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hmem : ((x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) : ChainParamsC n) ∈
      carrierC D b dd n 2 := by
    refine ⟨hx2.1, hx2.2.1, ?_⟩
    show |((x.2.2 + fun a => if a = q then (s : ℂ) else 0) _).im| < _
    simp only [Pi.add_apply, hre _, Complex.add_im, zero_add]
    split_ifs
    · simp only [Complex.ofReal_im, abs_zero]; positivity
    · simp only [Complex.zero_im, abs_zero]; positivity
  rw [trimExt_of_mem hmem]

/-- **A context invariant gives a holomorphic extension.** -/
theorem CtxInv.isHolExtension (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {f : GenSort.Sem .ctx} {F : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p f F B) :
    IsHolExtension D b j₀ i p f (trimExt D b F) := by
  classical
  refine ⟨fun dd n t ht => ?_, ⟨fun dd n x => ?_, fun dd n t ht x hx => ⟨fun v hv => ?_,
    fun k v hv => ?_⟩, fun dd n x hx => ?_⟩, fun ch t ht ζ hch => ?_⟩
  · exact (hF.hol dd n t ht).congr fun x hx => trimExt_of_mem hx
  · by_cases hx : x ∈ carrierC D b dd n 2
    · simp only [trimExt, hx, ite_true]; exact hF.meas dd n x hx
    · simp only [trimExt, hx, ite_false]; exact measurable_const
  · have hs : x.shiftFinal v ∈ carrierC D b dd n 2 := (mem_carrierC_shiftFinal_iff x v).mpr hx
    rw [trimExt_of_mem hs, trimExt_of_mem hx, hF.fin dd n t ht x hx v hv]
  · have hs : x.shiftChild k v ∈ carrierC D b dd n 2 := (mem_carrierC_shiftChild_iff x k v).mpr hx
    rw [trimExt_of_mem hs, trimExt_of_mem hx, hF.child dd n t ht x hx k v hv]
  · obtain ⟨U, hU, M, hM⟩ := hF.bdd dd n x hx
    refine ⟨U ∩ carrierC D b dd n 2, inter_mem hU ((isOpen_carrierC D b dd n 2).mem_nhds hx), M,
      fun t ht y hy => ?_⟩
    rw [trimExt_of_mem hy.2]
    exact hM t ht y hy.1
  · rw [trimExt_of_mem (GenSem.paramsC_mem_carrierC hΛ hb hch ζ)]
    exact hF.agree ch t ht ζ hch

/-- **The mode bound of the conclusion.** -/
theorem CtxInv.ctxModeSupAt_trim_le (hb : 0 < b) {f : GenSort.Sem .ctx} {F : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p f F B) {mres : ℝ} (hm0 : 0 ≤ mres)
    (hm2 : mres ≤ 2) (h : ℤ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ctxModeSupAt D b j₀ i p (trimExt D b F) mres h t ≤ B mres h t := by
  refine ctxModeSupAt_le fun dd n hdd x hx hre => ?_
  rw [finalPhaseCoeff_trimExt hb hm2 hx hre]
  exact hF.mode mres hm0 hm2 h t ht dd n hdd x hx hre
end

end AVRegularity.Providers.ComplexContext
end
