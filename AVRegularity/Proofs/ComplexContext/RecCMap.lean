-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.ComplexContext.Leaf
public import AVRegularity.Proofs.ComplexContext.RecC
public import AVRegularity.Proofs.ComplexChain.InvLeaf
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the appended child at complex parameters**. For the finer slot `p'` and the
output time `t`, the parameters of the chain with the appended child are `appendC x t`: the same
base label and children, the child `(ε_i d_i(s_{𝗉'}; t, ζ), ζ + d_i(s_{𝗉'}; t, ζ))` (`appCenter`,
`appPhase`), final phase `0`; the discrete data are `appData dd p'`. This map is holomorphic
(`differentiable_appendC`), maps the carrier of reserve `m ≥ 0` into the carrier of the appended
data, also along the final-phase strip `|Im ζ_q| ≤ 3b + b/128` (`appendC_mem_carrierC`), restricts
to the real appended chain (`appendC_paramsC`), and turns the final-phase translations into
translations of the appended child's phase (`appendC_shiftFinal`, `appendC_shiftChild`). -/

section
open AVRegularity.Providers.ComplexFlow

/-- The discrete data of the chain with the child appended for the finer slot `p'`. -/
def appData (dd : ChainData) (p' : ℤ) : ChainData := ⟨dd.baseLevel, dd.slots ++ [p']⟩

/-- **The parameters of the chain with the appended child.** -/
def appendC (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) (x : ChainParamsC n) :
    ChainParamsC (n + 1) :=
  (x.1, Fin.snoc x.2.1 (appCenter D dd n p' t x, appPhase D dd n p' t x), 0)

variable {D : OCData}

theorem differentiable_appendC (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) :
    Differentiable ℂ (appendC D dd n p' t) := by
  unfold appendC
  refine differentiable_fst.prodMk (Differentiable.prodMk ?_ (differentiable_const _))
  rw [differentiable_pi]
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [Fin.snoc_last]
    exact (differentiable_appCenter D dd n p' t).prodMk (differentiable_appPhase D dd n p' t)
  · simp only [Fin.snoc_castSucc]
    exact (by fun_prop : Differentiable ℂ fun x : ChainParamsC n => x.2.1 k)

/-- Continuity of the appended parameters in the parameters and the time. -/
theorem continuous_appendC (hζ : IsFastProfile D.ζ) (dd : ChainData) (n : ℕ) (p' : ℤ) :
    Continuous fun r : ChainParamsC n × ℝ => appendC D dd n p' r.2 r.1 := by
  have hpi : Continuous fun r : ChainParamsC n × ℝ =>
      ((D.eps (appLevel dd n))⁻¹ * ∫ v in r.2..D.slotAnchor (appLevel dd n + 1) p',
        ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (dd.slots.getLastD 0) v) := by
    refine continuous_const.mul ?_
    have hc := ComplexFlow.continuous_ocPulse D hζ (appLevel dd n) (dd.slots.getLastD 0)
    have := (intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hc.intervalIntegrable a b) (D.slotAnchor (appLevel dd n + 1) p'))
    have e : (fun r : ChainParamsC n × ℝ => ∫ v in r.2..D.slotAnchor (appLevel dd n + 1) p',
        ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (dd.slots.getLastD 0) v) = fun r =>
        -∫ v in D.slotAnchor (appLevel dd n + 1) p'..r.2,
          ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (dd.slots.getLastD 0) v := by
      funext r; rw [intervalIntegral.integral_symm]
    rw [e]
    exact (this.comp continuous_snd).neg
  have hsh : Continuous fun r : ChainParamsC n × ℝ => ocShearVelC D.α D.q D.Λ (appLevel dd n)
      (dd.slots.getLastD 0) (((D.eps (appLevel dd n) : ℝ) : ℂ) • r.1.2.2) :=
    (differentiable_ocShearVelC _ _ _ _ _).continuous.comp
      ((continuous_const (y := ((D.eps (appLevel dd n) : ℝ) : ℂ))).smul
        (continuous_fst.snd.snd : Continuous fun r : ChainParamsC n × ℝ => r.1.2.2))
  have hrd : Continuous fun r : ChainParamsC n × ℝ => relDispC D (appLevel dd n)
      (dd.slots.getLastD 0) (D.slotAnchor (appLevel dd n + 1) p') r.2 r.1.2.2 := by
    unfold relDispC
    exact (Complex.continuous_ofReal.comp hpi).smul hsh
  unfold appendC
  refine continuous_fst.fst.prodMk (Continuous.prodMk ?_ continuous_const)
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [Fin.snoc_last, appCenter, appPhase]
    exact ((continuous_const (y := epsC D (appLevel dd n))).smul hrd).prodMk
      (continuous_fst.snd.snd.add hrd)
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply k).comp continuous_fst.snd.fst

section Carrier

variable {b : ℝ} {dd : ChainData} {n : ℕ}

theorem appData_slots_getD_lt (p' : ℤ) {k : ℕ} (hk : k < dd.slots.length) :
    (appData dd p').slots.getD k 0 = dd.slots.getD k 0 := by
  simp [appData, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem appData_slots_getD_last (p' : ℤ) (hlen : dd.slots.length = n + 1) :
    (appData dd p').slots.getD n 0 = dd.slots.getLastD 0 := by
  rw [appData_slots_getD_lt p' (by omega)]
  obtain ⟨l, a, hl⟩ : ∃ l a, dd.slots = l ++ [a] := by
    rcases List.eq_nil_or_concat dd.slots with h | ⟨l, a, h⟩
    · rw [h] at hlen; simp at hlen
    · exact ⟨l, a, by simpa using h⟩
  have hn : l.length = n := by rw [hl] at hlen; simpa using hlen
  rw [hl, List.getLastD_eq_getLast?, List.getLast?_append]
  simp [List.getD_eq_getElem?_getD, hn]

/-- **The appended parameters lie in the carrier of the appended data**, along the final-phase
strip `|Im ζ_q| < 3b + b/64 + mres b/4`. -/
theorem appendC_mem_carrierC (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 10000) (hlen : dd.slots.length = n + 1) {p' : ℤ} {t : ℝ}
    (hah : ocA D.α D.q D.Λ (appLevel dd n) * ocTauPP D.α D.q D.Λ (appLevel dd n + 1) ≤ b / 10000)
    (ht : t ∈ slotWin D (appLevel dd n + 1) p') {mres : ℝ} (hm0 : 0 ≤ mres)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2)
    (hxm1 : (∑ a : Fin 2, |(x.1 a).im|) < (1 + mres / 4) * (1 / 100) * D.eps dd.baseLevel)
    (hxm2 : ∀ k : Fin n, (∑ a : Fin 2, ‖(x.2.1 k).1 a‖) <
        (1 + mres) * b / 4 * D.eps (dd.baseLevel + 1 + k) ∧
      |((x.2.1 k).2 (transverseIndex (dd.slots.getD k 0))).im| < (3 + mres / 4) * b + b / 64)
    (hxm3 : |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b + b / 64) :
    appendC D dd n p' t x ∈ carrierC D b (appData dd p') (n + 1) mres := by
  have he : 0 < D.eps (appLevel dd n) := Construction.Stream.ocEpsilon_pos hΛ
  refine ⟨hxm1, fun j => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [appendC, Fin.snoc_last]
      constructor
      · have hc := norm_appCenter_le hζ hΛ hb0 hb1 hah ht hx
        have hl1 : (∑ a : Fin 2, ‖appCenter D dd n p' t x a‖) ≤ 2 * ‖appCenter D dd n p' t x‖ := by
          rw [Fin.sum_univ_two]
          linarith [norm_le_pi_norm (appCenter D dd n p' t x) 0,
            norm_le_pi_norm (appCenter D dd n p' t x) 1]
        have hlev : (appData dd p').baseLevel + 1 + ((Fin.last n : Fin (n + 1)) : ℕ) =
            appLevel dd n := by
          simp [appData, appLevel]; ring
        rw [hlev]
        have : 0 < b * D.eps (appLevel dd n) := mul_pos hb0 he
        nlinarith
      · rw [show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl, appData_slots_getD_last p' hlen,
          appPhase_transverse]
        exact hxm3
    · simp only [appendC, Fin.snoc_castSucc]
      have := hxm2 k
      rw [show ((Fin.castSucc k : Fin (n + 1)) : ℕ) = k from rfl,
        appData_slots_getD_lt p' (by omega)]
      exact this
  · show |((0 : Fin 2 → ℂ) _).im| < _
    simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
    positivity

end Carrier

/-- **The appended parameters at a real chain** are the parameters of the real appended chain. -/
theorem appendC_paramsC (ch : RealChain) (p' : ℤ) (t : ℝ) (ζ : Vec 2)
    (hl : (ch.appendChild D p' t ζ).children.length = ch.children.length + 1) :
    appendC D ch.data ch.children.length p' t (ch.paramsC ζ) =
      (ch.appendChild D p' t ζ).paramsN (ch.children.length + 1) hl 0 := by
  have hlev : appLevel ch.data ch.children.length = ch.ctxLevel := by
    simp [appLevel, RealChain.data, RealChain.ctxLevel, RealChain.lastLevel]
  have hslot : ch.data.slots.getLastD 0 = ch.slot := rfl
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [appendC, Fin.snoc_last, RealChain.paramsN]
      have hget : (ch.appendChild D p' t ζ).children.get (Fin.cast hl.symm (Fin.last _)) =
          ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot
            (D.slotAnchor (ch.ctxLevel + 1) p') t ζ,
            ζ + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ⟩ := by
        simp only [RealChain.appendChild, List.get_eq_getElem]
        exact List.getElem_concat_length rfl _
      rw [hget]
      refine Prod.ext ?_ ?_
      · funext a
        simp only [appCenter, hlev, hslot, RealChain.paramsC]
        rw [show (fun a => ((ζ a : ℝ) : ℂ)) = ofRealVec ζ from rfl, relDispC_ofRealVec]
        simp [ofRealVec, epsC]
      · funext a
        simp only [appPhase, hlev, hslot, RealChain.paramsC]
        rw [show (fun a => ((ζ a : ℝ) : ℂ)) = ofRealVec ζ from rfl, relDispC_ofRealVec]
        simp [ofRealVec]
    · simp only [appendC, Fin.snoc_castSucc, RealChain.paramsN, RealChain.paramsC]
      have hget : (ch.appendChild D p' t ζ).children.get (Fin.cast hl.symm k.castSucc) =
          ch.children.get k := by
        simp only [RealChain.appendChild, List.get_eq_getElem]
        exact List.getElem_append_left k.2
      rw [hget]
  · funext a
    simp [appendC, RealChain.paramsN]

/-- The appended child's phase absorbs the final-phase translations. -/
theorem appendC_shiftFinal (hΛ : 1 ≤ D.Λ) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ)
    (x : ChainParamsC n) {v : Vec 2} (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getLastD 0)) = m) :
    appendC D dd n p' t (x.shiftFinal v) = (appendC D dd n p' t x).shiftChild (Fin.last n) v := by
  have hε : D.eps (appLevel dd n) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hrd : relDispC D (appLevel dd n) (dd.slots.getLastD 0)
      (D.slotAnchor (appLevel dd n + 1) p') t (x.shiftFinal v).2.2 =
      relDispC D (appLevel dd n) (dd.slots.getLastD 0) (D.slotAnchor (appLevel dd n + 1) p') t
        x.2.2 := relDispC_shift D hε _ _ _ _ hv
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [appendC, ChainParamsC.shiftChild, Function.update_self, Fin.snoc_last]
    refine Prod.ext ?_ ?_
    · simp only [appCenter, hrd]
    · simp only [appPhase]
      rw [hrd]
      simp only [ChainParamsC.shiftFinal]
      funext a; simp only [Pi.add_apply]; ring
  · have hk : (Fin.castSucc k : Fin (n + 1)) ≠ Fin.last n := Fin.castSucc_ne_last k
    simp only [appendC, ChainParamsC.shiftChild, Function.update_of_ne hk, Fin.snoc_castSucc,
      ChainParamsC.shiftFinal]

/-- The appended parameters commute with the child-phase translations. -/
theorem appendC_shiftChild (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) (x : ChainParamsC n)
    (k : Fin n) (v : Vec 2) :
    appendC D dd n p' t (x.shiftChild k v) = (appendC D dd n p' t x).shiftChild k.castSucc v := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · have hk : (Fin.last n : Fin (n + 1)) ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
    simp only [appendC, ChainParamsC.shiftChild, Function.update_of_ne hk, Fin.snoc_last]
    rfl
  · by_cases hl : l = k
    · subst hl
      simp only [appendC, ChainParamsC.shiftChild, Function.update_self, Fin.snoc_castSucc]
    · have hl' : (l.castSucc : Fin (n + 1)) ≠ k.castSucc := fun h => hl (Fin.castSucc_inj.mp h)
      simp only [appendC, ChainParamsC.shiftChild, Function.update_of_ne hl', Fin.snoc_castSucc,
        Function.update_of_ne hl]
end

/-! **Carrier calculus: the own-frame geometric letters** `F_t(0)`, `F_t(0)⁻¹`, `𝒢_t(0)` (`geo own`).
Each entry is a leaf of the complex chain (`F − I`, `F⁻¹ − I`, `𝒢 − I`: `jacLeaf_isHolExtension`,
`ownLeaf_isHolExtension`) plus the constant `δ_ac`. The leaves do not depend on the final phase,
so the only mode is the zero mode, at most `B(m)`, `m = K a_{i-1} (6/5) h_i`; under the smallness
`m ≤ 1/100` of the carrier start every entry is at most `2` (`CtxInv.geoOwn_jac`,
`CtxInv.geoOwn_jacInv`, `CtxInv.geoOwn_metric`). Also the congruence and monotonicity of the
invariants (`CtxInv.congr`, `CtxInv.mono`, and their family and cell versions). -/

section
open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-! ### Congruence and monotonicity -/

theorem CtxInv.congr {f f' : GenSort.Sem .ctx} {F : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CtxInv D b j₀ i p f F B)
    (h : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch → ∀ ζ,
      f t ch ζ = f' t ch ζ) : CtxInv D b j₀ i p f' F B :=
  { hF with agree := fun ch t ht ζ hch => by rw [hF.agree ch t ht ζ hch, h t ht ch hch ζ] }

theorem CtxInv.mono {f : GenSort.Sem .ctx} {F : Ext} {B B' : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CtxInv D b j₀ i p f F B)
    (h : ∀ mres h t, 0 ≤ mres → mres ≤ 2 → t ∈ ocPulseWindow D.α D.q D.Λ i p →
      B mres h t ≤ B' mres h t) : CtxInv D b j₀ i p f F B' :=
  { hF with mode := fun mres hm0 hm2 k t ht dd n hdd x hx hre =>
      (hF.mode mres hm0 hm2 k t ht dd n hdd x hx hre).trans (h mres k t hm0 hm2 ht) }

theorem FamInv.congr {f f' : GenSort.Sem .fam} {G : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : FamInv D b j₀ i p f G B)
    (h : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
      f t ch = f' t ch) : FamInv D b j₀ i p f' G B :=
  { hF with agree := fun ch t ht hch => by rw [hF.agree ch t ht hch, h t ht ch hch] }

theorem FamInv.mono {f : GenSort.Sem .fam} {G : Ext} {B B' : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : FamInv D b j₀ i p f G B)
    (h : ∀ mres t, 0 ≤ mres → mres ≤ 2 → t ∈ ocPulseWindow D.α D.q D.Λ i p →
      B mres 0 t ≤ B' mres 0 t) : FamInv D b j₀ i p f G B' :=
  { hF with mode := fun mres hm0 hm2 t ht dd n hdd x hx =>
      (hF.mode mres hm0 hm2 t ht dd n hdd x hx).trans (h mres t hm0 hm2 ht) }

theorem CellInv.congr {f f' : GenSort.Sem .cell} {W : ℤ → Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CellInv D b j₀ i p f W B)
    (h : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch → ∀ η,
      f t ch η = f' t ch η) : CellInv D b j₀ i p f' W B :=
  { hF with agree := fun ch t ht hch η => by rw [← h t ht ch hch η]; exact hF.agree ch t ht hch η }

theorem CellInv.mono {f : GenSort.Sem .cell} {W : ℤ → Ext} {B B' : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CellInv D b j₀ i p f W B)
    (h : ∀ mres h t, 0 ≤ mres → mres ≤ 2 → t ∈ ocPulseWindow D.α D.q D.Λ i p →
      B mres h t ≤ B' mres h t) : CellInv D b j₀ i p f W B' :=
  { hF with mode := fun mres hm0 hm2 k t ht dd n hdd x hx =>
      (hF.mode mres hm0 hm2 k t ht dd n hdd x hx).trans (h mres k t hm0 hm2 ht) }

/-! ### The own-frame letters -/

/-- The size `m = K a_{i-1} (6/5) h_i` of `F − I` over a slot of level `i`. -/
def ownSize (D : OCData) (i : ℕ) : ℝ :=
  chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i)

/-- The bound `m(1+m)/(1-m)²` of `F⁻¹ − I` is at most `1/25` for `m ≤ 1/100`. -/
theorem invB_le {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 100) : m * (1 + m) / (1 - m) ^ 2 ≤ 1 / 25 := by
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

theorem metricB_le {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 100) : metricB m ≤ 1 / 10 := by
  unfold metricB
  have h1 := invB_le hm0 hm
  have h0 : 0 ≤ m * (1 + m) / (1 - m) ^ 2 := by
    have : 0 < (1 - m) ^ 2 := by nlinarith
    positivity
  nlinarith

/-- The constant `δ_ac` as a time letter. -/
def deltaL (a c : Fin 2) : TimeLetter := .const (if a = c then 1 else 0)

theorem deltaL_le (a c : Fin 2) (t : ℝ) : |(deltaL a c).eval D t| ≤ 1 := by
  unfold deltaL TimeLetter.eval
  split_ifs <;> simp

/-- **The own-frame Jacobian entries.** -/
theorem CtxInv.geoOwn_jac (env : ChainEnv D b CH Υ j₀) (hm : ownSize D i ≤ 1 / 100) (a c : Fin 2) :
    CtxInv D b j₀ i p (GeoLetter.eval D i .own (.jac a c))
      (fun dd n t x => jacLeafExt D b j₀ i p a c dd n t x + (((deltaL a c).eval D t : ℝ) : ℂ))
      (fun _ h _ => if h = 0 then ENNReal.ofReal 2 else 0) := by
  have h1 := (CtxInv.of_leaf (jacLeaf_isHolExtension env i p a c)
    (jacLeaf_ctxModeSup_le env i p a c)).add env.hb0
    (CtxInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p) (L := deltaL a c) continuous_const)
  refine (h1.congr fun t _ ch _ ζ => ?_).mono fun mres h t _ _ _ => ?_
  · simp [GenSort.add, GenSort.ofTime, GeoLetter.eval, GeoLetter.evalAt, deltaL, TimeLetter.eval]
  · have hm0 : 0 ≤ ownSize D i := by
      unfold ownSize
      exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
        (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le _))
        (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos env.hΛ1).le)
    split_ifs with h0
    · rw [← ENNReal.ofReal_add (by unfold ownSize at hm0; exact hm0) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := deltaL_le (D := D) a c t
      unfold ownSize at hm
      linarith
    · simp

/-- **The own-frame entries of `F⁻¹`.** -/
theorem CtxInv.geoOwn_jacInv (env : ChainEnv D b CH Υ j₀) (hm : ownSize D i ≤ 1 / 100)
    (a c : Fin 2) :
    CtxInv D b j₀ i p (GeoLetter.eval D i .own (.jacInv a c))
      (fun dd n t x => ownLeafExt D b j₀ i p (fun A => A⁻¹ a c - (if a = c then 1 else 0))
        dd n t x + (((deltaL a c).eval D t : ℝ) : ℂ))
      (fun _ h _ => if h = 0 then ENNReal.ofReal 2 else 0) := by
  have h1 := (CtxInv.of_leaf (ownLeaf_isHolExtension env i p (invSub_entryFun a c))
    (ownLeaf_ctxModeSup_le env i p (invSub_entryFun a c))).add env.hb0
    (CtxInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p) (L := deltaL a c) continuous_const)
  have hm0 : 0 ≤ ownSize D i := by
    unfold ownSize
    exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos env.hΛ1).le)
  refine (h1.congr fun t _ ch _ ζ => ?_).mono fun mres h t _ _ _ => ?_
  · simp [GenSort.add, GenSort.ofTime, GeoLetter.eval, GeoLetter.evalAt, deltaL, TimeLetter.eval]
  · have hB := invB_le hm0 hm
    have hB0 : 0 ≤ ownSize D i * (1 + ownSize D i) / (1 - ownSize D i) ^ 2 := by
      have : 0 < (1 - ownSize D i) ^ 2 := by nlinarith
      positivity
    split_ifs with h0
    · unfold ownSize at hB hB0
      rw [← ENNReal.ofReal_add hB0 (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := deltaL_le (D := D) a c t
      linarith
    · simp

/-- **The own-frame entries of the molecular metric `𝒢 = F⁻¹F⁻ᵀ`.** -/
theorem CtxInv.geoOwn_metric (env : ChainEnv D b CH Υ j₀) (hm : ownSize D i ≤ 1 / 100)
    (a c : Fin 2) :
    CtxInv D b j₀ i p (GeoLetter.eval D i .own (.metric a c))
      (fun dd n t x => ownLeafExt D b j₀ i p
        (fun A => (A⁻¹ * A⁻¹.transpose) a c - (if a = c then 1 else 0)) dd n t x +
          (((deltaL a c).eval D t : ℝ) : ℂ))
      (fun _ h _ => if h = 0 then ENNReal.ofReal 2 else 0) := by
  have h1 := (CtxInv.of_leaf (ownLeaf_isHolExtension env i p (metricSub_entryFun a c))
    (ownLeaf_ctxModeSup_le env i p (metricSub_entryFun a c))).add env.hb0
    (CtxInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p) (L := deltaL a c) continuous_const)
  have hm0 : 0 ≤ ownSize D i := by
    unfold ownSize
    exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos env.hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos env.hΛ1).le)
  refine (h1.congr fun t _ ch _ ζ => ?_).mono fun mres h t _ _ _ => ?_
  · simp [GenSort.add, GenSort.ofTime, GeoLetter.eval, GeoLetter.evalAt, deltaL, TimeLetter.eval,
      RealChain.famMetric]
  · have hB := metricB_le hm0 hm
    have hB0 : 0 ≤ metricB (ownSize D i) :=
      (metricSub_entryFun a c).B_nonneg _ hm0
    split_ifs with h0
    · unfold ownSize at hB hB0
      rw [← ENNReal.ofReal_add hB0 (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := deltaL_le (D := D) a c t
      linarith
    · simp
end

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the complex recentering map**. The
recentering by the offset `h` moves the base label by `h` for a chain without children, and
otherwise the center of the last child by `R(h)` and its phase by `R(h)/ε'` (`recC`). It is
holomorphic in the parameters and the offset (`differentiableOn_recC`), does not touch the final
phase (`recC_final`), commutes with the child-phase translations (`recC_shiftChild`), and maps the
carrier of reserve `𝗆` into the carrier of reserve `𝗆 + Δ` for `|h| ≤ b ε_{i-1} Δ/12`
(`recC_mem`). -/

open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

/-- **The complex recentering** of the parameters by the offset `h`. -/
def recC (D : OCData) (dd : ChainData) : (n : ℕ) → ChainParamsC n → CVec → ChainParamsC n
  | 0, x, h => (x.1 + h, x.2.1, x.2.2)
  | m + 1, x, h => (x.1, Function.update x.2.1 (Fin.last m)
      ((x.2.1 (Fin.last m)).1 + recShift D dd m x h,
        (x.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h), x.2.2)

theorem recC_final (D : OCData) (dd : ChainData) (n : ℕ) (x : ChainParamsC n) (z h : CVec) :
    recC D dd n (x.1, x.2.1, z) h = ((recC D dd n x h).1, (recC D dd n x h).2.1, z) := by
  cases n <;> rfl

theorem recC_snd_snd (D : OCData) (dd : ChainData) (n : ℕ) (x : ChainParamsC n) (h : CVec) :
    (recC D dd n x h).2.2 = x.2.2 := by
  cases n <;> rfl

/-- **The recentering commutes with the child-phase translations.** -/
theorem recC_shiftChild (hΛ : 1 ≤ D.Λ) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2} (hv : TInt (dd.slots.getD k 0) v) (h : CVec) :
    recC D dd n (x.shiftChild k v) h = (recC D dd n x h).shiftChild k v := by
  cases n with
  | zero => exact k.elim0
  | succ m =>
    have hrec : ∀ y : ChainParamsC (m + 1), recC D dd (m + 1) y h = (y.1,
        Function.update y.2.1 (Fin.last m) ((y.2.1 (Fin.last m)).1 + recShift D dd m y h,
          (y.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m y h), y.2.2) :=
      fun y => rfl
    rw [hrec, hrec, recShift_shiftChild hΛ hdd x k hv h]
    simp only [ChainParamsC.shiftChild]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j
    by_cases hjl : j = Fin.last m
    · subst hjl
      by_cases hkl : k = Fin.last m
      · subst hkl
        simp only [Function.update_self]
        refine Prod.ext rfl ?_
        show (x.2.1 (Fin.last m)).2 + (fun a => (v a : ℂ)) +
            epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h =
          (x.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h +
            fun a => (v a : ℂ)
        abel
      · simp only [Function.update_self, Function.update_of_ne (Ne.symm hkl)]
    · by_cases hjk : j = k
      · subst hjk
        simp only [Function.update_self, Function.update_of_ne hjl]
      · simp only [Function.update_of_ne hjl, Function.update_of_ne hjk]

/-- **The recentering is holomorphic** in the parameters and the offset. -/
theorem differentiableOn_recC (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) :
    DifferentiableOn ℂ (fun q : ChainParamsC n × CVec => recC D dd n q.1 q.2)
      (carrierC D b dd n 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + n))) := by
  cases n with
  | zero =>
    exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC 0 × CVec =>
      ((q.1.1 + q.2, q.1.2.1, q.1.2.2) : ChainParamsC 0)).differentiableOn
  | succ m =>
    have hR := differentiableOn_recShift env hdd
    have hupd : DifferentiableOn ℂ (fun q : ChainParamsC (m + 1) × CVec =>
        Function.update q.1.2.1 (Fin.last m)
          ((q.1.2.1 (Fin.last m)).1 + recShift D dd m q.1 q.2,
            (q.1.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m q.1 q.2))
        (carrierC D b dd (m + 1) 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + m + 1))) := by
      refine differentiableOn_pi.2 fun j => ?_
      by_cases hj : j = Fin.last m
      · subst hj
        simp only [Function.update_self]
        refine DifferentiableOn.prodMk ?_ ?_
        · exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC (m + 1) × CVec =>
            (q.1.2.1 (Fin.last m)).1).differentiableOn.add hR
        · have h2 : DifferentiableOn ℂ (fun q : ChainParamsC (m + 1) × CVec =>
              epsInvC D (dd.baseLevel + m + 1) • recShift D dd m q.1 q.2)
              (carrierC D b dd (m + 1) 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + m + 1))) :=
            hR.fun_const_smul _
          exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC (m + 1) × CVec =>
            (q.1.2.1 (Fin.last m)).2).differentiableOn.add h2
      · simp only [Function.update_of_ne hj]
        exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC (m + 1) × CVec =>
          q.1.2.1 j).differentiableOn
    exact (by fun_prop : Differentiable ℂ fun q : ChainParamsC (m + 1) × CVec =>
      q.1.1).differentiableOn.prodMk (hupd.prodMk (by fun_prop : Differentiable ℂ
        fun q : ChainParamsC (m + 1) × CVec => q.1.2.2).differentiableOn)

/-- `∑ |Im z_a| ≤ 2‖z‖` and `∑ ‖z_a‖ ≤ 2‖z‖`. -/
theorem sum_abs_im_le (z : CVec) : ∑ a : Fin 2, |(z a).im| ≤ 2 * ‖z‖ := by
  rw [Fin.sum_univ_two]
  have h0 := (Complex.abs_im_le_norm (z 0)).trans (norm_le_pi_norm z 0)
  have h1 := (Complex.abs_im_le_norm (z 1)).trans (norm_le_pi_norm z 1)
  linarith

theorem sum_norm_le (z : CVec) : ∑ a : Fin 2, ‖z a‖ ≤ 2 * ‖z‖ := by
  rw [Fin.sum_univ_two]
  have h0 := norm_le_pi_norm z 0
  have h1 := norm_le_pi_norm z 1
  linarith

/-- **The recentering maps the carrier of reserve `𝗆` into the carrier of reserve `𝗆 + Δ`.** -/
theorem recC_mem (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    {mres Δ : ℝ} (hm0 : 0 ≤ mres) (hΔ : 0 < Δ) (hmΔ : mres + Δ ≤ 2) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n mres) {h : CVec}
    (hh : ‖h‖ ≤ b * D.eps (dd.baseLevel + n) * Δ / 12) :
    recC D dd n x h ∈ carrierC D b dd n (mres + Δ) := by
  have hb0 := env.hb0
  have hb1 := env.hb1
  have hε : 0 < D.eps (dd.baseLevel + n) := Construction.Stream.ocEpsilon_pos env.hΛ1
  have hfin : |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + (mres + Δ) / 4) * b := by
    have := hx.2.2
    nlinarith
  cases n with
  | zero =>
    refine ⟨?_, fun k => k.elim0, hfin⟩
    show ∑ a : Fin 2, |((x.1 + h) a).im| < _
    have h1 : ∑ a : Fin 2, |((x.1 + h) a).im| ≤ ∑ a : Fin 2, |(x.1 a).im| + 2 * ‖h‖ := by
      calc ∑ a : Fin 2, |((x.1 + h) a).im| ≤ ∑ a : Fin 2, (|(x.1 a).im| + |(h a).im|) :=
            Finset.sum_le_sum fun a _ => by
              rw [Pi.add_apply, Complex.add_im]; exact abs_add_le _ _
        _ = ∑ a : Fin 2, |(x.1 a).im| + ∑ a : Fin 2, |(h a).im| := Finset.sum_add_distrib
        _ ≤ _ := add_le_add le_rfl (sum_abs_im_le h)
    have h2 := hx.1
    have h3 : 2 * ‖h‖ ≤ Δ / 4 * (1 / 100) * D.eps dd.baseLevel := by
      have e : dd.baseLevel + 0 = dd.baseLevel := rfl
      rw [e] at hh hε
      have := mul_le_mul_of_nonneg_right hb1 (mul_nonneg hε.le hΔ.le)
      nlinarith
    calc ∑ a : Fin 2, |((x.1 + h) a).im| ≤ ∑ a : Fin 2, |(x.1 a).im| + 2 * ‖h‖ := h1
      _ < (1 + mres / 4) * (1 / 100) * D.eps dd.baseLevel + Δ / 4 * (1 / 100) * D.eps dd.baseLevel :=
          add_lt_add_of_lt_of_le h2 h3
      _ = (1 + (mres + Δ) / 4) * (1 / 100) * D.eps dd.baseLevel := by ring
  | succ m =>
    have hx2 : x ∈ carrierC D b dd (m + 1) 2 := carrierC_mono hb0.le (by linarith) hx
    have hh' : ‖h‖ < b * D.eps (dd.baseLevel + m + 1) := by
      have e : dd.baseLevel + (m + 1) = dd.baseLevel + m + 1 := rfl
      rw [e] at hh hε
      have : b * D.eps (dd.baseLevel + m + 1) * Δ / 12 < b * D.eps (dd.baseLevel + m + 1) := by
        have := mul_pos hb0 hε
        nlinarith
      linarith
    have hR := norm_recShift_le env hdd hx2 hh'
    have hbase : (∑ a : Fin 2, |(x.1 a).im|) < (1 + (mres + Δ) / 4) * (1 / 100) * D.eps dd.baseLevel := by
      have := hx.1
      have : 0 < D.eps dd.baseLevel := Construction.Stream.ocEpsilon_pos env.hΛ1
      nlinarith
    have hrec : (recC D dd (m + 1) x h).2.1 = Function.update x.2.1 (Fin.last m)
        ((x.2.1 (Fin.last m)).1 + recShift D dd m x h,
          (x.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h) := rfl
    refine ⟨hbase, fun j => ?_, hfin⟩
    rw [hrec]
    by_cases hj : j = Fin.last m
    · subst hj
      have hc := hx.2.1 (Fin.last m)
      simp only [Fin.val_last] at hc ⊢
      rw [show dd.baseLevel + 1 + m = dd.baseLevel + m + 1 by omega] at hc ⊢
      have e2 : dd.baseLevel + (m + 1) = dd.baseLevel + m + 1 := rfl
      rw [e2] at hh hε
      rw [Function.update_self]
      constructor
      · calc ∑ a : Fin 2, ‖((x.2.1 (Fin.last m)).1 + recShift D dd m x h) a‖
            ≤ ∑ a : Fin 2, ‖(x.2.1 (Fin.last m)).1 a‖ + 2 * ‖recShift D dd m x h‖ := by
              calc _ ≤ ∑ a : Fin 2, (‖(x.2.1 (Fin.last m)).1 a‖ + ‖recShift D dd m x h a‖) :=
                    Finset.sum_le_sum fun a _ => by rw [Pi.add_apply]; exact norm_add_le _ _
                _ = _ := Finset.sum_add_distrib
                _ ≤ _ := add_le_add le_rfl (sum_norm_le _)
          _ < (1 + mres) * b / 4 * D.eps (dd.baseLevel + m + 1) +
              Δ * b / 4 * D.eps (dd.baseLevel + m + 1) := by
              refine add_lt_add_of_lt_of_le hc.1 ?_
              have := mul_nonneg hb0.le hε.le
              nlinarith
          _ = (1 + (mres + Δ)) * b / 4 * D.eps (dd.baseLevel + m + 1) := by ring
      · have hq := hc.2
        set q := transverseIndex (dd.slots.getD m 0) with hqdef
        have hRq : |(recShift D dd m x h q).im| ≤ 3 / 2 * ‖h‖ :=
          (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm _ q).trans hR)
        have hsm : |((epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h) q).im| ≤
            (D.eps (dd.baseLevel + m + 1))⁻¹ * (3 / 2 * ‖h‖) := by
          rw [Pi.smul_apply, epsInvC, smul_eq_mul, Complex.im_ofReal_mul, abs_mul,
            abs_of_pos (inv_pos.mpr hε)]
          exact mul_le_mul_of_nonneg_left hRq (inv_nonneg.mpr hε.le)
        have hsm' : (D.eps (dd.baseLevel + m + 1))⁻¹ * (3 / 2 * ‖h‖) ≤ Δ / 4 * b := by
          rw [inv_mul_le_iff₀ hε]
          have := mul_nonneg hb0.le hε.le
          nlinarith
        calc |(((x.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) •
              recShift D dd m x h) q).im|
            ≤ |((x.2.1 (Fin.last m)).2 q).im| +
                |((epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x h) q).im| := by
              rw [Pi.add_apply, Complex.add_im]; exact abs_add_le _ _
          _ < (3 + mres / 4) * b + b / 64 + Δ / 4 * b := add_lt_add_of_lt_of_le hq (hsm.trans hsm')
          _ = (3 + (mres + Δ) / 4) * b + b / 64 := by ring
    · have hc := hx.2.1 j
      rw [Function.update_of_ne hj]
      have hej : 0 < D.eps (dd.baseLevel + 1 + j) := Construction.Stream.ocEpsilon_pos env.hΛ1
      have hp1 : 0 < b * D.eps (dd.baseLevel + 1 + j) * Δ := by positivity
      have hp2 : 0 < b * Δ := by positivity
      refine ⟨?_, ?_⟩
      · have := hc.1
        nlinarith
      · have := hc.2
        nlinarith

end AVRegularity.Providers.ComplexContext
end
