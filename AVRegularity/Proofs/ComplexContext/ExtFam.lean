-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.RecCMap
import AVRegularity.Proofs.ComplexContext.Restrict
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the complex recentering at real chains.** The chain without its last child is
admissible over the second to last slot (`dropLastChild_admissible`), so the parent family agrees
with its real geometry (`parent_agree`); hence at real parameters and real offsets the complex
displacement is the real one (`recShift_real`) and the complex recentering gives the parameters of
the recentered chain (`recC_real`). Small real recenterings of an admissible chain are admissible
(`recenter_admissible`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **The chain without its last child is admissible** over the second to last slot. -/
theorem dropLastChild_admissible {ch : RealChain} (hch : IsAdmissibleChain D b j₀ i p ch)
    (hne : ch.children ≠ []) :
    IsAdmissibleChain D b j₀ (i - 1) ch.dropLastChild.slot ch.dropLastChild := by
  obtain ⟨hctx, hbase, hlen, _, hodd, hsched, hchild⟩ := hch
  have hn : 0 < ch.children.length := List.length_pos_of_ne_nil hne
  refine ⟨?_, hbase, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [RealChain.ctxLevel, RealChain.lastLevel, RealChain.dropLastChild,
      List.length_dropLast] at hctx ⊢
    omega
  · simp only [RealChain.dropLastChild, List.length_dropLast]
    omega
  · intro q hq
    exact hodd q (List.mem_of_mem_dropLast hq)
  · intro k hk
    simp only [RealChain.dropLastChild, List.length_dropLast] at hk ⊢
    rw [List.getElem_dropLast, List.getElem_dropLast]
    exact hsched k (by omega)
  · intro k hk
    simp only [RealChain.dropLastChild, List.length_dropLast] at hk ⊢
    rw [List.getElem_dropLast]
    exact hchild k (by omega)

theorem headD_dropLast {l : List ℤ} (hl : 2 ≤ l.length) : l.dropLast.headD 0 = l.headD 0 := by
  rcases l with _ | ⟨a, _ | ⟨b', l⟩⟩
  · simp at hl
  · simp at hl
  · rfl

/-- **The parent family agrees with the real geometry of the chain without its last child.** -/
theorem parent_agree (env : ChainEnv D b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {m : ℕ} (hn : ch.children.length = m + 1) (ζ : Vec 2) :
    CGeomAgree (slotWin D (ch.baseLevel + 1) (ch.slots.headD 0))
      ((chainFam D (dropData ch.data) m).toGeom (projLast (ch.paramsN (m + 1) hn ζ)))
      (ch.dropLastChild.geom D) := by
  have hne : ch.children ≠ [] := by intro h; rw [h] at hn; simp at hn
  have hch' := dropLastChild_admissible hch hne
  have hag := chainFam_agree env.hΛ env.hvel env.hag env.hb1 env.hCH env.hΥ env.hcs hch' 0
  have hm : ch.dropLastChild.children.length = m := by
    simp [RealChain.dropLastChild, hn]
  have hhead : ch.dropLastChild.slots.headD 0 = ch.slots.headD 0 := by
    show ch.slots.dropLast.headD 0 = _
    have := hch.2.2.1
    exact headD_dropLast (by omega)
  have hP : ch.dropLastChild.paramsN m hm 0 = projLast (ch.paramsN (m + 1) hn ζ) := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext j
      simp only [RealChain.paramsN, projLast, RealChain.dropLastChild, List.get_eq_getElem,
        List.getElem_dropLast]
      rfl
    · funext a
      simp [RealChain.paramsN, projLast]
  have hag' : CGeomAgree (slotWin D (ch.baseLevel + 1) (ch.slots.headD 0))
      ((chainFam D ch.dropLastChild.data ch.dropLastChild.children.length).toGeom
        (ch.dropLastChild.paramsC 0)) (ch.dropLastChild.geom D) := by
    rw [← hhead]
    exact hag
  exact paramsC_transport ch.dropLastChild (dropData ch.data) m rfl hm _ 0 hP
    (fun dd n P => CGeomAgree (slotWin D (ch.baseLevel + 1) (ch.slots.headD 0))
      ((chainFam D dd n).toGeom P) (ch.dropLastChild.geom D)) hag'

/-- **At real parameters and real offsets, the complex displacement is the real one.** -/
theorem recShift_real (env : ChainEnv D b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {m : ℕ} (hn : ch.children.length = m + 1)
    (ζ h : Vec 2) :
    recShift D ch.data m (ch.paramsN (m + 1) hn ζ) (ofRealVec h) =
      ofRealVec (recenterShift D ch (ch.children[m]'(by omega)) h) := by
  have hΛ1 := env.hΛ1
  have hdd := chainOK_of_admissible hch
  rw [hn] at hdd
  have hsep : ∀ k, j₀ ≤ k → ocTauPP D.α D.q D.Λ (k + 1) < ocTau D.α D.q D.Λ k / 48 :=
    fun k hk => separation_of_carrierStart hΛ1 env.hCH env.hcs hk
  have hag := parent_agree env hch hn ζ
  set x := ch.paramsN (m + 1) hn ζ with hx
  set F := chainFam D (dropData ch.data) m with hF
  set g := ch.dropLastChild.geom D with hg
  set G := slotWin D (ch.baseLevel + 1) (ch.slots.headD 0) with hG
  have hhead : ch.data.slots.getD 0 0 = ch.slots.headD 0 := by
    show ch.slots.getD 0 0 = _
    rcases ch.slots with _ | ⟨q, qs⟩ <;> rfl
  -- the times
  have hs' : lastAnchor D ch.data m ∈ G := by
    have h1 := hdd.slotWin_subset hΛ1 hsep (m + 1) le_rfl
    rw [hdd.getD_last, hhead] at h1
    refine h1 ?_
    have e : ch.data.baseLevel + 1 + (m + 1) = ch.data.baseLevel + m + 2 := by omega
    rw [e]
    exact anchor_mem_slotWin D hΛ1 _ _
  have hO := env.chainFam_over (chainOK_dropData hdd)
  have hanc : F.anc ∈ G := by
    have h1 := hdd.slotWin_subset hΛ1 hsep m (by omega)
    rw [hhead] at h1
    refine h1 ?_
    rw [hO.anc, dropData_getLastD hdd,
      show (dropData ch.data).baseLevel + m + 1 = ch.data.baseLevel + 1 + m by
        show ch.baseLevel + m + 1 = ch.baseLevel + 1 + m; omega]
    exact anchor_mem_slotWin D hΛ1 _ _
  have hc : (x.2.1 (Fin.last m)).1 = ofRealVec (ch.children[m]'(by omega)).center := by
    funext a
    simp [hx, RealChain.paramsN, ofRealVec]
  have hctr : F.ctr (projLast x) = ofRealVec g.2.1 := hag.center
  have hancg : F.anc = g.2.2 := hag.anchor
  have hflow := hag.flow
  show F.fl (projLast x) F.anc (F.fl (projLast x) (lastAnchor D ch.data m)
      (F.ctr (projLast x) + (x.2.1 (Fin.last m)).1) F.anc + ofRealVec h) (lastAnchor D ch.data m) -
    (F.ctr (projLast x) + (x.2.1 (Fin.last m)).1) = _
  rw [hc, hctr, ← ofRealVec_add]
  have h1 : F.fl (projLast x) (lastAnchor D ch.data m)
      (ofRealVec (g.2.1 + (ch.children[m]'(by omega)).center)) F.anc =
      ofRealVec (g.1 (lastAnchor D ch.data m) (g.2.1 + (ch.children[m]'(by omega)).center) g.2.2) := by
    rw [hancg]
    exact hflow _ hs' _ (hancg ▸ hanc) _
  rw [h1, ← ofRealVec_add]
  have h2 : F.fl (projLast x) F.anc (ofRealVec (g.1 (lastAnchor D ch.data m)
      (g.2.1 + (ch.children[m]'(by omega)).center) g.2.2 + h)) (lastAnchor D ch.data m) =
      ofRealVec (g.1 g.2.2 (g.1 (lastAnchor D ch.data m)
        (g.2.1 + (ch.children[m]'(by omega)).center) g.2.2 + h) (lastAnchor D ch.data m)) := by
    rw [hancg]
    exact hflow _ (hancg ▸ hanc) _ hs' _
  rw [h2, ← ofRealVec_sub]
  congr 1
  unfold recenterShift shiftOf
  have e1 : D.slotAnchor (ch.lastLevel + 1) ch.slot = lastAnchor D ch.data m := by
    show D.slotAnchor (ch.baseLevel + ch.children.length + 1) (ch.slots.getLastD 0) =
      D.slotAnchor (ch.baseLevel + m + 2) (ch.slots.getLastD 0)
    rw [show ch.baseLevel + ch.children.length + 1 = ch.baseLevel + m + 2 by omega]
  rw [e1]
  abel


theorem norm_ofRealVec_le (h : Vec 2) : ‖ofRealVec h‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).mpr fun a => ?_
  rw [show ofRealVec h a = ((h a : ℝ) : ℂ) from rfl, Complex.norm_real]
  exact norm_le_pi_norm h a

theorem norm_le_norm_ofRealVec (h : Vec 2) : ‖h‖ ≤ ‖ofRealVec h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => ?_
  have := norm_le_pi_norm (ofRealVec h) a
  rwa [show ofRealVec h a = ((h a : ℝ) : ℂ) from rfl, Complex.norm_real] at this

/-- The last child of a chain with `m + 1` children. -/
theorem children_eq_snoc {ch : RealChain} {m : ℕ} (hn : ch.children.length = m + 1) :
    ch.children = ch.children.dropLast ++ [ch.children[m]'(by omega)] := by
  have hne : ch.children ≠ [] := by intro h'; rw [h'] at hn; simp at hn
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  congr 2
  rw [List.getLast_eq_getElem]
  simp [hn]

/-- **At real parameters and real offsets, the complex recentering gives the parameters of the
recentered chain.** -/
theorem recC_real (env : ChainEnv D b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {n : ℕ} (hn : ch.children.length = n) (ζ h : Vec 2)
    (hl : (ch.recenter D h).children.length = n) :
    recC D ch.data n (ch.paramsN n hn ζ) (ofRealVec h) = (ch.recenter D h).paramsN n hl ζ := by
  cases n with
  | zero =>
    have hc : ch.children = [] := List.length_eq_zero_iff.mp hn
    have hr := recenter_nil D ch hc h
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext a
      show ((ch.base a : ℝ) : ℂ) + ofRealVec h a = (((ch.recenter D h).base a : ℝ) : ℂ)
      rw [hr]
      simp [ofRealVec]
    · funext k
      exact k.elim0
    · rfl
  | succ m =>
    have hc := children_eq_snoc hn
    have hr := recenter_snoc D ch ch.children.dropLast (ch.children[m]'(by omega)) hc h
    have hR := recShift_real env hch hn ζ h
    have hchild := congrArg RealChain.children hr
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext a
      show ((ch.base a : ℝ) : ℂ) = (((ch.recenter D h).base a : ℝ) : ℂ)
      rw [hr]
    · funext k
      have hdl : ch.children.dropLast.length = m := by rw [List.length_dropLast, hn]; rfl
      show Function.update (ch.paramsN (m + 1) hn ζ).2.1 (Fin.last m) _ k =
        (fun a => (((ch.recenter D h).children[(k : ℕ)]'(by rw [hl]; exact k.2)).center a : ℂ),
          fun a => (((ch.recenter D h).children[(k : ℕ)]'(by rw [hl]; exact k.2)).phase a : ℂ))
      rw [List.getElem_of_eq hchild]
      by_cases hk : k = Fin.last m
      · subst hk
        rw [Function.update_self]
        simp only [Fin.val_last]
        rw [List.getElem_append_right (by rw [hdl])]
        simp only [hdl, Nat.sub_self, List.getElem_singleton]
        rw [hR]
        refine Prod.ext ?_ ?_
        · funext a
          simp [RealChain.paramsN, ofRealVec]
        · funext a
          simp only [Pi.add_apply, Pi.smul_apply, epsInvC, ofRealVec, smul_eq_mul]
          simp [RealChain.paramsN, RealChain.lastLevel, hn]
          left
          rfl
      · have hkm : (k : ℕ) < m := by
          have := k.2
          have : (k : ℕ) ≠ m := fun h' => hk (Fin.ext (by simp [h']))
          omega
        rw [Function.update_of_ne hk, List.getElem_append_left (by rw [hdl]; exact hkm),
          List.getElem_dropLast]
        rfl
    · rfl

/-- **Small real recenterings of an admissible chain are admissible.** -/
theorem recenter_admissible (env : ChainEnv D b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) :
    ∀ᶠ h in 𝓝 (0 : Vec 2), IsAdmissibleChain D b j₀ i p (ch.recenter D h) := by
  by_cases hne : ch.children = []
  · refine Eventually.of_forall fun h => ?_
    rw [recenter_nil D ch hne h]
    exact hch
  · obtain ⟨m, hn⟩ : ∃ m, ch.children.length = m + 1 :=
      ⟨ch.children.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
    have hΛ1 := env.hΛ1
    have hc := children_eq_snoc hn
    set c := ch.children[m]'(by omega) with hcdef
    have hbd := hch.2.2.2.2.2.2 m (by omega)
    have hpos : 0 < b * D.eps (ch.data.baseLevel + m + 1) :=
      mul_pos env.hb0 (Construction.Stream.ocEpsilon_pos hΛ1)
    set δ : ℝ := ((1 + 2) * b / 4 * D.eps (ch.baseLevel + 1 + m) -
      ∑ a : Fin 2, |c.center a|) / 3 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hdd := chainOK_of_admissible hch
    rw [hn] at hdd
    have hx : ch.paramsN (m + 1) hn 0 ∈ carrierC D b ch.data (m + 1) 2 :=
      paramsC_transport ch ch.data (m + 1) rfl hn _ 0 rfl
        (fun dd n P => P ∈ carrierC D b dd n 2) (GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch 0)
    filter_upwards [Metric.ball_mem_nhds (0 : Vec 2) (lt_min hδ0 hpos)] with h hh
    rw [mem_ball, dist_zero_right] at hh
    have hh1 : ‖h‖ < δ := hh.trans_le (min_le_left _ _)
    have hh2 : ‖ofRealVec h‖ < b * D.eps (ch.data.baseLevel + m + 1) :=
      (norm_ofRealVec_le h).trans_lt (hh.trans_le (min_le_right _ _))
    have hR := norm_recShift_le env hdd hx hh2
    rw [recShift_real env hch hn 0 h] at hR
    have hRr : ‖recenterShift D ch c h‖ ≤ 3 / 2 * ‖h‖ :=
      (norm_le_norm_ofRealVec _).trans (hR.trans
        (mul_le_mul_of_nonneg_left (norm_ofRealVec_le h) (by norm_num)))
    rw [recenter_snoc D ch ch.children.dropLast c hc h]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hch
    have hdl : ch.children.dropLast.length = m := by rw [List.length_dropLast, hn]; rfl
    refine ⟨?_, h2, ?_, h4, h5, h6, ?_⟩
    · simp only [RealChain.ctxLevel, RealChain.lastLevel, List.length_append, hdl,
        List.length_singleton] at h1 ⊢
      rw [hn] at h1
      exact h1
    · simp only [List.length_append, hdl, List.length_singleton]
      rw [h3, hn]
    · intro k hk
      simp only [List.length_append, hdl, List.length_singleton] at hk
      by_cases hkm : k < m
      · rw [List.getElem_append_left (by rw [hdl]; exact hkm), List.getElem_dropLast]
        exact h7 k (by omega)
      · have hk' : m = k := by omega
        subst hk'
        rw [List.getElem_append_right (by rw [hdl])]
        simp only [hdl, Nat.sub_self, List.getElem_singleton]
        have hsum : ∑ a : Fin 2, |(c.center + recenterShift D ch c h) a| ≤
            ∑ a : Fin 2, |c.center a| + 2 * ‖recenterShift D ch c h‖ := by
          rw [Fin.sum_univ_two, Fin.sum_univ_two]
          have e0 := norm_le_pi_norm (recenterShift D ch c h) 0
          have e1 := norm_le_pi_norm (recenterShift D ch c h) 1
          rw [Real.norm_eq_abs] at e0 e1
          simp only [Pi.add_apply]
          linarith [abs_add_le (c.center 0) (recenterShift D ch c h 0),
            abs_add_le (c.center 1) (recenterShift D ch c h 1)]
        calc ∑ a : Fin 2, |(c.center + recenterShift D ch c h) a|
            ≤ ∑ a : Fin 2, |c.center a| + 2 * ‖recenterShift D ch c h‖ := hsum
          _ ≤ ∑ a : Fin 2, |c.center a| + 3 * ‖h‖ := by linarith
          _ < ∑ a : Fin 2, |c.center a| + 3 * δ := by linarith
          _ = (1 + 2) * b / 4 * D.eps (ch.baseLevel + 1 + m) := by rw [hδ]; ring

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: evaluation in the coarser chart** (`evalChild`). The extension of
`ϖ_{i+1,𝗉'}(t) c(t, 𝒜^♮)` is the cutoff times the extension of the family `c` of the finer slot at
the appended parameters `appendC x t` (`evalF`). Where the cutoff does not vanish, the appended
parameters lie in the carrier of the finer slot, so `evalF` is holomorphic; it is measurable in time
by the Carathéodory property of the family extension (`measurable_caratheodory_comp`); the
final-phase translations become translations of the appended child's phase, where the family is
symmetric. Along the final-phase strip of width `3b + b/128` the appended parameters stay in the
carrier of the same reserve `mres ≥ 0`, so the final-phase modes are at most `ϖ e^{-6πb|h|}` times
the bound of the family (`CtxInv.evalChild`). -/

open AVRegularity.Providers.ComplexFlow

/-! ### Carathéodory composition -/

/-- **Measurability of a composition with a family continuous in the parameters and measurable in
time.** -/
theorem measurable_caratheodory_comp {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {m : ℕ} {T : Set ℝ} {U : Set (ChainParamsC m)}
    {G : ℝ → ChainParamsC m → ℂ} (hG : ∀ t ∈ T, ContinuousOn (G t) U)
    (hm : ∀ y ∈ U, Measurable fun t : T => G t y) (τ : α → T) (hτ : Continuous τ) (φ : α → U)
    (hφ : Continuous φ) : Measurable fun a => G (τ a) (φ a) := by
  set u : U → T → ℂ := fun y t => G t y with hu
  have hc : ∀ t : T, Continuous fun y : U => u y t := fun t =>
    (continuousOn_iff_continuous_domRestrict.mp (hG t t.2))
  have hmeas : ∀ y : U, Measurable (u y) := fun y => hm y y.2
  have hU := measurable_uncurry_of_continuous_of_measurable hc hmeas
  exact hU.comp (hφ.prodMk hτ).measurable

/-! ### The cutoff -/

theorem cutoff_nonneg (D : OCData) (k : ℕ) (p : ℤ) (t : ℝ) : 0 ≤ ocCutoff D.α D.q D.Λ k p t :=
  Real.smoothTransition.nonneg _

theorem cutoff_le_one (D : OCData) (k : ℕ) (p : ℤ) (t : ℝ) : ocCutoff D.α D.q D.Λ k p t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The support of the cutoff lies in the output window of its slot. -/
theorem mem_window_of_cutoff {D : OCData} (hΛ : 1 ≤ D.Λ) {k : ℕ} {p : ℤ} {t : ℝ}
    (hc : ocCutoff D.α D.q D.Λ k p t ≠ 0) : t ∈ ocPulseWindow D.α D.q D.Λ k p := by
  set τ := ocTau D.α D.q D.Λ k with hτdef
  have hτ0 : 0 < τ := Construction.Stream.ocTau_pos hΛ
  have hpos : 0 < 5 / 2 - 2 * |t - (p : ℝ) * τ| / τ := by
    by_contra hneg
    exact hc (Real.smoothTransition.zero_of_nonpos (not_lt.1 hneg))
  have habs : |t - (p : ℝ) * τ| < 5 * τ / 4 := by
    have h1 : 2 * |t - (p : ℝ) * τ| / τ < 5 / 2 := by linarith
    rw [div_lt_iff₀ hτ0] at h1
    linarith
  have habs' := abs_lt.1 habs
  constructor <;> nlinarith [habs'.1, habs'.2]

/-! ### The evaluation -/

/-- The data on which the evaluation is defined: `n + 1` slots, last family of level `i - 1`. -/
def EvalGood (i : ℕ) (dd : ChainData) (n : ℕ) : Prop :=
  dd.slots.length = n + 1 ∧ dd.baseLevel + n + 1 = i

open scoped Classical in
/-- **The extension of the evaluation in the coarser chart.** -/
def evalF (D : OCData) (i : ℕ) (p' : ℤ) (G : Ext) : Ext :=
  fun dd n t x => if EvalGood i dd n then
    ((ocCutoff D.α D.q D.Λ (i + 1) p' t : ℝ) : ℂ) * G (appData dd p') (n + 1) t (appendC D dd n p' t x)
    else 0

theorem AdmData.evalGood {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {dd : ChainData} {n : ℕ}
    (h : AdmData D b j₀ i p dd n) : EvalGood i dd n := by
  obtain ⟨ch, hch, hd, hn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hd, ← hn]; exact hch.2.2.1
  · rw [← hd, ← hn]; exact hch.1

/-- Admissible data with an appended child. -/
theorem AdmData.append {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {dd : ChainData} {n : ℕ}
    (hb : 0 < b) (hΛ : 1 ≤ D.Λ) (h : AdmData D b j₀ i p dd n) {p' : ℤ} (hp' : Odd p')
    (hsch : IsScheduledIn D i p' p) : AdmData D b j₀ (i + 1) p' (appData dd p') (n + 1) := by
  obtain ⟨ch, hch, hd, hn⟩ := h
  obtain ⟨hctx, hbase, hlen, hslot, hodd, hsched, hchild⟩ := hch
  refine ⟨{ ch with slots := ch.slots ++ [p'], children := ch.children ++ [⟨0, 0⟩] },
    ⟨?_, hbase, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [RealChain.ctxLevel, RealChain.lastLevel, List.length_append, List.length_singleton]
    simp only [RealChain.ctxLevel, RealChain.lastLevel] at hctx
    omega
  · simp [hlen]
  · simp [RealChain.slot]
  · intro q' hq'
    simp only [List.mem_append, List.mem_singleton] at hq'
    rcases hq' with h | h
    · exact hodd q' h
    · rw [h]; exact hp'
  · intro kk hkk
    simp only [List.length_append, List.length_singleton] at hkk
    by_cases hlt : kk + 1 < ch.slots.length
    · rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
      exact hsched kk hlt
    · have hkk' : kk = ch.children.length := by omega
      subst hkk'
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      have e1 : ch.baseLevel + 1 + ch.children.length = i := by
        simp only [RealChain.ctxLevel, RealChain.lastLevel] at hctx; omega
      have e2 : ch.slots[ch.children.length] = p := by
        have := hslot
        simp only [RealChain.slot, List.getLastD_eq_getLast?] at this
        rw [List.getLast?_eq_getElem?] at this
        simp only [hlen, Nat.add_sub_cancel] at this
        rw [List.getElem?_eq_getElem (by omega)] at this
        simpa using this
      simp only [e1, e2]
      simpa [hlen] using hsch
  · intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hlt : k < ch.children.length
    · rw [List.getElem_append_left hlt]; exact hchild k hlt
    · have hk' : k = ch.children.length := by omega
      subst hk'
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_singleton, Pi.zero_apply, abs_zero,
        Finset.sum_const_zero]
      have : 0 < D.eps (ch.baseLevel + 1 + ch.children.length) :=
        Construction.Stream.ocEpsilon_pos hΛ
      positivity
  · rw [← hd]; rfl
  · rw [← hn]; simp

section Eval

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- The appended parameters of good data lie in the carrier of the appended data where the cutoff
does not vanish. -/
theorem appendC_mem_of_good (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 10000)
    (hah : ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤ b / 10000) {p' : ℤ}
    {dd : ChainData} {n : ℕ} (hg : EvalGood i dd n) {t : ℝ}
    (hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0) {mres : ℝ} (hm0 : 0 ≤ mres)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2)
    (hxm1 : (∑ a : Fin 2, |(x.1 a).im|) < (1 + mres / 4) * (1 / 100) * D.eps dd.baseLevel)
    (hxm2 : ∀ k : Fin n, (∑ a : Fin 2, ‖(x.2.1 k).1 a‖) <
        (1 + mres) * b / 4 * D.eps (dd.baseLevel + 1 + k) ∧
      |((x.2.1 k).2 (transverseIndex (dd.slots.getD k 0))).im| < (3 + mres / 4) * b + b / 64)
    (hxm3 : |(x.2.2 (transverseIndex (dd.slots.getLastD 0))).im| < (3 + mres / 4) * b + b / 64) :
    appendC D dd n p' t x ∈ carrierC D b (appData dd p') (n + 1) mres := by
  have hlev : appLevel dd n = i := hg.2
  have ht : t ∈ slotWin D (appLevel dd n + 1) p' := by
    rw [hlev]; exact mem_slotWin_of_cutoff D hΛ hcut
  have hah' : ocA D.α D.q D.Λ (appLevel dd n) * ocTauPP D.α D.q D.Λ (appLevel dd n + 1) ≤
      b / 10000 := by rw [hlev]; exact hah
  exact appendC_mem_carrierC hζ hΛ hb0 hb1 hg.1 hah' ht hm0 hx hxm1 hxm2 hxm3

theorem appendC_mem_of_good₂ (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 10000)
    (hah : ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤ b / 10000) {p' : ℤ}
    {dd : ChainData} {n : ℕ} (hg : EvalGood i dd n) {t : ℝ}
    (hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t ≠ 0) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) :
    appendC D dd n p' t x ∈ carrierC D b (appData dd p') (n + 1) 2 :=
  appendC_mem_of_good hζ hΛ hb0 hb1 hah hg hcut (by norm_num) hx hx.1 hx.2.1
    (by have := hx.2.2; linarith)

/-- The strain-time smallness at level `i` from the carrier start. -/
theorem hah_of_start {b : ℝ} (hb0 : 0 < b) {j₀ i : ℕ}
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hij : j₀ ≤ i) : ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤ b / 10000 := by
  have h1 := hstart i (by omega)
  have hpi : 10000 ≤ 2 * (64 * (8 * Real.pi ^ 2)) := by
    have := Real.pi_gt_d2; nlinarith
  have h2 : b / (64 * (8 * Real.pi ^ 2)) ≤ 2 * (b / 10000) := by
    rw [div_le_iff₀ (by positivity)]
    calc b = b / 10000 * 10000 := by ring
      _ ≤ b / 10000 * (2 * (64 * (8 * Real.pi ^ 2))) :=
          mul_le_mul_of_nonneg_left hpi (by positivity)
      _ = _ := by ring
  linarith

/-- **Evaluation in the coarser chart.** -/
theorem CtxInv.evalChild (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 10000)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hij : j₀ ≤ i) {p' : ℤ} (hp' : Odd p') (hsch : IsScheduledIn D i p' p)
    {fc : GenSort.Sem .fam} {G : Ext} {Bc : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hc : FamInv D b j₀ (i + 1) p' fc G Bc) :
    CtxInv D b j₀ i p
      (fun t ch ζ => ocCutoff D.α D.q D.Λ (i + 1) p' t * fc t (ch.appendChild D p' t ζ))
      (evalF D i p' G)
      (fun mres h t => ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) p' t) *
        ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) * Bc mres 0 t) where
  hol dd n t ht := by
    classical
    have hah := hah_of_start hb0 hstart hij
    by_cases hg : EvalGood i dd n
    · by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
      · have : evalF D i p' G dd n t = fun _ => 0 := by
          funext x; simp [evalF, hg, hcut]
        rw [this]; exact differentiableOn_const 0
      · have htw := mem_window_of_cutoff hΛ hcut
        have hd := (hc.hol (appData dd p') (n + 1) t htw).comp
          (differentiable_appendC dd n p' t).differentiableOn
          (fun x hx => appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg hcut hx)
        refine (hd.const_mul ((ocCutoff D.α D.q D.Λ (i + 1) p' t : ℝ) : ℂ)).congr fun x _ => ?_
        simp [evalF, hg]
    · have : evalF D i p' G dd n t = fun _ => 0 := by
        funext x; simp [evalF, hg]
      rw [this]; exact differentiableOn_const 0
  meas dd n x hx := by
    classical
    have hah := hah_of_start hb0 hstart hij
    by_cases hg : EvalGood i dd n
    · set S : Set (ocPulseWindow D.α D.q D.Λ i p) :=
        {t | ocCutoff D.α D.q D.Λ (i + 1) p' (t : ℝ) ≠ 0} with hS
      have hcutc : Continuous fun t : ℝ => ocCutoff D.α D.q D.Λ (i + 1) p' t := by
        unfold ocCutoff; exact Real.smoothTransition.continuous.comp (by fun_prop)
      have hSm : MeasurableSet S :=
        (isOpen_ne_fun (hcutc.comp continuous_subtype_val) continuous_const).measurableSet
      refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
      · have hτ : Continuous fun t : S => (⟨(t : ℝ), mem_window_of_cutoff hΛ t.2⟩ :
            ocPulseWindow D.α D.q D.Λ (i + 1) p') :=
          (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        have hφ : Continuous fun t : S => (⟨appendC D dd n p' (t : ℝ) x,
            appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg t.2 hx⟩ :
              carrierC D b (appData dd p') (n + 1) 2) := by
          refine Continuous.subtype_mk ?_ _
          exact (continuous_appendC hζ dd n p').comp
            (continuous_const.prodMk (continuous_subtype_val.comp continuous_subtype_val))
        have hG := measurable_caratheodory_comp (G := G (appData dd p') (n + 1))
          (fun t ht => (hc.hol (appData dd p') (n + 1) t ht).continuousOn)
          (fun y hy => hc.meas (appData dd p') (n + 1) y hy) _ hτ _ hφ
        have hcm : Measurable fun t : S => ((ocCutoff D.α D.q D.Λ (i + 1) p' (t : ℝ) : ℝ) : ℂ) :=
          (Complex.continuous_ofReal.comp
            (hcutc.comp (continuous_subtype_val.comp continuous_subtype_val))).measurable
        convert hcm.mul hG using 1
        funext t
        simp [evalF, hg]
      · convert measurable_const (a := (0 : ℂ)) using 1
        funext t
        have h0 : ocCutoff D.α D.q D.Λ (i + 1) p' (t : ℝ) = 0 := by
          have := t.2; simp only [hS, mem_compl_iff, mem_ofPred_eq, not_not] at this; exact this
        simp [evalF, hg, h0]
    · convert measurable_const (a := (0 : ℂ)) using 1
      funext t
      simp [evalF, hg]
  agree ch t ht ζ hch := by
    classical
    have hg : EvalGood i ch.data ch.children.length := ⟨hch.2.2.1, hch.1⟩
    simp only [evalF, hg, ite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
    · simp [hcut]
    · have hadm := GenSem.appendChild_admissible D hΛ hζ hb0 hstart i p ch hch p' hp' hsch t
        hcut ζ
      have htw := mem_window_of_cutoff hΛ hcut
      have hl : (ch.appendChild D p' t ζ).children.length = ch.children.length + 1 := by
        simp [RealChain.appendChild]
      have hP := appendC_paramsC ch p' t ζ hl
      have hval := hc.agree (ch.appendChild D p' t ζ) t htw hadm
      have hval' := GenSem.paramsC_transport (ch.appendChild D p' t ζ) (appData ch.data p')
        (ch.children.length + 1) rfl hl _ 0 hP.symm
        (fun dd m P => G dd m t P = (fc t (ch.appendChild D p' t ζ) : ℂ)) hval
      rw [hval']
      push_cast
      ring
  fin dd n t ht x hx v hv := by
    classical
    have hah := hah_of_start hb0 hstart hij
    by_cases hg : EvalGood i dd n
    · simp only [evalF, hg, ite_true]
      by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
      · simp [hcut]
      · congr 1
        rw [appendC_shiftFinal hΛ dd n p' t x hv]
        refine hc.child (appData dd p') (n + 1) t (mem_window_of_cutoff hΛ hcut) _
          (appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg hcut hx) (Fin.last n) v ?_
        rw [show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl, appData_slots_getD_last p' hg.1]
        exact hv
    · simp [evalF, hg]
  child dd n t ht x hx k v hv := by
    classical
    have hah := hah_of_start hb0 hstart hij
    by_cases hg : EvalGood i dd n
    · simp only [evalF, hg, ite_true]
      by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
      · simp [hcut]
      · congr 1
        rw [appendC_shiftChild dd n p' t x k v]
        refine hc.child (appData dd p') (n + 1) t (mem_window_of_cutoff hΛ hcut) _
          (appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg hcut hx) k.castSucc v ?_
        rw [show ((k.castSucc : Fin (n + 1)) : ℕ) = k from rfl,
          appData_slots_getD_lt p' (by rw [hg.1]; omega)]
        exact hv
    · simp [evalF, hg]
  bdd dd n x hx := by
    classical
    have hah := hah_of_start hb0 hstart hij
    by_cases hg : EvalGood i dd n
    · have : ProperSpace (ChainParamsC n) := FiniteDimensional.proper ℂ _
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp (isOpen_carrierC D b dd n 2) x hx
      set T₀ := slotWin D (i + 1) p'
      set K : Set (ChainParamsC (n + 1)) :=
        (fun r : ChainParamsC n × ℝ => appendC D dd n p' r.2 r.1) '' (closedBall x (r / 2) ×ˢ T₀)
      have hKc : IsCompact K :=
        ((isCompact_closedBall x _).prod isCompact_Icc).image (continuous_appendC hζ dd n p')
      have hKS : K ⊆ carrierC D b (appData dd p') (n + 1) 2 := by
        rintro _ ⟨⟨y, t⟩, ⟨hy, htT⟩, rfl⟩
        have hy' : y ∈ carrierC D b dd n 2 :=
          hrS (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith)))
        have hlev : appLevel dd n = i := hg.2
        have ht' : t ∈ slotWin D (appLevel dd n + 1) p' := by rw [hlev]; exact htT
        have hah' : ocA D.α D.q D.Λ (appLevel dd n) *
            ocTauPP D.α D.q D.Λ (appLevel dd n + 1) ≤ b / 10000 := by rw [hlev]; exact hah
        exact appendC_mem_carrierC hζ hΛ hb0 hb1 hg.1 hah' ht' (by norm_num) hy' hy'.1 hy'.2.1
          (by have := hy'.2.2; linarith)
      obtain ⟨M, hM⟩ := (hc.bdd (appData dd p') (n + 1)).exists_bound hKc hKS
      refine ⟨ball x (r / 2), ball_mem_nhds x (by positivity), max M 0, fun t _ y hy => ?_⟩
      simp only [evalF, hg, ite_true]
      by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
      · simp [hcut]
      · have htw := mem_window_of_cutoff hΛ hcut
        have hts : t ∈ T₀ := mem_slotWin_of_cutoff D hΛ hcut
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg D _ _ t)]
        have hGb := hM t htw _ ⟨(y, t), ⟨mem_closedBall.mpr (mem_ball.mp hy).le, hts⟩, rfl⟩
        calc ocCutoff D.α D.q D.Λ (i + 1) p' t *
              ‖G (appData dd p') (n + 1) t (appendC D dd n p' t y)‖ ≤ 1 * max M 0 :=
            mul_le_mul (cutoff_le_one D _ _ t) (hGb.trans (le_max_left _ _)) (norm_nonneg _)
              zero_le_one
          _ = max M 0 := one_mul _
    · exact ⟨univ, univ_mem, 0, fun t _ y _ => by simp [evalF, hg]⟩
  mode mres hm0 hm2 h t ht dd n hdd x hx hre := by
    classical
    have hah := hah_of_start hb0 hstart hij
    have hg := hdd.evalGood
    have hsl := hdd.lastSlot
    have hx2 := carrierC_mono hb0.le hm2 hx
    set q := transverseIndex p with hq
    rw [finalPhaseCoeff_eq_pcoeff]
    by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
    · have e : (fun s : ℝ => lineF q (evalF D i p' G dd n t) x s) = fun _ => 0 := by
        funext s; simp [lineF, evalF, hg, hcut]
      rw [e]; simp [pcoeff]
    set ϖ := ocCutoff D.α D.q D.Λ (i + 1) p' t with hϖ
    have htw := mem_window_of_cutoff hΛ hcut
    set g : ℂ → ℂ := fun z => G (appData dd p') (n + 1) t
      (appendC D dd n p' t (x.1, x.2.1, x.2.2 + evec q z)) with hgdef
    have hline : (fun s : ℝ => lineF q (evalF D i p' G dd n t) x s) =
        fun s : ℝ => (ϖ : ℂ) * g s := by
      funext s; simp [lineF, evalF, hg, hgdef, ← hϖ]
    have hpc : pcoeff (fun s : ℝ => (ϖ : ℂ) * g s) h = (ϖ : ℂ) * pcoeff (fun s : ℝ => g s) h := by
      unfold pcoeff
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext s; ring
    rw [hline, hpc, enorm_mul]
    have hϖ0 : 0 ≤ ϖ := cutoff_nonneg D _ _ t
    have hϖpos : 0 < ϖ := lt_of_le_of_ne hϖ0 (Ne.symm hcut)
    have hen : ‖(ϖ : ℂ)‖ₑ = ENNReal.ofReal ϖ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hϖ0]
    rw [hen, mul_assoc]
    refine mul_le_mul' le_rfl ?_
    by_cases htop : Bc mres 0 t = ⊤
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']; exact le_top
    -- the line through the appended parameters
    have hmem : ∀ z : ℂ, |z.im| < 3 * b + b / 128 →
        ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) ∈ carrierC D b dd n 2 := by
      intro z hz
      have := mem_carrierC_line hx2 (hre _) (z := z) (by linarith)
      rwa [hsl] at this
    have hgb : ∀ z : ℂ, |z.im| < 3 * b + b / 128 → ‖g z‖ ≤ (Bc mres 0 t).toReal := by
      intro z hz
      have hap : appendC D dd n p' t (x.1, x.2.1, x.2.2 + evec q z) ∈
          carrierC D b (appData dd p') (n + 1) mres := by
        refine appendC_mem_of_good hζ hΛ hb0 hb1 hah hg hcut hm0 (hmem z hz) hx.1 hx.2.1 ?_
        show |((x.2.2 + evec q z) (transverseIndex (dd.slots.getLastD 0))).im| < _
        rw [hsl]
        simp only [Pi.add_apply, evec, hq, ↓reduceIte, Complex.add_im, hre _, zero_add]
        have : (3 : ℝ) * b + b / 128 ≤ (3 + mres / 4) * b + b / 64 := by nlinarith
        linarith
      have h1 := hc.mode mres hm0 hm2 t htw (appData dd p') (n + 1)
        (hdd.append hb0 hΛ hp' hsch) _ hap
      rw [← ofReal_norm] at h1
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
    have hgd : DifferentiableOn ℂ g {z : ℂ | |z.im| < 3 * b + b / 128} := by
      have hl : Differentiable ℂ fun z : ℂ => ((x.1, x.2.1, x.2.2 + evec q z) : ChainParamsC n) := by
        refine (differentiable_const _).prodMk ((differentiable_const _).prodMk ?_)
        refine (differentiable_const _).add ?_
        rw [differentiable_pi]
        intro a
        unfold evec
        split_ifs
        · exact differentiable_id
        · exact differentiable_const _
      refine (hc.hol (appData dd p') (n + 1) t htw).comp
        ((differentiable_appendC dd n p' t).comp hl).differentiableOn fun z hz => ?_
      exact appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg hcut (hmem z hz)
    have hgp : ∀ z : ℂ, |z.im| < 3 * b + b / 128 → g (z + 1) = g z := by
      intro z hz
      simp only [hgdef]
      rw [← shiftFinal_line, appendC_shiftFinal hΛ dd n p' t _ (tInt_rvec_any _ q)]
      refine hc.child (appData dd p') (n + 1) t htw _
        (appendC_mem_of_good₂ hζ hΛ hb0 hb1 hah hg hcut (hmem z hz)) (Fin.last n) (rvec q) ?_
      rw [show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl, appData_slots_getD_last p' hg.1]
      exact tInt_rvec_any _ q
    have hdec := norm_pcoeff_le_of_strip hgd hgp hgb h (w' := 3 * b) (by positivity) (by linarith)
    rw [← ofReal_norm, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (hdec.trans (le_of_eq ?_))
    rw [mul_comm]
    congr 2
    ring

end Eval

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexFlow

/-! **Carrier calculus: the appended child with the displacement scalar as a parameter.** The
appended child of the complex chain (`appFam D dd n p' t`) depends on the output time `t` only
through the real scalar `λ(t) = ε_i⁻¹ ∫_t^{s_{𝗉'}} p_𝗉` of its relative displacement. Treating `λ`
as a complex parameter gives one family over `ChainParamsC n × ℂ` (`appFamX`), the child of the
pullback of the last family (`CFam.pullFst`). It is over the finer slot on the product of the outer
carrier with a disc containing every `λ(t)` with `t` in the window of the finer slot
(`appFamX_over`); in particular it is jointly continuous in the parameters, the time and the point,
and `appFam D dd n p' t` at `x` is `appFamX` at `(x, λ(t))` (`appFam_jacC_eq`). This gives the
measurability in time of the child-frame letters. -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- **The pullback of a family** to the parameters with an extra complex coordinate. -/
def pullFst (F : CFam Par) : CFam (Par × ℂ) :=
  ⟨fun P => F.fl P.1, fun P => F.ctr P.1, F.anc⟩

variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

theorem OK.pullFst (h : F.OK Ω W ϱ Λ T) {V : Set ℂ} (hV : IsOpen V) :
    F.pullFst.OK (Ω ×ˢ V) W ϱ Λ T where
  hϱ := h.hϱ
  hΛ := h.hΛ
  hT := h.hT
  hΛT := h.hΛT
  anc_mem := h.anc_mem
  hΩ := h.hΩ.prod hV
  ctr_hol := h.ctr_hol.comp differentiableOn_fst fun P hP => hP.1
  cur_anc P hP := h.cur_anc P.1 hP.1
  hol u hu r hr := by
    have hφ : DifferentiableOn ℂ (fun q : (Par × ℂ) × CVec => ((q.1.1, q.2) : Par × CVec))
        (F.pullFst.dom (Ω ×ˢ V) ϱ r) :=
      (differentiable_fst.fst.prodMk differentiable_snd).differentiableOn
    exact (h.hol u hu r hr).comp hφ fun q hq => ⟨hq.1.1, hq.2⟩
  init P hP r hr y hy := h.init P.1 hP.1 r hr y hy
  jac P hP u hu r hr y hy := h.jac P.1 hP.1 u hu r hr y hy
  group P hP u hu v hv r hr y hy := h.group P.1 hP.1 u hu v hv r hr y hy

omit [NormedSpace ℂ Par] in
theorem TimeCont.pullFst (h : F.TimeCont Ω W ϱ) (V : Set ℂ) :
    F.pullFst.TimeCont (Ω ×ˢ V) W ϱ := by
  intro r hr
  have hφ : Continuous fun q : (Par × ℂ) × ℝ × CVec => ((q.1.1, q.2.1, q.2.2) : Par × ℝ × CVec) :=
    continuous_fst.fst.prodMk (continuous_snd.fst.prodMk continuous_snd.snd)
  exact (h r hr).comp hφ.continuousOn fun q hq => ⟨hq.1.1, hq.2.1, hq.2.2⟩

theorem Over.pullFst {D : OCData} {b : ℝ} {l : ℕ} {p : ℤ} (h : F.Over D b Ω l p) {V : Set ℂ}
    (hV : IsOpen V) : F.pullFst.Over D b (Ω ×ˢ V) l p where
  anc := h.anc
  ok := h.ok.pullFst hV
  cont := h.cont.pullFst V

end CFam

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

/-- The level and the slot of the appended child. -/
abbrev appSlot (dd : ChainData) : ℤ := dd.slots.getLastD 0

/-- The shear of the appended child at the final phase `ζ`. -/
def appShear (D : OCData) (dd : ChainData) (n : ℕ) (ζ : CVec) : CVec :=
  ocShearVelC D.α D.q D.Λ (appLevel dd n) (appSlot dd) (((D.eps (appLevel dd n) : ℝ) : ℂ) • ζ)

/-- **The appended child with the displacement scalar as a parameter.** -/
def appFamX (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) : CFam (ChainParamsC n × ℂ) :=
  (chainFam D dd n).pullFst.child D (appLevel dd n) (appSlot dd)
    (D.slotAnchor (appLevel dd n + 1) p')
    (fun P => epsC D (appLevel dd n) • (P.2 • appShear D dd n P.1.2.2))
    (fun P => P.1.2.2 + P.2 • appShear D dd n P.1.2.2)

/-- The displacement scalar `λ(t) = ε_i⁻¹ ∫_t^{s_{𝗉'}} p_𝗉` of the appended child. -/
def lamT (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t : ℝ) : ℂ :=
  (((D.eps (appLevel dd n))⁻¹ * ∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
    ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v : ℝ) : ℂ)

theorem appFam_jacC_eq (D : OCData) (dd : ChainData) (n : ℕ) (p' : ℤ) (t u : ℝ)
    (x : ChainParamsC n) :
    (appFam D dd n p' t).jacC x u = (appFamX D dd n p').jacC (x, lamT D dd n p' t) u := rfl

/-- The radius of the disc of displacement scalars. -/
def lamR (D : OCData) (dd : ChainData) (n : ℕ) : ℝ :=
  2 * (6 / 5 * ocTauPP D.α D.q D.Λ (appLevel dd n + 1)) / D.eps (appLevel dd n)

/-- The parameter set of the extended appended child. -/
def appOmega (D : OCData) (b : ℝ) (dd : ChainData) (n : ℕ) : Set (ChainParamsC n × ℂ) :=
  carrierC D b dd n 2 ×ˢ ball (0 : ℂ) (lamR D dd n)

/-- The displacement scalars of the window of the finer slot lie in the disc. -/
theorem lamT_mem (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {dd : ChainData} {n : ℕ} {p' : ℤ}
    {t : ℝ} (ht : t ∈ slotWin D (appLevel dd n + 1) p') :
    lamT D dd n p' t ∈ ball (0 : ℂ) (lamR D dd n) := by
  have he : 0 < D.eps (appLevel dd n) := Construction.Stream.ocEpsilon_pos hΛ
  have hh : 0 < ocTauPP D.α D.q D.Λ (appLevel dd n + 1) := Construction.Stream.ocTauPP_pos hΛ
  rw [mem_ball, dist_zero_right, lamT, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (inv_pos.mpr he)]
  have h1 := abs_integral_pulse_le D hζ (appLevel dd n) (appSlot dd)
    (D.slotAnchor (appLevel dd n + 1) p') t
  have h2 := abs_sub_le_of_mem_slotWin D (anchor_mem_slotWin D hΛ (appLevel dd n + 1) p') ht
  have h3 : |∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
      ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v| ≤
      6 / 5 * ocTauPP D.α D.q D.Λ (appLevel dd n + 1) := by
    exact h1.trans h2
  unfold lamR
  rw [lt_div_iff₀ he]
  calc (D.eps (appLevel dd n))⁻¹ * |∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
        ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v| * D.eps (appLevel dd n)
      = |∫ v in t..D.slotAnchor (appLevel dd n + 1) p',
        ocPulse D.α D.q D.Λ D.ζ (appLevel dd n) (appSlot dd) v| := by field_simp
    _ < 2 * (6 / 5 * ocTauPP D.α D.q D.Λ (appLevel dd n + 1)) := by linarith

/-- The center and the phase of the extended appended child satisfy the hypotheses of the child
step. -/
theorem appFamX_conds (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) :
    DifferentiableOn ℂ (fun P : ChainParamsC n × ℂ =>
        epsC D (appLevel dd n) • (P.2 • appShear D dd n P.1.2.2)) (appOmega D b dd n) ∧
      DifferentiableOn ℂ (fun P : ChainParamsC n × ℂ => P.1.2.2 + P.2 • appShear D dd n P.1.2.2)
        (appOmega D b dd n) ∧
      (∀ P ∈ appOmega D b dd n, ‖epsC D (appLevel dd n) • (P.2 • appShear D dd n P.1.2.2)‖ ≤
        3 / 4 * b * D.eps (dd.baseLevel + n + 1)) ∧
      ∀ P ∈ appOmega D b dd n,
        |((P.1.2.2 + P.2 • appShear D dd n P.1.2.2) (transverseIndex (appSlot dd))).im| ≤ phB b := by
  have hΛ1 := env.hΛ1
  have hS : LevelScales D b (dd.baseLevel + n) :=
    levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
      (by have := hdd.base; omega)
  have he : 0 < D.eps (appLevel dd n) := Construction.Stream.ocEpsilon_pos hΛ1
  have hdiff : Differentiable ℂ fun P : ChainParamsC n × ℂ => appShear D dd n P.1.2.2 := by
    unfold appShear
    exact (differentiable_ocShearVelC _ _ _ _ _).comp (by fun_prop)
  refine ⟨?_, ?_, fun P hP => ?_, fun P hP => ?_⟩
  · exact (by fun_prop : Differentiable ℂ fun P : ChainParamsC n × ℂ =>
      epsC D (appLevel dd n) • (P.2 • appShear D dd n P.1.2.2)).differentiableOn
  · exact (by fun_prop : Differentiable ℂ fun P : ChainParamsC n × ℂ =>
      P.1.2.2 + P.2 • appShear D dd n P.1.2.2).differentiableOn
  · -- the center of the appended child is small
    have hshear := norm_ocShearVelC_le D.α D.q D.Λ (appLevel dd n) (appSlot dd) he
      (((D.eps (appLevel dd n) : ℝ) : ℂ) • P.1.2.2)
    have him : |(P.1.2.2 (transverseIndex (appSlot dd))).im| < (3 + 2 / 4) * b := hP.1.2.2
    have hexp : Real.exp (shearFreq D.q D.Λ (appLevel dd n) *
        |((((D.eps (appLevel dd n) : ℝ) : ℂ) • P.1.2.2) (transverseIndex (appSlot dd))).im|) ≤
        Real.exp (30 * Real.pi * b) := by
      refine Real.exp_le_exp.mpr ?_
      have e1 : ((((D.eps (appLevel dd n) : ℝ) : ℂ) • P.1.2.2) (transverseIndex (appSlot dd))).im =
          D.eps (appLevel dd n) * (P.1.2.2 (transverseIndex (appSlot dd))).im := by
        simp
      rw [e1, abs_mul, abs_of_pos he]
      unfold shearFreq
      have h2 : 2 * Real.pi * (ocEpsilon D.q D.Λ (appLevel dd n))⁻¹ *
          (D.eps (appLevel dd n) * |(P.1.2.2 (transverseIndex (appSlot dd))).im|) =
          2 * Real.pi * |(P.1.2.2 (transverseIndex (appSlot dd))).im| := by
        show 2 * Real.pi * (D.eps (appLevel dd n))⁻¹ * (D.eps (appLevel dd n) * _) = _
        field_simp
      rw [h2]
      nlinarith [Real.pi_pos, env.hb0, abs_nonneg (P.1.2.2 (transverseIndex (appSlot dd))).im]
    have hA := shearAmp_eq (α := D.α) he
    have hlam : ‖P.2‖ < lamR D dd n := by have := hP.2; rwa [mem_ball, dist_zero_right] at this
    have hX := exp_small_le env.hb0.le env.hb1
    have hah : ocA D.α D.q D.Λ (appLevel dd n) * ocTauPP D.α D.q D.Λ (appLevel dd n + 1) ≤
        b / 10000 := hS.hah
    have ha0 : 0 ≤ ocA D.α D.q D.Λ (appLevel dd n) := Real.rpow_nonneg he.le _
    have hh0 : 0 ≤ ocTauPP D.α D.q D.Λ (appLevel dd n + 1) :=
      (Construction.Stream.ocTauPP_pos hΛ1).le
    rw [norm_smul, norm_smul, epsC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
    have hsh : ‖appShear D dd n P.1.2.2‖ ≤
        2 * Real.pi * ocA D.α D.q D.Λ (appLevel dd n) * D.eps (appLevel dd n) * (101 / 100) := by
      refine hshear.trans ?_
      rw [hA]
      exact mul_le_mul_of_nonneg_left (hexp.trans hX) (by have := Real.pi_pos; positivity)
    unfold lamR at hlam
    calc D.eps (appLevel dd n) * (‖P.2‖ * ‖appShear D dd n P.1.2.2‖)
        ≤ D.eps (appLevel dd n) * ((2 * (6 / 5 * ocTauPP D.α D.q D.Λ (appLevel dd n + 1)) /
            D.eps (appLevel dd n)) * (2 * Real.pi * ocA D.α D.q D.Λ (appLevel dd n) *
              D.eps (appLevel dd n) * (101 / 100))) := by
          gcongr
      _ = 24 / 5 * Real.pi * (101 / 100) * (ocA D.α D.q D.Λ (appLevel dd n) *
            ocTauPP D.α D.q D.Λ (appLevel dd n + 1)) * D.eps (appLevel dd n) := by
          field_simp; ring
      _ ≤ 3 / 4 * b * D.eps (dd.baseLevel + n + 1) := by
          have hπ := Real.pi_lt_d2
          show _ ≤ 3 / 4 * b * D.eps (appLevel dd n)
          have : 24 / 5 * Real.pi * (101 / 100) * (ocA D.α D.q D.Λ (appLevel dd n) *
              ocTauPP D.α D.q D.Λ (appLevel dd n + 1)) ≤ 3 / 4 * b := by
            have h1 : 24 / 5 * Real.pi * (101 / 100) ≤ 16 := by nlinarith
            calc _ ≤ 16 * (b / 10000) := mul_le_mul h1 hah (mul_nonneg ha0 hh0) (by norm_num)
              _ ≤ 3 / 4 * b := by nlinarith [env.hb0]
          exact mul_le_mul_of_nonneg_right this he.le
  · -- the appended phase has the transverse imaginary part of the final phase
    show |((P.1.2.2 + P.2 • appShear D dd n P.1.2.2) (transverseIndex (appSlot dd))).im| ≤ phB b
    have h0 : appShear D dd n P.1.2.2 (transverseIndex (appSlot dd)) = 0 := by
      unfold appShear; exact ocShearVelC_transverse _ _ _ _ _ _
    simp only [Pi.add_apply, Pi.smul_apply, h0, smul_zero, add_zero]
    have him : |(P.1.2.2 (transverseIndex (appSlot dd))).im| < (3 + 2 / 4) * b := hP.1.2.2
    have := env.hb0
    unfold phB
    linarith

/-- **The extended appended child is over the finer slot.** -/
theorem appFamX_over (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) {p' : ℤ} (hp' : IsScheduledIn D (appLevel dd n) p' (appSlot dd)) :
    (appFamX D dd n p').Over D b (appOmega D b dd n) (appLevel dd n) p' := by
  have hS : LevelScales D b (dd.baseLevel + n) :=
    levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
      (by have := hdd.base; omega)
  have hF := (env.chainFam_over hdd).pullFst (V := ball (0 : ℂ) (lamR D dd n)) isOpen_ball
  obtain ⟨h1, h2, h3, h4⟩ := appFamX_conds env hdd
  exact hF.child hS env.hζ hp' h1 h2 h3 h4

end AVRegularity.Providers.ComplexFlow
end
