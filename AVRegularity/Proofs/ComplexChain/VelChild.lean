-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexChain.Vel
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
open scoped ENNReal
namespace AVRegularity.Providers.ComplexFlow

/-! **The certificate of the Jacobian leaf** `F_t(0)_{ac} − δ_{ac}`. Over a slot `p` of level `i`,
the leaf has the complex extension `jacLeafExt`: on scheduled discrete data over `p` and on the
outer carrier, the entry of the complex Jacobian of the last family `chainFam` minus `δ_{ac}`; zero
elsewhere. It is a holomorphic, time-measurable extension of the real leaf
(`jacLeaf_isHolExtension`), and it does not depend on the final phase, so its only nonzero mode is
`h = 0`, where it is at most `K a_{i-1} (6/5) h_i` (`jacLeaf_ctxModeSup_le`). The standing facts of
the construction used here are collected in `ChainEnv`. -/

/-- **The standing facts used by the complex chains**: the scales, the analytic velocities and
the carrier start. -/
structure ChainEnv (D : OCData) (b CH Υ : ℝ) (j₀ : ℕ) : Prop where
  hq : 1 < D.q
  hΛ : 128 ≤ D.Λ
  hα : D.α < 1 / 3
  hζ : IsFastProfile D.ζ
  hvel : ∀ m, ∃ V, HolField (velC D.α D.q D.Λ D.ζ m) (D.eps m / 50) (velA * ocA D.α D.q D.Λ m) V
  hag : ∀ m t x, velC D.α D.q D.Λ D.ζ m t (ofRealVec x) = ofRealVec (streamVel (D.Φ m) t x)
  hb0 : 0 < b
  hb1 : b ≤ 1 / 10000
  hCH : 1 ≤ CH
  hΥ : 1 ≤ Υ
  hcs : IsCarrierStart D.α D.q D.Λ b CH Υ j₀

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

theorem ChainEnv.hΛ1 (env : ChainEnv D b CH Υ j₀) : 1 ≤ D.Λ := by have := env.hΛ; omega

theorem ChainEnv.chainFam_over (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) :
    (chainFam D dd n).Over D b (carrierC D b dd n 2) (dd.baseLevel + n) (dd.slots.getLastD 0) :=
  ComplexFlow.chainFam_over env.hq env.hΛ env.hα env.hζ env.hvel env.hb0 env.hb1 env.hCH env.hΥ
    env.hcs hdd

/-- The output window of a slot lies in its family window. -/
theorem ocPulseWindow_subset_slotWin (hΛ : 1 ≤ D.Λ) (i : ℕ) (p : ℤ) :
    ocPulseWindow D.α D.q D.Λ i p ⊆ slotWin D i p := by
  intro t ht
  have h1 := abs_le.1 (abs_sub_anchor_le_of_mem_window D hΛ ht)
  have h2 := tau_le D hΛ i
  have h0 : 0 < ocTau D.α D.q D.Λ i := Construction.Stream.ocTau_pos hΛ
  constructor <;> linarith [h1.1, h1.2]

theorem getD_eq_getLastD {p : ℤ} : ∀ (ps : List ℤ), (p :: ps).getD ps.length 0 = (p :: ps).getLastD 0
  | [] => rfl
  | q :: qs => by
    rw [List.length_cons, List.getD_cons_succ, getD_eq_getLastD qs]
    simp

/-- The last slot of scheduled data is the slot `getD n`. -/
theorem ChainOK.getD_last {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n) :
    dd.slots.getD n 0 = dd.slots.getLastD 0 := by
  obtain ⟨p, ps, hsl⟩ : ∃ p ps, dd.slots = p :: ps := by
    rcases h : dd.slots with _ | ⟨p, ps⟩
    · have := hdd.len; rw [h] at this; simp at this
    · exact ⟨p, ps, rfl⟩
  have hlen : ps.length = n := by have := hdd.len; rw [hsl] at this; simpa using this
  rw [hsl, ← hlen, getD_eq_getLastD]

/-! ### The complex Jacobian at real parameters -/

/-- **At the real parameters of an admissible chain, the complex Jacobian is the real one.** -/
theorem jacC_chainFam_real (env : ChainEnv D b CH Υ j₀) {i : ℕ} {p : ℤ} {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2) {t : ℝ} (ht : t ∈ slotWin D i p)
    (a c : Fin 2) :
    (chainFam D ch.data ch.children.length).jacC (ch.paramsC ζ) t a c =
      ((ch.famJac D t a c : ℝ) : ℂ) := by
  have hΛ1 := env.hΛ1
  have hdd := chainOK_of_admissible hch
  have hO := env.chainFam_over hdd
  have hag := chainFam_agree env.hΛ env.hvel env.hag env.hb1 env.hCH env.hΥ env.hcs hch ζ
  have hsep : ∀ m, j₀ ≤ m → ocTauPP D.α D.q D.Λ (m + 1) < ocTau D.α D.q D.Λ m / 48 :=
    fun m hm => separation_of_carrierStart hΛ1 env.hCH env.hcs hm
  set F := chainFam D ch.data ch.children.length
  set x := ch.paramsC ζ
  -- the level and the slot of the last family
  have hi : ch.baseLevel + ch.children.length + 1 = i := hch.1
  have hp : ch.slots.getLastD 0 = p := hch.2.2.2.1
  have hW : slotWin D i p ⊆ slotWin D (ch.baseLevel + 1) (ch.slots.headD 0) := by
    have h1 := hdd.slotWin_subset hΛ1 hsep ch.children.length le_rfl
    have e1 : ch.data.baseLevel + 1 + ch.children.length = i := by
      show ch.baseLevel + 1 + ch.children.length = i; omega
    have e2 : ch.data.slots.getD ch.children.length 0 = p := by rw [hdd.getD_last]; exact hp
    have e3 : ch.data.slots.getD 0 0 = ch.slots.headD 0 := by
      show ch.slots.getD 0 0 = _; rcases ch.slots with _ | ⟨q, qs⟩ <;> rfl
    rw [e1, e2, e3] at h1
    exact h1
  have hanc : F.anc = D.slotAnchor i p := by
    rw [hO.anc]
    show D.slotAnchor (ch.baseLevel + ch.children.length + 1) (ch.slots.getLastD 0) = _
    rw [hi, hp]
  have hancG : F.anc ∈ slotWin D (ch.baseLevel + 1) (ch.slots.headD 0) := by
    rw [hanc]; exact hW (anchor_mem_slotWin D hΛ1 i p)
  have htW : t ∈ slotWin D (ch.data.baseLevel + ch.children.length + 1)
      (ch.data.slots.getLastD 0) := by
    show t ∈ slotWin D (ch.baseLevel + ch.children.length + 1) (ch.slots.getLastD 0)
    rw [hi, hp]; exact ht
  have hxΩ : x ∈ carrierC D b ch.data ch.children.length 2 :=
    GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
  have hU : DifferentiableOn ℂ (fun y => F.fl x t y F.anc) (ball (F.ctr x) (8 * b * D.eps
      (ch.data.baseLevel + ch.children.length))) := fun y hy =>
    (hO.ok.differentiableAt_fl hxΩ htW hO.ok.anc_mem
      (by rw [hO.ok.cur_anc x hxΩ]; exact hy)).differentiableWithinAt
  have hFf : ∀ y, F.fl x t (ofRealVec y) F.anc =
      ofRealVec ((ch.geom D).1 t y (ch.geom D).2.2) := by
    intro y
    have := hag.flow t (hW ht) F.anc hancG y
    rw [← hag.anchor]
    exact this
  have hctr : F.ctr x = ofRealVec (ch.geom D).2.1 := hag.center
  have hx : ofRealVec (ch.geom D).2.1 ∈ ball (F.ctr x) (8 * b * D.eps
      (ch.data.baseLevel + ch.children.length)) := by
    rw [← hctr]; exact mem_ball_self hO.ok.hϱ
  have h := jacMatrix_ofReal_eq isOpen_ball hU hFf hx a c
  show fderiv ℂ (fun y => F.fl x t y F.anc) (F.ctr x) (cbasis c) a = _
  rw [hctr, h]
  rfl

/-! ### The leaf -/

theorem integral_exp_mode (h : ℤ) :
    ∫ s in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) =
      if h = 0 then 1 else 0 := by
  split_ifs with h0
  · subst h0; simp
  · have hh : (h : ℂ) ≠ 0 := by exact_mod_cast h0
    have hc : -(2 * Real.pi * Complex.I * (h : ℂ)) ≠ 0 := by
      have : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      exact neg_ne_zero.mpr (mul_ne_zero this hh)
    have e : (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ)))) =
        fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ)) * s) := by
      funext s; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show -(2 * Real.pi * Complex.I * (h : ℂ)) * ((1 : ℝ) : ℂ) =
        ((-h : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h1]
    simp

/-- The final-phase coefficient of a function invariant under real shifts of the final phase. -/
theorem finalPhaseCoeff_of_invariant {n : ℕ} (q : Fin 2) {G : ChainParamsC n → ℂ}
    {x : ChainParamsC n}
    (hG : ∀ s : ℝ, G (x.1, x.2.1, x.2.2 + fun a => if a = q then (s : ℂ) else 0) = G x)
    (h : ℤ) : finalPhaseCoeff q G x h = if h = 0 then G x else 0 := by
  unfold finalPhaseCoeff
  simp_rw [hG]
  rw [intervalIntegral.integral_const_mul, integral_exp_mode]
  split_ifs <;> simp

/-- The data are scheduled over the slot `p` of level `i`. -/
def GoodData (D : OCData) (j₀ i : ℕ) (p : ℤ) (dd : ChainData) (n : ℕ) : Prop :=
  ChainOK D j₀ dd n ∧ dd.slots.getLastD 0 = p ∧ dd.baseLevel + n + 1 = i

open scoped Classical in
/-- **The complex extension of the Jacobian leaf** `F_t(0)_{ac} − δ_{ac}` over the slot `p` of
level `i`. -/
def jacLeafExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (a c : Fin 2) :
    ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ :=
  fun dd n t x =>
    if GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 then
      (chainFam D dd n).jacC x t a c - (if a = c then 1 else 0)
    else 0

/-- The window of good data. -/
theorem GoodData.mem_slotWin (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    t ∈ slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0) := by
  rw [hg.2.1, hg.2.2]; exact ocPulseWindow_subset_slotWin hΛ i p ht

/-- The leaf does not depend on the final phase. -/
theorem jacLeafExt_shift (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} (a c : Fin 2) {dd : ChainData} {n : ℕ}
    (t : ℝ)
    (x : ChainParamsC n) (v : CVec) (hv : ∀ a', (v a').im = 0) :
    jacLeafExt D b j₀ i p a c dd n t (x.1, x.2.1, x.2.2 + v) = jacLeafExt D b j₀ i p a c dd n t x := by
  classical
  have hmem : ((x.1, x.2.1, x.2.2 + v) : ChainParamsC n) ∈ carrierC D b dd n 2 ↔
      x ∈ carrierC D b dd n 2 := by
    unfold carrierC
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Complex.add_im, hv, add_zero]
  have hjac : (chainFam D dd n).jacC (x.1, x.2.1, x.2.2 + v) t = (chainFam D dd n).jacC x t := by
    have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
    have e : (chainFam D dd n).toGeom (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).toGeom x := by
      rw [chainFam_toGeom D hε, chainFam_toGeom D hε]
      rfl
    unfold CFam.jacC
    have e1 : (chainFam D dd n).fl (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).fl x :=
      congrArg Prod.fst e
    have e2 : (chainFam D dd n).ctr (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).ctr x :=
      congrArg (fun g : CGeom => g.2.1) e
    rw [e1, e2]
  unfold jacLeafExt
  rw [hmem, hjac]

/-- **The size of the Jacobian leaf**, uniformly in the output time. -/
theorem norm_jacLeafExt_le (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ) (a c : Fin 2)
    (dd : ChainData) (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (x : ChainParamsC n) :
    ‖jacLeafExt D b j₀ i p a c dd n t x‖ ≤
      chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i) := by
  classical
  have hΛ1 := env.hΛ1
  by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
  · have hO := env.chainFam_over hgx.1.1
    have htW := hgx.1.mem_slotWin hΛ1 ht
    have hb := CFam.norm_jacC_sub_le hO.ok hgx.2 htW a c
    simp only [jacLeafExt, hgx, and_self, ite_true]
    refine hb.trans ?_
    have hi : dd.baseLevel + n = i - 1 := by have := hgx.1.2.2; omega
    have hanc : (chainFam D dd n).anc = D.slotAnchor (dd.baseLevel + n + 1)
        (dd.slots.getLastD 0) := hO.anc
    have hst : |t - (chainFam D dd n).anc| ≤ 6 / 5 * ocTauPP D.α D.q D.Λ i := by
      rw [hanc]
      have := abs_sub_le_of_mem_slotWin D htW
        (anchor_mem_slotWin D hΛ1 (dd.baseLevel + n + 1) (dd.slots.getLastD 0))
      calc _ ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (dd.baseLevel + n + 1) := this
        _ = 6 / 5 * ocTauPP D.α D.q D.Λ i := by rw [hgx.1.2.2]
    rw [hi]
    exact mul_le_mul_of_nonneg_left hst (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
  · simp only [jacLeafExt, hgx, ite_false, norm_zero]
    exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos hΛ1).le)

/-- The Jacobian leaf is invariant under the child-phase translations. -/
theorem jacLeafExt_shiftChild (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} (a c : Fin 2) {dd : ChainData}
    {n : ℕ} (t : ℝ) (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) :
    jacLeafExt D b j₀ i p a c dd n t (x.shiftChild k v) = jacLeafExt D b j₀ i p a c dd n t x := by
  classical
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold jacLeafExt
  rw [mem_carrierC_shiftChild_iff, jacC_chainFam_shiftChild D hε dd x k hv]

/-- **The Jacobian leaf has a holomorphic, time-measurable extension.** -/
theorem jacLeaf_isHolExtension (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ) (a c : Fin 2) :
    IsHolExtension D b j₀ i p (fun t ch _ => ch.famJac D t a c - (if a = c then 1 else 0))
      (jacLeafExt D b j₀ i p a c) := by
  classical
  have hΛ1 := env.hΛ1
  refine ⟨fun dd n t ht => ?_, ⟨fun dd n x => ?_, fun dd n t ht x _ =>
    ⟨fun v _ => jacLeafExt_shift hΛ1 a c t x (fun a' => (v a' : ℂ)) (fun a' => by simp),
      fun k v hv => jacLeafExt_shiftChild hΛ1 a c t x k hv⟩, fun dd n x hx =>
    ⟨_, (isOpen_carrierC D b dd n 2).mem_nhds hx, _, fun t ht y _ =>
      norm_jacLeafExt_le env i p a c dd n ht y⟩⟩, fun ch t ht ζ hch => ?_⟩
  · -- holomorphy
    by_cases hg : GoodData D j₀ i p dd n
    · have hO := env.chainFam_over hg.1
      have hd := (CFam.differentiableOn_jacC hO.ok (hg.mem_slotWin hΛ1 ht) a c).sub
        (differentiableOn_const (if a = c then (1 : ℂ) else 0))
      refine hd.congr fun x hx => ?_
      simp [jacLeafExt, hg, hx]
    · have : jacLeafExt D b j₀ i p a c dd n t = fun _ => 0 := by
        funext x; simp [jacLeafExt, hg]
      rw [this]; exact differentiableOn_const 0
  · -- measurability in time
    by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
    · have hO := env.chainFam_over hgx.1.1
      have hS : ocPulseWindow D.α D.q D.Λ i p ⊆
          slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0) := fun t ht =>
        hgx.1.mem_slotWin hΛ1 ht
      have hm := (CFam.measurable_jacC hO.ok hO.cont hgx.2 hS a c).sub_const
        (if a = c then (1 : ℂ) else 0)
      have e : (fun t : ocPulseWindow D.α D.q D.Λ i p => jacLeafExt D b j₀ i p a c dd n t x) =
          fun t : ocPulseWindow D.α D.q D.Λ i p =>
            (chainFam D dd n).jacC x t a c - (if a = c then (1 : ℂ) else 0) := by
        funext t; simp [jacLeafExt, hgx]
      rw [e]; exact hm
    · have : (fun t : ocPulseWindow D.α D.q D.Λ i p => jacLeafExt D b j₀ i p a c dd n t x) =
          fun _ => 0 := by
        funext t; simp [jacLeafExt, hgx]
      rw [this]; exact measurable_const
  · -- agreement at the real chains
    have hdd := chainOK_of_admissible hch
    have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
    have hx := GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
    simp only [jacLeafExt, hg, hx, and_self, ite_true]
    rw [jacC_chainFam_real env hch ζ (ocPulseWindow_subset_slotWin hΛ1 i p ht) a c]
    split_ifs <;> push_cast <;> ring

/-- **The mode bound of the Jacobian leaf**: only the zero mode, at most `K a_{i-1} (6/5) h_i`. -/
theorem jacLeaf_ctxModeSup_le (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ) (a c : Fin 2)
    (mres : ℝ) (h : ℤ) :
    ctxModeSup D b j₀ i p (jacLeafExt D b j₀ i p a c) mres h ≤
      if h = 0 then ENNReal.ofReal (chainK * ocA D.α D.q D.Λ (i - 1) *
        (6 / 5 * ocTauPP D.α D.q D.Λ i)) else 0 := by
  classical
  have hΛ1 := env.hΛ1
  refine iSup_le fun dd => iSup_le fun n => iSup_le fun _ => iSup_le fun t => iSup_le fun ht =>
    iSup_le fun x => iSup_le fun _ => iSup_le fun hre => ?_
  rw [finalPhaseCoeff_of_invariant _ (fun s => jacLeafExt_shift hΛ1 a c t x _ (fun a' => by
    split_ifs <;> simp))]
  split_ifs with h0
  · rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
    · have hO := env.chainFam_over hgx.1.1
      have htW := hgx.1.mem_slotWin hΛ1 ht
      have hb := CFam.norm_jacC_sub_le hO.ok hgx.2 htW a c
      simp only [jacLeafExt, hgx, and_self, ite_true]
      refine hb.trans ?_
      have hi : dd.baseLevel + n = i - 1 := by have := hgx.1.2.2; omega
      have hanc : (chainFam D dd n).anc = D.slotAnchor (dd.baseLevel + n + 1)
          (dd.slots.getLastD 0) := hO.anc
      have hst : |t - (chainFam D dd n).anc| ≤ 6 / 5 * ocTauPP D.α D.q D.Λ i := by
        rw [hanc]
        have := abs_sub_le_of_mem_slotWin D htW
          (anchor_mem_slotWin D hΛ1 (dd.baseLevel + n + 1) (dd.slots.getLastD 0))
        calc _ ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (dd.baseLevel + n + 1) := this
          _ = 6 / 5 * ocTauPP D.α D.q D.Λ i := by rw [hgx.1.2.2]
      rw [hi]
      exact mul_le_mul_of_nonneg_left hst (mul_nonneg (by rw [chainK_eq]; norm_num)
        (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
    · simp only [jacLeafExt, hgx, ite_false, norm_zero]
      exact mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
        (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
        (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos hΛ1).le)
  · simp

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Metric
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The velocity of the base family.** The base family is the complex flow of the
analytic velocity `v`. By its integral equation `𝔛(u, y, t) = y + ∫_t^u v(σ, 𝔛(σ, y, t)) dσ` and
the uniform continuity of `(σ, y) ↦ v(σ, 𝔛(σ, y, t))` on the compact set `[a, b] × B̄(c(t), ϱ)`,
its velocity is `v` itself (`baseFam_velOK`). -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

/-- **The velocity of the base family is the analytic velocity.** -/
theorem baseFam_velOK (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {W : Set ℝ}
    (hW : W ⊆ Icc a b) {ctr : Par → CVec} {Ω : Set Par} {s ϱ : ℝ}
    (hU : ∀ P ∈ Ω, ∀ r ∈ W, ball ((baseFam v ℓ' ctr s : CFam Par).cur P r) ϱ ⊆ Z0 ℓ' Γ a b) :
    (baseFam v ℓ' ctr s : CFam Par).VelOK Ω W ϱ (fun _ t y => v t y) where
  hol t ht := by
    have hs : ∀ q ∈ (baseFam v ℓ' ctr s : CFam Par).dom Ω ϱ t, q.2 ∈ strip ℓ := by
      intro q hq
      have hZ := hU q.1 hq.1 t ht hq.2
      have h1 := cflow_mem hv.toStripField hw hZ (hW ht) (hW ht)
      rw [cflow_start hv.toStripField hw hZ (hW ht)] at h1
      exact cstrip_subset_strip hw.hℓℓ h1
    exact (hv.holo t).comp differentiableOn_snd hs
  lim P hP t ht ε hε := by
    have htI := hW ht
    set c := (baseFam v ℓ' ctr s : CFam Par).cur P t with hc
    rcases le_or_gt ϱ 0 with hϱ | hϱ
    · refine Eventually.of_forall fun u y hy => ?_
      rw [ball_eq_empty.mpr hϱ] at hy
      exact absurd hy (notMem_empty y)
    have hK : closedBall c ϱ ⊆ Z0 ℓ' Γ a b := by
      rw [← closure_ball c hϱ.ne']
      exact (isClosed_cstrip _).closure_subset_iff.mpr (hU P hP t ht)
    set S : Set (ℝ × CVec) := Icc a b ×ˢ closedBall c ϱ with hS
    have hSc : IsCompact S := isCompact_Icc.prod (isCompact_closedBall c ϱ)
    have hg : Continuous fun q : ℝ × CVec => ((q.1, q.2, t) : ℝ × CVec × ℝ) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    have hmaps : MapsTo (fun q : ℝ × CVec => ((q.1, q.2, t) : ℝ × CVec × ℝ)) S
        (flowDom ℓ' Γ a b) := fun q hq => ⟨hq.1, hK hq.2, htI⟩
    have hcfl : ContinuousOn (fun q : ℝ × CVec => cflow v ℓ' q.1 q.2 t) S := by
      have h := (continuousOn_cflow hv.toStripField hw).comp hg.continuousOn hmaps
      exact h
    have hf : ContinuousOn (fun q : ℝ × CVec => v q.1 (cflow v ℓ' q.1 q.2 t)) S :=
      hv.cont.comp (continuousOn_fst.prodMk hcfl) fun q hq =>
        ⟨mem_univ _, cstrip_subset_strip hw.hℓℓ (cflow_mem hv.toStripField hw (hK hq.2) htI hq.1)⟩
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp
      (hSc.uniformContinuousOn_of_continuous hf) ε hε
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)] with
      u huW hut y hy
    have huI := hW huW
    have hyZ : y ∈ Z0 ℓ' Γ a b := hU P hP t ht hy
    have hyK : y ∈ closedBall c ϱ := ball_subset_closedBall hy
    show ‖cflow v ℓ' u y t - y - (u - t) • v t y‖ ≤ ε * |u - t|
    have hsub : uIcc t u ⊆ Icc a b := uIcc_subset_Icc htI huI
    have hint : IntervalIntegrable (fun σ => v σ (cflow v ℓ' σ y t)) MeasureTheory.volume t u := by
      refine ContinuousOn.intervalIntegrable ?_
      exact hf.comp (continuousOn_id.prodMk continuousOn_const) fun σ hσ => ⟨hsub hσ, hyK⟩
    rw [cflow_eq hv.toStripField hw hyZ htI huI, add_sub_cancel_left,
      ← intervalIntegral.integral_const, ← intervalIntegral.integral_sub hint
        intervalIntegrable_const]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    have hσI : σ ∈ Icc a b := uIoc_subset_window huI htI hσ
    have hσt : |σ - t| ≤ |u - t| := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hσ)
    have hd : dist ((σ, y) : ℝ × CVec) (t, y) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
      exact lt_of_le_of_lt hσt (by rw [mem_ball, Real.dist_eq] at hut; exact hut)
    have h1 := hδf (σ, y) ⟨hσI, hyK⟩ (t, y) ⟨htI, hyK⟩ hd
    rw [dist_eq_norm] at h1
    simp only at h1
    rw [cflow_start hv.toStripField hw hyZ htI] at h1
    exact h1.le

end CFam

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **The inverse and the metric letters**. For a family with
the invariants, `‖F_t(0) − I‖ ≤ m` in operator norm (sup norm on `ℂ²`), so every row of
`F − I` has `ℓ¹` norm at most `m` (`sum_norm_row_le`). For `m < 1` this gives
`|det F| ≥ (1−m)²` (`norm_det_ge`), the entries of `F⁻¹` are at most `(1+m)/(1−m)²`
and those of `F⁻¹ − I` at most `m(1+m)/(1−m)²` (`norm_inv_sub_one_le`). The complex inverse
`F⁻¹` and the complex metric `F⁻¹F⁻ᵀ` are holomorphic in the parameters where `det F ≠ 0`.
At real parameters they
are the real inverse and metric (`inv_map_ofReal`). -/

/-! ### Rows, determinant and inverse of a perturbed identity -/

/-- **Each row of the matrix of an operator has `ℓ¹` norm at most the operator norm.** -/
theorem sum_norm_row_le (E : CVec →L[ℂ] CVec) (a : Fin 2) :
    ∑ c : Fin 2, ‖E (cbasis c) a‖ ≤ ‖E‖ := by
  set z : Fin 2 → ℂ := fun c => E (cbasis c) a with hz
  set v : CVec := fun c => if z c = 0 then 0 else starRingEnd ℂ (z c) / (‖z c‖ : ℂ) with hv_def
  have hvc : ∀ c, v c * z c = (‖z c‖ : ℂ) := by
    intro c
    by_cases h : z c = 0
    · simp [hv_def, h]
    · have hn : (‖z c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      simp only [hv_def, h, ite_false]
      rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
      ring
  have hv : ‖v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => ?_
    by_cases h : z c = 0
    · simp [hv_def, h]
    · simp only [hv_def, h, ite_false, norm_div, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_norm]
      rw [div_self (norm_ne_zero_iff.mpr h)]
  have hsum : v = ∑ c : Fin 2, v c • cbasis c := by
    funext b
    simp [cbasis, Finset.sum_apply, Pi.single_apply]
  have hEv : E v a = ∑ c : Fin 2, (‖z c‖ : ℂ) := by
    conv_lhs => rw [hsum]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← hvc c]
  have h1 : ‖E v a‖ ≤ ‖E‖ :=
    (norm_le_pi_norm _ a).trans ((E.le_opNorm v).trans (by
      simpa using mul_le_mul_of_nonneg_left hv (norm_nonneg E)))
  have h2 : ‖E v a‖ = ∑ c : Fin 2, ‖z c‖ := by
    rw [hEv, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun c _ => norm_nonneg _)]
  rw [← h2]; exact h1

/-- Two-row bound in the entries. -/
structure RowSmall (E : Matrix (Fin 2) (Fin 2) ℂ) (m : ℝ) : Prop where
  row0 : ‖E 0 0‖ + ‖E 0 1‖ ≤ m
  row1 : ‖E 1 0‖ + ‖E 1 1‖ ≤ m

/-- **The determinant of a perturbed identity.** -/
theorem norm_det_ge {E : Matrix (Fin 2) (Fin 2) ℂ} {m : ℝ} (hE : RowSmall E m) (hm : m ≤ 1) :
    (1 - m) ^ 2 ≤ ‖(1 + E).det‖ := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
  set x := ‖E 0 0‖; set y := ‖E 0 1‖; set u := ‖E 1 0‖; set z := ‖E 1 1‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hu : 0 ≤ u := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have h0 := hE.row0
  have h1 := hE.row1
  have ha : 1 - x ≤ ‖1 + E 0 0‖ := by
    have := norm_add_le (1 + E 0 0) (-E 0 0)
    simp only [add_neg_cancel_right, norm_one, norm_neg] at this
    linarith
  have hd : 1 - z ≤ ‖1 + E 1 1‖ := by
    have := norm_add_le (1 + E 1 1) (-E 1 1)
    simp only [add_neg_cancel_right, norm_one, norm_neg] at this
    linarith
  have hprod : (1 - x) * (1 - z) ≤ ‖(1 + E 0 0) * (1 + E 1 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul ha hd (by linarith) (norm_nonneg _)
  have hoff : ‖E 0 1 * E 1 0‖ ≤ (m - x) * (m - z) := by
    rw [norm_mul]
    exact mul_le_mul (by linarith) (by linarith) hu (by linarith)
  have htri := norm_sub_norm_le ((1 + E 0 0) * (1 + E 1 1)) (E 0 1 * E 1 0)
  have key : (1 - m) ^ 2 ≤ (1 - x) * (1 - z) - (m - x) * (m - z) := by nlinarith
  linarith

/-- The inverse of a `2 × 2` matrix over a field, entrywise. -/
theorem inv_apply_fin_two {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (a c : Fin 2) :
    A⁻¹ a c = (A.det)⁻¹ * A.adjugate a c := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']

theorem adjugate_one_add (E : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + E).adjugate 0 0 = 1 + E 1 1 ∧ (1 + E).adjugate 0 1 = -E 0 1 ∧
      (1 + E).adjugate 1 0 = -E 1 0 ∧ (1 + E).adjugate 1 1 = 1 + E 0 0 := by
  rw [Matrix.adjugate_fin_two]
  simp

theorem det_one_add (E : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + E).det = (1 + E 0 0) * (1 + E 1 1) - E 0 1 * E 1 0 := by
  rw [Matrix.det_fin_two]
  simp

theorem norm_div_le_of {num den : ℂ} {N m : ℝ} (hden : (1 - m) ^ 2 ≤ ‖den‖)
    (hpos : 0 < (1 - m) ^ 2) (hnum : ‖num‖ ≤ N) : ‖num / den‖ ≤ N / (1 - m) ^ 2 := by
  rw [norm_div]
  exact div_le_div₀ ((norm_nonneg _).trans hnum) hnum hpos hden

/-- **The inverse of a perturbed identity is close to the identity.** -/
theorem norm_inv_sub_one_le {E : Matrix (Fin 2) (Fin 2) ℂ} {m : ℝ} (hE : RowSmall E m)
    (hm : m < 1) (a c : Fin 2) :
    ‖(1 + E)⁻¹ a c - (if a = c then 1 else 0)‖ ≤ m * (1 + m) / (1 - m) ^ 2 := by
  have hdet := norm_det_ge hE hm.le
  have hpos : 0 < (1 - m) ^ 2 := by have : 0 < 1 - m := by linarith
                                    positivity
  have hd0 : (1 + E).det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; linarith
  have hx := norm_nonneg (E 0 0)
  have hy := norm_nonneg (E 0 1)
  have hu := norm_nonneg (E 1 0)
  have hz := norm_nonneg (E 1 1)
  have h0 := hE.row0
  have h1 := hE.row1
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨a00, a01, a10, a11⟩ := adjugate_one_add E
  have hdet' := det_one_add E
  have hmm : m ≤ m * (1 + m) := by nlinarith
  rw [inv_apply_fin_two]
  fin_cases a <;> fin_cases c
  · -- (0,0)
    have e : ((1 + E).det)⁻¹ * (1 + E).adjugate 0 0 - (if (0 : Fin 2) = 0 then 1 else 0) =
        (-(E 0 0 * (1 + E 1 1)) + E 0 1 * E 1 0) / (1 + E).det := by
      simp only [a00, ↓reduceIte]; field_simp; rw [hdet']; ring
    simp only [Fin.zero_eta, Fin.isValue] at e ⊢
    rw [e]
    refine norm_div_le_of hdet hpos ?_
    have hb1 : ‖1 + E 1 1‖ ≤ 1 + m := (norm_add_le _ _).trans (by simp; linarith)
    calc ‖-(E 0 0 * (1 + E 1 1)) + E 0 1 * E 1 0‖
        ≤ ‖E 0 0‖ * ‖1 + E 1 1‖ + ‖E 0 1‖ * ‖E 1 0‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg, norm_mul, norm_mul]
      _ ≤ ‖E 0 0‖ * (1 + m) + ‖E 0 1‖ * (1 + m) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hb1 hx) (mul_le_mul_of_nonneg_left ?_ hy)
          linarith
      _ ≤ m * (1 + m) := by nlinarith
  · -- (0,1)
    have e : ((1 + E).det)⁻¹ * (1 + E).adjugate 0 1 - (if (0 : Fin 2) = 1 then 1 else 0) =
        (-E 0 1) / (1 + E).det := by
      simp only [a01, Fin.isValue, zero_ne_one, ↓reduceIte]; field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e ⊢
    rw [e]
    refine norm_div_le_of hdet hpos ?_
    rw [norm_neg]; linarith
  · -- (1,0)
    have e : ((1 + E).det)⁻¹ * (1 + E).adjugate 1 0 - (if (1 : Fin 2) = 0 then 1 else 0) =
        (-E 1 0) / (1 + E).det := by
      simp only [a10, Fin.isValue, one_ne_zero, ↓reduceIte]; field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e ⊢
    rw [e]
    refine norm_div_le_of hdet hpos ?_
    rw [norm_neg]; linarith
  · -- (1,1)
    have e : ((1 + E).det)⁻¹ * (1 + E).adjugate 1 1 - (if (1 : Fin 2) = 1 then 1 else 0) =
        (-(E 1 1 * (1 + E 0 0)) + E 0 1 * E 1 0) / (1 + E).det := by
      simp only [a11, ↓reduceIte]; field_simp; rw [hdet']; ring
    simp only [Fin.isValue, Fin.mk_one] at e ⊢
    rw [e]
    refine norm_div_le_of hdet hpos ?_
    have hb0 : ‖1 + E 0 0‖ ≤ 1 + m := (norm_add_le _ _).trans (by simp; linarith)
    calc ‖-(E 1 1 * (1 + E 0 0)) + E 0 1 * E 1 0‖
        ≤ ‖E 1 1‖ * ‖1 + E 0 0‖ + ‖E 0 1‖ * ‖E 1 0‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg, norm_mul, norm_mul]
      _ ≤ ‖E 1 1‖ * (1 + m) + m * ‖E 1 0‖ := by
          refine add_le_add (mul_le_mul_of_nonneg_left hb0 hz) (mul_le_mul_of_nonneg_right ?_ hu)
          linarith
      _ ≤ m * (1 + m) := by nlinarith

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The velocity of a child.** For a family `(𝔛, x, s)` with velocity `V` and its child
of level `k` with anchor `s'`, center `c` and phase `ζ`, the two-time child flow from the time `t`
is `𝔛'(u, y, t) = 𝔛(u, Θ_u(y), t)` with `Θ_u(y) = 𝔛(t, w + I(u,t) 𝐮(w - (x + c) + ε_kζ), s)`,
`w = 𝔛(s, y, t)` (parent group law). Since `Θ_t = id`, `I(u, t) = p(t)(u - t) + o(u - t)` and
`D𝔛(t, ·, s)` is Lipschitz on the half balls (Cauchy), the child has the velocity
`V'(t, y) = V(t, y) + p_{k,p}(t) D𝔛(t, w, s)[𝐮(w - (x + c) + ε_kζ)]` (`ChildHyp.velOK`).
Ingredients: the second-order expansion of the flow (`OK.norm_fl_sub_sub_fderiv_le`) and the
Lipschitz bound `|V(t, y) - V(t, y')| ≤ Λ|y - y'|` of a velocity (`VelOK.norm_vel_sub_le`). -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

section General

variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ} {Vel : Par → ℝ → CVec → CVec}

/-- **The second-order expansion of the flow** on the half balls. -/
theorem OK.norm_fl_sub_sub_fderiv_le (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ}
    (hu : u ∈ W) (hr : r ∈ W) {a b : CVec} (ha : a ∈ ball (F.cur P r) (ϱ / 2))
    (hb : b ∈ ball (F.cur P r) (ϱ / 2)) :
    ‖F.fl P u a r - F.fl P u b r - fderiv ℂ (fun z => F.fl P u z r) b (a - b)‖ ≤
      4 * (Λ * T) / ϱ * ‖a - b‖ ^ 2 := by
  set L := fderiv ℂ (fun z => F.fl P u z r) b with hL
  set g : CVec → CVec := fun z => F.fl P u z r - L z with hg
  have hseg : segment ℝ b a ⊆ ball (F.cur P r) (ϱ / 2) := (convex_ball _ _).segment_subset hb ha
  have hball : ball (F.cur P r) (ϱ / 2) ⊆ ball (F.cur P r) ϱ :=
    ball_subset_ball (by linarith [h.hϱ])
  have hgd : ∀ z ∈ segment ℝ b a,
      HasFDerivAt g (fderiv ℂ (fun z => F.fl P u z r) z - L) z := fun z hz =>
    (h.differentiableAt_fl hP hu hr (hball (hseg hz))).hasFDerivAt.sub L.hasFDerivAt
  have hbd : ∀ z ∈ segment ℝ b a, ‖fderiv ℂ g z‖ ≤ 4 * (Λ * T) / ϱ * ‖a - b‖ := by
    intro z hz
    rw [(hgd z hz).fderiv]
    refine (h.norm_fderiv_fl_sub_le hP hu hr (hseg hz) hb).trans ?_
    have hK0 : 0 ≤ 4 * (Λ * T) / ϱ := by
      have := h.hϱ; have := mul_nonneg h.hΛ h.hT0; positivity
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
  have hmv := (convex_segment b a).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hgd z hz).differentiableAt) hbd (left_mem_segment ℝ b a)
    (right_mem_segment ℝ b a)
  have e : g a - g b = F.fl P u a r - F.fl P u b r - L (a - b) := by
    simp only [hg, map_sub]
    abel
  rw [e] at hmv
  calc _ ≤ 4 * (Λ * T) / ϱ * ‖a - b‖ * ‖a - b‖ := hmv
    _ = _ := by ring

/-- **A velocity is `Λ`-Lipschitz** on the ball. -/
theorem VelOK.norm_vel_sub_le (h : F.OK Ω W ϱ Λ T) (hV : F.VelOK Ω W ϱ Vel) {P : Par} (hP : P ∈ Ω)
    {t : ℝ} (ht : t ∈ W) (hne : (𝓝[W \ {t}] t).NeBot) {y y' : CVec}
    (hy : y ∈ ball (F.cur P t) ϱ) (hy' : y' ∈ ball (F.cur P t) ϱ) :
    ‖Vel P t y - Vel P t y'‖ ≤ Λ * ‖y - y'‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev' : ∀ᶠ u in 𝓝[W \ {t}] t, (u ∈ W ∧ u ≠ t) ∧ ∀ z ∈ ball (F.cur P t) ϱ,
      ‖F.fl P u z t - z - (u - t) • Vel P t z‖ ≤ ε / 2 * |u - t| := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_mono t sdiff_subset (hV.lim P hP t ht (ε / 2) (by positivity))] with u hu h2
    exact ⟨⟨hu.1, hu.2⟩, h2⟩
  have := hne
  obtain ⟨u, ⟨huW, hut⟩, hexp⟩ := hev'.exists
  have hpos : 0 < |u - t| := abs_pos.mpr (sub_ne_zero.mpr hut)
  have h1 := hexp y hy
  have h2 := hexp y' hy'
  have h3 := h.norm_fl_sub_sub_le hP huW ht hy hy'
  have e : (u - t) • (Vel P t y - Vel P t y') =
      (F.fl P u y t - F.fl P u y' t - (y - y')) - (F.fl P u y t - y - (u - t) • Vel P t y) +
        (F.fl P u y' t - y' - (u - t) • Vel P t y') := by
    rw [smul_sub]
    abel
  have h4 : |u - t| * ‖Vel P t y - Vel P t y'‖ ≤ |u - t| * (Λ * ‖y - y'‖ + ε) := by
    rw [← Real.norm_eq_abs, ← norm_smul, e, Real.norm_eq_abs]
    calc _ ≤ ‖F.fl P u y t - F.fl P u y' t - (y - y')‖ +
          ‖F.fl P u y t - y - (u - t) • Vel P t y‖ +
          ‖F.fl P u y' t - y' - (u - t) • Vel P t y'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Λ * |u - t| * ‖y - y'‖ + ε / 2 * |u - t| + ε / 2 * |u - t| :=
          add_le_add (add_le_add h3 h1) h2
      _ = |u - t| * (Λ * ‖y - y'‖ + ε) := by ring
  exact le_of_mul_le_mul_left h4 hpos

end General

namespace ChildHyp

variable {D : OCData} {F : CFam Par} {Ω : Set Par} {W W' : Set ℝ} {ϱ Λ T : ℝ} {k : ℕ} {pk : ℤ}
  {s' : ℝ} {cc ph : Par → CVec} {ϱ' T' Bc Bph σ Ms Ms' : ℝ} {Vel : Par → ℝ → CVec → CVec}

/-- The shear argument `w - (x + c) + ε_kζ`, `w = 𝔛(s, y, t)`, of the child. -/
def shArg (D : OCData) (F : CFam Par) (k : ℕ) (cc ph : Par → CVec) (P : Par) (t : ℝ)
    (y : CVec) : CVec :=
  F.fl P F.anc y t - (F.ctr P + cc P) + epsC D k • ph P

/-- The Eulerian velocity `D𝔛(t, w, s)[𝐮(w - (x + c) + ε_kζ)]` of the relative shear. -/
def shearVel (D : OCData) (F : CFam Par) (k : ℕ) (pk : ℤ) (cc ph : Par → CVec) (P : Par)
    (t : ℝ) (y : CVec) : CVec :=
  fderiv ℂ (fun z => F.fl P t z F.anc) (F.fl P F.anc y t) (Sh D k pk (shArg D F k cc ph P t y))

/-- **The velocity of the child** `V'(t, y) = V(t, y) + p_{k,p}(t) D𝔛(t, w, s)[𝐮(…)]`. -/
def childVel (D : OCData) (F : CFam Par) (k : ℕ) (pk : ℤ) (cc ph : Par → CVec)
    (Vel : Par → ℝ → CVec → CVec) : Par → ℝ → CVec → CVec :=
  fun P t y => Vel P t y + ((ocPulse D.α D.q D.Λ D.ζ k pk t : ℝ) : ℂ) •
    shearVel D F k pk cc ph P t y

section

variable (h : ChildHyp D F Ω W W' ϱ Λ T k pk s' cc ph ϱ' T' Bc Bph σ Ms Ms')
include h

theorem norm_shearVel_le {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W') {y : CVec}
    (hy : y ∈ ball ((F.child D k pk s' cc ph).cur P t) ϱ') :
    ‖shearVel D F k pk cc ph P t y‖ ≤ (1 + Λ * T) * Ms := by
  have hs := h.hF.anc_mem
  have htW := h.mem_W ht
  have hw' : F.fl P F.anc y t ∈ ball (F.cur P F.anc) ϱ :=
    ball_subset_ball (by linarith [h.hF.hϱ]) (h.w_mem hP ht hy)
  have hJ := h.hF.jac P hP t htW F.anc hs _ hw'
  have hnorm : ‖fderiv ℂ (fun z => F.fl P t z F.anc) (F.fl P F.anc y t)‖ ≤ 1 + Λ * T := by
    calc ‖fderiv ℂ (fun z => F.fl P t z F.anc) (F.fl P F.anc y t)‖
        = ‖(fderiv ℂ (fun z => F.fl P t z F.anc) (F.fl P F.anc y t) -
            ContinuousLinearMap.id ℂ CVec) + ContinuousLinearMap.id ℂ CVec‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ Λ * T + 1 := add_le_add (hJ.trans (mul_le_mul_of_nonneg_left
          (h.hF.hT t htW F.anc hs) h.hF.hΛ)) ContinuousLinearMap.norm_id_le
      _ = 1 + Λ * T := by ring
  have hSa : ‖Sh D k pk (shArg D F k cc ph P t y)‖ ≤ Ms := h.hMs _ (h.im_arg_le hP ht hy)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hnorm hSa (norm_nonneg _) (by linarith [h.hL0]))

/-- **The velocity of the child.** -/
theorem velOK [FiniteDimensional ℂ Par] (hV : F.VelOK Ω W ϱ Vel)
    (hne : ∀ t ∈ W', (𝓝[W \ {t}] t).NeBot) :
    (F.child D k pk s' cc ph).VelOK Ω W' ϱ' (childVel D F k pk cc ph Vel) where
  hol t ht := by
    have htW := h.mem_W ht
    have hs := h.hF.anc_mem
    have h1 := (hV.hol t htW).mono (h.dom_child_subset ht)
    have hΦ : DifferentiableOn ℂ (fun q : Par × CVec => F.fl q.1 t q.2 F.anc)
        (F.dom Ω ϱ F.anc) := h.hF.hol t htW F.anc hs
    have hg : DifferentiableOn ℂ (fun q : Par × CVec =>
        Sh D k pk (q.2 - (F.ctr q.1 + cc q.1) + epsC D k • ph q.1)) (F.dom Ω ϱ F.anc) := by
      have hph' : DifferentiableOn ℂ (fun q : Par × CVec => ph q.1) (F.dom Ω ϱ F.anc) :=
        h.hph.comp differentiableOn_fst fun q hq => hq.1
      refine (differentiable_ocShearVelC _ _ _ _ _).comp_differentiableOn ?_
      exact (differentiableOn_snd.sub ((h.hF.ctr_hol.comp differentiableOn_fst fun q hq => hq.1).add
        (h.hcc.comp differentiableOn_fst fun q hq => hq.1))).add
        ((differentiableOn_const (epsC D k)).smul hph')
    have hD := differentiableOn_fderiv_snd_apply (h.hF.isOpen_dom hs) hΦ hg
    have hm : DifferentiableOn ℂ (fun q : Par × CVec => ((q.1, F.fl q.1 F.anc q.2 t) : Par × CVec))
        ((F.child D k pk s' cc ph).dom Ω ϱ' t) :=
      differentiableOn_fst.prodMk ((h.hF.hol F.anc hs t htW).mono (h.dom_child_subset ht))
    have hmaps : MapsTo (fun q : Par × CVec => ((q.1, F.fl q.1 F.anc q.2 t) : Par × CVec))
        ((F.child D k pk s' cc ph).dom Ω ϱ' t) (F.dom Ω ϱ F.anc) := fun q hq =>
      ⟨hq.1, ball_subset_ball (by linarith [h.hF.hϱ]) (h.w_mem hq.1 ht hq.2)⟩
    have h2 := hD.comp hm hmaps
    have h3 := h1.add (h2.const_smul ((ocPulse D.α D.q D.Λ D.ζ k pk t : ℝ) : ℂ))
    exact h3
  lim P hP t ht ε hε := by
    have hs := h.hF.anc_mem
    have htW := h.mem_W ht
    have hϱ := h.hF.hϱ
    have hL0 := h.hL0
    have hLT := h.hLT
    have hMs0 := h.hMs0
    have hΛ0 := h.hF.hΛ
    set K : ℝ := 4 * (Λ * T) / ϱ with hK
    have hK0 : 0 ≤ K := by have := mul_nonneg h.hF.hΛ h.hF.hT0; positivity
    set L : ℝ := 1 + Λ * T with hLdef
    have hL1 : 0 ≤ L * Ms := mul_nonneg (by linarith) hMs0
    set p : ℝ := ocPulse D.α D.q D.Λ D.ζ k pk t with hp
    set M₀ : ℝ := Λ * (L * Ms + K * Ms ^ 2) + K * Ms ^ 2 + 1 with hM₀
    have hKM : 0 ≤ K * Ms ^ 2 := mul_nonneg hK0 (sq_nonneg Ms)
    have hM₀0 : 0 < M₀ := by
      have := mul_nonneg hΛ0 (add_nonneg hL1 hKM)
      rw [hM₀]; linarith
    set δ : ℝ := min 1 (ε / 4 / M₀) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    set ε₂ : ℝ := ε / 4 / (L * Ms + 1) with hε₂
    have hε₂0 : 0 < ε₂ := by positivity
    have hε₂L : ε₂ * (L * Ms) ≤ ε / 4 := by
      calc ε₂ * (L * Ms) ≤ ε₂ * (L * Ms + 1) := mul_le_mul_of_nonneg_left (by linarith) hε₂0.le
        _ = ε / 4 := by rw [hε₂]; field_simp
    -- the time integral of the pulse
    have hpc := continuous_ocPulse D h.hζ k pk
    have hId : HasDerivAt (fun u => pInt D k pk u t) p t :=
      intervalIntegral.integral_hasDerivAt_right (hpc.intervalIntegrable _ _)
        (hpc.stronglyMeasurableAtFilter _ _) hpc.continuousAt
    have hIo := Asymptotics.isLittleO_iff.mp (hasDerivAt_iff_isLittleO.mp hId) hε₂0
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_mono t h.hW' (hV.lim P hP t htW (ε / 4) (by positivity)),
      nhdsWithin_le_nhds hIo, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ0)] with
      u huW' hpar hI hut y hy
    simp only [pInt_same, sub_zero, smul_eq_mul, Real.norm_eq_abs] at hI
    have huW := h.mem_W huW'
    show ‖(F.child D k pk s' cc ph).fl P u y t - y - (u - t) • childVel D F k pk cc ph Vel P t y‖ ≤
      ε * |u - t|
    set x := |u - t| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have hxδ : x < δ := by rw [mem_ball, Real.dist_eq] at hut; exact hut
    have hx1 : x ≤ 1 := hxδ.le.trans (min_le_left _ _)
    have hxM : x * M₀ ≤ ε / 4 := (le_div_iff₀ hM₀0).mp (hxδ.le.trans (min_le_right _ _))
    have hx2 : x ^ 2 ≤ x := by
      calc x ^ 2 = x * x := sq x
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx1 hx0
        _ = x := mul_one x
    -- the points
    set w := F.fl P F.anc y t with hw
    set a := shArg D F k cc ph P t y with ha
    set I : ℝ := pInt D k pk u t with hIdef
    set Ψ := w + (I : ℂ) • Sh D k pk a with hΨ
    set Θ := F.fl P t Ψ F.anc with hΘ
    set E := shearVel D F k pk cc ph P t y with hE
    have hwm : w ∈ ball (F.cur P F.anc) (ϱ / 4) := h.w_mem hP ht hy
    have hΨm : Ψ ∈ ball (F.cur P F.anc) (ϱ / 4) := h.Zu_mem hP huW' ht hy
    have hy4 : y ∈ ball (F.cur P t) (ϱ / 4) := h.mem_parent hP ht hy
    have hSa : ‖Sh D k pk a‖ ≤ Ms := h.hMs _ (h.im_arg_le hP ht hy)
    have hIx : |I| ≤ x := abs_pInt_le D h.hζ k pk u t
    have hΨw : ‖Ψ - w‖ ≤ x * Ms := by
      rw [hΨ, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hIx hSa (norm_nonneg _) hx0
    -- `y = 𝔛(t, w, s)` and the child flow passes through `Θ`
    have hyw : F.fl P t w F.anc = y := by
      rw [hw, h.hF.group P hP t htW F.anc hs t htW y hy4]
      exact h.hF.init P hP t htW y (ball_subset_ball (by linarith) hy4)
    have hchild : (F.child D k pk s' cc ph).fl P u y t = F.fl P u Θ t := by
      show F.fl P u Ψ F.anc = F.fl P u (F.fl P t Ψ F.anc) t
      rw [h.hF.group P hP u huW t htW F.anc hs Ψ hΨm]
    have hΘm : Θ ∈ ball (F.cur P t) ϱ := by
      have h1 := h.hF.fl_mem_ball hP htW hs (ρ := ϱ / 4) (by linarith) hΨm
      refine ball_subset_ball ?_ h1
      have := mul_le_mul_of_nonneg_right hLT (by linarith : (0 : ℝ) ≤ ϱ / 4)
      linarith
    -- the second-order expansion
    have h2nd : ‖Θ - y - (I : ℂ) • E‖ ≤ K * (x * Ms) ^ 2 := by
      have h1 := h.hF.norm_fl_sub_sub_fderiv_le hP htW hs (ball_subset_ball (by linarith) hΨm)
        (ball_subset_ball (by linarith) hwm)
      have e1 : fderiv ℂ (fun z => F.fl P t z F.anc) w (Ψ - w) = (I : ℂ) • E := by
        rw [hΨ, add_sub_cancel_left, map_smul]
        rfl
      rw [hyw, e1] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΨw 2) hK0)
    have hEn : ‖E‖ ≤ L * Ms := h.norm_shearVel_le hP ht hy
    have hΘy : ‖Θ - y‖ ≤ x * (L * Ms) + K * (x * Ms) ^ 2 := by
      have hE' : ‖(I : ℂ) • E‖ ≤ x * (L * Ms) := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hIx hEn (norm_nonneg _) hx0
      calc ‖Θ - y‖ = ‖(Θ - y - (I : ℂ) • E) + (I : ℂ) • E‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ K * (x * Ms) ^ 2 + x * (L * Ms) := add_le_add h2nd hE'
        _ = _ := by ring
    have hVel : ‖Vel P t Θ - Vel P t y‖ ≤ Λ * (x * (L * Ms) + K * (x * Ms) ^ 2) :=
      (hV.norm_vel_sub_le h.hF hP htW (hne t ht) hΘm (ball_subset_ball (by linarith) hy4)).trans
        (mul_le_mul_of_nonneg_left hΘy hΛ0)
    have hIp : ‖((I : ℂ) - (((u - t) * p : ℝ) : ℂ)) • E‖ ≤ ε₂ * x * (L * Ms) := by
      rw [← Complex.ofReal_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hI hEn (norm_nonneg _) (by positivity)
    -- the decomposition
    rw [hchild]
    have e : F.fl P u Θ t - y - (u - t) • childVel D F k pk cc ph Vel P t y =
        (F.fl P u Θ t - Θ - (u - t) • Vel P t Θ) + (u - t) • (Vel P t Θ - Vel P t y) +
          (Θ - y - (I : ℂ) • E) + ((I : ℂ) - (((u - t) * p : ℝ) : ℂ)) • E := by
      rw [show childVel D F k pk cc ph Vel P t y = Vel P t y + ((p : ℝ) : ℂ) • E from rfl]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      push_cast
      module
    rw [e]
    have hb1 := hpar Θ hΘm
    have hb2 : ‖(u - t) • (Vel P t Θ - Vel P t y)‖ ≤ x * (Λ * (x * (L * Ms) + K * (x * Ms) ^ 2)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hVel hx0
    -- the small factors
    have hA : Λ * (x * (L * Ms) + K * (x * Ms) ^ 2) ≤ ε / 4 := by
      have e2 : (x * Ms) ^ 2 = x ^ 2 * Ms ^ 2 := mul_pow x Ms 2
      calc Λ * (x * (L * Ms) + K * (x * Ms) ^ 2) ≤ Λ * (x * (L * Ms) + K * (x * Ms ^ 2)) := by
            rw [e2]
            refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hΛ0
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx2 (sq_nonneg Ms)) hK0
        _ = x * (Λ * (L * Ms + K * Ms ^ 2)) := by ring
        _ ≤ x * M₀ := by
            refine mul_le_mul_of_nonneg_left ?_ hx0
            rw [hM₀]; linarith
        _ ≤ ε / 4 := hxM
    have hB : K * (x * Ms) ^ 2 ≤ x * (ε / 4) := by
      have e2 : K * (x * Ms) ^ 2 = x * (x * (K * Ms ^ 2)) := by ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ hx0
      calc x * (K * Ms ^ 2) ≤ x * M₀ := by
            refine mul_le_mul_of_nonneg_left ?_ hx0
            have := mul_nonneg hΛ0 (add_nonneg hL1 hKM)
            rw [hM₀]; linarith
        _ ≤ ε / 4 := hxM
    have hC : ε₂ * x * (L * Ms) ≤ x * (ε / 4) := by
      have e2 : ε₂ * x * (L * Ms) = x * (ε₂ * (L * Ms)) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left hε₂L hx0
    have hA' : x * (Λ * (x * (L * Ms) + K * (x * Ms) ^ 2)) ≤ x * (ε / 4) :=
      mul_le_mul_of_nonneg_left hA hx0
    calc _ ≤ ‖F.fl P u Θ t - Θ - (u - t) • Vel P t Θ‖ + ‖(u - t) • (Vel P t Θ - Vel P t y)‖ +
          ‖Θ - y - (I : ℂ) • E‖ + ‖((I : ℂ) - (((u - t) * p : ℝ) : ℂ)) • E‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ ε / 4 * x + x * (Λ * (x * (L * Ms) + K * (x * Ms) ^ 2)) + K * (x * Ms) ^ 2 +
          ε₂ * x * (L * Ms) := add_le_add (add_le_add (add_le_add hb1 hb2) h2nd) hIp
      _ ≤ ε * x := by linarith

end

end ChildHyp

end CFam

end AVRegularity.Providers.ComplexFlow
end
