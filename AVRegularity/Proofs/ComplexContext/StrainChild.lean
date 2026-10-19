-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.MetricExtInst
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexChain.VelChain
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.RingTheory.PicardGroup

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the own-frame strain letter** `a_{i-1}⁻¹ (∂_uF_u F_u⁻¹)(t)` (`geo own (strain a c)`).
Over the slot `𝗉` of level `i`, the extension on scheduled data and the outer
carrier is `a_{i-1}⁻¹` times the strain entry of the last family `chainFam` (`ownStrainExt`). The
last family has a velocity (`chainFam_velOK`), so the strain entry is the entry of `DV(t, c(t))`:
holomorphic, bounded by the rate `K a_{i-1}` of the family, and equal to the real strain at the
admissible chains. Time measurability is that of a derivative (`measurable_deriv`). The family
does not depend on the final phase, so the only mode is `h = 0`, at most `K`
(`CtxInv.strainOwn`). -/

open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- The last family of scheduled data has a velocity. -/
theorem chainVel (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n) :
    ∃ Vel, (chainFam D dd n).VelOK (carrierC D b dd n 2)
      (slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0)) (8 * b * D.eps (dd.baseLevel + n))
      Vel :=
  chainFam_velOK env.hq env.hΛ env.hα env.hζ env.hvel env.hb0 env.hb1 env.hCH env.hΥ env.hcs hdd

/-- The window of good data is a neighborhood of the output times. -/
theorem goodData_slotWin_mem_nhds (hΛ : 1 ≤ D.Λ) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0) ∈ 𝓝 t := by
  rw [hg.2.1, hg.2.2]
  exact slotWin_mem_nhds_of_window hΛ ht

theorem ocA_pos (hΛ : 1 ≤ D.Λ) (k : ℕ) : 0 < ocA D.α D.q D.Λ k :=
  Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ) _

open scoped Classical in
/-- **The extension of the own-frame strain letter.** -/
def ownStrainExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (a c : Fin 2) : Ext :=
  fun dd n t x => if GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 then
    (((ocA D.α D.q D.Λ (i - 1))⁻¹ : ℝ) : ℂ) * strainEnt (chainFam D dd n) x t a c else 0

theorem ownStrainExt_of {a c : Fin 2} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : GoodData D j₀ i p dd n) (hx : x ∈ carrierC D b dd n 2) :
    ownStrainExt D b j₀ i p a c dd n t x =
      (((ocA D.α D.q D.Λ (i - 1))⁻¹ : ℝ) : ℂ) * strainEnt (chainFam D dd n) x t a c := by
  unfold ownStrainExt
  split_ifs with h
  · rfl
  · exact (h ⟨hg, hx⟩).elim

theorem ownStrainExt_of_not {a c : Fin 2} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (h : ¬(GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2)) :
    ownStrainExt D b j₀ i p a c dd n t x = 0 := by
  unfold ownStrainExt
  split_ifs with h'
  · exact (h h').elim
  · rfl

/-- **The size of the own-frame strain letter.** -/
theorem norm_ownStrainExt_le (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData) (n : ℕ)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (x : ChainParamsC n) :
    ‖ownStrainExt D b j₀ i p a c dd n t x‖ ≤ chainK := by
  have hΛ1 := env.hΛ1
  by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
  · obtain ⟨hg, hx⟩ := hgx
    have hO := env.chainFam_over hg.1
    obtain ⟨Vel, hV⟩ := chainVel env hg.1
    have hW := goodData_slotWin_mem_nhds hΛ1 hg ht
    have hb := norm_strainEnt_le hO.ok hV hx (mem_of_mem_nhds hW) hW a c
    have hi : dd.baseLevel + n = i - 1 := by have := hg.2.2; omega
    rw [hi] at hb
    have hA := ocA_pos hΛ1 (i - 1)
    rw [ownStrainExt_of hg hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hA]
    calc (ocA D.α D.q D.Λ (i - 1))⁻¹ * ‖strainEnt (chainFam D dd n) x t a c‖
        ≤ (ocA D.α D.q D.Λ (i - 1))⁻¹ * (chainK * ocA D.α D.q D.Λ (i - 1)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA.le)
      _ = chainK := by field_simp
  · rw [ownStrainExt_of_not hgx, norm_zero, chainK_eq]
    norm_num

theorem ownStrainExt_hol (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData) (n : ℕ)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    DifferentiableOn ℂ (ownStrainExt D b j₀ i p a c dd n t) (carrierC D b dd n 2) := by
  by_cases hg : GoodData D j₀ i p dd n
  · have hO := env.chainFam_over hg.1
    obtain ⟨Vel, hV⟩ := chainVel env hg.1
    have hW := goodData_slotWin_mem_nhds env.hΛ1 hg ht
    have hd := (differentiableOn_strainEnt hO.ok hV (mem_of_mem_nhds hW) hW a c).const_mul
      ((((ocA D.α D.q D.Λ (i - 1))⁻¹ : ℝ) : ℂ))
    exact hd.congr fun x hx => ownStrainExt_of hg hx
  · have : ownStrainExt D b j₀ i p a c dd n t = fun _ => 0 :=
      funext fun x => ownStrainExt_of_not fun h => hg h.1
    rw [this]
    exact differentiableOn_const 0

theorem ownStrainExt_meas (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData) (n : ℕ)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) :
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => ownStrainExt D b j₀ i p a c dd n t x := by
  by_cases hg : GoodData D j₀ i p dd n
  · have hO := env.chainFam_over hg.1
    have hS : ocPulseWindow D.α D.q D.Λ i p ⊆
        slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0) := fun t ht =>
      hg.mem_slotWin env.hΛ1 ht
    have hMat : Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => (chainFam D dd n).jacC x t :=
      measurable_pi_iff.2 fun a' => measurable_pi_iff.2 fun c' =>
        CFam.measurable_jacC hO.ok hO.cont hx hS a' c'
    have hinv : ∀ b' : Fin 2, Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹ b' c := by
      intro b'
      have := (invSub_entryFun b' c).meas.add_const (if b' = c then (1 : ℂ) else 0)
      simpa using this
    have hd : ∀ b' : Fin 2, Measurable fun t : ocPulseWindow D.α D.q D.Λ i p =>
        deriv (fun u => (chainFam D dd n).jacC x u a b') t := fun b' =>
      (measurable_deriv _).comp measurable_subtype_coe
    have h1 : Measurable fun t : ocPulseWindow D.α D.q D.Λ i p =>
        (((ocA D.α D.q D.Λ (i - 1))⁻¹ : ℝ) : ℂ) * strainEnt (chainFam D dd n) x t a c := by
      refine measurable_const.mul ?_
      simp only [strainEnt, Matrix.mul_apply, Matrix.of_apply]
      exact Finset.measurable_sum _ fun b' _ => (hd b').mul ((hinv b').comp hMat)
    convert h1 using 1
    funext t
    exact ownStrainExt_of hg hx
  · convert measurable_const (a := (0 : ℂ)) using 1
    funext t
    exact ownStrainExt_of_not fun h => hg h.1

theorem ownStrainExt_agree (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) (ζ : Vec 2) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ownStrainExt D b j₀ i p a c ch.data ch.children.length t (ch.paramsC ζ) =
      ((GeoLetter.eval D i .own (.strain a c) t ch ζ : ℝ) : ℂ) := by
  have hΛ1 := env.hΛ1
  have hdd := chainOK_of_admissible hch
  have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
  have hx := GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
  have hO := env.chainFam_over hdd
  obtain ⟨Vel, hV⟩ := chainVel env hdd
  have hW := goodData_slotWin_mem_nhds hΛ1 hg ht
  have hl : ch.lastLevel = i - 1 := by
    have hi : ch.baseLevel + ch.children.length + 1 = i := hch.1
    show ch.baseLevel + ch.children.length = i - 1
    omega
  rw [ownStrainExt_of hg hx, strainEnt_real hO.ok hV hx (mem_of_mem_nhds hW) hW
    (M := fun u => ch.famJac D u)
    (fun u hu a' c' => jacC_chainFam_real env hch ζ (by rw [hg.2.1, hg.2.2] at hu; exact hu) a' c')
    a c]
  simp only [GeoLetter.eval, GeoLetter.evalAt, RealChain.famStrain, hl]
  push_cast
  ring

/-- The own-frame strain letter does not depend on the final phase. -/
theorem ownStrainExt_shift (hΛ : 1 ≤ D.Λ) (a c : Fin 2) {dd : ChainData} {n : ℕ} (t : ℝ)
    (x : ChainParamsC n) (z : CVec) (hz : ∀ a', (z a').im = 0) :
    ownStrainExt D b j₀ i p a c dd n t (x.1, x.2.1, x.2.2 + z) =
      ownStrainExt D b j₀ i p a c dd n t x := by
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hmem : ((x.1, x.2.1, x.2.2 + z) : ChainParamsC n) ∈ carrierC D b dd n 2 ↔
      x ∈ carrierC D b dd n 2 := by
    unfold carrierC
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Complex.add_im, hz, add_zero]
  have hj : ∀ u, (chainFam D dd n).jacC (x.1, x.2.1, x.2.2 + z) u = (chainFam D dd n).jacC x u :=
    fun u => jacC_chainFam_final D hε dd x _ u
  have hs : strainEnt (chainFam D dd n) (x.1, x.2.1, x.2.2 + z) t a c =
      strainEnt (chainFam D dd n) x t a c := by
    simp only [strainEnt, hj]
  unfold ownStrainExt
  rw [hmem, hs]

/-- The own-frame strain letter is invariant under the child-phase translations. -/
theorem ownStrainExt_shiftChild (hΛ : 1 ≤ D.Λ) (a c : Fin 2) {dd : ChainData} {n : ℕ} (t : ℝ)
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2} (hv : TInt (dd.slots.getD k 0) v) :
    ownStrainExt D b j₀ i p a c dd n t (x.shiftChild k v) =
      ownStrainExt D b j₀ i p a c dd n t x := by
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hj : ∀ u, (chainFam D dd n).jacC (x.shiftChild k v) u = (chainFam D dd n).jacC x u :=
    fun u => jacC_chainFam_shiftChild D hε dd x k hv u
  have hs : strainEnt (chainFam D dd n) (x.shiftChild k v) t a c =
      strainEnt (chainFam D dd n) x t a c := by
    simp only [strainEnt, hj]
  unfold ownStrainExt
  rw [mem_carrierC_shiftChild_iff, hs]

/-- **The own-frame strain letter**: only the zero mode, at most `K`. -/
theorem CtxInv.strainOwn (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) :
    CtxInv D b j₀ i p (GeoLetter.eval D i .own (.strain a c)) (ownStrainExt D b j₀ i p a c)
      (fun _ h _ => if h = 0 then ENNReal.ofReal chainK else 0) where
  hol dd n _ ht := ownStrainExt_hol env a c dd n ht
  meas dd n _ hx := ownStrainExt_meas env a c dd n hx
  agree _ _ ht ζ hch := ownStrainExt_agree env a c hch ζ ht
  fin _ _ t _ x _ v _ := ownStrainExt_shift env.hΛ1 a c t x (fun a' => (v a' : ℂ)) fun a' => by simp
  child _ _ t _ x _ k _ hv := ownStrainExt_shiftChild env.hΛ1 a c t x k hv
  bdd dd n _ _ := ⟨univ, univ_mem, chainK, fun _ ht y _ => norm_ownStrainExt_le env a c dd n ht y⟩
  mode _ _ _ h t ht dd n _ x _ _ := by
    rw [finalPhaseCoeff_of_invariant _ (fun s => ownStrainExt_shift env.hΛ1 a c t x _ fun a' => by
      split_ifs <;> simp)]
    split_ifs with h0
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_ownStrainExt_le env a c dd n ht x)
    · simp

end AVRegularity.Providers.ComplexContext
end
end

section
/-! **Carrier calculus: the child-frame strain letter** `a_i⁻¹ (∂_uF^♮_u (F^♮_u)⁻¹)(t)`
(`geo (child 𝗉') (strain a c)`, not gated by the cutoff). The strain of the
appended child does not depend on the finer slot (`contextStrain_eq_childStrain`), so the extension
uses at each output time `t` the odd slot `k(t)` of level `i + 1` nearest to `t` (`oddNear`), whose
cutoff does not vanish at `t` (`cutoff_oddNear_ne`): it is `a_i⁻¹` times the strain entry of the
extended appended child `appFamX k(t)` at `(x, λ_{k(t)}(t))` (`childStrainExt`). The extended
appended child has a velocity (`appFamX_velOK`), so the strain entry is holomorphic, bounded by
the rate `K a_i`, and equal to the real strain of the appended chain. In time, the extension is
measurable on each of the countably many pieces `k(t) = k` by the Carathéodory property in the
displacement scalar (`measurable_caratheodory_comp_c`). Its modes are at most
`K e^{-6πb|h|}` (`CtxInv.strainChild`). -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal

namespace AVRegularity.Providers.ComplexFlow

/-- **The velocity of the pullback.** -/
theorem CFam.VelOK.pullFst {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
    {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ : ℝ} {Vel : Par → ℝ → CVec → CVec}
    (hV : F.VelOK Ω W ϱ Vel) (V : Set ℂ) :
    F.pullFst.VelOK (Ω ×ˢ V) W ϱ (fun P => Vel P.1) where
  hol t ht := by
    have hφ : DifferentiableOn ℂ (fun q : (Par × ℂ) × CVec => ((q.1.1, q.2) : Par × CVec))
        (F.pullFst.dom (Ω ×ˢ V) ϱ t) :=
      (differentiable_fst.fst.prodMk differentiable_snd).differentiableOn
    exact (hV.hol t ht).comp hφ fun q hq => ⟨hq.1.1, hq.2⟩
  lim P hP t ht ε hε := hV.lim P.1 hP.1 t ht ε hε

end AVRegularity.Providers.ComplexFlow

namespace AVRegularity.Providers.ComplexContext

open AVRegularity.Providers.ComplexFlow

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-! ### The velocity of the extended appended child -/

/-- **The extended appended child has a velocity.** -/
theorem appFamX_velOK (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hdd : ChainOK D j₀ dd n) {p' : ℤ} (hp' : IsScheduledIn D (appLevel dd n) p' (appSlot dd)) :
    ∃ Vel, (appFamX D dd n p').VelOK (appOmega D b dd n) (slotWin D (appLevel dd n + 1) p')
      (8 * b * D.eps (appLevel dd n)) Vel := by
  have hS : LevelScales D b (dd.baseLevel + n) :=
    levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
      (by have := hdd.base; omega)
  have hF := (env.chainFam_over hdd).pullFst (V := ball (0 : ℂ) (lamR D dd n)) isOpen_ball
  obtain ⟨h1, h2, h3, h4⟩ := appFamX_conds env hdd
  have hC := hF.childHyp hS env.hζ hp' h1 h2 h3 h4
  obtain ⟨Vel, hV⟩ := chainVel env hdd
  exact ⟨_, hC.velOK (hV.pullFst (ball (0 : ℂ) (lamR D dd n))) fun t ht =>
    slotWin_neBot env.hΛ1 _ _ (hC.hW' ht)⟩

theorem goodData_appFamX_velOK (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) {p' : ℤ} (hsch : IsScheduledIn D i p' p) :
    ∃ Vel, (appFamX D dd n p').VelOK (appOmega D b dd n) (slotWin D (i + 1) p')
      (8 * b * D.eps i) Vel := by
  have hlev : appLevel dd n = i := hg.2.2
  obtain ⟨Vel, hV⟩ := appFamX_velOK env hg.1 (p' := p')
    (by rw [hlev, show appSlot dd = p from hg.2.1]; exact hsch)
  rw [hlev] at hV
  exact ⟨Vel, hV⟩

/-! ### The odd slot nearest to a time -/

/-- The odd slot `2⌊t/(2τ_{i+1})⌋ + 1` of level `i + 1`, within `τ_{i+1}` of the time `t`. -/
def oddNear (D : OCData) (i : ℕ) (t : ℝ) : ℤ := 2 * ⌊t / ocTau D.α D.q D.Λ (i + 1) / 2⌋ + 1

theorem cutoff_oddNear_ne (hΛ : 1 ≤ D.Λ) (i : ℕ) (t : ℝ) :
    ocCutoff D.α D.q D.Λ (i + 1) (oddNear D i t) t ≠ 0 := by
  have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) := Construction.Stream.ocTau_pos hΛ
  set τ := ocTau D.α D.q D.Λ (i + 1) with hτdef
  set m := ⌊t / τ / 2⌋ with hm
  have h1 : (m : ℝ) ≤ t / τ / 2 := Int.floor_le _
  have h2 : t / τ / 2 < m + 1 := Int.lt_floor_add_one _
  have e : t / τ / 2 * (2 * τ) = t := by field_simp
  have h3 : (m : ℝ) * (2 * τ) ≤ t := by
    calc (m : ℝ) * (2 * τ) ≤ t / τ / 2 * (2 * τ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = t := e
  have h4 : t < ((m : ℝ) + 1) * (2 * τ) := by
    calc t = t / τ / 2 * (2 * τ) := e.symm
      _ < ((m : ℝ) + 1) * (2 * τ) := mul_lt_mul_of_pos_right h2 (by positivity)
  have hab : |t - ((oddNear D i t : ℤ) : ℝ) * τ| ≤ τ := by
    have e2 : ((oddNear D i t : ℤ) : ℝ) = 2 * (m : ℝ) + 1 := by
      unfold oddNear
      push_cast
      ring
    rw [e2, abs_le]
    constructor <;> linarith
  unfold ocCutoff
  refine ne_of_gt (Real.smoothTransition.pos_of_pos ?_)
  have h5 : 2 * |t - ((oddNear D i t : ℤ) : ℝ) * τ| / τ ≤ 2 := by
    rw [div_le_iff₀ hτ]
    linarith
  linarith

theorem oddNear_sched (hΛ : 1 ≤ D.Λ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    IsScheduledIn D i (oddNear D i t) p :=
  ⟨t, cutoff_oddNear_ne hΛ i t, ht⟩

theorem measurable_oddNear (D : OCData) (i : ℕ) : Measurable (oddNear D i) := by
  have h1 : Measurable fun t : ℝ => ⌊t / ocTau D.α D.q D.Λ (i + 1) / 2⌋ :=
    (measurable_id.div_const _ |>.div_const _).floor
  exact (measurable_of_countable (fun m : ℤ => 2 * m + 1)).comp h1

/-! ### Carathéodory in the displacement scalar -/

/-- **Measurability of a composition with a function continuous in a complex parameter and
measurable in time.** -/
theorem measurable_caratheodory_comp_c {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {T : Set ℝ} {U : Set ℂ} {G : ℝ → ℂ → ℂ}
    (hG : ∀ t ∈ T, ContinuousOn (G t) U) (hm : ∀ y ∈ U, Measurable fun t : T => G t y)
    (τ : α → T) (hτ : Continuous τ) (φ : α → U) (hφ : Continuous φ) :
    Measurable fun a => G (τ a) (φ a) := by
  set u : U → T → ℂ := fun y t => G t y with hu
  have hc : ∀ t : T, Continuous fun y : U => u y t := fun t =>
    (continuousOn_iff_continuous_domRestrict.mp (hG t t.2))
  have hmeas : ∀ y : U, Measurable (u y) := fun y => hm y y.2
  have hU := measurable_uncurry_of_continuous_of_measurable hc hmeas
  exact hU.comp (hφ.prodMk hτ).measurable

theorem measurable_inv_apply (b' c : Fin 2) :
    Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹ b' c := by
  have := (invSub_entryFun b' c).meas.add_const (if b' = c then (1 : ℂ) else 0)
  simpa using this

/-! ### The extension -/

open scoped Classical in
/-- **The extension of the child-frame strain letter**, through the appended child of the odd
slot nearest to the output time. -/
def childStrainExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (a c : Fin 2) : Ext :=
  fun dd n t x => if GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 then
    (((ocA D.α D.q D.Λ i)⁻¹ : ℝ) : ℂ) *
      strainEnt (appFamX D dd n (oddNear D i t)) (x, lamT D dd n (oddNear D i t) t) t a c
    else 0

theorem childStrainExt_of {a c : Fin 2} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : GoodData D j₀ i p dd n) (hx : x ∈ carrierC D b dd n 2) :
    childStrainExt D b j₀ i p a c dd n t x = (((ocA D.α D.q D.Λ i)⁻¹ : ℝ) : ℂ) *
      strainEnt (appFamX D dd n (oddNear D i t)) (x, lamT D dd n (oddNear D i t) t) t a c := by
  unfold childStrainExt
  split_ifs with h
  · rfl
  · exact (h ⟨hg, hx⟩).elim

theorem childStrainExt_of_not {a c : Fin 2} {dd : ChainData} {n : ℕ} {t : ℝ}
    {x : ChainParamsC n} (h : ¬(GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2)) :
    childStrainExt D b j₀ i p a c dd n t x = 0 := by
  unfold childStrainExt
  split_ifs with h'
  · exact (h h').elim
  · rfl

/-- **The size of the child-frame strain letter.** -/
theorem norm_childStrainExt_le (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData)
    (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (x : ChainParamsC n) :
    ‖childStrainExt D b j₀ i p a c dd n t x‖ ≤ chainK := by
  have hΛ1 := env.hΛ1
  by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
  · obtain ⟨hg, hx⟩ := hgx
    have hcut := cutoff_oddNear_ne hΛ1 i t
    have hsch := oddNear_sched hΛ1 ht
    have hO := goodData_appFamX_over env hg hsch
    obtain ⟨Vel, hV⟩ := goodData_appFamX_velOK env hg hsch
    have hW := slotWin_mem_nhds_of_cutoff hΛ1 hcut
    have htW := mem_of_mem_nhds hW
    have hP : ((x, lamT D dd n (oddNear D i t) t) : ChainParamsC n × ℂ) ∈ appOmega D b dd n :=
      ⟨hx, lamT_mem env.hζ hΛ1 (dd := dd) (n := n) (p' := oddNear D i t) (t := t)
        (by rw [show appLevel dd n = i from hg.2.2]; exact htW)⟩
    have hb := norm_strainEnt_le hO.ok hV hP htW hW a c
    have hA := ocA_pos hΛ1 i
    rw [childStrainExt_of hg hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hA]
    calc (ocA D.α D.q D.Λ i)⁻¹ *
          ‖strainEnt (appFamX D dd n (oddNear D i t)) (x, lamT D dd n (oddNear D i t) t) t a c‖
        ≤ (ocA D.α D.q D.Λ i)⁻¹ * (chainK * ocA D.α D.q D.Λ i) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA.le)
      _ = chainK := by field_simp
  · rw [childStrainExt_of_not hgx, norm_zero, chainK_eq]
    norm_num

theorem childStrainExt_hol (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData) (n : ℕ)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    DifferentiableOn ℂ (childStrainExt D b j₀ i p a c dd n t) (carrierC D b dd n 2) := by
  have hΛ1 := env.hΛ1
  by_cases hg : GoodData D j₀ i p dd n
  · have hcut := cutoff_oddNear_ne hΛ1 i t
    have hsch := oddNear_sched hΛ1 ht
    have hO := goodData_appFamX_over env hg hsch
    obtain ⟨Vel, hV⟩ := goodData_appFamX_velOK env hg hsch
    have hW := slotWin_mem_nhds_of_cutoff hΛ1 hcut
    have htW := mem_of_mem_nhds hW
    have hlam := lamT_mem env.hζ hΛ1 (dd := dd) (n := n) (p' := oddNear D i t) (t := t)
      (by rw [show appLevel dd n = i from hg.2.2]; exact htW)
    have hmap : MapsTo (fun x : ChainParamsC n =>
        ((x, lamT D dd n (oddNear D i t) t) : ChainParamsC n × ℂ))
        (carrierC D b dd n 2) (appOmega D b dd n) := fun x hx => ⟨hx, hlam⟩
    have hd := ((differentiableOn_strainEnt hO.ok hV htW hW a c).comp
      (differentiableOn_id.prodMk (differentiableOn_const _)) hmap).const_mul
      ((((ocA D.α D.q D.Λ i)⁻¹ : ℝ) : ℂ))
    exact hd.congr fun x hx => childStrainExt_of hg hx
  · have : childStrainExt D b j₀ i p a c dd n t = fun _ => 0 :=
      funext fun x => childStrainExt_of_not fun h => hg h.1
    rw [this]
    exact differentiableOn_const 0

theorem childStrainExt_meas (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) (dd : ChainData) (n : ℕ)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) :
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => childStrainExt D b j₀ i p a c dd n t x := by
  have hΛ1 := env.hΛ1
  by_cases hg : GoodData D j₀ i p dd n
  · set g : ℤ → ocPulseWindow D.α D.q D.Λ i p → ℂ := fun k t =>
      if ocCutoff D.α D.q D.Λ (i + 1) k (t : ℝ) ≠ 0 then
        (((ocA D.α D.q D.Λ i)⁻¹ : ℝ) : ℂ) *
          strainEnt (appFamX D dd n k) (x, lamT D dd n k t) t a c
      else 0 with hgdef
    have hgm : ∀ k, Measurable (g k) := by
      intro k
      by_cases hk : IsScheduledIn D i k p
      · have hO := goodData_appFamX_over env hg hk
        obtain ⟨Vel, hV⟩ := goodData_appFamX_velOK env hg hk
        have hcutc : Continuous fun t : ℝ => ocCutoff D.α D.q D.Λ (i + 1) k t := by
          unfold ocCutoff; exact Real.smoothTransition.continuous.comp (by fun_prop)
        set S : Set (ocPulseWindow D.α D.q D.Λ i p) :=
          {t | ocCutoff D.α D.q D.Λ (i + 1) k (t : ℝ) ≠ 0} with hS
        have hSm : MeasurableSet S :=
          (isOpen_ne_fun (hcutc.comp continuous_subtype_val) continuous_const).measurableSet
        refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
        · set T : Set ℝ := {t | ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0} with hT
          set U : Set ℂ := ball (0 : ℂ) (lamR D dd n) with hU
          have hxU : ∀ w ∈ U, ((x, w) : ChainParamsC n × ℂ) ∈ appOmega D b dd n :=
            fun w hw => ⟨hx, hw⟩
          have hG : ∀ t ∈ T, ContinuousOn
              (fun w : ℂ => strainEnt (appFamX D dd n k) (x, w) t a c) U := by
            intro t ht
            have hW := slotWin_mem_nhds_of_cutoff hΛ1 ht
            exact ((differentiableOn_strainEnt hO.ok hV (mem_of_mem_nhds hW) hW a c).comp
              ((differentiableOn_const x).prodMk differentiableOn_id) hxU).continuousOn
          have hm : ∀ w ∈ U, Measurable fun t : T =>
              strainEnt (appFamX D dd n k) (x, w) t a c := by
            intro w hw
            have hTS : T ⊆ slotWin D (i + 1) k := fun t ht => mem_slotWin_of_cutoff D hΛ1 ht
            have hMat : Measurable fun t : T => (appFamX D dd n k).jacC (x, w) t :=
              measurable_pi_iff.2 fun a' => measurable_pi_iff.2 fun c' =>
                CFam.measurable_jacC hO.ok hO.cont (hxU w hw) hTS a' c'
            simp only [strainEnt, Matrix.mul_apply, Matrix.of_apply]
            exact Finset.measurable_sum _ fun b' _ =>
              ((measurable_deriv _).comp measurable_subtype_coe).mul
                ((measurable_inv_apply b' c).comp hMat)
          have hτ : Continuous fun t : S => (⟨(t : ℝ), t.2⟩ : T) :=
            (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
          have hφ : Continuous fun t : S => (⟨lamT D dd n k t, lamT_mem env.hζ hΛ1
              (by rw [show appLevel dd n = i from hg.2.2]; exact mem_slotWin_of_cutoff D hΛ1 t.2)⟩ :
                U) :=
            ((continuous_lamT env.hζ dd n k).comp
              (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
          have h1 := measurable_caratheodory_comp_c hG hm _ hτ _ hφ
          have h2 := (measurable_const (a := ((((ocA D.α D.q D.Λ i)⁻¹ : ℝ) : ℂ)))).mul h1
          convert h2 using 1
          funext t
          show g k t = _
          rw [hgdef]
          dsimp only
          split_ifs with h
          · rfl
          · exact absurd t.2 h
        · convert measurable_const (a := (0 : ℂ)) using 1
          funext t
          show g k t = 0
          rw [hgdef]
          dsimp only
          split_ifs with h
          · exact absurd h t.2
          · rfl
      · have : g k = fun _ => 0 := by
          funext t
          have h0 : ocCutoff D.α D.q D.Λ (i + 1) k (t : ℝ) = 0 := by
            by_contra hne
            exact hk ⟨t, hne, t.2⟩
          rw [hgdef]
          dsimp only
          split_ifs with h
          · exact absurd h0 h
          · rfl
        rw [this]
        exact measurable_const
    have hprod : Measurable fun q : ocPulseWindow D.α D.q D.Λ i p × ℤ => g q.2 q.1 :=
      measurable_from_prod_countable_left fun k => hgm k
    have hpair : Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => (t, oddNear D i t) :=
      measurable_id.prodMk ((measurable_oddNear D i).comp measurable_subtype_coe)
    have hfun : (fun t : ocPulseWindow D.α D.q D.Λ i p => childStrainExt D b j₀ i p a c dd n t x) =
        (fun q : ocPulseWindow D.α D.q D.Λ i p × ℤ => g q.2 q.1) ∘
          fun t : ocPulseWindow D.α D.q D.Λ i p => (t, oddNear D i t) := by
      funext t
      show childStrainExt D b j₀ i p a c dd n t x = g (oddNear D i t) t
      rw [childStrainExt_of hg hx, hgdef]
      dsimp only
      split_ifs with h
      · rfl
      · exact absurd (cutoff_oddNear_ne hΛ1 i t) h
    rw [hfun]
    exact hprod.comp hpair
  · convert measurable_const (a := (0 : ℂ)) using 1
    funext t
    exact childStrainExt_of_not fun h => hg h.1

theorem childStrainExt_agree (env : ChainEnv D b CH Υ j₀) (a c : Fin 2) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {p' : ℤ} (ζ : Vec 2) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    childStrainExt D b j₀ i p a c ch.data ch.children.length t (ch.paramsC ζ) =
      ((GeoLetter.eval D i (.child p') (.strain a c) t ch ζ : ℝ) : ℂ) := by
  have hΛ1 := env.hΛ1
  have hdd := chainOK_of_admissible hch
  have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
  have hx := GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
  have hcut := cutoff_oddNear_ne hΛ1 i t
  have hsch := oddNear_sched hΛ1 ht
  have hO := goodData_appFamX_over env hg hsch
  obtain ⟨Vel, hV⟩ := goodData_appFamX_velOK env hg hsch
  have hW := slotWin_mem_nhds_of_cutoff hΛ1 hcut
  have htW := mem_of_mem_nhds hW
  have hP : ((ch.paramsC ζ, lamT D ch.data ch.children.length (oddNear D i t) t) :
      ChainParamsC ch.children.length × ℂ) ∈ appOmega D b ch.data ch.children.length :=
    ⟨hx, lamT_mem env.hζ hΛ1 (by rw [show appLevel ch.data ch.children.length = i from hg.2.2]; exact htW)⟩
  rw [childStrainExt_of hg hx, strainEnt_real hO.ok hV hP htW hW
    (M := fun u => (ch.appendChild D (oddNear D i t) t ζ).famJac D u)
    (fun u hu a' c' => by
      rw [← appFam_jacC_eq]
      exact jacC_appFam_real_at env hch hsch ζ htW hu a' c') a c]
  have hl : ch.WellSlotted := hch.2.2.1
  have hfs : (ch.appendChild D (oddNear D i t) t ζ).famStrain D t =
      (ch.appendChild D p' t ζ).famStrain D t := by
    rw [← GenSem.contextStrain_eq_childStrain D env.hζ hΛ1 ch hl (oddNear D i t) t ζ,
      GenSem.contextStrain_eq_childStrain D env.hζ hΛ1 ch hl p' t ζ]
  have hlast : (ch.appendChild D p' t ζ).lastLevel = i := by
    have hi : ch.baseLevel + ch.children.length + 1 = i := hch.1
    simp only [RealChain.lastLevel, RealChain.appendChild, List.length_append,
      List.length_singleton]
    omega
  have e1 : (Matrix.of fun a c => deriv (fun u => (ch.appendChild D (oddNear D i t) t ζ).famJac D u a c) t) *
      ((ch.appendChild D (oddNear D i t) t ζ).famJac D t)⁻¹ =
      (ch.appendChild D (oddNear D i t) t ζ).famStrain D t := rfl
  rw [e1, hfs]
  simp only [GeoLetter.eval, GeoLetter.isStrain, true_or, ↓reduceIte, GeoLetter.evalAt, hlast]
  push_cast
  ring

/-- The child-frame strain letter does not see the final-phase translations. -/
theorem childStrainExt_shiftFinal (hΛ : 1 ≤ D.Λ) (a c : Fin 2) {dd : ChainData} {n : ℕ} (t : ℝ)
    (x : ChainParamsC n) {v : Vec 2} (hv : TInt (dd.slots.getLastD 0) v) :
    childStrainExt D b j₀ i p a c dd n t (x.shiftFinal v) =
      childStrainExt D b j₀ i p a c dd n t x := by
  have hj : ∀ u, (appFamX D dd n (oddNear D i t)).jacC
      (x.shiftFinal v, lamT D dd n (oddNear D i t) t) u =
      (appFamX D dd n (oddNear D i t)).jacC (x, lamT D dd n (oddNear D i t) t) u := fun u =>
    jacC_of_toGeom (appFamX_toGeom_shiftFinal hΛ dd n _ (x, lamT D dd n (oddNear D i t) t) hv) u
  have hs : strainEnt (appFamX D dd n (oddNear D i t))
      (x.shiftFinal v, lamT D dd n (oddNear D i t) t) t a c =
      strainEnt (appFamX D dd n (oddNear D i t)) (x, lamT D dd n (oddNear D i t) t) t a c := by
    simp only [strainEnt, hj]
  unfold childStrainExt
  rw [mem_carrierC_shiftFinal_iff, hs]

/-- The child-frame strain letter does not see the child-phase translations. -/
theorem childStrainExt_shiftChild (hΛ : 1 ≤ D.Λ) (a c : Fin 2) {dd : ChainData} {n : ℕ} (t : ℝ)
    (x : ChainParamsC n) (k : Fin n) {v : Vec 2} (hv : TInt (dd.slots.getD k 0) v) :
    childStrainExt D b j₀ i p a c dd n t (x.shiftChild k v) =
      childStrainExt D b j₀ i p a c dd n t x := by
  have hj : ∀ u, (appFamX D dd n (oddNear D i t)).jacC
      (x.shiftChild k v, lamT D dd n (oddNear D i t) t) u =
      (appFamX D dd n (oddNear D i t)).jacC (x, lamT D dd n (oddNear D i t) t) u := fun u =>
    jacC_of_toGeom (appFamX_toGeom_shiftChild hΛ dd n _ (x, lamT D dd n (oddNear D i t) t) k hv) u
  have hs : strainEnt (appFamX D dd n (oddNear D i t))
      (x.shiftChild k v, lamT D dd n (oddNear D i t) t) t a c =
      strainEnt (appFamX D dd n (oddNear D i t)) (x, lamT D dd n (oddNear D i t) t) t a c := by
    simp only [strainEnt, hj]
  unfold childStrainExt
  rw [mem_carrierC_shiftChild_iff, hs]

/-- **The child-frame strain letter**, with the profile `K e^{-6πb|h|}`. -/
theorem CtxInv.strainChild (env : ChainEnv D b CH Υ j₀) (p' : ℤ) (a c : Fin 2) :
    CtxInv D b j₀ i p (GeoLetter.eval D i (.child p') (.strain a c)) (childStrainExt D b j₀ i p a c)
      (fun _ h _ => ENNReal.ofReal (chainK * Real.exp (-(6 * Real.pi * b * |(h : ℝ)|)))) where
  hol dd n _ ht := childStrainExt_hol env a c dd n ht
  meas dd n _ hx := childStrainExt_meas env a c dd n hx
  agree _ _ ht ζ hch := childStrainExt_agree env a c hch ζ ht
  fin _ _ t _ x _ _ hv := childStrainExt_shiftFinal env.hΛ1 a c t x hv
  child _ _ t _ x _ k _ hv := childStrainExt_shiftChild env.hΛ1 a c t x k hv
  bdd dd n _ _ := ⟨univ, univ_mem, chainK, fun _ ht y _ => norm_childStrainExt_le env a c dd n ht y⟩
  mode _ _ hm2 h _ ht _ _ hdd _ hx hre :=
    ctxMode_le_of_uniform env.hb0 (fun dd n _ ht => childStrainExt_hol env a c dd n ht)
      (fun _ _ t _ x _ _ hv => childStrainExt_shiftFinal env.hΛ1 a c t x hv)
      (fun dd n _ ht x _ => norm_childStrainExt_le env a c dd n ht x) hm2 h ht hdd hx hre

end AVRegularity.Providers.ComplexContext
end
end
