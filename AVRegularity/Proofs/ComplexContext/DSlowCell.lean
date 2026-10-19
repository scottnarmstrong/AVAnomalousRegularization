-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexContext.ExtFam
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexContext.Restrict
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexFlow

/-! **Carrier calculus: the Jacobian of the appended child.**
* `measurable_fderiv_moving`: a derivative at a moving point of a family jointly continuous in
  time and point is measurable in time;
* `appFamX_toGeom_shiftFinal`, `appFamX_toGeom_shiftChild`: the extended appended child is
  invariant under the phase translations (the shear is periodic in the transverse phase);
* `jacC_appFam_real_at`, `jacC_appFam_real`: at the real parameters of an admissible chain, the
  Jacobian of the appended child is the real Jacobian of the chain with the appended child;
* `jacSub_entryFun`: the entries of `F − I` as a certifiable function of the Jacobian. -/

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

/-- **Measurability in time of a derivative at a moving point.** -/
theorem measurable_fderiv_moving {g : ℝ → CVec → CVec} {T : Set ℝ} {c : ℝ → CVec} {ρ : ℝ}
    (hρ : 0 < ρ) (hcc : ContinuousOn c T)
    (hc : ContinuousOn (fun q : ℝ × CVec => g q.1 q.2) {q | q.1 ∈ T ∧ q.2 ∈ ball (c q.1) ρ})
    (hd : ∀ t ∈ T, DifferentiableAt ℂ (g t) (c t)) {S : Set ℝ} (hS : S ⊆ T) (w : CVec) :
    Measurable fun t : S => fderiv ℂ (g t) (c t) w := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖w‖ / ρ)
  set cn : ℕ → ℂ := fun n => ((n + N + 1 : ℕ) : ℂ) with hc_def
  have hcpos : ∀ n, (0 : ℝ) < (n + N + 1 : ℕ) := fun n => by positivity
  have hnc : ∀ n, ‖cn n‖ = ((n + N + 1 : ℕ) : ℝ) := fun n => by
    rw [hc_def, Complex.norm_natCast]
  have hsmall : ∀ n, ‖(cn n)⁻¹ • w‖ < ρ := by
    intro n
    rw [norm_smul, norm_inv, hnc]
    have h1 : ‖w‖ / ρ < (n + N + 1 : ℕ) := by
      have : (N : ℝ) ≤ (n + N + 1 : ℕ) := by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      linarith
    rw [div_lt_iff₀ hρ] at h1
    rw [inv_mul_lt_iff₀ (hcpos n)]
    linarith
  have hcont : ∀ z : CVec, ‖z‖ < ρ → Continuous fun t : S => g t (c t + z) := by
    intro z hz
    have h1 : ContinuousOn (fun t : ℝ => g t (c t + z)) T := by
      refine hc.comp (continuousOn_id.prodMk (hcc.add continuousOn_const)) fun t ht => ⟨ht, ?_⟩
      rw [mem_ball, dist_eq_norm]; simpa using hz
    exact (h1.mono hS).domRestrict
  have hf : ∀ n, Measurable fun t : S => cn n • (g t (c t + (cn n)⁻¹ • w) - g t (c t)) := by
    intro n
    have h2 := (hcont _ (hsmall n)).sub (by simpa using hcont 0 (by simpa using hρ))
    exact (h2.const_smul (cn n)).measurable
  refine measurable_of_tendsto_metrizable' atTop hf ?_
  rw [tendsto_pi_nhds]
  intro t
  have hl := (hd t (hS t.2)).hasFDerivAt.lim w (c := cn) (l := atTop) (by
    simp_rw [hnc]
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩))
  exact hl

/-! ### Symmetries of the extended appended child -/

theorem appFamX_toGeom (hΛ : 1 ≤ D.Λ) (dd : ChainData) (n : ℕ) (p' : ℤ)
    (P : ChainParamsC n × ℂ) :
    (appFamX D dd n p').toGeom P = childGeomC D (appLevel dd n) (appSlot dd)
      (D.slotAnchor (appLevel dd n + 1) p')
      (epsC D (appLevel dd n) • (P.2 • appShear D dd n P.1.2.2),
        P.1.2.2 + P.2 • appShear D dd n P.1.2.2) ((chainFam D dd n).toGeom P.1) := by
  have hε : D.eps (appLevel dd n) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold appFamX
  rw [CFam.toGeom, ← CFam.child_eq_childGeomC D hε]
  rfl

theorem appShear_shift (hΛ : 1 ≤ D.Λ) (dd : ChainData) (n : ℕ) (ζ : CVec) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (appSlot dd)) = m) :
    appShear D dd n (ζ + ofRealVec v) = appShear D dd n ζ := by
  have hε : ocEpsilon D.q D.Λ (appLevel dd n) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold appShear
  rw [smul_add]
  exact ocShearVelC_shift (α := D.α) hε _ hv

/-- **The extended appended child does not see the final-phase translations.** -/
theorem appFamX_toGeom_shiftFinal (hΛ : 1 ≤ D.Λ) (dd : ChainData) (n : ℕ) (p' : ℤ)
    (P : ChainParamsC n × ℂ) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getLastD 0)) = m) :
    (appFamX D dd n p').toGeom (P.1.shiftFinal v, P.2) = (appFamX D dd n p').toGeom P := by
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [appFamX_toGeom hΛ, appFamX_toGeom hΛ]
  have hfin := chainFam_final D hε dd P.1 (P.1.shiftFinal v).2.2
  have hpar : (chainFam D dd n).toGeom (P.1.shiftFinal v) = (chainFam D dd n).toGeom P.1 := by
    unfold CFam.toGeom
    rw [show P.1.shiftFinal v = (P.1.1, P.1.2.1, (P.1.shiftFinal v).2.2) from rfl, hfin.1, hfin.2]
  have hsh : appShear D dd n (P.1.shiftFinal v).2.2 = appShear D dd n P.1.2.2 :=
    appShear_shift hΛ dd n P.1.2.2 hv
  rw [hpar, hsh]
  have e : (P.1.shiftFinal v).2.2 + P.2 • appShear D dd n P.1.2.2 =
      (P.1.2.2 + P.2 • appShear D dd n P.1.2.2) + ofRealVec v := by
    simp only [ChainParamsC.shiftFinal]
    rw [show (fun a => ((v a : ℝ) : ℂ)) = ofRealVec v from rfl]
    abel
  rw [e]
  exact childGeomC_shift D (hε _) _ _ (_, _) _ hv

/-- **The extended appended child does not see the child-phase translations.** -/
theorem appFamX_toGeom_shiftChild (hΛ : 1 ≤ D.Λ) (dd : ChainData) (n : ℕ) (p' : ℤ)
    (P : ChainParamsC n × ℂ) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) :
    (appFamX D dd n p').toGeom (P.1.shiftChild k v, P.2) = (appFamX D dd n p').toGeom P := by
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [appFamX_toGeom hΛ, appFamX_toGeom hΛ]
  have hpar : (chainFam D dd n).toGeom (P.1.shiftChild k v) = (chainFam D dd n).toGeom P.1 := by
    obtain ⟨e1, e2⟩ := chainFam_shiftChild D hε dd P.1 k hv
    unfold CFam.toGeom
    rw [e1, e2]
  rw [hpar]
  rfl

theorem jacC_of_toGeom {n : ℕ} {F : CFam (ChainParamsC n × ℂ)} {P Q : ChainParamsC n × ℂ}
    (h : F.toGeom P = F.toGeom Q) (t : ℝ) : F.jacC P t = F.jacC Q t := by
  have e1 : F.fl P = F.fl Q := congrArg Prod.fst h
  have e2 : F.ctr P = F.ctr Q := congrArg (fun g : CGeom => g.2.1) h
  unfold CFam.jacC
  rw [e1, e2]

/-! ### The Jacobian of the appended child at real parameters -/

/-- **At the real parameters, the Jacobian of the appended child is the real Jacobian of the
appended chain**, at every time of the window of the finer slot. -/
theorem jacC_appFam_real_at (env : ChainEnv D b CH Υ j₀) {i : ℕ} {p : ℤ} {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {p' : ℤ} (hsch : IsScheduledIn D i p' p) (ζ : Vec 2)
    {t : ℝ} (ht : t ∈ slotWin D (i + 1) p') {u : ℝ} (hu : u ∈ slotWin D (i + 1) p') (a c : Fin 2) :
    (appFam D ch.data ch.children.length p' t).jacC (ch.paramsC ζ) u a c =
      (((ch.appendChild D p' t ζ).famJac D u a c : ℝ) : ℂ) := by
  have hΛ1 := env.hΛ1
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ1).ne'
  have hdd := chainOK_of_admissible hch
  have hag := chainFam_agree env.hΛ env.hvel env.hag env.hb1 env.hCH env.hΥ env.hcs hch ζ
  have hsep : ∀ m, j₀ ≤ m → ocTauPP D.α D.q D.Λ (m + 1) < ocTau D.α D.q D.Λ m / 48 :=
    fun m hm => separation_of_carrierStart hΛ1 env.hCH env.hcs hm
  set G := slotWin D (ch.baseLevel + 1) (ch.slots.headD 0)
  have hi : ch.baseLevel + ch.children.length + 1 = i := hch.1
  have hp : ch.slots.getLastD 0 = p := hch.2.2.2.1
  have hlev : appLevel ch.data ch.children.length = i := hi
  have hW : slotWin D i p ⊆ G := by
    have h1 := hdd.slotWin_subset hΛ1 hsep ch.children.length le_rfl
    have e1 : ch.data.baseLevel + 1 + ch.children.length = i := by
      show ch.baseLevel + 1 + ch.children.length = i; omega
    have e2 : ch.data.slots.getD ch.children.length 0 = p := by rw [hdd.getD_last]; exact hp
    have e3 : ch.data.slots.getD 0 0 = ch.slots.headD 0 := by
      show ch.slots.getD 0 0 = _; rcases ch.slots with _ | ⟨q, qs⟩ <;> rfl
    rw [e1, e2, e3] at h1
    exact h1
  have hjI : j₀ ≤ i := by
    have hb := hdd.base
    have e : ch.data.baseLevel = ch.baseLevel := rfl
    omega
  have hW' : slotWin D (i + 1) p' ⊆ G :=
    (slotWin_subset D hΛ1 hsch (hsep i hjI)).trans hW
  have hO := env.chainFam_over hdd
  have hancG : (ch.geom D).2.2 ∈ G := by
    rw [← hag.anchor, show (chainFam D ch.data ch.children.length).toGeom (ch.paramsC ζ) =
      ((chainFam D ch.data ch.children.length).fl (ch.paramsC ζ),
        (chainFam D ch.data ch.children.length).ctr (ch.paramsC ζ),
        (chainFam D ch.data ch.children.length).anc) from rfl]
    show (chainFam D ch.data ch.children.length).anc ∈ G
    rw [hO.anc]
    show D.slotAnchor (ch.baseLevel + ch.children.length + 1) (ch.slots.getLastD 0) ∈ G
    rw [hi, hp]
    exact hW (anchor_mem_slotWin D hΛ1 i p)
  have hs' : D.slotAnchor (i + 1) p' ∈ G := hW' (anchor_mem_slotWin D hΛ1 (i + 1) p')
  -- the appended real child and its complex parameters
  set cR : ChainChild := ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot
      (D.slotAnchor (ch.ctxLevel + 1) p') t ζ,
    ζ + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) p') t ζ⟩ with hcR
  have hctx : ch.ctxLevel = i := hi
  have hgeomR : (ch.appendChild D p' t ζ).geom D =
      D.childGeom i p (D.slotAnchor (i + 1) p') cR (ch.geom D) := by
    simp only [RealChain.geom, RealChain.appendChild]
    rw [ChainGeometry.geomAux_append D _ _ ch.children _ ch.slots _ hch.2.2.1]
    have hhead : (ch.slots ++ [p']).headD 0 = ch.slots.headD 0 := by
      cases h : ch.slots with
      | nil => have := hch.2.2.1; rw [h] at this; simp at this
      | cons a l => rfl
    have hL : ch.baseLevel + 1 + ch.children.length = i := by omega
    rw [hhead, hL, hp]
  have hccR : (appCenter D ch.data ch.children.length p' t (ch.paramsC ζ),
      appPhase D ch.data ch.children.length p' t (ch.paramsC ζ)) = cR.toC := by
    have hsl : ch.data.slots.getLastD 0 = ch.slot := rfl
    refine Prod.ext ?_ ?_
    · simp only [appCenter, hlev, hsl, ← hctx, ChainChild.toC, hcR]
      rw [show (ch.paramsC ζ).2.2 = ofRealVec ζ from rfl, relDispC_ofRealVec, epsC,
        ← ofRealVec_smul]
    · simp only [appPhase, hlev, hsl, ← hctx, ChainChild.toC, hcR]
      rw [show (ch.paramsC ζ).2.2 = ofRealVec ζ from rfl, relDispC_ofRealVec, ← ofRealVec_add]
  have hgeomC : (appFam D ch.data ch.children.length p' t).toGeom (ch.paramsC ζ) =
      childGeomC D i p (D.slotAnchor (i + 1) p') cR.toC
        ((chainFam D ch.data ch.children.length).toGeom (ch.paramsC ζ)) := by
    unfold appFam
    rw [CFam.toGeom, ← CFam.child_eq_childGeomC D (hε _)]
    rw [← hccR, hlev, show ch.data.slots.getLastD 0 = p from hp]
    rfl
  have hAg : CGeomAgree G ((appFam D ch.data ch.children.length p' t).toGeom (ch.paramsC ζ))
      ((ch.appendChild D p' t ζ).geom D) := by
    rw [hgeomC, hgeomR]
    exact childGeomC_agree D hag hancG i p hs' cR
  -- the derivative at the center
  have hApp := appFam_over env.hq env.hΛ env.hα env.hζ env.hvel env.hb0 env.hb1 env.hCH env.hΥ
    env.hcs hdd (p' := p') (by
      rw [hlev, show ch.data.slots.getLastD 0 = p from hp]; exact hsch)
    (t := t) (by rw [hlev]; exact ht)
  set F := appFam D ch.data ch.children.length p' t
  set x := ch.paramsC ζ
  have hxΩ : x ∈ carrierC D b ch.data ch.children.length 2 :=
    GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
  have huW : u ∈ slotWin D (appLevel ch.data ch.children.length + 1) p' := by rw [hlev]; exact hu
  have hU : DifferentiableOn ℂ (fun y => F.fl x u y F.anc)
      (ball (F.ctr x) (8 * b * D.eps (appLevel ch.data ch.children.length))) := fun y hy =>
    (hApp.ok.differentiableAt_fl hxΩ huW hApp.ok.anc_mem
      (by rw [hApp.ok.cur_anc x hxΩ]; exact hy)).differentiableWithinAt
  have hFf : ∀ y, F.fl x u (ofRealVec y) F.anc =
      ofRealVec (((ch.appendChild D p' t ζ).geom D).1 u y ((ch.appendChild D p' t ζ).geom D).2.2) := by
    intro y
    have := hAg.flow u (hW' hu) F.anc (by
      show D.slotAnchor (appLevel ch.data ch.children.length + 1) p' ∈ G
      rw [hlev]; exact hs') y
    rw [← hAg.anchor]
    exact this
  have hctr : F.ctr x = ofRealVec ((ch.appendChild D p' t ζ).geom D).2.1 := hAg.center
  have hx : ofRealVec ((ch.appendChild D p' t ζ).geom D).2.1 ∈
      ball (F.ctr x) (8 * b * D.eps (appLevel ch.data ch.children.length)) := by
    rw [← hctr]; exact mem_ball_self hApp.ok.hϱ
  have h := jacMatrix_ofReal_eq isOpen_ball hU hFf hx a c
  show fderiv ℂ (fun y => F.fl x u y F.anc) (F.ctr x) (cbasis c) a = _
  rw [hctr, h]
  rfl

/-- **At the real parameters, the Jacobian of the appended child is the real Jacobian of the
appended chain** (at the output time). -/
theorem jacC_appFam_real (env : ChainEnv D b CH Υ j₀) {i : ℕ} {p : ℤ} {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {p' : ℤ} (hsch : IsScheduledIn D i p' p) (ζ : Vec 2)
    {t : ℝ} (ht : t ∈ slotWin D (i + 1) p') (a c : Fin 2) :
    (appFam D ch.data ch.children.length p' t).jacC (ch.paramsC ζ) t a c =
      (((ch.appendChild D p' t ζ).famJac D t a c : ℝ) : ℂ) :=
  jacC_appFam_real_at env hch hsch ζ ht ht a c

/-! ### The entries of `F − I` -/

/-- **The entries of `F − I`.** -/
theorem jacSub_entryFun (a c : Fin 2) :
    EntryFun (fun A => A a c - (if a = c then 1 else 0))
      (fun A => A a c - (if a = c then 1 else 0)) (fun m => m) where
  hol := fun n U M hM _ => (hM a c).sub_const _
  meas := (measurable_pi_apply c |>.comp (measurable_pi_apply a)).sub_const _
  real := fun A => by split_ifs <;> simp
  bd := fun E m hE _ => by
    have h : ‖(1 + E) a c - (if a = c then 1 else 0)‖ = ‖E a c‖ := by
      congr 1
      simp only [Matrix.add_apply, Matrix.one_apply]
      split_ifs <;> ring
    rw [h]
    match a, c with
    | 0, 0 => linarith [hE.row0, norm_nonneg (E 0 1)]
    | 0, 1 => linarith [hE.row0, norm_nonneg (E 0 0)]
    | 1, 0 => linarith [hE.row1, norm_nonneg (E 1 1)]
    | 1, 1 => linarith [hE.row1, norm_nonneg (E 1 0)]
  B_nonneg := fun m hm => hm

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Metric Homogenization Complex
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: derivatives along a holomorphic family of parameter maps.** For a map `Φ(x, h)`,
holomorphic on `S × B(0, ρ₀)` with `Φ(x, 0) = x`, and a function `G` holomorphic on the open set
`S`, the derivative `dAlong Φ G w x = ∂_h G(Φ(x, h))|_{h=0}[w]` is:
* holomorphic in `x` on `S` (`differentiableOn_dAlong`);
* measurable in a parameter in which `G` is measurable (`measurable_dAlong`);
* at most `M/r` if `G(Φ(x, ζw))` is at most `M` for `|ζ| ≤ r` (Cauchy, `norm_dAlong_le`);
* locally bounded uniformly in time when `G` is (`locBdd_dAlong`);
* unchanged by a symmetry of `G` compatible with `Φ` (`dAlong_congr`). -/

open AVRegularity.Providers.ComplexFlow

/-- **The derivative along the parameter maps** `∂_h G(Φ(x, h))|_{h=0}[w]`. -/
def dAlong {E : Type*} (Φ : E → CVec → E) (G : E → ℂ) (w : CVec) (x : E) : ℂ :=
  fderiv ℂ (fun h => G (Φ x h)) 0 w

section Along

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {Φ : E → CVec → E} {S : Set E} {ρ₀ : ℝ}

omit [FiniteDimensional ℂ E] in
/-- The domain where the parameter maps stay in `S`. -/
theorem isOpen_alongDom (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀)) :
    IsOpen ((S ×ˢ ball (0 : CVec) ρ₀) ∩ (fun q : E × CVec => Φ q.1 q.2) ⁻¹' S) :=
  hΦ.continuousOn.isOpen_inter_preimage (hS.prod isOpen_ball) hS

omit [FiniteDimensional ℂ E] in
/-- The offsets at a point where the parameter maps stay in `S`. -/
theorem isOpen_alongFib (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀)) {x : E}
    (hx : x ∈ S) : IsOpen (ball (0 : CVec) ρ₀ ∩ (fun h => Φ x h) ⁻¹' S) := by
  have hc : ContinuousOn (fun h => Φ x h) (ball (0 : CVec) ρ₀) :=
    (hΦ.comp ((differentiableOn_const x).prodMk differentiableOn_id)
      fun h hh => ⟨hx, hh⟩).continuousOn
  exact hc.isOpen_inter_preimage isOpen_ball hS

/-- **The derivative along the parameter maps is holomorphic.** -/
theorem differentiableOn_dAlong (hS : IsOpen S) (hρ : 0 < ρ₀)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀))
    (hΦ0 : ∀ x ∈ S, Φ x 0 = x) {G : E → ℂ} (hG : DifferentiableOn ℂ G S) (w : CVec) :
    DifferentiableOn ℂ (dAlong Φ G w) S := by
  set V := (S ×ˢ ball (0 : CVec) ρ₀) ∩ (fun q : E × CVec => Φ q.1 q.2) ⁻¹' S with hV
  have hVo : IsOpen V := isOpen_alongDom hS hΦ
  have hΨ : DifferentiableOn ℂ (fun q : E × CVec => G (Φ q.1 q.2)) V :=
    hG.comp (hΦ.mono fun q hq => hq.1) fun q hq => hq.2
  have hD := GenSem.differentiableOn_fderiv_apply hVo hΨ ((0 : E), w)
  have hmap : MapsTo (fun x : E => ((x, 0) : E × CVec)) S V := fun x hx =>
    ⟨⟨hx, mem_ball_self hρ⟩, by show Φ x 0 ∈ S; rw [hΦ0 x hx]; exact hx⟩
  refine (hD.comp (differentiableOn_id.prodMk (differentiableOn_const _)) hmap).congr
    fun x hx => ?_
  have hd : DifferentiableAt ℂ (fun q : E × CVec => G (Φ q.1 q.2)) (x, 0) :=
    (hΨ _ (hmap hx)).differentiableAt (hVo.mem_nhds (hmap hx))
  have hinr : HasFDerivAt (fun z : CVec => ((x, z) : E × CVec))
      (ContinuousLinearMap.inr ℂ E CVec) 0 :=
    (hasFDerivAt_const x 0).prodMk (hasFDerivAt_id 0)
  have hc : HasFDerivAt (fun h => G (Φ x h))
      ((fderiv ℂ (fun q : E × CVec => G (Φ q.1 q.2)) (x, 0)).comp
        (ContinuousLinearMap.inr ℂ E CVec)) 0 := by
    have := hd.hasFDerivAt
    exact this.comp 0 hinr
  show fderiv ℂ (fun h => G (Φ x h)) 0 w = fderiv ℂ (fun q : E × CVec => G (Φ q.1 q.2)) (x, 0) (0, w)
  rw [hc.fderiv]
  rfl

omit [FiniteDimensional ℂ E] in
/-- **The derivative along the parameter maps is measurable** in a parameter. -/
theorem measurable_dAlong {α : Type*} [MeasurableSpace α] (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀)) (hρ : 0 < ρ₀)
    (hΦ0 : ∀ x ∈ S, Φ x 0 = x) {G : α → E → ℂ} (hG : ∀ a, DifferentiableOn ℂ (G a) S)
    (hm : ∀ y ∈ S, Measurable fun a => G a y) {x : E} (hx : x ∈ S) (w : CVec) :
    Measurable fun a => dAlong Φ (G a) w x := by
  set U := ball (0 : CVec) ρ₀ ∩ (fun h => Φ x h) ⁻¹' S with hU
  have hUo : IsOpen U := isOpen_alongFib hS hΦ hx
  have hΦx : DifferentiableOn ℂ (fun h => Φ x h) U :=
    (hΦ.comp ((differentiableOn_const x).prodMk differentiableOn_id) fun h hh => ⟨hx, hh.1⟩).mono
      subset_rfl
  have h0 : (0 : CVec) ∈ U := ⟨mem_ball_self hρ, by show Φ x 0 ∈ S; rw [hΦ0 x hx]; exact hx⟩
  exact measurable_fderiv_apply_param (F := fun a h => G a (Φ x h)) hUo
    (fun a => (hG a).comp hΦx fun h hh => hh.2) (fun h hh => hm _ hh.2) h0 w

omit [FiniteDimensional ℂ E] in
/-- **Cauchy's bound for the derivative along the parameter maps.** -/
theorem norm_dAlong_le (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀))
    {G : E → ℂ} (hG : DifferentiableOn ℂ G S) {x : E} (hx : x ∈ S) {w : CVec} {r M : ℝ}
    (hr : 0 < r)
    (hball : ∀ ζ : ℂ, ‖ζ‖ ≤ r → ‖ζ • w‖ < ρ₀ ∧ Φ x (ζ • w) ∈ S ∧ ‖G (Φ x (ζ • w))‖ ≤ M) :
    ‖dAlong Φ G w x‖ ≤ M / r := by
  set U := ball (0 : CVec) ρ₀ ∩ (fun h => Φ x h) ⁻¹' S with hU
  have hUo : IsOpen U := isOpen_alongFib hS hΦ hx
  have hF : DifferentiableOn ℂ (fun h => G (Φ x h)) U :=
    hG.comp (hΦ.comp ((differentiableOn_const x).prodMk differentiableOn_id)
      fun h hh => ⟨hx, hh.1⟩) fun h hh => hh.2
  have hyU : ∀ ζ : ℂ, ‖ζ‖ ≤ r → (0 : CVec) + ζ • w ∈ U := fun ζ hζ => by
    rw [zero_add]
    exact ⟨mem_ball_zero_iff.mpr (hball ζ hζ).1, (hball ζ hζ).2.1⟩
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  unfold dAlong
  rw [fderiv_apply_eq_circle hUo hF hr hyU, norm_smul]
  have hbd : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      GenSem.cauchyKernel r θ • G (Φ x (0 + circleMap 0 r θ • w))‖ ≤
      r⁻¹ * M * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_cauchyKernel hr, zero_add]
    exact mul_le_mul_of_nonneg_left (hball _ (hcirc θ)).2.2 (by positivity)
  have h2pi : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [h2pi]
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_pos Real.two_pi_pos]
  field_simp

omit [FiniteDimensional ℂ E] in
/-- **The derivative along the parameter maps is unchanged by a compatible symmetry.** -/
theorem dAlong_congr (hS : IsOpen S) (hρ : 0 < ρ₀)
    (hΦ : DifferentiableOn ℂ (fun q : E × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀))
    (hΦ0 : ∀ x ∈ S, Φ x 0 = x) {G : E → ℂ} {τ : E → E} (hG : ∀ y ∈ S, G (τ y) = G y)
    (hτ : ∀ x h, Φ (τ x) h = τ (Φ x h)) {x : E} (hx : x ∈ S) (w : CVec) :
    dAlong Φ G w (τ x) = dAlong Φ G w x := by
  unfold dAlong
  have hU := isOpen_alongFib hS hΦ hx
  have h0 : (0 : CVec) ∈ ball (0 : CVec) ρ₀ ∩ (fun h => Φ x h) ⁻¹' S :=
    ⟨mem_ball_self hρ, by show Φ x 0 ∈ S; rw [hΦ0 x hx]; exact hx⟩
  have e : (fun h => G (Φ (τ x) h)) =ᶠ[𝓝 0] fun h => G (Φ x h) := by
    filter_upwards [hU.mem_nhds h0] with h hh
    rw [hτ]
    exact hG _ hh.2
  rw [e.fderiv_eq]

end Along

/-- **The derivative along the parameter maps is locally bounded uniformly in time.** -/
theorem locBdd_dAlong {n : ℕ} {Φ : ChainParamsC n → CVec → ChainParamsC n}
    {S : Set (ChainParamsC n)} {ρ₀ : ℝ} (hS : IsOpen S) (hρ : 0 < ρ₀)
    (hΦ : DifferentiableOn ℂ (fun q : ChainParamsC n × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀))
    (hΦ0 : ∀ x ∈ S, Φ x 0 = x) {G : ℝ → ChainParamsC n → ℂ} {T : Set ℝ} (hGb : LocBdd G T S)
    (hGd : ∀ t ∈ T, DifferentiableOn ℂ (G t) S) {w : CVec} (hw : ‖w‖ ≤ 1) :
    LocBdd (fun t => dAlong Φ (G t) w) T S := by
  intro x hx
  set V := (S ×ˢ ball (0 : CVec) ρ₀) ∩
    (fun q : ChainParamsC n × CVec => Φ q.1 q.2) ⁻¹' S with hV
  have hVo : IsOpen V := isOpen_alongDom hS hΦ
  have hxV : ((x, 0) : ChainParamsC n × CVec) ∈ V :=
    ⟨⟨hx, mem_ball_self hρ⟩, by show Φ x 0 ∈ S; rw [hΦ0 x hx]; exact hx⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo _ hxV
  have : ProperSpace (ChainParamsC n) := FiniteDimensional.proper ℂ _
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : closedBall x δ ×ˢ closedBall (0 : CVec) δ ⊆ V := by
    rintro ⟨y, h⟩ ⟨hy, hh⟩
    refine hεV ?_
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hy).trans_lt (by linarith),
      (mem_closedBall.mp hh).trans_lt (by linarith)⟩
  set K := (fun q : ChainParamsC n × CVec => Φ q.1 q.2) '' (closedBall x δ ×ˢ closedBall (0 : CVec) δ)
  have hKc : IsCompact K :=
    ((isCompact_closedBall x δ).prod (isCompact_closedBall _ δ)).image_of_continuousOn
      (hΦ.continuousOn.mono fun q hq => (hsub hq).1)
  have hKS : K ⊆ S := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hsub hq).2
  obtain ⟨M, hM⟩ := LocBdd.exists_bound hGb hKc hKS
  refine ⟨ball x δ, ball_mem_nhds x hδ0, M / δ, fun t ht y hy => ?_⟩
  have hy0 : ((y, 0) : ChainParamsC n × CVec) ∈ closedBall x δ ×ˢ closedBall (0 : CVec) δ :=
    ⟨mem_closedBall.mpr (mem_ball.mp hy).le, mem_closedBall_self hδ0.le⟩
  have hyS : y ∈ S := (hsub hy0).1.1
  refine norm_dAlong_le hS hΦ (hGd t ht) hyS hδ0 fun ζ hζ => ?_
  have hζw : ‖ζ • w‖ ≤ δ := by
    rw [norm_smul]
    calc ‖ζ‖ * ‖w‖ ≤ δ * 1 := mul_le_mul hζ hw (norm_nonneg _) hδ0.le
      _ = δ := mul_one δ
  have hq : ((y, ζ • w) : ChainParamsC n × CVec) ∈ closedBall x δ ×ˢ closedBall (0 : CVec) δ :=
    ⟨mem_closedBall.mpr (mem_ball.mp hy).le, mem_closedBall_zero_iff.mpr hζw⟩
  exact ⟨mem_ball_zero_iff.mp (hsub hq).1.2, (hsub hq).2, hM t ht _ ⟨_, hq, rfl⟩⟩

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the slow-label derivative of family expressions** (`dSlowFam`). The
extension of `∂_{h_j} c(t, 𝒜^{[h]})|_{h=0}` is the derivative along the complex recentering `recC`
at `h = 0` of the extension of `c` (`dSlowG`). The recentering is holomorphic, the identity at
`h = 0`, commutes with the phase translations and agrees with the real recentering, so the
derivative is holomorphic, measurable, symmetric, locally bounded and equal to the real one. For
`|h| ≤ b ε_{i-1} Δ/12` the recentering maps the carrier of reserve `𝗆` into that of reserve `𝗆 + Δ`,
so Cauchy's inequality gives the bound `(12/b)/(ε_{i-1}Δ) B(𝗆 + Δ)` (`FamInv.dSlow`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-! ### Facts on the recentering -/

theorem recC_zero (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ} (hdd : ChainOK D j₀ dd n)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) : recC D dd n x 0 = x := by
  cases n with
  | zero =>
    show ((x.1 + 0, x.2.1, x.2.2) : ChainParamsC 0) = x
    rw [add_zero]
  | succ m =>
    have h0 : recShift D dd m x 0 = 0 := by
      unfold recShift
      rw [add_zero, parent_fl_lastChild_ctr env hdd hx, sub_self]
    show ((x.1, Function.update x.2.1 (Fin.last m)
      ((x.2.1 (Fin.last m)).1 + recShift D dd m x 0,
        (x.2.1 (Fin.last m)).2 + epsInvC D (dd.baseLevel + m + 1) • recShift D dd m x 0), x.2.2) :
          ChainParamsC (m + 1)) = x
    rw [h0, add_zero, smul_zero, add_zero, Function.update_eq_self]

theorem recenter_data (ch : RealChain) (h : Vec 2) : (ch.recenter D h).data = ch.data := by
  cases hc : ch.children.getLast? <;> simp only [RealChain.recenter, hc] <;> rfl

theorem recenter_length (ch : RealChain) (h : Vec 2) :
    (ch.recenter D h).children.length = ch.children.length := by
  cases hc : ch.children.getLast? with
  | none => simp only [RealChain.recenter, hc]
  | some c =>
    have hne : ch.children ≠ [] := by
      intro h'
      rw [h'] at hc
      simp at hc
    have := List.length_pos_of_ne_nil hne
    simp only [RealChain.recenter, hc, List.length_append, List.length_dropLast,
      List.length_singleton]
    omega

theorem AdmData.goodData {dd : ChainData} {n : ℕ} (h : AdmData D b j₀ i p dd n) :
    GoodData D j₀ i p dd n := by
  obtain ⟨ch, hch, rfl, rfl⟩ := h
  exact ⟨chainOK_of_admissible hch, hch.2.2.2.1, hch.1⟩

/-- **The extension at a real recentering is the real function.** -/
theorem ext_recenter_eq (env : ChainEnv D b CH Υ j₀) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {G : Ext} {t : ℝ} {ζ : Vec 2} {g : RealChain → ℂ}
    (hG : ∀ ch', IsAdmissibleChain D b j₀ i p ch' →
      G ch'.data ch'.children.length t (ch'.paramsC ζ) = g ch') :
    ∀ᶠ h in 𝓝 (0 : Vec 2), g (ch.recenter D h) =
      G ch.data ch.children.length t (recC D ch.data ch.children.length (ch.paramsC ζ) (ofRealVec h)) := by
  filter_upwards [recenter_admissible env hch] with h hadm
  have hl := recenter_length (D := D) ch h
  have hP : (ch.recenter D h).paramsN ch.children.length hl ζ =
      recC D ch.data ch.children.length (ch.paramsC ζ) (ofRealVec h) :=
    (recC_real env hch rfl ζ h hl).symm
  exact (paramsC_transport (ch.recenter D h) ch.data ch.children.length (recenter_data ch h) hl _ ζ hP
    (fun dd n P => G dd n t P = g (ch.recenter D h)) (hG _ hadm)).symm

/-! ### The slow-label derivative of family expressions -/

open scoped Classical in
/-- **The extension of the slow-label derivative.** -/
def dSlowG (D : OCData) (j₀ i : ℕ) (p : ℤ) (j : Fin 2) (G : Ext) : Ext :=
  fun dd n t x => if GoodData D j₀ i p dd n then dAlong (recC D dd n) (G dd n t) (cbasis j) x
    else 0

theorem dSlowG_of {j : Fin 2} {G : Ext} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : GoodData D j₀ i p dd n) :
    dSlowG D j₀ i p j G dd n t x = dAlong (recC D dd n) (G dd n t) (cbasis j) x := by
  simp only [dSlowG, hg, ↓reduceIte]

theorem dSlowG_of_not {j : Fin 2} {G : Ext} {dd : ChainData} {n : ℕ} {t : ℝ} {x : ChainParamsC n}
    (hg : ¬GoodData D j₀ i p dd n) : dSlowG D j₀ i p j G dd n t x = 0 := by
  simp only [dSlowG, hg, ↓reduceIte]

/-- The facts on the recentering used by the derivatives, for good data. -/
theorem recC_facts (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) :
    0 < b * D.eps (dd.baseLevel + n) ∧
      DifferentiableOn ℂ (fun q : ChainParamsC n × CVec => recC D dd n q.1 q.2)
        (carrierC D b dd n 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + n))) ∧
      ∀ x ∈ carrierC D b dd n 2, recC D dd n x 0 = x :=
  ⟨mul_pos env.hb0 (Construction.Stream.ocEpsilon_pos env.hΛ1), differentiableOn_recC env hg.1,
    fun _ hx => recC_zero env hg.1 hx⟩

/-- **Cauchy's bound on a nested carrier.** -/
theorem norm_dAlong_recC_le (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {n : ℕ}
    (hg : GoodData D j₀ i p dd n) {G : ChainParamsC n → ℂ}
    (hG : DifferentiableOn ℂ G (carrierC D b dd n 2)) {mres Δ : ℝ} (hm0 : 0 ≤ mres)
    (hΔ : 0 < Δ) (hmΔ : mres + Δ ≤ 2) {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    {M : ℝ} (hM : ∀ y ∈ carrierC D b dd n (mres + Δ), ‖G y‖ ≤ M) (j : Fin 2) :
    ‖dAlong (recC D dd n) G (cbasis j) x‖ ≤ M / (b * D.eps (dd.baseLevel + n) * Δ / 12) := by
  obtain ⟨hρ, hΦ, -⟩ := recC_facts env hg
  have hx2 : x ∈ carrierC D b dd n 2 := carrierC_mono env.hb0.le (by linarith) hx
  have hr : 0 < b * D.eps (dd.baseLevel + n) * Δ / 12 := by positivity
  refine norm_dAlong_le (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ hG hx2 hr fun ζ hζ => ?_
  have hζw : ‖ζ • cbasis j‖ = ‖ζ‖ := by rw [norm_smul, norm_cbasis, mul_one]
  have hmem := recC_mem env hg.1 hm0 hΔ hmΔ hx (h := ζ • cbasis j) (by rw [hζw]; exact hζ)
  refine ⟨?_, carrierC_mono env.hb0.le hmΔ hmem, hM _ hmem⟩
  rw [hζw]
  calc ‖ζ‖ ≤ b * D.eps (dd.baseLevel + n) * Δ / 12 := hζ
    _ < b * D.eps (dd.baseLevel + n) := by nlinarith

/-- The Cauchy bound as a derivative cost. -/
theorem enorm_le_derivCost {C : ℝ≥0∞} {b ε Δ mres a : ℝ} (hb : 0 < b) (hε : 0 < ε) (hΔ : 0 < Δ)
    (hC : ENNReal.ofReal (12 / b) ≤ C) {B : ℝ≥0∞} (hmΔ : mres + Δ ≤ 2)
    (ha : a ≤ B.toReal / (b * ε * Δ / 12)) (hB : B ≠ ⊤) :
    ENNReal.ofReal a ≤ derivCost C ε Δ mres B := by
  simp only [derivCost, hmΔ, ↓reduceIte]
  have e : B.toReal / (b * ε * Δ / 12) = 12 / b / (ε * Δ) * B.toReal := by
    field_simp
  rw [e] at ha
  refine (ENNReal.ofReal_le_ofReal ha).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hB,
    ENNReal.ofReal_div_of_pos (by positivity)]
  gcongr

/-- **The slow-label derivative of a family expression.** -/
theorem FamInv.dSlow (env : ChainEnv D b CH Υ j₀) {Δ : ℝ} (hΔ : 0 < Δ) {C : ℝ≥0∞}
    (hC : ENNReal.ofReal (12 / b) ≤ C) (j : Fin 2) {fc : GenSort.Sem .fam} {G : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : FamInv D b j₀ i p fc G B) :
    FamInv D b j₀ i p (fun t ch => fderiv ℝ (fun h : Vec 2 => fc t (ch.recenter D h)) 0 (basisVec j))
      (dSlowG D j₀ i p j G) (fun mres h t => derivCost C (D.eps (i - 1)) Δ mres (B (mres + Δ) h t)) where
  hol dd n t ht := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      exact (differentiableOn_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (hF.hol dd n t ht) (cbasis j)).congr fun x _ => dSlowG_of hg
    · have : dSlowG D j₀ i p j G dd n t = fun _ => 0 := funext fun _ => dSlowG_of_not hg
      rw [this]
      exact differentiableOn_const 0
  meas dd n x hx := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      have h1 := measurable_dAlong (G := fun t : ocPulseWindow D.α D.q D.Λ i p => G dd n t)
        (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ hρ hΦ0 (fun t => hF.hol dd n t t.2)
        (fun y hy => hF.meas dd n y hy) hx (cbasis j)
      convert h1 using 1
      funext t
      exact dSlowG_of hg
    · convert measurable_const (a := (0 : ℂ)) using 1
      funext t
      exact dSlowG_of_not hg
  indep dd n t x z := by
    by_cases hg : GoodData D j₀ i p dd n
    · rw [dSlowG_of hg, dSlowG_of hg]
      have e : (fun h => G dd n t (recC D dd n (x.1, x.2.1, z) h)) =
          fun h => G dd n t (recC D dd n x h) := funext fun h => by rw [recC_final, hF.indep]
      unfold dAlong
      rw [e]
    · rw [dSlowG_of_not hg, dSlowG_of_not hg]
  agree ch t ht hch := by
    have hdd := chainOK_of_admissible hch
    have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
    obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
    have hx := GenSem.paramsC_mem_carrierC env.hΛ1 env.hb0 hch 0
    rw [dSlowG_of hg]
    have hev := ext_recenter_eq env hch (G := G) (t := t) (ζ := 0)
      (g := fun ch' => ((fc t ch' : ℝ) : ℂ)) fun ch' hch' => hF.agree ch' t ht hch'
    set U := ball (0 : CVec) (b * D.eps (ch.data.baseLevel + ch.children.length)) ∩
      (fun h => recC D ch.data ch.children.length (ch.paramsC 0) h) ⁻¹'
        carrierC D b ch.data ch.children.length 2 with hU
    have hUo : IsOpen U := isOpen_alongFib (ComplexFlow.isOpen_carrierC _ _ _ _ _) hΦ hx
    have h0 : (0 : CVec) ∈ U := ⟨mem_ball_self hρ, by
      show recC D ch.data ch.children.length (ch.paramsC 0) 0 ∈
        carrierC D b ch.data ch.children.length 2
      rw [hΦ0 _ hx]; exact hx⟩
    have hGd : DifferentiableAt ℂ
        (fun w => G ch.data ch.children.length t (recC D ch.data ch.children.length (ch.paramsC 0) w))
        (ofRealVec 0) := by
      have e : ofRealVec (0 : Vec 2) = 0 := by funext a; simp [ofRealVec]
      rw [e]
      refine (((hF.hol _ _ t ht).comp (hΦ.comp ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w hw => ⟨hx, hw.1⟩) fun w hw => hw.2) 0 h0).differentiableAt (hUo.mem_nhds h0)
    have h1 := ofReal_fderiv_eq_of_hol (ι := ofRealVec) ofRealVecCLM.hasFDerivAt hGd hev (basisVec j)
    rw [h1]
    have e : ofRealVec (0 : Vec 2) = 0 := by funext a; simp [ofRealVec]
    rw [e]
    show _ = fderiv ℂ _ 0 (ofRealVec (basisVec j))
    rw [ofRealVec_basisVec]
    rfl
  child dd n t ht x hx k v hv := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      rw [dSlowG_of hg, dSlowG_of hg]
      exact dAlong_congr (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (τ := fun y => y.shiftChild k v) (fun y hy => hF.child dd n t ht y hy k v hv)
        (fun x' h => recC_shiftChild env.hΛ1 hg.1 x' k hv h) hx (cbasis j)
    · rw [dSlowG_of_not hg, dSlowG_of_not hg]
  bdd dd n := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      have h1 := locBdd_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0 (hF.bdd dd n)
        (hF.hol dd n) (w := cbasis j) (by rw [norm_cbasis])
      intro x hx
      obtain ⟨U, hU, M, hM⟩ := h1 x hx
      exact ⟨U, hU, M, fun t ht y hy => by rw [dSlowG_of hg]; exact hM t ht y hy⟩
    · exact fun _ _ => ⟨univ, univ_mem, 0, fun t _ y _ => by rw [dSlowG_of_not hg, norm_zero]⟩
  mode mres hm0 hm2 t ht dd n hdd x hx := by
    have hg := hdd.goodData
    by_cases hmΔ : mres + Δ ≤ 2
    · by_cases htop : B (mres + Δ) 0 t = ⊤
      · simp only [derivCost, hmΔ, ↓reduceIte]
        rw [htop, ENNReal.mul_top]
        · exact le_top
        · exact ENNReal.div_ne_zero.mpr ⟨(lt_of_lt_of_le (ENNReal.ofReal_pos.mpr
            (by have := env.hb0; positivity)) hC).ne', ENNReal.ofReal_ne_top⟩
      have hM : ∀ y ∈ carrierC D b dd n (mres + Δ), ‖G dd n t y‖ ≤ (B (mres + Δ) 0 t).toReal := by
        intro y hy
        have h1 := hF.mode (mres + Δ) (by linarith) hmΔ t ht dd n hdd y hy
        rw [← ofReal_norm] at h1
        exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
      have hb := norm_dAlong_recC_le env hg (hF.hol dd n t ht) hm0 hΔ hmΔ hx hM j
      have hi : dd.baseLevel + n = i - 1 := by have := hg.2.2; omega
      rw [hi] at hb
      rw [dSlowG_of hg, ← ofReal_norm]
      exact enorm_le_derivCost env.hb0 (Construction.Stream.ocEpsilon_pos env.hΛ1) hΔ hC hmΔ hb htop
    · simp only [derivCost, hmΔ, ↓reduceIte]
      exact le_top

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization Complex
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the slow-label derivative of cell expressions** (`dSlowCell`). Each mode of
the phase series is differentiated along the complex recentering (`dSlowW`). The modes keep their
exponential decay, locally uniformly (Cauchy on compact neighborhoods, `decay_exists_bound`), the
phase series of the derivatives converges to the real derivative of the cell function by
termwise differentiation (`hasFDerivAt_tsum_of_isPreconnected`), and each mode has the Cauchy
bound of the nested carriers (`CellInv.dSlow`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

variable {D : OCData} {b CH Υ : ℝ} {j₀ i : ℕ} {p : ℤ}

/-! ### Cauchy tools -/

/-- **Uniform exponential decay on compact sets** from local uniform decay. -/
theorem decay_exists_bound {n : ℕ} {W : ℤ → ℝ → ChainParamsC n → ℂ} {T : Set ℝ}
    {S : Set (ChainParamsC n)}
    (hW : ∀ x ∈ S, ∃ U ∈ 𝓝 x, ∃ M w : ℝ, 0 < w ∧ ∀ (k : ℤ), ∀ t ∈ T, ∀ y ∈ U,
      ‖W k t y‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(k : ℝ)|)))
    {K : Set (ChainParamsC n)} (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ M w : ℝ, 0 < w ∧ ∀ (k : ℤ), ∀ t ∈ T, ∀ y ∈ K,
      ‖W k t y‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(k : ℝ)|)) := by
  choose U hU M w hw hM using fun x (hx : x ∈ K) => hW x (hKS hx)
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' U hU
  rcases s.eq_empty_or_nonempty with hse | hne
  · refine ⟨0, 1, one_pos, fun k t _ y hy => ?_⟩
    have := hs hy
    rw [hse] at this
    simp at this
  · set w₀ := s.inf' hne fun x => w x.1 x.2 with hw₀
    have hw₀pos : 0 < w₀ := by
      rw [hw₀, Finset.lt_inf'_iff]
      exact fun x _ => hw x.1 x.2
    refine ⟨∑ x ∈ s, |M x.1 x.2|, w₀, hw₀pos, fun k t ht y hy => ?_⟩
    obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs hy)
    have h1 := hM x.1 x.2 k t ht y hyx
    have h2 : w₀ ≤ w x.1 x.2 := Finset.inf'_le _ hxs
    have h3 := exp_rate_le h2 k
    have h4 : |M x.1 x.2| ≤ ∑ x ∈ s, |M x.1 x.2| :=
      Finset.single_le_sum (f := fun x => |M x.1 x.2|) (fun _ _ => abs_nonneg _) hxs
    have he : 0 ≤ Real.exp (-(2 * Real.pi * w x.1 x.2 * |(k : ℝ)|)) := (Real.exp_pos _).le
    calc ‖W k t y‖ ≤ M x.1 x.2 * Real.exp (-(2 * Real.pi * w x.1 x.2 * |(k : ℝ)|)) := h1
      _ ≤ |M x.1 x.2| * Real.exp (-(2 * Real.pi * w x.1 x.2 * |(k : ℝ)|)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) he
      _ ≤ (∑ x ∈ s, |M x.1 x.2|) * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|)) :=
          mul_le_mul h4 h3 he ((Finset.sum_nonneg fun _ _ => abs_nonneg _))

/-- **A compact neighborhood for Cauchy's estimates along the parameter maps.** -/
theorem exists_cauchy_nbhd {n : ℕ} {Φ : ChainParamsC n → CVec → ChainParamsC n}
    {S : Set (ChainParamsC n)} {ρ₀ : ℝ} (hS : IsOpen S) (hρ : 0 < ρ₀)
    (hΦ : DifferentiableOn ℂ (fun q : ChainParamsC n × CVec => Φ q.1 q.2) (S ×ˢ ball 0 ρ₀))
    (hΦ0 : ∀ x ∈ S, Φ x 0 = x) {x : ChainParamsC n} (hx : x ∈ S) :
    ∃ δ > 0, ∃ K, IsCompact K ∧ K ⊆ S ∧ ∀ y ∈ ball x δ, y ∈ S ∧
      ∀ h : CVec, ‖h‖ ≤ δ → ‖h‖ < ρ₀ ∧ Φ y h ∈ K := by
  set V := (S ×ˢ ball (0 : CVec) ρ₀) ∩
    (fun q : ChainParamsC n × CVec => Φ q.1 q.2) ⁻¹' S with hV
  have hVo : IsOpen V := isOpen_alongDom hS hΦ
  have hxV : ((x, 0) : ChainParamsC n × CVec) ∈ V :=
    ⟨⟨hx, mem_ball_self hρ⟩, by show Φ x 0 ∈ S; rw [hΦ0 x hx]; exact hx⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo _ hxV
  have : ProperSpace (ChainParamsC n) := FiniteDimensional.proper ℂ _
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : closedBall x δ ×ˢ closedBall (0 : CVec) δ ⊆ V := by
    rintro ⟨y, h⟩ ⟨hy, hh⟩
    refine hεV ?_
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hy).trans_lt (by linarith),
      (mem_closedBall.mp hh).trans_lt (by linarith)⟩
  set K := (fun q : ChainParamsC n × CVec => Φ q.1 q.2) ''
    (closedBall x δ ×ˢ closedBall (0 : CVec) δ) with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall x δ).prod (isCompact_closedBall _ δ)).image_of_continuousOn
      (hΦ.continuousOn.mono fun q hq => (hsub hq).1)
  have hKS : K ⊆ S := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hsub hq).2
  refine ⟨δ, hδ0, K, hKc, hKS, fun y hy => ?_⟩
  have hy0 : ((y, 0) : ChainParamsC n × CVec) ∈ closedBall x δ ×ˢ closedBall (0 : CVec) δ :=
    ⟨mem_closedBall.mpr (mem_ball.mp hy).le, mem_closedBall_self hδ0.le⟩
  refine ⟨(hsub hy0).1.1, fun h hh => ?_⟩
  have hq : ((y, h) : ChainParamsC n × CVec) ∈ closedBall x δ ×ˢ closedBall (0 : CVec) δ :=
    ⟨mem_closedBall.mpr (mem_ball.mp hy).le, mem_closedBall_zero_iff.mpr hh⟩
  exact ⟨mem_ball_zero_iff.mp (hsub hq).1.2, ⟨_, hq, rfl⟩⟩

/-- **Cauchy's bound for a directional derivative** on a disc. -/
theorem norm_fderiv_apply_le_of_disc {U : Set CVec} (hU : IsOpen U) {F : CVec → ℂ}
    (hF : DifferentiableOn ℂ F U) {y v : CVec} {r M : ℝ} (hr : 0 < r)
    (hd : ∀ ζ : ℂ, ‖ζ‖ ≤ r → y + ζ • v ∈ U ∧ ‖F (y + ζ • v)‖ ≤ M) :
    ‖fderiv ℂ F y v‖ ≤ M / r := by
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 r θ‖ ≤ r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  rw [fderiv_apply_eq_circle hU hF hr (fun ζ hζ => (hd ζ hζ).1), norm_smul]
  have hbd : ‖∫ θ in (0 : ℝ)..2 * Real.pi,
      GenSem.cauchyKernel r θ • F (y + circleMap 0 r θ • v)‖ ≤ r⁻¹ * M * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_cauchyKernel hr]
    exact mul_le_mul_of_nonneg_left (hd _ (hcirc θ)).2 (by positivity)
  have h2pi : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [h2pi]
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_pos Real.two_pi_pos]
  field_simp

/-! ### The slow-label derivative of cell expressions -/

open scoped Classical in
/-- **The extensions of the modes of the slow-label derivative.** -/
def dSlowW (D : OCData) (j₀ i : ℕ) (p : ℤ) (j : Fin 2) (W : ℤ → Ext) : ℤ → Ext :=
  fun k => dSlowG D j₀ i p j (W k)

/-- **The slow-label derivative of a cell expression.** -/
theorem CellInv.dSlow (env : ChainEnv D b CH Υ j₀) {Δ : ℝ} (hΔ : 0 < Δ) {C : ℝ≥0∞}
    (hC : ENNReal.ofReal (12 / b) ≤ C) (j : Fin 2) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CellInv D b j₀ i p fw W B) :
    CellInv D b j₀ i p
      (fun t ch η => fderiv ℝ (fun h : Vec 2 => fw t (ch.recenter D h) η) 0 (basisVec j))
      (dSlowW D j₀ i p j W)
      (fun mres h t => derivCost C (D.eps (i - 1)) Δ mres (B (mres + Δ) h t)) where
  hol k dd n t ht := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      exact (differentiableOn_dAlong (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (hF.hol k dd n t ht) (cbasis j)).congr fun x _ => dSlowG_of hg
    · have : dSlowW D j₀ i p j W k dd n t = fun _ => 0 := funext fun _ => dSlowG_of_not hg
      rw [this]
      exact differentiableOn_const 0
  meas k dd n x hx := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      have h1 := measurable_dAlong (G := fun t : ocPulseWindow D.α D.q D.Λ i p => W k dd n t)
        (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ hρ hΦ0 (fun t => hF.hol k dd n t t.2)
        (fun y hy => hF.meas k dd n y hy) hx (cbasis j)
      convert h1 using 1
      funext t
      exact dSlowG_of hg
    · convert measurable_const (a := (0 : ℂ)) using 1
      funext t
      exact dSlowG_of_not hg
  indep k dd n t x z := by
    by_cases hg : GoodData D j₀ i p dd n
    · show dSlowG D j₀ i p j (W k) dd n t (x.1, x.2.1, z) = dSlowG D j₀ i p j (W k) dd n t x
      rw [dSlowG_of hg, dSlowG_of hg]
      have e : (fun h => W k dd n t (recC D dd n (x.1, x.2.1, z) h)) =
          fun h => W k dd n t (recC D dd n x h) := funext fun h => by rw [recC_final, hF.indep]
      unfold dAlong
      rw [e]
    · show dSlowG D j₀ i p j (W k) dd n t (x.1, x.2.1, z) = dSlowG D j₀ i p j (W k) dd n t x
      rw [dSlowG_of_not hg, dSlowG_of_not hg]
  agree ch t ht hch η := by
    have hdd := chainOK_of_admissible hch
    have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
    obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
    set n := ch.children.length with hn
    set x0 := ch.paramsC 0 with hx0def
    have hx0 : x0 ∈ carrierC D b ch.data n 2 := GenSem.paramsC_mem_carrierC env.hΛ1 env.hb0 hch 0
    set e : ℤ → ℂ := fun k => emode k (η (transverseIndex p)) with hedef
    have hen : ∀ k, ‖e k‖ = 1 := fun k => norm_emode _ _
    set Ψ : ℤ → CVec → ℂ := fun k w => W k ch.data n t (recC D ch.data n x0 w) with hΨ
    -- the good offsets
    set U0 := ball (0 : CVec) (b * D.eps (ch.data.baseLevel + n)) ∩
      (fun w => recC D ch.data n x0 w) ⁻¹' carrierC D b ch.data n 2 with hU0
    have hU0o : IsOpen U0 := isOpen_alongFib (ComplexFlow.isOpen_carrierC _ _ _ _ _) hΦ hx0
    have h0 : (0 : CVec) ∈ U0 := ⟨mem_ball_self hρ, by
      show recC D ch.data n x0 0 ∈ carrierC D b ch.data n 2
      rw [hΦ0 _ hx0]; exact hx0⟩
    have hΨd : ∀ k, DifferentiableOn ℂ (Ψ k) U0 := fun k =>
      (hF.hol k _ _ t ht).comp (hΦ.comp ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w hw => ⟨hx0, hw.1⟩) fun w hw => hw.2
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU0o 0 h0
    set r' := r / 3 with hr'
    have hr'0 : 0 < r' := by positivity
    have hsub : closedBall (0 : CVec) (2 * r') ⊆ U0 := fun w hw =>
      hrU (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (by linarith)))
    have : ProperSpace CVec := FiniteDimensional.proper ℂ _
    set K := (fun w => recC D ch.data n x0 w) '' closedBall (0 : CVec) (2 * r') with hK
    have hKc : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
      ((hΦ.comp ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w hw => ⟨hx0, (hsub hw).1⟩).continuousOn)
    have hKS : K ⊆ carrierC D b ch.data n 2 := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hsub hw).2
    obtain ⟨M, w₀, hw₀, hM⟩ := decay_exists_bound
      (fun x hx => hF.decay ch.data n x hx) hKc hKS
    set u : ℤ → ℝ := fun k => M * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|)) / r' with hu
    have hus : Summable u := (summable_exp_rate hw₀ M).div_const r'
    -- the derivative bounds on the small ball
    have hΨb : ∀ k, ∀ w ∈ ball (0 : CVec) r', ‖fderiv ℂ (Ψ k) w‖ ≤ u k := by
      intro k w hw
      have hC0 : 0 ≤ u k := by
        have := hF.decay ch.data n x0 hx0
        have h1 : 0 ≤ M * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|)) :=
          (norm_nonneg _).trans (hM k t ht _ ⟨0, mem_closedBall_self (by positivity), rfl⟩)
        positivity
      refine ContinuousLinearMap.opNorm_le_of_unit_norm hC0 fun v hv => ?_
      refine norm_fderiv_apply_le_of_disc hU0o (hΨd k) hr'0 fun ζ hζ => ?_
      have hm : w + ζ • v ∈ closedBall (0 : CVec) (2 * r') := by
        rw [mem_closedBall, dist_zero_right]
        calc ‖w + ζ • v‖ ≤ ‖w‖ + ‖ζ‖ * ‖v‖ := by rw [← norm_smul]; exact norm_add_le _ _
          _ ≤ r' + r' * 1 := add_le_add (mem_ball_zero_iff.mp hw).le
              (mul_le_mul hζ hv.le (norm_nonneg _) hr'0.le)
          _ = 2 * r' := by ring
      exact ⟨hsub hm, hM k t ht _ ⟨_, hm, rfl⟩⟩
    have hΨD : ∀ k, ∀ w ∈ ball (0 : CVec) r', HasFDerivAt (fun w => Ψ k w * e k)
        (e k • fderiv ℂ (Ψ k) w) w := by
      intro k w hw
      have hw' : w ∈ U0 := hsub (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith)) hw)
      exact ((hΨd k w hw').differentiableAt (hU0o.mem_nhds hw')).hasFDerivAt.mul_const (e k)
    have hsum0 : Summable fun k => Ψ k 0 * e k := by
      refine (summable_exp_rate hw₀ M).of_norm_bounded fun k => ?_
      rw [norm_mul, hen, mul_one]
      exact hM k t ht _ ⟨0, mem_closedBall_self (by positivity), rfl⟩
    have hS := hasFDerivAt_tsum_of_isPreconnected hus isOpen_ball (convex_ball _ _).isPreconnected
      (fun k w hw => hΨD k w hw) (fun k w hw => by
        rw [norm_smul, hen, one_mul]; exact hΨb k w hw) (mem_ball_self hr'0) hsum0
      (mem_ball_self hr'0)
    -- the real cell function along real recenterings
    have hev : ∀ᶠ h' in 𝓝 (0 : Vec 2), ((fw t (ch.recenter D h') η : ℝ) : ℂ) =
        (fun w => ∑' k, Ψ k w * e k) (ofRealVec h') := by
      filter_upwards [recenter_admissible env hch] with h' hadm
      have hl := recenter_length (D := D) ch h'
      have hP : (ch.recenter D h').paramsN n hl 0 = recC D ch.data n x0 (ofRealVec h') :=
        (recC_real env hch rfl 0 h' hl).symm
      have hQ := paramsC_transport (ch.recenter D h') ch.data n (recenter_data ch h') hl _ 0 hP
        (fun dd m P => HasSum (fun k => W k dd m t P * e k) ((fw t (ch.recenter D h') η : ℝ) : ℂ))
        (hF.agree _ t ht hadm η)
      exact hQ.tsum_eq.symm
    have e0 : ofRealVec (0 : Vec 2) = 0 := by funext a; simp [ofRealVec]
    have hSd : DifferentiableAt ℂ (fun w => ∑' k, Ψ k w * e k) (ofRealVec 0) := by
      rw [e0]; exact hS.differentiableAt
    have h1 := ofReal_fderiv_eq_of_hol (ι := ofRealVec) ofRealVecCLM.hasFDerivAt hSd hev
      (basisVec j)
    show HasSum (fun k => dSlowG D j₀ i p j (W k) ch.data n t x0 * e k) _
    rw [h1, e0, hS.fderiv]
    show HasSum _ ((∑' k, e k • fderiv ℂ (Ψ k) 0) (ofRealVec (basisVec j)))
    have hsumL : Summable fun k => e k • fderiv ℂ (Ψ k) 0 :=
      hus.of_norm_bounded fun k => by
        rw [norm_smul, hen, one_mul]; exact hΨb k 0 (mem_ball_self hr'0)
    have hmap := (ContinuousLinearMap.apply ℂ ℂ (cbasis j)).map_tsum hsumL
    simp only [ContinuousLinearMap.apply_apply] at hmap
    rw [ofRealVec_basisVec, hmap]
    have hterm : (fun k => dSlowG D j₀ i p j (W k) ch.data n t x0 * e k) =
        fun k => (e k • fderiv ℂ (Ψ k) 0) (cbasis j) := by
      funext k
      rw [dSlowG_of hg, smul_apply, smul_eq_mul, mul_comm]
      rfl
    rw [hterm]
    exact (hsumL.mapL (ContinuousLinearMap.apply ℂ ℂ (cbasis j))).hasSum
  child k dd n t ht x hx kk v hv := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      show dSlowG D j₀ i p j (W k) dd n t (x.shiftChild kk v) = dSlowG D j₀ i p j (W k) dd n t x
      rw [dSlowG_of hg, dSlowG_of hg]
      exact dAlong_congr (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0
        (τ := fun y => y.shiftChild kk v) (fun y hy => hF.child k dd n t ht y hy kk v hv)
        (fun x' h => recC_shiftChild env.hΛ1 hg.1 x' kk hv h) hx (cbasis j)
    · show dSlowG D j₀ i p j (W k) dd n t (x.shiftChild kk v) = dSlowG D j₀ i p j (W k) dd n t x
      rw [dSlowG_of_not hg, dSlowG_of_not hg]
  decay dd n x hx := by
    by_cases hg : GoodData D j₀ i p dd n
    · obtain ⟨hρ, hΦ, hΦ0⟩ := recC_facts env hg
      obtain ⟨δ, hδ, K, hKc, hKS, hK⟩ := exists_cauchy_nbhd
        (ComplexFlow.isOpen_carrierC D b dd n 2) hρ hΦ hΦ0 hx
      obtain ⟨M, w₀, hw₀, hM⟩ := decay_exists_bound (fun x hx => hF.decay dd n x hx) hKc hKS
      refine ⟨ball x δ, ball_mem_nhds x hδ, M / δ, w₀, hw₀, fun k t ht y hy => ?_⟩
      show ‖dSlowG D j₀ i p j (W k) dd n t y‖ ≤ _
      rw [dSlowG_of hg]
      obtain ⟨hyS, hyK⟩ := hK y hy
      have h1 := norm_dAlong_le (ComplexFlow.isOpen_carrierC D b dd n 2) hΦ (hF.hol k dd n t ht)
        hyS hδ (M := M * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|))) fun ζ hζ => by
          have hζw : ‖ζ • cbasis j‖ ≤ δ := by rw [norm_smul, norm_cbasis, mul_one]; exact hζ
          exact ⟨(hyK _ hζw).1, hKS (hyK _ hζw).2, hM k t ht _ (hyK _ hζw).2⟩
      calc _ ≤ M * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|)) / δ := h1
        _ = M / δ * Real.exp (-(2 * Real.pi * w₀ * |(k : ℝ)|)) := by ring
    · refine ⟨univ, univ_mem, 0, 1, one_pos, fun k t _ y _ => ?_⟩
      show ‖dSlowG D j₀ i p j (W k) dd n t y‖ ≤ _
      rw [dSlowG_of_not hg, norm_zero]
      simp
  mode mres hm0 hm2 k t ht dd n hdd x hx := by
    have hg := hdd.goodData
    by_cases hmΔ : mres + Δ ≤ 2
    · by_cases htop : B (mres + Δ) k t = ⊤
      · simp only [derivCost, hmΔ, ↓reduceIte]
        rw [htop, ENNReal.mul_top]
        · exact le_top
        · exact ENNReal.div_ne_zero.mpr ⟨(lt_of_lt_of_le (ENNReal.ofReal_pos.mpr
            (by have := env.hb0; positivity)) hC).ne', ENNReal.ofReal_ne_top⟩
      have hM : ∀ y ∈ carrierC D b dd n (mres + Δ), ‖W k dd n t y‖ ≤ (B (mres + Δ) k t).toReal := by
        intro y hy
        have h1 := hF.mode (mres + Δ) (by linarith) hmΔ k t ht dd n hdd y hy
        rw [← ofReal_norm] at h1
        exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h1
      have hb := norm_dAlong_recC_le env hg (hF.hol k dd n t ht) hm0 hΔ hmΔ hx hM j
      have hi : dd.baseLevel + n = i - 1 := by have := hg.2.2; omega
      rw [hi] at hb
      show ‖dSlowG D j₀ i p j (W k) dd n t x‖ₑ ≤ _
      rw [dSlowG_of hg, ← ofReal_norm]
      exact enorm_le_derivCost env.hb0 (Construction.Stream.ocEpsilon_pos env.hΛ1) hΔ hC hmΔ hb htop
    · simp only [derivCost, hmΔ, ↓reduceIte]
      exact le_top

end AVRegularity.Providers.ComplexContext
end
