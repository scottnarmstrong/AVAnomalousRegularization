-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexChain.VelChild
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.Proofs.ComplexChain.VelChain
public import AVRegularity.Proofs.ComplexContext.Inv
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.ComplexContext.Leaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: derivatives of holomorphic extensions.**
* `ofReal_fderiv_eq_of_hol`: if a real function agrees near a point with a holomorphic function
  composed with a real-differentiable parameter map, its real derivative is the complex derivative
  applied to the derivative of the map (the derivative clauses of `Gen.Denotes`);
* `measurable_fderiv_apply_param`: the directional derivative of a family that is holomorphic in
  the parameters and measurable in time is measurable in time;
* `LocBdd.fderiv_apply`: local bounds uniform in time pass to directional derivatives (Cauchy);
* `fderiv_add_const_eq`: the derivative of a function invariant under a translation is invariant;
  the phase translations are translations (`shiftFinal_eq_add`, `shiftChild_eq_add`). -/

section
open AVRegularity.Providers.ComplexFlow

/-- **The real derivative of the restriction of a holomorphic function.** -/
theorem ofReal_fderiv_eq_of_hol {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ} {ι : V → E} {ι' : V →L[ℝ] E}
    {f : V → ℝ} {ζ : V} (hι : HasFDerivAt ι ι' ζ) (hG : DifferentiableAt ℂ G (ι ζ))
    (hf : ∀ᶠ ζ' in 𝓝 ζ, (f ζ' : ℂ) = G (ι ζ')) (w : V) :
    (fderiv ℝ f ζ w : ℂ) = fderiv ℂ G (ι ζ) (ι' w) := by
  set L : V →L[ℝ] ℂ := ((fderiv ℂ G (ι ζ)).restrictScalars ℝ).comp ι' with hL
  have hGι : HasFDerivAt (fun ζ' => G (ι ζ')) L ζ :=
    (hG.hasFDerivAt.restrictScalars ℝ).comp ζ hι
  have hg : HasFDerivAt (fun ζ' => (f ζ' : ℂ)) L ζ :=
    hGι.congr_of_eventuallyEq (hf.mono fun ζ' h => h)
  have hfre : HasFDerivAt f (Complex.reCLM.comp L) ζ := by
    have := (Complex.reCLM.hasFDerivAt (x := (f ζ : ℂ))).comp ζ hg
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun ζ' => ?_)
    simp
  have hg' : HasFDerivAt (fun ζ' => (f ζ' : ℂ)) (Complex.ofRealCLM.comp (Complex.reCLM.comp L)) ζ :=
    (Complex.ofRealCLM.hasFDerivAt (x := f ζ)).comp ζ hfre
  have huniq := hg.unique hg'
  rw [hfre.fderiv]
  have := congrArg (fun T : V →L[ℝ] ℂ => T w) huniq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply] at this
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ← this]
  simp [hL]

/-- **The directional derivative of a measurable holomorphic family is measurable in time.** -/
theorem measurable_fderiv_apply_param {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : α → E → ℂ} {U : Set E} (hU : IsOpen U)
    (hd : ∀ a, DifferentiableOn ℂ (F a) U) (hm : ∀ y ∈ U, Measurable fun a => F a y) {x : E}
    (hx : x ∈ U) (v : E) : Measurable fun a => fderiv ℂ (F a) x v := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  set K : ℝ := 2 * (‖v‖ + 1) / r with hK
  have hK0 : 0 < K := by positivity
  set c : ℕ → ℂ := fun n => (((n : ℝ) + 1) * K : ℝ) with hc
  have hcn : ∀ n, ‖c n‖ = ((n : ℝ) + 1) * K := fun n => by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmem : ∀ n, x + (c n)⁻¹ • v ∈ U := by
    intro n
    apply hrU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, hcn]
    have h1 : 1 ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have h2 : K ≤ ((n : ℝ) + 1) * K := le_mul_of_one_le_left hK0.le h1
    calc (((n : ℝ) + 1) * K)⁻¹ * ‖v‖ ≤ K⁻¹ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hK0 h2) (norm_nonneg v)
      _ = r * ‖v‖ / (2 * (‖v‖ + 1)) := by rw [hK]; field_simp
      _ < r := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
  have htend : Tendsto (fun n => ‖c n‖) atTop atTop := by
    simp_rw [hcn]
    exact Tendsto.atTop_mul_const hK0 (tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop)
  refine measurable_of_tendsto_metrizable (f := fun n a => c n • (F a (x + (c n)⁻¹ • v) - F a x))
    (fun n => ((hm _ (hmem n)).sub (hm x hx)).const_smul (c n)) (tendsto_pi_nhds.mpr fun a => ?_)
  exact (((hd a) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.lim v htend

/-- **Local bounds uniform in time pass to directional derivatives.** -/
theorem LocBdd.fderiv_apply {n : ℕ} {F : ℝ → ChainParamsC n → ℂ} {T : Set ℝ}
    {S : Set (ChainParamsC n)} (hS : IsOpen S) (hF : LocBdd F T S)
    (hd : ∀ t ∈ T, DifferentiableOn ℂ (F t) S) (v : ChainParamsC n) :
    LocBdd (fun t y => fderiv ℂ (F t) y v) T S := by
  intro x hx
  obtain ⟨U, hU, M, hM⟩ := hF x hx
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hS x hx
  obtain ⟨ε', hε', hε'U⟩ := Metric.mem_nhds_iff.mp hU
  set ρ : ℝ := min ε ε' / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hcb : closedBall x (3 * ρ) ⊆ S ∩ U := fun y hy => by
    rw [mem_closedBall] at hy
    refine ⟨hεS ?_, hε'U ?_⟩ <;> rw [mem_ball]
    · linarith [min_le_left ε ε']
    · linarith [min_le_right ε ε']
  refine ⟨ball x ρ, ball_mem_nhds x hρ, M / ρ * ‖v‖, fun t ht y hy => ?_⟩
  have hsub : closedBall y ρ ⊆ closedBall x (3 * ρ) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    rw [mem_ball] at hy
    have := dist_triangle w y x
    linarith
  have hb := GenSem.norm_fderiv_le_of_closedBall hρ ((hd t ht).mono fun w hw => (hcb (hsub hw)).1)
    fun w hw => hM t ht w (hcb (hsub hw)).2
  exact ((fderiv ℂ (F t) y).le_opNorm v).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg v))

/-- **The derivative of a translation invariant function is translation invariant.** -/
theorem fderiv_add_const_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ}
    {S : Set E} (hS : IsOpen S) {c : E} (hG : ∀ y ∈ S, G (y + c) = G y) {x : E} (hx : x ∈ S) :
    fderiv ℂ G (x + c) = fderiv ℂ G x := by
  rw [← fderiv_comp_add_right]
  exact Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hS.mem_nhds hx) hG)

/-- The final-phase translation vector. -/
def finalVec (n : ℕ) (v : Vec 2) : ChainParamsC n := (0, 0, fun a => (v a : ℂ))

/-- The child-phase translation vector. -/
def childVec {n : ℕ} (k : Fin n) (v : Vec 2) : ChainParamsC n :=
  (0, Pi.single k (0, fun a => (v a : ℂ)), 0)

theorem shiftFinal_eq_add {n : ℕ} (x : ChainParamsC n) (v : Vec 2) :
    x.shiftFinal v = x + finalVec n v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [ChainParamsC.shiftFinal, finalVec]

theorem shiftChild_eq_add {n : ℕ} (x : ChainParamsC n) (k : Fin n) (v : Vec 2) :
    x.shiftChild k v = x + childVec k v := by
  refine Prod.ext (by simp [ChainParamsC.shiftChild, childVec])
    (Prod.ext ?_ (by simp [ChainParamsC.shiftChild, childVec]))
  funext j
  by_cases hj : j = k
  · subst hj
    refine Prod.ext ?_ ?_ <;> simp [ChainParamsC.shiftChild, childVec]
  · simp [ChainParamsC.shiftChild, childVec, hj]
end

/-! **Carrier calculus: the final-phase derivative of context functions** (`dPhase`). The extension of
`∂_{ζ_q} a` is the complex derivative of the extension of `a` in the direction `e_q` of the final
phase (`dPhaseF`). It is holomorphic, measurable in time (difference quotients), invariant under
the phase translations, locally bounded uniformly in time (Cauchy), equal to the real derivative
at real parameters (`ofReal_fderiv_eq_of_hol`), and its final-phase coefficients are `2πih` times
those of `a` by the periodicity of the final-phase line (`pcoeff_deriv`): `CtxInv.dPhase`. -/

section
open AVRegularity.Providers.ComplexFlow

/-- The direction `e_q` of the final phase. -/
def phaseDir (n : ℕ) (q : Fin 2) : ChainParamsC n := (0, 0, evec q 1)

/-- The extension of the final-phase derivative. -/
def dPhaseF (q : Fin 2) (F : Ext) : Ext := fun dd n t x => fderiv ℂ (F dd n t) x (phaseDir n q)

/-- The real final phase of a chain as a linear map. -/
def finalCLM (n : ℕ) : Vec 2 →L[ℝ] ChainParamsC n :=
  (0 : Vec 2 →L[ℝ] (Fin 2 → ℂ)).prod ((0 : Vec 2 →L[ℝ] (Fin n → (Fin 2 → ℂ) × (Fin 2 → ℂ))).prod
    ofRealVecCLM)

theorem finalCLM_apply (n : ℕ) (w : Vec 2) : finalCLM n w = (0, 0, ofRealVec w) := rfl

theorem hasFDerivAt_paramsC (ch : RealChain) (ζ : Vec 2) :
    HasFDerivAt (fun ζ' : Vec 2 => ch.paramsC ζ') (finalCLM ch.children.length) ζ := by
  have h := (hasFDerivAt_const (ch.paramsC 0).1 ζ).prodMk
    ((hasFDerivAt_const (ch.paramsC 0).2.1 ζ).prodMk ofRealVecCLM.hasFDerivAt)
  unfold finalCLM
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun ζ' => rfl)

theorem finalCLM_basisVec (n : ℕ) (q : Fin 2) : finalCLM n (basisVec q) = phaseDir n q := by
  rw [finalCLM_apply]
  refine Prod.ext rfl (Prod.ext rfl (funext fun a => ?_))
  simp only [ofRealVec, basisVec_apply, phaseDir, evec]
  split_ifs <;> simp

/-- The final-phase line has derivative `F'(γ s) e_q`. -/
theorem hasDerivAt_lineF {n : ℕ} (q : Fin 2) {G : ChainParamsC n → ℂ} {x : ChainParamsC n} {s : ℝ}
    (hG : DifferentiableAt ℂ G (x.1, x.2.1, x.2.2 + evec q s)) :
    HasDerivAt (fun s : ℝ => lineF q G x s)
      (fderiv ℂ G (x.1, x.2.1, x.2.2 + evec q s) (phaseDir n q)) s := by
  have hγ : HasDerivAt (fun s : ℝ => ((x.1, x.2.1, x.2.2 + evec q s) : ChainParamsC n))
      (phaseDir n q) s := by
    have h1 : HasDerivAt (fun s : ℝ => evec q (s : ℂ)) (evec q 1) s := by
      rw [hasDerivAt_pi]
      intro a
      unfold evec
      split_ifs
      · exact (hasDerivAt_id s).ofReal_comp
      · exact hasDerivAt_const _ _
    exact (hasDerivAt_const s x.1).prodMk ((hasDerivAt_const s x.2.1).prodMk
      ((hasDerivAt_const s x.2.2).add h1 |>.congr_deriv (by simp)))
  exact (hG.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hγ

section DPhase

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **The final-phase derivative of a context expression.** -/
theorem CtxInv.dPhase (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fa : GenSort.Sem .ctx} {F : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p fa F B) :
    CtxInv D b j₀ i p (fun t ch ζ => fderiv ℝ (fa t ch) ζ (basisVec (transverseIndex p)))
      (dPhaseF (transverseIndex p) F) (fun mres h t => modeMul h * B mres h t) where
  hol dd n t ht :=
    GenSem.differentiableOn_fderiv_apply (isOpen_carrierC D b dd n 2) (hF.hol dd n t ht) _
  meas dd n x hx :=
    measurable_fderiv_apply_param (F := fun t : ocPulseWindow D.α D.q D.Λ i p => F dd n t)
      (isOpen_carrierC D b dd n 2) (fun t => hF.hol dd n t t.2)
      (fun y hy => hF.meas dd n y hy) hx _
  agree ch t ht ζ hch := by
    have hx := GenSem.paramsC_mem_carrierC hΛ hb hch ζ
    have hG := (hF.hol _ _ t ht _ hx).differentiableAt ((isOpen_carrierC _ _ _ _ _).mem_nhds hx)
    have := ofReal_fderiv_eq_of_hol (hasFDerivAt_paramsC ch ζ) hG
      (Eventually.of_forall fun ζ' => (hF.agree ch t ht ζ' hch).symm) (basisVec (transverseIndex p))
    rw [finalCLM_basisVec] at this
    exact this.symm
  fin dd n t ht x hx v hv := by
    unfold dPhaseF
    rw [shiftFinal_eq_add, fderiv_add_const_eq (isOpen_carrierC D b dd n 2) (fun y hy => by
      rw [← shiftFinal_eq_add]; exact hF.fin dd n t ht y hy v hv) hx]
  child dd n t ht x hx k v hv := by
    unfold dPhaseF
    rw [shiftChild_eq_add, fderiv_add_const_eq (isOpen_carrierC D b dd n 2) (fun y hy => by
      rw [← shiftChild_eq_add]; exact hF.child dd n t ht y hy k v hv) hx]
  bdd dd n :=
    (hF.bdd dd n).fderiv_apply (isOpen_carrierC D b dd n 2) (fun t ht => hF.hol dd n t ht) _
  mode mres hm0 hm2 h t ht dd n hdd x hx hre := by
    set q := transverseIndex p
    have hx2 := carrierC_mono hb.le hm2 hx
    have hsl := hdd.lastSlot
    have hmem : ∀ s : ℝ, ((x.1, x.2.1, x.2.2 + evec q s) : ChainParamsC n) ∈
        carrierC D b dd n 2 := fun s => by
      have := mem_carrierC_line hx2 (hre _) (z := (s : ℂ)) (by
        simp only [Complex.ofReal_im, abs_zero]; positivity)
      rwa [hsl] at this
    have hU := isOpen_carrierC D b dd n 2
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => lineF q (F dd n t) x s)
        (lineF q (dPhaseF q F dd n t) x s) s := fun s =>
      hasDerivAt_lineF q ((hF.hol dd n t ht _ (hmem s)).differentiableAt (hU.mem_nhds (hmem s)))
    have hc : Continuous fun s : ℝ => lineF q (dPhaseF q F dd n t) x s := by
      have hdF := GenSem.differentiableOn_fderiv_apply hU (hF.hol dd n t ht) (phaseDir n q)
      refine hdF.continuousOn.comp_continuous ?_ hmem
      exact continuous_const.prodMk (continuous_const.prodMk (continuous_const.add
        (continuous_pi fun a => by unfold evec; split_ifs <;> fun_prop)))
    have hper : Function.Periodic (fun s : ℝ => lineF q (F dd n t) x s) 1 := by
      intro s
      have e := shiftFinal_line q x (s : ℂ)
      simp only [Complex.ofReal_add, Complex.ofReal_one]
      unfold lineF
      rw [← e]
      have := hF.fin dd n t ht _ (hmem s) (rvec q) (by rw [hsl]; exact tInt_rvec p)
      exact this
    rw [finalPhaseCoeff_eq_pcoeff, pcoeff_deriv hd hc hper h, enorm_mul,
      ← finalPhaseCoeff_eq_pcoeff]
    refine mul_le_mul' (le_of_eq ?_) (hF.mode mres hm0 hm2 h t ht dd n hdd x hx hre)
    rw [← ofReal_norm, modeMul]
    congr 1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp

end DPhase
end

/-! **Carrier calculus: the time-only letters** (`time`). The partition weight, the covariance
primitive, the flat reference tensor and the constants are continuous in time
(`continuous_timeLetter`, with positive diffusivities). A time-only letter is constant in the
parameters, so its only mode is the zero mode, with the exact value `|L(t)|`:
`CtxInv.time`, `FamInv.time`, `CellInv.time`. -/

section
open AVRegularity.Providers.ComplexFlow

/-- **The time-only letters are continuous.** -/
theorem continuous_timeLetter (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : ∀ m, 0 < D.kap m) (L : TimeLetter) : Continuous (L.eval D) := by
  cases L with
  | partition lev k =>
    unfold TimeLetter.eval ocCutoff
    exact Real.smoothTransition.continuous.comp (by fun_prop)
  | covPrimitive lev s a c =>
    unfold TimeLetter.eval ocCovariance
    simp only [Matrix.of_apply]
    exact intervalIntegral.continuous_primitive (fun x y =>
      ((FreshAxes.refFlux_entry_continuous hΛ hζ (hκ lev) a c).sub
        continuous_const).intervalIntegrable x y) s
  | refFlux lev a c => exact FreshAxes.refFlux_entry_continuous hΛ hζ (hκ lev) a c
  | const c => exact continuous_const

/-- A continuous function of time is bounded on the output window. -/
theorem exists_bound_window {g : ℝ → ℝ} (hg : Continuous g) (D : OCData) (i : ℕ) (p : ℤ) :
    ∃ M : ℝ, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, |g t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := ((p : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ i)
    (b := ((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i)).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨M, fun t ht => by simpa [Real.norm_eq_abs] using hM t ht⟩

section Time

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **A time-only letter as a context expression.** -/
theorem CtxInv.time {L : TimeLetter} (hL : Continuous (L.eval D)) :
    CtxInv D b j₀ i p (GenSort.ofTime .ctx (L.eval D)) (fun _ _ t _ => ((L.eval D t : ℝ) : ℂ))
      (fun _ h t => if h = 0 then ENNReal.ofReal |L.eval D t| else 0) where
  hol dd n t ht := differentiableOn_const _
  meas dd n x hx :=
    (Complex.continuous_ofReal.comp (hL.comp continuous_subtype_val)).measurable
  agree ch t ht ζ hch := rfl
  fin dd n t ht x hx v hv := rfl
  child dd n t ht x hx k v hv := rfl
  bdd dd n x hx := by
    obtain ⟨M, hM⟩ := exists_bound_window hL D i p
    exact ⟨univ, univ_mem, M, fun t ht y _ => by simpa using hM t ht⟩
  mode mres hm0 hm2 h t ht dd n hdd x hx hre := by
    rw [finalPhaseCoeff_of_invariant _ (G := fun _ => ((L.eval D t : ℝ) : ℂ)) (fun s => rfl)]
    split_ifs with h0
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    · simp

/-- **A time-only letter as a family expression.** -/
theorem FamInv.time {L : TimeLetter} (hL : Continuous (L.eval D)) :
    FamInv D b j₀ i p (GenSort.ofTime .fam (L.eval D)) (fun _ _ t _ => ((L.eval D t : ℝ) : ℂ))
      (fun _ h t => if h = 0 then ENNReal.ofReal |L.eval D t| else 0) where
  hol dd n t ht := differentiableOn_const _
  meas dd n x hx :=
    (Complex.continuous_ofReal.comp (hL.comp continuous_subtype_val)).measurable
  indep dd n t x z := rfl
  agree ch t ht hch := rfl
  child dd n t ht x hx k v hv := rfl
  bdd dd n x hx := by
    obtain ⟨M, hM⟩ := exists_bound_window hL D i p
    exact ⟨univ, univ_mem, M, fun t ht y _ => by simpa using hM t ht⟩
  mode mres hm0 hm2 t ht dd n hdd x hx := by
    simp only [ite_true]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

/-- **A time-only letter as a cell expression.** -/
theorem CellInv.time {L : TimeLetter} (hL : Continuous (L.eval D)) :
    CellInv D b j₀ i p (GenSort.ofTime .cell (L.eval D))
      (fun h _ _ t _ => if h = 0 then ((L.eval D t : ℝ) : ℂ) else 0)
      (fun _ h t => if h = 0 then ENNReal.ofReal |L.eval D t| else 0) where
  hol h dd n t ht := differentiableOn_const _
  meas h dd n x hx := by
    split_ifs
    · exact (Complex.continuous_ofReal.comp (hL.comp continuous_subtype_val)).measurable
    · exact measurable_const
  indep h dd n t x z := rfl
  agree ch t ht hch η := by
    convert hasSum_ite_eq (0 : ℤ) ((L.eval D t : ℝ) : ℂ) using 1
    · funext h
      split_ifs with h0
      · subst h0; simp [emode]
      · simp
    · rfl
  child h dd n t ht x hx k v hv := rfl
  decay dd n x hx := by
    obtain ⟨M, hM⟩ := exists_bound_window hL D i p
    refine ⟨univ, univ_mem, M, 1, one_pos, fun h t ht y _ => ?_⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ht)
    split_ifs with h0
    · subst h0; simpa using hM t ht
    · rw [norm_zero]; positivity
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    split_ifs with h0
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    · simp

end Time
end

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
namespace AVRegularity.Providers.ComplexFlow

/-! **Carrier calculus: the recentering displacement of the last child**. Recentering a chain by `h` moves only the last child: its center by
`R(h) = 𝔛_par(s, x' + h, s') - x_par - c` and its phase by `R(h)/ε'`, where `𝔛_par` is the flow of
the parent family, `x_par` its center point, `s'` the anchor of the child and `x'` its center point.
Here the parent family is the last family of the chain without its last child, pulled back to the
parameters of the full chain along the projection dropping the last child (`parentFam`,
`CFam.pull`); the last child is its child (`lastChild`), and the complex displacement is
`recShift`. It is holomorphic in the parameters and the offset (`differentiableOn_recShift`),
`(3/2)`-Lipschitz in the offset (`norm_recShift_le`), independent of the final phase, and invariant
under the child-phase translations (`recShift_shiftChild`). -/

/-! ### Pullback of a family -/

namespace CFam

variable {Par Par' : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par] [NormedAddCommGroup Par']
  [NormedSpace ℂ Par']

/-- **The pullback of a family** along a map of the parameters. -/
def pull (F : CFam Par) (π : Par' → Par) : CFam Par' :=
  ⟨fun P => F.fl (π P), fun P => F.ctr (π P), F.anc⟩

variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

theorem OK.pull (h : F.OK Ω W ϱ Λ T) {Ω' : Set Par'} (hΩ' : IsOpen Ω') {π : Par' → Par}
    (hπ : Differentiable ℂ π) (hmaps : MapsTo π Ω' Ω) : (F.pull π).OK Ω' W ϱ Λ T where
  hϱ := h.hϱ
  hΛ := h.hΛ
  hT := h.hT
  hΛT := h.hΛT
  anc_mem := h.anc_mem
  hΩ := hΩ'
  ctr_hol := h.ctr_hol.comp hπ.differentiableOn hmaps
  cur_anc P hP := h.cur_anc (π P) (hmaps hP)
  hol u hu r hr := by
    have hφ : DifferentiableOn ℂ (fun q : Par' × CVec => ((π q.1, q.2) : Par × CVec))
        ((F.pull π).dom Ω' ϱ r) :=
      ((hπ.comp differentiable_fst).prodMk differentiable_snd).differentiableOn
    exact (h.hol u hu r hr).comp hφ fun q hq => ⟨hmaps hq.1, hq.2⟩
  init P hP r hr y hy := h.init (π P) (hmaps hP) r hr y hy
  jac P hP u hu r hr y hy := h.jac (π P) (hmaps hP) u hu r hr y hy
  group P hP u hu v hv r hr y hy := h.group (π P) (hmaps hP) u hu v hv r hr y hy

omit [NormedSpace ℂ Par] [NormedSpace ℂ Par'] in
theorem TimeCont.pull (h : F.TimeCont Ω W ϱ) {Ω' : Set Par'} {π : Par' → Par}
    (hπ : Continuous π) (hmaps : MapsTo π Ω' Ω) : (F.pull π).TimeCont Ω' W ϱ := by
  intro r hr
  have hφ : Continuous fun q : Par' × ℝ × CVec => ((π q.1, q.2.1, q.2.2) : Par × ℝ × CVec) :=
    (hπ.comp continuous_fst).prodMk (continuous_snd.fst.prodMk continuous_snd.snd)
  exact (h r hr).comp hφ.continuousOn fun q hq => ⟨hmaps hq.1, hq.2.1, hq.2.2⟩

theorem Over.pull {D : OCData} {b : ℝ} {l : ℕ} {p : ℤ} (h : F.Over D b Ω l p) {Ω' : Set Par'}
    (hΩ' : IsOpen Ω') {π : Par' → Par} (hπ : Differentiable ℂ π) (hmaps : MapsTo π Ω' Ω) :
    (F.pull π).Over D b Ω' l p where
  anc := h.anc
  ok := h.ok.pull hΩ' hπ hmaps
  cont := h.cont.pull hπ.continuous hmaps

end CFam

/-! ### The parent of the last family -/

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

/-- The discrete data without the last slot. -/
def dropData (dd : ChainData) : ChainData := ⟨dd.baseLevel, dd.slots.dropLast⟩

/-- The parameters without the last child, with the final phase `0`. -/
def projLast {m : ℕ} (x : ChainParamsC (m + 1)) : ChainParamsC m :=
  (x.1, fun j => x.2.1 j.castSucc, 0)

theorem differentiable_projLast (m : ℕ) : Differentiable ℂ (projLast (m := m)) := by
  unfold projLast
  refine differentiable_fst.prodMk (Differentiable.prodMk ?_ (differentiable_const _))
  exact differentiable_pi.2 fun j =>
    (by fun_prop : Differentiable ℂ fun x : ChainParamsC (m + 1) => x.2.1 j.castSucc)

theorem getD_dropLast {l : List ℤ} {j : ℕ} (hj : j + 1 < l.length) :
    l.dropLast.getD j 0 = l.getD j 0 := by
  have h1 : j < l.dropLast.length := by rw [List.length_dropLast]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by omega), List.getElem_dropLast]

theorem chainOK_dropData {dd : ChainData} {m : ℕ} (hdd : ChainOK D j₀ dd (m + 1)) :
    ChainOK D j₀ (dropData dd) m where
  base := hdd.base
  len := by
    show dd.slots.dropLast.length = m + 1
    rw [List.length_dropLast, hdd.len]
    rfl
  sched k hk := by
    have h1 := hdd.sched k (by omega)
    have hl := hdd.len
    show IsScheduledIn D (dd.baseLevel + 1 + k) (dd.slots.dropLast.getD (k + 1) 0)
      (dd.slots.dropLast.getD k 0)
    rwa [getD_dropLast (by omega), getD_dropLast (by omega)]

/-- The slot of the parent is the second to last slot. -/
theorem dropData_getLastD {dd : ChainData} {m : ℕ} (hdd : ChainOK D j₀ dd (m + 1)) :
    (dropData dd).slots.getLastD 0 = dd.slots.getD m 0 := by
  rw [← (chainOK_dropData hdd).getD_last]
  show dd.slots.dropLast.getD m 0 = _
  exact getD_dropLast (by rw [hdd.len]; omega)

theorem projLast_mem {dd : ChainData} {m : ℕ} (hdd : ChainOK D j₀ dd (m + 1)) (hb : 0 < b)
    {mres : ℝ} (hm : 0 ≤ mres) {x : ChainParamsC (m + 1)} (hx : x ∈ carrierC D b dd (m + 1) mres) :
    projLast x ∈ carrierC D b (dropData dd) m mres := by
  refine ⟨hx.1, fun k => ⟨(hx.2.1 k.castSucc).1, ?_⟩, ?_⟩
  · have h1 := (hx.2.1 k.castSucc).2
    show |((x.2.1 k.castSucc).2 (transverseIndex (dd.slots.dropLast.getD k 0))).im| < _
    rw [getD_dropLast (by rw [hdd.len]; omega)]
    exact h1
  · show |((0 : Fin 2 → ℂ) _).im| < _
    simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
    have : 0 < 3 + mres / 4 := by linarith
    positivity

/-- **The parent of the last family**, over the parameters of the full chain. -/
def parentFam (D : OCData) (dd : ChainData) (m : ℕ) : CFam (ChainParamsC (m + 1)) :=
  (chainFam D (dropData dd) m).pull projLast

theorem parentFam_over (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {m : ℕ}
    (hdd : ChainOK D j₀ dd (m + 1)) :
    (parentFam D dd m).Over D b (carrierC D b dd (m + 1) 2) (dd.baseLevel + m)
      ((dropData dd).slots.getLastD 0) :=
  (env.chainFam_over (chainOK_dropData hdd)).pull (isOpen_carrierC D b dd (m + 1) 2)
    (differentiable_projLast m) fun _ hx => projLast_mem hdd env.hb0 (by norm_num) hx

/-- The anchor of the last child. -/
abbrev lastAnchor (D : OCData) (dd : ChainData) (m : ℕ) : ℝ :=
  D.slotAnchor (dd.baseLevel + m + 2) (dd.slots.getLastD 0)

/-- **The last child**, as the child of the parent family. -/
def lastChild (D : OCData) (dd : ChainData) (m : ℕ) : CFam (ChainParamsC (m + 1)) :=
  (parentFam D dd m).child D (dd.baseLevel + m + 1) ((dropData dd).slots.getLastD 0)
    (lastAnchor D dd m) (fun x => (x.2.1 (Fin.last m)).1) (fun x => (x.2.1 (Fin.last m)).2)

/-- **The recentering displacement** `R(h) = 𝔛_par(s, x' + h, s') - x_par - c` of the last child. -/
def recShift (D : OCData) (dd : ChainData) (m : ℕ) (x : ChainParamsC (m + 1)) (h : CVec) : CVec :=
  (parentFam D dd m).fl x (parentFam D dd m).anc ((lastChild D dd m).ctr x + h) (lastAnchor D dd m) -
    ((parentFam D dd m).ctr x + (x.2.1 (Fin.last m)).1)

section Last

variable (env : ChainEnv D b CH Υ j₀) {dd : ChainData} {m : ℕ} (hdd : ChainOK D j₀ dd (m + 1))
include env hdd

omit env in
theorem lastChild_sched :
    IsScheduledIn D (dd.baseLevel + m + 1) (dd.slots.getLastD 0) ((dropData dd).slots.getLastD 0) := by
  have h1 := hdd.sched m (by omega)
  rw [hdd.getD_last, show dd.baseLevel + 1 + m = dd.baseLevel + m + 1 by omega] at h1
  rw [dropData_getLastD hdd]
  exact h1

/-- **The child hypotheses of the last child.** -/
theorem lastChildHyp :
    CFam.ChildHyp D (parentFam D dd m) (carrierC D b dd (m + 1) 2)
      (slotWin D (dd.baseLevel + m + 1) ((dropData dd).slots.getLastD 0))
      (slotWin D (dd.baseLevel + m + 2) (dd.slots.getLastD 0)) (8 * b * D.eps (dd.baseLevel + m))
      (chainK * ocA D.α D.q D.Λ (dd.baseLevel + m)) (6 / 5 * ocTauPP D.α D.q D.Λ (dd.baseLevel + m + 1))
      (dd.baseLevel + m + 1) ((dropData dd).slots.getLastD 0) (lastAnchor D dd m)
      (fun x => (x.2.1 (Fin.last m)).1) (fun x => (x.2.1 (Fin.last m)).2)
      (8 * b * D.eps (dd.baseLevel + m + 1)) (6 / 5 * ocTauPP D.α D.q D.Λ (dd.baseLevel + m + 2))
      (3 / 4 * b * D.eps (dd.baseLevel + m + 1)) (phB b) (15 * b * D.eps (dd.baseLevel + m + 1))
      (2 * Real.pi * ocA D.α D.q D.Λ (dd.baseLevel + m + 1) * D.eps (dd.baseLevel + m + 1) *
        Real.exp (30 * Real.pi * b))
      (4 * Real.pi ^ 2 * ocA D.α D.q D.Λ (dd.baseLevel + m + 1) * Real.exp (30 * Real.pi * b + 1)) := by
  have hS : LevelScales D b (dd.baseLevel + m) :=
    levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
      (by have := hdd.base; omega)
  refine (parentFam_over env hdd).childHyp hS env.hζ (lastChild_sched hdd)
    (by fun_prop : Differentiable ℂ fun x : ChainParamsC (m + 1) => (x.2.1 (Fin.last m)).1).differentiableOn
    (by fun_prop : Differentiable ℂ fun x : ChainParamsC (m + 1) => (x.2.1 (Fin.last m)).2).differentiableOn
    (fun x hx => ?_) (fun x hx => ?_)
  · have h1 := (hx.2.1 (Fin.last m)).1
    refine (norm_le_l1 _).trans ?_
    unfold l1
    have e : (1 + 2) * b / 4 * D.eps (dd.baseLevel + 1 + (Fin.last m : ℕ)) =
        3 / 4 * b * D.eps (dd.baseLevel + m + 1) := by
      rw [Fin.val_last, show dd.baseLevel + 1 + m = dd.baseLevel + m + 1 by omega]
      ring
    linarith
  · have h1 := (hx.2.1 (Fin.last m)).2
    rw [Fin.val_last, ← dropData_getLastD hdd] at h1
    unfold phB
    linarith

/-- The parent maps the last child center back to `x_par + c`. -/
theorem parent_fl_lastChild_ctr {x : ChainParamsC (m + 1)} (hx : x ∈ carrierC D b dd (m + 1) 2) :
    (parentFam D dd m).fl x (parentFam D dd m).anc ((lastChild D dd m).ctr x) (lastAnchor D dd m) =
      (parentFam D dd m).ctr x + (x.2.1 (Fin.last m)).1 := by
  have h := lastChildHyp env hdd
  have hs := h.hF.anc_mem
  have hs'W := h.mem_W h.hs'
  show (parentFam D dd m).fl x (parentFam D dd m).anc ((parentFam D dd m).fl x (lastAnchor D dd m)
    ((parentFam D dd m).ctr x + (x.2.1 (Fin.last m)).1) (parentFam D dd m).anc)
      (lastAnchor D dd m) = _
  rw [h.hF.group x hx _ hs _ hs'W _ hs _ (h.ctr_add_mem hx)]
  exact h.hF.init x hx _ hs _ (ball_subset_ball (by linarith [h.hF.hϱ]) (h.ctr_add_mem hx))

/-- The last child center lies in the parent ball at its anchor. -/
theorem lastChild_ctr_mem {x : ChainParamsC (m + 1)} (hx : x ∈ carrierC D b dd (m + 1) 2) :
    (lastChild D dd m).ctr x ∈ ball ((parentFam D dd m).cur x (lastAnchor D dd m))
      (3 / 8 * (8 * b * D.eps (dd.baseLevel + m))) := by
  have h := lastChildHyp env hdd
  have hs := h.hF.anc_mem
  have hs'W := h.mem_W h.hs'
  have h1 := h.hF.fl_mem_ball hx hs'W hs (ρ := 8 * b * D.eps (dd.baseLevel + m) / 4)
    (by linarith [h.hF.hϱ]) (h.ctr_add_mem hx)
  refine ball_subset_ball ?_ h1
  have := mul_le_mul_of_nonneg_right h.hLT (by linarith [h.hF.hϱ] :
    (0 : ℝ) ≤ 8 * b * D.eps (dd.baseLevel + m) / 4)
  linarith

/-- The radius of the offsets: `b ε_{l+1}` at the level `l + 1` of the last child. -/
theorem recShift_pt_mem {x : ChainParamsC (m + 1)} (hx : x ∈ carrierC D b dd (m + 1) 2) {h : CVec}
    (hh : ‖h‖ < b * D.eps (dd.baseLevel + m + 1)) :
    (lastChild D dd m).ctr x + h ∈ ball ((parentFam D dd m).cur x (lastAnchor D dd m))
      (8 * b * D.eps (dd.baseLevel + m)) := by
  have hS : LevelScales D b (dd.baseLevel + m) :=
    levelScales_of_carrierStart env.hq env.hΛ env.hα env.hb0 env.hb1 env.hCH env.hΥ env.hcs
      (by have := hdd.base; omega)
  have h1 := lastChild_ctr_mem env hdd hx
  have he : D.eps (dd.baseLevel + m + 1) ≤ D.eps (dd.baseLevel + m) := by
    have := hS.heps
    have : 0 < D.eps (dd.baseLevel + m + 1) := Construction.Stream.ocEpsilon_pos env.hΛ1
    linarith
  have hb := env.hb0
  rw [mem_ball] at h1 ⊢
  calc dist ((lastChild D dd m).ctr x + h) ((parentFam D dd m).cur x (lastAnchor D dd m))
      ≤ dist ((lastChild D dd m).ctr x) ((parentFam D dd m).cur x (lastAnchor D dd m)) + ‖h‖ := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
    _ < 3 / 8 * (8 * b * D.eps (dd.baseLevel + m)) + b * D.eps (dd.baseLevel + m + 1) :=
        add_lt_add h1 hh
    _ ≤ 8 * b * D.eps (dd.baseLevel + m) := by
        have h2 := mul_le_mul_of_nonneg_left he hb.le
        have h3 : 0 < b * D.eps (dd.baseLevel + m) :=
          mul_pos hb (Construction.Stream.ocEpsilon_pos env.hΛ1)
        linarith

/-- **The displacement is `(3/2)`-Lipschitz in the offset.** -/
theorem norm_recShift_le {x : ChainParamsC (m + 1)} (hx : x ∈ carrierC D b dd (m + 1) 2)
    {h : CVec} (hh : ‖h‖ < b * D.eps (dd.baseLevel + m + 1)) :
    ‖recShift D dd m x h‖ ≤ 3 / 2 * ‖h‖ := by
  have hC := lastChildHyp env hdd
  have hs := hC.hF.anc_mem
  have hs'W := hC.mem_W hC.hs'
  have h1 := recShift_pt_mem env hdd hx hh
  have hpos : 0 < b * D.eps (dd.baseLevel + m + 1) :=
    mul_pos env.hb0 (Construction.Stream.ocEpsilon_pos env.hΛ1)
  have h0 := recShift_pt_mem env hdd hx (h := 0) (by rw [norm_zero]; exact hpos)
  rw [add_zero] at h0
  have h2 := hC.hF.norm_fl_sub_le hx hs hs'W h1 h0
  unfold recShift
  rw [← parent_fl_lastChild_ctr env hdd hx]
  rw [add_sub_cancel_left] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right hC.hLT (norm_nonneg _))

/-- **The displacement is holomorphic** in the parameters and the offset. -/
theorem differentiableOn_recShift :
    DifferentiableOn ℂ (fun q : ChainParamsC (m + 1) × CVec => recShift D dd m q.1 q.2)
      (carrierC D b dd (m + 1) 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + m + 1))) := by
  have hC := lastChildHyp env hdd
  have hs := hC.hF.anc_mem
  have hs'W := hC.mem_W hC.hs'
  have hfl := hC.hF.hol _ hs _ hs'W
  have hctr : DifferentiableOn ℂ (lastChild D dd m).ctr (carrierC D b dd (m + 1) 2) :=
    hC.ctr_hol_child
  have hmap : MapsTo (fun q : ChainParamsC (m + 1) × CVec =>
      ((q.1, (lastChild D dd m).ctr q.1 + q.2) : ChainParamsC (m + 1) × CVec))
      (carrierC D b dd (m + 1) 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + m + 1)))
      ((parentFam D dd m).dom (carrierC D b dd (m + 1) 2) (8 * b * D.eps (dd.baseLevel + m))
        (lastAnchor D dd m)) := fun q hq =>
    ⟨hq.1, recShift_pt_mem env hdd hq.1 (by simpa using hq.2)⟩
  have h1 := hfl.comp (differentiableOn_fst.prodMk ((hctr.comp differentiableOn_fst
    fun q hq => hq.1).add differentiableOn_snd)) hmap
  have h2 : DifferentiableOn ℂ (fun q : ChainParamsC (m + 1) × CVec =>
      (parentFam D dd m).ctr q.1 + (q.1.2.1 (Fin.last m)).1)
      (carrierC D b dd (m + 1) 2 ×ˢ ball (0 : CVec) (b * D.eps (dd.baseLevel + m + 1))) :=
    (hC.hF.ctr_hol.comp differentiableOn_fst fun q hq => hq.1).add
      (by fun_prop : Differentiable ℂ fun q : ChainParamsC (m + 1) × CVec =>
        (q.1.2.1 (Fin.last m)).1).differentiableOn
  exact h1.sub h2

end Last

/-- **The displacement is invariant under the child-phase translations.** -/
theorem recShift_shiftChild (hΛ : 1 ≤ D.Λ) {dd : ChainData} {m : ℕ}
    (hdd : ChainOK D j₀ dd (m + 1)) (x : ChainParamsC (m + 1)) (k : Fin (m + 1)) {v : Vec 2}
    (hv : ∃ n : ℤ, v (transverseIndex (dd.slots.getD k 0)) = n) (h : CVec) :
    recShift D dd m (x.shiftChild k v) h = recShift D dd m x h := by
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  -- the parent does not see the translation
  have hpar : (chainFam D (dropData dd) m).fl (projLast (x.shiftChild k v)) =
        (chainFam D (dropData dd) m).fl (projLast x) ∧
      (chainFam D (dropData dd) m).ctr (projLast (x.shiftChild k v)) =
        (chainFam D (dropData dd) m).ctr (projLast x) := by
    by_cases hk : (k : ℕ) = m
    · have e : projLast (x.shiftChild k v) = projLast x := by
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        funext j
        have hj : j.castSucc ≠ k := fun hjk => by
          have := congrArg Fin.val hjk; simp at this; omega
        simp [projLast, ChainParamsC.shiftChild, Function.update_of_ne hj]
      rw [e]
      exact ⟨rfl, rfl⟩
    · set j : Fin m := ⟨k, by have := k.2; omega⟩ with hjdef
      have hjk : j.castSucc = k := Fin.ext rfl
      have e : projLast (x.shiftChild k v) = (projLast x).shiftChild j v := by
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        funext j'
        by_cases hj' : j' = j
        · subst hj'
          simp [projLast, ChainParamsC.shiftChild, hjk]
        · have h1 : j'.castSucc ≠ k := fun h => hj' (Fin.ext (by
            have := congrArg Fin.val h; simp [hjdef] at this ⊢; omega))
          simp [projLast, ChainParamsC.shiftChild, Function.update_of_ne h1,
            Function.update_of_ne hj']
      rw [e]
      refine chainFam_shiftChild D hε (dropData dd) (projLast x) j ?_
      obtain ⟨n0, hn0⟩ := hv
      refine ⟨n0, ?_⟩
      show v (transverseIndex (dd.slots.dropLast.getD j 0)) = n0
      rw [getD_dropLast (by have := hdd.len; have := k.2; simp [hjdef]; omega)]
      exact hn0
  have hc : ((x.shiftChild k v).2.1 (Fin.last m)).1 = (x.2.1 (Fin.last m)).1 := by
    by_cases hk : k = Fin.last m
    · subst hk; simp [ChainParamsC.shiftChild]
    · simp [ChainParamsC.shiftChild, Function.update_of_ne (Ne.symm hk)]
  have hfl : (parentFam D dd m).fl (x.shiftChild k v) = (parentFam D dd m).fl x := hpar.1
  have hctr : (parentFam D dd m).ctr (x.shiftChild k v) = (parentFam D dd m).ctr x := hpar.2
  have hlc : (lastChild D dd m).ctr (x.shiftChild k v) = (lastChild D dd m).ctr x := by
    show (parentFam D dd m).fl (x.shiftChild k v) (lastAnchor D dd m)
        ((parentFam D dd m).ctr (x.shiftChild k v) + ((x.shiftChild k v).2.1 (Fin.last m)).1)
        (parentFam D dd m).anc = _
    rw [hfl, hctr, hc]
    rfl
  unfold recShift
  rw [hfl, hctr, hlc, hc]

end AVRegularity.Providers.ComplexFlow
end
