-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeRetainedEquation
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeKernelFluxTime
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

/-! Native covariance images, coefficient time data, and pointwise time calculus
for the literal complete lift, at the actual stage and menu. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The menu covariance has a continuous derivative at its original anchor. -/
theorem native_menu_covariance_contDiff (D : OCData) (Mn : SuccMenu) (m : ℕ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ m) (i j : Fin 2) :
    ContDiff ℝ 1 (fun t => menuCovPrimitive D Mn m t i j) := by
  have hd := native_menu_covariance_derivative D Mn m hΛ hζ hν
  refine contDiff_one_iff_deriv.mpr ⟨fun t => (hd t i j).differentiableAt, ?_⟩
  have he : deriv (fun t => menuCovPrimitive D Mn m t i j) = fun t =>
      (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) i j :=
    funext fun t => (hd t i j).deriv
  rw [he]
  exact (FreshAxes.refFlux_entry_continuous (α := D.α) (q := D.q) (m := m)
    hΛ hζ hν i j).sub continuous_const

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {F : Frame D hr Dm bw j₀}

/-- The actual prepared field has a single classical time derivative on the window,
for every stage and every menu anchor. -/
theorem native_input_prepared_time (hi : NativeInput F) :
    ∃ dRep : F.Field, ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep := by
  classical
  obtain ⟨dZ, hZc, hdZ, hZt⟩ := native_input_readout_sobolev_time hi
  let Z (v : CompIn F.G.comps) (t : ℝ) :=
    succReadout F.m (D.eps (F.m - 1)) F.η₀ F.Naux (fun c => F.Y c t) v
  have hres := hi.auxiliary
  have hK : 4 ≤ F.Naux - 2 * F.p := by omega
  have hKL : F.Naux - 2 * F.p + 2 * F.p ≤ F.Naux := by omega
  have hν : 0 < D.κ F.m :=
    CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band (by
      rw [← hi.level]
      exact hi.stage.top)
  have hH := native_menu_covariance_contDiff D F.Mn F.m hi.stage.base hi.stage.profile hν
  have ht (v : CompIn F.G.comps) := native_covImage_strong_time (by omega :
      2 ≤ F.Naux - 2 * F.p) hKL hi.window
    (menuCovPrimitive D F.Mn F.m) hH (Z v) (dZ v) (F.PZ v) (hZc v) (hdZ v) (hZt v)
    (fun t ht => (F.lift.2.1 v t ht).1)
  choose dRep hLp htime using fun v => (ht v).2
  apply native_classical_time_curve_exists F (F.Naux - 2 * F.p) hK hi.window
    F.PZ dRep F.aRep
  · intro v t ht
    exact FullLift.classicalRep_order_mono _ _ (F.lift.2.1 v t ht).2
      (Nat.sub_le (F.Naux - 2 * F.p) 2)
  · exact fun v => (ht v).1
  · exact hLp
  · exact htime

/-- A literal physical coefficient acting on a prepared chart word has a common
time derivative on the overlap of its pulse and the readout window. -/
theorem native_input_coefficient_prepared_term_time (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let c := D.cellScaleSq F.m
    let W := Icc F.tp F.tf ∩ Icc (D.slotStart F.m p.1)
      (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
    ∀ᵐ t ∂volume.restrict W, ∀ x,
      DifferentiableAt ℝ (fun s =>
        F.CcT p.1 g n m α (c⁻¹ * s) (ρ⁻¹ • label s x) ((D.eps F.m)⁻¹ • label s x) v u
          (orderedDerivative α (fun Y => F.aRep s (chart s (ρ • Y)) u) (ρ⁻¹ • label s x))) t := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
  let W := Icc F.tp F.tf ∩ Icc a b
  let Φ := fun t Y => chart t (ρ • Y)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) :=
    hchart.comp (contDiff_fst.prodMk ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hres : m + 4 ≤ F.Naux - 2 * F.p := by
    have hA := hi.auxiliary
    omega
  obtain ⟨_dc, _hdata, _hc, hdt⟩ := native_input_coefficient_mixed_time hi p g n m hg hn hm α v u
  have hdc : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ γ : ℝ → Vec 2 × Vec 2,
      ∀ V : Vec 2 × Vec 2, HasDerivAt γ V t →
        DifferentiableAt ℝ (fun s => F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * s)
          (γ s).2 (γ s).1 v u) t := by
    filter_upwards [hdt] with t ht
    intro γ V hγ
    have hh := ht 0 (fun i => Fin.elim0 i) 0 (fun i => Fin.elim0 i) γ V hγ
    simpa only [orderedDerivative_zero] using hh.differentiableAt
  have hdp := native_classical_curve_pullback_word_moving_differentiable F Q hi.window hres u Φ hΦ α
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (show W ⊆ Icc a b from inter_subset_right) hdc,
    ae_restrict_of_ae_restrict_of_subset (show W ⊆ Icc F.tp F.tf from inter_subset_left) hdp]
    with t hct hpt
  intro x
  have hlt : HasDerivAt (fun s => label s x) (deriv (fun s => label s x) t) t :=
    ((hlabel.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
  have hfast := hlt.const_smul ((D.eps F.m)⁻¹)
  have hslow := hlt.const_smul (ρ⁻¹)
  exact (hct _ _ (hfast.prodMk hslow)).clm_apply (hpt _ _ hslow)

/-- The cutoff of a literal coefficient/prepared-word term is absolutely
continuous through both pulse endpoints. The coefficient is extended only by
its endpoint values, and the cutoff removes that extension from the result. -/
theorem native_input_weighted_prepared_term_ac (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) (x : Vec 2) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    AbsolutelyContinuousOnInterval (fun t => ocCutoff D.α D.q D.Λ F.m p.1 t •
      F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
        (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
        (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u)
          (ρ⁻¹ • label t x))) F.tp F.tf := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
  have hab : a ≤ b := by
    have hw := EntryWeakProofs.weakData_lift_window_strict
      D hi.stage.base hi.stage.profile hi.stage.band F.m p.1
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    exact (div_le_div_iff_of_pos_right hc).mp hw.le
  obtain ⟨dc, hc⟩ := native_input_coefficient_physical_time_data hi p g n m hg hn hm α v u
  let Γ := fun t => (((D.eps F.m)⁻¹ • label t x), (ρ⁻¹ • label t x))
  have hl : ContDiff ℝ (⊤ : ℕ∞) (fun t => label t x) :=
    hlabel.comp (contDiff_id.prodMk contDiff_const)
  have hΓ : ContDiff ℝ (⊤ : ℕ∞) Γ :=
    ((contDiff_const (c := (D.eps F.m)⁻¹)).smul hl).prodMk
      ((contDiff_const (c := ρ⁻¹)).smul hl)
  have hcoef := (hc.time_clamp hab F.tp F.tf).global_moving_ac hi.window Γ
    (hΓ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  let Φ := fun t Y => chart t (ρ • Y)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) :=
    hchart.comp (contDiff_fst.prodMk ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hword := native_classical_curve_pullback_word_smooth_label_ac F Q hi.window
    (show m + 4 ≤ F.Naux - 2 * F.p by have := hi.auxiliary; omega) u Φ hΦ
    (fun t => ρ⁻¹ • label t x) ((contDiff_const (c := ρ⁻¹)).smul hl) α
  have hproduct := native_bilinear_time_ac ((ContinuousLinearMap.apply ℝ (hr v.1.root)).flip)
    hcoef hword
  have hcut : AbsolutelyContinuousOnInterval (ocCutoff D.α D.q D.Λ F.m p.1) F.tp F.tf :=
    ((CycleReference.ocCutoff_contDiff hi.stage.base p.1).of_le
      (by simp)).contDiffOn.absolutelyContinuousOnInterval
  apply (hcut.fun_smul hproduct).congr
  intro t _ht
  by_cases ht : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
  · simp only [ht, zero_smul]
  · have hw : t ∈ Icc a b := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
      (Construction.Stream.ocTau_pos hi.stage.base) ht
    dsimp only [Γ, Φ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]
    rw [projIcc_of_mem hab hw]
    rfl

/-- Literal coefficient/prepared-word terms have finite uniform spatial budgets
through the pulse endpoints. Clamping is removed by the cutoff, not by an
outside-window premise on the coefficient. -/
theorem native_input_weighted_prepared_term_jet_bound (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps) (R : ℕ)
    (hR : R + F.N + 2 ≤ F.Naux - 2 * F.p)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (X : Set (Vec 2)) (hX : IsCompact X) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    NativeCompactSpatialBudget F.tp F.tf R X (fun t y => ocCutoff D.α D.q D.Λ F.m p.1 t •
        F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
          (ρ⁻¹ • label t y) ((D.eps F.m)⁻¹ • label t y) v u
          (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u)
            (ρ⁻¹ • label t y))) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let a := D.slotStart F.m p.1
  let b := (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
  have hab : a ≤ b := by
    have hw := EntryWeakProofs.weakData_lift_window_strict
      D hi.stage.base hi.stage.profile hi.stage.band F.m p.1
    have hc := EntryWeakProofs.weakData_cellScaleSq_pos
      D hi.stage.base hi.stage.profile hi.stage.band F.m
    exact (div_le_div_iff_of_pos_right hc).mp hw.le
  obtain ⟨dc, hc⟩ := native_input_coefficient_physical_time_data hi p g n m hg hn hm α v u
  let Γ := fun t y => (((D.eps F.m)⁻¹ • label t y), (ρ⁻¹ • label t y))
  have hΓ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Γ) :=
    ((contDiff_const (c := (D.eps F.m)⁻¹)).smul hlabel).prodMk
      ((contDiff_const (c := ρ⁻¹)).smul hlabel)
  let C := fun t y => F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * projIcc a b hab t)
    (Γ t y).2 (Γ t y).1 v u
  have hC (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : ContDiff ℝ (R : ℕ∞) (C t) := by
    obtain ⟨hs, _⟩ := native_local_reserve_joint_data (Ω := univ) R _
      ((hc.time_clamp hab F.tp F.tf).coefficient R)
    have hh := hs t ht
    rw [univ_prod_univ] at hh
    exact (contDiffOn_univ.mp hh).comp
      ((hΓ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))
  have hCb (k : ℕ) (_hk : k ≤ R) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x ∈ X, ‖iteratedFDeriv ℝ k (C t) x‖ ≤ B :=
    native_local_reserve_sample_jet_bound k
      (fun Y => (hc.time_clamp hab F.tp F.tf).coefficient k Y (mem_univ _)) Γ hΓ X hX
  let Φ := fun t Y => chart t (ρ • Y)
  let Ψ := fun t y => ρ⁻¹ • label t y
  let W := fun t y => orderedDerivative α (fun Y => F.aRep t (Φ t Y) u) (Ψ t y)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Φ) :=
    hchart.comp (contDiff_fst.prodMk ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Ψ) :=
    (contDiff_const (c := ρ⁻¹)).smul hlabel
  have hW (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : ContDiff ℝ (R : ℕ∞) (W t) := by
    have hf : ContDiff ℝ ((R + m : ℕ) : ℕ∞) (fun y => F.aRep t y u) :=
      ((Q.field u).smooth t ht).of_le (Nat.cast_le.mpr (by omega))
    have hP : ContDiff ℝ ((R + m : ℕ) : ℕ∞) (Φ t) :=
      (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    exact (CycleComparison.Lift.orderedDerivative_contDiff α R _
      (by simpa only [Nat.add_comm, Function.comp_def] using hf.comp hP)).comp
        ((hΨ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))
  have hWb (k : ℕ) (hk : k ≤ R) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x ∈ X, ‖iteratedFDeriv ℝ k (W t) x‖ ≤ B :=
    native_classical_curve_pullback_word_compact_jet_bound F Q u α k (by omega)
      Φ Ψ hΦ hΨ X hX
  obtain ⟨B, hB, hb⟩ := native_uniform_bilinear_jet_bound
    ((ContinuousLinearMap.apply ℝ (hr v.1.root)).flip) R X C W hC hW hCb hWb
  obtain ⟨Bc, hbc⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (CycleReference.ocCutoff_contDiff hi.stage.base p.1).continuous.continuousOn
  have he (t : ℝ) (ht : t ∈ Icc F.tp F.tf) : (fun y => ocCutoff D.α D.q D.Λ F.m p.1 t •
      F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
        (ρ⁻¹ • label t y) ((D.eps F.m)⁻¹ • label t y) v u
        (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u) (ρ⁻¹ • label t y))) =
      fun y => ocCutoff D.α D.q D.Λ F.m p.1 t • C t y (W t y) := by
    funext y
    by_cases hz : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
    · simp only [hz, zero_smul]
    · have hw : t ∈ Icc a b := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
        (Construction.Stream.ocTau_pos hi.stage.base) hz
      dsimp only [C, Γ, W, Φ, Ψ]
      rw [projIcc_of_mem hab hw]
  refine ⟨?_, max Bc 0 * B, mul_nonneg (le_max_right _ _) hB, ?_⟩
  · intro t ht
    rw [he t ht]
    exact ((hC t ht).clm_apply (hW t ht)).const_smul _
  intro t ht x hx
  have hprod : ContDiff ℝ (R : ℕ∞) (fun y => C t y (W t y)) := (hC t ht).clm_apply (hW t ht)
  rw [he t ht, iteratedFDeriv_const_smul_apply' (a := ocCutoff D.α D.q D.Λ F.m p.1 t) hprod.contDiffAt, norm_smul]
  exact mul_le_mul ((hbc t ht).trans (le_max_left _ _)) (hb t ht x hx)
    (norm_nonneg _) (le_max_right _ _)

/-- A full physical pulse has time derivatives at every spatial point on one
common time set. The coefficient and prepared-field exceptional sets are chosen
before any point or component. -/
theorem native_input_pulse_time_differentiable (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    let W := Icc F.tp F.tf ∩ Icc (D.slotStart F.m p.1)
      (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
    ∀ᵐ t ∂volume.restrict W, ∀ x v,
      DifferentiableAt ℝ (fun s => pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ) F.N F.depth
        (F.CcT p.1) chart label F.aRep s x v) t := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let W := Icc F.tp F.tf ∩ Icc (D.slotStart F.m p.1)
    (((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
  let T := fun g n m (α : DerivativeWord2 m) (v u : CompIn F.G.comps) s x =>
    F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * s)
      (ρ⁻¹ • label s x) ((D.eps F.m)⁻¹ • label s x) v u
      (orderedDerivative α (fun Y => F.aRep s (chart s (ρ • Y)) u) (ρ⁻¹ • label s x))
  have hterms : ∀ᵐ t ∂volume.restrict W, ∀ g, g ≤ F.depth → ∀ n, n ≤ F.N →
      ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u, ∀ x,
        DifferentiableAt ℝ (fun s => T g n m α v u s x) t := by
    apply ae_all_iff.mpr
    intro g
    apply ae_all_iff.mpr
    intro hg
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro hn
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro hm
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro u
    exact native_input_coefficient_prepared_term_time hi p Q g n m hg hn hm α v u
      chart label hchart hlabel
  have hinside : ∀ᵐ t ∂volume.restrict W, t ∈ Ioo F.tp F.tf := by
    apply ae_restrict_of_ae_restrict_of_subset inter_subset_left
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  have hc : D.cellScaleSq F.m ≠ 0 := (EntryWeakProofs.weakData_cellScaleSq_pos
    D hi.stage.base hi.stage.profile hi.stage.band F.m).ne'
  filter_upwards [hterms, hinside] with t ht hti
  intro x v
  have hsum : DifferentiableAt ℝ (fun s =>
      ∑ g ∈ Finset.range (F.depth + 1), ∑ n ∈ Finset.range (F.N + 1),
        ε ^ n • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          T g n m α v u s x) t := by
    apply DifferentiableAt.fun_sum
    intro g hg
    apply DifferentiableAt.fun_sum
    intro n hn
    apply DifferentiableAt.const_smul
    apply DifferentiableAt.fun_sum
    intro m hm
    apply DifferentiableAt.fun_sum
    intro α _
    apply DifferentiableAt.fun_sum
    intro u _
    exact ht g (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg)
      n (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
      m (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm) α v u x
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
  exact native_classical_pulse_expansion F Q (D.cellScaleSq F.m) ρ (D.eps F.m) ε hc
    F.N F.depth (by have := hi.auxiliary; omega) (F.CcT p.1) chart label s
    (Ioo_subset_Icc_self hs) ((hchart.comp (contDiff_const.prodMk contDiff_id)).of_le
      (by simp)) x v

/-- A cutoff-weighted physical pulse is absolutely continuous on the entire
observation window, including times outside its coefficient window. -/
theorem native_input_weighted_pulse_ac (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label)) (x : Vec 2) (v : CompIn F.G.comps) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    AbsolutelyContinuousOnInterval (fun t => ocCutoff D.α D.q D.Λ F.m p.1 t •
      pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ) F.N F.depth
        (F.CcT p.1) chart label F.aRep t x v) F.tp F.tf := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let T := fun g n m (α : DerivativeWord2 m) (u : CompIn F.G.comps) t =>
    ocCutoff D.α D.q D.Λ F.m p.1 t •
      F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
        (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
        (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u) (ρ⁻¹ • label t x))
  have hsum : AbsolutelyContinuousOnInterval (fun t =>
      ∑ g ∈ Finset.range (F.depth + 1), ∑ n ∈ Finset.range (F.N + 1),
        ε ^ n • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          T g n m α u t) F.tp F.tf := by
    apply native_time_finset_sum
    intro g hg
    apply native_time_finset_sum
    intro n hn
    apply AbsolutelyContinuousOnInterval.const_smul
    apply native_time_finset_sum
    intro m hm
    apply native_time_finset_sum
    intro α _
    apply native_time_finset_sum
    intro u _
    exact native_input_weighted_prepared_term_ac hi p Q g n m
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg)
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm)
      α v u chart label hchart hlabel x
  apply hsum.congr
  intro t ht
  rw [uIcc_of_le hi.window] at ht
  dsimp only
  change _ = ocCutoff D.α D.q D.Λ F.m p.1 t •
    pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth
      (F.CcT p.1) chart label F.aRep t x v
  rw [native_classical_pulse_expansion F Q (D.cellScaleSq F.m) ρ (D.eps F.m) ε
    (EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.m).ne'
    F.N F.depth (by have := hi.auxiliary; omega) (F.CcT p.1) chart label t ht
    ((hchart.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) x v]
  dsimp only [T]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_comm (ocCutoff D.α D.q D.Λ F.m p.1 t) (ε ^ n)]
  apply congrArg (fun y : hr v.1.root => ε ^ n • y)
  simp only [Finset.smul_sum]

/-- The literal complete lift is absolutely continuous at every spatial point.
One fixed finite observed-pulse sum represents it on the closed window. -/
theorem native_input_lifted_time_ac (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (x : Vec 2) (v : CompIn F.G.comps) :
    AbsolutelyContinuousOnInterval (fun t => F.uh t x v) F.tp F.tf := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let chart := fun j s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j)
  let label := fun j s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j) y s
  let P := fun j s => pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε
    F.N F.depth (F.CcT j) (chart j) (label j) F.aRep s x v
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  have hsum : AbsolutelyContinuousOnInterval (fun t =>
      ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m F.tp F.tf,
        ocCutoff D.α D.q D.Λ F.m j t • P j t) F.tp F.tf := by
    apply native_time_finset_sum
    intro j hj
    exact native_input_weighted_pulse_ac hi ⟨j, (Finset.mem_filter.mp hj).2.1⟩ Q
      (chart j) (label j)
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := D.slotAnchor F.m j)))))
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        ((contDiff_const (c := D.slotAnchor F.m j)).prodMk (contDiff_snd.prodMk contDiff_fst))) x v
  apply hsum.congr
  intro t ht
  rw [uIcc_of_le hi.window] at ht
  unfold Frame.uh menuLiftedRep gluedLift
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine (Finset.sum_subset
    (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ ht)
      (fun j hj hnj => ?_)).symm
  have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
    (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
      (Finset.mem_filter.mp hj).2.1 hin)
  rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j t hout, zero_smul]

/-- A cutoff-weighted physical pulse has uniform compact spatial jet budgets
on the entire observation window. -/
theorem native_input_weighted_pulse_jet_bound (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (R : ℕ) (hR : R + F.N + 2 ≤ F.Naux - 2 * F.p)
    (X : Set (Vec 2)) (hX : IsCompact X) (v : CompIn F.G.comps) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    NativeCompactSpatialBudget F.tp F.tf R X (fun t x => ocCutoff D.α D.q D.Λ F.m p.1 t •
      pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ) F.N F.depth
        (F.CcT p.1) chart label F.aRep t x v) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let T := fun g n m (α : DerivativeWord2 m) (u : CompIn F.G.comps) t x =>
    ocCutoff D.α D.q D.Λ F.m p.1 t •
      F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
        (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
        (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u) (ρ⁻¹ • label t x))
  have hsum : NativeCompactSpatialBudget F.tp F.tf R X (fun t x =>
      ∑ g ∈ Finset.range (F.depth + 1), ∑ n ∈ Finset.range (F.N + 1),
        ε ^ n • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          T g n m α u t x) := by
    apply NativeCompactSpatialBudget.sum
    intro g hg
    apply NativeCompactSpatialBudget.sum
    intro n hn
    apply NativeCompactSpatialBudget.const_smul
    apply NativeCompactSpatialBudget.sum
    intro m hm
    apply NativeCompactSpatialBudget.sum
    intro α _
    apply NativeCompactSpatialBudget.sum
    intro u _
    exact native_input_weighted_prepared_term_jet_bound hi p Q g n m
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg)
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
      (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm)
      α v u R hR chart label hchart hlabel X hX
  apply hsum.congr_window
  intro t ht x
  dsimp only
  change _ = ocCutoff D.α D.q D.Λ F.m p.1 t •
    pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth
      (F.CcT p.1) chart label F.aRep t x v
  rw [native_classical_pulse_expansion F Q (D.cellScaleSq F.m) ρ (D.eps F.m) ε
    (EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.m).ne'
    F.N F.depth (by have := hi.auxiliary; omega) (F.CcT p.1) chart label t ht
    ((hchart.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) x v]
  dsimp only [T]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_comm (ocCutoff D.α D.q D.Λ F.m p.1 t) (ε ^ n)]
  apply congrArg (fun y : hr v.1.root => ε ^ n • y)
  simp only [Finset.smul_sum]

/-- The complete literal lift has finite uniform spatial jet budgets on every
compact set, with constants chosen before the time and spatial points. -/
theorem native_input_lifted_compact_spatial_budget (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (R : ℕ) (hR : R + F.N + 2 ≤ F.Naux - 2 * F.p)
    (X : Set (Vec 2)) (hX : IsCompact X) (v : CompIn F.G.comps) :
    NativeCompactSpatialBudget F.tp F.tf R X (fun t x => F.uh t x v) := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let chart := fun j s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j)
  let label := fun j s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j) y s
  let P := fun j s x => pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε
    F.N F.depth (F.CcT j) (chart j) (label j) F.aRep s x v
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  have hsum : NativeCompactSpatialBudget F.tp F.tf R X (fun t x =>
      ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m F.tp F.tf,
        ocCutoff D.α D.q D.Λ F.m j t • P j t x) := by
    apply NativeCompactSpatialBudget.sum
    intro j hj
    exact native_input_weighted_pulse_jet_bound hi ⟨j, (Finset.mem_filter.mp hj).2.1⟩ Q
      (chart j) (label j)
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := D.slotAnchor F.m j)))))
      ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
        ((contDiff_const (c := D.slotAnchor F.m j)).prodMk (contDiff_snd.prodMk contDiff_fst))) R hR X hX v
  apply hsum.congr_window
  intro t ht x
  unfold Frame.uh menuLiftedRep gluedLift
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine (Finset.sum_subset
    (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ ht)
      (fun j hj hnj => ?_)).symm
  have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
    (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
      (Finset.mem_filter.mp hj).2.1 hin)
  rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j t hout, zero_smul]

/-- The literal complete lift has its actual periodic window budgets and uniform
word bounds. Its time dependence need only be absolutely continuous. -/
theorem native_input_lifted_window_bound (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (R : ℕ) (hR : R + F.N + 2 ≤ F.Naux - 2 * F.p) (v : CompIn F.G.comps) :
    ClassicalWindowBound F.tp F.tf R (fun t x => F.uh t x v) ∧
      ∀ n ≤ R, ∀ w : DerivativeWord2 n, ∃ B : ℝ,
        ∀ t ∈ Icc F.tp F.tf, ∀ x ∈ AVenhance.unitCube,
          ‖orderedDerivative w (fun y => F.uh t y v) x‖ ≤ B := by
  have hcube : AVenhance.unitCube ⊆ Icc (0 : Vec 2) 1 := by
    intro x hx
    exact ⟨fun i => (hx i (mem_univ _)).1.le, fun i => (hx i (mem_univ _)).2.le⟩
  have hbudget (n : ℕ) (hn : n ≤ R) :
      NativeCompactSpatialBudget F.tp F.tf n AVenhance.unitCube (fun t x => F.uh t x v) := by
    have hh := native_input_lifted_compact_spatial_budget hi Q n (by omega)
      (Icc (0 : Vec 2) 1) isCompact_Icc v
    obtain ⟨B, hB, hb⟩ := hh.bound
    exact ⟨hh.smooth, B, hB, fun t ht x hx => hb t ht x (hcube hx)⟩
  refine ⟨native_classical_window_bound_of_uniform_jets hbudget
    (fun t ht k x => congrFun (native_input_lifted_periodic hi t ht k x) v)
    (fun x => ?_), ?_⟩
  · have hh := (native_input_lifted_time_ac hi Q x v).continuousOn
    rwa [uIcc_of_le hi.window] at hh
  · intro n hn w
    obtain ⟨B, _hB, hb⟩ := (hbudget n hn).bound
    refine ⟨B, fun t ht x hx => ?_⟩
    exact (ChartTransport.norm_orderedDerivative_le ((hbudget n hn).smooth t ht) w x).trans
      (hb t ht x hx)

/-- Every odd physical pulse has a derivative representative on its own overlap
with the observation window, chosen before spatial points or tests. -/
theorem native_input_pulse_time_reps_exists (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep) :
    ∃ dT : ℤ → F.Field, ∀ j, Odd j → IsTimeDerivRep
      (Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j)
      (Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep)
      (dT j) := by
  refine ⟨fun j t x v => deriv (fun s => Construction.Residual.Presentation.pulseLiftRep
    F.Mn F.G F.m F.N F.depth F.CcT j F.aRep s x v) t, ?_⟩
  intro j hj
  let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j)
  let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j) y s
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk
        (contDiff_const (c := D.slotAnchor F.m j))))
  have hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
      ((contDiff_const (c := D.slotAnchor F.m j)).prodMk
        (contDiff_snd.prodMk contDiff_fst))
  have hh := native_input_pulse_time_differentiable hi ⟨j, hj⟩ Q chart label hchart hlabel
  change ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j), _
  simp only [ocPulseWindow, OCData.slotStart] at hh ⊢
  filter_upwards [hh] with t ht
  intro x
  exact hasDerivAt_pi.mpr (fun v => (ht x v).hasDerivAt)

/-- Pulse-local derivative representatives glue with the literal product rule.
The same representatives work for every spatial point on one common time set. -/
theorem native_input_glued_time_rep (hi : NativeInput F) (dT : ℤ → F.Field)
    (hT : ∀ j, Odd j → IsTimeDerivRep
      (Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j)
      (Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep)
      (dT j)) :
    IsTimeDerivRep (Icc F.tp F.tf) F.uh
      (Construction.Residual.Presentation.gluedTimeDeriv
        F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT) := by
  classical
  let P := fun j => Construction.Residual.Presentation.pulseLiftRep
    F.Mn F.G F.m F.N F.depth F.CcT j F.aRep
  let c := ocCutoff D.α D.q D.Λ F.m
  let R := fun j t x v => deriv (c j) t • P j t x v + c j t • dT j t x v
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  have hzero (j : ℤ) (t : ℝ) (ht : t ∉ ocPulseWindow D.α D.q D.Λ F.m j) :
      deriv (c j) t = 0 ∧ c j t = 0 := by
    have hgerm : c j =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with s hs
      exact WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j s hs
    exact ⟨((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hgerm).deriv,
      WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j t ht⟩
  have hpulse (p : OddSlot) : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ x v,
      HasDerivAt (fun s => c p.1 s • P p.1 s x v) (R p.1 t x v) t := by
    have hraw : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf),
        t ∈ ocPulseWindow D.α D.q D.Λ F.m p.1 → ∀ x,
          HasDerivAt (fun s => P p.1 s x) (dT p.1 t x) t := by
      apply (ae_restrict_iff' measurableSet_Icc).mp
      simpa only [IsTimeDerivRep, Measure.restrict_restrict measurableSet_Icc,
        inter_comm, ocPulseWindow, P] using hT p.1 p.2
    filter_upwards [hraw] with t ht
    intro x v
    by_cases hw : t ∈ ocPulseWindow D.α D.q D.Λ F.m p.1
    · simpa only [R, c, Pi.smul_apply, add_comm] using
        ((CycleReference.ocCutoff_contDiff hi.stage.base p.1).differentiable
          (by simp) t).hasDerivAt.fun_smul ((hasDerivAt_pi.mp (ht hw x)) v)
    · have hz := hzero p.1 t hw
      have hgerm : (fun s => c p.1 s • P p.1 s x v) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hw] with s hs
        rw [show c p.1 s = 0 from WeakEntryProofs.ocCutoff_zero_off_output
          D.α D.q D.Λ F.m hτ p.1 s hs, zero_smul]
      simpa only [R, hz.1, hz.2, zero_smul, add_zero] using
        (hasDerivAt_const t (0 : hr v.1.root)).congr_of_eventuallyEq hgerm
  have hpulses := ae_all_iff.mpr hpulse
  have hinside : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), t ∈ Ioo F.tp F.tf := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hpulses, hinside] with t ht hti
  intro x
  apply hasDerivAt_pi.mpr
  intro v
  have hsum : HasDerivAt (fun s =>
      ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m F.tp F.tf, c j s • P j s x v)
      (∑ j ∈ ocObsPulses D.α D.q D.Λ F.m F.tp F.tf, R j t x v) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact ht ⟨j, (Finset.mem_filter.mp hj).2.1⟩ x v
  have he : Construction.Residual.Presentation.gluedTimeDeriv
      F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT t x v =
      ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m F.tp F.tf, R j t x v := by
    simp only [Construction.Residual.Presentation.gluedTimeDeriv,
      Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    refine Finset.sum_subset
      (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ
        (Ioo_subset_Icc_self hti)) fun j hj hnj => ?_
    have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
      (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
        (Finset.mem_filter.mp hj).2.1 hin)
    have hz := hzero j t hout
    change R j t x v = 0
    simp only [R, hz.1, hz.2, zero_smul, add_zero]
  rw [← he] at hsum
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hti] with s hs
  unfold Frame.uh menuLiftedRep gluedLift
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_subset
    (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ
      (Ioo_subset_Icc_self hs)) fun j hj hnj => ?_
  have hout : s ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
    (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
      (Finset.mem_filter.mp hj).2.1 hin)
  rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j s hout, zero_smul]

/-- Every common derivative representative of the literal lift can be realized
exactly as gluedTimeDeriv of pulse-local representatives. The correction is
zero on one common full-measure time set and uses the cutoff partition of unity. -/
theorem native_input_glued_reps_of_rep (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (dUh : F.Field) (hd : IsTimeDerivRep (Icc F.tp F.tf) F.uh dUh) :
    ∃ dT : ℤ → F.Field,
      dUh = Construction.Residual.Presentation.gluedTimeDeriv
        F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT ∧
      ∀ j, Odd j → IsTimeDerivRep (Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j)
        (Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep)
        (dT j) := by
  classical
  obtain ⟨dT₀, hT₀⟩ := native_input_pulse_time_reps_exists hi Q
  let R := Construction.Residual.Presentation.gluedTimeDeriv
    F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT₀
  have hR : IsTimeDerivRep (Icc F.tp F.tf) F.uh R := native_input_glued_time_rep hi dT₀ hT₀
  have he : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ x, dUh t x = R t x := by
    filter_upwards [hd, hR] with t ht hrt
    exact fun x => (ht x).unique (hrt x)
  let dT := fun j t x v => dT₀ j t x v + (dUh t x v - R t x v)
  refine ⟨dT, ?_, ?_⟩
  · funext t x v
    have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
    have hsum : ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m t t,
        ocCutoff D.α D.q D.Λ F.m j t = 1 :=
      Providers.CascadeInvariants.sum_ocCutoff_eq_one hτ _
        (fun j hj => (Finset.mem_filter.mp hj).2.1) t
        (fun j hj hcut => Construction.Residual.Presentation.mem_obsPulses_time
          D.α D.q D.Λ F.m hτ hj (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut))
    change dUh t x v = _
    simp only [Construction.Residual.Presentation.gluedTimeDeriv,
      Finset.sum_apply, Pi.add_apply, Pi.smul_apply, dT, smul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_smul, hsum, one_smul, ← add_assoc, ← Finset.sum_add_distrib]
    have hRe : R t x v = ∑ j ∈ ocObsPulses D.α D.q D.Λ F.m t t,
        (deriv (ocCutoff D.α D.q D.Λ F.m j) t •
          Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep t x v +
          ocCutoff D.α D.q D.Λ F.m j t • dT₀ j t x v) := by
      simp only [R, Construction.Residual.Presentation.gluedTimeDeriv,
        Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    rw [← hRe]
    abel
  · intro j hj
    filter_upwards [hT₀ j hj,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left he] with t ht het
    intro x
    have hx := het x
    have hdT : dT j t x = dT₀ j t x := by
      funext v
      simp only [dT, congrFun hx v, sub_self, add_zero]
    rw [hdT]
    exact ht x

/-- Any common derivative representative of the literal lift has the same
pointwise primitives and finite time integrals. -/
theorem native_input_lifted_time_primitives_of_rep (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (dUh : F.Field) (hd : IsTimeDerivRep (Icc F.tp F.tf) F.uh dUh) :
    (∀ x v, IntervalIntegrable (fun t => dUh t x v) volume F.tp F.tf) ∧
      ∀ t ∈ Icc F.tp F.tf, ∀ x v,
        F.uh t x v - F.uh F.tp x v = ∫ s in Ioc F.tp t, dUh s x v := by
  have hdx (x : Vec 2) (v : CompIn F.G.comps) :
      ∀ᵐ t ∂volume.restrict (uIcc F.tp F.tf),
        HasDerivAt (fun s => F.uh s x v) (dUh t x v) t := by
    rw [uIcc_of_le hi.window]
    filter_upwards [hd] with t ht
    exact (hasDerivAt_pi.mp (ht x)) v
  refine ⟨fun x v => native_finite_time_derivative_integrable _ _
    (native_input_lifted_time_ac hi Q x v) (hdx x v), ?_⟩
  intro t ht x v
  have hsub : uIcc F.tp t ⊆ uIcc F.tp F.tf := by
    rw [uIcc_of_le ht.1, uIcc_of_le hi.window]
    exact Icc_subset_Icc le_rfl ht.2
  have he := native_finite_time_increment (fun s => F.uh s x v) (fun s => dUh s x v)
    ((native_input_lifted_time_ac hi Q x v).mono hsub)
    ((hdx x v).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  rw [intervalIntegral.integral_of_le ht.1] at he
  exact he

/-- Every cutoff-weighted pulse word has a common derivative with integrable
spatial budgets, because its forward and inverse charts leave prepared jets stationary. -/
theorem native_input_weighted_prepared_term_derivative (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (g n m : ℕ) (hg : g ≤ F.depth) (hn : n ≤ F.N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : CompIn F.G.comps)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (hinv : ∀ t x, chart t (label t x) = x)
    (R : ℕ) (hR : R + F.N + 4 ≤ F.Naux - 2 * F.p) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ df, NativeTimeDerivativeBudget F.tp F.tf R
      (fun t x => ocCutoff D.α D.q D.Λ F.m p.1 t •
        F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
          (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
          (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u) (ρ⁻¹ • label t x))) df := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : ρ ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  let T := fun (c : OrderedFinpartition m) t x => ocCutoff D.α D.q D.Λ F.m p.1 t •
    F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
      (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
      ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (fun y => F.aRep t y u) x)
        (fun i => iteratedFDeriv ℝ (c.partSize i) (fun Y => chart t (ρ • Y))
          (ρ⁻¹ • label t x))) (fun i => basisVec (α (Fin.rev i))))
  have hpart (c : OrderedFinpartition m) : ∃ df, NativeTimeDerivativeBudget F.tp F.tf R (T c) df := by
    obtain ⟨L, dL, hL, heL⟩ := native_input_pulse_word_operator_time hi p g n m hg hn hm α c v u
      chart label hchart hlabel
    have h := native_uniform_operator_prepared_jet_time F Q
      (n := c.length) (R := R) (by have := c.length_le; omega) hi.window u L dL hL
    refine ⟨_, h.congr_window ?_⟩
    intro t ht x
    exact heL t ht x _
  obtain ⟨df, hdf⟩ := NativeTimeDerivativeBudget.exists_sum Finset.univ T (fun c _ => hpart c)
  refine ⟨df, hdf.congr_window ?_⟩
  intro t ht x
  have ha : ContDiff ℝ (m : ℕ∞) (fun y => F.aRep t y u) :=
    ((Q.field u).smooth t ht).of_le (Nat.cast_le.mpr (by omega))
  have hΦ : ContDiff ℝ (m : ℕ∞) (fun Y => chart t (ρ • Y)) :=
    ((hchart.comp (contDiff_const.prodMk contDiff_id)).comp
      ((contDiff_const (c := ρ)).smul contDiff_id)).of_le (by simp)
  change ∑ c, T c t x = ocCutoff D.α D.q D.Λ F.m p.1 t •
    F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
      (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
      (orderedDerivative α ((fun y => F.aRep t y u) ∘ (fun Y => chart t (ρ • Y)))
        (ρ⁻¹ • label t x))
  rw [native_pullback_word_eq_faa α (fun y => F.aRep t y u)
    (fun Y => chart t (ρ • Y)) ha hΦ (ρ⁻¹ • label t x)]
  rw [smul_inv_smul₀ hρ, hinv]
  simp only [map_sum, Finset.smul_sum, T]

/-- The complete cutoff-weighted physical pulse has a common-time derivative
with the spatial reserve and integrable time budgets of the prepared curve. -/
theorem native_input_weighted_pulse_derivative (hi : NativeInput F) (p : OddSlot)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry chart))
    (hlabel : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry label))
    (hinv : ∀ t x, chart t (label t x) = x)
    (R : ℕ) (hR : R + F.N + 4 ≤ F.Naux - 2 * F.p) (v : CompIn F.G.comps) :
    let ρ := F.Mn.lenFactor * liftLength D F.m
    ∃ df, NativeTimeDerivativeBudget F.tp F.tf R (fun t x => ocCutoff D.α D.q D.Λ F.m p.1 t •
      pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ) F.N F.depth
        (F.CcT p.1) chart label F.aRep t x v) df := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let T := fun g n m (α : DerivativeWord2 m) (u : CompIn F.G.comps) t x =>
    ocCutoff D.α D.q D.Λ F.m p.1 t •
      F.CcT p.1 g n m α ((D.cellScaleSq F.m)⁻¹ * t)
        (ρ⁻¹ • label t x) ((D.eps F.m)⁻¹ • label t x) v u
        (orderedDerivative α (fun Y => F.aRep t (chart t (ρ • Y)) u) (ρ⁻¹ • label t x))
  have hsum : ∃ df, NativeTimeDerivativeBudget F.tp F.tf R (fun t x =>
      ∑ g ∈ Finset.range (F.depth + 1), ∑ n ∈ Finset.range (F.N + 1),
        ε ^ n • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          T g n m α u t x) df := by
    apply NativeTimeDerivativeBudget.exists_sum
    intro g hg
    apply NativeTimeDerivativeBudget.exists_sum
    intro n hn
    have hinner : ∃ df, NativeTimeDerivativeBudget F.tp F.tf R (fun t x =>
        ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u,
          T g n m α u t x) df := by
      apply NativeTimeDerivativeBudget.exists_sum
      intro m hm
      apply NativeTimeDerivativeBudget.exists_sum
      intro α _
      apply NativeTimeDerivativeBudget.exists_sum
      intro u _
      exact native_input_weighted_prepared_term_derivative hi p Q g n m
        (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg)
        (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
        (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm)
        α v u chart label hchart hlabel hinv R hR
    obtain ⟨df, hdf⟩ := hinner
    exact ⟨_, hdf.const_smul (ε ^ n)⟩
  obtain ⟨df, hdf⟩ := hsum
  refine ⟨df, hdf.congr_window ?_⟩
  intro t ht x
  change _ = ocCutoff D.α D.q D.Λ F.m p.1 t •
    pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε F.N F.depth
      (F.CcT p.1) chart label F.aRep t x v
  rw [native_classical_pulse_expansion F Q (D.cellScaleSq F.m) ρ (D.eps F.m) ε
    (EntryWeakProofs.weakData_cellScaleSq_pos D hi.stage.base hi.stage.profile hi.stage.band F.m).ne'
    F.N F.depth (by have := hi.auxiliary; omega) (F.CcT p.1) chart label t ht
    ((hchart.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) x v]
  dsimp only [T]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_comm (ocCutoff D.α D.q D.Λ F.m p.1 t) (ε ^ n)]
  apply congrArg (fun y : hr v.1.root => ε ^ n • y)
  simp only [Finset.smul_sum]

/-- All observed cutoff pulses assemble before choosing a spatial point, giving
one derivative candidate for each component of the literal complete lift. -/
theorem native_input_lifted_component_derivative_budget (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep)
    (R : ℕ) (hR : R + F.N + 4 ≤ F.Naux - 2 * F.p) (v : CompIn F.G.comps) :
    ∃ df, NativeTimeDerivativeBudget F.tp F.tf R (fun t x => F.uh t x v) df := by
  classical
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let ε := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / ρ
  let chart := fun j s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m j)
  let label := fun j s y => D.flowOf (F.m - 1) (D.slotAnchor F.m j) y s
  let P := fun j t x => ocCutoff D.α D.q D.Λ F.m j t •
    pulsePhysicalLift (D.cellScaleSq F.m) ρ (D.eps F.m) ε
      F.N F.depth (F.CcT j) (chart j) (label j) F.aRep t x v
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hi.stage.base
  obtain ⟨df, hdf⟩ := NativeTimeDerivativeBudget.exists_sum
    (ocObsPulses D.α D.q D.Λ F.m F.tp F.tf) P (fun j hj =>
      native_input_weighted_pulse_derivative hi ⟨j, (Finset.mem_filter.mp hj).2.1⟩ Q
        (chart j) (label j)
        ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
          (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := D.slotAnchor F.m j)))))
        ((CycleReference.streamFlow_joint_smooth (D.hΦ (F.m - 1))).comp
          ((contDiff_const (c := D.slotAnchor F.m j)).prodMk (contDiff_snd.prodMk contDiff_fst)))
        (fun t x => (CycleReference.streamFlowHomeomorph (D.hΦ (F.m - 1))
          t (D.slotAnchor F.m j)).right_inv x) R hR v)
  refine ⟨df, hdf.congr_window ?_⟩
  intro t ht x
  unfold Frame.uh menuLiftedRep gluedLift
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine (Finset.sum_subset
    (Construction.Residual.Presentation.obsPulses_time_subset D.α D.q D.Λ F.m hτ ht)
      (fun j hj hnj => ?_)).symm
  have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m j := fun hin => hnj
    (Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ F.m hτ
      (Finset.mem_filter.mp hj).2.1 hin)
  dsimp only [P]
  rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ j t hout, zero_smul]

/-- The actual native complete lift has the full classical time package,
including spatially regular periodic derivatives and every reserved word primitive. -/
theorem native_input_lifted_classical_time (hi : NativeInput F)
    {dRep : F.Field} (Q : ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep) :
    ∃ dUh : F.Field, ClassicalTimeCurve F (Dm + 4) F.uh dUh := by
  classical
  have hR : Dm + F.N + 4 ≤ F.Naux - 2 * F.p := by have := hi.auxiliary; omega
  have hb (v : CompIn F.G.comps) : ∃ df,
      ClassicalWindowBound F.tp F.tf Dm df ∧
      ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ x,
        HasDerivAt (fun s => F.uh s x v) (df t x) t := by
    obtain ⟨df, hdf⟩ := native_input_lifted_component_derivative_budget hi Q Dm hR v
    exact hdf.periodic_selection (fun t ht k x => congrFun (native_input_lifted_periodic hi t ht k x) v)
  choose df hdf hd using hb
  let dUh := fun t x v => df v t x
  have hder : IsTimeDerivRep (Icc F.tp F.tf) F.uh dUh := by
    have ha : ∀ᵐ t ∂volume.restrict (Icc F.tp F.tf), ∀ v, ∀ x,
        HasDerivAt (fun s => F.uh s x v) (df v t x) t := ae_all_iff.mpr hd
    filter_upwards [ha] with t ht
    intro x
    exact hasDerivAt_pi.mpr (fun v => ht v x)
  refine ⟨dUh, native_classical_time_curve_of_value_primitive F (Dm + 4) F.uh dUh hi.window
    (fun v => ?_) (fun v n hn w => ?_) hder (fun v => ?_) ?_⟩
  · simpa only [show Dm + 4 - 2 = Dm + 2 by omega] using
      (native_input_lifted_window_bound hi Q (Dm + 2) (by have := hi.auxiliary; omega) v).1
  · exact (native_input_lifted_window_bound hi Q (Dm + 2) (by have := hi.auxiliary; omega) v).2
      n (by omega) w
  · simpa only [Nat.add_sub_cancel] using hdf v
  · intro v t ht x
    exact (native_input_lifted_time_primitives_of_rep hi Q dUh hder).2 t ht x v

/-- The three actual native curves and the pulse-local representatives are selected
once, independently of every test, with the literal glued derivative witness. -/
theorem native_input_classical_time_packages (hi : NativeInput F) :
    ∃ dZ dRep dUh : F.Field,
      ClassicalTimeCurve F F.Naux F.aZ dZ ∧
      ClassicalTimeCurve F (F.Naux - 2 * F.p) F.aRep dRep ∧
      ClassicalTimeCurve F (Dm + 4) F.uh dUh ∧
      ∃ dT : ℤ → F.Field,
        dUh = Construction.Residual.Presentation.gluedTimeDeriv
          F.Mn F.G F.m F.N F.depth F.CcT F.aRep dT ∧
        ∀ j, Odd j → IsTimeDerivRep (Icc F.tp F.tf ∩ ocPulseWindow D.α D.q D.Λ F.m j)
          (Construction.Residual.Presentation.pulseLiftRep F.Mn F.G F.m F.N F.depth F.CcT j F.aRep)
          (dT j) := by
  obtain ⟨dZ, hZ⟩ := native_input_readout_time hi
  obtain ⟨dRep, hRep⟩ := native_input_prepared_time hi
  obtain ⟨dUh, hUh⟩ := native_input_lifted_classical_time hi hRep
  exact ⟨dZ, dRep, dUh, hZ, hRep, hUh,
    native_input_glued_reps_of_rep hi hRep dUh hUh.derivative⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
