-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFluxContinuityProduction
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.SourcesA
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativePreparedTime
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero
open AVRegularity.Providers.PathDecomp
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Positive lift grades vanish for an empty edge array, regardless of the ambient order. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

omit [DecidableEq ι] in
/-- With no edge, the cell source of a positive grade of arrays vanishing at the positive grades
vanishes. -/
theorem liftCellSource_empty_edges (Q : LiftOperatorData ι hs Dm)
    (hedge : ∀ v u d, Q.edge v u d = [])
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hz : ∀ hh', hh' ≠ 0 → ∀ n, Cc hh' n = 0)
    (a : ℝ → Vec 2 → ∀ i, hs i) {hh : ℕ} (hh0 : hh ≠ 0) (n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftCellSource Q Cc a hh n t X z = 0 := by
  have hA : ∀ hh', hh' ≠ 0 → ∀ n' X' z', liftA Q Cc a hh' n' t X' z' = 0 := by
    intro hh' h0 n' X' z'
    funext v
    refine liftA_apply_eq_zero (fun X'' z'' => ?_) (fun X'' z'' => ?_)
      (fun _ j u => Or.inl fun d => hedge v u d) X' z'
    · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz hh' h0]; rfl)
    · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz hh' h0]; rfl)
  have hM : ∀ hh', hh' ≠ 0 → ∀ n', liftMean Q Cc a hh' n' t = fun _ => 0 := by
    intro hh' h0 n'
    funext X'
    unfold liftMean
    rw [show (fun z' => liftA Q Cc a hh' n' t X' z') = fun _ => 0 from funext (hA hh' h0 n' X')]
    exact fieldCellMean_zero
  unfold liftCellSource
  rw [hA hh hh0, hM hh hh0]
  simp only [sub_self, neg_zero, zero_add]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p hp => ?_
  funext v
  by_cases hp1 : p.1 = 0
  · have hp2 : p.2 ≠ 0 := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega
    exact liftApply_apply_eq_zero fun m α u => Or.inr fun X' => by rw [hM p.2 hp2]; rfl
  · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz p.1 hp1]; rfl)

omit [DecidableEq ι] in
/-- With no edge, the grade-zero part of a lift sequence is a lift sequence. -/
theorem gradeZeroPart_lift [∀ i, FiniteDimensional ℝ (hs i)]
    {Q : LiftOperatorData ι hs Dm} {sX sZ N H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hedge : ∀ v u d, Q.edge v u d = [])
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hsZ : 1 ≤ sZ) :
    IsLiftSequence Q sX sZ t₀ t₁ N H (hlGradeZeroPart Cc) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha₀ t ht X z
    rw [hlGradeZeroPart_zero]
    exact h0 a₀ ha₀ t ht X z
  · intro hh hh1 _ m α t X z v u
    rw [hlGradeZeroPart_pos Cc (by omega)]
    rfl
  · intro hh hhH n hn m α t X z v u
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h2 0 hhH n hn m α t X z v u
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m hnm α t X z v u
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h3 0 hhH n m hnm α t X z v u
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m α σ
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h4 0 hhH n m α σ
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m α v u t ht
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h5 0 hhH n m α v u t ht
    · rw [hlGradeZeroPart_pos Cc hz]
      exact ⟨isBoxSmooth_zero sX sZ, fun X n' x => rfl⟩
  · intro hh hhH n hn1 hnN a₀ ha₀ X
    by_cases hz : hh = 0
    · subst hz
      have hc := h6 0 hhH n hn1 hnN a₀ ha₀ X
      rw [hlGradeZeroPart_zero]
      refine CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ t₀ t₁ _ _ _ _
        (fun t ht => ?_) hc
      funext z
      have IH : ∀ hh' n', (hh' < 0 ∨ (hh' = 0 ∧ n' < n)) →
          Uniqueness.CoeffEq Cc (hlGradeZeroPart Cc) t₀ t₁ hh' n' := by
        rintro hh' n' (h | ⟨rfl, h⟩)
        · omega
        · intro t _ m α
          rw [hlGradeZeroPart_zero]
      exact congrFun (congrFun
        (Uniqueness.liftCellSource_congr Q 0 n hn1 IH ht (fun _ => a₀)) X) z
    · have hs0 : (fun t z => liftCellSource Q (hlGradeZeroPart Cc) (fun _ => a₀) hh n t X z) =
          fun _ _ => 0 := funext fun t => funext fun z =>
        liftCellSource_empty_edges Q hedge (fun hh' h' n' => hlGradeZeroPart_pos Cc h' n')
          (fun _ => a₀) hz n t X z
      have hf0 : (fun t z => liftApply n (hlGradeZeroPart Cc hh n) (fun _ => a₀) t X z) =
          fun _ _ => 0 := by
        funext t z v
        exact liftApply_apply_eq_zero fun m α u =>
          Or.inl (by rw [hlGradeZeroPart_pos Cc hz]; rfl)
      rw [hs0, hf0]
      exact hl_isCellFieldInverse_zero _ _ hsZ t₀ t₁

omit [DecidableEq ι] in
/-- **With no edge, the positive grades of a lift sequence vanish on the window.** -/
theorem lift_positive_grade_empty_edges [∀ i, FiniteDimensional ℝ (hs i)]
    (Q : LiftOperatorData ι hs Dm) (hedge : ∀ v u d, Q.edge v u d = []) {sX sZ N H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (hsZ : 1 ≤ sZ) (hh : ℕ) (hz : hh ≠ 0) (hhH : hh ≤ H) (n m : ℕ) (α : DerivativeWord2 m)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X z : Vec 2) (v u : ι) :
    Cc hh n m α t X z v u = 0 := by
  have h := Uniqueness.lift_sequence_unique_window Q t₀ t₁ hab hW sX sZ N H Cc
    (hlGradeZeroPart Cc) hC (gradeZeroPart_lift hedge hC hsZ) hh hhH n m α t ht X z v u
  rw [h, hlGradeZeroPart_pos Cc hz]
  rfl


omit [DecidableEq ι] in
/-- Vanishing coefficients at a fixed time give a zero lift action at that time. -/
theorem liftApply_at_zero (Cc : ℕ → ℕ → LiftCoeff ι hs) (hh n : ℕ) (t : ℝ)
    (hz : ∀ m α X z v u, Cc hh n m α t X z v u = 0)
    (a : ℝ → Vec 2 → ∀ i, hs i) : liftApply n (Cc hh n) a t = fun _ _ => 0 := by
  funext X z v
  simp [liftApply, hz]

omit [DecidableEq ι] in
/-- With empty edges, a vanished positive lift grade has zero flux. -/
theorem liftFluxX_empty_grade (Q : LiftOperatorData ι hs Dm)
    (hedge : ∀ v u d, Q.edge v u d = []) (Cc : ℕ → ℕ → LiftCoeff ι hs)
    (hh n : ℕ) (t : ℝ) (hz : ∀ n m α X z v u, Cc hh n m α t X z v u = 0)
    (a : ℝ → Vec 2 → ∀ i, hs i) (X z : Vec 2) (j : Fin 2) :
    liftFluxX Q Cc a hh n t X z j = 0 := by
  have ha (n') := liftApply_at_zero Cc hh n' t (hz n') a
  have hs (j' : ℕ) : (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
      (liftApply (n - j') (Cc (hh - 1) (n - j')) a t) j X z) = fun _ => 0 := by
    funext ε v
    exact sourceFlux_apply_eq_zero (fun u => Or.inl (hedge v u)) j X z
  unfold liftFluxX
  simp [ha, hs, fastPartial, slowPartial]

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! The stage-generic kernel readout equation, usable at the terminal anchor. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The raw retained kernel equation on an arbitrary native frame. -/
theorem native_kernel_readout (F : Frame D hr Dm bw j₀) (hi : NativeInput F) :
    F.weakEquation (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1))) F.aZ
      0 (fluxR F) 0 := by
  have haux := hi.auxiliary
  have hDm : Dm ≤ F.Naux := by omega
  have hk : 1 ≤ F.Naux := by omega
  have hGrlev : F.Gr.level = F.m - 1 := by
    rw [hi.retained]
    change F.G'.level = F.m - 1
    rw [hi.actual.2.1, hi.level]
  have hilevel := hi.stage.level
  have hΛ : 1 ≤ D.Λ := hi.stage.base
  obtain ⟨hnat, hshift, k, hctx, hres⟩ := native_input_retained_certificates hi
  have hcoeff : ∀ v u (γ : F.Gr.fam.Γ v u) d, ∀ t ∈ Set.Icc F.tp F.tf,
      Continuous (F.Gr.physCoeff v u γ d t) := by
    intro v u γ d t ht
    exact ((native_context_physical_fields hΛ hi.stage.bandwidth
      (by rw [hGrlev]; rw [hi.level] at hilevel; omega)
      (by rw [hGrlev]; rw [hi.level] at hilevel; omega)
      hctx hnat hshift hres F.tp F.tf 0 d v u γ).1 t ht).1.continuous
  have hstream : IsAdmissibleStream (D.Φ (F.m - 1)) :=
    D.hΦ (F.m - 1)
  have hcomp := classical_kernel_component F.Gr F.P F.seedK F.freshK F.φ₀ hi.integrable
    hi.smooth (Providers.hasCompactSupport_of_unitBall hi.support) F.Naux
    (D.κ (F.m - 1)) F.tp F.tf (streamVel (D.Φ (F.m - 1))) hDm hk hi.window
    (fun t _ => hstream.vel_continuous.comp (continuous_const.prodMk continuous_id)) hcoeff
    hi.Y0 F.Y hi.Yw hi.Yk hi.solution F.aY F.retained
  unfold Frame.weakEquation
  apply finite_parent_readout_weak F.m (D.eps (F.m - 1)) F.η₀
    (D.κ (F.m - 1)) F.tp F.tf (streamVel (D.Φ (F.m - 1))) hi.window F.aY F.aZ
    (fun v s x => coeffFluxOn F.P F.seedK F.freshK F.φ₀ F.Gr .kernel F.aY v s x)
  · intro v t ht
    exact (F.retained v t ht).2.1.of_le (by exact_mod_cast hk)
  · intro v t ht
    exact readout_representative_eq F.m (D.eps (F.m - 1)) F.η₀
      (fun v => F.Y v t) (fun v x => F.aY t x v) (fun v x => F.aZ t x v)
      (fun v => F.retained v t ht) (fun v => F.readout v t ht) v
  · exact hcomp

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! Readout weak equation on a native frame from provenance reindexing and reconstruction. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The sum of the two correction fluxes is continuous by the native upsilon budget. -/
theorem native_cancellation (F : Frame D hr Dm bw j₀) (hi : NativeInput F)
    (hindex : ReindexOn F) (hrec : ReconstructOn F) : CancellationOn F := by
  have haux := hi.auxiliary
  have hsplit := kernelSplitOn_of_profile F hi.integrable hi.smooth
    (Providers.hasCompactSupport_of_unitBall hi.support) (by omega)
  obtain ⟨dZ, dRep, dUh, hZ, hRep, hUh, _hT⟩ := native_input_classical_time_packages hi
  have hups := nativeUpsilon_window hi (show NativeBudgetCurves F dZ dRep dUh from ⟨hZ, hRep, hUh⟩)
  intro v t ht φ hφ hp
  have hsub : ∀ s ∈ Set.Ioc F.tp t, s ∈ Set.Icc F.tp F.tf :=
    fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hU : ∀ s ∈ Set.Ioc F.tp t, Integrable (fun x => ∑ j : Fin 2,
      inner ℝ ((fluxRD F v s x + fluxRO F v s x) j) (gradE φ x j))
      (volume.restrict unitCube) := by
    intro s hs
    apply fluxPairing_integrable _ hφ
    exact ((hups v).smooth s (hsub s hs)).continuous
  have h := testedFlux_sub_common (C := fun s x => fluxRD F v s x + fluxRO F v s x)
    (hrec v t ht φ hφ hp) hU
  refine testedFlux_congr h ?_ ?_
  · intro s hs x
    show fluxR F v s x = fluxPl F v s x - (fluxRD F v s x + fluxRO F v s x)
    rw [hindex v s (hsub s hs) x, hsplit v s (hsub s hs) x]
    abel
  · intro s _hs x
    show -(fluxN F v s x + (fluxRD F v s x + fluxRO F v s x)) =
      -fluxN F v s x - (fluxRD F v s x + fluxRO F v s x)
    abel

/-- No cascade prefix is used: both weak-equation operations are performed on this frame. -/
theorem native_readoutWeak (F : Frame D hr Dm bw j₀) (hi : NativeInput F)
    (hindex : ReindexOn F) (hrec : ReconstructOn F) : F.readoutWeak := by
  have hraw := native_kernel_readout F hi
  have hcancel := native_cancellation F hi hindex hrec
  intro v t ht φ hφ hp
  apply weakIdentity_of_tested_flux_agreement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ (hraw v t ht φ hφ hp)
  simpa only [Pi.zero_apply, zero_add, add_zero] using hcancel v t ht φ hφ hp

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The terminal covariance-transport frame** (step W.a of the coarse weak equation).

`termCovFrame c x` is the `Frame` at the terminal context: diffusivity `κ_{M-1}`, menu
`A.Mt M sXT sZT t_p c_r`, truncation order `K̂ - 2`. The retained solution `Z`, the covariance image
`P_pZ` and the lifted field `û` are truncated to the orders `K̂ - 2`, `K̂ - 2 - 2p_T` and `0`; the
three frame clauses `lift`, `readout`, `retained` follow from the clauses of `IsTerminalLiftedField`
and the representatives of `x` by the truncation lemmas of the full-lift package.

Special cases: `Z = 0` (every field is zero); `p_T = 1`; `K̂ = 2k₀ + 2` (the least `K̂`). -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Truncation commutes with a cast along an equality of roots (any order). -/
theorem truncate_cast_root' {K L : ℕ} (hKL : K ≤ L) {r r' : ℕ} (e : r = r')
    (x : TorusHk L (ScalarH r)) :
    truncateTorusHk hKL (cast (congrArg (fun r => TorusHk L (ScalarH r)) e) x) =
      cast (congrArg (fun r => TorusHk K (ScalarH r)) e) (truncateTorusHk hKL x) := by
  subst e
  rfl

/-- The readout commutes with truncation (any two orders). -/
theorem truncate_succReadout' {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K L : ℕ} (hKL : K ≤ L)
    (Y : ∀ v' : CompIn S', TorusHk L (ScalarH v'.1.root)) (v : CompIn S) :
    truncateTorusHk hKL (succReadout m E η L Y v) =
      succReadout m E η K (fun v' => truncateTorusHk hKL (Y v')) v := by
  unfold succReadout
  rw [map_sum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1
  · simp only [h, dite_true]
    rw [map_smul,
      truncate_cast_root' hKL ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))]
  · simp only [h, dite_false, map_zero]

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M) (x : TermResAux c)

/-- The retained solution truncated to the frame order `K̂ - 2`. -/
def termFrameY : ∀ v : CompIn (c.Gt'.retained M 1 A.RT).comps, ℝ →
    TorusHk (A.Khat Kout - 2) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Nat.sub_le _ 2) (c.Z v t)

/-- The covariance image truncated to the frame order `K̂ - 2 - 2p_T`. -/
def termFramePZ : ∀ v : CompIn c.Gw.comps, ℝ →
    TorusHk (A.Khat Kout - 2 - 2 * A.pT) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (by omega) (c.PZ v t)

/-- The lifted field truncated to order `0`. -/
def termFrameU : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Nat.zero_le _) (c.û v t)

/-- **W.a, the lift clause**: `IsMenuLiftedField` of the terminal menu at the truncated orders. -/
theorem termFrame_lift :
    IsMenuLiftedField (A.Mt M sXT sZT c.tp cr) c.Gw (c.Gt'.retained M 1 A.RT) M A.pT
      (A.Khat Kout - 2) A.NT A.dW sXT sZT A.η₀ c.tp (c.a + A.T₀) (termFrameY c)
      c.CcT (termFramePZ c) c.aRep (termFrameU c) := by
  obtain ⟨h1, h2, h3⟩ := c.lift
  refine ⟨h1, fun v t ht => ?_, fun v t ht => ?_⟩
  · obtain ⟨hcov, hrep⟩ := h2 v t ht
    have hsub : A.Khat Kout - 2 - 2 * A.pT ≤ A.Khat Kout - 2 * A.pT := by omega
    refine ⟨?_, ?_⟩
    · have := covImage_truncate_input (Nat.sub_le (A.Khat Kout) 2)
        _ _ _ (covImage_truncate hsub _ _ _ hcov)
      change IsCovImage _ (succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout - 2)
        (fun v' => truncateTorusHk (Nat.sub_le _ 2) (c.Z v' t)) v) (truncateTorusHk hsub (c.PZ v t))
      rw [← truncate_succReadout']
      exact this
    · exact classicalRep_truncate hsub (by omega) _ _
        (classicalRep_order_mono _ _ hrep (by omega))
  · exact (h3 v t ht)

/-- **W.a, the readout clause**: the readout of the truncated retained solution has the
representative `aZ` at the order `K̂ - 2`. -/
theorem termFrame_readout (v : CompIn c.Gw.comps) (t : ℝ) (ht : t ∈ Set.Icc c.tp (c.a + A.T₀)) :
    IsClassicalRep (succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout - 2)
      (fun v' => termFrameY c v' t) v) (fun y => x.aZ t y v) (A.Khat Kout - 2) := by
  unfold termFrameY
  rw [← truncate_succReadout']
  exact classicalRep_truncate (Nat.sub_le _ 2) le_rfl _ _ (x.repZ v t ht)

/-- **W.a, the retained clause**: the truncated retained solution has the representative `aY`. -/
theorem termFrame_retained (v : CompIn (c.Gt'.retained M 1 A.RT).comps) (t : ℝ)
    (ht : t ∈ Set.Icc c.tp (c.a + A.T₀)) :
    IsClassicalRep (termFrameY c v t) (fun y => x.aY t y v) (A.Khat Kout - 2) :=
  classicalRep_truncate (Nat.sub_le _ 2) le_rfl _ _ (x.repY v t ht)

/-- **W.a: the terminal covariance-transport frame.** -/
def termCovFrame : Frame c.D ScalarH A.Dt A.bw j₀ where
  G := c.Gw
  G' := c.Gt'
  Gr := c.Gt'.retained M 1 A.RT
  Mn := A.Mt M sXT sZT c.tp cr
  P := A.Pt c.D Cw cr M
  seedK := A.Kw_ c.D M nW
  freshK := A.Kn_ c.D M cr
  φ₀ := A.φ₀
  m := M
  H := 1
  J := A.RT
  N := A.NT
  p := A.pT
  depth := A.dW
  Naux := A.Khat Kout - 2
  sX := sXT
  sZ := sZT
  η₀ := A.η₀
  tp := c.tp
  tf := c.a + A.T₀
  Y := termFrameY c
  CcT := c.CcT
  PZ := termFramePZ c
  aRep := c.aRep
  aZ := x.aZ
  aY := x.aY
  û := termFrameU c
  lift := termFrame_lift c
  readout := termFrame_readout c x
  retained := termFrame_retained c x

/-- The coarse equation at the context is the macro equation of the terminal frame. -/
theorem termCoarseWeakAt_iff : TermCoarseWeakAt c x ↔ (termCovFrame c x).macroWeak := Iff.rfl

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! First-source input without the degree cutoff, which is used only by the path-mean matching.
This private terminal adapter retains the actual menu and all analytic premises. The first-source
proof uses the alphabet, the lift reserves and the other fields, but not the lower bound two on
Dord. The original shared core is untouched. -/

open CovarianceTransport
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

structure FirstSourceInput (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) : Prop where
  stage : StageSuccessor.Input P Mn G
  successor : IsActualSuccessor D P Mn G G'
  lift : ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
      (CcT k)
  range : ∃ Dord nMax hMax npad : ℕ, Mn.A = succAlphabet nMax hMax Mn.p npad ∧
    Mn.N + Dord ≤ nMax ∧
    (∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)), Dord < d →
        G.fam.flux p c v u γ d I = fun _ _ _ => 0) ∧
    (∀ h, StagePath G h → h ≤ hMax ∧ h ≤ depth) ∧
    max (Mn.N + Dord) (2 * Mn.p) + Dm + 2 ≤ Mn.sX ∧
    max (Mn.N + Dord) (2 * Mn.p) + Dm + 2 ≤ Mn.sZ
  edge : ∃ k : InvConsts, G.IsContextCertified k ∧ G.IsSlotTransverse ∧
    ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1 ∧ compReserve k v.1 ≤ 2
  stream : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ
  history : ∃ Mtop : ℕ, StageHistoryInvariant G Mtop
  start : IsCarrierStart D.α D.q D.Λ b 1 1 j₀
  alpha_pos : 0 < D.α
  q_gt : 1 < D.q

def FirstSourceIdentityStatement' : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    FirstSourceInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (ta tb : ℝ) (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc ta tb,
        ContDiff ℝ (K : ℕ) (fun x => g t x v) ∧ IsZ2Periodic (fun x => g t x v)) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2,
      diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 g v t x =
        -covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
