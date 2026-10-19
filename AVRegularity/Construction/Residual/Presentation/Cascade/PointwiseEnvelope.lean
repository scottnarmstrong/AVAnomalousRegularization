-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.Construction.Residual.Presentation.Cascade.Swap
import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFineLift
import AVRegularity.IterationPassage.PassageJetClausesOfBounds
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
import AVRegularity.EntryTerminal.Ingredients.ErrorEnergy.ResidualAssembly
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.TerminalForced
import AVRegularity.Proofs.WeakGen.Residual.Equation.IncomingPassage
import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The filter-defect form from the rows of the successor** (generic over
the stages and the fibres).

`FilterDefectForm` is about the readout `𝖱` of the rows
`rootFluxDefect … v'` of the successor `G'` to the rows of `G`. Here:

* `readout_isFluxRealization`: the readout of a realization of the rows realizes the readout
  of the rows, for general fibres `hr` (the terminal `readout_isFluxRealization_scalar` is for
  scalar fibres, where the root casts are trivial);
* `filterDefectForm_of_rows`: smooth periodic rows with a realized mass bound `Y` in the
  masses `σ` of `G'` give `FilterDefectForm … (√C_f · Y)` in the masses `π` of `G`, under the
  three facts of the readout (`readout_fluxMassLe`): the parent of a component of `G'` is in `G`,
  the weight of a child against its parent is at most `1`, and a parent has at most `C_f`
  children.

The degenerate cases are included: no component of `G'` (the readout is `0`); one child per parent
(`C_f = 1`); `Y = 0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

private theorem zero_carrier_jet_ae' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) :
    (0 : TorusHk k E).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube]
      (fun _ => 0) := by
  filter_upwards [KernelEnergy.torusHk_toFunction_jet_ae (0 : TorusHk k E) (valueIndex2 k),
    (Lp.coeFn_zero (E := E) (p := 2) (μ := volume.restrict unitCube))] with x hx hz
  exact hx.trans hz

private theorem root_cast_value_ae' {r r' k : ℕ} (heq : r = r')
    (W : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr r)))
    (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => hr r))
    (hf : W.toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube] f) :
    (cast (congrArg (fun n => TorusHk k (PiLp 2 (fun _ : Fin 2 => hr n))) heq) W).toFunction.jet
      (valueIndex2 k) =ᵐ[volume.restrict unitCube]
        (fun x => cast (congrArg (fun n => PiLp 2 (fun _ : Fin 2 => hr n)) heq) (f x)) := by
  subst r'
  exact hf

/-- **The readout of a realization realizes the readout** (general fibres). -/
theorem readout_isFluxRealization {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ)
    (I : Set ℝ) (F : ∀ c : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr c.1.root))
    (Fk : ∀ c : CompIn S', ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => hr c.1.root)))
    (hF : IsFluxRealization (ι := CompIn S') (h := fun c => hr c.1.root) K I F Fk) :
    IsFluxRealization (ι := CompIn S) (h := fun v => hr v.1.root) K I
      (readoutFlux (hr := hr) m E η (fun _ => True) F)
      (fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η K
        (fun c => Fk c t) v) := by
  classical
  intro v t ht
  unfold succReadout readoutFlux
  apply KernelEnergy.torusJet_sum_ae_of_eq
  intro c
  by_cases hp : compParent m c.1 = v.1
  · simp only [hp, and_true, ↓reduceDIte]
    have hc := root_cast_value_ae'
      ((compParent_root m c.1).symm.trans (congrArg Comp.root hp)) (Fk c t) (F c t) (hF c t ht)
    exact (KernelEnergy.torusJet_smul_ae (E ^ (η * (compWord m c.1).length))
      (cast (congrArg (fun n => TorusHk K (PiLp 2 (fun _ : Fin 2 => hr n)))
        ((compParent_root m c.1).symm.trans (congrArg Comp.root hp))) (Fk c t))
      (valueIndex2 K)).trans (hc.mono fun _ h => congrArg _ h)
  · simp only [hp, false_and, ↓reduceDIte]
    exact zero_carrier_jet_ae' K

/-- **The filter-defect form from the rows of the successor.** -/
theorem filterDefectForm_of_rows (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (G G' : GenStage D hr Dm b j₀) (m p kc : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (π : CompIn G.comps → ℝ)
    (σ : CompIn G'.comps → ℝ) (tp tf ρ Y Cf : ℝ) (hν : 0 < D.κ (m - 1)) (hE : 0 ≤ E)
    (hCf : 0 ≤ Cf) (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c)
    (hparent : ∀ c : CompIn G'.comps, compParent m c.1 ∈ G.comps)
    (hentry : ∀ (v : CompIn G.comps) (c : CompIn G'.comps), compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ * E ^ (η₀ * (compWord m c.1).length) ≤ 1)
    (hfiber : ∀ v : CompIn G.comps,
      ((Finset.univ : Finset (CompIn G'.comps)).filter fun c => compParent m c.1 = v.1).card ≤
        Cf)
    (hsm : ∀ v' : CompIn G'.comps, ∀ t ∈ Set.Icc tp tf,
      ContDiff ℝ ((kc + 2 * p : ℕ) : ℕ∞)
          (fun y => rootFluxDefect P seedK freshK φ₀ G G' aZ v' t y) ∧
        IsZ2Periodic (fun y => rootFluxDefect P seedK freshK φ₀ G G' aZ v' t y))
    (hrows : HasFluxBound (ι := CompIn G'.comps) (h := fun v => hr v.1.root) (kc + 2 * p)
      (Set.Icc tp tf) (D.κ (m - 1)) ρ σ
      (fun v' t y => rootFluxDefect P seedK freshK φ₀ G G' aZ v' t y) Y) :
    FilterDefectForm P seedK freshK φ₀ G G' m p kc E η₀ aZ π tp tf ρ (Real.sqrt Cf * Y) := by
  refine ⟨fun v t ht => ?_, ?_⟩
  · have hro := readoutFlux_smooth (hr := hr) m E η₀ (S := G.comps) (S' := G'.comps)
      (fun _ => True)
      (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') t (kc + 2 * p)
      (fun v' => hsm v' t ht) v
    refine ⟨PiLp.contDiff_ofLp.comp hro.1, ?_⟩
    intro k y
    have := hro.2 k y
    unfold filterReadoutDefect
    simp only [this]
  · obtain ⟨Fk, hreal, hmass⟩ := hrows
    exact ⟨fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η₀
        (kc + 2 * p) (fun u => Fk u t) v,
      readout_isFluxRealization m E η₀ _ _ Fk hreal,
      readout_fluxMassLe (hr := hr) m E η₀ (D.κ (m - 1)) ρ Cf Y (Set.Icc tp tf) hν hE hCf π σ
        hπ hσ hparent hentry hfiber Fk hmass⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Analysis.Convolution
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The kernels of the actual successor, and the filter-defect form of an actual successor
from named inputs** (generic over the stages).

* `kernelOf_property`: a property of kernels that holds for the kernel of every identity of `G`
  and for the fresh kernel of the level `G.level - 1` holds for the kernel of every identity of
  the actual successor `G'` (`actual_successor_kernel_key_property`: the kernel key of an identity
  of `G'` is the key of an identity of `G` or the fresh key).
* `freshWidth_eq`: the fresh kernel born at the level `m - 1` has the width
  `ρ E^{σ₀}`, `ρ = rhoEnh D c_r m`, `E = ε_{m-1}` (the fresh ratio of `succFilterPrice`).
* the join of the row mass (`rootFlux_hasFluxBound'`) and the readout
  (`filterDefectForm_of_rows`) for an actual successor, with the kernel facts stated on `G` and on
  the fresh kernel only, gives `FilterDefectForm … (√C_f · (q^L · M_c · θ · E_n))`.

The degenerate cases are included: `G` without identities (only the fresh kernel is asked);
`L = 0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **A property of the kernels of `G` and of the fresh kernel passes to the kernels of the actual
successor.** -/
theorem kernelOf_property (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (G G' : GenStage D hr Dm b j₀) (hactual : IsActualSuccessor D P Mn G G')
    (Q : KernelSpec → Prop)
    (hold : ∀ v u (γ : G.fam.Γ v u), Q (G.kernelOf P seedK freshK v u γ))
    (hfresh : Q (freshK (G.level - 1))) :
    ∀ v u (γ : G'.fam.Γ v u), Q (G'.kernelOf P seedK freshK v u γ) := by
  have h := Construction.Preservation.FullLift.actual_successor_kernel_key_property P Mn G G'
    hactual (fun key => Q (match key with
      | .seed i => seedK i
      | .fresh i => freshK i)) (fun v u γ => hold v u γ) hfresh
  exact fun v u γ => h v u γ

/-- The fresh kernel born at the level `m - 1` has the width `rhoEnh D c_r m · ε_{m-1}^{σ₀}`. -/
theorem freshWidth_eq (D : OCData) (cr σ₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    freshWidth D cr σ₀ (m - 1) = rhoEnh D cr m * D.eps (m - 1) ^ σ₀ := by
  unfold freshWidth freshLength rhoEnh
  rw [show m - 1 + 1 = m by omega]

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Mean-flux identification at a frame from the two readout smoothness clauses. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀)

/-- The exact two smoothness clauses consumed by the polynomial mean-flux split. -/
def ReadoutSmooth : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf,
    ContDiff ℝ ((2 * F.p : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux (S := F.G.comps) F.m
      (D.eps (F.m - 1)) F.η₀ (fun _ => True)
      (fun v' s y' => rootFluxDefect F.P F.seedK F.freshK F.φ₀ F.G F.G' F.aZ v' s y') v t y)) ∧
    ContDiff ℝ ((2 * F.p : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux (S := F.G.comps) F.m
      (D.eps (F.m - 1)) F.η₀ (fun c' => ¬ IsRetained F.m F.H F.J c')
      (fun v' s y' => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ F.G' F.Gr F.aY v' s y') v t y))

/-- Identification uses the realizations pointwise in time and the value-jet subtraction API. -/
theorem meanFlux_of_readoutSmooth (kc : ℕ) (hsm : ReadoutSmooth F) :
    MeanFluxStatement F kc := by
  intro F1 F2 F3 hreal v t ht
  obtain ⟨h1, h2, h3⟩ := hreal
  have e1 := h1 v t ht
  have e2 := h2 v t ht
  have e3 := h3 v t ht
  filter_upwards [jet_sub_ae (F1 v t - F3 v t) (F2 v t), jet_sub_ae (F1 v t) (F3 v t), e1, e2, e3]
    with y hs1 hs2 a1 a2 a3
  have hs := menuMeanFluxSplit (Mn := F.Mn) F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr
    F.m F.N F.p F.depth F.H F.J (D.eps (F.m - 1)) F.η₀ F.CcT F.aZ F.aY v t
    (hsm v t ht).1 (hsm v t ht).2 y
  change (F1 v t - F3 v t - F2 v t).toFunction.jet (valueIndex2 kc) y = _
  change _ = toFluxL (menuMeanFluxF F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ
    (upsilonFlux F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m F.H F.J
      (D.eps (F.m - 1)) F.η₀ F.aZ F.aY) v t y)
  rw [hs1, hs2, a1, a2, a3, hs]
  simp [toFluxL, WithLp.toLp_sub]

/-- Both readouts have the required smoothness from a cascade certificate and the auxiliary floor. -/
theorem readoutSmooth_of_certificate {kI : InvConsts} {M : ℕ}
    (hcert : F.G'.IsContextCertified kI) (hST : F.G'.IsSlotTransverse)
    (hnat : F.G'.IsNatural M) (hSH : F.G'.IsShiftInvariant)
    (hlev : 1 ≤ F.G'.level) (hj : j₀ ≤ F.G'.level) (hb : 0 < b)
    (hε : 0 < D.eps (F.G'.level - 1)) (hres : ∀ v : CompIn F.G'.comps, 0 ≤ compReserve kI v.1)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφsupp : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hK : 2 * F.p + Dm ≤ F.Naux) : ReadoutSmooth F := by
  intro v t ht
  have hcoef := fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) (d : ℕ) =>
    And.intro
      (Construction.Preservation.FullLift.native_physCoeff_all_order_smooth hcert hST hnat hlev
        hj hb hε t t v u γ (hres v) ((compReserve_le_one' kI v.1).trans (by norm_num))
        (2 * F.p) d t ⟨le_rfl, le_rfl⟩)
      (Construction.Preservation.Buffer.native_physCoeff_periodic hnat hSH v u γ d t)
  have hZ : ∀ u : CompIn F.G.comps,
      ContDiff ℝ ((2 * F.p + Dm : ℕ) : ℕ∞) (fun y => F.aZ t y u) ∧
        IsZ2Periodic (fun y => F.aZ t y u) := fun u => by
    obtain ⟨-, h1, h2, -⟩ := F.readout u t ht
    exact ⟨(by exact_mod_cast h1 : ContDiff ℝ (F.Naux : ℕ∞) _).of_le
      (by exact_mod_cast hK), h2⟩
  have hY : ∀ u : CompIn F.Gr.comps,
      ContDiff ℝ ((2 * F.p + Dm : ℕ) : ℕ∞) (fun y => F.aY t y u) ∧
        IsZ2Periodic (fun y => F.aY t y u) := fun u => by
    obtain ⟨-, h1, h2, -⟩ := F.retained u t ht
    exact ⟨(by exact_mod_cast h1 : ContDiff ℝ (F.Naux : ℕ∞) _).of_le
      (by exact_mod_cast hK), h2⟩
  have hroot := rootFluxDefect_smooth F.P F.seedK F.freshK F.φ₀ hφs hφsupp F.G F.G' F.aZ
    t (2 * F.p) hcoef hZ
  have homit := omittedFluxClassical_smooth F.P F.seedK F.freshK F.φ₀ hφs hφsupp F.G' F.Gr F.aY
    t (2 * F.p) hcoef hY
  have hro1 := readoutFlux_smooth (hr := hr) F.m (D.eps (F.m - 1)) F.η₀
    (S := F.G.comps) (S' := F.G'.comps) (fun _ => True)
    (fun v' s y' => rootFluxDefect F.P F.seedK F.freshK F.φ₀ F.G F.G' F.aZ v' s y') t
    (2 * F.p) hroot v
  have hro2 := readoutFlux_smooth (hr := hr) F.m (D.eps (F.m - 1)) F.η₀
    (S := F.G.comps) (S' := F.G'.comps) (fun c' => ¬ IsRetained F.m F.H F.J c')
    (fun v' s y' => omittedFluxClassical F.P F.seedK F.freshK F.φ₀ F.G' F.Gr F.aY v' s y') t
    (2 * F.p) homit v
  exact ⟨PiLp.contDiff_ofLp.comp hro1.1, PiLp.contDiff_ofLp.comp hro2.1⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The reconstruction bound at every context with a degenerate window (the degenerate-window case
at the context)** (cascade side of the bill residual).

A context of the bill has `t_p ≤ t_f` only, and `succPrefix_recon` asks `t_p < t_f`.

* `frameReconAt_degenerate_of_fineLift`: at a frame with `F.tf = F.tp` whose stage has depth
  at most `F.depth`, the lift step at an order `K₀ ≥ D_m·R − 1` (`FrameFineLiftAt`) gives
  `FrameReconAt` whenever the bound `C·𝔅·A_in` is nonnegative: the slots are the descending slots
  `D_m·(R − rank v)` of the depth rank (`isDescending_descSlots`), and the realization of the
  lifted field at the single time `t_p` is the truncation of the representative of the lift step.
* `succPrefix_reconDegenerate`: in the common prefix form, at every context of level `≥ m_*`
  with `t_f = t_p`, at the frame of every lifted field with classical representatives whose
  lifted classical field is jointly measurable on the window, `FrameReconAt` for every coarse
  order, every rate, every flux constant and every `C ≥ 0`. The order `D_m·R` of the lift step
  is paid by the order floor (`D_m·R + 1 + N + 2p ≤ succReconFloor ≤ N_aux`).

An empty component family, `A_in = 0` and `C = 0` are allowed; for `R = 0` all slots are `0`. -/

section Frame

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The bill of the reconstruction is nonnegative. -/
theorem succReconBill_nonneg (G : GenStage D hr Dm b j₀) (m : ℕ) (cr c σ₀ η : ℝ)
    (p N Lc Acl J H : ℕ) (tp tf θ₁ θ₂ : ℝ) (hE : 0 ≤ D.eps (m - 1)) (he : 0 ≤ D.eps m)
    (hcr : 0 ≤ cr) : 0 ≤ succReconBill D G m cr c σ₀ η p N Lc Acl J H tp tf θ₁ θ₂ := by
  have hρ : 0 ≤ rhoEnh D cr m := mul_nonneg hcr (Real.sqrt_nonneg _)
  have hω : 0 ≤ (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ a' : Fin 2,
      |covPrimitive D m t a a'|) / rhoEnh D cr m ^ 2 :=
    div_nonneg (Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)
  have hεc : 0 ≤ ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D cr m :=
    div_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) hρ
  have hεo : 0 ≤ max (D.eps (m - 1) ^ σ₀)
      (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rhoEnh D cr m) :=
    (Real.rpow_nonneg hE _).trans (le_max_left _ _)
  have hZcl : 0 ≤ Real.sqrt (tf - tp) / Real.sqrt (D.cellScaleSq m) *
      (D.eps m / rhoEnh D cr m) ^ Acl :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (pow_nonneg (div_nonneg he hρ) _)
  unfold succReconBill succCovPrice succFilterPrice succFrontPrice
  exact add_nonneg (add_nonneg
    (mul_nonneg (Real.rpow_nonneg hE _) (add_nonneg (add_nonneg
      (add_nonneg (pow_nonneg hω _) (pow_nonneg hω _)) (pow_nonneg hεo _))
      (add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _))))
    (mul_nonneg (pow_nonneg hεc _) (add_nonneg zero_le_one hZcl)))
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le)

/-- **The reconstruction bound at a frame with a degenerate window from the lift step** at an order
`K₀ ≥ D_m·R − 1`. -/
theorem frameReconAt_degenerate_of_fineLift (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (htt : F.tf = F.tp) (hdepth : F.G.fam.HasDepthAtMost F.depth) {c₀' : ℝ} {K₀ : ℕ}
    {Ain' C' : ℝ} (hK₀ : Dm * F.depth ≤ K₀ + 1) (hL : FrameFineLiftAt F law c₀' K₀ Ain' C')
    (kc : ℕ) (c₀ cr c σ₀ : ℝ) (Lc Acl : ℕ) (θ₁ θ₂ Ain Cfl C : ℝ)
    (hX : 0 ≤ C * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ *
      Ain) :
    FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl C := by
  obtain ⟨Û, ⟨-, hval, -⟩, -⟩ := hL
  have hle : ∀ v, descSlots F.G.fam F.depth Dm v ≤ K₀ + 1 := fun v =>
    (descSlots_le F.G.fam F.depth Dm v).trans hK₀
  have hmax : ∀ v u (γ : F.G.fam.Γ v u), (F.G.fam.identity v u γ).maxOrder ≤ Dm :=
    fun v u γ => (F.G.fam.identity v u γ).le_D
  refine frameReconAt_degenerate F law htt (descSlots F.G.fam F.depth Dm)
    (isDescending_descSlots F.G.fam hdepth hmax)
    (fun v => truncateTorusHk (hle v) (Û v F.tp)) (fun v => ?_) kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain
    Cfl C hX
  exact (IterationPassage.torus_truncate_value_ae (hle v) (Û v F.tp)).trans
    (hval v F.tp ⟨le_rfl, htt.ge⟩)

end Frame

/-- **The reconstruction bound at every context of level `≥ m_*` with a degenerate window
`t_f = t_p`**, at the frame of every lifted field with classical representatives whose lifted
classical field is jointly measurable on the window. -/
def ReconDegCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl Lc : ℕ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tf = c.tp →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) →
    ∀ (kc : ℕ) (cg Cfl C : ℝ), 0 ≤ C →
      FrameReconAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kc kI.c₀ kI.cr cg σ₀ Lc Acl
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        c.Ain Cfl C

/-- **The reconstruction bound on a degenerate window in the common prefix form**; the constant is
the level `m_*`. -/
theorem succPrefix_reconDegenerate (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconDegCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x) := by
  have h1 := succPrefix_fineLiftAt α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ _ _ _ _ _ _ _ => succSchedD D₀ N p (H + 1) * succSchedR r₀ J H)
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hfl, -, hpk⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 ≤ kI.cr := by rw [hkI.2.1]; exact hfacts.hcr.le
  -- the order `D_m·R` of the lift step is paid by the order floor
  have hfloor : succSchedD D₀ N p (H + 1) * succSchedR r₀ J H + 1 + N + 2 * p ≤ Naux := by
    have h := hfacts.recon
    unfold succReconFloor at h
    have h2 : 2 * p ≤ max (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
        ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p) :=
      le_trans (by omega) (le_max_left _ _)
    have h3 : succSchedD D₀ N p (H + 1) * succSchedR r₀ J H ≤
        2 * succSchedD D₀ N p (H + 1) * succSchedR r₀ J H := by
      rw [Nat.mul_assoc]
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    omega
  refine ⟨max x.1.2 x.2.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm htt CcT PZ aRep û hlift aZ aY hZ hY hmeas kc cg Cfl C hC
  have hm1 : x.1.2 ≤ c.m := le_trans (le_max_left _ _) hm
  have hm2 : x.2.2 ≤ c.m := le_trans (le_max_right _ _) hm
  obtain ⟨hgeom, -, -⟩ := hpk (by omega : 0 + N + 2 * p ≤ Naux) c hm2
  have hL := hfl hfloor c hm1 CcT PZ aRep û hlift aZ aY hZ hY hmeas
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hfacts.hΛ
  have hE : 0 ≤ c.D.eps (c.m - 1) := (Scales.epsilon_basic (m := c.m - 1) hqD hΛD).1.le
  have he : 0 ≤ c.D.eps c.m := (Scales.epsilon_basic (m := c.m) hqD hΛD).1.le
  have hbill := succReconBill_nonneg c.G c.m kI.cr cg σ₀ (succEta0 α q s) p N Lc Acl J H
    c.tp c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
    (succTheta2 α q s σ₀ (succDstar D₀ N p H)) hE he hcr
  have hA : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  exact frameReconAt_degenerate_of_fineLift (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
    htt hgeom.2.2.2.2.1 (Nat.le_succ _) hL kc kI.c₀ kI.cr cg σ₀ Lc Acl _ _ c.Ain Cfl C
    (mul_nonneg (mul_nonneg hC hbill) hA)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The initial error at the bill context**.

`initialError`: `InitialErrorStatement`. The lifted field at `t_p` is the truncation of
`P Z(t_p)` (the quiet entrance, `uhat_eq_trunc`), so
`‖U(t_p) - û(t_p)‖ ≤ ‖P_reg f - U(t_p)‖ + ‖P Z(t_p) - P_reg f‖`: the first by clause 3 of the
common preparation (`w = 1`), the second by the covariance-filter estimate and clause 4.

For `f = 0` the bound is `0`; an empty family is allowed. -/

/-- The weighted norm (plain weights) of a difference is symmetric. -/
theorem weightedNorm_sub_comm {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (X Y : ∀ v : CompIn S, TorusHk k (hr v.1.root)) :
    weightedNorm ρ π (fun _ => 1) (fun v => Y v - X v) =
      weightedNorm ρ π (fun _ => 1) (fun v => X v - Y v) := by
  have h : (fun v => Y v - X v) = -(fun v => X v - Y v) := by
    funext v
    simp
  simp only [weightedNorm, one_pow, div_one]
  rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => k) ρ π hπ
      (fun v => Y v - X v),
    ← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => k) ρ π hπ
      (fun v => X v - Y v), h]
  rw [ContinuousLinearMap.map_neg, norm_neg]

/-- The arithmetic of the initial error. -/
theorem initial_arith {X A B R n e W CQ : ℝ} (hXd : X ≤ B + A) (hA : A ≤ e * n)
    (hB : B ≤ W * R) (hR : R ≤ CQ * n) (hW : 0 ≤ W) : X ≤ (e + W * CQ) * n := by
  nlinarith [mul_le_mul_of_nonneg_left hR hW]

section Context

open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- `t_p ≤ t_f` at the context. -/
theorem tp_le_tf' : c.tp ≤ c.tf := by
  have h := c.hprep.2.2.1
  rw [c.hlevel, c.hα, c.hq, c.hΛ] at h
  linarith [c.htf]

/-- **The initial error** (`InitialErrorStatement`). -/
theorem initialError (Cfil ω : ℝ) : InitialErrorStatement c Cfil ω := by
  intro hsc hC hω U Uw Uk hU CcT PZ aRep û hlift hvan hIV hfilt
  obtain ⟨Qh, hQ, hP, -⟩ := hIV
  have htp := tp_le_tf' c
  have hu : (fun v => U v c.tp - û v c.tp) = fun v => U v c.tp -
      truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp) := by
    funext v
    rw [uhat_eq_trunc c hlift hvan hsc htp v]
  rw [hu]
  obtain ⟨-, -, -, -, hw⟩ := c.hprep
  obtain ⟨h3, -, h4, -⟩ := hw (fun _ => 1) (Or.inl rfl) c.f
  have h3' := h3 U Uw Uk (by rw [c.hlevel]; exact hU)
  have hl : c.G.level = c.m := c.hlevel
  have h3'' := h3'.trans (le_of_eq (by rw [hl]))
  have h4' := (le_of_eq (by rw [hl])).trans h4
  have hfil := hfilt Qh hQ hP
  have htri := AVRegularity.EntryTerminal.Route.weightedNorm_sub_le (1 : ℝ) (c.G.mass c.law)
    hsc.hπ (fun v => truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp))
    (fun v => truncateTorusHk (Nat.zero_le Nout) (c.Preg c.f v)) (fun v => U v c.tp)
  exact (weightedNorm_sub_comm 1 (c.G.mass c.law) hsc.hπ (fun v => U v c.tp)
    (fun v => truncateTorusHk (Nat.zero_le (Naux - 2 * p)) (PZ v c.tp))).symm.le.trans
    (initial_arith htri h3'' hfil h4' (mul_nonneg hC (pow_nonneg hω _)))

end Context

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open scoped ENNReal
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Providers.WeakGen.Residual
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The error energy at the bill context**.

The error `U - û` solves the regularized system on `[t_p, t_f]` with the initial value
`U(t_p) - û(t_p)` and the forcing `(-R, -q)`: `U` restarts at `t_p`
(`kernelWeakSolutionTorus_restart`) and the two solutions subtract
(`kernelWeakSolutionTorus_sub`). The forced energy of the stage at order
`0` (`stage_forced_energy`) bounds its strong energy, and `obsErrorNorm` is at most twice the
strong energy (`obsErrorNorm_le`).

For a zero residual (`resBound = 0`) and for `t_p = t_f` the statement is trivially true. -/

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- **The error solves the system with the forcing `(-R, -q)` from `t_p`.** -/
theorem diff_solution
    {U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)}
    {Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root)}
    {Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)}
    (hU : c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
      φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
      U Uw Uk)
    {û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)}
    {ŵ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root)}
    {ŷ : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)}
    {Rres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {qres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)}
    (hû : c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
      φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf (fun v => û v c.tp) Rres qres û ŵ ŷ)
    (hs : c.s₀ ≤ c.tp) (htp : c.tp ≤ c.tf) :
    c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
      φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf
      (fun v => U v c.tp - û v c.tp) (fun v t => (-1 : ℝ) • Rres v t)
      (fun v t => (-1 : ℝ) • qres v t) (fun v t => U v t - û v t)
      (fun v t => Uw v t - ŵ v t) (fun v u γ t => Uk v u γ t - ŷ v u γ t) := by
  unfold GenStage.IsRegSolution at hU hû ⊢
  have hUr := kernelWeakSolutionTorus_restart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU c.tp ⟨hs, htp⟩
  obtain ⟨hv, -, -, ⟨V, hV⟩, -⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data
    (c.D.hΦ c.m) c.tp c.tf
  exact kernelWeakSolutionTorus_sub _ _ _ _ _ _ _ _ _ htp
    (fun s' hs' => ⟨(hv s' hs').continuous, max V 0, le_max_right _ _,
      fun x => (hV s' hs' x).trans (le_max_left _ _)⟩)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hUr hû (fun _ => rfl) (fun i t => by simp)
    (fun i t => by simp) (fun _ _ _ => rfl)
    (fun _ => Filter.Eventually.of_forall fun _ => rfl) (fun _ _ _ _ => rfl)

/-- The diffusivity of the stage is `κ_m` at the level `m ≤ n < M`. -/
theorem kap_level : c.D.kap c.G.level = c.D.κ c.m := by
  have h1 : c.m ≤ c.D.term := by
    rw [c.hterm]
    exact c.hmn.trans c.hnM.le
  simp [OCData.kap, c.hlevel, min_eq_left h1]

/-- `t_A ≤ s₀` at the context. -/
theorem tA_le_s0 (hΛ1 : 1 ≤ Λ) : c.tA ≤ c.s₀ := by
  have := Construction.Stream.ocTau_pos (α := α) (q := q) (m := c.m) hΛ1
  linarith [c.hs₀]

/-- **The forced energy of the stage at order `0`** for a solution of the system on
`[t_p, t_f]` with forcing `(F, g)`. -/
theorem stage_bound (hsc : StageScale c) (htA : c.tA ≤ c.tp) (htp : c.tp ≤ c.tf)
    (f0 : ∀ v : CompIn c.G.comps, TorusHk 0 (hr v.1.root))
    (F : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (g Δ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Δw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Δy : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (hΔ : c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
      c.freshK φ₀ hφ₀ (c.D.kap c.G.level) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf f0 F g Δ Δw Δy)
    (hFm : ∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc c.tp c.tf)))
    (hgm : ∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc c.tp c.tf)))
    (X : ℝ) (hX : 0 ≤ X)
    (hFw : ∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc c.tp c.tf, ∑ v, ENNReal.ofReal (c.G.mass c.law v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ r : Fin 2,
          ‖rhoStar c.D kI.c₀ c.G.level ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (c.D.kap c.G.level * X ^ 2))
    (hgw : ∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc c.tp c.tf, (∑ v, ENNReal.ofReal (c.G.mass c.law v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube,
          ‖rhoStar c.D kI.c₀ c.G.level ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    strongEnergy (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (c.D.kap c.G.level)
        (c.G.mass c.law) c.tp c.tf Δ Δw ≤
      ENNReal.ofReal ((3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0) *
        (Real.sqrt (massNormSq (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048))
          (c.G.mass c.law) (fun v => (f0 v).val)) + X)) := by
  have hρ : 0 < min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048) := lt_min hsc.hR (by norm_num)
  have hρ2 := min_le_right (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)
  exact AVRegularity.EntryTerminal.ForcedEnergy.stage_forced_energy c.law
    (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ c.Mnat kI c.tA
    c.tf _ _ c.G c.hinv hsc.hres0 hsc.hq hsc.hΛ hsc.hi hsc.hj hsc.hb hsc.hε (htA.trans htp)
    hsc.hν _ hsc.hR hsc.hRε rfl _ hρ (min_le_left _ _) hsc.hD hsc.hθ 0 (Nat.zero_le _) c.tp htA
    htp (c.D.hΦ c.m) 0 1 le_rfl one_pos (by rw [div_one]; linarith)
    (by rw [zero_mul, zero_mul]; exact div_nonneg hsc.hν.le (by norm_num))
    (fun _ _ l hl1 hl0 _ => absurd hl1 (by omega)) f0 F g Δ Δw Δy hΔ hFm hgm X hX hFw hgw

/-- The forcing words of `(-R, -q)` at the stage radius, from the residual norm. -/
theorem forcing_words (hsc : StageScale c)
    (Rres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)) (resBound : ℝ)
    (hres : residualNorm (c.D.κ c.m) (c.G.mass c.law) (Set.Icc c.tp c.tf)
        (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
        (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤ ENNReal.ofReal resBound) :
    (∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc c.tp c.tf, ∑ v, ENNReal.ofReal (c.G.mass c.law v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ r : Fin 2,
          ‖rhoStar c.D kI.c₀ c.G.level ^ j.val •
            (torusJetOrder ((-1 : ℝ) • Rres v t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (c.D.kap c.G.level * (max 0 resBound) ^ 2)) ∧
    (∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc c.tp c.tf, (∑ v, ENNReal.ofReal (c.G.mass c.law v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube,
          ‖rhoStar c.D kI.c₀ c.G.level ^ j.val • torusJetOrder ((-1 : ℝ) • qres v t) j.val β x‖ₑ ^ 2) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (max 0 resBound)) := by
  have hkap := kap_level c
  have hν : 0 < c.D.κ c.m := by rw [← hkap]; exact hsc.hν
  have hX : 0 ≤ max 0 resBound := le_max_left _ _
  have hres' := hres
  unfold residualNorm at hres'
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact flux_words (c.D.κ c.m) _ (max 0 resBound) hν hX (c.G.mass c.law)
      (Set.Icc c.tp c.tf) Rres
      (le_self_add.trans (hres'.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))))
  · exact value_words _ (max 0 resBound) (c.G.mass c.law) (Set.Icc c.tp c.tf) qres
      (le_add_self.trans (hres'.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))))


/-- The last step: the strong energy bound gives the error norm bound. -/
theorem error_final (hsc : StageScale c)
    (Δ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)) (f1 : ∀ v : CompIn c.G.comps,
      TorusHk 0 (hr v.1.root))
    (Δw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (hΔw : ∀ v, MemLp (Δw v) 2 (volume.restrict (Set.Icc c.tp c.tf)))
    (X E₀ : ℝ)
    (hmain : strongEnergy (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (c.D.κ c.m)
        (c.G.mass c.law) c.tp c.tf Δ Δw ≤
      ENNReal.ofReal ((3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0) *
        (Real.sqrt (massNormSq (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048))
          (c.G.mass c.law) (fun v => (f1 v).val)) + X)))
    (hE0 : weightedNorm 1 (c.G.mass c.law) (fun _ => 1) f1 ≤ E₀) :
    obsErrorNorm (c.D.κ c.m) (c.G.mass c.law) (fun _ => 0) c.tp c.tf Δ Δw ≤
      ENNReal.ofReal (ErrConst * (E₀ + X)) := by
  have hkap := kap_level c
  have hπ : ∀ v, 0 < c.G.mass c.law v := fun v => by
    unfold GenStage.mass
    exact Construction.Preservation.Buffer.birth_compMass_pos hsc.hq hsc.hΛ c.law v.1
  have hν : 0 < c.D.κ c.m := by rw [← hkap]; exact hsc.hν
  have hwm : ∀ i, AEMeasurable (fun t => ENNReal.ofReal
      (gradFactorialNormSq (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (Δw i t).val))
      (volume.restrict (Set.Icc c.tp c.tf)) := fun i =>
    AVRegularity.EntryTerminal.Route.grad_aemeasurable _ (hΔw i)
  have hobs := obsErrorNorm_le (c.D.κ c.m) (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048))
    hν.le (c.G.mass c.law) hπ c.tp c.tf Δ Δw hwm
  have hwn : Real.sqrt (massNormSq (E := fun v : CompIn c.G.comps => hr v.1.root)
      (K := fun _ => 0) (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (c.G.mass c.law)
      (fun v => (f1 v).val)) = weightedNorm 1 (c.G.mass c.law) (fun _ => 1) f1 := by
    unfold weightedNorm massNormSq
    simp only [one_pow, div_one]
    congr 1
  rw [hwn] at hmain
  have hW0 := AVRegularity.EntryTerminal.ForcedEnergy.wordCount_nonneg 0
  refine hobs.trans ?_
  calc 2 * strongEnergy (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (c.D.κ c.m)
        (c.G.mass c.law) c.tp c.tf Δ Δw
      ≤ 2 * ENNReal.ofReal ((3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0) *
        (weightedNorm 1 (c.G.mass c.law) (fun _ => 1) f1 + X)) := mul_le_mul_right hmain _
    _ = ENNReal.ofReal (2 * ((3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0) *
        (weightedNorm 1 (c.G.mass c.law) (fun _ => 1) f1 + X))) := by
        have h2 : ENNReal.ofReal 2 = 2 := by simp
        rw [ENNReal.ofReal_mul (p := 2) (by norm_num), h2]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold ErrConst
        have h3 : 0 ≤ 3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0 := by linarith
        have := mul_le_mul_of_nonneg_left (add_le_add_right hE0 X) h3
        nlinarith [this]

/-- The strong energy of the error from the difference solution. -/
theorem error_stage (hsc : StageScale c) (htA : c.tA ≤ c.tp) (htp : c.tp ≤ c.tf)
    (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (ŵ : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
    (ŷ : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
      TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (Rres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qres : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (hΔ : c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
      c.freshK φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf
      (fun v => U v c.tp - û v c.tp) (fun v t => (-1 : ℝ) • Rres v t)
      (fun v t => (-1 : ℝ) • qres v t) (fun v t => U v t - û v t)
      (fun v t => Uw v t - ŵ v t) (fun v u γ t => Uk v u γ t - ŷ v u γ t))
    (hRm : ∀ v, AEStronglyMeasurable (Rres v) (volume.restrict (Set.Icc c.tp c.tf)))
    (hqm : ∀ v, AEStronglyMeasurable (qres v) (volume.restrict (Set.Icc c.tp c.tf)))
    (resBound : ℝ)
    (hres : residualNorm (c.D.κ c.m) (c.G.mass c.law) (Set.Icc c.tp c.tf)
        (fun t x k v => ((Rres v t).toFunction.jet (valueIndex2 0) x) k)
        (fun t x v => (qres v t).toFunction.jet (valueIndex2 0) x) ≤ ENNReal.ofReal resBound) :
    strongEnergy (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048)) (c.D.κ c.m)
        (c.G.mass c.law) c.tp c.tf (fun v t => U v t - û v t) (fun v t => Uw v t - ŵ v t) ≤
      ENNReal.ofReal ((3 + 8 * AVRegularity.EntryTerminal.ForcedEnergy.wordCount 0) *
        (Real.sqrt (massNormSq (min (rhoStar c.D kI.c₀ c.G.level) (1 / 2048))
          (c.G.mass c.law) (fun v => (U v c.tp - û v c.tp).val)) + max 0 resBound)) := by
  have hkap := kap_level c
  obtain ⟨hFw, hgw⟩ := forcing_words c hsc Rres qres resBound hres
  have hX : 0 ≤ max 0 resBound := le_max_left _ _
  have hΔ' : c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
      c.freshK φ₀ hφ₀ (c.D.kap c.G.level) (streamVel (c.D.Φ c.m)) 0 c.tp c.tf
      (fun v => U v c.tp - û v c.tp) (fun v t => (-1 : ℝ) • Rres v t)
      (fun v t => (-1 : ℝ) • qres v t) (fun v t => U v t - û v t)
      (fun v t => Uw v t - ŵ v t) (fun v u γ t => Uk v u γ t - ŷ v u γ t) := by
    rw [hkap]; exact hΔ
  have hmain := stage_bound c hsc htA htp (fun v => U v c.tp - û v c.tp)
    (fun v t => (-1 : ℝ) • Rres v t) (fun v t => (-1 : ℝ) • qres v t) (fun v t => U v t - û v t)
    (fun v t => Uw v t - ŵ v t) (fun v u γ t => Uk v u γ t - ŷ v u γ t)
    hΔ' (fun v => (hRm v).const_smul (-1 : ℝ)) (fun v => (hqm v).const_smul (-1 : ℝ))
    (max 0 resBound) hX hFw hgw
  rw [hkap] at hmain
  exact hmain

/-- **The error energy** (`ErrorEnergyStatement'`). -/
theorem errorEnergy : ErrorEnergyStatement' c := by
  intro hsc U Uw Uk hU û ŵ ŷ Rres qres hû hRm hqm resBound E₀ hres hE0
  have htp := tp_le_tf' c
  have hs0 : c.s₀ ≤ c.tp := c.hprep.2.1
  have hΛ1 : 1 ≤ Λ := by
    have := hsc.hΛ
    rw [c.hΛ] at this
    omega
  have htA := (tA_le_s0 c hΛ1).trans hs0
  have hΔ := diff_solution c hU hû hs0 htp
  have hmain := error_stage c hsc htA htp U Uw Uk û ŵ ŷ Rres qres hΔ hRm hqm resBound hres
  exact error_final c hsc _ (fun v => U v c.tp - û v c.tp) _ (fun v => hΔ.2.1 v)
    (max 0 resBound) E₀ hmain hE0

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The pointwise molecular envelope of a step stage of the cascade: the two general
lemmas** (cascade side of the bill residual).

* `step_higher_length`: the higher original identities of a step stage
  `G = G₁'.retained G₁.level H J` have length `≤ ρ_*(c₀, G.level)`, from the lengths of the
  stage `G₁` before it (`actual_successor_higher_lengths`; the body of
  `retained_pointwise_context_inputs` one stage back).
* `pointwise_of_estimate`: the shared producer's estimate (`context_stage_envelopes`) at
  a stage with its context input gives `IsSeedPointwiseMolecular law k G a t_f` at the constants
  `k` (weights `w = 1`).

Both are generic over the stage. For a stage without identities both are vacuous, and for a
window with `a > t_f` the inner domain is empty. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Higher lengths of a step stage.** `G₁` has the tags of `P`, the old lengths of `G₁`
fit `ρ`, and the fresh length of level `G₁.level - 1` fits `ρ`; then every identity of order
`≥ 3` of the retained successor has length `≤ ρ`. -/
theorem step_higher_length {P : ProvParams} {Mn : SuccMenu}
    {G₁ G₁' : GenStage D hr Dm b j₀} (hG : G₁.HasTags P)
    (hact : IsActualSuccessor D P Mn G₁ G₁') {ρ : ℝ}
    (hold : ∀ v u (γ : G₁.fam.Γ v u), 1 ≤ (G₁.fam.identity v u γ).record.birthExcess →
      (G₁.fam.identity v u γ).record.length ≤ ρ)
    (hfresh : P.Rb (G₁.level - 1) ≤ ρ) :
    ∀ v u (γ : (G₁'.retained G₁.level Mn.H Mn.J).fam.Γ v u),
      3 ≤ ((G₁'.retained G₁.level Mn.H Mn.J).fam.identity v u γ).maxOrder →
      ((G₁'.retained G₁.level Mn.H Mn.J).fam.identity v u γ).record.length ≤ ρ := by
  have hout := actual_successor_higher_lengths hG hact hold hfresh
  intro v u γ h3
  exact hout ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ h3

theorem markerConj_one' {ι : Type*} {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    {Dm : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h Dm P Ctx) :
    markerConj (fun _ => 1) F = F := by
  unfold markerConj
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]

/-- **The pointwise molecular envelope from the shared producer's estimate.** -/
theorem pointwise_of_estimate [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {pe : ContextEnvelopeParameters} (est : ContextEnvelopeEstimate pe)
    (G : GenStage D hr Dm b j₀) (kI : InvConsts)
    (hinput : ContextEnvelopeInput pe G kI kI.mEnv (rhoStar D kI.c₀ G.level))
    (hfloor : est.levelFloor ≤ G.level) (hCa : est.Ca ≤ kI.Ca)
    (hCm : ∀ j, est.Cm j ≤ kI.Cm j) (law : BirthLaw) (a tf : ℝ) :
    IsSeedPointwiseMolecular law kI G a tf := by
  intro K hK
  have h := est.bound hr D Dm j₀ b G kI kI.mEnv (rhoStar D kI.c₀ G.level) hinput hfloor hCa hCm
    law (Set.Icc a tf)
  have h1 := h (fun _ => 1) (fun _ => zero_lt_one)
  dsimp only at h1
  rw [markerConj_one' G.fam] at h1
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] at h1
  exact (h1 K hK).2.2.2

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
