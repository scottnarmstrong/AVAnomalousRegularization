-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.LiftBoundSplit
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFloors
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Jets
public import AVRegularity.Construction.Residual.Presentation.Cascade.FluxForms
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.SchurF
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import Mathlib.Data.Int.Star

section
section
@[expose] public noncomputable section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The measurability in time of the lifted field at a context

* `classicalRep_time_continuousOn`, `classicalRep_measurable`: classical representatives
  of a trajectory that is continuous in time in `H^K`, `K ≥ 2`, are continuous in time at every
  point (the sup bound `classicalRep_orderedDerivative_le` on the difference), hence jointly
  measurable.
* `aRep_measurable`: the coarse field `aRep` of a terminal context is jointly measurable on
  the window, from the energy step (`ReconEnergyAt`: `P_pZ` truncated is continuous in time).
* `liftMeasAt`: **measurability at a context**: every classical `Û` of the lifted field is a.e.
  strongly measurable in time (`menuLiftedRep_measurable` and the template
  `aesm_of_value`).

Degenerate cases: `t_p = a + T₀` (the window is a point); `N_T = 0` (no derivative of the coarse
field is used). -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **Classical representatives of a time-continuous trajectory are continuous in time at every
point.** -/
theorem classicalRep_time_continuousOn {K r : ℕ} (hr : r + 2 ≤ K) {I : Set ℝ}
    {W : ℝ → TorusHk K E} {a : ℝ → Vec 2 → E} (hW : ContinuousOn W I)
    (hrep : ∀ t ∈ I, IsClassicalRep (W t) (a t) r) (y : Vec 2) :
    ContinuousOn (fun t => a t y) I := by
  obtain ⟨C, -, hC⟩ :=
    CycleComparison.Reconstruction.classicalRep_orderedDerivative_le (E := E) K r hr
  intro t₀ ht₀
  have hW0 : Tendsto W (𝓝[I] t₀) (𝓝 (W t₀)) := hW t₀ ht₀
  rw [tendsto_iff_norm_sub_tendsto_zero] at hW0
  show Tendsto (fun t => a t y) (𝓝[I] t₀) (𝓝 (a t₀ y))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => C * ‖W t - W t₀‖) (𝓝[I] t₀) (𝓝 0) := by
    have h := hW0.const_mul C
    rwa [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h := hC (W t - W t₀) (fun x => a t x - a t₀ x)
    (CycleComparison.Reconstruction.isClassicalRep_sub (hrep t ht) (hrep t₀ ht₀)) 0
    (Nat.zero_le r) Fin.elim0 y
  have he : orderedDerivative (Fin.elim0 : DerivativeWord2 0) (fun x => a t x - a t₀ x) y =
      a t y - a t₀ y := by
    simp [orderedDerivative]
  rwa [he] at h

/-- **Classical representatives of a time-continuous trajectory are jointly measurable.** -/
theorem classicalRep_measurable {K r : ℕ} (hr : r + 2 ≤ K) {I : Set ℝ}
    {W : ℝ → TorusHk K E} {a : ℝ → Vec 2 → E} (hW : ContinuousOn W I)
    (hrep : ∀ t ∈ I, IsClassicalRep (W t) (a t) r) :
    Measurable (fun p : I × Vec 2 => a p.1.1 p.2) :=
  measurable_joint (T := I) (Y := Vec 2) (fun t y => a t.1 y)
    (fun t => (hrep t.1 t.2).2.1.continuous)
    (fun y => (continuousOn_iff_continuous_domRestrict.1
      (classicalRep_time_continuousOn hr hW hrep y)).measurable)

end Abstract

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The coarse field of a terminal context is jointly measurable on the window**. -/
theorem aRep_measurable
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) {Cs : ℝ}
    (hR : ReconEnergyAt c x kc ℓ hW Cs) (h2 : 2 ≤ kc + 1 + (A.NT + A.Dt)) :
    Measurable (fun p : Set.Icc c.tp (c.a + A.T₀) × Vec 2 => c.aRep p.1.1 p.2) := by
  refine measurable_pi_iff.2 fun v => ?_
  have hI : c.tp + rTobs c = c.a + A.T₀ := by simp only [rTobs]; ring
  have hc := hR.1 v
  rw [hI] at hc
  have h := classicalRep_measurable (r := 0) (W := reconW c kc hW v)
    (a := fun t y => c.aRep t y v) (by omega) hc (fun t ht =>
      Construction.Preservation.FullLift.classicalRep_truncate hW (Nat.zero_le _) (c.PZ v t)
        (fun y => c.aRep t y v) (rdJets_classicalRep_mono (c.lift.2.1 v t ht).2 (Nat.zero_le _)))
  exact h

/-- **(b2) at a context**: every classical `Û` of the lifted field is a.e. strongly measurable in
time on the window. -/
theorem liftMeasAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) {Cs : ℝ}
    (hR : ReconEnergyAt c x kc ℓ hW Cs) (hΛD : 1 ≤ c.D.Λ) (hζD : IsFastProfile c.D.ζ)
    (hbandD : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ)
    (h2 : 2 ≤ kc + 1 + (A.NT + A.Dt)) : TermLiftMeasAt c x := by
  intro Û hÛ v
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hNT : A.NT ≤ A.Khat Kout - 2 * A.pT := by omega
  have haC : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ContDiff ℝ ((A.NT : ℕ) : ℕ∞) (c.aRep t) :=
    fun t ht => contDiff_pi.2 fun w =>
      ((c.lift.2.1 w t ht).2.2.1).of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast hNT))
  have ham := aRep_measurable c x kc ℓ hW hR h2
  have hf := menuLiftedRep_measurable (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev c.CcT
    hΛD hζD hbandD sXT sZT c.lift.1 c.aRep c.tp (c.a + A.T₀) haC ham v
  have hval : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      (Û v t).toFunction.jet (valueIndex2 (fineOrder (A := A) + 1)) =ᵐ[volume.restrict
        AVenhance.unitCube] fun y =>
        menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v :=
    fun t ht => Construction.Preservation.FullLift.classicalRep_value_ae (Û v t) _ (hÛ v t ht)
  exact Construction.Residual.Presentation.Cascade.aesm_of_value c.tp (c.a + A.T₀) (Û v)
    (fun t y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v)
    hf hval

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **The strong energy of the readout at a terminal context, as data.**

The data behind `covGrad_ctx_energy`, with the strong energy bound, the square
integrability of the order-`K̂+1` readout and its a.e. truncation identity, stated for the radius
`termRho`. Used for the energy of the zero extension of the readout (`FilterEnergyStatement`).

Degenerate case: `f = 0` gives the energy bound `0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.CovGrad

/-- **The readout energy data.** -/
theorem readout_data (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid → ∀ cHP' : ℝ, ∃ M₀ : ℕ,
      ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
        {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ},
        M₀ ≤ M →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP' Cw
          Ce cker j₀ M), TermResAux c →
        (∀ v, 0 < c.Gw.mass c.lawW v) ∧ 0 < c.D.κ (M - 1) ∧
        strongEnergy (c.D.termRho cr M) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
          (eZr c) (eZrw c) ≤ ENNReal.ofReal (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
            (Real.sqrt 2 * max CP 0 * c.normF)) ∧
        (∀ v, MemLp (eZrw c v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
        (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
          truncateTorusHk (Nat.le_succ _) (eZrw c v t) = eZr c v t) := by
  obtain ⟨ΛL, hΛL, hL⟩ := energyLarge X
  obtain ⟨ΛS, hΛS, hS⟩ := energySolution X
  refine ⟨max ΛL ΛS, le_trans hΛL (le_max_left _ _), fun A hΛ hV cHP' => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hL A (le_trans (le_max_left _ _) hΛ) hV cHP'
  refine ⟨max M₀ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP Cw Ce cker j₀ M hM c x
  have hlarge := hM₀ (le_trans (le_max_left _ _) hM) c x
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hsolE : EnergySolutionAt c := hS A (le_trans (le_max_right _ _) hΛ) hM2 c x
  obtain ⟨-, -, hent⟩ := hlarge
  obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := c.data
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ128 : 128 ≤ A.Λ := le_trans hΛL (le_trans (le_max_left _ _) hΛ)
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < rRho c := Real.sqrt_pos.2 (mul_pos hν hh)
  have hπW : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hπT : ∀ w, 0 < (c.Gt'.retained M 1 A.RT).mass c.lawT w := fun w =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawT w.1
  have hsol := c.sol
  unfold GenStage.IsRegSolution at hsol
  obtain ⟨hcont, hmem, hae, -⟩ := hsol
  have hroots : ∀ v : CompIn c.Gw.comps, v.1.births = [] := c.weak.2.2.2.2.1
  have hlevel : c.Gw.level = M := c.weak.2.2.1
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, M ≤ e.scale := by
    intro v hv e he
    exact absurd he (by rw [hroots ⟨v, hv⟩]; simp)
  have hsub := retained_comps_subset_succExt c.succ hlevel
  have hM1 : 1 ≤ M := by omega
  have hread : strongEnergy (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
      (eZr c) (eZrw c) ≤
      ENNReal.ofReal (Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
        strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
          c.tp (c.a + A.T₀) c.Z c.Zw := by
    have hE0 : 0 ≤ c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1.le
    exact readout_strongEnergy_of_diagonal_entries (S := c.Gw.comps)
      (S' := (c.Gt'.retained M 1 A.RT).comps) M (c.D.eps (M - 1)) A.η₀ (rRho c)
      (c.D.κ (M - 1)) c.tp (c.a + A.T₀) (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) hE0
      (by positivity) (c.Gw.mass c.lawW) ((c.Gt'.retained M 1 A.RT).mass c.lawT) hπW hπT
      (fun w => readout_parent_mem hM1 hold (hsub w.2)) hent
      (fun v => by exact_mod_cast readout_indexed_fiber_card_le hM1 hold hsub v.1)
      c.Z c.Zw hmem
  have hTe : c.tp + rTobs c = c.a + A.T₀ := by
    unfold rTobs
    ring
  have hsolE' : strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
      c.tp (c.a + A.T₀) c.Z c.Zw ≤ ENNReal.ofReal (Real.sqrt 2 * max CP 0 * c.normF) := by
    have := hsolE
    unfold EnergySolutionAt at this
    rwa [hTe] at this
  have hen : strongEnergy (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
      (eZr c) (eZrw c) ≤ ENNReal.ofReal (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF)) := by
    refine hread.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl hsolE'
  have hRw : ∀ v, MemLp (eZrw c v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) :=
    fun v => AVRegularity.EntryTerminal.Ingredients.Recon.Energy.memLp_succReadout M _ _ c.Zw hmem v
  have hae' : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (eZrw c v t) = eZr c v t := by
    intro v
    have hall := ae_all_iff.2 hae
    filter_upwards [hall] with t ht
    simp only [eZrw, eZr]
    rw [AVRegularity.EntryTerminal.Ingredients.Recon.Energy.truncate_succReadout]
    congr 1
    funext v'
    exact ht v'
  have hE0 : 0 ≤ Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF) := by
    have : 0 ≤ c.normF := Real.sqrt_nonneg _
    positivity
  have hρe : rRho c = c.D.termRho cr M := by
    simp only [rRho, OCData.termRho, OCData.termB, OCData.termH, x.one, one_mul]
  rw [hρe] at hen
  exact ⟨hπW, hν, hen, hRw, hae'⟩

end AVRegularity.EntryTerminal.CovGrad
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation

/-! **`FilterRowMassStatement` from the five named input statements**.

The five statements are joined by `termFluxPrefix_and`; the constant is relabelled by
`prefix_map`, whose context-level implication is `filterRowMassAt_of_inputs` together with the
positivity facts of the context (`filter_ctx_facts`).

Degenerate cases: an empty window (the zero flux); `C = 0`. -/

section Facts

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The positivity facts of a context. -/
theorem filter_ctx_facts (x : TermResAux c) (hΛ : 128 ≤ A.Λ) :
    0 < c.D.eps M ∧ 0 < c.D.eps (M - 1) ∧ 0 < c.D.κ (M - 1) ∧ 0 < c.D.termRho cr M ∧
      ∀ i, 0 < c.Gt'.mass c.lawT i := by
  obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := c.data
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ
  have hkey : ∀ y : ℝ, cr * y = y := fun y => by rw [x.one, one_mul]
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  refine ⟨(Scales.epsilon_basic hq1 hΛD).1, (Scales.epsilon_basic hq1 hΛD).1, hν, ?_, fun i => ?_⟩
  · show 0 < cr * _
    rw [hkey]
    exact Real.sqrt_pos.2 (mul_pos hν hh)
  · exact Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawT i.1

end Facts

/-- **`FilterRowMassStatement` from the five input statements.** -/
theorem filterRowMass_of_inputs (hR : FilterRegStatement) (hW : FilterSchurWStatement)
    (hF : FilterSchurFStatement) (hE : FilterEnergyStatement) (hS : FilterScaleStatement) :
    FilterRowMassStatement := by
  have j1 := termFluxPrefix_and (P₁ := fun c x kc _ => FilterEnergyAt c x kc)
    (P₂ := fun c _ _ _ => FilterScaleAt c) hE hS
  have j2 := termFluxPrefix_and (P₁ := fun c _ kc C => FilterSchurFAt c kc C)
    (P₂ := fun c x kc _ => FilterEnergyAt c x kc ∧ FilterScaleAt c) hF j1
  have j3 := termFluxPrefix_and (P₁ := fun c _ kc C => FilterSchurWAt c kc C)
    (P₂ := fun c x kc C => FilterSchurFAt c kc C ∧ (FilterEnergyAt c x kc ∧ FilterScaleAt c))
    hW j2
  have j4 := termFluxPrefix_and (P₁ := fun c _ kc _ => FilterRegAt c kc)
    (P₂ := fun c x kc C => FilterSchurWAt c kc C ∧
      (FilterSchurFAt c kc C ∧ (FilterEnergyAt c x kc ∧ FilterScaleAt c))) hR j3
  refine prefix_map (P := fun c x kc C => FilterRegAt c kc ∧ (FilterSchurWAt c kc C ∧
    (FilterSchurFAt c kc C ∧ (FilterEnergyAt c x kc ∧ FilterScaleAt c))))
    (R := fun c x kc C => FilterRowMassAt c x kc C) ?_ j4
  intro X A kc C₁ hΛ hV hC₁
  refine ⟨C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M hKO c x
    hP C' hC'
  obtain ⟨hε, hε1, hν, hρ, hπ⟩ := filter_ctx_facts c x hΛ
  have hD : 2 ≤ A.Dt := le_max_left _ _
  have h1 := filterRowMassAt_of_inputs c x kc C₁ hV hKO hε hε1 hν hρ hπ hD hC₁ hP.1 hP.2.1
    hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
  have hrw : 0 ≤ c.D.termRW A.σw M := by unfold OCData.termRW; positivity
  have hfp := filterPrice_nonneg c hε hε1 hρ hrw
  have hN : 0 ≤ c.normF := Real.sqrt_nonneg _
  exact hasFluxBound_mono_Y h1 (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC' hfp) hN)

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The zero-extended truncation of the readout and its algebra.**

`filtV c hle j t` is the truncation of the readout `eZr` at the component `j` if `j ∈ Gw`, and `0`
otherwise. This module gives the algebra of the zero extension: the classical representative, the
reindexing of the mass sums from `Gt'` to `Gw`, and the equality of the integrand with the
truncated readout of the order `K̂ + 1` lift almost everywhere.

Degenerate case: `Gw = ∅`, where `V = 0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The weak components are components of the terminal successor. -/
theorem weak_components_subset_terminal (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP
    cHP Cw Ce cker j₀ M) : c.Gw.comps ⊆ c.Gt'.comps := by
  intro u hu
  rw [c.succ.2.2.1]
  exact Finset.mem_union_left _ hu

/-- The zero extension of the truncated readout. -/
def filtV (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP
    cHP Cw Ce cker j₀ M) {K : ℕ} (hle : K ≤ A.Khat Kout) (j : CompIn c.Gt'.comps) (t : ℝ) :
    TorusHk K (ScalarH j.1.root) :=
  if h : j.1 ∈ c.Gw.comps then truncateTorusHk hle (eZr c ⟨j.1, h⟩ t) else 0

/-- The classical representative of the zero extension. -/
theorem filtV_rep (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW
    cP CP cHP Cw Ce cker j₀ M) (x : TermResAux c) {K : ℕ} (hle : K ≤ A.Khat Kout)
    (hK : K ≤ A.Khat Kout - 2) (j : CompIn c.Gt'.comps) (t : ℝ)
    (ht : t ∈ Set.Icc c.tp (c.a + A.T₀)) :
    IsClassicalRep (filtV c hle j t) (extAZ c.Gw c.Gt' x.aZ j t) K := by
  unfold filtV extAZ
  by_cases h : j.1 ∈ c.Gw.comps
  · simp only [h, dite_true]
    exact classicalRep_truncate hle le_rfl _ _
      (CycleComparison.Reconstruction.isClassicalRep_of_le (x.repZ ⟨j.1, h⟩ t ht) hK)
  · simp only [h, dite_false]
    exact classicalRep_zero le_rfl

/-- The zero extension is almost everywhere the truncation of the order-`K̂+1` readout. -/
theorem filtV_ae (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW
    cP CP cHP Cw Ce cker j₀ M) {K : ℕ} (hle : K + 1 ≤ A.Khat Kout)
    (hae : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (eZrw c v t) = eZr c v t) (v : CompIn c.Gw.comps) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      filtV c hle ⟨v.1, weak_components_subset_terminal c v.2⟩ t =
        truncateTorusHk (Nat.succ_le_succ (Nat.le_of_succ_le hle)) (eZrw c v t) := by
  filter_upwards [hae v] with t ht
  unfold filtV
  simp only [v.2, dite_true]
  rw [← ht]
  rfl

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
section
/-! **The energy of the zero extension of the readout (`FilterEnergyAt`).**

From the strong energy of the readout (`readout_data`): the sum over `Gt'` of the zero
extension reindexes to the sum over `Gw` (the root masses agree), equals almost everywhere the
gradient energy of the truncated order-`K̂+1` readout, and `covGrad_dissipation_le` bounds it.

Degenerate case: `f = 0`, where the energy bound is `0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux AVRegularity.EntryTerminal.CovGrad
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The masses of `Gt'` and `Gw` agree on the weak components. -/
theorem mass_eq (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (v : CompIn c.Gw.comps) :
    c.Gt'.mass c.lawT ⟨v.1, weak_components_subset_terminal c v.2⟩ = c.Gw.mass c.lawW v := by
  have hb : v.1.births = [] := c.weak.2.2.2.2.1 v
  unfold GenStage.mass compMass
  simp only [hb, List.map_nil, List.prod_nil, mul_one]
  rw [c.law.1]

/-- The reindexing of a sum supported on the weak components. -/
theorem sum_reindex (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW
    cP CP cHP Cw Ce cker j₀ M) (f : CompIn c.Gt'.comps → ℝ)
    (hf : ∀ j : CompIn c.Gt'.comps, j.1 ∉ c.Gw.comps → f j = 0) :
    ∑ j, f j = ∑ v : CompIn c.Gw.comps, f ⟨v.1, weak_components_subset_terminal c v.2⟩ := by
  symm
  refine Fintype.sum_of_injective (fun v : CompIn c.Gw.comps => (⟨v.1, weak_components_subset_terminal c v.2⟩ :
    CompIn c.Gt'.comps)) (fun a b hab => Subtype.ext (Subtype.mk.inj hab)) _ _
    (fun j hj => hf j fun hjw => hj ⟨⟨j.1, hjw⟩, rfl⟩) fun v => rfl

/-- **`FilterEnergyAt` from the strong energy of the readout.** -/
theorem energyAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (x : TermResAux c) (kc : ℕ)
    (hK : filterK A kc + 3 ≤ A.Khat Kout) (hν : 0 < c.D.κ (M - 1))
    (hπ : ∀ v, 0 < c.Gw.mass c.lawW v)
    (hen : strongEnergy (c.D.termRho cr M) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
      (eZr c) (eZrw c) ≤ ENNReal.ofReal (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF)))
    (hRw : ∀ v, MemLp (eZrw c v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (hae : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (eZrw c v t) = eZr c v t) :
    FilterEnergyAt c x kc := by
  have hle0 : filterK A kc ≤ A.Khat Kout := by omega
  have hle1 : filterK A kc + 1 ≤ A.Khat Kout := by omega
  let Wt : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (filterK A kc + 1) (ScalarH v.1.root) :=
    fun v s => truncateTorusHk (Nat.succ_le_succ hle0) (eZrw c v s)
  have hWt : ∀ v, MemLp (Wt v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) := fun v =>
    (truncateTorusHk (E := ScalarH v.1.root) (Nat.succ_le_succ hle0)).comp_memLp' (hRw v)
  have hzero : ∀ (j : CompIn c.Gt'.comps) (s : ℝ), j.1 ∉ c.Gw.comps →
      (c.Gt'.mass c.lawT j)⁻¹ * gradFactorialNormSq (c.D.termRho cr M)
        (filtV c hle1 j s).val = 0 := by
    intro j s hj
    simp [filtV, hj, gradFactorialNormSq]
  have hpt : ∀ s, massGradNormSq (E := fun j : CompIn c.Gt'.comps => ScalarH j.1.root)
      (K := fun _ => filterK A kc) (c.D.termRho cr M) (c.Gt'.mass c.lawT)
      (fun j => (filtV c hle1 j s).val) =
      ∑ v : CompIn c.Gw.comps, (c.Gw.mass c.lawW v)⁻¹ * gradFactorialNormSq (c.D.termRho cr M)
        (filtV c hle1 ⟨v.1, weak_components_subset_terminal c v.2⟩ s).val := by
    intro s
    unfold massGradNormSq
    rw [sum_reindex c _ (fun j hj => hzero j s hj)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mass_eq]
  have hall : ∀ᵐ s ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      ∀ v : CompIn c.Gw.comps, filtV c hle1 ⟨v.1, weak_components_subset_terminal c v.2⟩ s = Wt v s :=
    Filter.eventually_all.2 fun v => filtV_ae c hle1 hae v
  have hM : (fun s => massGradNormSq (E := fun j : CompIn c.Gt'.comps => ScalarH j.1.root)
      (K := fun _ => filterK A kc) (c.D.termRho cr M) (c.Gt'.mass c.lawT)
      (fun j => (filtV c hle1 j s).val)) =ᵐ[volume.restrict (Set.Icc c.tp (c.a + A.T₀))]
      fun s => ∑ v : CompIn c.Gw.comps, (c.Gw.mass c.lawW v)⁻¹ *
        gradFactorialNormSq (c.D.termRho cr M) (Wt v s).val := by
    filter_upwards [hall] with s hs
    rw [hpt]
    exact Finset.sum_congr rfl fun v _ => by rw [hs v]
  have hintW : Integrable (fun s => ∑ v : CompIn c.Gw.comps, (c.Gw.mass c.lawW v)⁻¹ *
      gradFactorialNormSq (c.D.termRho cr M) (Wt v s).val)
      (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) :=
    integrable_finsetSum _ fun v _ =>
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hWt v)).const_mul _
  have hE : 0 ≤ Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
      (Real.sqrt 2 * max CP 0 * c.normF) := by
    have : 0 ≤ c.normF := Real.sqrt_nonneg _
    positivity
  have hdis := covGrad_dissipation_le hν hE (c.Gw.mass c.lawW) hπ
    (fun v t => truncateTorusHk hle0 (eZr c v t)) Wt hWt
    ((strongEnergy_truncate_le hle0 (c.D.termRho cr M) (c.D.κ (M - 1)) (c.Gw.mass c.lawW)
      c.tp (c.a + A.T₀) (eZr c) (eZrw c)).trans hen)
  refine ⟨filtV c hle1, fun j t ht => filtV_rep c x hle1 (by omega) j t ht, ?_,
    hintW.congr hM.symm, ?_⟩
  · intro j
    by_cases hj : j.1 ∈ c.Gw.comps
    · have h1 := (hRw ⟨j.1, hj⟩).aestronglyMeasurable
      have h2 := (truncateTorusHk (E := ScalarH j.1.root)
        (Nat.succ_le_succ hle0)).continuous.comp_aestronglyMeasurable h1
      refine h2.congr ?_
      filter_upwards [filtV_ae c hle1 hae ⟨j.1, hj⟩] with t ht
      exact ht.symm
    · have : filtV c hle1 j = fun _ => 0 := by
        funext t
        simp [filtV, hj]
      rw [this]
      exact aestronglyMeasurable_const
  · rw [integral_congr_ae hM]
    rw [integral_finsetSum _ (fun i _ =>
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hWt i)).const_mul _)]
    simp only [integral_const_mul]
    have hfe : filterEb A CP * c.normF = Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF) := by
      unfold filterEb; ring
    rw [hfe]
    exact Real.sqrt_le_iff.2 ⟨hE, hdis⟩

/-- **(EN), `FilterEnergyStatement`.** -/
theorem filterEnergy : FilterEnergyStatement := by
  intro X
  obtain ⟨ΛR, hΛR, hR⟩ := readout_data X
  refine ⟨ΛR, hΛR, fun A hΛ hV => ?_⟩
  refine ⟨0, fun kc _ => ⟨0, 0, filterK A kc + 3, fun sXT sZT _ _ Kout hKout => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP
    cHP Cw Ce cker _ Cfl
  obtain ⟨M₀, hM₀⟩ := hR A hΛ hV cHP
  refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨M₀, fun M hM c x => ?_⟩⟩
  obtain ⟨hπ, hν, hen, hRw, hae⟩ := hM₀ hM c x
  exact energyAt c x kc (le_trans hKout (le_max_left _ _)) hν hπ hen hRw hae

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.QuietEntrance
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The energy of the lifted field at one context

The energy engine `strong_energy_le` applied to the terminal context: the lifted-field clauses
come from the context (`c.lift`) and from the classical-representative hypotheses on `(Û, Ŵ)`,
the coarse pair from the energy bound (`coarse`), the slot lifts and the flow jets are inputs.

Degenerate case: `Cs = 0`: the energy is `0` after the engine (the price is finite). -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The menu lifted representative is the glued lift of the engine (`cr = 1`, `level = M`). -/
theorem menu_eq_glued
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hlev : c.Gw.level = M) (t : ℝ) :
    menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t =
      Glued c.Gw A.NT A.dW c.CcT c.aRep t := by
  rw [menuLiftedRep_terminal (A.Mt M sXT sZT c.tp cr) cr rfl M A.NT A.dW c.CcT c.aRep]
  funext y
  simp only [termLiftedRep, Glued, hlev, x.one, one_mul]

/-- **The energy of the classical pair at one context** (the engine and the energy bound). -/
theorem ctx_energy
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (ℓ kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) {Cs : ℝ}
    (hR : ReconEnergyAt c x kc ℓ hW Cs) (hlev : c.Gw.level = M) (hcK : 0 < cK)
    (hkc : fineOrder (A := A) + 1 ≤ kc)
    (hℓ : fineOrder (A := A) + 1 + A.NT ≤ rpord A ℓ)
    (hK : fineOrder (A := A) + 1 + 1 ≤ rKlift A ℓ) (hL : fineOrder (A := A) + 1 + 1 ≤ rLlift A ℓ + 2)
    {CG Cw' : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S Sbar : ℝ}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift c.Gw slot (c.Gw.mass c.lawW) A.dW A.NT
      (rKlift A ℓ) (rLlift A ℓ) (rLlift A ℓ) CG Cw' Cj S)
    (hSbar : 0 ≤ Sbar) (hSS : S ≤ Sbar)
    (hi : 1 ≤ c.Gw.level) (hΛ : 1 ≤ c.D.Λ) (hζ : IsFastProfile c.D.ζ)
    (hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ)
    {C : ℝ} (hC : 1 ≤ C)
    (hflow : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ j ∈ ocObsPulses c.D.α c.D.q c.D.Λ c.Gw.level t t,
      ocCutoff c.D.α c.D.q c.D.Λ c.Gw.level j t ≠ 0 →
      ChartTransport.JetBound
        (fun y => c.D.flowOf (c.Gw.level - 1) t y (c.D.slotAnchor c.Gw.level j))
        (fineOrder (A := A) + 1 + 1 + A.NT) C (liftLength c.D c.Gw.level) ∧
      ChartTransport.JetBound
        (fun y => c.D.flowOf (c.Gw.level - 1) (c.D.slotAnchor c.Gw.level j) y t)
        (fineOrder (A := A) + 1 + 1 + A.NT) C (liftLength c.D c.Gw.level)) :
    ∀ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
      (Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
        IsClassicalRep (Û v t)
          (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v)
          (fineOrder (A := A) + 1)) →
      (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
        IsClassicalRep (Ŵ v t)
          (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v)
          (fineOrder (A := A) + 1 + 1)) →
      strongEnergy (c.D.termRStar cK M) (c.D.κ M) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Û Ŵ ≤
        ENNReal.ofReal ((max 1 cK) ^ (fineOrder (A := A) + 1)) *
          ((nativeLiftStrongEnergyPrice (fineOrder (A := A) + 1) (max (rLlift A ℓ) (rLlift A ℓ + 2))
            A.Dt A.dW A.NT CG Cw' Cj Sbar C) ^ (1 / 2 : ℝ) * ENNReal.ofReal (Cs * c.normF)) := by
  intro Û Ŵ hÛ hŴ
  have hseq : LiftSeqClause c.Gw c.Gw.level A.NT A.dW sXT sZT c.CcT := by
    rw [hlev]
    intro k hk
    simpa only [x.one, one_mul] using c.lift.1 k hk
  have hcl : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (c.PZ v t) (fun y => c.aRep t y v) (A.Khat Kout - 2 * A.pT) :=
    fun v t ht => (c.lift.2.1 v t ht).2
  have hval : LiftValueClause c.Gw c.Gw.level A.NT A.dW c.tp (c.a + A.T₀) c.CcT c.aRep Û := by
    intro v t ht
    refine (qe_value_rep (Û v t) _ (hÛ v t ht)).trans ?_
    exact Filter.Eventually.of_forall fun y =>
      congrFun (congrFun (menu_eq_glued c x hlev t) y) v
  have hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc c.tp (c.a + A.T₀)),
      truncateTorusHk (Nat.le_succ (fineOrder (A := A) + 1)) (Ŵ v t) = Û v t := by
    intro v
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    refine KernelEnergy.torusCarrier_eq_of_value_ae _ _ ?_
    exact (qe_value_rep _ _ (Construction.Preservation.FullLift.classicalRep_truncate (Nat.le_succ _) le_rfl (Ŵ v t) _
      (rdJets_classicalRep_mono (hŴ v t ht) (Nat.le_succ _)))).trans (qe_value_rep _ _ (hÛ v t ht)).symm
  obtain ⟨Z, Zw, hZ, hZw, hmeas, hE⟩ := coarse c x kc ℓ hW hR
    (n := fineOrder (A := A) + 1 + A.NT) (by omega) hℓ
  have hLev1 : (1 : ℕ) ≤ 2 := by norm_num
  have hle : fineOrder (A := A) + 1 + 1 + A.NT ≤ A.Khat Kout - 2 * A.pT := by omega
  have ha : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((fineOrder (A := A) + 1 + 1 + A.NT : ℕ) : ℕ∞) (c.aRep t) := fun t ht =>
    contDiff_pi.mpr fun v => (c.lift.2.1 v t ht).2.2.1.of_le (by exact Nat.cast_le.mpr hle)
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseqD, hbandD, htermD⟩ := c.data
  have hs := (slotLifts ⟨1, odd_one⟩).setting
  have hkap0 : c.D.kap c.Gw.level = c.D.κ c.Gw.level := by
    simp only [OCData.kap, htermD, hlev, min_self]
  have hkap1 : c.D.kap (c.Gw.level - 1) = c.D.κ (c.Gw.level - 1) := by
    simp only [OCData.kap, htermD, hlev]
    rw [min_eq_left (Nat.sub_le M 1)]
  have hρ : 0 < liftLength c.D c.Gw.level := hs.ρ_pos
  have hν : 0 < c.D.κ c.Gw.level := hkap0 ▸ hs.ν_pos
  have hB : 0 < c.D.κ (c.Gw.level - 1) := hkap1 ▸ hs.B_pos
  have hνB : c.D.κ c.Gw.level ≤ c.D.κ (c.Gw.level - 1) := by
    have h1 := hs.η_le
    rw [hs.η_eq, div_le_one hs.B_pos] at h1
    rwa [hkap0, hkap1] at h1
  have hcell : ocDStar c.D.q c.D.Λ c.Gw.level (c.D.κ c.Gw.level) (c.D.κ (c.Gw.level - 1)) /
      liftLength c.D c.Gw.level ≤ 1 := by
    have h1 := hs.εc_le
    simpa only [hkap0, hkap1] using h1
  have he : 0 < c.D.eps c.Gw.level := Construction.Stream.ocEpsilon_pos hΛ
  have hengine : ∀ rs : ℝ, 0 < rs → rs ≤ c.D.eps c.Gw.level →
      strongEnergy rs (c.D.κ c.Gw.level) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Û Ŵ ≤
        (nativeLiftStrongEnergyPrice (fineOrder (A := A) + 1) (max (rLlift A ℓ) (rLlift A ℓ + 2))
            A.Dt A.dW A.NT CG Cw' Cj Sbar C) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Cs * c.normF) := by
    intro rs hrs hrse
    have hres : ∀ slot : OddSlot, fineOrder (A := A) + 1 + 1 + (A.NT + (slotLifts slot).cap) ≤
        rKlift A ℓ + 4 * (A.dW + 1) * (A.NT + (slotLifts slot).cap) ^ 2 := by
      intro slot
      have h2 : A.NT + (slotLifts slot).cap ≤ 4 * (A.dW + 1) * (A.NT + (slotLifts slot).cap) ^ 2 := by
        nlinarith [Nat.zero_le (A.NT + (slotLifts slot).cap), Nat.zero_le A.dW,
          Nat.le_mul_self (A.NT + (slotLifts slot).cap)]
      omega
    have htorus : IsTorusCompatible c.Gw.fam c.Gw.actual (c.D.eps (c.Gw.level - 1)) := by
      have e : c.D.eps (c.Gw.level - 1) = c.D.eps (M - 1) := by rw [hlev]
      rw [e]; exact c.weak.isTorusCompatible
    have h := strong_energy_le slotLifts hi hΛ hζ hband htorus
      (fineOrder (A := A) + 1) hres (by omega) A.pT (A.Khat Kout) sXT sZT c.tp (c.a + A.T₀)
      c.CcT c.PZ c.aRep Û Ŵ hseq hcl hval hcompat ha Sbar hSbar hSS hC hrs hrse hρ hν hB hνB hcell
      hflow Z Zw hZ (fun v => (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun t ht => hZw v t ht)) hmeas
    refine h.trans (mul_le_mul_right ?_ _)
    rw [hlev]
    exact hE
  have hone : 1 ≤ ENNReal.ofReal ((max 1 cK) ^ (fineOrder (A := A) + 1)) :=
    ENNReal.one_le_ofReal.mpr (one_le_pow₀ (le_max_left _ _))
  by_cases hc1 : cK ≤ 1
  · have h := hengine (cK * c.D.eps c.Gw.level) (mul_pos hcK he)
      (by nlinarith [he])
    rw [hlev] at h
    calc _ ≤ _ := h
      _ = 1 * _ := (one_mul _).symm
      _ ≤ _ := by gcongr
  · replace hc1 := not_le.mp hc1
    have h := hengine (c.D.eps c.Gw.level) he le_rfl
    rw [hlev] at h
    have h2 := strongEnergy_mul_radius_le' (K := fineOrder (A := A) + 1) hc1.le
      (c.D.eps M) (c.D.κ M) c.tp (c.a + A.T₀) (c.Gw.mass c.lawW) Û Ŵ
    rw [max_eq_right hc1.le]
    exact h2.trans (by gcongr)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.EntryTerminal.Ingredients.Recon.Setting
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # Small facts for the prefix assembly of the energy-only statement -/

/-- A jet bound with a smaller constant is one with a larger constant. -/
theorem jetBound_mono' {Θ : Vec 2 → Vec 2} {N : ℕ} {D D' R : ℝ} (hR : 0 < R)
    (h : ChartTransport.JetBound Θ N D R) (hD : D ≤ D') : ChartTransport.JetBound Θ N D' R :=
  fun p hp1 hpN y => (h p hp1 hpN y).trans
    (mul_le_mul_of_nonneg_right hD (pow_nonneg (inv_nonneg.mpr hR.le) _))

/-- The native slot setting at `cr = 1`. -/
theorem slot_cr_one {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} {D : OCData} {M : ℕ}
    {Gw : GenStage D ScalarH Dt bw j₀} {law : BirthLaw} {cr Θ : ℝ} {N H K kk L : ℕ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {k : ℤ} {hk : Odd k} (h1 : cr = 1)
    (h : NativeSlotSetting D M Gw law cr Θ N H K kk L CG Cw Cj k hk) :
    NativeSlotSetting D M Gw law 1 Θ N H K kk L CG Cw Cj k hk := by
  subst h1; exact h

/-- The cap `D_t` is at least `N_T`. -/
theorem NT_le_Dt {X : TermConstruction} (A : TermArgs X) : A.NT ≤ A.Dt := by
  have h2 : letterOrder A.NT A.pT .diag ≤ A.Dt :=
    (Finset.le_sup (f := letterOrder A.NT A.pT)
      (succAlphabet_diag_mem (A.NT + A.DW) A.dW A.pT 0)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  simp only [letterOrder] at h2
  omega

/-- **(b1) `TermLiftEnergyOnlyStatement`.** -/
theorem termLiftEnergyOnly : TermLiftEnergyOnlyStatement := by
  classical
  intro X
  obtain ⟨Λa, h128a, hRa⟩ := Recon.Energy.reconEnergyU X
  obtain ⟨Λb, h128b, hSb⟩ := native_setting X
  refine ⟨max Λa Λb, le_trans h128a (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛa : Λa ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛb : Λb ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have h128 : 128 ≤ A.Λ := le_trans h128a hΛa
  set ℓ : ℕ := A.LfT + A.Dt + 2 + A.NT * A.dW with hℓdef
  obtain ⟨kc₀a, hRa'⟩ := hRa A hΛa hV ℓ
  obtain ⟨CG, Cw', Cj, hCj, hSet⟩ := hSb A hΛb hV ℓ
  obtain ⟨Mf, hMf, hflowC⟩ := uniform_native_physical_flow_jets X.α X.s X.q X.hα₀ X.hα₁ X.hs₀
    X.hs₁ X.hq A.Λ h128 X.ζ X.hζ (fineOrder (A := A) + 1 + 1 + A.NT)
  refine ⟨max kc₀a (fineOrder (A := A) + 1), fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hRb⟩ := hRa' kc (le_trans (le_max_left _ _) hkc)
  refine ⟨max SX (rKlift A ℓ + A.Dt + 2), max SZ (rLlift A ℓ + 2),
    max Kf (kc + 1 + (A.NT + A.Dt) + 2 * A.pT), fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hRc⟩ := hRb sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
    Kout (le_trans (le_max_left _ _) hK)
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan
    hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP _Cfl => ?_⟩
  obtain ⟨⟨Cs, hCs⟩, CHt, Υt, hCH, hΥ, hRd⟩ := hRc Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko
    hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce
    cker hcP
  obtain ⟨B, hB0, hB⟩ := nativeLiftStrongEnergyPrice_real_constant (fineOrder (A := A) + 1)
    (max (rLlift A ℓ) (rLlift A ℓ + 2)) A.Dt A.dW A.NT CG Cw' Cj (max 0 Cχ)
    (max 1 (EntryWeakProofs.weakChartJetBudget (fineOrder (A := A) + 1 + 1 + A.NT) 0))
  refine ⟨(max 1 cK) ^ (fineOrder (A := A) + 1) * B * Cs, 1, 1, one_pos, CHt, Υt, hCH, hΥ,
    fun C hC j₀ hj₀ => ?_⟩
  obtain ⟨M₀r, hM₀r⟩ := hRd j₀ hj₀
  obtain ⟨M₀n, hM₀n⟩ := hSet nW cr cK CL Cχ kW hcr0 hcr1 hcK hkW j₀
  refine ⟨max (max M₀r M₀n) (Mf + 1), fun M hM c x => ?_⟩
  have hMn : M₀n ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMr : M₀r ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMf1 : Mf + 1 ≤ M := le_trans (le_max_right _ _) hM
  have hset := hM₀n M hMn c.D c.data c.a c.lawW c.PW c.Gw c.aM c.weak x.reserve
  have hKh : Kout ≤ A.Khat Kout := le_max_left _ _
  have hW0 : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT := by
    have := le_trans (le_max_right _ _) hK
    omega
  have hR := hM₀r M hMr c x hW0
  have hlev : c.Gw.level = M := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseqD, hbandD, htermD⟩ := c.data
  have hΛD : 1 ≤ c.D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  have hbandD' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, htermD]; exact hbandD
  have hε1 : c.D.eps M ≤ 1 := ocEpsilon_le_one hΛD M
  have hε0 : 0 ≤ c.D.eps M := (Construction.Stream.ocEpsilon_pos hΛD).le
  have hχ : 0 < A.χw := hV.2.2.2.1.2.2.2.2.2.2.1
  have hp1 : c.D.eps M ^ A.χw ≤ 1 := Real.rpow_le_one hε0 hε1 hχ.le
  have hp0 : 0 ≤ c.D.eps M ^ A.χw := Real.rpow_nonneg hε0 _
  have hSS : Cχ * c.D.eps M ^ A.χw ≤ max 0 Cχ := by
    rcases le_total 0 Cχ with h0 | h0
    · nlinarith [le_max_right 0 Cχ]
    · nlinarith [le_max_left 0 Cχ]
  have hDt2 : 2 ≤ A.Dt := le_max_left _ _
  have hseqS : LiftSeqClause c.Gw M A.NT A.dW sXT sZT c.CcT := fun k hk => by
    simpa only [x.one, one_mul] using c.lift.1 k hk
  have hsX : rKlift A ℓ + A.Dt + 2 ≤ sXT := le_trans (le_max_right _ _) hX
  have hsZ : max (rLlift A ℓ + 1) (rLlift A ℓ + 2) ≤ sZT := by
    have := le_trans (le_max_right _ _) hZ
    omega
  have hne := native_slot_lifts c.D M c.Gw hlev c.lawW (Cχ * c.D.eps M ^ A.χw) A.NT A.dW (rKlift A ℓ)
    (rLlift A ℓ) (rLlift A ℓ) sXT sZT CG Cw' Cj hDt2 c.CcT hseqS hsX hsZ (NT_le_Dt A)
    (fun k hk => slot_cr_one x.one (hset k hk))
  let slotLifts := fun slot : OddSlot => Classical.choice (hne slot)
  have hs := (slotLifts ⟨1, odd_one⟩).setting
  have hlam : liftLength c.D c.Gw.level ≤ c.D.eps (c.Gw.level - 1) := by
    have h1 := hs.lam_le
    rwa [hs.lam_eq, div_le_one hs.E_pos] at h1
  have hkc' : fineOrder (A := A) + 1 ≤ kc := le_trans (le_max_right _ _) hkc
  have hctx := ctx_energy c x ℓ kc hW0 hR hlev hcK hkc'
    (by simp only [rpord, rKmax, rAcl, fineOrder, hℓdef]; omega)
    (by simp only [rKlift, rKmax, rAcl, fineOrder, hℓdef]; omega)
    (by simp only [rLlift, rKmax, fineOrder, hℓdef]; omega) slotLifts
    (le_max_left 0 Cχ) hSS (by omega) hΛD hζD hbandD' (le_max_left _ _)
    (fun t _ j hj hcut => by
      have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
      have hwin := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
        (Construction.Stream.ocTau_pos hΛD) hcut
      have hh := hflowC c.D hDα hDq hDΛ hDζ hseqD c.Gw.level (by omega) j hjodd
        (liftLength c.D c.Gw.level) hs.ρ_pos hlam t hwin
      exact ⟨jetBound_mono' hs.ρ_pos hh.1 (le_max_right _ _),
        jetBound_mono' hs.ρ_pos hh.2 (le_max_right _ _)⟩)
  intro Û Ŵ hÛ hŴ
  refine (hctx Û Ŵ hÛ hŴ).trans ?_
  rw [hB, ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one
    (le_max_left _ _)) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc _ = ((max 1 cK) ^ (fineOrder (A := A) + 1) * B * Cs) * c.normF := by ring
    _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # `TermLiftMeasStatement` and the terminal fine tail

`termLiftMeas : TermLiftMeasStatement`: with the prefix of the terminal residual, every classical
`Û` of the lifted field is a.e. strongly measurable in time on the window. At a context this is
`liftMeasAt`; the prefix supplies the energy step (`reconEnergyU`: `P_pZ` truncated is continuous
in time) at the coarse order `k_c` and the order floor `K_out ≥ k_c + 1 + N_T + D_t + 2 p_T`.

With `termLiftEnergyOnly`: `termFineTail : TermFineTailStatement`.

Degenerate cases: the statement has no constant (`C₀ = 0`, `c_gap = C_g = 1` are dummies); an empty
family of components is covered (the statement is per component). -/

/-- **(b2) `TermLiftMeasStatement`.** -/
theorem termLiftMeas : TermLiftMeasStatement := by
  classical
  intro X
  obtain ⟨Λa, h128a, hRa⟩ := Recon.Energy.reconEnergyU X
  refine ⟨Λa, h128a, fun A hΛ hV => ?_⟩
  have h128 : 128 ≤ A.Λ := le_trans h128a hΛ
  obtain ⟨kc₀a, hRa'⟩ := hRa A hΛ hV 0
  refine ⟨kc₀a, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hRb⟩ := hRa' kc hkc
  refine ⟨SX, SZ, max Kf (kc + 1 + (A.NT + A.Dt) + 2 * A.pT),
    fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hRc⟩ := hRb sXT sZT hX hZ Kout (le_trans (le_max_left _ _) hK)
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 hKs hKan hLan
    hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP _Cfl => ?_⟩
  obtain ⟨⟨Cs, hCs⟩, CHt, Υt, hCH, hΥ, hRd⟩ := hRc Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko
    hcr0 hcr1 hcre hcr hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce
    cker hcP
  refine ⟨0, 1, 1, one_pos, CHt, Υt, hCH, hΥ, fun C _ j₀ hj₀ => ?_⟩
  obtain ⟨M₀r, hM₀r⟩ := hRd j₀ hj₀
  refine ⟨M₀r, fun M hM c x => ?_⟩
  have hKh : Kout ≤ A.Khat Kout := le_max_left _ _
  have hW0 : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT := by
    have := le_trans (le_max_right _ _) hK
    omega
  have hR := hM₀r M hM c x hW0
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hbandD, htermD⟩ := c.data
  have hΛD : 1 ≤ c.D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  have hbandD' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, htermD]; exact hbandD
  have hDt2 : 2 ≤ A.Dt := le_max_left _ _
  exact liftMeasAt c x kc 0 hW0 hR hΛD hζD hbandD' (by omega)

/-- **The fine matrix tail at the terminal lifted field**: its two statements are proved. -/
theorem termFineTail : TermFineTailStatement :=
  termFineTail_of_split termLiftEnergyOnly termLiftMeas

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The filter defect, assembled.**

`filterRowMass : FilterRowMassStatement` from the five proved inputs (`filterReg`, `filterSchurW`,
`filterSchurF`, `filterEnergy`, `filterScale`) by the compiled `filterRowMass_of_inputs`, and
`filterDefect : FilterDefectStatement` from the three parts (`filterRowSmooth_proof`,
`filterRowMass`, `filterReadoutMap`) by `filterDefect_of_parts`.
-/

open AVRegularity.Construction.Residual.Presentation

/-- **The mass of the root flux defect rows.** -/
theorem filterRowMass : FilterRowMassStatement :=
  filterRowMass_of_inputs filterReg filterSchurW filterSchurF filterEnergy filterScale

/-- **The filter defect.** -/
theorem filterDefect : FilterDefectStatement :=
  filterDefect_of_parts filterRowSmooth_proof filterRowMass filterReadoutMap

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
