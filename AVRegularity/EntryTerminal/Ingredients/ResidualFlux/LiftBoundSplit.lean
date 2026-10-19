-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncCovGradient
import AVRegularity.EntryTerminal.Ingredients.PrepAnchor.PrepAnchor
import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelopeStatement
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.SchurF
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Applications.Global.CompactRangeMain

section
section
/-! **Positivity of the weak kernel constants** and the defect step of the fine tail.

For a weak stage with an edge, the stage invariant gives clause (4) of
`IsSpatialRegularizerTorus` for the weak kernel `isoPairedKernel r_w n_W` at `ρ = 1`, `k = 0`, on the
window `[a_M, a + T₀]`. For `M` large the window is nonempty and `r_w` is small, so the kernel moves
the mode `cos(2π x₁)` by less than its norm (`ckerShift_iso_tendsto`), and `ckerPos_of_close` gives
`0 < c_j` for `j + 2 ≤ D_t`.

Degenerate cases:
- No edge: excluded by hypothesis (`fineDefectAt_noEdge`).
- `j = 0`: `c_0 = 0` would force `S f = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter Topology
open AVRegularity.EntryTerminal.Route

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- The mode has positive norm. -/
theorem ckerMode_norm_pos : 0 < ‖ckerMode‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  have hae : ckerPhase 0 =ᵐ[volume.restrict unitCube] 0 := by
    filter_upwards [ckerMode_ae, Lp.coeFn_zero ℝ 2 (volume.restrict unitCube)] with x h1 h2
    rw [← h1, h0, h2]
  have hmeas : MeasurableSet unitCube := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hopen : IsOpen unitCube := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hU : IsOpen (unitCube ∩ {x : Vec 2 | ckerPhase 0 x ≠ 0}) :=
    hopen.inter (isOpen_ne_fun (by unfold ckerPhase; fun_prop) continuous_const)
  have hne : (unitCube ∩ {x : Vec 2 | ckerPhase 0 x ≠ 0}).Nonempty := by
    refine ⟨fun i => if i = 0 then 1 / 8 else 1 / 2, ?_, ?_⟩
    · intro i _
      by_cases hi : i = 0 <;> simp [hi] <;> norm_num
    · have : (0 : ℝ) < Real.cos (2 * Real.pi * (1 / 8) + 0) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> nlinarith [Real.pi_pos]
      simpa [ckerPhase] using this.ne'
  have hpos := hU.measure_pos (volume : Measure (Vec 2)) hne
  have hz : volume (unitCube ∩ {x : Vec 2 | ckerPhase 0 x ≠ 0}) = 0 := by
    have := (ae_restrict_iff' hmeas).1 hae
    refine measure_mono_null ?_ (ae_iff.1 this)
    intro x hx h
    exact hx.2 (h hx.1)
  exact absurd hz hpos.ne'

/-- **Positivity**: for a weak stage with an edge, the weak kernel constants are positive. -/
theorem termCker : TermCkerStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV nW CL Cχ kW j₀ => ?_⟩
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨-, ⟨-, hnn, hmass, -⟩, -, ⟨-, hτ0, hτT, -, hσw, -, -, -, -⟩, -⟩ := hV
  have hT : 0 < A.T₀ := hτ0.trans hτT
  obtain ⟨M₁, hM₁⟩ := EntryTerminal.Ingredients.prepAnchor_deadline X hΛ A.Jw hT
  -- smallness of the paired kernel
  have hlim := ckerShift_iso_tendsto A.hφ₀ hnn hmass nW 0 ckerMode
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1
    ((tendsto_order.1 hlim).2 _ ckerMode_norm_pos)
  obtain ⟨M₂, hM₂⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 hΛ
    (p := 1 + A.σw) (by linarith) (c := δ / 2) (by positivity)
  refine ⟨max M₁ M₂, fun M hM D hD a lawW PW Gw aM hW hedge m hm => ?_⟩
  obtain ⟨v, u, ⟨γ⟩⟩ := hedge
  obtain ⟨hDα, hDq, hDΛ, -⟩ := hD
  have hMa : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hMb : M₂ ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨-, haM2, -, -, -, -, -, -, -, hI⟩ := hW
  -- the window is nonempty
  have hτpos : 0 < ocTauPP X.α X.q A.Λ M :=
    Construction.Stream.ocTauPP_pos (by omega)
  have hwin : aM ≤ a + A.T₀ := by
    have h6 := hM₁ M hMa
    rw [hDα, hDq, hDΛ] at haM2
    have hJ := hτpos
    nlinarith
  -- the radius is small
  have hr : D.termRW A.σw M < δ := by
    have h := hM₂ M hMb
    have : D.termRW A.σw M = ocEpsilon X.q A.Λ M ^ (1 + A.σw) := by
      simp only [OCData.termRW, OCData.eps, hDq, hDΛ]
    rw [this]
    linarith
  have hr0 : 0 ≤ D.termRW A.σw M := by
    have hε : 0 < ocEpsilon X.q A.Λ M := (AVRegularity.Scales.epsilon_basic (m := M) hq1 hΛ).1
    have : D.termRW A.σw M = ocEpsilon X.q A.Λ M ^ (1 + A.σw) := by
      simp only [OCData.termRW, OCData.eps, hDq, hDΛ]
    rw [this]
    exact Real.rpow_nonneg hε.le _
  have hclose := hδ' (y := D.termRW A.σw M) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr0]; exact hr)
  -- the regularizer clause of the invariant
  have hreg := (hI.2.2.2.2.2.2.2.2.1 v u γ).2.2.2.2 1 one_pos 0 (Nat.zero_le _)
  have hk : Gw.kernelOf PW (fun _ => isoPairedKernel (D.termRW A.σw M) nW)
      (fun _ => isoPairedKernel (D.termRW A.σw M) nW) v u γ =
      isoPairedKernel (D.termRW A.σw M) nW := by
    unfold GenStage.kernelOf
    split <;> rfl
  unfold GenStage.sysS at hreg
  rw [hk] at hreg
  exact ckerPos_of_close (t := aM) hreg ⟨le_rfl, hwin⟩ hclose hm

/-- The defect step of the fine tail. -/
theorem termFineDefect : TermFineDefectStatement := termFineDefect_of_cker termCker

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # `TermFineLiftStatement` from `TermLiftEnergyStatement`

The passage at a context (`termFineLiftAt_of_energy`) follows the cascade's `fineLiftAt`: the
energy of `(Û, Ŵ)` gives the `L²` bound in time, the integrability and the coarse energy
(`energy_forms`, generic in the Hilbert family); the classical clause gives the value jet, the
regularity and the periodicity of the lifted field; the strong measurability is part of the energy
statement. The positivity facts (`ρ_* > 0`, `ν = κ_M > 0`, the masses) are those of the terminal
data. The prefix version raises the threshold constant to `max C₀ 0`, since the coarse energy
bound is stated with `C ≥ 0`.

Degenerate cases: an empty family (everything vacuous); `C = 0` (the energy is `0`); `L_f = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The passage at a context**: `FineLiftAt` from the energy of the lifted field. -/
theorem termFineLiftAt_of_energy
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {C : ℝ} (hC : 0 ≤ C) (hcK : 0 < cK)
    (h128 : 128 ≤ A.Λ) (h : TermLiftEnergyAt c x C) : FineLiftAt c x C := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, -⟩ := c.data
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hκM : 0 < c.D.κ M := by
    have hch : IsOCBandChain X.α X.q A.Λ X.ζ M c.D.κ := hchain
    exact AVRegularity.CycleReference.bandChain_pos (by omega) X.hζ hch le_rfl
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    AVRegularity.Construction.Preservation.Buffer.birth_compMass_pos hqq hΛ c.lawW v.1
  have heps : 0 < c.D.eps M := by
    show 0 < ocEpsilon c.D.q c.D.Λ M
    rw [hq, hΛD]
    exact Applications.eps_pos (m := M) X.hq.1 h128
  have hρ : 0 < c.D.termRStar cK M := by
    unfold OCData.termRStar
    exact mul_pos hcK heps
  obtain ⟨Û, Ŵ, hcl, htr, hmeas, hE⟩ := h
  have hCn : 0 ≤ C * c.normF := mul_nonneg hC (Real.sqrt_nonneg _)
  obtain ⟨hM, hI, hS⟩ := Construction.Residual.Presentation.Cascade.energy_forms
    (E := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (c.D.termRStar cK M) (c.D.κ M)
    (c.Gw.mass c.lawW) hπ hρ hκM c.tp (c.a + A.T₀) Û Ŵ htr hmeas (C * c.normF) hCn hE
  refine ⟨Û, ⟨hM, fun v t ht => ?_, fun v t ht => ?_⟩, hI, ?_⟩
  · exact Construction.Preservation.FullLift.classicalRep_value_ae _ _ (hcl v t ht)
  · exact ⟨(hcl v t ht).2.1, (hcl v t ht).2.2.1⟩
  · calc _ ≤ C * c.normF := hS
      _ ≤ _ := le_rfl

/-- **`TermFineLiftStatement` from `TermLiftEnergyStatement`.** -/
theorem termFineLift_of_energy (hE : TermLiftEnergyStatement) : TermFineLiftStatement := by
  intro X
  obtain ⟨Λ₀, h128, hE⟩ := hE X
  refine ⟨Λ₀, h128, fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 hΛ
  obtain ⟨kc₀, hE⟩ := hE A hΛ hV
  refine ⟨kc₀, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, hE⟩ := hE kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn, hE⟩ := hE sXT sZT hX hZ Kout hK
  refine ⟨Kn, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl => ?_⟩
  obtain ⟨C₀, cg, Cg, hcg, CH, Υ, hCH, hΥ, hE⟩ :=
    hE Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
      cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨max C₀ 0, cg, Cg, hcg, CH, Υ, hCH, hΥ, fun C hC j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hE⟩ := hE C (le_trans (le_max_left _ _) hC) j₀ hj₀
  exact ⟨M₀, fun M hM c x => termFineLiftAt_of_energy c x (le_trans (le_max_right _ _) hC) hcK
    hΛ128 (hE M hM c x)⟩

/-- **The fine matrix tail (`TermFineTailStatement`) from the energy of the lifted field alone**: the defect step is
proved (`termFineDefect`). -/
theorem termFineTail_of_energy (hE : TermLiftEnergyStatement) : TermFineTailStatement :=
  termFineTail_of_lift_defect (termFineLift_of_energy hE) termFineDefect

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The split of `TermLiftEnergyStatement` and its assembly

* `TermLiftRegAt`: the lifted field has representatives `Û` of order `K_f + 1` and `Ŵ` of order
  `K_f + 2`, both with the lifted field as classical representative on the window (of the orders
  `K_f + 1` and `K_f + 2`), `Ŵ` truncating to `Û`, 
* `TermLiftEnergyBoundAt`: every such pair is strongly measurable in time (from the continuity of `W = P_pZ`, the energy step) and has strong energy `≤ C ‖f‖₂` at `(r_*, κ_M)`.
  The pair is determined by the lifted field (all jets up to the order are classical derivatives),
  so the energy is a function of the lifted field.

Degenerate cases: an empty family (vacuous); `f = 0` (the energy bound is `0`); `L_f = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **(a) Regularity of the lifted field at the orders `K_f + 1`, `K_f + 2`**. -/
def TermLiftRegAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (_x : TermResAux c) : Prop :=
  ∃ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Û v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1)) ∧
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Ŵ v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1 + 1)) ∧
    (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ (fineOrder (A := A) + 1)) (Ŵ v t) = Û v t)

/-- **(b) The energy of the lifted field**. -/
def TermLiftEnergyBoundAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid
    kW cP CP cHP Cw Ce cker j₀ M) (_x : TermResAux c) (C : ℝ) : Prop :=
  ∀ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Û v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1)) →
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Ŵ v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1 + 1)) →
    (∀ v, AEStronglyMeasurable (Û v) (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    strongEnergy (c.D.termRStar cK M) (c.D.κ M) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Û Ŵ ≤
      ENNReal.ofReal (C * c.normF)

/-- The regularity statement with the prefix of `entry_terminal_residual`. -/
def TermLiftRegStatement : Prop := TermResPrefix fun c x _ _ _ _ _ => TermLiftRegAt c x

/-- The energy-bound statement with the prefix of `entry_terminal_residual`. -/
def TermLiftEnergyBoundStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => TermLiftEnergyBoundAt c x C

/-- The parts give the energy statement at a context. -/
theorem termLiftEnergyAt_of_parts
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {C : ℝ} (ha : TermLiftRegAt c x)
    (hb : TermLiftEnergyBoundAt c x C) : TermLiftEnergyAt c x C := by
  obtain ⟨Û, Ŵ, h1, h2, h3⟩ := ha
  obtain ⟨h4, h5⟩ := hb Û Ŵ h1 h2
  exact ⟨Û, Ŵ, h1, h3, h4, h5⟩

/-- **`TermLiftEnergyStatement` from (a) and (b).** -/
theorem termLiftEnergy_of_parts (hA : TermLiftRegStatement) (hB : TermLiftEnergyBoundStatement) :
    TermLiftEnergyStatement := by
  intro X
  obtain ⟨Λ₁, h128, hA⟩ := hA X
  obtain ⟨Λ₂, -, hB⟩ := hB X
  refine ⟨max Λ₁ Λ₂, le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 (le_trans (le_max_left _ _) hΛ)
  obtain ⟨kc₁, hA⟩ := hA A (le_trans (le_max_left _ _) hΛ) hV
  obtain ⟨kc₂, hB⟩ := hB A (le_trans (le_max_right _ _) hΛ) hV
  refine ⟨max kc₁ kc₂, fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, hA⟩ := hA kc (le_trans (le_max_left _ _) hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, hB⟩ := hB kc (le_trans (le_max_right _ _) hkc)
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, max Kf₁ Kf₂, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hA⟩ := hA sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
    Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, hB⟩ := hB sXT sZT (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hZ)
    Kout (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₁ ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₂ ≤ n := fun h => le_trans (le_max_right _ _) h
  obtain ⟨C₀₁, cg₁, Cg₁, hcg₁, CH₁, Υ₁, hCH₁, hΥ₁, hA⟩ :=
    hA Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0 (m1 hKs) (m1 hKan)
      (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₀₂, cg₂, Cg₂, hcg₂, CH₂, Υ₂, hCH₂, hΥ₂, hB⟩ :=
    hB Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0 (m2 hKs) (m2 hKan)
      (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨max C₀₂ C₀₁, 1, 1, one_pos, max CH₁ CH₂, max Υ₁ Υ₂,
    le_trans hCH₁ (le_max_left _ _), lt_of_lt_of_le hΥ₁ (le_max_left _ _), fun C hC j₀ hj₀ => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀
  obtain ⟨M₁, hA⟩ := hA C (le_trans (le_max_right _ _) hC) j₀ hj₁
  obtain ⟨M₂, hB⟩ := hB C (le_trans (le_max_left _ _) hC) j₀ hj₂
  exact ⟨max M₁ M₂, fun M hM c x => termLiftEnergyAt_of_parts c x
    (hA M (le_trans (le_max_left _ _) hM) c x) (hB M (le_trans (le_max_right _ _) hM) c x)⟩

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
section
/-! **`FilterSchurWStatement`, the weak price of the Schur bound.**

The prefix form of `schurW_at`: the constant `A_k` of the uniform identity price at the order
`k_c + 2 p_T` is fixed after `k_c`; the constant `C₀` absorbs
`K_c A_k (|W|+2) 4 max(C_w,0) max(C_χ,0)`; the level `M` is late enough for the scale facts of
`seedStruct_scales`, for the price (`m₀ + 2 ≤ M`) and for the smallness of the weak ledger and the
birth factor (`small_core`). If `c_H^P ≤ 0` there is no context (the terminal law has
`0 < c_H`).

Degenerate cases: `C_w = 0` or `C_χ ≤ 0`: `C₀ = 0` and the bound is `0 ≤ …`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- A Schur bound is monotone in the bound. -/
theorem schur_mono {ι : Type*} [Fintype ι] {θ θ' : ℝ} {b : ι → ι → ℝ}
    (h : SchurBound θ b) (hθ : θ ≤ θ') : SchurBound θ' b :=
  ⟨fun i => (h.1 i).trans hθ, fun i => (h.2 i).trans hθ⟩

/-- The arithmetic of the constant `C₀`. -/
theorem arith {Ak cd T Cw Cχ e Kc C : ℝ} (hAk : 0 ≤ Ak) (hcd : cd ≤ T + 1) (_hT : 0 ≤ T)
    (hCw : 0 ≤ Cw) (he : 0 < e) (hKc : 0 < Kc)
    (hC : Kc * (Ak * ((T + 1) * (4 * max Cw 0 * max Cχ 0))) ≤ C) :
    Ak * (cd * (4 * Cw * max (Cχ * e) 0)) ≤ C / Kc * e := by
  have h1 : max (Cχ * e) 0 = max Cχ 0 * e := by
    rw [max_mul_of_nonneg _ _ he.le, zero_mul]
  have hcd0 : cd ≤ T + 1 := hcd
  have hm : 0 ≤ max Cχ 0 := le_max_right _ _
  have hCw' : max Cw 0 = Cw := max_eq_left hCw
  rw [h1]
  have h2 : Ak * (cd * (4 * Cw * (max Cχ 0 * e))) ≤
      Ak * ((T + 1) * (4 * max Cw 0 * max Cχ 0)) * e := by
    rw [hCw']
    have : cd * (4 * Cw * (max Cχ 0 * e)) ≤ (T + 1) * (4 * Cw * (max Cχ 0 * e)) :=
      mul_le_mul_of_nonneg_right hcd0 (by positivity)
    calc Ak * (cd * (4 * Cw * (max Cχ 0 * e))) ≤ Ak * ((T + 1) * (4 * Cw * (max Cχ 0 * e))) :=
          mul_le_mul_of_nonneg_left this hAk
      _ = _ := by ring
  have h3 : Ak * ((T + 1) * (4 * max Cw 0 * max Cχ 0)) ≤ C / Kc := by
    rw [le_div_iff₀ hKc]
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 he.le)

/-- The smallness facts, for a possibly nonpositive `c_H`. -/
theorem small (X : TermConstruction) (A : TermArgs X) (hΛ : 128 ≤ A.Λ) (hV : A.Valid)
    (cHP Cχ : ℝ) :
    ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → 0 < cHP →
      cHP / ((max 1 A.nWords : ℕ) : ℝ) * ocEpsilon X.q A.Λ (M - 1) ^ (A.η₀ / 2) ≤ 1 ∧
        (|Cχ| + 1) * ocEpsilon X.q A.Λ M ^ A.χw ≤ 1 / 16 := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, -, hχw, hη₀, -⟩, -⟩ := hV
  by_cases hcH : 0 < cHP
  · have hwc : 0 < max 1 A.nWords := lt_of_lt_of_le one_pos (le_max_left _ _)
    obtain ⟨M₁, hM₁⟩ := small_core X.hq.1 hΛ hχw (half_pos hη₀) (half_pos hη₀) 1 1 Cχ 1 cHP
      (max 1 A.nWords) one_pos one_pos le_rfl hcH hwc
    refine ⟨M₁, fun M hM _ => ⟨(hM₁ M hM).1, ?_⟩⟩
    have := (hM₁ M hM).2.1
    norm_num at this
    linarith
  · exact ⟨0, fun _ _ h => absurd h hcH⟩

/-- **(SW), `FilterSchurWStatement`.** -/
theorem filterSchurW : FilterSchurWStatement := by
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  refine ⟨max Λc 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have h128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hbw : 0 < A.bw := hV.2.2.1.1
  have hV' : A.Valid := hV
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, -, -, -⟩, -, hsch, -⟩ := hV
  have htT : 0 ≤ A.tT := hsch.2.2.2.2.2.2.2.2.1.le
  refine ⟨0, fun kc _ => ?_⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, 0, fun sXT sZT hX hZ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _
    hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩
  obtain ⟨Ak, hAk0, m₀, hm₀2, hunif⟩ :=
    AVRegularity.Construction.Preservation.FullLift.uniform_native_identity_kernel_price
      X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hbw (kc + 2 * A.pT)
      (kc + 2 * A.pT + A.Dt) A.Dt le_rfl (fun _ => 1) (fun _ _ => zero_le_one)
  have hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw (kc + 2 * A.pT) A.Dt (fun _ => 1) Ak m₀ :=
    fun D hDα hDq hDΛ hDζ hseq => hunif ScalarH D hDα hDq hDΛ hDζ hseq
  obtain ⟨Ms, hMs2, hMs⟩ := hcore A.Λ hΛc' cr A.σw A.tT CL hcr0 hσw.le htT
  obtain ⟨M₁, hM₁⟩ := small X A h128 hV' cHP Cχ
  have hKc := filterKc_pos A CP kc
  refine ⟨filterKc A CP kc * (Ak * ((((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
    (4 * max Cw 0 * max Cχ 0))), 1, 0, one_pos, 1, 1, le_rfl, one_pos,
    fun C hC j₀ hcar => ?_⟩
  refine ⟨max Ms (max M₁ (max (m₀ + 2) (j₀ + 1))), fun M hM c x => ?_⟩
  have hMs' : Ms ≤ M := le_trans (le_max_left _ _) hM
  have hM1' : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMm : m₀ + 2 ≤ M :=
    le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  have hMj : j₀ + 1 ≤ M :=
    le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := c.data
  obtain ⟨-, hρε, -, hCL⟩ := hMs M hMs' c.D hDα hDq hDΛ hband
  have hq1 : 1 < c.D.q := by rw [hDq]; exact X.hq.1
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hDΛ]; exact h128
  obtain ⟨hmass, -, hcHeq, hiota, hwcEq, hetaB, -⟩ := c.law
  have hcH : 0 < cHP := by rw [← hcHeq]; exact c.lawT.cH_pos
  obtain ⟨h1, h2⟩ := hM₁ M hM1' hcH
  have hepsM : c.D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hF1 : 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT false := by
    refine birthFactor_ge_one hq1 hΛ128 c.lawT hiota ?_ false
    rw [hcHeq, hwcEq, hetaB, hDq, hDΛ]
    exact h1
  have hSm : max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    rw [hepsM]
    have he : 0 ≤ ocEpsilon X.q A.Λ M ^ A.χw :=
      Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 h128).1.le _
    refine max_le ?_ (by norm_num)
    nlinarith [le_abs_self Cχ, abs_nonneg Cχ]
  have hε : 0 < c.D.eps M := by
    rw [hepsM]; exact (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 h128).1
  have hmain := schurW_at c x hV' h128 le_rfl le_rfl hcar hX hZ hMj
    (by omega) hρε hCL x.cwNonneg kc Ak m₀ hMm hAk0 hu hF1 hSm
  have hcard : ((insert [] (wordsUpTo A.alph (A.RT + 1))).card : ℝ) ≤
      ((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1 := by
    exact_mod_cast Finset.card_insert_le _ _
  exact schur_mono hmain
    (arith hAk0 hcard (Nat.cast_nonneg _) x.cwNonneg (Real.rpow_pos_of_pos hε _) hKc hC)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **`FilterSchurFStatement`, the fresh price of the Schur bound.**

The prefix form of `schurF_at`; the constants are chosen as for the weak price, with
`C₀ = K_c A_k (|W|+2) 2|A| max(C_w,0) (1 + √(max(1,n)/c_H^P))`.

Degenerate cases: `C_w = 0` or `A = ∅`: `C₀ = 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- The arithmetic of the constant `C₀` for the fresh price. -/
theorem arithF {Ak cd T L Cw s e Kc C : ℝ} (hAk : 0 ≤ Ak) (hcd : cd ≤ T + 1)
    (_hT : 0 ≤ T) (hCw : 0 ≤ Cw) (hL : 0 ≤ L) (hs : 0 ≤ s) (he : 0 < e) (hKc : 0 < Kc)
    (hC : Kc * (Ak * ((T + 1) * (2 * L * max Cw 0 * (1 + s)))) ≤ C) :
    Ak * (cd * (2 * L * Cw * ((1 + s) * e))) ≤ C / Kc * e := by
  have hCw' : max Cw 0 = Cw := max_eq_left hCw
  rw [hCw'] at hC
  have h2 : Ak * (cd * (2 * L * Cw * ((1 + s) * e))) ≤
      Ak * ((T + 1) * (2 * L * Cw * (1 + s))) * e := by
    have : cd * (2 * L * Cw * ((1 + s) * e)) ≤ (T + 1) * (2 * L * Cw * ((1 + s) * e)) :=
      mul_le_mul_of_nonneg_right hcd (by positivity)
    calc Ak * (cd * (2 * L * Cw * ((1 + s) * e))) ≤
          Ak * ((T + 1) * (2 * L * Cw * ((1 + s) * e))) :=
          mul_le_mul_of_nonneg_left this hAk
      _ = _ := by ring
  have h3 : Ak * ((T + 1) * (2 * L * Cw * (1 + s))) ≤ C / Kc := by
    rw [le_div_iff₀ hKc]
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 he.le)

/-- **(SF), `FilterSchurFStatement`.** -/
theorem filterSchurF : FilterSchurFStatement := by
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := AVRegularity.EntryTerminal.Ingredients.seedStruct_scales X
  refine ⟨max Λc 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have h128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hbw : 0 < A.bw := hV.2.2.1.1
  have hV' : A.Valid := hV
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, -, -, -⟩, -, hsch, -⟩ := hV
  have htT : 0 ≤ A.tT := hsch.2.2.2.2.2.2.2.2.1.le
  refine ⟨0, fun kc _ => ?_⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, 0, fun sXT sZT hX hZ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _
    hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩
  obtain ⟨Ak, hAk0, m₀, hm₀2, hunif⟩ :=
    AVRegularity.Construction.Preservation.FullLift.uniform_native_identity_kernel_price
      X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ h128 X.ζ X.hζ A.bw hbw (kc + 2 * A.pT)
      (kc + 2 * A.pT + A.Dt) A.Dt le_rfl (fun _ => 1) (fun _ _ => zero_le_one)
  have hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw (kc + 2 * A.pT) A.Dt (fun _ => 1) Ak m₀ :=
    fun D hDα hDq hDΛ hDζ hseq => hunif ScalarH D hDα hDq hDΛ hDζ hseq
  obtain ⟨Ms, hMs2, hMs⟩ := hcore A.Λ hΛc' cr A.σw A.tT CL hcr0 hσw.le htT
  obtain ⟨M₁, hM₁⟩ := small X A h128 hV' cHP Cχ
  have hKc := filterKc_pos A CP kc
  refine ⟨filterKc A CP kc * (Ak * ((((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
    (2 * (A.alph.card : ℝ) * max Cw 0 *
      (1 + Real.sqrt (((max 1 A.nWords : ℕ) : ℝ) / cHP))))), 1, 0, one_pos, 1, 1, le_rfl, one_pos,
    fun C hC j₀ hcar => ?_⟩
  refine ⟨max Ms (max M₁ (max (m₀ + 2) (j₀ + 1))), fun M hM c x => ?_⟩
  have hMs' : Ms ≤ M := le_trans (le_max_left _ _) hM
  have hM1' : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMm : m₀ + 2 ≤ M :=
    le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  have hMj : j₀ + 1 ≤ M :=
    le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hM
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := c.data
  obtain ⟨-, hρε, -, hCL⟩ := hMs M hMs' c.D hDα hDq hDΛ hband
  have hq1 : 1 < c.D.q := by rw [hDq]; exact X.hq.1
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hDΛ]; exact h128
  obtain ⟨hmass, -, hcHeq, hiota, hwcEq, hetaB, -⟩ := c.law
  have hcH : 0 < cHP := by rw [← hcHeq]; exact c.lawT.cH_pos
  obtain ⟨h1, h2⟩ := hM₁ M hM1' hcH
  have hepsM : c.D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hF1 : 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT false := by
    refine birthFactor_ge_one hq1 hΛ128 c.lawT hiota ?_ false
    rw [hcHeq, hwcEq, hetaB, hDq, hDΛ]
    exact h1
  have hSm : max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2 := by
    rw [hepsM]
    have he : 0 ≤ ocEpsilon X.q A.Λ M ^ A.χw :=
      Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 h128).1.le _
    refine max_le ?_ (by norm_num)
    nlinarith [le_abs_self Cχ, abs_nonneg Cχ]
  have hε : 0 < c.D.eps M := by
    rw [hepsM]; exact (AVRegularity.Scales.epsilon_basic (m := M) X.hq.1 h128).1
  have hmain := schurF_at c x hV' h128 le_rfl le_rfl hcar hX hZ hMj
    (by omega) hρε hCL x.cwNonneg kc Ak m₀ hMm hAk0 hu hF1 hSm
  have hcard : ((insert [] (wordsUpTo A.alph (A.RT + 1))).card : ℝ) ≤
      ((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1 := by
    exact_mod_cast Finset.card_insert_le _ _
  rw [hwcEq, hcHeq] at hmain
  exact schur_mono hmain
    (arithF hAk0 hcard (Nat.cast_nonneg _) x.cwNonneg (Nat.cast_nonneg _)
      (Real.sqrt_nonneg _)
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ c.D.Λ)) _) hKc hC)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The regularity of the lifted field at the orders `K_f + 1`, `K_f + 2`, at a context

At a context with the slow periodicity of the coefficients (`CovTruncLiftSlowAt`), the
floors `s_X, s_Z ≥ K_f + 2` and `N_T + K_f + 2 + 2 p_T ≤ K_out`, the lifted field is `C^{K_f+2}` and
periodic at every time of the window (`menuLiftedRep_contDiff`, `menuLiftedRep_periodic`),
hence has the classical Hilbert representatives `Ŵ` of order `K_f + 2` and `Û = trunc Ŵ`.

Degenerate cases: an empty family; `Z = 0`; `L_f = 0`. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The lifted field is `C^{K_f+2}` and periodic on the window.** -/
theorem liftField_regular
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hslow : CovTruncLiftSlowAt c)
    (hX : fineOrder (A := A) + 1 + 1 ≤ sXT) (hZ : fineOrder (A := A) + 1 + 1 ≤ sZT)
    (hK : A.NT + (fineOrder (A := A) + 1 + 1) + 2 * A.pT ≤ Kout) :
    ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((fineOrder (A := A) + 1 + 1 : ℕ) : ℕ∞)
        (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v) ∧
      IsZ2Periodic
        (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v) := by
  classical
  intro v t ht
  obtain ⟨hα, hq, hΛD, hζ, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hB : 0 < c.D.κ (M - 1) :=
    AVRegularity.CycleReference.bandChain_pos (by omega) X.hζ hband (Nat.sub_le M 1)
  have hρ : 0 < cr * liftLength c.D M := by
    rw [(congrArg (· * liftLength c.D M) x.one).trans (one_mul _)]
    exact Real.sqrt_pos.mpr (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ1))
  have hν : 0 < c.D.κ M :=
    AVRegularity.CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hcc : 0 < c.D.cellScaleSq M := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hν
  have hprof : IsFastProfile c.D.ζ := hζ ▸ X.hζ
  have hband' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hα, hq, hΛD, hζ, hterm]; exact hband
  have hKlt : A.NT + (fineOrder (A := A) + 1 + 1) ≤ A.Khat Kout - 2 * A.pT := by
    dsimp only [TermArgs.Khat]; omega
  have haC : ContDiff ℝ ((A.NT + (fineOrder (A := A) + 1 + 1) : ℕ) : ℕ∞) (c.aRep t) := by
    refine contDiff_pi.2 fun w => ?_
    exact ((c.lift.2.1 w t ht).2.2.1).of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast hKlt))
  have haP : IsZ2Periodic (c.aRep t) := fun p y => by
    funext w
    exact (c.lift.2.1 w t ht).2.2.2.1 p y
  have hsm := menuLiftedRep_contDiff (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev c.CcT
    hΛ1 hprof hband' sXT sZT c.lift.1 (fineOrder (A := A) + 1 + 1) hX hZ c.aRep t haC
  have hper := menuLiftedRep_periodic (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW hlev c.CcT
    hρ.ne' hcc.ne' sXT sZT c.lift.1 c.aRep t hΛ1 hcc (hslow t ht) haP
  exact ⟨contDiff_pi.1 hsm v, fun p y => congrFun (hper p y) v⟩

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # `TermLiftRegStatement` is proved

At a context (`termLiftRegAt_of_slow`): the lifted field is `C^{K_f+2}` and periodic on the window
(`liftField_regular`), so `Ŵ v t` is its classical Hilbert representative of order `K_f + 2`
(`0` off the window) and `Û = trunc Ŵ`. With the prefix: the slow periodicity is the proved
`covTruncLiftSlow`; the floors `s_X, s_Z ≥ K_f + 2`, `K_out ≥ N_T + K_f + 2 + 2 p_T` are prefix
floors (`Floors`).

Degenerate cases: an empty family; `L_f = 0`; the window is a point. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **(a) at a context.** -/
theorem termLiftRegAt_of_slow
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hslow : CovTruncLiftSlowAt c)
    (hX : fineOrder (A := A) + 1 + 1 ≤ sXT) (hZ : fineOrder (A := A) + 1 + 1 ≤ sZT)
    (hK : A.NT + (fineOrder (A := A) + 1 + 1) + 2 * A.pT ≤ Kout) : TermLiftRegAt c x := by
  classical
  have hreg := liftField_regular c x hΛ hslow hX hZ hK
  let F : ∀ v : CompIn c.Gw.comps, ℝ → Vec 2 → ScalarH v.1.root := fun v t y =>
    menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v
  let Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root) :=
    fun v t => if h : t ∈ Set.Icc c.tp (c.a + A.T₀) then
      classicalHilbertHk (fineOrder (A := A) + 1 + 1) (F v t) (hreg v t h).1 (hreg v t h).2
    else 0
  have hŴ : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Ŵ v t) (F v t) (fineOrder (A := A) + 1 + 1) := by
    intro v t ht
    simp only [Ŵ, ht, ↓reduceDIte]
    exact classicalHilbertHk_rep _ _ (hreg v t ht).1 (hreg v t ht).2
  refine ⟨fun v t => truncateTorusHk (Nat.le_succ (fineOrder (A := A) + 1)) (Ŵ v t), Ŵ,
    fun v t ht => ?_, hŴ, fun v => Filter.Eventually.of_forall fun t => rfl⟩
  exact classicalRep_truncate (Nat.le_succ _) le_rfl (Ŵ v t) (F v t)
    (classicalRep_order_mono _ _ (hŴ v t ht) (Nat.le_succ _))

/-- The floors of the regularity: `Λ ≥ 128`, `s_X, s_Z ≥ K_f + 2`, `K_out ≥ N_T + K_f + 2 + 2p_T`. -/
def Floors (_c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
    Cw Ce cker j₀ M) : Prop :=
  128 ≤ A.Λ ∧ fineOrder (A := A) + 1 + 1 ≤ sXT ∧ fineOrder (A := A) + 1 + 1 ≤ sZT ∧
    A.NT + (fineOrder (A := A) + 1 + 1) + 2 * A.pT ≤ Kout

private theorem floors :
    TermResPrefix fun c _ _ _ _ _ _ => Floors c := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ⟨fineOrder (A := A) + 1 + 1,
    fineOrder (A := A) + 1 + 1, A.NT + (fineOrder (A := A) + 1 + 1) + 2 * A.pT,
    fun sXT sZT hX hZ Kout hK => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨0, fun M hM c x => ?_⟩⟩
  exact ⟨hΛ, hX, hZ, hK⟩

/-- **(a) is proved.** -/
theorem termLiftReg : TermLiftRegStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c _ _ _ => CovTruncLiftSlowAt c) (P₂ := fun c _ _ _ => Floors c)
    covTruncLiftSlow floors
  refine termFluxPrefix_map
    (P := fun c _ _ _ => CovTruncLiftSlowAt c ∧ Floors c)
    (R := fun c x _ _ => TermLiftRegAt c x) ?_ hjoin
  intro X A kc C₁ hΛ hC₁
  refine ⟨0, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C _
  exact termLiftRegAt_of_slow c x hP.2.1 hP.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # The split of `TermLiftEnergyBoundStatement` into measurability and energy

* `TermLiftMeasAt`: every classical `Û` is strongly measurable in time on the window.
* `TermLiftEnergyOnlyAt`: every classical pair has strong energy `≤ C ‖f‖₂` at `(r_*, κ_M)`.

The assembly `termLiftEnergyBound_of_parts` (energy and measurability give the energy bound) is proved; with
`termLiftReg` it gives `TermLiftEnergyStatement` (`termLiftEnergy_of_split`) and
`termFineTail_of_split`.

Degenerate cases: an empty family; `f = 0` (the energy is `0`). -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **(b2) Measurability in time of the representative**. -/
def TermLiftMeasAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (_x : TermResAux c) : Prop :=
  ∀ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Û v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1)) →
    ∀ v, AEStronglyMeasurable (Û v) (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))

/-- **(b1) The energy of the classical pair**. -/
def TermLiftEnergyOnlyAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid
    kW cP CP cHP Cw Ce cker j₀ M) (_x : TermResAux c) (C : ℝ) : Prop :=
  ∀ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Û v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1)) →
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Ŵ v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1 + 1)) →
    strongEnergy (c.D.termRStar cK M) (c.D.κ M) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Û Ŵ ≤
      ENNReal.ofReal (C * c.normF)

/-- (b2) with the prefix. -/
def TermLiftMeasStatement : Prop := TermResPrefix fun c x _ _ _ _ _ => TermLiftMeasAt c x

/-- (b1) with the prefix. -/
def TermLiftEnergyOnlyStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => TermLiftEnergyOnlyAt c x C

/-- **(b) from (b1) and (b2).** -/
theorem termLiftEnergyBound_of_parts (h1 : TermLiftEnergyOnlyStatement)
    (h2 : TermLiftMeasStatement) : TermLiftEnergyBoundStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x _ C => TermLiftEnergyOnlyAt c x C) (P₂ := fun c x _ _ => TermLiftMeasAt c x)
    h1 h2
  refine termFluxPrefix_map
    (P := fun c x _ C => TermLiftEnergyOnlyAt c x C ∧ TermLiftMeasAt c x)
    (R := fun c x _ C => TermLiftEnergyBoundAt c x C) ?_ hjoin
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C hC
  obtain ⟨h1, h2⟩ := hP
  exact fun Û Ŵ hÛ hŴ => ⟨h2 Û hÛ, (h1 Û Ŵ hÛ hŴ).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)))⟩

/-- **`TermLiftEnergyStatement` from (b1), (b2)**. -/
theorem termLiftEnergy_of_split (h1 : TermLiftEnergyOnlyStatement) (h2 : TermLiftMeasStatement) :
    TermLiftEnergyStatement :=
  termLiftEnergy_of_parts termLiftReg (termLiftEnergyBound_of_parts h1 h2)

/-- **The fine matrix tail from the energy and measurability statements.** -/
theorem termFineTail_of_split (h1 : TermLiftEnergyOnlyStatement) (h2 : TermLiftMeasStatement) :
    TermFineTailStatement :=
  termFineTail_of_energy (termLiftEnergy_of_split h1 h2)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
