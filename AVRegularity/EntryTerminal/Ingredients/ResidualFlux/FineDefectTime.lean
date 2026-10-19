-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGluedSlow
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.EntryTerminal.Ingredients.Recon.Energy.Chain
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.KernelDefect.UniformDerivArray
import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur
import AVRegularity.KernelEnergyPlane.PlaneFluxTermFamily
public import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import Mathlib.CategoryTheory.Countable

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Residual.Presentation

/-! Gluing the periodic native mean fluxes on their constrained grades. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Native data are slow-periodic, and an active pulse reads the periodic supplied coefficients. -/
theorem covTruncGluedPeriodic_of_slow
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hM : 1 ≤ M) (hslow : CovTruncLiftSlowAt c) :
    CovTruncGluedBoundedAt c := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hB : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ hband (Nat.sub_le M 1)
  have hρ : 0 < cr * liftLength c.D M := by
    rw [(congrArg (· * liftLength c.D M) x.one).trans (one_mul _)]
    exact Real.sqrt_pos.mpr (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ1))
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hcell : 0 < c.D.cellScaleSq M := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hν
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have htorus : IsTorusCompatible c.Gw.fam c.Gw.actual (c.D.eps (c.Gw.level - 1)) := by
    simpa only [hlev] using IsWeakStage.isTorusCompatible c.weak
  intro v t ht rs ns a hrs hpa p Y
  unfold menuGluedMeanFlux
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hodd
  · by_cases hcut : ocCutoff c.D.α c.D.q c.D.Λ M k t = 0
    · simp only [hcut, zero_smul]
    · apply congrArg (fun z => ocCutoff c.D.α c.D.q c.D.Λ M k t • z)
      have hpulse := covTruncPulse_meanFluxEuler_periodic (c.D.cellScaleSq M) (cr * liftLength c.D M)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / (cr * liftLength c.D M)) hρ.ne' hcell.ne'
        (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
          (c.Gw.fam.fiber ⟨k, hodd⟩ (c.Gw.actual ⟨k, hodd⟩))) (c.CcT k) A.dW r n (hrs r hr)
        (fun s y => c.D.flowOf (M - 1) s y (c.D.slotAnchor M k))
        (fun s y => c.D.flowOf (M - 1) (c.D.slotAnchor M k) y s) a t
        (fun p y => CycleReference.streamFlow_lattice_equivariant (c.D.hΦ (M - 1))
          t (c.D.slotAnchor M k) y p)
        (fun p y => CycleReference.streamFlow_lattice_equivariant (c.D.hΦ (M - 1))
          (c.D.slotAnchor M k) t y p)
        (fun p X i j => congrFun (congrFun (native_familyLiftData_metric_shift c.D M hM k hρ.ne'
          (c.Gw.fam.fiber ⟨k, hodd⟩ (c.Gw.actual ⟨k, hodd⟩)) p _ X) i) j)
        (fun p v u d γ hγ α X z => by
          have hmem : γ ∈ (familyLiftData c.D c.Gw.level k (nativeChain c.Gw.level k)
              (cr * liftLength c.D M) (c.Gw.fam.fiber ⟨k, hodd⟩ (c.Gw.actual ⟨k, hodd⟩))).edge v u d := by
            simpa only [hlev] using hγ
          simpa only [hlev] using native_familyLiftData_edge_coeff_shift c.Gw htorus ⟨k, hodd⟩ hρ.ne'
            p v u d γ hmem α _ X z)
        (fun p hh hhH n m α X z v u => hslow t ht k hk hcut p hh hhH n m α X z v u) hpa v
      exact hpulse p Y
  · rfl

private theorem covTruncGlued_level :
    TermResPrefix fun c _ _ _ _ _ _ => 1 ≤ c.Gw.level := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ⟨0, 0, 0,
    fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨1, fun M hM c x => ?_⟩⟩
  change 1 ≤ c.Gw.level
  rw [c.weak.2.2.1]
  exact hM

/-- Bounded glued mean-flux periodicity, with the exact terminal residual prefix. -/
theorem covTruncGluedPeriodicBounded : CovTruncGluedPeriodicBoundedStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c _ _ _ => CovTruncLiftSlowAt c) (P₂ := fun c _ _ _ => 1 ≤ c.Gw.level)
    covTruncLiftSlow covTruncGlued_level
  refine termFluxPrefix_map
    (P := fun c _ _ _ => CovTruncLiftSlowAt c ∧ 1 ≤ c.Gw.level)
    (R := fun c _ _ _ => CovTruncGluedBoundedAt c) ?_ hjoin
  intro X A kc C₁ hΛ hC₁
  refine ⟨0, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C _
  exact covTruncGluedPeriodic_of_slow c x hΛ (c.weak.2.2.1 ▸ hP.2) hP.1

/-- **Regularity of the pre-truncation flux**: G is smooth at its required order and is periodic, with no open inputs. -/
theorem covTruncGReg : CovTruncGRegStatement :=
  covTruncGReg_of_bounded_gluedPeriodic covTruncGluedPeriodicBounded

end AVRegularity.Construction.Residual.Presentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-! # The energy step with the offset after the datum

`reconEnergyU` is `termReconEnergy` in the shape `ReconPrefixU`: the offset `ℓ` is quantified
after the terminal datum `A`, so it may depend on `A` (the proof of `termReconEnergy` uses `ℓ` only
through `rpord A ℓ`, and the constant `C_s` does not depend on it).

Special case: `ℓ` fixed gives `termReconEnergy` back. -/

/-- **The energy step with the offset `ℓ` after the datum `A`** (the same proof as `termReconEnergy`: `ℓ` enters
only through `rpord A ℓ`). -/
theorem reconEnergyU_of_statements (hL : EnergyLargeStatement) (hC : EnergyChainStatement)
    (hS : EnergySolutionStatement) : ReconPrefixU (κ := {Cs : ℝ // 0 ≤ Cs})
    fun c x kc ℓ Cs => ∀ hW, ReconEnergyAt c x kc ℓ hW Cs.1 := by
  intro X
  obtain ⟨ΛL, hΛL, hL⟩ := hL X
  obtain ⟨ΛS, hΛS, hS⟩ := hS X
  refine ⟨max ΛL ΛS, le_trans hΛL (le_max_left _ _), fun A hΛ hV ℓ => ⟨rpord A ℓ, fun kc hkc =>
    ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _
      cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker hcP => ?_⟩⟩⟩⟩
  obtain ⟨M₁, hM₁⟩ := hL A (le_trans (le_max_left _ _) hΛ) hV cHP
  have hK0 : 0 ≤ AVRegularity.CycleComparison.Coarse.covPolyConst
      (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT * Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1) :=
    mul_nonneg (Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l)
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨⟨(AVRegularity.CycleComparison.Coarse.covPolyConst
      (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT * Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
      (Real.sqrt 2 * max CP 0), mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _)
        (le_max_right _ _))⟩, 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨max M₁ 2, fun M hM c x hW => ?_⟩⟩
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hΛ' : 128 ≤ A.Λ := le_trans (le_trans hΛL (le_max_left _ _)) hΛ
  have hlarge := hM₁ hM1 c x
  have hch := hC c x kc ℓ hW hΛ' (by omega) (by omega) hlarge
  have hsol := hS A (le_trans (le_max_right _ _) hΛ) hM2 c x
  refine ⟨hch.1, hch.2.trans ?_⟩
  calc _ ≤ _ := mul_le_mul_right hsol _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hK0]
      congr 1
      ring

/-- The energy step with the offset after the datum. -/
theorem reconEnergyU : ReconPrefixU (κ := {Cs : ℝ // 0 ≤ Cs})
    fun c x kc ℓ Cs => ∀ hW, ReconEnergyAt c x kc ℓ hW Cs.1 :=
  reconEnergyU_of_statements energyLarge energyChain energySolution

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy
end
end

section
/-! **The gradient flux of the readout of the retained solution at a terminal context**.

At a context with a large level, the classical gradient flux `∇ a_Z` of the readout `a_Z` of the
retained solution has a realization of order `K` (for `K + 1 ≤ K̂ - 2`) on the window with
`(B⁻¹ ∫ ‖·‖²_{ρ,K;π})^{1/2} ≤ B⁻¹ √(|W_{R_T+1}| + 1) √2 max(C_P, 0) ‖f‖₂`. The route is the
strong energy of the readout (`readout_strongEnergy_of_diagonal_entries` as in `energyChain`),
the strong energy of the given retained solution (`energySolution`), and
`covGrad_hasFluxBound_of_strongEnergy`.

Special case: `f = 0` gives the bound `0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.EntryTerminal.Ingredients.Recon AVRegularity.EntryTerminal.Ingredients.Recon.Energy
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.CovGrad

theorem isClassicalRep_mono {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {W : TorusHk K E} {a : Vec 2 → E}
    {r r' : ℕ} (h : IsClassicalRep W a r) (hr : r' ≤ r) : IsClassicalRep W a r' :=
  ⟨hr.trans h.1, h.2.1.of_le (by exact_mod_cast hr), h.2.2.1,
    fun m hm w => h.2.2.2 m (hm.trans hr) w⟩

/-- **The realized gradient flux of the readout of the retained solution.** -/
theorem covGrad_ctx_energy (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid → ∀ cHP' : ℝ, ∃ M₀ : ℕ,
      ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
        {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ},
        M₀ ≤ M →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP' Cw
          Ce cker j₀ M) (x : TermResAux c) (kc : ℕ), kc + 2 * A.pT + 3 ≤ A.Khat Kout →
        HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
          (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
          (fun v t y => toFluxL (gradE (fun z => x.aZ t z v) y))
          (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
            (Real.sqrt 2 * max CP 0 * c.normF) / c.D.κ (M - 1)) := by
  obtain ⟨ΛL, hΛL, hL⟩ := energyLarge X
  obtain ⟨ΛS, hΛS, hS⟩ := energySolution X
  refine ⟨max ΛL ΛS, le_trans hΛL (le_max_left _ _), fun A hΛ hV cHP' => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hL A (le_trans (le_max_left _ _) hΛ) hV cHP'
  refine ⟨max M₀ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP Cw Ce cker j₀ M hM c x kc hkc
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
  have hflux := covGrad_hasFluxBound_of_strongEnergy (ι := CompIn c.Gw.comps)
    (h := fun v => ScalarH v.1.root) (L := A.Khat Kout) (K' := kc + 2 * A.pT) (by omega)
    (c.Gw.mass c.lawW) hν hE0 hπW (eZr c) (eZrw c) x.aZ hRw hae'
    (fun v t ht => isClassicalRep_mono (x.repZ v t ht) (by omega)) hen
  have hρe : rRho c = c.D.termRho cr M := by
    simp only [rRho, OCData.termRho, OCData.termB, OCData.termH, x.one, one_mul]
  rw [hρe] at hflux
  exact hflux

end AVRegularity.EntryTerminal.CovGrad
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.CovGrad
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The gradient term of the covariance truncation**.

`covTruncGradStep : CovTruncGradStatement`. At a context with a large level
(`covGrad_ctx_energy`, `covGrad_ledger`), the flux of `covTruncGrad` is
`N_t (p!)⁻¹ 𝒞(H_t)^p ∇ a_Z` with `N_t = 𝖩_M(t) - κ_{M-1} I`; the gradient flux of `a_Z` is realized
with mass `Y = √(|W|+1) √2 max(C_P,0) ‖f‖₂ / κ_{M-1}` and `covGrad_flux` gives the realization of
`covTruncGrad` with mass `(p!)⁻¹ ((k+2p)² C_cov E^δ)^p (C_N κ_{M-1}) Y`, which is
`C_* E^{δ p} ‖f‖₂` with `C_* = (p!)⁻¹ ((k_c+2p)² C_cov)^p C_N √(|W|+1) √2 max(C_P,0)`.

Special cases:
- `p = 0`: `covTruncGrad = N ∇ a_Z` and the price is `C_N √(|W|+1) √2 max(C_P,0) ‖f‖₂`.
- `f = 0`: `Z = 0`, the flux vanishes. -/

/-- **The gradient term of the covariance truncation.** -/
theorem covTruncGradStep : CovTruncGradStatement := by
  intro X
  obtain ⟨Λ₁, hΛ₁, hled⟩ := covGrad_ledger X
  obtain ⟨Λ₂, hΛ₂, hen⟩ := covGrad_ctx_energy X
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun A hΛ hV => ?_⟩
  obtain ⟨Ccov, Cn, hCcov, hCn, hLed⟩ := hled A (le_trans (le_max_left _ _) hΛ)
  refine ⟨0, fun kc _ => ⟨0, 0, kc + 2 * A.pT + 3, fun sXT sZT _ _ Kout hKout => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨Me, hMe⟩ := hen A (le_trans (le_max_right _ _) hΛ) hV cHP
  set Cstar : ℝ := ((A.pT.factorial : ℝ)⁻¹) * ((((kc + 2 * A.pT : ℕ) : ℝ) ^ 2 * Ccov) ^ A.pT) * Cn *
    (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * (Real.sqrt 2 * max CP 0)) with hCstar
  refine ⟨Cstar, 1, 1, one_pos, 1, 1, le_rfl, one_pos, ?_⟩
  intro C hC j₀ hj₀
  refine ⟨max Me 2, fun M hM c x => ?_⟩
  have hMe' : Me ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hkc : kc + 2 * A.pT + 3 ≤ A.Khat Kout :=
    le_trans hKout (le_max_left _ _)
  have hF := hMe hMe' c x kc hkc
  obtain ⟨hcov, hcovc, hN, hNc⟩ := hLed hM2 c x
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ le_trans hΛ₁ (le_trans (le_max_left _ _) hΛ)
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) (le_trans hΛ₁ (le_trans (le_max_left _ _) hΛ))
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hε0 : 0 < c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1
  have hω : 0 ≤ Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q :=
    mul_nonneg hCcov (Real.rpow_pos_of_pos hε0 _).le
  have haN : 0 ≤ Cn * c.D.κ (M - 1) := mul_nonneg hCn hν.le
  have hreg : ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((kc + 2 * A.pT + 1 : ℕ) : WithTop ℕ∞) (fun z => x.aZ t z v) ∧
        AVenhance.IsZ2Periodic (fun z => x.aZ t z v) := by
    intro v t ht
    have h1 := x.repZ v t ht
    exact ⟨h1.2.1.of_le (by exact_mod_cast (by omega : kc + 2 * A.pT + 1 ≤ A.Khat Kout - 2)),
      h1.2.2.1⟩
  have hflux := EntryTerminal.CovGrad.covGrad_flux (ι := CompIn c.Gw.comps)
    (h := fun v => ScalarH v.1.root) kc A.pT (I := Set.Icc c.tp (c.a + A.T₀)) measurableSet_Icc
    (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) hν hρ hπ
    (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) (covGradN c.D M)
    (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) (Cn * c.D.κ (M - 1)) hcovc.continuousOn
    hNc.continuousOn hω (fun t _ => hcov t) (fun t _ => hN t) haN
    (fun v t z => x.aZ t z v) _ hreg hF
  have hpow : (c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) ^ A.pT = c.covPrice := by
    unfold TermResCtx.covPrice
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
  have hcov0 : 0 ≤ c.covPrice := (Real.rpow_pos_of_pos hε0 _).le
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have key : ((A.pT.factorial : ℝ)⁻¹) * ((((kc + 2 * A.pT : ℕ) : ℝ) ^ 2 *
        (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q)) ^ A.pT * (Cn * c.D.κ (M - 1))) *
      (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF) / c.D.κ (M - 1)) = Cstar * c.covPrice * c.normF := by
    rw [← hpow, hCstar, ← mul_assoc ((((kc + 2 * A.pT : ℕ) : ℝ) ^ 2)), mul_pow, mul_pow]
    field_simp
  have hC0 : 0 ≤ Cstar := by
    rw [hCstar]
    have : 0 ≤ max CP 0 := le_max_right _ _
    have : 0 ≤ Ccov := hCcov
    positivity
  unfold CovTruncGradAt
  refine hasFluxBound_mono_Y hflux ?_
  rw [key]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hcov0) hn

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The defect version of `kernel_flux_bound_torus` at one time (generic)

The data `FDData` is a family of coefficients `B_{ijαd}` and moving paired kernels `S_{ijα}` with
`L` vanishing moments and widths `r_{ijα} ≤ q ρ`, `q ≤ 1`. For `V_j ∈ H^{K+1}` with classical
representatives `a_j`, the flux
`A_i = ∑_{j,α,d} B_{ijαd} ∇^{d-1}(I - S_{ijα})a_j`
has the realization `A_i = ∑ fdTerm …` of order `k` with

`‖A‖²_{ρ,k;π} ≤ (ν · q^L · M · θ)² ‖∇V‖²_{ρ,K;π}`

where `θ` bounds the (undefected) Schur matrix of the kernel regularizer constants `c`, and
`M = ∑_{m ≤ D-2} C₀ ((k+L+m)!/k!)/c_m`. Needs `0 < c_m` for `m ≤ D - 2`.
Each term is `torusKernelFluxTerm` of the defect realization `kdRealization` of the truncation of
`V_j` to the order `k + (d-1) + L`: no lift to a common top order is needed.

Generic in the stage: the consumers are the fine matrix tail and the coarse filter tails. -/

/-- The data of the defect flux: coefficients, kernels, radius and orders. -/
structure FDData (ι : Type*) [Fintype ι] (h : ι → Type) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (Γ : ι → ι → Type*) [∀ i j, Fintype (Γ i j)] where
  /-- The template of the kernels. -/
  φ₀ : Vec 2 → ℝ
  hφ : Integrable φ₀
  hd : ContDiff ℝ (⊤ : ℕ∞) φ₀
  hnonneg : ∀ z, 0 ≤ φ₀ z
  hmass : ∫ z, φ₀ z = 1
  hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall
  /-- The window, the radius, the output order, the maximal derivative order, the moments. -/
  t₀ : ℝ
  t₁ : ℝ
  ρ : ℝ
  hρ : 0 < ρ
  k : ℕ
  D : ℕ
  hD : 2 ≤ D
  L : ℕ
  /-- The kernel order, the matrix bound and the width ratio. -/
  Γk : ℝ
  hΓk : 0 ≤ Γk
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q ≤ 1
  /-- The coefficients. -/
  B : ∀ (i j : ι) (_ : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))
  hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => B i j α d p.1 p.2
  hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t)
  hB_per : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (B i j α d t)
  hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤
  /-- The kernels. -/
  Kern : ∀ i j, Γ i j → KernelSpec
  hadm : ∀ i j α, (Kern i j α).IsAdmissible Γk L
  hwpos : ∀ i j α, 0 < (Kern i j α).width
  hwq : ∀ i j α, (Kern i j α).width ≤ q * ρ

variable {ι : Type*} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]

namespace FDData

variable (P : FDData ι h Γ)

theorem mem_Icc (d : ↥(Finset.Icc 2 P.D)) : 2 ≤ d.1 ∧ d.1 ≤ P.D := Finset.mem_Icc.1 d.2

/-- The input order: `V ∈ H^{K+1}` with `k + (D-2) + L ≤ K`. -/
def OrderOK (K : ℕ) : Prop := P.k + (P.D - 2) + P.L ≤ K

theorem orderOK_term (d : ↥(Finset.Icc 2 P.D)) {K : ℕ} (hK : P.OrderOK K) :
    (P.k + (d.1 - 2 + 1)) + P.L ≤ K + 1 := by
  have := P.mem_Icc d
  unfold OrderOK at hK
  omega

/-- One term of the defect flux: the flux term of the defect realization of `V_j`. -/
def term (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 P.D)) {K : ℕ} (hK : P.OrderOK K) (t : ℝ)
    (ht : t ∈ Set.Icc P.t₀ P.t₁) (V : TorusHk (K + 1) (h j)) :
    TorusHk P.k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusKernelFluxTerm (K := P.k) (m := d.1 - 2) (r := d.1 - 1)
    (by have := P.mem_Icc d; omega) P.ρ P.hρ P.t₀ P.t₁ (P.B i j α d) (P.hB_fin i j α d) t ht
    (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
    (kdRealization P.φ₀ P.hφ (P.Kern i j α) t
      (truncateTorusHk (P.orderOK_term d hK) V))

/-- The defect flux at the component `i`. -/
def flux (i : ι) {K : ℕ} (hK : P.OrderOK K) (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁)
    (V : ∀ j, TorusHk (K + 1) (h j)) : TorusHk P.k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j, ∑ α, ∑ d, P.term i j α d hK t ht (V j)

end FDData

theorem fd_torusHk_sum_value {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (f : α → TorusHk K E) (a : JetIndex2 K) :
    ((∑ i, f i : TorusHk K E).val).ofLp a = ∑ i, ((f i).val).ofLp a := by
  change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : JetIndex2 K =>
      Lp E 2 (volume.restrict AVenhance.unitCube)) a)
      ((torusHkGraph (E := E) K).toSubmodule.subtype (∑ i, f i)) = _
  rw [map_sum]
  rw [map_sum]
  rfl

theorem fd_sum_val {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {K : ℕ} (f : α → TorusHk K E) :
    (∑ i, f i : TorusHk K E).val = ∑ i, (f i).val := by
  change (torusHkGraph (E := E) K).toSubmodule.subtype (∑ i, f i) = _
  simp only [map_sum]
  rfl

/-- The value of a finite sum of torus fields is a.e. the sum of the values. -/
theorem fd_sum_value_ae {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (f : α → TorusHk K E) (a : JetIndex2 K) :
    (∑ i, f i : TorusHk K E).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ i, (f i).val a x := by
  have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset α) (fun i => (f i).val a)
  have hv := fd_torusHk_sum_value f a
  have := Lp.ext_iff.mp hv
  filter_upwards [this, hs] with x hx hsx
  rw [hx, hsx]


namespace FDData

variable (P : FDData ι h Γ)

/-- The defect realization of `V_j` is a classical representative of `(I - S)a_j`. -/
theorem defect_classicalRep (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 P.D)) {K : ℕ}
    (hK : P.OrderOK K) (t : ℝ) (V : TorusHk (K + 1) (h j)) (a : Vec 2 → h j)
    (hV : IsClassicalRep V a (K + 1)) :
    IsClassicalRep (kdRealization P.φ₀ P.hφ (P.Kern i j α) t
        (truncateTorusHk (P.orderOK_term d hK) V))
      (fun y => a y - (P.Kern i j α).applyClassical P.φ₀ t a y) (P.k + (d.1 - 2 + 1)) := by
  have hKL := P.orderOK_term d hK
  have hrep : IsClassicalRep (truncateTorusHk hKL V) a ((P.k + (d.1 - 2 + 1)) + P.L) :=
    Construction.Preservation.FullLift.classicalRep_truncate hKL le_rfl V a
      (CycleComparison.Reconstruction.isClassicalRep_of_le hV hKL)
  exact kdRealization_isClassicalRep P.hφ P.hd P.hsupp (P.Kern i j α) t _ a hrep

/-- The jets of one term. -/
theorem term_ae (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 P.D)) {K : ℕ} (hK : P.OrderOK K)
    (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁) (V : TorusHk (K + 1) (h j)) (a : Vec 2 → h j)
    (hV : IsClassicalRep V a (K + 1)) :
    (P.term i j α d hK t ht V).val (valueIndex2 P.k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word
          (fun y => a y - (P.Kern i j α).applyClassical P.φ₀ t a y) x) := by
  have hd := P.mem_Icc d
  have hm : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hrep := P.defect_classicalRep i j α d hK t V a hV
  have hbase := torusKernelFluxTerm_base_ae (K := P.k) (m := d.1 - 2) (r := d.1 - 1) hm P.ρ P.hρ
    P.t₀ P.t₁ (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
    (P.hB_per i j α d t ht)
    (kdRealization P.φ₀ P.hφ (P.Kern i j α) t (truncateTorusHk (P.orderOK_term d hK) V))
  have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ word : DerivativeWord2 (d.1 - 1),
      (kdRealization P.φ₀ P.hφ (P.Kern i j α) t
          (truncateTorusHk (P.orderOK_term d hK) V)).toFunction.jet
        ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
      orderedDerivative word (fun y => a y - (P.Kern i j α).applyClassical P.φ₀ t a y) x := by
    refine ae_all_iff.2 fun word => ?_
    have h1 := hrep.2.2.2 (d.1 - 1) (by omega) word
    have e : torusJetOrder (kdRealization P.φ₀ P.hφ (P.Kern i j α) t
          (truncateTorusHk (P.orderOK_term d hK) V)) (d.1 - 1) word =
        (kdRealization P.φ₀ P.hφ (P.Kern i j α) t
          (truncateTorusHk (P.orderOK_term d hK) V)).toFunction.jet
          ⟨⟨d.1 - 1, by omega⟩, word⟩ := by
      funext x
      simp [torusJetOrder, show d.1 - 1 ≤ P.k + (d.1 - 2 + 1) by omega]
    rw [e] at h1
    exact h1
  have hrep0 := torusHk_toFunction_jet_ae (P.term i j α d hK t ht V) (valueIndex2 P.k)
  filter_upwards [hrep0, hbase, hall] with x hx1 hx2 hx3
  rw [← hx1]
  refine hx2.trans (congrArg (P.B i j α d t x) ?_)
  apply PiLp.ext
  intro word
  exact hx3 word

/-- The jets of the defect flux. -/
theorem flux_ae (i : ι) {K : ℕ} (hK : P.OrderOK K) (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁)
    (V : ∀ j, TorusHk (K + 1) (h j)) (a : ∀ j, Vec 2 → h j)
    (hV : ∀ j, IsClassicalRep (V j) (a j) (K + 1)) :
    (P.flux i hK t ht V).toFunction.jet (valueIndex2 P.k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ j, ∑ α, ∑ d : ↥(Finset.Icc 2 P.D),
        P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word
            (fun y => a j y - (P.Kern i j α).applyClassical P.φ₀ t (a j) y) x) := by
  have h0 := torusHk_toFunction_jet_ae (P.flux i hK t ht V) (valueIndex2 P.k)
  have h1 := fd_sum_value_ae (fun j => ∑ α, ∑ d, P.term i j α d hK t ht (V j))
    (valueIndex2 P.k)
  have h2 : ∀ j, (∑ α, ∑ d, P.term i j α d hK t ht (V j) : TorusHk P.k _).val
      (valueIndex2 P.k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ α, ∑ d, (P.term i j α d hK t ht (V j)).val (valueIndex2 P.k) x := fun j => by
    have := fd_sum_value_ae (fun α => ∑ d, P.term i j α d hK t ht (V j)) (valueIndex2 P.k)
    have h3 : ∀ α, (∑ d, P.term i j α d hK t ht (V j) : TorusHk P.k _).val
        (valueIndex2 P.k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => ∑ d, (P.term i j α d hK t ht (V j)).val (valueIndex2 P.k) x := fun α =>
      fd_sum_value_ae (fun d => P.term i j α d hK t ht (V j)) (valueIndex2 P.k)
    have h4 := ae_all_iff.2 h3
    filter_upwards [this, h4] with x hx hx4
    rw [hx]
    exact Finset.sum_congr rfl fun α _ => hx4 α
  have h5 := ae_all_iff.2 h2
  have h6 : ∀ j α d, (P.term i j α d hK t ht (V j)).val (valueIndex2 P.k)
      =ᵐ[volume.restrict AVenhance.unitCube] _ := fun j α d =>
    P.term_ae i j α d hK t ht (V j) (a j) (hV j)
  have h7 : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j α d,
      (P.term i j α d hK t ht (V j)).val (valueIndex2 P.k) x =
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word
            (fun y => a j y - (P.Kern i j α).applyClassical P.φ₀ t (a j) y) x) := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun α => ae_all_iff.2 fun d => h6 j α d
  filter_upwards [h0, h1, h5, h7] with x x0 x1 x5 x7
  rw [x0]
  change (∑ j, (∑ α, ∑ d, P.term i j α d hK t ht (V j)) : TorusHk P.k _).val (valueIndex2 P.k) x = _
  rw [x1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [x5 j]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun d _ => x7 j α d

end FDData


namespace FDData

variable (P : FDData ι h Γ)

/-- The kernel-defect constants: `c'_m = C₀ ((k+L+m)!/k!) q^{L+m}`. -/
def cdef (m : ℕ) : ℝ :=
  kdUniformMomentConst P.φ₀ P.L P.Γk * (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) *
    P.q ^ (P.L + m)

/-- The price of the defect against a regularizer constant sequence `c`:
`M = ∑_{m ≤ D-2} C₀ ((k+L+m)!/k!)/c_m`. -/
def Mconst (c : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (P.D - 1),
    kdUniformMomentConst P.φ₀ P.L P.Γk * (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) / c m

theorem c0_nonneg : 0 ≤ kdUniformMomentConst P.φ₀ P.L P.Γk :=
  kdUniformMomentConst_nonneg P.φ₀ P.L P.hΓk

theorem cdef_nonneg (m : ℕ) : 0 ≤ P.cdef m := by
  unfold cdef
  have := P.c0_nonneg
  have := P.hq0
  positivity

theorem Mconst_nonneg {c : ℕ → ℝ} (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) : 0 ≤ P.Mconst c := by
  unfold Mconst
  refine Finset.sum_nonneg fun m hm => ?_
  have := P.c0_nonneg
  have h2 : 0 < c m := hc m (by have := Finset.mem_range.1 hm; omega)
  positivity

theorem cdef_le {c : ℕ → ℝ} (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) {m : ℕ} (hm : m + 2 ≤ P.D) :
    P.cdef m ≤ P.q ^ P.L * P.Mconst c * c m := by
  have h2 : 0 < c m := hc m hm
  have h0 := P.c0_nonneg
  set a := kdUniformMomentConst P.φ₀ P.L P.Γk * (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial)
    with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hM : a / c m ≤ P.Mconst c := by
    unfold Mconst
    refine Finset.single_le_sum (f := fun m => kdUniformMomentConst P.φ₀ P.L P.Γk *
      (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) / c m) (fun m hm => ?_)
      (Finset.mem_range.2 (by omega))
    have h3 : 0 < c m := hc m (by have := Finset.mem_range.1 hm; omega)
    positivity
  have hM' : a ≤ P.Mconst c * c m := by
    have := (div_le_iff₀ h2).1 hM
    exact this
  have hq : P.q ^ (P.L + m) ≤ P.q ^ P.L :=
    pow_le_pow_of_le_one P.hq0 P.hq1 (by omega)
  unfold cdef
  rw [← ha]
  calc a * P.q ^ (P.L + m) ≤ a * P.q ^ P.L := mul_le_mul_of_nonneg_left hq ha0
    _ ≤ (P.Mconst c * c m) * P.q ^ P.L := mul_le_mul_of_nonneg_right hM' (by
        have := P.hq0; positivity)
    _ = _ := by ring

end FDData


namespace FDData

variable (P : FDData ι h Γ)

/-- The Schur matrix of the defect constants is bounded by `q^L M` times the given one. -/
theorem schur_scale [∀ j, Nontrivial (h j)] (π : ι → ℝ) (ν : ℝ) (hν : 0 < ν) (c : ℕ → ℝ)
    (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) (θ : ℝ)
    (hschur : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ c (fun i j α => (P.Kern i j α).width) (fun _ j _ => ContinuousLinearMap.id ℝ (h j))
      P.B)) :
    SchurBound (P.q ^ P.L * P.Mconst c * θ)
      (kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ P.cdef (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B) := by
  set s0 := P.q ^ P.L * P.Mconst c with hs0
  have hs0nn : 0 ≤ s0 := mul_nonneg (pow_nonneg P.hq0 _) (P.Mconst_nonneg hc)
  have hle : ∀ i j, kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ P.cdef (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B i j ≤
      s0 * kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ c (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B i j := by
    intro i j
    unfold kernelSchurMatrix
    have key : ∀ (α : Γ i j) (d : ↥(Finset.Icc 2 P.D)),
        ((coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal * P.cdef (d.1 - 2)) /
          (ν * (P.Kern i j α).width ^ (d.1 - 2)) ≤
        s0 * (((coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal * c (d.1 - 2)) /
          (ν * (P.Kern i j α).width ^ (d.1 - 2))) := by
      intro α d
      have hd := P.mem_Icc d
      have hden : 0 < ν * (P.Kern i j α).width ^ (d.1 - 2) :=
        mul_pos hν (pow_pos (P.hwpos i j α) _)
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hden.le
      have h1 := mul_le_mul_of_nonneg_left (P.cdef_le hc (m := d.1 - 2) (by omega))
        (ENNReal.toReal_nonneg (a := coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)))
      calc _ ≤ _ := h1
        _ = _ := by ring
    have hsum : ∑ α : Γ i j, ‖(ContinuousLinearMap.id ℝ (h j))‖ * ∑ d : ↥(Finset.Icc 2 P.D),
          ((coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal * P.cdef (d.1 - 2)) /
            (ν * (P.Kern i j α).width ^ (d.1 - 2)) ≤
        s0 * ∑ α : Γ i j, ‖(ContinuousLinearMap.id ℝ (h j))‖ * ∑ d : ↥(Finset.Icc 2 P.D),
          ((coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal * c (d.1 - 2)) /
            (ν * (P.Kern i j α).width ^ (d.1 - 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ => ?_
      calc _ ≤ ‖(ContinuousLinearMap.id ℝ (h j))‖ * ∑ d : ↥(Finset.Icc 2 P.D),
            s0 * (((coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal * c (d.1 - 2)) /
              (ν * (P.Kern i j α).width ^ (d.1 - 2))) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d _ => key α d)
              (norm_nonneg (ContinuousLinearMap.id ℝ (h j)))
        _ = _ := by rw [← Finset.mul_sum, mul_left_comm]
    calc _ ≤ Real.sqrt (π j / π i) * (s0 * _) :=
          mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
      _ = _ := by ring
  refine ⟨fun i => ?_, fun j => ?_⟩
  · calc _ ≤ ∑ j, s0 * kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
          P.t₁ c (fun i j α => (P.Kern i j α).width)
          (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B i j :=
          Finset.sum_le_sum fun j _ => hle i j
      _ = s0 * ∑ j, _ := by rw [Finset.mul_sum]
      _ ≤ s0 * θ := mul_le_mul_of_nonneg_left (hschur.1 i) hs0nn
      _ = _ := by rw [hs0]
  · calc _ ≤ ∑ i, s0 * kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
          P.t₁ c (fun i j α => (P.Kern i j α).width)
          (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B i j :=
          Finset.sum_le_sum fun i _ => hle i j
      _ = s0 * ∑ i, _ := by rw [Finset.mul_sum]
      _ ≤ s0 * θ := mul_le_mul_of_nonneg_left (hschur.2 j) hs0nn
      _ = _ := by rw [hs0]

end FDData


namespace FDData

variable (P : FDData ι h Γ)

/-- The factorial norm of one term. -/
theorem term_root_le [∀ j, Nontrivial (h j)] (i j : ι) (α : Γ i j)
    (d : ↥(Finset.Icc 2 P.D)) {K : ℕ} (hK : P.OrderOK K) (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁)
    (V : TorusHk (K + 1) (h j)) (a : Vec 2 → h j) (hV : IsClassicalRep V a (K + 1)) :
    Real.sqrt (factorialNormSq P.ρ (P.term i j α d hK t ht V).val) ≤
      (coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d)).toReal *
        (P.cdef (d.1 - 2) / (P.Kern i j α).width ^ (d.1 - 2)) *
          ‖(ContinuousLinearMap.id ℝ (h j))‖ * Real.sqrt (gradFactorialNormSq P.ρ V.val) := by
  have hd := P.mem_Icc d
  have hOK : P.k + (d.1 - 2) + P.L ≤ K := by unfold OrderOK at hK; omega
  have hadm := P.hadm i j α
  have h1 := (hadm.2.2.1 t).1
  have h2 := (hadm.2.2.1 t).2.1
  set r := (P.Kern i j α).width with hr
  have hr0 : 0 < r := P.hwpos i j α
  have hrq : r / P.ρ ≤ P.q := by
    rw [div_le_iff₀ P.hρ]; exact P.hwq i j α
  set m := d.1 - 2 with hm
  have hbound := fd_derivFactorialNormSq_le_uniform P.hφ P.hd P.hnonneg P.hmass P.hsupp P.L P.Γk
    (P.Kern i j α) t P.ρ hadm.2.2.2
    hr0 P.hρ h1 h2 P.k m K hOK V a hV
  set γ := kdUniformMomentConst P.φ₀ P.L P.Γk * (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) *
    (r / P.ρ) ^ P.L * (P.ρ⁻¹) ^ m with hγ
  have hγ0 : 0 ≤ γ := by
    have := P.c0_nonneg
    have : 0 ≤ r / P.ρ := div_nonneg hr0.le P.hρ.le
    have := P.hρ
    rw [hγ]; positivity
  have hgn : 0 ≤ gradFactorialNormSq P.ρ V.val := by
    unfold gradFactorialNormSq
    refine Finset.sum_nonneg fun q _ => mul_nonneg (factorialWeight_nonneg _ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hrd : d.1 - 1 = m + 1 := by omega
  have hfl := torusKernelFluxTerm_factorialNorm_le (K := P.k) (m := m) (r := d.1 - 1) hrd P.ρ P.hρ
    P.t₀ P.t₁ (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
    (P.hB_per i j α d t ht)
    (kdRealization P.φ₀ P.hφ (P.Kern i j α) t (truncateTorusHk (P.orderOK_term d hK) V))
    γ hγ0 1 zero_le_one _ hgn (by rw [one_pow, mul_one]; exact hbound)
  have hid : ‖(ContinuousLinearMap.id ℝ (h j))‖ = 1 := ContinuousLinearMap.norm_id
  rw [hid, mul_one]
  have hσ := ENNReal.toReal_nonneg (a := coefficientSeminorm P.ρ P.k P.t₀ P.t₁ (P.B i j α d))
  have hγle : γ ≤ P.cdef m / r ^ m := by
    unfold cdef
    rw [le_div_iff₀ (pow_pos hr0 m)]
    have hs0 : 0 ≤ r / P.ρ := div_nonneg hr0.le P.hρ.le
    have e : (P.ρ⁻¹) ^ m * r ^ m = (r / P.ρ) ^ m := by
      rw [← mul_pow, div_eq_mul_inv, mul_comm]
    have := P.c0_nonneg
    calc γ * r ^ m = kdUniformMomentConst P.φ₀ P.L P.Γk *
          (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) *
          ((r / P.ρ) ^ P.L * (P.ρ⁻¹ ^ m * r ^ m)) := by rw [hγ]; ring
      _ = kdUniformMomentConst P.φ₀ P.L P.Γk *
          (((P.k + (P.L + m)).factorial : ℝ) / P.k.factorial) * (r / P.ρ) ^ (P.L + m) := by
          rw [e, pow_add]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hrq _) (by positivity)
  calc _ ≤ _ := hfl
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγle hσ) (Real.sqrt_nonneg _)

end FDData


namespace FDData

variable (P : FDData ι h Γ)

theorem flux_val_eq (i : ι) {K : ℕ} (hK : P.OrderOK K) (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁)
    (V : ∀ j, TorusHk (K + 1) (h j)) :
    (P.flux i hK t ht V).val =
      ∑ j, ∑ α, ∑ d : ↥(Finset.Icc 2 P.D), (P.term i j α d hK t ht (V j)).val := by
  simp only [FDData.flux, fd_sum_val]

/-- **The defect version of `kernel_flux_bound_torus` at one time** (generic). -/
theorem flux_massNormSq_le [∀ j, Nontrivial (h j)] (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν : ℝ)
    (hν : 0 < ν) (c : ℕ → ℝ) (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) (θ : ℝ)
    (hschur : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ c (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B))
    {K : ℕ} (hK : P.OrderOK K) (t : ℝ) (ht : t ∈ Set.Icc P.t₀ P.t₁)
    (V : ∀ j, TorusHk (K + 1) (h j)) (a : ∀ j, Vec 2 → h j)
    (hV : ∀ j, IsClassicalRep (V j) (a j) (K + 1)) :
    massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => P.k) P.ρ π
        (fun i => (P.flux i hK t ht V).val) ≤
      (ν * (P.q ^ P.L * P.Mconst c * θ)) ^ 2 *
        massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j).val) := by
  have hsch := P.schur_scale π ν hν c hc θ hschur
  have := AVRegularity.WeakEntryProofs.pfc_flux_mass_schur (E := h) (G := fun _ j _ => h j) (μ := volume.restrict AVenhance.unitCube)
    P.ρ ν (P.q ^ P.L * P.Mconst c * θ) hν P.k P.D P.t₀ P.t₁ π hπ P.B
    (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.cdef (fun i j α => (P.Kern i j α).width)
    (fun i j α => P.hwpos i j α)
    (fun i j α m _ => P.cdef_nonneg m)
    (fun i => (P.flux i hK t ht V).val)
    (fun j => gradFactorialNormSq P.ρ (V j).val)
    (fun j => by
      unfold gradFactorialNormSq
      exact Finset.sum_nonneg fun q _ => mul_nonneg (factorialWeight_nonneg _ _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (fun i j α d => (P.term i j α d hK t ht (V j)).val)
    (fun i => P.flux_val_eq i hK t ht V)
    (fun i j α d => P.term_root_le i j α d hK t ht (V j) (a j) (hV j)) hsch
  simpa [massGradNormSq] using this

end FDData

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The defect flux in `L²(I)` (generic)

The trajectory `t ↦ flux(t, V(t))` (clamped to the window outside it) of `FDData` is
`L²(I; H^k)` when `|∇V|²_{ρ,K;π}` is integrable, and
`(ν⁻¹ ∫_I ‖F‖²_{ρ,k;π})^{1/2} ≤ q^L M θ (ν ∫_I |∇V|²_{ρ,K;π})^{1/2}`
(`FDData.timeBound`). Measurability in time is that of `kdRealization`
(`kdRealization_stronglyMeasurable`) and of the flux term
(`torusKernelFluxTerm_time_stronglyMeasurable`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]

namespace FDData

variable (P : FDData ι h Γ)

/-- The clamped trajectory of the flux. -/
def fluxT (ht01 : P.t₀ ≤ P.t₁) (i : ι) {K : ℕ} (hK : P.OrderOK K)
    (V : ∀ j, ℝ → TorusHk (K + 1) (h j)) (t : ℝ) : TorusHk P.k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.flux i hK (Set.projIcc P.t₀ P.t₁ ht01 t) (Set.projIcc P.t₀ P.t₁ ht01 t).property
    (fun j => V j (Set.projIcc P.t₀ P.t₁ ht01 t))

theorem fluxT_eq (ht01 : P.t₀ ≤ P.t₁) (i : ι) {K : ℕ} (hK : P.OrderOK K)
    (V : ∀ j, ℝ → TorusHk (K + 1) (h j)) {t : ℝ} (ht : t ∈ Set.Icc P.t₀ P.t₁) :
    P.fluxT ht01 i hK V t = P.flux i hK t ht (fun j => V j t) := by
  unfold fluxT
  have : Set.projIcc P.t₀ P.t₁ ht01 t = t := by
    simp [Set.projIcc_of_mem _ ht]
  simp only [this]

theorem term_aesm (ht01 : P.t₀ ≤ P.t₁) (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 P.D)) {K : ℕ}
    (hK : P.OrderOK K) (V : ℝ → TorusHk (K + 1) (h j))
    (hV : AEStronglyMeasurable V (volume.restrict (Set.Icc P.t₀ P.t₁))) :
    AEStronglyMeasurable (fun t => P.term i j α d hK (Set.projIcc P.t₀ P.t₁ ht01 t)
      (Set.projIcc P.t₀ P.t₁ ht01 t).property (V (Set.projIcc P.t₀ P.t₁ ht01 t)))
      (volume.restrict (Set.Icc P.t₀ P.t₁)) := by
  have hd := P.mem_Icc d
  set W := hV.mk V with hW
  have hWm : StronglyMeasurable W := hV.stronglyMeasurable_mk
  have hWae : V =ᵐ[volume.restrict (Set.Icc P.t₀ P.t₁)] W := hV.ae_eq_mk
  have hKL := P.orderOK_term d hK
  have hm : Measurable (fun t : Set.Icc P.t₀ P.t₁ => (t : ℝ)) := measurable_subtype_coe
  have hu : StronglyMeasurable (fun t : Set.Icc P.t₀ P.t₁ =>
      truncateTorusHk hKL (W t)) :=
    (truncateTorusHk hKL).continuous.comp_stronglyMeasurable (hWm.comp_measurable hm)
  have hY : StronglyMeasurable (fun t : Set.Icc P.t₀ P.t₁ =>
      kdRealization P.φ₀ P.hφ (P.Kern i j α) (t : ℝ) (truncateTorusHk hKL (W t))) := by
    have := kdRealization_stronglyMeasurable P.hφ P.hd P.hsupp (P.Kern i j α)
      (P.hadm i j α).1 (P.hadm i j α).2.1
      (u := fun t : ℝ => truncateTorusHk hKL (W t))
      ((truncateTorusHk hKL).continuous.comp_stronglyMeasurable hWm)
    exact this.comp_measurable hm
  have hT := torusKernelFluxTerm_time_stronglyMeasurable (K := P.k) (m := d.1 - 2) (r := d.1 - 1)
    (by omega) P.ρ P.hρ P.t₀ P.t₁ (P.B i j α d) (P.hB_fin i j α d) (P.hB_meas i j α d)
    (P.hB_smooth i j α d) (P.hB_per i j α d) _ hY
  have hT' : StronglyMeasurable (fun t : ℝ => P.term i j α d hK (Set.projIcc P.t₀ P.t₁ ht01 t)
      (Set.projIcc P.t₀ P.t₁ ht01 t).property (W (Set.projIcc P.t₀ P.t₁ ht01 t))) :=
    hT.comp_measurable (continuous_projIcc (h := ht01)).measurable
  refine hT'.aestronglyMeasurable.congr ?_
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Icc P.t₀ P.t₁)), t ∈ Set.Icc P.t₀ P.t₁ :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem, hWae] with t ht hVt
  have e : Set.projIcc P.t₀ P.t₁ ht01 t = t := by simp [Set.projIcc_of_mem _ ht]
  simp only [e, hVt]

theorem fluxT_aesm (ht01 : P.t₀ ≤ P.t₁) (i : ι) {K : ℕ} (hK : P.OrderOK K)
    (V : ∀ j, ℝ → TorusHk (K + 1) (h j))
    (hV : ∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc P.t₀ P.t₁))) :
    AEStronglyMeasurable (P.fluxT ht01 i hK V) (volume.restrict (Set.Icc P.t₀ P.t₁)) := by
  unfold fluxT flux
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun α _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun d _ => P.term_aesm ht01 i j α d hK (V j) (hV j)

end FDData


namespace FDData

variable (P : FDData ι h Γ)

theorem massNormSq_nonneg' (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ℕ}
    (A : ∀ i, TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) :
    0 ≤ massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => K) P.ρ π
      (fun i => (A i).val) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le) (factorialNormSq_nonneg _ _)

theorem factorialNormSq_le_mass (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ℕ}
    (A : ∀ i, TorusHk K (PiLp 2 (fun _ : Fin 2 => h i))) (i : ι) :
    factorialNormSq P.ρ (A i).val ≤ π i *
      massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => K) P.ρ π
        (fun i => (A i).val) := by
  have hle : (π i)⁻¹ * factorialNormSq P.ρ (A i).val ≤
      massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => K) P.ρ π
        (fun i => (A i).val) :=
    Finset.single_le_sum (f := fun i => (π i)⁻¹ * factorialNormSq P.ρ (A i).val)
      (fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le) (factorialNormSq_nonneg _ _))
      (Finset.mem_univ i)
  have := mul_le_mul_of_nonneg_left hle (hπ i).le
  rwa [← mul_assoc, mul_inv_cancel₀ (hπ i).ne', one_mul] at this

/-- **The defect flux in `L²(I)`** (generic): realization, `L²` in time and the bound. -/
theorem timeBound [∀ j, Nontrivial (h j)] (ht01 : P.t₀ ≤ P.t₁) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (ν : ℝ) (hν : 0 < ν) (c : ℕ → ℝ)
    (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) (θ : ℝ) (hθ : 0 ≤ θ)
    (hschur : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ c (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) P.B))
    {K : ℕ} (hK : P.OrderOK K) (V : ∀ j, ℝ → TorusHk (K + 1) (h j))
    (a : ∀ j, ℝ → Vec 2 → h j)
    (hcl : ∀ j, ∀ t ∈ Set.Icc P.t₀ P.t₁, IsClassicalRep (V j t) (a j t) (K + 1))
    (hmeas : ∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc P.t₀ P.t₁)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := fun _ => K) P.ρ π
      (fun j => (V j t).val)) (volume.restrict (Set.Icc P.t₀ P.t₁))) :
    ∃ Fk : ∀ i, ℝ → TorusHk P.k (PiLp 2 (fun _ : Fin 2 => h i)),
      (∀ i, ∀ t ∈ Set.Icc P.t₀ P.t₁,
        (Fk i t).toFunction.jet (valueIndex2 P.k) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => ∑ j, ∑ α, ∑ d : ↥(Finset.Icc 2 P.D),
            P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              orderedDerivative word
                (fun y => a j t y - (P.Kern i j α).applyClassical P.φ₀ t (a j t) y) x)) ∧
      (∀ i, MemLp (Fk i) 2 (volume.restrict (Set.Icc P.t₀ P.t₁))) ∧
      Real.sqrt (ν⁻¹ * ∫ s in Set.Icc P.t₀ P.t₁,
          massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => P.k) P.ρ π
            (fun i => (Fk i s).val)) ≤
        P.q ^ P.L * P.Mconst c * θ * Real.sqrt (ν * ∫ s in Set.Icc P.t₀ P.t₁,
          massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j s).val)) := by
  set I := Set.Icc P.t₀ P.t₁ with hI
  set Fk : ∀ i, ℝ → TorusHk P.k (PiLp 2 (fun _ : Fin 2 => h i)) :=
    fun i => P.fluxT ht01 i hK V with hFk
  set s0 := P.q ^ P.L * P.Mconst c * θ with hs0
  have hpt : ∀ t ∈ I, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => P.k)
      P.ρ π (fun i => (Fk i t).val) ≤ (ν * s0) ^ 2 *
        massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j t).val) := by
    intro t ht
    have := P.flux_massNormSq_le π hπ ν hν c hc θ hschur hK t ht (fun j => V j t)
      (fun j => a j t) (fun j => hcl j t ht)
    simpa only [hFk, P.fluxT_eq ht01 _ hK V ht] using this
  have hG0 : ∀ t, 0 ≤ massGradNormSq (E := h) (K := fun _ => K) P.ρ π
      (fun j => (V j t).val) := fun t => Finset.sum_nonneg fun j _ => mul_nonneg
    (inv_nonneg.2 (hπ j).le) (by
        unfold gradFactorialNormSq
        exact Finset.sum_nonneg fun q _ => mul_nonneg (factorialWeight_nonneg _ _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hwmin := factorialWeightMin_pos (K := P.k) P.ρ P.hρ
  refine ⟨Fk, ?_, ?_, ?_⟩
  · intro i t ht
    have := P.flux_ae i hK t ht (fun j => V j t) (fun j => a j t) (fun j => hcl j t ht)
    simpa only [hFk, P.fluxT_eq ht01 _ hK V ht] using this
  · intro i
    have hae : AEStronglyMeasurable (Fk i) (volume.restrict I) := P.fluxT_aesm ht01 i hK V hmeas
    rw [memLp_two_iff_integrable_sq_norm hae]
    have hdom : Integrable (fun t => (π i / factorialWeightMin P.ρ P.k) * ((ν * s0) ^ 2 *
        massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j t).val)))
        (volume.restrict I) := (hint.const_mul _).const_mul _
    refine hdom.mono' (hae.norm.pow 2) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc (a := P.t₀) (b := P.t₁))] with t ht
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := KernelEnergyPlane.jetNorm_le_factorialRoot (μ := volume.restrict AVenhance.unitCube)
      P.ρ P.hρ (Fk i t).val
    have h2 : factorialNormSq P.ρ (Fk i t).val ≤ π i * massNormSq (E := fun i =>
        PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => P.k) P.ρ π (fun i => (Fk i t).val) :=
      P.factorialNormSq_le_mass π hπ (fun i => Fk i t) i
    have h3 := mul_le_mul_of_nonneg_left (hpt t ht) (hπ i).le
    have h4 : ‖Fk i t‖ ^ 2 ≤ factorialNormSq P.ρ (Fk i t).val / factorialWeightMin P.ρ P.k := by
      have h5 : ‖Fk i t‖ = ‖(Fk i t).val‖ := rfl
      rw [h5]
      have h6 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [div_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _), Real.sq_sqrt hwmin.le] at h6
    calc ‖Fk i t‖ ^ 2 ≤ _ := h4
      _ ≤ (π i * ((ν * s0) ^ 2 * massGradNormSq (E := h) (K := fun _ => K) P.ρ π
            (fun j => (V j t).val))) / factorialWeightMin P.ρ P.k :=
          div_le_div_of_nonneg_right (h2.trans h3) hwmin.le
      _ = _ := by ring
  · have hint2 : Integrable (fun t => (ν * s0) ^ 2 *
        massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j t).val))
        (volume.restrict I) := hint.const_mul _
    have hmono : ∫ s in I, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
        (K := fun _ => P.k) P.ρ π (fun i => (Fk i s).val) ≤
        (ν * s0) ^ 2 * ∫ s in I, massGradNormSq (E := h) (K := fun _ => K) P.ρ π
          (fun j => (V j s).val) := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
        P.massNormSq_nonneg' π hπ (fun i => Fk i t)) hint2 ?_
      filter_upwards [ae_restrict_mem (measurableSet_Icc (a := P.t₀) (b := P.t₁))] with t ht
      exact hpt t ht
    have hG : 0 ≤ ∫ s in I, massGradNormSq (E := h) (K := fun _ => K) P.ρ π
        (fun j => (V j s).val) := integral_nonneg fun t => hG0 t
    have hs0nn : 0 ≤ s0 := mul_nonneg (mul_nonneg (pow_nonneg P.hq0 _)
      (P.Mconst_nonneg hc)) hθ
    calc _ ≤ Real.sqrt (ν⁻¹ * ((ν * s0) ^ 2 * ∫ s in I, massGradNormSq (E := h)
            (K := fun _ => K) P.ρ π (fun j => (V j s).val))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hν.le))
      _ = Real.sqrt (s0 ^ 2 * (ν * ∫ s in I, massGradNormSq (E := h)
            (K := fun _ => K) P.ρ π (fun j => (V j s).val))) := by
          congr 1; field_simp
      _ = _ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs0nn]

end FDData

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
