-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentWeakMeanArrayProduction
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Construction.EntryScales.TerminalCore
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
/-! A common positive mean budget covers both source kinds without changing their produced fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ level p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

def IndependentWeakMeanArrayProduction.enlargeBudget
    (M : IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n θ B native)
    (hθ : 0 ≤ θ) (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i)
    (B' : ℝ) (hBB' : B ≤ B') :
    IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n θ B' native where
  field := M.field
  reserve := M.reserve
  budget c d word k hk := (M.budget c d word k hk).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBB'
      (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _))
        (Real.rpow_pos_of_pos (hε _) _).le)) hθ)
  phase := M.phase
  geometry := M.geometry
  native_copy := M.native_copy

end AVRegularity.EntryWeakProofs
end
end

section
/-! Equal stage levels transport actual mean arrays without changing the flux readout. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}

def IndependentWeakMeanArrayProduction.relevelFlux
    (flux : FamFluxOp)
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase cap H n θ B
      (fun p A d word t => fluxCoeff (flux p.1 t A.1) d word 0))
    (he : fine = level) :
    IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n θ B
      (fun p A d word t => fluxCoeff (flux p.1 t A.1) d word 0) := by
  subst level
  exact M

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal equality of native readouts changes no produced field or reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ level p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

def IndependentWeakMeanArrayProduction.replaceNative
    (M : IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n θ B native)
    (other : ∀ p : OddSlot, StageCtx D bw j₀ level p → ∀ d,
      DerivativeWord2 (d - 1) → ℝ → Vec 2)
    (he : ∀ p A d word t, native p A d word t = other p A d word t) :
    IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n θ B other where
  field := M.field
  reserve := M.reserve
  budget := M.budget
  phase := M.phase
  geometry := M.geometry
  native_copy c d word hd hdn t ht z := (M.native_copy c d word hd hdn t ht z).trans (he _ _ _ _ _)

end AVRegularity.EntryWeakProofs
end
end

section
/-! A produced stage gives actual cell-clock incoming fields with the original stored witnesses. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap H : ℕ} {B : ℝ}
  {G : GenStage D hr Dm bw j₀}

def IndependentWeakStageFluxProduction.incomingField
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2 :=
  fun t z Y => (D.kap G.level * D.eps G.level ^ (d - 2))⁻¹ •
    S.field c v u γ d word (D.cellScaleSq G.level * t) z Y

theorem IndependentWeakStageFluxProduction.incomingField_reserve
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : D.term ≤ G.level) (hB : 0 ≤ B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (hd : 2 ≤ d) (hdn : d ≤ (G.fam.identity v u γ).maxOrder) :
    ∃ Q : IndependentParameterSourceReserve H (S.incomingField c v u γ d word),
      ∀ n ≤ H, Q.budget n ≤ (G.fam.identity v u γ).record.size * B := by
  let Q := (S.reserve c v u γ d word hd hdn).timeReparam
    (fun t => D.cellScaleSq G.level * t) (measurable_const.mul measurable_id)
  have hQ : ∀ n ≤ H, Q.budget n ≤ (G.fam.identity v u γ).record.size *
      (D.κ D.term * D.eps (G.level + 1) ^ ((G.fam.identity v u γ).maxOrder - 2) *
        D.eps G.level ^ ((d : ℝ) - ((G.fam.identity v u γ).maxOrder : ℝ))) * B := by
    intro n hn
    exact (S.budget c v u γ d word hd hdn n hn).trans_eq (by ring)
  let R := actualWeakIncomingSourceReserve H D hq hΛ hζ hband
    G.level (G.level + 1) hm (Nat.le_succ _)
    (G.fam.identity v u γ).maxOrder d (hd.trans hdn) hd
    (fun t z Y => S.field c v u γ d word (D.cellScaleSq G.level * t) z Y) Q
    (G.fam.identity v u γ).record.size B (G.fam.identity v u γ).record.size_nonneg hB hQ
  exact ⟨R, fun _ _ => le_refl _⟩

theorem IndependentWeakStageFluxProduction.incomingField_translation
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (δ : Vec (2 + 4 * c.chain.1.children.length))
    (hδ : δ ∈ independentFreshPhaseTranslations c.chain.1.children.length) :
    IndependentSourceTranslationInvariant δ (S.incomingField c v u γ d word) := by
  intro t z Y
  unfold incomingField
  rw [S.phase c v u γ d word δ hδ]

theorem IndependentWeakStageFluxProduction.incomingField_native_copy
    (S : IndependentWeakStageFluxProduction G minBase cap H B)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (hd : 2 ≤ d) (hdn : d ≤ (G.fam.identity v u γ).maxOrder)
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
      j₀ G.level c.slot.1) (t : ℝ) (z : Vec 2) :
    S.incomingField c v u γ d word t z Y =
      G.fam.flux c.slot (c.atParameter Y hY)
        v u γ d word (D.cellScaleSq G.level * t)
        (independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) z := by
  unfold incomingField
  rw [S.native_copy c v u γ d word hd hdn Y hY]
  unfold ChartedFamily.dimFlux ChartedFamily.slowFlux
  have hden : D.kap G.level * D.eps G.level ^ (d - 2) ≠ 0 :=
    mul_ne_zero (weakData_kap_pos D hΛ hζ hband G.level).ne'
      (pow_ne_zero (d - 2) (show D.eps G.level ≠ 0 from (Construction.Stream.ocEpsilon_pos hΛ).ne'))
  rw [inv_smul_smul₀ (show D.eps (G.level - 1) ≠ 0 from (Construction.Stream.ocEpsilon_pos hΛ).ne'),
    inv_smul_smul₀ hden]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Active cutoffs supply measurable physical windows strictly inside the original lift interval. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

def weakStageCutoffWindow (D : OCData) (level : ℕ) (slot : ℤ) : Set ℝ :=
  {t | ocCutoff D.α D.q D.Λ level slot t ≠ 0}

theorem weakStageCutoffWindow_isOpen (D : OCData) (hΛ : 1 ≤ D.Λ) (level : ℕ) (slot : ℤ) :
    IsOpen (weakStageCutoffWindow D level slot) := by
  change IsOpen ((fun t => ocCutoff D.α D.q D.Λ level slot t) ⁻¹' ({0} : Set ℝ))ᶜ
  exact (isClosed_singleton.preimage (CycleReference.ocCutoff_contDiff hΛ slot).continuous).isOpen_compl

theorem weakStageCutoffWindow_measurable (D : OCData) (hΛ : 1 ≤ D.Λ) (level : ℕ) (slot : ℤ) :
    MeasurableSet (weakStageCutoffWindow D level slot) :=
  (weakStageCutoffWindow_isOpen D hΛ level slot).measurableSet

theorem weakStageCutoffWindow_clock (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (level : ℕ) (slot : ℤ) (t : ℝ) (ht : t ∈ weakStageCutoffWindow D level slot) :
    (D.cellScaleSq level)⁻¹ * t ∈ weakStageMeanClockWindow D level slot := by
  have hd := abs_lt.mp (CycleReference.cutoff_nonzero_distance hΛ slot t ht)
  have hτ : 0 < ocTau D.α D.q D.Λ level := Construction.Stream.ocTau_pos hΛ
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband level
  rw [inv_mul_eq_div]
  constructor
  · apply div_le_div_of_nonneg_right ?_ hc.le
    change ((slot : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ level ≤ t
    linarith only [hd.1, hτ]
  · apply div_le_div_of_nonneg_right ?_ hc.le
    change t ≤ ((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level
    linarith only [hd.2, hτ]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Recentered native charts supply exact local models at every physical slow point. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem IndependentWeakStageFluxProduction.native_local_model
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (c : WeakStageProductionContext D bw j₀ G'.level minBase cap)
    (hc : c.chain.1.children = []) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u)
    (d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ (G'.fam.identity v u γ).maxOrder)
    (word : DerivativeWord2 (d - 1)) (X₀ X : Vec 2) (hX : ‖X - X₀‖ < 1 / 8)
    (t : ℝ) (z : Vec 2) :
    let c' := c.recenterEmpty hc (D.eps (G'.level - 1) • X₀)
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
      c.slot c.chain v u γ d word t (D.eps (G'.level - 1) • X) z =
    S.field c' v u γ d word t z
      (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) (X - X₀)
        (independentFreshCoarseChainPacking D c'.chain.1)) := by
  let c' := c.recenterEmpty hc (D.eps (G'.level - 1) • X₀)
  let Y := independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) (X - X₀)
    (independentFreshCoarseChainPacking D c'.chain.1)
  have hY : Y ∈ actualIndependentCoarseProductionCarrier D c'.chain.1 bw (D.eps (G'.level - 1))
      j₀ G'.level c'.slot.1 := actualIndependentCoarseProductionCarrier_empty_native D hq hΛ
    c'.chain.1 (c.recenterEmpty_children hc _) bw _ hbw j₀ G'.level c'.slot.1 c'.chain.2 (X - X₀) hX
  have hat : c'.atParameter Y hY = c'.chain := by
    apply Subtype.ext
    change actualIndependentCoarseParameterChain D c'.chain.1
      (independentStoredParameterProjection (4 * c'.chain.1.children.length) Y) = c'.chain.1
    rw [independentIntrinsicParameterPacking_stored]
    exact actualIndependentCoarseParameterChain_native D (by omega) c'.chain.1 c'.chain.2.2.2.1
  have hcopy := S.native_copy c' v u γ d word hd hdn Y hY t z
  rw [hat] at hcopy
  have hslow : independentIntrinsicSlowProjection (4 * c'.chain.1.children.length) Y = X - X₀ :=
    independentIntrinsicParameterPacking_slow _ _ _
  rw [hslow] at hcopy
  have hrec := weakPassage_dimFlux_recenter (by omega) hζ hband P Mn rW Din hp ht v u γ c.slot
    c.chain (D.eps (G'.level - 1) • X₀) c'.chain.2 d hd word t
    (D.eps (G'.level - 1) • (X - X₀)) z
  have he : D.eps (G'.level - 1) • X₀ + D.eps (G'.level - 1) • (X - X₀) =
      D.eps (G'.level - 1) • X := by rw [← smul_add]; congr 1; abel
  rw [he] at hrec
  exact hrec.trans hcopy.symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native zero-child coefficients have global genuine joint reserves by exact recentered local models. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem independentIntrinsicParameterPacking_shift (d : ℕ) (P : Vec d) (X X₀ : Vec 2) :
    independentIntrinsicSlowEmbedding d X +
      (independentIntrinsicParameterPacking d 0 P - independentIntrinsicSlowEmbedding d X₀) =
    independentIntrinsicParameterPacking d (X - X₀) P := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Pi.add_apply, Pi.sub_apply, independentIntrinsicSlowEmbedding,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, independentIntrinsicParameterPacking,
      Fin.addCases_left, Pi.zero_apply]
    ring
  · simp only [Pi.add_apply, Pi.sub_apply, independentIntrinsicSlowEmbedding,
      ContinuousLinearMap.pi_apply, independentIntrinsicParameterPacking,
      Fin.addCases_right, zero_apply, sub_zero, zero_add]

variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem IndependentWeakStageFluxProduction.native_joint_reserve
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (c : WeakStageProductionContext D bw j₀ G'.level minBase cap)
    (hc : c.chain.1.children = []) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u)
    (d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ (G'.fam.identity v u γ).maxOrder)
    (word : DerivativeWord2 (d - 1)) :
    ∃ Q : JointSourceReserve H (fun t z X =>
      G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        c.slot c.chain v u γ d word t (D.eps (G'.level - 1) • X) z),
      ∀ k ≤ H, Q.budget k ≤ (G'.fam.identity v u γ).record.size *
        (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
          D.eps G'.level ^ ((d : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ)) * B) := by
  let ctx X₀ := c.recenterEmpty hc (D.eps (G'.level - 1) • X₀)
  let width X₀ := 4 * (ctx X₀).chain.1.children.length
  let packing X₀ := independentFreshCoarseChainPacking D (ctx X₀).chain.1
  let g X₀ t z X := S.field (ctx X₀) v u γ d word t z
    (independentIntrinsicSlowEmbedding (width X₀) X +
      (independentIntrinsicParameterPacking (width X₀) 0 (packing X₀) -
        independentIntrinsicSlowEmbedding (width X₀) X₀))
  let Q X₀ : JointSourceReserve H (g X₀) :=
    (S.reserve (ctx X₀) v u γ d word hd hdn).affineSlice
      (independentIntrinsicSlowEmbedding (width X₀)) (independentIntrinsicSlowEmbedding_norm_le _)
      (independentIntrinsicParameterPacking (width X₀) 0 (packing X₀) -
        independentIntrinsicSlowEmbedding (width X₀) X₀)
  let bound := (G'.fam.identity v u γ).record.size *
    (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
      D.eps G'.level ^ ((d : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ)) * B)
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D (by omega) hζ hband D.term).le
  have hb : 0 ≤ bound := mul_nonneg (G'.fam.identity v u γ).record.size_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hκ
      (pow_nonneg (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ D.Λ)).le _))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ D.Λ)) _).le) hB)
  have hcopy X₀ X (hX : ‖X - X₀‖ < 1 / 8) t z :
      G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        c.slot c.chain v u γ d word t (D.eps (G'.level - 1) • X) z = g X₀ t z X := by
    dsimp only [g]
    rw [independentIntrinsicParameterPacking_shift]
    exact S.native_local_model hq hΛ hζ hband hbw P Mn rW Din hp ht c hc v u γ d hd hdn word X₀ X hX t z
  refine ⟨jointSourceReserveOfLocalModels H _ g Q bound hb
    (fun X₀ k hk => S.budget (ctx X₀) v u γ d word hd hdn k hk)
    (fun X₀ t z => hcopy X₀ X₀ (by simp only [sub_self, norm_zero]; norm_num) t z) ?_, ?_⟩
  · intro X₀ t z
    have hn : ∀ᶠ W : Vec 2 × Vec 2 in 𝓝 (z, X₀), ‖W.2 - X₀‖ < 1 / 8 :=
      (isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const).mem_nhds
        (by change ‖X₀ - X₀‖ < (1 / 8 : ℝ); simp only [sub_self, norm_zero]; norm_num)
    filter_upwards [hn] with W hW
    exact hcopy X₀ W.2 hW t W.1
  · intro k _
    exact le_rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! Original path and Eddy mean arrays are arrays for the literal source flux operator. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw θ B : ℝ} {j₀ minBase cap H : ℕ}
  {G : GenStage D (fun _ => ℝ) Dm bw j₀}

def weakInheritedMeanArray_sourceReadout
    (w : List WordLetter) (h : ℕ) (π : StagePath G h) (n : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (M : IndependentWeakMeanArrayProduction D bw j₀ G.level minBase cap H n θ B
      (fun p A d word t => fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
        (familyLiftData D G.level p.1 A.1 (D.eps (G.level - 1)) (pathEdges G π p A))
        (Cc p.1 A.1) n t) d word 0)) :
    IndependentWeakMeanArrayProduction D bw j₀ G.level minBase cap H n θ B
      (fun p A d word t => fluxCoeff
        ((WeakSource.inherited w h π n).fluxOp (D.eps (G.level - 1)) Cc Cc0 p.1 t A.1) d word 0) :=
  M.replaceNative _ fun p A d word t => congrArg (fun f => fluxCoeff f d word 0)
    (weakSource_inherited_native_readout w h π n _ Cc Cc0 p A t).symm

def weakEddyMeanArray_sourceReadout
    (v : CompIn G.comps) (w : List WordLetter) (n : ℕ)
    (Cc Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (M : IndependentWeakMeanArrayProduction D bw j₀ G.level minBase cap H n θ B
      (fun p A d word t => fluxCoeff (weakEddyFlux D G.level (D.eps (G.level - 1))
        (familyLiftData (Dm := Dm) D G.level p.1 A.1 (D.eps (G.level - 1)) (fun _ _ _ => []))
        (Cc0 p.1 A.1) n t) d word 0)) :
    IndependentWeakMeanArrayProduction D bw j₀ G.level minBase cap H n θ B
      (fun p A d word t => fluxCoeff
        ((WeakSource.eddy v w n).fluxOp (D.eps (G.level - 1)) Cc Cc0 p.1 t A.1) d word 0) :=
  M.replaceNative _ fun p A d word t => congrArg (fun f => fluxCoeff f d word 0)
    (weakSource_eddy_native_readout v w n _ Cc Cc0 p A t).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual molecular metric extension retains every independent stored phase translation. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseScaledExtendedMetric_phase_translation (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (ρ a b t : ℝ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y Z, independentFreshCarrierCoordinates A.children.length Y =
      independentFreshCarrierCoordinates A.children.length Z → χ Y = χ Z)
    (δ : Vec (2 + 4 * A.children.length)) (hδ : δ ∈ independentFreshPhaseTranslations A.children.length)
    (Y : Vec (2 + 4 * A.children.length)) :
    actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t (Y + δ) =
      actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y := by
  apply independentFreshCutoffMetric_phase_translation D hΛ A.ctxLevel (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) _ _ ?_ ρ a b t χ hχ δ hδ Y
  intro p hp
  change p ∈ [realChainSlotSeq A 0] ++
    List.ofFn (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) at hp
  rcases List.mem_append.mp hp with hp | hp
  · have he : p = realChainSlotSeq A 0 := List.mem_singleton.mp hp
    rw [he]
    exact realChainSlotSeq_odd D A hA 0 (Nat.zero_le _)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact realChainSlotSeq_odd D A hA (j + 1) (by omega)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier full-parameter productions give the actual ordered inverse forcing at a common matrix
price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count hh n : ℕ} {BG BV BE B : ℝ}
  (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
  (P : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) (H + 2 * D + 2) q S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M p v u) B)

theorem independentLiftPredecessorSource_actual_inverse
    (hH : 1 ≤ H) (hD : 1 ≤ D) (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D)
    (A : Vec 2 →L[ℝ] ℝ) (inp : ι) (Y : Vec (2 + d)) (hY : Y ∈ S.U) :
    IsCellFieldInverse (S.molecular Y).G (S.molecular Y).v S.sZ S.a S.b 0
      (fun t z => independentTimeWindowSource (Ioc S.a S.b)
        (fun t z Y out => independentLiftPredecessorSource S P A out inp t z Y) t z Y)
      (fun t z => (Real.exp (A (independentIntrinsicSlowProjection d Y)))⁻¹ •
        liftApply n (S.Cc (independentStoredParameterProjection d Y) hh n)
          (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) t
          (independentIntrinsicSlowProjection d Y) z) := by
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y), S.v,
      independentConstituentEdgeSlice S.edge S.edgeField S.edges (independentIntrinsicSlowEmbedding d)
        (independentIntrinsicSliceOffset d Y)⟩
  let Dc := fun p q => independentScalarCoefficientSlice (independentLiftPredecessorFields S P p q)
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)
  let Cc := S.Cc (independentStoredParameterProjection d Y)
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)
  let U := independentIntrinsicSliceCarrier d S.U Y
  have hc := S.inverse hh hhh n hn hnN (fun X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ))
    ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const) Y hY
  have hforce t (_ht : t ∈ Icc S.a S.b) z :
      (fun out => independentLiftPredecessorSource S P A out inp t z Y) =
      normalizedLiftCellSource Q Dc f hh n A t z (independentIntrinsicSlowProjection d Y) := by
    funext out
    have he := independent_lift_coefficient_cell_source_slice H hH S.edge hD S.edgeField
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
      (independentIntrinsicSliceOffset d Y) A 1 S.G S.v (independentLiftPredecessorFields S P)
      hh n hn hnD out inp S.metric_entries S.drift_entries
      (independentLiftPredecessorFields_reserve S P) S.edges t z (independentIntrinsicSlowProjection d Y)
    rw [independentIntrinsicSliceOffset_base] at he
    exact he
  have hcopy : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q, ∀ α,
      ∀ t ∈ Icc S.a S.b, ∀ X ∈ U, ∀ z v u,
      Cc p q m α t X z v u = Dc p q m α t X z v u := by
    intro p q hpq m hm α t ht X hX z v u
    have hpR : p ≤ R := by rcases hpq with h | ⟨rfl, _⟩ <;> omega
    exact (independentLiftPredecessorFields_native_copy S P p q hpq hpR m hm α t ht Y X hX z v u).symm
  rw [S.molecular_metric, S.molecular_drift]
  have hmat : (fun t => Matrix.of (S.G t Y)) = (fun t => S.G t Y) := by
    funext t i j
    rfl
  have hi := independent_native_inverse_transfer Q Cc Dc f hh n S.sZ hn S.a S.b A U
    (independentIntrinsicSliceCarrier_isOpen d S.U S.open_carrier Y)
    (independentIntrinsicSlowProjection d Y) (independentIntrinsicSliceCarrier_base d S.U Y hY) Y
    (fun t z Y out => independentLiftPredecessorSource S P A out inp t z Y) hcopy hforce
    (by simpa only [Q, independentIntrinsicSliceOffset_base, hmat] using hc)
  simpa only [Q, independentIntrinsicSliceOffset_base, hmat] using hi

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The physical Piola input uses the literal native dimensional coefficients at all relevant orders. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

open scoped Classical in
def weakStagePhysicalSourceArray (G : GenStage D (fun _ => ℝ) Dm bw j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (t : ℝ) (p : OddSlot)
    (a : ℕ) (I : DerivativeWord2 (a - 1)) (x : Vec 2) : Vec 2 :=
  if a ∈ Finset.Icc 2 (G.fam.identity v u γ).maxOrder then
    G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
      p (G.actual p) v u γ a I t (((G.fam.piece p).material t).symm x)
      ((D.eps G.level)⁻¹ • ((G.fam.piece p).material t).symm x)
  else 0

theorem weakStagePhysicalSourceArray_transport_eq
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (t : ℝ) (p : OddSlot) (d : ℕ) (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) (x : Vec 2) :
    transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
      (G.fam.identity v u γ).maxOrder (fun a J => weakStagePhysicalSourceArray G v u γ t p a J x)
      (d - 1) I x =
    transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
      (G.fam.identity v u γ).maxOrder
      (fun a J => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
        p (G.actual p) v u γ a J t (((G.fam.piece p).material t).symm x)
        ((D.eps G.level)⁻¹ • ((G.fam.piece p).material t).symm x)) (d - 1) I x := by
  classical
  apply CycleJointProofs.transportedCoeff_source_congr
  intro a ha J
  exact ite_eq_left (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp ha).1; omega, (Finset.mem_Icc.mp ha).2⟩)

variable {G G' : GenStage D (fun _ => ℝ) Dm bw j₀} {minBase cap H : ℕ} {B : ℝ}

theorem IndependentWeakStageFluxProduction.physical_source_array_contDiff
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (t : ℝ) (p : OddSlot)
    (a : ℕ) (I : DerivativeWord2 (a - 1)) :
    ContDiff ℝ (H : ℕ∞) (weakStagePhysicalSourceArray G' v u γ t p a I) := by
  classical
  by_cases ha : a ∈ Finset.Icc 2 (G'.fam.identity v u γ).maxOrder
  · let c := WeakStageProductionContext.actual G' Mtop hG minBase cap hbase p
    have hc : c.chain.1.children = [] := by change (G'.actual p).1.children = []; rw [hG.2.2.1 p]; rfl
    obtain ⟨Q, _hQ⟩ := S.native_joint_reserve hq hΛ hζ hband hbw hB P Mn rW Din hp ht c hc v u γ a
      (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2 I
    have he : (weakStagePhysicalSourceArray G' v u γ t p a I) =
        fun y => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
          p (G'.actual p) v u γ a I t (((G'.fam.piece p).material t).symm y)
          ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm y) := by
      funext y
      exact ite_eq_left ha
    rw [he]
    exact dimensionalSourcePhysicalChartSample_contDiff Q
      (Construction.Stream.ocEpsilon_pos (by omega)) (Construction.Stream.ocEpsilon_pos (by omega)) _
      ((G'.fam.piece p).material_symm_smooth t) t
  · have he : weakStagePhysicalSourceArray G' v u γ t p a I = fun _ => 0 := by
      funext y
      exact ite_eq_right ha
    rw [he]
    exact contDiff_const

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every relevant native physical source order has the exact stored dimensional jet budget. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem IndependentWeakStageFluxProduction.physical_source_array_jet_le
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (t : ℝ) (p : OddSlot)
    (Ks : ℕ) (hKs : Ks ≤ H) (C : ℝ) (hC : 1 ≤ C)
    (hGj : ∀ k, 1 ≤ k → k ≤ Ks → ∀ y,
      ‖iteratedFDeriv ℝ k (rescaledChart (D.eps G'.level) ⇑((G'.fam.piece p).material t).symm) y‖ ≤ C)
    (a : ℕ) (ha : a ∈ Finset.Icc 2 (G'.fam.identity v u γ).maxOrder)
    (I : DerivativeWord2 (a - 1)) (k : ℕ) (hk : k ≤ Ks) (i : Fin 2) (x : Vec 2) :
    D.eps G'.level ^ k * ‖iteratedFDeriv ℝ k
      (fun y => weakStagePhysicalSourceArray G' v u γ t p a I y i) x‖ ≤
      (G'.fam.identity v u γ).record.size *
        (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
          D.eps G'.level ^ ((a : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ)) *
            (Ks.factorial * B * C ^ Ks)) := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hε : ∀ j, 0 < D.eps j := fun _ => Construction.Stream.ocEpsilon_pos hΛ₁
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ hband D.term).le
  let c := WeakStageProductionContext.actual G' Mtop hG minBase cap hbase p
  have hc : c.chain.1.children = [] := by change (G'.actual p).1.children = []; rw [hG.2.2.1 p]; rfl
  obtain ⟨Q, hQ⟩ := S.native_joint_reserve hq hΛ hζ hband hbw hB P Mn rW Din hp ht c hc v u γ a
    (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2 I
  have hratio : |D.eps G'.level / D.eps (G'.level - 1)| ≤ 1 := by
    rw [abs_of_pos (div_pos (hε _) (hε _))]
    apply (div_le_iff₀ (hε _)).2
    rw [one_mul]
    exact EntryScales.epsilon_antitone hq hΛ (Nat.sub_le _ _)
  let θ := (G'.fam.identity v u γ).record.size *
    (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
      D.eps G'.level ^ ((a : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ)))
  have hθ : 0 ≤ θ := mul_nonneg (G'.fam.identity v u γ).record.size_nonneg
    (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _)) (Real.rpow_pos_of_pos (hε _) _).le)
  have hreg := S.physical_source_array_contDiff hq hΛ hζ hband hbw hB P Mn rW Din hp ht
    Mtop hG hbase v u γ t p a I
  apply CycleJointProofs.vector_component_jet_budget _ k (hreg.of_le (by exact_mod_cast hk.trans hKs))
    (D.eps G'.level) _ (hε _).le ?_ i x
  intro y
  have hfun : weakStagePhysicalSourceArray G' v u γ t p a I =
      fun z => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        p (G'.actual p) v u γ a I t (((G'.fam.piece p).material t).symm z)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm z) := by funext z; exact ite_eq_left ha
  rw [hfun]
  have hj := dimensionalSourcePhysicalChartSample_jet_le Q (hε _) (hε _) hratio _
    ((G'.fam.piece p).material_symm_smooth t) Ks k hKs hk θ B C hθ hB hC
    (fun j hj => (hQ j (hj.trans hKs)).trans_eq (by dsimp only [θ]; ring)) hGj t y
  exact hj.trans_eq (by dsimp only [θ]; ring)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual inverse tests retain every nonnegative matrix entry through independent coefficient production. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A ι : Type*} [Fintype ι] [DecidableEq ι] {d H : ℕ}

theorem family_variable_window_nonnegative_independent_dual_coefficient_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S n m : ℕ) (hm : m ≤ n) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → Vec d → ι → ℝ}
    (out inp : ι)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x p, IndependentParameterSourceReserve H (fun t z Y => g x p t z Y out))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x p r, r ≤ H → (Qg x p).budget r ≤ θ x * Bs r)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x p t, t ≤ (a x) → ∀ z Y, g x p t z Y out = 0)
    (hmean : ∀ x p t Y, fieldCellMean (fun z => g x p t z Y out) = 0)
    (sZ : ℕ) (c : A → Vec d → LiftCoeff ι (fun _ => ℝ))
    (slowPoint : A → Vec d → Vec 2) (U : A → Set (Vec d))
    (hc : ∀ x Y β (σ : Equiv.Perm (Fin m)), c x Y m (β ∘ σ) = c x Y m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (hactual : ∀ x p Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x p t z Y)
      (fun t z => (Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) (slowPoint x Y)))⁻¹ •
        liftApply n (c x Y) (fun _ Z => Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint x Y) z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      ∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z,
        fext x t z Y = c x Y m α t (slowPoint x Y) z out inp 1 := by
  obtain ⟨B, hB, f, Q, hb, hzmean, hpast, he⟩ :=
    family_variable_window_nonnegative_functional_independent_meanfree_source_extensions_exist (A := A ×
      (Fin (m + 1) × Fin (n + 1))) (fun y => hab y.1) N K S hN hH hS hSK
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) out)
      (fun y => QG y.1) (fun y => Qg y.1 y.2) BG Bs hBG hBs
      (fun y => hQG y.1) (fun y => θ y.1) (fun y => hθ y.1)
      (fun y => hQg y.1 y.2) (fun y => P y.1) (fun y => hP y.1)
      (fun y => v y.1) (fun y => hv y.1) (fun y => hPv y.1) (fun y => V y.1)
      (fun y => hg y.1 y.2) (fun y => hmean y.1 y.2) sZ
      (fun y t Y z => (Real.exp ((lam • ((y.2.2 : ℝ) • coordinateSymbolDirection (y.2.1 : ℝ))) (slowPoint y.1 Y)))⁻¹ •
        liftApply n (c y.1 Y) (fun _ Z => Real.exp ((lam • ((y.2.2 : ℝ) • coordinateSymbolDirection (y.2.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint y.1 Y) z) (fun y => U y.1)
      (fun y => hactual y.1 y.2)
  have hprod x := independent_scalar_lift_calibration_meanfree_extension S n m hm
    (c x) (slowPoint x) (hc x) α (a x) (b x) lam hlam (U x) out inp
    (fun p => f (x, p)) (fun p => Q (x, p)) (fun p t ht Y hY z => by
      simpa only [ContinuousLinearMap.proj_apply, Pi.smul_apply, normalizedLiftTestField] using
        he (x, p) t ht Y hY z)
    (fun p => hzmean (x, p)) (fun p => hpast (x, p))
  choose fe Qe hbe hme hec hpe using hprod
  let BC := finiteScalarCalibrationBudget n m α lam (fun _ => B)
  refine ⟨BC, finiteScalarCalibrationBudget_nonneg n m α lam _ (fun _ => hB),
    fe, Qe, ?_, hme, hpe, hec⟩
  intro x r hr
  rw [hbe x r]
  apply (Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
    (hb (x, p) r hr) (norm_nonneg _))).trans_eq
  unfold BC finiteScalarCalibrationBudget
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual inverse tests retain every nonnegative matrix entry through independent coefficient production. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A ι : Type*} [Fintype ι] [DecidableEq ι] {d H : ℕ}

theorem family_variable_window_cross_natural_nonnegative_independent_dual_coefficient_extensions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S n m : ℕ) (hm : m ≤ n) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → Vec d → ι → ℝ}
    (out inp : ι)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x p, IndependentParameterSourceReserve H (fun t z Y => g x p t z Y out))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x p r, r ≤ H → (Qg x p).budget r ≤ θ x * Bs r)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x p t, t ≤ (a x) → ∀ z Y, g x p t z Y out = 0)
    (hmean : ∀ x p t Y, fieldCellMean (fun z => g x p t z Y out) = 0)
    (Rel : A → Vec d → Vec d → Prop)
    (hGR : ∀ x Y Z, Rel x Y Z → ∀ t, G x t Y = G x t Z)
    (hgR : ∀ x p Y Z, Rel x Y Z → ∀ t z, g x p t z Y out = g x p t z Z out)
    (sZ : ℕ) (c : A → Vec d → LiftCoeff ι (fun _ => ℝ))
    (slowPoint : A → Vec d → Vec 2) (U : A → Set (Vec d))
    (hc : ∀ x Y β (σ : Equiv.Perm (Fin m)), c x Y m (β ∘ σ) = c x Y m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (hactual : ∀ x p Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x p t z Y)
      (fun t z => (Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) (slowPoint x Y)))⁻¹ •
        liftApply n (c x Y) (fun _ Z => Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint x Y) z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (fext : A → ℝ → Vec 2 → Vec d → ℝ)
      (Qext : ∀ x, IndependentParameterSourceReserve S (fext x)),
      (∀ x r, r ≤ S → (Qext x).budget r ≤ θ x * (((d : ℝ) + 1) ^ r * B)) ∧
      (∀ x t Y, fieldCellMean (fun z => fext x t z Y) = 0) ∧
      (∀ x t, t ≤ (a x) → ∀ z Y, fext x t z Y = 0) ∧
      (∀ x t, t ∈ Icc (a x) (b x) → ∀ Y ∈ U x, ∀ z,
        fext x t z Y = c x Y m α t (slowPoint x Y) z out inp 1) ∧
      (∀ x t Y Z, Rel x Y Z → ∀ z, fext x t z Y = fext x t z Z) ∧
      ∀ x x' Y Z, θ x = θ x' → a x = a x' → b x = b x' → v x = v x' →
        (∀ t, G x t Y = G x' t Z) →
        (∀ p t z, g x p t z Y out = g x' p t z Z out) →
        ∀ t z, fext x t z Y = fext x' t z Z := by
  obtain ⟨B, hB, f, Q, hb, hzmean, hpast, he, hnat, hcross⟩ :=
    family_variable_window_cross_natural_nonnegative_functional_independent_meanfree_source_extensions_exist (A := A ×
      (Fin (m + 1) × Fin (n + 1))) (fun y => hab y.1) N K S hN hH hS hSK
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) out)
      (fun y => QG y.1) (fun y => Qg y.1 y.2) BG Bs hBG hBs
      (fun y => hQG y.1) (fun y => θ y.1) (fun y => hθ y.1)
      (fun y => hQg y.1 y.2) (fun y => P y.1) (fun y => hP y.1)
      (fun y => v y.1) (fun y => hv y.1) (fun y => hPv y.1) (fun y => V y.1)
      (fun y => hg y.1 y.2) (fun y => hmean y.1 y.2) (fun y => Rel y.1) (fun y => hGR y.1)
      (fun y Y Z hYZ t z => hgR y.1 y.2 Y Z hYZ t z) sZ
      (fun y t Y z => (Real.exp ((lam • ((y.2.2 : ℝ) • coordinateSymbolDirection (y.2.1 : ℝ))) (slowPoint y.1 Y)))⁻¹ •
        liftApply n (c y.1 Y) (fun _ Z => Real.exp ((lam • ((y.2.2 : ℝ) • coordinateSymbolDirection (y.2.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint y.1 Y) z) (fun y => U y.1)
      (fun y => hactual y.1 y.2)
  have hprod x := independent_scalar_lift_calibration_explicit_natural_meanfree_extension S n m hm
    (c x) (slowPoint x) (hc x) α (a x) (b x) lam hlam (U x) out inp
    (fun p => f (x, p)) (fun p => Q (x, p)) (fun p t ht Y hY z => by
      simpa only [ContinuousLinearMap.proj_apply, Pi.smul_apply, normalizedLiftTestField] using
        he (x, p) t ht Y hY z)
    (fun p => hzmean (x, p)) (Rel x) (fun p => hnat (x, p)) (fun p => hpast (x, p))
  choose fe Qe hbe hme hec hpe hne hformula using hprod
  let BC := finiteScalarCalibrationBudget n m α lam (fun _ => B)
  refine ⟨BC, finiteScalarCalibrationBudget_nonneg n m α lam _ (fun _ => hB),
    fe, Qe, ?_, hme, hpe, hec, hne, ?_⟩
  · intro x r hr
    rw [hbe x r]
    apply (Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
      (hb (x, p) r hr) (norm_nonneg _))).trans_eq
    unfold BC finiteScalarCalibrationBudget
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

  · intro x x' Y Z hθEq ha hb hvEq hG hgEq t z
    rw [hformula x, hformula x']
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    exact hcross (x, p) (x', p) Y Z hθEq ha hb hvEq hG
      (fun r w => hgEq p r w) t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual equal-depth chart comparisons do not require transporting stored coordinate vector types. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshClampedTransfer_equalDepth_geometry_ball (r s : ℕ) (hrs : r = s)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (other : Vec (4 * s) → RealChain)
    (hfamily : ∀ p, (family p).WellSlotted) (hother : ∀ p, (other p).WellSlotted)
    (m : ℕ) (pslot : ℤ)
    (hfm : ∀ p, (family p).ctxLevel = m) (hom : ∀ p, (other p).ctxLevel = m)
    (hfs : ∀ p, (family p).slot = pslot) (hos : ∀ p, (other p).slot = pslot)
    (ρ : ℝ) (P : Vec (4 * r)) (Q : Vec (4 * s))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (family P).geom D = (other Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) :
    ∀ slot t z h,
      independentFreshClampedTransferMatrix r D family m ρ slot t
        (z, independentIntrinsicParameterPacking (4 * r) X P) h =
      independentFreshClampedTransferMatrix s D other m ρ slot t
        (z, independentIntrinsicParameterPacking (4 * s) X Q) h := by
  subst s
  exact independentFreshClampedTransfer_geometry_on_reference_ball r D hΛ hζ family other hfamily hother
    m pslot hfm hom hfs hos ρ P Q hP hQ hgeom X hX

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine fine reserves and actual clamped transitions construct the incoming Piola datum. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshSampledPiolaDatum (r H N Dγ nγ : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : Vec (4 * r) → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps m = ρ * ell) (slot : ℤ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2))
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (C : ℝ) (hKC : ∀ t ∈ I, ∀ X : Vec 2 × Vec (2 + 4 * r), ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × Vec (2 + 4 * r)) × Vec 2 =>
        independentFreshClampedTransferMatrix r D family m ρ slot t Z.1 (D.eps m • Z.2) a b) (X, 0)‖ ≤ C)
    (clock : ℝ → ℝ) (hclock : Measurable clock)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => f d J t z Y a))
    (θ κ e B₀ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hB₀ : 0 ≤ B₀)
    (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤
      θ * (κ * e ^ (nγ - 2) * D.eps m ^ ((d : ℝ) - (nγ : ℝ)) * B₀))
    (hphase : ∀ d J δ, δ ∈ independentFreshPhaseTranslations (r + 1) →
      IndependentSourceTranslationInvariant δ (f d J)) :
    ∃ S : IndependentPiolaWindowDatum (Vec (2 + 4 * r)) H N Dγ nγ (D.eps m) C θ κ e
        (H.factorial * B₀ * (1 + (2 * Real.pi) ^ (H + 1)) ^ H),
      S.window = I ∧
      S.matrix = (fun t z Y h => independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h) ∧
      S.array = (fun d J t z Y a => independentTimeWindowSource I
        (independentFreshCoarseAppendedSource r D m pslot slot ell
          (fun t z Y => f d J (clock t) z Y a)) t z Y) := by
  let B := fun (d : ℕ) => κ * e ^ (nγ - 2) * D.eps m ^ ((d : ℝ) - (nγ : ℝ)) * B₀
  have hB d : 0 ≤ B d := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hκ (pow_nonneg he _))
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _)) hB₀
  have hprod d J a := independentFreshCoarseClockAppendedSource_window_reserve r D hΛ hζ
    m pslot slot hp ell hell clock hclock I hI hsmall H (fun t z Y => f d J t z Y a)
    (Q d J a) θ (B d) hθ (hB d) (hQ d J a)
    (fun δ hδ t z Y => congrFun (hphase d J δ hδ t z Y) a)
  choose R hR using hprod
  let S : IndependentPiolaWindowDatum (Vec (2 + 4 * r)) H N Dγ nγ (D.eps m) C θ κ e
      (H.factorial * B₀ * (1 + (2 * Real.pi) ^ (H + 1)) ^ H) := {
    window := I
    measurable_window := hI
    matrix := fun t z Y h => independentFreshClampedTransferMatrix r D family m ρ slot t (z, Y) h
    smooth := fun t a b => independentFreshClampedTransferMatrix_entry_contDiff r D hΛ hζ
      family hfamily m pslot hm hs hp harea ρ ell hscale slot t hf a b
    measurable := fun Y h a b => independentFreshClampedTransferMatrix_entry_measurable r D hΛ hζ
      family hfamily pslot hs hp harea m hm ρ slot Y h a b
    periodic := fun t Y h a b => independentFreshClampedTransferMatrix_entry_periodic r D hΛ hζ
      family hfamily pslot hs hp m hm ρ slot t Y h a b
    jets := hKC
    array := fun d J t z Y a => independentTimeWindowSource I
      (independentFreshCoarseAppendedSource r D m pslot slot ell
        (fun t z Y => f d J (clock t) z Y a)) t z Y
    reserve := R
    budget := by
      intro d J a n _
      rw [hR d J a n]
      exact le_of_eq (by dsimp only [B]; ring) }
  exact ⟨S, rfl, rfl, rfl⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The genuine open native carrier transfers metric values and all local slow derivatives to the original lift data. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseScaledExtendedMetric_carrier_copy (D : OCData) (A : RealChain) (bw ρ a b t : ℝ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (ht : t ∈ Icc a b) (Y : Vec (2 + 4 * A.children.length))
    (hY : Y ∈ actualIndependentCoarseNativeCarrier D A bw) :
    actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y = actualIndependentCoarseScaledMetric D A ρ t Y := by
  have he : χ Y = 1 := (hχ Y hY.2).eq_of_nhds
  simp only [actualIndependentCoarseScaledExtendedMetric, clampedParameterMetric, min_eq_right ht.2,
    max_eq_right ht.1, cutoffParameterMetric, he, one_smul, add_sub_cancel]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual clamped matrices agree across stored charts on the whole reference slow ball. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

theorem actualWeakClampedTransfer_reference_geometry (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (ρ : ℝ) (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (slot : ℤ) (t : ℝ) (z w : Vec 2) :
    independentFreshClampedTransferMatrix c.chain.1.children.length D
      (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel ρ slot t
      (z, independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) w =
    independentFreshClampedTransferMatrix c'.chain.1.children.length D
      (actualIndependentCoarseParameterChain D c'.chain.1) c'.chain.1.ctxLevel ρ slot t
      (z, independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) w := by
  rw [c.chain.2.1, c'.chain.2.1]
  exact independentFreshClampedTransfer_equalDepth_geometry_ball
    c.chain.1.children.length c'.chain.1.children.length hdepth D hΛ hζ
    (actualIndependentCoarseParameterChain D c.chain.1) (actualIndependentCoarseParameterChain D c'.chain.1)
    (actualIndependentCoarseParameterChain_wellSlotted D c.chain.1 c.chain.2.2.2.1)
    (actualIndependentCoarseParameterChain_wellSlotted D c'.chain.1 c'.chain.2.2.2.1)
    level c.slot.1
    (fun W => (actualIndependentCoarseParameterChain_ctxLevel D c.chain.1 W).trans c.chain.2.1)
    (fun W => (actualIndependentCoarseParameterChain_ctxLevel D c'.chain.1 W).trans c'.chain.2.1)
    (fun W => (actualIndependentCoarseParameterChain_slot D c.chain.1 W).trans c.chain.2.2.2.2.1)
    (fun W => (actualIndependentCoarseParameterChain_slot D c'.chain.1 W).trans
      (c'.chain.2.2.2.2.1.trans (congrArg Subtype.val hslot).symm))
    ρ P Q hP hQ hgeom X hX slot t z w

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual stored-chain geometry constructs sampled incoming data without extra regularity premises. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseSampledPiolaDatum (H N Dγ nγ : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (A : RealChain) {bw : ℝ} {j₀ i : ℕ} {p : ℤ}
    (hA : IsAdmissibleChain D bw j₀ i p A)
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps A.ctxLevel = ρ * ell) (slot : ℤ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (A.ctxLevel + 1) slot - t| * ocA D.α D.q D.Λ A.ctxLevel ≤ 1)
    (C : ℝ) (hKC : ∀ t ∈ I, ∀ X : Vec 2 × Vec (2 + 4 * A.children.length), ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × Vec (2 + 4 * A.children.length)) × Vec 2 =>
        independentFreshClampedTransferMatrix A.children.length D (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t Z.1 (D.eps A.ctxLevel • Z.2) a b) (X, 0)‖ ≤ C)
    (clock : ℝ → ℝ) (hclock : Measurable clock)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec (2 + 4 * (A.children.length + 1)) → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => f d J t z Y a))
    (θ κ e B₀ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hB₀ : 0 ≤ B₀)
    (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤
      θ * (κ * e ^ (nγ - 2) * D.eps A.ctxLevel ^ ((d : ℝ) - (nγ : ℝ)) * B₀))
    (hphase : ∀ d J δ, δ ∈ independentFreshPhaseTranslations (A.children.length + 1) →
      IndependentSourceTranslationInvariant δ (f d J)) :
    ∃ S : IndependentPiolaWindowDatum (Vec (2 + 4 * A.children.length)) H N Dγ nγ (D.eps A.ctxLevel) C θ κ e
        (H.factorial * B₀ * (1 + (2 * Real.pi) ^ (H + 1)) ^ H),
      S.window = I ∧
      S.matrix = (fun t z Y h => independentFreshClampedTransferMatrix A.children.length D (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t (z, Y) h) ∧
      S.array = (fun d J t z Y a => independentTimeWindowSource I
        (independentFreshCoarseAppendedSource A.children.length D A.ctxLevel A.slot slot ell
          (fun t z Y => f d J (clock t) z Y a)) t z Y) := by
  have hp : Odd A.slot := by
    have hh := realChainSlotSeq_odd D A hA A.children.length le_rfl
    rw [realChainSlotSeq_last A hA.2.2.1] at hh
    exact hh
  exact independentFreshSampledPiolaDatum A.children.length H N Dγ nγ D hΛ hζ
    (actualIndependentCoarseParameterChain D A)
    (actualIndependentCoarseParameterChain_wellSlotted D A hA.2.2.1)
    A.ctxLevel A.slot (actualIndependentCoarseParameterChain_ctxLevel D A)
    (actualIndependentCoarseParameterChain_slot D A) hp
    (actualIndependentCoarseParameterChain_area D hΛ A hA)
    ρ ell hell hscale slot
    (actualIndependentCoarseParameterChain_chart_contDiff D A hA.2.2.1 ρ (D.slotAnchor (A.ctxLevel + 1) slot))
    I hI hsmall C hKC clock hclock f Q θ κ e B₀ hθ hκ he hB₀ hQ hphase

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual inverse tests retain every nonnegative matrix entry through independent coefficient production. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {A ι : Type*} [Fintype ι] [DecidableEq ι] {d H : ℕ}

theorem family_variable_window_independent_coefficient_productions_exist {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K S n m : ℕ) (hm : m ≤ n) (hN : N + 2 ≤ H) (hH : N + (K + N) + 1 ≤ H)
    (hS : S ≤ N) (hSK : S + 4 ≤ K)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {g : A → (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → Vec d → ι → ℝ}
    (out inp : ι)
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qg : ∀ x p, IndependentParameterSourceReserve H (fun t z Y => g x p t z Y out))
    (BG Bs : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (θ : A → ℝ) (hθ : ∀ x, 0 ≤ θ x)
    (hQg : ∀ x p r, r ≤ H → (Qg x p).budget r ≤ θ x * Bs r)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (hg : ∀ x p t, t ≤ (a x) → ∀ z Y, g x p t z Y out = 0)
    (hmean : ∀ x p t Y, fieldCellMean (fun z => g x p t z Y out) = 0)
    (sZ : ℕ) (c : A → Vec d → LiftCoeff ι (fun _ => ℝ))
    (slowPoint : A → Vec d → Vec 2) (U : A → Set (Vec d))
    (hc : ∀ x Y β (σ : Equiv.Perm (Fin m)), c x Y m (β ∘ σ) = c x Y m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (hactual : ∀ x p Y, Y ∈ U x → IsCellFieldInverse (P x Y).G (P x Y).v sZ (a x) (b x) 0
      (fun t z => g x p t z Y)
      (fun t z => (Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) (slowPoint x Y)))⁻¹ •
        liftApply n (c x Y) (fun _ Z => Real.exp ((lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) Z) •
          (Pi.single inp (1 : ℝ) : ι → ℝ)) t (slowPoint x Y) z)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      Nonempty (IndependentScalarCoefficientProduction d S n (a x) (b x) (U x) (c x) (slowPoint x)
        m α out inp (θ x) B) := by
  obtain ⟨B, hB, f, Q, hb, hmean, hpast, hcopy⟩ :=
    family_variable_window_nonnegative_independent_dual_coefficient_extensions_exist hab N K S n m hm hN hH hS hSK
      out inp QG Qg BG Bs hBG hBs hQG θ hθ hQg P hP v hv hPv V hg hmean sZ c
      slowPoint U hc α lam hlam hactual
  refine ⟨((d : ℝ) + 1) ^ S * B, mul_nonneg (pow_nonneg (by positivity) _) hB, ?_⟩
  intro x
  refine ⟨⟨f x, Q x, ?_, hcopy x, fun _ => hmean x, fun _ => hpast x⟩⟩
  intro r hr
  exact (hb x r hr).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact le_add_of_nonneg_left (Nat.cast_nonneg d) : (1 : ℝ) ≤ (d : ℝ) + 1) hr) hB)
    (hθ x))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual stored-chain geometry constructs sampled incoming data without extra regularity premises. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseSampledPiolaDatum_cast (H N Dγ nγ : ℕ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (A : RealChain) {bw : ℝ} {j₀ i : ℕ} {p : ℤ}
    (hA : IsAdmissibleChain D bw j₀ i p A)
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps A.ctxLevel = ρ * ell) (slot : ℤ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (A.ctxLevel + 1) slot - t| * ocA D.α D.q D.Λ A.ctxLevel ≤ 1)
    (C : ℝ) (hKC : ∀ t ∈ I, ∀ X : Vec 2 × Vec (2 + 4 * A.children.length), ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × Vec (2 + 4 * A.children.length)) × Vec 2 =>
        independentFreshClampedTransferMatrix A.children.length D (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t Z.1 (D.eps A.ctxLevel • Z.2) a b) (X, 0)‖ ≤ C)
    (clock : ℝ → ℝ) (hclock : Measurable clock)
    (r : ℕ) (hr : r = A.children.length + 1)
    (f : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec (2 + 4 * r) → Vec 2)
    (Q : ∀ d J a, IndependentParameterSourceReserve H (fun t z Y => f d J t z Y a))
    (θ κ e B₀ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hB₀ : 0 ≤ B₀)
    (hQ : ∀ d J a n, n ≤ H → (Q d J a).budget n ≤
      θ * (κ * e ^ (nγ - 2) * D.eps A.ctxLevel ^ ((d : ℝ) - (nγ : ℝ)) * B₀))
    (hphase : ∀ d J δ, δ ∈ independentFreshPhaseTranslations r →
      IndependentSourceTranslationInvariant δ (f d J)) :
    ∃ S : IndependentPiolaWindowDatum (Vec (2 + 4 * A.children.length)) H N Dγ nγ (D.eps A.ctxLevel) C θ κ e
        (H.factorial * B₀ * (1 + (2 * Real.pi) ^ (H + 1)) ^ H),
      S.window = I ∧
      S.matrix = (fun t z Y h => independentFreshClampedTransferMatrix A.children.length D (actualIndependentCoarseParameterChain D A) A.ctxLevel ρ slot t (z, Y) h) ∧
      S.array = (fun d J t z Y a => independentTimeWindowSource I
        (independentFreshCoarseAppendedSource A.children.length D A.ctxLevel A.slot slot ell
          (fun t z Y => f d J (clock t) z
            (Eq.rec (motive := fun r _ => Vec (2 + 4 * r)) Y hr.symm) a)) t z Y) := by
  subst r
  exact actualIndependentCoarseSampledPiolaDatum H N Dγ nγ D hΛ hζ A hA ρ ell hell hscale
    slot I hI hsmall C hKC clock hclock f Q θ κ e B₀ hθ hκ he hB₀ hQ hphase

end AVRegularity.EntryWeakProofs
end
end
end
