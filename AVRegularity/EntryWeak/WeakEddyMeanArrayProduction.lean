-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.UniformWeakStageStepGeometry
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

section
section
/-! The literal scheduled successor field has a full independent reserve with one finite menu price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.stepField_production
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B) (he : level + 1 = fine)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps c.chain.1.ctxLevel = ρ * ell)
    (I : ℤ → Set ℝ) (hI : ∀ slot, MeasurableSet (I slot))
    (hsmall : ∀ slot, Odd slot ∧ IsScheduledIn D level slot c.slot.1 → ∀ t ∈ I slot,
      |D.slotAnchor (c.chain.1.ctxLevel + 1) slot - t| * ocA D.α D.q D.Λ c.chain.1.ctxLevel ≤ 1)
    (N K : ℕ) (hnK : n ≤ K) (hHN : H + K ≤ N)
    (C : ℝ) (hC : 0 ≤ C)
    (hKC : ∀ slot, Odd slot ∧ IsScheduledIn D level slot c.slot.1 → ∀ t ∈ I slot,
      ∀ X : Vec 2 × Vec (2 + 4 * c.chain.1.children.length), ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × Vec (2 + 4 * c.chain.1.children.length)) × Vec 2 =>
        independentFreshClampedTransferMatrix c.chain.1.children.length D
          (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel ρ slot t Z.1
          (D.eps c.chain.1.ctxLevel • Z.2) a b) (X, 0)‖ ≤ C)
    (hκ : 0 ≤ D.κ D.term) (hτ : 0 < ocTau D.α D.q D.Λ fine)
    (d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (M.stepField he hΛ hbw c ρ ell I d word),
      ∀ k ≤ H, Q.budget k ≤ θ *
        (D.κ D.term * D.eps fine ^ (n - 2) * D.eps level ^ ((d : ℝ) - (n : ℝ))) *
        weakPiolaProductionMenuBudget H N K C
          (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H) := by
  let Eligible : ℤ → Prop := fun slot => Odd slot ∧ IsScheduledIn D level slot c.slot.1
  have hp slot (hs : Eligible slot) := M.sampled_field_production hθ hB he hΛ hζ hbw c
    ⟨slot, hs.1⟩ hs.2 ρ ell hell hscale (I slot) (hI slot) (hsmall slot hs) C (hKC slot hs)
    hκ hC (by omega) d hd word
  choose R hR using hp
  let B₀ := H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H
  have hB₀ : 0 ≤ B₀ := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg (by positivity) _)
  let dim := θ * (D.κ D.term * D.eps fine ^ (n - 2) * D.eps level ^ ((d : ℝ) - (n : ℝ)))
  have hdim : 0 ≤ dim := mul_nonneg hθ (mul_nonneg (mul_nonneg hκ
    (pow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _))
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ) _).le)
  let price := 2 * ∑ j : Fin (H + 1), independentPiolaDimensionlessPrice N n j.val C B₀ (d - 1)
  have hprice : 0 ≤ price := mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    independentPiolaDimensionlessPrice_nonneg _ _ _ _ _ _ hC hB₀)
  obtain ⟨Q, hQ⟩ := independentWeakConditionalPartitionReserve D hΛ fine H hτ Eligible
    (fun slot hs => actualWeakSampledPiolaField D c.chain.1 ρ ell slot (I slot) n
      (M.referenceField he hΛ hbw c ⟨slot, hs.1⟩ hs.2) d word)
    R dim price hdim hprice hR
  refine ⟨Q, ?_⟩
  intro k hk
  have hc := weakPiolaProductionMenuCost_le H N K n (d - 1) C B₀ hC hB₀ hnK
    ((Nat.sub_le d 1).trans hdK)
  have hb := hQ k hk
  calc
    _ ≤ dim * weakPiolaProductionMenuCost H N C B₀ (n, d - 1) := by
      exact hb.trans_eq (by dsimp only [price, weakPiolaProductionMenuCost]; ring)
    _ ≤ dim * weakPiolaProductionMenuBudget H N K C B₀ := mul_le_mul_of_nonneg_left hc hdim

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual successor cutoff sum reads the original source flux on its native carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B C : ℝ} {j₀ minBase cap H n level fine N : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.stepField_native
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (geo : WeakStageStepGeometry D bw j₀ level minBase cap N C)
    (fop : FamFluxOp)
    (hnative : ∀ p A d word t, native p A d word t = fluxCoeff (fop p.1 t A.1) d word 0)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (level - 1))
      j₀ level c.slot.1) (t : ℝ) (z : Vec 2) (d : ℕ) (hd : 2 ≤ d)
    (word : DerivativeWord2 (d - 1)) :
    M.stepField he (by omega) hbw c (D.eps (level - 1)) (D.eps level / D.eps (level - 1))
      (weakStageCutoffWindow D fine) d word t z Y =
    let A := (actualIndependentCoarseParameterChain D c.chain.1
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)).recenter D
      (D.eps (level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y)
    ∑ᶠ (slot : ℤ) (_ : Odd slot ∧ IsScheduledIn D level slot c.slot.1),
      ocCutoff D.α D.q D.Λ fine slot t • transportedCoeff
        (fun w => (childTransition D slot t (A.recenter D w) (z + (D.eps level)⁻¹ • w))⁻¹) n
        (fun e β => fluxCoeff (fop slot t (A.appendChild D slot t z)) e β 0) (d - 1) word 0 := by
  classical
  unfold IndependentWeakMeanArrayProduction.stepField independentWeakCutoffPartition
  dsimp only
  apply finsum_congr
  intro slot
  rw [smul_finsum]
  apply finsum_congr
  intro hs
  by_cases ht : ocCutoff D.α D.q D.Λ fine slot t = 0
  · rw [ht, zero_smul, zero_smul]
  · have hw : t ∈ weakStageCutoffWindow D fine slot := ht
    have hw' : t ∈ weakStageCutoffWindow D (level + 1) slot := by simpa only [he] using hw
    have ha := geo.append c ⟨slot, hs.1⟩ hs.2 Y hY t hw' z
    have hc := M.sampledField_native he hq hΛ hζ hband hbw hbw₁ c ⟨slot, hs.1⟩ hs.2 Y hY t hw z
      ha geo.ratio (geo.displacement c.slot.1 c.slot.2 slot t hw' z) d hd word
    rw [hc]
    have hb : (fun e β => native ⟨slot, hs.1⟩
        ((c.appendNative Y ⟨slot, hs.1⟩ t z ha).relevel he).chain e β t) =
        (fun e β => fluxCoeff (fop slot t (weakStageAppendedNativeChain c Y slot t z)) e β 0) := by
      funext e β
      exact hnative _ _ e β t
    rw [hb]
    rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! The uniform geometry controls instantiate the literal successor reserve at its physical scales. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B C : ℝ} {j₀ minBase cap H n level fine N K : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.canonicalStep_production
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B) (he : level + 1 = fine)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (geo : WeakStageStepGeometry D bw j₀ level minBase cap N C)
    (hnK : n ≤ K) (hHN : H + K ≤ N) (hC : 0 ≤ C) (hκ : 0 ≤ D.κ D.term)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H
      (M.stepField he hΛ hbw c (D.eps (level - 1)) (D.eps level / D.eps (level - 1))
        (weakStageCutoffWindow D fine) d word),
      ∀ k ≤ H, Q.budget k ≤ θ *
        (D.κ D.term * D.eps fine ^ (n - 2) * D.eps level ^ ((d : ℝ) - (n : ℝ))) *
        weakPiolaProductionMenuBudget H N K C
          (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H) := by
  have hc : c.chain.1.ctxLevel = level := c.chain.2.1
  have hε : D.eps (level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  refine M.stepField_production hθ hB he hΛ hζ hbw c _ _ geo.ratio ?_
    (weakStageCutoffWindow D fine) (weakStageCutoffWindow_measurable D hΛ fine) ?_
    N K hnK hHN C hC ?_ hκ (Construction.Stream.ocTau_pos hΛ) d hd hdK word
  · rw [hc]
    exact (mul_div_cancel₀ _ hε).symm
  · intro slot _ t ht
    rw [hc]
    exact geo.small slot t (by simpa only [he] using ht)
  · intro slot hs t ht X a b j hj
    simpa only [hc] using geo.jets c ⟨slot, hs.1⟩ hs.2 t
      (by simpa only [he] using ht) X a b j hj

end AVRegularity.EntryWeakProofs
end
end

section
/-! Physical source amplitudes preserve the produced successor reserve with the exact stored weight. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B C lam : ℝ} {j₀ minBase cap H n level fine N K : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

def IndependentWeakMeanArrayProduction.scaledStepField
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (lam : ℝ) (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2 :=
  fun t z Y => lam • M.stepField he hΛ hbw c (D.eps (level - 1))
    (D.eps level / D.eps (level - 1)) (weakStageCutoffWindow D fine) d word t z Y

theorem IndependentWeakMeanArrayProduction.scaledStep_production
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (he : level + 1 = fine)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (geo : WeakStageStepGeometry D bw j₀ level minBase cap N C)
    (hnK : n ≤ K) (hHN : H + K ≤ N) (hC : 0 ≤ C) (hκ : 0 ≤ D.κ D.term)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (M.scaledStepField he hΛ hbw lam c d word),
      ∀ k ≤ H, Q.budget k ≤ (lam * θ) *
        (D.κ D.term * D.eps fine ^ (n - 2) * D.eps level ^ ((d : ℝ) - (n : ℝ)) *
        weakPiolaProductionMenuBudget H N K C
          (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H)) := by
  obtain ⟨Q, hQ⟩ := M.canonicalStep_production hθ hB he hΛ hζ hbw geo hnK hHN hC hκ c d hd hdK word
  refine ⟨Q.constSmul lam, ?_⟩
  intro k hk
  rw [IndependentParameterSourceReserve.constSmul_budget, abs_of_nonneg hlam]
  exact (mul_le_mul_of_nonneg_left (hQ k hk) hlam).trans_eq (by ring)

theorem IndependentWeakMeanArrayProduction.scaledStep_phase
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (lam : ℝ) (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (δ : Vec (2 + 4 * c.chain.1.children.length))
    (hδ : δ ∈ independentFreshPhaseTranslations c.chain.1.children.length) :
    IndependentSourceTranslationInvariant δ (M.scaledStepField he hΛ hbw lam c d word) := by
  intro t z Y
  exact congrArg (fun v : Vec 2 => lam • v)
    (M.stepField_phase he hΛ hζ hbw c _ _ _ d word δ hδ t z Y)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Source data retain the literal passage transfer and the independently produced fine mean array. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

open scoped Classical in
structure WeakStageProducedSourceMean
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (minBase cap H : ℕ) (B : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) where
  weight : ℝ
  amplitude : ℝ
  weight_nonneg : 0 ≤ weight
  amplitude_nonneg : 0 ≤ amplitude
  size_eq : (G.fam.identity v u γ).record.size = amplitude * weight
  flux : FamFluxOp
  mean : IndependentWeakMeanArrayProduction D bw j₀ (G.level + 1) minBase (cap + 1) H
    (G.fam.identity v u γ).maxOrder weight B
    (fun p A d word t => fluxCoeff (flux p.1 t A.1) d word 0)
  transfer : ∀ (p : OddSlot) (c : StageCtx D bw j₀ G.level p) (d : ℕ)
    (word : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
    G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
      p c v u γ d word t Y z =
    if IsAdmissibleChain D bw j₀ G.level p.1 (c.1.recenter D Y) then
      amplitude • ∑ᶠ (slot : ℤ) (_ : Odd slot ∧ IsScheduledIn D G.level slot p.1),
        ocCutoff D.α D.q D.Λ (G.level + 1) slot t • transportedCoeff
          (fun h => (childTransition D slot t ((c.1.recenter D Y).recenter D h)
            (z + (D.eps G.level)⁻¹ • h))⁻¹) (G.fam.identity v u γ).maxOrder
          (fun e β => fluxCoeff (flux slot t ((c.1.recenter D Y).appendChild D slot t z)) e β 0)
          (d - 1) word 0
    else 0

end AVRegularity.EntryWeakProofs
end
end

section
/-! Coherent produced fine means assemble into the actual coarse dimensional flux reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B C : ℝ} {j₀ minBase cap H N K : ℕ}
  {G : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem independentWeakStageFluxProduction_of_producedMeans
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK : G.maxOrderBound K) (hHN : H + K ≤ N)
    (geo : WeakStageStepGeometry D bw j₀ G.level minBase cap N C)
    (src : ∀ v u (γ : G.fam.Γ v u), WeakStageProducedSourceMean G minBase cap H B v u γ) :
    Nonempty (IndependentWeakStageFluxProduction G minBase cap H
      (weakPiolaProductionMenuBudget H N K C
        (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H))) := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ hband D.term).le
  have hp c v u γ d word (hd : 2 ≤ d) (hdn : d ≤ (G.fam.identity v u γ).maxOrder) :=
    (src v u γ).mean.scaledStep_production (src v u γ).weight_nonneg hB
      (src v u γ).amplitude_nonneg rfl hΛ₁ hζ hbw geo (hK v u γ) hHN hC hκ c d
      (by omega) (hdn.trans (hK v u γ)) word
  choose Q hQ using hp
  refine ⟨{ field := fun c v u γ => (src v u γ).mean.scaledStepField rfl hΛ₁ hbw
              (src v u γ).amplitude c
            reserve := Q
            budget := ?_
            phase := ?_
            native_copy := ?_
            geometry := ?_ }⟩
  · intro c v u γ d word hd hdn k hk
    rw [(src v u γ).size_eq]
    exact hQ c v u γ d word hd hdn k hk
  · intro c v u γ d word δ hδ
    exact (src v u γ).mean.scaledStep_phase rfl hΛ₁ hζ hbw _ c d word δ hδ
  · intro c v u γ d word hd _ Y hY t z
    rw [(src v u γ).transfer c.slot (c.atParameter Y hY) d word t _ z hd]
    have ha : IsAdmissibleChain D bw j₀ G.level c.slot.1
        ((c.atParameter Y hY).1.recenter D
          (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y)) := hY.1.2
    rw [ite_eq_left ha]
    apply congrArg (fun w : Vec 2 => (src v u γ).amplitude • w)
    exact (src v u γ).mean.stepField_native rfl hq hΛ hζ hband hbw hbw₁ geo
      (src v u γ).flux (fun _ _ _ _ _ => rfl) c Y hY t z d hd word
  · intro c c' hslot hdepth v u γ d word _ _ P Q hP hQ hgeom X hX t z
    apply congrArg (fun w : Vec 2 => (src v u γ).amplitude • w)
    exact (src v u γ).mean.stepField_geometry rfl hΛ₁ hζ hbw c c' hslot hdepth d word
      P Q hP hQ hgeom X hX geo.ratio (weakStageCutoffWindow D (G.level + 1))
      (fun slot _ t ht z => geo.displacement c.slot.1 c.slot.2 slot t ht z) t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Passage witnesses select actual produced means, retaining their original lift histories and tags. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakPassage_produced_source_means
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P) (htG : G.HasTags P)
    (produce : ∀ (s : WeakSource G)
      (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
      (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      s.Valid Mn.N Mn.R Din → s.IsLiftFamily Mn.sX Mn.sZ Mn.N (D.eps (G.level - 1)) Cc →
      (∀ (slot : ℤ) (A : RealChain), Odd slot → IsAdmissibleChain D bw j₀ G.level slot A →
        IsLiftSequence (familyLiftData (Dm := Dm) D G.level slot A
          (D.eps (G.level - 1)) (fun _ _ _ => [])) Mn.sX Mn.sZ
          (D.slotStart G.level slot / D.cellScaleSq G.level)
          ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          Mn.N 0 (Cc0 slot A)) →
      Nonempty (IndependentWeakMeanArrayProduction D bw j₀ G.level minBase (cap + 1) H
        s.degree (weakSourceMeanWeight P s) B
        (fun p A d word t => fluxCoeff
          (s.fluxOp (D.eps (G.level - 1)) Cc Cc0 p.1 t A.1) d word 0)))
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) :
    Nonempty (WeakStageProducedSourceMean G' minBase cap H B v u γ) := by
  obtain ⟨s, Cc, Cc0, hv, _hsrc, _htgt, hn, hsize, hCc, hCc0, htransfer⟩ :=
    weakPassage_production_data hΛ hζ hband P Mn rW Din G G' hp ht v u γ
  obtain ⟨M⟩ := produce s Cc Cc0 hv hCc hCc0
  have he : G.level - 1 = G'.level := hp.2.1.symm
  have he' : G.level = G'.level + 1 := by have := hp.1; omega
  refine ⟨{ weight := weakSourceMeanWeight P s
            amplitude := s.lam G.level Mn.η0
            weight_nonneg := weakSourceMeanWeight_nonneg P htG s
            amplitude_nonneg := weakSource_lam_nonneg hΛ Mn.η0 s
            size_eq := hsize.trans (weakSource_tag_size_meanWeight P rW Mn.η0 s)
            flux := s.fluxOp (D.eps (G.level - 1)) Cc Cc0
            mean := ?_
            transfer := ?_ }⟩
  · rw [hn]
    exact M.relevelFlux _ he'
  · intro p c d word t Y z hd
    simpa only [he, he', hn, Nat.add_sub_cancel] using htransfer p c d word t Y z hd

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual stage fields and original lift histories produce all inherited physical mean arrays coherently. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_inherited_mean_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H K N R sZ : ℕ) (hNK : N ≤ K) (hK₁ : 1 ≤ K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧
      ∃ E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV B, ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ) (hKD : K ≤ Dm), ∀ bw j₀ (G : GenStage D (fun _ => ℝ) Dm bw j₀),
      D.term < G.level → G.maxOrderBound K → ∀ minBase Hstage, M₀ ≤ minBase →
      weakInheritedPrimitiveMenuOrder H K N R + K + 1 ≤ Hstage →
      ∀ S : IndependentWeakStageFluxProduction G minBase J Hstage B,
      ∀ c : WeakStageProductionContext D bw j₀ G.level minBase J,
      ∀ h (π : StagePath G h) (hh : h ∈ Finset.Icc 1 R) sX,
      ∀ Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ),
      (∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
        IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
          (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
            (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
          (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
          ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          N h (Cc c.slot.1 A)) →
      ∃ x : IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
          (weakInheritedPrimitiveMenuOrder H K N R) K N h 1 sZ BG BV B,
        x.primitive.a = D.slotStart G.level c.slot.1 / D.cellScaleSq G.level ∧
        x.primitive.b =
          (((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level ∧
        x.primitive.U = actualIndependentCoarseProductionCarrier D c.chain.1 bw
          (D.eps (G.level - 1)) j₀ G.level c.slot.1 ∧
        x.primitive.G = actualIndependentCoarseScaledExtendedMetric D c.chain.1 (D.eps (G.level - 1))
          (χ c.chain.1.children.length) x.primitive.a x.primitive.b ∧
        x.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ G.level (D.kap G.level) c.slot.1 ∧
        x.primitive.edge = restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)) ∧
        x.primitive.edgeField = restrictedIndependentEdgeField K hKD
          (independentPathTemplateField (S.pathIncomingField π c)) ∧
        x.primitive.M = weightedPathMatrix h (stagePathStoredWeight G π) ∧
        x.primitive.Cc = independentCarrierCoefficientExtension
          (actualIndependentCoarseStoredCarrier D c.chain.1 bw)
          (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P)) ∧
        x.translations = independentFreshPhaseTranslations c.chain.1.children.length ∧
        ∀ (n : ℕ) (hn : n ∈ Finset.Icc 2 K) (d : ℕ) (hd : d ∈ Finset.Icc 2 n)
          (word : DerivativeWord2 (d - 1)),
        let j := IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n d
          c.depth_bound hh hn hd word
        ∃ Q : IndependentParameterSourceReserve H (E.physicalField j x D G.level),
          (∀ r ≤ H, Q.budget r ≤
            finiteMatrixPower (weightedPathMatrix h (stagePathStoredWeight G π)) h (Fin.last h) 0 *
              (D.κ D.term * D.eps G.level ^ (n - 2) *
                D.eps (G.level - 1) ^ ((d : ℝ) - (n : ℝ)) * E.budget)) ∧
          (∀ δ ∈ independentFreshPhaseTranslations c.chain.1.children.length,
            IndependentSourceTranslationInvariant δ (E.physicalField j x D G.level)) := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, M₀, hM₀, hprod⟩ :=
    uniform_weak_stage_inherited_primitive_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J (weakInheritedPrimitiveMenuOrder H K N R) K
  let E := independentWeakInheritedMeanProducer J H K N R sZ hNK hK₁ BG BV B
    (zero_le_one.trans hBG) hBV hB
  refine ⟨χ, BG, BV, hχ, hBG, hBV, E, M₀, hM₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK minBase Hstage
    hbase hH S c h π hh sX Cc hCc
  obtain ⟨x, ha, hb, hU, hG, hv, he, hf, hM, hc, hphase⟩ :=
    hprod D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK
      minBase Hstage B hbase hB hH S c h π N sX sZ hNK Cc hCc
  refine ⟨x, ha, hb, hU, hG, hv, he, hf, hM, hc, hphase, ?_⟩
  intro n hn d hd word
  let j := IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n d
    c.depth_bound hh hn hd word
  have hΛ' : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hκ : 0 ≤ D.κ D.term := by
    simpa only [weakData_kap_terminal D D.term le_rfl] using
      (weakData_kap_pos D hΛ' hζ' hband D.term).le
  obtain ⟨Q, hQ, hperiod⟩ := E.physicalField_production j x D G.level hκ
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ')
  refine ⟨Q, ?_, ?_⟩
  · intro r hr
    have hbound := hQ r hr
    rw [hM] at hbound
    exact hbound
  · intro δ hδ t z Y
    exact hperiod δ (by rw [hphase]; exact hδ) t z Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual produced stage means read the original path flux, using the original localized histories. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N h sZ n d : ℕ}
  {BG BV B C : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

def weakStageNativeInheritedLiftData (π : StagePath G h)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (hKD : K ≤ Dm)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) :
    LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) K :=
  familyLiftData D G.level c.slot.1
    (actualIndependentCoarseParameterChain D c.chain.1
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))
    (D.eps (G.level - 1)) (restrictConstituentEdges K hKD
      (actualIndependentCoarsePathEdges π c
        (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)))

theorem weakStageInheritedMean_physical_native_copy
    (S : IndependentWeakStageFluxProduction G minBase cap Hstage B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (π : StagePath G h)
    (hKD : K ≤ Dm) (hK : G.maxOrderBound K)
    (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates c.chain.1.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (word : DerivativeWord2 (d - 1))
    (E : IndependentInheritedMeanNaturalOutput (Fin (h + 1)) (4 * c.chain.1.children.length)
      H K N h 1 sZ h n (d - 1) word BG BV B C)
    (x : IndependentInheritedMeanInput (Fin (h + 1)) (4 * c.chain.1.children.length)
      H K N h 1 sZ BG BV B)
    (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < G.level)
    (hNK : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B)
    (hK₁ : 1 ≤ K) (hn : 2 ≤ n) (hhpos : h ≠ 0) (hd : d ≤ n) (hd₁ : 1 ≤ d)
    (sX : ℕ)
    (hCc : ∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
          (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
        (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
        ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N h (Cc c.slot.1 A))
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (hY : Y ∈ x.primitive.U)
    (t : ℝ) (ht : (D.cellScaleSq G.level)⁻¹ * t ∈ Icc x.primitive.a x.primitive.b) :
    fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
      (weakStageNativeInheritedLiftData π c hKD Y)
      (Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1
        (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))) n t)
      d word (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) =
    -(D.κ D.term * D.eps G.level ^ (n - 2) *
      D.eps (G.level - 1) ^ ((d : ℝ) - (n : ℝ))) •
      E.field x (Fin.last h) 0 ((D.cellScaleSq G.level)⁻¹ * t) 0 Y := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hY' := hY
  rw [hx.carrier] at hY'
  have hc := actualIndependentCoarsePath_isLiftSequenceOn_effective_order π c K hKD hK
    sX sZ N h hNK Cc hCc _ hY'.1.1.1
  rw [← hx.left, ← hx.right] at hc
  apply weakData_pathMeanFlux_produced_coefficient D hΛ₁ hζ hband G.level hweak E x
    hNK hBG hBV hB Y hY (actualIndependentCoarseStoredCarrier D c.chain.1 bw)
    (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P))
    hx.coefficients hY'.1.1.1 _ (weakStageNativeInheritedLiftData π c hKD Y) sX sZ hc
    (weakData_family_contrast D hΛ₁ hζ hband G.level hweak c.slot.1 _ _ _)
    hx.drift.symm hK₁ hn hhpos (Nat.sub_le_sub_right hd 1) _
    (Construction.Stream.ocEpsilon_pos hΛ₁) t ht _
    (inv_smul_smul₀ (show D.eps (G.level - 1) ≠ 0 from (Construction.Stream.ocEpsilon_pos hΛ₁).ne') _)
    (hx.native_metric hχ _ Y hY _ ht)
    (hx.native_edges hq hΛ hζ hband hweak.le hB Y hY _) hd₁

theorem weakStageInheritedMean_full_native_copy
    (S : IndependentWeakStageFluxProduction G minBase cap Hstage B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (π : StagePath G h)
    (hKD : K ≤ Dm) (hK : G.maxOrderBound K)
    (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates c.chain.1.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (word : DerivativeWord2 (d - 1))
    (E : IndependentInheritedMeanNaturalOutput (Fin (h + 1)) (4 * c.chain.1.children.length)
      H K N h 1 sZ h n (d - 1) word BG BV B C)
    (x : IndependentInheritedMeanInput (Fin (h + 1)) (4 * c.chain.1.children.length)
      H K N h 1 sZ BG BV B)
    (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < G.level)
    (hNK : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B)
    (hK₁ : 1 ≤ K) (hn : 2 ≤ n) (hnK : n ≤ K) (hhpos : h ≠ 0) (hd : d ≤ n) (hd₁ : 1 ≤ d)
    (sX : ℕ)
    (hCc : ∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
          (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
        (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
        ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N h (Cc c.slot.1 A))
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (hY : Y ∈ x.primitive.U)
    (hYnative : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw
      (D.eps (G.level - 1)) j₀ G.level c.slot.1)
    (t : ℝ) (ht : (D.cellScaleSq G.level)⁻¹ * t ∈ Icc x.primitive.a x.primitive.b) :
    fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
      (familyLiftData D G.level c.slot.1 (c.atParameter Y hYnative).1
        (D.eps (G.level - 1)) (pathEdges G π c.slot (c.atParameter Y hYnative)))
      (Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1
        (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))) n t)
      d word (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) =
    -(D.κ D.term * D.eps G.level ^ (n - 2) *
      D.eps (G.level - 1) ^ ((d : ℝ) - (n : ℝ))) •
      E.field x (Fin.last h) 0 ((D.cellScaleSq G.level)⁻¹ * t) 0 Y := by
  have hcopy := weakStageInheritedMean_physical_native_copy S c π hKD hK χ hχ Cc word E x hx
    hq hΛ hζ hband hweak hNK hBG hBV hB hK₁ hn hhpos hd hd₁ sX hCc Y hY t ht
  unfold weakStageNativeInheritedLiftData at hcopy
  rw [actualIndependentCoarsePathEdges_native π c _ hYnative.1.1.1] at hcopy
  rw [weakPath_pathMeanFlux_effective_order G K hKD hK π c.slot (c.atParameter Y hYnative)
    (D.eps (G.level - 1)) _ n hnK t]
  exact hcopy

end AVRegularity.EntryWeakProofs
end
end

section
/-! An actual inherited mean respects reference geometry on the whole fixed slow ball. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem independentIntrinsicParameterPacking_add_slow (r : ℕ) (X W : Vec 2) (P : Vec r) :
    independentIntrinsicSlowEmbedding r W + independentIntrinsicParameterPacking r X P =
      independentIntrinsicParameterPacking r (W + X) P := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Pi.add_apply, independentIntrinsicSlowEmbedding, independentIntrinsicParameterPacking,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.addCases_left,
      Fin.addCases_right, zero_apply, zero_add]

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The common inherited producer respects geometry across different actual context charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N h sZ n m : ℕ}
  {BG BV B C : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakStageEddyMean_cross_reference_geometry
    {level : ℕ}
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (ψ : Vec (2 + 4 * c'.chain.1.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates c.chain.1.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (hψ : ∀ Y, ‖independentFreshCarrierCoordinates c'.chain.1.children.length Y‖ < 1 / 4 →
      ψ =ᶠ[𝓝 Y] fun _ => 1)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (word : DerivativeWord2 m)
    (E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0)
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * c.chain.1.children.length)
      H N N 0 0 sZ BG BV 0)
    (y : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * c'.chain.1.children.length)
      H N N 0 0 sZ BG BV 0)
    (hx : WeakStageEddyPrimitiveRealization c χ Cc x)
    (hy : WeakStageEddyPrimitiveRealization c' ψ Cc y)
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (t : ℝ) (z : Vec 2) :
    E.field ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩ x n hn hnN m hm word 0 0 t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      E.field ⟨c'.chain.1.children.length, Nat.lt_succ_of_le c'.depth_bound⟩ y n hn hnN m hm word 0 0 t z
        (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  let Y := independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P
  let Z := independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q
  let V : Set (Vec 2) := {W | ‖W + X‖ < 1 / 8}
  have hV : IsOpen V := isOpen_lt (continuous_id.add continuous_const).norm continuous_const
  have hzeroV : (0 : Vec 2) ∈ V := by simpa only [V, Set.mem_ofPred_eq, zero_add] using hX
  have hcarrier (r : ℕ) (W : Vec (4 * r))
      (hW : ∀ j, ‖independentFreshChildProjection j false W‖ ≤ 3 / 16) :
      ‖independentFreshCarrierCoordinates r (independentIntrinsicParameterPacking (4 * r) X W)‖ < 1 / 4 := by
    apply lt_of_le_of_lt (independentFreshCarrierCoordinates_norm_le_of_bounds r _ (3 / 16)
      (by norm_num) ?_ ?_) (by norm_num)
    · simpa only [independentIntrinsicParameterPacking_stored] using hW
    · rw [independentIntrinsicParameterPacking_slow]
      exact hX.le.trans (by norm_num)
  have ha : x.data.primitive.a = y.data.primitive.a := by
    rw [hx.left, hy.left, hslot]
  have hb : x.data.primitive.b = y.data.primitive.b := by
    rw [hx.right, hy.right, hslot]
  have hv : x.data.primitive.v = y.data.primitive.v := by rw [hx.drift, hy.drift, hslot]
  have hM : x.data.primitive.M = y.data.primitive.M := hx.matrix.trans hy.matrix.symm
  have hedge : x.data.primitive.edge = y.data.primitive.edge := hx.edge.trans hy.edge.symm
  have hg := hgeom
  rw [actualIndependentCoarseParameterChain_eq_fresh D c.chain.1 c.chain.2.2.2.1,
    actualIndependentCoarseParameterChain_eq_fresh D c'.chain.1 c'.chain.2.2.2.1] at hg
  obtain ⟨W, hW, hzeroW, hmetric⟩ := independentFreshExtendedMetric_equalDepth_geometry_germ
    c.chain.1.children.length c'.chain.1.children.length hdepth D level
    (independentFreshBaseChain c.chain.1) (independentFreshBaseChain c'.chain.1)
    (independentFreshBaseChain_wellSlotted _) (independentFreshBaseChain_wellSlotted _)
    (fun j => realChainSlotSeq c.chain.1 (j + 1)) (fun j => realChainSlotSeq c'.chain.1 (j + 1))
    (independentFreshCoarseBirthLength D c.chain.1) (independentFreshCoarseBirthLength D c'.chain.1)
    (D.eps (level - 1)) x.data.primitive.a x.data.primitive.b Y Z
    (by simpa only [Y, Z, independentIntrinsicParameterPacking_stored] using hg)
    (by simp only [Y, Z, independentIntrinsicParameterPacking_slow]) χ ψ
    (hχ Y (hcarrier _ P hP)) (hψ Z (hcarrier _ Q hQ))
  have hGx := hx.metric
  change x.data.primitive.G = clampedParameterMetric
    (cutoffParameterMetric χ (independentFreshNativeMetric D c.chain.1.ctxLevel
      (independentFreshBaseChain c.chain.1) (fun j => realChainSlotSeq c.chain.1 (j + 1))
      (independentFreshCoarseBirthLength D c.chain.1) (D.eps (level - 1))))
    x.data.primitive.a x.data.primitive.b at hGx
  rw [c.chain.2.1] at hGx
  have hGy := hy.metric
  change y.data.primitive.G = clampedParameterMetric
    (cutoffParameterMetric ψ (independentFreshNativeMetric D c'.chain.1.ctxLevel
      (independentFreshBaseChain c'.chain.1) (fun j => realChainSlotSeq c'.chain.1 (j + 1))
      (independentFreshCoarseBirthLength D c'.chain.1) (D.eps (level - 1))))
    y.data.primitive.a y.data.primitive.b at hGy
  rw [c'.chain.2.1, ← ha, ← hb] at hGy
  have he : IndependentLiftHeterogeneousSliceEq x.data.primitive y.data.primitive (W ∩ V) Y Z := by
    refine ⟨ha, hb, hv, hM, hedge, ?_, ?_⟩
    · intro i j tt A hA _zz
      rw [hGx, hGy]
      exact hmetric i j tt A hA.1
    · intro v u e γ hγ
      rw [hx.edge] at hγ
      exact (List.not_mem_nil hγ).elim
  have hmean := independentEddy_equalDepth_cross E
    ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩
    ⟨c'.chain.1.children.length, Nat.lt_succ_of_le c'.depth_bound⟩ hdepth x y
    (W ∩ V) Y Z (hW.inter hV) ⟨hzeroW, hzeroV⟩ (hx.response.trans hy.response.symm) he
    n hn hnN m hm word 0 0
  simpa only [map_zero, zero_add] using hmean t 0 ⟨hzeroW, hzeroV⟩ z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Whole reference-ball naturality of the positive-response physical array. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}
  {E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem geometry (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (n : Finset.Icc 2 (N + 1)) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (t : ℝ) (z : Vec 2) :
    F.array c n d word t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      F.array c' n d word t z (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  by_cases hd : d ∈ Finset.Icc 2 n.val
  · have he (cc : WeakStageProductionContext D bw j₀ level minBase cap) :
        F.array cc n d word = independentProducedFluxSource
          (D.κ D.term * D.eps level ^ (n.val - 2) *
            D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)))
          (fun tt => (D.cellScaleSq level)⁻¹ * tt)
          (fun tt _ W => E.field ⟨cc.chain.1.children.length, Nat.lt_succ_of_le cc.depth_bound⟩
            (F.datum cc) (n.val - 1) (by have := (Finset.mem_Icc.mp n.property).1; omega)
            (by have := (Finset.mem_Icc.mp n.property).2; omega) (d - 1)
            (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) word 0 0 tt 0 W) := by
      unfold array weakEddyPhysicalArray
      exact dite_eq_left hd
    rw [he c, he c']
    have hmean := weakStageEddyMean_cross_reference_geometry c c' hslot hdepth
      (χ c.chain.1.children.length) (χ c'.chain.1.children.length) (hχ _) (hχ _) Cc word E
      (F.datum c) (F.datum c') (F.realization c) (F.realization c') P Q hP hQ hgeom X hX
      (n.val - 1) (by have := (Finset.mem_Icc.mp n.property).1; omega)
      (by have := (Finset.mem_Icc.mp n.property).2; omega)
      (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) ((D.cellScaleSq level)⁻¹ * t) 0
    exact congrArg (fun w : Vec 2 =>
      -(D.κ D.term * D.eps level ^ (n.val - 2) *
        D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ))) • w) hmean
  · have he (cc : WeakStageProductionContext D bw j₀ level minBase cap) :
        F.array cc n d word = fun _ _ _ => 0 := by
      unfold array weakEddyPhysicalArray
      exact dite_eq_right hd
    rw [he c, he c']


end AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
end
end

section
/-! The actual Eddy array copies the original zero-edge mean flux. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}
  {E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem toMeanArrayProduction (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hbw : bw ≤ 1 / 10000)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < level)
    (Dm sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A, IsAdmissibleChain D bw j₀ level p.1 A →
      IsLiftSequence (familyLiftData (Dm := Dm) D level p.1 A (D.eps (level - 1))
        (fun _ _ _ => [])) sX sZ (D.slotStart level p.1 / D.cellScaleSq level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)
        N 0 (Cc p.1 A))
    (n : Finset.Icc 2 (N + 1)) :
    Nonempty (IndependentWeakMeanArrayProduction D bw j₀ level minBase cap H n.val
      (D.weakPe level ^ 2) E.budget
      (fun p A d word t => fluxCoeff (weakEddyFlux D level (D.eps (level - 1))
        (familyLiftData (Dm := Dm) D level p.1 A.1 (D.eps (level - 1)) (fun _ _ _ => []))
        (Cc p.1 A.1) n.val t) d word 0)) := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ hband D.term).le
  have hp c d word := F.production hκ (fun _ => Construction.Stream.ocEpsilon_pos hΛ₁) c n d word
  choose Q hQ hphase using hp
  refine ⟨{ field := fun c => F.array c n
            reserve := Q
            budget := hQ
            phase := hphase
            geometry := ?_
            native_copy := ?_ }⟩
  · intro c c' hslot hdepth d word W Z hW hZ hgeom X hX t z
    exact F.geometry hχ c c' hslot hdepth n d word W Z hW hZ hgeom X hX t z
  · intro c d word hd hdn t htime z
    exact (F.native_anchor_copy hq hΛ hζ hbw hband hweak Dm sX hCc
      c n d (Finset.mem_Icc.mpr ⟨hd, hdn⟩) word t htime z).symm

end AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
end
end
end
