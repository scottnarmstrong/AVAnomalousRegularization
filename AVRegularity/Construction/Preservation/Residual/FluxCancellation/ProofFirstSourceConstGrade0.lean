-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseSum
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredCoeff
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Mean

section
section
/-! **The jet-locality step, Eulerian flux of one pulse**.

`pulseMeanFluxEuler` is the sum over `k` of the Jacobian entry `∂_k chart_j (label t y)` times
`-(c⁻¹ ε_c^n ρ)` times the cell mean of `liftFluxX` of the field
`b(s', X') = a (c s') (chart (c s') (ρ X'))` at `X' = ρ⁻¹ label t y`. At the time `c⁻¹ t` the field
is `a t ∘ chart t ∘ (ρ •)`, whose jets at `X₀ = ρ⁻¹ label t x` are those of `a t` at
`chart t (label t x) = x` (the hypothesis `hid`, `flow_chart_label` for the flow charts), by
`sameJet_comp`. Then the `liftFluxX` and cell-mean jet statements, composition with the label, and the
Jacobian factor. For `ρ = 0` the flux is `0`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- The Eulerian flux of one pulse at finite regularity. -/
theorem pulse_sameJet : PulseStatement := by
  intro ι _ h _ _ _ Dm c ρ εc n r Q Cc chart label a₁ a₂ t v s N H x hc hDm hrH hz hb hG hv hedge
    ha₁ ha₂ hj hchart hlabel hid
  have hcd : ∀ a : ℝ → Vec 2 → ∀ i, h i, ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t) →
      ContDiff ℝ (s : ℕ∞) (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a t y v) :=
    fun a ha => CovFluxReg.pulseMeanFluxEuler_contDiff c ρ εc n r Q Cc chart label a t v s N H
      hc hDm hrH hz hb hG hv hedge ha hchart hlabel
  refine ⟨hcd a₁ ha₁, hcd a₂ ha₂, ?_⟩
  by_cases hρ : ρ = 0
  · have : (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₁ t y v) =
        (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₂ t y v) := by
      funext y
      unfold pulseMeanFluxEuler
      simp [hρ]
    rw [this]
    exact fun _ _ _ => rfl
  -- the lifted fields at the pulse clock
  have hclk : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  set b₁ : ℝ → Vec 2 → ∀ i, h i := fun s' X' => a₁ (c * s') (chart (c * s') (ρ • X')) with hb₁
  set b₂ : ℝ → Vec 2 → ∀ i, h i := fun s' X' => a₂ (c * s') (chart (c * s') (ρ • X')) with hb₂
  have hbt : ∀ a : ℝ → Vec 2 → ∀ i, h i, (fun s' X' => a (c * s') (chart (c * s') (ρ • X')))
      (c⁻¹ * t) = fun X' => a t (chart t (ρ • X')) := by
    intro a
    funext X'
    show a (c * (c⁻¹ * t)) (chart (c * (c⁻¹ * t)) (ρ • X')) = _
    rw [hclk]
  have hφ : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (fun X' : Vec 2 => chart t (ρ • X')) :=
    hchart.comp (contDiff_const_smul ρ)
  have hX₀ : (fun X' : Vec 2 => chart t (ρ • X')) (ρ⁻¹ • label t x) = x := by
    show chart t (ρ • ρ⁻¹ • label t x) = x
    rw [smul_inv_smul₀ hρ, hid]
  have hX₀' : chart t (ρ • ρ⁻¹ • label t x) = x := hX₀
  have hb₁c : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (b₁ (c⁻¹ * t)) := by
    rw [hb₁, hbt]; exact ha₁.comp hφ
  have hb₂c : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (b₂ (c⁻¹ * t)) := by
    rw [hb₂, hbt]; exact ha₂.comp hφ
  have hbj : SameJetAt (s + Dm + N) (ρ⁻¹ • label t x) (b₁ (c⁻¹ * t)) (b₂ (c⁻¹ * t)) := by
    rw [hb₁, hb₂, hbt, hbt]
    exact sameJet_comp _ _ _ _ _ hφ ha₁ ha₂ (by show SameJetAt _ (chart t (ρ • ρ⁻¹ • label t x)) _ _; rw [hX₀']; exact hj)
  -- the cell mean of the lifted flux, one coordinate
  have hk : ∀ k : Fin 2, Triple s (ρ⁻¹ • label t x)
      (fun X => fieldCellMean (fun z => liftFluxX Q Cc b₁ r n (c⁻¹ * t) X z k))
      (fun X => fieldCellMean (fun z => liftFluxX Q Cc b₂ r n (c⁻¹ * t) X z k)) := by
    intro k
    have hW : ∀ (b : ℝ → Vec 2 → ∀ i, h i), ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (b (c⁻¹ * t)) →
        ContDiff ℝ (s : ℕ∞) (Function.uncurry fun X z => liftFluxX Q Cc b r n (c⁻¹ * t) X z k) :=
      fun b hbc => (CovFluxReg.liftFluxX_box Q Cc b r n (c⁻¹ * t) k s N H hDm hrH hz hb
        (hG k) (hv k) hedge hbc).contDiff_uncurry le_rfl le_rfl
    have hM : ∀ (b : ℝ → Vec 2 → ∀ i, h i), ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (b (c⁻¹ * t)) →
        ContDiff ℝ (s : ℕ∞) (fun X => fieldCellMean (fun z => liftFluxX Q Cc b r n (c⁻¹ * t) X z k)) :=
      fun b hbc => AVRegularity.Providers.PathDecomp.contDiff_fieldCellMean (hW b hbc)
    exact ⟨hM b₁ hb₁c, hM b₂ hb₂c, cellMean_sameJet s _ _ _ (hW b₁ hb₁c) (hW b₂ hb₂c)
      (liftFlux_sameJet Q Cc b₁ b₂ r n (c⁻¹ * t) k s N H _ hDm hrH hz hb (hG k) (hv k) hedge
        hb₁c hb₂c hbj)⟩
  have hjc : ∀ k : Fin 2, Triple s x
      (fun y => fieldCellMean (fun z => liftFluxX Q Cc b₁ r n (c⁻¹ * t) (ρ⁻¹ • label t y) z k) v)
      (fun y => fieldCellMean (fun z => liftFluxX Q Cc b₂ r n (c⁻¹ * t) (ρ⁻¹ • label t y) z k) v) := by
    intro k
    have hlab : ContDiff ℝ (s : ℕ∞) (fun y => ρ⁻¹ • label t y) := hlabel.const_smul ρ⁻¹
    have hcomp := sameJet_comp x s (fun y => ρ⁻¹ • label t y) _ _ hlab (hk k).1 (hk k).2.1
      (hk k).2.2
    have hpv := ContinuousLinearMap.proj (R := ℝ) (φ := h) v
    refine ⟨(contDiff_pi.1 ((hk k).1.comp hlab)) v, (contDiff_pi.1 ((hk k).2.1.comp hlab)) v, ?_⟩
    exact sameJet_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) ((hk k).1.comp hlab)
      ((hk k).2.1.comp hlab) hcomp
  have hchart1 : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) (chart t) :=
    hchart.of_le (by exact_mod_cast (by omega : s + 1 ≤ s + Dm + N))
  have hfin : ∀ j : Fin 2, Triple s x
      (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₁ t y v j)
      (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₂ t y v j) := by
    intro j
    unfold pulseMeanFluxEuler
    refine triple_sum _ fun k _ => triple_mul
      (CovFluxReg.jacMatrix_entry_contDiff hchart1 hlabel j k) ?_
    exact triple_smul _ (hjc k)
  exact sameJet_pi (h := fun _ : Fin 2 => h v) (fun j => (hfin j).1) (fun j => (hfin j).2.1)
    (fun j => (hfin j).2.2)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step, conclusion**: `menuMeanFluxJet : MenuMeanFluxJetStatement` and
`covMeanJet : CovMeanJetStatement`. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- Jet locality of the menu mean flux. -/
theorem menuMeanFluxJet : MenuMeanFluxJetStatement :=
  menuMeanFluxJet_of_pulse pulse_sameJet

/-- **The jet-locality step**: jet locality of the covariance mean at finite regularity. -/
theorem covMeanJet : CovMeanJetStatement :=
  covMeanJet_of_steps covPolyPJet covPolyQJet menuMeanFluxJet

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, jet locality of the label operator, layer 1: one pushed label flux.

The push-forward by a chart `Ψ` (inverse `Ψinv`) of the grade-zero path mean flux of a scalar
family is the Eulerian pulse flux `pulseMeanFluxEuler` of that family on `Fin 1`, with the constant
chart `Ψ` and label `Ψinv` (`fsj_push_eq_pulse`: the two definitions agree term by term). The
equal-jet statement of the pulse flux (`pulse_sameJet`) then gives: for the chart of a
well-slotted chain `B`, two fields of class `C^{s + Dm + N}` with the same jets of that order at
`x` have pushed label fluxes of class `C^s` with the same jets of order `s` at `x`
(`fsj_push_triple`).

For `ρ = 0` the flux vanishes, and for `s = 0` only values are compared. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- **The pushed grade-zero label flux is a pulse flux on `Fin 1`.** -/
theorem fsj_push_eq_pulse (D : OCData) {Dm : ℕ} (m : ℕ) (ρ : ℝ)
    (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (Ψ Ψinv : Vec 2 → Vec 2)
    (f : Vec 2 → ℝ) (x : Vec 2) :
    pushFlux Ψ Ψinv (pathMeanFlux (h := 0) D m ρ Q Cc n t) f x =
      pulseMeanFluxEuler (D.cellScaleSq m) ρ (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ)
        n 0 Q Cc (fun _ => Ψ) (fun _ => Ψinv) (fun _ y _ => f y) t x 0 := by
  funext j
  have hfield : (fun (_ : ℝ) (X : Vec 2) =>
      (Pi.single (0 : Fin (0 + 1)) ((f ∘ Ψ) (ρ • X)) : Fin (0 + 1) → ℝ)) =
      fun _ X _ => f (Ψ (ρ • X)) := by
    funext _ X i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    simp
  unfold pushFlux pathMeanFlux pulseMeanFluxEuler
  simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
  rw [hfield]
  rfl

/-- **One pushed label flux at finite regularity.** -/
theorem fsj_push_triple {Dm : ℕ} (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) {k : ℤ}
    (hk : Odd k) (ρ : ℝ) (B : RealChain) (hB : B.slots.length = B.children.length + 1)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (s N : ℕ)
    (hDm : 1 ≤ Dm) (hc : D.cellScaleSq m ≠ 0)
    (hz : ∀ n', N < n' → ∀ m' α τ X z v u, Cc0 k B 0 n' m' α τ X z v u = 0)
    (hbox : ∀ n' m' α v u, IsBoxSmooth (s + Dm) (s + Dm)
      (fun X z => Cc0 k B 0 n' m' α ((D.cellScaleSq m)⁻¹ * t) X z v u))
    (x : Vec 2) (f₁ f₂ : Vec 2 → ℝ) (hf₁ : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) f₁)
    (hf₂ : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) f₂) (hj : SameJetAt (s + Dm + N) x f₁ f₂) :
    Triple s x
      (fun y => pushFlux (B.famMap D t) (B.famMapInv D t) (diagLabelFlux D Dm m ρ Cc0 k B n t) f₁ y)
      (fun y => pushFlux (B.famMap D t) (B.famMapInv D t)
        (diagLabelFlux D Dm m ρ Cc0 k B n t) f₂ y) := by
  have hpi : ∀ f : Vec 2 → ℝ, ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) f →
      ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (fun y (_ : Fin 1) => f y) := fun f hf =>
    contDiff_pi.2 fun _ => hf
  have hjj : SameJetAt (s + Dm + N) x (fun y (_ : Fin 1) => f₁ y) (fun y (_ : Fin 1) => f₂ y) :=
    sameJet_pi (h := fun _ : Fin 1 => ℝ) (fun _ => hf₁) (fun _ => hf₂) (fun _ => hj)
  have key := pulse_sameJet (D.cellScaleSq m) ρ
    (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) n 0
    (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k B ρ (fun _ _ _ => [])) (Cc0 k B)
    (fun _ => B.famMap D t) (fun _ => B.famMapInv D t) (fun _ y _ => f₁ y) (fun _ y _ => f₂ y) t
    (0 : Fin 1) s N 0 x hc hDm le_rfl
    (fun hh' hh n' hn' m' α τ X z v u => by
      have h0 : hh' = 0 := Nat.le_zero.mp hh
      subst h0
      exact hz n' hn' m' α τ X z v u)
    (fun hh' hh n' m' α v u => by
      have h0 : hh' = 0 := Nat.le_zero.mp hh
      subst h0
      exact hbox n' m' α v u)
    (fun k' j => (EntryWeakProofs.familyLiftData_metric_entry_smooth D m k B hB ρ _ _ k' j).of_le
      (by exact_mod_cast le_top))
    (fun k' => (CovFluxReg.ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ m (D.kap m) hk _ k').of_le
      (by exact_mod_cast le_top))
    (fun h0 => absurd rfl h0) (hpi f₁ hf₁) (hpi f₂ hf₂) hjj
    ((Providers.GenSem.contDiff_famMap B t).of_le (by exact_mod_cast le_top))
    ((Providers.GenSem.contDiff_famMapInv B t).of_le (by exact_mod_cast le_top))
    (Providers.GenSem.famMap_famMapInv hζ B t x)
  exact triple_congr
    (fun y => (fsj_push_eq_pulse D m ρ _ (Cc0 k B) n t _ _ f₁ y).symm)
    (fun y => (fsj_push_eq_pulse D m ρ _ (Cc0 k B) n t _ _ f₂ y).symm) key

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The path-sum step at positive grades: the setting of the path decomposition on the native chain of
an odd pulse, from the hypotheses of the piece.

* `hl_ladder_univ`: the ladder of the native chain is all of `ℝ²`
  (`isAdmissibleChain_nativeChain_recenter`), so the localized lift relation of the path families
  is the global one.
* `HLZeroLift`, `hlLifts`: the lift of the empty path (the scalar lift with no edge, not among the
  hypotheses of the piece, which start at one edge) and the family of all path lifts.
* `hl_setting`: `HLDecomp.Setting` on the native chain, from `Input`, `ActualFluxJointSmooth`, the
  floors, the path lifts on the ladder and a lift of the empty path.
* `hl_decomposed_of_two_le`: the decomposition `HLDecomp.Decomposed` for `2 ≤ Dm`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

open CovarianceTransport CovFluxReg
open AVRegularity.Providers.PathDecomp

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The ladder of the native chain of an odd pulse is all of `ℝ²`. -/
theorem hl_ladder_univ {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) {k : ℤ} (hk : Odd k) (ρ : ℝ) :
    ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ = Set.univ := by
  have hl := hin.level
  refine Set.eq_univ_of_forall fun X => ?_
  exact Providers.QuietAtlas.isAdmissibleChain_nativeChain_recenter (D := D) (b := b) (j₀ := j₀)
    (by omega) (by omega) ⟨k, hk⟩ (ρ • X)

/-- A lift of the empty path on the native chain of the pulse `k`: a grade-zero lift sequence of
the scalar operator data with no edge. -/
def HLZeroLift (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (ρ : ℝ) (k : ℤ)
    (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : Prop :=
  IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k
      (nativeChain G.level k) ρ (fun _ _ _ => []))
    Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0 C0

/-- The path lifts of every length: `C0` on the empty path, the given ones on the others. -/
def hlLifts {G : GenStage D hr Dm b j₀} (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) :
    ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)
  | 0, _ => C0
  | h' + 1, π => Cπ (h' + 1) π

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The native context of the pulse `k` is the actual one. -/
theorem hl_native_ctx {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)) :
    (⟨nativeChain G.level k, hadm⟩ : StageCtx D b j₀ G.level ⟨k, hk⟩) = G.actual ⟨k, hk⟩ :=
  Subtype.ext (hin.natural.2.2.1 ⟨k, hk⟩).symm

/-- **The setting of the path decomposition on the native chain.** -/
theorem hl_setting {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G)
    (hsX : Mn.N + Dm + 2 ≤ Mn.sX) (hsZ : Mn.N + Dm + 2 ≤ Mn.sZ) (ρ : ℝ) {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hne : (HLWindow D G k).Nonempty) (g : ℕ)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : HLPathLifts Mn G ρ k hk hadm g Cπ)
    (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (hC0 : HLZeroLift Mn G ρ k C0) :
    HLDecomp.Setting G G.level k (nativeChain G.level k) ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      (g + 1) Mn.N Mn.sX Mn.sZ (hlLifts C0 Cπ) := by
  classical
  have hζ := hin.profile
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.base hin.profile hin.band G.level
  have hnat := hl_native_ctx hin hk hadm
  obtain ⟨τ₀, hτ₀⟩ := hne
  refine ⟨hτ₀.1.trans hτ₀.2, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · intro X'
    obtain ⟨lo, hi, hlo, he⟩ := Providers.GenSem.familyLiftData_pos_window D hζ G.level k
      (nativeChain G.level k) ρ (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) X'
    obtain ⟨Mv, hMv⟩ := Providers.GenSem.familyLiftData_v_bounded D hζ G.level hk
      (nativeChain G.level k) ρ (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)
    exact ⟨lo, hi, Mv, AVRegularity.Uniqueness.windowData_of_elliptic _ _ _ _ lo hi Mv
      (fun t => Providers.GenSem.familyLiftData_symm D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩) t X' 0 1)
      hlo he (fun t _ z => hMv t z)⟩
  · intro t _ i j
    exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k (nativeChain G.level k)
      rfl ρ (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩) t i j).of_le
      (by exact_mod_cast le_top)
  · intro t _ κ
    refine ⟨?_, fun X n x => ?_⟩
    · exact ((hl_familyLiftData_drift_smooth D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩) t κ).of_le
        (by exact_mod_cast le_top)).comp contDiff_snd
    · exact congrFun (Providers.GenSem.ocPulseCellDrift_periodic G.level (D.kap G.level) hk t n x) κ
  · intro v u γ t ht d α κ
    have hw := hl_window_mem G k hc ht
    by_cases hdD : d ≤ Dm
    · have h1 := hE ⟨k, hk⟩ v u γ d α _ hw (Mn.N + 1 + Dm)
      rw [← hnat] at h1
      have hg : GoodField (Mn.N + 1 + Dm) (fun X z =>
          G.fam.flux ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩ v u γ d α (D.cellScaleSq G.level * t)
            ((ρ / D.eps (G.level - 1)) • X) z κ) := by
        refine ⟨?_, fun X n x => ?_⟩
        · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ).contDiff.comp
            (h1.comp ((contDiff_fst.const_smul (ρ / D.eps (G.level - 1))).prodMk contDiff_snd))
        · simp only
          rw [G.fam.flux_periodic ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩ v u γ d α
            (D.cellScaleSq G.level * t) ((ρ / D.eps (G.level - 1)) • X) n x]
      exact hg.congr fun X z => by simp [stageDat, hdD]
    · exact GoodField.zero.congr fun X z => by simp [stageDat, hdD]
  · intro h' hh' σ
    cases h' with
    | zero =>
        have he : pathEdges G σ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩ = fun _ _ _ => [] := by
          funext v u d
          simp [pathEdges]
        show IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) ρ
          (pathEdges G σ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) Mn.sX Mn.sZ _ _ Mn.N 0 C0
        rw [he]
        exact hC0
    | succ h'' =>
        refine WeakEntryProofs.liftSequence_of_on_univ _ _ _ _ _ _ _ _ ?_
        rw [← hl_ladder_univ hin hk ρ]
        exact hπ (h'' + 1) (by omega) hh' σ

/-- The Hilbert lift of the piece, read at the native context and restricted to `g + 1` grades. -/
theorem hl_hilbert_native {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (ρ : ℝ) {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)} {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hlift : HLHilbertLift Mn G ρ depth k hk CcT) {g : ℕ} (hd : g ≤ depth) :
    IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N g
      (CcT k) := by
  rw [hl_native_ctx hin hk hadm]
  exact IsLiftSequence.restrict hlift hd

/-- **The decomposition on the native chain, for `2 ≤ Dm`.** -/
theorem hl_decomposed_of_two_le {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G)
    (hsX : Mn.N + Dm + 2 ≤ Mn.sX) (hsZ : Mn.N + Dm + 2 ≤ Mn.sZ) (ρ : ℝ) {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)} {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hlift : HLHilbertLift Mn G ρ depth k hk CcT)
    (hne : (HLWindow D G k).Nonempty) {g : ℕ} (hd : g + 1 ≤ depth)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : HLPathLifts Mn G ρ k hk hadm g Cπ)
    (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (hC0 : HLZeroLift Mn G ρ k C0)
    (hD2 : 2 ≤ Dm) :
    HLDecomp.Decomposed G G.level ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      (g + 1) (CcT k) (hlLifts C0 Cπ) :=
  (hl_setting hin hE hsX hsZ ρ hk hadm hne g Cπ hπ C0 hC0).decomposed hD2
    (hl_hilbert_native hin ρ hk hadm hlift hd)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, jet locality of the label operator, layer 2: the assembled diagonal flux.

For grade-zero lifts `Cc0` satisfying `IsDiagLifts` with box orders `s + Dm ≤ sX, sZ`, and two
fields of class `C^{s + Dm + N}` with the same jets of that order at `x`:

* `fsj_diagMean_triple`: `diagMeanFluxCtx … n f_i` are of class `C^s` with the same jets of order
  `s` at `x` (finite sum over the scheduled slots; a child off the carrier or a vanishing cut-off
  contributes zero; otherwise `fsj_push_triple`);
* `fsj_diagFlux_triple`: the same for `diagFluxCtx` (the reference term `𝖩_m ∇f` loses one
  derivative, `1 ≤ Dm`).

With no scheduled slot only the reference term remains. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The assembled mean flux as a finite sum over the scheduled slots. -/
theorem fsj_diagMean_eq_sum (D : OCData) (m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (t : ℝ) (ch : RealChain)
    (ζ : Vec 2) (n : ℕ) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot) (f : Vec 2 → ℝ) (x : Vec 2) :
    diagMeanFluxCtx D b j₀ Dm m ρ Cc0 t ch ζ n f x =
      ∑ k ∈ S, (if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
        ocCutoff D.α D.q D.Λ m k t • pushFlux ((ch.appendChild D k t ζ).famMap D t)
          ((ch.appendChild D k t ζ).famMapInv D t)
          (diagLabelFlux D Dm m ρ Cc0 k (ch.appendChild D k t ζ) n t) f x else 0) := by
  have hfin : {k : ℤ | Odd k ∧ IsScheduledIn D (m - 1) k ch.slot} = (S : Set ℤ) := by
    ext k; simp [hS k]
  unfold diagMeanFluxCtx
  rw [← finsum_mem_coe_finset]
  refine finsum_congr fun k => ?_
  rw [show (k ∈ (S : Set ℤ)) = (Odd k ∧ IsScheduledIn D (m - 1) k ch.slot) from by
    rw [← hfin]; rfl]

/-- The zero triple. -/
theorem fsj_triple_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℕ) (x : Vec 2) :
    Triple s x (fun _ => (0 : E)) (fun _ => (0 : E)) :=
  ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩

/-- **The assembled mean flux of degree `n` at finite regularity.** -/
theorem fsj_diagMean_triple (D : OCData) (hζ : IsFastProfile D.ζ) (Mn : SuccMenu) (m : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (hDm : 1 ≤ Dm) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcc : 0 < D.cellScaleSq m) (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot) (n : ℕ) (x : Vec 2)
    (f₁ f₂ : Vec 2 → ℝ) (hf₁ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) f₁)
    (hf₂ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) f₂) (hj : SameJetAt (s + Dm + Mn.N) x f₁ f₂) :
    Triple s x
      (fun y => diagMeanFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Cc0 t ch ζ n f₁ y)
      (fun y => diagMeanFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Cc0 t ch ζ n f₂ y) := by
  classical
  refine triple_congr
    (fun y => (fsj_diagMean_eq_sum D m _ Cc0 t ch ζ n S hS f₁ y).symm)
    (fun y => (fsj_diagMean_eq_sum D m _ Cc0 t ch ζ n S hS f₂ y).symm) ?_
  refine triple_sum _ fun k hk => ?_
  by_cases hadm : IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ)
  · simp only [hadm, ↓reduceIte]
    by_cases hcut : ocCutoff D.α D.q D.Λ m k t = 0
    · simp only [hcut, zero_smul]
      exact fsj_triple_zero s x
    · have hodd : Odd k := ((hS k).1 hk).1
      have hseq := hdiag k _ hodd hadm
      have ht' := CovFluxReg.clock_mem_window D m k t hτ hcc hcut
      refine triple_smul _ (fsj_push_triple D hζ m hodd _ _ hadm.2.2.1 Cc0 n t s Mn.N hDm
        hcc.ne' (fun n' hn' m' α τ X z v u => hseq.2.2.1 0 le_rfl n' hn' m' α τ X z v u)
        (fun n' m' α v u => (hseq.2.2.2.2.2.1 0 le_rfl n' m' α v u _ ht').1.mono hsX hsZ)
        x f₁ f₂ hf₁ hf₂ hj)
  · simp only [hadm, ↓reduceIte]
    exact fsj_triple_zero s x

/-- The reference term `M ∇f` loses one derivative. -/
theorem fsj_ref_triple (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℕ) (x : Vec 2) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) f₁) (hf₂ : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) f₂)
    (hj : SameJetAt (s + 1) x f₁ f₂) :
    Triple s x (fun y => M.mulVec (gradField f₁ y)) (fun y => M.mulVec (gradField f₂ y)) := by
  have hg : ∀ f : Vec 2 → ℝ, ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) f →
      ContDiff ℝ (s : ℕ∞) (fun y => gradField f y) := fun f hf =>
    contDiff_pi.2 fun k => cd_partial hf k
  have hgj : SameJetAt s x (fun y => gradField f₁ y) (fun y => gradField f₂ y) :=
    sameJet_pi (h := fun _ : Fin 2 => ℝ) (fun k => cd_partial hf₁ k)
      (fun k => cd_partial hf₂ k) (fun k => (sameJet_succ_iff.1 hj).2 k)
  set L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
    with hL
  have hLv : ∀ v : Fin 2 → ℝ, M.mulVec v = L v := fun v => rfl
  simp only [hLv]
  exact ⟨L.contDiff.comp (hg f₁ hf₁), L.contDiff.comp (hg f₂ hf₂),
    sameJet_clm L (hg f₁ hf₁) (hg f₂ hf₂) hgj⟩

/-- **The assembled diagonal flux `𝓕_A` at finite regularity.** -/
theorem fsj_diagFlux_triple (D : OCData) (hζ : IsFastProfile D.ζ) (Mn : SuccMenu) (m : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (hDm : 1 ≤ Dm) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (hcc : 0 < D.cellScaleSq m) (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (m - 1) k ch.slot) (x : Vec 2)
    (f₁ f₂ : Vec 2 → ℝ) (hf₁ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) f₁)
    (hf₂ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) f₂) (hj : SameJetAt (s + Dm + Mn.N) x f₁ f₂) :
    Triple s x
      (fun y => diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ f₁ y)
      (fun y => diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ f₂ y) := by
  have hmean := fun n => fsj_diagMean_triple D hζ Mn m Cc0 hdiag hDm hτ hcc s hsX hsZ t ch ζ S hS n
    x f₁ f₂ hf₁ hf₂ hj
  have hle : s + 1 ≤ s + Dm + Mn.N := by omega
  have href := fsj_ref_triple (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t) s x f₁ f₂
    (cd_le hle hf₁) (cd_le hle hf₂) (sameJet_mono hle hj)
  unfold diagFluxCtx
  exact triple_add (triple_sub (hmean 2) href) (triple_sum _ fun n _ => hmean n)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Source mean: the letters as Eulerian operators**: the Eulerian operator `sourceEulerOp` of
each kind of source with the empty word, in terms of the dressed path terms and of the direct
parts on the native families.

* `sourceEulerOp_copyQuad`: the quadratic conversion is the dressed term of degree `2`,
  `a = a' = 0`;
* `sourceEulerOp_letterMean`: the letter `𝖬_{n,h}` is the dressed term of degree `n`, `a = a' = 0`,
  minus, for a one-edge path, the glue of the direct part of the order `n`;
* `sourceEulerOp_copyDir`: the direct transport is the glue of the direct parts of the orders
  `3..Dm`;
* `sourceEulerOp_letterCov`: the letter `𝖵_{n,h,a,a'}` is the dressed term of degree `n` and
  `(a, a')`. The letter is formed with the centred family map of the native chain,
  `h ↦ Ψ(h) - Ψ(0)`, `Ψ = X_{m-1}(t, ·, s_k)` the chart of the glue; the push by `Ψ` of the pull by
  the centred map is the conjugation by the translation by `Ψ(0)` (`pushFlux_pullFlux_centered`,
  the Jacobian of the flow has determinant `1`), and the covariance operator commutes with
  translations (`covOperator_iterate_translate`), for every field, with no regularity.

All four hold for every field and every lift family. For `a = a' = 0` the covariance
form is the mean form, and a pulse whose native chain is not admissible, or an even pulse, contributes
`0` on both sides. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Providers.QuietAtlas

/-! ### Translations and the covariance operator -/

section Translate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The covariance operator commutes with translations (no regularity needed). -/
theorem covOperator_translate (Hc : Matrix (Fin 2) (Fin 2) ℝ) (φ : Vec 2 → E) (c : Vec 2) :
    covOperator Hc (fun y => φ (y + c)) = fun y => covOperator Hc φ (y + c) := by
  funext x
  unfold covOperator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : (fun y => fderiv ℝ (fun y' => φ (y' + c)) y (basisVec j)) =
      fun y => fderiv ℝ φ (y + c) (basisVec j) := by
    funext y
    rw [fderiv_comp_add_right]
  have e2 : fderiv ℝ (fun y => fderiv ℝ φ (y + c) (basisVec j)) x =
      fderiv ℝ (fun y' => fderiv ℝ φ y' (basisVec j)) (x + c) :=
    fderiv_comp_add_right (f := fun y' => fderiv ℝ φ y' (basisVec j)) c
  rw [e, e2]

/-- The iterates of the covariance operator commute with translations. -/
theorem covOperator_iterate_translate (Hc : Matrix (Fin 2) (Fin 2) ℝ) (a : ℕ) (φ : Vec 2 → E)
    (c : Vec 2) :
    (covOperator Hc)^[a] (fun y => φ (y + c)) = fun y => (covOperator Hc)^[a] φ (y + c) := by
  induction a generalizing φ with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, covOperator_translate, ih]

end Translate

/-! ### Push and pull by a chart and by its centred form -/

/-- The Jacobian of a map minus a constant. -/
theorem jacMatrix_sub_const (Ψ : Vec 2 → Vec 2) (c y : Vec 2) :
    jacMatrix (fun h => Ψ h - c) y = jacMatrix Ψ y := by
  unfold jacMatrix
  rw [fderiv_sub_const]

theorem pushFlux_sub (Ψ Ψi : Vec 2 → Vec 2) (L₁ L₂ : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (f : Vec 2 → ℝ) (x : Vec 2) :
    pushFlux Ψ Ψi (fun f y => L₁ f y - L₂ f y) f x =
      pushFlux Ψ Ψi L₁ f x - pushFlux Ψ Ψi L₂ f x := by
  unfold pushFlux
  exact Matrix.mulVec_sub _ _ _

theorem pushFlux_zero (Ψ Ψi : Vec 2 → Vec 2) (f : Vec 2 → ℝ) (x : Vec 2) :
    pushFlux Ψ Ψi (fun _ _ => 0) f x = 0 := by
  unfold pushFlux
  exact Matrix.mulVec_zero _

/-- The push by the centred chart `h ↦ Ψ h - c₀`, with inverse `w ↦ Ψi (c₀ + w)`, is the push by
`Ψ` conjugated by the translation by `c₀`. -/
theorem pushFlux_centered (Ψ Ψi : Vec 2 → Vec 2) (c₀ : Vec 2)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (g : Vec 2 → ℝ) (w : Vec 2) :
    pushFlux (fun h => Ψ h - c₀) (fun w => Ψi (c₀ + w)) L g w =
      pushFlux Ψ Ψi L (fun x' => g (x' - c₀)) (c₀ + w) := by
  unfold pushFlux
  rw [jacMatrix_sub_const]
  rfl

/-- **The push by a chart of the pull by its centred form** is the conjugation by the translation:
for a chart `Ψ` with inverse `Ψi` and unimodular Jacobian. -/
theorem pushFlux_pullFlux_centered {Ψ Ψi : Vec 2 → Vec 2} (c₀ : Vec 2)
    (h2 : ∀ x, Ψ (Ψi x) = x) (hdet : ∀ y, (jacMatrix Ψ y).det = 1)
    (F : (Vec 2 → ℝ) → Vec 2 → Vec 2) (f : Vec 2 → ℝ) (x : Vec 2) :
    pushFlux Ψ Ψi (pullFlux (fun h => Ψ h - c₀) (fun w => Ψi (c₀ + w)) F) f x =
      F (fun w => f (c₀ + w)) (x - c₀) := by
  have e : ((f ∘ Ψ) ∘ fun w => Ψi (c₀ + w)) = fun w => f (c₀ + w) := by
    funext w
    simp only [Function.comp_apply, h2]
  unfold pushFlux pullFlux
  rw [jacMatrix_sub_const, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one), Matrix.one_mulVec]
  beta_reduce
  rw [h2, e]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### The native chain: its centred maps -/

/-- The geometry of a native chain. -/
theorem geom_nativeChain {m : ℕ} (hm : 1 ≤ m) (k : ℤ) :
    (nativeChain m k).geom D = (D.flowOf (m - 1), 0, D.slotAnchor m k) := by
  have h0 : (nativeChain m k).recenter D 0 = nativeChain m k := by
    rw [nativeChain_recenter]
    rfl
  have h := geom_nativeChain_recenter D hm k 0
  rw [h0, add_zero] at h
  exact h

theorem famMap_nativeChain {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    (nativeChain m k).famMap D t =
      fun h => D.flowOf (m - 1) t h (D.slotAnchor m k) -
        D.flowOf (m - 1) t 0 (D.slotAnchor m k) := by
  funext h
  simp only [RealChain.famMap, geom_nativeChain (D := D) hm, zero_add]

theorem famMapInv_nativeChain {m : ℕ} (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    (nativeChain m k).famMapInv D t =
      fun w => D.flowOf (m - 1) (D.slotAnchor m k)
        (D.flowOf (m - 1) t 0 (D.slotAnchor m k) + w) t := by
  funext w
  simp only [RealChain.famMapInv, geom_nativeChain (D := D) hm, sub_zero]

/-! ### The direct part on the native families -/

open scoped Classical in
/-- The all-slow direct part of the orders `ords` of the identity `γ` on the native family of the
pulse `k` (zero unless the native chain is admissible and `k` is odd). -/
def nativeDirect (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    (ords : Finset ℕ) (k : ℤ) (t : ℝ) : (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  if hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k then
    directFlux G ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩ γ ords t
  else fun _ _ => 0

/-! ### The finer outputs on the native families -/

theorem fluxOp_copyQuad_native (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (s₀ : ℝ) (k : ℤ) (t : ℝ) :
    (SuccSource.copyQuad [] h π).fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t
        (nativeChain G.level k) = nativePathMean Mn G π Cc 2 k t := by
  unfold SuccSource.fluxOp nativePathMean
  split_ifs <;> rfl

theorem fluxOp_copyDir_native (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (ρ s₀ : ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (0 + 1)) (fun _ => ℝ)) (k : ℤ) (t : ℝ) :
    (SuccSource.copyDir [] v u γ).fluxOp ρ s₀ Cc k t (nativeChain G.level k) =
      nativeDirect G γ (Finset.Icc 3 Dm) k t := by
  unfold SuccSource.fluxOp nativeDirect
  split_ifs <;> rfl

theorem nativeDirect_pos (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    (ords : Finset ℕ) {k : ℤ} (t : ℝ)
    (hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k) :
    nativeDirect G γ ords k t =
      directFlux G ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩ γ ords t := by
  unfold nativeDirect
  split_ifs
  rfl

theorem nativeDirect_neg (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps} (γ : G.fam.Γ v u)
    (ords : Finset ℕ) {k : ℤ} (t : ℝ)
    (hA : ¬ (IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k)) :
    nativeDirect G γ ords k t = fun _ _ => 0 := by
  unfold nativeDirect
  split_ifs
  rfl

theorem nativePathMean_pos (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (n : ℕ) {k : ℤ} (t : ℝ)
    (hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k) :
    nativePathMean Mn G π Cc n k t =
      pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
        (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
          (pathEdges G π ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩))
        (Cc k (nativeChain G.level k)) n t := by
  unfold nativePathMean
  split_ifs
  rfl

theorem nativePathMean_neg (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (n : ℕ) {k : ℤ} (t : ℝ)
    (hA : ¬ (IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k)) :
    nativePathMean Mn G π Cc n k t = fun _ _ => 0 := by
  unfold nativePathMean
  split_ifs
  rfl

theorem fluxOp_letterMean_native (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (s₀ : ℝ) (n : ℕ) (k : ℤ) (t : ℝ) :
    (SuccSource.letterMean [] n h π).fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k t
        (nativeChain G.level k) =
      fun f y => nativePathMean Mn G π Cc n k t f y -
        (if hh : h = 1 then nativeDirect G (π.step ⟨0, by omega⟩).2.2 {n} k t f y else 0) := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · rw [nativePathMean_pos Mn G π Cc n t hA]
    unfold SuccSource.fluxOp
    rw [dite_eq_left hA]
    simp only [nativeDirect_pos G _ _ t hA]
  · rw [nativePathMean_neg Mn G π Cc n t hA]
    unfold SuccSource.fluxOp
    rw [dite_eq_right hA]
    funext f y
    by_cases hh : h = 1
    · subst hh
      simp only [↓reduceDIte, nativeDirect_neg G _ _ t hA, sub_zero]
    · simp only [hh, ↓reduceDIte, sub_zero]

/-! ### The Eulerian operators of the sources with the empty word -/

/-- **Degree `2`**: the quadratic conversion of a path. -/
theorem sourceEulerOp_copyQuad (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (t : ℝ) (φ : Vec 2 → ℝ) (x : Vec 2) :
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (SuccSource.copyQuad [] h π) Cc
        t φ x =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π Cc 2 0 0 k t φ x := by
  unfold sourceEulerOp gluedFluxOp dressedPathTerm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [fluxOp_copyQuad_native, Function.iterate_zero, id_eq, Nat.factorial_zero,
    Nat.cast_one, mul_one, inv_one, pow_zero, one_smul]

/-- **The direct transport**: the glue of the direct parts of the orders `3..Dm`. -/
theorem sourceEulerOp_copyDir (G : GenStage D hr Dm b j₀) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (ρ s₀ : ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (0 + 1)) (fun _ => ℝ)) (t : ℝ)
    (φ : Vec 2 → ℝ) (x : Vec 2) :
    sourceEulerOp ρ s₀ (SuccSource.copyDir [] v u γ) Cc t φ x =
      gluedFluxOp D G.level (fun k => nativeDirect G γ (Finset.Icc 3 Dm) k t) t φ x := by
  unfold sourceEulerOp
  simp only [fluxOp_copyDir_native]

/-- **Degree `n`, `a = a' = 0`**: the letter `𝖬_{n,h}` is the path mean minus, for a one-edge path,
the direct part of the order `n`. -/
theorem sourceEulerOp_letterMean (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (n : ℕ) (t : ℝ) (φ : Vec 2 → ℝ) (x : Vec 2) :
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
        (SuccSource.letterMean [] n h π) Cc t φ x =
      (∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π Cc n 0 0 k t φ x) -
      (if hh : h = 1 then gluedFluxOp D G.level
          (fun k => nativeDirect G (π.step ⟨0, by omega⟩).2.2 {n} k t) t φ x else 0) := by
  unfold sourceEulerOp gluedFluxOp dressedPathTerm
  simp only [fluxOp_letterMean_native, pushFlux_sub, smul_sub, Finset.sum_sub_distrib,
    Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, pow_zero,
    one_smul]
  congr 1
  by_cases hh : h = 1
  · subst hh
    simp only [↓reduceDIte]
  · simp only [hh, ↓reduceDIte, pushFlux_zero, smul_zero, Finset.sum_const_zero]

/-- **Degree `n`, `(a, a')`**: the letter `𝖵_{n,h,a,a'}` is the dressed term. -/
theorem sourceEulerOp_letterCov (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (hm : 1 ≤ G.level)
    {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ)
    (φ : Vec 2 → ℝ) (x : Vec 2) :
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
        (SuccSource.letterCov [] n h a a' π) Cc t φ x =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π Cc n a a' k t φ x := by
  unfold sourceEulerOp gluedFluxOp dressedPathTerm
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  beta_reduce
  by_cases hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k
  · have hfo : (SuccSource.letterCov [] n h a a' π).fluxOp
        (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t (nativeChain G.level k) =
        pullFlux ((nativeChain G.level k).famMap D t) ((nativeChain G.level k).famMapInv D t)
          (fun g x => ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
            (SuccSource.covAtFlux D G.level Mn.anchor t)^[a]
              (pushFlux ((nativeChain G.level k).famMap D t)
                ((nativeChain G.level k).famMapInv D t)
                (nativePathMean Mn G π Cc n k t)
                ((SuccSource.covAt D G.level Mn.anchor t)^[a'] g)) x) := by
      rw [nativePathMean_pos Mn G π Cc n t hA]
      unfold SuccSource.fluxOp
      rw [dite_eq_left hA]
    rw [hfo, famMap_nativeChain (D := D) hm, famMapInv_nativeChain (D := D) hm,
      pushFlux_pullFlux_centered _ (fun x => flowOf_inv D (G.level - 1) t (D.slotAnchor G.level k) x)
        (fun y => flowOf_det D (G.level - 1) t (D.slotAnchor G.level k) y)]
    congr 1
    have e1 : (fun w => φ (D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k) + w)) =
        fun w => φ (w + D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k)) := by
      funext w
      rw [add_comm]
    have e2 : (fun w => pushFlux
        (fun h => D.flowOf (G.level - 1) t h (D.slotAnchor G.level k) -
          D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k))
        (fun w => D.flowOf (G.level - 1) (D.slotAnchor G.level k)
          (D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k) + w) t)
        (nativePathMean Mn G π Cc n k t)
        (fun y => (SuccSource.covAt D G.level Mn.anchor t)^[a'] φ
          (y + D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k))) w) =
        fun w => pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
          (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
          (nativePathMean Mn G π Cc n k t) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ)
          (w + D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k)) := by
      funext w
      have h := pushFlux_centered (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
        (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
        (D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k)) (nativePathMean Mn G π Cc n k t)
        (fun y => (SuccSource.covAt D G.level Mn.anchor t)^[a'] φ
          (y + D.flowOf (G.level - 1) t 0 (D.slotAnchor G.level k))) w
      simp only [sub_add_cancel] at h
      rw [add_comm w]
      exact h
    unfold SuccSource.covAt at e2 ⊢
    unfold SuccSource.covAtFlux
    rw [e1, covOperator_iterate_translate]
    show (covOperator _)^[a] (fun w => pushFlux _ _ (nativePathMean Mn G π Cc n k t)
      (fun y => (covOperator _)^[a'] φ (y + _)) w) _ = _
    rw [e2, covOperator_iterate_translate]
    beta_reduce
    rw [sub_add_cancel]
  · have hfo : (SuccSource.letterCov [] n h a a' π).fluxOp
        (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t (nativeChain G.level k) =
        fun _ _ => 0 := by
      unfold SuccSource.fluxOp
      rw [dite_eq_right hA]
    rw [hfo, pushFlux_zero, nativePathMean_neg Mn G π Cc n t hA]
    have e : pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
        (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t) (fun _ _ => 0)
        ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ) = fun _ => 0 := by
      funext x'
      exact pushFlux_zero _ _ _ _
    unfold SuccSource.covAtFlux
    rw [e, ccfo_covOperator_iterate_zero, smul_zero]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The finer outputs annihilate constants: **`centeredConstants`**, and the corollary
`centeredCoefficientFiniteOrder`.

By `pcc_family_order_zero` the order-`0` entries of the lifts `Cc hh n'` vanish for
`(hh, n') ≠ (0, 0)`. For a grade `hh ≥ 1` the slow flux `liftFluxX` of a constant field is built
from lifts of grade `hh` (zero fields, or fields killed by the derivatives) and from the source
flux of lifts of grade `hh - 1` (zero fields, or at `(0, 0)` a constant field, killed by the
edges of orders `≥ 2`). So the path means of constants vanish, the direct parts of orders `≥ 2`
differentiate the constant, and the covariance operator kills constants. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness Providers Providers.GenSem

section Flux
variable {ι : Type} [Fintype ι] {Dm : ℕ} {Ω : Set (Vec 2)}

/-- The slow flux of a constant field vanishes for the grades `hh ≥ 1`. -/
theorem pcc_liftFluxX_const_zero [∀ i, FiniteDimensional ℝ ((fun _ : ι => ℝ) i)]
    (hΩ : IsOpen Ω) {Q : LiftOperatorData ι (fun _ => ℝ) Dm} {t₀ t₁ : ℝ} {sX sZ N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (hZ : ∀ hh' ≤ H, ∀ n', (hh' ≠ 0 ∨ n' ≠ 0) → PccZero Ω t₀ t₁ Cc hh' n')
    {hh : ℕ} (hh1 : 1 ≤ hh) (hhH : hh ≤ H) (c0 : ι → ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) {X : Vec 2} (hX : X ∈ Ω) (z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc (fun _ _ => c0) hh n t X z k = 0 := by
  have hg : PccGood Ω Cc c0 t hh (n + 1) :=
    pcc_good_of_zero hC c0 ht (fun hh' n' hlt h' =>
      hZ hh' (by rcases hlt with h | ⟨rfl, _⟩ <;> omega) n' h')
  have f1 : PccConstOn Ω (liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t) 0 :=
    pcc_liftApply_constOn (hZ hh hhH _ (Or.inl (by omega))) c0 ht
  have f2 : PccConstOn Ω (liftApply (n - 2) (Cc hh (n - 2)) (fun _ _ => c0) t) 0 :=
    pcc_liftApply_constOn (hZ hh hhH _ (Or.inl (by omega))) c0 ht
  have e1 : liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t X z = 0 := f1 X hX z
  have e2 : ∀ j, fastPartial j (liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t) X z = 0 :=
    fun j => pcc_fastPartial_zero f1 j X hX z
  have e3 : ∀ j, slowPartial j (liftApply (n - 2) (Cc hh (n - 2)) (fun _ _ => c0) t) X z = 0 :=
    fun j => pcc_slowPartial_zero hΩ f2 j X hX z
  have e4 : ∀ j ∈ Finset.Icc 1 (min Dm n),
      iteratedDeriv (j - 1) (fun ε : ℝ => sourceFlux Q.edge Q.η ε t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ _ => c0) t) k X z) 0 = 0 := by
    intro j hj
    obtain ⟨c, hc⟩ := hg (hh - 1) (n - j) (Or.inl (by omega))
    exact pcc_sourceFlux_iteratedDeriv_zero hΩ Q.edge Q.η t (j - 1) k hc hX z
  unfold liftFluxX
  have hh0 : hh ≠ 0 := by omega
  simp only [e1, e2, e3, hh0, ite_false, smul_zero, Finset.sum_const_zero, sub_zero, add_zero,
    zero_sub, neg_zero, ite_self]
  rw [Finset.sum_eq_zero fun j hj => by rw [e4 j hj, smul_zero]]
  simp

end Flux

section PathMean
variable {h Dm : ℕ} {Ω : Set (Vec 2)}

/-- The path mean flux of a constant field vanishes, at the labels with `ρ⁻¹ y ∈ Ω`. -/
theorem pcc_pathMeanFlux_const_zero (D : OCData) (m : ℕ) (ρ : ℝ) (hh1 : 1 ≤ h)
    (hΩ : IsOpen Ω) {Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm} {t₀ t₁ : ℝ}
    {sX sZ N : ℕ} {Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}
    (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N h Cc)
    (hZ : ∀ hh' ≤ h, ∀ n', (hh' ≠ 0 ∨ n' ≠ 0) → PccZero Ω t₀ t₁ Cc hh' n')
    (n : ℕ) (t : ℝ) (hs : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc t₀ t₁) (c : ℝ) (y : Vec 2)
    (hy : ρ⁻¹ • y ∈ Ω) :
    pathMeanFlux D m ρ Q Cc n t (fun _ => c) y = 0 := by
  funext κ
  unfold pathMeanFlux
  have hz : (fun z => liftFluxX Q Cc
      (fun _ X => (Pi.single (0 : Fin (h + 1)) ((fun _ : Vec 2 => c) (ρ • X)) : Fin (h + 1) → ℝ))
      h n ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) = fun _ => 0 :=
    funext fun z => pcc_liftFluxX_const_zero hΩ hC hZ hh1 le_rfl (Pi.single 0 c) n hs hy z κ
  rw [hz]
  simp [fieldCellMean]

end PathMean

section Direct
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The direct part of orders `≥ 2` of a constant field vanishes. -/
theorem pcc_directFlux_const_zero (G : GenStage D hr Dm b j₀) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ)
    (hords : ∀ d ∈ ords, 2 ≤ d) (t : ℝ) (c0 : ℝ) (y : Vec 2) :
    directFlux G p c γ ords t (fun _ => c0) y = 0 := by
  unfold directFlux
  refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun α _ => ?_
  have h1 : 1 ≤ d - 1 := by have := hords d hd; omega
  rw [pcc_orderedDerivative_const c0 h1 α y]
  simp

end Direct

section Cov
variable {h Dm : ℕ}

theorem pcc_covOperator_const_iterate (H : Matrix (Fin 2) (Fin 2) ℝ) (a : ℕ) :
    ∃ c : ℝ, (covOperator H)^[a] (fun _ : Vec 2 => (1 : ℝ)) = fun _ => c := by
  cases a with
  | zero => exact ⟨1, rfl⟩
  | succ a =>
    refine ⟨0, ?_⟩
    have h0 : covOperator H (fun _ : Vec 2 => (1 : ℝ)) = fun _ => 0 := by
      funext x
      simp [covOperator]
    rw [Function.iterate_succ_apply, h0, ccfo_covOperator_iterate_zero H a]

/-- **The covariance letter kills constants**, from the path means of constants near the label
`0`. -/
theorem pcc_covLetterFlux_const_zero (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (ρ s₀ : ℝ)
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (t : ℝ) (A : RealChain)
    (hP : ∀ᶠ y in 𝓝 (0 : Vec 2), ∀ c : ℝ, pathMeanFlux D m ρ Q Cc n t (fun _ => c) y = 0) :
    covLetterFlux D m ρ s₀ Q Cc n a a' t A (fun _ => 1) 0 = 0 := by
  unfold covLetterFlux pullFlux
  rw [famMap_zero A t]
  have hF : (((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
      (SuccSource.covAtFlux D m s₀ t)^[a]
        (pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t)
          ((SuccSource.covAt D m s₀ t)^[a'] ((fun _ => 1) ∘ A.famMapInv D t))) 0) = 0 := by
    obtain ⟨c1, hc1⟩ := pcc_covOperator_const_iterate
      (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) a'
    have hg : ((fun _ : Vec 2 => (1 : ℝ)) ∘ A.famMapInv D t) = fun _ => 1 := rfl
    have hW : pushFlux (A.famMap D t) (A.famMapInv D t) (pathMeanFlux D m ρ Q Cc n t)
        ((SuccSource.covAt D m s₀ t)^[a'] ((fun _ => 1) ∘ A.famMapInv D t)) =ᶠ[𝓝 0]
        fun _ => 0 := by
      rw [hg]
      have hc1' : (SuccSource.covAt D m s₀ t)^[a'] (fun _ : Vec 2 => (1 : ℝ)) = fun _ => c1 :=
        hc1
      rw [hc1']
      have hcont : ContinuousAt (A.famMapInv D t) 0 := (contDiff_famMapInv A t).continuous.continuousAt
      have hmem := hcont.preimage_mem_nhds (by rw [famMapInv_zero hζ A t]; exact hP)
      filter_upwards [hmem] with x hx
      unfold pushFlux
      have := hx c1
      simp only [Function.comp_def] at this ⊢
      rw [this]
      simp
    have hit := covOperator_iterate_germ
      (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) a hW
    have hv := hit.self_of_nhds
    simp only [SuccSource.covAtFlux]
    rw [hv, ccfo_covOperator_iterate_zero]
    simp
  beta_reduce
  rw [hF]
  simp

end Cov

/-- **The finer outputs annihilate constants** (the constants clause of the finer-output step). -/
theorem centeredConstants : CenteredConstantsStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G hin s hv hnd hres Cc hLF k hk t ht B hB
  have hΛ := hin.base
  have hζ := hin.profile
  have hκ := hin.band
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hlet : ∀ l ∈ Mn.A, 2 ≤ letterOrder P.N P.p l := fun l hl => (hin.letter_orders l hl).1
  have hts := ccov_inv_mul_mem_window hc ht
  have hO := isOpen_ladderOmega D b j₀ G.level k B (Mn.lenFactor * liftLength D G.level)
  have h0 := zero_mem_ladderOmega hζ hB (Mn.lenFactor * liftLength D G.level)
  have hy0 : (Mn.lenFactor * liftLength D G.level)⁻¹ • (0 : Vec 2) ∈
      ladderOmega D b j₀ G.level k B (Mn.lenFactor * liftLength D G.level) := by
    rw [smul_zero]; exact h0
  unfold SuccSource.fluxOp
  rw [dite_eq_left ⟨hB, hk⟩]
  cases s with
  | copyDir t' v u γ =>
    exact pcc_directFlux_const_zero G ⟨k, hk⟩ ⟨B, hB⟩ γ _
      (fun d hd => by have := (Finset.mem_Icc.mp hd).1; omega) t 1 0
  | letterDiag t' u => exact absurd trivial hnd
  | copyQuad t' h π =>
    have hC := hLF k B ⟨hB, hk⟩
    exact pcc_pathMeanFlux_const_zero D G.level _ hv.2.2 hO hC
      (pcc_family_order_zero hΛ hζ hκ Mn π k hk hB (Cc k B) hC) _ t hts 1 0 hy0
  | letterMean t' n h π =>
    have hC := hLF k B ⟨hB, hk⟩
    have hn2 : 2 ≤ n := hlet _ (hv.2.1 _ rfl).2
    have hp := pcc_pathMeanFlux_const_zero D G.level (Mn.lenFactor * liftLength D G.level)
      hv.2.2 hO hC (pcc_family_order_zero hΛ hζ hκ Mn π k hk hB (Cc k B) hC) n t hts 1 0 hy0
    have hd : (if hh : h = 1 then
        directFlux G ⟨k, hk⟩ ⟨B, hB⟩ (π.step ⟨0, by omega⟩).2.2 {n} t (fun _ => 1) 0
      else (0 : Vec 2)) = 0 := by
      split_ifs with h1
      · exact pcc_directFlux_const_zero G ⟨k, hk⟩ ⟨B, hB⟩ _ {n}
          (fun d hd => by rw [Finset.mem_singleton.mp hd]; exact hn2) t 1 0
      · rfl
    exact (congrArg₂ (· - ·) hp hd).trans (sub_zero _)
  | letterCov t' n h a a' π =>
    have hC := hLF k B ⟨hB, hk⟩
    have hZ := pcc_family_order_zero hΛ hζ hκ Mn π k hk hB (Cc k B) hC
    have hO' : IsOpen {y : Vec 2 | (Mn.lenFactor * liftLength D G.level)⁻¹ • y ∈
        ladderOmega D b j₀ G.level k B (Mn.lenFactor * liftLength D G.level)} :=
      hO.preimage (continuous_const_smul _)
    have hP : ∀ᶠ y in 𝓝 (0 : Vec 2), ∀ c : ℝ, pathMeanFlux D G.level
        (Mn.lenFactor * liftLength D G.level) (familyLiftData D G.level k B
          (Mn.lenFactor * liftLength D G.level) (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) (Cc k B) n t
        (fun _ => c) y = 0 := by
      filter_upwards [hO'.mem_nhds hy0] with y hy c
      exact pcc_pathMeanFlux_const_zero D G.level _ hv.2.2 hO hC hZ n t hts c y hy
    exact pcc_covLetterFlux_const_zero D hζ G.level _ Mn.anchor _ (Cc k B) n a a' t B hP

/-- **The finer-output step, corrected statement, proved.** -/
theorem centeredCoefficientFiniteOrder : CenteredCoefficientFiniteOrderStatement :=
  centeredCoefficientFiniteOrder_of_constants centeredConstants

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, constants at grade zero: the path mean flux of a constant field vanishes for a
scalar lift sequence of grade zero and degree `n ≥ 2`, once the order-zero entries of the lifts
`(0, n')`, `n' ≠ 0`, vanish. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness

/-- The slow flux of a constant field at grade zero and degree `n ≥ 2` vanishes. -/
theorem fsc_liftFluxX_const_zero_grade0 {ι : Type} [Fintype ι] {Dm : ℕ}
    [∀ i, FiniteDimensional ℝ ((fun _ : ι => ℝ) i)] {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    {Q : LiftOperatorData ι (fun _ => ℝ) Dm} {t₀ t₁ : ℝ} {sX sZ N : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N 0 Cc)
    (hZ : ∀ n', n' ≠ 0 → PccZero Ω t₀ t₁ Cc 0 n') (c0 : ι → ℝ) {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) {X : Vec 2} (hX : X ∈ Ω) (z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc (fun _ _ => c0) 0 n t X z k = 0 := by
  have f1 : PccConstOn Ω (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ _ => c0) t) 0 :=
    pcc_liftApply_constOn (hZ _ (by omega)) c0 ht
  have f2 : ∃ c, PccConstOn Ω (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ _ => c0) t) c := by
    by_cases h2 : n - 2 = 0
    · rw [h2]
      exact ⟨c0, fun X' _ z' => hC.1 (fun _ => c0) contDiff_const t ht X' z'⟩
    · exact ⟨0, pcc_liftApply_constOn (hZ _ h2) c0 ht⟩
  obtain ⟨c2, f2⟩ := f2
  have e1 : liftApply (n - 1) (Cc 0 (n - 1)) (fun _ _ => c0) t X z = 0 := f1 X hX z
  have e2 : ∀ j, fastPartial j (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ _ => c0) t) X z = 0 :=
    fun j => pcc_fastPartial_zero f1 j X hX z
  have e3 : ∀ j, slowPartial j (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ _ => c0) t) X z = 0 :=
    fun j => pcc_slowPartial_zero hΩ f2 j X hX z
  unfold liftFluxX
  simp [e1, e2, e3, hn]

/-- The path mean flux of a constant field vanishes at grade zero and degree `n ≥ 2`. -/
theorem fsc_pathMeanFlux_const_zero_grade0 (D : OCData) (m : ℕ) (ρ : ℝ) {Dm : ℕ}
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) {Q : LiftOperatorData (Fin (0 + 1)) (fun _ => ℝ) Dm}
    {t₀ t₁ : ℝ} {sX sZ N : ℕ} {Cc : ℕ → ℕ → LiftCoeff (Fin (0 + 1)) (fun _ => ℝ)}
    (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N 0 Cc)
    (hZ : ∀ n', n' ≠ 0 → PccZero Ω t₀ t₁ Cc 0 n') {n : ℕ} (hn : 2 ≤ n) (t : ℝ)
    (hs : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc t₀ t₁) (c : ℝ) (y : Vec 2) (hy : ρ⁻¹ • y ∈ Ω) :
    pathMeanFlux D m ρ Q Cc n t (fun _ => c) y = 0 := by
  funext κ
  unfold pathMeanFlux
  have hz : (fun z => liftFluxX Q Cc
      (fun _ X => (Pi.single (0 : Fin (0 + 1)) ((fun _ : Vec 2 => c) (ρ • X)) : Fin (0 + 1) → ℝ))
      0 n ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) = fun _ => 0 :=
    funext fun z => fsc_liftFluxX_const_zero_grade0 hΩ hC hZ (Pi.single 0 c) hn hs hy z κ
  rw [hz]
  simp [fieldCellMean]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
