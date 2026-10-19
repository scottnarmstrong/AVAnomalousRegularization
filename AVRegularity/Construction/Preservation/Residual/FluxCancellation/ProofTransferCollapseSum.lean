-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeSplitInput
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Mean
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCenteredCoeff
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleJoint.PlaneWindowScalarDiffusion
import AVRegularity.EntryWeakAssembly.MolecularHigherTraceJetDerivative
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
public import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.EntryWeak.NormalizedPulseTransverse

section
section
/-! **The jet-locality step: the layer statements and the glued assembly**.

`MenuMeanFluxJetStatement` is reduced to the four layer statements

* `SrcCoeffStatement`: the `ε`-coefficients `SrcCoeff` of the source flux;
* `LiftFluxStatement`: `liftFluxX` (four terms, using `SrcCoeffStatement` and the `liftApply`,
  partial derivative layers);
* `CellMeanStatement`: the cell mean commutes with equal jets;
* `PulseStatement`: `pulseMeanFluxEuler` (chart, label, Jacobian factor), from
  `LiftFluxStatement` and `CellMeanStatement`,

and the glue over the pulses of `menuGluedMeanFlux` is proved here from `PulseStatement` alone
(`menuMeanFluxJet_of_pulse`). The chart-label identity `chart t (label t y) = y` for the
flow charts of `D.flowOf` is `flow_chart_label`, from the group law `flowOf_group` and the
value `flowOf k s x s = x`.

At a time with no active pulse the cutoff is `0` and the flux vanishes. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- A function with both `C^s` and equal jets of order `s` at `x`. -/
def Triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℕ) (x : Vec 2)
    (f g : Vec 2 → E) : Prop :=
  ContDiff ℝ (↑s : ℕ∞) f ∧ ContDiff ℝ (↑s : ℕ∞) g ∧ SameJetAt s x f g

/-- Equal jets of the lifted fields give equal jets of the `ε`-coefficients of the source
flux (loss `D`). -/
def SrcCoeffStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ₁ Φ₂ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (ℓ r : ℕ) (X₀ : Vec 2),
    (∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth r r (fun X z => γ.coeff α t X z)) →
    IsBoxSmooth (r + D) (r + D) Φ₁ → IsBoxSmooth (r + D) (r + D) Φ₂ → SameJetX (r + D) X₀ Φ₁ Φ₂ →
    SameJetX r X₀ (CovFluxReg.SrcCoeff edge η t Φ₁ k ℓ) (CovFluxReg.SrcCoeff edge η t Φ₂ k ℓ)

/-- The cell mean of fields with equal `X`-jets has equal jets. -/
def CellMeanStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (s : ℕ) (X₀ : Vec 2)
    (Φ₁ Φ₂ : Vec 2 → Vec 2 → E), ContDiff ℝ (↑s : ℕ∞) (Function.uncurry Φ₁) →
    ContDiff ℝ (↑s : ℕ∞) (Function.uncurry Φ₂) → SameJetX s X₀ Φ₁ Φ₂ →
    SameJetAt s X₀ (fun X => fieldCellMean (Φ₁ X)) (fun X => fieldCellMean (Φ₂ X))

/-- Equal jets of the coarse fields give equal `X`-jets of `liftFluxX`. -/
def LiftFluxStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₁ a₂ : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (k : Fin 2) (s N H : ℕ) (X₀ : Vec 2),
    1 ≤ Dm → hh ≤ H →
    (∀ hh' ≤ H, ∀ n', N < n' → ∀ m α t X z v u, Cc hh' n' m α t X z v u = 0) →
    (∀ hh' ≤ H, ∀ n' m α v u,
      IsBoxSmooth (s + Dm) (s + Dm) (fun X z => Cc hh' n' m α t X z v u)) →
    (∀ j, ContDiff ℝ (s : ℕ∞) (fun X => Q.G t X k j)) →
    ContDiff ℝ (s : ℕ∞) (fun z => Q.v t z k) →
    (hh ≠ 0 → ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α t X z)) →
    ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a₁ t) → ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a₂ t) →
    SameJetAt (s + Dm + N) X₀ (a₁ t) (a₂ t) →
    SameJetX s X₀ (fun X z => liftFluxX Q Cc a₁ hh n t X z k)
      (fun X z => liftFluxX Q Cc a₂ hh n t X z k)

/-- The Eulerian flux of one pulse: equal jets of the coarse fields at `x` (with
`chart t (label t x) = x`) give equal jets of the flux at `x`. -/
def PulseStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] {Dm : ℕ} (c ρ εc : ℝ) (n r : ℕ)
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2)
    (a₁ a₂ : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (v : ι) (s N H : ℕ) (x : Vec 2),
    c ≠ 0 → 1 ≤ Dm → r ≤ H →
    (∀ hh' ≤ H, ∀ n', N < n' → ∀ m α t X z v u, Cc hh' n' m α t X z v u = 0) →
    (∀ hh' ≤ H, ∀ n' m α v u,
      IsBoxSmooth (s + Dm) (s + Dm) (fun X z => Cc hh' n' m α (c⁻¹ * t) X z v u)) →
    (∀ k j, ContDiff ℝ (s : ℕ∞) (fun X => Q.G (c⁻¹ * t) X k j)) →
    (∀ k, ContDiff ℝ (s : ℕ∞) (fun z => Q.v (c⁻¹ * t) z k)) →
    (r ≠ 0 → ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth s s (fun X z => γ.coeff α (c⁻¹ * t) X z)) →
    ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a₁ t) → ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a₂ t) →
    SameJetAt (s + Dm + N) x (a₁ t) (a₂ t) →
    ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (chart t) → ContDiff ℝ (s : ℕ∞) (label t) →
    chart t (label t x) = x →
    Triple s x (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₁ t y v)
      (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a₂ t y v)

theorem flowOf_self' (D : OCData) (k : ℕ) (s : ℝ) (x : Vec 2) : D.flowOf k s x s = x := by
  have hX := AVenhance.flow_isFlow _ (D.hΦ k).vel_continuous (D.hΦ k).vel_lipschitz
  change streamFlow (D.Φ k) (D.hΦ k) s x s = x
  unfold streamFlow
  exact hX.1 x s

/-- **The chart-label identity** for the flow charts of `D.flowOf`. -/
theorem flow_chart_label (D : OCData) (k : ℕ) (a t : ℝ) (x : Vec 2) :
    D.flowOf k t (D.flowOf k a x t) a = x := by
  rw [AVRegularity.Providers.QuietAtlas.flowOf_group D k x t a t, flowOf_self']

/-- Sums of triples. -/
theorem triple_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}
    (S : Finset κ) {s : ℕ} {x : Vec 2} {f g : κ → Vec 2 → E}
    (h : ∀ i ∈ S, Triple s x (f i) (g i)) :
    Triple s x (fun y => ∑ i ∈ S, f i y) (fun y => ∑ i ∈ S, g i y) :=
  ⟨ContDiff.sum fun i hi => (h i hi).1, ContDiff.sum fun i hi => (h i hi).2.1,
    sameJet_sum S (fun i hi => (h i hi).1) (fun i hi => (h i hi).2.1)
      (fun i hi => (h i hi).2.2)⟩

/-- A constant multiple of a triple. -/
theorem triple_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ} {x : Vec 2}
    {f g : Vec 2 → E} (c : ℝ) (h : Triple s x f g) :
    Triple s x (fun y => c • f y) (fun y => c • g y) := by
  refine ⟨h.1.const_smul c, h.2.1.const_smul c, ?_⟩
  have := sameJet_clm (c • ContinuousLinearMap.id ℝ E) h.1 h.2.1 h.2.2
  simpa using this

/-- **The glue over the pulses**, from the pulse statement. -/
theorem menuMeanFluxJet_of_pulse (hPulse : PulseStatement) :
    MenuMeanFluxJetStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin s hs t x a₁ a₂ h₁ h₂ hj v
  obtain ⟨hX, hZ⟩ := CovFluxReg.floors' P Mn G G' depth CcT hin
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hin.stage.base hin.stage.profile
    hin.stage.band G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hin.stage.base
  have hDm : 1 ≤ Dm := hin.stage.order
  have hsa : 2 * Mn.p + Dm + Mn.N ≤ s := by omega
  have ha : ∀ (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (↑s : ℕ∞) (fun y => a t y v)) →
      ContDiff ℝ ((2 * Mn.p + Dm + Mn.N : ℕ) : ℕ∞) (a t) := fun a h =>
    (contDiff_pi.2 h).of_le (by exact_mod_cast hsa)
  have hjj : SameJetAt (2 * Mn.p + Dm + Mn.N) x (a₁ t) (a₂ t) :=
    sameJet_pi (fun w => (h₁ w).of_le (by exact_mod_cast hsa))
      (fun w => (h₂ w).of_le (by exact_mod_cast hsa))
      (fun w => sameJet_mono hsa (hj w))
  unfold menuMeanFluxE menuGluedMeanFlux
  refine (triple_sum _ fun k _ => triple_sum _ fun r hrr => triple_sum _
    fun n _ => ?_).2.2
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · simp only [hcut, zero_smul]
      exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩
    · refine triple_smul _ ?_
      have ht' := CovFluxReg.clock_mem_window D G.level k t hτ hcc hcut
      have hwin := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
      obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hin.lift k hodd
      refine hPulse _ _ _ n r _ _ _ _ a₁ a₂ t v (2 * Mn.p) Mn.N depth x hcc.ne'
        hDm (Finset.mem_Icc.mp hrr).2 hz3 ?_ ?_ ?_ ?_ (ha a₁ h₁) (ha a₂ h₂) hjj ?_ ?_ ?_
      · exact fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono hX hZ
      · intro k' j
        exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
          (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top)
      · intro k'
        exact (CovFluxReg.ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level)
          hodd _ k').of_le (by exact_mod_cast le_top)
      · intro _
        exact CovFluxReg.fiber_edge_boxSmooth G
          (CovFluxReg.actualFluxJointSmooth P Mn G G' depth CcT hin) k hodd _ _ t hcc.ne' hwin
          (2 * Mn.p)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
          (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
          (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)
      · exact flow_chart_label D (G.level - 1) (D.slotAnchor G.level k) t x
  · simp only [hodd, dite_false]
    exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step, the cell mean at finite regularity**.

For jointly `C^s` fields `Φ₁, Φ₂` with equal `X`-jets of order `s` at `X₀` (at every `z`), the cell
means `X ↦ ∫_{[0,1]²} Φ_i(X, z) dz` have equal jets of order `s` at `X₀`
(`cellMean_sameJet`, the statement `CellMeanStatement`). By induction on `s`: the
derivative of the cell mean is the cell mean of the `X`-partial derivative
(`fderiv_cellMean`), and the partials have equal jets of order `s - 1`
(`sameJet_succ_iff`). The global-bound interchange lemma `orderedDerivative_parameter_integral`
is not used (it needs bounds uniform in `X`).

For `s = 0` the statement reduces to continuity and equality of values. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter Topology Metric
open AVRegularity.Providers.PathDecomp
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `X`-partial of a jointly `C^1` field, from the joint derivative. -/
theorem slice_fderiv {Φ : Vec 2 → Vec 2 → E} (hΦ : ContDiff ℝ 1 (Function.uncurry Φ))
    (y z v : Vec 2) :
    fderiv ℝ (fun X => Φ X z) y v = fderiv ℝ (Function.uncurry Φ) (y, z) (v, 0) := by
  have h1 : HasFDerivAt (fun X' : Vec 2 => (X', z)) (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) y :=
    ((hasFDerivAt_id y).prodMk (hasFDerivAt_const z y)).congr_fderiv (by ext <;> simp)
  have h2 := ((hΦ.differentiable one_ne_zero) (y, z)).hasFDerivAt.comp y h1
  have h3 : HasFDerivAt (fun X => Φ X z) _ y := h2
  rw [h3.fderiv]
  simp

/-- **Differentiation under the cell mean.** -/
theorem fderiv_cellMean [CompleteSpace E] {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ContDiff ℝ 1 (Function.uncurry Φ)) (y v : Vec 2) :
    fderiv ℝ (fun X => fieldCellMean (Φ X)) y v =
      fieldCellMean (fun z => fderiv ℝ (Function.uncurry Φ) (y, z) (v, 0)) := by
  let F' : Vec 2 → Vec 2 → (Vec 2 →L[ℝ] E) := fun X z =>
    (fderiv ℝ (Function.uncurry Φ) (X, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))
  have hF'c : Continuous (Function.uncurry F') :=
    (hΦ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hpart : ∀ X z, HasFDerivAt (fun X' => Φ X' z) (F' X z) X := by
    intro X z
    have h1 : HasFDerivAt (fun X' : Vec 2 => (X', z)) (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) X :=
      ((hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)).congr_fderiv (by ext <;> simp)
    exact (hΦ.differentiable one_ne_zero (X, z)).hasFDerivAt.comp X h1
  have hderiv : HasFDerivAt (fun X => ∫ z in closedCell, Φ X z) (∫ z in closedCell, F' y z) y := by
    obtain ⟨M, hM⟩ := ((isCompact_closedBall y 1).prod isCompact_closedCell).exists_bound_of_continuousOn
      hF'c.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.restrict closedCell) (F := fun X z => Φ X z) (F' := F') (bound := fun _ => M)
      (closedBall_mem_nhds y one_pos) (Eventually.of_forall fun X => ?_) ?_ ?_ ?_
      (integrable_const M) (Eventually.of_forall fun z X _ => hpart X z)
    · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        isCompact_closedCell
    · exact (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · refine (ae_restrict_iff' isCompact_closedCell.measurableSet).2
        (Eventually.of_forall fun z hz X hX => ?_)
      exact hM (X, z) ⟨hX, hz⟩
  have hi : Integrable (fun z => F' y z) (volume.restrict closedCell) :=
    (hF'c.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      isCompact_closedCell
  simp only [fieldCellMean_eq_closedCell]
  rw [hderiv.fderiv, ContinuousLinearMap.integral_apply hi]
  rfl

/-- Values of the cell mean. -/
theorem cellMean_value {Φ₁ Φ₂ : Vec 2 → Vec 2 → E} {X₀ : Vec 2} (hj : SameJetX 0 X₀ Φ₁ Φ₂) :
    fieldCellMean (Φ₁ X₀) = fieldCellMean (Φ₂ X₀) := by
  simp only [fieldCellMean]
  exact integral_congr_ae (ae_of_all _ fun z =>
    (sameJet_zero_iff (x := X₀) (f := fun X => Φ₁ X z) (g := fun X => Φ₂ X z)).1 (hj z))

/-- The `i`-th `X`-partial of a jointly `C^{r+1}` field is jointly `C^r`. -/
theorem partial_contDiff {r : ℕ} {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ContDiff ℝ (↑(r + 1) : ℕ∞) (Function.uncurry Φ)) (i : Fin 2) :
    ContDiff ℝ (↑r : ℕ∞) (Function.uncurry fun y z => fderiv ℝ (Function.uncurry Φ) (y, z)
      (basisVec i, 0)) :=
  (hΦ.fderiv_right (by exact_mod_cast le_refl _)).clm_apply contDiff_const

/-- The cell mean at finite regularity. -/
theorem cellMean_sameJet : CellMeanStatement := by
  intro E _ _ _ s
  induction s with
  | zero =>
    intro X₀ Φ₁ Φ₂ _ _ hj
    exact sameJet_zero_iff.2 (cellMean_value hj)
  | succ r ih =>
    intro X₀ Φ₁ Φ₂ h₁ h₂ hj
    have h₁' : ContDiff ℝ 1 (Function.uncurry Φ₁) := h₁.of_le (by exact_mod_cast Nat.succ_pos r)
    have h₂' : ContDiff ℝ 1 (Function.uncurry Φ₂) := h₂.of_le (by exact_mod_cast Nat.succ_pos r)
    rw [sameJet_succ_iff]
    refine ⟨cellMean_value (fun z => sameJet_mono (Nat.zero_le _) (hj z)), fun i => ?_⟩
    have e : ∀ {Φ : Vec 2 → Vec 2 → E}, ContDiff ℝ 1 (Function.uncurry Φ) →
        (fun y => fderiv ℝ (fun X => fieldCellMean (Φ X)) y (basisVec i)) =
          fun y => fieldCellMean (fun z => fderiv ℝ (Function.uncurry Φ) (y, z) (basisVec i, 0)) :=
      fun h => funext fun y => fderiv_cellMean h y _
    rw [e h₁', e h₂']
    refine ih X₀ (fun y z => fderiv ℝ (Function.uncurry Φ₁) (y, z) (basisVec i, 0))
      (fun y z => fderiv ℝ (Function.uncurry Φ₂) (y, z) (basisVec i, 0))
      (partial_contDiff h₁ i) (partial_contDiff h₂ i) fun z => ?_
    have := (sameJet_succ_iff.1 (hj z)).2 i
    simp only [slice_fderiv h₁', slice_fderiv h₂'] at this
    exact this

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step, the `ε`-coefficients of the source flux**.

The sequences `QuietDecay.seqWord η l Φ i` (the `ε`-coefficients of the word derivative) lose one
`X`-derivative per letter: if the box smooth fields `Φ₁, Φ₂` have equal `X`-jets of order
`r + |l|`, the coefficients have equal `X`-jets of order `r` (`seqWord_sameJetX`). Hence
`srcW` and `SrcCoeff` (finite sums of coefficients times `srcW`) have equal jets
(`srcCoeff_sameJetX`, the statement `SrcCoeffStatement`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sameJetX_mono {r r' : ℕ} (hr : r ≤ r') {X₀ : Vec 2} {Φ₁ Φ₂ : Vec 2 → Vec 2 → E}
    (h : SameJetX r' X₀ Φ₁ Φ₂) : SameJetX r X₀ Φ₁ Φ₂ := fun z => sameJet_mono hr (h z)

/-- Fast and slow partials of a box smooth field have `X`-slices of class `C^r`, in the form used
by the word recursion. -/
theorem fast_slice {a r : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth a a Ψ)
    (hr : r + 1 ≤ a) (k : Fin 2) :
    IsBoxSmooth r r (fastPartial k Ψ) :=
  ((h.mono (by omega) (by omega) : IsBoxSmooth r (r + 1) Ψ).fastPartial k)

theorem slow_slice {a r : ℕ} {Ψ : Vec 2 → Vec 2 → E} (h : IsBoxSmooth a a Ψ)
    (hr : r + 1 ≤ a) (k : Fin 2) :
    IsBoxSmooth r r (slowPartial k Ψ) :=
  ((h.mono (by omega) (by omega) : IsBoxSmooth (r + 1) r Ψ).slowPartial k)

/-- **The word recursion loses one `X`-derivative per letter.** -/
theorem seqWord_sameJetX (η : ℝ) (X₀ : Vec 2) {Φ₁ Φ₂ : Vec 2 → Vec 2 → E} {s : ℕ}
    (h₁ : IsBoxSmooth s s Φ₁) (h₂ : IsBoxSmooth s s Φ₂) (l : List (Fin 2)) :
    ∀ r, r + l.length ≤ s → SameJetX (r + l.length) X₀ Φ₁ Φ₂ →
      ∀ i, SameJetX r X₀ (QuietDecay.seqWord η l Φ₁ i) (QuietDecay.seqWord η l Φ₂ i) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro r _ hj i
    cases i with
    | zero => simpa [QuietDecay.seqWord_nil, QuietDecay.seqInit] using hj
    | succ j => exact fun z _ _ _ => rfl
  | append_singleton l k ih =>
    intro r hr hj i
    simp only [List.length_append, List.length_singleton] at hr hj
    have hb₁ := QuietDecay.isBoxSmooth_seqWord η l h₁ (by omega)
    have hb₂ := QuietDecay.isBoxSmooth_seqWord η l h₂ (by omega)
    have jet : ∀ r', r' ≤ r + 1 → ∀ i, SameJetX r' X₀ (QuietDecay.seqWord η l Φ₁ i)
        (QuietDecay.seqWord η l Φ₂ i) := fun r' hr' i =>
      ih r' (by omega) (sameJetX_mono (by omega) hj) i
    rw [QuietDecay.seqWord_concat, QuietDecay.seqWord_concat]
    have hf : ∀ i, SameJetX r X₀ (fastPartial k (QuietDecay.seqWord η l Φ₁ i))
        (fastPartial k (QuietDecay.seqWord η l Φ₂ i)) := fun i =>
      fastPartial_sameJetX
        ((hb₁ i).mono (by omega) (by omega)) ((hb₂ i).mono (by omega) (by omega))
        (jet r (by omega) i) k
    cases i with
    | zero => exact hf 0
    | succ j =>
      intro z
      have hsl : SameJetX r X₀ (slowPartial k (QuietDecay.seqWord η l Φ₁ j))
          (slowPartial k (QuietDecay.seqWord η l Φ₂ j)) :=
        slowPartial_sameJetX (jet (r + 1) le_rfl j) k
      have c1 : ∀ {Φ : Vec 2 → Vec 2 → E}, IsBoxSmooth s s Φ → ∀ i,
          ContDiff ℝ (↑r : ℕ∞) (fun X => fastPartial k (QuietDecay.seqWord η l Φ i) X z) := by
        intro Φ hΦ i
        exact boxSmooth_slice (fast_slice
          ((QuietDecay.isBoxSmooth_seqWord η l hΦ (by omega) i)) (by omega) k) z
      have c2 : ∀ {Φ : Vec 2 → Vec 2 → E}, IsBoxSmooth s s Φ → ∀ i,
          ContDiff ℝ (↑r : ℕ∞) (fun X => slowPartial k (QuietDecay.seqWord η l Φ i) X z) := by
        intro Φ hΦ i
        exact boxSmooth_slice (slow_slice
          ((QuietDecay.isBoxSmooth_seqWord η l hΦ (by omega) i)) (by omega) k) z
      show SameJetAt r X₀ (fun X => fastPartial k (QuietDecay.seqWord η l Φ₁ (j + 1)) X z +
          Real.sqrt η • slowPartial k (QuietDecay.seqWord η l Φ₁ j) X z)
        (fun X => fastPartial k (QuietDecay.seqWord η l Φ₂ (j + 1)) X z +
          Real.sqrt η • slowPartial k (QuietDecay.seqWord η l Φ₂ j) X z)
      refine sameJet_add (c1 h₁ _) (c1 h₂ _) ((c2 h₁ _).const_smul _) ((c2 h₂ _).const_smul _)
        (hf (j + 1) z) ?_
      have := sameJet_clm (Real.sqrt η • ContinuousLinearMap.id ℝ E) (c2 h₁ j) (c2 h₂ j) (hsl z)
      simpa using this

section Source

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- `srcW` loses `|α|` derivatives. -/
theorem srcW_sameJetX (η : ℝ) (X₀ : Vec 2) {Φ₁ Φ₂ : Vec 2 → Vec 2 → ∀ i, h i} {s : ℕ}
    (h₁ : IsBoxSmooth s s Φ₁) (h₂ : IsBoxSmooth s s Φ₂) (u : ι) {m : ℕ} (α : DerivativeWord2 m)
    {r : ℕ} (hr : r + m ≤ s) (hj : SameJetX (r + m) X₀ Φ₁ Φ₂) (i : ℕ) :
    SameJetX r X₀ (QuietDecay.srcW η u α Φ₁ i) (QuietDecay.srcW η u α Φ₂ i) := by
  have hp : ∀ {Φ : Vec 2 → Vec 2 → ∀ i, h i}, IsBoxSmooth s s Φ →
      IsBoxSmooth s s (fun X z => Φ X z u) := fun hΦ =>
    hΦ.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
  have key := seqWord_sameJetX η X₀ (hp h₁) (hp h₂) (List.ofFn α) r (by simpa using hr)
    (by
      simp only [List.length_ofFn]
      intro z
      refine sameJet_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)
        (boxSmooth_slice (h₁.mono (by omega) (by omega)) z)
        (boxSmooth_slice (h₂.mono (by omega) (by omega)) z) (hj z)) i
  exact key

/-- Sums over a list of triples. -/
theorem list_sum_triple {κ : Type*} (L : List κ) {r : ℕ} {x : Vec 2} {f g : κ → Vec 2 → E}
    (hL : ∀ γ ∈ L, Triple r x (f γ) (g γ)) :
    Triple r x (fun y => (L.map fun γ => f γ y).sum) (fun y => (L.map fun γ => g γ y).sum) := by
  induction L with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩
  | cons a L ih =>
    have h1 := hL a (by simp)
    have h2 := ih fun γ hγ => hL γ (by simp [hγ])
    refine ⟨?_, ?_, ?_⟩
    · simpa using h1.1.add h2.1
    · simpa using h1.2.1.add h2.2.1
    · simpa using sameJet_add h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2 h2.2.2

/-- The `ε`-coefficients of the source flux have equal jets. -/
theorem srcCoeff_sameJetX : SrcCoeffStatement := by
  intro ι _ h _ _ D edge η t Φ₁ Φ₂ k ℓ r X₀ hΓ h₁ h₂ hj z
  have hv : ∀ v, Triple r X₀ (fun X => CovFluxReg.SrcCoeff edge η t Φ₁ k ℓ X z v)
      (fun X => CovFluxReg.SrcCoeff edge η t Φ₂ k ℓ X z v) := by
    intro v
    simp only [CovFluxReg.SrcCoeff]
    refine triple_sum _ fun u _ => triple_sum _ fun d _ =>
      list_sum_triple _ fun γ hγ => triple_sum _ fun α _ => ?_
    have hd := Finset.mem_Icc.mp d.2
    have hm : d.1 - 1 ≤ D := by omega
    have hc : ContDiff ℝ (↑r : ℕ∞) (fun X => γ.coeff α t X z k) :=
      contDiff_pi.1 (boxSmooth_slice (hΓ v u d γ hγ α) z) k
    have hw : ∀ {Φ : Vec 2 → Vec 2 → ∀ i, h i}, IsBoxSmooth (r + D) (r + D) Φ →
        ContDiff ℝ (↑r : ℕ∞) (fun X => γ.map (QuietDecay.srcW η u α Φ ℓ X z)) := by
      intro Φ hΦ
      have := QuietDecay.isBoxSmooth_srcW η u α hΦ (by omega : d.1 - 1 ≤ r + D) ℓ
      exact γ.map.contDiff.comp (boxSmooth_slice (this.mono (by omega) (by omega)) z)
    refine ⟨hc.smul (hw h₁), hc.smul (hw h₂), ?_⟩
    have hjw := srcW_sameJetX η X₀ h₁ h₂ u α (r := r) (by omega)
      (sameJetX_mono (by omega) hj) ℓ z
    have hjw' := sameJet_clm γ.map
      (boxSmooth_slice ((QuietDecay.isBoxSmooth_srcW η u α h₁ (by omega : d.1 - 1 ≤ r + D)
        ℓ).mono (by omega) (by omega)) z)
      (boxSmooth_slice ((QuietDecay.isBoxSmooth_srcW η u α h₂ (by omega : d.1 - 1 ≤ r + D)
        ℓ).mono (by omega) (by omega)) z) hjw
    exact sameJet_bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v) X₀ r _ _ _ hc
      (hw h₁) (hw h₂) hjw'
  exact sameJet_pi (fun v => (hv v).1) (fun v => (hv v).2.1) (fun v => (hv v).2.2)

end Source

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jet-locality step, `liftFluxX` at finite regularity**.

Equal jets of order `s + Dm + N` at `X₀` of the coarse fields `a₁(t, ·), a₂(t, ·)` give equal
`X`-jets of order `s` of `liftFluxX Q Cc a_i hh n t · z k`, at every `z`
(`liftFlux_sameJet`, the statement `LiftFluxStatement`). The four terms:
`T1` (a function of `z` times `liftApply`), `T2` (`G(X)` times the fast partial), `T3` (`G(X)` times
the slow partial; one more `X`-derivative, covered by the `Dm ≥ 1` reserve), `T4` (the source flux
`ε`-coefficients, from `SrcCoeffStatement`). Mirrors `liftFluxX_box`.

For `n = 1` one has `T3 = 0`, and for `hh = 0` one has `T4 = 0`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem triple_congr {s : ℕ} {x : Vec 2} {f g f' g' : Vec 2 → E} (hf : ∀ y, f y = f' y)
    (hg : ∀ y, g y = g' y) (h : Triple s x f g) : Triple s x f' g' := by
  have e1 : f = f' := funext hf
  have e2 : g = g' := funext hg
  subst e1 e2
  exact h

theorem triple_neg {s : ℕ} {x : Vec 2} {f g : Vec 2 → E} (h : Triple s x f g) :
    Triple s x (fun y => -f y) (fun y => -g y) :=
  triple_congr (fun y => by simp) (fun y => by simp) (triple_smul (-1) h)

theorem triple_add {s : ℕ} {x : Vec 2} {f₁ f₂ g₁ g₂ : Vec 2 → E} (h₁ : Triple s x f₁ f₂)
    (h₂ : Triple s x g₁ g₂) :
    Triple s x (fun y => f₁ y + g₁ y) (fun y => f₂ y + g₂ y) :=
  ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, sameJet_add h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 h₂.2.2⟩

theorem triple_sub {s : ℕ} {x : Vec 2} {f₁ f₂ g₁ g₂ : Vec 2 → E} (h₁ : Triple s x f₁ f₂)
    (h₂ : Triple s x g₁ g₂) :
    Triple s x (fun y => f₁ y - g₁ y) (fun y => f₂ y - g₂ y) :=
  triple_congr (fun y => by simp [sub_eq_add_neg]) (fun y => by simp [sub_eq_add_neg])
    (triple_add h₁ (triple_neg h₂))

/-- Real-valued `C^s` factor times a triple. -/
theorem triple_mul {s : ℕ} {x : Vec 2} {c : Vec 2 → ℝ} {f g : Vec 2 → E}
    (hc : ContDiff ℝ (↑s : ℕ∞) c) (h : Triple s x f g) :
    Triple s x (fun y => c y • f y) (fun y => c y • g y) :=
  ⟨hc.smul h.1, hc.smul h.2.1,
    sameJet_bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) x s c f g hc h.1 h.2.1
      h.2.2⟩

/-- The `X`-slice of a box smooth field with equal jets is a triple. -/
theorem slice_triple {s : ℕ} {X₀ : Vec 2} {Φ₁ Φ₂ : Vec 2 → Vec 2 → E} (z : Vec 2)
    (h₁ : IsBoxSmooth s s Φ₁) (h₂ : IsBoxSmooth s s Φ₂) (hj : SameJetX s X₀ Φ₁ Φ₂) :
    Triple s X₀ (fun X => Φ₁ X z) (fun X => Φ₂ X z) :=
  ⟨boxSmooth_slice h₁ z, boxSmooth_slice h₂ z, hj z⟩

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- `liftFluxX` at finite regularity. -/
theorem liftFlux_sameJet : LiftFluxStatement := by
  intro ι _ h _ _ Dm Q Cc a₁ a₂ hh n t k s N H X₀ hDm hhH hz hb hG hv hedge ha₁ ha₂ hj z
  have hbox : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t) →
      ∀ hh' ≤ H, ∀ n', IsBoxSmooth (s + Dm) (s + Dm) (fun X z => liftApply n' (Cc hh' n') a t X z) :=
    fun {a} ha hh' hh'H n' => CovFluxReg.liftApply_box Cc a t hh' n' N (s + Dm) (hz hh' hh'H)
      (hb hh' hh'H) ha
  have hLj : ∀ hh' ≤ H, ∀ n', SameJetX (s + Dm) X₀ (fun X z => liftApply n' (Cc hh' n') a₁ t X z)
      (fun X z => liftApply n' (Cc hh' n') a₂ t X z) := fun hh' hh'H n' =>
    liftApply_sameJet Cc a₁ a₂ t hh' n' (s + Dm) N X₀ (hz hh' hh'H) (hb hh' hh'H) ha₁ ha₂ hj
  -- the triple of the lifted fields in `X`, at the fixed `z`
  have hLt : ∀ hh' ≤ H, ∀ n', ∀ m ≤ s + Dm, Triple m X₀
      (fun X => liftApply n' (Cc hh' n') a₁ t X z) (fun X => liftApply n' (Cc hh' n') a₂ t X z) := by
    intro hh' hh'H n' m hm
    exact slice_triple z ((hbox ha₁ hh' hh'H n').mono hm hm) ((hbox ha₂ hh' hh'H n').mono hm hm)
      (sameJetX_mono hm (hLj hh' hh'H n'))
  suffices hT : Triple s X₀ (fun X => liftFluxX Q Cc a₁ hh n t X z k)
      (fun X => liftFluxX Q Cc a₂ hh n t X z k) from hT.2.2
  simp only [liftFluxX]
  refine triple_sub (triple_add (triple_sub ?_ ?_) ?_) ?_
  · -- T1
    exact triple_smul _ (hLt hh hhH (n - 1) s (by omega))
  · -- T2
    refine triple_smul _ (triple_sum _ fun j _ => triple_mul (hG j) ?_)
    have hfs : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t) →
        IsBoxSmooth s s (fastPartial j (fun X z => liftApply (n - 1) (Cc hh (n - 1)) a t X z)) :=
      fun {a} ha => fast_slice (hbox ha hh hhH (n - 1)) (by omega) j
    exact slice_triple z (hfs ha₁) (hfs ha₂)
      (fastPartial_sameJetX ((hbox ha₁ hh hhH (n - 1)).mono (by omega) (by omega))
        ((hbox ha₂ hh hhH (n - 1)).mono (by omega) (by omega))
        (sameJetX_mono (by omega) (hLj hh hhH (n - 1))) j)
  · -- T3
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      refine triple_neg (triple_smul _ (triple_sum _ fun j _ =>
        triple_mul (hG j) ?_))
      have hss : ∀ {a : ℝ → Vec 2 → ∀ i, h i}, ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t) →
          IsBoxSmooth s s (slowPartial j (fun X z => liftApply (n - 2) (Cc hh (n - 2)) a t X z)) :=
        fun {a} ha => slow_slice (hbox ha hh hhH (n - 2)) (by omega) j
      exact slice_triple z (hss ha₁) (hss ha₂)
        (slowPartial_sameJetX (sameJetX_mono (by omega) (hLj hh hhH (n - 2))) j)
    · simp only [h2, ite_false]
      exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩
  · -- T4
    by_cases h0 : hh = 0
    · simp only [h0, ite_true]
      exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩
    · simp only [h0, ite_false]
      refine triple_sum _ fun j hj' => ?_
      have hj'' := Finset.mem_Icc.mp hj'
      have hℓ : j - 1 < Dm := by have := Finset.mem_Icc.mp hj'; omega
      have hDs : Dm ≤ s + Dm + 1 := by omega
      have hΦ₁ := hbox ha₁ (hh - 1) (by omega) (n - j)
      have hΦ₂ := hbox ha₂ (hh - 1) (by omega) (n - j)
      have hsrc := srcCoeff_sameJetX Q.edge Q.η t _ _ k (j - 1) s X₀ (hedge h0)
        (by simpa using hΦ₁) (by simpa using hΦ₂)
        (sameJetX_mono (le_of_eq (by ring)) (hLj (hh - 1) (by omega) (n - j))) z
      have hT : Triple s X₀
          (fun X => CovFluxReg.SrcCoeff Q.edge Q.η t
            (fun X z => liftApply (n - j) (Cc (hh - 1) (n - j)) a₁ t X z) k (j - 1) X z)
          (fun X => CovFluxReg.SrcCoeff Q.edge Q.η t
            (fun X z => liftApply (n - j) (Cc (hh - 1) (n - j)) a₂ t X z) k (j - 1) X z) :=
        ⟨boxSmooth_slice (CovFluxReg.isBoxSmooth_srcCoeff Q.edge Q.η t _ k (j - 1)
            (s := s) (N := s + Dm) (hedge h0) hΦ₁ (by omega)) z,
          boxSmooth_slice (CovFluxReg.isBoxSmooth_srcCoeff Q.edge Q.η t _ k (j - 1)
            (s := s) (N := s + Dm) (hedge h0) hΦ₂ (by omega)) z, hsrc⟩
      refine triple_congr (fun X => ?_) (fun X => ?_)
        (triple_smul (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹)
          (triple_smul ((j - 1).factorial : ℝ) hT))
      · rw [CovFluxReg.iteratedDeriv_sourceFlux Q.edge Q.η t _ hΦ₁ hDs k X z hℓ]
      · rw [CovFluxReg.iteratedDeriv_sourceFlux Q.edge Q.η t _ hΦ₂ hDs k X z hℓ]

end Lift

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! Transfer collapse, one active finer slot in one coarser piece. The coarser
slot `p` has level `m`, the finer slot `k` level `m + 1 = G.level`; both are active at the time
`t` (nonzero cutoffs).

* `tc_single_pulse_avail`: on the availability interval of `k` only the pulse `p` of level `m`
  acts (the interval is within `τ_m/24` of `t` by the carrier start, and `t` within `(5/4)τ_m` of
  the centre of `p`).
* `tc_slot_jacobian`: the transfer Jacobians read by `transferAt` at the native context of `p`
  recentred at `y` are the inverse Jacobians of the label change, translated.
* `tc_slot_coeff`: the coefficients read by `transferAt` (label `0` of the appended child) are
  those of the finer native family at the finer label of the point: the appended child is
  admissible (`appendChild_admissible`), has the history geometry of the recentred native family
  (`tc_appendChild_histEq`), so the finer outputs agree as germs by the carried history invariant
  (`fluxOp_germ_of_histEq`), and the centered coefficient expansion (i) moves the label. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.QuietAtlas Providers.GenSem

/-- A nonzero cutoff puts the time within `(5/4) τ` of the centre of the slot. -/
theorem ocCutoff_ne_zero_abs_lt {α q : ℝ} {Λ m : ℕ} (hτ : 0 < ocTau α q Λ m) {k : ℤ} {t : ℝ}
    (h : ocCutoff α q Λ m k t ≠ 0) :
    |t - (k : ℝ) * ocTau α q Λ m| < 5 / 4 * ocTau α q Λ m := by
  unfold ocCutoff at h
  have hpos : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    by_contra hneg
    exact h (Real.smoothTransition.zero_of_nonpos (not_lt.mp hneg))
  have h2 : 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 5 / 2 := by linarith
  rw [div_lt_iff₀ hτ] at h2
  linarith

/-- **Only the coarser pulse `p` acts on the availability interval of an active finer slot.** -/
theorem tc_single_pulse_avail {D : OCData} (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {b : ℝ} {j₀ : ℕ}
    (hstart : IsCarrierStart D.α D.q D.Λ b 1 1 j₀) (Mtop : ℕ) {m : ℕ} (hm : 1 ≤ m) (hj : j₀ ≤ m)
    {p : ℤ} (hp : Odd p) {k : ℤ} {t : ℝ} (hcp : ocCutoff D.α D.q D.Λ m p t ≠ 0)
    (hck : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0) :
    ∀ u ∈ availInterval D Mtop (m + 1) k, SinglePulseAt D m p u := by
  intro u hu
  have hτ : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  obtain ⟨h1, h2⟩ := active_child_availInterval_subset hΛ le_rfl hstart Mtop m hj k t hck hu
  have hp' := abs_lt.mp (ocCutoff_ne_zero_abs_lt hτ hcp)
  refine singlePulseAt_of_near hseq hζ hΛ hm hp (abs_lt.mpr ⟨?_, ?_⟩)
  · linarith [hp'.1]
  · linarith [hp'.2]

/-- **The transfer Jacobians at the recentred native context** are the inverse Jacobians of the
label change, translated by the label. -/
theorem tc_slot_jacobian {D : OCData} (hζ : IsFastProfile D.ζ) {m : ℕ} (hm : 1 ≤ m)
    (hε : D.eps m ≠ 0) (p k : ℤ) (t : ℝ) (y : Vec 2)
    (hsp : ∀ v ∈ Set.uIcc t (D.slotAnchor (m + 1) k), SinglePulseAt D m p v) :
    (fun h : Vec 2 => (childTransition D k t ((⟨m - 1, [p], y, []⟩ : RealChain).recenter D h)
        ((D.eps m)⁻¹ • y + (D.eps m)⁻¹ • h))⁻¹) =
      fun h => chartInvJacobian (labelChange D m p k t) (y + h) := by
  funext h
  rw [StrainPhysical.recenter_native, ← smul_add]
  exact tc_childTransition_inv hζ hm hε p k t (y + h) hsp

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The recentring shift gives the covariance of the old fluxes at the output times. -/
theorem fluxRecenterCovariantOnPulses_of_shift (hΛ : 1 ≤ D.Λ) {G : GenStage D hr Dm b j₀}
    (h : FluxRecenterShift G) : FluxRecenterCovariantOnPulses G := by
  intro p c v u γ d I t ht Y z hadm
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have h1 := h p c.1 c.2 (D.eps (G.level - 1) • Y) hadm t ht v u γ d I 0 z
  rw [inv_smul_smul₀ hε, zero_add] at h1
  exact h1.symm

/-- **The coefficients read by the transfer are those of the finer native family** at the finer
label of the point. -/
theorem tc_slot_coeff
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (hin : StageSuccessor.Input P Mn G) (hT : TransferInput Mn G) {m : ℕ} (hL : G.level = m + 1)
    (s : SuccSource G) (hv : s.Valid Mn.A Mn.J) (hnd : ¬ s.IsDiag)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) {p : ℤ} (hp : Odd p) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hcp : ocCutoff D.α D.q D.Λ m p t ≠ 0) (hck : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0)
    (y : Vec 2) (d : ℕ) (J : DerivativeWord2 (d - 1)) :
    fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t
        ((⟨m - 1, [p], y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • y))) d J 0 =
      fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t
        (nativeChain G.level k)) d J (labelChange D m p k t y) := by
  obtain ⟨Mtop, hinv⟩ := hT.history
  obtain ⟨kI, hcert⟩ := hin.context
  have hΛ := hin.base
  have hζ := hin.profile
  have hκ := hin.band
  have hlev := hin.level
  have hm1 : 1 ≤ m := by omega
  have hjm : j₀ ≤ m := by omega
  have hε : D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hτk : 0 < ocTau D.α D.q D.Λ (m + 1) := Construction.Stream.ocTau_pos hΛ
  have hτp : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  have hsp := tc_single_pulse_avail hT.stream hζ hΛ hT.start Mtop hm1 hjm hp hcp hck
  have htk : t ∈ ocPulseWindow D.α D.q D.Λ (m + 1) k :=
    mem_ocPulseWindow_of_ocCutoff_ne_zero hτk hck
  have htav : t ∈ availInterval D Mtop (m + 1) k := mem_availInterval_of_ocCutoff D hΛ hck
  have hsav : D.slotAnchor (m + 1) k ∈ availInterval D Mtop (m + 1) k :=
    slotAnchor_mem_availInterval D Mtop (m + 1) k
  have hhist := tc_appendChild_histEq hζ hm1 hε p k t y
    (I := availInterval D Mtop (m + 1) k)
    (fun u hu v hv => hsp v (uIcc_subset_availInterval D Mtop (m + 1) k hsav hu hv))
    (fun v hv => hsp v (uIcc_subset_availInterval D Mtop (m + 1) k htav hsav hv))
  -- admissibility of the two chains
  have hch : IsAdmissibleChain D b j₀ m p ⟨m - 1, [p], y, []⟩ :=
    nativeChain_isCarrier D b j₀ m p 2 hm1 hjm hp y
  have hsch : IsScheduledIn D m k p :=
    ⟨t, Function.mem_support.mpr hck, mem_ocPulseWindow_of_ocCutoff_ne_zero hτp hcp⟩
  have hA : IsAdmissibleChain D b j₀ (m + 1) k
      ((⟨m - 1, [p], y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • y)) :=
    appendChild_admissible D hΛ hζ hin.bandwidth
      (startBound_of_carrierStart hΛ le_rfl le_rfl hT.start) m p _ hch k hk hsch t hck _
  have hB : IsAdmissibleChain D b j₀ (m + 1) k ⟨m, [k], labelChange D m p k t y, []⟩ :=
    nativeChain_isCarrier D b j₀ (m + 1) k 2 (by omega) (by omega) hk _
  have hN : IsAdmissibleChain D b j₀ (m + 1) k (nativeChain (m + 1) k) :=
    nativeChain_isCarrier D b j₀ (m + 1) k 2 (by omega) (by omega) hk 0
  have hBeq : (⟨m, [k], labelChange D m p k t y, []⟩ : RealChain) =
      (nativeChain (m + 1) k).recenter D (labelChange D m p k t y) := by
    rw [nativeChain_recenter]
    rfl
  rw [← hL] at hA hB hN hhist htk hBeq
  -- the finer outputs agree as germs at the label `0`
  have hshift : FluxRecenterShift G := fluxRecenterShift_of_oldCert hΛ hζ hcert.oldCert
  have hc2 := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hgerm := fun f : Vec 2 → ℝ => fluxOp_germ_of_histEq hζ hΛ hc2
    (fluxRecenterCovariantOnPulses_of_shift hΛ hshift) hinv Mn Mn.anchor s Cc hLF ⟨k, hk⟩ hA hB
    hhist htk f
  have e1 : fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t
        ((⟨m - 1, [p], y, []⟩ : RealChain).appendChild D k t ((D.eps m)⁻¹ • y))) d J 0 =
      fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k t
        ⟨m, [k], labelChange D m p k t y, []⟩) d J 0 := by
    unfold fluxCoeff
    rw [(hgerm _).eq_of_nhds]
  rw [e1, hBeq]
  have hBadm : IsAdmissibleChain D b j₀ G.level k
      ((nativeChain G.level k).recenter D (labelChange D m p k t y)) := hBeq ▸ hB
  exact fluxCoeff_recenter (fun f => (centeredCoefficient_expansion P Mn G hin s hv hnd Cc hLF k
    hk t htk (nativeChain G.level k) hN (labelChange D m p k t y) hBadm).1 f) d J

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Transfer collapse of the flux cancellation: **the transfer to the coarser chart collapses to the
finer natural chart**, statements and assembly. The conclusion is
`TransferredIdentityEulerianOnStatement`.

Proved: the identification of the appended child with the recentred finer native family at every
time of nonzero weight, in the three forms the transfer reads (`tc_single_pulse_avail`,
`tc_slot_jacobian`, `tc_slot_coeff`). Together with the centered coefficient expansion
(`centeredCoefficient_expansion`) this is the content of the piece.

Two named steps of finite algebra:
* `TransferPieceEulerianStatement` (step A: `transferPieceEulerian`): one coarser piece of nonzero
  weight gives the Eulerian operator of the source.
* `TransferPieceCollapseStatement` (step B: `transferPieceCollapse`): the sum over the coarser
  pieces collapses (`ocCutoff_finsum_one`).
`transferChartCollapse_of_steps` assembles `TransferChartCollapseStatement` from them; it uses
neither the Piola-transport step nor the centered coefficient expansion as hypotheses
(`transportedCoeff_flux_orders_of_contDiff` and `centeredCoefficient_expansion` are used
directly), so the transfer collapse takes no such hypothesis.
Transfer collapse itself is `transferChartCollapse`. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **Step A of the transfer collapse (one coarser piece gives the Eulerian operator).** For an identity of `G'`
other than a first source, a coarser slot `p` of nonzero weight at the time `t`, a field of class
`C^{Dm-1}`, a point `x` and a flux index `κ`: the array of the piece `p` (the transport along
`Υ = Φ_p(t,·)⁻¹` of the dimensional samples at the native context, as in `constituentPhysical`),
contracted with the jets of the field through the map of the identity, is `lam` times the
component `κ` of `fluxOpApply Dm (sourceEulerOp …)` (written out).
Proof: `transferPieceEulerian`.
Route (`m = G'.level`, `G.level = m + 1`, `y = Υ x`):
1. for `d' ≥ 2` the sample is `lam • ∑ k ∈ activeSlots D hΛ m t, ϖ_{m+1,k}(t) •
   transportedCoeff K_k Dγ B_k (d'-1) I 0` (`W.spec`, the natural pieces and native contexts of
   `G'`, `nativeChain_recenter`, `nativeChain_isCarrier`, `Providers.QuietAtlas.dim_transferAt`
   with `κ_m ≠ 0` from `weakData_kap_pos`);
2. `tc_slot_jacobian` with `transportedCoeff_translate` turn `K_k` into
   `chartInvJacobian (labelChange D m p k t)` at `y`; `tc_slot_coeff` turns `B_k` into the
   coefficients of the finer native family at the label `labelChange D m p k t y`;
3. `transportedCoeff_congr` (the outer transport reads the orders `≥ 2` only),
   `transportedCoeff_smul`, `transportedCoeff_finset_sum`, then `transportedCoeff_comp` (with
   `hder_of_inverse` for `Υ` and the material map) and `chartInvJacobian_comp`: the outer transport
   of the inner one is the transport along `labelChange ∘ Υ = X_m(s_k, ·, t)`
   (`flowOf_labelChange`), the inverse of the finer natural chart, word by word;
4. on the right, `fluxCoeff` is linear in the operator, the glue over `ocObsPulses` is the sum
   over `activeSlots` (zero cutoffs drop), and for each `k` the permutation sums of
   `fluxCoeff (pushFlux Ψ_k Ψ_k⁻¹ (fop k t native))` are those of the same transported array
   (`centeredCoefficient_expansion` (ii) at the label `X_m(s_k, x, t)` of the native chain on the
   smooth field `mono x I ∘ Ψ_k`, then `transportedCoeff_flux_orders_of_contDiff` with
   `χ = Ψ_k`, `ψ = Ψ_k⁻¹`, `V = mono x I ∘ Ψ_k`, and `sum_orderedDerivative_mono`); the weights
   `C (∂^A f x)` are symmetric (`orderedDerivative_comp_perm_of_contDiff`), so
   `CycleComparison.Reconstruction.sum_word_smul_eq_of_perm_sum` concludes.
The maximal orders agree: `(G'.fam.identity ..).maxOrder` is the order of the tags of the source
(`HasTags` of `G'`, `W.spec`), which is the order in `centeredCoefficient_expansion`. -/
def TransferPieceEulerianStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → IsActualSuccessor D P Mn G G' → TransferInput Mn G →
    ∀ (W : SplitWitness P Mn G G') (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
    ¬ (W.e v' u' γ').1.IsDiag →
    ∀ (p : OddSlot) (t : ℝ), ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 →
    ∀ (f : Vec 2 → hr u'.1.root), ContDiff ℝ (Dm - 1 : ℕ) f → ∀ (x : Vec 2) (κ : Fin 2),
      ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (G'.fam.identity v' u' γ').maxOrder
          (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
            (G'.actual p) v' u' γ' d' I t (((G'.fam.piece p).material t).symm x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
          (d - 1) A x κ • (G'.fam.identity v' u' γ').map (orderedDerivative A f x) =
      (W.e v' u' γ').1.lam G.level Mn.η0 •
        ∑ d ∈ Finset.Icc 2 Dm, ∑ I : DerivativeWord2 (d - 1),
          fluxCoeff (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
            (W.e v' u' γ').1 (W.Cc (W.e v' u' γ').1) t) d I x κ •
            (G'.fam.identity v' u' γ').map (orderedDerivative I f x)

/-- **Step B of the transfer collapse (the sum over the coarser pieces collapses).** From step A.
Proof: `transferPieceCollapse`. Route: `G'.physCoeff` is `constituentPhysical`, a `finsum` over the
odd slots of `weight p t •` the operator of the piece; the weights are the cutoffs (`IsNatural` of
`G'`), nonzero for finitely many slots (`CycleReference.ocCutoff_support_finite`), so the
`finsum` is a finite sum (`CycleJointProofs.piece_finsum_eq_window_sum`); apply it to the jet vector
and read the component `κ` (`PiLp.continuousLinearEquiv`, `ContinuousLinearMap.pi`, `PiLp.proj`);
exchange the sums over the orders and the pieces; step A on every piece of nonzero weight; the
weights add to one (`WeakEntryProofs.ocCutoff_finsum_one`); `fluxOpApply` is the written-out right
side of step A by definition. The orders `d ∈ Finset.Icc 2 Dm` as a subtype sum:
`Finset.sum_coe_sort`. -/
def TransferPieceCollapseStatement : Prop :=
  TransferPieceEulerianStatement → TransferredIdentityEulerianOnStatement

/-- **Transfer collapse from its two steps.** Neither the Piola-transport step nor the centered coefficient expansion enters as a hypothesis. -/
theorem transferChartCollapse_of_steps (hA : TransferPieceEulerianStatement)
    (hB : TransferPieceCollapseStatement) : TransferChartCollapseStatement :=
  fun _ _ => hB hA

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Transfer collapse, the Eulerian side of step A: **the symmetric
coefficients of a pushed-forward label operator are the permutation sums of the transported label
coefficients**.

For a label flux operator `L` which at the label `Ψ⁻¹ x` is, on smooth fields, the differential
operator of its coefficients of the orders `1 ≤ d ≤ K` (clause (ii) of the centered coefficient expansion with the
zeroth-order term kept), and a smooth chart `Ψ` with smooth inverse,
`(d-1)! · fluxCoeff (pushFlux Ψ Ψ⁻¹ L) d I x = ∑_σ transportedCoeff (DΨ⁻¹)⁻¹ K B (d-1) (I∘σ) x`
for `d ≥ 2`, `B` the coefficients of `L` at `Ψ⁻¹ x` (`tc_fluxCoeff_pushFlux`). Proof: test `L` on
`mono x I ∘ Ψ`, whose value at the label vanishes, and read the result through the finite-order
Piola identity `transportedCoeff_flux_orders_of_contDiff` on the monomial. This is step 4 of the
route of `TransferPieceEulerianStatement`, for one finer slot. `tc_transport_comp` is step 3 for
one finer slot: the two transports compose into the transport along the inverse of the finer
natural chart (`transportedCoeff_comp`). -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.GenSem CycleComparison.Reconstruction

/-- The transported array vanishes at the word lengths `r ≥ Dγ`. -/
theorem transportedCoeff_eq_zero_of_le (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) {Dγ r : ℕ}
    (h : Dγ ≤ r) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (A : DerivativeWord2 r)
    (y : Vec 2) : transportedCoeff K Dγ B r A y = 0 := by
  funext a₀
  unfold transportedCoeff
  rw [Finset.Icc_eq_empty (by omega)]
  simp

/-- **The symmetric coefficients of the push-forward** of a label operator of finite order. -/
theorem tc_fluxCoeff_pushFlux {Ψ Ψi : Vec 2 → Vec 2} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨi : ContDiff ℝ (⊤ : ℕ∞) Ψi) (h1 : ∀ y, Ψi (Ψ y) = y) (h2 : ∀ x, Ψ (Ψi x) = x)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (K : ℕ) (x : Vec 2)
    (hfo : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L g (Ψi x) = ∑ d ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d - 1),
        orderedDerivative J g (Ψi x) • fluxCoeff L d J (Ψi x))
    {d : ℕ} (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) (a₀ : Fin 2) :
    ((d - 1).factorial : ℝ) * fluxCoeff (pushFlux Ψ Ψi L) d I x a₀ =
      ∑ σ : Equiv.Perm (Fin (d - 1)),
        transportedCoeff (chartInvJacobian Ψi) K (fun d' J => fluxCoeff L d' J (Ψi x)) (d - 1)
          (I ∘ σ) x a₀ := by
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (mono x I) := (contDiff_mono x I).of_le le_top
  have hVs : ContDiff ℝ (⊤ : ℕ∞) (mono x I ∘ Ψ) := hmono.comp hΨ
  have hVψ : (mono x I ∘ Ψ) ∘ Ψi = mono x I := by
    funext x'
    simp only [Function.comp_apply, h2]
  have hp2 := transportedCoeff_flux_orders_of_contDiff hΨ hΨi h1 h2 (n := K)
    (V := mono x I ∘ Ψ) (hVs.of_le (by exact_mod_cast le_top)) K (Nat.le_succ K)
    (fun d' J => fluxCoeff L d' J (Ψi x)) x a₀
  rw [hVψ] at hp2
  -- the left side of the Piola identity on the monomial
  have hL2 : (∑ d' ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d' - 1),
      transportedCoeff (chartInvJacobian Ψi) K (fun d' J => fluxCoeff L d' J (Ψi x)) (d' - 1) A x
        a₀ • orderedDerivative A (mono x I) x) =
      ∑ σ : Equiv.Perm (Fin (d - 1)),
        transportedCoeff (chartInvJacobian Ψi) K (fun d' J => fluxCoeff L d' J (Ψi x)) (d - 1)
          (I ∘ σ) x a₀ := by
    by_cases hdK : d ≤ K
    · rw [Finset.sum_eq_single d]
      · rw [← sum_orderedDerivative_mono x I (fun A =>
          transportedCoeff (chartInvJacobian Ψi) K (fun d' J => fluxCoeff L d' J (Ψi x)) (d - 1)
            A x a₀)]
        exact Finset.sum_congr rfl fun A _ => by rw [smul_eq_mul, smul_eq_mul, mul_comm]
      · intro d' hd' hne
        refine Finset.sum_eq_zero fun A _ => ?_
        rw [orderedDerivative_mono_of_ne x I A
          (by have := (Finset.mem_Icc.mp hd').1; omega), smul_zero]
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨by omega, hdK⟩) h
    · rw [Finset.sum_eq_zero fun d' hd' => Finset.sum_eq_zero fun A _ => ?_,
        Finset.sum_eq_zero fun σ _ => ?_]
      · rw [transportedCoeff_eq_zero_of_le _ (by omega)]
        rfl
      · rw [orderedDerivative_mono_of_ne x I A
          (by have := (Finset.mem_Icc.mp hd').2; omega), smul_zero]
  -- the right side: the operator on `mono x I ∘ Ψ`, read through the inverse Jacobian
  have hR2 : (∑ d' ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d' - 1), ∑ i₀ : Fin 2,
      (chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀) •
        orderedDerivative J (mono x I ∘ Ψ) (Ψi x)) =
      ∑ i₀ : Fin 2, chartInvJacobian Ψi x a₀ i₀ * L (mono x I ∘ Ψ) (Ψi x) i₀ := by
    rw [hfo _ hVs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : ∀ d' : ℕ, (∑ J : DerivativeWord2 (d' - 1), ∑ i₀ : Fin 2,
        chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀ *
          orderedDerivative J (mono x I ∘ Ψ) (Ψi x)) =
        ∑ i₀ : Fin 2, ∑ J : DerivativeWord2 (d' - 1),
          chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀ *
            orderedDerivative J (mono x I ∘ Ψ) (Ψi x) := fun d' => Finset.sum_comm
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun d' _ =>
      Finset.sum_congr rfl fun J _ => ?_
    ring
  have hjac : chartInvJacobian Ψi x = jacMatrix Ψ (Ψi x) := by
    rw [chartInvJacobian_eq_of_inverse (hΨ.differentiable (by simp))
      (hΨi.differentiable (by simp)) h1 h2 x]
    rfl
  have hfact : ((d - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [← hL2, hp2, hR2, hjac]
  unfold fluxCoeff pushFlux
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [← mul_assoc, mul_inv_cancel₀ hfact, one_mul]
  rfl

/-- **The transport along the coarser chart of the transport along the label change** is the
transport along their composite (the inverse of the finer natural chart), word by word and at
every order. `Υ` is the inverse of the coarser material map `Φ`, `φ` the label change; the inner
array is read at the label `Υ x` through the translated Jacobians, as `transferAt` does
(`tc_slot_jacobian`). This is step 3 of the route of `TransferPieceEulerianStatement`. -/
theorem tc_transport_comp {Υ Φ φ φi : Vec 2 → Vec 2} (hΥ : ContDiff ℝ (⊤ : ℕ∞) Υ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΥΦ : ∀ y, Υ (Φ y) = y) (hΦΥ : ∀ x, Φ (Υ x) = x)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφi : ContDiff ℝ (⊤ : ℕ∞) φi) (h1 : ∀ y, φi (φ y) = y)
    (h2 : ∀ y, φ (φi y) = y) (Dγ : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ)
    (A : DerivativeWord2 r) (x : Vec 2) :
    transportedCoeff (chartInvJacobian Υ) Dγ
        (fun e J => transportedCoeff (fun h => chartInvJacobian φ (Υ x + h)) Dγ B (e - 1) J 0)
        r A x =
      transportedCoeff (chartInvJacobian (φ ∘ Υ)) Dγ B r A x := by
  have hK₁ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x' => chartInvJacobian Υ x' a i :=
    chartInvJacobian_entry_contDiff hΦ hΥ hΥΦ hΦΥ
  have hK₂ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x' => chartInvJacobian φ x' a i :=
    chartInvJacobian_entry_contDiff hφi hφ h2 h1
  have hcomp : (fun x' => chartInvJacobian Υ x' * chartInvJacobian φ (Υ x')) =
      chartInvJacobian (φ ∘ Υ) := funext fun x' =>
    (Providers.QuietAtlas.chartInvJacobian_comp x' (hφ.differentiable (by simp) _)
      (hΥ.differentiable (by simp) _)).symm
  have e : (fun (e : ℕ) (J : DerivativeWord2 (e - 1)) =>
      transportedCoeff (fun h => chartInvJacobian φ (Υ x + h)) Dγ B (e - 1) J 0) =
      fun e J => transportedCoeff (chartInvJacobian φ) Dγ B (e - 1) J (Υ x) := by
    funext e J
    rw [Providers.QuietAtlas.transportedCoeff_translate, add_zero]
  rw [e, ← hcomp, Providers.QuietAtlas.transportedCoeff_comp hK₁ hK₂ hΥ
    (Providers.QuietAtlas.hder_of_inverse (hΦ.differentiable (by simp))
      (hΥ.differentiable (by simp)) hΥΦ hΦΥ)]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! Transfer collapse, step B: **the sum over the coarser pieces collapses**.

`G'.physCoeff` is `constituentPhysical`, the sum over the odd slots of the weight of the piece
times the operator of its transported array. At a fixed time it is a finite sum
(`constituentPhysical_eq_window_sum` on the window `[t, t]`), whose component `κ` on a jet vector
is written out in `tc_physCoeff_apply`. The weights of `G'` are the cutoffs (`IsNatural`, from
`IsActualSuccessor`) and add to one (`ocCutoff_finsum_one`, `tc_weight_sum_one`). A piece of zero
weight contributes nothing; a piece of nonzero weight contributes the Eulerian operator of the
source by step A (`TransferPieceEulerianStatement`), which does not depend on the piece. This
proves `TransferPieceCollapseStatement` (`transferPieceCollapse`), and the transfer collapse is reduced to step A
alone (`transferChartCollapse_of_eulerian`). -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The component `κ` of the physical coefficient on a jet vector**, as the finite sum over the
pieces whose output meets the time. -/
theorem tc_physCoeff_apply (G' : GenStage D hr Dm b j₀) (v' u' : CompIn G'.comps)
    (γ' : G'.fam.Γ v' u') (d : ℕ) (t : ℝ) (x : Vec 2)
    (J : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u'.1.root)) (κ : Fin 2) :
    G'.physCoeff v' u' γ' d t x J κ =
      ∑ p ∈ (G'.fam.locally_finite t t).toFinset, G'.fam.weight p t •
        ∑ A : DerivativeWord2 (d - 1),
          transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
            (G'.fam.identity v' u' γ').maxOrder
            (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
              (G'.actual p) v' u' γ' d' I t (((G'.fam.piece p).material t).symm x)
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
            (d - 1) A x κ • (G'.fam.identity v' u' γ').map (J A) := by
  rw [GenStage.physCoeff, CycleJointProofs.constituentPhysical_eq_window_sum G'.fam _ _ _ G'.actual
    t t t ⟨le_rfl, le_rfl⟩ v' u' γ' d x]
  simp only [_root_.sum_apply, _root_.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, CycleJointProofs.nativeArrayAssembly_apply]

/-- **The weights of a natural stage add to one** over the pieces whose output meets the time. -/
theorem tc_weight_sum_one (G' : GenStage D hr Dm b j₀) {M : ℕ} (hnat : G'.IsNatural M)
    (hΛ : 1 ≤ D.Λ) (t : ℝ) :
    ∑ p ∈ (G'.fam.locally_finite t t).toFinset, G'.fam.weight p t = 1 := by
  rw [← CycleJointProofs.piece_finsum_eq_window_sum G'.fam t t t ⟨le_rfl, le_rfl⟩
    (fun p => G'.fam.weight p t) (fun p hp => G'.fam.weight_zero p t hp),
    ← WeakEntryProofs.ocCutoff_finsum_one D.α D.q D.Λ G'.level
      (Construction.Stream.ocTau_pos hΛ) t]
  exact finsum_congr fun p => hnat.2.1 p t

/-- **Step B of the transfer collapse**: the sum over the coarser pieces collapses. -/
theorem transferPieceCollapse : TransferPieceCollapseStatement := by
  intro hA hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' hin hsucc hT W v' u' γ' hnd t f hf x
  have hnat : G'.IsNatural Mn.M := hsucc.2.2.2.1
  ext κ
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [tc_physCoeff_apply]
  rw [Finset.sum_coe_sort (Finset.Icc 2 Dm) fun d : ℕ =>
    ∑ p ∈ (G'.fam.locally_finite t t).toFinset, G'.fam.weight p t •
      ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (G'.fam.identity v' u' γ').maxOrder
          (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
            (G'.actual p) v' u' γ' d' I t (((G'.fam.piece p).material t).symm x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
          (d - 1) A x κ • (G'.fam.identity v' u' γ').map (orderedDerivative A f x),
    Finset.sum_comm]
  have hpiece : ∀ p ∈ (G'.fam.locally_finite t t).toFinset,
      (∑ d ∈ Finset.Icc 2 Dm, G'.fam.weight p t •
        ∑ A : DerivativeWord2 (d - 1),
          transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
            (G'.fam.identity v' u' γ').maxOrder
            (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
              (G'.actual p) v' u' γ' d' I t (((G'.fam.piece p).material t).symm x)
              ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
            (d - 1) A x κ • (G'.fam.identity v' u' γ').map (orderedDerivative A f x)) =
        G'.fam.weight p t • ((W.e v' u' γ').1.lam G.level Mn.η0 •
          fluxOpApply Dm
            (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (W.e v' u' γ').1
              (W.Cc (W.e v' u' γ').1) t)
            (G'.fam.identity v' u' γ').map f x) κ := by
    intro p _
    rw [← Finset.smul_sum]
    by_cases hw : G'.fam.weight p t = 0
    · rw [hw, zero_smul, zero_smul]
    · rw [hA P Mn G G' hin hsucc hT W v' u' γ' hnd p t (by rw [← hnat.2.1 p t]; exact hw) f hf x κ]
      rfl
  rw [Finset.sum_congr rfl hpiece, ← Finset.sum_smul, tc_weight_sum_one G' hnat hin.base t,
    one_smul]

/-- **Transfer collapse from step A alone.** -/
theorem transferChartCollapse_of_eulerian (hA : TransferPieceEulerianStatement) :
    TransferChartCollapseStatement :=
  transferChartCollapse_of_steps hA transferPieceCollapse

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
