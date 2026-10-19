-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFirstSourceConstGrade0
import AVRegularity.EntryWeakAssembly.StoredSourceCounting
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBoundStep
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Construction.Residual.Presentation.FluxAe
import AVRegularity.CycleComparison.Reconstruction.ChainLinear
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
/-! The path-sum step at positive grades: the assembly.

`hilbertLiftPathSum_of_parts` proves `HilbertLiftPathSumStatement` from the proved grade zero and
two named statements:

* `HLZeroLiftStatement`: the lift of the empty path exists (a grade-zero lift sequence of the
  scalar operator data with no edge on the native chain), as soon as one fibre carries a nonzero
  functional. The hypotheses of the piece give the path lifts from one edge on; the grade induction
  of the decomposition starts from the empty path.
* `HLLowOrderStatement`: the decomposition for `Dm < 2` (no edge at all; the explicit formulas of
  the general case ask for `2 ≤ Dm`).

With them: on the native chain either the setting and the decomposition hold
(`hl_decomposed_or_trivial`), or every fibre is trivial and both sides vanish. The pointwise
identity and the continuity (`hl_pointwise_core`, `hl_pathContinuous_core`) do not use
`HLArrayIdentities`. The cell mean is split by `hl_cellMean_core`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

open CovarianceTransport CovFluxReg
open AVRegularity.Providers.PathDecomp

/-- **The lift of the empty path exists.** From the grade-zero part of the Hilbert lift on the
native chain of the pulse `k`: for a component `v₀` and a functional `ℓ₀` with `ℓ₀ e₀ = 1`, the
scalar arrays `ℓ₀ (CcT k 0 n m α · v₀ v₀ e₀)` are a grade-zero lift sequence of the scalar operator
data with no edge. -/
def HLZeroLiftStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → Mn.N + Dm + 2 ≤ Mn.sX → Mn.N + Dm + 2 ≤ Mn.sZ →
    ∀ (ρ : ℝ) (depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (k : ℤ) (hk : Odd k),
    HLHilbertLift Mn G ρ depth k hk CcT → (HLWindow D G k).Nonempty →
    ∀ (v₀ : CompIn G.comps) (ℓ₀ : hr v₀.1.root →L[ℝ] ℝ) (e₀ : hr v₀.1.root), ℓ₀ e₀ = 1 →
      ∃ C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ), HLZeroLift Mn G ρ k C0

/-- **The decomposition for `Dm < 2`.** With no edge at all, the lift of the fibre and the path
lifts are still the path-candidate arrays of the top entries (their positive grades vanish). -/
def HLLowOrderStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → ActualFluxJointSmooth G →
    Mn.N + Dm + 2 ≤ Mn.sX → Mn.N + Dm + 2 ≤ Mn.sZ →
    ∀ (ρ : ℝ) (depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (k : ℤ) (hk : Odd k) (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)),
    HLHilbertLift Mn G ρ depth k hk CcT → (HLWindow D G k).Nonempty →
    ∀ (g : ℕ), g + 1 ≤ depth →
    ∀ (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)),
      HLPathLifts Mn G ρ k hk hadm g Cπ →
    ∀ (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)), HLZeroLift Mn G ρ k C0 → Dm < 2 →
      HLDecomp.Decomposed G G.level ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        (g + 1) (CcT k) (hlLifts C0 Cπ)

/-- The slow flux of the zero field vanishes. -/
theorem hl_liftFluxX_zero_field {ι : Type} [Fintype ι] {hs : ι → Type}
    [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}
    (Q : LiftOperatorData ι hs Dm) (Cc : ℕ → ℕ → LiftCoeff ι hs) (hh n : ℕ) (t : ℝ)
    (X z : Vec 2) (κ : Fin 2) :
    liftFluxX Q Cc (fun _ _ => 0) hh n t X z κ = 0 := by
  have h := HLDecomp.hl_liftFluxX_field_sum Q Cc (∅ : Finset Unit) (fun _ _ => 0) hh n t X z κ
    (fun k hh' => by
      funext X z
      exact HLDecomp.hl_liftApply_field_sum ∅ k _ _ (by simp) t X z)
    (by simp) (by simp)
  simpa using h

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- When every fibre is trivial the scalar input of a path vanishes. -/
theorem hl_hlIn_eq_zero {G : GenStage D hr Dm b j₀}
    (htriv : ∀ (v : CompIn G.comps) (x : hr v.1.root), x = 0) {h : ℕ} (π : StagePath G h)
    {r : ℕ} (ℓ : hr r →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    hlIn G π ℓ a = fun _ _ => 0 := by
  classical
  funext s' X'
  unfold hlIn
  by_cases hπ : π.src ∈ G.comps
  · simp [hπ, htriv ⟨π.src, hπ⟩ (a s' X' ⟨π.src, hπ⟩)]
  · simp [hπ]

/-- **On the native chain: the setting and the decomposition, or every fibre is trivial.** -/
theorem hl_decomposed_or_trivial [∀ r, CompleteSpace (hr r)] (hZ : HLZeroLiftStatement)
    (hL : HLLowOrderStatement) {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G)
    (hsX : Mn.N + Dm + 2 ≤ Mn.sX) (hsZ : Mn.N + Dm + 2 ≤ Mn.sZ) (ρ : ℝ) {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)} {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hlift : HLHilbertLift Mn G ρ depth k hk CcT)
    (hne : (HLWindow D G k).Nonempty) {g : ℕ} (hd : g + 1 ≤ depth)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : HLPathLifts Mn G ρ k hk hadm g Cπ) :
    (∃ C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ),
      HLDecomp.Setting G G.level k (nativeChain G.level k) ρ ⟨k, hk⟩
        ⟨nativeChain G.level k, hadm⟩ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        (g + 1) Mn.N Mn.sX Mn.sZ (hlLifts C0 Cπ) ∧
      HLDecomp.Decomposed G G.level ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        (g + 1) (CcT k) (hlLifts C0 Cπ)) ∨
      ∀ (v : CompIn G.comps) (x : hr v.1.root), x = 0 := by
  by_cases h : ∃ (v₀ : CompIn G.comps) (x : hr v₀.1.root), x ≠ 0
  · left
    obtain ⟨v₀, x, hx⟩ := h
    have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    have h1 : ((‖x‖ ^ 2)⁻¹ • innerSL ℝ x) x = 1 := by
      simp [inv_mul_cancel₀ hn]
    obtain ⟨C0, hC0⟩ := hZ P Mn G hin hsX hsZ ρ depth CcT k hk hlift hne v₀ _ x h1
    refine ⟨C0, hl_setting hin hE hsX hsZ ρ hk hadm hne g Cπ hπ C0 hC0, ?_⟩
    by_cases hD2 : 2 ≤ Dm
    · exact hl_decomposed_of_two_le hin hE hsX hsZ ρ hk hadm hlift hne hd Cπ hπ C0 hC0 hD2
    · exact hL P Mn G hin hE hsX hsZ ρ depth CcT k hk hadm hlift hne g hd Cπ hπ C0 hC0
        (by omega)
  · right
    intro v x
    by_contra hx
    exact h ⟨v, x, hx⟩

open scoped Classical in
/-- **The pointwise flux identity of the path-sum step** (no array identities assumed). -/
theorem hl_pointwise_core [∀ r, CompleteSpace (hr r)] (hZ : HLZeroLiftStatement)
    (hL : HLLowOrderStatement) {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G)
    (hsX : Mn.N + Dm + 2 ≤ Mn.sX) (hsZ : Mn.N + Dm + 2 ≤ Mn.sZ) (ρ : ℝ) {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)} {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hlift : HLHilbertLift Mn G ρ depth k hk CcT) {g : ℕ} (hd : g + 1 ≤ depth)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : HLPathLifts Mn G ρ k hk hadm g Cπ) {τ : ℝ} (hτ : τ ∈ HLWindow D G k)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (ha : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (a s))
    (n : ℕ) (X : Vec 2) (j : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (z : Vec 2) :
    ℓ (liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v) =
      ∑ᶠ π : StagePath G (g + 1), if π.tgt = v.1 ∧ π.src ∈ G.comps then
        hlPathFlux G ρ k hk hadm g Cπ π ℓ a n τ X z j
      else 0 := by
  rcases hl_decomposed_or_trivial hZ hL hin hE hsX hsZ ρ hk hadm hlift ⟨τ, hτ⟩ hd Cπ hπ with
    ⟨C0, H, Hd⟩ | htriv
  · rw [← hl_native_ctx hin hk hadm]
    exact hl_flux_pointwise_of_decomposed H Hd le_rfl hτ a (ha τ) n X z j v ℓ
  · have h0 := htriv v (liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v)
    rw [h0, map_zero]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun π => ?_
    split_ifs
    · unfold hlPathFlux
      rw [hl_hlIn_eq_zero htriv π ℓ a, hl_liftFluxX_zero_field]
      rfl
    · rfl

/-- **Continuity of the path integrands of the path-sum step** (no array identities assumed). -/
theorem hl_pathContinuous_core [∀ r, CompleteSpace (hr r)] (hZ : HLZeroLiftStatement)
    (hL : HLLowOrderStatement) {P : ProvParams} {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hin : StageSuccessor.Input P Mn G) (hE : ActualFluxJointSmooth G)
    (hsX : Mn.N + Dm + 2 ≤ Mn.sX) (hsZ : Mn.N + Dm + 2 ≤ Mn.sZ) (ρ : ℝ) {depth : ℕ}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)} {k : ℤ} (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k))
    (hlift : HLHilbertLift Mn G ρ depth k hk CcT) {g : ℕ} (hd : g + 1 ≤ depth)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ))
    (hπ : HLPathLifts Mn G ρ k hk hadm g Cπ) {τ : ℝ} (hτ : τ ∈ HLWindow D G k)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (ha : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (a s))
    (n : ℕ) (X : Vec 2) (j : Fin 2) (r : ℕ) (ℓ : hr r →L[ℝ] ℝ) (π : StagePath G (g + 1)) :
    Continuous fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
      (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ (g + 1) π) (hlIn G π ℓ a)
      (g + 1) n τ X z j := by
  rcases hl_decomposed_or_trivial hZ hL hin hE hsX hsZ ρ hk hadm hlift ⟨τ, hτ⟩ hd Cπ hπ with
    ⟨C0, H, Hd⟩ | htriv
  · exact hl_path_continuous_of_decomposed H Hd le_rfl π hτ a (ha τ) ℓ n X j
  · rw [hl_hlIn_eq_zero htriv π ℓ a]
    have e : (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ (g + 1) π) (fun _ _ => 0)
        (g + 1) n τ X z j) = fun _ => 0 := funext fun z => hl_liftFluxX_zero_field _ _ _ _ _ _ _ _
    rw [e]
    exact continuous_const

open scoped Classical in
/-- The cell mean splits over the finite path sum, with the pointwise identity and the continuity
as its only hypotheses. -/
theorem hl_cellMean_core [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {G : GenStage D hr Dm b j₀} (ρ : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) (k : ℤ) (hk : Odd k)
    (hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)) (g : ℕ)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) (τ : ℝ)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (n : ℕ) (X : Vec 2) (j : Fin 2)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ)
    (hpt : ∀ (v' : CompIn G.comps) (ℓ' : hr v'.1.root →L[ℝ] ℝ) (z : Vec 2),
      ℓ' (liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v') =
        ∑ᶠ π : StagePath G (g + 1), if π.tgt = v'.1 ∧ π.src ∈ G.comps then
          hlPathFlux G ρ k hk hadm g Cπ π ℓ' a n τ X z j
        else 0)
    (hco : ∀ (r : ℕ) (ℓ' : hr r →L[ℝ] ℝ) (π : StagePath G (g + 1)),
      Continuous fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ (g + 1) π) (hlIn G π ℓ' a)
        (g + 1) n τ X z j) :
    ℓ (fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j) v) =
      ∑ᶠ π : StagePath G (g + 1), if π.tgt = v.1 ∧ π.src ∈ G.comps then
        fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (pathEdges G π ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩)) (Cπ (g + 1) π) (hlIn G π ℓ a)
          (g + 1) n τ X z j) (Fin.last (g + 1))
      else 0 := by
  have : Fintype (StagePath G (g + 1)) := Fintype.ofFinite _
  have hcomp : ∀ v' : CompIn G.comps, Continuous fun z => liftFluxX
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v' := by
    intro v'
    refine HLTools.hl_continuous_of_functionals fun ℓ' => ?_
    have : (fun z => ℓ' (liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v')) =
        fun z => ∑ π : StagePath G (g + 1), if π.tgt = v'.1 ∧ π.src ∈ G.comps then
          hlPathFlux G ρ k hk hadm g Cπ π ℓ' a n τ X z j else 0 := by
      funext z
      rw [hpt v' ℓ' z, finsum_eq_sum_of_fintype]
    rw [this]
    refine continuous_finsetSum _ fun π _ => ?_
    split_ifs
    · exact (continuous_apply (Fin.last (g + 1))).comp (hco _ ℓ' π)
    · exact continuous_const
  have hF : Continuous fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j :=
    continuous_pi hcomp
  have h1 := fieldCellMean_clm (ℓ.comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun v' : CompIn G.comps => hr v'.1.root) v)) hF
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h1
  rw [← h1]
  have h2 : (fun z => ℓ (liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a (g + 1) n τ X z j v)) =
        fun z => ∑ π : StagePath G (g + 1), if π.tgt = v.1 ∧ π.src ∈ G.comps then
          hlPathFlux G ρ k hk hadm g Cπ π ℓ a n τ X z j else 0 := by
    funext z
    rw [hpt v ℓ z, finsum_eq_sum_of_fintype]
  rw [h2, fieldCellMean_sum _ (fun π _ => ?_), finsum_eq_sum_of_fintype]
  · refine Finset.sum_congr rfl fun π _ => ?_
    split_ifs
    · rw [hl_mean_eval (hco _ ℓ π) (Fin.last (g + 1))]
      rfl
    · exact fieldCellMean_zero
  · split_ifs
    · exact (continuous_apply (Fin.last (g + 1))).comp (hco _ ℓ π)
    · exact continuous_const

/-- **The path-sum step from the grade zero and the two named statements.** -/
theorem hilbertLiftPathSum_of_parts (h0 : HilbertLiftGradeZeroStatement)
    (hZ : HLZeroLiftStatement) (hL : HLLowOrderStatement) : HilbertLiftPathSumStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G hin hE hsX hsZ ρ hρ depth CcT k hk hadm hlift τ hτ a ha n X
    hX j v ℓ
  refine ⟨fun h h1 hd Cπ hπ => ?_, h0 P Mn G hin hsX hsZ ρ hρ depth CcT k hk hadm hlift τ hτ a ha
    n X hX j v ℓ⟩
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  rw [hl_cellMean_core ρ CcT k hk hadm g Cπ τ a n X j v ℓ
    (fun v' ℓ' z => hl_pointwise_core hZ hL hin hE hsX hsZ ρ hk hadm hlift hd Cπ hπ hτ a ha n X j
      v' ℓ' z)
    (fun r ℓ' π => hl_pathContinuous_core hZ hL hin hE hsX hsZ ρ hk hadm hlift hd Cπ hπ hτ a ha
      n X j r ℓ' π)]
  refine finsum_congr fun π => ?_
  by_cases h : π.tgt = v.1 ∧ π.src ∈ G.comps
  · have hin' : hlIn G π ℓ a = fun s' X' => Pi.single (0 : Fin (g + 1 + 1))
        (ℓ (rootPathMap hr π.src.root π.mapList v.1.root (a s' X' ⟨π.src, h.2⟩))) := by
      funext s' X'
      simp [hlIn, h.2]
    simp only [h, and_self, dite_true, ite_true, hin']
  · simp [h]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The path-sum step at positive grades: the lift of the empty path exists (`HLZeroLiftStatement`).

From a grade-zero lift sequence `Cc` of operator data `Q` on spaces `hs`, a component `v₀`, a
functional `ℓ₀` and a vector `e₀` with `ℓ₀ e₀ = 1`, the scalar arrays
`hlExtract`: `ℓ₀ (Cc 0 n m α · v₀ v₀ e₀)` are a grade-zero lift sequence of the scalar operator
data `Q0` with the same contrast, metric and drift. Induction on the truncation order `K ≤ N`
(`hl_extract_isLiftSequence`): if the extraction truncated at `K` is a lift sequence, its diagonal
candidate is one for `Q` (`hlDiag_isLiftSequence`), hence equals the truncation of `Cc`
(`lift_sequence_unique_window`); so the cell source of `Cc` of degree `n ≤ K + 1` on a field
`g₀ e₀` in the component `v₀` is, after `ℓ₀`, the scalar cell source of the extraction
(`hl_liftCellSource_transfer`), and the cell-inverse clause of `Cc` gives that of the
extraction at the degree `n` (`hl_extract_cellInverse`).

* `hlTrunc`, `hl_isLiftSequence_trunc`: truncation of a grade-zero lift sequence in the degree.
* `hlExtract`, `hl_liftApply_extract`, `hl_extract_clauses`: the extraction and its algebraic
  clauses.
* `hl_zeroLift : HLZeroLiftStatement`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

open CovarianceTransport CovFluxReg
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLMaps
open AVRegularity.Providers.PathDecomp

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

/-- The truncation of coefficient arrays at the degree `K`. -/
def hlTrunc (K : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι hs) : ℕ → ℕ → LiftCoeff ι hs :=
  fun hh n => if n ≤ K then Cc hh n else 0

omit [Fintype ι] [DecidableEq ι] in
theorem hlTrunc_of_le {K n : ℕ} (h : n ≤ K) (Cc : ℕ → ℕ → LiftCoeff ι hs) (hh : ℕ) :
    hlTrunc K Cc hh n = Cc hh n := by
  simp [hlTrunc, h]

omit [Fintype ι] [DecidableEq ι] in
theorem hlTrunc_of_lt {K n : ℕ} (h : K < n) (Cc : ℕ → ℕ → LiftCoeff ι hs) (hh : ℕ) :
    hlTrunc K Cc hh n = 0 := by
  simp [hlTrunc, not_le.mpr h]

omit [DecidableEq ι] in
/-- The truncation of a grade-zero lift sequence at a degree `K ≤ N` is a lift sequence of
truncation order `K`. -/
theorem hl_isLiftSequence_trunc [∀ i, FiniteDimensional ℝ (hs i)] {Q : LiftOperatorData ι hs Dm}
    {sX sZ N : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N 0 Cc) {K : ℕ} (hK : K ≤ N) :
    IsLiftSequence Q sX sZ t₀ t₁ K 0 (hlTrunc K Cc) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha₀ t ht X z
    rw [hlTrunc_of_le (Nat.zero_le K)]
    exact h0 a₀ ha₀ t ht X z
  · intro hh hh1 hh0
    omega
  · intro hh _ n hn m α t X z v u
    rw [hlTrunc_of_lt hn]
    rfl
  · intro hh hhH n m hnm α t X z v u
    by_cases hn : n ≤ K
    · rw [hlTrunc_of_le hn]
      exact h3 hh hhH n m hnm α t X z v u
    · rw [hlTrunc_of_lt (not_le.mp hn)]
      rfl
  · intro hh hhH n m α σ
    by_cases hn : n ≤ K
    · rw [hlTrunc_of_le hn]
      exact h4 hh hhH n m α σ
    · rw [hlTrunc_of_lt (not_le.mp hn)]
      rfl
  · intro hh hhH n m α v u t ht
    by_cases hn : n ≤ K
    · rw [hlTrunc_of_le hn]
      exact h5 hh hhH n m α v u t ht
    · rw [hlTrunc_of_lt (not_le.mp hn)]
      exact ⟨isBoxSmooth_zero sX sZ, fun X n' x => rfl⟩
  · intro hh hhH n hn1 hnK a₀ ha₀ X
    obtain rfl : hh = 0 := Nat.le_zero.mp hhH
    have hc := h6 0 le_rfl n hn1 (hnK.trans hK) a₀ ha₀ X
    rw [hlTrunc_of_le hnK]
    refine CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ t₀ t₁ _ _ _ _
      (fun t ht => ?_) hc
    funext z
    have IH : ∀ hh' n', (hh' < 0 ∨ (hh' = 0 ∧ n' < n)) →
        Uniqueness.CoeffEq Cc (hlTrunc K Cc) t₀ t₁ hh' n' := by
      rintro hh' n' (h | ⟨rfl, h⟩)
      · omega
      · intro t _ m α
        rw [hlTrunc_of_le (by omega)]
    exact congrFun (congrFun (Uniqueness.liftCellSource_congr Q 0 n hn1 IH ht (fun _ => a₀)) X) z

/-- The scalar arrays read off the diagonal entry `(v₀, v₀)` of the grade zero of `Cc` through
`ℓ₀` and `e₀`, truncated at the degree `K`. -/
def hlExtract (Cc : ℕ → ℕ → LiftCoeff ι hs) (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ) (e₀ : hs v₀) (K : ℕ) :
    ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ) :=
  fun _ n m α t X z _ _ =>
    if n ≤ K then ℓ₀ (Cc 0 n m α t X z v₀ v₀ e₀) • ContinuousLinearMap.id ℝ ℝ else 0

omit [Fintype ι] [DecidableEq ι] in
theorem hlExtract_apply_of_le (Cc : ℕ → ℕ → LiftCoeff ι hs) (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ)
    (e₀ : hs v₀) {K n : ℕ} (h : n ≤ K) (hh m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2)
    (i j : Fin 1) :
    hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z i j 1 = ℓ₀ (Cc 0 n m α t X z v₀ v₀ e₀) := by
  simp [hlExtract, h]

/-- The scalar value of the extraction is the functional of the value of `Cc` on a field in the
component `v₀` along `e₀`. -/
theorem hl_liftApply_extract (Cc : ℕ → ℕ → LiftCoeff ι hs) (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ)
    (e₀ : hs v₀) {K n : ℕ} (hn : n ≤ K) (b₀ : Vec 2 → Fin 1 → ℝ)
    (hb₀ : ContDiff ℝ (⊤ : ℕ∞) b₀) (t : ℝ) (X z : Vec 2) :
    liftApply n (hlExtract Cc v₀ ℓ₀ e₀ K 0 n) (fun _ => b₀) t X z 0 =
      ℓ₀ (liftApply n (Cc 0 n) (fun _ Y => Pi.single v₀ (b₀ Y 0 • e₀)) t X z v₀) := by
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) (fun Y => b₀ Y 0) := contDiff_pi.mp hb₀ 0
  rw [liftApply_scalar_fin1]
  simp only [liftApply, orderedDerivative_single e₀ hg₀, map_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single v₀]
  · rw [Pi.single_eq_same, map_smul, map_smul, smul_eq_mul, hlExtract_apply_of_le _ _ _ _ hn,
      mul_comm]
    congr 1
    exact hl_orderedDerivative_proj α (hb₀.of_le (by exact_mod_cast le_top)) X 0
  · intro u _ hu
    rw [Pi.single_eq_of_ne hu, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ v₀) h

/-- The algebraic clauses, the regularity and the periodicity of the extraction. -/
theorem hl_extract_clauses [∀ i, FiniteDimensional ℝ (hs i)] {Q : LiftOperatorData ι hs Dm}
    {sX sZ N : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N 0 Cc) (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ) (e₀ : hs v₀)
    (hℓ : ℓ₀ e₀ = 1) (K : ℕ) :
    (∀ a₀ : Vec 2 → Fin 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      liftApply 0 (hlExtract Cc v₀ ℓ₀ e₀ K 0 0) (fun _ => a₀) t X z = a₀ X) ∧
    (∀ hh, hh ≤ 0 → ∀ n, K < n → ∀ m α t X z v u,
      hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z v u = 0) ∧
    (∀ hh, hh ≤ 0 → ∀ n m, n < m → ∀ α t X z v u,
      hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z v u = 0) ∧
    (∀ hh, hh ≤ 0 → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      hlExtract Cc v₀ ℓ₀ e₀ K hh n m (α ∘ σ) = hlExtract Cc v₀ ℓ₀ e₀ K hh n m α) ∧
    (∀ hh, hh ≤ 0 → ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
      IsBoxSmooth sX sZ (fun X z => hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z v u) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z v u)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha₀ t ht X z
    have hg₀ : ContDiff ℝ (⊤ : ℕ∞) (fun Y => a₀ Y 0) := contDiff_pi.mp ha₀ 0
    have e := h0 (fun Y => Pi.single v₀ (a₀ Y 0 • e₀)) (contDiff_single_smul e₀ hg₀) t ht X z
    funext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [hl_liftApply_extract Cc v₀ ℓ₀ e₀ (Nat.zero_le K) a₀ ha₀ t X z, e, Pi.single_eq_same,
      map_smul, hℓ, smul_eq_mul, mul_one]
  · intro hh _ n hn m α t X z v u
    simp [hlExtract, not_le.mpr hn]
  · intro hh _ n m hnm α t X z v u
    by_cases hK : n ≤ K
    · simp [hlExtract, hK, h3 0 le_rfl n m hnm α t X z v₀ v₀]
    · simp [hlExtract, hK]
  · intro hh _ n m α σ
    funext t X z v u
    simp only [hlExtract]
    rw [h4 0 le_rfl n m α σ]
  · intro hh _ n m α v u t ht
    by_cases hK : n ≤ K
    · have hb := (h5 0 le_rfl n m α v₀ v₀ t ht).1.map_clm
        ((ℓ₀.comp (ContinuousLinearMap.apply ℝ (hs v₀) e₀)).smulRight
          (ContinuousLinearMap.id ℝ ℝ))
      refine ⟨?_, fun X n' x => ?_⟩
      · simpa [hlExtract, hK] using hb
      · have hp := (h5 0 le_rfl n m α v₀ v₀ t ht).2 X n' x
        simp only [hlExtract, hK, ite_true] at hp ⊢
        rw [hp]
    · refine ⟨?_, fun X n' x => by simp [hlExtract, hK]⟩
      have hz : (fun X z => hlExtract Cc v₀ ℓ₀ e₀ K hh n m α t X z v u) =
          fun _ _ => (0 : ℝ →L[ℝ] ℝ) := by
        funext X z
        simp [hlExtract, hK]
      rw [hz]
      exact isBoxSmooth_zero sX sZ

/-- **The cell-inverse clause of the extraction at the next truncation order.** -/
theorem hl_extract_cellInverse [∀ i, FiniteDimensional ℝ (hs i)] [∀ i, CompleteSpace (hs i)]
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v) {sX sZ N : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hC : IsLiftSequence Q sX sZ t₀ t₁ N 0 Cc) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (hsZ : 1 ≤ sZ) (hfX : N + 2 ≤ sX) (hfZ : N + 2 ≤ sZ)
    (hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ t k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k))
    (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ) (e₀ : hs v₀) (hℓ : ℓ₀ e₀ = 1) {K : ℕ} (hKN : K + 1 ≤ N)
    (hK : IsLiftSequence Q0 sX sZ t₀ t₁ K 0 (hlExtract Cc v₀ ℓ₀ e₀ K)) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n ≤ K + 1) (a₀ : Vec 2 → Fin 1 → ℝ) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q0.G t X)) Q0.v sZ t₀ t₁ (fun _ => 0)
      (fun t z => liftCellSource Q0 (hlExtract Cc v₀ ℓ₀ e₀ (K + 1)) (fun _ => a₀) 0 n t X z)
      (fun t z => liftApply n (hlExtract Cc v₀ ℓ₀ e₀ (K + 1) 0 n) (fun _ => a₀) t X z) := by
  classical
  -- the diagonal candidate of the truncated extraction is the truncated lift
  have hD := hlDiag_isLiftSequence (hs := hs) (hlExtract Cc v₀ ℓ₀ e₀ K) Q Q0 hη hG hv hK hab hsZ
    (by omega) (by omega) hGs hvs
  have hTr := hl_isLiftSequence_trunc hC (K := K) (by omega)
  have huniq := Uniqueness.lift_sequence_unique_window Q t₀ t₁ hab hW sX sZ K 0 (hlTrunc K Cc)
    (hlDiagCoeff hs (hlExtract Cc v₀ ℓ₀ e₀ K)) hTr hD
  -- the clause of `Cc` on the field in the component `v₀`
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) (fun Y => a₀ Y 0) := contDiff_pi.mp ha₀ 0
  have hA₀ : ContDiff ℝ (⊤ : ℕ∞) (fun Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) :=
    contDiff_single_smul e₀ hg₀
  have hc := hC.2.2.2.2.2.2 0 le_rfl n hn1 (by omega)
    (fun Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) hA₀ X
  have hP := isCellFieldInverse_clm hsZ
    (ContinuousLinearMap.pi fun _ : Fin 1 =>
      ℓ₀.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v₀)) hc
  rw [hG, hv]
  have hz : (fun x : Vec 2 => (ContinuousLinearMap.pi fun _ : Fin 1 =>
      ℓ₀.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v₀))
      ((fun _ : Vec 2 => (0 : ∀ i, hs i)) x)) = fun _ => (0 : Fin 1 → ℝ) := by
    funext x i
    simp
  rw [hz] at hP
  -- the sources agree on the window
  have hsrc : ∀ t ∈ Set.Icc t₀ t₁,
      (fun z => (ContinuousLinearMap.pi fun _ : Fin 1 =>
        ℓ₀.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v₀))
        (liftCellSource Q Cc (fun _ Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) 0 n t X z)) =
      fun z => liftCellSource Q0 (hlExtract Cc v₀ ℓ₀ e₀ (K + 1)) (fun _ => a₀) 0 n t X z := by
    intro t ht
    funext z i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    have IH1 : ∀ hh' n', (hh' < 0 ∨ (hh' = 0 ∧ n' < n)) →
        Uniqueness.CoeffEq Cc (hlDiagCoeff hs (hlExtract Cc v₀ ℓ₀ e₀ K)) t₀ t₁ hh' n' := by
      rintro hh' n' (h | ⟨rfl, h⟩)
      · omega
      · intro t' ht' m α
        funext X' z' v u
        have h' := huniq 0 le_rfl n' m α t' ht' X' z' v u
        rw [hlTrunc_of_le (by omega)] at h'
        exact h'
    have stepA := Uniqueness.liftCellSource_congr Q 0 n hn1 IH1 ht
      (fun _ Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i))
    have stepB := hl_liftCellSource_transfer (hlExtract Cc v₀ ℓ₀ e₀ K) Q Q0 hη hG hv ℓ₀
      (fun _ Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) n t X z (hGs t) (hvs t)
      (hA₀.of_le (by exact_mod_cast le_top))
      (fun n' m α v' u => (hD.2.2.2.2.2.1 0 le_rfl n' m α v' u t ht).1.mono (by omega) (by omega))
      (fun n' m α v' u => (hK.2.2.2.2.2.1 0 le_rfl n' m α v' u t ht).1.mono (by omega) (by omega))
    have stepC : hlScal ℓ₀ (fun (_ : ℝ) Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) =
        fun _ => a₀ := by
      funext s Y i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [hlScal, hℓ]
    have IH2 : ∀ hh' n', (hh' < 0 ∨ (hh' = 0 ∧ n' < n)) →
        Uniqueness.CoeffEq (hlExtract Cc v₀ ℓ₀ e₀ K) (hlExtract Cc v₀ ℓ₀ e₀ (K + 1)) t₀ t₁
          hh' n' := by
      rintro hh' n' (h | ⟨rfl, h⟩)
      · omega
      · intro t' _ m α
        funext X' z' i j
        simp [hlExtract, show n' ≤ K by omega, show n' ≤ K + 1 by omega]
    have stepD := Uniqueness.liftCellSource_congr Q0 0 n hn1 IH2 ht (fun _ => a₀)
    show ℓ₀ (liftCellSource Q Cc (fun _ Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) 0 n t X z
      v₀) = _
    rw [stepA, stepB, stepC, stepD]
  have hfld : ∀ t ∈ Set.Icc t₀ t₁,
      (fun z => (ContinuousLinearMap.pi fun _ : Fin 1 =>
        ℓ₀.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v₀))
        (liftApply n (Cc 0 n) (fun _ Y => (Pi.single v₀ (a₀ Y 0 • e₀) : ∀ i, hs i)) t X z)) =
      fun z => liftApply n (hlExtract Cc v₀ ℓ₀ e₀ (K + 1) 0 n) (fun _ => a₀) t X z := by
    intro t _
    funext z i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact (hl_liftApply_extract Cc v₀ ℓ₀ e₀ hnK a₀ ha₀ t X z).symm
  have h1 := CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ t₀ t₁ _ _ _ _ hsrc hP
  exact WeakEntryProofs.cellFieldInverse_field_congr_on _ _ sZ t₀ t₁ hab _ _ _ _ h1 hfld

/-- **The extraction is a grade-zero lift sequence of the scalar operator data**, at every
truncation order `K ≤ N`. -/
theorem hl_extract_isLiftSequence [∀ i, FiniteDimensional ℝ (hs i)] [∀ i, CompleteSpace (hs i)]
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v) {sX sZ N : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hC : IsLiftSequence Q sX sZ t₀ t₁ N 0 Cc) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (hsZ : 1 ≤ sZ) (hfX : N + 2 ≤ sX) (hfZ : N + 2 ≤ sZ)
    (hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ t k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k))
    (v₀ : ι) (ℓ₀ : hs v₀ →L[ℝ] ℝ) (e₀ : hs v₀) (hℓ : ℓ₀ e₀ = 1) :
    ∀ K ≤ N, IsLiftSequence Q0 sX sZ t₀ t₁ K 0 (hlExtract Cc v₀ ℓ₀ e₀ K) := by
  intro K
  induction K with
  | zero =>
      intro _
      obtain ⟨c1, c3, c4, c5, c6⟩ := hl_extract_clauses hC v₀ ℓ₀ e₀ hℓ 0
      exact ⟨c1, fun hh h1 h0 => by omega, c3, c4, c5, c6, fun hh _ n hn1 hn0 => by omega⟩
  | succ K ih =>
      intro hKN
      have hK := ih (by omega)
      obtain ⟨c1, c3, c4, c5, c6⟩ := hl_extract_clauses hC v₀ ℓ₀ e₀ hℓ (K + 1)
      refine ⟨c1, fun hh h1 h0 => by omega, c3, c4, c5, c6, ?_⟩
      intro hh hhH n hn1 hnK a₀ ha₀ X
      obtain rfl : hh = 0 := Nat.le_zero.mp hhH
      exact hl_extract_cellInverse Q Q0 hη hG hv hC hab hW hsZ hfX hfZ hGs hvs v₀ ℓ₀ e₀ hℓ hKN hK
        hn1 hnK a₀ ha₀ X

end Generic

/-- **The lift of the empty path exists** (`HLZeroLiftStatement`). -/
theorem hl_zeroLift : HLZeroLiftStatement := by
  intro hr _ _ _ _ D Dm b j₀ P Mn G hin hsX hsZ ρ depth CcT k hk hlift hne v₀ ℓ₀ e₀ hℓ
  classical
  have hζ := hin.profile
  obtain ⟨τ₀, hτ₀⟩ := hne
  have hab : D.slotStart G.level k / D.cellScaleSq G.level ≤
      (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level :=
    hτ₀.1.trans hτ₀.2
  have hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X =>
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))).G t X i j) := fun t i j =>
    EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k (nativeChain G.level k) rfl ρ
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)) t i j
  have hvs : ∀ t c, ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))).v t z c) := fun t c =>
    hl_familyLiftData_drift_smooth D G.level k (nativeChain G.level k) ρ
      (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)) t c
  have hW : ∀ X', ∃ lo A Mv : ℝ, AVRegularity.Uniqueness.WindowData
      (fun t => Matrix.of ((familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))).G t X'))
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))).v
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) lo A Mv := by
    intro X'
    obtain ⟨lo, hi, hlo, he⟩ := Providers.GenSem.familyLiftData_pos_window D hζ G.level k
      (nativeChain G.level k) ρ (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) X'
    obtain ⟨Mv, hMv⟩ := Providers.GenSem.familyLiftData_v_bounded D hζ G.level hk
      (nativeChain G.level k) ρ (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))
    exact ⟨lo, hi, Mv, AVRegularity.Uniqueness.windowData_of_elliptic _ _ _ _ lo hi Mv
      (fun t => Providers.GenSem.familyLiftData_symm D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)) t X' 0 1)
      hlo he (fun t _ z => hMv t z)⟩
  have hH := hl_isLiftSequence_grade_zero hlift
  exact ⟨hlExtract (CcT k) v₀ ℓ₀ e₀ Mn.N,
    hl_extract_isLiftSequence
      (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k (nativeChain G.level k) ρ
        (fun _ _ _ => []))
      rfl rfl rfl hH hab hW (by omega) (by omega) (by omega) hGs hvs v₀ ℓ₀ e₀ hℓ Mn.N le_rfl⟩

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Tools of the cascade flux order bound**.

* `fluxOrderLE_of_zero_at`: an operator vanishing at the label `0` on smooth fields has no
  coefficient (the tests of `fluxCoeff` are monomials); `FluxOrderLE.sub`.
* `directFlux_singleton_eq_zero`: the all-slow direct part of one order whose array vanishes.
* `pathEdges_coeff_eq_zero`: the lifted path edges of order above `max 2 E` vanish (`EdgeVanish`).
* `pathMeanFlux_high_eq_zero`: the path mean of degree `n > N + max 2 E` of a stage vanishes at the
  labels of the admissible offsets, at the times of the pulse window, on smooth fields
  (`pathMeanFlux_eq_zero_of_degree`). No certificate of the stage is used: the lift relation and
  the vanishing of the edges only. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.Providers.GenSem

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

/-- The monomial tests of `fluxCoeff` at the label `0` are smooth. -/
theorem fluxMonomial_contDiff {r : ℕ} (I : DerivativeWord2 r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) := by
  simp only [sub_zero]
  exact contDiff_prod fun j _ => contDiff_apply ℝ ℝ (I j)

theorem FluxOrderLE.sub {K : ℕ} {L₁ L₂ : (Vec 2 → ℝ) → Vec 2 → Vec 2} (h₁ : FluxOrderLE K L₁)
    (h₂ : FluxOrderLE K L₂) : FluxOrderLE K (fun f y => L₁ f y - L₂ f y) := by
  intro d I hd
  have e : fluxCoeff (fun f y => L₁ f y - L₂ f y) d I 0 =
      fluxCoeff L₁ d I 0 - fluxCoeff L₂ d I 0 := by
    unfold fluxCoeff
    rw [smul_sub]
  rw [e, h₁ d I hd, h₂ d I hd, sub_zero]

/-- An operator vanishing at the label `0` on smooth fields has no coefficient at all. -/
theorem fluxOrderLE_of_zero_at {K : ℕ} {L : (Vec 2 → ℝ) → Vec 2 → Vec 2}
    (h : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → L g 0 = 0) : FluxOrderLE K L := by
  intro d I _
  unfold fluxCoeff
  rw [h _ (fluxMonomial_contDiff I), smul_zero]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The all-slow direct part of an order whose array vanishes is zero. -/
theorem directFlux_singleton_eq_zero (G : GenStage D hr Dm b j₀) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (n : ℕ)
    (hz : ∀ α : DerivativeWord2 (n - 1), G.fam.flux p c v u γ n α = fun _ _ _ => 0) (t : ℝ)
    (f : Vec 2 → ℝ) (y : Vec 2) : directFlux G p c γ {n} t f y = 0 := by
  unfold directFlux
  rw [Finset.sum_singleton]
  refine Finset.sum_eq_zero fun α _ => ?_
  simp [hz α, fieldCellMean]

/-- The lifted path edges of order above `max 2 E` vanish. -/
theorem pathEdges_coeff_eq_zero {G : GenStage D hr Dm b j₀} {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D b j₀ G.level p) {E : ℕ}
    (hev : ∀ j, EdgeVanish G E (π.step j).2.2) (cs lam : ℝ) (v u : Fin (h + 1))
    (d : Finset.Icc 2 Dm) (hd : max 2 E < d.1) (γ : Constituent d.1 ℝ ℝ)
    (hγ : γ ∈ liftEdges cs lam (pathEdges G π p c) v u d) (α : DerivativeWord2 (d.1 - 1))
    (t : ℝ) (X z : Vec 2) (k : Fin 2) : γ.coeff α t X z k = 0 := by
  simp only [liftEdges, List.mem_map] at hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  unfold pathEdges at hγ₀
  split_ifs at hγ₀ with hvu hdm
  · rw [List.mem_singleton] at hγ₀
    subst hγ₀
    show G.fam.flux p c _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 α (cs * t) (lam • X) z k = 0
    rw [hev ⟨u, hvu.2⟩ p c d.1 α (by omega) (by omega)]
    rfl
  · simp at hγ₀
  · simp at hγ₀

/-- **The path mean of degree `n > N + max 2 E` of a stage vanishes** at the labels of the
admissible offsets, at the times of the pulse window, on smooth fields. -/
theorem pathMeanFlux_high_eq_zero (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) {G : GenStage D hr Dm b j₀} {h : ℕ}
    (π : StagePath G h) {E : ℕ} (hev : ∀ j, EdgeVanish G E (π.step j).2.2) (k : ℤ) (hk : Odd k)
    {B : RealChain} (hB : IsAdmissibleChain D b j₀ G.level k B) (ρ : ℝ) {sX sZ N : ℕ}
    (hRX : Dm ≤ sX) (hRZ : Dm ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hC : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) {n : ℕ} (hn : N + max 2 E < n)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {y : Vec 2}
    (hy : ρ⁻¹ • y ∈ ladderOmega D b j₀ G.level k B ρ) :
    pathMeanFlux D G.level ρ
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) Cc n t f y = 0 := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  exact pathMeanFlux_eq_zero_of_degree D G.level ρ _ Cc (isOpen_ladderOmega D b j₀ G.level k B ρ)
    hC hRX hRZ (le_max_left 2 E) (ccov_inv_mul_mem_window hc ht)
    (fun v u d hd γ hγ α X z k' =>
      pathEdges_coeff_eq_zero π ⟨k, hk⟩ ⟨B, hB⟩ hev _ _ v u d hd γ hγ α _ X z k') hn hf hy

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end
end

section
/-! **The letters of high degree**: `meanHighDegree`, `covHighDegree`.

At a time of the pulse window of the finer slot, a letter of degree `n > N + max 2 E` over a path
whose edges vanish above `max 2 E` has no coefficient at the label `0`:

* `meanHighDegree`: the path mean vanishes at the label `0` on smooth fields
  (`pathMeanFlux_high_eq_zero`), and for a one-edge path so does the subtracted all-slow part of
  the order `n > max 2 E` (`directFlux_singleton_eq_zero`, by `EdgeVanish`).
* `covHighDegree`: the path mean vanishes near the label `0` on smooth fields (the admissible
  offsets are open and contain `0`), and so does the letter at `0` (`covLetter_zero_at`: push,
  covariance iterates and pull keep germs; the family maps are smooth and fix `0`; the covariance
  iterates of a smooth field are smooth, `contDiff_covOperator_iterate`).

No certificate of the stage is used. The degenerate cases are included: `a = a' = 0` (the letter is
the push-pull of the mean); `h = 1` (the direct part is subtracted); `N = 0`, `E = 0` (`n ≥ 3`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.Providers.GenSem

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The covariance letter of a flux operator vanishing near the label `0` on smooth fields
vanishes at the label `0`. -/
theorem covLetter_zero_at (hζ : IsFastProfile D.ζ) (B : RealChain) (m : ℕ) (s₀ t c : ℝ)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hL : ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → L f =ᶠ[𝓝 0] fun _ => 0) (a a' : ℕ)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    pullFlux (B.famMap D t) (B.famMapInv D t) (fun g x =>
      c • (SuccSource.covAtFlux D m s₀ t)^[a]
        (pushFlux (B.famMap D t) (B.famMapInv D t) L
          ((SuccSource.covAt D m s₀ t)^[a'] g)) x) g 0 = 0 := by
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hΦi := contDiff_famMapInv (D := D) B t
  have hΦ := contDiff_famMap (D := D) B t
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (g ∘ B.famMapInv D t) := hg.comp hΦi
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      ((SuccSource.covAt D m s₀ t)^[a'] (g ∘ B.famMapInv D t)) := by
    rw [contDiff_infty]
    intro r
    exact contDiff_covOperator_iterate _ a' (hg'.of_le (htop _))
  have hfΦ : ContDiff ℝ (⊤ : ℕ∞)
      (((SuccSource.covAt D m s₀ t)^[a'] (g ∘ B.famMapInv D t)) ∘ B.famMap D t) := hf.comp hΦ
  have hW : pushFlux (B.famMap D t) (B.famMapInv D t) L
      ((SuccSource.covAt D m s₀ t)^[a'] (g ∘ B.famMapInv D t)) =ᶠ[𝓝 0] fun _ => 0 := by
    have hc : ContinuousAt (B.famMapInv D t) 0 := hΦi.continuous.continuousAt
    have hmem := hc.preimage_mem_nhds (by rw [famMapInv_zero hζ]; exact hL _ hfΦ)
    filter_upwards [hmem] with x hx
    unfold pushFlux
    have hx' : L (((SuccSource.covAt D m s₀ t)^[a'] (g ∘ B.famMapInv D t)) ∘ B.famMap D t)
        (B.famMapInv D t x) = 0 := hx
    rw [hx']
    simp
  have hcg := Uniqueness.covOperator_iterate_germ
    (ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) s₀ t) a hW
  have h0 : (SuccSource.covAtFlux D m s₀ t)^[a]
      (pushFlux (B.famMap D t) (B.famMapInv D t) L
        ((SuccSource.covAt D m s₀ t)^[a'] (g ∘ B.famMapInv D t))) 0 = 0 := by
    have h := hcg.eq_of_nhds
    rw [ccfo_covOperator_iterate_zero] at h
    exact h
  unfold pullFlux
  rw [famMap_zero]
  beta_reduce
  rw [h0, smul_zero, Matrix.mulVec_zero]

/-- **The letter `𝖬_{n,h}` of high degree** (`MeanHighDegreeStatement`). -/
theorem meanHighDegree :
    MeanHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro G Mn t n h π Cc E hΛ hζ hκ hsX hsZ hev hLF hn k τ A hτ
  unfold SuccSource.fluxOp
  apply fluxOrderLE_dite
  intro hA
  have hpm : FluxOrderLE 0 (pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
      (familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) n τ) := by
    refine fluxOrderLE_of_zero_at fun g hg => ?_
    exact pathMeanFlux_high_eq_zero hΛ hζ hκ π hev k hA.2 hA.1 _ hsX hsZ (Cc k A)
      (hLF k A hA) hτ hn hg (by rw [smul_zero]; exact zero_mem_ladderOmega hζ hA.1 _)
  by_cases hh1 : h = 1
  · subst hh1
    simp only [↓reduceDIte]
    refine hpm.sub (fluxOrderLE_of_zero_at fun g _ => ?_)
    exact directFlux_singleton_eq_zero G _ _ _ n
      (fun α => hev ⟨0, by omega⟩ ⟨k, hA.2⟩ ⟨A, hA.1⟩ n α (by omega) (by omega)) τ g 0
  · simp only [hh1, ↓reduceDIte, sub_zero]
    exact hpm

/-- **The letter `𝖵_{n,h,a,a'}` of high degree** (`CovHighDegreeStatement`). -/
theorem covHighDegree :
    CovHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro G Mn t n h a a' π Cc E hΛ hζ hκ hsX hsZ hev hLF hn k τ A hτ
  unfold SuccSource.fluxOp
  apply fluxOrderLE_dite
  intro hA
  have hC := hLF k A hA
  refine fluxOrderLE_of_zero_at fun g hg => ?_
  refine covLetter_zero_at hζ A G.level Mn.anchor τ _ _ (fun f hf => ?_) a a' hg
  have hO : IsOpen {y : Vec 2 | (Mn.lenFactor * liftLength D G.level)⁻¹ • y ∈
      ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)} :=
    (isOpen_ladderOmega D b j₀ G.level k A _).preimage (continuous_const_smul _)
  have h00 : (0 : Vec 2) ∈ {y : Vec 2 | (Mn.lenFactor * liftLength D G.level)⁻¹ • y ∈
      ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)} := by
    show (Mn.lenFactor * liftLength D G.level)⁻¹ • (0 : Vec 2) ∈
      ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)
    rw [smul_zero]
    exact zero_mem_ladderOmega hζ hA.1 _
  filter_upwards [hO.mem_nhds h00] with y hy
  have hz := pathMeanFlux_high_eq_zero hΛ hζ hκ π hev k hA.2 hA.1 _
    (sX := Mn.sX) (sZ := Mn.sZ) (N := Mn.N) hsX hsZ (Cc k A) hC hτ (n := n) hn hf hy
  rw [hz]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end
end

section
/-! Transfer collapse, step A for one coarser piece in abstract form. The
coarser slot `p` has level `m`, the finer slots `k` level `m + 1`; `L k` is a label flux operator
in the chart of the finer slot `k` (the finer output on the native family), of finite order at the
finer label of the point.

* `tc_sum_obsPulses_eq_activeSlots`: the glue over `ocObsPulses (m + 1) t t` is the sum over the
  active finer slots (the other observed pulses have zero cutoff).
* `tc_coarse_transport`: the transport along the inverse of the coarser natural chart of the
  arrays of the transfer (after `tc_slot_jacobian`, `tc_slot_coeff`) is `lam` times the sum over
  the active finer slots of the transports along the inverses of the finer natural charts
  (`tc_transport_comp`, `labelChange ∘ Υ = Ψ_k⁻¹`).
* `tc_fluxCoeff_glued`: the symmetric coefficients of the glue are the permutation sums of the
  same arrays (`tc_fluxCoeff_pushFlux`).
* `tc_word_sum`: against the jets of a field of class `C^{d-1}` (symmetric weights) an array and
  the symmetric coefficients with the same permutation sums give the same contraction.
* `tc_piece_eulerian`: the three together. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.QuietAtlas Providers.GenSem CycleComparison.Reconstruction

/-- **The glue over the observed pulses is the sum over the active finer slots.** -/
theorem tc_sum_obsPulses_eq_activeSlots (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (t : ℝ) {E : Type*}
    [AddCommGroup E] [Module ℝ E] (F : ℤ → E) :
    ∑ k ∈ ocObsPulses D.α D.q D.Λ (m + 1) t t, ocCutoff D.α D.q D.Λ (m + 1) k t • F k =
      ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t • F k.1 := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ (m + 1) := Construction.Stream.ocTau_pos hΛ
  refine Eq.trans ?_ (Finset.sum_map (activeSlots D hΛ m t) (Function.Embedding.subtype _)
    (fun k => ocCutoff D.α D.q D.Λ (m + 1) k t • F k))
  symm
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := Finset.mem_map.mp hk
    have hc : ocCutoff D.α D.q D.Λ (m + 1) k'.1 t ≠ 0 := by simpa [activeSlots] using hk'
    exact Construction.Residual.Presentation.mem_obsPulses_time D.α D.q D.Λ (m + 1) hτ k'.2
      (mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hc)
  · intro k hk hnot
    by_contra hne
    have hc : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 := fun h0 => hne (by rw [h0, zero_smul])
    exact hnot (Finset.mem_map.mpr ⟨⟨k, CycleComparison.LiftSetting.obsPulse_odd hk⟩,
      by simpa [activeSlots] using hc, rfl⟩)

/-- The label change after the inverse of the coarser natural chart is the inverse of the finer
natural chart. -/
theorem tc_labelChange_comp (D : OCData) (m : ℕ) (p k : ℤ) (t : ℝ) :
    labelChange D m p k t ∘ (fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t) =
      fun x' => D.flowOf m (D.slotAnchor (m + 1) k) x' t := by
  funext x'
  simp only [Function.comp_apply, labelChange, flowOf_inv]

/-- **The transport of the arrays of the transfer along the inverse of the coarser chart.** -/
theorem tc_coarse_transport (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (p : ℤ) (t : ℝ) (x : Vec 2)
    (lam : ℝ) (order : ℕ) (L : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2) (r : ℕ)
    (A : DerivativeWord2 r) :
    transportedCoeff (chartInvJacobian fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t) order
        (fun d' I => lam • ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
          transportedCoeff (fun h => chartInvJacobian (labelChange D m p k.1 t)
              (D.flowOf (m - 1) (D.slotAnchor m p) x t + h)) order
            (fun d J => fluxCoeff (L k.1) d J
              (labelChange D m p k.1 t (D.flowOf (m - 1) (D.slotAnchor m p) x t))) (d' - 1) I 0)
        r A x =
      lam • ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
        transportedCoeff (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t)
          order (fun d J => fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
          r A x := by
  have h1 := transportedCoeff_smul
    (chartInvJacobian fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t) order lam
    (fun d' I => ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
      transportedCoeff (fun h => chartInvJacobian (labelChange D m p k.1 t)
          (D.flowOf (m - 1) (D.slotAnchor m p) x t + h)) order
        (fun d J => fluxCoeff (L k.1) d J
          (labelChange D m p k.1 t (D.flowOf (m - 1) (D.slotAnchor m p) x t))) (d' - 1) I 0)
    r A x
  have h2 := transportedCoeff_finset_sum (activeSlots D hΛ m t)
    (chartInvJacobian fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t) order
    (fun k => ocCutoff D.α D.q D.Λ (m + 1) k.1 t)
    (fun k d' I => transportedCoeff (fun h => chartInvJacobian (labelChange D m p k.1 t)
          (D.flowOf (m - 1) (D.slotAnchor m p) x t + h)) order
        (fun d J => fluxCoeff (L k.1) d J
          (labelChange D m p k.1 t (D.flowOf (m - 1) (D.slotAnchor m p) x t))) (d' - 1) I 0)
    r A x
  refine h1.trans (congrArg (fun v => lam • v) (h2.trans ?_))
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg (fun v => ocCutoff D.α D.q D.Λ (m + 1) k.1 t • v) ?_
  have hv : labelChange D m p k.1 t (D.flowOf (m - 1) (D.slotAnchor m p) x t) =
      D.flowOf m (D.slotAnchor (m + 1) k.1) x t := congrFun (tc_labelChange_comp D m p k.1 t) x
  have h := tc_transport_comp (Υ := fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t)
    (Φ := fun y => D.flowOf (m - 1) t y (D.slotAnchor m p)) (φ := labelChange D m p k.1 t)
    (φi := labelChangeInv D m p k.1 t) (flowOf_contDiff D (m - 1) _ _)
    (flowOf_contDiff D (m - 1) _ _) (fun y => flowOf_inv D (m - 1) _ _ y)
    (fun x' => flowOf_inv D (m - 1) _ _ x') (contDiff_labelChange D m p k.1 t)
    (contDiff_labelChangeInv D m p k.1 t) (labelChange_inv D m p k.1 t)
    (labelChangeInv_inv D m p k.1 t) order
    (fun d J => fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t)) r A x
  rw [tc_labelChange_comp] at h
  rw [hv]
  exact h

/-- **The symmetric coefficients of the glue** of label operators of finite order at the finer
labels of the point are the permutation sums of the transported arrays. -/
theorem tc_fluxCoeff_glued (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (t : ℝ) (x : Vec 2) (order : ℕ)
    (L : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hfo : ∀ k ∈ activeSlots D hΛ m t, ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L k.1 g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) =
        ∑ d ∈ Finset.Icc 1 order, ∑ J : DerivativeWord2 (d - 1),
          orderedDerivative J g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) •
            fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
    {d : ℕ} (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) (a₀ : Fin 2) :
    ((d - 1).factorial : ℝ) * fluxCoeff (gluedFluxOp D (m + 1) L t) d I x a₀ =
      ∑ σ : Equiv.Perm (Fin (d - 1)),
        (∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
          transportedCoeff
            (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) order
            (fun d' J => fluxCoeff (L k.1) d' J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
            (d - 1) (I ∘ σ) x) a₀ := by
  have hglue : fluxCoeff (gluedFluxOp D (m + 1) L t) d I x =
      ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
        fluxCoeff (pushFlux (fun y => D.flowOf m t y (D.slotAnchor (m + 1) k.1))
          (fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) (L k.1)) d I x := by
    unfold fluxCoeff gluedFluxOp
    simp only [Nat.add_sub_cancel]
    rw [tc_sum_obsPulses_eq_activeSlots D hΛ m t (fun k =>
      pushFlux (fun y => D.flowOf m t y (D.slotAnchor (m + 1) k))
        (fun x' => D.flowOf m (D.slotAnchor (m + 1) k) x' t) (L k)
        (fun Y => ∏ j, (Y - x) (I j)) x), Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm]
  rw [hglue]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_sum, ← tc_fluxCoeff_pushFlux (flowOf_contDiff D m _ _)
    (flowOf_contDiff D m _ _) (fun y => flowOf_inv D m _ _ y) (fun x' => flowOf_inv D m _ _ x')
    (L k.1) order x (hfo k hk) hd I a₀]
  ring

/-- **An array and the symmetric coefficients with the same permutation sums** give the same
contraction with the jets of a field of class `C^{d-1}`. -/
theorem tc_word_sum {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (C : E →L[ℝ] E') {d : ℕ}
    (T : DerivativeWord2 (d - 1) → ℝ) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (x : Vec 2) (a₀ : Fin 2)
    (hT : ∀ I : DerivativeWord2 (d - 1), ((d - 1).factorial : ℝ) * fluxCoeff L d I x a₀ =
      ∑ σ : Equiv.Perm (Fin (d - 1)), T (I ∘ σ))
    {f : Vec 2 → E} (hf : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) f) :
    ∑ A : DerivativeWord2 (d - 1), T A • C (orderedDerivative A f x) =
      ∑ I : DerivativeWord2 (d - 1), fluxCoeff L d I x a₀ • C (orderedDerivative I f x) := by
  refine sum_word_smul_eq_of_perm_sum _ _ _
    (fun A σ => by rw [orderedDerivative_comp_perm_of_contDiff A σ hf x]) fun A => ?_
  rw [← hT A]
  have hsym : ∀ σ : Equiv.Perm (Fin (d - 1)),
      fluxCoeff L d (A ∘ σ) x a₀ = fluxCoeff L d A x a₀ := by
    intro σ
    unfold fluxCoeff
    have e : (fun Y : Vec 2 => ∏ j, (Y - x) ((A ∘ σ) j)) = fun Y => ∏ j, (Y - x) (A j) := by
      funext Y
      exact Equiv.prod_comp σ fun j => (Y - x) (A j)
    rw [e]
  simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

/-- **One coarser piece gives the Eulerian operator of the glue**, in abstract form: the arrays
of the transfer (after `tc_slot_jacobian`, `tc_slot_coeff`), transported along the inverse of the
coarser natural chart and contracted with the jets of a field of class `C^{Dm-1}`, are `lam`
times the differential operator of the symmetric coefficients of the glue of the `L k`. -/
theorem tc_piece_eulerian (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (p : ℤ) (t : ℝ) (x : Vec 2)
    (lam : ℝ) (order : ℕ) (L : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hfo : ∀ k ∈ activeSlots D hΛ m t, ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L k.1 g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) =
        ∑ d ∈ Finset.Icc 1 order, ∑ J : DerivativeWord2 (d - 1),
          orderedDerivative J g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) •
            fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (C : E →L[ℝ] E') (Dm : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (Dm - 1 : ℕ) f) (κ : Fin 2) :
    ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian fun x' => D.flowOf (m - 1) (D.slotAnchor m p) x' t)
          order
          (fun d' I => lam • ∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
            transportedCoeff (fun h => chartInvJacobian (labelChange D m p k.1 t)
                (D.flowOf (m - 1) (D.slotAnchor m p) x t + h)) order
              (fun d J => fluxCoeff (L k.1) d J
                (labelChange D m p k.1 t (D.flowOf (m - 1) (D.slotAnchor m p) x t)))
              (d' - 1) I 0)
          (d - 1) A x κ • C (orderedDerivative A f x) =
      lam • ∑ d ∈ Finset.Icc 2 Dm, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (gluedFluxOp D (m + 1) L t) d I x κ • C (orderedDerivative I f x) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdD := (Finset.mem_Icc.mp hd).2
  have hcast : ∀ a c : ℕ, a ≤ c → ((a : ℕ∞) : WithTop ℕ∞) ≤ (c : WithTop ℕ∞) :=
    fun a c h => by exact_mod_cast h
  have hfd : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) f :=
    hf.of_le (hcast _ _ (Nat.sub_le_sub_right hdD 1))
  simp only [tc_coarse_transport, Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  exact tc_word_sum C (fun A => (∑ k ∈ activeSlots D hΛ m t,
      ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
        transportedCoeff (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t)
          order (fun d J => fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
          (d - 1) A x) κ) (gluedFluxOp D (m + 1) L t) x κ
    (fun I => tc_fluxCoeff_glued D hΛ m t x order L hfo hd2 I κ) hfd

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The cascade flux order bound**, by induction on
`IsCascadeStage` from the seed, with no certificate of any stage.

* `cascadeFluxOrderBound_of_highDegree`: the induction, from the two statements on the letters of
  high degree (`orderBound_step'`);
* `cascadeFluxOrderBound`: the same with the two statements proved (`meanHighDegree`,
  `covHighDegree`);
* `cascadeFluxOrderBoundWeak : CascadeFluxOrderBoundWeak`, the form used by
  `cascadeSplitInput_of_weakOrderBound`.

`CascadeFluxOrderBoundWeak` is the bound of `cascadeFluxOrderBound` with the conclusion
restricted to `2 < d` and with the stream data of the step (`1 ≤ Λ`, the fast profile, the band
chain; all three are at the call site). -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound

/-- The cascade flux order bound for the orders `d > 2` (the array of order `2` of
a quadratic conversion in grade `0` need not vanish when `D₀ < 2`), with the stream data. -/
def CascadeFluxOrderBoundWeak : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (P : ProvParams) (Mn : SuccMenu) (D₀ hMax npad : ℕ)
    (seed G : GenStage D hr Dm b j₀),
    P.N = Mn.N → P.p = Mn.p →
    Mn.A = succAlphabet (Mn.N + succSchedD D₀ Mn.N Mn.p Mn.H) hMax Mn.p npad →
    (∀ v : CompIn seed.comps, v.1.births = []) →
    (∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ D₀) →
    1 ≤ D.Λ → IsFastProfile D.ζ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    Dm + 2 ≤ Mn.sX → Dm + 2 ≤ Mn.sZ → IsCascadeStage D P Mn seed G →
    ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)), 2 < d →
      succSchedD D₀ Mn.N Mn.p (compGrade v.1) < d → G.fam.flux p c v u γ d I = fun _ _ _ => 0

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The cascade flux order bound from the two statements on the letters of high degree: induction
on `IsCascadeStage`, no certificate of any stage. -/
theorem cascadeFluxOrderBound_of_highDegree
    (hmean : MeanHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (hcov : CovHighDegreeStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀))
    (P : ProvParams) (Mn : SuccMenu) (D₀ hMax npad : ℕ) (seed G : GenStage D hr Dm b j₀)
    (hPN : P.N = Mn.N) (hPp : P.p = Mn.p)
    (hA : Mn.A = succAlphabet (Mn.N + succSchedD D₀ Mn.N Mn.p Mn.H) hMax Mn.p npad)
    (hbirth : ∀ v : CompIn seed.comps, v.1.births = [])
    (hmax : ∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ D₀)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hsX : Dm ≤ Mn.sX) (hsZ : Dm ≤ Mn.sZ) (hG : IsCascadeStage D P Mn seed G) :
    OrdIH G D₀ Mn.N Mn.p := by
  induction hG with
  | seed =>
    intro pp c v u γ d I _ hd
    refine seed.fam.flux_zero pp c v u γ d I ?_
    have h0 : compGrade v.1 = 0 := by simp [compGrade, hbirth v]
    rw [h0] at hd
    have := hmax v u γ
    intro hh
    change succSchedD D₀ Mn.N Mn.p 0 < d at hd
    simp only [succSchedD] at hd
    omega
  | @step G G' hc hsucc ih =>
    have hgm := Providers.CascadeInvariants.grade_mono_of_cascade hbirth hc
    have hst := orderBound_step' P Mn D₀ hMax npad hPN hPp hA G G' hsucc hgm hΛ hζ hκ hsX hsZ ih
      hmean hcov
    intro pp c v u γ d I h2 hd
    exact hst pp c ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ d I
      h2 hd

/-- **The cascade flux order bound**: in a stage of the cascade the flux arrays of the orders
`d > 2` into a component of grade `g` vanish above `D_g = succSchedD D₀ N p g`. -/
theorem cascadeFluxOrderBound (P : ProvParams) (Mn : SuccMenu) (D₀ hMax npad : ℕ)
    (seed G : GenStage D hr Dm b j₀) (hPN : P.N = Mn.N) (hPp : P.p = Mn.p)
    (hA : Mn.A = succAlphabet (Mn.N + succSchedD D₀ Mn.N Mn.p Mn.H) hMax Mn.p npad)
    (hbirth : ∀ v : CompIn seed.comps, v.1.births = [])
    (hmax : ∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ D₀)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hsX : Dm ≤ Mn.sX) (hsZ : Dm ≤ Mn.sZ) (hG : IsCascadeStage D P Mn seed G) :
    OrdIH G D₀ Mn.N Mn.p :=
  cascadeFluxOrderBound_of_highDegree meanHighDegree covHighDegree P Mn D₀ hMax npad seed G hPN hPp
    hA hbirth hmax hΛ hζ hκ hsX hsZ hG

/-- **`CascadeFluxOrderBoundWeak` is proved.** -/
theorem cascadeFluxOrderBoundWeak : CascadeFluxOrderBoundWeak := by
  intro hr _ _ D Dm b j₀ P Mn D₀ hMax npad seed G hPN hPp hA hbirth hmax hΛ hζ hκ hsX hsZ hG
  exact cascadeFluxOrderBound P Mn D₀ hMax npad seed G hPN hPp hA hbirth hmax hΛ hζ hκ
    (by omega) (by omega) hG

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.OrderBound
end
end
end
