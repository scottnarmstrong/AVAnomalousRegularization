-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Families.ActualFamily
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Definitions.Construction.ScheduleFloor

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity

/-! **Envelopes and coefficients of the actual-context family**.
- The edge coefficients are those of the stage at its actual contexts
  (`edgeCoefficient_actualFamily`): off the output window of a piece its weight vanishes.
- At native actual contexts, `onWindow` of the actual-context family lies in the stage's inner
  domain (`GenStage.innerDomain_native`), and on it the fields agree. So the smoothness, the
  essential and the pointwise envelopes of the stage on its inner domain give those of the
  actual-context family on `onWindow` (`IsEnvelope.actualFamily`,
  `IsPointwiseMolecularEnvelope.actualFamily`, `IsPointwiseAnalyticEnvelope.actualFamily`).

The degenerate cases are included:
- An empty window: every domain is empty and every jet supremum is zero.
- A stage with no identity: the sums are empty.
- The window inside one output window: one piece contributes. -/

/-- A jet supremum on a smaller domain, of a field agreeing on it, is at most the supremum. -/
theorem jetSupOn_le_of_eqOn {dom dom' : Set (ℝ × Vec 2)} (r q : ℕ)
    {f f' : ℝ → Vec 2 → Vec 2 → Vec 2} (hsub : dom' ⊆ dom)
    (heq : ∀ t Y, (t, Y) ∈ dom' → f' t = f t) :
    jetSupOn dom' r q f' ≤ jetSupOn dom r q f := by
  unfold jetSupOn
  refine essSup_mono_ae (Filter.Eventually.of_forall fun t => ?_)
  refine iSup₂_le fun Y hY => ?_
  refine le_iSup₂_of_le (f := fun Y (_ : Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}) => ⨆ z : Vec 2,
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ) Y (hsub hY) ?_
  rw [heq t Y hY]

/-- The pointwise version. -/
theorem pointwiseJetSupOn_le_of_eqOn {dom dom' : Set (ℝ × Vec 2)} (r q : ℕ)
    {f f' : ℝ → Vec 2 → Vec 2 → Vec 2} (hsub : dom' ⊆ dom)
    (heq : ∀ t Y, (t, Y) ∈ dom' → f' t = f t) :
    pointwiseJetSupOn dom' r q f' ≤ pointwiseJetSupOn dom r q f := by
  unfold pointwiseJetSupOn
  refine iSup_mono fun t => iSup₂_le fun Y hY => ?_
  refine le_iSup₂_of_le (f := fun Y (_ : Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}) => ⨆ z : Vec 2,
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ) Y (hsub hY) ?_
  rw [heq t Y hY]

namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The fields of the actual-context family at an output time are those of the actual context. -/
theorem actualFamily_flux_of_mem (G : GenStage D hr Dm b j₀) (p : OddSlot) (c : Unit)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) {t : ℝ}
    (ht : t ∈ (G.fam.piece p).output) :
    G.actualFamily.flux p c v u γ d I t = G.fam.flux p (G.actual p) v u γ d I t := by
  funext X z
  simp only [actualFamily, ht, ↓reduceIte]

/-- The slow fields at an output time. -/
theorem actualFamily_slowFlux_of_mem (G : GenStage D hr Dm b j₀) (E : ℝ) (p : OddSlot) (c : Unit)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) {t : ℝ}
    (ht : t ∈ (G.fam.piece p).output) :
    G.actualFamily.slowFlux E p c v u γ d I t = G.fam.slowFlux E p (G.actual p) v u γ d I t := by
  funext Y z
  simp only [ChartedFamily.slowFlux, G.actualFamily_flux_of_mem p c v u γ d I ht]

/-- The dimensional fields at an output time. -/
theorem actualFamily_dimFlux_of_mem (G : GenStage D hr Dm b j₀) (ν e E : ℝ) (p : OddSlot)
    (c : Unit) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    {t : ℝ} (ht : t ∈ (G.fam.piece p).output) :
    G.actualFamily.dimFlux ν e E p c v u γ d I t =
      G.fam.dimFlux ν e E p (G.actual p) v u γ d I t := by
  funext Y z
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux,
    G.actualFamily_flux_of_mem p c v u γ d I ht]

/-- The dimensional fields at an output time, applied. -/
theorem actualFamily_dimFlux_apply_of_mem (G : GenStage D hr Dm b j₀) (ν e E : ℝ) (p : OddSlot)
    (c : Unit) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    {t : ℝ} (ht : t ∈ (G.fam.piece p).output) (Y z : Vec 2) :
    G.actualFamily.dimFlux ν e E p c v u γ d I t Y z =
      G.fam.dimFlux ν e E p (G.actual p) v u γ d I t Y z := by
  rw [G.actualFamily_dimFlux_of_mem ν e E p c v u γ d I ht]

/-- The constituent coefficients are those of the stage at its actual contexts. -/
theorem constituentPhysical_actualFamily (G : GenStage D hr Dm b j₀) (ν e E : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (t : ℝ) (x : Vec 2) :
    constituentPhysical G.actualFamily ν e E (fun _ => ()) v u γ d t x =
      constituentPhysical G.fam ν e E G.actual v u γ d t x := by
  unfold constituentPhysical
  refine finsum_congr fun p => ?_
  by_cases ht : t ∈ (G.fam.piece p).output
  · simp only [G.actualFamily_dimFlux_apply_of_mem ν e E p () v u γ _ _ ht]
    rfl
  · have h0 : ∀ X : (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)), G.fam.weight p t • X = 0 := fun X => by
      rw [G.fam.weight_zero p t ht]
      exact zero_smul ℝ X
    show G.fam.weight p t • _ = G.fam.weight p t • _
    rw [h0, h0]

/-- **The edge coefficients of the actual-context family** are those of the stage. -/
theorem edgeCoefficient_actualFamily (G : GenStage D hr Dm b j₀) (ν e E : ℝ)
    (K : CompIn G.comps → ℕ) :
    edgeCoefficient G.actualFamily ν e E (fun _ => ()) K =
      edgeCoefficient G.fam ν e E G.actual K := by
  funext i i' d t x
  simp only [edgeCoefficient, physicalCoefficient]
  exact Finset.sum_congr rfl fun γ _ => G.constituentPhysical_actualFamily ν e E i i' γ d t x

section Transfer

variable (G : GenStage D hr Dm b j₀) {W W' : Set ℝ} (hW : W ⊆ W') (mres : ℝ)
  (hact : ∀ p, (G.actual p).1 = nativeChain G.level p.1) (hi : 1 ≤ G.level) (hjl : j₀ ≤ G.level)
include hW hact hi hjl

/-- **The window domain of the actual-context family lies in the stage's inner domain** at the
native actual contexts (`innerDomain_native`). -/
theorem onWindow_actualFamily_subset (p : OddSlot) (c : Unit) :
    ChartedFamily.Domain.onWindow G.actualFamily W p c ⊆ G.innerDomain W' mres p (G.actual p) :=
  fun tY htY => G.innerDomain_native W' mres p (hact p) hi hjl tY.1 ⟨htY.1.1, hW htY.1.2⟩ tY.2

theorem isSmoothOn_actualFamily {E : ℝ} {n : CompIn G.comps → ℕ}
    (h : G.fam.IsSmoothOn (G.innerDomain W' mres) E n) :
    G.actualFamily.IsSmoothOn (ChartedFamily.Domain.onWindow G.actualFamily W) E n := by
  intro p c v u γ d I tY htY z
  rw [G.actualFamily_flux_of_mem p c v u γ d I htY.1.1]
  exact h p (G.actual p) v u γ d I tY (G.onWindow_actualFamily_subset hW mres hact hi hjl p c htY) z

theorem jetSupFam_actualFamily_le (r q : ℕ)
    (f' : G.actualFamily.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (f : G.fam.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hf : ∀ p t, t ∈ (G.fam.piece p).output → f' ⟨p, ()⟩ t = f ⟨p, G.actual p⟩ t) :
    jetSupFam (fun x : G.actualFamily.Index =>
        ChartedFamily.Domain.onWindow G.actualFamily W x.1 x.2) r q f' ≤
      jetSupFam (fun x : G.fam.Index => G.innerDomain W' mres x.1 x.2) r q f :=
  iSup_le fun x => le_iSup_of_le ⟨x.1, G.actual x.1⟩ (jetSupOn_le_of_eqOn r q
    (G.onWindow_actualFamily_subset hW mres hact hi hjl x.1 x.2) fun t _ htY => hf x.1 t htY.1.1)

theorem pointwiseJetSupFam_actualFamily_le (r q : ℕ)
    (f' : G.actualFamily.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (f : G.fam.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hf : ∀ p t, t ∈ (G.fam.piece p).output → f' ⟨p, ()⟩ t = f ⟨p, G.actual p⟩ t) :
    pointwiseJetSupFam (fun x : G.actualFamily.Index =>
        ChartedFamily.Domain.onWindow G.actualFamily W x.1 x.2) r q f' ≤
      pointwiseJetSupFam (fun x : G.fam.Index => G.innerDomain W' mres x.1 x.2) r q f :=
  iSup_le fun x => le_iSup_of_le ⟨x.1, G.actual x.1⟩ (pointwiseJetSupOn_le_of_eqOn r q
    (G.onWindow_actualFamily_subset hW mres hact hi hjl x.1 x.2) fun t _ htY => hf x.1 t htY.1.1)

theorem molecularJet_actualFamily_le (ρ e : ℝ) (k j : ℕ)
    (f' : G.actualFamily.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (f : G.fam.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hf : ∀ p t, t ∈ (G.fam.piece p).output → f' ⟨p, ()⟩ t = f ⟨p, G.actual p⟩ t) :
    molecularJet ρ e k j (fun x : G.actualFamily.Index =>
        ChartedFamily.Domain.onWindow G.actualFamily W x.1 x.2) f' ≤
      molecularJet ρ e k j (fun x : G.fam.Index => G.innerDomain W' mres x.1 x.2) f := by
  unfold molecularJet
  exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => mul_le_mul_right
    (G.jetSupFam_actualFamily_le hW mres hact hi hjl _ _ f' f hf) _

theorem pointwiseMolecularJet_actualFamily_le (ρ e : ℝ) (k j : ℕ)
    (f' : G.actualFamily.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (f : G.fam.Index → ℝ → Vec 2 → Vec 2 → Vec 2)
    (hf : ∀ p t, t ∈ (G.fam.piece p).output → f' ⟨p, ()⟩ t = f ⟨p, G.actual p⟩ t) :
    pointwiseMolecularJet ρ e k j (fun x : G.actualFamily.Index =>
        ChartedFamily.Domain.onWindow G.actualFamily W x.1 x.2) f' ≤
      pointwiseMolecularJet ρ e k j (fun x : G.fam.Index => G.innerDomain W' mres x.1 x.2) f := by
  unfold pointwiseMolecularJet
  exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun q _ => mul_le_mul_right
    (G.pointwiseJetSupFam_actualFamily_le hW mres hact hi hjl _ _ f' f hf) _

/-- **The analytic envelope** of the stage on its inner domain gives that of the actual-context
family on the window. -/
theorem isAnalyticEnvelope_actualFamily {π : CompIn G.comps → ℝ} {E C : ℝ} {Ks Ls : ℕ}
    {B : CompIn G.comps → CompIn G.comps → ℝ}
    (h : IsAnalyticEnvelope G.fam π (G.innerDomain W' mres) E C Ks Ls B) :
    IsAnalyticEnvelope G.actualFamily π (ChartedFamily.Domain.onWindow G.actualFamily W) E C Ks Ls
      B := by
  refine ⟨G.isSmoothOn_actualFamily hW mres hact hi hjl h.1, fun v u => le_trans ?_ (h.2 v u)⟩
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ => mul_le_mul_right (Finset.sum_le_sum
    fun d _ => Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun r _ => Finset.sum_le_sum
      fun q _ => mul_le_mul_right (G.jetSupFam_actualFamily_le hW mres hact hi hjl r q
        (fun x => G.actualFamily.slowFlux E x.1 x.2 v u γ d I)
        (fun x => G.fam.slowFlux E x.1 x.2 v u γ d I)
        fun p t ht => G.actualFamily_slowFlux_of_mem E p () v u γ d I ht) _) _) _

/-- **The molecular envelope.** -/
theorem isMolecularEnvelope_actualFamily {π : CompIn G.comps → ℝ} {K : CompIn G.comps → ℕ}
    {ν e E ρ : ℝ} {C : ℕ → ℝ} {J : ℕ} {B : CompIn G.comps → CompIn G.comps → ℝ}
    (h : IsMolecularEnvelope G.fam π K (G.innerDomain W' mres) ν e E ρ C J B) :
    IsMolecularEnvelope G.actualFamily π K (ChartedFamily.Domain.onWindow G.actualFamily W) ν e E
      ρ C J B := by
  refine ⟨G.isSmoothOn_actualFamily hW mres hact hi hjl h.1,
    fun v u j hj => le_trans ?_ (h.2 v u j hj)⟩
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ => mul_le_mul_right (Finset.sum_le_sum
    fun d _ => Finset.sum_le_sum fun I _ => mul_le_mul_left (mul_le_mul_left
      (G.molecularJet_actualFamily_le hW mres hact hi hjl ρ e (K v) j
        (fun x => G.actualFamily.dimFlux ν e E x.1 x.2 v u γ d I)
        (fun x => G.fam.dimFlux ν e E x.1 x.2 v u γ d I)
        fun p t ht => G.actualFamily_dimFlux_of_mem ν e E p () v u γ d I ht) _) _) _) _

/-- **The pointwise molecular envelope.** -/
theorem isPointwiseMolecularEnvelope_actualFamily {π : CompIn G.comps → ℝ}
    {K : CompIn G.comps → ℕ} {ν e E ρ : ℝ} {C : ℕ → ℝ} {J : ℕ}
    {B : CompIn G.comps → CompIn G.comps → ℝ}
    (h : IsPointwiseMolecularEnvelope G.fam π K (G.innerDomain W' mres) ν e E ρ C J B) :
    IsPointwiseMolecularEnvelope G.actualFamily π K
      (ChartedFamily.Domain.onWindow G.actualFamily W) ν e E ρ C J B := by
  refine ⟨G.isSmoothOn_actualFamily hW mres hact hi hjl h.1,
    fun v u j hj => le_trans ?_ (h.2 v u j hj)⟩
  exact mul_le_mul_right (Finset.sum_le_sum fun γ _ => mul_le_mul_right (Finset.sum_le_sum
    fun d _ => Finset.sum_le_sum fun I _ => mul_le_mul_left (mul_le_mul_left
      (G.pointwiseMolecularJet_actualFamily_le hW mres hact hi hjl ρ e (K v) j
        (fun x => G.actualFamily.dimFlux ν e E x.1 x.2 v u γ d I)
        (fun x => G.fam.dimFlux ν e E x.1 x.2 v u γ d I)
        fun p t ht => G.actualFamily_dimFlux_of_mem ν e E p () v u γ d I ht) _) _) _) _

/-- **The two independent envelopes.** -/
theorem isEnvelope_actualFamily {π : CompIn G.comps → ℝ} {K : CompIn G.comps → ℕ}
    {ν e E ρ : ℝ} {B : CompIn G.comps → CompIn G.comps → ℝ} {S Ca : ℝ} {Ks Ls : ℕ}
    {Cm : ℕ → ℝ} {J : ℕ}
    (h : IsEnvelope G.fam π K (G.innerDomain W' mres) ν e E ρ B S Ca Ks Ls Cm J) :
    IsEnvelope G.actualFamily π K (ChartedFamily.Domain.onWindow G.actualFamily W) ν e E ρ B S Ca
      Ks Ls Cm J :=
  ⟨h.nonneg, h.row_sum, h.col_sum,
    G.isAnalyticEnvelope_actualFamily hW mres hact hi hjl h.analytic,
    G.isMolecularEnvelope_actualFamily hW mres hact hi hjl h.molecular⟩

end Transfer

end GenStage

end AVRegularity
end
end

section
/-! **Time measurability of the actual-context family: the import path**. Time
measurability of `GenStage.actualFamily` comes from the context certificate
(`GenStage.IsContextCertified`, a clause of `IsStageInvariant`):
`GenStage.isTimeMeasurable_actualFamily_of_certified`, with outputs = pulse windows. Its
underlying lemma is `contextCertified_flux_time_measurable`.

A hypothesis asserting measurability of every generated context function on the pulse windows
would be false, since `OCData.ζ` is unconstrained and a time-only letter built from a
non-measurable `ζ` is generated; nor is it provable by structural induction.

This is the measurability part of the adapter (`ChartedFamily.IsTimeMeasurable` for the
actual-context family), proved below.

The degenerate cases are included:
- A stage without identities: the clause is vacuous.
- A non-admissible recentered actual context: the coefficient is zero on the window.
- A time off the output windows: every field of the actual-context family is zero there. -/
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! **The atlas and the structural clauses of the actual-context family**.
- `actualAtlas T`: the atlas of the stage read on the actual-context family. It has
  - the same adjacency and transitions, with each overlap cut to the output times of both pieces;
  - the identification `sameCtx` of the stage at the actual contexts.
- On the cut overlaps the fields are the stage's fields at the actual contexts, so:
  - quiet transitions transfer (`actualAtlas_isQuiet`);
  - consecutive closure transfers (`actualAtlas_isConsecutiveClosed`);
  - the quiet cover transfers (`actualAtlas_coversQuiet`).
- Transversality on pulses, fast independence and torus compatibility are read at the output
  times of each piece, where the fields are the stage's at the actual context; outside, the
  fields vanish.
- Depth and descent read only the identities.

The degenerate cases are included:
- No adjacent pair: every atlas clause is vacuous.
- A quiet time outside the output of one piece: not in the cover (the clause asks for both
  outputs).
- `T.sameCtx` false at the actual contexts: the transfer of `IsQuiet` is vacuous there. -/

namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm b j₀)

/-- **The atlas of the stage on the actual-context family.** -/
def actualAtlas (T : G.fam.Atlas) : G.actualFamily.Atlas where
  adjacent := T.adjacent
  tr := fun p q hpq =>
    { T.tr p q hpq with
      overlap := (T.tr p q hpq).overlap ∩
        {tY | tY.1 ∈ (G.fam.piece p).output ∩ (G.fam.piece q).output} }
  sameCtx := fun p q hpq _ _ => T.sameCtx p q hpq (G.actual p) (G.actual q)

theorem actualAtlas_isQuiet {T : G.fam.Atlas} {ν e E : ℝ} (h : T.IsQuiet ν e E) :
    (G.actualAtlas T).IsQuiet ν e E := by
  intro p q hpq c c' hcc
  have hq := h p q hpq (G.actual p) (G.actual q) hcc
  refine ⟨fun tY htY v u γ d I z z' => ?_, fun tY htY z v u γ r A => ?_⟩
  · rw [G.actualFamily_flux_of_mem p c v u γ d I htY.2.1,
      G.actualFamily_flux_of_mem q c' v u γ d I htY.2.2]
    exact hq.1 tY htY.1 v u γ d I z z'
  · have hq' : ∀ d (I : DerivativeWord2 (d - 1)), G.actualFamily.flux q c' v u γ d I tY.1 =
        G.fam.flux q (G.actual q) v u γ d I tY.1 :=
      fun d I => G.actualFamily_flux_of_mem q c' v u γ d I htY.2.2
    have hp' : ∀ d (I : DerivativeWord2 (d - 1)),
        G.actualFamily.dimFlux ν e E p c v u γ d I tY.1 =
          G.fam.dimFlux ν e E p (G.actual p) v u γ d I tY.1 :=
      fun d I => G.actualFamily_dimFlux_of_mem ν e E p c v u γ d I htY.2.1
    simp only [hq', hp']
    exact hq.2 tY htY.1 z v u γ r A

theorem actualAtlas_isConsecutiveClosed {T : G.fam.Atlas} {W : Set ℝ}
    (h : T.IsConsecutiveClosed W) : (G.actualAtlas T).IsConsecutiveClosed W :=
  fun p q hpq hlab hne => h p q hpq hlab hne

theorem actualAtlas_coversQuiet {T : G.fam.Atlas} {quiet W : Set ℝ}
    (h : T.CoversQuiet quiet W) : (G.actualAtlas T).CoversQuiet quiet W :=
  fun p q hpq t ht Y => ⟨h p q hpq t ht Y, ht.1.2, ht.2⟩

theorem isTransverseOnPulses_actualFamily {κ : Type*} {pulse : κ → Set ℝ} {orient : κ → Fin 2}
    (h : G.fam.IsTransverseOnPulses pulse orient) :
    G.actualFamily.IsTransverseOnPulses pulse orient := by
  intro k p c v u γ d I t ht X z s
  rw [G.actualFamily_flux_of_mem p c v u γ d I ht.2]
  exact h k p (G.actual p) v u γ d I t ht X z s

theorem isFastIndependentOn_actualFamily {S : Set ℝ} (h : G.fam.IsFastIndependentOn S) :
    G.actualFamily.IsFastIndependentOn S := by
  intro p c v u γ d I t ht X z z'
  rw [G.actualFamily_flux_of_mem p c v u γ d I ht.2]
  exact h p (G.actual p) v u γ d I t ht X z z'

theorem isTorusCompatible_actualFamily {E : ℝ} (h : IsTorusCompatible G.fam G.actual E) :
    IsTorusCompatible G.actualFamily (fun _ => ()) E := by
  refine ⟨h.1, fun p t v u γ d I z => ?_⟩
  by_cases ht : t ∈ (G.fam.piece p).output
  · rw [G.actualFamily_flux_of_mem p () v u γ d I ht]
    exact h.2 p t v u γ d I z
  · intro n x
    simp only [actualFamily, ht, ↓reduceIte]

theorem hasDepthAtMost_actualFamily {H : ℕ} (h : G.fam.HasDepthAtMost H) :
    G.actualFamily.HasDepthAtMost H := h

theorem isDescending_actualFamily {K : CompIn G.comps → ℕ} (h : G.fam.IsDescending K) :
    G.actualFamily.IsDescending K := h

end GenStage

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! **Time measurability of the actual-context family of a certified stage**.
The context certificate (`GenStage.IsContextCertified`, a clause
of the stage invariant) gives every flux coefficient as a generated function `f p` with a
holomorphic extension `F p` (`IsHolExtension`). That extension is measurable in time on the pulse
window at every fixed parameter, and at the parameters of an admissible chain it is `f p`. The
certificate's flux clause holds at every context and time of the window; the recentered chain does
not depend on time. So on the window each coefficient of the actual-context family is the real
part of a measurable function, or zero; off the output window (the pulse window, for natural
pieces) it is zero. No measurability of arbitrary generated functions is used. On the window
this is `contextCertified_flux_time_measurable` at the actual context.

The degenerate cases are included:
- A non-admissible recentered actual context: the coefficient is zero on the window.
- A time at an endpoint of the window: it lies in the closed window, where the certificate holds.
- A stage without identities: vacuous. -/

namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The actual-context family of a context-certified stage with natural output windows is
measurable in time.** -/
theorem isTimeMeasurable_actualFamily_of_certified (G : GenStage D hr Dm b j₀) {k : InvConsts}
    (hcert : G.IsContextCertified k)
    (hout : ∀ p, (G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ G.level p.1) :
    G.actualFamily.IsTimeMeasurable := by
  intro p c v u γ d I X z
  rw [measurable_pi_iff]
  intro κ
  set W := ocPulseWindow D.α D.q D.Λ G.level p.1 with hWdef
  have hW : MeasurableSet W := measurableSet_Icc
  refine measurable_of_restrict_of_restrict_compl hW ?_ ?_
  · -- on the window: the stage's flux at the actual context
    have e : W.domRestrict (fun t => G.actualFamily.flux p c v u γ d I t X z κ) =
        fun t : W => G.fam.flux p (G.actual p) v u γ d I t X z κ := by
      funext t
      have ht : (t : ℝ) ∈ (G.fam.piece p).output := (hout p).symm ▸ t.2
      show G.actualFamily.flux p c v u γ d I t X z κ = _
      rw [G.actualFamily_flux_of_mem p c v u γ d I ht]
    rw [e]
    exact Construction.Preservation.Buffer.contextCertified_flux_time_measurable hcert p
      (G.actual p) v u γ d I κ X z
  · -- off the window: zero
    have e : Wᶜ.domRestrict (fun t => G.actualFamily.flux p c v u γ d I t X z κ) =
        fun _ : (Wᶜ : Set ℝ) => 0 := by
      funext t
      have ht : (t : ℝ) ∉ (G.fam.piece p).output := by rw [hout p]; exact t.2
      show G.actualFamily.flux p c v u γ d I t X z κ = _
      simp only [actualFamily, ht, ↓reduceIte, Pi.zero_apply]
    rw [e]
    exact measurable_const

end GenStage

end AVRegularity
end
end
