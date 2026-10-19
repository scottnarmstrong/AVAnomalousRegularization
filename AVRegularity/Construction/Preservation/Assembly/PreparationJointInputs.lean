-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.ChainMetric
public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Assembly

/-! The two retained structural certificates independent of the marked-ledger recurrence. -/

/-- Component restriction preserves native pieces, weights, contexts and provenance injection. -/
def StageRestrictionNaturalityStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀),
    G.IsNatural M → ∀ (S : Finset Comp) (hS : S ⊆ G.comps), (G.restrict S hS).IsNatural M

/-- Recorded widths identify the actual kernels after one coefficient-production step. -/
def ActualSuccessorKernelWidthStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (P : ProvParams) (Mn : SuccMenu)
    (seedK freshK : ℕ → KernelSpec) (G G' : GenStage D hr Dm bw j₀),
    G.HasTags P →
    (∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width) →
    (freshK (G.level - 1)).width = P.rb (G.level - 1) →
    IsActualSuccessor D P Mn G G' →
    ∀ v u (γ : G'.fam.Γ v u),
      (G'.kernelOf P seedK freshK v u γ).width = (G'.fam.identity v u γ).record.width

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Restrict the actual successor's two structural certificates to the retained family. -/
theorem retained_structural_certificates_of_ingredients
    (hnatural : StageRestrictionNaturalityStatement) (hwidth : ActualSuccessorKernelWidthStatement)
    (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (G G' : GenStage D hr Dm bw j₀) (ht : G.HasTags P)
    (hw : ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width)
    (hf : (freshK (G.level - 1)).width = P.rb (G.level - 1))
    (hs : IsActualSuccessor D P Mn G G') (m H J : ℕ) :
    (G'.retained m H J).IsNatural Mn.M ∧
    ∀ v u (γ : (G'.retained m H J).fam.Γ v u),
      ((G'.retained m H J).kernelOf P seedK freshK v u γ).width =
        ((G'.retained m H J).fam.identity v u γ).record.width := by
  refine ⟨hnatural hr D Dm bw j₀ Mn.M G' hs.2.2.2.1 _ (Finset.filter_subset _ _), ?_⟩
  intro v u γ
  exact hwidth hr D Dm bw j₀ P Mn seedK freshK G G' ht hw hf hs
    ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩ ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩ γ

end AVRegularity.Construction.Preservation.Assembly
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Assembly

/-! Common thresholds for the already proved certificate inputs. Only the five threshold
fields actually read by invariant admissibility need to be enlarged. -/

/-- Pointwise maximum of the effective invariant thresholds. -/
def certificateThresholdJoin (a b : InvConsts) : InvConsts :=
  { a with
    Γk := max a.Γk b.Γk
    Cwid := max a.Cwid b.Cwid
    Ca := max a.Ca b.Ca
    Cm := fun j => max (a.Cm j) (b.Cm j)
    cker := fun j => max (a.cker j) (b.cker j) }

/-- Weakening the effective thresholds keeps all allocation and equality clauses unchanged. -/
theorem invariant_admissible_of_threshold_bounds {kS a b kI : InvConsts}
    {H J N p nk Kres Lpr Lc Lf : ℕ} {σ₀ δ q c : ℝ}
    (hΓ : a.Γk ≤ b.Γk) (hW : a.Cwid ≤ b.Cwid) (hA : a.Ca ≤ b.Ca)
    (hM : ∀ j, a.Cm j ≤ b.Cm j) (hK : ∀ j, a.cker j ≤ b.cker j)
    (h : IsInvariantAdmissible kS b kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c) :
    IsInvariantAdmissible kS a kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c := by
  rcases h with ⟨hc, hcr, hΓS, hΓI, hWS, hWI, hσ, hlam₀, hlamS, hlam,
    hAS, hAI, hMI, hKI, hrest⟩
  exact ⟨hc, hcr, hΓS, hΓ.trans hΓI, hWS, hW.trans hWI, hσ, hlam₀, hlamS, hlam,
    hAS, hA.trans hAI, fun j => ⟨(hMI j).1, (hM j).trans (hMI j).2⟩,
    fun j => ⟨(hKI j).1, (hK j).trans (hKI j).2⟩, hrest⟩

theorem invariant_admissible_threshold_left {kS a b kI : InvConsts}
    {H J N p nk Kres Lpr Lc Lf : ℕ} {σ₀ δ q c : ℝ}
    (h : IsInvariantAdmissible kS (certificateThresholdJoin a b) kI
      H J N p nk Kres Lpr Lc Lf σ₀ δ q c) :
    IsInvariantAdmissible kS a kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c :=
  invariant_admissible_of_threshold_bounds (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (fun _ => le_max_left _ _) (fun _ => le_max_left _ _) h

theorem invariant_admissible_threshold_right {kS a b kI : InvConsts}
    {H J N p nk Kres Lpr Lc Lf : ℕ} {σ₀ δ q c : ℝ}
    (h : IsInvariantAdmissible kS (certificateThresholdJoin a b) kI
      H J N p nk Kres Lpr Lc Lf σ₀ δ q c) :
    IsInvariantAdmissible kS b kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c :=
  invariant_admissible_of_threshold_bounds (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (fun _ => le_max_right _ _) (fun _ => le_max_right _ _) h

/-- The two kernel lower bounds in invariant admissibility. -/
theorem invariant_admissible_kernel_bounds {kS thr kI : InvConsts}
    {H J N p nk Kres Lpr Lc Lf : ℕ} {σ₀ δ q c : ℝ}
    (h : IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c) :
    ∀ j, kS.cker j ≤ kI.cker j ∧ thr.cker j ≤ kI.cker j := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hK, _⟩
  exact hK

end AVRegularity.Construction.Preservation.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Assembly

/-! Analytic inputs for the full-lift assembly, with no lifted-field conclusion assumed. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def IncomingLiftGeometryStatement (G : GenStage D hr Dm bw j₀) (kI : InvConsts)
    (depth mExist mEnergy : ℕ) : Prop :=
  mExist ≤ G.level ∧ mEnergy ≤ G.level ∧ G.level < D.term ∧ j₀ ≤ G.level ∧
  G.fam.HasDepthAtMost depth ∧
  (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) ∧
  (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) ∧
  (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
    (G.fam.identity v u γ).record.length ≤ D.eps G.level) ∧
  0 < rhoStar D kI.c₀ G.level ∧ rhoStar D kI.c₀ G.level ≤ D.eps G.level

def RetainedHigherValuesStatement (Gr : GenStage D hr Dm bw j₀) (Naux : ℕ)
    (tp tf : ℝ) (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)) : Prop :=
  ∃ Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root),
    ∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)

def RetainedReadoutBudgetStatement (law : BirthLaw) (G Gr : GenStage D hr Dm bw j₀)
    (m p Naux N k : ℕ) (hk : k + N + 2 * p ≤ Naux) (η cr tp tf Cread Ain : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)) : Prop :=
  ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    readoutEnergy law G Gr m η (rhoEnh D cr m) hk w tp tf Y Yw ≤
      ENNReal.ofReal (Cread * Ain)

end AVRegularity.Construction.Preservation.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! Monotonicity of the quantitative conclusions, used to combine independent producers.
No derivative, kernel, or quiet-transition premise is changed. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem commonPreparation_mono_constant
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    (cr Q CQ C₀ C₁ : ℝ) (p Nout Naux : ℕ) (s tf tp : ℝ)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hC : C₀ ≤ C₁)
    (h : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C₀ p Nout Naux s tf tp Preg) :
    IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ C₁ p Nout Naux s tf tp Preg := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro w hw f
  obtain ⟨he, hn, hj, hc⟩ := h.2.2.2.2 w hw f
  refine ⟨he, hn, hj, ?_⟩
  intro Ain hA Qh hQh
  exact (hc Ain hA Qh hQh).trans
    (mul_le_mul_of_nonneg_right hC ((Real.sqrt_nonneg _).trans hA))

theorem retainedSolution_mono_constant
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Gr : GenStage D hr Dm bw j₀)
    (m k : ℕ) (cr C₀ C₁ Q Ain tp tf : ℝ)
    (Y0 : ∀ v : CompIn Gr.comps, TorusHk k (hr v.1.root))
    (hA : 0 ≤ Ain) (hE : 0 ≤ D.eps (m - 1)) (hC : C₀ ≤ C₁)
    (h : RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m k cr C₀ Q Ain tp tf Y0) :
    RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m k cr C₁ Q Ain tp tf Y0 := by
  refine ⟨h.1, ?_⟩
  intro Y Y' Yw Yw' Yk Yk' hs hs'
  obtain ⟨hu, he⟩ := h.2 Y Y' Yw Yw' Yk Yk' hs hs'
  refine ⟨hu, ?_⟩
  intro w hw t ht
  obtain ⟨hc, hi, hm⟩ := he w hw t ht
  refine ⟨hc, hi.trans (mul_le_mul_of_nonneg_right hC hA), hm.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hA
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hC
    (add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)))

theorem comparisonClauses_mono
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm bw j₀)
    (m p Naux N depth sX sZ : ℕ) (η s₀ tp tf r₀ r₁ e₀ e₁ : ℝ)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hres : r₀ ≤ r₁) (he : e₀ ≤ e₁)
    (h : ComparisonClauses law P seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η s₀ tp tf r₀ e₀ f Y) :
    ComparisonClauses law P seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η s₀ tp tf r₁ e₁ f Y := by
  refine ⟨h.1, ?_⟩
  intro U Uw Uk hU CcT PZ aRep û hlift
  obtain ⟨ŵ, ŷ, Rres, qres, hsol, hbound, herr⟩ := h.2 U Uw Uk hU CcT PZ aRep û hlift
  exact ⟨ŵ, ŷ, Rres, qres, hsol, hbound.trans (ENNReal.ofReal_le_ofReal hres),
    herr.trans (ENNReal.ofReal_le_ofReal he)⟩

/-- Absorb a signed producer constant while preserving squared frontier bounds. -/
theorem squared_budget_mono {a C x : ℝ} (hC : |a| ≤ C) (hx : 0 ≤ x) :
    (a * x) ^ 2 ≤ (C * x) ^ 2 := by
  rw [← sq_abs (a * x), abs_mul, abs_of_nonneg hx]
  exact sq_le_sq₀ (mul_nonneg (abs_nonneg _) hx)
    (mul_nonneg ((abs_nonneg a).trans hC) hx) |>.2
      (mul_le_mul_of_nonneg_right hC hx)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] [∀ r, MeasurableSpace (hr r)] in
/-- The explicit bill is nonnegative, including empty component/identity supremum types. -/
theorem succBill_nonneg (G : GenStage D hr Dm bw j₀) (m : ℕ)
    (c₀ cr c σ₀ η : ℝ) (p N Lc Lf Acl J H : ℕ) (tp tf θ₁ θ₂ : ℝ)
    (hE : 0 ≤ D.eps (m - 1)) (he : 0 ≤ D.eps m) (hc₀ : 0 ≤ c₀) (hcr : 0 ≤ cr) :
    0 ≤ succBill D G m c₀ cr c σ₀ η p N Lc Lf Acl J H tp tf θ₁ θ₂ := by
  have hρ : 0 ≤ rhoEnh D cr m := mul_nonneg hcr (Real.sqrt_nonneg _)
  have hρs : 0 ≤ rhoStar D c₀ m :=
    mul_nonneg hc₀ (le_min he (Real.sqrt_nonneg _))
  have hω : 0 ≤ (⨆ t : Set.Icc tp tf, ∑ a : Fin 2, ∑ b : Fin 2,
      |covPrimitive D m t a b|) := Real.iSup_nonneg fun _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hεc : 0 ≤ ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D cr m :=
    div_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) hρ
  have hεo : 0 ≤ max (D.eps (m - 1) ^ σ₀)
      (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
        (G.fam.identity v u γ).record.width / rhoEnh D cr m) :=
    (Real.rpow_nonneg hE _).trans (le_max_left _ _)
  have hεf : 0 ≤ (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoStar D c₀ m) :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      div_nonneg (ConstituentRecord.width_pos _).le hρs
  have hZcl : 0 ≤ Real.sqrt (tf - tp) / Real.sqrt (D.cellScaleSq m) *
      (D.eps m / rhoEnh D cr m) ^ Acl :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (pow_nonneg (div_nonneg he hρ) _)
  unfold succBill
  dsimp only
  positivity

end AVRegularity.Construction.Preservation.Assembly
end
end

section
section
/-! Torus compatibility assembled from the two base-label production laws. The slow-offset law,
low-order vanishing and native-chart torus law are proved and used here. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Assembly

/-- Base-label invariance of non-diagonal transferred coefficients, at every time and offset. -/
def NonDiagonalTransferBaseShiftStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ : ℕ) (P : ProvParams),
  IsFastProfile D.ζ → (∀ i, 0 < D.κ i) →
  ∀ (Mn : SuccMenu) (M : ℕ) (G G' : GenStage D hr Dm b j₀), G.IsNatural M →
  (∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale) →
  G.IsShiftInvariant → IsActualSuccessor D P Mn G G' →
  ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ),
  c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u),
  (∀ m, G'.prov v u γ ≠ Prov.letter m .diag []) →
  ∀ (d : ℕ) (I : DerivativeWord2 (d-1)), 2 ≤ d → ∀ (t : ℝ) (X z : Vec 2),
    G'.fam.flux p c' v u γ d I t X z = G'.fam.flux p c v u γ d I t X z

/-- Base-label invariance of the first-source coefficients, at every time and offset. -/
def DiagonalSourceBaseShiftStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ : ℕ) (P : ProvParams),
  IsFastProfile D.ζ → (∀ i, 0 < D.κ i) →
  ∀ (Mn : SuccMenu) (M : ℕ) (G G' : GenStage D hr Dm b j₀), G.IsNatural M →
  (∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale) →
  G.IsShiftInvariant → IsActualSuccessor D P Mn G G' →
  ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ),
  c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u),
  (∃ m, G'.prov v u γ = Prov.letter m .diag []) →
  ∀ (d : ℕ) (I : DerivativeWord2 (d-1)), 2 ≤ d → ∀ (t : ℝ) (X z : Vec 2),
    G'.fam.flux p c' v u γ d I t X z = G'.fam.flux p c v u γ d I t X z

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- The exact torus statement from its two remaining production laws. -/
theorem successor_torus_compatible_of_ingredients
    (hnd : NonDiagonalTransferBaseShiftStatement) (hdg : DiagonalSourceBaseShiftStatement)
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (P : ProvParams)
    (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.κ i)
    (Mn : SuccMenu) (M : ℕ) (G G' : GenStage D hr Dm b j₀) (hnat : G.IsNatural M)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hsh : G.IsShiftInvariant) (hsucc : IsActualSuccessor D P Mn G G') :
    G'.IsShiftInvariant ∧ IsTorusCompatible G'.fam G'.actual (D.eps (G'.level - 1)) := by
  classical
  have hbase : ∀ (p : OddSlot) (c c' : StageCtx D b j₀ G'.level p) (n : Fin 2 → ℤ),
      c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d-1)),
        G'.fam.flux p c' v u γ d I = G'.fam.flux p c v u γ d I := by
    intro p c c' n hc v u γ d I
    funext t X z
    by_cases hd : 2 ≤ d
    · by_cases hdiag : ∃ m, G'.prov v u γ = Prov.letter m .diag []
      · exact hdg hr D Dm b j₀ P hζ hκ Mn M G G' hnat hold hsh hsucc p c c' n hc v u γ
          hdiag d I hd t X z
      · exact hnd hr D Dm b j₀ P hζ hκ Mn M G G' hnat hold hsh hsucc p c c' n hc v u γ
          (fun m hm => hdiag ⟨m, hm⟩) d I hd t X z
    · rw [G'.fam.flux_zero p c' v u γ d I (fun h => hd h.1),
        G'.fam.flux_zero p c v u γ d I (fun h => hd h.1)]
  have hshift : G'.IsShiftInvariant := ⟨hbase, hsucc.slowOffset' hbase⟩
  exact ⟨hshift, GenStage.isTorusCompatible_of_shiftInvariant hsucc.2.2.2.1 hshift⟩

end AVRegularity.Construction.Preservation.Assembly
end
end

section
/-! Exact preservation interfaces. The first producer supplies one preparation pair before
all data; the second supplies the retained family and homogeneous solutions for every such pair.
Neither producer includes the physical comparison.
The interfaces use explicit lift floors and nontrivial roots.
Empty component families remain allowed in these signatures because nontriviality is
imposed on root spaces. Negative CQ or Cpr are not excluded: the common-preparation premise
retains its actual quantitative content.
-/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-- Data-dependent part of SuccessorBillStatement; all preceding choices are fixed. -/
def SuccessorBillDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C c : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆
        ocQuietTimes α q Λ ζ m →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        ≤ C * D.eps (m - 1) ^ Q ∧
      ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀ tp tf
        (C * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C * D.eps (m - 1) ^ Q * Ain) f Y

/-- The existing bill statement, copied without its proof or an import of it. -/
def SuccessorBillStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C c : ℝ) (mStar : ℕ), 0 < c ∧
    SuccessorBillDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C c mStar

/-- Data-dependent part of CommonPreparationProductionStatement; all preceding choices are fixed. -/
def CommonPreparationProductionDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ C p Nout Naux s₀ tf tp Preg ∧
      s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp ∧
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆
        ocQuietTimes α q Λ ζ m

/-- Joint preparation at the choice order with explicit lift floors, for both weights
and before the datum, including the buffer lower bound and quiet margin of the common endpoint.
For an empty component set the linear map is unique, and a seed with no edges reduces to
the scalar drift-diffusion preparation. The buffer lower bound and quiet margin are supplied
by the mass-uniform cycle-joint witness at the buffer endpoint and need no component. -/
def CommonPreparationProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∃ Kneed : ℕ, ∀ sX sZ : ℕ,
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
    CommonPreparationProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Q T₀ C mStar

/-- Data-dependent part of PreparedRetainedEnergyProductionStatement; all preceding choices are fixed. -/
def PreparedRetainedEnergyProductionDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      NextFamilyClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        kI seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card tp tf ∧
      ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
        weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
        (∀ k ≤ Kres, ∃ Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root),
          IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 ∧
          RetainedSolutionClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            φ₀ hφ₀ (G'.retained m H J) m k kI.cr C Q Ain tp tf Y0)

/-- The retained family's priced action, mass/readout bounds, trace and homogeneous energy
solutions, for every preparation with the supplied constants CQ and Cpr.
The energy producer does not require a pointwise molecular envelope of the seed.
Empty families have vacuous solutions and zero norms, and a seed with no edges still
produces the fresh diagonal response. The retained-system route uses the nontrivial-root
instances. -/
def PreparedRetainedEnergyProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ sX sZ : ℕ,
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    PreparedRetainedEnergyProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar

/-- Literal conclusion after the uniform choices. -/
def PreservationSuccessorDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ C p Nout Naux s₀ tf tp Preg ∧
      s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp ∧
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
      NextFamilyClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        kI seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card tp tf ∧
      ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
        weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
        (∀ k ≤ Kres, ∃ Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root),
          IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 ∧
          RetainedSolutionClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            φ₀ hφ₀ (G'.retained m H J) m k kI.cr C Q Ain tp tf Y0) ∧
        ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
          (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
          (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
          (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
            TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
          IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
          (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
            seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
            (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
          ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
            G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀
            tp tf (C * D.eps (m - 1) ^ Q * Ain) (C * D.eps (m - 1) ^ Q * Ain) f Y

/-- Literal conclusion, with the data-dependent part named. -/
def PreservationSuccessorStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
    PreservationSuccessorDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Q T₀ C mStar

end AVRegularity.Construction.Preservation.Assembly
end
end

section
/-! Separate the physical residual/error estimate from the numerical schedule reduction.
The scalar reduction takes any positive entrance-decay rate chosen by the residual producer.
The interfaces use explicit lift floors and nontrivial roots.
Empty component families remain allowed in these signatures because nontriviality is
imposed on root spaces. Negative CQ or Cpr are not excluded: the common-preparation premise
retains its actual quantitative content.
-/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-- Data-dependent part of SuccessorBillResidualStatement; all preceding choices are fixed. -/
def SuccessorBillResidualDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C c : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆
        ocQuietTimes α q Λ ζ m →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀ tp tf
        (C * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C * Ain * (succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)) +
          D.eps (m - 1) ^ Q)) f Y

/-- Data-dependent part of SuccessorBillScaleStatement; all preceding choices are fixed. -/
def SuccessorBillScaleDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C c : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        ≤ C * D.eps (m - 1) ^ Q

/-- The complete scalar bill is O(E^Q) for each positive decay rate fixed before the data.
The identity metric is allowed without assuming that its covariance term vanishes. One
component and an empty family have the same scalar bound (empty kernel suprema use the
actual definitions), and an edgeless seed still pays temporal and entrance terms. -/
def SuccessorBillScaleStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr c : ℝ, 0 < c → ∃ (C : ℝ) (mStar : ℕ),
    SuccessorBillScaleDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C c mStar

/-- Residual presentation and error with the explicit bill, choosing its genuine decay rate.
Empty families give zero residual and error, and an edgeless seed still has covariance and
diagonal defects. The error retains succBill + E^Q; the assembly consumes the separate scale
bound. The quiet margin is an explicit premise, and no quiet identity is strengthened.
The order floor of the physical reconstruction, `succReconFloor … ≤ Naux`, is an
explicit premise (the scale half does not take it).
The data statement takes the pointwise molecular envelope of the seed,
`IsSeedPointwiseMolecular law kS seed tS tf` (the scale half does not take it). -/
def SuccessorBillResidualStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C c : ℝ) (mStar : ℕ), 0 < c ∧
    SuccessorBillResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C c mStar


end AVRegularity.Construction.Preservation.Assembly
end
end
end

section
/-! The preservation route uses the joint preparation `cycle_joint` together with a single
shared window-cover input. The cover is not derived from a statement that already assumes it.
The flow certificate is reused from the level-generic statement proved from `oc_flow_jets`.

The interfaces make no assumption on the component type, so a singleton, an empty component
type and a seed with no edges all use the same scalar cover and still need the chart
certificate. The cover does not exclude terminal levels; the cascade's m<M restriction belongs
to its scale instantiation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
universe u v w x
namespace AVRegularity.Construction.Preservation.Assembly

/-- The existing statement as one named proposition, including CH=2 and the witness chosen
before the masses, with the quiet margin of its endpoint. -/
def PreservationCycleJointStatement : Prop :=
  CycleJointProofs.Assembly.CycleJointStatement.{u, v, w, x}

/-- One supplied full cover, with the radius and window used by cycle_joint. At the
chosen CH=2 this is shared two-renewal-window input. All numeric conditions remain
inside the supplied cover; this definition proves none of them. -/
def CommonPreparationWindowCoverStatement
    (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B s₀ CH cMol g g₀ a B₀ lam Cb : ℝ)
    (qJ Kmax : ℕ) (CG : ℕ → ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2) : Prop :=
  IsWindowCover α q Λ m ζ Φ hφ ν B s₀ (s₀ + CH * ocTauPP α q Λ m)
    (ocRhoMol α q Λ m cMol ν) g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀

/-- The conclusion of `cycle_joint` strengthened by the preservation time bound, in the form:
one witness for every mass family, with the quiet margin of the endpoint. The cover remains one named
hypothesis, and every other premise and output of `cycle_joint` is retained verbatim. -/
def CycleJointPreparationStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ (Pacc : ℝ), 0 < Pacc → ∀ (Mout H D Kmax : ℕ), 2 ≤ D →
      ∃ (Ks Ls Jm qJ Jchart : ℕ) (CH : ℝ), 0 < CH ∧ CH = 2 ∧
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ), 0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : CommonPreparationWindowCoverStatement α q Λ m ζ Φ hφ ν B tS CH cMol g g₀ a B₀
          lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + CH * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + CH * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + CH * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ (tp : ℝ) (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
        tp ∈ Set.Ioc tS (tS + CH * ocTauPP α q Λ m) ∧
        tS ≤ tp ∧ tp ≤ tS + 4 * ocTauPP α q Λ m ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
        Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
        ∀ (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
          (_henv : IsEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
          (_hpointwise : IsPointwiseMolecularEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + CH * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)),
          IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Pacc
            (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP Pd Pg ∧
          IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
            (ocEpsilon q Λ (m - 1)) Pacc CP (streamVel (Φ m))
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg

end AVRegularity.Construction.Preservation.Assembly
end
end
