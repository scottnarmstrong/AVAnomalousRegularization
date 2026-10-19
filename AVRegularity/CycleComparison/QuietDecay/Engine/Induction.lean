-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Engine.DiffConv
import AVRegularity.CycleComparison.Residual.TailJets
public import AVRegularity.CycleEvolution.CellPeriodicSliceGraphFluxSlice
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
/-! Packaging finitely many scalar components into one `PiLp 2` field: the squared norm is the sum of
the squared components, and difference quotients and derivatives act componentwise. The generic
difference-quotient bounds then hold with the sum over components inside the supremum. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped ENNReal

namespace AVRegularity.QuietDecay

variable {κ : Type*} [Fintype κ]

/-- The packaged field. -/
def vecF (φ : κ → Vec 2 → Vec 2 → ℂ) : Vec 2 → Vec 2 → PiLp 2 (fun _ : κ => ℂ) :=
  fun X z => WithLp.toLp 2 fun k => φ k X z

theorem enorm_sq_toLp (v : κ → ℂ) :
    ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : κ => ℂ))‖ₑ ^ 2 = ∑ k, ‖v k‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem sdiff_toLp (i : Fin 2) (h : ℝ) (g : κ → Vec 2 → ℂ) (X : Vec 2) :
    sdiff i h (fun Y => (WithLp.toLp 2 fun k => g k Y : PiLp 2 (fun _ : κ => ℂ))) X =
      WithLp.toLp 2 fun k => sdiff i h (g k) X := by
  ext k
  simp [sdiff]

theorem slowDiffs_vecF (l : List (Fin 2)) (h : ℝ) (φ : κ → Vec 2 → Vec 2 → ℂ) (X z : Vec 2) :
    slowDiffs l h (vecF φ) X z = WithLp.toLp 2 fun k => slowDiffs l h (φ k) X z := by
  induction l using List.reverseRecOn generalizing X with
  | nil => rfl
  | append_singleton l i ih =>
      simp only [slowDiffs_append]
      rw [show (fun X' => slowDiffs l h (vecF φ) X' z) = fun X' =>
          (WithLp.toLp 2 fun k => slowDiffs l h (φ k) X' z : PiLp 2 (fun _ : κ => ℂ)) from
        funext fun X' => ih X']
      exact sdiff_toLp i h (fun k X' => slowDiffs l h (φ k) X' z) X

/-- The packaging map as a continuous linear equivalence. -/
abbrev packL : (κ → ℂ) ≃L[ℝ] PiLp 2 (fun _ : κ => ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm

theorem fderiv_toLp {g : κ → Vec 2 → ℂ} {X : Vec 2} (hg : ∀ k, DifferentiableAt ℝ (g k) X)
    (e : Vec 2) :
    fderiv ℝ (fun Y => (WithLp.toLp 2 fun k => g k Y : PiLp 2 (fun _ : κ => ℂ))) X e =
      WithLp.toLp 2 fun k => fderiv ℝ (g k) X e := by
  have hpi : DifferentiableAt ℝ (fun Y => fun k => g k Y) X := differentiableAt_pi.2 hg
  set L : (κ → ℂ) →L[ℝ] PiLp 2 (fun _ : κ => ℂ) :=
    (packL : (κ → ℂ) ≃L[ℝ] _).toContinuousLinearMap
  have e1 : (fun Y => (WithLp.toLp 2 fun k => g k Y : PiLp 2 (fun _ : κ => ℂ))) =
      L ∘ fun Y => fun k => g k Y := rfl
  rw [e1, fderiv_comp X L.differentiableAt hpi, L.fderiv, ContinuousLinearMap.comp_apply,
    fderiv_pi hg]
  rfl

theorem isSlowSmooth_vecF {n : ℕ} {φ : κ → Vec 2 → Vec 2 → ℂ} (hφ : ∀ k, IsSlowSmooth n (φ k)) :
    IsSlowSmooth n (vecF φ) := by
  have h1 : IsSlowSmooth n (fun X z => fun k => φ k X z) := IsSlowSmooth.pi fun k => hφ k
  exact h1.clm_comp (packL : (κ → ℂ) ≃L[ℝ] PiLp 2 (fun _ : κ => ℂ)).toContinuousLinearMap

theorem slowDerivs_vecF : ∀ (l : List (Fin 2)) {φ : κ → Vec 2 → Vec 2 → ℂ},
    (∀ k, IsSlowSmooth (l.length + 1) (φ k)) → ∀ X z,
      slowDerivs l (vecF φ) X z = WithLp.toLp 2 fun k => slowDerivs l (φ k) X z := by
  intro l
  induction l with
  | nil => intro φ _ X z; rfl
  | cons i l ih =>
      intro φ hφ X z
      simp only [slowDerivs_cons]
      have hφ' : ∀ k, IsSlowSmooth (l.length + 1 + 1) (φ k) := fun k => by simpa using hφ k
      have hp : AVRegularity.slowPartial i (vecF φ) =
          vecF (fun k => AVRegularity.slowPartial i (φ k)) := by
        funext X' z'
        unfold AVRegularity.slowPartial vecF
        exact fderiv_toLp (fun k => ((hφ' k).1 z').differentiable (by simp) X') _
      rw [hp]
      exact ih (fun k => (hφ' k).slowPartial i) X z

end AVRegularity.QuietDecay
end
end

section
/-! Changing the metric of a cell solution: the weak identity for the metric `G₁` is the weak
identity for the metric `G₂` with the additional flux `(G₁ - G₂)ᵀ ∇u`. With this, a difference of
cell solutions for nearby metrics is a cell solution for one metric with a flux source. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution

namespace AVRegularity.QuietDecay

/-- The flux carrying the metric change `G₁ → G₂` of the gradient `du`. -/
def metricFluxChange (G₁ G₂ : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (du : ℝ → Fin 2 → Vec 2 → ℂ) (τ : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℂ) :=
  WithLp.toLp 2 fun k => ∑ j : Fin 2, ((G₁ τ x j k - G₂ τ x j k : ℝ) : ℂ) * du τ j x

theorem cellLiteralRHS_metric_change (G₁ G₂ : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (κ : ℝ → ℂ) (τ : ℝ) (u : Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (src : Vec 2 → ℂ)
    (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS ⟨G₁, v, 0, κ⟩ τ u (du τ) ψ dψ src F x =
      cellLiteralRHS ⟨G₂, v, 0, κ⟩ τ u (du τ) ψ dψ src
        (fun y => F y + metricFluxChange G₁ G₂ du τ y) x := by
  simp only [cellLiteralRHS, metricFluxChange, Pi.zero_apply, mul_zero, zero_mul, add_zero,
    sub_zero, PiLp.add_apply, Fin.sum_univ_two]
  push_cast
  ring

/-- The weak identity under a change of metric. -/
theorem cellWeakIdentity_metric_change (G₁ G₂ : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (κ : ℝ → ℂ) (s t : ℝ) (u0 u1 ψ : Vec 2 → ℂ)
    (dψ : Fin 2 → Vec 2 → ℂ) (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity ⟨G₁, v, 0, κ⟩ s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity ⟨G₂, v, 0, κ⟩ s t u0 u1 ψ dψ u du src
      (fun τ y => F τ y + metricFluxChange G₁ G₂ du τ y) := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS ⟨G₁, v, 0, κ⟩ r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS ⟨G₂, v, 0, κ⟩ r (u r) (du r) ψ dψ (src r)
    (fun y => F r y + metricFluxChange G₁ G₂ du r y)
  have hR : R = R' := funext fun r => funext fun x =>
    cellLiteralRHS_metric_change G₁ G₂ v κ r (u r) du ψ dψ (src r) (F r) x
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  rw [← hR]
  exact h

/-- A cell solution for the metric `G₁` is a cell solution for the metric `G₂` with the
additional flux `metricFluxChange G₁ G₂`. -/
theorem cellSolution_metric_change {I : Set ℝ} (G₁ G₂ : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (κ : ℝ → ℂ) {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution I ⟨G₁, v, 0, κ⟩ src F D) :
    IsCellSolution I ⟨G₂, v, 0, κ⟩ src
      (fun τ y => F τ y + metricFluxChange G₁ G₂ (fun τ k => cellGradComp (D τ) k) τ y) D := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun s hs t ht hst ψ =>
    cellWeakIdentity_metric_change G₁ G₂ v κ s t _ _ _ _ _ _ src F (h7 s hs t ht hst ψ)⟩

end AVRegularity.QuietDecay
end
end

section
/-! Families of cell solutions indexed by a slow point, and their slow difference quotients.

A family `X ↦ (D X, src X, F X)` solves the cell equation with the slow-point metric `G · X`. Its slow
difference quotient in the direction `i` with step `h` is again such a family: the metric change
`G(X + h eᵢ) → G(X)` becomes an additional flux. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution

namespace AVRegularity.QuietDecay

/-- A family of cell data indexed by the slow point. -/
structure CellFam where
  /-- The raw jets. -/
  D : Vec 2 → ℝ → RawJet2 1 ℂ
  /-- The scalar sources. -/
  src : Vec 2 → ℝ → Vec 2 → ℂ
  /-- The fluxes. -/
  F : Vec 2 → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)

/-- The cell coefficients of the slow point `X`. -/
def slowCoeffs (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (X : Vec 2) :
    CellCoefficients :=
  ⟨fun t _ => G t X, v, 0, 0⟩

/-- Every member of the family is a cell solution on `J` for its own slow-point metric. -/
def IsCellFam (J : Set ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (Φ : CellFam) : Prop :=
  ∀ X, IsCellSolution J (slowCoeffs G v X) (Φ.src X) (Φ.F X) (Φ.D X)

/-- The slow difference quotient of a family. -/
def slowStep (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (h : ℝ) (Φ : CellFam) :
    CellFam where
  D X t := h⁻¹ • (Φ.D (X + h • basisVec i) t - Φ.D X t)
  src X t z := (h⁻¹ : ℂ) * (Φ.src (X + h • basisVec i) t z - Φ.src X t z)
  F X t z := h⁻¹ • (Φ.F (X + h • basisVec i) t z - Φ.F X t z +
    metricFluxChange (fun τ _ => G τ (X + h • basisVec i)) (fun τ _ => G τ X)
      (fun τ k => cellGradComp (Φ.D (X + h • basisVec i) τ) k) t z)

theorem isCellFam_slowStep {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Φ : CellFam} (hΦ : IsCellFam J G v Φ) (i : Fin 2) (h : ℝ) :
    IsCellFam J G v (slowStep G i h Φ) := by
  intro X
  set X' := X + h • basisVec i
  have h1 : IsCellSolution J (slowCoeffs G v X) (Φ.src X')
      (fun τ y => Φ.F X' τ y + metricFluxChange (fun τ _ => G τ X') (fun τ _ => G τ X)
        (fun τ k => cellGradComp (Φ.D X' τ) k) τ y) (Φ.D X') :=
    cellSolution_metric_change _ _ v 0 (hΦ X')
  have h2 := cellSolution_smul (hΦ X) (-1)
  have h3 := cellSolution_smul (cellSolution_add h1 h2) h⁻¹
  have hD : (slowStep G i h Φ).D X = h⁻¹ • (Φ.D X' + (-1 : ℝ) • Φ.D X) := by
    funext t
    simp only [slowStep, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, X', neg_one_smul, sub_eq_add_neg]
  rw [hD]
  refine cellSolution_source_congr_sections J _ _ _ _ _ _
    (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun z => ?_)
    (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun z => ?_) h3
  · simp only [Pi.smul_apply, Pi.add_apply, slowStep, X']
    rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring
  · simp only [Pi.smul_apply, Pi.add_apply, slowStep, X']
    rw [neg_one_smul, ← sub_eq_add_neg, sub_add_eq_add_sub]

end AVRegularity.QuietDecay
end
end

section
/-! Iterated slow difference quotients of a family of cell solutions, and the structure of their
fluxes: after a word `l` of slow steps (starting from zero flux), the flux is a finite sum of terms
`(Δ_A G)(X + a) ∇D_B(X + b)` with `A` nonempty and `B` strictly shorter than `l` (discrete Leibniz
for the commutator `Δ_l(G∇u) - G(X)∇Δ_l u`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution

namespace AVRegularity.QuietDecay

/-- Iterated scalar difference quotients along a list (first letter first). -/
def diffs (l : List (Fin 2)) (h : ℝ) (g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  l.foldl (fun g' i => sdiff i h g') g

theorem diffs_append (l : List (Fin 2)) (i : Fin 2) (h : ℝ) (g : Vec 2 → ℝ) :
    diffs (l ++ [i]) h g = sdiff i h (diffs l h g) := by
  simp [diffs, List.foldl_append]

/-- The family after the slow steps of the word `l` (first letter first). -/
def famWord (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (l : List (Fin 2)) (h : ℝ) :
    CellFam :=
  l.foldl (fun Ψ i => slowStep G i h Ψ) Φ

theorem famWord_append (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (i : Fin 2) (h : ℝ) :
    famWord G Φ (l ++ [i]) h = slowStep G i h (famWord G Φ l h) := by
  simp [famWord, List.foldl_append]

theorem isCellFam_famWord {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {Φ : CellFam} (hΦ : IsCellFam J G v Φ) (l : List (Fin 2)) (h : ℝ) :
    IsCellFam J G v (famWord G Φ l h) := by
  induction l using List.reverseRecOn with
  | nil => exact hΦ
  | append_singleton l i ih =>
      rw [famWord_append]
      exact isCellFam_slowStep ih i h

/-- The flux `M ∇D` of a matrix `M` and a raw jet `D`. -/
def mflux (M : Fin 2 → Fin 2 → ℝ) (D : RawJet2 1 ℂ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℂ) :=
  WithLp.toLp 2 fun k => ∑ j : Fin 2, (M j k : ℂ) * cellGradComp D j z

/-- A flux term: the differences `gw` of the metric at the shift `gs`, against the gradient of the
member of the word `dw` at the shift `ds`. -/
structure FluxTerm where
  gw : List (Fin 2)
  gs : Vec 2
  dw : List (Fin 2)
  ds : Vec 2

/-- One slow step on the flux terms (the current word is `l`, the new letter `i`). -/
def termsStep (h : ℝ) (Ts : List FluxTerm) (l : List (Fin 2)) (i : Fin 2) : List FluxTerm :=
  Ts.flatMap (fun τ => [⟨τ.gw ++ [i], τ.gs, τ.dw, τ.ds + h • basisVec i⟩,
    ⟨τ.gw, τ.gs, τ.dw ++ [i], τ.ds⟩]) ++ [⟨[i], 0, l, h • basisVec i⟩]

/-- The flux terms of the word `l`. -/
def terms (h : ℝ) : List (Fin 2) → List FluxTerm
  | l => (l.foldl (fun p i => (p.1 ++ [i], termsStep h p.2 p.1 i))
      (([] : List (Fin 2)), ([] : List FluxTerm))).2

theorem terms_aux_fst (h : ℝ) (l : List (Fin 2)) :
    (l.foldl (fun p i => (p.1 ++ [i], termsStep h p.2 p.1 i))
      (([] : List (Fin 2)), ([] : List FluxTerm))).1 = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l i ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact congrArg (· ++ [i]) ih

theorem terms_aux (h : ℝ) (l : List (Fin 2)) :
    (l.foldl (fun p i => (p.1 ++ [i], termsStep h p.2 p.1 i))
      (([] : List (Fin 2)), ([] : List FluxTerm))) = (l, terms h l) :=
  Prod.ext (terms_aux_fst h l) rfl

theorem terms_append (h : ℝ) (l : List (Fin 2)) (i : Fin 2) :
    terms h (l ++ [i]) = termsStep h (terms h l) l i := by
  have e := terms_aux h (l ++ [i])
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, terms_aux h l] at e
  exact (congrArg Prod.snd e).symm

/-- The value of a flux term. -/
def FluxTerm.eval (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (h : ℝ) (τ : FluxTerm)
    (X : Vec 2) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℂ) :=
  mflux (fun j k => diffs τ.gw h (fun Y => G t Y j k) (X + τ.gs))
    ((famWord G Φ τ.dw h).D (X + τ.ds) t) z

theorem mflux_sub_smul (M M' : Fin 2 → Fin 2 → ℝ) (D D' : RawJet2 1 ℂ) (h : ℝ) (z : Vec 2) :
    h⁻¹ • (mflux M D z - mflux M' D' z) =
      mflux (fun j k => h⁻¹ * (M j k - M' j k)) D z + mflux M' (h⁻¹ • (D - D')) z := by
  ext k
  simp only [mflux, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, cellGradComp,
    Pi.smul_apply, Pi.sub_apply, Fin.sum_univ_two, Complex.real_smul]
  push_cast
  ring

theorem famWord_D_append (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (i : Fin 2) (h : ℝ) (X : Vec 2) (t : ℝ) :
    (famWord G Φ (l ++ [i]) h).D X t =
      h⁻¹ • ((famWord G Φ l h).D (X + h • basisVec i) t - (famWord G Φ l h).D X t) := by
  rw [famWord_append]; rfl

/-- The step identity of one flux term. -/
theorem FluxTerm.eval_step (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (h : ℝ)
    (τ : FluxTerm) (i : Fin 2) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    h⁻¹ • (τ.eval G Φ h (X + h • basisVec i) t z - τ.eval G Φ h X t z) =
      (⟨τ.gw ++ [i], τ.gs, τ.dw, τ.ds + h • basisVec i⟩ : FluxTerm).eval G Φ h X t z +
        (⟨τ.gw, τ.gs, τ.dw ++ [i], τ.ds⟩ : FluxTerm).eval G Φ h X t z := by
  unfold FluxTerm.eval
  rw [mflux_sub_smul]
  congr 1
  · congr 1
    · funext j k
      simp only [diffs_append, sdiff]
      congr 2
      abel_nf
    · simp only
      congr 1
      abel
  · simp only
    rw [famWord_D_append]
    congr 2
    abel_nf

/-- The new term of one slow step. -/
theorem metricFluxChange_eq_eval (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (i : Fin 2) (h : ℝ) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    h⁻¹ • metricFluxChange (fun τ _ => G τ (X + h • basisVec i)) (fun τ _ => G τ X)
      (fun τ k => cellGradComp ((famWord G Φ l h).D (X + h • basisVec i) τ) k) t z =
      (⟨[i], 0, l, h • basisVec i⟩ : FluxTerm).eval G Φ h X t z := by
  ext k
  simp only [metricFluxChange, FluxTerm.eval, mflux, diffs, List.foldl_cons, List.foldl_nil,
    sdiff, add_zero, PiLp.smul_apply, Fin.sum_univ_two, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem list_sum_map_sub {α M : Type*} [AddCommGroup M] (L : List α) (A B : α → M) :
    (L.map A).sum - (L.map B).sum = (L.map fun τ => A τ - B τ).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ← ih]; abel

theorem list_smul_sum {α M : Type*} [AddCommGroup M] [Module ℝ M] (r : ℝ) (L : List α)
    (A : α → M) : r • (L.map A).sum = (L.map fun τ => r • A τ).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, smul_add, ih]

theorem list_sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (g : α → List β)
    (A : β → M) : ((L.flatMap g).map A).sum = (L.map fun τ => ((g τ).map A).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

/-- The flux of the word `l` is the sum of its flux terms (zero initial flux). -/
theorem famWord_F (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (hF : Φ.F = fun _ _ _ => 0)
    (h : ℝ) (l : List (Fin 2)) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    (famWord G Φ l h).F X t z = ((terms h l).map fun τ => τ.eval G Φ h X t z).sum := by
  induction l using List.reverseRecOn generalizing X with
  | nil => simp [famWord, terms, hF]
  | append_singleton l i ih =>
      rw [famWord_append, terms_append]
      change h⁻¹ • ((famWord G Φ l h).F (X + h • basisVec i) t z - (famWord G Φ l h).F X t z +
        metricFluxChange (fun τ _ => G τ (X + h • basisVec i)) (fun τ _ => G τ X)
          (fun τ k => cellGradComp ((famWord G Φ l h).D (X + h • basisVec i) τ) k) t z) = _
      rw [smul_add, metricFluxChange_eq_eval, ih, ih, list_sum_map_sub, list_smul_sum]
      simp only [termsStep, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      congr 1
      rw [list_sum_map_flatMap]
      congr 1
      refine List.map_congr_left fun τ _ => ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact FluxTerm.eval_step G Φ h τ i X t z

end AVRegularity.QuietDecay
end
end
end

section
section
/-! Counting the flux terms of a word: there are fewer than `2^|l|`, each with a metric word of
length at most `|l|` and a gradient word strictly shorter than `l`. -/

@[expose] public noncomputable section

namespace AVRegularity.QuietDecay

theorem terms_length_le (h : ℝ) (l : List (Fin 2)) : (terms h l).length + 1 ≤ 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [terms]
  | append_singleton l i ih =>
      rw [terms_append]
      have hc : ∀ L : List FluxTerm, (L.flatMap fun τ => [(⟨τ.gw ++ [i], τ.gs, τ.dw,
          τ.ds + h • Homogenization.basisVec i⟩ : FluxTerm), ⟨τ.gw, τ.gs, τ.dw ++ [i], τ.ds⟩]).length =
          2 * L.length := by
        intro L
        induction L with
        | nil => simp
        | cons a L ihL => simp only [List.flatMap_cons, List.length_append, ihL,
            List.length_cons, List.length_nil]; ring
      simp only [termsStep, List.length_append, List.length_singleton]
      rw [hc, pow_succ]
      omega

theorem mem_terms (h : ℝ) (l : List (Fin 2)) :
    ∀ τ ∈ terms h l, τ.dw.length < l.length ∧ τ.gw.length ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [terms]
  | append_singleton l i ih =>
      intro τ hτ
      rw [terms_append] at hτ
      simp only [termsStep, List.mem_append, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] at hτ
      simp only [List.length_append, List.length_singleton]
      rcases hτ with ⟨τ', hτ', rfl | rfl⟩ | rfl
      · have := ih τ' hτ'
        simp only [List.length_append, List.length_singleton]
        omega
      · have := ih τ' hτ'
        simp only [List.length_append, List.length_singleton]
        omega
      · simp

end AVRegularity.QuietDecay
end
end

section
/-! The members of the iterated slow families: mean zero, measurable sources and fluxes, and the
pointwise bound of the flux by the gradients of the lower members. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.QuietDecay

/-- The product measure of the window and the cell. -/
abbrev winMeasure (J : Set ℝ) : Measure (ℝ × Vec 2) :=
  (volume.restrict J).prod (volume.restrict AVenhance.unitCube)

theorem diffs_measurable (h : ℝ) (g : ℝ → Vec 2 → ℝ) (hg : ∀ Y, Measurable fun t => g t Y)
    (l : List (Fin 2)) (Y : Vec 2) : Measurable fun t => diffs l h (g t) Y := by
  induction l using List.reverseRecOn generalizing Y with
  | nil => exact hg Y
  | append_singleton l i ih =>
      simp only [diffs_append, sdiff]
      exact ((ih _).sub (ih Y)).const_mul _

theorem famWord_src_append (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (i : Fin 2) (h : ℝ) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    (famWord G Φ (l ++ [i]) h).src X t z = (h⁻¹ : ℂ) *
      ((famWord G Φ l h).src (X + h • basisVec i) t z - (famWord G Φ l h).src X t z) := by
  rw [famWord_append]; rfl

theorem famWord_srcm {J : Set ℝ} (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (hΦ : ∀ X, AEStronglyMeasurable (Function.uncurry (Φ.src X)) (winMeasure J)) (h : ℝ)
    (l : List (Fin 2)) (X : Vec 2) :
    AEStronglyMeasurable (Function.uncurry ((famWord G Φ l h).src X)) (winMeasure J) := by
  induction l using List.reverseRecOn generalizing X with
  | nil => exact hΦ X
  | append_singleton l i ih =>
      have e : Function.uncurry ((famWord G Φ (l ++ [i]) h).src X) = fun p =>
          (h⁻¹ : ℂ) * (Function.uncurry ((famWord G Φ l h).src (X + h • basisVec i)) p -
            Function.uncurry ((famWord G Φ l h).src X) p) := by
        funext p; exact famWord_src_append G Φ l i h X p.1 p.2
      rw [e]
      exact aestronglyMeasurable_const.mul ((ih _).sub (ih X))

theorem cellValue_smul_sub (D₁ D₂ : ℝ → RawJet2 1 ℂ) (h t : ℝ) :
    cellValue (fun s => h⁻¹ • (D₁ s - D₂ s)) t = fun x => (h⁻¹ : ℂ) * (cellValue D₁ t x - cellValue D₂ t x) := by
  funext x
  simp [cellValue, Complex.real_smul]

theorem famWord_mean {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam}
    {v : ℝ → Vec 2 → Vec 2} (hΦ : IsCellFam J G v Φ)
    (hm : ∀ X, ∀ t ∈ J, cellMean (cellValue (Φ.D X) t) = 0) (h : ℝ) (l : List (Fin 2)) (X : Vec 2)
    (t : ℝ) (ht : t ∈ J) : cellMean (cellValue ((famWord G Φ l h).D X) t) = 0 := by
  induction l using List.reverseRecOn generalizing X with
  | nil => exact hm X t ht
  | append_singleton l i ih =>
      have hfam := isCellFam_famWord hΦ l h
      have e : cellValue ((famWord G Φ (l ++ [i]) h).D X) t = fun x => (h⁻¹ : ℂ) *
          (cellValue ((famWord G Φ l h).D (X + h • basisVec i)) t x -
            cellValue ((famWord G Φ l h).D X) t x) := by
        have := cellValue_smul_sub ((famWord G Φ l h).D (X + h • basisVec i))
          ((famWord G Φ l h).D X) h t
        rw [← this]
        congr 1
        funext s
        exact famWord_D_append G Φ l i h X s
      have : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ]
        have hsub : AVenhance.unitCube ⊆ Set.Icc (0 : Vec 2) 1 := fun x hx =>
          ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
        exact (measure_mono hsub).trans_lt measure_Icc_lt_top
      have i1 := ((hfam (X + h • basisVec i)).2.2.1 t ht).1.integrable one_le_two
      have i2 := ((hfam X).2.2.1 t ht).1.integrable one_le_two
      rw [e]
      unfold cellMean at *
      rw [integral_const_mul, integral_sub i1 i2]
      have h1 := ih (X + h • basisVec i)
      have h2 := ih X
      rw [h1, h2, sub_zero, mul_zero]

theorem mflux_aestronglyMeasurable {J : Set ℝ} {M : ℝ → Fin 2 → Fin 2 → ℝ}
    (hM : ∀ j k, Measurable fun t => M t j k) {D : ℝ → RawJet2 1 ℂ}
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2) (winMeasure J)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => mflux (M p.1) (D p.1) p.2) (winMeasure J) := by
  have hc : ∀ k, AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      ∑ j : Fin 2, (M p.1 j k : ℂ) * cellGradComp (D p.1) j p.2) (winMeasure J) := by
    intro k
    have hj : ∀ j, AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
        (M p.1 j k : ℂ) * cellGradComp (D p.1) j p.2) (winMeasure J) := fun j =>
      ((Complex.measurable_ofReal.comp ((hM j k).comp measurable_fst)).aestronglyMeasurable).mul
        (hD _)
    simp only [Fin.sum_univ_two]
    exact (hj 0).add (hj 1)
  have h1 : AEStronglyMeasurable (fun p : ℝ × Vec 2 => fun k =>
      ∑ j : Fin 2, (M p.1 j k : ℂ) * cellGradComp (D p.1) j p.2) (winMeasure J) :=
    (aemeasurable_pi_iff.mpr fun k => (hc k).aemeasurable).aestronglyMeasurable
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp_aestronglyMeasurable h1

theorem famWord_Fm {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam}
    {v : ℝ → Vec 2 → Vec 2} (hΦ : IsCellFam J G v Φ) (hF : Φ.F = fun _ _ _ => 0)
    (hGm : ∀ Y i j, Measurable fun t => G t Y i j) (h : ℝ) (l : List (Fin 2)) (X : Vec 2) :
    AEStronglyMeasurable (Function.uncurry ((famWord G Φ l h).F X)) (winMeasure J) := by
  have e : Function.uncurry ((famWord G Φ l h).F X) =
      fun p => ((terms h l).map fun τ => τ.eval G Φ h X p.1 p.2).sum := by
    funext p; exact famWord_F G Φ hF h l X p.1 p.2
  rw [e]
  have hterm : ∀ τ : FluxTerm, AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => τ.eval G Φ h X p.1 p.2) (winMeasure J) := by
    intro τ
    exact mflux_aestronglyMeasurable
      (fun j k => diffs_measurable h (fun t Y => G t Y j k) (fun Y => hGm Y j k) τ.gw _)
      ((isCellFam_famWord hΦ τ.dw h (X + τ.ds)).2.2.2.1)
  induction (terms h l) with
  | nil => exact aestronglyMeasurable_const
  | cons τ L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hterm τ).add ih

/-- The pointwise bound of a flux term. -/
theorem norm_eval_le (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (h Γ : ℝ)
    (τ : FluxTerm) (X : Vec 2) (t : ℝ) (z : Vec 2) (k : Fin 2)
    (hΓ : ∀ j, |diffs τ.gw h (fun Y => G t Y j k) (X + τ.gs)| ≤ Γ) :
    ‖τ.eval G Φ h X t z k‖ ≤
      ∑ j : Fin 2, Γ * ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) t) j z‖ := by
  simp only [FluxTerm.eval, mflux, PiLp.toLp_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hΓ j) (norm_nonneg _)

end AVRegularity.QuietDecay
end
end

section
/-! The cell `L²` bound of the flux of an iterated family member at one time by the gradients of
the lower members, and the measurability of time densities. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.QuietDecay

theorem list_sq_sum_le {α : Type*} (L : List α) (f : α → ℝ) :
    (L.map f).sum ^ 2 ≤ L.length * (L.map fun x => f x ^ 2).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      set S := (L.map f).sum
      set Q := (L.map fun x => f x ^ 2).sum
      have hQ : 0 ≤ Q := List.sum_nonneg fun y hy => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; positivity
      set n : ℝ := (L.length : ℝ)
      have hn : 0 ≤ n := Nat.cast_nonneg _
      have key : 2 * f a * S ≤ n * f a ^ 2 + Q := by
        rcases hn.eq_or_lt with h0 | hpos
        · have : S ^ 2 ≤ 0 := by rw [← h0] at ih; simpa using ih
          have hS : S = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg S))
          rw [hS, ← h0]; simp [hQ]
        · have h1 : n * (2 * f a * S) ≤ n * (n * f a ^ 2 + Q) := by
            nlinarith [sq_nonneg (n * f a - S)]
          exact le_of_mul_le_mul_left h1 hpos
      push_cast
      nlinarith [key, ih]

/-- A time density of a jointly measurable field is a.e.-measurable. -/
theorem aemeasurable_cellL2Norm_sq {J : Set ℝ} {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → Vec 2 → E} (hf : AEStronglyMeasurable (Function.uncurry f) (winMeasure J)) :
    AEMeasurable (fun σ => cellL2Norm (f σ) ^ 2) (volume.restrict J) := by
  have h1 : AEMeasurable (fun σ => ∫⁻ z in AVenhance.unitCube, ‖f σ z‖ₑ ^ 2)
      (volume.restrict J) :=
    ((hf.enorm.pow_const 2).lintegral_prod_right' : _)
  refine h1.congr ?_
  filter_upwards [hf.prodMk_left] with σ hσ
  exact (cellL2Norm_sq_eq_lintegral hσ).symm

theorem enorm_sq_ofReal {F : Type*} [NormedAddCommGroup F] (w : F) :
    ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The pointwise flux bound: `‖F_k‖² ≤ 2 T Γ² Σ_τ Σ_j ‖∇_j D_τ‖²`. -/
theorem flux_pt_le (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (hF : Φ.F = fun _ _ _ => 0) (h Γ : ℝ) (hΓ0 : 0 ≤ Γ) (l : List (Fin 2)) (X : Vec 2) (σ : ℝ)
    (hΓ : ∀ τ ∈ terms h l, ∀ j k, |diffs τ.gw h (fun Y => G σ Y j k) (X + τ.gs)| ≤ Γ)
    (k : Fin 2) (z : Vec 2) :
    ‖(famWord G Φ l h).F X σ z k‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * (terms h l).length * Γ ^ 2) *
      ((terms h l).map fun τ => ∑ j : Fin 2,
        ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2).sum := by
  set T := terms h l
  set g : FluxTerm → Fin 2 → ℝ := fun τ j =>
    ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖
  have h1 : ‖(famWord G Φ l h).F X σ z k‖ ≤ (T.map fun τ => ∑ j : Fin 2, Γ * g τ j).sum := by
    rw [famWord_F G Φ hF h l X σ z]
    have : ∀ L : List FluxTerm, (∀ τ ∈ L, τ ∈ T) →
        ‖(L.map fun τ => τ.eval G Φ h X σ z).sum k‖ ≤
          (L.map fun τ => ∑ j : Fin 2, Γ * g τ j).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons τ L ih =>
          simp only [List.map_cons, List.sum_cons, PiLp.add_apply]
          refine (norm_add_le _ _).trans (add_le_add ?_ (ih fun τ' h' => hL τ' (by simp [h'])))
          exact norm_eval_le G Φ h Γ τ X σ z k fun j => hΓ τ (hL τ (by simp)) j k
    exact this T fun τ h => h
  have hA : ∀ τ, (∑ j : Fin 2, Γ * g τ j) ^ 2 ≤ 2 * Γ ^ 2 * ∑ j : Fin 2, g τ j ^ 2 := by
    intro τ
    simp only [Fin.sum_univ_two]
    nlinarith [sq_nonneg (g τ 0 - g τ 1), sq_nonneg Γ, mul_nonneg hΓ0 hΓ0]
  have hS0 : 0 ≤ (T.map fun τ => ∑ j : Fin 2, Γ * g τ j).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
      exact Finset.sum_nonneg fun j _ => mul_nonneg hΓ0 (norm_nonneg _)
  have h2 : ‖(famWord G Φ l h).F X σ z k‖ ^ 2 ≤
      2 * T.length * Γ ^ 2 * (T.map fun τ => ∑ j : Fin 2, g τ j ^ 2).sum := by
    calc ‖(famWord G Φ l h).F X σ z k‖ ^ 2
        ≤ (T.map fun τ => ∑ j : Fin 2, Γ * g τ j).sum ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ T.length * (T.map fun τ => (∑ j : Fin 2, Γ * g τ j) ^ 2).sum := list_sq_sum_le _ _
      _ ≤ T.length * (T.map fun τ => 2 * Γ ^ 2 * ∑ j : Fin 2, g τ j ^ 2).sum := by
          gcongr
          exact List.sum_le_sum fun τ _ => hA τ
      _ = 2 * T.length * Γ ^ 2 * (T.map fun τ => ∑ j : Fin 2, g τ j ^ 2).sum := by
          have e := list_smul_sum (2 * Γ ^ 2) T (fun τ => ∑ j : Fin 2, g τ j ^ 2)
          simp only [smul_eq_mul] at e
          rw [← e]
          ring
  have hnn : ∀ τ, 0 ≤ ∑ j : Fin 2, g τ j ^ 2 := fun τ => by positivity
  rw [enorm_sq_ofReal]
  have hsum : (T.map fun τ => ∑ j : Fin 2,
      ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2).sum =
      ENNReal.ofReal (T.map fun τ => ∑ j : Fin 2, g τ j ^ 2).sum := by
    have : ∀ L : List FluxTerm, (L.map fun τ => ∑ j : Fin 2,
        ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2).sum =
        ENNReal.ofReal (L.map fun τ => ∑ j : Fin 2, g τ j ^ 2).sum := by
      intro L
      induction L with
      | nil => simp
      | cons τ L ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih, ENNReal.ofReal_add (hnn τ) (List.sum_nonneg fun y hy => by
            obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; exact hnn x)]
          congr 1
          rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
          exact Finset.sum_congr rfl fun j _ => enorm_sq_ofReal _
    exact this T
  rw [hsum, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h2

/-- The cell `L²` flux bound of a member at one time. -/
theorem flux_sq_le (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (hF : Φ.F = fun _ _ _ => 0) (h Γ : ℝ) (hΓ0 : 0 ≤ Γ) (l : List (Fin 2)) (X : Vec 2) (σ : ℝ)
    (hΓ : ∀ τ ∈ terms h l, ∀ j k, |diffs τ.gw h (fun Y => G σ Y j k) (X + τ.gs)| ≤ Γ)
    (hmeas : ∀ τ ∈ terms h l, ∀ j, AEStronglyMeasurable
      (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) (volume.restrict AVenhance.unitCube))
    (hFm : ∀ k, AEStronglyMeasurable (fun z => (famWord G Φ l h).F X σ z k)
      (volume.restrict AVenhance.unitCube)) :
    ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Φ l h).F X σ z k) ^ 2 ≤
      ENNReal.ofReal (4 * (terms h l).length * Γ ^ 2) *
        ((terms h l).map fun τ => ∑ j : Fin 2,
          cellL2Norm (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) ^ 2).sum := by
  set T := terms h l
  have hint : ∀ L : List FluxTerm, (∀ τ ∈ L, τ ∈ T) →
      ∫⁻ z in AVenhance.unitCube, (L.map fun τ => ∑ j : Fin 2,
        ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2).sum =
      (L.map fun τ => ∑ j : Fin 2,
        cellL2Norm (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) ^ 2).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons τ L ih =>
        simp only [List.map_cons, List.sum_cons]
        have hm : AEMeasurable (fun z => ∑ j : Fin 2,
            ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2)
            (volume.restrict AVenhance.unitCube) :=
          by
            simp only [Fin.sum_univ_two]
            exact ((hmeas τ (hL τ (by simp)) 0).enorm.pow_const 2).add
              ((hmeas τ (hL τ (by simp)) 1).enorm.pow_const 2)
        rw [lintegral_add_left' hm, ih fun τ' h' => hL τ' (by simp [h'])]
        congr 1
        rw [lintegral_finsetSum' _ fun j _ => (hmeas τ (hL τ (by simp)) j).enorm.pow_const 2]
        exact Finset.sum_congr rfl fun j _ =>
          (cellL2Norm_sq_eq_lintegral (hmeas τ (hL τ (by simp)) j)).symm
  calc ∑ k : Fin 2, cellL2Norm (fun z => (famWord G Φ l h).F X σ z k) ^ 2
      = ∑ k : Fin 2, ∫⁻ z in AVenhance.unitCube, ‖(famWord G Φ l h).F X σ z k‖ₑ ^ 2 :=
        Finset.sum_congr rfl fun k _ => cellL2Norm_sq_eq_lintegral (hFm k)
    _ ≤ ∑ _k : Fin 2, ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal (2 * T.length * Γ ^ 2) *
          (T.map fun τ => ∑ j : Fin 2,
            ‖cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j z‖ₑ ^ 2).sum :=
        Finset.sum_le_sum fun k _ => lintegral_mono fun z =>
          flux_pt_le G Φ hF h Γ hΓ0 l X σ hΓ k z
    _ = ENNReal.ofReal (4 * T.length * Γ ^ 2) *
          (T.map fun τ => ∑ j : Fin 2,
            cellL2Norm (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) ^ 2).sum := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hint T fun τ h => h,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [show (4 : ℝ) * T.length * Γ ^ 2 = 2 * (2 * T.length * Γ ^ 2) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        norm_num

end AVRegularity.QuietDecay
end
end

section
/-! The slow engine: endpoint and weighted gradient bounds of all members of the iterated slow
difference families of a family of cell solutions, uniform in the slow point and in the step, by
induction on the length of the word. The flux of a member is controlled by the weighted gradient
energies of strictly shorter members (`flux_sq_le`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.QuietDecay

/-- The hypotheses of the slow engine on the window `[a, b]` with step `h` and metric
difference bound `Γ` through `P` letters. -/
structure EngineHyp (a b : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (h Γ : ℝ) (P : ℕ) : Prop where
  hab : a ≤ b
  Gm : ∀ X i j, Measurable fun t => G t X i j
  Gs : ∀ t ∈ Icc a b, ∀ X i j, G t X i j = G t X j i
  Ge : ∀ t ∈ Icc a b, ∀ X (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t X i j * ξ i * ξ j ∧
    ∑ i, ∑ j, G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2
  fam : IsCellFam (Icc a b) G (fun _ _ => 0) Φ
  F0 : Φ.F = fun _ _ _ => 0
  mean : ∀ X, ∀ t ∈ Icc a b, cellMean (cellValue (Φ.D X) t) = 0
  srcm : ∀ X, AEStronglyMeasurable (Function.uncurry (Φ.src X)) (winMeasure (Icc a b))
  Γ0 : 0 ≤ Γ
  Gd : ∀ t ∈ Icc a b, ∀ gw : List (Fin 2), gw.length ≤ P → ∀ Y j k,
    |diffs gw h (fun Y => G t Y j k) Y| ≤ Γ

variable {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam} {h Γ : ℝ} {P : ℕ}

/-- The exponential weight `e^{-π² (τ - σ)}`. -/
def wt (τ σ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) * (τ - σ)))

/-- The engine constants. -/
def engK (Γ : ℝ) : ℕ → ℝ≥0∞
  | 0 => 2
  | n + 1 => engK Γ n + 2 * (1 + ENNReal.ofReal (32 * 4 ^ (n + 1) * Γ ^ 2) * engK Γ n)

theorem engK_mono (Γ : ℝ) {m n : ℕ} (hmn : m ≤ n) : engK Γ m ≤ engK Γ n := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp only [engK]; exact le_self_add)

theorem list_smul_sum_ennreal {α : Type*} (r : ℝ≥0∞) (L : List α) (A : α → ℝ≥0∞) :
    (L.map fun x => r * A x).sum = r * (L.map A).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem wt_measurable (τ : ℝ) : Measurable (wt τ) := by
  unfold wt
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_const.sub measurable_id)))

theorem lintegral_list_sum {α : Type*} {μ : Measure ℝ} (L : List α) (f : α → ℝ → ℝ≥0∞)
    (hf : ∀ x ∈ L, AEMeasurable (f x) μ) :
    ∫⁻ σ, (L.map fun x => f x σ).sum ∂μ = (L.map fun x => ∫⁻ σ, f x σ ∂μ).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [lintegral_add_left' (hf x (by simp)), ih fun y hy => hf y (by simp [hy])]

/-- The gradient energy density of a member at the time `σ`. -/
def gradDen (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam) (h : ℝ)
    (l : List (Fin 2)) (X : Vec 2) (σ : ℝ) : ℝ≥0∞ :=
  ∑ j : Fin 2, cellL2Norm (cellGradComp ((famWord G Φ l h).D X σ) j) ^ 2

section Core

variable (H : EngineHyp a b G Φ h Γ P)
include H

theorem member_sol (l : List (Fin 2)) (X : Vec 2) :
    IsCellSolution (Icc a b) (slowCoeffs G (fun _ _ => 0) X) ((famWord G Φ l h).src X)
      ((famWord G Φ l h).F X) ((famWord G Φ l h).D X) :=
  isCellFam_famWord H.fam l h X

theorem gradDen_aemeasurable (l : List (Fin 2)) (X : Vec 2) :
    AEMeasurable (gradDen G Φ h l X) (volume.restrict (Icc a b)) := by
  unfold gradDen
  have hj : ∀ j : Fin 2, AEMeasurable (fun σ =>
      cellL2Norm (cellGradComp ((famWord G Φ l h).D X σ) j) ^ 2) (volume.restrict (Icc a b)) :=
    fun j => aemeasurable_cellL2Norm_sq (f := fun σ z => cellGradComp ((famWord G Φ l h).D X σ) j z)
      ((member_sol H l X).2.2.2.1 _)
  simp only [Fin.sum_univ_two]
  exact (hj 0).add (hj 1)

theorem src_aemeasurable (l : List (Fin 2)) (X : Vec 2) :
    AEMeasurable (fun σ => cellL2Norm ((famWord G Φ l h).src X σ) ^ 2) (volume.restrict (Icc a b)) :=
  aemeasurable_cellL2Norm_sq (famWord_srcm G Φ H.srcm h l X)

theorem ae_flux_meas (l : List (Fin 2)) (X : Vec 2) :
    ∀ᵐ σ ∂volume.restrict (Icc a b), ∀ k, AEStronglyMeasurable
      (fun z => (famWord G Φ l h).F X σ z k) (volume.restrict AVenhance.unitCube) := by
  filter_upwards [(famWord_Fm H.fam H.F0 H.Gm h l X).prodMk_left] with σ hσ k
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).continuous.comp_aestronglyMeasurable hσ

theorem ae_grad_meas (l : List (Fin 2)) (X : Vec 2) :
    ∀ᵐ σ ∂volume.restrict (Icc a b), ∀ τ ∈ terms h l, ∀ j, AEStronglyMeasurable
      (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) (volume.restrict AVenhance.unitCube) := by
  classical
  have : ∀ τ ∈ (terms h l).toFinset, ∀ᵐ σ ∂volume.restrict (Icc a b), ∀ j, AEStronglyMeasurable
      (cellGradComp ((famWord G Φ τ.dw h).D (X + τ.ds) σ) j) (volume.restrict AVenhance.unitCube) := by
    intro τ _
    filter_upwards [(member_sol H τ.dw (X + τ.ds)).2.1] with σ hσ j
    exact (hσ.2.1 _).aestronglyMeasurable
  have h2 := (Filter.eventually_all_finset _).2 this
  filter_upwards [h2] with σ hσ τ hτ
  exact hσ τ (List.mem_toFinset.2 hτ)

theorem member_mean (l : List (Fin 2)) (X : Vec 2) (t : ℝ) (ht : t ∈ Icc a b) :
    cellMean (cellValue ((famWord G Φ l h).D X) t) = 0 :=
  famWord_mean H.fam H.mean h l X t ht

omit H in
theorem terms_sq_le (l : List (Fin 2)) :
    (((terms h l).length : ℝ)) ^ 2 ≤ 4 ^ l.length := by
  have h1 := terms_length_le h l
  have h2 : ((terms h l).length : ℝ) ≤ 2 ^ l.length := by
    have : (terms h l).length ≤ 2 ^ l.length := by omega
    exact_mod_cast this
  calc (((terms h l).length : ℝ)) ^ 2 ≤ (2 ^ l.length) ^ 2 := by gcongr
    _ = 4 ^ l.length := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

end Core

end AVRegularity.QuietDecay
end
end
end
