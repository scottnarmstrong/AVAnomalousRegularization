-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.Families.QuietTransitionBridge
public import AVRegularity.CycleComparison.Reconstruction.ChainLinear
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
import AVRegularity.CycleComparison.LiftSetting.Metric
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseChartIndex
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.Proofs.Intermediate.CycleComparison.OcFlowJets
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Residual.TailDiff.Main
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Residual.QuietMean.CellMean
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Quiet overlaps: the transported physical edges of two pieces coincide**.

The quiet transition is asserted on the trimmed quiet overlap only.

Let `tr : ChartTransition (F.piece p) (F.piece q)`, `y = Υ(y')`, `Φ_q(t,y') = Φ_p(t,Υ(y'))`, and
`F.IsQuietTransition ν e E tr c c'`. Write `χ_p = Φ_p(t,·)`, `ψ_p = χ_p⁻¹`, `K_p = D χ_p ∘ ψ_p`
(`chartInvJacobian ψ_p`), `K_Υ = chartInvJacobian Υ`.

* `transition_label`, `transition_right_inv`, `transition_left_inv`: `Υ ∘ ψ_q = ψ_p`, and `Υ` is a
  diffeomorphism with inverse `ψ_q ∘ χ_p`.
* `chartInvJacobian_transition`: `K_p(x) = K_q(x) K_Υ(ψ_q x)` (chain rule).
* `dimFlux_quiet`: on the overlap, `∑_σ 𝔞_q[r+1, A∘σ](t, y', e⁻¹y') = ∑_σ B̃_{r+1,A∘σ}(y')`,
  the transport along `Υ` of the old samples `𝔞_p(t, Υ y', e⁻¹ Υ y')`, summed over the
  permutations of the word (`IsQuietTransition.summed` with the fast variable `e⁻¹y'`, then
  `IsQuietTransition.fastIndependent` to move the fast variable of the old fields to
  `e⁻¹ Υ y'`). The quiet transition is read only through these two bridge lemmas.
* `constituent_transition_of_contDiff`: the ordered derivatives of a `C^r` field are symmetric in
  the words of length at most `r`,
  so the word sums of the two sides see only the permutation sums
  (`sum_word_smul_eq_of_perm_sum`).
* `labelEdgeFlux_transition_of_contDiff`: on the overlap,
  `G_q(y')_{i₀} = ∑_j K_Υ(y')_{i₀ j} G_p(Υ y')_j` for the label edge fluxes of the label fields
  `U ∘ χ_q` and `U ∘ χ_p` (jets: `transportedCoeff_flux` along `Υ`).
* `pieceFlux_transition_of_contDiff`: at `x` with `(t, ψ_q x)` in the overlap,
  `∑_{i₀} K_q(x)_{a₀ i₀} G_q(ψ_q x)_{i₀} = ∑_j K_p(x)_{a₀ j} G_p(ψ_p x)_j`.
* `edgeFlux_quiet_overlap_of_contDiff`: if at `t` only `p ≠ q` are active, with weights summing to
  one, and the actual contexts are quietly related, the flux term of the actual equation at such `x`
  is the single transported label flux of `p` (`edgeCoefficient = ∑ ϖ_k E_k` collapses).
* `edgeFlux_quiet_overlap_atlas_of_contDiff`: the same, with the quiet transition and the overlap
  membership read off an atlas `T` (`T.IsQuiet`, `T.CoversQuiet`, `T.sameCtx` of the actual
  contexts).

The last five are stated for a physical field `U` of class `C^r` with `D ≤ r + 1`. -/

section
section Transition

/-- `Υ ∘ ψ_q = ψ_p`. -/
theorem transition_label {Pp Pq : ChartPiece} (tr : ChartTransition Pp Pq) (t : ℝ)
    (x : Vec 2) : tr.Υ ((Pq.material t).symm x) = (Pp.material t).symm x := by
  have h1 : Pp.material t (tr.Υ ((Pq.material t).symm x)) = x := by
    rw [← tr.compat t, Homeomorph.apply_symm_apply]
  calc tr.Υ ((Pq.material t).symm x)
      = (Pp.material t).symm (Pp.material t (tr.Υ ((Pq.material t).symm x))) :=
        ((Pp.material t).symm_apply_apply _).symm
    _ = (Pp.material t).symm x := by rw [h1]

/-- `Υ ∘ (ψ_q ∘ χ_p) = id`. -/
theorem transition_right_inv {Pp Pq : ChartPiece} (tr : ChartTransition Pp Pq) (t : ℝ)
    (y : Vec 2) : tr.Υ ((Pq.material t).symm (Pp.material t y)) = y := by
  rw [transition_label tr t, Homeomorph.symm_apply_apply]

/-- `(ψ_q ∘ χ_p) ∘ Υ = id`. -/
theorem transition_left_inv {Pp Pq : ChartPiece} (tr : ChartTransition Pp Pq) (t : ℝ)
    (y' : Vec 2) : (Pq.material t).symm (Pp.material t (tr.Υ y')) = y' := by
  rw [← tr.compat t, Homeomorph.symm_apply_apply]

/-- The inverse transition `ψ_q ∘ χ_p` is smooth. -/
theorem transition_inv_smooth (Pp Pq : ChartPiece) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (Pq.material t).symm (Pp.material t y)) :=
  (Pq.material_symm_smooth t).comp (Pp.material_smooth t)

/-- **The inverse Jacobians compose along the transition:** `K_p(x) = K_q(x) K_Υ(ψ_q x)`. -/
theorem chartInvJacobian_transition {Pp Pq : ChartPiece} (tr : ChartTransition Pp Pq) (t : ℝ)
    (x : Vec 2) (a j : Fin 2) :
    chartInvJacobian ⇑(Pp.material t).symm x a j =
      ∑ i : Fin 2, chartInvJacobian ⇑(Pq.material t).symm x a i *
        chartInvJacobian tr.Υ ((Pq.material t).symm x) i j := by
  have hχpd : Differentiable ℝ ⇑(Pp.material t) :=
    (Pp.material_smooth t).differentiable (by simp)
  have hψpd : Differentiable ℝ ⇑(Pp.material t).symm :=
    (Pp.material_symm_smooth t).differentiable (by simp)
  have hχqd : Differentiable ℝ ⇑(Pq.material t) :=
    (Pq.material_smooth t).differentiable (by simp)
  have hψqd : Differentiable ℝ ⇑(Pq.material t).symm :=
    (Pq.material_symm_smooth t).differentiable (by simp)
  have hΥd : Differentiable ℝ tr.Υ := tr.smooth.differentiable (by simp)
  have hΥid : Differentiable ℝ (fun y => (Pq.material t).symm (Pp.material t y)) :=
    (transition_inv_smooth Pp Pq t).differentiable (by simp)
  have hχp_eq : ⇑(Pp.material t) =
      ⇑(Pq.material t) ∘ fun y => (Pq.material t).symm (Pp.material t y) :=
    funext fun y => by simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  have hcomp : HasFDerivAt ⇑(Pp.material t)
      ((fderiv ℝ ⇑(Pq.material t) ((Pq.material t).symm x)).comp
        (fderiv ℝ (fun y => (Pq.material t).symm (Pp.material t y)) ((Pp.material t).symm x)))
      ((Pp.material t).symm x) := by
    have hq : HasFDerivAt ⇑(Pq.material t) (fderiv ℝ ⇑(Pq.material t) ((Pq.material t).symm x))
        ((Pq.material t).symm (Pp.material t ((Pp.material t).symm x))) := by
      rw [Homeomorph.apply_symm_apply]
      exact (hχqd _).hasFDerivAt
    have h2 := hq.comp ((Pp.material t).symm x) (hΥid ((Pp.material t).symm x)).hasFDerivAt
    rw [← hχp_eq] at h2
    exact h2
  rw [chartInvJacobian_apply_of_inverse hχpd hψpd (Pp.material t).symm_apply_apply
      (Pp.material t).apply_symm_apply x a j, hcomp.fderiv, ContinuousLinearMap.comp_apply,
    transition_clm_apply_eq_sum (fderiv ℝ ⇑(Pq.material t) ((Pq.material t).symm x))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartInvJacobian_apply_of_inverse hχqd hψqd (Pq.material t).symm_apply_apply
      (Pq.material t).apply_symm_apply x a i,
    chartInvJacobian_apply_of_inverse hΥid hΥd (transition_right_inv tr t)
      (transition_left_inv tr t) ((Pq.material t).symm x) i j,
    transition_label tr t x, mul_comm]

end Transition

section Quiet

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [Fintype ι] in
/-- **The quiet transport of one order, summed over the permutations of the word.** On the
overlap, the new samples of order `r + 1` at the fast variable `e⁻¹y'`, summed over the
permutations `A ∘ σ` of the word, are the transport along `Υ` of the old samples taken at
the matched fast variable `e⁻¹ Υ(y')`, summed the same way. -/
theorem dimFlux_quiet (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hquiet : F.IsQuietTransition ν e E tr c c') {t : ℝ} {y' : Vec 2}
    (hov : (t, y') ∈ tr.overlap) (v u : ι) (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r) :
    ∑ σ : Equiv.Perm (Fin r), F.dimFlux ν e E q c' v u γ (r + 1) (A ∘ σ) t y' (e⁻¹ • y') =
      ∑ σ : Equiv.Perm (Fin r),
        transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
          (fun d I => F.dimFlux ν e E p c v u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y')) r (A ∘ σ) y' := by
  have h2 : ∑ σ : Equiv.Perm (Fin r),
      (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) (A ∘ σ) t (E⁻¹ • y') (e⁻¹ • y') =
      ∑ σ : Equiv.Perm (Fin r),
        transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
          (fun d I => F.dimFlux ν e E p c v u γ d I t (tr.Υ y') (e⁻¹ • y')) r (A ∘ σ) y' :=
    hquiet.summed (t, y') hov (e⁻¹ • y') v u γ r A
  have hB : (fun d I => F.dimFlux ν e E p c v u γ d I t (tr.Υ y') (e⁻¹ • y')) =
      fun d I => F.dimFlux ν e E p c v u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y') := by
    funext d I
    have hz : F.flux p c v u γ d I t (E⁻¹ • tr.Υ y') (e⁻¹ • y') =
        F.flux p c v u γ d I t (E⁻¹ • tr.Υ y') (e⁻¹ • tr.Υ y') :=
      (hquiet.fastIndependent (t, y') hov v u γ d I _ _).1
    simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, hz]
  have hr : r + 1 - 2 = r - 1 := by omega
  have h1 : ∀ σ : Equiv.Perm (Fin r),
      F.dimFlux ν e E q c' v u γ (r + 1) (A ∘ σ) t y' (e⁻¹ • y') =
        (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) (A ∘ σ) t (E⁻¹ • y') (e⁻¹ • y') := by
    intro σ
    show (ν * e ^ (r + 1 - 2)) • F.flux q c' v u γ (r + 1) (A ∘ σ) t (E⁻¹ • y') (e⁻¹ • y') = _
    rw [hr]
  rw [Finset.sum_congr rfl fun σ _ => h1 σ, h2, hB]

end Quiet
end

/-! **The sampled source of the lifted pulse, finite smoothness**.

The sampled source of the lifted fiber of a piece is a label divergence of its label edge flux
(as in `sourceOp_lift_apply_eq_labelDiv`), with the sampled field `twoScaleSample ρ e Φ` only
`C^r`, `D ≤ r + 1` (the inner flux uses the label jets of order `≤ D - 1`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **The sampled source of the lifted fiber is a label divergence**, for a `C^r` sampled field
with `D ≤ r + 1`: at `(ρ⁻¹y, e⁻¹y)` it is `e` times the label divergence of `(e/ν)` times the
label edge flux of the piece. -/
theorem sourceOp_lift_eq_label_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P)
    (c : Ctx p) {η ε ρ cℓ lam : ℝ} (he : e ≠ 0) (hν : ν ≠ 0)
    (hscale : Real.sqrt η * ε = e * ρ⁻¹) (hlam : lam * ρ⁻¹ = E⁻¹) (s : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i}
    (hΓ : ∀ v u d, ∀ γ ∈ liftEdges cℓ lam (F.fiber p c) v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α s X z))
    (hΦ : IsBoxSmooth D D Φ) {r : ℕ} (hV : ContDiff ℝ (r : ℕ∞) (twoScaleSample ρ e Φ))
    (hrD : D ≤ r + 1) (y : Vec 2) :
    sourceOp (liftEdges cℓ lam (F.fiber p c)) η ε s Φ (ρ⁻¹ • y) (e⁻¹ • y) =
      e • ∑ k : Fin 2, fderiv ℝ (fun (y' : Vec 2) (v : ι) =>
        (e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k) y
        (basisVec k) := by
  refine (sample_sourceOp_label (liftEdges cℓ lam (F.fiber p c)) he hscale s hΓ hΦ y).trans ?_
  refine congrArg (e • ·) (Finset.sum_congr rfl fun k _ => ?_)
  have hfun : (fun (y' : Vec 2) (v : ι) => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((liftEdges cℓ lam (F.fiber p c) v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α s (ρ⁻¹ • y') (e⁻¹ • y') k) •
            γ.map (e ^ (d.1 - 1) • orderedDerivative α (twoScaleSample ρ e Φ) y' u)).sum) =
      fun (y' : Vec 2) (v : ι) =>
        (e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) (twoScaleSample ρ e Φ) v y' k :=
    funext fun y' => funext fun v =>
      liftFlux_eq_labelEdgeFlux_of_contDiff F ν e E p c cℓ lam ρ s hlam hν hV hrD v y' k
  exact congrArg (fun f : Vec 2 → ∀ i, h i => fderiv ℝ f y (basisVec k)) hfun
end

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.ChartTransport AVRegularity.CycleComparison.Charts
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The renewal chart of a pulse on its window**. Every renewal chart is an exact chart of the
plane (`isChart_ocChart`), and the chart of a pulse is short on the window of the pulse
(`pulseWindow_chartTime`: `|t - lτ''| ≤ τ''` since `τ ≤ τ''/25`), so its jets and those of its
inverse are bounded at the coarse scale `ε_{m-1}` with constants depending only on the order
(`pulseChart_jetBound`, from `Charts.ocChart_window_jets`). -/

/-- **Every renewal chart is an exact chart.** -/
theorem isChart_ocChart {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (α q : ℝ) (Λ m : ℕ)
    (l : ℤ) (t : ℝ) : IsChart (ocChart α q Λ m φ hφ l t) (ocChartInv α q Λ m φ hφ l t) where
  contΦ := ((contDiff_ocChart_joint hφ α q Λ m l).comp
    (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
  contΨ := ((contDiff_ocChartInv_joint hφ α q Λ m l).comp
    (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast le_top)
  left := ocChartInv_ocChart α q Λ m φ hφ l t
  right := ocChart_ocChartInv α q Λ m φ hφ l t
  equiv := fun n y => ocChart_latticeShift hφ α q Λ m l t n y
  det := ocChart_det hφ α q Λ m l t

/-- The renewal charts are smooth at every time. -/
theorem contDiff_ocChart {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (α q : ℝ) (Λ m : ℕ)
    (l : ℤ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φ hφ l t) :=
  (contDiff_ocChart_joint hφ α q Λ m l).comp (contDiff_const.prodMk contDiff_id)

/-- The inverse renewal charts are smooth at every time. -/
theorem contDiff_ocChartInv {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (α q : ℝ)
    (Λ m : ℕ) (l : ℤ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ocChartInv α q Λ m φ hφ l t) :=
  (contDiff_ocChartInv_joint hφ α q Λ m l).comp (contDiff_const.prodMk contDiff_id)

/-- **The chart of a pulse is short on the window of the pulse.** -/
theorem pulseWindow_chartTime (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) {k : ℤ} {t : ℝ}
    (ht : t ∈ ocPulseWindow α q Λ m k) :
    |t - (ocPulseChartIndex α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m := by
  have hh := Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hτ := LiftSetting.ocTau_le_div α q hΛ m
  obtain ⟨h1, h2⟩ := LiftSetting.pulseChartIndex_bounds α q hΛ m k
  obtain ⟨ht1, ht2⟩ := ht
  rw [abs_le]
  constructor <;> linarith

/-- The jet constant of the renewal charts through order `N`. -/
def pulseChartD (N : ℕ) : ℝ :=
  1 + ∑ p ∈ Finset.range (N + 1), |chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) p|

theorem one_le_pulseChartD (N : ℕ) : 1 ≤ pulseChartD N :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- **The jets of the chart of a pulse and of its inverse on the window of the pulse** are
bounded at the coarse scale `ε_{m-1}`. -/
theorem pulseChart_jetBound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (k : ℤ) {t : ℝ} (ht : t ∈ ocPulseWindow α q Λ m k)
    (N : ℕ) :
    JetBound (ocChart α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) N
        (pulseChartD N) (ocEpsilon q Λ (m - 1)) ∧
      JetBound (ocChartInv α q Λ m (Φ (m - 1)) hφ (ocPulseChartIndex α q Λ m k) t) N
        (pulseChartD N) (ocEpsilon q Λ (m - 1)) := by
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (Scales.epsilon_basic (q := q) (Λ := Λ) (m := m - 1) hq.1 hΛ).1
  have hct := pulseWindow_chartTime α q (by omega : 1 ≤ Λ) m ht
  have hj := fun p hp y => ocChart_window_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ
    (ocPulseChartIndex α q Λ m k) t hct p hp y
  exact ⟨jetBound_of_Cχ hE fun p hp _ y => (hj p hp y).1,
    jetBound_of_Cχ hE fun p hp _ y => (hj p hp y).2⟩

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Quiet overlaps for a `C^r` field**.

The physical field `U` is `C^r` with `D ≤ r + 1` (the label words of the flux have length
`≤ D - 1`); the charts and the transition stay smooth. The smoothness-free lemmas
(`transition_label`, `chartInvJacobian_transition`, `dimFlux_quiet`) are reused. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **One constituent across a quiet transition**, for a `C^r` field with `D ≤ r + 1`: on the
overlap, the label flux of the constituent `γ` for the piece `q` at `y'` is its label flux for
the piece `p` at `Υ y'`, transported by `chartInvJacobian Υ`. -/
theorem constituent_transition_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    {p q : P} {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hquiet : F.IsQuietTransition ν e E tr c c') {t : ℝ} {y' : Vec 2}
    (hov : (t, y') ∈ tr.overlap) {r : ℕ} {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U)
    (hrD : D ≤ r + 1) (i u : ι) (γ : F.Γ i u) (i₀ : Fin 2) :
    (F.identity i u γ).map (∑ d ∈ Finset.Icc 1 (F.identity i u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), F.dimFlux ν e E q c' i u γ d I t y' (e⁻¹ • y') i₀ •
          orderedDerivative I (fun y => U ((F.piece q).material t y) u) y') =
      ∑ j : Fin 2, chartInvJacobian tr.Υ y' i₀ j • (F.identity i u γ).map
        (∑ d ∈ Finset.Icc 1 (F.identity i u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          F.dimFlux ν e E p c i u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y') j •
            orderedDerivative I (fun y => U ((F.piece p).material t y) u) (tr.Υ y')) := by
  have hΥi := transition_inv_smooth (F.piece p) (F.piece q) t
  have hVp : ContDiff ℝ (r : ℕ∞) (fun y => U ((F.piece p).material t y) u) :=
    contDiff_pi.1 (hU.comp (((F.piece p).material_smooth t).of_le
      (WithTop.coe_le_coe.mpr le_top))) u
  have hVq : (fun y => U ((F.piece q).material t y) u) =
      (fun y => U ((F.piece p).material t y) u) ∘ tr.Υ :=
    funext fun y => by simp only [Function.comp_apply, tr.compat t y]
  have hsum : ∑ d ∈ Finset.Icc 1 (F.identity i u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), F.dimFlux ν e E q c' i u γ d I t y' (e⁻¹ • y') i₀ •
        orderedDerivative I (fun y => U ((F.piece q).material t y) u) y' =
      ∑ d ∈ Finset.Icc 1 (F.identity i u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        ∑ j : Fin 2, (chartInvJacobian tr.Υ y' i₀ j *
          F.dimFlux ν e E p c i u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y') j) •
          orderedDerivative I (fun y => U ((F.piece p).material t y) u) (tr.Υ y') := by
    rw [transition_sum_Icc_one, ← transportedCoeff_flux_of_contDiff hΥi tr.smooth
      (transition_right_inv tr t) (transition_left_inv tr t) hVp (F.identity i u γ).maxOrder
      ((F.identity i u γ).le_D.trans hrD)
      (fun d I => F.dimFlux ν e E p c i u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y')) y' i₀]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hVq]
    have hsr : s ≤ r := by
      have h1 := Finset.mem_range.1 hs
      have h2 := (F.identity i u γ).le_D
      omega
    have hW : ContDiff ℝ (s : ℕ∞) ((fun y => U ((F.piece p).material t y) u) ∘ tr.Υ) :=
      (hVp.comp (tr.smooth.of_le (WithTop.coe_le_coe.mpr le_top))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hsr))
    exact sum_word_smul_eq_of_perm_sum
      (fun A => F.dimFlux ν e E q c' i u γ (s + 1) A t y' (e⁻¹ • y') i₀)
      (fun A => transportedCoeff (chartInvJacobian tr.Υ) (F.identity i u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c i u γ d I t (tr.Υ y') (e⁻¹ • tr.Υ y')) s A y' i₀)
      (fun A => orderedDerivative A ((fun y => U ((F.piece p).material t y) u) ∘ tr.Υ) y')
      (fun A σ => orderedDerivative_comp_perm_of_contDiff A σ hW y')
      (fun A => by
        have hA := congrFun (dimFlux_quiet F ν e E hquiet hov i u γ s A) i₀
        simp only [Finset.sum_apply] at hA
        exact hA)
  rw [hsum]
  exact map_sum_dir _ _ _ _ _

/-- **The label edge fluxes across a quiet transition**, for a `C^r` field with `D ≤ r + 1`:
on the overlap, `G_q(y')_{i₀} = ∑_j K_Υ(y')_{i₀ j} G_p(Υ y')_j`. -/
theorem labelEdgeFlux_transition_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    {p q : P} {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hquiet : F.IsQuietTransition ν e E tr c c') {t : ℝ} {y' : Vec 2}
    (hov : (t, y') ∈ tr.overlap) {r : ℕ} {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U)
    (hrD : D ≤ r + 1) (i : ι) (i₀ : Fin 2) :
    labelEdgeFlux F ν e E q c' t (fun y => U ((F.piece q).material t y)) i y' i₀ =
      ∑ j : Fin 2, chartInvJacobian tr.Υ y' i₀ j •
        labelEdgeFlux F ν e E p c t (fun y => U ((F.piece p).material t y)) i (tr.Υ y') j := by
  simp only [labelEdgeFlux]
  refine Eq.trans (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun γ _ =>
    constituent_transition_of_contDiff F ν e E hquiet hov hU hrD i u γ i₀) ?_
  refine Eq.trans (sum_dep_pull _ _) ?_
  simp only [Finset.smul_sum]

/-- **The transported label fluxes of the two pieces agree**, for a `C^r` field with
`D ≤ r + 1`: at `x` with `(t, ψ_q x)` in the overlap,
`∑_{i₀} K_q(x)_{a₀ i₀} G_q(ψ_q x)_{i₀} = ∑_j K_p(x)_{a₀ j} G_p(ψ_p x)_j`. -/
theorem pieceFlux_transition_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hquiet : F.IsQuietTransition ν e E tr c c') {t : ℝ} {r : ℕ} {U : Vec 2 → ∀ i, h i}
    (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι) (x : Vec 2)
    (hov : (t, ((F.piece q).material t).symm x) ∈ tr.overlap) (a₀ : Fin 2) :
    ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece q).material t).symm x a₀ i₀ •
        labelEdgeFlux F ν e E q c' t (fun y => U ((F.piece q).material t y)) i
          (((F.piece q).material t).symm x) i₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece p).material t).symm x a₀ j •
        labelEdgeFlux F ν e E p c t (fun y => U ((F.piece p).material t y)) i
          (((F.piece p).material t).symm x) j := by
  simp only [labelEdgeFlux_transition_of_contDiff F ν e E hquiet hov hU hrD i, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm, transition_label tr t x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← chartInvJacobian_transition tr t x a₀ j]

/-- **The flux term on a quiet overlap**, for a `C^r` field with `D ≤ r + 1`: if only `p ≠ q`
are active at `t`, with weights summing to one, and the actual contexts are quietly related, the
flux term of the actual equation at `x` is the transported label flux of `p`. -/
theorem edgeFlux_quiet_overlap_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) {t : ℝ} {p q : P}
    (hpq : p ≠ q) {tr : ChartTransition (F.piece p) (F.piece q)}
    (hquiet : F.IsQuietTransition ν e E tr (actual p) (actual q))
    (hw : ∀ p', F.weight p' t ≠ 0 → p' = p ∨ p' = q) (hsum : F.weight p t + F.weight q t = 1)
    {r : ℕ} {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι)
    (x : Vec 2) (hov : (t, ((F.piece q).material t).symm x) ∈ tr.overlap) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece p).material t).symm x a₀ j •
        labelEdgeFlux F ν e E p (actual p) t (fun y => U ((F.piece p).material t y)) i
          (((F.piece p).material t).symm x) j := by
  classical
  have hS : ∀ p', F.weight p' t ≠ 0 → p' ∈ ({p, q} : Finset P) := fun p' hp' => by
    rcases hw p' hp' with h' | h'
    · rw [h']
      exact Finset.mem_insert_self p {q}
    · rw [h']
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  rw [edgeFlux_eq_sum_pieces_of_contDiff F ν e E actual K hdesc {p, q} hS hU hrD i x a₀,
    Finset.sum_pair hpq, pieceFlux_transition_of_contDiff F ν e E hquiet hU hrD i x hov a₀,
    ← add_smul, hsum, one_smul]

/-- **The flux term on a quiet overlap of an atlas**: `edgeFlux_quiet_overlap_of_contDiff` with
the quiet transition and the overlap membership read off an atlas `T`. -/
theorem edgeFlux_quiet_overlap_atlas_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) (T : F.Atlas)
    {quiet W : Set ℝ} (hTcov : T.CoversQuiet quiet W) (hTq : T.IsQuiet ν e E) {t : ℝ}
    {p q : P} (hpq : p ≠ q) (hadj : T.adjacent p q)
    (hctx : T.sameCtx p q hadj (actual p) (actual q))
    (ht : t ∈ quiet ∩ W ∩ (F.piece p).output ∩ (F.piece q).output)
    (hw : ∀ p', F.weight p' t ≠ 0 → p' = p ∨ p' = q) (hsum : F.weight p t + F.weight q t = 1)
    {r : ℕ} {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι)
    (x : Vec 2) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ j : Fin 2, chartInvJacobian ⇑((F.piece p).material t).symm x a₀ j •
        labelEdgeFlux F ν e E p (actual p) t (fun y => U ((F.piece p).material t y)) i
          (((F.piece p).material t).symm x) j :=
  edgeFlux_quiet_overlap_of_contDiff F ν e E actual K hdesc hpq
    (hTq p q hadj (actual p) (actual q) hctx) hw hsum hU hrD i x
    (hTcov p q hadj t ht (((F.piece q).material t).symm x)) a₀
end

/-! **The physical edge flux of a field and its linearity** (the edge term `∑_u 𝒮_{vu} û_u` of
the actual equation). `physEdgeFluxVec … t U v x` is the flux
`∑_{u, d} A_{vu}^d(t, x) ∇^{d-1} U_u(x)` of the actual equation applied to the classical jets of a
field `U`; it is linear in `U` over weighted sums whose terms of nonzero weight are `C^D`
(`physEdgeFluxVec_weighted_sum`), so the flux of the glued lift is the weighted sum of the fluxes
of the pulse lifts. -/

section
/-- The word derivative of the zero field vanishes. -/
theorem orderedDerivative_zero_fun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}
    (β : DerivativeWord2 j) (x : Vec 2) : orderedDerivative β (fun _ : Vec 2 => (0 : F)) x = 0 := by
  have h0 := congrFun (CoarseFluxDiff.orderedDerivative_const_smul β (0 : ℝ)
    (contDiff_const (c := (0 : F)))) x
  simpa using h0

/-- **Word derivatives of a weighted sum**, with smoothness required only for nonzero weights. -/
theorem orderedDerivative_weighted_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {κ : Type*} (S : Finset κ) (w : κ → ℝ) {j : ℕ} (β : DerivativeWord2 j) (g : κ → Vec 2 → F)
    (hg : ∀ k ∈ S, w k ≠ 0 → ContDiff ℝ (j : ℕ∞) (g k)) (x : Vec 2) :
    orderedDerivative β (fun y => ∑ k ∈ S, w k • g k y) x =
      ∑ k ∈ S, w k • orderedDerivative β (g k) x := by
  have hzero : ∀ k, w k = 0 → (fun y => w k • g k y) = fun _ => (0 : F) := fun k hw =>
    funext fun y => by simp [hw]
  have hcd : ∀ k ∈ S, ContDiff ℝ (j : ℕ∞) (fun y => w k • g k y) := fun k hk => by
    by_cases hw : w k = 0
    · rw [hzero k hw]
      exact contDiff_const
    · exact (hg k hk hw).const_smul (w k)
  rw [MixedTail.orderedDerivative_sum S β hcd]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : w k = 0
  · rw [hzero k hw, hw, zero_smul]
    exact orderedDerivative_zero_fun β x
  · rw [CoarseFluxDiff.orderedDerivative_const_smul β (w k) (hg k hk hw)]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The physical edge flux of the actual equation applied to the classical jets of `U`. -/
def physEdgeFluxVec (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (t : ℝ) (U : Vec 2 → ∀ i, h i) (v : ι) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ i' : ι, ∑ d : admissibleOrders K D v i', edgeCoefficient F ν e E actual K v i' d t x
    (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => U y i') x)

/-- A component of the physical edge flux. -/
theorem physEdgeFluxVec_apply (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (t : ℝ) (U : Vec 2 → ∀ i, h i) (v : ι) (x : Vec 2)
    (a : Fin 2) :
    physEdgeFluxVec F ν e E actual K t U v x a =
      ∑ i' : ι, ∑ d : admissibleOrders K D v i', edgeCoefficient F ν e E actual K v i' d t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word (fun y => U y i') x) a := by
  simp only [physEdgeFluxVec, WithLp.ofLp_sum, Finset.sum_apply]

/-- **The physical edge flux is linear over weighted sums of `C^D` fields.** -/
theorem physEdgeFluxVec_weighted_sum (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (t : ℝ) {κ : Type*} (S : Finset κ) (w : κ → ℝ)
    (T : κ → Vec 2 → ∀ i, h i) (hT : ∀ k ∈ S, w k ≠ 0 → ContDiff ℝ (D : ℕ∞) (T k)) (v : ι)
    (x : Vec 2) :
    physEdgeFluxVec F ν e E actual K t (fun y => ∑ k ∈ S, w k • T k y) v x =
      ∑ k ∈ S, w k • physEdgeFluxVec F ν e E actual K t (T k) v x := by
  have hjet : ∀ i' (d : admissibleOrders K D v i'),
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => (∑ k ∈ S, w k • T k y) i') x) =
      ∑ k ∈ S, w k • (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => T k y i') x) := fun i' d => by
    have hd : d.1 - 1 ≤ D := by
      have h1 := (Finset.mem_filter.1 d.2).1
      have h2 := Finset.mem_Icc.1 h1
      omega
    have hfun : (fun y => (∑ k ∈ S, w k • T k y) i') = fun y => ∑ k ∈ S, w k • T k y i' :=
      funext fun y => by simp only [Finset.sum_apply, Pi.smul_apply]
    have hw : ∀ word : DerivativeWord2 (d.1 - 1),
        orderedDerivative word (fun y => (∑ k ∈ S, w k • T k y) i') x =
          ∑ k ∈ S, w k • orderedDerivative word (fun y => T k y i') x := fun word => by
      rw [hfun]
      refine orderedDerivative_weighted_sum S w word (fun k y => T k y i') (fun k hk hwk => ?_) x
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := h) i').contDiff.comp (hT k hk hwk)).of_le
        (by exact_mod_cast hd)
    have hfun' : (fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => (∑ k ∈ S, w k • T k y) i') x) =
        ∑ k ∈ S, w k • (fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word (fun y => T k y i') x) := by
      funext word
      rw [hw word, Finset.sum_apply]
      rfl
    rw [hfun', WithLp.toLp_sum]
    rfl
  simp only [physEdgeFluxVec, hjet, map_sum, map_smul, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
end

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Slice norms of convex combinations**. At one time the glued residual fields are combinations
of the per-pulse fields with the lift-partition weights, which are nonnegative and sum to one. By
the convexity of the squared norm, the mass-weighted cell norms of the weighted word derivatives of
such a combination are at most the largest norm of the fields with nonzero weight
(`fluxInt_word_convex_le`, `scalInt_word_convex_le`): the glue costs no factor of the number of
pulses. -/

/-- **Convexity of the squared norm**: for nonnegative weights summing to one,
`‖∑ w_k y_k‖² ≤ ∑ w_k ‖y_k‖²`. -/
theorem enorm_convex_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}
    (S : Finset κ) (w : κ → ℝ) (hw0 : ∀ k ∈ S, 0 ≤ w k) (hw1 : ∑ k ∈ S, w k = 1) (y : κ → E) :
    ‖∑ k ∈ S, w k • y k‖ₑ ^ 2 ≤ ∑ k ∈ S, ENNReal.ofReal (w k) * ‖y k‖ₑ ^ 2 := by
  have h1 : ‖∑ k ∈ S, w k • y k‖ ≤ ∑ k ∈ S, w k * ‖y k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k hk => by
      rw [norm_smul, Real.norm_of_nonneg (hw0 k hk)]))
  have h2 : (∑ k ∈ S, w k * ‖y k‖) ^ 2 ≤ (∑ k ∈ S, w k) * ∑ k ∈ S, w k * ‖y k‖ ^ 2 := by
    have e1 : ∀ k ∈ S, Real.sqrt (w k) * (Real.sqrt (w k) * ‖y k‖) = w k * ‖y k‖ :=
      fun k hk => by rw [← mul_assoc, Real.mul_self_sqrt (hw0 k hk)]
    have e2 : ∀ k ∈ S, Real.sqrt (w k) ^ 2 = w k := fun k hk => Real.sq_sqrt (hw0 k hk)
    have e3 : ∀ k ∈ S, (Real.sqrt (w k) * ‖y k‖) ^ 2 = w k * ‖y k‖ ^ 2 :=
      fun k hk => by rw [mul_pow, Real.sq_sqrt (hw0 k hk)]
    have := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => Real.sqrt (w k))
      (fun k => Real.sqrt (w k) * ‖y k‖)
    rwa [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
  have hreal : ‖∑ k ∈ S, w k • y k‖ ^ 2 ≤ ∑ k ∈ S, w k * ‖y k‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (h2.trans_eq (by rw [hw1, one_mul]))
  rw [enorm_sq_eq_ofReal]
  calc ENNReal.ofReal (‖∑ k ∈ S, w k • y k‖ ^ 2)
      ≤ ENNReal.ofReal (∑ k ∈ S, w k * ‖y k‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ∑ k ∈ S, ENNReal.ofReal (w k) * ‖y k‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k hk => mul_nonneg (hw0 k hk) (sq_nonneg _)]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [ENNReal.ofReal_mul (hw0 k hk), enorm_sq_eq_ofReal]

/-- A weighted sum of bounded terms whose weights sum to one. -/
theorem sum_ofReal_mul_le_of_convex {κ : Type*} (S : Finset κ) (w : κ → ℝ)
    (hw0 : ∀ k ∈ S, 0 ≤ w k) (hw1 : ∑ k ∈ S, w k = 1) (X : κ → ℝ≥0∞) {Bd : ℝ≥0∞}
    (hb : ∀ k ∈ S, w k ≠ 0 → X k ≤ Bd) : ∑ k ∈ S, ENNReal.ofReal (w k) * X k ≤ Bd := by
  calc ∑ k ∈ S, ENNReal.ofReal (w k) * X k ≤ ∑ k ∈ S, ENNReal.ofReal (w k) * Bd := by
        refine Finset.sum_le_sum fun k hk => ?_
        by_cases hwk : w k = 0
        · rw [hwk, ENNReal.ofReal_zero, zero_mul, zero_mul]
        · exact mul_le_mul_right (hb k hk hwk) _
    _ = Bd := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hw0, hw1, ENNReal.ofReal_one,
          one_mul]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The flux slice norm of a convex combination** is at most the bound of the fluxes with
nonzero weight. -/
theorem fluxInt_convex_le {κ : Type*} (S : Finset κ) (w : κ → ℝ) (hw0 : ∀ k ∈ S, 0 ≤ w k)
    (hw1 : ∑ k ∈ S, w k = 1) (G : κ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ k ∈ S, ∀ l, Continuous (fun x => G k x l)) (π : ι → ℝ) {Bd : ℝ≥0∞}
    (hb : ∀ k ∈ S, w k ≠ 0 → fluxInt π (G k) ≤ Bd) :
    fluxInt π (fun x l => ∑ k ∈ S, w k • G k x l) ≤ Bd := by
  have hm : ∀ k ∈ S, ∀ v, Measurable (fun x => ∑ l : Fin 2, ‖G k x l v‖ₑ ^ 2) :=
    fun k hk v => Finset.measurable_sum _ fun l _ =>
      ((continuous_apply v).comp (hG k hk l)).enorm.measurable.pow_const 2
  have hpt : ∀ v x, ∑ l : Fin 2, ‖(∑ k ∈ S, w k • G k x l) v‖ₑ ^ 2 ≤
      ∑ k ∈ S, ENNReal.ofReal (w k) * ∑ l : Fin 2, ‖G k x l v‖ₑ ^ 2 := by
    intro v x
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun l _ => ?_
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact enorm_convex_sq_le S w hw0 hw1 fun k => G k x l v
  have hle : fluxInt π (fun x l => ∑ k ∈ S, w k • G k x l) ≤
      ∑ k ∈ S, ENNReal.ofReal (w k) * fluxInt π (G k) := by
    unfold fluxInt
    calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ∑ l : Fin 2, ‖(∑ k ∈ S, w k • G k x l) v‖ₑ ^ 2
        ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∑ k ∈ S, ENNReal.ofReal (w k) *
            ∫⁻ x in AVenhance.unitCube, ∑ l : Fin 2, ‖G k x l v‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun v _ => ?_
          gcongr
          refine (lintegral_mono fun x => hpt v x).trans_eq ?_
          rw [lintegral_finsetSum' _ fun k hk => ((hm k hk v).const_mul _).aemeasurable]
          exact Finset.sum_congr rfl fun k hk => lintegral_const_mul _ (hm k hk v)
      _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ => by ring
  exact hle.trans (sum_ofReal_mul_le_of_convex S w hw0 hw1 _ hb)

/-- **The scalar slice norm of a convex combination** is at most the bound of the scalars with
nonzero weight. -/
theorem scalInt_convex_le {κ : Type*} (S : Finset κ) (w : κ → ℝ) (hw0 : ∀ k ∈ S, 0 ≤ w k)
    (hw1 : ∑ k ∈ S, w k = 1) (q : κ → Vec 2 → ∀ i, h i) (hq : ∀ k ∈ S, Continuous (q k))
    (π : ι → ℝ) {Bd : ℝ≥0∞} (hb : ∀ k ∈ S, w k ≠ 0 → scalInt π (q k) ≤ Bd) :
    scalInt π (fun x => ∑ k ∈ S, w k • q k x) ≤ Bd := by
  have hm : ∀ k ∈ S, ∀ v, Measurable (fun x => ‖q k x v‖ₑ ^ 2) :=
    fun k hk v => ((continuous_apply v).comp (hq k hk)).enorm.measurable.pow_const 2
  have hpt : ∀ v x, ‖(∑ k ∈ S, w k • q k x) v‖ₑ ^ 2 ≤
      ∑ k ∈ S, ENNReal.ofReal (w k) * ‖q k x v‖ₑ ^ 2 := by
    intro v x
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact enorm_convex_sq_le S w hw0 hw1 fun k => q k x v
  have hle : scalInt π (fun x => ∑ k ∈ S, w k • q k x) ≤
      ∑ k ∈ S, ENNReal.ofReal (w k) * scalInt π (q k) := by
    unfold scalInt
    calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ‖(∑ k ∈ S, w k • q k x) v‖ₑ ^ 2
        ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∑ k ∈ S, ENNReal.ofReal (w k) *
            ∫⁻ x in AVenhance.unitCube, ‖q k x v‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun v _ => ?_
          gcongr
          refine (lintegral_mono fun x => hpt v x).trans_eq ?_
          rw [lintegral_finsetSum' _ fun k hk => ((hm k hk v).const_mul _).aemeasurable]
          exact Finset.sum_congr rfl fun k hk => lintegral_const_mul _ (hm k hk v)
      _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ => by ring
  exact hle.trans (sum_ofReal_mul_le_of_convex S w hw0 hw1 _ hb)

/-- **The weighted word derivatives of a convex combination of fluxes.** -/
theorem fluxInt_word_convex_le {κ : Type*} (S : Finset κ) (w : κ → ℝ) (hw0 : ∀ k ∈ S, 0 ≤ w k)
    (hw1 : ∑ k ∈ S, w k = 1) (X : κ → Vec 2 → Fin 2 → ∀ i, h i) {j : ℕ}
    (hX : ∀ k ∈ S, ∀ l, ContDiff ℝ (j : ℕ∞) (fun y => X k y l)) (rs : ℝ) (β : DerivativeWord2 j)
    (π : ι → ℝ) {Bd : ℝ≥0∞}
    (hb : ∀ k ∈ S, w k ≠ 0 →
      fluxInt π (fun x l => rs ^ j • orderedDerivative β (fun x' => X k x' l) x) ≤ Bd) :
    fluxInt π (fun x l => rs ^ j • orderedDerivative β (fun x' => ∑ k ∈ S, w k • X k x' l) x)
      ≤ Bd := by
  have e : (fun x l => rs ^ j • orderedDerivative β (fun x' => ∑ k ∈ S, w k • X k x' l) x) =
      fun x l => ∑ k ∈ S, w k • (rs ^ j • orderedDerivative β (fun x' => X k x' l) x) := by
    funext x l
    rw [MixedTail.orderedDerivative_sum S β fun k hk => (hX k hk l).const_smul (w k),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [CoarseFluxDiff.orderedDerivative_const_smul β (w k) (hX k hk l), smul_comm]
  rw [e]
  exact fluxInt_convex_le S w hw0 hw1 _
    (fun k hk l => (continuous_orderedDerivative β (hX k hk l)).const_smul (rs ^ j)) π hb

/-- **The weighted word derivatives of a convex combination of scalars.** -/
theorem scalInt_word_convex_le {κ : Type*} (S : Finset κ) (w : κ → ℝ) (hw0 : ∀ k ∈ S, 0 ≤ w k)
    (hw1 : ∑ k ∈ S, w k = 1) (q : κ → Vec 2 → ∀ i, h i) {j : ℕ}
    (hq : ∀ k ∈ S, ContDiff ℝ (j : ℕ∞) (q k)) (rs : ℝ) (β : DerivativeWord2 j) (π : ι → ℝ)
    {Bd : ℝ≥0∞}
    (hb : ∀ k ∈ S, w k ≠ 0 → scalInt π (fun x => rs ^ j • orderedDerivative β (q k) x) ≤ Bd) :
    scalInt π (fun x => rs ^ j • orderedDerivative β (fun x' => ∑ k ∈ S, w k • q k x') x)
      ≤ Bd := by
  have e : (fun x => rs ^ j • orderedDerivative β (fun x' => ∑ k ∈ S, w k • q k x') x) =
      fun x => ∑ k ∈ S, w k • (rs ^ j • orderedDerivative β (q k) x) := by
    funext x
    rw [MixedTail.orderedDerivative_sum S β fun k hk => (hq k hk).const_smul (w k),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [CoarseFluxDiff.orderedDerivative_const_smul β (w k) (hq k hk), smul_comm]
  rw [e]
  exact scalInt_convex_le S w hw0 hw1 _
    (fun k hk => (continuous_orderedDerivative β (hq k hk)).const_smul (rs ^ j)) π hb

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The sampled tail of the lift in cleanup form**.

Let `(f_n, F_n)` present the tail coefficients `R_n^{(hh)}` (`IsLiftTailPresentation`, the
conclusion of `cycle_lift_tail`) and let `A` be a coarse field, smooth at the cell time used.
* The tail is `ε^{N+1}` times the divided tail:
  `∑_{n=N+1}^{2N+D} εⁿ R_n^{(hh)} A = ε^{N+1} (f_A + div_z F_A)`, where `f_A = tailScalarField` and
  `F_A = tailFluxField` (`tail_sum_eq_divided`).
* The divided tail fields are box smooth, `ℤ²`-periodic and centered, so they have a cleanup
  chain (`exists_tail_cleanupChain`). This goes through `cycle_cleanup_chain_exists` on the
  Euclidean product `PiLp 2 h` (`exists_isCleanupChain_pi`), because the sup-normed product
  `∀ i, h i` is not an inner product space.
* Sample at `(c t, ρ⁻¹ y, e⁻¹ y)`. Then `c` times the tail is the divergence of
  `c ε^{N+1} cleanupFlux`, plus `c ε^{N+1} cleanupRemainder` (`tail_sample_eq_cleanup`).
  With `c = ℓ⁻²` and `A(s, X) = a(ℓ² s, ρX)`, this is exactly the pair `(R, q)` that
  `cycle_residual_bound` bounds.

The power base `ε` of the label lift equals the setting's `εc`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

section LiftAction

/-- Fast smoothness of a lift action at a fixed time and slow point. -/
theorem contDiff_liftApply_fast_pi (M q : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X : Vec 2) (hc : ∀ m α v u, ContDiff ℝ (q : ℕ∞) (fun z => c m α t X z v u)) :
    ContDiff ℝ (q : ℕ∞) (fun z => liftApply M c a t X z) := by
  refine contDiff_pi.2 fun v => ?_
  show ContDiff ℝ (q : ℕ∞) (fun z => ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m,
    ∑ u : ι, c m α t X z v u (orderedDerivative α (a t) X u))
  exact ContDiff.sum fun m _ => ContDiff.sum fun α _ => ContDiff.sum fun u _ =>
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a t) X u)).contDiff.comp
      (hc m α v u)

/-- `ℤ²`-periodicity in the fast variable of a lift action with periodic coefficients. -/
theorem liftApply_isZ2Periodic (M : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (X : Vec 2) (hc : ∀ m α v u, AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) :
    AVenhance.IsZ2Periodic (fun z => liftApply M c a t X z) := by
  intro l z
  funext v
  show ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
      c m α t X (z + AVenhance.latticeShift l) v u (orderedDerivative α (a t) X u) =
    ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
      c m α t X z v u (orderedDerivative α (a t) X u)
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have e : c m α t X (z + AVenhance.latticeShift l) v u = c m α t X z v u := hc m α v u l z
  rw [e]

end LiftAction

section Euclidean

/-- **Cleanup chains for data in a finite product of finite-dimensional inner product spaces.**
`cycle_cleanup_chain_exists` needs an inner product on the values. The sup-normed product
`∀ i, h i` has none, so transport the data to `PiLp 2 h` and the chain back. -/
theorem exists_isCleanupChain_pi [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    (sX sZ A : ℕ) (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    (f₀ : Vec 2 → Vec 2 → ∀ i, h i) (F₀ : Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) :
    ∃ V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i, IsCleanupChain sX sZ A f₀ F₀ V := by
  let Φ := PiLp.continuousLinearEquiv 2 ℝ h
  let P := Φ.symm.toContinuousLinearMap
  let R := Φ.toContinuousLinearMap
  have hRP : ∀ w : ∀ i, h i, R (P w) = w := fun w => Φ.apply_symm_apply w
  have hg : IsBoxSmooth (sX + A) (sZ + 1) (fun X z => P (f₀ X z)) := hf.map_clm P
  have hG : IsBoxSmooth (sX + A) (sZ + 1) (fun X z k => P (F₀ X z k)) := hF.map_clm (clmVec P)
  have hgp : ∀ X, AVenhance.IsZ2Periodic (fun z => P (f₀ X z)) := fun X n z => by
    show P (f₀ X (z + AVenhance.latticeShift n)) = P (f₀ X z)
    rw [hfp X n z]
  have hGp : ∀ X, AVenhance.IsZ2Periodic (fun z k => P (F₀ X z k)) := fun X n z => by
    funext k
    show P (F₀ X (z + AVenhance.latticeShift n) k) = P (F₀ X z k)
    rw [hFp X n z]
  have hgm : ∀ X, fieldCellMean (fun z => P (f₀ X z)) = 0 := fun X => by
    rw [fieldCellMean_clm P (hf.1 X).continuous, hfm X, map_zero]
  have hGm : ∀ X (k : Fin 2), fieldCellMean (fun z => P (F₀ X z k)) = 0 := fun X k => by
    have hc : Continuous fun z => F₀ X z k := (continuous_apply k).comp (hF.1 X).continuous
    rw [fieldCellMean_clm P hc, hFm X k, map_zero]
  obtain ⟨W, hW⟩ := AVRegularity.Providers.cycle_cleanup_chain_exists (E := PiLp 2 h) sX sZ A
    hsZ _ _ hg hgp hgm hG hGp hGm
  have hWR : IsCleanupChain sX sZ A (fun X z => R (P (f₀ X z)))
      (fun X z k => R (P (F₀ X z k))) (fun j X z k => R (W j X z k)) :=
    IsCleanupChain.clm_comp hsX hsZ (hG.mono (Nat.le_add_right sX A) le_rfl).isSlowSmooth hW R
  have e1 : (fun X z => R (P (f₀ X z))) = f₀ := by
    funext X z
    exact hRP _
  have e2 : (fun X z k => R (P (F₀ X z k))) = F₀ := by
    funext X z k
    exact hRP _
  rw [e1, e2] at hWR
  exact ⟨_, hWR⟩

end Euclidean

section Presentation

variable {D : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {π : ι → ℝ}
  {t₀ t₁ : ℝ} {N K : ℕ} {CL Θ : ℝ} {hh sX sZ : ℕ}
  {f : ℕ → LiftCoeff ι h} {F : ℕ → Fin 2 → LiftCoeff ι h}

/-- The divided tail scalar field of a presentation is box smooth on the window. -/
theorem isBoxSmooth_tailScalarField_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A τ)) :
    IsBoxSmooth sX sZ (tailScalarField f N D ε A τ) := by
  refine AVRegularity.TailDiff.isBoxSmooth_pi (H := h) fun v => ?_
  have e : (fun X z => tailScalarField f N D ε A τ X z v) = fun X z =>
      ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
        ε ^ (n - N - 1) • liftApply (2 * N + D) (f n) A τ X z v := by
    funext X z
    simp only [tailScalarField, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine IsBoxSmooth.sum _ fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  obtain ⟨-, -, -, -, -, hfb, -⟩ := hpres n hn1 hn2
  exact (AVRegularity.QuietDecay.Partition.isBoxSmooth_liftApply (2 * N + D) sX sZ (f n) A τ
    (fun m α v' u => (hfb m α v' u τ hτ).1) (hA.of_le (by exact_mod_cast le_top)) v).const_smul _

/-- The divided tail flux field of a presentation is box smooth on the window. -/
theorem isBoxSmooth_tailFluxField_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A τ)) :
    IsBoxSmooth sX sZ (tailFluxField F N D ε A τ) := by
  refine AVRegularity.TailDiff.isBoxSmooth_pi (H := fun _ : Fin 2 => ∀ i, h i) fun k =>
    AVRegularity.TailDiff.isBoxSmooth_pi (H := h) fun v => ?_
  have e : (fun X z => tailFluxField F N D ε A τ X z k v) = fun X z =>
      ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
        ε ^ (n - N - 1) • liftApply (2 * N + D) (F n k) A τ X z v := by
    funext X z
    simp only [tailFluxField, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine IsBoxSmooth.sum _ fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  obtain ⟨-, -, -, -, -, -, hFb, -⟩ := hpres n hn1 hn2
  exact (AVRegularity.QuietDecay.Partition.isBoxSmooth_liftApply (2 * N + D) sX sZ (F n k) A τ
    (fun m α v' u => (hFb k m α v' u τ hτ).1) (hA.of_le (by exact_mod_cast le_top)) v).const_smul _

/-- The divided tail scalar field of a presentation is `ℤ²`-periodic in the fast variable. -/
theorem tailScalarField_isZ2Periodic_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁) (X : Vec 2) :
    AVenhance.IsZ2Periodic (tailScalarField f N D ε A τ X) := by
  intro l z
  show ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (f n) A τ X (z + AVenhance.latticeShift l) =
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (f n) A τ X z
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  obtain ⟨-, -, -, -, -, hfb, -⟩ := hpres n hn1 hn2
  have hp := liftApply_isZ2Periodic (2 * N + D) (f n) A τ X
    (fun m α v u => (hfb m α v u τ hτ).2 X) l z
  exact congrArg (fun w => ε ^ (n - N - 1) • w) hp

/-- The divided tail flux field of a presentation is `ℤ²`-periodic in the fast variable. -/
theorem tailFluxField_isZ2Periodic_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁) (X : Vec 2) :
    AVenhance.IsZ2Periodic (tailFluxField F N D ε A τ X) := by
  intro l z
  funext k
  show ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (F n k) A τ X (z + AVenhance.latticeShift l) =
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
      liftApply (2 * N + D) (F n k) A τ X z
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  obtain ⟨-, -, -, -, -, -, hFb, -⟩ := hpres n hn1 hn2
  have hp := liftApply_isZ2Periodic (2 * N + D) (F n k) A τ X
    (fun m α v u => (hFb k m α v u τ hτ).2 X) l z
  exact congrArg (fun w => ε ^ (n - N - 1) • w) hp

/-- The divided tail scalar field of a presentation is centered. -/
theorem fieldCellMean_tailScalarField_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A τ)) (X : Vec 2) :
    fieldCellMean (tailScalarField f N D ε A τ X) = 0 := by
  show fieldCellMean (fun z => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
    ε ^ (n - N - 1) • liftApply (2 * N + D) (f n) A τ X z) = 0
  refine AVRegularity.CycleComparison.Lift.fieldCellMean_finset_sum_smul_zero
    (Finset.Icc (N + 1) (2 * N + D)) (fun n => ε ^ (n - N - 1))
    (fun n z => liftApply (2 * N + D) (f n) A τ X z) (fun n hn => ?_) (fun n hn => ?_)
  · obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, hfb, -⟩ := hpres n hn1 hn2
    exact (contDiff_liftApply_fast_pi (2 * N + D) sZ (f n) A τ X
      fun m α v u => (hfb m α v u τ hτ).1.1 X).continuous
  · obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, -, -, -, hmean, -⟩ := hpres n hn1 hn2
    exact (hmean (A τ) hA τ hτ X).1

/-- The divided tail flux field of a presentation is centered. -/
theorem fieldCellMean_tailFluxField_of_presentation
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ Set.Icc t₀ t₁)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A τ)) (X : Vec 2) (k : Fin 2) :
    fieldCellMean (fun z => tailFluxField F N D ε A τ X z k) = 0 := by
  show fieldCellMean (fun z => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
    ε ^ (n - N - 1) • liftApply (2 * N + D) (F n k) A τ X z) = 0
  refine AVRegularity.CycleComparison.Lift.fieldCellMean_finset_sum_smul_zero
    (Finset.Icc (N + 1) (2 * N + D)) (fun n => ε ^ (n - N - 1))
    (fun n z => liftApply (2 * N + D) (F n k) A τ X z) (fun n hn => ?_) (fun n hn => ?_)
  · obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, -, hFb, -⟩ := hpres n hn1 hn2
    exact (contDiff_liftApply_fast_pi (2 * N + D) sZ (F n k) A τ X
      fun m α v u => (hFb k m α v u τ hτ).1.1 X).continuous
  · obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, -, -, -, hmean, -⟩ := hpres n hn1 hn2
    exact (hmean (A τ) hA τ hτ X).2 k

/-- **The cleanup chain of the divided tail exists** on the window. It needs the presentation
box smooth through `(sXc + Acl, sZc + 1)`, which is one slow order per link and one fast order
above the chain orders `(sXc, sZc)`. -/
theorem exists_tail_cleanupChain [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    (sXc sZc Acl : ℕ) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (hX : sXc + Acl ≤ sX)
    (hZ : sZc + 1 ≤ sZ)
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i)
    (hA : ∀ τ ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (A τ)) :
    ∃ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i, ∀ τ ∈ Set.Icc t₀ t₁,
      IsCleanupChain sXc sZc Acl (tailScalarField f N D ε A τ) (tailFluxField F N D ε A τ)
        (fun j => Vc j τ) := by
  have hex : ∀ τ, ∃ V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i, τ ∈ Set.Icc t₀ t₁ →
      IsCleanupChain sXc sZc Acl (tailScalarField f N D ε A τ) (tailFluxField F N D ε A τ)
        V := by
    intro τ
    by_cases hτ : τ ∈ Set.Icc t₀ t₁
    · obtain ⟨V, hV⟩ := exists_isCleanupChain_pi sXc sZc Acl hXc hZc _ _
        ((isBoxSmooth_tailScalarField_of_presentation hpres ε A hτ (hA τ hτ)).mono hX hZ)
        (tailScalarField_isZ2Periodic_of_presentation hpres ε A hτ)
        (fieldCellMean_tailScalarField_of_presentation hpres ε A hτ (hA τ hτ))
        ((isBoxSmooth_tailFluxField_of_presentation hpres ε A hτ (hA τ hτ)).mono hX hZ)
        (tailFluxField_isZ2Periodic_of_presentation hpres ε A hτ)
        (fieldCellMean_tailFluxField_of_presentation hpres ε A hτ (hA τ hτ))
      exact ⟨V, fun _ => hV⟩
    · exact ⟨fun _ _ _ _ => 0, fun h' => absurd h' hτ⟩
  choose V hV using hex
  exact ⟨fun j τ => V τ j, fun τ hτ => hV τ hτ⟩

/-- **The tail of the lift is `ε^{N+1}` times the divided tail.** At a cell time `s` of the
window, if the coarse field `A s` is smooth, then
`∑_{n=N+1}^{2N+D} εⁿ R_n^{(hh)} A = ε^{N+1} (f_A + div_z F_A)` at every `(X, z)`, with
`f_A = tailScalarField f N D ε A` and `F_A = tailFluxField F N D ε A`. -/
theorem tail_sum_eq_divided (hsZ : 1 ≤ sZ)
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A s)) (X z : Vec 2) :
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n • liftTailCoeff Q Cc N (fun _ => A s) hh n s X z
      = ε ^ (N + 1) • (tailScalarField f N D ε A s X z
          + ∑ k : Fin 2, fastPartial k (fun X' z' => tailFluxField F N D ε A s X' z' k) X z) := by
  have hq : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sZ ≠ 0)
  -- the fast differentiability of the flux actions
  have hdiff0 : ∀ k : Fin 2, ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      DifferentiableAt ℝ (fun z' => liftApply (2 * N + D) (F n k) A s X z') z := by
    intro k n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, -, hFb, -⟩ := hpres n hn1 hn2
    exact (contDiff_liftApply_fast_pi (2 * N + D) sZ (F n k) A s X
      fun m α v u => (hFb k m α v u s hs).1.1 X).differentiable hq z
  -- each power: the presentation identity, with `εⁿ = ε^{N+1} ε^{n-N-1}`
  have hterm : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D),
      ε ^ n • liftTailCoeff Q Cc N (fun _ => A s) hh n s X z =
        ε ^ (N + 1) • (ε ^ (n - N - 1) • (liftApply (2 * N + D) (f n) A s X z +
          ∑ k : Fin 2, fastPartial k
            (fun X' z' => liftApply (2 * N + D) (F n k) A s X' z') X z)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    obtain ⟨-, -, -, -, -, -, -, hid, -⟩ := hpres n hn1 hn2
    have hid' : liftTailCoeff Q Cc N (fun _ => A s) hh n s X z =
        liftApply (2 * N + D) (f n) A s X z + ∑ k : Fin 2, fastPartial k
          (fun X' z' => liftApply (2 * N + D) (F n k) A s X' z') X z :=
      hid (A s) hA s hs X z
    rw [hid', smul_smul, ← pow_add, show N + 1 + (n - N - 1) = n by omega]
  -- the scalar part
  have hS : ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
      ε ^ (n - N - 1) • liftApply (2 * N + D) (f n) A s X z = tailScalarField f N D ε A s X z :=
    rfl
  -- the flux part: the fast divergence commutes with the finite sum over the powers
  have hP : ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ∑ k : Fin 2, ε ^ (n - N - 1) •
      fastPartial k (fun X' z' => liftApply (2 * N + D) (F n k) A s X' z') X z =
      ∑ k : Fin 2, fastPartial k (fun X' z' => tailFluxField F N D ε A s X' z' k) X z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdk : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), DifferentiableAt ℝ
        (fun z' => ε ^ (n - N - 1) • liftApply (2 * N + D) (F n k) A s X z') z :=
      fun n hn => (hdiff0 k n hn).const_smul (ε ^ (n - N - 1))
    show _ = fderiv ℝ (fun z' => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
      ε ^ (n - N - 1) • liftApply (2 * N + D) (F n k) A s X z') z (basisVec k)
    rw [fderiv_fun_sum hdk]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [fderiv_fun_const_smul (hdiff0 k n hn)]
    rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← hS, ← hP, ← Finset.sum_add_distrib]
  refine congrArg (fun w => ε ^ (N + 1) • w) (Finset.sum_congr rfl fun n _ => ?_)
  rw [smul_add, Finset.smul_sum]

/-- **The sampled tail of the lift in cleanup form.** Let the cell time `c t` lie in the
window, let the coarse field `A (c t)` be smooth, and let `Vc` be a cleanup chain of the
divided tail on the window, of orders `(sXc, sZc)` below those of the presentation. At the label
`y`, `c` times the tail sampled at `(c t, ρ⁻¹ y, e⁻¹ y)` is the divergence of
`c ε^{N+1} cleanupFlux` plus `c ε^{N+1} cleanupRemainder`. -/
theorem tail_sample_eq_cleanup (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc)
    (hZc : 1 ≤ sZc) (hX : sXc ≤ sX) (hZ : sZc ≤ sZ)
    (hpres : ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
      IsLiftTailPresentation Q Cc sX sZ π t₀ t₁ N K CL Θ hh n (f n) (F n))
    (ε c : ℝ) {ρ e : ℝ} (hρ : ρ ≠ 0) (he : e ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ τ ∈ Set.Icc t₀ t₁, IsCleanupChain sXc sZc Acl (tailScalarField f N D ε A τ)
      (tailFluxField F N D ε A τ) (fun j => Vc j τ))
    {t : ℝ} (ht : c * t ∈ Set.Icc t₀ t₁) (hAs : ContDiff ℝ (⊤ : ℕ∞) (A (c * t))) (y : Vec 2) :
    c • ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
        liftTailCoeff Q Cc N (fun _ => A (c * t)) hh n (c * t) (ρ⁻¹ • y) (e⁻¹ • y)
      = ∑ k : Fin 2, fderiv ℝ (fun y' => c • ε ^ (N + 1) • cleanupFlux c ρ e Acl Vc t y' k) y
            (basisVec k)
        + c • ε ^ (N + 1) • cleanupRemainder c ρ e Acl Vc t y := by
  have hsZ : 1 ≤ sZ := hZc.trans hZ
  have hbox : IsBoxSmooth sXc sZc (tailFluxField F N D ε A (c * t)) :=
    (isBoxSmooth_tailFluxField_of_presentation hpres ε A ht hAs).mono hX hZ
  -- the cleanup identity at the cell time `c t`
  have hcl : tailScalarField f N D ε A (c * t) (ρ⁻¹ • y) (e⁻¹ • y)
      + ∑ k : Fin 2, fastPartial k (fun X' z' => tailFluxField F N D ε A (c * t) X' z' k)
          (ρ⁻¹ • y) (e⁻¹ • y)
      = ∑ k : Fin 2, fderiv ℝ (fun y' => cleanupFlux c ρ e Acl Vc t y' k) y (basisVec k)
        + cleanupRemainder c ρ e Acl Vc t y :=
    cleanup_identity hAcl hXc hZc hρ he hbox (hV _ ht) y
  have hd : ∀ k : Fin 2, DifferentiableAt ℝ (fun y' => cleanupFlux c ρ e Acl Vc t y' k) y :=
    fun k => differentiableAt_cleanupFlux hXc hZc c ρ e t
      (IsCleanupChain.isBoxSmooth hbox (hV _ ht)) y k
  rw [tail_sum_eq_divided hsZ hpres ε A ht hAs (ρ⁻¹ • y) (e⁻¹ • y), hcl, smul_add, smul_add,
    Finset.smul_sum, Finset.smul_sum, add_left_inj]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd' : DifferentiableAt ℝ (fun y' => ε ^ (N + 1) • cleanupFlux c ρ e Acl Vc t y' k) y :=
    (hd k).const_smul (ε ^ (N + 1))
  rw [fderiv_fun_const_smul hd' c, fderiv_fun_const_smul (hd k) (ε ^ (N + 1))]
  rfl

end Presentation

end AVRegularity.CycleComparison.Reconstruction
end
end
