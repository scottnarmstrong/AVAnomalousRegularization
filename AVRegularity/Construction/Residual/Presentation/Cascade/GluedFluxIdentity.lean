-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFloors
public import AVRegularity.KernelEnergy.TorusTimeFlux
import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.CycleComparison.Coarse.Bound.AtTime
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovCommTime
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
public import AVRegularity.CycleComparison.Lift.SettingLiftALeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Jets
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.KernelEnergy
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The kernel inputs `yom` of the order-`k` retained data at every time**.

`retainedEdgeInputs`: for a stage `G'` with the retained stage `R` (a stage whose components are among those
of `G'`), the regularizer lift of a carrier `W` of order `k + 1` on the components of `R`, to the
order `k + D_m - 1`, on the edges of `G'`: the clamped regularized input of the stage's kernel on
the window `[t_p, t_f]` at the retained targets, and `0` at the others.
`Yom_value`: at every time of the window the value of the lift is the kernel `S_{vuγ}(t)`
applied to the value of `W`. This is the kernel compatibility asked by
`frontierInner_bound` (`hv`), and it holds at every time because the lift does not go
through the solution predicate.

By linearity `W = 0` gives `yom = 0`, and a non-retained target gives `0`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The regularizer clause of the kernels of `G'` at the retained targets `R`, on `[tp, tf]`. -/
def RegClause (G' R : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (tp tf : ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ v u (γ : G'.fam.Γ v u), u.1 ∈ R.comps →
    IsSpatialRegularizerTorus 1 k Dm tp tf c (G'.kernelOf P seedK freshK v u γ).width
      (G'.sysS P seedK freshK φ₀ hφ₀ v u γ)

/-- The kernel inputs of the retained carrier `W`: the regularizer lift at retained targets. -/
def retainedEdgeInputs (G' R : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hS : RegClause G' R P seedK freshK φ₀ hφ₀ k tp tf c)
    (W : ∀ u : CompIn R.comps, ℝ → TorusHk (k + 1) (hr u.1.root)) :
    ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
  fun v u γ t =>
    if hu : u.1 ∈ R.comps then
      clampedRegularizedInputCLM 1 k Dm hD tp tf c (G'.kernelOf P seedK freshK v u γ).width
        (ContinuousLinearMap.id ℝ (hr u.1.root)) (G'.sysS P seedK freshK φ₀ hφ₀ v u γ)
        (hS v u γ hu) one_pos htf t (W ⟨u.1, hu⟩ t)
    else 0

/-- **The kernel compatibility at every time of the window.** -/
theorem Yom_value (G' R : GenStage D hr Dm b j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (k : ℕ)
    (hD : 2 ≤ Dm) (tp tf : ℝ) (htf : tp ≤ tf) (c : ℕ → ℝ)
    (hS : RegClause G' R P seedK freshK φ₀ hφ₀ k tp tf c)
    (W : ∀ u : CompIn R.comps, ℝ → TorusHk (k + 1) (hr u.1.root))
    (t : ℝ) (ht : t ∈ Set.Icc tp tf) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u)
    (hu : u.1 ∈ R.comps) :
    (retainedEdgeInputs G' R P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS W v u γ t).val
        (valueIndex2 (k + Dm - 1)) =
      (G'.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t
        ((W ⟨u.1, hu⟩ t).val (valueIndex2 (k + 1))) := by
  unfold retainedEdgeInputs
  simp only [hu, ↓reduceDIte]
  change (torusRegularizedInput 1 k Dm hD tp tf c (G'.kernelOf P seedK freshK v u γ).width
    (ContinuousLinearMap.id ℝ (hr u.1.root)) (G'.sysS P seedK freshK φ₀ hφ₀ v u γ) (hS v u γ hu)
    (Set.projIcc tp tf htf t) (Set.projIcc tp tf htf t).property (W ⟨u.1, hu⟩ t)).val _ = _
  rw [torusRegularizedInput_value, Set.projIcc_of_mem htf ht]
  simp only [Providers.WeakGen.Comparison.id_compLp_eq]
  rfl

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The retained data at the order `k = k_c + 2p` for the frontier bound at
every time of the window.**

`retainedData`: from the bill's regular solution of the retained system at the order `N_aux`
with its retained trace and the classical representative `aY` of `Y` at every time of the window,
and `k + 1 ≤ N_aux`, there are retained data `Y₀, Y, Y_w, Y_k` of order `k` and kernel inputs
`yom` with

1. `R.IsRegSolution … k t_p t_f Y₀ 0 0 Y Y_w Y_k`, `IsRetainedTrace G R m p t_p h Y₀` (the premises
   of the frontier proof `FrontierAnalyticProductionDataStatement`);
2. `‖Y₀‖ ≤ B` as soon as the bill's `‖Y₀‖ ≤ B` (same weights);
3. `IsClassicalRep (Y_w u t) (aY t ·) (k+1)` at EVERY `t ∈ [t_p, t_f]` (`hYcl` of
   `frontierInner_bound`);
4. the kernel compatibility of `yom` at EVERY `t ∈ [t_p, t_f]` (`hv` of
   `frontierInner_bound`), hence also the a.e. one asked by the proof (`G'.sysS` is
   `(G'.kernelOf …).op …` by definition).

`Y_w := truncate Y` is defined from `Y` (classical at every time); the solution predicate holds for
it by `kernel_solution_truncate_torus` and the stability lemma `kernelWeakSolution_congr_w`
(the bill's gradient carrier agrees with `truncate Y` for almost every time).

For `t_f < t_p` the window is empty and `yom = 0`, and for `Y = 0` every retained quantity
vanishes. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}


omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- Truncation does not increase the weighted norm (any weights with `π ≥ 0`). -/
theorem weightedNorm_truncate_le' {S : Finset Comp} {K L : ℕ} (hKL : K ≤ L) (ρ : ℝ)
    (π w : CompIn S → ℝ) (hπ : ∀ v, 0 ≤ π v) (f : ∀ v : CompIn S, TorusHk L (hr v.1.root)) :
    weightedNorm ρ π w (fun v => truncateTorusHk hKL (f v)) ≤ weightedNorm ρ π w f := by
  unfold weightedNorm massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    (AVRegularity.CycleComparison.Error.factorialNormSq_truncateTorusHk_le hKL ρ (f v)) ?_)
  exact inv_nonneg.2 (div_nonneg (hπ v) (sq_nonneg _))

/-- The truncation of a regular solution is a regular solution of the lower order. -/
theorem regSolution_truncate {R : GenStage D hr Dm b j₀} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {tp tf : ℝ} {Naux k : ℕ} (hkN : k ≤ Naux)
    {Y0b : ∀ v : CompIn R.comps, TorusHk Naux (hr v.1.root)}
    {Yb : ∀ v : CompIn R.comps, ℝ → TorusHk Naux (hr v.1.root)}
    {Ywb : ∀ v : CompIn R.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)}
    {Ykb : ∀ v u (_ : R.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root)}
    (hsol : R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv Naux tp tf Y0b (fun _ _ => 0)
      (fun _ _ => 0) Yb Ywb Ykb) :
    R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k tp tf (fun v => truncateTorusHk hkN (Y0b v))
      (fun _ _ => 0) (fun _ _ => 0) (fun v t => truncateTorusHk hkN (Yb v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ hkN) (Ywb v t))
      (fun v u γ t => truncateTorusHk (by omega) (Ykb v u γ t)) := by
  unfold GenStage.IsRegSolution at hsol ⊢
  have h1 := Providers.kernel_solution_truncate_torus tp tf ν bv k Naux Dm hkN _ _ _ _ _ _ _ _ _
    hsol
  simpa only [map_zero] using h1

/-- A regular solution stays one when its gradient carrier is changed on a null set of times. -/
theorem regSolution_congr_w {R : GenStage D hr Dm b j₀} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {tp tf : ℝ} {k : ℕ}
    {Y0 : ∀ v : CompIn R.comps, TorusHk k (hr v.1.root)}
    {Y : ∀ v : CompIn R.comps, ℝ → TorusHk k (hr v.1.root)}
    {Yw : ∀ v : CompIn R.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Yk : ∀ v u (_ : R.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (hsol : R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k tp tf Y0 (fun _ _ => 0)
      (fun _ _ => 0) Y Yw Yk)
    (Yw' : ∀ v : CompIn R.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (hww : ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)), Yw' i s = Yw i s)
    (hvc : ∀ s ∈ Set.Icc tp tf, Continuous (bv s))
    (hvb : ∀ s ∈ Set.Icc tp tf, ∃ M, ∀ x, ‖bv s x‖ ≤ M) :
    R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k tp tf Y0 (fun _ _ => 0)
      (fun _ _ => 0) Y Yw' Yk := by
  unfold GenStage.IsRegSolution at hsol ⊢
  exact kernelWeakSolution_congr_w hsol Yw' hww hvc hvb

/-- The drift facts asked by `retainedData` for the velocity `streamVel (Φ m)` of a stream
sequence: continuous and bounded in space at every time. -/
theorem streamVel_facts (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t : ℝ) :
    Continuous (streamVel (Φ m) t) ∧ ∃ M, ∀ x, ‖streamVel (Φ m) t x‖ ≤ M :=
  ⟨(Applications.streamVel_slice_smooth α q ζ hζ Λ hΛ Φ hΦ m t).continuous,
    ⟨_, Applications.streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t⟩⟩

/-- **The retained data of order `k` at every time** (see the module docstring). -/
theorem retainedData {G G' R : GenStage D hr Dm b j₀} (law : BirthLaw)
    (hπ : ∀ v, 0 < R.mass law v) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (ν : ℝ) (bv : ℝ → Vec 2 → Vec 2) (m p : ℕ)
    (tp tf : ℝ) {Nh : ℕ} (h : ∀ v : CompIn G.comps, TorusHk Nh (hr v.1.root)) (Naux k : ℕ)
    (hk : k + 1 ≤ Naux)
    (Y0b : ∀ v : CompIn R.comps, TorusHk Naux (hr v.1.root))
    (Yb : ∀ v : CompIn R.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Ywb : ∀ v : CompIn R.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (Ykb : ∀ v u (_ : R.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root))
    (hsol : R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv Naux tp tf Y0b (fun _ _ => 0)
      (fun _ _ => 0) Yb Ywb Ykb)
    (htr : IsRetainedTrace G R m p tp h Y0b)
    (aY : ℝ → Vec 2 → ∀ v : CompIn R.comps, hr v.1.root)
    (hret : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Yb v t) (fun x => aY t x v) Naux)
    (hvc : ∀ s ∈ Set.Icc tp tf, Continuous (bv s))
    (hvb : ∀ s ∈ Set.Icc tp tf, ∃ M, ∀ x, ‖bv s x‖ ≤ M)
    (hD : 2 ≤ Dm) (c : ℕ → ℝ) (hS : RegClause G' R P seedK freshK φ₀ hφ₀ k tp tf c)
    (ρ B : ℝ) (hY0b : weightedNorm ρ (R.mass law) (R.marker law) Y0b ≤ B) :
    ∃ (Y0k : ∀ v : CompIn R.comps, TorusHk k (hr v.1.root))
      (Yk : ∀ v : CompIn R.comps, ℝ → TorusHk k (hr v.1.root))
      (Ywk : ∀ v : CompIn R.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Ykk : ∀ v u (_ : R.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
      (yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
      R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k tp tf Y0k (fun _ _ => 0) (fun _ _ => 0)
        Yk Ywk Ykk ∧
      IsRetainedTrace G R m p tp h Y0k ∧
      weightedNorm ρ (R.mass law) (R.marker law) Y0k ≤ B ∧
      (∀ u, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Ywk u t) (fun x => aY t x u) (k + 1)) ∧
      (∀ t ∈ Set.Icc tp tf, ∀ (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (hu : u.1 ∈ R.comps),
        (yom v u γ t).val (valueIndex2 (k + Dm - 1)) =
          (G'.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t
            ((Ywk ⟨u.1, hu⟩ t).val (valueIndex2 (k + 1)))) := by
  classical
  have hkN : k ≤ Naux := by omega
  have hk1 : k + 1 ≤ Naux := hk
  have hDk : k + Dm - 1 ≤ Naux + Dm - 1 := by omega
  let Y0k : ∀ v : CompIn R.comps, TorusHk k (hr v.1.root) :=
    fun v => truncateTorusHk hkN (Y0b v)
  let Yk : ∀ v : CompIn R.comps, ℝ → TorusHk k (hr v.1.root) :=
    fun v t => truncateTorusHk hkN (Yb v t)
  let Ywk : ∀ v : CompIn R.comps, ℝ → TorusHk (k + 1) (hr v.1.root) :=
    fun v t => truncateTorusHk hk1 (Yb v t)
  let Ykk : ∀ v u (_ : R.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
    fun v u γ t => truncateTorusHk hDk (Ykb v u γ t)
  have hsol' : R.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k tp tf Y0k (fun _ _ => 0)
      (fun _ _ => 0) Yk Ywk Ykk := by
    refine regSolution_congr_w (regSolution_truncate hkN hsol) Ywk ?_ hvc hvb
    intro i
    filter_upwards [hsol.2.2.1 i] with s hs
    change truncateTorusHk hk1 (Yb i s) = truncateTorusHk (Nat.succ_le_succ hkN) (Ywb i s)
    rw [← hs]
    rfl
  have hcl : ∀ u, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Ywk u t) (fun x => aY t x u) (k + 1) :=
    fun u t ht => classicalRep_truncate hk1 le_rfl _ _
      (classicalRep_order_mono _ _ (hret u t ht) hk1)
  have htr' : IsRetainedTrace G R m p tp h Y0k := by
    refine ⟨fun v' hv => covImage_truncate hkN _ _ _ (htr.1 v' hv), fun v' hv' => ?_⟩
    change truncateTorusHk hkN (Y0b v') = 0
    rw [htr.2 v' hv', map_zero]
  have hnorm : weightedNorm ρ (R.mass law) (R.marker law) Y0k ≤ B :=
    (weightedNorm_truncate_le' hkN ρ _ _ (fun v => (hπ v).le) Y0b).trans hY0b
  by_cases htf : tp ≤ tf
  · refine ⟨Y0k, Yk, Ywk, Ykk, retainedEdgeInputs G' R P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS Ywk,
      hsol', htr', hnorm, hcl, ?_⟩
    intro t ht v u γ hu
    exact Yom_value G' R P seedK freshK φ₀ hφ₀ k hD tp tf htf c hS Ywk t ht v u γ hu
  · exact ⟨Y0k, Yk, Ywk, Ykk, fun _ _ _ _ => 0, hsol', htr', hnorm, hcl,
      fun t ht => absurd (ht.1.trans ht.2) htf⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Error
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.CovOp
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The covariance-filter estimate** (cascade side of the bill residual, an input
of the initial error).

For a matrix `𝖧`, the covariance polynomials `𝖯_p = ∑_{l ≤ p} 𝒞^l/l!` and
`𝖰_p = ∑_{l ≤ p} (−𝒞)^l/l!` of `𝒞 = 𝖧:∇²` satisfy `𝖰_p𝖯_p − I = ∑_{p+1 ≤ a+b} ± 𝒞^{a+b}/(a! b!)`
(`sub_covPolyQ_covPolyP_eq`, the remainder `qpRem`). For a periodic Sobolev field `h` of order
`N_h ≥ 4p` with its covariance images `Q h = 𝖰_p h` and `P Z = 𝖯_p(Q h)` (by duality,
`IsCovImage`):

* `filter_eq`: `trunc(P Z) − trunc(h)` is the image of `h` under the formal adjoint of
  `qpRem` (`TorusAdj.qpRem`, negated), as an element of `H⁰`;
* `filter_component`: if `|𝖧| ≤ ω ρ²` (in the norm `covBound` of the covariance size form)
  and `0 ≤ ω ≤ 1`, then
  `‖trunc(P Z) − trunc(h)‖_ρ ≤ cqp((4p)²) p · ω^{p+1} · ‖h‖_ρ` in the factorial norms.

The smallness `ω ≤ 1` is needed: the remainder has the powers `ω^{p+1}, …, ω^{2p}`
(`cqp_le'`).

For `𝖧 = 0` one may take `ω = 0` and the difference vanishes; for `p = 0` the remainder is
empty, `cqp X 0 = 0`, since `𝖯_0 = 𝖰_0 = I`. -/

/-- The constant of the remainder is nonnegative. -/
theorem cqp_nonneg' {X : ℝ} (hX : 0 ≤ X) (p : ℕ) : 0 ≤ cqp X p := by
  unfold cqp
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

/-- The remainder constant at a small argument: every term has degree at least `p + 1`. -/
theorem cqp_le' {X Y ω : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y * ω) (hY : 0 ≤ Y) (hω0 : 0 ≤ ω)
    (hω1 : ω ≤ 1) (p : ℕ) : cqp X p ≤ cqp Y p * ω ^ (p + 1) := by
  unfold cqp
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs with hab
  · have hfac : (0 : ℝ) ≤ (a.factorial : ℝ) * (b.factorial : ℝ) := by positivity
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hfac
    calc X ^ (a + b) ≤ (Y * ω) ^ (a + b) := pow_le_pow_left₀ hX hXY _
      _ = Y ^ (a + b) * ω ^ (a + b) := mul_pow _ _ _
      _ ≤ Y ^ (a + b) * ω ^ (p + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hω0 hω1 hab) (pow_nonneg hY _)
  · rw [zero_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **The filter defect is the adjoint remainder**: `trunc(P Z) − trunc(h)` in `H⁰`. -/
theorem filter_eq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {Nh Nq Np : ℕ}
    (h4 : 0 + 4 * p ≤ Nh) (h : TorusHk Nh E) (Qh : TorusHk Nq E) (PZ : TorusHk Np E)
    (hQ : IsCovImage (covPolyQ Hc p) h Qh) (hP : IsCovImage (covPolyP Hc p) Qh PZ) :
    truncateTorusHk (Nat.zero_le Np) PZ - truncateTorusHk (Nat.zero_le Nh) h =
      (TorusAdj.qpRem (E := E) Hc (le_refl (covBound Hc)) p 0 (4 * p)).neg.adj 0
        (Nat.zero_add (4 * p)).le (truncateTorusHk h4 h) := by
  apply InitialValue.torusHk_ext_of_jet_ae
  apply hilbert_ae_eq_of_cellInner_eq (InitialValue.torusHk_integrableOn_jet _ _)
    (InitialValue.torusHk_integrableOn_jet _ _)
  intro φ hφ hpφ
  have hPφ : ContDiff ℝ (⊤ : ℕ∞) (covPolyP Hc p φ) := contDiff_covPolyP_top Hc p hφ
  have hQPφ : ContDiff ℝ (⊤ : ℕ∞) (covPolyQ Hc p (covPolyP Hc p φ)) :=
    contDiff_covPolyQ_top Hc p hPφ
  have hL : cellInner (tval (truncateTorusHk (Nat.zero_le Np) PZ -
      truncateTorusHk (Nat.zero_le Nh) h)) φ = cellInner (tval PZ) φ - cellInner (tval h) φ := by
    rw [sub_eq_add_neg, cellInner_tval_add _ _ hφ.continuous, cellInner_tval_neg,
      tval_truncateTorusHk, tval_truncateTorusHk]
    ring
  have h1 : cellInner (tval PZ) φ = cellInner (tval h) (covPolyQ Hc p (covPolyP Hc p φ)) :=
    (hP φ hφ hpφ).trans (hQ _ hPφ (isZ2Periodic_covPolyP Hc p hφ hpφ))
  have hR := (TorusAdj.qpRem (E := E) Hc (le_refl (covBound Hc)) p 0 (4 * p)).neg.ident 0
    (Nat.zero_add (4 * p)).le (truncateTorusHk h4 h) φ (hφ.of_le (by exact_mod_cast le_top)) hpφ
  rw [tval_truncateTorusHk] at hR
  have hrem : qpRem Hc p φ = covPolyQ Hc p (covPolyP Hc p φ) - φ := by
    rw [← neg_sub, sub_covPolyQ_covPolyP_eq Hc p hφ, neg_neg]
  have hsplit : cellInner (tval h) (- -qpRem Hc p φ) =
      cellInner (tval h) (covPolyQ Hc p (covPolyP Hc p φ)) - cellInner (tval h) φ := by
    have e : - -qpRem Hc p φ = fun x => covPolyQ Hc p (covPolyP Hc p φ) x + (-φ) x := by
      rw [neg_neg, hrem]
      funext x
      simp only [Pi.sub_apply, Pi.neg_apply, sub_eq_add_neg]
    have e2 : cellInner (tval h) (-φ) = -cellInner (tval h) φ := cellInner_neg_right (tval h) φ
    rw [e, cellInner_add_right (tval h) (ψ₁ := covPolyQ Hc p (covPolyP Hc p φ)) (ψ₂ := -φ)
      (integrable_tval_inner h hQPφ.continuous) (integrable_tval_inner h hφ.continuous.neg), e2]
    ring
  show cellInner (tval (truncateTorusHk (Nat.zero_le Np) PZ -
    truncateTorusHk (Nat.zero_le Nh) h)) φ = cellInner (tval _) φ
  rw [hL, h1, hR, hsplit]

/-- **The covariance-filter estimate for one field**, in the factorial norms at the radius `ρ`. -/
theorem filter_component {ρ ω : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : covBound Hc ≤ ω * ρ ^ 2) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (p : ℕ) {Nh Nq Np : ℕ}
    (h4 : 4 * p ≤ Nh) (h : TorusHk Nh E) (Qh : TorusHk Nq E) (PZ : TorusHk Np E)
    (hQ : IsCovImage (covPolyQ Hc p) h Qh) (hP : IsCovImage (covPolyP Hc p) Qh PZ) :
    Real.sqrt (factorialNormSq ρ (truncateTorusHk (Nat.zero_le Np) PZ -
        truncateTorusHk (Nat.zero_le Nh) h).val) ≤
      cqp (((4 * p : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) * Real.sqrt (factorialNormSq ρ h.val) := by
  have h4' : 0 + 4 * p ≤ Nh := by omega
  rw [filter_eq Hc p h4' h Qh PZ hQ hP]
  have hF := (TorusAdj.FBound.neg (TorusAdj.FBound.qpRem (E := E) hρ Hc
    (le_refl (covBound Hc)) p 0 (4 * p))) 0 (Nat.zero_add (4 * p)).le (truncateTorusHk h4' h)
  refine hF.trans ?_
  have hc := cqp_le' (fbCovConst_nonneg hρ Hc (4 * p))
    (covOp_fbCovConst_le hρ Hc (4 * p) hb) (sq_nonneg _) hω0 hω1 p
  exact mul_le_mul hc (Real.sqrt_le_sqrt (factorialNormSq_truncateTorusHk_le h4' ρ h))
    (Real.sqrt_nonneg _) (mul_nonneg (cqp_nonneg' (sq_nonneg _) p) (pow_nonneg hω0 _))

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The reconstruction defect (i): the cell-mean identity at a lift setting**.

`cellMean_liftFluxX_eq'`: at a lift setting with a lift sequence of box orders `≥ D`, the cell
mean of the slow lift flux `liftFluxX` of positive grade is the action of the positive mean-flux
coefficient. This is `positiveMeanFluxCoefficient_literal_apply` (`EntryWeakProofs`) with its
regularity hypotheses discharged from `IsLiftSetting` and `IsLiftSequence`. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- A lift action of box smooth coefficients on a smooth field is box smooth and periodic, hence
a good field of any order up to the box orders. -/
theorem goodField_liftApply' {sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh q r : ℕ) (hr : r ≤ sX) (hr' : r ≤ sZ) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (hbox : ∀ m α v u, IsBoxSmooth sX sZ (fun X z => Cc hh q m α t X z v u))
    (hper : ∀ X m α v u, AVenhance.IsZ2Periodic (fun z => Cc hh q m α t X z v u)) :
    GoodField r (liftApply q (Cc hh q) (fun _ => f) t) := by
  have hb : IsBoxSmooth sX sZ (liftApply q (Cc hh q) (fun _ => f) t) :=
    AVRegularity.CycleComparison.Lift.isBoxSmooth_pi sX sZ _ fun v =>
      QuietDecay.Partition.isBoxSmooth_liftApply q sX sZ (Cc hh q) _ t (fun m α v' u => hbox m α v' u)
        (hf.of_le (by exact_mod_cast le_top)) v
  exact ⟨hb.contDiff_uncurry hr hr', fun X =>
    AVRegularity.CycleComparison.Reconstruction.liftApply_isZ2Periodic q (Cc hh q) _ t X
      (fun m α v u => hper X m α v u)⟩

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The cell-mean identity** (the reconstruction defect (i)): the cell mean of the
positive-grade slow lift flux is the action of the positive mean-flux coefficient. -/
theorem cellMean_liftFluxX_eq' (sX sZ : ℕ) (hX : D ≤ sX) (hZ : D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k₀ : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z v =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z k₀) v := by
  have hD2 := P.D_ge
  have hN1 := P.N_ge
  have hb : ∀ hh', hh' ≤ H → ∀ q m α v u, IsBoxSmooth sX sZ
      (fun X z => Cc hh' q m α t X z v u) := fun hh' h' q m α v u =>
    (hseq.2.2.2.2.2.1 hh' h' q m α v u t ht).1
  have hp : ∀ hh', hh' ≤ H → ∀ q X m α v u, AVenhance.IsZ2Periodic
      (fun z => Cc hh' q m α t X z v u) := fun hh' h' q X m α v u =>
    (hseq.2.2.2.2.2.1 hh' h' q m α v u t ht).2 X
  have hgood1 : ∀ hh' q, hh' ≤ H → ∀ r, r ≤ D →
      GoodField r (liftApply q (Cc hh' q) (fun _ => f) t) := fun hh' q h' r hr =>
    goodField_liftApply' Cc hh' q r (hr.trans hX) (hr.trans hZ) f hf t (hb hh' h' q)
      (fun X m α v u => hp hh' h' q X m α v u)
  have hΨmean : ∀ X', fieldCellMean (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t X') = 0 := by
    intro X'
    by_cases h0 : n - 2 = 0
    · have : liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t = fun _ _ => 0 :=
        liftApply_eq_zero_of_coeff _ _ (fun m α t X z v u => by
          rw [h0]; exact hseq.2.1 hh hhpos hhh m α t X z v u) _ _
      rw [this]; exact fieldCellMean_zero
    · by_cases hle : n - 2 ≤ N
      · exact liftApply_fieldCellMean_eq_zero Q sX sZ a b N H Cc hseq hh hhh (n - 2)
          (by omega) hle f hf t ht X'
      · have : liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t = fun _ _ => 0 :=
          liftApply_eq_zero_of_coeff _ _ (fun m α t X z v u =>
            hseq.2.2.1 hh hhh (n - 2) (by omega) m α t X z v u) _ _
        rw [this]; exact fieldCellMean_zero
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z) := by
    intro v u d γ hγ α
    have hbs := P.coeff_smooth v u d γ hγ α t ht
    have hqs : 1 ≤ qs := by
      have h1 : 0 < N + D := by omega
      have h2 : 0 < 4 * (H + 1) * (N + D) ^ 2 := by positivity
      rw [P.qs_eq]; omega
    have hqf : 1 ≤ qf := by rw [P.qf_eq]; omega
    exact ⟨hbs.contDiff_uncurry hqs hqf, fun X => γ.periodic α t X⟩
  have hi := liftFluxX_cell_mean_intrinsic Q (by omega) Cc hh n hn
    (by omega) (fun _ => f) t X k₀
    (fun i j => (P.G_smooth t ht i j).of_le (by exact_mod_cast Nat.zero_le qs))
    (setting_drift_continuous P t ht) (hgood1 hh (n - 1) hhh 1 (by omega))
    ⟨hgood1 hh (n - 2) hhh 1 (by omega), fun _ X' => hΨmean X'⟩
    (fun q => hgood1 (hh - 1) q (by omega) D le_rfl) hΓ
  have hres : 0 + (N + D) ≤ qs := by
    rw [P.qs_eq]
    nlinarith [P.N_ge, P.D_ge, Nat.zero_le K, Nat.zero_le H, sq_nonneg (N + D)]
  have hvec := setting_positive_mean_flux_coefficient_vector_apply P sX sZ
    (by omega) (by omega) Cc hseq 0 hres hh hhpos hhh n hn hnR f hf k₀ t ht X z
  have hsrc : (fun y => sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X y) =
      fun y => ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxCoefficientArray Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t) k₀ j X y := by
    funext y
    exact setting_sourceFlux_lift_convolution P sX sZ (by omega) Cc hseq
      (hh - 1) (by omega) (n - 1) k₀ f hf t ht X y
  change sourceFluxCoeff Q.edge Q.η (n - 1) t
    (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X = _ at hsrc
  rw [hsrc] at hvec
  exact congrFun (hvec.trans hi.symm) v

include P in
omit [∀ i, BorelSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- **The cell-mean identity at grade zero**: the cell mean of the grade-zero slow lift flux is the
action of the diagonal mean-flux coefficient. -/
theorem diag_cellMean_liftFluxX_eq' (sX sZ : ℕ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k₀) (fun _ => f) t X z =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z k₀) := by
  have hb : ∀ q m α v u, IsBoxSmooth sX sZ (fun X z => Cc 0 q m α t X z v u) :=
    fun q m α v u => (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) q m α v u t ht).1
  have hgood : ∀ q, GoodField 1 (liftApply q (Cc 0 q) (fun _ => f) t) := fun q =>
    goodField_liftApply' Cc 0 q 1 hX hZ f hf t (hb q)
      (fun X m α v u => (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) q m α v u t ht).2 X)
  have hΦ := hgood (n - 1)
  have hΨ := hgood (n - 2)
  set Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t with hΦdef
  set Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t with hΨdef
  have hΦX : ContDiff ℝ 1 (Φ X) := by
    have := hΦ.1.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ _ (fun z : Vec 2 => (X, z)))
    exact this
  have hcΦ : Continuous (Φ X) := hΦX.continuous
  have hfast : ∀ j : Fin 2, fieldCellMean (fun z => fastPartial j Φ X z) = 0 := fun j =>
    fieldCellMean_fastPartial_eq_zero (Φ X) hΦX (hΦ.2 X) j
  have hcfast : ∀ j : Fin 2, Continuous (fun z => fastPartial j Φ X z) := fun j =>
    (hΦX.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcslow : ∀ j : Fin 2, Continuous (fun z => slowPartial j Ψ X z) := by
    intro j
    have := continuous_fderiv_slow_of_contDiff hΨ.1
    exact (this.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hslow : ∀ j : Fin 2, fieldCellMean (fun z => slowPartial j Ψ X z) =
      if n = 2 then fderiv ℝ f X (basisVec j) else 0 := by
    intro j
    rw [fieldCellMean_slowPartial hΨ.1 X j]
    by_cases hn2 : n = 2
    · subst hn2
      have hΨf : Ψ = fun X' _ => f X' := by
        funext X' z'
        exact hseq.1 f hf t ht X' z'
      have : (fun X' => fieldCellMean (Ψ X')) = f := by
        funext X'
        rw [hΨf]; exact fieldCellMean_const _
      rw [this]; simp
    · have hmean : ∀ X', fieldCellMean (Ψ X') = 0 := by
        intro X'
        by_cases hle : n - 2 ≤ N
        · exact liftApply_fieldCellMean_eq_zero Q sX sZ a b N H Cc hseq 0 (Nat.zero_le H)
            (n - 2) (by omega) hle f hf t ht X'
        · have : Ψ = fun _ _ => 0 := liftApply_eq_zero_of_coeff _ _
            (fun m α t X z v u => hseq.2.2.1 0 (Nat.zero_le H) (n - 2) (by omega) m α t X z v u)
            _ _
          rw [this]; exact fieldCellMean_zero
      have : (fun X' => fieldCellMean (Ψ X')) = fun _ => 0 := funext hmean
      rw [this]; simp [hn2]
  have hcA : Continuous (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z) :=
    ((continuous_const.mul ((continuous_apply k₀).comp (setting_drift_continuous P t ht))).fun_smul
      hcΦ)
  have hcB : Continuous (fun z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) :=
    continuous_const.fun_smul (continuous_finsetSum _ fun j _ => continuous_const.fun_smul (hcfast j))
  have hcC : Continuous (fun z => Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z) :=
    continuous_const.fun_smul (continuous_finsetSum _ fun j _ => continuous_const.fun_smul (hcslow j))
  have hfs := fieldCellMean_sum (Finset.univ : Finset (Fin 2))
    (f := fun j z => Q.G t X k₀ j • fastPartial j Φ X z)
    (fun j _ => continuous_const.fun_smul (hcfast j))
  have hss := fieldCellMean_sum (Finset.univ : Finset (Fin 2))
    (f := fun j z => Q.G t X k₀ j • slowPartial j Ψ X z)
    (fun j _ => continuous_const.fun_smul (hcslow j))
  have hflux : (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z k₀) = fun z =>
      ((Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
        -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z) := by
    funext z
    simp [liftFluxX, show 2 ≤ n by omega, hΦdef, hΨdef]
  have e1 : fieldCellMean (fun z => ((Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
        -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z)) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
      fieldCellMean (fun z => -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z)) :=
    fieldCellMean_add (hcA.sub hcB) hcC.neg
  have e2 : fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z) -
      fieldCellMean (fun z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) :=
    fieldCellMean_sub hcA hcB
  rw [hflux, e1, e2, fieldCellMean_neg, fieldCellMean_smul, fieldCellMean_smul, hfs, hss]
  simp only [fieldCellMean_smul, hfast, hslow, smul_zero, Finset.sum_const_zero, sub_zero]
  rw [setting_diagonal_mean_flux_coefficient_vector_apply P sX sZ Cc hseq n hn f k₀ t ht X z]
  by_cases hn2 : n = 2
  · subst hn2
    simp only [ite_true, neg_smul]
    rfl
  · simp only [hn2, ite_false, smul_zero, Finset.sum_const_zero, neg_zero, add_zero]
    rfl

end AVRegularity.Construction.Residual.Presentation.Cascade
end
