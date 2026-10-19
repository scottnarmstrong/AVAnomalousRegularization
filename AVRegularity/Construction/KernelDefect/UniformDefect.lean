-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Analysis.Convolution.Kernel.PairedSource
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.KernelEnergy.TorusMultiplierTime
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The moment bound of a kernel defect, at the regularizer level** (generic; no stage,
no terminal context). 

A moving paired kernel `S(t) = S_{r,H₁(t)} S_{r,H₂(t)}` (`KernelSpec`, acting on classical fields by
`KernelSpec.applyClassical`) whose signed profile `𝗄_n` has vanishing moments through `L`
(`KernelSpec.IsAdmissible S Γ L`: `‖H_i(t)‖ ≤ Γ`, `L + 1 ≤ 2n`) leaves a defect `(I - S(t))a` of
size `(r/ρ)^L` relative to `L` more derivatives at the radius `ρ ≥ r`:
`‖(I - S(t))a‖_{ρ,k} ≤ C_{k,L}(r/ρ)^L ‖a‖_{ρ,k+L}` in the factorial weighted norm
(`factorialNormSq`) of the torus jets. Derivatives commute with the convolution (the matrices
depend on time only), so the order-`k` statement is the value-level moment bound applied to each
jet; the value-level bound is the Taylor expansion of `a(y - rH₁z - rH₂z')` to order `L - 1`, whose
polynomial terms the vanishing moments remove. The constant depends on `k, L, Γ`, the profile and
the order `n` of the kernel (through `∫|𝗄_n|`) only.

Consumers: the fine matrix tail (`FineDefectAt`: the weak kernel `S_w` at `r_w` with
`L = L_f`) and the coarse filter tails (`FilterDefectStatement`: the fresh kernels at
`r_new` with `L_c`, the old filters at `r_w` with `L_o`).

Degenerate cases:
- `L = 0`: `‖(I - S)a‖_{ρ,k} ≤ C‖a‖_{ρ,k}`, the boundedness of the kernel on each jet (`Γ`-dependent).
- `k = 0`: the value-level bound `‖(I - S)a‖_{L²} ≤ C(r/ρ)^L ‖a‖_{ρ,L}`.
- `a` constant: `(I - S)a = 0` (`∫ 𝗄_n = 1`), and both sides are consistent.
- `ρ = r`: the factor `(r/ρ)^L = 1`, again boundedness.
- `H₁ = H₂ = 0`: excluded by `IsAdmissible` (the spanning matrix is singular).
- Constant order: `C` is chosen after `(φ₀, k, L, n, Γ)` and before the kernel, the time, the
  radius and the field. It cannot be uniform in `n`: `∫|𝗄_n|` grows with `n`. The consumers fix
  `n` (`n_W`, `n_T`) before their constants. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.Construction.KernelDefect

/-- **Pointwise in time.** For a moment kernel of width `r ≤ ρ` with vanishing moments
through `L`, the defect of a `C^{k+L}` periodic field has a torus realization of order `k` with
`‖(I - S(t))a‖_{ρ,k} ≤ C(r/ρ)^L‖a‖_{ρ,k+L}`. -/
def KernelDefectStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (φ₀ : Vec 2 → ℝ), Integrable φ₀ → ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (k L : ℕ) (n : ℕ+) (Γ : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (S : KernelSpec) (t ρ : ℝ), S.order = n → S.IsAdmissible Γ L → 0 < S.width → S.width ≤ ρ →
    ∀ (u : TorusHk (k + L) E) (a : Vec 2 → E), IsClassicalRep u a (k + L) →
    ∃ w : TorusHk k E, IsClassicalRep w (fun y => a y - S.applyClassical φ₀ t a y) k ∧
      factorialNormSq ρ w.val ≤ (C * (S.width / ρ) ^ L) ^ 2 * factorialNormSq ρ u.val

end AVRegularity.Construction.KernelDefect
end
end

section
/-! **Moment bound of one jet.** For a field `F` with `L` weak derivatives,
`‖F - S(t) F‖_{L²} ≤ C₀ r^L ‖∇^L F‖_{L²}`, where `C₀` depends on the profile, the order `n`, `L`
and the bound `Γ` of the matrices only. It is the value-level torus bound
`momentKernel_paired_approximation_torus` for the Hilbert matrices `r H_i(t)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.KernelDefect

/-- The moment constant of one jet. -/
def kdMomentConst (φ₀ : Vec 2 → ℝ) (n : ℕ+) (L : ℕ) (Γ : ℝ) : ℝ :=
  if L = 0 then 2 else
    2 * (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) * (2 * Γ) ^ L / (L.factorial : ℝ)

/-- A template supported in the closed Euclidean unit ball has compact support. -/
theorem kd_hasCompactSupport {φ₀ : Vec 2 → ℝ}
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) : HasCompactSupport φ₀ := by
  have hc : IsCompact closedEuclideanUnitBall := by
    let L := (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm
    have heq : closedEuclideanUnitBall = L ⁻¹' Metric.closedBall 0 1 := by
      ext z
      simp only [closedEuclideanUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right, euclideanNorm]
      rfl
    rw [heq]
    exact L.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 1)
  have hcl : IsClosed closedEuclideanUnitBall :=
    isClosed_le euclideanNorm_continuous continuous_const
  exact HasCompactSupport.intro' hc hcl
    (fun x hx => Function.notMem_support.1 fun h => hx (hφsupp h))

theorem kd_hilbert_norm_le (v : Vec 2) : ‖HilbertVec.ofVec v‖ ≤ 2 * ‖v‖ := by
  have h0 := norm_le_pi_norm v 0
  have h1 := norm_le_pi_norm v 1
  have hsq : ‖HilbertVec.ofVec v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have h2 : ‖HilbertVec.ofVec v‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
    rw [hsq]
    nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2

/-- The Hilbert-space matrix of `r H`. -/
def kdHilbert (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) : HilbertTwo →L[ℝ] HilbertTwo :=
  coordinateHilbertEquiv.symm.toContinuousLinearMap.comp
    ((r • H).comp coordinateHilbertEquiv.toContinuousLinearMap)

theorem spatialHilbertOperator_kdHilbert (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) :
    spatialHilbertOperator (kdHilbert r H) = r • H := by
  ext z : 1
  simp [spatialHilbertOperator, kdHilbert]

theorem kdHilbert_norm_le {r Γ : ℝ} (hr : 0 ≤ r) {H : Vec 2 →L[ℝ] Vec 2} (hH : ‖H‖ ≤ Γ) :
    ‖kdHilbert r H‖ ≤ 2 * (r * Γ) := by
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hH
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have e1 : ‖coordinateHilbertEquiv h‖ ≤ ‖h‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact HilbertVec.abs_apply_le_norm h i
  have e2 : ‖(r • H) (coordinateHilbertEquiv h)‖ ≤ r * Γ * ‖h‖ := by
    calc ‖(r • H) (coordinateHilbertEquiv h)‖ ≤ ‖r • H‖ * ‖coordinateHilbertEquiv h‖ :=
          (r • H).le_opNorm _
      _ ≤ (r * Γ) * ‖h‖ := by
          have : ‖r • H‖ ≤ r * Γ := by
            rw [norm_smul, Real.norm_of_nonneg hr]
            exact mul_le_mul_of_nonneg_left hH hr
          exact mul_le_mul this e1 (norm_nonneg _) (by positivity)
  change ‖HilbertVec.ofVec ((r • H) (coordinateHilbertEquiv h))‖ ≤ _
  calc _ ≤ 2 * ‖(r • H) (coordinateHilbertEquiv h)‖ := kd_hilbert_norm_le _
    _ ≤ 2 * (r * Γ * ‖h‖) := by linarith
    _ = 2 * (r * Γ) * ‖h‖ := by ring

section Bound

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem kd_displacement_eq (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) :
    torusQuotient.comp (displacement r H) =
      torusQuotient.comp ((spatialHilbertOperator (kdHilbert r H)).toAddHom : Vec 2 →+ Vec 2) := by
  congr 1

omit [FiniteDimensional ℝ E] in
theorem kd_op_sub_zero {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1) (S : KernelSpec) (t : ℝ) (F : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    ‖F - S.op φ₀ hφ t F‖ ≤ 2 * ‖F‖ := by
  have h : ‖S.op φ₀ hφ t F‖ ≤ ‖F‖ := by
    unfold KernelSpec.op
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    exact (periodicComponentAverage_momentKernel_norm _ _ hφ hnonneg hmass _ _).trans
      (periodicComponentAverage_momentKernel_norm _ _ hφ hnonneg hmass _ _)
  calc ‖F - S.op φ₀ hφ t F‖ ≤ ‖F‖ + ‖S.op φ₀ hφ t F‖ := norm_sub_le _ _
    _ ≤ 2 * ‖F‖ := by linarith

omit [FiniteDimensional ℝ E] in
theorem kd_derivativeNormSq_zero (f : TorusHk 0 E) :
    Real.sqrt (derivativeNormSq f.val ⟨0, Nat.lt_succ_self 0⟩) = ‖f.val (valueIndex2 0)‖ := by
  unfold derivativeNormSq
  rw [Fintype.sum_unique]
  rw [Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- **The moment bound of one jet.** -/
theorem kd_moment_bound {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (n : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t : ℝ) (hn : S.order = n) (hL : L + 1 ≤ 2 * (n : ℕ)) (hr : 0 < S.width)
    (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ) (f : TorusHk L E) :
    ‖f.val (valueIndex2 L) - S.op φ₀ hφ t (f.val (valueIndex2 L))‖ ≤
      kdMomentConst φ₀ n L Γ * S.width ^ L *
        Real.sqrt (derivativeNormSq f.val ⟨L, Nat.lt_succ_self L⟩) := by
  subst hn
  by_cases hL0 : L = 0
  · subst hL0
    have := kd_op_sub_zero hφ hnonneg hmass S t (f.val (valueIndex2 0))
    rw [kd_derivativeNormSq_zero]
    simpa [kdMomentConst] using this
  · have hK : 0 < L := Nat.pos_of_ne_zero hL0
    have hKn : L < 2 * (S.order : ℕ) := by omega
    have hc := kd_hasCompactSupport hsupp
    have hsupp' : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1 :=
      fun z hz => hsupp hz
    have hΓ : 0 ≤ Γ := (norm_nonneg _).trans h1
    set T₁ := kdHilbert S.width (S.H₁ t) with hT₁
    set T₂ := kdHilbert S.width (S.H₂ t) with hT₂
    have happrox := momentKernel_paired_approximation_torus (E := E) hc hd hnonneg hmass hsupp' S.order
      hK hKn T₁ T₂ f
    set F := f.val (valueIndex2 L) with hF
    have hA := averagingOperator_torus_congr_map (E := E)
      (ρ := torusQuotient.comp (displacement S.width (S.H₁ t)))
      (σ := torusQuotient.comp (spatialHilbertOperator T₁).toAddHom)
      (kd_displacement_eq _ _) (continuous_torusQuotient.comp (continuous_displacement _ _))
      (continuous_torusQuotient.comp (spatialHilbertOperator T₁).continuous)
      (κ := momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order)
    have hB := averagingOperator_torus_congr_map (E := E)
      (ρ := torusQuotient.comp (displacement S.width (S.H₂ t)))
      (σ := torusQuotient.comp (spatialHilbertOperator T₂).toAddHom)
      (kd_displacement_eq _ _) (continuous_torusQuotient.comp (continuous_displacement _ _))
      (continuous_torusQuotient.comp (spatialHilbertOperator T₂).continuous)
      (κ := momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order)
    have hop : S.op φ₀ hφ t F = torusToCell (averagingOperator (E := E) (μ := torusMeasure)
        (torusQuotient.comp (displacement S.width (S.H₁ t)))
        (continuous_torusQuotient.comp (continuous_displacement _ _)) (momentKernel φ₀ S.order)
        (integrable_momentKernel hφ S.order) (averagingOperator (E := E) (μ := torusMeasure)
        (torusQuotient.comp (displacement S.width (S.H₂ t)))
        (continuous_torusQuotient.comp (continuous_displacement _ _)) (momentKernel φ₀ S.order)
        (integrable_momentKernel hφ S.order) (cellToTorus F))) := by
      unfold KernelSpec.op periodicComponentAverage
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      rw [cellToTorus_torusToCell]
    have hT1 := kdHilbert_norm_le hr.le h1
    have hT2 := kdHilbert_norm_le hr.le h2
    have hM : 0 ≤ ∫ z : Vec 2, ‖momentKernel φ₀ S.order z‖ := integral_nonneg fun _ => norm_nonneg _
    have hpow : ‖T₂‖ ^ L + ‖T₁‖ ^ L ≤ 2 * (2 * (S.width * Γ)) ^ L := by
      have a1 := pow_le_pow_left₀ (norm_nonneg _) hT1 L
      have a2 := pow_le_pow_left₀ (norm_nonneg _) hT2 L
      linarith
    have hfac : (0 : ℝ) < L.factorial := by exact_mod_cast Nat.factorial_pos L
    calc ‖F - S.op φ₀ hφ t F‖ = ‖cellToTorus F - averagingOperator (E := E) (μ := torusMeasure)
          (torusQuotient.comp (spatialHilbertOperator T₁).toAddHom)
          (continuous_torusQuotient.comp (spatialHilbertOperator T₁).continuous)
          (momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order)
          (averagingOperator (E := E) (μ := torusMeasure)
          (torusQuotient.comp (spatialHilbertOperator T₂).toAddHom)
          (continuous_torusQuotient.comp (spatialHilbertOperator T₂).continuous)
          (momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order) (cellToTorus F))‖ := by
          rw [← hA, ← hB, ← torusToCell.norm_map, map_sub, hop, torusToCell_cellToTorus]
      _ = ‖averagingOperator (E := E) (μ := torusMeasure)
          (torusQuotient.comp (spatialHilbertOperator T₁).toAddHom)
          (continuous_torusQuotient.comp (spatialHilbertOperator T₁).continuous)
          (momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order)
          (averagingOperator (E := E) (μ := torusMeasure)
          (torusQuotient.comp (spatialHilbertOperator T₂).toAddHom)
          (continuous_torusQuotient.comp (spatialHilbertOperator T₂).continuous)
          (momentKernel φ₀ S.order) (integrable_momentKernel hφ S.order) (cellToTorus F)) - cellToTorus F‖ :=
          norm_sub_rev _ _
      _ ≤ _ := happrox
      _ ≤ (∫ z : Vec 2, ‖momentKernel φ₀ S.order z‖) * ((2 * (2 * (S.width * Γ)) ^ L) *
            Real.sqrt (derivativeNormSq f.val ⟨L, Nat.lt_succ_self L⟩) / (L.factorial : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)) hfac.le
      _ = _ := by
          simp only [kdMomentConst, hL0, ite_false]
          rw [mul_pow, mul_pow, mul_pow]
          field_simp

end Bound

end AVRegularity.Construction.KernelDefect
end
end

section
/-! **The moment bound of one jet, uniform in the order of the kernel.**

`kd_moment_bound` bounds `‖F - S(t)F‖_{L²}` by `kdMomentConst φ₀ n L Γ · r^L ‖∇^L F‖_{L²}` with a
constant that depends on the order `n` of the kernel through `∫|𝗄_n|`. Here the same bound is
proved with the constant of any order `m ≤ n` that still has `L + 1 ≤ 2m`
(`kd_moment_bound_of_order_le`), hence with the constant of the least admissible order
`n₀ = L/2 + 1`, which depends on the profile, `L` and `Γ` only (`kdUniformMomentConst`).

Proof: for one average, `averagingOperator_momentKernel_defect_le_of_le` bounds the order-`n` defect
at the matrix `rH` by the order-`m` defect at the matrix `(m/n) rH`, to which the value-level bound
of the tree (`momentKernel_approximation_torus`, at the fixed order `m`) applies with the smaller
matrix; the pair costs the factor `2` as in `kd_moment_bound`.

The degenerate cases are included: for `L = 0` the constant is `2` (boundedness of `S`); `n = 1`
forces `L ≤ 1` and `n₀ = 1`, the bound of `kd_moment_bound` itself; `m = n` is `kd_moment_bound`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.KernelDefect

/-- The least order `n₀` with `L + 1 ≤ 2 n₀`. -/
def kdUniformOrder (L : ℕ) : ℕ+ := ⟨L / 2 + 1, Nat.succ_pos _⟩

theorem kdUniformOrder_spec (L : ℕ) : L + 1 ≤ 2 * (kdUniformOrder L : ℕ) := by
  change L + 1 ≤ 2 * (L / 2 + 1)
  omega

theorem kdUniformOrder_le {L : ℕ} {n : ℕ+} (hL : L + 1 ≤ 2 * (n : ℕ)) : kdUniformOrder L ≤ n := by
  change L / 2 + 1 ≤ (n : ℕ)
  omega

/-- The moment constant of one jet at the least admissible order: it depends on the profile, `L`
and the bound `Γ` of the matrices only. -/
def kdUniformMomentConst (φ₀ : Vec 2 → ℝ) (L : ℕ) (Γ : ℝ) : ℝ :=
  kdMomentConst φ₀ (kdUniformOrder L) L Γ

/-- The displacement of `r H` shrunk by `c` is the displacement of the Hilbert matrix of
`(r c) H`. -/
theorem kd_rescaled_displacement_eq (c r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) :
    rescaleDisplacement c (torusQuotient.comp (displacement r H)) =
      torusQuotient.comp
        ((spatialHilbertOperator (kdHilbert (r * c) H)).toAddHom : Vec 2 →+ Vec 2) := by
  apply AddMonoidHom.ext
  intro z
  have h : r • H (c • z) = ((r * c) • H) z := by
    rw [map_smul, smul_smul]
    rfl
  change torusQuotient (r • H (c • z)) =
    torusQuotient (spatialHilbertOperator (kdHilbert (r * c) H) z)
  rw [spatialHilbertOperator_kdHilbert, h]

theorem kd_pair_const_eq (M r Γ s : ℝ) (L : ℕ) :
    M * ((2 * (r * Γ)) ^ L * s / (L.factorial : ℝ)) +
        M * ((2 * (r * Γ)) ^ L * s / (L.factorial : ℝ)) =
      2 * M * (2 * Γ) ^ L / (L.factorial : ℝ) * r ^ L * s := by
  rw [mul_pow, mul_pow, mul_pow]
  ring

section Bound

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One average on the torus: the defect of the order-`n` kernel at the matrix `r H` has the
moment bound of every order `m ≤ n` with `L < 2m`. -/
theorem kd_single_defect_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) {L : ℕ} (hL0 : 0 < L) {m n : ℕ+}
    (hmn : m ≤ n) (hLm : L < 2 * (m : ℕ)) {r Γ : ℝ} (hr : 0 ≤ r) {H : Vec 2 →L[ℝ] Vec 2}
    (hH : ‖H‖ ≤ Γ) (f : TorusHk L E) :
    ‖cellToTorus (f.val (valueIndex2 L)) -
        averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (displacement r H))
          (continuous_torusQuotient.comp (continuous_displacement r H)) (momentKernel φ₀ n)
          (integrable_momentKernel hφ n) (cellToTorus (f.val (valueIndex2 L)))‖ ≤
      (∫ z : Vec 2, ‖momentKernel φ₀ m z‖) * ((2 * (r * Γ)) ^ L *
        Real.sqrt (derivativeNormSq f.val ⟨L, Nat.lt_succ_self L⟩) / (L.factorial : ℝ)) := by
  have hc := kd_hasCompactSupport hsupp
  have hsupp' : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1 :=
    fun z hz => hsupp hz
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hH
  have hc0 : 0 ≤ orderRatio m n := (orderRatio_pos m n).le
  have hc1 : orderRatio m n ≤ 1 := orderRatio_le_one hmn
  set T := kdHilbert (r * orderRatio m n) H with hT
  have hred := averagingOperator_momentKernel_defect_le_of_le (E := E) (μ := torusMeasure)
    (torusQuotient.comp (displacement r H))
    (continuous_torusQuotient.comp (continuous_displacement r H)) hφ hnonneg hmass hmn
    (cellToTorus (f.val (valueIndex2 L)))
  have hcong := averagingOperator_torus_congr_map (E := E)
    (ρ := rescaleDisplacement (orderRatio m n) (torusQuotient.comp (displacement r H)))
    (σ := torusQuotient.comp (spatialHilbertOperator T).toAddHom)
    (kd_rescaled_displacement_eq (orderRatio m n) r H)
    (continuous_rescaleDisplacement _
      (continuous_torusQuotient.comp (continuous_displacement r H)))
    (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous)
    (κ := momentKernel φ₀ m) (integrable_momentKernel hφ m)
  have happrox := momentKernel_approximation_torus (E := E) hc hd hnonneg hmass hsupp' m hL0 hLm
    T f
  have hTn : ‖T‖ ≤ 2 * (r * Γ) := by
    have h := kdHilbert_norm_le (r := r * orderRatio m n) (mul_nonneg hr hc0) hH
    have h' : r * Γ * orderRatio m n ≤ r * Γ * 1 :=
      mul_le_mul_of_nonneg_left hc1 (mul_nonneg hr hΓ)
    calc ‖T‖ ≤ 2 * (r * orderRatio m n * Γ) := h
      _ = 2 * (r * Γ * orderRatio m n) := by ring
      _ ≤ 2 * (r * Γ * 1) := by linarith
      _ = 2 * (r * Γ) := by ring
  have hM : 0 ≤ ∫ z : Vec 2, ‖momentKernel φ₀ m z‖ := integral_nonneg fun _ => norm_nonneg _
  have hfac : (0 : ℝ) < L.factorial := by exact_mod_cast Nat.factorial_pos L
  refine hred.trans ?_
  rw [hcong, norm_sub_rev]
  refine happrox.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hM
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hTn L) (Real.sqrt_nonneg _))
    hfac.le

/-- **The moment bound of one jet with the constant of a lower order.** For a kernel of order
`n = S.order` and any order `m ≤ n` with `L + 1 ≤ 2m`, the bound of `kd_moment_bound` holds with
the constant of the order `m`. -/
theorem kd_moment_bound_of_order_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (m : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t : ℝ) (hm : m ≤ S.order) (hL : L + 1 ≤ 2 * (m : ℕ)) (hr : 0 < S.width)
    (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ) (f : TorusHk L E) :
    ‖f.val (valueIndex2 L) - S.op φ₀ hφ t (f.val (valueIndex2 L))‖ ≤
      kdMomentConst φ₀ m L Γ * S.width ^ L *
        Real.sqrt (derivativeNormSq f.val ⟨L, Nat.lt_succ_self L⟩) := by
  by_cases hL0 : L = 0
  · subst hL0
    have := kd_op_sub_zero hφ hnonneg hmass S t (f.val (valueIndex2 0))
    rw [kd_derivativeNormSq_zero]
    simpa [kdMomentConst] using this
  · have hK : 0 < L := Nat.pos_of_ne_zero hL0
    have hKm : L < 2 * (m : ℕ) := by omega
    set F := f.val (valueIndex2 L) with hF
    set A₁ := averagingOperator (E := E) (μ := torusMeasure)
      (torusQuotient.comp (displacement S.width (S.H₁ t)))
      (continuous_torusQuotient.comp (continuous_displacement _ _)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ S.order) with hA₁
    set A₂ := averagingOperator (E := E) (μ := torusMeasure)
      (torusQuotient.comp (displacement S.width (S.H₂ t)))
      (continuous_torusQuotient.comp (continuous_displacement _ _)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ S.order) with hA₂
    have hop : S.op φ₀ hφ t F = torusToCell (A₁ (A₂ (cellToTorus F))) := by
      unfold KernelSpec.op periodicComponentAverage
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap]
      rw [cellToTorus_torusToCell]
    have hA₁n : ‖A₁‖ ≤ 1 := averagingOperator_momentKernel_contraction _ _ hφ hnonneg hmass _
    have b1 : ‖cellToTorus F - A₁ (cellToTorus F)‖ ≤ _ :=
      kd_single_defect_le hφ hd hnonneg hmass hsupp hK hm hKm hr.le h1 f
    have b2 : ‖cellToTorus F - A₂ (cellToTorus F)‖ ≤ _ :=
      kd_single_defect_le hφ hd hnonneg hmass hsupp hK hm hKm hr.le h2 f
    have hsplit : ‖cellToTorus F - A₁ (A₂ (cellToTorus F))‖ ≤
        ‖cellToTorus F - A₂ (cellToTorus F)‖ + ‖cellToTorus F - A₁ (cellToTorus F)‖ := by
      have h := norm_comp_sub_le A₁ A₂ hA₁n (cellToTorus F)
      rw [norm_sub_rev (cellToTorus F) (A₁ (A₂ (cellToTorus F))),
        norm_sub_rev (cellToTorus F) (A₂ (cellToTorus F)),
        norm_sub_rev (cellToTorus F) (A₁ (cellToTorus F))]
      exact h
    have e : F - S.op φ₀ hφ t F = torusToCell (cellToTorus F - A₁ (A₂ (cellToTorus F))) := by
      rw [map_sub, torusToCell_cellToTorus, hop]
    rw [e, torusToCell.norm_map]
    refine hsplit.trans ((add_le_add b2 b1).trans (le_of_eq ?_))
    simp only [kdMomentConst, hL0, ite_false]
    exact kd_pair_const_eq _ _ _ _ _

end Bound

end AVRegularity.Construction.KernelDefect
end
end
end

section
section
/-! **Shifted jets.** For a classical representative `a` of `u : TorusHk (k+L) E`
and a word `β` of length `j ≤ k`, the derivative `∂^β a` is `C^L` and periodic, so it is the value
of a torus element `kdShift` of order `L`. The jets of `kdShift` are the jets of `u` of the
concatenated words, and the squared jet norms of the shifts sum to at most the squared jet norm of
`u` at order `j + L`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity

namespace AVRegularity.Construction.KernelDefect

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Derivatives along a concatenated word are iterated derivatives. -/
theorem kd_orderedDerivative_append {j L : ℕ} (β : DerivativeWord2 j) (γ : DerivativeWord2 L)
    (g : Vec 2 → E) :
    orderedDerivative γ (orderedDerivative β g) = orderedDerivative (Fin.append β γ) g := by
  unfold orderedDerivative
  rw [List.ofFn_fin_append, List.foldl_append]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem kd_contDiff_derivative {k L j : ℕ} {a : Vec 2 → E} (ha : ContDiff ℝ ((k + L : ℕ) : ℕ∞) a)
    (hj : j ≤ k) (β : DerivativeWord2 j) :
    ContDiff ℝ (L : ℕ∞) (orderedDerivative β a) :=
  ChartTransport.contDiff_orderedDerivative (p := L) β
    (ha.of_le (by exact_mod_cast (by omega : L + j ≤ k + L)))

/-- The torus element of order `L` carrying `∂^β a`. -/
def kdShift {k L : ℕ} (a : Vec 2 → E) (ha : ContDiff ℝ ((k + L : ℕ) : ℕ∞) a)
    (hp : AVenhance.IsZ2Periodic a) {j : ℕ} (hj : j ≤ k) (β : DerivativeWord2 j) :
    TorusHk L E :=
  CycleComparison.Reconstruction.periodicHk L (orderedDerivative β a)
    (kd_contDiff_derivative ha hj β) (ChartTransport.isZ2Periodic_orderedDerivative β hp)

theorem kdShift_jet_ae {k L : ℕ} {u : TorusHk (k + L) E} {a : Vec 2 → E}
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) (β : DerivativeWord2 j)
    {m : ℕ} (hm : m ≤ L) (γ : DerivativeWord2 m) :
    (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨⟨m, Nat.lt_succ_of_le hm⟩, γ⟩
      =ᵐ[volume.restrict AVenhance.unitCube]
        u.val ⟨⟨j + m, Nat.lt_succ_of_le (by omega)⟩, Fin.append β γ⟩ := by
  have h1 := CycleComparison.Reconstruction.periodicHk_jet_ae L (orderedDerivative β a)
    (kd_contDiff_derivative hu.2.1 hj β) (ChartTransport.isZ2Periodic_orderedDerivative β hu.2.2.1)
    ⟨⟨m, Nat.lt_succ_of_le hm⟩, γ⟩
  have h2 := CycleComparison.Assembly.torusJetOrder_ae u (m := j + m) (by omega)
    (Fin.append β γ)
  have h3 := hu.2.2.2 (j + m) (by omega) (Fin.append β γ)
  refine h1.trans ?_
  simp only
  rw [kd_orderedDerivative_append]
  exact (h3.symm.trans h2)

theorem kdShift_value_ae {k L : ℕ} {u : TorusHk (k + L) E} {a : Vec 2 → E}
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) (β : DerivativeWord2 j) :
    (kdShift a hu.2.1 hu.2.2.1 hj β).val (valueIndex2 L)
      = u.val ⟨⟨j, Nat.lt_succ_of_le (by omega)⟩, β⟩ := by
  have h := kdShift_jet_ae hu hj β (Nat.zero_le L) (Fin.elim0 : DerivativeWord2 0)
  apply Lp.ext
  refine h.trans ?_
  have e : (Fin.append β (Fin.elim0 : DerivativeWord2 0)) = β := by
    funext i; simp only [Fin.append, Fin.addCases]; simp [Fin.castLT]
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun w : DerivativeWord2 j =>
      (u.val ⟨⟨j, Nat.lt_succ_of_le (by omega)⟩, w⟩ : Vec 2 → E)) e)

theorem kd_append_injective (j L : ℕ) :
    Function.Injective (fun p : DerivativeWord2 j × DerivativeWord2 L => Fin.append p.1 p.2) := by
  intro p q h
  have h1 : p.1 = q.1 := by
    funext i
    have := congrFun h (Fin.castAdd L i)
    simpa using this
  have h2 : p.2 = q.2 := by
    funext i
    have := congrFun h (Fin.natAdd j i)
    simpa using this
  exact Prod.ext h1 h2

theorem kdShift_derivativeNormSq {k L : ℕ} {u : TorusHk (k + L) E} {a : Vec 2 → E}
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) (β : DerivativeWord2 j) :
    derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩
      = ∑ γ : DerivativeWord2 L,
          ‖u.val ⟨⟨j + L, Nat.lt_succ_of_le (by omega)⟩, Fin.append β γ⟩‖ ^ 2 := by
  unfold derivativeNormSq
  refine Finset.sum_congr rfl fun γ _ => ?_
  have h : (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨⟨L, Nat.lt_succ_self L⟩, γ⟩
      = u.val ⟨⟨j + L, Nat.lt_succ_of_le (by omega)⟩, Fin.append β γ⟩ :=
    Lp.ext (kdShift_jet_ae hu hj β le_rfl γ)
  simp only [h]

/-- The shifts of all words of length `j` have total squared jet norm at most the squared jet norm
of `u` at order `j + L`. -/
theorem kdShift_sum_le {k L : ℕ} {u : TorusHk (k + L) E} {a : Vec 2 → E}
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) :
    ∑ β : DerivativeWord2 j,
        derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩
      ≤ derivativeNormSq u.val ⟨j + L, Nat.lt_succ_of_le (by omega)⟩ := by
  simp only [kdShift_derivativeNormSq hu hj]
  rw [← Fintype.sum_prod_type']
  unfold derivativeNormSq
  set F : DerivativeWord2 (j + L) → ℝ := fun δ =>
    ‖u.val ⟨⟨j + L, Nat.lt_succ_of_le (by omega)⟩, δ⟩‖ ^ 2 with hF
  have : ∑ p : DerivativeWord2 j × DerivativeWord2 L, F (Fin.append p.1 p.2) =
      ∑ δ ∈ Finset.univ.image (fun p : DerivativeWord2 j × DerivativeWord2 L =>
        Fin.append p.1 p.2), F δ :=
    (Finset.sum_image (fun p _ q _ h => kd_append_injective j L h)).symm
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => sq_nonneg _)

end AVRegularity.Construction.KernelDefect
end
end

section
/-! **Defect at one time.** The realization of the defect of a classical
representative is `U - S(t) U` for the truncation `U` of `u` to order `k`; its jets are
`(I - S(t))` applied to the jets of `u`. The bound is the one-jet moment bound for the shifted
jets, weighted by the factorials. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.KernelDefect

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The weak realization of the defect `(I - S(t))` of the order-`k` truncation of `u`. -/
def kdRealization (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀) (S : KernelSpec) (t : ℝ) {k L : ℕ}
    (u : TorusHk (k + L) E) : TorusHk k E :=
  truncateTorusHk (Nat.le_add_right k L) u -
    AVRegularity.Analysis.Convolution.pairedTorusMomentSmoothing S.width (S.H₁ t) (S.H₂ t) hφ
      S.order (truncateTorusHk (Nat.le_add_right k L) u)

omit [FiniteDimensional ℝ E] in
theorem kdRealization_val {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀) (S : KernelSpec) (t : ℝ)
    {k L : ℕ} (u : TorusHk (k + L) E) {j : ℕ} (hj : j ≤ k) (β : DerivativeWord2 j) :
    (kdRealization φ₀ hφ S t u).val ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩ =
      u.val ⟨⟨j, Nat.lt_succ_of_le (by omega)⟩, β⟩ -
        S.op φ₀ hφ t (u.val ⟨⟨j, Nat.lt_succ_of_le (by omega)⟩, β⟩) := rfl

theorem kd_factorial_shift (j k L : ℕ) (hj : j ≤ k) :
    ((j + L).factorial : ℝ) * k.factorial ≤ ((k + L).factorial : ℝ) * j.factorial := by
  have h1 := Nat.factorial_mul_ascFactorial j L
  have h2 := Nat.factorial_mul_ascFactorial k L
  have h3 : (j + 1).ascFactorial L ≤ (k + 1).ascFactorial L := Nat.ascFactorial_le L (by omega)
  have : (j + L).factorial * k.factorial ≤ (k + L).factorial * j.factorial := by
    rw [← h1, ← h2]
    calc j.factorial * (j + 1).ascFactorial L * k.factorial
        = (j + 1).ascFactorial L * (j.factorial * k.factorial) := by ring
      _ ≤ (k + 1).ascFactorial L * (j.factorial * k.factorial) := Nat.mul_le_mul_right _ h3
      _ = k.factorial * (k + 1).ascFactorial L * j.factorial := by ring
  exact_mod_cast this

theorem kd_weight_shift {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) {j k : ℕ} (L : ℕ) (hj : j ≤ k) :
    factorialWeight ρ j * r ^ (2 * L) ≤
      (((k + L).factorial : ℝ) / k.factorial) ^ 2 * (r / ρ) ^ (2 * L) *
        factorialWeight ρ (j + L) := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hjf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hjL : (0 : ℝ) < (j + L).factorial := by exact_mod_cast Nat.factorial_pos _
  have key := kd_factorial_shift j k L hj
  have key' : ((j + L).factorial : ℝ) / j.factorial ≤ ((k + L).factorial : ℝ) / k.factorial := by
    rw [div_le_div_iff₀ hjf hk]; exact key
  have key2 : (((j + L).factorial : ℝ) / j.factorial) ^ 2 ≤
      (((k + L).factorial : ℝ) / k.factorial) ^ 2 :=
    pow_le_pow_left₀ (by positivity) key' 2
  unfold factorialWeight
  have hp : ρ ^ (2 * (j + L)) = ρ ^ (2 * j) * ρ ^ (2 * L) := by rw [← pow_add]; ring_nf
  have hρL : (0 : ℝ) < ρ ^ (2 * L) := by positivity
  have hρj : (0 : ℝ) < ρ ^ (2 * j) := by positivity
  have hX : 0 ≤ ρ ^ (2 * j) * r ^ (2 * L) := by positivity
  have e1 : (((k + L).factorial : ℝ) / k.factorial) ^ 2 * (r / ρ) ^ (2 * L) *
        (ρ ^ (2 * (j + L)) / ((j + L).factorial : ℝ) ^ 2) =
      (ρ ^ (2 * j) * r ^ (2 * L)) * ((((k + L).factorial : ℝ) / k.factorial) ^ 2 /
        ((j + L).factorial : ℝ) ^ 2) := by
    rw [hp, div_pow r ρ]
    field_simp
  have e2 : ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2 * r ^ (2 * L) =
      (ρ ^ (2 * j) * r ^ (2 * L)) * (1 / (j.factorial : ℝ) ^ 2) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ hX
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : ((j + L).factorial : ℝ) ^ 2 ≤ (((k + L).factorial : ℝ) / k.factorial) ^ 2 *
      (j.factorial : ℝ) ^ 2 := by
    have h := key2
    rw [div_pow, div_le_iff₀ (by positivity)] at h
    rw [div_pow]
    calc _ ≤ _ := h
      _ = _ := by ring
  linarith

theorem kdRealization_isClassicalRep {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (S : KernelSpec) (t : ℝ) {k L : ℕ} (u : TorusHk (k + L) E) (a : Vec 2 → E)
    (hu : IsClassicalRep u a (k + L)) :
    IsClassicalRep (kdRealization φ₀ hφ S t u) (fun y => a y - S.applyClassical φ₀ t a y) k := by
  have hU := Construction.Preservation.FullLift.classicalRep_truncate (Nat.le_add_right k L)
    le_rfl u a (CycleComparison.Reconstruction.isClassicalRep_of_le hu (Nat.le_add_right k L))
  have hP := Construction.Preservation.Residual.kernel_readout_kernel_classical_rep hφ hd
    (kd_hasCompactSupport hsupp) S t _ a hU
  exact CycleComparison.Reconstruction.isClassicalRep_sub hU hP

/-- The squared jet norm of the realization at level `j`. -/
theorem kdRealization_jet_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (n : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t : ℝ) (hn : S.order = n) (hL : L + 1 ≤ 2 * (n : ℕ)) (hr : 0 < S.width)
    (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ) {k : ℕ} (u : TorusHk (k + L) E) (a : Vec 2 → E)
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) :
    derivativeNormSq (kdRealization φ₀ hφ S t u).val ⟨j, Nat.lt_succ_of_le hj⟩ ≤
      (kdMomentConst φ₀ n L Γ * S.width ^ L) ^ 2 *
        derivativeNormSq u.val ⟨j + L, Nat.lt_succ_of_le (by omega)⟩ := by
  unfold derivativeNormSq
  calc ∑ β : DerivativeWord2 j, ‖(kdRealization φ₀ hφ S t u).val ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩‖ ^ 2
      ≤ ∑ β : DerivativeWord2 j, (kdMomentConst φ₀ n L Γ * S.width ^ L) ^ 2 *
          derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩ := by
        refine Finset.sum_le_sum fun β _ => ?_
        have hb := kd_moment_bound hφ hd hnonneg hmass hsupp L n Γ S t hn hL hr h1 h2
          (kdShift a hu.2.1 hu.2.2.1 hj β)
        rw [kdShift_value_ae hu hj β] at hb
        rw [kdRealization_val hφ S t u hj β]
        have hd0 := derivativeNormSq_nonneg (kdShift a hu.2.1 hu.2.2.1 hj β).val
          ⟨L, Nat.lt_succ_self L⟩
        calc _ ≤ (kdMomentConst φ₀ n L Γ * S.width ^ L *
              Real.sqrt (derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val
                ⟨L, Nat.lt_succ_self L⟩)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = _ := by rw [mul_pow, Real.sq_sqrt hd0]
    _ = (kdMomentConst φ₀ n L Γ * S.width ^ L) ^ 2 * ∑ β : DerivativeWord2 j,
          derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩ := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (kdShift_sum_le hu hj) (sq_nonneg _)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem kd_shift_sum_le {k L : ℕ} (ρ : ℝ) (D : JetL2 (volume.restrict AVenhance.unitCube) (k + L) E) :
    ∑ j : Fin (k + 1), factorialWeight ρ (j.val + L) *
        derivativeNormSq D ⟨j.val + L, by omega⟩ ≤ factorialNormSq ρ D := by
  unfold factorialNormSq
  let g : Fin (k + 1) → Fin (k + L + 1) := fun j => ⟨j.val + L, by omega⟩
  have hg : Function.Injective g := fun a b h => by
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [g] at this
    omega
  have := Finset.sum_image (s := (Finset.univ : Finset (Fin (k + 1))))
    (f := fun m : Fin (k + L + 1) => factorialWeight ρ m.val * derivativeNormSq D m)
    (g := g) (fun a _ b _ h => hg h)
  refine le_trans (le_of_eq this.symm) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun m _ _ => mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _))

theorem kdRealization_normSq_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (k L : ℕ) (n : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t ρ : ℝ) (hn : S.order = n) (hL : L + 1 ≤ 2 * (n : ℕ)) (hr : 0 < S.width)
    (hrρ : S.width ≤ ρ) (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ)
    (u : TorusHk (k + L) E) (a : Vec 2 → E) (hu : IsClassicalRep u a (k + L)) :
    factorialNormSq ρ (kdRealization φ₀ hφ S t u).val ≤
      (kdMomentConst φ₀ n L Γ * (((k + L).factorial : ℝ) / k.factorial) *
        (S.width / ρ) ^ L) ^ 2 * factorialNormSq ρ u.val := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  set c0 := kdMomentConst φ₀ n L Γ with hc0
  set Q : ℝ := ((k + L).factorial : ℝ) / k.factorial with hQ
  set r := S.width with hrdef
  unfold factorialNormSq
  calc ∑ j : Fin (k + 1), factorialWeight ρ j.val *
        derivativeNormSq (kdRealization φ₀ hφ S t u).val j
      ≤ ∑ j : Fin (k + 1), factorialWeight ρ j.val *
          ((c0 * r ^ L) ^ 2 * derivativeNormSq u.val ⟨j.val + L, by omega⟩) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left
          (kdRealization_jet_le hφ hd hnonneg hmass hsupp L n Γ S t hn hL hr h1 h2 u a hu
            (Nat.lt_succ_iff.mp j.isLt)) (factorialWeight_nonneg _ _)
    _ ≤ ∑ j : Fin (k + 1), (c0 * Q * (r / ρ) ^ L) ^ 2 *
          (factorialWeight ρ (j.val + L) * derivativeNormSq u.val ⟨j.val + L, by omega⟩) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hw := kd_weight_shift (r := r) hρ hr.le L (Nat.lt_succ_iff.mp j.isLt)
        have hD := derivativeNormSq_nonneg u.val ⟨j.val + L, by omega⟩
        have e : (c0 * r ^ L) ^ 2 = c0 ^ 2 * r ^ (2 * L) := by
          rw [mul_pow, ← pow_mul, mul_comm L 2]
        have e2 : (c0 * Q * (r / ρ) ^ L) ^ 2 = c0 ^ 2 * (Q ^ 2 * (r / ρ) ^ (2 * L)) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm L 2]; ring
        calc _ = c0 ^ 2 * ((factorialWeight ρ j.val * r ^ (2 * L)) *
              derivativeNormSq u.val ⟨j.val + L, by omega⟩) := by rw [e]; ring
          _ ≤ c0 ^ 2 * ((Q ^ 2 * (r / ρ) ^ (2 * L) * factorialWeight ρ (j.val + L)) *
              derivativeNormSq u.val ⟨j.val + L, by omega⟩) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hD)
                (sq_nonneg _)
          _ = _ := by rw [e2]; ring
    _ = (c0 * Q * (r / ρ) ^ L) ^ 2 * ∑ j : Fin (k + 1), factorialWeight ρ (j.val + L) *
          derivativeNormSq u.val ⟨j.val + L, by omega⟩ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (kd_shift_sum_le ρ u.val) (sq_nonneg _)

theorem kdMomentConst_nonneg (φ₀ : Vec 2 → ℝ) (n : ℕ+) (L : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    0 ≤ kdMomentConst φ₀ n L Γ := by
  unfold kdMomentConst
  split_ifs
  · norm_num
  · have hM : 0 ≤ ∫ z : Vec 2, ‖momentKernel φ₀ n z‖ := integral_nonneg fun _ => norm_nonneg _
    positivity

/-- **Pointwise in time.** -/
theorem kernelDefect : KernelDefectStatement := by
  intro E _ _ _ _ _ _ φ₀ hφ hd hnonneg hmass hsupp k L n Γ
  refine ⟨kdMomentConst φ₀ n L |Γ| * (((k + L).factorial : ℝ) / k.factorial), ?_, ?_⟩
  · exact mul_nonneg (kdMomentConst_nonneg φ₀ n L (abs_nonneg Γ)) (by positivity)
  · intro S t ρ hn hadm hr hrρ u a hu
    obtain ⟨-, -, hH, hL⟩ := hadm
    rw [hn] at hL
    refine ⟨kdRealization φ₀ hφ S t u,
      kdRealization_isClassicalRep hφ hd hsupp S t u a hu, ?_⟩
    exact kdRealization_normSq_le hφ hd hnonneg hmass hsupp k L n |Γ| S t ρ hn hL hr hrρ
      ((hH t).1.trans (le_abs_self Γ)) ((hH t).2.1.trans (le_abs_self Γ)) u a hu

end AVRegularity.Construction.KernelDefect
end
end

section
/-! **Defect in `L²(I)`.** The realization `t ↦ (I - S(t)) U(t)` of the defect of
a trajectory is strongly measurable in time because the matrices `H_i` are Borel and the moving
average of a measurable `L²`-valued function is measurable; the squared norms are integrated
against the pointwise bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.KernelDefect

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The moving kernel applied to a strongly measurable trajectory is strongly measurable. -/
theorem kd_op_stronglyMeasurable_var (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (S : KernelSpec) (hH₁ : Measurable S.H₁) (hH₂ : Measurable S.H₂)
    (hκ : Measurable (momentKernel φ₀ S.order))
    (f : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun t => S.op φ₀ hφ₀ t (f t)) := by
  let inner : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) := fun t =>
    periodicComponentAverage (displacement S.width (S.H₂ t))
      (continuous_displacement S.width (S.H₂ t)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ₀ S.order) (f t)
  have hinner : StronglyMeasurable inner :=
    Construction.Preservation.FullLift.moving_periodic_average_stronglyMeasurable S.H₂ hH₂
      S.width (momentKernel φ₀ S.order) hκ (integrable_momentKernel hφ₀ S.order) f hf
  change StronglyMeasurable (fun t => periodicComponentAverage
    (displacement S.width (S.H₁ t)) (continuous_displacement S.width (S.H₁ t))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order) (inner t))
  exact Construction.Preservation.FullLift.moving_periodic_average_stronglyMeasurable S.H₁ hH₁
    S.width (momentKernel φ₀ S.order) hκ (integrable_momentKernel hφ₀ S.order) inner hinner

theorem kdRealization_stronglyMeasurable {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (S : KernelSpec) (hH₁ : Measurable S.H₁) (hH₂ : Measurable S.H₂) {k L : ℕ}
    (u : ℝ → TorusHk (k + L) E) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t => kdRealization φ₀ hφ S t (u t)) := by
  have hκ : Measurable (momentKernel φ₀ S.order) :=
    (contDiff_momentKernel (kd_hasCompactSupport hsupp) hd S.order).continuous.measurable
  apply KernelEnergy.torusCarrier_stronglyMeasurable_of_tests k
  intro φ
  have hg : StronglyMeasurable (fun t => CoupledEnergy.Galerkin.torusHkValueCLM (u t)) :=
    (CoupledEnergy.Galerkin.torusHkValueCLM (K := k + L) (E := E)).continuous.comp_stronglyMeasurable hu
  have hop := kd_op_stronglyMeasurable_var φ₀ hφ S hH₁ hH₂ hκ _ hg
  have hfun : (fun t => inner ℝ (CoupledEnergy.Galerkin.torusHkValueCLM
        (kdRealization φ₀ hφ S t (u t))) (CoupledEnergy.Galerkin.torusHkValueCLM φ)) =
      fun t => inner ℝ (CoupledEnergy.Galerkin.torusHkValueCLM (u t) -
        S.op φ₀ hφ t (CoupledEnergy.Galerkin.torusHkValueCLM (u t)))
        (CoupledEnergy.Galerkin.torusHkValueCLM φ) := by
    funext t; rfl
  rw [hfun]
  exact (hg.sub hop).inner stronglyMeasurable_const

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem kd_continuous_factorialNormSq {K : ℕ} (ρ : ℝ) :
    Continuous (fun D : JetL2 (volume.restrict AVenhance.unitCube) K E => factorialNormSq ρ D) := by
  unfold factorialNormSq derivativeNormSq
  fun_prop

end AVRegularity.Construction.KernelDefect
end
end

section
/-! **The kernel defect with a constant uniform in the order of the kernel.**

The jet bound of the realization `kdRealization` of the defect, with the moment constant of any
order `m ≤ S.order` that has `L + 1 ≤ 2m` (`kdRealization_jet_le_of_order_le`;
`kdRealization_jet_le` is the case `m = S.order`). The proof is that of `kdRealization_jet_le`
with `kd_moment_bound_of_order_le` in place of `kd_moment_bound`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution

namespace AVRegularity.Construction.KernelDefect

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The squared jet norm of the realization at level `j`, with the constant of a lower order. -/
theorem kdRealization_jet_le_of_order_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (m : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t : ℝ) (hm : m ≤ S.order) (hL : L + 1 ≤ 2 * (m : ℕ)) (hr : 0 < S.width)
    (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ) {k : ℕ} (u : TorusHk (k + L) E) (a : Vec 2 → E)
    (hu : IsClassicalRep u a (k + L)) {j : ℕ} (hj : j ≤ k) :
    derivativeNormSq (kdRealization φ₀ hφ S t u).val ⟨j, Nat.lt_succ_of_le hj⟩ ≤
      (kdMomentConst φ₀ m L Γ * S.width ^ L) ^ 2 *
        derivativeNormSq u.val ⟨j + L, Nat.lt_succ_of_le (by omega)⟩ := by
  unfold derivativeNormSq
  calc ∑ β : DerivativeWord2 j, ‖(kdRealization φ₀ hφ S t u).val ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩‖ ^ 2
      ≤ ∑ β : DerivativeWord2 j, (kdMomentConst φ₀ m L Γ * S.width ^ L) ^ 2 *
          derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩ := by
        refine Finset.sum_le_sum fun β _ => ?_
        have hb := kd_moment_bound_of_order_le hφ hd hnonneg hmass hsupp L m Γ S t hm hL hr h1 h2
          (kdShift a hu.2.1 hu.2.2.1 hj β)
        rw [kdShift_value_ae hu hj β] at hb
        rw [kdRealization_val hφ S t u hj β]
        have hd0 := derivativeNormSq_nonneg (kdShift a hu.2.1 hu.2.2.1 hj β).val
          ⟨L, Nat.lt_succ_self L⟩
        calc _ ≤ (kdMomentConst φ₀ m L Γ * S.width ^ L *
              Real.sqrt (derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val
                ⟨L, Nat.lt_succ_self L⟩)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = _ := by rw [mul_pow, Real.sq_sqrt hd0]
    _ = (kdMomentConst φ₀ m L Γ * S.width ^ L) ^ 2 * ∑ β : DerivativeWord2 j,
          derivativeNormSq (kdShift a hu.2.1 hu.2.2.1 hj β).val ⟨L, Nat.lt_succ_self L⟩ := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (kdShift_sum_le hu hj) (sq_nonneg _)

theorem kdUniformMomentConst_nonneg (φ₀ : Vec 2 → ℝ) (L : ℕ) {Γ : ℝ} (hΓ : 0 ≤ Γ) :
    0 ≤ kdUniformMomentConst φ₀ L Γ :=
  kdMomentConst_nonneg φ₀ (kdUniformOrder L) L hΓ

end AVRegularity.Construction.KernelDefect
end
end
end
