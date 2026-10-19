-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Gluing weak identities with a partition of unity in time** (the gluing identity). If each
field `T_k` satisfies, on its window `[α_k, β_k] ∩ [A, B]`, the tested identity
`d/dt ∫⟪T_k, φ⟫ = -∫⟪b · ∇T_k, φ⟫ - ν ∫ ∑_j ⟪∂_j T_k, ∂_j φ⟫ + r_k`,
and `ϖ_k` is a `C¹` weight supported in `[α_k, β_k]`, then the glued field `û = ∑_k ϖ_k T_k`
satisfies on `[A, B]`
`d/dt ∫⟪û, φ⟫ = -∫⟪b · ∇û, φ⟫ - ν ∫ ∑_j ⟪∂_j û, ∂_j φ⟫ + ∑_k (ϖ_k' ∫⟪T_k, φ⟫ + ϖ_k r_k)`
(`glued_weak`). Terms of a vanishing weight need no regularity of `T_k`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cell integral of a weighted sum, with integrability required only for nonzero
weights. -/
theorem integral_weighted_sum {κ : Type*} (S : Finset κ) (w : κ → ℝ) (f : κ → Vec 2 → ℝ)
    (hf : ∀ k ∈ S, w k ≠ 0 → Integrable (f k) (volume.restrict AVenhance.unitCube)) :
    ∫ x in AVenhance.unitCube, ∑ k ∈ S, w k * f k x =
      ∑ k ∈ S, w k * ∫ x in AVenhance.unitCube, f k x := by
  have hint : ∀ k ∈ S, Integrable (fun x => w k * f k x) (volume.restrict AVenhance.unitCube) :=
    fun k hk => by
      by_cases hw : w k = 0
      · simp only [hw, zero_mul]
        exact integrable_zero _ _ _
      · exact (hf k hk hw).const_mul _
  rw [integral_finsetSum S hint]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- The derivative of a weighted sum, with differentiability required only for nonzero
weights. -/
theorem fderiv_weighted_sum_apply {κ : Type*} (S : Finset κ) (w : κ → ℝ) (T : κ → Vec 2 → E)
    (x e : Vec 2) (hT : ∀ k ∈ S, w k ≠ 0 → DifferentiableAt ℝ (T k) x) :
    fderiv ℝ (fun x' => ∑ k ∈ S, w k • T k x') x e = ∑ k ∈ S, w k • fderiv ℝ (T k) x e := by
  have hd : ∀ k ∈ S, DifferentiableAt ℝ (fun x' => w k • T k x') x := fun k hk => by
    by_cases hw : w k = 0
    · simp only [hw, zero_smul]
      exact differentiableAt_const _
    · exact (hT k hk hw).const_smul (w k)
  rw [fderiv_fun_sum hd]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hw : w k = 0
  · simp [hw]
  · rw [fderiv_fun_const_smul (hT k hk hw)]
    rfl

/-- **Gluing tested weak identities with a `C¹` partition in time.** -/
theorem glued_weak {κ : Type*} (S : Finset κ) {A B : ℝ} (hAB : A ≤ B) (ϖ : κ → ℝ → ℝ)
    (α β : κ → ℝ) (hϖ : ∀ k ∈ S, ContDiff ℝ 1 (ϖ k))
    (hsupp : ∀ k ∈ S, ∀ t, ϖ k t ≠ 0 → t ∈ Icc (α k) (β k))
    (T : κ → ℝ → Vec 2 → E) (bv : ℝ → Vec 2 → Vec 2) (ν : ℝ) (r : κ → ℝ → ℝ)
    (φt : Vec 2 → E) (hφt : ContDiff ℝ 1 φt)
    (hT : ∀ k ∈ S, ∀ t ∈ Icc (max (α k) A) (min (β k) B), ContDiff ℝ 1 (T k t))
    (hbv : ∀ t ∈ Icc A B, Continuous (bv t))
    (hprim : ∀ k ∈ S, IsPrimOn (max (α k) A) (min (β k) B)
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ (T k t x) (φt x))
      (fun t => -(∫ x in AVenhance.unitCube,
          inner ℝ (∑ j, bv t x j • fderiv ℝ (T k t) x (basisVec j)) (φt x)) -
        ν * (∫ x in AVenhance.unitCube, ∑ j,
          inner ℝ (fderiv ℝ (T k t) x (basisVec j)) (fderiv ℝ φt x (basisVec j))) + r k t)) :
    IsPrimOn A B
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ (∑ k ∈ S, ϖ k t • T k t x) (φt x))
      (fun t => -(∫ x in AVenhance.unitCube, inner ℝ (∑ j, bv t x j •
          fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j)) (φt x)) -
        ν * (∫ x in AVenhance.unitCube, ∑ j,
          inner ℝ (fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j))
            (fderiv ℝ φt x (basisVec j))) +
        ∑ k ∈ S, (deriv (ϖ k) t * (∫ x in AVenhance.unitCube, inner ℝ (T k t x) (φt x)) +
          ϖ k t * r k t)) := by
  classical
  have hmem : ∀ k ∈ S, ∀ t ∈ Icc A B, ϖ k t ≠ 0 → t ∈ Icc (max (α k) A) (min (β k) B) :=
    fun k hk t ht hw => ⟨max_le (hsupp k hk t hw).1 ht.1, le_min (hsupp k hk t hw).2 ht.2⟩
  have hφc := hφt.continuous
  have hdφ : ∀ j : Fin 2, Continuous (fun x => fderiv ℝ φt x (basisVec j)) := fun j =>
    (hφt.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdT : ∀ k ∈ S, ∀ t ∈ Icc (max (α k) A) (min (β k) B), ∀ j : Fin 2,
      Continuous (fun x => fderiv ℝ (T k t) x (basisVec j)) := fun k hk t ht j =>
    ((hT k hk t ht).continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine (IsPrimOn.glue S hAB ϖ α β _ _ hϖ hsupp hprim).congr hAB (fun t ht => ?_)
    (fun t ht => ?_)
  · -- the tested glued field
    have hpt : ∀ x, inner ℝ (∑ k ∈ S, ϖ k t • T k t x) (φt x) =
        ∑ k ∈ S, ϖ k t * inner ℝ (T k t x) (φt x) := fun x => by
      simp only [sum_inner, real_inner_smul_left]
    simp only [hpt, smul_eq_mul]
    refine (integral_weighted_sum S (fun k => ϖ k t) _ fun k hk hw => ?_).symm
    exact CoupledEnergy.Galerkin.continuous_cell_integrable _
      ((hT k hk t (hmem k hk t ht hw)).continuous.inner hφc)
  · -- the density: drift and diffusion of the glued field
    have hfd : ∀ x (j : Fin 2), fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j) =
        ∑ k ∈ S, ϖ k t • fderiv ℝ (T k t) x (basisVec j) := fun x j =>
      fderiv_weighted_sum_apply S (fun k => ϖ k t) (fun k => T k t) x (basisVec j)
        fun k hk hw => ((hT k hk t (hmem k hk t ht hw)).differentiable one_ne_zero) x
    have hD : ∫ x in AVenhance.unitCube, inner ℝ (∑ j, bv t x j •
          fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j)) (φt x) =
        ∑ k ∈ S, ϖ k t * ∫ x in AVenhance.unitCube,
          inner ℝ (∑ j, bv t x j • fderiv ℝ (T k t) x (basisVec j)) (φt x) := by
      have hpt : ∀ x, inner ℝ (∑ j, bv t x j •
          fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j)) (φt x) =
          ∑ k ∈ S, ϖ k t *
            inner ℝ (∑ j, bv t x j • fderiv ℝ (T k t) x (basisVec j)) (φt x) := fun x => by
        simp only [hfd, Finset.smul_sum]
        rw [Finset.sum_comm]
        simp only [smul_comm (bv t x _) (ϖ _ t), ← Finset.smul_sum, sum_inner,
          real_inner_smul_left]
      simp only [hpt]
      refine integral_weighted_sum S (fun k => ϖ k t) _ fun k hk hw => ?_
      have hk' := hmem k hk t ht hw
      exact CoupledEnergy.Galerkin.continuous_cell_integrable _
        ((continuous_finsetSum _ fun j _ =>
          ((continuous_apply j).comp (hbv t ht)).smul (hdT k hk t hk' j)).inner hφc)
    have hL : ∫ x in AVenhance.unitCube, ∑ j,
          inner ℝ (fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x (basisVec j))
            (fderiv ℝ φt x (basisVec j)) =
        ∑ k ∈ S, ϖ k t * ∫ x in AVenhance.unitCube, ∑ j,
          inner ℝ (fderiv ℝ (T k t) x (basisVec j)) (fderiv ℝ φt x (basisVec j)) := by
      have hpt : ∀ x, ∑ j, inner ℝ (fderiv ℝ (fun x' => ∑ k ∈ S, ϖ k t • T k t x') x
            (basisVec j)) (fderiv ℝ φt x (basisVec j)) =
          ∑ k ∈ S, ϖ k t * ∑ j,
            inner ℝ (fderiv ℝ (T k t) x (basisVec j)) (fderiv ℝ φt x (basisVec j)) :=
        fun x => by
          simp only [hfd, sum_inner, real_inner_smul_left, Finset.mul_sum]
          exact Finset.sum_comm
      simp only [hpt]
      refine integral_weighted_sum S (fun k => ϖ k t) _ fun k hk hw => ?_
      have hk' := hmem k hk t ht hw
      exact CoupledEnergy.Galerkin.continuous_cell_integrable _
        (continuous_finsetSum _ fun j _ => (hdT k hk t hk' j).inner (hdφ j))
    rw [hD, hL]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The mass-weighted norm of the joint model datum.** The coarse family of the comparison window
is started at the joint model datum `𝑷f`, where
`(𝑷x)_v = P_diag x_v + ∑_{h=1}^H ∑_u P^{(h)}_{vu} x_u` (`jointOperator`) obeys the model clause
`IsJointModel` of the joint preparation:
`|P_diag g|_{ρ_m,M_out} ≤ C ‖g‖₂` and `|P^{(h)}_{vu} g|_{ρ_m,M_out} ≤ C (A^h)_{vu} ‖g‖₂`.

For an `L²` input `x` and an order `N ≤ M_out`, the truncation to order `N` of `𝑷x` has
mass-weighted factorial norm (`massNormSq`, radius `ρ`, all slots `N`)
`‖𝑷x‖_{ρ,N;π} ≤ jointModelConst C S H N (ρ/ρ_m) · (∑_u π_u⁻¹ ‖x_u‖₂²)^{1/2}`
(`jointModel_massNormSq_le_input`), with
`jointModelConst C S H N r = max(1, r)^N · max(C, 0) · (1 + ∑_{h=1}^H S^h)`, where `S` bounds the
row and column sums of the mass-conjugated matrix `√(π_u/π_v) A_{vu}`. The radius change costs
`max(1, ρ/ρ_m)^N` (`torusHkNorm_radius_conversion`), lowering the order from `M_out` to `N` is free
(`torusHkNorm_le_of_order`), the blocks are bounded by the model clause, and the degree-`h` part
is a mass-weighted Schur bound with the powers `A^h`, whose conjugated row and column sums are at
most `S^h` (`massL2_jointMajorant_le`). For the prepared datum (`x_u` the order-zero truncation of
`f_u`), `‖x_u‖₂ ≤ |f_u|_{ρold,K_u} ≤ F_u` (`jointModel_massNormSq_le`). The constant `C` of the
model clause enters through `max(C, 0)`: the clause does not fix its sign. -/

/-! ### The mass-weighted `ℓ²` norm of a real family -/

/-- The mass-weighted `ℓ²` norm `(∑_v π_v⁻¹ y_v²)^{1/2}` of a real family. -/
def massL2 {ι : Type*} [Fintype ι] (π y : ι → ℝ) : ℝ :=
  Real.sqrt (∑ v, (π v)⁻¹ * y v ^ 2)

/-- The vector `(π_v^{-1/2} y_v)_v` of `ℓ²`, whose norm is `massL2 π y`. -/
def massVec {ι : Type*} (π y : ι → ℝ) : PiLp 2 (fun _ : ι => ℝ) :=
  WithLp.toLp 2 (fun v => Real.sqrt ((π v)⁻¹) * y v)

theorem massL2_eq_norm {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (y : ι → ℝ) : massL2 π y = ‖massVec π y‖ := by
  unfold massL2
  rw [PiLp.norm_eq_of_L2]
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun v _ => ?_)
  change (π v)⁻¹ * y v ^ 2 = ‖Real.sqrt ((π v)⁻¹) * y v‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (inv_nonneg.mpr (hπ v).le)]

/-- Minkowski's inequality for the mass-weighted `ℓ²` norm. -/
theorem massL2_add_le {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (y z : ι → ℝ) : massL2 π (y + z) ≤ massL2 π y + massL2 π z := by
  have e : massVec π (y + z) = massVec π y + massVec π z := by
    refine PiLp.ext fun v => ?_
    change Real.sqrt ((π v)⁻¹) * (y v + z v) =
      Real.sqrt ((π v)⁻¹) * y v + Real.sqrt ((π v)⁻¹) * z v
    ring
  rw [massL2_eq_norm π hπ (y + z), massL2_eq_norm π hπ y, massL2_eq_norm π hπ z, e]
  exact norm_add_le _ _

theorem massL2_zero {ι : Type*} [Fintype ι] (π : ι → ℝ) : massL2 π 0 = 0 := by
  have h0 : ∀ v, (π v)⁻¹ * (0 : ι → ℝ) v ^ 2 = 0 := fun v => by simp
  unfold massL2
  rw [Finset.sum_congr rfl fun v _ => h0 v, Finset.sum_const_zero, Real.sqrt_zero]

/-- Minkowski's inequality for a finite sum of families. -/
theorem massL2_add_sum_le {ι α : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (y : ι → ℝ) (s : Finset α) (e : α → ι → ℝ) :
    massL2 π (fun v => y v + ∑ i ∈ s, e i v) ≤ massL2 π y + ∑ i ∈ s, massL2 π (e i) := by
  have hfun : (fun v => y v + ∑ i ∈ s, e i v) = y + ∑ i ∈ s, e i := by
    funext v
    rw [Pi.add_apply, Finset.sum_apply]
  refine (congrArg (massL2 π) hfun).trans_le ?_
  exact (massL2_add_le π hπ y _).trans (add_le_add le_rfl
    (Finset.le_sum_of_subadditive (massL2 π) (massL2_zero π).le (massL2_add_le π hπ) s e))

theorem massL2_mono {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    {y z : ι → ℝ} (hy : ∀ v, 0 ≤ y v) (hyz : ∀ v, y v ≤ z v) : massL2 π y ≤ massL2 π z := by
  unfold massL2
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hy v) (hyz v) 2) (inv_nonneg.mpr (hπ v).le))

theorem massL2_const_mul {ι : Type*} [Fintype ι] (π : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (y : ι → ℝ) : massL2 π (fun v => c * y v) = c * massL2 π y := by
  unfold massL2
  have e : (∑ v, (π v)⁻¹ * (c * y v) ^ 2) = c ^ 2 * ∑ v, (π v)⁻¹ * y v ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **Mass-weighted Schur test.** A nonnegative matrix whose mass-conjugated matrix
`√(π_u/π_v) B_{vu}` has row and column sums at most `θ` has norm at most `θ` on nonnegative families
in the mass-weighted `ℓ²` norm. -/
theorem massL2_matrix_le {ι : Type*} [Fintype ι] (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (B : Matrix ι ι ℝ) (hB : ∀ v u, 0 ≤ B v u) {θ : ℝ} (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * B v u ≤ θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * B v u ≤ θ) {y : ι → ℝ} (hy : ∀ u, 0 ≤ y u) :
    massL2 π (fun v => ∑ u, B v u * y u) ≤ θ * massL2 π y := by
  have hbound : ∀ v, 0 ≤ (∑ u, B v u * y u) / Real.sqrt (π v) ∧
      (∑ u, B v u * y u) / Real.sqrt (π v) ≤
        1 * ∑ u, (Real.sqrt (π u / π v) * B v u) * (y u / Real.sqrt (π u)) := by
    intro v
    refine ⟨div_nonneg (Finset.sum_nonneg fun u _ => mul_nonneg (hB v u) (hy u))
      (Real.sqrt_nonneg _), ?_⟩
    rw [one_mul, Finset.sum_div]
    refine le_of_eq (Finset.sum_congr rfl fun u _ => ?_)
    have e := CycleJointProofs.mass_normalized_block_bound_identity π hπ v u 1 (B v u) (y u)
    simpa only [one_mul] using e
  have hs := KernelEnergy.finiteRootSchur (fun v u => Real.sqrt (π u / π v) * B v u)
    (fun u => y u / Real.sqrt (π u)) (fun v => (∑ u, B v u * y u) / Real.sqrt (π v)) 1 θ
    one_pos (fun v u => mul_nonneg (Real.sqrt_nonneg _) (hB v u)) hrow hcol hbound
  simp only [one_mul, CycleJointProofs.mass_normalized_square π hπ] at hs
  unfold massL2
  calc Real.sqrt (∑ v, (π v)⁻¹ * (∑ u, B v u * y u) ^ 2)
      ≤ Real.sqrt (θ ^ 2 * ∑ u, (π u)⁻¹ * y u ^ 2) := Real.sqrt_le_sqrt hs
    _ = θ * Real.sqrt (∑ u, (π u)⁻¹ * y u ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ]

/-! ### The scalar majorant of the joint operator -/

/-- The scalar majorant `b_v + ∑_{h'=1}^H ∑_u (A^{h'})_{vu} b_u` of the joint operator. -/
def jointMajorant {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (H : ℕ)
    (b : ι → ℝ) (v : ι) : ℝ :=
  b v + ∑ h' ∈ Finset.Icc 1 H, ∑ u, (A ^ h') v u * b u

/-- The mass-weighted norm of the majorant: Minkowski over the degrees and the Schur test for
every power `A^{h'}` (conjugated row and column sums at most `S^{h'}`). -/
theorem massL2_jointMajorant_le {ι : Type*} [Fintype ι] [DecidableEq ι] (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) {S : ℝ} (hS : 0 ≤ S)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ S) (H : ℕ) {b : ι → ℝ}
    (hb : ∀ u, 0 ≤ b u) :
    massL2 π (jointMajorant A H b) ≤ (1 + ∑ h' ∈ Finset.Icc 1 H, S ^ h') * massL2 π b := by
  calc massL2 π (jointMajorant A H b)
      ≤ massL2 π b + ∑ h' ∈ Finset.Icc 1 H, massL2 π (fun v => ∑ u, (A ^ h') v u * b u) :=
        massL2_add_sum_le π hπ b (Finset.Icc 1 H) (fun h' v => ∑ u, (A ^ h') v u * b u)
    _ ≤ massL2 π b + ∑ h' ∈ Finset.Icc 1 H, S ^ h' * massL2 π b :=
        add_le_add le_rfl (Finset.sum_le_sum fun h' _ =>
          massL2_matrix_le π hπ (A ^ h') (CycleJointProofs.positiveMatrix_pow_nonneg A hA h')
            (pow_nonneg hS h') (CycleJointProofs.massMatrix_pow_row_sum π hπ A hA S hS hrow h')
            (CycleJointProofs.massMatrix_pow_col_sum π hπ A hA S hS hcol h') hb)
    _ = (1 + ∑ h' ∈ Finset.Icc 1 H, S ^ h') * massL2 π b := by
        rw [add_mul, one_mul, Finset.sum_mul]

/-! ### The factorial norm `torusHkNorm` as a seminorm -/

section Seminorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem torusHkNorm_add_le (ρ : ℝ) {K L : ℕ} (hKL : K ≤ L) (x y : TorusHk L E) :
    torusHkNorm ρ hKL (x + y) ≤ torusHkNorm ρ hKL x + torusHkNorm ρ hKL y :=
  (congrArg (fun U : TorusHk K E => Real.sqrt (factorialNormSq ρ U.val))
    (map_add (truncateTorusHk (E := E) hKL) x y)).trans_le (Coarse.sqrt_fNSq_torus_add_le ρ _ _)

theorem torusHkNorm_zero (ρ : ℝ) {K L : ℕ} (hKL : K ≤ L) :
    torusHkNorm ρ hKL (0 : TorusHk L E) = 0 :=
  (congrArg (fun U : TorusHk K E => Real.sqrt (factorialNormSq ρ U.val))
    (map_zero (truncateTorusHk (E := E) hKL))).trans (Coarse.sqrt_fNSq_torus_zero ρ)

theorem torusHkNorm_sum_le {α : Type*} (ρ : ℝ) {K L : ℕ} (hKL : K ≤ L) (s : Finset α)
    (g : α → TorusHk L E) :
    torusHkNorm ρ hKL (∑ i ∈ s, g i) ≤ ∑ i ∈ s, torusHkNorm ρ hKL (g i) :=
  Finset.le_sum_of_subadditive (torusHkNorm ρ hKL) (torusHkNorm_zero (E := E) ρ hKL).le
    (torusHkNorm_add_le (E := E) ρ hKL) s g

/-- Lowering the order of the factorial norm does not increase it. -/
theorem torusHkNorm_le_of_order (ρ : ℝ) {N M L : ℕ} (hN : N ≤ L) (hM : M ≤ L) (hNM : N ≤ M)
    (g : TorusHk L E) : torusHkNorm ρ hN g ≤ torusHkNorm ρ hM g :=
  Coarse.sqrt_fNSq_torus_truncate_le ρ hNM (truncateTorusHk hM g)

end Seminorm

/-- The mass-weighted factorial norm of a family truncated to the common order `N` is the
mass-weighted `ℓ²` norm of the componentwise factorial norms. -/
theorem sqrt_massNormSq_truncate_eq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ : ℝ) (π : ι → ℝ) {N : ℕ} {L : ι → ℕ} (hN : ∀ v, N ≤ L v)
    (g : ∀ v, TorusHk (L v) (h v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
        (fun v => (truncateTorusHk (hN v) (g v)).val)) =
      massL2 π (fun v => torusHkNorm ρ (hN v) (g v)) := by
  unfold massL2 massNormSq
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun v _ => ?_)
  change (π v)⁻¹ * factorialNormSq ρ (truncateTorusHk (hN v) (g v)).val =
    (π v)⁻¹ * Real.sqrt (factorialNormSq ρ (truncateTorusHk (hN v) (g v)).val) ^ 2
  rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _)]

/-- **Componentwise bound of the joint operator** from the model clause: at the model radius and
order, `|(𝑷x)_v|_{ρ_m,M_out} ≤ max(C, 0) (b_v + ∑_{h'=1}^H ∑_u (A^{h'})_{vu} b_u)` with
`b_u = ‖x_u‖₂`. -/
theorem torusHkNorm_jointOperator_le {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (K : ι → ℕ) (Mout H : ℕ) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (ρm C : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hPd : ∀ v f, torusHkNorm ρm (le_max_left Mout (K v)) (Pd v f) ≤
      C * torusHkNorm 1 (le_refl 0) f)
    (hPg : ∀ h', 1 ≤ h' → h' ≤ H → ∀ v u f,
      torusHkNorm ρm (le_max_left Mout (K v)) (Pg h' v u f) ≤
        C * (A ^ h') v u * torusHkNorm 1 (le_refl 0) f)
    (x : ∀ u, TorusHk 0 (h u)) (v : ι) :
    torusHkNorm ρm (le_max_left Mout (K v)) (jointOperator K Mout H Pd Pg x v) ≤
      max C 0 * jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u)) v := by
  have hb : ∀ u, 0 ≤ torusHkNorm 1 (le_refl 0) (x u) := fun u => Real.sqrt_nonneg _
  have hsub : torusHkNorm ρm (le_max_left Mout (K v)) (jointOperator K Mout H Pd Pg x v) ≤
      torusHkNorm ρm (le_max_left Mout (K v)) (Pd v (x v)) +
        ∑ h' ∈ Finset.Icc 1 H, ∑ u,
          torusHkNorm ρm (le_max_left Mout (K v)) (Pg h' v u (x u)) :=
    (torusHkNorm_add_le ρm (le_max_left Mout (K v)) (Pd v (x v))
      (∑ h' ∈ Finset.Icc 1 H, ∑ u, Pg h' v u (x u))).trans
      (add_le_add le_rfl ((torusHkNorm_sum_le ρm (le_max_left Mout (K v)) (Finset.Icc 1 H)
        (fun h' => ∑ u, Pg h' v u (x u))).trans
        (Finset.sum_le_sum fun h' _ => torusHkNorm_sum_le ρm (le_max_left Mout (K v))
          Finset.univ (fun u => Pg h' v u (x u)))))
  have hd : torusHkNorm ρm (le_max_left Mout (K v)) (Pd v (x v)) ≤
      max C 0 * torusHkNorm 1 (le_refl 0) (x v) :=
    (hPd v (x v)).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (hb v))
  have hg : ∀ h' ∈ Finset.Icc 1 H,
      ∑ u, torusHkNorm ρm (le_max_left Mout (K v)) (Pg h' v u (x u)) ≤
        ∑ u, max C 0 * ((A ^ h') v u * torusHkNorm 1 (le_refl 0) (x u)) := by
    intro h' hh'
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hh'
    refine Finset.sum_le_sum fun u _ => ?_
    exact (hPg h' h1 h2 v u (x u)).trans ((mul_assoc _ _ _).trans_le
      (mul_le_mul_of_nonneg_right (le_max_left C 0)
        (mul_nonneg (CycleJointProofs.positiveMatrix_pow_nonneg A hA h' v u) (hb u))))
  refine hsub.trans ((add_le_add hd (Finset.sum_le_sum hg)).trans (le_of_eq ?_))
  simp only [jointMajorant, mul_add, Finset.mul_sum]

/-- The constant of the joint-model bound,
`jointModelConst C S H N r = max(1, r)^N · max(C, 0) · (1 + ∑_{h'=1}^H S^{h'})`; it is used with
`r = ρ/ρ_m`, the ratio of the target radius to the model radius. -/
def jointModelConst (C S : ℝ) (H N : ℕ) (r : ℝ) : ℝ :=
  max 1 r ^ N * max C 0 * (1 + ∑ h' ∈ Finset.Icc 1 H, S ^ h')

theorem jointModelConst_nonneg (C : ℝ) {S : ℝ} (hS : 0 ≤ S) (H N : ℕ) (r : ℝ) :
    0 ≤ jointModelConst C S H N r := by
  unfold jointModelConst
  have h1 : (0 : ℝ) ≤ max 1 r := le_trans zero_le_one (le_max_left 1 r)
  exact mul_nonneg (mul_nonneg (pow_nonneg h1 N) (le_max_right C 0))
    (add_nonneg zero_le_one (Finset.sum_nonneg fun h' _ => pow_nonneg hS h'))

/-- **The mass-weighted norm of the joint model image of an `L²` family.** The truncation to an
order `N ≤ M_out` of `𝑷x` has mass-weighted factorial norm at radius `ρ` at most
`jointModelConst C S H N (ρ/ρ_m)` times the mass-weighted `L²` norm of `x`. -/
theorem jointModel_massNormSq_le_input {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Mout H : ℕ) (F : ChartedFamily ι h D P Ctx)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (Θ E Pacc ρm C CP : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hjm : IsJointModel π K Mout H F A Θ E Pacc ρm C CP Pd Pg) {S : ℝ}
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ S) (hS : 0 ≤ S) {ρ : ℝ} (hρ : 0 < ρ)
    (hρm : 0 < ρm) {N : ℕ} (hNM : N ≤ Mout) (hN : ∀ v, N ≤ max Mout (K v))
    (x : ∀ u, TorusHk 0 (h u)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
        (fun v => (truncateTorusHk (hN v) (jointOperator K Mout H Pd Pg x v)).val)) ≤
      jointModelConst C S H N (ρ / ρm) * massL2 π (fun u => torusHkNorm 1 (le_refl 0) (x u)) := by
  obtain ⟨-, -, hPd, hPg, -⟩ := hjm
  have ha1 : (1 : ℝ) ≤ max 1 (ρ / ρm) := le_max_left _ _
  have ha0 : (0 : ℝ) ≤ max 1 (ρ / ρm) := zero_le_one.trans ha1
  have hρa : ρ ≤ max 1 (ρ / ρm) * ρm := (div_le_iff₀ hρm).mp (le_max_right 1 (ρ / ρm))
  have hc : 0 ≤ max 1 (ρ / ρm) ^ N * max C 0 :=
    mul_nonneg (pow_nonneg ha0 N) (le_max_right C 0)
  have hb : ∀ u, 0 ≤ torusHkNorm 1 (le_refl 0) (x u) := fun u => Real.sqrt_nonneg _
  have hy : ∀ v, 0 ≤ torusHkNorm ρ (hN v) (jointOperator K Mout H Pd Pg x v) :=
    fun v => Real.sqrt_nonneg _
  have hv : ∀ v, torusHkNorm ρ (hN v) (jointOperator K Mout H Pd Pg x v) ≤
      (max 1 (ρ / ρm) ^ N * max C 0) *
        jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u)) v := by
    intro v
    calc torusHkNorm ρ (hN v) (jointOperator K Mout H Pd Pg x v)
        ≤ max 1 (ρ / ρm) ^ N * torusHkNorm ρm (hN v) (jointOperator K Mout H Pd Pg x v) :=
          CycleJointProofs.torusHkNorm_radius_conversion (hN v)
            (jointOperator K Mout H Pd Pg x v) hρ.le ha1 hρa
      _ ≤ max 1 (ρ / ρm) ^ N *
            torusHkNorm ρm (le_max_left Mout (K v)) (jointOperator K Mout H Pd Pg x v) :=
          mul_le_mul_of_nonneg_left
            (torusHkNorm_le_of_order ρm (hN v) (le_max_left Mout (K v)) hNM
              (jointOperator K Mout H Pd Pg x v))
            (pow_nonneg ha0 N)
      _ ≤ max 1 (ρ / ρm) ^ N *
            (max C 0 * jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u)) v) :=
          mul_le_mul_of_nonneg_left
            (torusHkNorm_jointOperator_le K Mout H A hA ρm C Pd Pg hPd hPg x v)
            (pow_nonneg ha0 N)
      _ = (max 1 (ρ / ρm) ^ N * max C 0) *
            jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u)) v :=
          (mul_assoc _ _ _).symm
  refine (sqrt_massNormSq_truncate_eq ρ π hN (jointOperator K Mout H Pd Pg x)).trans_le ?_
  calc massL2 π (fun v => torusHkNorm ρ (hN v) (jointOperator K Mout H Pd Pg x v))
      ≤ massL2 π (fun v => (max 1 (ρ / ρm) ^ N * max C 0) *
          jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u)) v) :=
        massL2_mono π hπ hy hv
    _ = (max 1 (ρ / ρm) ^ N * max C 0) *
          massL2 π (jointMajorant A H (fun u => torusHkNorm 1 (le_refl 0) (x u))) :=
        massL2_const_mul π hc _
    _ ≤ (max 1 (ρ / ρm) ^ N * max C 0) * ((1 + ∑ h' ∈ Finset.Icc 1 H, S ^ h') *
          massL2 π (fun u => torusHkNorm 1 (le_refl 0) (x u))) :=
        mul_le_mul_of_nonneg_left (massL2_jointMajorant_le π hπ A hA hS hrow hcol H hb) hc
    _ = jointModelConst C S H N (ρ / ρm) *
          massL2 π (fun u => torusHkNorm 1 (le_refl 0) (x u)) := by
        unfold jointModelConst
        ring

/-- **The mass-weighted norm of the joint model datum.** For the prepared datum `f` (the coarse
family of the comparison window starts at the order-`N` truncation of `𝑷f`, `N ≤ M_out`), with
`|f_v|_{ρold,K_v} ≤ F_v`:
`‖𝑷f‖_{ρ,N;π} ≤ jointModelConst C S H N (ρ/ρ_m) · (∑_v π_v⁻¹ F_v²)^{1/2}`. -/
theorem jointModel_massNormSq_le {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Mout H : ℕ) (F : ChartedFamily ι h D P Ctx)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (Θ E Pacc ρm C CP : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hjm : IsJointModel π K Mout H F A Θ E Pacc ρm C CP Pd Pg) {S : ℝ}
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ S) (hS : 0 ≤ S) {ρ : ℝ} (hρ : 0 < ρ)
    (hρm : 0 < ρm) {N : ℕ} (hNM : N ≤ Mout) (hN : ∀ v, N ≤ max Mout (K v))
    (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ) {ρold : ℝ}
    (hf : ∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
        (fun v => (truncateTorusHk (hN v) (jointOperator K Mout H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)).val)) ≤
      jointModelConst C S H N (ρ / ρm) * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) := by
  have hb : ∀ v, torusHkNorm 1 (le_refl 0) (truncateTorusHk (Nat.zero_le (K v)) (f v)) ≤
      Fv v := fun v =>
    ((CycleJointProofs.torusHkNorm_zero_input 1
      (truncateTorusHk (Nat.zero_le (K v)) (f v))).trans_le
      (CycleJointProofs.torusHk_value_le_modelNorm ρold (le_refl (K v)) (f v))).trans (hf v)
  have hy : ∀ v, 0 ≤ torusHkNorm 1 (le_refl 0) (truncateTorusHk (Nat.zero_le (K v)) (f v)) :=
    fun v => Real.sqrt_nonneg _
  exact (jointModel_massNormSq_le_input π hπ K Mout H F A hA Θ E Pacc ρm C CP Pd Pg hjm hrow
    hcol hS hρ hρm hNM hN (fun v => truncateTorusHk (Nat.zero_le _) (f v))).trans
    (mul_le_mul_of_nonneg_left (massL2_mono π hπ hy hb) (jointModelConst_nonneg C hS H N _))

/-- **The joint model bound at the model radius `c_j ρ`**: `jointModel_massNormSq_le` with
`ρ_m = c_j ρ`, whose constant is `jointModelConst C S H N c_j⁻¹`. -/
theorem jointModel_massNormSq_le_cj {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Mout H : ℕ) (F : ChartedFamily ι h D P Ctx)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (Θ E Pacc cj ρ C CP : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hjm : IsJointModel π K Mout H F A Θ E Pacc (cj * ρ) C CP Pd Pg) {S : ℝ}
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ S) (hS : 0 ≤ S) (hρ : 0 < ρ)
    (hcj : 0 < cj) {N : ℕ} (hNM : N ≤ Mout) (hN : ∀ v, N ≤ max Mout (K v))
    (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ) {ρold : ℝ}
    (hf : ∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
        (fun v => (truncateTorusHk (hN v) (jointOperator K Mout H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)).val)) ≤
      jointModelConst C S H N cj⁻¹ * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2) := by
  have hb := jointModel_massNormSq_le π hπ K Mout H F A hA Θ E Pacc (cj * ρ) C CP Pd Pg hjm hrow
    hcol hS hρ (mul_pos hcj hρ) hNM hN f Fv hf
  have hr : ρ / (cj * ρ) = cj⁻¹ := by
    rw [mul_comm cj, ← div_div, div_self hρ.ne', one_div]
  rwa [hr] at hb

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The physical edge coefficient is the transported label flux**.

Exact Piola transports flux by `(DΦR)∘Φ⁻¹` and scalars by composition; the divergence pairing
and the scalar norm are preserved, and chart jets pay the chain rule.

Let `χ` (chart, label `y` ↦ physical `x`) and `ψ` (label map) be smooth and mutually inverse,
`K = chartInvJacobian ψ`, `V` a smooth label field and `u = V ∘ ψ` the physical field.

* `transportedCoeff_flux`: for a label coefficient array `B` (orders `d`, words `I` of length
  `d - 1`, flux direction `i₀`) of maximal order `Dγ`, the transported array applied to the
  physical jets of `u` is the label flux read through `K`:
  `∑_{r<Dγ} ∑_{|A|=r} B̃_{r+1,a₀,A}(x) ∂^A u(x) =
    ∑_{d=1}^{Dγ} ∑_{|I|=d-1} ∑_{i₀} K_{a₀i₀}(x) B_{d,i₀,I} (∂^I V)(ψ x)`.
  For one piece, the left side is (before the time weight and the constituent map
  `(F.identity v u γ).map`, both linear) the `a₀`-component of the order-`d` operators of
  `constituentPhysical`, summed over the orders `d = r + 1`, applied to the word arrays
  `A ↦ ∂^A u(x)`; `transportedCoeff_flux_orders_of_contDiff` states it, for a `C^n` label field,
  with the orders `d` and words of length `d - 1` exactly as `constituentPhysical` indexes them.
* `chartInvJacobian_piola`: pointwise Piola identity for the physical flux
  `F_x(x)_{a₀} = ∑_{i₀} K_{a₀i₀}(x) F_y(ψ x)_{i₀}` (needs `det Dχ = 1`).
* the physical divergence of the transported flux equals the label divergence of the label flux
  `F_y(y)_{i₀} = ∑_{d,I} B_{d,i₀,I}(y) (∂^I V)(y)` at `ψ x` (`div_eq_label_div_of_transported`). -/

section Reindex

variable {M : Type*} [AddCommMonoid M]

/-- Pulling an inner finite sum out of a word-indexed double sum. -/
theorem transition_sum_pull {T : Type*} [Fintype T] (s : Finset ℕ)
    (f : ∀ r, DerivativeWord2 r → T → M) :
    ∑ r ∈ s, ∑ A : DerivativeWord2 r, ∑ j : T, f r A j =
      ∑ j : T, ∑ r ∈ s, ∑ A : DerivativeWord2 r, f r A j :=
  Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

/-- Pulling the flux direction out of an order- and word-indexed double sum. -/
theorem transition_sum_swap_dir (s : Finset ℕ) (f : ∀ d, DerivativeWord2 (d - 1) → Fin 2 → M) :
    ∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), ∑ j : Fin 2, f d I j =
      ∑ j : Fin 2, ∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), f d I j :=
  Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

/-- The triangular exchange of the output order `r` and the input order `d` (`r < d ≤ Dγ`). -/
theorem transition_flux_reindex (Dγ : ℕ)
    (F : ∀ r : ℕ, DerivativeWord2 r → ∀ d : ℕ, DerivativeWord2 (d - 1) → Fin 2 → M) :
    ∑ r ∈ Finset.range Dγ, ∑ A : DerivativeWord2 r, ∑ d ∈ Finset.Icc (r + 1) Dγ,
        ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2, F r A d I i₀ =
      ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        ∑ r ∈ Finset.range (d - 1 + 1), ∑ A : DerivativeWord2 r, F r A d I i₀ := by
  calc _ = ∑ r ∈ Finset.range Dγ, ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ A : DerivativeWord2 r,
          ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2, F r A d I i₀ :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 Dγ, ∑ r ∈ Finset.range (d - 1 + 1), ∑ A : DerivativeWord2 r,
          ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2, F r A d I i₀ := by
        refine Finset.sum_comm' fun _ _ => ?_
        simp only [Finset.mem_range, Finset.mem_Icc]
        constructor <;> intro h <;> omega
    _ = _ := Finset.sum_congr rfl fun d _ =>
        Eq.trans (transition_sum_pull (Finset.range (d - 1 + 1)) _)
          (Finset.sum_congr rfl fun _ _ => transition_sum_pull (Finset.range (d - 1 + 1)) _)

/-- Reindexing the orders `d ∈ [1, n]` by `r = d - 1 ∈ [0, n)`. -/
theorem transition_sum_Icc_one (n : ℕ) (G : ℕ → M) :
    ∑ d ∈ Finset.Icc 1 n, G d = ∑ r ∈ Finset.range n, G (r + 1) := by
  refine Finset.sum_nbij' (fun d => d - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    show d - 1 + 1 = d
    omega
  · intro r _
    show r + 1 - 1 = r
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    show G d = G (d - 1 + 1)
    rw [Nat.sub_add_cancel hd.1]

end Reindex

section Flux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `chartJacobian` is `jacMatrix`. -/
theorem chartJacobian_eq_jacMatrix (Υ : Vec 2 → Vec 2) (y : Vec 2) :
    chartJacobian Υ y = jacMatrix Υ y := rfl

/-- **Flux identity for the transported coefficient** (`transportedCoeff_flux`). With
`K = chartInvJacobian ψ`, a label array `B` of maximal order `Dγ` and `u = V ∘ ψ`, the transported
array applied to the physical jets of `u` is the label flux read through `K`:
`∑_{r<Dγ} ∑_{|A|=r} B̃_{r+1,a₀,A}(x) ∂^A u(x) =
  ∑_{d=1}^{Dγ} ∑_{|I|=d-1} ∑_{i₀} K_{a₀i₀}(x) B_{d,i₀,I} (∂^I V)(ψ x)`. -/
theorem transportedCoeff_flux {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {V : Vec 2 → E} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (x : Vec 2) (a₀ : Fin 2) :
    ∑ r ∈ Finset.range Dγ, ∑ A : DerivativeWord2 r,
        transportedCoeff (chartInvJacobian ψ) Dγ B r A x a₀ • orderedDerivative A (V ∘ ψ) x =
      ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        (chartInvJacobian ψ x a₀ i₀ * B d I i₀) • orderedDerivative I V (ψ x) := by
  calc _ = ∑ r ∈ Finset.range Dγ, ∑ A : DerivativeWord2 r, ∑ d ∈ Finset.Icc (r + 1) Dγ,
          ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
            (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
              transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
              orderedDerivative A (V ∘ ψ) x := by
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        simp only [transportedCoeff, Finset.sum_smul]
    _ = ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
          ∑ r ∈ Finset.range (d - 1 + 1), ∑ A : DerivativeWord2 r,
            (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
              transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
              orderedDerivative A (V ∘ ψ) x :=
        transition_flux_reindex Dγ fun _ A d I i₀ =>
          (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
            transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
            orderedDerivative A (V ∘ ψ) x
    _ = _ := by
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun _ _ => ?_
        rw [transitionT_chain hχ hψ hψχ hχψ hV I x]
        simp only [Finset.smul_sum, smul_smul]

/-- **Pointwise Piola identity for `K = chartInvJacobian ψ`.** If `det Dχ = 1`, the physical flux
`x ↦ (∑_{i₀} K_{a₀i₀}(x) F(ψ x)_{i₀})_{a₀}` has divergence `(div F) ∘ ψ`. -/
theorem chartInvJacobian_piola {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1) {F : Vec 2 → Fin 2 → E}
    (hF : ∀ l, Differentiable ℝ (fun y => F y l)) (x : Vec 2) :
    ∑ a₀ : Fin 2, fderiv ℝ (fun x' => ∑ i₀ : Fin 2, chartInvJacobian ψ x' a₀ i₀ • F (ψ x') i₀) x
        (basisVec a₀) =
      ∑ i₀ : Fin 2, fderiv ℝ (fun y => F y i₀) (ψ x) (basisVec i₀) := by
  have hK : ∀ (x' : Vec 2) (a i : Fin 2),
      chartInvJacobian ψ x' a i = jacMatrix χ (ψ x') a i := fun x' a i => by
    rw [chartInvJacobian_eq_of_inverse (hχ.differentiable (by simp))
      (hψ.differentiable (by simp)) hψχ hχψ x', chartJacobian_eq_jacMatrix]
  simp only [hK]
  exact AVRegularity.CycleComparison.Charts.piola_forward_vector hχ
    (hψ.differentiable (by simp)) hψχ hχψ hd hF x

end Flux

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time trajectories of torus Sobolev carriers.** Tools for packaging a family of finitely
smooth `ℤ²`-periodic fields `u t` as a trajectory `t ↦ periodicHk K (u t)` in `TorusHk K E`, in
the form consumed by `IsCoupledWeakSolutionTorus` (`u ∈ C(I;H^K) ∩ L²(I;H^{K+1})`, the higher
carrier truncating to the lower one):

* `truncate_periodicHk`, `truncate_periodicHk_succ`: the order `L` carrier truncates to the order
  `K ≤ L` carrier;
* `torusHk_sub_norm_le_of_jet_ae`: two elements of `TorusHk K E` whose jets are a.e. represented
  on the cell by uniformly `C`-close fields are `#(jet indices) · C`-close;
* `cellLp_norm_le_of_ae_bound`, `memLp_two_of_continuousOn_Icc`: the cell has unit volume, and a
  map continuous on a compact interval is in `L²` of that interval.

On `[t₀,t₁] × [0,1]²` jointly continuous jets are uniformly continuous, so they converge uniformly
on the cell, hence in `L²` of the cell. -/

/-- A cell `L²` class that is a.e. bounded by `C` has `L²` norm at most `C`: the cell has unit
volume. -/
theorem cellLp_norm_le_of_ae_bound {H : Type*} [NormedAddCommGroup H]
    (z : Lp H 2 (volume.restrict AVenhance.unitCube)) {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ‖z x‖ ≤ C) : ‖z‖ ≤ C := by
  have he := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict AVenhance.unitCube)
    (Lp.aestronglyMeasurable z) hz
  have he' : eLpNorm z 2 (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal C := by
    simpa only [Measure.restrict_apply_univ, EntryWeakProofs.weak_unitCube_volume,
      ENNReal.one_rpow, one_mul] using he
  refine (Lp.norm_def z).trans_le ?_
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he'

/-- A map that is continuous on a compact interval is in `L²` of that interval. -/
theorem memLp_two_of_continuousOn_Icc {H : Type*} [NormedAddCommGroup H] {t₀ t₁ : ℝ}
    {U : ℝ → H} (hU : ContinuousOn U (Set.Icc t₀ t₁)) :
    MemLp U 2 (volume.restrict (Set.Icc t₀ t₁)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  exact MemLp.of_bound (hU.aestronglyMeasurable measurableSet_Icc) C
    (ae_restrict_of_forall_mem measurableSet_Icc hC)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Two torus Sobolev elements whose jets are a.e. represented on the cell by fields that are
uniformly `C`-close on the cell are `#(jet indices) · C`-close in `TorusHk K E`. -/
theorem torusHk_sub_norm_le_of_jet_ae {K : ℕ} (F G : TorusHk K E)
    (f g : JetIndex2 K → Vec 2 → E)
    (hF : ∀ a : JetIndex2 K, F.val a =ᵐ[volume.restrict AVenhance.unitCube] f a)
    (hG : ∀ a : JetIndex2 K, G.val a =ᵐ[volume.restrict AVenhance.unitCube] g a)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : JetIndex2 K, ∀ x ∈ AVenhance.unitCube, ‖f a x - g a x‖ ≤ C) :
    ‖F - G‖ ≤ Fintype.card (JetIndex2 K) * C := by
  have hcoe (a : JetIndex2 K) : (F - G).val a = F.val a - G.val a := rfl
  have hterm (a : JetIndex2 K) : ‖(F - G).val a‖ ≤ C := by
    refine (congrArg norm (hcoe a)).trans_le ?_
    refine cellLp_norm_le_of_ae_bound _ hC ?_
    filter_upwards [Lp.coeFn_sub (F.val a) (G.val a), hF a, hG a,
      ae_restrict_mem Coarse.measurableSet_unitCube] with x hsub hFx hGx hx
    have h1 : (F.val a - G.val a) x = f a x - g a x := by
      refine hsub.trans ?_
      rw [Pi.sub_apply, hFx, hGx]
    exact (congrArg norm h1).trans_le (hb a x hx)
  refine (AVRegularity.Weighted.finitePiLp_norm_le_sum (F - G).val).trans ?_
  calc ∑ a : JetIndex2 K, ‖(F - G).val a‖ ≤ ∑ _a : JetIndex2 K, C :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = Fintype.card (JetIndex2 K) * C := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Truncation of the carrier of a finitely smooth periodic field.** For `K ≤ L` and a `C^L`
periodic field `f`, the order `L` carrier truncates to the order `K` carrier. -/
theorem truncate_periodicHk {K L : ℕ} (hKL : K ≤ L) (f : Vec 2 → E)
    (hf : ContDiff ℝ (L : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    truncateTorusHk hKL (periodicHk L f hf hp) =
      periodicHk K f (hf.of_le (by exact_mod_cast hKL)) hp := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  refine (truncateTorusHk_apply hKL (periodicHk L f hf hp) a).trans (Lp.ext ?_)
  exact (periodicHk_jet_ae L f hf hp (truncateJetIndex hKL a)).trans
    (periodicHk_jet_ae K f (hf.of_le (by exact_mod_cast hKL)) hp a).symm

/-- The order `K + 1` carrier of a `C^(K+1)` periodic field truncates to its order `K` carrier
(the form of the truncation clause of `IsCoupledWeakSolutionTorus`). -/
theorem truncate_periodicHk_succ (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    truncateTorusHk (Nat.le_succ K) (periodicHk (K + 1) f hf hp) =
      periodicHk K f (hf.of_le (by exact_mod_cast Nat.le_add_right K 1)) hp :=
  truncate_periodicHk (L := K + 1) (Nat.le_succ K) f hf hp

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleComparison.Reconstruction

/-! Order plumbing for the physical reconstruction of `cycle_comparison`.

* Box regularity, the cell inverse and lift sequences are monotone in the stored orders: a lift
  sequence stored at `(sX, sZ)` is one at every `(sX', sZ') ≤ (sX, sZ)`. (The same monotonicity of
  `IsBoxSmooth` is `AVRegularity.IsBoxSmooth.mono` in `Residual/MixedPartials.lean`; it is restated
  here to keep this module light.)
* The order arithmetic relating the orders of `cycle_comparison_physical_lift`
  (`Klift`, `Llift`, `compReserveK`, `A' = Ac`, `N' = Nc`) to the residual statements
  (`s₀ = A_cl + 2`, `kres = 4(N+D) + 2A_cl + 16`, `r ≤ Kmax` extra derivatives) and to the reserves
  of `cycle_comparison_lift_setting`. Here `compReserveK = kres + Kmax + H(D-2)`. -/

section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Box regularity is monotone in both orders. -/
theorem isBoxSmooth_mono {sX sZ sX' sZ' : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth sX sZ f) (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ) : IsBoxSmooth sX' sZ' f :=
  ⟨fun X => (hf.1 X).of_le (by exact_mod_cast hZ),
   fun b hb z => (hf.2.1 b (hb.trans hZ) z).of_le (by exact_mod_cast hX),
   fun a b ha hb => hf.2.2 a b (ha.trans hX) (hb.trans hZ)⟩

/-- The cell field inverse is monotone in the stored fast order. -/
theorem isCellFieldInverse_mono [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ sZ' : ℕ} {t₀ t₁ : ℝ} {c₀ : Vec 2 → E} {g c : ℝ → Vec 2 → E}
    (hc : IsCellFieldInverse G v sZ t₀ t₁ c₀ g c) (hZ : sZ' ≤ sZ) :
    IsCellFieldInverse G v sZ' t₀ t₁ c₀ g c :=
  ⟨fun t ht => (hc.1 t ht).of_le (by exact_mod_cast hZ), hc.2⟩

end Mono

section LiftMono

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
  {Q : LiftOperatorData ι h D} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}

/-- A lift sequence stored at `(sX, sZ)` is a lift sequence at every smaller pair of orders. -/
theorem isLiftSequence_mono {sX sZ sX' sZ' : ℕ} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ) : IsLiftSequence Q sX' sZ' t₀ t₁ N H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hseq
  refine ⟨h1, h2, h3, h4, h5, fun hh hhh n m α v u t ht => ?_,
    fun hh hhh n hn hnN a₀ ha₀ X => isCellFieldInverse_mono (h7 hh hhh n hn hnN a₀ ha₀ X) hZ⟩
  exact ⟨isBoxSmooth_mono (h6 hh hhh n m α v u t ht).1 hX hZ, (h6 hh hhh n m α v u t ht).2⟩

end LiftMono

end AVRegularity.CycleComparison.Reconstruction
end
end
