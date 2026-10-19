-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.Velocity.Port.Section2FlowInverseBounds
import AVRegularity.Velocity.Port.Section2JointInduction
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.CycleComparison.ActualMeans.KernelRegular
public import AVRegularity.Statements.Intermediate.CycleReference.OcMaterialMetric
public import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Section5.FlowPiolaDivergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleComparison.Charts

/-! The renewal chart and its inverse are mutually inverse spatial maps at every time. Both are
flow maps of the same stream velocity, and the flow group law gives `X(s, X(t, y, s), t) = y`. -/

/-- The flow of an admissible stream composes according to its time parameters. -/
theorem streamFlow_group_law {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (x : Vec 2)
    (s r t : ℝ) : streamFlow φ hφ t (streamFlow φ hφ r x s) r = streamFlow φ hφ t x s :=
  AVenhance.Infra.Flow.flow_group_law (streamVel φ) hφ.vel_lipschitz
    (flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz) x s r t

/-- The flow of an admissible stream is the identity at equal times. -/
theorem streamFlow_self {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (x : Vec 2) (s : ℝ) :
    streamFlow φ hφ s x s = x :=
  (flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz).1 x s

/-- The inverse renewal chart undoes the renewal chart. -/
theorem ocChartInv_ocChart (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l : ℤ) (t : ℝ) (y : Vec 2) :
    ocChartInv α q Λ m φ hφ l t (ocChart α q Λ m φ hφ l t y) = y := by
  unfold ocChartInv ocChart
  rw [streamFlow_group_law, streamFlow_self]

/-- The renewal chart undoes the inverse renewal chart. -/
theorem ocChart_ocChartInv (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l : ℤ) (t : ℝ) (x : Vec 2) :
    ocChart α q Λ m φ hφ l t (ocChartInv α q Λ m φ hφ l t x) = x := by
  unfold ocChartInv ocChart
  rw [streamFlow_group_law, streamFlow_self]

end AVRegularity.CycleComparison.Charts
end
end

section
@[expose] public section
open Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.CycleReference
open scoped Matrix
namespace AVRegularity.CycleComparison.Charts

/-! Piola transport under an exact volume-preserving smooth chart, for fluxes that are only
differentiable. If `Φ` is smooth with unit Jacobian determinant and inverse `Ψ`, then the
physical flux `x ↦ DΦ(Ψ x) F(Ψ x)` has divergence `(div F) ∘ Ψ`. -/

/-- The inverse-Jacobian Piola identity for a flux differentiable at the image point. -/
theorem inverse_jacobian_piola_at {M g : Vec 2 → Vec 2}
    (hM : ContDiff ℝ (⊤ : ℕ∞) M) (hd : ∀ x, (jacMatrix M x).det = 1) (x : Vec 2)
    (hg : DifferentiableAt ℝ g (M x)) :
    vecDiv (fun y => (jacMatrix M y)⁻¹.mulVec (g (M y))) x = vecDiv g (M x) := by
  have hdiff := hM.differentiable (by simp)
  have hcof (y : Vec 2) := rowCofactor_eq_jacMatrix_inverse hdiff y (hd y)
  obtain ⟨hQ, hdiv⟩ := rowCofactor_gradMatrix_piolaInputs (hM.of_le (by simp)) x
  have hdet : (gradMatrix M x).det = 1 := by
    rw [← Matrix.det_transpose, ← jacMatrix_eq_gradMatrix_transpose hdiff]
    exact hd x
  have ht := vecDiv_rowCofactorPiola (hdiff x).hasFDerivAt hg.hasFDerivAt hQ hdiv hdet
  simpa only [hcof] using ht

/-- **Forward Piola transport.** Pushing a differentiable chart-frame flux `F` forward by the
chart gives a physical flux whose divergence is the pushed-forward divergence. -/
theorem piola_forward {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : Differentiable ℝ Ψ) (hΨΦ : ∀ y, Ψ (Φ y) = y) (hΦΨ : ∀ x, Φ (Ψ x) = x)
    (hd : ∀ y, (jacMatrix Φ y).det = 1) {F : Vec 2 → Vec 2} (hF : Differentiable ℝ F)
    (x : Vec 2) :
    vecDiv (fun x' => (jacMatrix Φ (Ψ x')).mulVec (F (Ψ x'))) x = vecDiv F (Ψ x) := by
  set g : Vec 2 → Vec 2 := fun x' => (jacMatrix Φ (Ψ x')).mulVec (F (Ψ x')) with hgdef
  have hent : ∀ i j : Fin 2, Differentiable ℝ (fun y => jacMatrix Φ y i j) := by
    intro i j
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ Φ y) :=
      hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ Φ y (basisVec j)) :=
      h1.clm_apply contDiff_const
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => jacMatrix Φ y i j) := by
      simp only [jacMatrix, Matrix.of_apply]
      exact contDiff_pi.1 h2 i
    exact h3.differentiable (by simp)
  have hg : Differentiable ℝ g := by
    intro x'
    refine differentiableAt_pi.2 fun i => ?_
    have hsum : DifferentiableAt ℝ
        (fun x'' => ∑ j : Fin 2, jacMatrix Φ (Ψ x'') i j * F (Ψ x'') j) x' := by
      refine DifferentiableAt.fun_sum fun j _ => ?_
      have h1 : DifferentiableAt ℝ (fun x'' => jacMatrix Φ (Ψ x'') i j) x' :=
        (hent i j (Ψ x')).comp x' (hΨ x')
      have h2 : DifferentiableAt ℝ (fun x'' => F (Ψ x'') j) x' :=
        differentiableAt_pi.1 ((hF (Ψ x')).comp x' (hΨ x')) j
      exact h1.mul h2
    exact hsum
  have hinv := inverse_jacobian_piola_at hΦ hd (Ψ x) (hg (Φ (Ψ x)))
  have hfun : (fun y => (jacMatrix Φ y)⁻¹.mulVec (g (Φ y))) = F := by
    funext y
    have hdy : IsUnit (jacMatrix Φ y).det := by rw [hd y]; exact isUnit_one
    simp only [hgdef, hΨΦ y, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdy,
      Matrix.one_mulVec]
  rw [hfun, hΦΨ x] at hinv
  exact hinv.symm

/-- A scalar functional commutes with a directional derivative. -/
theorem fderiv_clm_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E →L[ℝ] ℝ) {G : Vec 2 → E} {x : Vec 2} (hG : DifferentiableAt ℝ G x) (e : Vec 2) :
    fderiv ℝ (fun x' => φ (G x')) x e = φ (fderiv ℝ G x e) :=
  congrArg (fun L : Vec 2 →L[ℝ] ℝ => L e) (φ.hasFDerivAt.comp x hG.hasFDerivAt).fderiv

/-- The Jacobian entries of a smooth chart are differentiable. -/
theorem differentiable_jacMatrix_entry {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i j : Fin 2) : Differentiable ℝ (fun y => jacMatrix Φ y i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ Φ y) :=
    hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ Φ y (basisVec j)) :=
    h1.clm_apply contDiff_const
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => jacMatrix Φ y i j) := by
    simp only [jacMatrix, Matrix.of_apply]
    exact contDiff_pi.1 h2 i
  exact h3.differentiable (by simp)

/-- **Forward Piola transport for vector-valued fluxes.** The divergence of the pushed-forward
flux `x ↦ DΦ(Ψ x) F(Ψ x)` is the pushed-forward divergence, for fluxes with values in any normed
space (tested against continuous linear functionals). -/
theorem piola_forward_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ Ψ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : Differentiable ℝ Ψ)
    (hΨΦ : ∀ y, Ψ (Φ y) = y) (hΦΨ : ∀ x, Φ (Ψ x) = x) (hd : ∀ y, (jacMatrix Φ y).det = 1)
    {F : Vec 2 → Fin 2 → E} (hF : ∀ l, Differentiable ℝ (fun y => F y l)) (x : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • F (Ψ x') l) x
        (basisVec k) =
      ∑ l : Fin 2, fderiv ℝ (fun y => F y l) (Ψ x) (basisVec l) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  have hFφ : Differentiable ℝ (fun y => (fun l => φ (F y l) : Vec 2)) :=
    differentiable_pi.2 fun l => φ.differentiable.comp (hF l)
  have hsc := piola_forward hΦ hΨ hΨΦ hΦΨ hd hFφ x
  have hG : ∀ k : Fin 2, DifferentiableAt ℝ
      (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • F (Ψ x') l) x := by
    intro k
    refine DifferentiableAt.fun_sum fun l _ => ?_
    have h1 : DifferentiableAt ℝ (fun x' => jacMatrix Φ (Ψ x') k l) x :=
      (differentiable_jacMatrix_entry hΦ k l (Ψ x)).comp x (hΨ x)
    have h2 : DifferentiableAt ℝ (fun x' => F (Ψ x') l) x := (hF l (Ψ x)).comp x (hΨ x)
    exact h1.fun_smul h2
  have hL : φ (∑ k : Fin 2, fderiv ℝ
        (fun x' => ∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • F (Ψ x') l) x (basisVec k)) =
      vecDiv (fun x' => (jacMatrix Φ (Ψ x')).mulVec (fun l => φ (F (Ψ x') l))) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← fderiv_clm_comp_apply φ (hG k)]
    have hfun : (fun x' => φ (∑ l : Fin 2, jacMatrix Φ (Ψ x') k l • F (Ψ x') l)) =
        fun y => (jacMatrix Φ (Ψ y)).mulVec (fun l => φ (F (Ψ y) l)) k := by
      funext x'
      simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [hfun]
    rfl
  have hR : φ (∑ l : Fin 2, fderiv ℝ (fun y => F y l) (Ψ x) (basisVec l)) =
      vecDiv (fun y => (fun l => φ (F y l) : Vec 2)) (Ψ x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← fderiv_clm_comp_apply φ (hF l (Ψ x))]
    rfl
  rw [hL, hR]
  exact hsc

end AVRegularity.CycleComparison.Charts
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.Velocity AVRegularity.Velocity.Port
namespace AVRegularity.CycleComparison.Charts

/-! Normalized jets of the short flow charts (`oc_flow_jets`).

The induction of the velocity construction bounds, for `|t| ≤ 2⁻²⁵/a_m`, the
`barNorm`s of the entries of `D X_m⁻¹(s + t, ·, s) - I` by `2²³ |t| a_m` at radius `2¹¹/ε_m`
(`section2_flow_inverse_regbounds_from_previous`). The inverse flow is the forward flow with the
times exchanged (`flowInv b t y s = flow b s y t`), so the same bound covers every pair of
times. Unpacking the `barNorm` into pointwise word bounds and summing the words and the matrix
entries gives `‖∇ⁿ(D X(t,·,t') - I)‖ ≤ 2²⁵ n! (2²⁵/ε)ⁿ a |t - t'|`. -/

/-- The operator norm of a linear map of `Vec 2` is at most the sum of its entries. -/
theorem clm_norm_le_sum_entries (A : Vec 2 →L[ℝ] Vec 2) :
    ‖A‖ ≤ ∑ j : Fin 2, ∑ i : Fin 2, |A (basisVec j) i| := by
  have h1 : ∀ j : Fin 2, ‖A (basisVec j)‖ ≤ ∑ i : Fin 2, |A (basisVec j) i| := by
    intro j
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |A (basisVec j) i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 := norm_le_sum_basisVec (F := Vec 2)
    ((continuousMultilinearCurryFin1 ℝ (Vec 2) (Vec 2)).symm A)
  have hnorm : ‖(continuousMultilinearCurryFin1 ℝ (Vec 2) (Vec 2)).symm A‖ = ‖A‖ :=
    LinearIsometryEquiv.norm_map _ _
  rw [hnorm] at h2
  refine h2.trans ?_
  calc ∑ w : DerivativeWord2 1, ‖(continuousMultilinearCurryFin1 ℝ (Vec 2) (Vec 2)).symm A
        (fun i => basisVec (w i))‖
      = ∑ j : Fin 2, ‖A (basisVec j)‖ := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ fun w => ?_
        simp [continuousMultilinearCurryFin1_symm_apply]
    _ ≤ _ := Finset.sum_le_sum fun j _ => h1 j

/-- Entries of the derivatives of a linear-map valued function. -/
theorem iteratedFDeriv_entry {n : ℕ} {F : Vec 2 → Vec 2 →L[ℝ] Vec 2}
    (hF : ContDiff ℝ n F) (i j : Fin 2) (y : Vec 2) (v : Fin n → Vec 2) :
    iteratedFDeriv ℝ n (fun x => F x (basisVec j) i) y v =
      iteratedFDeriv ℝ n F y v (basisVec j) i := by
  let L : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec j))
  have h := L.iteratedFDeriv_comp_left (hF.contDiffAt (x := y)) (i := n) le_rfl
  have h' : (fun x => F x (basisVec j) i) = L ∘ F := rfl
  rw [h', h]
  rfl

/-- A `barNorm` bound gives pointwise bounds of every coordinate word. -/
theorem word_le_of_barNorm_le {n : ℕ} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hbar : barNorm n R f ≤ ENNReal.ofReal B)
    (w : Fin n → Fin 2) (x : Vec 2) :
    |iteratedFDeriv ℝ n f x (fun k => basisVec (w k))| ≤
      B * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n := by
  set K : ℝ := ((n : ℝ) + 1) ^ 2 / (n.factorial : ℝ) with hK
  have hKpos : 0 < K := by positivity
  have hsup : eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (w k))) ⊤ volume ≤
      ENNReal.ofReal (B * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n) := by
    have hw : eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (w k))) ⊤ volume ≤
        ⨆ i : Fin n → Fin 2,
          eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) ⊤ volume :=
      le_iSup (fun i : Fin n → Fin 2 =>
        eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) ⊤ volume) w
    unfold barNorm at hbar
    set X := ⨆ i : Fin n → Fin 2,
      eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) ⊤ volume with hX
    have hRpos : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.2 hR).ne'
    have hfac : ENNReal.ofReal K * (ENNReal.ofReal R)⁻¹ ^ n ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_pos.2 hKpos).ne'
        (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top))
    have hfin : ENNReal.ofReal K * (ENNReal.ofReal R)⁻¹ ^ n ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hRpos))
    have hbar' : X * (ENNReal.ofReal K * (ENNReal.ofReal R)⁻¹ ^ n) ≤ ENNReal.ofReal B := by
      rw [mul_comm]; exact hbar
    have hle : X ≤ ENNReal.ofReal B / (ENNReal.ofReal K * (ENNReal.ofReal R)⁻¹ ^ n) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hfac) (Or.inl hfin)).2 hbar'
    refine hw.trans (hle.trans (le_of_eq ?_))
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 hKpos).ne')
        (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.inv_pow, inv_inv, ← ENNReal.ofReal_inv_of_pos hKpos,
      ← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hK]
    field_simp
  have hcont : Continuous (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (w k))) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) ℝ
      (fun k => basisVec (w k))).continuous.comp
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hae : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖iteratedFDeriv ℝ n f x (fun k => basisVec (w k))‖ₑ ≤
        ENNReal.ofReal (B * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n) := by
    have h0 := ae_le_eLpNormEssSup (μ := volume)
      (f := fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (w k)))
    have hvol : (FaaDiBruno.vecVolume 2) = (volume : Measure (Vec 2)) := by
      rw [FaaDiBruno.vecVolume, MeasureTheory.volume_pi]
    rw [hvol]
    filter_upwards [h0] with x hx
    have hsup2 := hsup
    rw [eLpNorm_exponent_top hcont.aestronglyMeasurable] at hsup2
    exact hx.trans hsup2
  have := Section2FlowHigherDerivative.continuous_norm_le_of_ae_le_vecVolume hcont
    (by positivity) hae x
  simpa [Real.norm_eq_abs] using this

/-! The normalized jets of the short flow charts of the construction. -/

/-- The arithmetic of the final constant. -/
theorem flowJets_constant {n : ℕ} {E a Δ : ℝ} (hE : 0 < E) (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) :
    ((2 : ℝ) ^ n * 4) * (2 ^ 23 * Δ * a * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
        (2 ^ 11 * E⁻¹) ^ n) ≤
      2 ^ 25 * (n.factorial : ℝ) * (2 ^ 25 / E) ^ n * (a * Δ) := by
  have hf : (n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ n.factorial := by
    refine div_le_self (by positivity) ?_
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hp : (2 : ℝ) ^ n * (2 ^ 11 * E⁻¹) ^ n ≤ (2 ^ 25 / E) ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [div_eq_mul_inv]
    have hEi : 0 < E⁻¹ := inv_pos.2 hE
    nlinarith
  have hfac0 : 0 ≤ (n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2 := by positivity
  calc ((2 : ℝ) ^ n * 4) * (2 ^ 23 * Δ * a * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
          (2 ^ 11 * E⁻¹) ^ n)
      = 2 ^ 25 * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) *
          ((2 : ℝ) ^ n * (2 ^ 11 * E⁻¹) ^ n) * (a * Δ) := by ring
    _ ≤ 2 ^ 25 * (n.factorial : ℝ) * (2 ^ 25 / E) ^ n * (a * Δ) := by
        gcongr

/-- The flow jets with explicit constants: `c = 2⁻²⁵`, `C = 2²⁵`. -/
theorem oc_flow_jets_explicit (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (t t' : ℝ)
    (hc : ocA α q Λ (m - 1) * |t - t'| ≤ 2 ^ (-25 : ℤ)) (n : ℕ) (y : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ (fun z => streamFlow (Φ (m - 1)) hφ t z t') x -
        ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
      2 ^ 25 * (n.factorial : ℝ) * (2 ^ 25 / ocEpsilon q Λ (m - 1)) ^ n *
        (ocA α q Λ (m - 1) * |t - t'|) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β - 1 := ⟨α + 1, by ring⟩
  set M := m - 1 with hM
  have hM1 : 1 ≤ M := by omega
  let D := ocJetRecursionData (β - 1) s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ ζ hζ
  have happB2 := AppB2Smoothness.appB2InverseFlowData_of_smoothPeriodicFlow D hΦ
  have hprev := section2_stream_induction D happB2 (M - 1)
  have hbound := Section2FlowInverseBounds.section2_flow_inverse_regbounds_from_previous D hΦ
    happB2 M hM1 hprev
  have hEpos : 0 < ocEpsilon q Λ M := Construction.Stream.ocEpsilon_pos (by omega)
  have hApos : 0 < ocA (β - 1) q Λ M := by
    unfold ocA; exact Real.rpow_pos_of_pos hEpos _
  have hΔ : |t' - t| = |t - t'| := abs_sub_comm t' t
  have ht : |t' - t| ≤ 2 ^ (-25 : ℤ) * (D.velocityAmplitude M)⁻¹ := by
    change |t' - t| ≤ 2 ^ (-25 : ℤ) * (ocA (β - 1) q Λ M)⁻¹
    rw [hΔ, le_mul_inv_iff₀ hApos, mul_comm]
    exact hc
  have hb := hbound t (t' - t) ht n
  -- the inverse Jacobian is the derivative of the forward flow with the times exchanged
  have hfun : ∀ x, Section2FlowIdentities.constructionFlowInvJacobian D hΦ M (t' - t) t x =
      fderiv ℝ (fun z => streamFlow (Φ M) hφ t z t') x := by
    intro x
    have h1 : t + (t' - t) = t' := by ring
    simp only [Section2FlowIdentities.constructionFlowInvJacobian,
      Section2FlowIdentities.streamFlowInvJacobian, Section2FlowIdentities.streamFlowInv, h1]
    rfl
  set F : Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    fun x => fderiv ℝ (fun z => streamFlow (Φ M) hφ t z t') x - ContinuousLinearMap.id ℝ (Vec 2)
    with hF
  have hFeq : (fun x => Section2FlowIdentities.constructionFlowInvJacobian D hΦ M (t' - t) t x -
      ContinuousLinearMap.id ℝ (Vec 2)) = F := by
    funext x; rw [hF, hfun x]
  rw [hFeq] at hb
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hJ := Section2FlowRegularityCore.streamFlowInvJacobian_joint_smooth
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)
    have hJx : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
        Section2FlowIdentities.streamFlowInvJacobian (Φ M)
          (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M) (t' - t) t x) :=
      hJ.comp ((contDiff_const (c := (t, t' - t))).prodMk contDiff_id)
    have hfun' : (fun x => Section2FlowIdentities.streamFlowInvJacobian (Φ M)
        (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M) (t' - t) t x) =
        fun x => fderiv ℝ (fun z => streamFlow (Φ M) hφ t z t') x := funext hfun
    rw [hfun'] at hJx
    exact hJx.sub contDiff_const
  set R : ℝ := 2 ^ 11 * (ocEpsilon q Λ M)⁻¹ with hR
  have hRpos : 0 < R := by positivity
  set Bd : ℝ := 2 ^ 23 * |t' - t| * ocA (β - 1) q Λ M with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hentry : ∀ i j : Fin 2, ∀ w : Fin n → Fin 2,
      |iteratedFDeriv ℝ n F y (fun k => basisVec (w k)) (basisVec j) i| ≤
        Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n := by
    intro i j w
    have hbar : barNorm n R (fun x => F x (basisVec j) i) ≤ ENNReal.ofReal Bd := by
      refine le_trans ?_ hb
      exact le_iSup₂ (f := fun (i : Fin 2) (j : Fin 2) =>
        barNorm n R (fun x => F x (basisVec j) i)) i j
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x (basisVec j) i) := by
      have hL : ContDiff ℝ (⊤ : ℕ∞) (fun A : Vec 2 →L[ℝ] Vec 2 => A (basisVec j) i) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
          (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec j))).contDiff
      exact hL.comp hFsmooth
    have hw := word_le_of_barNorm_le hRpos hBd0 hsm hbar w y
    rwa [iteratedFDeriv_entry (hFsmooth.of_le (by exact_mod_cast le_top)) i j y] at hw
  have hword : ∀ w : DerivativeWord2 n,
      ‖iteratedFDeriv ℝ n F y (fun k => basisVec (w k))‖ ≤
        4 * (Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n) := by
    intro w
    refine (clm_norm_le_sum_entries _).trans ?_
    calc ∑ j : Fin 2, ∑ i : Fin 2, |iteratedFDeriv ℝ n F y (fun k => basisVec (w k)) (basisVec j) i|
        ≤ ∑ _j : Fin 2, ∑ _i : Fin 2, Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hentry i j w
      _ = 4 * (Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum := norm_le_sum_basisVec (F := Vec 2 →L[ℝ] Vec 2) (iteratedFDeriv ℝ n F y)
  have htot : ‖iteratedFDeriv ℝ n F y‖ ≤
      (2 : ℝ) ^ n * (4 * (Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n)) := by
    refine hsum.trans ((Finset.sum_le_sum fun w _ => hword w).trans (le_of_eq ?_))
    rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul]
    push_cast
    ring
  calc ‖iteratedFDeriv ℝ n F y‖
      ≤ (2 : ℝ) ^ n * (4 * (Bd * ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * R ^ n)) := htot
    _ = ((2 : ℝ) ^ n * 4) * (2 ^ 23 * |t' - t| * ocA (β - 1) q Λ M *
          ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ 2) * (2 ^ 11 * (ocEpsilon q Λ M)⁻¹) ^ n) := by
        rw [hBd, hR]; ring
    _ ≤ 2 ^ 25 * (n.factorial : ℝ) * (2 ^ 25 / ocEpsilon q Λ M) ^ n *
          (ocA (β - 1) q Λ M * |t' - t|) :=
        flowJets_constant hEpos hApos.le (abs_nonneg _)
    _ = _ := by rw [hΔ]

/-- **Normalized jets of the short flow charts**. -/
theorem oc_flow_jets_main (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ (Λ : ℕ), 128 ≤ Λ → ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
      ∀ (m : ℕ), 2 ≤ m → ∀ (hφ : IsAdmissibleStream (Φ (m - 1))) (t t' : ℝ),
        ocA α q Λ (m - 1) * |t - t'| ≤ c →
        ∀ (n : ℕ) (y : Vec 2),
          ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ (fun z => streamFlow (Φ (m - 1)) hφ t z t') x -
              ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
            C * (n.factorial : ℝ) * (C / ocEpsilon q Λ (m - 1)) ^ n *
              (ocA α q Λ (m - 1) * |t - t'|) :=
  ⟨2 ^ (-25 : ℤ), 2 ^ 25, by positivity, by norm_num,
    fun Λ hΛ Φ hΦ m hm hφ t t' hc n y =>
      oc_flow_jets_explicit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ t t' hc n y⟩

end AVRegularity.CycleComparison.Charts
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleComparison.Charts

/-! The renewal charts `ocChart` and their inverses `ocChartInv` as exact charts of the plane:
joint smoothness, lattice equivariance, unit Jacobian determinant, and the normalized jets
`‖D^p Φ‖, ‖D^p Φ⁻¹‖ ≤ Cχ_p ε_{m-1}^{1-p}` on short charts (`a_{m-1}|t - lτ_m''| ≤ c`), from the
flow jets of the construction (`oc_flow_jets`). -/

section
section Qualitative

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)

theorem contDiff_streamFlow_slice (t t' : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => streamFlow φ hφ t z t') :=
  (CycleReference.streamFlow_joint_smooth hφ).comp
    (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))

theorem contDiff_ocChart_joint (α q : ℝ) (Λ m : ℕ) (l : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocChart α q Λ m φ hφ l p.1 p.2) :=
  (CycleReference.streamFlow_joint_smooth hφ).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

theorem contDiff_ocChartInv_joint (α q : ℝ) (Λ m : ℕ) (l : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocChartInv α q Λ m φ hφ l p.1 p.2) :=
  (CycleReference.streamFlow_joint_smooth hφ).comp
    (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))

theorem ocChart_latticeShift (α q : ℝ) (Λ m : ℕ) (l : ℤ) (t : ℝ) (p : Fin 2 → ℤ) (y : Vec 2) :
    ocChart α q Λ m φ hφ l t (y + latticeShift p) =
      ocChart α q Λ m φ hφ l t y + latticeShift p :=
  CycleReference.streamFlow_lattice_equivariant hφ t _ y p

theorem ocChart_det (α q : ℝ) (Λ m : ℕ) (l : ℤ) (t : ℝ) (y : Vec 2) :
    (jacMatrix (ocChart α q Λ m φ hφ l t) y).det = 1 :=
  CycleReference.streamFlow_jacMatrix_det_one hφ t _ y

end Qualitative

/-- The constants of the normalized chart jets. -/
def chartJetConst (C c : ℝ) (p : ℕ) : ℝ :=
  if p = 1 then 1 + C * c else C * ((p - 1).factorial : ℝ) * C ^ (p - 1) * c

/-- From the jets of `Df - I` to the normalized jets of `f`. -/
theorem chart_jets_of_flow_jets {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C E A c : ℝ}
    (hC : 1 ≤ C) (hE : 0 < E) (hAc : A ≤ c)
    (h : ∀ (n : ℕ) (y : Vec 2), ‖iteratedFDeriv ℝ n
      (fun x => fderiv ℝ f x - ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
        C * (n.factorial : ℝ) * (C / E) ^ n * A)
    (p : ℕ) (hp : 1 ≤ p) (y : Vec 2) :
    ‖iteratedFDeriv ℝ p f y‖ ≤ chartJetConst C c p * E⁻¹ ^ (p - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hbound : C * (n.factorial : ℝ) * (C / E) ^ n * A ≤
      C * (n.factorial : ℝ) * C ^ n * c * E⁻¹ ^ n := by
    have h1 : C * (n.factorial : ℝ) * (C / E) ^ n * A ≤ C * (n.factorial : ℝ) * (C / E) ^ n * c :=
      mul_le_mul_of_nonneg_left hAc (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [← norm_iteratedFDeriv_fderiv, Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 := h 0 y
    rw [norm_iteratedFDeriv_zero] at h0 ⊢
    have h1 : ‖fderiv ℝ f y‖ ≤ ‖fderiv ℝ f y - ContinuousLinearMap.id ℝ (Vec 2)‖ + 1 := by
      have e : fderiv ℝ f y =
          (fderiv ℝ f y - ContinuousLinearMap.id ℝ (Vec 2)) + ContinuousLinearMap.id ℝ (Vec 2) :=
        (sub_add_cancel _ _).symm
      calc ‖fderiv ℝ f y‖
          = ‖(fderiv ℝ f y - ContinuousLinearMap.id ℝ (Vec 2)) +
              ContinuousLinearMap.id ℝ (Vec 2)‖ := congrArg norm e
        _ ≤ ‖fderiv ℝ f y - ContinuousLinearMap.id ℝ (Vec 2)‖ +
              ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ f y - ContinuousLinearMap.id ℝ (Vec 2)‖ + 1 :=
            add_le_add_right ContinuousLinearMap.norm_id_le _
    have h2 := h0.trans hbound
    simp only [chartJetConst, zero_add, ite_true, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one] at h2 ⊢
    linarith
  · have hne : n ≠ 0 := by omega
    have e : iteratedFDeriv ℝ n (fun x => fderiv ℝ f x - ContinuousLinearMap.id ℝ (Vec 2)) y =
        iteratedFDeriv ℝ n (fderiv ℝ f) y :=
      ChartTransport.iteratedFDeriv_sub_const_pos (hfd.of_le (by exact_mod_cast le_top))
        le_rfl hne _ y
    have hn1 : n + 1 ≠ 1 := by omega
    rw [← e]
    refine (h n y).trans (hbound.trans (le_of_eq ?_))
    simp only [chartJetConst, ite_eq_right hn1, Nat.add_sub_cancel]

/-- **Normalized jets of the renewal charts on the anchor window** `|t - lτ_m''| ≤ τ_m''`, with
explicit constants. The smallness `a_{m-1} τ_m'' ≤ 2⁻²⁵` holds at every level. -/
theorem ocChart_window_jets (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m) (p : ℕ) (hp : 1 ≤ p)
    (y : Vec 2) :
    ‖iteratedFDeriv ℝ p (ocChart α q Λ m (Φ (m - 1)) hφ l t) y‖ ≤
        chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) p * (ocEpsilon q Λ (m - 1))⁻¹ ^ (p - 1) ∧
      ‖iteratedFDeriv ℝ p (ocChartInv α q Λ m (Φ (m - 1)) hφ l t) y‖ ≤
        chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) p * (ocEpsilon q Λ (m - 1))⁻¹ ^ (p - 1) := by
  have hEb := Scales.epsilon_basic (q := q) (Λ := Λ) (m := m - 1) hq.1 hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := hEb.1
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_nonneg hE.le _
  have hsmall : ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m| ≤ 2 ^ (-25 : ℤ) := by
    calc ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m|
        ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_le_mul_of_nonneg_left ht hA0
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
          (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ
            (by omega : 1 ≤ m)).2.2.2.2.1
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hE.le hEb.2.1 (by linarith))
            (by positivity)
      _ = 2 ^ (-25 : ℤ) := mul_one _
  have hsmall' : ocA α q Λ (m - 1) * |(l : ℝ) * ocTauPP α q Λ m - t| ≤ 2 ^ (-25 : ℤ) := by
    rw [abs_sub_comm]
    exact hsmall
  have hC : (1 : ℝ) ≤ 2 ^ 25 := by norm_num
  refine ⟨?_, ?_⟩
  · exact chart_jets_of_flow_jets (contDiff_streamFlow_slice hφ t _) hC hE hsmall
      (fun n y => oc_flow_jets_explicit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ t
        ((l : ℝ) * ocTauPP α q Λ m) hsmall n y) p hp y
  · exact chart_jets_of_flow_jets (contDiff_streamFlow_slice hφ _ t) hC hE hsmall'
      (fun n y => oc_flow_jets_explicit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ
        ((l : ℝ) * ocTauPP α q Λ m) t hsmall' n y) p hp y
end

/-! The deviation of the renewal charts from the identity on the anchor window
`|t - lτ_m''| ≤ τ_m''`: the Jacobian `DΦ_l - I` and the material metric `G_l - I` have
scale-weighted jets of size `g_m = a_{m-1} τ_m''` at the scale `ε_{m-1}`, so that identical-history
metric stability and the Piola deformation cost `C B g_m`; the flow jets are those of
`oc_flow_jets`. -/

section
open AVRegularity.CycleComparison.ActualMeans

/-! ### Entries of `DΦ - I` -/

/-- The jets of an entry of `DΦ - I` are bounded by the jets of `DΦ - I`. -/
theorem norm_iteratedFDeriv_jac_sub_le {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : ℕ)
    (a b : Fin 2) (y : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun z => jacMatrix Φ z a b - (if a = b then 1 else 0)) y‖ ≤
      ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) y‖ := by
  let L : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) a).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec b))
  have hL : ∀ z, jacMatrix Φ z a b - (if a = b then 1 else 0) =
      L (fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) := by
    intro z
    simp [L, jacMatrix]
  have hL1 : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    show ‖T (basisVec b) a‖ ≤ 1 * ‖T‖
    calc ‖T (basisVec b) a‖ ≤ ‖T (basisVec b)‖ := norm_le_pi_norm _ _
      _ ≤ ‖T‖ * ‖(basisVec b : Vec 2)‖ := T.le_opNorm _
      _ = 1 * ‖T‖ := by rw [ChartTransport.norm_basisVec, mul_one, one_mul]
  have hfd : ContDiff ℝ (i : ℕ∞)
      (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (h1.sub contDiff_const).of_le (by exact_mod_cast le_top)
  have e : (fun z => jacMatrix Φ z a b - (if a = b then 1 else 0)) =
      L ∘ (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) := funext hL
  rw [e]
  calc ‖iteratedFDeriv ℝ i
        (L ∘ (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2))) y‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ i
          (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) y‖ :=
        L.norm_iteratedFDeriv_comp_left hfd.contDiffAt (by exact_mod_cast le_rfl)
    _ ≤ 1 * ‖iteratedFDeriv ℝ i
          (fun z => fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Vec 2)) y‖ :=
        mul_le_mul_of_nonneg_right hL1 (norm_nonneg _)
    _ = _ := one_mul _

/-- The constants of the deviation of the chart Jacobian from the identity. -/
def chartDevConst (K : ℕ) : ℝ := 2 ^ 25 * (K.factorial : ℝ) * (2 ^ 25) ^ K

theorem chartDevConst_nonneg (K : ℕ) : 0 ≤ chartDevConst K := by
  unfold chartDevConst
  positivity

/-- **The Jacobian of a renewal chart on its anchor window** is `a_{m-1} τ_m''`-close to the
identity, with all its jets at the scale `ε_{m-1}`. -/
theorem ocChart_jac_deviation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m) (K : ℕ) (a b : Fin 2) :
    ScaledJet K (ocEpsilon q Λ (m - 1))
      (fun y => jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y a b - (if a = b then 1 else 0))
      (chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) := by
  have hEb := Scales.epsilon_basic (q := q) (Λ := Λ) (m := m - 1) hq.1 hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := hEb.1
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_nonneg hE.le _
  have hsmall : ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m| ≤ 2 ^ (-25 : ℤ) := by
    calc ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m|
        ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_le_mul_of_nonneg_left ht hA0
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
          (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ
            (by omega : 1 ≤ m)).2.2.2.2.1
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hE.le hEb.2.1 (by linarith))
            (by positivity)
      _ = 2 ^ (-25 : ℤ) := mul_one _
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m (Φ (m - 1)) hφ l t) :=
    contDiff_streamFlow_slice hφ t _
  refine ⟨contDiff_natCast_of_top ((contDiff_jacMatrix hchart a b).sub contDiff_const) K,
    fun y i hi => ?_⟩
  have h1 := norm_iteratedFDeriv_jac_sub_le hchart i a b y
  have h2 := oc_flow_jets_explicit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ t
    ((l : ℝ) * ocTauPP α q Λ m) hsmall i y
  have e : ocEpsilon q Λ (m - 1) ^ i * ((2 : ℝ) ^ 25 / ocEpsilon q Λ (m - 1)) ^ i =
      (2 ^ 25) ^ i := by
    rw [← mul_pow, mul_div_cancel₀ _ hE.ne']
  have hf : (i.factorial : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_le hi
  have hp : ((2 : ℝ) ^ 25) ^ i ≤ (2 ^ 25) ^ K := pow_le_pow_right₀ (by norm_num) hi
  have ha : ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m| ≤
      ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_le_mul_of_nonneg_left ht hA0
  have ha0 : 0 ≤ ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m| :=
    mul_nonneg hA0 (abs_nonneg _)
  calc ocEpsilon q Λ (m - 1) ^ i * ‖iteratedFDeriv ℝ i
        (fun y => jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y a b -
          (if a = b then 1 else 0)) y‖
      ≤ ocEpsilon q Λ (m - 1) ^ i * (2 ^ 25 * (i.factorial : ℝ) *
          (2 ^ 25 / ocEpsilon q Λ (m - 1)) ^ i *
          (ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m|)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hE.le i)
    _ = 2 ^ 25 * (i.factorial : ℝ) *
          (ocEpsilon q Λ (m - 1) ^ i * ((2 : ℝ) ^ 25 / ocEpsilon q Λ (m - 1)) ^ i) *
          (ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m|) := by ring
    _ = 2 ^ 25 * (i.factorial : ℝ) * (2 ^ 25) ^ i *
          (ocA α q Λ (m - 1) * |t - (l : ℝ) * ocTauPP α q Λ m|) := by rw [e]
    _ ≤ 2 ^ 25 * (K.factorial : ℝ) * (2 ^ 25) ^ K *
          (ocA α q Λ (m - 1) * ocTauPP α q Λ m) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hp
          (by positivity) (by positivity)) ha ha0 (by positivity)

/-! ### The material metric of a unimodular chart -/

/-- The inverse of a unimodular `2 × 2` matrix. -/
theorem inv_fin_two_of_det_one {M : Matrix (Fin 2) (Fin 2) ℝ} (hdet : M.det = 1) :
    M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]

/-- `N Nᵀ - I` in terms of `F = N - I`: `F + Fᵀ + F Fᵀ`. -/
theorem metric_dev_identity (N : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (N * N.transpose) i j - (if i = j then 1 else 0) =
      (N i j - (if i = j then 1 else 0)) + (N j i - (if j = i then 1 else 0)) +
        ((N i 0 - (if i = 0 then 1 else 0)) * (N j 0 - (if j = 0 then 1 else 0)) +
          (N i 1 - (if i = 1 then 1 else 0)) * (N j 1 - (if j = 1 then 1 else 0))) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The material metric `F⁻¹F⁻ᵀ` of a unimodular chart whose Jacobian is `gd`-close to the
identity is close to the identity. -/
theorem scaledJet_metric_deviation {Φ : Vec 2 → Vec 2} (hdet : ∀ y, (jacMatrix Φ y).det = 1)
    {K : ℕ} {s gd : ℝ} (hs : 0 < s)
    (hdev : ∀ a b : Fin 2, ScaledJet K s
      (fun y => jacMatrix Φ y a b - (if a = b then 1 else 0)) gd) (i j : Fin 2) :
    ScaledJet K s
      (fun y => ((jacMatrix Φ y)⁻¹ * ((jacMatrix Φ y)⁻¹).transpose) i j -
        (if i = j then 1 else 0))
      (gd + gd + (2 ^ K * ((K : ℝ) + 1) * gd * gd + 2 ^ K * ((K : ℝ) + 1) * gd * gd)) := by
  have h00 : ScaledJet K s
      (fun y => (jacMatrix Φ y)⁻¹ 0 0 - (if (0 : Fin 2) = 0 then 1 else 0)) gd := by
    have e : (fun y => (jacMatrix Φ y)⁻¹ 0 0 - (if (0 : Fin 2) = 0 then (1 : ℝ) else 0)) =
        fun y => jacMatrix Φ y 1 1 - (if (1 : Fin 2) = 1 then 1 else 0) := by
      funext y
      rw [inv_fin_two_of_det_one (hdet y)]
      simp
    rw [e]
    exact hdev 1 1
  have h11 : ScaledJet K s
      (fun y => (jacMatrix Φ y)⁻¹ 1 1 - (if (1 : Fin 2) = 1 then 1 else 0)) gd := by
    have e : (fun y => (jacMatrix Φ y)⁻¹ 1 1 - (if (1 : Fin 2) = 1 then (1 : ℝ) else 0)) =
        fun y => jacMatrix Φ y 0 0 - (if (0 : Fin 2) = 0 then 1 else 0) := by
      funext y
      rw [inv_fin_two_of_det_one (hdet y)]
      simp
    rw [e]
    exact hdev 0 0
  have h01 : ScaledJet K s
      (fun y => (jacMatrix Φ y)⁻¹ 0 1 - (if (0 : Fin 2) = 1 then 1 else 0)) gd := by
    have e : (fun y => (jacMatrix Φ y)⁻¹ 0 1 - (if (0 : Fin 2) = 1 then (1 : ℝ) else 0)) =
        fun y => (-1 : ℝ) • (jacMatrix Φ y 0 1 - (if (0 : Fin 2) = 1 then 1 else 0)) := by
      funext y
      rw [inv_fin_two_of_det_one (hdet y)]
      simp
    rw [e]
    exact scaledJet_mono (scaledJet_const_smul (-1) (hdev 0 1)) (by simp)
  have h10 : ScaledJet K s
      (fun y => (jacMatrix Φ y)⁻¹ 1 0 - (if (1 : Fin 2) = 0 then 1 else 0)) gd := by
    have e : (fun y => (jacMatrix Φ y)⁻¹ 1 0 - (if (1 : Fin 2) = 0 then (1 : ℝ) else 0)) =
        fun y => (-1 : ℝ) • (jacMatrix Φ y 1 0 - (if (1 : Fin 2) = 0 then 1 else 0)) := by
      funext y
      rw [inv_fin_two_of_det_one (hdet y)]
      simp
    rw [e]
    exact scaledJet_mono (scaledJet_const_smul (-1) (hdev 1 0)) (by simp)
  have hF : ∀ a b : Fin 2, ScaledJet K s
      (fun y => (jacMatrix Φ y)⁻¹ a b - (if a = b then 1 else 0)) gd := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have e : (fun y => ((jacMatrix Φ y)⁻¹ * ((jacMatrix Φ y)⁻¹).transpose) i j -
        (if i = j then (1 : ℝ) else 0)) =
      fun y => ((jacMatrix Φ y)⁻¹ i j - (if i = j then 1 else 0)) +
        ((jacMatrix Φ y)⁻¹ j i - (if j = i then 1 else 0)) +
        (((jacMatrix Φ y)⁻¹ i 0 - (if i = 0 then 1 else 0)) *
            ((jacMatrix Φ y)⁻¹ j 0 - (if j = 0 then 1 else 0)) +
          ((jacMatrix Φ y)⁻¹ i 1 - (if i = 1 then 1 else 0)) *
            ((jacMatrix Φ y)⁻¹ j 1 - (if j = 1 then 1 else 0))) :=
    funext fun y => metric_dev_identity _ i j
  rw [e]
  exact scaledJet_add hs.le (scaledJet_add hs.le (hF i j) (hF j i))
    (scaledJet_add hs.le (scaledJet_smul hs (hF i 0) (hF j 0))
      (scaledJet_smul hs (hF i 1) (hF j 1)))

/-- The constants of the deviation of the material metric from the identity. -/
def metricDevConst (K : ℕ) : ℝ :=
  2 * chartDevConst K + 2 * (2 ^ K * ((K : ℝ) + 1)) * chartDevConst K ^ 2

theorem metricDevConst_nonneg (K : ℕ) : 0 ≤ metricDevConst K := by
  have := chartDevConst_nonneg K
  unfold metricDevConst
  positivity

/-- **The material metric of a renewal chart on its anchor window** is `a_{m-1} τ_m''`-close to
the identity, with all its jets at the scale `ε_{m-1}`. -/
theorem ocMaterialMetric_deviation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 2 ≤ m)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (l : ℤ) (t : ℝ)
    (ht : |t - (l : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m) (K : ℕ) (i j : Fin 2) :
    ScaledJet K (ocEpsilon q Λ (m - 1))
      (fun y => ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y i j - (if i = j then 1 else 0))
      (metricDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) := by
  have hEb := Scales.epsilon_basic (q := q) (Λ := Λ) (m := m - 1) hq.1 hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := hEb.1
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_nonneg hE.le _
  have hτ0 : 0 ≤ ocTauPP α q Λ m := (abs_nonneg _).trans ht
  have hg0 : 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_nonneg hA0 hτ0
  have hg1 : ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ 1 := by
    calc ocA α q Λ (m - 1) * ocTauPP α q Λ m
        ≤ (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
          (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ
            (by omega : 1 ≤ m)).2.2.2.2.1
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hE.le hEb.2.1 (by linarith))
            (by positivity)
      _ ≤ 1 := by norm_num
  have hc0 := chartDevConst_nonneg K
  have h := scaledJet_metric_deviation
    (fun y => ocChart_det hφ α q Λ m l t y) hE
    (fun a b => ocChart_jac_deviation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm hφ l t ht K
      a b) i j
  refine scaledJet_mono h ?_
  have hsq : (ocA α q Λ (m - 1) * ocTauPP α q Λ m) ^ 2 ≤
      ocA α q Λ (m - 1) * ocTauPP α q Λ m := by
    rw [sq]
    exact mul_le_of_le_one_right hg0 hg1
  have hK0 : 0 ≤ 2 * (2 ^ K * ((K : ℝ) + 1)) * chartDevConst K ^ 2 := by positivity
  calc chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) +
        chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) +
        (2 ^ K * ((K : ℝ) + 1) * (chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) *
            (chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) +
          2 ^ K * ((K : ℝ) + 1) * (chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) *
            (chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)))
      = 2 * chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) +
          2 * (2 ^ K * ((K : ℝ) + 1)) * chartDevConst K ^ 2 *
            (ocA α q Λ (m - 1) * ocTauPP α q Λ m) ^ 2 := by ring
    _ ≤ 2 * chartDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) +
          2 * (2 ^ K * ((K : ℝ) + 1)) * chartDevConst K ^ 2 *
            (ocA α q Λ (m - 1) * ocTauPP α q Λ m) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hK0)
    _ = metricDevConst K * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by
        unfold metricDevConst
        ring
end

end AVRegularity.CycleComparison.Charts
end
end
