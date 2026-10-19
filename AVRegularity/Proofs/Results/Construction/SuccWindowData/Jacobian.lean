-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.Construction.ChainGeometry.Offset
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Construction.StrainPhysical.Context
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

section
open Homogenization AVenhance AVRegularity
namespace AVRegularity.Providers.SuccWindow

/-! Joint `C¹` regularity of the offset flows of a real chain: for every fixed anchor `r`, the map
`(u, x) ↦ 𝔛(u, x, r)` of the chain geometry is `C¹`. The base flow is a stream flow (jointly
smooth); each child composes the parent flow with the relative displacement of a shear pulse,
which is `C¹` in `(u, θ)` because the pulse is continuous (fundamental theorem of calculus) and
the shear velocity is smooth. -/

/-- The offset flow of a geometry is jointly `C¹` in `(u, x)` at every fixed anchor. -/
def GeomC1 (g : ChainGeom) : Prop :=
  ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r)

/-- The shear velocity of a pulse is `C¹`. -/
theorem contDiff_ocShearVel (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    ContDiff ℝ 1 (ocShearVel α q Λ m k) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) :=
    AVRegularity.CycleReference.ocShear_contDiff α q Λ m k
  have hc : ContDiff ℝ 1 (fderiv ℝ (ocShear α q Λ m k)) :=
    (hψ.fderiv_right (m := 1) (by simp)).of_le le_rfl
  have hg : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => spaceGrad (ocShear α q Λ m k) y j) := fun j =>
    hc.clm_apply contDiff_const
  change ContDiff ℝ 1 (fun y => sigmaMat.mulVec (spaceGrad (ocShear α q Λ m k) y))
  refine contDiff_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (contDiff_const.mul (hg 0)).add (contDiff_const.mul (hg 1))

/-- The relative displacement is `C¹` in `(u, θ)`. -/
theorem contDiff_relDisp (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (r : ℝ) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r p.2) := by
  have hc : Continuous (ocPulse D.α D.q D.Λ D.ζ k pk) :=
    AVRegularity.CycleReference.ocPulse_continuous hζ pk
  have hF : ContDiff ℝ 1 (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) := by
    rw [contDiff_one_iff_deriv]
    have hd : ∀ u, HasDerivAt (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v)
        (ocPulse D.α D.q D.Λ D.ζ k pk u) u := fun u =>
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    refine ⟨fun u => (hd u).differentiableAt, ?_⟩
    have : deriv (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) =
        ocPulse D.α D.q D.Λ D.ζ k pk := funext fun u => (hd u).deriv
    rw [this]; exact hc
  unfold OCData.relDisp
  exact ((hF.comp contDiff_fst).smul
    ((contDiff_ocShearVel _ _ _ _ _).comp (contDiff_snd.const_smul _))).const_smul _

theorem geomC1_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hg : GeomC1 g) : GeomC1 (D.childGeom k pk s' c g) := by
  intro r
  have hA : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 g.2.2 p.2 r) :=
    (hg r).comp (contDiff_const.prodMk contDiff_snd)
  have hR : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r
      ((D.eps k)⁻¹ • g.1 g.2.2 p.2 r + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) :=
    (contDiff_relDisp D hζ k pk r).comp
      (contDiff_fst.prodMk ((hA.const_smul _).add contDiff_const))
  exact (hg g.2.2).comp (contDiff_fst.prodMk (hA.add (hR.const_smul _)))

theorem geomC1_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomC1 g → GeomC1 (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact geomC1_geomAux D hζ cs (k + 1) (pk1 :: rest) (geomC1_childGeom D hζ k pk _ c hg)

/-- **The chain geometry is jointly `C¹`.** -/
theorem geomC1_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    GeomC1 (ch.geom D) := by
  refine geomC1_geomAux D hζ _ _ _ ?_
  intro r
  have h := AVRegularity.CycleReference.streamFlow_joint_smooth (D.hΦ ch.baseLevel)
  exact ((h.of_le (by exact_mod_cast le_top)).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))

end AVRegularity.Providers.SuccWindow
end

section
open Homogenization
namespace AVRegularity.Providers.SuccWindow

/-! The Jacobian of an offset flow and the window bounds of its molecular metric.

If `(u, x) ↦ 𝔛(u, x, s)` is `C¹` and the flow has the inverse law, then `F_u = D_x𝔛(u, x_𝒜, s)`
is continuous in `u` and invertible (its left inverse is the Jacobian of `𝔛(s, ·, u)`). The metric
`𝒢_u = F_u⁻¹F_u⁻ᵀ` is then continuous, and on a compact time window it is uniformly elliptic,
`𝒢 ≥ (4M²+1)⁻¹` with `M` a bound for the entries of `F`, with bounded entries. -/

/-- The Jacobian of the slice `y ↦ 𝔛(u, y, s)` is continuous in `u`. -/
theorem jac_continuous {f : ℝ → Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => f p.1 p.2)) (x : Vec 2) :
    Continuous (fun u => jacMatrix (f u) x) := by
  have hd : Differentiable ℝ (fun p : ℝ × Vec 2 => f p.1 p.2) := hf.differentiable (by norm_num)
  have hcf : Continuous (fun p : ℝ × Vec 2 => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) p) :=
    hf.continuous_fderiv (by norm_num)
  have hentry : ∀ i j : Fin 2, Continuous (fun u => jacMatrix (f u) x i j) := by
    intro i j
    have heq : (fun u => jacMatrix (f u) x i j) =
        fun u => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) (u, x) (0, basisVec j) i := by
      funext u
      simp only [jacMatrix, Matrix.of_apply]
      rw [AVRegularity.StrainPhysical.fderiv_slice_gen hd u x (basisVec j)]
    rw [heq]
    have h1 : Continuous (fun u : ℝ => fderiv ℝ (fun q : ℝ × Vec 2 => f q.1 q.2) (u, x)) :=
      hcf.comp (continuous_id.prodMk continuous_const)
    exact (continuous_apply i).comp (h1.clm_apply continuous_const)
  exact continuous_pi fun i => continuous_pi fun j => hentry i j

/-- Under the inverse law, the Jacobian of the slice has a left inverse, hence a unit
determinant. -/
theorem jac_isUnit_det {g : ChainGeom} (hinv : AVRegularity.ChainGeometry.InvLaw g)
    (hC : ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r)) (u s : ℝ) (x : Vec 2) :
    IsUnit (jacMatrix (fun y => g.1 u y s) x).det := by
  have hdiff : ∀ a r : ℝ, Differentiable ℝ (fun y => g.1 a y r) := by
    intro a r
    have h := (hC r).differentiable (by norm_num)
    exact h.comp ((differentiable_const a).prodMk differentiable_id)
  have hcomp : (fun w => g.1 s w u) ∘ (fun y => g.1 u y s) = id := by
    funext y
    exact hinv s u y
  have hJ := AVRegularity.CycleReference.jacMatrix_comp (f := fun w => g.1 s w u)
    (g := fun y => g.1 u y s) x (hdiff s u _) (hdiff u s x)
  rw [hcomp, AVRegularity.CycleReference.jacMatrix_identity] at hJ
  exact Matrix.isUnit_det_of_left_inverse hJ.symm

/-- The inverse of a continuous family of invertible matrices is continuous. -/
theorem continuous_inv_of_det {F : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hF : Continuous F)
    (hdet : ∀ u, IsUnit (F u).det) : Continuous (fun u => (F u)⁻¹) := by
  have heq : (fun u => (F u)⁻¹) = fun u => ((F u).det)⁻¹ • (F u).adjugate := by
    funext u
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [heq]
  exact ((hF.matrix_det).inv₀ fun u => (hdet u).ne_zero).smul hF.matrix_adjugate

/-- A continuous function on a compact interval is bounded. -/
theorem exists_bound_Icc {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |φ t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  have := hM t ht
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Algebraic ellipticity: if `A F = 1` and the entries of `F` are bounded by `M`, then
`ξ·(AAᵀ)ξ ≥ (4M²+1)⁻¹|ξ|²`. -/
theorem metric_elliptic {F A : Matrix (Fin 2) (Fin 2) ℝ} (hAF : A * F = 1) {M : ℝ}
    (hM : ∀ i j, |F i j| ≤ M) (ξ : Fin 2 → ℝ) :
    (4 * M ^ 2 + 1)⁻¹ * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j := by
  set η : Fin 2 → ℝ := fun k => ∑ i, A i k * ξ i with hη
  have hquad : ∑ i, ∑ j, (A * A.transpose) i j * ξ i * ξ j = ∑ k, η k ^ 2 := by
    simp only [hη, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  -- `ξ = Fᵀη`
  have hE : ∀ l i, A l 0 * F 0 i + A l 1 * F 1 i = if l = i then 1 else 0 := by
    intro l i
    have := congrFun (congrFun hAF l) i
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have e00 := hE 0 0
  have e01 := hE 0 1
  have e10 := hE 1 0
  have e11 := hE 1 1
  simp only [ite_true, show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    ite_false] at e00 e01 e10 e11
  have hξ0 : ξ 0 = ∑ k, F k 0 * η k := by
    simp only [hη, Fin.sum_univ_two]
    linear_combination (-(ξ 0)) * e00 - ξ 1 * e10
  have hξ1 : ξ 1 = ∑ k, F k 1 * η k := by
    simp only [hη, Fin.sum_univ_two]
    linear_combination (-(ξ 0)) * e01 - ξ 1 * e11
  have hξ : ∀ i, ξ i = ∑ k, F k i * η k := Fin.forall_fin_two.mpr ⟨hξ0, hξ1⟩
  have hMsq : ∀ i j, F i j ^ 2 ≤ M ^ 2 := fun i j => by
    have := hM i j
    have h0 : 0 ≤ |F i j| := abs_nonneg _
    nlinarith [sq_abs (F i j)]
  have hcs : ∀ i, ξ i ^ 2 ≤ 2 * M ^ 2 * ∑ k, η k ^ 2 := by
    intro i
    rw [hξ i]
    simp only [Fin.sum_univ_two]
    have h0 := hMsq 0 i
    have h1 := hMsq 1 i
    nlinarith [sq_nonneg (F 0 i * η 1 - F 1 i * η 0), sq_nonneg (η 0), sq_nonneg (η 1)]
  have hsum : ∑ i, ξ i ^ 2 ≤ 4 * M ^ 2 * ∑ k, η k ^ 2 := by
    simp only [Fin.sum_univ_two] at hcs ⊢
    nlinarith [hcs 0, hcs 1]
  rw [hquad]
  have hpos : 0 < 4 * M ^ 2 + 1 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  have hη0 : 0 ≤ ∑ k, η k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith

/-- Entry bound of `AAᵀ` from an entry bound of `A`. -/
theorem metric_entry_le {A : Matrix (Fin 2) (Fin 2) ℝ} {N : ℝ} (hN : ∀ i j, |A i j| ≤ N)
    (i j : Fin 2) : |(A * A.transpose) i j| ≤ 2 * N ^ 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN 0 0)
  calc |A i 0 * A j 0 + A i 1 * A j 1| ≤ |A i 0| * |A j 0| + |A i 1| * |A j 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ N * N + N * N := by
        gcongr <;> exact hN _ _
    _ = 2 * N ^ 2 := by ring

end AVRegularity.Providers.SuccWindow
end
