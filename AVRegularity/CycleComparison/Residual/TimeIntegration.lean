-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.FDeriv.Partial
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation

section
@[expose] public section
namespace AVRegularity

/-! Abstract real identities for the scale conversions of the residual bounds:

`(e/(√ν ℓ²)) ε_c^{N+1} ρ/√B = ε_c^N` and `ℓ^{-2} ε_c^{N+1} ϑ^A ρ √|I| /√B = ε_c^N Z`,
using `e = ℓ√ν` and `ε_c ρ = ℓ√B`. -/

theorem residual_scale_flux {ν B ρ ℓ e εc Q₁ Q₂ : ℝ} (hν : 0 < ν) (hB : 0 < B) (hℓ : 0 < ℓ)
    (he : e = ℓ * Real.sqrt ν) (hεc : εc * ρ = ℓ * Real.sqrt B) (N : ℕ) :
    (Real.sqrt ν)⁻¹ * ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * Q₁ * Q₂) * (Real.sqrt B)⁻¹ =
      εc ^ N * Q₁ * Q₂ := by
  have hsν := Real.sqrt_pos.2 hν
  have hsB := Real.sqrt_pos.2 hB
  have key : (Real.sqrt ν)⁻¹ * (ℓ ^ 2)⁻¹ * (εc * ρ) * e * (Real.sqrt B)⁻¹ = 1 := by
    rw [hεc, he]; field_simp
  calc (Real.sqrt ν)⁻¹ * ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * Q₁ * Q₂) * (Real.sqrt B)⁻¹
      = εc ^ N * Q₁ * Q₂ * ((Real.sqrt ν)⁻¹ * (ℓ ^ 2)⁻¹ * (εc * ρ) * e * (Real.sqrt B)⁻¹) := by
        ring
    _ = _ := by rw [key, mul_one]

theorem residual_scale_scalar {B ρ ℓ εc w T Q₁ Q₂ : ℝ} (hB : 0 < B) (hℓ : 0 < ℓ)
    (hεc : εc * ρ = ℓ * Real.sqrt B) (N : ℕ) :
    (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * w * ρ * Q₁ * Q₂ * T * (Real.sqrt B)⁻¹ =
      εc ^ N * (T / ℓ * w) * Q₁ * Q₂ := by
  have hsB := Real.sqrt_pos.2 hB
  have key : (ℓ ^ 2)⁻¹ * (εc * ρ) * (Real.sqrt B)⁻¹ = ℓ⁻¹ := by
    rw [hεc]; field_simp
  calc (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * w * ρ * Q₁ * Q₂ * T * (Real.sqrt B)⁻¹
      = εc ^ N * w * Q₁ * Q₂ * T * ((ℓ ^ 2)⁻¹ * (εc * ρ) * (Real.sqrt B)⁻¹) := by ring
    _ = _ := by rw [key]; ring

end AVRegularity
end
end

section
@[expose] public section
open scoped ENNReal NNReal
open Finset
namespace AVRegularity

/-! Elementary finite-sum inequalities in `ℝ≥0∞` used by the residual estimates. -/

/-- Cauchy–Schwarz for a finite sum in `ℝ≥0∞`. -/
theorem ennreal_sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  classical
  by_cases h : ∀ i ∈ s, f i ≠ ⊤
  · have hs : ∀ i ∈ s, f i = ((f i).toNNReal : ℝ≥0∞) := fun i hi => (ENNReal.coe_toNNReal (h i hi)).symm
    have key := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => (f i).toNNReal)
    have e1 : ∑ i ∈ s, f i = ((∑ i ∈ s, (f i).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofNNReal_finsetSum]; exact Finset.sum_congr rfl hs
    have e2 : ∑ i ∈ s, f i ^ 2 = ((∑ i ∈ s, (f i).toNNReal ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      push_cast; exact Finset.sum_congr rfl fun i hi => by rw [← hs i hi]
    rw [e1, e2]
    exact_mod_cast key
  · push Not at h
    obtain ⟨i, hi, hfi⟩ := h
    have hcard : (#s : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
      exact Finset.nonempty_iff_ne_empty.1 ⟨i, hi⟩
    have htop : ∑ i ∈ s, f i ^ 2 = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨i, hi, by simp [hfi]⟩
    rw [htop, ENNReal.mul_top hcard]
    exact le_top

/-- `(a + b)² ≤ 2 (a² + b²)` in `ℝ≥0∞`. -/
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have := ennreal_sq_sum_le_card_mul_sum_sq (Finset.univ : Finset Bool) (fun i => if i then a else b)
  simpa [add_comm] using this

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! Slow regularity of a two-scale field `f(X,y)`: `C^m` in the slow variable for each fast
point, with jointly continuous slow jets. This is the part of `IsBoxSmooth` that the residual
estimates use; the slow cell of the sampling inequality is also defined here. -/

/-- `X ↦ f X y` is `C^m` for each `y`, and the slow jets `D_X^a f` (`a ≤ m`) are jointly
continuous in `(X,y)`. -/
def IsSlowSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    (f : Vec 2 → Vec 2 → E) : Prop :=
  (∀ y, ContDiff ℝ (m : ℕ∞) (fun X => f X y)) ∧
  ∀ a, a ≤ m → Continuous (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => f X p.2) p.1)

/-- The slow period cell `[0, ρ⁻¹]²` of `a_ρ(X) = a(ρX)` for a `ℤ²`-periodic `a`. -/
def slowCell (ρ : ℝ) : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) ρ⁻¹

/-! The two-scale chain rule `∂_{x_k}[V(x/ρ, x/e)] = ρ⁻¹ (∂_{X_k}V)_diag + e⁻¹ (∂_{z_k}V)_diag`
for a field that is box smooth of slow and fast order at least one: the continuous partial
derivatives make the field jointly (strictly) differentiable. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative read off from the first jet of the zeroth jet. -/
theorem fderiv_eq_curry_iteratedFDeriv_one_zero (g : Vec 2 → E) (X : Vec 2) :
    fderiv ℝ g X =
      ((continuousMultilinearCurryFin0 ℝ (Vec 2) E : _ ≃ₗᵢ[ℝ] E) : _ →L[ℝ] E).comp
        (continuousMultilinearCurryFin1 ℝ (Vec 2) _
          (iteratedFDeriv ℝ 1 (fun X' => iteratedFDeriv ℝ 0 g X') X)) := by
  have hcomp : (fun X' => iteratedFDeriv ℝ 0 g X') =
      ⇑(continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘ g := rfl
  ext v
  simp only [ContinuousLinearMap.comp_apply, continuousMultilinearCurryFin1_apply,
    iteratedFDeriv_one_apply, hcomp, LinearIsometryEquiv.comp_fderiv]
  simp

/-- The derivative read off from the first jet. -/
theorem fderiv_eq_curry_iteratedFDeriv_one (g : Vec 2 → E) (z : Vec 2) :
    fderiv ℝ g z = continuousMultilinearCurryFin1 ℝ (Vec 2) E (iteratedFDeriv ℝ 1 g z) := by
  ext v
  simp [continuousMultilinearCurryFin1_apply]

/-- The derivative of a coordinate component is the component of the derivative. -/
theorem fderiv_component_apply {g : Vec 2 → Fin 2 → E} {x : Vec 2}
    (hg : DifferentiableAt ℝ g x) (k : Fin 2) (v : Vec 2) :
    fderiv ℝ (fun y => g y k) x v = fderiv ℝ g x v k := by
  rw [fderiv_apply hg k]
  rfl

namespace IsBoxSmooth

variable {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}

/-- Box smoothness is preserved by sums. -/
theorem add {g : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f) (hg : IsBoxSmooth sX sZ g) :
    IsBoxSmooth sX sZ (fun X z => f X z + g X z) := by
  have hsum : ∀ b, b ≤ sZ → ∀ X z, iteratedFDeriv ℝ b (fun z' => f X z' + g X z') z =
      iteratedFDeriv ℝ b (f X) z + iteratedFDeriv ℝ b (g X) z := by
    intro b hb X z
    exact iteratedFDeriv_add_apply
      (((hf.1 X).of_le (by exact_mod_cast hb : ((b : ℕ∞) : WithTop ℕ∞) ≤ ((sZ : ℕ∞) : WithTop ℕ∞))).contDiffAt)
      (((hg.1 X).of_le (by exact_mod_cast hb : ((b : ℕ∞) : WithTop ℕ∞) ≤ ((sZ : ℕ∞) : WithTop ℕ∞))).contDiffAt)
  refine ⟨fun X => (hf.1 X).add (hg.1 X), fun b hb z => ?_, fun a b ha hb => ?_⟩
  · simp_rw [hsum b hb]
    exact (hf.2.1 b hb z).add (hg.2.1 b hb z)
  · have hrw : (fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (fun z' => f X' z' + g X' z') p.2) p.1) =
        fun p => iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) p.1 +
          iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (g X') p.2) p.1 := by
      funext p
      simp_rw [hsum b hb]
      exact iteratedFDeriv_add_apply
        (((hf.2.1 b hb p.2).of_le
          (by exact_mod_cast ha : ((a : ℕ∞) : WithTop ℕ∞) ≤ ((sX : ℕ∞) : WithTop ℕ∞))).contDiffAt)
        (((hg.2.1 b hb p.2).of_le
          (by exact_mod_cast ha : ((a : ℕ∞) : WithTop ℕ∞) ≤ ((sX : ℕ∞) : WithTop ℕ∞))).contDiffAt)
    rw [hrw]
    exact (hf.2.2 a b ha hb).add (hg.2.2 a b ha hb)

theorem contDiff_slow (hf : IsBoxSmooth sX sZ f) (z : Vec 2) :
    ContDiff ℝ (sX : ℕ∞) (fun X => f X z) := by
  have h := hf.2.1 0 (Nat.zero_le _) z
  have : (fun X => f X z) =
      ⇑(continuousMultilinearCurryFin0 ℝ (Vec 2) E) ∘ (fun X => iteratedFDeriv ℝ 0 (f X) z) := by
    funext X; simp
  rw [this]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).contDiff.comp h

theorem continuous_fderiv_slow (hf : IsBoxSmooth sX sZ f) (hX : 1 ≤ sX) :
    Continuous (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => f X p.2) p.1) := by
  have h := hf.2.2 1 0 hX (Nat.zero_le _)
  have : (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => f X p.2) p.1) = fun p =>
      ((continuousMultilinearCurryFin0 ℝ (Vec 2) E : _ ≃ₗᵢ[ℝ] E) : _ →L[ℝ] E).comp
        (continuousMultilinearCurryFin1 ℝ (Vec 2) _
          (iteratedFDeriv ℝ 1 (fun X' => iteratedFDeriv ℝ 0 (f X') p.2) p.1)) := by
    funext p
    exact fderiv_eq_curry_iteratedFDeriv_one_zero (fun X => f X p.2) p.1
  rw [this]
  exact continuous_const.clm_comp
    ((continuousMultilinearCurryFin1 ℝ (Vec 2) _).continuous.comp h)

theorem continuous_fderiv_fast (hf : IsBoxSmooth sX sZ f) (hZ : 1 ≤ sZ) :
    Continuous (fun p : Vec 2 × Vec 2 => fderiv ℝ (f p.1) p.2) := by
  have h := hf.2.2 0 1 (Nat.zero_le _) hZ
  have : (fun p : Vec 2 × Vec 2 => fderiv ℝ (f p.1) p.2) = fun p =>
      continuousMultilinearCurryFin1 ℝ (Vec 2) E
        (continuousMultilinearCurryFin0 ℝ (Vec 2) _
          (iteratedFDeriv ℝ 0 (fun X' => iteratedFDeriv ℝ 1 (f X') p.2) p.1)) := by
    funext p
    rw [fderiv_eq_curry_iteratedFDeriv_one]
    simp
  rw [this]
  exact (continuousMultilinearCurryFin1 ℝ (Vec 2) E).continuous.comp
    ((continuousMultilinearCurryFin0 ℝ (Vec 2) _).continuous.comp h)

/-- Continuous partial derivatives: joint differentiability. -/
theorem hasFDerivAt_uncurry (hf : IsBoxSmooth sX sZ f) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (u : Vec 2 × Vec 2) :
    HasFDerivAt (Function.uncurry f)
      ((fderiv ℝ (fun X => f X u.2) u.1).coprod (fderiv ℝ (f u.1) u.2)) u := by
  have hsX : ((sX : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sX ≠ 0)
  have hsZ : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sZ ≠ 0)
  have hs := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := u) (f := f)
    (f₁ := fun X z => fderiv ℝ (fun X' => f X' z) X) (f₂ := fun X z => fderiv ℝ (f X) z)
    (Filter.Eventually.of_forall fun v =>
      ((hf.contDiff_slow v.2).differentiable hsX v.1).hasFDerivAt)
    (Filter.Eventually.of_forall fun v =>
      ((hf.1 v.1).differentiable hsZ v.2).hasFDerivAt)
    (hf.continuous_fderiv_slow hX).continuousAt (hf.continuous_fderiv_fast hZ).continuousAt
  exact hs.hasFDerivAt

/-- The two-scale chain rule along a coordinate direction. -/
theorem fderiv_diag (hf : IsBoxSmooth sX sZ f) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (ρ e : ℝ)
    (x v : Vec 2) :
    fderiv ℝ (fun x' => f (ρ⁻¹ • x') (e⁻¹ • x')) x v =
      ρ⁻¹ • fderiv ℝ (fun X => f X (e⁻¹ • x)) (ρ⁻¹ • x) v
        + e⁻¹ • fderiv ℝ (f (ρ⁻¹ • x)) (e⁻¹ • x) v := by
  have hg : HasFDerivAt (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x'))
      ((ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).prod (e⁻¹ • ContinuousLinearMap.id ℝ (Vec 2))) x :=
    ((ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.const_smul ρ⁻¹).prodMk
      ((ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.const_smul e⁻¹)
  have hc := (hf.hasFDerivAt_uncurry hX hZ (ρ⁻¹ • x, e⁻¹ • x)).comp x hg
  have heq : (fun x' => f (ρ⁻¹ • x') (e⁻¹ • x')) =
      Function.uncurry f ∘ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) := rfl
  rw [heq, hc.fderiv]
  simp

/-- The two-scale chain rule for a coordinate component of a vector field. -/
theorem fderiv_diag_component {V : Vec 2 → Vec 2 → Fin 2 → E} (hV : IsBoxSmooth sX sZ V)
    (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (ρ e : ℝ) (x : Vec 2) (k : Fin 2) (v : Vec 2) :
    fderiv ℝ (fun x' => V (ρ⁻¹ • x') (e⁻¹ • x') k) x v =
      ρ⁻¹ • fderiv ℝ (fun X => V X (e⁻¹ • x) k) (ρ⁻¹ • x) v
        + e⁻¹ • fderiv ℝ (fun z => V (ρ⁻¹ • x) z k) (e⁻¹ • x) v := by
  have hsX : ((sX : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sX ≠ 0)
  have hsZ : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : sZ ≠ 0)
  have hdiag : DifferentiableAt ℝ (fun x' => V (ρ⁻¹ • x') (e⁻¹ • x')) x := by
    have hg : DifferentiableAt ℝ (fun x' : Vec 2 => (ρ⁻¹ • x', e⁻¹ • x')) x := by fun_prop
    exact (hV.hasFDerivAt_uncurry hX hZ _).differentiableAt.comp x hg
  have hslow : DifferentiableAt ℝ (fun X => V X (e⁻¹ • x)) (ρ⁻¹ • x) :=
    (hV.contDiff_slow _).differentiable hsX _
  have hfast : DifferentiableAt ℝ (V (ρ⁻¹ • x)) (e⁻¹ • x) :=
    (hV.1 _).differentiable hsZ _
  rw [fderiv_component_apply hdiag, fderiv_component_apply hslow,
    fderiv_component_apply hfast, hV.fderiv_diag hX hZ]
  rfl

end IsBoxSmooth
end

end AVRegularity
end
end

section
@[expose] public section
open Homogenization Filter Topology
namespace AVRegularity

/-! Schwarz-type lemmas for box-smooth two-scale fields: closure of `IsBoxSmooth` under the
partial derivatives and linear operations, and the interchange `∂_{z_i} ∂_{X_j} = ∂_{X_j} ∂_{z_i}`
under the box regularity of order `(1,1)` (via locally uniform convergence of difference
quotients, with no joint `C^n` hypothesis). -/

section Core
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order Schwarz: the fast derivative of a slow directional derivative. -/
theorem hasFDerivAt_slowDir (f : Vec 2 → Vec 2 → E)
    (hX : ∀ z, Differentiable ℝ (fun X => f X z)) (hZ : ∀ X, Differentiable ℝ (f X))
    (hG : ∀ z, Differentiable ℝ (fun X => fderiv ℝ (f X) z))
    (hM : Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => fderiv ℝ (f X) p.2) p.1)
    (X z v : Vec 2) :
    HasFDerivAt (fun z' => fderiv ℝ (fun X' => f X' z') X v)
      (fderiv ℝ (fun X' => fderiv ℝ (f X') z) X v) z := by
  let F : ℝ → Vec 2 → E := fun h z' => h⁻¹ • (f (X + h • v) z' - f X z')
  let F' : ℝ → Vec 2 → (Vec 2 →L[ℝ] E) := fun h z' =>
    h⁻¹ • (fderiv ℝ (f (X + h • v)) z' - fderiv ℝ (f X) z')
  let Ψ' : ℝ → Vec 2 → (Vec 2 →L[ℝ] E) := fun s z' =>
    fderiv ℝ (fun X' => fderiv ℝ (f X') z') (X + s • v) v
  have hline : ∀ (s : ℝ), HasDerivAt (fun s : ℝ => X + s • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add X
  have hderivG : ∀ z' (s : ℝ),
      HasDerivAt (fun s : ℝ => fderiv ℝ (f (X + s • v)) z') (Ψ' s z') s := by
    intro z' s
    exact ((hG z' (X + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s))
  have hΨcont : Continuous (fun q : ℝ × Vec 2 => Ψ' q.1 q.2) := by
    have h1 : Continuous (fun q : ℝ × Vec 2 => (X + q.1 • v, q.2)) := by fun_prop
    have h2 := (hM.comp h1)
    exact h2.clm_apply continuous_const
  refine hasFDerivAt_of_tendstoUniformlyOnFilter (f := F) (f' := F') (l := (𝓝[≠] (0:ℝ)))
    (g := fun z' => fderiv ℝ (fun X' => f X' z') X v)
    (g' := fun z' => fderiv ℝ (fun X' => fderiv ℝ (f X') z') X v) (x := z) ?_ ?_ ?_
  · rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    have hc := Metric.continuousAt_iff.mp (hΨcont.continuousAt (x := ((0:ℝ), z))) (ε / 4)
      (by positivity)
    obtain ⟨δ, hδ, hδ'⟩ := hc
    have e1 : ∀ᶠ h in 𝓝[≠] (0:ℝ), h ∈ Metric.ball (0:ℝ) δ ∧ h ≠ 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hδ),
        self_mem_nhdsWithin] with h h1 h2 using ⟨h1, h2⟩
    have e2 : ∀ᶠ z' in 𝓝 z, z' ∈ Metric.ball z δ := Metric.ball_mem_nhds z hδ
    filter_upwards [e1.prod_mk e2] with q hq
    obtain ⟨⟨hh1, hh0⟩, hz'⟩ := hq
    set h := q.1
    set z' := q.2
    have hbound : ∀ s ∈ Metric.ball (0:ℝ) δ, ‖Ψ' s z' - Ψ' 0 z'‖ ≤ ε / 2 := by
      intro s hs
      have a1 := hδ' (x := (s, z')) (by
        rw [Prod.dist_eq]; simp only [dist_zero_right] at *
        exact max_lt (by simpa using hs) (by simpa using hz'))
      have a2 := hδ' (x := (0, z')) (by
        rw [Prod.dist_eq]
        exact max_lt (by simpa using hδ) (by simpa using hz'))
      simp only [dist_eq_norm] at a1 a2
      calc ‖Ψ' s z' - Ψ' 0 z'‖ = ‖(Ψ' s z' - Ψ' 0 z) - (Ψ' 0 z' - Ψ' 0 z)‖ := by
            congr 1; abel
        _ ≤ ‖Ψ' s z' - Ψ' 0 z‖ + ‖Ψ' 0 z' - Ψ' 0 z‖ := norm_sub_le _ _
        _ ≤ ε / 2 := by linarith
    set A := Ψ' 0 z'
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => fderiv ℝ (f (X + s • v)) z' - s • A)
      (f' := fun s => Ψ' s z' - A) (s := Metric.ball (0:ℝ) δ) (C := ε / 2) (x := 0) (y := h)
      (fun s _ => by
        have := ((hderivG z' s).sub ((hasDerivAt_id' s).smul_const A))
        rw [one_smul] at this
        exact this.hasDerivWithinAt (s := Metric.ball (0:ℝ) δ))
      (fun s hs => hbound s hs) (convex_ball _ _) (Metric.mem_ball_self hδ) hh1
    have hg : (fderiv ℝ (fun X' => fderiv ℝ (f X') z') X) v = A := by simp [A, Ψ']
    rw [hg]
    rw [dist_comm, dist_eq_norm]
    have hrw : F' h z' - Ψ' 0 z' = h⁻¹ • ((fderiv ℝ (f (X + h • v)) z' - h • A) -
        (fderiv ℝ (f (X + (0:ℝ) • v)) z' - (0:ℝ) • A)) := by
      simp only [F', zero_smul, sub_zero, smul_sub, A, smul_smul, inv_mul_cancel₀ hh0,
        one_smul]
      simp only [Ψ', zero_smul, add_zero]
      abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs]
    have hpos : 0 < |h| := abs_pos.mpr hh0
    have hmvt' : ‖(fderiv ℝ (f (X + h • v)) z' - h • A) -
        (fderiv ℝ (f (X + (0:ℝ) • v)) z' - (0:ℝ) • A)‖ ≤ ε / 2 * |h| := by
      simpa using hmvt
    calc |h|⁻¹ * ‖_‖ ≤ |h|⁻¹ * (ε / 2 * |h|) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · exact Eventually.of_forall fun q => by
      have := (((hZ (X + q.1 • v)).differentiableAt (x := q.2)).hasFDerivAt.sub
          ((hZ X).differentiableAt (x := q.2)).hasFDerivAt).const_smul q.1⁻¹
      exact this
  · refine Eventually.of_forall fun y => ?_
    have h0 : HasFDerivAt (fun X => f X y) (fderiv ℝ (fun X => f X y) X) (X + (0:ℝ) • v) := by
      simpa using ((hX y).differentiableAt (x := X)).hasFDerivAt
    have := (hasDerivAt_iff_tendsto_slope_zero.mp
      (h0.comp_hasDerivAt (0:ℝ) (hline 0)))
    simpa [F] using this
end Core

section Jets
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Applying the last argument of a jet to a direction: the jet of a directional derivative. -/
noncomputable def jetApply (b : ℕ) (v : Vec 2) : ContinuousMultilinearMap ℝ (fun _ : Fin (b + 1) => Vec 2) F →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) F :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) (Vec 2 →L[ℝ] F) F
    (ContinuousLinearMap.apply ℝ F v)).comp
    ((continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) F : _ ≃ₗᵢ[ℝ] _) : _ →L[ℝ] _)

theorem iteratedFDeriv_fderiv_apply {g : Vec 2 → F} {x : Vec 2} {b : ℕ}
    (hg : ContDiffAt ℝ ((b + 1 : ℕ) : WithTop ℕ∞) g x) (v : Vec 2) :
    iteratedFDeriv ℝ b (fun y => fderiv ℝ g y v) x = jetApply b v (iteratedFDeriv ℝ (b + 1) g x) := by
  have hfd : ContDiffAt ℝ (b : WithTop ℕ∞) (fderiv ℝ g) x := by
    have := hg.fderiv_right (m := (b : WithTop ℕ∞)) (by push_cast; exact le_rfl)
    exact this
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ F v) hfd
    (i := b) le_rfl
  have h2 : iteratedFDeriv ℝ b (fderiv ℝ g) x =
      (continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) F) (iteratedFDeriv ℝ (b + 1) g x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  have h3 : (fun y => fderiv ℝ g y v) = ⇑(ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ g := rfl
  rw [h3, h1, h2]
  rfl


theorem isSlowSmooth_clm_comp (L : F →L[ℝ] G) {m : ℕ} {g : Vec 2 → Vec 2 → F}
    (hg : IsSlowSmooth m g) : IsSlowSmooth m (fun X y => L (g X y)) := by
  refine ⟨fun y => L.contDiff.comp (hg.1 y), fun a ha => ?_⟩
  have : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => L (g X p.2)) p.1) =
      fun p => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) F G L)
        (iteratedFDeriv ℝ a (fun X => g X p.2) p.1) := by
    funext p
    exact ContinuousLinearMap.iteratedFDeriv_comp_left L (hg.1 p.2).contDiffAt
      (by exact_mod_cast ha)
  rw [this]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) F G L).continuous.comp (hg.2 a ha)

theorem isSlowSmooth_add {m : ℕ} {g₁ g₂ : Vec 2 → Vec 2 → F}
    (h₁ : IsSlowSmooth m g₁) (h₂ : IsSlowSmooth m g₂) :
    IsSlowSmooth m (fun X y => g₁ X y + g₂ X y) := by
  refine ⟨fun y => (h₁.1 y).add (h₂.1 y), fun a ha => ?_⟩
  have : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => g₁ X p.2 + g₂ X p.2) p.1) =
      fun p => iteratedFDeriv ℝ a (fun X => g₁ X p.2) p.1 +
        iteratedFDeriv ℝ a (fun X => g₂ X p.2) p.1 := by
    funext p
    exact iteratedFDeriv_add_apply ((h₁.1 p.2).contDiffAt.of_le (by exact_mod_cast ha))
      ((h₂.1 p.2).contDiffAt.of_le (by exact_mod_cast ha))
  rw [this]
  exact (h₁.2 a ha).add (h₂.2 a ha)

theorem isBoxSmooth_iff {sX sZ : ℕ} {f : Vec 2 → Vec 2 → F} :
    IsBoxSmooth sX sZ f ↔ (∀ X, ContDiff ℝ (sZ : ℕ∞) (f X)) ∧
      ∀ b, b ≤ sZ → IsSlowSmooth sX (fun X z => iteratedFDeriv ℝ b (f X) z) :=
  ⟨fun h => ⟨h.1, fun b hb => ⟨h.2.1 b hb, fun a ha => h.2.2 a b ha hb⟩⟩,
   fun h => ⟨h.1, fun b hb => (h.2 b hb).1, fun a b ha hb => (h.2 b hb).2 a ha⟩⟩

end Jets

namespace IsBoxSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}

theorem mono {sX' sZ' : ℕ} (hX : sX' ≤ sX) (hZ : sZ' ≤ sZ) (hf : IsBoxSmooth sX sZ f) :
    IsBoxSmooth sX' sZ' f :=
  ⟨fun X => (hf.1 X).of_le (by exact_mod_cast hZ),
   fun b hb z => (hf.2.1 b (hb.trans hZ) z).of_le (by exact_mod_cast hX),
   fun a b ha hb => hf.2.2 a b (ha.trans hX) (hb.trans hZ)⟩

theorem zero : IsBoxSmooth sX sZ (fun (_ _ : Vec 2) => (0 : E)) := by
  refine ⟨fun _ => contDiff_const, fun b _ z => ?_, fun a b _ _ => ?_⟩
  · simp only [iteratedFDeriv_fun_zero]; exact contDiff_const
  · simp
    exact continuous_const

theorem map_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hf : IsBoxSmooth sX sZ f)
    (L : E →L[ℝ] F) : IsBoxSmooth sX sZ (fun X z => L (f X z)) := by
  rw [isBoxSmooth_iff] at hf ⊢
  refine ⟨fun X => L.contDiff.comp (hf.1 X), fun b hb => ?_⟩
  have : (fun X z => iteratedFDeriv ℝ b (fun z' => L (f X z')) z) =
      fun X z => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin b => Vec 2) E F L)
        (iteratedFDeriv ℝ b (f X) z) := by
    funext X z
    exact ContinuousLinearMap.iteratedFDeriv_comp_left L (hf.1 X).contDiffAt (by exact_mod_cast hb)
  rw [this]
  exact isSlowSmooth_clm_comp _ (hf.2 b hb)

theorem neg (hf : IsBoxSmooth sX sZ f) : IsBoxSmooth sX sZ (fun X z => -f X z) :=
  hf.map_clm (-ContinuousLinearMap.id ℝ E)

theorem const_smul (c : ℝ) (hf : IsBoxSmooth sX sZ f) :
    IsBoxSmooth sX sZ (fun X z => c • f X z) :=
  hf.map_clm (c • ContinuousLinearMap.id ℝ E)

theorem sub {g : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f) (hg : IsBoxSmooth sX sZ g) :
    IsBoxSmooth sX sZ (fun X z => f X z - g X z) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem sum {κ : Type*} (s : Finset κ) {g : κ → Vec 2 → Vec 2 → E}
    (hg : ∀ i ∈ s, IsBoxSmooth sX sZ (g i)) :
    IsBoxSmooth sX sZ (fun X z => ∑ i ∈ s, g i X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsBoxSmooth.zero (sX := sX) (sZ := sZ) (E := E))
  | insert a s ha ih =>
    have := (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem fderiv_fast (hf : IsBoxSmooth sX (sZ + 1) f) :
    IsBoxSmooth sX sZ (fun X z => fderiv ℝ (f X) z) := by
  rw [isBoxSmooth_iff] at hf ⊢
  refine ⟨fun X => (hf.1 X).fderiv_right (m := (sZ : ℕ∞)) (by exact_mod_cast le_rfl), fun b hb => ?_⟩
  have : (fun X z => iteratedFDeriv ℝ b (fun z' => fderiv ℝ (f X) z') z) =
      fun X z => (((continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) E : _ ≃ₗᵢ[ℝ] _) : _ →L[ℝ] _))
        (iteratedFDeriv ℝ (b + 1) (f X) z) := by
    funext X z
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  rw [this]
  exact isSlowSmooth_clm_comp _ (hf.2 (b + 1) (by omega))

theorem fastPartial (hf : IsBoxSmooth sX (sZ + 1) f) (i : Fin 2) :
    IsBoxSmooth sX sZ (AVRegularity.fastPartial i f) :=
  hf.fderiv_fast.map_clm (ContinuousLinearMap.apply ℝ E (basisVec i))

end IsBoxSmooth

namespace IsBoxSmooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}

theorem contDiff_fderiv_fast_slow (hf : IsBoxSmooth sX sZ f) (hZ : 1 ≤ sZ) (z : Vec 2) :
    ContDiff ℝ (sX : ℕ∞) (fun X => fderiv ℝ (f X) z) := by
  have h := hf.2.1 1 hZ z
  have : (fun X => fderiv ℝ (f X) z) =
      ⇑(continuousMultilinearCurryFin1 ℝ (Vec 2) E) ∘ (fun X => iteratedFDeriv ℝ 1 (f X) z) := by
    funext X; exact fderiv_eq_curry_iteratedFDeriv_one (f X) z
  rw [this]
  exact (continuousMultilinearCurryFin1 ℝ (Vec 2) E).contDiff.comp h

theorem continuous_fderiv_slow_fast (hf : IsBoxSmooth sX sZ f) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) :
    Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => fderiv ℝ (f X) p.2) p.1 := by
  have h := hf.2.2 1 1 hX hZ
  have : (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => fderiv ℝ (f X) p.2) p.1) = fun p =>
      ((continuousMultilinearCurryFin1 ℝ (Vec 2) E : _ ≃ₗᵢ[ℝ] _) : _ →L[ℝ] _).comp
        (continuousMultilinearCurryFin1 ℝ (Vec 2) _
          (iteratedFDeriv ℝ 1 (fun X' => iteratedFDeriv ℝ 1 (f X') p.2) p.1)) := by
    funext p
    have e : (fun X => fderiv ℝ (f X) p.2) =
        ⇑(continuousMultilinearCurryFin1 ℝ (Vec 2) E) ∘ (fun X => iteratedFDeriv ℝ 1 (f X) p.2) := by
      funext X; exact fderiv_eq_curry_iteratedFDeriv_one (f X) p.2
    rw [e, LinearIsometryEquiv.comp_fderiv, fderiv_eq_curry_iteratedFDeriv_one]
  rw [this]
  exact continuous_const.clm_comp
    ((continuousMultilinearCurryFin1 ℝ (Vec 2) _).continuous.comp h)

end IsBoxSmooth

universe u

theorem slowDir_aux (b : ℕ) : ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec 2 → Vec 2 → E), IsBoxSmooth 1 b f → ∀ v X : Vec 2,
      ContDiff ℝ (b : ℕ∞) (fun z => fderiv ℝ (fun X' => f X' z) X v) ∧
      ∀ z, iteratedFDeriv ℝ b (fun z' => fderiv ℝ (fun X' => f X' z') X v) z =
        fderiv ℝ (fun X' => iteratedFDeriv ℝ b (f X') z) X v := by
  induction b with
  | zero =>
    intro E _ _ f hf v X
    refine ⟨?_, fun z => ?_⟩
    · have hc := hf.continuous_fderiv_slow (le_refl 1)
      have : Continuous fun z => fderiv ℝ (fun X' => f X' z) X v :=
        (hc.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
      simpa [contDiff_zero] using this
    · have e : (fun X' => iteratedFDeriv ℝ 0 (f X') z) =
          ⇑(continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘ (fun X' => f X' z) := by
        funext X'; simp [iteratedFDeriv_zero_eq_comp]
      rw [e, LinearIsometryEquiv.comp_fderiv]
      simp [iteratedFDeriv_zero_eq_comp]
  | succ b ih =>
    intro E _ _ f hf v X
    have h11 : IsBoxSmooth 1 1 f := hf.mono le_rfl (by omega)
    have hg : IsBoxSmooth 1 b (fun X z => fderiv ℝ (f X) z) := hf.fderiv_fast
    have hderiv : ∀ z, HasFDerivAt (fun z' => fderiv ℝ (fun X' => f X' z') X v)
        (fderiv ℝ (fun X' => fderiv ℝ (f X') z) X v) z := fun z =>
      hasFDerivAt_slowDir f (fun z => (h11.contDiff_slow z).differentiable (by norm_num))
        (fun X => (h11.1 X).differentiable (by norm_num))
        (fun z => (h11.contDiff_fderiv_fast_slow le_rfl z).differentiable (by norm_num))
        (h11.continuous_fderiv_slow_fast le_rfl le_rfl) X z v
    obtain ⟨ihc, ihj⟩ := ih (Vec 2 →L[ℝ] E) (fun X z => fderiv ℝ (f X) z) hg v X
    have hfd : fderiv ℝ (fun z' => fderiv ℝ (fun X' => f X' z') X v) =
        fun z => fderiv ℝ (fun X' => fderiv ℝ (f X') z) X v := by
      funext z; exact (hderiv z).fderiv
    have hdiff : Differentiable ℝ (fun z' => fderiv ℝ (fun X' => f X' z') X v) :=
      fun z => (hderiv z).differentiableAt
    refine ⟨?_, fun z => ?_⟩
    · rw [show (((b + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((b : ℕ∞) : WithTop ℕ∞) + 1 by norm_cast,
        contDiff_succ_iff_fderiv]
      refine ⟨hdiff, by simp, ?_⟩
      rw [hfd]; exact ihc
    · have hJ : (fun X' => iteratedFDeriv ℝ (b + 1) (f X') z) =
          ⇑(continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) E).symm ∘
            (fun X' => iteratedFDeriv ℝ b (fun z' => fderiv ℝ (f X') z') z) := by
        funext X'; rw [iteratedFDeriv_succ_eq_comp_right]; rfl
      have hc := LinearIsometryEquiv.comp_fderiv
        (continuousMultilinearCurryRightEquiv' ℝ b (Vec 2) E).symm (x := X)
        (f := fun X' => iteratedFDeriv ℝ b (fun z' => fderiv ℝ (f X') z') z)
      rw [hJ, hc, iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp_apply, hfd, ContinuousLinearMap.coe_comp, LinearIsometryEquiv.coe_coe'']
      rw [ihj z]

theorem isSlowSmooth_slowDir {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    {φ : Vec 2 → Vec 2 → F} (hφ : IsSlowSmooth (m + 1) φ) (v : Vec 2) :
    IsSlowSmooth m (fun X y => fderiv ℝ (fun X' => φ X' y) X v) := by
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · exact ((hφ.1 y).fderiv_right (m := (m : ℕ∞)) (by norm_cast)).clm_apply
      contDiff_const
  · have : (fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a (fun X => fderiv ℝ (fun X' => φ X' p.2) X v) p.1) =
        fun p => jetApply a v (iteratedFDeriv ℝ (a + 1) (fun X => φ X p.2) p.1) := by
      funext p
      exact iteratedFDeriv_fderiv_apply ((hφ.1 p.2).contDiffAt.of_le (by norm_cast; omega)) v
    show Continuous fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a (fun X => fderiv ℝ (fun X' => φ X' p.2) X v) p.1
    rw [this]
    exact (jetApply a v).continuous.comp (hφ.2 (a + 1) (Nat.succ_le_succ ha))

namespace IsBoxSmooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}

theorem slowPartial (hf : IsBoxSmooth (sX + 1) sZ f) (j : Fin 2) :
    IsBoxSmooth sX sZ (AVRegularity.slowPartial j f) := by
  have key : ∀ b, b ≤ sZ → ∀ X z, iteratedFDeriv ℝ b (AVRegularity.slowPartial j f X) z =
      AVRegularity.slowPartial j (fun X z => iteratedFDeriv ℝ b (f X) z) X z := fun b hb X z =>
    (slowDir_aux b E f (hf.mono (Nat.le_add_left 1 sX) hb) (basisVec j) X).2 z
  rw [isBoxSmooth_iff]
  refine ⟨fun X => (slowDir_aux sZ E f (hf.mono (Nat.le_add_left 1 sX) le_rfl) (basisVec j) X).1,
    fun b hb => ?_⟩
  have e : (fun X z => iteratedFDeriv ℝ b (AVRegularity.slowPartial j f X) z) =
      fun X z => fderiv ℝ (fun X' => iteratedFDeriv ℝ b (f X') z) X (basisVec j) := by
    funext X z; exact key b hb X z
  rw [e]
  exact isSlowSmooth_slowDir ((isBoxSmooth_iff.mp hf).2 b hb) (basisVec j)

theorem fastPartial_slowPartial (hf : IsBoxSmooth (sX + 1) (sZ + 1) f) (i j : Fin 2) (X z : Vec 2) :
    AVRegularity.fastPartial i (AVRegularity.slowPartial j f) X z =
      AVRegularity.slowPartial j (AVRegularity.fastPartial i f) X z := by
  have h11 : IsBoxSmooth 1 1 f := hf.mono (Nat.le_add_left 1 sX) (Nat.le_add_left 1 sZ)
  have hd := hasFDerivAt_slowDir f (fun z => (h11.contDiff_slow z).differentiable (by norm_num))
        (fun X => (h11.1 X).differentiable (by norm_num))
        (fun z => (h11.contDiff_fderiv_fast_slow le_rfl z).differentiable (by norm_num))
        (h11.continuous_fderiv_slow_fast le_rfl le_rfl) X z (basisVec j)
  have hG : DifferentiableAt ℝ (fun X' => fderiv ℝ (f X') z) X :=
    ((h11.contDiff_fderiv_fast_slow le_rfl z).differentiable (by norm_num)) X
  have h2 := (ContinuousLinearMap.apply ℝ E (basisVec i)).hasFDerivAt.comp X hG.hasFDerivAt
  unfold AVRegularity.fastPartial AVRegularity.slowPartial
  rw [hd.fderiv]
  have h3 := h2.fderiv
  have h4 : (fun X' => fderiv ℝ (fun z' => f X' z') z (basisVec i)) =
      (ContinuousLinearMap.apply ℝ E (basisVec i)) ∘ (fun X' => fderiv ℝ (f X') z) := rfl
  rw [h4, h3]
  simp

end IsBoxSmooth

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! Time integration of pointwise-in-time residual bounds: Cauchy–Schwarz for lower integrals
(the scalar part `L¹_t L²_x`), the residual norm from pointwise bounds, and the dissipative part
of the strong energy (its `L²_t` norm is at most `C_k ρ B^{-1/2} 𝓔`; only the scalar cleanup uses
Cauchy–Schwarz on all of `I`).

The energy step sums the components inside the time integral; that needs the time
measurability of the component jets, which is a hypothesis here. -/

/-- Cauchy–Schwarz for the lower integral of a square root. -/
theorem lintegral_rpow_half_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ^ (1 / 2 : ℝ) ∂μ ≤ μ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) := by
  obtain ⟨g, hg, hgf, hgeq⟩ := exists_measurable_le_lintegral_eq μ (fun x => f x ^ (1 / 2 : ℝ))
  rw [hgeq]
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun _ => (1 : ℝ≥0∞)) (g := g)
    aemeasurable_const hg.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  refine h.trans ?_
  gcongr with x
  calc g x ^ (2 : ℝ) ≤ (f x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by gcongr; exact hgf x
    _ = f x := by rw [← ENNReal.rpow_mul]; norm_num

/-- The residual norm from pointwise-in-time bounds of the two densities by `K² G`. -/
theorem residualNorm_le_of_pointwise {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (ν : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (R : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (q : ℝ → Vec 2 → ∀ i, h i) (G : ℝ → ℝ≥0∞)
    {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hI : MeasurableSet I)
    (hR : ∀ t ∈ I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖R t x k v‖ₑ ^ 2 ≤ ENNReal.ofReal (K₁ ^ 2) * G t)
    (hq : ∀ t ∈ I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ‖q t x v‖ₑ ^ 2 ≤ ENNReal.ofReal (K₂ ^ 2) * G t) :
    residualNorm ν π I R q ≤
      ENNReal.ofReal (Real.sqrt ν)⁻¹ * ENNReal.ofReal K₁ * (∫⁻ t in I, G t) ^ (1 / 2 : ℝ)
        + ENNReal.ofReal K₂ * volume I ^ (1 / 2 : ℝ) * (∫⁻ t in I, G t) ^ (1 / 2 : ℝ) := by
  have hsq : ∀ K : ℝ, 0 ≤ K → ENNReal.ofReal (K ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal K := by
    intro K hK
    rw [ENNReal.ofReal_pow hK, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  unfold residualNorm
  gcongr ?_ + ?_
  · rw [mul_assoc]
    gcongr
    calc (∫⁻ t in I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖R t x k v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ t in I, ENNReal.ofReal (K₁ ^ 2) * G t) ^ (1 / 2 : ℝ) := by
          exact ENNReal.rpow_le_rpow (setLIntegral_mono' hI hR) (by norm_num)
      _ = ENNReal.ofReal K₁ * (∫⁻ t in I, G t) ^ (1 / 2 : ℝ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq K₁ hK₁]
  · calc ∫⁻ t in I, (∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ‖q t x v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ ∫⁻ t in I, ENNReal.ofReal K₂ * G t ^ (1 / 2 : ℝ) := by
          refine setLIntegral_mono' hI fun t ht => ?_
          calc _ ≤ (ENNReal.ofReal (K₂ ^ 2) * G t) ^ (1 / 2 : ℝ) := by
                gcongr; exact hq t ht
            _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq K₂ hK₂]
      _ = ENNReal.ofReal K₂ * ∫⁻ t in I, G t ^ (1 / 2 : ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K₂ * (volume I ^ (1 / 2 : ℝ) * (∫⁻ t in I, G t) ^ (1 / 2 : ℝ)) := by
          gcongr
          simpa [Measure.restrict_apply_univ] using
            lintegral_rpow_half_le (volume.restrict I) G
      _ = _ := by rw [mul_assoc]

/-- Time measurability of the gradient factorial density from joint measurability of the
component word jets. -/
theorem measurable_classicalGradFactorialSq {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (ρ : ℝ) (m : ℕ)
    (a : ℝ → Vec 2 → ∀ i, h i) (v : ι)
    (hmeas : ∀ j, j ≤ m + 1 → ∀ w : DerivativeWord2 j,
      Measurable (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) :
    Measurable (fun t => classicalGradFactorialSq ρ m (fun x => a t x v)) := by
  unfold classicalGradFactorialSq
  refine Finset.measurable_sum _ fun j hj => ?_
  refine Measurable.const_mul (Finset.measurable_sum _ fun w _ => ?_) _
  have hj' : j + 1 ≤ m + 1 := by have := Finset.mem_range.1 hj; omega
  exact ((hmeas (j + 1) hj' w).pow_const 2).lintegral_prod_right'

/-- The dissipative part of the strong energy controls the time integral of the mass-weighted
gradient density. -/
theorem lintegral_gradDensity_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (ρ B : ℝ) (hB : 0 < B)
    (π : ι → ℝ) (I : Set ℝ) (m : ℕ) (a : ℝ → Vec 2 → ∀ i, h i)
    (hmeas : ∀ v, Measurable (fun t => classicalGradFactorialSq ρ m (fun x => a t x v))) :
    ∫⁻ t in I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * classicalGradFactorialSq ρ m (fun x => a t x v)
      ≤ ENNReal.ofReal B⁻¹ * classicalStrongEnergy ρ B π I m a ^ 2 := by
  rw [lintegral_finsetSum _ fun v _ => (hmeas v).const_mul _]
  simp_rw [lintegral_const_mul _ (hmeas _)]
  unfold classicalStrongEnergy
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [mul_left_comm]
  gcongr
  calc ∫⁻ t in I, classicalGradFactorialSq ρ m (fun x => a t x v)
      = ENNReal.ofReal B⁻¹ * (ENNReal.ofReal B *
          ∫⁻ t in I, classicalGradFactorialSq ρ m (fun x => a t x v)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hB.le), inv_mul_cancel₀ hB.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr; exact le_add_self

end AVRegularity
end
end
