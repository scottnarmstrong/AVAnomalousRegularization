-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Pipe.PushTest
public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Velocity.IncrementProvider
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix
namespace AVRegularity.Applications

/-! # Supports of pushed tests and the smooth flux field `G∇ζ`

* `pipePushTest ζ` is smooth with compact support inside the outer pipe when `ζ` is a test
  function compactly supported in `(t₁ - 8T, t₁) × B_R`;
* `pipeFlux i ζ` is the `i`-th component of the smooth field `adj(DF)adj(DF)ᵀ ∇ζ`, a test
  function in the same cylinder which agrees with `G∇ζ` on the window. -/

section
/-- The `i`-th component of the smooth surrogate `adj(DF) adj(DF)ᵀ ∇ζ` of `G∇ζ`. -/
def pipeFlux (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (ζ : ℝ × Vec 2 → ℝ) (i : Fin 2)
    (p : ℝ × Vec 2) : ℝ :=
  ((pipeAdj X t₁ p * (pipeAdj X t₁ p)ᵀ).mulVec (stSpaceGrad ζ p)) i

section

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

/-- The support of a pushed test lies in the image of the support under `pipeMap`. -/
theorem pipePushTest_support_image {ξ : ℝ × Vec 2 → ℝ} (hc : HasCompactSupport ξ)
    (hsub : tsupport ξ ⊆ {p | p.1 ∈ Set.Icc (t₁ - 8 * T) t₁}) :
    HasCompactSupport (pipePushTest X t₁ ξ) ∧
      tsupport (pipePushTest X t₁ ξ) ⊆ pipeMap X t₁ T '' tsupport ξ := by
  have hK : IsCompact (pipeMap X t₁ T '' tsupport ξ) :=
    hc.image (continuous_pipeMap ch)
  have hsupp : Function.support (pipePushTest X t₁ ξ) ⊆ pipeMap X t₁ T '' tsupport ξ := by
    rintro ⟨t, x⟩ hx
    have hz : ξ (t, X t₁ x t) ≠ 0 := hx
    have hmem : (t, X t₁ x t) ∈ tsupport ξ := subset_tsupport _ hz
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := hsub hmem
    refine ⟨(t, X t₁ x t), hmem, ?_⟩
    rw [pipeMap_apply_of_mem htI, ch.right t htI]
  have hcl : tsupport (pipePushTest X t₁ ξ) ⊆ pipeMap X t₁ T '' tsupport ξ :=
    closure_minimal hsupp hK.isClosed
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hcl, hcl⟩

theorem pipePushTest_support {ζ : ℝ × Vec 2 → ℝ}
    (hζ : IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) ζ) :
    HasCompactSupport (pipePushTest X t₁ ζ) ∧
      tsupport (pipePushTest X t₁ ζ) ⊆
        outerPipe (fun t y => X t y t₁) t₁ T R := by
  obtain ⟨hs, hc, hsub⟩ := hζ
  have hK : IsCompact (pipeMap X t₁ T '' tsupport ζ) :=
    hc.image (continuous_pipeMap ch)
  have hsupp : Function.support (pipePushTest X t₁ ζ) ⊆ pipeMap X t₁ T '' tsupport ζ := by
    rintro ⟨t, x⟩ hx
    have hz : ζ (t, X t₁ x t) ≠ 0 := hx
    have hmem : (t, X t₁ x t) ∈ tsupport ζ := subset_tsupport _ hz
    have ht := hsub hmem
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨ht.1.1.le, ht.1.2.le⟩
    refine ⟨(t, X t₁ x t), hmem, ?_⟩
    rw [pipeMap_apply_of_mem htI, ch.right t htI]
  have hcl : tsupport (pipePushTest X t₁ ζ) ⊆ pipeMap X t₁ T '' tsupport ζ :=
    closure_minimal hsupp hK.isClosed
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport _) hcl, ?_⟩
  intro p hp
  obtain ⟨⟨t, y⟩, hty, rfl⟩ := hcl hp
  have h := hsub hty
  have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨h.1.1.le, h.1.2.le⟩
  rw [pipeMap_apply_of_mem htI]
  exact ⟨h.1.1, h.1.2, y, h.2, rfl⟩

theorem pipeFlux_eq_metric {ζ : ℝ × Vec 2 → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)
    (i : Fin 2) (y : Vec 2) :
    pipeFlux X t₁ ζ i (t, y) = ((pipeMetric X t₁ (t, y)).mulVec (stSpaceGrad ζ (t, y))) i := by
  unfold pipeFlux
  rw [pipeMetric_eq_adj ch ht]

theorem contDiff_pipeFlux {ζ : ℝ × Vec 2 → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) ζ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (pipeFlux X t₁ ζ i) := by
  have hentry : ∀ j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 =>
      (pipeAdj X t₁ p * (pipeAdj X t₁ p)ᵀ) i j := by
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiff.sum fun k _ => (contDiff_pipeAdj_entry ch i k).mul (contDiff_pipeAdj_entry ch j k)
  have : pipeFlux X t₁ ζ i = fun p => ∑ j : Fin 2,
      (pipeAdj X t₁ p * (pipeAdj X t₁ p)ᵀ) i j * fderiv ℝ ζ p (0, basisVec j) := by
    funext p; simp [pipeFlux, Matrix.mulVec, dotProduct, stSpaceGrad]
  rw [this]
  exact ContDiff.sum fun j _ => (hentry j).mul (contDiff_fderiv_apply_of_smooth hs _)

omit ch in
theorem tsupport_pipeFlux_subset (ζ : ℝ × Vec 2 → ℝ) (i : Fin 2) :
    tsupport (pipeFlux X t₁ ζ i) ⊆ tsupport ζ := by
  have hsupp : Function.support (pipeFlux X t₁ ζ i) ⊆ tsupport ζ := by
    intro p hp
    by_contra hn
    apply hp
    have h0 : stSpaceGrad ζ p = 0 := by
      ext j; simp [stSpaceGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
    simp [pipeFlux, h0]
  exact closure_minimal hsupp (isClosed_tsupport _)

theorem pipeFlux_isSTTest {ζ : ℝ × Vec 2 → ℝ} {O : Set (ℝ × Vec 2)} (hζ : IsSTTest O ζ)
    (i : Fin 2) : IsSTTest O (pipeFlux X t₁ ζ i) := by
  obtain ⟨hs, hc, hsub⟩ := hζ
  have hsm := contDiff_pipeFlux ch hs i
  have hcl := tsupport_pipeFlux_subset (X := X) (t₁ := t₁) ζ i
  exact ⟨hsm, hc.of_isClosed_subset (isClosed_tsupport _) hcl, hcl.trans hsub⟩

theorem divSp_flux_eq {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    divSp (fun z => (pipeMetric X t₁ (t, z)).mulVec (stSpaceGrad ζ (t, z))) y =
      ∑ i : Fin 2, fderiv ℝ (pipeFlux X t₁ ζ i) (t, y) (0, basisVec i) := by
  unfold divSp
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun z => (pipeMetric X t₁ (t, z)).mulVec (stSpaceGrad ζ (t, z)) i) =
      fun z => pipeFlux X t₁ ζ i (t, z) := by
    funext z; exact (pipeFlux_eq_metric ch ht i z).symm
  rw [hfun, fderiv_slice (contDiff_pipeFlux ch hζ i)]

end
end

/-! # The label cylinder `(t₁ - 8T, t₁) × B_R` and the outer pipe

`pipeMap` maps the label cylinder onto the outer pipe, so square integrability of `θ` on the pipe
transfers to `U(t,y) = θ(t, F_t y)` on the cylinder. -/

section
theorem pipe_volume_euclidBall_lt_top (R : ℝ) : volume (euclidBall 0 R) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall (0 : Vec 2) |R|) ?_)
    (isCompact_closedBall _ _).measure_lt_top
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := norm_le_sqrt_vecNormSq y
  have h2 : vecNormSq y < R ^ 2 := by simpa [euclidBall] using hy
  have h3 : Real.sqrt (vecNormSq y) ≤ |R| :=
    Real.sqrt_le_iff.2 ⟨abs_nonneg _, by rw [sq_abs]; exact h2.le⟩
  exact h1.trans h3

theorem pipe_isOpen_euclidBall (c : Vec 2) (R : ℝ) : IsOpen (euclidBall c R) := by
  have hc : Continuous fun y : Vec 2 => vecNormSq (y - c) := by
    simp only [vecNormSq, vecDot]; fun_prop
  exact isOpen_lt hc continuous_const

theorem volume_cylinder_lt_top (t₁ T R : ℝ) :
    volume (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    (pipe_volume_euclidBall_lt_top R)

section

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

theorem pipeMap_preimage_outerPipe :
    pipeMap X t₁ T ⁻¹' outerPipe (fun t y => X t y t₁) t₁ T R =
      Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R := by
  ext ⟨t, y⟩
  simp only [Set.mem_preimage, outerPipe, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, y', hy', hxy⟩
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨h1.le, h2.le⟩
    have hmap : (pipeMap X t₁ T (t, y)).2 = X t y t₁ := by
      rw [pipeMap_apply_of_mem htI]
    have hfy : X t y t₁ = X t y' t₁ := by rw [← hmap]; exact hxy
    have : y = y' := by
      have := congrArg (fun z => X t₁ z t) hfy
      simpa [ch.left t htI] using this
    exact ⟨⟨h1, h2⟩, this ▸ hy'⟩
  · rintro ⟨⟨h1, h2⟩, hy⟩
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨h1.le, h2.le⟩
    refine ⟨h1, h2, y, hy, ?_⟩
    rw [pipeMap_apply_of_mem htI]

theorem pipeMap_measurableEmbedding (hT : 0 < T) :
    MeasurableEmbedding (pipeMap X t₁ T) :=
  (pipeHomeo ch hT).measurableEmbedding

/-- Square integrability of `θ` on the pipe transfers to `U = θ ∘ F` on the label cylinder. -/
theorem pipe_U_memLp (hT : 0 < T) {θ : ℝ → Vec 2 → ℝ}
    (h : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R))) :
    MemLp (fun p : ℝ × Vec 2 => θ p.1 (X p.1 p.2 t₁)) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)) := by
  have hmp := (pipeMap_mp ch hT).restrict_preimage_emb (pipeMap_measurableEmbedding ch hT)
    (outerPipe (fun t y => X t y t₁) t₁ T R)
  rw [pipeMap_preimage_outerPipe ch] at hmp
  have h2 := h.comp_measurePreserving hmp
  refine h2.ae_eq ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' ?_]
  · refine Filter.Eventually.of_forall fun ⟨t, y⟩ hp => ?_
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨hp.1.1.le, hp.1.2.le⟩
    simp [Function.comp, pipeMap_apply_of_mem htI]
  · exact measurableSet_Ioo.prod (pipe_isOpen_euclidBall 0 R).measurableSet

end
end

/-! # The pulled-back equation in material coordinates (generic form)

`pipe_pullback_weak_core`: if `θ ∈ L²(pipe)` satisfies the distributional equation of a
local energy solution (`IsLocalEnergySolution`) for all pipe tests, and `U = θ ∘ F` has slice
weak gradient `DU` on `B_R` (with `DU ∈ L²` of the label cylinder), then
`∬ (-U ∂ₜζ + (κ G DU - U V)·∇ζ) = 0` for all tests `ζ` in the label cylinder. -/

section
theorem st_derivs_zero {φ : ℝ × Vec 2 → ℝ} {p : ℝ × Vec 2} (hp : p ∉ tsupport φ) :
    stTimeDeriv φ p = 0 ∧ stSpaceGrad φ p = 0 ∧ stSpaceLap φ p = 0 := by
  refine ⟨by simp [stTimeDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp],
    by ext i; simp [stSpaceGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp], ?_⟩
  unfold stSpaceLap
  refine Finset.sum_eq_zero fun i _ => ?_
  have : p ∉ tsupport (fun q => fderiv ℝ φ q (0, basisVec i)) :=
    fun h => hp (tsupport_fderiv_apply_subset _ _ h)
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]

theorem vecDot_smul_left (c : ℝ) (x y : Vec 2) : vecDot (c • x) y = c * vecDot x y := by
  simp [vecDot, Fin.sum_univ_two]; ring

theorem vecDot_comm' (x y : Vec 2) : vecDot x y = vecDot y x := by
  simp [vecDot, mul_comm]

theorem integrable_mul_cts {μ : Measure (ℝ × Vec 2)} {U f : ℝ × Vec 2 → ℝ}
    (hU : Integrable U μ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun p => U p * f p) μ := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  exact hU.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

section Core

variable {b0 b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R κ : ℝ}

/-- Pointwise identity behind the change of variables: for `p = (t,y)`, `t` in the window. -/
theorem integrand_pullback (ch : IsPipeChart b0 X t₁ T) {θ : ℝ → Vec 2 → ℝ}
    {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₁ - 8 * T) t₁) (y : Vec 2) :
    θ t (X t y t₁) *
        (stTimeDeriv (pipePushTest X t₁ ζ) (t, X t y t₁) +
          vecDot (b t (X t y t₁)) (stSpaceGrad (pipePushTest X t₁ ζ) (t, X t y t₁)) +
          κ * stSpaceLap (pipePushTest X t₁ ζ) (t, X t y t₁)) =
      θ t (X t y t₁) *
        (stTimeDeriv ζ (t, y) + vecDot (pipeDrift b b0 X t₁ (t, y)) (stSpaceGrad ζ (t, y)) +
          κ * ∑ i : Fin 2, fderiv ℝ (pipeFlux X t₁ ζ i) (t, y) (0, basisVec i)) := by
  have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨ht.1.le, ht.2.le⟩
  rw [stTimeDeriv_push ch hζ ht y, drift_dot_push ch hζ htI b y, pipe_vecDot_sub_left,
    ← divSp_flux_eq ch hζ htI y, ← stSpaceLap_push ch hζ htI y]
  congr 1
  ring

theorem pipe_pullback_weak_core (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {B : ℝ}
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2)
    (hb0m : Measurable fun p : ℝ × Vec 2 => b0 p.1 p.2)
    (hbB : ∀ t x, ‖b t x‖ ≤ B) (hb0B : ∀ t x, ‖b0 t x‖ ≤ B)
    {θ : ℝ → Vec 2 → ℝ}
    (hθ2 : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R)))
    (heq : ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ outerPipe (fun t y => X t y t₁) t₁ T R →
      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 *
        (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
          + κ * ∑ i : Fin 2,
            fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0)
    {DU : ℝ → Vec 2 → Vec 2}
    (hDU2 : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (X t y t₁)) (DU t))
    {ζ : ℝ × Vec 2 → ℝ} (hζ : IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) ζ) :
    ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R,
      (-(θ p.1 (X p.1 p.2 t₁) * stTimeDeriv ζ p) +
        vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) -
          θ p.1 (X p.1 p.2 t₁) • pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) = 0 := by
  set S : Set (ℝ × Vec 2) := Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R with hS
  have hSm : MeasurableSet S :=
    measurableSet_Ioo.prod (pipe_isOpen_euclidBall 0 R).measurableSet
  set U : ℝ × Vec 2 → ℝ := fun p => θ p.1 (X p.1 p.2 t₁) with hUdef
  set φ := pipePushTest X t₁ ζ with hφdef
  have hζs := hζ.1
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_pipePushTest ch hζs
  obtain ⟨hφc, hφsub⟩ := pipePushTest_support ch hζ
  -- integrability of `U` on the cylinder
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cylinder_lt_top t₁ T R⟩
  have hUint : Integrable U (volume.restrict S) :=
    (pipe_U_memLp ch hT hθ2).integrable (by norm_num)
  have hDUint : ∀ i, Integrable (fun p : ℝ × Vec 2 => DU p.1 p.2 i) (volume.restrict S) :=
    fun i => (hDU2 i).integrable (by norm_num)
  -- Step 1: the equation tested against `φ`, as an integral over all of `ℝ × Vec 2`
  set Gf : ℝ × Vec 2 → ℝ := fun p => θ p.1 p.2 *
    (stTimeDeriv φ p + vecDot (b p.1 p.2) (stSpaceGrad φ p) + κ * stSpaceLap φ p) with hGf
  have hE : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, Gf p = 0 :=
    heq φ hφs hφc hφsub
  have hzero : ∀ p, p ∉ tsupport φ → Gf p = 0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := st_derivs_zero hp
    simp [hGf, h1, h2, h3, vecDot]
  have hA : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, Gf p = ∫ p, Gf p :=
    setIntegral_eq_integral_of_tsupport (g := φ) hφsub hzero
  have hB : ∫ p, Gf (pipeMap X t₁ T p) = ∫ p, Gf p :=
    (pipeMap_mp ch hT).integral_comp (pipeMap_measurableEmbedding ch hT) Gf
  -- Step 2: the integrand in label coordinates
  set h : ℝ × Vec 2 → ℝ := fun p => U p * (stTimeDeriv ζ p +
    vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p) +
    κ * ∑ i : Fin 2, fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i)) with hh
  have hC : ∀ p, Gf (pipeMap X t₁ T p) = h p := by
    rintro ⟨t, y⟩
    by_cases ht : t ∈ Set.Ioo (t₁ - 8 * T) t₁
    · rw [pipeMap_apply_of_mem ⟨ht.1.le, ht.2.le⟩]
      exact integrand_pullback ch hζs ht y
    · have hnot : (t, y) ∉ tsupport ζ := fun hm => ht (hζ.2.2 hm).1
      have hnot' : pipeMap X t₁ T (t, y) ∉ tsupport φ :=
        fun hm => ht ⟨(hφsub hm).1, (hφsub hm).2.1⟩
      rw [hzero _ hnot']
      obtain ⟨h1, h2, _⟩ := st_derivs_zero hnot
      have hfl : ∀ i, fderiv ℝ (pipeFlux X t₁ ζ i) (t, y) (0, basisVec i) = 0 := fun i => by
        have : (t, y) ∉ tsupport (pipeFlux X t₁ ζ i) :=
          fun hm => hnot (tsupport_pipeFlux_subset ζ i hm)
        simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
      simp [hh, h1, h2, hfl, vecDot]
  have hhz : ∀ p, p ∉ tsupport ζ → h p = 0 := by
    intro p hnot
    obtain ⟨h1, h2, _⟩ := st_derivs_zero hnot
    have hfl : ∀ i, fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) = 0 := fun i => by
      have : p ∉ tsupport (pipeFlux X t₁ ζ i) := fun hm => hnot (tsupport_pipeFlux_subset ζ i hm)
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
    simp [hh, h1, h2, hfl, vecDot]
  have hS0 : ∫ p in S, h p = 0 := by
    have hD : ∫ p in S, h p = ∫ p, h p :=
      setIntegral_eq_integral_of_tsupport (g := ζ) hζ.2.2 hhz
    rw [hD, ← integral_congr_ae (Filter.Eventually.of_forall hC), hB, ← hA, hE]
  -- Step 3: integrability of the pieces
  have hVm := measurable_pipeDrift ch hbm hb0m
  have hSw : ∀ p ∈ S, p.1 ∈ Set.Icc (t₁ - 8 * T) t₁ := fun p hp => ⟨hp.1.1.le, hp.1.2.le⟩
  have hdtc : Continuous (stTimeDeriv ζ) :=
    (contDiff_fderiv_apply_of_smooth hζs ((1 : ℝ), (0 : Vec 2))).continuous
  have hdtk : HasCompactSupport (stTimeDeriv ζ) := hasCompactSupport_fderiv_apply hζ.2.1 _
  have hfc : ∀ i : Fin 2, Continuous fun p => fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) :=
    fun i => (contDiff_fderiv_apply_of_smooth (pipeFlux_isSTTest ch hζ i).1 _).continuous
  have hfk : ∀ i : Fin 2, HasCompactSupport fun p =>
      fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) :=
    fun i => hasCompactSupport_fderiv_apply (pipeFlux_isSTTest ch hζ i).2.1 _
  have hgc : ∀ j : Fin 2, Continuous fun p => stSpaceGrad ζ p j :=
    fun j => (contDiff_fderiv_apply_of_smooth hζs (0, basisVec j)).continuous
  have hgk : ∀ j : Fin 2, HasCompactSupport fun p => stSpaceGrad ζ p j :=
    fun j => hasCompactSupport_fderiv_apply hζ.2.1 _
  have hia : Integrable (fun p => U p * stTimeDeriv ζ p) (volume.restrict S) :=
    integrable_mul_cts hUint hdtc hdtk
  have hic : ∀ i : Fin 2, Integrable (fun p => U p *
      fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i)) (volume.restrict S) :=
    fun i => integrable_mul_cts hUint (hfc i) (hfk i)
  have hie : ∀ i : Fin 2, Integrable (fun p => DU p.1 p.2 i * pipeFlux X t₁ ζ i p)
      (volume.restrict S) := fun i =>
    integrable_mul_cts (hDUint i) (pipeFlux_isSTTest ch hζ i).1.continuous
      (pipeFlux_isSTTest ch hζ i).2.1
  -- the drift pairing is bounded on `S`
  obtain ⟨Cg, hCg⟩ : ∃ C : ℝ, ∀ p (j : Fin 2), |stSpaceGrad ζ p j| ≤ C := by
    obtain ⟨C0, h0⟩ := (hgc 0).bounded_above_of_compact_support (hgk 0)
    obtain ⟨C1, h1⟩ := (hgc 1).bounded_above_of_compact_support (hgk 1)
    refine ⟨max C0 C1, fun p j => ?_⟩
    fin_cases j
    · exact (h0 p).trans (le_max_left _ _)
    · exact (h1 p).trans (le_max_right _ _)
  have hVb : ∀ p ∈ S, ∀ j : Fin 2, |pipeDrift b b0 X t₁ p j| ≤ 5 * |B| := by
    rintro ⟨t, y⟩ hp j
    have hw : ‖b t (X t y t₁) - b0 t (X t y t₁)‖ ≤ 2 * B := by
      have := norm_sub_le (b t (X t y t₁)) (b0 t (X t y t₁))
      linarith [hbB t (X t y t₁), hb0B t (X t y t₁)]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0 0)
    have h1 : vecNormSq ((pipeJac X t₁ (t, y))⁻¹.mulVec (b t (X t y t₁) - b0 t (X t y t₁))) ≤
        9 / 4 * vecNormSq (b t (X t y t₁) - b0 t (X t y t₁)) :=
      pipeJac_inv_close ch (hSw _ hp) y (b t (X t y t₁) - b0 t (X t y t₁))
    have h2 := vecNormSq_le_two_mul_norm_sq (b t (X t y t₁) - b0 t (X t y t₁))
    have h3 : ‖b t (X t y t₁) - b0 t (X t y t₁)‖ ^ 2 ≤ (2 * B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h4 : vecNormSq (pipeDrift b b0 X t₁ (t, y)) ≤ (5 * |B|) ^ 2 := by
      have : (5 * |B|) ^ 2 = 25 * B ^ 2 := by rw [mul_pow, sq_abs]; ring
      have h5 : (pipeDrift b b0 X t₁ (t, y)) = (pipeJac X t₁ (t, y))⁻¹.mulVec
        (b t (X t y t₁) - b0 t (X t y t₁)) := rfl
      rw [this, h5]
      nlinarith
    have h6 := norm_le_sqrt_vecNormSq (pipeDrift b b0 X t₁ (t, y))
    have h7 : Real.sqrt (vecNormSq (pipeDrift b b0 X t₁ (t, y))) ≤ 5 * |B| :=
      Real.sqrt_le_iff.2 ⟨by positivity, h4⟩
    have h8 := norm_le_pi_norm (pipeDrift b b0 X t₁ (t, y)) j
    rw [Real.norm_eq_abs] at h8
    exact h8.trans (h6.trans h7)
  have hid : Integrable (fun p => U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p))
      (volume.restrict S) := by
    refine hUint.mul_bdd (c := 2 * (5 * |B|) * Cg) ?_ ?_
    · have : (fun p => vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) = fun p =>
          ∑ j : Fin 2, pipeDrift b b0 X t₁ p j * stSpaceGrad ζ p j := rfl
      rw [this]
      exact (Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hVm).mul (hgc j).measurable).aestronglyMeasurable
    · refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun p hp => ?_)
      rw [Real.norm_eq_abs]
      simp only [vecDot, Fin.sum_univ_two]
      calc _ ≤ |pipeDrift b b0 X t₁ p 0 * stSpaceGrad ζ p 0| +
            |pipeDrift b b0 X t₁ p 1 * stSpaceGrad ζ p 1| := abs_add_le _ _
        _ ≤ 5 * |B| * Cg + 5 * |B| * Cg := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hVb p hp 0
          · exact hCg p 0
          · exact hVb p hp 1
          · exact hCg p 1
        _ = _ := by ring
  -- Step 4: weak gradient on the cylinder
  have hgrad' : ∀ i : Fin 2, ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakPartialDerivOn (euclidBall 0 R) i (fun y => U (τ, y))
        (fun y => (fun p : ℝ × Vec 2 => DU p.1 p.2 i) (τ, y)) := fun i => by
    filter_upwards [hgrad] with τ hτ
    exact hτ i
  have hw : ∀ i : Fin 2, ∫ p in S, U p * fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) =
      -∫ p in S, DU p.1 p.2 i * pipeFlux X t₁ ζ i p := fun i =>
    integral_mul_partial_slice (H := U) (g := fun p : ℝ × Vec 2 => DU p.1 p.2 i) i hUint
      (hDUint i) (hgrad' i) (pipeFlux_isSTTest ch hζ i)
  -- Step 5: assemble
  have hsplit : ∫ p in S, h p = (∫ p in S, U p * stTimeDeriv ζ p) +
      (∫ p in S, U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) +
        κ * ∑ i : Fin 2, ∫ p in S, U p * fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) := by
    have hfun : ∀ p, h p = U p * stTimeDeriv ζ p +
        U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p) +
        κ * ∑ i : Fin 2, U p * fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) := by
      intro p; simp only [hh, ← Finset.mul_sum]; ring
    simp_rw [hfun]
    have hsum : Integrable (fun p => U p * stTimeDeriv ζ p +
        U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) (volume.restrict S) := hia.add hid
    have hcs : Integrable (fun p => κ * ∑ i : Fin 2,
        U p * fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i)) (volume.restrict S) :=
      (integrable_finsetSum _ fun i _ => hic i).const_mul κ
    rw [integral_add hsum hcs, integral_add hia hid, integral_const_mul,
      integral_finsetSum _ fun i _ => hic i]
  have hgoal : ∫ p in S, (-(U p * stTimeDeriv ζ p) +
        vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) - U p • pipeDrift b b0 X t₁ p)
          (stSpaceGrad ζ p)) =
      -(∫ p in S, U p * stTimeDeriv ζ p) -
        (∫ p in S, U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) +
        κ * ∑ i : Fin 2, ∫ p in S, DU p.1 p.2 i * pipeFlux X t₁ ζ i p := by
    have hfun : ∀ p ∈ S, (-(U p * stTimeDeriv ζ p) +
        vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) - U p • pipeDrift b b0 X t₁ p)
          (stSpaceGrad ζ p)) =
        (-(U p * stTimeDeriv ζ p) -
          U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) +
        κ * ∑ i : Fin 2, DU p.1 p.2 i * pipeFlux X t₁ ζ i p := by
      rintro ⟨t, y⟩ hp
      have ht := hSw _ hp
      have hfl : ∑ i : Fin 2, DU t y i * pipeFlux X t₁ ζ i (t, y) =
          vecDot (DU t y) ((pipeMetric X t₁ (t, y)).mulVec (stSpaceGrad ζ (t, y))) := by
        simp only [vecDot]
        exact Finset.sum_congr rfl fun i _ => by rw [pipeFlux_eq_metric ch ht]
      rw [hfl, pipe_vecDot_sub_left, vecDot_smul_left, vecDot_mulVec_left, pipeMetric_symm,
        vecDot_comm' (DU t y)]
      have : vecDot (U (t, y) • pipeDrift b b0 X t₁ (t, y)) (stSpaceGrad ζ (t, y)) =
          U (t, y) * vecDot (pipeDrift b b0 X t₁ (t, y)) (stSpaceGrad ζ (t, y)) :=
        vecDot_smul_left _ _ _
      rw [this]
      ring
    have hna : Integrable (fun p => -(U p * stTimeDeriv ζ p)) (volume.restrict S) := hia.neg
    have h1 : Integrable (fun p => -(U p * stTimeDeriv ζ p) -
        U p * vecDot (pipeDrift b b0 X t₁ p) (stSpaceGrad ζ p)) (volume.restrict S) :=
      hna.sub hid
    have h2 : Integrable (fun p => κ * ∑ i : Fin 2, DU p.1 p.2 i * pipeFlux X t₁ ζ i p)
        (volume.restrict S) := (integrable_finsetSum _ fun i _ => hie i).const_mul κ
    rw [setIntegral_congr_fun hSm hfun, integral_add h1 h2, integral_sub hna hid,
      integral_neg, integral_const_mul, integral_finsetSum _ fun i _ => hie i]
  have hcsum : ∑ i : Fin 2, ∫ p in S, U p * fderiv ℝ (pipeFlux X t₁ ζ i) p (0, basisVec i) =
      -∑ i : Fin 2, ∫ p in S, DU p.1 p.2 i * pipeFlux X t₁ ζ i p := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hw i
  rw [hgoal]
  rw [hsplit, hcsum] at hS0
  linarith

end Core
end

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix Filter Topology
namespace AVRegularity.Applications

/-! # The material equation for local weak solutions (non-conservative form)

`pipe_pullback_weak_global_core`: if `u` is a local weak solution of `∂ₜu + b·∇u - κΔu = 0` on a
set `O` containing `{(t, F_t y) : t₁ - 8T ≤ a' < t < t₁}`, then `U = u ∘ (t, F_t y)` with
`DU = (D_yF_t)ᵀ (Du ∘ F)` satisfies
`∬ (-U ∂ₜξ + (V·DU) ξ + κ (G DU)·∇ξ) = 0` for tests `ξ ∈ C_c^∞((a',t₁) × ℝ²)`. -/

section
theorem hasCompactSupport_of_support_subset {f : ℝ × Vec 2 → ℝ} {K : Set (ℝ × Vec 2)}
    (hK : IsCompact K) (hf : Function.support f ⊆ K) :
    HasCompactSupport f ∧ tsupport f ⊆ K := by
  have h : tsupport f ⊆ K := closure_minimal hf hK.isClosed
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) h, h⟩

section

variable {b0 b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T κ : ℝ}

/-- Pointwise identity for the change of variables in the local weak formulation. -/
theorem integrand_pullback_global (ch : IsPipeChart b0 X t₁ T) {u : ℝ × Vec 2 → ℝ}
    {Du : ℝ × Vec 2 → Vec 2} {ξ : ℝ × Vec 2 → ℝ} (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₁ - 8 * T) t₁) (y : Vec 2) :
    (-(u (t, X t y t₁) * stTimeDeriv (pipePushTest X t₁ ξ) (t, X t y t₁)) +
        vecDot (b t (X t y t₁)) (Du (t, X t y t₁)) * pipePushTest X t₁ ξ (t, X t y t₁) +
        κ * vecDot (Du (t, X t y t₁)) (stSpaceGrad (pipePushTest X t₁ ξ) (t, X t y t₁))) -
      (u (t, X t y t₁) * vecDot (b0 t (X t y t₁)) (stSpaceGrad (pipePushTest X t₁ ξ) (t, X t y t₁))
        + vecDot (b0 t (X t y t₁)) (Du (t, X t y t₁)) *
          pipePushTest X t₁ ξ (t, X t y t₁)) =
    -(u (t, X t y t₁) * stTimeDeriv ξ (t, y)) +
      vecDot (pipeDrift b b0 X t₁ (t, y))
        ((pipeJac X t₁ (t, y))ᵀ.mulVec (Du (t, X t y t₁))) * ξ (t, y) +
      κ * vecDot ((pipeMetric X t₁ (t, y)).mulVec
        ((pipeJac X t₁ (t, y))ᵀ.mulVec (Du (t, X t y t₁)))) (stSpaceGrad ξ (t, y)) := by
  have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨ht.1.le, ht.2.le⟩
  set D := Du (t, X t y t₁) with hD
  set g := stSpaceGrad (pipePushTest X t₁ ξ) (t, X t y t₁) with hg
  have h1 : vecDot (pipeDrift b b0 X t₁ (t, y)) ((pipeJac X t₁ (t, y))ᵀ.mulVec D) =
      vecDot (b t (X t y t₁) - b0 t (X t y t₁)) D := by
    unfold pipeDrift
    rw [vecDot_mulVec_left, inv_transpose_mulVec ch htI]
  have h2 : (pipeMetric X t₁ (t, y)).mulVec ((pipeJac X t₁ (t, y))ᵀ.mulVec D) =
      (pipeJac X t₁ (t, y))⁻¹.mulVec D := by
    unfold pipeMetric
    rw [← Matrix.mulVec_mulVec, inv_transpose_mulVec ch htI]
  have h3 : vecDot ((pipeJac X t₁ (t, y))⁻¹.mulVec D) (stSpaceGrad ξ (t, y)) = vecDot D g := by
    rw [vecDot_mulVec_left, stSpaceGrad_push ch hξ htI y, inv_transpose_mulVec ch htI]
  rw [h1, h2, h3, pipe_vecDot_sub_left, stTimeDeriv_push ch hξ ht y, pipePushTest_apply ch htI]
  ring

theorem pipe_pullback_weak_global_core (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {a' : ℝ}
    (ha : t₁ - 8 * T ≤ a') {B : ℝ}
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) (hbB : ∀ t x, ‖b t x‖ ≤ B)
    (hb0s : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => b0 p.1 p.2)
    (hb0d : ∀ t x, divSp (b0 t) x = 0)
    {O : Set (ℝ × Vec 2)} (hO : ∀ t ∈ Set.Ioo a' t₁, ∀ y, (t, X t y t₁) ∈ O)
    {u : ℝ × Vec 2 → ℝ} {Du : ℝ × Vec 2 → Vec 2} (hu : IsLocalWeakSolution b κ O u Du)
    {ξ : ℝ × Vec 2 → ℝ} (hξ : IsSTTest (Set.Ioo a' t₁ ×ˢ Set.univ) ξ) :
    ∫ p in Set.Ioo a' t₁ ×ˢ (Set.univ : Set (Vec 2)),
      (-(u (p.1, X p.1 p.2 t₁) * stTimeDeriv ξ p) +
        vecDot (pipeDrift b b0 X t₁ p)
          ((pipeJac X t₁ p)ᵀ.mulVec (Du (p.1, X p.1 p.2 t₁))) * ξ p +
        κ * vecDot ((pipeMetric X t₁ p).mulVec
          ((pipeJac X t₁ p)ᵀ.mulVec (Du (p.1, X p.1 p.2 t₁)))) (stSpaceGrad ξ p)) = 0 := by
  set S : Set (ℝ × Vec 2) := Set.Ioo a' t₁ ×ˢ Set.univ with hS
  have hSw : ∀ p ∈ S, p.1 ∈ Set.Ioo (t₁ - 8 * T) t₁ := fun p hp =>
    ⟨lt_of_le_of_lt ha hp.1.1, hp.1.2⟩
  have hSO : S ⊆ O := by
    rintro ⟨t, x⟩ hp
    have hI := hSw _ hp
    have := hO t hp.1 (X t₁ x t)
    rwa [ch.right t ⟨hI.1.le, hI.2.le⟩] at this
  have hSm : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have hξs := hξ.1
  set φ := pipePushTest X t₁ ξ with hφdef
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_pipePushTest ch hξs
  obtain ⟨hφc, hφimg⟩ := pipePushTest_support_image ch hξ.2.1 (fun p hp =>
    ⟨(hSw p (hξ.2.2 hp)).1.le, (hSw p (hξ.2.2 hp)).2.le⟩)
  have hφS : tsupport φ ⊆ S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := hφimg hp
    exact ⟨(hξ.2.2 hq).1, Set.mem_univ _⟩
  have hu_loc : ∀ K : Set (ℝ × Vec 2), K ⊆ S → IsCompact K → IntegrableOn u K := by
    intro K hKS hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact (hu.1 K (hKS.trans hSO) hK).integrable (by norm_num)
  have hDu_loc : ∀ i : Fin 2, ∀ K : Set (ℝ × Vec 2), K ⊆ S → IsCompact K →
      IntegrableOn (fun p => Du p i) K := by
    intro i K hKS hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact (hu.2.1 K (hKS.trans hSO) hK i).integrable (by norm_num)
  -- derivative functions of `φ`
  have hdtc : Continuous (stTimeDeriv φ) :=
    (contDiff_fderiv_apply_of_smooth hφs ((1 : ℝ), (0 : Vec 2))).continuous
  have hdtk : HasCompactSupport (stTimeDeriv φ) := hasCompactSupport_fderiv_apply hφc _
  have hdts : tsupport (stTimeDeriv φ) ⊆ S :=
    (tsupport_fderiv_apply_subset _ _).trans hφS
  have hgc : ∀ j : Fin 2, Continuous fun p => stSpaceGrad φ p j :=
    fun j => (contDiff_fderiv_apply_of_smooth hφs (0, basisVec j)).continuous
  have hgk : ∀ j : Fin 2, HasCompactSupport fun p => stSpaceGrad φ p j :=
    fun j => hasCompactSupport_fderiv_apply hφc _
  have hgs : ∀ j : Fin 2, tsupport (fun p => stSpaceGrad φ p j) ⊆ S :=
    fun j => (tsupport_fderiv_apply_subset _ _).trans hφS
  -- the weights `b0_i * ∂_iφ` and `b0_i * φ` are continuous with support in `tsupport φ`
  have hb0c : ∀ i : Fin 2, Continuous fun p : ℝ × Vec 2 => b0 p.1 p.2 i :=
    fun i => (contDiff_pi.1 hb0s i).continuous
  have hsupp1 : ∀ i : Fin 2, Function.support (fun p : ℝ × Vec 2 =>
      b0 p.1 p.2 i * stSpaceGrad φ p i) ⊆ tsupport φ := by
    intro i p hp
    by_contra hn
    apply hp
    have : stSpaceGrad φ p = 0 := (st_derivs_zero hn).2.1
    simp [this]
  have hsupp2 : ∀ i : Fin 2, Function.support (fun p : ℝ × Vec 2 => b0 p.1 p.2 i * φ p) ⊆
      tsupport φ := by
    intro i p hp
    by_contra hn
    apply hp
    simp [image_eq_zero_of_notMem_tsupport hn]
  have hsupp3 : ∀ i : Fin 2, Function.support (fun p : ℝ × Vec 2 => φ p) ⊆ tsupport φ :=
    fun i => subset_tsupport φ
  -- integrability on the cylinder
  have hI1 : IntegrableOn (fun p => u p * stTimeDeriv φ p) S :=
    integrableOn_mul_of_support hu_loc hdtc hdtk hdts
  have hIb : ∀ i : Fin 2, IntegrableOn (fun p : ℝ × Vec 2 => b p.1 p.2 i * (Du p i * φ p)) S := by
    intro i
    have h0 : IntegrableOn (fun p => Du p i * φ p) S :=
      integrableOn_mul_of_support (hDu_loc i) hφs.continuous hφc hφS
    refine h0.bdd_mul (c := B) ((measurable_pi_apply i).comp hbm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    exact (norm_le_pi_norm (b p.1 p.2) i).trans (hbB _ _)
  have hIc : ∀ i : Fin 2, IntegrableOn (fun p : ℝ × Vec 2 => Du p i * stSpaceGrad φ p i) S :=
    fun i => integrableOn_mul_of_support (hDu_loc i) (hgc i) (hgk i) (hgs i)
  have hIr1 : ∀ i : Fin 2, IntegrableOn (fun p : ℝ × Vec 2 =>
      u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) S := fun i => by
    have hh := hasCompactSupport_of_support_subset hφc (hsupp1 i)
    exact integrableOn_mul_of_support hu_loc ((hb0c i).mul (hgc i)) hh.1 (hh.2.trans hφS)
  have hIr2 : ∀ i : Fin 2, IntegrableOn (fun p : ℝ × Vec 2 =>
      Du p i * (b0 p.1 p.2 i * φ p)) S := fun i => by
    have hh := hasCompactSupport_of_support_subset hφc (hsupp2 i)
    exact integrableOn_mul_of_support (hDu_loc i) ((hb0c i).mul hφs.continuous) hh.1
      (hh.2.trans hφS)
  -- the two integrands in physical coordinates
  set gx : ℝ × Vec 2 → ℝ := fun p => -(u p * stTimeDeriv φ p) +
    vecDot (b p.1 p.2) (Du p) * φ p + κ * vecDot (Du p) (stSpaceGrad φ p) with hgx
  set rx : ℝ × Vec 2 → ℝ := fun p => u p * vecDot (b0 p.1 p.2) (stSpaceGrad φ p) +
    vecDot (b0 p.1 p.2) (Du p) * φ p with hrx
  have hgx0 : ∀ p, p ∉ tsupport φ → gx p = 0 := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := st_derivs_zero hp
    simp [hgx, h1, h2, image_eq_zero_of_notMem_tsupport hp, vecDot]
  have hrx0 : ∀ p, p ∉ tsupport φ → rx p = 0 := by
    intro p hp
    obtain ⟨_, h2, _⟩ := st_derivs_zero hp
    simp [hrx, h2, image_eq_zero_of_notMem_tsupport hp, vecDot]
  have hgxS : ∫ p in S, gx p = 0 := by
    have h := hu.2.2.2 φ ⟨hφs, hφc, hφS.trans hSO⟩
    have h1 : ∫ p in O, gx p = 0 := h
    have e1 : ∫ p in O, gx p = ∫ p, gx p :=
      setIntegral_eq_integral_of_tsupport (g := φ) (hφS.trans hSO) hgx0
    have e2 : ∫ p in S, gx p = ∫ p, gx p :=
      setIntegral_eq_integral_of_tsupport (g := φ) hφS hgx0
    rw [e2, ← e1]
    exact h1
  -- integration by parts against the divergence free field `b0`
  have hψ : ∀ i : Fin 2, IsSTTest S (fun p : ℝ × Vec 2 => b0 p.1 p.2 i * φ p) := fun i =>
    ⟨(contDiff_pi.1 hb0s i).mul hφs,
      (hasCompactSupport_of_support_subset hφc (hsupp2 i)).1,
      (hasCompactSupport_of_support_subset hφc (hsupp2 i)).2.trans hφS⟩
  have hgrad : ∀ i : Fin 2, ∀ᵐ τ ∂(volume.restrict (Set.Ioo a' t₁)),
      HasWeakPartialDerivOn Set.univ i (fun y => u (τ, y)) (fun y => Du (τ, y) i) := by
    intro i
    refine (ae_restrict_iff' measurableSet_Ioo).2 (hu.2.2.1.mono fun τ hτ hτI => ?_)
    have : timeSection O τ = Set.univ :=
      Set.eq_univ_of_forall fun x => hSO ⟨hτI, Set.mem_univ x⟩
    rw [this] at hτ
    exact hτ i
  have hibp : ∀ i : Fin 2, ∫ p in S, u p * fderiv ℝ (fun q : ℝ × Vec 2 => b0 q.1 q.2 i * φ q) p
        (0, basisVec i) = -∫ p in S, Du p i * (b0 p.1 p.2 i * φ p) := fun i =>
    integral_mul_partial_slice_loc (H := u) (g := fun p => Du p i) i hu_loc (hDu_loc i)
      (hgrad i) (hψ i)
  have hIψ : ∀ i : Fin 2, IntegrableOn (fun p => u p *
      fderiv ℝ (fun q : ℝ × Vec 2 => b0 q.1 q.2 i * φ q) p (0, basisVec i)) S := fun i =>
    integrableOn_mul_of_support hu_loc
      (contDiff_fderiv_apply_of_smooth (hψ i).1 _).continuous
      (hasCompactSupport_fderiv_apply (hψ i).2.1 _)
      ((tsupport_fderiv_apply_subset _ _).trans (hψ i).2.2)
  have hpt : ∀ p, ∑ i : Fin 2, u p *
      fderiv ℝ (fun q : ℝ × Vec 2 => b0 q.1 q.2 i * φ q) p (0, basisVec i) =
      ∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i) := by
    rintro ⟨t, x⟩
    have hdiv := hb0d t x
    unfold divSp at hdiv
    have hexp : ∀ i : Fin 2, fderiv ℝ (fun q : ℝ × Vec 2 => b0 q.1 q.2 i * φ q) (t, x)
        (0, basisVec i) = b0 t x i * stSpaceGrad φ (t, x) i +
          φ (t, x) * fderiv ℝ (fun z => b0 t z i) x (basisVec i) := by
      intro i
      have hb0i : ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × Vec 2 => b0 q.1 q.2 i := contDiff_pi.1 hb0s i
      rw [fderiv_fun_mul (hb0i.differentiable (by simp) _) (hφs.differentiable (by simp) _)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      rw [fderiv_slice hb0i t x (basisVec i)]
      simp only [stSpaceGrad]
    simp only [hexp, mul_add, Finset.sum_add_distrib]
    have h0 : ∑ i : Fin 2, u (t, x) *
        (φ (t, x) * fderiv ℝ (fun z => b0 t z i) x (basisVec i)) = 0 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hdiv, mul_zero, mul_zero]
    rw [h0, add_zero]
  have hrxS : ∫ p in S, rx p = 0 := by
    have hrxform : ∀ p, rx p = (∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) +
        ∑ i : Fin 2, Du p i * (b0 p.1 p.2 i * φ p) := by
      intro p; simp [hrx, vecDot, Fin.sum_univ_two]; ring
    have hA : ∫ p in S, (∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) =
        -∑ i : Fin 2, ∫ p in S, Du p i * (b0 p.1 p.2 i * φ p) := by
      have hfun : (fun p => ∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) = fun p =>
          ∑ i : Fin 2, u p *
            fderiv ℝ (fun q : ℝ × Vec 2 => b0 q.1 q.2 i * φ q) p (0, basisVec i) :=
        funext fun p => (hpt p).symm
      rw [hfun, integral_finsetSum _ (fun i _ => hIψ i), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => hibp i
    have hsA : IntegrableOn (fun p => ∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) S :=
      integrable_finsetSum _ fun i _ => hIr1 i
    have hsC : IntegrableOn (fun p => ∑ i : Fin 2, Du p i * (b0 p.1 p.2 i * φ p)) S :=
      integrable_finsetSum _ fun i _ => hIr2 i
    simp_rw [hrxform]
    rw [integral_add hsA hsC, hA, integral_finsetSum _ (fun i _ => hIr2 i)]
    ring
  have hgxI : IntegrableOn gx S := by
    have hform : gx = fun p => (-(u p * stTimeDeriv φ p) +
        ∑ i : Fin 2, b p.1 p.2 i * (Du p i * φ p)) +
          κ * ∑ i : Fin 2, Du p i * stSpaceGrad φ p i := by
      funext p; simp [hgx, vecDot, Fin.sum_univ_two]; ring
    rw [hform]
    exact (hI1.neg.add (integrable_finsetSum _ fun i _ => hIb i)).add
      ((integrable_finsetSum _ fun i _ => hIc i).const_mul κ)
  have hrxI : IntegrableOn rx S := by
    have hform : rx = fun p => (∑ i : Fin 2, u p * (b0 p.1 p.2 i * stSpaceGrad φ p i)) +
        ∑ i : Fin 2, Du p i * (b0 p.1 p.2 i * φ p) := by
      funext p; simp [hrx, vecDot, Fin.sum_univ_two]; ring
    rw [hform]
    exact (integrable_finsetSum _ fun i _ => hIr1 i).add
      (integrable_finsetSum _ fun i _ => hIr2 i)
  have hgt : ∫ p, (gx p - rx p) = 0 := by
    rw [← setIntegral_eq_integral_of_tsupport (g := φ) (O := S) hφS
      (f := fun p => gx p - rx p) (fun p hp => by rw [hgx0 p hp, hrx0 p hp]; ring),
      integral_sub hgxI hrxI, hgxS, hrxS]
    simp
  -- change of variables to label coordinates
  set hl : ℝ × Vec 2 → ℝ := fun p =>
    -(u (p.1, X p.1 p.2 t₁) * stTimeDeriv ξ p) +
      vecDot (pipeDrift b b0 X t₁ p) ((pipeJac X t₁ p)ᵀ.mulVec (Du (p.1, X p.1 p.2 t₁))) * ξ p +
      κ * vecDot ((pipeMetric X t₁ p).mulVec
        ((pipeJac X t₁ p)ᵀ.mulVec (Du (p.1, X p.1 p.2 t₁)))) (stSpaceGrad ξ p) with hhl
  have hlab : ∀ p, gx (pipeMap X t₁ T p) - rx (pipeMap X t₁ T p) = hl p := by
    rintro ⟨t, y⟩
    by_cases ht : t ∈ Set.Ioo (t₁ - 8 * T) t₁
    · rw [pipeMap_apply_of_mem ⟨ht.1.le, ht.2.le⟩]
      exact integrand_pullback_global ch hξs ht y
    · have hnot : (t, y) ∉ tsupport ξ := fun hm => ht (hSw _ (hξ.2.2 hm))
      have hnot' : pipeMap X t₁ T (t, y) ∉ tsupport φ :=
        fun hm => ht (hSw _ (hφS hm))
      rw [hgx0 _ hnot', hrx0 _ hnot']
      obtain ⟨h1, h2, _⟩ := st_derivs_zero hnot
      simp [hhl, h1, h2, vecDot, image_eq_zero_of_notMem_tsupport hnot]
  have hlz : ∀ p, p ∉ tsupport ξ → hl p = 0 := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := st_derivs_zero hp
    simp [hhl, h1, h2, vecDot, image_eq_zero_of_notMem_tsupport hp]
  have hmp : ∫ p, (gx (pipeMap X t₁ T p) - rx (pipeMap X t₁ T p)) = ∫ p, (gx p - rx p) :=
    (pipeMap_mp ch hT).integral_comp (pipeMap_measurableEmbedding ch hT)
      (fun p => gx p - rx p)
  rw [setIntegral_eq_integral_of_tsupport (g := ξ) hξ.2.2 hlz,
    ← integral_congr_ae (Filter.Eventually.of_forall hlab), hmp, hgt]

end

section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

end Construction
end

/-! # The material equation for local energy solutions

`pipe_pullback_weak`: a local energy solution `θ` (`IsLocalEnergySolution`) in the
outer pipe pulls back to `U(t,y) = θ(t, F_t y)` solving
`∂ₜU = div(κ G∇U - VU)` weakly on `(t₁ - 8T, t₁) × B_R`. -/

section
section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- **Pull-back of a local energy solution to material coordinates.**
With `U(t,y) = θ(t, X(t,y,t₁))` and `DU` the slice gradient supplied by
`IsLocalEnergySolution`, `∂ₜU = div(κ G ∇U - V U)` weakly on the label cylinder. -/
theorem pipe_pullback_weak (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x)))
    (n : ℕ) (_hn : 2 ≤ n) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (hX : AVenhance.IsFlow (streamVel (Φ (n - 2))) X) (t₁ T : ℝ) (hT : 0 < T)
    (hh : 8 * T * ocA α q Λ (n - 2) ≤ ocCStar) {κ R : ℝ} (_hκ : 0 < κ) (_hR : 0 < R)
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ) :
    ∃ DU : ℝ → Vec 2 → Vec 2,
      (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
        (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
        HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (X t y t₁)) (DU t)) ∧
      ∀ ξ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) ξ →
        ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R,
          (-(θ p.1 (X p.1 p.2 t₁) * stTimeDeriv ξ p) +
            vecDot (κ • (pipeMetric X t₁ p).mulVec (DU p.1 p.2) -
              θ p.1 (X p.1 p.2 t₁) • pipeDrift b (streamVel (Φ (n - 2))) X t₁ p)
              (stSpaceGrad ξ p)) = 0 := by
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT hh
  obtain ⟨hbm, ⟨B, hBb⟩, _⟩ := limit_velocity_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  obtain ⟨_, C, _, _, _, _, _, _, _, _, _, _, hbdd⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  have hcont : ∀ M, Continuous fun p : ℝ × Vec 2 => streamVel (Φ M) p.1 p.2 := fun M =>
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)).smooth.continuous
  obtain ⟨hL2, heq, DU, _, hDU2, hgrad⟩ := hθ
  exact ⟨DU, hDU2, hgrad, fun ξ hξ =>
    pipe_pullback_weak_core (B := max B C) ch hT hbm (hcont (n - 2)).measurable
      (fun t x => (hBb t x).trans (le_max_left _ _))
      (fun t x => (hbdd (n - 2) t x).trans (le_max_right _ _)) hL2 heq hDU2 hgrad hξ⟩

end Construction
end

end AVRegularity.Applications
end
