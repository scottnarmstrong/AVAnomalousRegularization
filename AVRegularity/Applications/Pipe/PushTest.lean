-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Parabolic.SliceGrad
import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcCStar
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Slice integration by parts with locally integrable data

Variant of `integral_mul_partial_slice` on a cylinder `(a,b) × ℝ²` in which `H` and its slice
derivative `g` are only integrable on compact subsets of the cylinder. -/

/-- A function which is locally integrable on `S`, multiplied by a continuous function whose
support lies in a compact subset of `S`, is integrable on `S`. -/
theorem integrableOn_mul_of_support {S : Set (ℝ × Vec 2)} {H f : ℝ × Vec 2 → ℝ}
    (hH : ∀ K : Set (ℝ × Vec 2), K ⊆ S → IsCompact K → IntegrableOn H K)
    (hf : Continuous f) (hc : HasCompactSupport f) (hsub : tsupport f ⊆ S) :
    IntegrableOn (fun p => H p * f p) S := by
  have hK : IsCompact (tsupport f) := hc
  have h1 : IntegrableOn (fun p => H p * f p) (tsupport f) := by
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
    exact (hH _ hsub hK).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have h2 : IntegrableOn (fun p => H p * f p) (tsupport f) (volume.restrict S) := by
    unfold IntegrableOn at h1 ⊢
    rwa [Measure.restrict_restrict_of_subset hsub]
  refine h2.integrable_of_forall_notMem_eq_zero fun p hp => ?_
  rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]

/-- Slice integration by parts on `(a,b) × ℝ²` for locally integrable `H`, `g`. -/
theorem integral_mul_partial_slice_loc {a b : ℝ} {H g : ℝ × Vec 2 → ℝ} (i : Fin 2)
    (hH : ∀ K : Set (ℝ × Vec 2), K ⊆ Set.Ioo a b ×ˢ Set.univ → IsCompact K → IntegrableOn H K)
    (hg : ∀ K : Set (ℝ × Vec 2), K ⊆ Set.Ioo a b ×ˢ Set.univ → IsCompact K → IntegrableOn g K)
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      HasWeakPartialDerivOn Set.univ i (fun y => H (τ, y)) (fun y => g (τ, y)))
    {ψ : ℝ × Vec 2 → ℝ} (hψ : IsSTTest (Set.Ioo a b ×ˢ Set.univ) ψ) :
    ∫ p in Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)), H p * fderiv ℝ ψ p (0, basisVec i) =
      -∫ p in Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)), g p * ψ p := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hdc : Continuous fun p => fderiv ℝ ψ p (0, basisVec i) :=
    (contDiff_fderiv_apply_of_smooth hψ.1 _).continuous
  have hint1 : Integrable (fun p => H p * fderiv ℝ ψ p (0, basisVec i))
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) :=
    integrableOn_mul_of_support hH hdc (hasCompactSupport_fderiv_apply hψ.2.1 _)
      ((tsupport_fderiv_apply_subset _ _).trans hψ.2.2)
  have hint2 : Integrable (fun p => g p * ψ p) (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) :=
    integrableOn_mul_of_support hg hψc hψ.2.1 hψ.2.2
  rw [volume_restrict_prod_eq] at hint1 hint2 ⊢
  rw [integral_prod _ hint1, integral_prod _ hint2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hgrad] with τ hτ
  have ht := isSpTest_slice hψ τ
  have h := hτ (fun y => ψ (τ, y)) ht.1 ht.2.1 ht.2.2
  simp only [fderiv_slice hψ.1] at h
  exact h

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization Matrix
namespace AVRegularity.Applications

/-! # Jacobian matrices on `Vec 2`

`jacMat F y` is the matrix of `D F(y)` in the standard basis, `divSp w` the spatial divergence of
a vector field, and the basic chain rules in matrix form. -/

/-- The Jacobian matrix `(∂ⱼFᵢ)ᵢⱼ`. -/
def jacMat (F : Vec 2 → Vec 2) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ F y (basisVec j) i

/-- The divergence `Σᵢ ∂ᵢ wᵢ` of a vector field on `Vec 2`. -/
def divSp (w : Vec 2 → Vec 2) (y : Vec 2) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (fun z => w z i) y (basisVec i)

theorem vec_eq_sum_basisVec (v : Vec 2) : v = ∑ j : Fin 2, v j • basisVec j := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_two, basisVec]

theorem fderiv_apply_eq_jacMat_mulVec (F : Vec 2 → Vec 2) (y v : Vec 2) :
    fderiv ℝ F y v = (jacMat F y).mulVec v := by
  conv_lhs => rw [vec_eq_sum_basisVec v]
  ext i
  simp [jacMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem fderiv_scalar_eq_dot (φ : Vec 2 → ℝ) (y v : Vec 2) :
    fderiv ℝ φ y v = vecDot (spGrad φ y) v := by
  conv_lhs => rw [vec_eq_sum_basisVec v]
  simp [spGrad, vecDot, Fin.sum_univ_two, mul_comm]

/-- Chain rule for the gradient: `∇(φ ∘ F) = (DF)ᵀ ∇φ(F)`. -/
theorem spGrad_comp {φ : Vec 2 → ℝ} {F : Vec 2 → Vec 2} {y : Vec 2}
    (hφ : DifferentiableAt ℝ φ (F y)) (hF : DifferentiableAt ℝ F y) :
    spGrad (φ ∘ F) y = (jacMat F y)ᵀ.mulVec (spGrad φ (F y)) := by
  ext j
  simp only [spGrad]
  rw [fderiv_comp y hφ hF, ContinuousLinearMap.comp_apply, fderiv_scalar_eq_dot,
    fderiv_apply_eq_jacMat_mulVec]
  simp [vecDot, Matrix.mulVec, dotProduct, jacMat, Fin.sum_univ_two, mul_comm]

/-- Chain rule for Jacobians. -/
theorem jacMat_comp {G F : Vec 2 → Vec 2} {y : Vec 2}
    (hG : DifferentiableAt ℝ G (F y)) (hF : DifferentiableAt ℝ F y) :
    jacMat (G ∘ F) y = jacMat G (F y) * jacMat F y := by
  ext i j
  simp only [jacMat]
  rw [fderiv_comp y hG hF, ContinuousLinearMap.comp_apply, fderiv_apply_eq_jacMat_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, jacMat, Fin.sum_univ_two]

/-- The determinant of `jacMat` is the determinant of the derivative. -/
theorem jacMat_det (F : Vec 2 → Vec 2) (y : Vec 2) :
    (jacMat F y).det = (fderiv ℝ F y).det := by
  have : jacMat F y = LinearMap.toMatrix' (fderiv ℝ F y : Vec 2 →ₗ[ℝ] Vec 2) := by
    ext i j
    simp [jacMat, LinearMap.toMatrix'_apply, basisVec]
  rw [this, LinearMap.det_toMatrix']

/-! # The two-dimensional Piola identity

For a smooth map `F : Vec 2 → Vec 2` with `det DF ≡ 1`, `(DF)⁻¹ = adj(DF)` has divergence-free
columns (symmetry of mixed partials), whence `div_y((DF)⁻¹ (w ∘ F)) = (div w) ∘ F` for every
smooth vector field `w`. -/

theorem inv_jacMat_eq_adjugate {F : Vec 2 → Vec 2} {y : Vec 2} (h : (jacMat F y).det = 1) :
    (jacMat F y)⁻¹ = (jacMat F y).adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

/-- The linear functional `L ↦ (L e_b)_a` on `Vec 2 →L Vec 2`. -/
def jacEntryCLM (a b : Fin 2) : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec b))

theorem contDiff_fderiv_top {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) :=
  hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem contDiff_jacMat_entry {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => jacMat F z a b :=
  (jacEntryCLM a b).contDiff.comp (contDiff_fderiv_top hF)

theorem fderiv_jacMat_entry {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y v : Vec 2)
    (a b : Fin 2) :
    fderiv ℝ (fun z => jacMat F z a b) y v = fderiv ℝ (fderiv ℝ F) y v (basisVec b) a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    ((contDiff_fderiv_top hF).differentiable (by simp)) y
  have := ((jacEntryCLM a b).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  change fderiv ℝ ((jacEntryCLM a b) ∘ fderiv ℝ F) y v = _
  rw [this]
  rfl

theorem fderiv_jacMat_entry_symm {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Vec 2)
    (a b c : Fin 2) :
    fderiv ℝ (fun z => jacMat F z a b) y (basisVec c) =
      fderiv ℝ (fun z => jacMat F z a c) y (basisVec b) := by
  rw [fderiv_jacMat_entry hF, fderiv_jacMat_entry hF]
  have hs : IsSymmSndFDerivAt ℝ F y :=
    (hF.contDiffAt).isSymmSndFDerivAt (by simp)
  rw [hs (basisVec c) (basisVec b)]

theorem adjugate_jacMat_apply (F : Vec 2 → Vec 2) (z : Vec 2) (i k : Fin 2) :
    (jacMat F z).adjugate i k =
      if i = k then jacMat F z (1 - i) (1 - i) else - jacMat F z i k := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases k <;> simp

theorem contDiff_adjugate_entry {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i k : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (jacMat F z).adjugate i k := by
  have : (fun z => (jacMat F z).adjugate i k) = fun z =>
      if i = k then jacMat F z (1 - i) (1 - i) else - jacMat F z i k := by
    funext z; exact adjugate_jacMat_apply F z i k
  rw [this]
  split_ifs
  · exact contDiff_jacMat_entry hF _ _
  · exact (contDiff_jacMat_entry hF _ _).neg

/-- The columns of `adj (DF)` are divergence free. -/
theorem piola_column {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Vec 2) (k : Fin 2) :
    ∑ i : Fin 2, fderiv ℝ (fun z => (jacMat F z).adjugate i k) y (basisVec i) = 0 := by
  have e : ∀ i : Fin 2, fderiv ℝ (fun z => (jacMat F z).adjugate i k) y (basisVec i) =
      if i = k then fderiv ℝ (fun z => jacMat F z (1 - i) (1 - i)) y (basisVec i)
      else - fderiv ℝ (fun z => jacMat F z i k) y (basisVec i) := by
    intro i
    have : (fun z => (jacMat F z).adjugate i k) = fun z =>
        if i = k then jacMat F z (1 - i) (1 - i) else - jacMat F z i k := by
      funext z; exact adjugate_jacMat_apply F z i k
    rw [this]
    split_ifs
    · rfl
    · rw [fderiv_fun_neg]; rfl
  simp only [e, Fin.sum_univ_two]
  have h := fderiv_jacMat_entry_symm hF y
  fin_cases k
  · simp
    have := h 1 1 0
    have h2 := h 1 0 1
    linarith
  · simp
    have := h 0 0 1
    have h2 := h 0 1 0
    linarith

/-- **2D Piola identity.** For a smooth `F` with `det DF ≡ 1` and a smooth vector field `w`,
`div_y((DF)⁻¹ (w ∘ F)) = (div w) ∘ F`. -/
theorem piola_div {F : Vec 2 → Vec 2} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hdet : ∀ z, (jacMat F z).det = 1) {w : Vec 2 → Vec 2} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (y : Vec 2) :
    divSp (fun z => (jacMat F z)⁻¹.mulVec (w (F z))) y = divSp w (F y) := by
  have hfun : (fun z => (jacMat F z)⁻¹.mulVec (w (F z))) =
      fun z => (jacMat F z).adjugate.mulVec (w (F z)) := by
    funext z; rw [inv_jacMat_eq_adjugate (hdet z)]
  rw [hfun]
  have hFd : DifferentiableAt ℝ F y := (hF.differentiable (by simp)) y
  have hwk : ∀ k : Fin 2, DifferentiableAt ℝ (fun z => w z k) (F y) :=
    fun k => ((contDiff_pi.1 hw k).differentiable (by simp)) _
  have hA : ∀ i k : Fin 2, HasFDerivAt (fun z => (jacMat F z).adjugate i k)
      (fderiv ℝ (fun z => (jacMat F z).adjugate i k) y) y :=
    fun i k => (((contDiff_adjugate_entry hF i k).differentiable (by simp)) y).hasFDerivAt
  have hW : ∀ k : Fin 2, HasFDerivAt (fun z => w (F z) k)
      ((fderiv ℝ (fun z => w z k) (F y)).comp (fderiv ℝ F y)) y :=
    fun k => (hwk k).hasFDerivAt.comp y hFd.hasFDerivAt
  have hcomp : ∀ i : Fin 2,
      fderiv ℝ (fun z => ((jacMat F z).adjugate.mulVec (w (F z))) i) y (basisVec i) =
        ∑ k : Fin 2, (fderiv ℝ (fun z => (jacMat F z).adjugate i k) y (basisVec i) * w (F y) k
          + (jacMat F y).adjugate i k *
            fderiv ℝ (fun z => w z k) (F y) (fderiv ℝ F y (basisVec i))) := by
    intro i
    have hfn : (fun z => ((jacMat F z).adjugate.mulVec (w (F z))) i) =
        fun z => ∑ k : Fin 2, (jacMat F z).adjugate i k * w (F z) k := by
      funext z; simp [Matrix.mulVec, dotProduct]
    rw [hfn]
    have hs : HasFDerivAt (fun z => ∑ k : Fin 2, (jacMat F z).adjugate i k * w (F z) k)
        (∑ k : Fin 2, ((jacMat F y).adjugate i k •
            (fderiv ℝ (fun z => w z k) (F y)).comp (fderiv ℝ F y)
          + w (F y) k • fderiv ℝ (fun z => (jacMat F z).adjugate i k) y)) y :=
      HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hA i k).mul (hW k))
    rw [hs.fderiv]
    simp only [Fin.sum_univ_two, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    ring
  unfold divSp
  simp only [hcomp]
  have hP0 := piola_column hF y 0
  have hP1 := piola_column hF y 1
  have hd := hdet y
  rw [Matrix.det_fin_two] at hd
  have hlin : ∀ (k : Fin 2) (u : Vec 2), fderiv ℝ (fun z => w z k) (F y) u =
      fderiv ℝ (fun z => w z k) (F y) (basisVec 0) * u 0 +
        fderiv ℝ (fun z => w z k) (F y) (basisVec 1) * u 1 := by
    intro k u
    rw [fderiv_scalar_eq_dot]
    simp [vecDot, spGrad, Fin.sum_univ_two, mul_comm]
  have hJ : ∀ i : Fin 2, fderiv ℝ F y (basisVec i) = fun l => jacMat F y l i := by
    intro i; rw [fderiv_apply_eq_jacMat_mulVec]; ext l
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, basisVec]
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → Fin 2 → ℝ, ∀ k u, fderiv ℝ (fun z => w z k) (F y) u =
      g k 0 * u 0 + g k 1 * u 1 :=
    ⟨fun k l => fderiv ℝ (fun z => w z k) (F y) (basisVec l), hlin⟩
  simp only [hJ, hg, Fin.sum_univ_two, adjugate_jacMat_apply] at hP0 hP1 ⊢
  norm_num [basisVec] at hP0 hP1 ⊢
  linear_combination w (F y) 0 * hP0 + w (F y) 1 * hP1 + (g 0 0 + g 1 1) * hd

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity
namespace AVRegularity.Applications

/-! # The material chart `F_t = X(t, ·, t₁)`

`IsPipeChart b0 X t₁ T` collects the properties of the short flow map used by the pipe pullback:
joint smoothness of `F` and of its inverse, inverse relations, measure preservation,
`det DF = 1` and Euclidean closeness of `DF`, `DH` to the identity for `t ∈ [t₁ - 8T, t₁]`.
`isPipeChart_of_construction` produces it from the construction. -/

/-- Properties of the material chart `F_t = X(t,·,t₁)` with inverse `H_t = X(t₁,·,t)` on the
window `[t₁ - 8T, t₁]`. -/
structure IsPipeChart (b0 : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T : ℝ) :
    Prop where
  flow : AVenhance.IsFlow b0 X
  smoothF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => X p.1 p.2 t₁)
  smoothH : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => X t₁ p.2 p.1)
  left : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ y, X t₁ (X t y t₁) t = y
  right : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ x, X t (X t₁ x t) t₁ = x
  mp : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, MeasurePreserving (fun y => X t y t₁) volume volume
  det : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ y, (fderiv ℝ (fun z => X t z t₁) y).det = 1
  close : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ y v,
    vecNormSq (fderiv ℝ (fun z => X t z t₁) y v - v) ≤ (1 / 4) * vecNormSq v
  closeInv : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ x v,
    vecNormSq (fderiv ℝ (fun z => X t₁ z t) x v - v) ≤ (1 / 4) * vecNormSq v

section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- The material chart of the construction on `[t₁ - 8T, t₁]`. -/
theorem isPipeChart_of_construction (m : ℕ) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (hX : AVenhance.IsFlow (streamVel (Φ m)) X) (t₁ T : ℝ) (hT : 0 < T)
    (hh : 8 * T * ocA α q Λ m ≤ ocCStar) :
    IsPipeChart (streamVel (Φ m)) X t₁ T := by
  have hφ := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ m
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hdiv : ∀ u y, AVenhance.Infra.Flow.spatialDivergence (streamVel (Φ m)) u y = 0 :=
    fun u y => AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero
      hφ u y
  have hjoint := AVenhance.Infra.Flow.flow_joint_contDiff_infty hb hX
  have hsh : ∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, |t - t₁| ≤ 8 * T := by
    intro t ht
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  refine ⟨hX, hjoint.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)),
    hjoint.comp (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht y
    exact (short_flow_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m X hX t₁ (8 * T)
      (by linarith) hh t (hsh t ht)).1 y
  · intro t ht x
    exact (short_flow_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m X hX t₁ (8 * T)
      (by linarith) hh t (hsh t ht)).2.1 x
  · intro t ht
    exact (short_flow_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m X hX t₁ (8 * T)
      (by linarith) hh t (hsh t ht)).2.2.2.2.2.1
  · intro t _ y
    exact AVenhance.Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free hb hX hdiv
      y t₁ t
  · intro t ht y v
    exact (short_flow_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m X hX t₁ (8 * T)
      (by linarith) hh t (hsh t ht)).2.2.2.2.2.2.1 y v
  · intro t ht x v
    exact (short_flow_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m X hX t₁ (8 * T)
      (by linarith) hh t (hsh t ht)).2.2.2.2.2.2.2.1 x v

end Construction

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix
namespace AVRegularity.Applications

/-! # Chart coefficients and their algebra

`pipeMetric X t₁ (t,y) = (D_yF_t)⁻¹ (D_yF_t)⁻ᵀ` and
`pipeDrift b b0 X t₁ (t,y) = (D_yF_t)⁻¹ ((b - b0)(t, F_t y))`, with `F_t = X(t,·,t₁)`.
Ellipticity constants `1/4 ≤ G ≤ 9/4` follow from `|DF v - v| ≤ |v|/2` and `det DF = 1`. -/

section
/-- The Jacobian matrix `D_yF_t(y)` of the chart `F_t = X(t,·,t₁)` at `p = (t,y)`. -/
def pipeJac (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  jacMat (fun z => X p.1 z t₁) p.2

/-- The chart metric `G = (D_yF_t)⁻¹ (D_yF_t)⁻ᵀ`. -/
def pipeMetric (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (pipeJac X t₁ p)⁻¹ * ((pipeJac X t₁ p)⁻¹)ᵀ

/-- The relative drift `V = (D_yF_t)⁻¹ ((b - b0)(t, F_t y))`. -/
def pipeDrift (b b0 : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ)
    (p : ℝ × Vec 2) : Vec 2 :=
  (pipeJac X t₁ p)⁻¹.mulVec (b p.1 (X p.1 p.2 t₁) - b0 p.1 (X p.1 p.2 t₁))

theorem close_sq {u v : Vec 2} (h : vecNormSq (u - v) ≤ (1 / 4) * vecNormSq v) :
    (1 / 4) * vecNormSq v ≤ vecNormSq u ∧ vecNormSq u ≤ (9 / 4) * vecNormSq v := by
  set a := Real.sqrt (vecNormSq v) with ha
  set c := Real.sqrt (vecNormSq (u - v)) with hc
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = vecNormSq v := Real.sq_sqrt (vecNormSq_nonneg v)
  have hc2 : c ^ 2 = vecNormSq (u - v) := Real.sq_sqrt (vecNormSq_nonneg _)
  have hca : c ≤ a / 2 := by
    apply abs_le_of_sq_le_sq' _ (by linarith) |>.2
    nlinarith
  have hdot := abs_vecDot_le_sqrt_mul v (u - v)
  rw [← ha, ← hc] at hdot
  have hexp : vecNormSq u = vecNormSq v + 2 * vecDot v (u - v) + vecNormSq (u - v) := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]; ring
  have hlo := (abs_le.1 hdot).1
  have hhi := (abs_le.1 hdot).2
  constructor
  · nlinarith
  · nlinarith

theorem jacMat_det_one {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    (pipeJac X t₁ (t, y)).det = 1 := by
  unfold pipeJac
  rw [jacMat_det]
  exact ch.det t ht y

theorem contDiff_Ft {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => X t y t₁) :=
  ch.smoothF.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_Ht {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun x => X t₁ x t) :=
  ch.smoothH.comp (contDiff_const.prodMk contDiff_id)

theorem jacMat_id (y : Vec 2) : jacMat (fun z : Vec 2 => z) y = 1 := by
  ext i j
  simp only [jacMat, fderiv_fun_id, ContinuousLinearMap.id_apply]
  fin_cases i <;> fin_cases j <;> simp [basisVec]

section Window

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)

include ch ht

theorem pipeJac_inv_eq (y : Vec 2) :
    (pipeJac X t₁ (t, y))⁻¹ = jacMat (fun x => X t₁ x t) (X t y t₁) := by
  have hF := (contDiff_Ft ch t).differentiable (by simp)
  have hH := (contDiff_Ht ch t).differentiable (by simp)
  have hcomp := jacMat_comp (G := fun x => X t₁ x t) (F := fun z => X t z t₁) (y := y)
    (hH _) (hF y)
  have hid : ((fun x => X t₁ x t) ∘ fun z => X t z t₁) = fun z : Vec 2 => z := by
    funext z; exact ch.left t ht z
  rw [hid, jacMat_id] at hcomp
  exact Matrix.inv_eq_left_inv hcomp.symm

theorem pipeJac_close (y v : Vec 2) :
    (1 / 4) * vecNormSq v ≤ vecNormSq ((pipeJac X t₁ (t, y)).mulVec v) ∧
      vecNormSq ((pipeJac X t₁ (t, y)).mulVec v) ≤ (9 / 4) * vecNormSq v := by
  have h := close_sq (u := (pipeJac X t₁ (t, y)).mulVec v) (v := v) (by
    have := ch.close t ht y v
    rwa [fderiv_apply_eq_jacMat_mulVec] at this)
  exact h

theorem pipeJac_inv_close (y w : Vec 2) :
    vecNormSq ((pipeJac X t₁ (t, y))⁻¹.mulVec w) ≤ (9 / 4) * vecNormSq w := by
  rw [pipeJac_inv_eq ch ht]
  have h := close_sq (u := (jacMat (fun x => X t₁ x t) (X t y t₁)).mulVec w) (v := w) (by
    have := ch.closeInv t ht (X t y t₁) w
    rwa [fderiv_apply_eq_jacMat_mulVec] at this)
  exact h.2

theorem metric_form (e : Vec 2) (y : Vec 2) :
    vecDot e ((pipeMetric X t₁ (t, y)).mulVec e) =
      vecNormSq ((pipeJac X t₁ (t, y)).mulVec ![e 1, -(e 0)]) := by
  have hadj : (pipeJac X t₁ (t, y))⁻¹ = (pipeJac X t₁ (t, y)).adjugate :=
    inv_jacMat_eq_adjugate (jacMat_det_one ch ht y)
  unfold pipeMetric
  rw [hadj]
  simp only [Matrix.adjugate_fin_two, vecDot, vecNormSq_two, Fin.sum_univ_two]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  ring

theorem pipeMetric_bounds (y e : Vec 2) :
    (1 / 4) * vecNormSq e ≤ vecDot e ((pipeMetric X t₁ (t, y)).mulVec e) ∧
      vecNormSq ((pipeMetric X t₁ (t, y)).mulVec e) ≤ (9 / 4) ^ 2 * vecNormSq e := by
  have hn : vecNormSq (![e 1, -(e 0)] : Vec 2) = vecNormSq e := by
    simp [vecNormSq_two]; ring
  have hform := metric_form ch ht e y
  have hc := pipeJac_close ch ht y ![e 1, -(e 0)]
  rw [hn] at hc
  refine ⟨by rw [hform]; exact hc.1, ?_⟩
  have hGe : (pipeMetric X t₁ (t, y)).mulVec e =
      (pipeJac X t₁ (t, y))⁻¹.mulVec (((pipeJac X t₁ (t, y))⁻¹)ᵀ.mulVec e) := by
    unfold pipeMetric; rw [Matrix.mulVec_mulVec]
  have hq : vecDot e ((pipeMetric X t₁ (t, y)).mulVec e) =
      vecNormSq (((pipeJac X t₁ (t, y))⁻¹)ᵀ.mulVec e) := by
    rw [hGe]
    unfold vecDot vecNormSq vecDot
    rw [← dotProduct, ← dotProduct, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have h1 := pipeJac_inv_close ch ht y (((pipeJac X t₁ (t, y))⁻¹)ᵀ.mulVec e)
  rw [← hq, hform] at h1
  rw [hGe]
  refine h1.trans ?_
  nlinarith [hc.2, vecNormSq_nonneg e]

end Window

theorem pipeMetric_symm (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) :
    (pipeMetric X t₁ p)ᵀ = pipeMetric X t₁ p := by
  unfold pipeMetric
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The everywhere-defined smooth surrogate `adj (D_yF_t)` of `(D_yF_t)⁻¹`. -/
def pipeAdj (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (pipeJac X t₁ p).adjugate

theorem pipeJac_apply_eq {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (t : ℝ) (y : Vec 2) (a b : Fin 2) :
    pipeJac X t₁ (t, y) a b =
      fderiv ℝ (fun q : ℝ × Vec 2 => X q.1 q.2 t₁ a) (t, y) (0, basisVec b) := by
  have hFa : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => X q.1 q.2 t₁ a) :=
    contDiff_pi.1 ch.smoothF a
  rw [← fderiv_slice hFa t y (basisVec b)]
  have hF := ((contDiff_Ft ch t).differentiable (by simp)) y
  have h := (hasFDerivAt_pi'.1 hF.hasFDerivAt) a
  change fderiv ℝ (fun z => X t z t₁) y (basisVec b) a = _
  rw [h.fderiv]
  rfl

theorem contDiff_pipeJac_entry {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => pipeJac X t₁ p a b) := by
  have hFa : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => X q.1 q.2 t₁ a) :=
    contDiff_pi.1 ch.smoothF a
  have : (fun p : ℝ × Vec 2 => pipeJac X t₁ p a b) =
      fun p => fderiv ℝ (fun q : ℝ × Vec 2 => X q.1 q.2 t₁ a) p (0, basisVec b) := by
    funext ⟨t, y⟩; exact pipeJac_apply_eq ch t y a b
  rw [this]
  exact contDiff_fderiv_apply_of_smooth hFa _

theorem contDiff_pipeAdj_entry {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T) (i k : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => pipeAdj X t₁ p i k) := by
  have : (fun p : ℝ × Vec 2 => pipeAdj X t₁ p i k) = fun p =>
      if i = k then pipeJac X t₁ p (1 - i) (1 - i) else - pipeJac X t₁ p i k := by
    funext p
    unfold pipeAdj
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases k <;> simp
  rw [this]
  split_ifs
  · exact contDiff_pipeJac_entry ch _ _
  · exact (contDiff_pipeJac_entry ch _ _).neg

theorem pipeAdj_eq_inv {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    pipeAdj X t₁ (t, y) = (pipeJac X t₁ (t, y))⁻¹ :=
  (inv_jacMat_eq_adjugate (jacMat_det_one ch ht y)).symm

theorem pipeMetric_eq_adj {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    pipeMetric X t₁ (t, y) = pipeAdj X t₁ (t, y) * (pipeAdj X t₁ (t, y))ᵀ := by
  rw [pipeAdj_eq_inv ch ht]; rfl
end

/-! # Divergence-freeness of the relative drift in material coordinates

For `t ∈ [t₁ - 8T, t₁]` and `ψ ∈ C^∞_c(ℝ²)`: `∫ V(t,y)·∇ψ(y) dy = 0`, by the change of variables
`x = F_t y` and distributional incompressibility of `b - b0`. -/

/-- The fixed-time chart as a homeomorphism of `Vec 2`. -/
def chartHomeo {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) : Vec 2 ≃ₜ Vec 2 where
  toFun := fun y => X t y t₁
  invFun := fun x => X t₁ x t
  left_inv := ch.left t ht
  right_inv := ch.right t ht
  continuous_toFun := (contDiff_Ft ch t).continuous
  continuous_invFun := (contDiff_Ht ch t).continuous

theorem integrable_vecDot_bdd {v : Vec 2 → Vec 2} (hv : Measurable v) {B : ℝ}
    (hB : ∀ x, ‖v x‖ ≤ B) {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : Integrable (fun x => vecDot (v x) (spGrad χ x)) := by
  have hi : ∀ i : Fin 2, Integrable (fun x => v x i * spGrad χ x i) := by
    intro i
    have hcont : Continuous fun x => spGrad χ x i :=
      (contDiff_fderiv_apply_of_smooth hχ (basisVec i)).continuous
    have hint : Integrable (fun x => spGrad χ x i) :=
      hcont.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_apply hc _)
    refine hint.bdd_mul (c := B) ?_ ?_
    · exact ((measurable_pi_apply i).comp hv).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => (norm_le_pi_norm (v x) i).trans (hB x)
  simp only [vecDot]
  exact integrable_finsetSum _ fun i _ => hi i

theorem hasCompactSupport_comp_Ht {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)
    {ψ : Vec 2 → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (ψ ∘ fun x => X t₁ x t) := by
  have := hψc.comp_homeomorph (chartHomeo ch ht).symm
  exact this

theorem vecDot_mulVec_left (A : Matrix (Fin 2) (Fin 2) ℝ) (w g : Vec 2) :
    vecDot (A.mulVec w) g = vecDot w (Aᵀ.mulVec g) := by
  change (A.mulVec w) ⬝ᵥ g = w ⬝ᵥ (Aᵀ.mulVec g)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem pipe_vecDot_sub_left (u w g : Vec 2) : vecDot (u - w) g = vecDot u g - vecDot w g := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

/-- The relative drift is divergence free in material coordinates. -/
theorem pipeDrift_divFree {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)
    {b : ℝ → Vec 2 → Vec 2} {B : ℝ}
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2)
    (hb0m : Measurable fun p : ℝ × Vec 2 => b0 p.1 p.2)
    (hbB : ∀ t x, ‖b t x‖ ≤ B) (hb0B : ∀ t x, ‖b0 t x‖ ≤ B)
    (hdb : ∀ t, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b t x) (spGrad φ x) = 0)
    (hdb0 : ∀ t, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b0 t x) (spGrad φ x) = 0)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, vecDot (pipeDrift b b0 X t₁ (t, y)) (spGrad ψ y) = 0 := by
  set χ : Vec 2 → ℝ := ψ ∘ fun x => X t₁ x t with hχ
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := hψ.comp (contDiff_Ht ch t)
  have hχc : HasCompactSupport χ := hasCompactSupport_comp_Ht ch ht hψc
  set g : Vec 2 → ℝ := fun x => vecDot (b t x - b0 t x) (spGrad χ x) with hg
  have hpt : ∀ y, vecDot (pipeDrift b b0 X t₁ (t, y)) (spGrad ψ y) = g (X t y t₁) := by
    intro y
    have hHd := ((contDiff_Ht ch t).differentiable (by simp)) (X t y t₁)
    have hψd := (hψ.differentiable (by simp)) (X t₁ (X t y t₁) t)
    have hgrad := spGrad_comp hψd hHd
    have hcomp : spGrad χ (X t y t₁) = (jacMat (fun x => X t₁ x t) (X t y t₁))ᵀ.mulVec
        (spGrad ψ y) := by
      rw [hχ, hgrad, ch.left t ht y]
    simp only [hg, pipeDrift, hcomp, pipeJac_inv_eq ch ht]
    rw [vecDot_mulVec_left]
  have hmeas : ∀ s : ℝ, Measurable fun x => b s x := fun s =>
    hbm.comp (measurable_const.prodMk measurable_id)
  have hmeas0 : ∀ s : ℝ, Measurable fun x => b0 s x := fun s =>
    hb0m.comp (measurable_const.prodMk measurable_id)
  have hi1 := integrable_vecDot_bdd (hmeas t) (fun x => hbB t x) hχs hχc
  have hi2 := integrable_vecDot_bdd (hmeas0 t) (fun x => hb0B t x) hχs hχc
  have hint : ∫ x, g x = 0 := by
    simp only [hg, pipe_vecDot_sub_left]
    rw [integral_sub hi1 hi2, hdb t χ hχs hχc, hdb0 t χ hχs hχc, sub_zero]
  calc ∫ y, vecDot (pipeDrift b b0 X t₁ (t, y)) (spGrad ψ y)
      = ∫ y, g (X t y t₁) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x, g x := (ch.mp t ht).integral_comp (chartHomeo ch ht).measurableEmbedding g
    _ = 0 := hint

/-! # The space-time material map `Ψ(t,y) = (t, F_t y)`

To change variables on all of `ℝ × ℝ²` the time variable is clamped to the window
`[t₁ - 8T, t₁]`; the resulting `pipeMap` is a measure preserving homeomorphism of `ℝ × Vec 2`
that agrees with `(t,y) ↦ (t, F_t y)` for `t` in the window. -/

section
/-- Clamp `t` to the window `[t₁ - 8T, t₁]`. -/
def pipeClampT (t₁ T t : ℝ) : ℝ := max (t₁ - 8 * T) (min t t₁)

theorem pipeClampT_mem {t₁ T : ℝ} (hT : 0 ≤ T) (t : ℝ) : pipeClampT t₁ T t ∈ Set.Icc (t₁ - 8 * T) t₁ :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem pipeClampT_eq {t₁ T t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) : pipeClampT t₁ T t = t := by
  unfold pipeClampT
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_pipeClampT (t₁ T : ℝ) : Continuous (pipeClampT t₁ T) := by
  unfold pipeClampT; fun_prop

/-- The material map with clamped time. -/
def pipeMap (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  (p.1, X (pipeClampT t₁ T p.1) p.2 t₁)

/-- The inverse of `pipeMap`. -/
def pipeMapInv (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  (p.1, X t₁ p.2 (pipeClampT t₁ T p.1))

section

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T)

include ch hT

omit hT in
theorem continuous_pipeMap : Continuous (pipeMap X t₁ T) := by
  unfold pipeMap
  have h1 : Continuous fun p : ℝ × Vec 2 => (pipeClampT t₁ T p.1, p.2) :=
    ((continuous_pipeClampT t₁ T).comp continuous_fst).prodMk continuous_snd
  exact continuous_fst.prodMk (ch.smoothF.continuous.comp h1)

omit hT in
theorem continuous_pipeMapInv : Continuous (pipeMapInv X t₁ T) := by
  unfold pipeMapInv
  have h1 : Continuous fun p : ℝ × Vec 2 => (pipeClampT t₁ T p.1, p.2) :=
    ((continuous_pipeClampT t₁ T).comp continuous_fst).prodMk continuous_snd
  exact continuous_fst.prodMk (ch.smoothH.continuous.comp h1)

/-- `pipeMap` as a homeomorphism. -/
def pipeHomeo : (ℝ × Vec 2) ≃ₜ (ℝ × Vec 2) where
  toFun := pipeMap X t₁ T
  invFun := pipeMapInv X t₁ T
  left_inv := by
    rintro ⟨t, y⟩
    have hm := pipeClampT_mem hT.le (t₁ := t₁) t
    simp only [pipeMap, pipeMapInv, ch.left _ hm]
  right_inv := by
    rintro ⟨t, x⟩
    have hm := pipeClampT_mem hT.le (t₁ := t₁) t
    simp only [pipeMap, pipeMapInv, ch.right _ hm]
  continuous_toFun := continuous_pipeMap ch
  continuous_invFun := continuous_pipeMapInv ch

theorem pipeMap_mp : MeasurePreserving (pipeMap X t₁ T) volume volume := by
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (y : Vec 2) => X (pipeClampT t₁ T t) y t₁) := by
    have h1 : Continuous fun p : ℝ × Vec 2 => (pipeClampT t₁ T p.1, p.2) :=
      ((continuous_pipeClampT t₁ T).comp continuous_fst).prodMk continuous_snd
    exact (ch.smoothF.continuous.comp h1).measurable
  have := (MeasurePreserving.id (volume : Measure ℝ)).skew_product (μc := (volume : Measure (Vec 2)))
    (μd := (volume : Measure (Vec 2))) hmeas (Filter.Eventually.of_forall fun t => by
      have := (ch.mp _ (pipeClampT_mem hT.le (t₁ := t₁) t)).map_eq
      exact this)
  rw [← Measure.volume_eq_prod] at this
  exact this

end

theorem pipeMap_apply_of_mem {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    pipeMap X t₁ T (t, y) = (t, X t y t₁) := by
  simp [pipeMap, pipeClampT_eq ht]
end

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix Filter Topology
namespace AVRegularity.Applications

/-! # Bounds for the chart coefficients

`pipe_coeff_bounds_uniform`: for the construction and `t ∈ [t₁ - 8T, t₁]`, the chart metric `G`
satisfies `1/4 |e|² ≤ e·Ge`, `|Ge|² ≤ (9/4)² |e|²`; the relative drift satisfies
`|V|² ≤ (C₂ ε_{n-1}^α)²` and is divergence free in material coordinates; `G` and `V` are
measurable and `G` is continuous on the window. -/

theorem measurable_pipeJac_inv_entry {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T) (i k : Fin 2) :
    Measurable fun p : ℝ × Vec 2 => (pipeJac X t₁ p)⁻¹ i k := by
  have hdet : Measurable fun p : ℝ × Vec 2 => (pipeJac X t₁ p).det := by
    have : (fun p : ℝ × Vec 2 => (pipeJac X t₁ p).det) = fun p =>
        pipeJac X t₁ p 0 0 * pipeJac X t₁ p 1 1 - pipeJac X t₁ p 0 1 * pipeJac X t₁ p 1 0 := by
      funext p; rw [Matrix.det_fin_two]
    rw [this]
    exact ((((contDiff_pipeJac_entry ch 0 0).continuous.mul (contDiff_pipeJac_entry ch 1 1).continuous).sub
      ((contDiff_pipeJac_entry ch 0 1).continuous.mul
        (contDiff_pipeJac_entry ch 1 0).continuous))).measurable
  have : (fun p : ℝ × Vec 2 => (pipeJac X t₁ p)⁻¹ i k) = fun p =>
      (pipeJac X t₁ p).det⁻¹ * pipeAdj X t₁ p i k := by
    funext p
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  rw [this]
  exact hdet.inv.mul (contDiff_pipeAdj_entry ch i k).continuous.measurable

theorem measurable_pipeMetric_entry {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T) (i k : Fin 2) :
    Measurable fun p : ℝ × Vec 2 => pipeMetric X t₁ p i k := by
  have : (fun p : ℝ × Vec 2 => pipeMetric X t₁ p i k) = fun p =>
      ∑ j : Fin 2, (pipeJac X t₁ p)⁻¹ i j * (pipeJac X t₁ p)⁻¹ k j := by
    funext p; simp [pipeMetric, Matrix.mul_apply]
  rw [this]
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_pipeJac_inv_entry ch i j).mul (measurable_pipeJac_inv_entry ch k j)

theorem measurable_pipeDrift {b0 b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T)
    (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2)
    (hb0m : Measurable fun p : ℝ × Vec 2 => b0 p.1 p.2) :
    Measurable (pipeDrift b b0 X t₁) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hF : Measurable fun p : ℝ × Vec 2 => (p.1, X p.1 p.2 t₁) :=
    measurable_fst.prodMk ch.smoothF.continuous.measurable
  have hw : ∀ k : Fin 2, Measurable fun p : ℝ × Vec 2 =>
      (b p.1 (X p.1 p.2 t₁) - b0 p.1 (X p.1 p.2 t₁)) k := fun k =>
    (measurable_pi_apply k).comp ((hbm.comp hF).sub (hb0m.comp hF))
  have : (fun p : ℝ × Vec 2 => pipeDrift b b0 X t₁ p i) = fun p =>
      ∑ k : Fin 2, (pipeJac X t₁ p)⁻¹ i k *
        (b p.1 (X p.1 p.2 t₁) - b0 p.1 (X p.1 p.2 t₁)) k := by
    funext p; simp [pipeDrift, Matrix.mulVec, dotProduct]
  rw [this]
  exact Finset.measurable_sum _ fun k _ => (measurable_pipeJac_inv_entry ch i k).mul (hw k)

theorem continuousOn_pipeMetric {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t₁ T : ℝ} (ch : IsPipeChart b0 X t₁ T) :
    ContinuousOn (pipeMetric X t₁) {p : ℝ × Vec 2 | p.1 ∈ Set.Icc (t₁ - 8 * T) t₁} := by
  have hA : Continuous fun p : ℝ × Vec 2 => pipeAdj X t₁ p :=
    continuous_matrix fun i k => (contDiff_pipeAdj_entry ch i k).continuous
  have hG : Continuous fun p : ℝ × Vec 2 => pipeAdj X t₁ p * (pipeAdj X t₁ p)ᵀ :=
    hA.matrix_mul hA.matrix_transpose
  refine hG.continuousOn.congr ?_
  rintro ⟨t, y⟩ ht
  exact pipeMetric_eq_adj ch ht y

section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- Smoothness-free consequences of the construction used for the limit velocity `b`:
joint measurability, a uniform bound and distributional incompressibility on each slice. -/
theorem limit_velocity_facts (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    Measurable (fun p : ℝ × Vec 2 => b p.1 p.2) ∧ (∃ B : ℝ, ∀ t x, ‖b t x‖ ≤ B) ∧
      ∀ t, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, vecDot (b t x) (spGrad φ x) = 0 := by
  obtain ⟨_, C, _, _, _, _, _, _, _, _, _, _, hbdd⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  have hcont : ∀ M, Continuous fun p : ℝ × Vec 2 => streamVel (Φ M) p.1 p.2 := fun M =>
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)).smooth.continuous
  refine ⟨?_, ⟨C, fun t x => ?_⟩, ?_⟩
  · refine measurable_of_tendsto_metrizable (f := fun M p => streamVel (Φ M) p.1 p.2)
      (fun M => (hcont M).measurable) ?_
    exact tendsto_pi_nhds.2 fun p => hb p.1 p.2
  · exact le_of_tendsto (hb t x).norm (Filter.Eventually.of_forall fun M => hbdd M t x)
  · exact AVRegularity.Velocity.divFree_of_bounded_pointwise_limit (v := fun M => streamVel (Φ M))
      (fun M t => (hcont M).comp (continuous_const.prodMk continuous_id)) hbdd hb
      (AVRegularity.Velocity.streamSeq_velocity_divFree hζ hΛ hΦ)

/-- **Chart coefficient bounds, uniform constant.** The constant `C₂` of the drift bound does not
depend on `n`, `X`, `t₁`, `T`. -/
theorem pipe_coeff_bounds_uniform (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (X : ℝ → Vec 2 → ℝ → Vec 2),
      AVenhance.IsFlow (streamVel (Φ (n - 2))) X → ∀ (t₁ T : ℝ), 0 < T →
      8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
      (∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ y e : Vec 2,
        (1 / 4) * vecNormSq e ≤ vecDot e ((pipeMetric X t₁ (t, y)).mulVec e) ∧
          vecNormSq ((pipeMetric X t₁ (t, y)).mulVec e) ≤ (9 / 4) ^ 2 * vecNormSq e) ∧
      (∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ y : Vec 2,
        vecNormSq (pipeDrift b (streamVel (Φ (n - 2))) X t₁ (t, y)) ≤
          (C₂ * ocEpsilon q Λ (n - 1) ^ α) ^ 2) ∧
      (∀ p : ℝ × Vec 2, (pipeMetric X t₁ p)ᵀ = pipeMetric X t₁ p) ∧
      ContinuousOn (pipeMetric X t₁) {p : ℝ × Vec 2 | p.1 ∈ Set.Icc (t₁ - 8 * T) t₁} ∧
      (∀ i k : Fin 2, Measurable fun p : ℝ × Vec 2 => pipeMetric X t₁ p i k) ∧
      Measurable (pipeDrift b (streamVel (Φ (n - 2))) X t₁) ∧
      (∀ t ∈ Set.Icc (t₁ - 8 * T) t₁, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        ∫ y, vecDot (pipeDrift b (streamVel (Φ (n - 2))) X t₁ (t, y)) (spGrad ψ y) = 0) := by
  obtain ⟨_, C, hC0, _, _, htail, _, _, _, _, _, _, hbdd⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  refine ⟨3 * C, by positivity, fun n hn X hX t₁ T hT hh => ?_⟩
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT hh
  obtain ⟨hbm, ⟨B, hBb⟩, hdb⟩ := limit_velocity_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  have hcont : ∀ M, Continuous fun p : ℝ × Vec 2 => streamVel (Φ M) p.1 p.2 := fun M =>
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)).smooth.continuous
  have hb0m := (hcont (n - 2)).measurable
  have hn1 : n - 2 + 1 = n - 1 := by omega
  refine ⟨fun t ht y e => pipeMetric_bounds ch ht y e, ?_,
    pipeMetric_symm X t₁, continuousOn_pipeMetric ch, measurable_pipeMetric_entry ch,
    measurable_pipeDrift ch hbm hb0m, ?_⟩
  · intro t ht y
    have hw : ‖b t (X t y t₁) - streamVel (Φ (n - 2)) t (X t y t₁)‖ ≤
        C * ocEpsilon q Λ (n - 1) ^ α := by
      have := htail (n - 2) t (X t y t₁)
      rwa [hn1] at this
    have h1 := pipeJac_inv_close ch ht y
      (b t (X t y t₁) - streamVel (Φ (n - 2)) t (X t y t₁))
    have h2 := vecNormSq_le_two_mul_norm_sq
      (b t (X t y t₁) - streamVel (Φ (n - 2)) t (X t y t₁))
    have h3 : ‖b t (X t y t₁) - streamVel (Φ (n - 2)) t (X t y t₁)‖ ^ 2 ≤
        (C * ocEpsilon q Λ (n - 1) ^ α) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h4 : vecNormSq (pipeDrift b (streamVel (Φ (n - 2))) X t₁ (t, y)) ≤
        (9 / 4) * vecNormSq (b t (X t y t₁) - streamVel (Φ (n - 2)) t (X t y t₁)) := h1
    have h5 : 0 ≤ (C * ocEpsilon q Λ (n - 1) ^ α) ^ 2 := sq_nonneg _
    calc _ ≤ _ := h4
      _ ≤ (3 * C * ocEpsilon q Λ (n - 1) ^ α) ^ 2 := by nlinarith
  · intro t ht ψ hψ hψc
    exact pipeDrift_divFree (B := max B C) ch ht hbm hb0m (fun t x => (hBb t x).trans (le_max_left _ _))
      (fun t x => (hbdd (n - 2) t x).trans (le_max_right _ _)) hdb
      (AVRegularity.Velocity.streamSeq_velocity_divFree hζ hΛ hΦ (n - 2)) hψ hψc

end Construction

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Matrix
namespace AVRegularity.Applications

/-! # Pushing forward test functions along the material chart

`pipePushTest X t₁ ζ (t,x) = ζ(t, F_t⁻¹ x)`. For smooth `ζ` and `t` in the window:
* `pipePushTest ζ (t, F_t y) = ζ(t, y)`;
* `∇ζ = (D_yF)ᵀ (∇φ ∘ F)` hence `G∇ζ = (D_yF)⁻¹ (∇φ ∘ F)` and `V·∇ζ = ((b - b0)·∇φ) ∘ F`;
* `(∂ₜφ + b0·∇φ) ∘ F = ∂ₜζ`;
* `Δφ ∘ F = div_y(G ∇ζ)` (Piola). -/

/-- The push-forward `φ(t,x) = ζ(t, X(t₁, x, t))` of a test function to physical coordinates. -/
def pipePushTest (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (ζ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  ζ (p.1, X t₁ p.2 p.1)

theorem stSpaceGrad_eq_slice {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (τ : ℝ)
    (y : Vec 2) : stSpaceGrad ζ (τ, y) = spGrad (fun z => ζ (τ, z)) y := by
  ext i
  simp only [stSpaceGrad, spGrad]
  rw [fderiv_slice hζ]

theorem fderiv_st_space {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (τ : ℝ) (y v : Vec 2) :
    fderiv ℝ ζ (τ, y) (0, v) = vecDot (stSpaceGrad ζ (τ, y)) v := by
  rw [← fderiv_slice hζ, fderiv_scalar_eq_dot, stSpaceGrad_eq_slice hζ]

theorem stSpaceLap_eq_divSp {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (τ : ℝ)
    (x : Vec 2) : stSpaceLap φ (τ, x) = divSp (fun z => stSpaceGrad φ (τ, z)) x := by
  unfold stSpaceLap divSp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fderiv_slice (contDiff_fderiv_apply_of_smooth hφ (0, basisVec i))]
  rfl

section

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

theorem contDiff_pipePushTest {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (pipePushTest X t₁ ζ) :=
  hζ.comp (contDiff_fst.prodMk ch.smoothH)

theorem pipePushTest_apply {ζ : ℝ × Vec 2 → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁)
    (y : Vec 2) : pipePushTest X t₁ ζ (t, X t y t₁) = ζ (t, y) := by
  simp [pipePushTest, ch.left t ht y]

/-- Time derivative of the chart: `∂ₜ F(t,y) = b0(t, F(t,y))`. -/
theorem fderiv_chart_time (t : ℝ) (y : Vec 2) :
    fderiv ℝ (fun q : ℝ × Vec 2 => X q.1 q.2 t₁) (t, y) (1, 0) = b0 t (X t y t₁) := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => X q.1 q.2 t₁) (t, y) :=
    (ch.smoothF.differentiable (by simp)) _
  have hc : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have h := hd.hasFDerivAt.comp_hasDerivAt t hc
  exact h.unique (ch.flow.2 y t₁ t)

/-- The gradient identity for the pushed test: `∇ζ = (D_yF)ᵀ (∇φ ∘ F)`. -/
theorem stSpaceGrad_push {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    stSpaceGrad ζ (t, y) = (pipeJac X t₁ (t, y))ᵀ.mulVec
      (stSpaceGrad (pipePushTest X t₁ ζ) (t, X t y t₁)) := by
  have hφ := contDiff_pipePushTest ch hζ
  have hslice : (fun z => ζ (t, z)) = (fun x => pipePushTest X t₁ ζ (t, x)) ∘ fun z => X t z t₁ := by
    funext z; exact (pipePushTest_apply ch ht z).symm
  rw [stSpaceGrad_eq_slice hζ, hslice, spGrad_comp, ← stSpaceGrad_eq_slice hφ]
  · rfl
  · exact ((hφ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) _
  · exact ((contDiff_Ft ch t).differentiable (by simp)) y

theorem pipeJac_mul_inv {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    pipeJac X t₁ (t, y) * (pipeJac X t₁ (t, y))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [jacMat_det_one ch ht y]; exact isUnit_one)

theorem inv_transpose_mulVec {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y g : Vec 2) :
    ((pipeJac X t₁ (t, y))⁻¹)ᵀ.mulVec ((pipeJac X t₁ (t, y))ᵀ.mulVec g) = g := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, pipeJac_mul_inv ch ht y,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- `G ∇ζ = (D_yF)⁻¹ (∇φ ∘ F)`. -/
theorem metric_mulVec_push {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    (pipeMetric X t₁ (t, y)).mulVec (stSpaceGrad ζ (t, y)) =
      (pipeJac X t₁ (t, y))⁻¹.mulVec (stSpaceGrad (pipePushTest X t₁ ζ) (t, X t y t₁)) := by
  rw [stSpaceGrad_push ch hζ ht y]
  unfold pipeMetric
  rw [← Matrix.mulVec_mulVec, inv_transpose_mulVec ch ht]

/-- `V·∇ζ = ((b - b0)·∇φ) ∘ F`. -/
theorem drift_dot_push {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (b : ℝ → Vec 2 → Vec 2) (y : Vec 2) :
    vecDot (pipeDrift b b0 X t₁ (t, y)) (stSpaceGrad ζ (t, y)) =
      vecDot (b t (X t y t₁) - b0 t (X t y t₁))
        (stSpaceGrad (pipePushTest X t₁ ζ) (t, X t y t₁)) := by
  rw [stSpaceGrad_push ch hζ ht y]
  unfold pipeDrift
  rw [vecDot_mulVec_left, inv_transpose_mulVec ch ht]

/-- `(∂ₜφ + b0·∇φ) ∘ F = ∂ₜζ`. -/
theorem stTimeDeriv_push {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₁ - 8 * T) t₁) (y : Vec 2) :
    stTimeDeriv ζ (t, y) = stTimeDeriv (pipePushTest X t₁ ζ) (t, X t y t₁) +
      vecDot (b0 t (X t y t₁)) (stSpaceGrad (pipePushTest X t₁ ζ) (t, X t y t₁)) := by
  have hφ := contDiff_pipePushTest ch hζ
  set Ψ : ℝ × Vec 2 → ℝ × Vec 2 := fun q => (q.1, X q.1 q.2 t₁) with hΨ
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ := contDiff_fst.prodMk ch.smoothF
  have hev : ζ =ᶠ[nhds (t, y)] (pipePushTest X t₁ ζ) ∘ Ψ := by
    have hopen : IsOpen {q : ℝ × Vec 2 | q.1 ∈ Set.Ioo (t₁ - 8 * T) t₁} :=
      isOpen_Ioo.preimage continuous_fst
    filter_upwards [hopen.mem_nhds (show (t, y) ∈ _ from ht)] with q hq
    exact (pipePushTest_apply ch ⟨hq.1.le, hq.2.le⟩ q.2).symm
  have hΨd : DifferentiableAt ℝ Ψ (t, y) := (hΨs.differentiable (by simp)) _
  have hφd : DifferentiableAt ℝ (pipePushTest X t₁ ζ) (Ψ (t, y)) :=
    (hφ.differentiable (by simp)) _
  have hF : DifferentiableAt ℝ (fun q : ℝ × Vec 2 => X q.1 q.2 t₁) (t, y) :=
    (ch.smoothF.differentiable (by simp)) _
  have hΨ1 : fderiv ℝ Ψ (t, y) (1, 0) = (1, b0 t (X t y t₁)) := by
    rw [hΨ, DifferentiableAt.fderiv_prodMk differentiableAt_fst hF]
    simp [fderiv_chart_time ch t y, (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, y))).fderiv]
  unfold stTimeDeriv
  rw [hev.fderiv_eq, fderiv_comp _ hφd hΨd, ContinuousLinearMap.comp_apply, hΨ1]
  have hsplit : ((1 : ℝ), b0 t (X t y t₁)) = ((1 : ℝ), (0 : Vec 2)) + (0, b0 t (X t y t₁)) := by
    simp
  rw [hsplit, map_add, fderiv_st_space hφ]
  have hΨt : Ψ (t, y) = (t, X t y t₁) := rfl
  rw [hΨt]
  congr 1
  simp [vecDot, mul_comm]

/-- `Δφ ∘ F = div_y(G ∇ζ)` (Piola identity). -/
theorem stSpaceLap_push {ζ : ℝ × Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) :
    stSpaceLap (pipePushTest X t₁ ζ) (t, X t y t₁) =
      divSp (fun z => (pipeMetric X t₁ (t, z)).mulVec (stSpaceGrad ζ (t, z))) y := by
  have hφ := contDiff_pipePushTest ch hζ
  rw [stSpaceLap_eq_divSp hφ]
  have hw : ContDiff ℝ (⊤ : ℕ∞) fun z => stSpaceGrad (pipePushTest X t₁ ζ) (t, z) := by
    refine contDiff_pi.2 fun i => ?_
    exact (contDiff_fderiv_apply_of_smooth hφ (0, basisVec i)).comp
      (contDiff_const.prodMk contDiff_id)
  have := piola_div (contDiff_Ft ch t) (fun z => jacMat_det_one ch ht z) hw y
  rw [← this]
  congr 1
  funext z
  exact (metric_mulVec_push ch hζ ht z).symm

end

end AVRegularity.Applications
end
