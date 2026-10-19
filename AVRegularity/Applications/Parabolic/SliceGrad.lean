-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives
public import AVRegularity.Statements.Definitions.EuclidBall

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Space-time conventions for the applications layer

Points of space-time are `p : ℝ × Vec 2`, time first. Backward cylinders are
`openCyl z r = (z.1 - r², z.1) × B_r(z.2)` (Euclidean disc); the closed-top version used by the
Campanato characterization is `External.Campanato.cylinder z r`. The weak formulation of
`∂τU - div((I+K)∇U) + d·∇U = 0` in `Q₁`
is `IsSkewDriftWeak`. -/

/-- Open backward cylinder `Q_r(z) = (z.1 - r², z.1) × B_r(z.2)`. -/
def openCyl (z : ℝ × Vec 2) (r : ℝ) : Set (ℝ × Vec 2) :=
  Set.Ioo (z.1 - r ^ 2) z.1 ×ˢ euclidBall z.2 r

/-- The time derivative `∂ₜφ` of a space-time function. -/
def stTimeDeriv (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  fderiv ℝ φ p (1, 0)

/-- The spatial gradient `∇ₓφ` of a space-time function. -/
def stSpaceGrad (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : Vec 2 :=
  fun i => fderiv ℝ φ p (0, basisVec i)

/-- The spatial Laplacian `Δₓφ` of a space-time function. -/
def stSpaceLap (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i)

/-- Smooth test functions with compact support inside `O`. -/
def IsSTTest (O : Set (ℝ × Vec 2)) (φ : ℝ × Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O

/-- The gradient of a spatial function, `∇ψ(y)`. -/
def spGrad (ψ : Vec 2 → ℝ) (y : Vec 2) : Vec 2 :=
  fun i => fderiv ℝ ψ y (basisVec i)

/-- Smooth spatial test functions with compact support inside `B`. -/
def IsSpTest (B : Set (Vec 2)) (ψ : Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ B

/-- The concrete energy class `L^∞(-1,0;L²(B₁)) ∩ L²(-1,0;H¹(B₁))` on `Q₁` with spatial
gradient `DU`. -/
def IsEnergyClassQ1 (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) : Prop :=
  MemLp U 2 (volume.restrict (openCyl 0 1)) ∧
  (∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (openCyl 0 1))) ∧
  (∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
    HasWeakGradientOn (euclidBall 0 1) (fun y => U (τ, y)) (fun y => DU (τ, y))) ∧
  ∃ M : ℝ, ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)),
    ∫ y in euclidBall 0 1, U (τ, y) ^ 2 ≤ M

/-- `U` is a weak solution of `∂τU - div((I+K)∇U) + d·∇U = 0` in `Q₁`:
for every `φ ∈ C^∞_c(Q₁)`,
`∬ (-U ∂τφ + (I+K)∇U·∇φ + (d·∇U) φ) = 0`. -/
def IsSkewDriftWeak (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
    (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2) : Prop :=
  ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 1) φ →
    ∫ p in openCyl 0 1,
      (-(U p * stTimeDeriv φ p) + vecDot ((1 + K p).mulVec (DU p)) (stSpaceGrad φ p)
        + vecDot (d p) (DU p) * φ p) = 0

/-- The drift is divergence free on `Q₁`: for a.e. `τ`, `∫_{B₁} d(τ,·)·∇ψ = 0` for every
`ψ ∈ C^∞_c(B₁)`. -/
def IsDivFreeQ1 (d : ℝ × Vec 2 → Vec 2) : Prop :=
  ∀ᵐ τ ∂(volume.restrict (Set.Ioo (-1 : ℝ) 0)), ∀ ψ : Vec 2 → ℝ, IsSpTest (euclidBall 0 1) ψ →
    ∫ y in euclidBall 0 1, vecDot (d (τ, y)) (spGrad ψ y) = 0

/-! # Local weak solutions and translating tubes

`IsLocalWeakSolution v κ O u Du` is the local weak solution class of
display (8.3) of the paper: `u ∈ L²_loc(O)`, slices in `H¹_loc(O_t)` for a.e. `t`
with slice gradients `Du ∈ L²_loc(O)`, and the weak equation of
`∂ₜu + v·∇u - κΔu = 0` against `C^∞_c(O)`. `closedTube X t r κ` is the closed backward
translating tube of radius `r` and duration `r²/κ` along the curve `X`, ending at time `t`.
-/

/-- The time section `O_t = {x : (t,x) ∈ O}`. -/
def timeSection (O : Set (ℝ × Vec 2)) (t : ℝ) : Set (Vec 2) := {x | (t, x) ∈ O}

/-- Local weak solution of `∂ₜu + v·∇u - κΔu = 0` in `O` (display (8.3) of the paper). -/
def IsLocalWeakSolution (v : ℝ → Vec 2 → Vec 2) (κ : ℝ) (O : Set (ℝ × Vec 2))
    (u : ℝ × Vec 2 → ℝ) (Du : ℝ × Vec 2 → Vec 2) : Prop :=
  (∀ Kc : Set (ℝ × Vec 2), Kc ⊆ O → IsCompact Kc → MemLp u 2 (volume.restrict Kc)) ∧
  (∀ Kc : Set (ℝ × Vec 2), Kc ⊆ O → IsCompact Kc →
    ∀ i : Fin 2, MemLp (fun p => Du p i) 2 (volume.restrict Kc)) ∧
  (∀ᵐ t ∂(volume : Measure ℝ),
    HasWeakGradientOn (timeSection O t) (fun x => u (t, x)) (fun x => Du (t, x))) ∧
  ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest O φ →
    ∫ p in O, (-(u p * stTimeDeriv φ p) + vecDot (v p.1 p.2) (Du p) * φ p
      + κ * vecDot (Du p) (stSpaceGrad φ p)) = 0

/-- `X` is a backward trajectory of `v` on `[t - h, t]`: `Ẋ(τ) = v(τ, X(τ))` there
(one-sided at the endpoints). -/
def IsBackwardTrajectory (v : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2) (t h : ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (t - h) t, HasDerivWithinAt X (v τ (X τ)) (Set.Icc (t - h) t) τ

/-- The closed translating tube `{(τ,x) : t - r²/κ ≤ τ ≤ t, |x - X(τ)| ≤ r}`. -/
def closedTube (X : ℝ → Vec 2) (t r κ : ℝ) : Set (ℝ × Vec 2) :=
  {p | p.1 ∈ Set.Icc (t - r ^ 2 / κ) t ∧ vecNormSq (p.2 - X p.1) ≤ r ^ 2}

/-! # Integration by parts against space-time test functions

* `integral_stTimeDeriv_eq_zero`, `integral_stSpaceLap_eq_zero`: derivatives of a compactly
  supported smooth function integrate to zero;
* `integral_mul_stSpaceLap`: if the slices of `H` have weak gradient `DH` for a.e. time, then
  `∬ H Δφ = -∬ DH·∇φ` for `φ ∈ C^∞_c(J × B)`. -/

theorem integral_fderiv_eq_zero_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcs : HasCompactSupport φ) (v : E) : ∫ x, fderiv ℝ φ x v ∂μ = 0 := by
  have hc1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdcont : Continuous fun x => fderiv ℝ φ x v :=
    (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdcs : HasCompactSupport fun x => fderiv ℝ φ x v :=
    (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := v)
    (f := fun _ : E => (1 : ℝ)) (g := φ)
    (by simp) (by simpa using hdcont.integrable_of_hasCompactSupport hdcs)
    (by simpa using hc1.continuous.integrable_of_hasCompactSupport hcs)
    (fun _ _ => differentiableAt_const _) (fun x _ => (hc1.differentiable one_ne_zero) x)
  simpa using h

theorem setIntegral_eq_integral_of_tsupport {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] {μ : Measure E} {O : Set E} {f g : E → ℝ}
    (hts : tsupport g ⊆ O) (hfg : ∀ x, x ∉ tsupport g → f x = 0) :
    ∫ x in O, f x ∂μ = ∫ x, f x ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hfg x fun h => hx (hts h)

theorem contDiff_fderiv_apply_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => fderiv ℝ φ x v :=
  (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hcs : HasCompactSupport φ) (v : E) :
    HasCompactSupport fun x => fderiv ℝ φ x v :=
  (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)

theorem tsupport_fderiv_apply_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (v : E) : tsupport (fun x => fderiv ℝ φ x v) ⊆ tsupport φ := by
  refine (closure_mono ?_).trans (closure_minimal (support_fderiv_subset (𝕜 := ℝ)) isClosed_closure)
  intro x hx h0
  apply hx
  simp [h0]

instance isAddHaarMeasure_volume_spaceTime :
    (volume : Measure (ℝ × Vec 2)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

theorem integral_stTimeDeriv_eq_zero {O : Set (ℝ × Vec 2)} {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest O φ) : ∫ p in O, stTimeDeriv φ p = 0 := by
  rw [setIntegral_eq_integral_of_tsupport (g := φ) hφ.2.2 fun p hp => by
    simp [stTimeDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hp]]
  exact integral_fderiv_eq_zero_of_hasCompactSupport hφ.1 hφ.2.1 (1, 0)

theorem integral_stSpaceLap_eq_zero {O : Set (ℝ × Vec 2)} {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest O φ) : ∫ p in O, stSpaceLap φ p = 0 := by
  have hcont : ∀ i : Fin 2, Continuous fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) := by
    intro i
    exact (contDiff_fderiv_apply_of_smooth (contDiff_fderiv_apply_of_smooth hφ.1 _) _).continuous
  have hcs : ∀ i : Fin 2, HasCompactSupport fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) :=
    fun i => hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hφ.2.1 _) _
  have hsub : ∀ i : Fin 2, tsupport (fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i)) ⊆ tsupport φ :=
    fun i => (tsupport_fderiv_apply_subset _ _).trans (tsupport_fderiv_apply_subset _ _)
  unfold stSpaceLap
  rw [integral_finsetSum _ fun i _ =>
    ((hcont i).integrable_of_hasCompactSupport (hcs i)).integrableOn]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [setIntegral_eq_integral_of_tsupport (g := φ) hφ.2.2 fun p hp =>
    image_eq_zero_of_notMem_tsupport (f := fun p =>
      fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i)) fun h => hp (hsub i h)]
  exact integral_fderiv_eq_zero_of_hasCompactSupport
    (contDiff_fderiv_apply_of_smooth hφ.1 _) (hasCompactSupport_fderiv_apply hφ.2.1 _) _

/-! # Slice weak gradients against space-time tests

If for a.e. `τ ∈ (a,b)` the slice `H(τ,·)` has weak gradient `DH(τ,·)` on `B`, then
`∬ H ∂ᵢψ = -∬ DHᵢ ψ` for every `ψ ∈ C^∞_c((a,b) × B)`, and in particular
`∬ H Δφ = -∬ DH·∇φ`. -/

theorem volume_restrict_prod_eq (A : Set ℝ) (B : Set (Vec 2)) :
    volume.restrict (A ×ˢ B) = (volume.restrict A).prod (volume.restrict B) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- The time slice `y ↦ ψ(τ, y)` of a space-time test is a spatial test. -/
theorem isSpTest_slice {a b : ℝ} {B : Set (Vec 2)} {ψ : ℝ × Vec 2 → ℝ}
    (hψ : IsSTTest (Set.Ioo a b ×ˢ B) ψ) (τ : ℝ) : IsSpTest B (fun y => ψ (τ, y)) := by
  obtain ⟨hsm, hcs, hts⟩ := hψ
  have hcont : Continuous (fun y : Vec 2 => (τ, y)) := continuous_const.prodMk continuous_id
  have hsub : tsupport (fun y => ψ (τ, y)) ⊆ (fun y : Vec 2 => (τ, y)) ⁻¹' tsupport ψ := by
    refine closure_minimal ?_ (isClosed_tsupport ψ |>.preimage hcont)
    intro y hy
    exact subset_closure hy
  refine ⟨hsm.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
  · refine IsCompact.of_isClosed_subset (hcs.image continuous_snd) (isClosed_tsupport _) ?_
    intro y hy
    exact ⟨(τ, y), hsub hy, rfl⟩
  · intro y hy
    exact (hts (hsub hy)).2

theorem fderiv_slice {ψ : ℝ × Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (τ : ℝ) (y v : Vec 2) :
    fderiv ℝ (fun y => ψ (τ, y)) y v = fderiv ℝ ψ (τ, y) (0, v) := by
  have hd : DifferentiableAt ℝ ψ (τ, y) := (hψ.differentiable (by simp)).differentiableAt
  have hin : HasFDerivAt (fun y : Vec 2 => (τ, y)) (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  change fderiv ℝ (ψ ∘ fun y : Vec 2 => (τ, y)) y v = _
  rw [(hd.hasFDerivAt.comp y hin).fderiv]
  rfl

/-- Slice integration by parts for one partial derivative. -/
theorem integral_mul_partial_slice {a b : ℝ} {B : Set (Vec 2)} {H g : ℝ × Vec 2 → ℝ}
    (i : Fin 2)
    (hH : IntegrableOn H (Set.Ioo a b ×ˢ B)) (hg : IntegrableOn g (Set.Ioo a b ×ˢ B))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      HasWeakPartialDerivOn B i (fun y => H (τ, y)) (fun y => g (τ, y)))
    {ψ : ℝ × Vec 2 → ℝ} (hψ : IsSTTest (Set.Ioo a b ×ˢ B) ψ) :
    ∫ p in Set.Ioo a b ×ˢ B, H p * fderiv ℝ ψ p (0, basisVec i) =
      -∫ p in Set.Ioo a b ×ˢ B, g p * ψ p := by
  have hψc : Continuous ψ := hψ.1.continuous
  have hdc : Continuous fun p => fderiv ℝ ψ p (0, basisVec i) :=
    (contDiff_fderiv_apply_of_smooth hψ.1 _).continuous
  obtain ⟨Cψ, hCψ⟩ := hψc.bounded_above_of_compact_support hψ.2.1
  obtain ⟨Cd, hCd⟩ := hdc.bounded_above_of_compact_support
    (hasCompactSupport_fderiv_apply hψ.2.1 _)
  have hint1 : Integrable (fun p => H p * fderiv ℝ ψ p (0, basisVec i))
      (volume.restrict (Set.Ioo a b ×ˢ B)) :=
    hH.mul_bdd hdc.aestronglyMeasurable (Filter.Eventually.of_forall hCd)
  have hint2 : Integrable (fun p => g p * ψ p) (volume.restrict (Set.Ioo a b ×ˢ B)) :=
    hg.mul_bdd hψc.aestronglyMeasurable (Filter.Eventually.of_forall hCψ)
  rw [volume_restrict_prod_eq] at hint1 hint2 ⊢
  rw [integral_prod _ hint1, integral_prod _ hint2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hgrad] with τ hτ
  have ht := isSpTest_slice hψ τ
  have h := hτ (fun y => ψ (τ, y)) ht.1 ht.2.1 ht.2.2
  simp only [fderiv_slice hψ.1] at h
  exact h

/-- `∬ H Δφ = -∬ DH·∇φ` when the slices of `H` have weak gradient `DH`. -/
theorem integral_mul_stSpaceLap {a b : ℝ} {B : Set (Vec 2)} {H : ℝ × Vec 2 → ℝ}
    {DH : ℝ × Vec 2 → Vec 2}
    (hH : IntegrableOn H (Set.Ioo a b ×ˢ B))
    (hDH : ∀ i : Fin 2, IntegrableOn (fun p => DH p i) (Set.Ioo a b ×ˢ B))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn B (fun y => H (τ, y)) (fun y => DH (τ, y)))
    {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (Set.Ioo a b ×ˢ B) φ) :
    ∫ p in Set.Ioo a b ×ˢ B, H p * stSpaceLap φ p =
      -∫ p in Set.Ioo a b ×ˢ B, vecDot (DH p) (stSpaceGrad φ p) := by
  have hψ : ∀ i : Fin 2, IsSTTest (Set.Ioo a b ×ˢ B) fun q => fderiv ℝ φ q (0, basisVec i) :=
    fun i => ⟨contDiff_fderiv_apply_of_smooth hφ.1 _, hasCompactSupport_fderiv_apply hφ.2.1 _,
      (tsupport_fderiv_apply_subset _ _).trans hφ.2.2⟩
  have hterm : ∀ i : Fin 2,
      ∫ p in Set.Ioo a b ×ˢ B, H p *
          fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) =
        -∫ p in Set.Ioo a b ×ˢ B, DH p i * fderiv ℝ φ p (0, basisVec i) := by
    intro i
    refine integral_mul_partial_slice i hH (hDH i) ?_ (hψ i)
    filter_upwards [hgrad] with τ hτ
    exact hτ i
  -- integrability of the summands
  have hbd : ∀ {f : ℝ × Vec 2 → ℝ}, Continuous f → HasCompactSupport f →
      ∀ {h : ℝ × Vec 2 → ℝ}, IntegrableOn h (Set.Ioo a b ×ˢ B) →
        Integrable (fun p => h p * f p) (volume.restrict (Set.Ioo a b ×ˢ B)) := by
    intro f hf hfc h hh
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
    exact hh.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hLsplit : ∫ p in Set.Ioo a b ×ˢ B, H p * stSpaceLap φ p =
      ∑ i : Fin 2, ∫ p in Set.Ioo a b ×ˢ B,
        H p * fderiv ℝ (fun q => fderiv ℝ φ q (0, basisVec i)) p (0, basisVec i) := by
    rw [← integral_finsetSum _ fun i _ => hbd
      (contDiff_fderiv_apply_of_smooth (hψ i).1 _).continuous
      (hasCompactSupport_fderiv_apply (hψ i).2.1 _) hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [stSpaceLap, Fin.sum_univ_two]
    ring
  have hRsplit : ∫ p in Set.Ioo a b ×ˢ B, vecDot (DH p) (stSpaceGrad φ p) =
      ∑ i : Fin 2, ∫ p in Set.Ioo a b ×ˢ B, DH p i * fderiv ℝ φ p (0, basisVec i) := by
    rw [← integral_finsetSum _ fun i _ => hbd (hψ i).1.continuous (hψ i).2.1 (hDH i)]
    rfl
  rw [hLsplit, hRsplit, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib]

end AVRegularity.Applications
end
