-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.DistributionDerivative
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open MeasureTheory SchwartzMap FourierTransform Homogenization
open scoped ENNReal FourierTransform RealInnerProductSpace
open AVRegularity.CoupledEnergyPlane.Fourier (HilbertTwo coordinateHilbertEquiv)
namespace AVRegularity.CycleWords.Assembly

/-! # Plancherel for integrable functions

For an integrable `c`, `‖𝓕 c‖₂ = ‖c‖₂` in `[0, ∞]`: either side is finite exactly when the other
is (`eLpNorm_fourier_eq_of_integrable`). Both directions identify the pointwise transform with the
`L²` transform as distributions: the multiplication formula `∫ φ 𝓕c = ∫ 𝓕φ c` against Schwartz
tests, the agreement of the `L²` and tempered transforms, and uniqueness of locally integrable
functions tested against smooth compactly supported functions. On `Vec 2`, rescaling `θ = -2πx`
gives `‖∫ e^{iθ·z} c(θ) dθ‖₂ = 2π ‖c‖₂` (`eLpNorm_expTransform`). -/

section Core

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem integral_schwartz_smul_fourier {c : V → ℂ} (hc : Integrable c) (φ : 𝓢(V, ℂ)) :
    ∫ ξ, φ ξ • 𝓕 c ξ = ∫ x, (𝓕 φ) x • c x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (e := Real.fourierChar) (L := innerₗ V) Real.continuous_fourierChar
    continuous_inner hc φ.integrable
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    simp
  rw [hflip] at h
  have h2 : ∫ ξ, φ ξ • 𝓕 c ξ = ∫ x, 𝓕 (φ : V → ℂ) x • c x := by
    calc ∫ ξ, φ ξ • 𝓕 c ξ = ∫ ξ, 𝓕 c ξ • φ ξ := by simp_rw [smul_eq_mul, mul_comm]
      _ = ∫ x, c x • 𝓕 (φ : V → ℂ) x := h
      _ = ∫ x, 𝓕 (φ : V → ℂ) x • c x := by simp_rw [smul_eq_mul, mul_comm]
  exact h2

/-- A real smooth compactly supported test function as a complex Schwartz function. -/
noncomputable def realTest (g : V → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (g x : ℂ)) (hgc.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp hg)

/-- The `L²` inverse transform of the transform of an integrable function is the function. -/
theorem ae_eq_fourierInv_of_memLp {c : V → ℂ} (hc : Integrable c) (hG : MemLp (𝓕 c) 2) :
    c =ᵐ[volume] (𝓕⁻ (hG.toLp (𝓕 c)) : Lp ℂ 2 (volume : Measure V)) := by
  set h : Lp ℂ 2 (volume : Measure V) := 𝓕⁻ (hG.toLp (𝓕 c)) with hh
  refine ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((Lp.memLp h).locallyIntegrable (by norm_num)) fun g hg hgc => ?_
  set φ := realTest g hg hgc
  have e1 : ∀ f : V → ℂ, ∫ x, g x • f x = ∫ x, φ x • f x := fun f => by
    congr 1
  rw [e1, e1]
  have e2 : ∫ x, φ x • h x = (h : 𝓢'(V, ℂ)) φ := (Lp.toTemperedDistribution_apply h φ).symm
  rw [e2, hh, ← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  have e3 : ∫ ξ, (𝓕⁻ φ) ξ • (hG.toLp (𝓕 c)) ξ = ∫ ξ, (𝓕⁻ φ) ξ • 𝓕 c ξ :=
    integral_congr_ae (hG.coeFn_toLp.mono fun ξ hξ => by simp only [hξ])
  rw [e3, integral_schwartz_smul_fourier hc, fourier_fourierInv_eq]

/-- The transform of an integrable square integrable function is its `L²` transform. -/
theorem fourier_ae_eq_of_memLp {c : V → ℂ} (hc : Integrable c) (hc2 : MemLp c 2) :
    𝓕 c =ᵐ[volume] (𝓕 (hc2.toLp c) : Lp ℂ 2 (volume : Measure V)) := by
  set k : Lp ℂ 2 (volume : Measure V) := 𝓕 (hc2.toLp c) with hk
  have hGc : Continuous (𝓕 c) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hc
  refine ae_eq_of_integral_contDiff_smul_eq hGc.locallyIntegrable
    ((Lp.memLp k).locallyIntegrable (by norm_num)) fun g hg hgc => ?_
  set φ := realTest g hg hgc
  have e1 : ∀ f : V → ℂ, ∫ x, g x • f x = ∫ x, φ x • f x := fun f => by
    congr 1
  rw [e1, e1]
  have e2 : ∫ x, φ x • k x = (k : 𝓢'(V, ℂ)) φ := (Lp.toTemperedDistribution_apply k φ).symm
  have e3 : ∫ x, (𝓕 φ) x • (hc2.toLp c) x = ∫ x, (𝓕 φ) x • c x :=
    integral_congr_ae (hc2.coeFn_toLp.mono fun ξ hξ => by simp only [hξ])
  rw [e2, hk, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply, e3, integral_schwartz_smul_fourier hc]

theorem eLpNorm_lp_fourierInv (f : Lp ℂ 2 (volume : Measure V)) :
    eLpNorm (𝓕⁻ f : Lp ℂ 2 (volume : Measure V)) 2 volume = eLpNorm f 2 volume := by
  rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (𝓕⁻ f)),
    ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f), ← Lp.norm_def, ← Lp.norm_def]
  congr 1
  exact (Lp.fourierTransformₗᵢ V ℂ).symm.norm_map f

/-- **Plancherel for integrable functions**, in `[0, ∞]`. -/
theorem eLpNorm_fourier_eq_of_integrable {c : V → ℂ} (hc : Integrable c) :
    eLpNorm (𝓕 c) 2 volume = eLpNorm c 2 volume := by
  by_cases hG : MemLp (𝓕 c) 2
  · rw [eLpNorm_congr_ae (ae_eq_fourierInv_of_memLp hc hG), eLpNorm_lp_fourierInv,
      eLpNorm_congr_ae hG.coeFn_toLp]
  · have hc2 : ¬ MemLp c 2 := fun hc2 =>
      hG ((Lp.memLp (𝓕 (hc2.toLp c))).ae_eq (fourier_ae_eq_of_memLp hc hc2).symm)
    rw [not_lt_top_iff.1 (memLp_iff.not.1 hG), not_lt_top_iff.1 (memLp_iff.not.1 hc2)]

end Core

/-- The exponential transform `∫ e^{iθ·z} c(θ) dθ`. -/
noncomputable def expTransform (c : Vec 2 → ℂ) (z : Vec 2) : ℂ :=
  ∫ θ, Complex.exp (↑(vecDot θ z) * Complex.I) * c θ

theorem fourier_rescaled (c : Vec 2 → ℂ) (ξ : HilbertTwo) :
    𝓕 (fun x : HilbertTwo => c (WithLp.ofLp ((-(2 * Real.pi)) • x))) ξ =
      (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • expTransform c (WithLp.ofLp ξ) := by
  rw [Real.fourier_eq']
  set F : HilbertTwo → ℂ := fun y => Complex.exp (↑(vecDot (WithLp.ofLp y) (WithLp.ofLp ξ)) *
    Complex.I) * c (WithLp.ofLp y) with hF
  have h1 : ∀ x : HilbertTwo, Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I) •
      c (WithLp.ofLp ((-(2 * Real.pi)) • x)) = F ((-(2 * Real.pi)) • x) := by
    intro x
    have hi : vecDot (WithLp.ofLp ((-(2 * Real.pi)) • x)) (WithLp.ofLp ξ) =
        -2 * Real.pi * ⟪x, ξ⟫ := by
      simp only [vecDot, PiLp.inner_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [hF, hi, smul_eq_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), Measure.integral_comp_smul volume F]
  have ht := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
    (fun θ : Vec 2 => Complex.exp (↑(vecDot θ (WithLp.ofLp ξ)) * Complex.I) * c θ)
  have hdim : Module.finrank ℝ HilbertTwo = 2 := by simp [HilbertTwo]
  rw [hdim]
  have hscale : |((-(2 * Real.pi)) ^ 2)⁻¹| = ((2 * Real.pi) ^ 2)⁻¹ := by
    rw [neg_sq, abs_of_nonneg (by positivity)]
  rw [hscale]
  unfold expTransform
  exact congrArg _ ht

/-- Scaling the variable of a function on `Vec 2` scales its `L²` norm. -/
theorem eLpNorm_comp_smul_two {c : Vec 2 → ℂ} (hc : AEStronglyMeasurable c volume) {R : ℝ}
    (hR : R ≠ 0) :
    eLpNorm (fun θ => c (R • θ)) 2 volume =
      ENNReal.ofReal |(R ^ 2)⁻¹| ^ (1 / 2 : ℝ) * eLpNorm c 2 volume := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Vec 2)) hR
  have hdim : Module.finrank ℝ (Vec 2) = 2 := by simp
  rw [hdim] at hmap
  have hm : AEMeasurable (fun θ : Vec 2 => R • θ) volume := (measurable_const_smul R).aemeasurable
  have hcm : AEStronglyMeasurable c (Measure.map (fun θ : Vec 2 => R • θ) volume) := by
    rw [hmap]
    exact hc.smul_measure _
  have h := eLpNorm_map_measure (p := 2) hcm hm
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num) c _ hc] at h
  rw [← Function.comp_def, ← h]
  norm_num

theorem expTransform_eq (c : Vec 2 → ℂ) (z : Vec 2) :
    expTransform c z = (((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
      𝓕 (fun x : HilbertTwo => c (WithLp.ofLp ((-(2 * Real.pi)) • x))) (WithLp.toLp 2 z) := by
  rw [fourier_rescaled, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

/-- The exponential transform of an integrable function is continuous. -/
theorem expTransform_continuous {c : Vec 2 → ℂ} (hc : Integrable c) :
    Continuous (expTransform c) := by
  have hpres := PiLp.volume_preserving_ofLp (Fin 2)
  have hc' : Integrable (fun x : HilbertTwo => c (WithLp.ofLp x)) :=
    (hpres.integrable_comp_emb coordinateHilbertEquiv.toHomeomorph.measurableEmbedding).2 hc
  have hCi : Integrable (fun x : HilbertTwo => c (WithLp.ofLp ((-(2 * Real.pi)) • x))) :=
    hc'.comp_smul (neg_ne_zero.2 (by positivity))
  have hFc : Continuous (𝓕 fun x : HilbertTwo => c (WithLp.ofLp ((-(2 * Real.pi)) • x))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hCi
  rw [funext (expTransform_eq c)]
  exact continuous_const.mul (hFc.comp (PiLp.continuous_toLp 2 _))

/-- **Plancherel for the exponential transform** on `Vec 2`. -/
theorem eLpNorm_expTransform {c : Vec 2 → ℂ} (hc : Integrable c) :
    eLpNorm (expTransform c) 2 volume = ENNReal.ofReal (2 * Real.pi) * eLpNorm c 2 volume := by
  set R : ℝ := -(2 * Real.pi) with hR
  have hR0 : R ≠ 0 := by rw [hR]; exact neg_ne_zero.2 (by positivity)
  set C : HilbertTwo → ℂ := fun x => c (WithLp.ofLp (R • x)) with hC
  have hpres := PiLp.volume_preserving_ofLp (Fin 2)
  have hc' : Integrable (fun x : HilbertTwo => c (WithLp.ofLp x)) :=
    (hpres.integrable_comp_emb coordinateHilbertEquiv.toHomeomorph.measurableEmbedding).2 hc
  have hCi : Integrable C := hc'.comp_smul hR0
  have hEc := expTransform_continuous hc
  -- transport to the Hilbert coordinates
  have e1 : eLpNorm (expTransform c) 2 volume =
      eLpNorm (fun ξ : HilbertTwo => (((2 * Real.pi) ^ 2 : ℝ) : ℂ) * 𝓕 C ξ) 2 volume := by
    rw [← eLpNorm_comp_measurePreserving hEc.aestronglyMeasurable hpres]
    congr 1
    funext ξ
    simp only [Function.comp_apply, expTransform_eq]
    rfl
  have hcR : AEStronglyMeasurable (fun θ : Vec 2 => c (R • θ)) volume :=
    hc.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hR0)
  have e2 : eLpNorm C 2 volume = eLpNorm (fun θ : Vec 2 => c (R • θ)) 2 volume := by
    rw [← eLpNorm_comp_measurePreserving hcR hpres]
    rfl
  have e3 : (fun ξ : HilbertTwo => (((2 * Real.pi) ^ 2 : ℝ) : ℂ) * 𝓕 C ξ) =
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) • 𝓕 C := rfl
  have hn : ‖(((2 * Real.pi) ^ 2 : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs : ENNReal.ofReal |(R ^ 2)⁻¹| ^ (1 / 2 : ℝ) = ENNReal.ofReal (2 * Real.pi)⁻¹ := by
    have h2 : |(R ^ 2)⁻¹| = ((2 * Real.pi)⁻¹) ^ 2 := by
      rw [hR, neg_sq, inv_pow, abs_of_nonneg (by positivity)]
    rw [h2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (by positivity)]
  rw [e1, e3, eLpNorm_const_smul, eLpNorm_fourier_eq_of_integrable hCi, e2,
    eLpNorm_comp_smul_two hc.aestronglyMeasurable hR0, hn, hs, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Facade: the symmetry of the iterated derivatives of `C^n` functions moved to
`AVRegularity.Analysis.Convolution` (namespace `AVRegularity.Analysis`), shared by the cycle-words
and cycle-comparison developments. -/
end

section
@[expose] public noncomputable section
open Set
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp fast decay: the combinatorial loop over the windows

The induction over the windows crossed between `s` and `t`, with no analysis in it. The
analytic content enters through an abstract predicate `Reach τ ε`: "the curve at `τ` has an `H^j`
representative of norm `≤ ε e^{-π²(t-τ)/8} ‖w₀‖`". Three steps are used: a quiet stretch
(`quiet`: factor `3 e^{-3π²(τ-σ)/8}` relative to the rate `π²/8`), a crude crossing (`crude`:
factor `Bx`, which carries `P_e^Q`), and, at the start only, the window lemma.

The invariant is `ε ≤ 1/(3 Bx)`: it is restored after every crossing by the quiet buffer to the
left of the window. A quiet stretch at the start of a crossing keeps it (`3 a ≤ 1`). -/

/-- The step data of the loop. -/
structure SharpLoopData (reg : AVRegularity.BlockRegions) (s t : ℝ) (Reach : ℝ → ℝ → Prop)
    (Bx : ℝ) : Prop where
  mono : ∀ τ ε ε', ε ≤ ε' → Reach τ ε → Reach τ ε'
  quiet : ∀ σ τ ε, s ≤ σ → σ ≤ τ → τ ≤ t → Icc σ τ ⊆ reg.quiet → Reach τ ε →
    Reach σ (3 * ε * Real.exp (-(3 * Real.pi ^ 2 / 8) * (τ - σ)))
  crude : ∀ σ τ ε, s ≤ σ → σ ≤ τ → τ ≤ t → Reach τ ε → Reach σ (Bx * ε)
  cover : ∀ x ∈ Icc s t, x ∈ reg.quiet ∨ ∃ p, x ∈ Icc (reg.lo p) (reg.hi p)
  bufq : ∀ p, Ico (reg.lo p - reg.buffer) (reg.lo p) ⊆ reg.quiet
  bufqR : ∀ p, Ioc (reg.hi p) (reg.hi p + reg.buffer) ⊆ reg.quiet

/-- The nondegenerate windows starting at or before `τ`. -/
def sharpS (reg : AVRegularity.BlockRegions) (τ : ℝ) : Finset (Fin reg.P) :=
  Finset.univ.filter (fun p : Fin reg.P => reg.lo p ≤ τ ∧ reg.lo p ≤ reg.hi p)

@[simp] theorem mem_sharpS {reg : AVRegularity.BlockRegions} {τ : ℝ} {p : Fin reg.P} :
    p ∈ sharpS reg τ ↔ reg.lo p ≤ τ ∧ reg.lo p ≤ reg.hi p := by simp [sharpS]

variable {reg : AVRegularity.BlockRegions} {s t : ℝ} {Reach : ℝ → ℝ → Prop} {Bx : ℝ}

theorem sharpLoop_exp_le_one {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(3 * Real.pi ^ 2 / 8) * (x)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

/-- Exit through a quiet stretch down to `s`. -/
theorem sharpLoop_exit_quiet (hd : SharpLoopData reg s t Reach Bx) {τ ε : ℝ} (hsτ : s ≤ τ)
    (hτt : τ ≤ t) (hq : Icc s τ ⊆ reg.quiet) (hR : Reach τ ε) (hε0 : 0 ≤ ε) :
    Reach s (3 * ε) := by
  refine hd.mono _ _ _ ?_ (hd.quiet s τ ε le_rfl hsτ hτt hq hR)
  have := sharpLoop_exp_le_one (x := τ - s) (by linarith)
  nlinarith

/-- No window starts at or before `τ`: everything in `[s, τ]` is quiet. -/
theorem sharpLoop_noWindow (hd : SharpLoopData reg s t Reach Bx) {τ ε : ℝ} (hsτ : s ≤ τ)
    (hτt : τ ≤ t) (hempty : ∀ p, ¬ (reg.lo p ≤ τ ∧ reg.lo p ≤ reg.hi p)) (hR : Reach τ ε) (hε0 : 0 ≤ ε)
    (hε : 3 * ε ≤ 1) : Reach s 1 := by
  have hq : Icc s τ ⊆ reg.quiet := by
    intro x hx
    rcases hd.cover x ⟨hx.1, le_trans hx.2 hτt⟩ with h | ⟨p, hp⟩
    · exact h
    · exact absurd ⟨le_trans hp.1 hx.2, le_trans hp.1 hp.2⟩ (hempty p)
  exact hd.mono _ _ _ hε (sharpLoop_exit_quiet hd hsτ hτt hq hR hε0)

/-- The decay of one buffer: with `a` bounding `e^{-3π² x/8}` for `x ≥ D/4`. -/
theorem sharpLoop_a_pos {D a : ℝ}
    (ha : ∀ x, D / 4 ≤ x → Real.exp (-(3 * Real.pi ^ 2 / 8) * x) ≤ a) : 0 < a :=
  lt_of_lt_of_le (Real.exp_pos _) (ha (D / 4) le_rfl)

/-- The loop. Every state with `ε ≤ 1/(3 Bx)` reaches `s` with the constant `1`. -/
theorem sharpLoop (hd : SharpLoopData reg s t Reach Bx) (hD : 0 < reg.buffer) (hBx : 1 ≤ Bx)
    {a : ℝ} (ha : ∀ x, reg.buffer / 4 ≤ x → Real.exp (-(3 * Real.pi ^ 2 / 8) * x) ≤ a)
    (hnum : 3 * Bx * a ≤ 1) :
    ∀ n : ℕ, ∀ τ ε : ℝ, s ≤ τ → τ ≤ t →
      (sharpS reg (τ)).card ≤ n →
      Reach τ ε → 0 ≤ ε → ε ≤ 1 / (3 * Bx) → Reach s 1 := by
  have ha0 : 0 < a := sharpLoop_a_pos ha
  have hBx0 : 0 < Bx := by linarith
  have h3a : 3 * a ≤ 1 := by nlinarith
  have hε13 : ∀ ε : ℝ, ε ≤ 1 / (3 * Bx) → 3 * ε ≤ 1 / Bx := by
    intro ε h
    calc 3 * ε ≤ 3 * (1 / (3 * Bx)) := by linarith
      _ = 1 / Bx := by field_simp
  have hinv : 1 / Bx ≤ 1 := by
    rw [div_le_one hBx0]; exact hBx
  have h3ε : ∀ ε : ℝ, ε ≤ 1 / (3 * Bx) → 3 * ε ≤ 1 := fun ε h => le_trans (hε13 ε h) hinv
  have hBε : ∀ ε : ℝ, ε ≤ 1 / (3 * Bx) → 3 * (Bx * ε) ≤ 1 := by
    intro ε h
    have h1 : Bx * ε ≤ Bx * (1 / (3 * Bx)) := mul_le_mul_of_nonneg_left h hBx0.le
    have h2 : Bx * (1 / (3 * Bx)) = 1 / 3 := by field_simp
    linarith
  have hε0' : (0 : ℝ) < 1 / (3 * Bx) := by positivity
  intro n
  induction n with
  | zero =>
    intro τ ε hsτ hτt hcard hR hε0 hε
    have hempty : ∀ p, ¬ (reg.lo p ≤ τ ∧ reg.lo p ≤ reg.hi p) := by
      intro p hp
      have hmem : p ∈ sharpS reg (τ) := mem_sharpS.mpr hp
      have := Finset.card_pos.mpr ⟨p, hmem⟩
      omega
    exact sharpLoop_noWindow hd hsτ hτt hempty hR hε0 (h3ε ε hε)
  | succ n ih =>
    -- the crossing step
    have stepA : ∀ (τ ε : ℝ) (q : Fin reg.P), s ≤ τ → τ ≤ t →
        (sharpS reg (τ)).card ≤ n + 1 →
        reg.lo q ≤ τ → reg.lo q ≤ reg.hi q → Reach τ ε → 0 ≤ ε → ε ≤ 1 / (3 * Bx) → Reach s 1 := by
      intro τ ε q hsτ hτt hcard hlq hlhq hR hε0 hε
      have hσ1τ : reg.lo q - reg.buffer / 4 ≤ τ := by linarith
      by_cases h1 : reg.lo q - reg.buffer / 4 ≤ s
      · have := hd.crude s τ ε le_rfl hsτ hτt hR
        exact hd.mono _ _ _ (by linarith [hBε ε hε]) this
      · push Not at h1
        have hc := hd.crude (reg.lo q - reg.buffer / 4) τ ε (by linarith) hσ1τ hτt hR
        by_cases h2 : reg.lo q - reg.buffer ≤ s
        · have hsub : Icc s (reg.lo q - reg.buffer / 4) ⊆ reg.quiet := by
            intro x hx
            exact hd.bufq q ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have := sharpLoop_exit_quiet hd (τ := reg.lo q - reg.buffer / 4) (ε := Bx * ε)
            (by linarith) (by linarith) hsub hc (by positivity)
          exact hd.mono _ _ _ (hBε ε hε) this
        · push Not at h2
          have hsub : Icc (reg.lo q - reg.buffer) (reg.lo q - reg.buffer / 4) ⊆ reg.quiet := by
            intro x hx
            exact hd.bufq q ⟨hx.1, by linarith [hx.2]⟩
          have hq := hd.quiet (reg.lo q - reg.buffer) (reg.lo q - reg.buffer / 4) (Bx * ε)
            (by linarith) (by linarith) (by linarith) hsub hc
          have hex : Real.exp (-(3 * Real.pi ^ 2 / 8) *
              (reg.lo q - reg.buffer / 4 - (reg.lo q - reg.buffer))) ≤ a :=
            ha _ (by linarith)
          have hex0 := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) *
              (reg.lo q - reg.buffer / 4 - (reg.lo q - reg.buffer)))
          have hsmall : 3 * (Bx * ε) * Real.exp (-(3 * Real.pi ^ 2 / 8) *
              (reg.lo q - reg.buffer / 4 - (reg.lo q - reg.buffer))) ≤ 1 / (3 * Bx) := by
            have hb := hBε ε hε
            have hpos : 0 ≤ 3 * (Bx * ε) := by positivity
            calc 3 * (Bx * ε) * Real.exp (-(3 * Real.pi ^ 2 / 8) *
                  (reg.lo q - reg.buffer / 4 - (reg.lo q - reg.buffer)))
                ≤ 1 * a := mul_le_mul hb hex hex0.le (by norm_num)
              _ ≤ 1 / (3 * Bx) := by
                rw [one_mul, le_div_iff₀ (by positivity)]
                nlinarith
          have hsub2 : sharpS reg (reg.lo q - reg.buffer)
              ⊂ sharpS reg (τ) := by
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨q, mem_sharpS.mpr ⟨hlq, hlhq⟩, fun h => by
                have := (mem_sharpS.mp h).1
                linarith⟩
            · intro p hp
              rw [mem_sharpS] at hp ⊢
              exact ⟨by linarith [hp.1], hp.2⟩
          have hcard2 := Finset.card_lt_card hsub2
          exact ih (reg.lo q - reg.buffer) _ h2.le (by linarith) (by omega) hq (by positivity)
            hsmall
    intro τ ε hsτ hτt hcard hR hε0 hε
    by_cases hne : ∃ p, reg.lo p ≤ τ ∧ reg.lo p ≤ reg.hi p
    · obtain ⟨p, hp⟩ := hne
      have hmem : (sharpS reg (τ)).Nonempty := ⟨p, mem_sharpS.mpr hp⟩
      obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image _ (fun p : Fin reg.P => reg.hi p) hmem
      have hlq : reg.lo q ≤ τ := (mem_sharpS.mp hq).1
      have hlhq : reg.lo q ≤ reg.hi q := (mem_sharpS.mp hq).2
      by_cases hA : τ ≤ reg.hi q + reg.buffer / 2
      · exact stepA τ ε q hsτ hτt hcard hlq hlhq hR hε0 hε
      · push Not at hA
        -- a quiet stretch down to the window `q` (cost `3 a ≤ 1`)
        have hqu : ∀ σ, reg.hi q + reg.buffer / 4 ≤ σ → s ≤ σ → σ ≤ τ → Icc σ τ ⊆ reg.quiet := by
          intro σ hσ hsσ hστ x hx
          rcases hd.cover x ⟨le_trans hsσ hx.1, le_trans hx.2 hτt⟩ with h | ⟨p', hp'⟩
          · exact h
          · exfalso
            have hp'mem : p' ∈ sharpS reg (τ) :=
              mem_sharpS.mpr ⟨by linarith [hp'.1, hx.2], le_trans hp'.1 hp'.2⟩
            have := hqmax p' hp'mem
            linarith [hp'.2, hx.1]
        by_cases hs1 : reg.hi q + reg.buffer / 4 ≤ s
        · have := sharpLoop_exit_quiet hd hsτ hτt (hqu s hs1 le_rfl hsτ) hR hε0
          exact hd.mono _ _ _ (h3ε ε hε) this
        · push Not at hs1
          have hσ : s ≤ reg.hi q + reg.buffer / 4 := hs1.le
          have hστ : reg.hi q + reg.buffer / 4 ≤ τ := by linarith
          have hqσ := hd.quiet (reg.hi q + reg.buffer / 4) τ ε hσ hστ hτt
            (hqu _ le_rfl hσ hστ) hR
          have hex : Real.exp (-(3 * Real.pi ^ 2 / 8) * (τ - (reg.hi q + reg.buffer / 4))) ≤ a :=
            ha _ (by linarith)
          have hex0 := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) * (τ - (reg.hi q + reg.buffer / 4)))
          have hsmall : 3 * ε * Real.exp (-(3 * Real.pi ^ 2 / 8) *
              (τ - (reg.hi q + reg.buffer / 4))) ≤ 1 / (3 * Bx) := by
            calc 3 * ε * Real.exp (-(3 * Real.pi ^ 2 / 8) * (τ - (reg.hi q + reg.buffer / 4)))
                ≤ 3 * ε * a := mul_le_mul_of_nonneg_left hex (by positivity)
              _ ≤ ε * 1 := by nlinarith
              _ ≤ 1 / (3 * Bx) := by linarith
          have hlqσ : reg.lo q ≤ reg.hi q + reg.buffer / 4 := by
            linarith [hlhq]
          have hcard2 : (sharpS reg (reg.hi q + reg.buffer / 4)).card ≤ n + 1 := by
            refine le_trans (Finset.card_le_card ?_) hcard
            intro p hp
            rw [mem_sharpS] at hp ⊢
            exact ⟨by linarith [hp.1], hp.2⟩
          exact stepA _ _ q hσ (by linarith) hcard2 hlqσ hlhq hqσ (by positivity) hsmall
    · push Not at hne
      exact sharpLoop_noWindow hd hsτ hτt (fun p h => absurd h.2 (not_le.mpr (hne p h.1))) hR hε0 (h3ε ε hε)

/-- The start: from `Reach t 1`, the window lemma for the least window containing `t` (if any)
and the loop reach `s` with the constant `3 C₁`. -/
theorem sharpStart (hd : SharpLoopData reg s t Reach Bx) (hD : 0 < reg.buffer) (hBx : 1 ≤ Bx)
    {a C₁ : ℝ} (ha : ∀ x, reg.buffer / 4 ≤ x → Real.exp (-(3 * Real.pi ^ 2 / 8) * x) ≤ a)
    (hC₁ : 1 ≤ C₁) (hnum : 9 * C₁ * Bx * a ≤ 1) (hst : s ≤ t) (h0 : Reach t 1)
    (hW : ∀ p : Fin reg.P, reg.lo p ≤ t → t ≤ reg.hi p + reg.buffer / 2 → reg.lo p ≤ reg.hi p →
      (∀ p' : Fin reg.P, p' < p → reg.lo p' ≤ reg.hi p' →
        ¬ (reg.lo p' ≤ t ∧ t ≤ reg.hi p' + reg.buffer / 2)) →
      ∀ σ, s ≤ σ → reg.lo p - reg.buffer ≤ σ → σ ≤ reg.hi p → σ ≤ t → Reach σ C₁) :
    Reach s (3 * C₁) := by
  have ha0 : 0 < a := sharpLoop_a_pos ha
  have hBx0 : 0 < Bx := by linarith
  have hnum' : 3 * Bx * a ≤ 1 := by nlinarith [mul_pos hBx0 ha0]
  have hloop := sharpLoop hd hD hBx ha hnum'
  have h3C : (3 : ℝ) ≤ 3 * C₁ := by linarith
  have hsmallC : 3 * C₁ * a ≤ 1 / (3 * Bx) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsmall1 : 3 * a ≤ 1 / (3 * Bx) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hBx0 ha0]
  by_cases hex : ∃ p : Fin reg.P, reg.lo p ≤ t ∧ t ≤ reg.hi p + reg.buffer / 2 ∧ reg.lo p ≤ reg.hi p
  · -- t is in an extended window
    have hfne : (Finset.univ.filter
        (fun p : Fin reg.P => reg.lo p ≤ t ∧ t ≤ reg.hi p + reg.buffer / 2 ∧ reg.lo p ≤ reg.hi p)).Nonempty := by
      obtain ⟨p, hp⟩ := hex
      exact ⟨p, by simp [hp]⟩
    set p₀ := (Finset.univ.filter
        (fun p : Fin reg.P => reg.lo p ≤ t ∧ t ≤ reg.hi p + reg.buffer / 2 ∧ reg.lo p ≤ reg.hi p)).min' hfne with hp₀
    have hp₀mem := Finset.min'_mem _ hfne
    rw [← hp₀] at hp₀mem
    have hp₀prop : reg.lo p₀ ≤ t ∧ t ≤ reg.hi p₀ + reg.buffer / 2 ∧ reg.lo p₀ ≤ reg.hi p₀ := by
      simpa using hp₀mem
    have hmin : ∀ p' : Fin reg.P, p' < p₀ → reg.lo p' ≤ reg.hi p' →
        ¬ (reg.lo p' ≤ t ∧ t ≤ reg.hi p' + reg.buffer / 2) := by
      intro p' hlt hlh' hp'
      have hmem' : p' ∈ (Finset.univ.filter
          (fun p : Fin reg.P => reg.lo p ≤ t ∧ t ≤ reg.hi p + reg.buffer / 2 ∧
            reg.lo p ≤ reg.hi p)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp'.1, hp'.2, hlh'⟩
      have := Finset.min'_le _ p' hmem'
      rw [← hp₀] at this
      exact absurd hlt (not_lt.mpr this)
    have hWp := hW p₀ hp₀prop.1 hp₀prop.2.1 hp₀prop.2.2 hmin
    have hlh := hp₀prop.2.2
    by_cases hsh : reg.hi p₀ < s
    · have hq : Icc s t ⊆ reg.quiet := by
        intro x hx
        exact hd.bufqR p₀ ⟨by linarith [hx.1], by linarith [hx.2, hp₀prop.2.1]⟩
      have := sharpLoop_exit_quiet hd hst le_rfl hq h0 (by norm_num)
      exact hd.mono _ _ _ (by linarith) this
    · push Not at hsh
      by_cases hlo : reg.lo p₀ - reg.buffer ≤ s
      · exact hd.mono _ _ _ (by linarith) (hWp s le_rfl hlo hsh hst)
      · push Not at hlo
        have hW1 := hWp (reg.lo p₀ - reg.buffer / 4) (by linarith) (by linarith) (by linarith)
          (by linarith [hp₀prop.1])
        have hsub : Icc (reg.lo p₀ - reg.buffer) (reg.lo p₀ - reg.buffer / 4) ⊆ reg.quiet := by
          intro x hx
          exact hd.bufq p₀ ⟨hx.1, by linarith [hx.2]⟩
        have hq := hd.quiet (reg.lo p₀ - reg.buffer) (reg.lo p₀ - reg.buffer / 4) C₁
          (by linarith) (by linarith) (by linarith [hp₀prop.1]) hsub hW1
        have hex' : Real.exp (-(3 * Real.pi ^ 2 / 8) *
            (reg.lo p₀ - reg.buffer / 4 - (reg.lo p₀ - reg.buffer))) ≤ a :=
          ha _ (by linarith)
        have hex0 := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) *
            (reg.lo p₀ - reg.buffer / 4 - (reg.lo p₀ - reg.buffer)))
        have hsm : 3 * C₁ * Real.exp (-(3 * Real.pi ^ 2 / 8) *
            (reg.lo p₀ - reg.buffer / 4 - (reg.lo p₀ - reg.buffer))) ≤ 1 / (3 * Bx) :=
          le_trans (mul_le_mul_of_nonneg_left hex' (by positivity)) hsmallC
        have := hloop _ (reg.lo p₀ - reg.buffer) _ hlo.le (by linarith [hp₀prop.1]) le_rfl hq
          (by positivity) hsm
        exact hd.mono _ _ _ (by linarith) this
  · push Not at hex
    by_cases hne : ∃ p : Fin reg.P, reg.lo p ≤ t ∧ reg.lo p ≤ reg.hi p
    · obtain ⟨p, hp⟩ := hne
      have hmem : (sharpS reg (t)).Nonempty := ⟨p, mem_sharpS.mpr hp⟩
      obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image _ (fun p : Fin reg.P => reg.hi p) hmem
      have hlq : reg.lo q ≤ t := (mem_sharpS.mp hq).1
      have hlhq : reg.lo q ≤ reg.hi q := (mem_sharpS.mp hq).2
      have hA : reg.hi q + reg.buffer / 2 < t := by
        by_contra hc
        exact absurd hlhq (not_le.mpr (hex q hlq (not_lt.mp hc)))
      have hqu : ∀ σ, reg.hi q + reg.buffer / 4 ≤ σ → s ≤ σ → σ ≤ t → Icc σ t ⊆ reg.quiet := by
        intro σ hσ hsσ hστ x hx
        rcases hd.cover x ⟨le_trans hsσ hx.1, hx.2⟩ with h | ⟨p', hp'⟩
        · exact h
        · exfalso
          have hp'mem : p' ∈ sharpS reg (t) :=
            mem_sharpS.mpr ⟨by linarith [hp'.1, hx.2], le_trans hp'.1 hp'.2⟩
          have := hqmax p' hp'mem
          linarith [hp'.2, hx.1]
      by_cases hs1 : reg.hi q + reg.buffer / 4 ≤ s
      · have := sharpLoop_exit_quiet hd hst le_rfl (hqu s hs1 le_rfl hst) h0 (by norm_num)
        exact hd.mono _ _ _ (by linarith) this
      · push Not at hs1
        have hσ : s ≤ reg.hi q + reg.buffer / 4 := hs1.le
        have hσt : reg.hi q + reg.buffer / 4 ≤ t := by linarith
        have hqσ := hd.quiet (reg.hi q + reg.buffer / 4) t 1 hσ hσt le_rfl
          (hqu _ le_rfl hσ hσt) h0
        have hex' : Real.exp (-(3 * Real.pi ^ 2 / 8) * (t - (reg.hi q + reg.buffer / 4))) ≤ a :=
          ha _ (by linarith)
        have hex0 := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) * (t - (reg.hi q + reg.buffer / 4)))
        have hsm : 3 * 1 * Real.exp (-(3 * Real.pi ^ 2 / 8) *
            (t - (reg.hi q + reg.buffer / 4))) ≤ 1 / (3 * Bx) :=
          le_trans (mul_le_mul_of_nonneg_left hex' (by norm_num)) (by linarith [hsmall1])
        have := hloop _ (reg.hi q + reg.buffer / 4) _ hσ hσt le_rfl hqσ (by positivity) hsm
        exact hd.mono _ _ _ (by linarith) this
    · push Not at hne
      have hq : Icc s t ⊆ reg.quiet := by
        intro x hx
        rcases hd.cover x hx with h | ⟨p, hp⟩
        · exact h
        · exact absurd (le_trans hp.1 hp.2) (not_le.mpr (hne p (le_trans hp.1 hx.2)))
      have := sharpLoop_exit_quiet hd hst le_rfl hq h0 (by norm_num)
      exact hd.mono _ _ _ (by linarith) this

end AVRegularity.CycleWords.Assembly
end
end
