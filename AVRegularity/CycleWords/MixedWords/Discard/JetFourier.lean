-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.SharpDecayLoop
public import AVRegularity.CycleWords.MixedWords.Discard.BandRep
import AVRegularity.CycleWords.MixedWords.Discard.WeakContFluxTerm
import Mathlib.Analysis.Fourier.Convolution

section
/-! # the transform of an integrable `L²` function, and of the cutoff kernel

* `fourierL2_of_integrable`: for a real `g ∈ L¹ ∩ L²` on the plane, the `L²` transform is the
  integral, `fourierL2 g (x) = planeTransform g (2π x)` (`fourier_ae_eq_of_memLp`).
* `Hil_cutoffKernel_fourier`: the transform of the cutoff kernel of an even multiplier `μ` is `μ`
  (Fourier inversion on Schwartz functions; the kernel is real because `μ` is even).
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate

namespace AVRegularity.CycleWords.Discard

/-- The complexification of a real function on the plane, in the Hilbert coordinates. -/
def hilbertComplexify (g : Vec 2 → ℝ) : HilbertTwo → ℂ := fun x => (g (WithLp.ofLp x) : ℂ)

theorem Hil_integrable {g : Vec 2 → ℝ} (hg : Integrable g) : Integrable (hilbertComplexify g) :=
  ((PiLp.volume_preserving_ofLp (Fin 2)).integrable_comp_emb
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding).2 hg.ofReal

theorem Hil_memLp {g : Vec 2 → ℝ} (hg : MemLp g 2 volume) : MemLp (hilbertComplexify g) 2 volume :=
  hg.ofReal.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 2))

/-- The Mathlib transform in the Hilbert coordinates is the radian transform at `2π ξ`. -/
theorem Hil_fourier (g : Vec 2 → ℝ) (ξ : HilbertTwo) :
    𝓕 (hilbertComplexify g) ξ = planeTransform g ((2 * Real.pi) • WithLp.ofLp ξ) := by
  rw [Real.fourier_eq']
  have ht := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
    (fun y : Vec 2 => Complex.exp (-(Complex.I *
      (vecDot ((2 * Real.pi) • WithLp.ofLp ξ) y : ℂ))) * (g y : ℂ))
  unfold planeTransform
  rw [← ht]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  have hi : vecDot ((2 * Real.pi) • WithLp.ofLp ξ) (WithLp.ofLp x) =
      2 * Real.pi * inner ℝ x ξ := by
    simp only [vecDot, PiLp.inner_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RCLike.inner_apply, conj_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  change _ = Complex.exp (-(Complex.I *
      (vecDot ((2 * Real.pi) • WithLp.ofLp ξ) (WithLp.ofLp x) : ℂ))) * (g (WithLp.ofLp x) : ℂ)
  rw [hi]
  simp only [hilbertComplexify, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The class of a real `L²` function, complexified, in the Hilbert coordinates. -/
theorem coordinate_ofReal_toLp {g : Vec 2 → ℝ} (hg2 : MemLp g 2 volume) :
    coordinateL2Equiv (ofRealL2 volume (hg2.toLp g)) = (Hil_memLp hg2).toLp (hilbertComplexify g) := by
  apply Lp.ext
  have hmp := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving
  filter_upwards [coordinateL2Equiv_ae (ofRealL2 volume (hg2.toLp g)),
    hmp.ae (ofRealL2_ae volume (hg2.toLp g)), hmp.ae hg2.coeFn_toLp,
    (Hil_memLp hg2).coeFn_toLp] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  rfl

/-- An a.e. identity for the transform in the Hilbert coordinates, read on `Vec 2`. -/
theorem fourierL2_ae_of_coordinate (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (F : HilbertTwo → ℂ)
    (h : (𝓕 (coordinateL2Equiv f) : Lp ℂ 2 (volume : Measure HilbertTwo)) =ᵐ[volume] F) :
    fourierL2 f =ᵐ[volume] fun x => F (WithLp.toLp 2 x) := by
  rw [← coordinate_fourierL2] at h
  have he : ∀ᵐ ξ : HilbertTwo ∂volume, fourierL2 f (WithLp.ofLp ξ) = F ξ := by
    filter_upwards [h, coordinateL2Equiv_ae (fourierL2 f)] with ξ h1 h2
    rw [← h2, h1]
  exact (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.ae he

/-- **The `L²` transform of an integrable function is the integral.** -/
theorem fourierL2_of_integrable {g : Vec 2 → ℝ} (hg : Integrable g)
    (hg2 : MemLp g 2 volume) :
    fourierL2 (ofRealL2 volume (hg2.toLp g)) =ᵐ[volume]
      fun x => planeTransform g ((2 * Real.pi) • x) := by
  have h1 := fourier_ae_eq_of_memLp (Hil_integrable hg) (Hil_memLp hg2)
  have h2 := fourierL2_ae_of_coordinate (ofRealL2 volume (hg2.toLp g)) (𝓕 (hilbertComplexify g))
    (by rw [coordinate_ofReal_toLp hg2]; exact h1.symm)
  filter_upwards [h2] with x hx
  rw [hx, Hil_fourier]

/-- The complex cutoff kernel of an even multiplier is real. -/
theorem seamCutoffFourier_conj (m : Vec 2 → ℝ) (hev : ∀ θ, m (-θ) = m θ) (x : Vec 2) :
    conj (seamCutoffFourier m x) = seamCutoffFourier m x := by
  have h0 : seamCutoffFourier m x =
      ∫ θ : Vec 2, 𝐞 (-seamFourierPairing θ x) • (m θ : ℂ) := rfl
  rw [h0, ← integral_conj,
    ← integral_neg_eq_self (fun θ : Vec 2 => 𝐞 (-seamFourierPairing θ x) • (m θ : ℂ))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun θ => ?_
  simp only [map_neg, neg_apply, neg_neg, hev, Circle.smul_def,
    Real.fourierChar_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  congr 2
  push_cast
  ring

/-- The real cutoff kernel of an even multiplier is the complex Schwartz kernel. -/
theorem cutoffKernel_ofReal (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hev : ∀ θ, m (-θ) = m θ) (x : Vec 2) :
    (cutoffKernel m x : ℂ) =
      (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) * seamComplexCutoffSchwartz m R hm hs x := by
  rw [seamComplexCutoffSchwartz_eq, cutoffKernel_eq_seamCutoffFourier_re m R hm hs.continuous x]
  have him : (seamCutoffFourier m x).im = 0 :=
    Complex.conj_eq_iff_im.mp (seamCutoffFourier_conj m hev x)
  rw [Complex.ofReal_mul]
  congr 1
  exact Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, him])

/-- **The transform of the cutoff kernel is the multiplier.** -/
theorem Hil_cutoffKernel_fourier (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hev : ∀ θ, m (-θ) = m θ) (ξ : HilbertTwo) :
    𝓕 (hilbertComplexify (cutoffKernel m)) ξ = (m ((2 * Real.pi) • WithLp.ofLp ξ) : ℂ) := by
  set M : 𝓢(HilbertTwo, ℂ) := seamHilbertCutoffSchwartz m R hm hs with hM
  have hk : ∀ z : HilbertTwo, hilbertComplexify (cutoffKernel m) z =
      (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) * (𝓕 M) ((-(2 * Real.pi)⁻¹) • z) := by
    intro z
    rw [hilbertComplexify, cutoffKernel_ofReal m R hm hs hev]
    rfl
  have hinv := congrArg (fun g : 𝓢(HilbertTwo, ℂ) => g ((2 * Real.pi) • ξ))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(HilbertTwo, ℂ)) M)
  change (∫ x : HilbertTwo, 𝐞 (-inner ℝ x (-((2 * Real.pi) • ξ))) • (𝓕 M) x) =
    M ((2 * Real.pi) • ξ) at hinv
  rw [Real.fourier_eq]
  set F : HilbertTwo → ℂ := fun x => 𝐞 (-inner ℝ x (-((2 * Real.pi) • ξ))) • (𝓕 M) x with hF
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∀ z : HilbertTwo, 𝐞 (-inner ℝ z ξ) • hilbertComplexify (cutoffKernel m) z =
      (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) * F ((-(2 * Real.pi)⁻¹) • z) := by
    intro z
    have hph : -inner ℝ ((-(2 * Real.pi)⁻¹) • z) (-((2 * Real.pi) • ξ)) = -inner ℝ z ξ := by
      rw [inner_smul_left, inner_neg_right, inner_smul_right]
      simp only [conj_trivial]
      field_simp
    rw [hk z, hF]
    simp only
    rw [hph]
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
    Measure.integral_comp_smul volume F, hinv]
  have hdim : Module.finrank ℝ HilbertTwo = 2 := by simp [HilbertTwo]
  rw [hdim]
  have hscale : |((-(2 * Real.pi)⁻¹) ^ 2)⁻¹| = (2 * Real.pi) ^ 2 := by
    rw [neg_sq, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg _)]
  rw [hscale]
  have hMv : M ((2 * Real.pi) • ξ) = (m ((2 * Real.pi) • WithLp.ofLp ξ) : ℂ) := rfl
  have hone : (2 * Real.pi)⁻¹ ^ 2 * (2 * Real.pi) ^ 2 = 1 := by
    field_simp
  rw [hMv, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hone, Complex.ofReal_one,
    one_mul]

end AVRegularity.CycleWords.Discard
end
end

section
/-! # Plancherel with moments

`momentPlancherel : MomentPlancherelStatement`. For `γ ≤ β` on the path
`(0,0) → (β.1,0) → (β.1,β.2)` the moment `y^γ v` is in `L²` and its transform is
`i^{|γ|} (D γ)(2π x)` (`MomentFT`): one use of the step lemma `moment_step` per unit of `|γ|`.
The identity is then Plancherel (`fourierL2_norm`) and the dilation by `2π`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

/-- The square of the `L²` seminorm as a lower integral. -/
theorem eLpNorm_two_sq' {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The dilation by `2π` on the plane. -/
theorem lintegral_dilate (F : Vec 2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ((2 * Real.pi) • x) = ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, F ξ := by
  have hr : (2 * Real.pi) ≠ 0 := by positivity
  have hmap := Measure.map_addHaar_smul (volume : Measure (Vec 2)) hr
  have h1 : ∫⁻ x, F ((2 * Real.pi) • x) =
      ∫⁻ ξ, F ξ ∂(Measure.map (fun x : Vec 2 => (2 * Real.pi) • x) volume) :=
    (lintegral_map hF (measurable_const_smul _)).symm
  have hfin : Module.finrank ℝ (Vec 2) = 2 := by simp
  have habs : |((2 * Real.pi) ^ 2)⁻¹| = ((2 * Real.pi) ^ 2)⁻¹ := abs_of_pos (by positivity)
  rw [h1, hmap, lintegral_smul_measure, hfin, habs, smul_eq_mul]

/-- A continuous function with finite square integral, dilated, is in `L²`. -/
theorem memLp_dilate (c : ℂ) (F : Vec 2 → ℂ) (hF : Continuous F)
    (hL : ∫⁻ ξ, ‖F ξ‖ₑ ^ 2 < ∞) :
    MemLp (fun x : Vec 2 => c * F ((2 * Real.pi) • x)) 2 volume := by
  have hc : Continuous (fun x : Vec 2 => F ((2 * Real.pi) • x)) :=
    hF.comp (continuous_const_smul _)
  have h1 : MemLp (fun x : Vec 2 => F ((2 * Real.pi) • x)) 2 volume := by
    rw [memLp_iff]
    have h2 := eLpNorm_two_sq' (μ := (volume : Measure (Vec 2))) _ hc.aestronglyMeasurable
    rw [lintegral_dilate (fun ξ => ‖F ξ‖ₑ ^ 2) (hF.measurable.enorm.pow_const 2)] at h2
    have h3 : eLpNorm (fun x : Vec 2 => F ((2 * Real.pi) • x)) 2 volume ^ 2 < ∞ := by
      rw [h2]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at h3
    simp at h3
  exact h1.const_mul c

/-- The moment `y^γ v` is in `L²` with transform `i^{|γ|} (D γ)(2π x)`. -/
def MomentFT (v : Vec 2 → ℝ) (D : ℕ × ℕ → Vec 2 → ℂ) (γ : ℕ × ℕ) : Prop :=
  ∃ g : Lp ℂ 2 (volume : Measure (Vec 2)),
    (g =ᵐ[volume] fun y => ((momentWeight γ y * v y : ℝ) : ℂ)) ∧
    fourierL2 g =ᵐ[volume] fun x => Complex.I ^ (γ.1 + γ.2) * D γ ((2 * Real.pi) • x)

/-- The base of the induction: the hypothesis `HasFT`. -/
theorem momentFT_zero (v : Vec 2 → ℝ) (Φ : Vec 2 → ℂ) (D : ℕ × ℕ → Vec 2 → ℂ)
    (hv : HasFT v Φ) (hD0 : D (0, 0) = Φ) : MomentFT v D (0, 0) := by
  obtain ⟨hv2, hft⟩ := hv
  refine ⟨ofRealL2 volume (hv2.toLp v), ?_, ?_⟩
  · filter_upwards [ofRealL2_ae volume (hv2.toLp v), hv2.coeFn_toLp] with y h1 h2
    rw [h1, h2]
    simp [momentWeight]
  · filter_upwards [hft] with x hx
    rw [hx, hD0]
    simp

/-- One step of the induction: one more partial derivative of the transform, one more factor
`y_j` of the function. -/
theorem momentFT_step (v : Vec 2 → ℝ) (D : ℕ × ℕ → Vec 2 → ℂ) (γ γ' : ℕ × ℕ) (j : Fin 2)
    (hmw : ∀ y, momentWeight γ' y = y j * momentWeight γ y)
    (hdeg : γ'.1 + γ'.2 = γ.1 + γ.2 + 1)
    (hcont : Continuous (D γ')) (hL2 : ∫⁻ ξ, ‖D γ' ξ‖ₑ ^ 2 < ∞)
    (hd : ∀ ξ, HasDerivAt (fun t : ℝ => D γ (ξ + t • basisVec j)) (D γ' ξ) 0)
    (hP : MomentFT v D γ) : MomentFT v D γ' := by
  obtain ⟨g, hg, hft⟩ := hP
  have hH : MemLp (fun x : Vec 2 => (Complex.I ^ (γ.1 + γ.2) * (2 * (Real.pi : ℂ))) *
      D γ' ((2 * Real.pi) • x)) 2 volume := memLp_dilate _ _ hcont hL2
  have hder : ∀ x : Vec 2, HasDerivAt
      (fun t : ℝ => Complex.I ^ (γ.1 + γ.2) * D γ ((2 * Real.pi) • (x + t • basisVec j)))
      ((Complex.I ^ (γ.1 + γ.2) * (2 * (Real.pi : ℂ))) * D γ' ((2 * Real.pi) • x)) 0 := by
    intro x
    have h2 : HasDerivAt (fun t : ℝ => (2 * Real.pi) * t) (2 * Real.pi) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
    have h1 : HasDerivAt (fun s : ℝ => D γ ((2 * Real.pi) • x + s • basisVec j))
        (D γ' ((2 * Real.pi) • x)) ((2 * Real.pi) * 0) := by
      rw [mul_zero]
      exact hd ((2 * Real.pi) • x)
    have h4 := (h1.scomp (0 : ℝ) h2).const_mul (Complex.I ^ (γ.1 + γ.2))
    convert h4 using 1
    · funext t
      simp only [Function.comp_apply, smul_add, smul_smul]
    · simp only [Complex.real_smul]
      push_cast
      ring
  obtain ⟨g', hg', hft'⟩ := moment_step g j _ _ hft hH hder
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine ⟨g', ?_, ?_⟩
  · filter_upwards [hg', hg] with y h1 h2
    rw [h1, h2, hmw]
    push_cast
    ring
  · filter_upwards [hft'] with x hx
    rw [hx, hdeg, pow_succ]
    field_simp

/-- The moments `y_0^k v`, `k ≤ β.1`. -/
theorem momentFT_first (v : Vec 2 → ℝ) (Φ : Vec 2 → ℂ) (β : ℕ × ℕ)
    (D : ℕ × ℕ → Vec 2 → ℂ) (hv : HasFT v Φ) (hD : DerivFamily β Φ D)
    (hL : ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 < ∞) :
    ∀ k : ℕ, k ≤ β.1 → MomentFT v D (k, 0) := by
  intro k
  induction k with
  | zero => exact fun _ => momentFT_zero v Φ D hv hD.1
  | succ k ih =>
    intro hk
    refine momentFT_step v D (k, 0) (k + 1, 0) 0 ?_ rfl
      (hD.2.1 (k + 1, 0) hk (Nat.zero_le _)) (hL (k + 1, 0) hk (Nat.zero_le _))
      (hD.2.2.1 (k, 0) hk (Nat.zero_le _)) (ih (Nat.le_of_succ_le hk))
    intro y
    simp only [momentWeight]
    ring

/-- The moments `y_0^{β.1} y_1^l v`, `l ≤ β.2`. -/
theorem momentFT_second (v : Vec 2 → ℝ) (Φ : Vec 2 → ℂ) (β : ℕ × ℕ)
    (D : ℕ × ℕ → Vec 2 → ℂ) (hv : HasFT v Φ) (hD : DerivFamily β Φ D)
    (hL : ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 < ∞) :
    ∀ l : ℕ, l ≤ β.2 → MomentFT v D (β.1, l) := by
  intro l
  induction l with
  | zero => exact fun _ => momentFT_first v Φ β D hv hD hL β.1 le_rfl
  | succ l ih =>
    intro hl
    refine momentFT_step v D (β.1, l) (β.1, l + 1) 1 ?_ rfl
      (hD.2.1 (β.1, l + 1) le_rfl hl) (hL (β.1, l + 1) le_rfl hl)
      (hD.2.2.2 (β.1, l) le_rfl hl) (ih (Nat.le_of_succ_le hl))
    intro y
    simp only [momentWeight]
    ring

/-- Plancherel with moments. -/
theorem momentPlancherel : MomentPlancherelStatement := by
  intro v Φ hv β D hD hL
  obtain ⟨g, hg, hft⟩ := momentFT_second v Φ β D hv hD hL β.2 le_rfl
  have hn : eLpNorm g 2 volume = eLpNorm (fourierL2 g) 2 volume := by
    have h := fourierL2_norm g
    rw [Lp.norm_def, Lp.norm_def] at h
    exact ((ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp h).symm
  have h1 : eLpNorm g 2 volume ^ 2 =
      ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * v z ^ 2) := by
    rw [eLpNorm_two_sq' _ (Lp.aestronglyMeasurable g)]
    apply lintegral_congr_ae
    filter_upwards [hg] with z hz
    rw [hz, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, mul_pow]
  have h2 : eLpNorm (fourierL2 g) 2 volume ^ 2 =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ‖D β ξ‖ₑ ^ 2 := by
    rw [eLpNorm_two_sq' _ (Lp.aestronglyMeasurable _),
      ← lintegral_dilate (fun ξ => ‖D β ξ‖ₑ ^ 2)
        ((hD.2.1 β le_rfl le_rfl).measurable.enorm.pow_const 2)]
    apply lintegral_congr_ae
    filter_upwards [hft] with x hx
    have hI : ‖Complex.I ^ (β.1 + β.2)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_pow, Complex.norm_I, one_pow, ENNReal.ofReal_one]
    rw [hx, enorm_mul, hI, one_mul]
  rw [← h1, hn, h2]

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the assembly from the three component statements

`scalar_of_parts` proves `ScalarStatement` from `JetFourierStatement`,
`MomentPlancherelStatement` and `FtCalculusStatement`;
`blochOutput_of_open_parts` is the whole chain down to `BlochOutputStatement`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

universe u v

theorem enorm_sq_le_band {z : ℂ} {C : ℝ} {k : ℕ} {ρ : ℝ} {ι : Type*} (s : Finset ι)
    (ξ : Vec 2) (F : ι → ℂ) (hC : 0 ≤ C)
    (h : ‖z‖ ^ 2 ≤ C * ∑ i ∈ s, (if ρ ^ 2 ≤ vecDot ξ ξ then
          (1 + vecDot ξ ξ) ^ k * ‖F i‖ ^ 2 else 0)) :
    ‖z‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ i ∈ s, (if ρ ^ 2 ≤ vecDot ξ ξ then
          ENNReal.ofReal ((1 + vecDot ξ ξ) ^ k * ‖F i‖ ^ 2) else 0) := by
  have hnn : ∀ i ∈ s, 0 ≤ (if ρ ^ 2 ≤ vecDot ξ ξ then (1 + vecDot ξ ξ) ^ k * ‖F i‖ ^ 2 else 0) := by
    intro i _
    split_ifs
    · have : 0 ≤ vecDot ξ ξ := by
        unfold vecDot; simp only [Fin.sum_univ_two]; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]
      positivity
    · exact le_rfl
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖z‖ ^ 2) ≤ ENNReal.ofReal (C * ∑ i ∈ s, (if ρ ^ 2 ≤ vecDot ξ ξ then
          (1 + vecDot ξ ξ) ^ k * ‖F i‖ ^ 2 else 0)) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg hnn]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp

theorem scalar_of_parts (h12 : JetFourierStatement) (h2 : MomentPlancherelStatement)
    (h3 : FtCalculusStatement) : ScalarStatement := by
  intro Kf m ρ Bμ hρ hBμ
  obtain ⟨C, hC, hC3⟩ := h3 Kf m ρ Bμ hρ hBμ
  refine ⟨((2 * Real.pi) ^ 2)⁻¹ * C, by positivity, ?_⟩
  intro μ hμ hμc hμe hμB hμ1 κ hκ u hmom β hβ a ha w
  have hg1 : Integrable (planeValue u) := by
    have := hmom (0, 0) (by unfold momentIndices; simp)
    simpa using this
  have hmomg : ∀ β ∈ momentIndices m, Integrable (fun y => momentWeight β y * planeValue u y) :=
    fun β hβ => hmom β hβ
  obtain ⟨D, hD, hbound⟩ := hC3 μ hμ hμc hμe hμB hμ1 a ha w (planeValue u) hmomg β hβ
  have hFT := h12 μ hμ hμc hμe κ a (ha.trans hκ) u hg1 w
  set X : ℝ≥0∞ := ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2),
    ∫⁻ ξ, BandIntegrand Kf ρ (fun y => momentWeight β' y * planeValue u y) ξ with hX
  by_cases htop : X = ⊤
  · rw [htop, ENNReal.mul_top (by
      refine (ENNReal.ofReal_pos.2 ?_).ne'
      positivity)]
    exact le_top
  have hmem : ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → γ ∈ momentIndices m := by
    intro γ h1 h2'
    have hq : β.1 + β.2 ≤ m := by
      have := hβ
      unfold momentIndices at this
      exact (by simpa using this : (β.1 ≤ m ∧ β.2 ≤ m) ∧ β.1 + β.2 ≤ m).2
    unfold momentIndices
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  -- the bound on each derivative
  have hder : ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 →
      ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 ≤ ENNReal.ofReal C * X := by
    intro γ h1 h2'
    have hpt : ∀ ξ, ‖D γ ξ‖ₑ ^ 2 ≤ ENNReal.ofReal C *
        ∑ γ' ∈ (momentIndices m).filter (fun γ' => γ'.1 ≤ γ.1 ∧ γ'.2 ≤ γ.2),
          BandIntegrand Kf ρ (fun y => momentWeight γ' y * planeValue u y) ξ := by
      intro ξ
      exact enorm_sq_le_band _ ξ (fun γ' => planeTransform (fun y => momentWeight γ' y * planeValue u y) ξ)
        hC.le (hbound γ h1 h2' ξ)
    calc ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 ≤ ∫⁻ ξ, ENNReal.ofReal C *
        ∑ γ' ∈ (momentIndices m).filter (fun γ' => γ'.1 ≤ γ.1 ∧ γ'.2 ≤ γ.2),
          BandIntegrand Kf ρ (fun y => momentWeight γ' y * planeValue u y) ξ := lintegral_mono hpt
      _ = ENNReal.ofReal C * ∑ γ' ∈ (momentIndices m).filter (fun γ' => γ'.1 ≤ γ.1 ∧ γ'.2 ≤ γ.2),
          ∫⁻ ξ, BandIntegrand Kf ρ (fun y => momentWeight γ' y * planeValue u y) ξ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
        intro γ' hγ'
        exact Band_measurable Kf ρ (hmomg γ' (Finset.mem_filter.1 hγ').1)
      _ ≤ ENNReal.ofReal C * X := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset ?_)
        intro γ' hγ'
        simp only [Finset.mem_filter] at hγ' ⊢
        exact ⟨hγ'.1, hγ'.2.1.trans h1, hγ'.2.2.trans h2'⟩
  have hfin : ∀ γ : ℕ × ℕ, γ.1 ≤ β.1 → γ.2 ≤ β.2 → ∫⁻ ξ, ‖D γ ξ‖ₑ ^ 2 < ⊤ := fun γ h1 h2' =>
    (hder γ h1 h2').trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 htop))
  have hmain := h2 _ _ hFT β D hD hfin
  rw [hmain, ENNReal.ofReal_mul (by positivity), mul_assoc]
  exact mul_le_mul' le_rfl (hder β le_rfl le_rfl)

/-- The scalar plane statement from its three parts. -/
theorem blochOutput_of_open_parts (h12 : JetFourierStatement)
    (h2 : MomentPlancherelStatement) (h3 : FtCalculusStatement) :
    BlochOutputStatement.{u, v} :=
  blochOutput_of_parts bridge (plane_of_scalar (scalar_of_parts h12 h2 h3))

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the transform of `μ(D) g`, and one classical derivative of a smooth function

* `cutoff_base`: for `g ∈ L¹ ∩ L²` and an even smooth compactly supported `μ`, the function
  `μ(D) g = fourierCutoff μ g` is in `L²` with transform `μ(2πx) ĝ(2πx)` (the convolution theorem
  `Real.fourier_mul_convolution_eq` and the transform of the kernel).
* `smooth_deriv_fourier`: if a `C¹` function `H ∈ L²` has transform `Ψ` and `2πi x_i Ψ ∈ L²`,
  then the classical derivative `∂_i H` is in `L²` with transform `2πi x_i Ψ` (the `L²` function
  with that transform is the distributional derivative; it agrees a.e. with the classical one).
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal FourierTransform SchwartzMap Convolution

namespace AVRegularity.CycleWords.Discard

theorem fourierCutoff_memLp (μ : Vec 2 → ℝ) (R : ℝ)
    (hR : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) μ)
    {g : Vec 2 → ℝ} (hg2 : MemLp g 2 volume) : MemLp (fourierCutoff μ g) 2 volume := by
  have h := seamFourierCutoff_memLp μ R hR hs (hg2.toLp g)
  rwa [fourierCutoff_congr_ae' μ hg2.coeFn_toLp] at h

theorem fourierCutoff_integrable (μ : Vec 2 → ℝ) (R : ℝ)
    (hR : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) μ)
    {g : Vec 2 → ℝ} (hg : Integrable g) : Integrable (fourierCutoff μ g) :=
  (seamCutoffKernel_integrable μ R hR hs).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hg

/-- The cutoff in the Hilbert coordinates is a convolution. -/
theorem Hil_fourierCutoff (μ : Vec 2 → ℝ) (g : Vec 2 → ℝ) :
    hilbertComplexify (fourierCutoff μ g) =
      hilbertComplexify (cutoffKernel μ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] hilbertComplexify g := by
  funext y
  rw [convolution_def]
  have ht := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
    (fun x : Vec 2 => ((cutoffKernel μ x • g (WithLp.ofLp y - x) : ℝ) : ℂ))
  have h1 : hilbertComplexify (fourierCutoff μ g) y =
      ∫ x : Vec 2, ((cutoffKernel μ x • g (WithLp.ofLp y - x) : ℝ) : ℂ) := by
    unfold hilbertComplexify fourierCutoff
    exact integral_ofReal.symm
  rw [h1, ← ht]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun t => ?_
  change ((cutoffKernel μ (WithLp.ofLp t) • g (WithLp.ofLp y - WithLp.ofLp t) : ℝ) : ℂ) =
    (cutoffKernel μ (WithLp.ofLp t) : ℂ) * (g (WithLp.ofLp (y - t)) : ℂ)
  rw [smul_eq_mul, Complex.ofReal_mul]
  rfl

/-- **The transform of `μ(D) g`.** -/
theorem cutoff_base (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ)
    (hev : ∀ θ, μ (-θ) = μ θ) {g : Vec 2 → ℝ} (hg : Integrable g) (hg2 : MemLp g 2 volume) :
    ∃ hh : MemLp (fourierCutoff μ g) 2 volume,
      fourierL2 (ofRealL2 volume (hh.toLp (fourierCutoff μ g))) =ᵐ[volume]
        fun x => (μ ((2 * Real.pi) • x) : ℂ) * planeTransform g ((2 * Real.pi) • x) := by
  obtain ⟨R, hR⟩ := radius' μ hμc
  have hh := fourierCutoff_memLp μ R hR hs hg2
  have hint := fourierCutoff_integrable μ R hR hs hg
  have hk := seamCutoffKernel_integrable μ R hR hs
  refine ⟨hh, ?_⟩
  have h1 := fourier_ae_eq_of_memLp (Hil_integrable hint) (Hil_memLp hh)
  have h2 := fourierL2_ae_of_coordinate (ofRealL2 volume (hh.toLp (fourierCutoff μ g)))
    (𝓕 (hilbertComplexify (fourierCutoff μ g))) (by rw [coordinate_ofReal_toLp hh]; exact h1.symm)
  filter_upwards [h2] with x hx
  rw [hx, Hil_fourierCutoff,
    Real.fourier_mul_convolution_eq (Hil_integrable hk) (Hil_integrable hg),
    Hil_cutoffKernel_fourier μ R hR hs hev, Hil_fourier]

/-- The classical integration by parts of a `C¹` function against a compactly supported smooth
test, in the Hilbert coordinates. -/
theorem Hil_ibp {H : Vec 2 → ℝ} (hHs : ContDiff ℝ 1 H) (i : Fin 2) (ψ : HilbertTwo → ℂ)
    (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, ψ x * hilbertComplexify (fun x => fderiv ℝ H x (basisVec i)) x =
      -∫ x, fderiv ℝ ψ x (coordinateVector i) * hilbertComplexify H x := by
  have hc0 : Continuous (hilbertComplexify H) :=
    Complex.continuous_ofReal.comp (hHs.continuous.comp (PiLp.continuous_ofLp 2 _))
  have hc1 : Continuous (hilbertComplexify (fun x => fderiv ℝ H x (basisVec i))) :=
    Complex.continuous_ofReal.comp
      (((hHs.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        (PiLp.continuous_ofLp 2 _))
  have hcd : Continuous (fun x => fderiv ℝ ψ x (coordinateVector i)) :=
    (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ ψ x (coordinateVector i)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (coordinateVector i)
  refine integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure HilbertTwo)) (f := ψ)
    (f' := fun x => fderiv ℝ ψ x (coordinateVector i)) (g := hilbertComplexify H)
    (g' := hilbertComplexify (fun x => fderiv ℝ H x (basisVec i))) (v := coordinateVector i)
    (B := ContinuousLinearMap.mul ℝ ℂ) ?_ ?_ ?_ ?_ ?_
  · exact (hcd.mul hc0).integrable_of_hasCompactSupport hcs.mul_right
  · exact (hψs.continuous.mul hc1).integrable_of_hasCompactSupport hψc.mul_right
  · exact (hψs.continuous.mul hc0).integrable_of_hasCompactSupport hψc.mul_right
  · intro x _
    exact (hψs.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (coordinateVector i)
  · intro x _
    have h := ((hHs.differentiable one_ne_zero (WithLp.ofLp x)).hasFDerivAt.hasLineDerivAt
      (basisVec i))
    unfold HasLineDerivAt at h ⊢
    simp only [hilbertComplexify, ofLp_add_smul_coordinateVector]
    exact h.ofReal_comp

/-- **One classical derivative of a smooth `L²` function, on the frequency side.** -/
theorem smooth_deriv_fourier {H : Vec 2 → ℝ} (hHs : ContDiff ℝ 1 H)
    (hH2 : MemLp H 2 volume) (i : Fin 2) (Ψ : Vec 2 → ℂ)
    (hΨ : fourierL2 (ofRealL2 volume (hH2.toLp H)) =ᵐ[volume] Ψ)
    (hΨ' : MemLp (fun x : Vec 2 => (2 * (Real.pi : ℂ) * Complex.I) * (x i : ℂ) * Ψ x) 2
      volume) :
    ∃ hH' : MemLp (fun x => fderiv ℝ H x (basisVec i)) 2 volume,
      fourierL2 (ofRealL2 volume (hH'.toLp (fun x => fderiv ℝ H x (basisVec i)))) =ᵐ[volume]
        fun x => (2 * (Real.pi : ℂ) * Complex.I) * (x i : ℂ) * Ψ x := by
  set f : Lp ℂ 2 (volume : Measure (Vec 2)) := ofRealL2 volume (hH2.toLp H) with hf
  set q : Lp ℂ 2 (volume : Measure (Vec 2)) := fourierL2.symm (hΨ'.toLp _) with hq
  have hqft : fourierL2 q =ᵐ[volume] fun ξ =>
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * fourierL2 f ξ := by
    rw [hq, LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [hΨ'.coeFn_toLp, hΨ] with ξ h1 h2
    rw [h1, h2]
  have hdist := planeFourier_distribution_derivative_of_ae f q i hqft
  have hfH : (coordinateL2Equiv f : Lp ℂ 2 (volume : Measure HilbertTwo)) =ᵐ[volume]
      hilbertComplexify H := by
    rw [hf, coordinate_ofReal_toLp hH2]
    exact (Hil_memLp hH2).coeFn_toLp
  have hc1 : Continuous (hilbertComplexify (fun x => fderiv ℝ H x (basisVec i))) :=
    Complex.continuous_ofReal.comp
      (((hHs.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        (PiLp.continuous_ofLp 2 _))
  have hkey : (coordinateL2Equiv q : Lp ℂ 2 (volume : Measure HilbertTwo)) =ᵐ[volume]
      hilbertComplexify (fun x => fderiv ℝ H x (basisVec i)) := by
    refine ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp (coordinateL2Equiv q)).locallyIntegrable (by norm_num))
      hc1.locallyIntegrable fun φ hφ hφc => ?_
    have hψs : ContDiff ℝ (⊤ : ℕ∞) (fun x : HilbertTwo => (φ x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hφ
    have hψc : HasCompactSupport (fun x : HilbertTwo => (φ x : ℂ)) :=
      hφc.comp_left Complex.ofReal_zero
    have hid := compact_test_identity_of_lineDerivOp _ _ (coordinateVector i) hdist
      (fun x : HilbertTwo => (φ x : ℂ)) hψs hψc
    have hibp := Hil_ibp hHs i (fun x : HilbertTwo => (φ x : ℂ)) hψs hψc
    have hcongr : (∫ x, fderiv ℝ (fun x : HilbertTwo => (φ x : ℂ)) x (coordinateVector i) *
        (coordinateL2Equiv f : Lp ℂ 2 (volume : Measure HilbertTwo)) x) =
        ∫ x, fderiv ℝ (fun x : HilbertTwo => (φ x : ℂ)) x (coordinateVector i) * hilbertComplexify H x := by
      apply integral_congr_ae
      filter_upwards [hfH] with x hx
      rw [hx]
    simp only [Complex.real_smul]
    rw [hibp, ← hcongr, hid, neg_neg]
  have hmem : MemLp (hilbertComplexify (fun x => fderiv ℝ H x (basisVec i))) 2 volume :=
    (Lp.memLp (coordinateL2Equiv q)).ae_eq hkey
  have hH' : MemLp (fun x => fderiv ℝ H x (basisVec i)) 2 volume := by
    have h1 := (hmem.comp_measurePreserving (PiLp.volume_preserving_toLp (Fin 2))).re
    refine h1.congr_norm ?_ ?_
    · exact ((hHs.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simp [hilbertComplexify]
  refine ⟨hH', ?_⟩
  have heq : ofRealL2 volume (hH'.toLp (fun x => fderiv ℝ H x (basisVec i))) = q := by
    apply coordinateL2Equiv.injective
    rw [coordinate_ofReal_toLp hH']
    apply Lp.ext
    filter_upwards [(Hil_memLp hH').coeFn_toLp, hkey] with x h1 h2
    rw [h1, h2]
  rw [heq, hq, LinearIsometryEquiv.apply_symm_apply]
  exact hΨ'.coeFn_toLp

end AVRegularity.CycleWords.Discard
end
end

section
/-! # `FtCalculusStatement`

`D γ = ∂_0^{γ₁} ∂_1^{γ₂} [(iξ)^w (1 - μ) ĝ]` is the sum over the terms `(∂^δ h) · E γ'` of
`leibnizTerms γ.1 γ.2`, where `h = (iξ)^w (1 - μ)` and `E γ' = (-i)^{|γ'|} FT(y^{γ'} g)`
(`Ft_hasDerivAt`). The factors `∂^δ h` are bounded by `B (1 + ‖ξ‖)^{Kf}` for `|δ| ≤ m`
(`H_bound`) and vanish on `|ξ| < ρ`; there are `2^{|γ|}` terms. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

namespace AVRegularity.CycleWords.Discard

/-- `E γ' = (-i)^{|γ'|} FT(y^{γ'} g)`: the `γ'`-th derivative of `ĝ`. -/
def transformDerivative (g : Vec 2 → ℝ) (γ' : ℕ × ℕ) (ξ : Vec 2) : ℂ :=
  (-Complex.I) ^ (γ'.1 + γ'.2) * planeTransform (fun y => momentWeight γ' y * g y) ξ

theorem Eft_norm (g : Vec 2 → ℝ) (γ' : ℕ × ℕ) (ξ : Vec 2) :
    ‖transformDerivative g γ' ξ‖ = ‖planeTransform (fun y => momentWeight γ' y * g y) ξ‖ := by
  simp [transformDerivative]

theorem Eft_zero (g : Vec 2 → ℝ) : transformDerivative g (0, 0) = planeTransform g := by
  funext ξ
  simp [transformDerivative, momentWeight]

theorem Eft_continuous {g : Vec 2 → ℝ} {γ' : ℕ × ℕ}
    (hg : Integrable (fun y => momentWeight γ' y * g y)) : Continuous (transformDerivative g γ') :=
  continuous_const.mul (Ft_continuous hg)

theorem Eft_hasDerivAt {g : Vec 2 → ℝ} {γ' : ℕ × ℕ} (j : Fin 2)
    (hg : Integrable (fun y => momentWeight γ' y * g y))
    (hgj : Integrable (fun y => momentWeight (γ' + unitIndexPair j) y * g y)) (ξ : Vec 2) :
    HasDerivAt (fun t : ℝ => transformDerivative g γ' (ξ + t • basisVec j))
      (transformDerivative g (γ' + unitIndexPair j) ξ) 0 := by
  have hj : Integrable (fun y : Vec 2 => y j * (momentWeight γ' y * g y)) := by
    refine hgj.congr (Filter.Eventually.of_forall fun y => ?_)
    fin_cases j <;> simp [unitIndexPair, momentWeight] <;> ring
  have := (Ft_hasDerivAt hg j hj ξ).const_mul ((-Complex.I) ^ (γ'.1 + γ'.2))
  refine this.congr_deriv ?_
  have e : (fun y : Vec 2 => momentWeight (γ' + unitIndexPair j) y * g y) =
      fun y => y j * (momentWeight γ' y * g y) := by
    funext y
    fin_cases j <;> simp [unitIndexPair, momentWeight] <;> ring
  have hn : (γ' + unitIndexPair j).1 + (γ' + unitIndexPair j).2 = γ'.1 + γ'.2 + 1 := by
    fin_cases j <;> simp [unitIndexPair] <;> omega
  unfold transformDerivative
  rw [e, hn, pow_succ]
  ring

theorem Dfun_norm_le (h : Vec 2 → ℂ) (E : ℕ × ℕ → Vec 2 → ℂ) (M : Multiset Term)
    (ξ : Vec 2) (b : ℝ) (hM : ∀ p : Term, p ∈ M → ‖multiPartialDeriv h p.1 ξ * E p.2 ξ‖ ≤ b) :
    ‖Dfun h E M ξ‖ ≤ Multiset.card M * b := by
  unfold Dfun
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  refine (Multiset.sum_le_card_nsmul _ b ?_).trans ?_
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    exact hM p hp
  · simp

theorem Hd_norm_le {h : Vec 2 → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (δ : ℕ × ℕ) (ξ : Vec 2) :
    ‖multiPartialDeriv h δ ξ‖ ≤ ‖iteratedFDeriv ℝ (δ.1 + δ.2) h ξ‖ := by
  have := PL_norm_le hh (List.replicate δ.1 (basisVec 0) ++ List.replicate δ.2 (basisVec 1))
    (by
      intro v hv
      rw [List.mem_append, List.mem_replicate, List.mem_replicate] at hv
      rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [basisVec, Pi.norm_single]) ξ
  have hl : (List.replicate δ.1 (basisVec (0 : Fin 2)) ++ List.replicate δ.2 (basisVec (1 : Fin 2))).length =
      δ.1 + δ.2 := by simp
  rw [hl] at this
  exact this

theorem Hd_zero_on {h : Vec 2 → ℂ} {U : Set (Vec 2)} (hU : IsOpen U) (hz : ∀ ξ ∈ U, h ξ = 0)
    (δ : ℕ × ℕ) : ∀ ξ ∈ U, multiPartialDeriv h δ ξ = 0 := PL_zero_on hU hz _

theorem mem_momentIndices {m : ℕ} {β γ : ℕ × ℕ} (hβ : β ∈ momentIndices m)
    (h1 : γ.1 ≤ β.1) (h2 : γ.2 ≤ β.2) : γ ∈ momentIndices m := by
  simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ ⊢
  omega

theorem norm_sq_le (ξ : Vec 2) : ‖ξ‖ ^ 2 ≤ vecDot ξ ξ := by
  have hv : 0 ≤ vecDot ξ ξ := by
    unfold vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 : ‖ξ‖ ≤ Real.sqrt (vecDot ξ ξ) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    unfold vecDot
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp <;> nlinarith [mul_self_nonneg (ξ 0), mul_self_nonneg (ξ 1)]
  calc ‖ξ‖ ^ 2 ≤ (Real.sqrt (vecDot ξ ξ)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hv

theorem one_add_sq_le (Kf : ℕ) (nx v : ℝ) (hnx0 : 0 ≤ nx) (hnx : nx ^ 2 ≤ v) :
    (1 + nx) ^ (2 * Kf) ≤ 2 ^ Kf * (1 + v) ^ Kf := by
  rw [pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ Kf
  nlinarith [sq_nonneg (1 - nx)]

theorem term_real (Kf : ℕ) (B nx v Hn Fn W : ℝ) (hHn0 : 0 ≤ Hn)
    (hFn : 0 ≤ Fn) (hH : Hn ≤ B * (1 + nx) ^ Kf) (hnx0 : 0 ≤ nx) (hnx : nx ^ 2 ≤ v)
    (hW : (1 + v) ^ Kf * Fn ^ 2 ≤ W) : Hn * Fn ≤ Real.sqrt (B ^ 2 * 2 ^ Kf * W) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h3 : (Hn * Fn) ^ 2 ≤ (B * (1 + nx) ^ Kf * Fn) ^ 2 := by gcongr
  have h4 : (B * (1 + nx) ^ Kf * Fn) ^ 2 = B ^ 2 * (1 + nx) ^ (2 * Kf) * Fn ^ 2 := by
    rw [pow_mul']; ring
  have h5 := one_add_sq_le Kf nx v hnx0 hnx
  have h6 : B ^ 2 * (1 + nx) ^ (2 * Kf) * Fn ^ 2 ≤
      B ^ 2 * 2 ^ Kf * ((1 + v) ^ Kf * Fn ^ 2) := by
    calc _ ≤ B ^ 2 * (2 ^ Kf * (1 + v) ^ Kf) * Fn ^ 2 := by gcongr
      _ = _ := by ring
  calc (Hn * Fn) ^ 2 ≤ _ := h3
    _ = _ := h4
    _ ≤ _ := h6
    _ ≤ _ := by gcongr

theorem sum_real (n m : ℕ) (K W D : ℝ) (hn : n ≤ m) (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hD0 : 0 ≤ D)
    (hD : D ≤ 2 ^ n * Real.sqrt (K * W)) : D ^ 2 ≤ (4 ^ m * K + 1) * W := by
  have h1 : D ^ 2 ≤ (2 ^ n * Real.sqrt (K * W)) ^ 2 := by gcongr
  have h2 : (2 ^ n * Real.sqrt (K * W)) ^ 2 = (4 : ℝ) ^ n * (K * W) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3 : (4 : ℝ) ^ n ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hn
  have h4 : 0 ≤ K * W := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

theorem vecDot_nonneg (ξ : Vec 2) : 0 ≤ vecDot ξ ξ := by
  unfold vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- The band bound for one `D γ`, once the factors `∂^δ h` and the transforms are bounded. -/
theorem dfun_bound {h : Vec 2 → ℂ} {E : ℕ × ℕ → Vec 2 → ℂ} (Kf m : ℕ) (B : ℝ)
    (γ : ℕ × ℕ) (hγ : γ.1 + γ.2 ≤ m) (ξ : Vec 2) (S : Finset (ℕ × ℕ))
    (hH : ∀ p : Term, p ∈ leibnizTerms γ.1 γ.2 → ‖multiPartialDeriv h p.1 ξ‖ ≤ B * (1 + ‖ξ‖) ^ Kf)
    (hS : ∀ p : Term, p ∈ leibnizTerms γ.1 γ.2 → p.2 ∈ S) :
    ‖Dfun h E (leibnizTerms γ.1 γ.2) ξ‖ ^ 2 ≤ (4 ^ m * (B ^ 2 * 2 ^ Kf) + 1) *
      ∑ γ' ∈ S, (1 + vecDot ξ ξ) ^ Kf * ‖E γ' ξ‖ ^ 2 := by
  have hv := vecDot_nonneg ξ
  have hW0 : 0 ≤ ∑ γ' ∈ S, (1 + vecDot ξ ξ) ^ Kf * ‖E γ' ξ‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hterm : ∀ p : Term, p ∈ leibnizTerms γ.1 γ.2 →
      ‖multiPartialDeriv h p.1 ξ * E p.2 ξ‖ ≤
        Real.sqrt (B ^ 2 * 2 ^ Kf * ∑ γ' ∈ S, (1 + vecDot ξ ξ) ^ Kf * ‖E γ' ξ‖ ^ 2) := by
    intro p hp
    have h7 : (1 + vecDot ξ ξ) ^ Kf * ‖E p.2 ξ‖ ^ 2 ≤
        ∑ γ' ∈ S, (1 + vecDot ξ ξ) ^ Kf * ‖E γ' ξ‖ ^ 2 :=
      Finset.single_le_sum (f := fun γ' => (1 + vecDot ξ ξ) ^ Kf * ‖E γ' ξ‖ ^ 2)
        (fun _ _ => by positivity) (hS p hp)
    rw [norm_mul]
    exact term_real Kf B ‖ξ‖ (vecDot ξ ξ) _ _ _ (norm_nonneg _) (norm_nonneg _)
      (hH p hp) (norm_nonneg _) (norm_sq_le ξ) h7
  have hD := Dfun_norm_le h E _ ξ _ hterm
  have hcard : (Multiset.card (leibnizTerms γ.1 γ.2) : ℝ) = 2 ^ (γ.1 + γ.2) := by
    rw [Mab_card]; push_cast; ring
  rw [hcard] at hD
  exact sum_real (γ.1 + γ.2) m _ _ _ hγ (by positivity) hW0 (norm_nonneg _) hD

theorem ftCalculus : FtCalculusStatement := by
  intro Kf m ρ Bμ hρ hBμ
  obtain ⟨B, hB0, hBb⟩ := H_bound Kf m Bμ
  refine ⟨4 ^ m * (B ^ 2 * 2 ^ Kf) + 1, by positivity, ?_⟩
  intro μ hμ _hcs _hsymm hderiv hone a ha w g hint β hβ
  have hh : ContDiff ℝ (⊤ : ℕ∞) (symbolCutoffFactor μ w) := H_contDiff hμ w
  have hβm : β.1 + β.2 ≤ m := by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ
    omega
  have hintγ : ∀ γ' : ℕ × ℕ, γ'.1 ≤ β.1 → γ'.2 ≤ β.2 →
      Integrable (fun y => momentWeight γ' y * g y) :=
    fun γ' h1 h2 => hint γ' (mem_momentIndices hβ h1 h2)
  have hEd : ∀ (j : Fin 2) (γ' : ℕ × ℕ), (γ' + unitIndexPair j).1 ≤ β.1 → (γ' + unitIndexPair j).2 ≤ β.2 →
      ∀ ξ : Vec 2, HasDerivAt (fun t : ℝ => transformDerivative g γ' (ξ + t • basisVec j))
        (transformDerivative g (γ' + unitIndexPair j) ξ) 0 := by
    intro j γ' h1 h2 ξ
    refine Eft_hasDerivAt j (hintγ γ' ?_ ?_) (hintγ _ h1 h2) ξ
    · exact (Nat.le_add_right _ _).trans h1
    · exact (Nat.le_add_right _ _).trans h2
  have hsum := Mab_sum
  refine ⟨fun γ => Dfun (symbolCutoffFactor μ w) (transformDerivative g) (leibnizTerms γ.1 γ.2), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · funext ξ
    simp only [leibnizTerms, Function.iterate_zero, id, Dfun, Multiset.map_singleton,
      Multiset.sum_singleton, multiPartialDeriv, List.replicate_zero, List.append_nil, iterDirDeriv, Eft_zero]
    rfl
  · intro γ h1 h2
    refine Dfun_continuous hh _ _ fun p hp => ?_
    have hs := hsum γ.1 γ.2 p hp
    have e1 : p.1.1 + p.2.1 = γ.1 := congrArg Prod.fst hs
    have e2 : p.1.2 + p.2.2 = γ.2 := congrArg Prod.snd hs
    exact Eft_continuous (hintγ _ (by omega) (by omega))
  · intro γ h1 h2 ξ
    have := Mab_hasDerivAt hh (transformDerivative g) β hEd 0 γ (by simpa [unitIndexPair] using h1)
      (by simpa [unitIndexPair] using h2) ξ
    simpa [unitIndexPair] using this
  · intro γ h1 h2 ξ
    have := Mab_hasDerivAt hh (transformDerivative g) β hEd 1 γ (by simpa [unitIndexPair] using h1)
      (by simpa [unitIndexPair] using h2) ξ
    simpa [unitIndexPair] using this
  · intro γ h1 h2 ξ
    have hγm : γ.1 + γ.2 ≤ m := by omega
    set M := leibnizTerms γ.1 γ.2 with hM
    show ‖Dfun (symbolCutoffFactor μ w) (transformDerivative g) M ξ‖ ^ 2 ≤ _
    by_cases hξ : ρ ^ 2 ≤ vecDot ξ ξ
    · simp only [hξ, ite_true]
      have hS : ∀ p : Term, p ∈ M →
          p.2 ∈ (momentIndices m).filter (fun γ' => γ'.1 ≤ γ.1 ∧ γ'.2 ≤ γ.2) := by
        intro p hp
        have hs := hsum γ.1 γ.2 p hp
        have e1 : p.1.1 + p.2.1 = γ.1 := congrArg Prod.fst hs
        have e2 : p.1.2 + p.2.2 = γ.2 := congrArg Prod.snd hs
        rw [Finset.mem_filter]
        exact ⟨mem_momentIndices hβ (by omega) (by omega), by omega, by omega⟩
      have hH : ∀ p : Term, p ∈ M →
          ‖multiPartialDeriv (symbolCutoffFactor μ w) p.1 ξ‖ ≤ B * (1 + ‖ξ‖) ^ Kf := by
        intro p hp
        have hs := hsum γ.1 γ.2 p hp
        have e1 : p.1.1 + p.2.1 = γ.1 := congrArg Prod.fst hs
        have e2 : p.1.2 + p.2.2 = γ.2 := congrArg Prod.snd hs
        have hb := hBb μ hμ (fun l hl θ => hderiv l θ (by omega)) hBμ a ha w (p.1.1 + p.1.2)
          (by omega) ξ
        exact (Hd_norm_le hh p.1 ξ).trans hb
      have := dfun_bound (h := symbolCutoffFactor μ w) (E := transformDerivative g) Kf m B γ hγm ξ _ hH hS
      simpa only [Eft_norm] using this
    · have hlt : vecDot ξ ξ < ρ ^ 2 := not_le.1 hξ
      have hU : IsOpen {θ : Vec 2 | vecDot θ θ < ρ ^ 2} :=
        isOpen_lt (by unfold vecDot; fun_prop) continuous_const
      have hz : ∀ θ ∈ {θ : Vec 2 | vecDot θ θ < ρ ^ 2}, symbolCutoffFactor μ w θ = 0 := by
        intro θ hθ
        simp [symbolCutoffFactor, hone θ hθ]
      have h0 : Dfun (symbolCutoffFactor μ w) (transformDerivative g) M ξ = 0 := by
        unfold Dfun
        refine Multiset.sum_eq_zero fun x hx => ?_
        obtain ⟨p, _, rfl⟩ := Multiset.mem_map.1 hx
        simp [Hd_zero_on hU hz p.1 ξ hlt]
      rw [h0]
      simp [hξ]

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the transform of the jet of `u - μ(D)u`

`jetFourier : JetFourierStatement`. Both the weak jet `planeJetOrder u a w` and the classical
derivative `orderedDerivative w (μ(D) g)` are built letter by letter (`Fin.snoc`), so both
transforms are obtained by induction on the length of the word:

* `jet_fourier`: the jets, by `planeFourier_real_weakDerivative_ae`; the base is
  `fourierL2_of_integrable`.
* `cutoff_fourier`: the derivatives of `μ(D) g`, by `smooth_deriv_fourier`; the base is
  `cutoff_base`. The frequency side `(iξ)^w μ ĝ` is continuous with compact support.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

theorem symbol_zero (w : DerivativeWord2 0) (ξ : Vec 2) : derivativeWordSymbol w ξ = 1 := by
  simp [derivativeWordSymbol]

/-- The symbol of a word, one letter at a time, at the frequency `2π x`. -/
theorem symbol_snoc_scaled {a : ℕ} (w : DerivativeWord2 (a + 1)) (x : Vec 2) :
    derivativeWordSymbol w ((2 * Real.pi) • x) =
      (2 * (Real.pi : ℂ) * Complex.I) * (x (w (Fin.last a)) : ℂ) *
        derivativeWordSymbol (fun j : Fin a => w j.castSucc) ((2 * Real.pi) • x) := by
  unfold derivativeWordSymbol
  rw [Fin.prod_univ_castSucc]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem symbol_continuous {a : ℕ} (w : DerivativeWord2 a) : Continuous (derivativeWordSymbol w) := by
  unfold derivativeWordSymbol
  exact continuous_finsetProd _ fun j _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply (w j)))

theorem orderedDerivative_snoc' {a : ℕ} (w : DerivativeWord2 (a + 1)) (g : Vec 2 → ℝ) :
    orderedDerivative w g = fun x =>
      fderiv ℝ (orderedDerivative (fun i : Fin a => w i.castSucc) g) x
        (basisVec (w (Fin.last a))) := by
  unfold orderedDerivative
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  rfl

theorem orderedDerivative_contDiff' : ∀ {a : ℕ} (w : DerivativeWord2 a) {g : Vec 2 → ℝ},
    ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) (orderedDerivative w g)
  | 0, w, g, hg => by simpa [orderedDerivative] using hg
  | a + 1, w, g, hg => by
    rw [orderedDerivative_snoc']
    exact ((orderedDerivative_contDiff' (fun i : Fin a => w i.castSucc) hg).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- `HasFT` is stable under subtraction. -/
theorem hasFT_sub {v₁ v₂ : Vec 2 → ℝ} {Φ₁ Φ₂ : Vec 2 → ℂ} (h₁ : HasFT v₁ Φ₁)
    (h₂ : HasFT v₂ Φ₂) : HasFT (fun z => v₁ z - v₂ z) (fun ξ => Φ₁ ξ - Φ₂ ξ) := by
  obtain ⟨hv₁, hf₁⟩ := h₁
  obtain ⟨hv₂, hf₂⟩ := h₂
  refine ⟨hv₁.sub hv₂, ?_⟩
  have h : (hv₁.sub hv₂).toLp (fun z => v₁ z - v₂ z) = hv₁.toLp v₁ - hv₂.toLp v₂ := rfl
  rw [h, map_sub, map_sub]
  filter_upwards [Lp.coeFn_sub (fourierL2 (ofRealL2 volume (hv₁.toLp v₁)))
    (fourierL2 (ofRealL2 volume (hv₂.toLp v₂))), hf₁, hf₂] with x h0 h1 h2
  rw [h0, Pi.sub_apply, h1, h2]

theorem hasFT_congr {v : Vec 2 → ℝ} {Φ Φ' : Vec 2 → ℂ} (h : HasFT v Φ)
    (hΦ : ∀ ξ, Φ ξ = Φ' ξ) : HasFT v Φ' := by
  rw [← funext hΦ]
  exact h

/-- Consecutive jets of a plane Sobolev function are weak partial derivatives. -/
theorem jet_weak {κ a : ℕ} (ha : a + 1 ≤ κ) (u : PlaneHk Set.univ κ ℝ)
    (w : DerivativeWord2 (a + 1)) :
    HasWeakPartialDerivOn Set.univ (w (Fin.last a))
      (planeJetOrder u a (fun j : Fin a => w j.castSucc)) (planeJetOrder u (a + 1) w) := by
  have h := u.toFunction.hasWeakJet (⟨a, ha⟩ : Fin κ) (fun j : Fin a => w j.castSucc)
    (w (Fin.last a)) 1
  have hn : nextIndex2 (⟨a, ha⟩ : Fin κ) (fun j : Fin a => w j.castSucc) (w (Fin.last a)) =
      ⟨⟨a + 1, Nat.lt_succ_of_le ha⟩, w⟩ := by
    unfold nextIndex2 nextIndex
    congr 1
    exact Fin.snoc_init_self w
  rw [planeJetOrder_eq_stored (Nat.le_of_succ_le ha) u, planeJetOrder_eq_stored ha u]
  simpa only [Real.inner_apply, one_mul, mul_one, lowerIndex2, lowerIndex, hn] using h

/-- **The transform of the jets.** -/
theorem jet_fourier {κ : ℕ} (u : PlaneHk Set.univ κ ℝ) (hint : Integrable (planeValue u)) :
    ∀ (a : ℕ) (_ : a ≤ κ) (w : DerivativeWord2 a),
      HasFT (planeJetOrder u a w)
        (fun ξ => derivativeWordSymbol w ξ * planeTransform (planeValue u) ξ) := by
  intro a
  induction a with
  | zero =>
    intro ha w
    have hw : w = fun i => i.elim0 := Subsingleton.elim _ _
    subst hw
    have hm : MemLp (planeValue u) 2 volume := planeJetOrder_memLp ha u _
    refine ⟨hm, ?_⟩
    filter_upwards [fourierL2_of_integrable hint hm] with x hx
    rw [symbol_zero, one_mul]
    exact hx
  | succ a ih =>
    intro ha w
    have hw := jet_weak ha u w
    obtain ⟨hmem', hft'⟩ := ih (Nat.le_of_succ_le ha) (fun j : Fin a => w j.castSucc)
    have hmem := planeJetOrder_memLp ha u w
    have hw' : HasWeakPartialDerivOn Set.univ (w (Fin.last a))
        (hmem'.toLp (planeJetOrder u a (fun j : Fin a => w j.castSucc)))
        (hmem.toLp (planeJetOrder u (a + 1) w)) :=
      hasWeakPartialDerivOn_congr_ae
        (by simpa only [Measure.restrict_univ] using hmem'.coeFn_toLp.symm)
        (by simpa only [Measure.restrict_univ] using hmem.coeFn_toLp.symm) hw
    refine ⟨hmem, ?_⟩
    filter_upwards [planeFourier_real_weakDerivative_ae _ _ _ hw', hft'] with x h1 h2
    rw [h1, h2, symbol_snoc_scaled]
    ring

/-- The frequency side `(iξ)^w μ ĝ` of the derivatives of `μ(D) g`, at `2π x`, is in `L²`. -/
theorem cutoff_symbol_memLp (μ : Vec 2 → ℝ) (hs : Continuous μ) (hμc : HasCompactSupport μ)
    {g : Vec 2 → ℝ} (hg : Integrable g) {a : ℕ} (w : DerivativeWord2 a) :
    MemLp (fun x : Vec 2 => derivativeWordSymbol w ((2 * Real.pi) • x) *
      ((μ ((2 * Real.pi) • x) : ℂ) * planeTransform g ((2 * Real.pi) • x))) 2 volume := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hsm : Continuous (fun x : Vec 2 => (2 * Real.pi) • x) := continuous_const_smul _
  have hcμ : HasCompactSupport (fun x : Vec 2 => μ ((2 * Real.pi) • x)) :=
    hμc.comp_homeomorph (Homeomorph.smulOfNeZero (2 * Real.pi) hπ)
  refine Continuous.memLp_of_hasCompactSupport ?_ ?_
  · exact ((symbol_continuous w).comp hsm).mul
      ((Complex.continuous_ofReal.comp (hs.comp hsm)).mul ((Ft_continuous hg).comp hsm))
  · refine hcμ.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [h0, Complex.ofReal_zero, zero_mul, mul_zero]

/-- **The transform of the derivatives of `μ(D) g`.** -/
theorem cutoff_fourier (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hev : ∀ θ, μ (-θ) = μ θ) {g : Vec 2 → ℝ} (hg : Integrable g)
    (hg2 : MemLp g 2 volume) :
    ∀ (a : ℕ) (w : DerivativeWord2 a),
      HasFT (orderedDerivative w (fourierCutoff μ g))
        (fun ξ => derivativeWordSymbol w ξ * ((μ ξ : ℂ) * planeTransform g ξ)) := by
  intro a
  induction a with
  | zero =>
    intro w
    obtain ⟨hh, hft⟩ := cutoff_base μ hs hμc hev hg hg2
    have h0 : orderedDerivative w (fourierCutoff μ g) = fourierCutoff μ g := by
      simp [orderedDerivative]
    rw [h0]
    refine ⟨hh, ?_⟩
    filter_upwards [hft] with x hx
    rw [hx, symbol_zero, one_mul]
  | succ a ih =>
    intro w
    obtain ⟨hm', hft'⟩ := ih (fun j : Fin a => w j.castSucc)
    have hsm : ContDiff ℝ (⊤ : ℕ∞)
        (orderedDerivative (fun j : Fin a => w j.castSucc) (fourierCutoff μ g)) :=
      orderedDerivative_contDiff' _ (fourierCutoff_contDiff μ hs hμc hg)
    have hΨ' : MemLp (fun x : Vec 2 => (2 * (Real.pi : ℂ) * Complex.I) *
        (x (w (Fin.last a)) : ℂ) *
        (derivativeWordSymbol (fun j : Fin a => w j.castSucc) ((2 * Real.pi) • x) *
          ((μ ((2 * Real.pi) • x) : ℂ) * planeTransform g ((2 * Real.pi) • x)))) 2 volume := by
      refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_)
        (cutoff_symbol_memLp μ hs.continuous hμc hg w)
      simp only
      rw [symbol_snoc_scaled]
      ring
    obtain ⟨hm, hft⟩ := smooth_deriv_fourier (hsm.of_le (by simp)) hm' (w (Fin.last a)) _
      hft' hΨ'
    rw [orderedDerivative_snoc']
    refine ⟨hm, ?_⟩
    filter_upwards [hft] with x hx
    rw [hx, symbol_snoc_scaled]
    ring

/-- The transform of the jet of `u - μ(D)u`. -/
theorem jetFourier : JetFourierStatement := by
  intro μ hs hμc hev κ a ha u hint w
  have hg2 : MemLp (planeValue u) 2 volume := planeJetOrder_memLp (Nat.zero_le κ) u _
  have hJ := jet_fourier u hint a ha w
  have hC := cutoff_fourier μ hs hμc hev hint hg2 a w
  refine hasFT_congr (hasFT_sub hJ hC) fun ξ => ?_
  simp only [jetFrequencySide]
  push_cast
  ring

end AVRegularity.CycleWords.Discard
end
end
