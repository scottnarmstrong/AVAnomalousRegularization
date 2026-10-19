-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import AVRegularity.CoupledEnergyPlane.Fourier.DistributionDerivative
public import Homogenization.Sobolev.WeakDerivatives

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Extend scalar spatial operators to finite Hilbert fibers by orthonormal coordinates.
Parseval gives the same operator bound, without a dimension factor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {μ : Measure (Vec 2)}

/-- Extract one orthonormal fiber coordinate in spatial L². -/
def fiberCoordinate (k : Fin (Module.finrank ℝ E)) : Lp E 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E k)).compLpL 2 μ

/-- Synthesize one orthonormal fiber coordinate in spatial L². -/
def fiberInjection (k : Fin (Module.finrank ℝ E)) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E k)).compLpL 2 μ

theorem fiberCoordinate_ae (k : Fin (Module.finrank ℝ E)) (u : Lp E 2 μ) :
    fiberCoordinate k u =ᵐ[μ] fun x => inner ℝ (stdOrthonormalBasis ℝ E k) (u x) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem fiberInjection_ae (k : Fin (Module.finrank ℝ E)) (u : Lp ℝ 2 μ) :
    fiberInjection k u =ᵐ[μ] fun x => u x • stdOrthonormalBasis ℝ E k :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem fiberCoordinate_injection (j k : Fin (Module.finrank ℝ E)) (u : Lp ℝ 2 μ) :
    fiberCoordinate j (fiberInjection k u) = if j = k then u else 0 := by
  apply Lp.ext
  filter_upwards [fiberCoordinate_ae j (fiberInjection k u), fiberInjection_ae k u,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hc hi hz
  rw [hc, hi, real_inner_smul_right, OrthonormalBasis.inner_eq_ite]
  by_cases h : j = k
  · simp [h]
  · simp only [h, ite_false, mul_zero]
    exact hz.symm

theorem fiberL2_inner (u v : Lp E 2 μ) :
    inner ℝ u v = ∑ k : Fin (Module.finrank ℝ E),
      inner ℝ (fiberCoordinate k u) (fiberCoordinate k v) := by
  simp only [L2.inner_def]
  rw [← integral_finsetSum Finset.univ (fun k _ =>
    L2.integrable_inner (𝕜 := ℝ) (fiberCoordinate k u) (fiberCoordinate k v))]
  have hu := ae_all_iff.mpr (fun k => fiberCoordinate_ae k u)
  have hv := ae_all_iff.mpr (fun k => fiberCoordinate_ae k v)
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  simp_rw [hx, hy, Real.inner_apply]
  simpa only [real_inner_comm] using
    ((stdOrthonormalBasis ℝ E).sum_inner_mul_inner (u x) (v x)).symm

theorem fiberL2_normSq (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∑ k : Fin (Module.finrank ℝ E), ‖fiberCoordinate k u‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using fiberL2_inner u u

/-- Apply a scalar spatial operator independently in the fiber coordinates. -/
def hilbertLift (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  ∑ k : Fin (Module.finrank ℝ E), (fiberInjection k).comp (T.comp (fiberCoordinate k))

theorem hilbertLift_coordinate (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (u : Lp E 2 μ) (k : Fin (Module.finrank ℝ E)) :
    fiberCoordinate k (hilbertLift T u) = T (fiberCoordinate k u) := by
  classical
  simp only [hilbertLift, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, fiberCoordinate_injection]
  simp

theorem fiberCoordinate_ext {u v : Lp E 2 μ}
    (h : ∀ k : Fin (Module.finrank ℝ E), fiberCoordinate k u = fiberCoordinate k v) : u = v := by
  apply Lp.ext
  have hu := ae_all_iff.mpr (fun k => fiberCoordinate_ae k u)
  have hv := ae_all_iff.mpr (fun k => fiberCoordinate_ae k v)
  filter_upwards [hu, hv] with x hx hy
  apply (stdOrthonormalBasis ℝ E).repr.injective
  ext k
  simpa only [OrthonormalBasis.repr_apply_apply, ← hx k, ← hy k] using
    congrArg (fun f : Lp ℝ 2 μ => f x) (h k)

theorem hilbertLift_id (u : Lp E 2 μ) : hilbertLift (ContinuousLinearMap.id ℝ _) u = u := by
  apply fiberCoordinate_ext
  intro k
  rw [hilbertLift_coordinate, ContinuousLinearMap.id_apply]

end AVRegularity.CoupledEnergyPlane.Fourier
end
end

section
@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The actual distribution derivative of a smooth L² representative,
proved by global integration by parts against Schwartz functions. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem lineDerivOp_L2_of_smooth_representative
    (f g : Lp ℂ 2 (volume : Measure V)) (v : V) (F : V → ℂ)
    (hF : Differentiable ℝ F) (hf : f =ᵐ[volume] F)
    (hg : g =ᵐ[volume] fun x => fderiv ℝ F x v) :
    ∂_{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)) := by
  have hmF : MemLp F 2 (volume : Measure V) := (memLp_congr_ae hf).mp (Lp.memLp f)
  have hmD : MemLp (fun x => fderiv ℝ F x v) 2 (volume : Measure V) :=
    (memLp_congr_ae hg).mp (Lp.memLp g)
  ext ψ
  have hmψ := ψ.memLp 2 (volume : Measure V)
  have hmψD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume : Measure V) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using (∂_{v} ψ).memLp 2 (volume : Measure V)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hmD.integrable_mul hmψ) (hmF.integrable_mul hmψD) (hmF.integrable_mul hmψ)
    (fun x _ => hF x) (fun _ _ => ψ.differentiableAt)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  calc
    (∫ x, -(fderiv ℝ ψ x v) * f x) = -(∫ x, F x * fderiv ℝ ψ x v) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx, neg_mul, mul_comm]
    _ = ∫ x, fderiv ℝ F x v * ψ x := by rw [hibp, neg_neg]
    _ = ∫ x, ψ x * g x := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx, mul_comm]

end AVRegularity.CoupledEnergyPlane.Fourier
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CoupledEnergyPlane.L2Multiplier

/-! Literal bounded multipliers on L², using Mathlib's existing Hölder bilinear map.
These supply the bounded angular-frequency factors in the projected PDE. -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Multiplication by the actual essentially bounded symbol. -/
def operator (a : X → ℂ) (ha : MemLp a ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 (ha.toLp a)

theorem operator_ae (a : X → ℂ) (ha : MemLp a ∞ μ) (f : Lp ℂ 2 μ) :
    operator a ha f =ᵐ[μ] fun x => a x * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (ha.toLp a) f (r := 2)
  filter_upwards [h, ha.coeFn_toLp] with x hx hy
  change (ContinuousLinearMap.mul ℂ ℂ).holder 2 (ha.toLp a) f x = _
  rw [hx, hy]
  rfl

theorem operator_norm_apply_le (a : X → ℂ) (ha : MemLp a ∞ μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖operator a ha f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator_ae a ha f, hC] with x hx hcx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hcx (norm_nonneg _)

theorem operator_norm_le (a : X → ℂ) (ha : MemLp a ∞ μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖operator a ha‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC (operator_norm_apply_le a ha haC)

end AVRegularity.CoupledEnergyPlane.L2Multiplier
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Transport of actual distributional Fourier derivatives to the source
coordinate weak identities. All coordinate changes preserve volume. -/

/-- Hilbert-coordinate distribution derivatives give the literal source complex test identity. -/
theorem coordinate_compact_test_identity
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)))
    (ψ : Vec 2 → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ x, fderiv ℝ ψ x (basisVec i) * f x) = -(∫ x, ψ x * g x) := by
  have hd (x : HilbertTwo) :
      fderiv ℝ (ψ ∘ coordinateHilbertEquiv) x (coordinateVector i) =
        fderiv ℝ ψ (WithLp.ofLp x) (basisVec i) := by
    rw [coordinateHilbertEquiv.comp_right_fderiv]
    rfl
  have ht := compact_test_identity_of_lineDerivOp (coordinateL2Equiv f)
    (coordinateL2Equiv g) (coordinateVector i) hfg (ψ ∘ coordinateHilbertEquiv)
    (hs.comp coordinateHilbertEquiv.contDiff)
    (hc.comp_homeomorph coordinateHilbertEquiv.toHomeomorph)
  have hl : (∫ x : HilbertTwo, fderiv ℝ (ψ ∘ coordinateHilbertEquiv) x
      (coordinateVector i) * coordinateL2Equiv f x) =
      ∫ x : Vec 2, fderiv ℝ ψ x (basisVec i) * f x := by
    calc
      _ = ∫ x : HilbertTwo, fderiv ℝ ψ (WithLp.ofLp x) (basisVec i) *
          f (WithLp.ofLp x) := by
        apply integral_congr_ae
        filter_upwards [coordinateL2Equiv_ae f] with x hx
        rw [hd x, hx]
      _ = _ := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
        coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
        (fun x : Vec 2 => fderiv ℝ ψ x (basisVec i) * f x)
  have hr : (∫ x : HilbertTwo, (ψ ∘ coordinateHilbertEquiv) x * coordinateL2Equiv g x) =
      ∫ x : Vec 2, ψ x * g x := by
    calc
      _ = ∫ x : HilbertTwo, ψ (WithLp.ofLp x) * g (WithLp.ofLp x) := by
        apply integral_congr_ae
        filter_upwards [coordinateL2Equiv_ae g] with x hx
        rw [hx]
        rfl
      _ = _ := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
        coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
        (fun x : Vec 2 => ψ x * g x)
  rw [hl, hr] at ht
  exact ht

/-- Taking real parts yields the source weak derivative, with integrability proved from L². -/
theorem hasWeakPartialDerivOn_re_of_distribution
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) :
    HasWeakPartialDerivOn Set.univ i (fun x => (f x).re) (fun x => (g x).re) := by
  intro φ hs hc _
  let ψ : Vec 2 → ℂ := fun x => (φ x : ℂ)
  have hsψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hs
  have hcψ : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
  have hD (x : Vec 2) : fderiv ℝ ψ x (basisVec i) = (fderiv ℝ φ x (basisVec i) : ℂ) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x
      ((hs.differentiable (by simp)).differentiableAt.hasFDerivAt)
    exact congrArg (fun A : Vec 2 →L[ℝ] ℂ => A (basisVec i)) h.fderiv
  have hmψ : MemLp ψ 2 (volume : Measure (Vec 2)) :=
    hsψ.continuous.memLp_of_hasCompactSupport hcψ
  have hmD : MemLp (fun x => fderiv ℝ ψ x (basisVec i)) 2 (volume : Measure (Vec 2)) :=
    ((hsψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcψ.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have h := congrArg Complex.re (coordinate_compact_test_identity f g i hfg ψ hsψ hcψ)
  have hl := integral_re (hmD.integrable_mul (Lp.memLp f))
  have hr := integral_re (hmψ.integrable_mul (Lp.memLp g))
  change (∫ x, (fderiv ℝ ψ x (basisVec i) * f x).re) =
    (∫ x, fderiv ℝ ψ x (basisVec i) * f x).re at hl
  change (∫ x, (ψ x * g x).re) = (∫ x, ψ x * g x).re at hr
  rw [← hl, Complex.neg_re, ← hr] at h
  simp only [hD, ψ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  simpa only [Measure.restrict_univ, mul_comm] using h

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Recover the literal frequency product from an equality of actual L²
tempered distributions. Local integrability suffices for the unbounded
frequency product; its L² representative is supplied by the equality. -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem frequency_product_ae_of_toTemperedDistribution
    (f g : Lp ℂ 2 (volume : Measure V)) (v : V)
    (hfg : (g : 𝓢'(V, ℂ)) = (2 * (Real.pi : ℂ) * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ (fun x => (inner ℝ x v : ℂ)) (f : 𝓢'(V, ℂ))) :
    g =ᵐ[volume] fun x => (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x v : ℂ) * f x := by
  have hf : LocallyIntegrable (fun x =>
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x v : ℂ) * f x) :=
    LocallyIntegrable.continuous_mul (by fun_prop) ((Lp.memLp f).locallyIntegrable (by norm_num))
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp g).locallyIntegrable (by norm_num)) hf
  intro φ hs hc
  let ψ : V → ℂ := fun x => (φ x : ℂ)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hs
  have hcψ : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
  have hgrowth : (fun x : V => (inner ℝ x v : ℂ)).HasTemperateGrowth := by fun_prop
  have h := congrArg (fun T : 𝓢'(V, ℂ) => T (hcψ.toSchwartzMap hψ)) hfg
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply hgrowth,
    smul_eq_mul] at h
  change (∫ x, ψ x * g x) = (2 * (Real.pi : ℂ) * Complex.I) *
    (∫ x, ((inner ℝ x v : ℂ) * ψ x) * f x) at h
  rw [← integral_const_mul] at h
  simp only [Complex.real_smul]
  change (∫ x, ψ x * g x) = _
  rw [h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only [ψ]; ring

end AVRegularity.CoupledEnergyPlane.Fourier
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Scalar spatial operators commute with every constant finite Hilbert fiber map. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {μ : Measure (Vec 2)}

/-- Synthesize a scalar spatial field along any constant fiber vector. -/
def vectorInjection (e : E) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLpL 2 μ

omit [FiniteDimensional ℝ F] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem fiberCoordinate_vectorInjection (e : E) (f : Lp ℝ 2 μ)
    (k : Fin (Module.finrank ℝ E)) :
    fiberCoordinate k (vectorInjection e f) = inner ℝ (stdOrthonormalBasis ℝ E k) e • f := by
  apply Lp.ext
  filter_upwards [fiberCoordinate_ae k (vectorInjection e f),
    ContinuousLinearMap.coeFn_compLpL ((ContinuousLinearMap.id ℝ ℝ).smulRight e) f,
    Lp.coeFn_smul (inner ℝ (stdOrthonormalBasis ℝ E k) e) f] with x hx hv hs
  change vectorInjection e f x = f x • e at hv
  rw [hx, hv, hs]
  simp [real_inner_smul_right, mul_comm]

omit [FiniteDimensional ℝ F] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem hilbertLift_vectorInjection (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (e : E) (f : Lp ℝ 2 μ) :
    hilbertLift T (vectorInjection e f) = vectorInjection e (T f) := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertLift_coordinate, fiberCoordinate_vectorInjection, map_smul]

omit [FiniteDimensional ℝ F] in
theorem fiberMap_injection (L : E →L[ℝ] F) (k : Fin (Module.finrank ℝ E))
    (f : Lp ℝ 2 μ) :
    L.compLpL 2 μ (fiberInjection k f) = vectorInjection (L (stdOrthonormalBasis ℝ E k)) f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L (fiberInjection k f),
    fiberInjection_ae k f,
    ContinuousLinearMap.coeFn_compLpL
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (L (stdOrthonormalBasis ℝ E k))) f]
      with x hL hk hv
  change vectorInjection (L (stdOrthonormalBasis ℝ E k)) f x =
    f x • L (stdOrthonormalBasis ℝ E k) at hv
  rw [hL, hk, hv]
  simp

theorem hilbertLift_fiberMap (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (L : E →L[ℝ] F) (u : Lp E 2 μ) :
    hilbertLift T (L.compLpL 2 μ u) = L.compLpL 2 μ (hilbertLift T u) := by
  have hu := hilbertLift_id u
  unfold hilbertLift at hu
  simp only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu
  conv_lhs => rw [← hu]
  simp only [map_sum, fiberMap_injection, hilbertLift_vectorInjection]
  simp only [hilbertLift, sum_apply, ContinuousLinearMap.comp_apply, map_sum, fiberMap_injection]

end AVRegularity.CoupledEnergyPlane.Fourier
end
end
