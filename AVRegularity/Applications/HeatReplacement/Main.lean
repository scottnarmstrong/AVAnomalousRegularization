-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import AVRegularity.Applications.Parabolic.SliceGrad
import Homogenization.Sobolev.H1.BasicLemmas
import AVRegularity.External.Campanato.Representative

section
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace AVRegularity.Applications.HeatReplacement

/-! # The Hilbert space `L²(ν)³`

`toX u hu` packages a triple `u : α → Fin 3 → ℝ` of `L²(ν)` functions as an element of
`PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 ν)`; its inner product is the integral of the coordinatewise
product. -/

variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α}

/-- The ambient Hilbert space `L²(ν)³`. -/
abbrev Tri (ν : Measure α) := PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 ν)

/-- Package three `L²` functions as an element of `L²(ν)³`. -/
def toX (u : α → Fin 3 → ℝ) (hu : ∀ c, MemLp (fun p => u p c) 2 ν) : Tri ν :=
  WithLp.toLp 2 (fun c => (hu c).toLp (fun p => u p c))

theorem toX_apply (u : α → Fin 3 → ℝ) (hu : ∀ c, MemLp (fun p => u p c) 2 ν) (c : Fin 3) :
    toX u hu c = (hu c).toLp (fun p => u p c) := rfl

theorem toX_coeFn (u : α → Fin 3 → ℝ) (hu : ∀ c, MemLp (fun p => u p c) 2 ν) (c : Fin 3) :
    (toX u hu c : α → ℝ) =ᵐ[ν] fun p => u p c :=
  (hu c).coeFn_toLp

theorem toX_add (w u v : α → Fin 3 → ℝ) (hw : ∀ c, MemLp (fun p => w p c) 2 ν)
    (hu : ∀ c, MemLp (fun p => u p c) 2 ν) (hv : ∀ c, MemLp (fun p => v p c) 2 ν)
    (h : ∀ p c, w p c = u p c + v p c) :
    toX w hw = toX u hu + toX v hv := by
  refine PiLp.ext fun c => ?_
  rw [PiLp.add_apply, toX_apply, toX_apply, toX_apply, ← MemLp.toLp_add (hu c) (hv c)]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun p => h p c)

theorem toX_smul (r : ℝ) (w u : α → Fin 3 → ℝ) (hw : ∀ c, MemLp (fun p => w p c) 2 ν)
    (hu : ∀ c, MemLp (fun p => u p c) 2 ν) (h : ∀ p c, w p c = r * u p c) :
    toX w hw = r • toX u hu := by
  refine PiLp.ext fun c => ?_
  rw [PiLp.smul_apply, toX_apply, toX_apply, ← MemLp.toLp_const_smul r (hu c)]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun p => h p c)

theorem inner_Lp_real {f g : Lp ℝ 2 ν} :
    ⟪f, g⟫_ℝ = ∫ p, (f : α → ℝ) p * (g : α → ℝ) p ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_comm]

theorem inner_toX (u v : α → Fin 3 → ℝ) (hu : ∀ c, MemLp (fun p => u p c) 2 ν)
    (hv : ∀ c, MemLp (fun p => v p c) 2 ν) :
    ⟪toX u hu, toX v hv⟫_ℝ = ∫ p, ∑ c, u p c * v p c ∂ν := by
  rw [PiLp.inner_apply]
  have hint : ∀ c, Integrable (fun p => u p c * v p c) ν := fun c => (hu c).integrable_mul (hv c)
  rw [integral_finsetSum _ (fun c _ => hint c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [toX_apply, toX_apply, inner_Lp_real]
  refine integral_congr_ae ?_
  filter_upwards [(hu c).coeFn_toLp, (hv c).coeFn_toLp] with p h1 h2
  rw [h1, h2]

theorem inner_Tri_toX (z : Tri ν) (v : α → Fin 3 → ℝ) (hv : ∀ c, MemLp (fun p => v p c) 2 ν) :
    ⟪z, toX v hv⟫_ℝ = ∫ p, ∑ c, (z c : α → ℝ) p * v p c ∂ν := by
  rw [PiLp.inner_apply]
  have hint : ∀ c, Integrable (fun p => (z c : α → ℝ) p * v p c) ν :=
    fun c => (Lp.memLp (z c)).integrable_mul (hv c)
  rw [integral_finsetSum _ (fun c _ => hint c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [toX_apply, inner_Lp_real]
  refine integral_congr_ae ?_
  filter_upwards [(hv c).coeFn_toLp] with p h2
  rw [h2]

theorem norm_sq_toX (u : α → Fin 3 → ℝ) (hu : ∀ c, MemLp (fun p => u p c) 2 ν) :
    ‖toX u hu‖ ^ 2 = ∫ p, ∑ c, u p c * u p c ∂ν := by
  rw [← real_inner_self_eq_norm_sq, inner_toX]

end AVRegularity.Applications.HeatReplacement
end
end
end

section
public section
open scoped InnerProductSpace
namespace AVRegularity.Applications.HeatReplacement

/-! # Lions representation (abstract Hilbert-space form)

If `J` and `T` are linear maps into a real
Hilbert space and `⟪J φ, T φ⟫` controls `‖J φ‖²`, every functional `φ ↦ ⟪f, J φ⟫` is represented as
`φ ↦ ⟪z, T φ⟫` by an element `z` in the closure of the range of `J`, with `‖z‖ ≤ ‖f‖ / α`. -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Lions representation theorem**, with the norm bound. -/
theorem lions_representation_with_norm_bound (J T : V →ₗ[ℝ] X) {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ φ, α * ‖J φ‖ ^ 2 ≤ ⟪J φ, T φ⟫_ℝ) (f : X) :
    ∃ z ∈ (LinearMap.range J).topologicalClosure,
      (∀ φ, ⟪z, T φ⟫_ℝ = ⟪f, J φ⟫_ℝ) ∧ ‖z‖ ≤ ‖f‖ / α := by
  set K := (LinearMap.range J).topologicalClosure with hK
  have hKc : IsClosed (K : Set X) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace K := hKc.completeSpace_coe
  let P : X →L[ℝ] X := K.starProjection
  let T' : V →ₗ[ℝ] X := P.toLinearMap ∘ₗ T
  have hJK : ∀ φ, J φ ∈ K := fun φ =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self J φ)
  -- Coercivity survives the orthogonal projection.
  have hinner : ∀ φ, ⟪J φ, T' φ⟫_ℝ = ⟪J φ, T φ⟫_ℝ := by
    intro φ
    change ⟪J φ, K.starProjection (T φ)⟫_ℝ = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (hJK φ)]
  have hlow : ∀ φ, α * ‖J φ‖ ≤ ‖T' φ‖ := by
    intro φ
    have h1 := hcoer φ
    rw [← hinner] at h1
    have h2 := real_inner_le_norm (J φ) (T' φ)
    rcases eq_or_lt_of_le (norm_nonneg (J φ)) with h0 | hpos
    · rw [← h0]; simp
    · have hmul : α * ‖J φ‖ ^ 2 ≤ ‖J φ‖ * ‖T' φ‖ := h1.trans h2
      nlinarith
  -- The functional on the range of `T'`.
  let L : V →ₗ[ℝ] ℝ := (innerₛₗ ℝ f).comp J
  have hker : LinearMap.ker T' ≤ LinearMap.ker L := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hlow φ
    rw [hφ, norm_zero] at h
    have hJ : ‖J φ‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (J φ)]) (norm_nonneg _)
    simp [L, norm_eq_zero.1 hJ]
  let ℓ₀ : LinearMap.range T' →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T').liftQ L hker).comp T'.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ φ, ℓ₀ ⟨T' φ, LinearMap.mem_range_self T' φ⟩ = L φ := by
    intro φ
    have hquot : T'.quotKerEquivRange.symm ⟨T' φ, LinearMap.mem_range_self T' φ⟩ =
        Submodule.Quotient.mk φ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ℓ₀, LinearMap.comp_apply, LinearEquiv.coe_coe, hquot, Submodule.liftQ_apply]
  have hbound : ∀ y : LinearMap.range T', ‖ℓ₀ y‖ ≤ (‖f‖ / α) * ‖y‖ := by
    rintro ⟨y, φ, rfl⟩
    rw [hℓ₀ φ]
    have h1 : ‖L φ‖ ≤ ‖f‖ * ‖J φ‖ := by
      change |⟪f, J φ⟫_ℝ| ≤ _
      exact abs_real_inner_le_norm f (J φ)
    have h2 : ‖J φ‖ ≤ ‖T' φ‖ / α := by
      rw [le_div_iff₀ hα, mul_comm]
      exact hlow φ
    calc
      ‖L φ‖ ≤ ‖f‖ * ‖J φ‖ := h1
      _ ≤ ‖f‖ * (‖T' φ‖ / α) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (‖f‖ / α) * ‖(⟨T' φ, LinearMap.mem_range_self T' φ⟩ : LinearMap.range T')‖ := by
        rw [show ‖(⟨T' φ, LinearMap.mem_range_self T' φ⟩ : LinearMap.range T')‖ = ‖T' φ‖
          from rfl]
        ring
  let ℓ : StrongDual ℝ (LinearMap.range T') := ℓ₀.mkContinuous (‖f‖ / α) hbound
  obtain ⟨ℓ', hℓ', hℓ'norm⟩ := exists_extension_norm_eq (LinearMap.range T') ℓ
  let z₀ : X := (InnerProductSpace.toDual ℝ X).symm ℓ'
  refine ⟨P z₀, ?_, ?_, ?_⟩
  · change K.starProjection z₀ ∈ K
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  · intro φ
    have h1 : ⟪P z₀, T φ⟫_ℝ = ⟪z₀, T' φ⟫_ℝ := by
      change ⟪K.starProjection z₀, T φ⟫_ℝ = ⟪z₀, K.starProjection (T φ)⟫_ℝ
      exact Submodule.inner_starProjection_left_eq_right K z₀ (T φ)
    rw [h1, InnerProductSpace.toDual_symm_apply]
    have h2 := hℓ' ⟨T' φ, LinearMap.mem_range_self T' φ⟩
    simp only at h2
    rw [h2]
    change ℓ₀ ⟨T' φ, LinearMap.mem_range_self T' φ⟩ = _
    rw [hℓ₀ φ]
    simp [L]
  · calc
      ‖P z₀‖ ≤ ‖z₀‖ := K.norm_starProjection_apply_le z₀
      _ = ‖ℓ'‖ := by
        dsimp [z₀]
        exact (InnerProductSpace.toDual ℝ X).symm.norm_map ℓ'
      _ = ‖ℓ‖ := hℓ'norm
      _ ≤ ‖f‖ / α := by
        dsimp [ℓ]
        exact LinearMap.mkContinuous_norm_le _ (div_nonneg (norm_nonneg _) hα.le) hbound

end AVRegularity.Applications.HeatReplacement
end
end

section
public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.HeatReplacement

/-! # `L²`-limits of weak partial derivatives, and a.e. subsequences

* `sq_integral_mul_le`: the Cauchy–Schwarz inequality `(∫ f g)² ≤ (∫ f²)(∫ g²)`.
* `hasWeakPartialDerivOn_of_L2_limit`: if continuous functions with weak partial derivatives
  converge in `L²(U)` together with their derivatives, the limit has the limiting weak derivative.
* `exists_subseq_ae_tendsto_zero`: nonnegative integrable functions with integrals tending to zero
  have an a.e. null subsequence. -/

/-- Cauchy–Schwarz for `L²` functions. -/
theorem sq_integral_mul_le {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  have hf2 : Integrable (fun x => f x ^ 2) ν := hf.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) ν := hg.integrable_sq
  have hfg : Integrable (fun x => f x * g x) ν := hf.integrable_mul hg
  have key : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂ν) * (t * t) + 2 * (∫ x, f x * g x ∂ν) * t
      + ∫ x, g x ^ 2 ∂ν := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * f x + g x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have h1 : ∫ x, (t * f x + g x) ^ 2 ∂ν
        = (∫ x, f x ^ 2 ∂ν) * (t * t) + 2 * (∫ x, f x * g x ∂ν) * t + ∫ x, g x ^ 2 ∂ν := by
      have : (fun x => (t * f x + g x) ^ 2)
          = fun x => (t * t) * f x ^ 2 + (2 * t) * (f x * g x) + g x ^ 2 := by
        funext x; ring
      have iA : Integrable (fun x => t * t * f x ^ 2) ν := hf2.const_mul _
      have iB : Integrable (fun x => 2 * t * (f x * g x)) ν := hfg.const_mul _
      have e1 := integral_add (μ := ν) (f := fun x => t * t * f x ^ 2 + 2 * t * (f x * g x))
        (g := fun x => g x ^ 2) (iA.add iB) hg2
      have e2 := integral_add (μ := ν) (f := fun x => t * t * f x ^ 2)
        (g := fun x => 2 * t * (f x * g x)) iA iB
      rw [this]
      rw [e1, e2, integral_const_mul, integral_const_mul]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem abs_integral_mul_le {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    |∫ x, f x * g x ∂ν| ≤ Real.sqrt ((∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν) :=
  Real.abs_le_sqrt (sq_integral_mul_le hf hg)

/-- If `∫ f_n² → 0` then `∫ f_n g → 0` for fixed `g ∈ L²`. -/
theorem tendsto_integral_mul_of_sq {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν)
    (h0 : Tendsto (fun n => ∫ x, f n x ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * g x ∂ν) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt ((∫ x, f n x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν)) atTop (𝓝 0) := by
    have := (h0.mul_const (∫ x, g x ^ 2 ∂ν)).sqrt
    simpa using this
  exact squeeze_zero_norm (fun n => abs_integral_mul_le (hf n) hg) hs

/-- `L²(U)`-limits of continuous functions with weak partial derivatives. -/
theorem hasWeakPartialDerivOn_of_L2_limit {U : Set (Vec 2)} (i : Fin 2)
    {u d : Vec 2 → ℝ} {un dn : ℕ → Vec 2 → ℝ}
    (hun : ∀ n, HasWeakPartialDerivOn U i (un n) (dn n))
    (hunc : ∀ n, Continuous (un n)) (hdnc : ∀ n, Continuous (dn n))
    (hu : ∀ n, MemLp (fun y => un n y - u y) 2 (volume.restrict U))
    (hd : ∀ n, MemLp (fun y => dn n y - d y) 2 (volume.restrict U))
    (hu0 : Tendsto (fun n => ∫ y in U, (un n y - u y) ^ 2) atTop (𝓝 0))
    (hd0 : Tendsto (fun n => ∫ y in U, (dn n y - d y) ^ 2) atTop (𝓝 0)) :
    HasWeakPartialDerivOn U i u d := by
  intro φ hφ hφc hφU
  have hφcont : Continuous φ := hφ.continuous
  have hψc : Continuous fun y => fderiv ℝ φ y (basisVec i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψs : HasCompactSupport fun y => fderiv ℝ φ y (basisVec i) :=
    hφc.fderiv_apply (𝕜 := ℝ) _
  set ψ : Vec 2 → ℝ := fun y => fderiv ℝ φ y (basisVec i) with hψdef
  have hψL : MemLp ψ 2 (volume.restrict U) := hψc.memLp_of_hasCompactSupport hψs
  have hφL : MemLp φ 2 (volume.restrict U) := hφcont.memLp_of_hasCompactSupport hφc
  have hA := tendsto_integral_mul_of_sq hu hψL hu0
  have hB := tendsto_integral_mul_of_sq hd hφL hd0
  -- integrability of the smooth pieces
  have iuψ : ∀ n, Integrable (fun y => un n y * ψ y) (volume.restrict U) := fun n =>
    ((hunc n).mul hψc).integrable_of_hasCompactSupport hψs.mul_left
  have idφ : ∀ n, Integrable (fun y => dn n y * φ y) (volume.restrict U) := fun n =>
    ((hdnc n).mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have iuψ' : Integrable (fun y => u y * ψ y) (volume.restrict U) := by
    have h1 := (hu 0).integrable_mul hψL
    have := (iuψ 0).sub h1
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]; ring
  have idφ' : Integrable (fun y => d y * φ y) (volume.restrict U) := by
    have h1 := (hd 0).integrable_mul hφL
    have := (idφ 0).sub h1
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]; ring
  have hlim : Tendsto (fun n => (∫ y in U, (un n y - u y) * ψ y)
      + ∫ y in U, (dn n y - d y) * φ y) atTop (𝓝 0) := by
    simpa using hA.add hB
  have hconst : ∀ n, (∫ y in U, (un n y - u y) * ψ y) + ∫ y in U, (dn n y - d y) * φ y
      = -((∫ y in U, u y * ψ y) + ∫ y in U, d y * φ y) := by
    intro n
    have e1 : ∫ y in U, (un n y - u y) * ψ y
        = (∫ y in U, un n y * ψ y) - ∫ y in U, u y * ψ y := by
      rw [← integral_sub (iuψ n) iuψ']
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only; ring
    have e2 : ∫ y in U, (dn n y - d y) * φ y
        = (∫ y in U, dn n y * φ y) - ∫ y in U, d y * φ y := by
      rw [← integral_sub (idφ n) idφ']
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only; ring
    have := hun n φ hφ hφc hφU
    rw [e1, e2]
    simp only [hψdef] at this ⊢
    linarith
  have hlim' : Tendsto (fun _ : ℕ => -((∫ y in U, u y * ψ y) + ∫ y in U, d y * φ y)) atTop
      (𝓝 0) := by
    refine hlim.congr fun n => hconst n
  have h0 : -((∫ y in U, u y * ψ y) + ∫ y in U, d y * φ y) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim'
  simp only [hψdef] at h0 ⊢
  linarith

/-- Nonnegative integrable functions with integrals tending to zero have an a.e. null
subsequence. -/
theorem exists_subseq_ae_tendsto_zero {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {H : ℕ → α → ℝ} (hint : ∀ n, Integrable (H n) ν) (hnn : ∀ n x, 0 ≤ H n x)
    (h0 : Tendsto (fun n => ∫ x, H n x ∂ν) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂ν, Tendsto (fun k => H (s k) x) atTop (𝓝 0) := by
  have hmeas : TendstoInMeasure ν H atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    have : ∀ n, eLpNorm (H n - fun _ => (0 : ℝ)) 1 ν = ENNReal.ofReal (∫ x, H n x ∂ν) := by
      intro n
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [Pi.sub_apply, sub_zero]
      rw [ofReal_integral_eq_lintegral_ofReal (hint n) (Filter.Eventually.of_forall (hnn n))]
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal (hnn n x)]
      exact (hint n).aestronglyMeasurable.sub aestronglyMeasurable_const
    simp_rw [this]
    simpa using (ENNReal.tendsto_ofReal h0)
  obtain ⟨s, hs, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨s, hs, hae⟩

end AVRegularity.Applications.HeatReplacement
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.HeatReplacement

/-! # Test functions, jets and the maps `J`, `T` of the heat replacement

On the cylinder `Ω = (a,b) × B` with measure `μ = vol|_Ω` we use the smooth, compactly supported
test functions `φ` that vanish on the top slice `τ = b`. For such `φ`
* `J φ = (g φ, g ∂₁φ, g ∂₂φ)` with the weight `g(τ) = exp (τ - b)`,
* `T φ = (-∂τ φ, ∂₁φ, ∂₂φ)`,
both packaged in `L²(μ)³`. -/

/-- The cylinder `Ω = (a,b) × B`. -/
def Om (a b : ℝ) (B : Set (Vec 2)) : Set (ℝ × Vec 2) := Set.Ioo a b ×ˢ B

/-- The measure `vol|_Ω`. -/
abbrev mu (a b : ℝ) (B : Set (Vec 2)) : Measure (ℝ × Vec 2) := volume.restrict (Om a b B)

/-- The spatial partial derivative `∂ᵢφ`. -/
def partX (φ : ℝ × Vec 2 → ℝ) (i : Fin 2) (p : ℝ × Vec 2) : ℝ :=
  fderiv ℝ φ p (0, basisVec i)

/-- The weight `g(τ) = exp (τ - b)`. -/
def wt (b τ : ℝ) : ℝ := Real.exp (τ - b)

/-- The jet `(φ, ∂₁φ, ∂₂φ)`. -/
def jet (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : Fin 3 → ℝ :=
  ![φ p, partX φ 0 p, partX φ 1 p]

/-- The weighted jet `g · (φ, ∂₁φ, ∂₂φ)`. -/
def wjet (b : ℝ) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : Fin 3 → ℝ :=
  wt b p.1 • jet φ p

/-- The triple `(-∂τφ, ∂₁φ, ∂₂φ)`. -/
def tjet (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : Fin 3 → ℝ :=
  ![-stTimeDeriv φ p, partX φ 0 p, partX φ 1 p]

/-- The test class: smooth, compactly supported, vanishing on the top slice `τ = b`. -/
def testSub (b : ℝ) : Submodule ℝ (ℝ × Vec 2 → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ ∀ y, φ (b, y) = 0}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    exact ⟨h1.add k1, h2.add k2, fun y => by simp [h3 y, k3 y]⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun y => rfl⟩
  smul_mem' := by
    rintro r φ ⟨h1, h2, h3⟩
    exact ⟨contDiff_const.smul h1, h2.smul_left, fun y => by simp [h3 y]⟩

section Lemmas

variable {b : ℝ}

theorem testSub_diff {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) : Differentiable ℝ φ :=
  h.1.differentiable (by simp)

theorem testSub_cont_fderiv {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    Continuous (fderiv ℝ φ) := h.1.continuous_fderiv (by simp)

theorem continuous_partX {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (i : Fin 2) :
    Continuous (partX φ i) :=
  (testSub_cont_fderiv h).clm_apply continuous_const

theorem continuous_stTimeDeriv {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    Continuous (stTimeDeriv φ) :=
  (testSub_cont_fderiv h).clm_apply continuous_const

theorem hasCompactSupport_partX {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (i : Fin 2) :
    HasCompactSupport (partX φ i) := h.2.1.fderiv_apply (𝕜 := ℝ) _

theorem hasCompactSupport_stTimeDeriv {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    HasCompactSupport (stTimeDeriv φ) := h.2.1.fderiv_apply (𝕜 := ℝ) _

theorem memLp_of_cs {ν : Measure (ℝ × Vec 2)} [IsFiniteMeasureOnCompacts ν]
    {h : ℝ × Vec 2 → ℝ} (hc : Continuous h) (hs : HasCompactSupport h) : MemLp h 2 ν :=
  hc.memLp_of_hasCompactSupport hs

theorem continuous_wt (b : ℝ) : Continuous (fun p : ℝ × Vec 2 => wt b p.1) :=
  Real.continuous_exp.comp (continuous_fst.sub continuous_const)

theorem memLp_wjet {a b : ℝ} {B : Set (Vec 2)} {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    ∀ c, MemLp (fun p => wjet b φ p c) 2 (mu a b B) := by
  intro c
  have hφ : Continuous φ := h.1.continuous
  fin_cases c
  · exact memLp_of_cs ((continuous_wt b).mul hφ) h.2.1.mul_left
  · exact memLp_of_cs ((continuous_wt b).mul (continuous_partX h 0))
      (hasCompactSupport_partX h 0).mul_left
  · exact memLp_of_cs ((continuous_wt b).mul (continuous_partX h 1))
      (hasCompactSupport_partX h 1).mul_left

theorem memLp_tjet {a b : ℝ} {B : Set (Vec 2)} {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    ∀ c, MemLp (fun p => tjet φ p c) 2 (mu a b B) := by
  intro c
  fin_cases c
  · exact memLp_of_cs (continuous_stTimeDeriv h).neg (hasCompactSupport_stTimeDeriv h).neg
  · exact memLp_of_cs (continuous_partX h 0) (hasCompactSupport_partX h 0)
  · exact memLp_of_cs (continuous_partX h 1) (hasCompactSupport_partX h 1)

theorem partX_add {φ ψ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) (hψ : ψ ∈ testSub b) (i : Fin 2) :
    partX (φ + ψ) i = partX φ i + partX ψ i := by
  funext p
  simp only [partX, Pi.add_apply]
  rw [fderiv_add (testSub_diff hφ p) (testSub_diff hψ p)]
  rfl

theorem partX_smul (r : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) (i : Fin 2) :
    partX (r • φ) i = r • partX φ i := by
  funext p
  simp only [partX, Pi.smul_apply]
  rw [fderiv_const_smul (testSub_diff hφ p)]
  rfl

theorem stTimeDeriv_add {φ ψ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) (hψ : ψ ∈ testSub b) :
    stTimeDeriv (φ + ψ) = stTimeDeriv φ + stTimeDeriv ψ := by
  funext p
  simp only [stTimeDeriv, Pi.add_apply]
  rw [fderiv_add (testSub_diff hφ p) (testSub_diff hψ p)]
  rfl

theorem stTimeDeriv_smul (r : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) :
    stTimeDeriv (r • φ) = r • stTimeDeriv φ := by
  funext p
  simp only [stTimeDeriv, Pi.smul_apply]
  rw [fderiv_const_smul (testSub_diff hφ p)]
  rfl

theorem wjet_add {φ ψ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) (hψ : ψ ∈ testSub b) :
    wjet b (φ + ψ) = wjet b φ + wjet b ψ := by
  funext p c
  fin_cases c <;> simp [wjet, jet, partX_add hφ hψ, mul_add]

theorem wjet_smul (r : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) :
    wjet b (r • φ) = r • wjet b φ := by
  funext p c
  fin_cases c <;> simp [wjet, jet, partX_smul r hφ, mul_left_comm]

theorem tjet_add {φ ψ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) (hψ : ψ ∈ testSub b) :
    tjet (φ + ψ) = tjet φ + tjet ψ := by
  funext p c
  fin_cases c <;> simp [tjet, stTimeDeriv_add hφ hψ, partX_add hφ hψ]
  ring

theorem tjet_smul (r : ℝ) {φ : ℝ × Vec 2 → ℝ} (hφ : φ ∈ testSub b) :
    tjet (r • φ) = r • tjet φ := by
  funext p c
  fin_cases c <;> simp [tjet, stTimeDeriv_smul r hφ, partX_smul r hφ]

end Lemmas

/-- The map `J φ = g (φ, ∇φ)`. -/
def Jmap (a b : ℝ) (B : Set (Vec 2)) : testSub b →ₗ[ℝ] Tri (mu a b B) where
  toFun φ := toX (wjet b φ.1) (memLp_wjet φ.2)
  map_add' φ ψ :=
    toX_add _ _ _ _ (memLp_wjet φ.2) (memLp_wjet ψ.2) (fun p c => by
      rw [Submodule.coe_add, wjet_add φ.2 ψ.2]; rfl)
  map_smul' r φ :=
    toX_smul r _ _ _ (memLp_wjet φ.2) (fun p c => by
      rw [Submodule.coe_smul, wjet_smul r φ.2]; rfl)

/-- The map `T φ = (-∂τφ, ∇φ)`. -/
def Tmap (a b : ℝ) (B : Set (Vec 2)) : testSub b →ₗ[ℝ] Tri (mu a b B) where
  toFun φ := toX (tjet φ.1) (memLp_tjet φ.2)
  map_add' φ ψ :=
    toX_add _ _ _ _ (memLp_tjet φ.2) (memLp_tjet ψ.2) (fun p c => by
      rw [Submodule.coe_add, tjet_add φ.2 ψ.2]; rfl)
  map_smul' r φ :=
    toX_smul r _ _ _ (memLp_tjet φ.2) (fun p c => by
      rw [Submodule.coe_smul, tjet_smul r φ.2]; rfl)

end AVRegularity.Applications.HeatReplacement
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open scoped InnerProductSpace
namespace AVRegularity.Applications.HeatReplacement

/-! # Coercivity of the pair `(J, T)`

For `φ` in the test class (vanishing on the top slice `τ = b`),
`(1/2) ‖J φ‖² ≤ ⟪J φ, T φ⟫`. The only non-pointwise ingredient is
`∫_Ω (-g φ ∂τφ - (1/2) g φ²) ≥ 0`, obtained from the fundamental theorem of calculus in `τ`. -/

variable {a b : ℝ} {B : Set (Vec 2)}

/-- The time-derivative term, `-(g φ ∂τφ) - (1/2) g φ²`. -/
def timeTerm (b : ℝ) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -(wt b p.1 * φ p * stTimeDeriv φ p) - 1 / 2 * wt b p.1 * φ p ^ 2

theorem hasDerivAt_slice {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (y : Vec 2) (τ : ℝ) :
    HasDerivAt (fun s => φ (s, y)) (stTimeDeriv φ (τ, y)) τ := by
  have h1 : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : Vec 2)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (testSub_diff h (τ, y)).hasFDerivAt.comp_hasDerivAt τ h1

theorem hasDerivAt_wt (b τ : ℝ) : HasDerivAt (wt b) (wt b τ) τ := by
  have : HasDerivAt (fun s => s - b) 1 τ := (hasDerivAt_id τ).sub_const b
  have h2 := this.exp
  rw [mul_one] at h2
  exact h2

theorem integral_time_slice {φ : ℝ × Vec 2 → ℝ} (hab : a < b) (h : φ ∈ testSub b) (y : Vec 2) :
    0 ≤ ∫ τ in Set.Ioo a b, timeTerm b φ (τ, y) := by
  have hderiv : ∀ τ ∈ Set.uIcc a b, HasDerivAt (fun s => wt b s * φ (s, y) ^ 2)
      (wt b τ * φ (τ, y) ^ 2 + wt b τ * (2 * φ (τ, y) * stTimeDeriv φ (τ, y))) τ := by
    intro τ _
    have h2 := (hasDerivAt_slice h y τ).pow 2
    have h3 := (hasDerivAt_wt b τ).mul h2
    convert h3 using 1
    simp
  have hcont : Continuous fun τ : ℝ =>
      wt b τ * φ (τ, y) ^ 2 + wt b τ * (2 * φ (τ, y) * stTimeDeriv φ (τ, y)) := by
    have hw : Continuous (wt b) := Real.continuous_exp.comp (continuous_id.sub continuous_const)
    have hφ : Continuous fun τ : ℝ => φ (τ, y) :=
      h.1.continuous.comp (continuous_id.prodMk continuous_const)
    have hd : Continuous fun τ : ℝ => stTimeDeriv φ (τ, y) :=
      (continuous_stTimeDeriv h).comp (continuous_id.prodMk continuous_const)
    exact (hw.mul (hφ.pow 2)).add (hw.mul ((continuous_const.mul hφ).mul hd))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable a b)
  have hEq : ∀ τ, timeTerm b φ (τ, y) =
      -(1 / 2) * (wt b τ * φ (τ, y) ^ 2 + wt b τ * (2 * φ (τ, y) * stTimeDeriv φ (τ, y))) := by
    intro τ; simp only [timeTerm]; ring
  simp_rw [hEq]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_const_mul, hftc, h.2.2 y]
  have : 0 ≤ wt b a := (Real.exp_pos _).le
  norm_num
  nlinarith [sq_nonneg (φ (a, y)), mul_nonneg this (sq_nonneg (φ (a, y)))]

theorem timeTerm_eq (b : ℝ) (φ : ℝ × Vec 2 → ℝ) :
    timeTerm b φ = fun p => φ p * (-(wt b p.1 * stTimeDeriv φ p) - 1 / 2 * wt b p.1 * φ p) := by
  funext p; simp only [timeTerm]; ring

theorem integrable_timeTerm (a b : ℝ) (B : Set (Vec 2)) {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) :
    Integrable (timeTerm b φ) (mu a b B) := by
  rw [timeTerm_eq]
  have hc : Continuous fun p : ℝ × Vec 2 =>
      φ p * (-(wt b p.1 * stTimeDeriv φ p) - 1 / 2 * wt b p.1 * φ p) :=
    h.1.continuous.mul (((continuous_wt b).mul (continuous_stTimeDeriv h)).neg.sub
      ((continuous_const.mul (continuous_wt b)).mul h.1.continuous))
  exact hc.integrable_of_hasCompactSupport h.2.1.mul_right

theorem volume_restrict_Om (a b : ℝ) (B : Set (Vec 2)) :
    mu a b B = (volume.restrict (Set.Ioo a b)).prod (volume.restrict B) := by
  show volume.restrict (Set.Ioo a b ×ˢ B) = _
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem integral_timeTerm_nonneg {φ : ℝ × Vec 2 → ℝ} (hab : a < b) (h : φ ∈ testSub b) :
    0 ≤ ∫ p in Om a b B, timeTerm b φ p := by
  have hint := integrable_timeTerm a b B h
  have e : ∫ p in Om a b B, timeTerm b φ p
      = ∫ y in B, ∫ τ in Set.Ioo a b, timeTerm b φ (τ, y) := by
    change ∫ p, timeTerm b φ p ∂(mu a b B) = _
    rw [volume_restrict_Om] at hint ⊢
    exact integral_prod_symm _ hint
  rw [e]
  exact integral_nonneg fun y => integral_time_slice hab h y

theorem integrable_sum_mul {ν : Measure (ℝ × Vec 2)} {u v : ℝ × Vec 2 → Fin 3 → ℝ}
    (hu : ∀ c, MemLp (fun p => u p c) 2 ν) (hv : ∀ c, MemLp (fun p => v p c) 2 ν) :
    Integrable (fun p => ∑ c, u p c * v p c) ν :=
  integrable_finsetSum _ fun c _ => (hu c).integrable_mul (hv c)

theorem pair_sub_half_nrm {φ : ℝ × Vec 2 → ℝ} {p : ℝ × Vec 2} (hp : p.1 < b) :
    1 / 2 * (∑ c, wjet b φ p c * wjet b φ p c) + timeTerm b φ p
      ≤ ∑ c, wjet b φ p c * tjet φ p c := by
  have hw0 : 0 < wt b p.1 := Real.exp_pos _
  have hw1 : wt b p.1 ≤ 1 := by
    have : p.1 - b ≤ 0 := by linarith
    simpa [wt] using Real.exp_le_one_iff.2 this
  simp only [Fin.sum_univ_three, wjet, jet, tjet, timeTerm, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  set w := wt b p.1
  set x := φ p
  set x0 := partX φ 0 p
  set x1 := partX φ 1 p
  set t := stTimeDeriv φ p
  have h1 : 0 ≤ w * (1 - w) * x ^ 2 := mul_nonneg (mul_nonneg hw0.le (by linarith)) (sq_nonneg _)
  have h2 : 0 ≤ w * (2 - w) * x0 ^ 2 := mul_nonneg (mul_nonneg hw0.le (by linarith)) (sq_nonneg _)
  have h3 : 0 ≤ w * (2 - w) * x1 ^ 2 := mul_nonneg (mul_nonneg hw0.le (by linarith)) (sq_nonneg _)
  nlinarith [h1, h2, h3]

theorem coercive {φ : testSub b} (hab : a < b) (hB : MeasurableSet B) :
    (1 / 2 : ℝ) * ‖Jmap a b B φ‖ ^ 2 ≤ ⟪Jmap a b B φ, Tmap a b B φ⟫_ℝ := by
  have hJ := memLp_wjet (a := a) (B := B) φ.2
  have hT := memLp_tjet (a := a) (B := B) φ.2
  have e1 : ‖Jmap a b B φ‖ ^ 2 = ∫ p in Om a b B, ∑ c, wjet b φ.1 p c * wjet b φ.1 p c :=
    norm_sq_toX _ hJ
  have e2 : ⟪Jmap a b B φ, Tmap a b B φ⟫_ℝ = ∫ p in Om a b B, ∑ c, wjet b φ.1 p c * tjet φ.1 p c :=
    inner_toX _ _ hJ hT
  rw [e1, e2]
  have iN := integrable_sum_mul hJ hJ
  have iP := integrable_sum_mul hJ hT
  have iK := integrable_timeTerm a b B φ.2
  have hmono : ∫ p in Om a b B, (1 / 2 * (∑ c, wjet b φ.1 p c * wjet b φ.1 p c) + timeTerm b φ.1 p)
      ≤ ∫ p in Om a b B, ∑ c, wjet b φ.1 p c * tjet φ.1 p c := by
    refine setIntegral_mono_on ((iN.const_mul _).add iK) iP (measurableSet_Ioo.prod hB) ?_
    intro p hp
    exact pair_sub_half_nrm hp.1.2
  have hsplit : ∫ p in Om a b B, (1 / 2 * (∑ c, wjet b φ.1 p c * wjet b φ.1 p c) + timeTerm b φ.1 p)
      = 1 / 2 * (∫ p in Om a b B, ∑ c, wjet b φ.1 p c * wjet b φ.1 p c)
        + ∫ p in Om a b B, timeTerm b φ.1 p := by
    rw [integral_add (iN.const_mul _) iK, integral_const_mul]
  have hK := integral_timeTerm_nonneg (B := B) hab φ.2
  linarith

end AVRegularity.Applications.HeatReplacement
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open scoped InnerProductSpace
namespace AVRegularity.Applications.HeatReplacement

/-! # Slice weak gradients of limits of test jets

If `z ∈ L²(μ)³` lies in the closure of the range of `J`, then for almost every `τ` the slice
`z₀(τ, ·)` has weak gradient `(z₁, z₂)(τ, ·)` on `B`. The proof extracts a subsequence of test
functions along which the slice `L²(B)` distances converge to zero for a.e. `τ`, and passes to the
limit with `hasWeakPartialDerivOn_of_L2_limit`. -/

section
variable {a b : ℝ} {B : Set (Vec 2)}

theorem wjet_zero (b : ℝ) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    wjet b φ p 0 = wt b p.1 * φ p := by
  simp [wjet, jet]

theorem wjet_succ (b : ℝ) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) (i : Fin 2) :
    wjet b φ p i.succ = wt b p.1 * partX φ i p := by
  fin_cases i <;> simp [wjet, jet]

theorem fderiv_slice {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (τ : ℝ) (y v : Vec 2) :
    fderiv ℝ (fun y => φ (τ, y)) y v = fderiv ℝ φ (τ, y) (0, v) := by
  have h1 := (hasFDerivAt_const (𝕜 := ℝ) τ y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have h2 := (testSub_diff h (τ, y)).hasFDerivAt.comp y h1
  change fderiv ℝ (φ ∘ fun y => (τ, y)) y v = _
  rw [h2.fderiv]
  simp

theorem slice_contDiff {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (τ : ℝ) :
    ContDiff ℝ 1 (fun y => wt b τ * φ (τ, y)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => φ (τ, y)) :=
    h.1.comp (contDiff_const.prodMk contDiff_id)
  exact (contDiff_const.mul (h1.of_le (by exact_mod_cast le_top)))

theorem slice_hasWeakPartial {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (τ : ℝ) (i : Fin 2)
    (U : Set (Vec 2)) :
    HasWeakPartialDerivOn U i (fun y => wt b τ * φ (τ, y))
      (fun y => wt b τ * partX φ i (τ, y)) := by
  have := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i) (slice_contDiff h τ)
  convert this using 2
  rename_i y
  have hd : DifferentiableAt ℝ (fun y => φ (τ, y)) y :=
    ((testSub_diff h).comp (differentiable_const τ |>.prodMk differentiable_id)) y
  rw [fderiv_const_mul hd, smul_apply, AVRegularity.Applications.HeatReplacement.fderiv_slice h]
  simp [partX]

theorem continuous_slice_wjet_zero {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (τ : ℝ) :
    Continuous fun y => wjet b φ (τ, y) 0 := by
  simp only [wjet_zero]
  exact continuous_const.mul (h.1.continuous.comp (continuous_const.prodMk continuous_id))

theorem continuous_slice_wjet_succ {φ : ℝ × Vec 2 → ℝ} (h : φ ∈ testSub b) (τ : ℝ) (i : Fin 2) :
    Continuous fun y => wjet b φ (τ, y) i.succ := by
  simp only [wjet_succ]
  exact continuous_const.mul ((continuous_partX h i).comp (continuous_const.prodMk continuous_id))
end

/-! # Slice weak gradients of elements of the closure of `range J` -/

section
variable {a b : ℝ} {B : Set (Vec 2)}

/-- Components of `J φ_n - z` tend to zero in `L²(μ)`: the squared `L²` norms of the pointwise
differences go to zero. -/
theorem tendsto_sq_diff (z : Tri (mu a b B)) (φ : ℕ → testSub b)
    (hφ : Tendsto (fun n => Jmap a b B (φ n)) atTop (𝓝 z)) (c : Fin 3) :
    Tendsto (fun n => ∫ p, (wjet b (φ n).1 p c - (z c : ℝ × Vec 2 → ℝ) p) ^ 2 ∂(mu a b B))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ‖Jmap a b B (φ n) - z‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hφ
  have h2 : Tendsto (fun n => ‖(Jmap a b B (φ n) - z) c‖ ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => ‖(Jmap a b B (φ n) - z) c‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => PiLp.norm_apply_le _ c) h1
    simpa using this.pow 2
  refine h2.congr fun n => ?_
  rw [← real_inner_self_eq_norm_sq, inner_Lp_real]
  refine integral_congr_ae ?_
  have e1 : ((Jmap a b B (φ n) - z) c : ℝ × Vec 2 → ℝ)
      =ᵐ[mu a b B] fun p => wjet b (φ n).1 p c - (z c : ℝ × Vec 2 → ℝ) p := by
    have := Lp.coeFn_sub (Jmap a b B (φ n) c) (z c)
    filter_upwards [this, toX_coeFn (wjet b (φ n).1) (memLp_wjet (a := a) (B := B) (φ n).2) c]
      with p hp hq
    rw [PiLp.sub_apply, hp, Pi.sub_apply]
    exact congrArg (· - (z c : ℝ × Vec 2 → ℝ) p) hq
  filter_upwards [e1] with p hp
  rw [hp]; ring

/-- Slice weak gradients of elements in the closure of the range of `J`. -/
theorem slice_weak_gradient (z : Tri (mu a b B))
    (hz : z ∈ (LinearMap.range (Jmap a b B)).topologicalClosure) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn B (fun y => (z 0 : ℝ × Vec 2 → ℝ) (τ, y))
        (fun y i => (z i.succ : ℝ × Vec 2 → ℝ) (τ, y)) := by
  -- a sequence of test functions
  have hz' : z ∈ closure ((LinearMap.range (Jmap a b B) : Submodule ℝ (Tri (mu a b B))) :
      Set (Tri (mu a b B))) := by
    rw [← Submodule.topologicalClosure_coe]; exact hz
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.1 hz'
  choose φ hφx using fun n => LinearMap.mem_range.1 (hxmem n)
  have hφ : Tendsto (fun n => Jmap a b B (φ n)) atTop (𝓝 z) := by
    refine hxlim.congr fun n => ?_
    exact (hφx n).symm
  set W : Fin 3 → ℝ × Vec 2 → ℝ := fun c => (z c : ℝ × Vec 2 → ℝ) with hW
  set G : ℕ → Fin 3 → ℝ × Vec 2 → ℝ := fun n c p => wjet b (φ n).1 p c - W c p with hG
  have hGmem : ∀ n c, MemLp (G n c) 2 (mu a b B) := fun n c =>
    (memLp_wjet (a := a) (B := B) (φ n).2 c).sub (Lp.memLp (z c))
  have hGint : ∀ n c, Integrable (fun p => G n c p ^ 2) (mu a b B) := fun n c =>
    (hGmem n c).integrable_sq
  have hprod : mu a b B = (volume.restrict (Set.Ioo a b)).prod (volume.restrict B) :=
    volume_restrict_Om a b B
  -- slice functionals
  set H : ℕ → ℝ → ℝ := fun n τ => ∑ c, ∫ y in B, G n c (τ, y) ^ 2 with hH
  have hGint' : ∀ n c, Integrable (fun p => G n c p ^ 2)
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := fun n c => by
    rw [← hprod]; exact hGint n c
  have hHint : ∀ n, Integrable (H n) (volume.restrict (Set.Ioo a b)) := fun n =>
    integrable_finsetSum _ fun c _ => (hGint' n c).integral_prod_left
  have hHnn : ∀ n τ, 0 ≤ H n τ := fun n τ =>
    Finset.sum_nonneg fun c _ => integral_nonneg fun y => sq_nonneg _
  have hHint_eq : ∀ n, ∫ τ in Set.Ioo a b, H n τ = ∑ c, ∫ p, G n c p ^ 2 ∂(mu a b B) := by
    intro n
    simp only [hH]
    rw [integral_finsetSum _ fun c _ => (hGint' n c).integral_prod_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hprod]
    exact (integral_prod _ (hGint' n c)).symm
  have hHlim : Tendsto (fun n => ∫ τ in Set.Ioo a b, H n τ) atTop (𝓝 0) := by
    simp_rw [hHint_eq]
    have := (tendsto_finsetSum Finset.univ fun c _ => tendsto_sq_diff z φ hφ c)
    simpa using this
  obtain ⟨s, hs, hae⟩ := exists_subseq_ae_tendsto_zero hHint hHnn hHlim
  -- good slices
  have hgood : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)), ∀ n c,
      Integrable (fun y => G n c (τ, y) ^ 2) (volume.restrict B) ∧
        AEStronglyMeasurable (fun y => G n c (τ, y)) (volume.restrict B) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro c
    have hm : AEStronglyMeasurable (G n c)
        ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := by
      rw [← hprod]; exact (hGmem n c).aestronglyMeasurable
    filter_upwards [(hGint' n c).prod_right_ae, hm.prodMk_left] with τ h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hae, hgood] with τ hτ hτg
  intro i
  have hmem : ∀ n c, MemLp (fun y => G n c (τ, y)) 2 (volume.restrict B) := fun n c =>
    (memLp_two_iff_integrable_sq (hτg n c).2).2 (hτg n c).1
  have hle : ∀ n c, ∫ y in B, G n c (τ, y) ^ 2 ≤ H n τ := fun n c =>
    Finset.single_le_sum (f := fun c => ∫ y in B, G n c (τ, y) ^ 2)
      (fun c _ => integral_nonneg fun y => sq_nonneg _) (Finset.mem_univ c)
  have hzero : ∀ c, Tendsto (fun k => ∫ y in B, G (s k) c (τ, y) ^ 2) atTop (𝓝 0) := fun c =>
    squeeze_zero (fun k => integral_nonneg fun y => sq_nonneg _) (fun k => hle (s k) c) hτ
  refine hasWeakPartialDerivOn_of_L2_limit (U := B) i
    (u := fun y => W 0 (τ, y)) (d := fun y => W i.succ (τ, y))
    (un := fun k y => wjet b (φ (s k)).1 (τ, y) 0)
    (dn := fun k y => wjet b (φ (s k)).1 (τ, y) i.succ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    simp only [wjet_zero, wjet_succ]
    exact slice_hasWeakPartial (φ (s k)).2 τ i B
  · exact fun k => continuous_slice_wjet_zero (φ (s k)).2 τ
  · exact fun k => continuous_slice_wjet_succ (φ (s k)).2 τ i
  · exact fun k => hmem (s k) 0
  · exact fun k => hmem (s k) i.succ
  · exact hzero 0
  · exact hzero i.succ
end

end AVRegularity.Applications.HeatReplacement
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open scoped InnerProductSpace
namespace AVRegularity.Applications.HeatReplacement

/-! # Existence of the heat replacement on a general cylinder

For `a < b`, a measurable set `B ⊆ ℝ²` and a forcing `F ∈ L²((a,b) × B; ℝ²)`, there are
`Z ∈ L²` and `DZ ∈ L²` with a.e. slice weak gradients, the bound
`∫ Z² ≤ 4 e^{2(b-a)} ∫ |F|²`, and the weak heat equation with divergence forcing, tested
against smooth compactly supported `φ` vanishing on the top slice `τ = b`. The construction is the
Lions representation theorem applied to `J`, `T` with coercivity constant `1/2`. -/

variable {a b : ℝ} {B : Set (Vec 2)}

/-- The forcing triple `(0, -F₁ g⁻¹, -F₂ g⁻¹)`. -/
def forceTri (b : ℝ) (F : ℝ × Vec 2 → Vec 2) (p : ℝ × Vec 2) : Fin 3 → ℝ :=
  ![0, -(F p 0 * Real.exp (b - p.1)), -(F p 1 * Real.exp (b - p.1))]

theorem wt_mul_exp (b τ : ℝ) : wt b τ * Real.exp (b - τ) = 1 := by
  rw [wt, ← Real.exp_add]; simp

theorem exp_le_of_mem {p : ℝ} (hp : a < p) (b : ℝ) : Real.exp (b - p) ≤ Real.exp (b - a) :=
  Real.exp_le_exp.2 (by linarith)

theorem memLp_forceTri (hB : MeasurableSet B) {F : ℝ × Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (mu a b B)) :
    ∀ c, MemLp (fun p => forceTri b F p c) 2 (mu a b B) := by
  have hbd : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => -(F p i * Real.exp (b - p.1))) 2
      (mu a b B) := by
    intro i
    refine MemLp.of_le_mul (c := Real.exp (b - a)) (hF i)
      (((hF i).aestronglyMeasurable.mul
        (Real.continuous_exp.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable).neg)
      ?_
    refine (ae_restrict_iff' (measurableSet_Ioo.prod hB)).2 (Filter.Eventually.of_forall ?_)
    intro p hp
    have h1 := exp_le_of_mem hp.1.1 b
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [abs_nonneg (F p i), Real.exp_pos (b - a)]
  intro c
  fin_cases c
  · simp [forceTri]
  · simpa [forceTri] using hbd 0
  · simpa [forceTri] using hbd 1

theorem sum_forceTri_wjet (F : ℝ × Vec 2 → Vec 2) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    ∑ c, forceTri b F p c * wjet b φ p c = -vecDot (F p) (stSpaceGrad φ p) := by
  have h := wt_mul_exp b p.1
  simp only [Fin.sum_univ_three, forceTri, wjet, jet, vecDot, Fin.sum_univ_two, stSpaceGrad,
    partX, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-(F p 0 * fderiv ℝ φ p (0, basisVec 0))
    - F p 1 * fderiv ℝ φ p (0, basisVec 1)) * h

theorem sum_forceTri_sq {p : ℝ × Vec 2} (hp : p.1 ∈ Set.Ioo a b) (F : ℝ × Vec 2 → Vec 2) :
    ∑ c, forceTri b F p c * forceTri b F p c ≤ Real.exp (2 * (b - a)) * vecNormSq (F p) := by
  have h1 := exp_le_of_mem hp.1 b
  have h2 : Real.exp (b - p.1) ^ 2 ≤ Real.exp (2 * (b - a)) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; nlinarith [hp.1, hp.2])
  simp only [Fin.sum_univ_three, forceTri, vecNormSq, vecDot, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  nlinarith [mul_nonneg (sq_nonneg (F p 0)) (sub_nonneg.2 h2),
    mul_nonneg (sq_nonneg (F p 1)) (sub_nonneg.2 h2)]

/-- Existence of the heat replacement on `(a,b) × B`. -/
theorem exists_replacement (hab : a < b) (hB : MeasurableSet B) {F : ℝ × Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (mu a b B)) :
    ∃ (Z : ℝ × Vec 2 → ℝ) (DZ : ℝ × Vec 2 → Vec 2),
      MemLp Z 2 (mu a b B) ∧ (∀ i : Fin 2, MemLp (fun p => DZ p i) 2 (mu a b B)) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
        HasWeakGradientOn B (fun y => Z (τ, y)) (fun y => DZ (τ, y))) ∧
      ∫ p in Om a b B, Z p ^ 2 ≤
        4 * Real.exp (2 * (b - a)) * ∫ p in Om a b B, vecNormSq (F p) ∧
      ∀ φ : ℝ × Vec 2 → ℝ, φ ∈ testSub b →
        ∫ p in Om a b B, (-(Z p * stTimeDeriv φ p) + vecDot (DZ p) (stSpaceGrad φ p)) =
          -∫ p in Om a b B, vecDot (F p) (stSpaceGrad φ p) := by
  have hfm := memLp_forceTri (a := a) (b := b) hB hF
  set f : Tri (mu a b B) := toX (forceTri b F) hfm with hf
  obtain ⟨z, hzc, hzrep, hznorm⟩ := lions_representation_with_norm_bound
    (Jmap a b B) (Tmap a b B) (α := 1 / 2) (by norm_num)
    (fun φ => coercive hab hB) f
  refine ⟨fun p => (z 0 : ℝ × Vec 2 → ℝ) p, fun p i => (z i.succ : ℝ × Vec 2 → ℝ) p,
    Lp.memLp (z 0), fun i => Lp.memLp (z i.succ), slice_weak_gradient z hzc, ?_, ?_⟩
  · -- the bound
    have hZ : ∫ p in Om a b B, (z 0 : ℝ × Vec 2 → ℝ) p ^ 2 = ‖z 0‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_Lp_real]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have hz0 : ‖z 0‖ ≤ ‖z‖ := PiLp.norm_apply_le z 0
    have hfn : ‖f‖ ^ 2 = ∫ p in Om a b B, ∑ c, forceTri b F p c * forceTri b F p c :=
      norm_sq_toX _ hfm
    have hbound : ∫ p in Om a b B, ∑ c, forceTri b F p c * forceTri b F p c ≤
        Real.exp (2 * (b - a)) * ∫ p in Om a b B, vecNormSq (F p) := by
      rw [← integral_const_mul]
      have iF : Integrable (fun p => vecNormSq (F p)) (mu a b B) := by
        simp only [vecNormSq, vecDot, Fin.sum_univ_two]
        exact ((hF 0).integrable_mul (hF 0)).add ((hF 1).integrable_mul (hF 1))
      refine setIntegral_mono_on (integrable_sum_mul hfm hfm) (iF.const_mul _)
        (measurableSet_Ioo.prod hB) ?_
      intro p hp
      exact sum_forceTri_sq hp.1 F
    have hzn : ‖z‖ ≤ 2 * ‖f‖ := by
      have := hznorm
      rw [div_eq_mul_inv] at this
      have h2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
      rw [h2, mul_comm] at this
      exact this
    have hsq : ‖z‖ ^ 2 ≤ 4 * ‖f‖ ^ 2 := by nlinarith [norm_nonneg z, norm_nonneg f]
    have hz0sq : ‖z 0‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg (z 0)]
    rw [hZ]
    nlinarith [hfn, hbound]
  · intro φ hφ
    have hJ := memLp_wjet (a := a) (B := B) hφ
    have hT := memLp_tjet (a := a) (B := B) hφ
    have e := hzrep ⟨φ, hφ⟩
    have e1 : ⟪z, Tmap a b B ⟨φ, hφ⟩⟫_ℝ
        = ∫ p in Om a b B, ∑ c, (z c : ℝ × Vec 2 → ℝ) p * tjet φ p c :=
      inner_Tri_toX z _ hT
    have e2 : ⟪f, Jmap a b B ⟨φ, hφ⟩⟫_ℝ
        = ∫ p in Om a b B, ∑ c, forceTri b F p c * wjet b φ p c :=
      inner_toX _ _ hfm hJ
    rw [e1, e2] at e
    rw [← integral_neg]
    simp_rw [sum_forceTri_wjet] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Fin.sum_univ_three, tjet, vecDot, Fin.sum_univ_two, stSpaceGrad, partX,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring

end AVRegularity.Applications.HeatReplacement
end
end
end

section
public section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Heat replacement on `Q_{3/4}`

Step 1 of the proof of Lemma 3.3 of the paper: for every square integrable
forcing `F` on `Q_{3/4}` there are `Z`, `DZ` in `L²(Q_{3/4})` with `DZ(τ, ·)` the weak gradient of
`Z(τ, ·)` on `B_{3/4}` for a.e. `τ`, with `∫ Z² ≤ C ∫ |F|²` and with `∂τ Z - ΔZ = div F` in the
weak sense against all `φ ∈ C^∞_c(Q_{3/4})`.
The solution is produced by the Lions representation theorem
(`lions_representation_with_norm_bound`) rather than by a Fourier series; the constant is
`4 e^{9/8}`. -/

open AVRegularity.Applications.HeatReplacement in
theorem openCyl_three_quarters_eq :
    openCyl 0 (3 / 4) = Om (-(9 / 16)) 0 (euclidBall 0 (3 / 4)) := by
  simp only [openCyl, Om]
  norm_num

open AVRegularity.Applications.HeatReplacement in
/-- **Heat replacement.** Zero-data solution of the heat equation with divergence-form forcing
on `Q_{3/4}`, with an `L²` energy bound. -/
theorem heat_replacement :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ℝ × Vec 2 → Vec 2,
      (∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict (openCyl 0 (3 / 4)))) →
      ∃ (Z : ℝ × Vec 2 → ℝ) (DZ : ℝ × Vec 2 → Vec 2),
        MemLp Z 2 (volume.restrict (openCyl 0 (3 / 4))) ∧
        (∀ i : Fin 2, MemLp (fun p => DZ p i) 2 (volume.restrict (openCyl 0 (3 / 4)))) ∧
        (∀ᵐ τ ∂(volume.restrict (Set.Ioo (-(9 / 16) : ℝ) 0)),
          HasWeakGradientOn (euclidBall 0 (3 / 4)) (fun y => Z (τ, y)) (fun y => DZ (τ, y))) ∧
        ∫ p in openCyl 0 (3 / 4), Z p ^ 2 ≤ C * ∫ p in openCyl 0 (3 / 4), vecNormSq (F p) ∧
        ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (openCyl 0 (3 / 4)) φ →
          ∫ p in openCyl 0 (3 / 4), (-(Z p * stTimeDeriv φ p) + vecDot (DZ p) (stSpaceGrad φ p)) =
            -∫ p in openCyl 0 (3 / 4), vecDot (F p) (stSpaceGrad φ p) := by
  refine ⟨4 * Real.exp (2 * (0 - (-(9 / 16)))), by positivity, ?_⟩
  intro F hF
  have hB : MeasurableSet (euclidBall 0 (3 / 4)) :=
    AVRegularity.External.Campanato.euclidBall_measurable _ _
  rw [openCyl_three_quarters_eq] at hF ⊢
  obtain ⟨Z, DZ, hZ, hDZ, hslice, hbound, heq⟩ :=
    exists_replacement (a := -(9 / 16)) (b := 0) (B := euclidBall 0 (3 / 4)) (by norm_num) hB hF
  refine ⟨Z, DZ, hZ, hDZ, hslice, hbound, ?_⟩
  intro φ hφ
  refine heq φ ⟨hφ.1, hφ.2.1, fun y => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hφ.2.2 h
  exact lt_irrefl _ this.1.2

end AVRegularity.Applications
end
end
