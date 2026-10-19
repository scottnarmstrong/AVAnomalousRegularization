-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.CutoffComplementTaylor
public import AVRegularity.CycleWords.Seam.OldScalar.WindowRegions
public import AVRegularity.CycleWords.MixedWords.RetainedAssign
public import AVRegularity.CycleWords.Seam.CutoffComplementJetScale
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
/-! The exact cutoff-complement ingredient of the negative-norm seam estimate. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal

universe u v

namespace AVRegularity.CycleWords.Seam

/-- Estimate the actual complement against one unit compact test at the large scale. -/
theorem cutoff_family_complement_test_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]
    (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m ξ = 1)
    (π : ι → ℝ) (p N k : ℕ) (s ρ : ℝ) (hρ : 1 ≤ ρ)
    (g φ : ∀ v, Vec 2 → h v) (hg : ∀ v, MemLp (g v) 2 volume)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v))
    (hunit : weightedJetNorm π (-(p : ℝ)) (N + k) s ρ
      (fun v _ w z => orderedDerivative w (φ v) z) ≤ 1)
    (hfinite : Assembly.negJetNorm π p k s 1 g ≠ ⊤) :
    ENNReal.ofReal |∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z - fourierCutoff m (g v) z) (φ v z)| ≤
      ENNReal.ofReal ((((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * ρ⁻¹ ^ N) *
        ((2 : ℝ) ^ N * cutoffWeightedMoment (cutoffKernel m) s N p +
          2 ^ p + cutoffWeightedMoment (cutoffKernel m) s 0 p)) * Assembly.negJetNorm π p k s 1 g := by
  let D := Assembly.negJetNorm π p k s 1 g
  let L := ((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * ρ⁻¹ ^ N
  let B := L * D.toReal
  have hDreal : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hfinite
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have hfact : 0 < ((N + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (N + k)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hB : 0 ≤ B := mul_nonneg hL ENNReal.toReal_nonneg
  have hwords (z : Vec 2) (w : DerivativeWord2 N) :
      ‖orderedDerivative w (cutoffFamilyPair π g φ) z‖ ≤ B * (2 * cutoffBracket s z) ^ p := by
    have hp := cutoff_derivative_pair_le π p N k s ρ hρ g φ hφ hunit w z
    have hq : 0 ≤ (2 * cutoffBracket s z) ^ p * L :=
      mul_nonneg (pow_nonneg (by linarith only [cutoffBracket_one_le s z]) _) hL
    change ENNReal.ofReal |cutoffFamilyPair π g (fun v => orderedDerivative w (φ v)) z| ≤
      ENNReal.ofReal ((2 * cutoffBracket s z) ^ p * L) * D at hp
    rw [← hDreal, ← ENNReal.ofReal_mul hq] at hp
    have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hq ENNReal.toReal_nonneg)).mp hp
    rw [cutoffFamilyPair_orderedDerivative π g φ hg hφ w, Real.norm_eq_abs]
    exact hr.trans_eq (by dsimp only [B]; ring)
  have hscalar := cutoff_scalar_complement_bound m R hm hsm hflat (cutoffFamilyPair π g φ)
    (cutoffFamilyPair_contDiff π g φ hg hφ) N p s B hB hwords
  rw [cutoffFamilyPair_complement_eq m R hm hsm π g φ hg hφ]
  let Q := (2 : ℝ) ^ N * cutoffWeightedMoment (cutoffKernel m) s N p +
    2 ^ p + cutoffWeightedMoment (cutoffKernel m) s 0 p
  have hMN := cutoffWeightedMoment_nonneg (cutoffKernel m) s N p
  have hM0 := cutoffWeightedMoment_nonneg (cutoffKernel m) s 0 p
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have he : B * Q = (L * Q) * D.toReal := by dsimp only [B]; ring
  calc
    _ ≤ ENNReal.ofReal (B * Q) := ENNReal.ofReal_le_ofReal hscalar
    _ = _ := by
      rw [he, ENNReal.ofReal_mul (mul_nonneg hL hQ), ENNReal.ofReal_toReal hfinite]

end AVRegularity.CycleWords.Seam

namespace AVRegularity.CycleWords.Assembly

open AVRegularity.CycleWords.Seam

/-- The cutoff complement gains the exact `S^{-N/2}` in the stipulated negative norms. -/
theorem seamCutoffComplement : SeamCutoffComplementStatement.{u, v} := by
  intro ξ0 χm hχ _ hsupport hflat k N p
  let L : ℝ := ((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ)
  let MN := cutoffWeightedMoment (cutoffKernel χm) 1 N p
  let M0 := cutoffWeightedMoment (cutoffKernel χm) 1 0 p
  let Q : ℝ := (2 : ℝ) ^ N * MN + 2 ^ p + M0 + 1
  have hMN : 0 ≤ MN := cutoffWeightedMoment_nonneg _ _ _ _
  have hM0 : 0 ≤ M0 := cutoffWeightedMoment_nonneg _ _ _ _
  have hfact : 0 < ((N + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (N + k)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hC : 0 < L * Q := mul_pos hL hQ
  refine ⟨L * Q, hC.le, ?_⟩
  intro ι _ h _ _ _ _ _ _ π _ η S s hη hη1 hS hs g hg
  have hSp : 0 < S := zero_lt_one.trans_le hS
  let D := negJetNorm π p k s 1 g
  change negJetNorm π p (N + k) s s⁻¹
    (fun x z => g x z - fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (g x) z) ≤
    ENNReal.ofReal (L * Q * S ^ (-(N : ℝ) / 2)) * D
  by_cases hD : D = ⊤
  · rw [hD, ENNReal.mul_top (ENNReal.ofReal_pos.mpr
      (mul_pos hC (Real.rpow_pos_of_pos hSp _))).ne']
    exact le_top
  · let a := (Real.sqrt η)⁻¹
    have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hη)
    obtain ⟨hs0, hs1, ha1, hsa⟩ := cutoff_scale_relations η S s hη hη1 hS hs
    have hρ : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).mpr hs1
    obtain ⟨hscaled, hscaledSupport, hscaledFlat⟩ := cutoff_dilation_data χm ξ0 hsupport hχ hflat a ha
    have hMNscaled := cutoffWeightedMoment_dilation_le χm ξ0 hsupport hχ s a hs0.le ha hsa N p
    have hM0scaled := cutoffWeightedMoment_dilation_le χm ξ0 hsupport hχ s a hs0.le ha hsa 0 p
    simp only [pow_zero, one_mul] at hM0scaled
    have han : 1 ≤ a ^ N := one_le_pow₀ ha1
    let T := (2 : ℝ) ^ N * cutoffWeightedMoment (cutoffKernel (fun θ => χm (a • θ))) s N p +
      2 ^ p + cutoffWeightedMoment (cutoffKernel (fun θ => χm (a • θ))) s 0 p
    have hT : T ≤ a ^ N * Q := by
      have hsmall : 2 ^ p + M0 ≤ a ^ N * (2 ^ p + M0) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right han (by positivity : 0 ≤ (2 : ℝ) ^ p + M0)
      calc
        _ ≤ (2 : ℝ) ^ N * (a ^ N * MN) + 2 ^ p + M0 :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hMNscaled (by positivity)) le_rfl) hM0scaled
        _ = a ^ N * ((2 : ℝ) ^ N * MN) + (2 ^ p + M0) := by ring
        _ ≤ a ^ N * ((2 : ℝ) ^ N * MN) + a ^ N * (2 ^ p + M0) := add_le_add le_rfl hsmall
        _ = a ^ N * ((2 : ℝ) ^ N * MN + 2 ^ p + M0) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (pow_nonneg ha.le _)
    have hprice : L * s ^ N * T ≤ L * Q * S ^ (-(N : ℝ) / 2) := by
      calc
        _ ≤ L * s ^ N * (a ^ N * Q) := mul_le_mul_of_nonneg_left hT (mul_nonneg hL.le (pow_nonneg hs0.le _))
        _ = L * Q * (s * a) ^ N := by rw [mul_pow]; ring
        _ = _ := by rw [cutoff_scale_power η S s hη hS hs N]
    refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hunit => ?_
    have ht := cutoff_family_complement_test_le (fun θ => χm (a • θ)) (ξ0 / a)
      hscaledSupport hscaled hscaledFlat π p N k s s⁻¹ hρ g φ hg hφ hunit hD
    simp only [inv_inv] at ht
    exact ht.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hprice) le_rfl)

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # the kernel clauses of `SeamFutureKernelStatement` (statements only)

`SeamFutureKernelStatement` asks for a linear map `K₊` with three
clauses: smooth outputs on `L²` fields (1), the bound `(ϖ⁻¹,-L;p_in) → (r,M;p_out)` at cost
`C_{L,M}Θ₊` for every scale `r ≤ max 1 C_out · ϖ⁻¹` (2), and the fast remainder. This
file fixes `K₊` (`seamFutureKernel`) and reduces clauses (1) and (2) to two analytic statements.

The kernel is the retained map of the future block, built with the cutoff `χ_lo^{n+1}`
(`n = p_out + ∑K_s^F`, the cutoff placement of retainedGaussian), applied to the cell low pass
`μ(D)` of the field (`IsSeamLowPass`: `μ = 1` on `|ξ| ≤ 3π/8`, `0` on `|ξ| ≥ π/2`; the zero cell
harmonic `P₀`), on blocks well buffered at `(c₁, Q₁)`, and `0` on the others.
It is `0` when `Θ₊ = 0`: the right sides are then `ofReal 0 · ⊤ = 0` on fields of infinite
negative norm, where the retained map is unconstrained.

Why the Gaussian. The input norm takes derivatives at scale
`ϖ⁻¹ = √(S/η)` while the retained band is `|θ| ≲ √η`. Passing through the moment norm of the
input and retainedModelJets loses `S^{L/2}`: a wave packet at `|θ| ≈ ξ_lo√η` has
`momentNorm(μ(D)g) ≈ S^{L/2} negJet(g)`. The factor `e^{-c|θ|²/ϖ²}` of the retained amplitude
(retainedGaussian) absorbs `⟨θ/ϖ⟩^{2L}` instead.

* `SeamGaussianNegStatement` (Gaussian Plancherel): `GaussianPlancherelStatement` with the
  negative norm of `G` in place of the moment norm, for amplitudes bounded by the Bloch fibres of
  the cell low pass `μ(D)G`, at every output scale `r ≤ max 1 C_out · ϖ⁻¹`.
* `SeamLowPassMomentStatement` (qualitative): a field of finite negative norm
  with weight `n` has a low pass with `n` finite moments (retainedGaussian needs `n + 2`).
* `LowCutoffExistsStatement`: a low cutoff exists.
* `SeamFutureKernelClausesStatement`: clauses (1) and (2) for `seamFutureKernel`, for every
  regime `(c₁, Q₁)` with `c₁ ≤ c₀`, `Q₀ ≤ Q₁`. `SeamFutureKernelClausesAssembly`: from the Gaussian Plancherel statement,
  the low-pass moment statement and the retained-map statements. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- **Plancherel with a Gaussian amplitude, negative input norm.** If the amplitudes of a
band-limited family vanish outside `|θ| < π/2` and obey the Gaussian bound of retainedGaussian by
the Bloch fibre norms of the cell low pass `F = μ(D)G` of an `L²` field `G` (`μ` vanishing for
`|ξ| ≥ π/2`, so that every fibre of `F` at a frequency of the zone carries one plane wave), then
the weighted jets of the family at every scale `r ≤ max 1 C_out · ϖ⁻¹` are bounded by the
negative norm of `G` with weight `n + 2`, at every order `L`.

The statement is false without the low pass: a Bloch fibre of a general field carries all the
cell modes `θ + 2πn`, and the Gaussian damps only `θ`.

For `G = 0` the bound reads `0 ≤ 0`. For `M = 0`, `m = 0`, `n = 0` it says
`‖g‖₂² ≲ ∫ e^{-2c|θ|²/ϖ²}⟨θ/ϖ⟩^{2p} |μĜ(θ)|² dθ`; with `θ = ϖζ` this is
`‖e^{-c|D|²}⟨D⟩^p Ĝ_ϖ‖²` for the rescaled field, at most `C_L ‖G_ϖ‖²_{H^{-L}}` for every `L`,
because the Gaussian absorbs `⟨ζ⟩^{2L}`. For a wave packet at `|θ| ≈ ξ_lo√η` both sides are
`≲ e^{-cS}`-small or `S^{-L/2}`-small, consistently.
Quantifier order: `C` comes after the orders, the rates, `C_out` and the cutoffs, and before
`η, ϖ, r` and the fields. -/
def SeamGaussianNegStatement : Prop :=
  ∀ (m n p M L : ℕ) (cGa Cout : ℝ), 0 < cGa → 0 < Cout →
  ∀ μ χlo : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
    ContDiff ℝ (⊤ : ℕ∞) χlo → HasCompactSupport χlo →
  ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (η ϖ r ρ CGa : ℝ), 0 < η → η ≤ 1 → 0 < ϖ → ϖ ≤ Real.sqrt η → 0 < r →
    r ≤ max 1 Cout * ϖ⁻¹ → 0 ≤ CGa →
  ∀ g A B G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
    (∀ x, IsRetainedAmplitude (g x) ρ (A x) (B x)) →
    (∀ x, ContDiff ℝ m (A x) ∧ ContDiff ℝ m (B x)) →
    (∀ x θ, Real.pi / 2 ≤ Real.sqrt (vecDot θ θ) → A x θ = 0 ∧ B x θ = 0) →
    (∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
      amplitudeJetNorm π m ϖ A B θ ≤
        ENNReal.ofReal (CGa * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p *
            Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
          ∑ α ∈ momentIndices n,
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α
                (fun x => fourierCutoff μ (G x)) θ) →
    weightedJetNorm π (m : ℝ) M ϖ r (fun x _ wd z => orderedDerivative wd (g x) z) ≤
      ENNReal.ofReal (C * CGa) * negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G

/-- **The low pass of a field of finite negative norm has finite moments** (qualitative;
the constant may depend on `S`).

For `n = 0`, `P₀G` is band limited and `G ∈ H^{-L}`, so `P₀G ∈ L²`. For weight `n`,
`⟨ϖz⟩^n G ∈ H^{-L}`, and `⟨ϖz⟩^n μ(D)G = μ(D)(⟨ϖz⟩^n G) +` commutators with the kernel
moments, by induction on `n`. -/
def SeamLowPassMomentStatement : Prop :=
  ∀ (n L : ℕ) (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 →
  ∀ G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
    negJetNorm π (n : ℝ) L ϖ ϖ⁻¹ G < ⊤ →
    momentNorm π n ϖ (fun x => fourierCutoff μ (G x)) < ⊤

/-- **A low cutoff exists** (a radial smooth transition between `ξ_lo` and `2ξ_lo`). -/
def LowCutoffExistsStatement : Prop :=
  ∀ K : ScalarConstants, 0 < K.ξlo → ∃ χlo : Vec 2 → ℝ, IsLowCutoff K χlo

/-- The cell low pass of the seam (the zero cell harmonic `P₀`): smooth, even, compactly
supported, `1` on `|ξ| ≤ 3π/8` (which contains the retained band and the support of every low
pass `χ_lo(D/(2√η))`, since `4ξ_lo < 3π/8`), `0` on `|ξ| ≥ π/2`. -/
structure IsSeamLowPass (μ : Vec 2 → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) μ
  compact : HasCompactSupport μ
  even : ∀ ξ, μ (-ξ) = μ ξ
  one : ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ 3 * Real.pi / 8 → μ ξ = 1
  supp : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0

section Kernel

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Np : ℕ}

/-- The retained map (cutoff `χ_lo^{n+1}`) of the cell low pass of a square-integrable field. -/
def seamLowRetained (K : ScalarConstants) (χlo : Vec 2 → ℝ) (n : ℕ) {μ : Vec 2 → ℝ}
    (hμ : IsSeamLowPass μ) (π : ι → ℝ) (letters : Fin Np → CycleLetter ι h D)
    (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) :
    l2Fields ι h →ₗ[ℝ] (∀ x, Vec 2 → h x) where
  toFun g := retainedMap K (fun ξ => χlo ξ ^ (n + 1)) π letters η S ηg t₀ ϖ G v X₀
    (fun x => fourierCutoff μ (g.1 x))
  map_add' g₁ g₂ := by
    by_cases hR : ∃ R, IsRetainedMap K (fun ξ => χlo ξ ^ (n + 1)) π letters η S ηg t₀ ϖ G v X₀ R
    · rw [← map_add]
      exact (retainedMap_spec hR).congr _ _ fun x =>
        fourierCutoff_add_ae _ _ hμ.supp hμ.smooth (g₁.2 x) (g₂.2 x)
    · simp only [retainedMap_eq_zero hR, LinearMap.zero_apply, add_zero]
  map_smul' c g := by
    by_cases hR : ∃ R, IsRetainedMap K (fun ξ => χlo ξ ^ (n + 1)) π letters η S ηg t₀ ϖ G v X₀ R
    · rw [RingHom.id_apply, ← map_smul]
      exact (retainedMap_spec hR).congr _ _ fun x =>
        fourierCutoff_smul_ae _ _ hμ.supp hμ.smooth c (g.2 x)
    · simp only [retainedMap_eq_zero hR, LinearMap.zero_apply, smul_zero]

open Classical in
/-- **The future kernel of the seam** `K₊ = 𝒫₊ ∘ P₀`: on blocks well buffered at `(c₁, Q₁)` with
`Θ₊ ≠ 0`, the linear extension of `seamLowRetained` from the square-integrable fields; `0`
otherwise. -/
def seamFutureKernel (K : ScalarConstants) (χlo : Vec 2 → ℝ) (n : ℕ) {μ : Vec 2 → ℝ}
    (hμ : IsSeamLowPass μ) (π : ι → ℝ) (letters : Fin Np → CycleLetter ι h D)
    (η S ηg t₀ ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2)
    (c₁ : ℝ) (Q₁ : ℕ) (reg : BlockRegions) : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x) :=
  if wordTheta ηg letters = 0 then 0 else
    if IsWellBuffered c₁ Q₁ η S reg then
      (LinearMap.exists_extend (seamLowRetained K χlo n hμ π letters η S ηg t₀ ϖ G v X₀)).choose
    else 0

end Kernel

/-- **Clauses (1) and (2) of `SeamFutureKernelStatement` for `seamFutureKernel`**, for every
regime `(c₁, Q₁)` at least as strict as `(c₀, Q₀)`. `p_in = p_out + ∑K_s^F + 2`. -/
def SeamFutureKernelClausesStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ χlo : Vec 2 → ℝ, IsLowCutoff K χlo →
  ∀ μ : Vec 2 → ℝ, ∀ hμ : IsSeamLowPass μ, ∀ σ : SeamShape, σ.K = K →
  ∃ (c₀ : ℝ) (Q₀ : ℕ), 0 < c₀ ∧ ∀ (c₁ : ℝ) (Q₁ : ℕ), 0 < c₁ → c₁ ≤ c₀ → Q₀ ≤ Q₁ →
  ∀ Cout : ℝ, 0 < Cout →
  ∃ CK : ℕ → ℕ → ℝ, (∀ L M, 0 ≤ CK L M) ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ lettersF : Fin σ.Np → CycleLetter ι h σ.D,
    (∀ i, (lettersF i).order = σ.dF i ∧ (lettersF i).slow = σ.KsF i ∧
      (lettersF i).positive = σ.posF i) →
  ∀ η S ηg ϖ δ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → 0 < ηg → ηg ≤ 1 →
    ϖ = Real.sqrt (η / S) → δ = ϖ * ηg →
  ∀ (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ),
    IsCellMetric (fun t _ => GF t) → IsCellDrift vF →
    (∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t)) →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ σ.K.Cw) →
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ σ.K.Cvj j) →
    0 ≤ gF → gF ≤ σ.K.g0 → gF ≤ g₁ → IsMetricNearIdentity (fun t _ => GF t) gF →
  ∀ (regF : BlockRegions), ScalarPackage σ.K η GF vF tF S ϖ regF →
    (∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ) σ.Jstar σ.H) →
    (∀ i, IsTransverseOnPulses (lettersF i).edge
      (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient) →
    (∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S))) →
    (∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) →
  ∀ X₀F : Vec 2,
    (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      ∀ x (M : ℕ), ContDiff ℝ M (seamFutureKernel K χlo (σ.pout + ∑ i, σ.KsF i) hμ π lettersF η
        S ηg tF ϖ GF vF X₀F c₁ Q₁ regF g x)) ∧
    ∀ (L M : ℕ) (r : ℝ) (g : ∀ x, Vec 2 → h x), 0 < r → r ≤ max 1 Cout * ϖ⁻¹ →
      (∀ x, MemLp (g x) 2 volume) →
      weightedJetNorm π (σ.pout : ℝ) M ϖ r
          (fun x _ wd z => orderedDerivative wd (seamFutureKernel K χlo (σ.pout + ∑ i, σ.KsF i) hμ
            π lettersF η S ηg tF ϖ GF vF X₀F c₁ Q₁ regF g x) z) ≤
        ENNReal.ofReal (CK L M * wordTheta ηg lettersF) *
          negJetNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ g

/-- **Assembly of the kernel clauses** (its proof also uses `retainedMapExists`, `retainedGaussian`,
`IsWellBuffered.mono`, the window regions (`BlockRegions.inWindow`) to pass the quietness
on `reg.quiet ∩ [t_F, t_F + S]` to `IsWordBlock`, and `IsRetainedMap.band` for clause (1)). -/
def SeamFutureKernelClausesAssembly : Prop :=
  SeamGaussianNegStatement.{u, v} → SeamLowPassMomentStatement.{u, v} →
    SeamFutureKernelClausesStatement.{u, v}

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords.Seam

/-! # Radial smooth cutoffs

`radialCutoff_exists`: for `0 < r₀ < r₁` the radial smooth transition
`ξ ↦ smoothTransition((r₁² − |ξ|²)/(r₁² − r₀²))` is smooth, even, compactly supported, `1` on
`|ξ| ≤ r₀` and `0` on `|ξ| ≥ r₁`. Instances: `lowCutoffExists : LowCutoffExistsStatement`
(`r₀ = ξ_lo`, `r₁ = 2ξ_lo`) and the seam's cell low pass (`r₀ = 3π/8`, `r₁ = π/2`). -/

open AVRegularity.CycleWords.Assembly

theorem vecDot_self_nonneg (ξ : Vec 2) : 0 ≤ vecDot ξ ξ :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **A radial smooth cutoff** between the radii `r₀ < r₁`. -/
theorem radialCutoff_exists {r₀ r₁ : ℝ} (h0 : 0 < r₀) (h01 : r₀ < r₁) :
    ∃ χ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ ξ, χ (-ξ) = χ ξ) ∧
      (∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ r₀ → χ ξ = 1) ∧
      (∀ ξ, r₁ ≤ Real.sqrt (vecDot ξ ξ) → χ ξ = 0) := by
  have hd : 0 < r₁ ^ 2 - r₀ ^ 2 := by nlinarith
  have hz : ∀ ξ : Vec 2, r₁ ≤ Real.sqrt (vecDot ξ ξ) →
      Real.smoothTransition ((r₁ ^ 2 - vecDot ξ ξ) / (r₁ ^ 2 - r₀ ^ 2)) = 0 := by
    intro ξ hge
    apply Real.smoothTransition.zero_of_nonpos
    have hge2 : r₁ ^ 2 ≤ vecDot ξ ξ := by
      have := pow_le_pow_left₀ (by linarith) hge 2
      rwa [Real.sq_sqrt (vecDot_self_nonneg ξ)] at this
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  refine ⟨fun ξ => Real.smoothTransition ((r₁ ^ 2 - vecDot ξ ξ) / (r₁ ^ 2 - r₀ ^ 2)),
    ?_, ?_, fun ξ => ?_, fun ξ hle => ?_, hz⟩
  · have hv : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec 2 => vecDot ξ ξ) := by
      unfold vecDot
      exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub hv).div_const _)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) r₁) fun ξ hξ => hz ξ ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
    obtain ⟨i, hi⟩ : ∃ i, r₁ < |ξ i| := by
      by_contra hcon
      push Not at hcon
      exact absurd ((pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => by
        rw [Real.norm_eq_abs]; exact hcon i) (not_le.2 hξ)
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ r₁)]
    refine Real.sqrt_le_sqrt ?_
    have hsq : r₁ ^ 2 ≤ ξ i ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hi.le 2
      rwa [sq_abs] at this
    have hle : ξ i * ξ i ≤ vecDot ξ ξ :=
      Finset.single_le_sum (f := fun j => ξ j * ξ j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    nlinarith
  · have : vecDot (-ξ) (-ξ) = vecDot ξ ξ := by
      unfold vecDot
      simp only [Pi.neg_apply, neg_mul_neg]
    simp only [this]
  · apply Real.smoothTransition.one_of_one_le
    have hle2 : vecDot ξ ξ ≤ r₀ ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
      rwa [Real.sq_sqrt (vecDot_self_nonneg ξ)] at this
    rw [le_div_iff₀ hd]
    linarith

/-- **A low cutoff exists** when `ξ_lo > 0`. -/
theorem lowCutoffExists : LowCutoffExistsStatement := by
  intro K hξ
  obtain ⟨χ, hs, -, he, h1, h0⟩ := radialCutoff_exists hξ (by linarith : K.ξlo < 2 * K.ξlo)
  exact ⟨χ, ⟨hs, he, h1, h0⟩⟩

end AVRegularity.CycleWords.Seam
end
end

section
/-! # Tools for the assembly of the kernel clauses

* `ScalarPackage.inWindow`: the full package on the regions cut to its window (the extra fields
  involve only the marks and the actual fibre data, which `inWindow` keeps).
* `isWordBlock_of_seam`: the block hypotheses make a word block on the window regions (the hypotheses give
  quietness only on `reg.quiet ∩ [t_F, t_F + S]`).
* `seamFutureKernel_of_theta`, `seamFutureKernel_of_not_wellBuffered`, `seamFutureKernel_apply`.
* `seam_reserve_le`: the fast reserve of the retained statements at output weight `p_out` is at
  most `σ.Jstar`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- **The full package on the regions cut to its window.** -/
def ScalarPackage.inWindow {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : ScalarPackage K η G v t₀ S ϖ reg) : ScalarPackage K η G v t₀ S ϖ (reg.inWindow t₀ S) :=
  { pkg.toCoreScalarPackage.inWindow with
    gauss := pkg.gauss
    phase_jets := pkg.phase_jets
    marks_in := pkg.marks_in
    marks_sep := pkg.marks_sep
    marks_count := pkg.marks_count
    high_marks := pkg.high_marks }

end AVRegularity

namespace AVRegularity.CycleWords.Seam

open AVRegularity.CycleWords.Assembly

section Block

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The future letters are a word block** on the regions cut to the window. -/
theorem isWordBlock_of_seam {K : ScalarConstants} {g₁ : ℝ} {D Nw H J : ℕ} (hD : 2 ≤ D)
    {π : ι → ℝ} (hπ : ∀ x, 0 < π x) {letters : Fin Nw → CycleLetter ι h D}
    {η S ηg ϖ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hS : 1 ≤ S) (hηg : 0 < ηg) (hηg1 : ηg ≤ 1)
    (hϖ : ϖ = Real.sqrt (η / S)) {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {g : ℝ} (hGm : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j)
    (hg0 : 0 ≤ g) (hg : g ≤ K.g0) (hg₁ : g ≤ g₁)
    (hGn : IsMetricNearIdentity (fun t _ => G t) g) {reg : BlockRegions} {t₀ : ℝ}
    (hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc t₀ (t₀ + S) ×ˢ Set.univ) J H)
    (htrans : ∀ i, IsTransverseOnPulses (letters i).edge
      (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient)
    (hquiet : ∀ i, IsQuietOn (letters i).edge v (reg.quiet ∩ Set.Icc t₀ (t₀ + S)))
    (hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) :
    IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g (reg.inWindow t₀ S) where
  hD := hD
  hπ := hπ
  hη := hη
  hη1 := hη1
  hS := hS
  hηg := hηg
  hηg1 := hηg1
  hϖ := hϖ
  hGm := hGm
  hv := hv
  hv0 := hv0
  hvs := hvs
  hvw := hvw
  hvj := hvj
  hg0 := hg0
  hg := hg
  hg₁ := hg₁
  hGn := hGn
  hlet := hlet
  htrans := fun i => (htrans i).inWindow t₀ S
  hquiet := hquiet
  hmeas := hmeas

end Block

/-- The fast reserve of the retained statements of the future block at output weight `p_out`. -/
theorem seam_reserve_le (σ : SeamShape) {m : ℕ} (hm : m ≤ σ.pout) :
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m σ.KsF) σ.dF) σ.dF ≤ σ.Jstar := by
  have hsup : Finset.univ.sup σ.dF ≤ max (Finset.univ.sup σ.dO) (Finset.univ.sup σ.dF) :=
    le_max_right _ _
  unfold wordReserveJstar wordReserveKstar wordReserveN SeamShape.Jstar
  omega

section Kernel

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Np : ℕ}
  {K : ScalarConstants} {χlo : Vec 2 → ℝ} {n : ℕ} {μ : Vec 2 → ℝ} (hμ : IsSeamLowPass μ)
  {π : ι → ℝ} {letters : Fin Np → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ}
  {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2} {c₁ : ℝ} {Q₁ : ℕ}
  {reg : BlockRegions}

include hμ in
theorem seamFutureKernel_of_theta (hΘ : wordTheta ηg letters = 0) :
    seamFutureKernel K χlo n hμ π letters η S ηg t₀ ϖ G v X₀ c₁ Q₁ reg = 0 := by
  unfold seamFutureKernel
  split_ifs
  rfl

include hμ in
theorem seamFutureKernel_of_not_wellBuffered (hW : ¬IsWellBuffered c₁ Q₁ η S reg) :
    seamFutureKernel K χlo n hμ π letters η S ηg t₀ ϖ G v X₀ c₁ Q₁ reg = 0 := by
  unfold seamFutureKernel
  split_ifs <;> rfl

include hμ in
theorem seamFutureKernel_apply (hΘ : wordTheta ηg letters ≠ 0)
    (hW : IsWellBuffered c₁ Q₁ η S reg) (g : ∀ x, Vec 2 → h x)
    (hg : ∀ x, MemLp (g x) 2 volume) :
    seamFutureKernel K χlo n hμ π letters η S ηg t₀ ϖ G v X₀ c₁ Q₁ reg g =
      retainedMap K (fun ξ => χlo ξ ^ (n + 1)) π letters η S ηg t₀ ϖ G v X₀
        (fun x => fourierCutoff μ (g x)) := by
  unfold seamFutureKernel
  split_ifs with h1
  · exact absurd h1 hΘ
  have hspec := (LinearMap.exists_extend
    (seamLowRetained K χlo n hμ π letters η S ηg t₀ ϖ G v X₀)).choose_spec
  exact congrFun (congrArg DFunLike.coe hspec) ⟨g, hg⟩

end Kernel

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Tools for the assembly

* `s3b_reserve_le`: the reserve of the future block with `K_max + k` output and negative orders and
  `p_out` moments is within `σ.Jstar`.
* `s3b_weightedJetNorm_rescale`: the weighted output norm at derivative scale `r` is at most
  `(r/r₀)^M` times the norm at the scale `r₀ ≤ r`; the constants of the discard and of the quiet margin
  are taken at `C_out = 1`, so that their power `Q` does not depend on `C_out`.
* `s3b_quiet_margin_quiet`: the entrance quiet margin is quiet for the regions cut to the window. -/

section
open AVRegularity.CycleWords.Assembly

/-- The reserve of the future block with `K_max + k` orders and `p_out` moments. -/
theorem s3b_reserve_le (σ : SeamShape) {Kf m : ℕ} (hKf : Kf ≤ σ.Kmax + σ.k) (hm : m ≤ σ.pout) :
    wordReserveJstar (wordReserveKstar Kf (wordReserveN m σ.KsF) σ.dF) σ.dF ≤ σ.Jstar := by
  have hsup : Finset.univ.sup σ.dF ≤ max (Finset.univ.sup σ.dO) (Finset.univ.sup σ.dF) :=
    le_max_right _ _
  unfold wordReserveJstar wordReserveKstar wordReserveN SeamShape.Jstar
  omega

/-- **Rescaling the derivative scale.** -/
theorem s3b_weightedJetNorm_rescale {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (M : ℕ) (s : ℝ) {r₀ r : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    weightedJetNorm π p M s r J ≤ ENNReal.ofReal ((r / r₀) ^ M) * weightedJetNorm π p M s r₀ J := by
  unfold weightedJetNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have haM : a ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hq0 : 0 ≤ (r / r₀) ^ M := pow_nonneg (div_nonneg (hr₀.le.trans hr) hr₀.le) M
  rw [← mul_assoc, ← ENNReal.ofReal_mul hq0]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h1 : 1 ≤ r / r₀ := (one_le_div hr₀).2 hr
  have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hra : r ^ a = (r / r₀) ^ a * r₀ ^ a := by
    rw [← mul_pow, div_mul_cancel₀ _ hr₀.ne']
  rw [hra, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 haM) (by positivity)

/-- The entrance quiet margin is quiet for the regions cut to the window. -/
theorem s3b_quiet_margin_quiet {reg : BlockRegions} {t₀ S a : ℝ} (haS : a ≤ S)
    (hq : Set.Icc t₀ (t₀ + a) ⊆ reg.quiet) :
    Set.Icc t₀ (t₀ + a) ⊆ (reg.inWindow t₀ S).quiet := by
  rw [BlockRegions.inWindow_quiet]
  exact fun t ht => ⟨hq ht, ht.1, by linarith [ht.2]⟩

/-- The constant of the well-buffered regime. -/
theorem s3b_scalar_good {Θ P S Db a B CD CC C₅ C₁ C₅' cD cC c : ℝ} {QD QC Q₁ : ℕ}
    (hΘ : 0 ≤ Θ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hDb : 0 ≤ Db) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hCD : 0 ≤ CD) (hCC : 0 ≤ CC) (hC₅ : 0 ≤ C₅) (hC₁ : 0 ≤ C₁) (hC₅' : 0 ≤ C₅')
    (hcD : c ≤ cD) (hcC : c ≤ cC) :
    CD * Θ * P ^ QD * (1 + S) ^ QD * (Real.exp (-cD * S) + (1 + B) * Real.exp (-cD * Db)) * C₅ +
        CC * Θ * P ^ QC * (1 + S) ^ QC * (Real.exp (-cC * a) * (1 + C₁ * C₅)) ≤
      (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * Θ * P ^ (QD + QC + Q₁) *
        (1 + S) ^ (QD + QC + Q₁) *
        (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) := by
  set A := Θ * P ^ (QD + QC + Q₁) * (1 + S) ^ (QD + QC + Q₁) with hA
  have hA0 : 0 ≤ A := by positivity
  have hPD : P ^ QD ≤ P ^ (QD + QC + Q₁) := pow_le_pow_right₀ hP (by omega)
  have hPC : P ^ QC ≤ P ^ (QD + QC + Q₁) := pow_le_pow_right₀ hP (by omega)
  have hSD : (1 + S) ^ QD ≤ (1 + S) ^ (QD + QC + Q₁) := pow_le_pow_right₀ (by linarith) (by omega)
  have hSC : (1 + S) ^ QC ≤ (1 + S) ^ (QD + QC + Q₁) := pow_le_pow_right₀ (by linarith) (by omega)
  have hAD : Θ * P ^ QD * (1 + S) ^ QD ≤ A := by
    rw [hA]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPD hΘ) hSD (by positivity) (by positivity)
  have hAC : Θ * P ^ QC * (1 + S) ^ QC ≤ A := by
    rw [hA]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPC hΘ) hSC (by positivity) (by positivity)
  have he1 : Real.exp (-cD * S) ≤ Real.exp (-c * S) := Real.exp_le_exp.2 (by nlinarith)
  have he2 : Real.exp (-cD * Db) ≤ Real.exp (-c * Db) := Real.exp_le_exp.2 (by nlinarith)
  have he3 : Real.exp (-cC * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
  have hT1 : Real.exp (-cD * S) + (1 + B) * Real.exp (-cD * Db) ≤
      Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) :=
    add_le_add he1 (mul_le_mul_of_nonneg_left he2 (by linarith))
  have hE1 : 0 ≤ Real.exp (-cD * S) + (1 + B) * Real.exp (-cD * Db) := by positivity
  have hT1' : 0 ≤ Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) := by positivity
  have h1 : CD * Θ * P ^ QD * (1 + S) ^ QD *
      (Real.exp (-cD * S) + (1 + B) * Real.exp (-cD * Db)) * C₅ ≤
      CD * C₅ * A * (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db)) := by
    calc _ = CD * C₅ * (Θ * P ^ QD * (1 + S) ^ QD) *
          (Real.exp (-cD * S) + (1 + B) * Real.exp (-cD * Db)) := by ring
      _ ≤ CD * C₅ * A * (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hAD (by positivity)) hT1 hE1 (by positivity)
  have h2 : CC * Θ * P ^ QC * (1 + S) ^ QC * (Real.exp (-cC * a) * (1 + C₁ * C₅)) ≤
      CC * (1 + C₁ * C₅) * A * Real.exp (-c * a) := by
    calc _ = CC * (1 + C₁ * C₅) * (Θ * P ^ QC * (1 + S) ^ QC) * Real.exp (-cC * a) := by ring
      _ ≤ CC * (1 + C₁ * C₅) * A * Real.exp (-c * a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hAC (by positivity)) he3 (by positivity)
            (by positivity)
  have hrhs : (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * Θ * P ^ (QD + QC + Q₁) *
      (1 + S) ^ (QD + QC + Q₁) *
      (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) =
      (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * A *
        ((Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db)) + Real.exp (-c * a)) := by
    rw [hA]
    ring
  rw [hrhs]
  have hea : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCD hC₅) hA0) hT1',
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ CC * (1 + C₁ * C₅)) hA0) hea,
    mul_nonneg (mul_nonneg (mul_nonneg hCD hC₅) hA0) hea,
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ CC * (1 + C₁ * C₅)) hA0) hT1',
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ CC * (1 + C₅')) hA0) hT1',
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ CC * (1 + C₅')) hA0) hea]

/-- The constant of the regimes with zero kernel (`Θ₊ = 0`, or a block that is not well
buffered). -/
theorem s3b_scalar_zero {Θ P S Db a B CD CC C₅ C₁ C₅' cC c c₁ : ℝ} {QD QC Q₁ : ℕ}
    (hΘ : 0 ≤ Θ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hDb : 0 ≤ Db) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hCD : 0 ≤ CD) (hCC : 0 ≤ CC) (hC₅ : 0 ≤ C₅) (hC₁ : 0 ≤ C₁) (hC₅' : 0 ≤ C₅')
    (hcC : 0 ≤ cC) (hc₁ : c ≤ c₁)
    (hcase : Θ = 0 ∨ 1 < (1 + B) * P ^ Q₁ * (1 + S) ^ Q₁ * Real.exp (-c₁ * Db)) :
    CC * Θ * P ^ QC * (1 + S) ^ QC * (Real.exp (-cC * a) + C₅') ≤
      (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * Θ * P ^ (QD + QC + Q₁) *
        (1 + S) ^ (QD + QC + Q₁) *
        (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) := by
  have hRHS : 0 ≤ (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * Θ * P ^ (QD + QC + Q₁) *
      (1 + S) ^ (QD + QC + Q₁) *
      (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) := by positivity
  rcases hcase with h0 | hpoor
  · rw [h0]
    simp only [mul_zero, zero_mul]
    simp
  set A := Θ * P ^ (QD + QC + Q₁) * (1 + S) ^ (QD + QC + Q₁) with hA
  have hea : Real.exp (-cC * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hX0 : 0 ≤ CC * Θ * P ^ QC * (1 + S) ^ QC * (1 + C₅') := by positivity
  have hPQ : P ^ QC * P ^ Q₁ ≤ P ^ (QD + QC + Q₁) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hP (by omega)
  have hSQ : (1 + S) ^ QC * (1 + S) ^ Q₁ ≤ (1 + S) ^ (QD + QC + Q₁) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have he : Real.exp (-c₁ * Db) ≤ Real.exp (-c * Db) := Real.exp_le_exp.2 (by nlinarith)
  calc CC * Θ * P ^ QC * (1 + S) ^ QC * (Real.exp (-cC * a) + C₅')
      ≤ CC * Θ * P ^ QC * (1 + S) ^ QC * (1 + C₅') :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ CC * Θ * P ^ QC * (1 + S) ^ QC * (1 + C₅') *
          ((1 + B) * P ^ Q₁ * (1 + S) ^ Q₁ * Real.exp (-c₁ * Db)) :=
        le_mul_of_one_le_right hX0 hpoor.le
    _ = CC * (1 + C₅') * (1 + B) * Real.exp (-c₁ * Db) * Θ *
          (P ^ QC * P ^ Q₁) * ((1 + S) ^ QC * (1 + S) ^ Q₁) := by ring
    _ ≤ CC * (1 + C₅') * (1 + B) * Real.exp (-c * Db) * Θ *
          P ^ (QD + QC + Q₁) * (1 + S) ^ (QD + QC + Q₁) := by
        gcongr
    _ = CC * (1 + C₅') * A * ((1 + B) * Real.exp (-c * Db)) := by rw [hA]; ring
    _ ≤ _ := by
        rw [show (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * Θ * P ^ (QD + QC + Q₁) *
            (1 + S) ^ (QD + QC + Q₁) *
            (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) =
            (CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅')) * A *
              (Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a)) by
          rw [hA]; ring]
        have hA0 : 0 ≤ A := by positivity
        have h1 : CC * (1 + C₅') ≤ CD * C₅ + CC * (1 + C₁ * C₅) + CC * (1 + C₅') := by
          have : 0 ≤ CD * C₅ + CC * (1 + C₁ * C₅) := by positivity
          linarith
        have h2 : (1 + B) * Real.exp (-c * Db) ≤
            Real.exp (-c * S) + (1 + B) * Real.exp (-c * Db) + Real.exp (-c * a) := by
          have := Real.exp_pos (-c * S)
          have := Real.exp_pos (-c * a)
          linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hA0) h2 (by positivity) (by positivity)

/-- The final constant: rescaling, the output constant and the bound on compact data. -/
theorem s3b_final_le {W W₀ NNn NNp Bc : ℝ≥0∞} {ρ ρmax C₃ β : ℝ} (hρm : ρ ≤ ρmax) (hC₃ : 0 ≤ C₃)
    (hβ : 0 ≤ β) (h1 : W ≤ ENNReal.ofReal ρ * W₀) (h2 : W₀ ≤ ENNReal.ofReal C₃ * (Bc * NNn))
    (h3 : Bc ≤ ENNReal.ofReal β) (h4 : NNn ≤ NNp) :
    W ≤ ENNReal.ofReal (C₃ * ρmax * β) * NNp := by
  refine h1.trans ?_
  calc ENNReal.ofReal ρ * W₀
      ≤ ENNReal.ofReal ρmax * (ENNReal.ofReal C₃ * (ENNReal.ofReal β * NNp)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hρm) (h2.trans (mul_le_mul_right
          (mul_le_mul' h3 h4) _))
    _ = _ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul' hC₃, ← ENNReal.ofReal_mul' hβ]
        ring_nf

/-- The rescaling factor of the derivative scale. -/
theorem s3b_ratio_le {r C : ℝ} (hr : 0 < r) (hrC : r ≤ C) (M : ℕ) :
    (r / min r 1) ^ M ≤ (max 1 C) ^ M := by
  have h0 : 0 < min r 1 := lt_min hr one_pos
  refine pow_le_pow_left₀ (div_nonneg hr.le h0.le) ?_ M
  rcases le_total r 1 with h | h
  · rw [min_eq_left h, div_self hr.ne']
    exact le_max_left _ _
  · rw [min_eq_right h, div_one]
    exact hrC.trans (le_max_right _ _)

/-- The bound on compact data of the well-buffered regime, in `ℝ≥0∞`. -/
theorem s3b_enn_good {x₁ x₂ ea C₁ C₅ β : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hea : 0 ≤ ea)
    (hC₁ : 0 ≤ C₁) (hC₅ : 0 ≤ C₅) (h : x₁ * C₅ + x₂ * (ea * (1 + C₁ * C₅)) ≤ β) :
    ENNReal.ofReal x₁ * ENNReal.ofReal C₅ + ENNReal.ofReal x₂ *
      (ENNReal.ofReal ea * (1 + ENNReal.ofReal C₁ * ENNReal.ofReal C₅)) ≤ ENNReal.ofReal β := by
  rw [← ENNReal.ofReal_mul hx₁, ← ENNReal.ofReal_mul hC₁, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_mul hea,
    ← ENNReal.ofReal_mul hx₂, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The bound on compact data of the zero-kernel regime, in `ℝ≥0∞`. -/
theorem s3b_enn_zero {x₂ ea C₅' β : ℝ} (hx₂ : 0 ≤ x₂) (hea : 0 ≤ ea) (hC₅' : 0 ≤ C₅')
    (h : x₂ * (ea + C₅') ≤ β) :
    ENNReal.ofReal x₂ * (ENNReal.ofReal ea + ENNReal.ofReal C₅') ≤ ENNReal.ofReal β := by
  rw [← ENNReal.ofReal_add hea hC₅', ← ENNReal.ofReal_mul hx₂]
  exact ENNReal.ofReal_le_ofReal h
end

/-! # The cosine and sine transforms of an integrable plane field

`phaseTransform ψ H θ = ∫ ψ(θ·y) H(y) dy` for a phase `ψ` (`cos` or `sin`): the radian transform of the
field `H`, in the real form used by the Bloch fibres and by the retained amplitudes.

A finite moment norm with two more moments makes the moments integrable
(`integrable_bracket_of_momentNorm`): `⟨z⟩⁻² ∈ L²(ℝ²)`. -/

section
open AVRegularity.CycleWords.Assembly

/-- The transform `∫ ψ(θ·y) H(y) dy` of a plane field against the phase `ψ`. -/
def phaseTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : ℝ → ℝ) (H : Vec 2 → E)
    (θ : Vec 2) : E :=
  ∫ y, ψ (vecDot θ y) • H y

/-- `⟨z⟩⁻² ∈ L²(ℝ²)`. -/
theorem memLp_inv_jbracket_sq : MemLp (fun z : Vec 2 => (jbracket z ^ 2)⁻¹) 2 volume := by
  have hc : Continuous fun z : Vec 2 => (jbracket z ^ 2)⁻¹ :=
    (jbracket_contDiff.continuous.pow 2).inv₀ fun z => (pow_pos (jbracket_pos z) 2).ne'
  rw [memLp_two_iff_integrable_sq hc.aestronglyMeasurable]
  have hfr : (Module.finrank ℝ (Vec 2) : ℝ) < 4 := by
    simp only [Module.finrank_pi, Fintype.card_fin, Nat.cast_ofNat]
    norm_num
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Vec 2) (μ := volume) hfr
  refine hint.mono' (hc.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have hj : jbracket z ^ 2 = 1 + (z 0 ^ 2 + z 1 ^ 2) := by
    unfold jbracket
    exact Real.sq_sqrt (by positivity)
  have hn : ‖z‖ ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
    have h0 : ‖z‖ = max |z 0| |z 1| := by
      rw [Pi.norm_def]
      have : (Finset.univ : Finset (Fin 2)) = {0, 1} := by ext i; fin_cases i <;> simp
      rw [this]
      simp [NNReal.coe_max, Finset.sup_insert]
    rw [h0]
    rcases le_total |z 0| |z 1| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg (z 0)]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg (z 1)]
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hj, inv_pow,
    show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num, Real.rpow_neg hpos.le,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le (by linarith) 2)

section Moments

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **Two more moments in `L²` give integrable moments.** -/
theorem integrable_bracket_of_momentNorm {π : ι → ℝ} {n : ℕ} {s : ℝ} (hs : 0 < s)
    {F : ∀ v, Vec 2 → h v} (hF : momentNorm π (n + 2) s F < ⊤) {v : ι} (hv : 0 < π v)
    (hFm : AEStronglyMeasurable (F v) volume) :
    Integrable (fun z => jbracket z ^ n • F v z) volume := by
  have h2 := memLp_bracket_of_momentNorm hF hv hFm
  simp only [hs.ne', ↓reduceIte] at h2
  have h1 := memLp_inv_jbracket_sq.smul h2 (r := 1)
  rw [memLp_one_iff_integrable] at h1
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  have hj := (jbracket_pos z).ne'
  simp only [Pi.smul_apply', smul_smul]
  congr 1
  rw [pow_add]
  field_simp

end Moments
end

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Calculus of the transform of a field with integrable moments

For a unit phase `ψ` (`cos`, `sin` and their derivatives) and a field `H` with `n` integrable
moments (`HasIntegrableMoments n H`), the transform `phaseTransform ψ H θ = ∫ ψ(θ·y) H(y) dy` is `C^n` in `θ`
(`Trans_contDiff`) and its ordered derivatives are the transforms of the moments
(`Trans_orderedDerivative`): `D^w phaseTransform ψ H = phaseTransform ψ^{(a)} (y^w H)`.

The pair of the `cos` and `sin` transforms keeps its size under differentiating the phases
(`Trans_pair_iteratedDeriv`). -/

open AVRegularity.CycleWords.Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field with `n` integrable moments: `⟨y⟩^n H ∈ L¹`. -/
def HasIntegrableMoments (n : ℕ) (H : Vec 2 → E) : Prop :=
  AEStronglyMeasurable H volume ∧ Integrable (fun y => jbracket y ^ n • H y) volume

theorem HasIntegrableMoments.mono {n m : ℕ} {H : Vec 2 → E} (h : HasIntegrableMoments n H) (hm : m ≤ n) : HasIntegrableMoments m H := by
  refine ⟨h.1, h.2.mono ((jbracket_contDiff.continuous.pow m).aestronglyMeasurable.smul h.1)
    (Eventually.of_forall fun y => ?_)⟩
  have hj := one_le_jbracket y
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (jbracket_pos y).le m),
    abs_of_nonneg (pow_nonneg (jbracket_pos y).le n)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj hm) (norm_nonneg _)

theorem HasIntegrableMoments.integrable {n : ℕ} {H : Vec 2 → E} (h : HasIntegrableMoments n H) : Integrable H volume := by
  have h0 := (h.mono (Nat.zero_le n)).2
  simpa only [pow_zero, one_smul] using h0

/-- A coordinate costs one moment. -/
theorem HasIntegrableMoments.coord {n : ℕ} {H : Vec 2 → E} (h : HasIntegrableMoments (n + 1) H) (k : Fin 2) :
    HasIntegrableMoments n (fun y => y k • H y) := by
  have hck : Continuous fun y : Vec 2 => y k := continuous_apply k
  have hm : AEStronglyMeasurable (fun y : Vec 2 => y k • H y) volume :=
    hck.aestronglyMeasurable.smul h.1
  refine ⟨hm, h.2.mono ((jbracket_contDiff.continuous.pow n).aestronglyMeasurable.smul hm)
    (Eventually.of_forall fun y => ?_)⟩
  have hk := abs_coord_le_jbracket y k
  rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (jbracket_pos y).le n),
    abs_of_nonneg (pow_nonneg (jbracket_pos y).le (n + 1)), pow_succ, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk (pow_nonneg (jbracket_pos y).le n)) (norm_nonneg _)

/-- A word monomial of degree `j` costs `j` moments. -/
theorem HasIntegrableMoments.monomial : ∀ {j : ℕ} (w : DerivativeWord2 j) {n : ℕ} {H : Vec 2 → E},
    HasIntegrableMoments (n + j) H → HasIntegrableMoments n (fun y => wordMonomial w y • H y)
  | 0, w, n, H, h => by
    have he : (fun y : Vec 2 => wordMonomial w y • H y) = H := by
      funext y
      simp [wordMonomial]
    rw [he]
    exact h
  | j + 1, w, n, H, h => by
    have h1 : HasIntegrableMoments (n + 1) (fun y => wordMonomial (fun i : Fin j => w i.castSucc) y • H y) :=
      HasIntegrableMoments.monomial (fun i : Fin j => w i.castSucc) (by rwa [add_assoc, add_comm 1 j])
    have he : (fun y : Vec 2 => wordMonomial w y • H y) =
        fun y => y (w (Fin.last j)) • (wordMonomial (fun i : Fin j => w i.castSucc) y • H y) := by
      funext y
      rw [wordMonomial_succ, smul_smul]
    rw [he]
    exact h1.coord _

theorem HasIntegrableMoments.const_smul {n : ℕ} {H : Vec 2 → E} (h : HasIntegrableMoments n H) (c : ℝ) :
    HasIntegrableMoments n (fun y => c • H y) := by
  refine ⟨h.1.const_smul c, (h.2.smul c).congr (Eventually.of_forall fun y => ?_)⟩
  simp only [Pi.smul_apply, smul_comm c]

theorem isUnitPhase_deriv {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) : IsUnitPhase (deriv ψ) := by
  refine ⟨(contDiff_infty_iff_deriv.1 hψ.1).2, fun j t => ?_⟩
  rw [← iteratedDeriv_succ']
  exact hψ.2 (j + 1) t

theorem isUnitPhase_iteratedDeriv {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) :
    ∀ a : ℕ, IsUnitPhase (iteratedDeriv a ψ)
  | 0 => by rwa [iteratedDeriv_zero]
  | a + 1 => by
    rw [iteratedDeriv_succ]
    exact isUnitPhase_deriv (isUnitPhase_iteratedDeriv hψ a)

theorem isUnitPhase_continuous_comp {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (θ : Vec 2) :
    Continuous fun y : Vec 2 => ψ (vecDot θ y) :=
  hψ.1.continuous.comp (by unfold vecDot; fun_prop)

/-- The integrand of the transform is integrable. -/
theorem Trans_integrand_integrable {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : Integrable H volume) (θ : Vec 2) :
    Integrable (fun y => ψ (vecDot θ y) • H y) volume :=
  integrable_bdd_smul (isUnitPhase_continuous_comp hψ θ) (fun _ => hψ.abs_le _) hH

theorem Trans_norm_le {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : Integrable H volume) (θ : Vec 2) : ‖phaseTransform ψ H θ‖ ≤ ∫ y, ‖H y‖ := by
  unfold phaseTransform
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hH.norm
      (Eventually.of_forall fun y => ?_))
  change ‖ψ (vecDot θ y) • H y‖ ≤ ‖H y‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hψ.abs_le _)

theorem Trans_const_smul (ψ : ℝ → ℝ) (c : ℝ) (H : Vec 2 → E) (θ : Vec 2) :
    phaseTransform ψ (fun y => c • H y) θ = c • phaseTransform ψ H θ := by
  unfold phaseTransform
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_comm c]

theorem Trans_const_mul (ψ : ℝ → ℝ) (c : ℝ) (H : Vec 2 → E) (θ : Vec 2) :
    phaseTransform (fun t => c * ψ t) H θ = c • phaseTransform ψ H θ := by
  unfold phaseTransform
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_smul]

/-- The transform of an integrable field is continuous. -/
theorem Trans_continuous {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : Integrable H volume) : Continuous (phaseTransform ψ H) := by
  unfold phaseTransform
  refine continuous_of_dominated (bound := fun y => ‖H y‖)
    (fun θ => (Trans_integrand_integrable hψ hH θ).aestronglyMeasurable)
    (fun θ => Eventually.of_forall fun y => ?_) hH.norm
    (Eventually.of_forall fun y => ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψ.abs_le _)
  · exact (hψ.1.continuous.comp (by unfold vecDot; fun_prop)).smul continuous_const

variable [CompleteSpace E]

/-- The derivative in `θ` of the integrand of the transform. -/
def IntegrandDeriv (ψ' : ℝ → ℝ) (H : Vec 2 → E) (θ y : Vec 2) : Vec 2 →L[ℝ] E :=
  ∑ k : Fin 2, coordSmulRight k (ψ' (vecDot θ y) • (y k • H y))

omit [CompleteSpace E] in
theorem hasFDerivAt_integrand {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (H : Vec 2 → E)
    (θ y : Vec 2) :
    HasFDerivAt (fun θ => ψ (vecDot θ y) • H y) (IntegrandDeriv (deriv ψ) H θ y) θ := by
  have hd : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t =>
    (hψ.1.differentiable (by simp) t).hasDerivAt
  refine ((hasFDerivAt_phase_comp hd y θ).smul_const (H y)).congr_fderiv
    (ContinuousLinearMap.ext fun v => ?_)
  simp [IntegrandDeriv, coordSmulRight_apply, phaseCLM_apply, vecDot, Fin.sum_univ_two]
  module

omit [CompleteSpace E] in
theorem integrable_integrandTerm {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : HasIntegrableMoments 1 H) (θ : Vec 2) (k : Fin 2) :
    Integrable (fun y => deriv ψ (vecDot θ y) • (y k • H y)) volume :=
  Trans_integrand_integrable (isUnitPhase_deriv hψ) (hH.coord k).integrable θ

omit [CompleteSpace E] in
theorem integrable_integrandDeriv {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : HasIntegrableMoments 1 H) (θ : Vec 2) :
    Integrable (fun y => IntegrandDeriv (deriv ψ) H θ y) volume := by
  unfold IntegrandDeriv
  refine integrable_finsetSum (f := fun k y => coordSmulRight (E := E) k
    (deriv ψ (vecDot θ y) • (y k • H y))) Finset.univ fun k _ => ?_
  exact (coordSmulRight (E := E) k).integrable_comp (integrable_integrandTerm hψ hH θ k)

omit [CompleteSpace E] in
theorem norm_integrandDeriv_le {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) (H : Vec 2 → E)
    (θ y : Vec 2) : ‖IntegrandDeriv (deriv ψ) H θ y‖ ≤ 2 * (jbracket y * ‖H y‖) := by
  unfold IntegrandDeriv
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k : Fin 2, ‖coordSmulRight k (deriv ψ (vecDot θ y) • (y k • H y))‖ ≤
      jbracket y * ‖H y‖ := by
    intro k
    refine (norm_coordSmulRight_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |deriv ψ (vecDot θ y)| * (|y k| * ‖H y‖) ≤ 1 * (jbracket y * ‖H y‖) :=
          mul_le_mul ((isUnitPhase_deriv hψ).abs_le _)
            (mul_le_mul_of_nonneg_right (abs_coord_le_jbracket y k) (norm_nonneg _))
            (by positivity) zero_le_one
      _ = jbracket y * ‖H y‖ := one_mul _
  rw [Fin.sum_univ_two, two_mul]
  exact add_le_add (hterm 0) (hterm 1)

theorem integral_integrandDeriv {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : HasIntegrableMoments 1 H) (θ : Vec 2) :
    ∫ y, IntegrandDeriv (deriv ψ) H θ y =
      ∑ k : Fin 2, coordSmulRight k (phaseTransform (deriv ψ) (fun y => y k • H y) θ) := by
  unfold IntegrandDeriv
  rw [integral_finsetSum _ fun k _ => (coordSmulRight (E := E) k).integrable_comp
    (integrable_integrandTerm hψ hH θ k)]
  exact Finset.sum_congr rfl fun k _ =>
    (coordSmulRight (E := E) k).integral_comp_comm (integrable_integrandTerm hψ hH θ k)

/-- **Differentiation under the integral**: `∂_k phaseTransform ψ H = phaseTransform ψ' (y_k H)`. -/
theorem Trans_hasFDerivAt {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E} (hH : HasIntegrableMoments 1 H)
    (θ : Vec 2) :
    HasFDerivAt (phaseTransform ψ H)
      (∑ k : Fin 2, coordSmulRight k (phaseTransform (deriv ψ) (fun y => y k • H y) θ)) θ := by
  rw [← integral_integrandDeriv hψ hH θ]
  have hb : Integrable (fun y => 2 * (jbracket y * ‖H y‖)) volume := by
    have h1 := hH.2.norm
    simp only [pow_one, norm_smul, Real.norm_eq_abs] at h1
    refine (h1.const_mul 2).congr (Eventually.of_forall fun y => ?_)
    simp only [abs_of_pos (jbracket_pos y)]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (bound := fun y => 2 * (jbracket y * ‖H y‖)) Filter.univ_mem
    (Eventually.of_forall fun θ' =>
      (Trans_integrand_integrable hψ hH.integrable θ').aestronglyMeasurable)
    (Trans_integrand_integrable hψ hH.integrable θ)
    (integrable_integrandDeriv hψ hH θ).aestronglyMeasurable
    (Eventually.of_forall fun y θ' _ => norm_integrandDeriv_le hψ H θ' y) hb
    (Eventually.of_forall fun y θ' _ => hasFDerivAt_integrand hψ H θ' y)

theorem Trans_fderiv_basisVec {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {H : Vec 2 → E}
    (hH : HasIntegrableMoments 1 H) (θ : Vec 2) (k : Fin 2) :
    fderiv ℝ (phaseTransform ψ H) θ (basisVec k) = phaseTransform (deriv ψ) (fun y => y k • H y) θ := by
  rw [(Trans_hasFDerivAt hψ hH θ).fderiv]
  fin_cases k <;> simp [coordSmulRight_apply, basisVec_apply, Fin.sum_univ_two]

/-- **Smoothness** of the transform of a field with `n` integrable moments. -/
theorem Trans_contDiff : ∀ (n : ℕ) {ψ : ℝ → ℝ}, IsUnitPhase ψ → ∀ {H : Vec 2 → E},
    HasIntegrableMoments n H → ContDiff ℝ n (phaseTransform ψ H)
  | 0, ψ, hψ, H, hH => by
    rw [Nat.cast_zero, contDiff_zero]
    exact Trans_continuous hψ hH.integrable
  | n + 1, ψ, hψ, H, hH => by
    have h1 : HasIntegrableMoments 1 H := hH.mono (Nat.le_add_left 1 n)
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2 ⟨fun θ => (Trans_hasFDerivAt hψ h1 θ).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have hf : fderiv ℝ (phaseTransform ψ H) = fun θ =>
        ∑ k : Fin 2, coordSmulRight k (phaseTransform (deriv ψ) (fun y => y k • H y) θ) :=
      funext fun θ => (Trans_hasFDerivAt hψ h1 θ).fderiv
    rw [hf]
    exact ContDiff.sum fun k _ => (coordSmulRight (E := E) k).contDiff.comp
      (Trans_contDiff n (isUnitPhase_deriv hψ) (hH.coord k))

/-- **Ordered derivatives of the transform are the transforms of the moments.** -/
theorem Trans_orderedDerivative : ∀ {a : ℕ} (w : DerivativeWord2 a) {ψ : ℝ → ℝ},
    IsUnitPhase ψ → ∀ {H : Vec 2 → E}, HasIntegrableMoments a H →
    orderedDerivative w (phaseTransform ψ H) =
      phaseTransform (iteratedDeriv a ψ) (fun y => wordMonomial w y • H y)
  | 0, w, ψ, _, H, _ => by
    rw [AVRegularity.orderedDerivative_zero, iteratedDeriv_zero]
    have he : (fun y : Vec 2 => wordMonomial w y • H y) = H := by
      funext y
      simp [wordMonomial]
    rw [he]
  | a + 1, w, ψ, hψ, H, hH => by
    have hK : HasIntegrableMoments 1 (fun y => wordMonomial (fun i : Fin a => w i.castSucc) y • H y) :=
      HasIntegrableMoments.monomial (fun i : Fin a => w i.castSucc) (by rwa [add_comm 1 a])
    rw [AVRegularity.orderedDerivative_succ,
      Trans_orderedDerivative (fun i : Fin a => w i.castSucc) hψ (hH.mono (Nat.le_succ a))]
    funext θ
    rw [Trans_fderiv_basisVec (isUnitPhase_iteratedDeriv hψ a) hK θ, iteratedDeriv_succ]
    congr 1
    funext y
    rw [wordMonomial_succ, smul_smul]

omit [CompleteSpace E] in
/-- **The pair of the transforms keeps its size under differentiating the phases.** -/
theorem Trans_pair_iteratedDeriv (K : Vec 2 → E) (θ : Vec 2) (j : ℕ) :
    ‖phaseTransform (iteratedDeriv j Real.cos) K θ‖ ^ 2 +
        ‖phaseTransform (iteratedDeriv j Real.sin) K θ‖ ^ 2 =
      ‖phaseTransform Real.cos K θ‖ ^ 2 + ‖phaseTransform Real.sin K θ‖ ^ 2 := by
  have hmul : ∀ (c : ℝ) (ψ : ℝ → ℝ), phaseTransform ((fun _ => c) * ψ) K θ = c • phaseTransform ψ K θ :=
    fun c ψ => Trans_const_mul ψ c K θ
  have hc : ∀ n : ℕ, ((-1 : ℝ → ℝ) ^ n) = fun _ => (-1 : ℝ) ^ n := fun n => by
    funext t
    simp
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_even_sin, hc, hmul, hmul, norm_smul,
      norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, one_mul]
  · rw [Real.iteratedDeriv_odd_cos, Real.iteratedDeriv_odd_sin, hc, hc, hmul, hmul, norm_smul,
      norm_smul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, one_mul, one_mul,
      add_comm]

end AVRegularity.CycleWords.Seam
end
end
