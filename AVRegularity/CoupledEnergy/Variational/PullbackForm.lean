-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Strong temporal convergence of contracting spectral projections. The
fixed domination argument covers the L¹ source and the L² Sobolev trajectory. -/

variable {T H : Type*} [MeasurableSpace T] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Contracting projections converging strongly pointwise have vanishing L¹ temporal tails. -/
theorem contractingProjection_integral_norm_sub_tendsto (μ : Measure T)
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : Integrable u μ) :
    Tendsto (fun n => ∫ r, ‖P n (u r) - u r‖ ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun r => ‖P n (u r) - u r‖) μ :=
    ((P n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable |>.sub
      hu.aestronglyMeasurable).norm
  have hb (n : ℕ) : ∀ᵐ r ∂μ, ‖‖P n (u r) - u r‖‖ ≤ 2 * ‖u r‖ := by
    filter_upwards [] with r
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith [hp n (u r)])
  have ht (r : T) : Tendsto (fun n => ‖P n (u r) - u r‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using ((hlim (u r)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u r) atTop (𝓝 (u r)))).norm
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun r => 2 * ‖u r‖) hm (hu.norm.const_mul 2) hb (Eventually.of_forall ht)

/-- Contracting projections converging strongly pointwise have vanishing L² temporal tails. -/
theorem contractingProjection_integral_normSq_sub_tendsto (μ : Measure T)
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ r, ‖P n (u r) - u r‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun r => ‖P n (u r) - u r‖ ^ 2) μ :=
    (((P n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable).sub
      hu.aestronglyMeasurable).norm.pow 2
  have hi : Integrable (fun r => ‖u r‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hb (n : ℕ) : ∀ᵐ r ∂μ, ‖‖P n (u r) - u r‖ ^ 2‖ ≤ 4 * ‖u r‖ ^ 2 := by
    filter_upwards [] with r
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hn : ‖P n (u r) - u r‖ ≤ 2 * ‖u r‖ :=
      (norm_sub_le _ _).trans (by linarith [hp n (u r)])
    nlinarith [norm_nonneg (P n (u r) - u r), norm_nonneg (u r)]
  have ht (r : T) : Tendsto (fun n => ‖P n (u r) - u r‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((hlim (u r)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u r) atTop (𝓝 (u r)))).norm.pow 2)
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun r => 4 * ‖u r‖ ^ 2) hm (hi.const_mul 4) hb (Eventually.of_forall ht)

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
namespace AVRegularity.CoupledEnergy.Variational

/-! Extract a component identity from a finite family by a single supported
test. Kept independent of Sobolev carriers. -/

theorem finiteComponent_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, Zero (E i)] (L R : ∀ i, E i → ℝ)
    (hL : ∀ i, L i 0 = 0) (hR : ∀ i, R i 0 = 0)
    (hfamily : ∀ φ : ∀ i, E i, (∑ i, L i (φ i)) = ∑ i, R i (φ i))
    (i : ι) (φ : E i) : L i φ = R i φ := by
  have hsum (S : ∀ i, E i → ℝ) (hS : ∀ i, S i 0 = 0) :
      (∑ j, S j (Pi.single i φ j)) = S i φ := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, hS]
    · simp
  simpa only [hsum L hL, hsum R hR] using hfamily (Pi.single i φ)

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergy.Variational

/-! Scalar finite-form calculus without Sobolev instance inference. -/

theorem finiteSpatialForm_integrable_and_integral {X J : Type*} [MeasurableSpace X]
    [Fintype J] {R : J → Type*} [∀ j, Fintype (R j)] (μ : Measure X) (ν : ℝ)
    (D : X → ℝ) (V : Fin 2 → X → ℝ) (C : ∀ j, R j → X → ℝ) (F g : X → ℝ)
    (hD : Integrable D μ) (hV : ∀ k, Integrable (V k) μ)
    (hC : ∀ j d, Integrable (C j d) μ) (hF : Integrable F μ) (hg : Integrable g μ) :
    Integrable (fun x => -ν * D x - (∑ k, V k x) - (∑ j, ∑ d, C j d x) - F x + g x) μ ∧
    (∫ x, -ν * D x - (∑ k, V k x) - (∑ j, ∑ d, C j d x) - F x + g x ∂μ) =
      -ν * (∫ x, D x ∂μ) - (∑ k, ∫ x, V k x ∂μ) - (∑ j, ∑ d, ∫ x, C j d x ∂μ) -
        (∫ x, F x ∂μ) + (∫ x, g x ∂μ) := by
  have hv := integrable_finsetSum Finset.univ (fun k _ => hV k)
  have hcj (j : J) := integrable_finsetSum Finset.univ (fun d _ => hC j d)
  have hc := integrable_finsetSum Finset.univ (fun j _ => hcj j)
  have hi := ((((hD.const_mul (-ν)).sub hv).sub hc).sub hF).add hg
  refine ⟨by simpa only [Pi.add_apply, Pi.sub_apply] using! hi, ?_⟩
  have he0 := integral_add ((((hD.const_mul (-ν)).sub hv).sub hc).sub hF) hg
  have he1 := integral_sub (((hD.const_mul (-ν)).sub hv).sub hc) hF
  have he2 := integral_sub ((hD.const_mul (-ν)).sub hv) hc
  have he3 := integral_sub (hD.const_mul (-ν)) hv
  simp only [Pi.sub_apply] at he0 he1 he2 he3
  rw [he0, he1, he2, he3, integral_const_mul,
    integral_finsetSum Finset.univ (fun k _ => hV k),
    integral_finsetSum Finset.univ (fun j _ => hcj j)]
  simp_rw [integral_finsetSum Finset.univ (fun d _ => hC _ d)]

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
open Filter Function Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Sequential weak compactness in Hilbert spaces, and its continuous-linear-map companion. -/

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence whose inner products converge against every test vector. -/
theorem exists_strictMono_tendsto_inner_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
  let f : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) R := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
    simpa using hu n
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
  let v : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
  refine ⟨v, φ, hφ, fun z => ?_⟩
  simpa [f, v, Function.comp_def] using
    ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem exists_strictMono_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v)) := by
  obtain ⟨v, φ, hφ, hinner⟩ := exists_strictMono_tendsto_inner_of_norm_le u R hu
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

/-- A uniform Hilbert norm bound survives convergence of all scalar pairings. -/
theorem norm_le_of_tendsto_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {u : ℕ → H} {v : H} {R : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hlim : ∀ z : H, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z))) :
    ‖v‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (hu 0)
  have hp : inner ℝ v v ≤ R * ‖v‖ :=
    le_of_tendsto (hlim v) (Eventually.of_forall (fun n =>
      (real_inner_le_norm (u n) v).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg v))))
  rw [real_inner_self_eq_norm_sq] at hp
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · simpa only [← hv] using hR
  · nlinarith

/-- A uniform Hilbert norm bound survives convergence against every continuous linear functional. -/
theorem norm_le_of_tendsto_clm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {u : ℕ → H} {v : H} {R : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hlim : ∀ ell : H →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v))) :
    ‖v‖ ≤ R := by
  apply norm_le_of_tendsto_inner hu
  intro z
  simpa only [innerSL_apply_apply, real_inner_comm] using hlim (innerSL ℝ z)

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergy.Variational

/-! Finite-sum temporal calculus, kept independent of the Sobolev instance
chain so that the native coupled forms elaborate cheaply. -/

/-- Split an integrable finite component form into its separately integrated terms. -/
theorem integratedFiniteForm_split {J : Type*} [Fintype J] {R : J → Type*}
    [∀ j, Fintype (R j)] {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (ν : ℝ) (D : ℝ → ℝ) (V : Fin 2 → ℝ → ℝ) (C : ∀ j, R j → ℝ → ℝ)
    (F g : ℝ → ℝ)
    (hD : Integrable D (volume.restrict (Set.Icc a b)))
    (hV : ∀ k, Integrable (V k) (volume.restrict (Set.Icc a b)))
    (hC : ∀ j d, Integrable (C j d) (volume.restrict (Set.Icc a b)))
    (hF : Integrable F (volume.restrict (Set.Icc a b)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    (∫ r in a..t, -ν * D r - (∑ k, V k r) - (∑ j, ∑ d, C j d r) - F r + g r) =
      -ν * (∫ r in a..t, D r) - (∑ k, ∫ r in a..t, V k r) -
        (∑ j, ∑ d, ∫ r in a..t, C j d r) - (∫ r in a..t, F r) + (∫ r in a..t, g r) := by
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have toII (f : ℝ → ℝ) (hf : Integrable f (volume.restrict (Set.Icc a b))) :
      IntervalIntegrable f volume a t :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf).mono_set hsub
  have hd := toII D hD
  have hv := toII _ (integrable_finsetSum Finset.univ (fun k _ => hV k))
  have hcj (j : J) := integrable_finsetSum Finset.univ (fun d _ => hC j d)
  have hc := toII _ (integrable_finsetSum Finset.univ (fun j _ => hcj j))
  have hf := toII F hF
  have hgg := toII g hg
  rw [intervalIntegral.integral_add ((((hd.const_mul (-ν)).sub hv).sub hc).sub hf) hgg,
    intervalIntegral.integral_sub (((hd.const_mul (-ν)).sub hv).sub hc) hf,
    intervalIntegral.integral_sub ((hd.const_mul (-ν)).sub hv) hc,
    intervalIntegral.integral_sub (hd.const_mul (-ν)) hv, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => toII _ (hV k)),
    intervalIntegral.integral_finsetSum (fun j _ => toII _ (hcj j))]
  simp_rw [intervalIntegral.integral_finsetSum (fun d _ => toII _ (hC _ d))]

/-! A full-interval integrable majorant controls all closed-time energy
increments uniformly, including merely L¹ forcing. -/

theorem intervalIntegral_le_full_majorant {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (q m : ℝ → ℝ) (hq : AEStronglyMeasurable q (volume.restrict (Set.Icc a b)))
    (hm : Integrable m (volume.restrict (Set.Icc a b)))
    (hb : ∀ᵐ r ∂volume.restrict (Set.Icc a b), |q r| ≤ m r) :
    (∫ r in a..t, q r) ≤ ∫ r in Set.Icc a b, m r := by
  have hi : Integrable q (volume.restrict (Set.Icc a b)) :=
    hm.mono' hq (by simpa only [Real.norm_eq_abs] using hb)
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hqI := IntegrableOn.mono_set hi hsub
  have hmI := IntegrableOn.mono_set hm hsub
  have hle : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), q r ≤ m r :=
    (ae_restrict_of_ae_restrict_of_subset hsub hb).mono (fun r hr => (le_abs_self _).trans hr)
  have hn : ∀ᵐ r ∂volume.restrict (Set.Icc a b), 0 ≤ m r :=
    hb.mono (fun r hr => (abs_nonneg _).trans hr)
  rw [intervalIntegral.integral_of_le ht.1]
  exact (integral_mono_ae hqI hmI hle).trans (setIntegral_mono_set hm hn (Filter.Eventually.of_forall (fun r hr => hsub hr)))

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! L¹ value forcing passes to strongly converging spatial tests. No L²
hypothesis on the value source is needed for these temporal pairings. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Pairing with the source primitive is a bounded spatial test functional. -/
def l1TimeTestIntegralCLM (g : ℝ → H) (a b : ℝ) : H →L[ℝ] ℝ :=
  innerSL ℝ (∫ r in a..b, g r)

/-- The primitive functional is the literal time integral against a fixed spatial test. -/
theorem l1TimeTestIntegralCLM_apply (g : ℝ → H) {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (z : H) :
    l1TimeTestIntegralCLM g a b z = ∫ r in a..b, inner ℝ (g r) z := by
  have h := (innerSL ℝ z).intervalIntegral_comp_comm hg
  simpa only [l1TimeTestIntegralCLM, innerSL_apply_apply, real_inner_comm] using h.symm

/-- Strong test convergence suffices for the paper's L¹ value forcing. -/
theorem l1TimeTest_integral_tendsto (g : ℝ → H) {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (z : ℕ → H) (w : H)
    (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in a..b, inner ℝ (g r) (z n)) atTop
      (𝓝 (∫ r in a..b, inner ℝ (g r) w)) := by
  simpa only [Function.comp_def, l1TimeTestIntegralCLM_apply g hg] using
    (l1TimeTestIntegralCLM g a b).continuous.continuousAt.tendsto.comp hz

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section

/-! # Lions representation

The abstract Hilbert-space representation theorem of Lions. It is the abstract input for the
whole-space parabolic Cauchy construction.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace AVRegularity.CoupledEnergy.Variational

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Lions representation theorem.** If `J` and `T` are linear maps into a real Hilbert space
and `⟪J φ, T φ⟫` controls `‖J φ‖²`, then every continuous functional of the form
`φ ↦ ⟪f, J φ⟫` is represented as `φ ↦ ⟪z, T φ⟫` by an element `z` in the closure of the range
of `J`. -/
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

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The flux tail paired with a time L² higher-order trajectory vanishes.
This dominated convergence step avoids changing the L¹ value source. -/

variable {T H Z : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z]

theorem contractingProjection_tail_product_integrable (μ : Measure T)
    (P : H →L[ℝ] H) (u : T → H) (hu : MemLp u 2 μ) (z : T → Z) (hz : MemLp z 2 μ) :
    Integrable (fun t => ‖P (u t) - u t‖ * ‖z t‖) μ :=
  ((P.lipschitzWith.comp_memLp (map_zero P) hu).sub hu).norm.integrable_mul hz.norm

theorem contractingProjection_integral_tail_product_tendsto (μ : Measure T)
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : MemLp u 2 μ) (z : T → Z) (hz : MemLp z 2 μ) :
    Tendsto (fun n => ∫ t, ‖P n (u t) - u t‖ * ‖z t‖ ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun t => ‖P n (u t) - u t‖ * ‖z t‖) μ :=
    (((P n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable).sub
      hu.aestronglyMeasurable).norm.mul hz.aestronglyMeasurable.norm
  have hi : Integrable (fun t => 2 * (‖u t‖ * ‖z t‖)) μ :=
    (hu.norm.integrable_mul hz.norm).const_mul 2
  have hb (n : ℕ) : ∀ᵐ t ∂μ, ‖‖P n (u t) - u t‖ * ‖z t‖‖ ≤ 2 * (‖u t‖ * ‖z t‖) := by
    apply Filter.Eventually.of_forall
    intro t
    rw [norm_mul, norm_norm, norm_norm]
    have hn : ‖P n (u t) - u t‖ ≤ 2 * ‖u t‖ :=
      (norm_sub_le _ _).trans (by linarith [hp n (u t)])
    calc
      _ ≤ (2 * ‖u t‖) * ‖z t‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  have ht (t : T) : Tendsto (fun n => ‖P n (u t) - u t‖ * ‖z t‖) atTop (𝓝 (0 : ℝ)) := by
    have hh := (((hlim (u t)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u t) atTop (𝓝 (u t)))).norm).mul_const ‖z t‖
    simpa only [sub_self, norm_zero, zero_mul] using hh
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun t => 2 * (‖u t‖ * ‖z t‖)) hm hi hb (Filter.Eventually.of_forall ht)

end AVRegularity.CoupledEnergy.Variational
end
end

section
/-! Pull back Hilbert pairings along linear trial and test maps. -/

@[expose] public noncomputable section

namespace AVRegularity.CoupledEnergy.Variational

variable {V W H : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Hilbert pairing pulled back to two algebraic trial spaces. -/
def pullbackInner (L : V →ₗ[ℝ] H) (R : W →ₗ[ℝ] H) : V →ₗ[ℝ] W →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => inner ℝ (L x) (R y)
      map_add' := by intro y z; simp [inner_add_right]
      map_smul' := by intro c y; simp [real_inner_smul_right] }
  map_add' := by intro x y; ext z; simp [inner_add_left]
  map_smul' := by intro c x; ext z; simp [real_inner_smul_left]

@[simp] theorem pullbackInner_apply (L : V →ₗ[ℝ] H) (R : W →ₗ[ℝ] H) (x : V) (y : W) :
    pullbackInner L R x y = inner ℝ (L x) (R y) := rfl

end AVRegularity.CoupledEnergy.Variational

@[expose] public noncomputable section

namespace AVRegularity.CoupledEnergy.Variational

variable {V W H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Continuous version of the pulled-back Hilbert pairing. -/
def pullbackInnerCLM (L : V →L[ℝ] H) (R : W →L[ℝ] H) :
    V →L[ℝ] W →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ W H ℝ).flip R).comp ((innerSL ℝ).comp L)

@[simp] theorem pullbackInnerCLM_apply (L : V →L[ℝ] H) (R : W →L[ℝ] H)
    (x : V) (y : W) : pullbackInnerCLM L R x y = inner ℝ (L x) (R y) := rfl

end AVRegularity.CoupledEnergy.Variational
end
end
end
