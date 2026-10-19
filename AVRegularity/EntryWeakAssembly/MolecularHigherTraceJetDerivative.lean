-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.WindowFieldExtension
public import AVRegularity.Analysis.Convolution.Kernel.PairedSource
import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.EntryWeak.MetricCloseEllipticity
public import AVRegularity.CycleEvolution.CellPeriodicSliceGraphFluxSlice
public import AVRegularity.EntryWeak.SourceLocalMetricCongruence
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Literal pointwise source bounds control their actual spatial Hilbert classes. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.CycleEvolution

local instance cellSourceSlicePointwiseBoundFiniteCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by rw [Measure.restrict_apply_univ, cellCube_volume_one]; exact ENNReal.one_lt_top⟩

theorem cellSourceSlice_norm_le_pointwise (f : ℝ → Vec 2 → ℂ) (t C : ℝ)
    (hm : Measurable (f t)) (hC : 0 ≤ C) (hb : ∀ z, ‖f t z‖ ≤ C) :
    ‖cellSourceSlice f t‖ ≤ C := by
  have hs : MemLp (f t) 2 (volume.restrict AVenhance.unitCube) :=
    MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  have he := cellSourceSlice_ae f t hs
  have hh := Lp.norm_le_of_ae_bound hC (he.mono (fun z hz => by rw [hz]; exact hb z))
  simpa [measureUnivNNReal, Measure.restrict_apply_univ, cellCube_volume_one] using hh

end AVRegularity.WeakEntryProofs
end
end

section
/-! Real scalar multiplication preserves the complete weak Hilbert trajectory. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem cellWeakHilbertCurve_const_smul {a b : ℝ}
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) (c : ℝ) :
    CellWeakHilbertCurve a b (fun t => c • u t) (fun t => c • slice t)
      (fun t => c • g t) := by
  refine ⟨h.trace.const_smul c, h.state.const_smul c, h.dual.const_smul c, ?_, ?_⟩
  · filter_upwards [h.agrees] with t ht
    rw [map_smul, ht]
  · intro s hs t ht hst z
    simp only [real_inner_smul_left, intervalIntegral.integral_const_mul]
    have hh := h.increment s hs t ht hst z
    calc
      _ = c * (inner ℝ (u t) (torusHkValueCLM z) -
          inner ℝ (u s) (torusHkValueCLM z)) := by ring
      _ = _ := congrArg (fun x : ℝ => c * x) hh

end AVRegularity.WeakEntryProofs
end
end

section
/-! On an interval between consecutive odd centers, the cutoff has exactly two possible terms. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem oddCutoff_pair_sum (k : ℤ) (x : ℝ) (hl : (k : ℝ) ≤ x) (hr : x ≤ (k : ℝ) + 2) :
    Real.smoothTransition (5 / 2 - 2 * |x - k|) +
      Real.smoothTransition (5 / 2 - 2 * |x - (k + 2 : ℤ)|) = 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonpos (by push_cast; linarith)]
  apply smoothTransition_pair
  push_cast
  ring

theorem oddCutoff_off_pair (k j : ℤ) (hk : Odd k) (hj : Odd j)
    (hne : j ≠ k) (hne' : j ≠ k + 2) (x : ℝ)
    (hl : (k : ℝ) ≤ x) (hr : x ≤ (k : ℝ) + 2) :
    Real.smoothTransition (5 / 2 - 2 * |x - j|) = 0 := by
  have hgap : j ≤ k - 2 ∨ k + 4 ≤ j := by
    obtain ⟨a, ha⟩ := hk
    obtain ⟨b, hb⟩ := hj
    omega
  apply Real.smoothTransition.zero_of_nonpos
  rcases hgap with hgap | hgap
  · have hg : (j : ℝ) ≤ (k : ℝ) - 2 := by exact_mod_cast hgap
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hg : (k : ℝ) + 4 ≤ (j : ℝ) := by exact_mod_cast hgap
    rw [abs_of_nonpos (by linarith)]
    linarith

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal odd-slot glue cutoffs form a partition of unity on the entire time axis. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

open scoped BigOperators

theorem oddCutoff_finsum_between (k : ℤ) (hk : Odd k) (x : ℝ)
    (hl : (k : ℝ) ≤ x) (hr : x ≤ (k : ℝ) + 2) :
    ∑ᶠ j : OddSlot, Real.smoothTransition (5 / 2 - 2 * |x - j.1|) = 1 := by
  classical
  have hk' : Odd (k + 2) := by obtain ⟨n, hn⟩ := hk; exact ⟨n + 1, by omega⟩
  let p : OddSlot := ⟨k, hk⟩
  let q : OddSlot := ⟨k + 2, hk'⟩
  let f : OddSlot → ℝ := fun j => Real.smoothTransition (5 / 2 - 2 * |x - j.1|)
  have hpq : p ≠ q := by intro h; have := congrArg Subtype.val h; dsimp [p, q] at this; omega
  have hs : Function.support f ⊆ (↑({p, q} : Finset OddSlot) : Set OddSlot) := by
    intro j hj
    by_cases hjp : j = p
    · simp only [hjp, Finset.mem_coe, Finset.mem_insert, true_or]
    by_cases hjq : j = q
    · simp only [hjq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, or_true]
    exfalso
    apply hj
    exact oddCutoff_off_pair k j.1 hk j.2 (fun h => hjp (Subtype.ext h))
      (fun h => hjq (Subtype.ext h)) x hl hr
  rw [finsum_eq_sum_of_support_subset f hs, Finset.sum_pair hpq]
  exact oddCutoff_pair_sum k x hl hr

theorem oddCutoff_finsum (x : ℝ) :
    ∑ᶠ j : OddSlot, Real.smoothTransition (5 / 2 - 2 * |x - j.1|) = 1 := by
  let n : ℤ := ⌊(x - 1) / 2⌋
  have hlo : (n : ℝ) ≤ (x - 1) / 2 := Int.floor_le _
  have hhi : (x - 1) / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  apply oddCutoff_finsum_between (2 * n + 1) ⟨n, rfl⟩ x
  · push_cast
    linarith only [hlo]
  · push_cast
    linarith only [hhi]

end AVRegularity.WeakEntryProofs
end
end

section
/-! The weak stage's actual temporal weights sum to one, with no renormalization. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem ocCutoff_normalized (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m)
    (k : ℤ) (t : ℝ) :
    ocCutoff α q Λ m k t =
      Real.smoothTransition (5 / 2 - 2 * |t / ocTau α q Λ m - k|) := by
  unfold ocCutoff
  have he : (t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m =
      t / ocTau α q Λ m - k := by
    rw [sub_div, mul_div_cancel_right₀ _ hτ.ne']
  have ha : |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m =
      |t / ocTau α q Λ m - k| := by
    have ha := congrArg abs he
    rw [abs_div, abs_of_pos hτ] at ha
    exact ha
  rw [mul_div_assoc, ha]

theorem ocCutoff_finsum_one (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m) (t : ℝ) :
    ∑ᶠ p : OddSlot, ocCutoff α q Λ m p.1 t = 1 := by
  simp_rw [ocCutoff_normalized α q Λ m hτ]
  exact oddCutoff_finsum _

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual weak temporal weights vanish off their natural output intervals. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem ocCutoff_zero_off_output (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m)
    (k : ℤ) (t : ℝ) (ht : t ∉ ocPulseWindow α q Λ m k) :
    ocCutoff α q Λ m k t = 0 := by
  by_contra hn
  have hp : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    by_contra h
    exact hn (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  have hm : 2 * |t - (k : ℝ) * ocTau α q Λ m| < (5 / 2) * ocTau α q Λ m :=
    (div_lt_iff₀ hτ).mp (by linarith only [hp])
  have hd : |t - (k : ℝ) * ocTau α q Λ m| < (61 / 48) * ocTau α q Λ m := by
    linarith only [hm, hτ]
  rw [abs_lt] at hd
  apply ht
  constructor <;> linarith only [hd.1, hd.2]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Every bounded time window meets finitely many natural weak output pieces. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

theorem weak_output_locally_finite (α q : ℝ) (Λ m : ℕ) (hτ : 0 < ocTau α q Λ m)
    (a b : ℝ) :
    Set.Finite {p : OddSlot | (ocPulseWindow α q Λ m p.1 ∩ Set.Icc a b).Nonempty} := by
  let lo : ℝ := a / ocTau α q Λ m - 61 / 48
  let hi : ℝ := b / ocTau α q Λ m + 61 / 48
  let S : Set ℤ := Set.Icc (Int.ceil lo) (Int.ceil hi)
  have hf : S.Finite := Set.finite_Icc _ _
  have hp : Set.Finite ((fun p : OddSlot => p.1) ⁻¹' S) :=
    hf.preimage (fun _ _ _ _ h => Subtype.ext h)
  apply hp.subset
  intro p hmem
  obtain ⟨t, ht, hab⟩ := hmem
  have hl : lo ≤ (p.1 : ℝ) := by
    have hh : a ≤ ((p.1 : ℝ) + 61 / 48) * ocTau α q Λ m := hab.1.trans ht.2
    have hh' := (div_le_iff₀ hτ).mpr hh
    dsimp [lo]
    linarith only [hh']
  have hr : (p.1 : ℝ) ≤ hi := by
    have hh : ((p.1 : ℝ) - 61 / 48) * ocTau α q Λ m ≤ b := ht.1.trans hab.2
    have hh' := (le_div_iff₀ hτ).mpr hh
    dsimp [hi]
    linarith only [hh']
  exact ⟨Int.ceil_le.mpr hl, Int.cast_le.mp (hr.trans (Int.le_ceil hi))⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! **The forcing cost, step 1: the factorial gain of `I - S_w`** (shift `L`).

For the isotropic paired kernel `S_w = isoPairedKernel r n` of width `r ≤ ρ` and a jet `f` of order
`K + L + j` whose value is `u`, every `Y` of order `K + j` whose value is `u - S_w u` satisfies
`|∇^j Y|²_{ρ,K} ≤ (D (r/ρ)^L)² |∇^j f|²_{ρ,K+L}` (`exists_pfc_derivFactorial_gain`), for
`L < 2 n` and a constant `D` depending only on `φ₀, n, L, K` (not on `j`'s data, `r`, `ρ`).
* `exists_pfc_value_approx`: the value estimate `‖u - S_w u‖ ≤ c (r/ρ)^L |u|_{ρ,L}` (for `L = 0`
  by contraction, for `L > 0` by the paired moment approximation).
* `pfc_diff_jet`: the jets of `Y` are `(I - S_w)` of the jets of `f` (`S_w` commutes with
  derivatives, `derivative_pairedWeakSmoothing_torus`). -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
  AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.WeakEntryProofs

/-- The isotropic Hilbert matrix `2^{-1/2} I` of the weak paired kernel. -/
def pfcH : HilbertTwo ≃L[ℝ] HilbertTwo :=
  (LinearEquiv.smulOfNeZero ℝ HilbertTwo (Real.sqrt 2)⁻¹
    (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne')).toContinuousLinearEquiv

theorem pfcH_toCLM : (pfcH : HilbertTwo →L[ℝ] HilbertTwo) =
    (Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ HilbertTwo := by
  ext x : 1
  rfl

theorem pfcH_norm_le : ‖(pfcH : HilbertTwo →L[ℝ] HilbertTwo)‖ ≤ 1 := by
  rw [pfcH_toCLM, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (Real.sqrt_pos.mpr (by norm_num)))]
  have h1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  calc (Real.sqrt 2)⁻¹ * ‖ContinuousLinearMap.id ℝ HilbertTwo‖
      ≤ (Real.sqrt 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (inv_nonneg.mpr (by linarith))
    _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ h1

/-- The scaled spatial equivalence of the isotropic paired kernel of width `r`. -/
def pfcR (r : ℝ) (hr : 0 < r) : Vec 2 ≃L[ℝ] Vec 2 := scaledSpatialEquiv pfcH r hr.ne'

theorem pfcR_hom (r : ℝ) (hr : 0 < r) :
    (pfcR r hr).toLinearEquiv.toAddHom =
      displacement r ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) := by
  ext z : 1
  change scaledSpatialEquiv pfcH r hr.ne' z = _
  rw [scaledSpatialEquiv_apply]
  simp only [spatialHilbertOperator_apply]
  change r • coordinateHilbertEquiv (pfcH (coordinateHilbertEquiv.symm z)) = _
  have : pfcH (coordinateHilbertEquiv.symm z) = (Real.sqrt 2)⁻¹ • coordinateHilbertEquiv.symm z := rfl
  rw [this, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rfl

section Smoothing

variable {φ₀ : Vec 2 → ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The paired weak smoothing of the isotropic kernel of width `r`, as a torus jet of order `N`. -/
def pfcG (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (z : Lp E 2 (volume.restrict AVenhance.unitCube)) : TorusHk N E :=
  pairedWeakSmoothingTorus (K := N) (pfcR r hr) (pfcR r hr) (momentKernel φ₀ n)
    (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
    (fun i => inverseColumnCoeff pfcH r i) (fun i => inverseRowCoeff pfcH r i)
    (inverse_column_scaled_spatial_coefficients pfcH pfcH pfcH rfl rfl hr) (cellToTorus z)

omit [FiniteDimensional ℝ E] in
theorem pfcG_value (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) (r : ℝ)
    (hr : 0 < r) (hφ : Integrable φ₀) (t : ℝ) (N : ℕ)
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    (pfcG hc hd n r hr N z).val (valueIndex2 N) = (isoPairedKernel r n).op φ₀ hφ t z :=
  kernelSpec_paired_realization_value φ₀ hφ hc hd (isoPairedKernel r n) t (pfcR r hr) (pfcR r hr)
    (pfcR_hom r hr) (pfcR_hom r hr) (fun i => inverseColumnCoeff pfcH r i)
    (fun i => inverseRowCoeff pfcH r i)
    (inverse_column_scaled_spatial_coefficients pfcH pfcH pfcH rfl rfl hr) N z

theorem pfcG_jet_aux (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) (r : ℝ)
    (hr : 0 < r) (hφ : Integrable φ₀) (t : ℝ) {L m : ℕ} (f : TorusHk m E)
    (w : DerivativeWord2 m) :
    (pfcG hc hd n r hr (L + m) (f.val (valueIndex2 m))).val
        (truncateJetIndex (Nat.le_add_left m L) (⟨⟨m, Nat.lt_succ_self m⟩, w⟩ : JetIndex2 m)) =
      (isoPairedKernel r n).op φ₀ hφ t (f.val ⟨⟨m, Nat.lt_succ_self m⟩, w⟩) := by
  have h := congrArg (fun g : TorusHk L E => g.val (valueIndex2 L))
    (derivative_pairedWeakSmoothing_torus (K := m) (L := L) (pfcR r hr) (pfcR r hr)
      (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
      (fun i => inverseColumnCoeff pfcH r i) (fun i => inverseRowCoeff pfcH r i)
      (inverse_column_scaled_spatial_coefficients pfcH pfcH pfcH rfl rfl hr) f w)
  simp only [derivativeTorusHk_apply, prefix_valueIndex_eq_top] at h
  exact h.trans (pfcG_value hc hd n r hr hφ t L _)

theorem pfcG_jet (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) (r : ℝ)
    (hr : 0 < r) (hφ : Integrable φ₀) (t : ℝ) {N m : ℕ} (hm : m ≤ N) (f : TorusHk N E)
    (w : DerivativeWord2 m) :
    (pfcG hc hd n r hr N (f.val (valueIndex2 N))).val
        (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : JetIndex2 N) =
      (isoPairedKernel r n).op φ₀ hφ t (f.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩) := by
  obtain ⟨L, rfl⟩ : ∃ L, N = L + m := ⟨N - m, by omega⟩
  exact pfcG_jet_aux hc hd n r hr hφ t (truncateTorusHk (Nat.le_add_left m L) f) w

theorem pfc_diff_jet (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+)
    (r : ℝ) (hr : 0 < r) (hφ : Integrable φ₀) (t : ℝ) {N M : ℕ} (hMN : M ≤ N)
    (f : TorusHk N E) (Y : TorusHk M E)
    (hY : Y.val (valueIndex2 M) =
      f.val (valueIndex2 N) - (isoPairedKernel r n).op φ₀ hφ t (f.val (valueIndex2 N)))
    {m : ℕ} (hm : m ≤ M) (w : DerivativeWord2 m) :
    Y.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ =
      f.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hMN)⟩, w⟩ -
        (isoPairedKernel r n).op φ₀ hφ t (f.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hMN)⟩, w⟩) := by
  have hYeq : Y = truncateTorusHk hMN f -
      truncateTorusHk hMN (pfcG hc hd n r hr N (f.val (valueIndex2 N))) := by
    apply TorusHk.ext_value
    rw [hY]
    change _ = f.val (valueIndex2 N) - (pfcG hc hd n r hr N (f.val (valueIndex2 N))).val
      (valueIndex2 N)
    rw [pfcG_value hc hd n r hr hφ t]
  rw [hYeq]
  have hj := pfcG_jet hc hd n r hr hφ t (hm.trans hMN) f w
  change f.val ⟨⟨m, _⟩, w⟩ - (pfcG hc hd n r hr N (f.val (valueIndex2 N))).val ⟨⟨m, _⟩, w⟩ = _
  rw [hj]

end Smoothing

theorem pfcH_symm_norm_le : ‖(pfcH.symm : HilbertTwo →L[ℝ] HilbertTwo)‖ ≤ 2 := by
  have h : (pfcH.symm : HilbertTwo →L[ℝ] HilbertTwo) =
      Real.sqrt 2 • ContinuousLinearMap.id ℝ HilbertTwo := by
    ext x : 1
    apply pfcH.injective
    change pfcH (pfcH.symm x) = (Real.sqrt 2)⁻¹ • Real.sqrt 2 • x
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num)).ne', one_smul]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
  have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  calc Real.sqrt 2 * ‖ContinuousLinearMap.id ℝ HilbertTwo‖ ≤ Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.sqrt_nonneg _)
    _ ≤ 2 := by rw [mul_one]; exact h2

theorem pfc_weight_mul_le (ρ : ℝ) (i l : ℕ) :
    factorialWeight ρ i * factorialWeight ρ l ≤ 4 ^ (i + l) * factorialWeight ρ (i + l) := by
  have hfac : ((i + l).factorial : ℝ) ≤ 2 ^ (i + l) * ((i.factorial : ℝ) * (l.factorial : ℝ)) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i l
    have hc : ((i + l).choose l : ℝ) ≤ 2 ^ (i + l) := by exact_mod_cast Nat.choose_le_two_pow _ _
    have h' : ((i + l).factorial : ℝ) = ((i + l).choose l : ℝ) * (i.factorial : ℝ) *
        (l.factorial : ℝ) := by exact_mod_cast h.symm
    rw [h', mul_assoc]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hsq : ((i + l).factorial : ℝ) ^ 2 ≤ 4 ^ (i + l) * ((i.factorial : ℝ) * (l.factorial : ℝ)) ^ 2 := by
    calc ((i + l).factorial : ℝ) ^ 2 ≤ (2 ^ (i + l) * ((i.factorial : ℝ) * (l.factorial : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hfac 2
      _ = 4 ^ (i + l) * ((i.factorial : ℝ) * (l.factorial : ℝ)) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (i + l) 2, pow_mul]; norm_num
  unfold factorialWeight
  have hp : ρ ^ (2 * i) * ρ ^ (2 * l) = ρ ^ (2 * (i + l)) := by rw [← pow_add]; ring_nf
  have hpos1 : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hpos2 : (0 : ℝ) < (l.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos l
  have hpos3 : (0 : ℝ) < ((i + l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_mul_div_comm, ← hp, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hρ : 0 ≤ ρ ^ (2 * i) * ρ ^ (2 * l) := by
    rw [hp, pow_mul]; positivity
  calc ρ ^ (2 * i) * ρ ^ (2 * l) * ((i + l).factorial : ℝ) ^ 2
      ≤ ρ ^ (2 * i) * ρ ^ (2 * l) * (4 ^ (i + l) * ((i.factorial : ℝ) * (l.factorial : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hρ
    _ = 4 ^ (i + l) * (ρ ^ (2 * i) * ρ ^ (2 * l)) * ((i.factorial : ℝ) ^ 2 * (l.factorial : ℝ) ^ 2) := by
        ring

/-- **The value approximation of the weak paired kernel**, with a gain `(r/ρ)^L`. -/
theorem exists_pfc_value_approx {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (r ρ : ℝ), 0 < r → r ≤ ρ → ∀ (t : ℝ) (g : TorusHk L E),
      ‖g.val (valueIndex2 L) - (isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 L))‖ ≤
        c * (r / ρ) ^ L * Real.sqrt (factorialNormSq ρ g.val) := by
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    refine ⟨2, by norm_num, ?_⟩
    intro E _ _ _ _ _ _ r ρ hr hrρ t g
    have hρ : 0 ≤ ρ := hr.le.trans hrρ
    have hcontract : ‖(isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 0))‖ ≤
        ‖g.val (valueIndex2 0)‖ := by
      have hG := pfcG_value hc hd n r hr hφ t 0 (g.val (valueIndex2 0))
      have hsq : factorialNormSq ρ (truncateTorusHk (le_refl 0)
          (pfcG hc hd n r hr 0 (g.val (valueIndex2 0)))).val ≤ factorialNormSq ρ g.val := by
        have := truncate_pairedWeakSmoothingTorus (le_refl 0) (pfcR r hr) (pfcR r hr)
          (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
          (fun i => inverseColumnCoeff pfcH r i) (fun i => inverseRowCoeff pfcH r i)
          (inverse_column_scaled_spatial_coefficients pfcH pfcH pfcH rfl rfl hr) g
        change factorialNormSq ρ (truncateTorusHk (le_refl 0) (pairedWeakSmoothingTorus
          (pfcR r hr) (pfcR r hr) (momentKernel φ₀ n) (hasCompactSupport_momentKernel hc n)
          (contDiff_momentKernel hc hd n) (fun i => inverseColumnCoeff pfcH r i)
          (fun i => inverseRowCoeff pfcH r i)
          (inverse_column_scaled_spatial_coefficients pfcH pfcH pfcH rfl rfl hr)
          (cellToTorus (g.val (valueIndex2 0))))).val ≤ _
        rw [this]
        exact (periodicWeakAverage_momentKernel_factorialNormSq
          (pfcR r hr).toLinearEquiv.toAddHom (pfcR r hr).continuous hφ hnonneg hmass n ρ _).trans
          (periodicWeakAverage_momentKernel_factorialNormSq
            (pfcR r hr).toLinearEquiv.toAddHom (pfcR r hr).continuous hφ hnonneg hmass n ρ g)
      rw [AVRegularity.Construction.Preservation.FullLift.factorialNormSq_order_zero,
        AVRegularity.Construction.Preservation.FullLift.factorialNormSq_order_zero] at hsq
      have hv : (truncateTorusHk (le_refl 0)
          (pfcG hc hd n r hr 0 (g.val (valueIndex2 0)))).val (valueIndex2 0) =
          (isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 0)) := hG
      rw [hv] at hsq
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    rw [AVRegularity.Construction.Preservation.FullLift.factorialNormSq_order_zero, Real.sqrt_sq (norm_nonneg _), pow_zero, mul_one]
    calc ‖g.val (valueIndex2 0) - (isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 0))‖
        ≤ ‖g.val (valueIndex2 0)‖ +
          ‖(isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 0))‖ := norm_sub_le _ _
      _ ≤ 2 * ‖g.val (valueIndex2 0)‖ := by linarith
  · refine ⟨2 * ∫ z : Vec 2, ‖momentKernel φ₀ n z‖, by positivity, ?_⟩
    obtain ⟨D, -, hD⟩ := exists_paired_source_smoothing_torus hc hd hnonneg hmass hsupp n L L
      le_rfl hLpos hL
    intro E _ _ _ _ _ _ r ρ hr hrρ t g
    have h3 := (hD E pfcH pfcH pfcH rfl rfl pfcH_symm_norm_le r ρ 1 hr hrρ zero_le_one
      pfcH_norm_le pfcH_norm_le g).2.2
    have hG := pfcG_value hc hd n r hr hφ t L (g.val (valueIndex2 L))
    have hv : (truncateTorusHk (le_refl L)
        (pfcG hc hd n r hr L (g.val (valueIndex2 L)))).val (valueIndex2 L) =
        (isoPairedKernel r n).op φ₀ hφ t (g.val (valueIndex2 L)) := hG
    have h3' : ‖g.val (valueIndex2 L) - (truncateTorusHk (le_refl L)
        (pfcG hc hd n r hr L (g.val (valueIndex2 L)))).val (valueIndex2 L)‖ ≤
        (2 * ∫ z : Vec 2, ‖momentKernel φ₀ n z‖) * 1 ^ L * (r / ρ) ^ L *
          Real.sqrt (factorialNormSq ρ g.val) := h3
    rw [hv, one_pow, mul_one] at h3'
    exact h3'

/-- **The derivative factorial gain of `I - S_w` with a shift `L`**: if `Y` has the
value `(I - S) u` and `f` has the value `u`, then
`|∇^j Y|²_{ρ,K} ≤ (D (r/ρ)^L)² |∇^j f|²_{ρ,K+L}`. -/
theorem exists_pfc_derivFactorial_gain {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ)) (K j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
      (r ρ : ℝ), 0 < r → r ≤ ρ → ∀ (t : ℝ) (f : TorusHk (K + L + j) E) (Y : TorusHk (K + j) E),
      Y.val (valueIndex2 (K + j)) = f.val (valueIndex2 (K + L + j)) -
        (isoPairedKernel r n).op φ₀ hφ t (f.val (valueIndex2 (K + L + j))) →
      derivFactorialNormSq j ρ Y.val ≤
        (D * (r / ρ) ^ L) ^ 2 * derivFactorialNormSq (K := K + L) j ρ f.val := by
  obtain ⟨c, hc0, hap⟩ := exists_pfc_value_approx hc hd hnonneg hmass hsupp hφ n L hL
  refine ⟨c * Real.sqrt (((K : ℝ) + 1) * 4 ^ (K + L)), by positivity, ?_⟩
  intro E _ _ _ _ _ _ r ρ hr hrρ t f Y hY
  have hρ : 0 ≤ ρ := hr.le.trans hrρ
  set Q : ℝ := (r / ρ) ^ L with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hterm : ∀ (i : Fin (K + 1)) (w : DerivativeWord2 (i.val + j)),
      ‖Y.val ⟨⟨i.val + j, by have := i.isLt; omega⟩, w⟩‖ ^ 2 ≤
        (c * Q) ^ 2 * factorialNormSq ρ (derivativeJet (K := L) w
          (truncateTorusHk (by have := i.isLt; omega : L + (i.val + j) ≤ K + L + j) f).val) := by
    intro i w
    have hm : i.val + j ≤ K + j := by have := i.isLt; omega
    have hMN : K + j ≤ K + L + j := by omega
    have hjet := pfc_diff_jet hc hd n r hr hφ t hMN f Y hY hm w
    set f' := truncateTorusHk (by have := i.isLt; omega : L + (i.val + j) ≤ K + L + j) f with hf'
    set g : TorusHk L E := derivativeTorusHk (K := L) w f' with hg
    have hgv : g.val (valueIndex2 L) =
        f.val ⟨⟨i.val + j, Nat.lt_succ_of_le (hm.trans hMN)⟩, w⟩ := by
      change f'.val (prefixJetIndex w (valueIndex2 L)) = _
      rw [prefix_valueIndex_eq_top]
      rfl
    have hb := hap E r ρ hr hrρ t g
    rw [hgv] at hb
    rw [hjet]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [← hQ] at hsq
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg ρ _)]
    rfl
  set A : Fin (K + L + 1) → ℝ := fun n => factorialWeight ρ n.val *
      derivativeNormSq f.val ⟨n.val + j, by have := n.isLt; omega⟩ with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n =>
    mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg _ _)
  have hRHS : derivFactorialNormSq (K := K + L) j ρ f.val = ∑ n, A n := rfl
  have h1 : derivFactorialNormSq j ρ Y.val ≤ (c * Q) ^ 2 * ∑ i : Fin (K + 1),
      factorialWeight ρ i.val * ∑ l : Fin (L + 1), factorialWeight ρ l.val *
        derivativeNormSq f.val ⟨(i.val + j) + l.val, by have := i.isLt; have := l.isLt; omega⟩ := by
    unfold derivFactorialNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc factorialWeight ρ i.val * ∑ w : DerivativeWord2 (i.val + j),
          ‖Y.val ⟨⟨i.val + j, by have := i.isLt; omega⟩, w⟩‖ ^ 2
        ≤ factorialWeight ρ i.val * ∑ w : DerivativeWord2 (i.val + j), (c * Q) ^ 2 *
            factorialNormSq ρ (derivativeJet (K := L) w
              (truncateTorusHk (by have := i.isLt; omega : L + (i.val + j) ≤ K + L + j) f).val) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hterm i w)
            (factorialWeight_nonneg ρ _)
      _ = (c * Q) ^ 2 * (factorialWeight ρ i.val * ∑ w : DerivativeWord2 (i.val + j),
            factorialNormSq ρ (derivativeJet (K := L) w
              (truncateTorusHk (by have := i.isLt; omega : L + (i.val + j) ≤ K + L + j) f).val)) := by
          rw [← Finset.mul_sum]; ring
      _ = _ := by
          rw [derivativeArray_factorialNormSq]
          rfl
  have hpt : ∀ (i : Fin (K + 1)) (l : Fin (L + 1)), factorialWeight ρ i.val *
      (factorialWeight ρ l.val * derivativeNormSq f.val
        ⟨(i.val + j) + l.val, by have := i.isLt; have := l.isLt; omega⟩) ≤
      4 ^ (K + L) * A ⟨i.val + l.val, by have := i.isLt; have := l.isLt; omega⟩ := by
    intro i l
    have hi := i.isLt
    have hl := l.isLt
    have hN := derivativeNormSq_nonneg f.val
      (⟨(i.val + j) + l.val, by omega⟩ : Fin (K + L + j + 1))
    have hidx : (⟨(i.val + j) + l.val, by omega⟩ : Fin (K + L + j + 1)) =
        ⟨(i.val + l.val) + j, by omega⟩ :=
      Fin.ext (by change (i.val + j) + l.val = (i.val + l.val) + j; omega)
    have hw := pfc_weight_mul_le ρ i.val l.val
    have h4 : (4 : ℝ) ^ (i.val + l.val) ≤ 4 ^ (K + L) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hw0 := factorialWeight_nonneg ρ (i.val + l.val)
    calc factorialWeight ρ i.val * (factorialWeight ρ l.val * derivativeNormSq f.val
          ⟨(i.val + j) + l.val, by omega⟩)
        = (factorialWeight ρ i.val * factorialWeight ρ l.val) *
            derivativeNormSq f.val ⟨(i.val + j) + l.val, by omega⟩ := by ring
      _ ≤ (4 ^ (i.val + l.val) * factorialWeight ρ (i.val + l.val)) *
            derivativeNormSq f.val ⟨(i.val + j) + l.val, by omega⟩ :=
          mul_le_mul_of_nonneg_right hw hN
      _ ≤ (4 ^ (K + L) * factorialWeight ρ (i.val + l.val)) *
            derivativeNormSq f.val ⟨(i.val + j) + l.val, by omega⟩ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hw0) hN
      _ = 4 ^ (K + L) * A ⟨i.val + l.val, by omega⟩ := by
          rw [hA]
          simp only []
          rw [hidx]
          ring
  have hsum : (∑ i : Fin (K + 1), factorialWeight ρ i.val * ∑ l : Fin (L + 1),
      factorialWeight ρ l.val * derivativeNormSq f.val
        ⟨(i.val + j) + l.val, by have := i.isLt; have := l.isLt; omega⟩) ≤
      ((K : ℝ) + 1) * 4 ^ (K + L) * ∑ n, A n := by
    calc _ = ∑ i : Fin (K + 1), ∑ l : Fin (L + 1), factorialWeight ρ i.val *
          (factorialWeight ρ l.val * derivativeNormSq f.val
            ⟨(i.val + j) + l.val, by have := i.isLt; have := l.isLt; omega⟩) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin (K + 1), ∑ l : Fin (L + 1), 4 ^ (K + L) *
            A ⟨i.val + l.val, by have := i.isLt; have := l.isLt; omega⟩ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hpt i l
      _ = ∑ i : Fin (K + 1), 4 ^ (K + L) * ∑ l : Fin (L + 1),
            A ⟨i.val + l.val, by have := i.isLt; have := l.isLt; omega⟩ := by
          simp_rw [← Finset.mul_sum]
      _ ≤ ∑ i : Fin (K + 1), 4 ^ (K + L) * ∑ n, A n := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_comp_le_sum_nonneg
            (fun l : Fin (L + 1) => (⟨i.val + l.val, by have := i.isLt; have := l.isLt; omega⟩ :
              Fin (K + L + 1)))
            (fun a b hab => Fin.ext (Nat.add_left_cancel (congrArg Fin.val hab))) A hA0
      _ = ((K : ℝ) + 1) * 4 ^ (K + L) * ∑ n, A n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [hRHS]
  calc derivFactorialNormSq j ρ Y.val ≤ _ := h1
    _ ≤ (c * Q) ^ 2 * (((K : ℝ) + 1) * 4 ^ (K + L) * ∑ n, A n) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (c * Real.sqrt (((K : ℝ) + 1) * 4 ^ (K + L)) * Q) ^ 2 * ∑ n, A n := by
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((K : ℝ) + 1) * 4 ^ (K + L) by positivity)
        have he : (c * Real.sqrt (((K : ℝ) + 1) * 4 ^ (K + L)) * Q) ^ 2 =
            c ^ 2 * (Real.sqrt (((K : ℝ) + 1) * 4 ^ (K + L))) ^ 2 * Q ^ 2 := by ring
        rw [he, hs]
        ring

end AVRegularity.WeakEntryProofs
end
end

section
/-! Restriction of actual global lift witnesses to the admissible weak carrier. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs

open Homogenization AVRegularity.Sobolev

theorem boxSmoothOn_of_boxSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set (Vec 2)) (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth sX sZ f) :
    IsBoxSmoothOn Ω sX sZ f :=
  ⟨fun X _ => hf.1 X, fun b hb z => (hf.2.1 b hb z).contDiffOn,
    fun a b ha hb => (hf.2.2 a b ha hb).continuousOn⟩

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequenceOn_of_global (Ω : Set (Vec 2)) (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc) : IsLiftSequenceOn Ω Q sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhh n m α v u t ht
    have hs := hc.2.2.2.2.2.1 hh hhh n m α v u t ht
    exact ⟨boxSmoothOn_of_boxSmooth Ω sX sZ _ hs.1, hs.2⟩
  · intro hh hhh n hn hnN a₀ ha₀ X _hX
    exact hc.2.2.2.2.2.2 hh hhh n hn hnN a₀ ha₀ X

end AVRegularity.WeakEntryProofs
end
end

section
/-! The actual finite source-flux coefficient is good from genuine edge and lift fields. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakSourceFlux_good_of_coefficients
    (Q : LiftOperatorData ι h D) (N : ℕ) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh j : ℕ) (k : Fin 2)
    (f : Vec 2 → ∀ i, h i)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    GoodField 1 (sourceFluxCoeff Q.edge Q.η j t
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k) := by
  have heps : EpsPoly False N D
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) := by
    refine ⟨fun i => liftApply i (Cc hh i) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
    · intro i
      exact ⟨hgood i, False.elim⟩
    · intro i hi Y z
      exact congrFun (congrFun (hcut i hi) Y) z
  exact sourceFlux_family_coefficient_good Q.edge Q.η t hΓ heps k j

end AVRegularity.WeakEntryProofs
end
end

section
/-! Localized full-cell lifts retain every lower slow and fast order. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev

theorem boxSmoothOn_order_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set (Vec 2)) {sX sZ rX rZ : ℕ} (hX : rX ≤ sX) (hZ : rZ ≤ sZ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmoothOn Ω sX sZ f) :
    IsBoxSmoothOn Ω rX rZ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hΩ
    exact (hf.1 X hΩ).of_le (by exact_mod_cast hZ)
  · intro b hb z
    exact (hf.2.1 b (hb.trans hZ) z).of_le (by exact_mod_cast hX)
  · intro a b ha hb
    exact hf.2.2 a b (ha.trans hX) (hb.trans hZ)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequenceOn_order_mono (Ω : Set (Vec 2)) (Q : LiftOperatorData ι h D)
    {sX sZ rX rZ : ℕ} (hX : rX ≤ sX) (hZ : rZ ≤ sZ) (a b : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc) :
    IsLiftSequenceOn Ω Q rX rZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhh n m α v u t ht
    have hs := hc.2.2.2.2.2.1 hh hhh n m α v u t ht
    exact ⟨boxSmoothOn_order_mono Ω hX hZ _ hs.1, hs.2⟩
  · intro hh hhh n hn hnN f hf X hΩ
    exact CycleComparison.Lift.cellFieldInverse_order_mono _ _ sZ rZ hZ a b 0 _ _
      (hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X hΩ)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Localized lift relations on the whole slow space recover the global relation. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev

theorem boxSmooth_of_boxSmoothOn_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sX sZ : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmoothOn Set.univ sX sZ f) :
    IsBoxSmooth sX sZ f := by
  refine ⟨fun X => hf.1 X (Set.mem_univ X), ?_, ?_⟩
  · intro b hb z
    exact contDiffOn_univ.mp (hf.2.1 b hb z)
  · intro a b ha hb
    have hc := hf.2.2 a b ha hb
    rw [Set.univ_prod_univ] at hc
    exact continuousOn_univ.mp hc

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_of_on_univ (Q : LiftOperatorData ι h D) (sX sZ : ℕ)
    (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequenceOn Set.univ Q sX sZ a b N H Cc) :
    IsLiftSequence Q sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhh n m α v u t ht
    have hs := hc.2.2.2.2.2.1 hh hhh n m α v u t ht
    exact ⟨boxSmooth_of_boxSmoothOn_univ sX sZ _ hs.1, hs.2⟩
  · intro hh hhh n hn hnN f hf X
    exact hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X (Set.mem_univ X)

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Square-integrable Taylor errors may be combined without losing energy convergence. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Set Filter Topology AVRegularity.CycleEvolution

theorem window_normSq_add_integral_le {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) (f g : ℝ → E)
    (hf : MemLp f 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    (∫ s in a..b, ‖f s + g s‖ ^ 2) ≤
      2 * ((∫ s in a..b, ‖f s‖ ^ 2) + ∫ s in a..b, ‖g s‖ ^ 2) := by
  have hi := (cellTime_normSq_intervalIntegrable hab hf).add
    (cellTime_normSq_intervalIntegrable hab hg)
  have h := intervalIntegral.integral_mono_on hab
    (cellTime_normSq_intervalIntegrable hab (hf.add hg)) (hi.const_mul 2) (fun s _ => by
      simp only [Pi.add_apply]
      have hn := norm_add_le (f s) (g s)
      have hs := mul_self_le_mul_self (norm_nonneg _) hn
      nlinarith [sq_nonneg (‖f s‖ - ‖g s‖)])
  simpa only [Pi.add_apply, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (cellTime_normSq_intervalIntegrable hab hf)
      (cellTime_normSq_intervalIntegrable hab hg)] using h

theorem window_normSq_add_integral_tendsto_zero {A E : Type*} [NormedAddCommGroup E]
    (l : Filter A) {a b : ℝ} (hab : a ≤ b) (f g : A → ℝ → E)
    (hf : ∀ X, MemLp (f X) 2 (volume.restrict (Icc a b)))
    (hg : ∀ X, MemLp (g X) 2 (volume.restrict (Icc a b)))
    (htf : Tendsto (fun X => ∫ s in a..b, ‖f X s‖ ^ 2) l (𝓝 0))
    (htg : Tendsto (fun X => ∫ s in a..b, ‖g X s‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun X => ∫ s in a..b, ‖f X s + g X s‖ ^ 2) l (𝓝 0) := by
  have hn (X : A) : 0 ≤ ∫ s in a..b, ‖f X s + g X s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
  have he (X : A) := window_normSq_add_integral_le hab (f X) (g X) (hf X) (hg X)
  have ht : Tendsto (fun X => 2 * ((∫ s in a..b, ‖f X s‖ ^ 2) +
      ∫ s in a..b, ‖g X s‖ ^ 2)) l (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (htf.add htg).const_mul 2
  exact squeeze_zero hn he ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniformly vanishing forcing bounds imply vanishing finite-window energy. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Set Filter Topology AVRegularity.CycleEvolution

theorem window_normSq_integral_tendsto_zero_of_bound {A E : Type*} [NormedAddCommGroup E]
    (l : Filter A) {a b : ℝ} (hab : a ≤ b) (f : A → ℝ → E)
    (hf : ∀ X, MemLp (f X) 2 (volume.restrict (Icc a b)))
    (C : A → ℝ)
    (hb : ∀ᶠ X in l, ∀ t ∈ Icc a b, ‖f X t‖ ≤ C X)
    (hc : Tendsto C l (𝓝 0)) :
    Tendsto (fun X => ∫ t in a..b, ‖f X t‖ ^ 2) l (𝓝 0) := by
  have hn (X : A) : 0 ≤ ∫ t in a..b, ‖f X t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have he : ∀ᶠ X in l, (∫ t in a..b, ‖f X t‖ ^ 2) ≤ (b - a) * C X ^ 2 := by
    filter_upwards [hb] with X hXt
    have hh := intervalIntegral.integral_mono_on hab
      (cellTime_normSq_intervalIntegrable hab (hf X))
      (continuous_const.intervalIntegrable a b) (fun t ht => by
        exact pow_le_pow_left₀ (norm_nonneg _) (hXt t ht) 2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  have ht : Tendsto (fun X => (b - a) * C X ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hc.pow 2).const_mul (b - a)
  exact squeeze_zero' (Eventually.of_forall hn) he ht

end AVRegularity.WeakEntryProofs
end
end

section
/-! Componentwise Taylor-error energies assemble into the literal molecular forcing budget. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Set Filter Topology AVRegularity.CycleEvolution

theorem window_forcing_budget_tendsto_zero {A E : Type*} [NormedAddCommGroup E]
    (l : Filter A) {a b : ℝ} (hab : a ≤ b) (initial : A → E)
    (S : A → ℝ → E) (F : A → ℝ → Fin 2 → E)
    (hS : ∀ X, MemLp (S X) 2 (volume.restrict (Icc a b)))
    (hF : ∀ X j, MemLp (fun t => F X t j) 2 (volume.restrict (Icc a b)))
    (hi : Tendsto (fun X => ‖initial X‖) l (𝓝 0))
    (hs : Tendsto (fun X => ∫ t in a..b, ‖S X t‖ ^ 2) l (𝓝 0))
    (hf : ∀ j, Tendsto (fun X => ∫ t in a..b, ‖F X t j‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun X => ‖initial X‖ ^ 2 + ∫ t in a..b,
      ‖S X t‖ ^ 2 + 4 * ∑ j, ‖F X t j‖ ^ 2) l (𝓝 0) := by
  have he (X : A) : (∫ t in a..b, ‖S X t‖ ^ 2 + 4 * ∑ j, ‖F X t j‖ ^ 2) =
      (∫ t in a..b, ‖S X t‖ ^ 2) +
        4 * ((∫ t in a..b, ‖F X t 0‖ ^ 2) + ∫ t in a..b, ‖F X t 1‖ ^ 2) := by
    have hj (j : Fin 2) := cellTime_normSq_intervalIntegrable hab (hF X j)
    simp only [Fin.sum_univ_two]
    rw [intervalIntegral.integral_add (cellTime_normSq_intervalIntegrable hab (hS X))
      (((hj 0).add (hj 1)).const_mul 4), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hj 0) (hj 1)]
  simpa only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_zero] using
    (hi.pow 2).add (hs.add (((hf 0).add (hf 1)).const_mul 4))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Finite sums preserve convergence of actual time-window forcing energies. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Set Filter Topology

theorem window_normSq_list_sum_integral_tendsto_zero {A E I : Type*}
    [NormedAddCommGroup E] (l : Filter A) {a b : ℝ} (hab : a ≤ b)
    (words : List I) (f : I → A → ℝ → E)
    (hm : ∀ i ∈ words, ∀ X, MemLp (f i X) 2 (volume.restrict (Icc a b)))
    (ht : ∀ i ∈ words, Tendsto (fun X => ∫ s in a..b, ‖f i X s‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun X => ∫ s in a..b, ‖((words.map (fun i => f i X)).sum) s‖ ^ 2)
      l (𝓝 0) := by
  have main :
      (∀ X, MemLp ((words.map (fun i => f i X)).sum) 2 (volume.restrict (Icc a b))) ∧
      Tendsto (fun X => ∫ s in a..b, ‖((words.map (fun i => f i X)).sum) s‖ ^ 2)
        l (𝓝 0) := by
    induction words with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact ⟨fun _ => MemLp.zero, by simpa using (tendsto_const_nhds (x := (0 : ℝ)))⟩
    | cons i words ih =>
      obtain ⟨hrest, hlimit⟩ := ih
        (fun j hj => hm j (List.mem_cons_of_mem i hj))
        (fun j hj => ht j (List.mem_cons_of_mem i hj))
      simp only [List.map_cons, List.sum_cons]
      refine ⟨fun X => (hm i List.mem_cons_self X).add (hrest X), ?_⟩
      simpa only [Pi.add_apply] using
        window_normSq_add_integral_tendsto_zero l hab _ _
          (hm i List.mem_cons_self) hrest (ht i List.mem_cons_self) hlimit
  exact main.2

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal full-cell source depends only on local primitive and predecessor germs. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev Set AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem fullCellSource_slow_local_primitive_congr {U : Set (Vec 2)} (hU : IsOpen U)
    (Q Q' : LiftOperatorData ι h D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hG : ∀ X ∈ U, Q.G t X = Q'.G t X) (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m ≤ q, ∀ α X, X ∈ U → ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    SlowOpenFieldEq U (liftCellSource Q Cc f hh n t) (liftCellSource Q' Dc f hh n t) := by
  have hQ : {Q with G := Q'.G, edge := Q'.edge} = Q' := by
    cases Q
    cases Q'
    simp_all
  intro X hX z
  calc
    liftCellSource Q Cc f hh n t X z =
        liftCellSource {Q with G := Q'.G} Cc f hh n t X z :=
      liftCellSource_metric_slow_open_congr hU Q Q'.G Cc f hh n t hG X hX z
    _ = liftCellSource {Q with G := Q'.G, edge := Q'.edge} Cc f hh n t X z :=
      liftCellSource_edge_slow_open_congr hU {Q with G := Q'.G} Q'.edge Cc f hh n t hΓ X hX z
    _ = liftCellSource Q' Cc f hh n t X z := by rw [hQ]
    _ = liftCellSource Q' Dc f hh n t X z :=
      liftCellSource_slow_open_congr_predecessors hU Q' Cc Dc f hh n hn t he X hX z

end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniform raw Taylor remainder bounds give vanishing Hilbert forcing energy on a finite window. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization Set Filter Topology AVRegularity.CycleEvolution

theorem cellSourceSlice_window_integral_tendsto_zero {A : Type*} (l : Filter A)
    {a b : ℝ} (hab : a ≤ b) (f : A → ℝ → Vec 2 → ℂ)
    (hm : ∀ X, Measurable (Function.uncurry (f X)))
    (hf : ∀ X, MemLp (Function.uncurry (f X)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (C : A → ℝ) (hC : ∀ᶠ X in l, 0 ≤ C X)
    (hb : ∀ᶠ X in l, ∀ t z, ‖f X t z‖ ≤ C X)
    (hc : Tendsto C l (𝓝 0)) :
    Tendsto (fun X => ∫ t in a..b, ‖cellSourceSlice (f X) t‖ ^ 2) l (𝓝 0) := by
  apply window_normSq_integral_tendsto_zero_of_bound l hab
    (fun X => cellSourceSlice (f X))
    (fun X => cellSourceSlice_memLp (Icc a b) (f X) (hf X)) C _ hc
  filter_upwards [hC, hb] with X hX hXt
  intro t _
  exact cellSourceSlice_norm_le_pointwise (f X) t (C X)
    ((hm X).comp (measurable_const.prodMk measurable_id)) hX (hXt t)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Natural weak-stage chart pieces use the existing smooth material-flow homeomorphism. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

private theorem mem_intervalHull_self {S : Set ℝ} {t : ℝ} (ht : t ∈ S) :
    t ∈ intervalHull S := ⟨t, ht, t, ht, le_rfl, le_rfl⟩

theorem weak_avail_anchor (D : OCData) (M i : ℕ) (p : ℤ) :
    D.slotAnchor i p ∈ availInterval D M i p := by
  unfold availInterval
  cases M - i with
  | zero => exact mem_intervalHull_self (Set.mem_insert _ _)
  | succ n => exact mem_intervalHull_self (Set.mem_insert _ _)

theorem weak_output_subset_avail (D : OCData) (M i : ℕ) (p : ℤ) :
    ocPulseWindow D.α D.q D.Λ i p ⊆ availInterval D M i p := by
  intro t ht
  unfold availInterval
  cases M - i with
  | zero => exact mem_intervalHull_self (Set.mem_insert_of_mem _ ht)
  | succ n => exact mem_intervalHull_self (Set.mem_insert_of_mem _ (Or.inl ht))

def weakNaturalPiece (D : OCData) (M i : ℕ) (p : ℤ) : ChartPiece where
  label := ocLabel D.α D.q D.Λ i p
  output := ocPulseWindow D.α D.q D.Λ i p
  geometry := availInterval D M i p
  output_subset := weak_output_subset_avail D M i p
  anchor := D.slotAnchor i p
  anchor_mem := weak_avail_anchor D M i p
  material := fun t => CycleReference.streamFlowHomeomorph (D.hΦ (i - 1)) t (D.slotAnchor i p)
  material_smooth := fun t => CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) t _
  material_symm_smooth := fun t => CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) _ t

theorem weakNaturalPiece_isNatural (D : OCData) (M i : ℕ) (p : ℤ) :
    IsNaturalPiece D M i p (weakNaturalPiece D M i p) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! The literal cell equation under a positive change of clock. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.CycleEvolution

/-- Rescale the generator while retaining its spatial Bloch shift. -/
def cellClockCoefficients (C : CellCoefficients) (c : ℝ) : CellCoefficients where
  G t x := c • C.G (c * t) x
  v t x := c • C.v (c * t) x
  θ := C.θ
  κ t := c • C.κ (c * t)

theorem cellLiteralRHS_clock (C : CellCoefficients) (c t : ℝ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS (cellClockCoefficients C c) t u du ψ dψ
      (c • src) (c • F) x = c • cellLiteralRHS C (c * t) u du ψ dψ src F x := by
  simp only [cellLiteralRHS, cellClockCoefficients, Fin.sum_univ_two,
    Matrix.smul_apply, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.real_smul]
  ring

end AVRegularity.WeakEntryProofs
end
end

section
/-! Strong convergence of the energy trace and local higher bounds give classical jet convergence. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleEvolution

theorem molecular_higher_trace_jet_tendsto {A : Type*} (l : Filter A)
    (K n : ℕ) (hn : n + 4 ≤ K) (w : A → TorusHk K ℂ) (v : TorusHk K ℂ)
    (u : A → ComplexCellL2) (u₀ : ComplexCellL2)
    (hw : ∀ X, torusHkValueCLM (w X) = u X) (hv : torusHkValueCLM v = u₀)
    (hu : Tendsto (fun X => u X - u₀) l (𝓝 0))
    (R : ℝ) (hb : ∀ᶠ X in l, ‖w X‖ ≤ R) (z : Vec 2) :
    Tendsto (fun X => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (w X))) z) l
      (𝓝 (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z)) := by
  apply higher_carrier_real_jet_tendsto l K n hn w v _ R hb z
  have he (X : A) : (w X - v).val (valueIndex2 K) = u X - u₀ := by
    change torusHkValueCLM (w X - v) = u X - u₀
    rw [map_sub, hw X, hv]
  simpa only [he] using hu

theorem molecular_higher_trace_fast_jet_continuous {A : Type*} [TopologicalSpace A]
    (K n : ℕ) (hn : n + 4 ≤ K) (w : A → TorusHk K ℂ)
    (u : A → ComplexCellL2) (hu : Continuous u)
    (hw : ∀ X, torusHkValueCLM (w X) = u X)
    (R : ℝ) (hb : ∀ X, ‖w X‖ ≤ R) (z : Vec 2) :
    Continuous (fun X => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (w X))) z) := by
  apply continuous_iff_continuousAt.mpr
  intro Y
  exact molecular_higher_trace_jet_tendsto (𝓝 Y) K n hn w (w Y) u (u Y) hw (hw Y)
    (tendsto_sub_nhds_zero_iff.mpr (hu.tendsto Y)) R (Eventually.of_forall hb) z

end AVRegularity.WeakEntryProofs
end
end

section
/-! Box regularity on an open carrier depends only on the field's germ there. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs
open Homogenization Filter Topology AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boxSmoothOn_congr {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    (sX sZ : ℕ) {f g : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmoothOn Ω sX sZ f) (he : SlowOpenFieldEq Ω f g) :
    IsBoxSmoothOn Ω sX sZ g := by
  have hfast (b : ℕ) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) :
      iteratedFDeriv ℝ b (f X) z = iteratedFDeriv ℝ b (g X) z := by
    rw [show f X = g X from funext (he X hX)]
  have hmixed (a b : ℕ) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) :
      iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X =
        iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (g Y) z) X := by
    have hh : (fun Y => iteratedFDeriv ℝ b (f Y) z) =ᶠ[𝓝 X]
        fun Y => iteratedFDeriv ℝ b (g Y) z := by
      filter_upwards [hΩ.mem_nhds hX] with Y hY
      exact hfast b Y hY z
    exact (hh.iteratedFDeriv ℝ a).eq_of_nhds
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    rw [← show f X = g X from funext (he X hX)]
    exact hf.1 X hX
  · intro b hb z
    exact (hf.2.1 b hb z).congr (fun X hX => (hfast b X hX z).symm)
  · intro a b ha hb
    exact (hf.2.2 a b ha hb).congr (fun p hp => (hmixed a b p.1 hp.1 p.2).symm)

end AVRegularity.WeakEntryProofs
end
end

section
/-! Box regularity glues from actual open slow neighborhoods. -/
@[expose] public section
namespace AVRegularity.WeakEntryProofs
open Homogenization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boxSmoothOn_of_local_boxes (Ω : Set (Vec 2)) (sX sZ : ℕ)
    (f : Vec 2 → Vec 2 → E)
    (hf : ∀ X ∈ Ω, ∃ U : Set (Vec 2), IsOpen U ∧ X ∈ U ∧ IsBoxSmoothOn U sX sZ f) :
    IsBoxSmoothOn Ω sX sZ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨U, _, hU, hbox⟩ := hf X hX
    exact hbox.1 X hU
  · intro b hb z X hX
    obtain ⟨U, hU, hXU, hbox⟩ := hf X hX
    exact ((hbox.2.1 b hb z).contDiffAt (hU.mem_nhds hXU)).contDiffWithinAt
  · intro a b ha hb p hp
    obtain ⟨U, hU, hXU, hbox⟩ := hf p.1 hp.1
    exact ((hbox.2.2 a b ha hb).continuousAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hXU, Set.mem_univ p.2⟩)).continuousWithinAt

end AVRegularity.WeakEntryProofs
end
end

section
/-! Finite-window strong trace derivatives and bounded higher quotients yield classical derivatives. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleEvolution

theorem molecular_higher_trace_jet_hasDerivAt (K n : ℕ) (hn : n + 4 ≤ K)
    (w : ℝ → TorusHk K ℂ) (v : TorusHk K ℂ)
    (u : ℝ → ComplexCellL2) (u₁ : ComplexCellL2)
    (hw : ∀ h, torusHkValueCLM (w h) = u h) (hv : torusHkValueCLM v = u₁)
    (hu : Tendsto (fun h : ℝ => h⁻¹ • (u h - u 0) - u₁) (𝓝[≠] 0) (𝓝 0))
    (R : ℝ) (hb : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h⁻¹ • (w h - w 0)‖ ≤ R) (z : Vec 2) :
    HasDerivAt (fun h => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (w h))) z)
      (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM v)) z) 0 := by
  have he (h : ℝ) : (h⁻¹ • (w h - w 0) - v).val (valueIndex2 K) =
      h⁻¹ • (u h - u 0) - u₁ := by
    change torusHkValueCLM (h⁻¹ • (w h - w 0) - v) = _
    rw [map_sub, map_smul, map_sub, hw h, hw 0, hv]
  have ht : Tendsto (fun h : ℝ => (h⁻¹ • (w h - w 0) - v).val (valueIndex2 K))
      (𝓝[≠] 0) (𝓝 0) := by simpa only [he] using hu
  have hbound : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h⁻¹ • (w h - w 0) - v‖ ≤ R + ‖v‖ := by
    filter_upwards [hb] with h hh
    exact (norm_sub_le _ _).trans (add_le_add hh le_rfl)
  exact higher_carrier_real_jet_hasDerivAt K n hn w v ht (R + ‖v‖) hbound z

end AVRegularity.WeakEntryProofs
end
end
end
