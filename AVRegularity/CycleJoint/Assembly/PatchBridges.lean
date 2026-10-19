-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.CentreFlowWindow
public import AVRegularity.CycleJoint.PreparationWindowReferenceCellReturnMass
public import AVRegularity.CycleJoint.Assembly.PlaneModelExtension
public import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
public import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleJointProofs AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs.Assembly

/-! Counting a uniformly distorted grid by a summable product lattice weight. -/

/-- A norm bound converts the order-two radial decay into a product lattice majorant. -/
theorem lattice_radial_count_majorant (n : ℕ) (hn : 2 ≤ n) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A) (c : Vec 2) (i k : Fin 2 → ℤ)
    (hi : ‖c - latticeShift i‖ ≤ 1) (d : Vec 2)
    (hd : ‖latticeShift k - c‖ ≤ A * R⁻¹ * ‖d‖) :
    ((1 + R⁻¹ ^ 2 * (d 0 ^ 2 + d 1 ^ 2)) ^ n)⁻¹ ≤
      (16 * (2 + A) ^ 4) * (1 / spatialLatticeWeight (k - i)) ^ 2 := by
  let B := 1 + R⁻¹ ^ 2 * (d 0 ^ 2 + d 1 ^ 2)
  let t := R⁻¹ * ‖d‖
  have ht : 0 ≤ t := mul_nonneg (inv_pos.mpr hR).le (norm_nonneg _)
  have hB : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  have htsq : t ^ 2 ≤ 2 * (B - 1) := by
    have hh := mul_le_mul_of_nonneg_left (plane_norm_sq_le_twice_coordinate_sq d)
      (sq_nonneg R⁻¹)
    dsimp only [t, B]
    nlinarith only [hh]
  have hsmall : (1 + t) ^ 2 ≤ 4 * B := by
    nlinarith only [htsq, sq_nonneg (1 - t), hB]
  have hshift : ‖latticeShift (k - i)‖ ≤ A * t + 1 := by
    have he : latticeShift (k - i) = (latticeShift k - c) + (c - latticeShift i) := by
      funext j
      simp only [Pi.add_apply, latticeShift, Pi.sub_apply, Int.cast_sub]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (by simpa only [t, mul_assoc] using hd) hi)
  have hpoly : 1 + ‖latticeShift (k - i)‖ ≤ (2 + A) * (1 + t) := by
    nlinarith only [hshift, hA, ht]
  have hw : spatialLatticeWeight (k - i) ≤ 4 * (2 + A) ^ 2 * B := by
    calc
      _ ≤ (1 + ‖latticeShift (k - i)‖) ^ 2 := spatialLatticeWeight_le_shift_norm _
      _ ≤ ((2 + A) * (1 + t)) ^ 2 := pow_le_pow_left₀ (by positivity) hpoly 2
      _ = (2 + A) ^ 2 * (1 + t) ^ 2 := mul_pow _ _ _
      _ ≤ (2 + A) ^ 2 * (4 * B) := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by ring
  have hsq : spatialLatticeWeight (k - i) ^ 2 ≤ 16 * (2 + A) ^ 4 * B ^ 2 := by
    have hh := pow_le_pow_left₀ (spatialLatticeWeight_pos _).le hw 2
    convert hh using 1
    ring
  have hpow := pow_le_pow_right₀ hB hn
  have hfinal := hsq.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  change (B ^ n)⁻¹ ≤ _
  rw [← one_div, one_div_pow, mul_one_div]
  exact (div_le_div_iff₀ (pow_pos (lt_of_lt_of_le (by norm_num) hB) _)
    (sq_pos_of_pos (spatialLatticeWeight_pos _))).mpr (by simpa only [one_mul] using hfinal)

/-- A grid and any pointwise inverse Lipschitz bound give a uniform count. -/
theorem distorted_grid_count (n : ℕ) (hn : 2 ≤ n) (N : ℕ) (hN : 0 < N)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hNR : (N : ℝ) * R ≤ 9)
    (X : Vec 2 → Vec 2) (z x₀ : Vec 2)
    (hX : ∀ x, ‖x - x₀‖ ≤ L * ‖X x - z‖) :
    Summable (fun k : Fin 2 → ℤ =>
      ((1 + R⁻¹ ^ 2 * ((z 0 - X ((N : ℝ)⁻¹ • latticeShift k) 0) ^ 2 +
        (z 1 - X ((N : ℝ)⁻¹ • latticeShift k) 1) ^ 2)) ^ n)⁻¹) ∧
    (∑' k : Fin 2 → ℤ,
      ((1 + R⁻¹ ^ 2 * ((z 0 - X ((N : ℝ)⁻¹ • latticeShift k) 0) ^ 2 +
        (z 1 - X ((N : ℝ)⁻¹ • latticeShift k) 1) ^ 2)) ^ n)⁻¹) ≤
      (16 * (2 + 9 * L) ^ 4) * ∑' k : Fin 2 → ℤ, (1 / spatialLatticeWeight k) ^ 2 := by
  let c := (N : ℝ) • x₀
  obtain ⟨i, hi⟩ := exists_bounded_lattice_center c
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm (k : Fin 2 → ℤ) := lattice_radial_count_majorant n hn R (9 * L) hR
    (by positivity) c i k hi (z - X ((N : ℝ)⁻¹ • latticeShift k)) ?_
  · have hs : Summable (fun k : Fin 2 → ℤ => (1 / spatialLatticeWeight (k - i)) ^ 2) := by
      exact spatialLatticeReciprocal_square_summable.comp_injective (latticeDisplacementEquiv i).injective
    have hsC := hs.mul_left (16 * (2 + 9 * L) ^ 4)
    have hf : Summable (fun k : Fin 2 → ℤ =>
        ((1 + R⁻¹ ^ 2 * ((z 0 - X ((N : ℝ)⁻¹ • latticeShift k) 0) ^ 2 +
          (z 1 - X ((N : ℝ)⁻¹ • latticeShift k) 1) ^ 2)) ^ n)⁻¹) :=
      Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by simpa only [Pi.sub_apply] using hm k) hsC
    refine ⟨hf, ?_⟩
    apply (hf.tsum_le_tsum (fun k => by simpa only [Pi.sub_apply] using hm k) hsC).trans_eq
    rw [hs.tsum_mul_left]
    congr 1
    exact (latticeDisplacementEquiv i).tsum_eq
      (fun k : Fin 2 → ℤ => (1 / spatialLatticeWeight k) ^ 2)
  · have hg := mul_le_mul_of_nonneg_left (hX ((N : ℝ)⁻¹ • latticeShift k)) hNp.le
    have he : latticeShift k - c = (N : ℝ) • ((N : ℝ)⁻¹ • latticeShift k - x₀) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hNp.ne', one_smul]
    have hnorm : ‖latticeShift k - c‖ =
        (N : ℝ) * ‖(N : ℝ)⁻¹ • latticeShift k - x₀‖ := by
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hNp]
    rw [← hnorm] at hg
    have hNb : (N : ℝ) ≤ 9 * R⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hR).mpr hNR
    have hh := mul_le_mul_of_nonneg_right hNb (mul_nonneg hL (norm_nonneg (X ((N : ℝ)⁻¹ • latticeShift k) - z)))
    apply hg.trans
    apply hh.trans_eq
    rw [norm_sub_rev]
    ring

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVenhance.Infra.Flow AVRegularity.CycleJointProofs
namespace AVRegularity.CycleJointProofs.Assembly

/-! Ingredient CJ05: uniform counting of all transported patch images. -/

/-- Reverse the second lattice index, matching the sign of the counting weight. -/
def centreImageSignEquiv (N : ℕ) :
    ((Fin 2 → Fin N) × (Fin 2 → ℤ)) ≃ ((Fin 2 → Fin N) × (Fin 2 → ℤ)) where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The patch centres and their signed images enumerate the complete grid exactly. -/
def centreImageGridEquiv (N : ℕ) (hN : 0 < N) :
    ((Fin 2 → Fin N) × (Fin 2 → ℤ)) ≃ (Fin 2 → ℤ) :=
  (centreImageSignEquiv N).trans (periodImageLatticeEquiv N hN)

/-- Uniform counting with a constant independent of the stream, interval, and mesh. -/
theorem centreCounting : CentreCountingStatement := by
  intro n hn
  let L := Real.exp (1 / 4)
  let C := 16 * (2 + 9 * L) ^ 4
  let S := ∑' k : Fin 2 → ℤ, (1 / spatialLatticeWeight k) ^ 2
  have hL : 0 < L := Real.exp_pos _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hS : 0 ≤ S := tsum_nonneg (fun k => sq_nonneg _)
  refine ⟨C * (S + 1), mul_pos hC (by linarith), ?_⟩
  intro φ hφ s t T g R N hst hdt hT hg hg1 hgrad hR hmesh hNR z
  have hN : 0 < N := by
    by_contra h
    have hz : N = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hz] at hmesh
  let X := fun x => streamFlow φ hφ t x s
  let x₀ := streamFlow φ hφ s z t
  have hflow := flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
  have hInv (x : Vec 2) : streamFlow φ hφ s (X x) t = x :=
    (flow_group_law _ hφ.vel_lipschitz hflow x s t s).trans (hflow.1 x s)
  have hX (x : Vec 2) : ‖x - x₀‖ ≤ L * ‖X x - z‖ := by
    have hh := centre_inverse_flow_bound φ hφ s t T g hst hdt hT hg hg1 hgrad (X x) z
    rw [hInv] at hh
    exact hh
  have hgrid := distorted_grid_count n hn N hN R L hR hL.le hNR X z x₀ hX
  let F := fun k : Fin 2 → ℤ =>
    ((1 + R⁻¹ ^ 2 * ((z 0 - X ((N : ℝ)⁻¹ • latticeShift k) 0) ^ 2 +
      (z 1 - X ((N : ℝ)⁻¹ • latticeShift k) 1) ^ 2)) ^ n)⁻¹
  let e := centreImageGridEquiv N hN
  have he (p : (Fin 2 → Fin N) × (Fin 2 → ℤ)) :
      latticeCountWeight R⁻¹ n z (patchOutputCentre φ hφ s t N p.1) p.2 = F (e p) := by
    have hNp : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    have hp : (N : ℝ)⁻¹ • latticeShift (e p) =
        spatialPatchCentre N (fun i => (p.1 i : ℤ)) + latticeShift (-p.2) := by
      funext i
      change (N : ℝ)⁻¹ * (((p.1 i : ℤ) + (N : ℤ) * -(p.2 i) : ℤ) : ℝ) =
        ((p.1 i : ℤ) : ℝ) / N + ((-p.2 i : ℤ) : ℝ)
      push_cast
      field_simp
    have hshift : latticeShift (-p.2) = -latticeShift p.2 := by
      funext i
      simp only [latticeShift, Pi.neg_apply, Int.cast_neg]
    have hxp : X ((N : ℝ)⁻¹ • latticeShift (e p)) =
        patchOutputCentre φ hφ s t N p.1 - latticeShift p.2 := by
      rw [hp]
      change streamFlow φ hφ t (_ + latticeShift (-p.2)) s = _
      rw [AVRegularity.CycleReference.streamFlow_lattice_equivariant, hshift]
      rfl
    dsimp only [F, latticeCountWeight]
    rw [hxp]
    simp only [Pi.sub_apply, latticeShift]
    congr 2
    ring
  have hs : Summable (fun p : (Fin 2 → Fin N) × (Fin 2 → ℤ) => latticeCountWeight R⁻¹ n z
      (patchOutputCentre φ hφ s t N p.1) p.2) := by
    have hh := hgrid.1.comp_injective e.injective
    exact hh.congr (fun p => (he p).symm)
  refine ⟨hs, ?_⟩
  rw [tsum_congr he, e.tsum_eq]
  apply hgrid.2.trans
  change C * S ≤ C * (S + 1)
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) hC.le

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! **Raw readout of the block source letter**.

`blockLetterNativeArray` and `blockLetterRawConstituent` are the block-letter analogues of
`naturalFamilyTaylorNativeArray` and `naturalFamilyTaylorRawConstituent`: the weighted sum over the
pieces of their coefficients `blockLetterCoefficient` (`blockLetterAggCoeff`, exactly the
coefficient of the block letter's constituent) is Taylor-expanded in the slow variable at
`X₀ = E⁻¹ yc` with increment `(e / E) z`, the evaluation `taylorSlow 0 Ks · X₀ (δ • z)` of
`wordChainData`. The natural-family arrays Taylor-expand every piece separately; for the pieces of the block's
label (anchor at the reference time, identity flow and Jacobian) and spatially `C^Ks` coefficients
the two agree term by term (the Taylor polynomial is additive on `C^Ks` functions); for the other
pieces they differ by a Taylor remainder. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The coefficient of a block letter on the identity `γ`: the coefficients of the pieces in `S`
weighted by their time weights and summed (`blockLetterCoefficient`). -/
def blockLetterAggCoeff (F : ChartedFamily ι h D P Ctx) (S : Finset P) (actual : ∀ p, Ctx p)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E ℓ2 : ℝ)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (α : DerivativeWord2 (d - 1)) (τ : ℝ) (X z : Vec 2) :
    Vec 2 :=
  ∑ p ∈ S, F.weight p (ℓ2 * τ) •
    blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E ℓ2 d α τ X z

/-- The native array of the block letter for the identity `γ` and the derivative order `rjet`
(coefficient order `rjet + 1`): the slow Taylor polynomial of the weighted sum of the pieces'
coefficients, at `X₀ = E⁻¹ yc` with increment `(e / E) z`. -/
def blockLetterNativeArray (Ks : ℕ) (F : ChartedFamily ι h D P Ctx) (S : Finset P)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l : ℤ) (σ e E : ℝ) (yc : Vec 2) (rjet : ℕ) (τ : ℝ)
    (z : Vec 2) :=
  nativeArrayAssembly rjet (F.identity v u γ).map
    (fun k (I : DerivativeWord2 rjet) => taylorSlow 0 Ks
      (fun X => blockLetterAggCoeff F S actual hφ l σ yc e E timeScale v u γ (rjet + 1) I τ X z k)
      (E⁻¹ • yc) ((e / E) • z))

/-- The raw readout of the block source letter on the identity `γ`, summed over the derivative
orders. -/
def blockLetterRawConstituent (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E : ℝ) (yc : Vec 2)
    (ϖ ρ : ℝ) (μ : Measure ℝ) (v u : ι) (γ : F.Γ v u)
    (X : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ)
    (τ : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ j : Fin D,
    blockLetterNativeArray Ks F S actual v u γ timeScale hφ l σ e E yc (j.val + 1) τ z
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ X τ) (j.val + 1) I z))

/-- The readout of the block source letter on the identity `γ` for a plane field `W` of the
component `u` at cell time `τ`, summed over the pieces in `S` and the derivative orders. -/
def blockLetterFieldFlux (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E : ℝ) (yc : Vec 2) (v u : ι) (γ : F.Γ v u)
    (W : PlaneHk Set.univ (K u + 1) (h u)) (τ : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ j : Fin D,
    blockLetterNativeArray Ks F S actual v u γ timeScale hφ l σ e E yc (j.val + 1) τ z
      (WithLp.toLp 2 (fun I => planeJetOrder W (j.val + 1) I z))

/-- The raw readout of the block source letter vanishes on the zero carrier. -/
theorem blockLetterRawConstituent_zero (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E : ℝ) (yc : Vec 2)
    (ϖ ρ : ℝ) (μ : Measure ℝ) (v u : ι) (γ : F.Γ v u) :
    ∀ᵐ τ ∂μ, blockLetterRawConstituent Ks F S actual K timeScale hφ l σ e E yc ϖ ρ μ v u γ 0 τ
      =ᵐ[volume] (fun _ => 0) := by
  have ht : ∀ᵐ τ ∂μ, ∀ j : Fin D, ∀ᵐ z ∂volume,
      WithLp.toLp 2 (fun I : DerivativeWord2 (j.val + 1) => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ
          (0 : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ) τ)
        (j.val + 1) I z) = 0 :=
    ae_all_iff.mpr (fun j => planeAllMoment_zero_jet_array (K u + 1) ϖ ρ 0 μ (j.val + 1))
  filter_upwards [ht] with τ ht
  filter_upwards [ae_all_iff.mpr ht] with z hz
  unfold blockLetterRawConstituent
  apply Finset.sum_eq_zero
  intro j _
  rw [hz j, map_zero]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The one-patch statement from smooth patch models**.

The patch models of the one-patch statement (`PatchModelsGen`) act on `L²` data, while the construction (the word
chains of the two-block theorem and the seam kernels) acts on data at the family's slots `K`. `PatchSmoothModel` asks, for
one patch, a linear model `P` on slot-`K` data with the weighted model bound in terms of the `L²`
norm of the slot-`0` localization of the truncated datum, and the weighted physical error of the one-patch statement
for `P`; for an edge-free family also a slot-`0` model `P₀` agreeing with `P` on truncations, with
its model bound and its slot-`0` error. `patchModelsGen_of_smooth` extends `P` to `L²` data by
the plane-model extension (`planeModelExtension`: same bound, radial moments, uniqueness); the uniqueness identifies
the slot-`0` truncation of the extension with `P₀`.

For an empty index type all sums vanish and `P = 0` is a smooth model. For one edge-free component
the edge-free clause holds with `P₀` the truncation of `P`'s extension, so it asks only for the
slot-`0` error. For all slots `0` the truncations are identities and `P₀ = P` is the natural choice.
The minimal regularity `n = 4` is the threshold of the plane-model extension (`4 ≤ n`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The patch localization at slot `0` as a continuous linear map (norm at most `1`). -/
def spatialPatchLocalizationCLM {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) : TorusHk 0 E →L[ℝ] PlaneHk Set.univ 0 E :=
  (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0).mkContinuous 1 fun f => by
    have hs := spatialPatchLocalization_norm_sq_sum hζ N hN f
    have hj : ‖spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0 f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
      (Finset.single_le_sum (f := fun j' : Fin 2 → Fin N =>
        ‖spatialPatchLocalization hζ N hN (fun i => (j' i : ℤ)) 0 f‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans hs
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hj

omit [FiniteDimensional ℝ E] in
/-- The weighted factorial energy is monotone in its order. -/
theorem weightedFactorialNormSq_order_mono {K' : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r : ℝ)
    {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) (U : PlaneHk Set.univ K' E) :
    weightedFactorialNormSq n ϖ zc r K₁ U ≤ weightedFactorialNormSq n ϖ zc r K₂ U := by
  unfold weightedFactorialNormSq
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hK))

end Smooth

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **A smooth model of one patch** (the one-patch statement before the extension to `L²` data). The model bound is
at the order `Mb`, at least the required regularity `max Mout (K i)` (the plane-model extension extends in the full
required norm); the slot-`0` model's bound is at the order `Mout`. -/
def PatchSmoothModel {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Mout Mb D : ℕ) (C c ε : ℝ) (n : ℕ)
    (π : ι → ℝ) (K : ι → ℕ) (ν tS tp ρs ρold R : ℝ) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (y : Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop) : Prop :=
  ∃ P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)),
    (∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y (c * R) Mb (P f i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
        ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2)) ∧
    (∀ (f : ∀ i, TorusHk (K i) (h i)) (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν tS tp b D K A
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
        (fun _ _ => 0) (fun _ _ => 0) U W →
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y ρs (K i)
          (U i tp - truncatePlaneHk (le_max_right Mout (K i)) (P f i)) ≤
        ENNReal.ofReal (ε ^ 2 * ∑ i, (π i)⁻¹ * factorialNormSq ρold
          (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val)) ∧
    (edgeFree → ∃ P₀ : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout 0) (h i)),
      (∀ f, P₀ (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) =
        planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
          (fun _ => max_le_max le_rfl (Nat.zero_le _)) (P f)) ∧
      (∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n R⁻¹ y (c * R) Mout (P₀ g i) ≤
        ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖spatialPatchLocalizationCLM hζ N hN j (g i)‖ ^ 2)) ∧
      IsPatchError π (fun _ => 0) Mout D ν tS tp ρs ρold R ε n y b A0
        (fun _ => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) 0) P₀)

/-- The slot-`0` truncation of the extension of a smooth model is the slot-`0` model (uniqueness
of the plane-model extension for the truncated model). -/
theorem truncation_extension_eq {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {Mout Mb : ℕ} {C c : ℝ}
    {n : ℕ} (hn : 4 ≤ n) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (hMo : Mout ≤ Mb)
    (R : ℝ) (hR : 0 < R) (hc : 0 < c) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (y : Vec 2)
    (P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (Q : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)))
    (hPm : ∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y (c * R) Mb (P f i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
        ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2))
    (hQagree : ∀ f, Q (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) = P f)
    (hQbound : ∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n R⁻¹ y (c * R) Mb (Q g i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖spatialPatchLocalizationCLM hζ N hN j (g i)‖ ^ 2))
    (P₀ : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout 0) (h i)))
    (hagree0 : ∀ f, P₀ (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) =
      planeFamilyTruncation (fun _ => max Mout 0) (fun i => max Mout (K i))
        (fun _ => max_le_max le_rfl (Nat.zero_le _)) (P f))
    (hbound0 : ∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n R⁻¹ y (c * R) Mout (P₀ g i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖spatialPatchLocalizationCLM hζ N hN j (g i)‖ ^ 2)) :
    planeFamilyTruncation (h := h) (fun _ => max Mout 0) (fun i => max Mout (K i))
      (fun _ => max_le_max le_rfl (Nat.zero_le _)) ∘ₗ Q = P₀ := by
  let tr := planeFamilyTruncation (h := h) (fun _ => max Mout 0) (fun i => max Mout (K i))
    (fun _ => max_le_max le_rfl (Nat.zero_le _))
  have htr : ∀ (g : ∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)) i,
      weightedFactorialNormSq n R⁻¹ y (c * R) Mout (tr g i) =
        weightedFactorialNormSq n R⁻¹ y (c * R) Mout (g i) := fun g i =>
    CycleWords.weightedFactorialNormSq_truncate (max_le_max le_rfl (Nat.zero_le _))
      (le_max_left _ _) (g i) n R⁻¹ (c * R) y
  have hord : ∀ (g : ∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)),
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y (c * R) Mout (tr g i) ≤
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y (c * R) Mb (g i) :=
    fun g => le_trans (le_of_eq (Finset.sum_congr rfl fun i _ =>
        congrArg (fun z => ENNReal.ofReal ((π i)⁻¹) * z) (htr g i)))
      (Finset.sum_le_sum fun i _ =>
        mul_le_mul_right (weightedFactorialNormSq_order_mono n R⁻¹ y (c * R) hMo (g i)) _)
  obtain ⟨Q', -, -, -, hQ'uniq⟩ := planeModelExtension.{u, v} π hπ K
    (fun _ => max Mout 0) Mout n (fun _ => (max_eq_left (Nat.zero_le Mout)).le) hn R⁻¹ (c * R)
    C (inv_pos.2 hR) (mul_pos hc hR) y (fun _ => spatialPatchLocalizationCLM hζ N hN j)
    (tr ∘ₗ P) (fun f => (hord (P f)).trans (hPm f))
  have h1 : tr ∘ₗ Q = Q' := hQ'uniq C (tr ∘ₗ Q)
    (fun f => (congrArg tr (hQagree f) :)) (fun g => (hord (Q g)).trans (hQbound g))
  have h2 : P₀ = Q' := hQ'uniq C P₀ (fun f => hagree0 f) hbound0
  exact h1.trans h2.symm

/-- **The conclusion of the one-patch statement from smooth patch models**: the plane-model extension extends each smooth model to `L²` data. -/
theorem patchModelsGen_of_smooth {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {Mout Mb D : ℕ}
    {C c ε : ℝ} {n : ℕ} (hn : 4 ≤ n) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (hMb : ∀ i, max Mout (K i) ≤ Mb) (hMo : Mout ≤ Mb) (ν tS tp ρs ρold R : ℝ)
    (hR : 0 < R) (hc : 0 < c) (y : ∀ N : ℕ, (Fin 2 → Fin N) → Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A0 : ∀ (i i' : ι) (d : admissibleOrders (fun _ => 0) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (edgeFree : Prop)
    (hS : ∀ (N : ℕ) (hN : 0 < N), 8 ≤ (N : ℝ) * R → (N : ℝ) * R ≤ 9 → ∀ j : Fin 2 → Fin N,
      PatchSmoothModel hζ Mout Mb D C c ε n π K ν tS tp ρs ρold R N hN j (y N j) b A A0
        edgeFree) :
    PatchModelsGen hζ Mout D C c ε n π K ν tS tp ρs ρold R y b A A0 edgeFree := by
  intro N hN h8 h9 j
  refine Exists.elim (hS N hN h8 h9 j) fun P hP => ?_
  refine (planeModelExtension.{u, v} π hπ K
    (fun i => max Mout (K i)) Mb n hMb hn R⁻¹ (c * R) C (inv_pos.2 hR)
    (mul_pos hc hR) (y N j) (fun _ => spatialPatchLocalizationCLM hζ N hN j) P hP.1).elim
    fun Q hQ => ?_
  refine ⟨Q, fun f => le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
      (weightedFactorialNormSq_order_mono n R⁻¹ (y N j) (c * R) hMo (Q f i)) _) (hQ.2.1 f),
    hQ.2.2.1, fun f U W hs => ?_, fun hedge => ?_⟩
  · rw [hQ.1 f]
    exact hP.2.1 f U W hs
  · refine (hP.2.2 hedge).elim fun P₀ h0 => ?_
    have h3 := truncation_extension_eq hζ hn π hπ K hMo R hR hc N hN j (y N j) P Q hP.1 hQ.1
      hQ.2.1 P₀ h0.1 h0.2.1
    exact h3 ▸ h0.2.2

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The weighted error by interpolation**.

`MassInterpolationStatement`: Hölder in the moment weight. For `0 ≤ n ≤ n'`,
`n' > 0` and `θ = n/n'`, the mass-weighted factorial energy with weight
`(1 + ϖ²|z - zc|²)^n` is at most the unweighted energy to the power `1 - θ` times the energy with
weight `(1 + ϖ²|z - zc|²)^{n'}` to the power `θ`. (`(1 + ϖ²|·|²)^n = ((1 + ϖ²|·|²)^{n'})^θ · 1^{1-θ}`;
Hölder in `z` for every derivative order, then Hölder over the finite sum of orders and
components.)

`patch_error_interp`: an unweighted error `ε₁² S` and a moment bound `C₂ S` without `ε₁` give the
weighted error `ε² S` once `(ε₁²)^{1-θ} C₂^θ ≤ ε²` (every fixed output moment of that same
error is bounded without `ε`, by the full-interval actual energy and the model moment
estimate). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- **Interpolation of the moment weight** (mass-weighted family form). -/
def MassInterpolationStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (p : ι → ℝ≥0∞) (K K' : ι → ℕ) (U : ∀ i, PlaneHk Set.univ (K' i) (h i)) (n n' : ℕ),
    n ≤ n' → 0 < n' → ∀ (ϖ : ℝ) (zc : Vec 2) (r : ℝ),
    ∑ i, p i * weightedFactorialNormSq n ϖ zc r (K i) (U i) ≤
      (∑ i, p i * weightedFactorialNormSq 0 ϖ zc r (K i) (U i)) ^ (1 - (n : ℝ) / n') *
        (∑ i, p i * weightedFactorialNormSq n' ϖ zc r (K i) (U i)) ^ ((n : ℝ) / n')

/-- Real algebra of the interpolated price. -/
theorem interp_price_le {ε₁ C₂ ε S θ : ℝ} (hC₂ : 0 ≤ C₂) (hS : 0 ≤ S)
    (hε : (ε₁ ^ 2) ^ (1 - θ) * C₂ ^ θ ≤ ε ^ 2) :
    (ε₁ ^ 2 * S) ^ (1 - θ) * (C₂ * S) ^ θ ≤ ε ^ 2 * S := by
  have hsq : 0 ≤ ε₁ ^ 2 := sq_nonneg ε₁
  rw [Real.mul_rpow hsq hS, Real.mul_rpow hC₂ hS]
  have hSS : S ^ (1 - θ) * S ^ θ = S := by
    rw [← Real.rpow_add' hS (by linarith : (1 - θ) + θ ≠ 0)]
    simp
  calc (ε₁ ^ 2) ^ (1 - θ) * S ^ (1 - θ) * (C₂ ^ θ * S ^ θ)
      = (ε₁ ^ 2) ^ (1 - θ) * C₂ ^ θ * (S ^ (1 - θ) * S ^ θ) := by ring
    _ = (ε₁ ^ 2) ^ (1 - θ) * C₂ ^ θ * S := by rw [hSS]
    _ ≤ ε ^ 2 * S := mul_le_mul_of_nonneg_right hε hS

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The weighted error from the unweighted error and a moment bound.** -/
theorem patch_error_interp (hI : MassInterpolationStatement.{u, v}) (π : ι → ℝ) (K : ι → ℕ)
    {n n' : ℕ} (hnn : n ≤ n') (hn' : 0 < n') (ϖ : ℝ) (zc : Vec 2) (r : ℝ)
    (err : ∀ i, PlaneHk Set.univ (K i) (h i)) (S ε₁ C₂ ε : ℝ) (hS : 0 ≤ S) (hC₂ : 0 ≤ C₂)
    (hε : (ε₁ ^ 2) ^ (1 - (n : ℝ) / n') * C₂ ^ ((n : ℝ) / n') ≤ ε ^ 2)
    (h0 : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0 ϖ zc r (K i) (err i) ≤
      ENNReal.ofReal (ε₁ ^ 2 * S))
    (h1 : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n' ϖ zc r (K i) (err i) ≤
      ENNReal.ofReal (C₂ * S)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc r (K i) (err i) ≤
      ENNReal.ofReal (ε ^ 2 * S) := by
  have hn'r : (0 : ℝ) < n' := Nat.cast_pos.2 hn'
  have hθ0 : 0 ≤ (n : ℝ) / n' := div_nonneg (Nat.cast_nonneg n) hn'r.le
  have hθ1 : (n : ℝ) / n' ≤ 1 := (div_le_one hn'r).2 (Nat.cast_le.2 hnn)
  have h1θ : 0 ≤ 1 - (n : ℝ) / n' := by linarith
  calc ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc r (K i) (err i)
      ≤ (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0 ϖ zc r (K i) (err i)) ^
            (1 - (n : ℝ) / n') *
          (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n' ϖ zc r (K i) (err i)) ^
            ((n : ℝ) / n') :=
        hI (fun i => ENNReal.ofReal ((π i)⁻¹)) K K err n n' hnn hn' ϖ zc r
    _ ≤ ENNReal.ofReal (ε₁ ^ 2 * S) ^ (1 - (n : ℝ) / n') *
          ENNReal.ofReal (C₂ * S) ^ ((n : ℝ) / n') :=
        mul_le_mul' (ENNReal.rpow_le_rpow h0 h1θ) (ENNReal.rpow_le_rpow h1 hθ0)
    _ = ENNReal.ofReal ((ε₁ ^ 2 * S) ^ (1 - (n : ℝ) / n') * (C₂ * S) ^ ((n : ℝ) / n')) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (sq_nonneg _) hS) h1θ,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC₂ hS) hθ0,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (sq_nonneg _) hS) _)]
    _ ≤ ENNReal.ofReal (ε ^ 2 * S) :=
        ENNReal.ofReal_le_ofReal (interp_price_le hC₂ hS hε)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Truncation and the weighted norm for the return**.

Truncation: the return to physical variables commutes with truncation.

The return `preparationWindowReferenceCellReturnOperator` is the pullback by the window flow after
the affine rescaling of the cell chart; its value is the value of the cell field composed with
these maps, whatever the order. Truncating to a lower order keeps the value, so returning at the
higher order and truncating equals truncating and returning at the lower order.

Weighted norm: the moment-weighted factorial norm of the return, centred at `y`, is at most
`L^{2n}` times the squared composition constant times `e²` times the weighted norm of the cell
field at scale `ϖ e`, radius `ρ/e`, centred at the cell point `e⁻¹ (X y - yc)` of `y` (`X` the
window flow to the chart time, `L` the Lipschitz constant of its inverse). It rests on the
moment-weighted pullback bound (`WeightedPullbackStatement`) and the exact affine
identity `weightedFactorialNormSq_affine`. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference

universe uE

namespace AVRegularity.CycleJointProofs.Assembly

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The value of the return: the cell value at the rescaled flow image. -/
theorem preparationWindowReferenceCellReturn_value_ae
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1)) (J : ℕ) (hJ : J ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b) (V : PlaneHk univ J E) :
    planeValue (preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht V)
      =ᵐ[volume] fun x => planeValue V (-(e⁻¹ • yc) + e⁻¹ • streamFlowHomeomorph hφ σ t x) := by
  have h1 := CycleJointProofs.planeHkSmoothPullback_value_ae (streamFlowHomeomorph hφ σ t)
    (streamFlow_spatial_smooth hφ _ t) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_window_reference_time_inverse_flow_jets hc hcover σ hσ ha t ht j hj
        (hjJ.trans hJ) x)
    (CycleJointProofs.planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) V)
  have h2 := CycleJointProofs.planeCarrierAffine_value_ae e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) V
  have h3 := (streamFlow_measurePreserving hφ σ t).quasiMeasurePreserving.ae_eq_comp h2
  exact h1.trans h3

/-- **The return commutes with truncation.** -/
theorem preparationWindowReferenceCellReturn_truncate
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1)) {J L : ℕ} (hJL : J ≤ L)
    (hL : L ≤ Jchart + 1) (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (V : PlaneHk univ L E) :
    truncatePlaneHk hJL
        (preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha L hL e he yc t ht V) =
      preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J (hJL.trans hL) e he yc t ht
        (truncatePlaneHk hJL V) := by
  apply CycleWords.planeHk_eq_of_planeValue_ae
  have hv (W : PlaneHk univ L E) : planeValue (truncatePlaneHk hJL W) = planeValue W :=
    CycleWords.planeJetOrder_truncate hJL (Nat.zero_le J) W _
  rw [hv]
  refine (preparationWindowReferenceCellReturn_value_ae hc hcover σ hσ ha L hL e he yc t ht V).trans
    ?_
  have h2 := preparationWindowReferenceCellReturn_value_ae hc hcover σ hσ ha J (hJL.trans hL) e he
    yc t ht (truncatePlaneHk hJL V)
  simp only [hv] at h2
  exact h2.symm

/-- **The weighted factorial norm of the return.** -/
theorem preparationWindowReferenceCellReturn_weighted_le {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] (hW : WeightedPullbackStatement.{uE})
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1)) (J : ℕ) (hJ : J ≤ Jchart + 1)
    (hE : 0 < ocEpsilon q Λ (m - 1)) (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ)
    (ht : t ∈ Icc a b) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (L : ℝ)
    (hL : 1 ≤ L)
    (hlip : ∀ u v : Vec 2, ((streamFlowHomeomorph hφ σ t).symm u 0 -
        (streamFlowHomeomorph hφ σ t).symm v 0) ^ 2 +
        ((streamFlowHomeomorph hφ σ t).symm u 1 - (streamFlowHomeomorph hφ σ t).symm v 1) ^ 2 ≤
      L ^ 2 * ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2))
    (n : ℕ) (ϖ : ℝ) (y : Vec 2) (V : PlaneHk univ J E) :
    weightedFactorialNormSq n ϖ y ρ J
        (preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht V) ≤
      ENNReal.ofReal (L ^ (2 * n) *
          compositionFactorialNormBound (preparationFlowJetConstant Cchart) J ^ 2) *
        (ENNReal.ofReal |((e⁻¹) ^ 2)⁻¹| *
          weightedFactorialNormSq n (ϖ * e) (e⁻¹ • (streamFlowHomeomorph hφ σ t y - yc)) (ρ / e) J
            V) := by
  set X := streamFlowHomeomorph hφ σ t with hX
  have hscale : ∀ j, 1 ≤ j → j ≤ J → ρ ^ (j - 1) *
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j ≤
        preparationFlowJetConstant Cchart j := by
    intro j _ _
    unfold preparationPieceFlowJetBudget
    rw [abs_of_nonneg (mul_nonneg (preparationFlowJetConstant_nonneg Cchart j)
      (pow_nonneg (inv_nonneg.2 hE.le) _))]
    exact preparation_scaled_flow_budget hE hρ hρE Cchart j
  have h1 := hW X (streamFlow_spatial_smooth hφ _ t) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_window_reference_time_inverse_flow_jets hc hcover σ hσ ha t ht j hj
        (hjJ.trans hJ) x)
    hρ (preparationFlowJetConstant Cchart) hscale L hL hlip n ϖ (X y)
    (CycleJointProofs.planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) V)
  rw [Homeomorph.symm_apply_apply] at h1
  have h2 := CycleJointProofs.weightedFactorialNormSq_affine n (ϖ * e) (ρ / e) e⁻¹ (inv_ne_zero he)
    (-(e⁻¹ • yc)) (e⁻¹ • (X y - yc)) V
  have hϖ : ϖ * e * e⁻¹ = ϖ := by field_simp
  have hcen : (e⁻¹)⁻¹ • (e⁻¹ • (X y - yc) - -(e⁻¹ • yc)) = X y := by
    rw [sub_neg_eq_add, ← smul_add, sub_add_cancel, smul_smul, inv_inv, mul_inv_cancel₀ he,
      one_smul]
  have hρ' : ρ / e / e⁻¹ = ρ := by field_simp
  rw [hϖ, hcen, hρ'] at h2
  exact h1.trans (le_of_eq (by rw [h2]))

/-- A coordinate of a plane vector is bounded by the Euclidean length. -/
theorem vec2_norm_sq_le (w : Vec 2) : ‖w‖ ^ 2 ≤ w 0 ^ 2 + w 1 ^ 2 := by
  have hs : 0 ≤ Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := Real.sqrt_nonneg _
  have hn : ‖w‖ ≤ Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg hs).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; nlinarith [sq_nonneg (w 1)]
    · simp only [Fin.mk_one, Fin.isValue]; nlinarith [sq_nonneg (w 0)]
  calc ‖w‖ ^ 2 ≤ Real.sqrt (w 0 ^ 2 + w 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hn 2
    _ = w 0 ^ 2 + w 1 ^ 2 := Real.sq_sqrt (by positivity)

/-- **The Lipschitz bound of the inverse window flow** in the Euclidean form of
`WeightedPullbackStatement`, with constant `2 B₁` (`B₁` the first-jet budget, `≥ 1`). -/
theorem preparationWindowReference_inverse_flow_lipschitz
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1)) (t : ℝ) (ht : t ∈ Icc a b) :
    1 ≤ 2 * preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1 ∧
    ∀ u v : Vec 2, ((streamFlowHomeomorph hφ σ t).symm u 0 -
        (streamFlowHomeomorph hφ σ t).symm v 0) ^ 2 +
        ((streamFlowHomeomorph hφ σ t).symm u 1 - (streamFlowHomeomorph hφ σ t).symm v 1) ^ 2 ≤
      (2 * preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1) ^ 2 *
        ((u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2) := by
  set B₁ := preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1 with hB₁
  have hB₁1 : 1 ≤ B₁ := by
    rw [hB₁]
    unfold preparationPieceFlowJetBudget preparationFlowJetConstant
    simp only [↓reduceIte, pow_zero, mul_one, Nat.sub_self]
    rw [abs_of_nonneg (by positivity)]
    have := le_max_right (Cchart 0) 0
    linarith
  refine ⟨by linarith, fun u v => ?_⟩
  have hb : ∀ x, ‖iteratedFDeriv ℝ 1 (fun y => streamFlow φ hφ t y σ) x‖ ≤ (⟨B₁, by linarith⟩ : NNReal) :=
    fun x => preparation_window_reference_time_flow_jets hc hcover σ hσ ha t ht 1 le_rfl
      (by omega) x
  have hlip := CycleJointProofs.lipschitzWith_of_first_jet_bound _
    ((streamFlow_spatial_smooth hφ t σ).differentiable (by simp)) _ hb
  have hd := hlip.dist_le_mul u v
  have hsym : ∀ x, (streamFlowHomeomorph hφ σ t).symm x = streamFlow φ hφ t x σ := fun _ => rfl
  rw [hsym, hsym]
  set w := streamFlow φ hφ t u σ - streamFlow φ hφ t v σ with hw
  have hw0 : streamFlow φ hφ t u σ 0 - streamFlow φ hφ t v σ 0 = w 0 := rfl
  have hw1 : streamFlow φ hφ t u σ 1 - streamFlow φ hφ t v σ 1 = w 1 := rfl
  rw [hw0, hw1]
  have h1 : |w 0| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w 0
  have h2 : |w 1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w 1
  have hdw : ‖w‖ ≤ B₁ * ‖u - v‖ := by
    rw [dist_eq_norm, dist_eq_norm] at hd
    rw [hw]
    exact hd
  have huv := vec2_norm_sq_le (u - v)
  simp only [Pi.sub_apply] at huv
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have hsq : ‖w‖ ^ 2 ≤ B₁ ^ 2 * ‖u - v‖ ^ 2 := by
    have := pow_le_pow_left₀ hn hdw 2
    rw [mul_pow] at this
    exact this
  have e0 : w 0 ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e1 : w 1 ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hB2 : 0 ≤ B₁ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left huv hB2]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVenhance
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Elementary facts for the level-B assembly of `cycle_joint`: the patch mesh, the
vanishing of the coefficients of an edge-free family, the unweighted weighted norm, and the
uniform patch budget of the prepared norms. -/

/-- A patch mesh `N` with `8 ≤ N R ≤ 9` exists for every scale `0 < R ≤ 1`. -/
theorem exists_patch_mesh {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ 8 ≤ (N : ℝ) * R ∧ (N : ℝ) * R ≤ 9 := by
  refine ⟨⌈8 / R⌉₊, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.2 (div_pos (by norm_num) hR)
  · have h := Nat.le_ceil (8 / R)
    calc (8 : ℝ) = 8 / R * R := by field_simp
      _ ≤ (⌈8 / R⌉₊ : ℝ) * R := mul_le_mul_of_nonneg_right h hR.le
  · have h := Nat.ceil_lt_add_one (div_pos (by norm_num : (0 : ℝ) < 8) hR).le
    calc (⌈8 / R⌉₊ : ℝ) * R ≤ (8 / R + 1) * R := mul_le_mul_of_nonneg_right h.le hR.le
      _ = 8 + R := by field_simp
      _ ≤ 9 := by linarith

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The coefficients of a family without edges vanish. -/
theorem edgeCoefficient_eq_zero_of_isEmpty (F : ChartedFamily ι h D P Ctx)
    (hF : ∀ v u, IsEmpty (F.Γ v u)) (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (x : Vec 2) :
    edgeCoefficient F ν e E actual K v u d t x = 0 := by
  have := hF v u
  simp [edgeCoefficient, physicalCoefficient]

end Family

section Norms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- With moment order zero the weighted plane norm is the factorial norm. -/
theorem weightedFactorialNormSq_zero_moment {K : ℕ} (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq 0 ϖ zc ρ K U = ENNReal.ofReal (factorialNormSq ρ U.val) := by
  rw [weightedFactorialNormSq_stored_readout,
    ← CycleJointProofs.storedChartFactorialEnergy_one]
  congr 1

/-- The patch budget of the prepared norms, uniform over the slots `k ≤ Kmax`. -/
def patchBudgetUniform {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Kmax : ℕ) (L : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Kmax + 1), CycleJointProofs.patchFactorialEnergyBudget hζ k L

theorem patchBudgetUniform_nonneg {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Kmax : ℕ) (L : ℝ) :
    0 ≤ patchBudgetUniform hζ Kmax L :=
  Finset.sum_nonneg fun k _ => CycleJointProofs.patchFactorialEnergyBudget_nonneg hζ k L

theorem patchFactorialEnergyBudget_le_uniform {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {K Kmax : ℕ} (hK : K ≤ Kmax) (L : ℝ) :
    CycleJointProofs.patchFactorialEnergyBudget hζ K L ≤ patchBudgetUniform hζ Kmax L :=
  Finset.single_le_sum (f := fun k => CycleJointProofs.patchFactorialEnergyBudget hζ k L)
    (fun k _ => CycleJointProofs.patchFactorialEnergyBudget_nonneg hζ k L)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hK))

/-- **Patch budget of the prepared norms.** At a mesh with `ρ N ≤ L`, the prepared norms of the
patch localizations sum to at most the uniform budget times the prepared norm. -/
theorem patch_localization_factorial_sum_le [FiniteDimensional ℝ E] {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (f : TorusHk K E) (ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : 1 ≤ L) (hmesh : ρ * (N : ℝ) ≤ L) :
    ∑ j : Fin 2 → Fin N, factorialNormSq ρ
        (spatialPatchLocalization hζ N hN (fun i => (j i : ℤ)) K f).val ≤
      patchBudgetUniform hζ Kmax L * factorialNormSq ρ f.val := by
  have h := CycleJointProofs.spatialPatchLocalization_weighted_factorial_sum hζ N hN f ρ L hρ hL
    hmesh 0 0 0 le_rfl le_rfl (by simp)
  simp only [weightedFactorialNormSq_zero_moment, pow_zero, one_mul] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => factorialNormSq_nonneg ρ _),
    ← ENNReal.ofReal_mul (CycleJointProofs.patchFactorialEnergyBudget_nonneg hζ K L)] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (CycleJointProofs.patchFactorialEnergyBudget_nonneg hζ K L)
    (factorialNormSq_nonneg ρ _))).1 h
  exact h'.trans (mul_le_mul_of_nonneg_right
    (patchFactorialEnergyBudget_le_uniform hζ hK L) (factorialNormSq_nonneg ρ _))

/-- Truncation to the same order is the identity. -/
theorem truncateTorusHk_self {K : ℕ} (x : TorusHk K E) : truncateTorusHk (le_refl K) x = x := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

/-- Truncations of plane carriers compose. -/
theorem truncatePlaneHk_truncatePlaneHk {K L M : ℕ} (h₁ : K ≤ L) (h₂ : L ≤ M)
    (x : PlaneHk Set.univ M E) :
    truncatePlaneHk h₁ (truncatePlaneHk h₂ x) = truncatePlaneHk (h₁.trans h₂) x := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

end Norms

/-- **Mass-sum transfer.** Componentwise bounds by a patch sum, patchwise mass bounds and a
partition bound of the patch inputs combine into one mass bound. -/
theorem mass_sum_transfer {ι J : Type*} [Fintype ι] [Fintype J] (p a c : ι → ℝ)
    (b : J → ι → ℝ) (w : J → ι → ℝ≥0∞) (Cc C2 : ℝ)
    (hp : ∀ i, 0 ≤ p i) (ha : ∀ i, 0 ≤ a i) (hCc : 0 ≤ Cc) (hC2 : 0 ≤ C2)
    (hb : ∀ j i, 0 ≤ b j i)
    (h1 : ∀ i, ENNReal.ofReal (a i) ≤ ENNReal.ofReal Cc * ∑ j, w j i)
    (h2 : ∀ j, ∑ i, ENNReal.ofReal (p i) * w j i ≤ ENNReal.ofReal (C2 * ∑ i, p i * b j i))
    (h3 : ∀ i, ∑ j, b j i ≤ c i) :
    ∑ i, p i * a i ≤ Cc * C2 * ∑ i, p i * c i := by
  have hpb : ∀ j, 0 ≤ ∑ i, p i * b j i := fun j =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hb j i)
  have hreal : Cc * ∑ j, C2 * ∑ i, p i * b j i = Cc * C2 * ∑ i, p i * ∑ j, b j i := by
    have h₁ : Cc * ∑ j, C2 * ∑ i, p i * b j i = ∑ j, ∑ i, Cc * C2 * (p i * b j i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, Finset.mul_sum]
    have h₂ : Cc * C2 * ∑ i, p i * ∑ j, b j i = ∑ i, ∑ j, Cc * C2 * (p i * b j i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [h₁, h₂, Finset.sum_comm]
  have hL : ENNReal.ofReal (∑ i, p i * a i) ≤
      ENNReal.ofReal (Cc * C2 * ∑ i, p i * ∑ j, b j i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (ha i))]
    calc ∑ i, ENNReal.ofReal (p i * a i)
        = ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (a i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (hp i)]
      _ ≤ ∑ i, ENNReal.ofReal (p i) * (ENNReal.ofReal Cc * ∑ j, w j i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right (h1 i) _
      _ = ENNReal.ofReal Cc * ∑ i, ∑ j, ENNReal.ofReal (p i) * w j i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ENNReal.ofReal Cc * ∑ j, ∑ i, ENNReal.ofReal (p i) * w j i := by
          rw [Finset.sum_comm]
      _ ≤ ENNReal.ofReal Cc * ∑ j, ENNReal.ofReal (C2 * ∑ i, p i * b j i) :=
          mul_le_mul_right (Finset.sum_le_sum fun j _ => h2 j) _
      _ = ENNReal.ofReal (Cc * C2 * ∑ i, p i * ∑ j, b j i) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hC2 (hpb j)),
            ← ENNReal.ofReal_mul hCc, hreal]
  have hR : 0 ≤ Cc * C2 * ∑ i, p i * ∑ j, b j i :=
    mul_nonneg (mul_nonneg hCc hC2)
      (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Finset.sum_nonneg fun j _ => hb j i))
  refine ((ENNReal.ofReal_le_ofReal_iff hR).1 hL).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h3 i) (hp i))
    (mul_nonneg hCc hC2)

/-- Weighted `ℓ²` triangle inequality for nonnegative component sizes. -/
theorem weighted_sqrt_sum_le {ι : Type*} [Fintype ι] (p x y z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx : ∀ i, 0 ≤ x i) (hxyz : ∀ i, x i ≤ y i + z i) :
    Real.sqrt (∑ i, p i * x i ^ 2) ≤
      Real.sqrt (∑ i, p i * y i ^ 2) + Real.sqrt (∑ i, p i * z i ^ 2) := by
  set Y := ∑ i, p i * y i ^ 2 with hY
  set Z := ∑ i, p i * z i ^ 2 with hZ
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (p i) * y i)
    (fun i => Real.sqrt (p i) * z i)
  have hsq : ∀ u : ι → ℝ, ∀ i, (Real.sqrt (p i) * u i) ^ 2 = p i * u i ^ 2 := fun u i => by
    rw [mul_pow, Real.sq_sqrt (hp i)]
  have hprod : ∀ i, Real.sqrt (p i) * y i * (Real.sqrt (p i) * z i) = p i * (y i * z i) :=
    fun i => by
      have := Real.mul_self_sqrt (hp i)
      calc Real.sqrt (p i) * y i * (Real.sqrt (p i) * z i)
          = (Real.sqrt (p i) * Real.sqrt (p i)) * (y i * z i) := by ring
        _ = p i * (y i * z i) := by rw [this]
  simp only [hsq, hprod] at hcs
  have hW : ∑ i, p i * (y i * z i) ≤ Real.sqrt Y * Real.sqrt Z := by
    rw [← Real.sqrt_mul hY0]
    exact Real.le_sqrt_of_sq_le hcs
  have hexp : ∑ i, p i * (y i + z i) ^ 2 = Y + 2 * ∑ i, p i * (y i * z i) + Z := by
    rw [hY, hZ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hbound : ∑ i, p i * x i ^ 2 ≤ (Real.sqrt Y + Real.sqrt Z) ^ 2 := by
    calc ∑ i, p i * x i ^ 2 ≤ ∑ i, p i * (y i + z i) ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hx i) (hxyz i) 2) (hp i)
      _ = Y + 2 * ∑ i, p i * (y i * z i) + Z := hexp
      _ ≤ Y + 2 * (Real.sqrt Y * Real.sqrt Z) + Z := by linarith
      _ = (Real.sqrt Y + Real.sqrt Z) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hY0, Real.sq_sqrt hZ0]
          ring
  exact (Real.sqrt_le_sqrt hbound).trans_eq
    (Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Bridges from the periodized-sum and scalar-contraction statements as stated (`PeriodizedSumStatement`,
`ScalarContractionStatement`) to the forms used by the level-B assembly
(`PeriodizedRadialSumStatement`, `ScalarContractionVanishingStatement`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- Scalar contraction with pointwise-vanishing coefficients follows from scalar contraction with the zero coefficients. -/
theorem scalarContractionVanishing_of_scalarContraction
    (hB4 : ScalarContractionStatement.{u, v}) : ScalarContractionVanishingStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ φ hφ ν t₀ t₁ hν D A hA f u w hs
  obtain rfl : A = fun _ _ _ _ _ => 0 := by
    funext i i' d t z
    exact hA i i' d t z
  exact hB4 φ hφ ν t₀ t₁ hν D f u w hs

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The weighted norm through order `k` does not see the jets above `k`. -/
theorem weightedFactorialNormSq_truncate {k K : ℕ} (hk : k ≤ K) (n : ℕ) (ϖ : ℝ) (y : Vec 2)
    (r : ℝ) (G : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ y r k (truncatePlaneHk hk G) =
      weightedFactorialNormSq n ϖ y r k G := by
  unfold weightedFactorialNormSq
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hj : ∀ w : DerivativeWord2 m,
      planeJetOrder (truncatePlaneHk hk G) m w = planeJetOrder G m w := fun w => by
    funext z
    simp only [planeJetOrder, dite_eq_left hmk, dite_eq_left (hmk.trans hk)]
    rfl
  simp only [hj]

/-- A weighted norm finite at a positive radius is finite at every radius. -/
theorem weightedFactorialNormSq_ne_top_of_pos {K' k : ℕ} (n : ℕ) (ϖ : ℝ) (y : Vec 2)
    {r : ℝ} (hr : 0 < r) (r' : ℝ) (G : PlaneHk Set.univ K' E)
    (hG : weightedFactorialNormSq n ϖ y r k G ≠ ⊤) :
    weightedFactorialNormSq n ϖ y r' k G ≠ ⊤ := by
  unfold weightedFactorialNormSq at hG ⊢
  rw [ENNReal.sum_ne_top] at hG ⊢
  intro m hm
  have h := hG m hm
  have hc : ENNReal.ofReal (r ^ (2 * m) / ((m.factorial : ℝ)) ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  have hI : (∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - y 0) ^ 2 + (z 1 - y 1) ^ 2)) ^ n *
      ∑ w, ‖planeJetOrder G m w z‖ ^ 2)) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hc] at h
    exact h rfl
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI

end Weighted

/-- The counting constant is at least one as soon as there is a centre. -/
theorem one_le_count_of_mem {J : Type} (y : J → Vec 2) (R Cc : ℝ) (n : ℕ)
    (hcount : ∀ z : Vec 2, Summable (fun p : J × (Fin 2 → ℤ) =>
        latticeCountWeight R⁻¹ n z (y p.1) p.2) ∧
      ∑' p : J × (Fin 2 → ℤ), latticeCountWeight R⁻¹ n z (y p.1) p.2 ≤ Cc) (j₀ : J) :
    1 ≤ Cc := by
  obtain ⟨hs, hle⟩ := hcount (y j₀)
  have hnn : ∀ p : J × (Fin 2 → ℤ), 0 ≤ latticeCountWeight R⁻¹ n (y j₀) (y p.1) p.2 :=
    fun p => inv_nonneg.2 (pow_nonneg (by positivity) _)
  have h1 := hs.sum_le_tsum {(j₀, 0)} (fun p _ => hnn p)
  have hw : latticeCountWeight R⁻¹ n (y j₀) (y j₀) 0 = 1 := by
    simp [latticeCountWeight]
  simp only [Finset.sum_singleton, hw] at h1
  exact h1.trans hle

/-- **Periodized-sum bridge**: the stated periodized-sum statement gives the radial form used by the
level-B assembly. -/
theorem periodizedRadialSum_of_periodizedSum (hB3 : PeriodizedSumStatement.{v, 0}) :
    PeriodizedRadialSumStatement.{v} := by
  intro E _ _ _ _ _ _ J _ y R Cc n hR hR1 hn hcount K G hm k hk r hr
  by_cases hfin : ∀ j, weightedFactorialNormSq n R⁻¹ (y j) r k (G j) ≠ ⊤
  · let G' : J → ℝ →ₗ[ℝ] PlaneHk Set.univ k E :=
      fun j => LinearMap.toSpanSingleton ℝ _ (truncatePlaneHk hk (G j))
    have hG' : ∀ j t, weightedFactorialNormSq n R⁻¹ (y j) 1 k (G' j t) ≠ ⊤ := by
      intro j t
      simp only [G', LinearMap.toSpanSingleton_apply, CycleJointProofs.weightedFactorialNormSq_smul,
        weightedFactorialNormSq_truncate]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (weightedFactorialNormSq_ne_top_of_pos n R⁻¹ (y j) hr 1 (G j) (hfin j))
    obtain ⟨Y, -, hYae, hYb⟩ := hB3 (E := E) (V := ℝ) y R Cc n hR hR1 hn hcount k G' hG'
    have hY1 : Y 1 = truncateTorusHk hk
        (∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j) (hm j)) := by
      apply TorusHk.ext_value
      apply Lp.ext
      have h1 := hYae 1 (valueIndex2 k)
      have h2 : ((∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j) (hm j)).val
          (valueIndex2 K) : Vec 2 → E) =ᵐ[volume.restrict AVenhance.unitCube]
          ∑ j, ⇑((CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j) (hm j)).val
            (valueIndex2 K)) := by
        have he : (∑ j, CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j) (hm j)).val
            (valueIndex2 K) = ∑ j, (CycleJointProofs.periodizeRadialPlaneCarrier (G j) (y j)
              (hm j)).val (valueIndex2 K) := by
          change CycleJointProofs.torusJetComponentCLM (valueIndex2 K) _ = _
          simp only [map_sum, CycleJointProofs.torusJetComponentCLM_apply]
        rw [he]
        exact Lp.coeFn_finsetSum _ _
      have h3 := ae_all_iff.2 fun j =>
        CycleJointProofs.periodizeRadialPlaneCarrier_component_ae (G j) (y j) (hm j)
          (valueIndex2 K)
      rw [truncateTorusHk_apply]
      filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
      rw [hz1, show truncateJetIndex hk (valueIndex2 k) = valueIndex2 K from rfl, hz2]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hz3 j]
      simp only [G', LinearMap.toSpanSingleton_apply, one_smul]
      rfl
    have hb := hYb 1 k le_rfl r
    rw [truncateTorusHk_self, hY1] at hb
    simpa only [G', LinearMap.toSpanSingleton_apply, one_smul, weightedFactorialNormSq_truncate]
      using hb
  · simp only [not_forall, not_not] at hfin
    obtain ⟨j₀, hj₀⟩ := hfin
    have hCc := one_le_count_of_mem y R Cc n hcount j₀
    have hsum : ∑ j, weightedFactorialNormSq n R⁻¹ (y j) r k (G j) = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨j₀, Finset.mem_univ _, hj₀⟩
    rw [hsum, ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero]; linarith)]
    exact le_top

end AVRegularity.CycleJointProofs.Assembly
end
end
