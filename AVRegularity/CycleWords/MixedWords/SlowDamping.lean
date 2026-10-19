-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.JetToValueStep
import AVRegularity.CycleWords.MixedWords.AfwCrude
public import AVRegularity.CycleWords.MixedWords.FibreDuality
public import AVRegularity.Proofs.GenSem.CoeffArr.Mean
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

section
section
/-! Exact assembly of the moment, fibre and Fourier-amplitude conclusions. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords.Assembly
universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- The exact data of a word piece and its energy chain from compactly supported data: `φ` is a
strongly measurable compactly supported representative of the plane datum `planeValue (f x)`. -/
structure AmplitudeIdFrame (K : ScalarConstants) (g₁ : ℝ) where
  H : ℕ
  J : ℕ
  π : ι → ℝ
  letters : Fin Nw → CycleLetter ι h D
  η : ℝ
  S : ℝ
  ηg : ℝ
  t₀ : ℝ
  Sw : ℝ
  ϖ : ℝ
  a : ℝ
  b : ℝ
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  v : ℝ → Vec 2 → Vec 2
  g : ℝ
  reg : BlockRegions
  pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg
  piece : IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b
  left : t₀ ≤ a
  ordered : a ≤ b
  right : b ≤ t₀ + Sw
  X₀ : Vec 2
  κ : Fin (Nw + 1) → ι → ℕ
  slots : IsWordSlots letters κ
  cap : ∀ j x, κ j x ≤ J
  φ : ∀ x, Vec 2 → h x
  compact : ∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)
  f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)
  u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)
  w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)
  datum : ∀ x, planeValue (f x) =ᵐ[volume] φ x
  solution : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w

/-- Every level of a compact-data word has all ordinary integrable moments. -/
def AmplitudeIdMoments {K : ScalarConstants} {g₁ : ℝ} (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ (j : Fin (Nw + 1)) (x : ι), ∀ t ∈ Icc F.a F.b, ∀ n : ℕ, ∀ β ∈ momentIndices n,
    Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (F.u j x t) y)

/-- The moment-weighted periodized level solves its literal forced fibre equation. -/
def AmplitudeIdFibres {K : ScalarConstants} {g₁ : ℝ} (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) : Prop :=
  ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ), ∃ Dθ : ℝ → RawJet2 1 ℂ,
    IsCellSolution (Icc F.a F.b)
      (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0))
      (fun r z => planeBlochC θ (fun y =>
        (momentWeightLap (F.G r) β y + ∑ i, F.v r y i * momentWeightGrad β y i) *
            inner ℝ e (planeValue (F.u j x r) y) -
          ∑ i, momentWeightGrad β y i * inner ℝ e
            (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r) (j, x) r y i)) z)
      (fun r z => WithLp.toLp 2 fun k => planeBlochC θ (fun y =>
        momentWeight β y * inner ℝ e
            (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ (fun q => F.w q.1 q.2 r) (j, x) r y k) -
          (∑ i, (F.G r k i + F.G r i k) * momentWeightGrad β y i) *
            inner ℝ e (planeValue (F.u j x r) y)) z)
      Dθ ∧
    ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y))

/-- Closed moment ingredient, uniform over the exact word data. -/
def AmplitudeIdMomentsStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ), ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ},
    ∀ F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁, AmplitudeIdMoments F

/-- Closed forced-periodization ingredient on the same exact word data. -/
def AmplitudeIdFibresStatement : Prop :=
  ∀ (K : ScalarConstants) (g₁ : ℝ), ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw : ℕ},
    ∀ F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁, AmplitudeIdFibres F

/-- Assemble the exact statement; the final amplitude identity is already discharged. -/
theorem amplitudeIdentification_of_ingredients
    (hm : AmplitudeIdMomentsStatement.{u, v}) (hf : AmplitudeIdFibresStatement.{u, v}) :
    AmplitudeIdentificationStatement.{u, v} := by
  intro K
  refine ⟨1, zero_lt_one, ?_⟩
  intro ι _ h _ _ _ _ _ _ D Nw H J π letters η S ηg t₀ Sw ϖ a b G v g reg pkg piece ha hab hb
    X₀ κ hκ hcap f u w hsupp hsol
  obtain ⟨φ, hφ, hdatum⟩ := planeDatum_rep f hsupp
  let F : AmplitudeIdFrame K 1 := ⟨H, J, π, letters, η, S, ηg, t₀, Sw, ϖ, a, b, G, v, g, reg,
    pkg, piece, ha, hab, hb, X₀, κ, hκ, hcap, φ, hφ, f, u, w, hdatum, hsol⟩
  refine ⟨hm K 1 F, hf K 1 F, ?_⟩
  intro x e θ
  have hi := hm K 1 F (Fin.last Nw) x b ⟨hab, le_rfl⟩ 0 (0, 0) (by simp [momentIndices])
  have hi' : Integrable (planeValue (u (Fin.last Nw) x b)) := by
    simpa only [pow_zero, one_mul, one_smul] using hi
  exact integral_phase_eq_cell_planeBlochC θ (((innerSL ℝ e).integrable_comp hi'))

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Polynomial L2 budgets give every L1 moment, on the genuine plane measure. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-- A fixed product decay is square integrable on the plane. -/
theorem amplitudeId_inverse_polynomial_memLp :
    MemLp (fun y : Vec 2 => (1 + y 0 ^ 2)⁻¹ * (1 + y 1 ^ 2)⁻¹) 2 volume := by
  have hi : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 4) (by norm_num)
    convert h using 1
    funext x
    norm_num [Real.norm_eq_abs, sq_abs, Real.rpow_neg, Real.rpow_two, inv_pow]
  have hp := Integrable.fintype_prod (ι := Fin 2) (fun _ => hi)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [Fin.prod_univ_two, mul_pow, volume_pi] using hp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hölder with fixed polynomial decay converts all L2 moments to all L1 moments. -/
theorem amplitudeId_integrable_of_all_monomial_memLp (u : Vec 2 → E)
    (h : ∀ β : ℕ × ℕ, MemLp (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • u y) 2 volume)
    (β : ℕ × ℕ) : Integrable (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • u y) := by
  let B := fun y : Vec 2 => ((1 + y 0 ^ 2) * (1 + y 1 ^ 2)) •
    ((y 0 ^ β.1 * y 1 ^ β.2) • u y)
  have hB : MemLp B 2 volume := by
    have he : B = (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • u y) +
        (fun y => (y 0 ^ (β.1 + 2) * y 1 ^ β.2) • u y) +
        (fun y => (y 0 ^ β.1 * y 1 ^ (β.2 + 2)) • u y) +
        (fun y => (y 0 ^ (β.1 + 2) * y 1 ^ (β.2 + 2)) • u y) := by
      funext y
      have hc : ((1 + y 0 ^ 2) * (1 + y 1 ^ 2)) * (y 0 ^ β.1 * y 1 ^ β.2) =
          y 0 ^ β.1 * y 1 ^ β.2 + y 0 ^ (β.1 + 2) * y 1 ^ β.2 +
            y 0 ^ β.1 * y 1 ^ (β.2 + 2) + y 0 ^ (β.1 + 2) * y 1 ^ (β.2 + 2) := by
        simp only [pow_add]
        ring
      dsimp only [B]
      rw [← mul_smul, hc, add_smul, add_smul, add_smul]
      rfl
    rw [he]
    exact (((h β).add (h (β.1 + 2, β.2))).add (h (β.1, β.2 + 2))).add (h (β.1 + 2, β.2 + 2))
  have hp : MemLp ((fun y : Vec 2 => (1 + y 0 ^ 2)⁻¹ * (1 + y 1 ^ 2)⁻¹) • B) 1 volume :=
    amplitudeId_inverse_polynomial_memLp.smul hB
  have he : ((fun y : Vec 2 => (1 + y 0 ^ 2)⁻¹ * (1 + y 1 ^ 2)⁻¹) • B) =
      (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • u y) := by
    funext y
    have h₀ : 1 + y 0 ^ 2 ≠ 0 := by positivity
    have h₁ : 1 + y 1 ^ 2 ≠ 0 := by positivity
    change ((1 + y 0 ^ 2)⁻¹ * (1 + y 1 ^ 2)⁻¹) •
      (((1 + y 0 ^ 2) * (1 + y 1 ^ 2)) • ((y 0 ^ β.1 * y 1 ^ β.2) • u y)) = _
    rw [← mul_smul]
    have hc : ((1 + y 0 ^ 2)⁻¹ * (1 + y 1 ^ 2)⁻¹) *
        ((1 + y 0 ^ 2) * (1 + y 1 ^ 2)) = 1 := by field_simp [h₀, h₁]
    rw [hc, one_smul]
  rw [he] at hp
  exact memLp_one_iff_integrable.mp hp

/-- Each coordinate is bounded by a fixed multiple of the quadratic weight. -/
theorem amplitudeId_coordinate_weight_bound (ϖ : ℝ) (hϖ : 0 < ϖ) (x y : ℝ) :
    |x| ≤ (1 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (x ^ 2 + y ^ 2)) := by
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hW : 1 ≤ 1 + ϖ ^ 2 * (x ^ 2 + y ^ 2) := le_add_of_nonneg_right (by positivity)
  have hsq : x ^ 2 ≤ (1 + ϖ ^ 2 * (x ^ 2 + y ^ 2)) / ϖ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hϖ)).mpr
    nlinarith only [sq_nonneg y, sq_nonneg ϖ]
  calc
    _ ≤ 1 + x ^ 2 := hx
    _ ≤ 1 + (1 + ϖ ^ 2 * (x ^ 2 + y ^ 2)) / ϖ ^ 2 := add_le_add le_rfl hsq
    _ ≤ (1 + ϖ ^ 2 * (x ^ 2 + y ^ 2)) +
      (1 + ϖ ^ 2 * (x ^ 2 + y ^ 2)) / ϖ ^ 2 := add_le_add hW le_rfl
    _ = _ := by ring

/-- A quadratic polynomial times the value is in L2 when its squared budget is finite. -/
theorem amplitudeId_quadratic_memLp (u : Vec 2 → E)
    (hu : AEStronglyMeasurable u volume) (ϖ : ℝ) (n : ℕ)
    (h : (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ (2 * n) * ‖u y‖ ^ 2)) < ⊤) :
    MemLp (fun y => (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n • u y) 2 volume := by
  let W := fun y : Vec 2 => 1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)
  apply (memLp_two_iff_integrable_sq_norm ((by fun_prop : Continuous (fun y => W y ^ n)).aestronglyMeasurable.smul hu)).mpr
  have he : (fun y => ‖W y ^ n • u y‖ ^ 2) =
      (fun y => W y ^ (2 * n) * ‖u y‖ ^ 2) := by
    funext y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by dsimp [W]; positivity), mul_pow, ← pow_mul]
    congr 2
    omega
  change Integrable (fun y => ‖W y ^ n • u y‖ ^ 2) volume
  rw [he]
  refine ⟨(by fun_prop : Continuous (fun y => W y ^ (2 * n))).aestronglyMeasurable.mul (hu.norm.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => by dsimp [W]; positivity))]
  exact h

/-- All quadratic-weight L2 budgets control each ordinary polynomial moment in L2. -/
theorem amplitudeId_monomial_memLp_of_weighted (u : Vec 2 → E)
    (hu : AEStronglyMeasurable u volume) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (h : ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖u y‖ ^ 2)) < ⊤)
    (β : ℕ × ℕ) : MemLp (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • u y) 2 volume := by
  let n := β.1 + β.2
  let W := fun y : Vec 2 => 1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)
  let A := 1 + (ϖ ^ 2)⁻¹
  have hw : MemLp (fun y => W y ^ n • u y) 2 volume :=
    amplitudeId_quadratic_memLp u hu ϖ n (h (2 * n))
  apply (hw.const_smul (A ^ n)).of_le
    (((by fun_prop : Continuous (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2))).aestronglyMeasurable.smul hu)
  apply Filter.Eventually.of_forall
  intro y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W y := by dsimp [W]; positivity
  have hx := amplitudeId_coordinate_weight_bound ϖ hϖ (y 0) (y 1)
  have hy := amplitudeId_coordinate_weight_bound ϖ hϖ (y 1) (y 0)
  have hy' : |y 1| ≤ A * W y := by
    change |y 1| ≤ (1 + (ϖ ^ 2)⁻¹) * (1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2))
    convert hy using 1
    ring
  have hb := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx β.1)
    (pow_le_pow_left₀ (abs_nonneg _) hy' β.2) (pow_nonneg (abs_nonneg _) _) (by positivity)
  change ‖(y 0 ^ β.1 * y 1 ^ β.2) • u y‖ ≤ ‖A ^ n • (W y ^ n • u y)‖
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hA _), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hW _)]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact hb.trans_eq (by dsimp only [n]; rw [← pow_add, mul_pow])

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The level-0 stage data identity

On a finite lattice box the Bloch sums of a compactly supported `g` are finite sums, the
`θ`-derivative `∂_θ^α` of `∑_k cos(θ·y_k) g(y_k)` is `∑_k cos^{(n)}(θ·y_k) y_k^α g(y_k)`, and
`exp(-it) = cos t - i sin t`; Parseval in `E` and `pair_norm_sq_iteratedDeriv` close the identity. -/

@[expose] public section

open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal RealInnerProductSpace

namespace AVRegularity.CycleWords.Assembly

universe u

/-- The word monomial of the `thetaPartial` tuple is the moment weight. -/
theorem wordMonomial_append_eq (a b : ℕ) (y : Vec 2) :
    wordMonomial (Fin.append (fun _ : Fin a => (0 : Fin 2)) (fun _ : Fin b => (1 : Fin 2))) y =
      momentWeight (a, b) y := by
  unfold wordMonomial momentWeight
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right, Finset.prod_const]

theorem thetaPartial_latticeSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (K : Finset (Fin 2 → ℤ)) (y : (Fin 2 → ℤ) → Vec 2)
    (H : (Fin 2 → ℤ) → E) (a b : ℕ) (θ : Vec 2) :
    thetaPartial a b (fun θ => ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) θ =
      ∑ k ∈ K, iteratedDeriv (a + b) ψ (vecDot θ (y k)) • (momentWeight (a, b) (y k) • H k) := by
  have hc : ∀ k ∈ K, ContDiffAt ℝ (a + b : ℕ) (fun θ => ψ (vecDot θ (y k)) • H k) θ :=
    fun k _ => ((contDiff_phase_smul hψ (y k) (H k)).of_le
      (by exact_mod_cast le_top)).contDiffAt
  unfold thetaPartial
  rw [show (fun θ => ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) =
    ∑ k ∈ K, fun θ => ψ (vecDot θ (y k)) • H k from (Finset.sum_fn _ _).symm,
    iteratedFDeriv_sum_apply hc, _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hT : (Fin.append (fun _ : Fin a => basisVec (0 : Fin 2))
      (fun _ : Fin b => basisVec (1 : Fin 2))) = fun l => basisVec
        (Fin.append (fun _ : Fin a => (0 : Fin 2)) (fun _ : Fin b => (1 : Fin 2)) l) := by
    funext l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [Fin.append_left, Fin.append_right]
  rw [hT, iteratedFDeriv_phase_smul_basis hψ (y k) (H k), wordMonomial_append_eq, mul_smul]

/-- Parseval: the squared norm of the pair of lattice sums from the components. -/
theorem sum_sq_inner_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (w : ι → E) :
    ∑ e, (∑ k ∈ s, c k * inner ℝ (b e) (w k)) ^ 2 = ‖∑ k ∈ s, c k • w k‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right (∑ k ∈ s, c k • w k)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Real.norm_eq_abs, sq_abs, inner_sum]
  simp [inner_smul_right]

theorem planeBlochC_eq_box {G : Vec 2 → ℝ} {R : ℝ} (hG : ∀ y : Vec 2, R < ‖y‖ → G y = 0)
    {N : ℕ} (hN : R + 1 ≤ N) {z : Vec 2} (hz : z ∈ AVenhance.unitCube) (θ : Vec 2) :
    planeBlochC θ G z = ∑ k ∈ latticeBox N, Complex.exp (-(Complex.I *
      (vecDot θ (z + fun i => (k i : ℝ)) : ℂ))) * (G (z + fun i => (k i : ℝ)) : ℂ) := by
  unfold planeBlochC
  refine tsum_eq_sum fun k hk => ?_
  rw [hG _ (lattice_far hN hz hk)]
  simp

theorem norm_sq_exp_sum (s : Finset (Fin 2 → ℤ)) (t G : (Fin 2 → ℤ) → ℝ) :
    ‖∑ k ∈ s, Complex.exp (-(Complex.I * (t k : ℂ))) * (G k : ℂ)‖ ^ 2 =
      (∑ k ∈ s, Real.cos (t k) * G k) ^ 2 + (∑ k ∈ s, Real.sin (t k) * G k) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (∑ k ∈ s, Complex.exp (-(Complex.I * (t k : ℂ))) * (G k : ℂ)).re =
      ∑ k ∈ s, Real.cos (t k) * G k := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -(Complex.I * (t k : ℂ)) = ((-t k : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him : (∑ k ∈ s, Complex.exp (-(Complex.I * (t k : ℂ))) * (G k : ℂ)).im =
      -∑ k ∈ s, Real.sin (t k) * G k := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -(Complex.I * (t k : ℂ)) = ((-t k : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hre, him]
  ring

/-- **The level-0 stage data identity.** -/
theorem levelZeroData : LevelZeroDataStatement.{u} := by
  intro E _ _ _ n b g hgc α θ z hz
  obtain ⟨R, -, hR⟩ := exists_support_radius hgc
  set N : ℕ := ⌈R⌉₊ + 1 with hNdef
  have hN : R + 1 ≤ N := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil R]
  set y : (Fin 2 → ℤ) → Vec 2 := fun k => z + fun i => (k i : ℝ) with hy
  set t : (Fin 2 → ℤ) → ℝ := fun k => vecDot θ (y k) with ht
  set w : (Fin 2 → ℤ) → E := fun k => momentWeight α (y k) • g (y k) with hw
  have hbox : ∀ ψ : ℝ → ℝ, ∀ θ' : Vec 2,
      blochPhase ψ θ' g z = ∑ k ∈ latticeBox N, ψ (vecDot θ' (y k)) • g (y k) :=
    fun ψ θ' => blochPhase_eq_box ψ hR hN hz θ'
  -- left side
  have hL : ∀ e, ‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2 =
      (∑ k ∈ latticeBox N, Real.cos (t k) * inner ℝ (b e) (w k)) ^ 2 +
        (∑ k ∈ latticeBox N, Real.sin (t k) * inner ℝ (b e) (w k)) ^ 2 := by
    intro e
    rw [planeBlochC_eq_box (R := R) (fun y hy => by simp [hR y hy]) hN hz θ]
    have := norm_sq_exp_sum (latticeBox N) t
      (fun k => momentWeight α (y k) * inner ℝ (b e) (g (y k)))
    rw [this]
    simp only [hw, inner_smul_right]
  rw [Finset.sum_congr rfl fun e _ => hL e, Finset.sum_add_distrib,
    sum_sq_inner_sum b _ _ w, sum_sq_inner_sum b _ _ w]
  -- right side
  have hC : (fun θ' => blochCos θ' g z) =
      fun θ' => ∑ k ∈ latticeBox N, Real.cos (vecDot θ' (y k)) • g (y k) :=
    funext fun θ' => (blochCos_eq_blochPhase θ' g z).trans (hbox _ θ')
  have hS : (fun θ' => blochSin θ' g z) =
      fun θ' => ∑ k ∈ latticeBox N, Real.sin (vecDot θ' (y k)) • g (y k) :=
    funext fun θ' => (blochSin_eq_blochPhase θ' g z).trans (hbox _ θ')
  rw [hC, hS, thetaPartial_latticeSum Real.contDiff_cos, thetaPartial_latticeSum Real.contDiff_sin,
    pair_norm_sq_iteratedDeriv (latticeBox N) t w (α.1 + α.2)]

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Jointly measurable versions of time-dependent fields

Pointwise representatives of a time-dependent `L²` field are chosen separately at each time, so
`(t, y) ↦ f t y` need not be measurable. This module builds a jointly strongly measurable version.

`exists_stronglyMeasurable_version`: if every slice `f t` is locally integrable and every
mollified value `t ↦ (φ ⋆ f t)(y)` is strongly measurable, there is a strongly measurable
`G : ℝ × Vec 2 → E` with `G(t, ·) = f t` a.e. for **every** `t`. The construction:
`G = lim_k φ_k ⋆ f t`, with bumps `φ_k` of radius `1/(k+1)`. Each `φ_k ⋆ f t` is continuous in
`y` (`HasCompactSupport.continuous_convolution_left`), so `(t, y) ↦ (φ_k ⋆ f t)(y)` is jointly
measurable (`stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable`). The limit is
measurable (`StronglyMeasurable.limUnder`) and equals `f t` a.e. by Lebesgue differentiation
(`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`).

`exists_cellCurve_version`: an `L²(cell)`-valued curve, a.e. strongly measurable in time, has a
jointly strongly measurable version whose slices equal the curve on the cell for a.e. time. If
the curve is in `L²` in time, the version is in `L²` of the product. This is the form that
`cellSolution_to_Hilbert` needs, applied to the literal sources of the amplitude identification
through their time carriers. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Homogenization AVRegularity.CycleEvolution
open scoped Topology ENNReal Convolution

namespace AVRegularity.CycleWords.Assembly

/-- The bump of radius `1/(k+1)`. -/
def versionBump (k : ℕ) : ContDiffBump (0 : Vec 2) where
  rIn := 1 / (2 * ((k : ℝ) + 1))
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) hk]
    linarith

theorem versionBump_rOut_tendsto : Tendsto (fun k => (versionBump k).rOut) atTop (𝓝 0) := by
  simp only [versionBump]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem versionBump_rOut_le (k : ℕ) : (versionBump k).rOut ≤ 2 * (versionBump k).rIn := by
  simp only [versionBump]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [mul_one_div]
  exact le_of_eq (by field_simp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The mollified field. -/
def mollifiedField (f : ℝ → Vec 2 → E) (k : ℕ) (t : ℝ) (y : Vec 2) : E :=
  ((versionBump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f t) y

/-- **A jointly strongly measurable version** of a field with locally integrable slices whose
mollified values are measurable in time. -/
theorem exists_stronglyMeasurable_version (f : ℝ → Vec 2 → E)
    (hf : ∀ t, LocallyIntegrable (f t) volume)
    (hm : ∀ k y, StronglyMeasurable fun t => mollifiedField f k t y) :
    ∃ G : ℝ × Vec 2 → E, StronglyMeasurable G ∧ ∀ t, (fun y => G (t, y)) =ᵐ[volume] f t := by
  have hcont : ∀ k t, Continuous (mollifiedField f k t) := fun k t =>
    HasCompactSupport.continuous_convolution_left _ (versionBump k).hasCompactSupport_normed
      (versionBump k).continuous_normed (hf t)
  have hjoint : ∀ k, StronglyMeasurable fun p : ℝ × Vec 2 => mollifiedField f k p.1 p.2 := by
    intro k
    have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (y : Vec 2) (t : ℝ) => mollifiedField f k t y)
      (fun t => hcont k t) (fun y => hm k y)
    exact h.comp_measurable measurable_swap
  have hE : Nonempty E := ⟨0⟩
  refine ⟨fun p => limUnder atTop (fun k => mollifiedField f k p.1 p.2),
    StronglyMeasurable.limUnder hjoint, fun t => ?_⟩
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := versionBump) (l := atTop) (K := 2) versionBump_rOut_tendsto
    (Eventually.of_forall versionBump_rOut_le) (hf t)
  filter_upwards [hae] with y hy
  exact hy.limUnder_eq

section Cell

local instance jointVersionProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem measurableSet_unitCube : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem versionBump_bound (k : ℕ) :
    ∃ C : ℝ, ∀ x : Vec 2, ‖(versionBump k).normed volume x‖ ≤ C :=
  (versionBump k).hasCompactSupport_normed.exists_bound_of_continuous
    (versionBump k).continuous_normed

/-- The cell `L²` class of `w ↦ φ_k(y - w)`. -/
def cellBumpTest (k : ℕ) (y : Vec 2) : ComplexCellL2 :=
  (MemLp.of_bound (p := 2) (μ := volume.restrict AVenhance.unitCube)
    (f := fun w : Vec 2 => (((versionBump k).normed volume (y - w) : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp ((versionBump k).continuous_normed.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (versionBump_bound k).choose
    (Eventually.of_forall fun w => by
      rw [Complex.norm_real]
      exact (versionBump_bound k).choose_spec _)).toLp _

/-- The mollified value of a cell field (extended by `0`) is its pairing with the bump test. -/
theorem mollifiedField_cell_eq (R : ℝ → ComplexCellL2) (k : ℕ) (t : ℝ) (y : Vec 2) :
    mollifiedField (fun t => AVenhance.unitCube.indicator (R t : Vec 2 → ℂ)) k t y =
      inner ℂ (cellBumpTest k y) (R t) := by
  unfold mollifiedField
  rw [convolution_def]
  have hsub := integral_sub_left_eq_self (μ := (volume : Measure (Vec 2)))
    (fun w => ((versionBump k).normed volume (y - w)) •
      AVenhance.unitCube.indicator (R t : Vec 2 → ℂ) w) y
  simp only [sub_sub_cancel] at hsub
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [hsub, MeasureTheory.L2.inner_def]
  have hind : (fun w => ((versionBump k).normed volume (y - w)) •
      AVenhance.unitCube.indicator (R t : Vec 2 → ℂ) w) =
      AVenhance.unitCube.indicator (fun w => ((versionBump k).normed volume (y - w)) •
        (R t : Vec 2 → ℂ) w) := by
    funext w
    by_cases hw : w ∈ AVenhance.unitCube
    · simp only [Set.indicator_of_mem hw]
    · simp only [Set.indicator_of_notMem hw, smul_zero]
  rw [hind, integral_indicator measurableSet_unitCube]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict AVenhance.unitCube) (p := 2)
    (f := fun w : Vec 2 => (((versionBump k).normed volume (y - w) : ℝ) : ℂ)) _] with w hw
  unfold cellBumpTest
  rw [hw, Complex.real_smul, RCLike.inner_apply, Complex.conj_ofReal]
  ring

/-- **A jointly strongly measurable version of a cell curve.** -/
theorem exists_cellCurve_version {μt : Measure ℝ} (R : ℝ → ComplexCellL2)
    (hR : AEStronglyMeasurable R μt) :
    ∃ G : ℝ × Vec 2 → ℂ, StronglyMeasurable G ∧
      ∀ᵐ t ∂μt, (fun y => G (t, y)) =ᵐ[volume.restrict AVenhance.unitCube] R t := by
  set R' := hR.mk R with hR'def
  have hR'm : StronglyMeasurable R' := hR.stronglyMeasurable_mk
  have hf : ∀ t, LocallyIntegrable (AVenhance.unitCube.indicator (R' t : Vec 2 → ℂ)) volume :=
    fun t => ((integrable_indicator_iff measurableSet_unitCube).2
      ((Lp.memLp (R' t)).integrable one_le_two)).locallyIntegrable
  have hm : ∀ k y, StronglyMeasurable fun t =>
      mollifiedField (fun t => AVenhance.unitCube.indicator (R' t : Vec 2 → ℂ)) k t y := by
    intro k y
    simp only [mollifiedField_cell_eq]
    exact (innerSL ℂ (cellBumpTest k y)).continuous.comp_stronglyMeasurable hR'm
  obtain ⟨G, hG, hGs⟩ := exists_stronglyMeasurable_version _ hf hm
  refine ⟨G, hG, ?_⟩
  filter_upwards [hR.ae_eq_mk] with t ht
  rw [ht]
  filter_upwards [ae_restrict_of_ae (hGs t), ae_restrict_mem measurableSet_unitCube] with y hy hyc
  rw [hy, Set.indicator_of_mem hyc]

/-- **The version is in `L²` of the product** when the curve is in `L²` in time. -/
theorem cellCurve_version_memLp {μt : Measure ℝ} [SFinite μt] (R : ℝ → ComplexCellL2)
    (hR : MemLp R 2 μt) (G : ℝ × Vec 2 → ℂ) (hG : StronglyMeasurable G)
    (hGs : ∀ᵐ t ∂μt, (fun y => G (t, y)) =ᵐ[volume.restrict AVenhance.unitCube] R t) :
    MemLp G 2 (μt.prod (volume.restrict AVenhance.unitCube)) := by
  rw [memLp_iff, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hG.aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm]
  have hR' := hR
  rw [memLp_iff, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hR.aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm] at hR'
  simp only [ENNReal.toReal_ofNat] at hR' ⊢
  refine lt_of_le_of_lt (le_of_eq ?_) hR'
  congr 1
  rw [lintegral_prod _ (hG.enorm.pow_const _).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hGs] with t ht
  have hn : ‖R t‖ₑ =
      (∫⁻ y in AVenhance.unitCube, ‖(R t : Vec 2 → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable _), eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofNat]
  rw [hn, ← ENNReal.rpow_mul]
  norm_num
  exact lintegral_congr_ae (ht.mono fun y hy => by simp only at hy ⊢; rw [hy])

end Cell

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # Terminal output, part 1: phase integrals, Parseval and the coordinate identity

Calculus only. For a real integrable `g`, `‖∫ e^{-iθ·y} g‖² = (∫ cos g)² + (∫ sin g)²`. For an
integrable vector function and an orthonormal basis, `‖∫ ψ • W‖² = ∑_e (∫ ψ ⟨b_e, W⟩)²`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.CycleWords.Assembly

theorem toVecDot_continuous (θ : Vec 2) : Continuous fun y : Vec 2 => vecDot θ y := by
  unfold vecDot; fun_prop

theorem toIntegrable_cos_mul (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Integrable fun y => Real.cos (vecDot θ y) * g y :=
  hg.norm.mono' ((Real.continuous_cos.comp (toVecDot_continuous θ)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => by
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg (g y)) ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)

theorem toIntegrable_sin_mul (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Integrable fun y => Real.sin (vecDot θ y) * g y :=
  hg.norm.mono' ((Real.continuous_sin.comp (toVecDot_continuous θ)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => by
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg (g y)) ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_sin_le_one _)

theorem toPhase_pointwise (x g : ℝ) :
    Complex.exp (-(Complex.I * (x : ℂ))) * (g : ℂ) =
      ((Real.cos x * g : ℝ) : ℂ) - ((Real.sin x * g : ℝ) : ℂ) * Complex.I := by
  have : -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

/-- **Phase integral and cos/sin.** -/
theorem toPhase_norm_sq (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    ‖∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ)‖ ^ 2 =
      (∫ y, Real.cos (vecDot θ y) * g y) ^ 2 + (∫ y, Real.sin (vecDot θ y) * g y) ^ 2 := by
  simp_rw [toPhase_pointwise]
  have h1 : Integrable (fun y => ((Real.cos (vecDot θ y) * g y : ℝ) : ℂ)) :=
    (toIntegrable_cos_mul θ hg).ofReal
  have h2 : Integrable (fun y => ((Real.sin (vecDot θ y) * g y : ℝ) : ℂ) * Complex.I) :=
    (toIntegrable_sin_mul θ hg).ofReal.mul_const Complex.I
  rw [integral_sub h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- A continuous bounded scalar weight preserves integrability. -/
theorem toIntegrable_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Vec 2 → ℝ}
    (hc : Continuous c) (B : ℝ) (hB : ∀ y, |c y| ≤ B) {f : Vec 2 → E} (hf : Integrable f) :
    Integrable fun y => c y • f y :=
  (hf.norm.const_mul B).mono' (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))

/-- **Parseval for a vector-valued integral.** -/
theorem toParseval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Vec 2 → E) (ψ : Vec 2 → ℝ)
    (hψ : Integrable fun y => ψ y • W y) :
    ‖∫ y, ψ y • W y‖ ^ 2 =
      ∑ e : Fin (Module.finrank ℝ E),
        (∫ y, ψ y * inner ℝ (stdOrthonormalBasis ℝ E e) (W y)) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← integral_inner hψ, Real.norm_eq_abs, sq_abs]
  simp_rw [real_inner_smul_right]

/-- **The coordinate identity of the moment amplitude of one component.** -/
theorem toComponent_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (ϖ : ℝ) (β : ℕ × ℕ) (θ : Vec 2) (W : Vec 2 → E)
    (hm : Integrable fun y => momentWeight β y • W y) :
    ‖∫ y, (Real.cos (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • W y‖ ^ 2 +
      ‖∫ y, (Real.sin (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • W y‖ ^ 2 =
    ϖ ^ (2 * (β.1 + β.2)) * ∑ e : Fin (Module.finrank ℝ E),
      ‖∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeight β y * inner ℝ (stdOrthonormalBasis ℝ E e) (W y) : ℝ) : ℂ)‖ ^ 2 := by
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → (∀ x, |φ x| ≤ 1) →
      Integrable fun y => (φ (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • W y := by
    intro φ hφ hφ1
    have h1 : ∀ y : Vec 2, (φ (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • W y =
        (ϖ ^ (β.1 + β.2) * φ (vecDot θ y)) • (momentWeight β y • W y) := by
      intro y
      rw [smul_smul]
      congr 1
      unfold momentWeight
      rw [mul_pow, mul_pow, pow_add]
      ring
    simp_rw [h1]
    refine toIntegrable_smul (c := fun y => ϖ ^ (β.1 + β.2) * φ (vecDot θ y))
      (continuous_const.mul (hφ.comp (toVecDot_continuous θ))) (|ϖ| ^ (β.1 + β.2)) (fun y => ?_) hm
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (by positivity) (hφ1 _)
  have hcos := hint Real.cos Real.continuous_cos Real.abs_cos_le_one
  have hsin := hint Real.sin Real.continuous_sin Real.abs_sin_le_one
  rw [toParseval _ _ hcos, toParseval _ _ hsin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hg : Integrable fun y => momentWeight β y * inner ℝ (stdOrthonormalBasis ℝ E e) (W y) := by
    have := (innerSL ℝ (stdOrthonormalBasis ℝ E e)).integrable_comp hm
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [toPhase_norm_sq θ hg]
  have hw : ∀ (φ : ℝ → ℝ) (y : Vec 2), φ (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2 *
      inner ℝ (stdOrthonormalBasis ℝ E e) (W y) =
      ϖ ^ (β.1 + β.2) * (φ (vecDot θ y) * (momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ E e) (W y))) := by
    intro φ y
    unfold momentWeight
    rw [mul_pow, mul_pow, pow_add]
    ring
  simp_rw [hw, integral_const_mul]
  rw [pow_mul']
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The slow damping on the separated disc (the gauge hypothesis `hgauge` of `afw_bound`)

At a real frequency the package symbol is `λ = -η ξ·Gξ - i ⟨b r⟩`. The metric form is at most
`2|ξ|²` (`IsCellMetric`) and the drift coupling is at most `C_w C_g |ξ|²`, so the slow damping is
`-Re λ ≤ (2 + C_w C_g)|ξ|²` (`scalarPackageSymbol_neg_re_le`). On the retained disc `|ξ| ≤ 2ξ_lo`
this is at most `π²/16` by the smallness of the retained disc. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

local instance slowDampingProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The metric form at a real frequency is at most twice the square of the frequency. -/
theorem fibreQuad_re_le_two {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : ∀ ξ : Vec 2, ∑ i, ∑ j, ξ i * M i j * ξ j ≤ 2 * ∑ i, ξ i ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : ∀ i, (ξ i).im = 0) :
    (fibreQuad M ξ).re ≤ 2 * fibreNorm ξ ^ 2 := by
  have hreal : ∀ i, ξ i = ((ξ i).re : ℂ) := fun i => Complex.ext rfl (by simp [hξ i])
  have hq : fibreQuad M ξ = ((∑ i, ∑ j, (ξ i).re * M i j * (ξ j).re : ℝ) : ℂ) := by
    unfold fibreQuad
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hreal i, hreal j]
      simp
  have hn : fibreNorm ξ ^ 2 = ∑ i, (ξ i).re ^ 2 := by
    unfold fibreNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hreal i, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp
  rw [hq, Complex.ofReal_re, hn]
  exact hM fun i => (ξ i).re

/-- **The slow damping.** -/
theorem scalarPackageSymbol_neg_re_le {K : ScalarConstants} {η t0 S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (ξ : Fin 2 → ℂ) (hξr : ∀ i, (ξ i).im = 0) (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    -(fibreSeriesC data.lam ξ t).re ≤ (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 := by
  let D := fibreSeriesJet data.r ξ
  let b := fibreDriftCoupling η v ξ t
  have hd : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube) :=
    (scalarPackageGraph_memLp data ξ hξ t)
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)
  have hB := fibreDriftCoupling_norm_le η K.Cw v hw ξ t
  have hm := cellMultiplier_memLp b (cellValue D t) (K.Cw * fibreNorm ξ) hb hB hd
  have hnmean := (cellMean_enorm_le_cellL2Norm _ hm).trans
    ((cellL2Norm_mul_le b (cellValue D t) (K.Cw * fibreNorm ξ)
      (hb.aestronglyMeasurable.mul hd.aestronglyMeasurable)
      (Filter.Eventually.of_forall hB)).trans
      (mul_le_mul' le_rfl ((cellValue_cellL2Norm_le_energy D t).trans
        (data.graph.2.1 ξ hξ).2.2.2.2)))
  have hn : ‖cellMean (fun x => b x * cellValue D t x)‖ ≤
      (K.Cw * fibreNorm ξ) * (K.Cg * fibreNorm ξ) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul
      (mul_nonneg hCw (fibreNorm_nonneg ξ))] at hnmean
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ))
        (mul_nonneg hCg (fibreNorm_nonneg ξ)))).mp hnmean
  have hq := fibreQuad_re_le_two (M := G t) (fun ξ' => (hG.2.2.2 t 0 ξ').2) ξ hξr
  rw [(data.graph.2.1 ξ hξ).2.2.2.1 t]
  have hre : ∀ m : ℂ, -((-(η : ℂ) * fibreQuad (G t) ξ - Complex.I * m).re) =
      η * (fibreQuad (G t) ξ).re - m.im := by
    intro m
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  have h1 : η * (fibreQuad (G t) ξ).re ≤ 2 * fibreNorm ξ ^ 2 := by
    have h2 : 0 ≤ 2 * fibreNorm ξ ^ 2 := by positivity
    by_cases hqn : (fibreQuad (G t) ξ).re ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos hη0 hqn).trans h2
    · push Not at hqn
      calc η * (fibreQuad (G t) ξ).re ≤ 1 * (fibreQuad (G t) ξ).re :=
            mul_le_mul_of_nonneg_right hη1 hqn.le
        _ ≤ _ := by rw [one_mul]; exact hq
  have key : ∀ m : ℂ, ‖m‖ ≤ K.Cw * K.Cg * fibreNorm ξ ^ 2 →
      η * (fibreQuad (G t) ξ).re - m.im ≤ (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 := by
    intro m hm
    have him : -m.im ≤ ‖m‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm m)
    linarith
  exact key _ (hn.trans_eq (by ring))

/-- **The gauge growth** (the hypothesis `hgauge` of `afw_bound`). With `σ = (2 + C_w C_g)ρ²` and
`|ξ| ≤ ρ`, the gauge `Γ = |e^{-∫λ}|` grows at most like `e^{σ(s - r)}`. -/
theorem scalarPackage_gauge_growth {K : ScalarConstants} {η t0 S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t0 S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw)
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (ξ : Fin 2 → ℂ) (hξr : ∀ i, (ξ i).im = 0) (hξ : fibreNorm ξ < K.ξ0) {ρ : ℝ}
    (hξρ : fibreNorm ξ ≤ ρ) {r s : ℝ} (hrs : r ≤ s)
    (hint : IntervalIntegrable (fun τ => fibreSeriesC data.lam ξ τ) volume r s) :
    ‖Complex.exp (-∫ τ in r..s, fibreSeriesC data.lam ξ τ)‖ ≤
      Real.exp ((2 + K.Cw * K.Cg) * ρ ^ 2 * (s - r)) := by
  rw [Complex.norm_exp, Complex.neg_re]
  apply Real.exp_le_exp.2
  have hre : (∫ τ in r..s, fibreSeriesC data.lam ξ τ).re =
      ∫ τ in r..s, (fibreSeriesC data.lam ξ τ).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rfl
  rw [hre, ← intervalIntegral.integral_neg]
  have hσ : ∀ τ, -(fibreSeriesC data.lam ξ τ).re ≤ (2 + K.Cw * K.Cg) * ρ ^ 2 := by
    intro τ
    refine (scalarPackageSymbol_neg_re_le data hη0 hη1 hCg hCw hG hv hw ξ hξr hξ τ).trans ?_
    have : fibreNorm ξ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξρ 2
    have hc : 0 ≤ 2 + K.Cw * K.Cg := by positivity
    exact mul_le_mul_of_nonneg_left this hc
  have hreint : IntervalIntegrable (fun τ => (fibreSeriesC data.lam ξ τ).re) volume r s :=
    ⟨hint.1.re, hint.2.re⟩
  calc ∫ τ in r..s, -(fibreSeriesC data.lam ξ τ).re
      ≤ ∫ _τ in r..s, (2 + K.Cw * K.Cg) * ρ ^ 2 :=
        intervalIntegral.integral_mono_on hrs hreint.neg intervalIntegrable_const
          fun τ _ => hσ τ
    _ = (2 + K.Cw * K.Cg) * ρ ^ 2 * (s - r) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

end AVRegularity.CycleWords.Assembly
end
end
end
