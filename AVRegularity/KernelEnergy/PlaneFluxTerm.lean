-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizerTorus
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.KernelEnergy.TorusMultiplierCLM
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelSchurMatrix
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! The spatial regularizer (`IsSpatialRegularizerTorus`) supplies a canonical bounded linear map
on the same-order Sobolev carrier. Linearity follows from uniqueness of weak jets. -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

theorem torusRegularizer_exists_sameOrder (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : TorusHk k G) :
    ∃ y : TorusHk k G,
      y.val (valueIndex2 k) = S t (z.val (valueIndex2 k)) ∧
      factorialNormSq ρ y.val ≤ (c 0) ^ 2 * factorialNormSq ρ z.val := by
  simpa only [Nat.add_zero, pow_zero, div_one, derivFactorialNormSq,
    factorialNormSq, derivativeNormSq] using hS.2.2.2 t ht 0 (by omega) z

def torusRegularizerCarrier (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : TorusHk k G) : TorusHk k G :=
  Classical.choose (torusRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)

theorem torusRegularizerCarrier_value (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : TorusHk k G) :
    (torusRegularizerCarrier ρ k D hD a b c r S hS t ht z).val (valueIndex2 k) =
      S t (z.val (valueIndex2 k)) :=
  (Classical.choose_spec (torusRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)).1

theorem torusRegularizerCarrier_factorial_bound (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : TorusHk k G) :
    factorialNormSq ρ (torusRegularizerCarrier ρ k D hD a b c r S hS t ht z).val ≤
      (c 0) ^ 2 * factorialNormSq ρ z.val :=
  (Classical.choose_spec (torusRegularizer_exists_sameOrder ρ k D hD a b c r S hS t ht z)).2

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! A single factorial component is controlled by the common weighted mass. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
  {μ : Measure (Vec 2)} {K : ι → ℕ}

theorem componentFactorialRoot_le_mass (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, JetL2 μ (K i) (E i)) (i : ι) :
    Real.sqrt (factorialNormSq ρ (u i)) ≤ Real.sqrt (π i) * Real.sqrt (massNormSq ρ π u) := by
  have h := Real.sqrt_le_sqrt (componentFactorial_le_mass ρ π hπ u i)
  rwa [Real.sqrt_mul (hπ i).le] at h

variable [∀ i, InnerProductSpace ℝ (E i)]

theorem componentFactorialPairing_abs_le_mass (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u w : ∀ i, JetL2 μ (K i) (E i)) (i : ι) :
    |inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (u i))
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (w i))| ≤
      π i * Real.sqrt (massNormSq ρ π u) * Real.sqrt (massNormSq ρ π w) := by
  have h := factorialPairing_abs_le ρ (u i) (w i)
  rw [← factorialWeightedJet_inner] at h
  have hm := mul_le_mul (componentFactorialRoot_le_mass ρ π hπ u i)
    (componentFactorialRoot_le_mass ρ π hπ w i) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have he : (Real.sqrt (π i) * Real.sqrt (massNormSq ρ π u)) *
      (Real.sqrt (π i) * Real.sqrt (massNormSq ρ π w)) =
      π i * Real.sqrt (massNormSq ρ π u) * Real.sqrt (massNormSq ρ π w) := by
    rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (hπ i).le]
    ring
  exact h.trans (hm.trans_eq he)

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

def torusKernelFluxTerm {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t))
    (Y : TorusHk (K + (m + 1)) G) :
    TorusHk K (PiLp 2 (fun _ : Fin 2 => H)) := by
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 r :=
    congrArg DerivativeWord2 hr.symm
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  exact (mapTorusHk L.toContinuousLinearMap
      (torusDerivativeTensor (K := K) (r := m + 1) Y)).mulCoefficient
      (A t) hC hp
      (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
        (Nat.le_of_lt_succ l.isLt) t ht x)

theorem torusKernelFluxTerm_base_ae
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t))
    (Y : TorusHk (K + (m + 1)) G) :
    (torusKernelFluxTerm hr ρ hρ a b A hA t ht hC hp Y).toFunction.jet
        (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => A t x (WithLp.toLp 2 fun word : DerivativeWord2 r =>
        Y.toFunction.jet ⟨⟨r, by omega⟩, word⟩ x) := by
  cases hr
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 (m + 1) := rfl
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 (m + 1) := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  let W := torusDerivativeTensor (K := K) (r := m + 1) Y
  have hmul := torusMulCoefficient_toFunction_value_ae
    (mapTorusHk L.toContinuousLinearMap W) (A t) hC hp
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)
  have hmap := mapTorusHk_toFunction_jet_ae L.toContinuousLinearMap W (valueIndex2 K)
  have htensor := torusDerivativeTensor_base_ae (K := K) (r := m + 1) Y
  unfold torusKernelFluxTerm
  filter_upwards [hmul, hmap, htensor] with x hmulx hmapx htx
  have hL : L (WithLp.toLp 2 fun w : DerivativeWord2 (m + 1) =>
      Y.toFunction.jet (prefixJetIndex w (valueIndex2 K)) x) =
      WithLp.toLp 2 (fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x) := by
    apply PiLp.ext
    intro w
    simp [L, derivativeWordArrayIsometry, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', e, prefixJetIndex, valueIndex2, valueIndex]
  calc
    ((mapTorusHk L.toContinuousLinearMap W).mulCoefficient (A t) hC hp
        (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA
          l.val (Nat.le_of_lt_succ l.isLt) t ht x)).toFunction.jet
        (valueIndex2 K) x =
      A t x ((mapTorusHk L.toContinuousLinearMap W).toFunction.jet
        (valueIndex2 K) x) := hmulx
    _ = A t x (L (W.toFunction.jet (valueIndex2 K) x)) :=
      congrArg (A t x) hmapx
    _ = A t x (L (WithLp.toLp 2 fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet (prefixJetIndex w (valueIndex2 K)) x)) := by
      rw [htx]
    _ = A t x (WithLp.toLp 2 (fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x)) := congrArg (A t x) hL

theorem torusKernelFluxTerm_factorialNorm_le
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t))
    (Y : TorusHk (K + (m + 1)) G)
    (γ : ℝ) (hγ : 0 ≤ γ) (Cnorm : ℝ) (hCnorm : 0 ≤ Cnorm)
    (X : ℝ) (_hX : 0 ≤ X)
    (hY : derivFactorialNormSq (m + 1) ρ Y.val ≤ γ ^ 2 * Cnorm ^ 2 * X) :
    Real.sqrt (factorialNormSq ρ
      (torusKernelFluxTerm hr ρ hρ a b A hA t ht hC hp Y).val) ≤
      (coefficientSeminorm ρ K a b A).toReal * γ * Cnorm * Real.sqrt X := by
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 r :=
    congrArg DerivativeWord2 hr.symm
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  let W := torusDerivativeTensor (K := K) (r := m + 1) Y
  have hmul := torusMultiplyIntervalCoefficient_factorialNorm_le ρ hρ K a b A hA
    t ht hC hp (mapTorusHk L.toContinuousLinearMap W)
  have hmap := mapTorusHk_factorialNormSq_le ρ L.toContinuousLinearMap W
  have hLn : ‖L.toContinuousLinearMap‖ ≤ 1 :=
    L.toLinearIsometry.norm_toContinuousLinearMap_le
  have hW : factorialNormSq ρ (mapTorusHk L.toContinuousLinearMap W).val ≤
      factorialNormSq ρ W.val := by
    calc
      factorialNormSq ρ (mapTorusHk L.toContinuousLinearMap W).val ≤
          ‖L.toContinuousLinearMap‖ ^ 2 * factorialNormSq ρ W.val := hmap
      _ ≤ 1 ^ 2 * factorialNormSq ρ W.val := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith [norm_nonneg L.toContinuousLinearMap]
        · exact factorialNormSq_nonneg ρ W.val
      _ = factorialNormSq ρ W.val := by ring
  have hTensor := torusDerivativeTensor_factorialNormSq ρ Y
  have hsem : 0 ≤ (coefficientSeminorm ρ K a b A).toReal := ENNReal.toReal_nonneg
  have hrootY : Real.sqrt (factorialNormSq ρ W.val) ≤ γ * Cnorm * Real.sqrt X := by
    rw [hTensor]
    calc
      Real.sqrt (derivFactorialNormSq (m + 1) ρ Y.val) ≤
          Real.sqrt (γ ^ 2 * Cnorm ^ 2 * X) := Real.sqrt_le_sqrt hY
      _ = γ * Cnorm * Real.sqrt X := by
        rw [Real.sqrt_mul (mul_nonneg (sq_nonneg γ) (sq_nonneg Cnorm)),
          Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq_eq_abs, abs_of_nonneg hγ,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hCnorm]
  calc
    Real.sqrt (factorialNormSq ρ
        (torusKernelFluxTerm hr ρ hρ a b A hA t ht hC hp Y).val) ≤
      (coefficientSeminorm ρ K a b A).toReal *
        Real.sqrt (factorialNormSq ρ (mapTorusHk L.toContinuousLinearMap W).val) := hmul
    _ ≤ (coefficientSeminorm ρ K a b A).toReal * Real.sqrt (factorialNormSq ρ W.val) := by
      apply mul_le_mul_of_nonneg_left _ hsem
      exact Real.sqrt_le_sqrt hW
    _ ≤ (coefficientSeminorm ρ K a b A).toReal * (γ * Cnorm * Real.sqrt X) := by
      exact mul_le_mul_of_nonneg_left hrootY hsem
    _ = _ := by ring

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Original kernel hypotheses bundled for reuse in coefficient ODE and
Bochner-limit constructions. All bounds here are premises of `kernel_energy_torus`. -/

structure TorusKernelOperator (t₀ t₁ ρ ν : ℝ) (k D : ℕ)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    where
  htime : t₀ ≤ t₁
  radius_pos : 0 < ρ
  diffusivity_pos : 0 < ν
  order_ge_two : 2 ≤ D
  π : ι → ℝ
  hπ : ∀ i, 0 < π i
  B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))
  hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => B i j α d p.1 p.2
  hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t)
  hB_per : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (B i j α d t)
  hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤
  C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α
  S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))
  c : ℕ → ℝ
  r : ∀ i j, Γ i j → ℝ
  hr : ∀ i j α, 0 < r i j α
  hS : ∀ i j α, IsSpatialRegularizerTorus ρ k D t₀ t₁ c (r i j α) (S i j α)
  θ : ℝ
  hθ : θ ≤ 1 / 8
  hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B)

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! Short spatial and temporal flux arithmetic with a fixed carrier instance. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem torusValuePairing_add (F Q : TorusHk K E)
    (ψ : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM (F + Q) x) (ψ x)) =
    (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM F x) (ψ x)) +
    (∫ x in AVenhance.unitCube, inner ℝ (torusHkValueCLM Q x) (ψ x)) := by
  have he := (torusHkValueCLM (E := E) (K := K)).map_add F Q
  have hi := inner_add_left (torusHkValueCLM F) (torusHkValueCLM Q) ψ (𝕜 := ℝ)
  rw [← he] at hi
  simpa only [L2.inner_def] using hi

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! All regularizer gain levels together control the full Sobolev graph. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {k : ℕ}

theorem shiftedJet_level_bound (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ)
    (D : JetL2 μ (k + m) E) (j : Fin (k + 1)) :
    derivativeNormSq D ⟨j.val + m, by omega⟩ ≤
      derivFactorialNormSq m ρ D / factorialWeightMin ρ k := by
  have hm := factorialWeightMin_pos ρ hρ (K := k)
  let L : Fin (k + 1) → ℝ := fun i => factorialWeight ρ i.val *
    derivativeNormSq D ⟨i.val + m, by omega⟩
  have hL (i : Fin (k + 1)) : 0 ≤ L i :=
    mul_nonneg (factorialWeight_nonneg ρ i.val) (derivativeNormSq_nonneg D _)
  have hj : L j ≤ derivFactorialNormSq m ρ D :=
    Finset.single_le_sum (f := L) (fun i _ => hL i) (Finset.mem_univ j)
  rw [le_div_iff₀ hm, mul_comm]
  exact (mul_le_mul_of_nonneg_right (factorialWeightMin_le ρ j)
    (derivativeNormSq_nonneg D _)).trans hj

theorem shiftedJet_full_norm_bound [InnerProductSpace ℝ E] (ρ : ℝ) (hρ : 0 < ρ) (M : ℕ)
    (D : JetL2 μ (k + M) E) (B : ℝ)
    (hb : ∀ m : ℕ, ∀ hm : m ≤ M,
      derivFactorialNormSq m ρ (truncateJet (by omega : k + m ≤ k + M) D) ≤ B) :
    ‖D‖ ^ 2 ≤ (k + M + 1 : ℝ) * (B / factorialWeightMin ρ k) := by
  have hlevel (n : Fin (k + M + 1)) : derivativeNormSq D n ≤ B / factorialWeightMin ρ k := by
    let j : Fin (k + 1) := ⟨min n.val k, by omega⟩
    let m : ℕ := n.val - j.val
    have hsum : j.val + m = n.val := by dsimp [j, m]; omega
    have hm : m ≤ M := by dsimp [j, m]; omega
    have h := (shiftedJet_level_bound ρ hρ m
      (truncateJet (by omega : k + m ≤ k + M) D) j).trans
        (div_le_div_of_nonneg_right (hb m hm) (factorialWeightMin_pos ρ hρ (K := k)).le)
    have hn : (⟨j.val + m, by omega⟩ : Fin (k + M + 1)) = n := Fin.ext hsum
    change derivativeNormSq D ⟨j.val + m, by omega⟩ ≤ _ at h
    rw [hn] at h
    exact h
  rw [jet_norm_sq_eq_sum]
  calc
    _ ≤ ∑ _n : Fin (k + M + 1), B / factorialWeightMin ρ k :=
      Finset.sum_le_sum (fun n _ => hlevel n)
    _ = _ := by simp

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.KernelEnergy

/-! One additional periodic weak derivative from Sobolev lifts of the gradient. -/

private theorem torusJet_component_global_ae {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (u : TorusHk K E) (a : JetIndex2 K)
    (v : TorusHk L E) (b : JetIndex2 L) (h : u.val a = v.val b) :
    u.toFunction.jet a =ᵐ[volume] v.toFunction.jet b := by
  have hu := cellToTorus_global_ae u.val a
  have hv := cellToTorus_global_ae v.val b
  have hct := congrArg (fun z : Lp E 2 (volume.restrict AVenhance.unitCube) =>
    fun x : Vec 2 => cellToTorus z (torusQuotient x)) h
  have hglobal : (fun x : Vec 2 => cellToTorus (u.val a) (torusQuotient x)) =ᵐ[volume]
      fun x => cellToTorus (v.val b) (torusQuotient x) :=
    Filter.Eventually.of_forall (congrFun hct)
  exact hu.symm.trans (hglobal.trans hv)

private def upgradedTorusJet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (u : TorusHk 1 E) (g : Fin 2 → TorusHk K E) : RawJet2 (K + 1) E :=
  fun a =>
    if hz : a.1.val = 0 then
      u.toFunction.jet (valueIndex2 1)
    else
      let n := a.1.val - 1
      let hlen : n + 1 = a.1.val := by dsimp [n]; omega
      let w : DerivativeWord2 (n + 1) := fun i => a.2 (Fin.cast hlen i)
      (g (w ⟨0, by omega⟩)).toFunction.jet
        ⟨⟨n, by have ha := a.1.isLt; dsimp [n]; omega⟩, Fin.tail w⟩

private theorem upgradedTorusJet_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (u : TorusHk 1 E) (g : Fin 2 → TorusHk K E)
    (w : DerivativeWord2 0) :
    upgradedTorusJet u g ⟨⟨0, by omega⟩, w⟩ = u.toFunction.jet (valueIndex2 1) := by
  simp [upgradedTorusJet, valueIndex2, valueIndex]

private theorem upgradedTorusJet_succ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (u : TorusHk 1 E) (g : Fin 2 → TorusHk K E)
    (n : Fin (K + 1)) (w : DerivativeWord2 (n.val + 1)) :
    upgradedTorusJet u g ⟨n.succ, w⟩ =
      (g (w ⟨0, Nat.zero_lt_succ n.val⟩)).toFunction.jet ⟨n, Fin.tail w⟩ := by
  simp [upgradedTorusJet]

theorem exists_torusHk_succ_of_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (u : TorusHk 1 E)
    (g : Fin 2 → TorusHk K E)
    (hgrad : ∀ i, u.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
      (g i).val (valueIndex2 K)) :
    ∃ y : TorusHk (K + 1) E,
      y.val (valueIndex2 (K + 1)) = u.val (valueIndex2 1) := by
  classical
  let J := upgradedTorusJet u g
  have hmem : JetMemL2On AVenhance.unitCube J := by
    intro a
    change MemLp (upgradedTorusJet u g a) 2 (volume.restrict AVenhance.unitCube)
    by_cases hz : a.1.val = 0
    · simp [upgradedTorusJet, hz]
      exact u.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 1)
    · simp only [upgradedTorusJet, hz, dite_false]
      let n := a.1.val - 1
      let hlen : n + 1 = a.1.val := by dsimp [n]; omega
      let w : DerivativeWord2 (n + 1) := fun i => a.2 (Fin.cast hlen i)
      exact (g (w ⟨0, by omega⟩)).toFunction.hasPeriodicWeakJet.2.1 _
  have hperiodic : ∀ a, AVenhance.IsZ2Periodic (J a) := by
    intro a m x
    change upgradedTorusJet u g a (x + AVenhance.latticeShift m) =
      upgradedTorusJet u g a x
    by_cases hz : a.1.val = 0
    · simp [upgradedTorusJet, hz]
      exact u.toFunction.hasPeriodicWeakJet.1 (valueIndex2 1) m x
    · simp only [upgradedTorusJet, hz, dite_false]
      let n := a.1.val - 1
      let hlen : n + 1 = a.1.val := by dsimp [n]; omega
      let w : DerivativeWord2 (n + 1) := fun i => a.2 (Fin.cast hlen i)
      exact (g (w ⟨0, by omega⟩)).toFunction.hasPeriodicWeakJet.1 _ m x
  have hweak : HasOrderedWeakJetOn Set.univ J := by
    intro j w i e
    cases j using Fin.cases with
    | zero =>
      have hlo := upgradedTorusJet_zero u g w
      have hhi := upgradedTorusJet_succ u g ⟨0, by omega⟩ (Fin.snoc w i)
      have hwU := u.toFunction.hasPeriodicWeakJet.2.2
        ⟨0, Nat.zero_lt_succ 0⟩ Fin.elim0 i e
      have hgradGlobal : u.toFunction.jet (nextIndex2 ⟨0, Nat.zero_lt_succ 0⟩ Fin.elim0 i) =ᵐ[volume]
          (g i).toFunction.jet (valueIndex2 K) := by
        have hcell := torusJet_component_global_ae u
          (nextIndex2 ⟨0, Nat.zero_lt_succ 0⟩ Fin.elim0 i) (g i) (valueIndex2 K) (hgrad i)
        simpa [nextIndex2, nextIndex, valueIndex2, valueIndex] using hcell
      have hw : HasWeakPartialDerivOn Set.univ i
          (fun x => inner ℝ e (u.toFunction.jet (valueIndex2 1) x))
          (fun x => inner ℝ e ((g i).toFunction.jet (valueIndex2 K) x)) := by
        apply hasWeakPartialDerivOn_congr_ae _ _ hwU
        · filter_upwards [] with x
          rfl
        · simpa only [Measure.restrict_univ, Function.comp_def] using
            hgradGlobal.fun_comp (inner ℝ e)
      have hw0 : w = Fin.elim0 := by
        funext q
        exact Fin.elim0 q
      have hlo' : upgradedTorusJet u g (lowerIndex2 ⟨0, by omega⟩ w) =
          u.toFunction.jet (valueIndex2 1) := by
        simpa [lowerIndex2, lowerIndex] using hlo
      have hhi' : upgradedTorusJet u g (nextIndex2 ⟨0, by omega⟩ w i) =
          (g i).toFunction.jet (valueIndex2 K) := by
        rw [hw0, Fin.snoc_zero] at hhi
        have hsnoc0 : Fin.snoc w i = (fun _ : Fin 1 => i) := by
          rw [hw0]
          exact Fin.snoc_zero _ _
        have hidx : nextIndex2 ⟨0, by omega⟩ w i =
            ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ := by
          simp only [nextIndex2, nextIndex]
          rw [hsnoc0]
        rw [hidx]
        have htail0 : Fin.tail (fun _ : Fin 1 => i) = Fin.elim0 := by
          funext q
          exact Fin.elim0 q
        have hhead0 : (fun _ : Fin 1 => i) ⟨0, by omega⟩ = i := rfl
        simpa [valueIndex2, valueIndex, htail0, hhead0, Fin.snoc, Fin.tail] using hhi
      change HasWeakPartialDerivOn Set.univ i
        (fun x => inner ℝ e (upgradedTorusJet u g (lowerIndex2 ⟨0, by omega⟩ w) x))
        (fun x => inner ℝ e (upgradedTorusJet u g (nextIndex2 ⟨0, by omega⟩ w i) x))
      rw [hlo', hhi']
      exact hw
    | succ n =>
      let head : Fin 2 := w ⟨0, Nat.zero_lt_succ n.val⟩
      let tail : DerivativeWord2 n := Fin.tail w
      have hw := (g head).toFunction.hasPeriodicWeakJet.2.2 n tail i e
      let n₀ : Fin (K + 1) := ⟨n.val, Nat.lt_trans n.isLt (Nat.lt_succ_self K)⟩
      let n₁ : Fin (K + 1) := ⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩
      have hlo := upgradedTorusJet_succ u g n₀ w
      have hhi := upgradedTorusJet_succ u g n₁ (Fin.snoc w i)
      have hword : w = Fin.cons head (Fin.tail w) := by
        funext q
        refine Fin.cases ?_ ?_ q
        · simp [head]
        · intro q
          simp [Fin.tail]
      have hsnoc : Fin.snoc (α := fun _ : Fin (n + 2) => Fin 2)
          (Fin.cons head (Fin.tail w)) i =
            Fin.cons head (Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) (Fin.tail w) i) := by
        simpa using (Fin.cons_snoc_eq_snoc_cons head (Fin.tail w) i).symm
      have htail : Fin.tail (Fin.snoc (α := fun _ : Fin (n + 2) => Fin 2) w i) =
          Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) (Fin.tail w) i := by
        rw [hword, hsnoc]
        simp
      have hlo' : upgradedTorusJet u g (lowerIndex2 n.succ w) =
          (g head).toFunction.jet ⟨n₀, Fin.tail w⟩ := by
        simpa [lowerIndex2, lowerIndex, n₀, head] using hlo
      have hhi' : upgradedTorusJet u g (nextIndex2 n.succ w i) =
          (g head).toFunction.jet ⟨n₁, Fin.snoc (Fin.tail w) i⟩ := by
        simpa [nextIndex2, nextIndex, n₁, head, htail] using hhi
      change HasWeakPartialDerivOn Set.univ i
        (fun x => inner ℝ e (upgradedTorusJet u g (lowerIndex2 n.succ w) x))
        (fun x => inner ℝ e (upgradedTorusJet u g (nextIndex2 n.succ w i) x))
      rw [hlo', hhi']
      simpa [lowerIndex2, lowerIndex, nextIndex2, nextIndex] using hw
  let Y : TorusHk (K + 1) E :=
    (⟨J, hperiodic, hmem, hweak⟩ : TorusHkFunction (K + 1) E).toHk
  refine ⟨Y, ?_⟩
  apply Lp.ext
  have hY := torusJetToL2_ae J hmem (valueIndex2 (K + 1))
  have hu := periodicJetRepresentative_ae u.val (valueIndex2 1)
  filter_upwards [hY, hu] with x hYx hux
  exact hYx.trans hux

theorem exists_torusHk_succ_of_gradient_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (u : TorusHk 1 E)
    (g : Fin 2 → TorusHk K E)
    (hgrad : ∀ i, u.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
      (g i).val (valueIndex2 K)) :
    ∃ y : TorusHk (K + 1) E,
      y.val (valueIndex2 (K + 1)) = u.val (valueIndex2 1) ∧
      ∀ i, derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => i) y = g i := by
  obtain ⟨y, hy⟩ := exists_torusHk_succ_of_gradient u g hgrad
  have htr : 1 ≤ K + 1 := by omega
  let y1 := truncateTorusHk htr y
  have hidx0 : truncateJetIndex htr (valueIndex2 1) = valueIndex2 (K + 1) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hy1 : y1.val (valueIndex2 1) = u.val (valueIndex2 1) := by
    change y.val (truncateJetIndex htr (valueIndex2 1)) = _
    rw [hidx0]
    exact hy
  have hyEq : y1 = u := TorusHk.ext_value hy1
  refine ⟨y, hy, ?_⟩
  intro i
  let a : JetIndex2 1 := ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩
  have htridx : truncateJetIndex htr a =
      (⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ : JetIndex2 (K + 1)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hbase : y.val (⟨⟨1, by omega⟩, fun _ => i⟩ : JetIndex2 (K + 1)) = u.val a := by
    have h := congrArg (fun z : TorusHk 1 E => z.val a) hyEq
    change y.val (truncateJetIndex htr a) = u.val a at h
    rw [htridx] at h
    exact h
  have hpref : prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K) =
      (⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ : JetIndex2 (K + 1)) := by
    apply Sigma.ext
    · apply Fin.ext
      simp [prefixJetIndex, valueIndex2, valueIndex]
    ·
      change Fin.append (fun _ : Fin 1 => i) Fin.elim0 ≍ (fun _ : Fin 1 => i)
      have hword : Fin.append (fun _ : Fin 1 => i) Fin.elim0 =
          (fun _ : Fin 1 => i) := by
        funext j
        fin_cases j
        rfl
      rw [hword]
  have hvalue :
      (derivativeTorusHk (K := K) (r := 1) (fun _ : Fin 1 => i) y).val (valueIndex2 K) =
        (g i).val (valueIndex2 K) := by
    change y.val (prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K)) = _
    rw [hpref]
    exact hbase.trans (hgrad i)
  exact TorusHk.ext_value hvalue

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

theorem planeMultiplyIntervalCoefficient_factorialNorm_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (w : PlaneHk Set.univ K E) :
    Real.sqrt (factorialNormSq ρ (w.mulCoefficient (A t) hC
        (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA
          l.val (Nat.le_of_lt_succ l.isLt) t ht x)).val) ≤
      (coefficientSeminorm ρ K a b A).toReal *
        Real.sqrt (factorialNormSq ρ w.val) := by
  have hb := fun (l : Fin (K + 1)) (x : Vec 2) =>
    coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x
  have h := w.mulCoefficient_factorialNorm_le hC hb hρ.le
  rw [coefficientSeminorm_eq_sum_real_budget ρ hρ K a b A hA] at h
  exact h

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! One additional weak derivative from an `H¹` field and Sobolev lifts of its gradient. -/

private def upgradedPlaneJet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (u : PlaneHk Set.univ 1 E) (g : Fin 2 → PlaneHk Set.univ K E) : RawJet2 (K + 1) E :=
  fun a =>
    if hz : a.1.val = 0 then
      u.toFunction.jet (valueIndex2 1)
    else
      let n := a.1.val - 1
      let hlen : n + 1 = a.1.val := by dsimp [n]; omega
      let w : DerivativeWord2 (n + 1) := fun i => a.2 (Fin.cast hlen i)
      (g (w ⟨0, by omega⟩)).toFunction.jet
        ⟨⟨n, by have ha := a.1.isLt; dsimp [n]; omega⟩, Fin.tail w⟩

private theorem upgradedPlaneJet_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (u : PlaneHk Set.univ 1 E) (g : Fin 2 → PlaneHk Set.univ K E)
    (w : DerivativeWord2 0) :
    upgradedPlaneJet u g ⟨⟨0, by omega⟩, w⟩ = u.toFunction.jet (valueIndex2 1) := by
  simp [upgradedPlaneJet, valueIndex2, valueIndex]

private theorem upgradedPlaneJet_succ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (u : PlaneHk Set.univ 1 E) (g : Fin 2 → PlaneHk Set.univ K E)
    (n : Fin (K + 1)) (w : DerivativeWord2 (n.val + 1)) :
    upgradedPlaneJet u g ⟨n.succ, w⟩ =
      (g (w ⟨0, Nat.zero_lt_succ n.val⟩)).toFunction.jet ⟨n, Fin.tail w⟩ := by
  simp [upgradedPlaneJet]

theorem exists_planeHk_succ_of_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (u : PlaneHk Set.univ 1 E)
    (g : Fin 2 → PlaneHk Set.univ K E)
    (hgrad : ∀ i, u.toFunction.jet
      ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =ᵐ[volume.restrict Set.univ]
        (g i).toFunction.jet (valueIndex2 K)) :
    ∃ y : PlaneHk Set.univ (K + 1) E,
      y.val (valueIndex2 (K + 1)) = u.val (valueIndex2 1) := by
  classical
  let J := upgradedPlaneJet u g
  have hmem : JetMemL2On Set.univ J := by
    intro a
    change MemLp (upgradedPlaneJet u g a) 2 (volume.restrict Set.univ)
    by_cases hz : a.1.val = 0
    · simp [upgradedPlaneJet, hz]
      simpa using u.toFunction.memL2 (valueIndex2 1)
    · simp only [upgradedPlaneJet, hz, dite_false]
      let n := a.1.val - 1
      let hlen : n + 1 = a.1.val := by dsimp [n]; omega
      let w : DerivativeWord2 (n + 1) := fun i => a.2 (Fin.cast hlen i)
      exact (g (w ⟨0, by omega⟩)).toFunction.memL2 _
  have hweak : HasOrderedWeakJetOn Set.univ J := by
    intro j w i e
    cases j using Fin.cases with
    | zero =>
      have hlo := upgradedPlaneJet_zero u g w
      have hhi := upgradedPlaneJet_succ u g ⟨0, by omega⟩ (Fin.snoc w i)
      have hwU := u.toFunction.hasWeakJet ⟨0, Nat.zero_lt_succ 0⟩ Fin.elim0 i e
      have hw : HasWeakPartialDerivOn Set.univ i
          (fun x => inner ℝ e (u.toFunction.jet (valueIndex2 1) x))
          (fun x => inner ℝ e ((g i).toFunction.jet (valueIndex2 K) x)) := by
        apply hasWeakPartialDerivOn_congr_ae _ _ hwU
        · filter_upwards [] with x
          rfl
        · exact (hgrad i).fun_comp (inner ℝ e)
      have hlo' : upgradedPlaneJet u g (lowerIndex2 ⟨0, by omega⟩ w) =
          u.toFunction.jet (valueIndex2 1) := by
        simpa [lowerIndex2, lowerIndex] using hlo
      have hw0 : w = Fin.elim0 := by
        funext q
        exact Fin.elim0 q
      have hhi' : upgradedPlaneJet u g (nextIndex2 ⟨0, by omega⟩ w i) =
          (g i).toFunction.jet (valueIndex2 K) := by
        rw [hw0, Fin.snoc_zero] at hhi
        have hsnoc0 : Fin.snoc w i = (fun _ : Fin 1 => i) := by
          rw [hw0]
          exact Fin.snoc_zero _ _
        have hidx : nextIndex2 ⟨0, by omega⟩ w i =
            ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ := by
          simp only [nextIndex2, nextIndex]
          rw [hsnoc0]
        rw [hidx]
        have htail0 : Fin.tail (fun _ : Fin 1 => i) = Fin.elim0 := by
          funext q
          exact Fin.elim0 q
        have hhead0 : (fun _ : Fin 1 => i) ⟨0, by omega⟩ = i := rfl
        simpa [valueIndex2, valueIndex, htail0, hhead0, Fin.snoc, Fin.tail] using hhi
      change HasWeakPartialDerivOn Set.univ i
        (fun x => inner ℝ e (upgradedPlaneJet u g (lowerIndex2 ⟨0, by omega⟩ w) x))
        (fun x => inner ℝ e (upgradedPlaneJet u g (nextIndex2 ⟨0, by omega⟩ w i) x))
      rw [hlo', hhi']
      exact hw
    | succ n =>
      let head : Fin 2 := w ⟨0, Nat.zero_lt_succ n.val⟩
      let tail : DerivativeWord2 n := Fin.tail w
      have hw := (g head).toFunction.hasWeakJet n tail i e
      let n₀ : Fin (K + 1) := ⟨n.val, Nat.lt_trans n.isLt (Nat.lt_succ_self K)⟩
      let n₁ : Fin (K + 1) := ⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩
      have hlo := upgradedPlaneJet_succ u g n₀ w
      have hhi := upgradedPlaneJet_succ u g n₁ (Fin.snoc w i)
      have hword : w = Fin.cons head (Fin.tail w) := by
        funext q
        refine Fin.cases ?_ ?_ q
        · simp [head]
        · intro q
          simp [Fin.tail]
      have hsnoc : Fin.snoc (α := fun _ : Fin (n + 2) => Fin 2)
          (Fin.cons head (Fin.tail w)) i =
            Fin.cons head (Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) (Fin.tail w) i) := by
        simpa using (Fin.cons_snoc_eq_snoc_cons head (Fin.tail w) i).symm
      have htail : Fin.tail (Fin.snoc (α := fun _ : Fin (n + 2) => Fin 2) w i) =
          Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) (Fin.tail w) i := by
        rw [hword, hsnoc]
        simp
      have hlo' : upgradedPlaneJet u g (lowerIndex2 n.succ w) =
          (g head).toFunction.jet ⟨n₀, Fin.tail w⟩ := by
        simpa [lowerIndex2, lowerIndex, n₀, head] using hlo
      have hhi' : upgradedPlaneJet u g (nextIndex2 n.succ w i) =
          (g head).toFunction.jet ⟨n₁, Fin.snoc (Fin.tail w) i⟩ := by
        simpa [nextIndex2, nextIndex, n₁, head, htail] using hhi
      change HasWeakPartialDerivOn Set.univ i
        (fun x => inner ℝ e (upgradedPlaneJet u g (lowerIndex2 n.succ w) x))
        (fun x => inner ℝ e (upgradedPlaneJet u g (nextIndex2 n.succ w i) x))
      rw [hlo', hhi']
      simpa [lowerIndex2, lowerIndex, nextIndex2, nextIndex] using hw
  let Y : PlaneHk Set.univ (K + 1) E :=
    (⟨J, hmem, hweak⟩ : PlaneHkFunction Set.univ (K + 1) E).toHk
  refine ⟨Y, ?_⟩
  change (jetToL2 J hmem) (valueIndex2 (K + 1)) = u.val (valueIndex2 1)
  apply Lp.ext
  have hY := jetToL2_ae J hmem (valueIndex2 (K + 1))
  filter_upwards [hY] with x hYx
  simpa [Y, PlaneHkFunction.toHk, J, upgradedPlaneJet, valueIndex2, valueIndex,
    PlaneHk.toFunction, planeJetRepresentative] using hYx

theorem exists_planeHk_succ_of_gradient_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {K : ℕ} (u : PlaneHk Set.univ 1 E)
    (g : Fin 2 → PlaneHk Set.univ K E)
    (hgrad : ∀ i, u.toFunction.jet
      ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =ᵐ[volume.restrict Set.univ]
        (g i).toFunction.jet (valueIndex2 K)) :
    ∃ y : PlaneHk Set.univ (K + 1) E,
      y.val (valueIndex2 (K + 1)) = u.val (valueIndex2 1) ∧
      ∀ i, derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => i) y = g i := by
  obtain ⟨y, hy⟩ := exists_planeHk_succ_of_gradient u g hgrad
  have htr : 1 ≤ K + 1 := by omega
  let y1 := truncatePlaneHk htr y
  have hidx0 : truncateJetIndex htr (valueIndex2 1) = valueIndex2 (K + 1) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · simp [truncateJetIndex, valueIndex2, valueIndex]
  have hy1 : y1.val (valueIndex2 1) = u.val (valueIndex2 1) := by
    change y.val (truncateJetIndex htr (valueIndex2 1)) = _
    rw [hidx0]
    exact hy
  have hyEq : y1 = u := PlaneHk.ext_value isOpen_univ hy1
  refine ⟨y, hy, ?_⟩
  intro i
  let a : JetIndex2 1 := ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩
  have htridx : truncateJetIndex htr a =
      (⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ : JetIndex2 (K + 1)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hbase : y.val (⟨⟨1, by omega⟩, fun _ => i⟩ : JetIndex2 (K + 1)) =
      u.val a := by
    have h := congrArg (fun z : PlaneHk Set.univ 1 E => z.val a) hyEq
    change y.val (truncateJetIndex htr a) = u.val a at h
    rw [htridx] at h
    exact h
  have hpref : prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K) =
      (⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ : JetIndex2 (K + 1)) := by
    apply Sigma.ext
    · apply Fin.ext
      simp [prefixJetIndex, valueIndex2, valueIndex]
    ·
      change Fin.append (fun _ : Fin 1 => i) Fin.elim0 ≍ (fun _ : Fin 1 => i)
      have hword : Fin.append (fun _ : Fin 1 => i) Fin.elim0 =
          (fun _ : Fin 1 => i) := by
        funext j
        fin_cases j
        rfl
      rw [hword]
  have hvalue :
      (derivativePlaneHk (K := K) (r := 1) (fun _ : Fin 1 => i) y).val (valueIndex2 K) =
        (g i).val (valueIndex2 K) := by
    apply Lp.ext
    have hbaseAE := Lp.ext_iff.mp hbase
    filter_upwards [hbaseAE, hgrad i] with x hyx hgi
    simpa [derivativePlaneHk_apply, hpref, PlaneHk.toFunction,
      planeJetRepresentative] using hyx.trans hgi
  exact PlaneHk.ext_value isOpen_univ hvalue

/-! Arithmetic of periodic representatives, asserted almost everywhere.
The carrier arithmetic itself remains exact. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}

omit [FiniteDimensional ℝ E] in
theorem torusJet_add_ae (f g : TorusHk K E) (a : JetIndex2 K) :
    (f + g).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => f.toFunction.jet a x + g.toFunction.jet a x := by
  have he : (f + g).val a = f.val a + g.val a := rfl
  filter_upwards [torusHk_toFunction_jet_ae (f + g) a, torusHk_toFunction_jet_ae f a,
    torusHk_toFunction_jet_ae g a, Lp.coeFn_add (f.val a) (g.val a)] with x hsum hf hg ha
  rw [hsum, he, ha, hf, hg]
  rfl

omit [FiniteDimensional ℝ E] in
theorem torusJet_smul_ae (q : ℝ) (f : TorusHk K E) (a : JetIndex2 K) :
    (q • f).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => q • f.toFunction.jet a x := by
  have he : (q • f).val a = q • f.val a := rfl
  filter_upwards [torusHk_toFunction_jet_ae (q • f) a, torusHk_toFunction_jet_ae f a,
    Lp.coeFn_smul q (f.val a)] with x hsum hf ha
  rw [hsum, he, ha, hf]
  rfl

theorem torusCarrier_eq_of_value_ae (f g : TorusHk K E)
    (he : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      g.toFunction.jet (valueIndex2 K)) : f = g := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [torusHk_toFunction_jet_ae f (valueIndex2 K),
    torusHk_toFunction_jet_ae g (valueIndex2 K), he] with x hf hg hx
  exact hf.symm.trans (hx.trans hg)


omit [FiniteDimensional ℝ E] in
theorem torusJet_sum_ae {J : Type*} [Fintype J] (f : J → TorusHk K E) (a : JetIndex2 K) :
    (∑ j, f j).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ j, (f j).toFunction.jet a x := by
  have he : (∑ j, f j : TorusHk K E).val a = ∑ j, (f j).val a := by
    change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : JetIndex2 K =>
      Lp E 2 (volume.restrict AVenhance.unitCube)) a)
      ((torusHkGraph (E := E) K).toSubmodule.subtype (∑ j, f j)) = _
    rw [map_sum, map_sum]
    rfl
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j,
      (f j).toFunction.jet a x = (f j).val a x :=
    ae_all_iff.mpr (fun j => torusHk_toFunction_jet_ae (f j) a)
  filter_upwards [torusHk_toFunction_jet_ae (∑ j, f j) a,
    Lp.coeFn_fun_finsetSum Finset.univ (fun j => (f j).val a), hj] with x hx hsum hterms
  rw [hx, he, hsum]
  exact Finset.sum_congr rfl (fun j _ => (hterms j).symm)

omit [FiniteDimensional ℝ E] in
theorem torusJet_sum_ae_of_eq {J : Type*} [Fintype J]
    (f : J → TorusHk K E) (a : JetIndex2 K) (g : J → Vec 2 → E)
    (he : ∀ j, (f j).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] g j) :
    (∑ j, f j).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ j, g j x := by
  filter_upwards [torusJet_sum_ae f a, ae_all_iff.mpr he] with x hx hj
  exact hx.trans (Finset.sum_congr rfl (fun j _ => hj j))
end

/-! Uniform factorial budgets for the zeroth and first mapped regularizer inputs. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

private theorem mappedInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (Z : TorusHk k H) {R : ℝ} (hR : 0 ≤ R) (hZ : ‖Z‖ ≤ R) :
    factorialNormSq ρ (mapTorusHk C Z).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * R ^ 2 := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hs : ‖Z.val‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg Z) hR).mpr hZ
  exact (mapTorusHk_factorialNormSq_le ρ C Z).trans
    ((mul_le_mul_of_nonneg_left ((factorialNormSq_upper ρ Z.val).trans
      (mul_le_mul_of_nonneg_left hs hm)) (sq_nonneg ‖C‖)).trans_eq (mul_assoc _ _ _).symm)

theorem mappedLowerInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (V : TorusHk (k + 1) H) :
    factorialNormSq ρ (mapTorusHk C (truncateTorusHk (Nat.le_succ k) V)).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
  mappedInput_factorial_bound ρ k C _ (norm_nonneg V) (truncateTorusHk_norm_le _ V)

theorem mappedGradientInput_factorial_bound (ρ : ℝ) (k : ℕ) (C : H →L[ℝ] G)
    (V : TorusHk (k + 1) H) (q : Fin 2) :
    factorialNormSq ρ (mapTorusHk C
      (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) V)).val ≤
      ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
  mappedInput_factorial_bound ρ k C _ (norm_nonneg V) (derivativeTorusHk_norm_le _ V)
end

/-! The two constant fiber carrier constructions agree by
uniqueness of the weak jets. The bundled map is used thereafter. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem kernelMapTorusHk_eq_variational {K : ℕ} (L : E →L[ℝ] F) (u : TorusHk K E) :
    AVRegularity.CoupledEnergy.Variational.mapTorusHk L u = mapTorusHk L u := by
  apply TorusHk.ext_value
  rw [AVRegularity.CoupledEnergy.Variational.mapTorusHk_jet_eq_compLp, mapTorusHk_jet_eq_compLp]

theorem kernelMapTorusHkCLM_apply {K : ℕ} (L : E →L[ℝ] F) (u : TorusHk K E) :
    AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K L u = mapTorusHk L u := by
  rw [AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM_apply, kernelMapTorusHk_eq_variational]
end

/-! The ordered derivative and fiber maps bundle the derivative tensor as one continuous
linear map. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusKernelDerivativeTensorCLM (K r : ℕ) : TorusHk (K + r) E →L[ℝ]
    TorusHk K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  ∑ w : DerivativeWord2 r,
    (AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K (tensorEntryCLM w)).comp
      (derivativeTorusHk w)

@[simp] theorem torusKernelDerivativeTensorCLM_apply (K r : ℕ) (u : TorusHk (K + r) E) :
    torusKernelDerivativeTensorCLM K r u = torusDerivativeTensor u := by
  simp only [torusKernelDerivativeTensorCLM, sum_apply, ContinuousLinearMap.comp_apply,
    kernelMapTorusHkCLM_apply, torusDerivativeTensor, torusFamilyTensor]
end

end AVRegularity.KernelEnergy
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

def planeKernelFluxTerm {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (Y : PlaneHk Set.univ (K + (m + 1)) G) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => H)) := by
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 r :=
    congrArg DerivativeWord2 hr.symm
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  exact (mapPlaneHk L.toContinuousLinearMap
      (planeDerivativeTensor (K := K) (r := m + 1) Y)).mulCoefficient (A t) hC
      (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
        (Nat.le_of_lt_succ l.isLt) t ht x)

theorem planeKernelFluxTerm_base_ae
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (Y : PlaneHk Set.univ (K + (m + 1)) G) :
    (planeKernelFluxTerm hr ρ hρ a b A hA t ht hC Y).toFunction.jet
        (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      fun x => A t x (WithLp.toLp 2 fun word : DerivativeWord2 r =>
        Y.toFunction.jet ⟨⟨r, by omega⟩, word⟩ x) := by
  cases hr
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 (m + 1) := rfl
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 (m + 1) := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  let W := planeDerivativeTensor (K := K) (r := m + 1) Y
  have hmul := planeMulCoefficient_toFunction_value_ae
    (mapPlaneHk L.toContinuousLinearMap W) (A t) hC
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA
      l.val (Nat.le_of_lt_succ l.isLt) t ht x)
  have hmap := mapPlaneHk_toFunction_jet_ae L.toContinuousLinearMap W (valueIndex2 K)
  have htensor := planeDerivativeTensor_base_ae (K := K) (r := m + 1) Y
  unfold planeKernelFluxTerm
  filter_upwards [hmul, hmap, htensor] with x hmulx hmapx htx
  have hL : L (WithLp.toLp 2 fun w : DerivativeWord2 (m + 1) =>
      Y.toFunction.jet (prefixJetIndex w (valueIndex2 K)) x) =
      WithLp.toLp 2 (fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x) := by
    apply PiLp.ext
    intro w
    simp [L, derivativeWordArrayIsometry, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', e, prefixJetIndex, valueIndex2, valueIndex]
  calc
    ((mapPlaneHk L.toContinuousLinearMap W).mulCoefficient (A t) hC
        (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA
          l.val (Nat.le_of_lt_succ l.isLt) t ht x)).toFunction.jet (valueIndex2 K) x =
      A t x ((mapPlaneHk L.toContinuousLinearMap W).toFunction.jet
        (valueIndex2 K) x) := hmulx
    _ = A t x (L (W.toFunction.jet (valueIndex2 K) x)) :=
      congrArg (A t x) hmapx
    _ = A t x (L (WithLp.toLp 2 fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet (prefixJetIndex w (valueIndex2 K)) x)) := by
      rw [htx]
    _ = A t x (WithLp.toLp 2 (fun w : DerivativeWord2 (m + 1) =>
        Y.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x)) := congrArg (A t x) hL

theorem planeKernelFluxTerm_factorialNorm_le
    {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t))
    (Y : PlaneHk Set.univ (K + (m + 1)) G)
    (γ : ℝ) (hγ : 0 ≤ γ) (Cnorm : ℝ) (hCnorm : 0 ≤ Cnorm)
    (X : ℝ) (_hX : 0 ≤ X)
    (hY : derivFactorialNormSq (m + 1) ρ Y.val ≤ γ ^ 2 * Cnorm ^ 2 * X) :
    Real.sqrt (factorialNormSq ρ
      (planeKernelFluxTerm hr ρ hρ a b A hA t ht hC Y).val) ≤
      (coefficientSeminorm ρ K a b A).toReal * γ * Cnorm * Real.sqrt X := by
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 r :=
    congrArg DerivativeWord2 hr.symm
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := G) e
  let W := planeDerivativeTensor (K := K) (r := m + 1) Y
  have hmul := planeMultiplyIntervalCoefficient_factorialNorm_le ρ hρ K a b A hA
    t ht hC (mapPlaneHk L.toContinuousLinearMap W)
  have hmap := mapPlaneHk_factorialNormSq_le ρ L.toContinuousLinearMap W
  have hLn : ‖L.toContinuousLinearMap‖ ≤ 1 :=
    L.toLinearIsometry.norm_toContinuousLinearMap_le
  have hW : factorialNormSq ρ (mapPlaneHk L.toContinuousLinearMap W).val ≤
      factorialNormSq ρ W.val := by
    calc
      factorialNormSq ρ (mapPlaneHk L.toContinuousLinearMap W).val ≤
          ‖L.toContinuousLinearMap‖ ^ 2 * factorialNormSq ρ W.val := hmap
      _ ≤ 1 ^ 2 * factorialNormSq ρ W.val := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith [norm_nonneg L.toContinuousLinearMap]
        · exact factorialNormSq_nonneg ρ W.val
      _ = factorialNormSq ρ W.val := by ring
  have hTensor := planeDerivativeTensor_factorialNormSq ρ Y
  have hsem : 0 ≤ (coefficientSeminorm ρ K a b A).toReal := ENNReal.toReal_nonneg
  have hrootY : Real.sqrt (factorialNormSq ρ W.val) ≤ γ * Cnorm * Real.sqrt X := by
    rw [hTensor]
    calc
      Real.sqrt (derivFactorialNormSq (m + 1) ρ Y.val) ≤
          Real.sqrt (γ ^ 2 * Cnorm ^ 2 * X) := Real.sqrt_le_sqrt hY
      _ = γ * Cnorm * Real.sqrt X := by
        rw [Real.sqrt_mul (mul_nonneg (sq_nonneg γ) (sq_nonneg Cnorm)),
          Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq_eq_abs, abs_of_nonneg hγ,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hCnorm]
  calc
    Real.sqrt (factorialNormSq ρ
        (planeKernelFluxTerm hr ρ hρ a b A hA t ht hC Y).val) ≤
      (coefficientSeminorm ρ K a b A).toReal *
        Real.sqrt (factorialNormSq ρ (mapPlaneHk L.toContinuousLinearMap W).val) := hmul
    _ ≤ (coefficientSeminorm ρ K a b A).toReal * Real.sqrt (factorialNormSq ρ W.val) := by
      apply mul_le_mul_of_nonneg_left _ hsem
      exact Real.sqrt_le_sqrt hW
    _ ≤ (coefficientSeminorm ρ K a b A).toReal * (γ * Cnorm * Real.sqrt X) := by
      exact mul_le_mul_of_nonneg_left hrootY hsem
    _ = _ := by ring

end AVRegularity.KernelEnergy
end
end
