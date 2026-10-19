-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelEnergyTorus
public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionTorus
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizerTorus
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelSchurMatrix
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq

/-! The kernel-regularized coupled energy theorem at a common order `k` on `Ω = 𝕋²`
(Proposition 7.3 of the paper). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- **Kernel-regularized coupled energy theorem** on `Ω = 𝕋²` (Proposition 7.3 of the paper).
Conclusions: existence of a solution in the class `C(I;H^k) ∩ L²(I;H^{k+1})`; uniqueness;
restart at every `s ∈ I`; the forced estimate with constants `2, 8/ν, 10`; and, without
external forcing, the integrated form of `E_k' + (5/4) ν D_k ≤ 0` and the two component-supremum
bounds (stated in `[0,∞]` so that finiteness of the suprema is part of the conclusion). -/
theorem kernel_energy_torus (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (ρ : ℝ) (hρ : 0 < ρ)
    (ν : ℝ) (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ C)
    (hv_meas : Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => v p.1 p.2)
    (hv_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hv_div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ m : Fin 2, fderiv ℝ (v t) x (basisVec m) m = 0)
    (hv_per : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t))
    (a B₀ lam : ℝ) (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) (k : ℕ)
    (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ k → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hB : B₀ * ρ / lam ≤ 1 / 2) (hab : a * B₀ * ρ ^ 2 ≤ ν / 8)
    (D : ℕ) (hD : 2 ≤ D)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => B i j α d p.1 p.2)
    (hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t))
    (hB_per : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (B i j α d t))
    (hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤)
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ) (hr : ∀ i j α, 0 < r i j α)
    (hS : ∀ i j α, IsSpatialRegularizerTorus ρ k D t₀ t₁ c (r i j α) (S i j α))
    (θ : ℝ) (hθ : θ ≤ 1 / 8)
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B))
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc t₀ t₁))) :
    (∃ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y) ∧
    (∀ (u u' : ∀ i, ℝ → TorusHk k (h i))
      (w w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
      (y y' : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y →
      IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u' w' y' →
      ∀ i, ∀ t ∈ Set.Icc t₀ t₁, u i t = u' i t) ∧
    (∀ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y →
      ∀ s ∈ Set.Icc t₀ t₁,
        IsKernelWeakSolutionTorus ν s t₁ v k D B C S (fun i => u i s) F g u w y) ∧
    (∀ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y →
      ∀ t ∈ Set.Icc t₀ t₁,
        massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i t).val) +
          ν / 2 * ∫ s in Set.Icc t₀ t₁,
            massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i s).val)
        ≤ 2 * massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)
          + 8 / ν * (∫ s in Set.Icc t₀ t₁,
              massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => k) ρ π
                (fun i => (F i s).val))
          + 10 * (∫ s in Set.Icc t₀ t₁,
              Real.sqrt (massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (g i s).val))) ^ 2) ∧
    ((∀ i s, F i s = 0) → (∀ i s, g i s = 0) →
      ∀ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
        (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
        IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y →
        (∀ s ∈ Set.Icc t₀ t₁, ∀ t ∈ Set.Icc t₀ t₁, s ≤ t →
          massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i t).val) +
            5 * ν / 4 * ∫ τ in Set.Ioc s t,
              massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i τ).val)
          ≤ massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (u i s).val)) ∧
        (∑ i, ENNReal.ofReal (π i)⁻¹ *
            ⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u i t).val)
          ≤ ENNReal.ofReal
            (massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)
              + 2 * ν * θ * ∫ s in Set.Icc t₀ t₁,
                massGradNormSq (E := h) (K := fun _ => k) ρ π (fun i => (w i s).val))) ∧
        (∑ i, ENNReal.ofReal (π i)⁻¹ *
            ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
              ENNReal.ofReal (ν * ∫ s in Set.Icc t₀ t₁, gradFactorialNormSq ρ (w i s).val))
          ≤ ENNReal.ofReal
            (2 * massNormSq (E := h) (K := fun _ => k) ρ π (fun i => (f i).val)))) :=
  by exact AVRegularity.Providers.kernel_energy_torus t₀ t₁ ht ρ hρ ν hν v hv_bdd hv_meas hv_smooth hv_div hv_per a B₀ lam ha hB₀ hlam k hjets hB hab D hD π hπ B hB_meas hB_smooth hB_per hB_fin C S c r hr hS θ hθ hschur f F hF g hg

end AVRegularity
