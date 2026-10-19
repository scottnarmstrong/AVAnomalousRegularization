-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.KernelEnergy.DerivFactorialNormSq

/-! The hypotheses on one spatial convolution operator `S_α(t)` of the kernel-regularized flux
on the torus (the smoothing operators of system (7.2) of the paper): a strongly measurable
spatial convolution operator with `|∇^j S_α(t) z|_{ρ,k} ≤ c_j r_α^{-j} |z|_{ρ,k}`, whose
commutation with spatial derivatives is part of the hypothesis. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `S : ℝ → (L² →L L²)` (operators on `L²(unit cell;𝗀)`) is, on `I = [t₀,t₁]`, a regularizing
family of width `r` with constants `c`:
(1) strong measurability in `t` on `I` (`t ↦ S t z` for every `z`);
(2) commutation with the first spatial derivatives: for `t ∈ I` and `z ∈ H¹` there is
`y ∈ H¹` with value `S t z` and `∂ᵢ y = S t (∂ᵢ z)` (higher orders follow by induction);
Commutation with the component maps `C_α` is not assumed: `S_α` is applied after `C_α`, which is constant.
(3) `c_j ≥ 0` for `j ≤ D - 2`;
(4) for `t ∈ I`, `j ≤ D - 2` and `z ∈ H^k` there is a (necessarily unique) `Y ∈ H^{k+j}` with
value `S t z` and `|∇^j Y|²_{ρ,k} ≤ (c_j / r^j)² |z|²_{ρ,k}`. -/
def IsSpatialRegularizerTorus {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    (ρ : ℝ) (k D : ℕ) (t₀ t₁ : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp G 2 (volume.restrict AVenhance.unitCube))) : Prop :=
  (∀ z, StronglyMeasurable fun t : Set.Icc t₀ t₁ => S t z) ∧
  (∀ t ∈ Set.Icc t₀ t₁, ∀ z : TorusHk 1 G, ∃ y : TorusHk 1 G,
    y.val (valueIndex2 1) = S t (z.val (valueIndex2 1)) ∧
    ∀ i : Fin 2, y.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
      S t (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩)) ∧
  (∀ j : ℕ, j + 2 ≤ D → 0 ≤ c j) ∧
  (∀ t ∈ Set.Icc t₀ t₁, ∀ j : ℕ, j + 2 ≤ D → ∀ z : TorusHk k G,
    ∃ Y : TorusHk (k + j) G,
      Y.val (valueIndex2 (k + j)) = S t (z.val (valueIndex2 k)) ∧
      derivFactorialNormSq j ρ Y.val ≤ (c j / r ^ j) ^ 2 * factorialNormSq ρ z.val)

end AVRegularity
