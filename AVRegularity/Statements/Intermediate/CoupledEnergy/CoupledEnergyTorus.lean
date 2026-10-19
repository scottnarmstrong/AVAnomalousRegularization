-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus
public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurCondition
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix

/-! The coupled energy estimate (Proposition 7.6 of the paper) on `Ω = 𝕋²`, in the form: a solution
exists, solutions are unique, and every solution obeys the energy bound. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- **Coupled energy estimate** (`sup_I ‖u‖²_𝓗 + ν/2 ∫_I ‖∇u‖²_𝓗 ≤ …`, stated as the bound
for every `t ∈ I`; the remaining integrals are of integrable functions by `hF`, `hg`,
`MemLp w`; the torus is the unit cell `ℝ²/ℤ²`) on `Ω = 𝕋²` (Proposition 7.6 of the paper). -/
theorem coupled_energy_torus (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (ρ : ℝ) (hρ : 0 < ρ)
    (ν : ℝ) (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ C)
    (hv_meas : Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => v p.1 p.2)
    (hv_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hv_div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hv_per : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t))
    (a B₀ lam : ℝ) (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) (Kmax : ℕ)
    (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hB : B₀ * ρ / lam ≤ 1 / 2) (hab : a * B₀ * ρ ^ 2 ≤ ν / 8)
    (D : ℕ) (hD : 2 ≤ D)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hA_meas : ∀ i i' d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => A i i' d p.1 p.2)
    (hA_smooth : ∀ i i' d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hA_per : ∀ i i' d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (A i i' d t))
    (hA_fin : ∀ i i' d, coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d) ≠ ⊤)
    (hschur : SchurCondition (schurMatrix ν ρ π K D t₀ t₁ A))
    (f : ∀ i, TorusHk (K i) (h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc t₀ t₁))) :
    (∃ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w) ∧
    (∀ (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w →
      IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u' w' →
      ∀ i, ∀ t ∈ Set.Icc t₀ t₁, u i t = u' i t) ∧
    (∀ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w →
      ∀ t ∈ Set.Icc t₀ t₁,
        massNormSq (E := h) (K := K) ρ π (fun i => (u i t).val) +
          ν / 2 * ∫ s in Set.Icc t₀ t₁,
            massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val)
        ≤ 2 * massNormSq (E := h) (K := K) ρ π (fun i => (f i).val)
          + 8 / ν * (∫ s in Set.Icc t₀ t₁,
              massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π
                (fun i => (F i s).val))
          + 10 * (∫ s in Set.Icc t₀ t₁,
              Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (g i s).val))) ^ 2) :=
  by exact AVRegularity.Providers.coupled_energy_torus t₀ t₁ ht ρ hρ ν hν v hv_bdd hv_meas hv_smooth hv_div hv_per a B₀ lam ha hB₀ hlam Kmax hjets hB hab D hD π hπ K hK A hA_meas hA_smooth hA_per hA_fin hschur f F hF g hg

end AVRegularity
