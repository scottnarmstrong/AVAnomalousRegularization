-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseSlot
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponseFlux

/-! The finite causal family of genuine second-order energy solutions `U_{i,h}`, `0 ≤ i ≤ J`,
`0 ≤ h ≤ H`, of the temporal conjugation: `L_c U_{0,0} = 0`, `U_{0,0}(t₀) = 𝖰_p(t₀) f`;
`L_c U_{i,h} = div(-𝖰_p F_p U_{i-1,h} + 𝖰_p F_E 𝖯_p U_{i,h-1})`, `U_{i,h}(t₀) = 0` for `i + h > 0`,
with `L_c = ∂_t + 𝐛·∇ - BΔ` and `U_{i,h}` of order `K_{i,h} = coarseSlot`. Each is a solution in the
class of the coupled energy estimate `coupled_energy_torus`, with one component per Hilbert fibre,
no coupling (`A = 0`) and the response flux as forcing. The class `IsCoupledWeakSolutionTorus`
contains the continuous trace and the integrated `L²`-duality identity at every time of `[t₀,t₁]`,
so causality is by uniqueness. `𝖰_p(t₀) = I` (`H_cov(t₀) = 0`), so the initial value of `U_{0,0}` is
the `L²` class of `f`; the response `f` lives in the order `N = k + (J+H+3)L` space, `f₀` is its
restriction to order `K_{0,0}`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The family `(U,Uw)` with response fluxes `G` solves the response system of the coarse family. -/
def IsCoarseResponses {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (t₀ t₁ B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H p k J L N : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ v, TorusHk N (h v))
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
    (G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (PiLp 2 (fun _ : Fin 2 => h v))) :
    Prop :=
  ∀ i, i ≤ J → ∀ j, j ≤ H →
    ∃ f₀ : ∀ v, TorusHk (coarseSlot k J H L i j) (h v),
      (if i = 0 ∧ j = 0 then
        ∀ v, (f₀ v).toFunction.jet (valueIndex2 (coarseSlot k J H L i j)) =ᵐ[volume.restrict AVenhance.unitCube]
          (f v).toFunction.jet (valueIndex2 N)
       else ∀ v, f₀ v = 0) ∧
      IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => coarseSlot k J H L i j)
        (fun _ _ _ _ _ => 0) f₀ (G i j) (fun _ _ => 0) (U i j) (Uw i j) ∧
      IsCoarseResponseFlux t₀ t₁ b D H p AD CE Hcov (coarseSlot k J H L i j) (G i j)
        (if i = 0 then fun _ _ _ => 0
          else fun v s x => (U (i - 1) j v s).toFunction.jet
            (valueIndex2 (coarseSlot k J H L (i - 1) j)) x)
        (if j = 0 then fun _ _ _ => 0
          else fun v s x => (U i (j - 1) v s).toFunction.jet
            (valueIndex2 (coarseSlot k J H L i (j - 1))) x)

end AVRegularity
