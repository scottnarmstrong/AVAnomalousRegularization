-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CycleComparison.CovarianceMatrix
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The prescribed (constructed) centered tail presentation of the finite lift on one pulse.

Remarks on the statement:

* The relation does not conjoin `IsLiftTailPresentation`. That predicate carries the
  clause "the scalar tail ends at `2N+1`". For the constructed presentation the
  scalar cannot be moved into the flux (for `D = 2`, grade `1`, `n = 2N+2` the scalar
  is nonzero). The cutoff is the parameter
  `constructedScalarTailEnd`: `2N+1` at grade `0` and
  `2N+D` (no constraint) at positive grade; the `2N+1` cutoff is diagonal only.
* The qualitative box smoothness of `f, F` is requested only through slow order `K`
  (the order of the quantitative jets) and fast order `sZ - D`. The source fluxes spend at most
  `D - 1` fast derivatives, and the slow divergence and products spend none.
* The scalar is the tail minus the fast divergence of the raw flux. Its mean is not
  subtracted; centering is the separate conjunct, which then holds because
  `P_0 R_n = 0`.

These are definitions of the presentation, not quantitative reconstruction assumptions. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The cross-diffusion flux minus the source flux with its outer fast divergence retained.
The source flux is expanded against the preceding source grade of the full finite lift. -/
def constructedLiftTailRawFlux {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (k : Fin 2) : ∀ i, h i :=
  -Real.sqrt Q.η • ∑ j : Fin 2,
    (Q.G t X k j • fderiv ℝ (fun X' => liftApply (n - 1) (Cc hh (n - 1)) a t X' z)
        X (basisVec j) +
      fderiv ℝ (fun X' => Q.G t X' j k • liftApply (n - 1) (Cc hh (n - 1)) a t X' z)
        X (basisVec j)) -
    (if hh = 0 then 0 else
      sourceFluxCoeff Q.edge Q.η n t
        (fun ε X' z' => ∑ d ∈ Finset.range (N + 1),
          ε ^ d • liftApply d (Cc (hh - 1) d) a t X' z') k X z)

/-- The last cell degree at which the constructed scalar tail may be nonzero.
At grade `0` it is `2N+1`: the diagonal tail ends at `2N+1`.

At positive grade the scalar tail runs through `2N+D`,
which imposes no constraint; the cutoff `2N+1` is diagonal (grade `0`) only. -/
def constructedScalarTailEnd (N D hh : ℕ) : ℕ :=
  if hh = 0 then 2 * N + 1 else 2 * N + D  -- positive-grade scalar tail end

/-- The prescribed centered presentation `(f, F)` of the degree-`n`, grade-`hh` tail coefficient.

1. Positive tested orders at most `2N+D`, for the scalar and every flux component.
2. The scalar vanishes above `constructedScalarTailEnd N D hh`.
3. Both arrays are symmetric word arrays.
4. On the window, the coefficients are box smooth through slow order `K` and fast order
   `sZ - D`, and `ℤ²`-periodic in the fast variable.
5. The flux action is the raw flux minus its cell mean. This fixes the action of each flux
   on every smooth coarse field, not merely its fast divergence, so a divergence-free
   high-frequency flux cannot be added.
6. The scalar action is the tail minus the fast divergence of the raw flux.
7. The tail identity `R_n a = f a + div_z F a` (a consequence of 5–6, kept for consumers).
8. Both actions have zero cell mean.
9. Uniform-time cell-`L²` slow coefficient jets through `K` are bounded by `C Θ^hh`. -/
def IsConstructedLiftTailPresentation {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (sZ : ℕ) (π : ι → ℝ)
    (t₀ t₁ : ℝ) (N K : ℕ) (C Θ : ℝ) (hh n : ℕ)
    (f : LiftCoeff ι h) (F : Fin 2 → LiftCoeff ι h) : Prop :=
  (∀ m α t X z v u, (m = 0 ∨ 2 * N + D < m) → f m α t X z v u = 0) ∧
  (∀ k m α t X z v u, (m = 0 ∨ 2 * N + D < m) → F k m α t X z v u = 0) ∧
  (constructedScalarTailEnd N D hh < n → ∀ m α t X z v u, f m α t X z v u = 0) ∧
  (∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), f m (α ∘ σ) = f m α) ∧
  (∀ k m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), F k m (α ∘ σ) = F k m α) ∧
  (∀ m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth K (sZ - D) (fun X z => f m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => f m α t X z v u)) ∧
  (∀ k m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth K (sZ - D) (fun X z => F k m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => F k m α t X z v u)) ∧
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
    ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      (∀ k, liftApply (2 * N + D) (F k) (fun _ => a₀) t X z =
        constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k -
          fieldCellMean
            (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' k)) ∧
      liftApply (2 * N + D) f (fun _ => a₀) t X z =
        liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z -
          ∑ k : Fin 2, fastPartial k
            (fun X' z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X' z' k) X z) ∧
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
    liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z
      = liftApply (2 * N + D) f (fun _ => a₀) t X z
        + ∑ k : Fin 2, fastPartial k
            (fun X' z' => liftApply (2 * N + D) (F k) (fun _ => a₀) t X' z') X z) ∧
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
    fieldCellMean (fun z => liftApply (2 * N + D) f (fun _ => a₀) t X z) = 0 ∧
    ∀ k, fieldCellMean (fun z => liftApply (2 * N + D) (F k) (fun _ => a₀) t X z) = 0) ∧
  (∀ j, j ≤ K → ∀ m,
    schurCellL2Jet π (Set.Icc t₀ t₁) j (f m) ≤ ENNReal.ofReal (C * Θ ^ hh) ∧
    schurCellL2Jet π (Set.Icc t₀ t₁) j
      (fun p : DerivativeWord2 m × Fin 2 => F p.2 m p.1) ≤ ENNReal.ofReal (C * Θ ^ hh))

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The strong component energy
`𝓔^B_{ρ,K;π}(u) = (∑_v π_v⁻¹ (sup_I |u_v|²_{ρ,K} + B ∫_I |∇u_v|²_{ρ,K}))^{1/2}`
with each component's time supremum taken before its mass sum,
valued in `[0,∞]` (supremum and lower integral: no junk value for an unbounded or non-integrable
trajectory). It differs from `massNormSq` of the coupled energy estimate `coupled_energy_torus`
(supremum of the mass sum). `u` is the solution trajectory and `w` its order-`K+1` lift. -/

/-- `(∑_v π_v⁻¹ (⨆_{t∈I} |u_v(t)|²_{ρ,K} + B ∫⁻_I |∇ w_v|²_{ρ,K}))^{1/2}` in `[0,∞]`. -/
def strongEnergy {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ B : ℝ) (π : ι → ℝ) (t₀ t₁ : ℝ) {K : ℕ}
    (u : ∀ v, ℝ → TorusHk K (h v)) (w : ∀ v, ℝ → TorusHk (K + 1) (h v)) : ℝ≥0∞ :=
  (∑ v, ENNReal.ofReal (π v)⁻¹ *
    ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u v t).val))
      + ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁,
          ENNReal.ofReal (gradFactorialNormSq ρ (w v s).val))) ^ (1 / 2 : ℝ)

end AVRegularity
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The cell energy norm `‖c‖_𝓔 = sup_𝗍 ‖c(𝗍)‖_2 + ‖∇c‖_{L²_ul}` of a
classical field `c(t,z)` with values in a normed space `E` (the coefficients of the lift are
operator valued), over the cell-time window `I`. It is built from `cellL2Norm` and `cellUlNorm`;
`cellEnergyNorm` is the same norm for the complex jet representation of one scalar cell trajectory
and cannot take `E`-valued classical fields. The gradient is `fderiv` in `z` (operator norm of
`Vec 2 → E`, equal to the Euclidean norm up to a dimension constant absorbed by the statements). -/

/-- `⨆_{t∈I} ‖c t‖_{L²(𝕋²)} + ‖(t,z) ↦ ∇_z c‖_{L²_ul(I)}`. -/
def fieldEnergyNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ)
    (c : ℝ → Vec 2 → E) : ℝ≥0∞ :=
  (⨆ t ∈ I, cellL2Norm (c t)) + cellUlNorm I (fun t z => fderiv ℝ (c t) z)

end AVRegularity
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The strong component energy of order `m` of a field `W` stored at
a higher order `K ≥ m + 1`,
`𝓔^B_{ρ,m;π}(W) = (∑_v π_v⁻¹ (sup_I |W_v|²_{ρ,m} + B ∫_I |∇W_v|²_{ρ,m}))^{1/2}` in `[0,∞]`.
Same as `strongEnergy`
but reading both parts from the one order-`K` jet. -/

/-- `(∑_v π_v⁻¹ (⨆_{t∈I} |W_v(t)|²_{ρ,m} + B ∫⁻_I |∇W_v|²_{ρ,m}))^{1/2}` in `[0,∞]`. -/
def strongEnergyUpTo {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ B : ℝ) (π : ι → ℝ) (t₀ t₁ : ℝ) (m : ℕ) {K : ℕ}
    (W : ∀ v, ℝ → TorusHk K (h v)) : ℝ≥0∞ :=
  (∑ v, ENNReal.ofReal (π v)⁻¹ *
    ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSqUpTo ρ m (W v t).val))
      + ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁,
          ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val))) ^ (1 / 2 : ℝ)

end AVRegularity
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The cell energy jets of order `k` in the fast variable and `j` in the
slow variable of a coefficient `f(t,X,z)`,
`𝔈_{k,j}(f) = ∑_{q ≤ k} sup_X ‖D_z^q D_X^j f(·,X,·)‖_𝓔`, with the cell energy norm `𝓔` of
`fieldEnergyNorm` (the lifts have cell energy jets through fast order `k` and slow jets through
`K`). The slow derivative is taken first, then
the fast one, as in `jetSup`; the gradient inside `fieldEnergyNorm` supplies the order `q + 1`. -/

/-- `∑_{q ≤ k} ⨆_X fieldEnergyNorm I (D_z^q D_X^j f)`. -/
def cellEnergyJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (k j : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ∑ q ∈ Finset.range (k + 1), ⨆ X : Vec 2,
    fieldEnergyNorm I (fun t z =>
      iteratedFDeriv ℝ q (fun z' => iteratedFDeriv ℝ j (fun X' => f t X' z') X) z)

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The premises of the coarse proposition of one cycle:
the window `I = [t₀,t₁]`, the diffusivity `B`, the
bounded divergence-free periodic drift `𝐛` with the drift jet bounds through the order `N`; the
spatially constant symmetric flux `𝖩(t)`; the diagonal mean flux `F_A = ∑_d A_d ∇^{d-1}` and the
graded edge flux `F_E` with coefficients measurable in time, spatially `C^N` and with finite
`𝒜_{ρ,N}`; the reserves `L = D + 8p + 4`, `N = k + (J+H+3)L`; `ω = ‖H_cov‖_∞/ρ² ≤ 1`; the
supplied-mean hypotheses
`√(π_u/π_v) ∑_d 𝒜_{ρ,N}(C^{[r]}_{vu,d})/(Bρ^{d-2}) ≤ C_*^r (𝖠^r)_{vu}` with the positive (conjugated)
original edge matrix `𝖠`, both sums at most `Θ` (no smallness) and acyclic of depth `H`
(`𝖠^{H+1} = 0`). The scales `a, B₀, lam` are those of the drift jet bounds `drift_jets`; the
torus is the unit cell.

`Aedge` is the conjugated majorant masked by the edge graph
(`CycleComparison.Coarse.maskedEdgeMatrix`). For a nonnegative matrix, `Aedge ^ (H + 1) = 0` says
exactly that its support graph has depth at most `H` (`maskedEdgeMatrix_pow_eq_zero`), so
`edge_mean` is a masked entrywise (path-product) bound; masking keeps both sums below `Θ`. -/

/-- The premises of the coarse proposition of one cycle, on the torus. -/
structure IsCoarseSetting {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (t₀ t₁ ρ B a B₀ lam : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H p J k L N : ℕ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (π : ι → ℝ) (Aedge : Matrix ι ι ℝ) (Cstar Θ : ℝ) : Prop where
  window : t₀ ≤ t₁
  rho_pos : 0 < ρ
  B_pos : 0 < B
  D_ge : 2 ≤ D
  p_pos : 1 ≤ p
  L_eq : L = D + 8 * p + 4
  N_eq : N = k + (J + H + 3) * L
  mass_pos : ∀ v, 0 < π v
  drift_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖b t x‖ ≤ C
  drift_meas : Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => b q.1 q.2
  drift_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (b t)
  drift_div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0
  drift_per : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (b t)
  a_nonneg : 0 ≤ a
  B₀_ge : 1 ≤ B₀
  lam_pos : 0 < lam
  drift_jets : ∀ l : ℕ, 1 ≤ l → l ≤ N → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (b t)) l x‖ ≤
      a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B₀ * ρ / lam ≤ 1 / 2
  drift_small : a * B₀ * ρ ^ 2 ≤ B / 8
  J_symm : ∀ t i j, Jm t i j = Jm t j i
  J_meas : ∀ i j, Measurable fun t => Jm t i j
  J_bdd : matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≠ ⊤
  cov_small : matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁ ≤ ENNReal.ofReal (ρ ^ 2)
  AD_meas : ∀ d, Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => AD d q.1 q.2
  AD_smooth : ∀ d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (AD d t)
  AD_per : ∀ d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (AD d t)
  AD_fin : ∀ d, coefficientSeminorm ρ N t₀ t₁ (AD d) ≠ ⊤
  CE_meas : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => CE r v u d q.1 q.2
  CE_smooth : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (CE r v u d t)
  CE_per : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (CE r v u d t)
  CE_fin : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, coefficientSeminorm ρ N t₀ t₁ (CE r v u d) ≠ ⊤
  edge_nonneg : ∀ v u, 0 ≤ Aedge v u
  edge_row : ∀ v, ∑ u, Aedge v u ≤ Θ
  edge_col : ∀ u, ∑ v, Aedge v u ≤ Θ
  edge_acyclic : Aedge ^ (H + 1) = 0
  edge_mean : ∀ r ∈ Finset.Icc 1 H, ∀ v u,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (CE r v u d) *
        (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹
      ≤ ENNReal.ofReal (Cstar ^ r * (Aedge ^ r) v u)

end AVRegularity
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The weighted block norm `‖·‖_{𝒳;π}` of a left-coefficient array in the cell energy jet
norm. The array is indexed by a finite set `κ` (the ordered derivative words, and for fluxes also
the flux direction); the entry `(v,u)` norm is the sum over `κ` of the energy jet norms of the
operator entry `c_a(t,X,z)_{vu}` (operator norm), then `schurSums`. -/

/-- `schurSums π (v u ↦ ∑_a 𝔈_{k,j}(c_a · · · v u))`. -/
def schurEnergyJet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (k j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, cellEnergyJet I k j (fun t X z => c a t X z v u)

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! A lift sequence on a window with an arbitrary quiet entrance.

`IsLiftSequence` prescribes the zero-start lift: every positive-degree coefficient
starts from `0` at `t₀`. Terminal entry
 and the transitions of the time partition
 also use an old lift that enters a quiet gap with nonzero
coefficients and its inherited histories. `IsLiftSequenceFrom` keeps every clause of
`IsLiftSequence` except the initial state: each positive-degree coefficient solves the same
cell equations on `[t₀,t₁]` from its own trace at `t₀`. Nothing about the entrance is reset or
assumed; the entrance enters later estimates only through its actual measured jets.

`IsLiftSequence.isLiftSequenceFrom` shows that every zero-start lift sequence is one. -/

/-- `Cc` solves the lift recursion of `Q` on `[t₀,t₁]` from its own entrance trace at `t₀`. -/
def IsLiftSequenceFrom {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
    (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) : Prop :=
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
    liftApply 0 (Cc 0 0) (fun _ => a₀) t X z = a₀ X) ∧
  (∀ hh, 1 ≤ hh → hh ≤ H → ∀ m α t X z v u, Cc hh 0 m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n, N < n → ∀ m α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m, n < m → ∀ α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
    Cc hh n m (α ∘ σ) = Cc hh n m α) ∧
  (∀ hh, hh ≤ H → ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth sX sZ (fun X z => Cc hh n m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) ∧
  (∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
    ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁
      (fun z => liftApply n (Cc hh n) (fun _ => a₀) t₀ X z)
      (fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
      (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z))

/-- The value of the jet of a classical field is the field itself. -/
theorem cellValue_cellJetOfField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E) (t : ℝ) :
    cellValue (cellJetOfField ℓ c) t = fun x => ((ℓ (c t x) : ℝ) : ℂ) := by
  funext x
  simp [cellValue, cellJetOfField, valueIndex2, valueIndex]

/-- A zero-start lift sequence is a lift sequence from its own entrance trace. -/
theorem IsLiftSequence.isLiftSequenceFrom {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {D : ℕ} {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) :
    IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro hh hhH n hn1 hnN a₀ ha₀ X
  obtain ⟨hs, hl⟩ := h7 hh hhH n hn1 hnN a₀ ha₀ X
  refine ⟨hs, fun ℓ => ?_⟩
  obtain ⟨hsol, hmean, -, henergy⟩ := hl ℓ
  refine ⟨hsol, hmean, ?_, henergy⟩
  rw [cellValue_cellJetOfField]

end AVRegularity
end
end
end
