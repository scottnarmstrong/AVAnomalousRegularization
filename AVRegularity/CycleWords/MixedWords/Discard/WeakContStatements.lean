-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldProved
public import AVRegularity.CycleWords.Seam.B1NegFullField

@[expose] public noncomputable section

section
namespace AVRegularity.CycleWords.Discard

/-! # The source bound and the full-field fibre bound

`stageSourceHs' : StageSourceHsStatement` from the two forward operator statements
(`fwdSameOps`, `fwdLetterOps`), and `fullFieldFibre : FullFieldFibreStatement`. -/

universe u v

/-- The source bound for positive orders. -/
theorem stageSourceHs' : StageSourceHsStatement.{u, v} :=
  stageSourceHs_of_ops fwdSameOps fwdLetterOps

/-- The full-field bound at the fibre level. -/
theorem fullFieldFibre : FullFieldFibreStatement.{u, v} :=
  fullFieldFibre_of_sources stageSourceHs'

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleWords.Assembly
open AVRegularity.CycleWords.Seam
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # Weak continuity on rough data: the three pieces (statements)

`ChainWeakContinuityStatement` is about ARBITRARY chains of a block:
the datum has a finite moment norm and nothing else, so the letter flux of a level, a polynomial of
degree `K` in `z` times jets of the level below, need not be square integrable. The
duality step (`wordChain_letter_step_duality`) asks for an `L²(I; L²)` realization of that flux.
The weight is split instead between the flux and the test:

* (a) `WeakContFluxStatement`: for every family of level curves in `L²(I; H^{κ+1})`, the letter
  flux has an `L²(I; L²)` realization on every ball, and `⟨ϖz⟩^{-K}` times the flux is in `L²` at
  almost every time with norm at most `C ∑_u ‖w_u(r)‖_{H^{κ+1}}`. No moments.
* (b) `WeakContStepDualityStatement`: the step of the adjoint word chain for every chain, when the
  reversed chains of the test are rapidly decaying uniformly in time at the slow degree of the
  letter. The level is cut by a compact cutoff (then its source is in `L²(I; H⁻¹)` and the native
  Duhamel pairing applies) and the cutoff is removed by dominated convergence.
* (c) `WeakContLevelBoundStatement`: the level claim of the adjoint word chain
  (`wordChain_level_bound`) without its flux hypothesis. -/

universe u v

/-- **(a) The letter flux of an arbitrary level family.** For curves `w_u ∈ L²(I; H^{κ+1})`
(not necessarily a chain): on every ball the flux of the `j`-th letter has an `L²(I; L²)`
realization, and at almost every time `⟨ϖz⟩^{-K_j}` times the flux is in `L²(ℝ²)` with norm at most
`C ∑_u ‖w_u(r)‖`.

For `K_j = 0` and bounded coefficients the flux is in `L²(I; L²)`. For `w = 0` both
statements are `0 = 0`. The constant `C` is chosen after the letter and the scales, and before the
time. -/
def WeakContFluxStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ) (j : Fin N) (x : ι),
    IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H →
    (∀ u o (k : Fin ((letters j).edge x u o).length), ∀ w X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff w t X z)) →
  ∀ (ϖ ζ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 →
  ∀ (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ)
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2)),
    (∀ u, MemLp (Uw (j.castSucc, u)) 2 (volume.restrict (Set.Icc a b))) →
    (∀ M : ℕ, ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) →
          S r k z =
            wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k : Fin 2,
      eLpNorm (fun z => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ •
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k)
          2 volume ≤
        ENNReal.ofReal (C * ∑ u, ‖Uw (j.castSucc, u) r‖)

/-- **(b) The step of the adjoint word chain for every chain** (split weight). The statement of
`wordChain_letter_step_duality` with its `L²(I; L²)` realization of the letter flux replaced by
the split-weight pair: the two facts of (a) for the chain (realizations on balls; `⟨ϖz⟩^{-K_j}`
times the flux in `L²` at almost every time), and the scalar reversed chains of the test rapidly
decaying uniformly in time at the slow degree of the letter (`⟨ϖz⟩^{K_j}` times their values and
gradients bounded in `L²` over the window).

For `K_j = 0` the weight is `1` and the hypothesis is the energy bound of the reversed
chain. For a compactly supported datum see `wordChain_letter_step_duality`. For the zero chain the
identity reads `0 = 0 - 0`. -/
def WeakContStepDualityStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ}, 2 ≤ D → ∀ (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (letters : Fin N → CycleLetter ι h D) (a b : ℝ), a ≤ b →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ), IsCellMetric (fun t _ => G t) →
  ∀ (v : ℝ → Vec 2 → Vec 2), IsCellDrift v → ∀ (M : ℝ), (∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) →
  ∀ (ϖ ζ : ℝ) (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2)),
    IsPlaneChainFrom (wordChainData G letters X₀ (ζ * ϖ)) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)) →
  ∀ (j : Fin N),
    (∀ x (M : ℕ), ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) →
          S r k z =
            wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k) →
    (∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k : Fin 2,
      eLpNorm (fun z => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ •
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k)
          2 volume ≤
        ENNReal.ofReal (C * ∑ u, ‖Uw (j.castSucc, u) r‖)) →
  ∀ (B : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x)) (m d : ℕ)
    (hd : 1 ≤ d), (∀ x u (o : Finset.Icc 2 D), d < o.1 → (letters j).edge x u o = []) →
  ∀ (Φ : ∀ x, PlaneHk Set.univ (m + d) (h x))
    (ψ : ∀ x, Fin (Module.finrank ℝ (h x)) → ∀ (_ : Fin 1) (_ : Unit), ℝ →
      PlaneHk Set.univ (m + d) ℝ)
    (ψw : ∀ x, Fin (Module.finrank ℝ (h x)) → ∀ (_ : Fin 1) (_ : Unit), ℝ →
      PlaneHk Set.univ (m + d + 1) ℝ),
    (∀ x e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m + d)
      (-b) (-a) (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B x e) (Φ x))
      (fun _ _ _ => 0) (ψ x e) (ψw x e)) →
    (∀ᵐ r ∂volume.restrict (Set.Icc a b),
      LetterTermRegular (letters j) (if (letters j).positive then 1 else 0) X₀ (ζ * ϖ) r m d
        (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r)))) →
    (∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ r ∈ Set.Icc a b, ∀ x e,
      eLpNorm (fun z => polynomialMomentRoot ϖ z ^ (letters j).slow *
        (planeHkValueOperator 1 (truncatePlaneHk (le_trans hd (Nat.le_add_left d m))
          (ψ x e 0 () (-r))) : Vec 2 → ℝ) z) 2 volume ≤ ENNReal.ofReal Bd ∧
      ∀ k : Fin 2, eLpNorm (fun z => polynomialMomentRoot ϖ z ^ (letters j).slow *
        (planeH1GradientOperator (truncatePlaneHk (le_trans hd (Nat.le_add_left d m))
          (ψ x e 0 () (-r))) k : Vec 2 → ℝ) z) 2 volume ≤ ENNReal.ofReal Bd) →
    ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))
        (planeHkValueOperator (m + d) (Φ x)) =
      ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ j.succ x) (f (j.succ, x)))
          (planeHkValueOperator (m + d) (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) -
        ∫ r in a..b, ∑ u, (π u)⁻¹ * ∫ z,
          inner ℝ ((U (j.castSucc, u) r).toFunction.jet (valueIndex2 (κ j.castSucc u)) z)
            (letterTransposeJet π (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
              (fun x => (j.succ, x)) (fun u => (j.castSucc, u))
              (if (letters j).positive then 1 else 0) X₀ (ζ * ϖ) r m d
              (fun x => (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet) u
              (valueIndex2 m) z)

/-- **(c) The level claim for every chain**: `wordChain_level_bound` without the flux
realizations (and with the measurability in time of the coefficients, which the realizations on
balls use).

At level `0` the bound is the reversed-adjoint bound and Cauchy-Schwarz. For a compact datum see
`wordChain_level_bound`. The constants are those of `wordChain_level_bound`, chosen
after the orders, the reserve and the adjoint constants, and before the chain, the slots and the
test. -/
def WeakContLevelBoundStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ}, 2 ≤ D → ∀ (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ),
    (∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H) →
    (∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z) →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ), IsCellMetric (fun t _ => G t) →
  ∀ g : ℝ, 0 ≤ g → g ≤ 1 / 32 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (v : ℝ → Vec 2 → Vec 2), IsCellDrift v → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
  ∀ {η : ℝ}, 0 < η → ∀ (Cvj : ℕ → ℝ),
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j) →
  ∀ (M : ℝ), (∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) →
  ∀ (ϖ ζ : ℝ), 0 < ϖ → ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → ∀ P : ℝ, 1 ≤ P →
  ∀ (Ca : ℕ → ℕ → ℝ), (∀ k p, 0 ≤ Ca k p) → ∀ (Qa : ℕ → ℕ),
    (∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w')) →
  ∀ (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    IsPlaneChain (wordChainData G letters X₀ (ζ * ϖ)) κ a b v f (fun _ _ _ => 0) U Uw →
  ∀ (j : ℕ) (hj : j ≤ N) (m : ℕ), (∑ i ∈ Finset.range j, wordOrders letters i) + 1 ≤ m →
    m ≤ J + 1 → ∀ (p : ℕ) (t : ℝ), t ∈ Set.Icc a b →
  ∀ Φ : ∀ x, PlaneHk Set.univ m (h x), (∀ x, IsRapidPlaneHk ϖ (Φ x)) →
    ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
        (planeHkValueOperator (κ ⟨j, Nat.lt_succ_of_le hj⟩ x)
          (U ⟨j, Nat.lt_succ_of_le hj⟩ x t))
        (planeHkValueOperator m (Φ x))| ≤
      ENNReal.ofReal (levelC Ca (wordOrders letters) (wordSlows letters)
          (wordLetterConsts letters J) j m p * levelTheta (wordAmplitudes letters ζ) j *
          P ^ levelQ Qa (wordOrders letters) j m *
          (1 + (t - a)) ^ levelQ Qa (wordOrders letters) j m) *
        weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) *
        weightedJetNorm π ((p + ∑ i ∈ Finset.range j, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
          (fun x i w z => planeJetOrder (f x) i w z)

end AVRegularity.CycleWords.Discard
end
