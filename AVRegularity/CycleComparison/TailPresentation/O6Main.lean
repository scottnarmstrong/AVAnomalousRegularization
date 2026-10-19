-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.QuietDecay.Jet.Cell
public import AVRegularity.CycleComparison.Lift.TruncatedMeanCoefficientRegularity
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.Residual.TailDiff.Main
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! The statement of `cycle_lift_tail_constructed`, restated verbatim as a proposition (a standalone copy
of the statement). -/

/-- The constructed tail presentation and its slow bound (verbatim statement of
`cycle_lift_tail_constructed`). -/
def O6Statement (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
          ∃ (f : LiftCoeff ι h) (F : Fin 2 → LiftCoeff ι h),
            IsConstructedLiftTailPresentation Q Cc (max (k + 1) (L + 2)) π t₀ t₁ N K C Θ
              hh n f F

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! Schur cell jets of coefficient arrays from pointwise mixed bounds whose `(v, u)` profile is a
power of the physical edge envelope: the Schur sums then contribute `Θ ^ hh`. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The unit cell has volume one. -/
theorem volume_unitCube : volume (AVenhance.unitCube : Set (Vec 2)) = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp

/-- A cell `L²` norm is at most a pointwise bound. -/
theorem eLpNorm_unitCube_le {E : Type*} [NormedAddCommGroup E] (g : Vec 2 → E)
    (hgc : Continuous g) {C : ℝ} (hg : ∀ z, ‖g z‖ ≤ C) :
    eLpNorm g 2 (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal C := by
  refine (eLpNorm_le_of_ae_bound hgc.aestronglyMeasurable
    (Filter.Eventually.of_forall hg)).trans ?_
  rw [Measure.restrict_apply_univ, volume_unitCube]
  simp

/-- Schur sums of an array dominated by a constant times a power of the physical envelope. -/
theorem schurSums_le_of_power (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ) {Θ : ℝ}
    (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ) (hh : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (Nm : ι → ι → ℝ≥0∞)
    (hN : ∀ v u, Nm v u ≤
      ENNReal.ofReal (K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)) :
    schurSums π Nm ≤ ENNReal.ofReal (K * Θ ^ hh) := by
  have hb := physicalEdgeEnvelopeMatrix_power_schur_budget π hπ edge Θ hΘ hedge hh
  set M := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh
  have hw : ∀ v u, ENNReal.ofReal (Real.sqrt (π u / π v)) * Nm v u ≤
      ENNReal.ofReal (K * massConjugatedMatrix π M v u) := by
    intro v u
    calc ENNReal.ofReal (Real.sqrt (π u / π v)) * Nm v u
        ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) * ENNReal.ofReal (K * M v u) := by
          gcongr; exact hN v u
      _ = ENNReal.ofReal (K * massConjugatedMatrix π M v u) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          congr 1
          simp only [massConjugatedMatrix]
          ring
  have hrow : ∀ v, ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * Nm v u ≤
      ENNReal.ofReal (K * Θ ^ hh) := by
    intro v
    refine (Finset.sum_le_sum fun u _ => hw v u).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun u _ => mul_nonneg hK (hb.nonneg v u),
      ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hb.row_sum v) hK)
  have hcol : ∀ u, ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * Nm v u ≤
      ENNReal.ofReal (K * Θ ^ hh) := by
    intro u
    refine (Finset.sum_le_sum fun v _ => hw v u).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg hK (hb.nonneg v u),
      ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hb.col_sum u) hK)
  exact max_le (iSup_le hrow) (iSup_le hcol)

variable {κ : Type*} [Fintype κ]

/-- **Mixed Schur jets from pointwise power bounds.** -/
theorem schurMixedJet_le_of_power_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ) (hh : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (I : Set ℝ) {i b : ℕ} (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth i b (fun X z => c a t X z v u))
    (hbd : ∀ a v u, ∀ t ∈ I, ∀ X z,
      ‖iteratedFDeriv ℝ i (fun Y => iteratedFDeriv ℝ b (fun y => c a t Y y v u) z) X‖ ≤
        K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :
    MixedTail.schurMixedJet π I i δ c ≤
      ENNReal.ofReal (2 ^ i * (Fintype.card κ * K) * Θ ^ hh) := by
  refine (QuietDecay.Partition.schurMixedJet_le_schurMixedCellL2Jet π I δ c hc).trans ?_
  have hpt : ∀ a v u, ∀ t ∈ I, ∀ X, QuietDecay.ptJet (fun X z => c a t X z v u) X i b ≤
      ENNReal.ofReal (K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
    intro a v u t ht X
    exact eLpNorm_unitCube_le _ (((hc a v u t ht).2.2 i b le_rfl le_rfl).comp
      (Continuous.prodMk continuous_const continuous_id)).norm fun z => by
        simpa using hbd a v u t ht X z
  have hsc := QuietDecay.schurMixedCellL2Jet_le_of_ptJet_le π I c hc hpt
  refine (mul_le_mul_right hsc _).trans ?_
  have hs := schurSums_le_of_power π hπ edge hΘ hedge hh (K := Fintype.card κ * K)
    (by positivity) (fun v u => ∑ _a : κ,
      ENNReal.ofReal (K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (fun v u => by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact le_of_eq (congrArg ENNReal.ofReal (by ring)))
  calc (2 : ℝ≥0∞) ^ i * schurSums π (fun v u => ∑ _a : κ,
        ENNReal.ofReal (K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
      ≤ 2 ^ i * ENNReal.ofReal (Fintype.card κ * K * Θ ^ hh) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- **Slow Schur jets from pointwise power bounds.** -/
theorem schurCellL2Jet_le_of_power_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ) (hh : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (I : Set ℝ) (j : ℕ) (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hcont : ∀ a v u, ∀ t ∈ I, ∀ X,
      Continuous (fun z => iteratedFDeriv ℝ j (fun Y => c a t Y z v u) X))
    (hbd : ∀ a v u, ∀ t ∈ I, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => c a t Y z v u) X‖ ≤
        K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :
    schurCellL2Jet π I j c ≤ ENNReal.ofReal (Fintype.card κ * K * Θ ^ hh) := by
  refine schurSums_le_of_power π hπ edge hΘ hedge hh (by positivity) _ fun v u => ?_
  have hM : ∀ a, cellL2Jet I j (fun t X z => c a t X z v u) ≤
      ENNReal.ofReal (K * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
    intro a
    refine iSup₂_le fun t ht => iSup_le fun X => ?_
    exact eLpNorm_unitCube_le _ (hcont a v u t ht X) fun z => hbd a v u t ht X z
  refine (Finset.sum_le_sum fun a _ => hM a).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! The interface between the construction of the centered tail arrays and their consumers
(`cycle_lift_tail_constructed` and `cycle_residual_differentiated`).

`ArraysStatement` asserts that, for every lift setting and lift sequence, the constructed arrays
`(f, F)` of every grade `hh ≤ H` and tail degree `N+1 ≤ n ≤ 2N+D` exist with these properties:
* they are symmetric word arrays supported in orders `1, …, 2N+D`;
* the scalar vanishes above `constructedScalarTailEnd`;
* they have the prescribed actions (the raw flux minus its cell mean; the tail minus the fast
  divergence of the raw flux);
* on the window they are periodic and box smooth through slow order `K` and fast order
  `max k (L+2) + D - 1`;
* their mixed slow/fast derivatives are bounded pointwise by `Cm` times the `hh`-th power of the
  physical edge envelope. -/

/-- The fast order of the constructed arrays. -/
def arrayFastOrder (k L D : ℕ) : ℕ := max k (L + 2) + D - 1

/-- The constructed centered tail arrays and their pointwise entry bounds. -/
def ArraysStatement (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  ∃ Cm : ℝ, 0 ≤ Cm ∧
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
      (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
      (b : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
    ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
      IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      ∀ hh, hh ≤ H → ∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
        ∃ (fc : LiftCoeff ι h) (Fc : Fin 2 → LiftCoeff ι h),
          (∀ m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), fc m (β ∘ σ) = fc m β) ∧
          (∀ k m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), Fc k m (β ∘ σ) = Fc k m β) ∧
          (∀ m α t X z v u, (m = 0 ∨ 2 * N + D < m) → fc m α t X z v u = 0) ∧
          (∀ k m α t X z v u, (m = 0 ∨ 2 * N + D < m) → Fc k m α t X z v u = 0) ∧
          (constructedScalarTailEnd N D hh < n → ∀ m α t X z v u, fc m α t X z v u = 0) ∧
          (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
            (∀ k, liftApply (2 * N + D) (Fc k) (fun _ => a₀) t X z =
              constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k -
                fieldCellMean
                  (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' k)) ∧
            liftApply (2 * N + D) fc (fun _ => a₀) t X z =
              liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z -
                ∑ k : Fin 2, fastPartial k
                  (fun X' z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X' z' k)
                  X z) ∧
          (∀ t ∈ Set.Icc t₀ t₁, ∀ m α v u,
            IsBoxSmooth K (arrayFastOrder k L D) (fun X z => fc m α t X z v u) ∧
            (∀ X, AVenhance.IsZ2Periodic (fun z => fc m α t X z v u)) ∧
            ∀ k', IsBoxSmooth K (arrayFastOrder k L D) (fun X z => Fc k' m α t X z v u) ∧
              ∀ X, AVenhance.IsZ2Periodic (fun z => Fc k' m α t X z v u)) ∧
          (∀ t ∈ Set.Icc t₀ t₁, ∀ m α v u, ∀ r ≤ K, ∀ s ≤ arrayFastOrder k L D, ∀ X z,
            ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
                (fun y => fc m α t Y y v u) z) X‖ ≤
              Cm * finiteMatrixPower (physicalEdgeEnvelopeMatrix π b) hh v u ∧
            ∀ k', ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
                (fun y => Fc k' m α t Y y v u) z) X‖ ≤
              Cm * finiteMatrixPower (physicalEdgeEnvelopeMatrix π b) hh v u)

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! The statement of `Providers.cycle_residual_differentiated`, restated verbatim as
`D1Statement`. -/

/-- The statement for the constructed tail presentation, for each word of length at most `r`. -/
def D1Statement (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CL : ℝ) : Prop :=
  1 ≤ Acl →
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ) (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N (s0 + r) (kl + r) (Ll + r) qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + r + D + 2) (max (kl + r + 1) (Ll + r + 2)) t₀ t₁ N H Cc →
        ∀ (f : ℕ → LiftCoeff ι h) (F : ℕ → Fin 2 → LiftCoeff ι h) (hh : ℕ), hh ≤ H →
          (∀ n, N + 1 ≤ n → n ≤ 2 * N + D →
            IsConstructedLiftTailPresentation Q Cc (max (kl + r + 1) (Ll + r + 2)) π t₀ t₁ N (s0 + r)
              CL Θ hh n (f n) (F n)) →
        ∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          (∀ j, j ≤ kres + r + 1 → ∀ (w : DerivativeWord2 j) (v : ι), Measurable
            (fun p : ℝ × Vec 2 => ‖orderedDerivative w (fun x => a p.1 x v) p.2‖ₑ)) →
        ∀ Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain (s0 + r) (max (kl + r + 1) (Ll + r + 2)) Acl (tailScalarField f N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ)
              (tailFluxField F N D εc (fun s X => a (ℓ ^ 2 * s) (ρ • X)) τ) (fun j => Vc j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          ∀ (j : ℕ), j ≤ r → ∀ β : DerivativeWord2 j,
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => rs ^ j • orderedDerivative β
                (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl Vc t x' k) x)
              (fun t x => rs ^ j • orderedDerivative β
                (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl Vc t x') x)
            ≤ ENNReal.ofReal (C * Θ ^ hh * εc ^ N * (1 + Z)) *
              classicalStrongEnergy ρ B π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) a

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! Field-level consequences of the prescribed actions of the constructed tail arrays: the tail
identity and the vanishing cell means; regularity of lift actions in the fast variable; and slow
Schur jets of arrays with power-profile bounds. -/

section Fields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tail identity from the two prescribed actions. -/
theorem tail_identity_of_actions (Φ FA : Fin 2 → Vec 2 → Vec 2 → E) (fA T : Vec 2 → Vec 2 → E)
    (hF : ∀ k X z, FA k X z = Φ k X z - fieldCellMean (Φ k X))
    (hf : ∀ X z, fA X z = T X z - ∑ k : Fin 2, fastPartial k (Φ k) X z) (X z : Vec 2) :
    T X z = fA X z + ∑ k : Fin 2, fastPartial k (FA k) X z := by
  have hp : ∀ k, fastPartial k (FA k) X z = fastPartial k (Φ k) X z := by
    intro k
    have hfun : (fun z' => FA k X z') = fun z' => Φ k X z' - fieldCellMean (Φ k X) :=
      funext fun z' => hF k X z'
    simp only [fastPartial]
    rw [hfun, fderiv_sub_const]
  rw [hf X z, Finset.sum_congr rfl fun k _ => hp k]
  abel

/-- The vanishing cell means from the two prescribed actions. -/
theorem mean_zero_of_actions [FiniteDimensional ℝ E] [CompleteSpace E]
    (Φ FA : Fin 2 → Vec 2 → Vec 2 → E) (fA T : Vec 2 → Vec 2 → E)
    (hF : ∀ k X z, FA k X z = Φ k X z - fieldCellMean (Φ k X))
    (hf : ∀ X z, fA X z = T X z - ∑ k : Fin 2, fastPartial k (Φ k) X z)
    (hF1 : ∀ k X, ContDiff ℝ 1 (FA k X)) (hFper : ∀ k X, AVenhance.IsZ2Periodic (FA k X))
    (hfc : ∀ X, Continuous (fA X)) (hT : ∀ X, fieldCellMean (T X) = 0) (X : Vec 2) :
    fieldCellMean (fA X) = 0 ∧ ∀ k, fieldCellMean (FA k X) = 0 := by
  have hΦ : ∀ k, Φ k X = fun z => FA k X z + fieldCellMean (Φ k X) := fun k =>
    funext fun z => by rw [hF k X z]; abel
  have hΦc : ∀ k, Continuous (Φ k X) := fun k => by
    rw [hΦ k]; exact (hF1 k X).continuous.add continuous_const
  have hpart : ∀ k, Continuous (fun z => fastPartial k (FA k) X z) := fun k =>
    ((hF1 k X).continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine ⟨?_, fun k => ?_⟩
  · have hTX : T X = fun z => fA X z + ∑ k : Fin 2, fastPartial k (FA k) X z :=
      funext fun z => tail_identity_of_actions Φ FA fA T hF hf X z
    have hfA : fA X = fun z => T X z - ∑ k : Fin 2, fastPartial k (FA k) X z := by
      funext z; rw [hTX]; simp
    have hTc : Continuous (T X) := by
      rw [hTX]; exact (hfc X).add (continuous_finsetSum _ fun k _ => hpart k)
    rw [hfA, fieldCellMean_sub hTc (continuous_finsetSum _ fun k _ => hpart k), hT X,
      fieldCellMean_sum _ fun k _ => hpart k]
    have h0 : ∀ k : Fin 2, fieldCellMean (fun z => fastPartial k (FA k) X z) = 0 := fun k =>
      fieldCellMean_fastPartial_eq_zero (FA k X) (hF1 k X) (hFper k X) k
    simp [h0]
  · have hfun : FA k X = fun z => Φ k X z - fieldCellMean (Φ k X) := funext fun z => hF k X z
    rw [hfun, fieldCellMean_sub (hΦc k) continuous_const, fieldCellMean_const, sub_self]

/-- The slow jets of a box-smooth field, as functions of the fast variable, are continuous. -/
theorem continuous_slowJet_of_box {p q j : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth p q f)
    (hj : j ≤ p) (X : Vec 2) :
    Continuous (fun z => iteratedFDeriv ℝ j (fun Y => f Y z) X) := by
  have he : ∀ z, (fun Y => f Y z) =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E) ∘ fun Y => iteratedFDeriv ℝ 0 (f Y) z := by
    intro z
    funext Y
    simp [iteratedFDeriv_zero_eq_comp]
  have hc : Continuous (fun z => iteratedFDeriv ℝ j
      (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X) :=
    (hf.2.2 j 0 hj (Nat.zero_le _)).comp (Continuous.prodMk continuous_const continuous_id)
  have : (fun z => iteratedFDeriv ℝ j (fun Y => f Y z) X) = fun z =>
      ((continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv :
        _ →L[ℝ] E).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X) := by
    funext z
    rw [he z]
    exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv.iteratedFDeriv_comp_left
  rw [this]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _ _).continuous.comp hc

end Fields

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- A lift action is as smooth in the fast variable as its coefficients. -/
theorem contDiff_liftApply_fast {q : WithTop ℕ∞} (n : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2)
    (hc : ∀ m α v u, ContDiff ℝ q (fun z => c m α t X z v u)) :
    ContDiff ℝ q (fun z => liftApply n c a t X z) := by
  refine contDiff_pi.2 fun v => ?_
  simp only [liftApply]
  exact ContDiff.sum fun m _ => ContDiff.sum fun α _ => ContDiff.sum fun u _ =>
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a t) X u)).contDiff.comp (hc m α v u)

/-- A lift action is periodic in the fast variable when its coefficients are. -/
theorem periodic_liftApply_fast (n : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X : Vec 2) (hc : ∀ m α v u, AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) :
    AVenhance.IsZ2Periodic (fun z => liftApply n c a t X z) := by
  intro l z
  funext v
  simp only [liftApply]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  rw [show c m α t X (z + AVenhance.latticeShift l) v u = c m α t X z v u from hc m α v u l z]

end Lift

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! The diagonal scalar tail ends at `2N+1`: at grade `0` and degree
`n ≥ 2N+2`, the tail minus the fast divergence of the raw flux vanishes. Every lift of degree
`n - 1, n - 2 > N` is zero, and the diagonal means of degree `≥ N + 2` vanish because the lifts are
centered (`liftMean_diagonal_above_cutoff`). -/

section
section Field

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- A lift action at a time where the field vanishes is zero. -/
theorem liftApply_field_zero (n : ℕ) (c : LiftCoeff ι h) (g : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hg : ∀ X, g t X = 0) (X z : Vec 2) : liftApply n c g t X z = 0 := by
  have hgt : g t = fun _ => 0 := funext hg
  funext v
  simp [liftApply, hgt, orderedDerivative_const_zero]

end Field

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The diagonal scalar tail ends at `2N + 1`.** -/
theorem diagonal_tail_sub_rawFlux_div_zero
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : 2 * N + 2 ≤ n) (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftTailCoeff Q Cc N (fun _ => a₀) 0 n t X z -
      ∑ k : Fin 2, fastPartial k
        (fun X' z' => constructedLiftTailRawFlux Q Cc N 0 n (fun _ => a₀) t X' z' k) X z = 0 := by
  have hN := P.N_ge
  have h1 := Lift.liftApply_above_cutoff Q sX sZ a b N H Cc hseq 0 (Nat.zero_le _) (n - 1)
    (by omega) (fun _ => a₀)
  have h2 := Lift.liftApply_above_cutoff Q sX sZ a b N H Cc hseq 0 (Nat.zero_le _) (n - 2)
    (by omega) (fun _ => a₀)
  have hraw : ∀ X' z' k,
      constructedLiftTailRawFlux Q Cc N 0 n (fun _ => a₀) t X' z' k = 0 := by
    intro X' z' k
    simp [constructedLiftTailRawFlux, h1]
  have hdiv : ∀ k : Fin 2, fastPartial k
      (fun X' z' => constructedLiftTailRawFlux Q Cc N 0 n (fun _ => a₀) t X' z' k) X z = 0 := by
    intro k
    simp [fastPartial, hraw]
  have hA : liftA Q Cc (fun _ => a₀) 0 n t X z = 0 := by
    simp [liftA, h1, h2, cellB1, cellB2, slowPartial, fastPartial]
  have hM : ∀ r ∈ Finset.range (N + 1),
      (if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
          liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => a₀) p.2 (n - r)) t X z
      else 0) = 0 := by
    intro r hr
    have hrN : r ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    split_ifs
    · refine Finset.sum_eq_zero fun p hp => ?_
      have hp2 : p.2 = 0 := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
      rw [hp2]
      exact liftApply_field_zero r (Cc p.1 r) _ t (fun X' =>
        Lift.liftMean_diagonal_above_cutoff P sX sZ hX hZ Cc hseq a₀ ha₀ (n - r) (by omega)
          t ht X') X z
    · rfl
  simp only [liftTailCoeff, hA, Finset.sum_eq_zero hM, hdiv, Finset.sum_const_zero, sub_zero]
end

/-! The constructed presentation is unique on the window: two symmetric arrays supported in
orders at most `2N + D` with the same actions on smooth fields agree entrywise. Hence any
presentation satisfying `IsConstructedLiftTailPresentation` equals the constructed arrays on the
window, and its cell jets are those of the constructed arrays. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- Symmetric arrays supported in orders `≤ n` with equal actions agree entrywise. -/
theorem coeff_eq_of_actions (n : ℕ) (c d : LiftCoeff ι h)
    (hc : ∀ m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hd : ∀ m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), d m (β ∘ σ) = d m β)
    (hc0 : ∀ m α t X z v u, n < m → c m α t X z v u = 0)
    (hd0 : ∀ m α t X z v u, n < m → d m α t X z v u = 0)
    (t : ℝ) (X z : Vec 2) (v : ι)
    (he : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      liftApply n c (fun _ => a₀) t X z v = liftApply n d (fun _ => a₀) t X z v)
    (m : ℕ) (α : DerivativeWord2 m) (u : ι) : c m α t X z v u = d m α t X z v u := by
  by_cases hm : m ≤ n
  · exact Lift.symmetric_lift_coefficient_eq_of_operator_eq n m hm c d (hc m) (hd m) t X z v u
      he α
  · rw [hc0 m α t X z v u (by omega), hd0 m α t X z v u (by omega)]

/-- **Identification of a constructed presentation.** Any presentation satisfying the relation
equals, on the window, symmetric arrays supported in orders `≤ 2N + D` with the prescribed
actions. -/
theorem presentation_eq {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (sZ : ℕ) (π : ι → ℝ) (t₀ t₁ : ℝ) (N K : ℕ) (C Θ : ℝ) (hh n : ℕ)
    (f : LiftCoeff ι h) (F : Fin 2 → LiftCoeff ι h)
    (hP : IsConstructedLiftTailPresentation Q Cc sZ π t₀ t₁ N K C Θ hh n f F)
    (fc : LiftCoeff ι h) (Fc : Fin 2 → LiftCoeff ι h)
    (hfc : ∀ m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), fc m (β ∘ σ) = fc m β)
    (hFc : ∀ k m (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), Fc k m (β ∘ σ) = Fc k m β)
    (hfc0 : ∀ m α t X z v u, 2 * N + D < m → fc m α t X z v u = 0)
    (hFc0 : ∀ k m α t X z v u, 2 * N + D < m → Fc k m α t X z v u = 0)
    (hFa : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z k,
      liftApply (2 * N + D) (Fc k) (fun _ => a₀) t X z =
        constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k -
          fieldCellMean
            (fun z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z' k))
    (hfa : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      liftApply (2 * N + D) fc (fun _ => a₀) t X z =
        liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z -
          ∑ k : Fin 2, fastPartial k
            (fun X' z' => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X' z' k) X z) :
    (∀ t ∈ Set.Icc t₀ t₁, ∀ m α X z v u, f m α t X z v u = fc m α t X z v u) ∧
      ∀ t ∈ Set.Icc t₀ t₁, ∀ k m α X z v u, F k m α t X z v u = Fc k m α t X z v u := by
  obtain ⟨c1, c2, -, c4, c5, -, -, c8, -, -, -⟩ := hP
  refine ⟨fun t ht m α X z v u => ?_, fun t ht k m α X z v u => ?_⟩
  · refine coeff_eq_of_actions (2 * N + D) f fc c4 hfc
      (fun m α t X z v u hm => c1 m α t X z v u (Or.inr hm)) hfc0 t X z v
      (fun a₀ ha₀ => ?_) m α u
    rw [(c8 a₀ ha₀ t ht X z).2, hfa a₀ ha₀ t ht X z]
  · refine coeff_eq_of_actions (2 * N + D) (F k) (Fc k) (c5 k) (hFc k)
      (fun m α t X z v u hm => c2 k m α t X z v u (Or.inr hm)) (hFc0 k) t X z v
      (fun a₀ ha₀ => ?_) m α u
    rw [(c8 a₀ ha₀ t ht X z).1 k, hFa a₀ ha₀ t ht X z k]

omit [Fintype ι] [DecidableEq ι] in
/-- Mixed cell jets only see the window. -/
theorem mixedCellJet_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ}
    {i b : ℕ} (δ : DerivativeWord2 b) {f g : ℝ → Vec 2 → Vec 2 → E}
    (hfg : ∀ t ∈ I, ∀ X z, f t X z = g t X z) :
    MixedTail.mixedCellJet I i δ f = MixedTail.mixedCellJet I i δ g := by
  unfold MixedTail.mixedCellJet
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  have : f t = g t := funext fun X => funext fun z => hfg t ht X z
  rw [this]

omit [DecidableEq ι] in
/-- Schur mixed jets only see the window. -/
theorem schurMixedJet_congr (π : ι → ℝ) {κ : Type*} [Fintype κ] {I : Set ℝ} {i b : ℕ}
    (δ : DerivativeWord2 b) {c d : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v}
    (hcd : ∀ a, ∀ t ∈ I, ∀ X z v u, c a t X z v u = d a t X z v u) :
    MixedTail.schurMixedJet π I i δ c = MixedTail.schurMixedJet π I i δ d := by
  unfold MixedTail.schurMixedJet
  congr 1
  funext v u
  exact Finset.sum_congr rfl fun a _ =>
    mixedCellJet_congr δ fun t ht X z => hcd a t ht X z v u
end

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! D1 (`cycle_residual_differentiated`) from the constructed tail arrays and the conditional
differentiated residual estimate.

Any presentation satisfying `IsConstructedLiftTailPresentation` equals the constructed arrays on
the window (`presentation_eq`). Their pointwise mixed bounds give mixed Schur jets
`≤ Cs Θ^hh` (`schurMixedJet_le_of_power_bound`), which is the input of `TailDiff.Statement`. -/

section
/-- The Schur constant of the mixed jets: `2^(slow order) · (2 · 2^(2N+D)) · Cm`. -/
def mixedSchurConst (Acl N D r : ℕ) (Cm : ℝ) : ℝ :=
  2 ^ (Acl + 2 + r) * ((2 * 2 ^ (2 * N + D) : ℝ) * Cm)

theorem mixedSchurConst_nonneg (Acl N D r : ℕ) {Cm : ℝ} (hCm : 0 ≤ Cm) :
    0 ≤ mixedSchurConst Acl N D r Cm := by
  unfold mixedSchurConst; positivity

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- Mixed Schur jets of an array family with entries bounded by a power profile, and vanishing
above order `2N + D`, are at most `mixedSchurConst · Θ^hh`. -/
theorem schurMixedJet_le_mixedSchurConst (Acl N D r : ℕ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (edge : ι → ι → ℝ) {Θ : ℝ} (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ) (hh : ℕ)
    {Cm : ℝ} (hCm : 0 ≤ Cm) (I : Set ℝ) {m : ℕ} {κ : Type*} [Fintype κ]
    (hκ : (Fintype.card κ : ℝ) ≤ 2 * 2 ^ (2 * N + D) ∨ 2 * N + D < m)
    {i b : ℕ} (hi : i ≤ Acl + 2 + r) (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth i b (fun X z => c a t X z v u))
    (hbd : ∀ a v u, ∀ t ∈ I, ∀ X z,
      ‖iteratedFDeriv ℝ i (fun Y => iteratedFDeriv ℝ b (fun y => c a t Y y v u) z) X‖ ≤
        Cm * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)
    (hzero : 2 * N + D < m → ∀ a t X z v u, c a t X z v u = 0) :
    MixedTail.schurMixedJet π I i δ c ≤
      ENNReal.ofReal (mixedSchurConst Acl N D r Cm * Θ ^ hh) := by
  have hM0 : ∀ v u, 0 ≤ finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u :=
    finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge hedge.nonneg) hh
  have hi2 : (2 : ℝ) ^ i ≤ 2 ^ (Acl + 2 + r) := pow_le_pow_right₀ (by norm_num) hi
  rcases hκ with hκ | hm
  · refine (schurMixedJet_le_of_power_bound π hπ edge hΘ hedge hh hCm I δ c hc hbd).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    unfold mixedSchurConst
    have hΘh : 0 ≤ Θ ^ hh := pow_nonneg hΘ hh
    have h1 : (Fintype.card κ : ℝ) * Cm ≤ (2 * 2 ^ (2 * N + D)) * Cm :=
      mul_le_mul_of_nonneg_right hκ hCm
    have h2 : (2 : ℝ) ^ i * ((Fintype.card κ : ℝ) * Cm) ≤
        2 ^ (Acl + 2 + r) * ((2 * 2 ^ (2 * N + D)) * Cm) :=
      mul_le_mul hi2 h1 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h2 hΘh
  · have hz := schurMixedJet_le_of_power_bound π hπ edge hΘ hedge hh (K := 0) le_rfl I δ c hc
      (fun a v u t ht X z => by
        have : (fun Y => iteratedFDeriv ℝ b (fun y => c a t Y y v u) z) = fun _ => 0 := by
          funext Y
          have hY : (fun y => c a t Y y v u) = fun _ => 0 :=
            funext fun y => hzero hm a t Y y v u
          rw [hY]
          simp
        rw [this]
        simp)
    refine hz.trans ?_
    simp only [mul_zero, zero_mul, ENNReal.ofReal_zero]
    exact bot_le

end
end

/-! D1 from `ArraysStatement` (at the raised orders `K = Acl+2+r`, `k = kl+r`, `L = Ll+r`) and the
conditional differentiated residual estimate `TailDiff.Statement`. -/

section
universe u v

theorem card_words_le (N D m : ℕ) (hm : m ≤ 2 * N + D) :
    (Fintype.card (DerivativeWord2 m) : ℝ) ≤ 2 * 2 ^ (2 * N + D) := by
  have hc : (Fintype.card (DerivativeWord2 m) : ℝ) = 2 ^ m := by simp
  rw [hc]
  calc (2 : ℝ) ^ m ≤ 2 ^ (2 * N + D) := pow_le_pow_right₀ (by norm_num) hm
    _ ≤ 2 * 2 ^ (2 * N + D) := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) (2 * N + D)]

theorem card_flux_words_le (N D m : ℕ) (hm : m ≤ 2 * N + D) :
    (Fintype.card (DerivativeWord2 m × Fin 2) : ℝ) ≤ 2 * 2 ^ (2 * N + D) := by
  have hc : (Fintype.card (DerivativeWord2 m × Fin 2) : ℝ) = 2 ^ m * 2 := by simp
  rw [hc]
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  linarith

/-- **D1 from the constructed arrays and the conditional estimate.** -/
theorem d1_of_arrays (Acl N D H kl Ll : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CL : ℝ)
    (harr : ∀ r, ArraysStatement.{u, v} N (Acl + 2 + r) (kl + r) (Ll + r) D H CG Cw Cj)
    (htd : ∀ r, 1 ≤ Acl → TailDiff.Statement.{u, v} Acl N D r) :
    D1Statement.{u, v} Acl N D H kl Ll CG Cw Cj CL := by
  intro hA r
  obtain ⟨Cm, hCm, harr'⟩ := harr r
  obtain ⟨K₀, hK₀, htd'⟩ := htd r hA
  refine ⟨K₀ * mixedSchurConst Acl N D r Cm,
    mul_nonneg hK₀ (mixedSchurConst_nonneg Acl N D r hCm), ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ rs E ℓ dstar εc lam hrs hrse heρ par V qs qf b Θ kres s0
    hkres hs0 hset hM Cc hseq f F hh hhH hpres a ha _hper hmeas Vc hVc Z hZ j hj β
  subst hs0
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · simp [residualNorm, Finset.univ_eq_empty]
  have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
    (hset.envelope.row_sum v₀)
  have hedge : HasRealSchurBudget b Θ :=
    ⟨hset.envelope.nonneg, hset.envelope.row_sum, hset.envelope.col_sum⟩
  have hεc_eq : εc = ℓ * Real.sqrt B / ρ := by rw [hset.εc_eq, hset.dstar_eq]
  have hfast : r + 1 ≤ arrayFastOrder (kl + r) (Ll + r) D := by
    unfold arrayFastOrder; omega
  have harrn := fun n (h1 : N + 1 ≤ n) (h2 : n ≤ 2 * N + D) =>
    harr' Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq hh hhH n h1 h2
  have hS0 : 0 ≤ mixedSchurConst Acl N D r Cm * Θ ^ hh :=
    mul_nonneg (mixedSchurConst_nonneg Acl N D r hCm) (pow_nonneg hΘ hh)
  have key := htd' π t₀ t₁ e ν B ρ rs ℓ εc (mixedSchurConst Acl N D r Cm * Θ ^ hh)
    (max (kl + r + 1) (Ll + r + 2)) kres hset.mass_pos hset.window hset.e_pos hset.ν_pos
    hset.B_pos hset.ρ_pos hrs hrse heρ hM hset.ℓ_eq hεc_eq hset.εc_le hS0 (by omega) hkres f F
    (fun n h1 h2 τ hτ => by
      obtain ⟨fc, Fc, hfp, hFp, hf0, hF0, -, hact, hboxp, -⟩ := harrn n h1 h2
      obtain ⟨hidf, hidF⟩ := presentation_eq Q Cc _ π t₀ t₁ N _ CL Θ hh n (f n) (F n)
        (hpres n h1 h2) fc Fc hfp hFp
        (fun m α t X z v u hm => hf0 m α t X z v u (Or.inr hm))
        (fun k m α t X z v u hm => hF0 k m α t X z v u (Or.inr hm))
        (fun a₀ ha₀ t ht X z k => (hact a₀ ha₀ t ht X z).1 k)
        (fun a₀ ha₀ t ht X z => (hact a₀ ha₀ t ht X z).2)
      obtain ⟨-, -, -, -, -, c6, c7, -, -, -, -⟩ := hpres n h1 h2
      refine ⟨fun m α v u => ?_, fun k m α v u => ?_, fun m α v u X => (c6 m α v u τ hτ).2 X,
        fun k m α v u X => (c7 k m α v u τ hτ).2 X⟩
      · have hfun : (fun X y => f n m α τ X y v u) = fun X y => fc m α τ X y v u :=
          funext fun X => funext fun y => hidf τ hτ m α X y v u
        rw [hfun]
        exact (hboxp τ hτ m α v u).1.mono le_rfl hfast
      · have hfun : (fun X y => F n k m α τ X y v u) = fun X y => Fc k m α τ X y v u :=
          funext fun X => funext fun y => hidF τ hτ k m α X y v u
        rw [hfun]
        exact ((hboxp τ hτ m α v u).2.2 k).1.mono le_rfl hfast)
    (fun n h1 h2 => by
      obtain ⟨c1, c2, -, -, -, -, -, -, -, -, -⟩ := hpres n h1 h2
      exact ⟨fun α t X z v u => c1 0 α t X z v u (Or.inl rfl),
        fun k α t X z v u => c2 k 0 α t X z v u (Or.inl rfl)⟩)
    (fun n h1 h2 bb hb δ i hi m => by
      obtain ⟨fc, Fc, hfp, hFp, hf0, hF0, -, hact, hboxp, hbd⟩ := harrn n h1 h2
      obtain ⟨hidf, hidF⟩ := presentation_eq Q Cc _ π t₀ t₁ N _ CL Θ hh n (f n) (F n)
        (hpres n h1 h2) fc Fc hfp hFp
        (fun m α t X z v u hm => hf0 m α t X z v u (Or.inr hm))
        (fun k m α t X z v u hm => hF0 k m α t X z v u (Or.inr hm))
        (fun a₀ ha₀ t ht X z k => (hact a₀ ha₀ t ht X z).1 k)
        (fun a₀ ha₀ t ht X z => (hact a₀ ha₀ t ht X z).2)
      have hbb : bb ≤ arrayFastOrder (kl + r) (Ll + r) D := by omega
      constructor
      · rw [schurMixedJet_congr π δ (c := f n m) (d := fc m)
          (fun α t ht X z v u => hidf t ht m α X z v u)]
        refine schurMixedJet_le_mixedSchurConst Acl N D r π hset.mass_pos b hΘ hedge hh hCm
          (Set.Icc t₀ t₁) (m := m) ?_ hi δ (fc m)
          (fun α v u t ht => ((hboxp t ht m α v u).1).mono hi hbb)
          (fun α v u t ht X z => (hbd t ht m α v u i hi bb hbb X z).1)
          (fun hm α t X z v u => hf0 m α t X z v u (Or.inr hm))
        by_cases hm : m ≤ 2 * N + D
        · exact Or.inl (card_words_le N D m hm)
        · exact Or.inr (by omega)
      · rw [schurMixedJet_congr π δ (c := fun q : DerivativeWord2 m × Fin 2 => F n q.2 m q.1)
          (d := fun q : DerivativeWord2 m × Fin 2 => Fc q.2 m q.1)
          (fun q t ht X z v u => hidF t ht q.2 m q.1 X z v u)]
        refine schurMixedJet_le_mixedSchurConst Acl N D r π hset.mass_pos b hΘ hedge hh hCm
          (Set.Icc t₀ t₁) (m := m) ?_ hi δ (fun q : DerivativeWord2 m × Fin 2 => Fc q.2 m q.1)
          (fun q v u t ht => (((hboxp t ht m q.1 v u).2.2 q.2).1).mono hi hbb)
          (fun q v u t ht X z => (hbd t ht m q.1 v u i hi bb hbb X z).2 q.2)
          (fun hm q t X z v u => hF0 q.2 m q.1 t X z v u (Or.inr hm))
        by_cases hm : m ≤ 2 * N + D
        · exact Or.inl (card_flux_words_le N D m hm)
        · exact Or.inr (by omega))
    a ha hmeas Vc hVc Z hZ j hj β
  refine key.trans (le_of_eq ?_)
  congr 2
  ring
end

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! Entrywise operations on coefficient arrays: the difference, the cell mean in the fast
variable, and the fast divergence of a flux array. Each commutes with the lift action, and each
has entry bounds in terms of those of its arguments. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The entrywise difference of two arrays. -/
def subCoeff (c d : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X z v u => c m α t X z v u - d m α t X z v u

/-- The entrywise cell mean in the fast variable (constant in the fast variable). -/
def cellMeanCoeff (c : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X _ v u => fieldCellMean (fun z' => c m α t X z' v u)

/-- The entrywise fast divergence of a flux array. -/
def fastDivCoeff (R : Fin 2 → LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X z v u => ∑ k : Fin 2, fastPartial k (fun X' z' => R k m α t X' z' v u) X z

section Perm

variable {m : ℕ}

omit [Fintype ι] in
theorem subCoeff_perm {c d : LiftCoeff ι h}
    (hc : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hd : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), d m (β ∘ σ) = d m β)
    (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    subCoeff c d m (β ∘ σ) = subCoeff c d m β := by
  funext t X z v u
  simp only [subCoeff, hc β σ, hd β σ]

omit [Fintype ι] in
theorem cellMeanCoeff_perm {c : LiftCoeff ι h}
    (hc : ∀ (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    cellMeanCoeff c m (β ∘ σ) = cellMeanCoeff c m β := by
  funext t X z v u
  simp only [cellMeanCoeff, hc β σ]

omit [Fintype ι] in
theorem fastDivCoeff_perm {R : Fin 2 → LiftCoeff ι h}
    (hR : ∀ k (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), R k m (β ∘ σ) = R k m β)
    (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    fastDivCoeff R m (β ∘ σ) = fastDivCoeff R m β := by
  funext t X z v u
  simp only [fastDivCoeff, hR _ β σ]

end Perm

section Action

theorem liftApply_subCoeff (n : ℕ) (c d : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (X z : Vec 2) :
    liftApply n (subCoeff c d) a t X z = liftApply n c a t X z - liftApply n d a t X z := by
  funext v
  simp [liftApply, subCoeff, Finset.sum_sub_distrib]

theorem liftApply_cellMeanCoeff [∀ i, CompleteSpace (h i)] (n : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hc : ∀ m α u, Continuous (fun z' => c m α t X z' v u)) :
    liftApply n (cellMeanCoeff c) a t X z v = fieldCellMean (fun z' => liftApply n c a t X z' v) := by
  have hterm : ∀ m (α : DerivativeWord2 m) u, Continuous
      (fun z' => c m α t X z' v u (orderedDerivative α (a t) X u)) := fun m α u =>
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a t) X u)).continuous.comp (hc m α u)
  simp only [liftApply]
  rw [fieldCellMean_sum _ fun m _ => continuous_finsetSum _ fun α _ =>
    continuous_finsetSum _ fun u _ => hterm m α u]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fieldCellMean_sum _ fun α _ => continuous_finsetSum _ fun u _ => hterm m α u]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [fieldCellMean_sum _ fun u _ => hterm m α u]
  refine Finset.sum_congr rfl fun u _ => ?_
  have := fieldCellMean_clm (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a t) X u))
    (hc m α u)
  simpa [cellMeanCoeff] using this.symm

theorem liftApply_fastDivCoeff (n : ℕ) (R : Fin 2 → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hR : ∀ k m α v u, ContDiff ℝ 1 (fun y => R k m α t X y v u)) :
    liftApply n (fastDivCoeff R) a t X z v =
      ∑ k : Fin 2, fderiv ℝ (fun z' => liftApply n (R k) a t X z' v) z (basisVec k) := by
  have hk : ∀ k : Fin 2, liftApply n (MixedTail.fastCoeff (![k] : DerivativeWord2 1) (R k))
      a t X z v = fderiv ℝ (fun z' => liftApply n (R k) a t X z' v) z (basisVec k) := by
    intro k
    rw [MixedTail.liftApply_fastCoeff (![k] : DerivativeWord2 1) n (R k) a t X
      (fun m α v u => by exact_mod_cast hR k m α v u) z v]
    simp [orderedDerivative]
  simp_rw [← hk]
  simp only [liftApply]
  symm
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2)))]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [fastDivCoeff, MixedTail.fastCoeff, orderedDerivative, fastPartial]

end Action

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cell mean of a box-smooth field is a slow field with the slow bounds doubled per order. -/
theorem cellMean_box_bound [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p q : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p 0 f) {B : ℝ}
    (hb : ∀ j ≤ p, ∀ X z, ‖iteratedFDeriv ℝ j (fun Y => f Y z) X‖ ≤ B) :
    IsBoxSmooth p q (fun X (_ : Vec 2) => fieldCellMean (f X)) ∧
      ∀ r ≤ p, ∀ s, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun _ : Vec 2 => fieldCellMean (f Y)) z) X‖ ≤ 2 ^ r * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0 (Nat.zero_le _) 0 0)
  have key := fun r (hr : r ≤ p) => Lift.fieldCellMean_graded_jet_bound p r 0 0 hr f hf
    (fun _ => B) 1 (fun j hj X z => by simpa using hb j hj X z)
  refine ⟨Lift.isBoxSmooth_slow_field p q _ (key 0 (Nat.zero_le _)).1, ?_⟩
  intro r hr s X z
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    rw [Lift.norm_mixed_jet_fast_zero r (fun Y (_ : Vec 2) => fieldCellMean (f Y)) X z]
    simpa using (key r hr).2 X
  · have h0 : (fun Y => iteratedFDeriv ℝ s (fun _ : Vec 2 => fieldCellMean (f Y)) z) =
        fun _ => 0 := by
      funext Y
      rw [iteratedFDeriv_const_of_ne hs.ne']
      rfl
    rw [h0]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

/-- The fast divergence costs one fast order. -/
theorem fastDiv_box_bound {p q : ℕ} (f : Fin 2 → Vec 2 → Vec 2 → E)
    (hf : ∀ k, IsBoxSmooth p (q + 1) (f k)) {B : ℝ}
    (hb : ∀ k, ∀ r ≤ p, ∀ s ≤ q + 1, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (f k Y) z) X‖ ≤ B) :
    IsBoxSmooth p q (fun X z => ∑ k : Fin 2, fastPartial k (f k) X z) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => ∑ k : Fin 2, fastPartial k (f k) Y y) z) X‖ ≤ 2 * B := by
  have hbox : ∀ k, IsBoxSmooth p q (fastPartial k (f k)) := fun k => (hf k).fastPartial k
  refine ⟨IsBoxSmooth.sum Finset.univ fun k _ => hbox k, ?_⟩
  intro r hr s hs X z
  have hsum : (fun Y => iteratedFDeriv ℝ s (fun y => ∑ k : Fin 2, fastPartial k (f k) Y y) z) =
      fun Y => ∑ k : Fin 2, iteratedFDeriv ℝ s (fastPartial k (f k) Y) z := by
    funext Y
    rw [iteratedFDeriv_sum (fun k _ => ((hbox k).1 Y).of_le (by exact_mod_cast hs)),
      Finset.sum_apply]
  rw [hsum, iteratedFDeriv_sum (fun k _ =>
    (((hbox k).2.1 s hs z).of_le (by exact_mod_cast hr)))]
  calc ‖∑ k : Fin 2, iteratedFDeriv ℝ r
        (fun Y => iteratedFDeriv ℝ s (fastPartial k (f k) Y) z) X‖
      ≤ ∑ k : Fin 2, ‖iteratedFDeriv ℝ r
        (fun Y => iteratedFDeriv ℝ s (fastPartial k (f k) Y) z) X‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, B := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact (QuietDecay.norm_jetAt_fastPartial_le (hf k) k hr (by omega) X z).trans
          (hb k r hr (s + 1) (by omega) X z)
    _ = 2 * B := by simp

end Bounds

end AVRegularity.CycleComparison.TailPresentation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.TailPresentation

/-! O6 (`cycle_lift_tail_constructed`) from `ArraysStatement`: the constructed arrays satisfy every
clause of `IsConstructedLiftTailPresentation`, with slow constant `2 · 2^(2N+D) · Cm`. -/

universe u v

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- Slow Schur jets of an array family with power-profile bounds, vanishing above order
`2N + D`. -/
theorem schurCellL2Jet_le_o6 (N D : ℕ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ) (hh : ℕ) {Cm : ℝ} (hCm : 0 ≤ Cm)
    (I : Set ℝ) {m : ℕ} {κ : Type*} [Fintype κ]
    (hκ : (Fintype.card κ : ℝ) ≤ 2 * 2 ^ (2 * N + D) ∨ 2 * N + D < m) (j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hcont : ∀ a v u, ∀ t ∈ I, ∀ X,
      Continuous (fun z => iteratedFDeriv ℝ j (fun Y => c a t Y z v u) X))
    (hbd : ∀ a v u, ∀ t ∈ I, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => c a t Y z v u) X‖ ≤
        Cm * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)
    (hzero : 2 * N + D < m → ∀ a t X z v u, c a t X z v u = 0) :
    schurCellL2Jet π I j c ≤ ENNReal.ofReal (2 * 2 ^ (2 * N + D) * Cm * Θ ^ hh) := by
  rcases hκ with hκ | hm
  · refine (schurCellL2Jet_le_of_power_bound π hπ edge hΘ hedge hh hCm I j c hcont hbd).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hΘ hh))
    exact mul_le_mul_of_nonneg_right hκ hCm
  · refine (schurCellL2Jet_le_of_power_bound π hπ edge hΘ hedge hh (K := 0) le_rfl I j c hcont
      (fun a v u t ht X z => ?_)).trans ?_
    · have : (fun Y => c a t Y z v u) = fun _ => 0 := funext fun Y => hzero hm a t Y z v u
      rw [this]
      simp
    · simp only [mul_zero, zero_mul, ENNReal.ofReal_zero]
      exact bot_le

end

theorem card_words_le' (N D m : ℕ) (hm : m ≤ 2 * N + D) :
    (Fintype.card (DerivativeWord2 m) : ℝ) ≤ 2 * 2 ^ (2 * N + D) := by
  have hc : (Fintype.card (DerivativeWord2 m) : ℝ) = 2 ^ m := by simp
  rw [hc]
  calc (2 : ℝ) ^ m ≤ 2 ^ (2 * N + D) := pow_le_pow_right₀ (by norm_num) hm
    _ ≤ 2 * 2 ^ (2 * N + D) := by linarith [pow_pos (two_pos : (0 : ℝ) < 2) (2 * N + D)]

theorem card_flux_words_le' (N D m : ℕ) (hm : m ≤ 2 * N + D) :
    (Fintype.card (DerivativeWord2 m × Fin 2) : ℝ) ≤ 2 * 2 ^ (2 * N + D) := by
  have hc : (Fintype.card (DerivativeWord2 m × Fin 2) : ℝ) = 2 ^ m * 2 := by simp
  rw [hc]
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  linarith

/-- **O6 from the constructed arrays.** -/
theorem o6_of_arrays (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (harr : ArraysStatement.{u, v} N K k L D H CG Cw Cj) :
    O6Statement.{u, v} N K k L D H CG Cw Cj := by
  obtain ⟨Cm, hCm, harr'⟩ := harr
  refine ⟨2 * 2 ^ (2 * N + D) * Cm, by positivity, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq hh hhH n
    h1 h2
  classical
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  obtain ⟨fc, Fc, hfp, hFp, hf0, hF0, hend, hact, hboxp, hbd⟩ :=
    harr' Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq hh hhH n h1 h2
  have hD := hset.D_ge
  have hfast : max (k + 1) (L + 2) - D ≤ arrayFastOrder k L D := by
    unfold arrayFastOrder; omega
  have hfast1 : 1 ≤ arrayFastOrder k L D := by unfold arrayFastOrder; omega
  refine ⟨fc, Fc, hf0, hF0, hend, hfp, hFp, ?_, ?_, hact, ?_, ?_, ?_⟩
  · intro m α v u t ht
    exact ⟨(hboxp t ht m α v u).1.mono le_rfl hfast, (hboxp t ht m α v u).2.1⟩
  · intro k' m α v u t ht
    exact ⟨((hboxp t ht m α v u).2.2 k').1.mono le_rfl hfast, ((hboxp t ht m α v u).2.2 k').2⟩
  · intro a₀ ha₀ t ht X z
    exact tail_identity_of_actions
      (fun k X z => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k)
      (fun k X z => liftApply (2 * N + D) (Fc k) (fun _ => a₀) t X z)
      (fun X z => liftApply (2 * N + D) fc (fun _ => a₀) t X z)
      (fun X z => liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z)
      (fun k X z => (hact a₀ ha₀ t ht X z).1 k) (fun X z => (hact a₀ ha₀ t ht X z).2) X z
  · intro a₀ ha₀ t ht X
    exact mean_zero_of_actions
      (fun k X z => constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k)
      (fun k X z => liftApply (2 * N + D) (Fc k) (fun _ => a₀) t X z)
      (fun X z => liftApply (2 * N + D) fc (fun _ => a₀) t X z)
      (fun X z => liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z)
      (fun k X z => (hact a₀ ha₀ t ht X z).1 k) (fun X z => (hact a₀ ha₀ t ht X z).2)
      (fun k X => contDiff_liftApply_fast (2 * N + D) (Fc k) _ t X fun m α v u =>
        (((hboxp t ht m α v u).2.2 k).1.1 X).of_le (by exact_mod_cast hfast1))
      (fun k X => periodic_liftApply_fast (2 * N + D) (Fc k) _ t X fun m α v u =>
        ((hboxp t ht m α v u).2.2 k).2 X)
      (fun X => (contDiff_liftApply_fast (2 * N + D) fc _ t X fun m α v u =>
        ((hboxp t ht m α v u).1.1 X)).continuous)
      (fun X => setting_liftTailCoeff_mean_zero hset (K + D + 2) (max (k + 1) (L + 2))
        (by omega) (by omega) Cc hseq hh hhH n (by omega) a₀ ha₀ t ht X) X
  · intro j hj m
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
    · constructor <;> simp [schurCellL2Jet, schurSums]
    have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
      (hset.envelope.row_sum v₀)
    have hedge : HasRealSchurBudget b Θ :=
      ⟨hset.envelope.nonneg, hset.envelope.row_sum, hset.envelope.col_sum⟩
    have hs0 : (0 : ℕ) ≤ arrayFastOrder k L D := Nat.zero_le _
    constructor
    · refine schurCellL2Jet_le_o6 N D π hset.mass_pos b hΘ hedge hh hCm (Set.Icc t₀ t₁)
        (m := m) ?_ j (fc m)
        (fun α v u t ht X => continuous_slowJet_of_box (hboxp t ht m α v u).1 hj X)
        (fun α v u t ht X z => by
          have := (hbd t ht m α v u j hj 0 hs0 X z).1
          rwa [norm_mixed_jet_fast_zero j (fun Y y => fc m α t Y y v u) X z] at this)
        (fun hm α t X z v u => hf0 m α t X z v u (Or.inr hm))
      by_cases hm : m ≤ 2 * N + D
      · exact Or.inl (card_words_le' N D m hm)
      · exact Or.inr (by omega)
    · refine schurCellL2Jet_le_o6 N D π hset.mass_pos b hΘ hedge hh hCm (Set.Icc t₀ t₁)
        (m := m) ?_ j (fun q : DerivativeWord2 m × Fin 2 => Fc q.2 m q.1)
        (fun q v u t ht X => continuous_slowJet_of_box ((hboxp t ht m q.1 v u).2.2 q.2).1 hj X)
        (fun q v u t ht X z => by
          have := (hbd t ht m q.1 v u j hj 0 hs0 X z).2 q.2
          rwa [norm_mixed_jet_fast_zero j (fun Y y => Fc q.2 m q.1 t Y y v u) X z] at this)
        (fun hm q t X z v u => hF0 q.2 m q.1 t X z v u (Or.inr hm))
      by_cases hm : m ≤ 2 * N + D
      · exact Or.inl (card_flux_words_le' N D m hm)
      · exact Or.inr (by omega)

end AVRegularity.CycleComparison.TailPresentation
end
end
