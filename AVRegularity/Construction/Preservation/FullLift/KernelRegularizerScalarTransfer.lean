-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
public import AVRegularity.KernelEnergy.TorusMultiplierCLM
import AVRegularity.Proofs.Results.Finite.TraceClosure
public import AVRegularity.EntryWeak.JointSourceCongruence
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Expose each zero-order gain as the squared norm of the full top derivative array. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem regularizer_zero_gain_bound (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : j + 2 ≤ D)
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    ∃ y : TorusHk j E, y.val (valueIndex2 j) = S t z ∧
      (∑ w : DerivativeWord2 j, ‖y.val ⟨⟨j, Nat.lt_succ_self j⟩, w⟩‖ ^ 2) ≤
        (c j / r ^ j) ^ 2 * ‖z‖ ^ 2 := by
  obtain ⟨Y, hY, hb⟩ := hS.2.2.2 t ht j hj (torusZeroCarrier z)
  let y : TorusHk j E := truncateTorusHk (by omega : j ≤ 0 + j) Y
  have hy : y.val (valueIndex2 j) = S t z := by
    have hidx : truncateJetIndex (by omega : j ≤ 0 + j) (valueIndex2 j) =
        valueIndex2 (0 + j) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · rfl
    change Y.val (truncateJetIndex _ (valueIndex2 j)) = _
    rw [hidx]
    exact hY.trans (congrArg (S t) (torusZeroCarrier_value z))
  refine ⟨y, hy, ?_⟩
  rw [factorialNormSq_order_zero, torusZeroCarrier_value] at hb
  unfold derivFactorialNormSq at hb
  rw [Fin.sum_univ_succ] at hb
  simp only [Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul, Fin.sum_univ_zero, add_zero] at hb
  let e : DerivativeWord2 j ≃ DerivativeWord2 (0 + j) :=
    Equiv.arrowCongr (finCongr (Nat.zero_add j).symm) (Equiv.refl (Fin 2))
  have he : (∑ w : DerivativeWord2 j, ‖y.val ⟨⟨j, Nat.lt_succ_self j⟩, w⟩‖ ^ 2) =
      ∑ w : DerivativeWord2 (0 + j), ‖Y.val ⟨⟨0 + j, by omega⟩, w⟩‖ ^ 2 := by
    apply Fintype.sum_equiv e
    intro w
    change ‖Y.val (truncateJetIndex (by omega : j ≤ 0 + j)
      ⟨⟨j, Nat.lt_succ_self j⟩, w⟩)‖ ^ 2 = ‖Y.val ⟨⟨0 + j, by omega⟩, e w⟩‖ ^ 2
    apply congrArg (fun a : JetIndex2 (0 + j) => ‖Y.val a‖ ^ 2)
    apply Sigma.ext
    · apply Fin.ext
      change j = 0 + j
      omega
    · change w ≍ e w
      apply (Fin.heq_fun_iff (by omega)).mpr
      intro i
      rfl
  rw [he]
  exact hb
end

/-! At input order zero the regularizer certificate is independent of the factorial radius. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem derivFactorialNormSq_zero_radius (ρ R : ℝ) (j : ℕ)
    (Z : JetL2 (volume.restrict AVenhance.unitCube) (0 + j) E) :
    derivFactorialNormSq (K := 0) j ρ Z = derivFactorialNormSq (K := 0) j R Z := by
  unfold derivFactorialNormSq
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, factorialWeight,
    Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul, add_zero]

theorem spatial_regularizer_zero_radius [FiniteDimensional ℝ E]
    (ρ R : ℝ) (D : ℕ) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus R 0 D a b c r S) :
    IsSpatialRegularizerTorus ρ 0 D a b c r S := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, ?_⟩
  intro t ht j hj z
  obtain ⟨Y, hY, hb⟩ := hS.2.2.2 t ht j hj z
  refine ⟨Y, hY, ?_⟩
  rw [derivFactorialNormSq_zero_radius ρ R j Y.val,
    factorialNormSq_order_zero, ← factorialNormSq_order_zero R z]
  exact hb
end

/-! The covariance polynomial's individual powers have the exact periodic duality identity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOperator_power_cellInner_adjoint (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) (r : ℕ) (u q : Vec 2 → E)
    (hu : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) u)
    (hq : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) q)
    (hpu : AVenhance.IsZ2Periodic u) (hpq : AVenhance.IsZ2Periodic q) :
    cellInner ((covOperator Hc)^[r] u) q = cellInner u ((covOperator Hc)^[r] q) := by
  induction r generalizing u q with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have huR : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) u :=
      hu.of_le (by exact_mod_cast (by omega : 2 * r ≤ 2 * (r + 1)))
    have huMid : ContDiff ℝ 2 ((covOperator Hc)^[r] u) := by
      apply covOperator_iterate_contDiff Hc r 2
      simpa only [Nat.mul_succ, Nat.add_comm] using hu
    have hq2 : ContDiff ℝ 2 q :=
      hq.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((2 * (r + 1) : ℕ) : WithTop ℕ∞) from
        by exact_mod_cast (by omega : 2 ≤ 2 * (r + 1)))
    have hqR : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) (covOperator Hc q) := by
      apply covOperator_contDiff Hc (2 * r)
      simpa only [Nat.mul_succ] using hq
    rw [covOperator_cellInner_adjoint Hc hH _ q huMid hq2
      (covOperator_iterate_periodic Hc r u huR hpu) hpq]
    have hrec := ih u (covOperator Hc q) huR hqR hpu (covOperator_periodic Hc q hq2 hpq)
    simpa only [Function.iterate_succ_apply] using hrec
end

/-! Preserve the zero-order gain constant on every differentiated input word. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem regularizer_gain_word_budget (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : j + 2 ≤ D)
    {K : ℕ} (x : TorusHk K E) (y : TorusHk (K + j) E)
    (hvalue : y.val (valueIndex2 (K + j)) = S t (x.val (valueIndex2 K)))
    (s : Fin (K + 1)) (w : DerivativeWord2 s.val) :
    (∑ v : DerivativeWord2 j,
      ‖y.val ⟨⟨s.val + j, by have := s.isLt; omega⟩, Fin.append w v⟩‖ ^ 2) ≤
      (c j / r ^ j) ^ 2 * ‖x.val ⟨s, w⟩‖ ^ 2 := by
  have hlo : K ≤ K + j := Nat.le_add_right K j
  let ylo : TorusHk K E := truncateTorusHk hlo y
  have hvlo : ylo.val (valueIndex2 K) = S t (x.val (valueIndex2 K)) := hvalue
  have hjet := commuting_operator_jets (S t) (hS.2.1 t ht) K x ylo hvlo ⟨s, w⟩
  have hys : j + s.val ≤ K + j := by have := s.isLt; omega
  let g : TorusHk j E := derivativeTorusHk (K := j) (r := s.val) w
    (truncateTorusHk hys y)
  have hidx : truncateJetIndex hys (prefixJetIndex w (valueIndex2 j)) =
      truncateJetIndex hlo (⟨s, w⟩ : JetIndex2 K) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · change Fin.append w Fin.elim0 ≍ w
      rw [Fin.append_elim0]
      exact heq_of_eq rfl
  have hgv : g.val (valueIndex2 j) = S t (x.val ⟨s, w⟩) := by
    change y.val (truncateJetIndex hys (prefixJetIndex w (valueIndex2 j))) = _
    rw [hidx]
    exact hjet
  obtain ⟨Z, hZ, hb⟩ := regularizer_zero_gain_bound ρ D a b c r S hS t ht j hj
    (x.val ⟨s, w⟩)
  have hgZ : g = Z := TorusHk.ext_value (hgv.trans hZ.symm)
  change (∑ v : DerivativeWord2 j, ‖g.val ⟨⟨j, Nat.lt_succ_self j⟩, v⟩‖ ^ 2) ≤ _
  rw [hgZ]
  exact hb
end

/-! Sum the differentiated-input gains over the complete ordered tensor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem regularizer_gain_array_budget (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : j + 2 ≤ D)
    {K : ℕ} (x : TorusHk K E) (y : TorusHk (K + j) E)
    (hvalue : y.val (valueIndex2 (K + j)) = S t (x.val (valueIndex2 K)))
    (s : Fin (K + 1)) :
    (∑ v : DerivativeWord2 (s.val + j),
      ‖y.val ⟨⟨s.val + j, by have := s.isLt; omega⟩, v⟩‖ ^ 2) ≤
      (c j / r ^ j) ^ 2 * derivativeNormSq x.val s := by
  classical
  calc
    _ = ∑ w : DerivativeWord2 s.val, ∑ v : DerivativeWord2 j,
        ‖y.val ⟨⟨s.val + j, by have := s.isLt; omega⟩, Fin.append w v⟩‖ ^ 2 := by
      rw [← Fintype.sum_prod_type (fun p : DerivativeWord2 s.val × DerivativeWord2 j =>
        ‖y.val ⟨⟨s.val + j, by have := s.isLt; omega⟩, Fin.append p.1 p.2⟩‖ ^ 2)]
      exact (Fintype.sum_equiv (wordAppendEquiv s.val j) _ _ (fun _ => rfl)).symm
    _ ≤ ∑ w : DerivativeWord2 s.val,
        (c j / r ^ j) ^ 2 * ‖x.val ⟨s, w⟩‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      exact regularizer_gain_word_budget ρ D a b c r S hS t ht j hj x y hvalue s w
    _ = (c j / r ^ j) ^ 2 * derivativeNormSq x.val s := by
      rw [derivativeNormSq, Finset.mul_sum]
end

/-! The full factorial gain propagates with its original zero-order constant. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem regularizer_all_order_gain_bound (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : j + 2 ≤ D)
    (K : ℕ) (z : TorusHk K E) :
    ∃ y : TorusHk (K + j) E, y.val (valueIndex2 (K + j)) = S t (z.val (valueIndex2 K)) ∧
      derivFactorialNormSq j ρ y.val ≤ (c j / r ^ j) ^ 2 * factorialNormSq ρ z.val := by
  obtain ⟨y, hy⟩ := regularizer_all_order_carrier ρ D a b c r S hS t ht j hj K z
  refine ⟨y, hy, ?_⟩
  unfold derivFactorialNormSq factorialNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ factorialWeight ρ s.val * ((c j / r ^ j) ^ 2 * derivativeNormSq z.val s) :=
      mul_le_mul_of_nonneg_left
        (regularizer_gain_array_budget ρ D a b c r S hS t ht j hj z y hy s)
        (factorialWeight_nonneg ρ s.val)
    _ = (c j / r ^ j) ^ 2 * (factorialWeight ρ s.val * derivativeNormSq z.val s) := by ring

theorem spatial_regularizer_all_orders (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S) (K : ℕ) :
    IsSpatialRegularizerTorus ρ K D a b c r S := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, ?_⟩
  intro t ht j hj z
  exact regularizer_all_order_gain_bound ρ D a b c r S hS t ht j hj K z
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Landed passage scales and cascade inheritance pay the original higher-record radii. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {Mn : SuccMenu} {seed G : GenStage D hr Dm bw j₀}

theorem cascade_record_length_of_passScales {Cw cr σ₀ η₀ Cu : ℝ} {N p m₀ : ℕ}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hcr : cr ≤ 1)
    (hseedT : seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p))
    (hseedL : ∀ v u (γ : seed.fam.Γ v u),
      1 ≤ (seed.fam.identity v u γ).record.birthExcess →
        (seed.fam.identity v u γ).record.length ≤ D.eps seed.level)
    (hscales : ∀ b', m₀ ≤ b' → b' < seed.level → Providers.CascadeInvariants.PassScales D (b' + 1) Cu)
    (hc : IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G)
    (hm : m₀ ≤ G.level) :
    ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level := by
  apply Providers.CascadeInvariants.length_le_eps_of_cascade hseedT hseedL
    (fun k => Providers.CascadeInvariants.eps_succ_le hq hΛ k) _ hc hm
  intro b' hb hbs
  exact Providers.CascadeInvariants.freshLength_le_eps_of_passScales hcr (hscales b' hb hbs)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The uniform passage-scale theorem propagates seed record lengths throughout the cascade. -/

theorem uniform_cascade_record_length {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.ζ = ζ → Λ₀ ≤ D.Λ →
    IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (Mn : SuccMenu)
      (Cw cr σ₀ η₀ : ℝ) (N p : ℕ), cr ≤ 1 →
    ∀ seed G : GenStage D hr Dm bw j₀,
    seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p) →
    (∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level) →
    seed.level ≤ D.term →
    IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G → 1 ≤ G.level →
    ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level := by
  obtain ⟨Cu, _hCu, Λ₀, hΛ₀, hscales⟩ := Providers.CascadeInvariants.exists_passScales hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro hr _ _ D hDα hDq hDζ hΛ hband Dm bw j₀ Mn Cw cr σ₀ η₀ N p hcr
    seed G htags hlength hn hc hi
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := hΛ₀.trans hΛ
  have hband' : IsOCBandChain α q D.Λ ζ D.term D.κ := by
    simpa only [hDα, hDq, hDζ] using hband
  apply cascade_record_length_of_passScales (Cu := Cu) (m₀ := 1) hqD hΛD hcr htags hlength _ hc hi
  intro b' hb hbs
  exact hscales D hDα hDq hDζ hΛ hband' (b' + 1) (by omega) (by omega)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
section
/-! The dependent component-root cast preserves a classical representative. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem classicalRep_rootCast {i j K r : ℕ} (h : i = j)
    (W : TorusHk K (hr i)) (a : Vec 2 → hr i) (hrep : IsClassicalRep W a r) :
    IsClassicalRep (cast (congrArg (fun n => TorusHk K (hr n)) h) W)
      (fun x => cast (congrArg hr h) (a x)) r := by
  subst j
  exact hrep

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Reuse the compiled factorial integrability bridge for the actual component-sup strong energy. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_component_integral {ρ ν a b : ℝ} (hν : 0 ≤ ν)
    (π : ι → ℝ) {K : ℕ}
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    strongEnergy ρ ν π a b u w =
      (∑ i, ENNReal.ofReal (π i)⁻¹ *
        ((⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
          ENNReal.ofReal (ν * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val))) ^
        (1 / 2 : ℝ) := by
  unfold strongEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hw i))
    (Filter.Eventually.of_forall fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg ρ _),
    ← ENNReal.ofReal_mul hν]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Scalar convolution commutes with every constant Hilbert fiber map. These identities
are the algebraic input to transfer regularizer certificates without changing constants. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Preservation.FullLift

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
section Linear
variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Constant fiber maps commute with measure preserving pullback. -/
theorem lp_fiberMap_pullback {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (g : X → Y) (hg : MeasurePreserving g μ ν)
    (L : E →L[ℝ] F) (z : Lp E 2 ν) :
    L.compLpL 2 μ (Lp.compMeasurePreservingₗᵢ ℝ g hg z) =
      Lp.compMeasurePreservingₗᵢ ℝ g hg (L.compLpL 2 ν z) := by
  apply Lp.ext
  have hL := L.coeFn_compLpL (Lp.compMeasurePreservingₗᵢ ℝ g hg z)
  have hX := Lp.coeFn_compMeasurePreserving z hg
  have hR := Lp.coeFn_compMeasurePreserving (L.compLpL 2 ν z) hg
  have hLX := hg.quasiMeasurePreserving.ae_eq_comp (L.coeFn_compLpL z)
  filter_upwards [hL, hX, hR, hLX] with x hl hx hr hlx
  exact hl.trans ((congrArg L hx).trans (hr.trans hlx).symm)

section Average
variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] [CompleteSpace E] [CompleteSpace F]

/-- The Bochner average commutes with a constant fiber map. -/
theorem averagingOperator_fiberMap (L : E →L[ℝ] F)
    (ρ : Vec 2 →+ X) (hρ : Continuous ρ) (κ : Vec 2 → ℝ) (hκ : Integrable κ)
    (z : Lp E 2 μ) :
    L.compLpL 2 μ (averagingOperator ρ hρ κ hκ z) =
      averagingOperator ρ hρ κ hκ (L.compLpL 2 μ z) := by
  rw [averagingOperator_apply, ← (L.compLpL 2 μ).integral_comp_comm
    (integrable_average_integrand ρ hρ hκ z), averagingOperator_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [map_smul]
    congr 1
    exact lp_fiberMap_pullback _ (measurePreserving_add_left μ (-(ρ x))) L z
end Average
end Linear

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [BorelSpace F] in
/-- The literal torus average commutes with a constant fiber map. -/
theorem periodicComponentAverage_fiberMap (L : E →L[ℝ] F)
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ) (κ : Vec 2 → ℝ) (hκ : Integrable κ)
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    L.compLpL 2 (volume.restrict AVenhance.unitCube) (periodicComponentAverage ρ hρ κ hκ z) =
      periodicComponentAverage ρ hρ κ hκ (L.compLpL 2 (volume.restrict AVenhance.unitCube) z) := by
  simp only [periodicComponentAverage, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  have hc (y : Lp E 2 torusMeasure) :
      L.compLpL 2 (volume.restrict AVenhance.unitCube) (torusToCell y) =
        torusToCell (L.compLpL 2 torusMeasure y) :=
    lp_fiberMap_pullback _ measurePreserving_torusQuotient_cell L y
  have ht (y : Lp E 2 (volume.restrict AVenhance.unitCube)) :
      L.compLpL 2 torusMeasure (cellToTorus y) =
        cellToTorus (L.compLpL 2 (volume.restrict AVenhance.unitCube) y) :=
    lp_fiberMap_pullback _ measurePreserving_unitTorusRepresentative_cell L y
  rw [hc, averagingOperator_fiberMap, ht]

/-- The actual paired kernel commutes with all constant fiber maps. -/
theorem kernelSpec_op_fiberMap (L : E →L[ℝ] F)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec) (t : ℝ)
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    L.compLpL 2 (volume.restrict AVenhance.unitCube) (S.op φ₀ hφ₀ t z) =
      S.op φ₀ hφ₀ t (L.compLpL 2 (volume.restrict AVenhance.unitCube) z) := by
  simp only [KernelSpec.op, ContinuousLinearMap.comp_apply]
  rw [periodicComponentAverage_fiberMap L,
    periodicComponentAverage_fiberMap L]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The literal moving kernel preserves every ordered periodic weak jet. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Analysis.Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def kernelSpecWeakAverage (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (S : KernelSpec) (t : ℝ) {k : ℕ} (z : TorusHk k E) : TorusHk k E :=
  periodicWeakAverage (displacement S.width (S.H₁ t))
    (continuous_displacement S.width (S.H₁ t)) (momentKernel φ₀ S.order)
    (integrable_momentKernel hφ₀ S.order)
    (periodicWeakAverage (displacement S.width (S.H₂ t))
      (continuous_displacement S.width (S.H₂ t)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ₀ S.order) z)

theorem kernelSpecWeakAverage_component (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (S : KernelSpec) (t : ℝ) {k : ℕ} (z : TorusHk k E) (a : JetIndex2 k) :
    (kernelSpecWeakAverage φ₀ hφ₀ S t z).val a = S.op φ₀ hφ₀ t (z.val a) := rfl

theorem kernelSpec_commutes_first_derivatives (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (S : KernelSpec) (t : ℝ) (z : TorusHk 1 E) :
    ∃ y : TorusHk 1 E, y.val (valueIndex2 1) = S.op φ₀ hφ₀ t (z.val (valueIndex2 1)) ∧
      ∀ i : Fin 2, y.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
        S.op φ₀ hφ₀ t (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩) := by
  exact ⟨kernelSpecWeakAverage φ₀ hφ₀ S t z, rfl, fun _ => rfl⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Classical representatives identify the actual stored jet energies, without choosing a new field. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_jet_energy_eq {K r m : ℕ} (W : TorusHk K E) (f : Vec 2 → E)
    (hrep : IsClassicalRep W f r) (hm : m ≤ r) (w : DerivativeWord2 m) :
    ENNReal.ofReal (‖W.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrep.1)⟩, w⟩‖ ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w f x‖ₑ ^ 2 := by
  rw [ofReal_L2_norm_sq_eq_lintegral]
  apply lintegral_congr_ae
  have hweak : (fun x => W.val ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrep.1)⟩, w⟩ x) =ᵐ[
      volume.restrict AVenhance.unitCube] torusJetOrder W m w := by
    unfold torusJetOrder
    simp only [dite_eq_left (hm.trans hrep.1)]
    exact (periodicJetRepresentative_ae W.val
      ⟨⟨m, Nat.lt_succ_of_le (hm.trans hrep.1)⟩, w⟩).symm
  filter_upwards [hweak, hrep.2.2.2 m hm w] with x h₁ h₂
  rw [h₁, h₂]

theorem classicalRep_factorial_energy_eq {K : ℕ} (ρ : ℝ) (W : TorusHk K E)
    (f : Vec 2 → E) (hrep : IsClassicalRep W f K) :
    ENNReal.ofReal (factorialNormSq ρ W.val) = classicalFactorialSq ρ K f := by
  rw [factorialNormSq, ENNReal.ofReal_sum_of_nonneg
    (fun j _ => mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _))]
  have hlevel (j : Fin (K + 1)) :
      ENNReal.ofReal (factorialWeight ρ j.1 * derivativeNormSq W.val j) =
      ENNReal.ofReal (ρ ^ (2 * j.1) / (j.1.factorial : ℝ) ^ 2) *
        ∑ w : DerivativeWord2 j.1, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w f x‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _), derivativeNormSq,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    exact classicalRep_jet_energy_eq W f hrep (Nat.lt_succ_iff.mp j.2) w
  simp_rw [hlevel]
  exact Fin.sum_univ_eq_sum_range
    (fun j => ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) *
      ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w f x‖ₑ ^ 2) (K + 1)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Strong measurability of the literal paired moving kernel on the cell carrier. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Analysis.Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] in
theorem moving_periodic_average_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (H : T → Vec 2 →L[ℝ] Vec 2) (hH : Measurable H) (r : ℝ)
    (κ : Vec 2 → ℝ) (hκ : Measurable κ) (hκint : Integrable κ)
    (f : T → Lp E 2 (volume.restrict AVenhance.unitCube)) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun t => periodicComponentAverage
      (displacement r (H t)) (continuous_displacement r (H t)) κ hκint (f t)) := by
  have htorus := moving_torus_average_stronglyMeasurable H hH r κ hκ hκint
    (fun t => cellToTorus (f t)) (cellToTorus.continuous.comp_stronglyMeasurable hf)
  exact torusToCell.continuous.comp_stronglyMeasurable htorus

theorem kernelSpec_op_stronglyMeasurable (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (S : KernelSpec) (hH₁ : Measurable S.H₁) (hH₂ : Measurable S.H₂)
    (hκ : Measurable (momentKernel φ₀ S.order))
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    StronglyMeasurable (fun t => S.op φ₀ hφ₀ t z) := by
  let inner : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) := fun t =>
    periodicComponentAverage (displacement S.width (S.H₂ t))
      (continuous_displacement S.width (S.H₂ t)) (momentKernel φ₀ S.order)
      (integrable_momentKernel hφ₀ S.order) z
  have hinner : StronglyMeasurable inner :=
    moving_periodic_average_stronglyMeasurable S.H₂ hH₂ S.width
      (momentKernel φ₀ S.order) hκ (integrable_momentKernel hφ₀ S.order)
      (fun _ => z) stronglyMeasurable_const
  change StronglyMeasurable (fun t => periodicComponentAverage
    (displacement S.width (S.H₁ t)) (continuous_displacement S.width (S.H₁ t))
    (momentKernel φ₀ S.order) (integrable_momentKernel hφ₀ S.order) (inner t))
  exact moving_periodic_average_stronglyMeasurable S.H₁ hH₁ S.width
    (momentKernel φ₀ S.order) hκ (integrable_momentKernel hφ₀ S.order) inner hinner

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Transfer component square bounds to the literal component-sup strong energy. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_le_of_component_square_bounds {K L : ℕ}
    (ρ σ ν a b C : ℝ) (hC : 0 ≤ C) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (z : ∀ i, ℝ → TorusHk L (h i)) (v : ∀ i, ℝ → TorusHk (L + 1) (h i))
    (hv : ∀ i, AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq σ (v i t).val))
      (volume.restrict (Set.Icc a b)))
    (hu : ∀ i, ∀ t ∈ Set.Icc a b,
      factorialNormSq ρ (u i t).val ≤ C ^ 2 * factorialNormSq σ (z i t).val)
    (hw : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      gradFactorialNormSq ρ (w i t).val ≤ C ^ 2 * gradFactorialNormSq σ (v i t).val) :
    strongEnergy ρ ν π a b u w ≤ ENNReal.ofReal C * strongEnergy σ ν π a b z v := by
  classical
  let F := fun i t => (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (u i t).val)
  let W := fun i t => (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (w i t).val)
  let G := fun i t => (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (factorialNormSq σ (z i t).val)
  let V := fun i t => (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (gradFactorialNormSq σ (v i t).val)
  have hV : ∀ i, AEMeasurable (V i) (volume.restrict (Set.Icc a b)) :=
    fun i => aemeasurable_const.mul (hv i)
  have hvalue : ∀ i, ∀ t ∈ Set.Icc a b,
      F i t ≤ ENNReal.ofReal (C ^ 2) * ∑ j, if id j = i then G j t else 0 := by
    intro i t ht
    have hb := mul_le_mul' (le_refl ((ENNReal.ofReal (π i))⁻¹)) (ENNReal.ofReal_le_ofReal (hu i t ht))
    simpa [F, G, ENNReal.ofReal_mul (sq_nonneg C), mul_left_comm] using hb
  have hgrad : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      W i t ≤ ENNReal.ofReal (C ^ 2) * ∑ j, if id j = i then V j t else 0 := by
    intro i
    filter_upwards [hw i] with t ht
    have hb := mul_le_mul' (le_refl ((ENNReal.ofReal (π i))⁻¹)) (ENNReal.ofReal_le_ofReal ht)
    simpa [W, V, ENNReal.ofReal_mul (sq_nonneg C), mul_left_comm] using hb
  have hs := parent_component_strong_energy_le (volume.restrict (Set.Icc a b)) id
    (Set.Icc a b) (ENNReal.ofReal (C ^ 2)) (ENNReal.ofReal ν) F W G V hV hvalue hgrad
  have hroot : (ENNReal.ofReal (C ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg C) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hC]
  rw [strongEnergy_weighted_components ρ ν a b π hπ,
    strongEnergy_weighted_components σ ν a b π hπ]
  simpa only [hroot, F, W, G, V] using hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A fixed radius ratio transfers strong energy without increasing jet orders. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_mul_radius_le {K : ℕ} {A : ℝ} (hA : 1 ≤ A)
    (ρ ν a b : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (hw : ∀ i, AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq ρ (w i t).val))
      (volume.restrict (Set.Icc a b))) :
    strongEnergy (A * ρ) ν π a b u w ≤
      ENNReal.ofReal (A ^ K) * strongEnergy ρ ν π a b u w := by
  have hpow : (A ^ K) ^ 2 = A ^ (2 * K) := by rw [← pow_mul, Nat.mul_comm]
  apply strongEnergy_le_of_component_square_bounds (A * ρ) ρ ν a b (A ^ K)
    (pow_nonneg (le_trans zero_le_one hA) _) π hπ u w u w hw
  · intro i t _
    simpa only [hpow] using factorialNormSq_mul_radius_le hA ρ (u i t).val
  · intro i
    exact Filter.Eventually.of_forall fun t => by
      simpa only [hpow] using gradFactorialNormSq_mul_radius_le hA ρ (w i t).val

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Truncation contracts both parts of the literal component-sup strong energy. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem gradFactorialNormSq_truncate_le {μ : Measure (Vec 2)} {K L : ℕ}
    (hKL : K ≤ L) (ρ : ℝ) (D : JetL2 μ (L + 1) E) :
    gradFactorialNormSq ρ (truncateJet (Nat.succ_le_succ hKL) D) ≤
      gradFactorialNormSq ρ D := by
  let F : Fin (L + 1) → ℝ := fun j => factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 (j.val + 1), ‖D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2
  change (∑ j : Fin (K + 1), F (Fin.castLE (Nat.succ_le_succ hKL) j)) ≤ ∑ j, F j
  exact sum_comp_le_sum_nonneg (Fin.castLE (Nat.succ_le_succ hKL))
    (Fin.castLE_injective _) F (fun j => mul_nonneg (factorialWeight_nonneg _ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_truncate_le {K L : ℕ} (hKL : K ≤ L)
    (ρ ν : ℝ) (π : ι → ℝ) (a b : ℝ)
    (u : ∀ i, ℝ → TorusHk L (h i)) (w : ∀ i, ℝ → TorusHk (L + 1) (h i)) :
    strongEnergy ρ ν π a b
      (fun i t => truncateTorusHk hKL (u i t))
      (fun i t => truncateTorusHk (Nat.succ_le_succ hKL) (w i t)) ≤
        strongEnergy ρ ν π a b u w := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul' le_rfl
  apply add_le_add
  · apply iSup_mono
    intro t
    apply iSup_mono
    intro _ht
    apply ENNReal.ofReal_le_ofReal
    exact (Real.sqrt_le_sqrt_iff
      (factorialNormSq_nonneg ρ _)).mp
      (CycleComparison.Coarse.sqrt_fNSq_torus_truncate_le ρ hKL (u i t))
  · apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (gradFactorialNormSq_truncate_le hKL ρ (w i t).val)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A scalar classical representative of a Hilbert coordinate represents the same native jet. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classical_coordinate_jet {K r : ℕ} (W : TorusHk K E) (L : E →L[ℝ] ℝ)
    (a : Vec 2 → ℝ) (hrep : IsClassicalRep (KernelEnergy.mapTorusHk L W) a r)
    {m : ℕ} (hm : m ≤ r) (w : DerivativeWord2 m) :
    (fun x => L (torusJetOrder W m w x)) =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative w a := by
  have hmK := hm.trans hrep.1
  have hmap := KernelEnergy.mapTorusHk_toFunction_jet_ae L W
    ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
  have hr := hrep.2.2.2 m hm w
  unfold torusJetOrder at hr ⊢
  simp only [hmK, ↓reduceDIte] at hr ⊢
  exact hmap.symm.trans hr

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The classical gradient factorial energy is the stored Sobolev gradient energy. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_gradient_energy_eq {K : ℕ} (ρ : ℝ) (W : TorusHk (K + 1) E)
    (f : Vec 2 → E) (hrep : IsClassicalRep W f (K + 1)) :
    ENNReal.ofReal (gradFactorialNormSq ρ W.val) = classicalGradFactorialSq ρ K f := by
  rw [gradFactorialNormSq]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
  have hlevel (j : Fin (K + 1)) :
      ENNReal.ofReal (factorialWeight ρ j.1 *
        ∑ w : DerivativeWord2 (j.1 + 1),
          ‖W.val ⟨⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, w⟩‖ ^ 2) =
      ENNReal.ofReal (ρ ^ (2 * j.1) / (j.1.factorial : ℝ) ^ 2) *
        ∑ w : DerivativeWord2 (j.1 + 1),
          ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w f x‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    exact classicalRep_jet_energy_eq W f hrep (by have := j.2; omega) w
  simp_rw [hlevel]
  exact Fin.sum_univ_eq_sum_range
    (fun j => ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) *
      ∑ w : DerivativeWord2 (j + 1), ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w f x‖ₑ ^ 2) (K + 1)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A classical representative survives truncation without choosing a new representative. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusJetOrder_truncate_ae {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E)
    {m : ℕ} (hm : m ≤ K) (w : DerivativeWord2 m) :
    torusJetOrder (truncateTorusHk hKL f) m w =ᵐ[volume.restrict AVenhance.unitCube]
      torusJetOrder f m w := by
  have h := KernelEnergy.truncateTorusHk_toFunction_jet_ae hKL f
    ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩
  unfold torusJetOrder
  simp only [hm, hm.trans hKL, ↓reduceDIte]
  exact h

theorem classicalRep_truncate {K L r : ℕ} (hKL : K ≤ L) (hrK : r ≤ K)
    (f : TorusHk L E) (a : Vec 2 → E) (hrep : IsClassicalRep f a r) :
    IsClassicalRep (truncateTorusHk hKL f) a r := by
  refine ⟨hrK, hrep.2.1, hrep.2.2.1, ?_⟩
  intro m hm w
  exact (torusJetOrder_truncate_ae hKL f (hm.trans hrK) w).trans (hrep.2.2.2 m hm w)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The existing finite classical scalar jet gives its own classical representative. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

theorem classical_scalarHk_rep (K : ℕ) (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ (K : ℕ∞) a) (hp : AVenhance.IsZ2Periodic a) :
    IsClassicalRep (EntryWeakProofs.classicalFiniteHk K a ha hp).toHk a K := by
  refine ⟨le_rfl, ha, hp, ?_⟩
  intro m hm w
  let F := EntryWeakProofs.classicalFiniteHk K a ha hp
  have hj := torusJetToL2_ae F.jet F.hasPeriodicWeakJet.2.1
    (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : JetIndex2 K)
  have hr := KernelEnergy.torusHk_toFunction_jet_ae F.toHk
    (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : JetIndex2 K)
  unfold torusJetOrder
  simp only [hm, ↓reduceDIte]
  have hc : F.jet ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ = orderedDerivative w a := by
    rw [Providers.orderedDerivative_eq_classicalWordDerivative]
    rfl
  rw [hc] at hj
  exact hr.trans hj

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Assemble scalar coordinate representatives into a genuine finite-Hilbert representative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem classical_coordinate_assembly {K r : ℕ} (hrK : r ≤ K) (W : TorusHk K E)
    (a : Fin (Module.finrank ℝ E) → Vec 2 → ℝ)
    (hrep : ∀ i, IsClassicalRep
      (KernelEnergy.mapTorusHk (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)) W)
      (a i) r) :
    IsClassicalRep W (fun x => ∑ i, a i x • stdOrthonormalBasis ℝ E i) r := by
  have ha (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ (r : ℕ∞) (a i) := (hrep i).2.1
  refine ⟨hrK, ContDiff.sum (fun i _ => (ha i).smul contDiff_const), ?_, ?_⟩
  · intro n x
    apply Finset.sum_congr rfl
    intro i _
    rw [(hrep i).2.2.1 n x]
  · intro m hm w
    have ham (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ (m : ℕ∞) (a i) :=
      (ha i).of_le (by exact_mod_cast hm)
    have hd := orderedDerivative_coordinate_synthesis w a (stdOrthonormalBasis ℝ E) ham
    have hc (i : Fin (Module.finrank ℝ E)) := classical_coordinate_jet W
      (InnerProductSpace.toDual ℝ E (stdOrthonormalBasis ℝ E i)) (a i) (hrep i) hm w
    filter_upwards [ae_all_iff.mpr hc] with x hx
    rw [hd]
    calc
      _ = ∑ i, inner ℝ (stdOrthonormalBasis ℝ E i) (torusJetOrder W m w x) •
          stdOrthonormalBasis ℝ E i := (stdOrthonormalBasis ℝ E).sum_repr' _ |>.symm
      _ = _ := Finset.sum_congr rfl fun i _ => congrArg
        (fun z : ℝ => z • stdOrthonormalBasis ℝ E i) (hx i)
end

/-! Classical gradient densities inherit time measurability from their actual Sobolev carriers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalGradFactorialSq_aemeasurable {K : ℕ} (ρ : ℝ) (μ : Measure ℝ)
    (W : ℝ → TorusHk (K + 1) E) (f : ℝ → Vec 2 → E)
    (hW : AEStronglyMeasurable W μ)
    (hrep : ∀ᵐ t ∂μ, IsClassicalRep (W t) (f t) (K + 1)) :
    AEMeasurable (fun t => classicalGradFactorialSq ρ K (f t)) μ := by
  have hc : Continuous (fun w : TorusHk (K + 1) E => gradFactorialNormSq ρ w.val) :=
    (CycleComparison.Coarse.continuous_gradFactorialNormSq ρ K).comp continuous_subtype_val
  have hm := (hc.comp_aestronglyMeasurable hW).aemeasurable.ennreal_ofReal
  apply hm.congr
  filter_upwards [hrep] with t ht
  exact classicalRep_gradient_energy_eq ρ (W t) (f t) ht
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual component-sup Sobolev energy agrees with the energy of shared classical representatives. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem classicalRep_strong_energy_eq_ae {K : ℕ} (ρ ν t₀ t₁ : ℝ) (π : ι → ℝ)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (a : ℝ → Vec 2 → ∀ i, h i)
    (hu : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, IsClassicalRep (u i t) (fun x => a t x i) K)
    (hw : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
      IsClassicalRep (w i t) (fun x => a t x i) (K + 1)) :
    strongEnergy ρ ν π t₀ t₁ u w = classicalStrongEnergy ρ ν π (Set.Icc t₀ t₁) K a := by
  unfold strongEnergy classicalStrongEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  congr 1
  · apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    exact classicalRep_factorial_energy_eq ρ (u i t) _ (hu i t ht)
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [hw i] with t ht
    exact classicalRep_gradient_energy_eq ρ (w i t) _ ht

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.FullLift

/-! Contractive fiber maps and finite Hilbert Parseval on the literal L² jet norms.
These formulas retain the regularizer constants when passing between root spaces. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- Composition of constant fiber maps is literal composition on L² classes. -/
theorem lp_fiberMap_comp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : E →L[ℝ] F) {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : F →L[ℝ] H) (z : Lp E 2 μ) :
    T.compLpL 2 μ (L.compLpL 2 μ z) = (T.comp L).compLpL 2 μ z := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL (L.compLpL 2 μ z), L.coeFn_compLpL z,
    (T.comp L).coeFn_compLpL z] with x hx hy hz
  exact hx.trans ((congrArg T hy).trans hz.symm)

/-- A contractive fiber map contracts every factorial Sobolev norm. -/
theorem fiberMap_factorialNormSq_le {K : ℕ} (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (ρ : ℝ) (z : TorusHk K E) :
    factorialNormSq ρ (mapTorusHk L z).val ≤ factorialNormSq ρ z.val := by
  unfold factorialNormSq derivativeNormSq
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ j.val)
  apply Finset.sum_le_sum
  intro w _
  rw [mapTorusHk_jet_eq_compLp]
  exact pow_le_pow_left₀ (norm_nonneg _) ((L.norm_compLp_le _).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))) 2

/-- The same contraction applies to the shifted derivative norm. -/
theorem fiberMap_derivFactorialNormSq_le {K : ℕ} (j : ℕ) (L : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (ρ : ℝ) (z : TorusHk (K + j) E) :
    derivFactorialNormSq j ρ (mapTorusHk L z).val ≤ derivFactorialNormSq j ρ z.val := by
  unfold derivFactorialNormSq
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ i.val)
  apply Finset.sum_le_sum
  intro w _
  rw [mapTorusHk_jet_eq_compLp]
  exact pow_le_pow_left₀ (norm_nonneg _) ((L.norm_compLp_le _).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))) 2

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
private theorem lp_norm_sq_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (z : Lp E 2 μ) : ‖z‖ ^ 2 = ∫ x, ‖z x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Parseval for the L² representatives, without a dimension factor. -/
theorem lp_norm_sq_coordinates {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (z : Lp E 2 μ) :
    ∑ i, ‖(innerSL ℝ (b i)).compLpL 2 μ z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp_rw [lp_norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    (Lp.memLp ((innerSL ℝ (b i)).compLpL 2 μ z)).norm.integrable_sq)]
  apply integral_congr_ae
  have hcoord := ae_all_iff.mpr fun i => (innerSL ℝ (b i)).coeFn_compLpL z
  filter_upwards [hcoord] with x hx
  simp_rw [hx]
  exact b.sum_sq_norm_inner_right (z x)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Finite scalar coordinates reconstruct the L² class. -/
theorem lp_coordinates_reconstruct {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (z : Lp E 2 μ) :
    (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ
      ((innerSL ℝ (b i)).compLpL 2 μ z)) = z := by
  apply Lp.ext
  have hc := ae_all_iff.mpr fun i => (innerSL ℝ (b i)).coeFn_compLpL z
  have he := ae_all_iff.mpr fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
      ((innerSL ℝ (b i)).compLpL 2 μ z)
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset ι) (fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ
      ((innerSL ℝ (b i)).compLpL 2 μ z)), hc, he] with x hs hx hy
  rw [hs]
  simp_rw [hy, hx]
  exact b.sum_repr' (z x)

/-- Parseval for the factorial norm of all ordered jets. -/
theorem factorialNormSq_coordinates {K : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (ρ : ℝ) (z : TorusHk K E) :
    ∑ i, factorialNormSq ρ (mapTorusHk (innerSL ℝ (b i)) z).val =
      factorialNormSq ρ z.val := by
  unfold factorialNormSq derivativeNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [mapTorusHk_jet_eq_compLp]
  exact lp_norm_sq_coordinates _ b _

/-- Parseval also holds for every shifted ordered derivative norm. -/
theorem derivFactorialNormSq_coordinates {K : ℕ} (j : ℕ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (ρ : ℝ) (z : TorusHk (K + j) E) :
    ∑ i, derivFactorialNormSq j ρ (mapTorusHk (innerSL ℝ (b i)) z).val =
      derivFactorialNormSq j ρ z.val := by
  unfold derivFactorialNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [mapTorusHk_jet_eq_compLp]
  exact lp_norm_sq_coordinates _ b _
end

/-! A nontrivial real Hilbert fiber certifies the scalar convolution bound, with
exactly the same width and regularizer constants. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Transfer through a contractive Hilbert retraction of the fiber. -/
theorem kernel_regularizer_of_contractive_retract
    (L : E →L[ℝ] F) (I : F →L[ℝ] E) (hLI : L.comp I = ContinuousLinearMap.id ℝ F)
    (hL : ‖L‖ ≤ 1) (hI : ‖I‖ ≤ 1)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec)
    {ρ a b : ℝ} {k Dm : ℕ} {c : ℕ → ℝ}
    (hS : IsSpatialRegularizerTorus (G := E) ρ k Dm a b c S.width (S.op φ₀ hφ₀)) :
    IsSpatialRegularizerTorus (G := F) ρ k Dm a b c S.width (S.op φ₀ hφ₀) := by
  have hround (z : Lp F 2 (volume.restrict AVenhance.unitCube)) :
      L.compLpL 2 _ (I.compLpL 2 _ z) = z := by
    rw [lp_fiberMap_comp, hLI]
    apply Lp.ext
    exact (ContinuousLinearMap.id ℝ F).coeFn_compLpL z
  refine ⟨?_, fun t _ z => kernelSpec_commutes_first_derivatives φ₀ hφ₀ S t z, hS.2.2.1, ?_⟩
  · intro z
    have hm := (L.compLpL 2 (volume.restrict AVenhance.unitCube)).continuous.comp_stronglyMeasurable
      (hS.1 (I.compLpL 2 _ z))
    have heq : (fun t : Set.Icc a b => L.compLpL 2 _ (S.op φ₀ hφ₀ t (I.compLpL 2 _ z))) =
        (fun t : Set.Icc a b => S.op φ₀ hφ₀ t z) := by
      funext t
      rw [kernelSpec_op_fiberMap, hround]
    exact heq ▸ hm
  · intro t ht j hj z
    obtain ⟨Y, hY, hbound⟩ := hS.2.2.2 t ht j hj (mapTorusHk I z)
    refine ⟨mapTorusHk L Y, ?_, ?_⟩
    · rw [mapTorusHk_jet_eq_compLp, hY, kernelSpec_op_fiberMap,
        mapTorusHk_jet_eq_compLp, hround]
    · exact (fiberMap_derivFactorialNormSq_le j L hL ρ Y).trans
        (hbound.trans (mul_le_mul_of_nonneg_left
          (fiberMap_factorialNormSq_le I hI ρ z) (sq_nonneg _)))

/-- supplies a unit vector, so the original root certifies the scalar kernel. -/
theorem kernel_regularizer_to_scalar [Nontrivial E]
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (S : KernelSpec)
    {ρ a b : ℝ} {k Dm : ℕ} {c : ℕ → ℝ}
    (hS : IsSpatialRegularizerTorus (G := E) ρ k Dm a b c S.width (S.op φ₀ hφ₀)) :
    IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b c S.width (S.op φ₀ hφ₀) := by
  obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one : (0 : ℝ) ≤ 1)
  refine kernel_regularizer_of_contractive_retract (innerSL ℝ e)
    (ContinuousLinearMap.toSpanSingleton ℝ e) ?_ ?_ ?_ φ₀ hφ₀ S hS
  · ext
    simp [he]
  · rw [innerSL_apply_norm, he]
  · rw [ContinuousLinearMap.norm_toSpanSingleton, he]
end

end AVRegularity.Construction.Preservation.FullLift
end
end
