-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleComparison.Residual.CoarseFlux.Time
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.Velocity.IncrementProvider
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVenhance.Infra.Flow.GradientDeviation
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
section
/-! Finite joint coefficient regularity supplies the exact rectangular lift reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftEdges_boxSmooth_of_joint (c lam : ℝ) (edge : ConstituentEdges D h)
    (sX sZ : ℕ) (S T : Set ℝ) (hclock : ∀ t ∈ S, c * t ∈ T)
    (hj : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, ∀ t ∈ T,
      ContDiff ℝ (sX + sZ : ℕ) (Function.uncurry (γ.coeff α t))) :
    ∀ v u d, ∀ γ ∈ liftEdges c lam edge v u d, ∀ α, ∀ t ∈ S,
      IsBoxSmooth sX sZ (γ.coeff α t) := by
  intro v u d γ hγ α t ht
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  apply Weighted.isBoxSmooth_of_joint_contDiff
  exact (hj v u d δ hδ α (c * t) (hclock t ht)).comp
    ((contDiff_fst.const_smul lam).prodMk contDiff_snd)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Value uniqueness propagates the first-derivative commutation to higher carriers. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem commuting_operator_first_derivative
    (S : Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hcomm : ∀ z : TorusHk 1 E, ∃ y : TorusHk 1 E,
      y.val (valueIndex2 1) = S (z.val (valueIndex2 1)) ∧
      ∀ i : Fin 2, y.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
        S (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩))
    {K : ℕ} (x y : TorusHk (K + 1) E)
    (hvalue : y.val (valueIndex2 (K + 1)) = S (x.val (valueIndex2 (K + 1))))
    (i : Fin 2) :
    (derivativeTorusHk (K := K) (r := 1) (fun _ => i) y).val (valueIndex2 K) =
      S ((derivativeTorusHk (K := K) (r := 1) (fun _ => i) x).val (valueIndex2 K)) := by
  have htr : 1 ≤ K + 1 := by omega
  let x1 := truncateTorusHk htr x
  let y1 := truncateTorusHk htr y
  obtain ⟨z1, hz1, hg⟩ := hcomm x1
  have hy1 : y1.val (valueIndex2 1) = S (x1.val (valueIndex2 1)) := hvalue
  have heq : y1 = z1 := TorusHk.ext_value (hy1.trans hz1.symm)
  have hidx : prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K) =
      truncateJetIndex htr (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => i⟩ : JetIndex2 1) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · change Fin.append (fun _ : Fin 1 => i) Fin.elim0 ≍ (fun _ : Fin 1 => i)
      have hw : Fin.append (fun _ : Fin 1 => i) Fin.elim0 = (fun _ : Fin 1 => i) := by
        funext j
        fin_cases j
        rfl
      rw [hw]
  change y.val (prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K)) =
    S (x.val (prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K)))
  rw [hidx]
  change y1.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
    S (x1.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩)
  rw [heq]
  exact hg i

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A zero-order spatial gain propagates to every finite Sobolev order by commutation.
The carrier upgrade reuses the weak-gradient assembly. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem commuting_operator_gain_carrier
    (S : Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (j : ℕ)
    (hzero : ∀ z : TorusHk 0 E, ∃ y : TorusHk j E,
      y.val (valueIndex2 j) = S (z.val (valueIndex2 0)))
    (hcomm : ∀ z : TorusHk 1 E, ∃ y : TorusHk 1 E,
      y.val (valueIndex2 1) = S (z.val (valueIndex2 1)) ∧
      ∀ i : Fin 2, y.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
        S (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩)) :
    ∀ K, ∀ z : TorusHk K E, ∃ y : TorusHk (K + j) E,
      y.val (valueIndex2 (K + j)) = S (z.val (valueIndex2 K)) := by
  intro K
  induction K with
  | zero =>
    rw [Nat.zero_add]
    exact hzero
  | succ K ih =>
    intro z
    have htr : 1 ≤ K + 1 := by omega
    let z1 := truncateTorusHk htr z
    obtain ⟨y1, hy1, hgrad1⟩ := hcomm z1
    have hg : ∀ i : Fin 2, ∃ g : TorusHk (K + j) E,
        g.val (valueIndex2 (K + j)) = S
          ((derivativeTorusHk (K := K) (r := 1) (fun _ => i) z).val (valueIndex2 K)) :=
      fun i => ih (derivativeTorusHk (K := K) (r := 1) (fun _ => i) z)
    choose g hg using hg
    have hsource (i : Fin 2) : z1.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
        (derivativeTorusHk (K := K) (r := 1) (fun _ => i) z).val (valueIndex2 K) := by
      have hidx : truncateJetIndex htr
          (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => i⟩ : JetIndex2 1) =
          prefixJetIndex (fun _ : Fin 1 => i) (valueIndex2 K) := by
        apply Sigma.ext
        · apply Fin.ext
          rfl
        · change (fun _ : Fin 1 => i) ≍ Fin.append (fun _ : Fin 1 => i) Fin.elim0
          have hw : Fin.append (fun _ : Fin 1 => i) Fin.elim0 = (fun _ : Fin 1 => i) := by
            funext j
            fin_cases j
            rfl
          rw [hw]
      change z.val (truncateJetIndex htr _) = z.val (prefixJetIndex _ _)
      rw [hidx]
    obtain ⟨y, hy⟩ := KernelEnergy.exists_torusHk_succ_of_gradient y1 g
      (fun i => (hgrad1 i).trans ((congrArg S (hsource i)).trans (hg i).symm))
    have hval : y.val (valueIndex2 (K + j + 1)) = S (z.val (valueIndex2 (K + 1))) := by
      refine hy.trans (hy1.trans ?_)
      apply congrArg S
      have hidx : truncateJetIndex htr (valueIndex2 1) = valueIndex2 (K + 1) := by
        apply Sigma.ext
        · apply Fin.ext
          rfl
        · rfl
      change z.val (truncateJetIndex htr (valueIndex2 1)) = z.val (valueIndex2 (K + 1))
      rw [hidx]
    rw [Nat.add_right_comm K 1 j]
    exact ⟨y, hval⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The parent drift strain over an enhanced preparation time decays at a positive power. -/
@[expose] public section
open Filter Topology
namespace AVRegularity.Construction.Preservation.FullLift

theorem parent_drift_time_price {α s q : ℝ} {Λ m : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤
      2 ^ (26 : ℕ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := by
  have he := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have ht := (CycleReference.ocTauPP_asymp hα0 hα1 hs0 hs1 hq hΛ (m := m)).2
  calc
    _ ≤ ocA α q Λ (m - 1) *
        (2 ^ (26 : ℕ) * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q)) :=
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg he.le _)
    _ = 2 ^ (26 : ℕ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := by
      unfold ocA
      rw [mul_left_comm, ← Real.rpow_add he]
      congr 2
      ring

theorem parent_drift_time_eventually_small {α s q : ℝ} {Λ : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (C : ℝ) (hC : 0 ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) ≤ η := by
  have hd := (Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hpow := Buffer.preparation_parent_power_tendsto_zero hq.1 hΛ
    (mul_pos (by norm_num : (0 : ℝ) < 2) hd)
  have hlim : Tendsto (fun m : ℕ => (C * 2 ^ (26 : ℕ)) *
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (eventually_le_nhds hη))
  refine ⟨max 2 n, le_max_left _ _, ?_⟩
  intro m hm
  exact (mul_le_mul_of_nonneg_left (parent_drift_time_price hα0 hα1 hs0 hs1 hq hΛ) hC).trans
    (by simpa only [mul_assoc] using hn m ((le_max_right _ _).trans hm))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! First-derivative commutation identifies every ordered weak jet of a spatial operator. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem commuting_operator_jets
    (S : Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hcomm : ∀ z : TorusHk 1 E, ∃ y : TorusHk 1 E,
      y.val (valueIndex2 1) = S (z.val (valueIndex2 1)) ∧
      ∀ i : Fin 2, y.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩ =
        S (z.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => i⟩)) :
    ∀ K, ∀ x y : TorusHk K E,
      y.val (valueIndex2 K) = S (x.val (valueIndex2 K)) →
      ∀ a : JetIndex2 K, y.val a = S (x.val a) := by
  intro K
  induction K with
  | zero =>
    intro x y hv a
    rcases a with ⟨⟨n, hn⟩, w⟩
    have hn0 : n = 0 := by omega
    subst n
    have hw : w = Fin.elim0 := by
      funext i
      exact Fin.elim0 i
    subst w
    exact hv
  | succ K ih =>
    intro x y hv a
    rcases a with ⟨n, w⟩
    cases n using Fin.cases with
    | zero =>
      change DerivativeWord2 0 at w
      have hw : w = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      subst w
      exact hv
    | succ n =>
      change DerivativeWord2 (n.val + 1) at w
      let i : Fin 2 := w 0
      let a : JetIndex2 K := ⟨n, Fin.tail w⟩
      have hh := ih (derivativeTorusHk (K := K) (r := 1) (fun _ => i) x)
        (derivativeTorusHk (K := K) (r := 1) (fun _ => i) y)
        (commuting_operator_first_derivative S hcomm x y hv i) a
      have hidx : prefixJetIndex (fun _ : Fin 1 => i) a =
          (⟨⟨n.val + 1, by omega⟩, w⟩ : JetIndex2 (K + 1)) := by
        apply Sigma.ext
        · apply Fin.ext
          dsimp [prefixJetIndex, a]
          omega
        · change Fin.append (fun _ : Fin 1 => i) (Fin.tail w) ≍ w
          rw [Fin.append_left_eq_cons]
          apply (Fin.heq_fun_iff (by omega)).mpr
          intro t
          change (Fin.cons (w 0) (Fin.tail w)) (Fin.cast _ t) = w ⟨t.val, _⟩
          rw [Fin.cons_self_tail]
          rfl
      change y.val (prefixJetIndex (fun _ : Fin 1 => i) a) =
        S (x.val (prefixJetIndex (fun _ : Fin 1 => i) a)) at hh
      rw [hidx] at hh
      exact hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A tested lift action preserves a common slow translation of its coefficients and input. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.LiftMeanEntrywise
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_slow_translation_invariant (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (T : Vec 2)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ X z v u,
      c m α t (X + T) z v u = c m α t X z v u)
    (hf : ∀ X, f t (X + T) = f t X) (X z : Vec 2) :
    liftApply n c f t (X + T) z = liftApply n c f t X z := by
  have he : (fun Y => f t (Y + T)) = f t := funext hf
  have hd (m : ℕ) (α : DerivativeWord2 m) :
      orderedDerivative α (f t) (X + T) = orderedDerivative α (f t) X := by
    have hb := orderedDerivative_slowShift α (f t) T X
    rw [he] at hb
    exact hb.symm
  funext v
  simp only [liftApply]
  refine Finset.sum_congr rfl fun m hm => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hc m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) α X z v u, hd m α]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The physical input jet density is controlled at exactly its allocated factorial order. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem physical_jet_density_square_le (U : ℕ) (ρ : ℝ) (f : Vec 2 → E) (x : Vec 2) :
    (∑ j ∈ Finset.range (U + 1), ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2 ≤
      ((U + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (U + 1),
        (ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2 := by
  simpa only [Finset.card_range] using sq_sum_le_card_mul_sum_sq
    (s := Finset.range (U + 1)) (f := fun j => ρ ^ j * ‖iteratedFDeriv ℝ j f x‖)

theorem physical_jet_density_aemeasurable (μ : Measure (Vec 2)) (U : ℕ) (ρ : ℝ)
    (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    AEMeasurable (fun x => ∑ j ∈ Finset.range (U + 1),
      ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) μ := by
  apply Finset.aemeasurable_fun_sum
  intro j hj
  have hjU : j ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact aemeasurable_const.mul
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hjU)).norm.aemeasurable

theorem physical_jet_density_energy_le (U : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal
      ((∑ j ∈ Finset.range (U + 1), ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2)) ≤
      ENNReal.ofReal (((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), 2 ^ j * (j.factorial : ℝ) ^ 2) *
        classicalFactorialSq ρ U f := by
  have he (j : ℕ) (x : Vec 2) :
      ENNReal.ofReal ((ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2) =
        ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm j 2,
      ENNReal.ofReal_mul (pow_nonneg hρ.le _), ← enorm_sq_eq_ofReal']
  have hm (j : ℕ) (hj : j ∈ Finset.range (U + 1)) :
      Measurable (fun x => ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2) := by
    have hjU : j ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact measurable_const.mul (((hf.continuous_iteratedFDeriv
      (by exact_mod_cast hjU)).enorm.measurable).pow_const 2)
  have hp (x : Vec 2) :
      ENNReal.ofReal ((∑ j ∈ Finset.range (U + 1), ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2) ≤
        ENNReal.ofReal ((U + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (U + 1),
          ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
    have hb := ENNReal.ofReal_le_ofReal (physical_jet_density_square_le U ρ f x)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg (U + 1)),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg (ρ ^ j * ‖iteratedFDeriv ℝ j f x‖)),
      he] using hb
  apply (lintegral_mono hp).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ hm]
  calc
    _ = ENNReal.ofReal ((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), ENNReal.ofReal (ρ ^ (2 * j)) *
          ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), ENNReal.ofReal (2 ^ j * (j.factorial : ℝ) ^ 2) *
          classicalFactorialSq ρ U f := by
      apply mul_le_mul_right
      exact Finset.sum_le_sum (fun j hj =>
        CoarseFluxBound.lintegral_iteratedFDeriv_sq_le_classicalFactorialSq U j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hf hρ)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)),
        ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg (U + 1))]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Positive physical input jets use the gradient factorial energy with no extra input order. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_physical_jet_density_square_le (U : ℕ) (ρ : ℝ) (f : Vec 2 → E) (x : Vec 2) :
    (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
      ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2 ≤
      ((U + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (U + 1),
        (if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2 := by
  simpa only [Finset.card_range] using sq_sum_le_card_mul_sum_sq
    (s := Finset.range (U + 1))
    (f := fun j => if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖)

theorem positive_physical_jet_energy_sum_le (U : ℕ) (hU : 1 ≤ U)
    {ρ : ℝ} (hρ : 0 < ρ) (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
      ENNReal.ofReal (ρ ^ (2 * j)) *
        ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        2 ^ j * ((j - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
        classicalGradFactorialSq ρ (U - 1) f := by
  have hf' : ContDiff ℝ (((U - 1 + 1 : ℕ) : ℕ∞)) f := by
    simpa only [Nat.sub_add_cancel hU] using hf
  calc
    _ ≤ ∑ j ∈ Finset.range (U + 1),
        (if j = 0 then 0 else ENNReal.ofReal
          (2 ^ j * ((j - 1).factorial : ℝ) ^ 2 * ρ ^ 2)) *
          classicalGradFactorialSq ρ (U - 1) f := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · simp only [hj0, ite_eq_left, zero_mul, le_refl]
      · simp only [ite_eq_right hj0]
        exact lintegral_iteratedFDeriv_sq_le_classicalGradFactorialSq (U - 1) j
          (by omega) (by have := Finset.mem_range.mp hj; omega) hf' hρ
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by
        split_ifs <;> positivity)]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · exact ENNReal.ofReal_zero.symm
      · rfl

theorem positive_physical_jet_density_energy_le (U : ℕ) (hU : 1 ≤ U)
    {ρ : ℝ} (hρ : 0 < ρ) (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal
      ((∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2)) ≤
      ENNReal.ofReal (((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
          2 ^ j * ((j - 1).factorial : ℝ) ^ 2 * ρ ^ 2) *
        classicalGradFactorialSq ρ (U - 1) f := by
  have he (j : ℕ) (x : Vec 2) :
      ENNReal.ofReal ((if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2) =
        if j = 0 then 0 else
          ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
    by_cases hj : j = 0
    · simp only [ite_eq_left hj, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
    · simp only [ite_eq_right hj]
      rw [mul_pow, ← pow_mul, Nat.mul_comm j 2,
        ENNReal.ofReal_mul (pow_nonneg hρ.le _), ← enorm_sq_eq_ofReal']
  have hm (j : ℕ) (hj : j ∈ Finset.range (U + 1)) :
      Measurable (fun x => if j = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2) := by
    by_cases hj0 : j = 0
    · simp only [ite_eq_left hj0]
      exact measurable_const
    · simp only [ite_eq_right hj0]
      have hjU : j ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact measurable_const.mul (((hf.continuous_iteratedFDeriv
        (by exact_mod_cast hjU)).enorm.measurable).pow_const 2)
  have hp (x : Vec 2) :
      ENNReal.ofReal ((∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) ^ 2) ≤
      ENNReal.ofReal ((U + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (U + 1),
        if j = 0 then 0 else ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
    have hb := ENNReal.ofReal_le_ofReal (positive_physical_jet_density_square_le U ρ f x)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg (U + 1)),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg
        (if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖)), he] using hb
  apply (lintegral_mono hp).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ hm]
  have hi (j : ℕ) :
      (∫⁻ x in AVenhance.unitCube, if j = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2) =
      if j = 0 then 0 else ENNReal.ofReal (ρ ^ (2 * j)) *
        ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j f x‖ₑ ^ 2 := by
    by_cases hj : j = 0
    · simp only [ite_eq_left hj, lintegral_zero]
    · simp only [ite_eq_right hj]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hi]
  exact (mul_le_mul_right (positive_physical_jet_energy_sum_le U hU hρ f hf) _).trans_eq
    (by rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg (U + 1))])

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Removing one radius power from the positive physical density gives gradient factorial energy. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem physical_gradient_density_aemeasurable (μ : Measure (Vec 2)) (U : ℕ) (ρ : ℝ)
    (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    AEMeasurable (fun x => ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
      ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖) μ := by
  apply Finset.aemeasurable_fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · simp only [ite_eq_left hj0]
    exact aemeasurable_const
  · simp only [ite_eq_right hj0]
    exact aemeasurable_const.mul
      (hf.continuous_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).norm.aemeasurable

theorem physical_gradient_density_energy_le (U : ℕ) (hU : 1 ≤ U)
    {ρ : ℝ} (hρ : 0 < ρ) (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f) :
    (∫⁻ x in AVenhance.unitCube, ENNReal.ofReal
      ((∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖) ^ 2)) ≤
      ENNReal.ofReal (((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
          2 ^ j * ((j - 1).factorial : ℝ) ^ 2) *
        classicalGradFactorialSq ρ (U - 1) f := by
  have hfactor (x : Vec 2) :
      (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) =
      ρ * (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = 0
    · simp only [ite_eq_left hj, mul_zero]
    · simp only [ite_eq_right hj]
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)]
  have hb := positive_physical_jet_density_energy_le U hU hρ f hf
  simp_rw [hfactor, mul_pow, ENNReal.ofReal_mul (sq_nonneg ρ)] at hb
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hb
  have hconst : ((U + 1 : ℕ) : ℝ) *
      (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        2 ^ j * ((j - 1).factorial : ℝ) ^ 2 * ρ ^ 2) =
      ρ ^ 2 * (((U + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
          2 ^ j * ((j - 1).factorial : ℝ) ^ 2) := by
    have he (j : ℕ) : (if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2 * ρ ^ 2) =
        (if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2) * ρ ^ 2 := by
      split_ifs <;> simp only [zero_mul]
    simp_rw [he]
    rw [← Finset.sum_mul]
    ring
  rw [hconst, ENNReal.ofReal_mul (sq_nonneg ρ), mul_assoc] at hb
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hρ))
    ENNReal.ofReal_ne_top).mp hb

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Enlarge regularizer constants when combining incoming and fresh kernel certificates. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatial_regularizer_constants_mono
    {ρ a b r : ℝ} {k D : ℕ} {c C : ℕ → ℝ}
    {S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube)}
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S) (hr : 0 ≤ r)
    (hc : ∀ j, j + 2 ≤ D → c j ≤ C j) :
    IsSpatialRegularizerTorus ρ k D a b C r S := by
  refine ⟨hS.1, hS.2.1, fun j hj => (hS.2.2.1 j hj).trans (hc j hj), ?_⟩
  intro t ht j hj z
  obtain ⟨Y, hY, hbound⟩ := hS.2.2.2 t ht j hj z
  refine ⟨Y, hY, hbound.trans ?_⟩
  have hdiv : c j / r ^ j ≤ C j / r ^ j :=
    div_le_div_of_nonneg_right (hc j hj) (pow_nonneg hr j)
  have hnonneg : 0 ≤ c j / r ^ j :=
    div_nonneg (hS.2.2.1 j hj) (pow_nonneg hr j)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnonneg hdiv 2)
    (factorialNormSq_nonneg ρ z.val)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Move a positive component mass diagonal inside the time supremum and lower integral. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_weighted_components {K : ℕ} (ρ ν a b : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i)) :
    strongEnergy ρ ν π a b u w =
      (∑ i, ((⨆ t ∈ Set.Icc a b,
        (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
        ENNReal.ofReal ν * (∫⁻ t in Set.Icc a b,
          (ENNReal.ofReal (π i))⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (w i t).val)))) ^
        (1 / 2 : ℝ) := by
  unfold strongEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hfinite : (ENNReal.ofReal (π i))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (hπ i)))
  rw [ENNReal.ofReal_inv_of_pos (hπ i), mul_add, ENNReal.mul_iSup]
  congr 1
  · simp_rw [ENNReal.mul_iSup]
  · rw [lintegral_const_mul' _ _ hfinite, mul_left_comm]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A chosen classical representative covers every lower requested order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_order_mono {K r s : ℕ} (W : TorusHk K E) (a : Vec 2 → E)
    (hrep : IsClassicalRep W a r) (hsr : s ≤ r) : IsClassicalRep W a s := by
  refine ⟨hsr.trans hrep.1, hrep.2.1.of_le (by exact_mod_cast hsr), hrep.2.2.1, ?_⟩
  intro m hm w
  exact hrep.2.2.2 m (hm.trans hsr) w

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Qualitative Sobolev gains at every order follow from the zero-order regularizer and its
first-derivative commutation. This does not assert higher-order priced energy estimates. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem regularizer_all_order_carrier (ρ : ℝ) (D : ℕ) (a b : ℝ)
    (c : ℕ → ℝ) (r : ℝ)
    (S : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ 0 D a b c r S)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : j + 2 ≤ D) :
    ∀ K, ∀ z : TorusHk K E, ∃ y : TorusHk (K + j) E,
      y.val (valueIndex2 (K + j)) = S t (z.val (valueIndex2 K)) := by
  apply commuting_operator_gain_carrier (S t) j
  · intro z
    obtain ⟨y, hy, _⟩ := hS.2.2.2 t ht j hj z
    have hh : ∃ y : TorusHk (0 + j) E,
        y.val (valueIndex2 (0 + j)) = S t (z.val (valueIndex2 0)) := ⟨y, hy⟩
    rw [Nat.zero_add] at hh
    exact hh
  · exact hS.2.1 t ht

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Entrywise quadratic radius bounds give a stage-independent covariance polynomial price. -/

open CycleComparison.Coarse

theorem covBound_le_four_radius_sq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (C ρ : ℝ)
    (hH : ∀ i j, |Hc i j| ≤ C * ρ ^ 2) : covBound Hc ≤ 4 * C * ρ ^ 2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hH i j
  simpa only [covBound, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num] using hs

theorem fbCovConst_le_of_radius_entries {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ) (K : ℕ)
    (hH : ∀ i j, |Hc i j| ≤ C * ρ ^ 2) :
    fbCovConst ρ Hc K ≤ 4 * C * (K : ℝ) ^ 2 := by
  have hs := mul_le_mul_of_nonneg_right (covBound_le_four_radius_sq Hc C ρ hH)
    (sq_nonneg ((K : ℝ) / ρ))
  change covBound Hc * ((K : ℝ) / ρ) ^ 2 ≤ _
  convert hs using 1
  field_simp

theorem covPolyConst_mono {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (p : ℕ) :
    covPolyConst A p ≤ covPolyConst B p := by
  exact Finset.sum_le_sum fun l _ =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hA hAB l) (Nat.cast_nonneg _)

theorem covPolyConst_le_of_radius_entries {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (C : ℝ) (K p : ℕ)
    (hH : ∀ i j, |Hc i j| ≤ C * ρ ^ 2) :
    covPolyConst (fbCovConst ρ Hc K) p ≤ covPolyConst (4 * C * (K : ℝ) ^ 2) p :=
  covPolyConst_mono (fbCovConst_nonneg hρ Hc K)
    (fbCovConst_le_of_radius_entries hρ Hc C K hH) p

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Spatial words of a convex time-frozen pulse sum cost no pulse-count factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

theorem convex_spatial_word_norm_le (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ 1)
    {r : ℕ} (F : ι → Vec 2 → E)
    (hF : ∀ i ∈ s, w i ≠ 0 → ContDiff ℝ (r : ℕ∞) (F i))
    {rs B : ℝ} (hrs : 0 ≤ rs) (hB : 0 ≤ B) (β : DerivativeWord2 r) (x : Vec 2)
    (hb : ∀ i ∈ s, w i ≠ 0 → rs ^ r * ‖orderedDerivative β (F i) x‖ ≤ B) :
    rs ^ r * ‖orderedDerivative β (fun y => ∑ i ∈ s, w i • F i y) x‖ ≤ B := by
  have hreg (i : ι) (hi : i ∈ s) :
      ContDiff ℝ (r : ℕ∞) (fun y => w i • F i y) := by
    by_cases hwi : w i = 0
    · simp only [hwi, zero_smul]
      exact contDiff_const
    · exact (hF i hi hwi).const_smul (w i)
  rw [MixedTail.orderedDerivative_sum s β hreg]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hrs r)).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ s, w i * B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, zero_smul, orderedDerivative_const_zero, norm_zero, mul_zero, zero_mul, le_refl]
      · rw [CoarseFluxDiff.orderedDerivative_const_smul β (w i) (hF i hi hwi),
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi), mul_left_comm (rs ^ r) (w i)]
        exact mul_le_mul_of_nonneg_left (hb i hi hwi) (hw i hi)
    _ = (∑ i ∈ s, w i) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hB

/-- The actual gluing definition inherits a spatial word bound from active pulses. -/
theorem gluedLift_spatial_word_norm_le
    {κ : Type*} [Fintype κ] {h : κ → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff κ h) (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (v : κ)
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j t) (hs : ∑ j ∈ kset, ϖ j t ≤ 1)
    {r : ℕ}
    (hreg : ∀ j ∈ kset, ϖ j t ≠ 0 → ContDiff ℝ (r : ℕ∞)
      (fun y => pulsePhysicalLift c ρ e εc N H (Cc j) (chart j) (label j) a t y v))
    {rs B : ℝ} (hrs : 0 ≤ rs) (hB : 0 ≤ B) (β : DerivativeWord2 r) (x : Vec 2)
    (hb : ∀ j ∈ kset, ϖ j t ≠ 0 → rs ^ r * ‖orderedDerivative β
      (fun y => pulsePhysicalLift c ρ e εc N H (Cc j) (chart j) (label j) a t y v) x‖ ≤ B) :
    rs ^ r * ‖orderedDerivative β
      (fun y => gluedLift kset ϖ c ρ e εc N H Cc chart label a t y v) x‖ ≤ B := by
  have he : (fun y => gluedLift kset ϖ c ρ e εc N H Cc chart label a t y v) =
      fun y => ∑ j ∈ kset, ϖ j t • pulsePhysicalLift c ρ e εc N H
        (Cc j) (chart j) (label j) a t y v := by
    funext y
    simp only [gluedLift, Finset.sum_apply, Pi.smul_apply]
  rw [he]
  exact convex_spatial_word_norm_le kset (fun j => ϖ j t) hw hs _ hreg hrs hB β x hb
end

/-! Spatial words of a convex time-frozen pulse sum cost no pulse-count factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

theorem convex_weighted_spatial_word_norm_le (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ 1)
    {r : ℕ} (F : ι → Vec 2 → E)
    (hF : ∀ i ∈ s, w i ≠ 0 → ContDiff ℝ (r : ℕ∞) (F i))
    {weight B : ℝ} (hweight : 0 ≤ weight) (hB : 0 ≤ B) (β : DerivativeWord2 r) (x : Vec 2)
    (hb : ∀ i ∈ s, w i ≠ 0 → weight * ‖orderedDerivative β (F i) x‖ ≤ B) :
    weight * ‖orderedDerivative β (fun y => ∑ i ∈ s, w i • F i y) x‖ ≤ B := by
  have hreg (i : ι) (hi : i ∈ s) :
      ContDiff ℝ (r : ℕ∞) (fun y => w i • F i y) := by
    by_cases hwi : w i = 0
    · simp only [hwi, zero_smul]
      exact contDiff_const
    · exact (hF i hi hwi).const_smul (w i)
  rw [MixedTail.orderedDerivative_sum s β hreg]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hweight).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ s, w i * B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwi : w i = 0
      · simp only [hwi, zero_smul, orderedDerivative_const_zero, norm_zero, mul_zero, zero_mul, le_refl]
      · rw [CoarseFluxDiff.orderedDerivative_const_smul β (w i) (hF i hi hwi),
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi), mul_left_comm (weight) (w i)]
        exact mul_le_mul_of_nonneg_left (hb i hi hwi) (hw i hi)
    _ = (∑ i ∈ s, w i) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hB

/-- The actual gluing definition inherits a spatial word bound from active pulses. -/
theorem gluedLift_weighted_spatial_word_norm_le
    {κ : Type*} [Fintype κ] {h : κ → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff κ h) (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (v : κ)
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j t) (hs : ∑ j ∈ kset, ϖ j t ≤ 1)
    {r : ℕ}
    (hreg : ∀ j ∈ kset, ϖ j t ≠ 0 → ContDiff ℝ (r : ℕ∞)
      (fun y => pulsePhysicalLift c ρ e εc N H (Cc j) (chart j) (label j) a t y v))
    {weight B : ℝ} (hweight : 0 ≤ weight) (hB : 0 ≤ B) (β : DerivativeWord2 r) (x : Vec 2)
    (hb : ∀ j ∈ kset, ϖ j t ≠ 0 → weight * ‖orderedDerivative β
      (fun y => pulsePhysicalLift c ρ e εc N H (Cc j) (chart j) (label j) a t y v) x‖ ≤ B) :
    weight * ‖orderedDerivative β
      (fun y => gluedLift kset ϖ c ρ e εc N H Cc chart label a t y v) x‖ ≤ B := by
  have he : (fun y => gluedLift kset ϖ c ρ e εc N H Cc chart label a t y v) =
      fun y => ∑ j ∈ kset, ϖ j t • pulsePhysicalLift c ρ e εc N H
        (Cc j) (chart j) (label j) a t y v := by
    funext y
    simp only [gluedLift, Finset.sum_apply, Pi.smul_apply]
  rw [he]
  exact convex_weighted_spatial_word_norm_le kset (fun j => ϖ j t) hw hs _ hreg hweight hB β x hb
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Naturality and exact kernel widths for actual production and retained cascade stages.
The width proof follows the structural tags, including the widest-input quadratic rule. -/

/-- Restriction keeps the three native data and restricts each injective provenance map. -/
theorem stage_restriction_naturality : Assembly.StageRestrictionNaturalityStatement := by
  intro hr _ _ D Dm bw j₀ M G hG S hS
  refine ⟨hG.1, hG.2.1, hG.2.2.1, ?_⟩
  intro v u
  exact hG.2.2.2 ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩

private def lookupKernel (seedK freshK : ℕ → KernelSpec) : KernelKey → KernelSpec
  | .seed i => seedK i
  | .fresh i => freshK i

section OneStep
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Each source's kernel and width come from the same old tag or the same fresh birth. -/
theorem succSource_kernel_width_matching (G : GenStage D hr Dm bw j₀) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec)
    (hold : ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = ((G.prov v u γ).tags P).width)
    (hfresh : (freshK (G.level - 1)).width = P.rb (G.level - 1)) (s : SuccSource G) :
    (match ((s.prov G.level).tags P).kernel with
      | .seed i => seedK i
      | .fresh i => freshK i).width = ((s.prov G.level).tags P).width := by
  have hpath {h : ℕ} (π : StagePath G h) (tw : ProvTags)
      (htw : tw ∈ Prov.pathTags P π.provList) :
      (lookupKernel seedK freshK tw.kernel).width = tw.width := by
    rw [Providers.CascadeInvariants.pathTags_eq_map] at htw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp htw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hold _ _ _
  cases s with
  | copyDir _ v u γ =>
    cases hk : ((G.prov v u γ).tags P).kernel <;>
      simpa only [SuccSource.prov, Prov.tags, GenStage.kernelOf, hk] using hold v u γ
  | copyQuad _ _ π =>
    cases hw : widestTags (Prov.pathTags P π.provList) with
    | none => simpa only [SuccSource.prov, Prov.tags, hw, lookupKernel] using hfresh
    | some tw =>
      cases hk : tw.kernel <;>
        simpa only [SuccSource.prov, Prov.tags, hw, lookupKernel, hk] using
          hpath π tw (widestTags_mem hw)
  | letterDiag _ _ => simpa only [SuccSource.prov, Prov.tags, lookupKernel] using hfresh
  | letterMean _ _ _ _ => simpa only [SuccSource.prov, Prov.tags, lookupKernel] using hfresh
  | letterCov _ _ _ _ _ _ => simpa only [SuccSource.prov, Prov.tags, lookupKernel] using hfresh

end OneStep

/-- One actual successor preserves the width identification, including every newly born kernel. -/
theorem actual_successor_kernel_width_matching : Assembly.ActualSuccessorKernelWidthStatement := by
  intro hr _ _ D Dm bw j₀ P Mn seedK freshK G G' ht hw hf hs
  have ht' : G'.HasTags P := hs.2.2.2.2.1
  have hold : ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = ((G.prov v u γ).tags P).width := by
    intro v u γ
    exact (hw v u γ).trans (ht v u γ).1.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, e, _Cc, _Cc0, _, _, hall⟩ := hs
  intro v u γ
  have htag : (lookupKernel seedK freshK ((G'.prov v u γ).tags P).kernel).width =
      ((G'.prov v u γ).tags P).width := by
    rw [(hall v u γ).1]
    exact succSource_kernel_width_matching G P seedK freshK hold hf (e v u γ).1
  exact htag.trans (ht' v u γ).1.2.2.2.2.1.symm

section Cascade
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Width identification survives all retained steps; fresh hypotheses are needed only in the
birth band between the final stage and the seed. -/
theorem cascade_kernel_width_matching (P : ProvParams) (Mn : SuccMenu)
    (seed G : GenStage D hr Dm bw j₀) (hc : IsCascadeStage D P Mn seed G)
    (seedK freshK : ℕ → KernelSpec) (ht : seed.HasTags P)
    (hw : ∀ v u (γ : seed.fam.Γ v u),
      (seed.kernelOf P seedK freshK v u γ).width = (seed.fam.identity v u γ).record.width)
    (m₀ : ℕ) (hf : ∀ b, m₀ ≤ b → b < seed.level → (freshK b).width = P.rb b)
    (hlevel : m₀ ≤ G.level) :
    ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width := by
  induction hc with
  | seed => exact hw
  | @step G G' hc hs ih =>
    have hlevel' : m₀ ≤ G'.level := hlevel
    have hGlevel : G'.level = G.level - 1 := hs.2.1
    have hold := ih (by omega : m₀ ≤ G.level)
    have hfresh : (freshK (G.level - 1)).width = P.rb (G.level - 1) := hf _ (by omega) (by
      have hseedlevel := Providers.CascadeInvariants.level_le_of_cascade hc
      have hpos := hs.1
      omega)
    have hnext := actual_successor_kernel_width_matching hr D Dm bw j₀ P Mn seedK freshK G G'
      (Providers.CascadeInvariants.hasTags_of_cascade ht hc) hold hfresh hs
    intro v u γ
    exact hnext ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩ ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩ γ

/-- Closed assembly of the two requested retained structural certificates. -/
theorem retained_structural_certificates
    (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (G G' : GenStage D hr Dm bw j₀) (ht : G.HasTags P)
    (hw : ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width)
    (hf : (freshK (G.level - 1)).width = P.rb (G.level - 1))
    (hs : IsActualSuccessor D P Mn G G') (m H J : ℕ) :
    (G'.retained m H J).IsNatural Mn.M ∧
    ∀ v u (γ : (G'.retained m H J).fam.Γ v u),
      ((G'.retained m H J).kernelOf P seedK freshK v u γ).width =
        ((G'.retained m H J).fam.identity v u γ).record.width := by
  apply Assembly.retained_structural_certificates_of_ingredients
    stage_restriction_naturality actual_successor_kernel_width_matching P Mn seedK freshK G G' ht hw hf hs

end Cascade

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual OC stream has a quantitative first-derivative deviation from the identity. -/

open AVRegularity.Construction.Preservation.Buffer

theorem actual_stream_flow_derivative_deviation
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m)
    (s₀ t : ℝ) (hsmall : (1048576 * ocA α q Λ m) * |t - s₀| ≤ 1) (x : Vec 2) :
    ‖fderiv ℝ (fun y => AVRegularity.streamFlow (Φ m)
      (Velocity.streamSeq_admissible hζ hΛ hΦ m) t y s₀) x - 1‖ ≤
        2 * (1048576 * ocA α q Λ m) * |t - s₀| := by
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  exact Infra.Flow.flow_fderiv_deviation_of_small_time
    (Infra.Construction.smoothPeriodic_streamVel (Velocity.streamSeq_admissible hζ hΛ hΦ m))
    (StrainPhysical.isFlow_stream (Velocity.streamSeq_admissible hζ hΛ hΦ m))
    (mul_nonneg (by norm_num) ha.le)
    (actual_stream_spatial_derivative_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm)
    s₀ t x hsmall

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native lift action retains one fixed positive matrix and the local input jet density.

Reuse the finite-word action estimate at unit grading scale; the actual slow
scale is at most one, so its coefficient powers can be discarded for this energy bound. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- Coordinate words are contractions of the reserved mixed multilinear jet. -/
theorem norm_mixed_orderedDerivative_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth p q f) (α : DerivativeWord2 p) (β : DerivativeWord2 q)
    (X z : Vec 2) :
    ‖orderedDerivative α (fun Y => orderedDerivative β (f Y) z) X‖ ≤
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Vec 2) E
    (fun i => basisVec (β (Fin.rev i)))
  have he : (fun Y => orderedDerivative β (f Y) z) =
      L ∘ (fun Y => iteratedFDeriv ℝ q (f Y) z) := by
    funext Y
    exact congrFun (orderedDerivative_eq_iteratedFDeriv β (hf.1 Y)) z
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro A
    change ‖A (fun i => basisVec (β (Fin.rev i)))‖ ≤ 1 * ‖A‖
    have hvec (i : Fin q) : ‖basisVec (β (Fin.rev i))‖ = 1 := by
      simp only [basisVec, Pi.norm_single, norm_one]
    simpa only [hvec, Finset.prod_const_one, mul_one, one_mul] using
      A.le_opNorm (fun i => basisVec (β (Fin.rev i)))
  have hs : ContDiff ℝ (p : ℕ∞) (fun Y => orderedDerivative β (f Y) z) := by
    rw [he]
    exact L.contDiff.comp (hf.2.1 q le_rfl z)
  apply (norm_orderedDerivative_le hs α X).trans
  rw [he]
  exact (L.norm_iteratedFDeriv_comp_left (hf.2.1 q le_rfl z).contDiffAt le_rfl).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

theorem ambient_liftApply_mixed_pointwise_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => liftApply n c (fun _ => g) t Y y v) z) X‖ ≤
      finiteLiftWordCount n * 2 ^ (p + 2 * q) *
        (∑ u, M v u * ∑ j : Fin (p + n + 1),
          ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖) := by
  let C : ι → ℝ := fun u => ∑ j : Fin (p + n + 1),
    ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖
  have hC (u : ι) : 0 ≤ C u := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u : ι)
      (r : ℕ) (hr : r ≤ p) (s : ℕ) (hs : s ≤ q) (y : Vec 2) :
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun w => c m α t Y w v u) y) X‖ ≤ M v u * (1 : ℝ) ^ (n - m + r) := by
    rw [one_pow, mul_one]
    exact (data.bound m hm α v u r hr s hs t ht X y).trans
      (mul_le_of_le_one_right (data.nonneg v u) (pow_le_one₀ hlam hlam1))
  have hg' (u : ι) (r : ℕ) (hr : r ≤ p + n) :
      ‖iteratedFDeriv ℝ r (fun Y => g Y u) X‖ ≤ C u * (1 : ℝ) ^ (0 + r) := by
    rw [one_pow, mul_one]
    exact Finset.single_le_sum (fun (j : Fin (p + n + 1)) _ => norm_nonneg
      (iteratedFDeriv ℝ j.1 (fun Y => g Y u) X))
      (Finset.mem_univ (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (p + n + 1)))
  have hb := liftApply_slow_input_matrix_grading n p q 0 c g t X z v hg
    (fun m hm α u => data.box m hm α v u t ht) 1 zero_le_one
    (M v) C (data.nonneg v) hC hc hg'
  simpa only [one_pow, mul_one, C] using hb

/-- Positive lift terms annihilate constants, so their dissipative estimate can retain a field derivative. -/
theorem liftApply_sub_constant_of_zero_order (n : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (n : ℕ∞) g)
    (t : ℝ) (c₀ : ∀ i, h i)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, c 0 α t X z v u = 0) :
    liftApply n c (fun _ Y => g Y - c₀) t = liftApply n c (fun _ => g) t := by
  rw [liftApply_input_sub_at_time n c (fun _ => g) (fun _ _ => c₀) t hg contDiff_const]
  funext X z v
  change liftApply n c (fun _ => g) t X z v -
    liftApply n c (fun _ _ => c₀) t X z v = _
  rw [liftApply_const]
  simp only [hzero, zero_apply, Finset.sum_const_zero,
    sub_zero]

/-- The positive action uses only positive input derivatives, as required by coarse dissipation. -/
theorem ambient_positive_liftApply_mixed_pointwise_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, c 0 α t X z v u = 0)
    (X z : Vec 2) (v : ι) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => liftApply n c (fun _ => g) t Y y v) z) X‖ ≤
      finiteLiftWordCount n * 2 ^ (p + 2 * q) *
        (∑ u, M v u * ∑ j : Fin (p + n + 1),
          if j.1 = 0 then 0 else ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖) := by
  let g' : Vec 2 → ∀ i, h i := fun Y => g Y - g X
  have he := liftApply_sub_constant_of_zero_order n c g
    (hg.of_le (by exact_mod_cast Nat.le_add_left n p)) t (g X) hzero
  have hb := ambient_liftApply_mixed_pointwise_le data hlam hlam1 g'
    (hg.sub contDiff_const) t ht X z v
  change liftApply n c (fun _ => g') t = liftApply n c (fun _ => g) t at he
  rw [he] at hb
  have hj (u : ι) (j : Fin (p + n + 1)) :
      ‖iteratedFDeriv ℝ j.1 (fun Y => g' Y u) X‖ =
        if j.1 = 0 then 0 else ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖ := by
    by_cases hj0 : j.1 = 0
    · rw [ite_eq_left hj0, hj0, norm_iteratedFDeriv_zero]
      change ‖g X u - g X u‖ = 0
      rw [sub_self, norm_zero]
    · rw [ite_eq_right hj0]
      have hgu : ContDiff ℝ (j.1 : ℕ∞) (fun Y => g Y u) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hg).of_le
          (by exact_mod_cast Nat.le_of_lt_succ j.2)
      change ‖iteratedFDeriv ℝ j.1
        ((fun Y => g Y u) - (fun _ => g X u)) X‖ = _
      rw [iteratedFDeriv_sub_apply hgu.contDiffAt contDiffAt_const,
        iteratedFDeriv_const_of_ne hj0]
      simp only [Pi.zero_apply, sub_zero]
  simpa only [hj] using hb

end AVRegularity.Construction.Preservation.FullLift
end
end
