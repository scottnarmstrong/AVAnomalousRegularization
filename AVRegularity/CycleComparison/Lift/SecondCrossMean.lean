-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
import AVRegularity.CycleComparison.Residual.QuietMean.CellMean

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The full centered inverse source is determined by earlier grades and degrees. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_congr_predecessors (Q : LiftOperatorData ι h D)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (a₀ : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m (α : DerivativeWord2 m) X z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    liftCellSource Q Cc a₀ hh n t = liftCellSource Q Dc a₀ hh n t := by
  have ha := liftA_congr_predecessors Q Cc Dc a₀ hh n hn t he
  have hm := liftMean_congr_predecessors Q Cc Dc a₀ hh n hn t he
  funext X z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc a₀ p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Dc p.1 j) (liftMean Q Dc a₀ p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hm' : liftMean Q Cc a₀ p.2 (n - j) t = liftMean Q Dc a₀ p.2 (n - j) t := by
      apply liftMean_congr_predecessors Q Cc Dc a₀ p.2 (n - j) (by omega) t
      intro r s hrs
      apply he r s
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hr : r < hh
        · exact Or.inl hr
        · exact Or.inr ⟨by omega, by omega⟩
    have hop := liftApply_congr_at_time j (Cc p.1 j) (Dc p.1 j)
      (liftMean Q Cc a₀ p.2 (n - j)) t (he p.1 j (by
        by_cases hlt : p.1 < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩))
    have hin := liftApply_input_congr_at_time j (Dc p.1 j)
      (liftMean Q Cc a₀ p.2 (n - j)) (liftMean Q Dc a₀ p.2 (n - j)) t hm'
    exact congrFun (congrFun (hop.trans hin) X) z
  simp only [liftCellSource, ha, hm, hsum]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Restricting qualitative fast order preserves the same weak inverse equation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_order_mono
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (q r : ℕ) (hr : r ≤ q) (a b : ℝ) (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v q a b c0 g c) :
    IsCellFieldInverse G v r a b c0 g c :=
  ⟨fun t ht => (hc.1 t ht).of_le (by exact_mod_cast hr), hc.2⟩

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Constant real scaling of an actual inverse is recovered directly through its real dual relation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellJetOfField_scaled_dual (l : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E) (r : ℝ) :
    cellJetOfField l (fun t x => r • c t x) = cellJetOfField (r • l) c := by
  funext t a x
  unfold cellJetOfField
  split_ifs with ha
  · have he : (fun y => r • c t y) = r • c t := rfl
    dsimp only
    rw [he, fderiv_const_smul_field]
    simp only [Pi.smul_apply, smul_apply, map_smul, smul_eq_mul]
  · simp only [map_smul, smul_apply, smul_eq_mul]

variable [FiniteDimensional ℝ E]

theorem cellFieldInverse_const_smul (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (sZ : ℕ) (a b : ℝ)
    (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 g c) (r : ℝ) :
    IsCellFieldInverse G v sZ a b (fun x => r • c0 x)
      (fun t x => r • g t x) (fun t x => r • c t x) := by
  refine ⟨fun t ht => (hc.1 t ht).const_smul r, ?_⟩
  intro l
  have hs : (fun t x => ((l (r • g t x) : ℝ) : ℂ)) =
      fun t x => (((r • l) (g t x) : ℝ) : ℂ) := by
    funext t x
    simp only [map_smul, smul_apply, smul_eq_mul]
  have hi : (fun x => ((l (r • c0 x) : ℝ) : ℂ)) =
      fun x => (((r • l) (c0 x) : ℝ) : ℂ) := by
    funext x
    simp only [map_smul, smul_apply, smul_eq_mul]
  simpa only [hs, hi, cellJetOfField_scaled_dual] using hc.2 (r • l)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Exact scalar metric hypotheses used by the transverse Fourier time equation. -/

theorem cellMetric_profile_time_data (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (par : Fin 2) (a b : ℝ) :
    let g := fun t => G t par.rev par.rev
    AEStronglyMeasurable g volume ∧ (∀ t, |g t| ≤ 2) ∧ IntegrableOn g (Icc a b) ∧
      (∀ t, (1 / 2 : ℝ) ≤ g t) := by
  dsimp only
  let g := fun t => G t par.rev par.rev
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hgb (t : ℝ) : |g t| ≤ 2 := cellMetric_entry_bound hG t 0 par.rev par.rev
  have hi : IntegrableOn g (Icc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hgb t
  refine ⟨hgm, hgb, hi, ?_⟩
  intro t
  simpa [basisVec_apply, g] using (hG.2.2.2 t 0 (basisVec par.rev)).1

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite tested lift operators preserve exact fast periodicity of their coefficients. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftApply_periodic (Q : LiftOperatorData ι h D) (sX sZ : ℕ)
    (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (n : ℕ) (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    AVenhance.IsZ2Periodic (liftApply n (Cc hh n) f t X) := by
  rcases hseq with ⟨_, _, _, _, _, hper, _⟩
  intro k z
  funext v
  simp only [liftApply]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  exact congrArg (fun A => A (orderedDerivative α (f t) X u))
    ((hper hh hhh n m α v u t ht).2 X k z)
end

/-! The actual lift recurrence gives a genuine inverse equation for every normalized exponential test. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_normalized_exponential_inverse (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b (fun _ => 0)
      (fun t z => (Real.exp (A X))⁻¹ •
        liftCellSource Q Cc (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z)
      (fun t z => (Real.exp (A X))⁻¹ •
        liftApply n (Cc hh n) (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun Y => Real.exp (A Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN _ hf X
  simpa only [smul_zero] using cellFieldInverse_const_smul _ _ sZ a b
    (fun _ => 0) _ _ hi ((Real.exp (A X))⁻¹)
end

/-! Truncated graded compositions have continuous fast slices for arbitrary coarse inputs. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem tail_composition_term_fast_continuous (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh n r : ℕ) (hhh : hh ≤ H)
    (g : ℕ → ℕ → ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    Continuous (fun z => if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply r (Cc p.1 r) (g p.2 (n - r)) t X z else 0) := by
  split_ifs
  · apply continuous_finsetSum
    intro p hp
    have hq : p.1 ≤ H := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
    exact liftApply_fast_continuous r (Cc p.1 r) (g p.2 (n - r)) t X
      (fun m _ α v u => ((hseq.2.2.2.2.2.1 p.1 hq r m α v u t ht).1.1 X).continuous)
  · exact continuous_const
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Finite scalar calibrations preserve vanishing literal cell averages. -/

section
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fieldCellMean_finset_sum_smul_zero (s : Finset α) (w : α → ℝ)
    (f : α → Vec 2 → E) (hc : ∀ a ∈ s, Continuous (f a))
    (hm : ∀ a ∈ s, fieldCellMean (f a) = 0) :
    fieldCellMean (fun z => ∑ a ∈ s, w a • f a z) = 0 := by
  rw [AVRegularity.fieldCellMean_sum s (f := fun a z => w a • f a z) (fun a ha => continuous_const.smul (hc a ha))]
  apply Finset.sum_eq_zero
  intro a ha
  rw [AVRegularity.fieldCellMean_smul, hm a ha, smul_zero]
end

/-! The second cross mean on the identity lift is the coarse metric divergence. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fieldCellMean_cellB2_independent_divergence (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (f : Vec 2 → E) (hf : ContDiff ℝ 2 f) (X : Vec 2) :
    fieldCellMean (fun z => cellB2 η G t (fun Y _ => f Y) X z) =
      -∑ i : Fin 2, fderiv ℝ (fun Y => η • ∑ j : Fin 2,
        G t Y i j • fderiv ℝ f Y (basisVec j)) X (basisVec i) := by
  have hterm (i j : Fin 2) : ContDiff ℝ 1 (fun Y => G t Y i j • fderiv ℝ f Y (basisVec j)) :=
    (hG i j).smul ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  have he : (fun z => cellB2 η G t (fun Y _ => f Y) X z) =
      fun _ => -(η • ∑ i : Fin 2, ∑ j : Fin 2,
        fderiv ℝ (fun Y => G t Y i j • fderiv ℝ f Y (basisVec j)) X (basisVec i)) := by
    funext z
    rfl
  rw [he, AVRegularity.fieldCellMean_const]
  have hi (i : Fin 2) :
      fderiv ℝ (fun Y => η • ∑ j : Fin 2, G t Y i j • fderiv ℝ f Y (basisVec j)) X (basisVec i) =
        η • ∑ j : Fin 2, fderiv ℝ (fun Y => G t Y i j • fderiv ℝ f Y (basisVec j)) X (basisVec i) := by
    change fderiv ℝ (η • (fun Y => ∑ j : Fin 2, G t Y i j • fderiv ℝ f Y (basisVec j))) X
      (basisVec i) = _
    rw [congrFun (fderiv_const_smul_field η) X]
    change η • fderiv ℝ (fun Y => ∑ j : Fin 2, G t Y i j • fderiv ℝ f Y (basisVec j)) X
      (basisVec i) = _
    rw [fderiv_fun_sum (u := Finset.univ) (fun j _ => (hterm i j).differentiable one_ne_zero X)]
    simp
  simp_rw [hi]
  rw [Finset.smul_sum]
end

end AVRegularity.CycleComparison.Lift
end
