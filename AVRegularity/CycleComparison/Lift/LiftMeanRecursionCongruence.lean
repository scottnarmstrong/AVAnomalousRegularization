-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.Statements.Intermediate.CycleComparison.CellJetOfField
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleComparison.Lift

/-! Joint classical profile jets are measurable on the actual product cell window. -/

theorem classicalProfileJet_joint_aestronglyMeasurable (I : Set ℝ) (hI : MeasurableSet I)
    (c : ℝ → ℝ → ℂ) (p : Fin 2) (hf : ∀ t ∈ I, Differentiable ℝ (c t))
    (hc : ContinuousOn (Function.uncurry c) (I ×ˢ (Set.univ : Set ℝ)))
    (hd : ContinuousOn (fun x : ℝ × ℝ => deriv (c x.1) x.2)
      (I ×ˢ (Set.univ : Set ℝ))) (a : JetIndex2 1) :
    AEStronglyMeasurable (fun x : ℝ × Vec 2 => classicalCellJet (fun z => c x.1 (z p)) a x.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  rw [Measure.prod_restrict]
  have hj := classicalProfileJet_joint_continuousOn I c p hf hc hd a
  apply (hj.mono (fun _ hx => ⟨hx.1, mem_univ _⟩)).aestronglyMeasurable
  exact hI.prod AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The lift setting supplies the local admissibility needed by the actual cell inverse. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_cell_metric (X : Vec 2) :
    IsCellMetric (localCellMetric a b P.window (fun t => Matrix.of (Q.G t X))) := by
  apply localCellMetric_admissible
  · intro i j
    exact P.G_meas X i j
  · intro t ht
    ext i j
    exact P.G_symm t X j i
  · intro t ht ξ
    have hh := P.G_ellip t ht X ξ
    simpa only [Matrix.of_apply, mul_assoc, mul_left_comm, mul_comm] using hh

include P in
theorem setting_drift_continuous : ∀ t ∈ Set.Icc a b, Continuous (Q.v t) := by
  intro t ht
  have he : Q.v t = fun z => V t (z par.rev) • basisVec par := funext (P.v_shear t)
  rw [he]
  exact ((P.V_smooth t ht).continuous.comp (continuous_apply par.rev)).smul continuous_const

include P in
theorem setting_eta_pos : 0 < Q.η := by
  rw [P.η_eq]
  exact div_pos P.ν_pos P.B_pos

include P in
theorem setting_normalized_drift_bound (t : ℝ) (ht : t ∈ Set.Icc a b) (z : Vec 2) :
    ‖Real.sqrt Q.η • Q.v t z‖ ≤ max (Cw 0) 0 := by
  have hh := (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le z le_rfl))).trans
    (P.w_jets 0 (by omega))
  have hn : ENNReal.ofReal ‖Real.sqrt Q.η • Q.v t z‖ ≤ ENNReal.ofReal (max (Cw 0) 0) := by
    calc
      _ = ‖iteratedFDeriv ℝ 0 (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ := by
        rw [← ofReal_norm, norm_iteratedFDeriv_zero]
      _ ≤ ENNReal.ofReal (Cw 0) := hh
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp hn

include P in
theorem setting_drift_bound : ∃ W : ℝ, ∀ t ∈ Set.Icc a b, ∀ z,
    ∑ i, Q.v t z i ^ 2 ≤ W ^ 2 := by
  let M := max (Cw 0) 0
  let R := M / Real.sqrt Q.η
  have hs : 0 < Real.sqrt Q.η := Real.sqrt_pos.mpr (setting_eta_pos P)
  have hR : 0 ≤ R := div_nonneg (le_max_right _ _) hs.le
  refine ⟨2 * R, ?_⟩
  intro t ht z
  have hv : ‖Q.v t z‖ ≤ R := by
    apply (le_div_iff₀ hs).mpr
    have hh := setting_normalized_drift_bound P t ht z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hh
    simpa only [mul_comm] using hh
  have hi (i : Fin 2) : Q.v t z i ^ 2 ≤ R ^ 2 := by
    have habs : |Q.v t z i| ≤ R := (norm_le_pi_norm (Q.v t z) i).trans hv
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr habs
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
  nlinarith [sq_nonneg R]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! At zero cell parameter, covariant words are precisely the ordered fast derivatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dEpsWord_zero_parameter (η : ℝ) {m : ℕ} (α : DerivativeWord2 m)
    (Φ : Vec 2 → Vec 2 → E) (X : Vec 2) :
    dEpsWord η 0 α Φ X = orderedDerivative α (Φ X) := by
  have he : ∀ (l : List (Fin 2)) (Ψ : Vec 2 → Vec 2 → E),
      (l.foldl (fun Ψ' i => dEps η 0 i Ψ') Ψ) X =
        l.foldl (fun g i => fun z => fderiv ℝ g z (basisVec i)) (Ψ X) := by
    intro l
    induction l with
    | nil => intro Ψ; rfl
    | cons i l ih =>
      intro Ψ
      simp only [List.foldl_cons]
      rw [ih]
      have h0 : dEps η 0 i Ψ X = fun z => fderiv ℝ (Ψ X) z (basisVec i) := by
        funext z
        simp [dEps, fastPartial]
      rw [h0]
  exact he (List.ofFn α) Φ

theorem orderedDerivative_contDiff {m : ℕ} (α : DerivativeWord2 m)
    (r : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ ((r + m : ℕ) : ℕ∞) f) :
    ContDiff ℝ (r : ℕ∞) (orderedDerivative α f) := by
  have he : ∀ (l : List (Fin 2)) (g : Vec 2 → E),
      ContDiff ℝ ((r + l.length : ℕ) : ℕ∞) g →
        ContDiff ℝ (r : ℕ∞)
          (l.foldl (fun g' i => fun z => fderiv ℝ g' z (basisVec i)) g) := by
    intro l
    induction l with
    | nil => intro g hg; simpa using hg
    | cons i l ih =>
      intro g hg
      rw [List.foldl_cons]
      apply ih
      apply (hg.fderiv_right (m := ((r + l.length : ℕ) : ℕ∞)) (by exact_mod_cast (show r + l.length + 1 ≤ r + (i :: l).length by simp [Nat.add_assoc]))).clm_apply
      exact contDiff_const
  apply he
  simpa only [List.length_ofFn] using hf

theorem orderedDerivative_periodic {m : ℕ} (α : DerivativeWord2 m)
    (f : Vec 2 → E) (hf : ContDiff ℝ (m : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (orderedDerivative α f) := by
  have he : ∀ (l : List (Fin 2)) (g : Vec 2 → E),
      ContDiff ℝ (l.length : ℕ∞) g → AVenhance.IsZ2Periodic g →
        AVenhance.IsZ2Periodic
          (l.foldl (fun g' i => fun z => fderiv ℝ g' z (basisVec i)) g) := by
    intro l
    induction l with
    | nil => intro g _ hg; exact hg
    | cons i l ih =>
      intro g hg hgp
      rw [List.foldl_cons]
      apply ih
      · apply (hg.fderiv_right (m := (l.length : ℕ∞)) (by simp)).clm_apply contDiff_const
      · have hd := fderiv_isZ2Periodic (hg.differentiable (by simp)) hgp
        intro n z
        exact congrArg (fun A => A (basisVec i)) (hd n z)
  apply he
  · simpa only [List.length_ofFn] using hf
  · exact hp
end

/-! Finite lift terms retain the original coefficient reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftComponentLeftTerms_box (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) (v : ι) (p q : ℕ)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun X z => c m α t X z v u))
    (d : LeftTerm (∀ i, h i) (h v)) (hd : d ∈ liftComponentLeftTerms n c t v) :
    IsBoxSmooth p q d.coeff := by
  obtain ⟨m, hm, α, hα, u, hu, rfl⟩ := by
    simpa only [liftComponentLeftTerms, List.mem_flatMap, List.mem_map] using hd
  have hm' : m ≤ n := by
    have h := Finset.mem_range.mp (Finset.mem_toList.mp hm)
    omega
  exact (hc m hm' α u).clm_comp
    ((ContinuousLinearMap.compL ℝ (∀ i, h i) (h u) (h v)).flip (ContinuousLinearMap.proj u))
end

/-! Classical real-dual jets commute with addition at every differentiable time. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellJetOfField_add_at (l : E →L[ℝ] ℝ) (c d : ℝ → Vec 2 → E)
    (t : ℝ) (hc : Differentiable ℝ (c t)) (hd : Differentiable ℝ (d t)) :
    cellJetOfField l (fun s z => c s z + d s z) t =
      (cellJetOfField l c + cellJetOfField l d) t := by
  funext α x
  simp only [Pi.add_apply]
  unfold cellJetOfField
  split_ifs
  · have he : (fun z => c t z + d t z) = c t + d t := rfl
    dsimp only
    rw [he, fderiv_add (hc x) (hd x)]
    simp only [add_apply, map_add, Complex.ofReal_add]
  · simp only [map_add, Complex.ofReal_add]
end

/-! Complexified real dual jets are exactly the classical jets of their dual fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellJetOfField_eq_classical_at (l : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E)
    (t : ℝ) (hc : Differentiable ℝ (c t)) :
    cellJetOfField l c t = classicalCellJet (fun z => ((l (c t z) : ℝ) : ℂ)) := by
  let A := Complex.ofRealCLM.comp l
  have hd x : fderiv ℝ (fun z => A (c t z)) x = A.comp (fderiv ℝ (c t) x) :=
    (A.hasFDerivAt.comp x (hc x).hasFDerivAt).fderiv
  funext α x
  unfold cellJetOfField classicalCellJet
  split_ifs
  · change ((l (fderiv ℝ (c t) x (basisVec _)) : ℝ) : ℂ) =
      fderiv ℝ (fun z => A (c t z)) x (basisVec _)
    rw [hd]
    rfl
  · rfl

theorem classicalCellJet_const_smul (c : Vec 2 → ℂ) (r : ℝ) :
    classicalCellJet (fun z => r • c z) = r • classicalCellJet c := by
  funext α x
  simp only [Pi.smul_apply]
  unfold classicalCellJet
  split_ifs
  · have he : (fun z => r • c z) = r • c := rfl
    rw [he, fderiv_const_smul_field]
    rfl
  · rfl
end

/-! The recursion source only uses earlier source grades or earlier degrees in the same grade. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_congr_predecessors (Q : LiftOperatorData ι h D)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (a₀ : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m (α : DerivativeWord2 m) X z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    liftA Q Cc a₀ hh n t = liftA Q Dc a₀ hh n t := by
  have hop (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) :
      liftApply q (Cc p q) a₀ t = liftApply q (Dc p q) a₀ t :=
    liftApply_congr_at_time q _ _ a₀ t (he p q hpq)
  have h1 := hop hh (n - 1) (Or.inr ⟨rfl, by omega⟩)
  funext X z
  have h2eq : (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) a₀ t) X z else 0) =
      (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Dc hh (n - 2)) a₀ t) X z else 0) := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      exact congrArg (fun F => cellB2 Q.η Q.G t F X z)
        (hop hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    · simp only [h2, ite_false]
  have hSeq : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a₀ t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Dc (hh - 1) (n - j)) a₀ t) X z) := by
    by_cases h0 : hh = 0
    · simp only [h0, ite_true]
    · simp only [h0, ite_false]
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun F => sourceCoeff Q.edge Q.η j t F X z)
        (hop (hh - 1) (n - j) (Or.inl (by omega)))
  change _ + _ - _ = _ + _ - _
  rw [h1, h2eq, hSeq]
end

/-! Cell averaging preserves the triangular dependence of the recursion source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftMean_congr_predecessors (Q : LiftOperatorData ι h D)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h) (a₀ : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m (α : DerivativeWord2 m) X z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    liftMean Q Cc a₀ hh n t = liftMean Q Dc a₀ hh n t := by
  have ha := liftA_congr_predecessors Q Cc Dc a₀ hh n hn t he
  funext X
  simp only [liftMean, ha]
end

end AVRegularity.CycleComparison.Lift
end
