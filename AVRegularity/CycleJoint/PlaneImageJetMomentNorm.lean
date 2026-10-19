-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneWindowScalarDiffusion
public import AVRegularity.CycleComparison.Lift.ParameterIntegral
import AVRegularity.CycleWords.PlaneFourierDerivativeCriterion
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointModel
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The interval transport operator agrees with positive time normalization on its window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

/-- Time normalization gives the actual normalized velocity operator on the normalized window. -/
theorem planeIntervalTransport_time_normalization {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hvcN : ∀ t ∈ Set.Icc (ν * a) (ν * b), Continuous (ν⁻¹ • v (ν⁻¹ * t)))
    (MN : ℝ) (hvbN : ∀ t ∈ Set.Icc (ν * a) (ν * b), ∀ x,
      ‖(ν⁻¹ • v (ν⁻¹ * t)) x‖ ≤ MN)
    (t : ℝ) (ht : t ∈ Set.Icc (ν * a) (ν * b)) :
    ν⁻¹ • planeIntervalTransport (E := E) a b hab v hvc M hvb (ν⁻¹ * t) =
      planeIntervalTransport (E := E) (ν * a) (ν * b)
        (mul_le_mul_of_nonneg_left hab hν.le) (fun r => ν⁻¹ • v (ν⁻¹ * r))
        hvcN MN hvbN t := by
  have hmem : ν⁻¹ * t ∈ Set.Icc a b := by
    have hd : t / ν ∈ Set.Icc a b :=
      ⟨(le_div_iff₀ hν).2 (by simpa only [mul_comm] using ht.1),
        (div_le_iff₀ hν).2 (by simpa only [mul_comm] using ht.2)⟩
    simpa only [div_eq_mul_inv, mul_comm] using hd
  have hcOld (k : Fin 2) : Continuous (fun x => v (ν⁻¹ * t) x k) :=
    (continuous_apply k).comp (hvc _ hmem)
  have hcNew (k : Fin 2) : Continuous (fun x => (ν⁻¹ • v (ν⁻¹ * t)) x k) :=
    (continuous_apply k).comp (hvcN t ht)
  have hbOld (k : Fin 2) (x : Vec 2) : |v (ν⁻¹ * t) x k| ≤ max M 0 := by
    have h := norm_le_pi_norm (v (ν⁻¹ * t) x) k
    have hcomp : |v (ν⁻¹ * t) x k| ≤ ‖v (ν⁻¹ * t) x‖ := by
      simpa only [Real.norm_eq_abs] using h
    exact hcomp.trans ((hvb _ hmem x).trans (le_max_left M 0))
  have hbNew (k : Fin 2) (x : Vec 2) : |(ν⁻¹ • v (ν⁻¹ * t)) x k| ≤ max MN 0 := by
    have h := norm_le_pi_norm ((ν⁻¹ • v (ν⁻¹ * t)) x) k
    have hcomp : |(ν⁻¹ • v (ν⁻¹ * t)) x k| ≤ ‖(ν⁻¹ • v (ν⁻¹ * t)) x‖ := by
      simpa only [Real.norm_eq_abs] using h
    exact hcomp.trans ((hvbN t ht x).trans (le_max_left MN 0))
  have hOld : planeIntervalTransport (E := E) a b hab v hvc M hvb (ν⁻¹ * t) =
      planeScalarTransport (v (ν⁻¹ * t)) hcOld (le_max_right M 0) hbOld :=
    planeScalarTransport_congr _ _ (planeIntervalCoefficient_of_mem a b hab v (ν⁻¹ * t) hmem)
      _ hcOld (le_max_right M 0) (le_max_right M 0) _ hbOld
  have hNew : planeIntervalTransport (E := E) (ν * a) (ν * b)
      (mul_le_mul_of_nonneg_left hab hν.le) (fun r => ν⁻¹ • v (ν⁻¹ * r))
      hvcN MN hvbN t =
      planeScalarTransport (ν⁻¹ • v (ν⁻¹ * t)) hcNew (le_max_right MN 0) hbNew :=
    planeScalarTransport_congr _ _
      (planeIntervalCoefficient_of_mem (ν * a) (ν * b)
        (mul_le_mul_of_nonneg_left hab hν.le) (fun r => ν⁻¹ • v (ν⁻¹ * r)) t ht)
      _ hcNew (le_max_right MN 0) (le_max_right MN 0) _ hbNew
  rw [hOld, hNew]
  exact (planeScalarTransport_smul ν⁻¹ (v (ν⁻¹ * t)) hcOld hcNew
    (le_max_right M 0) (le_max_right MN 0) hbOld hbNew).symm

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Windowed coefficient bounds and energy time classes supply the genuine native weak dual Bochner class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWindowDual_memLp (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (Mv : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Icc a b, ∀ k j, Continuous (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (MG : ℝ) (hGb : ∀ t ∈ Icc a b, ∀ k j x, |G t x k j| ≤ MG)
    (u : ℝ → PlaneHk univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => planeWeakDualRepresentative
      (planeIntervalTransport a b hab v hvc Mv hvb t)
      (planeWindowScalarDiffusion a b hab G hGc MG hGb t) (u t) (F t))
      2 (volume.restrict (Icc a b)) := by
  dsimp only [planeIntervalTransport, planeWindowScalarDiffusion]
  apply planeScalarDual_memLp
    (planeIntervalCoefficient a b hab v) (planeIntervalCoefficient a b hab G)
    (planeIntervalVelocity_continuous a b hab v hvc)
    (planeIntervalMetric_continuous a b hab G hGc)
  · intro k
    exact (measurable_pi_apply k).comp (planeIntervalCoefficient_measurable a b hab v hvm)
  · intro k j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
      (planeIntervalCoefficient_measurable a b hab G hGm))
  · exact hu
  · exact hF

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleJointProofs

/-! The recursive native differential words agree with the project's stored ordered jet convention. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem listCoordinateDerivative_eq_reverse (I : List (Fin 2)) (g : Vec 2 → E) :
    listCoordinateDerivative I g = orderedListDerivative I.reverse g := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    rw [List.reverse_cons]
    unfold orderedListDerivative
    rw [List.foldl_append]
    change (fun y => fderiv ℝ (listCoordinateDerivative I g) y (basisVec i)) =
      fun y => fderiv ℝ (orderedListDerivative I.reverse g) y (basisVec i)
    rw [ih]

theorem listCoordinateDerivative_eq_ordered {n : ℕ} (A : DerivativeWord2 n)
    (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    listCoordinateDerivative (List.ofFn A) g = orderedDerivative A g := by
  rw [listCoordinateDerivative_eq_reverse]
  exact orderedListDerivative_perm (List.reverse_perm _) g hg

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every literal coefficient-array contribution pairs integrably with localized torus tests. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {K r : ℕ}

theorem torusCoefficientArray_unitPatch_pairings_integrable (i i' : ι)
    (A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hc : Continuous A) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖A x‖ ≤ M)
    (hp : AVenhance.IsZ2Periodic A) (T : TorusHk K (h i'))
    (α : DerivativeWord2 r → JetIndex2 K) (k : Fin 2)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let f := fun x => A x (WithLp.toLp 2 (fun w => T.toFunction.jet (α w) x)) k
    Integrable (fun x => inner ℝ (f x) (ψ.toFunction.jet (valueIndex2 1) x)) volume ∧
      ∀ j : Fin 2, Integrable (fun x => inner ℝ (f x)
        (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => j⟩ x)) volume := by
  dsimp only
  apply periodic_unitPatch_test_pairings_integrable _ _ _ hζ φ
  · apply couplingFlux_component_memLp i i' AVenhance.unitCube A hc M hM hb
    intro w
    exact periodicJetRepresentative_memL2 T.val (α w)
  · intro n x
    change A (x + AVenhance.latticeShift n)
      (WithLp.toLp 2 (fun w => T.toFunction.jet (α w) (x + AVenhance.latticeShift n))) k =
      A x (WithLp.toLp 2 (fun w => T.toFunction.jet (α w) x)) k
    rw [hp n x]
    have he : WithLp.toLp 2 (fun w => T.toFunction.jet (α w) (x + AVenhance.latticeShift n)) =
        WithLp.toLp 2 (fun w => T.toFunction.jet (α w) x) := by
      apply PiLp.ext
      intro w
      exact periodicJetRepresentative_periodic T.val (α w) n x
    rw [he]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Bounded finite scalar jet rows act continuously on actual native plane carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (c : JetIndex2 K → Vec 2 → ℝ) (hc : ∀ a, Continuous (c a))
    (M : JetIndex2 K → ℝ) (hM : ∀ a, 0 ≤ M a) (hb : ∀ a x, |c a x| ≤ M a)

def planeScalarJetRow : PlaneHk univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  ∑ a : JetIndex2 K, (planeScalarMultiplier (c a) (hc a) (hM a) (hb a)).comp
    (univToPlane.toContinuousLinearMap.comp (planeJetComponentCLM a))

omit [FiniteDimensional ℝ E] in
theorem planeScalarJetRow_ae (U : PlaneHk univ K E) :
    (planeScalarJetRow c hc M hM hb U : Vec 2 → E) =ᵐ[volume]
      fun x => ∑ a : JetIndex2 K, c a x • U.toFunction.jet a x := by
  let L (a : JetIndex2 K) : Lp E 2 (volume : Measure (Vec 2)) :=
    planeScalarMultiplier (c a) (hc a) (hM a) (hb a) (univToPlane (U.val a))
  have ha : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      L a x = c a x • U.toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [planeScalarMultiplier_ae (c a) (hc a) (hM a) (hb a)
      (univToPlane (U.val a)), univToPlane_ae (U.val a)] with x hx hj
    exact hx.trans (congrArg (fun e => c a x • e) hj)
  have hr : planeScalarJetRow c hc M hM hb U = ∑ a : JetIndex2 K, L a := by
    simp only [planeScalarJetRow, sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hr]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ L, ha] with x hx ha
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun a _ => ha a))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Coefficient and state layers of the exact native transition recursion. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transitionJetCoefficientLayer (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 2) (I : List (Fin 2)) (r : ℕ) (g : Vec 2 → E) (y : Vec 2) : E :=
  ∑ A : DerivativeWord2 r,
    weightedCoordinateDerivative K i (transitionT K I (List.ofFn A)) y •
      listCoordinateDerivative (List.ofFn A) g y

def transitionJetStateLayer (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 2) (I : List (Fin 2)) (r : ℕ) (g : Vec 2 → E) (y : Vec 2) : E :=
  ∑ a : Fin 2, K y a i •
    (∑ A : DerivativeWord2 r, transitionT K I (List.ofFn A) y •
      listCoordinateDerivative (a :: List.ofFn A) g y)

theorem transitionJetTerm_cons_succ
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2))
    (r : ℕ) (g : Vec 2 → E) (y : Vec 2) :
    transitionJetTerm K (i :: I) (r + 1) g y =
      transitionJetCoefficientLayer K i I (r + 1) g y +
        transitionJetStateLayer K i I r g y := by
  have he := transitionT_cons_flux K i I r
    (fun A => listCoordinateDerivative (List.ofFn A) g y) y
  simpa only [transitionJetTerm, transitionJetCoefficientLayer, transitionJetStateLayer,
    List.ofFn_cons] using he

theorem transitionJetCoefficientLayer_above_order
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2))
    (r : ℕ) (hr : I.length < r) (g : Vec 2 → E) :
    transitionJetCoefficientLayer K i I r g = 0 := by
  funext y
  unfold transitionJetCoefficientLayer
  apply Finset.sum_eq_zero
  intro A hA
  rw [transitionT_zero_above_native_order K I (List.ofFn A) (by simpa using hr)]
  simp [weightedCoordinateDerivative]
end

/-! Positive source-degree block estimates assemble the exact joint model predicate. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Conditional block assembly; the construction must supply the individual operator estimates. -/
theorem isJointModel_of_positive_blocks {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Mout H : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (C Cth Θ E Pacc ρ CP : ℝ) (hC : 0 ≤ C) (hCth : 0 ≤ Cth)
    (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1) (hδ : 0 ≤ 1 + CP * E ^ Pacc)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ Cth * Θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ Cth * Θ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hsupport : ∀ n, 1 ≤ n → n ≤ H → ∀ v u, ¬ HasEdgePath F n u v → Pg n v u = 0)
    (hdiag : ∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤ (1 + CP * E ^ Pacc) * ‖f‖)
    (hdiagJet : ∀ v f, torusHkNorm ρ (le_max_left Mout (K v)) (Pd v f) ≤ C * ‖f‖)
    (hsource : ∀ n, 1 ≤ n → n ≤ H → ∀ v u f,
      torusHkNorm ρ (le_max_left Mout (K v)) (Pg n v u f) ≤ C * (A ^ n) v u * ‖f‖)
    (hdconst : ∀ v c, Pd v (torusConstantCarrier 0 c) = torusConstantCarrier (max Mout (K v)) c)
    (hgconst : ∀ n, 1 ≤ n → n ≤ H → ∀ v u c, Pg n v u (torusConstantCarrier 0 c) = 0) :
    IsJointModel π K Mout H F A Θ E Pacc ρ (jointModelConstant C Cth H) CP Pd Pg := by
  have hCC := le_jointModelConstant C Cth H hC hCth
  refine ⟨hsupport, ?_, ?_, ?_, ?_, ?_⟩
  · intro v f
    simpa only [torusHkNorm_zero_input] using hdiag v f
  · intro v f
    rw [torusHkNorm_zero_input]
    exact (hdiagJet v f).trans (mul_le_mul_of_nonneg_right hCC (norm_nonneg _))
  · intro n hn hnH v u f
    rw [torusHkNorm_zero_input]
    exact (hsource n hn hnH v u f).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC (positiveMatrix_pow_nonneg A hA n v u)) (norm_nonneg _))
  · intro f
    have hb := torusJointOperator_analytic_mass_bound K Mout H π hπ A hA
      (1 + CP * E ^ Pacc) C Cth Θ ρ hδ hC hCth hΘ₀ hΘ₁ hrow hcol Pd Pg hdiag hsource f
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (source_sum_le_jointModelConstant C Cth H hC) hΘ₀)
  · exact torusJointOperator_fixes_constants K Mout H Pd Pg hdconst hgconst
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! A finite Piola combination of genuine jet row operators is a continuous native-to-plane operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (Y : Vec 2 → Vec 2) (hμ : MeasurePreserving Y volume volume)
    (c : Fin 2 → Vec 2 → ℝ) (hc : ∀ i, Continuous (c i))
    (M : Fin 2 → ℝ) (hM : ∀ i, 0 ≤ M i) (hb : ∀ i x, |c i x| ≤ M i)
    (R : Fin 2 → PlaneHk univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))

def planeJetRowPiolaOperator : PlaneHk univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  ∑ i : Fin 2, (planeScalarMultiplier (c i) (hc i) (hM i) (hb i)).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ Y hμ).toContinuousLinearMap.comp (R i))

omit [FiniteDimensional ℝ E] in
theorem planeJetRowPiolaOperator_ae (U : PlaneHk univ K E)
    (f : Fin 2 → Vec 2 → E) (hf : ∀ i, (R i U : Vec 2 → E) =ᵐ[volume] f i) :
    (planeJetRowPiolaOperator Y hμ c hc M hM hb R U : Vec 2 → E) =ᵐ[volume]
      fun x => ∑ i : Fin 2, c i x • f i (Y x) := by
  let L (i : Fin 2) : Lp E 2 (volume : Measure (Vec 2)) :=
    planeScalarMultiplier (c i) (hc i) (hM i) (hb i)
      (Lp.compMeasurePreservingₗᵢ ℝ Y hμ (R i U))
  have ha : ∀ᵐ x ∂volume, ∀ i : Fin 2, L i x = c i x • f i (Y x) := by
    apply ae_all_iff.mpr
    intro i
    have he := (Lp.coeFn_compMeasurePreserving (R i U) hμ).trans
      (hμ.quasiMeasurePreserving.ae_eq_comp (hf i))
    filter_upwards [planeScalarMultiplier_ae (c i) (hc i) (hM i) (hb i)
      (Lp.compMeasurePreservingₗᵢ ℝ Y hμ (R i U)), he] with x hx he
    exact hx.trans (congrArg (fun e => c i x • e) he)
  have hr : planeJetRowPiolaOperator Y hμ c hc M hM hb R U = ∑ i : Fin 2, L i := by
    simp only [planeJetRowPiolaOperator, sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hr]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ L, ha] with x hx ha
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ => ha i))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A bounded native jet row has its literal classical derivative readout on smooth representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarJetRow_smooth_ae {K : ℕ}
    (c : JetIndex2 K → Vec 2 → ℝ) (hc : ∀ a, Continuous (c a))
    (M : JetIndex2 K → ℝ) (hM : ∀ a, 0 ≤ M a) (hb : ∀ a x, |c a x| ≤ M a)
    (U : PlaneHk univ K E) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : planeValue U =ᵐ[volume] f) :
    (planeScalarJetRow c hc M hM hb U : Vec 2 → E) =ᵐ[volume]
      fun x => ∑ a : JetIndex2 K, c a x • orderedDerivative a.2 f x := by
  have ha : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      U.toFunction.jet a x = orderedDerivative a.2 f x := by
    apply ae_all_iff.mpr
    intro a
    rcases a with ⟨j, w⟩
    have hh := planeHk_smooth_jet_readout U hf hu j.val (Nat.le_of_lt_succ j.isLt) w
    unfold AVRegularity.planeJetOrder at hh
    simp only [dite_eq_left (Nat.le_of_lt_succ j.isLt)] at hh
    have he : (⟨⟨j.val, Nat.lt_succ_of_le (Nat.le_of_lt_succ j.isLt)⟩, w⟩ : JetIndex2 K) = ⟨j, w⟩ := by
      cases j
      rfl
    rw [he] at hh
    exact hh
  filter_upwards [planeScalarJetRow_ae c hc M hM hb U, ha] with x hx ha
  exact hx.trans (Finset.sum_congr rfl (fun a _ => congrArg (fun e => c a x • e) (ha a)))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A fixed Leibniz subset retains the uniform nine-patch energy bound. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem spatialPatch_multiplicationTerm_l2_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 K E) (hD : HasPeriodicOrderedWeakJet D)
    (hm : ∀ a, Measurable (D a)) (m : PositionMask j)
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) (maskLeftLength j m) x‖ ≤ A) :
    (∑ p : Fin 2 → Fin N, ∑ w : DerivativeWord2 j, ∫ x,
      ‖multiplicationTerm hj
        (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) D m w x‖ ^ 2 ∂volume) ≤
      (9 * A ^ 2) * ∑ v : DerivativeWord2 (maskRightLength j m),
        ∫ x in AVenhance.unitCube,
          ‖D ⟨⟨maskRightLength j m,
            Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x‖ ^ 2 ∂volume := by
  have he (p : Fin 2 → Fin N) := periodic_multiplicationTerm_integral_sumSq hj
    (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ)))
    (spatialPatchCoefficient_smooth hζ N (fun i => (p i : ℤ)) K)
    (spatialPatchCoefficient_compact hζ N hN (fun i => (p i : ℤ))) D hD m
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact spatialPatch_array_l2_integral_budget hζ N hN (maskLeftLength j m) A hA hb
    (D ⟨⟨maskRightLength j m,
      Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩)
    (hm _) (hD.2.1 _) (hD.1 _)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Filter Set AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Product-space representatives of arbitrary Bochner L2 curves on a finite time measure. -/

variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_bochner_joint_realization (μ : Measure T) (ν : Measure X)
    [IsFiniteMeasure μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (u : T → Lp E 2 ν) (hu : MemLp u 2 μ) :
    ∃ f : T × X → E, MemLp f 2 (μ.prod ν) ∧
      ∀ᵐ t ∂μ, (u t : X → E) =ᵐ[ν] fun x => f (t, x) := by
  obtain ⟨s, hs, hB⟩ := exists_bochner_simple_approximation μ u hu
  let f := fun n (p : T × X) => s n p.1 p.2
  have hf : ∀ n, MemLp (f n) 2 (μ.prod ν) := fun n => simpleLp_joint_memLp μ ν (s n)
  let A := fun n => (hf n).toLp (f n)
  let B := fun n => (hs n).toLp (s n)
  have hd (n m : ℕ) : dist (A n) (A m) = dist (B n) (B m) :=
    bochnerProduct_distance μ ν (f n) (f m) (hf n) (hf m) (s n) (s m) (hs n) (hs m)
      (Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl)))
      (Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl)))
  have hA : CauchySeq A := CycleEvolution.cellCauchy_of_distance_eq A B hd hB.cauchySeq
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete hA
  let F := fun (p : T × X) => P p
  have hF : MemLp F 2 (μ.prod ν) := Lp.memLp P
  let S := bochnerL2TotalSlice ν (Function.curry F)
  have hS : MemLp S 2 μ :=
    bochnerL2TotalSlice_memLp μ ν (Function.curry F) (Lp.stronglyMeasurable P) hF
  have heS : ∀ᵐ t ∂μ, (S t : X → E) =ᵐ[ν] fun x => F (t, x) := by
    filter_upwards [bochnerL2Product_memLp_slices μ ν (Function.curry F) hF] with t ht
    exact bochnerL2TotalSlice_ae ν (Function.curry F) t ht
  let Q := hS.toLp S
  have heP : hF.toLp F = P := Lp.toLp_coeFn P hF
  have hdP (n : ℕ) : dist (A n) P = dist (B n) Q := by
    rw [← heP]
    exact bochnerProduct_distance μ ν (f n) F (hf n) hF (s n) S (hs n) hS
      (Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))) heS
  have hBQ : Tendsto B atTop (𝓝 Q) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he : (fun n => dist (B n) Q) = fun n => dist (A n) P := by
      funext n
      exact (hdP n).symm
    rw [he]
    simpa only [dist_self] using hP.dist (tendsto_const_nhds (x := P))
  have he : hu.toLp u = Q := tendsto_nhds_unique hB hBQ
  refine ⟨F, hF, ?_⟩
  filter_upwards [hu.coeFn_toLp, hS.coeFn_toLp, heS] with t hut hst ht
  have hclass : u t = S t := by
    rw [← hut, he]
    exact hst
  rw [hclass]
  exact ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The finite native transition expansion obeys the genuine coordinate differential recursion. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transitionJetExpansion (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (I : List (Fin 2)) (g : Vec 2 → E) (y : Vec 2) : E :=
  ∑ r ∈ Finset.range (I.length + 1), transitionJetTerm K I r g y

theorem transitionJetTerm_cons_zero
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2))
    (g : Vec 2 → E) (y : Vec 2) :
    transitionJetTerm K (i :: I) 0 g y = transitionJetCoefficientLayer K i I 0 g y := by
  unfold transitionJetTerm transitionJetCoefficientLayer
  apply Finset.sum_congr rfl
  intro A hA
  simp only [List.ofFn_zero, transitionT, weightedCoordinateDerivative, smul_eq_mul, add_zero]

theorem transitionJetExpansion_cons
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => K y a b))
    (i : Fin 2) (I : List (Fin 2)) (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    transitionJetExpansion K (i :: I) g =
      weightedCoordinateDerivative K i (transitionJetExpansion K I g) := by
  funext y
  have he := finite_layer_recursion_sum I.length
    (fun r => transitionJetTerm K (i :: I) r g y)
    (fun r => transitionJetCoefficientLayer K i I r g y)
    (fun r => transitionJetStateLayer K i I r g y)
    (transitionJetTerm_cons_zero K i I g y)
    (fun r => transitionJetTerm_cons_succ K i I r g y)
    (congrFun (transitionJetCoefficientLayer_above_order K i I (I.length + 1)
      (Nat.lt_succ_self _) g) y)
  unfold transitionJetExpansion
  simp only [List.length_cons, Nat.add_assoc] at *
  rw [he, weightedCoordinateDerivative_sum K i _
    (fun r => transitionJetTerm K I r g) y
    (fun r _ => (transitionJetTerm_smooth K hK I r g hg).differentiable (by simp) y)]
  apply Finset.sum_congr rfl
  intro r hr
  exact (weightedCoordinateDerivative_transitionJetTerm K hK i I r g hg y).symm

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Joint L2 representatives preserve prescribed spatial classes at every time. -/

variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_bochner_joint_trace_realization (μ : Measure T) (ν : Measure X)
    [IsFiniteMeasure μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (u : T → Lp E 2 ν) (hu : MemLp u 2 μ) :
    ∃ f : T × X → E, MemLp f 2 (μ.prod ν) ∧
      ∀ t, (u t : X → E) =ᵐ[ν] fun x => f (t, x) := by
  classical
  obtain ⟨F, hF, he⟩ := exists_bochner_joint_realization μ ν u hu
  let Good := fun t => (u t : X → E) =ᵐ[ν] fun x => F (t, x)
  let f := fun p : T × X => if Good p.1 then F p else u p.1 p.2
  have hfe : f =ᵐ[μ.prod ν] F := by
    have hgood := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae he
    filter_upwards [hgood] with p hp
    exact ite_eq_left hp
  refine ⟨f, hF.ae_eq hfe.symm, ?_⟩
  intro t
  by_cases ht : Good t
  · simpa only [f, ite_eq_left ht] using ht
  · exact Filter.Eventually.of_forall (fun x => by simp only [f, ite_eq_right ht])

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual weighted original native array equals the regular inactive-time
extension, at every sample time and every natural-cell point. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem familyNaturalRemainder_native_array_weight_eq
    (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (Ks : ℕ) (timeScale a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (τ : ℝ) (z : Vec 2)
    (Jac : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (rjet : ℕ) (A : U →L[ℝ] V) :
    nativeArrayAssembly rjet A
      (fun k I => F.weight p (timeScale * τ) * transportedCoeff Jac (F.identity v u γ).maxOrder
        (fun d I k => naturalSlowRemainderTimeCoefficient Ks
          (fun t X y => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X y k)
          a b hφ r (fun _ => σ) e E yc τ z) rjet I z k) =
    nativeArrayAssembly rjet A
      (fun k I => F.weight p (timeScale * τ) * transportedCoeff Jac (F.identity v u γ).maxOrder
        (fun d I k => naturalSlowRemainderTimeCoefficient Ks
          (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
          a b hφ r (fun _ => σ) e E yc τ z) rjet I z k) := by
  apply congrArg (nativeArrayAssembly rjet A)
  funext k I
  apply transportedCoeff_weight_congr
  intro d _ I i
  exact inactiveTimeZeroFamily_weighted_natural_remainder_eq F p c v u γ d I i Ks
    timeScale a b hφ r σ e E yc τ z

end AVRegularity.CycleJointProofs
end

section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The order-lowering array is the exact finite expansion of the native coordinate differential
word. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transitionJetExpansion_nil
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → E) :
    transitionJetExpansion K [] g = g := by
  funext y
  simp [transitionJetExpansion, transitionJetTerm, transitionT, listCoordinateDerivative]

theorem weightedListCoordinateDerivative_expansion
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => K y a b))
    (I : List (Fin 2)) (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    weightedListCoordinateDerivative K I g = transitionJetExpansion K I g := by
  induction I with
  | nil => exact (transitionJetExpansion_nil K g).symm
  | cons i I ih =>
    change weightedCoordinateDerivative K i (weightedListCoordinateDerivative K I g) = _
    rw [ih, transitionJetExpansion_cons K hK i I g hg]
end

/-! Positive native source orders carry no value-only term in the exact expansion. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transitionJetTerm_nonempty_zero
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2))
    (g : Vec 2 → E) : transitionJetTerm K (i :: I) 0 g = 0 := by
  funext y
  unfold transitionJetTerm
  apply Finset.sum_eq_zero
  intro A hA
  rw [List.ofFn_zero, transitionT_empty_output_nonempty_native]
  simp only [Pi.zero_apply, zero_smul]

theorem transitionJetExpansion_positive
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2))
    (g : Vec 2 → E) (y : Vec 2) :
    transitionJetExpansion K (i :: I) g y =
      ∑ r ∈ Finset.Icc 1 (i :: I).length, transitionJetTerm K (i :: I) r g y := by
  unfold transitionJetExpansion
  rw [Finset.sum_range_succ', transitionJetTerm_nonempty_zero]
  simp only [Pi.zero_apply, add_zero]
  have hI : Finset.Icc 1 (i :: I).length = Finset.Ico 1 ((i :: I).length + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  simp only [Nat.add_comm]
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact weighted identification of the actual piece array with its natural-flow formula. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_piece_array_eq_natural
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (A : DerivativeWord2 r) (t : Set.Icc tS tZ) (x : Vec 2) :
    F.weight p t • transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d I => F.dimFlux ν e E p c v u γ d I t
        (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x)) r A x =
    transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor t)
      (F.identity v u γ).maxOrder
      (fun d I => F.weight p t • F.dimFlux ν e E p c v u γ d I t
        (streamFlow φ hφ (F.piece p).anchor x t)
        (e⁻¹ • streamFlow φ hφ (F.piece p).anchor x t)) r A x := by
  rw [transportedCoeff_smul_native]
  by_cases hw : F.weight p t = 0
  · rw [hw]
    exact (zero_smul ℝ _).trans (zero_smul ℝ _).symm
  have ht : (t : ℝ) ∈ (F.piece p).output := by
    by_contra hout
    exact hw (F.weight_zero p t hout)
  have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, ht, t.property⟩
  rw [preparation_inverseJacobian_eq_natural hc p hp t ((F.piece p).output_subset ht),
    preparation_inverse_material_eq_streamFlow hc p hp t ((F.piece p).output_subset ht)]

end AVRegularity.CycleJointProofs
end

section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Genuine smooth inverse charts satisfy the native order-lowering expansion. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartInvJacobian_homeomorph_smooth (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (a b : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => chartInvJacobian ⇑X.symm y a b) := by
  have he : chartInvJacobian ⇑X.symm = fun y => chartJacobian ⇑X (X.symm y) := by
    funext y
    exact chartInvJacobian_homeomorph_symm X
      (hX.differentiable (by simp)) (hY.differentiable (by simp)) y
  rw [he]
  let L : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) a).comp
      (ContinuousLinearMap.apply ℝ (Vec 2) (basisVec b))
  exact (L.contDiff.comp (hX.fderiv_right (by simp))).comp hY

theorem inverseChart_native_jet_expansion (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (I : List (Fin 2)) (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    transitionJetExpansion (chartInvJacobian ⇑X.symm) I (g ∘ X.symm) =
      (listCoordinateDerivative I g) ∘ X.symm := by
  rw [← weightedListCoordinateDerivative_expansion (chartInvJacobian ⇑X.symm)
    (chartInvJacobian_homeomorph_smooth X hX hY) I (g ∘ X.symm) (hg.comp hY)]
  exact inverseChart_list_coordinate_derivative X (hX.differentiable (by simp))
    (hY.differentiable (by simp)) I g hg

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Summed higher-order patch energy for literal periodic weak jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem spatialPatch_multiplicationRawJet_order_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 K E) (hD : HasPeriodicOrderedWeakJet D)
    (hm : ∀ a, Measurable (D a)) (A : ℕ → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l, l ≤ j → ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) l x‖ ≤ A l) :
    (∑ p : Fin 2 → Fin N, ∑ w : DerivativeWord2 j, ∫ x,
      ‖multiplicationRawJet
        (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) D
          ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x‖ ^ 2 ∂volume) ≤
      (Fintype.card (PositionMask j) : ℝ) *
        ∑ m : PositionMask j, (9 * A (maskLeftLength j m) ^ 2) *
          ∑ v : DerivativeWord2 (maskRightLength j m), ∫ x in AVenhance.unitCube,
            ‖D ⟨⟨maskRightLength j m,
              Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x‖ ^ 2 ∂volume := by
  have ht : (∑ p : Fin 2 → Fin N, ∑ w : DerivativeWord2 j, ∫ x,
      ‖multiplicationRawJet
        (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) D
          ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x‖ ^ 2 ∂volume) ≤
      ∑ p : Fin 2 → Fin N, ∑ w : DerivativeWord2 j,
        (Fintype.card (PositionMask j) : ℝ) * ∑ m : PositionMask j, ∫ x,
          ‖multiplicationTerm hj
            (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) D m w x‖ ^ 2 ∂volume := by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro w _
    exact periodic_multiplicationRawJet_integral_square_le _
      (spatialPatchCoefficient_smooth hζ N (fun i => (p i : ℤ)) K)
      (spatialPatchCoefficient_compact hζ N hN (fun i => (p i : ℤ)))
      D hD ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩
  apply ht.trans
  simp_rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let T := fun (p : Fin 2 → Fin N) (w : DerivativeWord2 j) (m : PositionMask j) =>
    ∫ x, ‖multiplicationTerm hj
      (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ))) D m w x‖ ^ 2 ∂volume
  have he : (∑ p, ∑ w, ∑ m, T p w m) = ∑ m, ∑ p, ∑ w, T p w m := by
    calc
      (∑ p, ∑ w, ∑ m, T p w m) = ∑ p, ∑ m, ∑ w, T p w m := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [he]
  apply Finset.sum_le_sum
  intro m _
  exact spatialPatch_multiplicationTerm_l2_budget hζ N hN hj D hD hm m
    (A (maskLeftLength j m)) (hA _) (hb _ (maskLeftLength_le j m))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact weighted identification of the actual piece array with its natural-flow formula. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_piece_operator_eq_natural
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (t : Set.Icc tS tZ) (x : Vec 2) :
    F.weight p t • (nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x)) r A x a)) =
    F.weight p t • (nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          (streamFlow φ hφ (F.piece p).anchor x t)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor x t)) r A x a)) := by
  by_cases hw : F.weight p t = 0
  · rw [hw]
    ext z k
    simp
  · have ht : (t : ℝ) ∈ (F.piece p).output := by
      by_contra hout
      exact hw (F.weight_zero p t hout)
    have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, ht, t.property⟩
    rw [preparation_inverseJacobian_eq_natural hc p hp t ((F.piece p).output_subset ht),
      preparation_inverse_material_eq_streamFlow hc p hp t ((F.piece p).output_subset ht)]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The complete rough coupled source has the exact cell flux price at every original derivative order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_affine_ae (K : ι → ℕ) (D : ℕ) (r e : ℝ)
    (he : e ≠ 0) (y : Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (W : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D r
      (fun v u d t z => (e * (e ^ (d.1 - 1))⁻¹) • A v u d t (y + e • z))
      (fun u => planeCarrierAffine e he y (W u)) i =ᵐ[volume]
      fun z => e • planeRawCouplingFlux K D r A W i (y + e • z) := by
  have hall : ∀ᵐ z ∂volume, ∀ u, ∀ a : JetIndex2 (K u + 1),
      (planeCarrierAffine e he y (W u)).toFunction.jet a z =
        e ^ a.1.val • (W u).toFunction.jet a (y + e • z) := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro a
    exact planeCarrierAffine_jet_ae e he y (W u) a
  filter_upwards [hall] with z hz
  unfold planeRawCouplingFlux
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hjet : (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
      (planeCarrierAffine e he y (W u)).toFunction.jet
        ⟨⟨d.1 - 1, by have hh := admissibleOrders_reserve K D i u d; omega⟩, word⟩ z)) =
      e ^ (d.1 - 1) • WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
        (W u).toFunction.jet
          ⟨⟨d.1 - 1, by have hh := admissibleOrders_reserve K D i u d; omega⟩, word⟩ (y + e • z)) := by
    apply PiLp.ext
    intro word
    exact hz u _
  rw [hjet, smul_apply, map_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ he), mul_one]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Sum all actual translated compact-test pairings before identifying the periodized raw jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem summed_compact_jet_pairing (U : Set (Vec 2)) (f : PlaneHk Set.univ K E)
    (α : JetIndex2 K) (φ : PlaneHk Set.univ L E) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (hs : (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ₑ) < ⊤) :
    (∑' n : Fin 2 → ℤ, ∫ x,
      inner ℝ ((planeCarrierTranslation K (AVenhance.latticeShift n) f).toFunction.jet α x)
        (φ.toFunction.jet β x)) =
      ∫ x, inner ℝ (periodizeRawJet f.toFunction.jet α x) (φ.toFunction.jet β x) := by
  let g := restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  have hg : g =ᵐ[volume.restrict U] φ.toFunction.jet β :=
    (restrictPlaneLpCLM_ae U _).trans ((univToPlane_ae (φ.val β)).restrict (s := U))
  have himages := Summable.of_enorm hs.ne
  have hseries := periodized_image_jet_series_ae U α f hs
  have hsupport : ∀ᵐ x ∂volume, x ∉ U →
      inner ℝ (periodizeRawJet f.toFunction.jet α x) (φ.toFunction.jet β x) = 0 := by
    filter_upwards [hφ] with x hx hxu
    rw [hx hxu, inner_zero_right]
  calc
    _ = ∑' n : Fin 2 → ℤ, inner ℝ (planeImageJetCLM U (AVenhance.latticeShift n) α f) g :=
      tsum_congr (fun n => translated_compact_jet_pairing U (AVenhance.latticeShift n) f α φ β hφ)
    _ = inner ℝ (∑' n : Fin 2 → ℤ, planeImageJetCLM U (AVenhance.latticeShift n) α f) g :=
      (inner_hilbert_tsum himages g).symm
    _ = ∫ x in U, inner ℝ (periodizeRawJet f.toFunction.jet α x) (φ.toFunction.jet β x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hseries, hg] with x hx hy
      exact congrArg₂ (inner ℝ) hx hy
    _ = _ := setIntegral_eq_integral_of_ae_compl_eq_zero hsupport

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.ChartTransport AVenhance.Infra.Section5
namespace AVRegularity.CycleJointProofs

/-! A family-independent scale-weighted bound for every native inverse-Piola matrix entry. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparationJacobian_scaled_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1)) (s r : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - s| ≤ 2 * Cage * ocTauPP α q Λ m)
    (n : ℕ) (hn : n ≤ Jchart) (i j : Fin 2) (x : Vec 2) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ l, l ≤ n → (ocEpsilon q Λ (m - 1)) ^ l *
      ‖iteratedFDeriv ℝ l (fun y => naturalPreparationJacobian hφ s r y i j) x‖ ≤
        compConst C n * C := by
  dsimp only
  let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  have hC : 1 ≤ C := one_le_jetConst _ _
  have hΦ : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (fun y => streamFlow φ hφ r y s) :=
    (hc.smooth r hr s hs).of_le (by exact_mod_cast Nat.add_le_add_right hn 1)
  have hΨ : ContDiff ℝ (n : ℕ∞) (fun y => streamFlow φ hφ s y r) :=
    (hc.smooth s hs r hr).of_le (by exact_mod_cast hn.trans (Nat.le_succ _))
  have hJF := preparation_flow_jetBound hc ha hE r s hr hs hage
  have hJR := preparation_flow_jetBound hc ha hE s r hs hr (by simpa only [abs_sub_comm] using hage)
  have hJΦ : JetBound (fun y => streamFlow φ hφ r y s) (n + 1) C (ocEpsilon q Λ (m - 1)) :=
    fun p hp hpN => hJF p hp (hpN.trans (Nat.add_le_add_right hn 1))
  have hJΨ : JetBound (fun y => streamFlow φ hφ s y r) n C (ocEpsilon q Λ (m - 1)) :=
    fun p hp hpN => hJR p hp (hpN.trans (hn.trans (Nat.le_succ _)))
  intro l hl
  simpa only [naturalPreparationJacobian, chartJacobian, jacMatrix] using
    jacComp_bound hΦ hΨ hC hE (le_refl _) hJΦ hJΨ i j x l hl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Fourth radial moments give a summable norm bound for actual localized image readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeImageJetCLM_radial_norm_le (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R)
    (hU : U ⊆ Metric.ball (0 : Vec 2) R) (z : Vec 2) (a : JetIndex2 K)
    (f : PlaneHk Set.univ K E) (M : ℝ) (hM : 0 ≤ M)
    (hw : AEStronglyMeasurable (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) volume)
    (hb : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume ≤ ENNReal.ofReal M)
    (n : Fin 2 → ℤ) :
    ‖planeImageJetCLM U (AVenhance.latticeShift n) a f‖ ≤
      ((1 + R + ‖z‖) ^ 4 * M) * (1 / spatialLatticeWeight n) ^ 2 := by
  have hf : AEStronglyMeasurable (f.toFunction.jet a) volume := by
    simpa only [Measure.restrict_univ] using (f.toFunction.memL2 a).aestronglyMeasurable
  have ht := (eLpNorm_mono_measure
    (fun x => f.toFunction.jet a (x + AVenhance.latticeShift n))
    (Measure.restrict_mono_set volume hU)).trans
      (radialMoment_image_eLpNorm_le (f.toFunction.jet a) z R hR hf hw n)
  have hp := ht.trans (mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ENNReal.ofReal ((1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2) from zero_le))
  rw [← ENNReal.ofReal_mul (by positivity)] at hp
  rw [Lp.norm_def, eLpNorm_congr_ae (planeImageJetCLM_ae U (AVenhance.latticeShift n) a f)]
  have hc : 0 ≤ ((1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2) * M := by positivity
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  rw [ENNReal.toReal_ofReal hc] at hh
  convert hh using 1
  ring

end AVRegularity.CycleJointProofs
end
