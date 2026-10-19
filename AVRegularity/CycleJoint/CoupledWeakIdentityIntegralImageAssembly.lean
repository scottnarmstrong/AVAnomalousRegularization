-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.TransportedCoeff
public import AVRegularity.CycleJoint.CompactWeakCorrectionIntegrability
public import AVRegularity.Statements.Construction.OcA
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual torus jet components are continuous linear coordinate readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def torusJetComponentCLM (a : JetIndex2 K) :
    TorusHk K E →L[ℝ] Lp E 2 (volume.restrict AVenhance.unitCube) :=
  (PiLp.proj (𝕜 := ℝ) 2
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) E) a).comp
    (torusHkGraph (E := E) K).toSubmodule.subtypeL

theorem torusJetComponentCLM_apply (a : JetIndex2 K) (f : TorusHk K E) :
    torusJetComponentCLM a f = f.val a := rfl

theorem torusJetComponent_add (a : JetIndex2 K) (f g : TorusHk K E) :
    (f + g).val a = f.val a + g.val a := (torusJetComponentCLM a).map_add f g

theorem torusJetComponent_smul (a : JetIndex2 K) (c : ℝ) (f : TorusHk K E) :
    (c • f).val a = c • f.val a := (torusJetComponentCLM a).map_smul c f

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal transported coefficient acts by the finite Piola and order-lowering flux expansion. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem transportedCoeff_flux_expansion
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ)
    (g : DerivativeWord2 r → E) (x : Vec 2) (a : Fin 2) :
    (∑ A : DerivativeWord2 r, transportedCoeff K D B r A x a • g A) =
      ∑ d ∈ Finset.Icc (r + 1) D, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
        (K x a i * B d I i) •
          (∑ A : DerivativeWord2 r, transitionT K (List.ofFn I) (List.ofFn A) x • g A) := by
  classical
  simp only [transportedCoeff, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.smul_sum]
end

/-! Original order D contributes only positive state derivative orders strictly below D. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem transportedCoeff_zero_at_or_above
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (hr : D ≤ r)
    (A : DerivativeWord2 r) (y : Vec 2) : transportedCoeff K D B r A y = 0 := by
  have he : Finset.Icc (r + 1) D = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
  funext a
  simp only [transportedCoeff, he, Finset.sum_empty, Pi.zero_apply]

theorem transportedCoeff_positive_flux_sum
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (g : ∀ r : ℕ, DerivativeWord2 r → E) (y : Vec 2) (a : Fin 2) :
    (∑ r ∈ Finset.Icc 1 (D - 1), ∑ A : DerivativeWord2 r,
      transportedCoeff K D B r A y a • g r A) =
      ∑ r ∈ Finset.Icc 1 D, ∑ A : DerivativeWord2 r,
        transportedCoeff K D B r A y a • g r A := by
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      (Finset.mem_Icc.mp hr).2.trans (Nat.sub_le _ _)⟩
  · intro r hr hn
    have hh : D ≤ r := by
      simp only [Finset.mem_Icc] at hr hn
      omega
    apply Finset.sum_eq_zero
    intro A hA
    rw [transportedCoeff_zero_at_or_above K D B r hh A y]
    simp only [Pi.zero_apply, zero_smul]
end

/-! Only original source orders in the defining finite interval affect a transported array. -/

theorem transportedCoeff_source_congr
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℕ)
    (B B' : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2)
    (hB : ∀ d ∈ Finset.Icc (r + 1) D, ∀ I, B d I = B' d I) :
    transportedCoeff K D B r A y = transportedCoeff K D B' r A y := by
  funext a
  unfold transportedCoeff
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro I hI
  rw [hB d hd I]

/-! Literal partition-weight congruence passes through the full Piola coefficient sum. -/

theorem transportedCoeff_weight_congr
    (J : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D r : ℕ) (A : DerivativeWord2 r)
    (B C : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (z : Vec 2) (a : Fin 2) (w : ℝ)
    (h : ∀ d ∈ Finset.Icc (r + 1) D, ∀ I i, w * B d I i = w * C d I i) :
    w * transportedCoeff J D B r A z a = w * transportedCoeff J D C r A z a := by
  unfold transportedCoeff
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro i _
  calc
    w * (J z a i * B d I i * transitionT J (List.ofFn I) (List.ofFn A) z) =
        J z a i * (w * B d I i) * transitionT J (List.ofFn I) (List.ofFn A) z := by ring
    _ = J z a i * (w * C d I i) * transitionT J (List.ofFn I) (List.ofFn A) z := by rw [h d hd I i]
    _ = w * (J z a i * C d I i * transitionT J (List.ofFn I) (List.ofFn A) z) := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The unit response price depends only on the two finite response indices. -/

theorem shiftedResponseEnergyBudget_unit_independent (p p' n n' j h : ℕ) :
    shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p n j h =
      shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p' n' j h := by
  induction j generalizing n n' h with
  | zero =>
    induction h generalizing n n' with
    | zero => simp only [shiftedResponseEnergyBudget]
    | succ h ih =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget, one_mul, one_mul]
      exact ih (n + p) (n' + p')
  | succ j ih =>
    induction h generalizing n n' with
    | zero =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget, one_mul, one_mul]
      exact ih (n + p) (n' + p') 0
    | succ h ihh =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget,
        ih (n + p) (n' + p') (h + 1), ihh (n + p) (n' + p')]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Integrated weak identities are invariant under actual almost-everywhere integrand equalities. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_integrands_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v v' : ℝ → Vec 2 → Vec 2) (u u' f f' φ φ' : Vec 2 → E)
    (dφ dφ' : Fin 2 → Vec 2 → E) (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g g' : ℝ → Vec 2 → E)
    (hu : (fun x => inner ℝ (u x) (φ x)) =ᵐ[μ] fun x => inner ℝ (u' x) (φ' x))
    (hf : (fun x => inner ℝ (f x) (φ x)) =ᵐ[μ] fun x => inner ℝ (f' x) (φ' x))
    (hr : ∀ s ∈ Set.Ioc a t, weakIdentityRhs ν v φ dφ du flux F g s =ᵐ[μ]
      weakIdentityRhs ν v' φ' dφ' du' flux' F' g' s)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v' u' f' φ' dφ' du' flux' F' g' := by
  have hi : (fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F g s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, weakIdentityRhs ν v' φ' dφ' du' flux' F' g' s x ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact integral_congr_ae (hr s hs)
  refine ⟨h.1.congr hu, h.2.1.congr hf, ?_, h.2.2.2.1.congr hi, ?_⟩
  · intro s hs
    exact (h.2.2.1 s hs).congr (hr s hs)
  · rw [← integral_congr_ae hu, ← integral_congr_ae hf]
    exact h.2.2.2.2.trans (integral_congr_ae hi)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The actual integrated PDE right-hand side is additive in the solution and forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weakIdentityRhs_add (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g g' : ℝ → Vec 2 → E) (s : ℝ) (x : Vec 2) :
    weakIdentityRhs ν v φ dφ (du + du') (flux + flux') (F + F') (g + g') s x =
      weakIdentityRhs ν v φ dφ du flux F g s x +
        weakIdentityRhs ν v φ dφ du' flux' F' g' s x := by
  simp only [weakIdentityRhs, Pi.add_apply, WithLp.ofLp_add, inner_add_left,
    Finset.sum_add_distrib, mul_add]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each weighted derivative tensor is bounded by the complete factorial energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem factorial_component_energy_le {μ : Measure (Vec 2)} {K : ℕ}
    (ρ : ℝ) (D : JetL2 μ K E) (j : Fin (K + 1)) :
    factorialWeight ρ j.val * derivativeNormSq D j ≤ factorialNormSq ρ D := by
  exact Finset.single_le_sum
    (fun l _ => mul_nonneg (factorialWeight_nonneg ρ l.val) (derivativeNormSq_nonneg D l))
    (Finset.mem_univ j)
end

/-! The factorial energy is the finite sum over the literal ordered jet indices. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_eq_sum_indices {μ : Measure (Vec 2)} {K : ℕ}
    (ρ : ℝ) (D : JetL2 μ K E) :
    factorialNormSq ρ D =
      ∑ a : JetIndex2 K, factorialWeight ρ a.1.val * ‖D a‖ ^ 2 := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [Finset.mul_sum]
  exact (Fintype.sum_sigma (fun a : JetIndex2 K => factorialWeight ρ a.1.val * ‖D a‖ ^ 2)).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Mesh derivatives are paid by the dimensionless product of radius and mesh size. -/

theorem factorialWeight_mesh_price (ρ s : ℝ) (l r : ℕ) :
    factorialWeight ρ (l + r) * s ^ (2 * l) ≤
      (ρ * s) ^ (2 * l) * factorialWeight ρ r := by
  unfold factorialWeight
  have hd : (r.factorial : ℝ) ^ 2 ≤ ((l + r).factorial : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
    exact_mod_cast Nat.factorial_le (Nat.le_add_left r l)
  have hn : 0 ≤ (ρ * s) ^ (2 * l) * ρ ^ (2 * r) := by
    rw [show 2 * l = l * 2 by omega, show 2 * r = r * 2 by omega,
      pow_mul, pow_mul]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : ρ ^ (2 * (l + r)) * s ^ (2 * l) =
      (ρ * s) ^ (2 * l) * ρ ^ (2 * r) := by
    rw [Nat.mul_add, pow_add, mul_pow]
    ring
  rw [div_mul_eq_mul_div, he]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_left hn
    (show (0 : ℝ) < (r.factorial : ℝ) ^ 2 by positivity) hd

/-! At radius at most one the finite factorial minimum has an explicit polynomial price. -/

theorem factorialWeight_decreasing_order (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {j K : ℕ} (hj : j ≤ K) : factorialWeight ρ K ≤ factorialWeight ρ j := by
  have hp : ρ ^ (2 * K) ≤ ρ ^ (2 * j) :=
    pow_le_pow_of_le_one hρ.le hρ1 (Nat.mul_le_mul_left 2 hj)
  have hf : (j.factorial : ℝ) ≤ (K.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have hs : (j.factorial : ℝ) ^ 2 ≤ (K.factorial : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hf
  unfold factorialWeight
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mul_le_mul hp hs (by positivity) (by positivity)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual radius-scaled derivative bounds assemble into the finite factorial norm without fiber-dimension losses. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialNormSq_le_of_scaled_jets {ρ F : ℝ} (hρ : 0 ≤ ρ) (hF : 0 ≤ F)
    (D : JetL2 μ K E) (M : ℕ → ℝ) (hM : ∀ n, n ≤ K → 0 ≤ M n)
    (hb : ∀ (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n),
      ρ ^ n * ‖D ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤ M n * F) :
    factorialNormSq ρ D ≤
      (∑ j : Fin (K + 1), (2 : ℝ) ^ j.val * (M j.val / (j.val.factorial : ℝ)) ^ 2) * F ^ 2 := by
  unfold factorialNormSq derivativeNormSq factorialWeight
  calc
    _ ≤ ∑ j : Fin (K + 1), ∑ _w : DerivativeWord2 j.val,
        (M j.val * F) ^ 2 / (j.val.factorial : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w _
      have hs := (sq_le_sq₀ (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _))
        (mul_nonneg (hM _ (Nat.le_of_lt_succ j.isLt)) hF)).mpr
          (hb j.val (Nat.le_of_lt_succ j.isLt) w)
      have he : ρ ^ (2 * j.val) / (j.val.factorial : ℝ) ^ 2 * ‖D ⟨j, w⟩‖ ^ 2 =
          (ρ ^ j.val * ‖D ⟨j, w⟩‖) ^ 2 / (j.val.factorial : ℝ) ^ 2 := by
        rw [Nat.mul_comm, pow_mul, mul_pow]
        ring
      rw [he]
      exact div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat, div_pow, mul_pow]
      ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The cell radius cancels the exact derivative price in each factorial weight. -/

theorem factorialWeight_affine (ρ e : ℝ) (he : e ≠ 0) (j : ℕ) :
    factorialWeight (ρ / e) j * ‖e ^ j‖ ^ 2 = factorialWeight ρ j := by
  have hp : (e ^ j) ^ 2 = e ^ (2 * j) := by
    rw [← pow_mul, Nat.mul_comm]
  have hepow : e ^ (2 * j) ≠ 0 := pow_ne_zero _ he
  have hfac : (j.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [Real.norm_eq_abs, sq_abs, hp]
  unfold factorialWeight
  rw [div_pow]
  field_simp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Hilbert-valued weak gradients give genuine native order-one plane carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def hilbertFirstJet (f : Vec 2 → E) (G : Fin 2 → Vec 2 → E) : RawJet2 1 E :=
  fun a x => if hj : a.1.val = 0 then f x
    else G (a.2 ⟨0, by omega⟩) x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem hilbertFirstJet_derivative (f : Vec 2 → E) (G : Fin 2 → Vec 2 → E)
    (w : DerivativeWord2 1) :
    hilbertFirstJet f G ⟨⟨1, by omega⟩, w⟩ = G (w 0) := by
  rfl

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem hilbertFirstJet_memL2 {U : Set (Vec 2)} (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict U)) (hG : ∀ i, MemLp (G i) 2 (volume.restrict U)) :
    JetMemL2On U (hilbertFirstJet f G) := by
  rintro ⟨j, w⟩
  fin_cases j
  · exact hf
  · exact hG (w 0)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem hilbertFirstJet_weak {U : Set (Vec 2)} (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E)
    (hw : ∀ i e, HasWeakPartialDerivOn U i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) :
    HasOrderedWeakJetOn U (hilbertFirstJet f G) := by
  intro j w i e
  fin_cases j
  change HasWeakPartialDerivOn U i (fun x => inner ℝ e (f x))
    (fun x => inner ℝ e (G i x))
  exact hw i e

def planeH1OfWeakGradient {U : Set (Vec 2)} (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict U)) (hG : ∀ i, MemLp (G i) 2 (volume.restrict U))
    (hw : ∀ i e, HasWeakPartialDerivOn U i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) : PlaneHk U 1 E :=
  (show PlaneHkFunction U 1 E from
    ⟨hilbertFirstJet f G, hilbertFirstJet_memL2 f G hf hG, hilbertFirstJet_weak f G hw⟩).toHk

theorem planeH1OfWeakGradient_value_ae {U : Set (Vec 2)} (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict U))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict U))
    (hw : ∀ i e, HasWeakPartialDerivOn U i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) :
    ((planeH1OfWeakGradient f G hf hG hw).val (valueIndex2 1) : Vec 2 → E)
      =ᵐ[volume.restrict U] f := by
  exact (hf.coeFn_toLp)

theorem planeH1OfWeakGradient_gradient_ae {U : Set (Vec 2)} (f : Vec 2 → E)
    (G : Fin 2 → Vec 2 → E) (hf : MemLp f 2 (volume.restrict U))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict U))
    (hw : ∀ i e, HasWeakPartialDerivOn U i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e (G i x))) (w : DerivativeWord2 1) :
    ((planeH1OfWeakGradient f G hf hG hw).val ⟨⟨1, by omega⟩, w⟩ : Vec 2 → E)
      =ᵐ[volume.restrict U] G (w 0) := by
  exact (hG (w 0)).coeFn_toLp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! The homogeneous spatial weak atoms have the literal signed integrals of their directions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def homogeneousWeakRhsIntegralAtom (μ : Measure (Vec 2)) (ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (j : Fin 3) (s : ℝ) : ℝ :=
  if j = 0 then -(∑ k : Fin 2, ∫ x, v s x k * inner ℝ (du s k x) (φ x) ∂μ)
  else if j = 1 then -ν * ∑ k : Fin 2, ∫ x, inner ℝ (du s k x) (dφ k x) ∂μ
  else -(∑ k : Fin 2, ∫ x, inner ℝ (flux s x k) (dφ k x) ∂μ)

theorem homogeneousWeakRhsAtom_integral (μ : Measure (Vec 2)) (ν s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hd : ∀ k, Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x)) μ)
    (hν : ∀ k, Integrable (fun x => inner ℝ (du s k x) (dφ k x)) μ)
    (hc : ∀ k, Integrable (fun x => inner ℝ (flux s x k) (dφ k x)) μ) (j : Fin 3) :
    (∫ x, homogeneousWeakRhsAtom ν v φ dφ du flux j s x ∂μ) =
      homogeneousWeakRhsIntegralAtom μ ν v φ dφ du flux j s := by
  unfold homogeneousWeakRhsAtom homogeneousWeakRhsIntegralAtom
  split_ifs
  · rw [integral_neg, integral_finsetSum Finset.univ (fun k _ => hd k)]
  · rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hν k)]
  · rw [integral_neg, integral_finsetSum Finset.univ (fun k _ => hc k)]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Literal lattice periodization and its exact periodicity. -/

variable {E : Type*} [NormedAddCommGroup E]

def latticePeriodization (f : Vec 2 → E) (x : Vec 2) : E :=
  ∑' n : Fin 2 → ℤ, f (x + AVenhance.latticeShift n)

theorem latticeShift_add (n k : Fin 2 → ℤ) :
    AVenhance.latticeShift (n + k) = AVenhance.latticeShift n + AVenhance.latticeShift k := by
  funext i
  simp [AVenhance.latticeShift]

theorem latticePeriodization_periodic (f : Vec 2 → E) :
    AVenhance.IsZ2Periodic (latticePeriodization f) := by
  intro k x
  have he := (latticeDisplacementEquiv (-k)).tsum_eq
    (fun n => f (x + AVenhance.latticeShift n))
  change (∑' n : Fin 2 → ℤ, f (x + AVenhance.latticeShift (n - -k))) = _ at he
  simpa only [latticePeriodization, sub_neg_eq_add, latticeShift_add,
    add_assoc, add_comm (AVenhance.latticeShift k)] using he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Add trajectories and their time-integrable lifts on the actual plane Sobolev carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierCurve_continuousOn_add (f g : ℝ → PlaneHk Set.univ K E) (I : Set ℝ)
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    ContinuousOn (fun t => f t + g t) I := hf.add hg

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem normedCurve_memLp_add (f g : ℝ → E) (μ : Measure ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : MemLp (fun t => f t + g t) 2 μ := hf.add hg
end

/-! The zero plane Sobolev carrier has zero raw jets almost everywhere. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeZero_rawJet_ae (K : ℕ) (α : JetIndex2 K) :
    (0 : PlaneHk Set.univ K E).toFunction.jet α =ᵐ[volume] 0 := by
  have hz := Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2)))
  simp only [Measure.restrict_univ] at hz
  exact hz
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The chart-age transfer uses only nonnegativity of the renewal and amplitude scales `ocTauPP`
and `ocA`. -/

theorem preparation_renewal_nonnegative (α q : ℝ) (Λ m : ℕ) :
    0 ≤ ocTauPP α q Λ m := by
  unfold ocTauPP
  positivity

theorem preparation_amplitude_nonnegative (α q : ℝ) (Λ m : ℕ)
    (hE : 0 ≤ ocEpsilon q Λ m) : 0 ≤ ocA α q Λ m := by
  exact Real.rpow_nonneg hE _

/-! Every ordering of the prescribed metric and source insertions occurs in the response list. -/

theorem responseInsertionWords_complete (w : List Bool) (j h : ℕ)
    (hlen : w.length = j + h) (hc : w.count true = h) :
    w ∈ responseInsertionWords j h := by
  induction w generalizing j h with
  | nil =>
    have hj : j = 0 := by simp only [List.length_nil] at hlen; omega
    have hh : h = 0 := by simpa using hc.symm
    subst j; subst h
    simp [responseInsertionWords]
  | cons b w ih =>
    have hbound : w.count true ≤ w.length := List.count_le_length
    cases b with
    | false =>
      have hc' : w.count true = h := by simpa using hc
      cases j with
      | zero => simp only [List.length_cons] at hlen; omega
      | succ j =>
        have hlen' : w.length = j + h := by simp only [List.length_cons] at hlen; omega
        have hm : false :: w ∈ (responseInsertionWords j h).map (false :: ·) :=
          List.mem_map.mpr ⟨w, ih j h hlen' hc', rfl⟩
        cases h with
        | zero => simpa only [responseInsertionWords] using hm
        | succ h =>
          rw [responseInsertionWords]
          exact List.mem_append.mpr (Or.inl hm)
    | true =>
      have hc' : w.count true + 1 = h := by simpa using hc
      cases h with
      | zero => omega
      | succ h =>
        have hlen' : w.length = j + h := by simp only [List.length_cons] at hlen; omega
        have hm : true :: w ∈ (responseInsertionWords j h).map (true :: ·) :=
          List.mem_map.mpr ⟨w, ih j h hlen' (by omega), rfl⟩
        cases j with
        | zero => simpa only [responseInsertionWords] using hm
        | succ j =>
          rw [responseInsertionWords]
          exact List.mem_append.mpr (Or.inr hm)

theorem mem_responseInsertionWords_iff (j h : ℕ) (w : List Bool) :
    w ∈ responseInsertionWords j h ↔ w.length = j + h ∧ w.count true = h :=
  ⟨responseInsertionWords_grade j h w, fun hw => responseInsertionWords_complete w j h hw.1 hw.2⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Joint spatial ordered derivatives of compact smooth Hilbert fields and their commuting time derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spacetimeOrderedDerivative (f : ℝ × Vec 2 → E) :
    {n : ℕ} → DerivativeWord2 n → ℝ × Vec 2 → E
  | 0, _ => f
  | n + 1, w => fun p => fderiv ℝ (spacetimeOrderedDerivative f (fun i => w i.castSucc)) p
      (0, basisVec (w (Fin.last n)))

theorem spacetimeOrderedDerivative_smooth (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {n : ℕ} (w : DerivativeWord2 n) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeOrderedDerivative f w) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ((ih (fun i => w i.castSucc)).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem spacetimeOrderedDerivative_compact (f : ℝ × Vec 2 → E)
    (hs : HasCompactSupport f) {n : ℕ} (w : DerivativeWord2 n) :
    HasCompactSupport (spacetimeOrderedDerivative f w) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    exact (ih (fun i => w i.castSucc)).fderiv_apply ℝ (0, basisVec (w (Fin.last n)))

theorem spacetime_slice_fderiv (f : ℝ × Vec 2 → E) (hf : Differentiable ℝ f)
    (t : ℝ) (x v : Vec 2) :
    fderiv ℝ f (t, x) (0, v) = fderiv ℝ (fun y => f (t, y)) x v := by
  have hd := (hf (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Vec 2) t x)
  have hd' : HasFDerivAt (fun y => f (t, y))
      ((fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x := by
    simpa only [Function.comp_def] using hd
  rw [hd'.fderiv]
  rfl

theorem spacetimeOrderedDerivative_slice (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {n : ℕ} (w : DerivativeWord2 n) (t : ℝ) (x : Vec 2) :
    spacetimeOrderedDerivative f w (t, x) = orderedDerivative w (fun y => f (t, y)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    let w' : DerivativeWord2 n := fun i => w i.castSucc
    have he : (fun y => spacetimeOrderedDerivative f w' (t, y)) =
        orderedDerivative w' (fun y => f (t, y)) := funext (fun y => ih w' y)
    change fderiv ℝ (spacetimeOrderedDerivative f w') (t, x)
      (0, basisVec (w (Fin.last n))) = _
    rw [orderedDerivative_succ, ← he]
    exact spacetime_slice_fderiv _ ((spacetimeOrderedDerivative_smooth f hf w').differentiable (by simp))
      t x (basisVec (w (Fin.last n)))

theorem spacetimeOrderedDerivative_time_commute (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {n : ℕ} (w : DerivativeWord2 n) :
    spacetimeOrderedDerivative (fun p => fderiv ℝ f p (1, 0)) w =
      (fun p => fderiv ℝ (spacetimeOrderedDerivative f w) p (1, 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let w' : DerivativeWord2 n := fun i => w i.castSucc
    change (fun p => fderiv ℝ (spacetimeOrderedDerivative (fun p => fderiv ℝ f p (1, 0)) w') p
      (0, basisVec (w (Fin.last n)))) = _
    rw [ih w']
    funext p
    exact smoothField_directional_derivative_commute (spacetimeOrderedDerivative f w')
      ((spacetimeOrderedDerivative_smooth f hf w').of_le (by simp)) p (1, 0)
      (0, basisVec (w (Fin.last n)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Adding actual weak identities preserves every spatial and temporal integrability clause. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_add (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u u' f f' φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g g' : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g)
    (h' : CoupledWeakIdentity μ ν a t v u' f' φ dφ du' flux' F' g') :
    CoupledWeakIdentity μ ν a t v (u + u') (f + f') φ dφ
      (du + du') (flux + flux') (F + F') (g + g') := by
  let r := weakIdentityRhs ν v φ dφ du flux F g
  let r' := weakIdentityRhs ν v φ dφ du' flux' F' g'
  have hr : weakIdentityRhs ν v φ dφ (du + du') (flux + flux') (F + F') (g + g') =
      r + r' := by
    funext s x
    exact weakIdentityRhs_add ν v φ dφ du du' flux flux' F F' g g' s x
  have hu : (fun x => inner ℝ ((u + u') x) (φ x)) =
      (fun x => inner ℝ (u x) (φ x)) + (fun x => inner ℝ (u' x) (φ x)) := by
    funext x; exact inner_add_left _ _ _
  have hf : (fun x => inner ℝ ((f + f') x) (φ x)) =
      (fun x => inner ℝ (f x) (φ x)) + (fun x => inner ℝ (f' x) (φ x)) := by
    funext x; exact inner_add_left _ _ _
  have ht : (fun s => ∫ x, (r + r') s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, r s x ∂μ) + (fun s => ∫ x, r' s x ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact integral_add (h.2.2.1 s hs) (h'.2.2.1 s hs)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable
      (weakIdentityRhs ν v φ dφ (du + du') (flux + flux') (F + F') (g + g') s) μ) ∧
    IntegrableOn (fun s => ∫ x,
      weakIdentityRhs ν v φ dφ (du + du') (flux + flux') (F + F') (g + g') s x ∂μ)
      (Set.Ioc a t) ∧
    (∫ x, inner ℝ ((u + u') x) (φ x) ∂μ) -
      (∫ x, inner ℝ ((f + f') x) (φ x) ∂μ) =
        ∫ s in Set.Ioc a t, ∫ x,
          weakIdentityRhs ν v φ dφ (du + du') (flux + flux') (F + F') (g + g') s x ∂μ
  rw [hu, hf, hr]
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1,
    fun s hs => (h.2.2.1 s hs).add (h'.2.2.1 s hs),
    (h.2.2.2.1.add h'.2.2.2.1).congr ht.symm, ?_⟩
  rw [integral_congr_ae ht]
  change (∫ x, inner ℝ (u x) (φ x) + inner ℝ (u' x) (φ x) ∂μ) -
    (∫ x, inner ℝ (f x) (φ x) + inner ℝ (f' x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, (∫ x, r s x ∂μ) + (∫ x, r' s x ∂μ)
  have hi : IntegrableOn (fun s => ∫ x, r s x ∂μ) (Set.Ioc a t) := h.2.2.2.1
  have hi' : IntegrableOn (fun s => ∫ x, r' s x ∂μ) (Set.Ioc a t) := h'.2.2.2.1
  rw [integral_add h.1 h'.1, integral_add h.2.1 h'.2.1,
    integral_add hi hi']
  have he : (∫ x, inner ℝ (u x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, r s x ∂μ := h.2.2.2.2
  have he' : (∫ x, inner ℝ (u' x) (φ x) ∂μ) - (∫ x, inner ℝ (f' x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, r' s x ∂μ := h'.2.2.2.2
  linarith

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The weak equation depends on the total internal and external flux. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reassigning flux between coupling and forcing leaves the actual spatial form unchanged. -/
theorem weakIdentityRhs_flux_reallocation_ae (μ : Measure (Vec 2)) (ν s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E)
    (hf : (fun x => flux s x + F s x) =ᵐ[μ] fun x => flux' s x + F' s x) :
    weakIdentityRhs ν v φ dφ du flux F g s =ᵐ[μ]
      weakIdentityRhs ν v φ dφ du flux' F' g s := by
  filter_upwards [hf] with x hx
  simp only [weakIdentityRhs, ← PiLp.add_apply, hx]

/-- A total-flux readout preserves every field of the integrated weak identity. -/
theorem coupledWeakIdentity_flux_reallocation (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u₀ f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E)
    (hf : ∀ s ∈ Set.Ioc a t,
      (fun x => flux s x + F s x) =ᵐ[μ] fun x => flux' s x + F' s x)
    (h : CoupledWeakIdentity μ ν a t v u₀ f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v u₀ f φ dφ du flux' F' g := by
  apply coupledWeakIdentity_integrands_congr μ ν a t v v _ _ _ _ _ _ _ _
    _ _ flux flux' F F' g g Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ h
  intro s hs
  exact weakIdentityRhs_flux_reallocation_ae μ ν s v φ dφ du flux flux' F F' g (hf s hs)
end

/-! Every atom of the coupled weak right side respects its spatial almost-everywhere class. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weakIdentityRhs_congr_ae (μ : Measure (Vec 2)) (ν s : ℝ)
    (v v' : ℝ → Vec 2 → Vec 2) (φ φ' : Vec 2 → E) (dφ dφ' : Fin 2 → Vec 2 → E)
    (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g g' : ℝ → Vec 2 → E)
    (hv : v s =ᵐ[μ] v' s) (hφ : φ =ᵐ[μ] φ')
    (hdφ : ∀ k, dφ k =ᵐ[μ] dφ' k) (hdu : ∀ k, du s k =ᵐ[μ] du' s k)
    (hflux : flux s =ᵐ[μ] flux' s) (hF : F s =ᵐ[μ] F' s) (hg : g s =ᵐ[μ] g' s) :
    weakIdentityRhs ν v φ dφ du flux F g s =ᵐ[μ] weakIdentityRhs ν v' φ' dφ' du' flux' F' g' s := by
  have hdφ' : ∀ᵐ x ∂μ, ∀ k, dφ k x = dφ' k x := ae_all_iff.mpr hdφ
  have hdu' : ∀ᵐ x ∂μ, ∀ k, du s k x = du' s k x := ae_all_iff.mpr hdu
  filter_upwards [hv, hφ, hdφ', hdu', hflux, hF, hg] with x hxv hxφ hxdφ hxdu hxfl hxF hxg
  simp only [weakIdentityRhs, hxv, hxφ, hxdφ, hxdu, hxfl, hxF, hxg]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Scaling the actual solution and forcing scales the literal PDE right-hand side. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weakIdentityRhs_smul (c ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (g : ℝ → Vec 2 → E) (s : ℝ) (x : Vec 2) :
    weakIdentityRhs ν v φ dφ (c • du) (c • flux) (c • F) (c • g) s x =
      c * weakIdentityRhs ν v φ dφ du flux F g s x := by
  simp only [weakIdentityRhs, Fin.sum_univ_two, Pi.smul_apply, WithLp.ofLp_smul,
    ← smul_add, real_inner_smul_left]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Weak derivative identities on every bounded ball identify a global weak jet. -/

theorem weakPartialDeriv_global_of_balls (i : Fin 2) (u g : Vec 2 → ℝ)
    (h : ∀ R : ℝ, 0 < R → HasWeakPartialDerivOn (Metric.ball (0 : Vec 2) R) i u g) :
    HasWeakPartialDerivOn Set.univ i u g := by
  intro φ hφ hc _
  obtain ⟨R, hr⟩ := hc.isBounded.exists_norm_le
  let r : ℝ := max R 0 + 1
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hs : tsupport φ ⊆ Metric.ball (0 : Vec 2) r := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact (hr x hx).trans_lt (by dsimp [r]; linarith [le_max_left R 0])
  have he := h r hrpos φ hφ hc hs
  have hnot (x : Vec 2) (hx : x ∉ Metric.ball (0 : Vec 2) r) : x ∉ tsupport φ :=
    fun hh => hx (hs hh)
  have hi : (∫ x in Metric.ball (0 : Vec 2) r,
      u x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
      ∫ x, u x * (fderiv ℝ φ x) (basisVec i) ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ (hnot x hx)]
      simp)
  have hj : (∫ x in Metric.ball (0 : Vec 2) r, g x * φ x ∂volume) =
      ∫ x, g x * φ x ∂volume :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : φ x = 0 := by
        by_contra hn
        exact hnot x hx (subset_closure hn)
      rw [hz, mul_zero])
  rw [hi, hj] at he
  simpa only [Measure.restrict_univ] using he

theorem orderedWeakJet_global_of_balls {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ℕ} (D : RawJet2 K E)
    (h : ∀ R : ℝ, 0 < R → HasOrderedWeakJetOn (Metric.ball (0 : Vec 2) R) D) :
    HasOrderedWeakJetOn Set.univ D := by
  intro j w i e
  exact weakPartialDeriv_global_of_balls i _ _ (fun R hR => h R hR j w i e)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Inverse Jacobian columns implement native coordinate differentiation after a chart change. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedCoordinateDerivative (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 2) (g : Vec 2 → E) (y : Vec 2) : E :=
  ∑ b : Fin 2, K y b i • fderiv ℝ g y (basisVec b)

theorem weightedCoordinateDerivative_eq
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (g : Vec 2 → E) (y : Vec 2) :
    weightedCoordinateDerivative K i g y = fderiv ℝ g y (fun b => K y b i) := by
  rw [AVRegularity.ChartTransport.vec2_eq_sum_basisVec (fun b => K y b i)]
  simp only [map_sum, map_smul]
  rfl

theorem weightedCoordinateDerivative_comp
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (Υ : Vec 2 → Vec 2) (g : Vec 2 → E) (y : Vec 2)
    (hΥ : DifferentiableAt ℝ Υ y) (hg : DifferentiableAt ℝ g (Υ y))
    (hK : fderiv ℝ Υ y (fun b => K y b i) = basisVec i) :
    weightedCoordinateDerivative K i (g ∘ Υ) y = fderiv ℝ g (Υ y) (basisVec i) := by
  rw [weightedCoordinateDerivative_eq, fderiv_comp y hg hΥ]
  change fderiv ℝ g (Υ y) (fderiv ℝ Υ y (fun b => K y b i)) = _
  rw [hK]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual zero plane carrier has every measurable or nonmeasurable scalar-weighted moment. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem zeroPlaneJet_weight_memLp (q : Vec 2 → ℝ) (a : JetIndex2 K) :
    MemLp (fun y => q y • (0 : PlaneHk Set.univ K E).toFunction.jet a y) 2 volume := by
  have he := Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2)))
  simp only [Measure.restrict_univ] at he
  apply (MemLp.zero' (μ := (volume : Measure (Vec 2))) (p := 2) (ε := E)).ae_eq
  filter_upwards [he] with y hy
  change (0 : E) = q y • ((0 : Lp E 2 (volume.restrict (Set.univ : Set (Vec 2)))) y)
  rw [hy]
  simp only [Pi.zero_apply, smul_zero]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The finite set attached to a singleton time consists exactly of pieces whose output contains that time. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem piece_time_finset_mem_iff (F : ChartedFamily ι h D P Ctx) (t : ℝ) (p : P) :
    p ∈ (F.locally_finite t t).toFinset ↔ t ∈ (F.piece p).output := by
  classical
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨r, hr, hrr⟩
    have he : r = t := le_antisymm hrr.2 hrr.1
    simpa only [he] using hr
  · intro hp
    exact ⟨t, hp, le_rfl, le_rfl⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The literal coupled weak identity assembles from individual spacetime image readouts. -/

variable {E N J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Countable N]

theorem coupledWeakIdentity_integral_image_assembly (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hiu : Integrable (fun x => inner ℝ (u x) (φ x)) μ)
    (hif : Integrable (fun x => inner ℝ (f x) (φ x)) μ)
    (hir : ∀ s ∈ Set.Ioc a t, Integrable (weakIdentityRhs ν v φ dφ du flux F g s) μ)
    (S : Finset J) (uImage fImage : N → ℝ)
    (hu : Summable uImage) (hf : Summable fImage)
    (huReadout : (∑' n, uImage n) = ∫ x, inner ℝ (u x) (φ x) ∂μ)
    (hfReadout : (∑' n, fImage n) = ∫ x, inner ℝ (f x) (φ x) ∂μ)
    (atoms : J → N → ℝ → ℝ)
    (hi : ∀ j ∈ S, ∀ n, IntegrableOn (atoms j n) (Set.Ioc a t))
    (hs : ∀ j ∈ S, Summable (fun n => ∫ s in Set.Ioc a t, ‖atoms j n s‖))
    (he : ∀ n, uImage n - fImage n = ∫ s in Set.Ioc a t, ∑ j ∈ S, atoms j n s)
    (G : J → ℝ → ℝ) (hG : ∀ j ∈ S, IntegrableOn (G j) (Set.Ioc a t))
    (hreadout : ∀ j ∈ S, (∑' n, ∫ s in Set.Ioc a t, atoms j n s) =
      ∫ s in Set.Ioc a t, G j s)
    (hr : (fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F g s x ∂μ) =ᵐ[
      volume.restrict (Set.Ioc a t)] fun s => ∑ j ∈ S, G j s) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g := by
  obtain ⟨hTime, hEquation⟩ := finite_weakEquation_integral_readout
    (volume.restrict (Set.Ioc a t)) S uImage fImage hu hf atoms hi hs he G hG hreadout
  refine ⟨hiu, hif, hir, hTime.congr hr.symm, ?_⟩
  rw [huReadout, hfReadout] at hEquation
  exact hEquation.trans (integral_congr_ae hr.symm)

end AVRegularity.CycleJointProofs
end
end
