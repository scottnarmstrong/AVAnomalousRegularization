-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Factorial-norm bounds for the formal adjoints of the coarse calculus.

* `TorusAdj.FBound A ρ Cf`: the adjoint maps of `A` are bounded by `Cf` in the factorial norms of
  radius `ρ` (input at order `K + m`, output at order `K`), for every admissible `K`.
* `GAdj T m' Kc ρ Cg`: a formal adjoint of an operator `T` of order `m' + 1` in gradient form,
  bounded by `Cg` times the factorial norm of the first derivatives of the input. The identity is
  required for smooth periodic test fields only. Operators in divergence form `T = ∑ⱼ ∂ⱼ Sⱼ` have
  such adjoints, `-∑ⱼ Sⱼ^* ∂ⱼ`; this is how the coarse response fluxes are controlled by the
  gradient part of the energy. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The factorial-norm bound of a formal adjoint. -/
def TorusAdj.FBound {T : (Vec 2 → F) → (Vec 2 → E)} {m R Kc : ℕ} {C : ℝ}
    (A : TorusAdj T m R Kc C) (ρ Cf : ℝ) : Prop :=
  ∀ K (hK : K + m ≤ Kc) (U : TorusHk (K + m) E),
    Real.sqrt (factorialNormSq ρ (A.adj K hK U).val) ≤ Cf * Real.sqrt (factorialNormSq ρ U.val)

/-- The factorial norm of the first derivatives of a periodic Sobolev field. -/
def gradNormSq {K : ℕ} (ρ : ℝ) (U : TorusHk (K + 1) E) : ℝ :=
  ∑ j : Fin 2, factorialNormSq ρ (derivativeTorusHk (K := K) (r := 1) (fun _ => j) U).val

/-- A formal adjoint in gradient form, of an operator of order `m' + 1`. -/
structure GAdj (T : (Vec 2 → F) → (Vec 2 → E)) (m' Kc : ℕ) (ρ Cg : ℝ) where
  /-- The adjoint maps. -/
  adj : ∀ K, K + (m' + 1) ≤ Kc → TorusHk (K + (m' + 1)) E →L[ℝ] TorusHk K F
  /-- The gradient bound in factorial norms. -/
  gbound : ∀ K (hK : K + (m' + 1) ≤ Kc) (U : TorusHk (K + (m' + 1)) E),
    Real.sqrt (factorialNormSq ρ (adj K hK U).val) ≤ Cg * Real.sqrt (gradNormSq (K := K + m') ρ U)
  /-- The adjoint identity on smooth periodic test fields. -/
  ident : ∀ K (hK : K + (m' + 1) ≤ Kc) (U : TorusHk (K + (m' + 1)) E) (ψ : Vec 2 → F),
    ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
    cellInner (tval (adj K hK U)) ψ = cellInner (tval U) (T ψ)
end

/-! The factorial norm as a seminorm on periodic Sobolev fields: triangle inequality, scalar
homogeneity, finite sums, truncation and order casts. The factorial norm is the Hilbert norm of the
weighted jet `a ↦ √(w_{|a|}) • D a`, which is linear in `D`. -/

section
section Jet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {μ : Measure (Vec 2)} {K : ℕ}

omit [BorelSpace E] [CompleteSpace E]

/-- The weighted jet whose Hilbert norm is the factorial norm. -/
def fjet (ρ : ℝ) (D : JetL2 μ K E) : JetL2 μ K E :=
  WithLp.toLp 2 (fun a => Real.sqrt (factorialWeight ρ a.1.val) • D a)

omit [InnerProductSpace ℝ E] in
theorem factorialNormSq_eq_sum_index (ρ : ℝ) (D : JetL2 μ K E) :
    factorialNormSq ρ D = ∑ a : JetIndex2 K, factorialWeight ρ a.1.val * ‖D a‖ ^ 2 := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [Finset.mul_sum]
  exact (Fintype.sum_sigma (fun a : JetIndex2 K => factorialWeight ρ a.1.val * ‖D a‖ ^ 2)).symm

theorem norm_fjet_sq (ρ : ℝ) (D : JetL2 μ K E) : ‖fjet ρ D‖ ^ 2 = factorialNormSq ρ D := by
  rw [PiLp.norm_sq_eq_of_L2, factorialNormSq_eq_sum_index]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ‖Real.sqrt (factorialWeight ρ a.1.val) • D a‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (factorialWeight_nonneg _ _)]

theorem sqrt_factorialNormSq_eq (ρ : ℝ) (D : JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ D) = ‖fjet ρ D‖ := by
  rw [← norm_fjet_sq, Real.sqrt_sq (norm_nonneg _)]

theorem fjet_add (ρ : ℝ) (D D' : JetL2 μ K E) : fjet ρ (D + D') = fjet ρ D + fjet ρ D' := by
  refine PiLp.ext fun a => ?_
  exact smul_add _ _ _

theorem fjet_smul (ρ c : ℝ) (D : JetL2 μ K E) : fjet ρ (c • D) = c • fjet ρ D := by
  refine PiLp.ext fun a => ?_
  exact smul_comm (Real.sqrt (factorialWeight ρ a.1.val)) c (D a)

theorem fjet_zero (ρ : ℝ) : fjet ρ (0 : JetL2 μ K E) = 0 := by
  refine PiLp.ext fun a => ?_
  exact smul_zero _

theorem fjet_neg (ρ : ℝ) (D : JetL2 μ K E) : fjet ρ (-D) = -fjet ρ D := by
  have := fjet_smul ρ (-1) D
  simpa using this

theorem sqrt_fNSq_add_le (ρ : ℝ) (D D' : JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (D + D')) ≤
      Real.sqrt (factorialNormSq ρ D) + Real.sqrt (factorialNormSq ρ D') := by
  rw [sqrt_factorialNormSq_eq, sqrt_factorialNormSq_eq, sqrt_factorialNormSq_eq, fjet_add]
  exact norm_add_le _ _

theorem sqrt_fNSq_smul (ρ c : ℝ) (D : JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (c • D)) = |c| * Real.sqrt (factorialNormSq ρ D) := by
  rw [sqrt_factorialNormSq_eq, sqrt_factorialNormSq_eq, fjet_smul, norm_smul, Real.norm_eq_abs]

theorem sqrt_fNSq_neg (ρ : ℝ) (D : JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (-D)) = Real.sqrt (factorialNormSq ρ D) := by
  rw [sqrt_factorialNormSq_eq, sqrt_factorialNormSq_eq, fjet_neg, norm_neg]

theorem sqrt_fNSq_zero (ρ : ℝ) : Real.sqrt (factorialNormSq ρ (0 : JetL2 μ K E)) = 0 := by
  rw [sqrt_factorialNormSq_eq, fjet_zero, norm_zero]

theorem sqrt_fNSq_truncate_le (ρ : ℝ) {L : ℕ} (hKL : K ≤ L) (D : JetL2 μ L E) :
    Real.sqrt (factorialNormSq ρ (truncateJet hKL D)) ≤ Real.sqrt (factorialNormSq ρ D) := by
  refine Real.sqrt_le_sqrt ?_
  rw [factorialNormSq_eq_sum_index, factorialNormSq_eq_sum_index]
  exact sum_comp_le_sum_nonneg (truncateJetIndex hKL) (truncateJetIndex_injective hKL)
    (fun b : JetIndex2 L => factorialWeight ρ b.1.val * ‖D b‖ ^ 2)
    (fun b => mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _))

end Jet

section Torus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem torus_val_add (U V : TorusHk K E) : (U + V).val = U.val + V.val := rfl

theorem torus_val_smul (c : ℝ) (U : TorusHk K E) : (c • U).val = c • U.val := rfl

theorem torus_val_neg (U : TorusHk K E) : (-U).val = -U.val := rfl

theorem torus_val_zero : (0 : TorusHk K E).val = 0 := rfl

theorem sqrt_fNSq_torus_add_le (ρ : ℝ) (U V : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (U + V).val) ≤
      Real.sqrt (factorialNormSq ρ U.val) + Real.sqrt (factorialNormSq ρ V.val) := by
  rw [torus_val_add]; exact sqrt_fNSq_add_le ρ _ _

theorem sqrt_fNSq_torus_smul (ρ c : ℝ) (U : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (c • U).val) = |c| * Real.sqrt (factorialNormSq ρ U.val) := by
  rw [torus_val_smul]; exact sqrt_fNSq_smul ρ c _

theorem sqrt_fNSq_torus_neg (ρ : ℝ) (U : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (-U).val) = Real.sqrt (factorialNormSq ρ U.val) := by
  rw [torus_val_neg]; exact sqrt_fNSq_neg ρ _

theorem sqrt_fNSq_torus_zero (ρ : ℝ) : Real.sqrt (factorialNormSq ρ (0 : TorusHk K E).val) = 0 := by
  rw [torus_val_zero]; exact sqrt_fNSq_zero ρ

theorem sqrt_fNSq_torus_sum_le {ι : Type*} (ρ : ℝ) (s : Finset ι) (f : ι → TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (∑ i ∈ s, f i).val) ≤
      ∑ i ∈ s, Real.sqrt (factorialNormSq ρ (f i).val) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (sqrt_fNSq_torus_zero ρ).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sqrt_fNSq_torus_add_le ρ _ _).trans (add_le_add le_rfl ih)

theorem sqrt_fNSq_torus_truncate_le (ρ : ℝ) {L : ℕ} (hKL : K ≤ L) (U : TorusHk L E) :
    Real.sqrt (factorialNormSq ρ (truncateTorusHk hKL U).val) ≤
      Real.sqrt (factorialNormSq ρ U.val) :=
  sqrt_fNSq_truncate_le ρ hKL U.val

theorem sqrt_fNSq_torusCast {L : ℕ} (ρ : ℝ) (h : K = L) (U : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (torusCast h U).val) = Real.sqrt (factorialNormSq ρ U.val) := by
  subst h; rfl

end Torus
end

/-! Closure rules for `TorusAdj.FBound`: reindexing, monotonicity, truncation, constants, linear
combinations and composition. Rules that multiply a bound (`liftOrder`, `comp`) need the relevant
constant to be nonnegative. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

namespace TorusAdj.FBound

variable {T T' T₁ T₂ : (Vec 2 → F) → (Vec 2 → E)} {m m' R Kc : ℕ} {C C₁ C₂ : ℝ} {ρ : ℝ}
  {Cf Cf₁ Cf₂ : ℝ}

theorem ofOp (h : T = T') {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) :
    (A.ofOp h).FBound ρ Cf := by
  subst h; exact hA

theorem ofOrder (h : m = m') {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) :
    (A.ofOrder h).FBound ρ Cf := by
  subst h; exact hA

theorem mono_const {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) {Cf' : ℝ} (h : Cf ≤ Cf') :
    A.FBound ρ Cf' := fun K hK U =>
  (hA K hK U).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

theorem mono {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) {R' Kc' : ℕ} (hR : R' ≤ R)
    (hKc : Kc' ≤ Kc) {C' : ℝ} (hC : C ≤ C') : (A.mono hR hKc hC).FBound ρ Cf :=
  fun K hK U => hA K (hK.trans hKc) U

theorem liftOrder {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) (hCf : 0 ≤ Cf) (hm : m ≤ m') :
    (A.liftOrder hm).FBound ρ Cf := fun K hK U =>
  (hA K (by omega) (truncateTorusHk (Nat.add_le_add_left hm K) U)).trans
    (mul_le_mul_of_nonneg_left (sqrt_fNSq_torus_truncate_le ρ _ U) hCf)

theorem zero (m R Kc : ℕ) (ρ : ℝ) :
    (TorusAdj.zero (E := E) (F := F) m R Kc).FBound ρ 0 := fun K hK U => by
  change Real.sqrt (factorialNormSq ρ (0 : TorusHk K F).val) ≤ _
  rw [sqrt_fNSq_torus_zero, zero_mul]

theorem id (R Kc : ℕ) (ρ : ℝ) : (TorusAdj.id (E := E) R Kc).FBound ρ 1 := fun K hK U => by
  rw [one_mul]; exact le_rfl

theorem add {A₁ : TorusAdj T₁ m R Kc C₁} {A₂ : TorusAdj T₂ m R Kc C₂}
    (h₁ : A₁.FBound ρ Cf₁) (h₂ : A₂.FBound ρ Cf₂) : (A₁.add A₂).FBound ρ (Cf₁ + Cf₂) :=
  fun K hK U => by
    change Real.sqrt (factorialNormSq ρ (A₁.adj K hK U + A₂.adj K hK U).val) ≤ _
    rw [add_mul]
    exact (sqrt_fNSq_torus_add_le ρ _ _).trans (add_le_add (h₁ K hK U) (h₂ K hK U))

theorem neg {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) : A.neg.FBound ρ Cf :=
  fun K hK U => by
    change Real.sqrt (factorialNormSq ρ (-A.adj K hK U).val) ≤ _
    rw [sqrt_fNSq_torus_neg]; exact hA K hK U

theorem sub {A₁ : TorusAdj T₁ m R Kc C₁} {A₂ : TorusAdj T₂ m R Kc C₂}
    (h₁ : A₁.FBound ρ Cf₁) (h₂ : A₂.FBound ρ Cf₂) : (A₁.sub A₂).FBound ρ (Cf₁ + Cf₂) :=
  ofOp _ (add h₁ h₂.neg)

theorem smul (c : ℝ) {A : TorusAdj T m R Kc C} (hA : A.FBound ρ Cf) :
    (A.smul c).FBound ρ (|c| * Cf) := fun K hK U => by
  change Real.sqrt (factorialNormSq ρ (c • A.adj K hK U).val) ≤ _
  rw [sqrt_fNSq_torus_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hA K hK U) (abs_nonneg c)

theorem sum {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)} {C Cf : ι → ℝ}
    {A : ∀ i, TorusAdj (T i) m R Kc (C i)} (hA : ∀ i, (A i).FBound ρ (Cf i)) :
    (TorusAdj.sum s A).FBound ρ (∑ i ∈ s, Cf i) := fun K hK U => by
  change Real.sqrt (factorialNormSq ρ ((∑ i ∈ s, (A i).adj K hK) U).val) ≤ _
  rw [sum_apply, Finset.sum_mul]
  exact (sqrt_fNSq_torus_sum_le ρ s _).trans (Finset.sum_le_sum fun i _ => hA i K hK U)

theorem sumMem {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)} {C Cf : ι → ℝ}
    {A : ∀ i ∈ s, TorusAdj (T i) m R Kc (C i)} (hA : ∀ i (hi : i ∈ s), (A i hi).FBound ρ (Cf i)) :
    (TorusAdj.sumMem s A).FBound ρ (∑ i ∈ s, Cf i) := by
  have h := FBound.sum (Finset.univ : Finset s) (T := fun i : s => T i.1)
    (C := fun i : s => C i.1) (Cf := fun i : s => Cf i.1) (A := fun i => A i.1 i.2)
    (fun i => hA i.1 i.2)
  have h2 := (h.mono le_rfl le_rfl (le_of_eq (by rw [Finset.sum_coe_sort s C]) :
    (∑ i : s, C i.1) ≤ ∑ i ∈ s, C i)).mono_const (le_of_eq (Finset.sum_coe_sort s Cf))
  unfold TorusAdj.sumMem
  exact ofOp _ h2

theorem comp {T₁ : (Vec 2 → G) → (Vec 2 → E)} {T₂ : (Vec 2 → F) → (Vec 2 → G)}
    {m₁ m₂ R₁ R₂ : ℕ} {A₁ : TorusAdj T₁ m₁ R₁ Kc C₁} {A₂ : TorusAdj T₂ m₂ R₂ Kc C₂}
    (h₁ : A₁.FBound ρ Cf₁) (h₂ : A₂.FBound ρ Cf₂) (hCf₂ : 0 ≤ Cf₂) {R : ℕ}
    (hR₁ : R ≤ R₁) (hR₂ : R + m₁ ≤ R₂) :
    (A₁.comp A₂ hR₁ hR₂).FBound ρ (Cf₁ * Cf₂) := fun K hK U => by
  change Real.sqrt (factorialNormSq ρ (A₂.adj K (by omega)
    (A₁.adj (K + m₂) (by omega) (torusCast (by omega : K + (m₁ + m₂) = K + m₂ + m₁) U))).val) ≤ _
  refine (h₂ K _ _).trans ?_
  have h3 := h₁ (K + m₂) (by omega) (torusCast (by omega : K + (m₁ + m₂) = K + m₂ + m₁) U)
  rw [sqrt_fNSq_torusCast] at h3
  calc Cf₂ * Real.sqrt (factorialNormSq ρ (A₁.adj (K + m₂) _ (torusCast _ U)).val)
      ≤ Cf₂ * (Cf₁ * Real.sqrt (factorialNormSq ρ U.val)) := mul_le_mul_of_nonneg_left h3 hCf₂
    _ = Cf₁ * Cf₂ * Real.sqrt (factorialNormSq ρ U.val) := by ring

end TorusAdj.FBound
end

end AVRegularity.CycleComparison.Coarse
end
