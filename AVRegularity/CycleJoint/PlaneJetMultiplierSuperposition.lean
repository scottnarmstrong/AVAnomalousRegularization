-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleWords.SmoothPullbackDifference
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A finite Leibniz bound for one native order-lowering step. -/

theorem transitionT_cons_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (I A : List (Fin 2)) (i : Fin 2) (n : ℕ) (C M : ℝ)
    (hKC : ∀ a b j, j ≤ n → ∀ x, ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (hTM : ∀ Q j, j ≤ n + 1 → ∀ x, ‖iteratedFDeriv ℝ j (transitionT K I Q) x‖ ≤ M)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (transitionT K (i :: I) A) x‖ ≤
      3 * (n + 1 : ℕ) * 2 ^ n * C * M := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hKC 0 0 0 (Nat.zero_le _) x)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hTM [] 0 (Nat.zero_le _) x)
  let P := (n + 1 : ℕ) * (2 : ℝ) ^ n * C * M
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hT (Q : List (Fin 2)) := transitionT_spatial_smooth K hK I Q
  have hD (b : Fin 2) : ContDiff ℝ (n : ℕ)
      (fun y => fderiv ℝ (transitionT K I A) y (basisVec b)) :=
    ((hT A).fderiv_right (by simp)).clm_apply contDiff_const
  have hp (b : Fin 2) :
      ‖iteratedFDeriv ℝ n (fun y => K y b i * fderiv ℝ (transitionT K I A) y (basisVec b)) x‖ ≤ P := by
    apply uniform_product_jet_bound _ _ x n ((hK b i).of_le (by simp)) (hD b) C M
    · intro j hj
      exact hKC b i j hj x
    · intro j hj
      apply (directional_derivative_jet_norm_le (transitionT K I A) j
        ((hT A).of_le (by simp)) x b).trans
      exact hTM A (j + 1) (Nat.add_le_add_right hj 1) x
  have hs : ‖iteratedFDeriv ℝ n (fun y => ∑ b : Fin 2,
      K y b i * fderiv ℝ (transitionT K I A) y (basisVec b)) x‖ ≤ 2 * P := by
    apply (finite_jet_sum_norm_le _ n (fun b => ((hK b i).of_le (by simp)).mul (hD b)) x).trans
    calc
      _ ≤ ∑ _b : Fin 2, P := Finset.sum_le_sum (fun b _ => hp b)
      _ = _ := by simp
  have heP : 3 * (n + 1 : ℕ) * 2 ^ n * C * M = 3 * P := by dsimp [P]; ring
  rw [heP]
  cases A with
  | nil =>
    have he : transitionT K (i :: I) [] = (fun y => ∑ b : Fin 2,
        K y b i * fderiv ℝ (transitionT K I []) y (basisVec b)) := by
      funext y
      simp only [transitionT, add_zero]
    rw [he]
    apply hs.trans
    change 2 * P ≤ 3 * P
    linarith
  | cons a A =>
    have hq : ‖iteratedFDeriv ℝ n (fun y => K y a i * transitionT K I A y) x‖ ≤ P := by
      apply uniform_product_jet_bound _ _ x n ((hK a i).of_le (by simp))
        ((hT A).of_le (by simp)) C M
      · intro j hj
        exact hKC a i j hj x
      · intro j hj
        exact hTM A j (hj.trans (Nat.le_succ _)) x
    have hh := finite_jet_add_norm_le
      (fun y : Vec 2 => ∑ b : Fin 2, K y b i *
        fderiv ℝ (transitionT K I (a :: A)) y (basisVec b))
      (fun y : Vec 2 => K y a i * transitionT K I A y) n
      (ContDiff.sum (fun b _ => ((hK b i).of_le (by simp)).mul (hD b)))
      (((hK a i).of_le (by simp)).mul ((hT A).of_le (by simp))) x
    change ‖iteratedFDeriv ℝ n (transitionT K (i :: I) (a :: A)) x‖ ≤ _ at hh
    apply hh.trans
    apply (add_le_add hs hq).trans
    change 2 * P + P ≤ 3 * P
    linarith

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Original charted constituents inherit the molecular cell reserve budget on whole-label slices. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyPointwiseMolecular_mixed_reserve (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ t : ℝ, ∀ a b : ℕ, a + b ≤ K v →
      (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' =>
          iteratedFDeriv ℝ b (F.flux p c v u γ d I t X') z) X‖ *
          derivativeReserveFactor (ρ / e) (K v) (d - 2) ≤
        ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
          ((ν * ρ ^ (d - 2)) *
            (((K v).factorial : ℝ) / ((K v + (d - 2)).factorial : ℝ)))) *
          (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)).toReal := by
  have hM := pointwiseMolecularEnvelope_constituent_jet_ne_top F π hπ K dom ν e E ρ hν he hρ
    C J b₀ henv v u γ hγ d hd I j hj
  intro t a b hab hdom X z
  have hf (t : ℝ) (ht : ∀ Y : Vec 2, (t, Y) ∈ dom p c) :
      IsBoxSmooth (j + a) b (F.flux p c v u γ d I t) := by
    apply Weighted.isBoxSmooth_of_joint_contDiff
    have hh := CycleWords.molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t ht v u γ d I
    exact hh.of_le (by exact_mod_cast (by omega : j + a + b ≤ K v + J))
  exact pointwiseMolecularNative_mixed_reserve ν e E ρ hν he hE hρ (K v) (d - 2)
    j a b hab (fun x : F.Index => dom x.1 x.2)
    (fun x => F.flux x.1 x.2 v u γ d I) ⟨p, c⟩ hf hM t hdom X z

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact component L2 prices of cell dilation on rough native jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierAffine_component_norm_sq (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    ‖(planeCarrierAffine e he y U).val a‖ ^ 2 =
      (‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹|) * ‖U.val a‖ ^ 2 := by
  rw [CoupledEnergyPlane.L2Indicator.norm_sq_eq_integral (𝕜 := ℝ),
    CoupledEnergyPlane.L2Indicator.norm_sq_eq_integral (𝕜 := ℝ)]
  simp only [Measure.restrict_univ]
  calc
    (∫ z : Vec 2, ‖((planeCarrierAffine e he y U).val a : Vec 2 → E) z‖ ^ 2) =
        ∫ z : Vec 2, ‖e ^ a.1.val • U.toFunction.jet a (y + e • z)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [planeCarrierAffine_jet_ae e he y U a] with z hz
      exact congrArg (fun v : E => ‖v‖ ^ 2) hz
    _ = ‖e ^ a.1.val‖ ^ 2 * ∫ z : Vec 2, ‖U.toFunction.jet a (y + e • z)‖ ^ 2 := by
      simp only [norm_smul, mul_pow]
      rw [integral_const_mul]
    _ = (‖e ^ a.1.val‖ ^ 2 * |(e ^ 2)⁻¹|) * ∫ x : Vec 2, ‖(U.val a : Vec 2 → E) x‖ ^ 2 := by
      rw [integral_plane_affine e he y (fun x => ‖U.toFunction.jet a x‖ ^ 2)]
      change ‖e ^ a.1.val‖ ^ 2 * (|(e ^ 2)⁻¹| * _) = _
      rw [mul_assoc]
      rfl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Taylor and word chains continue every level through the seam with its full trace. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Every response level retains its actual seam value; higher levels are not reset to zero. -/
theorem planeChainFrom_restart_subwindow {D N : ℕ} (cd : PlaneChainData ι h D N)
    (κ : Fin (N + 1) → ι → ℕ) (a b c d : ℝ)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ j i, PlaneHk Set.univ (κ j i) (h i))
    (F : ∀ j i, ℝ → PlaneHk Set.univ (κ j i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ j i, ℝ → PlaneHk Set.univ (κ j i) (h i))
    (w : ∀ j i, ℝ → PlaneHk Set.univ (κ j i + 1) (h i))
    (hs : IsPlaneChainFrom cd κ a b v f F u w) :
    IsPlaneChainFrom cd κ c d v (fun j i => u j i c) F u w :=
  planeWeakSolution_restart_subwindow (fun p : Fin (N + 1) × ι => κ p.1 p.2)
    D 1 a b c d hac hcd hdb v (planeChainCoefficient cd κ) (fun p => f p.1 p.2)
    (fun p => F p.1 p.2) (fun _ _ => 0) (fun p => u p.1 p.2) (fun p => w p.1 p.2) hs

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every finite native transition array has a uniform jet bound independent of its output word. -/

theorem transitionT_uniform_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hKC : ∀ a b j, j ≤ N → ∀ x, ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (I A : List (Fin 2)) (n : ℕ) (hn : n + I.length ≤ N) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (transitionT K I A) x‖ ≤
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length := by
  induction I generalizing A n x with
  | nil =>
    cases A with
    | nil =>
      cases n with
      | zero => simp [transitionT, norm_iteratedFDeriv_zero]
      | succ n => simp [transitionT, iteratedFDeriv_const_of_ne]
    | cons a A => simp [transitionT]
  | cons i I ih =>
    let B := 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hnn : n ≤ N := by simp only [List.length_cons] at hn; omega
    have hh := transitionT_cons_jet_bound K hK I A i n C (B ^ I.length)
      (fun a b j hj => hKC a b j (hj.trans hnn))
      (fun Q j hj y => ih Q j (by simp only [List.length_cons] at hn; omega) y) x
    apply hh.trans
    have hc : 3 * (n + 1 : ℕ) * (2 : ℝ) ^ n * C ≤ B := by
      dsimp [B]
      have hp : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hnn
      have hcnt : (n + 1 : ℕ) ≤ (N + 1 : ℕ) := Nat.add_le_add_right hnn 1
      have hcntr : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hcnt
      gcongr
    calc
      _ ≤ B * B ^ I.length := mul_le_mul_of_nonneg_right hc (pow_nonneg hB _)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-! The physical native Piola array normalizes to the exact cell-coordinate array. -/

theorem transportedCoeff_cell_normalization
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (D r : ℕ) (hr : 1 ≤ r) (A : DerivativeWord2 r)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (e ν : ℝ) (he : 0 < e) (hν : ν ≠ 0) (yc z : Vec 2) :
    (e * (e ^ r)⁻¹ * ν⁻¹) •
      transportedCoeff K D (fun d I => (ν * e ^ (d - 2)) • B d I) r A (yc + e • z) =
    transportedCoeff (fun x => K (yc + e • x)) D B r A z := by
  funext a
  simp only [transportedCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro i _
  rw [transitionT_affine_sampling K hK yc e he (List.ofFn I) (List.ofFn A) z]
  simp only [List.length_ofFn]
  have hrd : r ≤ d - 1 := by have := (Finset.mem_Icc.mp hd).1; omega
  have hpow : e ^ (((d - 1 : ℕ) : ℤ) - (r : ℤ)) = e ^ (d - 1 - r) := by
    rw [← Int.natCast_sub hrd, zpow_natCast]
  rw [hpow]
  have hscale := nativePiola_cell_prefactor e ν he.ne' hν r d hr (Finset.mem_Icc.mp hd).1
  calc
    _ = ((e * (e ^ r)⁻¹ * ν⁻¹) * (ν * e ^ (d - 2))) *
        (K (yc + e • z) a i * B d I i * transitionT K (List.ofFn I) (List.ofFn A) (yc + e • z)) := by ring
    _ = _ := by rw [hscale]; ring

end AVRegularity.CycleJointProofs
end

section
open AVRegularity.CycleWords Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The bounded slot gives a uniform mixed-jet constant for each positive molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyPointwiseMolecular_uniform_reserve (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J) (p : P) (c : Ctx p) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ a b : ℕ, a + b ≤ K v → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' =>
          iteratedFDeriv ℝ b (F.flux p c v u γ d I t X') z) X‖ *
          derivativeReserveFactor (ρ / e) (K v) (d - 2) ≤
        (Kmax.factorial : ℝ) ^ 2 * E ^ j *
          molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) := by
  intro t hdom a b hab X z
  have ht := familyPointwiseMolecular_mixed_reserve F π hπ K dom ν e E ρ hν he hE hρ
    C J b₀ henv v u γ hγ d hd I j hj p c t
  have hh := ht a b hab hdom X z
  have hKv := hK v
  have ha : (a.factorial : ℝ) ≤ (Kmax.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : a ≤ Kmax)
  have hb : (b.factorial : ℝ) ≤ (Kmax.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : b ≤ Kmax)
  have habf : (a.factorial : ℝ) * (b.factorial : ℝ) ≤ (Kmax.factorial : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul ha hb (by positivity) (by positivity)
  have hid := molecularRealPrice_div_identity ν ρ hν hρ (K v) (d - 2)
    (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  have heq : ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
      ((ν * ρ ^ (d - 2)) *
        (((K v).factorial : ℝ) / ((K v + (d - 2)).factorial : ℝ)))) *
      (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)).toReal =
      (a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j *
        molecularRealPrice ν ρ (K v) (d - 2)
          (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) := by
    rw [← hid]
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right habf (pow_pos hE j).le)
    (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual cell dilation preserves the factorial norm with only the exact plane L2 volume price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrierAffine_factorial_norm_sq (ρ e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) :
    factorialNormSq (ρ / e) (planeCarrierAffine e he y U).val =
      |(e ^ 2)⁻¹| * factorialNormSq ρ U.val := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro w _
  rw [planeCarrierAffine_component_norm_sq]
  calc
    factorialWeight (ρ / e) j.val *
        ((‖e ^ j.val‖ ^ 2 * |(e ^ 2)⁻¹|) * ‖U.val ⟨j, w⟩‖ ^ 2) =
        (factorialWeight (ρ / e) j.val * ‖e ^ j.val‖ ^ 2) *
          (|(e ^ 2)⁻¹| * ‖U.val ⟨j, w⟩‖ ^ 2) := by ring
    _ = |(e ^ 2)⁻¹| * (factorialWeight ρ j.val * ‖U.val ⟨j, w⟩‖ ^ 2) := by
      rw [factorialWeight_affine ρ e he]
      ring

theorem planeCarrierAffine_factorial_norm (ρ e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) :
    Real.sqrt (factorialNormSq (ρ / e) (planeCarrierAffine e he y U).val) =
      |e⁻¹| * Real.sqrt (factorialNormSq ρ U.val) := by
  rw [planeCarrierAffine_factorial_norm_sq, Real.sqrt_mul (abs_nonneg _), ← inv_pow,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_sq_eq_abs]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Literal coefficient multipliers of native jets superpose almost everywhere, including zero orders beyond the carrier reserve. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup X] [Module ℝ X] {K : ℕ}

theorem planeJetOrder_smul_ae (j : ℕ) (I : DerivativeWord2 j)
    (c : ℝ) (U : PlaneHk Set.univ K E) :
    planeJetOrder (c • U) j I =ᵐ[volume] fun z => c • planeJetOrder U j I z := by
  by_cases hj : j ≤ K
  · simp only [planeJetOrder_eq_stored hj]
    exact planeCarrier_jet_smul_ae c U _
  · apply Filter.Eventually.of_forall
    intro z
    simp only [planeJetOrder, dite_eq_right hj, smul_zero]

theorem planeJetOrder_add_all_ae (j : ℕ) (I : DerivativeWord2 j)
    (U V : PlaneHk Set.univ K E) :
    planeJetOrder (U + V) j I =ᵐ[volume]
      fun z => planeJetOrder U j I z + planeJetOrder V j I z := by
  by_cases hj : j ≤ K
  · exact planeJetOrder_add_ae hj U V I
  · apply Filter.Eventually.of_forall
    intro z
    simp only [planeJetOrder, dite_eq_right hj, add_zero]

theorem planeJetMultiplier_curve_superposition
    (μ : Measure ℝ) (c : ℝ → Vec 2 → ℝ) (T : E →L[ℝ] F)
    (j : ℕ) (I : DerivativeWord2 j) (U : X → ℝ → PlaneHk Set.univ K E)
    (hadd : ∀ x y, U (x + y) =ᵐ[μ] fun t => U x t + U y t)
    (hsmul : ∀ (r : ℝ) x, U (r • x) =ᵐ[μ] fun t => r • U x t) :
    (∀ x y, ∀ᵐ t ∂μ,
      (fun z => c t z • T (planeJetOrder (U (x + y) t) j I z)) =ᵐ[volume]
        fun z => c t z • T (planeJetOrder (U x t) j I z) +
          c t z • T (planeJetOrder (U y t) j I z)) ∧
    (∀ (r : ℝ) x, ∀ᵐ t ∂μ,
      (fun z => c t z • T (planeJetOrder (U (r • x) t) j I z)) =ᵐ[volume]
        fun z => r • (c t z • T (planeJetOrder (U x t) j I z))) := by
  constructor
  · intro x y
    filter_upwards [hadd x y] with t ht
    rw [ht]
    filter_upwards [planeJetOrder_add_all_ae j I (U x t) (U y t)] with z hz
    rw [hz, map_add, smul_add]
  · intro r x
    filter_upwards [hsmul r x] with t ht
    rw [ht]
    filter_upwards [planeJetOrder_smul_ae j I r (U x t)] with z hz
    rw [hz, map_smul]
    exact smul_comm (c t z) r _

end AVRegularity.CycleJointProofs
end
