-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.CycleComparison.Lift.FirstDiagonalSource
public import AVRegularity.CycleEvolution.CellPeriodicSliceGraphFluxSlice

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! One finite-order constant controls all mixed bilinear subjets. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_mixed_bilinear_uniform_graded_le_at_slow_point (p q r s : ℕ)
    (lam A B : ℝ) (hlam : 0 ≤ lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (T : E →L[ℝ] F →L[ℝ] G) (hT : ‖T‖ ≤ 1)
    (f : Vec 2 → Vec 2 → E) (g : Vec 2 → Vec 2 → F)
    (hf : IsBoxSmooth p q f) (hg : IsBoxSmooth p q g) (X : Vec 2)
    (hbf : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ A * lam ^ (r + a))
    (hbg : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (g Y) z) X‖ ≤ B * lam ^ (s + a)) :
    ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => T (f Y y) (g Y y)) z) X‖ ≤
        (2 ^ (p + 2 * q) * A * B) * lam ^ (r + s + a) := by
  intro a ha b hb z
  have hh := norm_mixed_bilinear_graded_le_at_slow_point a r s lam A B hlam hA hB
    T hT X b f g (hf.mono ha hb) (hg.mono ha hb)
    (fun i hi j hj y => hbf i (hi.trans ha) j (hj.trans hb) y)
    (fun i hi j hj y => hbg i (hi.trans ha) j (hj.trans hb) y) z
  apply hh.trans
  gcongr
  norm_num
end

/-! Both first cross-diffusion terms spend exactly one slow and one fast jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem crossDiffusion_mixed_grading_at_slow_point (p q δ : ℕ) (lam M C : ℝ)
    (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (g : Vec 2 → Vec 2 → ℝ) (hg : IsBoxSmooth (p + 1) q g)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (X : Vec 2)
    (hbg : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (g Y) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (i j : Fin 2) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => g Y y • fastPartial i (slowPartial j f) Y y +
        slowPartial i (fun Z w => g Z w • fastPartial j f Z w) Y y) z) X‖ ≤
      ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C) * lam ^ ((δ + 1) + p) := by
  let T : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hslow : IsBoxSmooth p (q + 1) (slowPartial j f) := hf.slowPartial j
  have hfastslow : IsBoxSmooth p q (fastPartial i (slowPartial j f)) := hslow.fastPartial i
  have hbslow := slowPartial_mixed_grading_at_slow_point p (q + 1) δ lam C f hf X hbf j
  have hbfastslow := fastPartial_mixed_grading_at_slow_point p q (δ + 1) lam C
    (slowPartial j f) hslow X hbslow i
  have hfirst : IsBoxSmooth p q (fun Y y => g Y y • fastPartial i (slowPartial j f) Y y) :=
    isBoxSmooth_bilinear (hg.mono (by omega) le_rfl) hfastslow T
  have hbfirst := norm_mixed_bilinear_uniform_graded_le_at_slow_point p q 0 (δ + 1)
    lam M C hlam hM hC T ContinuousLinearMap.opNorm_lsmul_le g
    (fastPartial i (slowPartial j f)) (hg.mono (by omega) le_rfl) hfastslow X
    (fun a ha b hb y => by simpa only [Nat.zero_add] using hbg a (by omega) b hb y) hbfastslow
  have hfast : IsBoxSmooth (p + 1) q (fastPartial j f) := hf.fastPartial j
  have hbfast := fastPartial_mixed_grading_at_slow_point (p + 1) q δ lam C f hf X hbf j
  have hprod : IsBoxSmooth (p + 1) q (fun Y y => g Y y • fastPartial j f Y y) :=
    isBoxSmooth_bilinear hg hfast T
  have hbprod := norm_mixed_bilinear_uniform_graded_le_at_slow_point (p + 1) q 0 δ
    lam M C hlam hM hC T ContinuousLinearMap.opNorm_lsmul_le g (fastPartial j f)
    hg hfast X (by simpa only [Nat.zero_add] using hbg) hbfast
  have hbsecond := slowPartial_mixed_grading_at_slow_point p q δ lam
    (2 ^ ((p + 1) + 2 * q) * M * C) (fun Y y => g Y y • fastPartial j f Y y) hprod X
    (by simpa only [T, Nat.zero_add] using! hbprod) i p le_rfl q le_rfl z
  have hbfirst' : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => g Y y • fastPartial i (slowPartial j f) Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * M * C) * lam ^ ((δ + 1) + p) := by
    simpa only [T, Nat.zero_add] using! hbfirst p le_rfl q le_rfl z
  apply (norm_mixed_jet_add_le hfirst (hprod.slowPartial i) X z).trans
  calc
    _ ≤ (2 ^ (p + 2 * q) * M * C) * lam ^ ((δ + 1) + p) +
        (2 ^ ((p + 1) + 2 * q) * M * C) * lam ^ ((δ + 1) + p) := add_le_add hbfirst' hbsecond
    _ = _ := by ring
end

/-! Normalized mixed bounds recover raw test bounds with a local exponential factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_exponential_denormalized_le (p q δ : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f) (X : Vec 2)
    (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • f Y y) z) X‖ ≤ C * lam ^ (δ + a))
    (a b : ℕ) (ha : a ≤ p) (hbq : b ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤
      (Real.exp ((lam • A) X) * (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * C)) *
        lam ^ (δ + a) := by
  let g : Vec 2 → Vec 2 → E := fun Y y => (Real.exp ((lam • A) Y))⁻¹ • f Y y
  have hg : IsBoxSmooth p q g := by
    have he := isBoxSmooth_slow_field p q (fun Y => Real.exp (-((lam • A) Y)))
      (Real.contDiff_exp.comp ((lam • A).contDiff.neg))
    simpa only [g, Real.exp_neg, ContinuousLinearMap.lsmul_apply] using!
      isBoxSmooth_bilinear he hf (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have he : (fun Y y => Real.exp ((lam • A) Y) • g Y y) = f := by
    funext Y y
    simp only [g, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hh := norm_mixed_exponential_smul_graded_le p q δ A lam C hlam hC g hg X hb
    a b ha hbq z
  have he' (Y : Vec 2) : (fun y => Real.exp ((lam • A) Y) • g Y y) = f Y :=
    congrFun he Y
  simpa only [he'] using hh
end

/-! The local exponential factor cancels after normalization, including every slow derivative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_exponential_normalized_le (p q δ : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p q f) (X : Vec 2)
    (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤
        (Real.exp ((lam • A) X) * C) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • f Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * C) * lam ^ (δ + p) := by
  have he (Y y : Vec 2) : (Real.exp ((lam • A) Y))⁻¹ • f Y y =
      Real.exp ((lam • (-A)) Y) • f Y y := by
    rw [show (lam • (-A)) Y = -((lam • A) Y) by
      simp only [smul_apply, neg_apply, smul_eq_mul]; ring, Real.exp_neg]
  simp_rw [he]
  have hC' : 0 ≤ Real.exp ((lam • A) X) * C := mul_nonneg (Real.exp_pos _).le hC
  have hh := norm_mixed_exponential_smul_graded_le p q δ (-A) lam
    (Real.exp ((lam • A) X) * C) hlam hC' f hf X hb p q le_rfl le_rfl z
  apply hh.trans_eq
  have hneg : (lam • (-A)) X = -((lam • A) X) := by
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  have hexp : Real.exp ((lam • (-A)) X) * Real.exp ((lam • A) X) = 1 := by
    rw [hneg, Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]
  simp only [norm_neg] at hh ⊢
  calc
    _ = (Real.exp ((lam • (-A)) X) * Real.exp ((lam • A) X)) *
        ((2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * C) * lam ^ (δ + p)) := by ring
    _ = _ := by rw [hexp, one_mul]
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A finite synthesis of component actions gives the full Pi-valued lift operator. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def liftPiLeftTerms (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) :
    List (LeftTerm (∀ i, h i) (∀ i, h i)) :=
  (Finset.univ.toList : List ι).flatMap fun v =>
    (liftComponentLeftTerms n c t v).map (fun d => d.postcompose (ContinuousLinearMap.single ℝ h v))

theorem liftPiLeftTerms_order (n : ℕ) (c : LiftCoeff ι h) (t : ℝ)
    (d : LeftTerm (∀ i, h i) (∀ i, h i)) (hd : d ∈ liftPiLeftTerms n c t) : d.order ≤ n := by
  obtain ⟨v, _, e, he, rfl⟩ := by simpa only [liftPiLeftTerms, List.mem_flatMap, List.mem_map] using hd
  exact liftComponentLeftTerms_order n c t v e he

theorem liftPiLeftTerms_box (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) (p q : ℕ)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth p q (fun X z => c m α t X z v u))
    (d : LeftTerm (∀ i, h i) (∀ i, h i)) (hd : d ∈ liftPiLeftTerms n c t) : IsBoxSmooth p q d.coeff := by
  obtain ⟨v, _, e, he, rfl⟩ := by simpa only [liftPiLeftTerms, List.mem_flatMap, List.mem_map] using hd
  exact e.postcompose_box _ p q (liftComponentLeftTerms_box n c t v p q
    (fun m hm α u => hc m hm α v u) e he)

theorem liftPiLeftTerms_apply (n : ℕ) (c : LiftCoeff ι h) (t : ℝ)
    (f : Vec 2 → ∀ i, h i) (X z : Vec 2) :
    leftTermsApply (liftPiLeftTerms n c t) f X z = liftApply n c (fun _ => f) t X z := by
  unfold liftPiLeftTerms
  rw [leftTermsApply_finset_flatMap]
  simp_rw [leftTermsApply_map_postcompose, liftComponentLeftTerms_apply]
  ext u
  simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The actual second cross operator spends two slow jets and raises the base grade by two. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB2_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (cellB2 η G t f Y) z) X‖ ≤
      (4 * (2 ^ ((p + 1) + 2 * q) * M * C)) * lam ^ ((δ + 2) + p) := by
  let B := 2 ^ ((p + 1) + 2 * q) * M * C
  let T := fun (i j : Fin 2) => slowPartial i
    (fun Y y => G t Y i j • slowPartial j f Y y)
  have hslow (j : Fin 2) : IsBoxSmooth (p + 1) q (slowPartial j f) := by
    exact (hf.mono (show (p + 1) + 1 ≤ p + 2 by omega) le_rfl).slowPartial j
  have hprod (i j : Fin 2) : IsBoxSmooth (p + 1) q
      (fun Y y => G t Y i j • slowPartial j f Y y) := by
    exact isBoxSmooth_bilinear (hG i j) (hslow j)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hT (i j : Fin 2) : IsBoxSmooth p q (T i j) := (hprod i j).slowPartial i
  have hTb (i j : Fin 2) :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T i j Y) z) X‖ ≤
        B * lam ^ ((δ + 2) + p) := by
    have hsp := slowPartial_mixed_grading_at_slow_point (p + 1) q δ lam C f
      (hf.mono (by omega) le_rfl) X (fun a ha b hb y => hbf a (by omega) b hb y) j
    have hpb := norm_mixed_bilinear_uniform_graded_le_at_slow_point (p + 1) q 0 (δ + 1)
      lam M C hlam hM hC
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
      (ContinuousLinearMap.opNorm_lsmul_le) (fun Y (_ : Vec 2) => G t Y i j)
      (slowPartial j f) (hG i j) (hslow j) X
      (by simpa only [Nat.zero_add] using hbG i j) hsp
    have hh := slowPartial_mixed_grading_at_slow_point p q (δ + 1) lam B
      (fun Y y => G t Y i j • slowPartial j f Y y) (hprod i j) X
      (by simpa only [B, Nat.zero_add] using! hpb) i p le_rfl q le_rfl z
    simpa only [T, show (δ + 1) + 1 = δ + 2 by omega] using hh
  let S := fun Y y => ∑ i : Fin 2, ∑ j : Fin 2, T i j Y y
  have hS : IsBoxSmooth p q S := IsBoxSmooth.sum Finset.univ fun i _ =>
    IsBoxSmooth.sum Finset.univ fun j _ => hT i j
  have he : cellB2 η G t f = fun Y y => (-η) • S Y y := by
    funext Y y
    exact (neg_smul η (S Y y)).symm
  rw [he, norm_mixed_jet_const_smul hS]
  have hsum : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (S Y) z) X‖ ≤
      4 * (B * lam ^ ((δ + 2) + p)) := by
    apply (norm_mixed_jet_finset_sum_le Finset.univ p q _
      (fun i _ => IsBoxSmooth.sum Finset.univ fun j _ => hT i j) X z).trans
    calc
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, B * lam ^ ((δ + 2) + p) :=
        Finset.sum_le_sum fun i _ => (norm_mixed_jet_finset_sum_le Finset.univ p q _
          (fun j _ => hT i j) X z).trans (Finset.sum_le_sum fun j _ => hTb i j)
      _ = _ := by simp; ring
  rw [abs_neg, abs_of_nonneg hη0]
  calc
    _ ≤ ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (S Y) z) X‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hη1
    _ ≤ _ := hsum
    _ = _ := by dsimp only [B]; ring
end

/-! Slow exponential tests preserve vector slow grading with a local factor that cancels in the inverse. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_slow_exponential_smul_graded_le (p δ : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C) (g : Vec 2 → E)
    (hg : ContDiff ℝ (p : ℕ∞) g) (X : Vec 2)
    (hb : ∀ a ≤ p, ‖iteratedFDeriv ℝ a g X‖ ≤ C * lam ^ (δ + a))
    (a : ℕ) (ha : a ≤ p) :
    ‖iteratedFDeriv ℝ a (fun Y => Real.exp ((lam • A) Y) • g Y) X‖ ≤
      (Real.exp ((lam • A) X) * (2 ^ p * (max 1 ‖A‖) ^ p * C)) * lam ^ (δ + a) := by
  have hh := norm_mixed_exponential_smul_graded_le p 0 δ A lam C hlam hC
    (fun Y (_ : Vec 2) => g Y) (isBoxSmooth_slow_field p 0 g hg) X
    (fun r hr s _ y => (norm_mixed_slow_field_le r s g X y).trans (hb r hr)) a 0 ha le_rfl 0
  simpa only [norm_mixed_fast_zero_eq, Nat.mul_zero, Nat.add_zero] using hh
end

/-! The first cross bound uses the scaled drift jets w = sqrt eta v, so its constant is independent of eta. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_scaled_drift_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M W C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => Real.sqrt η * v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (cellB1 η G v t f Y) z) X‖ ≤
      (2 * (2 ^ (p + 2 * q) * W * C) +
        4 * ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C)) *
          lam ^ ((δ + 1) + p) := by
  let J := 2 ^ (p + 2 * q) * W * C
  let K := (2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C
  let U := fun (k : Fin 2) (Y y : Vec 2) => (Real.sqrt η * v t y k) • slowPartial k f Y y
  let T := fun (i j : Fin 2) (Y y : Vec 2) =>
    G t Y i j • fastPartial i (slowPartial j f) Y y +
      slowPartial i (fun Z w => G t Z i j • fastPartial j f Z w) Y y
  have hU (k : Fin 2) : IsBoxSmooth p q (U k) :=
    isBoxSmooth_bilinear (hv k) ((hf.slowPartial k).mono le_rfl (by omega))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hUb (k : Fin 2) :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (U k Y) z) X‖ ≤
        J * lam ^ ((δ + 1) + p) := by
    have hbslow := slowPartial_mixed_grading_at_slow_point p q δ lam C f
      (hf.mono le_rfl (by omega)) X (fun a ha b hb y => hbf a ha b (by omega) y) k
    have hh := norm_mixed_bilinear_uniform_graded_le_at_slow_point p q 0 (δ + 1)
      lam W C hlam hW hC (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
      ContinuousLinearMap.opNorm_lsmul_le (fun (_ : Vec 2) y => Real.sqrt η * v t y k) (slowPartial k f)
      (hv k) ((hf.slowPartial k).mono le_rfl (by omega)) X
      (by simpa only [Nat.zero_add] using hbv k) hbslow
    simpa only [U, J, Nat.zero_add] using! hh p le_rfl q le_rfl z
  have hT (i j : Fin 2) : IsBoxSmooth p q (T i j) := by
    have hfirst := isBoxSmooth_bilinear ((hG i j).mono (by omega) le_rfl)
      ((hf.slowPartial j).fastPartial i)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    have hsecond := (isBoxSmooth_bilinear (hG i j) (hf.fastPartial j)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)).slowPartial i
    exact hfirst.add hsecond
  have hTb (i j : Fin 2) :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T i j Y) z) X‖ ≤
        K * lam ^ ((δ + 1) + p) :=
    crossDiffusion_mixed_grading_at_slow_point p q δ lam M C hlam hM hC
      (fun Y (_ : Vec 2) => G t Y i j) (hG i j) f hf X (hbG i j) hbf i j z
  let Afield := fun Y y => ∑ k : Fin 2, U k Y y
  let Bfield := fun Y y => ∑ i : Fin 2, ∑ j : Fin 2, T i j Y y
  have hA : IsBoxSmooth p q Afield := IsBoxSmooth.sum Finset.univ fun k _ => hU k
  have hB : IsBoxSmooth p q Bfield := IsBoxSmooth.sum Finset.univ fun i _ =>
    IsBoxSmooth.sum Finset.univ fun j _ => hT i j
  have he : cellB1 η G v t f = fun Y y => Afield Y y - Real.sqrt η • Bfield Y y := by
    funext Y y
    simp only [cellB1, Afield, Bfield, U, T]
  rw [he]
  have hAn : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (Afield Y) z) X‖ ≤
      2 * (J * lam ^ ((δ + 1) + p)) := by
    apply (norm_mixed_jet_finset_sum_le Finset.univ p q U (fun k _ => hU k) X z).trans
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hUb k)
    simpa using hh
  have hBn : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (Bfield Y) z) X‖ ≤
      4 * (K * lam ^ ((δ + 1) + p)) := by
    apply (norm_mixed_jet_finset_sum_le Finset.univ p q _
      (fun i _ => IsBoxSmooth.sum Finset.univ fun j _ => hT i j) X z).trans
    calc
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, K * lam ^ ((δ + 1) + p) :=
        Finset.sum_le_sum fun i _ => (norm_mixed_jet_finset_sum_le Finset.univ p q _
          (fun j _ => hT i j) X z).trans (Finset.sum_le_sum fun j _ => hTb i j)
      _ = _ := by simp; ring
  have hsqrt : Real.sqrt η ≤ 1 := by simpa using Real.sqrt_le_sqrt hη
  have hscaled : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => Real.sqrt η • Bfield Y y) z) X‖ ≤
        4 * (K * lam ^ ((δ + 1) + p)) := by
    rw [norm_mixed_jet_const_smul hB, abs_of_nonneg (Real.sqrt_nonneg η)]
    exact (mul_le_of_le_one_left (norm_nonneg _) hsqrt).trans hBn
  apply (norm_mixed_jet_sub_le hA (hB.const_smul (Real.sqrt η)) X z).trans
  apply (add_le_add hAn hscaled).trans_eq
  dsimp only [J, K]
  ring
end

/-! The actual second cross operator spends two slow jets and raises the base grade by two. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB2_uniform_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    : ∀ r ≤ p, ∀ s ≤ q, ∀ z,
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (cellB2 η G t f Y) z) X‖ ≤
      (4 * (2 ^ ((p + 1) + 2 * q) * M * C)) * lam ^ ((δ + 2) + r) := by
  intro r hr s hs z
  have hh := cellB2_mixed_grading_at_slow_point r s δ η lam M C hη0 hη1 hlam hM hC
    G t f (hf.mono (by omega) hs) (fun i j => (hG i j).mono (by omega) hs) X
    (fun i j a ha b hb y => hbG i j a (by omega) b (hb.trans hs) y)
    (fun a ha b hb y => hbf a (by omega) b (hb.trans hs) y) z
  apply hh.trans
  gcongr
  norm_num
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Symmetric averaged block coefficients act as the mean of the finite differential terms. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def leftTermsMeanBlockCoefficient (l : ∀ v, List (LeftTerm (∀ i, h i) (h v))) : LiftCoeff ι h :=
  liftCoefficientCellMean (leftTermsBlockCoefficient l)

theorem leftTermsMeanBlockCoefficient_perm (l : ∀ v, List (LeftTerm (∀ i, h i) (h v)))
    (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    leftTermsMeanBlockCoefficient l m (α ∘ σ) = leftTermsMeanBlockCoefficient l m α :=
  liftCoefficientCellMean_perm _ m (leftTermsBlockCoefficient_perm l m) α σ

theorem leftTermsMeanBlockCoefficient_apply
    (l : ∀ v, List (LeftTerm (∀ i, h i) (h v))) (n : ℕ)
    (hl : ∀ v, ∀ c ∈ l v, c.order ≤ n)
    (hb : ∀ v, ∀ c ∈ l v, IsBoxSmooth 0 0 c.coeff)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (leftTermsMeanBlockCoefficient l) (fun _ => f) t X z v =
      fieldCellMean (fun z => leftTermsApply (l v) f X z) := by
  unfold leftTermsMeanBlockCoefficient
  rw [liftCoefficientCellMean_apply n _ _ t X z v
    (fun m _ α u => (leftTermsBlockCoefficient_box l 0 0 hb m α t v u).1 X |>.continuous)]
  congr 1
  funext z
  exact leftTermsBlockCoefficient_apply l n hl f hf t X z v

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The actual first cross operator raises the source grade by one with a fixed finite-order constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_scaled_drift_uniform_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M W C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => Real.sqrt η * v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    : ∀ r ≤ p, ∀ s ≤ q, ∀ z,
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (cellB1 η G v t f Y) z) X‖ ≤
      (2 * (2 ^ (p + 2 * q) * W * C) +
        4 * ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C)) *
          lam ^ ((δ + 1) + r) := by
  intro r hr s hs z
  have hh := cellB1_scaled_drift_mixed_grading_at_slow_point r s δ η lam M W C hη hlam hM hW hC
    G v t f (hf.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) hs) (fun k => (hv k).mono hr hs) X
    (fun i j a ha b hb y => hbG i j a (by omega) b (hb.trans hs) y)
    (fun k a ha b hb y => hbv k a (ha.trans hr) b (hb.trans hs) y)
    (fun a ha b hb y => hbf a (by omega) b (by omega) y) z
  apply hh.trans
  gcongr <;> norm_num

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The Riesz generator commutes actual scalar-forced cell derivatives with absolute Fourier
sums. -/

def cellGeneratorDualCLM (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) : TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (cellGeneratorForm C hG V hv hb t)

theorem cellGeneratorDualCLM_pairing (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    inner ℝ (cellGeneratorDualCLM C hG V hv hb t u) z = cellGeneratorForm C hG V hv hb t u z := by
  exact InnerProductSpace.toDual_symm_apply

theorem cellDualDerivative_scalar_source (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u S (fun _ => 0) =
      cellGeneratorDualCLM C hG V hv hb t u + cellPivotDualCLM S := by
  apply ext_inner_right ℝ
  intro z
  rw [cellDualDerivative_pairing, inner_add_left, cellGeneratorDualCLM_pairing]
  have hp := ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)) z S
  change inner ℝ (cellPivotDualCLM S) z = inner ℝ S (torusHkValueCLM z) at hp
  rw [hp]
  simp only [cellSourceFunctional, map_zero, ContinuousLinearMap.zero_comp, Finset.sum_const_zero,
    sub_zero, ContinuousLinearMap.comp_apply, coe_innerSL_apply]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Normalized exponential tests preserve the second cross operator's two grading powers. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedCellB2MixedConstant (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M C : ℝ) : ℝ :=
  (2 ^ (p + 2 * q) * max 1 ‖A‖ ^ p) *
    (4 * (2 ^ ((p + 1) + 2 * q) * M *
      (2 ^ ((p + 2) + 2 * q) * max 1 ‖A‖ ^ (p + 2) * C)))

theorem normalizedCellB2_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      normalizedCellB2MixedConstant p q A M C * lam ^ ((δ + 2) + p) := by
  let Cexp := 2 ^ ((p + 2) + 2 * q) * max 1 ‖A‖ ^ (p + 2) * C
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  let U := 4 * (2 ^ ((p + 1) + 2 * q) * M * Cexp)
  have hU : 0 ≤ U := by positivity
  have hΦ : IsBoxSmooth (p + 2) q Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦb := norm_mixed_exponential_smul_graded_le (p + 2) q δ A lam C hlam hC f hf X hbf
  have hh := cellB2_uniform_mixed_grading_at_slow_point p q δ η lam M
    (Real.exp ((lam • A) X) * Cexp) hη0 hη1 hlam hM (by positivity)
    G t Φ hΦ hG X hbG (fun a ha b hb y => hΦb a b ha hb y)
  have hb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (cellB2 η G t Φ Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * U) * lam ^ ((δ + 2) + a) := by
    intro a ha b hb y
    apply (hh a ha b hb y).trans_eq
    dsimp only [U]
    ring
  have hn := norm_mixed_exponential_normalized_le p q (δ + 2) A lam U hlam hU
    (cellB2 η G t Φ) (cellB2_box_reserve p q η G t Φ hΦ hG) X hb z
  apply hn.trans_eq
  rfl

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A tested derivative cancels its left coefficient's order deficit in the exact mixed grading. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_mixed_operator_ordered_input_graded_le (p q n m δ : ℕ) (hm : m ≤ n)
    (α : DerivativeWord2 m) (c : Vec 2 → Vec 2 → E →L[ℝ] F) (g : Vec 2 → E)
    (hc : IsBoxSmooth p q c) (hg : ContDiff ℝ ((p + m : ℕ) : ℕ∞) g)
    (X z : Vec 2) (lam B C : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbc : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (c Y) y) X‖ ≤ B * lam ^ (n - m + a))
    (hbg : ∀ a ≤ p + m, ‖iteratedFDeriv ℝ a g X‖ ≤ C * lam ^ (δ + a)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => c Y y (orderedDerivative α g Y)) z) X‖ ≤
      (2 ^ (p + 2 * q) * B * C) * lam ^ (n + δ + p) := by
  have hd := AVRegularity.contDiff_orderedDerivative α hg
  have hbox := isBoxSmooth_slow_field p q (orderedDerivative α g) hd
  have hbound : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun _ : Vec 2 => orderedDerivative α g Y) y) X‖ ≤ C * lam ^ (δ + m + a) := by
    intro a ha b _ y
    apply (norm_mixed_slow_field_le a b (orderedDerivative α g) X y).trans
    have hga : ContDiff ℝ ((a + m : ℕ) : ℕ∞) g :=
      hg.of_le (by exact_mod_cast Nat.add_le_add_right ha m)
    have hh := (AVRegularity.norm_iteratedFDeriv_orderedDerivative_le α hga X).trans
      (hbg (a + m) (by omega))
    simpa only [Nat.add_assoc, Nat.add_comm m a] using hh
  have hh := norm_mixed_bilinear_graded_le_at_slow_point p (n - m) (δ + m) lam B C
    hlam hB hC (ContinuousLinearMap.id ℝ (E →L[ℝ] F)) ContinuousLinearMap.norm_id_le X q
    c (fun Y (_ : Vec 2) => orderedDerivative α g Y) hc hbox hbc hbound z
  have he : (n - m) + (δ + m) + p = n + δ + p := by omega
  simpa only [ContinuousLinearMap.id_apply, he] using! hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Common-reserve coefficient states depend only on the actual window, including their clamped values. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
  {c d : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem AmbientLiftCoefficientData.congr_on_window
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (heq : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      ∀ t ∈ Set.Icc a b, ∀ X z, d m α t X z v u = c m α t X z v u) :
    AmbientLiftCoefficientData par a b hab lam n p q d M := by
  have he m (hm : m ≤ n) α v u t (ht : t ∈ Set.Icc a b) :
      (fun X z => d m α t X z v u) = fun X z => c m α t X z v u :=
    funext fun X => funext fun z => heq m hm α v u t ht X z
  refine ⟨data.nonneg, ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    rw [he m hm α v u t ht]
    exact data.box m hm α v u t ht
  · intro m hm α v u r hr s hs t ht X z
    have hej : (fun Y => iteratedFDeriv ℝ s (fun y => d m α t Y y v u) z) =
        fun Y => iteratedFDeriv ℝ s (fun y => c m α t Y y v u) z := by
      funext Y
      exact congrArg (fun f : Vec 2 → (h u →L[ℝ] h v) => iteratedFDeriv ℝ s f z)
        (congrFun (he m hm α v u t ht) Y)
    rw [hej]
    exact data.bound m hm α v u r hr s hs t ht X z
  · intro m hm α v u t ht X z s
    exact (heq m hm α v u t ht X (z + s • basisVec par)).trans
      ((data.transverse m hm α v u t ht X z s).trans (heq m hm α v u t ht X z).symm)
  · intro m hm α v u l X z
    have hej : (fun t => l (d m α (Set.projIcc a b hab t) X z v u)) =
        fun t => l (c m α (Set.projIcc a b hab t) X z v u) := by
      funext t
      exact congrArg l (heq m hm α v u _ (Set.projIcc a b hab t).2 X z)
    rw [hej]
    exact data.measurable m hm α v u l X z
end

/-! Actual normalized inverse sources carry the analytic and geometric premises in one state. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

structure AmbientLiftSourceData (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hh n p q : ℕ) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (M : ι → ι → ℝ) : Prop where
  constant_nonneg : ∀ A, 0 ≤ K A
  matrix_nonneg : ∀ v u, 0 ≤ M v u
  box : ∀ A u v ξ, ∀ t ∈ Set.Icc a b,
    IsBoxSmooth p q (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t)
  bound : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
        (K A * M v u * ‖ξ‖) * lam ^ (n + r)
  transverse : ∀ A u v ξ, IsTransverseOn par (Set.Icc a b)
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
  measurable : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z,
    Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
      (Set.projIcc a b hab t) X z))
  periodic : ∀ A u v ξ, ∀ t ∈ Set.Icc a b, ∀ X,
    AVenhance.IsZ2Periodic (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X)
  centered : ∀ A u v ξ, ∀ t ∈ Set.Icc a b, ∀ X,
    fieldCellMean (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) = 0
end

/-! The actual uncentered source state used simultaneously with the coefficient induction. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def normalizedLiftUncenteredField (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (u v : ι) (ξ : h u) : ℝ → Vec 2 → Vec 2 → h v :=
  fun t X z => (Real.exp (A X))⁻¹ • liftA Q Cc
    (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z v

structure AmbientLiftUncenteredData (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hh n p q : ℕ) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (M : ι → ι → ℝ) : Prop where
  constant_nonneg : ∀ A, 0 ≤ K A
  matrix_nonneg : ∀ v u, 0 ≤ M v u
  box : ∀ A u v ξ, ∀ t ∈ Set.Icc a b,
    IsBoxSmooth p q (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t)
  bound : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
        (K A * M v u * ‖ξ‖) * lam ^ (n + r)
  transverse : ∀ A u v ξ, IsTransverseOn par (Set.Icc a b)
    (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ)
  measurable : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z,
    Measurable (fun t => l (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ
      (Set.projIcc a b hab t) X z))
  periodic : ∀ A u v ξ, ∀ t ∈ Set.Icc a b, ∀ X,
    AVenhance.IsZ2Periodic (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t X)

theorem AmbientLiftUncenteredData.mono {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
    {hh n p q p' q' : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {K : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (hp : p' ≤ p) (hq : q' ≤ q) :
    AmbientLiftUncenteredData par a b hab lam hh n p' q' Q Cc K M := by
  refine ⟨data.constant_nonneg, data.matrix_nonneg, ?_, ?_,
    data.transverse, data.measurable, data.periodic⟩
  · intro A u v ξ t ht
    exact (data.box A u v ξ t ht).mono hp hq
  · intro A u v ξ r hr s hs t ht X z
    exact data.bound A u v ξ r (hr.trans hp) s (hs.trans hq) t ht X z
end

/-! The literal zero coefficient array has every ambient reserve and zero matrix budget. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem ambient_zero_coefficient_data (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (n p q : ℕ) :
    AmbientLiftCoefficientData par a b hab lam n p q (0 : LiftCoeff ι h) (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_rfl, ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    exact IsBoxSmooth.zero
  · intro m hm α v u r hr s hs t ht X z
    simp
  · intro m hm α v u t ht X z s
    rfl
  · intro m hm α v u l X z
    simpa only [Pi.zero_apply, map_zero] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The existing good-field calculus gives classical continuity of both cross-operator outputs. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_continuous_slice (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (hw : ∀ q : Fin 2, Continuous (fun z => Real.sqrt η * v t z q))
    (Φ : Vec 2 → Vec 2 → E) (hΦ : GoodField 2 Φ) (X : Vec 2) :
    Continuous (fun z => cellB1 η G v t Φ X z) := by
  have hslow := fun j => hΦ.slowPartial (r := 1) j
  have hfast := fun j => hΦ.fastPartial (r := 1) j
  apply Continuous.sub
  · exact continuous_finsetSum _ fun q _ => (hw q).smul ((hslow q).continuous_slice X)
  · apply continuous_const.smul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (continuous_const.smul (((hslow j).fastPartial (r := 0) i).continuous_slice X)).add
      ((((hfast j).mulX (hG i j)).slowPartial (r := 0) i).continuous_slice X)

theorem cellB2_continuous_slice (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (Φ : Vec 2 → Vec 2 → E) (hΦ : GoodField 2 Φ) (X : Vec 2) :
    Continuous (fun z => cellB2 η G t Φ X z) := by
  apply Continuous.neg
  apply continuous_const.smul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((((hΦ.slowPartial (r := 1) j).mulX (hG i j)).slowPartial (r := 0) i).continuous_slice X)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Normalized exponential tests give an exact polynomial in the direction scale. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalized_exponential_lift_polynomial (n : ℕ) (c : LiftCoeff ι h)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) (ε : ℝ) :
    (Real.exp ((ε • A) X))⁻¹ •
      liftApply n c (fun _ Y => Real.exp ((ε • A) Y) • Pi.single u ξ) t X z v =
    ∑ m ∈ Finset.range (n + 1), ε ^ m •
      ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun j => A (basisVec j))).prod • c m α t X z v u ξ := by
  rw [liftApply_exponential_single, smul_smul,
    inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [wordSymbol_smul, smul_smul]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Normalized parameter derivatives identify the actual finite polynomial coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_polynomial_coefficient (q j : ℕ) (P : ℕ → E)
    (hz : ∀ i, q < i → P i = 0) :
    ((j.factorial : ℝ)⁻¹) •
      iteratedDeriv j (fun ε : ℝ => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i) 0 = P j := by
  rw [iteratedDeriv_epsPoly]
  by_cases hj : j ≤ q
  · simp [hj, Nat.factorial_ne_zero]
  · simp [hj, hz j (by omega)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Polynomial good fields may be multiplied by periodic coefficients depending on both variables. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem goodField_smul_field {r : ℕ} {g : Vec 2 → Vec 2 → ℝ} {Φ : Vec 2 → Vec 2 → E}
    (hg : GoodField r g) (hΦ : GoodField r Φ) :
    GoodField r (fun X z => g X z • Φ X z) :=
  ⟨hg.1.smul hΦ.1, fun X n z => by
    change g X (z + AVenhance.latticeShift n) • Φ X (z + AVenhance.latticeShift n) = _
    rw [hg.2 X n z, hΦ.2 X n z]⟩

theorem epsPoly_smul_field {q r : ℕ} {g : Vec 2 → Vec 2 → ℝ}
    {Ψ : ℝ → Vec 2 → Vec 2 → E} (hg : GoodField r g) (hΨ : EpsPoly False q r Ψ) :
    EpsPoly False q r (fun ε X z => g X z • Ψ ε X z) := by
  obtain ⟨P, hP, hz, he⟩ := hΨ
  refine ⟨fun i X z => g X z • P i X z,
    fun i => ⟨goodField_smul_field hg (hP i).1, False.elim⟩,
    fun i hi X z => by
      change g X z • P i X z = 0
      rw [hz i hi X z, smul_zero], ?_⟩
  intro ε X z
  change g X z • Ψ ε X z = ∑ i ∈ Finset.range (q + 1), ε ^ i • (g X z • P i X z)
  simp only [he, Finset.smul_sum, smul_comm (g X z)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Copy-adapt the compiled covariant polynomial recursion, retaining its explicit coefficient array. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dEps_finite_polynomial_expand (q : ℕ) (P : ℕ → Vec 2 → Vec 2 → E)
    (hP : ∀ i, GoodField 1 (P i)) (hz : ∀ i, q < i → P i = fun _ _ => 0)
    (η ε : ℝ) (k : Fin 2) (X z : Vec 2) :
    dEps η ε k (fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i Y y) X z =
      ∑ i ∈ Finset.range (q + 2), ε ^ i •
        (fastPartial k (P i) X z +
          if i = 0 then 0 else Real.sqrt η • slowPartial k (P (i - 1)) X z) := by
  have hg : ∀ i ∈ Finset.range (q + 1), GoodField 1 (P i) := fun i _ => hP i
  simp only [dEps]
  rw [fastPartial_sum_smul _ _ _ hg, slowPartial_sum_smul _ _ _ hg]
  have hA : (∑ i ∈ Finset.range (q + 2), ε ^ i • fastPartial k (P i) X z) =
      ∑ i ∈ Finset.range (q + 1), ε ^ i • fastPartial k (P i) X z := by
    rw [show q + 2 = (q + 1) + 1 by omega, Finset.sum_range_succ]
    rw [hz (q + 1) (by omega)]
    simp only [fastPartial_zero, smul_zero, add_zero]
  have hB : (∑ i ∈ Finset.range (q + 2), ε ^ i •
      (if i = 0 then (0 : E) else Real.sqrt η • slowPartial k (P (i - 1)) X z)) =
      (Real.sqrt η * ε) • ∑ i ∈ Finset.range (q + 1), ε ^ i • slowPartial k (P i) X z := by
    rw [show q + 2 = (q + 1) + 1 by omega, Finset.sum_range_succ', Finset.smul_sum]
    simp only [Nat.add_one_ne_zero, ite_false, ite_true, smul_zero, add_zero, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, smul_smul]
    congr 1
    ring
  simp only [smul_add, Finset.sum_add_distrib]
  rw [hA, hB]

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Paired actual inverse sources inherit geometry from the two proved native source states. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {Q Qi : LiftOperatorData ι h D} {Cc Ci : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {hh n p q : ℕ}
  {K Ki : (Vec 2 →L[ℝ] ℝ) → ℝ} {M Mi : ι → ι → ℝ}

theorem ambient_paired_source_geometry
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc K M)
    (datai : AmbientLiftSourceData par a b hab lam hh n p q Qi Ci Ki Mi)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) :
    let f := fun t X z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z -
      normalizedLiftSourceField Qi Ci hh n (lam • A) u v ξ t X z
    (∀ t ∈ Set.Icc a b, IsBoxSmooth p q (f t)) ∧
    IsTransverseOn par (Set.Icc a b) f ∧
    (∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b hab t) X z))) ∧
    (∀ t ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (f t X)) ∧
    (∀ t ∈ Set.Icc a b, ∀ X, fieldCellMean (f t X) = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (data.box A u v ξ t ht).sub (datai.box A u v ξ t ht)
  · intro t ht X z s
    exact congrArg₂ (fun x y => x - y)
      (data.transverse A u v ξ t ht X z s)
      (datai.transverse A u v ξ t ht X z s)
  · intro l X z
    simp_rw [map_sub]
    exact (data.measurable A u v ξ l X z).sub (datai.measurable A u v ξ l X z)
  · intro t ht X j z
    exact congrArg₂ (fun x y => x - y)
      (data.periodic A u v ξ t ht X j z) (datai.periodic A u v ξ t ht X j z)
  · intro t ht X
    rw [fieldCellMean_sub ((data.box A u v ξ t ht).1 X).continuous
      ((datai.box A u v ξ t ht).1 X).continuous,
      data.centered A u v ξ t ht X, datai.centered A u v ξ t ht X, sub_self]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Scalar differentiation extracts each homogeneous tested order from the actual lift. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem homogeneous_lift_symbol_extraction (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    ((m.factorial : ℝ)⁻¹) • iteratedDeriv m
      (fun ε : ℝ => (Real.exp ((ε • A) X))⁻¹ •
        liftApply n c (fun _ Y => Real.exp ((ε • A) Y) • Pi.single u ξ) t X z v) 0 =
      ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun j => A (basisVec j))).prod • c m α t X z v u ξ := by
  have he := funext (normalized_exponential_lift_polynomial n c A t X z v u ξ)
  rw [he, iteratedDeriv_epsPoly]
  simp only [hm, ite_true, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast m.factorial_ne_zero), one_smul]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Normalized exponential tests preserve the first cross operator's single grading power. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB1_scaled_drift_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M W C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      normalizedCellB1MixedConstant p q A M W C * lam ^ ((δ + 1) + p) := by
  let Cexp := 2 ^ ((p + 1) + 2 * (q + 1)) * max 1 ‖A‖ ^ (p + 1) * C
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  let U := 2 * (2 ^ (p + 2 * q) * W * Cexp) +
    4 * ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * Cexp)
  have hU : 0 ≤ U := by positivity
  have hΦ : IsBoxSmooth (p + 1) (q + 1) Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦb := norm_mixed_exponential_smul_graded_le (p + 1) (q + 1) δ A lam C hlam hC f hf X hbf
  have hh := cellB1_scaled_drift_uniform_mixed_grading_at_slow_point p q δ η lam M W
    (Real.exp ((lam • A) X) * Cexp) hη hlam hM hW (by positivity)
    G v t Φ hΦ hG (fun k => (hv k).const_smul (Real.sqrt η)) X hbG hbv (fun a ha b hb y => hΦb a b ha hb y)
  have hb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (cellB1 η G v t Φ Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * U) * lam ^ ((δ + 1) + a) := by
    intro a ha b hb y
    apply (hh a ha b hb y).trans_eq
    dsimp only [U]
    ring
  have hn := norm_mixed_exponential_normalized_le p q (δ + 1) A lam U hlam hU
    (cellB1 η G v t Φ) (cellB1_box_reserve p q η G v t Φ hΦ hG hv) X hb z
  apply hn.trans_eq
  rfl

end AVRegularity.CycleComparison.Lift
end
end
