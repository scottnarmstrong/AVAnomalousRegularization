-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleComparison.Reconstruction.GluedTail
public import AVRegularity.Proofs.ComplexChain.Family
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import Mathlib.Combinatorics.Matroid.Basic

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.QuietAtlas

/-! **The formal associativity of the order-lowering recursion** (the Piola leaf of the quiet
matching). `T_{I,A}` (`transitionT`) is the coefficient of the word `∂^A` in the formal Leibniz
expansion of the vector fields `∂'_i = ∑_b K_{bi} ∂_b` applied in the order of `I`, the words
being kept in order. That expansion is associative: if `K₁ = (Dψ)⁻¹` in the sense of `hder` and
`K₃ = K₁ · (K₂ ∘ ψ)`, then `T^{K₃}_{I,A} = ∑_J (T^{K₂}_{I,J} ∘ ψ) T^{K₁}_{J,A}`
(`transitionT_comp`). Hence the transported arrays compose exactly, word by word, at every
lowered order (`transportedCoeff_comp`). Also `T_{I,A} = 0` for `|A| > |I|`
(`transitionT_eq_zero_of_length_lt`), and `T` commutes with translations
(`transitionT_translate`). -/

open CycleComparison.Reconstruction

/-- `T_{I,A} = 0` when `A` is longer than `I`. -/
theorem transitionT_eq_zero_of_length_lt (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (I A : List (Fin 2)), I.length < A.length → transitionT K I A = fun _ => 0
  | [], [], h => absurd h (by simp)
  | [], _ :: _, _ => rfl
  | i :: I, A, h => by
    have h1 : transitionT K I A = fun _ => 0 :=
      transitionT_eq_zero_of_length_lt K I A (by simp only [List.length_cons] at h; omega)
    funext y
    cases A with
    | nil => simp at h
    | cons a A₀ =>
      have h2 : transitionT K I A₀ = fun _ => 0 :=
        transitionT_eq_zero_of_length_lt K I A₀ (by simp only [List.length_cons] at h; omega)
      rw [transitionT_cons_cons_apply, h1, h2]
      simp

/-- `T` commutes with translations. -/
theorem transitionT_translate (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (c : Vec 2) :
    ∀ (I A : List (Fin 2)) (y : Vec 2),
      transitionT (fun h => K (c + h)) I A y = transitionT K I A (c + y)
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | i :: I, A, y => by
    have ih : ∀ A', transitionT (fun h => K (c + h)) I A' = fun y => transitionT K I A' (c + y) :=
      fun A' => funext (transitionT_translate K c I A')
    cases A with
    | nil => simp only [transitionT_cons_nil_apply, ih, fderiv_comp_add_left]
    | cons a A₀ => simp only [transitionT_cons_cons_apply, ih, fderiv_comp_add_left]

/-- The transported array commutes with translations. -/
theorem transportedCoeff_translate (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (c : Vec 2) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff (fun h => K (c + h)) Dγ B r A y = transportedCoeff K Dγ B r A (c + y) := by
  unfold transportedCoeff
  simp only [transitionT_translate]

/-- Summing over the words of length `s + 1`. -/
theorem sum_word_succ_ofFn {M : Type*} [AddCommMonoid M] {s : ℕ} (F : List (Fin 2) → M) :
    ∑ J : DerivativeWord2 (s + 1), F (List.ofFn J) =
      ∑ j : Fin 2, ∑ J : DerivativeWord2 s, F (j :: List.ofFn J) := by
  rw [transition_sum_word_succ]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- The words longer than `I` do not contribute. -/
theorem sum_range_transitionT_eq (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (I : List (Fin 2))
    (X : ∀ r, DerivativeWord2 r → ℝ) {M N : ℕ} (hM : I.length + 1 ≤ M) (hN : M ≤ N)
    (w : Vec 2) :
    ∑ r ∈ Finset.range N, ∑ J : DerivativeWord2 r, transitionT K I (List.ofFn J) w * X r J =
      ∑ r ∈ Finset.range M, ∑ J : DerivativeWord2 r, transitionT K I (List.ofFn J) w * X r J := by
  rw [← Finset.sum_range_add_sum_Ico _ hN]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun J _ => ?_)
  rw [Finset.mem_Ico] at hr
  rw [transitionT_eq_zero_of_length_lt K I _ (by rw [List.length_ofFn]; omega), zero_mul]

/-- The non-derivative part of the recursion. -/
def extraT (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2)) :
    List (Fin 2) → Vec 2 → ℝ
  | [], _ => 0
  | a :: A₀, y => K y a i * transitionT K I A₀ y

theorem transitionT_cons (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I A : List (Fin 2))
    (y : Vec 2) :
    transitionT K (i :: I) A y =
      (∑ b : Fin 2, K y b i * fderiv ℝ (transitionT K I A) y (basisVec b)) + extraT K i I A y := by
  cases A with
  | nil => simp [transitionT, extraT]
  | cons a A₀ => simp [transitionT, extraT]

section Comp

variable {ψ : Vec 2 → Vec 2} {K₁ K₂ : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}

/-- The extra part of the outer recursion, split over the first letter. -/
theorem sum_extraT_succ (i : Fin 2) (I : List (Fin 2)) (A : List (Fin 2)) (M : ℕ) (w y : Vec 2) :
    ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r,
        extraT K₂ i I (List.ofFn J) w * transitionT K₁ (List.ofFn J) A y =
      ∑ r ∈ Finset.range M, ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
        K₂ w j i * (transitionT K₂ I (List.ofFn J) w * transitionT K₁ (j :: List.ofFn J) A y) := by
  rw [Finset.sum_range_succ']
  have h0 : ∑ J : DerivativeWord2 0,
      extraT K₂ i I (List.ofFn J) w * transitionT K₁ (List.ofFn J) A y = 0 :=
    Finset.sum_eq_zero fun J _ => by simp [extraT]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_word_succ_ofFn (fun L => extraT K₂ i I L w * transitionT K₁ L A y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [extraT]
  ring

/-- Extending a range by a top order that does not contribute. -/
theorem sum_range_extend (I : List (Fin 2)) (Z : ∀ r, DerivativeWord2 r → Fin 2 → ℝ)
    (c : Fin 2 → ℝ) {M : ℕ} (hM : I.length + 1 ≤ M) (w : Vec 2) :
    ∑ r ∈ Finset.range M, ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
        c j * (transitionT K₂ I (List.ofFn J) w * Z r J j) =
      ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
        c j * (transitionT K₂ I (List.ofFn J) w * Z r J j) := by
  rw [Finset.sum_range_succ]
  refine (add_eq_left.mpr (Finset.sum_eq_zero fun J _ => Finset.sum_eq_zero fun j _ => ?_)).symm
  rw [transitionT_eq_zero_of_length_lt K₂ I _ (by rw [List.length_ofFn]; omega)]
  simp

/-- **The formal associativity of the recursion.** If `K₁ = (Dψ)⁻¹` in the sense of `hder`, then
`T^{K₁·(K₂∘ψ)}_{I,A} = ∑_J (T^{K₂}_{I,J} ∘ ψ) T^{K₁}_{J,A}` (any range of word lengths beyond
`|I|`). -/
theorem transitionT_comp (hK₁ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => K₁ x a i)
    (hK₂ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => K₂ x a i) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hder : ∀ (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2), DifferentiableAt ℝ f (ψ y) →
      ∑ b : Fin 2, K₁ y b j * fderiv ℝ (f ∘ ψ) y (basisVec b) = fderiv ℝ f (ψ y) (basisVec j)) :
    ∀ (I A : List (Fin 2)) (N : ℕ), I.length + 1 ≤ N → ∀ y : Vec 2,
      transitionT (fun x => K₁ x * K₂ (ψ x)) I A y =
        ∑ r ∈ Finset.range N, ∑ J : DerivativeWord2 r,
          transitionT K₂ I (List.ofFn J) (ψ y) * transitionT K₁ (List.ofFn J) A y
  | [], A, N, hN, y => by
    rw [sum_range_transitionT_eq K₂ [] (fun r J => transitionT K₁ (List.ofFn J) A y) le_rfl hN]
    simp only [List.length_nil, zero_add, Finset.range_one, Finset.sum_singleton,
      Fintype.sum_unique, List.ofFn_zero]
    cases A <;> simp [transitionT]
  | i :: I, A, N, hN, y => by
    have hN' : I.length + 1 ≤ N := by simp only [List.length_cons] at hN; omega
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hM : I.length + 1 ≤ M := by simp only [List.length_cons] at hN; omega
    have ih : ∀ A', transitionT (fun x => K₁ x * K₂ (ψ x)) I A' =
        fun y => ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r,
          (fun x => transitionT K₂ I (List.ofFn J) (ψ x)) y • transitionT K₁ (List.ofFn J) A' y :=
      fun A' => funext fun y =>
        (transitionT_comp hK₁ hK₂ hψ hder I A' (M + 1) hN' y).trans (by simp only [smul_eq_mul])
    have hT1 : ∀ J A', Differentiable ℝ (transitionT K₁ J A') := fun J A' =>
      (AVRegularity.CycleJointProofs.transitionT_spatial_smooth K₁ hK₁ J A').differentiable
        (by simp)
    have hT2' : ∀ J, ContDiff ℝ (⊤ : ℕ∞) (transitionT K₂ I J) := fun J =>
      AVRegularity.CycleJointProofs.transitionT_spatial_smooth K₂ hK₂ I J
    have hT2 : ∀ J, Differentiable ℝ (fun x => transitionT K₂ I J (ψ x)) := fun J =>
      ((hT2' J).comp hψ).differentiable (by simp)
    -- the derivative of the inner expansion
    have hd : ∀ b, fderiv ℝ (transitionT (fun x => K₁ x * K₂ (ψ x)) I A) y (basisVec b) =
        ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r,
          (transitionT K₂ I (List.ofFn J) (ψ y) *
              fderiv ℝ (transitionT K₁ (List.ofFn J) A) y (basisVec b) +
            fderiv ℝ (fun x => transitionT K₂ I (List.ofFn J) (ψ x)) y (basisVec b) *
              transitionT K₁ (List.ofFn J) A y) := by
      intro b
      rw [ih A, transition_fderiv_wordSum_apply (Finset.range (M + 1))
        (fun r J x => transitionT K₂ I (List.ofFn J) (ψ x))
        (fun r J => transitionT K₁ (List.ofFn J) A) (fun r J => hT2 _) (fun r J => hT1 _ _) y
        (basisVec b)]
      simp only [smul_eq_mul]
    -- (a) the derivative part of the outer recursion
    have ha : ∑ b : Fin 2, (K₁ y * K₂ (ψ y)) b i *
          fderiv ℝ (transitionT (fun x => K₁ x * K₂ (ψ x)) I A) y (basisVec b) =
        (∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (transitionT K₂ I (List.ofFn J) (ψ y) *
            ∑ b : Fin 2, K₁ y b j * fderiv ℝ (transitionT K₁ (List.ofFn J) A) y (basisVec b))) +
        ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (fderiv ℝ (transitionT K₂ I (List.ofFn J)) (ψ y) (basisVec j) *
            transitionT K₁ (List.ofFn J) A y) := by
      simp only [hd]
      rw [← Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun J _ => ?_
      have hj : ∀ j : Fin 2, fderiv ℝ (transitionT K₂ I (List.ofFn J)) (ψ y) (basisVec j) =
          ∑ b : Fin 2, K₁ y b j *
            fderiv ℝ (fun x => transitionT K₂ I (List.ofFn J) (ψ x)) y (basisVec b) :=
        fun j => (hder _ y j ((hT2' _).differentiable (by simp) _)).symm
      simp only [hj, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    -- (b) the extra part of the outer recursion
    have hb : extraT (fun x => K₁ x * K₂ (ψ x)) i I A y =
        ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (transitionT K₂ I (List.ofFn J) (ψ y) *
            extraT K₁ j (List.ofFn J) A y) := by
      cases A with
      | nil => simp [extraT]
      | cons a A₀ =>
        simp only [extraT]
        rw [transitionT_comp hK₁ hK₂ hψ hder I A₀ (M + 1) hN' y, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        ring
    -- (c) the derivative part of the inner recursion
    have hc : ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r,
          (∑ b : Fin 2, K₂ (ψ y) b i *
            fderiv ℝ (transitionT K₂ I (List.ofFn J)) (ψ y) (basisVec b)) *
            transitionT K₁ (List.ofFn J) A y =
        ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (fderiv ℝ (transitionT K₂ I (List.ofFn J)) (ψ y) (basisVec j) *
            transitionT K₁ (List.ofFn J) A y) := by
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    -- (d) the extra part of the inner recursion
    have hdd : ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r,
          extraT K₂ i I (List.ofFn J) (ψ y) * transitionT K₁ (List.ofFn J) A y =
        (∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (transitionT K₂ I (List.ofFn J) (ψ y) *
            ∑ b : Fin 2, K₁ y b j * fderiv ℝ (transitionT K₁ (List.ofFn J) A) y (basisVec b))) +
        ∑ r ∈ Finset.range (M + 1), ∑ J : DerivativeWord2 r, ∑ j : Fin 2,
          K₂ (ψ y) j i * (transitionT K₂ I (List.ofFn J) (ψ y) *
            extraT K₁ j (List.ofFn J) A y) := by
      rw [sum_extraT_succ]
      rw [← sum_range_extend I (fun r J j => ∑ b : Fin 2, K₁ y b j *
          fderiv ℝ (transitionT K₁ (List.ofFn J) A) y (basisVec b)) (fun j => K₂ (ψ y) j i) hM,
        ← sum_range_extend I (fun r J j => extraT K₁ j (List.ofFn J) A y)
          (fun j => K₂ (ψ y) j i) hM, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [transitionT_cons K₁ j (List.ofFn J) A y]
      ring
    rw [transitionT_cons, ha, hb]
    simp only [transitionT_cons K₂ i I, add_mul, Finset.sum_add_distrib]
    rw [hc, hdd]
    ring

/-- **The transported arrays compose exactly**, word by word, at every order. -/
theorem transportedCoeff_comp (hK₁ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => K₁ x a i)
    (hK₂ : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) fun x => K₂ x a i) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hder : ∀ (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2), DifferentiableAt ℝ f (ψ y) →
      ∑ b : Fin 2, K₁ y b j * fderiv ℝ (f ∘ ψ) y (basisVec b) = fderiv ℝ f (ψ y) (basisVec j))
    (Dγ : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r)
    (y : Vec 2) :
    transportedCoeff (fun x => K₁ x * K₂ (ψ x)) Dγ B r A y =
      transportedCoeff K₁ Dγ (fun e J => transportedCoeff K₂ Dγ B (e - 1) J (ψ y)) r A y := by
  funext a₀
  set g : ℕ → ℕ → ℝ := fun s d => ∑ J : DerivativeWord2 s, ∑ I : DerivativeWord2 (d - 1),
      (∑ j₀ : Fin 2, ∑ i₀ : Fin 2, K₁ y a₀ j₀ * (K₂ (ψ y) j₀ i₀ * B d I i₀ *
        transitionT K₂ (List.ofFn I) (List.ofFn J) (ψ y))) *
        transitionT K₁ (List.ofFn J) (List.ofFn A) y with hg
  -- the composed recursion, without the words shorter than `A`
  have hT3 : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I : DerivativeWord2 (d - 1),
      transitionT (fun x => K₁ x * K₂ (ψ x)) (List.ofFn I) (List.ofFn A) y =
        ∑ s ∈ Finset.Ico r d, ∑ J : DerivativeWord2 s,
          transitionT K₂ (List.ofFn I) (List.ofFn J) (ψ y) *
            transitionT K₁ (List.ofFn J) (List.ofFn A) y := by
    intro d hd I
    have hd1 := (Finset.mem_Icc.mp hd).1
    rw [transitionT_comp hK₁ hK₂ hψ hder _ _ d (by rw [List.length_ofFn]; omega) y,
      Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) (by omega : r ≤ d)]
    refine add_eq_right.mpr (Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun J _ => ?_)
    rw [transitionT_eq_zero_of_length_lt K₁ _ _
      (by simp only [List.length_ofFn]; exact (Finset.mem_Ico.mp hs).2), mul_zero]
  simp only [transportedCoeff]
  calc _ = ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ s ∈ Finset.Ico r d, g s d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [hT3 d hd, Finset.mul_sum, hg]
        rw [Finset.sum_congr rfl fun I _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_congr rfl fun I _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        ring
    _ = ∑ s ∈ Finset.Ico r Dγ, ∑ d ∈ Finset.Icc (s + 1) Dγ, g s d :=
        Finset.sum_comm' fun d s => by simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    _ = _ := by
        rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add' _ r Dγ 1]
        refine Finset.sum_congr rfl fun s _ => ?_
        change _ = ∑ J : DerivativeWord2 s, ∑ i₀ : Fin 2, K₁ y a₀ i₀ *
          (∑ d ∈ Finset.Icc (s + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₁ : Fin 2,
            K₂ (ψ y) i₀ i₁ * B d I i₁ * transitionT K₂ (List.ofFn I) (List.ofFn J) (ψ y)) *
          transitionT K₁ (List.ofFn J) (List.ofFn A) y
        simp only [hg]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]

end Comp

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.QuietAtlas

/-! **Quiet matching of a stage, stage-generically** (shared by the weak entry, the
preservation argument and the level-C letters of `cycle_joint`). The quiet clauses of the stage
invariant (`IsStageInvariant` clause 3, `IsWeakStage`, `StageQuietMatchingClause`) on a
window `W`, with an arbitrary set `S` of times in place of `ocQuietTimes` in the fast-independence
clause only (`QuietMatchingOn`):
* an atlas of the pieces, consecutive and closed on `W`, whose transitions cover the quiet times
  (`ocQuietTimes`) of `W` on the overlaps of the outputs, quiet (`IsQuiet`), and whose identified
  contexts are exactly the actual ones (the common outputs of adjacent natural
  pieces lie `τ/16` from every pulse);
* transversality on the enlarged pulses;
* fast independence on `S ∩ W`.

Fast independence holds on trimmed quiet times only, and the
trimmed set is fixed below. The generic ingredient is stated for every set of
**history-quiet** times (`IsHistoryQuiet`): quiet times at which the whole availability interval
`I(k)` of every active child `k` (`availInterval`: its anchor, output interval and deeper child
intervals, on both sides of `t`) is quiet. Then no displacement of the parent pulse enters the child
geometry, neither through the anchor nor through the memory of the finer lifts. It holds for
either choice of the trimmed set. The producer clause is the case
`S = ocTrimmedQuietTimes` (the times whose `τ_m/24`-neighbourhood is quiet), and
`ocTrimmedQuiet D m` is that set.

The structural input is the transfer form of the coefficients: each is either
the transfer of a finer output (`transferAt`; every source of the weak passage and the
non-diagonal sources of the cascade successor) or the first source `𝖣` of the cascade successor
(`firstSourceFlux`, the diagonal letter). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The quiet matching clauses** of the stage `G` on the window `W`, with the set `S` in the
fast-independence clause. -/
def QuietMatchingOn (G : GenStage D hr Dm b j₀) (S W : Set ℝ) : Prop :=
  (∃ T : G.fam.Atlas,
    T.IsConsecutiveClosed W ∧
    T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) W ∧
    T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
    (∀ p q (hpq : T.adjacent p q),
      ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ W).Nonempty →
      T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
    (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
      c = G.actual p ∧ c' = G.actual q)) ∧
  G.fam.IsTransverseOnPulses (enlargedPulse D G.level W) parallelIndex ∧
  G.fam.IsFastIndependentOn (S ∩ W)

/-- **History-quiet times of level `m`** (with the finest level `Mtop` of the availability
intervals): quiet times at which the whole availability interval of every child of level `m + 1`
active at `t` is quiet. -/
def IsHistoryQuiet (D : OCData) (Mtop m : ℕ) (S : Set ℝ) : Prop :=
  S ⊆ ocQuietTimes D.α D.q D.Λ D.ζ m ∧
  ∀ t ∈ S, ∀ k : ℤ, ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0 →
    availInterval D Mtop (m + 1) k ⊆ ocQuietTimes D.α D.q D.Λ D.ζ m

/-- The trimmed quiet times of level `m` of the data `D`: the set
`ocTrimmedQuietTimes`. -/
def ocTrimmedQuiet (D : OCData) (m : ℕ) : Set ℝ :=
  ocTrimmedQuietTimes D.α D.q D.Λ D.ζ m

/-- History-quiet sets are closed under subsets. -/
theorem IsHistoryQuiet.mono {D : OCData} {Mtop m : ℕ} {S S' : Set ℝ} (h : IsHistoryQuiet D Mtop m S)
    (hS : S' ⊆ S) : IsHistoryQuiet D Mtop m S' :=
  ⟨hS.trans h.1, fun t ht => h.2 t (hS ht)⟩

/-- History-quiet sets are closed under unions. -/
theorem IsHistoryQuiet.union {D : OCData} {Mtop m : ℕ} {S S' : Set ℝ}
    (h : IsHistoryQuiet D Mtop m S) (h' : IsHistoryQuiet D Mtop m S') :
    IsHistoryQuiet D Mtop m (S ∪ S') :=
  ⟨Set.union_subset h.1 h'.1, fun t ht => ht.elim (h.2 t) (h'.2 t)⟩

/-- **The structural quiet times of level `m`**: the times at which the output windows of two
distinct slots meet. They contain the common outputs of adjacent natural pieces (the atlas clauses)
and the slivers of a neighbouring output inside an enlarged pulse (the transversality clause). -/
def outputOverlapTimes (D : OCData) (m : ℕ) : Set ℝ :=
  {t | ∃ p q : ℤ, Odd p ∧ Odd q ∧ p ≠ q ∧ t ∈ ocPulseWindow D.α D.q D.Λ m p ∧
    t ∈ ocPulseWindow D.α D.q D.Λ m q}

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public section
open Homogenization Set
namespace AVRegularity.Providers.QuietAtlas

/-! Complete availability intervals lie in the existing nested slot windows. The estimate is
uniform in the depth and gives history quietness of the trimmed set, for either carrier. -/

private theorem hull_subset_Icc {S : Set ℝ} {a b : ℝ} (h : S ⊆ Icc a b) :
    intervalHull S ⊆ Icc a b := by
  rintro t ⟨u, hu, v, hv, hut, htv⟩
  exact ⟨(h hu).1.trans hut, htv.trans (h hv).2⟩

private theorem output_subset_slotWin (D : OCData) (hΛ : 1 ≤ D.Λ) (i : ℕ) (p : ℤ) :
    ocPulseWindow D.α D.q D.Λ i p ⊆ ComplexFlow.slotWin D i p := by
  intro t ht
  have hdist := ComplexFlow.abs_sub_anchor_le_of_mem_window D hΛ ht
  have hscale := ComplexFlow.tau_le D hΛ i
  obtain ⟨hl, hu⟩ := abs_le.mp hdist
  constructor <;> linarith only [hl, hu, hscale]

/-- Every finite-depth availability hull lies in the slot's `3h/5` window. -/
theorem availAux_subset_slotWin (D : OCData) (hΛ : 1 ≤ D.Λ) (f i : ℕ) (p : ℤ)
    (hsep : ∀ k, i ≤ k → ocTauPP D.α D.q D.Λ (k + 1) < ocTau D.α D.q D.Λ k / 48) :
    availAux D f i p ⊆ ComplexFlow.slotWin D i p := by
  induction f generalizing i p with
  | zero =>
    apply hull_subset_Icc
    rintro t (rfl | ht)
    · exact ComplexFlow.anchor_mem_slotWin D hΛ i p
    · exact output_subset_slotWin D hΛ i p ht
  | succ f ih =>
    apply hull_subset_Icc
    rintro t (rfl | ht)
    · exact ComplexFlow.anchor_mem_slotWin D hΛ i p
    · rcases ht with ht | ht
      · exact output_subset_slotWin D hΛ i p ht
      · obtain ⟨p', ht⟩ := Set.mem_iUnion.mp ht
        obtain ⟨hs, ht⟩ := Set.mem_iUnion.mp ht
        exact ComplexFlow.slotWin_subset D hΛ hs.2 (hsep i le_rfl)
          (ih (i + 1) p' (fun k hk => hsep k (by omega)) ht)

/-- A carrier start with `CH ≥ 1` gives the nesting separation at every subsequent level. -/
theorem carrierStart_history_separation {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {i : ℕ} (hi : j₀ ≤ i) :
    ocTauPP D.α D.q D.Λ (i + 1) < ocTau D.α D.q D.Λ i / 48 := by
  have hpos := Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) hΛ (m := i + 1)
  have hmul := mul_le_mul_of_nonneg_right hCH hpos.le
  have hsmall := hstart.2 i hi
  linarith only [hmul, hsmall]

/-- The complete interval, including all deeper child histories, stays within `3h/5` of its
renewal anchor, uniformly in `Mtop - i`. -/
theorem availInterval_subset_slotWin {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (Mtop i : ℕ) (hi : j₀ ≤ i) (p : ℤ) :
    availInterval D Mtop i p ⊆ ComplexFlow.slotWin D i p :=
  availAux_subset_slotWin D hΛ (Mtop - i) i p fun _ hk =>
    carrierStart_history_separation hΛ hCH hstart (hi.trans hk)

/-- An active child's entire availability interval is within `τ_m/24` of the evaluation time. -/
theorem active_child_availInterval_subset {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (Mtop m : ℕ) (hm : j₀ ≤ m)
    (k : ℤ) (t : ℝ) (hcut : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0) :
    availInterval D Mtop (m + 1) k ⊆
      Icc (t - ocTau D.α D.q D.Λ m / 24) (t + ocTau D.α D.q D.Λ m / 24) := by
  intro u hu
  have hdist := ComplexFlow.abs_sub_le_of_mem_slotWin D
    (availInterval_subset_slotWin hΛ hCH hstart Mtop (m + 1) (by omega) k hu)
    (ComplexFlow.mem_slotWin_of_cutoff D hΛ hcut)
  have hpos := Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) hΛ (m := m + 1)
  have hmul := mul_le_mul_of_nonneg_right hCH hpos.le
  have hsmall := hstart.2 m hm
  obtain ⟨hl, hr⟩ := abs_le.mp hdist
  constructor <;> linarith only [hl, hr, hmul, hsmall, hpos]

/-! **The facts about the trimmed quiet times.** Every proof uses
`ocTrimmedQuietTimes` (and `ocTrimmedQuiet`) only through the lemmas of this module, so a different
body of the definition costs this module only:
* `mem_ocTrimmedQuietTimes`: the unfolding;
* `ocTrimmedQuietTimes_subset`: it is contained in `ocQuietTimes`;
* `isHistoryQuiet_ocTrimmedQuiet`: it is history quiet (two-sided, the whole availability interval
  of every active child), for every construction depth;
* `outputOverlapTimes_subset_ocTrimmedQuiet`: it contains the times at which two output windows
  meet (used for the atlas clauses, not for the producer clause). -/

/-- **The unfolding** of the trimmed quiet times. -/
theorem mem_ocTrimmedQuietTimes {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {m : ℕ} {t : ℝ} :
    t ∈ ocTrimmedQuietTimes α q Λ ζ m ↔
      Set.Icc (t - ocTau α q Λ m / 24) (t + ocTau α q Λ m / 24) ⊆ ocQuietTimes α q Λ ζ m :=
  Iff.rfl

/-- **The trimmed quiet times are quiet.** -/
theorem ocTrimmedQuietTimes_subset {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (ζ : ℝ → ℝ) (m : ℕ) :
    ocTrimmedQuietTimes α q Λ ζ m ⊆ ocQuietTimes α q Λ ζ m := by
  intro t ht
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) hΛ (m := m)
  apply mem_ocTrimmedQuietTimes.mp ht
  constructor <;> linarith only [hτ]

/-- The trimmed set is history quiet for every finite construction depth. -/
theorem isHistoryQuiet_ocTrimmedQuiet {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hCH : 1 ≤ CH)
    (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) (Mtop m : ℕ) (hm : j₀ ≤ m) :
    IsHistoryQuiet D Mtop m (ocTrimmedQuiet D m) := by
  refine ⟨ocTrimmedQuietTimes_subset hΛ D.ζ m, ?_⟩
  intro t ht k hcut
  exact (active_child_availInterval_subset hΛ hCH hstart Mtop m hm k t hcut).trans
    (mem_ocTrimmedQuietTimes.mp ht)

/-- **The structural quiet times are trimmed**: two output windows meet only for neighbouring slots
`p, p + 2`, on `[(p + 35/48)τ, (p + 61/48)τ]`, whose `τ/24`-neighbourhood lies in the quiet gap
`[(p + 2/3)τ, (p + 4/3)τ]` (`mem_ocQuietTimes_of_gap`). -/
theorem outputOverlapTimes_subset_ocTrimmedQuiet {D : OCData} (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) : outputOverlapTimes D m ⊆ ocTrimmedQuiet D m := by
  have hτ : 0 < ocTau D.α D.q D.Λ m := Construction.Stream.ocTau_pos hΛ
  have key : ∀ p q : ℤ, Odd p → Odd q → p < q → ∀ t, t ∈ ocPulseWindow D.α D.q D.Λ m p →
      t ∈ ocPulseWindow D.α D.q D.Λ m q → t ∈ ocTrimmedQuiet D m := by
    intro p q hp hq hpq t htp htq
    refine mem_ocTrimmedQuietTimes.mpr fun s hs => ?_
    obtain ⟨-, htp2⟩ := htp
    obtain ⟨htq1, -⟩ := htq
    obtain ⟨hs1, hs2⟩ := hs
    have hlt : ((q : ℝ) - p) * ocTau D.α D.q D.Λ m < 3 * ocTau D.α D.q D.Λ m := by nlinarith
    have hlt' : q - p < 3 := by
      have := lt_of_mul_lt_mul_right hlt hτ.le
      exact_mod_cast this
    have hq2 : q = p + 2 := by
      obtain ⟨a, rfl⟩ := hp
      obtain ⟨c, rfl⟩ := hq
      omega
    subst hq2
    push_cast at htq1
    refine CycleComparison.Reconstruction.mem_ocQuietTimes_of_gap hΛ hζ hp ?_ ?_ <;> nlinarith
  rintro t ⟨p, q, hp, hq, hpq, htp, htq⟩
  rcases lt_or_gt_of_ne hpq with h | h
  · exact key p q hp hq h t htp htq
  · exact key q p hq hp h t htq htp

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Filter Topology
open scoped Classical
namespace AVRegularity.Providers.QuietAtlas

/-! Source-level ingredients for quiet matching. The finer-output identities are germ
identities, before extraction of coefficients. This also retains the old-label derivatives
read by the covariance polynomial in the first source. No regularity or uniqueness of an
arbitrary finer output is implicit in the transfer presentation. -/

/-- The two production formulas, with their actual finer outputs kept as data. -/
inductive QuietSource where
  | transfer (lam : ℝ) (order : ℕ) (fop : FamFluxOp)
  | first (lam ρ s₀ : ℝ) (N pc : ℕ)
      (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))

/-- The normalized source array in a coarser context. -/
def QuietSource.array (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ m : ℕ)
    (src : QuietSource) (p : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) : Vec 2 :=
  match src with
  | .transfer lam order fop => transferAt D (m + 1) p lam order fop t ch z d I
  | .first lam ρ s₀ N pc Cc0 =>
      (lam * (D.κ m * D.eps m ^ (d - 2))⁻¹) •
        fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t ch z) d I 0

/-- The degree index is irrelevant for a transfer and is the mean-flux degree for a first source. -/
def QuietSource.degrees : QuietSource → Set ℕ
  | .transfer _ _ _ => {0}
  | .first _ _ _ N _ _ => insert 2 (Set.Icc 3 (N + 1))

/-- The finer operators actually read by the source formula. -/
def QuietSource.finer (D : OCData) (Dm m : ℕ) (src : QuietSource) (n : ℕ) : FamFluxOp :=
  match src with
  | .transfer _ _ fop => fop
  | .first _ ρ _ _ _ Cc0 => fun k t ch => diagLabelFlux D Dm (m + 1) ρ Cc0 k ch n t

/-- The time-independent transition from the labels of `q` to those of `p`. -/
def renewalTransition (D : OCData) (m : ℕ) (p q : OddSlot) (Y : Vec 2) : Vec 2 :=
  D.flowOf (m - 1) (D.slotAnchor m p.1) Y (D.slotAnchor m q.1)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A presentation chooses the same production data for every piece and context of an identity. -/
structure QuietPresentation (G : GenStage D hr Dm b j₀) where
  source : ∀ v u, G.fam.Γ v u → QuietSource
  represents : ∀ p (c : StageCtx D b j₀ G.level p) v u (γ : G.fam.Γ v u)
      d (I : DerivativeWord2 (d - 1)) t Y z, 2 ≤ d →
    G.fam.flux p c v u γ d I t Y z =
      if IsAdmissibleChain D b j₀ G.level p.1 (c.1.recenter D (D.eps (G.level - 1) • Y)) then
        (source v u γ).array D Dm b j₀ G.level p.1 t
          (c.1.recenter D (D.eps (G.level - 1) • Y)) z d I
      else 0

/-- QC1: at active children the finer operators are phase blind as old-label germs.
The contexts, including all their earlier parameters, are fixed. -/
def QuietPhaseBlind (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (U : Set ℝ) : Prop :=
  ∀ v u (γ : G.fam.Γ v u) p (ch : StageCtx D b j₀ G.level p) t,
    t ∈ U → t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
    ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
    ∀ n ∈ (P.source v u γ).degrees, ∀ z z' : Vec 2, ∀ f : Vec 2 → ℝ,
      (P.source v u γ).finer D Dm G.level n k t (ch.1.appendChild D k t z) f =ᶠ[𝓝 0]
        (P.source v u γ).finer D Dm G.level n k t (ch.1.appendChild D k t z') f

/-- QC2: the actual child in the two renewal descriptions gives the same finer operator germ.
The fast variable is fixed; it is never passed through the slow transition. -/
def QuietReanchors (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (U : Set ℝ) : Prop :=
  ∀ v u (γ : G.fam.Γ v u) (p q : OddSlot), p ≠ q → ∀ t,
    t ∈ U → t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
    t ∈ ocPulseWindow D.α D.q D.Λ G.level q.1 →
    ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ (G.level + 1) k t ≠ 0 →
    ∀ n ∈ (P.source v u γ).degrees, ∀ Y z : Vec 2, ∀ f : Vec 2 → ℝ,
      (P.source v u γ).finer D Dm G.level n k t
        (((nativeChain G.level p.1).recenter D (renewalTransition D G.level p q Y)).appendChild
          D k t z) f =ᶠ[𝓝 0]
      (P.source v u γ).finer D Dm G.level n k t
        (((nativeChain G.level q.1).recenter D Y).appendChild D k t z) f

/-- The remaining source phase algebra, before a chart representative and its off-carrier
extension are formed. It includes the Jacobian germ of a transfer and the covariance polynomial
of the first source; QC1 supplies the finer operators, not this assembled equality. -/
def QuietSourcePhaseStatement : Prop :=
  ∀ (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ),
    1 ≤ D.Λ → IsFastProfile D.ζ → IsHistoryQuiet D Mtop G.level U → QuietPhaseBlind G P U →
    ∀ p (ch : StageCtx D b j₀ G.level p) t, t ∈ U →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      ∀ v u (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)), 2 ≤ d → ∀ z z' : Vec 2,
        (P.source v u γ).array D Dm b j₀ G.level p.1 t ch.1 z d I =
          (P.source v u γ).array D Dm b j₀ G.level p.1 t ch.1 z' d I

/-- The phase-transfer layer: QC1 of the finer outputs gives phase blindness of the produced
arrays. This is a statement about the concrete source formulas, including the first source. -/
def QuietPhaseTransferStatement : Prop :=
  ∀ (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (U : Set ℝ),
    1 ≤ D.Λ → IsFastProfile D.ζ → IsHistoryQuiet D Mtop G.level U → QuietPhaseBlind G P U →
    ∀ p (ch : StageCtx D b j₀ G.level p) t, t ∈ U →
      t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
      ∀ v u (γ : G.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) (Y z z' : Vec 2),
        G.fam.flux p ch v u γ d I t Y z = G.fam.flux p ch v u γ d I t Y z'

/-- The incoming finer operators depend only on the centered material family over the slot's
complete history. The conclusion is a germ, so it also retains their old-label derivatives. -/
def FinerHistoryInvariant (G : GenStage D hr Dm b j₀) (P : QuietPresentation G)
    (Mtop : ℕ) : Prop :=
  ∀ v u (γ : G.fam.Γ v u) n, n ∈ (P.source v u γ).degrees →
    ∀ (k : OddSlot) (ch ch' : StageCtx D b j₀ (G.level + 1) k),
      SameHistoryGeometry D Mtop (G.level + 1) k.1 ch.1 ch'.1 →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ (G.level + 1) k.1, ∀ f : Vec 2 → ℝ,
        (P.source v u γ).finer D Dm G.level n k.1 t ch.1 f =ᶠ[𝓝 0]
          (P.source v u γ).finer D Dm G.level n k.1 t ch'.1 f

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.QuietAtlas

/-! A phase-blind source array gives a phase-blind independent field. Recentering retains all
earlier parameters; the off-carrier and absent-order branches are exact zeros. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The stage-level phase leaf is discharged from the raw production formula. -/
theorem quietPhaseTransfer_of_source
    (hsource : QuietSourcePhaseStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀)) :
    QuietPhaseTransferStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro G P Mtop U hΛ hζ hU hQC p ch t ht htp v u γ d I Y z z'
  by_cases hd : 2 ≤ d
  · rw [P.represents p ch v u γ d I t Y z hd, P.represents p ch v u γ d I t Y z' hd]
    split_ifs with hrec
    · exact hsource G P Mtop U hΛ hζ hU hQC p ⟨_, hrec⟩ t ht htp v u γ d I hd z z'
    · rfl
  · rw [G.fam.flux_zero p ch v u γ d I (fun h => hd h.1)]

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.QuietAtlas

/-! Quiet matching from the source algebra. Atlas geometry and the use of the structural set
`Q` are discharged here. The two remaining algebra statements are explicit in Statement. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The natural flow transition, with exactly the quiet overlap. -/
def naturalQuietTransition (G : GenStage D hr Dm b j₀) {Mtop : ℕ}
    (hnat : G.IsNatural Mtop) (W : Set ℝ) (p q : OddSlot) :
    ChartTransition (G.fam.piece p) (G.fam.piece q) where
  Υ := renewalTransition D G.level p q
  smooth := CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) _ _
  det_one := CycleReference.streamFlow_jacMatrix_det_one (D.hΦ (G.level - 1)) _ _
  compat := by
    intro t Y
    rw [(hnat.1 q).2.2.2.2 t, (hnat.1 p).2.2.2.2 t]
    exact (Infra.Flow.flow_group_law _ (D.hΦ (G.level - 1)).vel_lipschitz
      (flow_isFlow _ (D.hΦ (G.level - 1)).vel_continuous (D.hΦ (G.level - 1)).vel_lipschitz)
      Y (D.slotAnchor G.level q.1) (D.slotAnchor G.level p.1) t).symm
  overlap := {tY | tY.1 ∈ ocQuietTimes D.α D.q D.Λ D.ζ G.level ∩ W ∩
    (G.fam.piece p).output ∩ (G.fam.piece q).output}

/-- Consecutive closure, with precisely the actual contexts matched. -/
def naturalQuietAtlas (G : GenStage D hr Dm b j₀) {Mtop : ℕ}
    (hnat : G.IsNatural Mtop) (W : Set ℝ) : G.fam.Atlas where
  adjacent := fun p q => p ≠ q ∧
    ((G.fam.piece q).label = (G.fam.piece p).label + 1 ∨
      (G.fam.piece q).label = (G.fam.piece p).label) ∧
    ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ W).Nonempty
  tr := fun p q _ => naturalQuietTransition G hnat W p q
  sameCtx := fun p q _ c c' => c = G.actual p ∧ c' = G.actual q

end AVRegularity.Providers.QuietAtlas
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.Providers.QuietAtlas

/-! **Quiet times silence every pulse** (quiet matching, the common geometric fact).
* `ocPulse_eq_zero_of_mem_ocQuietTimes`: at a quiet time of level `m` every pulse of level `m`
  vanishes. At most one pulse is active at a time (`ocPulseStream_eq_active`), and its shear
  field is nonzero at the origin.
* `relDisp_eq_zero_of_quiet`, `labelShear_eq_zero_of_quiet`: the relative displacement of a
  pulse between two times of a quiet interval, and the label shear at a quiet time, vanish.
* `availInterval` is order connected and contains the anchor and the pulse window of its slot.
  So on a history-quiet set `U`, a child `k` active at `t ∈ U` sees no level-`m` displacement
  between any two times of its availability interval (`relDisp_eq_zero_of_historyQuiet`). -/

section Pulse

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

/-- **Every pulse vanishes at a quiet time.** -/
theorem ocPulse_eq_zero_of_mem_ocQuietTimes (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {t : ℝ}
    (ht : t ∈ ocQuietTimes α q Λ ζ m) {k : ℤ} (hk : Odd k) : ocPulse α q Λ ζ m k t = 0 := by
  by_contra hp
  have hs : ocPulseStream α q Λ ζ m t =
      fun y => ocPulse α q Λ ζ m k t * ocShear α q Λ m k y :=
    funext fun y => CycleReference.ocPulseStream_eq_active hΛ hζ hk hp
  have hd : DifferentiableAt ℝ (ocShear α q Λ m k) 0 :=
    ((CycleReference.ocShear_contDiff α q Λ m k).differentiable (by simp)) 0
  have hg : spaceGrad (ocPulseStream α q Λ ζ m t) 0 =
      ocPulse α q Λ ζ m k t • spaceGrad (ocShear α q Λ m k) 0 := by
    rw [hs]
    funext i
    simp [spaceGrad, fderiv_const_mul hd]
  have hvel : ocPulse α q Λ ζ m k t • ocShearVel α q Λ m k 0 = 0 := by
    have h1 : streamVel (ocPulseStream α q Λ ζ m) t 0 =
        ocPulse α q Λ ζ m k t • ocShearVel α q Λ m k 0 := by
      change sigmaMat.mulVec (spaceGrad (ocPulseStream α q Λ ζ m t) 0) = _
      rw [hg, Matrix.mulVec_smul]
      rfl
    rw [← h1]
    exact ht 0
  have hε : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hA : 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ ≠ 0 := by
    have := Real.rpow_pos_of_pos hε (1 + α)
    have := Real.pi_pos
    positivity
  obtain ⟨j, rfl⟩ := hk
  rcases (by omega : (2 * j + 1) % 4 = 1 ∨ (2 * j + 1) % 4 = 3) with h1 | h3
  · have h := congrFun hvel 1
    rw [CycleReference.ocShearVel_horizontal h1] at h
    simp only [Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul,
      Pi.zero_apply, mul_zero, Real.cos_zero, mul_one] at h
    exact hp ((mul_eq_zero.mp h).resolve_right hA)
  · have h := congrFun hvel 0
    rw [CycleReference.ocShearVel_vertical h3] at h
    simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, Pi.zero_apply, mul_zero,
      Real.cos_zero, mul_one, mul_neg, neg_eq_zero] at h
    exact hp ((mul_eq_zero.mp h).resolve_right hA)

/-- The integral of a pulse over a quiet interval vanishes. -/
theorem integral_ocPulse_eq_zero (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k)
    {a b : ℝ} (hab : Set.uIcc a b ⊆ ocQuietTimes α q Λ ζ m) :
    ∫ v in a..b, ocPulse α q Λ ζ m k v = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
    fun v hv => ocPulse_eq_zero_of_mem_ocQuietTimes hΛ hζ (hab hv) hk]
  simp

end Pulse

variable (D : OCData)

/-- The relative displacement of a pulse vanishes between two times of a quiet interval. -/
theorem relDisp_eq_zero_of_quiet (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {i : ℕ} {p : ℤ}
    (hp : Odd p) {u s : ℝ} (h : Set.uIcc s u ⊆ ocQuietTimes D.α D.q D.Λ D.ζ i) (θ : Vec 2) :
    D.relDisp i p u s θ = 0 := by
  unfold OCData.relDisp
  rw [integral_ocPulse_eq_zero hΛ hζ hp h, zero_smul, smul_zero]

/-- The label shear vanishes at a quiet time. -/
theorem labelShear_eq_zero_of_quiet (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {i : ℕ} {p : ℤ}
    (hp : Odd p) {t : ℝ} (ht : t ∈ ocQuietTimes D.α D.q D.Λ D.ζ i) :
    labelShear D i p t = 0 := by
  funext θ
  unfold labelShear
  rw [ocPulse_eq_zero_of_mem_ocQuietTimes hΛ hζ ht hp, zero_smul]
  rfl

/-! ### Availability intervals -/

theorem mem_intervalHull {S : Set ℝ} {t : ℝ} (ht : t ∈ S) : t ∈ intervalHull S :=
  ⟨t, ht, t, ht, le_rfl, le_rfl⟩

theorem uIcc_subset_intervalHull {S : Set ℝ} {s s' : ℝ} (hs : s ∈ intervalHull S)
    (hs' : s' ∈ intervalHull S) : Set.uIcc s s' ⊆ intervalHull S := by
  intro x hx
  obtain ⟨a, ha, b, hb, has, hsb⟩ := hs
  obtain ⟨a', ha', b', hb', has', hsb'⟩ := hs'
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨a, ha, b', hb', has.trans h1, h2.trans hsb'⟩
  · exact ⟨a', ha', b, hb, has'.trans h1, h2.trans hsb⟩

theorem anchor_window_subset_availAux (f i : ℕ) (p : ℤ) :
    insert (D.slotAnchor i p) (ocPulseWindow D.α D.q D.Λ i p) ⊆ availAux D f i p := by
  intro x hx
  cases f with
  | zero => exact mem_intervalHull hx
  | succ f =>
    refine mem_intervalHull ?_
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hx)

theorem availAux_eq_intervalHull (f i : ℕ) (p : ℤ) :
    ∃ S : Set ℝ, availAux D f i p = intervalHull S := by
  cases f with
  | zero => exact ⟨_, rfl⟩
  | succ f => exact ⟨_, rfl⟩

/-- An availability interval is order connected. -/
theorem uIcc_subset_availInterval (M i : ℕ) (p : ℤ) {s s' : ℝ}
    (hs : s ∈ availInterval D M i p) (hs' : s' ∈ availInterval D M i p) :
    Set.uIcc s s' ⊆ availInterval D M i p := by
  obtain ⟨S, hS⟩ := availAux_eq_intervalHull D (M - i) i p
  unfold availInterval at hs hs' ⊢
  rw [hS] at hs hs' ⊢
  exact uIcc_subset_intervalHull hs hs'

theorem slotAnchor_mem_availInterval (M i : ℕ) (p : ℤ) :
    D.slotAnchor i p ∈ availInterval D M i p :=
  anchor_window_subset_availAux D (M - i) i p (Set.mem_insert _ _)

theorem ocPulseWindow_subset_availInterval (M i : ℕ) (p : ℤ) :
    ocPulseWindow D.α D.q D.Λ i p ⊆ availInterval D M i p :=
  fun _ hx => anchor_window_subset_availAux D (M - i) i p (Set.mem_insert_of_mem _ hx)

/-- **No displacement on the history of an active child.** On a history-quiet set, a child `k`
active at `t` sees no displacement of any level-`m` pulse between two times of its
availability interval. -/
theorem relDisp_eq_zero_of_historyQuiet (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {Mtop m : ℕ}
    {U : Set ℝ} (hU : IsHistoryQuiet D Mtop m U) {t : ℝ} (ht : t ∈ U) {k : ℤ}
    (hk : ocCutoff D.α D.q D.Λ (m + 1) k t ≠ 0) {p : ℤ} (hp : Odd p) {u s : ℝ}
    (hu : u ∈ availInterval D Mtop (m + 1) k) (hs : s ∈ availInterval D Mtop (m + 1) k)
    (θ : Vec 2) : D.relDisp m p u s θ = 0 :=
  relDisp_eq_zero_of_quiet D hΛ hζ hp
    ((uIcc_subset_availInterval D Mtop (m + 1) k hs hu).trans (hU.2 t ht k hk)) θ

/-- The time of an active child lies in its availability interval. -/
theorem mem_availInterval_of_ocCutoff (hΛ : 1 ≤ D.Λ) {Mtop i : ℕ} {k : ℤ} {t : ℝ}
    (hk : ocCutoff D.α D.q D.Λ i k t ≠ 0) : t ∈ availInterval D Mtop i k :=
  ocPulseWindow_subset_availInterval D Mtop i k
    (GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hk)

end AVRegularity.Providers.QuietAtlas
end
end
