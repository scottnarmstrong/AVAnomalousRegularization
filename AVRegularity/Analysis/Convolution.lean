-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import AVRegularity.Analysis.Convolution.Kernel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Liouville

section
section
@[expose] public section
open Metric
namespace AVRegularity.Analysis

/-! # Cauchy estimates in several variables

For a complex-differentiable map on an open set containing a closed ball, bounded by `M` there,
`‖Df(x)‖ ≤ M/r` (`norm_fderiv_le_of_closedBall`, Cauchy along each complex line through `x`), and
for an analytic map `‖Dⁿf(x)‖ ≤ M nⁿ/rⁿ` (`norm_iteratedFDeriv_le_of_closedBall`, by induction on
nested balls of radii `r - r/(n+1)`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Cauchy's estimate for the first derivative**, in several variables. -/
theorem norm_fderiv_le_of_closedBall {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : E} {r M : ℝ} (hr : 0 < r) (hsub : closedBall x r ⊆ U)
    (hM : ∀ y ∈ closedBall x r, ‖f y‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M / r := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set u : E := ((‖v‖ : ℂ))⁻¹ • v with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hvn.ne']
  have hmaps : ∀ z ∈ closedBall (0 : ℂ) r, x + z • u ∈ closedBall x r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hun, mul_one]
    simpa using hz
  set g : ℂ → F := fun z => f (x + z • u) with hg
  have hdiff : DifferentiableOn ℂ g (closedBall 0 r) := by
    intro z hz
    have hzU : x + z • u ∈ U := hsub (hmaps z hz)
    have hlin : DifferentiableAt ℂ (fun z : ℂ => x + z • u) z :=
      (differentiableAt_id.smul_const u).const_add x
    exact ((hf.differentiableAt (hU.mem_nhds hzU)).comp z hlin).differentiableWithinAt
  have hd : DiffContOnCl ℂ g (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact hdiff
  have hC : ∀ z ∈ sphere (0 : ℂ) r, ‖g z‖ ≤ M := fun z hz =>
    hM _ (hmaps z (sphere_subset_closedBall hz))
  have hderiv : deriv g 0 = fderiv ℂ f x u := by
    have h1 : HasDerivAt (fun z : ℂ => x + z • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add x
    have hxU : x ∈ U := hsub (mem_closedBall_self hr.le)
    have h2 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • u) := by
      rw [zero_smul, add_zero]
      exact (hf.differentiableAt (hU.mem_nhds hxU)).hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hC
  rw [hderiv] at hbound
  have hvu : v = (‖v‖ : ℂ) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hvn.ne'), one_smul]
  calc ‖fderiv ℂ f x v‖ = ‖v‖ * ‖fderiv ℂ f x u‖ := by
        conv_lhs => rw [hvu]
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    _ ≤ ‖v‖ * (M / r) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = M / r * ‖v‖ := mul_comm _ _

/-- **Cauchy's estimate for the iterated derivatives**, in several variables:
`‖Dⁿf(x)‖ ≤ M nⁿ/rⁿ` when `‖f‖ ≤ M` on a closed ball of radius `r` inside the domain of
analyticity. -/
theorem norm_iteratedFDeriv_le_of_closedBall [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) {M : ℝ} (n : ℕ) :
    ∀ {x : E} {r : ℝ}, 0 < r → closedBall x r ⊆ U → (∀ y ∈ closedBall x r, ‖f y‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f x‖ ≤ M * (n : ℝ) ^ n / r ^ n := by
  induction n with
  | zero =>
    intro x r hr hsub hM
    simpa using hM x (mem_closedBall_self hr.le)
  | succ n ih =>
    intro x r hr hsub hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hr.le))
    rw [← norm_fderiv_iteratedFDeriv]
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    set ρ : ℝ := r / (n + 1) with hρ
    have hρ0 : 0 < ρ := div_pos hr hn1
    have hρr : ρ ≤ r := div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hbd : ∀ y ∈ closedBall x ρ,
        ‖iteratedFDeriv ℂ n f y‖ ≤ M * ((n : ℝ) + 1) ^ n / r ^ n := by
      intro y hy
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hM y (closedBall_subset_closedBall hρr hy)
      · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
        have hrρ : r - ρ = r * n / (n + 1) := by
          rw [hρ]
          field_simp
          ring
        have hr' : 0 < r - ρ := by rw [hrρ]; positivity
        have hsub' : closedBall y (r - ρ) ⊆ closedBall x r :=
          closedBall_subset_closedBall' (by linarith [mem_closedBall.1 hy])
        have h := ih hr' (hsub'.trans hsub) (fun z hz => hM z (hsub' hz))
        have heq : M * (n : ℝ) ^ n / (r - ρ) ^ n = M * ((n : ℝ) + 1) ^ n / r ^ n := by
          rw [hrρ, div_pow, mul_pow]
          field_simp
        linarith
    have hdiffU : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) U :=
      (hf.iteratedFDeriv_of_isOpen hU n).differentiableOn
    have h := norm_fderiv_le_of_closedBall hU hdiffU hρ0
      ((closedBall_subset_closedBall hρr).trans hsub) hbd
    have heq : M * ((n : ℝ) + 1) ^ n / r ^ n / ρ =
        M * ((n + 1 : ℕ) : ℝ) ^ (n + 1) / r ^ (n + 1) := by
      rw [hρ]
      push_cast
      field_simp
      ring
    linarith

end AVRegularity.Analysis
end
end

section
@[expose] public section
open Equiv
namespace AVRegularity.Analysis

/-! # Symmetry of the iterated derivatives of `C^n` functions

The permutations leaving a multilinear map invariant form a submonoid (`invariantPerms`), so
invariance under the adjacent transpositions gives invariance under all permutations
(`Equiv.Perm.mclosure_swap_castSucc_succ`). For a `C^n` function on a real normed space the `n`-th
derivative is invariant under the first transposition (the symmetric second derivative of
`y ↦ D^{n-2}f(y)(rest)`) and, by induction, under those fixing the first slot (the derivative of the
symmetric `D^{n-1}f(y)`), hence symmetric (`iteratedFDeriv_comp_perm_of_contDiff`). -/

section Symm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The permutations leaving a multilinear map invariant. -/
def invariantPerms {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    Submonoid (Perm (Fin n)) where
  carrier := {σ | ∀ v, M (v ∘ σ) = M v}
  one_mem' := fun _ => rfl
  mul_mem' := fun {σ τ} hσ hτ v => by
    show M (v ∘ ⇑(σ * τ)) = M v
    rw [Perm.coe_mul, ← Function.comp_assoc, hτ (v ∘ σ), hσ v]

/-- Invariance under the adjacent transpositions gives full symmetry. -/
theorem symm_of_adjacent {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) F)
    (h : ∀ i : Fin n, ∀ v, M (v ∘ swap i.castSucc i.succ) = M v) (σ : Perm (Fin (n + 1)))
    (v : Fin (n + 1) → E) : M (v ∘ σ) = M v := by
  have hle : Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) ≤
      invariantPerms M :=
    Submonoid.closure_le.2 (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [Perm.mclosure_swap_castSucc_succ] at hle
  exact hle (Submonoid.mem_top σ) v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem tail_comp_swap_succ {n : ℕ} (v : Fin (n + 2) → E) (j : Fin n) :
    Fin.tail (v ∘ swap j.succ.castSucc j.succ.succ) = Fin.tail v ∘ swap j.castSucc j.succ := by
  funext k
  simp only [Fin.tail, Function.comp_apply]
  rw [← Fin.succ_castSucc, (Fin.succ_injective _).swap_apply]

/-- **The iterated derivatives of a `C^n` function are symmetric.** -/
theorem iteratedFDeriv_comp_perm_of_contDiff : ∀ (n : ℕ) {f : E → F}, ContDiff ℝ n f →
    ∀ (x : E) (v : Fin n → E) (σ : Perm (Fin n)),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v
  | 0, f, _, x, v, σ => by
    congr 1
    funext i
    exact i.elim0
  | 1, f, _, x, v, σ => by
    have hσ : σ = 1 := Subsingleton.elim _ _
    rw [hσ]
    rfl
  | n + 2, f, hf, x, v, σ => by
    refine symm_of_adjacent _ (fun i w => ?_) σ v
    have hdiff : ∀ k : ℕ, k < n + 2 → Differentiable ℝ (iteratedFDeriv ℝ k f) := fun k hk =>
      hf.differentiable_iteratedFDeriv (by exact_mod_cast hk)
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, rfl⟩
    · -- the first transposition: the symmetric second derivative
      subst hi
      set rest : Fin n → E := fun k => w k.succ.succ with hrest
      set g : E → F := fun y => iteratedFDeriv ℝ n f y rest with hg
      have h2 : ContDiff ℝ 2 (iteratedFDeriv ℝ n f) :=
        hf.iteratedFDeriv_right (i := n) (by exact_mod_cast (show 2 + n ≤ n + 2 by omega))
      have hg2 : ContDiff ℝ 2 g :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F rest).contDiff.comp h2
      have hsymm := (hg2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
      have hgdiff : Differentiable ℝ g := hg2.differentiable (by norm_num)
      have hD1 : ∀ (y : E) (a : E), iteratedFDeriv ℝ (n + 1) f y (Fin.cons a rest) =
          fderiv ℝ g y a := fun y a => by
        rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons,
          ← fderiv_continuousMultilinear_apply_const_apply (hdiff n (by omega) y)]
      have hD2 : ∀ (u : Fin (n + 2) → E), iteratedFDeriv ℝ (n + 2) f x u =
          fderiv ℝ (fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (fun k => u k.succ.succ))) x
            (u 0) (u 1) := fun u => by
        rw [iteratedFDeriv_succ_apply_left,
          ← fderiv_continuousMultilinear_apply_const_apply (hdiff (n + 1) (by omega) x)]
        have hfun : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail u)) =
            fun y => fderiv ℝ (fun y' => iteratedFDeriv ℝ n f y' (fun k => u k.succ.succ)) y
              (u 1) := by
          funext y
          rw [iteratedFDeriv_succ_apply_left,
            ← fderiv_continuousMultilinear_apply_const_apply (hdiff n (by omega) y)]
          rfl
        rw [hfun]
        have hgu : Differentiable ℝ (fun y => iteratedFDeriv ℝ n f y (fun k => u k.succ.succ)) :=
          fun y => ((hdiff n (by omega) y).continuousMultilinear_apply_const _)
        have hgu2 : DifferentiableAt ℝ
            (fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (fun k => u k.succ.succ))) x := by
          have h2' : ContDiff ℝ 2 (fun y => iteratedFDeriv ℝ n f y (fun k => u k.succ.succ)) :=
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F
              (fun k => u k.succ.succ)).contDiff.comp h2
          exact (h2'.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
        rw [fderiv_clm_apply hgu2 (differentiableAt_const _)]
        simp
      rw [hD2, hD2]
      have hw0 : (w ∘ swap (0 : Fin (n + 1)).castSucc (0 : Fin (n + 1)).succ) 0 = w 1 := by
        simp [swap_apply_left]
      have hw1 : (w ∘ swap (0 : Fin (n + 1)).castSucc (0 : Fin (n + 1)).succ) 1 = w 0 := by
        simp [swap_apply_right]
      have hwr : (fun k : Fin n => (w ∘ swap (0 : Fin (n + 1)).castSucc
          (0 : Fin (n + 1)).succ) k.succ.succ) = fun k => w k.succ.succ := by
        funext k
        simp only [Function.comp_apply]
        rw [swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
      rw [hw0, hw1, hwr]
      exact (hsymm (w 0) (w 1)).symm
    · -- transpositions fixing the first slot: the derivative of a symmetric map
      have ih := iteratedFDeriv_comp_perm_of_contDiff (n + 1) (f := f)
        (hf.of_le (by exact_mod_cast Nat.le_succ _))
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have h0 : (w ∘ swap j.succ.castSucc j.succ.succ) 0 = w 0 := by
        simp only [Function.comp_apply]
        rw [swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
      rw [h0, tail_comp_swap_succ,
        ← fderiv_continuousMultilinear_apply_const_apply (hdiff (n + 1) (by omega) x),
        ← fderiv_continuousMultilinear_apply_const_apply (hdiff (n + 1) (by omega) x)]
      have hfun : (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail w ∘ swap j.castSucc j.succ)) =
          fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail w) :=
        funext fun y => ih y (Fin.tail w) _
      rw [hfun]

end Symm

end AVRegularity.Analysis
end
end

section
@[expose] public section
open MeasureTheory intervalIntegral Set
namespace AVRegularity.Analysis

/-! # A triangular Grönwall inequality with slow and fast parts

The engine of the fixed-frequency word bound. Stages `k < M` (levels and moments in
chronological-lexicographic order) carry a slow coordinate `A_k` and a fast seminorm `B_k`. Every
stage is forced by the earlier ones through letters whose slow–slow, slow–fast and fast–fast blocks
are at most `Θζ²`, `Θζ`, `Θ`, and the fast parts decay at rate `c`:
`A_k ≤ D + E + Θ ∑_{k'<k} ∫_0^t (ζ² A_{k'} + ζ B_{k'})`,
`B_k ≤ e^{-ct} D_p + E + Θ ∑_{k'<k} ∫_0^t e^{-c(t-r)} (ζ A_{k'} + B_{k'})`,
with `ζ D_p ≤ D` (the incoming fast part costs its exit zero). Then (`triangularGronwall_majorant`)
`A_k ≤ L^k (1 + ζ²t)^k (D + (1+t)^k E)` and
`B_k ≤ L^k (1 + ζ²t)^k (ζ D + e^{-ct/2} D_p + (1+t)^k E)`, `L = 1 + ΘM(2 + 2/c)`. This is the
triangular Grönwall inequality of the proof of Lemma 11.11 of the paper, in integrated form: a slow
stretch costs `ζ²t`, a fast excursion costs two zeros and an integrable duration, the initial fast
part has its exit zero and an integrable first duration. The errors `E` (replacements, quiet
switching) only gain polynomial factors in `t`. -/

/-- `∫_0^t e^{-cr/2} dr ≤ 2/c`. -/
theorem integral_exp_neg_half_le {c t : ℝ} (hc : 0 < c) :
    ∫ r in (0 : ℝ)..t, Real.exp (-(c / 2) * r) ≤ 2 / c := by
  have hF : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt (fun r => -(2 / c) * Real.exp (-(c / 2) * r))
      (Real.exp (-(c / 2) * r)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -(c / 2) * r) (-(c / 2)) r := by
      simpa using (hasDerivAt_id r).const_mul (-(c / 2))
    convert (h1.exp).const_mul (-(2 / c)) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hF (by apply Continuous.intervalIntegrable; fun_prop)]
  have := Real.exp_pos (-(c / 2) * t)
  have h2c : 0 < 2 / c := by positivity
  simp only [mul_zero, Real.exp_zero, mul_one]
  nlinarith

/-- `∫_0^t e^{-c(t-r)} dr ≤ 1/c`. -/
theorem integral_exp_neg_sub_le {c t : ℝ} (hc : 0 < c) :
    ∫ r in (0 : ℝ)..t, Real.exp (-c * (t - r)) ≤ 1 / c := by
  have hF : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt (fun r => (1 / c) * Real.exp (-c * (t - r)))
      (Real.exp (-c * (t - r))) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -c * (t - r)) c r := by
      have := ((hasDerivAt_id r).const_sub t).const_mul (-c)
      simpa using this
    convert (h1.exp).const_mul (1 / c) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hF (by apply Continuous.intervalIntegrable; fun_prop)]
  have := Real.exp_pos (-c * (t - 0))
  have h1c : 0 < 1 / c := by positivity
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
  nlinarith

/-- `∫_0^t e^{-c(t-r)} e^{-cr/2} dr ≤ (2/c) e^{-ct/2}`. -/
theorem integral_exp_neg_sub_mul_half_le {c t : ℝ} (hc : 0 < c) :
    ∫ r in (0 : ℝ)..t, Real.exp (-c * (t - r)) * Real.exp (-(c / 2) * r) ≤
      2 / c * Real.exp (-(c / 2) * t) := by
  have heq : ∀ r : ℝ, Real.exp (-c * (t - r)) * Real.exp (-(c / 2) * r) =
      Real.exp (-c * t + c / 2 * r) := by
    intro r
    rw [← Real.exp_add]
    ring_nf
  simp_rw [heq]
  have hF : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt (fun r => (2 / c) * Real.exp (-c * t + c / 2 * r))
      (Real.exp (-c * t + c / 2 * r)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -c * t + c / 2 * r) (c / 2) r := by
      simpa using ((hasDerivAt_id r).const_mul (c / 2)).const_add (-c * t)
    convert (h1.exp).const_mul (2 / c) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hF (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : -c * t + c / 2 * t = -(c / 2) * t := by ring
  rw [h1]
  have := Real.exp_pos (-c * t + c / 2 * 0)
  have h2c : 0 < 2 / c := by positivity
  nlinarith

/-- A monotone comparison of powers. -/
theorem pow_le_pow_of_one_le {x y : ℝ} {m n : ℕ} (h0 : 1 ≤ x) (hxy : x ≤ y) (hmn : m ≤ n) :
    x ^ m ≤ y ^ n :=
  (pow_le_pow_left₀ (by linarith) hxy m).trans (pow_le_pow_right₀ (h0.trans hxy) hmn)

/-- The slow integrand at one time. -/
theorem slow_integrand_le {ζ D Dp E W X R Y e a b : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hD : 0 ≤ D)
    (hDp : 0 ≤ Dp) (hE : 0 ≤ E) (hW : 0 ≤ W) (hWX : W ≤ X) (hR : 0 ≤ R) (hRY : R ≤ Y)
    (he : 0 ≤ e) (ha : a ≤ W * (D + R * E)) (hb : b ≤ W * (ζ * D + e * Dp + R * E)) :
    ζ ^ 2 * a + ζ * b ≤ X * (2 * ζ ^ 2 * D + 2 * Y * E) + X * (ζ * Dp) * e := by
  have hζ2 : ζ ^ 2 ≤ 1 := by nlinarith
  have h1 : ζ ^ 2 * a + ζ * b ≤
      W * (2 * ζ ^ 2 * D + (ζ ^ 2 + ζ) * R * E) + W * (ζ * Dp) * e := by
    have h2 : ζ ^ 2 * a ≤ ζ ^ 2 * (W * (D + R * E)) := mul_le_mul_of_nonneg_left ha (sq_nonneg ζ)
    have h3 : ζ * b ≤ ζ * (W * (ζ * D + e * Dp + R * E)) := mul_le_mul_of_nonneg_left hb hζ
    linarith [h2, h3]
  have h4 : (ζ ^ 2 + ζ) * R * E ≤ 2 * Y * E := by
    have : (ζ ^ 2 + ζ) * R ≤ 2 * Y := mul_le_mul (by linarith) hRY hR (by norm_num)
    exact mul_le_mul_of_nonneg_right this hE
  have h5 : 0 ≤ 2 * ζ ^ 2 * D + (ζ ^ 2 + ζ) * R * E := by positivity
  have h6 : 0 ≤ ζ * Dp * e := by positivity
  have h7 := mul_le_mul hWX (add_le_add (le_refl (2 * ζ ^ 2 * D)) h4) h5 (hW.trans hWX)
  have h8 := mul_le_mul_of_nonneg_right hWX h6
  linarith

/-- The fast integrand at one time (before the exponential weight). -/
theorem fast_integrand_le {ζ D Dp E W X R Y e a b : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hD : 0 ≤ D)
    (hDp : 0 ≤ Dp) (hE : 0 ≤ E) (hW : 0 ≤ W) (hWX : W ≤ X) (hR : 0 ≤ R) (hRY : R ≤ Y)
    (he : 0 ≤ e) (ha : a ≤ W * (D + R * E)) (hb : b ≤ W * (ζ * D + e * Dp + R * E)) :
    ζ * a + b ≤ X * (2 * ζ * D + 2 * Y * E) + X * Dp * e := by
  have h1 : ζ * a + b ≤ W * (2 * ζ * D + (ζ + 1) * R * E) + W * Dp * e := by
    have h2 : ζ * a ≤ ζ * (W * (D + R * E)) := mul_le_mul_of_nonneg_left ha hζ
    linarith [h2, hb]
  have h4 : (ζ + 1) * R * E ≤ 2 * Y * E := by
    have : (ζ + 1) * R ≤ 2 * Y := mul_le_mul (by linarith) hRY hR (by norm_num)
    exact mul_le_mul_of_nonneg_right this hE
  have h5 : 0 ≤ 2 * ζ * D + (ζ + 1) * R * E := by positivity
  have h6 : 0 ≤ Dp * e := by positivity
  have h7 := mul_le_mul hWX (add_le_add (le_refl (2 * ζ * D)) h4) h5 (hW.trans hWX)
  have h8 := mul_le_mul_of_nonneg_right hWX h6
  linarith

/-- The slow integral, integrated: the final algebra. `P = 1 + ζ²t`, `T = 1 + t`,
`p = P^{k-1}`, `q = T^{k-1}`, `Λ = L^{k-1}`. -/
theorem slow_final_le {ζ t D Dp E c Λ p q : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hζDp : ζ * Dp ≤ D) (hΛ : 0 ≤ Λ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    t * (Λ * p * (2 * ζ ^ 2 * D + 2 * q * E)) + Λ * p * (ζ * Dp) * (2 / c) ≤
      Λ * (2 + 2 / c) * ((1 + ζ ^ 2 * t) * p * (D + (1 + t) * q * E)) := by
  have h2c : 0 < 2 / c := by positivity
  have hζt : 0 ≤ ζ ^ 2 * t := by positivity
  have hpD : 0 ≤ p * D := mul_nonneg hp hD
  have hqE : 0 ≤ q * E := mul_nonneg hq hE
  have h1 : t * (p * (2 * ζ ^ 2 * D)) ≤ 2 * ((1 + ζ ^ 2 * t) * p * D) := by
    have : ζ ^ 2 * t * (p * D) ≤ (1 + ζ ^ 2 * t) * (p * D) :=
      mul_le_mul_of_nonneg_right (by linarith) hpD
    have e1 : t * (p * (2 * ζ ^ 2 * D)) = 2 * (ζ ^ 2 * t * (p * D)) := by ring
    have e2 : 2 * ((1 + ζ ^ 2 * t) * p * D) = 2 * ((1 + ζ ^ 2 * t) * (p * D)) := by ring
    rw [e1, e2]
    linarith
  have h2 : t * (p * (2 * q * E)) ≤ 2 * ((1 + ζ ^ 2 * t) * p * ((1 + t) * q * E)) := by
    have hA : t * (q * E) ≤ (1 + t) * (q * E) := mul_le_mul_of_nonneg_right (by linarith) hqE
    have hB : p * ((1 + t) * (q * E)) ≤ (1 + ζ ^ 2 * t) * (p * ((1 + t) * (q * E))) := by
      have : 0 ≤ p * ((1 + t) * (q * E)) := by positivity
      have : 0 ≤ ζ ^ 2 * t * (p * ((1 + t) * (q * E))) := by positivity
      linarith
    have hC := mul_le_mul_of_nonneg_left hA hp
    have e1 : t * (p * (2 * q * E)) = 2 * (p * (t * (q * E))) := by ring
    have e2 : 2 * ((1 + ζ ^ 2 * t) * p * ((1 + t) * q * E)) =
        2 * ((1 + ζ ^ 2 * t) * (p * ((1 + t) * (q * E)))) := by ring
    rw [e1, e2]
    linarith
  have h3 : p * (ζ * Dp) * (2 / c) ≤ (2 / c) * ((1 + ζ ^ 2 * t) * p * D) := by
    have h4 : p * (ζ * Dp) ≤ p * D := mul_le_mul_of_nonneg_left hζDp hp
    have h5 : p * D ≤ (1 + ζ ^ 2 * t) * p * D := by
      have : 0 ≤ ζ ^ 2 * t * (p * D) := by positivity
      have e : (1 + ζ ^ 2 * t) * p * D = p * D + ζ ^ 2 * t * (p * D) := by ring
      rw [e]
      linarith
    have := mul_le_mul_of_nonneg_right (h4.trans h5) h2c.le
    linarith
  have hX : 0 ≤ (2 / c) * ((1 + ζ ^ 2 * t) * p * ((1 + t) * q * E)) := by positivity
  have hsum : t * (p * (2 * ζ ^ 2 * D + 2 * q * E)) + p * (ζ * Dp) * (2 / c) ≤
      (2 + 2 / c) * ((1 + ζ ^ 2 * t) * p * (D + (1 + t) * q * E)) := by
    have e1 : t * (p * (2 * ζ ^ 2 * D + 2 * q * E)) =
        t * (p * (2 * ζ ^ 2 * D)) + t * (p * (2 * q * E)) := by ring
    have e2 : (2 + 2 / c) * ((1 + ζ ^ 2 * t) * p * (D + (1 + t) * q * E)) =
        2 * ((1 + ζ ^ 2 * t) * p * D) + 2 * ((1 + ζ ^ 2 * t) * p * ((1 + t) * q * E)) +
          (2 / c) * ((1 + ζ ^ 2 * t) * p * D) +
          (2 / c) * ((1 + ζ ^ 2 * t) * p * ((1 + t) * q * E)) := by ring
    rw [e1, e2]
    linarith
  calc t * (Λ * p * (2 * ζ ^ 2 * D + 2 * q * E)) + Λ * p * (ζ * Dp) * (2 / c)
      = Λ * (t * (p * (2 * ζ ^ 2 * D + 2 * q * E)) + p * (ζ * Dp) * (2 / c)) := by ring
    _ ≤ Λ * ((2 + 2 / c) * ((1 + ζ ^ 2 * t) * p * (D + (1 + t) * q * E))) :=
        mul_le_mul_of_nonneg_left hsum hΛ
    _ = _ := by ring

/-- The fast integral, integrated: the final algebra. -/
theorem fast_final_le {ζ t D Dp E c Λ p q e : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hζ : 0 ≤ ζ)
    (hD : 0 ≤ D) (hDp : 0 ≤ Dp) (hE : 0 ≤ E) (hΛ : 0 ≤ Λ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (he : 0 ≤ e) :
    Λ * p * (2 * ζ * D + 2 * q * E) * (1 / c) + Λ * p * Dp * (2 / c * e) ≤
      Λ * (2 / c) * ((1 + ζ ^ 2 * t) * p * (ζ * D + e * Dp + (1 + t) * q * E)) := by
  have h0 : 0 ≤ ζ * D + e * Dp + q * E := by positivity
  have h1 : p * (ζ * D + e * Dp + q * E) ≤ (1 + ζ ^ 2 * t) * p * (ζ * D + e * Dp + q * E) := by
    have : 0 ≤ ζ ^ 2 * t * (p * (ζ * D + e * Dp + q * E)) := by positivity
    have e1 : (1 + ζ ^ 2 * t) * p * (ζ * D + e * Dp + q * E) =
        p * (ζ * D + e * Dp + q * E) + ζ ^ 2 * t * (p * (ζ * D + e * Dp + q * E)) := by ring
    rw [e1]
    linarith
  have h2 : (1 + ζ ^ 2 * t) * p * (ζ * D + e * Dp + q * E) ≤
      (1 + ζ ^ 2 * t) * p * (ζ * D + e * Dp + (1 + t) * q * E) := by
    have : q * E ≤ (1 + t) * q * E := by
      have : 0 ≤ t * (q * E) := by positivity
      have e1 : (1 + t) * q * E = q * E + t * (q * E) := by ring
      rw [e1]
      linarith
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hL : Λ * p * (2 * ζ * D + 2 * q * E) * (1 / c) + Λ * p * Dp * (2 / c * e) =
      Λ * (2 / c) * (p * (ζ * D + e * Dp + q * E)) := by
    field_simp
    ring
  rw [hL]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

/-- Integrating the slow majorant. -/
theorem integral_slow_majorant_le {c t X K₁ Z₂ : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hXZ : 0 ≤ X * Z₂)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 t)
    (hle : ∀ r ∈ Icc 0 t, f r ≤ X * K₁ + X * Z₂ * Real.exp (-(c / 2) * r)) :
    ∫ r in (0 : ℝ)..t, f r ≤ t * (X * K₁) + X * Z₂ * (2 / c) := by
  have hg : IntervalIntegrable (fun r => X * K₁ + X * Z₂ * Real.exp (-(c / 2) * r)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  refine (integral_mono_on ht hf hg hle).trans ?_
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, sub_zero, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left (integral_exp_neg_half_le (t := t) hc) hXZ
  linarith

/-- Integrating the fast majorant. -/
theorem integral_fast_majorant_le {c t X K₁ Z₂ : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hXK : 0 ≤ X * K₁)
    (hXZ : 0 ≤ X * Z₂) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 t)
    (hle : ∀ r ∈ Icc 0 t, f r ≤ X * K₁ * Real.exp (-c * (t - r)) +
      X * Z₂ * (Real.exp (-c * (t - r)) * Real.exp (-(c / 2) * r))) :
    ∫ r in (0 : ℝ)..t, f r ≤ X * K₁ * (1 / c) + X * Z₂ * (2 / c * Real.exp (-(c / 2) * t)) := by
  have hg : IntervalIntegrable (fun r => X * K₁ * Real.exp (-c * (t - r)) +
      X * Z₂ * (Real.exp (-c * (t - r)) * Real.exp (-(c / 2) * r))) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  refine (integral_mono_on ht hf hg hle).trans ?_
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (integral_exp_neg_sub_le (t := t) hc) hXK
  have h2 := mul_le_mul_of_nonneg_left (integral_exp_neg_sub_mul_half_le (t := t) hc) hXZ
  linarith

/-- Combining the stages: `X ≤ D₀ + Θ ∑_{k'<k} S_{k'}` with `S_{k'} ≤ Λ K Z`, `D₀ ≤ Z`,
`1 + Θ k Λ K ≤ L^k` gives `X ≤ L^k Z`. -/
theorem stage_combine {k : ℕ} {X D₀ Θ Λ K Z Lk : ℝ} {S : ℕ → ℝ} (hΘ : 0 ≤ Θ) (hZ : 0 ≤ Z)
    (hX : X ≤ D₀ + Θ * ∑ k' ∈ Finset.range k, S k')
    (hS : ∀ k' ∈ Finset.range k, S k' ≤ Λ * K * Z) (hD₀ : D₀ ≤ Z)
    (hL : 1 + Θ * k * Λ * K ≤ Lk) : X ≤ Lk * Z := by
  have hsum : ∑ k' ∈ Finset.range k, S k' ≤ k * (Λ * K * Z) := by
    calc ∑ k' ∈ Finset.range k, S k' ≤ ∑ _k' ∈ Finset.range k, Λ * K * Z := Finset.sum_le_sum hS
      _ = k * (Λ * K * Z) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : Θ * ∑ k' ∈ Finset.range k, S k' ≤ Θ * (k * (Λ * K * Z)) :=
    mul_le_mul_of_nonneg_left hsum hΘ
  have h2 : (1 + Θ * k * Λ * K) * Z ≤ Lk * Z := mul_le_mul_of_nonneg_right hL hZ
  have e : (1 + Θ * k * Λ * K) * Z = Z + Θ * (k * (Λ * K * Z)) := by ring
  rw [e] at h2
  linarith

/-- `1 + Θ k L^{k-1} K ≤ L^k` when `L = 1 + Θ M K'` with `K ≤ K'`, `k ≤ M`. -/
theorem one_add_le_pow {Θ K K' : ℝ} {k M : ℕ} (hΘ : 0 ≤ Θ) (hK : 0 ≤ K) (hKK : K ≤ K')
    (hk : k ≤ M) : 1 + Θ * k * (1 + Θ * M * K') ^ (k - 1) * K ≤ (1 + Θ * M * K') ^ k := by
  set L := 1 + Θ * M * K' with hL
  have hK'0 : 0 ≤ K' := hK.trans hKK
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Θ * M * K' := by positivity
    linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have hLk1 : 1 ≤ L ^ (k - 1) := one_le_pow₀ hL1
    have hpow : L ^ k = L ^ (k - 1) + Θ * M * K' * L ^ (k - 1) := by
      have : L ^ k = L * L ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this, hL]
      ring
    rw [hpow]
    have hkM : (k : ℝ) ≤ M := by exact_mod_cast hk
    have h1 : Θ * k * K ≤ Θ * M * K' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hkM hΘ) hKK hK (by positivity)
    have h2 : Θ * k * K * L ^ (k - 1) ≤ Θ * M * K' * L ^ (k - 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have e : Θ * k * L ^ (k - 1) * K = Θ * k * K * L ^ (k - 1) := by ring
    rw [e]
    linarith

/-- **The triangular Grönwall inequality, majorant form.** Each stage is bounded through
continuous majorants of the earlier stages on `[0, t]`; no measurability of `A`, `B` is needed
(the fast seminorms are suprema over time-dependent test classes). -/
theorem triangularGronwall_majorant {M : ℕ} {T c ζ Θ D Dp E : ℝ} (hc : 0 < c) (hζ : 0 ≤ ζ)
    (hζ1 : ζ ≤ 1) (hΘ : 0 ≤ Θ) (hD : 0 ≤ D) (hDp : 0 ≤ Dp) (hζDp : ζ * Dp ≤ D) (hE : 0 ≤ E)
    (A B : ℕ → ℝ → ℝ)
    (hA : ∀ k < M, ∀ t ∈ Icc 0 T, ∀ a b : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a k') ∧ Continuous (b k') ∧
        ∀ r ∈ Icc 0 t, A k' r ≤ a k' r ∧ B k' r ≤ b k' r) →
      A k t ≤ D + E + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a k' r + ζ * b k' r))
    (hB : ∀ k < M, ∀ t ∈ Icc 0 T, ∀ a b : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a k') ∧ Continuous (b k') ∧
        ∀ r ∈ Icc 0 t, A k' r ≤ a k' r ∧ B k' r ≤ b k' r) →
      B k t ≤ Real.exp (-c * t) * Dp + E + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, Real.exp (-c * (t - r)) * (ζ * a k' r + b k' r)) :
    ∀ k < M, ∀ t ∈ Icc 0 T,
      A k t ≤ (1 + Θ * M * (2 + 2 / c)) ^ k * (1 + ζ ^ 2 * t) ^ k * (D + (1 + t) ^ k * E) ∧
      B k t ≤ (1 + Θ * M * (2 + 2 / c)) ^ k * (1 + ζ ^ 2 * t) ^ k *
        (ζ * D + Real.exp (-(c / 2) * t) * Dp + (1 + t) ^ k * E) := by
  have hL1 : 1 ≤ 1 + Θ * M * (2 + 2 / c) := by
    have : 0 ≤ Θ * M * (2 + 2 / c) := by positivity
    linarith
  -- the inductive bounds, as continuous majorants
  set bA : ℕ → ℝ → ℝ := fun k' r => (1 + Θ * M * (2 + 2 / c)) ^ k' * (1 + ζ ^ 2 * r) ^ k' *
    (D + (1 + r) ^ k' * E) with hbA
  set bB : ℕ → ℝ → ℝ := fun k' r => (1 + Θ * M * (2 + 2 / c)) ^ k' * (1 + ζ ^ 2 * r) ^ k' *
    (ζ * D + Real.exp (-(c / 2) * r) * Dp + (1 + r) ^ k' * E) with hbB
  have hbAc : ∀ k', Continuous (bA k') := fun k' => by rw [hbA]; fun_prop
  have hbBc : ∀ k', Continuous (bB k') := fun k' => by rw [hbB]; fun_prop
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk t ht
  have ht0 : 0 ≤ t := ht.1
  have hP1 : 1 ≤ 1 + ζ ^ 2 * t := by
    have := mul_nonneg (sq_nonneg ζ) ht0
    linarith
  have hT1 : 1 ≤ 1 + t := by linarith
  have hΛ0 : 0 ≤ (1 + Θ * M * (2 + 2 / c)) ^ (k - 1) := pow_nonneg (by linarith) _
  have hp0 : 0 ≤ (1 + ζ ^ 2 * t) ^ (k - 1) := pow_nonneg (by linarith) _
  have hq0 : 0 ≤ (1 + t) ^ (k - 1) := pow_nonneg (by linarith) _
  have hmaj : ∀ k' < k, Continuous (bA k') ∧ Continuous (bB k') ∧
      ∀ r ∈ Icc 0 t, A k' r ≤ bA k' r ∧ B k' r ≤ bB k' r := fun k' hk' =>
    ⟨hbAc k', hbBc k', fun r hr => ih k' hk' (hk'.trans hk) r ⟨hr.1, hr.2.trans ht.2⟩⟩
  -- the majorants of the earlier stages at every earlier time
  have hpt : ∀ k' ∈ Finset.range k, ∀ r ∈ Icc (0 : ℝ) t,
      ζ ^ 2 * bA k' r + ζ * bB k' r ≤
        ((1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1)) *
            (2 * ζ ^ 2 * D + 2 * (1 + t) ^ (k - 1) * E) +
          ((1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1)) * (ζ * Dp) *
            Real.exp (-(c / 2) * r) ∧
      ζ * bA k' r + bB k' r ≤
        ((1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1)) *
            (2 * ζ * D + 2 * (1 + t) ^ (k - 1) * E) +
          ((1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1)) * Dp *
            Real.exp (-(c / 2) * r) := by
    intro k' hk' r hr
    have hk'k : k' < k := Finset.mem_range.1 hk'
    have hr0 : 0 ≤ r := hr.1
    have hPr : 1 ≤ 1 + ζ ^ 2 * r := by
      have := mul_nonneg (sq_nonneg ζ) hr0
      linarith
    have hPrt : 1 + ζ ^ 2 * r ≤ 1 + ζ ^ 2 * t := by
      have := mul_le_mul_of_nonneg_left hr.2 (sq_nonneg ζ)
      linarith
    have hW0 : 0 ≤ (1 + Θ * M * (2 + 2 / c)) ^ k' * (1 + ζ ^ 2 * r) ^ k' :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
    have hWX : (1 + Θ * M * (2 + 2 / c)) ^ k' * (1 + ζ ^ 2 * r) ^ k' ≤
        (1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1) :=
      mul_le_mul (pow_le_pow_right₀ hL1 (by omega)) (pow_le_pow_of_one_le hPr hPrt (by omega))
        (pow_nonneg (by linarith) _) hΛ0
    have hR0 : 0 ≤ (1 + r) ^ k' := pow_nonneg (by linarith) _
    have hRY : (1 + r) ^ k' ≤ (1 + t) ^ (k - 1) :=
      pow_le_pow_of_one_le (by linarith) (by linarith [hr.2]) (by omega)
    have he := (Real.exp_pos (-(c / 2) * r)).le
    exact ⟨slow_integrand_le hζ hζ1 hD hDp hE hW0 hWX hR0 hRY he le_rfl le_rfl,
      fast_integrand_le hζ hζ1 hD hDp hE hW0 hWX hR0 hRY he le_rfl le_rfl⟩
  -- powers at stage `k ≥ 1`
  have hsplit : ∀ k' ∈ Finset.range k,
      (1 + ζ ^ 2 * t) ^ k = (1 + ζ ^ 2 * t) * (1 + ζ ^ 2 * t) ^ (k - 1) ∧
      (1 + t) ^ k = (1 + t) * (1 + t) ^ (k - 1) := by
    intro k' hk'
    have hk1 : k = k - 1 + 1 := by have := Finset.mem_range.1 hk'; omega
    constructor
    · conv_lhs => rw [hk1]
      rw [pow_succ, mul_comm]
    · conv_lhs => rw [hk1]
      rw [pow_succ, mul_comm]
  have hXK : 0 ≤ (1 + Θ * M * (2 + 2 / c)) ^ (k - 1) * (1 + ζ ^ 2 * t) ^ (k - 1) :=
    mul_nonneg hΛ0 hp0
  constructor
  · -- the slow coordinate
    refine (mul_assoc ((1 + Θ * M * (2 + 2 / c)) ^ k) ((1 + ζ ^ 2 * t) ^ k)
      (D + (1 + t) ^ k * E)).symm ▸ stage_combine hΘ (by positivity) (hA k hk t ht bA bB hmaj) ?_
        ?_ (one_add_le_pow hΘ (by positivity) le_rfl hk.le)
    · intro k' hk'
      have hint : IntervalIntegrable (fun r => ζ ^ 2 * bA k' r + ζ * bB k' r) volume 0 t := by
        apply Continuous.intervalIntegrable
        exact (continuous_const.mul (hbAc k')).add (continuous_const.mul (hbBc k'))
      have h1 := integral_slow_majorant_le hc ht0 (mul_nonneg hXK (mul_nonneg hζ hDp)) hint
        (fun r hr => (hpt k' hk' r hr).1)
      have h2 := slow_final_le (ζ := ζ) hc ht0 hD hE hζDp hΛ0 hp0 hq0
      obtain ⟨e1, e2⟩ := hsplit k' hk'
      rw [e1, e2]
      exact h1.trans h2
    · have h1 : 1 ≤ (1 + ζ ^ 2 * t) ^ k := one_le_pow₀ hP1
      have h2 : 1 ≤ (1 + t) ^ k := one_le_pow₀ hT1
      have h3 : D + E ≤ D + (1 + t) ^ k * E := by nlinarith
      have h4 : 0 ≤ D + (1 + t) ^ k * E := by positivity
      nlinarith
  · -- the fast seminorm
    refine (mul_assoc ((1 + Θ * M * (2 + 2 / c)) ^ k) ((1 + ζ ^ 2 * t) ^ k)
      (ζ * D + Real.exp (-(c / 2) * t) * Dp + (1 + t) ^ k * E)).symm ▸
        stage_combine hΘ (by positivity) (hB k hk t ht bA bB hmaj) ?_ ?_
        (one_add_le_pow hΘ (K := 2 / c) (by positivity) (by linarith) hk.le)
    · intro k' hk'
      have hint : IntervalIntegrable (fun r => Real.exp (-c * (t - r)) * (ζ * bA k' r + bB k' r))
          volume 0 t := by
        apply Continuous.intervalIntegrable
        exact (by fun_prop : Continuous fun r : ℝ => Real.exp (-c * (t - r))).mul
          ((continuous_const.mul (hbAc k')).add (hbBc k'))
      have h1 := integral_fast_majorant_le (K₁ := 2 * ζ * D + 2 * (1 + t) ^ (k - 1) * E) hc ht0
        (mul_nonneg hXK (by positivity)) (mul_nonneg hXK hDp) hint (fun r hr => by
          have h := mul_le_mul_of_nonneg_left (hpt k' hk' r hr).2 (Real.exp_pos (-c * (t - r))).le
          exact h.trans (le_of_eq (by ring)))
      have h2 := fast_final_le (ζ := ζ) hc ht0 hζ hD hDp hE hΛ0 hp0 hq0
        (Real.exp_pos (-(c / 2) * t)).le
      obtain ⟨e1, e2⟩ := hsplit k' hk'
      rw [e1, e2]
      exact h1.trans h2
    · have h1 : 1 ≤ (1 + ζ ^ 2 * t) ^ k := one_le_pow₀ hP1
      have h2 : 1 ≤ (1 + t) ^ k := one_le_pow₀ hT1
      have h5 : Real.exp (-c * t) ≤ Real.exp (-(c / 2) * t) :=
        Real.exp_le_exp.2 (by nlinarith)
      have h3 : Real.exp (-c * t) * Dp + E ≤
          ζ * D + Real.exp (-(c / 2) * t) * Dp + (1 + t) ^ k * E := by
        have := mul_le_mul_of_nonneg_right h5 hDp
        have := mul_nonneg hζ hD
        nlinarith
      have h4 : 0 ≤ ζ * D + Real.exp (-(c / 2) * t) * Dp + (1 + t) ^ k * E := by positivity
      nlinarith

/-- **The majorant form with stage-dependent monotone data.** -/
theorem triangularGronwall_majorant_mono {M : ℕ} {T c ζ Θ : ℝ} (D Dp E : ℕ → ℝ) (hc : 0 < c)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hΘ : 0 ≤ Θ) (hDm : Monotone D) (hDpm : Monotone Dp)
    (hEm : Monotone E) (hD : ∀ k, 0 ≤ D k) (hDp : ∀ k, 0 ≤ Dp k) (hζDp : ∀ k, ζ * Dp k ≤ D k)
    (hE : ∀ k, 0 ≤ E k) (A B : ℕ → ℝ → ℝ)
    (hA : ∀ k < M, ∀ t ∈ Icc 0 T, ∀ a b : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a k') ∧ Continuous (b k') ∧
        ∀ r ∈ Icc 0 t, A k' r ≤ a k' r ∧ B k' r ≤ b k' r) →
      A k t ≤ D k + E k + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a k' r + ζ * b k' r))
    (hB : ∀ k < M, ∀ t ∈ Icc 0 T, ∀ a b : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a k') ∧ Continuous (b k') ∧
        ∀ r ∈ Icc 0 t, A k' r ≤ a k' r ∧ B k' r ≤ b k' r) →
      B k t ≤ Real.exp (-c * t) * Dp k + E k + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, Real.exp (-c * (t - r)) * (ζ * a k' r + b k' r)) :
    ∀ k < M, ∀ t ∈ Icc 0 T,
      A k t ≤ (1 + Θ * M * (2 + 2 / c)) ^ k * (1 + ζ ^ 2 * t) ^ k * (D k + (1 + t) ^ k * E k) ∧
      B k t ≤ (1 + Θ * M * (2 + 2 / c)) ^ k * (1 + ζ ^ 2 * t) ^ k *
        (ζ * D k + Real.exp (-(c / 2) * t) * Dp k + (1 + t) ^ k * E k) := by
  intro k hk t ht
  have hkM : k + 1 ≤ M := hk
  have h := triangularGronwall_majorant (M := k + 1) (T := T) (D := D k) (Dp := Dp k) (E := E k)
    hc hζ hζ1 hΘ (hD k) (hDp k) (hζDp k) (hE k) A B
    (fun k' hk' t' ht' a b hab => (hA k' (lt_of_lt_of_le hk' hkM) t' ht' a b hab).trans (by
      have := hDm (Nat.lt_succ_iff.1 hk')
      have := hEm (Nat.lt_succ_iff.1 hk')
      linarith))
    (fun k' hk' t' ht' a b hab => (hB k' (lt_of_lt_of_le hk' hkM) t' ht' a b hab).trans (by
      have h1 := hDpm (Nat.lt_succ_iff.1 hk')
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-c * t')).le
      have := hEm (Nat.lt_succ_iff.1 hk')
      linarith)) k (Nat.lt_succ_self k) t ht
  have hc2 : 0 ≤ 2 + 2 / c := by positivity
  have hL : 1 + Θ * ((k + 1 : ℕ) : ℝ) * (2 + 2 / c) ≤ 1 + Θ * M * (2 + 2 / c) := by
    have : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hkM
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hΘ) hc2
    linarith
  have hL0 : 0 ≤ 1 + Θ * ((k + 1 : ℕ) : ℝ) * (2 + 2 / c) := by positivity
  have hpow := pow_le_pow_left₀ hL0 hL k
  have ht0 : 0 ≤ t := ht.1
  have hP : 0 ≤ (1 + ζ ^ 2 * t) ^ k := pow_nonneg (by positivity) _
  have hX1 : 0 ≤ D k + (1 + t) ^ k * E k := add_nonneg (hD k) (mul_nonneg (by positivity) (hE k))
  have hX2 : 0 ≤ ζ * D k + Real.exp (-(c / 2) * t) * Dp k + (1 + t) ^ k * E k := by
    have := hD k
    have := hDp k
    have := hE k
    positivity
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hP) hX1),
    h.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hP) hX2)⟩

end AVRegularity.Analysis
end
end

section
@[expose] public section
end
end

section
@[expose] public section
end
end
end

section
/-! Public interface to the paired convolution analysis. -/
end
