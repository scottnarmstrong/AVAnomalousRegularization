-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
public import AVRegularity.CycleComparison.QuietDecay.Source.Rep
import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.FullX
public import AVRegularity.Definitions.Construction.DiagLetter

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **The source-mean step, the matching of the letters with the path sum: the algebra**.

`sourceMean_match_algebra`: abstractly, with `x` ranging over the paths into a component (a finite
set `P`), `k` over the active pulses with their cutoffs `c k`, and `Dq x n a a' k` the dressed
term of degree `n` and covariance orders `(a, a')` of the path `x` on the pulse `k`:

* the quadratic conversions give `∑_x ∑_k c_k • Dq x 2 0 0 k`;
* the letters `𝖬_n`, `3 ≤ n ≤ nMax`, give `∑_x (∑_k c_k • Dmn x n k - dir x n)`, with their own
  dressed terms `Dmn`, equal to `Dq x n 0 0 k` whenever `c k ≠ 0`, and the direct parts `dir`;
* the letters `𝖵_{n,a,a'}`, `2 ≤ n ≤ nMax`, `a, a' ≤ p`, `1 ≤ a + a'`, give `∑_x ∑_k c_k • Dcv`,
  with `Dcv = Dq` whenever `c k ≠ 0`;
* the direct transports give back `∑_n ∑_x dir x n`;
* the dressed terms of the degrees `n > nMax` vanish whenever `c k ≠ 0`.

Their sum is `∑_k c_k • ∑_x ∑_{n=2}^{Ntop} ∑_{a,a' ≤ p} Dq x n a a' k`, for `2 ≤ nMax ≤ Ntop`.

For `P = ∅`, or when every `c k = 0`, both sides are `0` whatever the dressed terms; for
`p = 0` there is no covariance letter. -/

/-- Splitting off the pair `(0, 0)` of a double sum over `range (p + 1)`. -/
theorem sum_range_pair_split {V : Type*} [AddCommMonoid V] (p : ℕ) (f : ℕ → ℕ → V) :
    ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1), f a a' =
      f 0 0 + ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
        (if 1 ≤ a + a' then f a a' else 0) := by
  have h0 : ∀ a a' : ℕ, f a a' =
      (if a = 0 ∧ a' = 0 then f 0 0 else 0) + (if 1 ≤ a + a' then f a a' else 0) := by
    intro a a'
    by_cases h : a = 0 ∧ a' = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have h1 : 1 ≤ a + a' := by omega
      simp [h, h1]
  have h1 : ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
      (if a = 0 ∧ a' = 0 then f 0 0 else (0 : V)) = f 0 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro a' _ ha'
        simp [ha']
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos p)) h
    · intro a _ ha
      refine Finset.sum_eq_zero fun a' _ => ?_
      simp [ha]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos p)) h
  conv_lhs => rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => h0 a a']
  simp only [Finset.sum_add_distrib]
  rw [h1]

/-- **The matching of the letters with the path sum (algebra).** -/
theorem sourceMean_match_algebra {ι R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    (Ks : Finset ℤ) (c : ℤ → R) (P : Finset ι) (nMax Ntop p : ℕ)
    (h2 : 2 ≤ nMax) (hN : nMax ≤ Ntop)
    (Dq : ι → ℕ → ℕ → ℕ → ℤ → V) (Dmn : ι → ℕ → ℤ → V) (Dcv : ι → ℕ → ℕ → ℕ → ℤ → V)
    (dir : ι → ℕ → V)
    (hmn : ∀ x ∈ P, ∀ n, ∀ k ∈ Ks, c k ≠ 0 → Dmn x n k = Dq x n 0 0 k)
    (hcv : ∀ x ∈ P, ∀ n a a', ∀ k ∈ Ks, c k ≠ 0 → Dcv x n a a' k = Dq x n a a' k)
    (hhigh : ∀ x ∈ P, ∀ n a a', nMax < n → ∀ k ∈ Ks, c k ≠ 0 → Dq x n a a' k = 0) :
    (∑ x ∈ P, ∑ k ∈ Ks, c k • Dq x 2 0 0 k) +
      (∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, ((∑ k ∈ Ks, c k • Dmn x n k) - dir x n)) +
      (∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
        ∑ x ∈ P, if 1 ≤ a + a' then ∑ k ∈ Ks, c k • Dcv x n a a' k else 0) +
      (∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, dir x n) =
    ∑ k ∈ Ks, c k • ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 Ntop, ∑ a ∈ Finset.range (p + 1),
      ∑ a' ∈ Finset.range (p + 1), Dq x n a a' k := by
  set T : ι → ℕ → ℕ → ℕ → V := fun x n a a' => ∑ k ∈ Ks, c k • Dq x n a a' k with hT
  have emn : ∀ x ∈ P, ∀ n, ∑ k ∈ Ks, c k • Dmn x n k = T x n 0 0 := by
    intro x hx n
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hc : c k = 0
    · rw [hc, zero_smul, zero_smul]
    · rw [hmn x hx n k hk hc]
  have ecv : ∀ x ∈ P, ∀ n a a', ∑ k ∈ Ks, c k • Dcv x n a a' k = T x n a a' := by
    intro x hx n a a'
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hc : c k = 0
    · rw [hc, zero_smul, zero_smul]
    · rw [hcv x hx n a a' k hk hc]
  have ehigh : ∀ x ∈ P, ∀ n a a', nMax < n → T x n a a' = 0 := by
    intro x hx n a a' hn
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hc : c k = 0
    · rw [hc, zero_smul]
    · rw [hhigh x hx n a a' hn k hk hc, smul_zero]
  -- the right side as a sum of `T`
  have hR : ∑ k ∈ Ks, c k • ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 Ntop, ∑ a ∈ Finset.range (p + 1),
      ∑ a' ∈ Finset.range (p + 1), Dq x n a a' k =
      ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1),
        ∑ a' ∈ Finset.range (p + 1), T x n a a' := by
    have e1 : ∑ k ∈ Ks, c k • ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 Ntop, ∑ a ∈ Finset.range (p + 1),
        ∑ a' ∈ Finset.range (p + 1), Dq x n a a' k =
        ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 Ntop, ∑ a ∈ Finset.range (p + 1),
          ∑ a' ∈ Finset.range (p + 1), T x n a a' := by
      simp only [hT, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    refine Finset.sum_congr rfl fun x hx => ?_
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hN) ?_
    intro n hn hnn
    have hn' := Finset.mem_Icc.1 hn
    have hlt : nMax < n := by
      by_contra hc
      exact hnn (Finset.mem_Icc.2 ⟨hn'.1, by omega⟩)
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun a' _ => ?_
    exact ehigh x hx n a a' hlt
  rw [hR]
  -- the left side as a sum of `T`
  have hL1 : ∑ x ∈ P, ∑ k ∈ Ks, c k • Dq x 2 0 0 k = ∑ x ∈ P, T x 2 0 0 := rfl
  have hL2 : ∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, ((∑ k ∈ Ks, c k • Dmn x n k) - dir x n) =
      (∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, T x n 0 0) -
        ∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, dir x n := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [emn x hx n]
  have hL3 : ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
      ∑ x ∈ P, (if 1 ≤ a + a' then ∑ k ∈ Ks, c k • Dcv x n a a' k else 0) =
      ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
        ∑ x ∈ P, (if 1 ≤ a + a' then T x n a a' else 0) := by
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun x hx => ?_
    rw [ecv x hx n a a']
  rw [hL1, hL2, hL3]
  -- the pair `(0, 0)` and the degree `2`
  have hsplit : ∀ x n, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1), T x n a a' =
      T x n 0 0 + ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
        (if 1 ≤ a + a' then T x n a a' else 0) := fun x n =>
    sum_range_pair_split p (T x n)
  have hI : Finset.Icc 2 nMax = insert 2 (Finset.Icc 3 nMax) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h2n : (2 : ℕ) ∉ Finset.Icc 3 nMax := by
    simp
  have hR2 : ∑ x ∈ P, ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1),
      ∑ a' ∈ Finset.range (p + 1), T x n a a' =
      (∑ x ∈ P, T x 2 0 0) + (∑ n ∈ Finset.Icc 3 nMax, ∑ x ∈ P, T x n 0 0) +
        ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
          ∑ x ∈ P, (if 1 ≤ a + a' then T x n a a' else 0) := by
    simp only [hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [hI]
      simp only [Finset.sum_insert h2n, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
  rw [hR2]
  abel

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The first-source-flux step, sub-step Algebra, pure part: the covariance operator, its iterates and the
polynomials `covPolyP`, `covPolyQ` commute with translations of the argument (no regularity), and
with a continuous linear map `ℓ` on fields of enough regularity (`C^{2n}` for the `n`-th power). -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translation: the covariance operator of a translated field. -/
theorem fsAlg_covOperator_shift (Hc : Matrix (Fin 2) (Fin 2) ℝ) (φ : Vec 2 → E) (x : Vec 2) :
    covOperator Hc (fun y => φ (x + y)) = fun y => covOperator Hc φ (x + y) := by
  funext y
  unfold covOperator
  simp only [fderiv_comp_add_left]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact fderiv_comp_add_left (f := fun z => fderiv ℝ φ z (basisVec j)) (x := y) x

theorem fsAlg_covOperator_iterate_shift (Hc : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (φ : Vec 2 → E) (x : Vec 2) :
    (covOperator Hc)^[n] (fun y => φ (x + y)) = fun y => (covOperator Hc)^[n] φ (x + y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      fsAlg_covOperator_shift]

theorem fsAlg_covPolyQ_shift (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E)
    (x y : Vec 2) : covPolyQ Hc p (fun z => φ (x + z)) y = covPolyQ Hc p φ (x + y) := by
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply, fsAlg_covOperator_iterate_shift]

theorem fsAlg_covPolyP_shift (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E)
    (x y : Vec 2) : covPolyP Hc p (fun z => φ (x + z)) y = covPolyP Hc p φ (x + y) := by
  unfold covPolyP
  simp only [Finset.sum_apply, Pi.smul_apply, fsAlg_covOperator_iterate_shift]

/-- A continuous linear map commutes with the covariance operator on `C²` fields. -/
theorem fsAlg_covOperator_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : E →L[ℝ] F) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ 2 φ) :
    covOperator Hc (fun y => ℓ (φ y)) = fun y => ℓ (covOperator Hc φ y) := by
  funext x
  have hd : ∀ y, DifferentiableAt ℝ φ y := fun y => hφ.differentiable (by norm_num) y
  have h1 : ∀ y, fderiv ℝ (fun y => ℓ (φ y)) y = ℓ.comp (fderiv ℝ φ y) := fun y =>
    (ℓ.hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv
  have h2 : ∀ j : Fin 2, DifferentiableAt ℝ (fun y => fderiv ℝ φ y (basisVec j)) x := fun j =>
    (((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) x
  unfold covOperator
  simp only [h1, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [show (fun y => (ℓ.comp (fderiv ℝ φ y)) (basisVec j)) =
      fun y => ℓ (fderiv ℝ φ y (basisVec j)) from rfl]
  exact congrArg (fun L => L (basisVec i))
    ((ℓ.hasFDerivAt.comp x (h2 j).hasFDerivAt).fderiv)

/-- Iterates: `C^{2n}` suffices. -/
theorem fsAlg_covOperator_iterate_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : E →L[ℝ] F) :
    ∀ (n : ℕ) {φ : Vec 2 → E}, ContDiff ℝ ((2 * n : ℕ) : ℕ∞) φ →
      (covOperator Hc)^[n] (fun y => ℓ (φ y)) = fun y => ℓ ((covOperator Hc)^[n] φ y)
  | 0, _, _ => rfl
  | n + 1, φ, hφ => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hφ' : ContDiff ℝ ((2 * n : ℕ) : ℕ∞) φ :=
      hφ.of_le (by exact_mod_cast (by omega : 2 * n ≤ 2 * (n + 1)))
    rw [fsAlg_covOperator_iterate_clm Hc ℓ n hφ']
    refine fsAlg_covOperator_clm Hc ℓ ?_
    have := Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc n 2 φ
      (by simpa [Nat.mul_succ, Nat.add_comm] using hφ)
    exact_mod_cast this

theorem fsAlg_covPolyQ_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : E →L[ℝ] F) (p : ℕ)
    {φ : Vec 2 → E} (hφ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) φ) (x : Vec 2) :
    covPolyQ Hc p (fun y => ℓ (φ y)) x = ℓ (covPolyQ Hc p φ x) := by
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [fsAlg_covOperator_iterate_clm Hc ℓ l
    (hφ.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p)))]

theorem fsAlg_covPolyP_clm (Hc : Matrix (Fin 2) (Fin 2) ℝ) (ℓ : E →L[ℝ] F) (p : ℕ)
    {φ : Vec 2 → E} (hφ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) φ) (x : Vec 2) :
    covPolyP Hc p (fun y => ℓ (φ y)) x = ℓ (covPolyP Hc p φ x) := by
  unfold covPolyP
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [fsAlg_covOperator_iterate_clm Hc ℓ l
    (hφ.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p)))]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

/-! The `ε`-Taylor coefficients of the source flux (the flux-regularity step, clauses 1 and 2).

`ε ↦ sourceFlux edge η ε t Φ k X z` is a polynomial in `ε` of degree `< D` whose coefficients are
the explicit expressions `SrcCoeff` (the `ε`-coefficients `srcW` of the covariant words). Hence
`iteratedDeriv ℓ _ 0 = ℓ! • SrcCoeff … ℓ`, and the coefficient is box smooth of order `(s, s)`
as soon as the edge coefficients are and `Φ` is box smooth of order `N'` with `s + D ≤ N' + 1`. -/

section Poly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `ℓ`-th derivative at `0` of a polynomial of degree `< n`. -/
theorem iteratedDeriv_poly_zero (c : ℕ → E) (n ℓ : ℕ) :
    iteratedDeriv ℓ (fun ε : ℝ => ∑ i ∈ Finset.range n, ε ^ i • c i) 0 =
      if ℓ < n then (ℓ.factorial : ℝ) • c ℓ else 0 := by
  have hc : ∀ i ∈ Finset.range n, ContDiffAt ℝ ℓ (fun ε : ℝ => ε ^ i • c i) 0 := fun i _ =>
    (by fun_prop : ContDiff ℝ ℓ (fun ε : ℝ => ε ^ i • c i)).contDiffAt
  rw [iteratedDeriv_fun_sum hc]
  have hterm : ∀ i ∈ Finset.range n, iteratedDeriv ℓ (fun ε : ℝ => ε ^ i • c i) 0 =
      if ℓ = i then (ℓ.factorial : ℝ) • c i else 0 := by
    intro i _
    rw [iteratedDeriv_smul_const
      (by fun_prop : ContDiff ℝ ℓ (fun ε : ℝ => ε ^ i)).contDiffAt (c i),
      iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hl : ℓ < n
  · rw [Finset.sum_ite_eq]
    simp [hl]
  · simp only [hl, ite_false]
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    simp only [show ¬ ℓ = i by omega, ite_false]

/-- `F` is the polynomial `∑_{i<n} ε^i c_i`. -/
def PolyAt (F : ℝ → E) (n : ℕ) (c : ℕ → E) : Prop :=
  ∀ ε, F ε = ∑ i ∈ Finset.range n, ε ^ i • c i

theorem PolyAt.add {F G : ℝ → E} {n : ℕ} {c d : ℕ → E} (hF : PolyAt F n c) (hG : PolyAt G n d) :
    PolyAt (fun ε => F ε + G ε) n (fun i => c i + d i) := by
  intro ε
  simp only [hF ε, hG ε, smul_add, Finset.sum_add_distrib]

theorem PolyAt.sum {κ : Type*} (S : Finset κ) {F : κ → ℝ → E} {n : ℕ} {c : κ → ℕ → E}
    (h : ∀ x ∈ S, PolyAt (F x) n (c x)) :
    PolyAt (fun ε => ∑ x ∈ S, F x ε) n (fun i => ∑ x ∈ S, c x i) := by
  intro ε
  beta_reduce
  rw [Finset.sum_congr rfl fun x hx => h x hx ε, Finset.sum_comm]
  simp [Finset.smul_sum]

theorem PolyAt.list_sum {κ : Type*} (L : List κ) {F : κ → ℝ → E} {n : ℕ} {c : κ → ℕ → E}
    (h : ∀ x ∈ L, PolyAt (F x) n (c x)) :
    PolyAt (fun ε => (L.map fun x => F x ε).sum) n (fun i => (L.map fun x => c x i).sum) := by
  induction L with
  | nil => intro ε; simp
  | cons x L ih =>
    intro ε
    have hih := ih (fun y hy => h y (by simp [hy])) ε
    beta_reduce at hih
    beta_reduce
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp) ε, hih]
    simp [smul_add, Finset.sum_add_distrib]

theorem PolyAt.congr_coeff {F : ℝ → E} {n : ℕ} {c d : ℕ → E} (hF : PolyAt F n c)
    (hc : ∀ i, c i = d i) : PolyAt F n d := by
  intro ε
  rw [hF ε]
  exact Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem PolyAt.congr_fun {F G : ℝ → E} {n : ℕ} {c : ℕ → E} (hF : PolyAt F n c)
    (hFG : ∀ ε, F ε = G ε) : PolyAt G n c := by
  intro ε
  rw [← hFG ε]
  exact hF ε

theorem PolyAt.iteratedDeriv_zero {F : ℝ → E} {n : ℕ} {c : ℕ → E} (hF : PolyAt F n c) {ℓ : ℕ}
    (hℓ : ℓ < n) : iteratedDeriv ℓ F 0 = (ℓ.factorial : ℝ) • c ℓ := by
  have : F = fun ε => ∑ i ∈ Finset.range n, ε ^ i • c i := funext hF
  rw [this, iteratedDeriv_poly_zero]
  simp [hℓ]

end Poly

section Source

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The `ε^ℓ`-coefficient of the source flux. -/
def SrcCoeff (edge : ConstituentEdges D h) (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i)
    (k : Fin 2) (ℓ : ℕ) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z v => ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)).sum

/-- One word term of the source flux is a polynomial in `ε`. -/
theorem polyAt_wordTerm {v : ι} {u : ι} {m : ℕ} (α : DerivativeWord2 m)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hm : m ≤ s) (hmD : m < D)
    (c : ℝ) (L : h u →L[ℝ] h v) (η : ℝ) (X z : Vec 2) :
    PolyAt (fun ε => c • L (dEpsWord η ε α Φ X z u)) D
      (fun ℓ => c • L (QuietDecay.srcW η u α Φ ℓ X z)) := by
  intro ε
  beta_reduce
  rw [QuietDecay.dEpsWord_apply_eq η ε α hΦ hm u X z]
  have hsub : Finset.range (m + 1) ⊆ Finset.range D := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  rw [← Finset.sum_subset hsub (fun i hi hni => by
    have hi' := Finset.mem_range.mp hi
    have hni' : ¬ i < m + 1 := fun h' => hni (Finset.mem_range.mpr h')
    rw [QuietDecay.srcW_eq_zero η u α Φ (by omega)]
    simp)]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

/-- One edge-and-order term of the source flux is a polynomial in `ε`. -/
theorem polyAt_edgeTerm (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s + 1)
    (k : Fin 2) (X z : Vec 2) (v u : ι) (d : Finset.Icc 2 D) :
    PolyAt (fun ε => ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum) D
      (fun ℓ => ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)).sum) := by
  have hd := Finset.mem_Icc.mp d.2
  refine PolyAt.list_sum (edge v u d)
    (F := fun γ ε => ∑ α : DerivativeWord2 (d.1 - 1),
        (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u))
    (c := fun γ ℓ => ∑ α : DerivativeWord2 (d.1 - 1),
        (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)) fun γ _ => ?_
  exact PolyAt.sum Finset.univ
    (F := fun α ε => (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u))
    (c := fun α ℓ => (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z))
    fun α _ => polyAt_wordTerm α Φ hΦ (by omega) (by omega) _ γ.map η X z

/-- The source flux is a polynomial in `ε` of degree `< D`. -/
theorem sourceFlux_polyAt (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s + 1)
    (k : Fin 2) (X z : Vec 2) :
    PolyAt (fun ε => sourceFlux edge η ε t Φ k X z) D (fun ℓ => SrcCoeff edge η t Φ k ℓ X z) := by
  have hv : ∀ v, PolyAt (fun ε => sourceFlux edge η ε t Φ k X z v) D
      (fun ℓ => SrcCoeff edge η t Φ k ℓ X z v) := by
    intro v
    have hsf : ∀ ε, sourceFlux edge η ε t Φ k X z v = ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum := fun ε => rfl
    have hP : PolyAt (fun ε => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum) D
        (fun ℓ => ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)).sum) := by
      have hin : ∀ u : ι, PolyAt (fun ε => ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
          ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum) D
          (fun ℓ => ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
          ∑ α : DerivativeWord2 (d.1 - 1),
          (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)).sum) := fun u =>
        PolyAt.sum Finset.univ fun d _ => polyAt_edgeTerm edge η t Φ hΦ hDs k X z v u d
      exact PolyAt.sum Finset.univ fun u _ => hin u
    exact (hP.congr_fun fun ε => (hsf ε).symm).congr_coeff fun ℓ => rfl
  intro ε
  beta_reduce
  funext v
  have := hv v ε
  beta_reduce at this
  rw [this]
  simp [Finset.sum_apply]

/-- The `ℓ`-th `ε`-derivative at `0` of the source flux. -/
theorem iteratedDeriv_sourceFlux (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) {s : ℕ} (hΦ : IsBoxSmooth s s Φ) (hDs : D ≤ s + 1)
    (k : Fin 2) (X z : Vec 2) {ℓ : ℕ} (hℓ : ℓ < D) :
    iteratedDeriv ℓ (fun ε : ℝ => sourceFlux edge η ε t Φ k X z) 0 =
      (ℓ.factorial : ℝ) • SrcCoeff edge η t Φ k ℓ X z :=
  (sourceFlux_polyAt edge η t Φ hΦ hDs k X z).iteratedDeriv_zero hℓ

/-- Box smoothness of the `ε`-coefficients of the source flux. -/
theorem isBoxSmooth_srcCoeff (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (ℓ : ℕ) {s N : ℕ}
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth N N Φ) (hN : s + D ≤ N + 1) :
    IsBoxSmooth s s (SrcCoeff edge η t Φ k ℓ) := by
  have he : SrcCoeff edge η t Φ k ℓ = fun X z v => ∑ u : ι, ∑ d : Finset.Icc 2 D,
      ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        (γ.coeff α t X z k) • γ.map (QuietDecay.srcW η u α Φ ℓ X z)).sum := rfl
  rw [he]
  apply AVRegularity.CycleComparison.Lift.isBoxSmooth_pi
  intro v
  apply IsBoxSmooth.sum
  intro u _
  apply IsBoxSmooth.sum
  intro d _
  apply AVRegularity.CycleComparison.Lift.isBoxSmooth_list_sum
  intro γ hγ
  apply IsBoxSmooth.sum
  intro α _
  have hd := Finset.mem_Icc.mp d.2
  have hw : IsBoxSmooth s s (QuietDecay.srcW η u α Φ ℓ) :=
    ((QuietDecay.isBoxSmooth_srcW η u α hΦ (by omega) ℓ).mono (by omega) (by omega))
  have hscalar := (hΓ v u d γ hγ α).clm_comp (ContinuousLinearMap.proj k)
  have hvector := hw.clm_comp γ.map
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
    AVRegularity.CycleComparison.Lift.isBoxSmooth_bilinear hscalar hvector
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)

/-- Box smoothness of the `ℓ`-th `ε`-derivative at `0` of the source flux. -/
theorem isBoxSmooth_iteratedDeriv_sourceFlux (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) {ℓ : ℕ} (hℓ : ℓ < D) {s N : ℕ}
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth s s (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth N N Φ) (hN : s + D ≤ N + 1) :
    IsBoxSmooth s s (fun X z =>
      iteratedDeriv ℓ (fun ε : ℝ => sourceFlux edge η ε t Φ k X z) 0) := by
  have hDs : D ≤ N + 1 := by omega
  have : (fun X z => iteratedDeriv ℓ (fun ε : ℝ => sourceFlux edge η ε t Φ k X z) 0) =
      fun X z => (ℓ.factorial : ℝ) • SrcCoeff edge η t Φ k ℓ X z :=
    funext fun X => funext fun z => iteratedDeriv_sourceFlux edge η t Φ hΦ hDs k X z hℓ
  rw [this]
  exact (isBoxSmooth_srcCoeff edge η t Φ k ℓ hΓ hΦ hN).const_smul _

end Source

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLMaps

/-! Toolbox of commutations of a continuous linear map with the operators of the lift.

For a fixed continuous linear map `L : P →L[ℝ] E` and fields in the regularity class that the
box-smoothness of a lift sequence provides (`IsBoxSmooth`), the map commutes with

* the ordered slow derivative `orderedDerivative` (`hl_orderedDerivative_clm`),
* `liftApply` for an intertwined family of maps,
* the cross operators `cellB1`, `cellB2` and the partial derivatives
  (`CycleComparison.Lift.cellB1_postcomposition` etc., reused),
* the cell mean (`fieldCellMean_clm`, reused), and
* the ordered `ε`-derivatives.

All of these are false without differentiability, because `fderiv` is the junk value `0` off the
differentiable fields, so each carries the regularity it needs. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear map commutes with the ordered slow derivative of a field of class `C^m`. -/
theorem hl_orderedDerivative_clm (L : P →L[ℝ] E) {m : ℕ} (α : DerivativeWord2 m)
    {β : Vec 2 → P} (hβ : ContDiff ℝ (m : ℕ∞) β) :
    orderedDerivative α (fun Y => L (β Y)) = fun Y => L (orderedDerivative α β Y) := by
  have h := AVRegularity.Providers.PathDecomp.orderedDerivative_clm_sum
    (Finset.univ : Finset Unit) (fun _ => L) α (β := fun _ => β) (fun _ _ => hβ)
  simpa using h

/-- Pointwise form of `hl_orderedDerivative_clm`. -/
theorem hl_orderedDerivative_clm_apply (L : P →L[ℝ] E) {m : ℕ} (α : DerivativeWord2 m)
    {β : Vec 2 → P} (hβ : ContDiff ℝ (m : ℕ∞) β) (X : Vec 2) :
    orderedDerivative α (fun Y => L (β Y)) X = L (orderedDerivative α β X) :=
  congrFun (hl_orderedDerivative_clm L α hβ) X

/-- The ordered derivative of a family of fields is taken componentwise. -/
theorem hl_orderedDerivative_proj {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {m : ℕ} (α : DerivativeWord2 m) {β : Vec 2 → ∀ i, h i}
    (hβ : ContDiff ℝ (m : ℕ∞) β) (X : Vec 2) (u : ι) :
    orderedDerivative α β X u = orderedDerivative α (fun Y => β Y u) X :=
  (hl_orderedDerivative_clm_apply (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) α hβ X).symm

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLMaps
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

/-! Box smoothness of the slow flux `liftFluxX` of a lift sequence.

Orders: the coefficients `Cc` are box smooth of order `(s + Dm, s + Dm)`, the coarse field is `C^{s+Dm+N}`
(`N` the degree above which the coefficients vanish), the metric `Q.G` and the drift `Q.v` are `C^s`, and
the edge coefficients are box smooth of order `(s, s)`. The conclusion is box smoothness of order
`(s, s)` of `liftFluxX` at every grade `hh ≤ H` and degree `n`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

/-- Scalar field times box smooth field. -/
theorem box_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}
    {f : Vec 2 → Vec 2 → ℝ} {g : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth p q f)
    (hg : IsBoxSmooth p q g) : IsBoxSmooth p q (fun X z => f X z • g X z) := by
  simpa only [ContinuousLinearMap.lsmul_apply] using!
    AVRegularity.CycleComparison.Lift.isBoxSmooth_bilinear hf hg
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)

/-- `liftApply` is box smooth, also above the degree where the coefficients vanish. -/
theorem liftApply_box (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hh n' N S : ℕ)
    (hz : ∀ n', N < n' → ∀ m α t X z v u, Cc hh n' m α t X z v u = 0)
    (hb : ∀ n' m α v u, IsBoxSmooth S S (fun X z => Cc hh n' m α t X z v u))
    (ha : ContDiff ℝ ((S + N : ℕ) : ℕ∞) (a t)) :
    IsBoxSmooth S S (fun X z => liftApply n' (Cc hh n') a t X z) := by
  apply AVRegularity.CycleComparison.Lift.isBoxSmooth_pi
  intro v
  by_cases hn : n' ≤ N
  · exact AVRegularity.CycleComparison.Lift.liftApply_component_box_reserve n' S S (Cc hh n') a t v
      (ha.of_le (by exact_mod_cast Nat.add_le_add_left hn S))
      (fun m _ α u => hb n' m α v u)
  · have hz' := hz n' (by omega)
    have : (fun X z => liftApply n' (Cc hh n') a t X z v) = fun _ _ => 0 := by
      funext X z
      simp only [liftApply]
      apply Finset.sum_eq_zero
      intro m _
      apply Finset.sum_eq_zero
      intro α _
      apply Finset.sum_eq_zero
      intro u _
      simp [hz' m α t X z v u]
    rw [this]
    exact IsBoxSmooth.zero

/-- **Box smoothness of `liftFluxX`.** -/
theorem liftFluxX_box (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (k : Fin 2) (s N H : ℕ)
    (hDm : 1 ≤ Dm) (hhH : hh ≤ H)
    (hz : ∀ hh' ≤ H, ∀ n', N < n' → ∀ m α t X z v u, Cc hh' n' m α t X z v u = 0)
    (hb : ∀ hh' ≤ H, ∀ n' m α v u,
      IsBoxSmooth (s + Dm) (s + Dm) (fun X z => Cc hh' n' m α t X z v u))
    (hG : ∀ j, ContDiff ℝ (s : ℕ∞) (fun X => Q.G t X k j))
    (hv : ContDiff ℝ (s : ℕ∞) (fun z => Q.v t z k))
    (hedge : hh ≠ 0 → ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth s s (fun X z => γ.coeff α t X z))
    (ha : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t)) :
    IsBoxSmooth s s (fun X z => liftFluxX Q Cc a hh n t X z k) := by
  have hL : ∀ hh' ≤ H, ∀ n', IsBoxSmooth (s + Dm) (s + Dm)
      (fun X z => liftApply n' (Cc hh' n') a t X z) := fun hh' hh'H n' =>
    liftApply_box Cc a t hh' n' N (s + Dm) (hz hh' hh'H) (hb hh' hh'H) ha
  have hT1 : IsBoxSmooth s s (fun X z =>
      (Real.sqrt Q.η * Q.v t z k) • liftApply (n - 1) (Cc hh (n - 1)) a t X z) :=
    box_smul (AVRegularity.CycleComparison.Lift.isBoxSmooth_fast_field s s _
        (contDiff_const.mul hv))
      ((hL hh hhH (n - 1)).mono (by omega) (by omega))
  have hT2 : IsBoxSmooth s s (fun X z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k j •
      fastPartial j (liftApply (n - 1) (Cc hh (n - 1)) a t) X z) := by
    refine IsBoxSmooth.const_smul _ ?_
    refine IsBoxSmooth.sum _ fun j _ => ?_
    exact box_smul (AVRegularity.CycleComparison.Lift.isBoxSmooth_slow_field s s _ (hG j))
      (IsBoxSmooth.fastPartial ((hL hh hhH (n - 1)).mono (by omega) (by omega)) j)
  have hT3 : IsBoxSmooth s s (fun X z => if 2 ≤ n then -(Q.η • ∑ j : Fin 2, Q.G t X k j •
      slowPartial j (liftApply (n - 2) (Cc hh (n - 2)) a t) X z) else 0) := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      refine IsBoxSmooth.neg (IsBoxSmooth.const_smul _ ?_)
      refine IsBoxSmooth.sum _ fun j _ => ?_
      exact box_smul (AVRegularity.CycleComparison.Lift.isBoxSmooth_slow_field s s _ (hG j))
        (IsBoxSmooth.slowPartial ((hL hh hhH (n - 2)).mono (by omega) (by omega)) j)
    · simp only [h2, ite_false]
      exact IsBoxSmooth.zero
  have hT4 : IsBoxSmooth s s (fun X z => if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min Dm n),
      (Real.sqrt Q.η * ((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1) (fun ε : ℝ =>
        sourceFlux Q.edge Q.η ε t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) k X z) 0) := by
    by_cases h0 : hh = 0
    · simp only [h0, ite_true]
      exact IsBoxSmooth.zero
    · simp only [h0, ite_false]
      refine IsBoxSmooth.sum _ fun j hj => ?_
      have hj' := Finset.mem_Icc.mp hj
      refine IsBoxSmooth.const_smul _ ?_
      exact isBoxSmooth_iteratedDeriv_sourceFlux Q.edge Q.η t _ k
        (ℓ := j - 1) (by omega) (N := s + Dm) (hedge h0) (hL (hh - 1) (by omega) (n - j)) (by omega)
  exact ((hT1.sub hT2).add hT3).sub hT4

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
end
end
